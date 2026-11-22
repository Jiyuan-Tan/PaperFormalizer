// `--revise`: a paper's next version under the same slug (`revision.ts`), its transcription re-pointed
// at the revised source (`reanchor.ts`).
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { createVerifyInitialState } from "../../src/state.js";
import type { PatchFile } from "../../src/verify/patches.js";
import { dice, matchEnvs, reanchorRefs, reanchorSegments, referencedContextChanged, relocateLines, renumberSentences, setupChanged } from "../../src/verify/reanchor.js";
import { paperIndex } from "../../src/verify/referee_slices.js";
import type { RefCore } from "../../src/verify/ref_core.js";
import { adoptsRepair, completeSourceSwap, prepareRevision, reconcilePatches, freezeVersion, startRevision, versionDir } from "../../src/verify/revision.js";
import { hashSourceTree } from "../../src/verify/source_bundle.js";
import type { EnvsJson, PrepareSource, TexEnv } from "../../src/verify/types.js";

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

let line = 1;
function env(id: string, kind: TexEnv["kind"], body: string, proof: string | null = null, label: string | null = id.includes(":") ? id : null): TexEnv {
  const from = (line += 10);
  return {
    id,
    kind,
    envName: kind,
    label,
    title: null,
    body,
    proof,
    proofLines: proof === null ? null : { file: "main.tex", from: from + 3, to: from + 5, env: "proof", label: null },
    lines: { file: "main.tex", from, to: from + 2, env: kind, label },
    refs: [],
  };
}
const paper = (envs: TexEnv[], flat = ""): { envs: EnvsJson; flat: string } => ({ envs: { main_file: "main.tex", files: ["main.tex"], newtheorem: {}, envs, bibliography: [] }, flat });

describe("matching the environments of a revision", () => {
  it("a label keeps its environment; an unlabeled one whose ordinal moved is found by its text, a new one before it notwithstanding", () => {
    const before = [env("thm:main", "theorem", "The main result holds."), env("lemma-1", "lemma", "Every bounded sequence has a convergent subsequence."), env("lemma-2", "lemma", "The map is continuous on the closed set.")];
    const after = [
      env("thm:main", "theorem", "The main result holds, as stated."),
      env("lemma-1", "lemma", "A lemma the revision adds about something else entirely."),
      env("lemma-2", "lemma", "Every bounded sequence has a convergent subsequence."),
      env("lemma-3", "lemma", "The map is continuous on the closed set $K$."),
    ];
    const m = matchEnvs(before, after, new Set(before.map((e) => e.id)));
    expect(Object.fromEntries(m)).toEqual({ "thm:main": "thm:main", "lemma-1": "lemma-2", "lemma-2": "lemma-3" });
    // a proof reworded, a lemma added before: still the same result, by its statement
    const proved = [env("lemma-1", "lemma", "Every bounded sequence has a convergent subsequence.", "By bisection.")];
    const revised = [env("lemma-1", "lemma", "The function g is strictly increasing on the line.", "Differentiate."), env("lemma-2", "lemma", "Every bounded sequence has a convergent subsequence.", "Pick a monotone subsequence and apply completeness of the reals.")];
    expect(Object.fromEntries(matchEnvs(proved, revised, new Set(["lemma-1"])))).toEqual({ "lemma-1": "lemma-2" });
    // nothing alike enough: no counterpart
    expect(matchEnvs([env("lemma-1", "lemma", "Completely different words here.")], [env("lemma-1", "lemma", "Unrelated statement about graphs.")], new Set(["lemma-1"])).size).toBe(0);
    expect(dice("a b c", "a b c")).toBe(1);
  });

  it("a run of sentences is re-numbered on the sentences left as they were; a rewritten end gives none", () => {
    expect(renumberSentences("One holds. Two holds. Three holds.", "Zero is new. One holds. Two holds. Three holds.", [2, 3])).toEqual([3, 4]);
    expect(renumberSentences("One holds. Two holds. Three holds.", "One holds. Two now reads differently. Three holds.", [2, 2])).toBeNull();
  });
});

describe("reanchorRefs", () => {
  const ref = (over: Partial<RefCore> = {}): RefCore =>
    ({
      qid: "toy",
      target_estimand: "t",
      symbols: [],
      assumptions: [{ id: "ass:moment", source: { env: "assumption-1", region: "body", sentences: [2, 2] } }],
      definitions: [{ id: "def:rate", name: "rate", source: { prose: true, slice: { from: "We call", to: "the rate." } } }],
      statements: [
        { id: "thm:main", kind: "theorem", env: "thm:main", status: "to-prove", depends_on: ["ass:moment"] },
        { id: "lem:aux", kind: "lemma", env: "lemma-1", status: "to-prove", depends_on: [] },
      ],
      ...over,
    }) as RefCore;
  const v1 = () =>
    paper(
      [
        env("assumption-1", "assumption", "Let the data be independent. The fourth moment is finite."),
        env("thm:main", "theorem", "The estimator is consistent.", "By the law of large numbers."),
        env("lemma-1", "lemma", "The variance is bounded by the fourth moment.", "Apply Cauchy-Schwarz."),
      ],
      "Intro. We call $r_n$ the rate. More text.",
    );

  it("a revision that moves results and re-words one: the ids kept, the moved environment and sentences re-pointed, the changed node named", () => {
    const v2 = paper(
      [
        env("assumption-1", "assumption", "We work in a sampling model. Let the data be independent. The fourth moment is finite."),
        env("lemma-1", "lemma", "A new lemma the authors added."),
        env("thm:main", "theorem", "The estimator is consistent.", "By the strong law of large numbers."),
        env("lemma-2", "lemma", "The variance is bounded by the fourth moment.", "Apply Cauchy-Schwarz."),
      ],
      "A new opening. Intro. We call $r_n$ the rate. More text.",
    );
    const r = reanchorRefs(ref(), v1(), v2);
    expect(r.renamed).toEqual({ "lemma-1": "lemma-2" });
    expect(r.refs.statements.find((s) => s.id === "lem:aux")!.env).toBe("lemma-2");
    expect(r.refs.assumptions[0]!.source).toEqual({ env: "assumption-1", region: "body", sentences: [3, 3] });
    expect(r.same.sort()).toEqual(["ass:moment", "def:rate", "lem:aux"]);
    expect(r.changed).toEqual(["thm:main"]);
    expect(r.broken).toEqual([]);
    expect(r.brokenShare).toBe(0);
  });

  it("a rewritten run of sentences is cut by its old ends, and fails to cut when they are gone; a lost environment breaks its node", () => {
    const v2 = paper([env("assumption-1", "assumption", "Let the data be independent. Some new words: The fourth moment is finite."), env("thm:main", "theorem", "Something else.")], "No definition here.");
    const r = reanchorRefs(ref(), v1(), v2);
    expect(r.refs.assumptions[0]!.source).toEqual({ env: "assumption-1", region: "body", slice: { from: "The fourth moment is finite.", to: "The fourth moment is finite." } });
    // the passage its old ends cut is the same words: unchanged
    expect(r.same).toEqual(["ass:moment"]);
    expect(r.changed).toEqual(["thm:main"]);
    expect(r.broken.sort()).toEqual(["def:rate", "lem:aux"]);
    expect(r.brokenShare).toBe(0.5);
    // an unlabeled environment with no counterpart never takes the text of the one its ordinal now names
    const lemmaGone = paper([env("assumption-1", "assumption", "Let the data be independent. The fourth moment is finite."), env("thm:main", "theorem", "The estimator is consistent.", "By the law of large numbers."), env("lemma-1", "lemma", "The function g is strictly increasing.", "Differentiate.")], "Intro. We call $r_n$ the rate. More text.");
    const g = reanchorRefs(ref(), v1(), lemmaGone);
    expect(g.broken).toEqual(["lem:aux"]);
    expect(g.refs.statements.find((x) => x.id === "lem:aux")!.env).toBe("lemma-1 (no counterpart in the revised paper)");
    // its words gone: broken, for V1 to re-point
    const v3 = paper([env("assumption-1", "assumption", "Let the data be independent. Moments of order four are bounded."), env("thm:main", "theorem", "Something else.")], "No definition here.");
    expect(reanchorRefs(ref(), v1(), v3).broken.sort()).toEqual(["ass:moment", "def:rate", "lem:aux"]);
  });
});

describe("the patch file read against the revision", () => {
  const core = (statement: string): Core => ({ qid: "q", symbols: [], assumptions: [], definitions: [], statements: [{ id: "thm:a", kind: "theorem", statement, status: "to-prove", depends_on: [] }, { id: "lem:b", kind: "lemma", statement: "B.", status: "to-prove", depends_on: [] }], target_estimand: "t", bibliography: [] }) as unknown as Core;
  const file = (): PatchFile =>
    ({
      key_results: [],
      key_contribution: "",
      patches: [
        { node: "thm:a", ops: [{ op: "replace", unit: "thm:a/1/1", to: null, tex: "For $n \\ge 2$, A." }] },
        { node: "lem:b", ops: [{ op: "replace", unit: "lemma-1/proof/1/2", to: "lemma-1/proof/1/3", tex: "x" }] },
      ],
      unfixable: [],
      owner_readings: [{ id: "ass:pin-owner-1", node: "thm:a", reading: "n is an integer" }],
    }) as unknown as PatchFile;

  it("a repair of an unchanged node stands (its units re-pointed); one the author took is retired; any other on a changed node is set aside", () => {
    const before = core("A.");
    const patched = core("For $n \\ge 2$, A.");
    expect(adoptsRepair("thm:a", before, patched, core("For $n \\ge 2$, A."))).toBe(true);
    expect(adoptsRepair("thm:a", before, patched, core("A, reworded."))).toBe(false);
    const r = { same: ["lem:b"], changed: ["thm:a"], broken: [], renamed: { "lemma-1": "lemma-2" } };
    const text = (env: string) => (u: string, t?: string | null): string | null => (u.startsWith(`${env}/`) && (!t || t.startsWith(`${env}/`)) ? `text of ${u.split("/").slice(1).join("/")}..${t?.split("/").slice(1).join("/") ?? ""}` : null);
    const units = { before: text("lemma-1"), after: text("lemma-2") };
    const adopted = reconcilePatches(file(), r, { transcribedBefore: before, patchedBefore: patched, transcribedNow: core("For $n \\ge 2$, A.") }, units);
    expect(adopted).toMatchObject({ kept: ["lem:b"], adopted: ["thm:a"], set_aside: [], rulings_to_recheck: [{ id: "ass:pin-owner-1", node: "thm:a" }] });
    expect(adopted.file.patches.map((p) => p.node)).toEqual(["lem:b"]);
    expect(adopted.file.patches[0]!.ops).toEqual([{ op: "replace", unit: "lemma-2/proof/1/2", to: "lemma-2/proof/1/3", tex: "x" }]);
    // the owner's readings all stand
    expect(adopted.file.owner_readings).toHaveLength(1);
    // an operator's fix in place is no correction by the authors: the same text is set aside, not adopted
    expect(reconcilePatches(file(), r, { transcribedBefore: before, patchedBefore: patched, transcribedNow: core("For $n \\ge 2$, A.") }, units, { adopt: false })).toMatchObject({ adopted: [], set_aside: ["thm:a"] });
    const reworded = reconcilePatches(file(), r, { transcribedBefore: before, patchedBefore: patched, transcribedNow: core("A, reworded.") }, units);
    expect(reworded).toMatchObject({ adopted: [], set_aside: ["thm:a"] });
    // an unchanged node whose units were renumbered (a sentence added elsewhere in its environment): set aside
    const shifted = reconcilePatches(file(), r, { transcribedBefore: before, patchedBefore: patched, transcribedNow: core("A.") }, { before: units.before, after: () => "another passage" });
    expect(shifted).toMatchObject({ kept: [], set_aside: ["thm:a", "lem:b"] });
  });
});

describe("segments follow their lines", () => {
  it("a range moves with its block of lines; one whose lines are gone, or found twice, is dropped", () => {
    const before = "a\nb\nc\nd";
    expect(relocateLines(before.split("\n"), "new\na\nb\nc\nd".split("\n"), [2, 3])).toEqual([3, 4]);
    expect(relocateLines(before.split("\n"), "a\nB\nc\nd".split("\n"), [2, 3])).toBeNull();
    expect(relocateLines(before.split("\n"), "b\nc\nb\nc".split("\n"), [2, 3])).toBeNull();
    const out = reanchorSegments({ results: [{ lines: [1, 2], proof_lines: [3, 4] }], bindings: [{ result: "lemma-1", proof_lines: [4, 4] }], extend: [{ lines: [2, 2] }] }, before, "x\na\nb\nc\nD");
    expect(out.seg).toEqual({ results: [], bindings: [], extend: [{ lines: [3, 3] }] });
    expect(out.dropped).toBe(2);
    // a binding whose environment no longer reads as it did (an unlabeled ordinal now naming another): dropped
    const bound = reanchorSegments({ results: [], bindings: [{ result: "lemma-1", proof_lines: [2, 3] }] }, before, "x\na\nb\nc\nd", (id) => id !== "lemma-1");
    expect(bound).toMatchObject({ seg: { bindings: [] }, dropped: 1 });
  });

  it("a revision goes to the segmenter for what its parse leaves unplaced that the version's did not", async () => {
    const { newParserGaps } = await import("../../src/verify/stage_v1.js");
    const old = ["appendix.tex:7: \\begin{proof} is attached to no result (its title references lem:orphan)"];
    // the same gap, moved: not new
    expect(newParserGaps(["appendix.tex:12: \\begin{proof} is attached to no result (its title references lem:orphan)"], old)).toEqual([]);
    // a second one: new
    expect(newParserGaps(["appendix.tex:12: \\begin{proof} is attached to no result (its title references lem:orphan)", "sec/b.tex:3: \\begin{proof} is attached to no result (it does not directly follow one)"], old)).toHaveLength(1);
  });
});

describe("startRevision", () => {
  async function run(): Promise<{ runDir: string; state: ReturnType<typeof createVerifyInitialState>; revised: string; prepare: PrepareSource }> {
    const root = await mkdtemp(path.join(os.tmpdir(), "revise-"));
    tmpDirs.push(root);
    const runDir = path.join(root, "run");
    await mkdir(path.join(runDir, "source"), { recursive: true });
    await mkdir(path.join(runDir, "discovery"), { recursive: true });
    await mkdir(path.join(runDir, "bundle", "lean"), { recursive: true });
    await writeFile(path.join(runDir, "source", "main.tex"), "version one", "utf8");
    await writeFile(path.join(runDir, "discovery", "core.json"), "{}", "utf8");
    await writeFile(path.join(runDir, "bundle", "lean", "Main.lean"), "theorem t : True := trivial", "utf8");
    await writeFile(path.join(runDir, "report.md"), "# v1", "utf8");
    const state = createVerifyInitialState("q", {
      phase: "done",
      source: { input: "paper_v1.tex", main_file: "main.tex", sha256: await hashSourceTree(path.join(runDir, "source")) },
      targets: null,
      core_sha256: null,
      v1_rounds: 1,
      v1_5_rounds: 0,
      findings: [],
      report_path: null,
    });
    state.stage_completed = "V6";
    const revised = path.join(root, "paper_v2");
    await mkdir(revised, { recursive: true });
    await writeFile(path.join(revised, "main.tex"), "version two", "utf8");
    const prepare: PrepareSource = async ({ input, sourceDir }) => {
      await mkdir(sourceDir, { recursive: true });
      await writeFile(path.join(sourceDir, "main.tex"), await readFile(path.join(input, "main.tex"), "utf8"), "utf8");
      return { sourceDir, mainFile: "main.tex", sha256: await hashSourceTree(sourceDir), inputKind: "dir" };
    };
    return { runDir, state, revised, prepare };
  }

  it("freezes the version that stands under versions/v1 and puts the revised source in its place; the run is version 2", async () => {
    const { runDir, state, revised, prepare } = await run();
    const sha1 = state.verify!.source.sha256;
    const prepared = await prepareRevision({ runDir, state, input: revised, prepareSource: prepare });
    // nothing of the run has changed yet
    expect(state.verify!.version).toBeUndefined();
    expect(await readFile(path.join(runDir, "source", "main.tex"), "utf8")).toBe("version one");
    let saves = 0;
    const frozen = await freezeVersion({ runDir, state, now: () => new Date("2026-11-10T12:00:00Z") });
    // the freeze changes nothing of the state
    expect(state.verify!.version).toBeUndefined();
    const s = await startRevision({ runDir, state, prepared, frozen, save: async () => void (saves += 1) });
    expect(saves).toBe(2);
    const v1 = versionDir(runDir, 1);
    expect(s.version).toBe(2);
    expect(await readFile(path.join(v1, "source", "main.tex"), "utf8")).toBe("version one");
    expect(await readFile(path.join(v1, "bundle", "lean", "Main.lean"), "utf8")).toContain("theorem t");
    expect(await readFile(path.join(v1, "report.md"), "utf8")).toBe("# v1");
    expect(JSON.parse(await readFile(path.join(v1, "version.json"), "utf8"))).toMatchObject({ version: 1, input: "paper_v1.tex", source_sha256: sha1, stage_completed: "V6", phase: "done" });
    expect(await readFile(path.join(runDir, "source", "main.tex"), "utf8")).toBe("version two");
    expect(existsSync(path.join(runDir, ".revise_source"))).toBe(false);
    expect(existsSync(path.join(runDir, "versions", ".v1.partial"))).toBe(false);
    const v = state.verify!;
    expect(v.version).toBe(2);
    expect(v.versions).toHaveLength(1);
    expect(v.revision).toEqual({ from_version: 1, started_at: "2026-11-10T12:00:00.000Z" });
    // V1 sees the change: the hash on record is still version 1's
    expect(v.source).toMatchObject({ input: revised, sha256: sha1 });
  });

  it("a revision sent again before V1 read the first replaces it in place: nothing is frozen twice", async () => {
    const { runDir, state, revised, prepare } = await run();
    await startRevision({ runDir, state, prepared: await prepareRevision({ runDir, state, input: revised, prepareSource: prepare }), frozen: await freezeVersion({ runDir, state }), save: async () => {} });
    await writeFile(path.join(revised, "main.tex"), "version two, corrected", "utf8");
    // the same revision again is refused …
    await writeFile(path.join(revised, "main.tex"), "version two", "utf8");
    await expect(prepareRevision({ runDir, state, input: revised, prepareSource: prepare })).rejects.toThrow(/as it stands/);
    // … a corrected one replaces it
    await writeFile(path.join(revised, "main.tex"), "version two, corrected", "utf8");
    // the revision's starting point is recorded once, with the first: a replacement starts from it
    const base = path.join(versionDir(runDir, 1), "base", "state.json");
    expect(JSON.parse(await readFile(base, "utf8")).verify.revision).toMatchObject({ from_version: 1 });
    const baseBefore = await readFile(base, "utf8");
    // (an open revision is not frozen again)
    expect(await freezeVersion({ runDir, state })).toBeNull();
    const s = await startRevision({ runDir, state, prepared: await prepareRevision({ runDir, state, input: revised, prepareSource: prepare }), frozen: null, save: async () => {} });
    expect(s).toMatchObject({ version: 2, frozen: { version: 1 } });
    expect(await readFile(path.join(runDir, "source", "main.tex"), "utf8")).toBe("version two, corrected");
    expect(state.verify!.versions?.map((v) => v.version)).toEqual([1]);
    expect(existsSync(versionDir(runDir, 2))).toBe(false);
    expect(await readFile(path.join(versionDir(runDir, 1), "source", "main.tex"), "utf8")).toBe("version one");
    expect(await readFile(base, "utf8")).toBe(baseBefore);
  });

  it("is refused, nothing changed, when the revision is the source as it stands or a frozen version is in the way", async () => {
    const a = await run();
    await writeFile(path.join(a.revised, "main.tex"), "version one", "utf8");
    await expect(prepareRevision({ runDir: a.runDir, state: a.state, input: a.revised, prepareSource: a.prepare })).rejects.toThrow(/is the source of version 1 as it stands/);
    expect(existsSync(versionDir(a.runDir, 1))).toBe(false);
    const b = await run();
    await mkdir(versionDir(b.runDir, 1), { recursive: true });
    // (a copy that is not this version's: in the way)
    await expect(prepareRevision({ runDir: b.runDir, state: b.state, input: b.revised, prepareSource: b.prepare })).rejects.toThrow(/is not a copy of this run's version 1/);
    expect(b.state.verify!.version).toBeUndefined();
  });

  it("a frozen copy of this very version (a --revise killed before it recorded the revision) is reused, not refused", async () => {
    const { runDir, state, revised, prepare } = await run();
    const first = await freezeVersion({ runDir, state, now: () => new Date("2026-11-10T12:00:00Z") });
    // killed here: the state never recorded the revision; the next --revise goes on
    await writeFile(path.join(runDir, "report.md"), "# v1, after the kill", "utf8");
    const prepared = await prepareRevision({ runDir, state, input: revised, prepareSource: prepare });
    const again = await freezeVersion({ runDir, state });
    expect(again).toEqual(first);
    // the copy taken first (before anything was voided) is the one kept
    expect(await readFile(path.join(versionDir(runDir, 1), "report.md"), "utf8")).toBe("# v1");
    await startRevision({ runDir, state, prepared, frozen: again, save: async () => {} });
    expect(state.verify!.version).toBe(2);
  });

  it("a frozen copy of an EARLIER state of the version (the run went on after the kill) is replaced", async () => {
    const { runDir, state, revised, prepare } = await run();
    state.stage_completed = "3";
    await freezeVersion({ runDir, state, now: () => new Date("2026-11-10T12:00:00Z") });
    // killed; the run was resumed and finished meanwhile
    state.stage_completed = "V6";
    await writeFile(path.join(runDir, "report.md"), "# v1, delivered", "utf8");
    await writeFile(path.join(runDir, "report.json"), "{}", "utf8");
    await prepareRevision({ runDir, state, input: revised, prepareSource: prepare });
    const again = await freezeVersion({ runDir, state, now: () => new Date("2026-11-10T13:00:00Z") });
    expect(again).toMatchObject({ stage_completed: "V6", frozen_at: "2026-11-10T13:00:00.000Z" });
    expect(await readFile(path.join(versionDir(runDir, 1), "report.md"), "utf8")).toBe("# v1, delivered");
  });

  it("a swap cut short is finished by the next entry, wherever it stopped", async () => {
    for (const stop of ["before", "between"] as const) {
      const { runDir, state, revised, prepare } = await run();
      const prepared = await prepareRevision({ runDir, state, input: revised, prepareSource: prepare });
      // the state recorded the revision (a pending swap) and the process died
      state.verify!.revision = { from_version: 1, started_at: "t", source_swap_pending: true };
      // ("between": the version's source removed, the revised one not yet in its place)
      if (stop === "between") await rm(path.join(runDir, "source"), { recursive: true, force: true });
      expect(prepared.sha256).not.toBe(state.verify!.source.sha256);
      expect(await completeSourceSwap(runDir, state.verify)).toBe(true);
      expect(await readFile(path.join(runDir, "source", "main.tex"), "utf8")).toBe("version two");
      expect(existsSync(path.join(runDir, ".revise_source"))).toBe(false);
      expect(state.verify!.revision!.source_swap_pending).toBeUndefined();
      expect(await completeSourceSwap(runDir, state.verify)).toBe(false);
    }
  });
});

describe("the report of a revised version", () => {
  it("names what the revision changed, the corrections it adopts, the readings to confirm and every outcome that moved", async () => {
    const { reportRevision, renderRevision } = await import("../../src/verify/revision.js");
    const verify = {
      version: 2,
      revision: {
        from_version: 1,
        started_at: "t",
        reanchor: { same: 7, changed: ["thm:main"], broken: ["lem:aux"], renamed: {}, cold: false },
        patches: { kept: [], adopted: ["thm:main"], set_aside: [] },
        rulings_to_recheck: [{ id: "ass:pin-owner-1", node: "thm:main" }],
        transcribed: true,
      },
    };
    const rev = reportRevision(verify, [{ node_id: "thm:main", bucket: "verified" }, { node_id: "lem:aux", bucket: "verified" }, { node_id: "lem:new", bucket: "unproved" }], [{ node_id: "thm:main", bucket: "repaired" }, { node_id: "lem:aux", bucket: "verified" }])!;
    expect(rev.outcomes).toEqual([{ node: "thm:main", before: "repaired", now: "verified" }, { node: "lem:new", before: null, now: "unproved" }]);
    const md = renderRevision(rev).join("\n");
    expect(md).toMatch(/^## Changes from version 1/);
    expect(md).toContain("kept under `versions/v1/`");
    expect(md).toContain("left as they were: 7");
    expect(md).toContain("corrections of version 1 the revision adopts: `thm:main`");
    expect(md).toContain("`ass:pin-owner-1` (thm:main)");
    expect(md).toContain("| `lem:new` | (new) | unproved |");
    expect(reportRevision({}, [], null)).toBeNull();
    expect(renderRevision(null)).toEqual([]);
  });
});

describe("what a referee reads beyond a node's record", () => {
  const px = (flat: string) => paperIndex(flat, null, null);
  const core = (statement: string): Core => ({ qid: "q", symbols: [], assumptions: [], definitions: [], statements: [{ id: "thm:a", kind: "theorem", statement, status: "to-prove", depends_on: [], tex_locator: { file: "main.tex", from: 1, to: 1, env: "thm", label: "thm:a" } }], target_estimand: "t", bibliography: [] }) as unknown as Core;
  it("a passage a node references outside the core, revised, re-opens the node; the same passage moved does not", () => {
    const before = "\\begin{document}\n\nIntro.\n\\begin{equation}\\label{eq:key} x = y \\end{equation}\n\nMore.";
    const moved = "\\begin{document}\n\nA new intro paragraph.\n\nIntro.\n\\begin{equation}\\label{eq:key} x = y \\end{equation}\n\nMore.";
    const edited = "\\begin{document}\n\nIntro.\n\\begin{equation}\\label{eq:key} x = 2y \\end{equation}\n\nMore.";
    const c = core("By \\eqref{eq:key}, the claim holds.");
    expect(referencedContextChanged({ px: px(before), core: c }, { px: px(moved), core: c }, ["thm:a"])).toEqual([]);
    expect(referencedContextChanged({ px: px(before), core: c }, { px: px(edited), core: c }, ["thm:a"])).toEqual(["thm:a"]);
  });
  it("the setup changed: any word of it or a macro (a word can carry a hypothesis), not its line breaks", () => {
    const a = "\\newcommand{\\E}{\\mathbb{E}}\n\\begin{document}\nWe observe $n$ units with $Y_i \\in \\mathbb{R}$.\n\\begin{theorem}x\\end{theorem}";
    expect(setupChanged(px(a), px(a.replace("We observe $n$", "We observe\n$n$")))).toBe(false);
    expect(setupChanged(px(a), px(a.replace("We observe", "Throughout, we observe")))).toBe(true);
    expect(setupChanged(px(a), px(a.replace("$Y_i \\in \\mathbb{R}$", "$Y_i \\in [0,1]$")))).toBe(true);
    expect(setupChanged(px(a), px(a.replace("\\mathbb{E}}", "\\operatorname{E}}")))).toBe(true);
  });
});
