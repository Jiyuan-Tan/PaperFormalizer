/**
 * Minimal patches: the patch file's mechanical checks, the overlay, descoping, and V1 PATCH
 * mode (fixer faked). No network.
 */
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { runStructuralGate } from "../../src/core/gate.js";
import type { Core } from "../../src/core/schema.js";
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState } from "../../src/state.js";
import {
  applyPatchFile,
  blockedUnfixable,
  materializeReply,
  overlapViolations,
  PatchFileSchema,
  CoreGraphInputError,
  readPatchFile,
  repairSources,
  validatePatchFile,
  withoutMootDrops,
  type PatchFile,
} from "../../src/verify/patches.js";
import { nodePassage, PROOF_UNCHANGED, type RepairScope } from "../../src/verify/ops.js";
import { TEX_MATH_RULE } from "../../src/verify/owner_text.js";
import { runStageV1 } from "../../src/verify/stage_v1.js";
import { VERIFY_FILES } from "../../src/verify/types.js";
import { withOwnerExplanations, writeToyPaper } from "./owner_explained.js";
import { symbolReply } from "./symbol_fake.js";

const QID = "verify_toy_patch";
const tmpDirs: string[] = [];
afterEach(async () => {
  for (const dir of tmpDirs.splice(0)) await rm(dir, { recursive: true, force: true });
});

/** lem:rate is used by thm:main (the headline) and by thm:side (a non-key result); prop:aside
 * stands alone. */
function core(): Core {
  return {
    qid: QID,
    symbols: [{ name: "\\hat p", type: "estimated propensity" }],
    assumptions: [
      {
        id: "ass:overlap",
        condition: "\\(\\hat p < 1 - \\eta\\)",
        novel: { flag: true, justification: "Assumption 1" },
        used_by: ["lem:rate"],
      },
    ],
    definitions: [],
    statements: [
      { id: "lem:rate", kind: "lemma", statement: "the rate is \\(n^{-1/2}\\)", depends_on: ["ass:overlap"], status: "to-prove" },
      { id: "thm:main", kind: "theorem", statement: "the estimator is asymptotically normal", depends_on: ["lem:rate"], status: "to-prove" },
      { id: "thm:side", kind: "theorem", statement: "the variance estimator is consistent", depends_on: ["lem:rate"], status: "to-prove" },
      { id: "prop:aside", kind: "proposition", statement: "a remark-level identity", depends_on: [], status: "to-prove" },
    ],
    target_estimand: "\\(\\tau\\)",
  } as unknown as Core;
}

function patchFile(over: Partial<PatchFile> = {}): PatchFile {
  return PatchFileSchema.parse({
    key_results: ["thm:main"],
    key_contribution: "asymptotic normality of the estimator under overlap",
    patches: [
      {
        node: "lem:rate",
        corrected_statement: null,
        proof_note: "bound $1/\\hat p$ by $1/\\eta$ in the second display",
      },
    ],
    unfixable: [],
    ...over,
  });
}

describe("validatePatchFile", () => {
  it("accepts a well-formed patch file", () => {
    expect(validatePatchFile(core(), patchFile(), ["lem:rate"])).toEqual([]);
  });

  it("names a finding node left unaddressed, and one addressed twice", () => {
    const v = validatePatchFile(core(), patchFile({ unfixable: [{ node: "lem:rate", reason: "x" }] }), ["lem:rate", "prop:aside"]);
    expect(v.join(" ")).toContain(`"prop:aside" has a finding but neither a patch`);
    expect(v.join(" ")).toContain(`"lem:rate" is addressed more than once`);
  });
});

describe("readPatchFile refuses a file that does not fit the schema as the operator's input error", () => {
  const write = async (raw: unknown): Promise<string> => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "verify-patchfile-"));
    tmpDirs.push(dir);
    await mkdir(path.join(dir, "discovery"), { recursive: true });
    await writeFile(path.join(dir, VERIFY_FILES.patches), JSON.stringify(raw), "utf8");
    return dir;
  };
  const base = { key_results: ["thm:main"], key_contribution: "k", unfixable: [] };
  const p = (over: Record<string, unknown>) => ({ node: "lem:rate", corrected_statement: null, proof_note: "p", ...over });

  it("a non-replace op (in a patch or a suggestion) is a CoreGraphInputError naming the path, so a stage checkpoints instead of crashing", async () => {
    let err: unknown;
    await readPatchFile(await write({ ...base, patches: [p({ ops: [{ op: "insert_after", unit: "u", tex: "t" }] })] })).catch((e: unknown) => (err = e));
    expect(err).toBeInstanceOf(CoreGraphInputError);
    expect((err as CoreGraphInputError).file).toBe("patches.json");
    expect((err as CoreGraphInputError).problems.join(" ")).toMatch(/patches\.0\.ops\.0\.op: .*replace/);
    const suggestion = { node: "thm:main", reason: "r", suggested_repair: { corrected_statement: null, proof_note: "p", given_up: "g", ops: [{ op: "narrow", env: "thm:main", gives_up: "g" }] } };
    await expect(readPatchFile(await write({ ...base, patches: [], unfixable: [suggestion] }))).rejects.toThrow(/patches\.json cannot be built into a core[\s\S]*unfixable\.0\.suggested_repair\.ops\.0/);
    // V1's acceptance snapshot reports it and keeps the plain transcription as core.json, never throws
    const dir = await write({ ...base, patches: [p({ ops: [{ op: "insert_after", unit: "u", tex: "t" }] })] });
    await writeFile(path.join(dir, VERIFY_FILES.coreJson), JSON.stringify(core()), "utf8");
    const { snapshotTranscribedCore } = await import("../../src/verify/patches.js");
    await expect(snapshotTranscribedCore(dir, {})).resolves.toMatch(/does not fit the accepted transcription[\s\S]*patches\.0\.ops\.0\.op/);
  });

  it("a patch in the format before replacements (`add_assumptions` / `remove_depends_on`) is refused by name, never stripped", async () => {
    await expect(readPatchFile(await write({ ...base, patches: [p({ ops: [], add_assumptions: [{ id: "ass:x", condition: "c" }] })] }))).rejects.toThrow(
      /patches\.0\.add_assumptions: the format before replacements/,
    );
  });
});

describe("applyPatchFile", () => {
  it("a dependency the repair supersedes is unwired from the repaired statement and its hypothesis list; with no user left it leaves the core", () => {
    const f = patchFile();
    f.patches[0].corrected_statement = "the rate is \\(n^{-1/2}\\) when \\(\\eta < \\hat p < 1 - \\eta\\)";
    f.patches[0].supersedes = ["ass:overlap"];
    const { core: out } = applyPatchFile(core(), f);
    expect(out.statements.find((s) => s.id === "lem:rate")!.depends_on).not.toContain("ass:overlap");
    // with its only user gone the superseded assumption leaves the core
    expect(out.assumptions.map((a) => a.id)).not.toContain("ass:overlap");
    const c = core();
    c.statements.find((s) => s.id === "lem:rate")!.statement = "the rate is \\(n^{-1/2}\\) [Hypotheses: ass:overlap]";
    const g = patchFile();
    g.patches[0].supersedes = ["ass:overlap"];
    expect(applyPatchFile(c, g).core.statements.find((s) => s.id === "lem:rate")!.statement).toBe("the rate is \\(n^{-1/2}\\)");
  });

  it("`drops`: only a result drops, only a node it depends on (a hypothesis or a result); the result is unwired from it, a hypothesis leaving the core once no result uses it", () => {
    const f = patchFile();
    f.patches[0].corrected_statement = "the rate is \\(n^{-1/2}\\) when \\(E[\\psi^2] < \\infty\\)";
    f.patches[0].drops = ["ass:overlap"];
    expect(validatePatchFile(core(), f, ["lem:rate"])).toEqual([]);
    const { core: out } = applyPatchFile(core(), f);
    expect(out.statements.find((s) => s.id === "lem:rate")!.depends_on).toEqual([]);
    expect(out.assumptions).toEqual([]);
    // another result still using it keeps it in the core
    const shared = core();
    shared.statements.find((s) => s.id === "thm:side")!.depends_on.push("ass:overlap");
    expect(applyPatchFile(shared, f).core.assumptions.map((a) => a.id)).toEqual(["ass:overlap"]);
    // a result it no longer relies on is dropped too
    const onResult = patchFile({ patches: [{ node: "thm:main", corrected_statement: "the estimator is asymptotically normal under its own rate", drops: ["lem:rate"], proof_note: "p" }] });
    expect(validatePatchFile(core(), onResult, ["thm:main"])).toEqual([]);
    expect(applyPatchFile(core(), onResult).core.statements.find((s) => s.id === "thm:main")!.depends_on).toEqual([]);
    // a (non-key) result resting on a lemma set aside as unfixable is set aside with it — unless it drops it
    const side = (drops?: string[]) =>
      patchFile({ patches: [{ node: "thm:side", corrected_statement: "the variance estimator is consistent by its own bound", drops, proof_note: "p" }], unfixable: [{ node: "lem:rate", reason: "r" }] });
    expect(applyPatchFile(core(), side()).core.statements.map((s) => s.id)).not.toContain("thm:side");
    expect(applyPatchFile(core(), side(["lem:rate"])).core.statements.map((s) => s.id)).toContain("thm:side");
    // a re-extraction that unwired a dropped hypothesis another result still uses leaves the entry moot:
    // it is removed (from a suggestion too), not refused; one no result uses any more stays, and is
    // accepted — the build removes that hypothesis by it; a name that is no hypothesis stays for the check
    const unwiredCore = core();
    unwiredCore.statements.find((s) => s.id === "lem:rate")!.depends_on = [];
    unwiredCore.statements.find((s) => s.id === "thm:side")!.depends_on.push("ass:overlap");
    const withSuggestion = structuredClone(f);
    withSuggestion.unfixable = [{ node: "thm:main", reason: "r", suggested_repair: { corrected_statement: "weaker", drops: ["ass:overlap"], proof_note: "p" } }] as PatchFile["unfixable"];
    const moot = withoutMootDrops(unwiredCore, withSuggestion);
    expect(moot.removed).toEqual(["lem:rate: ass:overlap", "the suggestion on thm:main: ass:overlap"]);
    expect(moot.file.patches[0].drops).toBeUndefined();
    expect(moot.file.unfixable[0].suggested_repair!.drops).toBeUndefined();
    expect(f.patches[0].drops).toEqual(["ass:overlap"]);
    expect(withoutMootDrops(core(), f)).toEqual({ file: f, removed: [] });
    const orphaned = core();
    orphaned.statements.find((s) => s.id === "lem:rate")!.depends_on = [];
    expect(withoutMootDrops(orphaned, f).removed).toEqual([]);
    expect(validatePatchFile(orphaned, f, ["lem:rate"])).toEqual([]);
    expect(applyPatchFile(orphaned, f).core.assumptions).toEqual([]);
    expect(withoutMootDrops(unwiredCore, patchFile({ patches: [{ ...f.patches[0], drops: ["ass:gone"] }] })).removed).toEqual([]);
    // another result the repair only cites (to compare) may be dropped, so the build leaves it unwired
    // (live cns: a bandwidth comparison with Corollary CI-local)
    expect(validatePatchFile(core(), patchFile({ patches: [{ ...f.patches[0], drops: ["thm:main"] }] }), ["lem:rate"])).toEqual([]);
    // the result itself, drops on a hypothesis's own patch, and drops with the statement left as
    // printed (the result would silently lose a hypothesis) are refused (suggestions too)
    const bad = patchFile({
      patches: [
        { ...f.patches[0], drops: ["lem:rate"] },
        { node: "ass:overlap", corrected_statement: null, drops: ["ass:overlap"], proof_note: "p" },
      ],
      unfixable: [{ node: "thm:side", reason: "r", suggested_repair: { corrected_statement: null, drops: ["ass:overlap"], proof_note: "p" } }],
    });
    expect(validatePatchFile(core(), bad, ["lem:rate"])).toEqual([
      `the patch for "lem:rate" drops "lem:rate", which "lem:rate" does not depend on.`,
      `the patch for "ass:overlap" gives \`drops\`, but "ass:overlap" is not a result: only a result drops a node it no longer uses — set \`drops\` to null.`,
      `(suggested repair) the patch for "thm:side" drops dependencies but leaves the statement as printed: a result drops one only in its corrected statement.`,
    ]);
  });

  it("`adds`: only a result adds, stated in its corrected text, only a hypothesis it does not use yet; the build wires it in", () => {
    const f = patchFile({
      patches: [{ node: "thm:side", corrected_statement: "the variance estimator is consistent under overlap", adds: ["ass:overlap"], proof_note: "p" }],
    });
    expect(validatePatchFile(core(), f, ["thm:side"])).toEqual([]);
    expect(applyPatchFile(core(), f).core.statements.find((s) => s.id === "thm:side")!.depends_on).toEqual(["lem:rate", "ass:overlap"]);
    // a hypothesis one repair drops and another adds stays in the core
    const both = patchFile({ patches: [{ ...patchFile().patches[0], corrected_statement: "the rate is \\(n^{-1/2}\\) when \\(E[\\psi^2] < \\infty\\)", drops: ["ass:overlap"] }, f.patches[0]!] });
    expect(applyPatchFile(core(), both).core.assumptions.map((a) => a.id)).toEqual(["ass:overlap"]);
    // a hypothesis the replacement rewrites (superseded) is wired back when the repair adds it
    const back = patchFile({ patches: [{ ...patchFile().patches[0], corrected_statement: "the rate is \\(n^{-1/2}\\) under overlap", supersedes: ["ass:overlap"], adds: ["ass:overlap"] }] });
    expect(validatePatchFile(core(), back, ["lem:rate"])).toEqual([]);
    expect(applyPatchFile(core(), back).core.statements.find((s) => s.id === "lem:rate")!.depends_on).toEqual(["ass:overlap"]);
    const bad = patchFile({
      patches: [
        { node: "lem:rate", corrected_statement: "the rate is \\(n^{-1/2}\\) under overlap", adds: ["thm:main"], proof_note: "p" },
        { node: "thm:side", corrected_statement: null, adds: ["ass:overlap"], proof_note: "p" },
      ],
    });
    expect(validatePatchFile(core(), bad, ["lem:rate"])).toEqual([
      // a result named under `adds` is told where a used result goes: cited in the text, never listed
      `the patch for "lem:rate" adds "thm:main", which is not an assumption or definition of the core: \`adds\` lists only hypotheses (assumptions, definitions). "thm:main" is a result — a result the corrected statement or proof uses is cited by \\ref of its label in the text; remove it from \`adds\`.`,
      `the patch for "thm:side" adds hypotheses but leaves the statement as printed: a result adds a hypothesis only by imposing it in its corrected statement.`,
    ]);
  });

  it("writes the corrected statement (or an assumption's condition) and the proof change into the core; the input is untouched", () => {
    const f = patchFile();
    f.patches[0].corrected_statement = "the rate is \\(n^{-1/2}\\) uniformly";
    const input = core();
    const { core: out, descoped } = applyPatchFile(input, f);
    expect(descoped.size).toBe(0);
    const lem = out.statements.find((s) => s.id === "lem:rate")!;
    expect(lem.statement).toBe("the rate is \\(n^{-1/2}\\) uniformly");
    expect(lem.proof_tex).toContain("[Proof change (minimal patch): bound $1/\\hat p$ by $1/\\eta$");
    expect(input.statements.find((s) => s.id === "lem:rate")!.statement).toBe("the rate is \\(n^{-1/2}\\)");
    expect(out.statements.find((s) => s.id === "lem:rate")!.depends_on).toEqual(["ass:overlap"]);
    expect(runStructuralGate(out, { allowBookkeeping: true, verbatim: true }).violations).toEqual([]);
    const a = patchFile({ patches: [{ node: "ass:overlap", corrected_statement: "\\(\\eta < \\hat p < 1 - \\eta\\)", proof_note: "replace the one-sided bound" }] });
    expect(applyPatchFile(core(), a).core.assumptions.find((x) => x.id === "ass:overlap")!.condition).toBe("\\(\\eta < \\hat p < 1 - \\eta\\)");
  });

  it("an unfixable side result is descoped with every non-key result resting on it; a key result on its path blocks", () => {
    const side = patchFile({ patches: [], unfixable: [{ node: "prop:aside", reason: "the identity is false for every nontrivial design" }] });
    expect(blockedUnfixable(core(), side)).toEqual([]);
    const { core: out, descoped } = applyPatchFile(core(), side);
    expect([...descoped.keys()]).toEqual(["prop:aside"]);
    expect(out.statements.map((s) => s.id)).not.toContain("prop:aside");

    const onPath = patchFile({ patches: [], unfixable: [{ node: "lem:rate", reason: "no hypothesis restores the rate" }] });
    expect(blockedUnfixable(core(), onPath)).toEqual(["lem:rate"]);
    // thm:side is not key and rests on lem:rate: descoped with it
    expect([...applyPatchFile(core(), onPath).descoped.keys()].sort()).toEqual(["lem:rate", "thm:side"]);
  });

  it("an unfixable assumption leaves the core with the side results it descoped; no edge dangles", () => {
    const c = core();
    c.statements.push({ id: "prop:uses-overlap", kind: "proposition", statement: "s", depends_on: ["ass:overlap"], status: "to-prove" } as Core["statements"][number]);
    // lem:rate (on the key path) also uses ass:overlap, so make the side proposition its only user
    c.statements.find((s) => s.id === "lem:rate")!.depends_on = [];
    c.assumptions[0].used_by = ["prop:uses-overlap"];
    const f = patchFile({ patches: [], unfixable: [{ node: "ass:overlap", reason: "self-contradictory" }] });
    expect(blockedUnfixable(c, f)).toEqual([]);
    const { core: out, descoped } = applyPatchFile(c, f);
    expect([...descoped.keys()]).toEqual(["prop:uses-overlap"]);
    expect(out.assumptions.map((a) => a.id)).not.toContain("ass:overlap");
    expect(runStructuralGate(out, { allowBookkeeping: true, verbatim: true }).violations).toEqual([]);
  });
});


// ---------------------------------------------------------------------------
// V1 PATCH mode
// ---------------------------------------------------------------------------

function fakeCodex(replies: unknown[], calls: CodexRunInput[]): typeof runCodex {
  return (async (input: CodexRunInput) => {
    const sym = symbolReply(input);
    if (sym !== null) return { stdout: sym, stderr: "" };
    const reply = replies[calls.length];
    calls.push(input);
    if (reply === undefined) throw new Error(`unexpected codex call #${calls.length}`);
    return { stdout: JSON.stringify(withOwnerExplanations(reply)), stderr: "" };
  }) as typeof runCodex;
}

async function patchRun(findings: Array<{ id: string; axis: string; detail: string; witness: string | null }>) {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-patch-"));
  tmpDirs.push(repoRoot);
  const runDir = path.join(repoRoot, "doc", "verify", QID);
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  await writeFile(path.join(runDir, VERIFY_FILES.coreJson), JSON.stringify(core(), null, 2), "utf8");
  await writeFile(path.join(runDir, VERIFY_FILES.coreTranscribed), JSON.stringify(core(), null, 2), "utf8");
  await writeFile(path.join(runDir, VERIFY_FILES.flatTex), "\\begin{lemma}the rate\\end{lemma}\n", "utf8");
  await writeToyPaper(runDir, core());
  await writeFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), JSON.stringify({ mode: "patch", round: 1, findings }), "utf8");
  const state = createVerifyInitialState(QID, {
    phase: "init",
    source: { input: "paper.tex", main_file: "main.tex", sha256: "h" },
    targets: null,
    core_sha256: "stale",
    v1_rounds: 1,
    v1_5_rounds: 0,
    findings: [],
    report_path: null,
  });
  const calls: CodexRunInput[] = [];
  const args = (replies: unknown[]) => ({
    repoRoot,
    qid: QID,
    runDir,
    state,
    deps: { runCodex: fakeCodex(replies, calls) },
    dryRun: false,
    log: () => {},
  });
  return { runDir, state, calls, args };
}

/** What the fixer returns: the patch file without the runner-owned fields. */
function reply(f: PatchFile): unknown {
  return f;
}

describe("V1 patch mode", () => {
  const finding = { id: "lem:rate", axis: "correctness", detail: "1/p̂ is unbounded", witness: "p̂ → 0 on a sequence of designs" };

  it("writes the patch file (with the referee's finding attached), rebuilds the core from the transcription, and clears the stale hash", async () => {
    const r = await patchRun([finding]);
    const result = await runStageV1(r.args([reply(patchFile())]));
    expect(result.status).toBe("completed");
    expect(r.calls).toHaveLength(1);
    expect(r.calls[0]).toMatchObject({ reasoningEffort: "high", sandboxMode: "read-only" });
    expect(r.calls[0].model).toMatch(/sol/);
    const saved = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.patches), "utf8"));
    expect(r.state.verify!.paper_errors).toEqual({ "lem:rate": { detail: "1/p̂ is unbounded", witness: expect.any(String) } });
    expect(saved.errors).toBeUndefined(); // the ledger is the runner's, never in the editable file
    const rebuilt = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
    expect(rebuilt.statements.find((s) => s.id === "lem:rate")!.proof_tex).toContain("bound $1/\\hat p$ by $1/\\eta$");
    const transcribed = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.coreTranscribed), "utf8")) as Core;
    expect(transcribed.statements.find((s) => s.id === "lem:rate")!.proof_tex ?? "").not.toContain("bound $1/\\hat p$");
    expect(existsSync(path.join(r.runDir, VERIFY_FILES.v1ReviseDirective))).toBe(false);
    expect(r.state.verify!.core_sha256).toBeNull();
  });

  it("hands mechanical violations back to the fixer once, then accepts the corrected file", async () => {
    const r = await patchRun([finding]);
    const bad = patchFile();
    bad.patches[0].ops = [{ op: "replace", unit: "no-such-unit", tex: "t" }]; // not a unit of the paper
    const result = await runStageV1(r.args([reply(bad), reply(patchFile())]));
    expect(result.status).toBe("completed");
    expect(r.calls).toHaveLength(2);
    expect(r.calls[1].prompt).toContain("VIOLATIONS IN YOUR PREVIOUS REPLY");
    expect(r.calls[1].prompt).toContain('"no-such-unit" is not a unit id of the paper');
  });

  it("checkpoints when the file is still not clean after the retry", async () => {
    const r = await patchRun([finding]);
    const bad = patchFile({ key_results: ["thm:nope"] });
    const result = await runStageV1(r.args([reply(bad), reply(bad)]));
    expect(result.status).toBe("checkpoint");
    expect(existsSync(path.join(r.runDir, VERIFY_FILES.patches))).toBe(false);
  });

  it("stops the run when an unfixable node lies on a key result's path, recording the refutation", async () => {
    const r = await patchRun([finding]);
    const result = await runStageV1(r.args([reply(patchFile({ patches: [], unfixable: [{ node: "lem:rate", reason: "no hypothesis restores it" }] }))]));
    expect(result.status).toBe("failed");
    expect(r.state.verify!.findings).toEqual([
      expect.objectContaining({ node: "lem:rate", kind: "refuted", detail: expect.stringContaining("cannot be repaired") }),
    ]);
  });

  it("a second patch round keeps the paper's original error on the node, not the objection to the first patch", async () => {
    const r = await patchRun([{ id: "lem:rate", axis: "patch rejected", detail: "the first patch is too strong", witness: null }]);
    const first = patchFile();
    r.state.verify!.paper_errors = { "lem:rate": { detail: "1/p̂ is unbounded", witness: "p̂ → 0" } };
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(first), "utf8");
    await writeFile(path.join(r.runDir, VERIFY_FILES.coreTranscribed), JSON.stringify(core(), null, 2), "utf8");
    const result = await runStageV1(r.args([reply(patchFile())]));
    expect(result.status).toBe("completed");
    const saved = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.patches), "utf8"));
    expect(r.state.verify!.paper_errors).toEqual({ "lem:rate": { detail: "1/p̂ is unbounded", witness: "p̂ → 0" } });
    expect(saved.patches).toHaveLength(1);
    expect(r.calls[0].prompt).toContain("=== PATCHES FILE");
    // The fixer's assembled prompt states the TeX rule (user rule 2026-09-25).
    expect(r.calls[0].prompt.replace(/\s+/g, " ")).toContain(TEX_MATH_RULE.replace(/\s+/g, " "));
  });

  it("the ledger keeps a node's witnessed error when the same round also grades it ambiguous", async () => {
    const r = await patchRun([
      { id: "lem:rate", axis: "correctness", detail: "1/p̂ unbounded", witness: "p̂ → 0" },
      { id: "lem:rate", axis: "ambiguity", detail: "which norm?", witness: null },
    ]);
    await runStageV1(r.args([reply(patchFile())]));
    expect(r.state.verify!.paper_errors!["lem:rate"]).toEqual({ detail: "1/p̂ unbounded", witness: "p̂ → 0" });
  });
});

describe("V1 patch mode — an F-stage clarification", () => {
  const PIN = "the rate is for the Euclidean norm";
  const clarify = {
    id: "lem:rate",
    axis: "clarify",
    detail: "[F2.5 reviewer] [statement-wrong] the rate admits two readings (which norm?)",
    witness: null,
    from_stage: "F2.5",
    folds: [{ node: "lem:rate", reading: PIN }],
  };
  const clarified = (): PatchFile =>
    patchFile({
      patches: [{ node: "lem:rate", corrected_statement: "the rate is \\(n^{-1/2}\\) in the Euclidean norm", proof_note: "unchanged" }],
    });

  it("records a clarification (not an error) and tells the fixer to state the reading beside the statement", async () => {
    const r = await patchRun([clarify as never]);
    expect((await runStageV1(r.args([reply(clarified())]))).status).toBe("completed");
    expect(r.state.verify!.paper_errors).toEqual({ "lem:rate": { detail: clarify.detail, witness: null, kind: "clarification" } });
    expect(r.calls[0]!.prompt).toContain("STATING THE INTENDED READING IN `readings`");
    expect(r.calls[0]!.prompt).toContain(PIN);
  });
});

describe("V1 patch mode — the fixer may reject an F-stage finding", () => {
  const fFinding = {
    id: "lem:rate",
    axis: "correctness",
    detail: "[F1.5 reviewer] lem:rate needs overlap bounded away from zero, which the paper does not grant.",
    witness: "lem:rate needs overlap bounded away from zero",
    from_stage: "F1.5",
  };
  const rejection = { node: "lem:rate", reason: "the overlap assumption is stated and used", where_the_paper_grants_it: "Assumption 2, main.tex:15" };

  it("a rejection is recorded for the next V1.5 ruling; the finding stays out of the ledger and the rejection out of the patch file", async () => {
    const r = await patchRun([fFinding as never]);
    const result = await runStageV1(r.args([reply(patchFile({ patches: [], rejected: [rejection] }))]));
    expect(result.status).toBe("completed");
    expect(result.message).toContain("rejected lem:rate");
    expect(r.calls[0]!.prompt).toContain("WHEN AN F-STAGE FINDING IS WRONG");
    expect(r.state.verify!.fixer_rejections).toEqual([
      { node: "lem:rate", axis: "correctness", from_stage: "F1.5", finding: fFinding.detail, witness: fFinding.witness, reason: rejection.reason, where_the_paper_grants_it: rejection.where_the_paper_grants_it },
    ]);
    expect(r.state.verify!.paper_errors ?? {}).toEqual({});
    const saved = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.patches), "utf8"));
    expect(saved.rejected).toBeUndefined();
  });
});

describe("repairs derived from their ops", () => {
  const rep = (tex: string) => [{ op: "replace" as const, unit: "lem:rate/1/1", tex }];
  /** Two nodes printed in one passage (lem:rate's): their repairs address the same units. */
  const sharedScope = async (): Promise<(node: string) => RepairScope> => {
    const r = await patchRun([]);
    const src = (await repairSources(r.runDir))!;
    return () => ({ units: src.units, passage: nodePassage(src, "lem:rate") });
  };

  it("overlapViolations: two repairs replacing overlapping units differently → one violation naming both; identical replacements → none", async () => {
    const scopeOf = await sharedScope();
    const file = (a: string, b: string) => ({
      patches: [{ node: "lem:rate", corrected_statement: null, proof_note: "p", ops: rep(a) }],
      unfixable: [{ node: "thm:main", reason: "r", suggested_repair: { corrected_statement: null, proof_note: "p", given_up: "g", ops: rep(b) } }],
    }) as unknown as Pick<PatchFile, "patches" | "unfixable">;
    const v = overlapViolations(file("the rate is \\(n^{-1/3}\\)", "the rate is \\(n^{-1/4}\\)"), scopeOf);
    expect(v).toHaveLength(1);
    expect(v[0]).toContain('"lem:rate"');
    expect(v[0]).toContain('"thm:main"');
    expect(v[0]).toContain("lem:rate/1/1");
    expect(overlapViolations(file("the rate is \\(n^{-1/3}\\)", "the rate is \\(n^{-1/3}\\)"), scopeOf)).toEqual([]);
    // both replacements are shown; a locked side (a suggestion awaiting the owner) stays, the other follows it
    expect(v[0]).toContain('writes: "the rate is \\\\(n^{-1/3}\\\\)"');
    const locked = overlapViolations(file("the rate is \\(n^{-1/3}\\)", "the rate is \\(n^{-1/4}\\)"), scopeOf, new Set(["thm:main"]));
    expect(locked).toEqual([expect.stringContaining('"thm:main" awaits the owner and stays as it is: give "lem:rate" the same replacement')]);
    expect(overlapViolations(file("the rate is \\(n^{-1/3}\\)", "the rate is \\(n^{-1/4}\\)"), scopeOf, new Set(["thm:main", "lem:rate"]))).toEqual([]);
    // a declined suggestion prints nothing: it clashes with nothing
    const declined = file("the rate is \\(n^{-1/3}\\)", "the rate is \\(n^{-1/4}\\)");
    (declined.unfixable[0] as { declined?: string }).declined = "2026-09-27";
    expect(overlapViolations(declined, scopeOf)).toEqual([]);
  });

  it("readPatchFile derives every repair's texts from its ops: a stored stale corrected_statement is re-derived on read", async () => {
    const r = await patchRun([]);
    const stored = { key_results: ["thm:main"], key_contribution: "k", unfixable: [], patches: [{ node: "lem:rate", corrected_statement: "STALE TEXT", proof_note: "p", ops: rep("the rate is \\(n^{-1/3}\\)") }] };
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(stored), "utf8");
    const f = (await readPatchFile(r.runDir))!;
    expect(f.patches[0]!.corrected_statement).toContain("n^{-1/3}");
    expect(f.patches[0]!.corrected_statement).not.toContain("STALE");
  });

  it("materializeReply: a node whose proof is given (an assumption) gets PROOF_UNCHANGED without a violation; a result without a printed proof owes one", async () => {
    const scopeOf = await sharedScope();
    const given = (n: string) => n === "ass:overlap";
    const ok = materializeReply({ patches: [{ node: "ass:overlap", ops: [], proof_note: null }], unfixable: [] }, scopeOf, given);
    expect(ok.violations).toEqual([]);
    expect((ok.raw as { patches: Array<{ proof_note: string }> }).patches[0]!.proof_note).toBe(PROOF_UNCHANGED);
    const owed = materializeReply({ patches: [{ node: "lem:rate", ops: [], proof_note: null }], unfixable: [] }, scopeOf, given);
    expect(owed.violations).toEqual([expect.stringContaining("prints no proof of this result")]);
  });
});
