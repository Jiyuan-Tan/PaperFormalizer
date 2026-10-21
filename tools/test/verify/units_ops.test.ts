/**
 * Addressable units and replacement repairs (design 2026-09-25, P2; replacement-only 2026-09-26): the
 * units parser (whole sentences, items and displays; a lead-in keeps its display; nested lists and
 * alignment rows stay whole), the ops (schema — `replace` alone —, resolution, materialization of the
 * corrected statement and the amended proof), the fixer's reply in patch mode, and the refusal of a patch
 * file in the format before replacement-only repairs.
 */
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState } from "../../src/state.js";
import { PatchOpSchema, materializeRepair, nodePassage, type PassageSources, type PatchOp } from "../../src/verify/ops.js";
import { PatchFileSchema, materializeReply, normalizeTextlessEntries, readPatchFile } from "../../src/verify/patches.js";
import { RefCoreSchema } from "../../src/verify/ref_core.js";
import { runStageV1 } from "../../src/verify/stage_v1.js";
import { VERIFY_FILES, type EnvsJson } from "../../src/verify/types.js";
import { PaperUnits, regionUnits } from "../../src/verify/units.js";
import { withOwnerExplanations, writeToyPaper } from "./owner_explained.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

/** The units of a text as `kind text` lines (whitespace collapsed). */
const show = (text: string): string[] => regionUnits(text).map((u) => `${u.p}/${u.u} ${u.kind} ${text.slice(u.start, u.end).replace(/\s+/gu, " ")}`);

describe("the units parser: every unit whole", () => {
  it.each([
    ["sentences never cut inside math; a period inside math ends a sentence after the math", "Let $x = 1.$ Then $y$ holds. Also $a.b$ here.", ["1/1 sentence Let $x = 1.$", "1/2 sentence Then $y$ holds.", "1/3 sentence Also $a.b$ here."]],
    ["a lead-in without terminal punctuation keeps its display (one unit)", "Then we have\n$$\nx = 1,\n$$\nwhere $x$ is fixed. Next.", ["1/1 sentence Then we have $$ x = 1, $$ where $x$ is fixed.", "1/2 sentence Next."]],
    ["alignment rows are never split; a display after a full stop stands alone", "Observe.\n\\begin{align*}\n a &= b. \\\\\n c &= d.\n\\end{align*}\nHence done.", ["1/1 sentence Observe.", "1/2 display \\begin{align*} a &= b. \\\\ c &= d. \\end{align*}", "1/3 sentence Hence done."]],
  ])("%s", (_t, text, units) => {
    expect(show(text)).toEqual(units);
  });

  it("a list item is one unit (its sentences and a nested list inside it); its content starts after the \\item head", () => {
    const t = "Assume:\n\\begin{enumerate}\n\\item[(i)] First. Second.\n\\item Outer\n\\begin{itemize}\n\\item inner one\n\\item inner two\n\\end{itemize}\nend.\n\\end{enumerate}\nThen it holds.";
    const us = regionUnits(t);
    expect(show(t)).toEqual([
      "1/1 sentence Assume:",
      "1/2 item \\item[(i)] First. Second.",
      "1/3 item \\item Outer \\begin{itemize} \\item inner one \\item inner two \\end{itemize} end.",
      "1/4 sentence Then it holds.",
    ]);
    expect(t.slice(us[1]!.content, us[1]!.end)).toBe("First. Second.");
    expect(us[1]!.list).toBe(us[2]!.list);
    expect(t.slice(us[1]!.listStart!, us[1]!.listEnd!)).toMatch(/^\\begin\{enumerate\}[\s\S]*\\end\{enumerate\}$/u);
  });

  it("ids and offsets in flat.tex: <env>/<p>/<u>, <env>/proof/<p>/<u>", () => {
    const flat = "\\begin{lemma}\\label{lem:a}\nA holds. B holds.\n\\end{lemma}\n\\begin{proof}\nC. D.\n\\end{proof}\n";
    const envs = { envs: [{ id: "lem:a", kind: "lemma", envName: "lemma", label: "lem:a", title: null, body: "\\label{lem:a}\nA holds. B holds.\n", proof: "\nC. D.\n", proofLines: { file: "m", from: 4, to: 6 }, section: null, lines: { file: "m", from: 1, to: 3 }, refs: [] }] } as unknown as EnvsJson;
    const u = PaperUnits.parse(flat, envs);
    expect(u.unitsOf("lem:a").map((x) => `${x.id}=${u.textOf(x)}`)).toEqual(["lem:a/1/1=A holds.", "lem:a/1/2=B holds."]);
    expect(u.unitsOf("lem:a", "proof").map((x) => `${x.id}=${u.textOf(x)}`)).toEqual(["lem:a/proof/1/1=C.", "lem:a/proof/1/2=D."]);
    expect(flat.slice(u.unitById("lem:a/1/2")!.start, u.unitById("lem:a/1/2")!.end)).toBe("B holds.");
  });
});

// ---------------------------------------------------------------------------------------------
// ops on a small paper
// ---------------------------------------------------------------------------------------------

const BODY = "\\label{lem:a}\nSuppose $x > 0$. Assume:\n\\begin{enumerate}\n\\item $f$ is bounded.\n\\item $g$ is smooth.\n\\end{enumerate}\nThen $h(x) \\le 1$.\n";
const PROOF = "\nBy the first item, $f \\le c$. Hence $h \\le c$. \\qed\n";
function paper(): PassageSources {
  const flat = `\\begin{lemma}${BODY}\\end{lemma}\n\\begin{proof}${PROOF}\\end{proof}\n`;
  const envs = { envs: [{ id: "lem:a", kind: "lemma", envName: "lemma", label: "lem:a", title: null, body: BODY, proof: PROOF, proofLines: { file: "m", from: 9, to: 11 }, section: null, lines: { file: "m", from: 1, to: 8 }, refs: [] }] } as unknown as EnvsJson;
  const refs = RefCoreSchema.parse({ qid: "q", target_estimand: "t", statements: [{ id: "lem:a", kind: "lemma", env: "lem:a" }] });
  return { units: PaperUnits.parse(flat, envs), refs, statements: [{ id: "lem:a", depends_on: [] }], envs };
}
const scope = (src: PassageSources) => ({ units: src.units, passage: nodePassage(src, "lem:a") });
const ops = (x: unknown[]): PatchOp[] => x.map((o) => PatchOpSchema.parse(o));

describe("ops: resolution and materialization", () => {
  it("replacements (an item's content, a hypothesis added by restating the conclusion's sentence with it, a run over a whole list): the corrected statement is the printed text with the ops applied", () => {
    const src = paper();
    const m = materializeRepair(
      ops([
        { op: "replace", unit: "lem:a/1/4", tex: "$g$ is twice differentiable." },
        { op: "replace", unit: "lem:a/1/5", tex: "Suppose also $x < 1$. Then $h(x) \\le 2$." },
      ]),
      scope(src),
      "w",
    );
    expect(m.problems).toEqual([]);
    expect(m.corrected_statement).toBe("Suppose $x > 0$. Assume:\n\\begin{enumerate}\n\\item $f$ is bounded.\n\\item $g$ is twice differentiable.\n\\end{enumerate}\nSuppose also $x < 1$. Then $h(x) \\le 2$.");
    expect(m.proof).toBeNull();
    // no statement op: no corrected statement; a proof step added by replacing the step it follows with
    // both (the QED mark stays after it)
    const p = materializeRepair(ops([{ op: "replace", unit: "lem:a/proof/1/2", tex: "Hence $h \\le c$. So $h$ is bounded." }]), scope(src), "w");
    expect(p).toMatchObject({ corrected_statement: null, proof: "By the first item, $f \\le c$. Hence $h \\le c$. So $h$ is bounded. \\qed", problems: [] });
    // a run of several units takes every list it touches whole
    const whole = materializeRepair(ops([{ op: "replace", unit: "lem:a/1/2", to: "lem:a/1/4", tex: "Assume $f$ bounded and $g$ smooth." }]), scope(src), "w");
    expect(whole.corrected_statement).toBe("Suppose $x > 0$. Assume $f$ bounded and $g$ smooth.\nThen $h(x) \\le 1$.");
  });

  it("replace is the one operation: an insertion, a deletion, an added hypothesis or a narrowing does not parse", () => {
    for (const o of [
      { op: "insert_after", unit: "lem:a/1/1", tex: "y" },
      { op: "delete", unit: "lem:a/1/1" },
      { op: "add_hypothesis", target: "lem:a", tex: "h" },
      { op: "replace_conclusion", env: "lem:a", tex: "c" },
      { op: "narrow", env: "lem:a", gives_up: "g" },
    ]) expect(PatchOpSchema.safeParse(o).success, o.op).toBe(false);
    expect(PatchOpSchema.parse({ op: "replace", unit: "lem:a/1/1", to: " ", tex: "x" })).toEqual({ op: "replace", unit: "lem:a/1/1", tex: "x" });
  });

  it("violations: an unknown unit, an item's tex with its own \\item, two ops on overlapping units, a run ending before it starts, a run taking part of a list", () => {
    const src = paper();
    const v = (x: unknown[]): string[] => materializeRepair(ops(x), scope(src), "the patch").problems;
    expect(v([{ op: "replace", unit: "lem:zz/1/1", tex: "x" }])).toEqual([expect.stringContaining('"lem:zz/1/1" is not a unit id of the paper')]);
    expect(v([{ op: "replace", unit: "lem:a/1/3", tex: "\\item x" }])).toEqual([expect.stringContaining("the runner keeps its \\item")]);
    expect(v([{ op: "replace", unit: "lem:a/1/1", tex: "x" }, { op: "replace", unit: "lem:a/1/1", tex: "y" }])).toEqual([expect.stringContaining("replace overlapping units")]);
    expect(v([{ op: "replace", unit: "lem:a/1/5", to: "lem:a/1/1", tex: "x" }])).toEqual([expect.stringContaining("is not a unit at or after")]);
    expect(v([{ op: "replace", unit: "lem:a/1/2", to: "lem:a/1/3", tex: "x" }])).toEqual([expect.stringContaining("takes some items of a list and not others")]);
  });

  it("the reply: texts derived from the ops, a proof note where the paper prints none, a suggestion's given_up from its note (none given up: absent)", () => {
    const src = paper();
    const suggestion = { ops: [{ op: "replace", unit: "lem:a/1/5", to: null, tex: "Then $h(x) \\le 3$." }], proof_note: null };
    const raw = {
      patches: [{ node: "lem:a", ops: [{ op: "replace", unit: "lem:a/proof/1/2", to: null, tex: "Hence $h \\le 2c$." }], proof_note: null }],
      unfixable: [{ node: "lem:a", reason: "r", suggested_repair: suggestion }],
    };
    const d = materializeReply(raw, () => scope(src), () => true);
    expect(d.violations).toEqual([]);
    expect((d.raw as { unfixable: Array<{ suggested_repair: { given_up?: string } }> }).unfixable[0]!.suggested_repair.given_up).toBeUndefined();
    const r = d.raw as { patches: Array<{ corrected_statement: string | null; proof_note: string }> };
    expect(r.patches[0]!.corrected_statement).toBeNull();
    expect(r.patches[0]!.proof_note).toBe("By the first item, $f \\le c$. Hence $h \\le 2c$. \\qed");
    const given = materializeReply({ patches: [], unfixable: [{ node: "lem:a", reason: "r", suggested_repair: suggestion, owner_explanation: { gives_up: " the bound 1 " } }] }, () => scope(src), () => true);
    expect(given.violations).toEqual([]);
    const sr = (given.raw as { unfixable: Array<{ suggested_repair: { given_up: string; corrected_statement: string } }> }).unfixable[0]!.suggested_repair;
    expect(sr.given_up).toBe("the bound 1");
    expect(sr.corrected_statement).toContain("Then $h(x) \\le 3$.");
    expect(materializeReply({ patches: [{ node: "lem:a", ops: [], proof_note: null }], unfixable: [] }, () => scope(src), () => false).violations).toEqual([expect.stringContaining("prints no proof of this result — give the full proof")]);
  });

  it("a detail (\\vsDetail) rides in the amended proof the referee and the Lean stages read; a statement, a reading or a block's statement takes none", () => {
    const src = paper();
    const step = { op: "replace", unit: "lem:a/proof/1/2", to: null, tex: "Hence $h \\le 2c$.\\vsDetail{As $h = 2f$ and $f \\le c$.}" };
    const d = materializeReply({ patches: [{ node: "lem:a", ops: [step], proof_note: null }], unfixable: [] }, () => scope(src), () => true);
    expect(d.violations).toEqual([]);
    expect((d.raw as { patches: Array<{ proof_note: string }> }).patches[0]!.proof_note).toContain("Hence $h \\le 2c$.\\vsDetail{As $h = 2f$ and $f \\le c$.}");
    const stmt = { op: "replace", unit: "lem:a/1/5", to: null, tex: "Then $h(x) \\le 3$.\\vsDetail{x}" };
    expect(materializeReply({ patches: [{ node: "lem:a", ops: [stmt], proof_note: null }], unfixable: [] }, () => scope(src), () => true).violations).toEqual([expect.stringContaining("replaces text of the statement and holds a `\\vsDetail`")]);
    const reading = { node: "lem:a", ops: [step], proof_note: null, readings: ["$h$ is measurable.\\vsDetail{x}"] };
    expect(materializeReply({ patches: [reading], unfixable: [] }, () => scope(src), () => true).violations).toEqual([expect.stringContaining("a reading or a block's statement holds a `\\vsDetail`")]);
  });

});

// ---------------------------------------------------------------------------------------------
// patch mode: the fixer returns ops
// ---------------------------------------------------------------------------------------------

describe("patch mode: the fixer's reply is ops", () => {
  const core = (): Core =>
    ({
      qid: "po",
      symbols: [],
      assumptions: [],
      definitions: [],
      statements: [{ id: "lem:g", kind: "lemma", statement: "The bound $\\sigma \\ge c$ holds.", depends_on: [], status: "to-prove", proof_tex: "By Assumption 1, $E[U] = 0$. Hence the cross term vanishes. The bound follows." }],
      target_estimand: "t",
    }) as unknown as Core;
  async function run(replies: unknown[]) {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "v1-ops-"));
    tmp.push(repoRoot);
    const runDir = path.join(repoRoot, "runs", "po");
    await mkdir(path.join(runDir, "discovery"), { recursive: true });
    for (const f of [VERIFY_FILES.coreJson, VERIFY_FILES.coreTranscribed]) await writeFile(path.join(runDir, f), JSON.stringify(core(), null, 2));
    await writeToyPaper(runDir, core());
    const finding = { id: "lem:g", axis: "correctness", detail: "the cross term is dropped", witness: "a projection model" };
    await writeFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), JSON.stringify({ mode: "patch", round: 1, findings: [finding] }));
    const state = createVerifyInitialState("po", { phase: "init", source: { input: "p.tex", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
    state.verify!.paper_errors = { "lem:g": { detail: finding.detail, witness: finding.witness } };
    const calls: CodexRunInput[] = [];
    const codex = (async (input: CodexRunInput) => {
      const r = replies[calls.length];
      calls.push(input);
      if (r === undefined) throw new Error(`unexpected call #${calls.length}`);
      return { stdout: JSON.stringify(withOwnerExplanations(r)), stderr: "" };
    }) as typeof runCodex;
    const res = await runStageV1({ repoRoot, qid: "po", runDir, state, deps: { runCodex: codex }, dryRun: false, log: () => {} });
    return { runDir, calls, res };
  }
  const reply = (o: unknown[]) => ({ key_results: ["lem:g"], key_contribution: "c", patches: [{ node: "lem:g", ops: o, proof_note: null }], unfixable: [], rejected: [] });

  it("the PAPER UNITS block shows the units; an op that does not resolve goes back; the file keeps the ops and the texts derived from them", async () => {
    const good = [{ op: "replace", unit: "lem:g/proof/1/2", to: null, tex: "The cross term is bounded by Cauchy--Schwarz." }];
    const r = await run([reply([{ op: "replace", unit: "lem:g/proof/1/9", to: null, tex: "x" }]), reply(good)]);
    expect(r.res.status).toBe("completed");
    expect(r.calls[0]!.prompt).toContain("=== PAPER UNITS");
    expect(r.calls[0]!.prompt).toContain("[lem:g/proof/1/2] Hence the cross term vanishes.");
    expect(r.calls[1]!.prompt).toContain('(ops) the patch for "lem:g": ops[0] (replace): "lem:g/proof/1/9" is not a unit id of the paper');
    const raw = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.patches), "utf8"));
    const saved = PatchFileSchema.parse(raw);
    expect(saved.patches[0]!.ops).toEqual([{ op: "replace", unit: "lem:g/proof/1/2", tex: "The cross term is bounded by Cauchy--Schwarz." }]);
    expect(saved.patches[0]!.proof_note).toBe("By Assumption 1, $E[U] = 0$. The cross term is bounded by Cauchy--Schwarz. The bound follows.");
    const built = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
    expect(built.statements[0]!.proof_tex).toContain("The cross term is bounded by Cauchy--Schwarz.");
    await expect(readPatchFile(r.runDir)).resolves.toMatchObject({ patches: [{ node: "lem:g" }] });
  });

  it("a patch file with an op that is no replacement is refused: reading it names the operator's file and the path", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "v1-ops-old-"));
    tmp.push(repoRoot);
    const runDir = path.join(repoRoot, "runs", "po");
    await mkdir(path.join(runDir, "discovery"), { recursive: true });
    for (const f of [VERIFY_FILES.coreJson, VERIFY_FILES.coreTranscribed]) await writeFile(path.join(runDir, f), JSON.stringify(core(), null, 2));
    const old = { key_results: ["lem:g"], key_contribution: "c", patches: [{ node: "lem:g", corrected_statement: null, add_assumptions: [], remove_depends_on: [], ops: [{ op: "insert_after", unit: "lem:g/proof/1/2", tex: "x" }], proof_note: "p" }], unfixable: [] };
    await writeFile(path.join(runDir, VERIFY_FILES.patches), JSON.stringify(old));
    await writeFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), JSON.stringify({ mode: "patch", round: 1, findings: [{ id: "lem:g", axis: "correctness", detail: "d", witness: null }] }));
    const state = createVerifyInitialState("po", { phase: "init", source: { input: "p.tex", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
    await expect(readPatchFile(runDir)).rejects.toThrow(/patches\.json cannot be built into a core[\s\S]*patches\.0\.ops\.0\.op/u);
    // patch mode checkpoints on it with the same message, before any model call
    const res = await runStageV1({ repoRoot, qid: "po", runDir, state, deps: { runCodex: (async () => { throw new Error("no model call expected"); }) as unknown as typeof runCodex }, dryRun: false, log: () => {} });
    expect(res.status).toBe("checkpoint");
    expect(res.message).toContain("patches.json cannot be built into a core");
    // empty records from an older writer are stripped silently
    await writeFile(path.join(runDir, VERIFY_FILES.patches), JSON.stringify({ ...old, patches: [{ ...old.patches[0], ops: [{ op: "replace", unit: "lem:g/proof/1/2", tex: "x" }] }] }));
    await expect(readPatchFile(runDir)).resolves.toMatchObject({ patches: [{ node: "lem:g", ops: [{ op: "replace" }] }] });
  });
});

describe("normalizeTextlessEntries: the entry of a hypothesis with no printed text of its own", () => {
  const note = { claim: "c", defects: [], why: { objects: [], consequence: "q" }, fix: "f", gives_up: "the case n = 1" };
  const textless = (n: string) => n === "def:inner";

  it("an unfixable entry (with a suggestion) or an ops-less patch becomes a patch with no ops whose note gives nothing up; a patch with ops and every other node are left alone", () => {
    const raw = { patches: [], unfixable: [{ node: "def:inner", reason: "r", suggested_repair: { ops: [{ op: "replace", unit: "def:inner/1/1", tex: "x" }], proof_note: null }, owner_explanation: note }, { node: "thm:a", reason: "r", suggested_repair: null, owner_explanation: note }] };
    const out = normalizeTextlessEntries(raw, textless);
    expect(out.nodes).toEqual(["def:inner"]);
    expect(out.raw).toMatchObject({ patches: [{ node: "def:inner", ops: [], proof_note: null, owner_explanation: { ...note, gives_up: null } }], unfixable: [{ node: "thm:a" }] });
    expect(raw.unfixable).toHaveLength(2); // the input is not changed
    // an ops-less patch keeps its note with gives_up null; a patch with ops and every other node are left alone
    const raw2 = { patches: [{ node: "def:inner", ops: [], owner_explanation: note }, { node: "thm:a", ops: [], owner_explanation: note }], unfixable: [] };
    const out2 = normalizeTextlessEntries(raw2, textless) as { raw: { patches: Array<{ owner_explanation: { gives_up: string | null } }> }; nodes: string[] };
    expect(out2.nodes).toEqual(["def:inner"]);
    expect(out2.raw.patches.map((p) => p.owner_explanation.gives_up)).toEqual([null, "the case n = 1"]);
    const withOps = { patches: [{ node: "def:inner", ops: [{ op: "replace", unit: "u", tex: "x" }], owner_explanation: note }], unfixable: [] };
    expect(normalizeTextlessEntries(withOps, textless).nodes).toEqual([]);
  });
});
