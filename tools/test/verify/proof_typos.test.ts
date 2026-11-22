/**
 * Typos of proofs (owner decision 2026-11-15): a slip in a PROOF that the derivation plainly corrects and
 * that leaves the result true is no grade — the referee lists it in its verdict's `typos`, and the runner
 * corrects the printed proof with it the way a repair's replacements do (`patches.json` `typo_fixes`, ops
 * on the proof's units), with no finding, no fixer round, no owner decision and no grade. The corrected
 * paper prints the correction; the report lists it apart; a snippet the proof does not print exactly once
 * in one step is reported only.
 */
import { existsSync, readFileSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState } from "../../src/state.js";
import { applyEdits, planAnnotations, type AnnotationInput } from "../../src/verify/annotated_paper.js";
import { TYPO_FIX_MARKER, buildCore } from "../../src/verify/core_graph.js";
import { correctedTex } from "../../src/verify/corrected_tex.js";
import type { PassageSources } from "../../src/verify/ops.js";
import { PatchFileSchema, deriveTypoProofs, onlyTypoFixes, withRefereeTypos, type PatchFile } from "../../src/verify/patches.js";
import { buildReport, reportTypos } from "../../src/verify/report.js";
import { runStageV1_5 } from "../../src/verify/stage_v1_5.js";
import { VERIFY_FILES, type V15NodeVerdict, type V15Review } from "../../src/verify/types.js";
import { PaperUnits, flatLineStart } from "../../src/verify/units.js";
import { NODE_FIELDS_TEXT, NodeVerdictSchema, V15_NODE_REPLY } from "../../src/verify/v1_5_schema.js";
import { pinOwnerEntries } from "../../src/verify/weakening.js";
import { writeToyPaper } from "./owner_explained.js";
import { isRefereeCall, isRefereeGlobal, shardedRefereeReply, type WholeCoreReply } from "./referee_fake.js";
import { symbolReply } from "./symbol_fake.js";

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

const ok = (id: string, over: Partial<V15NodeVerdict> = {}): V15NodeVerdict => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "reproduced", witness: null, bookkeeping_assumption: null, reading: null, ...over });

// ---------------------------------------------------------------------------------------------
// A one-theorem paper whose proof has a typo in its first step
// ---------------------------------------------------------------------------------------------

const STEP1 = "First, $E[X_n] \\to \\mu$ by the law of large numbers, read from left to right.";
const STEP2 = "Then $\\hat\\theta - \\theta = O_p(n^{-1/2})$ follows, as $\\theta$ is fixed.";
const PROOF = `${STEP1}\n${STEP2}`;
const FLAT = [
  "\\documentclass{article}",
  "\\begin{document}",
  "\\begin{theorem}\\label{thm:a}",
  "The estimator is consistent.",
  "\\end{theorem}",
  "\\begin{proof}",
  STEP1,
  STEP2,
  "\\end{proof}",
  "\\end{document}",
].join("\n");
const LINE_MAP = FLAT.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 }));
const ENVS = {
  main_file: "main.tex",
  files: ["main.tex"],
  newtheorem: {},
  envs: [{ id: "thm:a", kind: "theorem", envName: "theorem", label: "thm:a", title: null, body: "The estimator is consistent.", proof: PROOF, proofLines: { file: "main.tex", from: 6, to: 9, env: "proof" }, section: null, lines: { file: "main.tex", from: 3, to: 5 }, refs: [] }],
  bibliography: [],
} as never;

function core(): Core {
  return {
    qid: "pf",
    symbols: [],
    assumptions: [],
    definitions: [],
    statements: [{ id: "thm:a", kind: "theorem", statement: "The estimator is consistent.", depends_on: [], proof_tex: PROOF, status: "to-prove", tex_locator: { file: "main.tex", from: 3, to: 5, env: "theorem", label: "thm:a" } }],
    target_estimand: "t",
    bibliography: [],
  } as unknown as Core;
}

function sources(): PassageSources {
  return { units: PaperUnits.parse(FLAT, ENVS, flatLineStart(FLAT, LINE_MAP)), refs: null, statements: core().statements, envs: ENVS };
}

const LEFT = { printed: "read from left to right", intended: "read from right to left", reason: "the comparison runs the other way" };

describe("the referee's `typos` field", () => {
  it("is in the reply schema and the field list; a verdict written before it reads as none", () => {
    expect(V15_NODE_REPLY.required as string[]).toContain("typos");
    expect(NODE_FIELDS_TEXT).toMatch(/^ {6}typos {2,}/mu);
    expect(NodeVerdictSchema.parse(ok("thm:a")).typos).toEqual([]);
    expect(NodeVerdictSchema.parse({ ...ok("thm:a"), typos: [LEFT] }).typos).toEqual([LEFT]);
    const brief = readFileSync(path.join(path.dirname(fileURLToPath(import.meta.url)), "..", "..", "src", "verify", "prompts", "V1.5", "review.txt"), "utf8").replace(/\s+/gu, " ");
    expect(brief).toContain("is a TYPO: list it in `typos`");
    expect(brief).toContain("A typo changes no grade");
  });
});

describe("a typo becomes a replacement of the proof step that prints it", () => {
  it("located exactly once: one op on that unit, the snippet swapped; listing it again changes nothing", () => {
    const src = sources();
    const [u1] = src.units.unitsOf("thm:a", "proof");
    const r = withRefereeTypos(null, [ok("thm:a", { typos: [LEFT] })], src);
    expect(r.added).toEqual([{ node: "thm:a", ...LEFT, unit: u1!.id }]);
    const fix = r.file!.typo_fixes![0]!;
    expect(fix.ops).toEqual([{ op: "replace", unit: u1!.id, tex: STEP1.replace("left to right", "right to left") }]);
    // the derived proof: the printed proof with the step corrected
    expect(fix.proof_note).toBe(PROOF.replace("left to right", "right to left"));
    // a file the runner wrote for typos alone owes the ledger nothing; it round-trips through the schema
    expect(onlyTypoFixes(r.file!)).toBe(true);
    expect(PatchFileSchema.parse(JSON.parse(JSON.stringify(r.file)))).toEqual(r.file);
    const again = withRefereeTypos(r.file, [ok("thm:a", { typos: [{ ...LEFT, reason: "said again" }] })], src);
    expect(again.added).toEqual([]);
    expect(again.file).toBe(r.file);
    // a pass that does not list it drops nothing
    expect(withRefereeTypos(r.file, [ok("thm:a")], src).file).toBe(r.file);
  });

  it("not printed, or printed twice, or in no proof: recorded with no unit and no op (reported only)", () => {
    const src = sources();
    const typos = [
      { printed: "law of small numbers", intended: "law of large numbers", reason: "absent" },
      { printed: "\\theta", intended: "\\vartheta", reason: "printed three times" },
      { printed: "is consistent", intended: "is efficient", reason: "a statement's text is no proof" },
      { printed: "fixed", intended: "fixed", reason: "changes nothing" },
    ];
    const r = withRefereeTypos(null, [ok("thm:a", { typos })], src);
    expect(r.added.map((a) => [a.printed, a.unit])).toEqual([
      ["law of small numbers", null],
      ["\\theta", null],
      ["is consistent", null],
    ]);
    const fix = r.file!.typo_fixes![0]!;
    expect(fix.ops).toEqual([]);
    expect(fix.proof_note).toBeUndefined();
    // nothing applies: the core's proof is the printed one
    const built = buildCore(core(), { patches: r.file });
    expect(built.core.statements[0]!.proof_tex).toBe(PROOF);
  });

  it("the core's proof carries the correction (the statement does not change); a repair's op on the same step wins", () => {
    const src = sources();
    const r = withRefereeTypos(null, [ok("thm:a", { typos: [LEFT] })], src);
    const st = buildCore(core(), { patches: r.file }).core.statements[0]!;
    expect(st.statement).toBe("The estimator is consistent.");
    expect(st.proof_tex!.startsWith(TYPO_FIX_MARKER)).toBe(true);
    expect(st.proof_tex).toContain(PROOF.replace("left to right", "right to left"));
    expect(st.proof_tex).not.toContain("[Proof change (minimal patch):");
    // with a repair revising the other step: one proof, both changes, under the repair's marker
    const [u1, u2] = src.units.unitsOf("thm:a", "proof");
    const repaired = (unit: string, tex: string): PatchFile => deriveTypoProofs({ ...r.file!, patches: [{ node: "thm:a", corrected_statement: null, ops: [{ op: "replace", unit, tex }], proof_note: "derived" }] } as PatchFile, (n) => ({ units: src.units, passage: { env: "thm:a", units: src.units.unitsOf(n) } }));
    const both = buildCore(core(), { patches: repaired(u2!.id, "Then the bias bound gives $O_p(n^{-1/3})$.") }).core.statements[0]!;
    expect(both.proof_tex).toContain("[Proof change (minimal patch): the printed proof, revised step by step]");
    expect(both.proof_tex).toContain("read from right to left.\nThen the bias bound gives $O_p(n^{-1/3})$.");
    // a repair replacing the step the typo is in: its text stands, the typo op gives way
    const over = repaired(u1!.id, "First, the mean converges.");
    expect(over.typo_fixes![0]!.proof_note).toBeUndefined();
  });

  it("a fixer reply never carries the typo fixes and never drops them", () => {
    const src = sources();
    const prior = withRefereeTypos(null, [ok("thm:a", { typos: [LEFT] })], src).file!;
    const reply = PatchFileSchema.parse({ key_results: ["thm:a"], key_contribution: "c", patches: [], unfixable: [] });
    expect(pinOwnerEntries(reply, prior).typo_fixes).toEqual(prior.typo_fixes);
  });
});

describe("the annotated and the corrected paper", () => {
  const input = (patches: AnnotationInput["patches"], over: Partial<AnnotationInput> = {}): AnnotationInput => ({
    files: { "main.tex": FLAT },
    envs: ENVS,
    flatText: FLAT,
    lineMap: LINE_MAP,
    refs: null,
    transcribed: core(),
    core: core(),
    patches,
    paperErrors: {},
    findings: [],
    review: null,
    ...over,
  });

  it("the step is marked as a corrected step, and the corrected paper prints the intended text", () => {
    const fixFile = withRefereeTypos(null, [ok("thm:a", { typos: [LEFT] })], sources()).file!;
    const plan = planAnnotations(input(fixFile));
    const annotated = applyEdits(FLAT, plan.edits["main.tex"] ?? []);
    expect(annotated).toMatch(/\\vsStep\{[^}]*read from left to right\.\}/u);
    // its own label: a typo corrected, no repair ("Corrected typo:", never "Revised:")
    expect(annotated).toMatch(/\\vsTypoStep\{[^}]*read from right to left\.\}/u);
    expect(annotated).not.toContain("\\vsCorrectedStep{");
    // never awaiting a decision; the index says what changed
    const rec = plan.records.find((x) => x.node === "thm:a")!;
    expect(rec.kind).toBe("corrected proof");
    expect(rec.summary).toContain("typos corrected in the proof of thm:a: read from left to right -> read from right to left");
    expect(plan.records.some((x) => x.kind === "awaiting decision")).toBe(false);
    const view = applyEdits(FLAT, planAnnotations(input(fixFile, { correctedView: true })).edits["main.tex"] ?? []);
    const corrected = correctedTex(view, { proofEnv: true });
    expect(corrected.tex).toContain(STEP1.replace("left to right", "right to left"));
    expect(corrected.tex).not.toContain("left to right");
    expect(corrected.tex).toContain(STEP2);
    expect(corrected.items).toEqual([]);
  });

  it("a typo reported only marks nothing", () => {
    const fixFile = withRefereeTypos(null, [ok("thm:a", { typos: [{ printed: "law of small numbers", intended: "x", reason: "r" }] })], sources()).file!;
    const plan = planAnnotations(input(fixFile));
    expect(plan.records).toEqual([]);
  });
});

describe("the report", () => {
  it("lists the typos apart — corrected or reported only — and they count toward no grade", () => {
    const fixFile = withRefereeTypos(null, [ok("thm:a", { typos: [LEFT, { printed: "law of small numbers", intended: "law of large numbers", reason: "absent" }] })], sources()).file!;
    const review: V15Review = { verdict: "PASS", summary: "s", nodes: [ok("thm:a", { typos: [LEFT, { printed: "a slip a later pass saw", intended: "b", reason: "r" }] })] };
    expect(reportTypos(fixFile.typo_fixes!, review.nodes).map((t) => [t.printed, t.corrected])).toEqual([
      ["read from left to right", true],
      ["law of small numbers", false],
      ["a slip a later pass saw", false],
    ]);
    const { json, md } = buildReport({
      qid: "pf",
      envs: { main_file: "main.tex", files: [], envs: [] } as never,
      scope: [],
      core: buildCore(core(), { patches: fixFile }).core,
      transcribed: core(),
      review,
      findings: [],
      addedAssumptions: [],
      crosswalk: null,
      graph: null,
      lean: null,
      warnings: { lint: [], parser: [] },
      flags: {},
      stageCompleted: "V1.5",
      earlyStop: true,
      sourceSha256: "h",
      inputs: { v1_5_review: "", crosswalk_full: "", graph_json: "", v1_scope: "", lean_evidence: "" },
      patches: fixFile,
    } as never);
    expect(json.typos).toHaveLength(3);
    expect(json.paper_grade!.grade).toBe("error_free");
    expect(md).toContain("## Proof slips corrected");
    expect(md).toContain("- `thm:a`: read from left to right → read from right to left — the comparison runs the other way");
    expect(md).toContain("law of small numbers → law of large numbers — absent (not corrected:");
    // no proof change is reported for a typo
    expect(json.results.every((r) => !r.change?.proof_change)).toBe(true);
  });
});

// ---------------------------------------------------------------------------------------------
// The stage: a typo is the referee's alone — no finding, no round, no checkpoint
// ---------------------------------------------------------------------------------------------

const SUM_PROOF = "By the moment bound, $a_n \\le C n^{-2}$ for every $n$.\nSumming from left to right gives $\\sum_n a_n < \\infty$.";

function stageCore(): Core {
  return {
    qid: "typo",
    symbols: [{ name: "a_n", type: "real sequence" }],
    assumptions: [],
    definitions: [],
    statements: [{ id: "thm:sum", kind: "theorem", statement: "The series $\\sum_n a_n$ converges.", depends_on: [], proof_tex: SUM_PROOF, status: "to-prove" }],
    target_estimand: "t",
    bibliography: [],
  } as unknown as Core;
}

async function setup() {
  const root = await mkdtemp(path.join(os.tmpdir(), "verify-typo-"));
  tmpDirs.push(root);
  const runDir = path.join(root, "runs", "typo");
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  for (const f of [VERIFY_FILES.coreJson, VERIFY_FILES.coreTranscribed]) await writeFile(path.join(runDir, f), JSON.stringify(stageCore(), null, 2));
  await writeToyPaper(runDir, stageCore());
  const state = createVerifyInitialState("typo", { phase: "v1", source: { input: "p", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
  const calls: CodexRunInput[] = [];
  let next = 0;
  const codex = (replies: unknown[]) =>
    (async (input: CodexRunInput) => {
      const sym = symbolReply(input);
      if (sym !== null) return { stdout: sym, stderr: "" };
      calls.push(input);
      const reply = replies[next];
      if (reply === undefined || !isRefereeCall(input)) throw new Error(`unexpected call #${calls.length}`);
      if (isRefereeGlobal(input)) next += 1;
      return { stdout: shardedRefereeReply(input, reply as WholeCoreReply)!, stderr: "" };
    }) as typeof runCodex;
  const args = (replies: unknown[]) => ({ repoRoot: root, qid: "typo", runDir, state, deps: { runCodex: codex(replies) }, dryRun: false, log: () => {} });
  const builtCore = async (): Promise<Core> => JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
  const patches = async (): Promise<PatchFile> => JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.patches), "utf8")) as PatchFile;
  return { runDir, state, calls, args, builtCore, patches };
}

const SUM_TYPO = { printed: "Summing from left to right", intended: "Summing over $n$", reason: "the sum has no direction" };
const passWith = (typos: V15NodeVerdict["typos"]) => ({ verdict: "PASS", summary: "reproduced", nodes: [ok("thm:sum", { typos })], patch_review: null, rejection_verdicts: null });

describe("runStageV1_5 — a proof's typo", () => {
  it("PASSes as it would without it: no finding, no ledger entry, no directive; the accepted core's proof carries the correction", async () => {
    const r = await setup();
    const res = await runStageV1_5(r.args([passWith([SUM_TYPO])]));
    expect(res.status).toBe("completed");
    expect(res.message).toContain("1 typo(s) of proofs corrected");
    expect(r.state.verify!.paper_errors ?? {}).toEqual({});
    expect(r.state.verify!.findings.filter((f) => f.node === "thm:sum")).toEqual([]);
    expect(r.state.verify!.patch_rounds ?? 0).toBe(0);
    expect(r.state.verify!.weakening_repair ?? null).toBeNull();
    expect(existsSync(path.join(r.runDir, VERIFY_FILES.v1ReviseDirective))).toBe(false);
    // one referee pass, no fixer
    expect(r.calls.every(isRefereeCall)).toBe(true);
    const file = await r.patches();
    expect(file.patches).toEqual([]);
    expect(file.typo_fixes![0]!.typos[0]!.unit).not.toBeNull();
    const st = (await r.builtCore()).statements.find((s) => s.id === "thm:sum")!;
    expect(st.statement).toBe("The series $\\sum_n a_n$ converges.");
    // the marker line names the swap; the proof below it is the corrected one
    const [marker, ...proof] = st.proof_tex!.split("\n");
    expect(marker).toBe("[The printed proof, its typos corrected (printed -> intended): Summing from left to right -> Summing over $n$]");
    expect(proof.join("\n")).toBe(SUM_PROOF.replace("Summing from left to right", "Summing over $n$"));
    // the review keeps the grade the referee gave
    const review = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v15Review), "utf8")) as V15Review;
    expect(review.verdict).toBe("PASS");
    expect(review.nodes.find((n) => n.id === "thm:sum")).toMatchObject({ correctness: "ok", typos: [SUM_TYPO] });

    // A later V1.5 pass: the typo-only patch file is no repair file (no checkpoint), the referee listing
    // the typo again adds nothing, and the correction stands.
    const again = await runStageV1_5(r.args([passWith([SUM_TYPO]), passWith([SUM_TYPO])]));
    expect(again.status).toBe("completed");
    expect((await r.patches()).typo_fixes).toEqual(file.typo_fixes);
    expect((await r.builtCore()).statements.find((s) => s.id === "thm:sum")!.proof_tex).toContain("Summing over $n$");
  });

  it("a snippet the proof does not print exactly once is reported only: the proof stands as printed", async () => {
    const r = await setup();
    const res = await runStageV1_5(r.args([passWith([{ printed: "a_n", intended: "b_n", reason: "printed in both steps" }])]));
    expect(res.status).toBe("completed");
    expect(res.message).not.toContain("typo(s) of proofs corrected");
    expect((await r.patches()).typo_fixes![0]!.typos[0]!.unit).toBeNull();
    expect((await r.builtCore()).statements.find((s) => s.id === "thm:sum")!.proof_tex).toBe(SUM_PROOF);
    expect(r.state.verify!.findings.filter((f) => f.node === "thm:sum")).toEqual([]);
  });
});
