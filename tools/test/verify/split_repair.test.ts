/**
 * A repair may SPLIT a result (owner request 2026-10-06): the node keeps a short general statement and
 * each special case is a corollary — a statement node of its own (`split_from`), graded, formalized
 * and reported like any result. The build, the patch-file checks, the referee's routing (an objection
 * to a corollary is answered on its parent; what is given up is judged on the set), the owner's
 * receipt, the report and the annotated paper; and the referee's FORM remark (`split`) on a repair
 * that should have been split: one bounded re-ask, never an error round. Fixer and referee faked; no
 * network.
 */
import { existsSync, readFileSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { runStructuralGate } from "../../src/core/gate.js";
import type { CodexRunInput } from "../../src/shared/codex.js";
import { createVerifyInitialState } from "../../src/state.js";
import { renderPaper } from "../../src/ui/tex_html.js";
import { applyEdits as applyTexEdits, planAnnotations, type AnnotationInput } from "../../src/verify/annotated_paper.js";
import { pendingDecisions } from "../../src/verify/annotate_run.js";
import { correctedTex } from "../../src/verify/corrected_tex.js";
import { UMBRELLA_PROOF, UMBRELLA_STATEMENT, buildCore, checkCoreInvariants, splitCorollaryId, type PatchFileLike } from "../../src/verify/core_graph.js";
import { PATCH_REPLY_JSON_SCHEMA, PatchFileSchema, corollaryNodes, onSplitParent, validatePatchFile, type PatchFile } from "../../src/verify/patches.js";
import { buildReport } from "../../src/verify/report.js";
import { repairTextViolations, runStageV1 } from "../../src/verify/stage_v1.js";
import { isRefinementRound, noteBasis, routeReview, runStageV1_5, splitObjection, splitRequests } from "../../src/verify/stage_v1_5.js";
import { VERIFY_FILES, type V15NodeVerdict, type V15Review } from "../../src/verify/types.js";
import { convertWeakeningPatches, recordWeakeningReceipt, weakeningMessage } from "../../src/verify/weakening.js";
import { cannedExplanation, writeToyPaper } from "./owner_explained.js";
import { cannedCodex } from "./referee_fake.js";

const QID = "split_paper";
const tmpDirs: string[] = [];
afterEach(async () => {
  for (const dir of tmpDirs.splice(0)) await rm(dir, { recursive: true, force: true });
});

/** thm:main rests on lem:rate; cor:use (a printed corollary, a theorem node) uses thm:main. */
function core(): Core {
  return {
    qid: QID,
    symbols: [],
    assumptions: [
      { id: "ass:overlap", condition: "\\(\\hat p < 1 - \\eta\\)", novel: { flag: true, justification: "Assumption 1" }, used_by: ["lem:rate"] },
      { id: "ass:gauss", condition: "the errors are Gaussian", novel: { flag: true, justification: "Assumption 2" } },
    ],
    definitions: [],
    statements: [
      { id: "lem:rate", kind: "lemma", statement: "the rate is \\(n^{-1/2}\\)", depends_on: ["ass:overlap"], status: "to-prove" },
      { id: "thm:main", kind: "theorem", statement: "the estimator is asymptotically normal and efficient", depends_on: ["lem:rate"], status: "to-prove" },
      { id: "thm:use", kind: "theorem", statement: "the interval has exact coverage", depends_on: ["thm:main"], status: "to-prove" },
      { id: "prop:aside", kind: "proposition", statement: "a remark-level identity", depends_on: [], status: "to-prove" },
    ],
    target_estimand: "\\(\\tau\\)",
  } as unknown as Core;
}

const GENERAL = "the estimator is asymptotically normal";
const COR = { title: "the Gaussian case", statement: "If the errors are Gaussian, the estimator of Theorem~\\ref{thm:main} is efficient.", follows: "Under Gaussian errors the limit variance of Theorem~\\ref{thm:main} equals the information bound.", adds: ["ass:gauss"] };
const COR_ID = splitCorollaryId("thm:main", COR.statement);
const MIXED = "the estimator is asymptotically normal; in the Gaussian case it is efficient; in the bounded case it is efficient up to a constant";
const WITNESS = "a heavy-tailed design";
const finding = { id: "thm:main", axis: "correctness", detail: "efficiency fails without Gaussian errors", witness: WITNESS };

const split = (over: Record<string, unknown> = {}) => ({ node: "thm:main", corrected_statement: GENERAL, ops: [{ op: "replace" as const, unit: "thm:main/1/1", tex: GENERAL }], proof_note: "The central limit theorem gives normality; efficiency is left to the Gaussian case.", corollaries: [COR], ...over });
const file = (over: Record<string, unknown> = {}): PatchFile => PatchFileSchema.parse({ key_results: ["thm:main"], key_contribution: "asymptotic normality of the estimator", patches: [], unfixable: [], ...over });
const like = (f: PatchFile): PatchFileLike => f as unknown as PatchFileLike;

function grade(id: string, over: Partial<V15NodeVerdict> = {}): V15NodeVerdict {
  return { id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "reproduced", witness: null, bookkeeping_assumption: null, reading: null, ...over };
}

async function setup() {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-split-"));
  tmpDirs.push(repoRoot);
  const runDir = path.join(repoRoot, "runs", QID);
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  for (const f of [VERIFY_FILES.coreJson, VERIFY_FILES.coreTranscribed]) await writeFile(path.join(runDir, f), JSON.stringify(core(), null, 2), "utf8");
  await writeToyPaper(runDir, core());
  const state = createVerifyInitialState(QID, { phase: "init", source: { input: "paper.tex", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
  state.verify!.paper_errors = { "thm:main": { detail: finding.detail, witness: WITNESS } };
  const calls: CodexRunInput[] = [];
  const args = (replies: unknown[]) => ({ repoRoot, qid: QID, runDir, state, deps: { runCodex: cannedCodex(replies, calls) }, dryRun: false, log: () => {} });
  const directive = (findings: unknown[]) => writeFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), JSON.stringify({ mode: "patch", round: 1, findings }), "utf8");
  const built = async (): Promise<Core> => JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
  const patches = async (): Promise<PatchFile> => PatchFileSchema.parse(JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.patches), "utf8")));
  const readDirective = async () => JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), "utf8")) as { findings: Array<{ id: string; axis: string; detail: string }> };
  /** A referee reply grading every node of the current `core.json`. */
  const review = async (over: Record<string, Partial<V15NodeVerdict>> = {}): Promise<V15Review> => {
    const c = await built();
    const ids = [...c.statements, ...c.assumptions, ...c.definitions].map((n) => n.id);
    return { verdict: "PASS", summary: "s", nodes: ids.map((id) => grade(id, over[id])), patch_review: { key_results_ok: true, detail: "thm:main is the headline" } };
  };
  /** The fixer answers the finding on thm:main with `patch`. */
  const fix = async (patch: Record<string, unknown>) => {
    await directive([finding]);
    return runStageV1(args([file({ patches: [patch] })]));
  };
  return { runDir, state, calls, args, directive, built, patches, review, fix, readDirective };
}

describe("the build: a repair's corollaries are statement nodes of their own", () => {
  it("each corollary is a node of the parent's kind with a deterministic id, depending on the parent and its `adds`; the users of the parent use it too; the core is a consistent graph the structural gate accepts", () => {
    const { core: c } = buildCore(core(), { patches: like(file({ patches: [split()] })) });
    const cor = c.statements.find((s) => s.id === COR_ID)!;
    expect(COR_ID).toMatch(/^thm:cor-fix-[0-9a-f]{8}$/);
    expect(cor).toMatchObject({ kind: "theorem", statement: COR.statement, split_from: "thm:main", status: "proved", proof_tex: COR.follows, depends_on: ["thm:main", "ass:gauss"] });
    expect(cor.tex_locator).toBeUndefined();
    // appended: no printed statement changes place
    expect(c.statements.map((s) => s.id)).toEqual(["lem:rate", "thm:main", "thm:use", "prop:aside", COR_ID]);
    expect(c.statements.find((s) => s.id === "thm:main")!.statement).toBe(GENERAL);
    // the printed result is the parent together with its corollaries: what used it uses them
    expect(c.statements.find((s) => s.id === "thm:use")!.depends_on).toEqual(["thm:main", COR_ID]);
    expect(c.statements.find((s) => s.id === "thm:use")!.statement).toBe("the interval has exact coverage");
    expect(c.assumptions.find((a) => a.id === "ass:gauss")!.used_by).toEqual([COR_ID]);
    expect(checkCoreInvariants(c)).toEqual([]);
    expect(runStructuralGate(c, { allowBookkeeping: true, verbatim: true }).violations).toEqual([]);
    // a lemma's corollary is a lemma
    expect(splitCorollaryId("lem:rate", "x")).toMatch(/^lem:cor-fix-/);
  });

  it("the id is the statement by its meaning: a re-typesetting keeps it (and so its grades, plan and receipts), a reworded corollary is another node, and a corollary no longer emitted leaves the core with every edge to it", () => {
    expect(splitCorollaryId("thm:main", `  ${COR.statement.replace(/ /g, "  ")}\n`)).toBe(COR_ID);
    const reworded = { ...COR, statement: "If the errors are Gaussian, the estimator attains the information bound." };
    const next = buildCore(core(), { patches: like(file({ patches: [split({ corollaries: [reworded] })] })) }).core;
    expect(next.statements.some((s) => s.id === COR_ID)).toBe(false);
    expect(next.statements.find((s) => s.id === "thm:use")!.depends_on).toEqual(["thm:main", splitCorollaryId("thm:main", reworded.statement)]);
    const dropped = buildCore(core(), { patches: like(file({ patches: [split({ corollaries: null })] })) }).core;
    expect(dropped.statements.map((s) => s.id)).toEqual(["lem:rate", "thm:main", "thm:use", "prop:aside"]);
    expect(dropped.statements.find((s) => s.id === "thm:use")!.depends_on).toEqual(["thm:main"]);
    expect(dropped.assumptions.find((a) => a.id === "ass:gauss")!.used_by).toBeUndefined();
  });

  it("a reading the repair states binds its corollaries too; a result that no longer uses the parent (`drops`) does not use them; a descoped parent splits nothing", () => {
    const withReading = buildCore(core(), { patches: like(file({ patches: [split({ readings: ["normality is in distribution"] })] })) }).core;
    const pin = withReading.assumptions.find((a) => a.id.startsWith("ass:pin-fix-"))!;
    expect(pin.used_by).toEqual([COR_ID, "thm:main"].sort());
    const user = { node: "thm:use", corrected_statement: "the interval has asymptotic coverage", ops: [{ op: "replace" as const, unit: "thm:use/1/1", tex: "the interval has asymptotic coverage" }], drops: ["thm:main"], proof_note: "direct.", consequence_of: ["thm:main"], reason: "it no longer uses efficiency" };
    const dropped = buildCore(core(), { patches: like(file({ patches: [split(), user] })) }).core;
    expect(dropped.statements.find((s) => s.id === "thm:use")!.depends_on).toEqual([]);
    const gone = buildCore(core(), { patches: like(file({ key_results: [], patches: [split()], unfixable: [{ node: "lem:rate", reason: "false" }] })) }).core;
    expect(gone.statements.map((s) => s.id)).toEqual(["prop:aside"]);
  });
});

describe("the patch file: what a split must satisfy", () => {
  it("the reply schema carries `corollaries` on a patch and on a suggested repair; the mechanical checks refuse a split of a non-result, a repeated corollary, one restating its parent and an `adds` that is no hypothesis", () => {
    const props = PATCH_REPLY_JSON_SCHEMA.properties as Record<string, { items: { required: string[] } }>;
    expect(props.patches!.items.required).toContain("corollaries");
    // null and [] read as absent
    expect(file({ patches: [split({ corollaries: null })] }).patches[0]!.corollaries).toBeUndefined();
    expect(file({ patches: [split({ corollaries: [] })] }).patches[0]!.corollaries).toBeUndefined();
    expect(validatePatchFile(core(), file({ patches: [split()] }), ["thm:main"])).toEqual([]);
    const bad = (patch: Record<string, unknown>, required = ["thm:main"]): string => validatePatchFile(core(), file({ patches: [patch] }), required).join("\n");
    expect(bad(split({ corollaries: [COR, { ...COR, title: "again" }] }))).toMatch(/corollary 2 of the patch for "thm:main" repeats another corollary/);
    expect(bad(split({ corollaries: [{ ...COR, statement: ` ${GENERAL} ` }] }))).toMatch(/restates the result itself/);
    expect(bad(split({ corollaries: [{ ...COR, adds: ["lem:rate", "ass:ghost"] }] }))).toMatch(/adds "lem:rate", which is not an assumption or definition[\s\S]*adds "ass:ghost"/);
    // a result is cited by \ref (its label named when it has one); an id that is no node gets no such advice
    const added = bad(split({ corollaries: [{ ...COR, adds: ["lem:rate", "ass:ghost"] }] })).split("\n").filter((v) => / adds "/.test(v));
    expect(added[0]).toMatch(/adds "lem:rate", which is not an assumption or definition of the core: `adds` lists only hypotheses \(assumptions, definitions\)\. "lem:rate" is a result — a result the corrected statement or proof uses is cited by \\ref(\{[^}]+\}| of its label) in the text; remove it from `adds`\.$/);
    expect(added[1]).toMatch(/adds "ass:ghost", which is not an assumption or definition of the core: `adds` lists only hypotheses \(assumptions, definitions\)\.$/);
    expect(bad({ node: "ass:overlap", corrected_statement: null, proof_note: "n", corollaries: [COR] }, ["ass:overlap"])).toMatch(/"ass:overlap" is not a result: only a result is split/);
    // a corollary is no node the fixer can name: never a key result, never an entry of its own
    expect(validatePatchFile(core(), file({ key_results: [COR_ID], patches: [split()] }), ["thm:main"]).join("\n")).toMatch(/is not a statement of the core/);
  });

  it("a finding on a corollary is put on its parent, saying which corollary; every other finding stands", () => {
    const f = file({ patches: [split()] });
    expect(corollaryNodes("thm:main", f.patches[0]).map((c) => c.id)).toEqual([COR_ID]);
    const out = onSplitParent([{ id: COR_ID, axis: "patch rejected", detail: "it does not follow" }, { id: "lem:rate", axis: "correctness", detail: "d" }], f);
    expect(out[0]).toEqual({ id: "thm:main", axis: "patch rejected", detail: expect.stringMatching(/^on the corollary "the Gaussian case" this repair splits off \("If the errors are Gaussian[^)]*"\): it does not follow$/) });
    expect(out[1]).toEqual({ id: "lem:rate", axis: "correctness", detail: "d" });
    // a suggested repair's corollaries too (graded as applied by the pass confirming its receipt)
    const sug = file({ unfixable: [{ node: "thm:main", reason: "r", suggested_repair: { corrected_statement: GENERAL, proof_note: "n", corollaries: [COR] } }] });
    expect(onSplitParent([{ id: COR_ID, detail: "d" }], sug)[0]!.id).toBe("thm:main");
  });

  it("the parent is graded with its corollaries: a corollary added, dropped or reworded changes its basis material, a repair without corollaries keeps the material it had", () => {
    const note = cannedExplanation("thm:main");
    const plain = noteBasis(file({ patches: [split({ corollaries: null, owner_explanation: note })] })).get("thm:main");
    expect(plain).toBe(JSON.stringify(note));
    const withCor = noteBasis(file({ patches: [split({ owner_explanation: note })] })).get("thm:main");
    expect(withCor).not.toBe(plain);
    expect(withCor).toContain(COR_ID);
  });
});

describe("V1 and V1.5 on a split repair", () => {
  it("the fixer's split is applied; the referee grades the corollary as a node; the confirmed repair is recorded with its corollaries and the report gives the corollary a row of its own after its parent", async () => {
    const r = await setup();
    expect((await r.fix(split())).status).toBe("completed");
    expect((await r.patches()).patches[0]!.corollaries).toEqual([COR]);
    expect((await r.built()).statements.find((s) => s.id === COR_ID)).toMatchObject({ split_from: "thm:main" });
    const result = await runStageV1_5(r.args([await r.review()]));
    expect(result.status).toBe("completed");
    // the corollary was put before a shard with the patch that wrote it
    const shard = r.calls.find((c) => c.prompt.includes(`- ${COR_ID}`) && c.prompt.includes("NODES TO GRADE"))!;
    expect(shard.prompt).toContain(`"id":"${COR_ID}"`);
    expect(shard.prompt).toContain("split_from");
    const refuted = r.state.verify!.findings.find((f) => f.node === "thm:main" && f.kind === "refuted")!;
    expect(refuted.patch).toMatchObject({ confirmed: true, corollaries: [COR_ID] });
    expect(r.state.verify!.findings.some((f) => f.node === COR_ID)).toBe(false);

    const envs = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.envsJson), "utf8")) as { envs: Array<{ id: string; lines: unknown }> };
    // the toy core carries no locators: each printed statement takes its environment's (a corollary has none)
    const located = (k: Core): Core => ({ ...k, statements: k.statements.map((st) => (st.split_from ? st : { ...st, tex_locator: envs.envs.find((e) => e.id === st.id)!.lines })) }) as Core;
    const { json, md } = buildReport({
      qid: QID, envs: envs as never, scope: envs.envs.map((e) => e.id), core: located(await r.built()), transcribed: located(core()), review: null, findings: r.state.verify!.findings,
      addedAssumptions: [], crosswalk: null, graph: null, lean: null, warnings: { lint: [], parser: [] }, flags: {}, stageCompleted: "V1.5", earlyStop: true, sourceSha256: "h",
      inputs: { v1_5_review: "x", crosswalk_full: "x", graph_json: "x", v1_scope: "x", lean_evidence: "x" },
    });
    expect(json.results.map((x) => x.node_id)).toEqual(["lem:rate", "thm:main", COR_ID, "thm:use", "prop:aside"]);
    const row = json.results.find((x) => x.node_id === COR_ID)!;
    expect(row).toMatchObject({ split_from: "thm:main", env_id: "thm:main", label: null, statement: COR.statement, bucket: "not_checked", change: null });
    expect(row.title).toMatch(/^Corollary of .* \(split off by its repair\)$/);
    expect(json.results.find((x) => x.node_id === "thm:main")!.bucket).toBe("repaired");
    expect(md).toContain(`split off as results of their own: ${COR_ID}`);
  });

  it("the referee's error on a corollary rejects the repair: the fixer is asked on the PARENT, the directive naming the corollary; the corollary is never recorded as a refuted claim of the paper", async () => {
    const r = await setup();
    await r.fix(split());
    const result = await runStageV1_5(r.args([await r.review({ [COR_ID]: { correctness: "error", detail: "efficiency needs more than Gaussian errors", witness: "a Gaussian design with a singular information matrix" } })]));
    expect(result.status).toBe("patch");
    const d = await r.readDirective();
    expect(d.findings).toEqual([expect.objectContaining({ id: "thm:main", axis: "patch rejected", detail: expect.stringContaining('on the corollary "the Gaussian case" this repair splits off') })]);
    expect(r.state.verify!.paper_errors).not.toHaveProperty(COR_ID);
    expect(r.state.verify!.level_pause?.errors.map((e) => e.id) ?? ["thm:main"]).toEqual(["thm:main"]);
    // the fixer returns the parent's entry, the corollary revised: accepted by the same checks
    const revised = { ...COR, statement: "If the errors are Gaussian with a nonsingular information matrix, the estimator of Theorem~\\ref{thm:main} is efficient." };
    const again = await runStageV1(r.args([file({ patches: [split({ corollaries: [revised] })] })]));
    expect(again.status).toBe("completed");
    expect((await r.built()).statements.filter((s) => s.split_from).map((s) => s.id)).toEqual([splitCorollaryId("thm:main", revised.statement)]);
  });

  it("an F-stage finding on a corollary reaches the fixer as a finding on the parent", async () => {
    const r = await setup();
    await r.fix(split());
    await r.directive([{ id: COR_ID, axis: "correctness", detail: "[F2.5 reviewer] the corollary needs finite variance", witness: "w", from_stage: "F2.5" }]);
    const out = await runStageV1(r.args([file({ patches: [split({ corollaries: [{ ...COR, statement: `${COR.statement} Assume finite variance.` }] })] })]));
    expect(out.status).toBe("completed");
    const prompt = r.calls.at(-1)!.prompt;
    expect(prompt).toContain('"id": "thm:main"');
    expect(prompt).not.toContain(`"id": "${COR_ID}"`);
  });

  it("a split never hides a weakening: the referee's weakening grade — on the parent or on a corollary — turns the WHOLE repair into a suggestion, and the owner's receipt, its halt message and the annotated paper's pending decision carry the corollaries", async () => {
    for (const on of ["thm:main", COR_ID]) {
      const r = await setup();
      await r.fix(split());
      const weakens = { correctness: "error" as const, weakens_contribution: true, detail: "weakens the contribution: efficiency in the bounded case is in no block", witness: "the bounded case of the printed statement" };
      const result = await runStageV1_5(r.args([await r.review({ [on]: weakens })]));
      expect(result.status).toBe("narrowed");
      const saved = await r.patches();
      expect(saved.patches).toEqual([]);
      expect(saved.unfixable).toEqual([expect.objectContaining({ node: "thm:main", suggested_by: "referee", suggested_repair: expect.objectContaining({ corrected_statement: GENERAL, corollaries: [COR] }) })]);
      // pending with the owner: the core is the printed paper again, the corollary gone with it
      expect((await r.built()).statements.some((s) => s.split_from)).toBe(false);
      const rec = r.state.verify!.weakening_repair!;
      expect(rec).toMatchObject({ status: "pending", items: [{ node: "thm:main", proposed: GENERAL, corollaries: [{ title: COR.title, statement: COR.statement }] }] });
      expect(weakeningMessage(rec, QID)).toContain("with corollary 1 (the Gaussian case): If the errors are Gaussian");
      expect(pendingDecisions(r.state.verify!, saved)!.weakening[0]!.corollaries).toEqual([COR]);
      expect(r.state.verify!.paper_errors!["thm:main"]!.suggested_repair).toContain("corollary 1 (the Gaussian case)");
    }
  });

  it("pure: a patch graded weakening moves to a suggestion with its corollaries, and the receipt lists them", () => {
    const moved = convertWeakeningPatches(file({ patches: [split()] }), [{ id: "thm:main", detail: "weakens the contribution: x" }]);
    expect(moved.unfixable[0]!.suggested_repair!.corollaries).toEqual([COR]);
    const state = createVerifyInitialState(QID, { phase: "init", source: { input: "p", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
    expect(recordWeakeningReceipt(state, core(), moved)!.items[0]!.corollaries).toEqual([{ title: COR.title, statement: COR.statement }]);
  });
});

describe("V1 and V1.5 on an umbrella: every conclusion a block, the result over them", () => {
  const B1 = { title: "normality", statement: "The estimator is asymptotically normal.", follows: "By the rate of the lemma and the central limit theorem." };
  const B2 = { title: "the Gaussian case", statement: "If the errors are Gaussian, the estimator is efficient.", follows: "Under Gaussian errors the limit variance equals the information bound.", adds: ["ass:gauss"] };
  const [I1, I2] = [B1, B2].map((b) => splitCorollaryId("thm:main", b.statement)) as [string, string];
  const umbrella = (over: Record<string, unknown> = {}) => ({ node: "thm:main", corrected_statement: null, ops: [], proof_note: "none of its own", umbrella: true, corollaries: [B1, B2], ...over });

  it("the fixer's umbrella is applied with the pipeline's sentence; the referee grades the umbrella and its blocks; the confirmed repair is recorded as an umbrella and the report derives its row from the blocks", async () => {
    const r = await setup();
    expect((await r.fix(umbrella())).status).toBe("completed");
    const p = (await r.patches()).patches[0]!;
    expect(p).toMatchObject({ umbrella: true, corrected_statement: UMBRELLA_STATEMENT, proof_note: UMBRELLA_PROOF, corollaries: [B1, B2] });
    const c = await r.built();
    expect(c.statements.find((s) => s.id === "thm:main")).toMatchObject({ umbrella: true, statement: UMBRELLA_STATEMENT, depends_on: [I1, I2] });
    expect(c.statements.find((s) => s.id === "thm:use")!.depends_on).toEqual(["thm:main", I1, I2]);
    expect(checkCoreInvariants(c)).toEqual([]);
    const result = await runStageV1_5(r.args([await r.review()]));
    expect(result.status).toBe("completed");
    // the referee is shown the patch as an umbrella, with the printed statement to judge the set against
    const shard = r.calls.find((x) => x.prompt.includes("NODES TO GRADE") && x.prompt.includes("- thm:main"))!;
    expect(shard.prompt).toContain('"umbrella":true');
    expect(shard.prompt).toContain("UMBRELLAS. A patch with `umbrella: true`");
    const refuted = r.state.verify!.findings.find((f) => f.node === "thm:main" && f.kind === "refuted")!;
    expect(refuted.patch).toMatchObject({ confirmed: true, umbrella: true, corollaries: [I1, I2] });

    const envs = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.envsJson), "utf8")) as { envs: Array<{ id: string; lines: unknown }> };
    const located = (k: Core): Core => ({ ...k, statements: k.statements.map((st) => (st.split_from ? st : { ...st, tex_locator: envs.envs.find((e) => e.id === st.id)!.lines })) }) as Core;
    const { json } = buildReport({
      qid: QID, envs: envs as never, scope: envs.envs.map((e) => e.id), core: located(await r.built()), transcribed: located(core()), review: null, findings: r.state.verify!.findings,
      addedAssumptions: [], crosswalk: null, graph: null, lean: null, warnings: { lint: [], parser: [] }, flags: {}, stageCompleted: "V1.5", earlyStop: true, sourceSha256: "h",
      inputs: { v1_5_review: "x", crosswalk_full: "x", graph_json: "x", v1_scope: "x", lean_evidence: "x" },
    });
    expect(json.results.map((x) => x.node_id)).toEqual(["lem:rate", "thm:main", I1, I2, "thm:use", "prop:aside"]);
    expect(json.results.find((x) => x.node_id === "thm:main")).toMatchObject({ umbrella: true, lean: null, bucket: "repaired" });
    expect(json.results.filter((x) => x.split_from === "thm:main").map((x) => x.split_kind)).toEqual(["proposition", "proposition"]);
  });

  it("an umbrella the fixer gets wrong goes back with the reason: one block, ops of its own", async () => {
    for (const [patch, why] of [
      [umbrella({ corollaries: [B1] }), /gives 1 block\(s\): an umbrella is a statement mixing several conclusions/u],
      [umbrella({ ops: [{ op: "replace", unit: "thm:main/1/1", tex: GENERAL }] }), /gives `ops`: an umbrella has no statement or proof of its own/u],
    ] as const) {
      const r = await setup();
      // the violation goes back in a second fixer call (none is canned: the round ends there)
      await expect(r.fix(patch)).rejects.toThrow(/unexpected codex call #2/u);
      const prompts = r.calls.map((c) => c.prompt).join("\n");
      expect(prompts).toMatch(why);
      expect(existsSync(path.join(r.runDir, VERIFY_FILES.patches)) ? (await r.patches()).patches.some((p) => p.umbrella) : false).toBe(false);
    }
  });

  it("the referee's error on a block of an umbrella is answered on the umbrella; its form remark asks once to restore a main claim, in a refinement round", async () => {
    const r = await setup();
    await r.fix(umbrella());
    const bad = await runStageV1_5(r.args([await r.review({ [I2]: { correctness: "error", detail: "efficiency needs a nonsingular information matrix", witness: "a singular design" } })]));
    expect(bad.status).toBe("patch");
    expect((await r.readDirective()).findings).toEqual([expect.objectContaining({ id: "thm:main", detail: expect.stringContaining('on the corollary "the Gaussian case" this repair splits off') })]);
    expect(r.state.verify!.paper_errors).not.toHaveProperty(I2);

    const s = await setup();
    await s.fix(umbrella());
    const errorRounds = s.state.verify!.v1_5_rounds;
    const remark = await runStageV1_5(s.args([await s.review({ "thm:main": { split: { why: "asymptotic normality is the theorem; efficiency is its Gaussian case" } } })]));
    expect(remark.status).toBe("patch");
    const d = await s.readDirective();
    expect(d.findings).toEqual([expect.objectContaining({ id: "thm:main", axis: "split", detail: expect.stringContaining("it states the result as an umbrella (`umbrella: true`) although the printed statement has a main claim of its own") })]);
    expect(s.state.verify!.split_requests).toEqual(["thm:main"]);
    expect(s.state.verify!.v1_5_rounds).toBe(errorRounds);
    // the fixer restores the claim: the existing split form, accepted by the same checks
    const again = await runStageV1(s.args([file({ patches: [split()] })]));
    expect(again.status).toBe("completed");
    expect((await s.built()).statements.find((x) => x.id === "thm:main")).toMatchObject({ statement: GENERAL });
    expect((await s.built()).statements.find((x) => x.id === "thm:main")!.umbrella).toBeUndefined();
  });

  it("an umbrella never hides a weakening: the referee's grade on it turns the whole repair into a suggestion that is still an umbrella, for the owner", async () => {
    const r = await setup();
    await r.fix(umbrella());
    const result = await runStageV1_5(r.args([await r.review({ "thm:main": { correctness: "error", weakens_contribution: true, detail: "efficiency outside the Gaussian case is in no block", witness: WITNESS } })]));
    expect(result.status).toBe("narrowed");
    expect((await r.patches()).patches).toEqual([]);
    expect((await r.built()).statements.some((x) => x.umbrella || x.split_from)).toBe(false);
    const u = (await r.patches()).unfixable.find((x) => x.node === "thm:main")!;
    expect(u.suggested_repair).toMatchObject({ umbrella: true, corrected_statement: UMBRELLA_STATEMENT, corollaries: [B1, B2] });
    expect(r.state.verify!.weakening_repair!.items[0]).toMatchObject({ node: "thm:main", proposed: UMBRELLA_STATEMENT, corollaries: [{ title: "normality", statement: B1.statement }, { title: "the Gaussian case", statement: B2.statement }] });
    expect(r.state.verify!.paper_errors!["thm:main"]!.suggested_repair).toContain("the statement becomes an umbrella over these blocks");
  });
});

describe("the form of a repair: the referee's `split` remark", () => {
  const why = "it states normality in general and efficiency case by case (Gaussian, bounded)";
  const unsplit = () => split({ corrected_statement: MIXED, ops: [{ op: "replace" as const, unit: "thm:main/1/1", tex: MIXED }], corollaries: null });

  it("a mixed repair the referee confirms gets the form finding and ONE re-ask, in a refinement round (no error round); a second unsplit answer stands, the repair confirmed and the remark noted in the report", async () => {
    const r = await setup();
    await r.fix(unsplit());
    const first = await runStageV1_5(r.args([await r.review({ "thm:main": { split: { why } } })]));
    expect(first).toMatchObject({ status: "patch", round_kind: "refinement" });
    expect(first.round_scope).toBeUndefined();
    expect((await r.readDirective()).findings).toEqual([expect.objectContaining({ id: "thm:main", axis: "split", detail: expect.stringContaining(why), witness: null })]);
    expect(r.state.verify!.split_requests).toEqual(["thm:main"]);
    // the repair is not downgraded: its verdict stays clean and cached, nothing halts, nothing goes to the owner
    const saved = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v15Review), "utf8")) as V15Review;
    expect(saved.nodes.find((n) => n.id === "thm:main")).toMatchObject({ correctness: "ok", split: { why } });
    expect(r.state.verify!.confirmed).toHaveProperty("thm:main");
    expect(r.state.verify!.weakening_repair ?? null).toBeNull();
    expect(r.state.verify!.cap_reached ?? null).toBeNull();
    expect(r.state.verify!.paper_errors).toEqual({ "thm:main": { detail: finding.detail, witness: WITNESS } });

    // the fixer returns the statement as it was: its answer stands
    const answer = await runStageV1(r.args([file({ patches: [unsplit()] })]));
    expect(answer.status).toBe("completed");
    const fixerPrompt = r.calls.at(-1)!.prompt;
    expect(fixerPrompt).toContain('"axis": "split"');
    const second = await runStageV1_5(r.args([await r.review({ "thm:main": { split: { why } } })]));
    expect(second.status).toBe("completed");
    expect(existsSync(path.join(r.runDir, VERIFY_FILES.v1ReviseDirective))).toBe(false);
    const fs = r.state.verify!.findings.filter((f) => f.node === "thm:main");
    expect(fs.find((f) => f.kind === "refuted")!.patch).toMatchObject({ confirmed: true });
    expect(fs.find((f) => f.kind === "note")!.detail).toContain(`the referee would state it as a general statement with corollaries: ${why}`);
  });

  it("the fixer may answer the re-ask with the split: the corollary is graded and the repair accepted", async () => {
    const r = await setup();
    await r.fix(unsplit());
    await runStageV1_5(r.args([await r.review({ "thm:main": { split: { why } } })]));
    expect((await runStageV1(r.args([file({ patches: [split()] })]))).status).toBe("completed");
    const done = await runStageV1_5(r.args([await r.review()]));
    expect(done.status).toBe("completed");
    expect(r.state.verify!.findings.some((f) => f.kind === "note" && /general statement with corollaries/.test(f.detail))).toBe(false);
    expect((await r.built()).statements.some((s) => s.id === COR_ID)).toBe(true);
  });

  it("a repair the referee does not remark on (a further conclusion under the same hypotheses — \"moreover …\") is accepted with no re-ask; a remark on a statement the paper prints is ignored", async () => {
    const r = await setup();
    const moreover = "the estimator is asymptotically normal; moreover its variance estimator is consistent";
    await r.fix(split({ corrected_statement: moreover, ops: [{ op: "replace" as const, unit: "thm:main/1/1", tex: moreover }], corollaries: null }));
    const result = await runStageV1_5(r.args([await r.review({ "thm:use": { split: { why: "it is long" } } })]));
    expect(result.status).toBe("completed");
    expect(r.state.verify!.split_requests ?? []).toEqual([]);
    expect(r.state.verify!.findings.some((f) => f.kind === "note" && /corollaries/.test(f.detail))).toBe(false);
  });

  it("pure: only a confirmed repair whose patch rewrites its statement is remarked on; asked once; never on a repair accepted as a weakening or awaiting the owner; the round it opens is a refinement round unless an error rides with it", () => {
    const f = file({ patches: [split({ corollaries: null })] });
    const results = new Set(["thm:main", "thm:use", "lem:rate"]);
    const review = (nodes: V15NodeVerdict[]): V15Review => ({ verdict: "PASS", summary: "", nodes } as V15Review);
    const remark = { split: { why } };
    const route = (nodes: V15NodeVerdict[], patches: PatchFile | null = f) => routeReview(review(nodes), patches, results);
    expect(route([grade("thm:main", remark), grade("thm:use", remark)]).splitRemarks.map((n) => n.id)).toEqual(["thm:main"]);
    // not confirmed → the errors lead, no remark; a proof-only repair has no statement to split; a blank remark is none
    expect(route([grade("thm:main", { ...remark, correctness: "error", witness: "w" })]).splitRemarks).toEqual([]);
    expect(route([grade("thm:main", remark)], file({ patches: [{ node: "thm:main", corrected_statement: null, proof_note: "n" }] })).splitRemarks).toEqual([]);
    expect(route([grade("thm:main", { split: { why: " " } })]).splitRemarks).toEqual([]);
    expect(route([grade("thm:main", remark)], null).splitRemarks).toEqual([]);
    const r = route([grade("thm:main", remark)]);
    expect(splitRequests(r, f, new Set()).ask.map((n) => n.id)).toEqual(["thm:main"]);
    expect(splitRequests(r, f, new Set(["thm:main"]))).toMatchObject({ ask: [], noted: [{ id: "thm:main" }] });
    expect(splitRequests(r, f, new Set(), new Set(["thm:main"]))).toMatchObject({ ask: [], noted: [{ id: "thm:main" }] });
    expect(splitRequests(r, file({ patches: [split({ corollaries: null, accepted_weakening: true, given_up: "g" })] }), new Set()).ask).toEqual([]);
    const o = splitObjection(grade("thm:main", remark));
    expect(o).toMatchObject({ id: "thm:main", axis: "split", note: true, witness: null });
    expect(isRefinementRound([o], { keyObjection: false, unresolvable: 0 })).toBe(true);
    expect(isRefinementRound([o, { id: "lem:rate", axis: "correctness", detail: "d", witness: "w" }], { keyObjection: false, unresolvable: 0 })).toBe(false);
    expect(isRefinementRound([o], { keyObjection: true, unresolvable: 0 })).toBe(false);
  });
});

describe("the annotated paper: a corollary is a block of its own after the result", () => {
  const FLAT = ["\\documentclass{article}", "\\begin{document}", "\\begin{theorem}\\label{thm:main}", "The estimator is normal and efficient.", "\\end{theorem}", "Text.", "\\end{document}"].join("\n");
  const one = (): Core => ({ qid: "a", symbols: [], assumptions: [], definitions: [], statements: [{ id: "thm:main", kind: "theorem", statement: "The estimator is normal and efficient.", depends_on: [], status: "to-prove", tex_locator: { file: "main.tex", from: 3, to: 5, env: "theorem", label: "thm:main" } }], target_estimand: "t", bibliography: [] } as unknown as Core);
  const patch = { node: "thm:main", corrected_statement: "The estimator is normal.", proof_note: "the proof as printed", corollaries: [COR] };
  const input = (over: Partial<AnnotationInput>): AnnotationInput => ({
    files: { "main.tex": FLAT },
    envs: { main_file: "main.tex", files: ["main.tex"], newtheorem: {}, bibliography: [], envs: [{ id: "thm:main", kind: "theorem", envName: "theorem", label: "thm:main", title: null, body: "The estimator is normal and efficient.", proof: null, proofLines: null, section: null, lines: { file: "main.tex", from: 3, to: 5 }, refs: [] }] } as never,
    flatText: FLAT, lineMap: FLAT.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 })), refs: null, transcribed: one(), core: one(),
    patches: { patches: [], unfixable: [] }, paperErrors: { "thm:main": { detail: "efficiency fails", witness: "w" } }, findings: [], review: null, ...over,
  });

  it("a confirmed split: the statement corrected in place, then `\\vsCorollary{id}{Theorem~\\ref}{statement … its proof}` right after the environment", () => {
    const plan = planAnnotations(input({ patches: { patches: [patch], unfixable: [] }, core: buildCore(one(), { patches: { key_results: [], patches: [patch], unfixable: [] } }).core }));
    const tex = applyTexEdits(FLAT, plan.edits["main.tex"] ?? []);
    const at = tex.indexOf("\\end{theorem}");
    const block = `\\vsCorollary{${splitCorollaryId("thm:main", COR.statement)}}{Theorem~\\ref{thm:main}}{\\textbf{the Gaussian case.} ${COR.statement} \\vsLine\\textit{Proof.} ${COR.follows}}`;
    expect(tex.indexOf(block)).toBeGreaterThan(at);
    expect(tex.slice(0, at)).toContain("\\vsCorrected{The estimator is normal.}");
    expect(plan.records.some((x) => x.node === "thm:main" && x.located_by === "after-env" && /corollary thm:cor-fix-/.test(x.summary))).toBe(true);
    expect(plan.unlocated).toEqual([]);
    // both texts are the fixer's: checked as fragments
    expect(plan.fragments.map((x) => x.text)).toEqual(expect.arrayContaining([COR.statement, COR.follows]));
  });

  it("a split awaiting the owner: `\\vsProposedCorollary`, and no corollary once the confirming check rejected the repair", () => {
    const pending = { weakening: [{ node: "thm:main", corrected_statement: "The estimator is normal.", given_up: "efficiency in general", detail: "efficiency fails", witness: "w", corollaries: [COR] }], rewind: null, cap: null };
    const tex = applyTexEdits(FLAT, planAnnotations(input({ pending })).edits["main.tex"] ?? []);
    expect(tex).toContain(`\\vsProposedCorollary{${splitCorollaryId("thm:main", COR.statement)}}{Theorem~\\ref{thm:main}}{`);
    expect(tex).not.toContain("\\vsCorollary{");
    const rejected = planAnnotations(input({ patches: { patches: [patch], unfixable: [] }, findings: [{ node: "thm:main", stage: "V1.5", kind: "refuted", detail: "d", witness: "w", patch: { corrected_statement: "x", proof_note: "n", confirmed: false }, at: "t" }] }));
    expect(applyTexEdits(FLAT, rejected.edits["main.tex"] ?? [])).not.toContain("Corollary{");
  });
});

describe("a split repair is shown block by block: the printed statement, the corrected statement, each corollary", () => {
  const BODY = "Suppose the errors are bounded. Let $n$ be large. Then the estimator is normal and efficient.";
  const FLAT = ["\\documentclass{article}", "\\begin{document}", "\\begin{theorem}\\label{thm:main}", BODY, "\\end{theorem}", "Text.", "\\end{document}"].join("\n");
  const CORRECTED = "Suppose the errors have two moments. Let $n$ be large. Then the estimator is normal.";
  const one = (): Core => ({ qid: "a", symbols: [], assumptions: [], definitions: [], statements: [{ id: "thm:main", kind: "theorem", statement: BODY, depends_on: [], status: "to-prove", tex_locator: { file: "main.tex", from: 3, to: 5, env: "theorem", label: "thm:main" } }], target_estimand: "t", bibliography: [] } as unknown as Core);
  // The ops change the first and the last sentence; the one between stands as printed.
  const ops = [{ op: "replace" as const, unit: "thm:main/1/1", tex: "Suppose the errors have two moments." }, { op: "replace" as const, unit: "thm:main/1/3", tex: "Then the estimator is normal." }];
  const patch = (corollaries: Array<typeof COR> | null) => ({ node: "thm:main", corrected_statement: null, ops, proof_note: "the proof as printed", ...(corollaries ? { corollaries } : {}) });
  const input = (over: Partial<AnnotationInput>): AnnotationInput => ({
    files: { "main.tex": FLAT },
    envs: { main_file: "main.tex", files: ["main.tex"], newtheorem: {}, bibliography: [], envs: [{ id: "thm:main", kind: "theorem", envName: "theorem", label: "thm:main", title: null, body: BODY, proof: null, proofLines: null, section: null, lines: { file: "main.tex", from: 3, to: 5 }, refs: [] }] } as never,
    flatText: FLAT, lineMap: FLAT.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 })), refs: null, transcribed: one(), core: one(),
    patches: { patches: [], unfixable: [] }, paperErrors: { "thm:main": { detail: "efficiency fails", witness: "w" } }, findings: [], review: null, ...over,
  });
  const annotated = (over: Partial<AnnotationInput>): string => applyTexEdits(FLAT, planAnnotations(input(over)).edits["main.tex"] ?? []);
  const count = (tex: string, macro: string): number => tex.split(`\\${macro}{`).length - 1;

  it("confirmed: one `\\vsOriginal` (the whole statement), one `\\vsCorrected` (derived from the ops), then `\\vsCorollary`; a repair that does not split keeps its per-op pairs", () => {
    const tex = annotated({ patches: { patches: [patch([COR])], unfixable: [] } });
    expect(tex).toContain(`\\vsOriginal{${BODY}} \\vsCorrected{${CORRECTED}}`);
    expect([count(tex, "vsOriginal"), count(tex, "vsCorrected"), count(tex, "vsCorollary")]).toEqual([1, 1, 1]);
    expect(tex.indexOf("\\vsCorollary{")).toBeGreaterThan(tex.indexOf("\\end{theorem}"));
    const plain = annotated({ patches: { patches: [patch(null)], unfixable: [] } });
    expect(plain).toContain("\\vsOriginal{Suppose the errors are bounded.} \\vsCorrected{Suppose the errors have two moments.} Let $n$ be large. \\vsOriginal{Then the estimator is normal and efficient.} \\vsCorrected{Then the estimator is normal.}");
  });

  it("awaiting the owner: one `\\vsOriginal`, one `\\vsProposed`, then `\\vsProposedCorollary` (the corollaries of the receipt, else of the suggested repair)", () => {
    const weak = { node: "thm:main", corrected_statement: null, ops, given_up: "efficiency in general", detail: "efficiency fails", witness: "w" };
    const onReceipt = annotated({ pending: { weakening: [{ ...weak, corollaries: [COR] }], rewind: null, cap: null } });
    const onFile = annotated({ pending: { weakening: [weak], rewind: null, cap: null }, patches: { patches: [], unfixable: [{ node: "thm:main", reason: "any repair weakens the contribution", suggested_repair: { corrected_statement: null, ops, corollaries: [COR] } }] } });
    for (const tex of [onReceipt, onFile]) {
      expect(tex).toContain(`\\vsOriginal{${BODY}} \\vsProposed{${CORRECTED}}`);
      expect([count(tex, "vsOriginal"), count(tex, "vsProposed"), count(tex, "vsProposedCorollary"), count(tex, "vsCorrected")]).toEqual([1, 1, 1, 0]);
    }
  });

  it("the corrected paper is the same statement whether or not the repair splits: one statement replaced by one statement", () => {
    const corrected = (corollaries: Array<typeof COR> | null): string => {
      const plan = planAnnotations(input({ patches: { patches: [patch(corollaries)], unfixable: [] }, correctedView: true }));
      return correctedTex(applyTexEdits(FLAT, plan.edits["main.tex"] ?? []), { proofEnv: true }).tex;
    };
    const env = (tex: string): string => tex.slice(tex.indexOf("\\begin{theorem}"), tex.indexOf("\\end{theorem}"));
    expect(env(corrected([COR]))).toBe(env(corrected(null)));
    expect(env(corrected([COR]))).toContain(CORRECTED);
    expect(corrected([COR])).toContain(`\\textit{Corollary (the Gaussian case).} ${COR.statement}`);
  });

  it("the page: a red block, a blue block, and each corollary a blue block headed \"Corollary of <the result>\"", () => {
    const tex = annotated({ patches: { patches: [patch([COR])], unfixable: [] } });
    const html = renderPaper({ files: { "main.tex": tex }, main: "main.tex", aux: String.raw`\newlabel{thm:main}{{5.2}{3}}` }).html;
    const blocks = [...html.matchAll(/<div class="(rv [^"]*)"[^>]*>(?:<span class="res-anchor"[^>]*><\/span>)?<span class="(?:rv-tag|env)">(.*?)<\/span>/gu)].map((m) => [m[1], m[2]!.replace(/<[^>]+>/gu, "")]);
    // the result's own proof (and its notes and readings) stay with it; its corollaries come after
    expect(blocks.slice(0, 4)).toEqual([["rv del", "Original"], ["rv ins", "Corrected"], ["rv ins", "Corrected proof (confirmed)"], ["rv ins cor formal k-corollary", "Corollary 5.2.1."]]);
    const pending = renderPaper({ files: { "main.tex": annotated({ pending: { weakening: [{ node: "thm:main", corrected_statement: null, ops, given_up: "g", detail: "d", witness: "w", corollaries: [COR] }], rewind: null, cap: null } }) }, main: "main.tex", aux: "" }).html;
    expect(pending).toMatch(/<div class="rv ins cor pending formal k-corollary" tabindex="0" data-res="[^"]*"[^>]*>.*<span class="env">Corollary [^<]*\.<\/span> <span class="rv-tag">Proposed — awaiting a ruling<\/span>/u);
    // in every view it is the corrected block it is: no rule of its own for its colour or whether it shows
    const css = readFileSync(path.join(import.meta.dirname, "..", "..", "src", "ui", "static", "app.css"), "utf8");
    expect(css.split("\n").filter((l) => l.includes(".rv.cor") && !l.includes(".rv-tag") && /color|background|display: none/u.test(l))).toEqual([]);
  });
});

describe("a repair's text never opens a theorem-like environment: a result that stands apart is a corollary entry", () => {
  const core = { statements: [{ id: "thm:main", statement: "The estimator is normal and efficient.", proof_tex: "By the claim. \\begin{claim} A. \\end{claim}" }], assumptions: [], definitions: [] } as unknown as Core;
  const nested = `${GENERAL}. \\begin{corollary}[the Gaussian case] ${COR.statement} \\end{corollary}`;
  const violations = (patchOver: Record<string, unknown>, newtheorem: Record<string, "theorem" | "corollary" | "remark"> = {}): string[] =>
    repairTextViolations(core, file({ patches: [split({ owner_explanation: null, ...patchOver })] }), null, newtheorem).filter((v) => v.includes("environment of its own"));

  it("in an op (named once, not again on the statement derived from it), in a corrected statement stored whole, and in a corollary's statement", () => {
    const inOp = violations({ corrected_statement: nested, ops: [{ op: "replace", unit: "thm:main/1/1", tex: nested }], corollaries: null });
    expect(inOp).toEqual([expect.stringContaining('the patch for "thm:main": states a result in an environment of its own in `ops[0] (replace)` (\\begin{corollary})')]);
    expect(inOp[0]).toContain("return a result that stands apart as an entry of `corollaries`");
    expect(violations({ corrected_statement: nested, ops: [], corollaries: null })).toEqual([expect.stringContaining("in `corrected_statement` (\\begin{corollary})")]);
    expect(violations({ corollaries: [{ ...COR, statement: `\\begin{lemma} ${COR.statement} \\end{lemma}` }] })).toEqual([expect.stringContaining("in `corollaries[0].statement` (\\begin{lemma})")]);
    expect(violations({})).toEqual([]);
  });

  it("the paper's own theorem environments count, a starred one too; an environment the printed text it replaces already opens, and one that states no result, do not", () => {
    const op = (tex: string, unit = "thm:main/1/1") => ({ corrected_statement: null, ops: [{ op: "replace", unit, tex }], corollaries: null });
    expect(violations(op("A. \\begin{kor*} B. \\end{kor*}"))).toEqual([]);
    expect(violations(op("A. \\begin{kor*} B. \\end{kor*}"), { kor: "corollary" })).toEqual([expect.stringContaining("(\\begin{kor})")]);
    expect(violations(op("A. \\begin{note} B. \\end{note}"), { note: "remark" })).toEqual([]);
    expect(violations(op("A. \\begin{enumerate}\\item B. \\end{enumerate}"))).toEqual([]);
    expect(violations(op("By the claim. \\begin{claim} A'. \\end{claim}", "thm:main/proof/1/1"))).toEqual([]);
    expect(violations(op("\\begin{claim} A. \\end{claim}"))).toEqual([expect.stringContaining("(\\begin{claim})")]);
  });

  it("the fixer's prompt states the rule", async () => {
    const prompt = (await readFile(path.join(import.meta.dirname, "..", "..", "src", "verify", "prompts", "V1", "patch.txt"), "utf8")).replace(/\s+/gu, " ");
    expect(prompt).toContain("neither it nor a corollary's `statement` opens a theorem-like environment");
    // `follows` is the corollary's proof (the corrected paper prints it as one), and the referee grades it so
    expect(prompt).toContain("`follows` is its complete proof");
    expect((await readFile(path.join(import.meta.dirname, "..", "..", "src", "verify", "prompts", "V1.5", "review.txt"), "utf8")).replace(/\s+/gu, " ")).toContain("`follows`, its complete proof, graded as any proof");
  });
});

describe("the corrected paper: a corollary's proof goes where the paper puts the proof of its result", () => {
  const BODY = "The estimator is normal and efficient.";
  const STMT = ["\\begin{theorem}\\label{thm:main}", BODY, "\\end{theorem}"];
  const PROOF = ["\\begin{proof}[Proof of Theorem~\\ref{thm:main}]", "By the central limit theorem.", "\\end{proof}"];
  const COR2 = { title: null, statement: "If the errors are bounded, the estimator of Theorem~\\ref{thm:main} is efficient up to a constant.", follows: "Bounded errors have all moments, so Theorem~\\ref{thm:main} applies; the constant is that of Lemma~\\ref{lem:c}." };
  const one = (): Core => ({ qid: "a", symbols: [], assumptions: [], definitions: [], statements: [{ id: "thm:main", kind: "theorem", statement: BODY, depends_on: [], status: "to-prove", tex_locator: { file: "main.tex", from: 3, to: 5, env: "theorem", label: "thm:main" } }], target_estimand: "t", bibliography: [] } as unknown as Core);
  /** The corrected files of a paper whose theorem (main.tex, lines 3-5) is split, its printed proof at `proofLines`. */
  const planInput = (files: Record<string, string>, proofLines: { file: string; from: number; to: number } | null, corollaries: unknown[], proof_note = "The proof as printed proves the repaired statement; no step changes."): AnnotationInput => ({
    files,
    envs: { main_file: "main.tex", files: Object.keys(files), newtheorem: {}, bibliography: [], envs: [{ id: "thm:main", kind: "theorem", envName: "theorem", label: "thm:main", title: null, body: BODY, proof: proofLines ? "By the central limit theorem." : null, proofLines, section: null, lines: { file: "main.tex", from: 3, to: 5 }, refs: [] }] } as never,
    flatText: Object.values(files).join("\n"), lineMap: Object.entries(files).flatMap(([file, t]) => t.split("\n").map((_, i) => ({ file, line: i + 1 }))), refs: null, transcribed: one(), core: one(),
    patches: { patches: [{ node: "thm:main", corrected_statement: "The estimator is normal.", proof_note, corollaries }], unfixable: [] } as never, paperErrors: { "thm:main": { detail: "efficiency fails", witness: "w" } }, findings: [], review: null, correctedView: true,
  });
  const corrected = (files: Record<string, string>, proofLines: { file: string; from: number; to: number } | null, corollaries: unknown[], opts: Parameters<typeof correctedTex>[1] = { proofEnv: true }, proof_note?: string): Record<string, string> => {
    const plan = planAnnotations(planInput(files, proofLines, corollaries, proof_note));
    expect(plan.unlocated).toEqual([]);
    return Object.fromEntries(Object.entries(files).map(([f, t]) => [f, correctedTex(applyTexEdits(t, plan.edits[f] ?? []), opts).tex]));
  };
  const doc = (...lines: string[]): string => ["\\documentclass{article}", "\\begin{document}", ...lines, "\\end{document}"].join("\n");
  const stmt = (c: { title: string | null; statement: string }): string => `\\noindent\\textit{Corollary${c.title ? ` (${c.title})` : ""}.} ${c.statement}`;

  const proofOf = (c: { follows: string }, head = ""): string => `\\begin{proof}${head}\n${c.follows}\n\\end{proof}`;
  const THM = [STMT[0], "The estimator is normal.", STMT[2]].join("\n");
  const APPENDIX = { "main.tex": doc(...STMT, "Text.", "\\input{appendix}"), "appendix.tex": ["\\section{Proofs}", ...PROOF, "More."].join("\n") };
  const AT = { file: "appendix.tex", from: 2, to: 4 };

  it("the result's proof follows its statement: the corollary and its proof come after that proof", () => {
    const out = corrected({ "main.tex": doc(...STMT, ...PROOF, "Text.") }, { file: "main.tex", from: 6, to: 8 }, [COR]);
    expect(out["main.tex"]).toBe(doc(THM, ...PROOF, "", stmt(COR), "", proofOf(COR), "", "Text."));
  });

  it("the result's proof is elsewhere (an appendix file, a later section): the corollary's statement follows the result, its proof follows the result's proof there, named", () => {
    const out = corrected(APPENDIX, AT, [COR]);
    expect(out["main.tex"]).toBe(doc(THM, "", stmt(COR), "", "Text.", "\\input{appendix}"));
    expect(out["appendix.tex"]).toBe(["\\section{Proofs}", ...PROOF, "", proofOf(COR, "[Proof of the corollary (the Gaussian case)]"), "", "More."].join("\n"));
    // a numbered corollary is named by its number
    const numbered = corrected(APPENDIX, AT, [COR], { proofEnv: true, corollaryEnv: { name: "cor", numbered: true } });
    expect(numbered["main.tex"]).toContain(`\\end{theorem}\n\n\\begin{cor}[the Gaussian case]\\label{${COR_ID}}\n${COR.statement}\n\\end{cor}\n\nText.`);
    expect(numbered["appendix.tex"]).toContain(`${PROOF[2]}\n\n${proofOf(COR, `[Proof of Corollary~\\ref{${COR_ID}}]`)}\n\nMore.`);
    // a later section of the same file; a paper without a proof environment
    const later = corrected({ "main.tex": doc(...STMT, "Text.", "\\section{Proofs}", ...PROOF, "More.") }, { file: "main.tex", from: 8, to: 10 }, [COR], { proofEnv: false });
    expect(later["main.tex"]).toBe(doc(THM, "", stmt(COR), "", "Text.", "\\section{Proofs}", ...PROOF, "", `\\noindent\\textit{Proof of the corollary (the Gaussian case).} ${COR.follows}`, "", "More."));
  });

  it("no proof of the result is located: the corollary's proof follows the corollary", () => {
    const out = corrected({ "main.tex": doc(...STMT, "Text.") }, null, [COR]);
    expect(out["main.tex"]).toBe(doc(THM, "", stmt(COR), "", proofOf(COR), "", "Text."));
  });

  it("several corollaries keep their order in both places; their proofs come after the result's own corrected proof", () => {
    const out = corrected(APPENDIX, AT, [COR, COR2], { proofEnv: true }, "Normality is the central limit theorem.");
    expect(out["main.tex"]).toBe(doc(THM, "", stmt(COR), "", stmt(COR2), "", "Text.", "\\input{appendix}"));
    expect(out["appendix.tex"]).toBe(["\\section{Proofs}", ...PROOF, "", "\\begin{proof}\nNormality is the central limit theorem.\n\\end{proof}", "", proofOf(COR, "[Proof of the corollary (the Gaussian case)]"), "", proofOf(COR2, "[Proof of the corollary]"), "", "More."].join("\n"));
    const inline = corrected({ "main.tex": doc(...STMT, ...PROOF, "Text.") }, { file: "main.tex", from: 6, to: 8 }, [COR, COR2]);
    expect(inline["main.tex"]).toBe(doc(THM, ...PROOF, "", stmt(COR), "", proofOf(COR), "", stmt(COR2), "", proofOf(COR2), "", "Text."));
  });

  it("the review views keep the proof inside the corollary's block, wherever the result is proved", () => {
    const plan = planAnnotations({ ...planInput(APPENDIX, AT, [COR]), correctedView: false });
    expect(applyTexEdits(APPENDIX["appendix.tex"], plan.edits["appendix.tex"] ?? [])).not.toContain("vsCorollary");
    expect(applyTexEdits(APPENDIX["main.tex"], plan.edits["main.tex"] ?? [])).toContain(`${COR.statement} \\vsLine\\textit{Proof.} ${COR.follows}}`);
  });
});
