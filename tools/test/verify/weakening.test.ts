/**
 * Repairs never weaken the contribution: the fixer's `unfixable` + `suggested_repair`, the referee's
 * `weakens_contribution` grade, the owner's halt, and both answers. Fixer and referee faked; no
 * network.
 */
import { ownerWordsTex } from "../../src/verify/owner_text.js";
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it, vi } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { StateJson } from "../../src/types.js";
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState, loadState, saveState } from "../../src/state.js";
import { statePath, verifyRunDir } from "../../src/paths.js";
import { PATCH_REPLY_JSON_SCHEMA, PatchFileSchema, rebuildPatchedCore, validatePatchFile, type PatchFile } from "../../src/verify/patches.js";
import { runVerifyPipeline } from "../../src/verify/pipeline.js";
import { runStageV1 } from "../../src/verify/stage_v1.js";
import { acceptV1_5AtCap, runStageV1_5 } from "../../src/verify/stage_v1_5.js";
import { MAX_SUGGESTION_REJECTIONS, VERIFY_FILES, type V15NodeVerdict, type V15Review, type VerifyStage } from "../../src/verify/types.js";
import { recordWeakeningReceipt, ruleOnReceipt, weakeningMessage } from "../../src/verify/weakening.js";
import { rejectWeakeningFinding } from "../../src/verify/owner_rulings.js";
import { bindingReadings, renderBindingReadings } from "../../src/verify/core_graph.js";
import { buildReport } from "../../src/verify/report.js";
import { tk } from "../toolkit/helpers.js";
import { cannedExplanation, withOwnerExplanations, writeToyPaper } from "./owner_explained.js";
import { cannedCodex, isRefereeCall, isRefereeGlobal } from "./referee_fake.js";

const QID = "weak_paper";
const tmpDirs: string[] = [];
afterEach(async () => {
  for (const dir of tmpDirs.splice(0)) await rm(dir, { recursive: true, force: true });
});

/** lem:rate is used by thm:main (the headline) and thm:side; prop:aside stands alone. */
function core(): Core {
  return {
    qid: QID,
    symbols: [{ name: "\\hat p", type: "estimated propensity" }],
    assumptions: [
      { id: "ass:overlap", condition: "\\(\\hat p < 1 - \\eta\\)", novel: { flag: true, justification: "Assumption 1" }, used_by: ["lem:rate"] },
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

const WITNESS = "$\\hat p \\to 0$ on a sequence of designs";
const GIVEN_UP = "the root-n rate: only n^{-1/4} holds under one-sided overlap";
/** A suggested repair of `node`: its statement unit (`<node>/1/1` in the toy paper) replaced by `tex`. */
const sug = (node: string, tex: string, given_up = GIVEN_UP, proof_note = "the second display is bounded by n^{-1/4}; every other step is unchanged.") => ({
  corrected_statement: tex,
  ops: [{ op: "replace" as const, unit: `${node}/1/1`, tex }],
  proof_note,
  given_up,
});
const SUGGESTION = sug("lem:rate", "the rate is \\(n^{-1/4}\\)");
/** An unfixable entry carrying a suggestion; its note's `gives_up` says what the suggestion gives up (the
 * runner reads the suggestion's `given_up` from it). */
const unfix = (node: string, suggested_repair: ReturnType<typeof sug>, reason = "r") => ({
  node,
  reason,
  suggested_repair,
  owner_explanation: { ...cannedExplanation(node), gives_up: suggested_repair.given_up },
});

/** `lem:rate` is a key result here, so a suggestion on it is the OWNER's (a main theorem); the
 * owner-scope tests below drop it to exercise the automatic narrowing of an intermediate result. */
function file(over: Partial<PatchFile> = {}): PatchFile {
  return PatchFileSchema.parse({ key_results: ["thm:main", "lem:rate"], key_contribution: "asymptotic normality of the estimator", patches: [], unfixable: [], ...over });
}

const fakeCodex = (replies: unknown[], calls: CodexRunInput[]): typeof runCodex => cannedCodex(replies, calls);

async function setup(opts: { repoRoot?: string; runDir?: string } = {}) {
  const repoRoot = opts.repoRoot ?? (await mkdtemp(path.join(os.tmpdir(), "verify-weak-")));
  if (!opts.repoRoot) tmpDirs.push(repoRoot);
  const runDir = opts.runDir ?? path.join(repoRoot, "runs", QID);
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  for (const f of [VERIFY_FILES.coreJson, VERIFY_FILES.coreTranscribed]) await writeFile(path.join(runDir, f), JSON.stringify(core(), null, 2), "utf8");
  await writeFile(path.join(runDir, VERIFY_FILES.flatTex), "\\begin{lemma}the rate\\end{lemma}\n", "utf8");
  await writeToyPaper(runDir, core());
  const state = createVerifyInitialState(QID, {
    phase: "init",
    source: { input: "paper.tex", main_file: "main.tex", sha256: "h" },
    targets: null,
    core_sha256: null,
    v1_rounds: 1,
    v1_5_rounds: 0,
    findings: [],
    report_path: null,
  });
  state.verify!.paper_errors = { "lem:rate": { detail: "1/p̂ is unbounded", witness: WITNESS } };
  const calls: CodexRunInput[] = [];
  const args = (replies: unknown[]) => ({ repoRoot, qid: QID, runDir, state, deps: { runCodex: fakeCodex(replies, calls) }, dryRun: false, log: () => {} });
  const directive = (findings: unknown[]) => writeFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), JSON.stringify({ mode: "patch", round: 1, findings }), "utf8");
  const patches = async (): Promise<PatchFile> => PatchFileSchema.parse(JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.patches), "utf8")));
  return { repoRoot, runDir, state, calls, args, directive, patches };
}

type Setup = Awaited<ReturnType<typeof setup>>;

const finding = { id: "lem:rate", axis: "correctness", detail: "1/p̂ is unbounded", witness: WITNESS };

function grade(id: string, over: Partial<V15NodeVerdict> = {}): V15NodeVerdict {
  return { id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "reproduced", witness: null, bookkeeping_assumption: null, reading: null, ...over };
}

/** A referee reply grading every node of the current `core.json` and of the transcription (a pending
 * suggestion's node is out of `core.json` but graded as a patch by the pass that confirms its receipt). */
async function review(r: Setup, over: Record<string, Partial<V15NodeVerdict>> = {}): Promise<V15Review> {
  const c = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
  const ids = [...new Set([c, core()].flatMap((k) => [...k.statements, ...k.assumptions, ...k.definitions].map((n) => n.id)))];
  return { verdict: "PASS", summary: "s", nodes: ids.map((id) => grade(id, over[id])), patch_review: { key_results_ok: true, detail: "thm:main is the headline" } };
}

/** The render's routing of a repair text of `node` that does not compile (`fragment_routing.ts`: what
 * `restateAllPatches` is given). */
const COMPILE_ERROR = "Missing $ inserted.";
const compileFails = (node: string, text: string) =>
  new Map([[node, [{ where: `the corrected statement the paper prints for "${node}"`, text, error: COMPILE_ERROR }]]]);

/** The halt the fixer leaves when no repair keeps lem:rate at full strength. */
async function haltedOnSuggestion(): Promise<Setup> {
  const r = await setup();
  await r.directive([finding]);
  const result = await runStageV1(r.args([file({ unfixable: [unfix("lem:rate", SUGGESTION, "the root-n rate needs two-sided overlap, which the paper excludes")] })]));
  expect(result.status).toBe("checkpoint");
  return r;
}

describe("the fixer's contract", () => {
  it("the reply schema requires a suggested_repair (patch body: replacement ops and the proof) on every unfixable entry; one whose note gives nothing up is recorded as it is", async () => {
    const items = ((PATCH_REPLY_JSON_SCHEMA.properties as Record<string, { items: { required: string[]; properties: Record<string, { anyOf: Array<{ required?: string[] }> }> } }>).unfixable).items;
    expect(items.required).toEqual(["node", "reason", "suggested_repair", "owner_explanation"]);
    expect(items.properties.suggested_repair.anyOf[0]!.required).toEqual(["ops", "drops", "adds", "readings", "conditions", "corollaries", "umbrella", "proof_note"]);
    const r = await setup();
    await r.directive([finding]);
    const silent = file({ unfixable: [{ ...unfix("lem:rate", SUGGESTION), owner_explanation: cannedExplanation("lem:rate") }] });
    const result = await runStageV1(r.args([silent]));
    expect(result.status).toBe("checkpoint");
    expect(r.calls).toHaveLength(1);
    expect(r.state.verify!.weakening_repair!.items[0]!.given_up).toBe("");
  });

  it("no non-weakening repair on a main theorem → the run halts with the suggestion, recorded in the ledger; on an intermediate result it is applied", async () => {
    const r = await haltedOnSuggestion();
    const rec = r.state.verify!.weakening_repair!;
    expect(rec).toMatchObject({ status: "pending", items: [{ node: "lem:rate", printed: "the rate is \\(n^{-1/2}\\)", proposed: SUGGESTION.corrected_statement, given_up: SUGGESTION.given_up, witness: WITNESS, source: "fixer" }] });
    expect(r.state.verify!.paper_errors!["lem:rate"]).toMatchObject({ weakens_contribution: true, suggested_repair: expect.stringContaining("gives up: the root-n rate") });
    const saved = await r.patches();
    expect(saved.unfixable).toEqual([expect.objectContaining({ node: "lem:rate", suggested_by: "fixer", reason: expect.stringContaining("the root-n rate needs") })]);
    expect(saved.patches).toEqual([]);
    expect(existsSync(path.join(r.runDir, VERIFY_FILES.v1ReviseDirective))).toBe(false);
    expect(r.state.verify!.findings).toEqual([]); // nothing is refuted until the owner rules

    // a side result (a proposition, not a key result) is intermediate: its strongest true version
    // is applied at once, and the narrowed core goes to V1.5 — no halt
    const side = await setup();
    side.state.verify!.paper_errors = { "prop:aside": { detail: "the identity is false", witness: "x = 1" } };
    await side.directive([{ id: "prop:aside", axis: "correctness", detail: "the identity is false", witness: "x = 1" }]);
    const out = await runStageV1(side.args([file({ unfixable: [unfix("prop:aside", sug("prop:aside", "a weaker identity"))] })]));
    expect(out.status).toBe("completed");
    expect(side.state.verify!.weakening_repair ?? null).toBeNull();
    const narrowed = await side.patches();
    expect(narrowed.unfixable).toEqual([]);
    expect(narrowed.patches).toEqual([expect.objectContaining({ node: "prop:aside", corrected_statement: "a weaker identity", accepted_weakening: true, narrowed_by: "runner", given_up: SUGGESTION.given_up })]);
    expect(side.state.verify!.paper_errors!["prop:aside"]).toMatchObject({ weakens_contribution: true, auto_narrowed: true });
    const built = JSON.parse(await readFile(path.join(side.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
    expect(built.statements.find((st) => st.id === "prop:aside")!.statement).toBe("a weaker identity");
  });

  it("a repair that restates the result with an added hypothesis and keeps the conclusion is a patch: no halt", async () => {
    const r = await setup();
    await r.directive([finding]);
    const TEX = "If \\(\\eta < \\hat p < 1 - \\eta\\), the rate is \\(n^{-1/2}\\)";
    const tightened = file({
      patches: [{ node: "lem:rate", corrected_statement: null, ops: [{ op: "replace", unit: "lem:rate/1/1", tex: TEX }], proof_note: "bound $1/\\hat p$ by $1/\\eta$ in the second display" }],
    });
    const result = await runStageV1(r.args([tightened]));
    expect(result.status).toBe("completed");
    expect(r.state.verify!.weakening_repair).toBeUndefined();
    const saved = await r.patches();
    expect(saved.patches.map((p) => p.node)).toEqual(["lem:rate"]);
    expect(saved.patches[0]!.corrected_statement).toContain("If \\(\\eta < \\hat p < 1 - \\eta\\)");
  });
});

describe("the referee's weakening grade", () => {
  async function patched(): Promise<Setup> {
    const r = await setup();
    r.state.verify!.phase = "v1";
    await writeFile(
      path.join(r.runDir, VERIFY_FILES.patches),
      JSON.stringify(file({ patches: [{ node: "lem:rate", ...SUGGESTION, given_up: undefined } as never] })),
      "utf8",
    );
    return r;
  }
  const weakens = { correctness: "error" as const, weakens_contribution: true, detail: "weakens the contribution: the root-n rate becomes n^{-1/4}; two-sided overlap would keep it", witness: "the printed n^{-1/2} rate is given up" };

  it("routes the node to the owner's halt, never back to the fixer (a confirming referee pass presents it; no fixer call)", async () => {
    const r = await patched();
    const result = await runStageV1_5(r.args([await review(r, { "lem:rate": weakens })]));
    // the patch becomes a suggestion; its receipt waits for the pass that grades it
    expect(result.status).toBe("narrowed");
    expect(r.state.verify!.weakening_repair).toMatchObject({ status: "pending", unconfirmed: true, items: [{ node: "lem:rate", source: "referee" }] });
    const before = r.calls.length;
    const second = await runStageV1_5(r.args([await review(r)]));
    expect(second.status).toBe("checkpoint");
    expect(r.state.verify!.weakening_repair!.unconfirmed).toBeUndefined();
    expect(r.calls.length).toBeGreaterThan(before);
    expect(r.calls.every(isRefereeCall)).toBe(true);
    const saved = await r.patches();
    expect(saved.patches).toEqual([]);
    expect(saved.unfixable).toEqual([
      expect.objectContaining({ node: "lem:rate", suggested_by: "referee", suggested_repair: expect.objectContaining({ corrected_statement: SUGGESTION.corrected_statement, given_up: expect.stringContaining("two-sided overlap would keep it") }) }),
    ]);
    expect(r.state.verify!.weakening_repair).toMatchObject({ status: "pending", items: [{ node: "lem:rate", source: "referee" }] });
  });

});

describe("the owner's answer", () => {
  it("--accept-repair: the suggestion becomes a patch, the confirming pass accepts it, and it is a repair that narrows the contribution", async () => {
    const r = await haltedOnSuggestion();
    const line = (await ruleOnReceipt(r.runDir, r.state, { accept: ["lem:rate"] })).join(" ");
    expect(line).toContain("--accept-repair");
    const saved = await r.patches();
    expect(saved.unfixable).toEqual([]);
    expect(saved.patches).toEqual([expect.objectContaining({ node: "lem:rate", corrected_statement: SUGGESTION.corrected_statement, accepted_weakening: true, given_up: SUGGESTION.given_up })]);
    expect(r.state.verify!).toMatchObject({ phase: "v1", core_sha256: null, weakening_repair: { status: "accepted" } });
    expect(r.state.verify!.paper_errors!["lem:rate"]).toMatchObject({ owner_decision: "accepted", weakens_contribution: true });
    const c = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
    expect(c.statements.find((s) => s.id === "lem:rate")!.statement).toContain("n^{-1/4}");
    // the referee still calls it a weakening: the owner ruled on exactly that, so it stands
    r.calls.length = 0;
    const result = await runStageV1_5(r.args([await review(r, { "lem:rate": { correctness: "error", weakens_contribution: true, detail: "weakens the contribution: n^{-1/4}", witness: "w" } })]));
    expect(result.status).toBe("completed");
    expect(r.state.verify!.findings).toEqual([
      expect.objectContaining({ node: "lem:rate", kind: "refuted", witness: WITNESS, patch: expect.objectContaining({ confirmed: true, narrowed: SUGGESTION.given_up }) }),
    ]);
  });

  it("--decline-repair: refuted with the declined suggestion, descoped with every result resting on it (key results too), and the rest is accepted", async () => {
    const r = await haltedOnSuggestion();
    await ruleOnReceipt(r.runDir, r.state, { decline: [{ node: "lem:rate", reason: "root-n is the point" }] });
    const saved = await r.patches();
    expect(saved.unfixable).toEqual([expect.objectContaining({ node: "lem:rate", declined: "root-n is the point" })]);
    expect(r.state.verify!.paper_errors!["lem:rate"]).toMatchObject({ owner_decision: "declined", decision_reason: "root-n is the point" });
    const c = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
    expect(c.statements.map((s) => s.id)).toEqual(["prop:aside"]);
    r.calls.length = 0;
    const result = await runStageV1_5(r.args([await review(r)]));
    expect(result.status).toBe("completed");
    const byNode = new Map(r.state.verify!.findings.map((f) => [f.node, f] as const));
    expect(byNode.get("lem:rate")).toMatchObject({ kind: "refuted", witness: WITNESS, descoped: true, suggested_repair: expect.stringContaining("n^{-1/4}"), suggestion_declined: "root-n is the point" });
    expect(byNode.get("thm:main")).toMatchObject({ kind: "unresolved", descoped: true, detail: expect.stringContaining("the owner declined") });
    expect(byNode.get("thm:side")).toMatchObject({ kind: "unresolved", descoped: true });
  });

});

describe("the owner withdraws the finding (--reject-finding)", () => {
  const READING = "the probability is conditional on the training sample, so the bound is a statement about the realized nuisances";

  it("the printed statement stands under the owner's pinned reading; the finding is withdrawn from the ledger and the report", async () => {
    const r = await haltedOnSuggestion();
    const line = await rejectWeakeningFinding(r.runDir, r.state, READING);
    expect(line).toContain("--reject-finding");
    const saved = await r.patches();
    expect(saved.unfixable).toEqual([]);
    // The ruling's one record: the reading and the finding it withdrew.
    expect(saved.owner_readings).toEqual([
      { id: "ass:pin-owner-1", node: "lem:rate", reading: READING, withdraws: [expect.objectContaining({ axis: "correctness", stage: "V1.5", route: "weakening halt", detail: "1/p̂ is unbounded" })] },
    ]);
    const v = r.state.verify!;
    expect(v).toMatchObject({ phase: "v1", core_sha256: null, weakening_repair: { status: "finding rejected", reason: READING } });
    expect(v.paper_errors!["lem:rate"]).toMatchObject({ owner_decision: "finding rejected", decision_reason: READING, owner_overruled: true, detail: "1/p̂ is unbounded" });
    expect(v.rejected_rewinds).toEqual([expect.objectContaining({ node: "lem:rate", axis: "correctness", stage: "V1.5", by: "owner", pin: "ass:pin-owner-1", reason: READING })]);
    // the core: the printed text, plus the owner's reading wired in — binding for the F stages
    const c = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
    const lem = c.statements.find((s) => s.id === "lem:rate")!;
    expect(lem.statement).toBe(core().statements[0]!.statement);
    expect(lem.depends_on).toContain("ass:pin-owner-1");
    expect(c.assumptions.find((a) => a.id === "ass:pin-owner-1")).toMatchObject({ condition: READING, bookkeeping: { added_by: "owner" } });
    expect(renderBindingReadings(bindingReadings(c, "lem:rate"))).toContain(`ass:pin-owner-1 (reading of lem:rate, adopted by the paper's owner): ${READING}`);
    expect(renderBindingReadings(bindingReadings(c, "thm:main"))).toBe(""); // wired into the node only

    // The next pass: the referee raises the same error again — overruled, a note, never a halt.
    r.calls.length = 0;
    const again = { correctness: "error" as const, detail: "the random bound is false", witness: WITNESS };
    // (no repair is left on file, so the pass judges no key-result list)
    const result = await runStageV1_5(r.args([{ ...(await review(r, { "lem:rate": again })), patch_review: null }]));
    expect(result.status).toBe("completed");
    const saved2 = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v15Review), "utf8")) as V15Review;
    expect(saved2.verdict).toBe("PASS");
    expect(saved2.nodes.find((n) => n.id === "lem:rate")).toMatchObject({ correctness: "ok", owner_overruled: true, owner_reason: READING, witness: null });
    const onRate = v.findings.filter((f) => f.node === "lem:rate");
    expect(onRate.map((f) => f.kind)).toEqual(["note", "note"]);
    expect(onRate.map((f) => f.detail).join("\n")).toMatch(/finding withdrawn by the paper's owner[\s\S]*raised again a finding the paper's owner withdrew/);
    expect(v.findings.some((f) => f.kind === "refuted")).toBe(false);

    // The report lists it as withdrawn, never as refuted or repaired.
    const withdrawn = v.rejected_rewinds!.filter((x) => x.by === "owner").map((x) => ({ node: x.node, stage: x.stage, finding: x.detail, reason: x.reason, pin: x.pin ?? null }));
    const { md, json } = buildReport({
      qid: QID,
      withdrawn,
      envs: { main_file: "main.tex", files: [], envs: [] } as never,
      scope: [],
      core: c,
      review: saved2,
      findings: v.findings,
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
    });
    expect(json.withdrawn_findings).toEqual([{ node: "lem:rate", stage: "V1.5", finding: "1/p̂ is unbounded", reason: READING, pin: "ass:pin-owner-1" }]);
    expect(md).toContain("## Findings withdrawn by the owner");
    expect(md).toContain(`\`lem:rate\` (raised at V1.5): the owner's reading (\`ass:pin-owner-1\`): ${READING}`);
    expect(json.verdict).not.toBe("errors_found");
  });

  it("covers the batch; a later withdrawal numbers its pin after the earlier ones", async () => {
    const r = await setup();
    await r.directive([finding, { id: "prop:aside", axis: "correctness", detail: "the identity is false", witness: "x = 1" }]);
    const suggest = (node: string) => unfix(node, sug(node, "a weaker claim"));
    await runStageV1(r.args([file({ key_results: ["thm:main", "lem:rate", "prop:aside"], unfixable: [suggest("lem:rate"), suggest("prop:aside")] })]));
    expect(r.state.verify!.weakening_repair!.items.map((i) => i.node)).toEqual(["lem:rate", "prop:aside"]);
    // the owner splits the batch: withdraw only prop:aside now
    r.state.verify!.weakening_repair!.items = r.state.verify!.weakening_repair!.items.filter((i) => i.node === "prop:aside");
    await rejectWeakeningFinding(r.runDir, r.state, READING);
    const saved = await r.patches();
    expect(saved.owner_readings!.map((o) => [o.id, o.node])).toEqual([["ass:pin-owner-1", "prop:aside"]]);
    expect(saved.unfixable.map((u) => u.node)).toEqual(["lem:rate"]); // still pending: presented again
    expect(validatePatchFile(core(), saved, ["lem:rate"])).toEqual([]);
    // a later fixer reply cannot drop the owner's reading
    const { pinOwnerEntries } = await import("../../src/verify/weakening.js");
    expect(pinOwnerEntries(file(), saved).owner_readings).toEqual(saved.owner_readings);
  });
});

describe("the pipeline halt", () => {
  it("halts in auto mode, re-presents on a plain --resume, and continues to F1 on either answer", async () => {
    for (const answer of ["accept", "decline", "reject"] as const) {
      const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-weak-pipe-"));
      tmpDirs.push(repoRoot);
      const runDir = verifyRunDir(repoRoot, QID);
      const seen: string[] = [];
      let v1Calls = 0;
      const v1: VerifyStage = async ({ state }) => {
        v1Calls += 1;
        seen.push(`V1@${state.verify!.phase}`);
        const r = await setup({ repoRoot, runDir });
        const f = file({ unfixable: [{ node: "lem:rate", reason: "r", suggested_repair: SUGGESTION }] });
        await writeFile(path.join(runDir, VERIFY_FILES.patches), JSON.stringify(f), "utf8");
        state.verify!.paper_errors = r.state.verify!.paper_errors;
        recordWeakeningReceipt(state, core(), f);
        return { status: "checkpoint", message: "suggestion pending" };
      };
      const v1_5: VerifyStage = async ({ state }) => {
        const rec = state.verify!.weakening_repair;
        seen.push(`V1.5@${state.verify!.phase}${rec?.unconfirmed ? " confirming" : ""}`);
        // the confirming pass grades the suggestion and, nothing left for the fixer, presents the receipt
        if (rec?.status === "pending" && rec.unconfirmed) {
          const { unconfirmed: _u, ...presented } = rec;
          state.verify!.weakening_repair = presented;
          return { status: "checkpoint", message: "confirmed; the receipt awaits the owner" };
        }
        state.stage_completed = "V1.5";
        return { status: "completed", message: "ok" };
      };
      const formal: string[] = [];
      const annotatedAt: string[] = [];
      const args = {
        toolkit: tk(repoRoot),
        qid: QID,
        input: "/papers/weak_paper.tex",
        mainHint: null,
        targets: null,
        resume: false,
        fromStage: null as string | null,
        auto: true,
        dryRun: true,
        deps: {
          prepareSource: async ({ sourceDir }: { sourceDir: string }) => { await mkdir(sourceDir, { recursive: true }); return { sourceDir, mainFile: "main.tex", sha256: "abc", inputKind: "tex" as const }; },
          annotate: (async ({ runDir, when }: { runDir: string; when: string }) => {
            annotatedAt.push(when);
            return { path: path.join(runDir, "annotated", "main.pdf"), line: path.join(runDir, "annotated", "main.pdf"), result: null, error: null };
          }),
        },
        stages: { v1, v1_5, v6: (async () => ({ status: "completed", message: "report" })) as VerifyStage },
        runPromotion: async () => ({ status: "empty" as const, batch_path: null, checklist_path: null, promoted: [] }),
        runFormalization: async ({ toolkit, qid, startStage }: { toolkit: { toolkitRoot: string }; qid: string; startStage?: string }) => {
          formal.push(String(startStage));
          const s = await loadState(toolkit.toolkitRoot, qid);
          s.stage_completed = "5";
          await saveState(toolkit.toolkitRoot, qid, s);
          return s;
        },
      };
      const spy = vi.spyOn(console, "log").mockImplementation(() => {});
      let verify = await runVerifyPipeline(args as never);
      const halt = spy.mock.calls.map((c) => String(c[0])).find((l) => l.includes("WEAKENED REPAIR:")) ?? "";
      spy.mockRestore();
      expect(verify.weakening_repair?.status).toBe("pending");
      // the owner is pointed at the annotated paper (the confirming V1.5 pass's), before the two answers
      expect(annotatedAt).toEqual(["V1.5"]);
      expect(halt.indexOf(`Review the annotated paper: ${path.join(runDir, "annotated", "main.pdf")}`)).toBeGreaterThan(0);
      expect(halt.indexOf("Review the annotated paper:")).toBeLessThan(halt.indexOf("Continue with one of:"));
      expect(formal).toEqual([]);
      verify = await runVerifyPipeline({ ...args, resume: true } as never);
      expect(v1Calls).toBe(1);
      await expect(runVerifyPipeline({ ...args, resume: true, declineRepair: "  " } as never)).rejects.toThrow(/needs a reason/);
      // a node-scoped decline naming no node of the core is an error, never a bare decline of every item
      await expect(runVerifyPipeline({ ...args, resume: true, declineRepair: "thm:nope: not the point" } as never)).rejects.toThrow(/thm:nope is not a node of the core/);
      expect((await loadState(repoRoot, QID)).verify!.weakening_repair).toMatchObject({ status: "pending", items: [expect.objectContaining({ node: "lem:rate" })] });
      // … the colon without a space is the node form too (it was read as a bare reason: every item declined), and a bare
      // reason that opens with a pending item's id is refused as ambiguous
      await expect(runVerifyPipeline({ ...args, resume: true, declineRepair: "thm:nope:not the point" } as never)).rejects.toThrow(/thm:nope is not a node of the core/);
      await expect(runVerifyPipeline({ ...args, resume: true, declineRepair: "lem:rate - not the point" } as never)).rejects.toThrow(/opens with the pending item lem:rate/);
      await expect(runVerifyPipeline({ ...args, resume: true, declineRepair: "lem:rate:" } as never)).rejects.toThrow(/needs a reason after the node/);
      await expect(runVerifyPipeline({ ...args, resume: true, rejectFinding: "thm:nope: the rate is stated" } as never)).rejects.toThrow(/opens with thm:nope, which is not a node of the core/);
      await expect(runVerifyPipeline({ ...args, resume: true, rejectFinding: "lem:rate is stated up to logs" } as never)).rejects.toThrow(/opens with lem:rate, but is not "<node>: <reading>"/);
      expect((await loadState(repoRoot, QID)).verify!.weakening_repair).toMatchObject({ status: "pending", items: [expect.objectContaining({ node: "lem:rate" })] });
      await expect(runVerifyPipeline({ ...args, resume: true, rejectFinding: "  " } as never)).rejects.toThrow(/needs the reading/);
      // an owner text not in TeX is refused with the answer's other checks, before any ruling is applied
      const patchesFile = path.join(runDir, VERIFY_FILES.patches);
      const patchesBefore = existsSync(patchesFile) ? await readFile(patchesFile, "utf8") : null;
      await expect(runVerifyPipeline({ ...args, resume: true, acceptRepair: ["lem:rate"], rejectFinding: ["lem:rate: for every γ ∈ Γ"] } as never)).rejects.toThrow(/must be written in TeX/);
      expect(existsSync(patchesFile) ? await readFile(patchesFile, "utf8") : null).toBe(patchesBefore);
      expect((await loadState(repoRoot, QID)).verify!.weakening_repair).toMatchObject({ status: "pending" });
      const flag = answer === "accept" ? { acceptRepair: true } : answer === "decline" ? { declineRepair: "root-n is the point" } : { rejectFinding: "the rate is stated conditionally on the design" };
      verify = await runVerifyPipeline({ ...args, resume: true, ...flag } as never);
      expect(verify.weakening_repair?.status).toBe(answer === "accept" ? "accepted" : answer === "decline" ? "declined" : "finding rejected");
      expect(seen).toEqual(["V1@init", "V1.5@v1 confirming", "V1.5@v1"]);
      expect(formal).toEqual(["1"]);
      expect(verify.phase).toBe("done");
      expect(existsSync(statePath(repoRoot, QID))).toBe(true);
      await expect(runVerifyPipeline({ ...args, resume: true, acceptRepair: true } as never)).rejects.toThrow(/requires a run halted at a suggested repair/);
    }
  });
});

describe("the owner downgrades an applied repair (--reject-finding \"<node>: …\", any halt)", () => {
  const READING = "the rate is stated conditionally on the design, so $\\hat p$ is bounded away from 0 on the event considered";
  const APPLIED = {
    node: "lem:rate",
    corrected_statement: "the rate is \\(n^{-1/2}\\) when \\(\\eta < \\hat p < 1 - \\eta\\)",
    ops: [{ op: "replace" as const, unit: "lem:rate/1/1", tex: "the rate is \\(n^{-1/2}\\) when \\(\\eta < \\hat p < 1 - \\eta\\)" }],
    proof_note: "bound $1/\\hat p$ by $1/\\eta$.",
  };
  async function applied(): Promise<Setup> {
    const r = await setup();
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(file({ patches: [APPLIED] })), "utf8");
    const { rebuildPatchedCore } = await import("../../src/verify/patches.js");
    await rebuildPatchedCore(r.runDir, { detectHandEdits: false });
    r.state.verify!.findings = [{ node: "lem:rate", stage: "V1.5", kind: "refuted", detail: "1/p̂ is unbounded", witness: WITNESS, at: "2026-09-24T00:00:00Z" }];
    return r;
  }

  // The reading form pins the printed statement (rendered); the bookkeeping form adds a binding side
  // condition that is never rendered and leaves the other repair standing.
  it.each([
    { kind: "reading" as const, node: "lem:rate", text: READING, pin: "ass:pin-owner-1", label: "reading", patchesLeft: [] as string[], rendered: true },
    { kind: "bookkeeping" as const, node: "prop:aside", text: "\\(x \\neq 0\\)", pin: "ass:bk-owner-1", label: "side condition", patchesLeft: ["lem:rate"], rendered: false },
  ])("the $kind form: parsed from \"<node>: …\", the finding withdrawn under an owner $pin", async ({ kind, node, text, pin, label, patchesLeft, rendered }) => {
    const { parseRejectFinding, rejectAppliedFindings } = await import("../../src/verify/owner_rulings.js");
    expect(parseRejectFinding(`${node}: ${kind === "bookkeeping" ? "bookkeeping: " : ""}${text}`, new Set(["lem:rate", "prop:aside"]))).toEqual({ node, kind, text });
    expect(parseRejectFinding("thm:unknown: r", new Set(["lem:rate"])).node).toBeNull();
    const r = await applied();
    if (node === "prop:aside") r.state.verify!.paper_errors = { ...r.state.verify!.paper_errors, "prop:aside": { detail: "the identity fails at x = 0", witness: "x = 0" } };
    const line = await rejectAppliedFindings(r.runDir, r.state, [{ node, kind, text }]);
    expect(line).toContain(`${node} → ${pin} (${label})`);
    const saved = await r.patches();
    expect(saved.patches.map((p) => p.node)).toEqual(patchesLeft);
    expect(saved.owner_readings).toEqual([
      { id: pin, node, reading: text, ...(kind === "bookkeeping" ? { kind } : {}), withdraws: [expect.objectContaining({ axis: "correctness", stage: "V1.5", route: "applied repair" })] },
    ]);
    const c = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
    const st = c.statements.find((s) => s.id === node)!;
    expect(st.statement).toBe(core().statements.find((s) => s.id === node)!.statement);
    expect(st.depends_on).toContain(pin);
    expect(bindingReadings(c, node)).toEqual([expect.objectContaining({ id: pin })]);
    const v = r.state.verify!;
    expect(v.paper_errors![node]).toMatchObject({ owner_decision: "finding rejected", decision_reason: text, owner_overruled: true });
    expect(v.findings.some((f) => f.node === node && f.kind === "refuted")).toBe(false);
    expect(v.rejected_rewinds).toEqual([expect.objectContaining({ node, by: "owner", pin, route: "applied repair" })]);
    expect(v).toMatchObject({ phase: "v1", core_sha256: null });
    const { pinsOn } = await import("../../src/verify/core_graph.js");
    expect(pinsOn(c, node)).toEqual(rendered ? [expect.objectContaining({ id: pin, by: "owner" })] : []); // the annotated paper renders pins only
  });

  it("a further reading on a node already ruled on withdraws nothing: a repair since placed on it (a consequential one) stands", async () => {
    const { rejectAppliedFindings } = await import("../../src/verify/owner_rulings.js");
    const r = await applied();
    await rejectAppliedFindings(r.runDir, r.state, [{ node: "lem:rate", kind: "reading", text: READING }]);
    expect((await r.patches()).patches).toEqual([]);
    // a later round restates lem:rate to follow another repair
    const later = { ...APPLIED, consequence_of: ["thm:side"], reason: "follows the repair of thm:side" };
    const withLater = { ...(await r.patches()), patches: [later] };
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(withLater), "utf8");
    const line = await rejectAppliedFindings(r.runDir, r.state, [{ node: "lem:rate", kind: "reading", text: "a further reading" }]);
    expect(line).toContain("a further reading of a finding already withdrawn");
    const saved = await r.patches();
    expect(saved.patches.map((p) => p.node)).toEqual(["lem:rate"]);
    expect(saved.owner_readings!.map((o) => [o.id, o.withdraws!.length])).toEqual([["ass:pin-owner-1", 1], ["ass:pin-owner-2", 0]]);
  });

  it("refuses a node with nothing to withdraw, a node twice, and an item of the pending receipt", async () => {
    const { rejectAppliedFindings } = await import("../../src/verify/owner_rulings.js");
    const r = await applied();
    await expect(rejectAppliedFindings(r.runDir, r.state, [{ node: "thm:side", kind: "reading", text: "x" }])).rejects.toThrow(/no finding and no repair.*--add-condition/);
    await expect(rejectAppliedFindings(r.runDir, r.state, [{ node: "lem:rate", kind: "reading", text: "x" }, { node: "lem:rate", kind: "reading", text: "y" }])).rejects.toThrow(/twice/);
    const h = await haltedOnSuggestion();
    await expect(rejectAppliedFindings(h.runDir, h.state, [{ node: "lem:rate", kind: "reading", text: "x" }])).rejects.toThrow(/pending receipt/);
  });

  it("--add-condition adds an owner side condition and withdraws nothing — an applied repair stays (live cns/yang: the withdrawal form removed repairs)", async () => {
    const { addOwnerConditions } = await import("../../src/verify/owner_rulings.js");
    const r = await applied();
    const before = await r.patches();
    expect(before.patches.map((p) => p.node)).toContain("lem:rate"); // lem:rate carries an applied repair
    const line = await addOwnerConditions(r.runDir, r.state, [{ node: "lem:rate", text: "\\(E|Y|<\\infty\\)." }, { node: "thm:side", text: "\\(Y_0=Y_0(0)\\)." }]);
    expect(line).toContain("lem:rate → ass:bk-owner-1, thm:side → ass:bk-owner-2");
    const saved = await r.patches();
    expect(saved.patches.map((p) => p.node)).toEqual(before.patches.map((p) => p.node)); // nothing removed
    expect(saved.owner_readings).toEqual([
      expect.objectContaining({ id: "ass:bk-owner-1", node: "lem:rate", kind: "bookkeeping", withdraws: [] }),
      expect.objectContaining({ id: "ass:bk-owner-2", node: "thm:side", kind: "bookkeeping", withdraws: [] }),
    ]);
    const c = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
    expect(c.statements.find((s) => s.id === "lem:rate")!.depends_on).toContain("ass:bk-owner-1");
    expect(c.statements.find((s) => s.id === "thm:side")!.depends_on).toContain("ass:bk-owner-2");
    expect(r.state.verify!.paper_errors?.["lem:rate"]?.owner_decision).toBeUndefined();
    expect(r.state.verify!.rejected_rewinds ?? []).toEqual([]);
  });

  it("a node already ruled on takes a further reading and withdraws nothing more; deleting a reading revokes its ruling", async () => {
    const { rejectAppliedFindings, syncOwnerRulingsOnDisk } = await import("../../src/verify/owner_rulings.js");
    const r = await applied();
    await rejectAppliedFindings(r.runDir, r.state, [{ node: "lem:rate", kind: "reading", text: READING }]);
    const line = await rejectAppliedFindings(r.runDir, r.state, [{ node: "lem:rate", kind: "reading", text: "the bound holds for every n" }]);
    expect(line).toContain("ass:pin-owner-2 (reading, a further reading of a finding already withdrawn)");
    const saved = await r.patches();
    expect(saved.owner_readings!.map((x) => [x.id, x.withdraws?.length])).toEqual([["ass:pin-owner-1", 1], ["ass:pin-owner-2", 0]]);
    const v = r.state.verify!;
    expect(v.rejected_rewinds).toEqual([expect.objectContaining({ node: "lem:rate", by: "owner", pin: "ass:pin-owner-1" })]);
    expect(v.paper_errors!["lem:rate"]).toMatchObject({ owner_decision: "finding rejected", decision_reason: READING });

    // Revoked in one place: the readings leave patches.json; the next invocation reopens the rest.
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify({ ...saved, owner_readings: [] }), "utf8");
    const lines = await syncOwnerRulingsOnDisk(r.runDir, r.state);
    expect(lines.join("\n")).toContain("ledger: lem:rate reopened");
    expect(v.rejected_rewinds).toBeUndefined();
    expect(v.paper_errors!["lem:rate"]!.owner_decision).toBeUndefined();
    expect(v.findings.some((f) => f.detail.includes("finding withdrawn by the paper's owner"))).toBe(false);
  });

  it("--edit-reading rewords a reading on record (id, node, kind, withdrawals kept); --remove-reading deletes it and sends its node back to the referee as printed", async () => {
    const { addOwnerConditions, parseEditReading, rejectAppliedFindings, reviseOwnerReadings } = await import("../../src/verify/owner_rulings.js");
    const { openErrorIds, readTranscribedCore, validatePatchFile } = await import("../../src/verify/patches.js");
    expect(parseEditReading(" ass:pin-owner-1 : new: text ")).toEqual({ id: "ass:pin-owner-1", text: "new: text" });
    expect(() => parseEditReading("lem:rate: text")).toThrow(/give "<id>: <new text>"/);
    const r = await applied();
    const v = r.state.verify!;
    await rejectAppliedFindings(r.runDir, r.state, [{ node: "lem:rate", kind: "reading", text: READING }]);
    await addOwnerConditions(r.runDir, r.state, [{ node: "thm:side", text: "\\(n \\ge 1\\)" }]);
    const before = await r.patches();
    const accepted = (): void => { v.phase = "formalization"; v.core_sha256 = "accepted"; r.state.stage_completed = "V1.5"; };
    const coreNow = async (): Promise<Core> => JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;

    // refused before anything changes: an id not on file, an id named twice
    accepted();
    await expect(reviseOwnerReadings(r.runDir, r.state, [], ["ass:pin-owner-9"])).rejects.toThrow(/ass:pin-owner-9 is not an owner reading .*on file: ass:pin-owner-1, ass:bk-owner-1/);
    await expect(reviseOwnerReadings(r.runDir, r.state, [{ id: "ass:pin-owner-1", text: "x" }], ["ass:pin-owner-1"])).rejects.toThrow(/named twice/);
    expect(await r.patches()).toEqual(before);
    expect(v.phase).toBe("formalization");

    // an edit: the text only; what derives from the reading follows it; the run re-enters V1.5
    const REWORDED = "the bound holds on the event \\(\\hat p > \\eta\\)";
    const edited = await reviseOwnerReadings(r.runDir, r.state, [{ id: "ass:pin-owner-1", text: REWORDED }], []);
    expect(edited).toContain("--edit-reading: ass:pin-owner-1 reworded");
    expect((await r.patches()).owner_readings).toEqual([{ ...before.owner_readings![0]!, reading: REWORDED }, before.owner_readings![1]]);
    expect(v.paper_errors!["lem:rate"]).toMatchObject({ owner_decision: "finding rejected", decision_reason: REWORDED });
    expect(v.rejected_rewinds).toEqual([expect.objectContaining({ node: "lem:rate", by: "owner", pin: "ass:pin-owner-1", reason: REWORDED })]);
    expect((await coreNow()).assumptions.find((a) => a.id === "ass:pin-owner-1")!.condition).toBe(REWORDED);
    expect([v.phase, v.core_sha256, r.state.stage_completed]).toEqual(["v1", null, "V1"]);

    // a removal: the entry, and every stamp derived from it; the node is the referee's again, as printed
    accepted();
    const removed = await reviseOwnerReadings(r.runDir, r.state, [], ["ass:pin-owner-1"]);
    expect(removed).toContain("--remove-reading: ass:pin-owner-1 removed (the finding on lem:rate is no longer withdrawn");
    const saved = await r.patches();
    expect(saved.owner_readings).toEqual([before.owner_readings![1]]);
    expect(v.paper_errors!["lem:rate"]).toBeUndefined();
    expect(v.rejected_rewinds).toBeUndefined();
    expect(v.findings.some((f) => f.detail.includes("finding withdrawn by the paper's owner"))).toBe(false);
    const c = await coreNow();
    expect(c.assumptions.map((a) => a.id)).toEqual(["ass:overlap", "ass:bk-owner-1"]);
    expect(c.statements.find((s) => s.id === "lem:rate")!.depends_on).toEqual(["ass:overlap"]);
    expect([v.phase, v.core_sha256, r.state.stage_completed]).toEqual(["v1", null, "V1"]);
    // V1.5's entry check passes: no finding is left open without a repair
    expect(validatePatchFile(await readTranscribedCore(r.runDir), saved, openErrorIds(v.paper_errors))).toEqual([]);

    // a patch round still due is not skipped
    v.phase = "init";
    await reviseOwnerReadings(r.runDir, r.state, [], ["ass:bk-owner-1"]);
    expect(v.phase).toBe("init");
    expect((await r.patches()).owner_readings).toEqual([]);
  });

});

describe("the owner redoes a repair (--redo-repair \"<node>: <guidance>\"), mixed with other rulings", () => {
  const GUIDANCE = "keep one-sided overlap: bound the inverse propensity on the trimmed sample instead";
  const SIDE = sug("thm:side", "the variance estimator is consistent when \\(\\hat p\\) is trimmed at \\(\\eta\\)", "consistency without trimming", "trim");
  const TRIMMED = "If \\(\\hat p\\) is trimmed at \\(\\eta\\), the rate is \\(n^{-1/2}\\)";
  const REDONE = {
    node: "lem:rate",
    corrected_statement: null,
    ops: [{ op: "replace" as const, unit: "lem:rate/1/1", tex: TRIMMED }],
    proof_note: "bound $1/\\hat p$ by $1/\\eta$ on the trimmed sample",
  };
  const halt = (state: StateJson, runDir: string) => async () => {
    const f = file({ unfixable: [{ node: "lem:rate", reason: "r", suggested_repair: SUGGESTION }, { node: "thm:side", reason: "r", suggested_repair: SIDE }] });
    await writeFile(path.join(runDir, VERIFY_FILES.patches), JSON.stringify(f), "utf8");
    state.verify!.paper_errors = { "lem:rate": { detail: "1/p̂ is unbounded", witness: WITNESS }, "thm:side": { detail: "the variance blows up", witness: "p̂ → 0" } };
    recordWeakeningReceipt(state, core(), f);
  };

  it("one resume: accept A, redo B → A applied, the fixer's directive carries B's guidance and B's SERVES block, the ledger says redo", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-weak-redo-"));
    tmpDirs.push(repoRoot);
    const runDir = verifyRunDir(repoRoot, QID);
    const calls: CodexRunInput[] = [];
    let v1Calls = 0;
    const v1: VerifyStage = async (stageArgs) => {
      v1Calls += 1;
      if (v1Calls === 1) {
        await setup({ repoRoot, runDir });
        await halt(stageArgs.state, runDir)();
        return { status: "checkpoint", message: "suggestions pending" };
      }
      // the redo: the real V1 patch mode, the fixer faked (it returns the accepted patch unchanged)
      const accepted = { node: "thm:side", corrected_statement: SIDE.corrected_statement, proof_note: SIDE.proof_note };
      return runStageV1({ ...stageArgs, dryRun: false, deps: { runCodex: fakeCodex([file({ patches: [REDONE, accepted] as never })], calls) } });
    };
    let v1_5Calls = 0;
    const v1_5: VerifyStage = async ({ state }) => {
      v1_5Calls += 1;
      // the confirming pass grades the suggestions and, nothing left for the fixer, presents the receipt
      const rec = state.verify!.weakening_repair;
      if (rec?.status === "pending" && rec.unconfirmed) {
        const { unconfirmed: _u, ...presented } = rec;
        state.verify!.weakening_repair = presented;
        return { status: "checkpoint", message: "confirmed; the receipt awaits the owner" };
      }
      state.stage_completed = "V1.5";
      return { status: "completed", message: "ok" };
    };
    const args = {
      toolkit: tk(repoRoot),
      qid: QID,
      input: "/papers/weak_paper.tex",
      mainHint: null,
      targets: null,
      resume: false,
      fromStage: null as string | null,
      auto: true,
      dryRun: true,
      deps: {
        prepareSource: async ({ sourceDir }: { sourceDir: string }) => { await mkdir(sourceDir, { recursive: true }); return { sourceDir, mainFile: "main.tex", sha256: "abc", inputKind: "tex" as const }; },
        annotate: (async ({ runDir: d }: { runDir: string }) => ({ path: path.join(d, "annotated", "main.pdf"), line: "annotated", result: null, error: null })),
      },
      stages: { v1, v1_5, v6: (async () => ({ status: "completed", message: "report" })) as VerifyStage },
      runPromotion: async () => ({ status: "empty" as const, batch_path: null, checklist_path: null, promoted: [] }),
      runFormalization: async ({ toolkit, qid }: { toolkit: { toolkitRoot: string }; qid: string }) => {
        const s = await loadState(toolkit.toolkitRoot, qid);
        s.stage_completed = "5";
        await saveState(toolkit.toolkitRoot, qid, s);
        return s;
      },
    };
    const spy = vi.spyOn(console, "log").mockImplementation(() => {});
    try {
      let verify = await runVerifyPipeline(args as never);
      expect(verify.weakening_repair?.items.map((i) => i.node).sort()).toEqual(["lem:rate", "thm:side"]);
      // presented after the confirming V1.5 pass
      expect(v1_5Calls).toBe(1);
      expect(verify.weakening_repair!.unconfirmed).toBeUndefined();
      await expect(runVerifyPipeline({ ...args, resume: true, redoRepair: ["lem:rate:   "] } as never)).rejects.toThrow(/needs the guidance/);
      await expect(runVerifyPipeline({ ...args, resume: true, acceptRepair: ["prop:aside"] } as never)).rejects.toThrow(/not a pending item/);
      // refused before any answer of the resume is applied: a withdrawal on thm:side beside a redo with no guidance,
      // or beside a second answer on the same result, leaves the receipt and the patch file as they were
      const patchesBefore = await readFile(path.join(runDir, "discovery", "patches.json"), "utf8");
      await expect(runVerifyPipeline({ ...args, resume: true, rejectFinding: ["thm:side: the side result is stated for the fixed design"], redoRepair: ["lem:rate:  "] } as never)).rejects.toThrow(/needs the guidance/);
      await expect(runVerifyPipeline({ ...args, resume: true, rejectFinding: ["thm:side: the side result is stated for the fixed design"], acceptRepair: ["thm:side"] } as never)).rejects.toThrow(/thm:side is named by two answers/);
      await expect(runVerifyPipeline({ ...args, resume: true, rejectFinding: ["the rate is stated up to logs"], acceptRepair: true } as never)).rejects.toThrow(/both answer the whole receipt/);
      // a bare answer with every item named has nothing to cover; an id with no reason is no reason
      await expect(runVerifyPipeline({ ...args, resume: true, acceptRepair: ["thm:side", "lem:rate"], declineRepair: "not worth it" } as never)).rejects.toThrow(/nothing is left for it to cover/);
      await expect(runVerifyPipeline({ ...args, resume: true, declineRepair: "thm:nope:" } as never)).rejects.toThrow(/needs a reason after the node/);
      // all or nothing: each answer is checked first by the function that applies it, which then writes nothing
      const { rejectWeakeningFinding } = await import("../../src/verify/owner_rulings.js");
      const { ruleOnReceipt } = await import("../../src/verify/weakening.js");
      const held = await loadState(repoRoot, QID);
      expect(await rejectWeakeningFinding(runDir, held, "the side result is stated for the fixed design", ["thm:side"], { check: true })).toBe("");
      expect(await ruleOnReceipt(runDir, held, { accept: ["thm:side"], decline: [], redo: [{ node: "lem:rate", guidance: "g" }] }, { check: true })).toEqual([]);
      await expect(rejectWeakeningFinding(runDir, held, "x", ["prop:aside"], { check: true })).rejects.toThrow(/not a pending item/);
      expect(held.verify!.weakening_repair!.decisions ?? {}).toEqual({});
      expect(await readFile(path.join(runDir, "discovery", "patches.json"), "utf8")).toBe(patchesBefore);
      expect((await loadState(repoRoot, QID)).verify!.weakening_repair!.items.map((i) => i.node).sort()).toEqual(["lem:rate", "thm:side"]);
      verify = await runVerifyPipeline({ ...args, resume: true, acceptRepair: ["thm:side"], redoRepair: [`lem:rate: ${GUIDANCE}`] } as never);
      expect(v1Calls).toBe(2);
      expect(calls).toHaveLength(1);
      const prompt = calls[0]!.prompt;
      expect(prompt).toContain("=== OWNER GUIDANCE");
      expect(prompt).toContain(`- lem:rate: ${GUIDANCE}`);
      const serves = prompt.split("=== SERVES")[1]!.split("\n===")[0]!;
      expect(serves).toContain("Key contribution: asymptotic normality of the estimator");
      expect(serves).toContain("lem:rate — SERVES (main results):");
      expect(serves).toContain("  - thm:main: the estimator is asymptotically normal");
      expect(serves).toContain("  - thm:side: the variance estimator is consistent");
      // only the redone node is a finding of this round; the accepted one is not re-litigated
      const block = prompt.split("=== FINDINGS")[1]!;
      const findings = JSON.parse(block.slice(block.indexOf("\n") + 1, block.indexOf("\n\n===")));
      expect(findings.map((f: { id: string }) => f.id)).toEqual(["lem:rate"]);
      expect(findings[0]).not.toHaveProperty("owner_guidance");
      const saved = PatchFileSchema.parse(JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.patches), "utf8")));
      expect(saved.unfixable).toEqual([]);
      expect(saved.patches.find((p) => p.node === "thm:side")).toMatchObject({ accepted_weakening: true, given_up: SIDE.given_up });
      expect(saved.patches.find((p) => p.node === "lem:rate")!.corrected_statement).toBe(TRIMMED);
      expect(verify.paper_errors!["lem:rate"]).toMatchObject({ owner_decision: "redo", guidance: GUIDANCE });
      expect(verify.paper_errors!["lem:rate"]).not.toHaveProperty("suggested_repair");
      expect(verify.paper_errors!["thm:side"]).toMatchObject({ owner_decision: "accepted" });
      expect(verify.weakening_repair).toMatchObject({ status: "ruled", decisions: { "lem:rate": "redo", "thm:side": "accepted" } });
      expect(existsSync(path.join(runDir, VERIFY_FILES.v1ReviseDirective))).toBe(false);
      expect(verify.phase).toBe("done");
    } finally {
      spy.mockRestore();
    }
  });

  it("a redo that again ends in a weakening suggestion halts with the owner's guidance shown; an unnamed item stays pending", async () => {
    const r = await setup();
    await halt(r.state, r.runDir)();
    const { ruleOnReceipt } = await import("../../src/verify/weakening.js");
    const lines = await ruleOnReceipt(r.runDir, r.state, { redo: [{ node: "lem:rate", guidance: GUIDANCE }] });
    expect(lines.join(" ")).toContain("--redo-repair");
    // thm:side was not named: its suggestion stays pending in the patch file, the receipt keeps it undecided
    expect(r.state.verify!.weakening_repair).toMatchObject({ status: "pending", decisions: { "lem:rate": "redo" } });
    const { closeReceipt } = await import("../../src/verify/weakening.js");
    closeReceipt(r.state.verify!);
    expect(r.state.verify!.weakening_repair).toMatchObject({ status: "redo", items: [expect.objectContaining({ node: "lem:rate" })] });
    const directive = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(directive).toMatchObject({ mode: "patch", findings: [{ id: "lem:rate", owner_guidance: GUIDANCE, detail: "1/p̂ is unbounded" }] });
    expect(r.state.verify!.phase).toBe("init");
    // the fixer again finds only a weaker version of lem:rate (and returns thm:side's pending suggestion as it was)
    const again = file({ unfixable: [unfix("lem:rate", SUGGESTION, "the guidance cannot be realised: trimming changes the estimand")] });
    const out = await runStageV1(r.args([again]));
    expect(out.status).toBe("checkpoint");
    const rec = r.state.verify!.weakening_repair!;
    expect(rec.status).toBe("pending");
    const item = rec.items.find((i) => i.node === "lem:rate")!;
    expect(item.guidance).toBe(GUIDANCE);
    expect(rec.items.map((i) => i.node).sort()).toEqual(["lem:rate", "thm:side"]);
    expect(weakeningMessage(rec, "weak_paper")).toContain(`your earlier guidance (--redo-repair): ${GUIDANCE}`);
    expect(weakeningMessage(rec, "weak_paper")).toContain("--redo-repair \"<node>: <guidance>\"");
  });
});

describe("a pending proposal whose text does not compile goes back to the fixer once before the owner decides (user rule 2026-09-25)", () => {
  const SUMMARY = sug("lem:rate", "Under the overlap conditions, the rate is $n^{-1/4}");
  const pend = async (r: Setup, s: typeof SUGGESTION) => {
    const f = file({ unfixable: [unfix("lem:rate", s)] });
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(f), "utf8");
    r.state.verify!.paper_errors = { "lem:rate": { detail: "1/p̂ is unbounded", witness: WITNESS } };
    recordWeakeningReceipt(r.state, core(), f);
  };

  it("sent back with the compiler's line (not an owner ruling); the fixer's RESTATEMENT block; a compliant answer is presented; each proposal text goes back at most once", async () => {
    const { restateAllPatches } = await import("../../src/verify/weakening.js");
    const r = await setup();
    await pend(r, SUMMARY);
    const fails = compileFails("lem:rate", SUMMARY.corrected_statement);
    const lines = await restateAllPatches(r.runDir, r.state, fails);
    expect(lines).toHaveLength(2);
    expect(lines[0]).toMatch(/^render check: 1 repair\(s\) with a text that does not compile — one scoped fixer round answers lem:rate; the pending receipt is withdrawn/u);
    expect(lines[1]).toContain(`render check: the suggested repair of lem:rate: the corrected statement the paper prints for "lem:rate" does not compile: ${COMPILE_ERROR}`);
    expect(r.state.verify!.weakening_repair).toBeNull();
    expect(r.state.verify!.phase).toBe("init");
    expect(r.state.verify!.paper_errors!["lem:rate"]).not.toHaveProperty("owner_decision");
    expect(r.state.verify!.paper_errors!["lem:rate"]).not.toHaveProperty("suggested_repair");
    expect((await r.patches()).unfixable).toEqual([]);
    const directive = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(directive.findings).toEqual([expect.objectContaining({ id: "lem:rate", axis: "correctness", restatement: [expect.stringContaining(`does not compile: ${COMPILE_ERROR}`)] })]);
    expect(directive.findings[0]).not.toHaveProperty("owner_guidance");

    // the fixer answers again (V1 patch mode): the problems in their own block, not in the findings JSON
    const out = await runStageV1(r.args([file({ unfixable: [unfix("lem:rate", SUGGESTION)] })]));
    expect(out.status).toBe("checkpoint");
    const prompt = r.calls[0]!.prompt;
    expect(prompt).toContain("=== RESTATEMENT");
    expect(prompt).toContain(`does not compile: ${COMPILE_ERROR}`);
    const block = prompt.split("=== FINDINGS")[1]!;
    expect(JSON.parse(block.slice(block.indexOf("\n") + 1, block.indexOf("\n\n===")))[0]).not.toHaveProperty("restatement");
    // the compliant suggestion is pending again and is presented as it is
    expect(r.state.verify!.weakening_repair?.status).toBe("pending");
    expect(await restateAllPatches(r.runDir, r.state, new Map())).toEqual([]);

    // the same failing text a second time: presented, not sent back again
    await pend(r, SUMMARY);
    expect(await restateAllPatches(r.runDir, r.state, fails)).toEqual([]);
    expect(r.state.verify!.weakening_repair?.status).toBe("pending");
  });

});

describe("an earlier entry the findings do not name is carried, not demanded again (every patch round)", () => {
  /** prop:aside's repair, already on file (a V1.5 pass confirmed it). */
  const ASIDE = {
    node: "prop:aside",
    corrected_statement: null,
    add_assumptions: [],
    remove_depends_on: [],
    proof_note: "the identity follows by expanding both sides.",
  };
  const FINDINGS_BLOCK = (prompt: string): Array<{ id: string }> => {
    const block = prompt.split("=== FINDINGS")[1]!;
    return JSON.parse(block.slice(block.indexOf("\n") + 1, block.indexOf("\n\n===")));
  };

  it("a V1.5 patch round: a reply without the carried patch keeps it; a reply that revises it is taken", async () => {
    for (const revise of [false, true]) {
      const r = await setup();
      const f = withOwnerExplanations(file({ patches: [ASIDE] }));
      await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(f), "utf8");
      r.state.verify!.paper_errors = { "lem:rate": { detail: "1/p̂ is unbounded", witness: WITNESS }, "prop:aside": { detail: "a sign is dropped", witness: null } };
      await r.directive([finding]);
      const RATE = { node: "lem:rate", corrected_statement: null, ops: [{ op: "replace" as const, unit: "lem:rate/1/1", tex: "If \\(\\hat p > \\eta\\), the rate is \\(n^{-1/2}\\)" }], proof_note: "the second display is bounded using $\\hat p > \\eta$; every other step is unchanged." };
      const REVISED = { ...ASIDE, proof_note: "expanding both sides gives the identity term by term." };
      const out = await runStageV1(r.args([file({ patches: revise ? [RATE, REVISED] : [RATE] })]));
      expect(out.status).toBe("completed");
      expect(r.calls).toHaveLength(1);
      expect(FINDINGS_BLOCK(r.calls[0]!.prompt).map((x) => x.id)).toEqual(["lem:rate"]);
      const saved = await r.patches();
      expect(saved.patches.map((p) => p.node).sort()).toEqual(["lem:rate", "prop:aside"]);
      expect(saved.patches.find((p) => p.node === "prop:aside")!.proof_note).toBe(revise ? REVISED.proof_note : ASIDE.proof_note);
    }
  });
});

describe("a repair text on file that does not compile goes back to the fixer in one scoped round (restateAllPatches)", () => {
  /** A patch whose corrected statement does not compile (the render's routing says so). */
  const POINTING = { node: "lem:rate", corrected_statement: "Under the overlap conditions, the rate is $n^{-1/2}", proof_note: "p" };
  const SIDE = { node: "thm:side", corrected_statement: "the variance estimator is consistent under two-sided overlap", proof_note: "p" };
  const ASIDE = { node: "prop:aside", corrected_statement: null, proof_note: "p" };

  it("demands only the failing node, carries the rest, drops its V1.5 confirmation, and sends each text once", async () => {
    const { restateAllPatches } = await import("../../src/verify/weakening.js");
    const r = await setup();
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(withOwnerExplanations(file({ patches: [POINTING, SIDE, ASIDE] }))), "utf8");
    const v = r.state.verify!;
    v.phase = "v1";
    v.confirmed = { "lem:rate": "b1", "thm:side": "b2", "prop:aside": "b3" };
    v.level_pause = { level: "L1", errors: [], via: "fixer", round: 1, carry: { "lem:rate": "b1", "thm:side": "b2" }, at: "t" };
    const fails = compileFails("lem:rate", POINTING.corrected_statement);
    const lines = await restateAllPatches(r.runDir, r.state, fails);
    expect(lines[0]).toMatch(/^render check: 1 repair\(s\) with a text that does not compile — one scoped fixer round answers lem:rate\./u);
    expect(lines[1]).toContain(`render check: the patch on lem:rate: the corrected statement the paper prints for "lem:rate" does not compile: ${COMPILE_ERROR}`);
    const directive = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(directive.findings).toEqual([expect.objectContaining({ id: "lem:rate", axis: "restatement", detail: "1/p̂ is unbounded", restatement: [expect.stringContaining(`does not compile: ${COMPILE_ERROR}`)] })]);
    expect(v.confirmed).toEqual({ "thm:side": "b2", "prop:aside": "b3" });
    expect(v.level_pause.carry).toEqual({ "thm:side": "b2" });
    expect(v.phase).toBe("init");
    // the patch stays applied until the fixer's answer replaces it; the ledger is untouched
    expect((await r.patches()).patches.map((p) => p.node)).toEqual(["lem:rate", "thm:side", "prop:aside"]);
    expect(v.paper_errors!["lem:rate"]).toEqual({ detail: "1/p̂ is unbounded", witness: WITNESS });
    expect(await restateAllPatches(r.runDir, r.state, fails)).toEqual([]);
    expect(v.restatement_rounds).toHaveLength(1);

    // the fixer's round demands lem:rate alone; a runner narrowing restated keeps its mark
    const lines2: string[] = [];
    const RESTATED = { ...POINTING, corrected_statement: "the rate is \\(n^{-1/2}\\) when overlap is two-sided" };
    const out = await runStageV1({ ...r.args([file({ patches: [RESTATED] })]), log: (m: string) => lines2.push(m) });
    expect(out.status).toBe("completed");
    expect(lines2.join("\n")).toContain("patch round 1: 1 node(s) to repair (lem:rate); 1 restated (lem:rate); 2 earlier entries carried as they stand (thm:side, prop:aside)");
    expect(r.calls[0]!.prompt).toContain("=== RESTATEMENT (the repair on file for these nodes breaks the contract");
    const saved = await r.patches();
    expect(saved.patches.find((p) => p.node === "lem:rate")!.corrected_statement).toBe(RESTATED.corrected_statement);
    expect(saved.patches.find((p) => p.node === "thm:side")).toEqual(expect.objectContaining(SIDE));
  });

});

describe("every new receipt waits for a confirming V1.5 pass before it is presented", () => {
  const PENDING = unfix("lem:rate", SUGGESTION, "the root-n rate needs two-sided overlap, which the paper excludes");
  const ASIDE = { node: "prop:aside", corrected_statement: "a narrower identity", proof_note: "write out the identity" };

  it("a narrowing in the confirming pass leaves the owner's suggestion pending on disk (never saved as accepted)", async () => {
    const { rebuildPatchedCore } = await import("../../src/verify/patches.js");
    const r = await setup();
    r.state.verify!.phase = "v1";
    r.state.verify!.paper_errors = { ...r.state.verify!.paper_errors, "prop:aside": { detail: "the identity is false", witness: "x = 1" } };
    const f = file({ patches: [ASIDE], unfixable: [PENDING] });
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(f), "utf8");
    recordWeakeningReceipt(r.state, core(), f);
    r.state.verify!.weakening_repair = { ...r.state.verify!.weakening_repair!, unconfirmed: true };
    await rebuildPatchedCore(r.runDir, { detectHandEdits: false });
    const weakens = { correctness: "error" as const, weakens_contribution: true, detail: "weakens the contribution: the identity holds only for x > 1", witness: "x = 1 is given up" };
    const result = await runStageV1_5(r.args([await review(r, { "prop:aside": weakens })]));
    expect(result.status).toBe("narrowed");
    const saved = await r.patches();
    expect(saved.unfixable.find((u) => u.node === "lem:rate")?.suggested_repair).toBeTruthy();
    expect(saved.patches.find((p) => p.node === "lem:rate")).toBeUndefined();
    expect(saved.patches.find((p) => p.node === "prop:aside")).toMatchObject({ accepted_weakening: true, narrowed_by: "runner" });
  });

  it("the confirming pass grades the nodes and presents the receipt in place of an acceptance; an unflagged receipt stops after the symbol pass", async () => {
    const { rebuildPatchedCore } = await import("../../src/verify/patches.js");
    for (const unconfirmed of [true, false]) {
      const r = await setup();
      r.state.verify!.phase = "v1";
      r.state.verify!.paper_errors = { ...r.state.verify!.paper_errors, "prop:aside": { detail: "the identity is false", witness: "x = 1" } };
      const f = file({ patches: [ASIDE], unfixable: [PENDING] });
      await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(f), "utf8");
      recordWeakeningReceipt(r.state, core(), f);
      if (unconfirmed) r.state.verify!.weakening_repair = { ...r.state.verify!.weakening_repair!, unconfirmed: true };
      const at = r.state.verify!.weakening_repair!.items;
      await rebuildPatchedCore(r.runDir, { detectHandEdits: false });
      const result = await runStageV1_5(r.args([await review(r)]));
      expect(result.status).toBe("checkpoint");
      // one node-referee pass (its shards and one global call), or none
      expect(r.calls.filter(isRefereeGlobal)).toHaveLength(unconfirmed ? 1 : 0);
      expect(r.calls.length > 0).toBe(unconfirmed);
      expect(r.calls.every(isRefereeCall)).toBe(true);
      expect(r.state.verify!.weakening_repair).toMatchObject({ status: "pending", items: at });
      expect(r.state.verify!.weakening_repair!.unconfirmed).toBeUndefined();
      expect(r.state.stage_completed).not.toBe("V1.5");
      expect(r.state.verify!.core_sha256).toBeNull();
    }
  });

  /** A pipeline whose V1 writes the receipt (plus, `other`, an applied repair of prop:aside) and whose
   * V1.5 is `v1_5` (default: the confirming pass settles — the flag cleared, a checkpoint). */
  async function pipeline(opts: { other: boolean; v1_5?: VerifyStage }) {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-weak-order-"));
    tmpDirs.push(repoRoot);
    const runDir = verifyRunDir(repoRoot, QID);
    const seen: string[] = [];
    const v1: VerifyStage = async ({ state }) => {
      seen.push(`V1@${state.verify!.phase}`);
      const r = await setup({ repoRoot, runDir });
      const f = file({ patches: opts.other ? [ASIDE] : [], unfixable: [PENDING] });
      await writeFile(path.join(runDir, VERIFY_FILES.patches), JSON.stringify(f), "utf8");
      state.verify!.paper_errors = r.state.verify!.paper_errors;
      recordWeakeningReceipt(state, core(), f);
      return { status: "checkpoint", message: "suggestion pending" };
    };
    const settles: VerifyStage = async ({ state }) => {
      const rec = state.verify!.weakening_repair;
      if (rec?.status === "pending" && rec.unconfirmed) {
        const { unconfirmed: _u, ...presented } = rec;
        state.verify!.weakening_repair = presented;
        return { status: "checkpoint", message: "confirmed; the receipt awaits the owner" };
      }
      state.stage_completed = "V1.5";
      return { status: "completed", message: "ok" };
    };
    const inner = opts.v1_5 ?? settles;
    const v1_5: VerifyStage = async (a) => {
      const built = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
      seen.push(`V1.5@${a.state.verify!.phase}${a.state.verify!.weakening_repair?.unconfirmed ? " confirming" : ""}${built.statements.some((s) => s.id === "lem:rate") ? " (lem:rate in core)" : ""}`);
      return inner(a);
    };
    const formal: string[] = [];
    const lines: string[] = [];
    const args = {
      toolkit: tk(repoRoot),
      qid: QID,
      input: "/papers/weak_paper.tex",
      mainHint: null,
      targets: null,
      resume: false,
      fromStage: null as string | null,
      auto: true,
      dryRun: true,
      deps: {
        prepareSource: async ({ sourceDir }: { sourceDir: string }) => { await mkdir(sourceDir, { recursive: true }); return { sourceDir, mainFile: "main.tex", sha256: "abc", inputKind: "tex" as const }; },
        annotate: (async ({ runDir, when }: { runDir: string; when: string }) => ({ path: path.join(runDir, "annotated", "main.pdf"), line: `annotated@${when}`, result: null, error: null })),
      },
      stages: {
        v1,
        v1_5,
        v6: (async () => ({ status: "completed", message: "report" })) as VerifyStage,
        acceptCapV1_5: (async ({ state }) => { state.stage_completed = "V1.5"; return { status: "completed", message: "cap accepted" }; }) as VerifyStage,
      },
      runPromotion: async () => ({ status: "empty" as const, batch_path: null, checklist_path: null, promoted: [] }),
      runFormalization: async ({ toolkit, qid, startStage }: { toolkit: { toolkitRoot: string }; qid: string; startStage?: string }) => {
        formal.push(String(startStage));
        const s = await loadState(toolkit.toolkitRoot, qid);
        s.stage_completed = "5";
        await saveState(toolkit.toolkitRoot, qid, s);
        return s;
      },
    };
    const run = async (over: Record<string, unknown> = {}) => {
      const spy = vi.spyOn(console, "log").mockImplementation((m: unknown) => { lines.push(String(m)); });
      try {
        return await runVerifyPipeline({ ...args, ...over } as never);
      } finally {
        spy.mockRestore();
      }
    };
    return { run, seen, formal, lines, root: repoRoot };
  }

  it("a crash in the confirming pass leaves a receipt no ruling answers; a plain --resume runs the confirmation again and presents it", async () => {
    let crash = true;
    const p = await pipeline({
      other: false,
      v1_5: async ({ state }) => {
        if (crash) throw new Error("the runner was killed");
        const { unconfirmed: _u, ...presented } = state.verify!.weakening_repair!;
        state.verify!.weakening_repair = presented;
        return { status: "checkpoint", message: "confirmed; the receipt awaits the owner" };
      },
    });
    await expect(p.run()).rejects.toThrow("the runner was killed");
    const root = tk(p.root).toolkitRoot;
    expect((await loadState(root, QID)).verify).toMatchObject({ phase: "v1", weakening_repair: { status: "pending", unconfirmed: true } });
    // The page shows what the CLI accepts: nothing to decide, no decision card.
    const { pendingDecisions } = await import("../../src/verify/annotate_run.js");
    expect(pendingDecisions((await loadState(root, QID)).verify!, null)).toMatchObject({ confirming: true });
    await expect(p.run({ resume: true, acceptRepair: true })).rejects.toThrow(/have not been presented yet[\s\S]*plain --resume/);
    crash = false;
    const before = p.seen.length;
    await p.run({ resume: true });
    expect(p.seen.slice(before)).toEqual(["V1.5@v1 confirming"]);
    const after = (await loadState(root, QID)).verify!;
    expect(after.weakening_repair).toMatchObject({ status: "pending" });
    expect(after.weakening_repair!.unconfirmed).toBeUndefined();
    expect(pendingDecisions(after, null)?.confirming).toBeUndefined();
    expect(p.lines.join("\n")).toContain("WEAKENED REPAIR");
  });

  it("a plain --resume with a fixer round due runs the fixer first, even while a receipt waits for its confirming pass", async () => {
    const p = await pipeline({ other: false });
    await p.run();
    const root = tk(p.root).toolkitRoot;
    const s = await loadState(root, QID);
    s.verify!.phase = "init";
    s.stage_completed = "V1";
    s.verify!.weakening_repair = { ...s.verify!.weakening_repair!, unconfirmed: true };
    await saveState(root, QID, s);
    const before = p.seen.length;
    await p.run({ resume: true });
    expect(p.seen.slice(before)).toEqual(["V1@init", "V1.5@v1 confirming"]);
  });

});

describe("the confirming pass grades each receipt suggestion as a patch", () => {
  /** A receipt of lem:rate's suggestion, written by a fixer round and not yet presented. */
  async function unconfirmedReceipt(): Promise<Setup> {
    const r = await setup();
    r.state.verify!.phase = "v1";
    const f = file({ unfixable: [unfix("lem:rate", SUGGESTION, "the root-n rate needs two-sided overlap, which the paper excludes")] });
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(f), "utf8");
    recordWeakeningReceipt(r.state, core(), f);
    r.state.verify!.weakening_repair = { ...r.state.verify!.weakening_repair!, unconfirmed: true };
    await rebuildPatchedCore(r.runDir, { detectHandEdits: false });
    return r;
  }
  const onDiskCore = async (r: Setup): Promise<Core> => JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
  const directiveOf = async (r: Setup) => JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v1ReviseDirective), "utf8")) as { mode: string; findings: Array<{ id: string; axis: string }> };
  /** The receipt is withdrawn: the suggestion leaves the patch file and the receipt, the ledger keeps the error's detail but not its weakening mark. */
  async function expectWithdrawn(r: Setup): Promise<void> {
    const saved = await r.patches();
    expect(saved.unfixable).toEqual([]);
    expect(saved.patches).toEqual([]);
    expect(r.state.verify!.weakening_repair ?? null).toBeNull();
    const e = r.state.verify!.paper_errors!["lem:rate"]!;
    expect(e).toMatchObject({ detail: "1/p̂ is unbounded", witness: WITNESS });
    expect(e).not.toHaveProperty("weakens_contribution");
    expect(e).not.toHaveProperty("suggested_repair");
    // core.json is rebuilt: the node is back as printed, for the fixer's round
    expect((await onDiskCore(r)).statements.find((st) => st.id === "lem:rate")?.statement).toBe("the rate is \\(n^{-1/2}\\)");
  }

  it("a weakening grade on the suggestion it checks is no objection, labelled as awaiting the owner", async () => {
    const r = await unconfirmedReceipt();
    await runStageV1_5(r.args([await review(r, { "lem:rate": { correctness: "error", weakens_contribution: true, detail: "weakens the contribution: the root-n rate becomes n^{-1/4}", witness: "w" } })]));
    const saved = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v15Review), "utf8")) as V15Review;
    expect(saved.nodes.find((n) => n.id === "lem:rate")).toMatchObject({ correctness: "ok", detail: expect.stringMatching(/^\[suggested weakening, awaiting the owner\]/u) });
  });

  it("the referee grades the suggestion `error`: it is withdrawn, and the fixer answers the node again", async () => {
    const r = await unconfirmedReceipt();
    const result = await runStageV1_5(r.args([await review(r, { "lem:rate": { correctness: "error", detail: "the n^{-1/4} rate fails as well", witness: "$\\hat p = n^{-1/2}$" } })]));
    expect(result.status).toBe("patch");
    await expectWithdrawn(r);
    const directive = await directiveOf(r);
    expect(directive.mode).toBe("patch");
    // It carries what the fixer answers again: the paper's error and the statement the referee rejected.
    const onRate = directive.findings.find((f: { id: string }) => f.id === "lem:rate") as unknown as { detail: string };
    expect(onRate.detail).toMatch(/^the n\^\{-1\/4\} rate fails as well\nThe error of the paper this node still answers: 1\/p̂ is unbounded/u);
    // the suggestion as it stood rides on the finding, not in its detail (which can reach the author)
    const back = directive.findings.find((f: { id: string }) => f.id === "lem:rate") as unknown as { withdrawn_repair?: { corrected_statement: string | null } };
    expect(back.withdrawn_repair?.corrected_statement).toBeTruthy();
    expect(onRate.detail).not.toContain("Your suggested (weaker) statement");
    expect(r.state.verify!.suggestion_rejections).toEqual({ "lem:rate": 1 });
  });

  it("a suggestion rejected past its limit halts at a cap; clearing it gives the fixer the node again", async () => {
    const { clearCap } = await import("../../src/verify/caps.js");
    const r = await unconfirmedReceipt();
    r.state.verify!.suggestion_rejections = { "lem:rate": MAX_SUGGESTION_REJECTIONS };
    const result = await runStageV1_5(r.args([await review(r, { "lem:rate": { correctness: "error", detail: "the n^{-1/4} rate fails as well", witness: "$\\hat p = n^{-1/2}$" } })]));
    expect(result.status).toBe("checkpoint");
    const cap = r.state.verify!.cap_reached!;
    expect(cap).toMatchObject({ suggestions: ["lem:rate"], suggestions_only: true });
    expect((await directiveOf(r)).findings.map((f) => f.id)).toContain("lem:rate");
    clearCap(r.state.verify!, cap);
    expect(r.state.verify!.suggestion_rejections).toEqual({});
  });

});

describe("a revision of an accepted weakening", () => {
  it("a runner narrowing takes what it gives up from the fixer's current note; an owner-accepted one keeps the owner's text", async () => {
    const { pinOwnerEntries } = await import("../../src/verify/weakening.js");
    const entry = (over: Record<string, unknown>) => ({ node: "lem:rate", corrected_statement: "the rate is \\(n^{-1/4}\\)", proof_note: "p", ...over });
    const prior = (narrowed: boolean) =>
      PatchFileSchema.parse({ key_results: ["thm:main"], key_contribution: "c", patches: [entry({ accepted_weakening: true, given_up: "the root-n rate", ...(narrowed ? { narrowed_by: "runner" } : {}) })], unfixable: [] });
    const reply = PatchFileSchema.parse({
      key_results: ["thm:main"],
      key_contribution: "c",
      patches: [entry({ owner_explanation: { ...cannedExplanation("lem:rate"), gives_up: "the root-n rate; and kernels without compact support" } })],
      unfixable: [],
    });
    expect(pinOwnerEntries(reply, prior(true)).patches[0]).toMatchObject({ accepted_weakening: true, narrowed_by: "runner", given_up: "the root-n rate; and kernels without compact support" });
    expect(pinOwnerEntries(reply, prior(false)).patches[0]).toMatchObject({ accepted_weakening: true, given_up: "the root-n rate" });
  });

  it("the owner accepted the REPAIR, not its statement text: a reply with the same text but other ops, hypotheses or readings goes to the owner again", async () => {
    const { pinOwnerEntries } = await import("../../src/verify/weakening.js");
    const accepted = { node: "lem:rate", corrected_statement: "the rate is \\(n^{-1/4}\\)", ops: [{ op: "replace" as const, unit: "lem:rate/1/1", tex: "the rate is \\(n^{-1/4}\\)" }], proof_note: "p", accepted_weakening: true, given_up: "the root-n rate" };
    const prior = PatchFileSchema.parse({ key_results: ["thm:main"], key_contribution: "c", patches: [accepted], unfixable: [] });
    const reply = (over: Record<string, unknown>) => PatchFileSchema.parse({ key_results: ["thm:main"], key_contribution: "c", patches: [{ node: "lem:rate", corrected_statement: accepted.corrected_statement, ops: accepted.ops, proof_note: "a reworded note", ...over }], unfixable: [] });
    expect(pinOwnerEntries(reply({}), prior).patches[0]).toMatchObject({ accepted_weakening: true, given_up: "the root-n rate" });
    for (const changed of [{ ops: [{ op: "replace", unit: "lem:rate/1/2", tex: accepted.corrected_statement }] }, { adds: ["ass:overlap"] }, { readings: ["the rate is pointwise"] }]) {
      expect(pinOwnerEntries(reply(changed), prior).patches[0]).not.toHaveProperty("accepted_weakening");
    }
  });
});

describe("the repair travels whole between a patch and a suggestion", () => {
  const body = { corrected_statement: "the rate is \\(n^{-1/4}\\)", ops: [{ op: "replace" as const, unit: "lem:rate/1/1", tex: "the rate is \\(n^{-1/4}\\)" }], adds: ["ass:overlap"], readings: ["the rate is pointwise"], proof_note: "p" };

  it("a referee's weakening grade moves the patch's readings (and every other repair field) into the suggestion, and --accept-repair brings them back", async () => {
    const { convertWeakeningPatches, withdrawnRepair } = await import("../../src/verify/weakening.js");
    const { applySuggestions } = await import("../../src/verify/patches.js");
    const f = file({ patches: [{ node: "lem:rate", ...body }] });
    const converted = convertWeakeningPatches(f, [{ id: "lem:rate", detail: "weakens the contribution: the root-n rate" }]);
    expect(converted.unfixable[0]!.suggested_repair).toEqual({ ...body, given_up: "the root-n rate", given_up_by: "referee" });
    expect(withdrawnRepair(converted, "lem:rate")).toEqual({ corrected_statement: body.corrected_statement, ops: body.ops, adds: body.adds, readings: body.readings });
    expect(applySuggestions(converted, new Set(["lem:rate"])).patches[0]).toMatchObject({ node: "lem:rate", ...body, accepted_weakening: true });
  });

  it("the receipt says what is wrong with the PRINTED statement — the ledger's error, else the repairs a consequential patch followed, else nothing — never the referee's grade of the repair", async () => {
    const { convertWeakeningPatches } = await import("../../src/verify/weakening.js");
    const grade = [{ id: "lem:rate", detail: "weakens the contribution: the root-n rate" }];
    const fresh = () => createVerifyInitialState(QID, { phase: "v1", source: { input: "p.tex", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
    const item = (state: ReturnType<typeof fresh>, f: PatchFile) => recordWeakeningReceipt(state, core(), f)!.items[0]!;
    // restated only to follow a corrected lemma: no finding names it, and the suggestion keeps what it followed
    const follows = convertWeakeningPatches(file({ patches: [{ node: "lem:rate", ...body, consequence_of: ["lem:ipw-identity"], reason: "The proof now uses the corrected identity." }] }), grade);
    expect(PatchFileSchema.parse(follows).unfixable[0]).toMatchObject({ reason: "any repair weakens the contribution: the root-n rate", consequence_of: ["lem:ipw-identity"] });
    // what it followed is the card's: no referee is shown it
    const { patchesShown } = await import("../../src/verify/stage_v1_5.js");
    expect(JSON.stringify(patchesShown({ patches: follows } as never))).not.toMatch(/consequence_/);
    const state = fresh();
    for (let pass = 0; pass < 2; pass++) {
      // (written again, the ledger entry the first receipt made holds the grade)
      const it = item(state, follows);
      expect(it.given_up).toBe("the root-n rate");
      expect(it.detail).toContain("lem:ipw-identity");
      expect(it.detail).toContain("The proof now uses the corrected identity.");
      expect(it.detail).not.toContain("the root-n rate");
    }
    // an error of its own: the ledger's finding and witness
    const own = fresh();
    own.verify!.paper_errors = { "lem:rate": { detail: "the bound fails at n = 1", witness: "take n = 1" } };
    const plain = convertWeakeningPatches(file({ patches: [{ node: "lem:rate", ...body }] }), grade);
    expect(item(own, plain)).toMatchObject({ detail: "the bound fails at n = 1", witness: "take n = 1" });
    // no finding on record (the ledger holds a weakening grade only): nothing, not the grade again
    const none = fresh();
    none.verify!.paper_errors = { "lem:rate": { detail: "weakens the contribution: the root-n rate", witness: "w" } };
    expect(item(none, plain)).toMatchObject({ detail: "", witness: null });
    expect(item(fresh(), plain).detail).toBe("");
  });

  it("a receipt written again keeps the owner's rulings on the items still listed; a suggestion with nothing given up prints no 'gives up'", async () => {
    const { suggestionText } = await import("../../src/verify/patches.js");
    const state = createVerifyInitialState(QID, { phase: "v1", source: { input: "p.tex", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
    const f = file({ unfixable: [unfix("lem:rate", SUGGESTION), unfix("thm:side", sug("thm:side", "a weaker claim"))] });
    recordWeakeningReceipt(state, core(), f);
    state.verify!.weakening_repair!.decisions = { "lem:rate": "accepted" };
    recordWeakeningReceipt(state, core(), f);
    expect(state.verify!.weakening_repair).toMatchObject({ status: "pending", decisions: { "lem:rate": "accepted" } });
    recordWeakeningReceipt(state, core(), file({ unfixable: [unfix("thm:side", sug("thm:side", "a weaker claim"))] }));
    expect(state.verify!.weakening_repair).not.toHaveProperty("decisions");
    expect(suggestionText({ corrected_statement: "S", proof_note: "p" })).toBe("corrected statement: S");
  });
});

describe("core.json hand edits (live Athey–Imbens, 2026-09-30)", () => {
  it("a changed patch file is not a hand edit of core.json; a change to core.json since the runner wrote it is", async () => {
    const r = await setup();
    const corePath = path.join(r.runDir, VERIFY_FILES.coreJson);
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(file()), "utf8");
    await rebuildPatchedCore(r.runDir, { detectHandEdits: false }); // the runner's first write
    // The owner extends a reading in patches.json: the rebuild differs, and nobody touched core.json.
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(file({ owner_readings: [{ id: "ass:pin-owner-1", node: "lem:rate", reading: "the rate holds on the event considered" }] })), "utf8");
    expect((await rebuildPatchedCore(r.runDir)).handEdited).toBe(false);
    expect(existsSync(`${corePath}.prev`)).toBe(false);
    // Someone edits core.json itself.
    const c = JSON.parse(await readFile(corePath, "utf8")) as Core;
    c.statements[0]!.statement = `${c.statements[0]!.statement} (edited)`;
    await writeFile(corePath, JSON.stringify(c, null, 2), "utf8");
    expect((await rebuildPatchedCore(r.runDir)).handEdited).toBe(true);
    expect(existsSync(`${corePath}.prev`)).toBe(true);
  });

  it("a core that differs from its rebuild with no record of the runner's write is not called a hand edit (a run from before the record)", async () => {
    const r = await setup();
    const corePath = path.join(r.runDir, VERIFY_FILES.coreJson);
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(file()), "utf8");
    await rebuildPatchedCore(r.runDir, { detectHandEdits: false });
    const c = JSON.parse(await readFile(corePath, "utf8")) as Core;
    c.statements[0]!.statement = `${c.statements[0]!.statement} (as an earlier version built it)`;
    await writeFile(corePath, JSON.stringify(c, null, 2), "utf8");
    await rm(`${corePath}.written.sha256`);
    expect((await rebuildPatchedCore(r.runDir)).handEdited).toBe("unknown");
    expect(existsSync(`${corePath}.prev`)).toBe(true);
  });
});

describe("the owner's words are kept as plain-ASCII TeX", () => {
  it("dashes, quotes, an ellipsis and common signs a keyboard or a page produces take their TeX spelling", () => {
    expect(ownerWordsTex("the local rates \u2014 fold \u201Cboth\u201D in\u2026 for h \u2264 1")).toBe("the local rates --- fold ``both'' in\\ldots{} for h $\\leq$ 1");
    expect(ownerWordsTex("plain $x \\leq 1$")).toBe("plain $x \\leq 1$");
  });
});

describe("a statement the paper leaves undetermined is never recorded as refuted", () => {
  const unfixable = file({ unfixable: [{ node: "lem:rate", reason: "any repair weakens the contribution: every reading states less", suggested_repair: null, owner_explanation: cannedExplanation("lem:rate") }] });

  it("an unresolvable ambiguity the fixer cannot repair is `unresolved` and `undetermined`; an error with a witness stays `refuted`", async () => {
    const r = await setup();
    r.state.verify!.paper_errors = {};
    await r.directive([{ id: "lem:rate", axis: "ambiguity", detail: "the paper names neither the estimator nor the mode of convergence", witness: null }]);
    expect((await runStageV1(r.args([unfixable]))).status).toBe("failed");
    expect(r.state.verify!.paper_errors!["lem:rate"]).toMatchObject({ undetermined: true, witness: null });
    expect(r.state.verify!.findings.filter((f) => f.node === "lem:rate").map((f) => [f.kind, f.undetermined ?? false])).toEqual([["unresolved", true]]);

    const wrong = await setup();
    await wrong.directive([finding]);
    expect((await runStageV1(wrong.args([unfixable]))).status).toBe("failed");
    expect(wrong.state.verify!.paper_errors!["lem:rate"]!.undetermined).toBeUndefined();
    expect(wrong.state.verify!.findings.filter((f) => f.node === "lem:rate").map((f) => [f.kind, f.undetermined ?? false])).toEqual([["refuted", false]]);
  });

  it("a witnessed error found later on the node replaces the ambiguity on record", async () => {
    const r = await setup();
    r.state.verify!.paper_errors = { "lem:rate": { detail: "the rate is not specified", witness: null, undetermined: true } };
    await r.directive([finding]);
    await runStageV1(r.args([unfixable]));
    expect(r.state.verify!.paper_errors!["lem:rate"]).toMatchObject({ detail: finding.detail, witness: WITNESS });
    expect(r.state.verify!.paper_errors!["lem:rate"]!.undetermined).toBeUndefined();
  });
});

describe("a repair of a statement the paper leaves undetermined", () => {
  const amb = { id: "lem:rate", axis: "ambiguity", detail: "the mode of convergence is not named", witness: null };
  const PRECISE = { node: "lem:rate", corrected_statement: null, ops: [{ op: "replace" as const, unit: "lem:rate/1/1", tex: "the rate is \\(n^{-1/2}\\) in probability" }], proof_note: "names the mode", owner_explanation: cannedExplanation("lem:rate") };
  async function repaired(): Promise<Setup> {
    const r = await setup();
    r.state.verify!.paper_errors = {};
    await r.directive([amb]);
    await runStageV1(r.args([file({ patches: [PRECISE as never] })]));
    expect(r.state.verify!.paper_errors!["lem:rate"]).toMatchObject({ undetermined: true });
    return r;
  }
  /** `--accept-cap` at the error cap, on the referee's last review. */
  async function acceptedAtCap(r: Setup, over: Record<string, Partial<V15NodeVerdict>>) {
    await writeFile(path.join(r.runDir, VERIFY_FILES.v15Review), JSON.stringify({ ...(await review(r, over)), verdict: "FAIL" }), "utf8");
    r.state.verify!.cap_reached = { counter: "patch_rounds", rounds: 3, cap: 3 } as never;
    return acceptV1_5AtCap(r.args([]) as never);
  }
  const on = (r: Setup, node: string) => r.state.verify!.findings.filter((f) => f.node === node && !f.detail.startsWith("cited source"));

  it("confirmed, it is made precise — a note with the adopted text, never a refutation", async () => {
    const r = await repaired();
    expect((await runStageV1_5(r.args([await review(r)]))).status).toBe("completed");
    expect(on(r, "lem:rate")).toEqual([expect.objectContaining({ kind: "note", undetermined: true, witness: null, detail: expect.stringContaining("made precise — "), patch: expect.objectContaining({ confirmed: true }) })]);
  });

  it("refuted by the referee, the statement stays undetermined: the witness is against the repair tried, and nothing is counted refuted", async () => {
    const r = await repaired();
    const out = await acceptedAtCap(r, { "lem:rate": { correctness: "error", detail: "under the reading the repair states the rate fails", witness: WITNESS } });
    expect(out.message).toContain("FAIL: 0 refuted result(s); 1 refuted repair(s) of a statement the paper leaves undetermined — lem:rate");
    expect(on(r, "lem:rate").map((f) => [f.kind, f.undetermined ?? false, f.witness, f.patch?.confirmed ?? null])).toEqual([
      ["unresolved", true, null, false],
      ["unresolved", true, WITNESS, null],
    ]);
  });

  it("a result with no error on record that the fixer sets aside is unresolved, not refuted and not undetermined", async () => {
    const r = await setup();
    r.state.verify!.paper_errors = {};
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(file({ unfixable: [{ node: "prop:aside", reason: "the proof cannot be written out", suggested_repair: null, owner_explanation: cannedExplanation("prop:aside") }] })), "utf8");
    await acceptedAtCap(r, {});
    expect(on(r, "prop:aside").filter((f) => f.descoped).map((f) => [f.kind, f.undetermined ?? false])).toEqual([["unresolved", false]]);
  });

  it("the ledger keeps what was ruled on the entry a witnessed error replaces, except a withdrawal of the ambiguity", async () => {
    const unfixable = file({ unfixable: [{ node: "lem:rate", reason: "any repair weakens the contribution: r", suggested_repair: null, owner_explanation: cannedExplanation("lem:rate") }] });
    const r = await setup();
    r.state.verify!.paper_errors = { "lem:rate": { detail: "vague", witness: null, undetermined: true, weakens_contribution: true, suggested_repair: "s", owner_decision: "declined", decision_reason: "no" } };
    await r.directive([finding]);
    await runStageV1(r.args([unfixable]));
    expect(r.state.verify!.paper_errors!["lem:rate"]).toEqual({ detail: finding.detail, witness: WITNESS, weakens_contribution: true, suggested_repair: "s", owner_decision: "declined", decision_reason: "no" });
    const w = await setup();
    w.state.verify!.paper_errors = { "lem:rate": { detail: "vague", witness: null, undetermined: true, owner_decision: "finding rejected", decision_reason: "read it so", owner_overruled: true } };
    await w.directive([finding]);
    await runStageV1(w.args([unfixable]));
    expect(w.state.verify!.paper_errors!["lem:rate"]).toEqual({ detail: finding.detail, witness: WITNESS });
  });

  it("the halt for a weakened repair names what declining reports: not determined, never refuted", () => {
    const rec = { status: "pending", items: [{ node: "lem:rate", printed: "p", proposed: "q", given_up: "g", detail: "vague", witness: null, source: "fixer" }] } as never;
    expect(weakeningMessage(rec, QID, { "lem:rate": { detail: "vague", witness: null, undetermined: true } })).toContain("(report them not determined; they and what rests on them leave Lean");
    expect(weakeningMessage(rec, QID, { "lem:rate": { detail: "false", witness: "w" } })).toContain("(report them refuted; they and what rests on them leave Lean");
  });
});

describe("--reject-finding on an ambiguity pins a reading and shields the node from nothing", () => {
  const READING = "the rate is in probability";
  const PATCH = { node: "lem:rate", corrected_statement: "the rate is \\(n^{-1/2}\\) in probability", ops: [{ op: "replace" as const, unit: "lem:rate/1/1", tex: "the rate is \\(n^{-1/2}\\) in probability" }], proof_note: "names the mode" };
  const error = grade("lem:rate", { correctness: "error", detail: "the rate fails", witness: WITNESS });
  async function withdrawn(entry: { detail: string; witness: string | null; undetermined?: boolean }): Promise<Setup> {
    const { rejectAppliedFindings } = await import("../../src/verify/owner_rulings.js");
    const r = await setup();
    r.state.verify!.paper_errors = { "lem:rate": entry };
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(withOwnerExplanations(file({ patches: [PATCH as never] }))), "utf8");
    await rejectAppliedFindings(r.runDir, r.state, [{ node: "lem:rate", kind: "reading", text: READING }]);
    return r;
  }

  it("a later witnessed error on the node still goes to the fixer, and is not stamped withdrawn", async () => {
    const { governByOwnerRulings, syncOwnerRulingsOnDisk } = await import("../../src/verify/owner_rulings.js");
    const r = await withdrawn({ detail: "the mode of convergence is not named", witness: null, undetermined: true });
    expect((await r.patches()).owner_readings![0]!.withdraws).toEqual([expect.objectContaining({ axis: "ambiguity" })]);
    expect(r.state.verify!.rejected_rewinds).toEqual([expect.objectContaining({ node: "lem:rate", by: "owner", axis: "ambiguity" })]);
    const governed = governByOwnerRulings(r.state, [error]);
    expect(governed.overruled).toEqual([]);
    expect(governed.nodes[0]).toMatchObject({ correctness: "error", witness: WITNESS });
    r.state.verify!.paper_errors = { "lem:rate": { detail: "the rate fails", witness: WITNESS } };
    await syncOwnerRulingsOnDisk(r.runDir, r.state);
    expect(r.state.verify!.paper_errors!["lem:rate"]).toEqual({ detail: "the rate fails", witness: WITNESS });
  });

  it("a withdrawn error still overrules a repeat of itself", async () => {
    const { governByOwnerRulings } = await import("../../src/verify/owner_rulings.js");
    const r = await withdrawn({ detail: "1/p̂ is unbounded", witness: WITNESS });
    expect(r.state.verify!.rejected_rewinds).toEqual([expect.objectContaining({ axis: "correctness" })]);
    expect(governByOwnerRulings(r.state, [error]).overruled).toEqual(["lem:rate"]);
  });
});
