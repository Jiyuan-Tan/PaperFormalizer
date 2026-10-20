import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { directiveFindings, renderRuledOut, resolveTarget, rewindTarget, ruledOutScope } from "../../src/verify/cross_stage_rewind.js";

const core = {
  qid: "q",
  symbols: [],
  assumptions: [{ id: "ass:finite-kurtosis", condition: "c" }],
  definitions: [],
  statements: [
    { id: "thm:var-kurt", kind: "theorem", statement: "s", depends_on: [], status: "to-prove" },
    { id: "lem:aux", kind: "lemma", statement: "s", depends_on: [], status: "to-prove" },
    { id: "oeq:open-rate", kind: "openendedquestion", statement: "s", depends_on: [], status: "to-prove" },
  ],
  target_estimand: "t",
  bibliography: [],
} as unknown as Core;

describe("rewindTarget", () => {
  it.each([
    ["reads a `thm::x` typo as `thm:x`", "A-6 / thm::var-kurt (T-block t3) assume only finite kurtosis; lem:aux is fine", undefined, "thm:var-kurt"],
    ["never names an assumption", "ass:finite-kurtosis is too weak", undefined, null],
    ["finds a statement of any kind the schema admits (oeq:), never a name that is no statement of the core", "def:rate is unclear; oeq:open-rate is posed wrongly", undefined, "oeq:open-rate"],
    ["falls back to a statement's graph alias", "T-3 needs kappa > 1", new Map([["T-3", "thm:var-kurt"], ["A-6", "ass:finite-kurtosis"]]), "thm:var-kurt"],
  ] as const)("names the first statement of the core the finding mentions: %s", (_why, text, aliases, want) => {
    expect(rewindTarget(core, text, aliases as Map<string, string> | undefined)).toBe(want);
  });
});

// ---------------------------------------------------------------------------------------------
// F2.5–F4 proof-review routes (a defect in a PAPER statement)
// ---------------------------------------------------------------------------------------------

import { mkdtemp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterEach } from "vitest";
import { createInitialState } from "../../src/state.js";
import {
  applyPendingRewind,
  hypothesisRepairLine,
  presentPendingRewind,
  rejectPendingRewind,
  rejectedMatch,
  recordProofReviewRewind,
  sameFinding,
} from "../../src/verify/cross_stage_rewind.js";
import { MIN_PATCH_BACKSTOP, MAX_REFINEMENT_ROUNDS, VERIFY_FILES } from "../../src/verify/types.js";
import type { StateJson } from "../../src/types.js";

const PR_CORE = {
  qid: "q",
  symbols: [],
  assumptions: [
    { id: "ass:twoforms-invertible-cdfs", kind: "regularity", condition: "F_A and F_B are invertible.", novel: { flag: true, justification: "stated in the lemma" } },
    {
      id: "ass:pin-7",
      kind: "regularity",
      condition: "F_A^{-1}(p)-F_B^{-1}(p)=\\tau for 0<p<1, endpoints by one-sided limits.",
      bookkeeping: { flag: true, added_by: "V1.5", reason: "pins reading of lem:twoforms: the proof couples through U in (0,1)." },
    },
  ],
  definitions: [],
  statements: [
    { id: "lem:twoforms", kind: "lemma", statement: "Take A, B with invertible CDFs. Then the two forms are equivalent.", depends_on: ["ass:twoforms-invertible-cdfs", "ass:pin-7"], status: "to-prove" },
    { id: "thm:main", kind: "theorem", statement: "The test is valid.", depends_on: ["ass:twoforms-invertible-cdfs"], status: "to-prove" },
  ],
  target_estimand: "t",
  bibliography: [],
};
const LIVE_REASON =
  "[statement-wrong] Specify whether each CDF is invertible on all of ℝ or only where its value lies in (0,1), and define its endpoint inverse values; the frozen wording permits both readings.";

const prDirs: string[] = [];
afterEach(async () => {
  for (const d of prDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

async function prRun(): Promise<{ runDir: string; state: StateJson }> {
  const runDir = await mkdtemp(path.join(os.tmpdir(), "rewind-pr-"));
  prDirs.push(runDir);
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  await writeFile(path.join(runDir, VERIFY_FILES.coreJson), JSON.stringify(PR_CORE), "utf8");
  const state = createInitialState("q");
  state.stage_completed = "2";
  state.verify!.phase = "formalization";
  return { runDir, state };
}

/** What `recordProofReviewOutcome` leaves behind on an escalation. */
function escalate(state: StateJson, flag: NonNullable<StateJson["flags"]["proof_review_escalation_pending"]>): void {
  state.flags.proof_review_escalation_pending = flag;
  state.verify!.findings.push({ node: flag.obj_id ?? "run", stage: `F${flag.phase ?? "2.5"}`, kind: "unresolved", detail: flag.reason, witness: null, at: "t" });
}

describe("proof-review routes into V1 patch mode", () => {
  it("a fix-source [statement-wrong] escalation becomes a clarify directive on the named statement, folding its pinned reading", async () => {
    const { runDir, state } = await prRun();
    escalate(state, { route: "fix-source", reason: LIVE_REASON, kind: "statement-wrong", obj_id: "lem:twoforms", phase: "2.5" });
    expect(recordProofReviewRewind(state)).toBe(true);
    expect(recordProofReviewRewind(state)).toBe(false); // one receipt per escalation
    const out = await applyPendingRewind({ runDir, state });
    expect(out).toMatchObject({ applied: true, node: "lem:twoforms", round: 1 });
    const d = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(d).toMatchObject({ mode: "patch", round: 1 });
    expect(d.findings).toHaveLength(1);
    expect(d.findings[0]).toMatchObject({
      id: "lem:twoforms",
      axis: "clarify",
      witness: null,
      from_stage: "F2.5",
      folds: [{ node: "lem:twoforms", reading: PR_CORE.assumptions[1]!.condition }],
    });
    expect(d.findings[0].detail).toMatch(/^\[F2\.5 reviewer\] \[statement-wrong\] Specify/);
    expect(d.findings[0].detail).toContain("to be written into it");
    // the receipt records the stage and route; the escalation flag is cleared; the cursor is V1
    expect(state.verify!.cross_stage_rewind).toMatchObject({ status: "applied", stage: "F2.5", route: "fix-source", axis: "clarify", nodes: ["lem:twoforms"], round: 1 });
    expect(state.flags.proof_review_escalation_pending).toBeNull();
    // a clarification spends a REFINEMENT round, never an error round
    expect(state.verify!.refinement_rounds).toBe(1);
    expect(state.verify!.patch_rounds ?? 0).toBe(0);
    expect(state.stage_completed).toBe("V1");
    expect(state.verify!.phase).toBe("init");
    expect(state.verify!.findings[0]).toMatchObject({ kind: "note", detail: expect.stringContaining("routed to V1 patch mode on lem:twoforms") });
  });
  it("a wrong claim goes as `correctness` with the finding as its witness", async () => {
    const { runDir, state } = await prRun();
    escalate(state, { route: "fix-source", reason: "[statement-wrong] the test is not valid without a finite fourth moment", kind: "statement-wrong", obj_id: "thm:main", phase: "4" });
    recordProofReviewRewind(state);
    await applyPendingRewind({ runDir, state });
    const d = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(d.findings[0]).toMatchObject({ id: "thm:main", axis: "correctness", from_stage: "F4" });
    expect(d.findings[0].witness).toContain("finite fourth moment");
    expect(d.findings[0].folds).toBeUndefined();
  });

  it("a claim the reviewer refutes with a witness (fix-source [claim-false]) is a paper-statement finding too: presented, `correctness` (live Ding thm:binary)", async () => {
    const { runDir, state } = await prRun();
    escalate(state, { route: "fix-source", reason: "[claim-false] balanced binary populations with one success satisfy the hypotheses but violate the normal limit", kind: "claim-false", obj_id: "thm:main", phase: "2.5" });
    expect(recordProofReviewRewind(state)).toBe(true);
    await applyPendingRewind({ runDir, state });
    const d = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(d.findings[0]).toMatchObject({ id: "thm:main", axis: "correctness", from_stage: "F2.5" });
  });

  it("a ruling is shown to the reviewer on the node it concerns and on the results using it (live Ding: the same point re-raised in other words)", () => {
    const rejected = [{ node: "ass:regime", axis: "clarify" as const, stage: "F2.5", route: "fix-source", detail: "Specify whether increasing sizes requires monotonicity", reason: "only $N\\to\\infty$ is used", by: "orchestrator" as const, at: "t" }];
    expect(renderRuledOut(rejected, ["thm:main", "ass:regime"])).toContain("ass:regime: Specify whether increasing sizes requires monotonicity — RULING (orchestrator): only $N\\to\\infty$ is used");
    expect(renderRuledOut(rejected, ["thm:other"])).toBe("");
    expect(renderRuledOut(undefined, ["ass:regime"])).toBe("");
  });

  it("a pinned reading's reviewer sees the ruling made on the result carrying it (live drdid: the pin's reviewer re-raised a ruled question three times)", () => {
    const statements = [
      { id: "thm:bound", depends_on: ["ass:sampling", "ass:pin-2"] },
      { id: "thm:other", depends_on: ["ass:sampling"] },
    ];
    expect(ruledOutScope(statements, "ass:pin-2")).toEqual(["ass:pin-2", "thm:bound"]);
    expect(ruledOutScope(statements, "thm:bound")).toEqual(["thm:bound", "ass:sampling", "ass:pin-2"]);
    const rejected = [{ node: "thm:bound", axis: "clarify", stage: "F2.5", route: "fix-source", detail: "pointwise or a.s. on the support?", reason: "a.s. under the law of X given D=d", by: "orchestrator", at: "t" }] as never;
    expect(renderRuledOut(rejected, ruledOutScope(statements, "ass:pin-2"))).toContain("RULING (orchestrator): a.s. under the law of X given D=d");
  });

  it("a Lean-internal finding keeps halting: a Lean declaration is not a statement the fixer can restate", async () => {
    const { runDir, state } = await prRun();
    const flag = { route: "fix-source", reason: "[statement-wrong] aux_quantile_inv admits two readings (lem:twoforms uses it)", kind: "statement-wrong", obj_id: "aux_quantile_inv", phase: "2.5" };
    escalate(state, flag);
    recordProofReviewRewind(state);
    const out = await applyPendingRewind({ runDir, state });
    expect(out.applied).toBe(false);
    expect(state.verify!.cross_stage_rewind).toMatchObject({ status: "refused", why: expect.stringContaining("aux_quantile_inv") });
    expect(state.flags.proof_review_escalation_pending).toEqual(flag);
    expect(state.stage_completed).toBe("2");
    expect(state.verify!.patch_rounds ?? 0).toBe(0);
    expect(existsSync(path.join(runDir, VERIFY_FILES.v1ReviseDirective))).toBe(false);
    expect(state.verify!.findings[0]!.kind).toBe("unresolved");
    // a refused receipt is never re-derived from the same escalation
    expect(recordProofReviewRewind(state)).toBe(false);
  });

  it("a workflow route (redo-math, per-node strikes, a substrate gap) records no receipt", () => {
    const state = createInitialState("q");
    for (const flag of [
      { route: "redo-math", reason: "[claim-false] aux_x is refuted", kind: "claim-false", obj_id: "aux_x" },
      { route: "fix-source", reason: "[per-node-strikes] 'lem:twoforms' flagged in 3 scaffold-reroute rounds" },
      { route: "build-substrate", reason: "[needs-substrate] Glivenko–Cantelli", kind: "needs-substrate" },
    ]) {
      state.flags.proof_review_escalation_pending = flag;
      expect(recordProofReviewRewind(state)).toBe(false);
    }
    expect(state.verify!.cross_stage_rewind).toBeUndefined();
  });

  it("counts one round of its kind; at the cap it halts with a cap_reached receipt and the escalation stays pending", async () => {
    const { runDir, state } = await prRun();
    state.verify!.refinement_rounds = MAX_REFINEMENT_ROUNDS - 1;
    state.flags.proof_loop_counters = { iters: 7, scaffold_rounds: 9, stale: 2, tag_reroutes: 1, node_strikes: { "lem:twoforms": 2 }, review_error_strikes: { a: 2 }, filler_summaries: ["dead end"] };
    escalate(state, { route: "fix-source", reason: LIVE_REASON, kind: "statement-wrong", obj_id: "lem:twoforms" });
    recordProofReviewRewind(state);
    expect((await applyPendingRewind({ runDir, state })).applied).toBe(true);
    expect(state.verify!.refinement_rounds).toBe(MAX_REFINEMENT_ROUNDS);
    // the next formalization attempt starts with fresh loop budgets (the filler's memory kept)
    expect(state.flags.proof_loop_counters).toMatchObject({ iters: 0, scaffold_rounds: 0, node_strikes: {}, filler_summaries: ["dead end"] });

    // a wrong claim spends an ERROR round: the refinement cap does not bind it
    const wrong = await prRun();
    wrong.state.verify!.refinement_rounds = MAX_REFINEMENT_ROUNDS;
    escalate(wrong.state, { route: "fix-source", reason: "[statement-wrong] the test is not valid without a finite fourth moment", kind: "statement-wrong", obj_id: "thm:main" });
    recordProofReviewRewind(wrong.state);
    expect((await applyPendingRewind(wrong)).applied).toBe(true);
    expect(wrong.state.verify!.patch_rounds).toBe(1);

    const again = await prRun();
    again.state.verify!.refinement_rounds = MAX_REFINEMENT_ROUNDS;
    escalate(again.state, { route: "fix-source", reason: LIVE_REASON, kind: "statement-wrong", obj_id: "lem:twoforms" });
    recordProofReviewRewind(again.state);
    const out = await applyPendingRewind(again);
    expect(out).toMatchObject({ applied: false, capped: true });
    expect(again.state.verify!.cap_reached).toMatchObject({ counter: "refinement_rounds", rounds: MAX_REFINEMENT_ROUNDS, cap: MAX_REFINEMENT_ROUNDS, origin: "F-rewind", findings: [expect.objectContaining({ id: "lem:twoforms", axis: "clarify" })] });
    expect(again.state.verify!.cross_stage_rewind!.status).toBe("pending");
    expect(again.state.flags.proof_review_escalation_pending).not.toBeNull();
    expect(existsSync(path.join(again.runDir, VERIFY_FILES.v1ReviseDirective))).toBe(false);
    expect(MIN_PATCH_BACKSTOP).toBe(6);
    expect(MAX_REFINEMENT_ROUNDS).toBe(3);
  });
});

describe("rewinds are proposed, the orchestrator approves", () => {
  it("presents a pending receipt once (statement, axis, both ways forward), marking it presented", async () => {
    const { runDir, state } = await prRun();
    escalate(state, { route: "fix-source", reason: LIVE_REASON, kind: "statement-wrong", obj_id: "lem:twoforms", phase: "3" });
    recordProofReviewRewind(state);
    const p = await presentPendingRewind({ runDir, state, input: "paper.tex" });
    expect(p).toMatchObject({ kind: "present", node: "lem:twoforms" });
    expect(p.message).toContain("stage F3, route fix-source [statement-wrong], statement lem:twoforms, axis clarify");
    expect(p.message).toContain("--resume --reject-rewind");
    expect(p.message).toContain(`refinement round 1/${MAX_REFINEMENT_ROUNDS}`);
    // a clarification on a node with pinned readings shows them: a pin that settles it binds
    expect(p.message).toContain("Pinned readings (binding): ass:pin-7 (reading of lem:twoforms)");
    expect(state.verify!.cross_stage_rewind).toMatchObject({ status: "pending", presented: true, nodes: ["lem:twoforms"] });
    expect(existsSync(path.join(runDir, VERIFY_FILES.v1ReviseDirective))).toBe(false); // nothing routed yet
  });

  it("a rejection records the reason (receipt, ruled-out list, a note on the statement) and lifts the halt; a repeat is a note", async () => {
    const { runDir, state } = await prRun();
    escalate(state, { route: "fix-source", reason: LIVE_REASON, kind: "statement-wrong", obj_id: "lem:twoforms" });
    recordProofReviewRewind(state);
    await presentPendingRewind({ runDir, state, input: "paper.tex" });
    rejectPendingRewind(state, "the lemma's proof fixes the interior reading (line 830)");
    expect(state.verify!.cross_stage_rewind).toMatchObject({ status: "rejected", rejected_reason: expect.stringContaining("line 830") });
    expect(state.verify!.rejected_rewinds).toEqual([expect.objectContaining({ node: "lem:twoforms", axis: "clarify", by: "orchestrator" })]);
    expect(state.verify!.findings).toEqual([expect.objectContaining({ node: "lem:twoforms", kind: "note", detail: expect.stringContaining("rewind rejected by the orchestrator") })]);
    expect(state.flags.proof_review_escalation_pending).toBeNull();

    // the F stages raise the same finding again (even word for word): a fresh receipt, then a note
    escalate(state, { route: "fix-source", reason: LIVE_REASON, kind: "statement-wrong", obj_id: "lem:twoforms", phase: "4" });
    expect(recordProofReviewRewind(state)).toBe(true);
    const p = await presentPendingRewind({ runDir, state, input: "paper.tex" });
    expect(p).toMatchObject({ kind: "repeat", node: "lem:twoforms" });
    expect(state.verify!.cross_stage_rewind).toMatchObject({ status: "rejected", rejected_reason: expect.stringContaining("repeats") });
    expect(state.verify!.rejected_rewinds).toHaveLength(1);
    expect(state.flags.proof_review_escalation_pending).toBeNull();
    expect(state.verify!.findings.filter((f) => f.kind === "unresolved")).toEqual([]);

    // a DIFFERENT finding on the same node and axis is no repeat: it is presented for a ruling
    const OTHER = "[statement-wrong] lem:twoforms states the bound for every sample size, but the constant depends on n; the statement must fix which.";
    escalate(state, { route: "fix-source", reason: OTHER, kind: "statement-wrong", obj_id: "lem:twoforms", phase: "4" });
    expect(recordProofReviewRewind(state)).toBe(true);
    const q = await presentPendingRewind({ runDir, state, input: "paper.tex" });
    expect(q).toMatchObject({ kind: "present", node: "lem:twoforms" });
  });

  it("a repeat is the same finding by content: a re-tagged or re-spaced re-raise matches, another complaint does not", () => {
    const ruled = "[statement-wrong] The frozen clause admits a fixed-count reading and an unconditional reading; edit the NL to identify its randomization regime.";
    expect(sameFinding(ruled, ruled)).toBe(true);
    expect(sameFinding(ruled, "[unclear]   The frozen clause admits a fixed-count reading and an unconditional reading; edit the NL to identify its randomization regime")).toBe(true);
    expect(sameFinding(ruled, "[statement-wrong] Lemma norestr concludes Assumption 1, which needs positive group counts; the corrected statement does not say the counts are positive.")).toBe(false);
    const verify = { rejected_rewinds: [{ node: "lem:x", axis: "correctness", stage: "F2.5", route: "fix-source", detail: ruled, reason: "r", by: "owner", at: "t" }] } as never;
    expect(rejectedMatch(verify, "lem:x", "correctness", ruled)).toBeDefined();
    expect(rejectedMatch(verify, "lem:x", "correctness", "[statement-wrong] the counts must be positive")).toBeUndefined();
    expect(rejectedMatch(verify, "lem:x", "clarify", ruled)).toBeUndefined();
  });

  it("a clarification ruled out on a node answers a reworded one on the same node; an error still needs the same content", () => {
    const ruled = "[statement-wrong] 'On the conditioning support' does not specify pointwise equality on that support versus almost-everywhere equality under the conditional covariate law.";
    const reworded = "[statement-wrong] 'On the conditioning support' does not distinguish pointwise equality on a support from conditional-law almost-sure equality; explicitly specify the equality convention.";
    expect(sameFinding(ruled, reworded)).toBe(false);
    const verify = { rejected_rewinds: [{ node: "thm:y", axis: "clarify", stage: "F2.5", route: "fix-source", detail: ruled, reason: "a.s.", by: "orchestrator", at: "t" }] } as never;
    expect(rejectedMatch(verify, "thm:y", "clarify", reworded)).toBeDefined();
    expect(rejectedMatch(verify, "thm:other", "clarify", reworded)).toBeUndefined();
    expect(rejectedMatch(verify, "thm:y", "correctness", reworded)).toBeUndefined();
  });
});

// ---------------------------------------------------------------------------------------------
// Assumption / definition targets, and one batch per review pass
// ---------------------------------------------------------------------------------------------

const HYP_CORE = {
  ...PR_CORE,
  assumptions: [
    ...PR_CORE.assumptions,
    { id: "ass:main-moment", kind: "regularity", condition: "E|Y|^4 < ∞.", novel: { flag: true, justification: "stated" } },
    { id: "ass:unused", kind: "regularity", condition: "nothing uses this.", novel: { flag: true, justification: "stated" } },
  ],
  definitions: [{ id: "def:effect", name: "effect", construction: "τ = E[Y(1) − Y(0)]" }],
  statements: [
    PR_CORE.statements[0],
    { ...PR_CORE.statements[1], depends_on: ["ass:twoforms-invertible-cdfs", "ass:main-moment", "def:effect"] },
  ],
};

async function hypRun(): Promise<{ runDir: string; state: StateJson }> {
  const r = await prRun();
  await writeFile(path.join(r.runDir, VERIFY_FILES.coreJson), JSON.stringify(HYP_CORE), "utf8");
  return r;
}

const directive = async (runDir: string) => JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
const CDF_REASON = "[statement-wrong] The frozen phrase 'strictly increasing CDFs' admits global strict increase and strict increase only on the interior outcome support; edit the note to specify the intended domain before rescaffolding.";

describe("assumption and definition targets: one directive finding on the node, naming its users", () => {
  it.each([
    ["an assumption", "ass:main-moment", "fix-source", CDF_REASON, "statement-wrong", "clarify", ["thm:main"]],
    ["a multi-user assumption", "ass:twoforms-invertible-cdfs", "fix-source", "[statement-wrong] invertibility fails at atoms of F_A", "statement-wrong", "correctness", ["lem:twoforms", "thm:main"]],
    ["a definition", "def:effect", "unclear", "the NL is ambiguous: finite-population or superpopulation effect", "ambiguous-spec", "clarify", ["thm:main"]],
  ] as const)("%s target: ONE finding, id = the node, its detail the repair line naming every user; one round", async (_what, obj_id, route, reason, kind, axis, users) => {
    const { runDir, state } = await hypRun();
    escalate(state, { route, reason, kind, obj_id, phase: "2.5" });
    recordProofReviewRewind(state);
    expect(await applyPendingRewind({ runDir, state })).toMatchObject({ applied: true, nodes: [...users] });
    const d = await directive(runDir);
    expect(d.findings).toHaveLength(1);
    expect(d.findings[0]).toMatchObject({ id: obj_id, axis, from_stage: "F2.5" });
    const line = hypothesisRepairLine(HYP_CORE as unknown as Core, obj_id)!;
    expect(line).toContain(`used by ${users.join(", ")}`);
    expect(d.findings[0].detail).toContain(line);
    expect(d.findings[0].folds).toBeUndefined(); // pins belong to statement findings
    expect(state.verify!.cross_stage_rewind).toMatchObject({ status: "applied", nodes: [...users] });
    expect(axis === "clarify" ? state.verify!.refinement_rounds : state.verify!.patch_rounds).toBe(1);
  });
});

describe("a finding on a condition the referee added lands on the results carrying it", () => {
  it("resolves to the statements using it — the fixer cannot patch a node that is not the paper's (live Sant'Anna–Zhao ass:bk-3)", () => {
    const core = structuredClone(HYP_CORE) as unknown as Core;
    core.assumptions.push({ id: "ass:bk-9", kind: "regularity", condition: "the conditional means exist absolutely", bookkeeping: { flag: true, added_by: "V1.5", reason: "needed" } } as Core["assumptions"][number]);
    core.statements.find((s) => s.id === "thm:main")!.depends_on.push("ass:bk-9");
    const t = resolveTarget(core, { obj_id: "ass:bk-9", route: "fix-source", axis: "clarify", reason: "[statement-wrong] 'exist absolutely' admits two readings" });
    expect(t).toMatchObject({ node: "thm:main", node_kind: "statement", users: ["thm:main"], status: "routed" });
    expect(directiveFindings(core, "F2.5", [t]).map((f) => f.id)).toEqual(["thm:main"]);
  });
});

describe("one review pass, one batch", () => {
  const batchFlag = (extra: Array<{ route: string; reason: string; kind?: string; obj_id?: string }> = []) => {
    const batch = [
      { route: "fix-source", reason: LIVE_REASON, kind: "statement-wrong", obj_id: "lem:twoforms" },
      { route: "fix-source", reason: "[statement-wrong] the fourth moment must be uniform in n", kind: "statement-wrong", obj_id: "ass:main-moment" },
      ...extra,
    ];
    return { ...batch[0]!, phase: "2.5", batch };
  };
  const escalateBatch = (state: StateJson, flag: ReturnType<typeof batchFlag>) => {
    state.flags.proof_review_escalation_pending = flag;
    for (const b of flag.batch) state.verify!.findings.push({ node: b.obj_id ?? "run", stage: "F2.5", kind: "unresolved", detail: b.reason, witness: null, at: "t" });
  };

  it("two findings → one receipt with two targets → presented together → one round, one directive", async () => {
    const { runDir, state } = await hypRun();
    escalateBatch(state, batchFlag());
    expect(recordProofReviewRewind(state)).toBe(true);
    expect(state.verify!.cross_stage_rewind!.targets).toEqual([
      expect.objectContaining({ obj_id: "lem:twoforms", axis: "clarify" }),
      expect.objectContaining({ obj_id: "ass:main-moment", axis: "correctness" }),
    ]);
    const p = await presentPendingRewind({ runDir, state, input: "paper.tex" });
    expect(p).toMatchObject({ kind: "present", nodes: ["lem:twoforms", "thm:main"] });
    expect(p.message).toContain("2 findings of one review pass, ruled on together — one error round 1/3 at level global (total 1/");
    expect(p.message).toContain("1. route fix-source [statement-wrong], statement lem:twoforms, axis clarify");
    expect(p.message).toContain("2. route fix-source [statement-wrong], hypothesis ass:main-moment (used by thm:main), axis correctness");
    expect(p.message).toContain("approve all");
    expect(p.message).toContain("cross_stage_rewind.targets");
    const out = await applyPendingRewind({ runDir, state });
    expect(out).toMatchObject({ applied: true, nodes: ["lem:twoforms", "thm:main"], round: 1 });
    const d = await directive(runDir);
    expect(d).toMatchObject({ mode: "patch", round: 1 });
    expect(d.findings).toEqual([
      expect.objectContaining({ id: "lem:twoforms", axis: "clarify", folds: [expect.objectContaining({ node: "lem:twoforms" })] }),
      expect.objectContaining({ id: "ass:main-moment", axis: "correctness", detail: expect.stringContaining(hypothesisRepairLine(HYP_CORE as unknown as Core, "ass:main-moment")!) }),
    ]);
    // ONE round for the batch: an error round, since one finding is a wrong claim
    expect(state.verify!.patch_rounds).toBe(1);
    expect(state.verify!.refinement_rounds ?? 0).toBe(0);
    expect(state.verify!.findings.filter((f) => f.kind === "unresolved")).toEqual([]);
    expect(state.flags.proof_review_escalation_pending).toBeNull();
  });
});
