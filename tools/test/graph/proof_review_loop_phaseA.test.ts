import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addAssumption, addEdge, addNode, setProof, setNodeReview } from "../../src/graph/mutate.js";
import { discardReroutedAgentAssumptions, runProofReviewLoop } from "../../src/formalization/proof_review_loop.js";
import type { ReviewerResult } from "../../src/formalization/proof_reviewer.js";
import type { FillerResult } from "../../src/formalization/proof_filler.js";
import type { FormalizationGraph } from "../../src/graph/types.js";

/** A graph whose single frozen theorem is proved + matched → frozen closure is complete. */
function settledGraph(): FormalizationGraph {
  let g = createEmptyGraph("q");
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });
  g = setProof(g, "t1", "complete", 0);
  g = setNodeReview(g, "t1", "matched", "h");
  return g;
}

const rs = () => ({ graph: settledGraph(), skeleton: [], dirty: [], hashes: {} });
const okReview = (g: FormalizationGraph): ReviewerResult => ({ graph: g, ok: true, escalate: null, blocking: [], substrateGates: [] });
const AMBIG = "'strictly increasing CDFs' admits global strict increase and strict increase only on the interior support; specify the domain";
const throwingDeps = { runCodex: (async () => { throw new Error("seam should be stubbed"); }) as never };

describe("proof-review loop — Phase A statement/scaffold gate", () => {
  it("retires stale filler assumptions after their target is successfully re-scaffolded", () => {
    let g = settledGraph();
    g = addAssumption(g, {
      node: "t1",
      id: "ass:filler:2:t1:10:a_derived",
      statement: "a conclusion the filler temporarily assumed",
      tier: 2,
      classification: "faithful-refinement",
      anchor: "equation (2)",
      provenance: "agent-introduced",
    });
    const byAssumption = discardReroutedAgentAssumptions(g, ["ass:filler:2:t1:10:a_derived"]);
    expect(byAssumption.nodes.some((n) => n.id === "ass:filler:2:t1:10:a_derived")).toBe(false);
    expect(byAssumption.edges.some((e) => e.to === "ass:filler:2:t1:10:a_derived")).toBe(false);
    expect(byAssumption.nodes.find((n) => n.id === "t1")?.review).toEqual({
      status: "unreviewed",
      passed_hash: null,
    });

    const byParent = discardReroutedAgentAssumptions(g, ["t1"]);
    expect(byParent.nodes.some((n) => n.id === "ass:filler:2:t1:10:a_derived")).toBe(false);
    expect(byParent.nodes.some((n) => n.id === "t1")).toBe(true);

    let shared = addNode(g, {
      id: "t2", kind: "theorem", provenance: "from-note", nl_statement: "other", tex_anchor: "",
    });
    shared = addEdge(shared, {
      kind: "proof-uses", from: "t2", to: "ass:filler:2:t1:10:a_derived", source: "declared",
    });
    const localized = discardReroutedAgentAssumptions(shared, ["t1"]);
    expect(localized.nodes.some((n) => n.id === "ass:filler:2:t1:10:a_derived")).toBe(true);
    expect(localized.edges.some((e) => e.from === "t1" && e.to === "ass:filler:2:t1:10:a_derived")).toBe(false);
    expect(localized.edges.some((e) => e.from === "t2" && e.to === "ass:filler:2:t1:10:a_derived")).toBe(true);
  });

  // A Lean-side finding (or one a binding pinned reading settles) is re-scaffolded by F2 and the
  // loop proceeds once the re-review clears.
  it.each([
    { label: "a scaffold-mismatch", escalate: { kind: "scaffold-mismatch", obj_id: "t1", reason: "H7 budget missing from t1's binder" }, redirectContains: "" },
    // `kind_synthesized` marks routine schema drift, not a reviewer's judgment that it could not
    // adjudicate — halting on it would stall runs that used to self-heal.
    { label: "a SYNTHESIZED unadjudicable (reason with no kind)", escalate: { kind: "unadjudicable", kind_synthesized: true, obj_id: "t1", reason: "hypothesis H7 is missing" }, redirectContains: "" },
    { label: "a statement-wrong that a pinned reading settles", escalate: { kind: "statement-wrong", obj_id: "t1", reason: AMBIG, pinned: ["ass:pin-1 (reading of t1): F_1(y) < F_0(y) at finite interior points"] }, redirectContains: "F_1(y) < F_0(y) at finite interior points" },
  ])("$label reroutes to F2 (scaffold seam), then proceeds once the re-review clears", async ({ escalate, redirectContains }) => {
    let reviewCalls = 0;
    const scaffoldCalls: { redirect: string; targets: string[] }[] = [];
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: "/tmp", qid: "q" },
      deps: throwingDeps,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => rs(),
      scaffold: async (a) => { scaffoldCalls.push(a); },
      fill: async (g): Promise<FillerResult> => ({ graph: g, escalate: null, summary: "" }),
      review: async (s): Promise<ReviewerResult> => {
        if (++reviewCalls > 1) return okReview(s.graph);
        return { graph: s.graph, ok: false, escalate, blocking: ["t1"], substrateGates: [] } as ReviewerResult;
      },
    });
    expect(scaffoldCalls).toHaveLength(1);
    expect(scaffoldCalls[0].targets).toEqual(["t1"]);
    expect(scaffoldCalls[0].redirect).toContain(redirectContains);
    expect(outcome.status).toBe("completed");
  });

  // Everything else ESCALATES without touching Lean: re-scaffolding an unjudged or paper-side
  // target lets F2 re-emit it into a `matched` with the original question never answered.
  it.each([
    { kind: "note-wrong", route: "fix-source", reason: "note assumes a hypothesis the .tex never states" },
    { kind: "unadjudicable", route: "unclear", reason: "can't place fault between note and Lean" },
    { kind: "missing-review-evidence", route: undefined, reason: "review evidence unavailable" },
  ])("a $kind finding escalates without re-scaffolding", async ({ kind, route, reason }) => {
    const scaffoldCalls: unknown[] = [];
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: "/tmp", qid: "q" },
      deps: throwingDeps,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => rs(),
      scaffold: async (a) => { scaffoldCalls.push(a); },
      fill: async (g): Promise<FillerResult> => ({ graph: g, escalate: null, summary: "" }),
      review: async (s): Promise<ReviewerResult> => ({
        graph: s.graph, ok: false, escalate: { kind, obj_id: "t1", reason }, blocking: ["t1"], substrateGates: [],
      }),
    });
    expect(scaffoldCalls).toHaveLength(0);
    expect(outcome.status).toBe("escalate");
    if (outcome.status === "escalate") {
      if (route) expect(outcome.route).toBe(route);
      expect(outcome.reason).toContain(kind);
    }
  });
});

describe("proof-review loop — F4 dead-helper sweep wiring", () => {
  it("escalates fix-source at phase 4 when the sweep finds a dead decl, after the convergence review (whose receipts persist)", async () => {
    let reviewCalled = 0;
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: "/tmp", qid: "q" },
      deps: throwingDeps,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => rs(),
      fill: async (g): Promise<FillerResult> => ({ graph: g, escalate: null, summary: "" }),
      review: async (s, mode): Promise<ReviewerResult> => { if (mode === "convergence") reviewCalled++; return okReview(s.graph); },
      sweepDead: async () => [{ decl: "abandoned_route_helper", file: "Helpers/X.lean", line: 7 }],
    });
    expect(outcome).toMatchObject({ status: "escalate", route: "fix-source", phase: "4" });
    expect((outcome as { reason?: string }).reason).toContain("abandoned_route_helper");
    // The dual review ran first: the resume after pruning re-reviews only what the pruning changed,
    // instead of a full F4 re-entry per dead helper.
    expect(reviewCalled).toBe(1);
  });

  it("a convergence halt carries the dead helpers with it, so one resume settles both", async () => {
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: "/tmp", qid: "q" },
      deps: throwingDeps,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => rs(),
      fill: async (g): Promise<FillerResult> => ({ graph: g, escalate: null, summary: "" }),
      review: async (s, mode): Promise<ReviewerResult> =>
        mode === "convergence"
          ? { graph: s.graph, ok: false, escalate: null, blocking: ["t1"], substrateGates: [] }
          : okReview(s.graph),
      sweepDead: async () => [{ decl: "abandoned_route_helper", file: "Helpers/X.lean", line: 7 }],
    });
    expect(outcome).toMatchObject({ status: "escalate", route: "hint", phase: "4" });
    const reason = (outcome as { reason: string }).reason;
    expect(reason).toContain("convergence review flagged: t1");
    expect(reason).toContain("abandoned_route_helper");
  });
});

describe("proof-review loop — one review pass, one paper-statement batch", () => {
  const run = (review: ReviewerResult["escalations"], scaffoldCalls: unknown[] = []) =>
    runProofReviewLoop({
      ctx: { repoRoot: "/tmp", qid: "q" },
      deps: throwingDeps,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => rs(),
      scaffold: async (a) => { scaffoldCalls.push(a); },
      fill: async (g): Promise<FillerResult> => ({ graph: g, escalate: null, summary: "" }),
      review: async (s): Promise<ReviewerResult> => ({
        graph: s.graph, ok: false, escalate: review![0]!, escalations: review, blocking: ["t1"], substrateGates: [],
      }),
    });

  it("gathers every statement-level finding of the pass into one paper batch, ahead of and without a Lean-internal finding, re-scaffolding nothing", async () => {
    const scaffoldCalls: unknown[] = [];
    const outcome = await run([
      { kind: "scaffold-mismatch", obj_id: "t1", reason: "binder order" },
      { kind: "statement-wrong", obj_id: "lem:twoforms", reason: "the frozen wording permits both readings of the inverse" },
      { kind: "statement-wrong", obj_id: "ass:scale-cdf", reason: "'strictly increasing' admits two readings" },
    ], scaffoldCalls);
    expect(scaffoldCalls).toHaveLength(0);
    expect(outcome).toMatchObject({
      status: "escalate", route: "fix-source", phase: "2.5", kind: "statement-wrong", obj_id: "lem:twoforms",
      batch: [
        { route: "fix-source", kind: "statement-wrong", obj_id: "lem:twoforms", reason: "[statement-wrong] the frozen wording permits both readings of the inverse" },
        { route: "fix-source", kind: "statement-wrong", obj_id: "ass:scale-cdf", reason: "[statement-wrong] 'strictly increasing' admits two readings" },
      ],
    });
    if (outcome.status === "escalate") expect(outcome.batch).toHaveLength(2);
  });
});

describe("proof-review loop — budgets, worker failures and the basis ledger", () => {
  const drift = (g: FormalizationGraph, extra: Partial<ReviewerResult> = {}): ReviewerResult =>
    ({ graph: g, ok: false, escalate: { kind: "scaffold-mismatch", obj_id: "t1", reason: "H7 missing" }, blocking: ["t1"], substrateGates: [], ...extra });
  const base = (over: Partial<Parameters<typeof runProofReviewLoop>[0]>) => runProofReviewLoop({
    ctx: { repoRoot: "/tmp", qid: "q" },
    deps: throwingDeps,
    buildCheck: async () => ({ ok: true, errors: "" }),
    refresh: async () => rs(),
    scaffold: async () => {},
    fill: async (g): Promise<FillerResult> => ({ graph: g, escalate: null, summary: "" }),
    review: async (s): Promise<ReviewerResult> => okReview(s.graph),
    ...over,
  });
  /** A shared state the loop can also persist (F4 writes its receipts to disk under a real run dir). */
  const sharedState = async () => {
    const { mkdtemp } = await import("node:fs/promises");
    const { tmpdir } = await import("node:os");
    const path = await import("node:path");
    const { createInitialState, saveState } = await import("../../src/state.js");
    const dir = await mkdtemp(path.join(tmpdir(), "loop-budget-"));
    const state = createInitialState("q");
    await saveState(dir, "q", state);
    return { state, ctx: { repoRoot: dir, qid: "q" } };
  };

  it("a scaffold round is charged per DISPATCHED reroute: a pass that reroutes nothing (a resume, a re-entry) costs none", async () => {
    const clean = await sharedState();
    expect(await base(clean)).toMatchObject({ status: "completed" });
    expect(clean.state.flags.proof_loop_counters?.scaffold_rounds).toBe(0);
    let calls = 0;
    const rerouted = await sharedState();
    await base({ ...rerouted, review: async (s) => (++calls === 1 ? drift(s.graph) : okReview(s.graph)) });
    expect(rerouted.state.flags.proof_loop_counters?.scaffold_rounds).toBe(1);
  });

  it("a reroute whose F2 pass left the tree red hands the diagnostics to the filler's compile repair and clears the directive once green", async () => {
    const { state, ctx } = await sharedState();
    state.flags.scaffold_redirect = "pending directive";
    const directives: string[] = [];
    let calls = 0;
    const outcome = await base({
      state, ctx,
      review: async (s) => (++calls === 1 ? drift(s.graph) : okReview(s.graph)),
      scaffold: async () => { throw new Error("F2 run compile gate failed; refusing to advance to F2.5:\nT1.lean:3:2: error: unknown identifier 'foo'"); },
      fill: async (g, directive): Promise<FillerResult> => { if (directive) directives.push(directive); return { graph: g, escalate: null, summary: "fixed foo" }; },
    });
    expect(outcome).toMatchObject({ status: "completed" });
    expect(directives[0]).toContain("F3 LOCAL COMPILE REPAIR");
    expect(directives[0]).toContain("unknown identifier 'foo'");
    expect(state.flags.scaffold_redirect).toBeNull();
    // a repair that leaves it red keeps the directive pending for the resume and halts
    const red = await sharedState();
    red.state.flags.scaffold_redirect = "pending directive";
    calls = 0;
    const stuck = await base({
      ...red,
      review: async (s) => (++calls === 1 ? drift(s.graph) : okReview(s.graph)),
      scaffold: async () => { throw new Error("F2 run compile gate failed; refusing to advance to F2.5:\nstill red"); },
      buildCheck: async () => ({ ok: false, errors: "still red" }),
    });
    expect(stuck).toMatchObject({ status: "escalate", route: "fix-source", phase: "2.5" });
    expect((stuck as { reason: string }).reason).toContain("F2 re-scaffold did not complete");
    expect(red.state.flags.scaffold_redirect).toBe("pending directive");
  });

  it("a review unit whose worker failed repeats the pass once; a second failure in a row halts instead of unwinding the run", async () => {
    const failed = (g: FormalizationGraph): ReviewerResult => ({ ...okReview(g), failedUnits: [{ label: "t1", targets: ["t1"], error: "worker killed: inactivity timeout" }] });
    let calls = 0;
    expect(await base({ review: async (s) => (++calls === 1 ? failed(s.graph) : okReview(s.graph)) })).toMatchObject({ status: "completed" });
    expect(calls).toBeGreaterThan(2);
    const twice = await base({ review: async (s) => failed(s.graph) });
    expect(twice).toMatchObject({ status: "escalate", route: "hint", phase: "2.5" });
    expect((twice as { reason: string }).reason).toContain("[reviewer-worker-failure]");
  });

  it("a drift flagged while proofs are filled routes back through the statement gate like a Phase-A drift, instead of halting as a hint", async () => {
    const { phase3Drift } = await import("../../src/formalization/dispatcher.js");
    let delta = 0;
    const outcome = await base({
      review: async (s, mode) => (mode === "delta" && ++delta === 2
        ? { graph: s.graph, ok: false, escalate: null, blocking: ["lem:x"], driftNotes: { "lem:x": "should be ∀ᶠ n" }, substrateGates: [] }
        : okReview(s.graph)),
    });
    expect(outcome).toMatchObject({ status: "escalate", route: "unclear", phase: "3", kind: "scaffold-mismatch", obj_id: "lem:x" });
    expect((outcome as { reason: string }).reason).toContain("should be ∀ᶠ n");
    expect(phase3Drift(outcome)).toBe(true);
  });

  it("the repeated-error cap counts one drift event once, whether or not the reviewer wrapped it in an escalate object", async () => {
    let calls = 0;
    const outcome = await base({
      review: async (s) => (++calls % 2 === 1
        ? drift(s.graph)
        : { graph: s.graph, ok: false, escalate: null, blocking: ["t1"], substrateGates: [] }),
    });
    expect(outcome).toMatchObject({ status: "escalate", route: "fix-source" });
    expect((outcome as { reason: string }).reason).toContain("[repeated-f2.5-error]");
    expect((outcome as { reason: string }).reason).toContain("flagged 3 times");
  });

  it("the resume after a hint halt grants the first pass one re-review of an unchanged basis; a standing drift an F2 reroute could not move halts as a dispute", async () => {
    const { createInitialState } = await import("../../src/state.js");
    const state = createInitialState("q");
    state.flags.proof_review_escalation_pending = { route: "hint", reason: "reviewer flagged: t1", phase: "2.5" };
    const flips: Array<boolean | undefined> = [];
    const standing = (g: FormalizationGraph): ReviewerResult =>
      ({ ...drift(g, { escalate: null }), standing: ["t1"], driftNotes: { t1: "H7 missing" }, reviewBasis: { t1: { basis: "b1", reviews: 1 } } });
    const outcome = await base({
      state,
      review: async (s, _mode, opts) => { flips.push(opts?.rereviewUnchanged); return standing(s.graph); },
    });
    expect(flips).toEqual([true, false]); // one reroute on the basis, then the dispute
    expect(outcome).toMatchObject({ status: "escalate", route: "hint", phase: "2.5" });
    expect((outcome as { reason: string }).reason).toContain("[standing-drift]");
    expect((outcome as { reason: string }).reason).toContain("H7 missing");
  });
});
