import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile, mkdir } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, setProof } from "../../src/graph/mutate.js";
import { graphDerivedSkeleton } from "../../src/graph/skeleton.js";
import { proofTreeMeasure } from "../../src/graph/extractor.js";
import {
  runProofReviewLoop,
  improvesOn,
  MAX_ITERS,
  NO_PROGRESS_MAX,
  type ProofMeasure,
} from "../../src/formalization/proof_review_loop.js";
import { clearCapGate, resumeBlock, ITERATION_CEILING_TAG, ITERATION_CEILING_EXIT } from "../../src/cap_gates.js";
import { checkpointGuidance } from "../../src/checkpoint_playbook.js";
import { resetProofLoopBudgets } from "../../src/formalization/loop_limits.js";
import { createInitialState, loadState, saveState } from "../../src/state.js";
import type { StateJson } from "../../src/types.js";

// The Phase-B budget bounds a loop that is NOT progressing: the runner measures the Lean tree
// (open `sorry`s, proved declarations) and counts iterations since the best value. A total of 60
// iterations used to halt long builds that closed a lemma or proved helpers on every pass.

function openGraph() {
  let g = createEmptyGraph("q");
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
  g = { ...g, nodes: g.nodes.map((n) => (n.id === "t1" ? { ...n, lean: { decl_name: "t1_thm", file: "T1.lean" } } : n)) };
  return setProof(g, "t1", "sorry", 1);
}
const refreshed = () => {
  const g = openGraph();
  return { graph: g, skeleton: graphDerivedSkeleton(g), dirty: [], hashes: { t1: "h" } };
};

/** Run the loop on a theorem that stays open, with the tree's measure after `fills` filler passes
 *  given by `measureAt`. The filler escalates at pass `stopAt` (how a test ends a loop that would
 *  otherwise run on). Returns the outcome and the number of filler passes. */
async function run(opts: { state: StateJson; measureAt: (fills: number) => ProofMeasure; stopAt?: number }) {
  let fills = 0;
  const outcome = await runProofReviewLoop({
    ctx: { repoRoot: "/nonexistent-repo", qid: "q" },
    deps: {} as never,
    state: opts.state,
    buildCheck: async () => ({ ok: true, errors: "" }),
    refresh: async () => refreshed(),
    review: async (s) => ({ graph: s.graph, ok: true, escalate: null, blocking: [], substrateGates: [] }),
    fill: async (g) => {
      fills++;
      return fills === opts.stopAt
        ? { graph: g, escalate: { kind: "needs-substrate", reason: "test stop" }, summary: "" }
        : { graph: g, escalate: null, summary: "claims progress" };
    },
    measure: async () => opts.measureAt(fills),
    // The graph-diff stale cap is a separate budget; keep it out of the way.
    noProgressK: 10_000,
  });
  return { outcome, fills };
}
const reasonOf = (o: { status: string; reason?: string }) => (o.status === "escalate" ? o.reason ?? "" : "");

describe("proof-loop progress budget", () => {
  it("does not halt a loop that keeps improving past 60 iterations", async () => {
    const state = createInitialState("q");
    // One more proved helper per pass, one hole closed every tenth.
    const { outcome, fills } = await run({
      state,
      measureAt: (n) => ({ open: 20 - Math.floor(n / 10), proved: n }),
      stopAt: 90,
    });
    expect(fills).toBe(90);
    expect(reasonOf(outcome)).toContain("test stop");
    expect(state.flags.proof_loop_cap_hit).toBeUndefined();
    expect(state.flags.proof_loop_counters?.iters).toBe(90);
  });

  it("halts a loop that stops improving after the no-progress cap, naming the measure", async () => {
    const state = createInitialState("q");
    // Improves for 5 passes, then nothing.
    const { outcome, fills } = await run({ state, measureAt: (n) => ({ open: 3, proved: Math.min(n, 5) }) });
    expect(fills).toBe(5 + NO_PROGRESS_MAX);
    expect(outcome).toMatchObject({ status: "escalate", route: "bank-partial", phase: "3" });
    const reason = reasonOf(outcome);
    expect(reason).toContain(`no measurable proof progress in ${NO_PROGRESS_MAX} iterations`);
    expect(reason).toContain("3 open `sorry`(s), 5 proved declaration(s) (last beaten at iteration 5)");
    expect(state.flags.proof_loop_cap_hit).toBe(reason);
  });

  it("churn that never beats the best value still halts", async () => {
    const state = createInitialState("q");
    // A helper added then removed, a hole opened then closed: the tree changes on every pass.
    const cycle: ProofMeasure[] = [{ open: 3, proved: 10 }, { open: 3, proved: 9 }, { open: 4, proved: 12 }, { open: 3, proved: 10 }];
    const { outcome, fills } = await run({ state, measureAt: (n) => cycle[n % cycle.length] });
    // (the two records, fewest open and most proved, are each set once: at passes 0 and 2)
    expect(fills).toBe(2 + NO_PROGRESS_MAX);
    expect(reasonOf(outcome)).toContain("no measurable proof progress");
    expect(state.flags.proof_loop_counters?.progress_best).toEqual({ open: 3, proved: 12, iter: 2 });
  });

  // a hard goal split into sub-lemmas: more open than the record, and each one closed is progress
  it("a decomposition that raises the open count and then closes its sub-lemmas one per pass is not a stall", async () => {
    const state = createInitialState("q");
    const { outcome, fills } = await run({ state, measureAt: (n) => (n === 0 ? { open: 3, proved: 100 } : { open: 3 + 40 - Math.min(n, 40), proved: 100 + Math.min(n, 40) }), stopAt: 35 });
    expect(reasonOf(outcome)).toContain("test stop");
    expect(fills).toBe(35);
  });

  // with every proof closed the measure cannot move; the reviews that remain are not a stall
  it("the no-progress cap does not fire once no proof is open", async () => {
    const state = createInitialState("q");
    const { outcome, fills } = await run({ state, measureAt: () => ({ open: 0, proved: 50 }), stopAt: NO_PROGRESS_MAX + 10 });
    expect(reasonOf(outcome)).toContain("test stop");
    expect(fills).toBe(NO_PROGRESS_MAX + 10);
  });

  it("the count survives a resume", async () => {
    const state = createInitialState("q");
    const flat = () => ({ open: 2, proved: 7 });
    const first = await run({ state, measureAt: flat, stopAt: 8 });
    expect(reasonOf(first.outcome)).toContain("test stop");
    expect(state.flags.proof_loop_counters).toMatchObject({ iters: 8, progress_best: { open: 2, proved: 7, iter: 0 } });
    // The resumed loop has what is left of the budget, not a fresh one.
    const second = await run({ state: JSON.parse(JSON.stringify(state)) as StateJson, measureAt: flat });
    expect(second.fills).toBe(NO_PROGRESS_MAX - 8);
    expect(reasonOf(second.outcome)).toContain(`no measurable proof progress in ${NO_PROGRESS_MAX} iterations`);
  });

  it("the absolute ceiling stops a loop whose measure rises forever", async () => {
    const state = createInitialState("q");
    state.flags.proof_loop_counters = { iters: MAX_ITERS - 2, scaffold_rounds: 0, stale: 0, tag_reroutes: 0, node_strikes: {}, review_error_strikes: {} };
    const { outcome, fills } = await run({ state, measureAt: (n) => ({ open: 1, proved: n }) });
    expect(fills).toBe(2);
    expect(reasonOf(outcome)).toContain(`loop exceeded ${MAX_ITERS} iterations`);
    expect(state.flags.proof_loop_cap_hit).toBeTruthy();
  });

  it("at the ceiling the orchestrator asks the user, and a yes resets the count", async () => {
    const state = createInitialState("q");
    state.flags.proof_loop_counters = { iters: MAX_ITERS - 1, scaffold_rounds: 0, stale: 0, tag_reroutes: 0, node_strikes: {}, review_error_strikes: {} };
    const { outcome } = await run({ state, measureAt: (n) => ({ open: 1, proved: n }) });
    expect(reasonOf(outcome)).toContain(ITERATION_CEILING_TAG);
    // The halt and a refused resume both say to ask the user, not to diagnose a stall.
    for (const text of [resumeBlock(state.flags)!, checkpointGuidance("3", "blocked", state.flags, false, reasonOf(outcome))!]) {
      expect(text).toContain(ITERATION_CEILING_EXIT);
      expect(text).not.toContain("Do NOT simply re-resume");
    }
    // The user says yes: the gate is cleared, the loop runs again with a fresh count.
    clearCapGate(state.flags, "proof_loop_cap_hit");
    expect(state.flags.proof_loop_counters?.iters).toBe(0);
    expect(resumeBlock(state.flags)).toBeNull();
    state.flags.proof_loop_counters = { ...state.flags.proof_loop_counters!, iters: MAX_ITERS - 3 };
    const again = await run({ state, measureAt: (n) => ({ open: 1, proved: n }) });
    expect(again.fills).toBe(3);
  });

  it("a stalled loop keeps the diagnose-first guidance", async () => {
    const state = createInitialState("q");
    const { outcome } = await run({ state, measureAt: () => ({ open: 2, proved: 7 }) });
    expect(reasonOf(outcome)).not.toContain(ITERATION_CEILING_TAG);
    expect(resumeBlock(state.flags)).toContain("Do NOT simply re-resume");
  });

  it("clearing the gate, or a new formalization attempt, starts the measure over", () => {
    const seeded = (): StateJson => {
      const s = createInitialState("q");
      s.flags.proof_loop_counters = { iters: 30, scaffold_rounds: 0, stale: 0, tag_reroutes: 0, node_strikes: {}, review_error_strikes: {}, progress_best: { open: 1, proved: 9, iter: 10 } };
      return s;
    };
    const cleared = seeded();
    clearCapGate(cleared.flags, "proof_loop_cap_hit");
    expect(cleared.flags.proof_loop_counters?.progress_best).toBeUndefined();
    const rewound = seeded();
    resetProofLoopBudgets(rewound);
    expect(rewound.flags.proof_loop_counters?.progress_best).toBeUndefined();
    expect(rewound.flags.proof_loop_counters?.iters).toBe(0);
  });
});

describe("proof-loop progress budget on disk", () => {
  let dir: string;
  beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "loop-progress-")); });
  afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

  it("a state file written before the measure existed loads and takes its baseline from the tree", async () => {
    const old = createInitialState("q");
    old.flags.proof_loop_counters = { iters: 45, scaffold_rounds: 2, stale: 1, tag_reroutes: 0, node_strikes: {}, review_error_strikes: {} };
    await saveState(dir, "q", old);
    const state = await loadState(dir, "q");
    expect(state.flags.proof_loop_counters?.progress_best).toBeUndefined();
    // 45 iterations already spent: the old total of 60 would stop this improving loop 15 passes in.
    const { outcome, fills } = await run({ state, measureAt: (n) => ({ open: 5, proved: n }), stopAt: 30 });
    expect(fills).toBe(30);
    expect(reasonOf(outcome)).toContain("test stop");
    expect(state.flags.proof_loop_counters).toMatchObject({ iters: 75, scaffold_rounds: 2, progress_best: { open: 5, proved: 29, iter: 74 } });
    // And the new field round-trips through the schema.
    await saveState(dir, "q", state);
    expect((await loadState(dir, "q")).flags.proof_loop_counters?.progress_best).toEqual({ open: 5, proved: 29, iter: 74 });
  });

  it("measures the tree's text: a `sorry` helper is open work, not a proved declaration", async () => {
    const lean = path.join(dir, "lean");
    await mkdir(path.join(lean, "Helpers"), { recursive: true });
    await writeFile(path.join(lean, "Main.lean"), [
      "/-- no sorry here -/",
      "theorem main : 1 = 1 := by",
      "  have h : True := by sorry",
      "  sorry -- two holes",
      "def size : Nat := 3",
    ].join("\n"), "utf8");
    await writeFile(path.join(lean, "Helpers", "A.lean"), "lemma a : True := trivial\n\n@[simp] theorem b : True := by\n  trivial\n", "utf8");
    const before = await proofTreeMeasure(lean);
    expect(before).toEqual({ open: 2, proved: 2 });

    await writeFile(path.join(lean, "Helpers", "B.lean"), "lemma stub : True := by sorry\n", "utf8");
    const stubbed = await proofTreeMeasure(lean);
    expect(stubbed).toEqual({ open: 3, proved: 2 });
    expect(improvesOn(before, stubbed)).toBe(false);

    await writeFile(path.join(lean, "Helpers", "B.lean"), "lemma stub : True := trivial\n", "utf8");
    const proved = await proofTreeMeasure(lean);
    expect(proved).toEqual({ open: 2, proved: 3 });
    expect(improvesOn(before, proved)).toBe(true);
    // Fewer holes wins over fewer declarations; an equal value is not an improvement.
    expect(improvesOn(before, { open: 1, proved: 0 })).toBe(true);
    expect(improvesOn(before, { ...before })).toBe(false);
  });
});
