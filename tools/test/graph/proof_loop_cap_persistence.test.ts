import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile, mkdir } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { buildGraphFromMd } from "../../src/graph/from_note.js";
import { graphPath, saveGraph } from "../../src/graph/store.js";
import { runProofReviewLoop } from "../../src/formalization/proof_review_loop.js";
import { CAP_GATE_FLAGS, clearCapGate } from "../../src/cap_gates.js";
import { loadState, saveState, createInitialState } from "../../src/state.js";
import type { ReviewerResult } from "../../src/formalization/proof_reviewer.js";

let dir: string;
beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "loop-cap-")); });
afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

// A reviewer that ALWAYS flags the same node as drifted — it never converges.
// This is the adversarial case: without a persisted cap, each resume grants a fresh
// budget and the orchestrator can re-roll a non-deterministic reviewer forever.
const driftOut = JSON.stringify({
  status: "ok",
  statement_verdicts: [{ obj_id: "t1", verdict: "scaffold-mismatch", note: "drifted" }],
  assumption_verdicts: [],
  substrate_gates: [],
  escalate: { kind: "scaffold-mismatch", reason: "t1 drifted", targets: ["t1"] },
});

async function setup() {
  const md = "### T-block: t1 — Rate theorem\n**Statement.** the rate bound holds.\n";
  await writeFile(path.join(dir, "q_v1.md"), md, "utf8");
  await saveGraph(graphPath(dir), await buildGraphFromMd("q", path.join(dir, "q_v1.md")));
  const leanDir = path.join(dir, "lean");
  await mkdir(leanDir, { recursive: true });
  await writeFile(path.join(leanDir, "T1.lean"), "-- @node: t1\ntheorem t1_thm : True := by trivial\n", "utf8");
  // The loop persists its iteration counters into state.json — seed a real one.
  await saveState(dir, "q", createInitialState("q"));
  return leanDir;
}

const deps = {
  runCodex: (async () => ({ stdout: driftOut })) as never,
  runClaude: (async () => driftOut) as never,
};
const driftReview = async (s: { graph: ReviewerResult["graph"] }): Promise<ReviewerResult> => ({
  graph: s.graph,
  ok: false,
  escalate: { kind: "scaffold-mismatch", obj_id: "t1", reason: "t1 drifted" },
  blocking: ["t1"],
  substrateGates: [],
});

describe("proof-loop iteration caps are PERSISTED and only main can reset them", () => {
  it("escalates after the same F2.5 target+diagnostic is flagged three times", async () => {
    const leanDir = await setup();
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: dir, qid: "q" },
      deps,
      formalizationDir: dir,
      leanDir,
      review: driftReview,
      scaffold: async () => {},
      buildCheck: async () => ({ ok: true, errors: "" }),
    });
    expect(outcome.status).toBe("escalate");
    if (outcome.status === "escalate") {
      expect(outcome.reason).toContain("[repeated-f2.5-error]");
      expect(outcome.reason).toContain("flagged 3 times");
    }
    const persisted = await loadState(dir, "q");
    // A round is charged per DISPATCHED reroute: two were, and the third flag tripped the cap
    // before a third (a pass that reroutes nothing — a resume, a re-entry — costs no round).
    expect(persisted.flags.proof_loop_counters?.scaffold_rounds).toBe(2);
    expect(Object.values(persisted.flags.proof_loop_counters?.review_error_strikes ?? {})).toContain(3);
    expect(persisted.flags.proof_loop_counters?.node_strikes.t1).toBe(2);
  });

  it("an F2 reroute starts the proof measure over (it rewrites statements)", async () => {
    const leanDir = await setup();
    const st = await loadState(dir, "q");
    st.flags.proof_loop_counters = { iters: 30, scaffold_rounds: 0, stale: 0, tag_reroutes: 0, node_strikes: {}, review_error_strikes: {}, progress_best: { open: 0, proved: 40, iter: 12 } };
    await saveState(dir, "q", st);
    await runProofReviewLoop({
      ctx: { repoRoot: dir, qid: "q" },
      deps,
      formalizationDir: dir,
      leanDir,
      review: driftReview,
      scaffold: async () => {},
      buildCheck: async () => ({ ok: true, errors: "" }),
    });
    const persisted = await loadState(dir, "q");
    expect(persisted.flags.proof_loop_counters?.scaffold_rounds).toBeGreaterThan(0);
    expect(persisted.flags.proof_loop_counters?.progress_best).toBeUndefined();
    expect(persisted.flags.proof_loop_counters?.iters).toBe(30);
  });

  it("persists a tag-reroute spend before invoking the external scaffolder", async () => {
    const leanDir = await setup();
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: dir, qid: "q" },
      deps,
      formalizationDir: dir,
      leanDir,
      review: async (s): Promise<ReviewerResult> => ({
        graph: {
          ...s.graph,
          symbolReview: { "sym:X": { verdict: "untagged", hash: "cluster0" } },
        },
        ok: true,
        escalate: null,
        blocking: [],
        substrateGates: [],
      }),
      scaffold: async () => { throw new Error("simulated process-boundary failure"); },
      buildCheck: async () => ({ ok: true, errors: "" }),
    });
    expect(outcome.status).toBe("escalate");
    const persisted = await loadState(dir, "q");
    expect(persisted.flags.proof_loop_counters?.scaffold_rounds).toBe(1);
    expect(persisted.flags.proof_loop_counters?.tag_reroutes).toBe(1);
  });

  it("a RESUME does not hand the loop a fresh budget — scaffold rounds accumulate across calls", async () => {
    const leanDir = await setup();
    const args = {
      ctx: { repoRoot: dir, qid: "q" },
      deps,
      formalizationDir: dir,
      leanDir,
      review: driftReview,
      scaffold: async () => {},              // re-scaffold is a no-op: the node never converges
      buildCheck: async () => ({ ok: true, errors: "" }),
    };

    // First run: the loop burns budget on the non-converging node and trips the cap.
    const first = await runProofReviewLoop(args);
    expect(first.status).toBe("escalate");
    const afterFirst = await loadState(dir, "q");
    const spent = afterFirst.flags.proof_loop_counters?.scaffold_rounds ?? 0;
    expect(spent).toBeGreaterThan(0);                      // spend PERSISTED, not lost with the process
    expect(afterFirst.flags.proof_loop_cap_hit).toBeTruthy(); // cap tripped → blocks the next resume

    // Second run = a plain `--resume` with no root-cause fix and no `--clear-gate`.
    // It must NOT be handed a fresh budget: the counters carry over, they do not reset to 0.
    const second = await runProofReviewLoop(args);
    expect(second.status).toBe("escalate");
    const afterSecond = await loadState(dir, "q");
    const c = afterSecond.flags.proof_loop_counters;
    expect(c?.scaffold_rounds ?? 0).toBeGreaterThanOrEqual(spent); // carried over, never reset
    expect(afterSecond.flags.proof_loop_cap_hit).toBeTruthy();
  });

  it("after main clears the gate, the loop gets a fresh budget (the reset is auditable, not silent)", async () => {
    const leanDir = await setup();
    const args = {
      ctx: { repoRoot: dir, qid: "q" },
      deps,
      formalizationDir: dir,
      leanDir,
      review: driftReview,
      scaffold: async () => {},
      buildCheck: async () => ({ ok: true, errors: "" }),
    };
    expect(CAP_GATE_FLAGS).toContain("proof_loop_cap_hit");
    await runProofReviewLoop(args);
    const st = await loadState(dir, "q");
    expect(st.flags.proof_loop_counters?.scaffold_rounds ?? 0).toBeGreaterThan(0);
    const memory = ["round 12: blocker at measurability step"];
    st.flags.proof_loop_counters!.filler_summaries = memory;
    clearCapGate(st.flags, "proof_loop_cap_hit");
    await saveState(dir, "q", st);

    const reloaded = await loadState(dir, "q");
    expect(reloaded.flags.proof_loop_cap_hit).toBeUndefined();
    // ALL iteration counters reset, but the dead-end memory is not a budget: wiping it restarted
    // the resumed loop cold on the same known blockers.
    expect(reloaded.flags.proof_loop_counters).toMatchObject({
      iters: 0,
      scaffold_rounds: 0,
      stale: 0,
      tag_reroutes: 0,
      node_strikes: {},
      review_error_strikes: {},
      filler_summaries: memory,
    });
  });
});
