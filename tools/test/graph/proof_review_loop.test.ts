import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile, mkdir } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { buildGraphFromMd } from "../../src/graph/from_note.js";
import { graphPath, saveGraph } from "../../src/graph/store.js";
import { provisionLoopEnv } from "./loop_test_env.js";
import { saveState, createInitialState } from "../../src/state.js";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, setProof, setNodeReview } from "../../src/graph/mutate.js";
import { runProofReviewLoop } from "../../src/formalization/proof_review_loop.js";
import { graphDerivedSkeleton } from "../../src/graph/skeleton.js";

function thm(complete: boolean, matched: boolean) {
  let g = createEmptyGraph("q");
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
  g = { ...g, nodes: g.nodes.map((n) => (n.id === "t1" ? { ...n, lean: { decl_name: "t1_thm", file: "T1.lean" } } : n)) };
  g = setProof(g, "t1", complete ? "complete" : "sorry", complete ? 0 : 1);
  if (matched) g = setNodeReview(g, "t1", "matched", "h");
  return g;
}
const refreshOf = (g: ReturnType<typeof thm>) => ({ graph: g, skeleton: graphDerivedSkeleton(g), dirty: ["t1"], hashes: { t1: "h" } });

describe("runProofReviewLoop", () => {
  it("converges: review ok → fill → complete → convergence review → completed", async () => {
    const states = [refreshOf(thm(false, false)), refreshOf(thm(true, true))];
    let ri = 0;
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: "/r", qid: "q" },
      deps: {} as never,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => states[Math.min(ri++, states.length - 1)],
      review: async (s) => ({ graph: s.graph, ok: true, escalate: null, blocking: [], substrateGates: [] }),
      fill: async (g) => ({ graph: g, escalate: null, summary: "proved t1" }),
    });
    expect(outcome.status).toBe("completed");
  });

  it("escalates when the reviewer flags a blocking finding", async () => {
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: "/r", qid: "q" },
      deps: {} as never,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => refreshOf(thm(false, false)),
      review: async (s) => ({ graph: s.graph, ok: false, escalate: null, blocking: ["A-2"], substrateGates: [] }),
      fill: async (g) => ({ graph: g, escalate: null, summary: "" }),
    });
    expect(outcome.status).toBe("escalate");
    if (outcome.status === "escalate") expect(outcome.route).toBe("hint");
  });

  it("escalates build-substrate when the filler hits a substrate wall", async () => {
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: "/r", qid: "q" },
      deps: {} as never,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => refreshOf(thm(false, false)),
      review: async (s) => ({ graph: s.graph, ok: true, escalate: null, blocking: [], substrateGates: [] }),
      fill: async (g) => ({ graph: g, escalate: { kind: "needs-substrate", reason: "concentration bound" }, summary: "" }),
    });
    expect(outcome.status).toBe("escalate");
    if (outcome.status === "escalate") {
      expect(outcome.route).toBe("build-substrate");
      expect(outcome.phase).toBe("3");
    }
  });

  it("escalates bank-partial after K stale iterations", async () => {
    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: "/r", qid: "q" },
      deps: {} as never,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => refreshOf(thm(false, false)), // never progresses
      review: async (s) => ({ graph: s.graph, ok: true, escalate: null, blocking: [], substrateGates: [] }),
      fill: async (g) => ({ graph: g, escalate: null, summary: "no progress" }),
      noProgressK: 2,
    });
    expect(outcome.status).toBe("escalate");
    if (outcome.status === "escalate") expect(outcome.route).toBe("bank-partial");
  });
});

// REGRESSION: `pipeline.ts` loads state ONCE at run start and re-saves that same in-memory object
// after each stage. The loop wrote `proof_loop_counters` / `cited_checks` straight to disk via its
// own loadState→saveState, so the pipeline's stale copy CLOBBERED them (last-writer-wins,
// deterministic — not a race). Effects: the iteration caps became inert (every resume got a fresh
// budget → unbounded re-rolls) and `cited_checks: []` defeated the F5 cited-mismatch refusal.
// Fix: the loop must ALSO write into the SHARED state object the pipeline will save.
let dir: string;

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
  await saveState(dir, "q", createInitialState("q"));
  await provisionLoopEnv(dir);
  return leanDir;
}

const deps = {
  runCodex: (async () => ({ stdout: driftOut })) as never,
  runClaude: (async () => driftOut) as never,
};

describe("the loop writes its state onto the SHARED object, so the pipeline cannot clobber it", () => {
  beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "loop-shared-")); });
  afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

  it("iteration counters land on the shared state the pipeline will re-save", async () => {
    const leanDir = await setup();
    const shared = createInitialState("q"); // the object pipeline.ts holds and later saves

    const outcome = await runProofReviewLoop({
      ctx: { repoRoot: dir, qid: "q" },
      deps,
      state: shared,
      formalizationDir: dir,
      leanDir,
      corePath: path.join(dir, "core.json"),
      scaffold: async () => {},
      buildCheck: async () => ({ ok: true, errors: "" }),
    });
    expect(outcome.status).toBe("escalate");

    // Were the loop's writes visible on the SHARED object? If not, pipeline.ts's stale re-save
    // silently erases them and the caps are inert.
    expect(shared.flags.proof_loop_counters).toBeDefined();
    expect(shared.flags.proof_loop_counters?.scaffold_rounds ?? 0).toBeGreaterThan(0);
    // The no-op scaffold changed nothing: the drift stands on an unchanged basis after its one
    // reroute, so the loop halts as a dispute instead of re-rolling the reviewer up to the cap.
    if (outcome.status === "escalate") expect(outcome.reason).toContain("[standing-drift]");
    expect(shared.flags.proof_loop_counters?.scaffold_rounds).toBe(1);
  });
});
