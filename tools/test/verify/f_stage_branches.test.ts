import { createHash } from "node:crypto";
import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { assertFStageEntryCoherence } from "../../src/pipeline.js";
import { runProofReviewLoop } from "../../src/formalization/proof_review_loop.js";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, setNodeReview, setProof } from "../../src/graph/mutate.js";
import { graphDerivedSkeleton } from "../../src/graph/skeleton.js";
import { saveState } from "../../src/state.js";
import type { SubstrateGate } from "../../src/judgment.js";
import { runGatesPath } from "../../src/formalization/run_gates.js";
import { adjudicateRedoMathRewind, recordProofReviewOutcome } from "../../src/formalization/dispatcher.js";
import { recordVerifyFinding } from "../../src/verify/findings.js";
import {
  auditCitedReview,
  citedEvidenceHash,
  splitCitedFindingsForVerify,
} from "../../src/formalization/delivery_audit.js";
import { PlanSchema } from "../../src/formalization/plan/schema.js";
import type { Core } from "../../src/core/schema.js";
import { coreJsonPath } from "../../src/core/core_io.js";
import { createVerifyInitialState } from "../../src/state.js";
import type { CitedReviewReceipt, PipelineContext, StateJson } from "../../src/types.js";
import type { VerifyState } from "../../src/verify/types.js";
import { tk } from "../toolkit/helpers.js";

const QID = "user_paper";

function verifyBlock(): VerifyState {
  return {
    phase: "formalization",
    source: { input: "paper.tex", main_file: "paper.tex", sha256: "0".repeat(64) },
    targets: null,
    core_sha256: null,
    v1_rounds: 1,
    v1_5_rounds: 0,
    findings: [],
    report_path: null,
  };
}

function verifyState(): StateJson {
  const state = createVerifyInitialState(QID, verifyBlock());
  state.stage_completed = "V1.5";
  return state;
}

async function verifyCtx(): Promise<PipelineContext> {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-fbranch-"));
  return {
    repoRoot,
    toolkit: tk(repoRoot),
    qid: QID,
    resume: true,
    dryRun: false,
  };
}

/** Write `core.json` for the run and return its sha256. */
async function writeCore(ctx: PipelineContext, body: string): Promise<string> {
  const corePath = coreJsonPath(ctx);
  await mkdir(path.dirname(corePath), { recursive: true });
  await writeFile(corePath, body, "utf8");
  return createHash("sha256").update(Buffer.from(body, "utf8")).digest("hex");
}

describe("recordVerifyFinding", () => {
  it("dedupes on (node, stage, kind, detail)", () => {
    const state = verifyState();
    const f = { node: "thm:main", stage: "F3", kind: "unresolved" as const, detail: "stuck", witness: null };
    recordVerifyFinding(state, f);
    recordVerifyFinding(state, { ...f });
    expect(state.verify!.findings).toHaveLength(1);
    expect(state.verify!.findings[0].at).toMatch(/^\d{4}-\d{2}-\d{2}T/);
    recordVerifyFinding(state, { ...f, detail: "stuck differently" });
    expect(state.verify!.findings).toHaveLength(2);
  });
});

describe("assertFStageEntryCoherence", () => {
  it.each([
    ["refuses F entry before V1.5 accepted a core", async (ctx: PipelineContext, s: StateJson) => { s.stage_completed = "V1"; s.verify!.core_sha256 = await writeCore(ctx, "{}"); }, /V1\.5 has not accepted a core/],
    ["refuses F entry when core.json changed since V1.5", async (ctx: PipelineContext, s: StateJson) => { s.verify!.core_sha256 = createHash("sha256").update("{\"a\":1}").digest("hex"); await writeCore(ctx, "{\"a\":2}"); }, /core\.json changed since V1\.5 accepted it/],
    ["admits F entry when the core on disk is the one V1.5 accepted", async (ctx: PipelineContext, s: StateJson) => { s.verify!.core_sha256 = await writeCore(ctx, "{\"qid\":\"verify_user_paper\"}"); }, null],
  ] as const)("%s", async (_what, setup, refusal) => {
    const ctx = await verifyCtx();
    const state = verifyState();
    await setup(ctx, state);
    if (refusal) await expect(assertFStageEntryCoherence(ctx, state, "1")).rejects.toThrow(refusal);
    else await expect(assertFStageEntryCoherence(ctx, state, "1")).resolves.toBeUndefined();
  });
});

describe("recordProofReviewOutcome — verify mode", () => {
  it("records a finding for a reportable escalation route, keyed to the node, a Lean-side obj_id, or the run", () => {
    const state = verifyState();
    recordProofReviewOutcome(state, {
      status: "escalate",
      route: "fix-source",
      phase: "3",
      reason: "lem:aux-bound as stated is not what the proof uses",
    });
    expect(state.verify!.findings).toHaveLength(1);
    expect(state.verify!.findings[0]).toMatchObject({
      node: "lem:aux-bound",
      stage: "F3",
      kind: "unresolved",
      witness: null,
    });
    expect(state.stage_completed).toBe("2");
    for (const [reason, node] of [
      ["T-1 as stated is not what the proof establishes", "T-1"],
      ["lem:aux rests on T-1", "lem:aux"],
      ["no object is named here", "run"],
    ] as const) {
      const s = verifyState();
      recordProofReviewOutcome(s, { status: "escalate", route: "fix-source", phase: "3", reason });
      expect(s.verify!.findings[0]!.node, reason).toBe(node);
    }
    const r = verifyState();
    recordProofReviewOutcome(r, { status: "escalate", route: "bank-partial", reason: "out of budget" });
    expect(r.verify!.findings[0]).toMatchObject({ node: "run", stage: "F2.5" });
  });

  it("records nothing for a workflow route", () => {
    const state = verifyState();
    recordProofReviewOutcome(state, { status: "escalate", route: "hint", phase: "3", reason: "needs a hint" });
    recordProofReviewOutcome(state, { status: "escalate", route: "build-substrate", reason: "needs infra" });
    recordProofReviewOutcome(state, { status: "escalate", route: "redo-math", reason: "witnessed" });
    expect(state.verify!.findings).toHaveLength(0);
  });

  it("an escalation on a paper statement leaves a pending V1 patch-mode receipt; the flag keeps kind and node; a Lean-side one leaves none", () => {
    const state = verifyState();
    const reason = "[statement-wrong] Specify whether each CDF is invertible on all of ℝ; the frozen wording permits both readings.";
    recordProofReviewOutcome(state, { status: "escalate", route: "fix-source", phase: "2.5", reason, kind: "statement-wrong", obj_id: "lem:twoforms" });
    expect(state.flags.proof_review_escalation_pending).toEqual({ route: "fix-source", reason, kind: "statement-wrong", obj_id: "lem:twoforms", phase: "2.5" });
    expect(state.verify!.cross_stage_rewind).toMatchObject({ status: "pending", stage: "F2.5", route: "fix-source", axis: "clarify", target: "lem:twoforms", detail: reason });
    for (const outcome of [
      { status: "escalate" as const, route: "fix-source" as const, phase: "3" as const, reason: "[note-wrong] the note over-tags", kind: "note-wrong", obj_id: "lem:x" },
      { status: "escalate" as const, route: "unclear" as const, phase: "2.5" as const, reason: "[unadjudicable] no Lean to judge", kind: "unadjudicable", obj_id: "lem:x" },
      { status: "escalate" as const, route: "fix-source" as const, phase: "3" as const, reason: "filler LAUNDERED 1 forbidden proof-cheat token(s)" },
    ]) {
      const state = verifyState();
      recordProofReviewOutcome(state, outcome);
      expect(state.verify!.cross_stage_rewind, outcome.reason).toBeUndefined();
    }
  });

  it("a completed loop retracts the F-stage unresolved findings it left behind", () => {
    const state = verifyState();
    recordProofReviewOutcome(state, {
      status: "escalate", route: "unclear", phase: "2.5", reason: "thm:main: cannot close step 2",
    });
    recordVerifyFinding(state, {
      node: "lem:aux", stage: "F2.5", kind: "refuted", detail: "witnessed", witness: "n = 2",
    });
    expect(state.verify!.findings).toHaveLength(2);
    // The loop later converges: an escalation it resolved must not pin the row to `unresolved`.
    recordProofReviewOutcome(state, { status: "completed" });
    expect(state.flags.proof_review_escalation_pending).toBeNull();
    expect(state.verify!.findings.map((f) => f.kind)).toEqual(["refuted"]);
  });
});

describe("adjudicateRedoMathRewind — verify mode never rewinds", () => {
  const ctx = (): PipelineContext => ({
    repoRoot: path.join(path.sep, "nonexistent"),
    toolkit: tk(path.join(path.sep, "nonexistent")),
    qid: QID,
    resume: true,
    dryRun: true,
  });

  it.each([
    ["counterexample", "take n = 2, p = 1/2", "refuted", "PAPER STEP REFUTED"],
    ["hyps-insufficient", "no bound on the second moment", "unresolved", "PAPER STEP UNRESOLVED"],
  ] as const)("a %s witness is recorded as a finding; the cursor never moves", async (type, detail, kind, banner) => {
    const state = verifyState();
    state.stage_completed = "2.5";
    const result = await adjudicateRedoMathRewind({
      ctx: ctx(),
      state,
      rm: { obj_id: "aux_RateBound", witness: { type, detail }, dependents: ["thm:main"] },
      reason: "the rate step is false",
    });
    expect(result).toMatchObject({ stage: "2.5", status: "checkpoint", completedStage: "2" });
    expect(result.message).toContain(banner);
    expect(state.stage_completed).toBe("2.5");
    expect(Object.keys(state.flags).filter((k) => k.startsWith("redo_math"))).toEqual([]);
    expect(state.verify!.findings).toEqual([
      expect.objectContaining({ node: "aux_RateBound", stage: "F2.5", kind, detail: "the rate step is false", ...(kind === "refuted" ? { witness: detail } : {}) }),
    ]);
  });
});

/**
 * The cited-leaf question, settled with evidence rather than with either side's claim.
 *
 * A verify run's headline routinely rests on a result the paper only CITES. The fixtures below
 * are what F4 leaves behind for such a leaf whose source cannot be checked (an unpublished
 * manuscript: no arXiv, no verbatim text to match), and the assertions record exactly what the
 * F5 delivery audit then does with them.
 */
describe("cited leaves in verify mode", () => {
  const citedCore: Core = {
    qid: QID,
    symbols: [],
    assumptions: [],
    definitions: [],
    statements: [{
      id: "lem:cited",
      kind: "lemma",
      statement: "The cited moment bound holds for the weighted average.",
      depends_on: [],
      status: "cited",
      source: {
        cite: "unpublished2019",
        locator: "Lemma 4",
        verbatim_statement: "The cited moment bound holds for the weighted average.",
      },
    }],
    target_estimand: "tau",
    bibliography: [{ key: "unpublished2019", citation: "A. Author (2019), unpublished manuscript." }],
  };
  const citedPlan = PlanSchema.parse({
    qid: QID,
    env: [],
    nodes: {
      "lem:cited": {
        lean_kind: "assumption",
        lean_name: "citedMomentBound",
        disposition: "define-local",
        gate: true,
        gate_class: "cited",
        source: "cite:unpublished2019",
      },
    },
    citations: [{
      id: "cite:unpublished2019",
      title: "Unpublished manuscript",
      authors: "A. Author",
      year: 2019,
      locator: "Lemma 4",
      verbatim_statement: "The cited moment bound holds for the weighted average.",
    }],
    feasibility: "formalizable-now",
  });
  const citedGraph = {
    qid: QID,
    nodes: [{
      id: "lem:cited",
      kind: "gate" as const,
      provenance: "from-note" as const,
      nl: { statement: "cited moment bound", tex_anchor: "", frozen: true },
      lean: { decl_name: "citedMomentBound", file: "Basic.lean" },
      review: { status: "matched" as const, passed_hash: "h" },
      proof: { state: "complete" as const, sorry_count: 0 },
      gate: { gate_class: "cited" as const, source: "cite:unpublished2019" },
    }],
    edges: [],
  };
  const leanEvidence = { "lem:cited": "current-lean-digest" };
  const hash = citedEvidenceHash(citedCore, citedPlan, citedGraph, "lem:cited", leanEvidence["lem:cited"]);
  const receipt = (
    reviewer: "codex" | "claude",
    check_status: CitedReviewReceipt["check_status"],
  ): CitedReviewReceipt => ({
    node_id: "lem:cited",
    reviewer,
    check_status,
    cite_id: "cite:unpublished2019",
    locator: "Lemma 4",
    evidence_hash: hash,
  });

  it("an unverifiable source, a missing receipt and `cited-underspecified` are notes, never blocks", () => {
    expect(auditCitedReview({
      core: citedCore, plan: citedPlan, graph: citedGraph, leanEvidence,
      receipts: [receipt("codex", "cited-source-unverifiable"), receipt("claude", "cited-source-unverifiable")],
    })).toEqual([]);
    const findings = auditCitedReview({
      core: citedCore, plan: citedPlan, graph: citedGraph, leanEvidence, receipts: [],
    });
    expect(findings.map((f) => f.message)).toEqual([
      "expected exactly one codex cited-source receipt, found 0",
      "expected exactly one claude cited-source receipt, found 0",
    ]);
    const { blocking, notes } = splitCitedFindingsForVerify(findings);
    expect(blocking).toEqual([]);
    expect(notes).toHaveLength(2);
    const mixed = splitCitedFindingsForVerify(auditCitedReview({
      core: citedCore, plan: citedPlan, graph: citedGraph, leanEvidence,
      receipts: [receipt("codex", "cited-underspecified"), receipt("claude", "cited-mismatch")],
    }));
    expect(mixed.notes.map((f) => f.message)).toEqual(["codex cited-source verdict is cited-underspecified"]);
    expect(mixed.blocking.map((f) => f.message)).toEqual(["claude cited-source verdict is cited-mismatch"]);
  });

  it("an unknown status, `cited-mismatch` and an inconsistent artifact block (allow-list, never downgraded)", () => {
    for (const status of ["cited-partial", "cited-mismatch"]) {
      const { blocking, notes } = splitCitedFindingsForVerify(auditCitedReview({
        core: citedCore, plan: citedPlan, graph: citedGraph, leanEvidence,
        receipts: [receipt("codex", status), receipt("claude", status)],
      }));
      expect(notes, status).toEqual([]);
      expect(blocking.map((f) => f.message), status).toEqual([
        `codex cited-source verdict is ${status}`,
        `claude cited-source verdict is ${status}`,
      ]);
    }
    const stale = splitCitedFindingsForVerify(auditCitedReview({
      core: citedCore, plan: citedPlan, graph: citedGraph, leanEvidence,
      receipts: [
        { ...receipt("codex", "cited-source-unverifiable"), evidence_hash: "stale" },
        receipt("claude", "cited-source-unverifiable"),
      ],
    }));
    expect(stale.notes).toEqual([]);
    expect(stale.blocking.map((f) => f.message)).toEqual(["codex cited receipt is stale for the current source interface"]);
    const emptyPlan = PlanSchema.parse({
      qid: QID, env: [], nodes: {}, citations: [], feasibility: "formalizable-now",
    });
    const orphan = splitCitedFindingsForVerify(auditCitedReview({
      core: citedCore, plan: emptyPlan, graph: citedGraph, leanEvidence, receipts: [],
    }));
    expect(orphan.notes).toEqual([]);
    expect(orphan.blocking.map((f) => f.message)).toEqual([
      "delivered cited graph node is absent from the authoritative plan cited inventory",
    ]);
  });
});

describe("F4 cited match gate — verify mode", () => {
  /** A one-theorem graph the loop can converge on immediately. */
  function provedGraph() {
    let g = createEmptyGraph(QID);
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
    g = { ...g, nodes: g.nodes.map((n) => (n.id === "t1" ? { ...n, lean: { decl_name: "t1_thm", file: "T1.lean" } } : n)) };
    g = setProof(g, "t1", "complete", 0);
    return setNodeReview(g, "t1", "matched", "h");
  }

  const underspecified: SubstrateGate = {
    name: "citedMomentBound",
    statement: "The cited moment bound holds.",
    classical_fact: "moment bound of the cited manuscript",
    missing_infra: "none — imported from the literature",
    gate_class: "cited",
    source: { cite_id: "cite:unpublished2019", locator: "Lemma 4" },
    check_status: "cited-underspecified",
  };

  async function runWith(
    qid: string,
    state: StateJson,
    gates: SubstrateGate[] = [underspecified],
    repoRoot?: string,
  ): Promise<Awaited<ReturnType<typeof runProofReviewLoop>>> {
    repoRoot ??= await mkdtemp(path.join(os.tmpdir(), "causalsmith-verify-f4-"));
    // The loop re-loads state from disk to persist the F4 receipts; it must find this run's own.
    await saveState(repoRoot, qid, state);
    const g = provedGraph();
    return runProofReviewLoop({
      ctx: { repoRoot, qid },
      deps: {} as never,
      state,
      buildCheck: async () => ({ ok: true, errors: "" }),
      refresh: async () => ({ graph: g, skeleton: graphDerivedSkeleton(g), dirty: ["t1"], hashes: { t1: "h" } }),
      review: async (s) => ({
        graph: s.graph, ok: true, escalate: null, blocking: [], substrateGates: gates,
      }),
      fill: async (graph) => ({ graph, escalate: null, summary: "" }),
    });
  }

  it("verify mode reports it and converges — the paper may rest on a cited result", async () => {
    const state = verifyState();
    state.stage_completed = "2";
    const outcome = await runWith(QID, state);
    expect(outcome.status).toBe("completed");
    expect(state.verify!.findings).toEqual([
      expect.objectContaining({
        node: "citedMomentBound",
        stage: "F4",
        kind: "note",
        witness: null,
      }),
    ]);
    expect(state.verify!.findings[0]!.detail).toContain("cite:unpublished2019");
  });

  const gated: SubstrateGate = {
    name: "hPinsker", statement: "KL ≥ 2 TV²", classical_fact: "Pinsker's inequality",
    missing_infra: "Pinsker in the base library", gate_class: "gated",
  };

  it("records reviewer-flagged gates per run: gated always, cited only once the match passes", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "causalsmith-verify-gates-"));
    const state = verifyState();
    state.stage_completed = "2";
    expect((await runWith(QID, state, [gated, underspecified], root)).status).toBe("completed");
    const file = runGatesPath(root, QID);
    expect(file).toBe(path.join(root, "runs", QID, "formalization", "gates.json"));
    const rows = JSON.parse(await readFile(file, "utf8")).gates;
    expect(rows.map((g: SubstrateGate) => [g.name, g.gate_class])).toEqual([["hPinsker", "gated"], ["citedMomentBound", "cited"]]);
    expect(rows[0]).toMatchObject({ stage: "F4", classical_fact: "Pinsker's inequality" });

    // A cited MISMATCH halts the run: its gated rows are still owed, the cited row is not written.
    const root2 = await mkdtemp(path.join(os.tmpdir(), "causalsmith-verify-gates-"));
    const state2 = verifyState();
    state2.stage_completed = "2";
    const mismatch = { ...underspecified, check_status: "cited-mismatch" as const };
    expect((await runWith(QID, state2, [gated, mismatch], root2)).status).toBe("escalate");
    const rows2 = JSON.parse(await readFile(runGatesPath(root2, QID), "utf8")).gates;
    expect(rows2.map((g: SubstrateGate) => g.name)).toEqual(["hPinsker"]);
  });
});
