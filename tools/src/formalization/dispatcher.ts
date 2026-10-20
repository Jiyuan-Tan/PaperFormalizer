// Formalization dispatcher. The graph-driven proof-review loop is the sole proof path:
// it runs in the F2.5 slot and owns the statement gate, proof fill, unused-hyp lint, and
// dual-model convergence. It logs F2.5/F3/F3.5/F4 at their real phase boundaries and advances
// directly to F5.

import type { PipelineContext, Stage, StageResult, StateJson } from "../types.js";
import { artifactPaths, type StageDeps } from "../pipeline_support.js";
import { coreJsonPath } from "../core/core_io.js";
import { runProofReviewLoop, scaffoldFixable, writeRunBarrel, type LoopOutcome } from "./proof_review_loop.js";

/** How many times one F2.5–F4 entry sends a phase-3 drift back through the statement gate. */
const PHASE3_DRIFT_REENTRIES = 3;

/** A phase-3 (proof-fill) reviewer escalation the statement gate can reroute to F2: a scaffold-fixable
 * kind on a named target. */
export function phase3Drift(o: LoopOutcome): boolean {
  return o.status === "escalate" && o.phase === "3" && o.route === "unclear" && !!o.kind && scaffoldFixable(o.kind) && !!o.obj_id;
}
import * as leanLspServer from "../shared/lean_lsp_server.js";
import { clearSharedLeanLspUrl, setSharedLeanLspUrl, sharedLeanLspUrl } from "../shared/shared_lean_lsp_env.js";
import { runStage1 } from "./stage1.js";
import { runStage1_5 } from "./stage1_5.js";
import { runStage2 } from "./stage2.js";
import {
  F2_REVISION_TARGETS_HEADER,
  revisionTargetsFromRedirect,
} from "./f2_revision_context.js";
import { runStage5 } from "./stage5.js";
import { clearFormalizationUnresolved, recordVerifyFinding } from "../verify/findings.js";
import { recordProofReviewRewind } from "../verify/cross_stage_rewind.js";

const PROOF_REVIEW_BYPASS_STAGES = new Set<Stage>(["3", "3.5", "4", "5"]);

/**
 * Persist the proof-review boundary outcome on the shared state object. An
 * escalation immediately rewinds the durable completion cursor to F2; only a
 * genuine loop completion clears the unresolved marker.
 */
/** Escalation routes that mean "this paper step did not close", as opposed to a workflow step
 *  (`hint`, `build-substrate`) or the witnessed refutation `redo-math` owns. */
const VERIFY_REPORTABLE_ROUTES = new Set(["fix-source", "unclear", "bank-partial"]);

/** First node id mentioned in a reviewer's free text, else `"run"`. Two id spaces occur there:
 *  core ids (`thm:main`, `ass:overlap`) and the graph/crosswalk `obj_id`s the Lean side is keyed
 *  by (`T-1`, `L-2`, `D-3`, `A-1`, `P-2`). Both are resolvable — the V6 report maps an obj_id
 *  through the crosswalk — so matching only the first shape degraded every Lean-side escalation
 *  to a run-level finding that names no result. */
const NODE_ID_RE = /\b(?:thm|lem|prop|def|ass):[a-z0-9-]+|\b[TLDAP]-\d+\b/;

export function recordProofReviewOutcome(state: StateJson, outcome: LoopOutcome): void {
  if (outcome.status === "escalate") {
    state.flags.proof_review_escalation_pending = {
      route: outcome.route,
      reason: outcome.reason,
      ...(outcome.kind ? { kind: outcome.kind } : {}),
      ...(outcome.obj_id ? { obj_id: outcome.obj_id } : {}),
      phase: outcome.phase ?? "2.5",
      ...(outcome.batch && outcome.batch.length > 1 ? { batch: outcome.batch } : {}),
    };
    state.stage_completed = "2";
    // An escalation the loop could not resolve is a REPORTABLE observation about the user's
    // paper, not just a workflow halt — V6 lists it as `unresolved`.
    // A batch (several paper-statement findings of one review pass) records one per finding.
    for (const e of outcome.batch && outcome.batch.length > 1 ? outcome.batch : [outcome]) {
      if (!VERIFY_REPORTABLE_ROUTES.has(e.route)) continue;
      recordVerifyFinding(state, {
        node: NODE_ID_RE.exec(e.reason)?.[0] ?? "run",
        stage: `F${outcome.phase ?? "2.5"}`,
        kind: "unresolved",
        detail: e.reason,
        witness: null,
      });
    }
    // A defect in a PAPER statement (`statement-wrong`, or a statement whose wording is unclear)
    // leaves a pending receipt the verify runner proposes to the orchestrator as a V1 patch round
    // (`verify/cross_stage_rewind.ts`); anything else halts for the orchestrator as before.
    recordProofReviewRewind(state);
    return;
  }
  state.flags.proof_review_escalation_pending = null;
  // The loop COMPLETED, which it can only do with every node closed. Retract the
  // F-stage `unresolved` findings earlier escalations left behind — findings are otherwise
  // append-only, so one transient F2.5 bounce would otherwise pin the result to `unresolved`
  // in the report even though the proof later went through. Refutations and notes stay.
  clearFormalizationUnresolved(state);
}

/**
 * Fail closed against stale/manual stage pointers after a proof-review
 * escalation. `advance:false` is essential for F5: it prevents pipeline.ts
 * from treating this checkpoint as a completed F5 and firing the post-F5 hook.
 */
export function unresolvedProofReviewGuard(state: StateJson, stage: Stage): StageResult | null {
  const pending = state.flags.proof_review_escalation_pending;
  if (!pending || !PROOF_REVIEW_BYPASS_STAGES.has(stage)) return null;
  state.stage_completed = "2";
  return {
    stage,
    status: "checkpoint",
    advance: false,
    completedStage: "2",
    message:
      `PROOF-REVIEW ESCALATION UNRESOLVED [${pending.route}]: cannot enter F${stage}; ` +
      `rewound to completedStage F2 so resume re-enters F2.5. ${pending.reason}`,
  };
}

export async function runFormalizationStage(args: {
  ctx: PipelineContext;
  state: StateJson;
  stage: Stage;
  deps: StageDeps;
}): Promise<StageResult | null> {
  const proofReviewGuard = unresolvedProofReviewGuard(args.state, args.stage);
  if (proofReviewGuard) return proofReviewGuard;
  switch (args.stage) {
    case "1":
      return runStage1({ ctx: args.ctx, state: args.state, deps: args.deps });
    case "1.5":
      return runStage1_5({ ctx: args.ctx, state: args.state, deps: args.deps });
    case "2":
      return runStage2({ ctx: args.ctx, state: args.state, deps: args.deps });
    case "2.5":
      // The proof-review loop runs here and owns the entire proof/review path: F3, F3.5 and F4
      // are its phases (it completes through "4"), so a cursor set on one of them by hand is
      // unhandled and fails loud in `liveStageHandler`.
      return runProofReviewLoopStage(args);
    case "5":
      return runStage5({ ctx: args.ctx, state: args.state, deps: args.deps });
    default:
      return null;
  }
}

/** A pre-set `flags.scaffold_redirect` (hand-injected, or left by an interrupted run)
 *  must be consumed by an F2 pass BEFORE the proof-review loop reviews the stale
 *  scaffold — a plain `--resume` at stage_completed="2" otherwise never applies it.
 *  Returns null to proceed into the loop, or the non-completed F2 result (fail closed).
 *  `scaffoldFn` is injectable for tests. */
export async function consumePendingScaffoldRedirect(
  args: { ctx: PipelineContext; state: StateJson; deps: StageDeps },
  scaffoldFn: typeof runStage2 = runStage2,
): Promise<StageResult | null> {
  if (!args.state.flags.scaffold_redirect) return null;
  console.warn("[F] pending flags.scaffold_redirect found at F2.5 entry — running an F2 pass to consume it before the review loop.");
  const result = await scaffoldFn({
    ctx: args.ctx,
    state: args.state,
    deps: args.deps,
    revisionTargets: revisionTargetsFromRedirect(args.state.flags.scaffold_redirect),
  });
  if (result.status !== "completed") return result;
  return null; // runStage2 self-clears the flag on completion
}

/** The witness + blast-radius the proof-review loop reports for a witnessed refutation. */
export interface RedoMathProposal {
  /** GRAPH node id of the refuted claim. On the redo-math path this is ALWAYS an
   *  agent-introduced Lean decl id (e.g. `aux_BanditLaw`) — `from_core.ts` stamps
   *  `provenance:"from-note"` on every node built from the core, and the loop takes this
   *  path only when `provenance !== "from-note"` — so it is NEVER a `thm:`/`lem:` core id. */
  obj_id: string;
  witness: { type: string; detail: string };
  /** Transitive graph dependents of `obj_id` (mixed id space: Lean aux ids AND core ids). */
  dependents: string[];
}

/**
 * Adjudicate a witnessed F3 refutation. The refuted step belongs to the USER'S paper and the
 * pipeline never re-derives the paper's mathematics, so the witness is recorded as a report
 * finding and the run halts at a checkpoint. Performs no other state mutation and reads no
 * core, so the branch is total.
 */
export async function adjudicateRedoMathRewind(args: {
  ctx: PipelineContext;
  state: StateJson;
  rm: RedoMathProposal;
  reason: string;
}): Promise<StageResult> {
  const { rm } = args;
  const w0 = `witness[${rm.witness.type}]: ${rm.witness.detail}`;
  // `counterexample` is the only witness type that exhibits a concrete failure of the
  // statement; `hyps-insufficient` / `hyps-contradictory` say the formalization could not be
  // closed as stated, which is not a refutation of the paper.
  const refuted = rm.witness.type === "counterexample";
  recordVerifyFinding(args.state, {
    node: rm.obj_id,
    stage: "F2.5",
    kind: refuted ? "refuted" : "unresolved",
    detail: args.reason,
    witness: rm.witness.detail,
  });
  return {
    stage: "2.5", status: "checkpoint", completedStage: "2",
    message: `PAPER STEP ${refuted ? "REFUTED" : "UNRESOLVED"} [${rm.obj_id}] `
      + `(the paper's mathematics is never re-derived, so this is recorded as a `
      + `${refuted ? "refuted" : "unresolved"} finding for the report; `
      + `dependents: ${rm.dependents.join(", ") || "none"}; ${w0}): ${args.reason}`,
  };
}

/**
 * Run the graph-driven proof-review loop in the F2.5 slot. On convergence it completes through
 * stage "4" (so the pipeline advances directly to F5); on escalation it checkpoints with the route +
 * reason for the orchestrating agent to act on (build-substrate / hint / fix-source / unclear /
 * bank-partial) and `--resume`.
 */
async function runProofReviewLoopStage(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<StageResult> {
  const pendingRedirect = await consumePendingScaffoldRedirect(args);
  if (pendingRedirect) return pendingRedirect;
  const paths = artifactPaths(args.ctx, args.state);
  // Boot ONE shared streamable-HTTP `lean-lsp-mcp` (= one `lake serve`) for the whole proof
  // loop so the reviewer + per-target fillers reuse a single WARM server instead of each codex
  // call cold-starting its own stdio lean-lsp. On a loaded host a fresh per-call cold-start
  // re-elaborates the import closure for minutes, blows past codex's lean-lsp MCP timeout, and
  // the per-call servers proliferate. Only boot when a
  // launcher hasn't already exported a URL; non-fatal on failure (falls back to per-process stdio
  // lean-lsp — correct, just slower). `leanLspCodexFlags` (codex.ts) reads the env var per call.
  let shared: Awaited<ReturnType<typeof leanLspServer.startSharedLeanLsp>> | null = null;
  const ownsSharedLeanLsp = !sharedLeanLspUrl();
  if (ownsSharedLeanLsp) {
    try {
      shared = await leanLspServer.startSharedLeanLsp(args.ctx.repoRoot);
      setSharedLeanLspUrl(shared.url);
    } catch {
      shared = null;
    }
  }
  try {
  // Refresh the per-run barrel at F-stage entry so the whole run stays ONE buildable target.
  // Paper modules are unreachable from the library barrels, so the DEFAULT lake target skips
  // them and reports green on stale oleans. Best-effort — never sink a run.
  try {
    const barrel = await writeRunBarrel(
      args.ctx.repoRoot,
      paths.leanDir,
    );
    if (barrel) console.warn(`[F] run barrel refreshed: ${barrel}`);
  } catch (e) {
    console.warn(`[F] run-barrel refresh failed (non-fatal): ${e instanceof Error ? e.message : String(e)}`);
  }

  /** F2 sent the plan back to F1 from inside the loop (`planBackToF1`): the stage's result. */
  let planRewind: StageResult | null = null;
  const runLoop = () => runProofReviewLoop({
    ctx: { repoRoot: args.ctx.repoRoot, qid: args.ctx.qid, toolkit: args.ctx.toolkit },
    deps: { runCodex: args.deps.runCodex, runClaude: args.deps.runClaude },
    // The SHARED state object. `pipeline.ts` loads state once and re-saves this same object after
    // the stage, so the loop must mutate IT — a disk-only write is clobbered (last-writer-wins),
    // which silently made the iteration caps inert and left `cited_checks: []`.
    state: args.state,
    formalizationDir: paths.formalizationDir,
    leanDir: paths.leanDir,
    // Advisory context the filler/reviewer read for per-node proof_tex + statements:
    // the typed core (it
    // carries each statement's proof_tex). The load-bearing graph comes from graph.json.
    corePath: coreJsonPath(args.ctx),
    // Phase-B proof-fill directive: a load-bearing PROOF hint the orchestrator sets in
    // `state.flags` before `--resume` when the fill loop is stuck. Persists on state.flags
    // until the orchestrator clears it, so it steers every filler call this run.
    fillerDirective: args.state.flags.f3_filler_directive ?? null,
    // Phase-A re-scaffold seam: drive F2 in revise-mode via a scaffold_redirect directive (it
    // patches the named decls in place, preserving proofs via carry-over and self-clears the flag).
    scaffold: async ({ redirect, targets }) => {
      // NOT JSON.stringify: symbol obj_ids legitimately contain TeX
      // (`sym:\(\mathcal H\)`), and JSON doubling their backslashes made the
      // scaffolder grep for `\\(\\mathcal H\\)` — matching nothing in the Lean
      // tree, so the cluster was never found and the reroute burned its cap.
      args.state.flags.scaffold_redirect = [
        redirect,
        targets.length
          ? `${F2_REVISION_TARGETS_HEADER}\n${targets.map((t) => `- ${t}`).join("\n")}`
          : "",
      ].filter(Boolean).join("\n\n");
      const result = await runStage2({
        ctx: args.ctx,
        state: args.state,
        deps: args.deps,
        revisionTargets: targets,
      });
      if (result.status === "rewound") planRewind = result;
      if (result.status !== "completed") {
        // why: a failed F2 scaffold redirect must reject so the proof-review loop blocks fail-closed.
        throw new Error(`Stage 2 scaffold redirect did not complete (${result.status}): ${result.message}`);
      }
    },
  });
  let outcome = await runLoop();
  // No escalation for the orchestrator: the run goes on at the F1.5 pre-lint.
  if (planRewind) return planRewind;
  // A Lean-side drift the reviewer flags while proofs are filled (phase 3) goes back through the
  // statement gate, which reroutes it to F2 with the reviewer's note — as a resume would — instead of
  // stopping for the orchestrator. Bounded here and by the gate's own caps (per-node strikes, rounds).
  for (let again = 0; again < PHASE3_DRIFT_REENTRIES && phase3Drift(outcome); again++) {
    console.warn(`[F] phase-3 drift on ${outcome.status === "escalate" ? outcome.obj_id ?? "a target" : "a target"} (${outcome.status === "escalate" ? outcome.kind : ""}) — back through the statement gate (re-entry ${again + 1}/${PHASE3_DRIFT_REENTRIES})`);
    outcome = await runLoop();
    if (planRewind) return planRewind;
  }
  recordProofReviewOutcome(args.state, outcome);
  // A witnessed `statement-wrong`: record it as a finding and checkpoint (the loop only proposed it).
  if (outcome.status === "escalate" && outcome.route === "redo-math" && outcome.redoMath) {
    return adjudicateRedoMathRewind({
      ctx: args.ctx,
      state: args.state,
      rm: outcome.redoMath,
      reason: outcome.reason,
    });
  }
  if (outcome.status === "completed") {
    return {
      stage: "2.5",
      status: "completed",
      completedStage: "4",
      message: "proof-review loop converged (statement gate, proof fill, lint, and convergence review)",
    };
  }
  return {
    // The combined loop enters through F2.5 but may halt in F3/F3.5/F4. Preserve that
    // logical origin so pipeline.jsonl does not mislabel every escalation as F2.5.
    stage: outcome.phase ?? "2.5",
    status: "checkpoint",
    // The loop did NOT complete (it escalated). Record `completedStage: "2"` so a later
    // `--resume` RE-ENTERS the proof-review loop (next stage after "2" is "2.5") instead of
    // skipping it: with no `completedStage`, `pipeline.ts` would set `stage_completed = "2.5"`,
    // and resume would treat the loop as done — running 3/3.5/4 as no-ops straight to F5,
    // so the orchestrator's post-escalation fix never gets re-proved. "2" does NOT re-run F2
    // (STAGE_ORDER: … "2", "2.5", …); Phase A re-review is incremental (cached-matched).
    completedStage: "2",
    message:
      `PROOF-REVIEW LOOP ESCALATION [${outcome.route}]: ${outcome.reason}` +
      (args.state.verify?.cross_stage_rewind?.status === "pending" &&
      (args.state.verify.cross_stage_rewind.targets ?? [{ reason: args.state.verify.cross_stage_rewind.detail }]).some((t) => t.reason === outcome.reason)
        ? ` — ${(outcome.batch?.length ?? 1) > 1 ? `${outcome.batch!.length} defects in paper statements (one review pass)` : "a defect in a paper statement"}: the verify runner proposes a V1 patch round for the orchestrator to approve or reject.`
        : ""),
  };
  } finally {
    // Tear down the shared server we booted (a launcher-provided one is owned by the launcher).
    if (ownsSharedLeanLsp && shared) {
      try {
        await shared.stop();
      } catch {
        /* best-effort teardown */
      }
      clearSharedLeanLspUrl();
    }
  }
}
