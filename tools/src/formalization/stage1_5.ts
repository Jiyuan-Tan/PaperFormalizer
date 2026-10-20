// Formalization Stage 1.5 (F1.5) — the REUSE-SOUNDNESS review boundary.
//
// The deterministic plan gate (plan_gate.ts) owns one-to-one coverage / kind /
// member / hyp-closure / reuse-existence / module checks. F1.5 runs
// that gate as a pre-lint (a violation goes straight back to F1, no LLM spent),
// then an LLM reviews only the genuinely hard judgment: does each chosen reuse decl
// actually type-fit at the right abstraction level, and is each define-local
// justified.

import { laterStageEverRan } from "../shared/resume_mode.js";
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import type { PipelineContext, StageResult, StateJson } from "../types.js";
import type { ReviewResult } from "../judgment.js";
import { type StageDeps, artifactPaths, readRequired } from "../pipeline_support.js";
import { reviewWithCodex } from "./review_codex.js";
import { runReviewBoundary } from "../shared/review_boundary.js";
import { runStage1 } from "./stage1.js";
import { coreJsonPath, formalizationView, parseTypedCore } from "../core/core_io.js";
import { logPlanGateNotes } from "../formalization/plan/plan_gate.js";
import { planGateOnDisk } from "../formalization/plan/gate_run.js";
import { parseJsonWithEscapeRepair } from "../shared/codex_json.js";
import { PLAN_REVIEW_ROUNDS_MAX, addPlanReviewRounds, planReviewRounds, resetFormalizationLoopCounters } from "./loop_limits.js";
import { namedPlanEntries } from "./revise_scope.js";
import { PlanSchema } from "./plan/schema.js";
import type { Core } from "../core/schema.js";
import { GENERAL_REVIEW_HALT_EXITS } from "../cap_gates.js";

/** Run the deterministic plan gate over the just-written plan. Returns a synthetic
 *  `revise` verdict (routing F1 to fix the mechanical violations) when it fails, or
 *  `null` when the plan is gate-clean. core.json is REQUIRED (throws via
 *  readRequired if missing/unparseable); a missing plan.json still routes back to
 *  F1 as a synthetic revise. */
export async function planGatePrelint(
  args: { ctx: PipelineContext; state: StateJson },
  planPath: string,
): Promise<ReviewResult | null> {
  const corePath = coreJsonPath(args.ctx);
  // The deterministic plan gate is the structural hard-fail; silently skipping it
  // when core.json is missing/unparseable let a plan advance ungated. Fail loud.
  const coreText = await readRequired(corePath, "F1.5 plan gate");
  let core;
  try {
    core = formalizationView(parseTypedCore(coreText, `F1.5 plan gate: core.json at ${corePath}`));
  } catch (err) {
    throw new Error(
      `F1.5 plan gate: core.json at ${corePath} failed to parse/validate: ${err instanceof Error ? err.message : String(err)} (a core from before the typed core? rebuild it with --from-stage V1)`,
    );
  }
  // A core exists but F1 wrote no plan → route back to F1 to author it.
  if (!existsSync(planPath)) {
    return {
      status: "revise",
      classification: "plan-gate",
      perItemFindings: [{ label: "plan.json", verdict: "FLAG-missing", one_line: `F1 did not write a plan at ${planPath}` }],
      verbatim_critique: `No plan.json found at ${planPath}. Author the formalization plan — one node entry per core node (assumptions ∪ definitions ∪ statements), plus the env S-block(s).`,
    };
  }
  let planObj: unknown;
  try {
    planObj = parseJsonWithEscapeRepair(await readFile(planPath, "utf8"));
  } catch (err) {
    return {
      status: "revise",
      classification: "plan-gate",
      perItemFindings: [{ label: "plan.json", verdict: "FLAG-parse", one_line: String(err) }],
      verbatim_critique: "plan.json is not valid JSON; re-emit it as a single well-formed object.",
    };
  }
  // F1 ran this gate on the same plan and core just before: memoized, not run twice.
  const gate = planGateOnDisk(args.ctx, { planObj, coreText, core });
  logPlanGateNotes(gate.notes);
  if (gate.ok) return null;
  // Every hygiene violation is shown (one short line per entry): a plan that grew by accretion
  // is compacted in ONE revise round, not forty entries at a time.
  const hygiene = gate.violations.filter((v) => v.code === "P11");
  const shown = [...gate.violations.filter((v) => v.code !== "P11").slice(0, 40), ...hygiene];
  return {
    status: "revise",
    classification: "plan-gate",
    perItemFindings: shown.map((v) => ({ label: v.where, verdict: `FLAG-${v.code}`, one_line: v.message })),
    verbatim_critique:
      "The plan failed the deterministic gate (one-to-one coverage / kind / member / hyp-closure / reuse-existence / module / hygiene). Fix these mechanical violations in plan.json, keeping every core node mapped exactly once" +
      (hygiene.length > 0 ? `; fix ALL ${hygiene.length} P11 entries in this pass` : "") +
      ".",
  };
}

export async function runStage1_5(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
}): Promise<StageResult> {
  // F1 answered `blocked` inside this loop at the last entry: plan again first, with the review it
  // was correcting — the reviewer would only read the earlier plan, and could pass it.
  const blocked = args.state.flags.f1_blocked;
  if (blocked) {
    console.warn("[F] F1.5: F1 was blocked at the last entry — planning again before any review");
    // The orchestrator's directive answers the block: it starts the correction budget over, as on
    // every path a directive enters F1 by (F1 itself resets only when it carries no review).
    if (args.state.flags.f1_revise_directive) resetFormalizationLoopCounters(args.state);
    const again = await runStage1({ ...args, ...(blocked.review ? { priorReview: blocked.review as ReviewResult } : {}) });
    if (again.status !== "completed") return notReviewed(again);
  }
  // The orchestrator audits the FIRST plan. Once F2 has run on an approved plan, a re-plan is an
  // incremental revise (a rewind's nodes, a pin re-sync): a passing F1.5 review continues into F2
  // (`--stop-after F1.5` still stops for an audit).
  const approvedBefore = await laterStageEverRan(args.ctx, args.state, "1.5");
  if (approvedBefore) console.warn("[F] F1.5: a re-plan of an approved plan — a passing review continues into F2 (no checkpoint)");
  // The F1↔F1.5 correction budget is per formalization attempt, not per entry (`loop_limits.ts`):
  // this entry gets what is left of it, and the bounce past the budget halts for the orchestrator.
  const spent = planReviewRounds(args.state);
  const left = Math.max(0, PLAN_REVIEW_ROUNDS_MAX - spent);
  if (spent > 0) console.warn(`[F] F1.5: ${Math.min(spent, PLAN_REVIEW_ROUNDS_MAX)} of ${PLAN_REVIEW_ROUNDS_MAX} F1↔F1.5 correction round(s) spent in this formalization attempt`);
  return notReviewed(await runReviewBoundary({
    ctx: args.ctx,
    state: args.state,
    boundary: "stage_1.5_to_1",
    stage: "1.5",
    cap: left + 1,
    // The F1 plan + F1.5 reuse-soundness review settle into ONE consolidated
    // CKPT 1: a PASS halts here for the orchestrator's DEPTH + REUSE + fidelity
    // audit, rather than flowing straight into F2 scaffolding.
    ...(approvedBefore
      ? {}
      : { checkpointOnPass: "CONSOLIDATED CKPT 1 (F1 plan + F1.5 reuse-soundness passed). Audit DEPTH + REUSE + statement-vs-math fidelity before --resume into F2." }),
    // A bounce goes to F1 as it is: the reviewer's findings are the correction and the entries
    // they name the seeds of the scoped revise (`stage1ReviseSeeds`).
    producer: (prior, attempt) => runStage1({ ...args, priorReview: prior, attempt }),
    reviewer: async () => {
      const paths = artifactPaths(args.ctx, args.state);
      // 1. Deterministic gate pre-lint — must pass before the LLM runs.
      // 2. LLM reuse-soundness review over the gate-clean plan.
      const review = (await planGatePrelint(args, paths.plan)) ?? await reviewWithCodex(
        args,
        "stage1_5_reuse_soundness.txt",
        "1.5",
        "Review the plan's per-node reuse decisions for type-fit and abstraction level.",
        { replan: approvedBefore },
      );
      const halted = haltUnactionableReview(review, await planEntryNamer(args.ctx, paths.plan));
      return halted === review ? spendPlanReviewRound(args.state, review) : halted;
    },
  }));
}

/** A result that leaves the F1.5 slot records F1.5 complete only when it is the review's own (a
 *  pass, or the audit checkpoint after one). Whatever F1 returned through the slot — blocked, no
 *  usable plan — is no review: the stage does not advance, whatever that result says. */
export function notReviewed(result: StageResult): StageResult {
  return result.stage === "1.5" ? result : { ...result, advance: false };
}

/** One sentence on what the reviewer found, and that the orchestrator rules, for a halt message. */
function findingsSentence(review: Extract<ReviewResult, { status: "revise" | "reject" }>): string {
  const rows = review.perItemFindings.map((f) => `${f.label} [${f.verdict}] ${f.one_line}`).join("; ");
  return (
    `The reviewer found (${review.status}/${review.classification}): ${rows || "no item"} — ${review.verbatim_critique.trim().slice(0, 600) || "no critique"}. ` +
    `The orchestrator rules: ${GENERAL_REVIEW_HALT_EXITS}.`
  );
}

/** The plan entries a text names, read against the core and plan on disk (`namedPlanEntries`). */
async function planEntryNamer(ctx: PipelineContext, planPath: string): Promise<(texts: string[]) => string[]> {
  const corePath = coreJsonPath(ctx);
  const core: Core = formalizationView(parseTypedCore(await readRequired(corePath, "F1.5 review routing"), `F1.5 review routing: core.json at ${corePath}`));
  let plan = null;
  try {
    plan = PlanSchema.parse(parseJsonWithEscapeRepair(await readFile(planPath, "utf8")));
  } catch {
    // no readable plan: only core node ids count as entries
  }
  return (texts) => namedPlanEntries(core, plan, texts);
}

/** A bounce F1 cannot act on is turned into a halt (`halt_reason`), and F1 is not re-run: a
 *  `reject` (the reviewer roots the defect in the core, or could not be read), or a review that
 *  names no plan entry. The gate's own findings always go to F1. Pure; exported for tests. */
export function haltUnactionableReview(review: ReviewResult, namedEntries: (texts: string[]) => string[]): ReviewResult {
  if (review.status !== "revise" && review.status !== "reject") return review;
  const why =
    review.status === "reject"
      ? review.classification === "parse_failure"
        ? "the review could not be read (its raw text is the critique below)"
        : "the reviewer rejected the plan as not fixable by a re-plan — a defect in the paper's statement is recorded by the orchestrator (`discovery/patches.json`, `--from-stage V1.5`), nothing was recorded here"
      : review.classification !== "plan-gate" &&
          namedEntries([...review.perItemFindings.flatMap((f) => [f.label, f.one_line]), review.verbatim_critique]).length === 0
        ? "the review names no plan entry a re-plan could be applied to"
        : null;
  if (!why) return review;
  return { ...review, halt_reason: `F1.5 halted, F1 not re-run: ${why}. ${findingsSentence(review)}` } as ReviewResult;
}

/** A bounce (revise/reject) spends one round of the budget; the one past it is turned into a
 *  halt the boundary short-circuits on (`halt_reason`), so no producer retry runs on a plan the
 *  budget no longer covers. Pure apart from the counter; exported for tests. */
export function spendPlanReviewRound(state: Pick<StateJson, "flags">, review: ReviewResult): ReviewResult {
  if (review.status !== "revise" && review.status !== "reject") return review;
  addPlanReviewRounds(state, 1);
  const spent = planReviewRounds(state);
  if (spent <= PLAN_REVIEW_ROUNDS_MAX) return review;
  return {
    ...review,
    halt_reason:
      `F1↔F1.5 correction budget spent (all ${PLAN_REVIEW_ROUNDS_MAX} rounds of this formalization attempt) and the plan still fails review ` +
      `(${review.classification}: ${review.perItemFindings.map((f) => f.label).join(", ") || "no item"}). ` +
      findingsSentence(review),
  } as ReviewResult;
}
