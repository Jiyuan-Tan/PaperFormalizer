import type { StateJson } from "../types.js";

/** Authoritative Phase-A F2.5 scaffold/review budget. */
export const PROOF_SCAFFOLD_MAX = 10;

/** Identical F2.5 error signatures tolerated before fail-closed escalation. */
export const REPEATED_F25_ERROR_MAX = 3;

/** F1.5 verdicts that bounce the plan back to F1, PER FORMALIZATION ATTEMPT
 *  (`flags.plan_review_rounds`). The per-entry cap of the review boundary bounded one entry
 *  only: every resume, F2.5 fix-locus rewind or pin re-sync re-entered F1.5 with a fresh
 *  budget, and one run spent 14 F1 passes and 18 reviews that way. Persisted in state.json like
 *  `proof_loop_counters`, so a resume cannot refund it; only a rewind that starts a fresh plan
 *  (`resetFormalizationLoopCounters`) does. */
export const PLAN_REVIEW_ROUNDS_MAX = 6;

/** The counter lives on `flags` (its zod object passes unknown keys through). */
type PlanReviewFlags = { plan_review_rounds?: number };

/** F1.5 bounces spent so far in this formalization attempt. */
export function planReviewRounds(state: Pick<StateJson, "flags">): number {
  return (state.flags as PlanReviewFlags).plan_review_rounds ?? 0;
}

/** Record `n` more F1.5 bounces. */
export function addPlanReviewRounds(state: Pick<StateJson, "flags">, n: number): void {
  (state.flags as PlanReviewFlags).plan_review_rounds = planReviewRounds(state) + n;
}

/**
 * The F-stage loop budgets outside the proof loop are PER FORMALIZATION ATTEMPT: a rewind that
 * starts a fresh plan (the verify runner's V1 patch rounds and owner pins, which re-plan the
 * revised core) starts them over. Today that is the F1↔F1.5 correction budget; the proof loop's own counters are reset by their owners.
 */
export function resetFormalizationLoopCounters(state: Pick<StateJson, "flags">): void {
  delete (state.flags as PlanReviewFlags).plan_review_rounds;
}

/** The proof loop's budgets start over (a new formalization attempt); the filler's dead-end memory
 *  is not a budget and is kept. */
export function resetProofLoopBudgets(state: Pick<StateJson, "flags">): void {
  const c = state.flags.proof_loop_counters;
  if (c) state.flags.proof_loop_counters = { ...c, iters: 0, scaffold_rounds: 0, stale: 0, tag_reroutes: 0, node_strikes: {}, review_error_strikes: {}, last_build_error_sig: "", progress_best: undefined };
}

/**
 * The core is being replaced (`--from-stage V1|V1.5`): what the F stages recorded about the plan
 * and scaffold of the old one does not describe the new — the F1↔F1.5 budget, the proof loop's
 * budgets, a blocked F1, a missing-architecture block (its items named declarations the old
 * scaffold wanted) and a pending escalation.
 */
export function resetForNewCore(state: Pick<StateJson, "flags">): void {
  resetFormalizationLoopCounters(state);
  resetProofLoopBudgets(state);
  state.flags.f1_blocked = null;
  state.flags.missing_architecture = false;
  delete state.flags.missing_architecture_items;
  state.flags.proof_review_escalation_pending = null;
}
