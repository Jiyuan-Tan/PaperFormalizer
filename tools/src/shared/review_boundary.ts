import type { ReviewResult } from "../judgment.js";
import { appendReview } from "../pipeline_support.js";
import type { PipelineContext, Stage, StageResult, StateJson } from "../types.js";

/**
 * A producer/reviewer loop with no model call between the two: review, and on a bounce hand the
 * verdict to the producer as its correction, up to `cap` reviews. A pass completes the stage (or
 * halts at `checkpointOnPass`). The loop decides no route: a verdict carrying `halt_reason` (the
 * reviewer's wrapper found the producer cannot act on it), a `reject`, or a plan still failing at
 * the cap halts at a checkpoint behind the `general_review_halt` cap gate, and the orchestrator
 * reads the logged verdicts and rules.
 */
export async function runReviewBoundary(args: {
  ctx: PipelineContext;
  state: StateJson;
  boundary: string;
  stage: Stage;
  cap: number;
  producer: (prior: ReviewResult, attempt: number) => Promise<StageResult>;
  reviewer: (attempt: number) => Promise<ReviewResult>;
  /** When set, a pass halts at a checkpoint with this message (`advance: true`) instead of
   *  flowing on: F1.5 settles the plan and its review into the one checkpoint the orchestrator
   *  audits before F2. */
  checkpointOnPass?: string;
}): Promise<StageResult> {
  const halt = (message: string): StageResult => {
    args.state.flags.general_review_halt = message;
    return { stage: args.stage, status: "checkpoint", advance: false, message };
  };
  let prior: ReviewResult | null = null;
  for (let attempt = 1; attempt <= args.cap; attempt++) {
    if (prior) {
      const producerResult = await args.producer(prior, attempt);
      // A producer that did not produce (blocked, or halted without completing) ends the loop
      // with its own message: the reviewer would only read the earlier artifact again.
      if (producerResult.status === "blocked" || producerResult.advance === false) return producerResult;
    }
    const review = await args.reviewer(attempt);
    await appendReview(args.ctx, args.boundary, attempt, review);
    const haltReason = (review as { halt_reason?: string }).halt_reason;
    if (haltReason) return halt(`Review boundary ${args.boundary} halted: ${haltReason}`);
    if (review.status === "pass" || review.status === "accept") {
      if (args.checkpointOnPass) {
        return { stage: args.stage, status: "checkpoint", advance: true, message: args.checkpointOnPass };
      }
      return { stage: args.stage, status: "completed", message: `Review boundary ${args.boundary} passed` };
    }
    prior = review;
    // A reject means another producer retry cannot help.
    if (review.status === "reject") break;
  }
  const last = prior as Extract<ReviewResult, { status: "revise" | "reject" }>;
  const trigger = last.status === "reject" ? "rejected" : `still failing after ${args.cap} review(s)`;
  return halt(
    `REVIEW ESCALATION at ${args.boundary} (${trigger}; latest verdict ${last.status}/${last.classification}): ` +
      `${last.verbatim_critique.trim().slice(0, 600) || "see the review log"}`,
  );
}
