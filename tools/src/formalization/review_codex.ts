// The F1.5 Codex review: the plan's reuse decisions against the typed core — the whole plan the
// first time, what moved since the passed plan on a re-plan (`replanReviewContext`).

import { writeFile } from "node:fs/promises";
import path from "node:path";
import { MODEL_PLAN } from "../constants.js";
import { type ReviewResult } from "../judgment.js";
import { coreJsonPath, readFormalizationCore } from "../core/core_io.js";
import type { Core } from "../core/schema.js";
import { BINDING_READINGS_NOTE, SCOPED_SYMBOLS_NOTE, SHARED_READINGS_NOTE, formalizationCoreContextValue, readFormalizationCoreContext } from "./core_context.js";
import { buildF2RevisionContext } from "./f2_revision_context.js";
import { PlanSchema, type Plan } from "./plan/schema.js";
import {
  BEYOND_SCOPE_KEY,
  beyondScopeReported,
  coreChangeSeeds,
  planChangeSeeds,
  readReviseBasis,
  reviseLookupBlock,
  writeReviseBasis,
  type ReviseBasis,
} from "./revise_scope.js";
import { appendPipelineLog } from "../log.js";
import { planReviewedPath } from "../paths.js";
import type { PipelineContext, StateJson } from "../types.js";
import {
  artifactPaths,
  baseBrief,
  bookkeepingPolicyBlock,
  parseReview,
  readRequired,
  readPrompt,
  type StageDeps,
} from "../pipeline_support.js";
import { dispatchAgent } from "../framework/agent_dispatch.js";
import { librarySearchPromptBlock } from "../toolkit/search.js";
import { parseJsonWithEscapeRepair } from "../shared/codex_json.js";
import { PROMPT_INPUT_MAX } from "../shared/prompt_budget.js";

/** What one review prompt may hold: the budget of any call (a paper of 170 nodes, its plan and
 *  its core printed whole, passed the provider's limit by 500). */
export const REVIEW_INPUT_MAX = PROMPT_INPUT_MAX;

/** The plan and the core as the review prompt carries them: printed whole while they fit `room`;
 *  past it the core goes by file (`paths.core`, written by the caller), and the plan too if it
 *  still does not fit — the reviewer reads the files, and nothing is cut. Pure. */
export function reviewContext(planText: string, coreText: string, paths: { plan: string; core: string }, room: number): { block: string; coreByFile: boolean } {
  const planHead = "Formalization plan (plan.json — the subject of review)", coreHead = `Typed core JSON (structural ground truth; proof/publication prose omitted). ${BINDING_READINGS_NOTE} ${SCOPED_SYMBOLS_NOTE}`;
  const byFile = (head: string, file: string) => `${head}: too long to print here — it is the file ${file}. Read it whole before you review; it is part of this prompt.`;
  if (planText.length + coreText.length <= room) return { block: `${planHead}:\n${planText}\n\n${coreHead}\n${coreText}\n`, coreByFile: false };
  if (planText.length <= room) return { block: `${planHead}:\n${planText}\n\n${byFile(coreHead, paths.core)}\n`, coreByFile: true };
  return { block: `${byFile(planHead, paths.plan)}\n\n${byFile(coreHead, paths.core)}\n`, coreByFile: true };
}

/** The plan as the reviewer reads it: the same object, serialized compact (F1 writes it
 *  pretty-printed; the indentation was a tenth of the review prompt). Unparseable text is
 *  passed as is — the gate pre-lint has already bounced such a plan. Pure. */
export function planReviewText(planText: string): string {
  try {
    return JSON.stringify(parseJsonWithEscapeRepair(planText));
  } catch {
    return planText;
  }
}

/**
 * The context of the review of a RE-PLAN (a plan F1.5 passed before, patched since): the plan
 * entries that changed since that pass, what must move with them (`reviseAffectedNodeIds`), their
 * core records, and a reference line for every other node — not the whole plan again. Null when
 * there is no record of the passed plan, when nothing a review covers moved, or when a changed
 * entry is no plan node: the review then reads everything. Pure.
 */
export function replanReviewContext(args: {
  basis: ReviseBasis | null;
  planRaw: unknown;
  plan: Plan;
  core: Core;
  paths: { plan: string; core: string };
}): { block: string; changed: string[]; affected: number } | null {
  if (!args.basis) return null;
  const replanned = planChangeSeeds(args.basis.plan, args.planRaw);
  const moved = coreChangeSeeds(args.basis.core, formalizationCoreContextValue(args.core));
  // A citation or another plan-level field moved: no entry carries it, so the review reads the whole plan.
  if (replanned.other) return null;
  const changed = [...new Set([...replanned.nodes, ...moved.nodes])].filter((id) => id in args.plan.nodes);
  const packet = buildF2RevisionContext(args.core, args.plan, changed, { contextSymbols: moved.symbols, contextEnvs: replanned.envs });
  // A changed entry the packet could not place is not under review in it: the whole plan is read.
  if (!packet || packet.unresolved_targets.length > 0) return null;
  const block = [
    "=== REVIEW OF A RE-PLAN (scoped) ===",
    "This plan was reviewed and passed before; F1 has patched it since. Review ONLY the entries shown in full",
    `below: the ${changed.length} that changed since that pass${replanned.envs.length > 0 ? ` (and S-block(s) ${replanned.envs.join(", ")})` : ""} and the entries that must move with them.`,
    "Every other entry is as it passed — a reference line here, not under review. The deterministic gate ran on the WHOLE plan.",
    `Changed since the pass: ${[...changed, ...replanned.envs].join(", ")}`,
    "=== END REVIEW OF A RE-PLAN ===",
    "",
    ...(packet.context.length > 0 ? [`Shown beside them as context — an entry under review names them; not under review: ${packet.context.join(", ")}`, ""] : []),
    `Formalization plan — the entries under review (${packet.affected.length} of ${packet.affected.length + packet.context.length + packet.index.length} nodes):`,
    JSON.stringify(packet.plan),
    "",
    `Typed core JSON — the records of those nodes and the symbols they use (structural ground truth; proof/publication prose omitted). ${SHARED_READINGS_NOTE} ${SCOPED_SYMBOLS_NOTE}`,
    JSON.stringify(packet.core),
    "",
    reviseLookupBlock({
      index: packet.index,
      shown: packet.affected.length + packet.context.length,
      total: packet.affected.length + packet.context.length + packet.index.length,
      corePath: args.paths.core,
      planPath: args.paths.plan,
      replyField: `your \`notes\` (a pass) or \`verbatim_critique\` (a revise), written \`${BEYOND_SCOPE_KEY}: [<ids>]\``,
    }),
  ].join("\n");
  return { block, changed, affected: packet.affected.length };
}

export async function reviewWithCodex(
  args: { ctx: PipelineContext; state: StateJson; deps: StageDeps },
  promptName: string,
  stageLabel: "1.5",
  instruction: string,
  /** The plan under review was passed before (F2 has run on it): review what moved since. */
  opts: { replan?: boolean } = {},
): Promise<ReviewResult> {
  const paths = artifactPaths(args.ctx, args.state);
  // The formalization PLAN and the typed core are both REQUIRED (fail loud; see readRequired).
  const planRawText = await readRequired(paths.plan, "F1.5 review");
  const planText = planReviewText(planRawText);
  const coreFile = coreJsonPath(args.ctx);
  const coreText = await readFormalizationCoreContext(coreFile, "F1.5 review");
  const corePath = path.join(path.dirname(paths.plan), "f1_5_core_context.json");
  const reviewedPath = planReviewedPath(args.ctx.repoRoot, args.ctx.qid);
  let planRaw: unknown = null;
  let scoped: ReturnType<typeof replanReviewContext> = null;
  try {
    planRaw = parseJsonWithEscapeRepair(planRawText);
    const parsedPlan = PlanSchema.safeParse(planRaw);
    if (opts.replan && parsedPlan.success) {
      scoped = replanReviewContext({
        basis: await readReviseBasis(reviewedPath),
        planRaw,
        plan: parsedPlan.data as Plan,
        core: await readFormalizationCore(coreFile),
        paths: { plan: paths.plan, core: coreFile },
      });
    }
  } catch (err) {
    console.warn(`[leansmith] F1.5: scoped re-plan review unavailable, reviewing the whole plan: ${err instanceof Error ? err.message : String(err)}`);
  }
  if (opts.replan) {
    console.warn(
      scoped
        ? `[F] F1.5: re-plan review scoped to ${scoped.affected} entr${scoped.affected === 1 ? "y" : "ies"} (${scoped.changed.length} changed since the passed plan)`
        : "[F] F1.5: no record of the passed plan, or a change no entry carries — reviewing the whole plan",
    );
  }
  const fixed = (await readPrompt(args.ctx, promptName)).length + baseBrief(args.ctx, args.state).length + instruction.length + 8_000;
  const { block: wholeBlock, coreByFile } = scoped
    ? { block: "", coreByFile: false }
    : reviewContext(planText, coreText, { plan: paths.plan, core: corePath }, REVIEW_INPUT_MAX - fixed);
  if (coreByFile) await writeFile(corePath, coreText);
  const contextBlock = scoped?.block ?? wholeBlock;
  // The shared bookkeeping policy, so a regularity side-condition added by F1 is NOT
  // mis-flagged as illegitimate assumption-strengthening.
  const prompt = [
    `${await readPrompt(args.ctx, promptName)}\n${bookkeepingPolicyBlock()}\n`,
    "",
    baseBrief(args.ctx, args.state),
    "",
    librarySearchPromptBlock(args.ctx),
    "",
    instruction,
    "",
    contextBlock,
  ].join("\n");
  // lean-lsp is default-ON for every codex call (see shared/codex.ts) so the
  // reviewer's `lean_multi_attempt` vacuity probes are actually available.
  const out = await dispatchAgent({
    ctx: args.ctx,
    deps: args.deps,
    stage: stageLabel,
    label: `F${stageLabel} review (${promptName})`,
    prompt,
    promptSources: [promptName, "baseBrief", paths.plan, coreJsonPath(args.ctx)],
    model: MODEL_PLAN.stage1_5.model,
    reasoningEffort: MODEL_PLAN.stage1_5.effort,
  });
  const review = parseReview(out.stdout);
  // The mechanical affected set under-reached: say where, so the rule can be widened.
  const beyond = scoped ? beyondScopeReported(out.stdout) : [];
  if (beyond.length > 0) {
    await appendPipelineLog(args.ctx, {
      stage: stageLabel,
      status: "revise-scope",
      duration_ms: 0,
      message: `F1.5 re-plan review looked up ${beyond.length} node(s) beyond the affected set (${scoped!.affected}): ${beyond.join(", ")}`,
    });
    console.warn(`[leansmith] F1.5 re-plan review looked up ${beyond.length} node(s) beyond the affected set: ${beyond.join(", ")}`);
  }
  // The plan and core that passed: the review of the next re-plan covers what moved since.
  if ((review.status === "pass" || review.status === "accept") && planRaw) {
    await writeReviseBasis(reviewedPath, { plan: planRaw, core: JSON.parse(coreText) });
  }
  return review;
}
