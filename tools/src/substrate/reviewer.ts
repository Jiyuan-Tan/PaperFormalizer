// Study reviewer agent: ONE codex review pass judges the staging module against the requirement
// (no second reviewer; the deterministic build / sorry / axiom gates back it up).
import { MODELS } from "../models.js";
import { runCodex as realRunCodex } from "../shared/codex.js";
import { expectStringJsonOutput } from "../shared/codex_json.js";
import { logAgentCall } from "./log.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { buildReviewerPrompt, toolkitPromptContext } from "./prompts.js";
import { parseReviewVerdict, type ReviewVerdict } from "./types.js";

export interface ReviewerArgs { repoRoot: string; toolkit: ToolkitConfig; runDir: string; round: number; slug: string; requirement: string; leanDir: string; modulePrefix: string }
export interface ReviewerDeps { runCodex: typeof realRunCodex }

export async function runReviewer(
  args: ReviewerArgs,
  deps: ReviewerDeps = { runCodex: realRunCodex },
): Promise<ReviewVerdict> {
  const prompt = buildReviewerPrompt({ ...args, toolkit: toolkitPromptContext(args.toolkit) });
  const t0 = Date.now();
  let stdout = "";
  let parsed: ReviewVerdict | undefined;
  let parseError: string | undefined;
  try {
    const res = await deps.runCodex({ prompt, model: MODELS.codexKernel, reasoningEffort: "high", cwd: args.repoRoot, leanProjectPath: args.toolkit.leanProjectPath });
    stdout = res.stdout;
    parsed = parseReviewVerdict(expectStringJsonOutput(stdout));
    return parsed;
  } catch (err) {
    parseError = err instanceof Error ? err.message : String(err);
    throw err;
  } finally {
    await logAgentCall(args.runDir, {
      agent: "reviewer", round: args.round, callId: "main", model: MODELS.codexKernel,
      prompt, promptBytes: Buffer.byteLength(prompt), rawOutput: stdout,
      parsed, parseError, ok: parseError === undefined, durationMs: Date.now() - t0,
    });
  }
}
