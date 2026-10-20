// Study scaffolder agent: plans the staging module and emits one proof-fill prompt per filler.
import { runCodex as realRunCodex } from "../shared/codex.js";
import { MODELS } from "../models.js";
import { expectStringJsonOutput } from "../shared/codex_json.js";
import { logAgentCall } from "./log.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { buildScaffolderPrompt, toolkitPromptContext } from "./prompts.js";
import { parseScaffolderOutput, type ScaffolderOutput, type RoundReport, type ReviewVerdict } from "./types.js";

export interface ScaffolderArgs {
  /** The toolkit root (cwd and Lean project of the agent). */
  repoRoot: string; toolkit: ToolkitConfig; runDir: string; slug: string; requirement: string; leanDir: string; modulePrefix: string;
  planMarkdown: string | null; lastReport: RoundReport | null; lastReview: ReviewVerdict | null;
  buildRounds: number; buildCap: number;
}
export interface ScaffolderDeps { runCodex: typeof realRunCodex }

export async function runScaffolder(
  args: ScaffolderArgs,
  deps: ScaffolderDeps = { runCodex: realRunCodex },
): Promise<ScaffolderOutput> {
  const prompt = buildScaffolderPrompt({ ...args, toolkit: toolkitPromptContext(args.toolkit) });
  const t0 = Date.now();
  let stdout = "";
  let parsed: ScaffolderOutput | undefined;
  let parseError: string | undefined;
  try {
    const result = await deps.runCodex({
      prompt,
      model: MODELS.codexKernel,
      reasoningEffort: "high",
      cwd: args.repoRoot,
      leanProjectPath: args.toolkit.leanProjectPath,
    });
    stdout = result.stdout;
    parsed = parseScaffolderOutput(expectStringJsonOutput(stdout));
    return parsed;
  } catch (err) {
    parseError = err instanceof Error ? err.message : String(err);
    throw err;
  } finally {
    await logAgentCall(args.runDir, {
      agent: "scaffolder", round: args.buildRounds + 1, callId: "main", model: MODELS.codexKernel,
      prompt, promptBytes: Buffer.byteLength(prompt), rawOutput: stdout,
      parsed, parseError, ok: parseError === undefined, durationMs: Date.now() - t0,
    });
  }
}
