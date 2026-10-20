// The logged agent-dispatch boundary. Three rules
// from hard-won debugging:
//   (a) every dispatch logs its RESOLVED input (byte length + sources) BEFORE
//       the call, so "the model never received X" is visible in pipeline.jsonl;
//   (b) an empty prompt is a fault, never a dispatch — the existsSync?read:""
//       fail-open class dies here;
//   (c) a prompt past the provider's input limit never goes out as is: a codex agent gets it by
//       file, a claude agent's call is refused — either way pipeline.jsonl names the stage, the
//       size and the largest sections (`shared/prompt_budget.ts`), so the stage is fixed.
import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import { appendPipelineLog } from "../log.js";
import { statePath } from "../paths.js";
import { extractJsonObject } from "../judgment.js";
import type { PipelineContext, Stage } from "../types.js";
import type { StageDeps } from "../pipeline_support.js";
import type { CodexRunInput } from "../shared/codex.js";
import type { ClaudeRunInput } from "../workers/claude.js";
import { claudeRoleModel } from "../claude_roles.js";
import { PROMPT_INPUT_MAX, PromptTooLongError, assertPromptFits, promptSections } from "../shared/prompt_budget.js";

/** The inactivity window of a worker that builds Lean inside its own shell (the F2 scaffolder, the
 *  F3 filler): a `lake build` of a paper's modules prints nothing until it ends, and one may run
 *  the better part of an hour, slowed by the other builds on the machine. The worker's default
 *  (25m, `codex.ts`) killed three such sessions mid-build, every stderr tail a build in progress. */
export const WORKER_BUILD_INACTIVITY_MS = 60 * 60 * 1000;

export interface DispatchAgentArgs {
  ctx: Pick<PipelineContext, "repoRoot" | "qid">;
  deps: { runCodex: StageDeps["runCodex"] };
  stage: Stage;
  /** Short human label for the log, e.g. "F3 proof filler". */
  label: string;
  prompt: string;
  /** The files/blocks that fed the prompt — logged so a missing input is visible. */
  promptSources: string[];
  model: string;
  reasoningEffort: CodexRunInput["reasoningEffort"];
  inactivityTimeoutMs?: number;
  /** Forwarded to runCodex (e.g. the F5 link step disables the Lean LSP). */
  leanLsp?: boolean;
  /** Defaults to ctx.repoRoot. */
  cwd?: string;
  /** Forwarded to runCodex. The F2.5/F4 reviewer fans out concurrently and must
   *  disable codex's native sub-agents (see CodexRunInput.multiAgent). */
  multiAgent?: boolean;
  webSearch?: boolean;
  sandboxMode?: CodexRunInput["sandboxMode"];
  ignoreUserConfig?: boolean;
  /** Source-producing nested F calls need the production workspace writable. */
  productionWrite?: boolean;
  /** Forwarded to runCodex: the reply must be one JSON object of this schema. */
  outputSchema?: Record<string, unknown>;
}

/** What a prompt may weigh and still go out as one message (the provider's limit is 1,048,576 characters). */
export const PROMPT_INLINE_MAX = PROMPT_INPUT_MAX;

type DispatchId = { ctx: Pick<PipelineContext, "repoRoot" | "qid">; stage: Stage; label: string; promptSources: string[] };

/** The largest sections of an over-long prompt, one line: what the stage at fault pasted. */
function largestSections(prompt: string): string {
  return promptSections(prompt).slice(0, 5).map((s) => `${s.chars} chars: ${s.name}`).join(" | ");
}

/**
 * Rule (c) for a codex agent: a prompt past `PROMPT_INLINE_MAX` goes by file — the agent is told
 * to read it whole first (its shell reads a file of any size and line length). This keeps a run
 * alive; the length itself is a defect of the stage that built the prompt, so the fallback is
 * loud: a warning and a `dispatch-by-file` line in pipeline.jsonl with the size, the largest
 * sections and the sources. Returns the prompt to send.
 */
async function inlineOrByFile(args: DispatchId, prompt: string, model: string): Promise<string> {
  if (prompt.length <= PROMPT_INLINE_MAX) return prompt;
  const file = path.join(path.dirname(statePath(args.ctx.repoRoot, args.ctx.qid)), "logs", "prompts", `long_${String(args.stage).replace(/[^\w.-]/g, "_")}_${Date.now()}.txt`);
  await mkdir(path.dirname(file), { recursive: true });
  await writeFile(file, prompt);
  const what = `${args.label} (stage ${args.stage}): the prompt is ${prompt.length} characters, over the ${PROMPT_INLINE_MAX} one message holds — sent by file ${file}. Largest sections: ${largestSections(prompt)}`;
  console.warn(`[dispatch] WARNING ${what}. Fix the stage that builds it.`);
  await appendPipelineLog(args.ctx, {
    stage: args.stage,
    status: "dispatch-by-file",
    duration_ms: 0,
    model,
    message: `${what}. Sources: [${args.promptSources.join(", ")}]`,
  });
  return `Your instructions for this task are too long for one message: they are the file\n${file}\n(${prompt.length} characters, ${prompt.split("\n").length} lines). Read that file WHOLE, from its first line to its last, before you do anything else — in parts if your reader limits a read — and then carry it out exactly as if it had been this message. Everything it says about your output applies to your reply here.`;
}

/**
 * Rule (c) for a claude agent: refused before the call. The by-file fallback is not sound there —
 * its Read tool cuts a long line (a pasted JSON document is one line), so the agent would work
 * from a prompt silently truncated. The refusal is in pipeline.jsonl with the same diagnosis.
 */
async function refuseOverlongPrompt(args: DispatchId, prompt: string, model: string): Promise<void> {
  try {
    assertPromptFits(prompt, `dispatch '${args.label}' (stage ${args.stage})`);
  } catch (err) {
    if (!(err instanceof PromptTooLongError)) throw err;
    await appendPipelineLog(args.ctx, {
      stage: args.stage,
      status: "dispatch-refused",
      duration_ms: 0,
      model,
      message: `${err.message}\nSources: [${args.promptSources.join(", ")}]`,
    });
    throw err;
  }
}

export async function dispatchAgent(args: DispatchAgentArgs): Promise<{ stdout: string; stderr: string }> {
  if (args.prompt.trim().length === 0) {
    throw new Error(
      `dispatch '${args.label}' (stage ${args.stage}) resolved to an EMPTY prompt — refusing to dispatch. ` +
        `Sources: [${args.promptSources.join(", ")}]`,
    );
  }
  const prompt = await inlineOrByFile(args, args.prompt, args.model);
  const started = Date.now();
  await appendPipelineLog(args.ctx, {
    stage: args.stage,
    status: "dispatch",
    duration_ms: 0,
    model: args.model,
    message: `${args.label}: prompt ${Buffer.byteLength(args.prompt, "utf8")} bytes from [${args.promptSources.join(", ")}]`,
  });
  const out = await args.deps.runCodex({
    prompt,
    cwd: args.cwd ?? args.ctx.repoRoot,
    model: args.model,
    reasoningEffort: args.reasoningEffort,
    inactivityTimeoutMs: args.inactivityTimeoutMs,
    ...(args.leanLsp !== undefined ? { leanLsp: args.leanLsp } : {}),
    ...(args.multiAgent !== undefined ? { multiAgent: args.multiAgent } : {}),
    ...(args.webSearch !== undefined ? { webSearch: args.webSearch } : {}),
    ...(args.sandboxMode !== undefined ? { sandboxMode: args.sandboxMode } : {}),
    ...(args.ignoreUserConfig !== undefined ? { ignoreUserConfig: args.ignoreUserConfig } : {}),
    ...(args.productionWrite !== undefined ? { productionWrite: args.productionWrite } : {}),
    ...(args.outputSchema !== undefined ? { outputSchema: args.outputSchema } : {}),
  });
  await appendPipelineLog(args.ctx, {
    stage: args.stage,
    status: "dispatch-complete",
    duration_ms: Date.now() - started,
    model: args.model,
    message: `${args.label}: stdout ${Buffer.byteLength(out.stdout, "utf8")} bytes`,
  });
  return out;
}

/** Uniform stdout→JSON boundary: one place that knows how agent JSON is
 *  extracted and how failure is represented (value, not exception). */
export function parseAgentJson(
  stdout: string,
): { json: Record<string, unknown>; parseError?: undefined } | { json?: undefined; parseError: string } {
  try {
    return { json: extractJsonObject(stdout) as Record<string, unknown> };
  } catch (err) {
    return { parseError: err instanceof Error ? err.message : String(err) };
  }
}

/** Claude-runner twin of dispatchAgent: same two rules (empty-prompt refusal,
 *  resolved-I/O logging) around deps.runClaude. The full ClaudeRunInput passes
 *  through `input` so callers keep allowedTools/mcpConfigPath/etc. untouched.
 *  The log names the model the role really runs on (codex's, under `claude_roles.ts`). */
export async function dispatchClaudeAgent(args: {
  ctx: Pick<PipelineContext, "repoRoot" | "qid">;
  deps: { runClaude: StageDeps["runClaude"] };
  stage: Stage;
  label: string;
  /** The files/blocks that fed the prompt — logged so a missing input is visible. */
  promptSources: string[];
  input: ClaudeRunInput;
}): Promise<string> {
  if (args.input.prompt.trim().length === 0) {
    throw new Error(
      `dispatch '${args.label}' (stage ${args.stage}) resolved to an EMPTY prompt — refusing to dispatch. ` +
        `Sources: [${args.promptSources.join(", ")}]`,
    );
  }
  const model = claudeRoleModel(args.input.model);
  await refuseOverlongPrompt(args, args.input.prompt, model);
  const started = Date.now();
  await appendPipelineLog(args.ctx, {
    stage: args.stage,
    status: "dispatch",
    duration_ms: 0,
    model,
    message: `${args.label}: prompt ${Buffer.byteLength(args.input.prompt, "utf8")} bytes from [${args.promptSources.join(", ")}]`,
  });
  // The claude --model value may be an alias ("opus"); record what it resolved
  // to so the run log pins the concrete model id (reproducibility: the paper's
  // base-model claims must be readable off pipeline.jsonl, not inferred from
  // config history). Callers' own onResolvedModel, if any, still runs.
  let resolvedModel: string | undefined;
  const out = await args.deps.runClaude({
    ...args.input,
    onResolvedModel: (m) => {
      resolvedModel = m;
      args.input.onResolvedModel?.(m);
    },
  });
  await appendPipelineLog(args.ctx, {
    stage: args.stage,
    status: "dispatch-complete",
    duration_ms: Date.now() - started,
    model: resolvedModel ?? model,
    message: `${args.label}: stdout ${Buffer.byteLength(out, "utf8")} bytes`,
  });
  return out;
}
