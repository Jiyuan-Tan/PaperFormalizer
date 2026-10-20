import { appendFile } from "node:fs/promises";
import path from "node:path";

export interface ModelTokenUsage {
  input_tokens: number;
  cached_input_tokens: number;
  cache_creation_input_tokens: number;
  output_tokens: number;
  reasoning_output_tokens: number;
  total_tokens: number;
}

export interface TokenUsageRecord {
  timestamp: string;
  provider: "codex" | "claude";
  model: string;
  stage: string;
  /** Set on a call that is not the stage's own work (`auth warm-up`: the login probe made ahead of it). */
  role?: string;
  duration_ms: number;
  success: boolean;
  usage: ModelTokenUsage | null;
}

/** The usage of two attempts of one call as one record: a transient retry's first attempt was
 *  paid for too, and a ledger that kept only the last attempt lost it. */
export function addTokenUsage(a: ModelTokenUsage | null, b: ModelTokenUsage): ModelTokenUsage {
  if (!a) return b;
  return {
    input_tokens: a.input_tokens + b.input_tokens,
    cached_input_tokens: a.cached_input_tokens + b.cached_input_tokens,
    cache_creation_input_tokens: a.cache_creation_input_tokens + b.cache_creation_input_tokens,
    output_tokens: a.output_tokens + b.output_tokens,
    reasoning_output_tokens: a.reasoning_output_tokens + b.reasoning_output_tokens,
    total_tokens: a.total_tokens + b.total_tokens,
  };
}

export const TOKEN_USAGE_LEDGER = "token_usage.jsonl";
export const TOKEN_USAGE_INCOMPLETE = "token_usage_incomplete";

export async function appendTokenUsageRecord(runDir: string, record: TokenUsageRecord): Promise<void> {
  await appendFile(path.join(runDir, TOKEN_USAGE_LEDGER), `${JSON.stringify(record)}\n`, "utf8");
}

export async function markTokenUsageIncomplete(runDir: string, reason: string): Promise<void> {
  await appendFile(
    path.join(runDir, TOKEN_USAGE_INCOMPLETE),
    `${new Date().toISOString()} ${reason}\n`,
    "utf8",
  );
}

/**
 * A Codex runner that writes one ledger record per call under `stage` — for callers outside the F
 * stages' worker plumbing (the verify runner's V1, V1.5 and promotion calls). Telemetry is
 * best-effort: it never changes the call's outcome.
 */
export function withTokenLedger<I extends { model?: string; onUsage?: (usage: ModelTokenUsage) => void; onAuthWarmUp?: (call: { model: string; duration_ms: number; success: boolean; usage: ModelTokenUsage | null }) => void }, O>(
  run: (input: I) => Promise<O>,
  runDir: string,
  stage: string,
): (input: I) => Promise<O> {
  return async (input) => {
    const started = Date.now();
    let usage: ModelTokenUsage | null = null;
    const warmUps: Promise<void>[] = [];
    const record = async (success: boolean) =>
      Promise.all(warmUps).then(() => appendTokenUsageRecord(runDir, {
        timestamp: new Date().toISOString(), provider: "codex", model: input.model ?? "default", stage,
        duration_ms: Date.now() - started, success, usage,
      })).catch((err) => markTokenUsageIncomplete(runDir, String(err)).catch(() => {}));
    try {
      // The login warm-up made ahead of the call is a call of its own: one record, under this stage.
      const onAuthWarmUp = (call: { model: string; duration_ms: number; success: boolean; usage: ModelTokenUsage | null }): void => {
        warmUps.push(appendTokenUsageRecord(runDir, { timestamp: new Date().toISOString(), provider: "codex", stage, role: "auth warm-up", ...call }).catch(() => {}));
        input.onAuthWarmUp?.(call);
      };
      const out = await run({ ...input, onAuthWarmUp, onUsage: (u: ModelTokenUsage) => { usage = addTokenUsage(usage, u); input.onUsage?.(u); } });
      await record(true);
      return out;
    } catch (err) {
      await record(false);
      throw err;
    }
  };
}
