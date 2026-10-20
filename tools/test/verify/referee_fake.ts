/**
 * Test helper: the V1.5 referee is always sharded (`referee_shards.ts`) — node shards leaves-first,
 * then one global pass. A test written for the one-call referee cans ONE whole-core reply
 * (`{verdict, summary, nodes, patch_review, rejection_verdicts}`); `shardedRefereeReply` answers each
 * shard call with that reply's verdicts of the nodes the shard grades, and the global call with its
 * verdict, summary, patch review and rejection verdicts (no cross-node items unless the reply gives
 * `cross_node`). Node verdicts pass through `withOwnerExplanations` as before.
 */
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { GLOBAL_REPLY, SHARD_REPLY } from "../../src/verify/referee_shard_prompts.js";
import { withOwnerExplanations } from "./owner_explained.js";
import { symbolReply } from "./symbol_fake.js";

/** A whole-core referee reply, as tests canned it for the one-call referee. */
export interface WholeCoreReply {
  verdict?: string;
  summary?: string;
  nodes?: Array<Record<string, unknown> & { id: string }>;
  patch_review?: unknown;
  rejection_verdicts?: unknown;
  cross_node?: unknown[];
}

export const isRefereeShard = (input: CodexRunInput): boolean => input.outputSchema === SHARD_REPLY;
export const isRefereeGlobal = (input: CodexRunInput): boolean => input.outputSchema === GLOBAL_REPLY;
/** A node-shard or global call of the V1.5 referee. */
export const isRefereeCall = (input: CodexRunInput): boolean => isRefereeShard(input) || isRefereeGlobal(input);

/** The ids a shard call grades (its NODES TO GRADE section). */
export function shardIds(prompt: string): string[] {
  const m = /=== NODES TO GRADE[^\n]*===\n\n((?:- [^\n]*\n?)+)/.exec(prompt);
  return (m?.[1] ?? "").split("\n").filter(Boolean).map((l) => l.slice(2));
}

/**
 * The canned stdout of a referee call from the whole-core reply `reply`, or null when `input` is no
 * referee call. A shard grades the nodes it lists (each must carry a verdict in `reply`, else
 * `missing(id)` gives one — by default the call throws).
 */
export function shardedRefereeReply(input: CodexRunInput, reply: WholeCoreReply, missing?: (id: string) => Record<string, unknown>): string | null {
  if (isRefereeShard(input)) {
    const nodes = shardIds(input.prompt).map((id) => {
      const v = reply.nodes?.find((n) => n.id === id) ?? missing?.(id);
      if (!v) throw new Error(`the canned referee reply has no verdict for ${id}`);
      return v;
    });
    return JSON.stringify(withOwnerExplanations({ summary: reply.summary ?? "canned", nodes }));
  }
  if (isRefereeGlobal(input)) {
    return JSON.stringify({
      verdict: reply.verdict ?? "PASS",
      summary: reply.summary ?? "canned",
      patch_review: reply.patch_review ?? null,
      rejection_verdicts: reply.rejection_verdicts ?? null,
      cross_node: reply.cross_node ?? [],
    });
  }
  return null;
}

/**
 * A canned codex: symbol calls graded ok (`symbolReply`); otherwise `replies[k]` answers the k-th
 * model step — a fixer call, or a whole referee pass (every shard call and its global call, from one
 * whole-core reply). Every non-symbol call is pushed on `calls`; a step past the replies throws.
 */
export function cannedCodex(replies: unknown[], calls: CodexRunInput[], opts: { missing?: (id: string) => Record<string, unknown> } = {}): typeof runCodex {
  let next = 0;
  return (async (input: CodexRunInput) => {
    const sym = symbolReply(input);
    if (sym !== null) return { stdout: sym, stderr: "" };
    const reply = replies[next];
    calls.push(input);
    if (reply === undefined) throw new Error(`unexpected codex call #${calls.length} (step ${next + 1})`);
    if (isRefereeCall(input)) {
      if (isRefereeGlobal(input)) next += 1;
      return { stdout: shardedRefereeReply(input, reply as WholeCoreReply, opts.missing)!, stderr: "" };
    }
    next += 1;
    return { stdout: JSON.stringify(withOwnerExplanations(reply)), stderr: "" };
  }) as typeof runCodex;
}

/** The non-referee calls of `calls` (the fixer's). */
export const fixerCalls = (calls: readonly CodexRunInput[]): CodexRunInput[] => calls.filter((c) => !isRefereeCall(c));
