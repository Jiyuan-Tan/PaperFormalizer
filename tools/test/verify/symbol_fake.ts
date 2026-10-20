/**
 * Test helper: the V1.5 symbol referee (`referee_symbols.ts`) runs before the node referee. Canned-reply
 * fakes written for the node referee answer its calls here — every symbol graded `ok` (or as `grade` says) — so their reply queues and call counts are unchanged.
 */
import type { CodexRunInput } from "../../src/shared/codex.js";

export type SymbolGrader = (name: string) => Record<string, unknown>;

/** Whether a codex call is one of the symbol referee's (a shard or a single call). */
export function isSymbolCall(input: CodexRunInput): boolean {
  const req = (input.outputSchema as { required?: string[] } | undefined)?.required ?? [];
  return req.includes("symbols") || (req.includes("symbol") && req.includes("reason"));
}

/** The symbol names a symbol call grades (its SYMBOLS TO GRADE section). */
export function symbolNames(prompt: string): string[] {
  const adj = /=== THE SYMBOL: (.+?) — AND THE TWO GRADINGS ===/.exec(prompt);
  if (adj) return [adj[1]!];
  const m = /=== SYMBOLS TO GRADE[^\n]*===\n\n[^\n]*\n\n([\s\S]*?)\n\n===/.exec(prompt);
  return (m?.[1] ?? "").split("\n").filter(Boolean).map((l) => (JSON.parse(l) as { name: string }).name);
}

export function okSymbol(name: string): Record<string, unknown> {
  return { name, meaning: "ok", fix: null, ambiguity: "ok", reading: null, redefined_at: null, detail: "canned: as recorded" };
}

/** The canned stdout of a symbol call, or null when `input` is not one. */
export function symbolReply(input: CodexRunInput, grade: SymbolGrader = okSymbol): string | null {
  if (!isSymbolCall(input)) return null;
  const names = symbolNames(input.prompt);
  const req = (input.outputSchema as { required?: string[] }).required ?? [];
  const out = req.includes("symbols")
    ? { summary: "canned", symbols: names.map((n) => ({ ...okSymbol(n), ...grade(n) })) }
    : { reason: "canned", symbol: { ...okSymbol(names[0]!), ...grade(names[0]!) } };
  return JSON.stringify(out);
}
