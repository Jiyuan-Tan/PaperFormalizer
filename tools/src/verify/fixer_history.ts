/**
 * What the fixer was told before (`discovery/fixer_history.json`): each finding a patch round handed
 * it, per node. Its prompt shows a node's earlier findings next to the current one (`EARLIER FINDINGS`),
 * so a repair keeps meeting what it already answered and a chain of defects is seen whole rather than
 * one per round. Kept short: the last few per node, each cut to a paragraph.
 */
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import { z } from "zod";
import { writeJsonAtomic } from "../shared/json_atomic.js";

export const FIXER_HISTORY_FILE = "discovery/fixer_history.json";
/** Earlier findings shown per node, and kept per node on file. */
const SHOWN = 4;
const KEPT = 8;
/** Characters of a detail or a witness shown (a detail lists several defects as items). */
const CUT = 1200;

export interface FixerHistoryEntry {
  round: number;
  axis: string;
  detail: string;
  witness: string | null;
}
export type FixerHistory = Record<string, FixerHistoryEntry[]>;
type Finding = { id: string; axis: string; detail: string; witness?: string | null };

const HistorySchema = z.record(z.string(), z.array(z.object({ round: z.number(), axis: z.string(), detail: z.string(), witness: z.string().nullable() })));

const cut = (t: string): string => (t.length > CUT ? `${t.slice(0, CUT)}…` : t);

/** The earlier findings on the nodes `findings` name, one line each (empty: none); a node in `skip`
 * (its finding withdrawn by the owner) shows none. Pure. */
export function earlierFindingsBlock(history: FixerHistory, findings: readonly Finding[], skip: ReadonlySet<string> = new Set()): string {
  const lines: string[] = [];
  for (const id of new Set(findings.map((f) => f.id))) {
    if (skip.has(id)) continue;
    const current = new Set(findings.filter((f) => f.id === id).map((f) => f.detail));
    for (const e of (history[id] ?? []).filter((x) => !current.has(x.detail)).slice(-SHOWN)) {
      lines.push(`- ${id} (round ${e.round}, ${e.axis}): ${cut(e.detail)}${e.witness ? ` Witness: ${cut(e.witness)}` : ""}`);
    }
  }
  return lines.join("\n");
}

/** `history` with the findings of patch round `round` added (a finding already on file is not repeated). Pure. */
export function withFindings(history: FixerHistory, round: number, findings: readonly Finding[]): FixerHistory {
  const out: FixerHistory = { ...history };
  for (const f of findings) {
    if (f.id === "run") continue;
    const prior = out[f.id] ?? [];
    if (prior.some((e) => e.detail === f.detail)) continue;
    out[f.id] = [...prior, { round, axis: f.axis, detail: f.detail, witness: f.witness ?? null }].slice(-KEPT);
  }
  return out;
}

export async function readFixerHistory(runDir: string): Promise<FixerHistory> {
  const file = path.join(runDir, FIXER_HISTORY_FILE);
  if (!existsSync(file)) return {};
  try {
    const parsed = HistorySchema.safeParse(JSON.parse(await readFile(file, "utf8")));
    return parsed.success ? parsed.data : {};
  } catch {
    return {};
  }
}

export async function writeFixerHistory(runDir: string, history: FixerHistory): Promise<void> {
  await writeJsonAtomic(path.join(runDir, FIXER_HISTORY_FILE), history);
}
