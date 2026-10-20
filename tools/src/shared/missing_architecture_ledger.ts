// Per-run ledger (`runs/<slug>/MISSING_ARCHITECTURE.md`) of infrastructure the run NEEDED but
// that does not yet exist in the base libraries or the toolkit. Writer: F2 (stage2) on
// `blocked-missing-architecture` — records `missing_items`. Entries are keyed by
// `qid:source` and REPLACED in place on re-run, so repeated runs update rather than
// duplicate. Human-readable so a maintainer can scan it, land an item, then re-run.

import fs from "node:fs";
import path from "node:path";
import lockfile from "proper-lockfile";
import { missingArchitecturePath } from "../paths.js";

export interface MissingArchItem {
  id?: string;
  kind: string;
  description: string;
  effort?: string;
}

export interface MissingArchEntry {
  qid: string;
  /** e.g. "F1 needs-new-infrastructure" | "F2 missing-architecture". */
  source: string;
  /** YYYY-MM-DD; caller supplies (keeps this module clock-free / testable). */
  date: string;
  items: MissingArchItem[];
}

const HEADER = `# Missing Architecture Ledger

Auto-maintained by leansmith. Each block records infrastructure a run NEEDED but
that does not yet exist in the base libraries or the toolkit. Pick an item, land it,
then re-run. Blocks are keyed by \`qid:source\` and replaced in place on re-run.
`;

function sleepSync(ms: number): void {
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms);
}

function lockLedgerSync(lockPath: string): () => void {
  for (let attempt = 0; attempt <= 10; attempt += 1) {
    try {
      return lockfile.lockSync(lockPath, {
        stale: 60_000,
        realpath: false,
      });
    } catch (err) {
      if ((err as NodeJS.ErrnoException).code !== "ELOCKED" || attempt === 10) throw err;
      sleepSync(Math.min(5_000, 100 * 1.5 ** attempt));
    }
  }
  throw new Error(`Could not acquire ledger lock at ${lockPath}`);
}

/** Ledger location: the run's own `runs/<slug>/MISSING_ARCHITECTURE.md`. */
export function missingArchitectureLedgerPath(repoRoot: string, qid: string): string {
  return missingArchitecturePath(repoRoot, qid);
}

function escapeRegExp(s: string): string {
  return s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

function cell(s: string | undefined): string {
  // Escape only UNESCAPED pipes: a TeX norm `\|x\|` in a description would
  // otherwise become `\\|x\\|` — a row break plus a table-splitting pipe.
  return (s ?? "—").replace(/(?<!\\)\|/g, "\\|").replace(/\n/g, " ").trim() || "—";
}

/**
 * Upsert one entry into the ledger. Creates the file (with header) if absent;
 * removes any prior block with the same `qid:source` key before appending
 * the fresh one (idempotent across re-runs).
 */
export function recordMissingArchitecture(
  ledgerPath: string,
  entry: MissingArchEntry,
): void {
  fs.mkdirSync(path.dirname(ledgerPath), { recursive: true });
  const lockPath = `${ledgerPath}.lock`;
  if (!fs.existsSync(lockPath)) fs.writeFileSync(lockPath, "{}\n", { flag: "a" });
  const release = lockLedgerSync(lockPath);
  try {
    // why: concurrent qids upsert shared ledger blocks without lost updates.
    recordMissingArchitectureUnlocked(ledgerPath, entry);
  } finally {
    release();
  }
}

function recordMissingArchitectureUnlocked(
  ledgerPath: string,
  entry: MissingArchEntry,
): void {
  const key = `${entry.qid}:${entry.source}`;
  const begin = `<!-- BEGIN ${key} -->`;
  const end = `<!-- END ${key} -->`;

  let body = fs.existsSync(ledgerPath)
    ? fs.readFileSync(ledgerPath, "utf8")
    : HEADER;

  // Strip any existing block for this key.
  const re = new RegExp(
    `\\n*${escapeRegExp(begin)}[\\s\\S]*?${escapeRegExp(end)}\\n*`,
    "g",
  );
  body = body.replace(re, "\n");

  const rows = entry.items
    .map((i) => `| ${cell(i.id)} | ${cell(i.kind)} | ${cell(i.description)} | ${cell(i.effort)} |`)
    .join("\n");

  const block = [
    begin,
    `## ${entry.qid} — ${entry.source} (${entry.date})`,
    "| id | kind | description | effort |",
    "|----|------|-------------|--------|",
    rows,
    end,
  ]
    .filter((l) => l !== "")
    .join("\n");

  fs.writeFileSync(ledgerPath, `${body.trimEnd()}\n\n${block}\n`);
}
