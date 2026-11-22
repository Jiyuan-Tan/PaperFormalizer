// The toolkit provenance ledger, `<toolkit>/doc/ledger.json`: one record per declaration that
// entered the toolkit (where it came from, when, and on whose decision), plus the owner's
// proposal decisions. Writes are atomic (temp file + rename); every read-modify-write goes through
// `updateLedger`, under the ledger's own lock, so two papers' writes never lose each other's records.
import { existsSync } from "node:fs";
import { mkdir, readFile, stat } from "node:fs/promises";
import path from "node:path";
import { z } from "zod";
import { withStoreLock } from "../shared/build_mutex.js";
import { writeTextAtomic } from "../shared/json_atomic.js";

export const ledgerDeclarationSchema = z.object({
  name: z.string().min(1),
  module: z.string().min(1),
  division: z.string().min(1),
  origin: z.object({
    kind: z.enum(["study", "proposal"]),
    slug: z.string().min(1),
    run_id: z.string().min(1).optional(),
  }).passthrough(),
  date: z.string().regex(/^\d{4}-\d{2}-\d{2}$/, "date must be YYYY-MM-DD"),
  decision: z.string().min(1),
  nearest_existing: z.array(z.string()).optional(),
  used_by: z.array(z.string()).default([]),
}).passthrough();
export type LedgerDeclaration = z.infer<typeof ledgerDeclarationSchema>;

export const ledgerSchema = z.object({
  version: z.literal(1),
  declarations: z.array(ledgerDeclarationSchema).default([]),
  decisions: z.array(z.unknown()).default([]),
}).passthrough();
export type Ledger = z.infer<typeof ledgerSchema>;

export function emptyLedger(): Ledger {
  return { version: 1, declarations: [], decisions: [] };
}

export function parseLedger(text: string, source = "ledger.json"): Ledger {
  let json: unknown;
  try {
    json = JSON.parse(text);
  } catch (err) {
    throw new Error(`cannot parse ${source}: ${err instanceof Error ? err.message : String(err)}`);
  }
  const parsed = ledgerSchema.safeParse(json);
  if (!parsed.success) {
    throw new Error(`invalid ${source}: ${parsed.error.issues.map((i) => `${i.path.join(".")}: ${i.message}`).join("; ")}`);
  }
  return parsed.data;
}

export function serializeLedger(ledger: Ledger): string {
  return `${JSON.stringify(ledger, null, 2)}\n`;
}

/**
 * Append declaration records. Idempotent: a record whose name, module and origin slug match an
 * existing one is skipped (a recovered, interrupted promotion re-appends the same entries).
 * A name already recorded under a DIFFERENT module is a conflict and throws.
 */
export function appendDeclarations(
  ledger: Ledger,
  entries: LedgerDeclaration[],
): { ledger: Ledger; added: LedgerDeclaration[]; skipped: LedgerDeclaration[] } {
  const declarations = [...ledger.declarations];
  const added: LedgerDeclaration[] = [];
  const skipped: LedgerDeclaration[] = [];
  for (const raw of entries) {
    const entry = ledgerDeclarationSchema.parse(raw);
    const prior = declarations.find((d) => d.name === entry.name);
    if (prior) {
      if (prior.module !== entry.module) {
        throw new Error(`ledger conflict: ${entry.name} is already recorded in ${prior.module}, not ${entry.module}`);
      }
      if (prior.origin.slug === entry.origin.slug) {
        skipped.push(entry);
        continue;
      }
      throw new Error(`ledger conflict: ${entry.name} is already recorded from ${prior.origin.kind} ${prior.origin.slug}`);
    }
    declarations.push(entry);
    added.push(entry);
  }
  return { ledger: { ...ledger, declarations }, added, skipped };
}

/** Load the ledger; a missing file reads as an empty ledger. */
export async function loadLedger(ledgerPath: string): Promise<Ledger> {
  if (!existsSync(ledgerPath)) return emptyLedger();
  return parseLedger(await readFile(ledgerPath, "utf8"), ledgerPath);
}

export async function saveLedger(ledgerPath: string, ledger: Ledger): Promise<void> {
  await writeTextAtomic(ledgerPath, serializeLedger(ledgerSchema.parse(ledger)));
}

/** The ledger's own lock, beside it (gitignored as `.toolkit-ledger.lock`): never the promotion
 *  lock, so recording a decision waits behind no paper's gate. */
export const LEDGER_LOCK_FILENAME = ".toolkit-ledger.lock";
export function ledgerLockPath(ledgerPath: string): string {
  return path.join(path.dirname(ledgerPath), LEDGER_LOCK_FILENAME);
}

/** Times a read-modify-write is redone when the file changed under it before giving up the check. */
const LEDGER_WRITE_RETRIES = 5;

/** The file's inode, size and mtime, or "absent" (every writer renames a new file over it). */
async function ledgerStamp(file: string): Promise<string> {
  const s = await stat(file, { bigint: true }).catch(() => null);
  return s ? `${s.ino}:${s.size}:${s.mtimeNs}` : "absent";
}

/**
 * Read the ledger, apply `fn`, write the ledger it returns (null: nothing to write) — all under the
 * ledger's lock. A writer that holds no lock (a process started before the ledger had one) is caught
 * as well: when the file's stamp changed between the read and the write, `fn` is applied again to
 * what is there now. `fn` must therefore build its result from the ledger it is given alone.
 */
export async function updateLedger<T>(
  ledgerPath: string,
  fn: (ledger: Ledger) => { ledger: Ledger | null; result: T },
  /** Called under the lock with the update's result just before it is written (e.g. a promotion's
   *  journal, written ahead); called again when the update is redone. */
  beforeWrite?: (result: T) => Promise<void>,
): Promise<T> {
  const lock = ledgerLockPath(ledgerPath);
  await mkdir(path.dirname(lock), { recursive: true });
  return withStoreLock(lock, async () => {
    for (let attempt = 0; ; attempt += 1) {
      const before = await ledgerStamp(ledgerPath);
      const { ledger, result } = fn(await loadLedger(ledgerPath));
      if (ledger === null) return result;
      await beforeWrite?.(result);
      if (attempt < LEDGER_WRITE_RETRIES && (await ledgerStamp(ledgerPath)) !== before) continue;
      await saveLedger(ledgerPath, ledger);
      return result;
    }
  });
}

/**
 * Append owner decision records to `decisions[]` (under `updateLedger`). Idempotent: a record
 * whose `keyOf` matches an existing record is skipped, so a re-run apply never duplicates.
 */
export async function appendDecisionRecords<T extends object>(
  ledgerPath: string,
  records: readonly T[],
  keyOf: (record: unknown) => string | null,
): Promise<{ added: T[]; skipped: T[] }> {
  return updateLedger(ledgerPath, (ledger) => {
    const seen = new Set(ledger.decisions.map(keyOf).filter((k): k is string => k !== null));
    const added: T[] = [];
    const skipped: T[] = [];
    for (const r of records) {
      const key = keyOf(r);
      if (key !== null && seen.has(key)) {
        skipped.push(r);
        continue;
      }
      if (key !== null) seen.add(key);
      added.push(r);
    }
    return { ledger: added.length > 0 ? { ...ledger, decisions: [...ledger.decisions, ...added] } : null, result: { added, skipped } };
  });
}

/** A declaration a promotion recorded in the ledger: its name and the slug it was recorded from. */
export interface LedgerAdded { name: string; slug: string }

/** Record declarations that entered the toolkit (`appendDeclarations`, under `updateLedger`).
 *  `beforeWrite` gets exactly the declarations this append adds, under the lock, before the write. */
export async function appendLedgerDeclarations(
  ledgerPath: string,
  entries: LedgerDeclaration[],
  beforeWrite?: (added: LedgerAdded[]) => Promise<void>,
): Promise<{ added: LedgerDeclaration[]; skipped: LedgerDeclaration[] }> {
  return updateLedger(ledgerPath, (ledger) => {
    const r = appendDeclarations(ledger, entries);
    return { ledger: r.added.length ? r.ledger : null, result: { added: r.added, skipped: r.skipped } };
  }, beforeWrite ? (r) => beforeWrite(r.added.map((e) => ({ name: e.name, slug: e.origin.slug }))) : undefined);
}

/** Undo a promotion's ledger records: drop each declaration of that name recorded from that slug,
 *  leaving every other record — another paper's appended since included. */
export async function removeLedgerDeclarations(ledgerPath: string, added: readonly LedgerAdded[]): Promise<number> {
  if (!added.length) return 0;
  const drop = new Set(added.map((a) => `${a.slug}\u0000${a.name}`));
  return updateLedger(ledgerPath, (ledger) => {
    const declarations = ledger.declarations.filter((d) => !drop.has(`${d.origin.slug}\u0000${d.name}`));
    const n = ledger.declarations.length - declarations.length;
    return { ledger: n ? { ...ledger, declarations } : null, result: n };
  });
}
