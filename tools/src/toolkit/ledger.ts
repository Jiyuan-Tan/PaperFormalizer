// The toolkit provenance ledger, `<toolkit>/doc/ledger.json`: one record per declaration that
// entered the toolkit (where it came from, when, and on whose decision), plus the owner's
// proposal decisions. Writes are atomic (temp file + rename).
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import { z } from "zod";
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

/**
 * Append owner decision records to `decisions[]` (load, append, save; atomic). Idempotent: a
 * record whose `keyOf` matches an existing record is skipped, so a re-run apply never duplicates.
 */
export async function appendDecisionRecords<T extends object>(
  ledgerPath: string,
  records: readonly T[],
  keyOf: (record: unknown) => string | null,
): Promise<{ added: T[]; skipped: T[] }> {
  const ledger = await loadLedger(ledgerPath);
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
  if (added.length > 0) await saveLedger(ledgerPath, { ...ledger, decisions: [...ledger.decisions, ...added] });
  return { added, skipped };
}
