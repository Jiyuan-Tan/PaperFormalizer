// What moved in the typed core since the plan on disk was written — the WHAT CHANGED block of an
// F1 re-plan. F1 records the core it planned from (`planCorePath`) with every schema-valid plan;
// a later F1 pass (after a rewind through V1/V1.5) diffs the current core against that record, so
// the planner starts from the nodes that changed instead of re-deriving them by diffing the plan
// against the whole core.

import type { Core } from "../core/schema.js";

type Rec = Record<string, unknown>;

/** Derived or locator-only fields: their changes follow from the fields shown. */
const QUIET_FIELDS = new Set(["used_by", "tex_locator"]);
/** Long fields a plan does not map one-to-one: reported as changed, without their text. */
const TEXT_ELIDED = new Set(["proof_tex"]);

const show = (v: unknown): string => JSON.stringify(v ?? null);
const same = (a: unknown, b: unknown): boolean => JSON.stringify(a ?? null) === JSON.stringify(b ?? null);

/** A changed list of ids (`depends_on`, `refs`, …) as what left and what came, not both lists whole. */
function listChange(prev: unknown, cur: unknown): string | null {
  const ids = (x: unknown): string[] | null => (Array.isArray(x) && x.every((v) => typeof v === "string") ? (x as string[]) : null);
  const a = ids(prev);
  const b = ids(cur);
  if (!a || !b) return null;
  const removed = a.filter((v) => !b.includes(v));
  const added = b.filter((v) => !a.includes(v));
  if (removed.length + added.length === 0) return "reordered";
  return [removed.length > 0 ? `removed ${show(removed)}` : "", added.length > 0 ? `added ${show(added)}` : ""].filter(Boolean).join(", ");
}

function fieldLines(prev: Rec, cur: Rec): string[] {
  const keys = [...new Set([...Object.keys(prev), ...Object.keys(cur)])].filter((k) => !QUIET_FIELDS.has(k));
  return keys
    .filter((k) => !same(prev[k], cur[k]))
    .map((k) => (TEXT_ELIDED.has(k) ? `    ${k}: changed` : `    ${k}: ${listChange(prev[k], cur[k]) ?? `${show(prev[k])} → ${show(cur[k])}`}`));
}

/** `full`: print an added record whole (a symbol — a revise shows no symbol table); a node is
 *  named only, its record being among the affected nodes the revise shows in full. */
function listDelta(label: string, key: string, prev: Rec[], cur: Rec[], full = false): string[] {
  const before = new Map(prev.map((x) => [String(x[key]), x] as const));
  const after = new Map(cur.map((x) => [String(x[key]), x] as const));
  const out: string[] = [];
  for (const [id, x] of after) {
    const old = before.get(id);
    if (!old) {
      const shown = Object.fromEntries(Object.entries(x).filter(([k]) => !QUIET_FIELDS.has(k) && !TEXT_ELIDED.has(k)));
      out.push(full ? `- added ${label} ${id}: ${JSON.stringify(shown)}` : `- added ${label} ${id}`);
      continue;
    }
    const lines = fieldLines(old, x);
    if (lines.length > 0) out.push(`- changed ${label} ${id}:`, ...lines);
  }
  for (const id of before.keys()) if (!after.has(id)) out.push(`- removed ${label} ${id}`);
  return out;
}

/** One line per added / removed / changed node, symbol or sampling-model setting (old → new per
 *  changed field); empty when the core is unchanged. */
export function coreDeltaLines(prev: Core, cur: Core): string[] {
  const p = prev as unknown as Rec;
  const c = cur as unknown as Rec;
  const arr = (x: unknown): Rec[] => (Array.isArray(x) ? (x as Rec[]) : []);
  const rec = (x: unknown): Rec => (x && typeof x === "object" && !Array.isArray(x) ? (x as Rec) : {});
  const out = [
    ...listDelta("symbol", "name", arr(p.symbols), arr(c.symbols), true),
    ...listDelta("assumption", "id", arr(p.assumptions), arr(c.assumptions)),
    ...listDelta("definition", "id", arr(p.definitions), arr(c.definitions)),
    ...listDelta("statement", "id", arr(p.statements), arr(c.statements)),
  ];
  const settings = fieldLines(rec(p.sampling_model), rec(c.sampling_model));
  if (settings.length > 0) out.push("- changed sampling_model:", ...settings);
  for (const k of ["estimand_functional", "target_estimand"]) {
    if (!same(p[k], c[k])) out.push(`- changed ${k}: ${show(p[k])} → ${show(c[k])}`);
  }
  return out;
}

/** The re-plan's WHAT CHANGED block. `prev` null: no record of the core the plan was written from
 *  (a plan older than the record), so the planner is told to compare. Empty when nothing moved. */
export function whatChangedBlock(prev: Core | null, cur: Core): string {
  const head = "=== WHAT CHANGED IN THE CORE SINCE THE PLAN WAS WRITTEN ===";
  if (!prev) {
    return `${head}\nNo record of the core the plan on disk was written from: compare the plan with the typed core below to find what moved.\n`;
  }
  const lines = coreDeltaLines(prev, cur);
  if (lines.length === 0) return "";
  return [
    head,
    "The plan on disk was written from an earlier core. These are ALL the differences (old → new);",
    "every other node, symbol and setting is unchanged; the record of an added or changed node is",
    "among the affected nodes below. Patch the plan entries of these nodes and of the nodes whose",
    "`depends_on` reaches them.",
    "",
    ...lines,
    "",
  ].join("\n");
}
