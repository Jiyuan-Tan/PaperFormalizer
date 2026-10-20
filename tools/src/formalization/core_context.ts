import { readFile } from "node:fs/promises";
import { formalizationView, parseTypedCore } from "../core/core_io.js";
import type { Core } from "../core/schema.js";
import { bindingReadingItem, bindingReadings } from "../verify/core_graph.js";

/** The key under which a node's binding readings follow its text in a prompt's core JSON. */
export const BINDING_READINGS_KEY = "pinned_readings_binding";

/** The one sentence that tells an F stage what `pinned_readings_binding` means. */
export const BINDING_READINGS_NOTE =
  `A node's \`${BINDING_READINGS_KEY}\` lists the readings the referee pinned for its ambiguous wording (and conditions it appended): they are BINDING — formalize the node under them, never under another reading.`;

/** The one sentence that tells an F stage how a symbol entry of the core reads. */
export const SCOPED_SYMBOLS_NOTE =
  "A symbol's `def` is its meaning wherever it is used; each of its `scoped` entries `{results, text}` additionally holds of it in the listed results only.";

/**
 * Put each node's binding readings (`bindingReadings`: pinned readings and bookkeeping conditions
 * V1.5 appended) right after its text, under `pinned_readings_binding`: all of them for a
 * statement, a node's own pins for an assumption or definition. Nodes without any are unchanged.
 */
export function withBindingReadings(core: Core, projected: Record<string, unknown>): Record<string, unknown> {
  const annotate = (list: unknown, textKey: string, ownOnly: boolean): unknown =>
    Array.isArray(list)
      ? list.map((value) => {
          const node = value as Record<string, unknown>;
          const readings = bindingReadings(core, String(node.id), { ownOnly });
          if (readings.length === 0) return node;
          const out: Record<string, unknown> = {};
          for (const [k, v] of Object.entries(node)) {
            out[k] = v;
            if (k === textKey) out[BINDING_READINGS_KEY] = readings.map(bindingReadingItem);
          }
          if (!(BINDING_READINGS_KEY in out)) out[BINDING_READINGS_KEY] = readings.map(bindingReadingItem);
          return out;
        })
      : list;
  return {
    ...projected,
    statements: annotate(projected.statements, "statement", false),
    assumptions: annotate(projected.assumptions, "condition", true),
    definitions: annotate(projected.definitions, "construction", true),
  };
}

/** How a scoped packet tells its reader that the readings are printed once (`shareBindingReadings`). */
export const SHARED_READINGS_NOTE =
  `A node's \`${BINDING_READINGS_KEY}\` lists the ids of the readings the referee pinned for its ambiguous wording (and of conditions it appended); each reading is printed once, under \`binding_readings\`. They are BINDING — formalize the node under them, never under another reading. \`hypothesis_texts\` gives, by id, the text of each hypothesis a shown statement takes whose record is not shown.`;

/**
 * The records of a view with each node's binding readings cut to their ids, and the readings once,
 * by id: a reading several of the nodes share was printed in full under each. Pure.
 */
export function shareBindingReadings(nodes: ReadonlyArray<Record<string, unknown>>): { nodes: Record<string, unknown>[]; readings: Record<string, string> } {
  const readings: Record<string, string> = {};
  const out = nodes.map((node) => {
    const items = node[BINDING_READINGS_KEY];
    if (!Array.isArray(items)) return node;
    const ids = (items as string[]).map((item) => {
      const id = item.slice(0, item.indexOf(" ("));
      readings[id] = item.slice(id.length + 1);
      return id;
    });
    return { ...node, [BINDING_READINGS_KEY]: ids };
  });
  return { nodes: out, readings };
}

/** Remove fields that F1.5/F2 never need while preserving the typed structure. */
export function formalizationCoreContextValue(core: Core): Record<string, unknown> {
  const projected = structuredClone(core) as unknown as Record<string, unknown>;
  for (const key of [
    "tldr",
    "project_justification",
    "related_work",
    "interpretation",
    "technical_internal_limitation",
    "statement_notes",
    "comparator_promise_table",
    "bibliography",
  ]) delete projected[key];
  if (Array.isArray(projected.statements)) {
    projected.statements = projected.statements.map((value) => {
      const statement = { ...(value as Record<string, unknown>) };
      delete statement.proof_tex;
      delete statement.justification;
      delete statement.gap;
      delete statement.consumer;
      return statement;
    });
  }
  return withBindingReadings(core, projected);
}

/** The F1 planner's core view: the slim view plus the bibliography entries a node cites (F1
 *  mints the plan's `citations[]` from them); the rest of the bibliography is positioning. F1
 *  used to get the whole core — proof bodies and all, 1.7× the slim view — on every pass. */
export function plannerCoreContextValue(core: Core): Record<string, unknown> {
  const cited = new Set<string>();
  for (const s of core.statements) if (s.source?.cite) cited.add(s.source.cite);
  for (const a of core.assumptions) if ("standard" in a && a.standard?.cite) cited.add(a.standard.cite);
  const bibliography = (core.bibliography ?? []).filter((b) => cited.has(b.key));
  const projected = formalizationCoreContextValue(core);
  return bibliography.length > 0 ? { ...projected, bibliography } : projected;
}

/** The view cut down to the nodes in `ids` (an F1 revise shows only the affected nodes; the
 *  rest of the core stays on disk for the planner to Read). Symbols and settings are left out. */
export function restrictCoreContextValue(view: Record<string, unknown>, ids: ReadonlySet<string>): Record<string, unknown> {
  const keep = (list: unknown): unknown =>
    Array.isArray(list) ? list.filter((n) => ids.has(String((n as { id?: unknown }).id))) : list;
  return {
    qid: view.qid,
    assumptions: keep(view.assumptions),
    definitions: keep(view.definitions),
    statements: keep(view.statements),
  };
}

/** Structural core view for F1.5 reuse-fit and F2 scaffolding. These stages
 * need exact declarations and dependency metadata, not the completed paper's
 * proof bodies, positioning prose (per-statement justification/gap/consumer,
 * the comparator table), or bibliography (F2's cited-gate docstrings come from
 * the plan's `citations[]`, which F1 mints from the raw core). Parse first so
 * projection never hides a malformed/missing core. PROMPT-ONLY: this string is
 * never persisted; later stages read core.json itself. Serialized compact —
 * indentation was ~11% of the F2/F1.5 prompt bytes. */
export async function readFormalizationCoreContext(
  corePath: string,
  label: string,
): Promise<string> {
  let raw: string;
  try {
    raw = await readFile(corePath, "utf8");
  } catch (err) {
    throw new Error(`${label}: required typed core is unreadable at ${corePath}: ${err instanceof Error ? err.message : String(err)}`);
  }
  const core = formalizationView(parseTypedCore(raw, `${label}: typed core ${corePath}`));
  return JSON.stringify(formalizationCoreContextValue(core));
}
