// Build the formalization dependency graph straight from a typed `core`.
//
// The core already encodes the graph implicitly: `statement.depends_on` is the
// proof DAG, `definition.by_member_properties` carves a class out of member-atoms,
// and `assumption.used_by` is the reverse edge. This module turns those fields into
// the explicit graph object the F-stages consume — so F1/F2 never re-extract
// structure from prose.
import { coreNodeIds, type Core } from "./schema.js";

export type CoreNodeKind =
  | "assumption"
  | "definition-class"
  | "definition-construction"
  | "statement";

export interface CoreDag {
  /** All addressable core node ids (assumptions ∪ definitions ∪ statements). */
  nodes: Set<string>;
  /** node id → its kind. */
  kindOf: Map<string, CoreNodeKind>;
  /** class def id → its member-atom ids (from `by_member_properties`). */
  classMembers: Map<string, string[]>;
}

/** Construct the explicit dependency graph from a typed core. Pure; no LLM. */
export function buildDagFromCore(core: Core): CoreDag {
  const nodes = coreNodeIds(core);

  const kindOf = new Map<string, CoreNodeKind>();
  for (const a of core.assumptions) kindOf.set(a.id, "assumption");
  for (const d of core.definitions) {
    kindOf.set(d.id, d.by_member_properties !== undefined ? "definition-class" : "definition-construction");
  }
  for (const s of core.statements) kindOf.set(s.id, "statement");

  const classMembers = new Map<string, string[]>();
  for (const d of core.definitions) {
    if (d.by_member_properties === undefined) continue;
    classMembers.set(d.id, d.by_member_properties);
  }

  return { nodes, kindOf, classMembers };
}
