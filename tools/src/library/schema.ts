/**
 * Library-index schema for a library that ships a per-declaration index
 * (`doc/library_index.json` at its package root, produced by the library's own index exe)
 * and optional per-area review sidecars (`doc/library_review/<Area>.json`: headline-theorem
 * lists and review stamps whose semantics are "the NL translation faithfully renders this
 * formal statement at this hash"). Retrieval reads indices at any path through
 * `library/sources.ts` + `loadLibraryLenient`.
 */

export interface LibDecl {
  name: string;
  kind: string; // def | theorem | structure | class | inductive | instance | axiom | opaque
  module: string;
  file: string;
  line: number;
  statement: string;
  /** Verbatim declaration source (definition-like kinds; null for theorems). */
  source?: string | null;
  doc: string | null;
  refs: string[];
  /** Proof-term dependencies (premises used in theorem proofs), disjoint from statement refs. */
  proofRefs: string[];
  axioms: string[];
  usesSorry: boolean;
}

export interface ReviewEntry {
  decl: string;
  statement_hash: string;
  reviewed_at_commit: string;
  reviewer: string;
  note?: string;
}

export interface AreaSidecar {
  headline_theorems: string[];
  reviews: ReviewEntry[];
  flags: { decl: string; note: string; flagged_at_commit: string }[];
  /** Curated description for an area-root explorer page. */
  intro?: string;
  /** Curated descriptions for nested explorer pages, keyed below the area. */
  namespace_intros?: Record<string, string>;
}

export interface Library {
  commit: string;
  toolchain: string;
  entries: LibDecl[];
  /** module name → module docstring (null when the file has none) */
  modules: Record<string, string | null>;
  sidecars: Record<string, AreaSidecar>; // keyed by area
}

/** Top-level library area of a decl (`<Lib>/PO/Core/System.lean` → `PO`). */
export function declArea(d: LibDecl): string {
  const parts = d.file.split("/");
  return parts.length > 2 ? parts[1] : "Root";
}

const TIER1_KINDS = new Set(["def", "structure", "class", "inductive", "axiom"]);

/** Tier-1 = trust anchors: every definition-like decl + sidecar-listed headline theorems. */
export function isTier1(d: LibDecl, sidecars: Record<string, AreaSidecar>): boolean {
  if (TIER1_KINDS.has(d.kind)) return true;
  return (sidecars[declArea(d)]?.headline_theorems ?? []).includes(d.name);
}
