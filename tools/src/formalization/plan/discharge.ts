// Deterministic plan rewrites for declarations that exist outside the F stages: a round-A
// promotion found a plan node's result already in the toolkit or a base library (`proposals/apply_a.ts`).

/**
 * Point plan nodes at declarations that exist upstream: each named node becomes a
 * `lean_kind:"lemma"` with `defer_tier:false`, the module added, the gate keys cleared and the
 * node dropped from every node's `hyps`. An ordinary node becomes `disposition:"reuse"` of the
 * declaration. A `gate_class:"cited"` gate instead takes the PROVED form the plan gate and the
 * delivery audit accept for a cited result (`disposition:"define-local"`, `citation_discharged`,
 * `source` kept): a reuse would emit nothing locally for F2.5 to match against the source, so
 * the declaration is named in `notes` as what the local proof invokes. Edits `planObj` in
 * place; false when it has no `nodes`.
 */
export function applyBuiltDeclsToPlan(
  planObj: unknown,
  builtDecls: ReadonlyArray<{ gate_id: string; decl_name: string; module: string; note?: string }>,
): boolean {
  const pj = planObj as { nodes?: Record<string, Record<string, unknown>> };
  if (!pj || typeof pj !== "object" || !pj.nodes) return false;
  for (const d of builtDecls) {
    const node = pj.nodes[d.gate_id];
    if (node) {
      const cited = node.gate_class === "cited";
      delete node.gate;
      delete node.gate_class;
      node.lean_kind = "lemma";
      const mods = Array.isArray(node.modules) ? (node.modules as string[]) : [];
      node.modules = mods.includes(d.module) ? mods : [...mods, d.module];
      node.defer_tier = false;
      const notes: string[] = [typeof node.notes === "string" && node.notes ? node.notes : ""];
      if (cited) {
        node.citation_discharged = true;
        node.disposition = "define-local";
        node.reuse = null;
        notes.push(`proved locally from ${d.decl_name} (${d.module})`);
      } else {
        node.disposition = "reuse";
        node.reuse = d.decl_name;
      }
      if (d.note) notes.push(d.note);
      const joined = notes.filter(Boolean).join(" | ");
      if (joined) node.notes = joined;
    }
    // Drop the discharged gate from every node's `hyps` (it is a proved lemma now).
    for (const n of Object.values(pj.nodes)) {
      if (Array.isArray(n.hyps)) n.hyps = (n.hyps as string[]).filter((h) => h !== d.gate_id);
    }
  }
  return true;
}
