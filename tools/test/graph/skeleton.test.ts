import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge } from "../../src/graph/mutate.js";
import { graphDerivedSkeleton } from "../../src/graph/skeleton.js";

function g() {
  let x = createEmptyGraph("q");
  x = addNode(x, { id: "setup", kind: "setup", provenance: "from-note", nl_statement: "env", tex_anchor: "" });
  x = addNode(x, { id: "a1", kind: "assumption", provenance: "from-note", nl_statement: "ov", tex_anchor: "L5" });
  x = addNode(x, { id: "l1", kind: "lemma", provenance: "from-note", nl_statement: "h", tex_anchor: "" });
  x = addNode(x, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
  x = { ...x, nodes: x.nodes.map((n) => (n.id === "t1" ? { ...n, lean: { decl_name: "t1_thm", file: "T1.lean" } } : n)) };
  x = addEdge(x, { kind: "setup-of", from: "setup", to: "t1", source: "declared" });
  x = addEdge(x, { kind: "proof-uses", from: "t1", to: "a1", source: "declared" });
  x = addEdge(x, { kind: "statement-uses", from: "t1", to: "l1", source: "extracted" });
  return x;
}

describe("graphDerivedSkeleton", () => {
  it("projects P/L/T/A nodes to rows with the lean anchor and obj_id-resolved edges; skips setup", () => {
    const skel = graphDerivedSkeleton(g());
    const t1 = skel.find((e) => e.obj_id === "T-1")!;
    expect(t1.kind).toBe("theorem");
    expect(t1.lean?.decl).toBe("t1_thm");
    expect(skel.find((e) => e.obj_id === "setup")).toBeUndefined();
    expect(skel.find((e) => e.obj_id === "A-1")?.kind).toBe("assumption");
    // per-row dependency edges resolved to obj_ids
    expect(t1.uses).toEqual(["L-1"]); // statement-uses only
    expect(t1.proofUses).toEqual(["A-1"]); // proof-uses kept separate (not a statement-drift criterion)
    expect(t1.boundTo).toEqual(["setup"]);
    expect(skel.find((e) => e.obj_id === "A-1")!.usedBy).toEqual(["T-1"]);
  });
  it("keeps a case-sensitive exact T1 target distinct from legacy t1", () => {
    let x = createEmptyGraph("q");
    x = addNode(x, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "legacy", tex_anchor: "" });
    x = addNode(x, { id: "T1", kind: "theorem", provenance: "from-note", nl_statement: "exact", tex_anchor: "" });

    expect(graphDerivedSkeleton(x).map((row) => [row.graph_node_id, row.obj_id]).sort()).toEqual([
      ["T1", "T1"],
      ["t1", "T-1"],
    ]);
  });
});
