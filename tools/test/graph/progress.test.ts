import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge, setProof, setNodeReview } from "../../src/graph/mutate.js";
import { frozenClosuresComplete, frozenTheoremsProven } from "../../src/graph/progress.js";

function base() {
  let g = createEmptyGraph("q");
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
  g = addNode(g, { id: "l1", kind: "lemma", provenance: "agent-introduced", nl_statement: "helper", tex_anchor: "" });
  g = addEdge(g, { kind: "proof-uses", from: "t1", to: "l1", source: "declared" });
  return g;
}

describe("frozenClosuresComplete", () => {
  it("true when the frozen theorem is complete+matched and its (agent) helper is complete", () => {
    let g = base();
    g = setProof(g, "t1", "complete", 0);
    g = setNodeReview(g, "t1", "matched", "h");
    g = setProof(g, "l1", "complete", 0); // agent-introduced lemma: only proof needs completing
    expect(frozenClosuresComplete(g)).toBe(true);
  });

  it("false while the theorem is unproven or a helper in its closure still has a sorry", () => {
    let g = base();
    expect(frozenClosuresComplete(setProof(g, "t1", "sorry", 1))).toBe(false);
    g = setProof(g, "t1", "complete", 0);
    g = setNodeReview(g, "t1", "matched", "h");
    g = setProof(g, "l1", "sorry", 1);
    expect(frozenClosuresComplete(g)).toBe(false);
  });
});

describe("undelivered proof obligations", () => {
  it("requires delivered theorems but ignores a disclosed secondary theorem", () => {
    let g = base();
    g = setProof(g, "t1", "complete", 0);
    g = setNodeReview(g, "t1", "matched", "h");
    g = {
      ...g,
      nodes: g.nodes.map((n) => n.id === "t1"
        ? { ...n, lean: { decl_name: "main", file: "T.lean" } }
        : n).concat({
          id: "t2", kind: "theorem", provenance: "from-note",
          nl: { statement: "secondary atlas", tex_anchor: "", frozen: true },
          lean: { decl_name: null, file: null },
          review: { status: "unreviewed", passed_hash: null },
          proof: { state: "sorry", sorry_count: 0 },
          delivery: { status: "undelivered", role: "secondary", reason: "citation overflow" },
        }),
    };
    expect(frozenTheoremsProven(g)).toBe(true);
  });
});
