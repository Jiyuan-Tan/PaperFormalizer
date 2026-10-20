import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addEdge, addNode } from "../../src/graph/mutate.js";

describe("mutate", () => {
  it("addNode inserts a node and rejects duplicate ids", () => {
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "l7", kind: "lemma", provenance: "agent-introduced", nl_statement: "helper bound", tex_anchor: "" });
    expect(g.nodes.map((n) => n.id)).toEqual(["l7"]);
    expect(g.nodes[0].provenance).toBe("agent-introduced");
    expect(g.nodes[0].nl.frozen).toBe(false); // agent-introduced ⇒ not frozen
    expect(() => addNode(g, { id: "l7", kind: "lemma", provenance: "agent-introduced", nl_statement: "x", tex_anchor: "" })).toThrow(/duplicate/i);
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "tex:L1" });
    expect(g.nodes[1].nl.frozen).toBe(true); // from-note ⇒ frozen NL
  });

  it("addEdge rejects when an endpoint is missing", () => {
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
    expect(() => addEdge(g, { kind: "proof-uses", from: "t1", to: "l9", source: "declared" })).toThrow(/endpoint/i);
  });

  it("addEdge de-duplicates identical edges", () => {
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
    g = addNode(g, { id: "l1", kind: "lemma", provenance: "from-note", nl_statement: "h", tex_anchor: "" });
    g = addEdge(g, { kind: "proof-uses", from: "t1", to: "l1", source: "declared" });
    g = addEdge(g, { kind: "proof-uses", from: "t1", to: "l1", source: "declared" });
    expect(g.edges).toHaveLength(1);
  });
});
