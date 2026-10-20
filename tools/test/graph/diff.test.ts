import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge, markPassed } from "../../src/graph/mutate.js";
import { dirtyFrontier } from "../../src/graph/diff.js";
import { statementHash } from "../../src/graph/hash.js";

// t1 PROOF-uses l1 (a proof lemma) and STATEMENT-uses d1 (a def its statement references).
function chain() {
  let g = createEmptyGraph("q");
  g = addNode(g, { id: "l1", kind: "lemma", provenance: "from-note", nl_statement: "h", tex_anchor: "" });
  g = addNode(g, { id: "d1", kind: "definition", provenance: "from-note", nl_statement: "def", tex_anchor: "" });
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
  g = addEdge(g, { kind: "proof-uses", from: "t1", to: "l1", source: "declared" }); // proof-level dep
  g = addEdge(g, { kind: "statement-uses", from: "t1", to: "d1", source: "extracted" }); // statement-level dep
  g = markPassed(g, "l1", "h_l1");
  g = markPassed(g, "d1", "h_d1");
  g = markPassed(g, "t1", "h_t1");
  return g;
}

describe("dirtyFrontier", () => {
  it("a changed PROOF-USES lemma marks ONLY itself — proof deps don't dirty the dependent's statement", () => {
    const g = chain();
    expect(dirtyFrontier(g, { l1: "h_l1_NEW", d1: "h_d1", t1: "h_t1" })).toEqual(["l1"]);
  });

  it("a changed STATEMENT-USES def marks itself AND the statement-dependent theorem", () => {
    const g = chain();
    expect(dirtyFrontier(g, { l1: "h_l1", d1: "h_d1_NEW", t1: "h_t1" }).sort()).toEqual(["d1", "t1"]);
  });

  it("a from-note node never passed (no passed_hash) is dirty (needs first review)", () => {
    let g = chain();
    g = addNode(g, { id: "l2", kind: "lemma", provenance: "from-note", nl_statement: "x", tex_anchor: "" });
    expect(dirtyFrontier(g, { l1: "h_l1", d1: "h_d1", t1: "h_t1", l2: "h_l2" })).toEqual(["l2"]);
  });

  it.each([
    ["never reviewed", null, "h_aux1"],
    ["carrying an orphaned prior hash whose tag vanished", "old-lean-statement-hash", undefined],
    ["whose statement changed", "old-hash", "new-hash"],
  ] as const)("an AGENT-INTRODUCED helper %s is never a dirty source and never dirties its user", (_label, passed, fresh) => {
    let g = chain();
    g = addNode(g, { id: "aux1", kind: "definition", provenance: "agent-introduced", nl_statement: "aux", tex_anchor: "" });
    g = addEdge(g, { kind: "statement-uses", from: "t1", to: "aux1", source: "extracted" });
    if (passed !== null) g = markPassed(g, "aux1", passed);
    const freshHashes: Record<string, string> = { l1: "h_l1", d1: "h_d1", t1: "h_t1" };
    if (fresh !== undefined) freshHashes.aux1 = fresh;
    expect(dirtyFrontier(g, freshHashes)).toEqual([]);
  });

  // Hypothesis-backed nodes (no standalone `@node:` decl → absent from freshHashes) fall back to
  // the hash of their NL statement: a legacy sentinel or a changed spec is dirty, a match is stable.
  it("a reviewed hypothesis-backed node is dirty unless passed_hash IS its current NL-statement hash", () => {
    const fresh = { l1: "h_l1", d1: "h_d1", t1: "h_t1" };
    const hyp = (nl: string, passed: string) =>
      markPassed(addNode(chain(), { id: "hyp1", kind: "assumption", provenance: "agent-introduced", nl_statement: nl, tex_anchor: "" }), "hyp1", passed);
    expect(dirtyFrontier(hyp("assume the budget", "reviewed"), fresh)).toEqual(["hyp1"]);
    expect(dirtyFrontier(hyp("new spec", statementHash("old spec")), fresh)).toEqual(["hyp1"]);
    expect(dirtyFrontier(hyp("new spec", statementHash("new spec")), fresh)).toEqual([]);
  });
});
