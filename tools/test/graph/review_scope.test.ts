import { describe, it, expect } from "vitest";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge, addAssumption, setNodeReview } from "../../src/graph/mutate.js";
import { reviewTargets, convergenceTargets, incrementalSymbolRows, basisAllowsReview, recordReview, reviewBasisHash } from "../../src/graph/review_scope.js";
import { GraphSchema } from "../../src/graph/types.js";
import { dirtyFrontier } from "../../src/graph/diff.js";
import { statementHash } from "../../src/graph/hash.js";

/** A from-note theorem node carrying an as-persisted review block (pre-schema-parse). */
const node = (id: string, review: { status: string; passed_hash: string | null }) => ({
  id,
  kind: "theorem",
  provenance: "from-note",
  nl: { statement: id, tex_anchor: "", frozen: true },
  lean: { decl_name: null, file: null },
  review,
  proof: { state: "sorry", sorry_count: 1 },
});

function fixture() {
  let g = createEmptyGraph("q");
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });
  g = addNode(g, { id: "l1", kind: "lemma", provenance: "from-note", nl_statement: "helper t1 uses", tex_anchor: "" });
  g = addNode(g, { id: "l9", kind: "lemma", provenance: "agent-introduced", nl_statement: "orphan helper", tex_anchor: "" });
  g = addEdge(g, { kind: "proof-uses", from: "t1", to: "l1", source: "declared" }); // t1 uses l1
  // a2 = a NEW assumption on l1 (which t1 uses) → in t1's uses-closure
  g = addAssumption(g, { node: "l1", id: "a2", statement: "bounded", tier: 2, classification: "regularity-bookkeeping", anchor: "", provenance: "agent-introduced" });
  // a7 = an assumption on the ORPHAN l9 (no frozen theorem uses it)
  g = addAssumption(g, { node: "l9", id: "a7", statement: "x", tier: 2, classification: "faithful-refinement", anchor: "", provenance: "agent-introduced" });
  return g;
}

describe("reviewTargets", () => {
  it("targets dirty frozen theorems, new assumptions in their uses-closure, and from-note definitions — never agent-introduced or library objects", () => {
    const t = reviewTargets(fixture(), ["t1"]); // a2/a7 are unreviewed by construction
    expect(t.statementTargets).toEqual(["t1"]);
    expect(t.assumptionTargets).toContain("a2"); // a2 on l1, which t1 uses → in closure
    expect(t.assumptionTargets).not.toContain("a7"); // a7 on orphan l9 → not in any frozen closure

    let g = createEmptyGraph("q");
    g = addNode(g, { id: "t2", kind: "theorem", provenance: "agent-introduced", nl_statement: "aux", tex_anchor: "" });
    g = setNodeReview(g, "t2", "unreviewed", "");
    // a from-note definition is a paper object — checked even if reached only via a lemma
    g = addNode(g, { id: "p_tex", kind: "definition", provenance: "from-note", nl_statement: "the loss class", tex_anchor: "" });
    g = addNode(g, { id: "p_lib", kind: "definition", provenance: "library", nl_statement: "imported", tex_anchor: "" });
    g = addNode(g, { id: "p_aux", kind: "definition", provenance: "agent-introduced", nl_statement: "scaffold helper", tex_anchor: "" });
    const u = reviewTargets(g, ["t2"]);
    expect(u.statementTargets).toEqual([]);
    expect(u.definitionTargets).toEqual(["p_tex"]);
  });

  it("reviews every paper assumption (one only a lemma uses included), so none stays unreviewed and re-dirties a result every round", () => {
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "lem", kind: "lemma", provenance: "from-note", nl_statement: "standalone lemma", tex_anchor: "" });
    g = addNode(g, { id: "ass", kind: "assumption", provenance: "from-note", nl_statement: "exchangeable units", tex_anchor: "" });
    g = addEdge(g, { kind: "statement-uses", from: "lem", to: "ass", source: "extracted" });
    expect(dirtyFrontier(g, {})).toEqual(["ass", "lem"]);
    const t = reviewTargets(g, dirtyFrontier(g, {}));
    expect(t.assumptionTargets).toEqual(["ass"]);
    expect(t.lemmaTargets).toEqual(["lem"]);
    expect(convergenceTargets(g).assumptionTargets).toEqual(["ass"]);
    // Every paper node is reviewed, even one nothing uses; agent scaffolding outside every closure is not.
    g = addNode(g, { id: "unused", kind: "assumption", provenance: "from-note", nl_statement: "a standing convention", tex_anchor: "" });
    g = addNode(g, { id: "scaffold", kind: "assumption", provenance: "agent-introduced", nl_statement: "aux", tex_anchor: "" });
    expect(reviewTargets(g, []).assumptionTargets).toEqual(["ass", "unused"]);
    expect(convergenceTargets(g).assumptionTargets).toEqual(["ass", "unused"]);
    g = { ...g, nodes: g.nodes.filter((n) => n.id !== "unused" && n.id !== "scaffold") };
    // Once both pass at their hashes, nothing is dirty.
    const h = (id: string) => statementHash(g.nodes.find((n) => n.id === id)!.nl.statement);
    g = setNodeReview(setNodeReview(g, "ass", "matched", h("ass")), "lem", "matched", h("lem"));
    expect(dirtyFrontier(g, {})).toEqual([]);
  });

  it("keeps an undelivered theorem out of F2.5 statement review but includes it in the F4 delivery-role audit", () => {
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });
    g = addNode(g, { id: "t2", kind: "theorem", provenance: "from-note", nl_statement: "secondary", tex_anchor: "" });
    g = {
      ...g,
      nodes: g.nodes.map((n) => n.id === "t2" ? {
        ...n,
        delivery: { status: "undelivered", role: "secondary", reason: "citation overflow" },
      } : n),
    };
    expect(reviewTargets(g, ["t1", "t2"]).statementTargets).toEqual(["t1"]);
    expect(reviewTargets(g, ["t1", "t2"]).deliveryTargets).toEqual([]);
    expect(convergenceTargets(g).statementTargets).toEqual(["t1"]);
    expect(convergenceTargets(g).deliveryTargets).toEqual(["t2"]);
  });

  it("only `matched` clears a node — the retired `derived` status is no graph status at all", () => {
    // An F2 reroute that edited nothing leaves the flagged node CLEAN (not dirty) at the same hash,
    // so a status that clears without being a pass would let it slip the gate. `derived` used to
    // clear; it is refused on load, and a `drift` node stays in scope.
    expect(() => GraphSchema.parse({ qid: "q", nodes: [node("t1", { status: "derived", passed_hash: "h" })], edges: [] })).toThrow();
    const legacy = GraphSchema.parse({
      qid: "q",
      nodes: [
        node("t1", { status: "drift", passed_hash: "h" }),
        node("t2", { status: "drift", passed_hash: "h" }),
        node("t3", { status: "matched", passed_hash: "h" }),
      ],
      edges: [],
    });
    expect(reviewTargets(legacy, []).statementTargets).toEqual(["t1", "t2"]);
  });
});

describe("incrementalSymbolRows — symbol-tier incremental review", () => {
  const isPass = (v: string) => v === "matched" || v === "equivalent" || v === "untagged";
  const built = [
    { id: "sym:Y", hash: "hY" },
    { id: "sym:Z", hash: "hZ" },
    { id: "sym:P", hash: "hP" },
  ];

  type Prior = Record<string, { verdict: string; hash: string }> | undefined;
  it.each<{ label: string; prior: Prior; expected: string[] }>([
    { label: "a first pass (no prior state) reviews every symbol", prior: undefined, expected: ["sym:Y", "sym:Z", "sym:P"] },
    {
      label: "a delta skips symbols whose cluster is unchanged and whose last verdict passed (untagged counts as a pass)",
      prior: { "sym:Y": { verdict: "matched", hash: "hY" }, "sym:Z": { verdict: "untagged", hash: "hZ" } },
      expected: ["sym:P"],
    },
    {
      label: "a delta re-reviews a drifted symbol even if unchanged, and a passed one whose cluster hash changed",
      prior: {
        "sym:Y": { verdict: "drift", hash: "hY" },
        "sym:Z": { verdict: "matched", hash: "stale" },
        "sym:P": { verdict: "matched", hash: "hP" },
      },
      expected: ["sym:Y", "sym:Z"],
    },
  ])("$label", ({ prior, expected }) => {
    expect(incrementalSymbolRows(built, prior, isPass).map((s) => s.id)).toEqual(expected);
  });
});

describe("review basis — a node is reviewed once per basis, not once per pass", () => {
  const b1 = reviewBasisHash(["nl", "lean v1"]);
  const b2 = reviewBasisHash(["nl", "lean v2"]);
  it("a first review, or a changed basis, is dispatched; an unchanged one only while under the allowance", () => {
    expect(basisAllowsReview(undefined, "t1", b1)).toBe(true);
    const once = recordReview({}, "t1", b1);
    expect(once.t1).toEqual({ basis: b1, reviews: 1 });
    expect(basisAllowsReview(once, "t1", b1)).toBe(false); // the standing verdict holds
    expect(basisAllowsReview(once, "t1", b1, 2)).toBe(true); // the one reviewer-flip re-review
    expect(basisAllowsReview(recordReview(once, "t1", b1), "t1", b1, 2)).toBe(false); // never a third
    expect(basisAllowsReview(once, "t1", b2)).toBe(true); // the Lean (or NL, pins, rulings) changed
  });
  it("a changed basis restarts the count and drops the reroute mark; an unchanged one keeps it", () => {
    const rerouted = { t1: { basis: b1, reviews: 2, rerouted: b1 } };
    expect(recordReview(rerouted, "t1", b1).t1).toEqual({ basis: b1, reviews: 3, rerouted: b1 });
    expect(recordReview(rerouted, "t1", b2).t1).toEqual({ basis: b2, reviews: 1 });
  });
});
