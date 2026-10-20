// The class of a hypothesis the proof stage added is the reviewers', not the filler's own: the graph
// keeps it and the report reads it there (a `substrate-gate` makes the result conditional).
import { describe, expect, it } from "vitest";
import { withReviewedAssumptionClasses } from "../../src/formalization/proof_reviewer.js";
import { reviewedAssumptionClasses } from "../../src/formalization/reviewer_verdicts.js";
import type { FormalizationGraph } from "../../src/graph/types.js";

const node = (id: string, classification: string, over: Record<string, unknown> = {}) => ({
  id, kind: "assumption", provenance: "agent-introduced", nl: { statement: "s", tex_anchor: "", frozen: false },
  lean: { decl_name: null, file: null }, review: { status: "unreviewed", passed_hash: null }, proof: { state: "complete", sorry_count: 0 },
  assumption: { tier: 2, classification }, ...over,
});

describe("the reviewers' class of an added hypothesis", () => {
  it("is read off the passing assumption verdicts; of two reviewers, the one leaving more owed", () => {
    const got = reviewedAssumptionClasses([
      { id: "ass:a", verdict: "regularity-bookkeeping" }, { id: "ass:a", verdict: "substrate-gate" },
      { id: "ass:b", verdict: "faithful-refinement" }, { id: "ass:c", verdict: "content-gate" }, { id: "", verdict: "substrate-gate" },
    ]);
    expect([...got]).toEqual([["ass:a", "substrate-gate"], ["ass:b", "faithful-refinement"]]);
  });
  it("replaces the filler's own class on the node, by node id or reviewer-facing id", () => {
    const graph = { qid: "q", nodes: [node("ass:filler:1", "regularity-bookkeeping", { obj_id: "A-9" }), node("ass:filler:2", "substrate-gate"), { ...node("thm:t", "x"), kind: "theorem" }], edges: [] } as unknown as FormalizationGraph;
    const out = withReviewedAssumptionClasses(graph, new Map([["A-9", "substrate-gate"], ["ass:filler:2", "faithful-refinement"], ["thm:t", "substrate-gate"]]) as never);
    expect(out.nodes.map((n) => (n as { assumption?: { classification: string } }).assumption?.classification)).toEqual(["substrate-gate", "faithful-refinement", "x"]);
    expect(withReviewedAssumptionClasses(graph, new Map())).toBe(graph);
  });
});
