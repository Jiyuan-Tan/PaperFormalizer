import { describe, expect, it } from "vitest";
import { earlierFindingsBlock, withFindings } from "../../src/verify/fixer_history.js";

describe("fixer history", () => {
  it("shows a node's earlier findings next to the current one, once each", () => {
    let h = withFindings({}, 1, [{ id: "thm:a", axis: "correctness", detail: "v2 omits the superpopulation term.", witness: "p=1/2" }]);
    h = withFindings(h, 1, [{ id: "thm:a", axis: "correctness", detail: "v2 omits the superpopulation term.", witness: "p=1/2" }]);
    h = withFindings(h, 2, [{ id: "thm:a", axis: "patch rejected", detail: "the noise term is incomplete.", witness: null }, { id: "run", axis: "x", detail: "y" }]);
    expect(h["thm:a"]).toHaveLength(2);
    expect(h.run).toBeUndefined();
    const block = earlierFindingsBlock(h, [{ id: "thm:a", axis: "patch rejected", detail: "the noise term is incomplete." }]);
    expect(block).toBe("- thm:a (round 1, correctness): v2 omits the superpopulation term. Witness: p=1/2");
    expect(earlierFindingsBlock(h, [{ id: "thm:b", axis: "correctness", detail: "z" }])).toBe("");
  });
  it("shows a node with two current findings once, and none for a node the owner ruled on", () => {
    const h = withFindings({}, 1, [{ id: "thm:a", axis: "correctness", detail: "old", witness: null }]);
    const two = [{ id: "thm:a", axis: "correctness", detail: "new error" }, { id: "thm:a", axis: "ambiguity", detail: "new reading" }];
    expect(earlierFindingsBlock(h, two)).toBe("- thm:a (round 1, correctness): old");
    expect(earlierFindingsBlock(h, two, new Set(["thm:a"]))).toBe("");
  });
});
