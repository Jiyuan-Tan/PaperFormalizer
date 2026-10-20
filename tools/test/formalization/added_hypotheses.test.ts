import { describe, expect, it } from "vitest";
import { addedBinders, addedHypothesesBlock, recordPassedBinders } from "../../src/formalization/added_hypotheses.js";
import { statementBinders } from "../../src/formalization/unused_hypothesis_lint.js";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, markUnreviewed, setNodeReview } from "../../src/graph/mutate.js";

describe("statementBinders", () => {
  it("reads the bracketed binders before the result colon, comments and docstrings ignored, whitespace collapsed", () => {
    const decl = [
      "/-- Under (h : not a binder) the claim holds. -/",
      "@[simp] theorem Foo.bar {α : Type*} [Fintype α] (s : Finset α)",
      "    -- (hidden : False)",
      "    (hs : s.Nonempty)",
      "    (hsum : ∑ x ∈ s, (1 : ℕ) =",
      "      s.card) : 0 < s.card := by",
      "  exact hs.card_pos",
    ].join("\n");
    expect(statementBinders(decl)).toEqual(["{α : Type*}", "[Fintype α]", "(s : Finset α)", "(hs : s.Nonempty)", "(hsum : ∑ x ∈ s, (1 : ℕ) = s.card)"]);
  });
});

describe("addedBinders", () => {
  it("is empty with no record, and otherwise lists exactly the binders not in the passed signature", () => {
    const decl = "theorem t (n : Nat) (hn : 0 < n) (hextra : n < 5) : n ≠ 0 := by omega";
    expect(addedBinders({}, decl)).toEqual([]);
    expect(addedBinders({ passed_binders: ["(n : Nat)", "(hn : 0 < n)"] }, decl)).toEqual(["(hextra : n < 5)"]);
    // A retyped binder is a new hypothesis.
    expect(addedBinders({ passed_binders: ["(n : Nat)", "(hn : 1 < n)", "(hextra : n < 5)"] }, decl)).toEqual(["(hn : 0 < n)"]);
  });

  it("the block says when nothing was disclosed, and is empty when nothing was added", () => {
    expect(addedHypothesesBlock([], [])).toBe("");
    expect(addedHypothesesBlock(["(h : P)"], [])).toContain("None of them was disclosed.");
  });
});

describe("recordPassedBinders", () => {
  it("records only a paper theorem/lemma the reviewer passed, and the record survives a later unreview", () => {
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "thm:a", kind: "theorem", provenance: "from-note", nl_statement: "a", tex_anchor: "" });
    g = addNode(g, { id: "thm:b", kind: "theorem", provenance: "from-note", nl_statement: "b", tex_anchor: "" });
    g = addNode(g, { id: "aux", kind: "lemma", provenance: "agent-introduced", nl_statement: "c", tex_anchor: "" });
    g = setNodeReview(setNodeReview(setNodeReview(g, "thm:a", "matched", "h"), "thm:b", "drift", "h"), "aux", "matched", "h");
    const text = new Map([["thm:a", "theorem a (h : P) : Q := x"], ["thm:b", "theorem b (h : P) : Q := x"], ["aux", "lemma c (h : P) : Q := x"]]);
    g = recordPassedBinders(g, text);
    const by = (id: string) => g.nodes.find((n) => n.id === id)!;
    expect(by("thm:a").passed_binders).toEqual(["(h : P)"]);
    expect(by("thm:b").passed_binders).toBeUndefined();
    expect(by("aux").passed_binders).toBeUndefined();
    // The filler's disclosure flips the parent to unreviewed; the baseline it is diffed against stays.
    expect(markUnreviewed(g, "thm:a").nodes.find((n) => n.id === "thm:a")!.passed_binders).toEqual(["(h : P)"]);
  });
});
