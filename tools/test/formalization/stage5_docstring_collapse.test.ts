// F5: a docstring written above a declaration's existing one is collapsed to one before the build
// (live Athey–Imbens, 2026-10-01: 51 doubled docstrings broke the build).
import { describe, expect, it } from "vitest";
import { collapseAdjacentDocstrings } from "../../src/formalization/stage5_docstrings.js";

describe("collapseAdjacentDocstrings", () => {
  it("keeps the crosslinked docstring, and any tag comment between the two, in place", () => {
    const src = [
      "/-- A count cannot exceed the number of units. -/",
      "/-- For [prescribed counts](hyp:Nvec), [validity](goal) means no count exceeds N. -/",
      "def ValidCounts : Prop := True",
      "",
      "/-- Expectations depend only on the support. -/",
      "-- @node: expectation_eq",
      "/-- Given [equality on the support](hyp:h), [the expectations agree](goal). -/",
      "lemma expectation_eq : True := trivial",
      "",
      "/-- A single docstring stays. -/",
      "lemma lone : True := trivial",
    ].join("\n");
    const out = collapseAdjacentDocstrings(src);
    expect(out.collapsed).toBe(2);
    expect(out.text).toBe([
      "/-- For [prescribed counts](hyp:Nvec), [validity](goal) means no count exceeds N. -/",
      "def ValidCounts : Prop := True",
      "",
      "-- @node: expectation_eq",
      "/-- Given [equality on the support](hyp:h), [the expectations agree](goal). -/",
      "lemma expectation_eq : True := trivial",
      "",
      "/-- A single docstring stays. -/",
      "lemma lone : True := trivial",
    ].join("\n"));
  });
});
