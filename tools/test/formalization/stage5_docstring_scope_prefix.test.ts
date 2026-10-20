// A docstring above `omit … in` does not parse (live Sant'Anna–Zhao: the F5 pass broke the build on
// two `omit [MeasurableSpace Ω] in` lemmas and every docstring of the pass was rolled back).
import { describe, expect, it } from "vitest";
import { docstringAfterScopePrefix } from "../../src/formalization/stage5_docstrings.js";

describe("docstringAfterScopePrefix", () => {
  it("moves the docstring below the prefix, keeps the tag comment, and leaves a well-placed one alone", () => {
    const src = [
      "/-- [Odds](goal) equal the tilt. -/",
      "omit [MeasurableSpace Ω] in",
      "-- @node: odds_eq_exp",
      "lemma odds_eq_exp : True := trivial",
      "",
      "omit [Fintype ι] in",
      "/-- Already [in place](goal). -/",
      "lemma placed : True := trivial",
      "",
      "/-- A plain [one](goal). -/",
      "lemma plain : True := trivial",
    ].join("\n");
    const out = docstringAfterScopePrefix(src);
    expect(out.moved).toBe(1);
    expect(out.text).toBe([
      "omit [MeasurableSpace Ω] in",
      "-- @node: odds_eq_exp",
      "/-- [Odds](goal) equal the tilt. -/",
      "lemma odds_eq_exp : True := trivial",
      "",
      "omit [Fintype ι] in",
      "/-- Already [in place](goal). -/",
      "lemma placed : True := trivial",
      "",
      "/-- A plain [one](goal). -/",
      "lemma plain : True := trivial",
    ].join("\n"));
    expect(docstringAfterScopePrefix(out.text).moved).toBe(0);
  });
});

// The docstring-style linter is an error in the toolkit build (live Sant'Anna–Zhao: 19 docstrings
// ending "\n -/" rolled back a second whole pass).
import { normalizeDocstringEndings } from "../../src/formalization/stage5_docstrings.js";

describe("normalizeDocstringEndings", () => {
  it("ends every docstring with one space or one newline, and leaves good ones alone", () => {
    const src = [
      "/-- [Mass](goal) is positive.",
      " -/",
      "lemma a : True := trivial",
      "/-- No space.-/",
      "lemma b : True := trivial",
      "/-- Two spaces.  -/",
      "lemma c : True := trivial",
      "/-- Fine. -/",
      "lemma d : True := trivial",
      "/-- Fine too.",
      "-/",
      "lemma e : True := trivial",
    ].join("\n");
    const out = normalizeDocstringEndings(src);
    expect(out.fixed).toBe(3);
    expect(out.text).toBe([
      "/-- [Mass](goal) is positive.",
      "-/",
      "lemma a : True := trivial",
      "/-- No space. -/",
      "lemma b : True := trivial",
      "/-- Two spaces. -/",
      "lemma c : True := trivial",
      "/-- Fine. -/",
      "lemma d : True := trivial",
      "/-- Fine too.",
      "-/",
      "lemma e : True := trivial",
    ].join("\n"));
    expect(normalizeDocstringEndings(out.text).fixed).toBe(0);
  });
});

// A docstring with no closing `-/` comments out the rest of the file (live Sant'Anna–Zhao: four in
// one pass, each running into its `-- @node:` line).
import { closeUnterminatedDocstrings } from "../../src/formalization/stage5_docstrings.js";

describe("closeUnterminatedDocstrings", () => {
  it("closes a docstring that runs into a tag line or a declaration; closed ones are untouched", () => {
    const src = [
      "/-- [Parallel trends](hyp:hPT) imply",
      "[the gap equals the ATT](goal).",
      "-- @node: gap_att",
      "lemma gap_att : True := trivial",
      "",
      "/-- Open before a decl.",
      "theorem t : True := trivial",
      "",
      "/-- Closed",
      "on the next line. -/",
      "lemma ok : True := trivial",
    ].join("\n");
    const out = closeUnterminatedDocstrings(src);
    expect(out.closed).toBe(2);
    expect(out.text.split("\n").slice(0, 7)).toEqual([
      "/-- [Parallel trends](hyp:hPT) imply",
      "[the gap equals the ATT](goal). -/",
      "-- @node: gap_att",
      "lemma gap_att : True := trivial",
      "",
      "/-- Open before a decl. -/",
      "theorem t : True := trivial",
    ]);
    expect(closeUnterminatedDocstrings(out.text).closed).toBe(0);
  });
  it("leaves a closed docstring whose text line starts with a keyword", () => {
    const src = [
      "/-- Under [the model](hyp:M) the [policy overlap](goal) says [each policy",
      "class in every bin has probability at least the constant](step:1). -/",
      "def PolicyOverlap : Prop := True",
    ].join("\n");
    expect(closeUnterminatedDocstrings(src)).toEqual({ text: src, closed: 0 });
  });
  it("reads nested comments as Lean does and stops before any command", () => {
    const nested = ["/-- Text", "  /- note -/", "more text. -/", "def x : Prop := True"].join("\n");
    expect(closeUnterminatedDocstrings(nested)).toEqual({ text: nested, closed: 0 });
    const src = ["/-- Open text", "example : True := trivial", "/-- d -/", "def x : Prop := True"].join("\n");
    expect(closeUnterminatedDocstrings(src).text.split("\n").slice(0, 2)).toEqual(["/-- Open text -/", "example : True := trivial"]);
  });
  it("closes an open docstring before the next comment that opens", () => {
    const src = ["/-- Open text", "/-- Next. -/", "def x : Prop := True"].join("\n");
    expect(closeUnterminatedDocstrings(src)).toEqual({ text: ["/-- Open text -/", "/-- Next. -/", "def x : Prop := True"].join("\n"), closed: 1 });
  });
});
