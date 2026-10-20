// Two declarations of one file sharing a leaf name (`f` and `S.f`): a full name is resolved to the
// one whose written name is its longest dotted suffix, without an exact line (live LMZ F2.5:
// "declaration … is ambiguous without an exact line").
import { describe, expect, it } from "vitest";
import { extractDeclSnippet } from "../../src/presentation/lean_extract.js";

const SOURCE = [
  "namespace Papers.Demo",
  "",
  "def observedOutcome (z : Bool) : Nat := if z then 1 else 0",
  "",
  "def SampleModel.observedOutcome (n : Nat) : Nat := n + 2",
  "",
  "end Papers.Demo",
].join("\n");

describe("extractDeclSnippet — same leaf name in one file", () => {
  it("picks the declaration whose written name is the longest dotted suffix of the full name", () => {
    expect(extractDeclSnippet(SOURCE, "Papers.Demo.observedOutcome", 0)).toContain("if z then 1 else 0");
    expect(extractDeclSnippet(SOURCE, "Papers.Demo.SampleModel.observedOutcome", 0)).toContain("n + 2");
  });
  it("still refuses a name no written declaration is a suffix of", () => {
    expect(() => extractDeclSnippet(SOURCE, "Other.observedOutcomes", 0)).toThrow();
  });
});
