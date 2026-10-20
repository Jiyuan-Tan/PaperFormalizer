// The docstring pass rewrote docstrings and dropped the `@realizes` tag lines inside them; the
// delivery audit then refused the symbols they realized (live Ding F5, 2026-10-02). The runner puts
// lost tag lines back; the model never retypes them.
import { describe, expect, it } from "vitest";
import { restoreDocstringTags } from "../../src/formalization/stage5_docstrings.js";

const BEFORE = [
  "/-- The product of independent fair orientation coins.",
  "@realizes T_i(pair orientation, true treats position 1)",
  "@realizes \\bm{T}(function (Fin N) → Bool) -/",
  "-- @node: def:matched-pair-design",
  "noncomputable def matchedPairRandomization (N : ℕ) :",
  "    FiniteDesign (Fin N → Bool) := matchedPairDesign",
  "",
  "/-- @realizes \\tau_i(mean of both position-specific causal effects) -/",
  "noncomputable def pairEffect (p : (Fin N)) : ℝ := (∑ b, (y1 p b - y0 p b)) / 2",
  "",
  "/-- Untagged. -/",
  "def other : ℕ := 0",
].join("\n");

describe("restoreDocstringTags", () => {
  it("puts back the tag lines a rewritten docstring lost, on the same declaration, and nothing else", () => {
    const after = BEFORE
      .replace(/\/-- The product[\s\S]*?-\//, "/-- [The law of the pair orientations](goal) for [N pairs](hyp:N). -/")
      .replace("/-- @realizes \\tau_i(mean of both position-specific causal effects) -/", "/-- [The pair effect](goal) of [pair p](hyp:p).\n@realizes \\tau_i(mean of both position-specific causal effects) -/")
      .replace("/-- Untagged. -/", "/-- [Zero](goal). -/");
    const out = restoreDocstringTags(BEFORE, after);
    expect(out.restored).toBe(2);
    expect(out.text).toContain(
      "/-- [The law of the pair orientations](goal) for [N pairs](hyp:N).\n@realizes T_i(pair orientation, true treats position 1)\n@realizes \\bm{T}(function (Fin N) → Bool) -/\n-- @node: def:matched-pair-design\nnoncomputable def matchedPairRandomization",
    );
    expect(out.text.match(/@realizes \\tau_i/g)).toHaveLength(1);
    expect(out.text).toContain("/-- [Zero](goal). -/\ndef other");
  });
  it("leaves an untouched file as it is", () => {
    expect(restoreDocstringTags(BEFORE, BEFORE)).toEqual({ text: BEFORE, restored: 0 });
  });
});
