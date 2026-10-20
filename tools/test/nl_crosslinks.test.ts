import { describe, expect, it } from "vitest";
import { parseNlCrosslinks, stripNlCrosslinks, sourceBinders } from "../src/shared/nl_crosslinks.js";

describe("nl_crosslinks parsing", () => {
  it("parses hyp, goal and step links, splitting comma-separated names", () => {
    const segs = parseNlCrosslinks("Fix [Λ at least 1](hyp:Λ,hΛ), then [it holds](goal).");
    expect(segs).toEqual([
      { text: "Fix ", links: null },
      { text: "Λ at least 1", links: ["Λ", "hΛ"] },
      { text: ", then ", links: null },
      { text: "it holds", links: ["⊢"] },
      { text: ".", links: null },
    ]);
    const def = "the [law](goal) is the [pushforward](step:2) of [μ](hyp:μ)";
    expect(parseNlCrosslinks(def).filter((g) => g.links).map((g) => g.links)).toEqual([["⊢"], ["⊢2"], ["μ"]]);
  });

  it("strip removes only the markup and is lossless on ordinary markdown links", () => {
    expect(stripNlCrosslinks("If [overlap holds](hyp:hov), then [done](goal).")).toBe("If overlap holds, then done.");
    const s = "see [the paper](https://x.y) for context";
    expect(stripNlCrosslinks(s)).toBe(s);
  });

  it("ignores unbalanced brackets inside code/math spans (interval notation)", () => {
    const s = "If [overlap holds at level `ε ∈ (0, 1/2]`](hyp:hov) and [$x \\in [0,1)$ shifts](hyp:hx), done.";
    const segs = parseNlCrosslinks(s).filter((g) => g.links);
    expect(segs.map((g) => g.links)).toEqual([["hov"], ["hx"]]);
    expect(segs[0].text).toBe("overlap holds at level `ε ∈ (0, 1/2]`");
  });
});

describe("sourceBinders", () => {
  it("extracts binder names and hyp classification from authored source", () => {
    const src = `/-- doc with (parens) inside -/
theorem msmUpper_eq (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hoverlap : ∀ᵐ ω ∂P.μ, 0 < S.propScore true ω)
    {η : NuisanceVec γ} [inst : MeasurableSpace γ]
    (henv : Integrable (fun ω => S.wMax Λ ω) P.μ) :
    S.msmUpper Λ = S.msmUpperForm Λ := by
  sorry`;
    const binders = sourceBinders(src)!;
    expect(binders.map((b) => b.names.join(" "))).toEqual(["Λ", "hΛ", "hoverlap", "η", "inst", "henv"]);
    // implicit/instance binders are never hyp-classified; Λ is a plain decl.
    expect(binders.filter((b) => b.isHyp).map((b) => b.names[0])).toEqual(["hΛ", "hoverlap", "henv"]);
  });
});
