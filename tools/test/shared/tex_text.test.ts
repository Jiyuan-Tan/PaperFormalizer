import { describe, expect, it } from "vitest";
import {
  hasPlausibleSentenceEnd,
  maskNonBoundaryPeriods,
  truncateTexSafe,
} from "../../src/shared/tex_text.js";

describe("maskNonBoundaryPeriods", () => {
  it("masks decimals and multi-dot abbreviations, keeps sentence periods", () => {
    const masked = maskNonBoundaryPeriods("The errors are i.i.d. with variance 0.5. Then it holds.");
    expect(masked).not.toContain("i.i.d.");
    expect(masked).not.toContain("0.5");
    // The two genuine sentence periods survive.
    expect(masked.match(/\./g)?.length).toBe(2);
    // Genuine sentence enders no./etc. are not abbreviations.
    expect(maskNonBoundaryPeriods("The answer is no. Bounded, etc. Then done.").match(/\./g)?.length).toBe(3);
  });
});

describe("hasPlausibleSentenceEnd", () => {
  it("accepts period + closer + whitespace, rejects decimals after masking", () => {
    expect(hasPlausibleSentenceEnd(maskNonBoundaryPeriods("First. second"))).toBe(true);
    expect(hasPlausibleSentenceEnd(maskNonBoundaryPeriods("First.” Second"))).toBe(true);
    expect(hasPlausibleSentenceEnd(maskNonBoundaryPeriods("p(x) \\le 0.5 everywhere"))).toBe(false);
  });
});

describe("truncateTexSafe", () => {
  it("backs off rather than cutting inside inline math", () => {
    const text = "The estimand is \\(\\mathbb{E}[Y^{(1)} - Y^{(0)} \\mid W]\\) under overlap.";
    const cut = truncateTexSafe(text, 30); // 30 chars lands inside the \( … \)
    expect(cut).toBe("The estimand is");
    expect(cut).not.toContain("\\(");
  });

  it("treats $$…$$ as one display and backs off from position 0", () => {
    // per-`$` toggling read the display body as text mode and hard-cut inside it
    const display = "a $$" + "m".repeat(30) + "$$ b";
    expect(truncateTexSafe(display, 20)).toBe("a");
    // a math span opening AT 0 longer than max backs off to empty (balanced),
    // relying on every caller's fallback — never a sealed unbalanced delimiter
    const leading = "\\(" + "x".repeat(50) + "\\) tail";
    expect(truncateTexSafe(leading, 20)).toBe("");
  });
});
