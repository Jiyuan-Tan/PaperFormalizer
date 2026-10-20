// A coordination merge that only adds imports to an existing module is placed by the runner, sorted
// into the import block; anchored at a line it left the block unsorted or split, and the header lint
// refused the module three rounds running (live Li–Ding round B, 2026-10-02).
import { describe, expect, it } from "vitest";
import { importOnlyLines } from "../../src/substrate/coordinate.js";
import { insertImportSorted } from "../../src/toolkit/barrels.js";

describe("importOnlyLines", () => {
  it("recognises an import-only merge and nothing else", () => {
    expect(importOnlyLines("public import Mathlib.Probability.Distributions.Gaussian.Multivariate\n")).toEqual([
      "public import Mathlib.Probability.Distributions.Gaussian.Multivariate",
    ]);
    expect(importOnlyLines("import A.B\n\npublic import C\n")).toEqual(["import A.B", "public import C"]);
    expect(importOnlyLines("public import A\nlemma t : True := trivial\n")).toBeNull();
    expect(importOnlyLines("\n")).toBeNull();
  });
  it("such lines land sorted and contiguous in the module's import block", () => {
    const orig = "module\n\npublic import Mathlib.Order.Basic\npublic import Mathlib.Probability.Distributions.Gaussian.Real\n\n/-! doc -/\n";
    const out = importOnlyLines("public import Mathlib.Probability.Distributions.Gaussian.Multivariate")!.reduce((t, l) => insertImportSorted(t, l), orig);
    expect(out).toBe(
      "module\n\npublic import Mathlib.Order.Basic\npublic import Mathlib.Probability.Distributions.Gaussian.Multivariate\npublic import Mathlib.Probability.Distributions.Gaussian.Real\n\n/-! doc -/\n",
    );
  });
});
