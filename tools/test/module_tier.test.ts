import { describe, it, expect } from "vitest";
import { poolModules } from "../src/formalization/module_tier.js";

const c = (module: string, score: number, name = `${module}.d${score}`) => ({ module, name, score });

describe("poolModules (top-k pooled member scores → ranked modules)", () => {
  it("scores a module by the MEAN of its top-k member scores, ignoring the diluting tail", () => {
    const cands = [
      c("M1", 9), c("M1", 7), c("M1", 5), c("M1", 1), // top-3 mean = 7 (the 1 is ignored)
      c("M2", 8), c("M2", 8),                          // only 2 members → mean = 8
    ];
    const out = poolModules(cands, 10, 3);
    expect(out.map((m) => m.module)).toEqual(["M2", "M1"]);
    expect(out.find((m) => m.module === "M1")!.score).toBeCloseTo(7, 5);
    expect(out.find((m) => m.module === "M2")!.score).toBeCloseTo(8, 5);
  });

  it("breaks module-score ties deterministically by module name", () => {
    const out = poolModules([c("Zmod", 5), c("Amod", 5)], 10, 3);
    expect(out.map((m) => m.module)).toEqual(["Amod", "Zmod"]);
  });
});
