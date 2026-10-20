import { describe, it, expect } from "vitest";
import { blendSemantic, blendWeighted } from "../src/formalization/reuse_retrieval.js";

const lex = (name: string, score: number) => ({
  library: "L", name, statement: "", docFirstPara: "", module: "", file: "",
  tier1: false, usesSorry: false, score, matchedVia: "name" as const,
});

describe("blendSemantic (RRF fusion)", () => {
  it("a decl in BOTH lists outranks one in only a single list (RRF is additive)", () => {
    const out = blendSemantic(
      [lex("both", 5), lex("lexOnly", 4)],
      [{ name: "both", sim: 0.9 }, { name: "semOnly", sim: 0.8 }],
      10,
    );
    expect(out[0].name).toBe("both"); // rank1 in both lists → 2/(k0+1) beats any single 1/(k0+1)
    expect(out.find((c) => c.name === "semOnly")!.matchedVia).toBe("semantic");
  });

  it("respects topK", () => {
    const out = blendSemantic([lex("L1", 9), lex("L2", 8)], [{ name: "S1", sim: 0.7 }], 2);
    expect(out).toHaveLength(2);
  });

  it("does NOT let a dense-boosted wrong decl displace a confident lexical top hit", () => {
    // Explicit confidentScore (6th arg) pins the mechanism regardless of the production default.
    const out = blendSemantic(
      [lex("correct", 12), lex("wrong", 5)],
      [{ name: "wrong", sim: 0.9 }, { name: "noise", sim: 0.8 }],
      10, 60, undefined, 8,
    );
    expect(out[0].name).toBe("correct"); // under plain RRF this was "wrong"
  });
});

describe("blendWeighted (min-max-normalized weighted score sum)", () => {
  it("treats an all-equal channel as fully credited (no divide-by-zero)", () => {
    // single lexical + single dense, disjoint names → each normalizes to 1 within its channel
    const out = blendWeighted([lex("X", 7)], [{ name: "Z", sim: 0.4 }], 10, 0.3, 0.7);
    expect(out.find((c) => c.name === "X")!.score).toBeCloseTo(0.3, 5);
    expect(out.find((c) => c.name === "Z")!.score).toBeCloseTo(0.7, 5);
  });
});
