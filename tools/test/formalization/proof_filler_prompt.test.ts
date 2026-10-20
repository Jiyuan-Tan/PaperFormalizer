import { readFileSync } from "node:fs";
import { join } from "node:path";
import { describe, expect, it } from "vitest";

const prompt = readFileSync(join(process.cwd(), "src/formalization/prompts/F4/proof_filler.txt"), "utf8");

describe("proof filler prompt", () => {
  it("a library-wanted instance the paper never assumes is not regularity bookkeeping (live yang: StandardBorelSpace added three times, rejected each time)", () => {
    expect(prompt).toContain("NOT bookkeeping: a structure the paper never assumes that only a library lemma wants");
    expect(prompt).toContain("never add the instance");
  });

  it("a version the filler chooses for an a.e.-defined object carries Measurable (live cns: conditionalWeight / conditionalInverseRepresenter made a fiberwise conclusion choice-dependent)", () => {
    expect(prompt).toContain("A VERSION YOU CHOOSE for an object defined up to null sets");
    expect(prompt).toContain("carries `Measurable`");
  });

  it("is set for a verified paper: bookkeeping only when the paper entails or presupposes it; a condition the paper lacks is escalated, never added", () => {
    expect(prompt).toContain("The spec of record is the typed `core.json`: the user's paper as its referee accepted it");
    expect(prompt).toContain("that the paper neither states nor entails is NOT bookkeeping: it is a gap in the paper");
    expect(prompt).toContain("NEVER a core id");
    expect(prompt).not.toMatch(/from-note|p#\/a#|A human decides/);
  });
});

describe("proof filler prompt — the page carries the roadmap", () => {
  it("tells the filler not to open the core or the plan: the focus nodes' statements and proof_tex are on the page", () => {
    expect(prompt).toContain("do not open the core or the plan");
    expect(prompt).toContain("PROOF ROADMAP");
  });
});
