/**
 * V1 patch mode runs one more fixer round past its two when the violations fell between them — a
 * reply that answered most of what it was sent is finished, not handed to the orchestrator — and
 * never otherwise (the same count twice, more, or none left).
 */
import { describe, expect, it } from "vitest";
import { MAX_PATCH_AGENT_ROUNDS, MAX_PATCH_AGENT_ROUNDS_CONVERGING, fixerRoundAllowed } from "../../src/verify/stage_v1.js";

describe("fixerRoundAllowed", () => {
  it("the first two rounds always run (round 0 is the saved reply's validation)", () => {
    expect(fixerRoundAllowed(0, [])).toBe(true);
    expect(fixerRoundAllowed(1, [0])).toBe(true);
    expect(fixerRoundAllowed(2, [0, 7])).toBe(true);
    expect(MAX_PATCH_AGENT_ROUNDS).toBe(2);
  });

  it("a third round runs only when fewer violations are sent than last time", () => {
    expect(fixerRoundAllowed(3, [0, 15, 1])).toBe(true);
    expect(fixerRoundAllowed(3, [0, 3, 2])).toBe(true);
    expect(fixerRoundAllowed(3, [0, 2, 2])).toBe(false);
    expect(fixerRoundAllowed(3, [0, 1, 3])).toBe(false);
    // (the loop never asks past a clean reply; a zero sent is no round)
    expect(fixerRoundAllowed(3, [0, 2, 0])).toBe(false);
    // the saved reply of round 0 counts as a round sent nothing
    expect(fixerRoundAllowed(3, [5, 2])).toBe(true);
    expect(fixerRoundAllowed(3, [2])).toBe(false);
  });

  it("never a fourth", () => {
    expect(MAX_PATCH_AGENT_ROUNDS_CONVERGING).toBe(3);
    expect(fixerRoundAllowed(4, [0, 9, 4, 1])).toBe(false);
  });
});
