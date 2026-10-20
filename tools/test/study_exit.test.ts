// Every stop of a study prints its message and an exit that works: a plain `--resume` returns a
// halted or escalated study as it stands, so the exit names the flag that re-opens it.
import { describe, expect, it } from "vitest";
import { clearStudyCap, createInitialSubstrateState, studyExit } from "../src/substrate/state.js";

const halted = (msg: string, over: object = {}) => ({ ...createInitialSubstrateState("s"), phase: "halted" as const, terminalMessage: msg, buildRounds: 9, reviewRounds: 3, coordinateRounds: 3, ...over });

describe("a study's halts and their exits", () => {
  it("each cap names the flag that re-opens it, and the flag re-opens it", () => {
    for (const [cap, flag, opt, phase] of [
      ["BUILD_CAP", "--clear-build-cap", "clearBuildCap", "build"],
      ["REVIEW_CAP", "--clear-review-cap", "clearReviewCap", "build"],
      ["COORD_CAP", "--clear-coordinate-cap", "clearCoordinateCap", "coordinate"],
    ] as const) {
      const st = halted(`Reached ${cap} (3); …`);
      expect(studyExit(st, "s", "/tk")).toContain(`leansmith study s --resume ${flag} --toolkit /tk`);
      expect(clearStudyCap(st, { [opt]: true })).toBe(true);
      expect(st).toMatchObject({ phase, terminalMessage: null });
    }
    expect(halted("Reached REVIEW_CAP (3)").reviewRounds).toBe(3);
    const st = halted("Reached REVIEW_CAP (3)");
    clearStudyCap(st, { clearReviewCap: true });
    expect(st).toMatchObject({ reviewRounds: 0, buildRounds: 9 });
  });

  it("a flag for another cap is refused before the state is touched, naming the one that applies", () => {
    const st = halted("Reached REVIEW_CAP (3)");
    expect(() => clearStudyCap(st, { clearReviewCap: true, clearBuildCap: true })).toThrow(/--clear-build-cap requires a study halted at BUILD_CAP \(this one is halted at REVIEW_CAP: --clear-review-cap\)/);
    expect(st).toMatchObject({ phase: "halted", reviewRounds: 3 });
    expect(() => clearStudyCap({ ...createInitialSubstrateState("s"), phase: "build" }, { clearCoordinateCap: true })).toThrow(/requires a study halted at COORD_CAP$/);
    expect(clearStudyCap(st, {})).toBe(false);
  });

  it("an escalation never reads as resumable by a bare --resume unless that re-opens it", () => {
    const esc = (kind: string) => ({ ...createInitialSubstrateState("s"), phase: "escalated" as const, terminalMessage: "m", terminalEscalationKind: kind as never });
    expect(studyExit(esc("scaffolder"), "s", "/tk")).toMatch(/requirement\.md as the escalation asks, then `leansmith study s --resume --toolkit \/tk`: it re-opens only when the requirement changed/);
    expect(studyExit(esc("coordinate-timeout"), "s", "/tk")).toMatch(/No flag re-opens it/);
    expect(studyExit({ ...createInitialSubstrateState("s"), phase: "review" }, "s", "/tk")).toContain("continue with `leansmith study s --resume --toolkit /tk`");
    expect(studyExit({ ...createInitialSubstrateState("s"), phase: "done" }, "s", "/tk")).toBe("");
  });
});
