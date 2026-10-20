import { describe, expect, it } from "vitest";
import { phase3Drift } from "../../src/formalization/dispatcher.js";
import { scaffoldFixable } from "../../src/formalization/proof_review_loop.js";
import type { LoopOutcome } from "../../src/formalization/proof_review_loop.js";

const esc = (over: Record<string, unknown>): LoopOutcome =>
  ({ status: "escalate", route: "unclear", phase: "3", reason: "r", kind: "scaffold-mismatch", obj_id: "lem:x", ...over }) as unknown as LoopOutcome;

describe("phase-3 drift goes back through the statement gate (live cns, yang, drdid: each stopped the run for a fix the reviewer had already named)", () => {
  it("a scaffold-fixable reviewer escalation on a named target during proof filling re-enters the loop", () => {
    expect(phase3Drift(esc({}))).toBe(true);
    expect(phase3Drift(esc({ kind: "drift-in-binder" }))).toBe(true); // a model-invented kind is fixable
  });

  it("a paper finding, missing substrate, an F2.5 escalation, a filler escalation or an unnamed target still stops", () => {
    expect(phase3Drift(esc({ kind: "statement-wrong", route: "fix-source" }))).toBe(false);
    expect(phase3Drift(esc({ kind: "needs-substrate", route: "build-substrate" }))).toBe(false);
    expect(phase3Drift(esc({ kind: "unadjudicable" }))).toBe(false);
    expect(phase3Drift(esc({ phase: "2.5" }))).toBe(false);
    expect(phase3Drift(esc({ route: "fix-source" }))).toBe(false);
    expect(phase3Drift(esc({ obj_id: undefined }))).toBe(false);
  });

  it("scaffoldFixable keeps the gate's protect-kinds", () => {
    for (const k of ["note-wrong", "needs-substrate", "statement-wrong", "claim-false", "unparsable-output"]) expect(scaffoldFixable(k)).toBe(false);
    expect(scaffoldFixable("unadjudicable")).toBe(false);
    expect(scaffoldFixable("unadjudicable", true)).toBe(true);
    expect(scaffoldFixable("scaffold-mismatch")).toBe(true);
  });
});
