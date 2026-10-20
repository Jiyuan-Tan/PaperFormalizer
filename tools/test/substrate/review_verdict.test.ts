// The study reviewer's verdict: a fail may rest on a reason no check names, and a reply that
// contradicts itself is a fail the scaffolder is told about — never an abort.
import { describe, expect, it } from "vitest";
import { parseReviewVerdict } from "../../src/substrate/types.js";

const checks = (over: Record<string, boolean> = {}) => ({ generic: true, reusable: true, standard: true, not_vacuous: true, fulfills_goal: true, sorry_free: true, layered: true, documented: true, ...over });

describe("study reviewer verdict", () => {
  it("a fail with every check true stands on its findings", () => {
    expect(parseReviewVerdict({ pass: false, findings: "rebuilds Mathlib's `foo` instead of reusing it", checks: checks() })).toMatchObject({ pass: false, findings: "rebuilds Mathlib's `foo` instead of reusing it" });
    expect(parseReviewVerdict({ pass: false, findings: "", checks: checks() }).findings).toContain("without naming a check or a reason");
  });
  it("a pass with a failing check is a fail naming the check", () => {
    const v = parseReviewVerdict({ pass: true, findings: [], checks: checks({ documented: false }) });
    expect(v.pass).toBe(false);
    expect(v.findings).toContain("failing check(s): documented");
  });
  it("coherent replies are read as given", () => {
    expect(parseReviewVerdict({ pass: true, findings: null, checks: checks() })).toMatchObject({ pass: true, findings: "" });
    expect(parseReviewVerdict({ pass: false, findings: "x", checks: checks({ generic: false }) })).toMatchObject({ pass: false, findings: "x" });
  });
});
