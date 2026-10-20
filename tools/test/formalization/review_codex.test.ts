import { describe, expect, it } from "vitest";
import { planReviewText, reviewContext, REVIEW_INPUT_MAX } from "../../src/formalization/review_codex.js";

describe("planReviewText (the plan as the F1.5 reviewer reads it)", () => {
  it("serializes the plan compact, and passes text that does not parse through unchanged", () => {
    const pretty = JSON.stringify({ qid: "q", nodes: { "thm:t": { lean_kind: "theorem", notes: "trace" } } }, null, 2);
    expect(pretty).toMatch(/\n {2}"/);
    const compact = planReviewText(pretty);
    expect(compact).not.toContain("\n");
    expect(JSON.parse(compact)).toEqual(JSON.parse(pretty));
    expect(planReviewText("{not json")).toBe("{not json");
  });
});

describe("reviewContext (what the F1.5 prompt carries of the plan and the core)", () => {
  const paths = { plan: "/run/formalization/plan.json", core: "/run/formalization/f1_5_core_context.json" };
  it("prints both while they fit; past the room the core goes by file, then the plan too — never cut", () => {
    const whole = reviewContext("PLAN", "CORE", paths, 100);
    expect(whole).toMatchObject({ coreByFile: false });
    expect(whole.block).toContain("PLAN");
    expect(whole.block).toContain("CORE");
    const big = reviewContext("P".repeat(60), "C".repeat(60), paths, 100);
    expect(big.coreByFile).toBe(true);
    expect(big.block).toContain("P".repeat(60));
    expect(big.block).not.toContain("CCC");
    expect(big.block).toContain(`it is the file ${paths.core}. Read it whole`);
    const huge = reviewContext("P".repeat(200), "C".repeat(60), paths, 100);
    expect(huge.block).not.toContain("PPP");
    expect(huge.block).toContain(`it is the file ${paths.plan}.`);
    expect(huge.block).toContain(`it is the file ${paths.core}.`);
    expect(REVIEW_INPUT_MAX).toBeLessThan(1_048_576);
  });
});
