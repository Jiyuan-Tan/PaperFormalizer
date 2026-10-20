import { describe, expect, it } from "vitest";
import { parseJsonObject, verdictClass } from "../../src/formalization/reviewer_verdicts.js";

describe("verdictClass — TeX commands are not verdict tokens", () => {
  it("ignores TeX command and environment names but still sees a verdict word inside a TeX group", () => {
    expect(verdictClass("matched; uses \\partial_x f throughout")).toBe("pass");
    expect(verdictClass("\\begin{aligned} rows \\end{aligned}")).toBe("unknown");
    expect(verdictClass("matched, but \\emph{drifts} in the constant")).toBe("fail");
  });
});

describe("parseJsonObject — LaTeX in a reviewer note does not kill the verdict", () => {
  it("parses a verdict whose note carries under-escaped TeX", () => {
    const stdout =
      'Verdict follows.\n{"statement_verdicts":[{"obj_id":"T-1","verdict":"drift","note":"should be \\(\\forall n\\) eventually"}]}';
    const out = parseJsonObject(stdout);
    expect(Array.isArray(out.statement_verdicts)).toBe(true);
  });
});
