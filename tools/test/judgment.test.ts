import { describe, expect, it } from "vitest";
import { extractJsonObject, reviewResultSchema, stageOutputSchema } from "../src/judgment.js";

describe("reviewResultSchema", () => {
  it("accepts a revise result with per-item findings", () => {
    const parsed = reviewResultSchema.parse({
      status: "revise",
      classification: "correctness",
      dimension_findings: {
        structure: { verdict: "pass", notes: "structure is usable" },
        novelty: { verdict: "pass", notes: "novelty is plausible" },
        correctness: { verdict: "revise", notes: "one support condition is missing" },
      },
      perItemFindings: [
        {
          label: "Theorem 1",
          verdict: "correctness",
          one_line: "inverse step needs a rank hypothesis",
        },
      ],
      verbatim_critique: "Add the missing rank hypothesis and cite it in the proof.",
    });

    expect(parsed.status).toBe("revise");
  });

  it("loads retired output fields through the passthrough schemas", () => {
    const output = { status: "completed", artifacts: ["old.lean"], theorems: [{ theorem_local_id: "old" }], assumption_table_markdown: "old table" };
    expect(stageOutputSchema.parse(output)).toEqual(output);
    const review = { status: "pass", notes: "ok", assumption_table_markdown: "old table", substrate_gates: [{ name: "old", statement: "True", classical_fact: "old fact", missing_infra: "old library" }] };
    expect(reviewResultSchema.parse(review)).toEqual(review);
  });

  it("accepts the simple accept form", () => {
    expect(reviewResultSchema.parse({ status: "accept", notes: "fits" }).status).toBe("accept");
  });
});

describe("extractJsonObject", () => {
  it("skips accidentally balanced braces in prose before the real JSON", () => {
    // Production failure: prose contained a backticked Lean set `{Z=z_l}` BEFORE the real JSON.
    const text =
      "L-8 cites P-9 (partition by `{Z=z_l}` and integrability) and `{x | P x}` ahead.\n\n" +
      '{"route":"stage_2","reason":"Case 4b (encoding drift)","proposed_action":"Re-scaffold."}';
    expect(extractJsonObject(text)).toEqual({
      route: "stage_2",
      reason: "Case 4b (encoding drift)",
      proposed_action: "Re-scaffold.",
    });
  });

  it("parses JSON inside a fenced code block", () => {
    const text = "Here is the verdict:\n```json\n{\"route\":\"user\"}\n```\nDone.";
    expect(extractJsonObject(text)).toEqual({ route: "user" });
  });

  it("throws when no candidate parses", () => {
    expect(() => extractJsonObject("plain prose, no braces")).toThrow();
    expect(() => extractJsonObject("foo {bar} baz")).toThrow();
  });
});
