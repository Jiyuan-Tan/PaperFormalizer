// A cited result is planned either as a cited gate or, discharged, as a proved lemma/theorem; the
// plan gate (P9) accepts both, and the two prompts say so. Before, the gate refused the proved form
// in a fresh plan while the reviewer demanded it, and the boundary could not converge (live Ding,
// 2026-10-01).
import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";

const prompt = (rel: string): string => readFileSync(new URL(`../../src/formalization/prompts/${rel}`, import.meta.url), "utf8");

describe("cited results in the F1 and F1.5 prompts", () => {
  it("F1 may plan a cited result as proved, with the stamp the gate requires", () => {
    expect(prompt("F1/stage1_template.txt")).toContain("`citation_discharged:true`, its `source` kept");
  });
  it("the F1.5 reviewer flags a cited gate only when a library decl proves it, and asks for the proved form", () => {
    const p = prompt("F1.5/stage1_5_reuse_soundness.txt");
    expect(p).toContain("FLAG a cited gate only when a library decl proves it");
    expect(p).toContain("re-plan it in the proved form");
  });
  it("F2 is asked for the carrier P9 requires of a cited gate with no carrier on file: Sort 0, never `: Prop`", () => {
    // nothing writes `source.carrier`, so the gate's default (logical-claim → Sort 0) is every run's case
    const rule = prompt("F2/stage2_scaffold.txt").split("\n- ").find((r) => r.startsWith("`gate:true` statement node"))!;
    expect(rule).toContain("def <lean_name> : Sort 0 :=");
    expect(rule).not.toContain("def <lean_name> : Prop");
    expect(rule).not.toContain('source.carrier:"logical-claim"');
  });
});
