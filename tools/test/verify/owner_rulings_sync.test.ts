import { describe, expect, it } from "vitest";
import { createVerifyInitialState } from "../../src/state.js";
import type { StateJson } from "../../src/types.js";
import { syncOwnerRulings } from "../../src/verify/owner_rulings.js";
import type { OwnerReading } from "../../src/verify/core_graph.js";

function state(): StateJson {
  return createVerifyInitialState("q", { phase: "formalization", source: { input: "p.tex", main_file: "p.tex", sha256: "x" }, core_sha256: null, v1_rounds: 0, v1_5_rounds: 0, findings: [], report_path: null } as never);
}

describe("syncOwnerRulings — an owner ruling has one record, its owner reading", () => {
  it("a leftover owner entry no reading records is dropped, so it can never dismiss a later finding; the orchestrator's stay", () => {
    const s = state();
    const v = s.verify!;
    v.rejected_rewinds = [
      { node: "lem:norestr", axis: "correctness", stage: "F2.5", route: "fix-source", detail: "a reverted withdrawal", reason: "r", by: "owner", at: "t" },
      { node: "ass:pin-19", axis: "correctness", stage: "F2.5", route: "fix-source", detail: "d", reason: "a symbol reading", by: "orchestrator", at: "t" },
    ];
    v.paper_errors = { "lem:norestr": { detail: "gap", witness: "w", owner_decision: "finding rejected", decision_reason: "r", owner_overruled: true } };
    v.findings = [{ node: "lem:norestr", stage: "F2.5", kind: "note", detail: "x\n(finding withdrawn by the paper's owner on lem:norestr: r)", witness: null }] as never;
    const out = syncOwnerRulings(s, []);
    expect(v.rejected_rewinds).toEqual([expect.objectContaining({ node: "ass:pin-19", by: "orchestrator" })]);
    expect(v.paper_errors["lem:norestr"]).toEqual({ detail: "gap", witness: "w" }); // open again
    expect(v.findings).toEqual([]);
    expect(out.changes.join("\n")).toMatch(/dropped — no owner reading records it[\s\S]*lem:norestr reopened/);
  });

  it("derives the ledger stamp and the ruled-out entries from the readings, and is idempotent", () => {
    const s = state();
    const v = s.verify!;
    v.paper_errors = { "lem:a": { detail: "printed gap", witness: null, owner_decision: "finding rejected", decision_reason: "old wording", owner_overruled: true } };
    const readings: OwnerReading[] = [
      { id: "ass:pin-owner-1", node: "lem:a", reading: "the owner's reading, extended by hand", withdraws: [{ axis: "correctness", stage: "V1.5", route: "applied repair", detail: "printed gap", at: "t" }] },
      { id: "ass:pin-owner-2", node: "thm:b", reading: "τ is conditional", withdraws: [{ axis: "clarify", stage: "F2.5", route: "unclear", detail: "two readings", at: "t" }] },
    ];
    const first = syncOwnerRulings(s, readings);
    expect(first.readings).toEqual(readings);
    expect(v.rejected_rewinds).toEqual([
      expect.objectContaining({ node: "lem:a", by: "owner", pin: "ass:pin-owner-1", reason: "the owner's reading, extended by hand" }),
      expect.objectContaining({ node: "thm:b", axis: "clarify", by: "owner", pin: "ass:pin-owner-2", detail: "two readings" }),
    ]);
    // the reason follows the reading as it stands; a node with no ledger entry gets one
    expect(v.paper_errors!["lem:a"]).toMatchObject({ owner_decision: "finding rejected", decision_reason: "the owner's reading, extended by hand" });
    expect(v.paper_errors!["thm:b"]).toMatchObject({ detail: "two readings", kind: "clarification", owner_decision: "finding rejected" });
    const again = syncOwnerRulings(s, first.readings);
    expect(again).toMatchObject({ changes: [] });
  });
});
