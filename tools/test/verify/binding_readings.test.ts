import { describe, expect, it } from "vitest";
import { bindingReadings, compileReviewEdits } from "../../src/verify/core_graph.js";
import { formalizationCoreContextValue } from "../../src/formalization/core_context.js";
import { governByPinnedReadings, pinnedReadingGoverns } from "../../src/formalization/proof_review_loop.js";
import type { ReviewerResult } from "../../src/formalization/proof_reviewer.js";
import { createEmptyGraph } from "../../src/graph/store.js";
import type { Core } from "../../src/core/schema.js";
import type { V15Review } from "../../src/verify/types.js";
import { PINNED_CORE } from "./fixtures/pinned_core.js";

describe("binding readings (V1.5 pins and appended conditions)", () => {
  it("the F1.5/F2 core JSON puts them right under the node's text", () => {
    const view = formalizationCoreContextValue(PINNED_CORE) as { statements: Array<Record<string, unknown>>; assumptions: Array<Record<string, unknown>> };
    const scale = view.statements.find((s) => s.id === "thm:scale")!;
    expect(Object.keys(scale).slice(0, 4)).toEqual(["id", "kind", "statement", "pinned_readings_binding"]);
    expect(scale.pinned_readings_binding).toEqual([expect.stringMatching(/^ass:pin-1 \(reading of thm:scale\)/), "ass:bk-1 (condition of thm:scale): g is Borel measurable."]);
    expect(view.statements.find((s) => s.id === "lem:unpinned")).not.toHaveProperty("pinned_readings_binding");
    expect(view.assumptions.find((a) => a.id === "ass:other")!.pinned_readings_binding).toEqual([expect.stringContaining("ass:pin-2")]);
    expect(view.assumptions.find((a) => a.id === "ass:cdf-regularity")).not.toHaveProperty("pinned_readings_binding");
  });

  it("keeps a pinned reading on an unused definition for its F2.5 review", () => {
    const core = {
      qid: "q", symbols: [], assumptions: [],
      definitions: [{ id: "def:unused", name: "Unused", construction: "The input is P_i." }],
      statements: [], target_estimand: "t", bibliography: [],
    } as unknown as Core;
    const review = {
      verdict: "PASS", summary: "ok",
      nodes: [{
        id: "def:unused", faithfulness: "ok", ambiguity: "pinned", correctness: "ok",
        detail: "index fixed by the declared inputs", witness: null, bookkeeping_assumption: null,
        reading: { reading: "The displayed P is P_i.", evidence: "The inputs are indexed." },
      }],
    } as V15Review;
    const { edits } = compileReviewEdits(core, review);
    expect(edits).toContainEqual(expect.objectContaining({
      op: "add_assumption",
      node: expect.objectContaining({
        id: "ass:pin-1",
        condition: "The displayed P is P_i.",
        bookkeeping: expect.objectContaining({ reason: expect.stringContaining("pins reading of def:unused") }),
      }),
    }));
    expect(edits.some((edit) => edit.op === "wire")).toBe(false);
  });
});

describe("a pinned reading binds: an ambiguity it settles is a Lean-side fix", () => {
  const AMBIG = "The frozen phrase 'strictly increasing CDFs' admits global strict increase and strict increase only on the interior support; specify the domain.";
  const pinned = bindingReadings(PINNED_CORE, "ass:cdf-regularity").map((r) => `${r.id}: ${r.text}`);
  const result = (escalations: ReviewerResult["escalations"]): ReviewerResult => ({
    graph: createEmptyGraph("q"), ok: false, escalate: escalations![0]!, escalations, blocking: [], substrateGates: [],
  });

  it("classifies: ambiguity + pins → governed; a stated `unpinned`, no pins, or a wrong claim → a paper finding", () => {
    expect(pinnedReadingGoverns({ kind: "statement-wrong", obj_id: "ass:cdf-regularity", reason: AMBIG, pinned })).toBe(true);
    expect(pinnedReadingGoverns({ kind: "statement-wrong", obj_id: "ass:cdf-regularity", reason: AMBIG, pinned, unpinned: "the pin fixes the interior only; the endpoint convention is still open" })).toBe(false);
    expect(pinnedReadingGoverns({ kind: "statement-wrong", obj_id: "lem:unpinned", reason: AMBIG })).toBe(false);
    expect(pinnedReadingGoverns({ kind: "statement-wrong", obj_id: "ass:cdf-regularity", reason: "the claim fails for atoms: a counterexample with a point mass", pinned })).toBe(false);
    expect(pinnedReadingGoverns({ kind: "note-wrong", obj_id: "ass:cdf-regularity", reason: AMBIG, pinned })).toBe(false);
  });

  it("a governed finding becomes a scaffold-mismatch naming the pinned reading; the others are untouched", () => {
    const other = { kind: "statement-wrong", obj_id: "lem:unpinned", reason: AMBIG };
    const out = governByPinnedReadings(result([{ kind: "statement-wrong", obj_id: "ass:cdf-regularity", reason: AMBIG, pinned }, other]));
    expect(out.escalate).toMatchObject({ kind: "scaffold-mismatch", obj_id: "ass:cdf-regularity" });
    expect(out.escalate!.reason).toContain("[pinned reading governs]");
    expect(out.escalate!.reason).toContain("finite interior point");
    expect(out.escalations![1]).toBe(other);
    const untouched = result([other]);
    expect(governByPinnedReadings(untouched)).toBe(untouched);
  });
});
