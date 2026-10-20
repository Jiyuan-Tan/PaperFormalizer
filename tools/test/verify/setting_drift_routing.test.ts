// A wrong setting in the sampling model is the transcription's defect: it goes to V1's transcription
// mode even on a node a repair wrote; other drift there stays the repair's (live Athey–Imbens, 2026-09-30).
import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { routeReview } from "../../src/verify/stage_v1_5.js";
import { splitCorollaryId } from "../../src/verify/core_graph.js";
import type { V15NodeVerdict, V15Review } from "../../src/verify/types.js";

const node = (id: string, fix: V15NodeVerdict["fix"]): V15NodeVerdict =>
  ({ id, faithfulness: "drift", ambiguity: "ok", correctness: "ok", detail: "d", witness: null, fix, bookkeeping_assumption: null, reading: null }) as V15NodeVerdict;

describe("setting drift routing", () => {
  it("routes a setting fix on a repaired node to V1 transcription, other drift on it to the fixer", () => {
    const patches = { key_results: ["lem:a"], key_contribution: "k", patches: [{ node: "lem:a", corrected_statement: "x", ops: [{ op: "replace", unit: "lem:a/1/1", to: null, tex: "x" }], proof_note: "unchanged" }], unfixable: [] } as never;
    const setting = node("lem:a", { setting: "The potential outcomes are random, jointly distributed with the assignment." } as V15NodeVerdict["fix"]);
    const other = node("lem:a", null);
    const r = routeReview({ verdict: "REVISE", summary: "", nodes: [setting] } as V15Review, patches, new Set(["lem:a"]));
    expect(r.paperDrift(setting)).toBe(true);
    expect(r.patchDrift).toEqual([]);
    const r2 = routeReview({ verdict: "REVISE", summary: "", nodes: [other] } as V15Review, patches, new Set(["lem:a"]));
    expect(r2.paperDrift(other)).toBe(false);
    expect(r2.patchDrift.map((n) => n.id)).toEqual(["lem:a"]);
  });

  // Which hypotheses a setting holds follows from the wiring; a prose list of them goes stale at
  // every edge the referee adds, and the stale list is then graded drift again (live Ding, 2026-10-01).
  it("a setting lists results only: neither prompt asks for definitions or assumptions in it", () => {
    const prompt = (rel: string) => readFileSync(new URL(`../../src/verify/prompts/${rel}`, import.meta.url), "utf8").replace(/\s+/g, " ");
    expect(prompt("V1.5/review.txt")).toContain("A definition or assumption lives in the setting of every result using it: grade its setting through those results, never by whether a setting lists it");
    expect(prompt("V1/extract_core.txt")).toContain("Definitions and assumptions are not listed");
  });
  it("a setting asked for a corollary a repair split off is no drift: it lives in its parent's setting; its other drift still goes to the fixer", () => {
    const statement = "If the errors are Gaussian, the estimator is efficient.";
    const patches = { key_results: ["thm:a"], key_contribution: "k", patches: [{ node: "thm:a", corrected_statement: "x", proof_note: "unchanged", corollaries: [{ title: null, statement, follows: "By the theorem.", adds: null }] }], unfixable: [] } as never;
    const cor = splitCorollaryId("thm:a", statement);
    const setting = node(cor, { setting: "The law is fixed." } as V15NodeVerdict["fix"]);
    const r = routeReview({ verdict: "REVISE", summary: "", nodes: [setting] } as V15Review, patches, new Set(["thm:a", cor]));
    expect(r.paperDrift(setting)).toBe(false);
    expect(r.patchDrift).toEqual([]);
    const other = node(cor, null);
    const r2 = routeReview({ verdict: "REVISE", summary: "", nodes: [other] } as V15Review, patches, new Set(["thm:a", cor]));
    expect(r2.patchDrift.map((n) => n.id)).toEqual([cor]);
  });
});
