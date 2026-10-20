import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { PatchFileSchema } from "../../src/verify/patches.js";
import { droppedUnitProblems, restatementProblems } from "../../src/verify/restatement.js";
import type { PatchOp } from "../../src/verify/ops.js";
import { restatementViolations } from "../../src/verify/stage_v1.js";

// The live DFM run (2026-09-26): the fixer's ops for Theorem 4 replace its hypothesis sentence (unit 1/1)
// with one that redefines $BB$ and $\\xi$; the old text heuristic called that a dropped hypothesis.
const DFM_RAW = JSON.parse(readFileSync(path.join(path.dirname(fileURLToPath(import.meta.url)), "fixtures", "dfm_sks_ops.json"), "utf8")) as {
  printed: string; ops: Array<PatchOp | { op: string }>; corrected: string; deleted_1_1: string;
};
// The fixture predates replacement-only repairs: its replacements alone (its one insertion is in the proof).
const DFM = { ...DFM_RAW, ops: DFM_RAW.ops.filter((op): op is PatchOp => op.op === "replace") };

describe("coverage is structural: only a unit an op deletes is dropped (P2 ops)", () => {
  it("the live DFM ops replacing the hypothesis sentence pass: a replaced unit is an explicit change", () => {
    expect(DFM.ops.some((op) => op.op === "replace" && op.unit === "thm::sks-nuisance/1/1")).toBe(true);
    expect(restatementProblems(DFM.printed, DFM.corrected, { ops: DFM.ops })).toEqual([]);
    const core = { statements: [{ id: "thm:sks-nuisance", statement: DFM.printed }], assumptions: [], definitions: [] } as unknown as Core;
    const file = PatchFileSchema.parse({ key_results: [], key_contribution: "c", patches: [{ node: "thm:sks-nuisance", ops: DFM.ops, corrected_statement: DFM.corrected, proof_note: "p" }], unfixable: [] });
    expect(restatementViolations(core, file, null)).toEqual([]);
  });

  it("replacing the hypothesis unit by blank TeX (a deletion) fails, naming the unit", () => {
    const ops: PatchOp[] = [{ op: "replace", unit: "thm::sks-nuisance/1/1", tex: " " }];
    expect(restatementProblems(DFM.printed, DFM.deleted_1_1, { ops })).toEqual([expect.stringContaining("deletes the printed statement's unit thm::sks-nuisance/1/1")]);
    expect(droppedUnitProblems([{ op: "replace", unit: "e/1/2", to: "e/1/3", tex: " " }])).toEqual([expect.stringContaining("unit e/1/2 … e/1/3")]);
    // a blanked proof unit is a proof revision, not a drop from the statement
    expect(droppedUnitProblems([{ op: "replace", unit: "e/proof/1/2", tex: " " }])).toEqual([]);
  });
});
