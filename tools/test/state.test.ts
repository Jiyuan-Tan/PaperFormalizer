import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { canonicalLeanSubdir, statePath } from "../src/paths.js";
import {
  createVerifyInitialState,
  emptyVerifyState,
  loadState,
  saveState,
  stateSchema,
} from "../src/state.js";

const QID = "minimal_basis";

function fresh() {
  return createVerifyInitialState(QID, emptyVerifyState());
}

const BASE = {
  lean_subdir: "Papers/MinimalBasis",
  design_decisions: {},
  added_assumptions: [],
  flags: { missing_architecture: false },
};

describe("state schema", () => {

  it("accepts exactly the V+F cursor values — the CausalSmith-era cursors are not remapped", () => {
    for (const stage of ["init", "V1", "V1.5", "1", "1.5", "2", "2.5", "3", "3.5", "4", "5", "V6"]) {
      expect(stateSchema.parse({ ...BASE, stage_completed: stage }).stage_completed).toBe(stage);
    }
    for (const stage of ["-1.2", "0.5", "3.7", "-1.1", "-0.5", "0", "D0", "F1"]) {
      expect(() => stateSchema.parse({ ...BASE, stage_completed: stage }), stage).toThrow();
    }
  });

  it("round-trips a valid state and enforces qid/lean_subdir", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "leansmith-state-"));
    await saveState(repoRoot, QID, fresh());
    const loaded = await loadState(repoRoot, QID);
    expect(loaded.lean_subdir).toBe(canonicalLeanSubdir(QID));
    expect(loaded.qid).toBe(QID);
    const file = statePath(repoRoot, QID);
    expect(file).toBe(path.join(repoRoot, "runs", QID, "state.json"));
    expect(await readFile(file, "utf8")).toContain('"stage_completed": "init"');
    for (const subdir of ["Papers/Wrong", "CausalSmith/Verify/MinimalBasis_Verify", "Papers/../etc/MinimalBasis"]) {
      await expect(saveState(repoRoot, QID, { ...fresh(), lean_subdir: subdir }), subdir).rejects.toThrow(/invariant failed/);
    }
  });

  it("loads and preserves retired state keys through a save", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "leansmith-legacy-state-"));
    const legacy = {
      ...fresh(),
      pending_sorries: [{ file: "Papers/MinimalBasis/Basic.lean", line: 3, goal: "True" }],
      added_assumptions: [{ label: "A-1", statement: "finite", user_approved: true, reviewed: false }],
      flags: {
        ...fresh().flags,
        rewound_from_stage0: "old reason",
        f1_plan_retired: true,
        f2_scaffold_retired: true,
        stage3_5_advisory_unused: ["h"],
        stage3_5_build_failed: "old diagnostic",
        assumption_delta_review: "old review",
      },
    };
    const file = statePath(repoRoot, QID);
    await mkdir(path.dirname(file), { recursive: true });
    await writeFile(file, JSON.stringify(legacy));
    const loaded = await loadState(repoRoot, QID);
    await saveState(repoRoot, QID, loaded);
    expect(await loadState(repoRoot, QID)).toEqual(loaded);
    const saved = JSON.parse(await readFile(file, "utf8"));
    expect(saved.pending_sorries).toEqual(legacy.pending_sorries);
    expect(saved.added_assumptions).toEqual(legacy.added_assumptions);
    expect(saved.flags).toEqual(legacy.flags);
  });
});
