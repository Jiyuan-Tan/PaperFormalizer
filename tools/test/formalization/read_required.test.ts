import { describe, it, expect } from "vitest";
import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { planGatePrelint } from "../../src/formalization/stage1_5.js";

describe("planGatePrelint fail-loud core", () => {
  it("throws when core.json is missing instead of skipping the gate", async () => {
    const repoRoot = mkdtempSync(join(tmpdir(), "f15-"));
    const ctx = { repoRoot, qid: "q" } as never;
    await expect(planGatePrelint({ ctx, state: { flags: {} } as never }, join(repoRoot, "plan.json"))).rejects.toThrow(
      /F1\.5 plan gate: required input missing/,
    );
  });
});
