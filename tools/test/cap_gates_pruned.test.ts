// Only gates a live F-stage path can still set remain registered.
import { describe, expect, it } from "vitest";
import { CAP_GATE_FLAGS } from "../src/cap_gates.js";

describe("cap gates after the D stages were removed", () => {
  it("registers exactly the gates a live F-stage path can set", () => {
    expect([...CAP_GATE_FLAGS].sort()).toEqual([
      "general_review_halt",
      "proof_loop_cap_hit",
    ]);
    for (const retired of ["substrate_build_required", "stage_neg1_fallback", "theorem_splits_cap_hit", "stage0_budget_exhausted", "d0_loop_cap_hit"]) {
      expect(CAP_GATE_FLAGS).not.toContain(retired);
    }
  });

});

describe("a retired flag", () => {
  it("is in no schema, and a state file written with it still loads (flags pass through)", async () => {
    const { createInitialState, stateSchema } = await import("../src/state.js");
    const old = createInitialState("q") as unknown as { flags: Record<string, unknown> };
    old.flags.substrate_build_required = "build X";
    expect((stateSchema.parse(JSON.parse(JSON.stringify(old))) as unknown as { flags: Record<string, unknown> }).flags.substrate_build_required).toBe("build X");
  });
});

describe("fields no code reads are not asked of a model", () => {
  it("a shard verdict is the node verdict: no `depends_on_verdicts_used`", async () => {
    const { SHARD_NODE_FIELDS_TEXT, SHARD_NODE_REPLY } = await import("../src/verify/v1_5_schema.js");
    expect(JSON.stringify(SHARD_NODE_REPLY)).not.toContain("depends_on_verdicts_used");
    expect(SHARD_NODE_FIELDS_TEXT).not.toContain("depends_on_verdicts_used");
    const { readFileSync } = await import("node:fs");
    expect(readFileSync(new URL("../src/verify/referee_shard_prompts.ts", import.meta.url), "utf8")).not.toContain("depends_on_verdicts_used");
  });
});
