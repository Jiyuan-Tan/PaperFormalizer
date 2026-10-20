/** The proof-review loop's F2 reroute sent the plan back to F1: the stage rewinds, it does not escalate. */
import { describe, it, expect, vi } from "vitest";
import { createInitialState } from "../../src/state.js";
import type { StageResult } from "../../src/types.js";

const rewound: StageResult = { stage: "2", status: "rewound", advance: false, message: "F2 structural plan gate refused the plan the scaffolder's sync-back left" };

vi.mock("../../src/shared/lean_lsp_server.js", () => ({ startSharedLeanLsp: async () => ({ url: "http://127.0.0.1:0", stop: async () => {} }) }));
vi.mock("../../src/formalization/stage2.js", () => ({
  runStage2: async (args: { state: { stage_completed: string } }) => {
    args.state.stage_completed = "1";
    return rewound;
  },
}));
vi.mock("../../src/formalization/proof_review_loop.js", async (original) => ({
  ...(await original<typeof import("../../src/formalization/proof_review_loop.js")>()),
  writeRunBarrel: async () => null,
  // The loop as it reacts to a reroute that did not complete: it escalates.
  runProofReviewLoop: async (a: { scaffold: (x: { redirect: string; targets: string[] }) => Promise<void> }) => {
    const failure = await a.scaffold({ redirect: "fix it", targets: ["def:model"] }).then(() => "", (e: Error) => e.message);
    return { status: "escalate", route: "fix-source", phase: "2.5", reason: `F2 re-scaffold did not complete: ${failure}` };
  },
}));

describe("F2.5 loop: a reroute whose F2 pass sent the plan back to F1", () => {
  it("returns F2's rewind (cursor at F1, no escalation on record) instead of a checkpoint", async () => {
    const { runFormalizationStage } = await import("../../src/formalization/dispatcher.js");
    const state = createInitialState("plan_rewind_test");
    state.stage_completed = "2";
    const result = await runFormalizationStage({ ctx: { repoRoot: "/nonexistent", qid: "plan_rewind_test", dryRun: false, resume: true } as never, state, stage: "2.5", deps: {} as never });
    expect(result).toBe(rewound);
    expect(state.stage_completed).toBe("1");
    expect(state.flags.proof_review_escalation_pending ?? null).toBeNull();
  });
});
