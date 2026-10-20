import { describe, expect, it } from "vitest";
import { runFormalizationStage } from "../../src/formalization/dispatcher.js";

describe("formalization dispatcher — stage ownership", () => {
  it("F3, F3.5 and F4 are phases of the proof-review loop, not stages: a cursor set on one is unhandled (null), never a silent skip", async () => {
    for (const stage of ["3", "3.5", "4"] as const) {
      const result = await runFormalizationStage({ ctx: {} as never, state: { flags: {} } as never, stage, deps: {} as never });
      expect(result).toBeNull();
    }
  });
});
