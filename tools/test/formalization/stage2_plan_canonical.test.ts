import { describe, expect, it } from "vitest";
import { canonicalizeCitedPlanAfterF2 } from "../../src/formalization/stage2.js";
import type { Core } from "../../src/core/schema.js";

describe("canonicalizeCitedPlanAfterF2", () => {
  it("a core assumption synced back as lean_kind `def` is the planned `assumption` (a `def … : Prop`), never a gate refusal", () => {
    const core = { assumptions: [{ id: "ass:pin-1", condition: "the conclusion holds for every unit" }], definitions: [], statements: [] } as unknown as Core;
    const plan = { nodes: { "ass:pin-1": { lean_kind: "def", lean_name: "Pin1" }, "def:x": { lean_kind: "def", lean_name: "X" } } };
    const r = canonicalizeCitedPlanAfterF2(plan, core);
    expect(r.changed).toBe(true);
    expect((r.plan as typeof plan).nodes["ass:pin-1"].lean_kind).toBe("assumption");
    expect((r.plan as typeof plan).nodes["def:x"].lean_kind).toBe("def");
    expect(canonicalizeCitedPlanAfterF2(r.plan, core).changed).toBe(false);
  });
});
