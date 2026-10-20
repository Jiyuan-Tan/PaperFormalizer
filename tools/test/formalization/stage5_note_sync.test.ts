import { describe, it, expect } from "vitest";
import { unsyncedLoadBearingAssumptions } from "../../src/formalization/stage5.js";
import type { AddedAssumption, StateJson } from "../../src/types.js";

const state = (added: AddedAssumption[]): StateJson =>
  ({ added_assumptions: added }) as unknown as StateJson;

const premise = (label: string, classification = "substrate-gate"): AddedAssumption =>
  ({ label, statement: `the ${label} bound holds`, classification }) as AddedAssumption;

describe("unsyncedLoadBearingAssumptions", () => {
  it("flags a load-bearing premise whose label is absent from the note", () => {
    const out = unsyncedLoadBearingAssumptions(state([premise("A1")]), "## Load-bearing hypotheses\n(none)\n");
    expect(out.map((a) => a.label)).toEqual(["A1"]);
  });

  // A substring test would let an unrelated `A10` row satisfy `A1`, suppressing the warning for
  // a genuinely missing premise; punctuation-delimited mentions still count.
  it.each([
    ["- **A10**: an unrelated premise\n- **A11**: another\n", ["A1"]],
    ["- **A1**: the A1 bound holds\n", []],
    ["see hypothesis (A1); and `A1`,", []],
  ])("matches whole labels only in %j", (note, expected) => {
    expect(unsyncedLoadBearingAssumptions(state([premise("A1")]), note).map((a) => a.label)).toEqual(expected);
  });
});
