import { describe, expect, it } from "vitest";
import { parseLedger } from "../../src/toolkit/ledger.js";

describe("toolkit ledger", () => {
  it("preserves decisions and unknown fields through parse", () => {
    const l = parseLedger(JSON.stringify({ version: 1, declarations: [], decisions: [{ id: 1 }], note: "keep" }));
    expect(l.decisions).toEqual([{ id: 1 }]);
    expect((l as Record<string, unknown>).note).toBe("keep");
  });
});
