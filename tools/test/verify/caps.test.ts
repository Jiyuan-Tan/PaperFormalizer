import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { atCap, capMessage, capRecord, clearCap, countRound, errorScope, nextRound, patchBackstop } from "../../src/verify/caps.js";
import type { VerifyState } from "../../src/verify/types.js";

/** A chain core: def:d (level 0), then one statement per level, each using the one below. */
function chain(n: number): Core {
  const statements = Array.from({ length: n }, (_, i) => ({ id: `lem:s${i + 1}`, depends_on: i === 0 ? ["def:d"] : [`lem:s${i}`] }));
  return { definitions: [{ id: "def:d", depends_on: [] }], assumptions: [{ id: "hyp:p", depends_on: [] }], statements } as unknown as Core;
}
const fresh = (): VerifyState => ({ patch_rounds: 0 }) as unknown as VerifyState;

describe("per-level error caps (user decision 2026-09-26)", () => {
  it("halts at the 4th round of one level while other levels proceed; the receipt names the level and its nodes", () => {
    const core = chain(3); // L0..L3: backstop 12
    const v = fresh();
    const l1 = errorScope(v, core, ["lem:s1"]);
    expect(l1).toEqual({ level: "L1", nodes: ["lem:s1"], backstop: 12 });
    expect(nextRound(v, "error", l1)).toBe("error round 1/3 at level L1 (total 1/12)");
    for (let k = 0; k < 3; k += 1) {
      expect(atCap(v, "error", l1)).toBe(false);
      countRound(v, "error", l1);
    }
    expect(atCap(v, "error", l1)).toBe(true);
    const l2 = errorScope(v, core, ["lem:s2"]);
    expect(atCap(v, "error", l2)).toBe(false);
    expect(countRound(v, "error", l2)).toBe("error round 1/3 at level L2 (total 4/12)");
    const g = errorScope(v, core, null);
    expect(g.level).toBe("global");
    expect(atCap(v, "error", g)).toBe(false);
    const cap = capRecord(v, "error", "V1.5", [], null, l1);
    expect(cap).toMatchObject({ counter: "patch_rounds", rounds: 3, cap: 3, level: "L1", nodes: ["lem:s1"], backstop: 12, backstop_hit: false });
    expect(capMessage(cap, "run")).toContain("level L1 (lem:s1) is at its cap (3/3");
  });

  it("the whole-run backstop: 3 × the core's level count, at least 6", () => {
    expect(patchBackstop(chain(1))).toBe(6);
    expect(patchBackstop(chain(4))).toBe(15);
    const core = chain(1); // L0, L1: backstop 6
    const v = fresh();
    for (const owners of [["lem:s1"], ["lem:s1"], null, null, ["def:d"], ["def:d"]]) countRound(v, "error", errorScope(v, core, owners));
    expect(v.patch_rounds_by_level).toEqual({ L1: 2, global: 2, L0: 2 });
    const l1 = errorScope(v, core, ["lem:s1"]);
    expect(atCap(v, "error", l1)).toBe(true);
    const cap = capRecord(v, "error", "F-rewind", [], null, l1);
    expect(cap).toMatchObject({ rounds: 6, cap: 6, level: "L1", backstop_hit: true });
    expect(capMessage(cap, "run")).toContain("whole-run backstop is reached");
    expect(clearCap(v, cap)).toContain("whole-run backstop reset");
    expect([v.patch_rounds, v.patch_rounds_by_level]).toEqual([0, { L1: 2, global: 2, L0: 2 }]);
    expect(atCap(v, "error", l1)).toBe(false);
  });

  it("--clear-patch-cap resets only the capped level", () => {
    const core = chain(3);
    const v = fresh();
    const l1 = errorScope(v, core, ["lem:s1"]);
    const l2 = errorScope(v, core, ["lem:s2"]);
    for (let k = 0; k < 3; k += 1) countRound(v, "error", l1);
    countRound(v, "error", l2);
    const cap = capRecord(v, "error", "V1.5", [], null, l1);
    clearCap(v, cap);
    expect([v.patch_rounds, v.patch_rounds_by_level]).toEqual([4, { L1: 0, L2: 1 }]);
    expect(atCap(v, "error", l1)).toBe(false);
  });

  it("a patch hypothesis counts at its owner's level; refinement rounds keep their flat cap", () => {
    const core = chain(2);
    const v = fresh();
    expect(errorScope(v, core, ["lem:s2"]).level).toBe("L2");
    for (let k = 0; k < 3; k += 1) countRound(v, "refinement");
    expect(atCap(v, "refinement")).toBe(true);
    expect(v.patch_rounds_by_level).toEqual({});
  });

  it("an error round without a scope is refused where the cap is judged", () => {
    expect(() => atCap(fresh(), "error")).toThrow(/needs its scope/);
  });
});
