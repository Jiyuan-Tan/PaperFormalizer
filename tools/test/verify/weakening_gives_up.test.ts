/**
 * A referee-demoted repair gives up what its note's own `gives_up` field says, else the referee's
 * detail (live DFM 2026-09-26: the referee's per-hypothesis details, with their satisfiability
 * instance, were printed as "Gives up").
 */
import { describe, expect, it } from "vitest";
import type { PatchFile } from "../../src/verify/patches.js";
import { convertWeakeningPatches } from "../../src/verify/weakening.js";
import { cannedExplanation } from "./owner_explained.js";

const patch = (gives_up: string | null) => ({
  node: "thm:a",
  corrected_statement: null,
  ops: [{ op: "replace" as const, unit: "thm:a/1", tex: "Suppose $0<r<1$. Then the bound holds." }],
  proof_note: "p",
  owner_explanation: { ...cannedExplanation("thm:a"), gives_up },
});
const detail = "weakens the contribution: excludes matched pairs. The added conditions are satisfiable: Normal pairs.";
const convert = (gives_up: string | null) =>
  convertWeakeningPatches({ patches: [patch(gives_up)], unfixable: [] } as unknown as PatchFile, [{ id: "thm:a", detail }]).unfixable[0]!;

describe("the given_up of a referee-demoted repair", () => {
  it("is the note's gives_up when it has one (the suggestion keeps the repair's replacement ops), else the referee's detail (prefix dropped), marked as the referee's", () => {
    const u = convert("matched-pair designs");
    expect(u.suggested_repair!.given_up).toBe("matched-pair designs");
    expect(u.suggested_repair!.given_up_by).toBeUndefined();
    expect(u.suggested_repair!.ops).toEqual(patch(null).ops);
    expect(u.reason).toContain("excludes matched pairs"); // the referee's reason is kept as the reason
    expect(convert(null).suggested_repair!.given_up).toBe("excludes matched pairs. The added conditions are satisfiable: Normal pairs.");
    expect(convert(null).suggested_repair!.given_up_by).toBe("referee");
  });
});
