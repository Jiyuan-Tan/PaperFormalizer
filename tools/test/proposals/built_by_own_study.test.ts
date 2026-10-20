// A study that halted, was continued by hand and finished leaves its result in the toolkit; the
// re-run apply must not then refuse the entry because "its name is already declared" (live Li–Ding
// round B, the Wald comparison).
import { describe, expect, it } from "vitest";
import { builtByOwnStudy } from "../../src/proposals/build.js";

const decl = (name: string, origin: Record<string, unknown>) => ({ name, origin: origin as { kind: string; slug: string } });

describe("builtByOwnStudy", () => {
  const p = { id: "b-wald", round: "B" as const };
  const mine = decl("Toolkit.F.wald", { kind: "proposal", slug: "paper", round: "B", proposal_id: "b-wald" });
  it("a name this proposal's own study declared is not a collision", () => {
    expect(builtByOwnStudy([mine], "paper", p, "Toolkit.F.wald")).toBe(true);
  });
  it("a name declared by anything else still is", () => {
    expect(builtByOwnStudy([mine], "paper", p, "Toolkit.F.other")).toBe(false);
    expect(builtByOwnStudy([decl("Toolkit.F.wald", { kind: "proposal", slug: "other_paper", round: "B", proposal_id: "b-wald" })], "paper", p, "Toolkit.F.wald")).toBe(false);
    expect(builtByOwnStudy([decl("Toolkit.F.wald", { kind: "study", slug: "x" })], "paper", p, "Toolkit.F.wald")).toBe(false);
  });
});
