/**
 * The fixer repairs with the main theorems in mind (SERVES block; user decision 2026-09-24).
 */
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { servesBlock } from "../../src/verify/stage_v1.js";

const st = (id: string, kind: string, statement: string, depends_on: string[] = []) => ({ id, kind, statement, depends_on, status: "to-prove" });
const core = (statements: ReturnType<typeof st>[], assumptions: Array<{ id: string; condition: string }> = []): Core =>
  ({
    qid: "rc",
    symbols: [],
    assumptions: assumptions.map((a) => ({ ...a, kind: "regularity", novel: { flag: true, justification: "paper" } })),
    definitions: [],
    statements,
    target_estimand: "t",
    bibliography: [],
  }) as unknown as Core;

describe("SERVES block (fixer repairs a lemma with the main theorems in mind)", () => {
  const c = core(
    [
      st("lem:bias", "lemma", "The bias is $O(h^2)$. [Hypotheses: ass:k]", ["ass:k"]),
      st("lem:mid", "lemma", "The remainder is $o_p(n^{-1/2})$.", ["lem:bias"]),
      st("thm:clt", "theorem", "The estimator is asymptotically normal.", ["lem:mid"]),
      st("thm:rate", "theorem", "The estimator converges at rate $n^{-2/5}$.", ["lem:bias"]),
      st("lem:side", "lemma", "An unrelated bound.", []),
    ],
    [{ id: "ass:k", condition: "K is a kernel of order 2" }],
  );
  const file = { key_results: ["thm:clt"], key_contribution: "asymptotic normality at the optimal bandwidth" };

  it("lists every main theorem resting on a node (two users; transitively; an assumption too), with its printed statement and the key contribution", () => {
    const b = servesBlock(c, file, ["lem:bias"]);
    expect(b).toContain("Key contribution: asymptotic normality at the optimal bandwidth");
    expect(b).toContain("lem:bias — SERVES (main results):");
    expect(b).toContain("  - thm:clt: The estimator is asymptotically normal.");
    expect(b).toContain("  - thm:rate: The estimator converges at rate $n^{-2/5}$.");
    // transitive through an intermediate lemma; an assumption node too; the hypothesis list stripped
    expect(servesBlock(c, file, ["lem:mid"])).toContain("  - thm:clt:");
    expect(servesBlock(c, file, ["lem:mid"])).not.toContain("thm:rate");
    const a = servesBlock(c, file, ["ass:k"]);
    expect(a).toContain("ass:k — SERVES (main results):");
    expect(a).toContain("thm:rate");
    expect(a).not.toContain("[Hypotheses");
  });
  it("is absent for a main theorem no other main theorem uses and for a node no main theorem uses", () => {
    expect(servesBlock(c, file, ["thm:rate"])).toBe("");
    expect(servesBlock(c, file, ["lem:side"])).toBe("");
    expect(servesBlock(c, file, ["thm:rate", "lem:side", "run"])).toBe("");
  });
  it("clips a long statement to 600 characters", () => {
    const long = core([st("lem:a", "lemma", "x"), st("thm:b", "theorem", `The claim ${"y ".repeat(500)}`, ["lem:a"])]);
    const line = servesBlock(long, null, ["lem:a"]).split("\n").find((l) => l.startsWith("  - thm:b"))!;
    expect(line.length).toBeLessThanOrEqual("  - thm:b: ".length + 600);
    expect(line.endsWith("…")).toBe(true);
  });
});
