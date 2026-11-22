/**
 * A definition that fails only in a degenerate case (e.g. the refined
 * parameter 1 + log n/(1 + log(1/q)), printed "when q ≥ 0", is undefined at q = 0) is graded on the
 * definition by its own referee — a pinned reading with the exclusion — never deferred to the statement
 * using it, whose referee never sees the note. The pin binds every result using the definition.
 */
import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { buildCore } from "../../src/verify/core_graph.js";
import type { V15NodeVerdict, V15Review } from "../../src/verify/types.js";

const brief = (): string =>
  readFileSync(path.join(path.dirname(fileURLToPath(import.meta.url)), "..", "..", "src", "verify", "prompts", "V1.5", "review.txt"), "utf8").replace(/\s+/gu, " ");

const ok = (id: string, over: Partial<V15NodeVerdict> = {}): V15NodeVerdict => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "reproduced", witness: null, bookkeeping_assumption: null, reading: null, ...over });

describe("a definition failing only in a degenerate case", () => {
  it("the brief grades it on the definition itself, a pin that binds its users; the deferral to the statement is gone", () => {
    const text = brief();
    expect(text).not.toContain("the grade sits on the statement that uses it there");
    expect(text).toContain("A definition that fails only there is graded on the definition, by its own referee: `pinned`, the exclusion as its `reading` (`of` null), which binds every result using it.");
    expect(text).toContain("unresolvable: grade it by the rule for degenerate cases below.");
  });

  it("its pinned exclusion reaches every result using the definition, and only those", () => {
    const core = {
      qid: "deg",
      symbols: [],
      assumptions: [],
      definitions: [{ id: "def:refined", name: "refined parameter", construction: "$\\mathcal X = 1 + \\log n/(1 + \\log(1/q))$ when $q \\ge 0$" }],
      statements: [
        { id: "thm:main", kind: "theorem", statement: "The rate is $n^{-1/\\mathcal X}$.", depends_on: ["def:refined"], proof_tex: "Direct.", status: "to-prove" },
        { id: "lem:other", kind: "lemma", statement: "A bound holds.", depends_on: [], proof_tex: "Direct.", status: "to-prove" },
      ],
      target_estimand: "t",
      bibliography: [],
    } as unknown as Core;
    const review: V15Review = {
      verdict: "PASS",
      summary: "s",
      nodes: [
        ok("def:refined", { ambiguity: "pinned", detail: "undefined at $q = 0$, a degenerate endpoint", reading: { reading: "$0 < q < 1$", evidence: "the formula divides by $1 + \\log(1/q)$, undefined at $q = 0$", of: null } }),
        ok("thm:main"),
        ok("lem:other"),
      ],
    };
    const { core: built, added } = buildCore(core, { review });
    const pin = built.assumptions.find((a) => a.condition === "$0 < q < 1$")!;
    expect(pin.id).toMatch(/^ass:pin-/u);
    expect(added).toEqual([{ id: pin.id, node: "def:refined" }]);
    expect(built.statements.find((s) => s.id === "thm:main")!.depends_on).toContain(pin.id);
    expect(built.statements.find((s) => s.id === "lem:other")!.depends_on).not.toContain(pin.id);
  });
});
