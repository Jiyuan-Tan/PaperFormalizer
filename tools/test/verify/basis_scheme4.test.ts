/**
 * Basis scheme 4: a symbol reading, a symbol-table entry and a V1.5-appended condition are read by
 * their MEANING (`basis_text.ts`), so re-typesetting one re-opens no verdict, while a change of meaning
 * (or of the reading's state) still does — on a cut of the live CNS run too; and the delta log says why
 * each node is re-graded.
 */
import { readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { normalizeBasisText as norm } from "../../src/verify/basis_text.js";
import {
  basisInputs,
  basisInputsV4,
  basisOf,
  buildCore,
  nodeFingerprint,
  regradeCause,
  type BasisExtra,
} from "../../src/verify/core_graph.js";
import { partitionByBasis, regradeBreakdownLine, symbolBasisExtra } from "../../src/verify/stage_v1_5.js";
import type { V15NodeVerdict, V15Review, V15SymbolVerdict } from "../../src/verify/types.js";

describe("normalizeBasisText: typesetting is forgotten, meaning is not", () => {
  it("forgets Unicode vs TeX, spacing/sizing commands and synonymous commands; keeps a font, a subscript, a word; is idempotent", () => {
    const same = [
      ["W ∈ 𝒲 is a random vector with γ₀(W) ≤ 1.", "$W\\in\\mathcal{W}$ is a random vector with $\\gamma_0(W)\\le 1$"],
      ["$\\left( a \\,+\\; b \\right)$", "$(a+b)$"],
      ["$a \\le b \\to c$", "$a\\leq b\\rightarrow c$"],
    ];
    for (const [a, b] of same) expect(norm(a!)).toBe(norm(b!));
    const kept = [
      ["$\\mathcal{W}$", "$\\mathbb{W}$"],
      ["$\\gamma_0$", "$\\gamma_1$"],
      ["$\\sigma$ is fixed", "$\\sigma$ is random"],
    ];
    for (const [a, b] of kept) expect(norm(a!)).not.toBe(norm(b!));
    for (const t of ["W ∈ 𝒲 is γ₀.", "$\\left(\\hat\\theta\\right)$ “x”", "``a'' b~\\ref{x}."]) expect(norm(norm(t))).toBe(norm(t));
  });
});

function core(): Core {
  return {
    qid: "fp4",
    symbols: [
      { name: "\\sigma", type: "scale", def: "$\\sigma^2 = E[\\varepsilon^2]$" },
      { name: "\\theta", type: "parameter" },
      { name: "K", type: "kernel" },
    ],
    assumptions: [{ id: "ass:scale", condition: "$\\sigma > 0$.", free_symbols: ["\\sigma"] }],
    definitions: [],
    statements: [
      { id: "thm:b", kind: "theorem", statement: "The limit is normal.", depends_on: ["ass:scale"], status: "to-prove" },
      { id: "lem:a", kind: "lemma", statement: "$\\hat\\theta \\to \\theta$.", depends_on: [], status: "to-prove" },
    ],
    target_estimand: "x",
    bibliography: [],
  } as unknown as Core;
}

const sym = (name: string, over: Partial<V15SymbolVerdict> = {}): V15SymbolVerdict =>
  ({ name, meaning: "ok", fix: null, ambiguity: "ok", reading: null, redefined_at: null, detail: "d", ...over }) as V15SymbolVerdict;
const pinned = (name: string, reading: string, over: Partial<V15SymbolVerdict> = {}): V15SymbolVerdict =>
  sym(name, { ambiguity: "pinned", reading: { reading, evidence: "Section 2" }, ...over });
/** The core a pass with these symbol verdicts grades: their fixes and readings written into the table. */
const gradedOf = (c: Core, verdicts: V15SymbolVerdict[]): Core => buildCore(c, { symbols: verdicts }).core;
/** The basis extra such a pass gives (`symbolPass`). */
const extraOf = (c: Core, verdicts: V15SymbolVerdict[]): BasisExtra => symbolBasisExtra(gradedOf(c, verdicts), verdicts);
/** A node's fingerprint as a pass with these verdicts records it. */
const fp = (c: Core, id: string, verdicts: V15SymbolVerdict[]): string => nodeFingerprint(gradedOf(c, verdicts), id, extraOf(c, verdicts));

describe("scheme 4: the basis reads a symbol by its meaning", () => {
  it("a re-typeset pinned reading leaves the dependent statement's basis unchanged; a change of its meaning or its state (pinned / open / redefined) invalidates", () => {
    const c = core();
    expect(fp(c, "thm:b", [pinned("\\sigma", "$\\sigma$ is a fixed,  population scale")])).toBe(fp(c, "thm:b", [pinned("\\sigma", "$\\sigma$ is a fixed, population scale.")]));
    const base = fp(c, "thm:b", [pinned("\\sigma", "$\\sigma$ is fixed.")]);
    expect(fp(c, "thm:b", [pinned("\\sigma", "$\\sigma$ is random.")])).not.toBe(base);
    expect(fp(c, "thm:b", [sym("\\sigma", { ambiguity: "unresolvable" })])).not.toBe(base);
    expect(fp(c, "thm:b", [pinned("\\sigma", "$\\sigma$ is fixed.", { redefined_at: "Later, σ is the sample scale." })])).not.toBe(base);
    expect(fp(c, "thm:b", [])).not.toBe(base);
    // A symbol the node does not use moves nothing.
    expect(fp(c, "lem:a", [pinned("\\sigma", "$\\sigma$ is random.")])).toBe(fp(c, "lem:a", [pinned("\\sigma", "$\\sigma$ is fixed.")]));
  });
});

describe("regradeCause", () => {
  const c = core();
  const inp = (x: Core, id: string, e: BasisExtra = new Map()) => basisInputs(x, id, e);
  it("names the first thing that moved", () => {
    const v0 = [pinned("\\sigma", "$\\sigma$ is fixed.")];
    const g0 = gradedOf(c, v0);
    const e0 = extraOf(c, v0);
    const was = { inputs: inp(g0, "thm:b", e0), clean: true };
    expect(regradeCause(null, inp(g0, "thm:b"))).toBe("new");
    expect(regradeCause({ ...was, clean: false }, inp(g0, "thm:b", e0))).toBe("not clean before");
    expect(regradeCause({ inputs: undefined, clean: true }, inp(g0, "thm:b", e0))).toBe("no comparable record");
    const restated = { ...g0, statements: g0.statements.map((s) => (s.id === "thm:b" ? { ...s, statement: "The limit is normal (restated)." } : s)) } as Core;
    expect(regradeCause(was, inp(restated, "thm:b", e0))).toBe("content");
    const hyp = { ...g0, assumptions: g0.assumptions.map((a) => ({ ...a, condition: "$\\sigma \\ge 1$." })) } as Core;
    expect(regradeCause(was, inp(hyp, "thm:b", e0))).toBe("dependency");
    const random = [pinned("\\sigma", "$\\sigma$ is random.")];
    expect(regradeCause(was, inp(gradedOf(c, random), "thm:b", extraOf(c, random)))).toBe("symbol meaning");
    const retyped = [pinned("\\sigma", "$\\sigma$ is  fixed")];
    expect(regradeCause(was, inp(gradedOf(c, retyped), "thm:b", extraOf(c, retyped)))).toBe("cache withdrawn");
    expect(regradeCause(was, inp(g0, "thm:b", e0))).toBe("cache withdrawn");
    expect(regradeCause(was, basisInputs(g0, "thm:b", e0, "a rewritten note"))).toBe("note");
  });
});

describe("scheme 4 on the live CNS run (cut to five nodes)", () => {
  const fx = JSON.parse(readFileSync(path.join(import.meta.dirname, "fixtures/cns_basis_scheme4.json"), "utf8")) as {
    graded: { core: Core; confirmed: Record<string, string>; confirmed_scheme: number; review: V15Review };
    next: { core: Core; symbols: V15SymbolVerdict[] };
  };
  const ids = Object.keys(fx.graded.confirmed).sort();
  /** The cache as a scheme-4 pass on the graded core records it (the verdicts' readings in its table). */
  const graded = () => {
    const syms = fx.graded.review.symbols ?? [];
    const g = gradedOf(fx.graded.core, syms);
    const e = extraOf(fx.graded.core, syms);
    const confirmed = Object.fromEntries(ids.map((id) => [id, basisOf(basisInputsV4(g, id, e))]));
    const prior = {
      ...fx.graded.review,
      nodes: fx.graded.review.nodes.map((n: V15NodeVerdict) =>
        ids.includes(n.id) ? { ...n, basis: confirmed[n.id], basis_scheme: 4, basis_inputs: basisInputsV4(g, n.id, e) } : n,
      ),
    } as V15Review;
    return { confirmed, prior };
  };

  it("the next pass (the compile sweep re-typeset the symbol table, the model re-wrote the readings): re-typesets are carried, re-written readings re-graded", () => {
    const { confirmed, prior } = graded();
    const next = extraOf(fx.next.core, fx.next.symbols);
    const part = partitionByBasis(gradedOf(fx.next.core, fx.next.symbols), confirmed, prior, next);
    // A re-written reading is a changed meaning of the symbol: every node using it is re-graded —
    // statements, and (the reading being the symbol's def, 2026-09-30) the hypotheses and definitions too.
    expect(part.carried.map((n) => n.id)).toEqual([]);
    expect(part.toGrade.filter((id) => ids.includes(id)).sort()).toEqual(["ass:dml-noise", "def:algorithm-target", "def:operator-norm", "lem:rr-exists-rdd", "thm:local-finite-noise"]);
    const others = part.toGrade.filter((id) => !ids.includes(id)).length; // not in the cut review: new
    // (one of them through a node it uses: the symbols left open that bind that node changed)
    expect(part.why).toEqual({ causes: { "symbol meaning": 4, dependency: 1, new: others } });
    expect(regradeBreakdownLine(part.why)).toBe(
      `delta review: why re-graded — 0 content changed, 1 dependency changed, 4 symbol meaning changed, ${others} new`,
    );
  });
});
