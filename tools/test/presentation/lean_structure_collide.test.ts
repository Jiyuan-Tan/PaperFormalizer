// Two statements that mean different things must not be drawn alike. Every proposition with at most
// three connectives or quantifiers (∧ ∨ → ↔ ∀ ∃ ∀ᵐ), printed with the fewest brackets Lean's
// precedences allow (`↔` 20, `→` 25 right, `∨` 30 right, `∧` 35 right; a quantifier's body runs to
// the end), is cut; what the drawer shows of a cut — its nesting and each line's text, without the
// glue between lines — must tell them apart. The finding this guards: `P → Q ↔ R` and
// `P → (Q ↔ R)` were both drawn "assume P / then Q ↔ R" (33 such pairs).
import { describe, expect, it } from "vitest";
import { structureStatementView, type ConclusionCard, type HypRow } from "../../src/presentation/lean_structure.js";

type T = { k: "atom"; n: string } | { k: "and" | "or" | "imp" | "iff"; a: T; b: T } | { k: "all" | "ex" | "ae"; a: T };
const PREC = { iff: 20, imp: 25, or: 30, and: 35 } as const;
const SYM = { iff: "↔", imp: "→", or: "∨", and: "∧" } as const;
const Q = { all: "∀ x,", ex: "∃ x,", ae: "∀ᵐ x ∂μ," } as const;

/** `t` at context precedence `p`; `tail`: nothing follows it before the enclosing bracket closes. */
function show(t: T, p: number, tail: boolean): string {
  if (t.k === "atom") return t.n;
  if (t.k === "all" || t.k === "ex" || t.k === "ae") { const s = `${Q[t.k]} ${show(t.a, 0, true)}`; return tail ? s : `(${s})`; }
  const q = PREC[t.k];
  // right-associative except `↔`; a looser connective inside is bracketed
  const left = show(t.a, t.k === "iff" ? q + 1 : q + 1, false);
  const right = show((t as { b: T }).b, t.k === "iff" ? q + 1 : q, tail || q < p);
  const s = `${left} ${SYM[t.k]} ${right}`;
  return q < p ? `(${s})` : s;
}

function* trees(n: number): Generator<T> {
  if (n === 0) { yield { k: "atom", n: "?" }; return; }
  for (const k of ["all", "ex", "ae"] as const) for (const a of trees(n - 1)) yield { k, a };
  for (const k of ["and", "or", "imp", "iff"] as const) for (let i = 0; i < n; i++) for (const a of trees(i)) for (const b of trees(n - 1 - i)) yield { k, a, b };
}
/** Leaves named in reading order, so a cut's lines can only coincide by structure. */
function named(t: T, c = { i: 0 }): T {
  if (t.k === "atom") return { k: "atom", n: `${"ABCDEFGH"[c.i++]} x` };
  if (t.k === "all" || t.k === "ex" || t.k === "ae") return { ...t, a: named(t.a, c) };
  const a = named(t.a, c);
  return { ...t, a, b: named((t as { b: T }).b, c) } as T;
}

/** What the drawer shows: the nesting, each line's text, a line's kind (hypothesis, its parts, a clause, either/or). */
function drawn(sig: string): string {
  const v = structureStatementView(`theorem t : ${sig} := by\n  sorry`);
  if (!v) return `none:${sig}`;
  const hyp = (h: HypRow): unknown => (h.sub ? { prem: h.head ?? "", parts: h.sub.map(card) } : { hyp: h.code });
  const card = (c: ConclusionCard): unknown => ({ ...(c.alt ? { alt: c.alt } : {}), hyps: c.hyps.map(hyp), ...(c.intro ? { intro: c.intro } : {}), ...(c.code ? { code: c.code } : {}), ...(c.sub ? { sub: c.sub.map(card) } : {}) });
  return JSON.stringify({ shared: v.sharedHyps.map(hyp), clauses: v.conclusions.map(card) });
}

describe("no two meanings drawn alike", () => {
  it("every proposition of up to three connectives or quantifiers has a drawing of its own", () => {
    const by = new Map<string, string>();
    const collisions: string[] = [];
    let n = 0;
    for (let k = 1; k <= 3; k++) for (const shape of trees(k)) {
      const sig = show(named(shape), 0, true);
      const d = drawn(sig);
      n++;
      const was = by.get(d);
      if (was !== undefined && was !== sig) collisions.push(`${was}  vs  ${sig}`);
      else by.set(d, sig);
    }
    expect(n).toBeGreaterThan(1000);
    expect(collisions).toEqual([]);
  });
});
