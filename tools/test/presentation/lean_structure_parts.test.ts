// The cuts the third audit asked for, in `lean_structure_tc.ts`: a NAMED hypothesis whose type has
// parts is cut like a premise with parts (its head line, then a row per part); a disjunction of
// claims with parts is one card per alternative; and no implication is read where Lean's
// precedence makes the arrow a side of a top-level `↔`. With each, the strict round trip: the rows
// of the view, in reading order, are the statement's text, and what stands between two rows is
// only brackets, `:`, `,` and the connective the cut implies.
import { describe, expect, it } from "vitest";
import { leanStatementView, statementBody, viewRows } from "../../src/formalization/lean_rows.js";
import { structureStatementView } from "../../src/presentation/lean_structure.js";
import { iffAtLevel } from "../../src/presentation/lean_structure_tc.js";
import { squash } from "../../src/presentation/lean_text.js";

const T = (sig: string) => `theorem t ${sig} := by\n  sorry`;

/** The rows as F5 asks them, and what stands between them in the statement. */
function cut(sig: string): { rows: string[]; glue: string[] } {
  const v = leanStatementView(T(sig));
  if (!v) throw new Error(`no view: ${sig}`);
  const rows = viewRows(v);
  const text = squash(statementBody(v.statement));
  const glue: string[] = [];
  let pos = 0;
  for (const r of rows) {
    const code = squash(r.kind === "binder" ? `${r.names}:${r.lean}` : r.kind === "instance" ? `[${r.lean}]` : r.lean);
    const at = text.indexOf(code, pos);
    expect(at, `${sig}: row ${r.id} «${r.lean}» in order`).toBeGreaterThanOrEqual(0);
    glue.push(text.slice(pos, at));
    pos = at + code.length;
  }
  glue.push(text.slice(pos));
  // … and the name of a hypothesis whose head line is its name alone (`(h :`)
  for (const g of glue) expect(g.replace(/\([^\s():]+:$/, "(:"), `${sig}: glue`).toMatch(/^[()[\]{}⦃⦄:,→∧∨∀]*$/);
  return { rows: rows.map((r) => `${r.kind}:${r.kind === "binder" ? `${r.names} : ${r.lean}`.trim() : r.lean}`), glue };
}

describe("a named hypothesis with parts", () => {
  // The finding: 60 rows held 170 conjuncts (`(hstat : ∀ k, … ∧ … ∧ …)` was one row).
  it("is its head line — the name and what it quantifies, assumes or introduces — then a row per part", () => {
    expect(cut("(hstat : ∀ k, Measurable (f k) ∧ Integrable (f k) μ ∧ 0 ≤ f k) : C").rows).toEqual([
      "binder:hstat : ∀ k,", "premise:Measurable (f k)", "premise:Integrable (f k) μ", "premise:0 ≤ f k", "conclusion:C",
    ]);
    expect(cut("(hex_cate : kind = .cate → A ∧ B) : D").rows).toEqual(["binder:hex_cate : kind = .cate →", "premise:A", "premise:B", "conclusion:D"]);
    // a head that is the name alone states nothing: a label of its parts (the page draws it), no row
    expect(cut("(hInterior : A ∧ B ∧ C ∧ D) : E").rows).toEqual(["premise:A", "premise:B", "premise:C", "premise:D", "conclusion:E"]);
    expect(cut("(hDerivative : ∃ δ, 0 < δ ∧ P δ) : E").rows).toEqual(["binder:hDerivative : ∃ δ,", "premise:0 < δ", "premise:P δ", "conclusion:E"]);
    // an implication is cut even when what it concludes is one claim
    expect(cut("(hk : kind = .cate → A) : E").rows).toEqual(["binder:hk : kind = .cate →", "premise:A", "conclusion:E"]);
    // and so is a named premise, a binder group of a lifted `∀` header, and a named binder's parts inside parentheses
    expect(cut(": ∀ (x : ℕ) (hx : A x ∧ B x ∧ C x), D x").rows).toEqual(["binder:x : ℕ", "premise:A x", "premise:B x", "premise:C x", "conclusion:D x"]);
    expect(cut("(h : (∀ k, A k ∧ B k)) : E").rows).toEqual(["binder:h : (∀ k,", "premise:A k", "premise:B k", "conclusion:E"]);
  });
  it("stays one row for a two-sided bound, a lone quantified claim, a function, an object", () => {
    expect(cut("(hρ : 0 ≤ ρ ∧ ρ ≤ 1) : E").rows).toEqual(["binder:hρ : 0 ≤ ρ ∧ ρ ≤ 1", "conclusion:E"]);
    expect(cut("(hpos : ∀ n, 0 < f n) : E").rows).toEqual(["binder:hpos : ∀ n, 0 < f n", "conclusion:E"]);
    expect(cut("(m : Bool → X → ℝ) (hseq : ℕ → ℝ) : E").rows).toEqual(["binder:m : Bool → X → ℝ", "binder:hseq : ℕ → ℝ", "conclusion:E"]);
    expect(cut("{h : A ∧ B ∧ C} : E").rows).toEqual(["binder:h : A ∧ B ∧ C", "conclusion:E"]);
  });
  it("keeps the binder whole in its code: the drawer and the round trip of the signature see it as written", () => {
    const v = structureStatementView(T("(hI : A ∧ B ∧ C) : E"))!;
    expect(v.sharedHyps[0]).toMatchObject({ chip: "hyp", code: "(hI : A ∧ B ∧ C)", head: "(hI :" });
    expect(v.sharedHyps[0]!.sub!.map((c) => c.code)).toEqual(["A", "B", "C"]);
  });
  // The finding: `(hcov : A ∧ B ∧ C)` gave F5 a row `hcov : ` with nothing in it to link.
  it("gives a head that is the name alone no id: no row is asked or linked without text", () => {
    const v = leanStatementView(T("(n : ℕ) (hcov : A ∧ B ∧ C) (hk : ∀ k, D k → E k) : F"))!;
    expect(v.sharedHyps.map((h) => [h.head, h.id])).toEqual([[undefined, "r1"], ["(hcov :", undefined], ["(hk : ∀ k, D k →", "r5"]]);
    expect(viewRows(v).map((r) => `${r.id} ${r.names} : ${r.lean}`)).toEqual(["r1 n : ℕ", "r2  : A", "r3  : B", "r4  : C", "r5 hk : ∀ k, D k →", "r6  : E k", "r7  : F"]);
  });
});

describe("either / or", () => {
  it("a disjunction of claims with parts is one card per alternative, `∨` binding looser than `∧`", () => {
    const v = structureStatementView(T(": A ∧ B ∨ C ∧ D"))!;
    expect(v.conclusions[0]!.sub!.map((c) => [c.alt, c.sub?.map((s) => s.code) ?? c.code])).toEqual([["either", ["A", "B"]], ["or", ["C", "D"]]]);
    expect(cut(": A ∧ B ∨ C ∧ D").glue).toEqual([":", "∧", "∨", "∧", ""]);
    expect(cut("(h : A ∨ B ∧ C) : D").rows).toEqual(["premise:A", "premise:B", "premise:C", "conclusion:D"]);
  });
  it("leaves a plain disjunction whole, and one under a looser connective or a binder", () => {
    for (const [sig, leaf] of [[": A ∨ B", "A ∨ B"], [": (A ∧ B ∨ C) ↔ D", "(A ∧ B ∨ C) ↔ D"]]) expect(structureStatementView(T(sig))!.conclusions[0]!.code, sig).toBe(leaf);
    expect(structureStatementView(T(": A ∧ B ∨ C → D"))!.sharedHyps.map((h) => h.code)).toEqual(["A ∧ B ∨ C"]);
  });
});

// The finding: `P → Q ↔ R` was drawn "assume P / then Q ↔ R"; Lean reads `(P → Q) ↔ R`
// (`infix:20 " ↔ "`, the arrow `checkPrec 25`): 33 constructed statements drawn alike for two meanings.
describe("↔ and →", () => {
  it("no implication is cut where a top-level `↔` makes the arrow a side of the iff", () => {
    for (const sig of [": A → B ↔ C", ": A ↔ B → C", ": (A → B) ↔ C", ": A → B → C ↔ D", ": A ∧ B → C ↔ D"]) {
      const v = structureStatementView(T(sig))!;
      expect(v.sharedHyps, sig).toEqual([]);
      expect(v.conclusions.map((c) => c.code), sig).toEqual([sig.slice(2)]);
    }
    // an iff inside brackets or under a binder is its own clause's
    expect(cut(": A → (B ↔ C)").rows).toEqual(["premise:A", "conclusion:B ↔ C"]);
    expect(cut(": A → ∀ x, B x ↔ C x").rows).toEqual(["premise:A", "premise:∀ x", "conclusion:B x ↔ C x"]);
    expect(iffAtLevel("B ↔ C")).toBe(true);
    expect(iffAtLevel("(B ↔ C)")).toBe(false);
    expect(iffAtLevel("∀ x, B x ↔ C x")).toBe(false);
  });
});
