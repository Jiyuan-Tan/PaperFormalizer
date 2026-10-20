// PORTED from CausalSmith: the `structureStatementView` suite of `site/test/paperLean.test.ts` and
// the "Lean rows (ported structurer)" suite of `tools/test/presentation_nl_links.test.ts` (the
// tests that need its site bundle or its P4 block inputs are not here). They pin the port of
// `src/presentation/lean_structure.ts`: re-copy them with it.
import { describe, expect, it } from "vitest";
import {
  assignRowIds,
  structureDefinitionView,
  structurePropRecordView,
  structureStatementView,
  type ConclusionCard,
} from "../../src/presentation/lean_structure.js";

const THEOREM = [
  "theorem overlap_bound",
  "    (eps : ℝ)",
  "    (h1 : 0 < eps)",
  "    (h2 : eps ≤ 1) :",
  "    eps ≤ 1 - eps",
].join("\n");

describe("structureStatementView", () => {
  it("splits a top-level conjunction and lifts each conjunct's own telescope", () => {
    const v = structureStatementView(
      `theorem thm (n : ℕ) (hn : 0 < n) :
    Computable ∧
    (∀ eps : ℝ, 0 < eps → eps < 1 / 2 →
      risk n eps ≤ eps) ∧
    (∀ d : ℕ, 0 < d → rate n d ≤ 1) := by
  sorry`,
    )!;
    expect(v).not.toBeNull();
    expect(v.sharedHyps).toEqual([
      { chip: "decl", code: "(n : ℕ)" },
      { chip: "hyp", code: "(hn : 0 < n)" },
    ]);
    expect(v.conclusions).toHaveLength(3);
    expect(v.conclusions[0]).toEqual({ hyps: [], code: "Computable" });
    expect(v.conclusions[1].hyps).toEqual([
      { chip: "decl", code: "∀ eps : ℝ" },
      { chip: "hyp", code: "0 < eps" },
      { chip: "hyp", code: "eps < 1 / 2" },
    ]);
    expect(v.conclusions[1].code).toBe("risk n eps ≤ eps");
    expect(v.conclusions[2].hyps.map((h) => h.code)).toEqual(["∀ d : ℕ", "0 < d"]);
    expect(v.conclusions[2].code).toBe("rate n d ≤ 1");
  });

  it("lifts a goal-level ∀/→ prefix into the shared hypotheses", () => {
    const v = structureStatementView("theorem thm : ∀ n : ℕ, 0 < n → P n ∧ Q n := by sorry")!;
    expect(v.sharedHyps).toEqual([
      { chip: "decl", code: "∀ n : ℕ" },
      { chip: "hyp", code: "0 < n" },
    ]);
    expect(v.conclusions.map((c) => c.code)).toEqual(["P n", "Q n"]);
  });

  // `∧` binds tighter than `→`, so `A → B ∧ C` is `A → (B ∧ C)`. Splitting the
  // ∧ before lifting the arrow would silently restate the theorem.
  it("respects ∧/→ precedence instead of splitting across an implication", () => {
    const v = structureStatementView("theorem thm : A → B ∧ C := by sorry")!;
    expect(v.sharedHyps).toEqual([{ chip: "hyp", code: "A" }]);
    expect(v.conclusions.map((c) => c.code)).toEqual(["B", "C"]);
  });

  it("does not split ∧ underneath a looser connective: `A ∨ B ∧ C` is either A or (B and C)", () => {
    const v = structureStatementView("theorem thm : A ∨ B ∧ C := by sorry")!;
    expect(v.conclusions).toHaveLength(1);
    const [either, or] = v.conclusions[0].sub!;
    expect([either.alt, either.code]).toEqual(["either", "A"]);
    expect([or.alt, or.sub!.map((c) => c.code)]).toEqual(["or", ["B", "C"]]);
    // a plain disjunction, no alternative with parts, is one leaf; so is one under `→`
    expect(structureStatementView("theorem thm : A ∨ B := by sorry")!.conclusions[0].code).toBe("A ∨ B");
    expect(structureStatementView("theorem thm : A ∨ B ∧ C → D := by sorry")!.sharedHyps.map((h) => h.code)).toEqual(["A ∨ B ∧ C"]);
  });

  // A depth-0 `→` inside `∃ f : α → β, …` is the arrow of f's TYPE. Reading it
  // as an implication would invent the hypothesis `∃ f : α`.
  it("never mistakes a binder's function-type arrow for an implication", () => {
    const v = structureStatementView("theorem thm : ∃ f : ℕ → ℕ, f 0 = 0 := by sorry")!;
    expect(v.sharedHyps).toEqual([]);
    expect(v.conclusions).toEqual([{ hyps: [], code: "∃ f : ℕ → ℕ, f 0 = 0" }]);
  });

  it("hoists a leading ∃ run and splits what it scopes", () => {
    const v = structureStatementView("theorem thm : ∃ C N : ℝ, ∃ K : ℕ, 0 < C ∧ 0 < N ∧ P K := by sorry")!;
    const card = v.conclusions[0];
    expect(v.conclusions).toHaveLength(1);
    expect(card.intro).toBe("∃ C N : ℝ, ∃ K : ℕ,");
    expect(card.code).toBeUndefined();
    expect(card.sub!.map((s) => s.code)).toEqual(["0 < C", "0 < N", "P K"]);
  });

  it("structures the body of an explicit Prop-valued definition", () => {
    const v = structureStatementView(`def VCLocalizedEnvelope
      (P : Law) (policySet : Set Policy) (α : ℝ) : Prop :=
      ∃ C p : ℝ, 0 < C ∧ 0 ≤ p ∧
        ∀ m : ℕ, 0 < m → EnvelopeBound P policySet α C p m`)!;
    expect(v.sharedHyps.map((h) => h.code)).toEqual([
      "(P : Law)",
      "(policySet : Set Policy)",
      "(α : ℝ)",
    ]);
    expect(v.conclusions[0].intro).toBe("∃ C p : ℝ,");
    expect(v.conclusions[0].sub?.map((c) => c.code)).toEqual([
      "0 < C",
      "0 ≤ p",
      "EnvelopeBound P policySet α C p m",
    ]);
    expect(v.conclusions[0].sub?.[2].hyps.map((h) => h.code)).toEqual(["∀ m : ℕ", "0 < m"]);
  });

  it("structures a Prop-valued record into parameters and defining clauses", () => {
    const v = structurePropRecordView(`structure ExperimentClass (n : ℕ) {d : ℕ} (epsilon : ℝ)
      (P : Law d) (mu_n : Measure (Fin n → Obs d)) : Prop where
      epsilon_pos : 0 < epsilon
      epsilon_le_half : epsilon ≤ 1 / 2
      product_law : IidSampling P mu_n
      overlap : Overlap epsilon P`)!;
    expect(v.sharedHyps.map((h) => h.code)).toEqual([
      "(n : ℕ)",
      "{d : ℕ}",
      "(epsilon : ℝ)",
      "(P : Law d)",
      "(mu_n : Measure (Fin n → Obs d))",
    ]);
    expect(v.conclusions.map((c) => c.code)).toEqual([
      "epsilon_pos : 0 < epsilon",
      "epsilon_le_half : epsilon ≤ 1 / 2",
      "product_law : IidSampling P mu_n",
      "overlap : Overlap epsilon P",
    ]);
    expect(structurePropRecordView("structure Ordinary where value : Nat")).toBeNull();
  });

  // An ∃ that reveals nothing is left where the author wrote it: an `intro` row
  // over a single leaf would be scaffolding, not structure.
  it("keeps an ∃ inline when its body does not split", () => {
    const v = structureStatementView("theorem thm : ∃ n : ℕ, 0 < n := by sorry")!;
    expect(v.conclusions).toEqual([{ hyps: [], code: "∃ n : ℕ, 0 < n" }]);
  });

  it("splits a conjunction whose last conjunct is an unparenthesised ∀", () => {
    // `∀` extends to the end of the clause, so this is three conjuncts and the
    // `→` inside the last one is not the top level's.
    const v = structureStatementView("theorem thm : 0 < C ∧ 0 < r ∧ ∀ n : ℕ, 0 < n → P n := by sorry")!;
    expect(v.conclusions.map((c) => c.code)).toEqual(["0 < C", "0 < r", "P n"]);
    expect(v.conclusions[2].hyps.map((h) => h.code)).toEqual(["∀ n : ℕ", "0 < n"]);
  });

  it("nests to the deeper readability cap and then stops", () => {
    // Eight nested levels of `∀ xᵢ, … ∧ …`; the card at the cap keeps whatever
    // is left of its clause verbatim instead of recursing without a bound.
    const at = (i: number, body: string) => `∀ x${i} : ℕ, ${body}`;
    const src = `theorem thm : ${at(1, `A ∧ ${at(2, `B ∧ ${at(3, `C ∧ ${at(4, `D ∧ ${at(5, `E ∧ ${at(6, `F ∧ ${at(7, `G ∧ ${at(8, "H ∧ I")}`)}`)}`)}`)}`)}`)}`)} := by sorry`;
    const v = structureStatementView(src)!;
    const depthOf = (c: ConclusionCard): number => (c.sub ? 1 + Math.max(...c.sub.map(depthOf)) : 0);
    expect(Math.max(...v.conclusions.map(depthOf))).toBe(6);
    const deepest = (c: ConclusionCard): ConclusionCard => (c.sub ? deepest(c.sub[c.sub.length - 1]) : c);
    const leaf = deepest(v.conclusions[v.conclusions.length - 1]);
    expect(leaf.hyps.map((h) => h.code)).toEqual(["∀ x8 : ℕ"]);
    expect(leaf.code).toBe("H ∧ I"); // un-split at the cap, but nothing lost
  });

  it("turns conclusion-local lets into declaration rows and splits their body", () => {
    const v = structureStatementView(`theorem sharp_sign (x : ℝ) :
      let W := x + 1
      let denominator := W ^ 2 + 1
      let derivative := W / denominator
      HasDerivAt (fun y => y) derivative x ∧
      0 < denominator ∧
      (derivative < 0 ↔ W < 0) := by sorry`)!;
    const card = v.conclusions[0];
    expect(card.hyps.map((h) => [h.chip, h.code])).toEqual([
      ["decl", "let W := x + 1"],
      ["decl", "let denominator := W ^ 2 + 1"],
      ["decl", "let derivative := W / denominator"],
    ]);
    expect(card.sub?.map((c) => c.code)).toEqual([
      "HasDerivAt (fun y => y) derivative x",
      "0 < denominator",
      "derivative < 0 ↔ W < 0",
    ]);
  });

  it("peels semicolon lets before splitting their scoped conjunction", () => {
    const v = structureStatementView(`theorem recovery (x : ℝ) :
      (let f := x + 1;
       let Q := f ^ 2;
       Q ≠ 0 ∧ P Q ∧ R Q) := by sorry`)!;
    expect(v.conclusions).toHaveLength(1);
    expect(v.conclusions[0].hyps.map((h) => h.code)).toEqual([
      "let f := x + 1",
      "let Q := f ^ 2",
    ]);
    expect(v.conclusions[0].sub?.map((c) => c.code)).toEqual(["Q ≠ 0", "P Q", "R Q"]);
  });

  it("keeps splitting when lets and governed telescopes alternate", () => {
    const v = structureStatementView(`theorem layered :
      ∃ c : ℝ, 0 < c ∧
      let B := c + 1
      ∀ L : ℝ, B ≤ L →
        let C := L + 1
        0 < C ∧ P C ∧ Q C := by sorry`)!;
    const scoped = v.conclusions[0].sub?.[1];
    expect(scoped?.hyps.map((h) => h.code)).toEqual([
      "let B := c + 1",
      "∀ L : ℝ",
      "B ≤ L",
      "let C := L + 1",
    ]);
    expect(scoped?.sub?.map((c) => c.code)).toEqual(["0 < C", "P C", "Q C"]);
  });

  it("splits conjunctions after a big-operator binder comma", () => {
    const v = structureStatementView(`theorem overlap :
      ∀ M : Model, ∀ r : ℕ, 1 ≤ r →
        (∑ i, overlap M i r) = total M r ∧
        total M r ≤ bound M r ∧
        bound M r ≤ sharp M r := by sorry`)!;
    expect(v.sharedHyps.map((h) => h.code)).toEqual(["∀ M : Model", "∀ r : ℕ", "1 ≤ r"]);
    expect(v.conclusions.map((c) => c.code)).toEqual([
      "(∑ i, overlap M i r) = total M r",
      "total M r ≤ bound M r",
      "bound M r ≤ sharp M r",
    ]);
  });

  it("gives every card exactly one of code | sub", () => {
    const v = structureStatementView("theorem thm : A ∧ (∀ n : ℕ, 0 < n → B n ∧ C n) ∧ D := by sorry")!;
    const check = (c: ConclusionCard) => {
      expect(Number(c.code !== undefined) + Number(c.sub !== undefined)).toBe(1);
      (c.sub ?? []).forEach(check);
    };
    v.conclusions.forEach(check);
  });

  it("gives a non-conjunction goal a single card", () => {
    const v = structureStatementView("theorem thm (a : ℕ) : a ≤ a + 1 := by omega")!;
    expect(v.conclusions).toEqual([{ hyps: [], code: "a ≤ a + 1" }]);
  });

  it("omits the view rather than emitting an unparseable binder", () => {
    expect(structureStatementView("theorem thm () : True := trivial")).toBeNull();
    expect(structureStatementView("def notATheorem : ℕ := 0")).toBeNull();
    expect(structureStatementView("theorem thm (a : ℕ)")).toBeNull(); // no conclusion
  });

  // The load-bearing invariant: whatever is rendered must reproduce the source.
  it("never drops content — every emitted view rebuilds its source verbatim", () => {
    const sources = [
      "theorem thm (n : ℕ) (hn : 0 < n) : A n ∧ (∀ k : ℕ, k ≤ n → B n k) ∧ C n := by sorry",
      "theorem thm : ∀ n : ℕ, 0 < n → P n ∧ Q n := by sorry",
      "theorem thm : A → B ∧ C := by sorry",
      "theorem thm {α : Type*} [Fintype α] (s : Finset α) : s.card ≤ Fintype.card α := by sorry",
      "lemma lem : ∃ f : ℕ → ℕ, f 0 = 0 ∧ f 1 = 1 := by sorry",
    ];
    const squash = (s: string) => s.replace(/\s+/g, "");
    const renderCard = (c: ConclusionCard): string =>
      c.hyps.map((h) => h.code).join("") +
      (c.intro ?? "") +
      (c.code ?? "") +
      (c.sub ?? []).map(renderCard).join("");
    for (const src of sources) {
      const v = structureStatementView(src)!;
      expect(v, src).not.toBeNull();
      const rendered = squash(
        v.sharedHyps.map((h) => h.code).join("") + v.conclusions.map(renderCard).join(""),
      );
      // Everything after the declaration's own name and before the proof: the
      // binder telescope plus the goal, which is exactly what the view renders.
      const signature = squash(
        src.slice(0, src.search(/\s:=/)).replace(/^\s*(theorem|lemma)\s+\S+/, ""),
      );
      // Every identifier-bearing character of the signature must survive into
      // the view (only the ∀/→/∧/paren scaffolding is allowed to be dropped).
      for (const tok of signature.match(/[A-Za-z_][A-Za-z0-9_.']*/g) ?? []) {
        expect(rendered, `${src} lost ${tok}`).toContain(tok);
      }
    }
  });

});

describe("Lean rows (ported structurer)", () => {
  it("gives every hypothesis and conclusion a stable id in reading order", () => {
    const view = structureStatementView(THEOREM);
    expect(view).not.toBeNull();
    const rows = assignRowIds(view!);
    expect(rows.map((r) => r.id)).toEqual(rows.map((_, i) => `r${i + 1}`));
    expect(rows.filter((r) => r.kind === "hyp").length).toBeGreaterThan(0);
    expect(rows.some((r) => r.kind === "conclusion")).toBe(true);
    // ids land on the tree the site renders, not only on the flat list
    expect(view!.sharedHyps.every((h) => typeof h.id === "string")).toBe(true);
    expect(view!.conclusions.every((c) => typeof c.id === "string")).toBe(true);
  });

  it("gives no id to a purely branching card, so no empty row is invented", () => {
    // a conjunction that splits with no ∃ prefix: the parent card carries `sub`
    // only, and has no content row for the renderer to draw.
    const thm = [
      "theorem both",
      "    (h : True) :",
      "    (1 = 1 ∧ 2 = 2) ∧ 3 = 3",
    ].join("\n");
    const view = structureStatementView(thm);
    expect(view).not.toBeNull();
    const rows = assignRowIds(view!);
    expect(rows.every((r) => r.code.trim().length > 0)).toBe(true);
    const branching = (card: { intro?: string; code?: string; sub?: unknown[]; id?: string }): number =>
      (card.sub && card.intro === undefined && card.code === undefined ? 1 : 0) +
      ((card.sub ?? []) as typeof card[]).reduce((n, c) => n + branching(c), 0);
    const branchingCards = view!.conclusions.reduce((n, c) => n + branching(c), 0);
    if (branchingCards > 0) {
      // every branching card stayed id-less, so it produced no row
      const idsOnBranching = (card: { intro?: string; code?: string; sub?: unknown[]; id?: string }): number =>
        (card.sub && card.intro === undefined && card.code === undefined && card.id !== undefined ? 1 : 0) +
        ((card.sub ?? []) as typeof card[]).reduce((n, c) => n + idsOnBranching(c), 0);
      expect(view!.conclusions.reduce((n, c) => n + idsOnBranching(c), 0)).toBe(0);
    }
    // ids remain a dense reading-order sequence over the rows that DO exist
    expect(rows.map((r) => r.id)).toEqual(rows.map((_, i) => `r${i + 1}`));
  });

  it("lifts conclusion-local lets and exposes the conjunction beneath them", () => {
    const thm = `theorem sharp_sign (x : ℝ) :
      let W := x + 1
      let denominator := W ^ 2 + 1
      let derivative := W / denominator
      HasDerivAt (fun y => y) derivative x ∧
      0 < denominator ∧
      (derivative < 0 ↔ W < 0) := by
    sorry`;
    const view = structureStatementView(thm)!;
    expect(view).not.toBeNull();
    expect(view.conclusions).toHaveLength(1);
    expect(view.conclusions[0].hyps.map((h) => h.code)).toEqual([
      "let W := x + 1",
      "let denominator := W ^ 2 + 1",
      "let derivative := W / denominator",
    ]);
    expect(view.conclusions[0].sub?.map((c) => c.code)).toEqual([
      "HasDerivAt (fun y => y) derivative x",
      "0 < denominator",
      "derivative < 0 ↔ W < 0",
    ]);
    expect(assignRowIds(view).map((r) => r.code)).toEqual([
      "(x : ℝ)",
      "let W := x + 1",
      "let denominator := W ^ 2 + 1",
      "let derivative := W / denominator",
      "HasDerivAt (fun y => y) derivative x",
      "0 < denominator",
      "derivative < 0 ↔ W < 0",
    ]);
  });

  it("peels semicolon lets before splitting their scoped conjunction", () => {
    const view = structureStatementView(`theorem recovery (x : ℝ) :
      (let f := x + 1;
       let Q := f ^ 2;
       Q ≠ 0 ∧ P Q ∧ R Q) := by sorry`)!;
    expect(view.conclusions).toHaveLength(1);
    expect(view.conclusions[0].hyps.map((h) => h.code)).toEqual([
      "let f := x + 1",
      "let Q := f ^ 2",
    ]);
    expect(view.conclusions[0].sub?.map((c) => c.code)).toEqual(["Q ≠ 0", "P Q", "R Q"]);
  });

  it("keeps splitting when lets and governed telescopes alternate", () => {
    const view = structureStatementView(`theorem layered :
      ∃ c : ℝ, 0 < c ∧
      let B := c + 1
      ∀ L : ℝ, B ≤ L →
        let C := L + 1
        0 < C ∧ P C ∧ Q C := by sorry`)!;
    const scoped = view.conclusions[0].sub?.[1];
    expect(scoped?.hyps.map((h) => h.code)).toEqual([
      "let B := c + 1",
      "∀ L : ℝ",
      "B ≤ L",
      "let C := L + 1",
    ]);
    expect(scoped?.sub?.map((c) => c.code)).toEqual(["0 < C", "P C", "Q C"]);
  });

  it("keeps splitting below the former three-level Snipe cutoff", () => {
    const thm = `theorem frontier :
      ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, 0 < n →
        Main n ∧
        (∀ M : Model, ∀ r : ℕ, 1 ≤ r → Identity M r ∧ Bound M r ∧ Sharp M r) := by
    sorry`;
    const view = structureStatementView(thm)!;
    const quantified = view.conclusions[0].sub?.[1].sub?.[1];
    expect(quantified?.hyps.map((h) => h.code)).toEqual(["∀ M : Model", "∀ r : ℕ", "1 ≤ r"]);
    expect(quantified?.sub?.map((c) => c.code)).toEqual(["Identity M r", "Bound M r", "Sharp M r"]);
  });

  it("does not mistake a big-operator binder comma for connective scope", () => {
    const view = structureStatementView(`theorem overlap :
      ∀ M : Model, ∀ r : ℕ, 1 ≤ r →
        (∑ i, overlap M i r) = total M r ∧
        total M r ≤ bound M r ∧
        bound M r ≤ sharp M r := by sorry`)!;
    expect(view.sharedHyps.map((h) => h.code)).toEqual(["∀ M : Model", "∀ r : ℕ", "1 ≤ r"]);
    expect(view.conclusions.map((c) => c.code)).toEqual([
      "(∑ i, overlap M i r) = total M r",
      "total M r ≤ bound M r",
      "bound M r ≤ sharp M r",
    ]);
  });

});

// Not in CausalSmith's suites: the definition view the paper page opens under a row.
describe("structureDefinitionView (a Prop-valued definition)", () => {
  it("is parameters, a def row, and the proposition split as a goal is", () => {
    const v = structureDefinitionView(`def Bounded (P : Law) (c C : ℝ) : Prop :=
  0 < c ∧ (∀ n : ℕ, 0 < n → c ≤ rate P n) ∧ rate P 0 ≤ C`)!;
    expect(v.sharedHyps.map((h) => h.code)).toEqual(["(P : Law)", "(c C : ℝ)"]);
    expect(v.defRow).toEqual({ hyps: [], code: "Bounded P c C : Prop" });
    expect(v.conclusions.map((c) => c.code)).toEqual(["0 < c", "c ≤ rate P n", "rate P 0 ≤ C"]);
    expect(v.conclusions[1].hyps.map((h) => h.code)).toEqual(["∀ n : ℕ", "0 < n"]);
    // a def row takes its id between the parameters and the clauses
    expect(assignRowIds(v).map((r) => r.kind)).toEqual(["param", "param", "def", "value", "param", "param", "value", "value"]);
  });
});
