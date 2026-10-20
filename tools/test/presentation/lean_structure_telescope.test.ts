// LeanSmith's own additions to the ported structurer (`src/presentation/lean_structure.ts`):
// a clause's lifted `∀ (…) […] (…),` telescope is cut like a signature's (`forallRows`); a premise
// with parts of its own, a filter quantifier, a case split, `letI`/`haveI` and a record's field are
// cut too — and the invariant a reader relies on: the rows of a view, in reading order, are the
// statement's source.
import { existsSync, readFileSync, readdirSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { declSource, leanStatementView, viewRows } from "../../src/formalization/nl_links.js";
import { scanPropositionSignature } from "../../src/presentation/lean_statement.js";
import { bareHead } from "../../src/presentation/lean_structure_tc.js";
import { assignRowIds, structureDefinitionView, structurePropRecordView, structureStatementView, type ConclusionCard, type HypRow } from "../../src/presentation/lean_structure.js";

const DENSE = `theorem dense (P : Pop) :
    (∀ {Ω X : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
        (W : World Ω X μ) (m : Bool → X → ℝ) (ρ δ : ℝ)
        (hτ : Integrable (fun w => W.Y true w - W.Y false w) μ)
        (hρ : 0 ≤ ρ ∧ ρ < 1) (n : ℕ),
      0 < n → Result W m ρ n) ∧
    (∀ k (i : Fin k), Small P k i) ∧
    (∀ c : ℝ, 0 < c → ∃ d : ℝ, c < d ∧ Big P d) := by
  sorry`;

/** What a cut removes between rows — layout, quantifier, separators, brackets — and nothing else. */
const bare = (t: string) => t.replace(/[\s∀,;→∧∨():]/g, "");
/** The statement's own text (binders and goal) and the view's rows in reading order, both `bare`. */
function roundTrip(source: string): { source: string; rows: string } | null {
  const scan = scanPropositionSignature(source), view = leanStatementView(source);
  if (!scan || !view) return null;
  // a head that is the name alone (`(h :` over its parts) is a label, not a row: where the rows
  // part from the source at such a name, the source goes on without it
  const labels: string[] = [];
  JSON.stringify(view, (k, v) => { if (k === "head" && typeof v === "string" && bareHead(v)) labels.push(bare(v)); return v; });
  const text = bare(scan.cleaned.slice(scan.telescopeStart, scan.conclusionEnd < 0 ? undefined : scan.conclusionEnd));
  const rows = bare(assignRowIds(view).map((r) => r.code).join(""));
  let kept = "";
  for (let i = 0; i < text.length; ) {
    const at = text[i] === rows[kept.length] ? -1 : labels.findIndex((l) => text.startsWith(l, i));
    if (at < 0) kept += text[i++];
    else i += labels.splice(at, 1)[0]!.length;
  }
  return { source: kept, rows };
}

describe("a clause's own telescope, cut like a signature's", () => {
  it("is one row per binder group: declarations, instances, and the hypotheses among them chipped as such", () => {
    const v = structureStatementView(DENSE)!;
    expect(v.sharedHyps).toEqual([{ chip: "decl", code: "(P : Pop)" }]);
    expect(v.conclusions[0].hyps).toEqual([
      { chip: "decl", code: "{Ω X : Type*}" },
      { chip: "decl", code: "[MeasurableSpace Ω]" },
      { chip: "decl", code: "{μ : Measure Ω}" },
      { chip: "decl", code: "[IsProbabilityMeasure μ]" },
      { chip: "decl", code: "(W : World Ω X μ)" },
      { chip: "decl", code: "(m : Bool → X → ℝ)" },
      { chip: "decl", code: "(ρ δ : ℝ)" },
      { chip: "hyp", code: "(hτ : Integrable (fun w => W.Y true w - W.Y false w) μ)" },
      { chip: "hyp", code: "(hρ : 0 ≤ ρ ∧ ρ < 1)" },
      { chip: "decl", code: "(n : ℕ)" },
      { chip: "hyp", code: "0 < n" },
    ]);
    expect(v.conclusions[0].code).toBe("Result W m ρ n");
    // a header that is not written as binder groups stays one row
    expect(v.conclusions[1].hyps).toEqual([{ chip: "decl", code: "∀ k (i : Fin k)" }]);
    expect(v.conclusions[2].hyps).toEqual([{ chip: "decl", code: "∀ c : ℝ" }, { chip: "hyp", code: "0 < c" }]);
  });
  it("gives each group its own id in reading order — the rows F5 links", () => {
    const rows = viewRows(leanStatementView(DENSE)!);
    expect(rows.map((r) => r.id)).toEqual(rows.map((_, k) => `r${k + 1}`));
    expect(rows.slice(0, 13).map((r) => `${r.kind}:${r.names}`)).toEqual([
      "binder:P", "binder:Ω X", "instance:", "binder:μ", "instance:", "binder:W", "binder:m", "binder:ρ δ", "binder:hτ", "binder:hρ", "binder:n", "premise:", "conclusion:",
    ]);
    expect(Math.max(...rows.map((r) => r.lean.length))).toBeLessThan(60);
  });
  it("cuts the goal's own telescope and a Prop definition's the same way", () => {
    const goal = structureStatementView("theorem t : ∀ (x : ℕ) (hx : 0 < x), P x ∧ Q x := by sorry")!;
    expect(goal.sharedHyps).toEqual([{ chip: "decl", code: "(x : ℕ)" }, { chip: "hyp", code: "(hx : 0 < x)" }]);
    const def = structureDefinitionView("def Fine (P : Pop) : Prop :=\n  ∀ {c : ℝ} [Fact (0 < c)] (hc : c < 1), Big P c")!;
    expect(def.sharedHyps.map((h) => `${h.chip} ${h.code}`)).toEqual(["decl (P : Pop)", "decl {c : ℝ}", "decl [Fact (0 < c)]", "hyp (hc : c < 1)"]);
    expect(def.conclusions.map((c) => c.code)).toEqual(["Big P c"]);
  });
  it("keeps a multi-line group whole with its line breaks, as a signature's", () => {
    const v = structureStatementView("theorem t :\n    (∀ (f : ℕ → ℝ)\n        (hf : ∀ n,\n          0 < f n),\n      Good f) ∧ True := by sorry")!;
    expect(v.conclusions[0].hyps.map((h) => h.code)).toEqual(["(f : ℕ → ℝ)", "(hf : ∀ n,\n0 < f n)"]);
  });
});

/** A view as an outline: one line per row, indented by nesting (`hyp:` a hypothesis row, `|` a
 *  premise's own clauses, `>` a line its parts share). */
function outline(v: { sharedHyps: HypRow[]; conclusions: ConclusionCard[] }): string[] {
  const out: string[] = [];
  const flat = (t: string) => t.replace(/\s+/g, " ");
  const hyp = (h: HypRow, d: number) => { if (h.sub) { out.push(`${"  ".repeat(d)}hyp |`); h.sub.forEach((s) => card(s, d + 1)); } else out.push(`${"  ".repeat(d)}hyp: ${flat(h.code)}`); };
  const card = (c: ConclusionCard, d: number) => {
    c.hyps.forEach((h) => hyp(h, d));
    if (c.intro !== undefined) out.push(`${"  ".repeat(d)}> ${flat(c.intro)}`);
    if (c.code !== undefined) out.push(`${"  ".repeat(d)}${flat(c.code)}`);
    (c.sub ?? []).forEach((s) => card(s, d + 1));
  };
  v.sharedHyps.forEach((h) => hyp(h, 0));
  v.conclusions.forEach((c) => card(c, 0));
  return out;
}

// The shapes the structurer used to leave as one row (each with the statement it is cut from).
const SHAPES: Array<[string, string, string[]]> = [
  ["a parenthesised premise that is a conjunction of implications", "theorem t (P : Law) : ((A P → B P) ∧ (C P → D P ∧ E P)) → F P := by sorry", [
    "hyp: (P : Law)", "hyp |", "  hyp: A P", "  B P", "  hyp: C P", "    D P", "    E P", "F P",
  ]],
  ["a premise that is a quantified claim", "theorem t : (∀ g ∈ S, P g ∧ Q g) → (∃ D : Sub, R D ∧ T D) → (0 < c) → U := by sorry", [
    "hyp |", "  hyp: ∀ g ∈ S", "    P g", "    Q g", "hyp |", "  > ∃ D : Sub,", "    R D", "    T D", "hyp: (0 < c)", "U",
  ]],
  ["a binder written as a premise stays one row", "theorem t : (h : A ∧ B) → C := by sorry", ["hyp: (h : A ∧ B)", "C"]],
  ["letI / haveI peeled as let", "theorem t (W : World) :\n    letI := lawInst W\n    haveI : Fact (0 < W.n) := W.pos\n    ∀ m ∈ W.models, Good m → Fine m := by sorry", [
    "hyp: (W : World)", "hyp: letI := lawInst W", "hyp: haveI : Fact (0 < W.n) := W.pos", "hyp: ∀ m ∈ W.models", "hyp: Good m", "Fine m",
  ]],
  ["a.e. and eventually quantifiers as a line over what they scope", "theorem t : (∀ᵐ o ∂μ, 0 < f o ∧ f o ≤ C) ∧ (∀ᶠ h in 𝓝[>] (0 : ℝ), κ h < ∞ ∧ ζ h < ∞) ∧ (∀ᵐ o ∂μ, 0 < d o → k o = g o) := by sorry", [
    "> ∀ᵐ o ∂μ,", "  0 < f o", "  f o ≤ C", "> ∀ᶠ h in 𝓝[>] (0 : ℝ),", "  κ h < ∞", "  ζ h < ∞", "> ∀ᵐ o ∂μ,", "  hyp: 0 < d o", "  k o = g o",
  ]],
  ["a run of quantifiers is one line; one quantifier over a plain claim stays whole", "theorem t : (∃ B : ℝ, ∀ᵐ w ∂μ, f w ≤ B) ∧ (∀ᵐ w ∂μ, f w ≤ 1) ∧ (∃ (a : T) (b : U), R a b ∧ S a b) := by sorry", [
    "> ∃ B : ℝ, ∀ᵐ w ∂μ,", "  f w ≤ B", "∀ᵐ w ∂μ, f w ≤ 1", "> ∃ (a : T) (b : U),", "  R a b", "  S a b",
  ]],
  ["if … then … else …", "theorem t (n : ℕ) : if n = 0 then True else (0 < n ∧ n < 5 ∧ ∀ m, m < n → m < 5) := by sorry", [
    "hyp: (n : ℕ)", "  > if n = 0 then", "    True", "  > else", "    0 < n", "    n < 5", "    hyp: ∀ m", "    hyp: m < n", "    m < 5",
  ]],
  ["else if", "theorem t : if a then A else if b then B ∧ B' else C := by sorry", ["  > if a then", "    A", "  > else", "    > if b then", "      B", "      B'", "    > else", "      C"]],
  ["match … with", "theorem t (kind : Kind) :\n    match kind with\n    | .cate => Overlap P\n    | .rdd => (∃ h : ℝ, Fixed h ∧ Setup h) ∧ ∀ h : ℝ, Cont h → Bound h\n    | _ => True := by sorry", [
    "hyp: (kind : Kind)", "> match kind with", "  > | .cate =>", "    Overlap P", "  > | .rdd =>", "    > ∃ h : ℝ,", "      Fixed h", "      Setup h", "    hyp: ∀ h : ℝ", "    hyp: Cont h", "    Bound h", "  > | _ =>", "    True",
  ]],
  ["a match inside an alternative takes the alternatives after it", "theorem t : match a with | none => True | some s => match s with | none => True | some _ => ∀ t : Bool, I t ∧ J t := by sorry", [
    "> match a with", "  > | none =>", "    True", "  > | some s =>", "    > match s with", "      > | none =>", "        True", "      > | some _ =>", "        hyp: ∀ t : Bool", "          I t", "          J t",
  ]],
];

describe("shapes cut beyond CausalSmith's structurer", () => {
  for (const [name, src, want] of SHAPES) it(name, () => { expect(outline(structureStatementView(src)!)).toEqual(want); });

  it("rows of a premise's own clauses take ids in reading order; the premise itself is no row", () => {
    const view = leanStatementView(SHAPES[0][1])!;
    expect(viewRows(view).map((r) => `${r.id} ${r.kind} ${r.lean}`)).toEqual([
      // a premise's own rows are a hypothesis's: premises, what they conclude included
      "r1 binder Law", "r2 premise A P", "r3 premise B P", "r4 premise C P", "r5 premise D P", "r6 premise E P", "r7 conclusion F P",
    ]);
    expect(view.sharedHyps[1]).toMatchObject({ code: "((A P → B P) ∧ (C P → D P ∧ E P))" });
    expect(view.sharedHyps[1].id).toBeUndefined();
  });
  it("leaves alone what it does not read with confidence", () => {
    // absolute-value bars in a match alternative, an `if` with no `else`, a header that opens a binder of its own
    for (const src of [
      "theorem t : match x with | a => |f a| ≤ 1 ∧ B | b => C := by sorry",
      "theorem t : ∃ hn : ∀ t, 0 ≤ f t, A hn ∧ B hn := by sorry",
    ]) {
      const v = structureStatementView(src)!;
      expect(v.conclusions, src).toHaveLength(1);
      expect(v.conclusions[0].sub, src).toBeUndefined();
    }
  });
  it("a Prop record: its parameters are the binder groups as written, a field with parts is cut under its name", () => {
    const v = structurePropRecordView("structure Foo (α : Type) [Fintype α] ⦃x : α⦄ {y : α} (h : 0 < 1) : Prop where\n  pos : ∀ z : α, z = x → z = y\n  two : 0 < 1 ∧ 1 < 2\n  plain : x = y")!;
    expect(v.sharedHyps.map((h) => `${h.chip} ${h.code}`)).toEqual(["decl (α : Type)", "decl [Fintype α]", "decl ⦃x : α⦄", "decl {y : α}", "hyp (h : 0 < 1)"]);
    expect(outline({ sharedHyps: [], conclusions: v.conclusions })).toEqual([
      "> pos :", "  hyp: ∀ z : α", "  hyp: z = x", "  z = y", "> two :", "  0 < 1", "  1 < 2", "plain : x = y",
    ]);
    // the rows are the source, the comma after a field's `∀` header included
    const one = structurePropRecordView("structure V (M : Model) : Prop where\n  unc : ∀ n (i j : Fin n), i ≠ j → ∀ᵐ d ∂(M.P.map (M.design n)), (∫ y : Fin n → ℝ, (y i - M.mean n i d) * (y j - M.mean n j d) ∂(M.law n d)) = 0")!;
    const text = assignRowIds(one).map((r) => r.code).join("");
    expect(bare(text)).toBe(bare("(M : Model) unc : ∀ n (i j : Fin n), i ≠ j → ∀ᵐ d ∂(M.P.map (M.design n)), (∫ y : Fin n → ℝ, (y i - M.mean n i d) * (y j - M.mean n j d) ∂(M.law n d)) = 0"));
    expect(text).toContain("∀ n (i j : Fin n)");
  });
});

describe("the rows of a view, in reading order, are the statement's source", () => {
  it("holds for telescopes, lets, ∃ introductions and nested conjunctions", () => {
    const sources = [
      DENSE,
      "theorem t (n : ℕ) [Fact (0 < n)] (hn : 0 < n) : A n ∧ (∀ k : ℕ, k ≤ n → B n k) ∧ C n := by sorry",
      "theorem t : ∀ {α : Type*} [Fintype α] (s : Finset α) (hs : s.Nonempty), 0 < s.card ∧ s.card ≤ Fintype.card α := by sorry",
      "theorem t (P : Pop) :\n    let A := norm P\n    let B := cov P\n    (A ≤ B ∧ (B = 0 → A = 0)) ∧ (∀ (c : ℝ) (hc : 0 < c), ∃ d e : ℝ, c < d ∧ d < e) := by sorry",
      "theorem t : (type_of% @left) ∧ (type_of% @right) := by sorry",
      "lemma l : ∃ f : ℕ → ℕ, f 0 = 0 ∧ f 1 = 1 := by sorry",
      ...SHAPES.map(([, src]) => src),
    ];
    for (const src of sources) {
      const rt = roundTrip(src);
      expect(rt, src).not.toBeNull();
      expect(rt!.rows, src).toBe(rt!.source);
    }
  });

  // Every linked statement of the toolkit's runs, when LEANSMITH_TEST_TOOLKIT names one (the real
  // statements are the toolkit's own, not fixtures of this repository).
  const toolkit = process.env.LEANSMITH_TEST_TOOLKIT ?? "";
  const runs = toolkit && existsSync(path.join(toolkit, "runs")) ? readdirSync(path.join(toolkit, "runs")).filter((slug) => existsSync(path.join(toolkit, "runs", slug, "nl_links.json"))) : [];
  it.skipIf(runs.length === 0)("holds for every linked statement of the toolkit's runs", () => {
    const json = (file: string) => { try { return JSON.parse(readFileSync(file, "utf8")); } catch { return null; } };
    let checked = 0;
    for (const slug of runs) {
      const dir = path.join(toolkit, "runs", slug);
      const leanDir = json(path.join(dir, "state.json"))?.lean_subdir;
      const linked = new Set<string>((json(path.join(dir, "nl_links.json"))?.results ?? []).map((r: { node: string }) => r.node));
      for (const rep of (json(path.join(dir, "report.json"))?.results ?? []) as Array<{ node_id: string; lean?: { file: string; decl: string } }>) {
        const file = rep.lean && leanDir ? path.join(toolkit, leanDir, rep.lean.file) : null;
        if (!file || !linked.has(rep.node_id) || !existsSync(file)) continue;
        const src = declSource(readFileSync(file, "utf8"), rep.lean!.decl);
        const rt = src ? roundTrip(src) : null;
        if (!rt) continue; // a statement the view does not structure is shown as flat rows
        expect(rt.rows, `${slug} ${rep.node_id}`).toBe(rt.source);
        checked++;
      }
    }
    expect(checked).toBeGreaterThan(0);
  });
});
