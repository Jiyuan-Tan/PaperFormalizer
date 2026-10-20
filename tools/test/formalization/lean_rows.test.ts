// The binders a theorem takes from its section's `variable`s (`lean_rows.ts` `sectionScope`,
// `usedSectionVars`, `withSectionVariables`): which are in force where it stands, which it takes as
// Lean decides from the source, and the rows they become — the variable groups' own text, in order,
// before the statement's. The finding these guard: 40 of 63 drawers used names (a probability
// measure and its instance) that no row declared.
import { describe, expect, it } from "vitest";
import { declSource, flatLeanRows } from "../../src/formalization/nl_links.js";
import { forallHeaderChip, freeNames, leanStatementView, sectionScope, usedSectionVars, viewRows, withSectionVariables } from "../../src/formalization/lean_rows.js";
import { squash } from "../../src/presentation/lean_text.js";

/** The view of the theorem `name` of `text` with its section variables, as rows `id kind text`. */
function rowsOf(text: string, name: string): { rows: string[]; key: string } {
  const line = text.split("\n").findIndex((l) => new RegExp(`^(?:theorem|lemma) ${name}(?![\\w'])`).test(l)) + 1;
  const v = leanStatementView(declSource(text, name, line)!)!;
  withSectionVariables(v, text, line);
  return { rows: viewRows(v).map((r) => `${r.id}${r.section ? " §" : ""} ${r.kind === "binder" ? `${r.names} : ${r.lean}` : r.kind === "instance" ? `[${r.lean}]` : r.lean}`), key: v.key };
}

const FILE = [
  "namespace Papers.X",
  "",
  "variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) -- the law",
  "  [IsProbabilityMeasure ν] (unused : ℕ)",
  "variable (a b : ℝ) (P : Law)",
  "",
  "section Inner",
  "variable (hP : Good P)",
  "include hP",
  "",
  "theorem uses_nu (x : ℕ) (hx : 0 < x) : D x ν a := by",
  "  sorry",
  "",
  "end Inner",
  "",
  "variable {P} in",
  "theorem after (x : ℕ) : E P ∧ ∀ a, F a := by",
  "  sorry",
  "",
  "omit [IsProbabilityMeasure ν] in",
  "theorem bare : G ν := by",
  "  sorry",
  "",
  "theorem again : G ν := by",
  "  sorry",
  "",
  "end Papers.X",
  "",
].join("\n");

describe("the section's variables a statement takes", () => {
  it("takes the variables it names, those their types name, an instance on them, and the `include`d", () => {
    expect(rowsOf(FILE, "uses_nu").rows).toEqual([
      "v1 § Ω : Type*", "v2 § [MeasurableSpace Ω]", "v3 § ν : Measure Ω", "v4 § [IsProbabilityMeasure ν]",
      // of `(a b : ℝ)` only the name used; `hP` is included, and so the `P` its type names
      "v5 § a : ℝ", "v6 § P : Law", "v7 § hP : Good P",
      "r1 x : ℕ", "r2 hx : 0 < x", "r3 D x ν a",
    ]);
  });
  it("respects `section … end`, `variable … in` (re-bracketing a variable), `omit … in`, and a name the statement binds itself", () => {
    // out of `Inner`: no `hP`; `{P}` for this one theorem; `∀ a` binds its own `a`
    expect(rowsOf(FILE, "after").rows).toEqual(["v1 § P : Law", "r1 x : ℕ", "r2 E P", "r3 ∀ a", "r4 F a"]);
    expect(viewRows(withVars(FILE, "after")).find((r) => r.id === "v1")).toMatchObject({ kind: "binder", section: true });
    expect(sectionScope(FILE, FILE.split("\n").indexOf("theorem after (x : ℕ) : E P ∧ ∀ a, F a := by") + 1).vars.find((v) => v.names.includes("P"))!.raw).toBe("{P : Law}");
    expect(rowsOf(FILE, "bare").rows).toEqual(["v1 § Ω : Type*", "v2 § [MeasurableSpace Ω]", "v3 § ν : Measure Ω", "r1 G ν"]);
    // `omit … in` and `variable … in` held for one declaration only
    expect(rowsOf(FILE, "again").rows).toEqual(["v1 § Ω : Type*", "v2 § [MeasurableSpace Ω]", "v3 § ν : Measure Ω", "v4 § [IsProbabilityMeasure ν]", "r1 G ν"]);
    expect(sectionScope(FILE, FILE.split("\n").indexOf("theorem again : G ν := by") + 1).vars.find((v) => v.names.includes("P"))!.raw).toBe("(P : Law)");
    // past the namespace's `end`, none is in force
    expect(sectionScope(FILE, FILE.split("\n").length).vars).toEqual([]);
  });
  it("round trip: the section rows are the variable groups' own text (comments dropped), then the statement's rows", () => {
    const line = FILE.split("\n").indexOf("theorem uses_nu (x : ℕ) (hx : 0 < x) : D x ν a := by") + 1;
    const used = usedSectionVars(sectionScope(FILE, line), freeNames("(x : ℕ) (hx : 0 < x) : D x ν a"));
    const v = withVars(FILE, "uses_nu");
    const section = v.sharedHyps.filter((h) => h.section).map((h) => h.code);
    expect(section).toEqual(used.map((u) => u.raw));
    // every full group is written in the file as it stands in its row; a group cut to its used names keeps their order and type
    const src = squash(FILE.replace(/--[^\n]*/g, ""));
    for (const raw of section.filter((r) => r !== "(a : ℝ)")) expect(src.includes(squash(raw)), raw).toBe(true);
    expect(section).toContain("(a : ℝ)");
    const own = leanStatementView(declSource(FILE, "uses_nu", line)!)!;
    expect(viewRows(v).filter((r) => !r.section).map((r) => r.lean)).toEqual(viewRows(own).map((r) => r.lean));
  });
  it("the key takes the variables in: a variable's type changed is another statement; a theorem renamed is the same", () => {
    const before = rowsOf(FILE, "uses_nu").key;
    expect(rowsOf(FILE.replace("(ν : Measure Ω)", "(ν : FiniteMeasure Ω)"), "uses_nu").key).not.toBe(before);
    expect(rowsOf(FILE.replace("theorem uses_nu", "theorem uses_nu'"), "uses_nu'").key).toBe(before);
    expect(rowsOf(FILE.replace("(unused : ℕ)", "(unused : ℤ)"), "uses_nu").key).toBe(before);
  });
});

describe("a section variable the statement also binds", () => {
  const file = (ty: string, goal: string) => `variable (x : ${ty}) (y : ℕ)\n\ntheorem t : ${goal} := by\n  sorry\n`;
  // The finding: a name bound by one inner `∀` was dropped as a row everywhere, and its type left out of the key.
  it("is a row, and part of the key, when the statement uses it outside that binder; not when it is only shadowed", () => {
    const used = rowsOf(file("ℕ", "x = y ∧ ∀ x : ℕ, x = y"), "t");
    expect(used.rows).toEqual(["v1 § x : ℕ", "v2 § y : ℕ", "r1 x = y", "r2 ∀ x : ℕ", "r3 x = y"]);
    expect(rowsOf(file("ℤ", "x = y ∧ ∀ x : ℕ, x = y"), "t").key).not.toBe(used.key);
    const shadowed = rowsOf(file("ℕ", "(∀ x : ℕ, x = x) ∧ y = y"), "t");
    expect(shadowed.rows).toEqual(["v1 § y : ℕ", "r1 ∀ x : ℕ", "r2 x = x", "r3 y = y"]);
    expect(rowsOf(file("ℤ", "(∀ x : ℕ, x = x) ∧ y = y"), "t").key).toBe(shadowed.key);
  });
  it("reads what each binder binds and how far: a signature group all that follows, a quantifier its bracket", () => {
    const free = freeNames("(a : T b) : (∀ (c : ℕ) (d : U), P c d e) ∧ c = a ∧ ∃ f ∈ s, fun g => g f W.n");
    expect([..."abcdefgs", "W"].filter((n) => free.has(n))).toEqual(["b", "c", "e", "s", "W"]);
  });
});

describe("where a statement starts and ends", () => {
  const rows = (source: string) => viewRows(leanStatementView(source)!).map((r) => (r.kind === "binder" ? `${r.names} : ${r.lean}` : r.lean));
  // The finding: `n = n | 0 => rfl | n + 1 => rfl` was the conclusion row.
  it("ends where the arms of a proof by pattern matching begin", () => {
    const v = leanStatementView("theorem t : ∀ n : ℕ, n = n\n  | 0 => rfl\n  | n + 1 => by\n    have h := rfl\n    exact h")!;
    expect(v.statement).toBe("theorem t : ∀ n : ℕ, n = n");
    expect(viewRows(v).map((r) => r.lean)).toEqual(["∀ n : ℕ", "n = n"]);
    // a `match` of the statement's own keeps its alternatives; a bar that opens a line of it is no arm
    expect(rows("theorem t (b : Bool) : match b with\n  | true => A\n  | false => B := by\n  sorry")).toEqual(["b : Bool", "match b with", "| true =>", "A", "| false =>", "B"]);
    expect(rows("theorem t (x : ℝ) :\n    |x| ≤ 1 → P x := by\n  cases h with\n  | inl h => simp")).toEqual(["x : ℝ", "|x| ≤ 1", "P x"]);
  });
  it("takes no universe binder for a row, and reads a quoted name", () => {
    expect(rows("theorem t.{u, v} {α : Type u} (x : α) : x = x := rfl")).toEqual(["α : Type u", "x : α", "x = x"]);
    // the universe names are no part of the key, as the theorem's name is not
    expect(leanStatementView("theorem t.{u, v} {α : Type u} (x : α) : x = x := rfl")!.key).toBe(leanStatementView("theorem s {α : Type u} (x : α) : x = x := rfl")!.key);
    const quoted = "theorem «weird name» (x : ℕ) : x = x := rfl\n";
    expect(leanStatementView(declSource(quoted, "«weird name»")!)!.statement).toBe("theorem «weird name» (x : ℕ) : x = x");
    expect(rows(quoted)).toEqual(["x : ℕ", "x = x"]);
    expect(flatLeanRows(quoted)!.map((r) => r.id)).toEqual(["x", "⊢"]);
    expect(flatLeanRows("theorem t.{u} (x : ℕ) : x = x := rfl")!.map((r) => r.id)).toEqual(["x", "⊢"]);
  });
});

function withVars(text: string, name: string) {
  const line = text.split("\n").findIndex((l) => new RegExp(`^(?:theorem|lemma) ${name}(?![\\w'])`).test(l)) + 1;
  const v = leanStatementView(declSource(text, name, line)!)!;
  withSectionVariables(v, text, line);
  return v;
}

describe("a `∀` header's chip", () => {
  // The finding: `∀ ha : MemLp …` (a quantifier over a proof) was chipped "for each".
  it("is an assumption when it quantifies over a proof, an object otherwise", () => {
    expect(forallHeaderChip("∀ ha : MemLp g 2 μ")).toBe("hyp");
    expect(forallHeaderChip("∀ h : 0 < n")).toBe("hyp");
    expect(forallHeaderChip("∀ n : ℕ")).toBe("decl");
    expect(forallHeaderChip("∀ x ∈ s")).toBe("decl");
    expect(forallHeaderChip("∀ ε > 0")).toBe("decl");
    expect(forallHeaderChip("∀ k")).toBe("decl");
  });
});
