// The paper page's nested Lean statement: the links on the view's rows (one source of row ids),
// links written for another cut of the same statement and links that are not this statement's,
// the chip on each binder, the paper's own Prop-valued declarations a row names, the core node each
// formalizes with its place on the page, a clause that is another theorem's statement
// (`type_of% @name`) opened in place, and the drawer's renderer (its phrases ride on lines, never on
// cards; every line says in a word what it is).
import { mkdtempSync, mkdirSync, readFileSync, utimesSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import vm from "node:vm";
import { describe, expect, it } from "vitest";
import { flatLeanRows, leanStatementView, statementRows, viewRows } from "../../src/formalization/nl_links.js";
import { binderChip, leanScopes, parseFileDecls, withSectionVariables } from "../../src/formalization/lean_rows.js";
import { nodeTagAbove } from "../../src/graph/extractor.js";
import { applyLinks, boundNames, eachRow, leanDefs, linksRefusal, propDeclView, type PageCard, type PageRow, type PageView, type StoredRow } from "../../src/ui/lean_view.js";
import { citedNames, coreWhere, runDetail } from "../../src/ui/run_model.js";
import type { ToolkitConfig } from "../../src/toolkit/config.js";

const NESTED = `theorem main (P : Law) (hP : Good P 1) :
    (Base P → rate P ≤ 1 → Good P 2) ∧ (∀ c : ℝ, 0 < c → ∃ d : ℝ, c < d ∧ Good P d) := by
  sorry`;
const PLAIN = "theorem plain (P : Law) [Fact (0 < 1)] (hP : Good P 1) : Good P 2 ∧ Base P := by\n  sorry";

const view = (source: string) => leanStatementView(source) as PageView;
/** One line per row: its text, its phrases (or `unstated`), `~` when the link is not its own. */
const marks = (v: PageView) => { const out: string[] = []; eachRow(v, (r, content) => out.push(`${content.replace(/\s+/g, " ")} | ${r.xl ?? (r.unstated ? "unstated" : "")}${r.coarse ? " ~" : ""}`)); return out; };
const stored = (source: string, f: (id: string) => string[], cut: "flat" | "view" = "flat"): StoredRow[] =>
  (cut === "flat" ? flatLeanRows(source)! : viewRows(leanStatementView(source)!)).map((r) => ({ ...r, segments: f(r.id), unstated: r.kind !== "instance" && f(r.id).length === 0 }));

describe("applyLinks: the stored links on the view's rows", () => {
  it("links of the statement's own rows go row by row, at any depth, under the key they were written with", () => {
    const v = view(NESTED);
    const rows = stored(NESTED, (id) => (id === "r5" ? ["s2", "s3"] : id === "r8" ? ["s4"] : id === "r1" ? [] : ["s1"]), "view");
    expect(applyLinks(v, rows, v.key)).toBe(true);
    expect(v.sharedHyps[0]).toMatchObject({ id: "r1", unstated: true });
    expect(v.conclusions[0]).toMatchObject({ id: "r5", code: "Good P 2", xl: "s2 s3" });
    // the `∃ d : ℝ,` line is the splitting card's own row
    expect(v.conclusions[1]).toMatchObject({ id: "r8", intro: "∃ d : ℝ,", xl: "s4" });
    expect(marks(v).every((m) => !m.endsWith("~"))).toBe(true);
    // a row F5 marked as under a blanket list keeps that mark
    const blanket = view(NESTED);
    applyLinks(blanket, rows.map((r) => (r.id === "r3" ? { ...r, coarse: true } : r)), blanket.key);
    expect(marks(blanket).filter((m) => m.endsWith("~"))).toEqual(["Base P | s1 ~"]);
  });
  it("links written for the flat cut carry over: a row that is one stored row takes its link as its own", () => {
    const v = view(PLAIN);
    const old = stored(PLAIN, (id) => (id === "hP" ? ["s1"] : id === "⊢2" ? ["s2"] : []));
    expect(old.map((r) => r.id)).toEqual(["P", "inst1", "hP", "⊢1", "⊢2"]);
    expect(applyLinks(v, old)).toBe(true);
    expect(marks(v)).toEqual(["(P : Law) | unstated", "[Fact (0 < 1)] | ", "(hP : Good P 1) | s1", "Good P 2 | unstated", "Base P | s2"]);
  });
  it("… and the rows one stored row is now cut into share its link, marked coarse", () => {
    const v = view(NESTED);
    expect(applyLinks(v, stored(NESTED, (id) => (id === "hP" ? ["s1"] : id.startsWith("⊢1") ? ["s2"] : id.startsWith("⊢2") ? ["s3", "s4"] : [])))).toBe(true);
    expect(marks(v)).toEqual([
      "(P : Law) | unstated", "(hP : Good P 1) | s1",
      // clause 1 was cut premise by premise already: each row keeps its own
      "Base P | s2", "rate P ≤ 1 | s2", "Good P 2 | s2",
      // clause 2 was one row
      "∀ c : ℝ | s3 s4 ~", "0 < c | s3 s4 ~", "∃ d : ℝ, | s3 s4 ~", "c < d | s3 s4 ~", "Good P d | s3 s4 ~",
    ]);
    // links of the flat cut as it once was (a clause never cut into its premises): the same statement, placed the same way
    const older: StoredRow[] = [
      { id: "P", names: "P", lean: "Law", segments: [], unstated: true }, { id: "hP", names: "hP", lean: "Good P 1", segments: ["s1"] },
      { id: "⊢1", lean: "(Base P → rate P ≤ 1 → Good P 2)", segments: ["s2"] }, { id: "⊢2", lean: "(∀ c : ℝ, 0 < c → ∃ d : ℝ, c < d ∧ Good P d)", segments: ["s3"] },
    ];
    const w = view(NESTED);
    expect(applyLinks(w, older)).toBe(true);
    expect(marks(w).slice(2, 6)).toEqual(["Base P | s2 ~", "rate P ≤ 1 | s2 ~", "Good P 2 | s2 ~", "∀ c : ℝ | s3 ~"]);
  });
  it("links of an older nested cut, vouched for by the key: placed by where their rows stand", () => {
    const TELESCOPE = "theorem tele (P : Law) :\n    (∀ {Ω : Type*} [MeasurableSpace Ω] (W : World Ω) (hW : Good W 1), 0 < rate W → Fine W) ∧ Base P := by\n  sorry";
    const v = view(TELESCOPE);
    const rows: StoredRow[] = [
      { id: "r1", names: "P", lean: "Law", segments: [], unstated: true },
      { id: "r2", lean: "∀ {Ω : Type*} [MeasurableSpace Ω] (W : World Ω) (hW : Good W 1)", segments: ["s1", "s2"] },
      { id: "r3", lean: "0 < rate W", segments: ["s3"] }, { id: "r4", lean: "Fine W", segments: ["s4"] }, { id: "r5", lean: "Base P", segments: [], unstated: true },
    ];
    expect(applyLinks(v, rows, v.key)).toBe(true);
    expect(marks(v)).toEqual([
      "(P : Law) | unstated",
      "{Ω : Type*} | s1 s2 ~", "[MeasurableSpace Ω] | s1 s2 ~", "(W : World Ω) | s1 s2 ~", "(hW : Good W 1) | s1 s2 ~",
      "0 < rate W | s3", "Fine W | s4", "Base P | unstated",
    ]);
    // without the key nothing vouches for rows that are not the flat cut's; under another key they are another statement's
    expect(applyLinks(view(TELESCOPE), rows)).toBe(false);
    expect(applyLinks(view(TELESCOPE), rows, "0".repeat(40))).toBe(false);
  });

  // The finding these guard: stored links attached to a CHANGED statement (four constructed cases
  // of four). A refusal leaves the view untouched; the page then draws it unlinked, with a notice.
  const refused = (was: string, now: string, cut: "flat" | "view" = "flat") => {
    const v = view(now);
    const before = JSON.stringify(v);
    expect(applyLinks(v, stored(was, () => ["s1"], cut)), `${was}\n→ ${now}`).toBe(false);
    expect(JSON.stringify(v)).toBe(before);
  };
  it("refuses links of a statement whose conclusion was rewritten", () => {
    refused("theorem main (P : Law) (hP : Good P 1) : Good P 2 ∧ Base P := by sorry", "theorem main (P : Law) (hP : Good P 1) : Good P 99 ∧ (Awful P → Base P) := by sorry");
  });
  it("refuses links of a statement that gained a hypothesis", () => {
    refused("theorem main (P : Law) : (Base P → Good P 2) ∧ Base P := by sorry", "theorem main (P : Law) (hExtra : Strong P) : (Base P → Good P 2) ∧ Base P := by sorry");
  });
  it("refuses links when a connective changed — inside a stored row, or between two", () => {
    refused("theorem t (P : Law) : ∀ c : ℝ, 0 < c → Good P c := by sorry", "theorem t (P : Law) : ∀ c : ℝ, 0 < c ∧ Good P c := by sorry");
    // `→` between the stored rows `0 < c` and `Good P c` is what the flat cut's ids say; `∧` is another statement
    refused("theorem t (P : Law) (c : ℝ) : 0 < c → Good P c := by sorry", "theorem t (P : Law) (c : ℝ) : 0 < c ∧ Good P c := by sorry");
    refused("theorem t (P : Law) (c : ℝ) : 0 < c ∧ Good P c := by sorry", "theorem t (P : Law) (c : ℝ) : 0 < c → Good P c := by sorry");
  });
  // The finding this guards: links of the flat cut (no key) attached to a regrouped statement — the
  // glue between their rows was checked, not where the brackets stood.
  it("refuses links of the flat cut when brackets moved between its rows", () => {
    refused("theorem t (P : Law) : A P ∧ (B P → C P) := by sorry", "theorem t (P : Law) : (A P ∧ B P) → C P := by sorry");
    refused("theorem t : A → (B ∧ C) := by sorry", "theorem t : (A → B) ∧ C := by sorry");
    refused("theorem t : (∀ x, P x) ∧ Q := by sorry", "theorem t : ∀ x, (P x ∧ Q) := by sorry");
    refused("theorem t (P : Law) : (A P → B P) ∧ C P := by sorry", "theorem t (P : Law) : B P ∧ (A P → C P) := by sorry");
    // … and the flat cut honours Lean's precedence: `A ∧ B → C` is one premise, not two conjuncts
    expect(flatLeanRows("theorem t : A ∧ B → C := by sorry")!.map((r) => `${r.id} ${r.lean}`)).toEqual(["⊢.h1 A ∧ B", "⊢ C"]);
    expect(flatLeanRows("theorem t : A → B ↔ C := by sorry")!.map((r) => `${r.id} ${r.lean}`)).toEqual(["⊢ A → B ↔ C"]);
  });
  it("keeps keyed links of a theorem only renamed", () => {
    const was = "theorem t (P : Law) (hP : Good P 1) : Good P 2 ∧ Base P := by sorry";
    const v = view(was.replace("theorem t ", "theorem t' "));
    expect(applyLinks(v, stored(was, () => ["s1"], "view"), view(was).key)).toBe(true);
  });
  it("refuses links when brackets were regrouped: the same rows in the same order, another statement", () => {
    const [v1, v2] = ["theorem t (P : Law) : (∀ c : ℝ, Base P → (Good P c ∧ Fine P)) := by sorry", "theorem t (P : Law) : (∀ c : ℝ, (Base P → Good P c) ∧ Fine P) := by sorry"];
    expect(viewRows(leanStatementView(v1)!).map((r) => r.lean)).toEqual(viewRows(leanStatementView(v2)!).map((r) => r.lean));
    refused(v1, v2, "view");
    // … also when the links carry the key of the statement they were written for
    const v = view(v2);
    expect(applyLinks(v, stored(v1, () => ["s1"], "view"), leanStatementView(v1)!.key)).toBe(false);
    expect(leanStatementView(v1)!.key).not.toBe(v.key);
  });
  it("refuses links when a binder's type changed, a stored row has no place, or the stored goal stops short", () => {
    refused("theorem t (P : Law) (hP : Good P 1) : Good P 2 := by sorry", "theorem t (P : Law) (hP : Good P 7) : Good P 2 := by sorry");
    const v = view(NESTED);
    expect(applyLinks(v, stored(NESTED, () => ["s1"]).filter((r) => !r.id.startsWith("⊢2")))).toBe(false);
    expect(applyLinks(v, [...stored(NESTED, () => ["s1"]), { id: "⊢3", lean: "Extra P", segments: ["s5"] }])).toBe(false);
    // a goal an older cut ended at a `let`'s `:=`: the links were given for a row that is not the goal
    const LET = "theorem t (P : Law) :\n    let A := norm P\n    A ≤ 1 ∧ Good P 2 := by\n  sorry";
    expect(flatLeanRows(LET)!.at(-1)).toMatchObject({ id: "⊢", lean: "let A := norm P A ≤ 1 ∧ Good P 2" });
    const cutShort: StoredRow[] = [{ id: "P", names: "P", lean: "Law", segments: [] }, { id: "⊢", lean: "let A", segments: ["s1"] }];
    expect(applyLinks(view(LET), cutShort)).toBe(false);
    expect(linksRefusal(view(LET), cutShort)).toBe("truncated");
    expect(linksRefusal(view(LET), [...cutShort.slice(0, 1), { id: "⊢", lean: "let B", segments: ["s1"] }])).toBe("recut");
    expect(applyLinks(view(LET), stored(LET, () => ["s1"]))).toBe(true);
    expect(JSON.stringify(v)).not.toContain("s1");
  });
});

// The finding these guard: "given" on real hypotheses (`_hRange : PropensityRange …`), "assume" on
// a data binder (`Y : ∀ a, Fin (N a) → Fin Q → ℝ`) and on a quantifier header.
describe("chips: an object or a hypothesis", () => {
  it("binderChip: the type decides when it is a proposition or data by its shape; else what its head is; else the name", () => {
    const chip = (group: string, known?: "prop" | "data") => { const [names, type] = group.slice(1, -1).split(/ : (.*)/s); return binderChip(names, type, known); };
    // a proposition by its shape, whatever the name
    for (const g of ["(lt : a < b)", "(x : 0 ≤ ρ ∧ ρ < 1)", "(hf : ∀ n, 0 < f n)", "(e : ∃ c : ℝ, 0 < c)", "(m : x ∈ s)", "(ae : ∀ᵐ ω ∂μ, f ω = g ω)", "(hne : ¬ Empty α)"]) expect(chip(g), g).toBe("hyp");
    // data by its shape, whatever the name
    for (const g of ["(Y : ∀ a, Fin (N a) → Fin Q → ℝ)", "(h : ℝ)", "(h0 : ℝ)", "(hseq : ℕ → ℝ)", "(hstar : ℝ≥0∞)", "(H : Vec r →L[ℝ] ℝ)", "(hΩ : Type*)", "(hs : Set (ℝ × ℝ))", "(e : α ≃ β)"]) expect(chip(g), g).toBe("decl");
    // neither: the hypothesis names
    for (const g of ["(_hRange : PropensityRange P.μ W.X π)", "(hN : Tendsto N atTop atTop)", "(h : Foo x)", "(hfolds : ∀ k, EqualFolds (rowSize L k) L (folds k))", "(h_noise : NoiseBound P σ)"]) expect(chip(g), g).toBe("hyp");
    for (const g of ["(P : Law)", "(μ : Measure Ω)", "(W : World Ω X μ)", "(F : ImprovedPanelData W z ν)", "(HRange : PropensityRange P)"]) expect(chip(g), g).toBe("decl");
    // … unless the page knows what the type's head is
    expect(chip("(range : PropensityRange P.μ W.X π)", "prop")).toBe("hyp");
    expect(chip("(hist : History P)", "data")).toBe("decl");
    expect(chip("(h : ℝ)", "prop")).toBe("decl");
  });
  it("leanStatementView chips every hypothesis row: binders by that rule, a `∀` header as the quantifier it is, a premise as a hypothesis", () => {
    const v = leanStatementView("theorem t (Y : ∀ a, Fin (N a) → ℝ) (_hRange : Range Y) {α : Type} [Fintype α] (h : ℝ) (hF : FraserCLT) : ∀ ha : MemLp g 2 μ, ∀ n : ℕ, 0 < n → let c := h + 1; (P n → Q n) → R n := by sorry", new Set(["FraserCLT"]))!;
    expect(v.sharedHyps.map((r) => `${r.chip} ${r.code}`)).toEqual([
      "decl (Y : ∀ a, Fin (N a) → ℝ)", "hyp (_hRange : Range Y)", "decl {α : Type}", "decl [Fintype α]", "decl (h : ℝ)",
      // a hypothesis that assumes a result the paper cites
      "cited (hF : FraserCLT)",
      "hyp ∀ ha : MemLp g 2 μ", "decl ∀ n : ℕ", "hyp 0 < n",
    ]);
    expect(v.conclusions[0].hyps.map((r) => `${r.chip} ${r.code}`)).toEqual(["decl let c := h + 1", "hyp (P n → Q n)"]);
    // the rows of a premise's own clauses are chipped too
    expect(v.conclusions[0].hyps[1].sub![0].hyps.map((r) => r.chip)).toEqual(["hyp"]);
  });
  it("citedNames: the declarations stating the run's cited gates, qualified and by leaf", () => {
    expect([...citedNames({ nodes: [
      { id: "lem:fraser", kind: "gate", lean: { decl_name: "Papers.Demo.FraserCLT" }, gate: { gate_class: "cited" } },
      { id: "ass:reg", kind: "gate", lean: { decl_name: "Papers.Demo.Regular" }, gate: { gate_class: "bookkeeping" } },
      { id: "thm:a", kind: "theorem", lean: { decl_name: "Papers.Demo.a" } },
    ] })].sort()).toEqual(["FraserCLT", "Papers.Demo.FraserCLT"]);
    expect(citedNames(null).size).toBe(0);
  });
});

describe("propDeclView: what a row's name opens", () => {
  it("a Prop-valued definition and a Prop-valued record; nothing else", () => {
    const def = propDeclView("def Good (P : Law) (c : ℝ) : Prop :=\n  Base P ∧ 0 < c")!;
    expect(def.role).toBe("definition");
    expect(def.view!.defRow!.code).toBe("Good P c : Prop");
    expect(def.view!.conclusions.map((c) => c.code)).toEqual(["Base P", "0 < c"]);
    const rec = propDeclView("structure Base (P : Law) : Prop where\n  pos : 0 < P.n\n  fin : P.n < 10")!;
    expect(rec.role).toBe("assumption");
    expect(rec.view!.conclusions.map((c) => c.code)).toEqual(["pos : 0 < P.n", "fin : P.n < 10"]);
    expect(propDeclView("noncomputable def rate (P : Law) : ℝ := 1")).toBeNull();
    // a cited result's statement is written `Sort 0`: the same thing as `Prop`
    const cited = propDeclView("noncomputable def CitedClt : Sort 0 :=\n  ∀ (n : ℕ) (x : ℝ), 0 < n → Base n")!;
    expect(cited.role).toBe("definition");
    expect(cited.view!.defRow!.code).toBe("CitedClt : Prop");
    expect(cited.view!.sharedHyps.map((r) => r.code)).toEqual(["(n : ℕ)", "(x : ℝ)", "0 < n"]);
    expect(cited.view!.conclusions.map((c) => c.code)).toEqual(["Base n"]);
    // also with its signature over several lines
    expect(propDeclView("def CitedUi\n    (A : Law) (J : ℕ → ℕ) : Sort 0 :=\n  Base A →\n  Good A J")!.view!.defRow!.code).toBe("CitedUi A J : Prop");
    expect(propDeclView("structure Law where\n  n : ℕ")).toBeNull();
    expect(propDeclView("theorem t : True := trivial")).toBeNull();
    // its own parameters are chipped by the same rule as a theorem's
    expect(propDeclView("def D (_hR : Range P) (Y : ∀ a, Fin a → ℝ) : Prop := True")!.view!.sharedHyps.map((h) => h.chip)).toEqual(["hyp", "decl"]);
  });
  it("boundNames: binder groups, quantifier headers and lets are not references", () => {
    const v = view("theorem t (P Q : Law) {α : Type} : ∀ (c : ℝ) (d : ℝ), 0 < c → ∃ e f : ℝ, e < f ∧ (let g := e + f; g < c ∧ P = Q) := by sorry");
    expect([...boundNames(v)].sort()).toEqual(["P", "Q", "c", "d", "e", "f", "g", "α"].sort());
  });
});

describe("leanDefs: the paper's own Prop-valued declarations a statement names", () => {
  const root = mkdtempSync(path.join(tmpdir(), "tc-leanview-"));
  const lean = path.join(root, "Papers", "Demo");
  mkdirSync(path.join(lean, "Helpers"), { recursive: true });
  mkdirSync(path.join(lean, "tmp"), { recursive: true });
  mkdirSync(path.join(root, "Toolkit"), { recursive: true });
  writeFileSync(path.join(lean, "T.lean"), `import Mathlib\nimport Papers.Demo.Helpers.Defs\nimport Toolkit.Outside\n\nnamespace Papers.Demo\n\n${NESTED}\n\ntheorem shadow (Base : ℕ) (h : Scratch) : Base = Base ∧ Loop := by\n  sorry\n\ntheorem kinds (range : Good P 1) (hist : Law) (hF : FraserCLT) : Loop := by\n  sorry\n\nend Papers.Demo\n`);
  writeFileSync(path.join(lean, "Helpers", "Defs.lean"), [
    "import Papers.Demo.Helpers.Base", "", "namespace Papers.Demo", "",
    "/-- The rate. -/", "noncomputable def rate (P : Law) : ℝ := 1", "",
    "def Good (P : Law) (c : ℝ) : Prop :=", "  Base P ∧ rate P ≤ c", "",
    "-- @node: ass:pin-1", "def Loop : Prop := Pool ∧ True", "", "def Pool : Prop := Loop", "", "end Papers.Demo", "",
  ].join("\n"));
  writeFileSync(path.join(lean, "Helpers", "Base.lean"), "namespace Papers.Demo\n\nstructure Law where\n  n : ℕ\n\n-- @node: ass:base\n/-- The base\ncondition. -/\nstructure Base (P : Law) : Prop where\n  pos : 0 < P.n\n\nend Papers.Demo\n");
  writeFileSync(path.join(lean, "tmp", "Scratch.lean"), "def Scratch : Prop := True\n");
  writeFileSync(path.join(root, "Toolkit", "Outside.lean"), "def Outside : Prop := True\ndef Good : Prop := False\n");
  const src = (decl: string) => readFileSync(path.join(lean, "T.lean"), "utf8").split(`theorem ${decl}`)[1].split("\n\n")[0];
  const refsOf = (v: PageView) => { const out: Record<string, string[]> = {}; eachRow(v, (r, content) => { if (r.refs) out[content] = r.refs; }); return out; };

  it("stamps each row with the declarations it names and files each once, with those it names in turn", async () => {
    const v = view(`theorem main${src("main")}`);
    const named = leanDefs(root, lean);
    await named.annotate(v, "T.lean", "Papers.Demo.main");
    const good = "Helpers/Defs.lean#Good", base = "Helpers/Base.lean#Base";
    expect(refsOf(v)).toEqual({ "(hP : Good P 1)": [good], "Base P": [base], "Good P 2": [good], "Good P d": [good] });
    // `rate` is a data definition, `Law` a data record: neither opens
    expect(Object.keys(named.defs).sort()).toEqual([base, good].sort());
    expect(named.defs[good]).toMatchObject({ name: "Good", kind: "def", file: "Helpers/Defs.lean", line: 8, role: "definition", source: "" });
    // the definition's own row names the record: one level down, in the same table
    expect(named.defs[good].view!.conclusions[0]).toMatchObject({ code: "Base P", refs: [base] });
    expect(named.defs[base]).toMatchObject({ kind: "structure", role: "assumption", node: "ass:base" });
    // an untagged declaration formalizes no core node
    expect("node" in named.defs[good]).toBe(false);
    expect(named.defs[base].view!.conclusions.map((c) => c.code)).toEqual(["pos : 0 < P.n"]);
  });
  it("a bound name is not a reference, a file not imported is out of scope, and a cycle ends", async () => {
    const v = view(`theorem shadow${src("shadow")}`);
    const named = leanDefs(root, lean);
    await named.annotate(v, "T.lean", "Papers.Demo.shadow");
    expect(refsOf(v)).toEqual({ Loop: ["Helpers/Defs.lean#Loop"] });
    expect(Object.keys(named.defs).sort()).toEqual(["Helpers/Defs.lean#Loop", "Helpers/Defs.lean#Pool"]);
    expect(named.defs["Helpers/Defs.lean#Pool"].view!.conclusions[0].refs).toEqual(["Helpers/Defs.lean#Loop"]);
    // a tag is the next declaration's alone
    expect(named.defs["Helpers/Defs.lean#Loop"].node).toBe("ass:pin-1");
    expect(named.defs["Helpers/Defs.lean#Pool"].node).toBeUndefined();
  });
  it("what a binder's type names decides its chip: a Prop-valued declaration of the paper a hypothesis, a data record an object", async () => {
    const v = view(`theorem kinds${src("kinds")}`);
    // by name alone neither is right
    expect(v.sharedHyps.map((h) => h.chip)).toEqual(["decl", "hyp", "hyp"]);
    const named = leanDefs(root, lean, new Set(["FraserCLT"]));
    const again = leanStatementView(`theorem kinds${src("kinds")}`, new Set(["FraserCLT"])) as PageView;
    await named.annotate(again, "T.lean", "Papers.Demo.kinds");
    expect(again.sharedHyps.map((h) => `${h.chip} ${h.code}`)).toEqual(["hyp (range : Good P 1)", "decl (hist : Law)", "cited (hF : FraserCLT)"]);
  });
  it("nodeTagAbove: the tag binds across a docstring and attributes, to the first declaration after it", () => {
    const lines = ["-- @node: ass:a", "/-- Doc", "def Fake : Prop -/", "@[simp]", "def A : Prop := True", "", "def B : Prop := A", "-- @node: ass:orphan", "-- @node: ass:c", "structure C : Prop where"];
    expect([4, 6, 9].map((at) => nodeTagAbove(lines, at))).toEqual(["ass:a", null, "ass:c"]);
  });
  it("coreWhere: a labelled environment, a passage of the text, or a reading the paper does not print", () => {
    const w = coreWhere({
      statements: [{ id: "thm:main", kind: "theorem", tex_locator: { label: "thm:main" } }, { id: "thm:prose", kind: "theorem" }],
      assumptions: [
        { id: "ass:base", condition: " the base holds ", tex_locator: { file: "m.tex", from: 3, to: 4, label: "ass:Base 1" } },
        { id: "ass:prose", condition: "Assume no ties.", tex_locator: { file: "m.tex", from: 9, label: null } },
        { id: "ass:pin-1", condition: "The rate is uniform.", used_by: ["thm:main", "thm:prose"] },
      ],
      definitions: [{ id: "def:rate", construction: "Let $r$ be the rate.", tex_locator: { file: "m.tex", from: 6, to: 7 } }],
    });
    expect(w.places).toEqual({
      "thm:main": { anchor: "lbl-thm-main" }, "thm:prose": { anchor: "res-thm-prose" },
      "ass:base": { anchor: "lbl-ass-base-1", says: "the base holds" }, "ass:prose": { anchor: "res-ass-prose", says: "Assume no ties." },
      "ass:pin-1": { reading: true }, "def:rate": { anchor: "res-def-rate", says: "Let $r$ be the rate." },
    });
    expect(w.passages).toEqual([{ node: "ass:prose", file: "m.tex", from: 9, to: 9, text: "Assume no ties." }, { node: "def:rate", file: "m.tex", from: 6, to: 7, text: "Let $r$ be the rate." }]);
    expect(w.readings).toEqual([{ node: "ass:pin-1", text: "The rate is uniform.", labels: ["thm:main"] }]);
    expect(coreWhere(null)).toEqual({ places: {}, passages: [], readings: [] });
  });
  it("reads nothing outside the run's Lean directory", async () => {
    const v = view("theorem t (h : Outside) : Good := by sorry");
    const outside = leanDefs(root, path.join(root, "Toolkit"));
    await outside.annotate(v, "../Papers/Demo/T.lean", "t");
    expect(outside.defs).toEqual({});
    const elsewhere = leanDefs(root, path.dirname(root));
    await elsewhere.annotate(v, path.join(path.basename(root), "Toolkit", "Outside.lean"), "Outside");
    expect(elsewhere.defs).toEqual({});
    expect(JSON.stringify(v)).not.toContain("refs");
  });

  // The finding this guards: a drawer showed the STORED Lean rows of an older statement, with no notice.
  it("runDetail: the Lean drawn is the statement as it stands — linked when the stored links are its own, unlinked and said so when they are not", async () => {
    const cfg = { toolkitRoot: root } as ToolkitConfig;
    const run = (slug: string, links: unknown) => {
      const dir = path.join(root, "runs", slug);
      mkdirSync(path.join(dir, "discovery"), { recursive: true });
      writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V6", lean_subdir: "Papers/Demo", verify: { phase: "done" } }));
      writeFileSync(path.join(dir, "discovery", "core.json"), JSON.stringify({
        statements: [{ id: "thm:main", kind: "theorem", tex_locator: { label: "thm:main" } }],
        assumptions: [{ id: "ass:base", condition: "the base holds", tex_locator: { file: "m.tex", from: 3, to: 3, label: "ass:base" } }, { id: "ass:unused", condition: "x", tex_locator: { file: "m.tex", from: 5, label: "ass:unused" } }],
      }));
      writeFileSync(path.join(dir, "report.json"), JSON.stringify({ results: [{ node_id: "thm:main", bucket: "verified", lean: { decl: "Papers.Demo.main", file: "T.lean", line: 7 } }] }));
      if (links) writeFileSync(path.join(dir, "nl_links.json"), JSON.stringify(links));
    };
    const source = `theorem main${src("main")}`;
    const segments = [{ id: "s1", text: "Then it is good." }, { id: "s2", text: "$$ a<b,\\quad", display: "s2" }, { id: "s3", text: "c<d $$", display: "s2" }];
    const scopes = leanScopes({ toolkitRoot: root, leanDir: lean, read: async (abs) => readFileSync(abs, "utf8") });
    const cut = (await statementRows(source, { file: "T.lean", decl: "Papers.Demo.main", lean: scopes }))!;
    run("fresh", null);
    run("linked", { results: [{ node: "thm:main", key: cut.key, segments, uncovered: ["s3"], rows: cut.rows.map((r) => ({ ...r, segments: r.id === "r5" ? ["s1"] : [], unstated: r.id !== "r5" })) }] });
    run("old", { results: [{ node: "thm:main", segments, uncovered: [], rows: flatLeanRows(source)!.map((r) => ({ ...r, segments: ["s1"], unstated: false })) }] });
    run("stale", { results: [{ node: "thm:main", segments, uncovered: ["s1"], rows: [{ id: "P", kind: "binder", names: "P", lean: "Law" }, { id: "hP", kind: "binder", names: "hP", lean: "Good P 1" }, { id: "⊢", kind: "conclusion", names: "", lean: "Good P 3" }].map((r) => ({ ...r, segments: ["s1"], unstated: false })) }] });
    run("rekeyed", { results: [{ node: "thm:main", key: "0".repeat(40), segments, uncovered: [], rows: cut.rows.map((r) => ({ ...r, segments: ["s1"], unstated: false })) }] });

    const fresh = (await runDetail(cfg, "fresh")).results[0];
    expect(fresh.rows!.map((r) => r.id)).toEqual(["r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8", "r9", "r10"]);
    expect(fresh.leanView!.conclusions[0]).toMatchObject({ id: "r5", refs: ["Helpers/Defs.lean#Good"] });
    expect(fresh).toMatchObject({ segments: null, uncovered: [] });
    expect("linksStale" in fresh).toBe(false);
    const detail = await runDetail(cfg, "fresh");
    expect(Object.keys(detail.leanDefs).sort()).toEqual(["Helpers/Base.lean#Base", "Helpers/Defs.lean#Good"]);
    // one place per core node a named declaration formalizes — no other node of the core
    expect(detail.leanDefs["Helpers/Base.lean#Base"].node).toBe("ass:base");
    expect(detail.places).toEqual({ "ass:base": { anchor: "lbl-ass-base", says: "the base holds" } });
    // what the links are checked against stays on the server
    expect(JSON.stringify(fresh.leanView)).not.toMatch(/"statement"|"key"/);

    // the statements are cut once: held while the run's records and the Lean files read stand, cut again when one changed
    expect((await runDetail(cfg, "fresh")).results[0].leanView).toBe(fresh.leanView);
    expect((await runDetail(cfg, "fresh", { lean: false })).results[0]).toMatchObject({ rows: null, leanView: null, lean: { decl: "Papers.Demo.main" }, proved: true });
    const defsFile = path.join(lean, "Helpers", "Defs.lean"), later = new Date(Date.now() + 5000);
    utimesSync(defsFile, later, later);
    const again = (await runDetail(cfg, "fresh")).results[0];
    expect(again.leanView).not.toBe(fresh.leanView);
    expect(again.leanView).toEqual(fresh.leanView);
    expect((await runDetail(cfg, "fresh")).results[0].leanView).toBe(again.leanView);
    const reportFile = path.join(root, "runs", "fresh", "report.json");
    utimesSync(reportFile, later, later);
    expect((await runDetail(cfg, "fresh")).results[0].leanView).not.toBe(again.leanView);

    const linked = (await runDetail(cfg, "linked")).results[0];
    expect(linked.leanView!.conclusions[0]).toMatchObject({ id: "r5", xl: "s1" });
    expect(linked.leanView!.sharedHyps[0]).toMatchObject({ id: "r1", unstated: true });
    expect(linked.rows!.find((r) => r.id === "r5")).toMatchObject({ lean: "Good P 2", segments: ["s1"], unstated: false });
    // a display cut into parts reaches the page as parts of one display: each as the formula it is alone, the first with the whole
    expect(linked.segments).toEqual([
      segments[0],
      { ...segments[1], alone: { text: "\\[ a<b,\\quad\\]" }, whole: { text: "$$ a<b,\\quadc<d $$" } },
      { ...segments[2], alone: { text: "\\[c<d \\]" } },
    ]);
    expect(linked.uncovered).toEqual(["s3"]);

    // links of the flat cut: the view nests all the same, each clause's rows on that clause's phrases
    const old = (await runDetail(cfg, "old")).results[0];
    expect(old.leanView!.conclusions[0]).toMatchObject({ id: "r5", xl: "s1" });
    expect(old.leanView!.conclusions[0].hyps.map((h) => h.xl)).toEqual(["s1", "s1"]);
    expect("linksStale" in old).toBe(false);

    // links of another statement, by their rows or by their key: the current statement, unlinked, and the page told
    for (const slug of ["stale", "rekeyed"]) {
      const stale = (await runDetail(cfg, slug)).results[0];
      expect(stale.linksStale, slug).toBe(slug === "stale" ? "recut" : "changed");
      expect(stale.leanView!.conclusions[0], slug).toMatchObject({ id: "r5", code: "Good P 2" });
      expect(stale.rows!.map((r) => r.lean), slug).toEqual(fresh.rows!.map((r) => r.lean));
      expect(JSON.stringify(stale.rows), slug).not.toContain("Good P 3");
      expect(stale, slug).toMatchObject({ segments: null, uncovered: [] });
      expect(JSON.stringify(stale.leanView), slug).not.toMatch(/"xl"|"unstated"|"coarse"/);
    }

    // an assumption's declaration takes its node's links when they are its own: its rows carry the
    // block's phrases (ids told apart by the node) — in every drawer's copy of the page model
    const base = propDeclView("structure Base (P : Law) : Prop where\n  pos : 0 < P.n")!.view!;
    const baseLinks = (key: string) => ({ node: "ass:base", key, segments: [{ id: "s1", text: "the base holds" }], uncovered: ["s1"], rows: viewRows(base).map((r) => ({ ...r, segments: r.id === "r2" ? ["s1"] : [], unstated: r.id !== "r2" })) });
    run("deflinked", { results: [baseLinks(base.key)] });
    const withDef = await runDetail(cfg, "deflinked");
    expect(withDef.leanDefs["Helpers/Base.lean#Base"]).toMatchObject({ node: "ass:base", segments: [{ id: "ass:base:s1", text: "the base holds" }], uncovered: ["ass:base:s1"] });
    expect(withDef.leanDefs["Helpers/Base.lean#Base"].view).toMatchObject({ sharedHyps: [{ id: "r1", unstated: true }], conclusions: [{ id: "r2", xl: "ass:base:s1" }] });
    expect("segments" in withDef.leanDefs["Helpers/Defs.lean#Good"]).toBe(false);
    expect(JSON.stringify(withDef.leanDefs)).not.toMatch(/"key"/);
    // links for another version of the declaration, or none answered: its rows as they stand, no phrase
    run("defstale", { results: [baseLinks("0".repeat(40))] });
    run("defunanswered", { results: [{ ...baseLinks(base.key), unanswered: true }] });
    for (const slug of ["defstale", "defunanswered"]) {
      const d = (await runDetail(cfg, slug)).leanDefs["Helpers/Base.lean#Base"];
      expect("segments" in d || "uncovered" in d, slug).toBe(false);
      expect(JSON.stringify(d.view), slug).not.toMatch(/"xl"|"unstated"/);
      expect(d.view!.conclusions[0], slug).toMatchObject({ id: "r2", code: "pos : 0 < P.n" });
    }

    // a result F5 asked and no call answered: drawn with its rows, the page told
    run("unanswered", { results: [{ node: "thm:main", key: cut.key, unanswered: true, segments, uncovered: [], rows: cut.rows.map((r) => ({ ...r, segments: [], unstated: false })) }] });
    const unanswered = (await runDetail(cfg, "unanswered")).results[0];
    expect(unanswered).toMatchObject({ linksUnanswered: true });
    expect("linksStale" in unanswered).toBe(false);
    // a declaration the file no longer holds: no rows, and the page told
    run("gone", null);
    writeFileSync(path.join(root, "runs", "gone", "report.json"), JSON.stringify({ results: [{ node_id: "thm:main", bucket: "verified", lean: { decl: "Papers.Demo.renamed_away", file: "T.lean", line: 7 } }] }));
    const gone = (await runDetail(cfg, "gone")).results[0];
    expect(gone).toMatchObject({ leanMissing: true, rows: null, leanView: null });
  });

  // The drawer's renderer is plain page script: its section of app.js, run on the server's view.
  const js = readFileSync(path.join(__dirname, "..", "..", "src", "ui", "static", "app.js"), "utf8").replace(/\r\n/g, "\n");
  const section = js.slice(js.indexOf("const DS_TERMS"), js.indexOf("// a fold is drawn when first opened"));
  const drawer = (defs: Record<string, unknown>, places: Record<string, string> = {}) => {
    const ctx = vm.createContext({
      esc: (s: unknown) => String(s ?? "").replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c]!),
      P: { detail: { leanDefs: defs }, folds: new Set<string>() },
      plOf: (node?: string) => (node && places[node] ? { label: places[node] } : null),
    });
    vm.runInContext(`${section}\nglobalThis.draw = (v, x) => dsViewHTML(v, { terms: DS_TERMS.theorem, linked: true, path: "", depth: 0, n: { k: 0 }, ...x });\nglobalThis.def = (d, links) => dsDefHTML(d, "", 1, links);`, ctx);
    return { draw: (ctx as unknown as { draw: (v: PageView, x?: object) => string }).draw, def: (ctx as unknown as { def: (d: object, links?: object) => string }).def, folds: (ctx as unknown as { P: { folds: Set<string> } }).P.folds };
  };
  const linesOf = (html: string) => [...html.matchAll(/<div class="srow ([^"]*)" data-binder="([^"]*)"[^>]*>(?:<span class="ds-chip[^>]*>[^<]*<\/span>|<span><\/span>)?(?:<div class="ds-code">)?([^<]*)/g)].map((m) => `${m[3].replace(/&lt;/g, "<").replace(/\s+/g, " ")} | ${m[2]}${m[1].includes("xl-coarse") ? " ~" : ""}`);

  it("the drawer draws nested cards whose phrases ride on lines only, and opens a named declaration in place", async () => {
    const v = view(`theorem main${src("main")}`);
    const named = leanDefs(root, lean);
    await named.annotate(v, "T.lean", "Papers.Demo.main");
    applyLinks(v, viewRows(v as never).map((r) => ({ ...r, segments: r.kind === "instance" ? [] : [`s${r.id.slice(1)}`], unstated: false })), v.key);
    const places: Record<string, string> = {};
    const { draw, folds } = drawer(named.defs, places);
    const html = draw(v);
    const count = (re: RegExp) => (html.match(re) ?? []).length;
    expect(count(/<div/g)).toBe(count(/<\/div>/g));
    // every row is one line carrying its own phrases; no card, sub-card or fold carries any
    expect([...html.matchAll(/class="srow [^"]*" data-binder="([^"]*)"/g)].map((m) => m[1])).toEqual(["s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10"]);
    expect(count(/data-binder=/g)).toBe(10);
    expect(html).toContain(`<div class="ds-card"><div class="ds-label">Conclusion 2</div>`);
    expect(html).toContain(`<div class="ds-subs"><div class="ds-sub"><div class="srow ds-concl" data-binder="s9">`);
    expect(html).toContain(`<div class="srow ds-intro" data-binder="s8">∃ d : ℝ,</div>`);
    // every line but a plain `∀` or `∃ …,` opens with a word for what it is, the Lean term in its tooltip
    expect([...html.matchAll(/<span class="ds-chip ds-chip-(\w+)" title="([^"]*)">([^<]*)<\/span>/g)].map((m) => `${m[1]}:${m[3]}:${m[2]}`)).toEqual([
      "decl:given:binder", "hyp:assume:hypothesis",
      // of the hypotheses of one list only the first reads "assume"
      "hyp:assume:hypothesis", "hyp:and:hypothesis", "concl:then:what the result concludes",
      "hyp:assume:hypothesis", "concl:such that:what holds of the names just introduced", "concl:and:one more claim, alongside the one above",
    ]);
    expect(html).not.toMatch(/⊢<|>decl<|>hyp<|turnstile/);
    // closed folds hold nothing until opened
    expect(count(/<details class="ds-fold"/g)).toBe(4);
    expect(html).not.toContain("Holds when");
    const path0 = /data-fold="([^"]*#Good)"/.exec(html)![1];
    folds.add(path0);
    const opened = draw(v);
    expect(opened).toContain(`<details class="ds-fold" data-fold="${path0}" data-def="Helpers/Defs.lean#Good" data-depth="1" open>`);
    // a Prop is hypothesis or conclusion by where it stands: no "Holds when", its clauses read as claims
    expect(opened).not.toContain("Holds when");
    // the declaration's own rows are lines with no phrases of their own
    expect(opened).toContain(`<div class="srow ds-concl ds-def" data-binder=""><span class="ds-chip ds-chip-def" title="the declaration: its name, parameters and type">def</span><div class="ds-code">Good P c : Prop</div></div>`);
    expect(opened).toContain(`<span class="ds-chip ds-chip-concl" title="one of the claims this proposition makes">then</span><div class="ds-code">Base P</div>`);
    expect((opened.match(/data-binder="s\d+"/g) ?? []).length).toBe(10);
    // without links nothing claims a phrase, and no row is called unstated
    expect(draw(v, { linked: false })).not.toMatch(/data-binder="s|rtag/);
    // no place on the page: no chip, and no line carries a node
    expect(opened).not.toMatch(/ds-place|data-places/);
    // the place of the node a declaration formalizes: named on its fold, carried by the line naming it
    places["ass:base"] = "Assumption 1";
    const placed = draw(v);
    expect(placed).toContain(`<div class="srow ds-row ds-row-hyp" data-binder="s3" data-places="ass:base">`);
    expect(placed).toContain(`<code>Base</code><button type="button" class="ds-place" data-place="ass:base" title="Where the paper states this — click to go there">→ Assumption 1</button>`);
    // … also inside a declaration that is opened: `Good` names `Base`
    expect((placed.match(/class="ds-place"/g) ?? []).length).toBe(2);
    expect((placed.match(/data-places="ass:base"/g) ?? []).length).toBe(2);
  });

  // The findings these guard: the parts of a hypothesis read "then" under "assume"; `∃!` read "there
  // exist"; a named hypothesis with parts and a binder of the section had no line of their own.
  it("a declaration's rows carry its own phrases in its block's drawer, and none where a row of a statement opens it", () => {
    const view = propDeclView("def Good (P : Law) (c : ℝ) : Prop :=\n  Base P ∧ rate P ≤ c")!.view as PageView;
    eachRow(view, (row) => { if (row.id === "r1") row.unstated = true; else row.xl = `ass:good:s${row.id!.slice(1)}`; });
    const d = { role: "definition", view }, { def } = drawer({});
    expect(linesOf(def(d, { found: new Set(["ass:good:s3", "ass:good:s4", "ass:good:s5"]), whole: new Set() }))).toEqual(["(P : Law) | ", "(c : ℝ) | ass:good:s2", "Good P c : Prop | ass:good:s3", "Base P | ass:good:s4", "rate P ≤ c | ass:good:s5"]);
    expect(def(d, { found: new Set(["ass:good:s3"]), whole: new Set() })).toMatch(/not in the paper's text.*phrase not found on this page/s);
    expect(linesOf(def(d)).map((l) => l.split(" | ")[1])).toEqual(["", "", "", "", ""]);
    expect(def(d)).not.toMatch(/rtag|unstated/);
  });
  it("labels each line by what it is: a hypothesis's parts \"and\", a named one's head, `∃!`, either / or, a section binder", () => {
    const { draw } = drawer({});
    const text = (html: string) => [...html.matchAll(/<span class="ds-chip[^"]*" title="[^"]*">([^<]*)<\/span>(?:<div class="ds-code">)?([^<]*)/g)].map((m) => `${m[1]} ${m[2]}`.trim());
    expect(text(draw(view("theorem t : (A ∧ B ∧ C) → D := by sorry")))).toEqual(["assume", "and A", "and B", "and C", "then D"]);
    // an implication inside a premise keeps "then" for what it concludes
    expect(text(draw(view("theorem t : (A → B) → D := by sorry")))).toEqual(["assume", "assume A", "then B", "then D"]);
    expect(text(draw(view("theorem t (hI : A ∧ B ∧ C) : E := by sorry")))).toEqual(["assume (hI :", "and A", "and B", "and C", "then E"]);
    // of several hypotheses only the first reads "assume" / "if"; what a condition concludes from them reads "then"
    expect(text(draw(view("theorem t : A → B → C → D := by sorry")))).toEqual(["assume A", "and B", "and C", "then D"]);
    expect(text(draw({ ...view("theorem t : A → B → C ∧ D := by sorry"), defRow: { code: "Good : Prop" } } as PageView))).toEqual(["if A", "and B", "def Good : Prop", "then C", "and D"]);
    expect(text(draw(view("theorem t : ∃! x, P x ∧ Q x := by sorry")))[0]).toBe("there exists exactly one ∃! x,");
    const alt = draw(view("theorem t (h : A ∨ B ∧ C) : D := by sorry"));
    expect(text(alt)).toEqual(["assume (h :", "either A", "and B", "and C", "then D"]);
    expect(alt).toContain(`<div class="ds-label ds-alt" title="one alternative of a disjunction (∨)">or</div>`);
    const sec = view("theorem t (x : ℕ) : D x ν := by sorry");
    withSectionVariables(sec as never, "variable (ν : Measure Ω)\n\ntheorem t (x : ℕ) : D x ν := by sorry\n", 3);
    expect(draw(sec)).toMatch(/<div class="ds-code">\(ν : Measure Ω\)<\/div><span class="rtag rtag-section"[^>]*>from the section<\/span>/);
  });

  // The finding this guards: the rows Lean needs and the paper never says (types, instances, side
  // conditions) buried the few rows to compare with the paper.
  it("a run of three or more rows the paper says nowhere is one closed fold where it stands; the linked rows, short runs and conclusions stay", () => {
    const LONG = "theorem t (A : Type) (B : Type) (C : Type) (hA : P A) (D : Type) [Fact D] (hB : Q B) (E : Type) (F : Type) (G : Type) (hG : Z G) (hC : R C) :\n    (S A → T B → U C → V D → W) ∧ X := by\n  sorry";
    const linkedBy = (said: string[]) => { const v = view(LONG); applyLinks(v, viewRows(v as never).map((r, k) => { const segments = said.some((t) => r.lean.includes(t)) ? [`s${k + 1}`] : []; return { ...r, segments, unstated: r.kind !== "instance" && !segments.length }; }), v.key); return v; };
    const v = linkedBy(["P A", "Q B", "R C", "V D", "W", "X"]);
    const { draw, folds } = drawer({});
    const html = draw(v);
    const more = [...html.matchAll(/<details class="ds-fold ds-more" data-fold="([^"]*)"><summary[^>]*>([^<]*)<\/summary>(.*?)<\/details>/g)];
    expect(more.map((m) => m[2])).toEqual(["3 rows Lean adds (3 binders)", "4 rows Lean adds (3 binders, 1 hypothesis)", "3 rows Lean adds (3 hypotheses)"]);
    expect(more.map((m) => linesOf(m[3]).map((l) => l.split(" | ")[0]))).toEqual([["(A : Type)", "(B : Type)", "(C : Type)"], ["(E : Type)", "(F : Type)", "(G : Type)", "(hG : Z G)"], ["S A", "T B", "U C"]]);
    // outside the folds: the rows the paper states, the run of two between them, and every conclusion
    const outside = html.replace(/<details class="ds-fold ds-more".*?<\/details>/g, "");
    expect(linesOf(outside).map((l) => l.split(" | ")[0])).toEqual(["(hA : P A)", "(D : Type)", "[Fact D]", "(hB : Q B)", "(hC : R C)", "V D", "W", "X"]);
    // the rows are drawn as they were, in their order: without the fold lines it is the statement drawn whole
    const whole = draw(v, { linked: false }), strip = (h: string) => h.replace(/<details class="ds-fold ds-more"[^>]*><summary[^>]*>[^<]*<\/summary>|<\/details>/g, "");
    expect(linesOf(html).map((l) => l.split(" | ")[0])).toEqual(linesOf(whole).map((l) => l.split(" | ")[0]));
    expect(strip(html).replace(/ unstated| data-binder="[^"]*"|<span class="rtag">[^<]*<\/span>/g, "")).toBe(whole.replace(/ data-binder="[^"]*"/g, ""));
    // an opened fold stays open when the drawer is drawn again
    folds.add(more[1][1]);
    expect(draw(v)).toContain(`<details class="ds-fold ds-more" data-fold="${more[1][1]}" open>`);
    expect(new Set(more.map((m) => m[1])).size).toBe(3);
    // a conclusion the paper says nowhere is never folded; a statement with no link at all is drawn whole
    expect(linesOf(draw(linkedBy(["P A"])).replace(/<details class="ds-fold ds-more".*?<\/details>/g, "")).map((l) => l.split(" | ")[0])).toEqual(["(hA : P A)", "W", "X"]);
    expect(draw(linkedBy([]))).not.toContain("ds-more");
    expect(draw(view(LONG), { linked: false })).not.toContain("ds-more");
  });

  // The finding this guards: an inherited link looked exactly like one F5 gave the row.
  it("a link the row does not have alone is drawn quieter, its run of rows labelled once — unless the row is linked by its place", async () => {
    const v = view(`theorem main${src("main")}`);
    const named = leanDefs(root, lean);
    await named.annotate(v, "T.lean", "Papers.Demo.main");
    // links of a cut that gave each clause one row
    expect(applyLinks(v, [
      { id: "P", names: "P", lean: "Law", segments: [] }, { id: "hP", names: "hP", lean: "Good P 1", segments: ["s1"] },
      { id: "⊢1", lean: "(Base P → rate P ≤ 1 → Good P 2)", segments: ["s2", "s3"] }, { id: "⊢2", lean: "(∀ c : ℝ, 0 < c → ∃ d : ℝ, c < d ∧ Good P d)", segments: ["s3", "s4"] },
    ])).toBe(true);
    const { draw } = drawer(named.defs);
    const html = draw(v);
    expect(linesOf(html)).toEqual([
      "(P : Law) | ", "(hP : Good P 1) | s1",
      "Base P | s2 s3 ~", "rate P ≤ 1 | s2 s3 ~", "Good P 2 | s2 s3 ~",
      "∀ c : ℝ | s3 s4 ~", "0 < c | s3 s4 ~", "∃ d : ℝ, | s3 s4 ~", "c < d | s3 s4 ~", "Good P d | s3 s4 ~",
    ]);
    // one label per run of rows sharing a list: two clauses, two labels, each on the run's first row
    const label = `<span class="rtag rtag-coarse">this clause as a whole ↔ these phrases — not linked row by row yet</span>`;
    expect(html.split(label)).toHaveLength(3);
    expect(html).toContain(`<div class="ds-code">Base P</div>${label}`);
    expect(html).toContain(`<div class="ds-code">∀ c : ℝ</div>${label}`);
    // a row whose declaration has a place in the paper is linked by that place too — its phrases stay
    // its clause's, marked so (the finding: 117 such rows drawn as exact links); no "not linked"
    const placed = drawer(named.defs, { "ass:base": "Assumption 1" }).draw(v);
    expect(linesOf(placed).slice(2, 5)).toEqual(["Base P | s2 s3 ~", "rate P ≤ 1 | s2 s3 ~", "Good P 2 | s2 s3 ~"]);
    expect(placed).toContain(`<div class="ds-code">Base P</div>${label}`);
    expect(placed).toMatch(/class="srow ds-row ds-row-hyp xl-coarse" data-binder="s2 s3" data-places="ass:base"/);
    const bare = view(`theorem main${src("main")}`);
    await named.annotate(bare, "T.lean", "Papers.Demo.main");
    expect(drawer(named.defs, { "ass:base": "Assumption 1" }).draw(bare).match(/not linked yet/g)).toHaveLength(9);
    expect(drawer(named.defs).draw(bare).match(/not linked yet/g)).toHaveLength(10);
  });
  it("a row none of whose phrases is found on the page says so; a part of a display that lights its formula whole says that", () => {
    const v = view(PLAIN);
    applyLinks(v, stored(PLAIN, (id) => (id === "r3" ? ["s1", "s2"] : id === "r4" ? ["s3"] : id === "r5" ? ["s4"] : []), "view"), v.key);
    const { draw } = drawer({});
    const html = draw(v, { found: new Set(["s2", "s4"]), whole: new Set(["s4"]) });
    expect(html).toContain(`<div class="ds-code">(hP : Good P 1)</div></div>`);
    expect(html).toContain(`<div class="ds-code">Good P 2</div><span class="rtag">phrase not found on this page</span>`);
    expect(html).toContain(`<div class="ds-code">Base P</div><span class="rtag rtag-coarse">lights its formula whole</span>`);
    // when the page cannot tell where phrases stand at all, no row is blamed
    expect(draw(v, { found: null })).not.toContain("phrase not found");
  });
  it("a premise with parts of its own, a case split and a filter quantifier draw as cards under a word for what they are", () => {
    const v = view("theorem t (n : ℕ) : ((A n → B n) ∧ C n) → (∀ᵐ o ∂μ, 0 < f o ∧ f o ≤ 1) ∧ (if n = 0 then D else E n) ∧ (match k with | .a => F | .b => G) := by sorry");
    const html = drawer({}).draw(v, { linked: false });
    const count = (re: RegExp) => (html.match(re) ?? []).length;
    expect(count(/<div/g)).toBe(count(/<\/div>/g));
    expect(html).toContain(`<div class="ds-prem"><span class="ds-chip ds-chip-hyp" title="a hypothesis that states a claim of its own: its parts follow">assume</span><div class="ds-subs"><div class="ds-sub"><div class="ds-rows"><div class="srow ds-row ds-row-hyp" data-binder=""><span class="ds-chip ds-chip-hyp" title="hypothesis">assume</span><div class="ds-code">A n</div></div></div>`);
    expect([...html.matchAll(/<span class="ds-chip ds-chip-intro" title="[^"]*">([^<]*)<\/span>([^<]*)/g)].map((m) => `${m[1]}: ${m[2]}`)).toEqual([
      "for almost every: ∀ᵐ o ∂μ,", "if: if n = 0 then", "otherwise: else", "by cases: match k with", "case: | .a =&gt;", "case: | .b =&gt;",
    ]);
  });
  /** The drawer read down: each label, and each line as `word | text`. */
  const read = (source: string, defs = false) => {
    const html = drawer({}).draw(defs ? (propDeclView(source)!.view as PageView) : view(source));
    return [...html.matchAll(/<div class="ds-label[^>]*>([^<]*)<\/div>|<span class="ds-chip[^>]*title="([^"]*)">([^<]*)<\/span>(?:<div class="ds-code">)?([^<]*)/g)]
      .map((m) => (m[1] !== undefined ? `[${m[1]}]` : `${m[3]} | ${m[4].replace(/&lt;/g, "<").replace(/\s+/g, " ").trim()}`));
  };
  // The findings: every conjunct of a conclusion read "then"; the claims under an `∃` read "and" from the first
  // (or "then", each); `(A ∧ B) ∨ (C → D)` drew `D` as "and".
  it("of the claims side by side only the first reads \"then\"; the first after an ∃ \"such that\"; a part with hypotheses \"assume … then\"", () => {
    expect(read("theorem t (x : ℕ) : A x ∧ B x ∧ (C x → D x ∧ E x) := sorry")).toEqual([
      "[Hypotheses]", "given | (x : ℕ)", "[Conclusion 1]", "then | A x", "[Conclusion 2]", "and | B x", "[Conclusion 3]", "assume | C x", "then | D x", "and | E x",
    ]);
    expect(read("theorem t : ∀ n : ℕ, 0 < n → P n ∧ Q n ∧ R n := sorry").filter((l) => !l.startsWith("[")).slice(-3)).toEqual(["then | P n", "and | Q n", "and | R n"]);
    expect(read("theorem t : ∃ δ : ℝ, A δ ∧ B δ ∧ C δ := sorry")).toEqual([
      "[Conclusion 1]", "such that | A δ", "[Conclusion 2]", "and | B δ", "[Conclusion 3]", "and | C δ",
    ]);
    // nested, and under a `∀` (a `∀` row and an `∃ …,` line read as they stand, with no word; an `∃` over one claim stays one line)
    expect(read("theorem t : ∀ ε : ℝ, 0 < ε → (∃ δ : ℝ, P δ ε ∧ ∃ N : ℕ, Q N δ ∧ R N) ∧ ∃ M : ℕ, S M ε := sorry")).toEqual([
      "[Hypotheses]", "assume | 0 < ε",
      "[Conclusion 1]", "such that | P δ ε", "such that | Q N δ", "and | R N",
      "[Conclusion 2]", "and | ∃ M : ℕ, S M ε",
    ]);
    // in a hypothesis: after its `∃`, "such that" then "and"; its parts otherwise "and", one with hypotheses "assume … then"
    expect(read("theorem t (h : ∃ δ : ℝ, A δ ∧ B δ ∧ C δ) (g : A ∧ (B → C ∧ D) ∧ E) : F := sorry").slice(1, -1)).toEqual([
      "assume | (h : ∃ δ : ℝ,", "such that | A δ", "and | B δ", "and | C δ",
      "assume | (g :", "and | A", "assume | B", "then | C", "and | D", "and | E",
    ]);
    expect(read("theorem t : (A ∧ B) ∨ (C → D) := sorry")).toEqual(["[Conclusion 1]", "[either]", "and | A", "and | B", "[or]", "assume | C", "then | D"]);
    // every word has a tooltip in plain words; the clauses of a condition (a `def … : Prop`, a record's fields) read "then", then "and"
    const html = drawer({}).draw(view("theorem t : ∃ δ : ℝ, A δ ∧ B δ := sorry"));
    expect([...html.matchAll(/title="([^"]*)">(such that|and)</g)].map((m) => `${m[2]}: ${m[1]}`)).toEqual(["such that: what holds of the names just introduced", "and: one more claim, alongside the one above"]);
    expect(read("def Good (n : ℕ) : Prop :=\n  A n ∧ B n ∧ ∃ m : ℕ, C m ∧ D m", true).filter((l) => !l.startsWith("["))).toEqual([
      "given | (n : ℕ)", "def | Good n : Prop", "then | A n", "and | B n", "such that | C m", "and | D m",
    ]);
  });
  // The finding: `(hcov : A ∧ B ∧ C)` drew a head line `(hcov :` that was asked, linked and tagged like a row.
  it("a hypothesis's bare name is a label of its parts: it carries no phrase and no tag, and links written when it was a row still place", () => {
    const source = "theorem t (n : ℕ) (hcov : A n ∧ B n ∧ C n) : D n := by\n  sorry";
    const v = view(source);
    const now = viewRows(v as never);
    expect(now.map((r) => r.id)).toEqual(["r1", "r2", "r3", "r4", "r5"]);
    expect(applyLinks(v, now.map((r) => ({ ...r, segments: [`s${r.id.slice(1)}`], unstated: false })), v.key)).toBe(true);
    const html = drawer({}).draw(v);
    expect(html).toContain(`<div class="srow ds-row ds-row-hyp ds-head" data-binder=""><span class="ds-chip ds-chip-hyp" title="a hypothesis that states a claim of its own: its parts follow">assume</span><div class="ds-code">(hcov :</div></div>`);
    expect([...html.matchAll(/data-binder="([^"]*)"/g)].map((m) => m[1])).toEqual(["s1", "", "s2", "s3", "s4", "s5"]);
    expect(html).not.toContain("not linked yet");
    // the links of the cut that had the row `hcov : ` (same statement, same key): each part keeps its own
    const old = view(source);
    const was = [{ id: "r1", names: "n", lean: "ℕ", segments: ["s1"] }, { id: "r2", names: "hcov", lean: "", segments: ["s9"] }, ...["A n", "B n", "C n", "D n"].map((lean, k) => ({ id: `r${k + 3}`, lean, segments: [`s${k + 2}`] }))];
    expect(applyLinks(old, was, old.key)).toBe(true);
    expect(marks(old)).toEqual(["(n : ℕ) | s1", "A n | s2", "B n | s3", "C n | s4", "D n | s5"]);
  });
  it("the flat rows of a statement that does not structure name no ⊢", () => {
    const flat = js.slice(js.indexOf("const rowHTML = (row)"), js.indexOf("// the statement as it now stands"));
    expect(flat).toContain(`title="what the result concludes">then</span>`);
    expect(flat).not.toMatch(/title="[^"]*(?:⊢|row\.id)/);
  });
});

describe("a name is resolved as Lean resolves it: in the namespaces enclosing its use, then those opened", () => {
  const root = mkdtempSync(path.join(tmpdir(), "tc-ns-"));
  const lean = path.join(root, "Papers", "Demo");
  mkdirSync(lean, { recursive: true });
  const text = [
    "theorem part : RootStatement := by", "  sorry", "",
    "namespace Papers.Demo.Inner", "",
    "theorem part (h : InnerHyp) : InnerStatement := by", "  sorry", "",
    "theorem both : (type_of% @part) ∧ Extra := by", "  sorry", "",
    "theorem rooted : (type_of% @_root_.part) ∧ Extra := by", "  sorry", "",
    "end Papers.Demo.Inner", "",
    "namespace Other", "theorem lonely : OtherStatement := by", "  sorry", "end Other", "",
    "namespace Papers.Demo",
    "theorem uses : (type_of% @lonely) ∧ Extra := by", "  sorry", "",
    "theorem qualified : (type_of% @Other.lonely) ∧ Extra := by", "  sorry", "",
    "section", "open Other", "theorem opened : (type_of% @lonely) ∧ Extra := by", "  sorry", "end", "",
    "theorem closed : (type_of% @lonely) ∧ Extra := by", "  sorry", "",
    "def Good : Prop := RootGood", "namespace Deep", "def Good : Prop := DeepGood", "theorem g (h : Good) : Good ∧ Extra := by", "  sorry", "end Deep", "end Papers.Demo", "",
  ].join("\n");
  writeFileSync(path.join(lean, "T.lean"), text);
  const first = async (name: string) => {
    const v = view(text.slice(text.indexOf(`theorem ${name} `)).split("\n\n")[0]);
    const named = leanDefs(root, lean);
    await named.annotate(v, "T.lean", name);
    return { card: v.conclusions[0], v, named };
  };

  it("parseFileDecls: each declaration with its namespace, the namespaces searched from it, and those open there", () => {
    const by = new Map(parseFileDecls(text).decls.map((d) => [`${d.ns}|${d.name}`, d]));
    expect(by.get("Papers.Demo.Inner|both")).toMatchObject({ line: 9, scopes: ["Papers.Demo.Inner", "Papers.Demo", "Papers", ""], opened: [] });
    expect(by.get("Papers.Demo|opened")!.opened).toEqual(["Papers.Demo.Other", "Papers.Other", "Other"]);
    expect(by.get("Papers.Demo|closed")!.opened).toEqual([]);
    expect(by.get("|part")).toMatchObject({ line: 1, scopes: [""] });
  });
  it("`type_of% @name` opens the innermost theorem of that name — never one whose namespace is not open", async () => {
    expect((await first("both")).card.of).toMatchObject({ name: "part", line: 6 });
    expect((await first("rooted")).card.of).toMatchObject({ name: "part", line: 1 });
    // `lonely` lives in `Other`, which is not open where `uses` stands: Lean would not find it, nor does the page
    expect((await first("uses")).card).toMatchObject({ code: "type_of% @lonely" });
    expect((await first("closed")).card).toMatchObject({ code: "type_of% @lonely" });
    expect((await first("qualified")).card.of).toMatchObject({ name: "lonely" });
    expect((await first("opened")).card.of).toMatchObject({ name: "lonely" });
  });
  it("a row's declaration is the innermost of its name too", async () => {
    const { v, named } = await first("g");
    expect(v.sharedHyps[0].refs).toEqual(["T.lean#Good"]);
    expect(Object.values(named.defs).map((d) => d.line)).toEqual([text.split("\n").indexOf("def Good : Prop := DeepGood") + 1]);
  });
});

describe("leanDefs: a clause that is another theorem's statement (`type_of% @name`)", () => {
  const root = mkdtempSync(path.join(tmpdir(), "tc-typeof-"));
  const lean = path.join(root, "Papers", "Demo");
  mkdirSync(lean, { recursive: true });
  writeFileSync(path.join(lean, "Parts.lean"), [
    "namespace Papers.Demo", "",
    "def Good (n : ℕ) : Prop := 0 < n", "",
    "-- @node: thm:left", "/-- The left part. -/",
    "theorem left_part {n : ℕ} [Fact (0 < n)] (hn : Good n) :", "    A n ∧ (∀ (m : ℕ) (hm : m < n), B m) := by", "  sorry", "",
    "theorem right_part : ∀ (k : ℕ) (hk : Good k), C k := by", "  sorry", "",
    "theorem deep : (type_of% @left_part) ∧ D := by", "  sorry", "",
    "theorem loop_a : type_of% @loop_b := by", "  sorry", "",
    "theorem loop_b : type_of% @loop_a := by", "  sorry", "",
    ...Array.from({ length: 9 }, (_, k) => `theorem chain${k} : ${k < 8 ? `type_of% @chain${k + 1}` : "E"} := by\n  sorry\n`),
    "end Papers.Demo", "",
  ].join("\n"));
  const BOTH = "theorem both : (type_of% @left_part) ∧ (type_of% @missing_part) ∧ (type_of% @Papers.Demo.right_part) ∧ (type_of% @deep) := by\n  sorry";
  writeFileSync(path.join(lean, "T.lean"), `import Papers.Demo.Parts\n\nnamespace Papers.Demo\n\n${BOTH}\n\ntheorem t_loop : type_of% @loop_a := by sorry\n\ntheorem t_chain : type_of% @chain0 := by sorry\n\nend Papers.Demo\n`);
  const lines = (v: PageView) => {
    const out: string[] = [];
    const row = (r: PageRow | PageCard, text: string, d: number) => out.push(`${"  ".repeat(d)}${text} | ${r.xl ?? ""}${r.coarse ? " ~" : ""}`);
    const walk = (c: PageCard, d: number) => {
      if (c.of) row(c, `of ${c.of.name}`, d);
      c.hyps.forEach((h) => row(h, h.code, d));
      if (c.intro ?? c.code) row(c, (c.intro ?? c.code)!, d);
      (c.sub ?? []).forEach((s) => walk(s, d + 1));
    };
    v.sharedHyps.forEach((h) => row(h, h.code, 0));
    v.conclusions.forEach((c) => walk(c, 0));
    return out;
  };
  const expanded = async (source: string, decl = "both") => {
    const v = view(source);
    const named = leanDefs(root, lean);
    await named.annotate(v, "T.lean", decl);
    return { v, named };
  };

  // The finding this guards: the page drew 153 rows of the named theorems with no id, while F5 was
  // offered the two `type_of%` lines — so none of them could ever be linked.
  it("puts the theorem's statement in the clause as rows of this statement, each with an id under the clause's — the rows F5 is asked", async () => {
    const { v, named } = await expanded(BOTH);
    const ids: string[] = [];
    eachRow(v, (r) => ids.push(r.id!));
    expect(ids).toEqual([
      "r1/r1", "r1/r2", "r1/r3", "r1/r4", "r1/r5", "r1/r6", "r1/r7", "r2", "r3/r1", "r3/r2", "r3/r3",
      "r4/r1/r1", "r4/r1/r2", "r4/r1/r3", "r4/r1/r4", "r4/r1/r5", "r4/r1/r6", "r4/r1/r7", "r4/r2",
    ]);
    const scopes = leanScopes({ toolkitRoot: root, leanDir: lean, read: async (abs) => readFileSync(abs, "utf8") });
    const asked = (await statementRows(BOTH, { file: "T.lean", decl: "Papers.Demo.both", lean: scopes }))!;
    expect(asked.rows.map((r) => r.id)).toEqual(ids);
    expect(asked.key).toBe(v.key);
    // links F5 wrote for those rows land on them, one by one
    expect(applyLinks(v, asked.rows.map((r) => ({ ...r, segments: [`s-${r.id}`], unstated: false })), asked.key)).toBe(true);
    expect(lines(v)).toEqual([
      "of left_part | ",
      "{n : ℕ} | s-r1/r1", "[Fact (0 < n)] | s-r1/r2", "(hn : Good n) | s-r1/r3",
      "  A n | s-r1/r4",
      "  (m : ℕ) | s-r1/r5", "  (hm : m < n) | s-r1/r6", "  B m | s-r1/r7",
      "type_of% @missing_part | s-r2",
      "of right_part | ",
      "(k : ℕ) | s-r3/r1", "(hk : Good k) | s-r3/r2",
      "  C k | s-r3/r3",
      // a statement that itself names one opens the same way
      "of deep | ",
      "  of left_part | ",
      "  {n : ℕ} | s-r4/r1/r1", "  [Fact (0 < n)] | s-r4/r1/r2", "  (hn : Good n) | s-r4/r1/r3",
      "    A n | s-r4/r1/r4",
      "    (m : ℕ) | s-r4/r1/r5", "    (hm : m < n) | s-r4/r1/r6", "    B m | s-r4/r1/r7",
      "  D | s-r4/r2",
    ]);
    const left = v.conclusions[0];
    expect(left).toMatchObject({ id: "r1", of: { name: "left_part", kind: "theorem", file: "Parts.lean", line: 7, node: "thm:left", written: "type_of% @left_part" } });
    expect("code" in left).toBe(false);
    expect(left.hyps.map((h) => h.chip)).toEqual(["decl", "decl", "hyp"]);
    expect(v.conclusions[2].of).toEqual({ name: "right_part", kind: "theorem", file: "Parts.lean", line: 11, written: "type_of% @Papers.Demo.right_part" });
    // its rows name the paper's Prop definitions like any other row; a theorem is no definition to fold
    expect(left.hyps[2].refs).toEqual(["Parts.lean#Good"]);
    expect(Object.keys(named.defs)).toEqual(["Parts.lean#Good"]);
  });
  it("links written for the clauses as one row each reach the opened rows as the clause's, coarse", async () => {
    const { v } = await expanded(BOTH);
    expect(applyLinks(v, stored(BOTH, (id) => [`s${id.slice(1)}`]))).toBe(true);
    expect(lines(v).filter((l) => !l.includes("s4"))).toEqual([
      "of left_part | s1",
      "{n : ℕ} | s1 ~", "[Fact (0 < n)] | s1 ~", "(hn : Good n) | s1 ~", "  A n | s1 ~", "  (m : ℕ) | s1 ~", "  (hm : m < n) | s1 ~", "  B m | s1 ~",
      "type_of% @missing_part | s2",
      "of right_part | s3", "(k : ℕ) | s3 ~", "(hk : Good k) | s3 ~", "  C k | s3 ~",
      // the line naming a theorem opened inside another is no row
      "  of left_part | ",
    ]);
    expect(lines(v).filter((l) => l.endsWith("| s4 ~"))).toHaveLength(8);
    expect(lines(v)).toContain("of deep | s4");
  });
  it("a cycle ends where it closes and a chain at the depth cap, the rest as written", async () => {
    const loop = (await expanded("theorem t_loop : type_of% @loop_a := by sorry", "t_loop")).v;
    expect(lines(loop)).toEqual(["of loop_a | ", "  of loop_b | ", "    type_of% @loop_a | "]);
    const chain = (await expanded("theorem t_chain : type_of% @chain0 := by sorry", "t_chain")).v;
    expect(lines(chain).map((l) => l.trim())).toEqual(["of chain0 |", "of chain1 |", "of chain2 |", "of chain3 |", "of chain4 |", "of chain5 |", "type_of% @chain6 |"]);
  });
  it("the drawer draws one line per row of the opened statement, each a carrier of its own phrases; a linked result is offered", async () => {
    const js = readFileSync(path.join(__dirname, "..", "..", "src", "ui", "static", "app.js"), "utf8").replace(/\r\n/g, "\n");
    const section = js.slice(js.indexOf("const DS_TERMS"), js.indexOf("// a fold is drawn when first opened"));
    const { v, named } = await expanded(BOTH);
    applyLinks(v, viewRows(v as never).map((r) => ({ ...r, segments: [`s${r.id.replace(/\W/g, "")}`], unstated: false })), v.key);
    const results: Record<string, unknown> = {};
    const ctx = vm.createContext({
      esc: (s: unknown) => String(s ?? "").replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c]!),
      P: { detail: { leanDefs: named.defs }, folds: new Set<string>() },
      plOf: () => null, resultById: (id: string) => results[id] ?? null, envOf: () => ({ heading: "Theorem 2" }),
    });
    vm.runInContext(`${section}\nglobalThis.draw = (v) => dsViewHTML(v, { terms: DS_TERMS.theorem, linked: true, path: "", depth: 0, n: { k: 0 } });`, ctx);
    const draw = (ctx as unknown as { draw: (v: PageView) => string }).draw;
    const html = draw(v);
    const count = (re: RegExp) => (html.match(re) ?? []).length;
    expect(count(/<div/g)).toBe(count(/<\/div>/g));
    // one line per row, in reading order, and nothing but lines carries phrases
    const carriers = [...html.matchAll(/<div class="srow ([^"]*)" data-binder="([^"]*)"/g)].map((m) => `${m[1].split(" ")[0]}:${m[2]}`);
    expect(carriers).toEqual(lines(v).map((l) => `${l.trim().startsWith("of ") ? "ds-of" : /^[({[]/.test(l.trim()) ? "ds-row" : "ds-concl"}:${l.split(" | ")[1]}`));
    expect(count(/data-binder=/g)).toBe(carriers.length);
    expect(html).toContain(`<div class="ds-card"><div class="ds-label">Conclusion 1</div><div class="srow ds-of" data-binder=""><span>the statement of</span><span class="ds-fold-kind">theorem</span><code>left_part</code><span class="ds-fold-at">Parts.lean:7</span></div><div class="ds-rows"><div class="srow ds-row ds-row-decl" data-binder="sr1r1"><span class="ds-chip ds-chip-decl" title="binder">given</span><div class="ds-code">{n : ℕ}</div></div>`);
    expect(html).toContain(`<span class="ds-chip ds-chip-concl" title="one more claim, alongside the one above">and</span><div class="ds-code">type_of% @missing_part</div>`);
    // the line naming the theorem is no row: it is never called unlinked
    expect(html).not.toMatch(/data-umbgo|rtag/);
    // the theorem is itself a result of the paper with links of its own: the line says so and leads there
    results["thm:left"] = { id: "thm:left", segments: [{ id: "s1", text: "…" }] };
    expect(draw(v).match(/<button type="button" class="linkbtn" data-umbgo="thm:left"[^>]*>→ Theorem 2<\/button>/g)).toHaveLength(2);
    // a row of a linked statement with neither a phrase nor the links' word that the paper leaves it out says so
    const bare = view(BOTH);
    expect(draw(bare).match(/<span class="rtag">not linked yet<\/span>/g)).toHaveLength(4);
  });
});
