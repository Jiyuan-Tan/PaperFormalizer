import { mkdtemp, mkdir, rm, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import {
  buildCompleteCrosswalkFromGraph,
  buildSymbolClusters,
  crosswalkVerifiedWithoutAnchor,
  findHiddenStatementDefs,
  parseLeanDecls,
  parseRealizesTags,
  persistCrosswalk,
  renderCrosswalkMd,
  splitStatement,
  statementText,
  deriveObjId,
} from "../../src/formalization/crosswalk.js";
import type { FormalizationGraph } from "../../src/graph/types.js";
import type { CrosswalkEntry, CrosswalkVerdict } from "../../src/types.js";

// A Basic.lean mirroring the stat_ate_overlap_decay shape: a P-10 class def
// annotated with its block id in a `/-! ## P-10 — … -/` section comment, plus a
// helper def with NO block id (must be skipped), and a T-1 theorem (matched by
// name `t1_thm`). The section comment deliberately omits A4/A5/A6 clauses.
const BASIC = `import Mathlib

/-- A helper with no block id — must be skipped by the crosswalk. -/
noncomputable def overlapDen (x : Real) : Real := x + 1

/-! ## P-10 — Triangular-array weak-overlap class (build-inline)

Encodes A1, A2 and a boundary condition; A4/A5/A6 deferred to theorem hyps. -/
noncomputable def triangularClass (k b : Real) (n : Nat) : Set Real :=
  {x | 0 ≤ x}

/-- **L-7.** A lemma — excluded from the crosswalk. -/
lemma l7_aux : True := by sorry

theorem t1_thm (n : Nat) : n + 0 = n := by simp
`;

let dir: string;
let leanDir: string;

beforeEach(async () => {
  dir = await mkdtemp(path.join(os.tmpdir(), "crosswalk-"));
  leanDir = path.join(dir, "lean");
  await mkdir(leanDir, { recursive: true });
  await writeFile(path.join(leanDir, "Basic.lean"), BASIC, "utf8");
});

afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

describe("findHiddenStatementDefs", () => {
  it("BFS is not truncated by a named-argument `:=` in a hypothesis binder", async () => {
    // A theorem whose hypothesis uses Lean named-argument syntax `(𝒳 := 𝒳)`
    // BEFORE referencing the class def. A raw `indexOf(":=")` would cut the
    // statement at the named arg and never reach `hiddenClass` (and everything
    // it transitively reaches) — the bug that made the AUX hidden-def audit
    // silently cover almost nothing for `t2_thm`.
    const lean = `import Mathlib

/-- A build-inline membership predicate with no obj_id. -/
def hiddenInner (g : Real) : Prop := 0 ≤ g

/-- The class def, named in the CONCLUSION after the hypothesis named-arg. -/
def hiddenClass (k : Real) : Prop := hiddenInner k

/-- A wrapper that takes a named argument. -/
def wrap (p : Prop) : Prop := p

/-- **T-1.** -/
theorem t1_thm (n : Nat) (h : wrap (p := True)) : hiddenClass 0 := by sorry
`;
    await writeFile(path.join(leanDir, "Basic.lean"), lean, "utf8");
    const hidden = await findHiddenStatementDefs(leanDir);
    const names = hidden.map((h) => h.name);
    // The conclusion `hiddenClass 0` sits AFTER the `(p := True)` named-arg. A raw
    // first-`:=` cut would drop it (and its transitively-reached `hiddenInner`);
    // the depth-0 cut reaches both.
    expect(names).toContain("hiddenClass");
    expect(names).toContain("hiddenInner");
  });

  it("treats a typed-core @node theorem as a hidden-definition reachability seed", async () => {
    const lean = `import Mathlib

def atlasSemantics : Prop := True

structure AtlasPayload where
  exact : atlasSemantics

-- @node: thm:exact-real-atlas
theorem exactRealAtlas : Nonempty AtlasPayload := by sorry
`;
    await writeFile(path.join(leanDir, "Basic.lean"), lean, "utf8");
    const hidden = await findHiddenStatementDefs(leanDir);
    const payload = hidden.find((h) => h.name === "AtlasPayload");
    const semantics = hidden.find((h) => h.name === "atlasSemantics");
    expect(payload?.reachedFrom).toEqual(["thm:exact-real-atlas"]);
    expect(semantics?.reachedFrom).toEqual(["thm:exact-real-atlas"]);
    expect(payload?.contentHash).toMatch(/^[0-9a-f]{40}$/);
  });
});

describe("statement seeds of every typed-core statement kind", () => {
  it("a `prop:` theorem and a `lem:` lemma seed the hidden-definition scan like a `thm:`", async () => {
    // Only `thm:` (and legacy T-n) seeded the scan: a changed inline predicate under a `prop:`
    // never invalidated its cached F2.5 verdict.
    const lean = `import Mathlib

def propPredicate : Prop := True
def lemPredicate : Prop := True

-- @node: prop:a-proposition
theorem aProposition : propPredicate := by sorry

-- @node: lem:a-lemma
lemma aLemma : lemPredicate := by sorry
`;
    await writeFile(path.join(leanDir, "Basic.lean"), lean, "utf8");
    const hidden = await findHiddenStatementDefs(leanDir);
    expect(hidden.find((h) => h.name === "propPredicate")?.reachedFrom).toEqual(["prop:a-proposition"]);
    expect(hidden.find((h) => h.name === "lemPredicate")?.reachedFrom).toEqual(["lem:a-lemma"]);
    expect(deriveObjId("theorem", "aProposition", "-- @node: prop:a-proposition")).toBe("prop:a-proposition");
    expect(deriveObjId("lemma", "x", "-- @node: oeq:open-q")).toBe("oeq:open-q");
    expect(deriveObjId("def", "x", "-- @node: prop:a-proposition")).toBeNull();
  });
});

describe("buildCompleteCrosswalkFromGraph", () => {
  it("downgrades unresolved local anchors instead of writing line:null", async () => {
    const g: FormalizationGraph = {
      qid: "q",
      nodes: [{
        id: "p1",
        obj_id: "P-1",
        kind: "definition",
        provenance: "from-note",
        nl: { statement: "S", tex_anchor: "", frozen: true },
        lean: { decl_name: "MissingDecl", file: "Basic.lean" },
        review: { status: "unreviewed", passed_hash: null },
        proof: { state: "sorry", sorry_count: 0 },
      }],
      edges: [],
    };
    const rows = await buildCompleteCrosswalkFromGraph(g, leanDir);
    expect(rows[0].lean).toBeNull();
  });
});

// A scaffold mirroring the policy-regret laundering shape:
//  - `lawClass` (Prop, ∃ real constants): reached only TRANSITIVELY via the
//    conclusion def `witnessRisk`, NO obj_id → the uniform-constant trap.
//  - `witnessRisk` (Prop): named directly in the CONCLUSION → surfaced.
//  - `hypClass` (Prop): named directly as a HYPOTHESIS → covered by H.1, must NOT
//    re-surface; but its body references `hiddenSub`, reached transitively under a
//    hypothesis (a hidden over-strengthening) → `hiddenSub` MUST surface.
//  - `bundleStruct` (structure): an assumption-bundle reached from the conclusion.
//  - `scoreVal` (ℝ computational) and `unreachedClass` (Prop, reached by nobody):
//    must stay hidden.
const LAUNDER = `import Mathlib

/-- Build-inline membership predicate — NO block id, ∃ over real constants. -/
def lawClass (P : Nat) : Prop := ∃ Co co : ℝ, 0 < Co ∧ 0 < co ∧ Co + co = (P : ℝ)

/-- An ℝ-valued helper reached only via another def's body — NOT in a conclusion. -/
def helperVal (P : Nat) : ℝ := (P : ℝ)

/-- Converse conclusion predicate referencing the membership predicate. -/
def witnessRisk (P : Nat) (rate : ℝ) : Prop := lawClass P ∧ rate ≤ helperVal P

/-- A predicate hidden UNDER a hypothesis predicate (reached transitively). -/
def hiddenSub (P : Nat) : Prop := P ≠ 0

/-- A hypothesis predicate named directly in the theorem — covered by the H.1 matrix. -/
def hypClass (P : Nat) : Prop := hiddenSub P ∧ P ≤ P

/-- An assumption-bundle structure reached from the conclusion. -/
structure bundleStruct (P : Nat) : Prop where
  fieldA : P = P

/-- An ℝ-valued quantity named DIRECTLY in the conclusion — its formula is checked. -/
def scoreVal (P : Nat) : ℝ := (P : ℝ)

/-- A Prop ∃-real class reached by NO theorem — must stay hidden. -/
def unreachedClass : Prop := ∃ K : ℝ, 0 < K

theorem t2_thm (P : Nat) (h : hypClass P) :
    ∃ rate : ℝ, witnessRisk P rate ∧ scoreVal P = scoreVal P ∧ bundleStruct P := by sorry
`;

describe("hidden-statement-def augmentation (laundering surface)", () => {
  let ldir: string;
  beforeEach(async () => {
    const d = await mkdtemp(path.join(os.tmpdir(), "crosswalk-launder-"));
    ldir = path.join(d, "lean");
    await mkdir(ldir, { recursive: true });
    await writeFile(path.join(ldir, "Basic.lean"), LAUNDER, "utf8");
  });

  const hidden = async (name: string) => (await findHiddenStatementDefs(ldir)).find((h) => h.name === name);

  it("surfaces every reached statement def with its flavor", async () => {
    // lawClass is reached only transitively via the conclusion def witnessRisk (the
    // uniform-constant trap); witnessRisk, bundleStruct and scoreVal are named in it.
    expect(await hidden("lawClass")).toMatchObject({ kind: "def", flavor: "const-exist" });
    expect(await hidden("witnessRisk")).toMatchObject({ flavor: "predicate" });
    expect(await hidden("bundleStruct")).toMatchObject({ kind: "structure", flavor: "structure" });
    expect(await hidden("scoreVal")).toMatchObject({ kind: "def", flavor: "quantity" });
  });

  it("surfaces a predicate hidden TRANSITIVELY under a hypothesis, but not the direct hypothesis itself", async () => {
    // hiddenSub is reached only via hypClass's body → must surface (hidden over-strengthening risk)
    expect(await hidden("hiddenSub")).toBeDefined();
    // hypClass is named directly as a hypothesis → already in the H.1 matrix → must NOT re-surface
    expect(await hidden("hypClass")).toBeUndefined();
  });

  it("does NOT surface ℝ helpers reached only off-conclusion, or unreached defs", async () => {
    expect(await hidden("helperVal")).toBeUndefined(); // ℝ-valued, not in a conclusion
    expect(await hidden("unreachedClass")).toBeUndefined(); // reached by no theorem
  });
});

describe("persistCrosswalk + renderCrosswalkMd", () => {
  it("writes JSON + MD and the MD shows the P-10 row", async () => {
    const merged: CrosswalkEntry[] = [{
      obj_id: "P-10",
      kind: "definition",
      title: "Triangular-array weak-overlap class",
      tex: { label: "Triangular-array weak-overlap class", line_range: "" },
      lean: { file: "Basic.lean", decl: "triangularClass", decl_kind: "def", line: 9 },
      verdict: "weaker-in-Lean",
      note: "n",
    }];
    const jsonPath = path.join(dir, "cw.json");
    const md = path.join(dir, "cw.md");
    await persistCrosswalk(jsonPath, md, merged);
    const parsed = JSON.parse(await readFile(jsonPath, "utf8"));
    expect(parsed.find((e: { obj_id: string }) => e.obj_id === "P-10").verdict).toBe("weaker-in-Lean");
    const rendered = renderCrosswalkMd(merged);
    expect(rendered).toContain("P-10");
    expect(rendered).toContain("triangularClass");
    expect(rendered).toContain("weaker-in-Lean");
  });
});

describe("crosswalk anchors: a verified verdict never stands against lean:null", () => {
  const entry = (obj_id: string, verdict: CrosswalkVerdict, decl: string | null): CrosswalkEntry => ({
    obj_id,
    kind: "assumption",
    title: obj_id,
    tex: { label: `obj:${obj_id}`, line_range: "1-2" },
    lean: decl == null ? null : { file: "Basic.lean", decl, decl_kind: "def", line: 1 },
    verdict,
  });
  const node = (id: string, status: string, declName: string | null) => ({
    id, kind: "assumption", provenance: "agent-introduced",
    review: { status }, lean: { decl_name: declName, file: declName ? "Basic.lean" : null },
    nl: { statement: `${id} statement` },
  });

  it("the F5 gate flags exact/equivalent rows with no anchor, not unmatched or anchored rows", () => {
    const rows = [
      entry("P-8", "equivalent", null),
      entry("P-2", "exact", null),
      entry("P-7", "unmatched", null),
      entry("P-1", "equivalent", "ConditionalRegression"),
    ];
    expect(crosswalkVerifiedWithoutAnchor(rows).map((e) => e.obj_id)).toEqual(["P-8", "P-2"]);
  });

  it("downgrades a `matched` node with NO Lean anchor to `unmatched`", async () => {
    const graph = { nodes: [node("eps_admissible", "matched", null)], edges: [] } as unknown as FormalizationGraph;
    const rows = await buildCompleteCrosswalkFromGraph(graph);
    const row = rows.find((r) => r.obj_id === "eps_admissible")!;
    expect(row.lean).toBeNull();
    expect(row.verdict).toBe("unmatched");
    expect(crosswalkVerifiedWithoutAnchor(rows)).toEqual([]);
  });

  it("keeps `drift` on an unanchored node (a real negative verdict is not hidden)", async () => {
    const graph = { nodes: [node("x", "drift", null)], edges: [] } as unknown as FormalizationGraph;
    const rows = await buildCompleteCrosswalkFromGraph(graph);
    expect(rows.find((r) => r.obj_id === "x")!.verdict).toBe("drift");
  });
});

describe("parseLeanDecls declaration inventory", () => {
  it("detects attributed and non-theorem declarations under a public section, ignoring tmp/", async () => {
    const d = await mkdtemp(path.join(os.tmpdir(), "crosswalk-decls-"));
    try {
      await writeFile(path.join(d, "Basic.lean"), [
        "module",
        "/-! Module-style fixture. -/",
        "@[expose] public section",
        "@[simp] theorem exactRealAtlas : True := by trivial",
        "class AtlasWitness where",
        "  ok : True",
        "instance atlasWitness : AtlasWitness where",
        "  ok := trivial",
        "opaque hiddenAtlas : Prop",
        "axiom assumedAtlas : Prop",
        "theorem",
        "  multilineAtlas : True := by trivial",
        "theorem «quotedAtlas» : True := by trivial",
      ].join("\n"));
      await mkdir(path.join(d, "tmp"));
      await writeFile(path.join(d, "tmp", "Main.lean"), "theorem disposableProbe : True := by trivial");
      const names = (await parseLeanDecls(d, { includeLemmas: true })).map((decl) => decl.name);
      expect(names).toEqual(expect.arrayContaining([
        "exactRealAtlas", "AtlasWitness", "atlasWitness", "hiddenAtlas", "assumedAtlas",
        "multilineAtlas", "quotedAtlas",
      ]));
      expect(names).not.toContain("disposableProbe");
    } finally {
      await rm(d, { recursive: true, force: true });
    }
  });
});

/** `let`-bound conclusion: the first depth-0 `:=` belongs to a `let` binder, not the proof. */
const LET_CONCLUSION_DECL = `lemma finitePoissonObjective_snd_sign_of_nuisance_score
    {U I : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (q m : I → ℝ) (A : (U × ℝ) →ₗ[ℝ] (I → ℝ)) (u₀ : U)
    (hq : ∀ i, 0 < q i)
    (hNuisance : ∀ u : U,
      ∑ i, q i * A (u, 0) i * (m i - Real.exp (A (u₀, 0) i)) = 0) :
    let beta :=
      (maximizerOrZero (finitePoissonObjective q m A)).2
    let scalarScore :=
      ∑ i, q i * A (0, 1) i * (m i - Real.exp (A (u₀, 0) i))
    (beta < 0 ↔ scalarScore < 0) ∧
    (beta = 0 ↔ scalarScore = 0) ∧
    (0 < beta ↔ 0 < scalarScore) := by
  dsimp only`;

describe("statementText / splitStatement", () => {
  it.each([
    ["a let-bound conclusion", LET_CONCLUSION_DECL],
    ["a line-initial |absolute value|", "lemma abs_le (a b : ℝ) :\n    |a / b - c / d| ≤ 1 := by simp"],
    ["a := inside a comment", "theorem foo : Q -- let prose := marker\n:= by exact q"],
  ])("cuts exactly at the proof := past %s", (_label, decl) => {
    expect(statementText(decl).trimEnd()).toBe(decl.slice(0, decl.lastIndexOf(":= by")).trimEnd());
  });

  it("returns the whole decl for an equation-compiler def (no proof :=)", () => {
    // Over-inclusion is the safe direction; do NOT cut at the first `|` (absolute values).
    const decl = "def f : ℕ → ℕ\n  | 0 => 1\n  | n + 1 =>\n      let r := f n\n      r + 1";
    expect(statementText(decl)).toBe(decl);
  });

  it("reports the real conclusion, not the bare `let beta` binder head", () => {
    const { hyp, concl } = splitStatement(statementText(LET_CONCLUSION_DECL));
    expect(hyp).toContain("hNuisance");
    expect(concl).toContain("0 < beta ↔ 0 < scalarScore");
    expect(concl.trim()).not.toBe("let beta");
  });

  it("ignores colons and brackets in comments while finding the conclusion", () => {
    const split = splitStatement("theorem foo -- : ) ] }\n  (h : P) : Q");
    expect(split.hyp).toContain("(h : P)");
    expect(split.concl.trim()).toBe("Q");
  });
});

describe("parseRealizesTags (@realizes docstring parser)", () => {
  it("parses a comma list with optional clause hints (commas inside a hint stay); no tag → []", () => {
    const doc = "/-- foo.\n@realizes tau_P(contrast x = mu1 x - mu0 x, range [-2,2]), e_P, mu_0(in [-1,1]) -/";
    expect(parseRealizesTags(doc)).toEqual([
      { symbol: "tau_P", hint: "contrast x = mu1 x - mu0 x, range [-2,2]" },
      { symbol: "e_P" },
      { symbol: "mu_0", hint: "in [-1,1]" },
    ]);
    expect(parseRealizesTags("/-- a plain docstring with no tag -/")).toEqual([]);
  });

  it("parses every `; @realizes`-separated tag on one line, keeping a `;` inside a hint", () => {
    expect(parseRealizesTags("  -- @realizes T_i(Z)(product over N_i of Z_k); @realizes A(carrier; range ℝ); @realizes Z_k")).toEqual([
      { symbol: "T_i(Z)", hint: "product over N_i of Z_k" },
      { symbol: "A", hint: "carrier; range ℝ" },
      { symbol: "Z_k" },
    ]);
  });

  it.each([
    ["math delimiters", "/-- @realizes \\(Y(a)\\)(potential outcome); @realizes $d$ -/",
      [{ symbol: "Y(a)", hint: "potential outcome" }, { symbol: "d" }]],
    ["comma-indexed TeX names", "@realizes kappa_{r,a}(P)(cumulant coordinate), R^right_{m,L}(t)",
      [{ symbol: "kappa_{r,a}(P)", hint: "cumulant coordinate" }, { symbol: "R^right_{m,L}(t)" }]],
    ["unbalanced prose delimiters", "@realizes V_env(G_n,p)(range [0,∞) co-realizer: every overlap load is nonnegative)",
      [{ symbol: "V_env(G_n,p)", hint: "range [0,∞) co-realizer: every overlap load is nonnegative" }]],
  ])("keeps the symbol id intact under %s", (_label, line, expected) => {
    expect(parseRealizesTags(line)).toEqual(expected);
  });
});

describe("buildSymbolClusters (@realizes scan → per-symbol cluster)", () => {
  const clustersOf = async (lines: string[], symbols: { name: string; space?: string }[]) => {
    const d = await mkdtemp(path.join(os.tmpdir(), "clusters-"));
    try {
      await writeFile(path.join(d, "Basic.lean"), lines.join("\n"), "utf8");
      const clusters = await buildSymbolClusters(d, symbols);
      return { clusters, byName: Object.fromEntries(clusters.map((c) => [c.symbol, c.members.map((m) => m.decl)])) };
    } finally {
      await rm(d, { recursive: true, force: true });
    }
  };

  it("groups the conjunction of decls realizing each symbol; case-sensitive (pi ≠ Pi); untagged → empty", async () => {
    const { clusters, byName } = await clustersOf([
      "/-- Observation. @realizes O(carrier), A(A:Bool ↔ {0,1}), Y(carrier ℝ) -/",
      "structure Observation where",
      "  A : Bool",
      "",
      "/-- Law fields. @realizes e_P(propensity : 𝒳 → ℝ carrier), tau_P(contrast carrier) -/",
      "structure ObservedLaw where",
      "  propensity : Nat",
      "",
      "/-- @realizes e_P(propensity x ∈ Icc 0 1), tau_P(contrast = mu1 - mu0) -/",
      "def WellFormedLaw : Prop := True",
      "",
      "/-- @realizes e_P(a.s. 0 < e < 1) -/",
      "def Positivity : Prop := True",
      "",
      "/-- Binary policy. @realizes pi(𝒳→Bool) -/",
      "abbrev Policy := Nat",
      "",
      "/-- Policy class. @realizes Pi(finite-VC) -/",
      "def PolicyClassVC : Prop := True",
      "",
      "/-- a theorem that merely USES e_P but does not realize it -/",
      "theorem usesEp : True := trivial",
    ], [
      { name: "e_P", space: "X -> (0,1)" },
      { name: "tau_P", space: "X -> [-2,2]" },
      { name: "pi", space: "X -> {0,1}" },
      { name: "Pi", space: "set of (X->{0,1})" },
      { name: "mu_0", space: "X -> [-1,1]" },
    ]);
    expect(byName["e_P"]).toEqual(["ObservedLaw", "WellFormedLaw", "Positivity"]);
    expect(byName["tau_P"]).toEqual(["ObservedLaw", "WellFormedLaw"]);
    expect(byName["pi"]).toEqual(["Policy"]);
    expect(byName["Pi"]).toEqual(["PolicyClassVC"]);
    expect(byName["mu_0"]).toEqual([]);
    const ep = clusters.find((c) => c.symbol === "e_P")!;
    expect(ep.members.find((m) => m.decl === "Positivity")!.hint).toBe("a.s. 0 < e < 1");
  });

  it.each([
    ["a trailing tag under a def body", [
      "/-- Treated load. -/",
      "noncomputable def r1 (p : Nat) : Nat :=",
      "  p + 1",
      "  -- @realizes r_{ij}^1(G,p)(treated load; range [0,∞))",
      "",
      "/-- Control load. -/",
      "noncomputable def r0 (p : Nat) : Nat := p",
    ], "r_{ij}^1(G,p)", ["r1"]],
    ["a tag trailing a `variable` command", [
      "/-- Variance scale. -/",
      "noncomputable def varScale (p : Nat) : Nat :=",
      "  p * p",
      "",
      "variable (D : Nat) (p : Nat)   -- @realizes Z(assignment space)",
      "",
      "def IndepBernoulli (D : Nat) : Prop := True",
    ], "Z", ["variable@5"]],
    ["an inline tag on a structure's last field", [
      "/-- Law. -/",
      "structure ObservedLaw where",
      "  mu1 : Nat -- @realizes mu_1(carrier; [-1,1] via Bounded)",
      "",
      "",
      "/-- Overlap def. @realizes p_P(min e 1-e) -/",
      "def overlap : Nat := 0",
    ], "mu_1", ["ObservedLaw"]],
  ])("binds %s to the enclosing declaration, not the next one", async (_label, lines, symbol, expected) => {
    const { byName } = await clustersOf(lines as string[], [{ name: symbol as string }]);
    expect(byName[symbol as string]).toEqual(expected);
  });

  it("matches math-wrapped core symbols to ordinary tags without conflating case", async () => {
    const { byName } = await clustersOf([
      "/-- @realizes P(law); @realizes I_0,I_1(split); @realizes pi(policy) -/",
      "def wrappedTargets : Nat := 0",
      "/-- @realizes Pi(policy class) -/",
      "def policyClass : Nat := 0",
    ], [{ name: String.raw`\(P\)` }, { name: String.raw`\(I_0,I_1\)` }, { name: "pi" }, { name: "Pi" }]);
    expect(byName[String.raw`\(P\)`]).toEqual(["wrappedTargets"]);
    expect(byName[String.raw`\(I_0,I_1\)`]).toEqual(["wrappedTargets"]);
    expect(byName.pi).toEqual(["wrappedTargets"]);
    expect(byName.Pi).toEqual(["policyClass"]);
  });
});
