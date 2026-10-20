// Round-B MOVE without lake: declaration spans, scope-aware reference rewriting, the move plan
// (target module, paper rewrite, imports), and applyMoveItem's gate / rollback with mocked commands.
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { applyMoveItem, verifyKeptMove, lineScopes, moveAxiomsFailure, neededContext, planMove, rewriteReferences, type MovePlanInput, rootedOpens } from "../../src/proposals/move.js";
import { realApplyDeps, type ApplyDeps } from "../../src/proposals/gate.js";
import { declarationSpans } from "../../src/toolkit/lean_source.js";
import { loadLedger } from "../../src/toolkit/ledger.js";
import { writeSkeleton } from "../toolkit/helpers.js";
import { PAPER_MAIN } from "./helpers.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});


describe("an `open` carried into a toolkit namespace", () => {
  it("is rooted when the toolkit namespace has a component of the same name, and otherwise untouched", () => {
    const ns = "Toolkit.Foundations.MeasureTheory.Integral";
    expect(rootedOpens(["open MeasureTheory ProbabilityTheory", "open scoped Topology ENNReal", "open Filter in", "universe u"], ns))
      .toEqual(["open _root_.MeasureTheory ProbabilityTheory", "open scoped Topology ENNReal", "open Filter in", "universe u"]);
    expect(rootedOpens(["open scoped Topology", "open MeasureTheory.Measure"], "Toolkit.Foundations.Topology.MeasureTheory"))
      .toEqual(["open scoped _root_.Topology", "open _root_.MeasureTheory.Measure"]);
    expect(rootedOpens(["open MeasureTheory"], "Toolkit.Foundations.Probability.Conditioning")).toEqual(["open MeasureTheory"]);
  });
});

describe("declarationSpans", () => {
  it("finds each declaration with its doc comment, attributes, `open … in` and column-0 equations", () => {
    const spans = declarationSpans(PAPER_MAIN);
    expect(spans.map((s) => s.name)).toEqual([
      "Papers.Fix.twice", "Papers.Fix.twice_eq_two_mul", "Papers.Fix.uses_k", "Papers.Fix.sq_le_sq_of_le", "Papers.Fix.f", "Papers.Fix.main_result",
    ]);
    const text = (n: string) => { const s = spans.find((x) => x.name === n)!; return PAPER_MAIN.slice(s.from, s.to); };
    expect(text("Papers.Fix.twice_eq_two_mul")).toMatch(/^\/-- Adding[\s\S]*@\[simp\]\ntheorem twice_eq_two_mul[\s\S]*ring\n$/);
    expect(text("Papers.Fix.sq_le_sq_of_le")).toMatch(/^open Finset in\ntheorem sq_le_sq_of_le/);
    expect(text("Papers.Fix.f")).toContain("| n + 1 => twice (f n)");
    const s = spans.find((x) => x.name === "Papers.Fix.twice")!;
    expect(s.context).toEqual(["open Nat", "variable (k : ℕ) {m : ℕ} (P : Papers.Fix.Setup)"]);
    expect(s.namespaces).toEqual(["Papers.Fix"]);
  });
});

describe("rewriteReferences", () => {
  it("rewrites what resolves to a moved name at the use site, keeping field access and comments", () => {
    const text = "namespace Papers.Fix\n-- twice here\ntheorem x : twice 1 = Fix.twice 1 := (twice_eq 1).trans twice.foo\nend Papers.Fix\ntheorem y : Papers.Fix.twice 1 = 2 := rfl\ntheorem z : twice 2 = 4 := rfl\n";
    const r = rewriteReferences(text, new Map([["Papers.Fix.twice", "T.twice"]]));
    expect(r.text).toContain("-- twice here");
    expect(r.text).toContain("theorem x : T.twice 1 = T.twice 1 := (twice_eq 1).trans T.twice.foo");
    expect(r.text).toContain("theorem y : T.twice 1 = 2");
    // Outside the namespace a bare `twice` does not denote Papers.Fix.twice.
    expect(r.text).toContain("theorem z : twice 2 = 4");
    expect(lineScopes("open A B in\ntheorem t : x := y\ntheorem u : x := y\n")[1]!.opens).toEqual(["A", "B"]);
  });
});

describe("neededContext", () => {
  it("with the source files' opens kept (no minimal header), an open of a toolkit namespace stays only when the block uses it (live Li–Ding: unknown namespace)", () => {
    const ctx = ["open Filter MeasureTheory", "open Toolkit.Foundations.Design"];
    const text = ["lemma t (V : Matrix (Fin K) (Fin K) ℝ) (hV : V.PosSemidef) : 0 ≤ V c c := hV.diag_nonneg"];
    const own = { lib: "Toolkit", used: [{ name: "Matrix.PosSemidef" }] };
    expect(neededContext(ctx, text, "Papers", undefined, own)).toEqual(["open Filter MeasureTheory"]);
    const uses = { lib: "Toolkit", used: [{ name: "Toolkit.Foundations.Design.finitePopulationCov" }] };
    expect(neededContext(ctx, ["lemma u : finitePopulationCov y z = 0 := sorry"], "Papers", undefined, uses)).toEqual(ctx);
  });

  it("keeps only the variables the moved text mentions and drops opens of paper namespaces", () => {
    const ctx = ["open Nat Papers.Fix", "variable (k : ℕ) {m : ℕ} [Fact (0 < m)] (P : Papers.Fix.Setup)", "set_option maxHeartbeats 400000"];
    expect(neededContext(ctx, ["theorem t : m + k = k + m := by omega"], "Papers"))
      .toEqual(["open Nat", "variable (k : ℕ) {m : ℕ} [Fact (0 < m)]", "set_option maxHeartbeats 400000"]);
    expect(neededContext(ctx, ["theorem t : 1 = 1 := rfl"], "Papers")).toEqual(["open Nat", "set_option maxHeartbeats 400000"]);
  });

  // live lms: `[mΩ : MeasurableSpace Ω]` was dropped (its name never occurs), and the moved lemma's measure elaborated to `sorry`
  it("keeps a named instance binder whose class's variables are kept, as an anonymous one; drops it with them", () => {
    const ctx = ["variable (G : Papers.Fix.Game) {Ω : Type*} [mΩ : MeasurableSpace Ω]"];
    expect(neededContext(ctx, ["lemma l (μ : Measure Ω) (f : Ω → ℝ) : μ.real {ω | f ω ≤ 0} ≤ 1 := sorry"], "Papers")).toEqual(["variable {Ω : Type*} [mΩ : MeasurableSpace Ω]"]);
    expect(neededContext(ctx, ["lemma l (x : ℝ) : x ≤ x := le_rfl"], "Papers")).toEqual([]);
  });

  it("decides over every `variable` command at once, to a fixpoint: Lean's own inclusion rule", () => {
    const meas = "lemma l (μ : Measure Ω) : μ Set.univ = μ Set.univ := rfl";
    // the instance on its own line follows its variable from the line before
    expect(neededContext(["variable {Ω : Type*}", "variable [mΩ : MeasurableSpace Ω]"], [meas], "Papers")).toEqual(["variable {Ω : Type*}", "variable [mΩ : MeasurableSpace Ω]"]);
    // a dotted use of a kept variable counts as that variable
    expect(neededContext(["variable (G : Game) [IsProbabilityMeasure G.μ]"], ["lemma l : G.μ Set.univ = 1 := measure_univ"], "Papers")).toEqual(["variable (G : Game) [IsProbabilityMeasure G.μ]"]);
    // an anonymous instance with a typed binder inside binds no name, and does not hide a named one
    expect(neededContext(["variable {m : ℕ} [Fact ((m : ℕ) < 5)] [hm : Fact (0 < m)]"], ["lemma l : m = m := rfl"], "Papers")).toEqual(["variable {m : ℕ} [Fact ((m : ℕ) < 5)] [hm : Fact (0 < m)]"]);
    // a kept binder's type brings its variables
    expect(neededContext(["variable {α : Type*} (x : α)"], ["lemma l : x = x := rfl"], "Papers")).toEqual(["variable {α : Type*} (x : α)"]);
  });
});

function input(root: string, over: Partial<MovePlanInput> = {}): MovePlanInput {
  const main = path.join(root, "Papers", "Fix", "Main.lean");
  return {
    cfg: { lib: "Toolkit", papersLib: "Papers", toolkitRoot: root },
    paperFiles: new Map([[main, PAPER_MAIN]]),
    decls: [
      { from: "Papers.Fix.twice", to: "Toolkit.Tricks.Arith.twice", kind: "def" },
      { from: "Papers.Fix.twice_eq_two_mul", to: "Toolkit.Tricks.Arith.twice_eq_two_mul'", kind: "theorem" },
    ],
    mainFrom: "Papers.Fix.twice_eq_two_mul",
    docstringOverride: null,
    fallbackDocstring: "unused",
    target: { rel: "Toolkit/Tricks/Arith/Doubling.lean", module: "Toolkit.Tricks.Arith.Doubling", division: "Tricks", overview: "Doubling.", existingText: null },
    alreadyMoved: new Map(),
    toolkitModulesUsed: [],
    readModule: () => null,
    ...over,
  };
}

describe("planMove", () => {
  it("creates the target module and rewires the paper", () => {
    const root = "/tk";
    const plan = planMove(input(root));
    const target = plan.writes.get(path.join(root, "Toolkit", "Tricks", "Arith", "Doubling.lean"))!;
    expect(plan.created).toBe(true);
    expect(target).toBe([
      "module", "", "public import Mathlib.Tactic.Ring", "", "/-!", "# Toolkit.Tricks.Arith.Doubling", "", "Doubling.", "-/", "",
      "@[expose] public section", "",
      "namespace Toolkit.Tricks.Arith", "", "@[expose] section", "", "open Nat", "",
      "/-- The sum of a number with itself. -/", "def twice (n : ℕ) : ℕ := n + n", "",
      "/-- Adding a number to itself is multiplying it by two. -/", "@[simp]", "theorem twice_eq_two_mul' (n : ℕ) : twice n = 2 * n := by", "  unfold twice; ring", "",
      "end", "", "end Toolkit.Tricks.Arith", "",
    ].join("\n"));
    const paper = plan.writes.get(path.join(root, "Papers", "Fix", "Main.lean"))!;
    expect(paper).toContain("public import Mathlib.Tactic.Ring\npublic import Toolkit.Tricks.Arith.Doubling\n");
    expect(paper).not.toContain("def twice");
    expect(paper).not.toContain("theorem twice_eq_two_mul");
    expect(paper).toContain("| n + 1 => Toolkit.Tricks.Arith.twice (f n)");
    expect(paper).toContain("theorem main_result {a b : ℕ} (h : a ≤ b) : Toolkit.Tricks.Arith.twice (a * a) ≤ 2 * (b * b) := by\n  rw [Toolkit.Tricks.Arith.twice_eq_two_mul']");
    expect(paper).not.toMatch(/\n\n\n/);
  });

  it("appends to an existing module: missing imports only, `@[expose]` blanket for a definition, edited docstring", () => {
    const existing = "module\n\npublic import Mathlib.Order.Basic\n\n/-!\n# Doubling\n\nX.\n-/\n\npublic section\n\ntheorem old : True := trivial\n";
    const plan = planMove(input("/tk", {
      target: { rel: "Toolkit/Tricks/Arith/Doubling.lean", module: "Toolkit.Tricks.Arith.Doubling", division: "Tricks", overview: null, existingText: existing },
      docstringOverride: "Twice is two times.",
      toolkitModulesUsed: ["Toolkit.Foundations.A.B"],
    }));
    const t = plan.writes.get(plan.targetAbs)!;
    expect(plan.importsAdded).toEqual(["Mathlib.Tactic.Ring", "Toolkit.Foundations.A.B"]);
    expect(t.startsWith("module\n\npublic import Mathlib.Order.Basic\npublic import Mathlib.Tactic.Ring\npublic import Toolkit.Foundations.A.B\n")).toBe(true);
    expect(t).toContain("@[expose] public section\n\ntheorem old : True := trivial\n\nnamespace Toolkit.Tricks.Arith");
    expect(t).toContain("/-- Twice is two times. -/\n@[simp]\ntheorem twice_eq_two_mul'");
  });

  it("refuses a declaration it cannot find, and a closure outside the proposed namespace", () => {
    expect(() => planMove(input("/tk", { decls: [{ from: "Papers.Fix.nope", to: "T.nope", kind: "theorem" }], mainFrom: "Papers.Fix.nope" }))).toThrow(/cannot find the declaration Papers\.Fix\.nope/);
    expect(() => planMove(input("/tk", { decls: [{ from: "Papers.Fix.twice", to: "A.twice", kind: "def" }, { from: "Papers.Fix.twice_eq_two_mul", to: "B.t", kind: "theorem" }] }))).toThrow(/not in the namespace B/);
  });

  it("imports what a dropped paper import brought in", () => {
    const main = path.join("/tk", "Papers", "Fix", "Main.lean");
    const text = PAPER_MAIN.replace("public import Mathlib.Tactic.Ring", "public import Papers.Fix.Defs");
    const plan = planMove(input("/tk", {
      paperFiles: new Map([[main, text]]),
      readModule: (m) => (m === "Papers.Fix.Defs" ? "module\n\npublic import Mathlib.Data.Real.Basic\npublic import Toolkit.Tricks.X.Y\n" : null),
    }));
    expect(plan.writes.get(plan.targetAbs)).toContain("module\n\npublic import Mathlib.Data.Real.Basic\n\n/-!");
  });
});

// ─── applyMoveItem ─────────────────────────────────────────────────────────

async function moveFixture(runLog: string[], failAt: string | null) {
  const root = await mkdtemp(path.join(os.tmpdir(), "move-"));
  tmp.push(root);
  const cfg = await writeSkeleton(root);
  const main = path.join(root, "Papers", "Fix", "Main.lean");
  await mkdir(path.dirname(main), { recursive: true });
  await writeFile(main, PAPER_MAIN);
  const plan = planMove(input(root));
  const d: ApplyDeps = {
    ...realApplyDeps,
    run: async (cmd) => {
      runLog.push(cmd);
      if (failAt && cmd.includes(failAt)) return { code: 1, log: `error: ${failAt} failed` };
      if (cmd.startsWith("lake env lean")) {
        const probe = await readFile(cmd.slice("lake env lean ".length), "utf8");
        const names = [...probe.matchAll(/#print axioms (\S+)/g)].map((m) => m[1]);
        return { code: 0, log: names.map((n) => `'${n}' depends on axioms: [propext]`).join("\n") };
      }
      if (cmd.includes("toolkit_index")) await writeFile(cfg.indexPath, "{\"entries\":[]}");
      return { code: 0, log: "ok" };
    },
  };
  const args = {
    cfg, toolsDir: "/tools", slug: "fix", proposalId: "b-twice-eq-two-mul", paperModule: "Papers.Fix", plan,
    target: input(root).target, decls: input(root).decls, headlineBaseline: new Map([["Papers.Fix.main_result", ["propext"]]]),
    ledgerEntries: input(root).decls.map((x) => ({
      name: x.to, module: "Toolkit.Tricks.Arith.Doubling", division: "Tricks",
      origin: { kind: "proposal" as const, slug: "fix", round: "B", proposal_id: "b-twice-eq-two-mul" }, date: "2026-09-23", decision: "accepted", used_by: ["fix"],
    })),
    journalFile: path.join(root, "runs", "fix", "proposals", "move_journal.json"),
    probeFile: path.join(root, "runs", "fix", "proposals", "move_axioms.lean"),
    indexStep: { label: "toolkit index", cmd: "lake exe toolkit_index", cwd: root },
  };
  await mkdir(path.dirname(args.journalFile), { recursive: true });
  return { root, cfg, main, d, args };
}

describe("applyMoveItem", () => {
  it("writes target, barrel, paper and ledger, then runs the gate in order", async () => {
    const runLog: string[] = [];
    const { root, cfg, main, d, args } = await moveFixture(runLog, null);
    const r = await applyMoveItem(args, d);
    expect(r.ok).toBe(true);
    expect(runLog.map((c) => c.split(" ").slice(0, 3).join(" "))).toEqual([
      "lake build Toolkit", "lake build Papers.Fix", "lake env lean", "npx tsx bin/lint_module_headers.ts", "npx tsx bin/lint_toolkit_layout.ts", "lake exe toolkit_index",
    ]);
    expect(runLog[1]).toBe("lake build Papers.Fix Papers");
    expect(await readFile(path.join(root, "Toolkit", "Tricks", "Arith", "Doubling.lean"), "utf8")).toContain("def twice");
    expect(await readFile(path.join(root, "Toolkit", "Tricks.lean"), "utf8")).toContain("public import Toolkit.Tricks.Arith.Doubling");
    expect(await readFile(main, "utf8")).toContain("public import Toolkit.Tricks.Arith.Doubling");
    expect((await loadLedger(cfg.ledgerPath)).declarations.map((e) => e.name)).toEqual(["Toolkit.Tricks.Arith.twice", "Toolkit.Tricks.Arith.twice_eq_two_mul'"]);
    expect(existsSync(args.journalFile)).toBe(false);
  });

  it("a failing gate restores nothing: the files stay as written, with the originals on record, for the orchestrator", async () => {
    const runLog: string[] = [];
    const { root, cfg, main, d, args } = await moveFixture(runLog, "lake build Papers.Fix");
    const before = { main: await readFile(main, "utf8"), ledger: await readFile(cfg.ledgerPath, "utf8") };
    const r = await applyMoveItem(args, d);
    expect(r).toMatchObject({ ok: false, kept: true });
    expect(r.log).toMatch(/gate step 'lake build paper' failed; the files are left as written/);
    expect(await readFile(main, "utf8")).toContain("public import Toolkit.Tricks.Arith.Doubling");
    expect(existsSync(path.join(root, "Toolkit", "Tricks", "Arith", "Doubling.lean"))).toBe(true);
    // the journal holds what each file was, should the move be undone by hand
    const journal = JSON.parse(await readFile(args.journalFile, "utf8")) as { entries: Array<{ path: string; orig: string | null }> };
    expect(journal.entries.find((e) => e.path === main)!.orig).toBe(before.main);
    expect(journal.entries.find((e) => e.path === cfg.ledgerPath)!.orig).toBe(before.ledger);
    expect(journal.entries.find((e) => e.path.endsWith("Doubling.lean"))!.orig).toBeNull();

    // the orchestrator repairs the Lean; the gate alone, on the files as they stand, settles the move
    const ok: typeof d = { ...d, run: async (cmd, cwd) => d.run(cmd.replace("lake build Papers.Fix", "lake  build Papers.Fix"), cwd) };
    const v = await verifyKeptMove(args, ok);
    expect(v.ok).toBe(true);
    expect(existsSync(args.journalFile)).toBe(false);
    // … and while it still fails, nothing is touched
    const { d: d2, args: args2 } = await moveFixture([], "lake build Papers.Fix");
    await applyMoveItem(args2, d2);
    expect((await verifyKeptMove(args2, d2)).ok).toBe(false);
    expect(existsSync(args2.journalFile)).toBe(true);
  });

  it("a second attempt at the same move writes over the first and keeps the first originals", async () => {
    const { main, d, args } = await moveFixture([], "lake build Papers.Fix");
    const before = await readFile(main, "utf8");
    await applyMoveItem(args, d);
    const again = await applyMoveItem(args, d);
    expect(again).toMatchObject({ ok: false, kept: true });
    const journal = JSON.parse(await readFile(args.journalFile, "utf8")) as { entries: Array<{ path: string; orig: string | null }> };
    expect(journal.entries.find((e) => e.path === main)!.orig).toBe(before);
  });

  it("changed headline axioms fail the gate", () => {
    const log = "'Papers.Fix.main_result' depends on axioms: [propext, sorryAx]\n'T.x' does not depend on any axioms";
    expect(moveAxiomsFailure(log, ["T.x"], new Map([["Papers.Fix.main_result", ["propext"]]]))).toMatch(/axioms changed from \[propext\] to \[propext, sorryAx\]/);
    expect(moveAxiomsFailure("'T.x' depends on axioms: [Foo.ax]", ["T.x"], new Map())).toMatch(/T\.x depends on Foo\.ax/);
    expect(moveAxiomsFailure("'T.x' does not depend on any axioms", ["T.x"], new Map())).toBeNull();
  });

  it("refuses to write a block containing sorry", async () => {
    const runLog: string[] = [];
    const { main, d, args } = await moveFixture(runLog, null);
    const bad = new Map(args.plan.writes);
    bad.set(args.plan.targetAbs, `${bad.get(args.plan.targetAbs)!}\ntheorem h : False := sorry\n`);
    const before = await readFile(main, "utf8");
    const r = await applyMoveItem({ ...args, plan: { ...args.plan, writes: bad } }, d);
    expect(r.ok).toBe(false);
    expect(r.log).toMatch(/contains `sorry`/);
    expect(runLog).toEqual([]);
    expect(await readFile(main, "utf8")).toBe(before);
  });
});
