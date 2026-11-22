// Round-B MOVE without lake: declaration spans, scope-aware reference rewriting, the move plan
// (target module, paper rewrite, imports), and gateMoveBatch's writes, gate and undo with mocked commands.
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { brokenBefore, failingModules, gateMoveBatch, killedModules, gatedOthers, otherPaperModules, readBatchRecord, lineScopes, moveAxiomsFailure, neededContext, planMove, rewriteReferences, type MovePlan, type MovePlanInput, rootedOpens } from "../../src/proposals/move.js";
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

// ─── gateMoveBatch: a move's writes and its gate ────────────────────────────

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
    cfg, proposalId: "b-twice-eq-two-mul", plan,
    target: input(root).target, decls: input(root).decls, headlineBaseline: new Map([["Papers.Fix.main_result", ["propext"]]]),
    ledgerEntries: input(root).decls.map((x) => ({
      name: x.to, module: "Toolkit.Tricks.Arith.Doubling", division: "Tricks",
      origin: { kind: "proposal" as const, slug: "fix", round: "B", proposal_id: "b-twice-eq-two-mul" }, date: "2026-09-23", decision: "accepted", used_by: ["fix"],
    })),
    journalFile: path.join(root, "runs", "fix", "proposals", "move_batch_journal.json"),
    probeFile: path.join(root, "runs", "fix", "proposals", "move_axioms.lean"),
    indexStep: { label: "toolkit index", cmd: "lake exe toolkit_index", cwd: root },
  };
  await mkdir(path.dirname(args.journalFile), { recursive: true });
  return { root, cfg, main, d, args };
}
type MoveArgs = Awaited<ReturnType<typeof moveFixture>>["args"];

/** The fixture's move as a batch of its own (`gateMoveBatch`), planned as `plan`. */
const batchOf = (args: MoveArgs, plan: MovePlan = args.plan) => ({
  cfg: args.cfg, toolsDir: "/tools", journalFile: args.journalFile, probeFile: args.probeFile, indexStep: args.indexStep,
  headlineBaseline: args.headlineBaseline, invariance: [],
  moves: [{ slug: "fix", proposalId: args.proposalId, paperModule: "Papers.Fix", decls: args.decls, ledgerEntries: args.ledgerEntries, plan: async () => ({ plan, target: args.target }) }],
});

describe("gateMoveBatch", () => {
  it("writes target, barrel, paper and ledger, then runs the gate in order; passed, its journal says so", async () => {
    const runLog: string[] = [];
    const { root, cfg, main, d, args } = await moveFixture(runLog, null);
    const r = await gateMoveBatch(batchOf(args), d);
    expect(r.ok).toBe(true);
    expect(runLog.map((c) => c.split(" ").slice(0, 3).join(" "))).toEqual([
      "lake build Toolkit", "lake build Papers.Fix", "lake env lean", "npx tsx bin/lint_module_headers.ts", "npx tsx bin/lint_toolkit_layout.ts", "lake exe toolkit_index",
    ]);
    // the moving paper only: the other papers are built by the daily library check
    expect(runLog[1]).toBe("lake build Papers.Fix");
    expect(await readFile(path.join(root, "Toolkit", "Tricks", "Arith", "Doubling.lean"), "utf8")).toContain("def twice");
    expect(await readFile(path.join(root, "Toolkit", "Tricks.lean"), "utf8")).toContain("public import Toolkit.Tricks.Arith.Doubling");
    expect(await readFile(main, "utf8")).toContain("public import Toolkit.Tricks.Arith.Doubling");
    expect((await loadLedger(cfg.ledgerPath)).declarations.map((e) => e.name)).toEqual(["Toolkit.Tricks.Arith.twice", "Toolkit.Tricks.Arith.twice_eq_two_mul'"]);
    expect((await readBatchRecord(args.journalFile, d))).toMatchObject({ passed: true, moves: [{ proposal_id: "b-twice-eq-two-mul", module: "Toolkit.Tricks.Arith.Doubling" }] });
  });

  it("a failing gate undoes the batch: every file as it was, the ledger's declarations removed, the journal dropped", async () => {
    const runLog: string[] = [];
    const { root, cfg, main, d, args } = await moveFixture(runLog, "lake build Papers.Fix");
    const r = await gateMoveBatch(batchOf(args), d);
    expect(r).toMatchObject({ ok: false, restored: true });
    expect(r.log).toMatch(/gate step 'lake build paper' failed/);
    expect(await readFile(main, "utf8")).toBe(PAPER_MAIN);
    expect(existsSync(path.join(root, "Toolkit", "Tricks", "Arith", "Doubling.lean"))).toBe(false);
    expect((await loadLedger(cfg.ledgerPath)).declarations).toEqual([]);
    expect(existsSync(args.journalFile)).toBe(false);
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
    const r = await gateMoveBatch(batchOf(args, { ...args.plan, writes: bad }), d);
    expect(r.ok).toBe(false);
    expect(r.log).toMatch(/contains `sorry`/);
    expect(runLog).toEqual([]);
    expect(await readFile(main, "utf8")).toBe(PAPER_MAIN);
  });
});

// ─── another paper that imports the moving one ─────────────────────────────

const OTHER_USE = `module

public import Papers.Fix.Main

namespace Papers.Other

open Papers.Fix

theorem four_eq : Papers.Fix.twice_eq_two_mul 2 = Papers.Fix.twice_eq_two_mul 2 := rfl

theorem also : twice 3 = 2 * 3 := twice_eq_two_mul 3

end Papers.Other
`;

describe("a move of declarations another paper uses (papers may import each other)", () => {
  it("rewrites that paper's references as in its own, and its gate builds the module it rewrote", async () => {
    const runLog: string[] = [];
    const { root, cfg, main, d, args } = await moveFixture(runLog, null);
    const use = path.join(root, "Papers", "Other", "Use.lean");
    await mkdir(path.dirname(use), { recursive: true });
    await writeFile(use, OTHER_USE);
    const plan = planMove(input(root, { paperFiles: new Map([[main, PAPER_MAIN], [use, OTHER_USE]]) }));
    const text = plan.writes.get(use)!;
    expect(text).toContain("public import Toolkit.Tricks.Arith.Doubling");
    expect(text).toContain("theorem four_eq : Toolkit.Tricks.Arith.twice_eq_two_mul' 2 = Toolkit.Tricks.Arith.twice_eq_two_mul' 2 := rfl");
    expect(text).toContain("theorem also : Toolkit.Tricks.Arith.twice 3 = 2 * 3 := Toolkit.Tricks.Arith.twice_eq_two_mul' 3");
    expect(otherPaperModules(cfg, plan.writes.keys(), "Papers.Fix")).toEqual(["Papers.Other.Use"]);
    const r = await gateMoveBatch(batchOf(args, plan), d);
    expect(r.ok).toBe(true);
    // (built once before the move: it builds, so the gate builds it again)
    expect(runLog[0]).toBe("lake build Papers.Other.Use");
    expect(runLog[2]).toBe("lake build Papers.Fix Papers.Other.Use");
    expect(await readFile(use, "utf8")).toBe(text);
  });

  it("failingModules, killedModules and gatedOthers read Lake's log", () => {
    expect(gatedOthers(["Papers.A.X", "Papers.B.Y"], new Set(["Papers.B.Y"]))).toEqual(["Papers.A.X"]);
    expect(failingModules("✖ [12/40] Building Papers.Other.Use\nerror: ./Papers/Other/Two.lean:3:1: unknown\nerror: ././././Papers/Other/Three.lean:1:1: x\n")).toEqual(["Papers.Other.Three", "Papers.Other.Two", "Papers.Other.Use"]);
    // (2026-11-11) a job whose Lean was killed (137: the OOM killer), not one with an error of its own, nor a crash (139)
    expect(killedModules("✖ [1/9] Building Papers.A.Big (237s)\ntrace: .> LEAN_PATH=…\nerror: Lean exited with code 137\n⚠ [2/9] Built Papers.A.Ok\n✖ [3/9] Building Papers.B.Bad\nerror: Papers/B/Bad.lean:3:1: unknown\nerror: Lean exited with code 1\n✖ [4/9] Building Papers.C.Deep\nerror: Lean exited with code 139\n")).toEqual(["Papers.A.Big"]);
  });

  it("brokenBefore: one build per paper; a failure counts every module asked of that paper (a third paper's breakage included)", async () => {
    const cmds: string[] = [];
    const d = { run: async (cmd: string) => { cmds.push(cmd); return cmd.includes("Papers.Y.") ? { code: 1, log: "✖ [3/9] Building Papers.X.Base" } : { code: 0, log: "ok" }; } };
    expect(await brokenBefore({ toolkitRoot: "/tk" }, d, ["Papers.Y.A", "Papers.Z.C", "Papers.Y.B"])).toEqual(new Set(["Papers.Y.A", "Papers.Y.B"]));
    expect(cmds).toEqual(["lake build Papers.Y.A Papers.Y.B", "lake build Papers.Z.C"]);
    expect(await brokenBefore({ toolkitRoot: "/tk" }, d, [])).toEqual(new Set());
  });

  it("a batch reads what other papers' modules build just before writing, and its gate does not wait on the broken ones", async () => {
    const runLog: string[] = [];
    const { root, main, d, args } = await moveFixture(runLog, null);
    const use = path.join(root, "Papers", "Other", "Use.lean");
    await mkdir(path.dirname(use), { recursive: true });
    await writeFile(use, OTHER_USE);
    const plan = planMove(input(root, { paperFiles: new Map([[main, PAPER_MAIN], [use, OTHER_USE]]) }));
    const broken: typeof d = { ...d, run: async (cmd, cwd) => (cmd === "lake build Papers.Other.Use" && !existsSync(path.join(root, "Toolkit", "Tricks", "Arith", "Doubling.lean")) ? (runLog.push(cmd), { code: 1, log: "error" }) : d.run(cmd, cwd)) };
    const res = await gateMoveBatch({
      cfg: args.cfg, toolsDir: "/tools", journalFile: path.join(root, "runs", "fix", "proposals", "move_batch_journal.json"), probeFile: args.probeFile,
      indexStep: args.indexStep, headlineBaseline: args.headlineBaseline, invariance: [],
      moves: [{ slug: "fix", proposalId: args.proposalId, paperModule: "Papers.Fix", decls: args.decls, ledgerEntries: args.ledgerEntries, plan: async () => ({ plan, target: args.target }) }],
    }, broken);
    expect(res.ok).toBe(true);
    expect(runLog[0]).toBe("lake build Papers.Other.Use");
    expect(runLog).toContain("lake build Papers.Fix");
    expect(runLog.filter((c) => c.includes("Papers.Other.Use"))).toHaveLength(1);
    expect(res.log).toContain("rewritten, not gated: Papers.Other.Use");
  });

  it("a paper file changed since the plan read it (a live run's edit) is never written over: nothing of the move is written", async () => {
    const runLog: string[] = [];
    const { root, main, d, args } = await moveFixture(runLog, null);
    const use = path.join(root, "Papers", "Other", "Use.lean");
    await mkdir(path.dirname(use), { recursive: true });
    await writeFile(use, OTHER_USE);
    const plan = planMove(input(root, { paperFiles: new Map([[main, PAPER_MAIN], [use, OTHER_USE]]) }));
    const edited = `${OTHER_USE}\ntheorem saved_meanwhile : True := trivial\n`;
    await writeFile(use, edited);
    const r = await gateMoveBatch(batchOf(args, plan), d);
    expect(r.ok).toBe(false);
    expect(r.log).toMatch(/Papers\/Other\/Use\.lean changed since the move was planned/);
    expect(await readFile(use, "utf8")).toBe(edited);
    expect(await readFile(main, "utf8")).toBe(PAPER_MAIN);
    expect(existsSync(path.join(root, "Toolkit", "Tricks", "Arith", "Doubling.lean"))).toBe(false);
    // (what the other paper's module builds was read; no gate ran)
    expect(runLog).toEqual(["lake build Papers.Other.Use"]);
  });

  it("a batch plans each move again after building other papers' modules: an edit saved during that build is kept and rewritten", async () => {
    const { root, main, d, args } = await moveFixture([], null);
    const use = path.join(root, "Papers", "Other", "Use.lean");
    await mkdir(path.dirname(use), { recursive: true });
    await writeFile(use, OTHER_USE);
    const edited = OTHER_USE.replace("end Papers.Other", "theorem saved_meanwhile : twice 1 = 2 := by decide\n\nend Papers.Other");
    const editing: typeof d = { ...d, run: async (cmd, cwd) => { if (cmd === "lake build Papers.Other.Use" && (await readFile(use, "utf8")) === OTHER_USE) await writeFile(use, edited); return d.run(cmd, cwd); } };
    const plan = async () => ({ plan: planMove(input(root, { paperFiles: new Map([[main, await readFile(main, "utf8")], [use, await readFile(use, "utf8")]]) })), target: args.target });
    const res = await gateMoveBatch({
      cfg: args.cfg, toolsDir: "/tools", journalFile: path.join(root, "runs", "fix", "proposals", "move_batch_journal.json"), probeFile: args.probeFile,
      indexStep: args.indexStep, headlineBaseline: args.headlineBaseline, invariance: [],
      moves: [{ slug: "fix", proposalId: args.proposalId, paperModule: "Papers.Fix", decls: args.decls, ledgerEntries: args.ledgerEntries, plan }],
    }, editing);
    expect(res.ok).toBe(true);
    const now = await readFile(use, "utf8");
    expect(now).toContain("theorem saved_meanwhile : Toolkit.Tricks.Arith.twice 1 = 2");
    expect(now).toContain("Toolkit.Tricks.Arith.twice_eq_two_mul' 3");
  });

  it("otherPaperModules: only modules of other papers, never the moving paper's own files or the toolkit", () => {
    const cfg = { toolkitRoot: "/tk", papersLib: "Papers" };
    expect(otherPaperModules(cfg, ["/tk/Papers/Fix/Main.lean", "/tk/Papers/Fix.lean", "/tk/Toolkit/Tricks/A.lean", "/tk/Papers/Other/Sub/Use.lean", "/tk/Papers/Other/Sub/Use.lean", "/tk/Papers/Fixed/X.lean"], "Papers.Fix"))
      .toEqual(["Papers.Fixed.X", "Papers.Other.Sub.Use"]);
  });
});
