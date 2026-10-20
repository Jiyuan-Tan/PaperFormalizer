import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge, setLean, setNodeReview } from "../../src/graph/mutate.js";
import { type ConvergenceLedger, type FormalizationGraph } from "../../src/graph/types.js";
import type { Core } from "../../src/core/schema.js";
import { TOOLKIT_JSON } from "../toolkit/helpers.js";
import {
  auditConvergenceReview,
  clearedTargets,
  restampCleared,
  buildSymbolReviewRows,
  dualClearedAt,
  dualMatchedReceipts,
  loadPartialReceipts,
  partialReceiptsPath,
  nodeConvergenceEvidence,
  REVIEW_STANDARD,
  symbolConvergenceEvidence,
} from "../../src/formalization/convergence_evidence.js";
import { parseStatementFingerprints, takeStatementFingerprints, type StatementFingerprints } from "../../src/formalization/statement_fingerprints.js";

const LEAN = [
  "import Mathlib.Data.Real.Basic",
  "",
  "-- an untagged helper: no @node, not a graph node, reached only by name",
  "def helperBound (n : ℕ) : ℝ := n + 1",
  "",
  "/-- @realizes K -/",
  "def kArms : ℕ := 2",
  "",
  "-- @node: def:class",
  "structure ModelClass where",
  "  /-- the bound -/",
  "  bound : ℝ",
  "  bound_pos : 0 < bound",
  "",
  "-- @node: thm:main",
  "theorem mainThm (M : ModelClass) (n : ℕ) : M.bound ≤ helperBound n + 1 := by",
  "  sorry",
  "",
  "-- @node: lem:side",
  "lemma sideLemma : True := by trivial",
].join("\n");

function fixtureGraph(): FormalizationGraph {
  let g = createEmptyGraph("q");
  g = addNode(g, { id: "thm:main", kind: "theorem", provenance: "from-note", nl_statement: "the main bound", tex_anchor: "" });
  g = addNode(g, { id: "def:class", kind: "definition", provenance: "from-note", nl_statement: "the model class", tex_anchor: "" });
  g = addNode(g, { id: "lem:side", kind: "lemma", provenance: "from-note", nl_statement: "a side fact", tex_anchor: "" });
  g = setLean(g, "thm:main", "mainThm", "Main.lean");
  g = setLean(g, "def:class", "ModelClass", "Main.lean");
  g = setLean(g, "lem:side", "sideLemma", "Main.lean");
  g = addEdge(g, { kind: "statement-uses", from: "thm:main", to: "def:class", source: "extracted" });
  for (const id of ["thm:main", "def:class", "lem:side"]) g = setNodeReview(g, id, "matched", "h");
  return g;
}

const core = {
  qid: "q",
  symbols: [{ name: "K", space: "\\{2,3,\\dots\\}", role: "core" }],
  assumptions: [],
  definitions: [],
  statements: [{ id: "thm:main", kind: "theorem", statement: "the main bound", depends_on: [], status: "proved", proof_tex: "p" }],
  target_estimand: "x",
  bibliography: [],
} as unknown as Core;

const receipt = (h: string) => ({ codex: { verdict: "matched" as const, evidence_hash: h }, claude: { verdict: "matched" as const, evidence_hash: h } });

/** A scan of the fixture as `candidate_scan --fingerprints` reports one: declared names with their
 *  namespace, files relative to the toolkit root, one closure hash each. */
const SCAN = { "Toy.helperBound": "c-helper", "Toy.kArms": "c-karms", "Toy.ModelClass": "c-class", "Toy.mainThm": "c-main", "Toy.sideLemma": "c-side" };
const scan = (hashes: Record<string, string> = SCAN, file = "Papers/Toy/Main.lean"): StatementFingerprints =>
  parseStatementFingerprints(JSON.stringify({ declarations: Object.entries(hashes).map(([name, closure_hash]) => ({ name, file, closure_hash })) }), "Papers/Toy")!;

let dir = "";
let rubric = "";

beforeEach(async () => {
  rubric = REVIEW_STANDARD;
  dir = await mkdtemp(join(tmpdir(), "conv-evidence-"));
  await writeFile(join(dir, "Main.lean"), LEAN);
});
afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

const evidenceOf = (nodeId: string, graph = fixtureGraph(), fingerprints: StatementFingerprints | null = scan(), rubricHash = rubric): string | null =>
  nodeConvergenceEvidence({ graph, fingerprints, core, rubricHash, nodeId });
const symbolEvidence = async (fingerprints: StatementFingerprints | null = scan()) => {
  const rows = await buildSymbolReviewRows(dir, core.symbols);
  return symbolConvergenceEvidence({ fingerprints, rubricHash: rubric, row: rows[0] });
};

describe("statement fingerprints", () => {
  it("reads closure hashes off a scan; a scan with none (an older CandidateScan.lean, a broken file) is null", () => {
    expect(scan().byShort.get("mainThm")).toEqual([{ name: "Toy.mainThm", file: "Papers/Toy/Main.lean", hash: "c-main" }]);
    expect(parseStatementFingerprints(JSON.stringify({ declarations: [{ name: "Toy.mainThm", file: "Papers/Toy/Main.lean", stmt_hash: "1" }] }), "Papers/Toy")).toBeNull();
    expect(parseStatementFingerprints("{ not json", "Papers/Toy")).toBeNull();
  });

  it("is one build and one scan of the run's modules; any failure is null, never a throw", async () => {
    const root = await mkdtemp(join(tmpdir(), "conv-fp-"));
    try {
      const leanDir = join(root, "Papers", "Toy");
      await mkdir(join(leanDir, "Helpers"), { recursive: true });
      await mkdir(join(leanDir, "tmp"), { recursive: true });
      await writeFile(join(leanDir, "Main.lean"), LEAN);
      await writeFile(join(leanDir, "Helpers", "Aux.lean"), "def aux : Nat := 0\n");
      await writeFile(join(leanDir, "tmp", "Probe.lean"), "def probe : Nat := 0\n");
      const calls: string[][] = [];
      const exec = (code: number) => async (args: string[]) => {
        calls.push(args);
        if (args[0] === "exe") await writeFile(args[args.indexOf("--out") + 1], JSON.stringify({ declarations: [{ name: "Toy.mainThm", file: "Papers/Toy/Main.lean", closure_hash: "c" }] }));
        return { code, output: "" };
      };
      // no lakefile, no exe: nothing is spawned
      expect(await takeStatementFingerprints(root, leanDir, exec(0))).toBeNull();
      expect(calls).toEqual([]);
      await writeFile(join(root, "leansmith.json"), JSON.stringify(TOOLKIT_JSON));
      await writeFile(join(root, "lakefile.toml"), 'name = "t"\n\n[[lean_lib]]\nname = "Toolkit"\n\n[[lean_lib]]\nname = "Papers"\n\n[[lean_exe]]\nname = "candidate_scan"\nroot = "CandidateScan"\n');
      const fp = await takeStatementFingerprints(root, leanDir, exec(0));
      expect(fp?.byShort.get("mainThm")?.[0].hash).toBe("c");
      expect(fp?.modules).toEqual(["Papers.Toy.Helpers.Aux", "Papers.Toy.Main"]);
      expect(calls[0]).toEqual(["build", "Papers.Toy.Helpers.Aux", "Papers.Toy.Main", "candidate_scan"]);
      expect(calls[1].slice(0, 11)).toEqual(["exe", "candidate_scan", "--", "--graph", "--fingerprints", "--toolkit-prefix", "Toolkit", "--papers-prefix", "Papers", "--modules", "Papers.Toy.Helpers.Aux,Papers.Toy.Main"]);
      // a red build: no scan, no fingerprints
      calls.length = 0;
      expect(await takeStatementFingerprints(root, leanDir, exec(1))).toBeNull();
      expect(calls.map((c) => c[0])).toEqual(["build"]);
      // a build stopped by its timeout is retried once; a stall that clears yields the scan
      calls.length = 0;
      let stalls = 1;
      const stalling = async (args: string[]) => {
        if (args[0] === "build" && stalls-- > 0) { calls.push(args); return { code: null, output: "", killed: true }; }
        return exec(0)(args);
      };
      expect((await takeStatementFingerprints(root, leanDir, stalling))?.byShort.get("mainThm")?.[0].hash).toBe("c");
      expect(calls.map((c) => c[0])).toEqual(["build", "build", "exe"]);
      // one that stalls twice is reported as a timeout and yields nothing
      calls.length = 0;
      stalls = 2;
      expect(await takeStatementFingerprints(root, leanDir, stalling)).toBeNull();
      expect(calls.map((c) => c[0])).toEqual(["build", "build"]);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });
});

describe("node convergence evidence", () => {
  it("is what Lean elaborated: source text that leaves the fingerprints alone leaves the hash alone", async () => {
    const before = [evidenceOf("thm:main"), evidenceOf("def:class"), evidenceOf("lem:side"), await symbolEvidence()];
    // options, an `open`, a `variable`, an import, a notation file, a new helper, a proof, docstrings,
    // and both tags moved (the `@realizes` from its docstring to a trailing comment)
    await writeFile(join(dir, "Notation.lean"), "import Mathlib.Data.Real.Basic\nopen Real\nnotation \"BND\" => 42\n");
    await writeFile(join(dir, "Main.lean"), LEAN
      .replace("import Mathlib.Data.Real.Basic", "import Mathlib.Data.Real.Basic\nimport Papers.Toy.Notation\nset_option linter.unusedVariables false\nset_option maxHeartbeats 400000\nopen Real Set\nvariable (k : ℕ)")
      .replace("/-- @realizes K -/\ndef kArms : ℕ := 2", "/-- The number of arms. -/\ndef kArms : ℕ := 2 -- @realizes K")
      .replace("-- @node: thm:main\n", "/-- The [main bound](goal) holds. -/\n-- @node: thm:main\n")
      .replace("  sorry", "  simp")
      .replace("def helperBound", "/-- helper doc -/\ndef helperBound")
      + "\n\ndef unrelatedHelper : ℕ := 3\n");
    const after = scan({ ...SCAN, "Toy.unrelatedHelper": "c-new" });
    expect([evidenceOf("thm:main", fixtureGraph(), after), evidenceOf("def:class", fixtureGraph(), after), evidenceOf("lem:side", fixtureGraph(), after), await symbolEvidence(after)]).toEqual(before);
  });

  it("a changed definition re-opens exactly the targets whose closure Lean reports changed", async () => {
    // `helperBound` gets a new body: Lean moves its closure hash and that of `mainThm`, which states it
    const after = scan({ ...SCAN, "Toy.helperBound": "c-helper-2", "Toy.mainThm": "c-main-2" });
    expect(evidenceOf("thm:main", fixtureGraph(), after)).not.toBe(evidenceOf("thm:main"));
    expect(evidenceOf("def:class", fixtureGraph(), after)).toBe(evidenceOf("def:class"));
    expect(evidenceOf("lem:side", fixtureGraph(), after)).toBe(evidenceOf("lem:side"));
    expect(await symbolEvidence(after)).toBe(await symbolEvidence());
  });

  it("a target with no fingerprint has no evidence and is never current; a library anchor is keyed by name", () => {
    expect(evidenceOf("thm:main", fixtureGraph(), null)).toBeNull();
    const { "Toy.mainThm": _gone, ...rest } = SCAN;
    expect(evidenceOf("thm:main", fixtureGraph(), scan(rest))).toBeNull();
    expect(evidenceOf("lem:side", fixtureGraph(), scan(rest))).toBe(evidenceOf("lem:side"));
    // the anchor's file is part of it: the same name in another file is another declaration
    expect(evidenceOf("thm:main", fixtureGraph(), scan(SCAN, "Papers/Toy/Other.lean"))).toBeNull();
    expect(dualClearedAt({ "thm:main": receipt("h") }, "thm:main", null)).toBe(false);
    let g = fixtureGraph();
    g = addNode(g, { id: "S1", kind: "definition", provenance: "library", nl_statement: "a library object", tex_anchor: "" });
    g = { ...g, nodes: g.nodes.map((n) => (n.id === "S1" ? { ...n, lean: { decl_name: "Lib.Stat.sample", file: null } } : n)) };
    const lib = evidenceOf("S1", g);
    expect(lib).not.toBeNull();
    expect(evidenceOf("S1", g, scan({ ...SCAN, "Toy.mainThm": "c-main-2" }))).toBe(lib);
    expect(evidenceOf("S1", g, null)).toBeNull();
    // a toolkit declaration the scan reports is read by its fingerprint, wherever it lives
    const toolkit = (h: string) => parseStatementFingerprints(JSON.stringify({ declarations: [{ name: "Lib.Stat.sample", file: "Toolkit/Stat.lean", closure_hash: h }] }), "Papers/Toy")!;
    expect(evidenceOf("S1", g, toolkit("a"))).not.toBe(evidenceOf("S1", g, toolkit("b")));
  });

  it("the review standard is a hand-bumped token, not a hash of the prompt or the reviewer source", () => {
    // Frozen at the value reviewerRubricHash returned on 2026-09-12 for the shipped
    // proof_reviewer.txt, so receipts written before the change stay valid. An accidental edit
    // here invalidates every convergence receipt in every run.
    expect(REVIEW_STANDARD).toBe("16865e36da9271bbf0e9906def5868e43c1ec0d8");
  });

  it("changes with the rubric, the NL statement, the anchor, and a gated substrate hypothesis", () => {
    const before = evidenceOf("thm:main");
    expect(evidenceOf("thm:main", fixtureGraph(), scan(), "review-standard-bumped")).not.toBe(before);
    let g = fixtureGraph();
    g = { ...g, nodes: g.nodes.map((n) => (n.id === "thm:main" ? { ...n, nl: { ...n.nl, statement: "a weaker bound" } } : n)) };
    expect(evidenceOf("thm:main", g)).not.toBe(before);
    // the `@node` tag now binds the node to another declaration
    expect(evidenceOf("thm:main", setLean(fixtureGraph(), "thm:main", "sideLemma", "Main.lean"))).not.toBe(before);
    let gg = fixtureGraph();
    gg = addNode(gg, { id: "gate:x", kind: "gate", provenance: "from-note", nl_statement: "assumed substrate", tex_anchor: "" });
    gg = { ...gg, nodes: gg.nodes.map((n) => (n.id === "gate:x" ? { ...n, gate: { gate_class: "gated" as const } } : n)) };
    gg = addEdge(gg, { kind: "proof-uses", from: "thm:main", to: "gate:x", source: "declared" });
    expect(evidenceOf("thm:main", gg)).not.toBe(before);
  });
});

describe("symbol convergence evidence", () => {
  it("binds a symbol cluster to what its members elaborate to, and to which declarations they are", async () => {
    const rows = await buildSymbolReviewRows(dir, core.symbols);
    expect(rows.map((r) => [r.id, r.empty])).toEqual([["sym:K", false]]);
    const before = await symbolEvidence();
    // the prompt row is name-level: the delta key alone would NOT notice a new body
    expect(await symbolEvidence(scan({ ...SCAN, "Toy.kArms": "c-karms-2" }))).not.toBe(before);
    const { "Toy.kArms": _gone, ...rest } = SCAN;
    expect(await symbolEvidence(scan(rest))).toBeNull();
    expect(await symbolEvidence(null)).toBeNull();
    // the tag moves to another declaration: another realization
    await writeFile(join(dir, "Main.lean"), LEAN.replace("/-- @realizes K -/\n", "").replace("def helperBound", "/-- @realizes K -/\ndef helperBound"));
    expect(await symbolEvidence()).not.toBe(before);
  });

  it("a standalone `variable` carrier is read through every declaration of its file", async () => {
    await writeFile(join(dir, "Main.lean"), LEAN.replace("/-- @realizes K -/\ndef kArms : ℕ := 2", "variable (K : ℕ) -- @realizes K"));
    const { "Toy.kArms": _gone, ...rest } = SCAN;
    const before = await symbolEvidence(scan(rest));
    expect(before).not.toBeNull();
    expect(await symbolEvidence(scan({ ...rest, "Toy.sideLemma": "c-side-2" }))).not.toBe(before);
    expect(await symbolEvidence(scan(rest, "Papers/Toy/Other.lean"))).toBeNull();
  });
});

describe("a declaration tagged twice for a symbol", () => {
  it("is one member of the symbol's realization: a second `@realizes` tag on it changes nothing", async () => {
    const [once] = await buildSymbolReviewRows(dir, core.symbols as never);
    await writeFile(join(dir, "Main.lean"), LEAN.replace("def kArms : ℕ := 2", "def kArms : ℕ := 2 -- @realizes K"));
    const [twice] = await buildSymbolReviewRows(dir, core.symbols as never);
    expect(twice!.members.length).toBeGreaterThan(once!.members.length);
    expect(twice!.hash).toBe(once!.hash);
    expect(twice!.evidenceRow).toBe(once!.evidenceRow);
  });
});

describe("dualClearedAt / ledgerNodeTargets", () => {
  it("requires BOTH peers matched at the exact evidence", () => {
    const ledger: ConvergenceLedger = {
      t: { codex: { verdict: "matched", evidence_hash: "e" }, claude: { verdict: "matched", evidence_hash: "e" } },
      one: { codex: { verdict: "matched", evidence_hash: "e" } },
      drift: { codex: { verdict: "matched", evidence_hash: "e" }, claude: { verdict: "drift", evidence_hash: "e" } },
      stale: { codex: { verdict: "matched", evidence_hash: "e" }, claude: { verdict: "matched", evidence_hash: "old" } },
    };
    expect(dualClearedAt(ledger, "t", "e")).toBe(true);
    expect(dualClearedAt(ledger, "t", "e2")).toBe(false);
    expect(dualClearedAt(ledger, "one", "e")).toBe(false);
    expect(dualClearedAt(ledger, "drift", "e")).toBe(false);
    expect(dualClearedAt(ledger, "stale", "e")).toBe(false);
    expect(dualClearedAt(undefined, "t", "e")).toBe(false);
  });

});

describe("receipts across a change Lean certifies leaves every statement as it was", () => {
  it("the targets both peers had passed are carried to the new evidence; one that was not current is not", async () => {
    const g = fixtureGraph();
    const ledgerGraph = { ...g, convergenceReview: { "thm:main": receipt(evidenceOf("thm:main", g)!), "lem:side": receipt("an-older-statement") } };
    const cleared = await clearedTargets({ graph: ledgerGraph, leanDir: dir, core, fingerprints: scan() });
    expect(cleared).toEqual(["thm:main"]);
    expect(await clearedTargets({ graph: ledgerGraph, leanDir: dir, core, fingerprints: null })).toEqual([]);
    // a move renames a helper the theorem states: Lean reports another closure, the receipt is no longer current …
    const moved = scan({ ...SCAN, "Toy.helperBound": "c-helper-moved", "Toy.mainThm": "c-main-moved" });
    const after = evidenceOf("thm:main", g, moved);
    expect(dualClearedAt(ledgerGraph.convergenceReview, "thm:main", after)).toBe(false);
    // … and is carried over
    const r = await restampCleared({ graph: ledgerGraph, leanDir: dir, core, fingerprints: moved, ids: cleared });
    expect(r.restamped).toEqual(["thm:main"]);
    expect(dualClearedAt(r.graph.convergenceReview, "thm:main", after)).toBe(true);
    expect(r.graph.convergenceReview!["lem:side"]).toEqual(receipt("an-older-statement"));
    // without fingerprints after the change there is nothing to carry to
    expect((await restampCleared({ graph: ledgerGraph, leanDir: dir, core, fingerprints: null, ids: cleared })).restamped).toEqual([]);
  });
});

describe("receipts of a pass that did not finish", () => {
  it("only entries both peers passed on the same evidence are kept for the next pass", async () => {
    const ledger: ConvergenceLedger = {
      "thm:a": receipt("h1"),
      "thm:b": { codex: { verdict: "matched", evidence_hash: "h2" } },
      "thm:c": { codex: { verdict: "matched", evidence_hash: "h3" }, claude: { verdict: "drift", evidence_hash: "h3" } },
      "thm:d": { codex: { verdict: "matched", evidence_hash: "h4" }, claude: { verdict: "matched", evidence_hash: "h5" } },
    };
    expect(Object.keys(dualMatchedReceipts(ledger))).toEqual(["thm:a"]);
    expect(await loadPartialReceipts(dir)).toEqual({});
    await writeFile(partialReceiptsPath(dir), JSON.stringify(ledger));
    expect(await loadPartialReceipts(dir)).toEqual({ "thm:a": receipt("h1") });
    await writeFile(partialReceiptsPath(dir), "{ not json");
    expect(await loadPartialReceipts(dir)).toEqual({});
  });
});

describe("auditConvergenceReview", () => {
  it("passes when every governed target is dual-receipted at current evidence, and names each gap otherwise", async () => {
    const g = fixtureGraph();
    const ev = (id: string) => evidenceOf(id, g)!;
    const rows = await buildSymbolReviewRows(dir, core.symbols);
    const symEv = (await symbolEvidence())!;
    const fingerprints = async () => scan();
    const ledger: ConvergenceLedger = {
      "thm:main": receipt(ev("thm:main")),
      "def:class": receipt(ev("def:class")),
      "lem:side": receipt(ev("lem:side")),
      "sym:K": receipt(symEv),
    };
    const good = { ...g, symbolReview: { "sym:K": { verdict: "matched", hash: rows[0].hash } }, convergenceReview: ledger };
    expect(await auditConvergenceReview({ graph: good, leanDir: dir, core, fingerprints })).toEqual([]);

    // Tree edited after F4: the theorem's receipt is stale, the others still hold.
    const edited = async () => scan({ ...SCAN, "Toy.mainThm": "c-main-2" });
    const stale = await auditConvergenceReview({ graph: good, leanDir: dir, core, fingerprints: edited });
    expect(stale.map((f) => f.node_id)).toEqual(["thm:main"]);
    expect(stale[0].message).toMatch(/stale/);

    // No fingerprints for the built tree, or none for one anchor: nothing can be verified there.
    const blind = await auditConvergenceReview({ graph: good, leanDir: dir, core, fingerprints: async () => null });
    expect(blind.map((f) => f.node_id).sort()).toEqual(["def:class", "lem:side", "sym:K", "thm:main"]);
    expect(blind[0].message).toMatch(/no statement fingerprints/);
    const { "Toy.sideLemma": _gone, ...rest } = SCAN;
    const unbound = await auditConvergenceReview({ graph: good, leanDir: dir, core, fingerprints: async () => scan(rest) });
    expect(unbound.map((f) => f.node_id)).toEqual(["lem:side"]);
    expect(unbound[0].message).toMatch(/elaborated no declaration/);

    // One peer missing / a delta-only clearance / a symbol not delta-passed.
    const half = { ...good, convergenceReview: { ...ledger, "lem:side": { codex: ledger["lem:side"].codex } } };
    expect((await auditConvergenceReview({ graph: half, leanDir: dir, core, fingerprints })).map((f) => f.node_id)).toEqual(["lem:side"]);
    const noLedger = { ...good, convergenceReview: undefined };
    expect((await auditConvergenceReview({ graph: noLedger, leanDir: dir, core, fingerprints })).map((f) => f.node_id).sort())
      .toEqual(["def:class", "lem:side", "sym:K", "thm:main"]);
    const symDrift = { ...good, symbolReview: { "sym:K": { verdict: "drift", hash: rows[0].hash } } };
    expect((await auditConvergenceReview({ graph: symDrift, leanDir: dir, core, fingerprints })).map((f) => f.node_id)).toEqual(["sym:K"]);
    const nodeDrift = { ...good, nodes: good.nodes.map((n) => (n.id === "def:class" ? { ...n, review: { ...n.review, status: "drift" as const } } : n)) };
    expect((await auditConvergenceReview({ graph: nodeDrift, leanDir: dir, core, fingerprints })).map((f) => f.node_id)).toEqual(["def:class"]);
  });
});
