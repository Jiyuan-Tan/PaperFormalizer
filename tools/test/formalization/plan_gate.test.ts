import { mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { knownDeclsForContext } from "../../src/formalization/known_decls.js";
import { toolkitConfigFromJson } from "../../src/toolkit/config.js";
import { describe, expect, it } from "vitest";
import { planHygieneViolations, runPlanGate, type PlanGateViolation } from "../../src/formalization/plan/plan_gate.js";
import { NodeEntrySchema, PLAN_NOTES_MAX, PlanSchema } from "../../src/formalization/plan/schema.js";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { planGatePrelint } from "../../src/formalization/stage1_5.js";
import { applyBuiltDeclsToPlan } from "../../src/formalization/plan/discharge.js";
import type { Core } from "../../src/core/schema.js";
import { addNode, markPassed, setLean, setProof } from "../../src/graph/mutate.js";
import { createEmptyGraph } from "../../src/graph/store.js";
import { statementHash } from "../../src/graph/hash.js";
import type { ExtractedDecl } from "../../src/graph/extractor.js";

// A small, schema-valid core exercising every node kind: a standalone atom, two
// shared member atoms, a class, a construction, and a theorem.
function makeCore(): Core {
  return {
    qid: "panel_demo",
    cluster: "stat",
    symbols: [
      { name: "X", type: "covariate" },
      { name: "Y", type: "outcome" },
      { name: "e", type: "propensity" },
    ],
    assumptions: [
      { id: "ass:overlap", condition: "0 < e(X) < 1", free_symbols: ["e", "X"], novel: { flag: true, justification: "weak overlap regime" } },
      { id: "ass:consistency", condition: "Y = Y(D)", free_symbols: ["Y"], novel: { flag: true, justification: "PO consistency" } },
      { id: "ass:ignorability", condition: "(Y(1),Y(0)) ⫫ D | X", free_symbols: ["Y", "X"], novel: { flag: true, justification: "unconfoundedness" } },
    ],
    definitions: [
      { id: "def:overlap-class", name: "OverlapClass", construction: "{ P : P satisfies ass:consistency, ass:ignorability }", by_member_properties: ["ass:consistency", "ass:ignorability"] },
      { id: "def:estimator", name: "tauHat", construction: "tauHat = average of psi", inputs: ["O"] },
    ],
    statements: [
      { id: "thm:main", kind: "theorem", statement: "tauHat → tau", depends_on: ["ass:overlap", "ass:consistency", "ass:ignorability", "def:overlap-class", "def:estimator"], status: "proved" },
      { id: "oeq:tight", kind: "openendedquestion", statement: "is the feasible rate tight?", depends_on: ["thm:main"], status: "to-prove" },
    ],
    target_estimand: "tau = E[Y(1) - Y(0)]",
    bibliography: [],
  } as Core;
}

// A plan that maps makeCore() one-to-one. `consistency`/`ignorability` are reached
// by `thm:main` through the bundled class, so they need not be re-listed in hyps.
function makePlan() {
  return {
    qid: "panel_demo",
    cluster: "stat",
    lean_subdir: "Stat/Demo",
    env: [
      { id: "S1", world: "po-system", binds_symbols: ["X", "Y", "e"], binds_sampling_model: true, disposition: "reuse", reuse: "Causalean.PO.System.POStructure", modules: ["Causalean.PO.System"] },
    ],
    nodes: {
      "ass:overlap": { lean_kind: "assumption", lean_name: "assOverlap", disposition: "define-local", modules: ["Causalean.PO.Overlap"] },
      "ass:consistency": { lean_kind: "assumption", lean_name: "assConsistency", disposition: "define-local" },
      "ass:ignorability": { lean_kind: "assumption", lean_name: "assIgnorability", disposition: "define-local" },
      "def:overlap-class": { lean_kind: "structure", lean_name: "OverlapClass", members: ["ass:consistency", "ass:ignorability"], disposition: "define-local" },
      "def:estimator": { lean_kind: "def", lean_name: "tauHat", disposition: "define-local" },
      "thm:main": { lean_kind: "theorem", lean_name: "main", target_file: "Basic.lean", hyps: ["ass:overlap", "def:overlap-class"], disposition: "define-local" },
      "oeq:tight": { lean_kind: "def", lean_name: "tightOpenQuestion", disposition: "define-local" },
    },
    feasibility: "formalizable-now",
  };
}

function codes(vs: PlanGateViolation[]): string[] {
  return vs.map((v) => v.code);
}

describe("F1 plan gate — golden minimal plan", () => {
  it("a one-to-one plan over the demo core passes every check", () => {
    const res = runPlanGate(makePlan(), makeCore());
    expect(res.violations).toEqual([]);
    expect(res.ok).toBe(true);
  });
});

type DemoPlan = ReturnType<typeof makePlan>;

describe("F1 plan gate — structural checks", () => {
  it.each([
    ["a missing node entry", (plan: DemoPlan) => { delete (plan.nodes as Record<string, unknown>)["ass:overlap"]; }],
    ["an extra node entry that is not a core node", (plan: DemoPlan) => {
      (plan.nodes as Record<string, unknown>)["ass:bogus"] = { lean_kind: "assumption", lean_name: "x", disposition: "define-local" };
    }],
    ["an unbound symbol", (plan: DemoPlan) => { plan.env[0].binds_symbols = ["X", "Y"]; }],
  ])("P1 flags %s", (_label, mutate) => {
    const plan = makePlan();
    mutate(plan);
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P1");
  });

  it.each([
    ["P2", "a class whose members disagree with by_member_properties", (plan: DemoPlan) => { plan.nodes["def:overlap-class"].members = ["ass:consistency"]; }],
    ["P3", "a wrong lean_kind for a core kind", (plan: DemoPlan) => { plan.nodes["def:overlap-class"].lean_kind = "def"; }],
    ["P3", "a theorem disposition for an unresolved open-ended question", (plan: DemoPlan) => { plan.nodes["oeq:tight"].lean_kind = "theorem"; }],
  ])("%s flags %s", (code, _label, mutate) => {
    const plan = makePlan();
    mutate(plan);
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain(code);
  });

  it("P4 accepts a hyp inherited from a result the node uses, and still flags one reached by none (live cns, drdid: 'under the conditions of Lemma X')", () => {
    const core = makeCore();
    core.statements.push({ id: "thm:corollary", kind: "theorem", statement: "under the conditions of the theorem, …", depends_on: ["thm:main"], status: "to-prove" } as Core["statements"][number]);
    const plan = makePlan() as DemoPlan & { nodes: Record<string, unknown> };
    (plan.nodes as Record<string, unknown>)["thm:corollary"] = { lean_kind: "theorem", lean_name: "corollary", target_file: "Basic.lean", hyps: ["ass:overlap"], disposition: "define-local" };
    expect(runPlanGate(plan, core).violations.filter((v) => v.code === "P4")).toEqual([]);
    (plan.nodes["thm:corollary"] as { hyps: string[] }).hyps = ["ass:overlap", "ass:phantom"];
    expect(runPlanGate(plan, core).violations.filter((v) => v.code === "P4").map((v) => v.message)).toEqual(["hyp 'ass:phantom' is not in depends_on"]);
  });

  it("P4 flags a hyp not in depends_on", () => {
    const plan = makePlan();
    plan.nodes["thm:main"].hyps = ["ass:overlap", "def:overlap-class", "ass:phantom"];
    expect(codes(runPlanGate(plan, makeCore()).violations)).toContain("P4");
  });

  it.each([
    ["P6", "a malformed module path", (plan: DemoPlan) => { plan.nodes["ass:overlap"].modules = ["not a module"]; return {}; }],
    ["P7", "emitted-tag drift against the plan", (_plan: DemoPlan) => ({ leanTags: { nodes: new Set(["thm:main"]), envs: new Set(["S1"]) } })],
    ["P8", "stored feasibility disagreeing with the derived value", (plan: DemoPlan) => {
      (plan.nodes["def:estimator"] as Record<string, unknown>).defer_tier = true;
      return {};
    }],
  ])("%s flags %s", (code, _label, mutate) => {
    const plan = makePlan();
    const opts = mutate(plan);
    expect(codes(runPlanGate(plan, makeCore(), opts).violations)).toContain(code);
  });
});

describe("F1 plan gate — paper-owned proof obligations", () => {
  it.each([
    ["deferred without an external gate", { defer_tier: true }, "needs-new-infrastructure", "paper-owned proved/to-prove statement"],
    ["relabeled as an external gate", { lean_kind: "assumption", defer_tier: true, gate: true, gate_class: "gated" }, "needs-new-infrastructure", "planner-authored external gate"],
    ["deferred and marked undelivered", { defer_tier: true, delivery_status: "undelivered", delivery_role: "secondary", delivery_reason: "too difficult" }, "formalizable-now", "paper-owned proved/to-prove statement"],
  ])("rejects a proved paper statement %s", (_label, patch, feasibility, message) => {
    const plan = makePlan();
    Object.assign(plan.nodes["thm:main"], patch);
    plan.feasibility = feasibility;
    expect(runPlanGate(plan, makeCore()).violations).toContainEqual(
      expect.objectContaining({ code: "P8", where: "thm:main", message: expect.stringContaining(message) }),
    );
  });
});

describe("F1 plan gate — P5 reuse", () => {
  it("flags a reuse decl absent from the library index and passes when it is present", () => {
    const plan = makePlan();
    expect(codes(runPlanGate(plan, makeCore(), { knownDecls: new Set(["SomethingElse"]) }).violations)).toContain("P5");
    expect(runPlanGate(plan, makeCore(), { knownDecls: new Set(["Causalean.PO.System.POStructure"]) }).ok).toBe(true);
  });
  it("accepts a toolkit declaration known only from the ledger or the toolkit sources", () => {
    const dir = mkdtempSync(path.join(os.tmpdir(), "known-decls-"));
    const root = path.join(dir, "tk");
    const index = path.join(dir, "base", "doc", "library_index.json");
    mkdirSync(path.dirname(index), { recursive: true });
    writeFileSync(index, JSON.stringify({ commit: "c", toolchain: "t", modules: {}, entries: [{
      name: "Causalean.other", kind: "theorem", module: "Causalean.X", file: "Causalean/X.lean", line: 1, statement: "True",
      doc: "", refs: [], axioms: [], usesSorry: false,
    }] }));
    const cfg = toolkitConfigFromJson(root, {
      version: 1, owner: { name: "T" },
      toolkit: { lib: "Toolkit", papers_lib: "Papers", divisions: ["Foundations"] },
      base: [{ name: "Base", kind: "path", path: "../base", index: "../base/doc/library_index.json" }],
      lean: { toolchain: "leanprover/lean4:v4.33.0" },
    });
    mkdirSync(path.join(root, "doc"), { recursive: true });
    const ledgerDecl = (name: string) => ({ name, module: "Toolkit.Foundations.PO.System", division: "Foundations",
      origin: { kind: "study", slug: "po" }, date: "2026-09-23", decision: "accepted-by-study", used_by: [] });
    writeFileSync(cfg.ledgerPath, JSON.stringify({ version: 1, declarations: [ledgerDecl("Causalean.PO.System.POStructure")], decisions: [] }));
    const src = (ns: string, name: string) => `module\n\n/-! # M -/\n\npublic section\n\nnamespace ${ns}\n\ntheorem ${name} : True := trivial\n\nend ${ns}\n`;
    mkdirSync(path.join(root, "Toolkit", "Foundations", "Topic"), { recursive: true });
    writeFileSync(path.join(root, "Toolkit", "Foundations", "Topic", "A.lean"), src("Toolkit.Foundations.Topic", "scanned"));
    mkdirSync(path.join(root, "Toolkit", "Staging", "S"), { recursive: true });
    writeFileSync(path.join(root, "Toolkit", "Staging", "S", "B.lean"), src("Toolkit.Staging.S", "staged"));

    const known = knownDeclsForContext({ repoRoot: root, toolkit: cfg })!;
    expect(known.names.has("Causalean.other")).toBe(true);
    expect(known.names.has("Causalean.PO.System.POStructure")).toBe(true); // ledger-only
    expect(known.names.has("Toolkit.Foundations.Topic.scanned")).toBe(true); // source-scanned
    expect(known.names.has("Toolkit.Staging.S.staged")).toBe(false); // staging is imported by nothing
    // Owned prefixes: the index's module roots plus the toolkit and papers libraries.
    expect(known.ownedPrefixes).toEqual(["Causalean", "Papers", "Toolkit"]);
    const gateWith = (k: typeof known | undefined, plan = makePlan()) =>
      runPlanGate(plan, makeCore(), { knownDecls: k?.names, ownedDeclPrefixes: k?.ownedPrefixes });
    const res = gateWith(known);
    expect(res.violations.filter((v) => v.code === "P5")).toEqual([]);
    // Without the ledger record the same plan fails P5 (the name is under an owned prefix).
    writeFileSync(cfg.ledgerPath, JSON.stringify({ version: 1, declarations: [], decisions: [] }));
    const res2 = gateWith(knownDeclsForContext({ repoRoot: root, toolkit: cfg }));
    expect(codes(res2.violations)).toContain("P5");
    expect(res2.notes).toEqual([]);

    // A Mathlib name (no indexed source owns `ProbabilityTheory`) is a note, never a violation;
    // an absent name under the toolkit or papers prefix still fails.
    const plan3 = makePlan();
    plan3.env[0].reuse = "ProbabilityTheory.cdf";
    const res3 = gateWith(known, plan3);
    expect(res3.violations.filter((v) => v.code === "P5")).toEqual([]);
    expect(res3.notes).toEqual([{ code: "P5", where: "S1", message: "reuse decl 'ProbabilityTheory.cdf' is in an unindexed library, not checked" }]);
    for (const owned of ["Toolkit.Foundations.Topic.missing", "Papers.Other.helper"]) {
      const plan4 = makePlan();
      plan4.env[0].reuse = owned;
      const res4 = gateWith(known, plan4);
      expect(res4.violations).toContainEqual({ code: "P5", where: "S1", message: `reuse decl '${owned}' not found in library index` });
      expect(res4.notes).toEqual([]);
    }
  });
});

describe("F1 plan gate — P7 plan-less helpers", () => {
  function helperCase(mutate: (graph: ReturnType<typeof createEmptyGraph>, decls: ExtractedDecl[]) => ReturnType<typeof createEmptyGraph>) {
    const plan = makePlan();
    const statement = "lemma helper : True";
    let graph = createEmptyGraph("panel_demo");
    graph = addNode(graph, { id: "helper", kind: "lemma", provenance: "agent-introduced", nl_statement: "helper", tex_anchor: "" });
    graph = setLean(graph, "helper", "Demo.helper", "Helpers.lean");
    graph = setProof(graph, "helper", "complete", 0);
    graph = markPassed(graph, "helper", statementHash(statement));
    const annotatedDecls: ExtractedDecl[] = [{ nodeId: "helper", declKind: "lemma", declName: "Demo.helper", namespace: "Demo", file: "Helpers.lean", statement, hasSorry: false }];
    graph = mutate(graph, annotatedDecls);
    const leanTags = { nodes: new Set([...Object.keys(plan.nodes), "helper"]), envs: new Set(["S1"]) };
    return runPlanGate(plan, makeCore(), { leanTags, preF2Graph: graph, annotatedDecls, preF2AnnotatedDecls: structuredClone(annotatedDecls) })
      .violations.filter((v) => v.code === "P7" && v.where === "helper");
  }

  it.each([
    ["unchanged and complete", (g: ReturnType<typeof createEmptyGraph>) => g],
    ["revised by F2 (live yang: a redirect removed an instance from it)", (g: ReturnType<typeof createEmptyGraph>, d: ExtractedDecl[]) => { d[0].statement = "lemma helper : 1 = 1"; return g; }],
    ["unfinished (live yang: the filler escalated on it)", (g: ReturnType<typeof createEmptyGraph>, d: ExtractedDecl[]) => { d[0].hasSorry = true; return setProof(g, "helper", "sorry", 1); }],
    ["flagged drift", (g: ReturnType<typeof createEmptyGraph>) => { g.nodes[0].review.status = "drift"; return g; }],
  ])("keeps the tag of a pre-F2 agent-introduced helper %s", (_label, mutate) => {
    expect(helperCase(mutate)).toEqual([]);
  });

  it("keeps a self-named helper tag even when a re-plan rebuilt the graph without it (live yang: a re-plan dropped the filler's helpers)", () => {
    expect(helperCase((_g, d) => { d[0].declName = "Demo.helper"; return createEmptyGraph("panel_demo"); })).toEqual([]);
  });

  it.each([
    ["not on the pre-F2 graph and not named after its declaration", (_g: ReturnType<typeof createEmptyGraph>, d: ExtractedDecl[]) => { d[0].declName = "Demo.other"; return createEmptyGraph("panel_demo"); }],
    ["emitted on no declaration", (g: ReturnType<typeof createEmptyGraph>, d: ExtractedDecl[]) => { d.splice(0); return g; }],
  ])("refuses a helper tag %s", (_label, mutate) => {
    expect(helperCase(mutate as never)).toEqual([expect.objectContaining({ code: "P7", where: "helper" })]);
  });
});

// A minimal core+plan exercising a CITED node: `lem:borrowed-upper` is borrowed
// (status:"cited", a leaf with its own source), consumed by `thm:main`.
function makeCitedCore(): Core {
  return {
    qid: "panel_cite",
    cluster: "stat",
    symbols: [{ name: "Y", type: "outcome" }],
    assumptions: [
      { id: "ass:reg", condition: "Y bounded", free_symbols: ["Y"], novel: { flag: true, justification: "regularity" } },
    ],
    definitions: [],
    statements: [
      { id: "thm:main", kind: "theorem", statement: "rate holds", depends_on: ["ass:reg", "lem:borrowed-upper"], status: "proved" },
      { id: "lem:borrowed-upper", kind: "lemma", statement: "published upper bound", depends_on: [], status: "cited", source: { cite: "BK2022", locator: "Theorem 3" } },
    ],
    target_estimand: "theta",
    bibliography: [{ key: "BK2022", citation: "Bonvini, Kennedy (2022)" }],
  } as Core;
}

function makeCitedPlan() {
  return {
    qid: "panel_cite",
    cluster: "stat",
    lean_subdir: "Stat/Cite",
    env: [
      { id: "S1", world: "po-system", binds_symbols: ["Y"], binds_sampling_model: true, disposition: "reuse", reuse: "Causalean.PO.System.POStructure", modules: ["Causalean.PO.System"] },
    ],
    nodes: {
      "ass:reg": { lean_kind: "assumption", lean_name: "assReg", disposition: "define-local" },
      "lem:borrowed-upper": { lean_kind: "assumption", lean_name: "borrowedUpper", disposition: "define-local", gate: true, gate_class: "cited", source: "cite:bk2022" },
      "thm:main": { lean_kind: "theorem", lean_name: "main", target_file: "Basic.lean", hyps: ["ass:reg", "lem:borrowed-upper"], disposition: "define-local" },
    },
    citations: [{ id: "cite:bk2022", title: "Fast rates", authors: "Bonvini, Kennedy", year: 2022, arxiv: "2207.11825", locator: "Theorem 3" }],
    feasibility: "formalizable-now",
  };
}

type CitedPlan = ReturnType<typeof makeCitedPlan>;

describe("F1 plan gate — P9 cited mapping", () => {
  it("a faithful cited mapping passes every check", () => {
    const res = runPlanGate(makeCitedPlan(), makeCitedCore());
    expect(res.violations).toEqual([]);
    expect(res.ok).toBe(true);
  });

  it.each([
    ["re-laundering a cited statement as a non-cited gate", (plan: CitedPlan) => {
      (plan.nodes["lem:borrowed-upper"] as Record<string, unknown>).gate_class = "gated";
    }],
    ["a cited node whose source does not resolve", (plan: CitedPlan) => {
      (plan.nodes["lem:borrowed-upper"] as Record<string, unknown>).source = "cite:nonexistent";
    }],
    ["F1 inventing a citation for a non-cited statement", (plan: CitedPlan) => {
      (plan.nodes["thm:main"] as Record<string, unknown>).gate_class = "cited";
    }],
  ])("flags %s", (_label, mutate) => {
    const plan = makeCitedPlan();
    mutate(plan);
    expect(codes(runPlanGate(plan, makeCitedCore()).violations)).toContain("P9");
  });

  it.each([
    ["clearing a cited gate without mapping it to a proved lemma/theorem", false, (plan: CitedPlan) => {
      Object.assign(plan.nodes["lem:borrowed-upper"], { gate: false, gate_class: undefined });
      return {};
    }],
    ["relabeling a frozen logical quantitative citation as unthreaded metadata", false, (plan: CitedPlan) => {
      Object.assign(plan.nodes["lem:borrowed-upper"], { lean_kind: "def", lean_name: "borrowedScopeMetadata", gate: true, gate_class: "cited" });
      return {};
    }],
    ["a Prop-valued def emitted behind a metadata plan entry", true, (plan: CitedPlan) => {
      Object.assign(plan.nodes["lem:borrowed-upper"], { lean_kind: "def", lean_name: "borrowedScopeMetadata" });
      return { annotatedDecls: [{
        nodeId: "lem:borrowed-upper", declName: "borrowedScopeMetadata", namespace: "",
        file: "Basic.lean", hasSorry: false, declKind: "def", statement: "def borrowedScopeMetadata : Prop",
      }] as ExtractedDecl[] };
    }],
  ])("rejects %s", (_label, metadata, mutate) => {
    const core = makeCitedCore();
    if (metadata) core.statements.find((st) => st.id === "lem:borrowed-upper")!.source!.carrier = "bibliographic-metadata";
    const plan = makeCitedPlan();
    const opts = mutate(plan);
    plan.nodes["thm:main"].hyps = ["ass:reg"];
    expect(runPlanGate(plan, core, opts).violations).toContainEqual(
      expect.objectContaining({ code: "P9", where: "lem:borrowed-upper" }),
    );
  });

  it("an undelivered cited gate passes with no declaration (P9 asks for none) and is refused with one (P7)", () => {
    const plan = makeCitedPlan();
    plan.nodes["thm:main"].hyps = (plan.nodes["thm:main"].hyps ?? []).filter((h: string) => h !== "lem:borrowed-upper");
    Object.assign(plan.nodes["lem:borrowed-upper"], { delivery_status: "undelivered", delivery_role: "secondary", delivery_reason: "nothing delivered uses it" });
    const tags = (ids: string[]) => ({ nodes: new Set(ids), envs: new Set(Object.values(plan.env ?? []).map((e: { id: string }) => e.id)) });
    const others = Object.keys(plan.nodes).filter((id) => id !== "lem:borrowed-upper");
    const none = runPlanGate(plan, makeCitedCore(), { leanTags: tags(others) as never, annotatedDecls: [], proofsNotDue: true }).violations.filter((v) => v.where === "lem:borrowed-upper");
    expect(none).toEqual([]);
    const decl = { nodeId: "lem:borrowed-upper", declName: plan.nodes["lem:borrowed-upper"].lean_name, namespace: "", file: "Basic.lean", hasSorry: false, declKind: "def", statement: `def ${plan.nodes["lem:borrowed-upper"].lean_name} : Sort 0` } as ExtractedDecl;
    const withDecl = runPlanGate(plan, makeCitedCore(), { leanTags: tags([...others, "lem:borrowed-upper"]) as never, annotatedDecls: [decl], proofsNotDue: true }).violations.filter((v) => v.where === "lem:borrowed-upper");
    expect(withDecl.map((v) => v.code)).toEqual(["P7"]);
    // … while a delivered one with no declaration is still P9's (and P7's)
    delete (plan.nodes["lem:borrowed-upper"] as Record<string, unknown>).delivery_status;
    const delivered = runPlanGate(plan, makeCitedCore(), { leanTags: tags(others) as never, annotatedDecls: [], proofsNotDue: true }).violations.filter((v) => v.where === "lem:borrowed-upper");
    expect(delivered.map((v) => v.code).sort()).toEqual(["P7", "P9"]);
  });

  const dischargedShape = (plan: CitedPlan, stamped: boolean) => {
    Object.assign(plan.nodes["lem:borrowed-upper"], {
      lean_kind: "theorem",
      lean_name: "borrowedUpperDischarge",
      gate: false,
      gate_class: undefined,
      ...(stamped ? { citation_discharged: true } : {}),
      target_file: "BorrowedUpperDischarge.lean",
      hyps: [],
    });
    plan.nodes["thm:main"].hyps = ["ass:reg"];
  };

  it("rejects the proved shape without the citation_discharged stamp, naming the proved form", () => {
    const plan = makeCitedPlan();
    dischargedShape(plan, false);
    expect(runPlanGate(plan, makeCitedCore()).violations).toContainEqual(
      expect.objectContaining({ code: "P9", where: "lem:borrowed-upper" }),
    );
  });

  it("accepts the stamped discharged form (F1 may plan it), and at F2 requires it to match one sorry-free declaration", () => {
    const plan = makeCitedPlan();
    dischargedShape(plan, true);
    const res = runPlanGate(plan, makeCitedCore());
    expect(res.violations).toEqual([]);
    expect(res.ok).toBe(true);
    const badDecl: ExtractedDecl = {
      nodeId: "lem:borrowed-upper",
      declKind: "theorem",
      declName: "Demo.borrowedUpperDischarge",
      namespace: "Demo",
      file: "BorrowedUpperDischarge.lean",
      statement: "theorem borrowedUpperDischarge : True := by sorry",
      hasSorry: true,
    };
    expect(runPlanGate(plan, makeCitedCore(), { annotatedDecls: [badDecl] }).violations).toContainEqual(
      expect.objectContaining({ code: "P9", where: "lem:borrowed-upper" }),
    );
    expect(runPlanGate(plan, makeCitedCore(), {
      annotatedDecls: [{ ...badDecl, hasSorry: false }],
    }).violations).toEqual([]);
  });

  it("at the scaffold pass a discharged citation may still carry sorry (its proof is F3's); name and kind are still checked", () => {
    const plan = makeCitedPlan();
    dischargedShape(plan, true);
    const decl: ExtractedDecl = {
      nodeId: "lem:borrowed-upper", declKind: "theorem", declName: "Demo.borrowedUpperDischarge", namespace: "Demo",
      file: "BorrowedUpperDischarge.lean", statement: "theorem borrowedUpperDischarge : True := by sorry", hasSorry: true,
    };
    expect(runPlanGate(plan, makeCitedCore(), { annotatedDecls: [decl], proofsNotDue: true }).violations).toEqual([]);
    expect(runPlanGate(plan, makeCitedCore(), { annotatedDecls: [{ ...decl, declName: "Demo.other" }], proofsNotDue: true }).violations).toContainEqual(
      expect.objectContaining({ code: "P9", where: "lem:borrowed-upper" }),
    );
  });
});

describe("F1 plan gate — P11 hygiene (the plan is not a log)", () => {
  const bloated = () => {
    const plan = makePlan() as Record<string, any>;
    plan.decisions = ["Core revision 3 (CURRENT; supersedes revision 2)"];
    plan.env[0].notes = "w".repeat(PLAN_NOTES_MAX + 1);
    plan.nodes["thm:main"].notes = "h".repeat(PLAN_NOTES_MAX + 500);
    plan.nodes["thm:main"].archived_removed_entry_ass_x = { lean_name: "gone" };
    plan.nodes["thm:main"].rev3 = "CURRENT";
    plan.nodes["ass:overlap"].rekeyed_from = "ass:pin-1";
    plan.nodes["ass:consistency"].notes = "n".repeat(PLAN_NOTES_MAX);
    plan.nodes["ass:consistency"].classification = "modeling assumption";
    plan.nodes["ass:ignorability"].external_hyps = [];
    return plan;
  };

  it("names, per offender, each key the schema does not define and a note over the cap, and says what to do", () => {
    const vs = planHygieneViolations(bloated());
    expect(vs.every((v) => v.code === "P11")).toBe(true);
    expect(vs.map((v) => v.where)).toEqual(["<root>", "S1", "ass:overlap", "thm:main"]);
    const main = vs.find((v) => v.where === "thm:main")!.message;
    expect(main).toContain(`\`notes\` is ${PLAN_NOTES_MAX + 500} characters (cap ${PLAN_NOTES_MAX}): REWRITE it`);
    expect(main).toContain("`archived_removed_entry_ass_x`, `rev3` — DELETE them");
    expect(vs[0]!.message).toContain("`decisions`");
    expect(vs.find((v) => v.where === "ass:overlap")!.message).not.toContain("characters");
    expect(planHygieneViolations(makePlan())).toEqual([]);
  });

  it("is enforced where F1 can act on it (F1's self-check, F1.5's pre-lint) and nowhere else", () => {
    expect(runPlanGate(bloated(), makeCore()).ok).toBe(true);
    const gate = runPlanGate(bloated(), makeCore(), { hygiene: true });
    expect(gate.ok).toBe(false);
    expect([...new Set(codes(gate.violations))]).toEqual(["P11"]);
  });

  it("no F1 prompt asks for a key the gate refuses, and a plan from when one did is not bounced for it", () => {
    for (const name of ["stage1_template.txt", "stage1_head_revise.txt"]) {
      const text = readFileSync(fileURLToPath(new URL(`../../src/formalization/prompts/F1/${name}`, import.meta.url)), "utf8");
      expect(text).not.toContain("infrastructure_needed");
    }
    expect(Object.keys(PlanSchema.shape)).not.toContain("infrastructure_needed");
    const old = makePlan() as Record<string, any>;
    old.infrastructure_needed = [];
    expect(planHygieneViolations(old)).toEqual([]);
  });

  it("every key a stage writes into an entry is one the schema defines, and the F1 template states the cap", () => {
    const keys = Object.keys(NodeEntrySchema.shape);
    for (const k of ["classification", "citation_discharged", "gate_class", "source", "delivery_reason", "reuse_class"]) expect(keys).toContain(k);
    const template = readFileSync(fileURLToPath(new URL("../../src/formalization/prompts/F1/stage1_template.txt", import.meta.url)), "utf8");
    expect(template).toContain(`at most ${PLAN_NOTES_MAX} characters`);
    expect(template).toContain(`no \`notes\` over ${PLAN_NOTES_MAX} characters`);
  });

  it("the pre-lint sends EVERY hygiene violation back in one correction, past the cap on the other codes", async () => {
    const root = mkdtempSync(path.join(os.tmpdir(), "plan-hygiene-"));
    const core = makeCore();
    (core.statements[0] as { proof_tex?: string }).proof_tex = "by the argument above";
    const plan = makePlan() as Record<string, any>;
    for (let i = 0; i < 60; i += 1) {
      core.assumptions.push({ id: `ass:x${i}`, condition: "c", free_symbols: [], novel: { flag: true, justification: "j" } } as never);
      plan.nodes[`ass:x${i}`] = { lean_kind: "assumption", lean_name: `x${i}`, disposition: "define-local", history: "old" };
    }
    const dir = path.join(root, "runs", "panel_demo");
    mkdirSync(path.join(dir, "discovery"), { recursive: true });
    mkdirSync(path.join(dir, "formalization"), { recursive: true });
    writeFileSync(path.join(dir, "discovery", "core.json"), JSON.stringify(core));
    const planFile = path.join(dir, "formalization", "plan.json");
    writeFileSync(planFile, JSON.stringify(plan));
    const review = await planGatePrelint({ ctx: { repoRoot: root, qid: "panel_demo", dryRun: false, resume: false } as never, state: {} as never }, planFile);
    expect(review?.status).toBe("revise");
    const findings = (review as { perItemFindings: Array<{ label: string; verdict: string }> }).perItemFindings;
    expect(findings.filter((f) => f.verdict === "FLAG-P11")).toHaveLength(60);
    expect((review as { verbatim_critique: string }).verbatim_critique).toContain("fix ALL 60 P11 entries in this pass");
  });
});

describe("F1 plan gate — P10 undelivered guard", () => {
  it("rejects undelivered headline/support roles and delivered consumers", () => {
    const plan = makePlan();
    Object.assign(plan.nodes["thm:main"], {
      delivery_role: "headline",
      delivery_status: "undelivered",
      delivery_reason: "too hard",
    });
    const res = runPlanGate(plan, makeCore());
    expect(res.violations.some((v) => v.code === "P10" && v.where === "thm:main")).toBe(true);
    expect(res.violations.some((v) => v.code === "P10" && v.where === "oeq:tight")).toBe(true);
  });
});

describe("plan rewrite for declarations that exist upstream (plan/discharge.ts)", () => {
  it("points an ordinary node at the declaration as a reuse; a cited gate takes the proved form P9 accepts, and both leave every hyps list", () => {
    const plan = makeCitedPlan();
    const nodes = plan.nodes as Record<string, Record<string, unknown>>;
    nodes["lem:helper"] = { lean_kind: "lemma", lean_name: "helper", disposition: "define-local", target_file: "Basic.lean", hyps: ["ass:reg"] };
    plan.nodes["thm:main"].hyps.push("lem:helper");
    expect(applyBuiltDeclsToPlan(plan, [
      { gate_id: "lem:helper", decl_name: "Toolkit.helper", module: "Toolkit.Helpers" },
      { gate_id: "lem:borrowed-upper", decl_name: "Toolkit.borrowedUpper", module: "Toolkit.Rates", note: "round-A duplicate" },
    ])).toBe(true);
    expect(nodes["lem:helper"]).toMatchObject({ lean_kind: "lemma", disposition: "reuse", reuse: "Toolkit.helper", modules: ["Toolkit.Helpers"], defer_tier: false });
    const cited = plan.nodes["lem:borrowed-upper"] as Record<string, unknown>;
    expect(cited).toMatchObject({ lean_kind: "lemma", disposition: "define-local", reuse: null, citation_discharged: true, source: "cite:bk2022", defer_tier: false });
    expect(cited.gate).toBeUndefined();
    expect(cited.gate_class).toBeUndefined();
    expect(cited.notes).toBe("proved locally from Toolkit.borrowedUpper (Toolkit.Rates) | round-A duplicate");
    expect(plan.nodes["thm:main"].hyps).toEqual(["ass:reg"]);
    // the rewritten plan passes the gate — the cited node's shape was the P9 refusal before
    // (the helper is not a core node; it only exercised the hyps drop)
    delete nodes["lem:helper"];
    expect(runPlanGate(plan, makeCitedCore()).violations).toEqual([]);
    expect(applyBuiltDeclsToPlan({}, [])).toBe(false);
  });
});
