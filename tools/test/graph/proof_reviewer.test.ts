import { afterAll, beforeAll, describe, it, expect } from "vitest";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addEdge, addNode, addAssumption, setLean } from "../../src/graph/mutate.js";
import { graphDerivedSkeleton } from "../../src/graph/skeleton.js";
import { runReviewer, gradeReviewerOutput, reviewerEscalations } from "../../src/formalization/proof_reviewer.js";
import { pipelineLogPath, planPath, statePath } from "../../src/paths.js";
import { setClaudeRolesForTest } from "../../src/claude_roles.js";
import { runClaude, runClaudeRoleOnCodex } from "../../src/workers/claude.js";
import { MODELS } from "../../src/models.js";
import { loadPartialReceipts, partialReceiptsPath } from "../../src/formalization/convergence_evidence.js";
import { parseStatementFingerprints, type StatementFingerprints } from "../../src/formalization/statement_fingerprints.js";
import { auditCitedReview, citedLeanEvidence } from "../../src/formalization/delivery_audit.js";
import { readTypedCore } from "../../src/core/core_io.js";
import { PlanSchema } from "../../src/formalization/plan/schema.js";

function fixture() {
  let g = createEmptyGraph("q");
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "rate", tex_anchor: "" });
  g = { ...g, nodes: g.nodes.map((n) => (n.id === "t1" ? { ...n, lean: { decl_name: "t1_thm", file: "T1.lean" } } : n)) };
  g = addAssumption(g, { node: "t1", id: "a2", statement: "the hard rate bound", tier: 2, classification: "regularity-bookkeeping", anchor: "", provenance: "agent-introduced" });
  g = setLean(g, "a2", "a2_assumption", "T1.lean");
  return g;
}

// repoRoot is set to a real writable tmpdir in beforeAll below: the reviewer now
// dispatches through the framework boundary (dispatchAgent/dispatchClaudeAgent),
// which appends a dispatch/dispatch-complete pair to <repoRoot>/.../pipeline.jsonl
// before/after each call — an unwritable fake root like "/repo" trips EACCES on that mkdir.
let ctx = { repoRoot: "/repo", qid: "q" };
const minimalCore = (symbols: unknown[] = []) => ({
  qid: "q",
  symbols,
  assumptions: [],
  definitions: [],
  statements: [],
  target_estimand: "test estimand",
  bibliography: [],
});
let sharedCoreRoot = "";
let sharedCorePath = "";
const sharedPromptPath = join(process.cwd(), "src/formalization/prompts/F4/proof_reviewer.txt");

beforeAll(async () => {
  sharedCoreRoot = await mkdtemp(join(tmpdir(), "proof-reviewer-core-"));
  sharedCorePath = join(sharedCoreRoot, "core.json");
  await writeFile(sharedCorePath, JSON.stringify(minimalCore()));
  await writeFile(join(sharedCoreRoot, "T1.lean"), [
    "theorem t1_thm : True := by trivial",
    "def a2_assumption : Prop := True",
    "lemma l1_lemma : True := by trivial",
    "def d1_def : Prop := True",
  ].join("\n"));
  ctx = { repoRoot: sharedCoreRoot, qid: "q" };
});

afterAll(async () => {
  await rm(sharedCoreRoot, { recursive: true, force: true });
});

describe("runReviewer", () => {
  // Reviewer target resolution fails closed BEFORE any model call: an ambiguous or stale target
  // would write a verdict onto the wrong graph node.
  it.each([
    {
      label: "a non-exact reviewer alias has multiple graph owners",
      symbols: [] as unknown[],
      build: () => {
        let g = createEmptyGraph("q");
        g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "rate", tex_anchor: "" });
        g = addNode(g, { id: "a1", kind: "assumption", provenance: "from-note", nl_statement: "legacy", tex_anchor: "" });
        g = addNode(g, { id: "ass:other", kind: "setup", provenance: "from-note", nl_statement: "core", tex_anchor: "" });
        g = { ...g, nodes: g.nodes.map((n) => n.id === "ass:other" ? { ...n, obj_id: "A-1" } : n) };
        g = setLean(g, "t1", "t1_thm", "T1.lean");
        g = setLean(g, "a1", "a2_assumption", "T1.lean");
        g = addEdge(g, { kind: "proof-uses", from: "t1", to: "a1", source: "declared" });
        return { g, skeleton: graphDerivedSkeleton(g), dirty: ["t1", "a1", "ass:other"] };
      },
      escalate: {
        kind: "ambiguous-review-target-alias",
        reason: 'review target alias "A-1" has multiple graph owners: a1, ass:other',
      },
    },
    {
      label: "a skeleton row is owned by the wrong (stale) graph node",
      symbols: [] as unknown[],
      build: () => {
        const g = fixture();
        const skeleton = graphDerivedSkeleton(g).map((row) =>
          row.obj_id === "T-1" ? { ...row, graph_node_id: "stale-old-node" } : row,
        );
        return { g, skeleton, dirty: ["t1", "a2"] };
      },
      escalate: {
        kind: "review-target-resolution-error",
        reason: 'review skeleton target "T-1" must have exactly one row owned by "t1"; found 1 row(s) owned by stale-old-node',
      },
    },
    {
      label: "a synthetic symbol collides with a requested node's stamped alias",
      symbols: [{ name: "sigma", type: "scale", space: "[0,1]" }] as unknown[],
      build: () => {
        let g = createEmptyGraph("q");
        g = addNode(g, { id: "foo", kind: "definition", provenance: "from-note", nl_statement: "scale", tex_anchor: "" });
        g = { ...g, nodes: g.nodes.map((n) => n.id === "foo" ? { ...n, obj_id: "sym:sigma" } : n) };
        g = setLean(g, "foo", "d1_def", "T1.lean");
        return { g, skeleton: graphDerivedSkeleton(g), dirty: ["foo"] };
      },
      escalate: {
        kind: "ambiguous-review-target-alias",
        reason: 'synthetic symbol target "sym:sigma" collides with requested graph node alias owned by "foo"',
      },
    },
  ])("fails before dispatch, leaving the graph untouched, when $label", async ({ symbols, build, escalate }) => {
    const root = await mkdtemp(join(tmpdir(), "proof-reviewer-alias-"));
    const corePath = join(root, "core.json");
    await writeFile(corePath, JSON.stringify(minimalCore(symbols)));
    const { g, skeleton, dirty } = build();
    const graphBefore = JSON.stringify(g);
    let calls = 0;
    try {
      const r = await runReviewer({
        ctx,
        deps: { runCodex: async () => { calls += 1; return { stdout: "{}", stderr: "" }; } },
        graph: g,
        skeleton,
        dirty,
        hashes: {},
        mode: "delta",
        corePath,
        promptPath: sharedPromptPath,
        leanDir: sharedCoreRoot,
      });
      expect(calls).toBe(0);
      expect(r.ok).toBe(false);
      expect(r.escalate).toEqual(escalate);
      expect(JSON.stringify(r.graph)).toBe(graphBefore);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it("dispatches ONE focused codex call per target, writes matched/drift back, and blocks on a content-gate", async () => {
    const g = fixture();
    const seen: string[] = [];
    const r = await runReviewer({
      ctx,
      deps: {
        runCodex: async ({ prompt }) => {
          // Per-item dispatch: each call must carry EXACTLY one target block (its `### <obj_id> (` header) —
          // never both. A single batched call (the old behavior) would contain both T-1 and A-2.
          const hasT1 = prompt.includes("### T-1 (");
          const hasA2 = prompt.includes("### A-2 (");
          expect([hasT1, hasA2].filter(Boolean)).toHaveLength(1);
          const id = hasT1 ? "T-1" : "A-2";
          seen.push(id);
          const out =
            id === "A-2"
              ? { statement_verdicts: [], assumption_verdicts: [{ obj_id: "A-2", verdict: "content-gate", note: "crux" }], escalate: null }
              : { statement_verdicts: [{ obj_id: "T-1", verdict: "matched", note: "ok" }], assumption_verdicts: [], escalate: null };
          return { stdout: JSON.stringify(out), stderr: "" };
        },
      },
      graph: g,
      skeleton: graphDerivedSkeleton(g),
      dirty: ["t1", "a2"],
      hashes: { t1: "h1", a2: "h2" },
      mode: "delta",
      corePath: sharedCorePath,
      promptPath: sharedPromptPath,
      leanDir: sharedCoreRoot,
    });
    expect(seen.sort()).toEqual(["A-2", "T-1"]); // exactly one call per target
    expect(r.graph.nodes.find((n) => n.id === "t1")!.review.status).toBe("matched");
    expect(r.graph.nodes.find((n) => n.id === "a2")!.review.status).toBe("drift");
    expect(r.blocking).toContain("A-2");
  });

  it("makes both F4 reviewers independently audit an undelivered node and fails if either rejects its secondary role", async () => {
    const root = await mkdtemp(join(tmpdir(), "proof-reviewer-undelivered-"));
    const corePath = join(root, "core.json");
    await writeFile(corePath, JSON.stringify({
      qid: "q",
      tldr: "The headline is theorem t1; the atlas is not advertised as a principal result.",
      honest_scope: "The exact atlas is a secondary diagnostic and no delivered theorem uses it.",
      project_justification: { gap: "missing atlas audit", niche: "secondary diagnostic", fill: "Recover the causal arrow generically." },
      symbols: [],
      assumptions: [],
      definitions: [],
      // proof_tex is required for `proved`: a proved node with no proof renders as an
      // established result with nothing establishing it. Immaterial to what this test
      // exercises (F4 reviewers auditing an UNDELIVERED node's secondary role), but the
      // fixture must be a core the schema accepts.
      statements: [{ id: "thm:atlas", kind: "theorem", statement: "exact real atlas", depends_on: [], status: "proved", proof_tex: "Proof of the atlas." }],
      target_estimand: "causal arrow",
      bibliography: [],
    }));
    const localCtx = { repoRoot: root, qid: "q" };
    const pp = planPath(root, "q");
    await mkdir(join(pp, ".."), { recursive: true });
    await writeFile(pp, JSON.stringify({
      qid: "q",
      env: [],
      nodes: {
        "thm:atlas": {
          lean_kind: "theorem",
          lean_name: "exactRealAtlas",
          disposition: "define-local",
          delivery_role: "secondary",
          delivery_status: "undelivered",
          delivery_reason: "citation instantiation overflow",
        },
      },
      citations: [],
      feasibility: "formalizable-now",
    }));
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "thm:atlas", kind: "theorem", provenance: "from-note", nl_statement: "exact real atlas", tex_anchor: "" });
    g = {
      ...g,
      nodes: g.nodes.map((n) => n.id === "thm:atlas" ? {
        ...n,
        delivery: { status: "undelivered" as const, role: "secondary" as const, reason: "citation instantiation overflow" },
      } : n),
    };
    const prompts: string[] = [];

    try {
      const r = await runReviewer({
        ctx: localCtx,
        deps: {
          runCodex: async ({ prompt }) => {
            prompts.push(prompt);
            return { stdout: JSON.stringify({
              status: "ok",
              statement_verdicts: [{ obj_id: "thm:atlas", verdict: "matched", note: "secondary and unconsumed" }],
              assumption_verdicts: [], substrate_gates: [], escalate: null,
            }), stderr: "" };
          },
          runClaude: async ({ prompt }) => {
            prompts.push(prompt);
            return JSON.stringify({
              status: "flagged",
              statement_verdicts: [{ obj_id: "thm:atlas", verdict: "drift", note: "the core actually advertises it as headline" }],
              assumption_verdicts: [], substrate_gates: [],
              escalate: { kind: "delivery-role-conflict", obj_id: "thm:atlas", reason: "headline omission" },
            });
          },
        },
        graph: g,
        skeleton: graphDerivedSkeleton(g),
        dirty: ["thm:atlas"],
        hashes: {},
        mode: "convergence",
        corePath: corePath,
        promptPath: sharedPromptPath,
      });

      expect(prompts).toHaveLength(2);
      // both peers see the core's own framing of what is headline
      for (const prompt of prompts) {
        expect(prompt).toContain("The headline is theorem t1");
        expect(prompt).toContain("Recover the causal arrow generically");
      }
      expect(r.ok).toBe(false);
      expect(r.blocking).toContain("thm:atlas");
      expect(r.escalate?.kind).toBe("delivery-role-conflict");
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it("reviews a cited non-Prop def by closed payload/source correspondence, not Prop implication", async () => {
    const root = await mkdtemp(join(tmpdir(), "proof-reviewer-cited-metadata-"));
    const localCtx = { repoRoot: root, qid: "q" };
    const pp = planPath(root, "q");
    const corePath = join(root, "core.json");
    await mkdir(join(pp, ".."), { recursive: true });
    await writeFile(corePath, JSON.stringify({
      ...minimalCore(),
      statements: [{
        id: "lem:source-scope", kind: "lemma", statement: "The source studies model X only.",
        depends_on: [], status: "cited",
        source: {
          cite: "source", locator: "Theorem 2", carrier: "bibliographic-metadata",
          verbatim_statement: "The source studies model X only.",
        },
      }],
      bibliography: [{ key: "source", citation: "A (2020), Source" }],
    }));
    await writeFile(pp, JSON.stringify({
      qid: "q",
      env: [],
      nodes: {
        "lem:source-scope": {
          lean_kind: "def",
          lean_name: "SourceScope",
          disposition: "define-local",
          gate: true,
          gate_class: "cited",
          source: "cite:source",
        },
      },
      citations: [{
        id: "cite:source", title: "Source", authors: "A", year: 2020,
        locator: "Theorem 2", verbatim_statement: "The source studies model X only.",
      }],
      feasibility: "formalizable-now",
    }));
    await writeFile(join(root, "Basic.lean"), 'def SourceScope : List String := ["The source studies model X only"]\n');
    let g = createEmptyGraph("q");
    g = addNode(g, {
      id: "lem:source-scope",
      kind: "gate",
      provenance: "from-note",
      nl_statement: "The source studies model X only.",
      tex_anchor: "",
    });
    g = setLean(g, "lem:source-scope", "SourceScope", "Basic.lean");
    g.nodes[0].gate = { gate_class: "cited", source: "cite:source" };
    const prompts: string[] = [];

    try {
      const result = await runReviewer({
        ctx: localCtx,
        deps: {
          runCodex: async ({ prompt }) => {
            prompts.push(prompt);
            return { stdout: JSON.stringify({
              status: "ok",
              statement_verdicts: [],
              assumption_verdicts: [{
                obj_id: "lem:source-scope",
                verdict: "faithful-refinement",
                note: "closed payload records the frozen scope",
              }],
              substrate_gates: [{
                name: "SourceScope",
                gate_class: "cited",
                source: { cite_id: "cite:source", locator: "Theorem 2" },
                check_status: "cited-verified-attested",
              }],
              escalate: null,
            }), stderr: "" };
          },
        },
        graph: g,
        skeleton: graphDerivedSkeleton(g),
        dirty: ["lem:source-scope"],
        hashes: { "lem:source-scope": "metadata-hash" },
        mode: "delta",
        leanDir: root,
        corePath,
        promptPath: sharedPromptPath,
      });

      expect(prompts).toHaveLength(1);
      expect(result.ok).toBe(true);
      expect(result.citedReviewReceipts?.[0]?.check_status).toBe("cited-verified-attested");
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it("an inline citation (`cited_in`) is matched against the run's file of the cited work, and only for what the passage attributes to it", async () => {
    const root = await mkdtemp(join(tmpdir(), "proof-reviewer-cited-inline-"));
    const pp = planPath(root, "q");
    const corePath = join(root, "core.json");
    const PASSAGE = "Therefore the error is at most twice the transport distance, which is small by the cited bound.";
    await mkdir(join(pp, ".."), { recursive: true });
    await writeFile(corePath, JSON.stringify({
      ...minimalCore(),
      statements: [
        { id: "thm:host", kind: "theorem", statement: "The error is small.", depends_on: ["lem:step"], status: "to-prove" },
        { id: "lem:step", kind: "lemma", statement: PASSAGE, depends_on: [], status: "cited", cited_in: "thm:host", source: { cite: "source", locator: "Theorem 2" } },
      ],
      bibliography: [{ key: "source", citation: "A (2020), Source" }],
    }));
    await writeFile(pp, JSON.stringify({
      qid: "q",
      env: [],
      nodes: { "lem:step": { lean_kind: "assumption", lean_name: "transportBound", disposition: "define-local", gate: true, gate_class: "cited", source: "cite:source" } },
      // a statement the planner typed is not the source of record of an inline citation
      citations: [{ id: "cite:source", title: "Source", authors: "A", year: 2020, locator: "Theorem 2", verbatim_statement: PASSAGE }],
      feasibility: "formalizable-now",
    }));
    await writeFile(join(root, "Basic.lean"), "def transportBound : Prop := True\n");
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "lem:step", kind: "gate", provenance: "from-note", nl_statement: PASSAGE, tex_anchor: "" });
    g = setLean(g, "lem:step", "transportBound", "Basic.lean");
    g.nodes[0].gate = { gate_class: "cited", source: "cite:source" };
    const review = async (): Promise<string> => {
      const prompts: string[] = [];
      await runReviewer({
        ctx: { repoRoot: root, qid: "q" },
        deps: {
          runCodex: async ({ prompt }) => {
            prompts.push(prompt);
            return { stdout: JSON.stringify({
              status: "ok", statement_verdicts: [],
              assumption_verdicts: [{ obj_id: "lem:step", verdict: "faithful-refinement", note: "matches" }],
              substrate_gates: [{ name: "transportBound", gate_class: "cited", source: { cite_id: "cite:source", locator: "Theorem 2" }, check_status: "cited-source-unverifiable" }],
              escalate: null,
            }), stderr: "" };
          },
        },
        graph: g,
        skeleton: graphDerivedSkeleton(g),
        dirty: ["lem:step"],
        hashes: { "lem:step": "inline-hash" },
        mode: "delta",
        leanDir: root,
        corePath,
        promptPath: sharedPromptPath,
      });
      expect(prompts).toHaveLength(1);
      return prompts[0]!;
    };

    try {
      // no file of the cited work in the run: never "attested" on the paper's own passage
      const without = await review();
      expect(without).toContain("INLINE CITATION — the frozen node is a passage of the proof of thm:host, not the cited result's statement. The Lean declaration must state ONLY what the passage attributes to the cited result");
      expect(without).toContain("Whatever else the passage asserts is for thm:host to prove and must NOT be in this declaration");
      expect(without).toContain('(no fetchable source and no verbatim statement — emit check_status "cited-source-unverifiable")');
      expect(without).not.toContain(`~~~~~\n${PASSAGE}`);
      const sources = join(dirname(statePath(root, "q")), "discovery", "cited_sources");
      await mkdir(sources, { recursive: true });
      await writeFile(join(sources, "source.txt"), "Theorem 2. For laws P, Q on a bounded set, W_1(P, Q) <= C t.");
      const withFile = await review();
      expect(withFile).toContain("~~~~~\nTheorem 2. For laws P, Q on a bounded set, W_1(P, Q) <= C t.\n~~~~~");
      expect(withFile).toContain('check_status = "cited-verified-attested"');
      expect(withFile).toContain("source supplied at discovery/cited_sources/source.txt @ Theorem 2");
      // a supplied file may be the whole work, windowed: attested only on a statement the excerpt shows
      expect(withFile).toContain('(EXCERPT of the source supplied for the cited work — locate "Theorem 2" in it. If it is NOT present in this excerpt, emit check_status "cited-source-unverifiable" — do NOT infer a verdict from surrounding text.)\n~~~~~\nTheorem 2.');
      // one rule of equivalence, not two: against what the passage attributes to the cited result
      expect(withFile).toContain("Require logical equivalence to what the frozen node attributes to the cited result (INLINE CITATION below) plus");
      expect(withFile).not.toContain("Require logical equivalence to the frozen node");
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it("fails closed when either F4 peer omits the source-and-locator row for a delivered cited node", async () => {
    const root = await mkdtemp(join(tmpdir(), "proof-reviewer-cited-"));
    const localCtx = { repoRoot: root, qid: "q" };
    const pp = planPath(root, "q");
    await mkdir(join(pp, ".."), { recursive: true });
    await writeFile(pp, JSON.stringify({
      qid: "q",
      env: [],
      nodes: {
        "gate:source": {
          lean_kind: "assumption",
          lean_name: "sourceInterface",
          disposition: "define-local",
          gate: true,
          gate_class: "cited",
          source: "cite:source",
        },
      },
      citations: [{
        id: "cite:source", title: "Source", authors: "A", year: 2020,
        locator: "Theorem 2", verbatim_statement: "For every x, P x.",
      }],
      feasibility: "formalizable-now",
    }));
    await writeFile(join(root, "Basic.lean"), "def sourceInterface : Prop := True\n");
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "gate:source", kind: "gate", provenance: "from-note", nl_statement: "source interface", tex_anchor: "" });
    g = setLean(g, "gate:source", "sourceInterface", "Basic.lean");
    g.nodes[0].gate = { gate_class: "cited", source: "cite:source" };
    const faithful = [{ obj_id: "gate:source", verdict: "faithful-refinement", note: "matches" }];

    try {
      const result = await runReviewer({
        ctx: localCtx,
        deps: {
          runCodex: async () => ({ stdout: JSON.stringify({
            status: "ok",
            statement_verdicts: [], assumption_verdicts: faithful,
            substrate_gates: [{
              name: "sourceInterface", gate_class: "cited",
              source: { cite_id: "cite:source", locator: "Theorem 2" },
              check_status: "cited-verified-attested",
            }],
            escalate: null,
          }), stderr: "" }),
          runClaude: async () => JSON.stringify({
            status: "ok", statement_verdicts: [], assumption_verdicts: faithful,
            substrate_gates: [], escalate: null,
          }),
        },
        graph: g,
        skeleton: graphDerivedSkeleton(g),
        dirty: ["gate:source"],
        hashes: { "gate:source": "h" },
        mode: "convergence",
        leanDir: root,
        corePath: sharedCorePath,
        promptPath: sharedPromptPath,
      });

      expect(result.ok).toBe(false);
      expect(result.blocking).toContain("gate:source");
      expect(result.citedReviewReceipts).toHaveLength(2);
      expect(result.citedReviewReceipts?.find((receipt) => receipt.reviewer === "codex")?.check_status).toBe("cited-verified-attested");
      expect(result.citedReviewReceipts?.find((receipt) => receipt.reviewer === "claude")?.check_status).toBe("missing");
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it("binds successful cited receipts to the post-verdict graph accepted by F5", async () => {
    const root = await mkdtemp(join(tmpdir(), "proof-reviewer-cited-current-"));
    const localCtx = { repoRoot: root, qid: "q" };
    const pp = planPath(root, "q");
    await mkdir(join(pp, ".."), { recursive: true });
    const planJson = {
      qid: "q", env: [],
      nodes: {
        "gate:source": {
          lean_kind: "assumption", lean_name: "sourceInterface", disposition: "define-local",
          gate: true, gate_class: "cited", source: "cite:source",
        },
      },
      citations: [{
        id: "cite:source", title: "Source", authors: "A", year: 2020,
        locator: "Theorem 2", verbatim_statement: "For every x, P x.",
      }],
      feasibility: "formalizable-now",
    };
    await writeFile(pp, JSON.stringify(planJson));
    await writeFile(join(root, "Basic.lean"), "def sourceInterface : Prop := True\n");
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "gate:source", kind: "gate", provenance: "from-note", nl_statement: "source interface", tex_anchor: "" });
    g = setLean(g, "gate:source", "sourceInterface", "Basic.lean");
    g.nodes[0].gate = { gate_class: "cited", source: "cite:source" };
    const peerOutput = JSON.stringify({
      status: "ok",
      statement_verdicts: [],
      assumption_verdicts: [{ obj_id: "gate:source", verdict: "faithful-refinement", note: "matches" }],
      substrate_gates: [{
        name: "sourceInterface", gate_class: "cited",
        source: { cite_id: "cite:source", locator: "Theorem 2" },
        check_status: "cited-verified-attested",
      }],
      escalate: null,
    });

    try {
      const result = await runReviewer({
        ctx: localCtx,
        deps: {
          runCodex: async () => ({ stdout: peerOutput, stderr: "" }),
          runClaude: async () => peerOutput,
        },
        graph: g,
        skeleton: graphDerivedSkeleton(g),
        dirty: ["gate:source"],
        hashes: { "gate:source": "current-hash" },
        mode: "convergence",
        leanDir: root,
        corePath: sharedCorePath,
        promptPath: sharedPromptPath,
      });
      expect(result.ok).toBe(true);
      expect(result.graph.nodes[0].review.passed_hash).toBe("current-hash");
      const parsedPlan = PlanSchema.parse(JSON.parse(await readFile(pp, "utf8")));
      const parsedCore = await readTypedCore(sharedCorePath);
      expect(auditCitedReview({
        core: parsedCore,
        plan: parsedPlan,
        graph: result.graph,
        leanEvidence: await citedLeanEvidence(root, parsedPlan),
        receipts: result.citedReviewReceipts,
      })).toEqual([]);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

});

describe("gradeReviewerOutput — tolerates the schema reviewers actually emit, and never grades a rejection as a pass", () => {
  it.each([
    {
      label: "object rows: prose rejections with a positive root, hedged or retracted positives, negative prefixes, rejecting assumption tokens; kind-less escalate array",
      out: {
        statement_verdicts: [
          { obj_id: "T-1", verdict: "fails to match", note: "reviewer rejected equivalence" },
          { obj_id: "T-2", verdict: "mostly faithful with an important gate/strengthening caveat" },
          { obj_id: "T-3", verdict: "matched — no concerns" },
          { obj_id: "T-4", verdict: "faithful but weakens the theorem" },
          { obj_id: "T-5", verdict: "misaligned" },
        ],
        assumption_verdicts: [
          { obj_id: "A-1", verdict: "derived" },
          { obj_id: "A-2", verdict: "drift", note: "carrier floor smuggled in" },
          { obj_id: "A-3", verdict: "partial" },
          { obj_id: "A-4", verdict: "faithful-refinement" },
          { obj_id: "A-5", verdict: "regularity-bookkeeping" },
          { obj_id: "A-6", verdict: "substrate-gate" },
        ],
        escalate: [{ target: "T-1", reason: "extra witness hyps" }],
      },
      blocking: ["T-1", "T-2", "T-4", "T-5", "A-1", "A-2", "A-3"],
      drift: ["T-1"],
      escalateKind: null,
    },
    {
      label: "bare-string rows ('L-1: faithful. …'); an escalate array item with a real kind",
      out: {
        statement_verdicts: [
          "L-1: faithful. uses the derived ConditionalExchangeability consequence — acceptable.",
          "L-10: drift. the NL is a generic Le Cam bridge; the Lean is a specialized rate theorem.",
          "L-11: partial drift. only tail-bias membership is proven by this anchor.",
        ],
        assumption_verdicts: ["A-1: faithful. unfolds to a genuine CondIndepFun primitive."],
        escalate: [{ kind: "note-wrong", obj_id: "L-10", reason: "tex disagrees" }],
      },
      blocking: ["L-10", "L-11"],
      drift: ["L-10", "L-11"],
      escalateKind: "note-wrong",
    },
    {
      label: "invented compound tokens and `target`/`observation` keys",
      out: {
        statement_verdicts: [
          { target: "L-3", verdict: "factored_equivalent", observation: "faithful as the algebraic core" },
          { obj_id: "L-1", verdict: "aligned", observations: ["consumes the derived consequence"] },
          { obj_id: "T-2", verdict: "drift/conditionalized", note: "extra hyps" },
          { obj_id: "P-9", verdict: "aligned, the Lean uses the derived consequence which is fine" },
        ],
      },
      blocking: ["T-2"],
      drift: ["T-2"],
      escalateKind: null,
    },
  ])("$label", ({ out, blocking, drift, escalateKind }) => {
    const g = gradeReviewerOutput(out as never);
    expect(new Set(g.blocking)).toEqual(new Set(blocking));
    for (const id of drift) expect(g.rows.find((r) => r.obj_id === id)?.verdict).toBe("drift");
    expect(g.escalate?.kind ?? null).toBe(escalateKind);
  });
});

describe("F4 convergence receipts", () => {
  const LEAN = [
    "def helperBound (n : Nat) : Nat := n + 1",
    "-- @node: t1",
    "theorem t1_thm (n : Nat) : helperBound n = n + 1 := by rfl",
    "-- @node: l1",
    "lemma l1_lemma : True := by trivial",
    "-- @node: d1",
    "def d1_def : Prop := True",
  ].join("\n");
  const okVerdict = (prompt: string) => {
    const objId = prompt.match(/### ([^\s(]+) \(/)?.[1];
    return JSON.stringify({ status: "ok", statement_verdicts: objId ? [{ obj_id: objId, verdict: "matched", note: "ok" }] : [], assumption_verdicts: [], substrate_gates: [], escalate: null });
  };
  function graph() {
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "headline claim", tex_anchor: "" });
    g = addNode(g, { id: "l1", kind: "lemma", provenance: "from-note", nl_statement: "routine lemma", tex_anchor: "" });
    g = addNode(g, { id: "d1", kind: "definition", provenance: "from-note", nl_statement: "model-class definition", tex_anchor: "" });
    g = setLean(g, "t1", "t1_thm", "T1.lean");
    g = setLean(g, "l1", "l1_lemma", "T1.lean");
    g = setLean(g, "d1", "d1_def", "T1.lean");
    return g;
  }
  /** What `candidate_scan --fingerprints` reports for the fixture tree. */
  const scanned = parseStatementFingerprints(JSON.stringify({
    declarations: ["helperBound", "t1_thm", "l1_lemma", "d1_def"].map((name) => ({ name, file: "P/T1.lean", closure_hash: `c-${name}` })),
  }), "P");
  async function round(g: ReturnType<typeof graph>, root: string, verdict: (prompt: string, peer: "codex" | "claude") => string = okVerdict, fingerprints: StatementFingerprints | null = scanned) {
    const seen: string[] = [];
    const r = await runReviewer({
      ctx: { repoRoot: root, qid: "q" },
      deps: {
        runCodex: async ({ prompt }) => { seen.push(`codex:${prompt.match(/### ([^\s(]+) \(/)?.[1]}`); return { stdout: verdict(prompt, "codex"), stderr: "" }; },
        runClaude: async ({ prompt }) => { seen.push(`claude:${prompt.match(/### ([^\s(]+) \(/)?.[1]}`); return verdict(prompt, "claude"); },
      },
      graph: g,
      skeleton: graphDerivedSkeleton(g),
      dirty: [],
      hashes: { t1: "h1", l1: "h2", d1: "h3" },
      mode: "convergence",
      corePath: join(root, "core.json"),
      promptPath: sharedPromptPath,
      leanDir: root,
      fingerprints: async () => fingerprints,
    });
    return { r, seen: seen.sort() };
  }
  let root = "";
  beforeAll(async () => {
    root = await mkdtemp(join(tmpdir(), "proof-reviewer-receipts-"));
    await writeFile(join(root, "core.json"), JSON.stringify(minimalCore()));
  });
  afterAll(async () => { await rm(root, { recursive: true, force: true }); });

  it("with the claude roles on codex, the second reviewer is a separate codex call with the same prompt, named as such", async () => {
    const own = await mkdtemp(join(tmpdir(), "proof-reviewer-codex-peer-"));
    await writeFile(join(own, "core.json"), JSON.stringify(minimalCore()));
    await writeFile(join(own, "T1.lean"), LEAN);
    const calls: Array<{ prompt: string; outputSchema?: unknown; sandboxMode?: string; model?: string }> = [];
    const runCodex = async (o: { prompt: string; outputSchema?: unknown; sandboxMode?: string; model?: string }) => { calls.push(o); return { stdout: okVerdict(o.prompt), stderr: "" }; };
    setClaudeRolesForTest({ runner: "codex", explicit: false, reason: "its CLI is not installed" });
    try {
      const r = await runReviewer({
        ctx: { repoRoot: own, qid: "q" },
        deps: {
          runCodex: runCodex as never,
          runClaude: (o) => runClaude(o, { runner: () => "codex", claude: async () => { throw new Error("the claude CLI must not be called"); }, codex: (i) => runClaudeRoleOnCodex(i, runCodex as never) }),
        },
        graph: graph(),
        skeleton: graphDerivedSkeleton(graph()),
        dirty: [],
        hashes: { t1: "h1", l1: "h2", d1: "h3" },
        mode: "convergence",
        corePath: join(own, "core.json"),
        promptPath: sharedPromptPath,
        leanDir: own,
        fingerprints: async () => scanned,
      });
      expect(r.ok).toBe(true);
      // every unit: the first reviewer's call (schema-constrained), then the second's — its own call, the same prompt
      const unit = (c: { prompt: string }) => c.prompt.match(/### ([^\s(]+) \(/)?.[1];
      expect(calls.map(unit).sort()).toEqual(["L-1", "L-1", "T-1", "T-1", "d1", "d1"]);
      const t1 = calls.filter((c) => unit(c) === "T-1");
      expect(t1[1]!.prompt).toBe(t1[0]!.prompt);
      expect(t1.map((c) => Boolean(c.outputSchema))).toEqual([true, false]);
      expect(t1[1]).toMatchObject({ sandboxMode: "read-only", model: MODELS.codexKernel });
      // both receipts are written, in the same two slots the merge reads
      expect(Object.keys(r.graph.convergenceReview!.t1).sort()).toEqual(["claude", "codex"]);
      const log = await readFile(pipelineLogPath(own, "q"), "utf8");
      expect(log).toContain("F4 convergence second codex reviewer :: ");
      expect(log).not.toContain("claude reviewer");
      expect(log.split("\n").filter(Boolean).map((l) => JSON.parse(l).model)).toEqual(Array(12).fill(MODELS.codexKernel));
    } finally {
      setClaudeRolesForTest(null);
      await rm(own, { recursive: true, force: true });
    }
  });

  it("round 1 dual-reviews everything and writes both receipts; an unchanged round 2 spends no model call", async () => {
    await writeFile(join(root, "T1.lean"), LEAN);
    const one = await round(graph(), root);
    expect(one.r.ok).toBe(true);
    expect(one.seen).toEqual(["claude:L-1", "claude:T-1", "claude:d1", "codex:L-1", "codex:T-1", "codex:d1"]);
    const ledger = one.r.graph.convergenceReview!;
    expect(Object.keys(ledger).sort()).toEqual(["d1", "l1", "t1"]);
    for (const id of ["t1", "l1", "d1"]) {
      expect(ledger[id].codex?.verdict).toBe("matched");
      expect(ledger[id].claude?.verdict).toBe("matched");
      expect(ledger[id].codex?.evidence_hash).toBe(ledger[id].claude?.evidence_hash);
    }
    const two = await round(one.r.graph, root);
    expect(two.seen).toEqual([]);
    expect(two.r.ok).toBe(true);
    expect(two.r.graph.convergenceReview).toEqual(ledger);
  });

  it("without statement fingerprints nothing is skipped and no receipt is issued", async () => {
    await writeFile(join(root, "T1.lean"), LEAN);
    const done = await round(graph(), root);
    const blind = await round(done.r.graph, root, okVerdict, null);
    expect(blind.seen).toHaveLength(6);
    expect(blind.r.ok).toBe(true);
    expect(blind.r.graph.convergenceReview).toEqual({});
    // one declaration the scan does not report: that target alone is reviewed, and holds no receipt
    const partial = parseStatementFingerprints(JSON.stringify({
      declarations: ["t1_thm", "d1_def"].map((name) => ({ name, file: "P/T1.lean", closure_hash: `c-${name}` })),
    }), "P");
    const one = await round(done.r.graph, root, okVerdict, partial);
    expect(one.seen).toEqual(["claude:L-1", "codex:L-1"]);
    expect(Object.keys(one.r.graph.convergenceReview!).sort()).toEqual(["d1", "t1"]);
  });

  it("a unit whose worker dies is reported, not thrown: the receipts the other units issued are kept and the next pass reviews only the rest", async () => {
    await writeFile(join(root, "T1.lean"), LEAN);
    await mkdir(dirname(statePath(root, "q")), { recursive: true });
    const done = await round(graph(), root);
    // the same graph with no ledger: every target is due
    const due = { ...done.r.graph, convergenceReview: undefined };
    const died = await round(due, root, (prompt, peer) => {
      if (peer === "claude" && /### T-1 \(/.test(prompt)) throw new Error("worker killed: inactivity timeout");
      return okVerdict(prompt);
    });
    // one watchdog kill used to reject the whole wave, discarding the sibling units' paid verdicts
    expect(died.r.failedUnits).toEqual([expect.objectContaining({ targets: ["T-1"], error: expect.stringContaining("inactivity timeout") })]);
    expect(died.r.blocking).toEqual([]); // a worker failure is not a finding on T-1
    expect(Object.keys(died.r.graph.convergenceReview!).sort()).toEqual(["d1", "l1"]);
    // the pass ran to its end: nothing is left beside the run
    expect(await loadPartialReceipts(dirname(statePath(root, "q")))).toEqual({});
    const next = await round(died.r.graph, root);
    expect(next.seen).toEqual(["claude:T-1", "codex:T-1"]);
    expect(next.r.ok).toBe(true);
    expect(Object.keys(next.r.graph.convergenceReview!).sort()).toEqual(["d1", "l1", "t1"]);
  });

  it("a pass that died after its last receipt, before the graph was saved: the next pass spends no model call and the graph holds every receipt", async () => {
    await writeFile(join(root, "T1.lean"), LEAN);
    const runDir = dirname(statePath(root, "q"));
    await mkdir(runDir, { recursive: true });
    const done = await round(graph(), root);
    // every receipt is beside the run, none in the graph
    await writeFile(partialReceiptsPath(runDir), JSON.stringify(done.r.graph.convergenceReview));
    const next = await round({ ...done.r.graph, convergenceReview: undefined }, root);
    expect(next.seen).toEqual([]);
    expect(next.r.ok).toBe(true);
    expect(next.r.graph.convergenceReview).toEqual(done.r.graph.convergenceReview);
    expect(await loadPartialReceipts(runDir)).toEqual({});
    // one receipt beside the run, the others already in the graph
    const full = done.r.graph.convergenceReview!;
    await writeFile(partialReceiptsPath(runDir), JSON.stringify({ t1: full.t1 }));
    const mixed = await round({ ...done.r.graph, convergenceReview: { l1: full.l1, d1: full.d1 } }, root);
    expect(mixed.seen).toEqual([]);
    expect(mixed.r.graph.convergenceReview).toEqual(full);
  });

  it("a target one peer flagged is re-reviewed next round; a delta `matched` with no ledger never clears", async () => {
    await writeFile(join(root, "T1.lean"), LEAN);
    const one = await round(graph(), root, (prompt, peer) => {
      const objId = prompt.match(/### ([^\s(]+) \(/)?.[1];
      const bad = peer === "claude" && objId === "L-1";
      return JSON.stringify({ status: bad ? "flagged" : "ok", statement_verdicts: [{ obj_id: objId, verdict: bad ? "drift" : "matched", note: bad ? "weaker" : "ok" }], assumption_verdicts: [], substrate_gates: [], escalate: null });
    });
    expect(one.r.ok).toBe(false);
    expect(one.r.blocking).toEqual(["L-1"]);
    expect(one.r.graph.convergenceReview!.l1.claude?.verdict).toBe("drift");
    // Delta later re-marks l1 matched at the same text (a reviewer flip); F4 must still dual-review it.
    let g = one.r.graph;
    g = { ...g, nodes: g.nodes.map((n) => (n.id === "l1" ? { ...n, review: { status: "matched" as const, passed_hash: "h2" } } : n)) };
    const two = await round(g, root);
    expect(two.seen).toEqual(["claude:L-1", "codex:L-1"]);
    expect(two.r.ok).toBe(true);
    // And a graph that carries no ledger at all reviews everything, whatever delta says.
    const fresh = await round(graph(), root);
    expect(fresh.seen).toHaveLength(6);
  });

});

describe("one review pass reports every unit's escalation", () => {
  it("runReviewer returns the escalations of every per-node unit of a delta pass", async () => {
    let g = createEmptyGraph("q");
    for (const id of ["t1", "t2"]) {
      g = addNode(g, { id, kind: "theorem", provenance: "from-note", nl_statement: `claim ${id}`, tex_anchor: "" });
      g = setLean(g, id, "t1_thm", "T1.lean");
    }
    const r = await runReviewer({
      ctx,
      deps: { runCodex: async (o) => {
        const id = String((o as { prompt?: string }).prompt ?? "").includes("### T-2") ? "T-2" : "T-1";
        return { stdout: JSON.stringify({
          status: "flagged",
          statement_verdicts: [{ obj_id: id, verdict: "drift", note: "n" }],
          assumption_verdicts: [],
          substrate_gates: [],
          escalate: { kind: "statement-wrong", obj_id: id, reason: `the frozen wording of ${id} permits both readings` },
        }), stderr: "" };
      } },
      graph: g,
      skeleton: graphDerivedSkeleton(g),
      dirty: ["t1", "t2"],
      hashes: {},
      mode: "delta",
      corePath: sharedCorePath,
      promptPath: sharedPromptPath,
      leanDir: sharedCoreRoot,
    });
    expect(r.escalate).not.toBeNull();
    expect(reviewerEscalations(r).map((e) => e.obj_id).sort()).toEqual(["T-1", "T-2"]);
  });
});

describe("the reviewer reads the pinned readings", () => {
  it("each target shows its binding readings under its NL, and an escalation carries them", async () => {
    const { PINNED_CORE } = await import("../verify/fixtures/pinned_core.js");
    const dir = await mkdtemp(join(tmpdir(), "reviewer-pins-"));
    try {
      const corePath = join(dir, "core.json");
      await writeFile(corePath, JSON.stringify(PINNED_CORE));
      await writeFile(join(dir, "T1.lean"), "theorem t1_thm : True := by trivial\n");
      let g = createEmptyGraph("q");
      g = addNode(g, { id: "thm:scale", kind: "theorem", provenance: "from-note", nl_statement: "Under strictly increasing CDFs, a transformation g exists.", tex_anchor: "" });
      g = setLean(g, "thm:scale", "t1_thm", "T1.lean");
      const prompts: string[] = [];
      const r = await runReviewer({
        ctx: { repoRoot: dir, qid: "q" },
        deps: { runCodex: async (o) => {
          prompts.push(String((o as { prompt?: string }).prompt ?? ""));
          return { stdout: JSON.stringify({
            status: "flagged",
            statement_verdicts: [{ obj_id: "thm:scale", verdict: "drift", note: "n" }],
            assumption_verdicts: [], substrate_gates: [],
            escalate: { kind: "statement-wrong", obj_id: "thm:scale", reason: "'strictly increasing' admits two readings; specify the domain" },
          }), stderr: "" };
        } },
        graph: g,
        skeleton: graphDerivedSkeleton(g),
        dirty: ["thm:scale"],
        hashes: {},
        mode: "delta",
        corePath,
        promptPath: sharedPromptPath,
        leanDir: dir,
      });
      const target = prompts.find((p) => p.includes("### thm:scale"))!;
      // The readings are rendered ONCE per prompt (a batch of one result's assumptions used to carry
      // them once per target); each target's block points at them.
      expect(target).toMatch(/Under strictly increasing CDFs, a transformation g exists\.\nPinned readings: listed once under PINNED READINGS \(binding\) below, for thm:scale\./);
      expect(target).toMatch(/PINNED READINGS \(binding[^\n]*\n• for thm:scale: Pinned readings \(binding\): ass:pin-1 \(reading of thm:scale\): F_1\(y\) < F_0\(y\) at every finite interior point/);
      expect(r.escalate?.pinned).toEqual([expect.stringContaining("ass:pin-1 (reading of thm:scale)"), expect.stringContaining("ass:bk-1")]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});

describe("the reviewer reads a result the target defers to", () => {
  it("a target whose NL names another result by reference carries that result's statement on its page", async () => {
    const { PINNED_CORE } = await import("../verify/fixtures/pinned_core.js");
    const dir = await mkdtemp(join(tmpdir(), "reviewer-refs-"));
    try {
      const core = structuredClone(PINNED_CORE) as typeof PINNED_CORE;
      const scale = core.statements.find((st) => st.id === "thm:scale")!;
      scale.tex_locator = { ...(scale.tex_locator ?? { file: "main.tex", from: 1, to: 2, env: "theorem" }), label: "thm:scale-label" } as typeof scale.tex_locator;
      await writeFile(join(dir, "core.json"), JSON.stringify(core));
      await writeFile(join(dir, "T1.lean"), "theorem t1_thm : True := by trivial\n");
      let g = createEmptyGraph("q");
      g = addNode(g, { id: "ass:deferred", kind: "assumption", provenance: "from-note", nl_statement: "The conditions of Theorem~\\ref{thm:scale-label} hold, and those of~\\ref{sec:elsewhere}.", tex_anchor: "" });
      g = addNode(g, { id: "thm:scale", kind: "theorem", provenance: "from-note", nl_statement: "See~\\ref{thm:scale-label}.", tex_anchor: "" });
      g = setLean(g, "thm:scale", "t1_thm", "T1.lean");
      const prompts: string[] = [];
      await runReviewer({
        ctx: { repoRoot: dir, qid: "q" },
        deps: { runCodex: async (o) => {
          prompts.push(String((o as { prompt?: string }).prompt ?? ""));
          return { stdout: JSON.stringify({ status: "ok", statement_verdicts: [], assumption_verdicts: [], substrate_gates: [], escalate: null }), stderr: "" };
        } },
        graph: g,
        skeleton: graphDerivedSkeleton(g),
        dirty: ["ass:deferred", "thm:scale"],
        hashes: {},
        mode: "delta",
        corePath: join(dir, "core.json"),
        promptPath: sharedPromptPath,
        leanDir: dir,
      });
      const deferred = prompts.find((p) => p.includes("### ass:deferred"))!;
      // the typed core is named, to be opened when the page does not settle a question
      expect(deferred).toContain(`- Typed core (the spec of record, JSON): ${join(dir, "core.json")} — open it WHEN NECESSARY`);
      expect(deferred).toContain("REFERENCED RESULTS");
      expect(deferred).toContain("\\ref{thm:scale-label}:\n~~~~~\n" + scale.statement);
      expect(deferred).not.toContain("\\ref{sec:elsewhere}:");
      // A result's own label is not a deferral.
      expect(prompts.find((p) => p.includes("### thm:scale") && !p.includes("### ass:deferred"))).not.toContain("REFERENCED RESULTS");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});

describe("hypotheses added to a paper statement since it last passed", () => {
  it("a pass records the statement's binders; the next pass names each new one and what was disclosed", async () => {
    const dir = await mkdtemp(join(tmpdir(), "reviewer-added-"));
    try {
      await writeFile(join(dir, "core.json"), JSON.stringify(minimalCore()));
      const lean = (extra: string) => `/-- doc (h : ignored) -/\ntheorem t1_thm (n : Nat) (hn : 0 < n)${extra} : n ≠ 0 := by\n  omega\n`;
      await writeFile(join(dir, "T1.lean"), lean(""));
      let g = createEmptyGraph("q");
      g = addNode(g, { id: "thm:t", kind: "theorem", provenance: "from-note", nl_statement: "every positive n is nonzero", tex_anchor: "" });
      g = setLean(g, "thm:t", "t1_thm", "T1.lean");
      const prompts: string[] = [];
      const review = (graph: typeof g) => runReviewer({
        ctx: { repoRoot: dir, qid: "q" },
        deps: { runCodex: async (o) => {
          prompts.push(String((o as { prompt?: string }).prompt ?? ""));
          return { stdout: JSON.stringify({ status: "ok", statement_verdicts: [{ obj_id: "thm:t", verdict: "matched", note: "n" }], assumption_verdicts: [], substrate_gates: [], escalate: null }), stderr: "" };
        } },
        graph,
        skeleton: graphDerivedSkeleton(graph),
        dirty: ["thm:t"],
        hashes: {},
        mode: "delta",
        corePath: join(dir, "core.json"),
        promptPath: sharedPromptPath,
        leanDir: dir,
      });
      // First pass: no record yet, so no diff — the whole statement is judged; its binders are recorded.
      const first = await review(g);
      expect(prompts.some((p) => p.includes("HYPOTHESES ADDED"))).toBe(false);
      expect(first.graph.nodes.find((n) => n.id === "thm:t")!.passed_binders).toEqual(["(n : Nat)", "(hn : 0 < n)"]);

      // An agent adds a binder (and discloses one assumption for the result); the next pass names it.
      await writeFile(join(dir, "T1.lean"), lean("\n    (hcount : n = n + 0)"));
      const g2 = addAssumption(first.graph, { node: "thm:t", id: "ass:filler:x", statement: "the count identity", tier: 2, classification: "substrate-gate", anchor: "", provenance: "agent-introduced" });
      prompts.length = 0;
      const second = await review(g2);
      const target = prompts.find((p) => p.includes("### thm:t"))!;
      expect(target).toContain("HYPOTHESES ADDED SINCE THIS STATEMENT LAST PASSED REVIEW");
      expect(target).toContain("  • (hcount : n = n + 0)");
      expect(target).not.toContain("  • (hn : 0 < n)");
      expect(target).toContain("ass:filler:x (substrate-gate): the count identity");
      // Passing again moves the record to the new signature.
      expect(second.graph.nodes.find((n) => n.id === "thm:t")!.passed_binders).toEqual(["(n : Nat)", "(hn : 0 < n)", "(hcount : n = n + 0)"]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});

describe("review basis — a drift node is not re-dispatched on an unchanged page", () => {
  const drift = { statement_verdicts: [{ obj_id: "T-1", verdict: "drift", note: "H7 missing" }], assumption_verdicts: [], substrate_gates: [], escalate: null };
  function driftGraph() {
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "rate", tex_anchor: "" });
    g = setLean(g, "t1", "t1_thm", "T1.lean");
    return { ...g, nodes: g.nodes.map((n) => (n.id === "t1" ? { ...n, review: { status: "drift" as const, passed_hash: "h1", note: "stale note" } } : n)) };
  }
  async function pass(g: ReturnType<typeof driftGraph>, reviewBasis: Record<string, { basis: string; reviews: number }> | undefined, opts: { rereviewUnchanged?: boolean; dirty?: string[] } = {}) {
    const prompts: string[] = [];
    let schema: unknown;
    const r = await runReviewer({
      ctx,
      deps: { runCodex: async (o) => { prompts.push(o.prompt); schema = o.outputSchema; return { stdout: JSON.stringify(drift), stderr: "" }; } },
      graph: g, skeleton: graphDerivedSkeleton(g), dirty: opts.dirty ?? [], hashes: { t1: "h1" }, mode: "delta",
      corePath: sharedCorePath, promptPath: sharedPromptPath, leanDir: sharedCoreRoot,
      reviewBasis, rereviewUnchanged: opts.rereviewUnchanged,
    });
    return { r, prompts, schema };
  }

  it("reviews once per basis; the standing verdict and its note hold after that; the resume after a hint halt gets one more review, never a third", async () => {
    const one = await pass(driftGraph(), undefined);
    expect(one.prompts).toHaveLength(1);
    expect(one.r.reviewBasis?.t1.reviews).toBe(1);
    expect(one.r.graph.nodes.find((n) => n.id === "t1")!.review).toMatchObject({ status: "drift", note: "H7 missing" });
    // the same page again: no dispatch, the standing drift blocks with the persisted note
    const two = await pass(one.r.graph, one.r.reviewBasis);
    expect(two.prompts).toHaveLength(0);
    expect(two.r.ok).toBe(false);
    expect(two.r.standing).toEqual(["T-1"]);
    expect(two.r.blocking).toEqual(["T-1"]);
    expect(two.r.driftNotes).toEqual({ "T-1": "H7 missing" });
    expect(two.r.reviewBasis?.t1.reviews).toBe(1);
    // the reviewer-flip re-review: exactly one more on the unchanged basis
    const three = await pass(one.r.graph, one.r.reviewBasis, { rereviewUnchanged: true });
    expect(three.prompts).toHaveLength(1);
    expect(three.r.reviewBasis?.t1.reviews).toBe(2);
    const four = await pass(three.r.graph, three.r.reviewBasis, { rereviewUnchanged: true });
    expect(four.prompts).toHaveLength(0);
    expect(four.r.standing).toEqual(["T-1"]);
    // a hash-dirty node (its Lean changed) is always reviewed
    const dirty = await pass(three.r.graph, three.r.reviewBasis, { dirty: ["t1"] });
    expect(dirty.prompts).toHaveLength(1);
  });

  // live wss, tbs: the scaffolder's fix landed two definitions below the tagged one; the page (one
  // hop) was unchanged, the stale drift stood, and the node spent its strikes
  it("a change two definitions below the target changes the basis, so the standing drift is reviewed again", async () => {
    const dir = await mkdtemp(join(tmpdir(), "proof-reviewer-deep-"));
    const lean = (inner: string) => ["def innerPred (n : Nat) : Prop := " + inner, "def outerPred (n : Nat) : Prop := innerPred n", "theorem t1_thm : outerPred 0 := by sorry"].join("\n");
    try {
      await writeFile(join(dir, "core.json"), JSON.stringify(minimalCore()));
      await writeFile(join(dir, "T1.lean"), lean("n = n"));
      const run = async (g: ReturnType<typeof driftGraph>, reviewBasis?: Record<string, { basis: string; reviews: number }>) => {
        let calls = 0;
        const r = await runReviewer({
          ctx: { repoRoot: dir, qid: "q" },
          deps: { runCodex: async () => { calls += 1; return { stdout: JSON.stringify(drift), stderr: "" }; } },
          graph: g, skeleton: graphDerivedSkeleton(g), dirty: [], hashes: { t1: "h1" }, mode: "delta",
          corePath: join(dir, "core.json"), promptPath: sharedPromptPath, leanDir: dir, reviewBasis,
        });
        return { r, calls };
      };
      const one = await run(driftGraph());
      expect(one.calls).toBe(1);
      expect((await run(one.r.graph, one.r.reviewBasis)).calls).toBe(0);
      await writeFile(join(dir, "T1.lean"), lean("0 ≤ n"));
      expect((await run(one.r.graph, one.r.reviewBasis)).calls).toBe(1);
      // a definition past the one-hop cap (12) is on no page, and still in the basis
      const wide = (last: string) => [`theorem t1_thm : ${Array.from({ length: 14 }, (_, i) => `p${i}`).join(" ∧ ")} := by sorry`, ...Array.from({ length: 14 }, (_, i) => `def p${i} : Prop := ${i === 13 ? last : "True"}`)].join("\n");
      await writeFile(join(dir, "T1.lean"), wide("True"));
      const w1 = await run(driftGraph());
      expect((await run(w1.r.graph, w1.r.reviewBasis)).calls).toBe(0);
      await writeFile(join(dir, "T1.lean"), wide("1 = 1"));
      expect((await run(w1.r.graph, w1.r.reviewBasis)).calls).toBe(1);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  // A graph row has no line: the target's span was read from the head of its file, so what the
  // target itself refers to was neither unfolded nor in the basis unless the file began with it.
  it("a rewritten definition the target is an alias of changes the basis wherever the target sits in its file", async () => {
    const dir = await mkdtemp(join(tmpdir(), "proof-reviewer-alias-"));
    const lean = (helper: string) => [
      "namespace Papers.Q",
      "variable (k : Nat)",
      "def unrelated : Prop := True",
      "def helperPred (n : Nat) : Prop := " + helper,
      "-- @node: t1",
      "theorem t1_thm : helperPred 0 := by sorry",
      "end Papers.Q",
    ].join("\n");
    try {
      await writeFile(join(dir, "core.json"), JSON.stringify(minimalCore()));
      await writeFile(join(dir, "T1.lean"), lean("n = n"));
      const run = async (g: ReturnType<typeof driftGraph>, reviewBasis?: Record<string, { basis: string; reviews: number }>) => {
        const prompts: string[] = [];
        const r = await runReviewer({
          ctx: { repoRoot: dir, qid: "q" },
          deps: { runCodex: async (o) => { prompts.push(o.prompt); return { stdout: JSON.stringify(drift), stderr: "" }; } },
          graph: g, skeleton: graphDerivedSkeleton(g), dirty: [], hashes: { t1: "h1" }, mode: "delta",
          corePath: join(dir, "core.json"), promptPath: sharedPromptPath, leanDir: dir, reviewBasis,
        });
        return { r, prompts };
      };
      const one = await run(setLean(driftGraph(), "t1", "Papers.Q.t1_thm", "T1.lean") as ReturnType<typeof driftGraph>);
      expect(one.prompts).toHaveLength(1);
      expect(one.prompts[0]).toContain("def helperPred (n : Nat) : Prop := n = n");
      expect(one.prompts[0]).not.toContain("def unrelated");
      expect((await run(one.r.graph, one.r.reviewBasis)).prompts).toHaveLength(0);
      await writeFile(join(dir, "T1.lean"), lean("0 ≤ n"));
      expect((await run(one.r.graph, one.r.reviewBasis)).prompts).toHaveLength(1);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  /** One delta pass over `files` for the drift theorem anchored at `decl` in `file`: the names the page unfolds, and the result. */
  async function unfolded(dir: string, files: Record<string, string>, decl: string, file: string, prior?: Awaited<ReturnType<typeof runReviewer>>) {
    await writeFile(join(dir, "core.json"), JSON.stringify(minimalCore()));
    for (const [name, text] of Object.entries(files)) await writeFile(join(dir, name), text);
    const g = prior?.graph ?? setLean(driftGraph(), "t1", decl, file);
    const prompts: string[] = [];
    const r = await runReviewer({
      ctx: { repoRoot: dir, qid: "q" },
      deps: { runCodex: async (o) => { prompts.push(o.prompt); return { stdout: JSON.stringify(drift), stderr: "" }; } },
      graph: g, skeleton: graphDerivedSkeleton(g), dirty: [], hashes: { t1: "h1" }, mode: "delta",
      corePath: join(dir, "core.json"), promptPath: sharedPromptPath, leanDir: dir, reviewBasis: prior?.reviewBasis,
    });
    const names = prompts[0]?.match(/Referenced definitions \(unfolded once[^\n]*: ([^\n]*)/)?.[1].split(", ") ?? [];
    return { r, prompts, names };
  }

  it("a definition the target reaches only through a section variable is on the page and in the basis", async () => {
    const dir = await mkdtemp(join(tmpdir(), "proof-reviewer-secvar-"));
    const defs = (ok: string) => ["structure Model where", "  n : Nat", "  ok : " + ok].join("\n");
    const main = ["import Defs", "variable (M : Model) (unusedVar : Other)", "theorem t1_thm : M.n = M.n := rfl"].join("\n");
    try {
      const one = await unfolded(dir, { "Defs.lean": defs("n = n") + "\ndef Other : Prop := True", "Main.lean": main }, "t1_thm", "Main.lean");
      expect(one.names).toEqual(["Model"]);
      expect((await unfolded(dir, {}, "t1_thm", "Main.lean", one.r)).prompts).toHaveLength(0);
      expect((await unfolded(dir, { "Defs.lean": defs("0 ≤ n") + "\ndef Other : Prop := True" }, "t1_thm", "Main.lean", one.r)).prompts).toHaveLength(1);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("the names scanned are the target's own: not a neighbour's, a trailing command's, or its proof's", async () => {
    const dir = await mkdtemp(join(tmpdir(), "proof-reviewer-own-"));
    const helpers = ["def helperA : Prop := True", "def helperB : Prop := True", "def helperC : Prop := True"];
    try {
      // a non-ASCII name, between a declaration and commands that are not declarations of the index
      const one = await unfolded(dir, { "T1.lean": [...helpers, "def neighbour : Prop := helperA", "def σAlg : Prop := helperB", "example : helperC := trivial", "instance : Inhabited helperA := ⟨trivial⟩"].join("\n") }, "σAlg", "T1.lean");
      expect(one.names).toEqual(["helperB"]);
      // a non-ASCII-named declaration after the target bounds it
      const two = await unfolded(dir, { "T1.lean": [...helpers, "def target : Prop := helperB", "def σNext : Prop := helperC"].join("\n") }, "target", "T1.lean");
      expect(two.names).toEqual(["helperB"]);
      // a theorem: its statement, not its proof
      const three = await unfolded(dir, { "T1.lean": [...helpers, "theorem t1_thm : helperB := by", "  have h : helperC := trivial", "  trivial"].join("\n") }, "t1_thm", "T1.lean");
      expect(three.names).toEqual(["helperB"]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("the page names the typed core for on-demand lookup only, names the tool budget and its logical stage, and the reply is schema-constrained", async () => {
    const one = await pass(driftGraph(), undefined);
    const [prompt] = one.prompts;
    expect(prompt.startsWith("=== F2.5 DELTA REVIEW ===\n")).toBe(true);
    expect(prompt).toContain(`${sharedCorePath} — open it WHEN NECESSARY`);
    expect(prompt).toContain("do not read the file whole");
    expect(prompt).toContain("Budget: at most 6 tool calls per target");
    expect(one.schema).toMatchObject({ type: "object", required: expect.arrayContaining(["statement_verdicts", "escalate"]) });
  });

  it("a reply that is not one schema-shaped JSON object still parses, and the fallback is logged", async () => {
    const warned: string[] = [];
    const warn = console.warn;
    console.warn = (...a: unknown[]) => { warned.push(a.map(String).join(" ")); };
    try {
      const g = driftGraph();
      const r = await runReviewer({
        ctx,
        deps: { runCodex: async () => ({ stdout: `Analysis: the set {x | P x} is fine.\n${JSON.stringify(drift)}\nDone.`, stderr: "" }) },
        graph: g, skeleton: graphDerivedSkeleton(g), dirty: ["t1"], hashes: { t1: "h1" }, mode: "delta",
        corePath: sharedCorePath, promptPath: sharedPromptPath, leanDir: sharedCoreRoot,
      });
      expect(r.blocking).toEqual(["T-1"]);
      expect(warned.some((w) => w.includes("heuristic parser"))).toBe(true);
    } finally {
      console.warn = warn;
    }
  });
});

describe("prompt composition — shared sections are rendered once per batch", () => {
  it("a definition two batched targets reference is unfolded once, each target naming it", async () => {
    const root = await mkdtemp(join(tmpdir(), "proof-reviewer-unfold-"));
    try {
      await writeFile(join(root, "core.json"), JSON.stringify(minimalCore()));
      await writeFile(join(root, "T1.lean"), [
        "def dShared : Prop := True",
        "def a2_assumption : Prop := dShared",
        "def a3_assumption : Prop := dShared ∧ True",
        "theorem t1_thm : True := by trivial",
      ].join("\n"));
      let g = createEmptyGraph("q");
      g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "rate", tex_anchor: "" });
      g = setLean(g, "t1", "t1_thm", "T1.lean");
      for (const id of ["a2", "a3"]) {
        g = addAssumption(g, { node: "t1", id, statement: `premise ${id}`, tier: 2, classification: "regularity-bookkeeping", anchor: "", provenance: "agent-introduced" });
        g = setLean(g, id, `${id}_assumption`, "T1.lean");
      }
      g = { ...g, nodes: g.nodes.map((n) => (n.id === "t1" ? { ...n, review: { status: "matched" as const, passed_hash: "h1" } } : n)) };
      const prompts: string[] = [];
      await runReviewer({
        ctx: { repoRoot: root, qid: "q" },
        deps: { runCodex: async ({ prompt }) => {
          prompts.push(prompt);
          return { stdout: JSON.stringify({ statement_verdicts: [], assumption_verdicts: [
            { obj_id: "A-2", verdict: "faithful-refinement", note: "" }, { obj_id: "A-3", verdict: "faithful-refinement", note: "" },
          ], substrate_gates: [], escalate: null }), stderr: "" };
        } },
        graph: g, skeleton: graphDerivedSkeleton(g), dirty: ["a2", "a3"], hashes: { t1: "h1", a2: "h2", a3: "h3" }, mode: "delta",
        corePath: join(root, "core.json"), promptPath: sharedPromptPath, leanDir: root,
      });
      const batch = prompts.find((p) => p.includes("### A-2 (") && p.includes("### A-3 ("))!;
      expect(batch).toBeDefined();
      expect(batch.match(/-- dShared \(def\) in T1\.lean/g)).toHaveLength(1);
      expect(batch.match(/Referenced definitions \(unfolded once under REFERENCED DEFINITIONS below[^\n]*: dShared/g)).toHaveLength(2);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });
});

describe("symbol clusters — an untagged symbol is graded once", () => {
  it("an empty cluster graded `untagged` is not re-dispatched while it stays empty", async () => {
    const root = await mkdtemp(join(tmpdir(), "proof-reviewer-untagged-"));
    try {
      await writeFile(join(root, "core.json"), JSON.stringify(minimalCore([{ name: "sigma", type: "scale", space: "[0,1]" }])));
      await writeFile(join(root, "T1.lean"), "theorem t1_thm : True := by trivial\n");
      let g = createEmptyGraph("q");
      g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "rate", tex_anchor: "" });
      g = setLean(g, "t1", "t1_thm", "T1.lean");
      g = { ...g, nodes: g.nodes.map((n) => (n.id === "t1" ? { ...n, review: { status: "matched" as const, passed_hash: "h1" } } : n)) };
      const pass = async (graph: typeof g) => {
        let calls = 0;
        const r = await runReviewer({
          ctx: { repoRoot: root, qid: "q" },
          deps: { runCodex: async () => { calls++; return { stdout: JSON.stringify({ statement_verdicts: [{ obj_id: "sym:sigma", verdict: "untagged", note: "no @realizes tag" }], assumption_verdicts: [], substrate_gates: [], escalate: null }), stderr: "" }; } },
          graph, skeleton: graphDerivedSkeleton(graph), dirty: [], hashes: { t1: "h1" }, mode: "delta",
          corePath: join(root, "core.json"), promptPath: sharedPromptPath, leanDir: root,
        });
        return { r, calls };
      };
      const one = await pass(g);
      expect(one.calls).toBe(1);
      expect(one.r.graph.symbolReview?.["sym:sigma"]?.verdict).toBe("untagged");
      const two = await pass(one.r.graph);
      expect(two.calls).toBe(0); // the persisted `untagged` is what the tag-reroute reads
      expect(two.r.graph.symbolReview?.["sym:sigma"]?.verdict).toBe("untagged");
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it("drops a stale untagged verdict after the symbol leaves the reviewed surface", async () => {
    const root = await mkdtemp(join(tmpdir(), "proof-reviewer-stale-symbol-"));
    try {
      await writeFile(join(root, "core.json"), JSON.stringify(minimalCore([
        { name: "s", type: "integer depth parameter", space: "$\\mathbb{N}$" },
      ])));
      await writeFile(join(root, "T1.lean"), "theorem t1_thm : True := by trivial\n");
      let g = createEmptyGraph("q");
      g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "rate", tex_anchor: "" });
      g = setLean(g, "t1", "t1_thm", "T1.lean");
      g = {
        ...g,
        nodes: g.nodes.map((n) => (n.id === "t1"
          ? { ...n, review: { status: "matched" as const, passed_hash: "h1" } }
          : n)),
        symbolReview: { "sym:s": { verdict: "untagged", hash: "stale" } },
      };
      let calls = 0;
      const r = await runReviewer({
        ctx: { repoRoot: root, qid: "q" },
        deps: { runCodex: async () => { calls++; return { stdout: "{}", stderr: "" }; } },
        graph: g, skeleton: graphDerivedSkeleton(g), dirty: [], hashes: { t1: "h1" }, mode: "delta",
        corePath: join(root, "core.json"), promptPath: sharedPromptPath, leanDir: root,
      });
      expect(calls).toBe(0);
      expect(r.graph.symbolReview?.["sym:s"]).toBeUndefined();
      // with no typed core there is no surface to compare: the verdicts stay
      const kept = await runReviewer({
        ctx: { repoRoot: root, qid: "q" },
        deps: { runCodex: async () => { calls++; return { stdout: "{}", stderr: "" }; } },
        graph: g, skeleton: graphDerivedSkeleton(g), dirty: [], hashes: { t1: "h1" }, mode: "delta",
        promptPath: sharedPromptPath, leanDir: root,
      });
      expect(calls).toBe(0);
      expect(kept.graph.symbolReview?.["sym:s"]).toEqual({ verdict: "untagged", hash: "stale" });
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });
});
