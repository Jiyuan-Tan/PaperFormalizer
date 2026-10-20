import { describe, it, expect, afterAll } from "vitest";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge, setProof } from "../../src/graph/mutate.js";
import { nodeIdToObjId } from "../../src/graph/from_note.js";
import { runFiller } from "../../src/formalization/proof_filler.js";
import { WORKER_BUILD_INACTIVITY_MS } from "../../src/framework/agent_dispatch.js";
import type { CodexRunInput } from "../../src/shared/codex.js";

// The filler dispatches a WRITE-CAPABLE agent, so it must never run on a degraded prompt: the
// base prompt carries the no-axiom / disclosure / frozen-statement contract. Point every test at
// the real prompt file rather than letting a missing one silently become "".
const realPromptPath = join(process.cwd(), "src/formalization/prompts/F4/proof_filler.txt");

function fixture() {
  let g = createEmptyGraph("q");
  g = addNode(g, { id: "setup", kind: "setup", provenance: "from-note", nl_statement: "PO env", tex_anchor: "" });
  g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "the rate holds", tex_anchor: "L1" });
  g = { ...g, nodes: g.nodes.map((n) => (n.id === "t1" ? { ...n, lean: { decl_name: "t1_thm", file: "T1.lean" } } : n)) };
  g = setProof(g, "t1", "sorry", 1);
  g = addEdge(g, { kind: "setup-of", from: "setup", to: "t1", source: "declared" });
  return g;
}

function fixtureWithObjAlias() {
  let g = createEmptyGraph("q");
  g = addNode(g, { id: "setup", kind: "setup", provenance: "from-note", nl_statement: "PO env", tex_anchor: "" });
  g = addNode(g, { id: "thm:main", kind: "theorem", provenance: "from-note", nl_statement: "the rate holds", tex_anchor: "L1" });
  g = { ...g, nodes: g.nodes.map((n) => (n.id === "thm:main" ? { ...n, obj_id: "T-1", lean: { decl_name: "t1_thm", file: "T1.lean" } } : n)) };
  g = setProof(g, "thm:main", "sorry", 1);
  g = addEdge(g, { kind: "setup-of", from: "setup", to: "thm:main", source: "declared" });
  return g;
}

const codexStub = (out: object) => ({
  runCodex: async () => ({ stdout: JSON.stringify(out), stderr: "" }),
});

// A real writable dir: the filler now dispatches through the framework boundary
// (dispatchAgent), which appends a dispatch/dispatch-complete pair to
// <repoRoot>/.../pipeline.jsonl before/after each call — an unwritable fake root
// like "/repo" trips EACCES on that mkdir.
const fillerRepoRoot = mkdtempSync(join(tmpdir(), "proof-filler-ctx-"));
afterAll(() => rmSync(fillerRepoRoot, { recursive: true, force: true }));
const ctx = { repoRoot: fillerRepoRoot, qid: "q" };

describe("runFiller", () => {
  it("its worker waits an hour of silence before it is killed: the shell builds the paper's modules", async () => {
    const calls: CodexRunInput[] = [];
    const reply = { added_assumptions: [], escalate: null, summary: "s" };
    await runFiller({
      ctx,
      promptPath: realPromptPath,
      leanDir: "/repo/lean",
      graph: fixture(),
      deps: { runCodex: async (input: CodexRunInput) => (calls.push(input), { stdout: JSON.stringify(reply), stderr: "" }) },
    });
    expect(calls).toHaveLength(1);
    expect(calls[0]!.inactivityTimeoutMs).toBe(WORKER_BUILD_INACTIVITY_MS);
    expect(WORKER_BUILD_INACTIVITY_MS).toBeGreaterThanOrEqual(60 * 60 * 1000);
  });

  it("records an added assumption as a node + proof-uses edge and flips the parent unreviewed", async () => {
    const r = await runFiller({
      ctx,
      promptPath: realPromptPath,
      leanDir: "/repo/lean",
      graph: fixture(),
      deps: codexStub({
        added_assumptions: [
          { id: "a9", statement: "the outcome is bounded", classification: "regularity-bookkeeping", attached_to: "t1" },
        ],
        escalate: null,
        summary: "added boundedness; closed 1 sorry",
      }),
    });
    const id = "ass:filler:2:t1:2:a9";
    const a9 = r.graph.nodes.find((n) => n.id === id)!;
    expect(a9.kind).toBe("assumption");
    expect(a9.provenance).toBe("agent-introduced");
    expect(r.graph.edges).toContainEqual({ kind: "proof-uses", from: "t1", to: id, source: "declared" });
    expect(r.graph.nodes.find((n) => n.id === "t1")!.review.status).toBe("unreviewed");
    expect(r.escalate).toBeNull();
  });

  it("a premise the reviewer classed otherwise, listed again by the filler, is the node on file: no second node, the reviewer's class kept", async () => {
    const { withReviewedAssumptionClasses } = await import("../../src/formalization/proof_reviewer.js");
    const reply = { added_assumptions: [{ id: "a9", statement: "the outcome is bounded", classification: "regularity-bookkeeping", attached_to: "t1" }], escalate: null, summary: "s" };
    const id = "ass:filler:2:t1:2:a9";
    const first = await runFiller({ ctx, promptPath: realPromptPath, leanDir: "/repo/lean", graph: fixture(), deps: codexStub(reply) });
    const reviewed = withReviewedAssumptionClasses(first.graph, new Map([[id, "substrate-gate" as const]]));
    const again = await runFiller({ ctx, promptPath: realPromptPath, leanDir: "/repo/lean", graph: reviewed, deps: codexStub(reply) });
    const premises = again.graph.nodes.filter((n) => n.kind === "assumption" && n.nl.statement === "the outcome is bounded");
    expect(premises.map((n) => [n.id, n.assumption?.classification])).toEqual([[id, "substrate-gate"]]);
    // … while another statement under the same id is still another premise
    const other = await runFiller({ ctx, promptPath: realPromptPath, leanDir: "/repo/lean", graph: reviewed, deps: codexStub({ ...reply, added_assumptions: [{ ...reply.added_assumptions[0]!, statement: "the outcome has four moments" }] }) });
    expect(other.graph.nodes.some((n) => n.id === `${id}:1`)).toBe(true);
  });

  const withFrozenA1 = (g: ReturnType<typeof fixtureWithObjAlias>) => {
    g = addNode(g, { id: "ass:frozen", kind: "assumption", provenance: "from-note", nl_statement: "the frozen assumption", tex_anchor: "A-1" });
    return { ...g, nodes: g.nodes.map((n) => n.id === "ass:frozen" ? { ...n, obj_id: "A-1" } : n) };
  };
  const generated = "ass:filler:8:thm:main:2:a1";
  it.each([
    ["its legacy reviewer alias is already owned", (g: ReturnType<typeof fixtureWithObjAlias>) => withFrozenA1(g), generated],
    ["its exact id is owned by a different premise", (g: ReturnType<typeof fixtureWithObjAlias>) =>
      addNode(g, { id: "a1", kind: "assumption", provenance: "agent-introduced", nl_statement: "a different premise", tex_anchor: "" }), generated],
    ["the generated namespace id is also taken", (g: ReturnType<typeof fixtureWithObjAlias>) =>
      withFrozenA1(addNode(g, { id: generated, kind: "assumption", provenance: "agent-introduced", nl_statement: "occupied generated id", tex_anchor: "" })), `${generated}:1`],
  ] as const)("mints a filler assumption under a fresh id when %s (never reuses another owner)", async (_label, prepare, expectedId) => {
    const graph = prepare(fixtureWithObjAlias());
    const r = await runFiller({
      ctx, promptPath: realPromptPath, leanDir: "/repo/lean", graph,
      deps: codexStub({
        added_assumptions: [
          { id: "a1", statement: "the new premise", classification: "regularity-bookkeeping", attached_to: "T-1" },
        ],
        escalate: null, summary: "added premise",
      }),
    });
    expect(r.graph.nodes.find((n) => n.id === expectedId)?.nl.statement).toBe("the new premise");
    expect(r.graph.edges).toContainEqual({ kind: "proof-uses", from: "thm:main", to: expectedId, source: "declared" });
    // every pre-existing owner keeps its own statement, and "A-1" still has one owner at most
    for (const n of graph.nodes) expect(r.graph.nodes.find((m) => m.id === n.id)?.nl.statement).toBe(n.nl.statement);
    expect(r.graph.nodes.filter((n) => [n.id, n.obj_id, nodeIdToObjId(n.id)].includes("A-1")).length).toBeLessThanOrEqual(1);
    expect(nodeIdToObjId(expectedId)).toBe(expectedId);
  });

  // A degraded base prompt strips the no-axiom / disclosure / frozen-statement contract while
  // leaving the agent's write access intact, so the filler must refuse to dispatch at all.
  it.each([
    ["missing", async () => join(tmpdir(), "causalsmith-no-such-proof-filler-prompt.txt"), /proof-filler prompt missing/],
    ["blank", async () => {
      const blank = join(await mkdtemp(join(tmpdir(), "filler-blank-prompt-")), "proof_filler.txt");
      await writeFile(blank, "   \n\n");
      return blank;
    }, /proof-filler prompt is empty/],
  ] as const)("refuses to dispatch when the base prompt is %s", async (_label, promptFile, err) => {
    const promptPath = await promptFile();
    let dispatched = false;
    try {
      await expect(
        runFiller({
          ctx,
          promptPath,
          leanDir: "/repo/lean",
          graph: fixture(),
          deps: { runCodex: async () => { dispatched = true; return { stdout: "{}", stderr: "" }; } },
        }),
      ).rejects.toThrow(err);
      expect(dispatched).toBe(false);
    } finally {
      if (promptPath.includes("filler-blank-prompt-")) await rm(join(promptPath, ".."), { recursive: true, force: true });
    }
  });

  // The loop has no stage-level catch, so a throw here would abort the whole run on one flaky
  // model reply. Mirror the reviewer's parse boundary: escalate `unparsable-output` instead.
  it("escalates (not throws) when the filler output has no parseable JSON", async () => {
    const r = await runFiller({
      ctx,
      promptPath: realPromptPath,
      leanDir: "/repo/lean",
      graph: fixture(),
      deps: { runCodex: async () => ({ stdout: "I could not finish; no JSON here.", stderr: "" }) },
    });
    expect(r.escalate?.kind).toBe("unparsable-output");
    expect(r.graph).toEqual(fixture());
  });

  // An assumption attached to an unknown parent cannot land on the graph; it must be dropped
  // LOUDLY (the Lean already carries the hypothesis — a silent drop loses the disclosure).
  it("warns when an added assumption's parent cannot be resolved, and does not mint the node", async () => {
    const warns: string[] = [];
    const orig = console.warn;
    console.warn = (...a: unknown[]) => { warns.push(a.map(String).join(" ")); };
    try {
      const r = await runFiller({
        ctx,
        promptPath: realPromptPath,
        leanDir: "/repo/lean",
        graph: fixture(),
        deps: codexStub({
          added_assumptions: [
            { id: "a11", statement: "smuggled", classification: "substrate-gate", attached_to: "no-such-node" },
          ],
          escalate: null,
          summary: "attached to ghost",
        }),
      });
      expect(r.graph.nodes.some((n) => n.id === "a11")).toBe(false);
      expect(r.escalate).toBeNull();
      expect(warns.some((w) => w.includes("a11") && w.includes("no-such-node"))).toBe(true);
    } finally {
      console.warn = orig;
    }
  });

  it("surfaces an escalation", async () => {
    const r = await runFiller({
      ctx,
      promptPath: realPromptPath,
      leanDir: "/repo/lean",
      graph: fixture(),
      deps: codexStub({ added_assumptions: [], escalate: { kind: "needs-substrate", reason: "needs a concentration bound", node: "t1" }, summary: "stuck" }),
    });
    expect(r.escalate).toEqual({ kind: "needs-substrate", reason: "needs a concentration bound", node: "t1" });
  });
});

describe("filler context — the page carries this round's work, not every open node in full", () => {
  it("focuses leaf-first on a few open nodes with their statement and proof roadmap; the rest are one line; the environment is one line each", async () => {
    const { renderFillerContext } = await import("../../src/formalization/proof_filler.js");
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "setup", kind: "setup", provenance: "from-note", nl_statement: "The sampling world. ".repeat(60), tex_anchor: "" });
    for (const id of ["l1", "l2", "l3", "l4"]) {
      g = addNode(g, { id, kind: "lemma", provenance: "from-note", nl_statement: `statement of ${id}`, tex_anchor: "" });
      g = setProof(g, id, "sorry", 1);
    }
    g = addEdge(g, { kind: "proof-uses", from: "l2", to: "l1", source: "declared" });
    g = addEdge(g, { kind: "proof-uses", from: "l3", to: "l2", source: "declared" });
    g = addEdge(g, { kind: "proof-uses", from: "l4", to: "l3", source: "declared" });
    const page = renderFillerContext(g, [], new Map([["l1", "ROADMAP_L1"], ["l4", "ROADMAP_L4"]]));
    const [focus, rest] = page.split("OTHER OPEN WORK");
    expect(focus).toContain("- l1 (lemma, (unlinked), sorry) [FROZEN STATEMENT — do not weaken]: statement of l1");
    expect(focus).toContain("PROOF ROADMAP (proof_tex): ROADMAP_L1");
    expect(focus).toContain("statement of l2");
    expect(focus).toContain("statement of l3");
    expect(focus).not.toContain("statement of l4");
    expect(rest).toContain("- l4 (lemma, (unlinked), sorry)");
    expect(rest).not.toContain("ROADMAP_L4");
    const env = page.split("\n").find((l) => l.startsWith("- setup:"))!;
    expect(env.length).toBeLessThan(300);
    expect(env.endsWith("…")).toBe(true);
  });

  it("the prompt names its logical stage, embeds the focus node's roadmap from the core instead of pointing at it, and the reply is schema-constrained", async () => {
    const corePath = join(fillerRepoRoot, "core.json");
    await writeFile(corePath, JSON.stringify({
      qid: "q", symbols: [], assumptions: [], definitions: [], target_estimand: "rate", bibliography: [],
      statements: [{ id: "thm:main", kind: "theorem", statement: "the rate holds", depends_on: [], status: "to-prove", proof_tex: "ROADMAP_T1" }],
    }));
    let prompt = "";
    let schema: unknown;
    await runFiller({
      ctx, promptPath: realPromptPath, leanDir: "/repo/lean", graph: fixtureWithObjAlias(), corePath,
      deps: { runCodex: async (o) => { prompt = o.prompt; schema = o.outputSchema; return { stdout: JSON.stringify({ added_assumptions: [], escalate: null, summary: "" }), stderr: "" }; } },
    });
    expect(prompt.startsWith("=== F3 PROOF FILL ===\n")).toBe(true);
    expect(prompt).toContain("PROOF ROADMAP (proof_tex): ROADMAP_T1");
    expect(prompt).not.toContain(corePath);
    expect(prompt).toContain("do not read the typed core");
    expect(schema).toMatchObject({ type: "object", required: ["added_assumptions", "escalate", "summary"] });
  });
});
