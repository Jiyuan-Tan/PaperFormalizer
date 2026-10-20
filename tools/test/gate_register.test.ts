import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises"; // writeFile used to seed husk shapes
import path from "node:path";
import os from "node:os";
import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { fileURLToPath } from "node:url";
import { beforeEach, describe, expect, it } from "vitest";
import { createInitialState, loadState, saveState } from "../src/state.js";
import { saveGraph, graphPath } from "../src/graph/store.js";
import { formalizationDir, planPath } from "../src/paths.js";
import type { FormalizationGraph, GraphNode } from "../src/graph/types.js";
import { TOOLKIT_JSON } from "./toolkit/helpers.js";
import { isGateDisclosure, withoutGateKeys } from "../src/formalization/gate_ops.js";

const exec = promisify(execFile);
const __TOOLS_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
// Always launched as `node <cli.mjs>`: a bare `.mjs` path is not executable on
// Windows, and the `node_modules/.bin/tsx` shim is a `.cmd` execFile cannot spawn.
const TSX_CLI = path.resolve(__TOOLS_ROOT, "node_modules", "tsx", "dist", "cli.mjs");
const GATE = path.resolve(__TOOLS_ROOT, "bin", "gate.ts");

const QID = "stat_demo";
const CONSUMER = "oeq:feasible-upper";
const GATE_ID = "bochner_integrability_gate";
/** The real shape of the defect: a substrate-gate disclosed in prose, with no node behind it. */
const PROSE_LABEL = "crossfit reductions: 4× Integrable sSup gates";

let repoRoot: string;

const node = (id: string, kind: GraphNode["kind"]): GraphNode => ({
  id,
  kind,
  provenance: "from-note",
  nl: { statement: `${id} statement`, tex_anchor: id, frozen: false },
  lean: { decl_name: `Ns.${id.replace(/[:-]/g, "_")}`, file: "F.lean" },
  review: { status: "matched", passed_hash: "h0" },
  proof: { state: "complete", sorry_count: 0 },
});

function gate(args: string[]): Promise<{ stdout: string; stderr: string }> {
  // The toolkit is found by walking up from the cwd to `theoremchecker.json`.
  const env = { ...process.env };
  delete env.THEOREMCHECKER_TOOLKIT;
  return exec(process.execPath, [TSX_CLI, GATE, QID, ...args], { cwd: repoRoot, env });
}

async function seedLeanDecl(
  kind: "def" | "lemma" | "theorem",
  name: string,
  rel = "Helper.lean",
  body = "by trivial",
) {
  const st = await loadState(repoRoot, QID);
  const leanDir = path.join(repoRoot, ...st.lean_subdir.split("/"));
  await mkdir(path.dirname(path.join(leanDir, rel)), { recursive: true });
  await writeFile(
    path.join(leanDir, rel),
    `namespace Ns\n-- @node: ${GATE_ID}\n${kind} ${name} : True := ${body}\nend Ns\n`,
  );
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "gate-reg-"));
  await writeFile(path.join(repoRoot, "theoremchecker.json"), JSON.stringify(TOOLKIT_JSON));

  const st = createInitialState(QID);
  st.added_assumptions = [
    { label: PROSE_LABEL, statement: "Bochner integrability of the sSup integrands", classification: "substrate-gate" },
  ];
  await saveState(repoRoot, QID, st);

  const graph: FormalizationGraph = { qid: QID, nodes: [node(CONSUMER, "theorem")], edges: [] };
  const fdir = formalizationDir(repoRoot, QID);
  await mkdir(fdir, { recursive: true });
  await saveGraph(graphPath(fdir), graph);

  const ppath = planPath(repoRoot, QID);
  await mkdir(path.dirname(ppath), { recursive: true });
  await writeFile(ppath, JSON.stringify({ nodes: { [CONSUMER]: { lean_kind: "theorem", hyps: [] } } }, null, 2));
});

describe("gate.ts registration of a prose-only substrate-gate", () => {
  // Before minting existed, `gate.ts` exited 1 on a node absent from the graph — so a debt
  // disclosed only in `state.added_assumptions` (what `--audit` calls "prose-only and
  // unenforceable") could never be registered. The only escape from the defect was blocked.
  it("MINTS the missing gate node, threads consumers, and registers it", async () => {
    const { stdout } = await gate([
      GATE_ID, "--consumers", CONSUMER, "--statement", "hBochner: integrability of the offset sSup",
      "--lean-name", "hBochner", "--supersedes", PROSE_LABEL,
    ]);
    expect(stdout).toMatch(/minted/i);

    const g = JSON.parse(await readFile(graphPath(formalizationDir(repoRoot, QID)), "utf8"));
    const gn = g.nodes.find((n: GraphNode) => n.id === GATE_ID);
    expect(gn.kind).toBe("gate");
    expect(gn.gate.gate_class).toBe("gated");
    expect(g.edges).toContainEqual({ kind: "proof-uses", from: CONSUMER, to: GATE_ID, source: "declared" });

    const plan = JSON.parse(await readFile(planPath(repoRoot, QID), "utf8"));
    expect(plan.nodes[GATE_ID]).toMatchObject({ gate: true, gate_class: "gated", lean_name: "hBochner" });
    expect(plan.nodes[CONSUMER].hyps).toContain(GATE_ID);

    // Registering makes the consumer's statement CONDITIONAL → it must be re-reviewed.
    expect(g.nodes.find((n: GraphNode) => n.id === CONSUMER).review.status).toBe("unreviewed");
  });

  it("REFUSES to mint without --statement, and says how to supply it", async () => {
    await expect(gate([GATE_ID, "--consumers", CONSUMER])).rejects.toMatchObject({ code: 1 });
    await expect(gate([GATE_ID, "--consumers", CONSUMER])).rejects.toThrow(/--statement/);
  });

  // REGRESSION (seen in a live exp_bipartite discharge): a plan gate node carrying ONLY gate keys
  // (registered by the pipeline scaffolder, not gate.ts's fuller mint) was left as `{}` by
  // `withoutGateKeys` on --ungate — no lean_kind/lean_name/disposition, so it trips the F2 post-sync
  // plan_gate schema on every later run. A node that is nothing but a gate must be DELETED.
  it("DELETES a gate-only plan node on --ungate (no {} husk)", async () => {
    // Seed the husk-producing shape directly: a plan node with only gate keys + a graph gate node.
    const gp = graphPath(formalizationDir(repoRoot, QID));
    const g = JSON.parse(await readFile(gp, "utf8"));
    g.nodes.push({ ...node(GATE_ID, "gate"), gate: { gate_class: "gated" }, provenance: "agent-introduced" });
    g.edges.push({ kind: "proof-uses", from: CONSUMER, to: GATE_ID, source: "declared" });
    await writeFile(gp, JSON.stringify(g));
    const pp = planPath(repoRoot, QID);
    const plan0 = JSON.parse(await readFile(pp, "utf8"));
    plan0.nodes[GATE_ID] = { gate: true, gate_class: "gated" }; // only gate keys
    plan0.nodes[CONSUMER].hyps = [GATE_ID];
    await writeFile(pp, JSON.stringify(plan0));

    await gate([GATE_ID, "--ungate"]);

    const plan = JSON.parse(await readFile(pp, "utf8"));
    expect(GATE_ID in plan.nodes).toBe(false); // deleted, not {}
    expect(plan.nodes[CONSUMER].hyps).not.toContain(GATE_ID); // consumer survives, un-threaded
  });

  // REGRESSION (exp_saturation_exacthit_deficiency_design): after a minted local
  // substrate gate was proved, discharge deleted both its transient plan entry AND
  // its completed graph node. The Lean @node tag survived, so F2's P7 exact-helper
  // exemption had no pre-F2 graph witness and rejected the next scaffold. A proved
  // local helper is no longer a gate-only placeholder: remove it from the core-only
  // plan, but preserve its completed graph identity and proof-use edge.
  it("PRESERVES a proved minted helper in the graph while deleting its plan gate", async () => {
    await gate([
      GATE_ID, "--consumers", CONSUMER, "--statement", "finite categorical histogram law",
      "--lean-name", "iid_finiteCategorical_counts_multinomial",
    ]);

    const gp = graphPath(formalizationDir(repoRoot, QID));
    const graph0 = JSON.parse(await readFile(gp, "utf8"));
    const helper = graph0.nodes.find((n: GraphNode) => n.id === GATE_ID);
    helper.lean = { decl_name: "Ns.iid_finiteCategorical_counts_multinomial", file: "Helpers/FiniteCategoricalCounts.lean" };
    helper.proof = { state: "complete", sorry_count: 0 };
    await writeFile(gp, JSON.stringify(graph0));
    await seedLeanDecl("lemma", "iid_finiteCategorical_counts_multinomial", "Helpers/FiniteCategoricalCounts.lean");

    await gate([
      GATE_ID, "--discharge", "--lean-kind", "lemma",
      "--lean-name", "iid_finiteCategorical_counts_multinomial",
    ]);

    const plan = JSON.parse(await readFile(planPath(repoRoot, QID), "utf8"));
    expect(GATE_ID in plan.nodes).toBe(false);
    expect(plan.nodes[CONSUMER].hyps).not.toContain(GATE_ID);

    const graph = JSON.parse(await readFile(gp, "utf8"));
    expect(graph.nodes.find((n: GraphNode) => n.id === GATE_ID)).toMatchObject({
      kind: "lemma",
      provenance: "agent-introduced",
      lean: { decl_name: "Ns.iid_finiteCategorical_counts_multinomial", file: "Helpers/FiniteCategoricalCounts.lean" },
      proof: { state: "complete", sorry_count: 0 },
    });
    expect(graph.edges).toContainEqual({ kind: "proof-uses", from: CONSUMER, to: GATE_ID, source: "declared" });
  });

  it("refuses to preserve a drifted completed helper before mutation", async () => {
    await gate([GATE_ID, "--consumers", CONSUMER, "--statement", "s", "--lean-name", "provedHelper"]);
    const gp = graphPath(formalizationDir(repoRoot, QID));
    const pp = planPath(repoRoot, QID);
    const graph0 = JSON.parse(await readFile(gp, "utf8"));
    const helper = graph0.nodes.find((n: GraphNode) => n.id === GATE_ID);
    helper.lean = { decl_name: "Ns.provedHelper", file: "Helper.lean" };
    helper.proof = { state: "complete", sorry_count: 0 };
    helper.review = { status: "drift", passed_hash: null };
    await writeFile(gp, JSON.stringify(graph0));
    await seedLeanDecl("lemma", "provedHelper");
    const before = await Promise.all([readFile(gp, "utf8"), readFile(pp, "utf8")]);

    await expect(gate([GATE_ID, "--discharge", "--lean-kind", "lemma"])).rejects.toThrow(/review status is drift/);
    const after = await Promise.all([readFile(gp, "utf8"), readFile(pp, "utf8")]);
    expect(after).toEqual(before);
  });

  it.each([
    ["admit", "by admit"],
    ["sorryAx", "by exact sorryAx True true"],
  ])("refuses to discharge a tagged lemma containing %s", async (_token, body) => {
    await gate([GATE_ID, "--consumers", CONSUMER, "--statement", "s", "--lean-name", "badHelper"]);
    const gp = graphPath(formalizationDir(repoRoot, QID));
    const graph0 = JSON.parse(await readFile(gp, "utf8"));
    const helper = graph0.nodes.find((n: GraphNode) => n.id === GATE_ID);
    helper.lean = { decl_name: "Ns.badHelper", file: "Helper.lean" };
    helper.proof = { state: "complete", sorry_count: 0 };
    await writeFile(gp, JSON.stringify(graph0));
    await seedLeanDecl("lemma", "badHelper", "Helper.lean", body);

    await expect(gate([GATE_ID, "--discharge", "--lean-name", "badHelper"])).rejects.toThrow(/sorry-free/);
    const graph = JSON.parse(await readFile(gp, "utf8"));
    expect(graph.nodes.find((n: GraphNode) => n.id === GATE_ID).kind).toBe("gate");
  });

  it("restores a discharged cited theorem-family node with its plan kind", async () => {
    const gp = graphPath(formalizationDir(repoRoot, QID));
    const g = JSON.parse(await readFile(gp, "utf8"));
    g.nodes.push({ ...node(GATE_ID, "gate"), gate: { gate_class: "cited" } });
    await writeFile(gp, JSON.stringify(g));
    const pp = planPath(repoRoot, QID);
    const plan0 = JSON.parse(await readFile(pp, "utf8"));
    plan0.nodes[GATE_ID] = {
      lean_kind: "assumption",
      lean_name: "provedCitation",
      disposition: "define-local",
      defer_tier: true,
      gate: true,
      gate_class: "cited",
      source: "cite:source",
    };
    await writeFile(pp, JSON.stringify(plan0));

    await gate([GATE_ID, "--ungate", "--lean-kind", "theorem", "--lean-name", "provedCitation"]);

    const graph = JSON.parse(await readFile(gp, "utf8"));
    expect(graph.nodes.find((n: GraphNode) => n.id === GATE_ID).kind).toBe("theorem");
    const plan = JSON.parse(await readFile(pp, "utf8"));
    expect(plan.nodes[GATE_ID]).toMatchObject({
      citation_discharged: true,
      lean_kind: "theorem",
      defer_tier: false,
    });
  });
});

describe("gate_ops", () => {
  it("withoutGateKeys DELETES gate + gate_class (never leaves gate_class: null, which trips the plan schema)", () => {
    const out = withoutGateKeys({ lean_name: "X", gate: true, gate_class: "gated", disposition: "define-local" }) as Record<string, unknown>;
    expect("gate_class" in out).toBe(false);
    expect(out).toEqual({ lean_name: "X", disposition: "define-local" });
  });

  it("isGateDisclosure matches one gate's node-id and Lean-name labels, not a gate sharing the anchor prefix", () => {
    const ids = ["input:hetero-clt-denominator-tightness", "HeteroDenominatorTightnessInput"];
    expect(isGateDisclosure({ label: `thm:hetero-clt:${ids[0]}` }, ids)).toBe(true);
    expect(isGateDisclosure({ label: `thm:hetero-clt:${ids[1]}` }, ids)).toBe(true);
    expect(isGateDisclosure({ label: "thm:hetero-clt:HeteroLinScoreCLTInput" }, ids)).toBe(false);
  });
});
