import { fileURLToPath } from "node:url";
/**
 * V1.5 stage tests. No network: `runCodex` is a fake returning canned JSON, so every
 * case exercises the stage's own logic — the contract checks, the COMPUTED verdict, the
 * bookkeeping application, and what each verdict persists.
 */
import type { OwnerExplanation } from "../../src/verify/owner_text.js";
import { MAX_PATCH_ROUNDS_PER_LEVEL, MIN_PATCH_BACKSTOP, MAX_REVISE_ROUNDS_PER_NODE } from "../../src/verify/types.js";
import { existsSync, readFileSync } from "node:fs";
import { mkdir, mkdtemp, readdir, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { parseTypedCore } from "../../src/core/core_io.js";
import { runStructuralGate } from "../../src/core/gate.js";
import type { Core } from "../../src/core/schema.js";
import type { runCodex, CodexRunInput } from "../../src/shared/codex.js";
import { createVerifyInitialState, loadState } from "../../src/state.js";
import { SYMBOL_REPLY } from "../../src/verify/referee_shard_prompts.js";
import type { StateJson } from "../../src/types.js";
import { sha256File } from "../../src/verify/core_hash.js";
import { acceptCapLosses, acceptV1_5AtCap, runStageV1_5, spentCapLine } from "../../src/verify/stage_v1_5.js";
import { GLOBAL_REPLY, SHARD_REPLY } from "../../src/verify/referee_shards.js";
import { BASIS_SCHEME } from "../../src/verify/core_graph.js";
import { MAX_REFINEMENT_ROUNDS, VERIFY_FILES, type V15Review, type VerifyStageArgs, type VerifyStageResult } from "../../src/verify/types.js";
import { withOwnerExplanations } from "./owner_explained.js";
import { symbolReply } from "./symbol_fake.js";

const QID = "toy_paper";
const FLAT_FIXTURE = path.join(
  path.dirname(fileURLToPath(import.meta.url)),
  "fixtures",
  "v1_5",
  "flat.tex",
);

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const dir of tmpDirs.splice(0)) await rm(dir, { recursive: true, force: true });
});

/** A small but REAL core: three statements (one a `cited` leaf), two assumptions, one
 * definition, every id resolvable. Built here rather than read from disk so the gate
 * assertion below is a live check on the fixture. */
function fixtureCore(): Core {
  return {
    qid: QID,
    symbols: [
      { name: "Y", type: "random variable", role: "outcome" },
      { name: "D", type: "random variable", role: "treatment" },
      { name: "X", type: "random vector", role: "covariates" },
      { name: "e", type: "function", sig: "\\(e : \\mathcal{X} \\to [0,1]\\)" },
      { name: "\\tau", type: "real" },
    ],
    assumptions: [
      {
        id: "ass:unconfoundedness",
        kind: "causal-structural",
        condition: "\\(Y(d) \\perp D \\mid X\\) for \\(d \\in \\{0,1\\}\\)",
        novel: { flag: true, justification: "Assumption 1 of the paper" },
        used_by: ["thm:ate-identification"],
        tex_locator: { file: "main.tex", from: 11, to: 13, env: "assumption", label: "ass:unconf" },
      },
      {
        id: "ass:overlap",
        kind: "support",
        condition: "\\(0 < e(X) < 1\\) almost surely",
        novel: { flag: true, justification: "Assumption 2 of the paper" },
        used_by: ["lem:ipw-identity", "thm:ate-identification"],
        tex_locator: { file: "main.tex", from: 15, to: 17, env: "assumption", label: "ass:overlap" },
      },
    ],
    definitions: [
      {
        id: "def:propensity",
        name: "propensity score",
        construction: "\\(e(x) = \\Pr(D = 1 \\mid X = x)\\)",
        tex_locator: { file: "main.tex", from: 8, to: 9, env: "definition", label: null },
      },
    ],
    statements: [
      {
        id: "lem:ipw-identity",
        kind: "lemma",
        statement: "\\(E[DY/e(X)] = E[Y(1)]\\)",
        depends_on: ["ass:overlap", "def:propensity"],
        proof_tex: "Condition on \\(X\\) and apply the tower property.",
        status: "to-prove",
        tex_locator: { file: "main.tex", from: 19, to: 21, env: "lem", label: "lem:ipw" },
      },
      {
        id: "thm:ate-identification",
        kind: "theorem",
        statement: "\\(\\tau = E[DY/e(X) - (1-D)Y/(1-e(X))]\\)",
        depends_on: [
          "ass:unconfoundedness",
          "ass:overlap",
          "def:propensity",
          "lem:ipw-identity",
        ],
        proof_tex: "Apply the IPW identity to each arm and subtract.",
        status: "to-prove",
        tex_locator: { file: "main.tex", from: 26, to: 28, env: "thm", label: "thm:ate" },
      },
      {
        id: "lem:delta-method",
        kind: "lemma",
        statement:
          "If \\(\\sqrt{n}(T_n - \\theta) \\rightsquigarrow T\\) and \\(\\phi\\) is differentiable at \\(\\theta\\), then \\(\\sqrt{n}(\\phi(T_n) - \\phi(\\theta)) \\rightsquigarrow \\phi'_\\theta(T)\\)",
        depends_on: [],
        status: "cited",
        source: {
          cite: "vandervaart1998",
          locator: "Theorem 3.1",
          verbatim_statement: "Delta method, as quoted by the paper.",
        },
        tex_locator: { file: "main.tex", from: 33, to: 35, env: "lem", label: "lem:delta" },
      },
    ],
    target_estimand: "\\(\\tau = E[Y(1) - Y(0)]\\)",
    bibliography: [{ key: "vandervaart1998", citation: "van der Vaart (1998). Asymptotic Statistics." }],
  };
}

function verdictNode(
  id: string,
  over: Partial<V15Review["nodes"][number]> = {},
): V15Review["nodes"][number] {
  return {
    id,
    faithfulness: "ok",
    ambiguity: "ok",
    correctness: "ok",
    detail: "reproduced",
    witness: null,
    bookkeeping_assumption: null,
    reading: null,
    ...over,
  };
}

/** Every addressable id of `fixtureCore()`. The referee must grade ALL of them (coverage is a
 * contract check), so tests build their reviews from this list and override the nodes they
 * are about. */
const CORE_IDS = [
  "ass:unconfoundedness",
  "ass:overlap",
  "def:propensity",
  "lem:ipw-identity",
  "thm:ate-identification",
  "lem:delta-method",
] as const;

function fullNodes(
  overrides: Partial<Record<(typeof CORE_IDS)[number], Partial<V15Review["nodes"][number]>>> = {},
): V15Review["nodes"] {
  return CORE_IDS.map((id) => verdictNode(id, overrides[id] ?? {}));
}

/** The ids a shard call grades (its NODES TO GRADE section). */
function shardIds(prompt: string): string[] {
  return (prompt.match(/=== NODES TO GRADE[^\n]*===\n\n(?:[^\n-][^\n]*\n\n)?((?:- .*\n?)+)/)?.[1] ?? "").split("\n").filter(Boolean).map((l) => l.slice(2));
}

/** The node-shard calls / the global-pass calls among `calls`. */
const shardCalls = (calls: CodexRunInput[]): CodexRunInput[] => calls.filter((c) => c.outputSchema === SHARD_REPLY);
const globalCalls = (calls: CodexRunInput[]): CodexRunInput[] => calls.filter((c) => c.outputSchema === GLOBAL_REPLY);
/** The retries among `calls` (a call re-asked after a contract violation). */
const retriesOf = (calls: CodexRunInput[]): CodexRunInput[] => calls.filter((c) => c.prompt.includes("=== CONTRACT VIOLATIONS IN YOUR PREVIOUS REPLY ==="));

/**
 * The sharded referee answered from whole canned reviews (`{verdict, summary, nodes, patch_review,
 * rejection_verdicts}`), one per round of grading: a shard call takes its nodes' grades from reply k,
 * k one past the most any of its nodes was graded (a shard's retry reads the next reply; a grade of an
 * id outside the core — `corePath` as it stands — goes to every shard); the global call takes the reply
 * the last shard read (a retry the next). A call past the canned replies throws, so a stage that retries
 * when it should not fails loudly. `calls`: every referee call (symbol calls answered apart).
 */
function fakeCodex(replies: unknown[], calls: CodexRunInput[], corePath?: string): typeof runCodex {
  const graded = new Map<string, number>();
  let lastK = 0;
  let globals = 0;
  const known = (): Set<string> => {
    if (!corePath || !existsSync(corePath)) return new Set(CORE_IDS);
    const c = JSON.parse(readFileSync(corePath, "utf8")) as Core;
    return new Set([...c.statements, ...c.assumptions, ...c.definitions].map((n) => n.id));
  };
  return (async (input: CodexRunInput) => {
    const sym = symbolReply(input);
    if (sym !== null) return { stdout: sym, stderr: "" };
    calls.push(input);
    if (input.outputSchema === SHARD_REPLY) {
      const ids = shardIds(input.prompt);
      const k = 1 + Math.max(0, ...ids.map((id) => graded.get(id) ?? 0));
      for (const id of ids) graded.set(id, k);
      lastK = Math.max(lastK, k);
      globals = 0;
      const reply = replies[k - 1] as V15Review | undefined;
      if (reply === undefined) throw new Error(`unexpected shard call: grading #${k} of ${ids.join(", ")} (only ${replies.length} canned)`);
      const ks = known();
      const nodes = (withOwnerExplanations(reply).nodes ?? []).filter((n) => ids.includes(n.id) || !ks.has(n.id));
      return { stdout: JSON.stringify({ summary: reply.summary, nodes }), stderr: "" };
    }
    if (input.outputSchema !== GLOBAL_REPLY) throw new Error("a referee call that is neither a shard nor the global pass");
    const at = Math.max(lastK, 1) - 1 + globals;
    globals += 1;
    const reply = replies[at] as V15Review | undefined;
    if (reply === undefined) throw new Error(`unexpected global call (reply #${at + 1}, only ${replies.length} canned)`);
    const { verdict, summary, patch_review, rejection_verdicts } = withOwnerExplanations(reply);
    return { stdout: JSON.stringify({ verdict, summary, patch_review: patch_review ?? null, rejection_verdicts: rejection_verdicts ?? null, cross_node: (reply as { cross_node?: unknown[] }).cross_node ?? [] }), stderr: "" };
  }) as typeof runCodex;
}

interface Harness {
  runDir: string;
  corePath: string;
  state: StateJson;
  calls: CodexRunInput[];
  args: (replies: unknown[], dryRun?: boolean) => VerifyStageArgs;
}

async function harness(): Promise<Harness> {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-v1_5-"));
  tmpDirs.push(repoRoot);
  const runDir = path.join(repoRoot, "doc", "verify", QID);
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  const corePath = path.join(runDir, VERIFY_FILES.coreJson);
  await writeFile(corePath, `${JSON.stringify(fixtureCore(), null, 2)}\n`, "utf8");
  await writeFile(path.join(runDir, VERIFY_FILES.coreTranscribed), `${JSON.stringify(fixtureCore(), null, 2)}\n`, "utf8");
  await writeFile(
    path.join(runDir, VERIFY_FILES.flatTex),
    await readFile(FLAT_FIXTURE, "utf8"),
    "utf8",
  );
  // the fixture cites van der Vaart (1998), which has no arXiv id: its source is supplied
  await mkdir(path.join(runDir, "discovery", "cited_sources"), { recursive: true });
  await writeFile(
    path.join(runDir, "discovery", "cited_sources", "vandervaart1998.txt"),
    "Theorem 3.1 (Delta method). If sqrt(n)(T_n - theta) converges weakly to T and phi is differentiable at theta, then ...",
    "utf8",
  );
  const state = createVerifyInitialState(QID, {
    phase: "v1",
    source: { input: "paper.tex", main_file: "main.tex", sha256: "src-hash" },
    targets: null,
    core_sha256: null,
    v1_rounds: 1,
    v1_5_rounds: 0,
    findings: [],
    report_path: null,
  });
  const calls: CodexRunInput[] = [];
  return {
    runDir,
    corePath,
    state,
    calls,
    args: (replies, dryRun = false) => ({
      repoRoot,
      qid: QID,
      runDir,
      state,
      deps: { runCodex: fakeCodex(replies, calls, corePath) },
      dryRun,
      // Every level graded in one pass (the review these tests judge is the whole core's); the
      // fix-as-you-go pause is tested in referee_shards.test.ts.
      refereeFixAsYouGo: false,
      log: () => {},
    }),
  };
}

/** The run's findings without the cited-source provenance notes every accepted review records. */
function paperFindings(state: StateJson) {
  return state.verify!.findings.filter((f) => !f.detail.startsWith("cited source checked: "));
}

/** What a V1 round that re-transcribed `id` leaves behind: the node's text in the transcription
 * moves, so its basis does and the next V1.5 pass grades it afresh. */
async function retranscribe(h: Harness, id: string): Promise<void> {
  const p = path.join(h.runDir, VERIFY_FILES.coreTranscribed);
  const core = JSON.parse(await readFile(p, "utf8")) as Core;
  const node = [...core.statements, ...core.assumptions, ...core.definitions].find((n) => n.id === id)! as { tex_locator?: { to: number } };
  node.tex_locator = { ...(node.tex_locator as object), to: (node.tex_locator?.to ?? 0) + 1 } as never;
  await writeFile(p, JSON.stringify(core, null, 2), "utf8");
}

/** A pass due a patch round at the ERROR cap halts (never fails); `--accept-cap` then records what
 * the loop leaves — the substantive-failure record the report reads. */
async function runAtCapAndAccept(h: Harness, replies: unknown[]): Promise<VerifyStageResult> {
  const halted = await runStageV1_5(h.args(replies));
  expect(halted.status).toBe("checkpoint");
  expect(h.state.verify!.cap_reached).toMatchObject({ counter: "patch_rounds", origin: "V1.5", rounds: MIN_PATCH_BACKSTOP, cap: MAX_PATCH_ROUNDS_PER_LEVEL });
  expect(existsSync(path.join(h.runDir, VERIFY_FILES.v1ReviseDirective))).toBe(true);
  return acceptV1_5AtCap(h.args([]));
}

async function readReview(runDir: string): Promise<V15Review> {
  return JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.v15Review), "utf8")) as V15Review;
}

describe("runStageV1_5 — the symbol pass on record", () => {
  it("the symbol verdicts and their keys are saved together: a pass that dies right after grades no symbol again", async () => {
    const h = await harness();
    // no node reply canned: the stage dies at its first shard, after the symbol pass
    await runStageV1_5(h.args([])).catch(() => undefined);
    const symbols = (JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.v15Symbols), "utf8")) as { symbols: Array<{ name: string; basis: string }> }).symbols;
    expect(symbols.length).toBeGreaterThan(0);
    const onDisk = await loadState(path.dirname(path.dirname(path.dirname(h.runDir))), QID);
    expect(onDisk.verify!.confirmed_symbols).toEqual(Object.fromEntries(symbols.map((v) => [v.name, v.basis])));
    const again = { ...h.args([]), state: onDisk };
    let symbolCalls = 0;
    const inner = again.deps.runCodex;
    again.deps = { runCodex: (async (i: CodexRunInput) => { if (i.outputSchema === SYMBOL_REPLY) symbolCalls += 1; return inner(i); }) as typeof runCodex };
    await runStageV1_5(again).catch(() => undefined);
    expect(symbolCalls).toBe(0);
  });
});

describe("runStageV1_5 — PASS", () => {
  it("applies a bookkeeping assumption, re-gates, and stamps the core hash", async () => {
    const h = await harness();
    const review: V15Review = {
      verdict: "PASS",
      summary: "reproduced both derivations.",
      nodes: fullNodes({
        "thm:ate-identification": {
          correctness: "bookkeeping",
          detail: "the tower-property step needs the ratio to be integrable.",
          bookkeeping_assumption: {
            condition: "\\(E[|DY/e(X)|] < \\infty\\)",
            reason: "the tower-property step interchanges expectation and conditioning.",
          },
        },
      }),
    };
    const result = await runStageV1_5(h.args([review]));

    expect(result.status).toBe("completed");
    // One shard per dependency level, then the global pass; no retry.
    expect(h.calls.map((c) => c.outputSchema)).toEqual([SHARD_REPLY, SHARD_REPLY, SHARD_REPLY, GLOBAL_REPLY]);
    for (const c of h.calls) {
      expect(c.reasoningEffort).toBe("high");
      expect(c.sandboxMode).toBe("read-only");
      expect(c.leanLsp).toBe(false);
    }
    // The global pass sees both artifacts, in order.
    const g = globalCalls(h.calls)[0]!.prompt;
    expect(g).toContain("=== TYPED CORE (discovery/core.json) ===");
    expect(g).toContain("=== PAPER (flattened LaTeX) ===");
    expect(g).toContain("\\begin{thm}\\label{thm:ate}");
    expect(g.indexOf("=== PAPER")).toBeGreaterThan(g.indexOf("=== TYPED CORE"));
    // The schema block is last (the prompt body also NAMES it, hence lastIndexOf).
    expect(g.lastIndexOf("=== GLOBAL OUTPUT ===")).toBeGreaterThan(g.indexOf("=== PAPER"));

    const written = parseTypedCore(await readFile(h.corePath, "utf8"), h.corePath);
    const added = written.assumptions.find((a) => a.id === "ass:bk-1");
    expect(added).toMatchObject({
      id: "ass:bk-1",
      kind: "regularity",
      condition: "\\(E[|DY/e(X)|] < \\infty\\)",
      bookkeeping: { flag: true, added_by: "V1.5" },
      used_by: ["thm:ate-identification"],
    });
    // `undefined` (never declared), not `[]` — see the AssumptionSchema comment.
    expect(added && "free_symbols" in added).toBe(false);
    expect(
      written.statements.find((s) => s.id === "thm:ate-identification")!.depends_on,
    ).toContain("ass:bk-1");
    // The written core carries the verify-only `bookkeeping` tag, so it is well-formed for the
    // V stages and (deliberately) a G6 violation for any research-mode caller.
    expect(runStructuralGate(written, { allowBookkeeping: true }).ok).toBe(true);
    expect(runStructuralGate(written).ok).toBe(false);

    expect(h.state.stage_completed).toBe("V1.5");
    expect(h.state.verify!.core_sha256).toBe(await sha256File(h.corePath));
    expect(await readReview(h.runDir)).toMatchObject({ verdict: "PASS" });
    expect(paperFindings(h.state)).toEqual([]);
  });

});

describe("runStageV1_5 — computed verdict", () => {
  it("overrides a claimed PASS when a node is graded `error` (patch rounds spent → FAIL)", async () => {
    const h = await harness();
    h.state.verify!.patch_rounds = MIN_PATCH_BACKSTOP;
    const before = await sha256File(h.corePath);
    const review: V15Review = {
      verdict: "PASS", // the model's own claim — must not win
      summary: "looks fine to me.",
      nodes: fullNodes({
        "lem:ipw-identity": {
          correctness: "error",
          detail: "the identity drops the \\(1-e(X)\\) arm.",
          witness: "Take \\(e(X) \\equiv 1/2\\), \\(Y = D\\): the left side is 1, the right side 1/2.",
        },
        "thm:ate-identification": {
          correctness: "unclear",
          detail: "shadowed by the lemma's error.",
        },
      }),
    };
    const result = await runAtCapAndAccept(h, [review]);

    expect(result.status).toBe("failed");
    expect(result.message).toContain("lem:ipw-identity");
    expect(result.message).toContain("main.tex:19-21"); // the tex locator
    expect(await readReview(h.runDir)).toMatchObject({ verdict: "FAIL" });
    expect(paperFindings(h.state)).toEqual([
      {
        node: "lem:ipw-identity",
        stage: "V1.5",
        kind: "refuted",
        detail: "the identity drops the \\(1-e(X)\\) arm.",
        witness: expect.stringContaining("Take"),
        at: expect.any(String),
      },
      {
        node: "thm:ate-identification",
        stage: "V1.5",
        kind: "unresolved",
        detail: expect.stringContaining("shadowed by the lemma's error."),
        witness: null,
        at: expect.any(String),
      },
    ]);
    // A refutation touches neither the core nor the F-stage entry gate.
    expect(await sha256File(h.corePath)).toBe(before);
    expect(h.state.verify!.core_sha256).toBeNull();
    expect(h.state.stage_completed).not.toBe("V1.5");
  });
});

describe("runStageV1_5 — drift repeat", () => {
  it("the same node drifting again for a NEW reason (a different fix) is allowed another round", async () => {
    const h = await harness();
    const a: V15Review = { verdict: "REVISE", summary: "a.", nodes: fullNodes({ "thm:ate-identification": { faithfulness: "drift", detail: "x", fix: { add_depends_on: ["ass:overlap"] } } }) };
    const b: V15Review = { verdict: "REVISE", summary: "b.", nodes: fullNodes({ "thm:ate-identification": { faithfulness: "drift", detail: "y", fix: { add_depends_on: ["lem:ipw-identity"] } } }) };
    const args = h.args([a, b, b]);
    expect((await runStageV1_5(args)).status).toBe("revise");
    h.state.verify!.v1_5_rounds = 1;
    expect((await runStageV1_5(args)).status).toBe("revise");
    h.state.verify!.v1_5_rounds = 2;
    const repeat = await runStageV1_5(args);
    expect(repeat.status).toBe("checkpoint"); // same fix twice
    expect(repeat.message).toMatch(/drift REPEATED/);
  });

  it("drift that moves to a different node is allowed another round", async () => {
    const h = await harness();
    const a: V15Review = { verdict: "REVISE", summary: "a.", nodes: fullNodes({ "thm:ate-identification": { faithfulness: "drift", detail: "x" } }) };
    const b: V15Review = { verdict: "REVISE", summary: "b.", nodes: fullNodes({ "lem:ipw-identity": { faithfulness: "drift", detail: "y" } }) };
    const args = h.args([a, b]);
    expect((await runStageV1_5(args)).status).toBe("revise");
    h.state.verify!.v1_5_rounds = 1;
    // V1's round moved lem:ipw-identity too (a node whose basis is unchanged keeps its verdict and
    // cannot newly drift), so the fresh pass grades both.
    await retranscribe(h, "lem:ipw-identity");
    expect((await runStageV1_5(args)).status).toBe("revise");
    expect(h.state.verify!.last_drift).toEqual({ "lem:ipw-identity": "" });
  });
});

/** Every node's revise rounds spent. */
const capped = (): Record<string, number> => Object.fromEntries(["ass:overlap", "thm:ate-identification", "lem:ipw-identity"].map((k) => [k, MAX_REVISE_ROUNDS_PER_NODE]));

describe("runStageV1_5 — revise cap", () => {
  it("the cap is per drifting node: a node with rounds left revises although another node is spent", async () => {
    const h = await harness();
    h.state.verify!.v1_5_rounds = 3;
    h.state.verify!.v1_5_rounds_by_node = { "thm:ate-identification": MAX_REVISE_ROUNDS_PER_NODE };
    const review: V15Review = { verdict: "REVISE", summary: "x.", nodes: fullNodes({ "ass:overlap": { faithfulness: "drift", detail: "missing a clause." } }) };
    expect((await runStageV1_5(h.args([review]))).status).toBe("revise");
    expect(h.state.verify!.v1_5_rounds).toBe(4);
    expect(h.state.verify!.v1_5_rounds_by_node).toEqual({ "thm:ate-identification": MAX_REVISE_ROUNDS_PER_NODE, "ass:overlap": 1 });
  });

  it("on the last allowed round with drift left: a checkpoint, never a verdict — the drift is recorded, the errors graded on it stay provisional", async () => {
    const h = await harness();
    h.state.verify!.v1_5_rounds_by_node = capped();
    // the last round was told this drift (with an edit it could not apply)
    h.state.verify!.last_drift = { "thm:ate-identification": "{}" };
    const review: V15Review = {
      verdict: "REVISE",
      summary: "the fold index stays free; the lemma is wrong.",
      nodes: fullNodes({
        "thm:ate-identification": { faithfulness: "drift", detail: "still missing a dependency." },
        "ass:overlap": { ambiguity: "unresolvable", detail: "free fold index; the rate changes." },
        "lem:ipw-identity": { correctness: "error", detail: "drops an arm.", witness: "Take e=1/2." },
      }),
    };
    const result = await runStageV1_5(h.args([review]));
    expect(result.status).toBe("checkpoint");
    expect(result.message).toMatch(/could not make the core faithful at 1 node\(s\).*1 error\(s\) and 1 unresolvable reading\(s\) graded on this core are provisional/su);
    expect(paperFindings(h.state).map((f) => [f.node, f.kind])).toEqual([["thm:ate-identification", "note"]]);
  });

  // Live extreme-effects (2026-10-08): a repair round re-opened a result whose three rounds earlier
  // passes had spent; the halt read "V1 could not make the core faithful … after 7 revise round(s)"
  // though no transcription round had been run on that drift.
  it("a cap already spent when the drift appears says so: the rounds are earlier passes', none was run on it, and what the referee asks", async () => {
    const h = await harness();
    h.state.verify!.v1_5_rounds = 7;
    h.state.verify!.v1_5_rounds_by_node = capped();
    const fix = { add_depends_on: ["ass:overlap"], remove_depends_on: null, wire_into: null, unwire_from: null, extend_to: null, new_assumption: null, setting: "The sample is i.i.d." };
    const review: V15Review = { verdict: "REVISE", summary: "x.", nodes: fullNodes({ "thm:ate-identification": { faithfulness: "drift", detail: "the setting describes another estimator.", fix } as never }) };
    const result = await runStageV1_5(h.args([review]));
    expect(result.status).toBe("checkpoint");
    expect(result.message).toContain(`drift at 1 node(s) with no revise round left for it, and none was run on it — thm:ate-identification (${MAX_REVISE_ROUNDS_PER_NODE} of ${MAX_REVISE_ROUNDS_PER_NODE} round(s) counted on it by earlier passes; the referee asks a setting and wiring); 7 of `);
    expect(result.message).not.toContain("could not make the core faithful");
    // drift a revise round was told about and left keeps the old line
    const told = await harness();
    told.state.verify!.v1_5_rounds_by_node = capped();
    told.state.verify!.last_drift = { "thm:ate-identification": "{}" };
    const again: V15Review = { verdict: "REVISE", summary: "x.", nodes: fullNodes({ "thm:ate-identification": { faithfulness: "drift", detail: "still missing a dependency." } }) };
    expect((await runStageV1_5(told.args([again]))).message).toContain("could not make the core faithful at 1 node(s)");
    expect(spentCapLine([{ id: "lem:a", fix: null } as never], {}, 2, 15)).toBe(`lem:a (0 of ${MAX_REVISE_ROUNDS_PER_NODE} round(s) counted on it by earlier passes; the referee asks no edit named); 2 of 15 round(s) in all`);
  });

  it("on FAIL, pinned readings are still recorded as suggestion notes", async () => {
    const h = await harness();
    h.state.verify!.patch_rounds = MIN_PATCH_BACKSTOP;
    const review: V15Review = {
      verdict: "FAIL",
      summary: "one error, one pin.",
      nodes: fullNodes({
        "ass:overlap": {
          ambiguity: "pinned",
          detail: "two readings.",
          reading: { reading: "a.s. w.r.t. P", evidence: "the proof integrates against P" },
        },
        "lem:ipw-identity": { correctness: "error", detail: "drops an arm.", witness: "Take e=1/2." },
      }),
    };
    const result = await runAtCapAndAccept(h, [review]);
    expect(result.status).toBe("failed");
    // thm:ate-identification uses the refuted lemma: unclear ("depends on …, graded error"), unresolved.
    expect(paperFindings(h.state).map((f) => [f.node, f.kind]).sort()).toEqual([
      ["ass:overlap", "note"],
      ["lem:ipw-identity", "refuted"],
      ["thm:ate-identification", "unresolved"],
    ]);
    expect(paperFindings(h.state).find((f) => f.node === "ass:overlap")!.detail).toContain("pinned reading");
  });

  it("a pinned reading is added to the core as an explicit assumption and reported as a note", async () => {
    const h = await harness();
    const review: V15Review = {
      verdict: "PASS",
      summary: "one reading pinned.",
      nodes: fullNodes({
        "ass:overlap": {
          ambiguity: "pinned",
          detail: "`almost surely` could refer to P or to the sampling measure.",
          reading: { reading: "`almost surely` is with respect to P.", evidence: "the proof integrates against P." },
        },
      }),
    };
    const result = await runStageV1_5(h.args([review]));
    expect(result.status).toBe("completed");
    const core = JSON.parse(await readFile(h.corePath, "utf8")) as { assumptions: Array<{ id: string; condition: string; bookkeeping?: { reason: string } }>; statements: Array<{ id: string; depends_on: string[] }> };
    const pin = core.assumptions.find((a) => a.id === "ass:pin-1");
    expect(pin?.condition).toBe("`almost surely` is with respect to P.");
    expect(pin?.bookkeeping?.reason).toContain("pins reading of ass:overlap");
    // wired into every statement that depended on the disambiguated node
    const dependents = core.statements.filter((s) => s.depends_on.includes("ass:overlap"));
    expect(dependents.length).toBeGreaterThan(0);
    for (const s of dependents) expect(s.depends_on).toContain("ass:pin-1");
    expect(paperFindings(h.state).map((f) => f.kind)).toEqual(["note"]);
    expect(paperFindings(h.state)[0]!.detail).toContain("pinned reading");
  });

  it("on the last allowed round, leftover drift alone is a checkpoint: our transcription failed", async () => {
    const h = await harness();
    h.state.verify!.v1_5_rounds_by_node = capped();
    const review: V15Review = {
      verdict: "REVISE",
      summary: "one dependency still missing.",
      nodes: fullNodes({ "thm:ate-identification": { faithfulness: "drift", detail: "depends_on lacks lem:ipw-identity." } }),
    };
    const result = await runStageV1_5(h.args([review]));
    expect(result.status).toBe("checkpoint");
    expect(paperFindings(h.state).map((f) => f.kind)).toEqual(["note"]);
  });
});

describe("runStageV1_5 — REVISE", () => {
  it("writes the V1 directive and leaves the core untouched", async () => {
    const h = await harness();
    const before = await sha256File(h.corePath);
    const review: V15Review = {
      verdict: "FAIL", // claimed FAIL with no `error` node — the grades give REVISE
      summary: "transcription problems.",
      nodes: fullNodes({
        "thm:ate-identification": {
          faithfulness: "drift",
          detail: "the paper conditions on \\(X\\); the core states it unconditionally.",
        },
        "ass:overlap": {
          faithfulness: "drift",
          detail: "the core drops `almost surely`.",
        },
      }),
    };
    const result = await runStageV1_5(h.args([review]));

    expect(result.status).toBe("revise");
    expect(await readReview(h.runDir)).toMatchObject({ verdict: "REVISE" });
    const directive = JSON.parse(
      await readFile(path.join(h.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"),
    ) as { round: number; findings: Array<{ id: string; axis: string; detail: string }> };
    expect(directive.round).toBe(1); // the round is charged here, to each drifting node
    expect(h.state.verify!.v1_5_rounds_by_node).toEqual({ "ass:overlap": 1, "thm:ate-identification": 1 });
    expect(directive.findings.map((f) => [f.id, f.axis]).sort()).toEqual([
      ["ass:overlap", "faithfulness"],
      ["thm:ate-identification", "faithfulness"],
    ]);
    expect(await sha256File(h.corePath)).toBe(before);
    expect(h.state.verify!.core_sha256).toBeNull();
    expect(h.state.stage_completed).not.toBe("V1.5");
  });
});

describe("runStageV1_5 — contract violations", () => {
  it("a shard's grade of an unknown node id is retried once, then dropped: the shard's own grades stand", async () => {
    const h = await harness();
    const bad: V15Review = {
      verdict: "PASS",
      summary: "graded a node that is not in the core.",
      nodes: [...fullNodes(), verdictNode("thm:not-a-node")],
    };
    const result = await runStageV1_5(h.args([bad, bad]));

    const retries = retriesOf(h.calls);
    expect(retries).toHaveLength(3); // each level's shard, once
    for (const r of retries) expect(r.prompt).toContain("thm:not-a-node");
    expect(result.status).toBe("completed");
    expect((await readReview(h.runDir)).nodes.map((n) => n.id).sort()).toEqual([...CORE_IDS].sort());
  });

  it("retries once on an `error` with no witness, then checkpoints", async () => {
    const h = await harness();
    const bad: V15Review = {
      verdict: "FAIL",
      summary: "an error I cannot show.",
      nodes: fullNodes({
        "lem:ipw-identity": {
          correctness: "error",
          detail: "I could not reproduce step 2.",
        },
      }),
    };
    const result = await runStageV1_5(h.args([bad, bad]));

    expect(retriesOf(h.calls)).toHaveLength(1); // the lemma's shard, once; then the lemma is set aside
    expect(result.status).toBe("checkpoint");
    expect(result.message).toContain("set aside (lem:ipw-identity");
    expect(result.message).toContain("no witness");
    expect(result.message).not.toContain("carry no verdict");
    expect(paperFindings(h.state)).toEqual([]);
  });

  it("accepts a corrected reply on the retry", async () => {
    const h = await harness();
    const bad: V15Review = {
      verdict: "PASS",
      summary: "duplicate grade.",
      nodes: [...fullNodes(), verdictNode("lem:ipw-identity")],
    };
    const good: V15Review = {
      verdict: "PASS",
      summary: "corrected.",
      nodes: fullNodes(),
    };
    const result = await runStageV1_5(h.args([bad, good]));

    const retries = retriesOf(h.calls);
    expect(retries).toHaveLength(1); // the shard grading lem:ipw-identity
    expect(retries[0]!.prompt).toContain("graded more than once");
    expect(result.status).toBe("completed");
    expect(h.state.stage_completed).toBe("V1.5");
    // Every live call's prompt is on disk (discovery/prompts), the retry's included, beside its reply.
    const dir = path.join(h.runDir, VERIFY_FILES.v15Prompts);
    const files = await readdir(dir);
    expect(files.some((f) => /^v1_5_shard_L1-1_retry__.+\.txt$/.test(f))).toBe(true);
    const saved = await Promise.all(files.map((f) => readFile(path.join(dir, f), "utf8")));
    for (const c of h.calls) expect(saved).toContain(c.prompt);
    const raw = await readdir(path.join(h.runDir, "codex_raw"));
    for (const f of files) expect(raw.some((r) => r.startsWith(`${f.split("__")[0]}__`))).toBe(true);
  });
});

describe("runStageV1_5 — coverage", () => {
  it("retries and checkpoints when the referee grades NOTHING", async () => {
    const h = await harness();
    const empty: V15Review = { verdict: "PASS", summary: "looks fine.", nodes: [] };
    const result = await runStageV1_5(h.args([empty, empty]));

    // Each level's shard is retried once, told which of its nodes carry no verdict.
    const retries = retriesOf(h.calls);
    expect(retries).toHaveLength(3);
    expect(retries.map((r) => r.prompt.match(/(\d+) core node\(s\) carry no verdict/)?.[1])).toEqual(["3", "2", "1"]);
    for (const id of CORE_IDS) expect(retries.some((r) => r.prompt.includes(`carry no verdict: ${id}`) || new RegExp(`carry no verdict: [^\n]*${id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}`).test(r.prompt))).toBe(true);
    expect(result.status).toBe("checkpoint");
    expect(result.message).toContain("6 node(s) broke the output contract twice and were set aside");
    expect(result.message).toContain("carries no verdict");
    // An ungraded core is never accepted, however clean the claimed verdict.
    expect(h.state.stage_completed).not.toBe("V1.5");
    expect(h.state.verify!.core_sha256).toBeNull();
    expect(h.state.verify!.confirmed ?? {}).toEqual({});
  });

});

describe("runStageV1_5 — bookkeeping is applied only on a `bookkeeping` grade", () => {
  it("rejects a condition attached to any other grade", async () => {
    const h = await harness();
    const before = await sha256File(h.corePath);
    const bad: V15Review = {
      verdict: "PASS",
      summary: "slipped a condition onto an `ok` node.",
      nodes: fullNodes({
        "thm:ate-identification": {
          correctness: "ok",
          bookkeeping_assumption: { condition: "\\(X\\) is bounded", reason: "step 2." },
        },
      }),
    };
    const result = await runStageV1_5(h.args([bad, bad]));

    const retries = retriesOf(h.calls);
    expect(retries).toHaveLength(1); // the theorem's shard, once; then set aside
    expect(retries[0]!.prompt).toContain("carries a bookkeeping_assumption but is graded correctness");
    expect(result.status).toBe("checkpoint");
    expect(result.message).toContain("set aside (thm:ate-identification");
    // The core is never touched by a review the contract rejects.
    expect(await sha256File(h.corePath)).toBe(before);
    expect(
      parseTypedCore(await readFile(h.corePath, "utf8"), h.corePath).assumptions.some((a) =>
        a.id.startsWith("ass:bk-"),
      ),
    ).toBe(false);
  });
});

describe("runStageV1_5 — V1 lint warnings", () => {
  const warningsPath = (runDir: string): string =>
    path.join(runDir, "discovery", "v1_lint_warnings.json");

  it("appends V1's warnings for the referee to confirm", async () => {
    const h = await harness();
    await writeFile(
      warningsPath(h.runDir),
      JSON.stringify({
        warnings: [
          "thm:ate-identification depends on ass:unconfoundedness which the environment never references; V1.5 must confirm the inheritance.",
          // an inline citation (`inline_citations.ts`): a line about its host node, like any other
          "thm:ate-identification: the proof of thm:ate invokes [vdv1998, Theorem 2.18] (thm:ate/proof/1/1): a published result used inside the proof, with no cited node of its own. Not a defect of the node or of its wiring: grade the step as any use of a published result. paper: \"…\"",
        ],
        parser_warnings: ["defs.tex is \\input twice; folded once."],
      }),
      "utf8",
    );
    const result = await runStageV1_5(
      h.args([{ verdict: "PASS", summary: "all nodes.", nodes: fullNodes() }]),
    );
    expect(result.status).toBe("completed");
    // A lint line about a node goes to the shard grading it; the parser's notes about the source tree
    // to the global pass. Each block sits before the reply contract, the last thing the referee reads.
    const shard = shardCalls(h.calls).find((c) => shardIds(c.prompt).includes("thm:ate-identification"))!.prompt;
    expect(shard).toContain("=== V1 LINT WARNINGS (confirm each) ===");
    expect(shard).toContain("which the environment never references");
    expect(shard).toContain("invokes [vdv1998, Theorem 2.18]");
    expect(shardCalls(h.calls).filter((c) => c.prompt.includes("invokes [vdv1998, Theorem 2.18]"))).toHaveLength(1);
    expect(globalCalls(h.calls)[0]!.prompt).not.toContain("invokes [vdv1998, Theorem 2.18]");
    expect(shard.lastIndexOf("=== SHARD OUTPUT ===")).toBeGreaterThan(shard.indexOf("=== V1 LINT WARNINGS"));
    const prompt = globalCalls(h.calls)[0]!.prompt;
    expect(prompt).toContain("=== V1 LINT WARNINGS (confirm each) ===");
    expect(prompt).toContain("defs.tex is \\input twice; folded once.");
    expect(prompt.lastIndexOf("=== GLOBAL OUTPUT ===")).toBeGreaterThan(
      prompt.indexOf("=== V1 LINT WARNINGS"),
    );
  });

  it("fails loudly on a malformed warnings file rather than dropping it", async () => {
    const h = await harness();
    await writeFile(warningsPath(h.runDir), JSON.stringify({ warnings: "oops" }), "utf8");
    await expect(
      runStageV1_5(h.args([{ verdict: "PASS", summary: "x", nodes: fullNodes() }])),
    ).rejects.toThrow(/v1_lint_warnings\.json/);
    expect(h.calls).toEqual([]);
  });
});

describe("runStageV1_5 — dry run", () => {
  it("writes a synthetic PASS and accepts the core without calling codex", async () => {
    const h = await harness();
    const before = await sha256File(h.corePath);
    const result = await runStageV1_5(h.args([], true));

    expect(result.status).toBe("completed");
    expect(h.calls).toEqual([]);
    const review = await readReview(h.runDir);
    expect(review.verdict).toBe("PASS");
    expect(review.nodes.every((n) => n.graded === "fresh" && n.correctness === "ok")).toBe(true);
    expect(new Set(review.nodes.map((n) => n.id))).toEqual(new Set(CORE_IDS));
    expect(h.state.stage_completed).toBe("V1.5");
    expect(h.state.verify!.core_sha256).toBe(before);
    // a second dry pass over the same core carries every synthetic grade
    await runStageV1_5(h.args([], true));
    expect((await readReview(h.runDir)).nodes.every((n) => n.graded === "carried")).toBe(true);
  });

});

describe("runStageV1_5 — minimal patches", () => {
  const error = {
    correctness: "error" as const,
    detail: "the identity needs overlap bounded away from zero.",
    witness: "Take $e(X) \\to 0$ on a sequence: $E[DY/e(X)]$ diverges.",
  };

  async function withFixerPatch(h: Harness): Promise<void> {
    h.state.verify!.paper_errors = { "lem:ipw-identity": { detail: error.detail, witness: error.witness } };
    await writeFile(path.join(h.runDir, VERIFY_FILES.coreTranscribed), await readFile(h.corePath, "utf8"), "utf8");
    await writeFile(
      path.join(h.runDir, VERIFY_FILES.patches),
      JSON.stringify({
        key_results: ["thm:ate-identification"],
        key_contribution: "identification of the ATE by inverse weighting",
        patches: [
          {
            node: "lem:ipw-identity",
            corrected_statement: "\\(E[DY/e(X)] = E[Y(1)]\\) whenever \\(e\\) is bounded below: \\(e(X) \\ge \\eta > 0\\) a.s.",
            proof_note: "bound DY/e(X) by |Y|/η before the tower property",
          },
        ],
        unfixable: [],
      }),
      "utf8",
    );
  }

  /** The theorem, which uses the lemma, restated with the hypothesis the lemma's repair adds (a
   * consequential patch: `consequence_of` the lemma's repair). */
  async function restateTheorem(h: Harness): Promise<void> {
    const file = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.patches), "utf8"));
    file.patches.push({
      node: "thm:ate-identification",
      corrected_statement: "Suppose \\(e(X) \\ge \\eta > 0\\) a.s. Then \\(\\tau = E[DY/e(X) - (1-D)Y/(1-e(X))]\\).",
      proof_note: "apply the repaired lemma to each arm",
      consequence_of: ["lem:ipw-identity"],
      reason: "The theorem now assumes the propensity bound the repair of the lemma adds.",
    });
    await writeFile(path.join(h.runDir, VERIFY_FILES.patches), JSON.stringify(file), "utf8");
  }

  it("an error on a faithful core with patch rounds left goes to V1 patch mode; nothing is recorded yet", async () => {
    const h = await harness();
    const before = await sha256File(h.corePath);
    const review: V15Review = { verdict: "FAIL", summary: "one error.", nodes: fullNodes({ "lem:ipw-identity": error }) };
    const result = await runStageV1_5(h.args([review]));
    expect(result.status).toBe("patch");
    const directive = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    // Every level is graded: the theorem using the refuted lemma is unclear ("depends on …"), to be written out.
    expect(directive).toMatchObject({
      mode: "patch",
      round: 1,
      findings: [
        { id: "lem:ipw-identity", axis: "correctness", witness: expect.stringContaining("diverges") },
        { id: "thm:ate-identification", axis: "clarify", detail: expect.stringContaining("depends on lem:ipw-identity, graded error") },
      ],
    });
    expect(paperFindings(h.state)).toEqual([]);
    expect(await sha256File(h.corePath)).toBe(before);
  });

  it("a confirming pass over the patched core records each patch as a confirmed repair and accepts the core", async () => {
    const h = await harness();
    await withFixerPatch(h);
    const review: V15Review = {
      verdict: "PASS",
      summary: "the patched lemma holds.",
      nodes: fullNodes(),
      patch_review: { key_results_ok: true, detail: "the ATE theorem is the headline." },
    };
    const result = await runStageV1_5(h.args([review]));
    expect(result.status).toBe("completed");
    // the global pass sees the corrected core AND the printed text of each patched node
    const g = globalCalls(h.calls)[0]!.prompt;
    expect(g).toContain("=== PATCHES");
    expect(g).toContain('"printed":"\\\\(E[DY/e(X)] = E[Y(1)]\\\\)"');
    const core = JSON.parse(await readFile(h.corePath, "utf8")) as Core;
    const lem = core.statements.find((s) => s.id === "lem:ipw-identity")!;
    expect(lem.statement).toContain("bounded below");
    expect(lem.proof_tex).toContain("[Proof change (minimal patch):");
    expect(h.state.verify!.core_sha256).toBe(await sha256File(h.corePath));
    expect(paperFindings(h.state)).toEqual([
      expect.objectContaining({
        node: "lem:ipw-identity",
        kind: "refuted",
        witness: expect.stringContaining("diverges"),
        patch: expect.objectContaining({ confirmed: true, corrected_statement: expect.stringContaining("bounded below") }),
      }),
    ]);
  });

  /** A fixer's note on a repair (the referee writes none; it grades this one's clarity). */
  const shaped = (fix = "The repair requires the propensity to be bounded below.", over: Partial<OwnerExplanation> = {}): OwnerExplanation => ({
    claim: "The lemma claims the inverse-weighting identity under overlap alone.",
    defects: [{ kind: "out_of_domain", step_unit: "lem:ipw/proof/1/1", uses: "integrability of the weight $1/e(X)$", assumed_on: "propensities bounded away from zero", applied_at: "propensities tending to zero", detail: null }],
    why: { objects: ["$e(X)=1/n$ on half the covariate values"], consequence: "the weighted mean $E\\{DY/e(X)\\}$ grows like $n$ and diverges" },
    fix,
    gives_up: null,
    ...over,
  });
  /** The lemma's repair carrying the fixer's note `note`. */
  async function withNote(h: Harness, note: OwnerExplanation): Promise<void> {
    const pf = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.patches), "utf8"));
    pf.patches[0].owner_explanation = note;
    await writeFile(path.join(h.runDir, VERIFY_FILES.patches), JSON.stringify(pf), "utf8");
  }

  it("a confirmed repair whose note the referee grades unclear: a `note` finding in a refinement round; the repair stands, the ledger gains no error", async () => {
    const h = await harness();
    await withFixerPatch(h);
    await withNote(h, shaped("Bound e below."));
    const ledger = structuredClone(h.state.verify!.paper_errors);
    const review: V15Review = {
      verdict: "PASS",
      summary: "the patched lemma holds.",
      nodes: fullNodes({ "lem:ipw-identity": { explanation_clarity: { grade: "unclear", reason: "it never says which step fails" } } }),
      patch_review: { key_results_ok: true, detail: "the ATE theorem is the headline." },
    };
    const result = await runStageV1_5(h.args([review]));
    expect(result).toMatchObject({ status: "patch", round_kind: "refinement" });
    const directive = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(directive.findings).toEqual([{ id: "lem:ipw-identity", axis: "note", detail: expect.stringContaining("it never says which step fails"), witness: null }]);
    expect((await readReview(h.runDir)).nodes.find((n) => n.id === "lem:ipw-identity")).toMatchObject({ correctness: "ok", explanation_clarity: { grade: "unclear" } });
    expect(h.state.verify!.paper_errors).toEqual(ledger);
    expect(paperFindings(h.state)).toEqual([]);
    // the shard confirming the repair is shown the fixer's note as the author reads it
    const shard = shardCalls(h.calls).find((c) => shardIds(c.prompt).includes("lem:ipw-identity"))!.prompt;
    expect(shard).toContain("Bound e below.");
  });

  it("disputed key results send the patch file back to the fixer", async () => {
    const h = await harness();
    await withFixerPatch(h);
    const review: V15Review = {
      verdict: "PASS",
      summary: "patches hold, but the headline list is short.",
      nodes: [...fullNodes()],
      patch_review: { key_results_ok: false, detail: "lem:delta-method feeds the inference result the abstract announces." },
    };
    const result = await runStageV1_5(h.args([review]));
    expect(result.status).toBe("patch");
    const directive = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(directive.findings).toEqual([expect.objectContaining({ id: "run", axis: "key_results" })]);
  });

  it("a patch the confirming pass rejects, with the patch rounds spent, is a substantive failure recorded with the unconfirmed patch", async () => {
    const h = await harness();
    await withFixerPatch(h);
    h.state.verify!.patch_rounds = MIN_PATCH_BACKSTOP;
    const review: V15Review = {
      verdict: "FAIL",
      summary: "the patch does not close the gap.",
      nodes: [
        ...fullNodes({ "lem:ipw-identity": { correctness: "error", detail: "Y is not integrable either.", witness: "Cauchy Y." } }),
      ],
      patch_review: { key_results_ok: true, detail: "ok" },
    };
    const result = await runAtCapAndAccept(h, [review]);
    expect(result.status).toBe("failed");
    const refuted = paperFindings(h.state).filter((f) => f.kind === "refuted");
    expect(refuted.some((f) => f.patch && !f.patch.confirmed)).toBe(true);
    expect(refuted.some((f) => f.detail === "Y is not integrable either.")).toBe(true);
  });

  it("a hand edit of core.json is kept aside, and deleting patches.json leaves the plain transcription", async () => {
    const h = await harness();
    await withFixerPatch(h);
    const pass: V15Review = { verdict: "PASS", summary: "ok", nodes: [...fullNodes()], patch_review: { key_results_ok: true, detail: "ok" } };
    // the harness core.json is the UNPATCHED one — as if the operator had reverted it by hand
    await runStageV1_5(h.args([pass]));
    expect(existsSync(`${h.corePath}.prev`)).toBe(true);
    // start the repair over
    await rm(path.join(h.runDir, VERIFY_FILES.patches));
    const plain: V15Review = { verdict: "PASS", summary: "ok", nodes: fullNodes() };
    await runStageV1_5(h.args([plain]));
    const core = JSON.parse(await readFile(h.corePath, "utf8")) as Core;
    expect(core.statements.find((s) => s.id === "lem:ipw-identity")!.statement).toBe("\\(E[DY/e(X)] = E[Y(1)]\\)");
  });

  it("a result restated to follow another repair (consequence_of) must be confirmed too", async () => {
    const h = await harness();
    await withFixerPatch(h);
    await restateTheorem(h);
    const review: V15Review = {
      verdict: "PASS",
      summary: "lemma fine; theorem under the new hypothesis not followed.",
      nodes: [...fullNodes({ "thm:ate-identification": { correctness: "unclear", detail: "gap" } })],
      patch_review: { key_results_ok: true, detail: "ok" },
    };
    const result = await runStageV1_5(h.args([review]));
    expect(result.status).toBe("patch");
    const directive = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(directive.findings).toEqual([expect.objectContaining({ id: "thm:ate-identification", axis: "patch rejected" })]);
  });

  it("a hand-written patch file must still address every error in the ledger", async () => {
    const h = await harness();
    await withFixerPatch(h);
    h.state.verify!.paper_errors!["thm:ate-identification"] = { detail: "another error", witness: "w" };
    const result = await runStageV1_5(h.args([]));
    expect(result.status).toBe("checkpoint");
    expect(result.message).toContain(`"thm:ate-identification" has a finding but neither a patch`);
  });

  it("a hand-edited patch file that makes an unfixable node block a key result stops for the operator", async () => {
    const h = await harness();
    await withFixerPatch(h);
    const file = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.patches), "utf8"));
    file.patches = [];
    file.unfixable = [{ node: "lem:ipw-identity", reason: "hand-declared" }];
    await writeFile(path.join(h.runDir, VERIFY_FILES.patches), JSON.stringify(file), "utf8");
    const result = await runStageV1_5(h.args([]));
    expect(result.status).toBe("checkpoint");
    expect(result.message).toContain("unfixable on a key result's path");
  });

  it("a supporting patch (no error of the paper behind it) is a change, not a refutation", async () => {
    const h = await harness();
    await withFixerPatch(h);
    const file = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.patches), "utf8"));
    file.patches.push({
      node: "thm:ate-identification",
      corrected_statement: null,
      proof_note: "the IPW identity is applied under the bounded-below propensity",
    });
    await writeFile(path.join(h.runDir, VERIFY_FILES.patches), JSON.stringify(file), "utf8");
    const review: V15Review = {
      verdict: "PASS",
      summary: "ok",
      nodes: [...fullNodes()],
      patch_review: { key_results_ok: true, detail: "ok" },
    };
    expect((await runStageV1_5(h.args([review]))).status).toBe("completed");
    expect(paperFindings(h.state).map((f) => [f.node, f.kind])).toEqual([["lem:ipw-identity", "refuted"]]);
  });

  it("a missing use of another RESULT on a repaired node is the paper's wiring: a revise round the runner applies, not the fixer's", async () => {
    const h = await harness();
    await withFixerPatch(h);
    const review: V15Review = {
      verdict: "REVISE",
      summary: "the proof uses the delta method, not wired.",
      nodes: [
        ...fullNodes({
          "lem:ipw-identity": {
            faithfulness: "drift",
            detail: "the proof applies the delta method; the result is not wired to it",
            fix: { add_depends_on: ["lem:delta-method"], remove_depends_on: null, extend_to: null, new_assumption: null },
          },
        }),
      ],
      patch_review: { key_results_ok: true, detail: "ok" },
    };
    const result = await runStageV1_5(h.args([review]));
    expect(result.status).toBe("revise");
    const directive = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(directive.mode).not.toBe("patch");
    expect(JSON.stringify(directive)).toContain("lem:delta-method");
  });

  it("drift on a repaired node is the repair's defect: a `patch rejected` objection, never a revise round", async () => {
    const h = await harness();
    await withFixerPatch(h);
    const review: V15Review = {
      verdict: "REVISE",
      summary: "a premise the paper concludes is wired as a hypothesis.",
      nodes: [
        ...fullNodes({
          "lem:ipw-identity": {
            faithfulness: "drift",
            detail: "ass:overlap is concluded by the paper, not assumed",
            fix: { add_depends_on: null, remove_depends_on: ["ass:overlap"], extend_to: null, new_assumption: null },
          },
        }),
      ],
      patch_review: { key_results_ok: true, detail: "ok" },
    };
    const result = await runStageV1_5(h.args([review]));
    expect(result.status).toBe("patch");
    const directive = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(directive.mode).toBe("patch");
    expect(directive.findings).toEqual([
      expect.objectContaining({ id: "lem:ipw-identity", axis: "patch rejected", detail: expect.stringContaining("the repaired text does not fit the paper around it: ass:overlap is concluded") }),
    ]);
    // the referee's wiring fix reaches the fixer in the terms of its reply
    expect(directive.findings[0].detail).toContain("The referee's fix: it no longer uses ass:overlap: list them in `drops`.");
    expect(await readReview(h.runDir)).toMatchObject({ verdict: "PASS" });
    expect(h.state.verify!.v1_5_rounds).toBe(0);
  });

  it("a correct but non-minimal patch is not accepted: the weaker condition goes back to the fixer", async () => {
    const h = await harness();
    await withFixerPatch(h);
    const review: V15Review = {
      verdict: "PASS",
      summary: "the patch works but is stronger than needed.",
      nodes: fullNodes({
        "lem:ipw-identity": {
          correctness: "error",
          detail: "not minimal",
          witness: "$E[|Y|/e(X)] < \\infty$ is all the tower step uses",
        },
      }),
      patch_review: { key_results_ok: true, detail: "ok" },
    };
    expect((await runStageV1_5(h.args([review]))).status).toBe("patch");
    const directive = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(directive.findings).toEqual([
      expect.objectContaining({ id: "lem:ipw-identity", axis: "patch rejected", detail: expect.stringContaining("not minimal") }),
      expect.objectContaining({ id: "thm:ate-identification", axis: "clarify" }),
    ]);

    // with the patch rounds spent it fails, the patch recorded as unconfirmed
    const h2 = await harness();
    await withFixerPatch(h2);
    h2.state.verify!.patch_rounds = MIN_PATCH_BACKSTOP;
    expect((await runAtCapAndAccept(h2, [review])).status).toBe("failed");
    expect(paperFindings(h2.state).find((f) => f.node === "lem:ipw-identity")?.patch?.confirmed).toBe(false);
  });


  it("verdicts carry: an unchanged core costs no referee call; a changed patch re-grades only what rests on it", async () => {
    const h = await harness();
    await withFixerPatch(h);
    const pass: V15Review = {
      verdict: "PASS",
      summary: "ok",
      nodes: [...fullNodes()],
      patch_review: { key_results_ok: true, detail: "ok" },
    };
    expect((await runStageV1_5(h.args([pass]))).status).toBe("completed");
    const all = [...CORE_IDS];
    expect(Object.keys(h.state.verify!.confirmed ?? {}).sort()).toEqual([...all].sort());
    expect((await readReview(h.runDir)).nodes.every((n) => n.graded === "fresh" && typeof n.basis === "string")).toBe(true);

    // the same core again (a V1 re-entry that changed nothing): every verdict carried, no call
    const firstPass = h.calls.length;
    expect((await runStageV1_5(h.args([pass]))).status).toBe("completed");
    expect(h.calls).toHaveLength(firstPass);
    const carried = await readReview(h.runDir);
    expect(carried.nodes.map((n) => n.graded)).toEqual(all.map(() => "carried"));
    expect(carried.patch_review?.key_results_ok).toBe(true);

    // the patch changes: the patched lemma and the theorem resting on it are graded afresh — and
    // only they; a fresh `unclear` on the patched lemma counts (it is never served from the cache)
    const file = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.patches), "utf8"));
    file.patches[0].proof_note = "a different amended argument";
    await writeFile(path.join(h.runDir, VERIFY_FILES.patches), JSON.stringify(file), "utf8");
    const noisy: V15Review = {
      ...pass,
      nodes: [...fullNodes({ "lem:ipw-identity": { correctness: "unclear", detail: "could not follow" } })],
    };
    const third = await runStageV1_5(h.args([noisy]));
    expect(third.status).toBe("patch");
    const regraded = shardCalls(h.calls.slice(firstPass)).flatMap((c) => shardIds(c.prompt));
    expect(regraded.sort()).toEqual(["lem:ipw-identity", "thm:ate-identification"]);
    const saved = await readReview(h.runDir);
    const graded = Object.fromEntries(saved.nodes.map((n) => [n.id, n.graded]));
    expect(graded).toMatchObject({ "lem:ipw-identity": "fresh", "thm:ate-identification": "fresh", "ass:overlap": "carried" });
    expect(saved.nodes.find((n) => n.id === "lem:ipw-identity")!.correctness).toBe("unclear");
    expect(h.state.verify!.confirmed?.["lem:ipw-identity"]).toBeUndefined();
  });

  it("a cache recorded under another basis scheme (but 4, carried over: basis_scheme5.test.ts) is dropped: every node is graded afresh, and the log says why", async () => {
    const h = await harness();
    const pass: V15Review = { verdict: "PASS", summary: "ok", nodes: fullNodes() };
    expect((await runStageV1_5(h.args([pass]))).status).toBe("completed");
    h.state.verify!.confirmed_scheme = 3;
    h.state.stage_completed = "V1";
    const before = h.calls.length;
    const logs: string[] = [];
    expect((await runStageV1_5({ ...h.args([pass]), log: (m) => logs.push(m) })).status).toBe("completed");
    expect(logs).toContain(`verdict bases: the cache was recorded under basis scheme 3, not ${BASIS_SCHEME}: every node is graded afresh`);
    expect(shardCalls(h.calls.slice(before)).flatMap((c) => shardIds(c.prompt)).sort()).toEqual([...CORE_IDS].sort());
    expect((await readReview(h.runDir)).nodes.every((n) => n.graded === "fresh")).toBe(true);
    expect(h.state.verify!.confirmed_scheme).toBe(BASIS_SCHEME);
  });

  it("a cited result with no checkable source stops V1.5 for the user — the paper's own quote never counts", async () => {
    const h = await harness();
    await rm(path.join(h.runDir, "discovery", "cited_sources"), { recursive: true });
    const result = await runStageV1_5(h.args([]));
    expect(result.status).toBe("checkpoint");
    expect(result.message).toContain("discovery/cited_sources/vandervaart1998.txt");
    expect(h.calls).toHaveLength(0); // no referee call on an unchecked citation
  });

  it("a cited work declared inaccessible lets the run continue: taken as printed, NOT checked, and said so", async () => {
    const h = await harness();
    const dir = path.join(h.runDir, "discovery", "cited_sources");
    await rm(path.join(dir, "vandervaart1998.txt"));
    await writeFile(path.join(dir, "vandervaart1998.unavailable"), "library copy only; no scan online\n", "utf8");
    const review: V15Review = {
      verdict: "PASS",
      summary: "citation not checkable",
      nodes: fullNodes({ "lem:delta-method": { correctness: "unclear", detail: "the cited work is not shown" } }),
    };
    const result = await runStageV1_5(h.args([review]));
    expect(result.status).toBe("completed");
    const prompts = shardCalls(h.calls).map((c) => c.prompt).join("\n");
    expect(prompts).toContain("SOURCE UNAVAILABLE: library copy only; no scan online");
    const leaf = (await readReview(h.runDir)).nodes.find((n) => n.id === "lem:delta-method")!;
    expect(leaf.correctness).toBe("ok");
    expect(leaf.detail).toMatch(/^\[cited source unavailable — not checked against the cited work\]/);
    const notes = h.state.verify!.findings.filter((f) => f.node === "lem:delta-method").map((f) => f.detail);
    expect(notes.some((d) => d.startsWith("cited source NOT checked: ") && d.includes("library copy only"))).toBe(true);
  });

  it("a refutation of the quoted statement stands even when its source is unavailable", async () => {
    const h = await harness();
    const dir = path.join(h.runDir, "discovery", "cited_sources");
    await rm(path.join(dir, "vandervaart1998.txt"));
    await writeFile(path.join(dir, "vandervaart1998.unavailable"), "not online", "utf8");
    const review: V15Review = {
      verdict: "FAIL",
      summary: "the quoted statement is false",
      nodes: fullNodes({ "lem:delta-method": { correctness: "error", detail: "false as printed", witness: "phi not differentiable at theta", witness_regime: "in_scope", witness_instance: "phi(x)=|x|, theta=0" } }),
    };
    await runStageV1_5(h.args([review, review, review]));
    expect((await readReview(h.runDir)).nodes.find((n) => n.id === "lem:delta-method")!.correctness).toBe("error");
  });

  it("an empty inaccessibility declaration does not count: V1.5 still asks for the source", async () => {
    const h = await harness();
    const dir = path.join(h.runDir, "discovery", "cited_sources");
    await rm(path.join(dir, "vandervaart1998.txt"));
    await writeFile(path.join(dir, "vandervaart1998.unavailable"), "  \n", "utf8");
    const result = await runStageV1_5(h.args([]));
    expect(result.status).toBe("checkpoint");
    expect(result.message).toContain("vandervaart1998.unavailable is empty");
    expect(h.calls).toHaveLength(0);
  });

  it("a cited result the referee cannot find in its source goes back to the user, not the fixer", async () => {
    const h = await harness();
    const review: V15Review = {
      verdict: "PASS",
      summary: "citation not found",
      nodes: fullNodes({ "lem:delta-method": { correctness: "unclear", detail: "the source shown does not contain the delta method" } }),
    };
    const result = await runStageV1_5(h.args([review]));
    expect(result.status).toBe("checkpoint");
    expect(result.message).toContain("could not check 1 cited result");
  });
});

// ---------------------------------------------------------------------------------------------
// Cap accounting (user decisions 2026-09-23): error rounds vs refinement rounds; caps halt.
// ---------------------------------------------------------------------------------------------

describe("runStageV1_5 — error rounds, refinement rounds, caps", () => {
  const paperError = { detail: "the identity needs overlap bounded away from zero.", witness: "Take $e(X) \\to 0$: $E[DY/e(X)]$ diverges." };

  async function patched(h: Harness): Promise<void> {
    h.state.verify!.paper_errors = { "lem:ipw-identity": paperError };
    await writeFile(path.join(h.runDir, VERIFY_FILES.coreTranscribed), await readFile(h.corePath, "utf8"), "utf8");
    await writeFile(
      path.join(h.runDir, VERIFY_FILES.patches),
      JSON.stringify({
        key_results: ["thm:ate-identification"],
        key_contribution: "identification of the ATE by inverse weighting",
        patches: [
          {
            node: "lem:ipw-identity",
            corrected_statement: "\\(E[DY/e(X)] = E[Y(1)]\\) whenever \\(e(X) \\ge \\eta > 0\\) a.s.",
            proof_note: "bound DY/e(X) by |Y|/η before the tower property",
          },
        ],
        unfixable: [],
      }),
      "utf8",
    );
  }

  const nonMinimal: Partial<V15Review["nodes"][number]> = {
    correctness: "error",
    detail: "sufficient but not minimal: the tower step only needs integrability of the weight.",
    witness: "$E[|Y|/e(X)] < \\infty$ is a strictly weaker sufficient replacement.",
    minimality: true,
  };
  const minimalityOnly: V15Review = {
    verdict: "FAIL",
    summary: "the repair holds; its hypothesis is stronger than needed.",
    nodes: fullNodes({ "lem:ipw-identity": nonMinimal }),
    patch_review: { key_results_ok: true, detail: "ok" },
  };

  it("a minimality-only round is a REFINEMENT round (its own counter), even with the error rounds spent", async () => {
    const h = await harness();
    await patched(h);
    h.state.verify!.patch_rounds = MIN_PATCH_BACKSTOP; // error rounds spent: irrelevant to a refinement
    const result = await runStageV1_5(h.args([minimalityOnly]));
    expect(result).toMatchObject({ status: "patch", round_kind: "refinement" });
    const directive = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(directive).toMatchObject({ mode: "patch", round: 1 });
    expect(directive.findings).toEqual([expect.objectContaining({ id: "lem:ipw-identity", axis: "patch rejected", detail: expect.stringContaining("not minimal") })]);
    expect(directive.findings[0].minimality).toBeUndefined(); // routing metadata never reaches the fixer
    expect(h.state.verify!.cap_reached ?? null).toBeNull();
  });

  it("the refinement cap halts (never fails); --accept-cap keeps the repair as correct but non-minimal", async () => {
    const h = await harness();
    await patched(h);
    h.state.verify!.refinement_rounds = MAX_REFINEMENT_ROUNDS;
    const halted = await runStageV1_5(h.args([minimalityOnly]));
    expect(halted.status).toBe("checkpoint");
    expect(h.state.verify!.cap_reached).toMatchObject({
      counter: "refinement_rounds",
      rounds: MAX_REFINEMENT_ROUNDS,
      cap: MAX_REFINEMENT_ROUNDS,
      origin: "V1.5",
      findings: [expect.objectContaining({ id: "lem:ipw-identity" })],
      proposed: [expect.objectContaining({ node: "lem:ipw-identity", corrected_statement: expect.stringContaining("\\eta > 0") })],
    });
    expect(paperFindings(h.state)).toEqual([]); // nothing recorded until the orchestrator rules

    const accepted = await acceptV1_5AtCap(h.args([]));
    // the confirmed repair is ACCEPTED: hashed and handed to F1, so Lean certifies it
    expect(accepted.status).toBe("completed");
    expect(h.state.stage_completed).toBe("V1.5");
    expect(h.state.verify!.core_sha256).toBe(await sha256File(h.corePath));
    const found = paperFindings(h.state);
    // the paper's error is REPAIRED (confirmed); the minimality objection refutes nothing
    expect(found.find((f) => f.node === "lem:ipw-identity" && f.kind === "refuted")).toMatchObject({ patch: expect.objectContaining({ confirmed: true }) });
    expect(found.filter((f) => f.kind === "refuted")).toHaveLength(1);
  });

  it("accepting a refinement cap would lose nothing (else it is refused before anything changes): every error has its entry; an accepted repair is no suggestion only; a clarification needs none", async () => {
    const h = await harness();
    await patched(h);
    const transcribed = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.coreTranscribed), "utf8"));
    const file = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.patches), "utf8"));
    const ledger = h.state.verify!.paper_errors!;
    expect(acceptCapLosses(transcribed, file, ledger)).toEqual([]);
    // the repair's entry gone, its error recorded: a loss
    const gone = { ...file, patches: file.patches.filter((p: { node: string }) => p.node !== "lem:ipw-identity") };
    expect(acceptCapLosses(transcribed, gone, ledger).join(" ")).toContain("lem:ipw-identity");
    // … but not for a clarification's entry
    expect(acceptCapLosses(transcribed, gone, { ...ledger, "lem:ipw-identity": { ...ledger["lem:ipw-identity"]!, kind: "clarification" } as never })).toEqual([]);
    // an accepted repair held as a suggestion only: a loss
    const accepted = { ...ledger, "lem:ipw-identity": { ...ledger["lem:ipw-identity"]!, owner_decision: "accepted" } as never };
    const asSuggestion = { ...gone, unfixable: [{ node: "lem:ipw-identity", reason: "r", suggested_repair: { corrected_statement: "x", proof_note: "p" } }] };
    expect(acceptCapLosses(transcribed, asSuggestion, accepted).join(" ")).toMatch(/the owner accepted the weakened repair of "lem:ipw-identity"/);
    // an accepted repair kept as a patch (its mark dropped by a revision) is no loss
    expect(acceptCapLosses(transcribed, file, accepted)).toEqual([]);
  });

  it("at the error cap, a minimality objection is never printed as a refuted result, and rejects no repair", async () => {
    const h = await harness();
    await patched(h);
    h.state.verify!.patch_rounds = MIN_PATCH_BACKSTOP;
    const review: V15Review = {
      ...minimalityOnly,
      nodes: fullNodes({ "lem:ipw-identity": nonMinimal, "lem:delta-method": { correctness: "error", detail: "the source needs Hadamard differentiability.", witness: "a Gateaux-only map fails." } }),
    };
    const result = await runAtCapAndAccept(h, [review]);
    expect(result.status).toBe("failed");
    expect(result.message).not.toContain("no tex_locator");
    expect(result.message).toContain("lem:delta-method (main.tex:33-35)");

    // a minimality objection rejects nothing: the lemma's repair stays confirmed
    expect(paperFindings(h.state).find((f) => f.node === "lem:ipw-identity" && f.kind === "refuted")?.patch?.confirmed).toBe(true);
  });

});

describe("runStageV1_5 — the referee rules on the fixer's rejections of F-stage findings", () => {
  const rejection = {
    node: "thm:ate-identification",
    axis: "correctness" as const,
    from_stage: "F2.5",
    finding: "[F2.5 reviewer] [statement-wrong] thm:ate-identification needs overlap, which the paper does not state.",
    witness: "[statement-wrong] thm:ate-identification needs overlap",
    reason: "Assumption 2 (overlap) is stated and the theorem uses it.",
    where_the_paper_grants_it: "main.tex:15-17, Assumption 2",
  };

  it("an UPHELD rejection is a note, is ruled out for repeats, and the core is accepted", async () => {
    const h = await harness();
    h.state.verify!.fixer_rejections = [rejection];
    const review: V15Review = { verdict: "PASS", summary: "ok", nodes: fullNodes(), rejection_verdicts: [{ node: rejection.node, upheld: true, detail: "Assumption 2 is in the theorem's hypotheses." }] };
    const result = await runStageV1_5(h.args([review]));
    expect(result.status).toBe("completed");
    expect(globalCalls(h.calls)[0]!.prompt).toContain("=== FIXER REJECTIONS");
    expect(h.state.verify!.fixer_rejections).toEqual([]);
    expect(h.state.verify!.rejected_rewinds).toEqual([expect.objectContaining({ node: rejection.node, axis: "correctness", by: "fixer+referee" })]);
    expect(paperFindings(h.state)).toContainEqual(expect.objectContaining({ node: rejection.node, stage: "F2.5", kind: "note", detail: expect.stringContaining("upheld the rejection") }));
    expect(h.state.verify!.paper_errors?.[rejection.node]).toBeUndefined();
  });

  it("an OVERRULED rejection joins the ledger and goes back to the fixer as a patch round it may not reject again", async () => {
    const h = await harness();
    h.state.verify!.fixer_rejections = [rejection];
    const review: V15Review = { verdict: "PASS", summary: "ok", nodes: fullNodes(), rejection_verdicts: [{ node: rejection.node, upheld: false, detail: "Assumption 2 bounds e(X) away from 1 only." }] };
    const result = await runStageV1_5(h.args([review]));
    expect(result).toMatchObject({ status: "patch", round_kind: "error" });
    const directive = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(directive.findings).toEqual([expect.objectContaining({ id: rejection.node, axis: "correctness", overruled: true, from_stage: "F2.5", detail: expect.stringContaining("OVERRULED") })]);
    expect(h.state.verify!.paper_errors?.[rejection.node]).toMatchObject({ detail: rejection.finding });
    expect(h.state.verify!.fixer_rejections).toEqual([]);
  });

});
