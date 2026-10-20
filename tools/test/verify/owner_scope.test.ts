/**
 * The owner decides only for MAIN THEOREMS (user decision 2026-09-24): a weakening-only repair on an
 * intermediate result is applied automatically, confirmed by V1.5 and reported "narrowed"; only a
 * main theorem halts for the owner. Fixer and
 * referee faked; no network.
 */
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState } from "../../src/state.js";
import { PatchFileSchema, type PatchFile } from "../../src/verify/patches.js";
import { buildReport } from "../../src/verify/report.js";
import { runStageV1_5 } from "../../src/verify/stage_v1_5.js";
import { VERIFY_FILES, type V15NodeVerdict, type V15Review } from "../../src/verify/types.js";
import { mainTheoremIds } from "../../src/verify/weakening.js";
import { cannedCodex } from "./referee_fake.js";

const QID = "scope_paper";
const tmpDirs: string[] = [];
afterEach(async () => {
  for (const dir of tmpDirs.splice(0)) await rm(dir, { recursive: true, force: true });
});

const st = (id: string, kind: string, deps: string[] = []) => ({ id, kind, statement: `the claim of ${id}`, depends_on: deps, status: "to-prove" });

/** The CNS receipt's shape: two theorems (a theorem and its clause) resting on five lemmas. */
function core(): Core {
  return {
    qid: QID,
    symbols: [{ name: "\\sigma", type: "score standard deviation" }],
    assumptions: [{ id: "ass:moments", condition: "bounded moments", novel: { flag: true, justification: "Assumption 1" }, used_by: ["lem:global"] }],
    definitions: [],
    statements: [
      st("lem:global", "lemma", ["ass:moments"]),
      st("lem:rp-alt1", "lemma"),
      st("lem:rp-alt2", "lemma"),
      st("lem:cont-deriv", "lemma"),
      st("lem:bounded-rr-local-alt3", "lemma"),
      st("thm:local", "theorem", ["lem:global", "lem:rp-alt1", "lem:rp-alt2", "lem:cont-deriv", "lem:bounded-rr-local-alt3"]),
      st("thm:local-local-clause", "theorem", ["lem:global"]),
      st("prop:aside", "proposition"),
    ],
    target_estimand: "\\(\\theta\\)",
  } as unknown as Core;
}

const LEMMAS = ["lem:global", "lem:rp-alt1", "lem:rp-alt2", "lem:cont-deriv", "lem:bounded-rr-local-alt3"];
const THEOREMS = ["thm:local", "thm:local-local-clause"];
const suggestion = (node: string) => ({
  node,
  reason: `any repair weakens the contribution: ${node} fails as printed`,
  suggested_repair: { corrected_statement: `the weaker claim of ${node}`, add_assumptions: [], remove_depends_on: [], proof_note: "the same argument with the cross term kept.", given_up: `the full strength of ${node}` },
  suggested_by: "fixer" as const,
});

function file(over: Partial<PatchFile> = {}): PatchFile {
  return PatchFileSchema.parse({ key_results: [...THEOREMS], key_contribution: "local rates", patches: [], unfixable: [], ...over });
}

const fakeCodex = (replies: unknown[], calls: CodexRunInput[]): typeof runCodex => cannedCodex(replies, calls);

async function setup(opts: { repoRoot?: string; runDir?: string } = {}) {
  const repoRoot = opts.repoRoot ?? (await mkdtemp(path.join(os.tmpdir(), "verify-scope-")));
  if (!opts.repoRoot) tmpDirs.push(repoRoot);
  const runDir = opts.runDir ?? path.join(repoRoot, "runs", QID);
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  for (const f of [VERIFY_FILES.coreJson, VERIFY_FILES.coreTranscribed]) await writeFile(path.join(runDir, f), JSON.stringify(core(), null, 2), "utf8");
  await writeFile(path.join(runDir, VERIFY_FILES.flatTex), "\\begin{lemma}the claim\\end{lemma}\n", "utf8");
  const state = createVerifyInitialState(QID, {
    phase: "v1",
    source: { input: "paper.tex", main_file: "main.tex", sha256: "h" },
    targets: null,
    core_sha256: null,
    v1_rounds: 1,
    v1_5_rounds: 0,
    findings: [],
    report_path: null,
  });
  state.verify!.paper_errors = Object.fromEntries([...LEMMAS, ...THEOREMS].map((id) => [id, { detail: `${id} fails as printed`, witness: `a witness against ${id}` }]));
  const calls: CodexRunInput[] = [];
  const args = (replies: unknown[]) => ({ repoRoot, qid: QID, runDir, state, deps: { runCodex: fakeCodex(replies, calls) }, dryRun: false, log: (m: string) => lines.push(m) });
  const lines: string[] = [];
  const patches = async (): Promise<PatchFile> => PatchFileSchema.parse(JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.patches), "utf8")));
  const builtCore = async (): Promise<Core> => JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
  return { repoRoot, runDir, state, calls, args, lines, patches, builtCore };
}

function grade(id: string, over: Partial<V15NodeVerdict> = {}): V15NodeVerdict {
  return { id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "reproduced", witness: null, bookkeeping_assumption: null, reading: null, ...over };
}

async function review(runDir: string): Promise<V15Review> {
  const c = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
  const ids = [...c.statements, ...c.assumptions, ...c.definitions].map((n) => n.id);
  return { verdict: "PASS", summary: "s", nodes: ids.map((id) => grade(id)), patch_review: { key_results_ok: true, detail: "the theorems are the headline" } };
}

describe("main theorems", () => {
  it("are the core's theorem statements and the fixer's key results; lemmas, propositions and hypotheses are intermediate", () => {
    const mains = mainTheoremIds(core(), file({ key_results: ["thm:local", "lem:rp-alt1"] }));
    expect([...mains].sort()).toEqual(["lem:rp-alt1", "thm:local", "thm:local-local-clause"]);
    for (const id of ["lem:global", "prop:aside", "ass:moments"]) expect(mains.has(id)).toBe(false);
  });
});

describe("a pending suggestion on an intermediate result at a V1.5 entry", () => {
  it("is applied, confirmed in the same pass, and reported as a narrowed intermediate result (no halt)", async () => {
    const r = await setup();
    r.state.verify!.paper_errors = { "prop:aside": { detail: "prop:aside fails as printed", witness: "x = 1" } };
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(file({ unfixable: [suggestion("prop:aside")] })), "utf8");
    const result = await runStageV1_5(r.args([await review(r.runDir)]));
    expect(result.status).toBe("completed");
    expect(r.state.verify!.weakening_repair ?? null).toBeNull();
    expect(r.lines.some((l) => l.startsWith("prop:aside is an intermediate result: its strongest true version is applied automatically (narrowed: the full strength of prop:aside)"))).toBe(true);
    expect((await r.builtCore()).statements.find((s) => s.id === "prop:aside")!.statement).toBe("the weaker claim of prop:aside");
    const f = r.state.verify!.findings.find((x) => x.node === "prop:aside")!;
    expect(f).toMatchObject({ kind: "refuted", patch: { confirmed: true, narrowed: "the full strength of prop:aside", narrowed_by: "runner" } });
    const { md } = buildReport({
      qid: QID,
      envs: { main_file: "main.tex", files: [], envs: [] } as never,
      scope: [],
      core: await r.builtCore(),
      review: null,
      findings: r.state.verify!.findings,
      addedAssumptions: [],
      crosswalk: null,
      graph: null,
      lean: null,
      warnings: { lint: [], parser: [] },
      flags: {},
      stageCompleted: "V1.5",
      earlyStop: true,
      sourceSha256: "h",
      inputs: { v1_5_review: "", crosswalk_full: "", graph_json: "", v1_scope: "", lean_evidence: "" },
    } as never);
    expect(md).toContain("narrowed: the full strength of prop:aside");
    expect(md).not.toContain("the owner accepted the weaker version");
  });

  it("on a main theorem it still halts for the owner, and the receipt lists only the theorems", async () => {
    const r = await setup();
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(file({ unfixable: [...LEMMAS, ...THEOREMS].map(suggestion) })), "utf8");
    const result = await runStageV1_5(r.args([]));
    expect(result.status).toBe("checkpoint");
    expect(result.message).toContain("weaken a main theorem");
    expect(r.state.verify!.weakening_repair!.items.map((i) => i.node)).toEqual(THEOREMS);
    expect((await r.patches()).patches.map((p) => p.node)).toEqual(LEMMAS);
    expect(r.calls).toHaveLength(0); // nothing reviewed until the owner rules
  });
});
