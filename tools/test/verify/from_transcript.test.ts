/**
 * `--resume --from-transcript`: a run reviewed, repaired and formalized under an older design
 * re-enters as if V1 had just completed — `core.json` is the transcription again, everything derived
 * from it is archived (never deleted) and cleared, owner rulings stay, and the next step is a fresh
 * V1.5. No model call: V1.5 is a stub that records what it was handed.
 */
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readFile, readdir, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it, vi } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { verifyRunDir } from "../../src/paths.js";
import type { runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState, loadState, saveState } from "../../src/state.js";
import type { StateJson } from "../../src/types.js";
import { sha256File } from "../../src/verify/core_hash.js";
import { parseVerifyArgsForTest } from "../../src/verify/cli.js";
import { PatchFileSchema } from "../../src/verify/patches.js";
import { runVerifyPipeline } from "../../src/verify/pipeline.js";
import { hashSourceTree } from "../../src/verify/source_bundle.js";
import { flattenTex } from "../../src/verify/tex_envs.js";
import { VERIFY_FILES, type VerifyStage } from "../../src/verify/types.js";
import { tk } from "../toolkit/helpers.js";

const QID = "old_design_paper";
const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

const MAIN_TEX = [
  "\\documentclass{article}",
  "\\begin{document}",
  "\\begin{assumption}\\label{ass:overlap} $0 < e(X) < 1$ almost surely. \\end{assumption}",
  "\\begin{theorem}\\label{thm:ate} Under Assumption \\ref{ass:overlap}, $\\tau = E[DY/e(X)]$. \\end{theorem}",
  "\\end{document}",
  "",
].join("\n");

/** The transcription V1 wrote. */
function transcript(): Core {
  return {
    qid: QID,
    symbols: [{ name: "Y", type: "random variable", role: "outcome" }],
    assumptions: [
      { id: "ass:overlap", kind: "support", condition: "$0 < e(X) < 1$ almost surely.", novel: { flag: true, justification: "Assumption 1" }, tex_locator: { file: "main.tex", from: 3, to: 3, env: "assumption", label: "ass:overlap" } },
    ],
    definitions: [],
    statements: [
      { id: "thm:ate-identification", kind: "theorem", statement: "Under Assumption \\ref{ass:overlap}, $\\tau = E[DY/e(X)]$.", depends_on: ["ass:overlap"], proof_tex: "Condition on $X$.", status: "to-prove", tex_locator: { file: "main.tex", from: 4, to: 4, env: "theorem", label: "thm:ate" } },
    ],
    target_estimand: "$\\tau = E[Y(1) - Y(0)]$",
    bibliography: [],
  } as unknown as Core;
}

/** The core the old design left: the transcription plus a patch hypothesis. */
function patchedCore(): Core {
  const c = transcript();
  return {
    ...c,
    assumptions: [...c.assumptions, { id: "ass:patch-bounded", kind: "regularity", condition: "$Y$ is bounded.", novel: { flag: true, justification: "patch" } }],
    statements: c.statements.map((s) => ({ ...s, statement: "Under Assumption \\ref{ass:overlap} and bounded $Y$, $\\tau = E[DY/e(X)]$.", depends_on: [...s.depends_on, "ass:patch-bounded"] })),
  } as unknown as Core;
}

// The owner's ruling on ass:overlap (its ledger stamp and ruled-out entry below), as the runner records it.
const OWNER_READING = {
  id: "ass:pin-owner-1",
  node: "ass:overlap",
  reading: "τ is the population average treatment effect",
  withdraws: [{ axis: "correctness" as const, stage: "V1.5", route: "weakening", detail: "d", at: "t" }],
};

/** Paths the reset must move into the archive, with a byte payload each. */
const ARCHIVED: Record<string, string> = {
  [`${VERIFY_FILES.coreJson}.prev`]: "{}",
  [`${VERIFY_FILES.patches}.prev`]: "{}",
  [VERIFY_FILES.v15Review]: JSON.stringify({ nodes: [] }),
  [VERIFY_FILES.v15RefereeMetrics]: "{}",
  [VERIFY_FILES.v15Symbols]: "[]",
  [VERIFY_FILES.v1ReviseDirective]: JSON.stringify({ mode: "patch", round: 2, findings: [] }),
  [VERIFY_FILES.v1PendingReply]: "{}",
  "formalization/plan.json": "{}",
  "proposals/voided/x/A.json": "{}",
  "reviews/reviews.jsonl": "{}\n",
  "graph.json": "{}",
  [VERIFY_FILES.reportJson]: "{}",
  [VERIFY_FILES.reportMd]: "# old report\n",
  "annotated/main.tex": "old",
};
/** V1's outputs and the run's other logs: they stay. */
const KEPT = [VERIFY_FILES.flatTex, VERIFY_FILES.envsJson, VERIFY_FILES.flatLineMap, "discovery/core_refs.json", "discovery/v1_scope.json", "discovery/v1_lint_warnings.json", VERIFY_FILES.coreTranscribed, "logs/agent_calls.log", "logs/v1_patch_mufsht52_round1.json", "pipeline.jsonl"];

async function seed(mutate?: (s: StateJson, runDir: string) => Promise<void> | void): Promise<{ repoRoot: string; runDir: string }> {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-fromtx-"));
  tmpDirs.push(repoRoot);
  const runDir = verifyRunDir(repoRoot, QID);
  const sourceDir = path.join(runDir, VERIFY_FILES.sourceDir);
  await mkdir(sourceDir, { recursive: true });
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  await writeFile(path.join(sourceDir, "main.tex"), MAIN_TEX, "utf8");
  const flat = await flattenTex(sourceDir, "main.tex");
  await writeFile(path.join(runDir, VERIFY_FILES.flatTex), flat.text, "utf8");
  for (const f of KEPT.filter((k) => k !== VERIFY_FILES.flatTex && k !== VERIFY_FILES.coreTranscribed)) {
    await mkdir(path.dirname(path.join(runDir, f)), { recursive: true });
    await writeFile(path.join(runDir, f), "{}", "utf8");
  }
  await writeFile(path.join(runDir, VERIFY_FILES.coreTranscribed), JSON.stringify(transcript(), null, 2), "utf8");
  await writeFile(path.join(runDir, VERIFY_FILES.coreJson), JSON.stringify(patchedCore(), null, 2), "utf8");
  await writeFile(
    path.join(runDir, VERIFY_FILES.patches),
    JSON.stringify(PatchFileSchema.parse({ key_results: ["thm:ate-identification"], key_contribution: "ATE", patches: [], unfixable: [], owner_readings: [OWNER_READING] }), null, 2),
    "utf8",
  );
  for (const [rel, text] of Object.entries(ARCHIVED)) {
    await mkdir(path.dirname(path.join(runDir, rel)), { recursive: true });
    await writeFile(path.join(runDir, rel), text, "utf8");
  }
  const state = createVerifyInitialState(QID, {
    phase: "formalization",
    source: { input: "/papers/old.tex", main_file: "main.tex", sha256: await hashSourceTree(sourceDir) },
    targets: null,
    core_sha256: "old-core",
    v1_rounds: 2,
    v1_5_rounds: 1,
    findings: [{ node: "thm:ate-identification", stage: "V1.5", kind: "refuted", detail: "d", witness: null, at: "t" }],
    report_path: path.join(runDir, "report.md"),
  });
  state.stage_completed = "5";
  state.design_decisions = { a: "b" };
  state.flags.missing_architecture = true;
  const v = state.verify!;
  v.transcribed_sha256 = await sha256File(path.join(runDir, VERIFY_FILES.coreTranscribed));
  v.confirmed = { "ass:overlap": "basis" };
  v.confirmed_symbols = { Y: "basis" };
  v.confirmed_scheme = 2;
  v.patch_rounds = 2;
  v.refinement_rounds = 1;
  v.paper_errors = {
    "thm:ate-identification": { detail: "needs bounded Y", witness: "w" },
    "ass:overlap": { detail: "withdrawn", witness: null, owner_decision: "finding rejected", decision_reason: OWNER_READING.reading, owner_overruled: true },
  } as never;
  v.rejected_rewinds = [
    { node: "ass:overlap", axis: "correctness", stage: "V1.5", route: "weakening", detail: "d", reason: OWNER_READING.reading, by: "owner", pin: "ass:pin-owner-1", at: "t" },
    { node: "thm:ate-identification", axis: "correctness", stage: "F2.5", route: "fix-source", detail: "d", reason: "paper grants it", by: "orchestrator", at: "t" },
  ];
  v.weakening_repair = { status: "accepted", items: [], at: "t" } as never;
  v.cap_reached = { counter: "patch_rounds", rounds: 2, cap: 2, origin: "V1.5", findings: [], proposed: [], at: "t" } as never;
  v.level_pause = { level: 1 } as never;
  v.restatement_rounds = ["k"];
  v.fixer_rejections = [{ node: "n" }] as never;
  v.voided_receipts = [{ kind: "cap_reached" }] as never;
  await mutate?.(state, runDir);
  await saveState(repoRoot, QID, state);
  return { repoRoot, runDir };
}

const noCodex = (async () => {
  throw new Error("no model call in these tests");
}) as unknown as typeof runCodex;

function pipelineArgs(repoRoot: string, v1_5: VerifyStage, extra: Record<string, unknown> = {}) {
  return {
    toolkit: tk(repoRoot),
    qid: QID,
    input: "/papers/old.tex",
    mainHint: null,
    targets: null,
    resume: true,
    fromStage: null,
    auto: true,
    dryRun: false,
    fromTranscript: true,
    deps: { runCodex: noCodex, annotate: (async () => ({ path: "", line: "(stub)", result: null, error: null })) as never },
    stages: { v1_5, v1: (async () => { throw new Error("V1 must not run"); }) as VerifyStage },
    runFormalization: (async () => { throw new Error("the F stages must not run"); }) as never,
    ...extra,
  };
}

async function logged(fn: () => Promise<unknown>): Promise<string[]> {
  const spy = vi.spyOn(console, "log").mockImplementation(() => {});
  try {
    await fn();
    return spy.mock.calls.map((c) => String(c[0]));
  } finally {
    spy.mockRestore();
  }
}

describe("--resume --from-transcript", () => {
  it("restores the transcript, archives what was derived from it, clears the state, and hands a fresh V1.5 the run", async () => {
    const { repoRoot, runDir } = await seed();
    const seen: Array<Record<string, unknown>> = [];
    const v1_5: VerifyStage = async ({ state }) => {
      const core = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
      seen.push({ phase: state.verify!.phase, stage: state.stage_completed, confirmed: state.verify!.confirmed, symbols: state.verify!.confirmed_symbols, core });
      return { status: "checkpoint", message: "stub" };
    };
    const lines = await logged(() => runVerifyPipeline(pipelineArgs(repoRoot, v1_5) as never));
    const summary = lines.find((l) => l.includes("--from-transcript:")) ?? "";
    expect(summary).toContain("restored from discovery/core.transcribed.json (1 statements, 2 assumptions");
    expect(summary).toContain("replaced 1 statements, 2 assumptions");
    expect(summary).toContain("transcript is the one V1.5 accepted");
    expect(summary).toContain("owner rulings kept: 1 pinned reading(s), 1 withdrawal(s), 1 withdrawn ledger entry");

    // The next step was a fresh V1.5 on the plain transcription (+ the owner's pin): nothing carried.
    expect(seen).toHaveLength(1);
    expect(seen[0]!.phase).toBe("v1");
    expect(seen[0]!.stage).toBe("V1");
    expect(seen[0]!.confirmed).toBeUndefined();
    expect(seen[0]!.symbols).toBeUndefined();
    const core = seen[0]!.core as Core;
    expect(core.statements.map((s) => s.statement)).toEqual(transcript().statements.map((s) => s.statement));
    expect(core.assumptions.map((a) => a.id).sort()).toEqual(["ass:overlap", "ass:pin-owner-1"]);

    // Archived, not deleted: every derived artefact sits under the archive with its path; V1's stay.
    const [stamp] = await readdir(path.join(runDir, "_archive"));
    expect(stamp).toMatch(/^from_transcript_/);
    const archive = path.join(runDir, "_archive", stamp!);
    for (const [rel, text] of Object.entries(ARCHIVED)) {
      expect(existsSync(path.join(runDir, rel)), rel).toBe(false);
      expect(await readFile(path.join(archive, rel), "utf8"), rel).toBe(text);
    }
    expect(JSON.parse(await readFile(path.join(archive, VERIFY_FILES.coreJson), "utf8"))).toEqual(patchedCore());
    expect(PatchFileSchema.parse(JSON.parse(await readFile(path.join(archive, VERIFY_FILES.patches), "utf8"))).key_results).toEqual(["thm:ate-identification"]);
    const archivedState = JSON.parse(await readFile(path.join(archive, "state.json"), "utf8")) as StateJson;
    expect(archivedState.stage_completed).toBe("5");
    expect(Object.keys(archivedState.verify!.paper_errors ?? {})).toHaveLength(2);
    for (const rel of KEPT) expect(existsSync(path.join(runDir, rel)), rel).toBe(true);
    expect(existsSync(path.join(runDir, "formalization"))).toBe(true);

    // The new patch file carries only the owner's pinned reading.
    const patches = PatchFileSchema.parse(JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.patches), "utf8")));
    expect(patches).toEqual(expect.objectContaining({ key_results: [], patches: [], unfixable: [], owner_readings: [OWNER_READING] }));

    // State: V1 complete, the old review's verdicts, receipts, counters and the F stages' records gone.
    const after = await loadState(repoRoot, QID);
    const v = after.verify!;
    expect(after.stage_completed).toBe("V1");
    expect(v.phase).toBe("v1");
    for (const k of ["confirmed", "confirmed_symbols", "confirmed_scheme", "fixer_rejections", "weakening_repair", "level_pause", "cap_reached", "cross_stage_rewind", "voided_receipts", "restatement_rounds"] as const) {
      expect(v[k], k).toBeUndefined();
    }
    expect(v.paper_errors).toEqual({ "ass:overlap": expect.objectContaining({ owner_decision: "finding rejected" }) });
    expect(v.rejected_rewinds?.map((r) => r.by)).toEqual(["owner"]);
    expect([v.patch_rounds, v.refinement_rounds, v.v1_5_rounds]).toEqual([0, 0, 0]);
    expect(v.findings).toEqual([]);
    expect([v.core_sha256, v.transcribed_sha256, v.report_path]).toEqual([null, null, null]);
    expect(v.v1_rounds).toBe(2);
    expect(after.design_decisions).toEqual({});
    expect(after.flags.missing_architecture).toBe(false);
  });

  it("refuses a run whose transcript cannot be vouched for, and touches nothing", async () => {
    const cases: Array<[string, (s: StateJson, runDir: string) => Promise<void> | void, RegExp]> = [
      ["no transcript", async (_s, d) => rm(path.join(d, VERIFY_FILES.coreTranscribed)), /no discovery\/core\.transcribed\.json on file/],
      ["V1 never completed", (s) => { s.stage_completed = "init"; s.verify!.phase = "init"; }, /V1 has not completed/],
      ["mid-V1 revise", async (s, d) => {
        s.stage_completed = "V1";
        s.verify!.phase = "init";
        await writeFile(path.join(d, VERIFY_FILES.v1ReviseDirective), JSON.stringify({ mode: "transcribe", round: 1, findings: [] }), "utf8");
      }, /the run is mid-V1/],
      ["source changed", async (_s, d) => writeFile(path.join(d, VERIFY_FILES.sourceDir, "main.tex"), `${MAIN_TEX}% edited\n`, "utf8"), /the source changed/],
      ["transcript edited after acceptance", async (_s, d) => writeFile(path.join(d, VERIFY_FILES.coreTranscribed), JSON.stringify(transcript()), "utf8"), /differs from the transcript V1\.5 accepted/],
      ["no hash, flat no longer matches", async (s, d) => {
        s.verify!.transcribed_sha256 = null;
        await writeFile(path.join(d, VERIFY_FILES.flatTex), "other text", "utf8");
      }, /no longer flattens/],
    ];
    for (const [name, mutate, re] of cases) {
      const { repoRoot, runDir } = await seed(mutate);
      const v1_5: VerifyStage = async () => { throw new Error("V1.5 must not run"); };
      await expect(runVerifyPipeline(pipelineArgs(repoRoot, v1_5) as never), name).rejects.toThrow(re);
      expect(existsSync(path.join(runDir, "_archive")), name).toBe(false);
      expect(JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.coreJson), "utf8")), name).toEqual(patchedCore());
      expect((await loadState(repoRoot, QID)).verify!.confirmed, name).toEqual({ "ass:overlap": "basis" });
    }
  });

  it("the parser and the runner refuse it without --resume, with --from-stage / --fresh-review, or with a halt's answer", async () => {
    const parse = parseVerifyArgsForTest;
    expect(parse(["paper.tex", "--resume", "--from-transcript"]).fromTranscript).toBe(true);
    expect(parse(["paper.tex"]).fromTranscript).toBe(false);
    expect(() => parse(["paper.tex", "--from-transcript"])).toThrow(/--from-transcript requires --resume/);
    expect(() => parse(["paper.tex", "--resume", "--from-transcript", "--from-stage", "V1.5"])).toThrow(/does not combine with --from-stage/);
    expect(() => parse(["paper.tex", "--resume", "--from-transcript", "--from-stage", "V1.5", "--fresh-review"])).toThrow(/does not combine/);
    expect(() => parse(["paper.tex", "--resume", "--from-transcript", "--accept-cap"])).toThrow(/clears every halt/);
    expect(() => parse(["paper.tex", "--stop", "--from-transcript"])).toThrow(/--stop combines only/);
    const { repoRoot } = await seed();
    const v1_5: VerifyStage = async () => { throw new Error("V1.5 must not run"); };
    await expect(runVerifyPipeline(pipelineArgs(repoRoot, v1_5, { resume: false }) as never)).rejects.toThrow(/needs --resume/);
    await expect(runVerifyPipeline(pipelineArgs(repoRoot, v1_5, { fromStage: "V1.5" }) as never)).rejects.toThrow(/does not combine with --from-stage/);
    await expect(runVerifyPipeline(pipelineArgs(repoRoot, v1_5, { acceptCap: true }) as never)).rejects.toThrow(/clears every halt/);
  });
});

describe("verify --resume by the slug alone", () => {
  it("parses with no paper (the runner reads the one the run was launched on); a cold start still needs one", () => {
    expect(parseVerifyArgsForTest(["--slug", "r1", "--resume"]).input).toBe("");
    expect(parseVerifyArgsForTest(["--slug", "r1", "--resume", "--accept-repair", "thm:a"]).input).toBe("");
    expect(() => parseVerifyArgsForTest(["--slug", "r1"])).toThrow(/Missing <paper/);
    expect(() => parseVerifyArgsForTest(["--resume"])).toThrow(/Missing <paper/);
  });
});
