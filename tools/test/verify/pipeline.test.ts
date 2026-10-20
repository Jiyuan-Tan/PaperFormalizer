import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it, vi } from "vitest";
import { planPath, statePath, verifyRunDir } from "../../src/paths.js";
import { tk } from "../toolkit/helpers.js";
import { loadState, saveState } from "../../src/state.js";
import type { Stage, StateJson } from "../../src/types.js";
import {
  runVerifyPipeline,
  type RunFormalization,
} from "../../src/verify/pipeline.js";
import type { AnnotateRun } from "../../src/verify/annotate_run.js";
import {
  MIN_PATCH_BACKSTOP,
  type PrepareSource,
  type VerifyStage,
  type VerifyStageArgs,
  type VerifyStageResult,
} from "../../src/verify/types.js";

const QID = "sample_paper";

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const dir of tmpDirs.splice(0)) await rm(dir, { recursive: true, force: true });
});

async function tmpRepo(): Promise<string> {
  const dir = await mkdtemp(path.join(os.tmpdir(), "verify-pipeline-"));
  tmpDirs.push(dir);
  return dir;
}

/** Records the phase each stage saw, so the test asserts the ORDER of the machine. */
interface Trace {
  stages: string[];
  formalization: Array<Stage | undefined>;
  stopAfter: Array<Stage | undefined>;
}

function fakePrepareSource(): PrepareSource {
  return async ({ sourceDir }) => {
    await mkdir(sourceDir, { recursive: true });
    return { sourceDir, mainFile: "main.tex", sha256: "abc123", inputKind: "tex" };
  };
}

function fakeStage(
  label: string,
  trace: Trace,
  status: VerifyStageResult["status"] = "completed",
  mutate?: (state: StateJson) => void,
): VerifyStage {
  return async ({ state }) => {
    trace.stages.push(`${label}@${state.verify!.phase}`);
    mutate?.(state);
    return { status, message: `fake ${label}` };
  };
}

/** Stand-in for the F1–F5 runner: persists a terminal `stage_completed` like the real one. */
function fakeFormalization(trace: Trace, finalStage: Stage): RunFormalization {
  return async ({ toolkit, qid, startStage, stopAfterStage }) => {
    const repoRoot = toolkit.toolkitRoot;
    trace.formalization.push(startStage);
    trace.stopAfter.push(stopAfterStage);
    const state = await loadState(repoRoot, qid);
    state.stage_completed = finalStage;
    await saveState(repoRoot, qid, state);
    return state;
  };
}

function baseArgs(repoRoot: string, trace: Trace) {
  return {
    toolkit: tk(repoRoot),
    qid: QID,
    input: "/papers/sample_paper.tex",
    mainHint: null,
    targets: ["thm:main"],
    resume: false,
    fromStage: null as string | null,
    auto: false,
    dryRun: true,
    deps: { prepareSource: fakePrepareSource() },
    stages: {
      v1: fakeStage("V1", trace),
      v1_5: fakeStage("V1.5", trace),
      v6: fakeStage("V6", trace),
    },
    runFormalization: fakeFormalization(trace, "5"),
    runPromotion: async () => ({ status: "empty" as const, batch_path: null, checklist_path: null, promoted: [] }),
  };
}

function newTrace(): Trace {
  return { stages: [], formalization: [], stopAfter: [] };
}

describe("runVerifyPipeline", () => {
  it("--from-stage V6 writes the report again and keeps an applied promotion round", async () => {
    const repoRoot = await tmpRepo();
    const done = await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), runFormalization: fakeFormalization(newTrace(), "5") });
    expect(done.phase).toBe("done");
    const s = await loadState(repoRoot, QID);
    s.verify!.promotion = { status: "applied", batch_path: null, checklist_path: null, promoted: ["Toolkit.x"] };
    await saveState(repoRoot, QID, s);
    let proposed = 0;
    const runPromotion = async () => { proposed += 1; return { status: "empty" as const, batch_path: null, checklist_path: null, promoted: [] }; };
    const trace = newTrace();
    // Rebuilding a report does not answer a question the agent left on the page.
    const asked = path.join(verifyRunDir(repoRoot, QID), "orch_requests.json");
    await writeFile(asked, JSON.stringify([{ id: "q1", at: "x", text: "which account?" }]));
    const again = await runVerifyPipeline({ ...baseArgs(repoRoot, trace), resume: true, fromStage: "V6", runPromotion });
    expect(existsSync(asked)).toBe(true);
    expect(trace.stages.some((x) => x.startsWith("V6"))).toBe(true);
    expect(proposed).toBe(0);
    expect(again.promotion).toMatchObject({ status: "applied", promoted: ["Toolkit.x"] });
    expect(again.phase).toBe("done");
  });

  it.each([null, "V1", "V1.5"])("preserves outstanding page requests when resuming from %s", async (fromStage) => {
    const repoRoot = await tmpRepo();
    await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), stopAfter: "V1" });
    const asked = path.join(verifyRunDir(repoRoot, QID), "orch_requests.json");
    const requests = JSON.stringify([
      { id: "q1", at: "x", text: "Please supply the cited source." },
      { id: "q2", at: "y", text: "Which reading did you intend?" },
    ]);
    await writeFile(asked, requests);
    const trace = newTrace();
    const args = baseArgs(repoRoot, trace);
    args.stages.v1_5 = fakeStage("V1.5", trace, "checkpoint");
    await runVerifyPipeline({ ...args, resume: true, fromStage });
    expect(trace.stages).toContain("V1.5@v1");
    expect(await readFile(asked, "utf8")).toBe(requests);
  });

  it("a promotion round already held is not held again when the run is re-entered at V1.5 or F1", async () => {
    const repoRoot = await tmpRepo();
    await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), runFormalization: fakeFormalization(newTrace(), "5") });
    const s = await loadState(repoRoot, QID);
    s.verify!.promotion = { status: "applied", batch_path: null, checklist_path: null, promoted: ["Toolkit.x"] };
    s.verify!.promotion_a = { status: "deferred", batch_path: null, checklist_path: null, promoted: [] };
    await saveState(repoRoot, QID, s);
    const never = async (): Promise<never> => { throw new Error("the round is held again"); };
    for (const fromStage of ["V1.5", "F1"]) {
      const out = await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), resume: true, fromStage, runFormalization: fakeFormalization(newTrace(), "5"), runPromotion: never, runPromotionA: never });
      expect(out.promotion).toMatchObject({ status: "applied", promoted: ["Toolkit.x"] });
      expect(out.promotion_a?.status).toBe("deferred");
      expect(out.phase).toBe("done");
    }
  });

  it("--from-stage V1 with --targets re-scopes the transcription; a resume keeps the scope on record", async () => {
    const repoRoot = await tmpRepo();
    await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), runFormalization: fakeFormalization(newTrace(), "5") });
    expect((await loadState(repoRoot, QID)).verify!.targets).toEqual(["thm:main"]);
    await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), fromStage: "V1", targets: ["thm:other"], runFormalization: fakeFormalization(newTrace(), "5") });
    expect((await loadState(repoRoot, QID)).verify!.targets).toEqual(["thm:other"]);
    await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), resume: true, fromStage: "V6", targets: ["thm:main"], runFormalization: fakeFormalization(newTrace(), "5") });
    expect((await loadState(repoRoot, QID)).verify!.targets).toEqual(["thm:other"]);
  });

  it("a cold --from-stage V1 sets the review items and reported issues aside with the patch file: they name the old transcription", async () => {
    const repoRoot = await tmpRepo();
    await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), runFormalization: fakeFormalization(newTrace(), "5") });
    const runDir = verifyRunDir(repoRoot, QID);
    const files = ["discovery/patches.json", "orch_decisions.json", "owner_objections.json"].map((f) => path.join(runDir, f));
    await writeFile(files[0]!, JSON.stringify({ patches: [], unfixable: [] }));
    await writeFile(files[1]!, JSON.stringify([{ id: "d1", node: "thm:main", text: "withdrew the finding" }]));
    await writeFile(files[2]!, JSON.stringify([{ id: "obj-1", comment: "c3", text: "this note is wrong" }]));
    await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), fromStage: "V1", runFormalization: fakeFormalization(newTrace(), "5") });
    for (const f of files) {
      expect(existsSync(f), f).toBe(false);
      expect(existsSync(`${f}.prev`), f).toBe(true);
    }
    expect(JSON.parse(await readFile(`${files[1]}.prev`, "utf8"))[0].id).toBe("d1");
  });

  it("a live run records the CLI that runs its claude roles; a resume keeps it, an explicit setting rewrites it; a dry run records none", async () => {
    const { setClaudeRolesForTest } = await import("../../src/claude_roles.js");
    const log = vi.spyOn(console, "log").mockImplementation(() => {});
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    try {
      const dry = await tmpRepo();
      await runVerifyPipeline(baseArgs(dry, newTrace()));
      expect((await loadState(dry, QID)).claude_roles).toBeUndefined();

      const repoRoot = await tmpRepo();
      // the first process of the run found no usable claude
      setClaudeRolesForTest({ runner: "codex", explicit: false, reason: "its CLI is not installed" });
      await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), dryRun: false, stopAfter: "V1" });
      expect((await loadState(repoRoot, QID)).claude_roles).toBe("codex");
      // a later process with no setting: the record, whatever the machine now has
      setClaudeRolesForTest(null);
      vi.stubEnv("THEOREMCHECKER_CLAUDE_ROLES", "");
      await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), dryRun: false, resume: true, stopAfter: "V1.5" });
      expect((await loadState(repoRoot, QID)).claude_roles).toBe("codex");
      expect(warn.mock.calls.flat().join("\n")).toMatch(/run on codex \(\S+\), as recorded for this run/);
      expect(warn.mock.calls.flat().join("\n")).not.toContain("WARN");
      // a later process with an explicit setting: it wins, warns once, and is the new record
      setClaudeRolesForTest(null);
      vi.stubEnv("THEOREMCHECKER_CLAUDE_ROLES", "claude");
      await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), dryRun: false, resume: true, stopAfter: "V1.5" });
      expect((await loadState(repoRoot, QID)).claude_roles).toBe("claude");
      expect(warn.mock.calls.flat().filter((l) => String(l).includes("WARN"))).toEqual(["[theoremchecker] WARN this run's claude roles ran on codex so far: from now on they run on claude (set by THEOREMCHECKER_CLAUDE_ROLES)."]);
    } finally {
      vi.unstubAllEnvs();
      setClaudeRolesForTest(null);
      log.mockRestore();
      warn.mockRestore();
    }
  });

  it("a dry run marks its state; a live resume refuses it, a live --from-stage V1 takes it over", async () => {
    const repoRoot = await tmpRepo();
    await runVerifyPipeline(baseArgs(repoRoot, newTrace()));
    expect((await loadState(repoRoot, QID)).verify!.dry_run).toBe(true);
    // A live resume (and a live re-entry past V1) is refused before any stage runs.
    for (const extra of [{ resume: true }, { fromStage: "V1.5" }, { fromStage: "F2" }]) {
      const trace = newTrace();
      await expect(runVerifyPipeline({ ...baseArgs(repoRoot, trace), dryRun: false, ...extra }))
        .rejects.toThrow(/seeded or advanced by --dry-run[\s\S]*--from-stage V1[\s\S]*fresh --slug/);
      expect(trace.stages).toEqual([]);
      expect(trace.formalization).toEqual([]);
    }
    expect((await loadState(repoRoot, QID)).verify!.dry_run).toBe(true);
    // A live re-extraction replaces the dry record.
    const trace = newTrace();
    await runVerifyPipeline({ ...baseArgs(repoRoot, trace), dryRun: false, fromStage: "V1" });
    expect(trace.stages[0]).toBe("V1@init");
    expect((await loadState(repoRoot, QID)).verify!.dry_run).toBeUndefined();
  });

  it("never downgrades a live state: --dry-run --resume / --from-stage on a live run is refused", async () => {
    const repoRoot = await tmpRepo();
    await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), dryRun: false, stopAfter: "V1" });
    const before = await loadState(repoRoot, QID);
    expect(before.verify!.dry_run).toBeUndefined();
    for (const extra of [{ resume: true }, { fromStage: "V1" }, { fromStage: "F1" }]) {
      const trace = newTrace();
      await expect(runVerifyPipeline({ ...baseArgs(repoRoot, trace), dryRun: true, ...extra }))
        .rejects.toThrow(/is a live run; --dry-run never continues/);
      expect(trace.stages).toEqual([]);
    }
    const after = await loadState(repoRoot, QID);
    expect(after.verify).toEqual(before.verify);
    expect(after.stage_completed).toBe(before.stage_completed);
  });

  it("the toolkit promotion round follows the report; a finished run without one enters it on --resume, V6 not re-run", async () => {
    const repoRoot = await tmpRepo();
    const trace = newTrace();
    const verify = await runVerifyPipeline(baseArgs(repoRoot, trace));
    expect(verify).toMatchObject({ phase: "done", promotion: { status: "empty" } });
    // A run finished before the round existed: no record.
    const st = await loadState(repoRoot, QID);
    delete st.verify!.promotion;
    await saveState(repoRoot, QID, st);
    const pending = { status: "pending_user" as const, batch_path: null, checklist_path: "/x.B.md", promoted: [] };
    const resumed = await runVerifyPipeline({ ...baseArgs(repoRoot, trace), resume: true, runPromotion: async () => pending });
    expect(resumed).toMatchObject({ phase: "proposals_B", promotion: pending });
    expect(trace.stages.filter((s) => s.startsWith("V6"))).toHaveLength(1);
  });

  it("cold-starts: builds the layout, seeds state, and walks init→v1→v1_5→F→v6→done", async () => {
    const repoRoot = await tmpRepo();
    const trace = newTrace();
    const verify = await runVerifyPipeline(baseArgs(repoRoot, trace));

    const runDir = verifyRunDir(repoRoot, QID);
    expect(runDir).toBe(path.join(repoRoot, "runs", QID));
    for (const sub of ["discovery", "formalization", "logs", "source"]) {
      expect(existsSync(path.join(runDir, sub))).toBe(true);
    }
    expect(existsSync(statePath(repoRoot, QID))).toBe(true);

    expect(trace.stages).toEqual(["V1@init", "V1.5@v1", "V6@v6"]);
    // First entry into the F runner starts at F1.
    expect(trace.formalization).toEqual(["1"]);
    expect(verify.phase).toBe("done");

    const persisted = await loadState(repoRoot, QID);
    expect(persisted.lean_subdir).toBe("Papers/SamplePaper");
    // The report after a full F run closes the cursor.
    expect(persisted.stage_completed).toBe("V6");
    expect(persisted.verify).toMatchObject({
      phase: "done",
      targets: ["thm:main"],
      source: { input: "/papers/sample_paper.tex", main_file: "main.tex", sha256: "abc123" },
      core_sha256: null,
      v1_rounds: 0,
      findings: [],
    });
  });

  it("routes a failed V1.5 to V6 and ends in `failed`, never entering the F stages", async () => {
    const repoRoot = await tmpRepo();
    const trace = newTrace();
    const args = baseArgs(repoRoot, trace);
    args.stages.v1_5 = fakeStage("V1.5", trace, "failed", (state) => {
      state.verify!.findings.push({
        node: "thm:main",
        stage: "V1.5",
        kind: "refuted",
        detail: "step 3 is false",
        witness: "counterexample",
        at: new Date().toISOString(),
      });
    });
    const verify = await runVerifyPipeline(args);

    expect(trace.stages).toEqual(["V1@init", "V1.5@v1", "V6@v6"]);
    expect(trace.formalization).toEqual([]);
    expect(verify.phase).toBe("failed");
    expect(verify.findings).toHaveLength(1);
    // the log says what each V pass ended in: a refutation at V1.5 (a failed V1 is a failed transcription, not one)
    const events = (await readFile(path.join(verifyRunDir(args.toolkit.toolkitRoot, QID), "pipeline.jsonl"), "utf8")).trim().split("\n").map((l) => JSON.parse(l));
    expect(events.map((e) => `${e.stage} ${e.status}`)).toEqual(["V1 completed", "V1.5 refuted", "V6 completed"]);
    const failedV1 = baseArgs(await tmpRepo(), newTrace());
    failedV1.stages.v1 = fakeStage("V1", newTrace(), "failed");
    await runVerifyPipeline(failedV1);
    expect(JSON.parse((await readFile(path.join(verifyRunDir(failedV1.toolkit.toolkitRoot, QID), "pipeline.jsonl"), "utf8")).split("\n")[0]!)).toMatchObject({ stage: "V1", status: "transcription-failed" });
  });

  it("--stop-after V1 halts after extraction; --resume then continues; an F value is forwarded", async () => {
    const repoRoot = await tmpRepo();
    const trace = newTrace();
    const halted = await runVerifyPipeline({ ...baseArgs(repoRoot, trace), stopAfter: "V1" });
    expect(trace.stages).toEqual(["V1@init"]);
    expect(halted.phase).toBe("v1");

    const second = newTrace();
    const again = await runVerifyPipeline({
      ...baseArgs(repoRoot, second),
      resume: true,
      stopAfter: "F1.5",
      // Round A (after F1) is not what this test is about.
      deferProposals: true,
      runFormalization: fakeFormalization(second, "1.5"),
    });
    expect(second.stages).toEqual(["V1.5@v1"]);
    expect(second.stopAfter).toEqual(["1.5"]);
    expect(again.phase).toBe("formalization");
    const persisted = await loadState(repoRoot, QID);
    expect(persisted.stage_completed).toBe("1.5");

    // a resume that starts past V1.5 under --stop-after V1.5 never enters the F stages
    const held = newTrace();
    await runVerifyPipeline({ ...baseArgs(repoRoot, held), resume: true, stopAfter: "V1.5", runFormalization: fakeFormalization(held, "5") });
    expect(held.stages).toEqual([]);
    expect(held.formalization).toEqual([]);

    const third = newTrace();
    const done = await runVerifyPipeline({
      ...baseArgs(repoRoot, third),
      resume: true,
      stopAfter: "F5",
      runFormalization: fakeFormalization(third, "5"),
    });
    expect(third.stages).toEqual([]);
    expect(done.phase).toBe("v6");
  });

  it("--stop-after V6 halts once the report is written, before promotion round B; --resume holds the round. THEOREMCHECKER_STOP_AFTER=F5 is --stop-after F5", async () => {
    const repoRoot = await tmpRepo();
    const trace = newTrace();
    let rounds = 0;
    const args = { ...baseArgs(repoRoot, trace), runPromotion: async () => { rounds += 1; return { status: "empty" as const, batch_path: null, checklist_path: null, promoted: [] }; } };
    const halted = await runVerifyPipeline({ ...args, stopAfter: "V6" });
    expect(halted.phase).toBe("proposals_B");
    expect(trace.stages.at(-1)).toBe("V6@v6");
    expect(rounds).toBe(0);
    // a resume that still says --stop-after V6 stays before the round
    await runVerifyPipeline({ ...args, resume: true, stopAfter: "V6" });
    expect(rounds).toBe(0);
    await runVerifyPipeline({ ...args, resume: true });
    expect(rounds).toBe(1);
    // the round applied: writing the report again with --stop-after V6 is not "before round B" — the run ends done
    const st = await loadState(repoRoot, QID);
    st.verify!.promotion = { status: "applied", batch_path: null, checklist_path: null, promoted: [], applied_at: "x" } as never;
    st.verify!.phase = "done";
    await saveState(repoRoot, QID, st);
    const again = await runVerifyPipeline({ ...args, resume: true, fromStage: "V6", stopAfter: "V6" });
    expect(again.phase).toBe("done");
    expect(rounds).toBe(1);
    expect((await loadState(repoRoot, QID)).stage_completed).toBe("V6");
    // a V6 that throws while writing the report again leaves the run not complete (the cursor stayed at V6: the page read done)
    const throwing = { ...args, resume: true, fromStage: "V6", stages: { ...args.stages, v6: async () => { throw new Error("the report could not be written"); } } };
    await expect(runVerifyPipeline(throwing)).rejects.toThrow(/could not be written/);
    expect(await loadState(repoRoot, QID)).toMatchObject({ stage_completed: "5", verify: { phase: "v6" } });
    expect((await runVerifyPipeline({ ...args, resume: true })).phase).toBe("done");
    // an F entry the F runner would refuse is refused before the re-entry is saved: the run stays as it was
    const before = await readFile(statePath(repoRoot, QID), "utf8");
    const { runFormalization: _fake, ...real } = args;
    await expect(runVerifyPipeline({ ...real, resume: true, fromStage: "F2" })).rejects.toThrow(/refusing F2 entry: V1\.5 has not accepted a core/);
    expect(await readFile(statePath(repoRoot, QID), "utf8")).toBe(before);

    const other = await tmpRepo();
    const t2 = newTrace();
    process.env.THEOREMCHECKER_STOP_AFTER = "F5";
    try {
      const v = await runVerifyPipeline(baseArgs(other, t2));
      expect(v.phase).toBe("v6");
      expect(t2.stages).not.toContain("V6@v6");
    } finally {
      delete process.env.THEOREMCHECKER_STOP_AFTER;
    }
    // … for a V stage too (the F runner leaves it to the verify runner), and a value that is no stage is refused
    const third = await tmpRepo();
    const t3 = newTrace();
    process.env.THEOREMCHECKER_STOP_AFTER = "V1.5";
    try {
      await runVerifyPipeline(baseArgs(third, t3));
      expect(t3.stages).toEqual(["V1@init", "V1.5@v1"]);
      expect(t3.formalization).toEqual([]);
      process.env.THEOREMCHECKER_STOP_AFTER = "D0";
      await expect(runVerifyPipeline(baseArgs(await tmpRepo(), newTrace()))).rejects.toThrow(/THEOREMCHECKER_STOP_AFTER=D0 is not a stage/);
      // … at once, under the flag too; and nothing is saved when the variable's stage precedes the entry
      await expect(runVerifyPipeline({ ...baseArgs(await tmpRepo(), newTrace()), stopAfter: "F2" })).rejects.toThrow(/THEOREMCHECKER_STOP_AFTER=D0 is not a stage \(expected one of V1\|/);
      process.env.THEOREMCHECKER_STOP_AFTER = "V1.5";
      const before = await readFile(statePath(third, QID), "utf8");
      await expect(runVerifyPipeline({ ...baseArgs(third, newTrace()), resume: true, fromStage: "F2" })).rejects.toThrow(/THEOREMCHECKER_STOP_AFTER=V1.5 precedes --from-stage F2/);
      expect(await readFile(statePath(third, QID), "utf8")).toBe(before);
      // the flag wins over the variable, in the F runner too (it used to read the variable itself)
      process.env.THEOREMCHECKER_STOP_AFTER = "F1";
      const t4 = newTrace();
      await runVerifyPipeline({ ...baseArgs(third, t4), resume: true, stopAfter: "F2", deferProposals: true });
      expect(t4.stopAfter).toEqual(["2"]);
    } finally {
      delete process.env.THEOREMCHECKER_STOP_AFTER;
    }
  });

  it("stops (and does not advance) when the F runner halts at a checkpoint", async () => {
    const repoRoot = await tmpRepo();
    const trace = newTrace();
    const args = baseArgs(repoRoot, trace);
    args.runFormalization = fakeFormalization(trace, "3");
    const verify = await runVerifyPipeline(args);

    expect(trace.stages).toEqual(["V1@init", "V1.5@v1"]);
    expect(verify.phase).toBe("formalization");
    const persisted = await loadState(repoRoot, QID);
    expect(persisted.stage_completed).toBe("3");
  });

  it("a halt behind a cap gate names the gate and its --clear-gate, never a plain --resume", async () => {
    const repoRoot = await tmpRepo();
    const trace = newTrace();
    const args = baseArgs(repoRoot, trace);
    args.runFormalization = async ({ toolkit, qid }) => {
      const state = await loadState(toolkit.toolkitRoot, qid);
      state.stage_completed = "1";
      state.flags.general_review_halt = "Review boundary stage_1.5_to_1 halted: budget spent";
      await saveState(toolkit.toolkitRoot, qid, state);
      return state;
    };
    const lines: string[] = [];
    const spy = vi.spyOn(console, "log").mockImplementation((m: unknown) => { lines.push(String(m)); });
    try {
      await runVerifyPipeline({ ...args, deferProposals: true } as never);
    } finally {
      spy.mockRestore();
    }
    const out = lines.join("\n");
    expect(out).toContain("GENERAL_REVIEW_HALT BLOCKED: Review boundary stage_1.5_to_1 halted: budget spent");
    expect(out).toContain("--clear-gate general_review_halt");
    expect(out).not.toContain("then continue with `theoremchecker verify <input> --resume`");
  });

  it("--clear-gate is applied on entry, also when the re-entry halts before the F stages; --from-stage V1.5 starts the plan-review budget over", async () => {
    const repoRoot = await tmpRepo();
    const trace = newTrace();
    await runVerifyPipeline(baseArgs(repoRoot, trace));
    const s = await loadState(repoRoot, QID);
    s.flags.general_review_halt = "Review boundary stage_1.5_to_1 halted: budget spent";
    (s.flags as { plan_review_rounds?: number }).plan_review_rounds = 6;
    s.flags.f1_blocked = { message: "F1 blocked: x" };
    s.flags.missing_architecture = true;
    s.flags.missing_architecture_items = [{ kind: "lemma", name_suggestion: "old_decl", purpose: "p", why_substantial: "w" }] as never;
    await saveState(repoRoot, QID, s);
    const again = { ...baseArgs(repoRoot, newTrace()), resume: true, fromStage: "V1.5" };
    await expect(runVerifyPipeline({ ...again, clearGates: ["no_such_gate"] })).rejects.toThrow(/unknown gate 'no_such_gate'/);
    expect((await loadState(repoRoot, QID)).flags.general_review_halt).toContain("budget spent");
    // a resume refused for another flag clears no gate either: nothing is saved before every flag is checked
    await expect(runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), resume: true, clearGates: ["general_review_halt"], acceptCap: true })).rejects.toThrow(/--accept-cap requires a run halted at a patch cap/);
    expect((await loadState(repoRoot, QID)).flags.general_review_halt).toContain("budget spent");
    // an F entry behind the gate, not cleared by the invocation, is refused before anything is saved (the F
    // runner rewound the cursor and then refused: a later resume re-planned instead of reviewing again)
    const gated = await readFile(statePath(repoRoot, QID), "utf8");
    await expect(runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), resume: true, fromStage: "F1" })).rejects.toThrow(/--from-stage F1 is refused, nothing changed: GENERAL_REVIEW_HALT BLOCKED/);
    expect(await readFile(statePath(repoRoot, QID), "utf8")).toBe(gated);
    // … nor one whose ruling is refused by the function that applies it (a reading id not on file), which also
    // leaves the question the agent put on the page
    await writeFile(path.join(verifyRunDir(repoRoot, QID), "orch_requests.json"), JSON.stringify([{ id: "q1", text: "which source?" }]));
    await expect(runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), resume: true, clearGates: ["general_review_halt"], editReading: ["ass:pin-owner-9: another reading"] })).rejects.toThrow();
    expect((await loadState(repoRoot, QID)).flags.general_review_halt).toContain("budget spent");
    expect(existsSync(path.join(verifyRunDir(repoRoot, QID), "orch_requests.json"))).toBe(true);
    // … nor does a re-entry the F runner would refuse (checked against the state before the entry settles anything)
    const { runFormalization: _fake, ...real } = baseArgs(repoRoot, newTrace());
    await expect(runVerifyPipeline({ ...real, resume: true, fromStage: "F2", clearGates: ["general_review_halt"] })).rejects.toThrow(/refusing F2 entry/);
    expect((await loadState(repoRoot, QID)).flags.general_review_halt).toContain("budget spent");
    again.stages.v1_5 = fakeStage("V1.5", newTrace(), "checkpoint");
    await runVerifyPipeline({ ...again, clearGates: ["general_review_halt"] });
    const after = await loadState(repoRoot, QID);
    expect(after.verify!.phase).toBe("v1");
    expect(after.flags.general_review_halt ?? null).toBeNull();
    expect((after.flags as { plan_review_rounds?: number }).plan_review_rounds).toBeUndefined();
    // … with everything else the F stages recorded of the old core: a blocked F1, a missing-architecture block
    expect(after.flags).toMatchObject({ f1_blocked: null, missing_architecture: false });
    expect(after.flags.missing_architecture_items).toBeUndefined();
    // a re-entry past F1 (a finding ruled out) leaves no blocked-F1 record behind
    after.flags.f1_blocked = { message: "F1 blocked: x" };
    await saveState(repoRoot, QID, after);
    await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), resume: true, fromStage: "F2" });
    expect((await loadState(repoRoot, QID)).flags.f1_blocked ?? null).toBeNull();
  });

  it("--resume continues from the persisted phase without re-running earlier stages", async () => {
    const repoRoot = await tmpRepo();
    const first = newTrace();
    const cold = baseArgs(repoRoot, first);
    cold.stages.v1_5 = fakeStage("V1.5", first, "checkpoint");
    const halted = await runVerifyPipeline(cold);
    expect(first.stages).toEqual(["V1@init", "V1.5@v1"]);
    expect(halted.phase).toBe("v1");
    // a plain V checkpoint is on record where the page and the watcher read a halt (the state holds nothing of it)
    const events = (await readFile(path.join(verifyRunDir(repoRoot, QID), "pipeline.jsonl"), "utf8")).trim().split("\n").map((l) => JSON.parse(l));
    expect(events.at(-1)).toMatchObject({ stage: "V1.5", status: "checkpoint", message: "fake V1.5 — settle what it names, then continue with --resume." });

    const second = newTrace();
    const resumed = await runVerifyPipeline({
      ...baseArgs(repoRoot, second),
      resume: true,
      runFormalization: fakeFormalization(second, "5"),
    });
    // V1 is NOT re-run: the resume re-enters at the persisted `v1` phase.
    expect(second.stages).toEqual(["V1.5@v1", "V6@v6"]);
    expect(resumed.phase).toBe("done");
    // … and the pass that went on is the run's last V1.5 event: the checkpoint line no longer stands as its halt
    const after = (await readFile(path.join(verifyRunDir(repoRoot, QID), "pipeline.jsonl"), "utf8")).trim().split("\n").map((l) => JSON.parse(l));
    expect(after.filter((e) => e.stage === "V1.5").at(-1)).toMatchObject({ status: "completed" });
    expect(after.at(-1)).toMatchObject({ stage: "V6", status: "completed" });
  });

  it("--from-stage V1.5 drops every finding about the core being replaced (V1.5's and the F stages') and its accepted hash", async () => {
    const repoRoot = await tmpRepo();
    await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), stopAfter: "V1" });
    const st = await loadState(repoRoot, QID);
    st.verify!.findings.push(
      { node: "thm:a", stage: "V1.5", kind: "refuted", detail: "old", witness: "w", at: "t" },
      { node: "thm:a", stage: "F3", kind: "refuted", detail: "old Lean counterexample", witness: "w", at: "t" },
    );
    st.verify!.core_sha256 = "accepted-before";
    // thm:b's repair was sent back and the run stopped before the fixer answered: no entry on file.
    st.verify!.paper_errors = { "thm:a": { detail: "d", witness: "w" }, "thm:b": { detail: "d", witness: "w" } } as never;
    await saveState(repoRoot, QID, st);
    await mkdir(path.join(verifyRunDir(repoRoot, QID), "discovery"), { recursive: true });
    await writeFile(path.join(verifyRunDir(repoRoot, QID), "discovery/patches.json"), JSON.stringify({ key_results: [], key_contribution: "", patches: [], unfixable: [{ node: "thm:a", reason: "no repair keeps it" }] }));
    const reentry = baseArgs(repoRoot, newTrace());
    reentry.stages.v1_5 = fakeStage("V1.5", newTrace(), "checkpoint");
    await runVerifyPipeline({ ...reentry, fromStage: "V1.5", stopAfter: "V1.5" });
    const after = await loadState(repoRoot, QID);
    expect(after.verify!.findings).toEqual([]);
    expect(after.verify!.core_sha256).toBeNull();
    expect(Object.keys(after.verify!.paper_errors ?? {})).toEqual(["thm:a"]);
  });

  it("--from-stage F2.5 hands straight to the F runner at that stage", async () => {
    const repoRoot = await tmpRepo();
    const setup = newTrace();
    const cold = baseArgs(repoRoot, setup);
    cold.runFormalization = fakeFormalization(setup, "3");
    await runVerifyPipeline(cold);

    const trace = newTrace();
    const verify = await runVerifyPipeline({
      ...baseArgs(repoRoot, trace),
      fromStage: "F2.5",
      runFormalization: fakeFormalization(trace, "5"),
    });
    expect(trace.stages).toEqual(["V6@v6"]);
    expect(trace.formalization).toEqual(["2.5"]);
    expect(verify.phase).toBe("done");
  });
});

describe("runVerifyPipeline — rewinds revise, they never rebuild", () => {
  const CORE = {
    qid: QID,
    symbols: [],
    assumptions: [],
    definitions: [],
    statements: [{ id: "thm:main", kind: "theorem", statement: "The estimator is asymptotically normal.", depends_on: [], status: "to-prove" }],
    target_estimand: "tau",
    bibliography: [],
  };
  const DETAIL = "Case 2 (Bucket A): thm::main needs kappa > 1, which the paper does not grant.";

  /** An F runner that leaves, on its first call, a pending receipt naming its statement in the
   * finding's text only (no `targets`: the shape of a receipt recorded before batching). Later
   * calls complete F5. */
  function rewindingFormalization(trace: Trace, calls = { n: 0 }): RunFormalization {
    return async ({ toolkit, qid, startStage }) => {
      trace.formalization.push(startStage);
      const state = await loadState(toolkit.toolkitRoot, qid);
      calls.n += 1;
      if (calls.n === 1) {
        const { pendingRewind } = await import("../../src/verify/cross_stage_rewind.js");
        const { recordVerifyFinding } = await import("../../src/verify/findings.js");
        state.stage_completed = "1";
        const detail = `${DETAIL}\nHypothesis the paper does not grant (A-kurt): kappa_z > 1\nNeeded because: the variance term must not vanish`;
        state.flags.verify_no_d_rewind = `stage_0 rewind refused (the paper's mathematics is not re-derived): ${DETAIL}`;
        recordVerifyFinding(state, { node: "run", stage: "F1", kind: "unresolved", detail, witness: null });
        state.verify!.cross_stage_rewind = pendingRewind("F1", "stage_0", detail);
      } else {
        state.stage_completed = "5";
      }
      await saveState(toolkit.toolkitRoot, qid, state);
      return state;
    };
  }

  async function withCore(repoRoot: string): Promise<void> {
    const { writeFile } = await import("node:fs/promises");
    await writeFile(path.join(verifyRunDir(repoRoot, QID), "discovery", "core.json"), JSON.stringify(CORE), "utf8");
  }

  it("a proposed F-stage rewind halts with the annotated paper named before the choices", async () => {
    const { vi } = await import("vitest");
    const annotated: string[] = [];
    const annotate: AnnotateRun = async ({ runDir, when }) => {
      annotated.push(when);
      const pdf = path.join(runDir, "annotated", "main.pdf");
      return { path: pdf, line: `${pdf} (1 annotation(s), 1 awaiting your decision)`, result: null, error: null };
    };
    const spy = vi.spyOn(console, "log").mockImplementation(() => {});
    try {
      const repoRoot = await tmpRepo();
      const trace = newTrace();
      const args = { ...baseArgs(repoRoot, trace), deps: { prepareSource: fakePrepareSource(), annotate } };
      args.stages.v1 = async ({ state }) => {
        trace.stages.push(`V1@${state.verify!.phase}`);
        await withCore(repoRoot);
        return { status: "completed", message: "fake V1" };
      };
      args.runFormalization = rewindingFormalization(trace);
      const halted = await runVerifyPipeline(args);
      expect(halted.cross_stage_rewind).toMatchObject({ status: "pending", presented: true });
      expect(annotated).toEqual(["V1.5", "rewind proposal halt"]);
      const msg = spy.mock.calls.map((c) => String(c[0])).find((l) => l.includes("F-STAGE REWIND PROPOSED")) ?? "";
      const at = msg.indexOf("Review the annotated paper: ");
      expect(at).toBeGreaterThan(0);
      expect(msg.slice(at)).toMatch(/^Review the annotated paper: \S*annotated[\\/]main\.pdf/);
      expect(at).toBeLessThan(msg.indexOf("Continue with one of:"));
    } finally {
      spy.mockRestore();
    }
  });

  it("approved at the error cap, the rewind halts with a cap_reached receipt: --clear-patch-cap routes it, --accept-cap reports", async () => {
    for (const answer of ["clear", "accept", "reject-rewind", "reject-finding"] as const) {
      const repoRoot = await tmpRepo();
      const trace = newTrace();
      const args = baseArgs(repoRoot, trace);
      const seen: unknown[] = [];
      args.stages.v1 = async ({ state, runDir }) => {
        trace.stages.push(`V1@${state.verify!.phase}`);
        const p = path.join(runDir, "discovery", "v1_revise_directive.json");
        if (existsSync(p)) {
          seen.push(JSON.parse(await readFile(p, "utf8")));
          await rm(p);
        }
        return { status: "completed", message: "fake V1" };
      };
      args.runFormalization = rewindingFormalization(trace);
      await runVerifyPipeline({ ...args, stopAfter: "V1.5" });
      await withCore(repoRoot);
      const st = await loadState(repoRoot, QID);
      st.verify!.patch_rounds = MIN_PATCH_BACKSTOP;
      await saveState(repoRoot, QID, st);
      expect((await runVerifyPipeline({ ...args, resume: true, auto: true })).cross_stage_rewind).toMatchObject({ status: "pending", presented: true });
      let verify = await runVerifyPipeline({ ...args, resume: true, auto: true });
      expect(verify.phase).toBe("formalization");
      expect(verify.cap_reached).toMatchObject({ counter: "patch_rounds", rounds: MIN_PATCH_BACKSTOP, origin: "F-rewind" });
      expect(verify.cross_stage_rewind?.status).toBe("pending");
      // a plain --resume stays halted at the cap (nothing runs)
      const before = trace.formalization.length;
      verify = await runVerifyPipeline({ ...args, resume: true, auto: true });
      expect(verify.cap_reached).not.toBeNull();
      expect(trace.formalization.length).toBe(before);
      // every exit the halt prints acts; the receipt's nodes are answered with the receipt, not by node
      if (answer === "reject-rewind" || answer === "reject-finding") {
        const lines: string[] = [];
        const spy = vi.spyOn(console, "log").mockImplementation((m: unknown) => { lines.push(String(m)); });
        try { await runVerifyPipeline({ ...args, resume: true, auto: true }); } finally { spy.mockRestore(); }
        const halt = lines.join("\n");
        expect(halt).toContain('--resume --reject-rewind "<where the paper grants it>"');
        expect(halt).toContain('--resume --reject-finding "<reading>"');
        expect(halt).not.toContain('--reject-finding "<node>: <reading>"');
        const d = path.join(verifyRunDir(repoRoot, QID), "discovery");
        await writeFile(path.join(d, "core.transcribed.json"), await readFile(path.join(d, "core.json"), "utf8"));
        verify = await runVerifyPipeline(answer === "reject-rewind" ? { ...args, resume: true, rejectRewind: "Assumption 3 grants it" } : { ...args, resume: true, rejectFinding: "the moment is conditional on the design" });
        expect(verify.cap_reached ?? null).toBeNull();
        expect(verify.cross_stage_rewind).toMatchObject({ status: "rejected" });
        expect(seen).toEqual([]);
        continue;
      }
      if (answer === "clear") {
        verify = await runVerifyPipeline({ ...args, resume: true, clearPatchCap: true });
        expect(seen).toEqual([expect.objectContaining({ mode: "patch", round: 1 })]);
        expect(verify.patch_rounds).toBe(1); // a fresh window, this rewind its first round
        expect(verify.cross_stage_rewind).toMatchObject({ status: "applied" });
        expect(verify.phase).toBe("done");
      } else {
        verify = await runVerifyPipeline({ ...args, resume: true, acceptCap: true });
        expect(seen).toEqual([]);
        expect(verify.cross_stage_rewind).toMatchObject({ status: "refused", why: expect.stringContaining("accepted the patch_rounds cap") });
        expect(verify.cap_reached ?? null).toBeNull();
        expect(trace.stages.at(-1)).toBe("V6@v6");
      }
    }
  });

  const PR_REASON = "[statement-wrong] Specify whether the limit is taken along n or along the design; the frozen wording permits both readings.";

  /** An F runner whose F2.5 proof reviewer escalates `fix-source [statement-wrong]` on its first
   * call, recorded as `recordProofReviewOutcome` records it; later calls complete F5. */
  function proofReviewEscalating(trace: Trace, objId: string, calls = { n: 0 }): RunFormalization {
    return async ({ toolkit, qid, startStage }) => {
      trace.formalization.push(startStage);
      const state = await loadState(toolkit.toolkitRoot, qid);
      calls.n += 1;
      if (calls.n === 1) {
        const { recordProofReviewOutcome } = await import("../../src/formalization/dispatcher.js");
        recordProofReviewOutcome(state, { status: "escalate", route: "fix-source", phase: "2.5", reason: PR_REASON, kind: "statement-wrong", obj_id: objId });
      } else {
        state.flags.proof_review_escalation_pending = null;
        state.stage_completed = "5";
      }
      await saveState(toolkit.toolkitRoot, qid, state);
      return state;
    };
  }

  function consumingV1(trace: Trace, repoRoot: string, seen: unknown[]): VerifyStage {
    return async ({ state, runDir }) => {
      trace.stages.push(`V1@${state.verify!.phase}`);
      const p = path.join(runDir, "discovery", "v1_revise_directive.json");
      if (existsSync(p)) {
        seen.push(JSON.parse(await readFile(p, "utf8")));
        await rm(p);
      } else {
        await withCore(repoRoot);
      }
      return { status: "completed", message: "fake V1" };
    };
  }

  it("a Lean-internal escalation keeps halting; the next --resume re-enters F2.5 as before", async () => {
    const repoRoot = await tmpRepo();
    const trace = newTrace();
    const args = baseArgs(repoRoot, trace);
    args.stages.v1 = consumingV1(trace, repoRoot, []);
    const calls = { n: 0 };
    args.runFormalization = proofReviewEscalating(trace, "aux_limit_along_n", calls);
    let verify = await runVerifyPipeline(args);
    expect(verify.phase).toBe("formalization");
    expect(verify.cross_stage_rewind).toMatchObject({ status: "refused", why: expect.stringContaining("aux_limit_along_n") });
    expect((await loadState(repoRoot, QID)).flags.proof_review_escalation_pending).not.toBeNull();
    expect(verify.patch_rounds ?? 0).toBe(0);
    verify = await runVerifyPipeline({ ...args, resume: true });
    expect(trace.formalization).toEqual(["1", undefined]); // the resume hands F2.5 back to the F runner
    expect(verify.phase).toBe("done");
  });

  it("two paper-statement findings of one F2.5 pass (a statement and an assumption) → one receipt, one approval, one round, one directive", async () => {
    const { writeFile } = await import("node:fs/promises");
    const repoRoot = await tmpRepo();
    const trace = newTrace();
    const args = baseArgs(repoRoot, trace);
    const core = {
      ...CORE,
      assumptions: [{ id: "ass:reg", kind: "regularity", condition: "F is strictly increasing.", novel: { flag: true, justification: "stated" } }],
      statements: [
        { ...CORE.statements[0], depends_on: ["ass:reg"] },
        { id: "lem:aux", kind: "lemma", statement: "The limit exists.", depends_on: [], status: "to-prove" },
      ],
    };
    const seen: Array<{ findings: Array<{ id: string; detail: string }> }> = [];
    args.stages.v1 = async ({ state, runDir }) => {
      trace.stages.push(`V1@${state.verify!.phase}`);
      const p = path.join(runDir, "discovery", "v1_revise_directive.json");
      if (existsSync(p)) {
        seen.push(JSON.parse(await readFile(p, "utf8")));
        await rm(p);
      } else {
        await writeFile(path.join(runDir, "discovery", "core.json"), JSON.stringify(core), "utf8");
      }
      return { status: "completed", message: "fake V1" };
    };
    const calls = { n: 0 };
    args.runFormalization = async ({ toolkit, qid, startStage }) => {
      trace.formalization.push(startStage);
      const state = await loadState(toolkit.toolkitRoot, qid);
      calls.n += 1;
      if (calls.n === 1) {
        const { recordProofReviewOutcome } = await import("../../src/formalization/dispatcher.js");
        const batch = [
          { route: "fix-source" as const, reason: PR_REASON, kind: "statement-wrong", obj_id: "lem:aux" },
          { route: "fix-source" as const, reason: "[statement-wrong] 'strictly increasing' admits two readings; specify the domain", kind: "statement-wrong", obj_id: "ass:reg" },
        ];
        recordProofReviewOutcome(state, { status: "escalate", phase: "2.5", ...batch[0]!, batch });
      } else {
        state.flags.proof_review_escalation_pending = null;
        state.stage_completed = "5";
      }
      await saveState(toolkit.toolkitRoot, qid, state);
      return state;
    };
    const halted = await runVerifyPipeline(args);
    expect(halted.cross_stage_rewind).toMatchObject({ status: "pending", presented: true, nodes: ["lem:aux", "thm:main"] });
    expect(halted.cross_stage_rewind!.targets).toHaveLength(2);
    expect(halted.findings.filter((f) => f.kind === "unresolved")).toHaveLength(2);
    const verify = await runVerifyPipeline({ ...args, resume: true });
    expect(trace.formalization).toEqual(["1", "1"]);
    expect(seen).toHaveLength(1);
    // the assumption's finding is one directive finding on the assumption itself, naming its user
    expect(seen[0]!.findings).toEqual([
      expect.objectContaining({ id: "lem:aux" }),
      expect.objectContaining({ id: "ass:reg", detail: expect.stringContaining("This hypothesis of the paper is used by thm:main") }),
    ]);
    expect(verify.cross_stage_rewind).toMatchObject({ status: "applied", nodes: ["lem:aux", "thm:main"], round: 1 });
    expect(verify.refinement_rounds).toBe(1); // both are clarifications: one refinement round for the batch
    expect(verify.patch_rounds ?? 0).toBe(0);
    expect(verify.phase).toBe("done");
  });

});

describe("runVerifyPipeline — the orchestrator rules on rewinds and caps (every mode)", () => {
  const CORE = {
    qid: QID,
    symbols: [],
    assumptions: [],
    definitions: [],
    statements: [{ id: "thm:main", kind: "theorem", statement: "The estimator is asymptotically normal.", depends_on: [], status: "to-prove" }],
    target_estimand: "tau",
    bibliography: [],
  };
  const REASON = "[statement-wrong] thm:main needs a finite fourth moment, which the paper does not grant.";

  async function atFormalization(repoRoot: string): Promise<void> {
    const { writeFile } = await import("node:fs/promises");
    await runVerifyPipeline({ ...baseArgs(repoRoot, newTrace()), stopAfter: "V1.5" });
    // V1 accepted the transcription: core.json and its unpatched copy.
    for (const f of ["core.json", "core.transcribed.json"]) await writeFile(path.join(verifyRunDir(repoRoot, QID), "discovery", f), JSON.stringify(CORE), "utf8");
  }

  it("a plain resume in the Lean stages that clears a gate is checked against the F runner's entry rule first: refused, the gate stands", async () => {
    const repoRoot = await tmpRepo();
    await atFormalization(repoRoot);
    const st = await loadState(repoRoot, QID);
    // halted in the proof loop at its cap; the core was edited since V1.5 accepted it
    Object.assign(st, { stage_completed: "2" });
    Object.assign(st.verify!, { phase: "formalization", core_sha256: "accepted-before-the-edit" });
    st.flags.proof_loop_cap_hit = "iters 12/12";
    await saveState(repoRoot, QID, st);
    const { runFormalization: _fake, ...real } = baseArgs(repoRoot, newTrace());
    await expect(runVerifyPipeline({ ...real, resume: true, clearGates: ["proof_loop_cap_hit"] })).rejects.toThrow(/refusing F2\.5 entry/);
    expect((await loadState(repoRoot, QID)).flags.proof_loop_cap_hit).toBe("iters 12/12");
  });

  /** F runner: escalates `statement-wrong` on thm:main on the calls listed in `escalateOn`, else completes F5. */
  function escalatingOn(trace: Trace, escalateOn: number[], calls = { n: 0 }): RunFormalization {
    return async ({ toolkit, qid, startStage }) => {
      trace.formalization.push(startStage);
      const state = await loadState(toolkit.toolkitRoot, qid);
      calls.n += 1;
      if (escalateOn.includes(calls.n)) {
        const { recordProofReviewOutcome } = await import("../../src/formalization/dispatcher.js");
        recordProofReviewOutcome(state, { status: "escalate", route: "fix-source", phase: "3", reason: REASON, kind: "statement-wrong", obj_id: "thm:main" });
      } else {
        state.flags.proof_review_escalation_pending = null;
        state.stage_completed = "5";
      }
      await saveState(toolkit.toolkitRoot, qid, state);
      return state;
    };
  }

  it("--auto does not bypass the proposal; --reject-rewind records it, the F stages continue, and a repeat is a note", async () => {
    const repoRoot = await tmpRepo();
    await atFormalization(repoRoot);
    const trace = newTrace();
    const calls = { n: 0 };
    const args = { ...baseArgs(repoRoot, trace), runFormalization: escalatingOn(trace, [1, 2], calls), auto: true, resume: true };
    const halted = await runVerifyPipeline(args);
    expect(halted.phase).toBe("formalization");
    expect(halted.cross_stage_rewind).toMatchObject({ status: "pending", presented: true, stage: "F3", nodes: ["thm:main"], axis: "correctness" });
    expect(trace.stages).toEqual([]); // no V1 patch round without the orchestrator's approval

    // (the annotated paper written at the halt asks for the decision: it is written again once the rewind is rejected)
    const whens: Array<{ when: string; pending: string | undefined }> = [];
    const annotate = (async ({ runDir, when, state }: { runDir: string; when: string; state: StateJson }) => {
      whens.push({ when, pending: state.verify?.cross_stage_rewind?.status });
      return { path: path.join(runDir, "annotated", "main.pdf"), line: "annotated", result: null, error: null };
    }) as never;
    const verify = await runVerifyPipeline({ ...args, deps: { ...args.deps, annotate }, rejectRewind: "Assumption 3 grants E|Y|^4 < ∞ (Section 2)." });
    expect(whens[0]).toEqual({ when: "rewind rejected", pending: "rejected" });
    // continued from where F halted (call 2), which re-raised the same finding: a note, and on (call 3)
    expect(trace.formalization).toEqual(["1", undefined, undefined]);
    expect(trace.stages).toEqual(["V6@v6"]);
    expect(verify.phase).toBe("done");
    expect(verify.rejected_rewinds).toEqual([expect.objectContaining({ node: "thm:main", axis: "correctness", by: "orchestrator", reason: expect.stringContaining("Assumption 3") })]);
    expect(verify.cross_stage_rewind).toMatchObject({ status: "rejected", rejected_reason: expect.stringContaining("repeats") });
    expect(verify.findings.filter((f) => f.node === "thm:main").map((f) => f.kind)).toEqual(["note", "note"]);
    expect(verify.patch_rounds ?? 0).toBe(0);
  });

  it("--reject-finding at a proposed rewind: the owner's reading is pinned into the statement, the finding is withdrawn, V1.5 re-grades and F1 re-plans", async () => {
    const repoRoot = await tmpRepo();
    await atFormalization(repoRoot);
    const trace = newTrace();
    const calls = { n: 0 };
    const args = { ...baseArgs(repoRoot, trace), runFormalization: escalatingOn(trace, [1], calls), auto: true, resume: true };
    const halted = await runVerifyPipeline(args);
    expect(halted.cross_stage_rewind).toMatchObject({ status: "pending", presented: true, nodes: ["thm:main"] });
    await expect(runVerifyPipeline({ ...args, rejectFinding: "  " })).rejects.toThrow(/needs the reading/);
    // a node of the receipt is answered with the receipt, never by node (nothing is changed)
    await expect(runVerifyPipeline({ ...args, rejectFinding: ["thm:main: the paper means it conditionally"] })).rejects.toThrow(/item of the pending receipt: answer the receipt/);
    const reading = "The fourth moment is finite by Assumption 3 read with the paper's conditional convention.";
    const verify = await runVerifyPipeline({ ...args, rejectFinding: reading });
    expect(verify.cross_stage_rewind).toMatchObject({ status: "rejected", rejected_reason: reading });
    expect(verify.rejected_rewinds).toEqual([expect.objectContaining({ node: "thm:main", axis: "correctness", by: "owner", reason: reading, pin: "ass:pin-owner-1" })]);
    expect(verify.paper_errors!["thm:main"]).toMatchObject({ owner_decision: "finding rejected", decision_reason: reading, owner_overruled: true });
    // the pin is in the core, wired into the statement, and binds the F stages
    const runDir = verifyRunDir(repoRoot, QID);
    const core = JSON.parse(await readFile(path.join(runDir, "discovery", "core.json"), "utf8"));
    expect(core.assumptions).toEqual([expect.objectContaining({ id: "ass:pin-owner-1", condition: reading, bookkeeping: expect.objectContaining({ added_by: "owner" }) })]);
    expect(core.statements[0].depends_on).toContain("ass:pin-owner-1");
    expect(core.statements[0].statement).toBe(CORE.statements[0]!.statement);
    const { bindingReadings, renderBindingReadings } = await import("../../src/verify/core_graph.js");
    expect(renderBindingReadings(bindingReadings(core, "thm:main"))).toContain("ass:pin-owner-1 (reading of thm:main, adopted by the paper's owner)");
    // no patch round: V1.5 grades what changed, then F1 plans the core with the pin
    expect(trace.stages).toEqual(["V1.5@v1", "V6@v6"]);
    expect(trace.formalization).toEqual(["1", "1"]);
    expect(verify.patch_rounds ?? 0).toBe(0);
    expect(verify.phase).toBe("done");
    expect(verify.findings.filter((f) => f.node === "thm:main").map((f) => f.kind)).toEqual(["note"]);
    expect(verify.findings.find((f) => f.node === "thm:main")!.detail).toContain("finding withdrawn by the paper's owner");

    // the reading on record, reworded then removed: each resume re-enters at V1.5 and re-plans from F1
    await expect(runVerifyPipeline({ ...args, removeReading: ["ass:pin-owner-7"] })).rejects.toThrow(/ass:pin-owner-7 is not an owner reading/);
    await expect(runVerifyPipeline({ ...args, removeReading: ["ass:pin-owner-1"], acceptCap: true })).rejects.toThrow(/give one/);
    const reworded = await runVerifyPipeline({ ...args, editReading: ["ass:pin-owner-1: The fourth moment is finite by Assumption 3."] });
    expect(trace.stages).toEqual(["V1.5@v1", "V6@v6", "V1.5@v1", "V6@v6"]);
    expect(trace.formalization).toEqual(["1", "1", "1"]);
    expect(reworded.paper_errors!["thm:main"]).toMatchObject({ owner_decision: "finding rejected", decision_reason: "The fourth moment is finite by Assumption 3." });
    expect(JSON.parse(await readFile(path.join(runDir, "discovery", "core.json"), "utf8")).assumptions[0].condition).toBe("The fourth moment is finite by Assumption 3.");
    // … also at a render / contract checkpoint (the reading's own text may be the block that does not
    // compile): the edit is applied, and the V1.5 pass it starts renders again — never "was not read"
    const halted2 = await loadState(repoRoot, QID);
    halted2.verify!.render_checkpoint = { kind: "contract", when: "V1.5", defects: [{ node: "thm:main", block: "reading", reason: "does not compile" }] as never, at: "x" };
    await saveState(repoRoot, QID, halted2);
    await expect(runVerifyPipeline({ ...args, acceptCap: true })).rejects.toThrow(/--accept-cap was not read/);
    // a REFUSED edit leaves the checkpoint standing: nothing is cleared before the edit is applied
    await expect(runVerifyPipeline({ ...args, removeReading: ["ass:pin-owner-9"] })).rejects.toThrow(/ass:pin-owner-9 is not an owner reading/);
    expect((await loadState(repoRoot, QID)).verify!.render_checkpoint).toBeTruthy();
    const revoked = await runVerifyPipeline({ ...args, removeReading: ["ass:pin-owner-1"] });
    expect(revoked.render_checkpoint ?? null).toBeNull();
    expect(trace.stages).toEqual(["V1.5@v1", "V6@v6", "V1.5@v1", "V6@v6", "V1.5@v1", "V6@v6"]);
    expect(trace.formalization).toEqual(["1", "1", "1", "1"]);
    expect(revoked.rejected_rewinds).toBeUndefined();
    expect(revoked.paper_errors?.["thm:main"]).toBeUndefined();
    const bare = JSON.parse(await readFile(path.join(runDir, "discovery", "core.json"), "utf8"));
    expect(bare.assumptions).toEqual([]);
    expect(bare.statements[0].depends_on).not.toContain("ass:pin-owner-1");
  });

  it("another ruling given at a proposed rewind approves nothing: the core it changes is reviewed and the proposal is shown again — only a plain --resume approves", async () => {
    const repoRoot = await tmpRepo();
    await atFormalization(repoRoot);
    const trace = newTrace();
    const args = { ...baseArgs(repoRoot, trace), runFormalization: escalatingOn(trace, [1], { n: 0 }), auto: true, resume: true };
    expect((await runVerifyPipeline(args)).cross_stage_rewind).toMatchObject({ status: "pending", presented: true });
    const before = trace.stages.length;
    const again = await runVerifyPipeline({ ...args, addCondition: ["thm:main: the moments are finite"] });
    expect(trace.stages.slice(before)).toEqual(["V1.5@v1"]);
    expect(again.cross_stage_rewind).toMatchObject({ status: "pending", presented: true });
    expect(again.phase).toBe("formalization");
    expect(again.patch_rounds ?? 0).toBe(0);
    // the plain resume then approves it
    const approved = await runVerifyPipeline(args);
    expect(approved.cross_stage_rewind).toMatchObject({ status: "applied" });
  });

  it("each answer is refused anywhere but at its halt", async () => {
    const repoRoot = await tmpRepo();
    await atFormalization(repoRoot);
    const args = { ...baseArgs(repoRoot, newTrace()), resume: true };
    await expect(runVerifyPipeline({ ...args, rejectRewind: "r" })).rejects.toThrow(/halted at a proposed F-stage rewind/);
    await expect(runVerifyPipeline({ ...args, rejectFinding: "r" })).rejects.toThrow(/--reject-finding "<reading>" \(no node named\) requires a run halted at a suggested repair .* or at a proposed F-stage rewind/);
    await expect(runVerifyPipeline({ ...args, clearPatchCap: true })).rejects.toThrow(/--clear-patch-cap requires a run halted at a patch cap/);
    await expect(runVerifyPipeline({ ...args, acceptCap: true })).rejects.toThrow(/--accept-cap requires a run halted at a patch cap/);
    await expect(runVerifyPipeline({ ...args, resume: false, fromStage: "F1", clearPatchCap: true })).rejects.toThrow(/needs --resume/);
    await expect(runVerifyPipeline({ ...args, clearPatchCap: true, acceptCap: true })).rejects.toThrow(/give one/);
  });

  /** A V1.5 that halts at the error cap the first time (as `runStageV1_5` does), then accepts. */
  function cappingV1_5(trace: Trace): VerifyStage {
    let n = 0;
    return async ({ state }) => {
      trace.stages.push(`V1.5@${state.verify!.phase}`);
      n += 1;
      if (n === 1) {
        state.verify!.patch_rounds = MIN_PATCH_BACKSTOP;
        state.verify!.cap_reached = { counter: "patch_rounds", rounds: MIN_PATCH_BACKSTOP, cap: MIN_PATCH_BACKSTOP, origin: "V1.5", findings: [{ id: "thm:main", axis: "correctness", detail: "still wrong", witness: "w" }], proposed: [], at: "t" };
        return { status: "checkpoint", message: "cap" };
      }
      return { status: "completed", message: "accepted" };
    };
  }

  it("a V1.5 cap halts in --auto; a plain --resume stays halted; --clear-patch-cap opens a new window at V1", async () => {
    const repoRoot = await tmpRepo();
    const trace = newTrace();
    const args = { ...baseArgs(repoRoot, trace), auto: true };
    args.stages.v1_5 = cappingV1_5(trace);
    let verify = await runVerifyPipeline(args);
    expect(verify.cap_reached).toMatchObject({ counter: "patch_rounds", origin: "V1.5" });
    expect(verify.phase).toBe("v1");
    verify = await runVerifyPipeline({ ...args, resume: true });
    expect(trace.stages).toEqual(["V1@init", "V1.5@v1"]); // nothing ran
    verify = await runVerifyPipeline({ ...args, resume: true, clearPatchCap: true });
    expect(trace.stages).toEqual(["V1@init", "V1.5@v1", "V1@init", "V1.5@v1", "V6@v6"]);
    expect(verify.patch_rounds).toBe(1);
    expect(verify.cap_reached ?? null).toBeNull();
    expect(verify.phase).toBe("done");
  });

  it("--accept-cap ends the loop at a V1.5 cap: the cap acceptance records, then V6 reports", async () => {
    const repoRoot = await tmpRepo();
    const trace = newTrace();
    const args = baseArgs(repoRoot, trace);
    const stages = {
      ...args.stages,
      v1_5: cappingV1_5(trace),
      acceptCapV1_5: fakeStage("accept-cap", trace, "failed", (state) => {
        state.verify!.findings.push({ node: "thm:main", stage: "V1.5", kind: "refuted", detail: "still wrong", witness: "w", at: "t" });
      }),
    };
    await runVerifyPipeline({ ...args, stages });
    const verify = await runVerifyPipeline({ ...args, stages, resume: true, acceptCap: true });
    expect(trace.stages).toEqual(["V1@init", "V1.5@v1", "accept-cap@v1", "V6@v6"]);
    expect(verify.phase).toBe("failed");
    expect(verify.cap_reached ?? null).toBeNull();
    // the runner's patch directive for the round that never ran is withdrawn
    expect(existsSync(path.join(verifyRunDir(repoRoot, QID), "discovery", "v1_revise_directive.json"))).toBe(false);
  });

  it("the annotated paper: written at the end of every V1.5 pass and at each owner halt, named before the choices", async () => {
    const { vi } = await import("vitest");
    const annotated: string[] = [];
    const annotate: AnnotateRun = async ({ runDir, when }) => {
      annotated.push(when);
      const pdf = path.join(runDir, "annotated", "main.pdf");
      return { path: pdf, line: `${pdf} (1 annotation(s))`, result: null, error: null };
    };
    const spy = vi.spyOn(console, "log").mockImplementation(() => {});
    const lines = (): string[] => spy.mock.calls.map((c) => String(c[0]));
    const beforeChoices = (header: string): void => {
      const msg = lines().filter((l) => l.includes(header) && l.includes("Continue with one of:")).at(-1) ?? "";
      const at = msg.indexOf("Review the annotated paper: ");
      expect(at).toBeGreaterThan(0);
      expect(msg.slice(at)).toMatch(/^Review the annotated paper: \S*annotated[\\/]main\.pdf/);
      expect(at).toBeLessThan(msg.indexOf("Continue with one of:"));
    };
    try {
      // A V1.5 pass that accepts (with --stop-after V1.5): the completion line and the stop name it.
      {
        const repoRoot = await tmpRepo();
        const args = { ...baseArgs(repoRoot, newTrace()), deps: { prepareSource: fakePrepareSource(), annotate } };
        await runVerifyPipeline({ ...args, stopAfter: "V1.5" });
        expect(annotated).toEqual(["V1.5"]);
        expect(lines()).toContainEqual(expect.stringMatching(/V1\.5: completed — .*; annotated paper: \S*annotated[\\/]main\.pdf/));
        expect(lines()).toContainEqual(expect.stringMatching(/--stop-after V1\.5: halting for inspection — review the annotated paper: \S*main\.pdf/));
      }
      // A V1.5 pass ending at the cap: one tree for the pass (reused by the halt); a plain --resume
      // re-presents the halt with a regenerated tree.
      {
        annotated.length = 0;
        const repoRoot = await tmpRepo();
        const trace = newTrace();
        const args = { ...baseArgs(repoRoot, trace), deps: { prepareSource: fakePrepareSource(), annotate } };
        args.stages.v1_5 = cappingV1_5(trace);
        await runVerifyPipeline(args);
        expect(annotated).toEqual(["V1.5"]);
        beforeChoices("PATCH CAP:");
        await runVerifyPipeline({ ...args, resume: true });
        expect(annotated).toEqual(["V1.5", "patch cap halt"]);
        beforeChoices("PATCH CAP:");
      }
    } finally {
      spy.mockRestore();
    }
  });
});

describe("runVerifyPipeline — rendering fallbacks are a checkpoint (user decision 2026-09-25)", () => {
  /** An annotated paper whose render leaves an escaped fragment until `fixedAfter` renders (the renderer "fixed"). */
  const escapingAnnotate = (whens: string[], fixedAfter = Infinity): AnnotateRun => async ({ runDir, when }) => {
    whens.push(when);
    const render = whens.length > fixedAfter ? [] : [{ node: "lem:a", block: "corrected step of the proof of lem:a", reason: "fragment escaped (math outside math in \"Therefore\\quad x\")" }];
    const pdf = path.join(runDir, "annotated", "main.pdf");
    return { path: pdf, line: pdf, result: null, error: null, render };
  };
  const quiet = async <T>(f: (lines: () => string[]) => Promise<T>): Promise<T> => {
    const { vi } = await import("vitest");
    const spy = vi.spyOn(console, "log").mockImplementation(() => {});
    try {
      return await f(() => spy.mock.calls.map((c) => String(c[0])));
    } finally {
      spy.mockRestore();
    }
  };

  it("an escaped fragment at the V1.5 pass end halts before F1 (--auto too); --resume renders again: still escaped → halted, clean → cleared and the run goes on", async () => {
    await quiet(async (lines) => {
      const repoRoot = await tmpRepo();
      const trace = newTrace();
      const whens: string[] = [];
      const args = { ...baseArgs(repoRoot, trace), auto: true, deps: { prepareSource: fakePrepareSource(), annotate: escapingAnnotate(whens, 2) } };
      let verify = await runVerifyPipeline(args);
      expect(trace.formalization).toEqual([]);
      expect(verify.render_checkpoint).toMatchObject({ defects: [{ node: "lem:a", block: "corrected step of the proof of lem:a" }] });
      expect(lines()).toContainEqual(expect.stringMatching(/^\[verify\] render checkpoint: 1 block\(s\) could not be set as TeX —\n {4}lem:a — corrected step of the proof of lem:a: fragment escaped/u));
      expect(lines()).toContainEqual(expect.stringContaining("RENDER CHECKPOINT"));
      expect(lines()).toContainEqual(expect.stringContaining("never route it to the owner"));
      // a plain resume renders again; still escaped → still halted
      verify = await runVerifyPipeline({ ...args, resume: true });
      expect(whens).toEqual(["V1.5", "render checkpoint"]);
      expect(trace.formalization).toEqual([]);
      expect(verify.render_checkpoint).toBeTruthy();
      // the renderer is fixed: the next render is clean, the checkpoint clears, F1 runs
      verify = await runVerifyPipeline({ ...args, resume: true });
      expect(whens).toEqual(["V1.5", "render checkpoint", "render checkpoint"]);
      expect(verify.render_checkpoint).toBeNull();
      expect(trace.formalization).toEqual(["1"]);
      expect(lines()).toContainEqual(expect.stringContaining("render checkpoint cleared"));
    });
  });

  it("an owner halt (patch cap) is not presented while the render is defective", async () => {
    await quiet(async (lines) => {
      const repoRoot = await tmpRepo();
      const trace = newTrace();
      const whens: string[] = [];
      const args = { ...baseArgs(repoRoot, trace), deps: { prepareSource: fakePrepareSource(), annotate: escapingAnnotate(whens, 2) } };
      args.stages.v1_5 = async ({ state }) => {
        trace.stages.push(`V1.5@${state.verify!.phase}`);
        state.verify!.patch_rounds = MIN_PATCH_BACKSTOP;
        state.verify!.cap_reached = { counter: "patch_rounds", rounds: MIN_PATCH_BACKSTOP, cap: MIN_PATCH_BACKSTOP, origin: "V1.5", findings: [{ id: "thm:main", axis: "correctness", detail: "still wrong", witness: "w" }], proposed: [], at: "t" };
        return { status: "checkpoint", message: "cap" };
      };
      const verify = await runVerifyPipeline(args);
      expect(verify.cap_reached).toBeTruthy();
      expect(verify.render_checkpoint).toBeTruthy();
      expect(lines().some((l) => l.includes("PATCH CAP:"))).toBe(false);
      // a ruling sent while the checkpoint still stands is refused aloud, never dropped (still defective)
      await expect(runVerifyPipeline({ ...args, resume: true, acceptCap: true })).rejects.toThrow(/--accept-cap was not read: the run is halted at a render checkpoint/);
      expect(lines().some((l) => l.includes("PATCH CAP:"))).toBe(false);
      await runVerifyPipeline({ ...args, resume: true }); // clean: the halt is presented
      expect(lines().some((l) => l.includes("PATCH CAP:"))).toBe(true);
      expect(whens).toEqual(["V1.5", "render checkpoint", "render checkpoint", "patch cap halt"]);
    });
  });
});

describe("runVerifyPipeline — a model fragment that does not compile goes back to its producer (user rule 2026-09-25)", () => {
  const symbolFrag = { node: "symbol N", block: "symbol reading", reason: "Missing $ inserted.; printed verbatim — the fragment: N is the size", fragment: { kind: "note" as const, text: "N is the size", producer: "symbol" as const, error: "Missing $ inserted.", ref: "N" } };
  /** An annotated paper whose render carries a failing symbol reading until `fixedAfter` renders. */
  const fragAnnotate = (whens: string[], fixedAfter = Infinity): AnnotateRun => async ({ runDir, when }) => {
    whens.push(when);
    const render = whens.length > fixedAfter ? [] : [symbolFrag];
    const pdf = path.join(runDir, "annotated", "main.pdf");
    return { path: pdf, line: pdf, result: null, error: null, render };
  };
  const quiet = async <T>(f: (lines: () => string[]) => Promise<T>): Promise<T> => {
    const { vi } = await import("vitest");
    const spy = vi.spyOn(console, "log").mockImplementation(() => {});
    try {
      return await f(() => spy.mock.calls.map((c) => String(c[0])));
    } finally {
      spy.mockRestore();
    }
  };

  it("at the V1.5 pass end: no render checkpoint — the symbol's verdict is dropped, the core re-opened, another V1.5 pass writes it again, then F1", async () => {
    await quiet(async (lines) => {
      const repoRoot = await tmpRepo();
      const trace = newTrace();
      const whens: string[] = [];
      const args = { ...baseArgs(repoRoot, trace), auto: true, deps: { prepareSource: fakePrepareSource(), annotate: fragAnnotate(whens, 1) } };
      args.stages.v1_5 = fakeStage("V1.5", trace, "completed", (st) => {
        st.verify!.confirmed_symbols = { ...(st.verify!.confirmed_symbols ?? {}), N: "basis" };
      });
      const verify = await runVerifyPipeline(args);
      expect(trace.stages).toEqual(["V1@init", "V1.5@v1", "V1.5@v1", "V6@v6"]);
      expect(whens).toEqual(["V1.5", "V1.5"]);
      expect(verify.render_checkpoint ?? null).toBeNull();
      expect(trace.formalization).toEqual(["1"]);
      expect(lines().some((l) => l.includes("RENDER CHECKPOINT") || l.includes("CONTRACT CHECKPOINT"))).toBe(false);
      expect(lines()).toContainEqual(expect.stringContaining("1 fragment(s) of the symbol referee do not compile — routed back (N)"));
    });
  });

  it("a V1.5 pass that ends in a patch round routes its failing texts too: the referee's verdict dropped before V1 runs", async () => {
    await quiet(async (lines) => {
      const repoRoot = await tmpRepo();
      const trace = newTrace();
      const whens: string[] = [];
      const refFrag = { node: "thm:a", block: "weakening", reason: "Missing $ inserted.; printed verbatim — the fragment: see depends_on", fragment: { kind: "note" as const, text: "see depends_on", producer: "referee" as const, error: "Missing $ inserted." } };
      const annotate: AnnotateRun = async ({ runDir, when }) => {
        whens.push(when);
        const pdf = path.join(runDir, "annotated", "main.pdf");
        return { path: pdf, line: pdf, result: null, error: null, render: whens.length === 1 ? [refFrag] : [] };
      };
      const args = { ...baseArgs(repoRoot, trace), auto: true, deps: { prepareSource: fakePrepareSource(), annotate } };
      let reviews = 0;
      let confirmedAtV1: unknown = "unset";
      args.stages.v1 = async ({ state }) => {
        trace.stages.push(`V1@${state.verify!.phase}`);
        if (reviews === 1) confirmedAtV1 = state.verify!.confirmed?.["thm:a"] ?? null;
        return { status: "completed", message: "fake V1" };
      };
      args.stages.v1_5 = async ({ state }) => {
        trace.stages.push(`V1.5@${state.verify!.phase}`);
        reviews += 1;
        if (reviews === 1) {
          state.verify!.confirmed = { ...(state.verify!.confirmed ?? {}), "thm:a": "basis" } as never;
          return { status: "patch", message: "one error" };
        }
        return { status: "completed", message: "accepted" };
      };
      await runVerifyPipeline(args);
      expect(lines()).toContainEqual(expect.stringContaining("routed back (thm:a)"));
      expect(confirmedAtV1).toBeNull();
    });
  });

});

describe("the referee options reach V1.5", () => {
  it("referee.max_concurrent and the shard limits reach V1.5", async () => {
    let got: Pick<VerifyStageArgs, "refereeMaxConcurrent" | "refereeShardLimits"> = {};
    const capture: VerifyStage = async (a) => {
      got = { refereeMaxConcurrent: a.refereeMaxConcurrent, refereeShardLimits: a.refereeShardLimits };
      return { status: "checkpoint", message: "stop" };
    };
    const repoRoot = await tmpRepo();
    const base = baseArgs(repoRoot, newTrace());
    const referee = { max_concurrent: 2, shard_bytes: 40_000, shard_max_theorems: 2 };
    await runVerifyPipeline({ ...base, toolkit: { ...base.toolkit, referee }, stages: { ...base.stages, v1_5: capture } });
    expect(got).toEqual({ refereeMaxConcurrent: 2, refereeShardLimits: { bytes: 40_000, theorems: 2 } });
  });
});

describe("toolkit promotion round A (after F1)", () => {
  // An F runner that honours the requested stop: it reaches `stopAfterStage`, else F5.
  const stoppingFormalization = (trace: Trace): RunFormalization => async ({ toolkit, qid, startStage, stopAfterStage }) => {
    trace.formalization.push(startStage);
    trace.stopAfter.push(stopAfterStage);
    const state = await loadState(toolkit.toolkitRoot, qid);
    state.stage_completed = stopAfterStage ?? "5";
    await saveState(toolkit.toolkitRoot, qid, state);
    return state;
  };

  it("a plan that breaks the plan schema goes back to F1 with the violations before round A is held; never a crash on the first one", async () => {
    const repoRoot = await tmpRepo();
    const trace = newTrace();
    const directives: (string | null | undefined)[] = [];
    // F1 writes a plan whose citation lacks its fields; the re-plan (told so) writes none in this fake.
    const planner: RunFormalization = async (a) => {
      const before = await loadState(a.toolkit.toolkitRoot, a.qid);
      directives.push(before.flags.f1_revise_directive);
      const file = planPath(a.toolkit.toolkitRoot, a.qid);
      await mkdir(path.dirname(file), { recursive: true });
      if (trace.formalization.length === 0) await writeFile(file, JSON.stringify({ citations: [{ id: "cite:x" }] }), "utf8");
      else await rm(file, { force: true });
      return stoppingFormalization(trace)(a);
    };
    let heldA = 0;
    const runPromotionA = async () => {
      heldA += 1;
      return { status: "pending_user" as const, batch_path: null, checklist_path: null, promoted: [] };
    };
    const out = await runVerifyPipeline({ ...baseArgs(repoRoot, trace), runFormalization: planner, runPromotionA });
    expect(trace.formalization).toEqual(["1", "1"]);
    expect(directives[1]).toContain("citations.0.authors");
    expect(heldA).toBe(1);
    expect(out.phase).toBe("proposals_A");
  });

  it("stops after F1 for the owner's decisions, continues at F1.5 once applied; --defer-proposals and runs past F1 skip it", async () => {
    const repoRoot = await tmpRepo();
    const trace = newTrace();
    let heldA = 0;
    const runPromotionA = async () => {
      heldA += 1;
      return { status: "pending_user" as const, batch_path: null, checklist_path: path.join(repoRoot, "doc", "proposals", `${QID}.A.md`), promoted: [] };
    };
    const first = await runVerifyPipeline({ ...baseArgs(repoRoot, trace), runFormalization: stoppingFormalization(trace), runPromotionA });
    expect(trace.stopAfter).toEqual(["1"]);
    expect(first.phase).toBe("proposals_A");
    expect(heldA).toBe(1);
    // A resume while the decisions are pending stops again without re-curating.
    const pending = newTrace();
    expect((await runVerifyPipeline({ ...baseArgs(repoRoot, pending), resume: true, runFormalization: stoppingFormalization(pending), runPromotionA })).phase).toBe("proposals_A");
    expect(heldA).toBe(1);
    // `propose --round A --apply` marks the round applied; the resume continues after F1.
    const s = await loadState(repoRoot, QID);
    s.verify!.promotion_a = { ...s.verify!.promotion_a!, status: "applied" };
    await saveState(repoRoot, QID, s);
    const rest = newTrace();
    const done = await runVerifyPipeline({ ...baseArgs(repoRoot, rest), resume: true, runFormalization: stoppingFormalization(rest), runPromotionA });
    expect(rest.formalization).toEqual([undefined]);
    expect(rest.stopAfter).toEqual([undefined]);
    expect(done.phase).toBe("done");

    // A decided round stands when the run is re-entered at V1.5 or F1 (the cited results are the same) …
    for (const fromStage of ["V1.5", "F1"]) {
      const again = newTrace();
      const re = await runVerifyPipeline({ ...baseArgs(repoRoot, again), resume: true, fromStage, runFormalization: stoppingFormalization(again), runPromotionA });
      expect(re.promotion_a?.status).toBe("applied");
      expect(heldA).toBe(1);
      expect(again.stopAfter).toEqual([undefined]);
    }
    // … and is held again after a new transcription.
    const retr = newTrace();
    const reV1 = await runVerifyPipeline({ ...baseArgs(repoRoot, retr), resume: true, fromStage: "V1", runFormalization: stoppingFormalization(retr), runPromotionA });
    expect(reV1.phase).toBe("proposals_A");
    expect(heldA).toBe(2);

    // --defer-proposals: no round A.
    const r2 = await tmpRepo();
    const t2 = newTrace();
    const deferred = await runVerifyPipeline({ ...baseArgs(r2, t2), deferProposals: true, runFormalization: stoppingFormalization(t2), runPromotionA });
    expect(t2.stopAfter).toEqual([undefined]);
    expect(deferred.promotion_a?.status).toBe("deferred");
    expect(heldA).toBe(2);

    // A run already past F1 when round A was introduced is not sent back to it.
    const r3 = await tmpRepo();
    const notHeld = async (): Promise<never> => { throw new Error("round A is not held"); };
    await runVerifyPipeline({ ...baseArgs(r3, newTrace()), stopAfter: "F5", runFormalization: fakeFormalization(newTrace(), "5"), runPromotionA: notHeld });
    const s3 = await loadState(r3, QID);
    delete s3.verify!.promotion_a;
    await saveState(r3, QID, s3);
    const t3 = newTrace();
    const after = await runVerifyPipeline({ ...baseArgs(r3, t3), resume: true, runFormalization: stoppingFormalization(t3), runPromotionA: notHeld });
    expect(after.promotion_a?.status).toBe("deferred");
    expect(after.phase).toBe("done");
  });
});
