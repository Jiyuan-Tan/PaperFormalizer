import { createHash } from "node:crypto";
import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it, vi } from "vitest";
import { runVerifyPipeline } from "../src/verify/pipeline.js";
import {
  stageIndex,
  F_STAGE_ORDER,
  nextStage,
  runPipeline,
} from "../src/pipeline.js";
import { dryRunStageHandler } from "../src/pipeline_stages.js";
import type { PipelineContext, Stage, StateJson } from "../src/types.js";
import { pipelineLogPath } from "../src/paths.js";
import { tk } from "./toolkit/helpers.js";
import { createVerifyInitialState, loadState, saveState } from "../src/state.js";
import { coreJsonPath } from "../src/core/core_io.js";
import type { VerifyState } from "../src/verify/types.js";

const CORE_BODY = JSON.stringify({ qid: "runner_test" });

function verifyBlock(): VerifyState {
  return {
    phase: "formalization",
    source: { input: "paper.tex", main_file: "paper.tex", sha256: "0".repeat(64) },
    targets: null,
    core_sha256: null,
    v1_rounds: 1,
    v1_5_rounds: 0,
    findings: [],
    report_path: null,
    // `seedAcceptedRun` contexts are dry runs; a dry run continues only a dry-run state.
    dry_run: true,
  };
}

/** Seed a verify run exactly as V1.5 leaves it: cursor at "V1.5", `core.json` on disk, and its
 *  sha256 recorded as the accepted core. Returns the resume context. */
async function seedAcceptedRun(
  name: string,
  mutate: (state: StateJson) => void = () => undefined,
): Promise<PipelineContext> {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), `leansmith-runner-${name}-`));
  const qid = name.replace(/\W/g, "_");
  const ctx: PipelineContext = { repoRoot, toolkit: tk(repoRoot), qid, resume: true, dryRun: true };
  const corePath = coreJsonPath(ctx);
  await mkdir(path.dirname(corePath), { recursive: true });
  await writeFile(corePath, CORE_BODY, "utf8");
  const state = createVerifyInitialState(qid, verifyBlock());
  state.stage_completed = "V1.5";
  state.verify!.core_sha256 = createHash("sha256").update(CORE_BODY).digest("hex");
  mutate(state);
  await saveState(repoRoot, qid, state);
  return ctx;
}

async function logRows(ctx: PipelineContext): Promise<Array<{ stage: string; status: string; message?: string }>> {
  return (await readFile(pipelineLogPath(ctx.repoRoot, ctx.qid), "utf8"))
    .trim().split("\n").map((line) => JSON.parse(line));
}

const completedStages = async (ctx: PipelineContext): Promise<string[]> =>
  (await logRows(ctx)).filter((r) => r.status === "completed").map((r) => r.stage);

const okHandler = (seen: Stage[] = []) => async ({ stage }: { stage: Stage }) => {
  seen.push(stage);
  return { stage, status: "completed" as const, message: "ok" };
};

describe("F-only runner", () => {
  it("orders the F stages explicitly", () => {
    expect(F_STAGE_ORDER).toEqual(["1", "1.5", "2", "2.5", "3", "3.5", "4", "5"]);
    expect(nextStage("init")).toBe("V1");
    expect(nextStage("V1")).toBe("V1.5");
    expect(nextStage("V1.5")).toBe("1");
    expect(nextStage("1")).toBe("1.5");
    expect(nextStage("3.5")).toBe("4");
    expect(nextStage("5")).toBe("V6");
    expect(nextStage("V6")).toBeNull();
  });

  it("dry-runs F1 through F5 from an accepted core", async () => {
    const ctx = await seedAcceptedRun("dryrun");
    const state = await runPipeline(ctx, dryRunStageHandler);
    expect(state.stage_completed).toBe("5");
    expect(await completedStages(ctx)).toEqual(["1", "1.5", "2", "2.5", "3", "3.5", "4", "5"]);
  });

  it("re-enters at an explicit startStage on a completed run", async () => {
    const ctx = await seedAcceptedRun("reentry", (s) => { s.stage_completed = "5"; });
    const seen: Stage[] = [];
    const state = await runPipeline(ctx, okHandler(seen), { startStage: "2.5" });
    expect(seen).toEqual(["2.5", "3", "3.5", "4", "5"]);
    expect(state.stage_completed).toBe("5");
  });

  it.each(["3", "3.5", "4"] as const)("refuses startStage %s before touching the state: the loop starts at F2.5", async (start) => {
    const ctx = await seedAcceptedRun(`refuse-start-${start.replace(".", "-")}`, (s) => { s.stage_completed = "5"; });
    const seen: Stage[] = [];
    await expect(runPipeline(ctx, okHandler(seen), { startStage: start })).rejects.toThrow(/not an entry point[\s\S]*--from-stage F2\.5/);
    expect(seen).toEqual([]);
  });

  it.each(["1", "1.5", "2", "5"] as const)("a halt at F%s re-entered on a finished run is a halt of the run: the cursor is rewound, no report is written over it, the page does not read done", async (start) => {
    const ctx = await seedAcceptedRun(`reenter-halt-${start.replace(".", "-")}`, (s) => { s.stage_completed = "V6"; s.verify!.phase = "done"; });
    const v6: string[] = [];
    const lines: string[] = [];
    const spy = vi.spyOn(console, "log").mockImplementation((m: unknown) => { lines.push(String(m)); });
    let verify;
    try {
      verify = await runVerifyPipeline({
        toolkit: ctx.toolkit!, qid: ctx.qid, input: "paper.tex", mainHint: null, targets: null, resume: true, fromStage: `F${start}`, auto: false, dryRun: true,
        stages: { v1: async () => ({ status: "completed", message: "" }), v1_5: async () => ({ status: "completed", message: "" }), v6: async () => { v6.push("V6"); return { status: "completed", message: "" }; } },
        // the F runner itself, its stage halting as a blocked F1 / an F1.5 review halt / an F5 refusal does
        runFormalization: (a: { startStage?: Stage; stopAfterStage?: Stage }) => runPipeline({ ...ctx }, async ({ stage }) => ({ stage, status: "checkpoint", advance: false, message: `F${stage} refuses` }), { startStage: a.startStage, stopAfterStage: a.stopAfterStage }),
        runPromotion: async () => { throw new Error("no round B on a halted run"); },
      } as never);
    } finally {
      spy.mockRestore();
    }
    expect(v6).toEqual([]);
    expect(verify.phase).toBe("formalization");
    const state = await loadState(ctx.repoRoot, ctx.qid);
    expect(stageIndex(state.stage_completed)).toBe(stageIndex(start) - 1);
    expect(lines.join("\n")).toMatch(/F stages halted at stage/);
    expect((await logRows(ctx)).at(-1)).toMatchObject({ stage: start, status: "checkpoint", message: `F${start} refuses` });
    // the page: a report on file is the earlier state's, the run is not done
    const { reportCurrent, runSummary } = await import("../src/ui/run_model.js");
    expect(reportCurrent(state)).toBe(false);
    expect((await runSummary(ctx.toolkit!, ctx.qid)).status).not.toBe("done");
  });

  it("honors stopAfterStage", async () => {
    const ctx = await seedAcceptedRun("stopafter");
    const seen: Stage[] = [];
    const state = await runPipeline(ctx, okHandler(seen), { startStage: "1", stopAfterStage: "2" });
    expect(seen).toEqual(["1", "1.5", "2"]);
    expect(state.stage_completed).toBe("2");
    expect((await loadState(ctx.repoRoot, ctx.qid)).stage_completed).toBe("2");
  });

  it("plain resume continues after the persisted cursor", async () => {
    const ctx = await seedAcceptedRun("resume", (s) => { s.stage_completed = "2"; });
    const seen: Stage[] = [];
    await runPipeline(ctx, okHandler(seen));
    expect(seen).toEqual(["2.5", "3", "3.5", "4", "5"]);
  });

  it("logs a combined handler at the logical stage it completed", async () => {
    const ctx = await seedAcceptedRun("combined-log");
    const seen: Stage[] = [];
    await runPipeline(ctx, async ({ stage }) => {
      seen.push(stage);
      if (stage === "2.5") {
        return { stage, status: "completed", completedStage: "4", message: "combined proof-review loop converged" };
      }
      return { stage, status: "completed", message: "ok" };
    });
    const rows = await logRows(ctx);
    expect(rows.find((row) => row.message === "combined proof-review loop converged")?.stage).toBe("4");
    // Advances from the logical completion, so F3/F3.5/F4 are not re-dispatched.
    expect(seen).toEqual(["1", "1.5", "2", "2.5", "5"]);
  });

  it("a rewound stage advances from the rewound marker", async () => {
    const ctx = await seedAcceptedRun("rewind");
    const seen: Stage[] = [];
    let rewound = false;
    await runPipeline(ctx, async ({ state, stage }) => {
      seen.push(stage);
      if (stage === "3" && !rewound) {
        rewound = true;
        state.stage_completed = "1.5";
        return { stage, status: "rewound", advance: false, message: "redirect to F2" };
      }
      return { stage, status: "completed", message: "ok" };
    });
    expect(seen).toEqual(["1", "1.5", "2", "2.5", "3", "2", "2.5", "3", "3.5", "4", "5"]);
  });

  it("stops fail-closed when a handler rewinds below F1", async () => {
    const ctx = await seedAcceptedRun("rewind-below");
    await expect(runPipeline(ctx, async ({ state, stage }) => {
      if (stage === "2") {
        state.stage_completed = "init";
        return { stage, status: "rewound", advance: false, message: "wants V1" };
      }
      return { stage, status: "completed", message: "ok" };
    })).rejects.toThrow(/refusing V1 .*dispatches only F1/);
    expect((await loadState(ctx.repoRoot, ctx.qid)).stage_completed).toBe("init");
  });

  it("journals a handler exception as a failed stage event before rethrowing", async () => {
    const ctx = await seedAcceptedRun("handler-failure");
    await expect(runPipeline(ctx, async ({ stage }) => {
      throw new Error(`handler exploded at ${stage}`);
    })).rejects.toThrow(/handler exploded/);
    expect((await logRows(ctx)).at(-1)).toMatchObject({ stage: "1", status: "failed", message: "handler exploded at 1" });
  });

  it("blocks resume while a cap-gate flag is set", async () => {
    const ctx = await seedAcceptedRun("cap-block", (s) => {
      s.stage_completed = "2";
      (s.flags as unknown as Record<string, unknown>).general_review_halt = "plan review halted";
    });
    const seen: Stage[] = [];
    const state = await runPipeline(ctx, okHandler(seen));
    expect(seen).toEqual([]);
    expect(state.stage_completed).toBe("2");
    expect((await logRows(ctx)).at(-1)).toMatchObject({ stage: "resume", status: "blocked", message: expect.stringMatching(/GENERAL_REVIEW_HALT BLOCKED: plan review halted[\s\S]*--clear-gate general_review_halt/) });
  });

  it("a missing-architecture block names its items and its exit", async () => {
    const ctx = await seedAcceptedRun("arch-block", (s) => {
      s.stage_completed = "1.5";
      s.flags.missing_architecture = true;
      s.flags.missing_architecture_items = [{ kind: "lemma", name_suggestion: "no_such_decl_anywhere", purpose: "p", why_substantial: "w" }] as never;
    });
    const seen: Stage[] = [];
    await runPipeline(ctx, okHandler(seen));
    expect(seen).toEqual([]);
    const message = String((await logRows(ctx)).at(-1)!.message);
    expect(message).toMatch(/MISSING ARCHITECTURE BLOCKED: no_such_decl_anywhere\nResolve: build each named declaration[\s\S]*flags\.missing_architecture_items/);
  });
});

describe("F-only runner — refusals", () => {
  it.each([
    ["an entry that is not an F stage", (_s: StateJson) => undefined, { startStage: "V1" as Stage }, false,
      /dispatches only F1, F1\.5, F2, F2\.5, F3, F3\.5, F4, F5/],
    ["F1 entry before V1.5 accepted a core", (s: StateJson) => { s.verify!.core_sha256 = null; }, { startStage: "1" as Stage }, false,
      /refusing F1 entry: V1\.5 has not accepted a core/],
    ["a live runner on a dry-run state", (_s: StateJson) => undefined, {}, true, /seeded or advanced by --dry-run/],
  ])("refuses %s without dispatch or state mutation", async (name, mutate, opts, live, error) => {
    const ctx = await seedAcceptedRun(`refuse-${name.replace(/\W+/g, "-")}`, mutate);
    let dispatched = false;
    await expect(runPipeline({ ...ctx, dryRun: !live }, async ({ stage }) => {
      dispatched = true;
      return { stage, status: "completed", message: "must not dispatch" };
    }, opts)).rejects.toThrow(error);
    expect(dispatched).toBe(false);
    expect((await loadState(ctx.repoRoot, ctx.qid)).stage_completed).toBe("V1.5");
  });

  it.each([
    ["V1.5", /stopAfterStage/],
    ["3", /can never fire[\s\S]*--stop-after F2 \(halt before the loop\)[\s\S]*--stop-after F4/],
  ] as const)("refuses stopAfterStage %s", async (stop, error) => {
    const ctx = await seedAcceptedRun(`refuse-stop-${stop}`);
    let dispatched = false;
    await expect(runPipeline(ctx, async ({ stage }) => {
      dispatched = true;
      return { stage, status: "completed", message: "x" };
    }, { stopAfterStage: stop })).rejects.toThrow(error);
    expect(dispatched).toBe(false);
  });

  it("re-checks the core hash at every F transition", async () => {
    const ctx = await seedAcceptedRun("midrun-edit");
    const seen: Stage[] = [];
    await expect(runPipeline(ctx, async ({ stage }) => {
      seen.push(stage);
      if (stage === "1.5") await writeFile(coreJsonPath(ctx), "{}", "utf8");
      return { stage, status: "completed", message: "ok" };
    })).rejects.toThrow(/refusing F2 entry: core\.json changed/);
    expect(seen).toEqual(["1", "1.5"]);
  });
});
