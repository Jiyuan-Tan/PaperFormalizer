/**
 * F-only stage runner. The verify runner (`verify/pipeline.ts`) owns V1 / V1.5 / V6 and hands
 * off here with `startStage`; this runner dispatches only the F stages
 * `1, 1.5, 2, 2.5, 3, 3.5, 4, 5` and refuses every other stage id. The cursor values before F1
 * (`"init"`, `"V1"`, `"V1.5"`) and after F5 (`"V6"`) belong to the verify runner and are never
 * dispatched here. The runner only resumes a run the verify runner seeded (it never creates
 * state), and every F entry is gated by `assertFStageEntryCoherence`: V1.5 must have accepted
 * exactly the `core.json` on disk.
 */
import { existsSync } from "node:fs";
import { createHash } from "node:crypto";
import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import { performance } from "node:perf_hooks";
import { F_STAGES, formatStageLabel, fromStageRefusal, STAGE_ORDER, STAGE_TO_HALT_ID, stopAfterRefusal } from "./constants.js";
import { MISSING_ARCHITECTURE_EXIT, resumeBlock } from "./cap_gates.js";
import { appendPipelineLog } from "./log.js";
import { checkpointGuidance } from "./checkpoint_playbook.js";
import { statePath } from "./paths.js";
import { loadState, saveState } from "./state.js";
import { dryRunStageHandler, liveStageHandler, type StageHandler } from "./pipeline_stages.js";
import { withRunHeartbeat } from "./shared/run_heartbeat.js";
import { coreJsonPath } from "./core/core_io.js";
import type { PipelineContext, Stage, StateJson } from "./types.js";
import { dryRunRefusal } from "./verify/dry_run.js";

/** The cursor stage after `stage` (`null` after `"V6"`). */
export function nextStage(stage: Stage): Stage | null {
  const index = STAGE_ORDER.indexOf(stage);
  if (index === -1) throw new Error(`Unknown stage: ${formatStageLabel(stage)}`);
  return STAGE_ORDER[index + 1] ?? null;
}

/** Position of a cursor value in `STAGE_ORDER`. */
export function stageIndex(stage: Stage): number {
  return STAGE_ORDER.indexOf(stage);
}

/** The stages this runner dispatches, in order. */
export const F_STAGE_ORDER: readonly Stage[] = F_STAGES;

export function isFStage(stage: Stage): boolean {
  return F_STAGE_ORDER.includes(stage);
}

/** Fail closed on any stage id this runner does not own (a V-stage cursor value, or an unknown one). */
function refuseNonFStage(stage: Stage, why: string): never {
  throw new Error(
    `refusing ${formatStageLabel(stage)} (${why}): this runner dispatches only ` +
      `${F_STAGE_ORDER.map((s) => formatStageLabel(s)).join(", ")}`,
  );
}

/**
 * Fail closed at the V/F boundary. The F stages read `core.json`; V1.5 is the only stage allowed
 * to accept one. So F entry requires (a) a run seeded by the verify runner (`state.verify`),
 * (b) V1.5 to have completed (stage cursor at or past `"V1.5"`) with a recorded core hash, and
 * (c) the core on disk to be byte-identical to the one V1.5 accepted — a hand-edited core must
 * be re-reviewed, never formalized on the strength of a stale verdict. The runner calls it
 * before each stage.
 */
export async function assertFStageEntryCoherence(
  ctx: PipelineContext,
  state: StateJson,
  targetStage: Stage,
): Promise<void> {
  const verify = state.verify;
  if (!verify) {
    throw new Error(
      `refusing ${formatStageLabel(targetStage)} entry: state.verify is missing; ` +
        "the run was not seeded by the verify runner",
    );
  }
  // A dry-run V1.5 accepts a core no referee read: a live F stage must never build on it, and a
  // dry run never advances a live state.
  const modeRefusal = dryRunRefusal(state, ctx.dryRun === true);
  if (modeRefusal) throw new Error(`refusing ${formatStageLabel(targetStage)} entry: ${modeRefusal}`);
  if (stageIndex(state.stage_completed) < stageIndex("V1.5") || !verify.core_sha256) {
    throw new Error(
      `refusing ${formatStageLabel(targetStage)} entry: V1.5 has not accepted a core; ` +
        "run `paperformalizer verify … --resume`",
    );
  }
  const corePath = coreJsonPath(ctx);
  if (!existsSync(corePath)) {
    throw new Error(
      `refusing ${formatStageLabel(targetStage)} entry: core.json is missing at ${corePath}; ` +
        "re-extract with `--from-stage V1`",
    );
  }
  const onDisk = createHash("sha256").update(await readFile(corePath)).digest("hex");
  if (onDisk !== verify.core_sha256) {
    throw new Error(
      `refusing ${formatStageLabel(targetStage)} entry: core.json changed since V1.5 accepted it — ` +
        "re-review with `--from-stage V1.5`",
    );
  }
}

export interface RunPipelineOptions {
  startStage?: Stage;
  stopAfterStage?: Stage;
}

/** Why the F runner refuses a cold start (see `runPipeline`). */
function coldStartRefusal(ctx: PipelineContext): string {
  return (
    `refusing to cold-start the F runner for ${ctx.qid}: only the verify runner seeds a run ` +
    "(it prepares the source and runs V1/V1.5 first). Start with `paperformalizer verify <paper>`; " +
    "the F stages are entered from there with --resume."
  );
}

/**
 * Load the run's state. The F runner never creates one: a cold start (`resume: false`) is
 * refused before any file is touched, and a missing state file is an error naming the verify
 * runner, never a fresh seed.
 */
export async function initializeOrLoadState(ctx: PipelineContext): Promise<StateJson> {
  if (!ctx.resume) throw new Error(coldStartRefusal(ctx));
  const file = statePath(ctx.repoRoot, ctx.qid);
  if (!existsSync(file)) {
    throw new Error(`no run state at ${file}; start the run with \`paperformalizer verify <paper>\``);
  }
  return loadState(ctx.repoRoot, ctx.qid);
}

export async function runPipeline(
  ctx: PipelineContext,
  handler: StageHandler = ctx.dryRun ? dryRunStageHandler : liveStageHandler,
  options: RunPipelineOptions = {},
): Promise<StateJson> {
  // Refuse a cold start and a non-F entry before touching the heartbeat or any state: only the
  // verify runner seeds a run, so a `resume: false` call here could only write a stray state.
  if (!ctx.resume) throw new Error(coldStartRefusal(ctx));
  if (options.startStage && !isFStage(options.startStage)) {
    refuseNonFStage(options.startStage, "startStage");
  }
  if (options.startStage) {
    const refusal = fromStageRefusal(STAGE_TO_HALT_ID[options.startStage as keyof typeof STAGE_TO_HALT_ID]);
    if (refusal) throw new Error(refusal);
  }
  if (options.stopAfterStage && !isFStage(options.stopAfterStage)) {
    refuseNonFStage(options.stopAfterStage, "stopAfterStage");
  }
  if (options.stopAfterStage) {
    const refusal = stopAfterRefusal(STAGE_TO_HALT_ID[options.stopAfterStage as keyof typeof STAGE_TO_HALT_ID]);
    if (refusal) throw new Error(refusal);
  }
  return withRunHeartbeat(ctx.repoRoot, ctx.qid, () => runPipelineInner(ctx, handler, options));
}

async function runPipelineInner(
  ctx: PipelineContext,
  handler: StageHandler,
  options: RunPipelineOptions,
): Promise<StateJson> {
  const state = await initializeOrLoadState(ctx);
  // Mode check on EVERY entry (also past F5, where no stage entry is gated below).
  const modeRefusal = dryRunRefusal(state, ctx.dryRun === true);
  if (modeRefusal) throw new Error(modeRefusal);

  // Check the entry stage (forced or natural) before any resume-preflight mutation can be
  // persisted. A natural entry past a completed F5 has no F stage to run.
  const fDone = stageIndex(state.stage_completed) >= stageIndex("5");
  const entryStage = options.startStage ?? (fDone ? null : nextStage(state.stage_completed));
  if (entryStage) {
    if (!isFStage(entryStage)) refuseNonFStage(entryStage, `next stage after ${formatStageLabel(state.stage_completed)}`);
    await assertFStageEntryCoherence(ctx, state, entryStage);
  }

  // A forced re-entry at or before the cursor rewinds it to just before the entered stage: the run
  // is no longer complete past it, whatever the stage then does. A halt there (which leaves the
  // cursor alone) used to be read, under a cursor still at F5 or V6, as a finished formalization —
  // the report written, round B opened, the halt never printed. (The run's history still says a
  // later stage ran: `laterStageEverRan` reads the log, so a re-plan stays a revise.)
  if (options.startStage && stageIndex(state.stage_completed) >= stageIndex(options.startStage)) {
    state.stage_completed = STAGE_ORDER[stageIndex(options.startStage) - 1]!;
  }

  // The caller's mode, onto state: auto unless the run is in debug mode (`verify --debug`,
  // itself latched by the verify runner, which passes `auto` from it).
  if (ctx.auto !== undefined) state.auto_mode = ctx.auto;

  const resumeGate = await resolveResumeGates(ctx, state);
  if (!resumeGate.open) {
    await appendPipelineLog(ctx, {
      stage: "resume",
      status: "blocked",
      duration_ms: 0,
      message: resumeGate.message,
    });
    console.warn(`\n[paperformalizer] resume refused, nothing ran. ${resumeGate.message}\n`);
    await saveState(ctx.repoRoot, ctx.qid, state);
    return state;
  }

  // Commit resume preflight mutations before dispatching another stage. A live
  // handler may crash after making external calls; if the run's mode
  // or a satisfied missing-architecture gate only lived in memory until that
  // handler returned, the next resume resurrected stale state and repeated
  // already-authorized work.
  await saveState(ctx.repoRoot, ctx.qid, state);

  // An explicit `--from-stage` re-entry OVERRIDES the "already complete" short-circuit: the operator
  // is deliberately re-running a stage on a finished run (e.g. to re-review after a reviewer fix), so
  // fall through to the stage dispatch below instead of returning "already complete".
  if (fDone && !options.startStage) {
    await appendPipelineLog(ctx, {
      stage: "resume",
      status: "complete",
      duration_ms: 0,
      message: "Pipeline already complete",
    });
    return state;
  }

  let stage: Stage | null = entryStage;
  const MAX_STAGE_ITERATIONS = 100;
  let stageIters = 0;
  while (stage && stageIters++ < MAX_STAGE_ITERATIONS) {
    // A rewind can move the cursor below F1 (a handler that resets `stage_completed` to a
    // pre-F marker); this runner has no stage there, so stop fail-closed with the state saved.
    if (!isFStage(stage)) refuseNonFStage(stage, `next stage after ${formatStageLabel(state.stage_completed)}`);
    await assertFStageEntryCoherence(ctx, state, stage);
    const started = performance.now();
    let result;
    try {
      result = await handler({ ctx, state, stage });
    } catch (error) {
      const duration_ms = Math.round(performance.now() - started);
      const message = error instanceof Error ? error.message : String(error);
      // A handler exception is still a pipeline event. Previously it escaped before
      // any journal append, so event-trigger monitors saw neither progress nor failure
      // and waited the full window while the process had already exited.
      try {
        await appendPipelineLog(ctx, { stage, status: "failed", duration_ms, message });
      } catch (logError) {
        // Preserve the original stage failure; a secondary journal failure must not
        // replace the actionable exception that stopped the pipeline.
        console.error(`[paperformalizer] failed to journal stage ${stage} exception: ${logError instanceof Error ? logError.message : String(logError)}`);
      }
      throw error;
    }
    const duration_ms = Math.round(performance.now() - started);
    // A combined handler may enter in one slot but complete through a later logical stage. The
    // F2.5 proof-review handler, for example, owns proof fill, lint, and dual convergence and returns
    // `completedStage: "4"`. Log that successful aggregate completion as F4. Combined handlers
    // can also report a later logical stage for a checkpoint (for example an F3 escalation while
    // entered via F2.5), so prefer their returned stage over the physical entry slot.
    const loggedStage = result.status === "completed" && result.completedStage
      ? result.completedStage
      : result.stage;
    // On a halt, re-surface the orchestrator playbook (it drifts out of
    // attention over a long run) — both on the checkpoint line it reads and on
    // the console it sees after `--resume`.
    // (by the stage of the RESULT: a combined handler halts for another stage than its slot's)
    const guidance = checkpointGuidance(result.stage, result.status, state.flags, state.auto_mode, result.message);
    await appendPipelineLog(ctx, {
      stage: loggedStage,
      status: result.status,
      duration_ms,
      message: result.message,
      ...(guidance ? { next_step_guidance: guidance } : {}),
    });
    if (guidance) {
      console.warn(
        `\n[paperformalizer] halt at ${formatStageLabel(result.stage)} (${result.status}). NEXT STEPS:\n${guidance}\n`,
      );
    }

    if (result.status === "blocked") {
      await saveState(ctx.repoRoot, ctx.qid, state);
      break;
    }

    if (result.advance !== false) {
      state.stage_completed = result.completedStage ?? stage;
    }
    await saveState(ctx.repoRoot, ctx.qid, state);


    if (stage === "5" && result.advance !== false) break;
    if (result.status === "checkpoint") {
      break;
    }
    const logicalCompletedStage = result.completedStage ?? stage;
    // Stop-after (the verify runner resolves `--stop-after` over `PAPERFORMALIZER_STOP_AFTER`, once)
    // fires only when the stage actually completed. A rewound stage has not produced a settled
    // artifact at `stage`, so the pipeline keeps running until the rewound chain re-completes it
    // (or hits a real checkpoint).
    if (result.status === "completed" && options.stopAfterStage === logicalCompletedStage) break;
    // Rewound stages reset `state.stage_completed` to an earlier marker; the
    // next iteration must advance from that marker, not from the local `stage`
    // variable which still points at the stage whose handler just rewound.
    stage =
      result.status === "rewound"
        ? nextStage(state.stage_completed)
        // Combined handlers may complete several logical stages at once. Advance from the stage
        // actually completed so their already-logged phases do not reappear as legacy skip rows.
        : nextStage(result.completedStage ?? stage);
  }
  if (stageIters > MAX_STAGE_ITERATIONS) {
    throw new Error(
      `Pipeline exceeded ${MAX_STAGE_ITERATIONS} stage iterations — possible infinite rewind loop`,
    );
  }

  return state;
}

async function resolveResumeGates(
  ctx: PipelineContext,
  state: StateJson,
): Promise<{ open: true } | { open: false; message: string }> {
  // Gates: cap-hit / halt flags. A naive `--resume` would re-run the producer and its
  // reviewer (hours of codex), hit the same persisted cap, and checkpoint again with no
  // exit instructions. Refuse up front with the reason + the deliberate clear step.
  // The set + clear semantics live in `CAP_GATES` (cap_gates.ts), shared with the
  // `--clear-gate <flag>` CLI so the orchestrator clears them via the CLI, never a
  // hand-edit of state.json.
  const capBlock = resumeBlock({ ...state.flags, missing_architecture: false });
  if (capBlock) return { open: false, message: capBlock };
  if (!state.flags.missing_architecture) return { open: true };
  const items = state.flags.missing_architecture_items ?? [];
  const unresolved = [];
  for (const item of items) {
    const found = await declarationExists(ctx, item.name_suggestion, item.suggested_location);
    if (!found) unresolved.push(item);
  }
  if (unresolved.length > 0) {
    return {
      open: false,
      message: `MISSING ARCHITECTURE BLOCKED: ${unresolved
        .map((item) => item.name_suggestion)
        .join(", ")}\nResolve: ${MISSING_ARCHITECTURE_EXIT}.`,
    };
  }
  state.flags.missing_architecture = false;
  delete state.flags.missing_architecture_items;
  return { open: true };
}

/**
 * Whether a missing-architecture item has since been built: a textual search of the toolkit
 * library, the papers library, and every path-kind base library (the `suggested_location`,
 * relative to the toolkit root, first). Lake build trees are never searched.
 */
async function declarationExists(
  ctx: PipelineContext,
  name: string,
  suggestedLocation: string | undefined,
): Promise<boolean> {
  const toolkit = ctx.toolkit;
  const roots = [
    ...(suggestedLocation ? [path.resolve(ctx.repoRoot, suggestedLocation)] : []),
    ...(toolkit
      ? [
          toolkit.toolkitLibDir,
          toolkit.papersDir,
          ...toolkit.baseLibraries.flatMap((b) => (b.kind === "path" && b.path ? [b.path] : [])),
        ]
      : [ctx.repoRoot]),
  ];
  for (const root of roots) {
    if (await fileOrTreeContains(root, name)) return true;
  }
  return false;
}

async function fileOrTreeContains(target: string, needle: string): Promise<boolean> {
  if (!existsSync(target)) return false;
  const statEntries = await readdir(target, { withFileTypes: true }).catch(async () => []);
  if (statEntries.length === 0 && target.endsWith(".lean")) {
    return (await readFile(target, "utf8").catch(() => "")).includes(needle);
  }
  for (const entry of statEntries) {
    const full = path.join(target, entry.name);
    if (entry.isDirectory() && (entry.name === ".lake" || entry.name === ".git" || entry.name === "node_modules")) continue;
    if (entry.isDirectory() && (await fileOrTreeContains(full, needle))) return true;
    if (entry.isFile() && entry.name.endsWith(".lean")) {
      const text = await readFile(full, "utf8").catch(() => "");
      if (text.includes(needle)) return true;
    }
  }
  return false;
}
