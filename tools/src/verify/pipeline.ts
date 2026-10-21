/**
 * `paperformalizer verify` runner.
 *
 * Owns the V stages (V1 extract, V1.5 review, V6 report) and delegates F1–F5 to the F runner
 * (`runPipeline`). `state.verify.phase` says which runner owns the next step;
 * `state.stage_completed` is the linear stage cursor over `STAGE_ORDER`:
 *
 *     init → V1 → V1.5 → 1 … 5 (F runner) → V6
 *
 * V1 completing writes `"V1"`, V1.5 accepting writes `"V1.5"`, the F runner writes `"1"`…`"5"`,
 * and a report written after F5 writes `"V6"`. An early stop (V1.5 refutation) leaves the cursor
 * where the run stopped, so the report can tell that the run never reached Lean.
 *
 *     init → v1 → v1_5 → formalization (F1) → proposals_A → formalization (F1.5…F5) → v6
 *          → proposals_B → done | failed
 *                    └──── failed ──────→ v6 → failed
 *
 * TOOLKIT PROMOTION (`src/proposals/`). Round A (`proposals_A`), after F1 wrote the plan: the
 * results the paper cites without proving are proposed to the toolkit owner, and the run stops
 * until the owner decides (`paperformalizer propose <slug> --round A --apply`, which builds the
 * accepted ones with the study pipeline and points the plan at them); `--defer-proposals` skips it,
 * and a round with nothing proposed continues without stopping. Round B (`proposals_B`), after the
 * report of a full F run: the paper's proved results are proposed the same way. The decisions are
 * the owner's in every mode (auto mode too). `--from-stage V1|V1.5|F1` sets round A aside (it is
 * held again after the new plan); a run already past F1 when round A was introduced is not sent
 * back to it.
 *
 * REWINDS REVISE, THEY NEVER REBUILD — AND THE ORCHESTRATOR APPROVES THEM (2026-09-23). An
 * F-stage finding that a paper
 * statement is wrong or admits several readings (an F2.5–F4 proof-review escalation) comes back
 * from the F runner as a pending receipt (`state.verify.cross_stage_rewind`). The runner presents it
 * and halts in every mode (auto mode too). `--resume` approves it: a V1 patch round
 * (`cross_stage_rewind.ts`) — fixer → V1 → V1.5 (only the changed nodes are graded) → F1 re-plans.
 * `--resume --reject-rewind "<reason>"` rejects it: recorded, and the F stages continue; the same
 * finding on the same node is a note from then on. A finding may name an assumption or definition
 * (the directive goes to the statements using it), and one receipt carries every paper-statement
 * finding of one review pass: one decision, one round. `--from-stage V1` keeps the transcription,
 * the patch file and the carried V1.5 verdicts while the source is unchanged (`v1EntryMode`);
 * `--fresh-review` makes the next V1.5 grade every node. Either re-entry VOIDS the pending owner
 * receipts (a weakened repair, a proposed rewind, a patch cap): they were derived from the verdicts
 * the redone review replaces, so they are set aside and never presented again (`reentry_void.ts`).
 *
 * CAPS HALT, THEY NEVER FAIL (2026-09-23). A patch round due while its counter (`patch_rounds` for
 * error rounds, `refinement_rounds` for clarify rewinds and minimality-only rounds) is at its cap
 * records `state.verify.cap_reached` and halts in every mode: `--resume --clear-patch-cap` grants
 * one more window, `--resume --accept-cap` ends the loop — to F1 with the repair kept at a V1.5
 * refinement cap, else to V6 (`caps.ts`).
 *
 * REPAIRS NEVER WEAKEN THE CONTRIBUTION (2026-09-23). When no repair keeps a result at full strength
 * (the fixer says so, or the referee grades a repair `weakens_contribution`), the strongest true
 * version is a SUGGESTION. On an intermediate result (anything but a main theorem: a `theorem` /
 * `corollary` of the core or a fixer `key_results` entry) the runner applies it at once and V1.5
 * confirms it (reported repaired, "narrowed: …"). On a main theorem it is recorded (`state.verify.weakening_repair`) and the run halts for
 * the paper's owner in every mode: `--resume --accept-repair` applies it (V1.5 confirms; reported
 * repaired, contribution narrowed), `--resume --decline-repair "<reason>"` reports the result refuted
 * and descopes it with what rests on it (`weakening.ts`). The receipt is presented only after a V1.5
 * pass has graded each suggestion as a repair (its weakening accepted, its note graded) and nothing is
 * left for the fixer: a new receipt is marked `unconfirmed` (`confirmBeforeOwner`); a suggestion the
 * referee objects to leaves the receipt and goes back to the fixer (`weakening.ts`
 * `withdrawSuggestions`); a pass that sends other work back loops as usual (round caps apply), the
 * receipt carried. No answer to it is taken until it is presented.
 *
 * THE OWNER MAY WITHDRAW A FINDING (2026-09-24). At a weakened-repair halt and at a proposed F-stage
 * rewind, `--resume --reject-finding "<reading>"` says the finding is a misreading: the printed
 * statement stands, the reading is pinned into the core (`ass:pin-owner-<n>`, binding for the F
 * stages), the finding may not be raised again on that node, and the report lists it as withdrawn
 * (`owner_rulings.ts`). V1.5 then grades what changed and F1 plans the core with the pin.
 */
import { existsSync } from "node:fs";
import { mkdir, readFile, rename, rm } from "node:fs/promises";
import path from "node:path";
import { appendPipelineLog } from "../log.js";
import { FROM_STAGE_USAGE, fromStageRefusal, resolveStageHaltId, STAGE_HALT_IDS, STAGE_HALT_ID_TO_INTERNAL, STOP_AFTER_USAGE, STAGE_ORDER, stopAfterRefusal, type StageHaltId } from "../constants.js";
import { leanModulePrefix, statePath, verifyRunDir } from "../paths.js";
import { removePapersBarrelImport } from "../toolkit/barrels.js";
import { createVerifyInitialState, loadState, saveState } from "../state.js";
import { claudeRoles } from "../claude_roles.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { runCodex } from "../shared/codex.js";
import { withTokenLedger } from "../token_usage.js";
import type { Stage, StateJson } from "../types.js";
import { FIXER_HISTORY_FILE } from "./fixer_history.js";
import { prepareSource as realPrepareSource } from "./source_bundle.js";
import { runStageV1, v1EntryMode } from "./stage_v1.js";
import { applyPendingRewind, presentPendingRewind, recordProofReviewRewind, rejectPendingRewind } from "./cross_stage_rewind.js";
import { acceptCapLosses, acceptV1_5AtCap, runStageV1_5 } from "./stage_v1_5.js";
import { capMessage, capScope, clearCap, countRound } from "./caps.js";
import { CAP_GATE_FLAGS, clearCapGate, resumeBlock } from "../cap_gates.js";
import { resetForNewCore } from "../formalization/loop_limits.js";
import { contractCheckpointGuidance, patchCapGuidance, renderCheckpointGuidance, rewindApprovalGuidance, weakeningRepairGuidance } from "../checkpoint_playbook.js";
import { DECLINE_NODES, haltAnswerConflict, haltAnswerFlags, restateAllPatches, closeReceipt, ruleOnReceipt, undecidedItems, weakeningMessage } from "./weakening.js";
import { addOwnerConditions, assertOwnerTex, convertToUmbrella, parseEditReading, parseUmbrella, parseRejectFinding, rejectAppliedFindings, rejectRewindFinding, rejectWeakeningFinding, reviseOwnerReadings, syncOwnerRulingsOnDisk, transcribedNodeIds } from "./owner_rulings.js";
import { runStageV6 } from "./stage_v6_report.js";
import { voidPendingReceipts } from "./reentry_void.js";
import { fromTranscriptLine, fromTranscriptRefusal, resetFromTranscript } from "./from_transcript.js";
import { annotateRun, withAnnotatedPaper, type AnnotateRun, type AnnotatedOutcome } from "./annotate_run.js";
import { contractBlock, renderBlock, splitRenderDefects } from "./render_check.js";
import { FragmentRouter, type RenderSite } from "./fragment_routing.js";
import { isWithdrawn, readPatchFile, readTranscribedCore, rebuildPatchedCore } from "./patches.js";
import type { CompileTex } from "./annotated_paper.js";
import { dryRunRefusal } from "./dry_run.js";
import {
  MAX_REFINEMENT_ROUNDS,
  MIN_PATCH_BACKSTOP,
  VERIFY_FILES,
  type PrepareSource,
  type VerifyStage,
  type VerifyStageArgs,
  type VerifyStageResult,
  type VerifyState,
} from "./types.js";

/** Hand-off into the F1–F5 runner. Injectable so tests drive the phase machine without
 * loading the F stages. */
export type RunFormalization = (args: {
  toolkit: ToolkitConfig;
  qid: string;
  dryRun: boolean;
  auto: boolean;
  /** Internal stage id to (re-)enter at; `undefined` = continue after `stage_completed`. */
  startStage?: Stage;
  /** Internal stage id to halt after (the F runner's `stopAfterStage`). */
  stopAfterStage?: Stage;
}) => Promise<StateJson>;

/** The toolkit promotion round after the report (scan, curate, check, write batch + checklist).
 * Injectable for tests. */
export type RunPromotion = (args: {
  toolkit: ToolkitConfig;
  qid: string;
  dryRun: boolean;
  runCodex: typeof runCodex;
  log: (msg: string) => void;
}) => Promise<import("../proposals/schema.js").ProposalRoundState>;

async function defaultRunPromotion(args: Parameters<RunPromotion>[0]): Promise<import("../proposals/schema.js").ProposalRoundState> {
  const { runRoundB } = await import("../proposals/round_b.js");
  return runRoundB(args);
}

async function defaultRunPromotionA(args: Parameters<RunPromotion>[0]): Promise<import("../proposals/schema.js").ProposalRoundState> {
  const { runRoundA } = await import("../proposals/round_a.js");
  return runRoundA(args);
}

export interface VerifyPipelineArgs {
  toolkit: ToolkitConfig;
  /** The run id (the slug). */
  qid: string;
  /** The `.tex` / dir / archive as typed on the command line (cold start only). */
  input: string;
  mainHint: string | null;
  targets: string[] | null;
  resume: boolean;
  /** `V1` | `V1.5` | `V6` reset the phase; an `F*` value hands straight to the F runner. */
  fromStage: string | null;
  /** Halt once this stage (`V1` | `V1.5` | `F*` | `V6`) completes; `--resume` continues. */
  stopAfter?: string | null;
  /** Auto mode, the default; `false` is `--debug`, which latches onto `state.debug_mode` (the run's
   *  mode is `autoMode()` below, read from the state). */
  auto: boolean;
  /** `--full-auto` (implies auto mode; latching onto `state.full_auto`): the owner's decisions take the
   *  agent's recommendations. */
  fullAuto?: boolean;
  dryRun: boolean;
  /** `--clear-gate <flag>` values (with `--resume`): each cap gate is cleared as the run is entered. */
  clearGates?: string[];
  /** `annotate` writes the annotated paper at each V1.5 pass end and owner halt (`annotate_run.ts`);
   *  `compileTex` is its compile step. Tests inject both. */
  deps?: { runCodex?: typeof runCodex; prepareSource?: PrepareSource; annotate?: AnnotateRun; compileTex?: CompileTex };
  stages?: { v1?: VerifyStage; v1_5?: VerifyStage; v6?: VerifyStage; acceptCapV1_5?: VerifyStage };
  runFormalization?: RunFormalization;
  runPromotion?: RunPromotion;
  /** Round A (after F1), injectable for tests. */
  runPromotionA?: RunPromotion;
  /** `--defer-proposals`: skip toolkit promotion round A (the cited results stay assumptions). */
  deferProposals?: boolean;
  /** `--fresh-review` (with `--from-stage V1|V1.5`): the next V1.5 grades every node afresh instead
   *  of carrying the verdicts whose basis is unchanged. */
  freshReview?: boolean;
  /** `--from-transcript` (with `--resume`): re-enter as if V1 had just completed under the current
   *  design — `core.json` is the finished transcription again, everything derived from it is
   *  archived and cleared, and the next step is a fresh V1.5 (`from_transcript.ts`). */
  fromTranscript?: boolean;
  /** `--reject-rewind "<reason>"` (with `--resume`): reject the F-stage rewind the run halted to
   *  propose; the F stages continue. */
  rejectRewind?: string | null;
  /** `--clear-patch-cap` (with `--resume`): one more window of rounds on the counter the run halted
   *  at (`state.verify.cap_reached`). */
  clearPatchCap?: boolean;
  /** DRY RUN only: nodes the synthetic sharded referee grades `error` until patched (exercises the
   *  fix-as-you-go interleave; `VerifyStageArgs.dryRunSyntheticErrors`). */
  dryRunSyntheticErrors?: readonly string[];
  /** `--accept-cap` (with `--resume`): end the patch loop at the cap (V1.5 refinement cap → F1, else V6). */
  acceptCap?: boolean;
  /** `--accept-repair [<node>,…]` (with `--resume`): the owner applies the suggested repairs that
   *  weaken the contribution (`state.verify.weakening_repair`) — every pending one (`true`), or those
   *  of the nodes named. */
  acceptRepair?: boolean | readonly string[];
  /** `--decline-repair "[<node>,…: ]<reason>"` (with `--resume`): the owner declines them; the results
   *  are reported refuted and descoped with what rests on them. */
  declineRepair?: string | null;
  /** `--redo-repair "<node>: <guidance>"` (with `--resume`; repeatable): the owner discards that
   *  node's suggested repair; the fixer repairs it again under the guidance (`ruleOnReceipt`). */
  redoRepair?: readonly string[] | null;
  /** `--reject-finding` (with `--resume`): `"<reading>"` at a weakened-repair or F-stage rewind halt —
   *  the paper's owner withdraws the finding, the printed statement stands under the owner's reading,
   *  pinned into the core; `"<node>: <reading>"` / `"<node>: bookkeeping: <condition>"` (repeatable)
   *  at ANY halt — the finding on that node is withdrawn, its applied repair removed
   *  (`owner_rulings.ts` `rejectAppliedFindings`). */
  rejectFinding?: string | readonly string[] | null;
  /** `--add-condition "<node>: <condition>"` values (`addOwnerConditions`). */
  addCondition?: readonly string[] | null;
  /** `--edit-reading "<id>: <new text>"` / `--remove-reading <id>` values (`reviseOwnerReadings`). */
  editReading?: readonly string[] | null;
  removeReading?: readonly string[] | null;
  /** `--umbrella <node>` / `"<node>: <title>"` values (`convertToUmbrella`). */
  umbrella?: readonly string[] | null;
}

/** Whether the cursor is before F1: the F runner has never been entered, so the hand-off
 * starts it at F1 rather than "the next stage". */
function isPreF(stage: Stage): boolean {
  return STAGE_ORDER.indexOf(stage) < STAGE_ORDER.indexOf("1");
}

/** Whether F5 has completed (cursor at `"5"` or `"V6"`). */
function fDone(stage: Stage): boolean {
  return STAGE_ORDER.indexOf(stage) >= STAGE_ORDER.indexOf("5");
}

/** Repeats of a ruled-out F-stage finding one invocation turns into notes before it halts (the F
 * stages kept re-raising it: the orchestrator should look). */
const MAX_REPEATS_PER_INVOCATION = 2;

/** Loop guard: the phase machine is monotone apart from the bounded V1.5→V1 loops. Each revise
 * round is two steps (V1 then V1.5); a patch round at most four (an F-stage rewind: F, V1, V1.5,
 * the hand-off), budgeted at five; a noted repeat one F re-entry; on top: the first V1 + V1.5, the
 * hand-off, F, V6, done. Error rounds are bounded by the core's backstop (`caps.ts`), which may
 * exceed `MIN_PATCH_BACKSTOP`: every error round past it spent in this invocation extends the
 * guard by five steps. */
const MAX_PHASE_STEPS =
  2 * (MIN_PATCH_BACKSTOP + 1) + 5 * (MIN_PATCH_BACKSTOP + MAX_REFINEMENT_ROUNDS) + MAX_REPEATS_PER_INVOCATION + 14;

async function defaultRunFormalization(
  args: Parameters<RunFormalization>[0],
): Promise<StateJson> {
  const { runPipeline } = await import("../pipeline.js");
  const { dryRunStageHandler, liveStageHandler } = await import("../pipeline_stages.js");
  return runPipeline(
    {
      repoRoot: args.toolkit.toolkitRoot,
      toolkit: args.toolkit,
      qid: args.qid,
      dryRun: args.dryRun,
      resume: true,
      auto: args.auto,
    },
    args.dryRun ? dryRunStageHandler : liveStageHandler,
    { startStage: args.startStage, stopAfterStage: args.stopAfterStage },
  );
}

/** The report's verdict as a terminal phase: a refutation recorded by any stage makes the run
 * `failed`, otherwise `done`. A refutation repaired by a confirmed minimal patch does not fail the
 * run (the corrected statement was formalized), nor does one descoped as an unfixable side result
 * (reported; no key result rests on it); any other refutation does. An ambiguity the paper leaves
 * open (V1.5 `unresolved`, not a descoping note) fails it too. */
function reportTerminalPhase(verify: VerifyState): "done" | "failed" {
  return verify.findings.some(
    (f) =>
      (f.kind === "refuted" && !f.patch?.confirmed && !f.descoped) ||
      (f.kind === "unresolved" && f.stage === "V1.5" && !f.descoped),
  )
    ? "failed"
    : "done";
}

function verifyBlock(state: StateJson, stateFile: string): VerifyState {
  if (!state.verify) {
    throw new Error(
      `${stateFile} has no \`verify\` block — it was not seeded by \`paperformalizer verify\`.`,
    );
  }
  return state.verify;
}

async function loadVerifyState(repoRoot: string, qid: string): Promise<StateJson> {
  const stateFile = statePath(repoRoot, qid);
  const state = await loadState(repoRoot, qid);
  const verify = verifyBlock(state, stateFile);
  // A run already past F1 when round A was introduced is not sent back to it.
  if (!verify.promotion_a && !isPreF(state.stage_completed) && state.stage_completed !== "1") {
    verify.promotion_a = { status: "deferred", reason: "the run was past F1 when round A was introduced", batch_path: null, checklist_path: null, promoted: [] };
  }
  return state;
}

/** The stage `PAPERFORMALIZER_STOP_AFTER` names, as `--stop-after` takes it (a bare F stage number
 * too); null when unset. A value that is no stage, or one `--stop-after` refuses, is refused here. */
function envStopAfter(): StageHaltId | null {
  const raw = process.env.PAPERFORMALIZER_STOP_AFTER?.trim();
  if (!raw) return null;
  const id = resolveStageHaltId(raw) ?? resolveStageHaltId(`F${raw}`);
  if (!id) throw new Error(`PAPERFORMALIZER_STOP_AFTER=${raw} is not a stage (expected one of ${STOP_AFTER_USAGE}).`);
  const refusal = stopAfterRefusal(id);
  if (refusal) throw new Error(refusal.replace("--stop-after ", () => "PAPERFORMALIZER_STOP_AFTER="));
  return id;
}

/**
 * Drive a verify run to its next stopping point: `done` / `failed`, an F-stage
 * checkpoint, or a V-stage checkpoint. Returns the final `state.verify`.
 */
export async function runVerifyPipeline(given: VerifyPipelineArgs): Promise<VerifyState> {
  // `PAPERFORMALIZER_STOP_AFTER` is `--stop-after` (the flag wins), for every stage it takes.
  // Resolved here, once: the F runner takes the stage it is passed and reads no variable. An invalid
  // value is refused even under the flag — it would be the next invocation's stop.
  const env = envStopAfter();
  const args: VerifyPipelineArgs = given.stopAfter || !env ? given : { ...given, stopAfter: env };
  const { toolkit, qid, dryRun } = args;
  const repoRoot = toolkit.toolkitRoot;
  const runDir = verifyRunDir(repoRoot, qid);
  const stateFile = statePath(repoRoot, qid);
  if (args.stopAfter) {
    const refusal = stopAfterRefusal(args.stopAfter as StageHaltId);
    if (refusal) throw new Error(refusal);
  }
  if (args.fromStage) {
    // Before any state is touched: the re-entry below voids a pending promotion round.
    const refusal = fromStageRefusal(args.fromStage as StageHaltId);
    if (refusal) throw new Error(refusal);
  }
  if (args.fromStage && args.stopAfter && STAGE_HALT_IDS.indexOf(args.stopAfter as StageHaltId) < STAGE_HALT_IDS.indexOf(args.fromStage as StageHaltId)) {
    // Also for the variable: it used to save the re-entry, halt before F1 and lose the entry stage.
    throw new Error(`${given.stopAfter ? "--stop-after " : "PAPERFORMALIZER_STOP_AFTER="}${args.stopAfter} precedes --from-stage ${args.fromStage}; nothing would run.`);
  }
  if (args.freshReview && args.fromStage !== "V1" && args.fromStage !== "V1.5") {
    throw new Error("--fresh-review re-grades every node at the next V1.5; it needs --from-stage V1 or V1.5.");
  }
  // VALIDATE, THEN MUTATE: nothing of the run is changed or saved before every flag of the
  // invocation has been checked. What needs no state is checked here; what needs the run's state,
  // below, before the first ruling is applied (`checked against the state`).
  {
    const answers = haltAnswerFlags(args);
    if (answers.length > 0 && (!args.resume || args.fromStage)) throw new Error(`${answers.join(", ")} answers a halt: it needs --resume (and no --from-stage).`);
    const conflict = haltAnswerConflict(args);
    if (conflict) throw new Error(conflict);
    if (args.clearGates?.length && !args.resume) throw new Error("--clear-gate requires --resume.");
    for (const name of args.clearGates ?? []) {
      if (!CAP_GATE_FLAGS.includes(name)) throw new Error(`--clear-gate: unknown gate '${name}'. Known gates: ${CAP_GATE_FLAGS.join(", ")}`);
    }
  }
  if (args.fromTranscript) {
    if (!args.resume) throw new Error("--from-transcript re-enters an existing run: it needs --resume.");
    if (args.fromStage || args.freshReview) throw new Error("--from-transcript already re-enters at a fresh V1.5; it does not combine with --from-stage or --fresh-review.");
    if (haltAnswerFlags(args).length > 0) throw new Error("--from-transcript clears every halt; it does not combine with an answer to one.");
  }
  const log = (msg: string): void => console.log(`[verify] ${msg}`);

  const prepareSource = args.deps?.prepareSource ?? realPrepareSource;
  const codex = args.deps?.runCodex ?? runCodex;
  const stages = {
    v1: args.stages?.v1 ?? runStageV1,
    v1_5: args.stages?.v1_5 ?? runStageV1_5,
    v6: args.stages?.v6 ?? runStageV6,
    acceptCapV1_5: args.stages?.acceptCapV1_5 ?? acceptV1_5AtCap,
  };
  const runFormalization = args.runFormalization ?? defaultRunFormalization;
  const runPromotion = args.runPromotion ?? defaultRunPromotion;
  const runPromotionA = args.runPromotionA ?? defaultRunPromotionA;
  const deferRoundA = (verify: VerifyState): void => {
    verify.promotion_a = { status: "deferred", reason: "--defer-proposals", batch_path: null, checklist_path: null, promoted: [] };
    log("promotion A: deferred (--defer-proposals) — the cited results stay assumptions of the paper.");
  };

  let state: StateJson;
  /** Clear cap gates once every flag has been checked and its rulings have applied. Page requests
   * stay open until explicitly closed: resuming the run does not answer them. */
  let entrySettled = false;
  const settleEntry = async (): Promise<void> => {
    if (entrySettled || !args.resume) return;
    entrySettled = true;
    if (args.clearGates?.length) {
      for (const name of args.clearGates) {
        clearCapGate(state.flags, name);
        log(`cleared cap gate flags.${name}`);
      }
      // (a gate cleared is a ruling on the F1.5 halt: a blocked F1 recorded before it is answered too)
      if (args.fromStage) state.flags.f1_blocked = null;
      await saveState(repoRoot, qid, state);
    }
  };
  /** The entry flags checked against the run's state, before the entry changes anything: an old
   * patch file, a `--from-transcript` with no transcription to restart from, and an F entry the F
   * runner would refuse (no accepted core, a core edited since, a dry-run state) — it refused it
   * after the phase was set and round B set aside, under a cursor still at V6, and the page read
   * the run as done. */
  const checkEntry = async (): Promise<void> => {
    await readPatchFile(runDir);
    if (args.fromTranscript) {
      const checked = await fromTranscriptRefusal(runDir, state);
      if (checked.refusal !== null) throw new Error(checked.refusal);
    }
    // (… the natural entry too, when a plain resume in the Lean stages clears a gate: the gate is
    // settled before the F runner checks that entry)
    const v = state.verify;
    const natural = !args.fromStage && args.clearGates?.length && haltAnswerFlags(args).length === 0 && v?.phase === "formalization" &&
      v.cross_stage_rewind?.status !== "pending" && !v.cap_reached && v.weakening_repair?.status !== "pending"
      ? STAGE_ORDER[STAGE_ORDER.indexOf(state.stage_completed as (typeof STAGE_ORDER)[number]) + 1]
      : undefined;
    const fEntry = args.fromStage?.startsWith("F") ? STAGE_HALT_ID_TO_INTERNAL[args.fromStage as StageHaltId] : natural && /^\d/.test(natural) ? (natural as Stage) : undefined;
    if (fEntry && args.fromStage) {
      // … or behind a cap gate this invocation does not clear: it rewound the cursor, then refused.
      const flags = structuredClone(state.flags);
      for (const name of args.clearGates ?? []) clearCapGate(flags, name);
      const gate = resumeBlock({ ...flags, missing_architecture: false });
      if (gate) throw new Error(`--from-stage ${args.fromStage} is refused, nothing changed: ${gate}`);
    }
    if (fEntry && !args.runFormalization) {
      const { assertFStageEntryCoherence } = await import("../pipeline.js");
      await assertFStageEntryCoherence({ repoRoot, toolkit, qid, dryRun, resume: true, auto: args.auto }, state, fEntry);
    }
  };
  const stateExists = existsSync(stateFile);
  if (args.resume) {
    if (!stateExists) {
      throw new Error(
        `--resume: no verify run found at ${stateFile}. Start it without --resume.`,
      );
    }
    state = await loadVerifyState(repoRoot, qid);
    const refusal = dryRunRefusal(state, dryRun, { fromStage: args.fromStage });
    if (refusal) throw new Error(refusal);
    log(`resuming ${qid} in phase ${verifyBlock(state, stateFile).phase}`);
    // (`--clear-gate` is settled once every flag has been checked against the state: `settleEntry`.)
    await checkEntry();
    if (haltAnswerFlags(args).length === 0) await settleEntry();
  } else if (stateExists) {
    if (!args.fromStage) {
      throw new Error(
        `A verify run already exists at ${runDir}. Continue it with --resume, re-enter a ` +
          `stage with --from-stage <${FROM_STAGE_USAGE}>, or remove the run directory to start over.`,
      );
    }
    state = await loadVerifyState(repoRoot, qid);
    const refusal = dryRunRefusal(state, dryRun, { fromStage: args.fromStage });
    if (refusal) throw new Error(refusal);
    await checkEntry();
    log(`re-entering ${qid} at ${args.fromStage}`);
  } else {
    for (const sub of ["discovery", "formalization", "logs"]) {
      await mkdir(path.join(runDir, sub), { recursive: true });
    }
    log(`preparing source from ${args.input}`);
    const prepared = await prepareSource({
      input: args.input,
      sourceDir: path.join(runDir, VERIFY_FILES.sourceDir),
      mainHint: args.mainHint,
    });
    if (prepared.note) log(prepared.note);
    state = createVerifyInitialState(qid, {
      phase: "init",
      source: { input: args.input, main_file: prepared.mainFile, sha256: prepared.sha256 },
      targets: args.targets,
      core_sha256: null,
      v1_rounds: 0,
      v1_5_rounds: 0,
      findings: [],
      report_path: null,
      ...(dryRun ? { dry_run: true } : {}),
    }, toolkit.papersLib);
    await saveState(repoRoot, qid, state);
    log(`seeded ${stateFile} (main=${prepared.mainFile}, ${prepared.inputKind})`);
  }
  // `--full-auto` latches onto the state: the owner's decisions take the agent's recommendations from here on.
  if (args.fullAuto && state.full_auto !== true) { state.full_auto = true; state.debug_mode = false; await saveState(repoRoot, qid, state); }
  // `--debug` (`auto: false`) latches too: auto mode stays off for the run. A full-auto run is never in debug mode.
  if (args.auto === false && state.debug_mode !== true) {
    if (state.full_auto === true) log("--debug ignored: this run is in full auto, which it keeps across resumes");
    else { state.debug_mode = true; await saveState(repoRoot, qid, state); }
  }
  const fullAuto = (): boolean => state.full_auto === true;
  const autoMode = (): boolean => fullAuto() || state.debug_mode !== true;
  if (state.auto_mode !== autoMode()) { state.auto_mode = autoMode(); await saveState(repoRoot, qid, state); }
  if (stateExists && args.targets !== null && args.fromStage === "V1") {
    // A new transcription takes the new scope (`stage_v1.ts` `computeScope` reads `verify.targets`).
    verifyBlock(state, stateFile).targets = args.targets;
    log(`--targets: the new transcription covers ${args.targets.join(", ")} and what they cite`);
    await saveState(repoRoot, qid, state);
  }
  // An owner ruling is recorded once, as its `patches.json` reading: what derives from it (ledger
  // stamp, ruled-out entry, withdrawal note) is re-synced before anything reads it.
  if (stateExists && state.verify) {
    const synced = await syncOwnerRulingsOnDisk(runDir, state);
    for (const line of synced) log(`owner rulings: ${line}`);
    if (synced.length > 0) await saveState(repoRoot, qid, state);
  }

  // The CLI that runs the claude roles is the run's: chosen by its first live process, recorded,
  // and kept by a resume (`claude_roles.ts`) — decided and logged here, ahead of the first model call.
  if (!dryRun) {
    const runner = claudeRoles(state.claude_roles).runner;
    if (state.claude_roles !== runner) {
      state.claude_roles = runner;
      await saveState(repoRoot, qid, state);
    }
  }

  const save = async (): Promise<void> => {
    await saveState(repoRoot, qid, state);
  };

  /** The paper is re-formalized or its report re-run: a pending promotion round is set aside and
   *  the record dropped, so the new report is proposed afresh (moves an applied round made stay in
   *  the toolkit and the ledger). */
  const voidPromotion = async (reason: string, round: "A" | "B" = "B", opts: { keepDecided?: boolean } = {}): Promise<void> => {
    const verify = verifyBlock(state, stateFile);
    const rec = round === "A" ? verify.promotion_a : verify.promotion;
    if (!rec) return;
    // A round that has been held and settled (applied, deferred, or nothing to propose) is not held
    // again because the run is re-entered: the owner decided it once. Only a round still waiting
    // for decisions is set aside, since what it proposed may no longer match the paper's Lean.
    // (`propose <slug> --reopen-deferred` re-proposes deferred entries on request.)
    if (opts.keepDecided && rec.status !== "pending_user") {
      log(`promotion ${round}: already held (${rec.status}); it stands and is not held again`);
      return;
    }
    if (rec.status === "pending_user") {
      const { voidRoundB } = await import("../proposals/round_b.js");
      await voidRoundB({ toolkit, qid, rec, reason, dryRun, log, round });
    }
    if (round === "A") delete verify.promotion_a;
    else delete verify.promotion;
  };
  const voidForNewCore = async (): Promise<void> => {
    // A new core is a new formalization attempt, however it comes about (a re-entry at V1 or V1.5,
    // a condition added, a reading revised, an umbrella, a finding withdrawn on a node): what the
    // F stages recorded of the old one goes — their budgets, a blocked F1, a missing-architecture
    // block (F2 raises it again if the new scaffold still lacks the declaration).
    resetForNewCore(state);
    if (!dryRun) {
      const r = await removePapersBarrelImport(toolkit, leanModulePrefix(state.lean_subdir));
      if (r.changed) log(`removed ${leanModulePrefix(state.lean_subdir)} from ${r.path} until its F5 completes again`);
    }
    await voidPromotion("the paper's core is being revised", "B", { keepDecided: args.fromStage !== "V1" });
    // a new transcription (`--from-stage V1`) may cite other results: only then is it held again
    await voidPromotion("the paper's core is being revised", "A", { keepDecided: args.fromStage !== "V1" });
  };

  /**
   * The repair texts a render printed verbatim because they do not compile go back to the fixer in
   * one scoped round (`weakening.ts` `restateAllPatches`; the phase becomes `init`). A core accepted
   * past V1.5 is being revised (`voidForNewCore`). True when the round was opened.
   */
  const restateAll = async (when: string, compile: Parameters<typeof restateAllPatches>[2]): Promise<boolean> => {
    const verify = verifyBlock(state, stateFile);
    const accepted = verify.phase === "v1_5" || verify.phase === "formalization";
    const lines = await restateAllPatches(runDir, state, compile);
    for (const line of lines) log(`${when}: ${line}`);
    if (lines.length === 0) return false;
    if (accepted) await voidForNewCore();
    await save();
    return true;
  };

  /** A pending F-stage rewind, or a pending proof-review escalation on a paper statement that has
   * no receipt yet (recorded here, so a resume at F2.5 routes it before re-entering the loop). */
  const rewindPending = (): boolean =>
    recordProofReviewRewind(state) || verifyBlock(state, stateFile).cross_stage_rewind?.status === "pending";

  /** The annotated paper for the run as it stands (never throws). The owner reviews THIS at every
   * halt and after every V1.5 pass. */
  const annotate = (when: string): Promise<AnnotatedOutcome> =>
    (args.deps?.annotate ?? annotateRun)({
      runDir,
      qid,
      state,
      when,
      compile: args.deps?.compileTex,
      log,
    });
  /** The annotated paper the V1.5 pass that just ended wrote (reused by the halt it ends in). */
  let passAnnotation: AnnotatedOutcome | null = null;
  /** Read through a call: set inside `runStage`, which the compiler's narrowing does not see. */
  const lastPass = (): AnnotatedOutcome | null => passAnnotation;

  /** The invocation answers a halt (an owner's or the orchestrator's flag): its own flow opens any
   * fixer round, a render never does. */
  const answering = haltAnswerFlags(args).length > 0;
  /** Failing model fragments go back to their producers (`fragment_routing.ts`). */
  const router = new FragmentRouter({
    state: () => state,
    runDir,
    restate: (when, compile) => restateAll(when, compile),
    reopenAccepted: () => voidForNewCore(),
    answering,
  });

  /**
   * The two render checkpoints (user decision 2026-09-25: rendering fallbacks are a checkpoint, never
   * silent; user rule 2026-09-25: fix the order and the classification). A RENDERER defect of the
   * render behind `a` (`render_check.ts` `splitRenderDefects`: a block the renderer itself could not
   * set, a pdflatex error) records `state.verify.render_checkpoint` (kind `renderer`) and halts —
   * before any owner decision and F1, in every mode; the renderer is fixed
   * and `--resume` renders again. A MODEL-TEXT defect (a model fragment failing its compile check) is
   * routed to its producer (`FragmentRouter.gate` at `site`): the run continues into that producer's
   * pass, the halt is presented with the fragments listed, or — the model could not write it within
   * its retries — the CONTRACT checkpoint halts (kind `contract`; `--resume` routes the fragments
   * again). Returns `halt`, `continue` (nothing is presented: the run goes on) or `present`. Clears a
   * checkpoint on file when a render comes back clean. An outcome with nothing written never blocks.
   */
  const renderGate = async (a: AnnotatedOutcome | null, site: RenderSite): Promise<"halt" | "continue" | "present"> => {
    const verify = verifyBlock(state, stateFile);
    if (!a?.render) return "present";
    const { renderer, fragments } = splitRenderDefects(a.render);
    const block = renderBlock(renderer);
    if (block) {
      verify.render_checkpoint = { kind: "renderer", when: a.line, defects: renderer, at: new Date().toISOString() };
      await save();
      log(
        `render checkpoint: ${block}\n` +
          (fragments.length > 0 ? `  (and ${fragments.length} model-written fragment(s) that do not compile, routed to their producers once the renderer is fixed)\n` : "") +
          `  The annotated paper (written anyway): ${a.line}\n` +
          `  A text from the run's record (transcription, reading, patch) is corrected there; a renderer defect is fixed with a test and recorded in pipeline_issues.md (paperformalizer SKILL §'When the pipeline itself fails'). Then continue with:\n` +
          `    paperformalizer verify ${args.input} --resume   (renders the annotated paper again; the run continues where it stopped once it is clean)\n` +
          `  (with the --toolkit / --slug / --dry-run the run was started with; \`paperformalizer lint-annotated <slug>\` re-checks a tree written by \`paperformalizer annotate <slug>\`)`,
      );
      log(renderCheckpointGuidance(autoMode()));
      return "halt";
    }
    // (Also with no fragment in this render: one routed earlier may still wait for its producer's pass.)
    const g = await router.gate(fragments, site);
    for (const line of g.lines) log(`render check: ${line}`);
    if (g.verdict === "contract") {
      verify.render_checkpoint = { kind: "contract", when: a.line, defects: g.stuck, at: new Date().toISOString() };
      await save();
      log(
        `contract checkpoint: ${contractBlock(g.stuck)}\n` +
          `  The annotated paper (written anyway, these printed verbatim): ${a.line}\n` +
          `  Continue with:\n` +
          `    paperformalizer verify ${args.input} --resume   (routes the fragments to their producers again; the run continues where it stopped once they compile)\n` +
          `  (with the --toolkit / --slug / --dry-run the run was started with)`,
      );
      log(contractCheckpointGuidance(autoMode()));
      return "halt";
    }
    if (verify.render_checkpoint) {
      log(`${verify.render_checkpoint.kind === "contract" ? "contract" : "render"} checkpoint cleared: no renderer defect${g.pending.length > 0 ? `; ${g.pending.length} model fragment(s) routed to their producers` : ", no model fragment that fails to compile"}.`);
      verify.render_checkpoint = null;
    }
    await save();
    if (g.verdict === "present" && g.pending.length > 0) log(`render check: ${g.pending.length} model-written fragment(s) fail the compile check and are printed verbatim (a too-wide display shrunk) in the paper presented below — routed to their producers, whose next pass (after this halt is answered) writes them again:\n${g.pending.map((d) => `    ${d.node ?? "(file)"} — ${d.block}: ${d.fragment.error}`).join("\n")}`);
    return g.verdict === "continue" ? "continue" : "present";
  };
  /** The checkpoints on an annotated paper (`renderGate`): `halt`, `continue` (the render routed
   * model fragments and the run goes on into their producers' passes; nothing is presented) or
   * `present`. */
  const annotationGate = async (a: AnnotatedOutcome | null, site: RenderSite): Promise<"halt" | "continue" | "present"> => {
    return renderGate(a, site);
  };
  /** Whether the checkpoints on an annotated paper halt the run. */
  const annotationHalt = async (a: AnnotatedOutcome | null, site: RenderSite): Promise<boolean> => (await annotationGate(a, site)) === "halt";

  /** The halt at a patch cap: the annotated paper, the receipt, and what the orchestrator weighs. */
  const haltAtCap = async (verify: VerifyState, annotated: AnnotatedOutcome | null = null): Promise<VerifyState> => {
    const a = annotated ?? (await annotate("patch cap halt"));
    if (await annotationHalt(a, "decision")) return verify;
    log(withAnnotatedPaper(capMessage(verify.cap_reached!, args.input, { rewind: verify.cross_stage_rewind?.status === "pending" }), a));
    log(patchCapGuidance(autoMode()));
    return verify;
  };

  /** The halt on suggested repairs that weaken the contribution: the annotated paper, the receipt,
   * and whose call it is. Null: the render routed model fragments a pass reachable from here writes
   * again (the symbol table, the fixer's texts) — nothing is presented, the caller runs on. */
  const haltAtWeakening = async (verify: VerifyState, annotated: AnnotatedOutcome | null = null): Promise<VerifyState | null> => {
    const a = annotated ?? (await annotate("weakened-repair halt"));
    const gate = await annotationGate(a, "weakening");
    if (gate === "halt") return verify;
    if (gate === "continue") {
      log("the weakened-repair halt is presented after the pass that writes the routed texts again.");
      return null;
    }
    log(withAnnotatedPaper(weakeningMessage(verify.weakening_repair!, args.input, verify.paper_errors), a));
    log(weakeningRepairGuidance(autoMode(), fullAuto()));
    return verify;
  };

  /** A receipt the fixer's round just wrote is not presented yet: it is marked `unconfirmed` and a
   * V1.5 pass grades each suggestion as a repair (and the round's other changes); that pass presents
   * it once nothing is left for the fixer. Returns whether the pass comes first (phase `v1`,
   * `core.json` rebuilt). */
  const confirmBeforeOwner = async (verify: VerifyState): Promise<boolean> => {
    const rec = verify.weakening_repair;
    if (rec?.status !== "pending") return false;
    verify.weakening_repair = { ...rec, unconfirmed: true };
    log(`the owner's receipt (${rec.items.map((i) => i.node).join(", ")}) waits for the V1.5 pass that grades its suggestions first.`);
    await rebuildPatchedCore(runDir, { detectHandEdits: false }).catch(() => undefined); // V1.5 rebuilds it and reports a failure
    verify.phase = "v1";
    state.stage_completed = "V1";
    await save();
    return true;
  };

  /** A proposed F-stage rewind's message, with the annotated paper named before the choices; null
   * when the render checkpoint halted first (the receipt is then NOT presented, so a later
   * `--resume` shows it rather than approving it unseen). */
  const presentRewindMessage = async (message: string): Promise<string | null> => {
    const a = await annotate("rewind proposal halt");
    if (await annotationHalt(a, "decision")) {
      const rec = verifyBlock(state, stateFile).cross_stage_rewind;
      if (rec) verifyBlock(state, stateFile).cross_stage_rewind = { ...rec, presented: false };
      await save();
      return null;
    }
    return withAnnotatedPaper(message, a);
  };

  let repeatsNoted = 0;
  /**
   * A pending F-stage rewind receipt. `routed`: approved and applied (phase `init`). `continue`:
   * the F stages go on (a noted repeat of a ruled-out finding, or — at entry — a refused
   * proof-review receipt, which lets F2.5 re-enter as before). `halt`: the run stops here (a
   * receipt presented for approval, a patch cap, a refused F1.5 route). A plain `--resume` at
   * formalization entry approves a receipt an earlier invocation presented; nothing else does.
   */
  /** Whether this invocation approves a rewind an earlier one presented: a plain `--resume` (no
   * `--from-stage`, no answer to any halt), or `--clear-patch-cap` on the cap its already approved
   * round ran into. A resume that carried any other ruling approves nothing: the core it changed
   * is reviewed, and the proposal is shown again. */
  const approvesRewind = ((answers) =>
    Boolean(args.resume) && !args.fromStage && (answers.length === 0 || (answers.length === 1 && answers[0] === "--clear-patch-cap")))(haltAnswerFlags(args));
  const handleRewind = async (atEntry: boolean): Promise<"routed" | "continue" | "halt"> => {
    const verify = verifyBlock(state, stateFile);
    const rec = verify.cross_stage_rewind!;
    const refusedFollowup = (): "continue" | "halt" => {
      const route = verifyBlock(state, stateFile).cross_stage_rewind?.route;
      if (atEntry && (route === "fix-source" || route === "unclear")) return "continue";
      log("F stages halted on the reviewer's finding (recorded for the report) — inspect the run, then continue with --resume.");
      return "halt";
    };
    if (rec.presented) {
      if (!(atEntry && approvesRewind)) {
        // Only a PLAIN `--resume` approves (`approvesRewind`); any other entry — a re-entry, a resume
        // that carried another ruling and came back here through V1.5 — shows the proposal again.
        const again = await presentPendingRewind({ runDir, state, input: args.input });
        await save();
        const shown = again.kind === "present" ? await presentRewindMessage(again.message) : again.message;
        if (shown === null) return "halt";
        log(shown);
        if (again.kind === "present") log(rewindApprovalGuidance(autoMode()));
        return again.kind === "repeat" ? "continue" : again.kind === "refused" ? refusedFollowup() : "halt";
      }
      const n = rec.targets?.filter((t) => t.status !== "refused" && t.status !== "repeat").length ?? 1;
      log(`--resume: the orchestrator approves the ${rec.stage} ${rec.route} rewind${n > 1 ? ` (${n} findings, one round)` : ""} on ${rec.nodes?.join(", ") || rec.target || "?"}.`);
      const out = await applyPendingRewind({ runDir, state });
      log(out.message);
      if (out.applied) {
        await voidForNewCore();
        log(`re-entering V1 in patch mode — the fixer answers ${out.nodes.join(", ")}; V1.5 then grades only what changed.`);
        await save();
        return "routed";
      }
      await save();
      if (out.capped) {
        await haltAtCap(verify);
        return "halt";
      }
      return refusedFollowup();
    }
    const p = await presentPendingRewind({ runDir, state, input: args.input });
    await save();
    const shown = p.kind === "present" ? await presentRewindMessage(p.message) : p.message;
    if (shown === null) return "halt";
    log(shown);
    if (p.kind === "repeat") {
      repeatsNoted += 1;
      if (repeatsNoted > MAX_REPEATS_PER_INVOCATION) {
        log(`the F stages re-raised ruled-out findings ${repeatsNoted} times in this invocation — halting for the orchestrator; continue with --resume.`);
        return "halt";
      }
      return "continue";
    }
    if (p.kind === "refused") return refusedFollowup();
    log(rewindApprovalGuidance(autoMode()));
    return "halt";
  };

  // `--from-transcript`: the run restarts from its finished transcription under the current design.
  // Everything derived from it (patches, verdicts, ledger, receipts, F-stage artefacts) is archived
  // and cleared; owner rulings stay; the phase is `v1`, so the next step is a fresh V1.5.
  if (args.fromTranscript) {
    const summary = await resetFromTranscript({
      runDir,
      state,
      papersLib: toolkit.papersLib,
      voidRounds: () => voidForNewCore(),
    });
    await save();
    log(fromTranscriptLine(summary, runDir));
  }

  // A patch file in an older format is rewritten first, never read in it
  // (`patches.ts` `readPatchFile` refuses it).
  await readPatchFile(runDir);

  // `--from-stage`: V values rewind the V-phase cursor; an F value hands straight
  // to the F runner at that stage.
  let fStartOverride: Stage | undefined;
  // Re-plans this invocation asked of F1 for a plan round A could not read.
  let planReplans = 0;
  const MAX_PLAN_REPLANS = 2;
  if (args.fromStage) {
    const verify = verifyBlock(state, stateFile);
    // A V1/V1.5 re-entry is the operator ACTING on the revise cap (they read the review and
    // fixed the core or the source), so it clears the round counter; every other entry leaves
    // it, and V1.5's cap (`MAX_REVISE_ROUNDS_PER_NODE`) then still holds on a plain `--resume`.
    if (args.fromStage === "V1" || args.fromStage === "V1.5") {
      // The review is redone: a pending owner receipt (weakened repair, F-stage rewind, patch cap)
      // was derived from the verdicts it replaces — set aside, never presented again. Owner
      // decisions already taken stay binding (`reentry_void.ts`).
      await voidPendingReceipts({ runDir, state, reason: `--from-stage ${args.fromStage}${args.freshReview ? " --fresh-review" : ""}`, log });
      verify.v1_5_rounds = 0;
      verify.v1_5_rounds_by_node = {};
      verify.suggestion_rejections = {};
      verify.patch_rounds = 0;
      verify.patch_rounds_by_level = {};
      verify.refinement_rounds = 0;
      verify.fixer_rejections = [];
      // A fix-as-you-go pause belongs to the review being redone: the next V1.5 grades every level.
      delete verify.level_pause;
      // The core will be accepted afresh, so any progress past the re-entered stage is void (V6
      // would otherwise read a stale "F5 done" and look for Lean output of a core never proved).
      // V1 revises (or, the source changed, re-extracts) the transcription; V1.5 re-reviews the
      // core V1 already wrote.
      state.stage_completed = args.fromStage === "V1" ? "init" : "V1";
      // Every earlier finding — V1.5's and the F stages' alike — describes the core being
      // replaced: superseded, not accumulated (V1.5 restates what still holds, carried verdicts
      // included).
      verify.findings = [];
      if (args.freshReview) {
        verify.confirmed = {};
        verify.confirmed_symbols = {};
        log("--fresh-review: no V1.5 verdict is carried; the next review grades every node and every symbol.");
      }
      // No core is accepted until the fresh review accepts one.
      verify.core_sha256 = null;
      verify.transcribed_sha256 = null;
      // The paper-error ledger describes the TRANSCRIPTION: it survives a re-review (V1.5), not a
      // re-transcription (V1), whose node ids and text may differ.
      // Re-transcribing restarts the repair: the old patch file addressed the old transcription,
      // so it is set aside (kept as patches.json.prev), never re-applied to a new one.
      // A re-entry while the source is unchanged REVISES: the transcription, its ledger, the patch
      // file and the carried verdicts all stand (`v1EntryMode`).
      const entry = args.fromStage === "V1" ? await v1EntryMode(runDir, verify.source.sha256, dryRun) : null;
      if (entry) log(`--from-stage V1: ${entry.mode === "revise" ? "revise" : "cold re-extraction"} — ${entry.why}`);
      if (entry?.mode === "cold") {
        verify.paper_errors = {};
        verify.confirmed = {};
        verify.confirmed_symbols = {};
        const patchesFile = path.join(runDir, VERIFY_FILES.patches);
        if (existsSync(patchesFile)) await rename(patchesFile, `${patchesFile}.prev`);
        // … and so do the rulings awaiting the owner's review and the issues they reported
        // (`orch.mjs`, the page): they name nodes and comments of the old transcription.
        for (const f of ["orch_decisions.json", "owner_objections.json"].map((n) => path.join(runDir, n))) if (existsSync(f)) await rename(f, `${f}.prev`);
        await rm(path.join(runDir, FIXER_HISTORY_FILE), { force: true });
      } else {
        // A ledger error no entry of the patch file addresses — its repair was sent back to the
        // fixer and the run stopped (a cap) before the fixer answered — is dropped: the re-review
        // grades the node as printed and finds it again if it still stands.
        const patchesFile = path.join(runDir, VERIFY_FILES.patches);
        const onFile = existsSync(patchesFile) ? (JSON.parse(await readFile(patchesFile, "utf8")) as { patches?: Array<{ node: string }>; unfixable?: Array<{ node: string }> }) : null;
        const addressed = new Set([...(onFile?.patches ?? []), ...(onFile?.unfixable ?? [])].map((e) => e.node));
        const open = Object.keys(verify.paper_errors ?? {}).filter((id) => !addressed.has(id) && !isWithdrawn(verify.paper_errors![id]));
        for (const id of open) delete verify.paper_errors![id];
        if (open.length > 0) log(`--from-stage ${args.fromStage}: ${open.join(", ")} — an error with no repair on file; the re-review grades it as printed`);
      }
      // The transcription comes first: a pending PATCH directive would send V1 into patch mode on
      // the old transcription. Its V1.5 errors are in the ledger; its F-stage findings, like every
      // earlier finding, are superseded by the re-entry.
      const directiveFile = path.join(runDir, VERIFY_FILES.v1ReviseDirective);
      if (entry && existsSync(directiveFile) && JSON.parse(await readFile(directiveFile, "utf8"))?.mode === "patch") {
        await rm(directiveFile, { force: true });
        log("--from-stage V1: the pending patch directive is set aside; the transcription is revised first.");
      }
    }
    // The core is about to be replaced: the paper leaves the papers barrel until F5 completes again.
    if (args.fromStage === "V1" || args.fromStage === "V1.5") await voidForNewCore(); else if (args.fromStage === "V6" && verifyBlock(state, stateFile).promotion?.status === "applied") {
      // Only the report is written again: the Lean is the one the applied round was decided on.
      log("--from-stage V6: the report is written again; the applied promotion round stands.");
    } else {
      await voidPromotion(`--from-stage ${args.fromStage}: the run is re-entered, so its report is proposed afresh`, "B", { keepDecided: true });
      if (args.fromStage === "F1") await voidPromotion("--from-stage F1: the paper is re-planned", "A", { keepDecided: true });
    }
    // A re-entry at any stage is a ruling past a blocked F1: its record would only misname a later halt.
    state.flags.f1_blocked = null;
    // A live re-extraction replaces everything a dry run wrote (`dryRunRefusal` admits exactly
    // this entry), so the state stops being a dry-run state.
    if (args.fromStage === "V1" && !dryRun && verify.dry_run) {
      delete verify.dry_run;
      log("--from-stage V1 without --dry-run: the dry-run record is replaced by a live re-extraction.");
    }
    if (args.fromStage === "V1") verify.phase = "init";
    else if (args.fromStage === "V1.5") verify.phase = "v1";
    else if (args.fromStage === "V6") {
      verify.phase = "v6";
      // The report is being written again: the run is not complete past F5 until it is (V6 closes
      // the cursor again). A V6 that threw left the cursor at V6, and the page read the run as done.
      if (state.stage_completed === "V6") state.stage_completed = "5";
    }
    else {
      const internal = STAGE_HALT_ID_TO_INTERNAL[args.fromStage as StageHaltId];
      if (!internal || internal.startsWith("V")) {
        throw new Error(
          `--from-stage ${args.fromStage} is not a known stage id (expected V1, V1.5, V6, or an F stage).`,
        );
      }
      verify.phase = "formalization";
      fStartOverride = internal;
    }
    await save();
  }

  /** `referee.shard_bytes` / `shard_max_*`, as the stage takes them (unset keys keep the defaults). */
  const shardLimitsOf = (r: NonNullable<typeof toolkit.referee>): NonNullable<VerifyStageArgs["refereeShardLimits"]> => ({
    ...(r.shard_bytes ? { bytes: r.shard_bytes } : {}),
    ...(r.shard_max_hypotheses ? { hypotheses: r.shard_max_hypotheses } : {}),
    ...(r.shard_max_lemmas ? { lemmas: r.shard_max_lemmas } : {}),
    ...(r.shard_max_theorems ? { theorems: r.shard_max_theorems } : {}),
  });
  const runStage = async (label: string, stage: VerifyStage): Promise<VerifyStageResult> => {
    log(`${label}: start`);
    const confirming = state.verify?.weakening_repair?.status === "pending" && state.verify.weakening_repair.unconfirmed === true;
    const result = await stage({
      repoRoot,
      qid,
      runDir,
      state,
      deps: { runCodex: withTokenLedger(codex, runDir, label.split(" ")[0]!) },
      dryRun,
      ...(toolkit.referee?.max_concurrent ? { refereeMaxConcurrent: toolkit.referee.max_concurrent } : {}),
      ...(toolkit.referee ? { refereeShardLimits: shardLimitsOf(toolkit.referee) } : {}),
      ...(toolkit.referee?.symbol_effort ? { refereeSymbolEffort: toolkit.referee.symbol_effort } : {}),
      ...(dryRun && args.dryRunSyntheticErrors?.length ? { dryRunSyntheticErrors: args.dryRunSyntheticErrors } : {}),
      log: (msg) => log(`${label}: ${msg}`),
    });
    // The producers of model texts this stage wrote again (`fragment_routing.ts`): V1 the fixer's,
    // V1.5 the symbol table's and — unless it stopped at a pending receipt it was not confirming — the nodes'.
    if (label === "V1") router.notePass("V1");
    else if (label.startsWith("V1.5")) router.notePass("V1.5", confirming || !(result.status === "checkpoint" && state.verify?.weakening_repair?.status === "pending"));
    // Every V1.5 pass ends with the annotated paper of its verdicts (and of any halt it ends in).
    passAnnotation = label.startsWith("V1.5") ? await annotate(label) : null;
    log(`${label}: ${result.status} — ${result.message}${passAnnotation ? `; annotated paper: ${passAnnotation.line}` : ""}`);
    // Every V pass leaves its outcome where the page reads the run's last event: an earlier
    // checkpoint line stood as "halted" after a pass that went on. (A checkpoint is written by the
    // halt it ends in, below.)
    if (result.status !== "checkpoint") await appendPipelineLog({ repoRoot, qid }, { stage: label.split(" ")[0] as Stage, status: result.status !== "failed" ? result.status : label === "V1" ? "transcription-failed" : "refuted", duration_ms: 0, message: result.message });
    return result;
  };

  // A render checkpoint on file is answered first, by rendering again (the orchestrator fixed the
  // renderer; a contract checkpoint's fragments go back to their producers): a renderer defect → halt
  // again; model fragments that do not compile → routed, and the run goes on into their producers'
  // passes; clean → cleared. A re-entry at V1 / V1.5 redoes the review, and its pass renders anew.
  {
    const verify = verifyBlock(state, stateFile);
    const rc = verify.render_checkpoint ?? null;
    // An edit of a reading on record changes the core and sends the run to V1.5 (below), whose pass
    // ends in a fresh render: it is taken at this halt too — the reading's own text may be the block
    // that does not compile — and the checkpoint is re-evaluated by that render, as on a re-entry.
    const readingEdit = Boolean(args.resume && !args.fromStage && (args.editReading?.length || args.removeReading?.length));
    if (rc && readingEdit) {
      // Nothing is cleared here: the checkpoint goes once the edit has been APPLIED (below) — a
      // refused edit leaves it standing.
      log(`${rc.kind === "contract" ? "contract" : "render"} checkpoint: the reading on record is revised first; the V1.5 pass it starts renders the paper again.`);
    } else if (rc && (args.fromStage === "V1" || args.fromStage === "V1.5")) {
      verify.render_checkpoint = null;
      await save();
    } else if (rc) {
      const name = rc.kind === "contract" ? "contract" : "render";
      log(`${name} checkpoint: rendering the annotated paper again (${rc.defects.length} block(s) on file).`);
      // The checkpoint is answered before any ruling is read: while it stands, a ruling sent with this
      // resume would be read by nobody — refused aloud, never dropped (it is taken once the render is clean).
      const answers = haltAnswerFlags(args);
      const unread = (): Error => new Error(
        `${answers.join(", ")} was not read: the run is halted at a ${name} checkpoint, which comes before every ruling and still stands ` +
          `(${rc.defects.length} block(s); a tool defect, the orchestrating agent's to settle — no decision of the owner's). Settle it, then send the ruling again.`,
      );
      const a = await annotate("render checkpoint");
      if (!a.render) {
        log("render checkpoint: the annotated paper was not written — the checkpoint stands.");
        if (answers.length > 0) throw unread();
        return verify;
      }
      if ((await renderGate(a, "resume")) === "halt") {
        if (answers.length > 0) throw unread();
        return verify;
      }
    }
  }

  // The answers to the halts that ask for a ruling: the owner's on a weakened repair (entered for
  // them, or sent from the page), the orchestrator's on a proposed rewind and a cap. Each is refused
  // anywhere but at its halt, so a stray flag can never approve, reject or waive something unseen.
  {
    const acceptNamed = Array.isArray(args.acceptRepair) ? [...(args.acceptRepair as readonly string[])] : [];
    const acceptBare = args.acceptRepair === true;
    const accepting = acceptBare || acceptNamed.length > 0;
    const verify = verifyBlock(state, stateFile);
    // The owner's ruling on suggested repairs that weaken a main theorem.
    const weak = verify.weakening_repair?.status === "pending" ? verify.weakening_repair : null;
    // `--reject-finding` values: the batch form (the pending receipt's items) or one per node (any halt).
    const rfValues = args.rejectFinding == null ? [] : (typeof args.rejectFinding === "string" ? [args.rejectFinding] : [...args.rejectFinding]).map((v) => v.trim());
    if (rfValues.some((v) => v === "")) throw new Error("--reject-finding needs the reading: say how the paper is to be read and why the finding does not apply.");
    const coreIds = rfValues.length > 0 || args.declineRepair != null || (args.redoRepair?.length ?? 0) > 0 || (args.addCondition?.length ?? 0) > 0 ? await transcribedNodeIds(runDir) : new Set<string>();
    const rfParsed = rfValues.map((v) => ({ v, ...parseRejectFinding(v, coreIds) }));
    // A node-scoped withdrawal of an item of the pending receipt is answered with the receipt below.
    const receiptNodes = new Set(weak ? undecidedItems(weak).map((i) => i.node) : []);
    const receiptRejects = rfParsed.filter((x) => x.node !== null && receiptNodes.has(x.node)).map((x) => ({ node: x.node!, kind: x.kind, text: x.text }));
    const nodeFindings = rfParsed.filter((x) => x.node !== null && !receiptNodes.has(x.node)).map((x) => ({ node: x.node!, kind: x.kind, text: x.text }));
    // `--redo-repair "<node>: <guidance>"`, and `--decline-repair "<node>[,<node>]: <reason>"` (else bare).
    const redo = (args.redoRepair ?? []).map((v) => {
      const m = /^\s*([A-Za-z]+:[A-Za-z0-9._-]+)\s*:\s*([\s\S]*)$/.exec(v);
      if (!m || !coreIds.has(m[1]!)) throw new Error(`--redo-repair "${v}": give "<node>: <guidance>", the node an item of the pending receipt.`);
      return { node: m[1]!, guidance: m[2]!.trim() };
    });
    const dm = args.declineRepair != null ? DECLINE_NODES.exec(args.declineRepair) : null;
    const dNodes = dm ? dm[1]!.split(",").map((n) => n.trim()) : [];
    // A value in the node-scoped form names nodes of the core, or it is an error: it never falls
    // through to a bare decline of every item (its "reason" would be the misspelt node).
    const dUnknown = dNodes.filter((n) => !coreIds.has(n));
    if (dUnknown.length > 0) throw new Error(`--decline-repair "${args.declineRepair}": ${dUnknown.join(", ")} ${dUnknown.length > 1 ? "are" : "is"} not a node of the core; give "<node>[,<node>]: <reason>" with the nodes of the pending receipt (or a bare reason to decline every item).`);
    const declineNamed = dm ? { nodes: dNodes, reason: dm[2]!.trim() } : null;
    const declineBare = args.declineRepair != null && !declineNamed ? args.declineRepair : null;
    const batch = rfParsed.filter((x) => x.node === null).map((x) => x.v);
    if (batch.length > 1) throw new Error("--reject-finding without a node answers the pending receipt as a whole: give it once (name a node, \"<node>: <reading>\", to answer one result).");
    if (batch.length > 0 && nodeFindings.length > 0) throw new Error("--reject-finding: give either the batch form (the pending receipt) or one answer per node, not both.");
    const rejectFinding = batch[0] ?? null;
    // The batch form withdraws EVERY pending item: a value that opens with a node id was meant for one
    // result (the same rule as a bare `--decline-repair`).
    const rfOpens = rejectFinding === null ? null : /^\s*([A-Za-z]+:[A-Za-z0-9._-]+)\s*:/.exec(rejectFinding)?.[1] ?? [...receiptNodes].find((n) => rejectFinding.startsWith(n) && !/^[A-Za-z0-9._-]/.test(rejectFinding.slice(n.length))) ?? null;
    if (rfOpens) {
      throw new Error(`--reject-finding "${rejectFinding}": it opens with ${rfOpens}, ${coreIds.has(rfOpens) ? "but is not" : "which is not a node of the core, so it is not"} "<node>: <reading>" — as the batch form it would answer every pending item. Give "<node>: <reading>" with a node of the core, or a reading that does not open with a node id.`);
    }
    if (weak?.unconfirmed && (accepting || args.declineRepair != null || redo.length > 0 || rejectFinding !== null || receiptRejects.length > 0)) {
      throw new Error(
        `the suggested repair(s) of ${weak.items.map((i) => i.node).join(", ")} have not been presented yet: the V1.5 pass confirming the other changes of their round has not settled. ` +
          "Continue with a plain --resume; the receipt is presented when only the owner's decisions are left.",
      );
    }
    const rewindPresented = verify.cross_stage_rewind?.status === "pending" && verify.cross_stage_rewind.presented === true;
    // --- CHECKED AGAINST THE STATE, before anything is applied: each ruling names a halt the run is
    // at and items that exist. A refusal that needs the patch file (a reading id not on file, a
    // text that does not fit) is thrown by the function that applies the ruling, which validates
    // before it persists; the entry is settled (`settleEntry`) only after those have applied.
    const conditionItems = (args.addCondition ?? []).map((v) => {
      const m = /^\s*([A-Za-z]+:[A-Za-z0-9._-]+)\s*:\s*([\s\S]+)$/.exec(v);
      if (!m || !coreIds.has(m[1]!)) throw new Error(`--add-condition "${v}": give "<node>: <condition>", the node a core id.`);
      return { node: m[1]!, text: m[2]!.trim() };
    });
    const readingEdits = (args.editReading ?? []).map(parseEditReading);
    const readingRemovals = (args.removeReading ?? []).map((id) => id.trim());
    const umbrellas = (args.umbrella ?? []).map(parseUmbrella);
    // every owner text this answer records is TeX: checked here, so a refused one leaves nothing half-applied
    for (const t of [...conditionItems.map((c) => c.text), ...readingEdits.map((e) => e.text), ...rfParsed.map((x) => x.text)]) assertOwnerTex(t);
    const ruling = accepting || args.declineRepair != null || redo.length > 0;
    const rulingFlag = accepting ? "--accept-repair" : args.declineRepair != null ? "--decline-repair" : "--redo-repair";
    if (rejectFinding !== null && !weak && !rewindPresented) {
      throw new Error("--reject-finding \"<reading>\" (no node named) requires a run halted at a suggested repair that weakens the contribution (state.verify.weakening_repair pending) or at a proposed F-stage rewind (state.verify.cross_stage_rewind pending and presented); to withdraw the finding on one result at any halt, name it: --reject-finding \"<node>: <reading>\".");
    }
    if (ruling && !weak) {
      throw new Error(`${rulingFlag} requires a run halted at a suggested repair that weakens the contribution (state.verify.weakening_repair pending).`);
    }
    if (weak) {
      if (declineBare !== null && !declineBare.trim()) throw new Error("--decline-repair needs a reason: say why the weakened version is not worth formalizing.");
      if (declineBare !== null && /^\s*[A-Za-z]+:[A-Za-z0-9._-]+(\s*,\s*[A-Za-z]+:[A-Za-z0-9._-]+)*\s*:\s*$/.test(declineBare)) throw new Error(`--decline-repair "${declineBare}" needs a reason after the node(s): say why the weakened version is not worth formalizing.`);
      // A bare reason declines EVERY pending item: one that opens with an item's id was meant for that item.
      const opens = declineBare === null ? undefined : [...receiptNodes].find((n) => declineBare.trim().startsWith(n) && !/^[A-Za-z0-9._-]/.test(declineBare.trim().slice(n.length)));
      if (opens) throw new Error(`--decline-repair "${declineBare}": it opens with the pending item ${opens} but is not "<node>[,<node>]: <reason>" — as a bare reason it would decline every pending item (${[...receiptNodes].join(", ")}). Give "${opens}: <reason>", or a reason that does not open with a node id.`);
      const strangers = [...acceptNamed, ...(declineNamed?.nodes ?? []), ...redo.map((x) => x.node)].filter((n) => !receiptNodes.has(n));
      if (strangers.length > 0) throw new Error(`${strangers.join(", ")} ${strangers.length > 1 ? "are" : "is"} not a pending item of the receipt (items still to rule on: ${[...receiptNodes].join(", ") || "none"}).`);
      // (what `ruleOnReceipt` would refuse after a withdrawal of this resume was already applied)
      const bareAnswers = [acceptBare && "--accept-repair", declineBare !== null && "--decline-repair", rejectFinding !== null && "--reject-finding"].filter(Boolean);
      if (bareAnswers.length > 1) throw new Error(`${bareAnswers.join(" and ")} both answer the whole receipt; give one, or name nodes.`);
      const namedAll = [...acceptNamed, ...(declineNamed?.nodes ?? []), ...receiptRejects.map((x) => x.node), ...redo.map((x) => x.node)];
      if (bareAnswers.length === 1 && [...receiptNodes].every((n) => namedAll.includes(n))) throw new Error(`${bareAnswers[0]} without a node covers the items no other answer names, and every pending item is named: nothing is left for it to cover. Drop it, or name fewer nodes.`);
      const twice = namedAll.find((n, k) => namedAll.indexOf(n) !== k);
      if (twice) throw new Error(`${twice} is named by two answers; give one answer per result.`);
      const noGuidance = redo.find((x) => !x.guidance);
      if (noGuidance) throw new Error(`--redo-repair "${noGuidance.node}: <guidance>" needs the guidance: say how the fixer should repair it.`);
    }
    const capAtEntry = verify.cap_reached ?? null;
    if ((args.clearPatchCap || args.acceptCap) && !capAtEntry) {
      throw new Error(`${args.clearPatchCap ? "--clear-patch-cap" : "--accept-cap"} requires a run halted at a patch cap (state.verify.cap_reached is unset).`);
    }
    if (args.rejectRewind != null) {
      if (!rewindPresented) throw new Error("--reject-rewind requires a run halted at a proposed F-stage rewind (state.verify.cross_stage_rewind pending and presented).");
      if (!args.rejectRewind.trim()) throw new Error("--reject-rewind needs a reason: say where the paper grants what the finding says it lacks.");
    }
    // A receipt presented to the owner comes before a cap or a rewind: an answer to one of those
    // would be read by nobody at this halt — refused aloud.
    {
      const later = [args.rejectRewind != null && "--reject-rewind", args.clearPatchCap && "--clear-patch-cap", args.acceptCap && "--accept-cap"].filter(Boolean);
      if (weak && !weak.unconfirmed && later.length > 0) {
        throw new Error(`${later.join(", ")} was not read: the run is halted at a suggested repair that weakens ${weak.items.map((i) => i.node).join(", ")}, which is ruled on first (the user's decision, on the page).`);
      }
    }
    // --- APPLIED. (`settleEntry` follows the calls below that may still refuse.)
    if (conditionItems.length > 0) {
      // Accepted at any halt, like a node-scoped withdrawal: the core changes and V1.5 re-reviews.
      log(await addOwnerConditions(runDir, state, conditionItems));
      if (verify.cap_reached) verify.cap_reached = null;
      await voidForNewCore();
      await save();
    }
    if (readingEdits.length > 0 || readingRemovals.length > 0) {
      // Accepted at any halt: the reading on record changes, so the core does and V1.5 re-reviews.
      log(await reviseOwnerReadings(runDir, state, readingEdits, readingRemovals));
      if (verify.cap_reached) verify.cap_reached = null;
      // … a render / contract checkpoint too: the edit is applied, and the V1.5 pass it starts
      // renders the paper again (a refused edit threw above, the checkpoint standing).
      if (verify.render_checkpoint) verify.render_checkpoint = null;
      await voidForNewCore();
      await save();
    }
    if (umbrellas.length > 0) {
      // Accepted at any halt: the repair changes form, so the core does and V1.5 re-reviews.
      log(await convertToUmbrella(runDir, state, umbrellas));
      if (verify.cap_reached) verify.cap_reached = null;
      await voidForNewCore();
      await save();
    }
    if (nodeFindings.length > 0) {
      // Accepted at any halt: the core changes, so a pending cap's round is void and V1.5 re-reviews.
      log(await rejectAppliedFindings(runDir, state, nodeFindings));
      if (verify.cap_reached) {
        log(`the ${verify.cap_reached.counter} cap halt is lifted: the core it stopped on changed, and V1.5 re-reviews it.`);
        verify.cap_reached = null;
      }
      await voidForNewCore();
      await save();
    }
    if (weak && !ruling && rejectFinding === null && receiptRejects.length === 0) {
      // A receipt already presented is presented again; one still waiting for its confirming pass
      // is not: the run goes on from its phase (a fixer round due runs first).
      if (!weak.unconfirmed) {
        await settleEntry();
        const halted = await haltAtWeakening(verify);
        if (halted) return halted;
      }
    } else if (weak) {
      if (declineBare !== null && !declineBare.trim()) throw new Error("--decline-repair needs a reason: say why the weakened version is not worth formalizing.");
      // Node-scoped answers rule on their items; one bare answer covers the items no answer names;
      // items left unnamed stay pending suggestions and are presented again at the next halt.
      const bare = [acceptBare && "--accept-repair", declineBare !== null && "--decline-repair", rejectFinding !== null && "--reject-finding"].filter(Boolean);
      if (bare.length > 1) throw new Error(`${bare.join(" and ")} both answer the whole receipt; give one, or name nodes.`);
      const named = new Set([...acceptNamed, ...(declineNamed?.nodes ?? []), ...receiptRejects.map((x) => x.node), ...redo.map((x) => x.node)]);
      const rest = [...receiptNodes].filter((n) => !named.has(n));
      const accept = [...acceptNamed, ...(acceptBare ? rest : [])];
      const decline = [...(declineNamed ? declineNamed.nodes.map((node) => ({ node, reason: declineNamed.reason })) : []), ...(declineBare !== null ? rest.map((node) => ({ node, reason: declineBare.trim() })) : [])];
      // All or nothing: every answer is checked (its fit included) before the first is applied — a
      // later refusal left the earlier ones written, and the same command then failed on them.
      for (const check of [true, false]) {
        const said = (line: string | string[]): void => { if (!check) for (const l of [line].flat()) log(l); };
        for (const x of receiptRejects) said(await rejectWeakeningFinding(runDir, state, x.kind === "bookkeeping" ? `bookkeeping: ${x.text}` : x.text, [x.node], { check }));
        if (rejectFinding !== null && rest.length > 0) said(await rejectWeakeningFinding(runDir, state, rejectFinding, rest, { check }));
        if (accept.length > 0 || decline.length > 0 || redo.length > 0) said(await ruleOnReceipt(runDir, state, { accept, decline, redo }, { check }));
      }
      closeReceipt(verify);
      await settleEntry();
      if (verify.weakening_repair?.status === "pending") {
        const halted = await haltAtWeakening(verify);
        if (halted) return halted;
      }
      await save();
    }
    // A proposed rewind is answered before a cap its approved round ran into (the receipt is still
    // pending there, `applyPendingRewind`): rejecting the rewind, or withdrawing its finding under a
    // reading, leaves no round to cap — the cap goes with it. (A cap a V1.5 pass set stands.)
    const liftRewindCap = (why: string): void => {
      const c = verify.cap_reached;
      if (c && c.origin !== "V1.5") {
        verify.cap_reached = null;
        log(`the ${c.counter} cap halt is lifted: ${why}, so the round it stopped is not due.`);
      }
    };
    if (rejectFinding !== null && !weak) {
      log(await rejectRewindFinding(runDir, state, rejectFinding));
      liftRewindCap("the finding is withdrawn");
      await voidForNewCore();
      await save();
    }
    if (args.rejectRewind != null) {
      const rec = verify.cross_stage_rewind!;
      const reason = args.rejectRewind.trim();
      const nodes = rec.targets?.filter((t) => t.status === "routed" || t.status === undefined).map((t) => t.node ?? t.obj_id ?? "run") ?? [rec.nodes?.[0] ?? rec.target ?? "run"];
      rejectPendingRewind(state, reason);
      liftRewindCap("the rewind is rejected");
      log(`--reject-rewind: the ${rec.stage} ${rec.route} finding${nodes.length > 1 ? "s" : ""} on ${nodes.join(", ")} ${nodes.length > 1 ? "are" : "is"} ruled out (${reason}); the same finding on the same node is a note from now on. The F stages continue.`);
      await save();
      // The paper written at the halt asks for this decision; the Lean stages go on without a
      // pass that would write it again. Best-effort: the ruling is applied whatever the render says.
      await annotate("rewind rejected").catch((err) => log(`the annotated paper was not written again (${err instanceof Error ? err.message : String(err)}); it still shows the rewind as awaiting a decision.`));
    }
    await settleEntry();
    const cap = verify.cap_reached ?? null;
    if (cap && args.clearPatchCap) {
      // One more window: the cap stops a loop that is not converging, it does not declare the
      // repair impossible. Granting it twice for the same dispute is the signal to accept instead.
      log(`--clear-patch-cap: ${clearCap(verify, cap)}`);
      verify.cap_reached = null;
      if (cap.origin === "V1.5") {
        // The halting V1.5 pass already wrote the round's directive: the round opens now.
        log(`V1.5 patch round: ${countRound(verify, cap.counter === "refinement_rounds" ? "refinement" : "error", capScope(cap))} — re-entering V1 in patch mode.`);
        verify.phase = "init";
      }
      await save();
    } else if (cap && args.acceptCap) {
      log(`--accept-cap: the orchestrator ends the patch loop at ${cap.counter} ${cap.rounds}/${cap.cap}.`);
      // At a V1.5 refinement cap the repair is correct (only minimality is disputed): the core is
      // accepted and F1 formalizes it, so Lean certifies the confirmed repair. Otherwise V6
      // reports the state as it stands.
      let next: "v1_5" | "v6" = "v6";
      if (cap.origin === "V1.5") {
        // Refused aloud, nothing changed (the directive keeps a withdrawn suggestion), when accepting
        // would lose an entry of the ledger.
        if (cap.counter === "refinement_rounds") {
          const losses = acceptCapLosses(await readTranscribedCore(runDir), await readPatchFile(runDir), verify.paper_errors);
          if (losses.length > 0) throw new Error(`--accept-cap refused, nothing applied: ${losses.join(" ")} Restore the entry in ${VERIFY_FILES.patches} (a withdrawn suggestion is in ${VERIFY_FILES.v1ReviseDirective}, \`withdrawn_repair\`), or answer the cap with --clear-patch-cap.`);
        }
        await rm(path.join(runDir, VERIFY_FILES.v1ReviseDirective), { force: true });
        const result = await runStage("V1.5 (cap accepted)", stages.acceptCapV1_5);
        if (result.status === "checkpoint") {
          await save();
          log("halted at a V1.5 checkpoint while accepting the cap — continue with --resume --accept-cap.");
          return verify;
        }
        if (result.status === "completed") next = "v1_5";
      } else if (verify.cross_stage_rewind?.status === "pending") {
        verify.cross_stage_rewind = { ...verify.cross_stage_rewind, status: "refused", why: `the orchestrator accepted the ${cap.counter} cap: the finding is reported, not repaired` };
      }
      verify.cap_reached = null;
      verify.phase = next;
      const receipt = verify.weakening_repair?.status === "pending" ? verify.weakening_repair : null;
      if (next === "v1_5" && receipt) {
        // The loop that confirmed the receipt's round ends here: only the owner's decisions are left.
        const { unconfirmed: _u, ...presented } = receipt;
        verify.weakening_repair = presented;
        verify.phase = "v1";
        await save();
        log("the repaired core is accepted as correct but non-minimal; the owner rules on the suggested repair(s) before F1.");
        return (await haltAtWeakening(verify)) ?? verify;
      }
      log(next === "v1_5" ? "the repaired core is accepted as correct but non-minimal; F1 formalizes it." : "V6 reports the state as it stands.");
      await save();
      if (cap.origin === "V1.5" && (await annotationHalt(lastPass(), "pass"))) return verify;
    } else if (cap) {
      return haltAtCap(verify);
    }
  }

  const roundsAtEntry = state.verify?.patch_rounds ?? 0;
  const reviseAtEntry = state.verify?.v1_5_rounds ?? 0;
  // Rounds past the minimum backstop spent in this invocation extend the guard: five steps per
  // error round, two per revise round.
  const stepLimit = (): number =>
    MAX_PHASE_STEPS +
    5 * Math.max(0, (state.verify?.patch_rounds ?? 0) - roundsAtEntry - MIN_PATCH_BACKSTOP) +
    2 * Math.max(0, (state.verify?.v1_5_rounds ?? 0) - reviseAtEntry - MIN_PATCH_BACKSTOP);
  for (let step = 0; step < stepLimit(); step += 1) {
    const verify = verifyBlock(state, stateFile);
    switch (verify.phase) {
      case "done":
      case "failed": {
        // A finished full run that never had a promotion round (an earlier version, or one voided):
        // `--resume` opens it now, from the report on file.
        if (args.resume && state.stage_completed === "V6" && !verify.promotion) {
          log(`${qid}: the report is on file — opening the toolkit promotion round`);
          verify.phase = "proposals_B";
          await save();
          break;
        }
        log(`${qid} finished in phase ${verify.phase}.`);
        return verify;
      }
      case "init":
      case "v1": {
        const isV1 = verify.phase === "init";
        const receiptBefore = verify.weakening_repair?.at;
        const result = await runStage(isV1 ? "V1" : "V1.5", isV1 ? stages.v1 : stages.v1_5);
        const current = verifyBlock(state, stateFile);
        if (result.status === "checkpoint") {
          await save();
          if (current.cap_reached) return haltAtCap(current, lastPass());
          // The fixer's round wrote a receipt: a V1.5 pass grades its suggestions first. (Any other V1
          // checkpoint — a patch file the fixer could not make clean — halts below.)
          const wroteReceipt = isV1 && current.weakening_repair?.status === "pending" && current.weakening_repair.at !== receiptBefore;
          if (wroteReceipt && (await confirmBeforeOwner(current))) break;
          // (A V1.5 pass that stopped before confirming the receipt's round halts as any checkpoint.)
          if (current.weakening_repair?.status === "pending" && !current.weakening_repair.unconfirmed) {
            const halted = await haltAtWeakening(current, lastPass());
            if (halted) return halted;
            // The render routed model texts: V1.5 writes them again (its symbol pass runs before it
            // stops at the receipt), then the receipt is presented.
            if (isV1) {
              // V1 wrote the fixer's suggestion into the patch file and left core.json as it was (the
              // owner's): rebuilt here so V1.5 does not take the difference for a hand edit.
              await rebuildPatchedCore(runDir, { detectHandEdits: false }).catch(() => undefined); // V1.5 rebuilds it and reports a failure
              current.phase = "v1";
              await save();
            }
            break;
          }
          if (!isV1 && (await annotationHalt(lastPass(), "decision"))) return current;
          // The other V halts are on record in the state (a receipt, a cap, a rewind, a render
          // checkpoint); this one is only its message — written where the page and the watcher read
          // a halt, or the run reads as stopped for no reason.
          await appendPipelineLog({ repoRoot, qid }, { stage: isV1 ? "V1" : "V1.5", status: "checkpoint", duration_ms: 0, message: `${result.message} — settle what it names, then continue with --resume.` });
          log(`halted at a ${isV1 ? "V1" : "V1.5"} checkpoint — continue with --resume.`);
          return current;
        }
        if (result.status === "narrowed") {
          if (isV1) throw new Error("V1 returned `narrowed`; only V1.5 narrows intermediate results itself.");
          // The phase stays `v1`: the next step is a fresh V1.5 pass over the narrowed core.
          state.stage_completed = "V1";
          await save();
          log(`V1.5 narrowed intermediate result(s) — a fresh V1.5 pass confirms them — ${result.message}`);
          // Model texts of the pass that do not compile go back to their producers here too.
          if (await annotationHalt(lastPass(), "pass")) return current;
          break;
        }
        if (result.status === "patch") {
          if (isV1) throw new Error("V1 returned `patch`; only V1.5 may request a patch round.");
          const moved = countRound(current, result.round_kind ?? "error", result.round_scope);
          current.phase = "init";
          await save();
          log(`V1.5 patch round: ${moved} — re-entering V1 in patch mode — ${result.message}`);
          if (await annotationHalt(lastPass(), "pass")) return current;
          break;
        }
        if (result.status === "revise") {
          if (isV1) throw new Error("V1 returned `revise`; only V1.5 may request a revise round.");
          // V1.5 charged the round (its level is known there) and never asks past the cap.
          current.phase = "init";
          await save();
          // No render gate here: the transcription is re-read first, and the pass after it routes
          // whatever of its texts still does not compile.
          log(`V1.5 revise round ${current.v1_5_rounds}: re-entering V1 with the directive.`);
          break;
        }
        // A `failed` V1.5 is a refutation: the findings it recorded are the
        // report's content, so go straight to V6. A `failed` V1 is treated the
        // same way — the run stops early and V6 reports why.
        current.phase = result.status === "failed" ? "v6" : isV1 ? "v1" : "v1_5";
        // V1.5's acceptance writes its own cursor ("V1.5", with the core hash); V1 is recorded here.
        if (isV1 && result.status === "completed") state.stage_completed = "V1";
        await save();
        // Model texts that
        // do not compile re-open the core for the pass that writes them again.
        if (!isV1 && (await annotationHalt(lastPass(), "pass"))) return current;
        if (result.status !== "failed" && args.stopAfter === (isV1 ? "V1" : "V1.5")) {
          log(`--stop-after ${args.stopAfter}: halting for inspection${!isV1 && lastPass() ? ` — review the annotated paper: ${lastPass()!.line}` : ""} — continue with --resume.`);
          return current;
        }
        break;
      }
      case "v1_5": {
        verify.phase = "formalization";
        await save();
        break;
      }
      case "formalization": {
        // A rewind the F runner left pending (presented by an earlier invocation, or an F2.5–F4
        // escalation on a paper statement still pending): ruled on before any F stage. A refused
        // proof-review receipt already halted the F runner; this resume is the operator's answer
        // to it, so F2.5 re-enters as before.
        if (rewindPending()) {
          const out = await handleRewind(true);
          if (out === "routed") break;
          if (out === "halt") return verifyBlock(state, stateFile);
        }
        // A stop at V1 or V1.5 holds on a resume that starts past it (e.g. after a checkpoint that
        // followed the V1.5 acceptance): the F stages never start under it.
        if (args.stopAfter === "V1" || args.stopAfter === "V1.5") {
          log(`--stop-after ${args.stopAfter}: V1.5 is accepted; halting before F1 — continue with --resume.`);
          return verifyBlock(state, stateFile);
        }
        const startStage =
          fStartOverride ?? (isPreF(state.stage_completed) ? ("1" as Stage) : undefined);
        fStartOverride = undefined;
        const userStopAfter = args.stopAfter?.startsWith("F")
          ? STAGE_HALT_ID_TO_INTERNAL[args.stopAfter as StageHaltId]
          : undefined;
        // Round A sits between F1 and F1.5: until it has been held, F1 runs alone and the runner
        // stops after it. A resume that finds F1 done goes straight to the round.
        let roundAGate = false;
        if (!verify.promotion_a && (startStage === "1" || (startStage === undefined && state.stage_completed === "1"))) {
          if (args.deferProposals) {
            deferRoundA(verify);
            await save();
          } else if (startStage === undefined) {
            verify.phase = "proposals_A";
            await save();
            break;
          } else {
            roundAGate = true;
          }
        }
        log(
          `handing off to the F runner (${startStage ? `start F${startStage}` : `continue after stage ${state.stage_completed}`}` +
            `${roundAGate ? "; stopping after F1 for toolkit promotion round A" : ""})`,
        );
        await runFormalization({
          toolkit,
          qid,
          dryRun,
          auto: autoMode(),
          startStage,
          stopAfterStage: roundAGate ? ("1" as Stage) : userStopAfter,
        });
        // The F runner persists its own state; re-read rather than trusting the
        // in-memory copy, which is now stale.
        state = await loadVerifyState(repoRoot, qid);
        const current = verifyBlock(state, stateFile);
        // An F-stage finding that the paper lacks a hypothesis / is wrong as stated: proposed to the
        // orchestrator (halt), a noted repeat of a ruled-out finding (the F stages go on), or refused
        // (halt as before).
        if (rewindPending()) {
          const out = await handleRewind(false);
          if (out === "halt") return verifyBlock(state, stateFile);
          if (out === "continue" || out === "routed") break;
        }
        if (roundAGate && state.stage_completed === "1") {
          current.phase = "proposals_A";
          await save();
          if (userStopAfter === "1") {
            log("--stop-after F1: halting before toolkit promotion round A — continue with --resume.");
            return current;
          }
          break;
        }
        if (!fDone(state.stage_completed)) {
          // A set gate refuses a plain resume: say which, and how it is cleared.
          const block = resumeBlock(state.flags);
          if (block) {
            log(`F stages halted at stage ${state.stage_completed}; a plain --resume is refused until the gate is answered.\n${block}`);
            return current;
          }
          const why = userStopAfter !== undefined && userStopAfter === state.stage_completed ? `--stop-after ${args.stopAfter}` : "checkpoint";
          log(
            `F stages halted at stage ${state.stage_completed} (${why}) — inspect the run, ` +
              "then continue with `paperformalizer verify <input> --resume`.",
          );
          return current;
        }
        if (userStopAfter === "5") {
          current.phase = "v6";
          await save();
          log("--stop-after F5: halting before the V6 report — continue with --resume.");
          return current;
        }
        current.phase = "v6";
        await save();
        break;
      }
      case "v6": {
        const result = await runStage("V6", stages.v6);
        const current = verifyBlock(state, stateFile);
        if (result.status === "checkpoint") {
          await save();
          log("halted at a V6 checkpoint — continue with --resume.");
          return current;
        }
        // The report's own verdict decides the terminal phase (`reportTerminalPhase`); a full F run
        // passes through the toolkit promotion round first.
        // The report closes the cursor only after a full F run; an early stop keeps the cursor
        // where the run stopped (the report reads it to say the run never reached Lean).
        const full = fDone(state.stage_completed);
        if (full) state.stage_completed = "V6";
        current.phase = full ? "proposals_B" : reportTerminalPhase(current);
        await save();
        // (a round already held — applied, deferred, waiting — is not "before round B": the phase below settles it)
        if (full && args.stopAfter === "V6" && !current.promotion) {
          log("--stop-after V6: the report is written; halting before toolkit promotion round B — continue with --resume.");
          return current;
        }
        break;
      }
      case "proposals_A": {
        let rec = verify.promotion_a;
        if (!rec && args.deferProposals) {
          deferRoundA(verify);
          rec = verify.promotion_a!;
        }
        if (!rec) {
          // Round A reads the plan: one that breaks the plan schema goes back to F1 with the
          // violations (as F1.5's gate would send it) before the round is held.
          const { planSchemaViolations } = await import("../proposals/round_a.js");
          const violations = await planSchemaViolations(repoRoot, qid);
          if (violations) {
            if (planReplans >= MAX_PLAN_REPLANS) {
              throw new Error(`promotion A: the F1 plan still breaks the plan schema after ${planReplans} re-plan(s) — fix the planner's contract, then --resume:\n${violations}`);
            }
            planReplans += 1;
            log(`promotion A: the F1 plan breaks the plan schema — back to F1 (re-plan ${planReplans}/${MAX_PLAN_REPLANS}):\n${violations}`);
            state.flags.f1_revise_directive = `plan.json breaks the plan schema. Fix exactly these fields, keeping the rest of the plan:\n${violations}`;
            fStartOverride = "1";
            verify.phase = "formalization";
            await save();
            break;
          }
          rec = await runPromotionA({ toolkit, qid, dryRun, runCodex: withTokenLedger(codex, runDir, "promotion A"), log });
          verify.promotion_a = rec;
        }
        if (rec.status === "pending_user") {
          await save();
          if (args.deferProposals) log("--defer-proposals: round A is already proposed and waits for decisions — the flag skips a round not yet proposed; to skip this one, defer its entries on the checklist.");
          const { roundAStopMessage } = await import("../proposals/round_a.js");
          const { proposalBatchSchema } = await import("../proposals/schema.js");
          const count = rec.batch_path && existsSync(rec.batch_path)
            ? proposalBatchSchema.parse(JSON.parse(await readFile(rec.batch_path, "utf8"))).proposals.filter((p) => p.verdict === "propose").length
            : 0;
          log(roundAStopMessage(toolkit, qid, rec, count, dryRun, fullAuto()));
          return verify;
        }
        verify.phase = "formalization";
        await save();
        break;
      }
      case "proposals_B": {
        let rec = verify.promotion;
        if (!rec && args.stopAfter === "V6") {
          log("--stop-after V6: the report is on file; halting before toolkit promotion round B — continue with --resume.");
          return verify;
        }
        if (!rec) {
          rec = await runPromotion({ toolkit, qid, dryRun, runCodex: withTokenLedger(codex, runDir, "promotion B"), log });
          verify.promotion = rec;
        }
        if (rec.status === "pending_user") {
          await save();
          const { roundBStopMessage } = await import("../proposals/round_b.js");
          const { proposalBatchSchema } = await import("../proposals/schema.js");
          const count = rec.batch_path && existsSync(rec.batch_path)
            ? proposalBatchSchema.parse(JSON.parse(await readFile(rec.batch_path, "utf8"))).proposals.filter((p) => p.verdict === "propose").length
            : 0;
          log(roundBStopMessage(toolkit, qid, rec, count, dryRun, fullAuto()));
          return verify;
        }
        if (rec.status === "empty") log("promotion: nothing to propose — the run finishes.");
        verify.phase = reportTerminalPhase(verify);
        await save();
        break;
      }
    }
  }
  throw new Error(
    `verify pipeline did not settle within ${stepLimit()} phase steps for ${qid} ` +
      `(phase ${verifyBlock(state, stateFile).phase}) — this is a runner bug.`,
  );
}
