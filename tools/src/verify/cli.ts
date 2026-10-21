/**
 * `paperformalizer verify` — argument parsing and process entry.
 *
 * Resolves the machine env + billing path, parses, loads the toolkit (`--toolkit`,
 * `PAPERFORMALIZER_TOOLKIT`, or the nearest ancestor holding `paperformalizer.json`), mints the run id
 * (the slug), pays the lean-lsp cold start once, and hands off to `runVerifyPipeline`.
 */
import { existsSync } from "node:fs";
import path from "node:path";
import { applyAuthEnv } from "../auth.js";
import { applyWorkerEnv, assertLeanProjectOverride } from "../local_config.js";
import { assertQidSlug, childrenPath, statePath, verifyRunDir } from "../paths.js";
import { setChildrenFile, stopRecordedRun } from "../shared/child_registry.js";
import { loadState } from "../state.js";
import { dryRunLeftover, dryRunRefusal } from "./dry_run.js";
import { clearSharedLeanLspUrl, setSharedLeanLspUrl, sharedLeanLspUrl } from "../shared/shared_lean_lsp_env.js";
import { loadToolkitConfig } from "../toolkit/config.js";
import { assertToolkitLakefile } from "../toolkit/lakefile.js";
import { runVerifyPipeline } from "./pipeline.js";
import { haltAnswerConflict, haltAnswerFlags, type HaltAnswers } from "./weakening.js";
import { FROM_STAGE_USAGE, fromStageRefusal, STAGE_HALT_IDS, STOP_AFTER_USAGE, stopAfterRefusal, type StageHaltId } from "../constants.js";
import { warmUpLeanOrThrow } from "../shared/lean_warmup.js";

export const USAGE =
  "Usage: paperformalizer verify <paper.tex|dir|archive> [--toolkit <path>] [--slug s] [--main relpath] " +
  "[--targets label,label] [--resume] " +
  "[--from-stage <stage>] [--fresh-review] [--from-transcript] [--stop-after <stage>] [--clear-gate <flag>]... [--defer-proposals] [--debug | --full-auto] [--dry-run]\n" +
  "  <paper.tex>: a .tex that includes files lying beside it is taken with its directory (the file the main one);\n" +
  "  one whose included .tex files are missing is refused — pass the paper's directory or an archive\n" +
  "  --defer-proposals: skip toolkit promotion round A (after F1); the paper's cited results stay assumptions\n" +
  "  auto mode is the default: the orchestrating agent rules on every checkpoint itself, without asking; the owner's\n" +
  "  decisions stay the owner's. --debug (kept across resumes) turns it off: the agent may bring a ruling to the user\n" +
  "  --full-auto (kept across resumes): the owner's decisions are delegated as well — a repair that\n" +
  "  would weaken a main result and the promotion rounds take the agent's recommendation on each item, listed for\n" +
  "  the owner's review on the page\n" +
  "  verify --stop --slug <s> [--toolkit <path>] (no other flag; the paper in place of --slug names the same run):\n" +
  "  stop the run's live runner and child processes recorded in runs/<slug>/logs/children.json — each pid only if\n" +
  "  its start time still matches — then clear the file\n" +
  "  [--reject-rewind \"<reason>\"] [--clear-patch-cap] [--accept-cap] [--accept-repair [<node>,…]] [--decline-repair \"[<node>,…: ]<reason>\"]\n" +
  "  [--reject-finding \"<reading>\" | \"<node>: <reading>\" | \"<node>: bookkeeping: <condition>\"]... [--redo-repair \"<node>: <guidance>\"]...\n" +
  "  [--add-condition \"<node>: <condition>\"]... [--edit-reading \"<id>: <new text>\"]... [--remove-reading <id>]...\n" +
  "  [--umbrella <node> | \"<node>: <title>\"]...\n" +
  "  (each with --resume, answering its halt)\n" +
  `  --from-stage <stage> ∈ ${FROM_STAGE_USAGE}; --stop-after <stage> ∈ ${STOP_AFTER_USAGE}\n` +
  "  (F2.5, F3, F3.5 and F4 run as one proof-review loop: entered at F2.5, completed as F4)\n" +
  "  --from-stage V1 revises the existing transcription while the source is unchanged; V1.5 grades only\n" +
  "  the nodes that changed and carries the rest. --fresh-review (with --from-stage V1|V1.5) grades every node.\n" +
  "  --from-transcript (with --resume) re-runs a paper under the current design from its finished V1 transcription:\n" +
  "  core.json becomes discovery/core.transcribed.json again; patches, verdicts, the error ledger, owner receipts and\n" +
  "  every F-stage artefact are moved under runs/<slug>/_archive/from_transcript_<stamp>/ and cleared (owner rulings\n" +
  "  stay); the next step is a fresh V1.5. Refused mid-V1, without a transcript, or when the source changed.\n" +
  "  With --resume, --slug alone names the run: the paper it was launched on is read again.\n" +
  "  The run id is the slug: --slug, else the input's file name. --main applies at a cold start only; --targets at a\n" +
  "  cold start or with --from-stage V1 (the new transcription takes the new scope), never with a plain --resume.\n" +
  "  An F-stage finding on a paper statement halts as a PROPOSED rewind (every mode, auto mode too): --resume\n" +
  "  approves it (a V1 patch round), --resume --reject-rewind \"<reason>\" rejects it (the F stages continue).\n" +
  "  A patch round due at its cap (3 error rounds per dependency level, a whole-run backstop, 3 refinement rounds)\n" +
  "  halts: --resume --clear-patch-cap grants one more window (that level's), --resume\n" +
  "  --accept-cap ends the loop (a refinement cap keeps the repair and continues to F1; else the report).\n" +
  "  A repair never weakens the paper: when only a weaker version of a result holds, it is SUGGESTED and the run\n" +
  "  halts for the owner (every mode): --resume --accept-repair applies it (V1.5 confirms it), --resume\n" +
  "  --decline-repair \"<reason>\" reports the result refuted (not determined, when the paper leaves the statement open) and leaves it, and what\n" +
  "  rests on it, out of Lean;\n" +
  "  --resume --redo-repair \"<node>: <guidance>\" discards the suggestion and has the fixer repair that result again\n" +
  "  along the owner's guidance (binding), then V1.5 confirms it. Name nodes to rule item by item in one resume\n" +
  "  (--accept-repair thm:a --redo-repair \"thm:b: …\"); a bare answer covers the items no other answer names.\n" +
  "  At either halt a finding that misreads the paper is withdrawn instead: --resume --reject-finding \"<reading>\"\n" +
  "  (the printed statement stands; the reading is pinned into the core, binds the formalization, and the same\n" +
  "  finding on the same node is a note from then on). At ANY halt the finding on one result is withdrawn the\n" +
  "  same way, its applied repair included: --resume --reject-finding \"<node>: <reading>\" (a pinned reading) or\n" +
  "  \"<node>: bookkeeping: <condition>\" (a side condition every reader takes for granted); repeatable.\n" +
  "  An owner reading on record (discovery/patches.json owner_readings, ass:pin-owner-<n> / ass:bk-owner-<n>) is\n" +
  "  revised at any halt: --resume --edit-reading \"<id>: <new text>\" rewords it (id, node and the findings it\n" +
  "  withdrew kept), --resume --remove-reading <id> deletes it (a finding it withdrew is open again); V1.5 then\n" +
  "  grades what changed. Both repeatable, and they combine.\n" +
  "  A repair that split blocks off a result whose printed statement mixes several conclusions under different\n" +
  "  conditions, none its own main claim, is turned into the umbrella form at any halt, with no fixer round:\n" +
  "  --resume --umbrella <node> (or \"<node>: <title>\") makes what the corrected statement still states one more\n" +
  "  proposition block and the result an umbrella over its blocks, established exactly when all of them are;\n" +
  "  V1.5 grades what changed and F1 re-plans.\n" +
  "  An annotated paper with a block that could not be set as TeX (escaped text, a code point, an odd $, a pdflatex\n" +
  "  error) halts the run as a RENDER CHECKPOINT, before any owner decision and F1 (every mode):\n" +
  "  a tool defect with no owner waiver — correct a text from the run's record, else fix the renderer with a test; --resume renders again (`paperformalizer lint-annotated`).";

/** Stages `--from-stage` and `--stop-after` accept: the two V stages the verify runner
 * owns, the F stages it delegates, and the report. (`--from-stage V1.5` re-runs the
 * review of an existing core; an `F*` value hands straight to the F runner.
 * `--stop-after <stage>` halts once that stage completes, so a first run can be
 * inspected stage by stage and continued with `--resume`.) */
export const VERIFY_FROM_STAGES = STAGE_HALT_IDS;
export type VerifyFromStage = (typeof VERIFY_FROM_STAGES)[number];

export interface VerifyArgs {
  /** The `.tex` file, directory, or archive as typed on the command line (`""`: `--stop --slug`). */
  input: string;
  /** `--toolkit <path>`, when given. */
  toolkit: string | null;
  slug: string | null;
  /** `--main <relpath>`: which file inside a directory/archive is the main `.tex`. */
  main: string | null;
  targets: string[] | null;
  resume: boolean;
  fromStage: VerifyFromStage | null;
  /** `--stop-after <stage>`: halt after this stage completes (continue with `--resume`). */
  stopAfter: VerifyFromStage | null;
  /** `--clear-gate <flag>` (repeatable, `--resume` only): clear a resume-blocking cap gate. */
  clearGates: string[];
  /** `--fresh-review` (needs `--from-stage V1|V1.5`): the next V1.5 carries no verdict. */
  freshReview: boolean;
  /** `--from-transcript` (with `--resume`): restart from the finished V1 transcription (`from_transcript.ts`). */
  fromTranscript: boolean;
  /** `--reject-rewind "<reason>"` (with `--resume`): reject the proposed F-stage rewind. */
  rejectRewind: string | null;
  /** `--clear-patch-cap` (with `--resume`): one more window of patch rounds at a cap. */
  clearPatchCap: boolean;
  /** `--accept-cap` (with `--resume`): end the patch loop at a cap (refinement cap → F1, else V6). */
  acceptCap: boolean;
  /** `--accept-repair [<node>,…]` (with `--resume`): apply the suggested repairs that weaken the
   * contribution — every pending one (`true`), or those of the nodes named. */
  acceptRepair: boolean | string[];
  /** `--decline-repair "[<node>,…: ]<reason>"` (with `--resume`): decline them (refuted, descoped). */
  declineRepair: string | null;
  /** `--redo-repair "<node>: <guidance>"` (with `--resume`; repeatable): discard that node's suggested
   * repair; the fixer repairs it again under the owner's guidance (`weakening.ts` `ruleOnReceipt`). */
  redoRepair: string[] | null;
  /** `--reject-finding` (with `--resume`; repeatable): `"<reading>"` withdraws the finding at a
   * weakening or rewind halt; `"<node>: <reading>"` / `"<node>: bookkeeping: <condition>"` withdraws
   * the finding on that node, its applied repair included, at any halt (`owner_rulings.ts`). */
  rejectFinding: string[] | null;
  /** `--add-condition "<node>: <condition>"` (with `--resume`; repeatable): an owner side condition the
   * paper takes for granted, added at any halt; withdraws nothing (`owner_rulings.ts` `addOwnerConditions`). */
  addCondition: string[] | null;
  /** `--edit-reading "<id>: <new text>"` / `--remove-reading <id>` (with `--resume`; repeatable): an
   * owner reading on record is reworded or deleted (`owner_rulings.ts` `reviseOwnerReadings`). */
  editReading: string[] | null;
  removeReading: string[] | null;
  /** `--umbrella <node>` / `--umbrella "<node>: <title>"` (with `--resume`; repeatable): a split repair
   * becomes the umbrella form without a fixer round (`owner_rulings.ts` `convertToUmbrella`). */
  umbrella: string[] | null;
  /** Auto mode: on unless `--debug`. */
  auto: boolean;
  /** `--debug` (latching onto `state.debug_mode`): auto mode off for the run. */
  debug: boolean;
  /** `--full-auto`: the owner's decisions take the agent's recommendations (`SharedState.full_auto`). */
  fullAuto: boolean;
  /** `--defer-proposals`: skip toolkit promotion round A. */
  deferProposals: boolean;
  dryRun: boolean;
  /** `--stop`: stop the run's recorded runner and children (`children.json`) instead of running. */
  stop: boolean;
}

/** Max characters of the derived slug. Keeps `runs/<slug>/…` paths short enough for Windows
 * checkouts. */
export const VERIFY_SLUG_MAX = 40;

/** An owner reading's id, and an `--edit-reading` value naming one (`owner_rulings.ts` `parseEditReading`). */
const OWNER_READING_ID = /^ass:(pin|bk)-owner-[0-9]+$/;
const OWNER_READING_EDIT = /^\s*ass:(pin|bk)-owner-[0-9]+\s*:\s*\S/;

/** A comma-separated list of core node ids (`thm:a,lem:b-2`): `--accept-repair`'s optional value. */
const NODE_LIST = /^[A-Za-z]+:[A-Za-z0-9._-]+(\s*,\s*[A-Za-z]+:[A-Za-z0-9._-]+)*$/;

function usageError(detail: string): Error {
  return new Error(`${detail}\n${USAGE}`);
}

function parseVerifyArgs(argv: string[]): VerifyArgs {
  const args = [...argv];

  const takeFlag = (flag: string): boolean => {
    const i = args.indexOf(flag);
    if (i === -1) return false;
    args.splice(i, 1);
    if (args.includes(flag)) throw usageError(`${flag} given more than once.`);
    return true;
  };
  const takeValue = (flag: string): string | null => {
    const i = args.indexOf(flag);
    if (i === -1) return null;
    const value = args[i + 1];
    if (value === undefined || value.startsWith("-")) {
      throw usageError(`${flag} requires a value.`);
    }
    args.splice(i, 2);
    if (args.includes(flag)) throw usageError(`${flag} given more than once.`);
    return value;
  };

  // Booleans first, and position-independently so
  // `verify --resume paper.tex` and `verify paper.tex --resume` behave alike.
  const resume = takeFlag("--resume");
  const fullAuto = takeFlag("--full-auto");
  // auto mode is the default: `--auto` is accepted and changes nothing; `--debug` turns it off
  const autoFlag = takeFlag("--auto");
  const debug = takeFlag("--debug");
  if (debug && fullAuto) throw usageError("--debug and --full-auto exclude each other: --debug turns auto mode off.");
  const auto = !debug;
  const deferProposals = takeFlag("--defer-proposals");
  const dryRun = takeFlag("--dry-run");
  const freshReview = takeFlag("--fresh-review");
  const fromTranscript = takeFlag("--from-transcript");
  const clearPatchCap = takeFlag("--clear-patch-cap");
  const acceptCap = takeFlag("--accept-cap");
  // `--accept-repair` alone, or followed by a comma-separated node list (`thm:a,lem:b`).
  let acceptRepair: boolean | string[] = false;
  {
    const i = args.indexOf("--accept-repair");
    if (i !== -1) {
      const next = args[i + 1];
      const nodes = next !== undefined && NODE_LIST.test(next) ? next.split(",").map((n) => n.trim()) : null;
      args.splice(i, nodes ? 2 : 1);
      if (args.includes("--accept-repair")) throw usageError("--accept-repair given more than once (name several nodes with commas).");
      acceptRepair = nodes ?? true;
    }
  }
  const stop = takeFlag("--stop");

  const clearGates: string[] = [];
  for (let i = args.indexOf("--clear-gate"); i !== -1; i = args.indexOf("--clear-gate")) {
    const value = args[i + 1];
    if (value === undefined || value.startsWith("-")) throw usageError("--clear-gate requires a flag name.");
    clearGates.push(value);
    args.splice(i, 2);
  }
  if (clearGates.length > 0 && !resume) throw usageError("--clear-gate requires --resume.");
  const toolkit = takeValue("--toolkit");
  const slug = takeValue("--slug");
  const main = takeValue("--main");
  const targetsRaw = takeValue("--targets");
  const fromStageRaw = takeValue("--from-stage");
  const stopAfterRaw = takeValue("--stop-after");
  // The reason is free text and may start with anything but a dash.
  const rejectRewind = takeValue("--reject-rewind");
  const declineRepair = takeValue("--decline-repair");
  const rejectFindings: string[] = [];
  for (let i = args.indexOf("--reject-finding"); i !== -1; i = args.indexOf("--reject-finding")) {
    const value = args[i + 1];
    if (value === undefined || value.startsWith("-")) throw usageError("--reject-finding requires a value.");
    rejectFindings.push(value);
    args.splice(i, 2);
  }
  const rejectFinding = rejectFindings.length > 0 ? rejectFindings : null;
  const addConditions: string[] = [];
  for (let i = args.indexOf("--add-condition"); i !== -1; i = args.indexOf("--add-condition")) {
    const value = args[i + 1];
    if (value === undefined || value.startsWith("-")) throw usageError("--add-condition requires \"<node>: <condition>\".");
    addConditions.push(value);
    args.splice(i, 2);
  }
  const addCondition = addConditions.length > 0 ? addConditions : null;
  const editReadings: string[] = [];
  for (let i = args.indexOf("--edit-reading"); i !== -1; i = args.indexOf("--edit-reading")) {
    const value = args[i + 1];
    if (value === undefined || !OWNER_READING_EDIT.test(value)) throw usageError("--edit-reading requires \"<id>: <new text>\" (the id ass:pin-owner-<n> or ass:bk-owner-<n>).");
    editReadings.push(value);
    args.splice(i, 2);
  }
  const editReading = editReadings.length > 0 ? editReadings : null;
  const removeReadings: string[] = [];
  for (let i = args.indexOf("--remove-reading"); i !== -1; i = args.indexOf("--remove-reading")) {
    const value = args[i + 1];
    if (value === undefined || !OWNER_READING_ID.test(value)) throw usageError("--remove-reading requires an owner reading's id (ass:pin-owner-<n> or ass:bk-owner-<n>).");
    removeReadings.push(value);
    args.splice(i, 2);
  }
  const removeReading = removeReadings.length > 0 ? removeReadings : null;
  const umbrellas: string[] = [];
  for (let i = args.indexOf("--umbrella"); i !== -1; i = args.indexOf("--umbrella")) {
    const value = args[i + 1];
    if (value === undefined || !/^\s*[A-Za-z]+:[A-Za-z0-9._-]+\s*(?::|$)/.test(value)) throw usageError("--umbrella requires \"<node>\" or \"<node>: <title>\" (a result whose repair splits off blocks).");
    umbrellas.push(value);
    args.splice(i, 2);
  }
  const umbrella = umbrellas.length > 0 ? umbrellas : null;
  const redoRepairs: string[] = [];
  for (let i = args.indexOf("--redo-repair"); i !== -1; i = args.indexOf("--redo-repair")) {
    const value = args[i + 1];
    if (value === undefined || value.startsWith("-")) throw usageError("--redo-repair requires \"<node>: <guidance>\".");
    redoRepairs.push(value);
    args.splice(i, 2);
  }
  const redoRepair = redoRepairs.length > 0 ? redoRepairs : null;
  const halt: HaltAnswers = { rejectRewind, clearPatchCap, acceptCap, acceptRepair, declineRepair, rejectFinding, redoRepair, addCondition, editReading, removeReading, umbrella };
  const answers = haltAnswerFlags(halt);
  if (answers.length > 0 && !resume) throw usageError(`${answers.join(", ")} requires --resume.`);
  const conflict = haltAnswerConflict(halt);
  if (conflict) throw usageError(conflict);

  // `--stop --slug <s>` names its run by the slug: no paper is read. A run resumed (`--resume`) by its slug
  // alone reads the paper it was launched on (`runVerifyCli`).
  const [input = (stop || resume) && slug !== null ? "" : undefined, extra] = args;
  if (input === undefined || input.startsWith("-")) {
    throw usageError(stop ? "--stop needs the run: --slug <s>, or the paper it was launched on." : "Missing <paper.tex|dir|archive> (a run taken up again by --slug alone reads the one it was launched on).");
  }
  if (extra !== undefined) {
    throw usageError(`Unexpected argument: ${extra}`);
  }

  let targets: string[] | null = null;
  if (targetsRaw !== null) {
    targets = targetsRaw
      .split(",")
      .map((t) => t.trim())
      .filter((t) => t.length > 0);
    if (targets.length === 0) {
      throw usageError("--targets is empty; give a comma-separated list of theorem labels.");
    }
  }

  const parseStage = (flag: string, raw: string | null): VerifyFromStage | null => {
    if (raw === null) return null;
    if (!(VERIFY_FROM_STAGES as readonly string[]).includes(raw)) {
      throw usageError(
        `${flag} ${raw} is not a verify stage (expected one of ${flag === "--from-stage" ? FROM_STAGE_USAGE : STOP_AFTER_USAGE}).`,
      );
    }
    return raw as VerifyFromStage;
  };
  const fromStage = parseStage("--from-stage", fromStageRaw);
  const stopAfter = parseStage("--stop-after", stopAfterRaw);
  if (fromStage) {
    const refusal = fromStageRefusal(fromStage as StageHaltId);
    if (refusal) throw usageError(refusal);
  }
  if (stopAfter) {
    const refusal = stopAfterRefusal(stopAfter as StageHaltId);
    if (refusal) throw usageError(refusal);
  }
  if (freshReview && fromStage !== "V1" && fromStage !== "V1.5") {
    throw usageError("--fresh-review needs --from-stage V1 or V1.5 (it re-grades every node at the next V1.5).");
  }
  if (fromStage && stopAfter && stageIndex(stopAfter) < stageIndex(fromStage)) {
    throw usageError(`--stop-after ${stopAfter} precedes --from-stage ${fromStage}; nothing would run.`);
  }

  if (stop) {
    const others = Object.entries({ resume, auto: autoFlag, debug, fullAuto, deferProposals, dryRun, freshReview, fromTranscript, main, targets, fromStage, stopAfter, answers: answers.length > 0, clearGates: clearGates.length > 0 })
      .filter(([, v]) => v !== false && v !== null)
      .map(([k]) => k);
    if (others.length > 0) throw usageError(`--stop combines only with --toolkit and --slug (got ${others.join(", ")}).`);
  }
  if (answers.length > 0 && fromStage) throw usageError(`${answers.join(", ")} answers a halt; it does not combine with --from-stage.`);
  // The source is prepared at a cold start only; the scope may change with a new transcription.
  if (main !== null && (resume || fromStage)) throw usageError("--main names the main file of a new run; it does not combine with --resume or --from-stage.");
  if (targets !== null && (resume || fromStage) && fromStage !== "V1") throw usageError("--targets sets the scope of a transcription: give it at a cold start or with --from-stage V1, not with a plain --resume.");
  if (fromTranscript) {
    if (!resume) throw usageError("--from-transcript requires --resume (it re-enters an existing run).");
    if (fromStage || freshReview) throw usageError("--from-transcript already re-enters at a fresh V1.5; it does not combine with --from-stage or --fresh-review.");
    if (answers.length > 0) throw usageError(`--from-transcript clears every halt; it does not combine with ${answers.join(", ")}.`);
  }
  return { input, toolkit, slug, main, targets, resume, fromStage, stopAfter, clearGates, freshReview, fromTranscript, rejectRewind, clearPatchCap, acceptCap, acceptRepair, declineRepair, redoRepair, rejectFinding, addCondition, editReading, removeReading, umbrella, auto, debug, fullAuto, deferProposals, dryRun, stop };
}

function stageIndex(stage: VerifyFromStage): number {
  return VERIFY_FROM_STAGES.indexOf(stage);
}

/** Test-only access to the `paperformalizer verify` parser. */
export function parseVerifyArgsForTest(argv: string[]): VerifyArgs {
  return parseVerifyArgs(argv);
}

/**
 * Run id of a verify run: the slug, taken from `--slug`, else from the input's basename minus
 * its extension. The slug is lowercased, every run of non-`[a-z0-9]` characters becomes `_`,
 * leading/trailing `_` are dropped, and it is capped at `VERIFY_SLUG_MAX`. The result is checked
 * by the same path-segment guard every run id passes, so a hostile filename cannot escape
 * `runs/`.
 */
export function deriveVerifyQid(input: string, slugOverride: string | null): string {
  const raw = slugOverride ?? path.basename(input).replace(/\.[^.]+$/, "");
  const slug = raw
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "_")
    .replace(/^_+|_+$/g, "")
    .slice(0, VERIFY_SLUG_MAX)
    .replace(/_+$/, "");
  if (slug === "") {
    throw usageError(
      `Cannot derive a run slug from '${slugOverride ?? input}' (no alphanumeric characters). ` +
        "Pass --slug <name>.",
    );
  }
  return assertQidSlug(slug);
}

/** Run the paper-verification pipeline behind `paperformalizer verify`. */
export async function runVerifyCli(argv: string[]): Promise<void> {
  applyWorkerEnv();
  applyAuthEnv();
  const parsed = parseVerifyArgs(argv);
  const toolkit = loadToolkitConfig({ explicit: parsed.toolkit });
  if (parsed.stop) {
    await stopRecordedRun(childrenPath(toolkit.toolkitRoot, deriveVerifyQid(parsed.input, parsed.slug)));
    return;
  }
  if (parsed.input === "") {
    // the run's own paper, as its state records it
    const recorded = existsSync(statePath(toolkit.toolkitRoot, parsed.slug!)) ? (await loadState(toolkit.toolkitRoot, parsed.slug!)).verify?.source?.input : undefined;
    if (!recorded) throw usageError(`run ${parsed.slug} records no paper to resume from: give <paper.tex|dir|archive>.`);
    parsed.input = recorded;
  }
  assertLeanProjectOverride(toolkit);
  // Fail closed before any work: F5 needs the `paper_index` exe, retrieval the `toolkit_index` one.
  assertToolkitLakefile(toolkit);
  const qid = deriveVerifyQid(parsed.input, parsed.slug);
  console.log(`[paperformalizer] toolkit: ${toolkit.toolkitRoot} (from ${toolkit.source}); run: ${qid}`);

  // Refuse a dry/live mode mismatch before the Lean warm-up or any model call (the runner
  // checks again; this only moves the refusal ahead of the expensive start-up).
  if (existsSync(statePath(toolkit.toolkitRoot, qid))) {
    const refusal = dryRunRefusal(await loadState(toolkit.toolkitRoot, qid), parsed.dryRun, { fromStage: parsed.fromStage });
    if (refusal) throw new Error(refusal);
  }

  // One runner per run, for its whole life (V stages, halts and resumes included): a second
  // `verify` on the same slug is refused before it touches the run's files.
  const { withRunHeartbeat } = await import("../shared/run_heartbeat.js");
  await withRunHeartbeat(toolkit.toolkitRoot, qid, () => runVerifyLocked(parsed, toolkit, qid));
}

async function runVerifyLocked(
  parsed: ReturnType<typeof parseVerifyArgs>,
  toolkit: ReturnType<typeof loadToolkitConfig>,
  qid: string,
): Promise<void> {
  // From here every child is recorded, so `verify … --stop` can clean up after a crash.
  setChildrenFile(childrenPath(toolkit.toolkitRoot, qid));

  const { startSharedLeanLsp } = await import("../shared/lean_lsp_server.js");

  // Fail fast before a cold lean-lsp stage parks on a from-scratch build.
  if (!parsed.dryRun) await warmUpLeanOrThrow(toolkit.leanProjectPath, "verify");

  // Pay the lean-lsp cold start once and share it across the whole run.
  let shared: Awaited<ReturnType<typeof startSharedLeanLsp>> | null = null;
  const ownsSharedLeanLsp = !sharedLeanLspUrl();
  if (ownsSharedLeanLsp && !parsed.dryRun) {
    try {
      shared = await startSharedLeanLsp(toolkit.leanProjectPath);
      setSharedLeanLspUrl(shared.url);
    } catch {
      shared = null;
    }
  }
  try {
    const verify = await runVerifyPipeline({
      toolkit,
      qid,
      input: parsed.input,
      mainHint: parsed.main,
      targets: parsed.targets,
      resume: parsed.resume,
      fromStage: parsed.fromStage,
      stopAfter: parsed.stopAfter,
      clearGates: parsed.clearGates,
      auto: parsed.auto,
      ...(parsed.fullAuto ? { fullAuto: true } : {}),
      ...(parsed.deferProposals ? { deferProposals: true } : {}),
      dryRun: parsed.dryRun,
      freshReview: parsed.freshReview,
      ...(parsed.fromTranscript ? { fromTranscript: true } : {}),
      rejectRewind: parsed.rejectRewind,
      clearPatchCap: parsed.clearPatchCap,
      acceptCap: parsed.acceptCap,
      acceptRepair: parsed.acceptRepair,
      declineRepair: parsed.declineRepair,
      redoRepair: parsed.redoRepair,
      rejectFinding: parsed.rejectFinding,
      ...(parsed.addCondition ? { addCondition: parsed.addCondition } : {}),
      ...(parsed.editReading ? { editReading: parsed.editReading } : {}),
      ...(parsed.removeReading ? { removeReading: parsed.removeReading } : {}),
      ...(parsed.umbrella ? { umbrella: parsed.umbrella } : {}),
    });
    console.log(
      `PaperFormalizer verify ${parsed.dryRun ? "dry-run " : ""}${qid} finished in phase ${verify.phase}.`,
    );
    if (parsed.dryRun) console.log(dryRunLeftover(verifyRunDir(toolkit.toolkitRoot, qid)));
  } finally {
    if (ownsSharedLeanLsp && shared) {
      try {
        await shared.stop();
      } catch {
        /* best-effort teardown */
      }
      clearSharedLeanLspUrl();
    }
  }
}
