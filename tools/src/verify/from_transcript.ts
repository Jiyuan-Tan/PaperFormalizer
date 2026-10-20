/**
 * `--resume --from-transcript`: re-run a paper under the CURRENT design while reusing its finished
 * V1 transcription (2026-09-25).
 *
 * A run reviewed, repaired and formalized under an older design carries everything that design
 * derived from the transcription: patches, carried verdicts, the paper-error ledger, owner receipts,
 * F-stage artefacts. This entry keeps only what V1 produced from the source — the transcription
 * (`core.transcribed.json`), the flattened paper and its line map, the environments, the reference
 * core, the scope and V1's lint list — and puts the run where V1 just completed: `core.json` is the
 * plain transcription again, the next step is a FRESH V1.5 (every node and symbol graded; sharded
 * per the toolkit config), and every later stage runs afresh from it. Nothing is deleted: what is
 * cleared is moved under `runs/<slug>/_archive/from_transcript_<stamp>/` (paths kept), with the
 * state as it stood.
 *
 * Refused when the transcription cannot be vouched for: it is missing, V1 never completed or is
 * mid-revision (a transcribe directive on file), the source tree no longer hashes as seeded, or the
 * transcript differs from the one V1.5 accepted (`transcribed_sha256`) — or, when no hash was ever
 * recorded, the source no longer flattens to the `flat.tex` the transcript was cut from.
 *
 * Owner rulings stay binding (the transcription they rule on is unchanged): the owner's pinned
 * readings (`patches.json` `owner_readings`, `ass:pin-owner-<n>` / `ass:bk-owner-<n>`), the owner's
 * withdrawals (`rejected_rewinds` with `by: "owner"`) and the ledger entries they withdrew.
 */
import { existsSync } from "node:fs";
import { copyFile, mkdir, readFile, rename } from "node:fs/promises";
import path from "node:path";
import { parseTypedCore } from "../core/core_io.js";
import type { Core } from "../core/schema.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import { createVerifyInitialState } from "../state.js";
import type { StateJson } from "../types.js";
import { sha256File } from "./core_hash.js";
import { isWithdrawn, readPatchFile, rebuildPatchedCore } from "./patches.js";
import { FIXER_HISTORY_FILE } from "./fixer_history.js";
import { hashSourceTree } from "./source_bundle.js";
import { flattenTex, recordedNoteMacros } from "./tex_envs.js";
import { VERIFY_FILES, type PaperError } from "./types.js";

/** Where a `--from-transcript` entry sets aside what it clears. */
export function fromTranscriptArchiveDir(runDir: string, at: string): string {
  return path.join(runDir, "_archive", `from_transcript_${at.replace(/[:.]/g, "-")}`);
}

/** What the transcription alone does not determine: moved into the archive (run-relative paths).
 * The V1 outputs (`flat.tex`, `flat.linemap.json`, `envs.json`, `core_refs.json`, `v1_scope.json`,
 * `v1_lint_warnings.json`, `core.transcribed.json`), the source and the run's logs stay. */
export const FROM_TRANSCRIPT_ARCHIVED: readonly string[] = [
  // Derived from the old review and repair loop.
  VERIFY_FILES.coreJson,
  `${VERIFY_FILES.coreJson}.prev`,
  VERIFY_FILES.patches,
  `${VERIFY_FILES.patches}.prev`,
  VERIFY_FILES.v15Review,
  VERIFY_FILES.v15RefereeMetrics,
  VERIFY_FILES.v15Symbols,
  VERIFY_FILES.v1ReviseDirective,
  VERIFY_FILES.v1PendingReply,
  FIXER_HISTORY_FILE,
  // The annotated paper of the old verdicts (and its pre-rename folder).
  "annotated",
  "annotated_preview",
  // Everything from F1 on.
  "formalization",
  "proposals",
  "reviews",
  "graph.json",
  VERIFY_FILES.reportJson,
  VERIFY_FILES.reportMd,
  "SUBSTRATE_DEBT.md",
  "MISSING_ARCHITECTURE.md",
];

export interface FromTranscriptSummary {
  /** The archive directory (absolute). */
  archiveDir: string;
  /** Run-relative paths moved into the archive. */
  archived: string[];
  /** Node counts of the restored core. */
  restored: { statements: number; assumptions: number; definitions: number; symbols: number };
  /** Node counts of the core it replaced (null: none on file). */
  replaced: { statements: number; assumptions: number; definitions: number; symbols: number } | null;
  /** Owner rulings kept: pinned readings, withdrawals, withdrawn ledger entries. */
  kept: { ownerReadings: number; ownerWithdrawals: number; withdrawnLedger: number };
  /** How the transcript was vouched for. */
  check: string;
}

const countsOf = (c: Pick<Core, "statements" | "assumptions" | "definitions" | "symbols">): FromTranscriptSummary["restored"] => ({
  statements: c.statements.length,
  assumptions: c.assumptions.length,
  definitions: c.definitions.length,
  symbols: c.symbols.length,
});

/** The one-line summary the runner logs. */
export function fromTranscriptLine(s: FromTranscriptSummary, runDir: string): string {
  const n = (c: FromTranscriptSummary["restored"]): string => `${c.statements} statements, ${c.assumptions} assumptions, ${c.definitions} definitions, ${c.symbols} symbols`;
  const kept = s.kept.ownerReadings + s.kept.ownerWithdrawals + s.kept.withdrawnLedger;
  return (
    `--from-transcript: ${VERIFY_FILES.coreJson} restored from ${VERIFY_FILES.coreTranscribed} (${n(s.restored)}` +
    `${s.replaced ? `; replaced ${n(s.replaced)}` : ""}); ${s.check}; archived ${s.archived.length} path(s) to ` +
    `${path.relative(runDir, s.archiveDir)} (${s.archived.join(", ") || "nothing"}); state reset to V1 complete — ` +
    `next: a fresh V1.5 (every node and symbol graded)` +
    (kept > 0 ? `; owner rulings kept: ${s.kept.ownerReadings} pinned reading(s), ${s.kept.ownerWithdrawals} withdrawal(s), ${s.kept.withdrawnLedger} withdrawn ledger entr${s.kept.withdrawnLedger === 1 ? "y" : "ies"}` : "")
  );
}

/**
 * Why this run cannot re-enter from its transcript, or null when it can; `check` says how the
 * transcript was vouched for. Reads only.
 */
export async function fromTranscriptRefusal(runDir: string, state: StateJson): Promise<{ refusal: string; check?: never } | { refusal: null; check: string }> {
  const verify = state.verify;
  const refuse = (why: string): { refusal: string } => ({ refusal: `--from-transcript: ${why}` });
  if (!verify) return refuse("the state has no `verify` block — this is not a verify run.");
  const transcribedPath = path.join(runDir, VERIFY_FILES.coreTranscribed);
  if (!existsSync(transcribedPath)) {
    return refuse(`no ${VERIFY_FILES.coreTranscribed} on file — there is no finished transcription to reuse. Re-run V1 (\`--from-stage V1\`).`);
  }
  if (state.stage_completed === "init") {
    return refuse(`V1 has not completed (stage_completed is "init"): the transcription on file is not a finished one. Continue with --resume.`);
  }
  const directivePath = path.join(runDir, VERIFY_FILES.v1ReviseDirective);
  if (verify.phase === "init" && existsSync(directivePath)) {
    let mode: unknown = null;
    try {
      mode = (JSON.parse(await readFile(directivePath, "utf8")) as { mode?: unknown }).mode;
    } catch {
      mode = "unreadable";
    }
    if (mode !== "patch") {
      return refuse(`the run is mid-V1: a transcription revise directive is on file (${VERIFY_FILES.v1ReviseDirective}, mode ${String(mode)}), so V1 is rewriting the transcription. Continue with --resume.`);
    }
  }
  for (const f of [VERIFY_FILES.flatTex, VERIFY_FILES.envsJson]) {
    if (!existsSync(path.join(runDir, f))) return refuse(`${f} is missing; the transcription cannot be reviewed without it. Re-run V1 (\`--from-stage V1\`).`);
  }
  try {
    parseTypedCore(await readFile(transcribedPath, "utf8"), `transcribed core ${transcribedPath}`);
  } catch (err) {
    return refuse(`${VERIFY_FILES.coreTranscribed} is not a readable core (${err instanceof Error ? err.message : String(err)}).`);
  }
  const sourceDir = path.join(runDir, VERIFY_FILES.sourceDir);
  const sourceSha = await hashSourceTree(sourceDir);
  const short = (h: string): string => h.slice(0, 12);
  if (sourceSha !== verify.source.sha256) {
    return refuse(`the source changed since it was transcribed (sha ${short(verify.source.sha256)} → ${short(sourceSha)}); the transcript is of another text. Re-extract with --from-stage V1.`);
  }
  if (verify.transcribed_sha256) {
    const sha = await sha256File(transcribedPath);
    if (sha !== verify.transcribed_sha256) {
      return refuse(
        `${VERIFY_FILES.coreTranscribed} differs from the transcript V1.5 accepted (sha ${short(verify.transcribed_sha256)} → ${short(sha)}): it was edited after the review. ` +
          "Re-review it as it stands with --from-stage V1.5 --fresh-review, or re-extract with --from-stage V1.",
      );
    }
    return { refusal: null, check: `source unchanged (sha ${short(sourceSha)}), transcript is the one V1.5 accepted (sha ${short(sha)})` };
  }
  // No accepted hash on file: recompute what V1 cut the transcript from.
  const flat = await flattenTex(sourceDir, verify.source.main_file, await recordedNoteMacros(runDir));
  const onDisk = await readFile(path.join(runDir, VERIFY_FILES.flatTex), "utf8");
  if (flat.text !== onDisk) {
    return refuse(`no accepted transcript hash is on file, and the source no longer flattens to ${VERIFY_FILES.flatTex} (the transcript's anchors may not hold). Re-extract with --from-stage V1.`);
  }
  return { refusal: null, check: `source unchanged (sha ${short(sourceSha)}) and it flattens to ${VERIFY_FILES.flatTex} as transcribed (no accepted transcript hash on file)` };
}

/**
 * Re-enter a run from its transcript (see the module comment). Checks first (throws the refusal),
 * then archives, resets `state` in place (the caller saves it) and rebuilds `core.json` from the
 * transcript (+ the owner's pinned readings). `voidRounds` runs after the state snapshot and before
 * the archive moves: the caller re-opens the accepted core there.
 */
export async function resetFromTranscript(args: {
  runDir: string;
  state: StateJson;
  papersLib?: string;
  voidRounds?: () => Promise<void>;
  now?: () => Date;
}): Promise<FromTranscriptSummary> {
  const { runDir, state } = args;
  const checked = await fromTranscriptRefusal(runDir, state);
  if (checked.refusal !== null) throw new Error(checked.refusal);
  const verify = state.verify!;

  const at = (args.now ?? (() => new Date()))().toISOString();
  const archiveDir = fromTranscriptArchiveDir(runDir, at);
  await mkdir(archiveDir, { recursive: true });
  // The state as it stood (before any void below touches it).
  const stateFile = path.join(runDir, "state.json");
  if (existsSync(stateFile)) await copyFile(stateFile, path.join(archiveDir, "state.json"));
  else await writeJsonAtomic(path.join(archiveDir, "state.json"), state);

  // Read what survives before its files move.
  const patchFile = existsSync(path.join(runDir, VERIFY_FILES.patches)) ? await readPatchFile(runDir) : null;
  const ownerReadings = patchFile?.owner_readings ?? [];
  let replaced: FromTranscriptSummary["replaced"] = null;
  const corePath = path.join(runDir, VERIFY_FILES.coreJson);
  if (existsSync(corePath)) {
    try {
      replaced = countsOf(JSON.parse(await readFile(corePath, "utf8")) as Core);
    } catch {
      replaced = null;
    }
  }

  await args.voidRounds?.();

  const archived: string[] = [];
  const move = async (rel: string): Promise<void> => {
    const from = path.join(runDir, rel);
    if (!existsSync(from)) return;
    const to = path.join(archiveDir, rel);
    await mkdir(path.dirname(to), { recursive: true });
    await rename(from, to);
    archived.push(rel);
  };
  for (const rel of FROM_TRANSCRIPT_ARCHIVED) await move(rel);
  // The F runner writes into these.
  await mkdir(path.join(runDir, "formalization"), { recursive: true });

  // The owner's pinned readings stay binding: the only content of the new patch file.
  if (ownerReadings.length > 0) {
    await writeJsonAtomic(path.join(runDir, VERIFY_FILES.patches), { key_results: [], key_contribution: "", patches: [], unfixable: [], owner_readings: ownerReadings });
  }

  // state.verify: as V1 left it, with the owner's rulings.
  const ownerWithdrawals = (verify.rejected_rewinds ?? []).filter((r) => r.by === "owner");
  const withdrawnLedger: Record<string, PaperError> = Object.fromEntries(Object.entries(verify.paper_errors ?? {}).filter(([, e]) => isWithdrawn(e)));
  for (const k of [
    "confirmed", "confirmed_symbols", "confirmed_scheme", "fixer_rejections", "weakening_repair", "level_pause", "cap_reached",
    "cross_stage_rewind", "render_checkpoint", "voided_receipts", "restatement_rounds", "last_drift",
  ] as const) {
    delete verify[k];
  }
  verify.paper_errors = withdrawnLedger;
  if (ownerWithdrawals.length > 0) verify.rejected_rewinds = ownerWithdrawals;
  else delete verify.rejected_rewinds;
  verify.patch_rounds = 0;
  verify.patch_rounds_by_level = {};
  verify.refinement_rounds = 0;
  verify.v1_5_rounds = 0;
  verify.v1_5_rounds_by_node = {};
  verify.suggestion_rejections = {};
  verify.findings = [];
  verify.core_sha256 = null;
  verify.transcribed_sha256 = null;
  verify.report_path = null;
  // V1 just completed: the next step is V1.5.
  verify.phase = "v1";

  // Top level: everything the F stages wrote goes back to its seed value.
  const seed = createVerifyInitialState(state.qid ?? "run", verify, args.papersLib);
  const mutable = state as unknown as Record<string, unknown>;
  delete mutable.theorems;
  state.design_decisions = seed.design_decisions;
  state.added_assumptions = seed.added_assumptions;
  state.cited_checks = seed.cited_checks;
  mutable.cited_review_receipts = [];
  state.delivery_review_receipts = seed.delivery_review_receipts;
  state.flags = seed.flags as StateJson["flags"];
  state.stage_completed = "V1";

  // core.json := the transcription (+ the owner's pins), exactly as V1 materializes it.
  await rebuildPatchedCore(runDir, { detectHandEdits: false });
  const restored = countsOf(JSON.parse(await readFile(corePath, "utf8")) as Core);

  return {
    archiveDir,
    archived,
    restored,
    replaced,
    kept: { ownerReadings: ownerReadings.length, ownerWithdrawals: ownerWithdrawals.length, withdrawnLedger: Object.keys(withdrawnLedger).length },
    check: checked.check,
  };
}
