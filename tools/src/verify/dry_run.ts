// Dry-run / live separation of a verify run. A dry run's V1.5 "accepts" a core no referee read
// and its F stages dispatch nothing, so a state a dry run seeded or advanced must never be taken
// for a live one: every dry-run seed sets `state.verify.dry_run = true`, and the live runners
// (the verify runner, the F runner, `assertFStageEntryCoherence`) refuse such a state. The
// converse holds too: a dry run never touches a live state (it would overwrite real progress).
import type { StateJson } from "../types.js";

/**
 * Why a run in mode `dryRun` may not continue `state`, or null when it may. `fromStage: "V1"`
 * lets a LIVE run take over a dry-run state (re-extraction from scratch replaces everything the
 * dry run wrote; the caller clears the flag). No other entry converts a dry state into a live one.
 */
export function dryRunRefusal(
  state: Pick<StateJson, "verify" | "qid">,
  dryRun: boolean,
  opts: { fromStage?: string | null } = {},
): string | null {
  const verify = state.verify;
  if (!verify) return null;
  if (verify.dry_run === true && !dryRun) {
    if (opts.fromStage === "V1") return null;
    return (
      `run ${state.qid} was seeded or advanced by --dry-run: its V1.5 acceptance and F stages are ` +
      "synthetic, so a live run cannot continue it. Re-run without --dry-run from V1 " +
      "(`--from-stage V1`), or use a fresh --slug."
    );
  }
  if (verify.dry_run !== true && dryRun) {
    return (
      `run ${state.qid} is a live run; --dry-run never continues or rewinds a live state ` +
      "(it would overwrite real progress). Use a fresh --slug for the dry run."
    );
  }
  return null;
}

/** The last line of a dry run: what it left on disk (nothing else names it, and no live run may reuse it). */
export function dryRunLeftover(runDir: string): string {
  return `(dry run: it wrote ${runDir} — nothing there is a result; delete the directory when you are done.)`;
}
