// tools/src/substrate/state.ts
import { existsSync } from "node:fs";
import { mkdir, readFile, rename, writeFile } from "node:fs/promises";
import path from "node:path";
import { requirementPath, substrateStatePath } from "./paths.js";
import { substrateStateSchema, type SubstrateState } from "./types.js";

export function createInitialSubstrateState(slug: string): SubstrateState {
  return {
    slug,
    phase: "build",
    buildRounds: 0,
    reviewRounds: 0,
    coordinateRounds: 0,
    lastCoordinateLog: null,
    moduleFiles: [],
    pendingPrompts: [],
    lastReport: null,
    lastReview: null,
    terminalMessage: null,
    terminalRequirementHash: null,
    terminalEscalationKind: null,
    requirementVersion: 0,
    pendingApply: null,
  };
}

export async function substrateStateExists(repoRoot: string, slug: string, dryRun = false): Promise<boolean> {
  return existsSync(substrateStatePath(repoRoot, slug, dryRun));
}

export async function loadSubstrateState(repoRoot: string, slug: string, dryRun = false): Promise<SubstrateState> {
  const file = substrateStatePath(repoRoot, slug, dryRun);
  return substrateStateSchema.parse(JSON.parse(await readFile(file, "utf8")));
}

export async function saveSubstrateState(repoRoot: string, slug: string, state: SubstrateState, dryRun = false): Promise<void> {
  const file = substrateStatePath(repoRoot, slug, dryRun);
  await mkdir(path.dirname(file), { recursive: true });
  const tmp = `${file}.tmp`;
  await writeFile(tmp, `${JSON.stringify(state, null, 2)}\n`, "utf8");
  await rename(tmp, file);
}

/** The caps a study halts at, each with the flag that re-opens it and the phase it re-opens in. */
const STUDY_CAPS = [
  { name: "BUILD_CAP", flag: "--clear-build-cap", opt: "clearBuildCap", phase: "build", rounds: "buildRounds" },
  { name: "REVIEW_CAP", flag: "--clear-review-cap", opt: "clearReviewCap", phase: "build", rounds: "reviewRounds" },
  { name: "COORD_CAP", flag: "--clear-coordinate-cap", opt: "clearCoordinateCap", phase: "coordinate", rounds: "coordinateRounds" },
] as const;
export type StudyCapOptions = { clearBuildCap?: boolean; clearReviewCap?: boolean; clearCoordinateCap?: boolean };

/** The cap a halted study stopped at, by its message; null when it is not halted at one. */
function studyCapOf(state: Pick<SubstrateState, "phase" | "terminalMessage">): (typeof STUDY_CAPS)[number] | null {
  if (state.phase !== "halted") return null;
  return STUDY_CAPS.find((c) => state.terminalMessage?.startsWith(`Reached ${c.name}`)) ?? null;
}

/** Apply the `--clear-*-cap` flags of an invocation: each must name the cap the study is halted at
 * (all checked before the state is touched). True when the state changed. */
export function clearStudyCap(state: SubstrateState, opts: StudyCapOptions): boolean {
  const asked = STUDY_CAPS.filter((c) => opts[c.opt]);
  if (asked.length === 0) return false;
  const at = studyCapOf(state);
  const wrong = asked.find((c) => c !== at);
  if (wrong) throw new Error(`${wrong.flag} requires a study halted at ${wrong.name}${at ? ` (this one is halted at ${at.name}: ${at.flag})` : ""}`);
  state.phase = at!.phase;
  state[at!.rounds] = 0;
  state.terminalMessage = null;
  return true;
}

/**
 * What continues a study that did not end `done`, as a sentence naming the command: every stop of
 * a study has one. A plain `--resume` returns a halted or escalated study as it stands, so it is
 * the exit only of a study interrupted mid-phase.
 */
export function studyExit(state: Pick<SubstrateState, "phase" | "terminalMessage" | "terminalEscalationKind">, slug: string, toolkitRoot: string): string {
  if (state.phase === "done") return "";
  const cmd = (flags: string): string => `theoremchecker study ${slug} --resume${flags} --toolkit ${toolkitRoot}`;
  const cap = studyCapOf(state);
  if (cap) return `Grant one more window with \`${cmd(` ${cap.flag}`)}\` (the staged Lean is kept; a second grant is the signal to stop), or leave the study.`;
  if (state.phase === "halted") return "Correct what the message names and run the command again (nothing was recorded).";
  if (state.phase === "escalated" && state.terminalEscalationKind === "scaffolder") {
    return `Correct ${requirementPath(toolkitRoot, slug)} as the escalation asks, then \`${cmd("")}\`: it re-opens only when the requirement changed.`;
  }
  if (state.phase === "escalated") return "No flag re-opens it: settle the toolkit by hand as the message says (a resume returns this state as it stands).";
  return `It was interrupted in phase ${state.phase}: continue with \`${cmd("")}\`.`;
}
