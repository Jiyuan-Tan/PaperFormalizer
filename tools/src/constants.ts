import { MODELS } from "./models.js";

/**
 * The run's stage cursor (`state.stage_completed`), in order. `"init"` is the seed value (no
 * stage completed yet; `state.verify.phase` is `"init"`). The V stages are owned by the verify
 * runner (`verify/pipeline.ts`); the F stages `1 … 5` keep their bare-number ids so the F-stage
 * code and on-disk state stay stable; `"V6"` is recorded once the report is written.
 */
export const STAGE_ORDER = [
  "init",
  "V1",
  "V1.5",
  "1",
  "1.5",
  "2",
  "2.5",
  "3",
  "3.5",
  "4",
  "5",
  "V6",
] as const;

/** The F stages the F runner (`pipeline.ts`) dispatches, in order. */
export const F_STAGES = ["1", "1.5", "2", "2.5", "3", "3.5", "4", "5"] as const;

/** A cursor value (`state.stage_completed`): one of `STAGE_ORDER`. */
export type CursorStage = (typeof STAGE_ORDER)[number];

export const MODEL_PLAN = {
  // Shared "mechanical / clerical" codex tier (default gpt-6.1-sol, env THEOREMCHECKER_MODEL_CODEX_MECH).
  // Not a stage: V1 passes `MODEL_PLAN.mechanicalTier.model` for its extraction calls.
  mechanicalTier: { runner: "codex", model: MODELS.codexMechanical, effort: "high" },
  stage1: { runner: "claude", model: MODELS.claudeMain },
  // F1.5 review: plan DEPTH + REUSE + statement-vs-math
  // fidelity audit, on the mechanical tier at high effort. Env: THEOREMCHECKER_MODEL_CODEX_MECH.
  stage1_5: { runner: "codex", model: MODELS.codexMechanical, effort: "high" },
  stage2: { runner: "codex", model: MODELS.codexKernel, effort: "high" },
  // F2.5/F3/F3.5/F4 are the proof-review loop (`proof_reviewer.ts::runUnit` routes its
  // reviewers: codexKernel with per-target high/medium effort); no plan entry here.
  // F5 (doc-generation pass): clerical → mechanical tier.
  stage5: { runner: "codex", model: MODELS.codexMechanical, effort: "medium" },
} as const;

/**
 * Display/CLI-facing stage ids: the V stages as themselves, the F stages with an `F` prefix.
 * What logs print (`formatStageLabel`); `--from-stage` and `--stop-after` take the ones
 * `fromStageRefusal` / `stopAfterRefusal` admit (`FROM_STAGE_USAGE`, `STOP_AFTER_USAGE`). The internal cursor keeps bare numbers for the F
 * stages so on-disk state stays stable.
 */
export const STAGE_HALT_IDS = [
  "V1",
  "V1.5",
  "F1",
  "F1.5",
  "F2",
  "F2.5",
  "F3",
  "F3.5",
  "F4",
  "F5",
  "V6",
] as const;

export type StageHaltId = (typeof STAGE_HALT_IDS)[number];

/** Internal cursor stage → display id (`"init"` has no halt id and prints as itself). */
export const STAGE_TO_HALT_ID: Record<Exclude<(typeof STAGE_ORDER)[number], "init">, StageHaltId> = {
  V1: "V1",
  "V1.5": "V1.5",
  "1": "F1",
  "1.5": "F1.5",
  "2": "F2",
  "2.5": "F2.5",
  "3": "F3",
  "3.5": "F3.5",
  "4": "F4",
  "5": "F5",
  V6: "V6",
};

/** Display id → internal cursor stage (the `--from-stage` / `--stop-after` mapping). */
export const STAGE_HALT_ID_TO_INTERNAL: Record<StageHaltId, Exclude<(typeof STAGE_ORDER)[number], "init">> = {
  V1: "V1",
  "V1.5": "V1.5",
  F1: "1",
  "F1.5": "1.5",
  F2: "2",
  "F2.5": "2.5",
  F3: "3",
  "F3.5": "3.5",
  F4: "4",
  F5: "5",
  V6: "V6",
};

/**
 * `--stop-after` values that can never fire: the combined proof-review handler dispatched at
 * F2.5 owns F2.5/F3/F3.5/F4 and completes as F4 (or checkpoints back at F2), so the runner never
 * settles at F2.5, F3 or F3.5.
 */
export const UNSTOPPABLE_HALT_IDS: ReadonlySet<StageHaltId> = new Set<StageHaltId>(["F2.5", "F3", "F3.5"]);

/** Why `--stop-after <id>` is refused, or null when it is accepted. */
export function stopAfterRefusal(id: StageHaltId): string | null {
  if (!UNSTOPPABLE_HALT_IDS.has(id)) return null;
  return (
    `--stop-after ${id} can never fire: F2.5, F3 and F3.5 run inside the combined proof-review ` +
    "loop, which completes as F4. Use --stop-after F2 (halt before the loop) or --stop-after F4 " +
    "(halt after it)."
  );
}

/**
 * `--from-stage` values no handler runs: F3, F3.5 and F4 are phases of the proof-review loop the F
 * runner dispatches at F2.5 (`formalization/dispatcher.ts`), never entry points of their own.
 */
export const UNENTERABLE_HALT_IDS: ReadonlySet<StageHaltId> = new Set<StageHaltId>(["F3", "F3.5", "F4"]);

/** The values `--from-stage` and `--stop-after` take, as every usage line and message prints them. */
export const FROM_STAGE_USAGE = STAGE_HALT_IDS.filter((s) => !UNENTERABLE_HALT_IDS.has(s)).join("|");
export const STOP_AFTER_USAGE = STAGE_HALT_IDS.filter((s) => !UNSTOPPABLE_HALT_IDS.has(s)).join("|");

/** `theoremchecker study`, as its own usage error and the top-level usage print it. */
export const STUDY_SYNOPSIS = "theoremchecker study <slug> [--toolkit <path>] [--resume] [--clear-build-cap] [--clear-review-cap] [--clear-coordinate-cap] [--dry-run]";

/** Why `--from-stage <id>` is refused, or null when it is accepted. */
export function fromStageRefusal(id: StageHaltId): string | null {
  if (!UNENTERABLE_HALT_IDS.has(id)) return null;
  return (
    `--from-stage ${id} is not an entry point: F3, F3.5 and F4 are phases of the proof-review ` +
    `loop, which starts at F2.5. A rewind can start at ${FROM_STAGE_USAGE}; use --from-stage F2.5 to run the loop again.`
  );
}

/**
 * Format a cursor stage as its display id. Use this in log strings instead of interpolating
 * raw stage literals. Examples: `"3"` → `"F3"`, `"V1.5"` → `"V1.5"`, `"init"` → `"init"`.
 */
export function formatStageLabel(stage: CursorStage): string {
  if (stage === "init") return "init";
  // A value outside STAGE_ORDER can only come from a bug or a hand-edited state; print it raw.
  return STAGE_TO_HALT_ID[stage] ?? String(stage);
}

/** Resolve a user-supplied stage token (`V1`, `F2.5`, …) to a display id; null when unknown. */
export function resolveStageHaltId(token: string): StageHaltId | null {
  return (STAGE_HALT_IDS as readonly string[]).includes(token) ? (token as StageHaltId) : null;
}
