import type { StateJson } from "./types.js";

type StateFlags = StateJson["flags"];

/**
 * A cap / halt flag that BLOCKS `--resume` until the orchestrator deliberately
 * clears it. This registry is the single source of truth shared by:
 *
 *  - `resolveResumeGates` (pipeline.ts) — reads `flags[flag]`; if truthy it refuses
 *    the resume and surfaces `guidance`.
 *  - the `--clear-gate <flag>` resume option (`runVerifyPipeline`, as the run is entered) — calls
 *    `clear(flags)` as part of the resume, so the orchestrator NEVER hand-edits `state.json`. Hand-editing risks a
 *    Zod-invalid state that fails the NEXT resume; routing every flag flip through the CLI
 *    keeps the state schema-valid and the action auditable.
 *
 * Each `clear` nulls/undefines the blocking flag AND resets any paired counter (so the
 * cap does not immediately re-trip on the next pass).
 */
export interface CapGate {
  /** The flag key on `state.flags` that blocks resume while truthy. */
  flag: string;
  /** Clear the flag (+ reset any paired counter). */
  clear: (flags: StateFlags) => void;
  /** Halt-message guidance shown when the gate blocks a resume. */
  guidance: string;
}

/** The exits of a review-boundary halt (F1.5), each with `--clear-gate general_review_halt`. A
 *  plain resume is none of them: it is refused while the gate is set, and clearing the gate alone
 *  re-runs the reviewer on the same plan, with no record of a ruling. */
export const GENERAL_REVIEW_HALT_EXITS =
  "read the review (`reviews/`, the halt reason in pipeline.jsonl) and rule, each with `--clear-gate general_review_halt`: " +
  "a plan defect F1 did not fix → your directive in `flags.f1_revise_directive`, then `--resume --from-stage F1` (a fresh budget); " +
  "a finding you rule out → `--resume --from-stage F2` (past the review); " +
  "a defect in the paper's statement → record it (`discovery/patches.json`), then `--resume --from-stage V1.5`. " +
  "A plain resume is refused while the gate is set; `--resume --clear-gate general_review_halt` alone only re-runs the reviewer on the same plan";

/** Marks the proof loop's absolute iteration ceiling in its halt reason (`flags.proof_loop_cap_hit`). */
export const ITERATION_CEILING_TAG = "[iteration-ceiling]";

/** The exit of the iteration ceiling: unlike the other loop budgets, continuing is the user's call. */
export const ITERATION_CEILING_EXIT =
  "the proof loop reached its absolute iteration ceiling. A loop with a proof open that stops beating its records halts first, " +
  "on the no-progress budget, so this one ran out of iterations rather than stalling. Whether to continue is the USER's decision: " +
  "ask them (`orch.mjs ask`, with one line in the session), giving the measure the halt states, and wait — never stop the run " +
  "for good on your own, and never continue without their answer. Yes → `--resume --clear-gate proof_loop_cap_hit` (every loop " +
  "counter resets: a fresh budget of iterations); no → report the run as it stands. On a run the user started with `--full-auto`, decide it yourself";

export const CAP_GATES: CapGate[] = [
  {
    flag: "general_review_halt",
    clear: (f) => {
      f.general_review_halt = null;
    },
    guidance: GENERAL_REVIEW_HALT_EXITS,
  },
  {
    // Covers EVERY proof-review-loop iteration budget: iterations without measurable proof
    // progress and their absolute ceiling, Phase-A scaffold-reroute rounds, per-node strikes,
    // tag reroutes, and the no-progress bound. These were in-process
    // locals, so a plain `--resume` reset them all silently — unbounded, unaudited re-rolls of a
    // non-deterministic reviewer (laundering by resampling). Now persisted; only MAIN clears.
    flag: "proof_loop_cap_hit",
    clear: (f) => {
      f.proof_loop_cap_hit = undefined;
      f.proof_loop_counters = {
        iters: 0,
        scaffold_rounds: 0,
        stale: 0,
        tag_reroutes: 0,
        node_strikes: {},
        review_error_strikes: {},
        // Budgets reset; the filler's dead-end memory is NOT a budget — wiping it here
        // restarted the resumed loop cold on the same known blockers (audit, 2026-08-26).
        filler_summaries: f.proof_loop_counters?.filler_summaries ?? [],
      };
    },
    guidance:
      "a proof-loop iteration budget is exhausted. Do NOT simply re-resume — that is a re-roll, not a retry, and the reviewer is non-deterministic. Diagnose the ROOT cause first (scaffolder drifting → set `flags.f2_scaffold_directive` in state.json; the filler stuck on a proof it can be told how to close → a proof hint in `flags.f3_filler_directive`; reviewer wrong → fix the reviewer PROMPT as a pipeline-bug; plan wrong → rewind). Only once something at the root has CHANGED, resume with `--clear-gate proof_loop_cap_hit` (resets all loop counters). MAIN's authority only — a sub-orchestrator never resets its own cap.",
  },
];

/** How a missing-architecture block is left (it is no cap gate: the next resume re-checks it). */
export const MISSING_ARCHITECTURE_EXIT =
  "build each named declaration under the paper's own tree (its `suggested_location` in `flags.missing_architecture_items`), then `--resume`: the gate opens once every name is found in the toolkit, the papers tree or a base library. An item F2 does not need: delete it from `flags.missing_architecture_items` in state.json and say why in `flags.f2_scaffold_directive`";

/** The guidance for a set cap gate: the iteration ceiling has its own exit (the user decides). */
export function capGateGuidance(gate: CapGate, value: unknown): string {
  return gate.flag === "proof_loop_cap_hit" && String(value ?? "").includes(ITERATION_CEILING_TAG) ? ITERATION_CEILING_EXIT : gate.guidance;
}

/**
 * What refuses the next `--resume` of the F stages, as the halt prints it: the first set cap gate
 * with its `--clear-gate` exit, else a missing-architecture block; null when a resume would run.
 */
export function resumeBlock(flags: StateFlags): string | null {
  const rec = flags as unknown as Record<string, unknown>;
  for (const gate of CAP_GATES) {
    if (rec[gate.flag]) return `${gate.flag.toUpperCase()} BLOCKED: ${rec[gate.flag]}\nResolve: ${capGateGuidance(gate, rec[gate.flag])}.`;
  }
  if (!flags.missing_architecture) return null;
  const names = (flags.missing_architecture_items ?? []).map((item) => item.name_suggestion).join(", ");
  return `MISSING ARCHITECTURE BLOCKED: ${names || "(no item named)"}\nResolve: ${MISSING_ARCHITECTURE_EXIT}.`;
}

/** All clearable cap-gate flag names, for CLI validation + usage text. */
export const CAP_GATE_FLAGS: string[] = CAP_GATES.map((g) => g.flag);

/**
 * Clear a cap gate by flag name (mutates `flags`). Throws on an unknown name so the CLI
 * reports the valid set instead of silently no-op'ing. Returns the matched gate.
 */
export function clearCapGate(flags: StateFlags, name: string): CapGate {
  const gate = CAP_GATES.find((g) => g.flag === name);
  if (!gate) {
    throw new Error(
      `--clear-gate: unknown gate '${name}'. Known gates: ${CAP_GATE_FLAGS.join(", ")}`,
    );
  }
  gate.clear(flags);
  return gate;
}
