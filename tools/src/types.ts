import type { CursorStage } from "./constants.js";

/** A stage-cursor value (`state.stage_completed`): see `STAGE_ORDER` in constants.ts. */
export type Stage = CursorStage;

export interface AddedAssumption {
  label: string;
  statement: string;
  source?: string;
  /** `.tex`/`.md` anchor the premise is claimed to match (the F3 filler adds). */
  anchor?: string;
  /**
   * Faithfulness class of the premise, on the crux-vs-gate axis:
   *  - `faithful-refinement`: the .tex already states/implies it in this setting.
   *  - `regularity-bookkeeping`: a measurability/integrability/finiteness side-condition.
   *  - `substrate-gate`: a genuinely classical, dischargeable fact (must be built before banking).
   */
  classification?: "faithful-refinement" | "regularity-bookkeeping" | "substrate-gate";
}

export interface MissingItem {
  kind: string;
  name_suggestion: string;
  purpose: string;
  why_substantial: string;
  nl_artifact_reference?: string;
  suggested_location?: string;
}

/**
 * `StateJson` is the intersection of shared and formalization fields: `SharedState` (cursor, Lean
 * directory, run block), review directives (`DiscoveryFlags`), and `FormalizationState` (assumptions, review receipts).
 */

/**
 * Review halts and orchestrator directives read or written by the F stages.
 */
export interface DiscoveryFlags {
  /** An F-stage escalation asked to rewind into D-1/D0, which a verify run has no stages for.
   *  Written by runs before 2026-10-07 (the F1.5 intervention judge's refused route); still
   *  read by the report and lifted with a receipt. */
  verify_no_d_rewind?: string | null;
  /** Why a review boundary halted for the orchestrator (`runReviewBoundary`; a cap gate). */
  general_review_halt?: string | null;
  /**
   * F3 phase-B proof-fill directive: a load-bearing PROOF hint the orchestrator injects into
   * every filler call until cleared in `state.json`. A proof hint only — the
   * anti-laundering and assumption/definition gates still reject any statement change.
   */
  f3_filler_directive?: string | null;
  /** Persistent orchestrator F2 scaffold directive (analogue of `f3_filler_directive`):
   *  read on every scaffold/revise pass as a top-priority faithfulness constraint,
   *  persists across resumes until cleared in `state.json`. */
  f2_scaffold_directive?: string | null;
}

/**
 * Drift verdict vocabulary, shared with the H.1 hypothesis matrix. `exact` /
 * `equivalent` pass; everything else is a blocking drift the F2.5 gate folds
 * into its findings.
 */
export type CrosswalkVerdict =
  | "exact"
  | "equivalent"
  | "stronger-in-Lean"
  | "weaker-in-Lean"
  | "missing-in-Lean"
  | "extra-in-Lean"
  | "encoding-drift"
  | "drift"
  | "unmatched"; // skeleton-only placeholder before the reviewer assigns a verdict

/**
 * One object in the F2.5 tex↔Lean crosswalk. The deterministic skeleton builder
 * fills every field EXCEPT `verdict`/`note` (left as
 * `unmatched`/empty); the codex reviewer fills those, keyed by `obj_id`. Durable
 * anchors are `obj_id` (.md/.tex side) and `(lean.file, lean.decl)` (Lean side);
 * `lean.line` and `tex.line_range` are convenience and re-derivable.
 */
export interface CrosswalkEntry {
  obj_id: string;
  kind: "definition" | "assumption" | "theorem" | "lemma" | "proposition";
  title: string;
  tex: { label: string; line_range: string };
  lean: { file: string; decl: string; decl_kind: string; line: number } | null;
  verdict: CrosswalkVerdict;
  note?: string;
}

/** Flag fields owned by the formalization half (Stages 2 … 5). */
export interface FormalizationFlags {
  missing_architecture: boolean;
  missing_architecture_items?: MissingItem[];
  /** Verbatim re-scaffold directive (the proof-review loop's, or the orchestrator's); consumed by runStage2 then cleared on success. */
  scaffold_redirect?: string | null;
  /** The plan-gate refusal (`code @ where`, sorted) F2 last sent back to F1; the same one again halts. Cleared when a sync-back passes. */
  plan_rewind_violations?: string | null;
  /** The proof-review loop's iteration budgets, PERSISTED across resumes. These used to be
   * in-process locals, so every `--resume` silently handed the loop a fresh budget — an
   * orchestrator could re-roll the (non-deterministic) reviewer indefinitely with no flag, no
   * audit trail, and no gate. Persisting them makes a cap a real circuit breaker. */
  proof_loop_counters?: {
    iters: number;
    scaffold_rounds: number;
    stale: number;
    tag_reroutes: number;
    node_strikes: Record<string, number>;
    /** Hash-keyed counts of identical F2.5 target+diagnostic signatures. */
    review_error_strikes: Record<string, number>;
    /** Hash of the last red `lake build` diagnostic, so the identically-red no-progress
     * cap survives a `--resume` instead of resetting `stale` on every re-entry. */
    last_build_error_sig?: string;
    /** Last few one-line filler session summaries (the anti-identical-prompt memory).
     * Persisted for the same reason as the counters: as an in-process local, every
     * `--resume` restarted Phase B with byte-identical filler prompts until new summaries
     * accumulated — the exact repeat-dead-end waste the memory exists to stop. */
    filler_summaries?: string[];
    /** Best proof measure the Lean tree reached in Phase B (open `sorry` tokens, proved
     * theorem/lemma declarations) and the `iters` count at which it was reached: the no-progress
     * cap counts iterations since. Absent until the first measurement (and in older state files). */
    progress_best?: { open: number; proved: number; iter: number };
  };
  /** Set when any `proof_loop_counters` budget is exhausted. BLOCKS `--resume` until cleared via
   * `--clear-gate proof_loop_cap_hit`. Only MAIN may clear it (a sub never resets its own cap). */
  proof_loop_cap_hit?: string;
  /**
   * Durable fail-closed record that the combined F2.5 proof-review loop returned
   * an escalation without converging. While present, the dispatcher must not
   * enter the retired F3/F3.5/F4 pass-through slots or F5. It is cleared only
   * after a genuine `runProofReviewLoop` completion.
   */
  proof_review_escalation_pending?: {
    route: string;
    reason: string;
    /** The reviewer's / filler's escalation kind and the node it names, when it came from one
     *  of them; the F phase (`"2.5"`, `"3"`, `"4"`) that raised it. */
    kind?: string;
    obj_id?: string;
    phase?: string;
    /** Every paper-statement finding the same review pass produced (the one above included),
     *  ruled on together as one rewind batch (`verify/cross_stage_rewind.ts`). */
    batch?: Array<{ route: string; reason: string; kind?: string; obj_id?: string }>;
  } | null;
  /** A re-plan directive for F1 (the runner's, or the orchestrator's); consumed by runStage1's revise mode then cleared. */
  f1_revise_directive?: string | null;
  /** F1 answered `blocked` and wrote no plan: its message, and the review it was correcting when
   *  that was inside the F1.5 loop. While set, the next F-stage entry plans again before any review
   *  (`runStage1_5`), and a halt at F1 / F1.5 prints the blocked-F1 reminder. Cleared by the F1
   *  pass that completes. */
  f1_blocked?: { message: string; review?: unknown } | null;
}

/** Cross-phase fields: stage cursor, target Lean directory, run block. */
export interface SharedState {
  /** Last completed stage (`STAGE_ORDER`); `"init"` on a freshly seeded run. */
  stage_completed: Stage;
  /** Paper Lean directory relative to the toolkit root, posix form: `Papers/<Pascal>`. */
  lean_subdir: string;
  /** The run id (the slug), stamped on every save (see `saveState`). */
  qid?: string;
  /**
   * Auto mode — the default (off under `verify --debug`), written by the verify runner from
   * `debug_mode` / `full_auto`. When true the orchestrator makes every checkpoint decision itself and
   * `--resume`s without asking the user; the owner's decisions stay theirs. Re-surfaced on every
   * checkpoint line (`checkpointGuidance`).
   */
  auto_mode?: boolean;
  /**
   * Debug mode — set by `verify --debug`: auto mode off, so the orchestrator may bring a checkpoint
   * ruling to the user. Latching: the run stays in debug mode across resumes.
   */
  debug_mode?: boolean;
  /**
   * Full auto — set by `verify --full-auto` (implies `auto_mode`). The owner delegates their own
   * decisions as well — a repair that would weaken a main result, the promotion rounds, any other
   * ruling that would weaken one: the agent's recommendation on each is applied once it has given
   * one on every item (`orch.mjs recommend`), and each is listed for the owner's review. Latching.
   */
  full_auto?: boolean;
  /** The CLI that runs this run's claude roles, recorded at the run's first decision and kept by
   *  a resume unless an explicit setting says otherwise (`claude_roles.ts`). */
  claude_roles?: "claude" | "codex";
  /**
   * The verify run block: the V-stage lifecycle cursor, the paper-source coordinates, and the
   * findings the V6 report renders. Required for every run; optional in the type only because
   * the schema must parse it before the runner checks it.
   */
  verify?: import("./verify/types.js").VerifyState;
}

/**
 * Formalization-phase fields (Stages 2 … 5): scaffold/proof bookkeeping,
 * assumption accumulation, free-form design notes. `design_decisions` is
 * formally cross-phase but in practice every writer lives in formalization
 * code paths, so it is owned here.
 */
/** One cited node's persisted F4 source-match verdict. See {@link FormalizationState.cited_checks}. */
export interface CitedCheck {
  name: string;
  check_status: string;
  cite_id?: string;
  locator?: string;
  reviewer?: "codex" | "claude";
}

/** Durable, source-bound proof that one F4 peer checked a delivered cited node.
 * Unlike the compatibility `cited_checks` summary, this preserves peer identity and locator. */
export interface CitedReviewReceipt {
  node_id: string;
  reviewer: "codex" | "claude";
  check_status: string;
  cite_id: string;
  locator: string;
  evidence_hash: string;
}

/** Durable proof that each F4 peer independently accepted one disclosed omission.
 * The evidence hash binds the receipt to the current plan/graph contribution evidence,
 * so changing a role, reason, or dependency closure invalidates an old receipt. */
export interface DeliveryReviewReceipt {
  node_id: string;
  reviewer: "codex" | "claude";
  verdict: "matched" | "drift";
  evidence_hash: string;
  note?: string;
}

export interface FormalizationState {
  design_decisions: Record<string, string>;
  added_assumptions: AddedAssumption[];
  /**
   * The F4 reviewer's CITED source-match verdicts. `cited-mismatch` / `cited-underspecified`
   * block delivery; the F5 delivery audit enforces that from `cited_review_receipts`, and this
   * per-node summary of them is read by no stage.
   *
   * Optional for backward compatibility: every state written before this field existed omits it,
   * and the Zod schema defaults it to `[]` on parse. Absent ⇒ no cited nodes ⇒ nothing to block.
   */
  cited_checks?: CitedCheck[];
  cited_review_receipts?: CitedReviewReceipt[];
  delivery_review_receipts?: DeliveryReviewReceipt[];
}

export interface StateJson
  extends SharedState,
    FormalizationState {
  flags: DiscoveryFlags & FormalizationFlags;
}

export interface PipelineContext {
  /** The toolkit root (= `toolkit.toolkitRoot`): every run record and Lean path resolves
   *  against it. Kept as its own field because the F-stage code reads it directly. */
  repoRoot: string;
  /**
   * The user's toolkit (Lean project, run records, base libraries), from `theoremchecker.json`.
   * Every runner populates it (the verify runner, the F runner's callers, the study CLI, the
   * operator bins).
   */
  toolkit: import("./toolkit/config.js").ToolkitConfig;
  /** The run id: the paper slug. */
  qid: string;
  dryRun: boolean;
  resume: boolean;
  /** Auto mode (the default; off under `verify --debug`): see `SharedState.auto_mode`. Persisted onto state. */
  auto?: boolean;
}

export interface StageResult {
  stage: Stage;
  /**
   * Loop-control semantics:
   *  - `completed` / `skipped`: pipeline advances to `nextStage(stage)`.
   *  - `checkpoint`: pipeline halts; user must `--resume`. Use when human input is needed before the next stage can run (genuine CKPTs, NO-PASS-with-user-action, a review boundary's halt).
   *  - `blocked`: pipeline halts; `state.flags` carries the block reason. Used for missing architecture (F2) and an unreadable note (F5).
   *  - `rewound`: handler programmatically reset `state.stage_completed` to an earlier marker; pipeline continues from `nextStage(state.stage_completed)`. Use when an escalation routes back to an earlier stage WITHOUT needing user input. `advance: false` MUST be set so the loop does not overwrite the handler's reset.
   */
  status: "completed" | "checkpoint" | "blocked" | "skipped" | "rewound";
  message: string;
  advance?: boolean;
  completedStage?: Stage;
}

export interface PipelineLogEntry {
  timestamp: string;
  stage: Stage | "resume" | "init";
  model?: string;
  status: string;
  duration_ms: number;
  message?: string;
  /**
   * Condensed orchestrator reminder for a checkpoint/blocked halt: what to do
   * at this checkpoint + what the next phase is, with a pointer to the canonical
   * SKILL section. Populated by `checkpointGuidance`; absent on ordinary
   * `completed` transitions. The theoremchecker skill tells the orchestrator
   * to read this on the last pipeline.jsonl line so it re-grounds after a long run.
   */
  next_step_guidance?: string;
}
