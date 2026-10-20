import { mkdir, readFile, rename, writeFile } from "node:fs/promises";
import { randomUUID } from "node:crypto";
import path from "node:path";
import { z } from "zod";
import { STAGE_ORDER } from "./constants.js";
import { canonicalLeanSubdir, isPaperLeanSubdir, statePath } from "./paths.js";
import type { StateJson } from "./types.js";
import type { VerifyState } from "./verify/types.js";

const stageSchema = z.enum(STAGE_ORDER);

/** One cited node's F2.5/F4 source-match verdict, persisted so the F5 delivery audit can enforce it. */
const citedCheckSchema = z.object({
  name: z.string(),
  check_status: z.string(),
  cite_id: z.string().optional(),
  locator: z.string().optional(),
  reviewer: z.enum(["codex", "claude"]).optional(),
});

const citedReviewReceiptSchema = z.object({
  node_id: z.string().min(1),
  reviewer: z.enum(["codex", "claude"]),
  check_status: z.string().min(1),
  cite_id: z.string().min(1),
  locator: z.string().min(1),
  evidence_hash: z.string().min(1),
});

const deliveryReviewReceiptSchema = z.object({
  node_id: z.string().min(1),
  reviewer: z.enum(["codex", "claude"]),
  verdict: z.enum(["matched", "drift"]),
  evidence_hash: z.string().min(1),
  note: z.string().optional(),
});

const addedAssumptionSchema = z.object({
  label: z.string(),
  statement: z.string(),
  source: z.string().optional(),
  anchor: z.string().optional(),
  classification: z
    .enum(["faithful-refinement", "regularity-bookkeeping", "substrate-gate"])
    .optional(),
}).passthrough();

const missingItemSchema = z.object({
  kind: z.string(),
  name_suggestion: z.string(),
  purpose: z.string(),
  why_substantial: z.string(),
  nl_artifact_reference: z.string().optional(),
  suggested_location: z.string().optional(),
}).passthrough();

export const stateSchema = z
  .object({
    stage_completed: stageSchema,
    lean_subdir: z.string(),
    // Self-identifying run coordinates, stamped on every save.
    qid: z.string().optional(),
    design_decisions: z.record(z.string()).default({}),
    added_assumptions: z.array(addedAssumptionSchema).default([]),
    /**
     * Durable record of the F4 reviewer's CITED source-match verdicts, one per cited node.
     *
     * The `cited-mismatch` / `cited-underspecified` verdicts HARD-BLOCK banking, but the verdict
     * used to live only in the reviewer's in-memory return value: the block was enforced solely
     * inside the proof–review loop, so a resume re-entering at F5 delivered a mismatched cited def
     * silently. What enforces the guarantee where the run completes is `cited_review_receipts`
     * (the F5 delivery audit reads those, with peer identity and locator); this list is the
     * per-node summary of them, written beside them and read by no stage.
     */
    cited_checks: z.array(citedCheckSchema).default([]),
    cited_review_receipts: z.array(citedReviewReceiptSchema).default([]),
    delivery_review_receipts: z.array(deliveryReviewReceiptSchema).default([]),
    // auto mode, the default: persisted autonomy flag (see SharedState.auto_mode).
    auto_mode: z.boolean().default(false),
    // `--debug`: auto mode off for this run (see SharedState.debug_mode).
    debug_mode: z.boolean().default(false),
    // `--full-auto`: the owner's decisions are delegated too (see SharedState.full_auto).
    full_auto: z.boolean().default(false),
    // The CLI that runs this run's claude roles, recorded at its first decision (`claude_roles.ts`).
    claude_roles: z.enum(["claude", "codex"]).optional(),
    flags: z.object({
      missing_architecture: z.boolean().default(false),
      missing_architecture_items: z.array(missingItemSchema).optional(),
      scaffold_redirect: z.string().nullable().optional(),
      plan_rewind_violations: z.string().nullable().optional(),
      f1_blocked: z.object({ message: z.string(), review: z.unknown().optional() }).nullable().optional(),
      // Proof-review loop iteration budgets — persisted so a `--resume` cannot silently
      // hand the loop a fresh budget (see types.ts).
      proof_loop_counters: z
        .object({
          iters: z.number().int().nonnegative().default(0),
          scaffold_rounds: z.number().int().nonnegative().default(0),
          stale: z.number().int().nonnegative().default(0),
          tag_reroutes: z.number().int().nonnegative().default(0),
          node_strikes: z.record(z.string(), z.number().int().nonnegative()).default({}),
          review_error_strikes: z.record(z.string(), z.number().int().nonnegative()).default({}),
          // Hash of the last red `lake build` diagnostic. Persisted so the identically-red
          // no-progress cap survives a `--resume` — an in-process comparand reset `stale` to 0
          // on every re-entry, refunding the circuit breaker a fresh budget each time.
          last_build_error_sig: z.string().default(""),
          // Filler anti-identical-prompt memory — persisted so a `--resume` does not
          // restart Phase B re-hitting the same dead ends with byte-identical prompts.
          filler_summaries: z.array(z.string()).default([]),
          // Best proof measure of the tree and the iteration that reached it (the no-progress cap).
          progress_best: z
            .object({
              open: z.number().int().nonnegative(),
              proved: z.number().int().nonnegative(),
              iter: z.number().int().nonnegative(),
            })
            .optional(),
        })
        .optional(),
      proof_loop_cap_hit: z.string().optional(),
      proof_review_escalation_pending: z
        .object({
          route: z.string(),
          reason: z.string(),
          kind: z.string().optional(),
          obj_id: z.string().optional(),
          phase: z.string().optional(),
          batch: z
            .array(z.object({ route: z.string(), reason: z.string(), kind: z.string().optional(), obj_id: z.string().optional() }))
            .optional(),
        })
        .nullable()
        .default(null),
      // Why a review boundary halted for the orchestrator (a cap gate).
      general_review_halt: z.string().nullable().optional(),
      // F3 phase-B proof-fill directive (build→resume): a load-bearing PROOF hint the
      // orchestrator injects for the filler (lemma names / tactic strategy / Mathlib API)
      // when the fill loop is stuck. Loop-wide + persistent — injected into every filler
      // call for the rest of phase B until the orchestrator clears it. Mirrors the
      // escalation-log directive channel; NOT a license to change statements/hypotheses
      // (the per-iteration anti-laundering + assumption/def gates still apply).
      f3_filler_directive: z.string().nullable().optional(),
      // Persistent orchestrator SCAFFOLD directive for F2 (analogue of `f3_filler_directive`):
      // read by `runStage2` on every scaffold/revise pass and injected verbatim as a
      // top-priority faithfulness constraint. Unlike `scaffold_redirect` (one-shot, capped,
      // self-clearing, review-loop-driven) this PERSISTS across resumes until the orchestrator
      // clears it in `state.json`. A faithfulness/statement-shape steer only — the
      // F2.5 review + anti-laundering gates still apply.
      f2_scaffold_directive: z.string().nullable().optional(),
    }).passthrough(),
  })
  .passthrough()
  .transform((raw) => raw as unknown as StateJson);

/**
 * Seed state of a run — the only initial state there is. The cursor starts at `"init"`; the
 * verify runner owns the run until `state.verify.phase` reaches `"formalization"`, and V1.5's
 * acceptance moves the cursor to `"V1.5"`, after which the F runner is entered at F1.
 * `papersLib` is the toolkit's per-paper library (`ToolkitConfig.papersLib`).
 */
export function createVerifyInitialState(
  qid: string,
  verify: VerifyState,
  papersLib?: string,
): StateJson {
  return {
    stage_completed: "init",
    lean_subdir: canonicalLeanSubdir(qid, papersLib),
    design_decisions: {},
    added_assumptions: [],
    cited_checks: [],
    delivery_review_receipts: [],
    flags: {
      missing_architecture: false,
      scaffold_redirect: null,
      f2_scaffold_directive: null,
      proof_review_escalation_pending: null,
    },
    verify,
  };
}

/** A fresh `state.verify` block (phase `init`, no source yet). */
export function emptyVerifyState(): VerifyState {
  return {
    phase: "init",
    source: { input: "", main_file: "", sha256: "" },
    targets: null,
    core_sha256: null,
    v1_rounds: 0,
    v1_5_rounds: 0,
    findings: [],
    report_path: null,
  };
}

/**
 * `createVerifyInitialState` with an empty verify block (no source yet). For test fixtures and
 * tools that need a well-formed state; runners always call `createVerifyInitialState` with the
 * prepared source.
 */
export function createInitialState(qid: string): StateJson {
  return createVerifyInitialState(qid, emptyVerifyState());
}

/** A run's Lean directory must be `<papers_lib>/<slugToPascal(qid)>` (see `isPaperLeanSubdir`). */
export function assertLeanSubdirInvariant(qid: string, state: StateJson): void {
  const normalized = state.lean_subdir.split(path.sep).join(path.posix.sep);
  if (!isPaperLeanSubdir(qid, normalized)) {
    throw new Error(
      `qid/lean_subdir invariant failed: expected ${canonicalLeanSubdir(qid)} (or another papers ` +
        `library followed by the same folder), found ${state.lean_subdir}`,
    );
  }
}

export async function loadState(repoRoot: string, qid: string): Promise<StateJson> {
  const file = statePath(repoRoot, qid);
  const parsed = stateSchema.parse(JSON.parse(await readFile(file, "utf8")));
  assertLeanSubdirInvariant(qid, parsed);
  return parsed;
}

export async function saveState(repoRoot: string, qid: string, state: StateJson): Promise<void> {
  assertLeanSubdirInvariant(qid, state);
  // Stamp the run id so the state file names its own run.
  state.qid = qid;
  const file = statePath(repoRoot, qid);
  await mkdir(path.dirname(file), { recursive: true });
  // Atomic write (temp + rename): state is saved many times mid-stage, and a crash during a
  // bare writeFile truncates the state file. Unique temp name (pid + uuid) so a pipeline save
  // racing a concurrent bin-tool save can never rename a half-written interleaving into place.
  const tmp = `${file}.${process.pid}.${randomUUID()}.tmp`;
  await writeFile(tmp, `${JSON.stringify(state, null, 2)}\n`, "utf8");
  await rename(tmp, file);
}
