// Condensed runtime echo of the orchestrator's playbook.
//
// WHY: over a long run the leansmith skill can drift out of the orchestrator's attention, so
// on resume it can forget what to do at the checkpoint it just hit. This module re-surfaces, on
// every F-stage halt, a SHORT operative reminder for the checkpoint just reached and the next
// phase — carried in the `next_step_guidance` field of the pipeline.jsonl checkpoint line and
// echoed to the console.
//
// SINGLE SOURCE OF TRUTH: `.claude/skills/leansmith/SKILL.md`. This file holds only the
// STABLE invariants + a pointer to the relevant skill section — keep the pointers matched to the
// current headings, and each entry to ~2 sentences. Point, don't paste.

import { CAP_GATES, GENERAL_REVIEW_HALT_EXITS, MISSING_ARCHITECTURE_EXIT } from "./cap_gates.js";
import type { Stage } from "./types.js";

/** The flags of the run's state a reminder reads: each names the halt it is set by. */
type HaltFlags = { general_review_halt?: string | null; f1_blocked?: unknown; missing_architecture?: boolean; proof_loop_cap_hit?: string | null };

/**
 * AUTO-MODE banner, prepended to the per-stage reminder when the run is autonomous
 * (`state.auto_mode`). The orchestrator tends to forget it is in auto mode after a long run and
 * revert to asking the user, so this re-asserts the rule on EVERY checkpoint line it reads.
 */
function autoBanner(stage: Stage): string {
  if (stage === "5") {
    return (
      "⚙ AUTO MODE — F5 refused to complete: fix what it names and `--resume` without asking; " +
      "a toolkit change or a commit always waits for the user.\n\n"
    );
  }
  return (
    "⚙ AUTO MODE — decide, act, and `--resume` without asking the user. Handle substrate and de-laundering autonomously; " +
    "report only a paper error, proven intractability, or a cap/budget block. Otherwise drive to the V6 report.\n\n"
  );
}

/**
 * Condensed orchestrator reminder for a halt at `stage` with `status`.
 * Returns `undefined` for stages that never need a human decision (so the
 * pipeline log stays quiet on ordinary `completed` transitions). When
 * `autoMode` is set, an AUTO-MODE banner is prepended so the orchestrator does
 * not forget the run is autonomous.
 */
export function checkpointGuidance(
  stage: Stage,
  status: string,
  flags: HaltFlags = {},
  autoMode = false,
  message = "",
): string | undefined {
  // Only checkpoints and blocks hand control back to the orchestrator.
  if (status !== "checkpoint" && status !== "blocked") return undefined;

  // The guard that refuses F5 while a proof-review escalation is unresolved is the loop's halt.
  const at: Stage = stage === "5" && /PROOF-REVIEW ESCALATION UNRESOLVED/.test(message) ? "2.5" : stage;
  const base = (at === "1" || at === "1.5") && flags.f1_blocked ? F1_BLOCKED_GUIDANCE : perStageGuidance(at, flags, message);
  if (base === undefined) return undefined;
  return autoMode ? autoBanner(at) + base : base;
}

/** F1 answered `blocked` (first plan, or a re-plan inside the F1.5 loop): no plan was written. */
const F1_BLOCKED_GUIDANCE =
  "F1 BLOCKED: the planner wrote no usable plan — the message says what is missing, contradictory or out of reach; a plan on disk is the earlier one, or the file that did not parse. " +
  "A defect of the paper's statement or of the core → record it (`discovery/patches.json`; a transcription defect in `discovery/core_refs.json`) and `--resume --from-stage V1.5` (`V1` for the transcription). " +
  "An obstacle you can settle for the planner → your directive in `flags.f1_revise_directive`, then `--resume`. A resume plans again before any review; never write the plan by hand. leansmith SKILL §'F stages'.";

function perStageGuidance(
  stage: Stage,
  flags: HaltFlags,
  message = "",
): string | undefined {
  switch (stage) {
    case "1.5":
      // The review bounced a plan F1 cannot (or could no longer) correct: not the audit checkpoint.
      if (flags.general_review_halt) {
        return `F1.5 REVIEW HALT (the gate \`general_review_halt\` is set): ${GENERAL_REVIEW_HALT_EXITS}. Never edit the plan by hand. leansmith SKILL §'F stages'.`;
      }
      return (
        "CONSOLIDATED CKPT 1: audit depth, reuse, fidelity, and contribution ownership. A genuinely published source-matched input may remain cited even when a headline invokes it; formalize every paper-owned/new step, including adaptations, embeddings, and splices. Never relabel difficult new work as cited or hand-patch the plan. " +
        "Then F2–F4 follows its route; reject laundering, and never edit the paper — a paper error is a V1.5 finding or a minimal patch. leansmith SKILL §'F stages'."
      );

    case "2":
      // The one F2 halt with a rule of its own; any other is the scaffolder not completing.
      return flags.missing_architecture
        ? `F2 MISSING ARCHITECTURE (every resume is refused while an item is unbuilt): ${MISSING_ARCHITECTURE_EXIT}. leansmith SKILL §'F stages'.`
        : "F2 DID NOT COMPLETE: the message is the scaffolder's reason; nothing advanced. `--resume` scaffolds again — put what it needs told in `flags.f2_scaffold_directive` first (it stays until you clear it); a defect of the plan is F1's (`--resume --from-stage F1`), one of the paper's statement a V1.5 finding. leansmith SKILL §'F stages'.";

    // (the proof-review loop runs in the F2.5 slot; its halt carries the phase that escalated)
    case "2.5":
    case "3":
    case "3.5":
    case "4":
      if (flags.proof_loop_cap_hit) {
        return `PROOF-LOOP CAP (the gate \`proof_loop_cap_hit\` is set: ${flags.proof_loop_cap_hit}): ${CAP_GATES.find((g) => g.flag === "proof_loop_cap_hit")!.guidance}. leansmith SKILL §'F stages'.`;
      }
      return (
        "F2–F4: follow the checkpoint route (hint / build-substrate / fix-source / unclear / bank-partial); keep running while revisions converge. A paper-statement finding comes back as a proposed rewind for you to approve or reject. " +
        "Use fix-source only when the paper is wrong (a report finding, never an edit to the source); unclear is undetermined, so investigate. After hand de-laundering, re-run the loop (`--from-stage F2.5`) through F5 and record added_assumptions. leansmith SKILL §'F stages'."
      );

    case "5":
      return f5RefusalGuidance(message);

    default:
      return undefined;
  }
}

/**
 * F5 halts only when one of its gates refuses to complete it (a completed F5 flows on to V6 with no
 * halt), so the reminder names the gate the message is from and its exit.
 */
function f5RefusalGuidance(message: string): string {
  const exit = " V6 writes the report only once F5 completes. leansmith SKILL §'F stages'.";
  if (/delivery audit REFUSED/.test(message)) {
    return (
      "F5 DELIVERY AUDIT REFUSED: the Lean is not the one the reviews cover — each finding names its node. A missing or stale convergence review, or a declaration changed since: run the loop again (`--from-stage F2.5`) so F4 reviews it. " +
      "A `cited-mismatch`: correct the Lean carrier to the cited source (or the plan's citation), then the loop again. Never edit a receipt." + exit
    );
  }
  if (/delivery audit could not validate/.test(message)) {
    return "F5 DELIVERY AUDIT could not read an artifact (graph, plan, core or a receipt): restore it by re-running the stage that writes it, then `--resume`." + exit;
  }
  // (every halt of the docstring gate: coverage short, the pass not validated, the pass breaking the build)
  if (/docstring (coverage|pass)/.test(message)) {
    return "F5 DOCSTRING GATE: the message lists the build error or the declarations still undocumented / crosslink-defective. Fix the build, or write those docstrings by hand to the contract (first paragraph the NL translation, a crosslink per hypothesis and the conclusion), then `--resume`; the gate cannot be skipped." + exit;
  }
  if (/bank-soundness/.test(message)) {
    return "F5 SOUNDNESS GATE: a `sorry` or a cheat token is left in the run's Lean. Prove it through the loop (`--from-stage F2.5`) — never delete a statement to pass — then `--resume`." + exit;
  }
  if (/crosswalk/.test(message)) {
    return "F5 CROSSWALK (paper ↔ Lean links): the message names the emit error or the rows that claim a Lean match with no anchor. Restore `graph.json` / wire the `-- @node:` anchor or correct the row's verdict, then `--resume`." + exit;
  }
  if (/formalization note/.test(message)) {
    return "F5 cannot read the formalization note the report consumes: restore it (F1 writes it with the plan), then `--resume`." + exit;
  }
  return "F5 did not complete: the message names the gate that refused; fix what it names, then `--resume`." + exit;
}

/**
 * The verify runner's halt on a PROPOSED F-stage rewind (`state.verify.cross_stage_rewind`,
 * `presented`). The orchestrator rules on it in every mode; in auto mode (the default) it rules without asking.
 */
export function rewindApprovalGuidance(autoMode: boolean): string {
  return (
    (autoMode ? "⚙ AUTO MODE — rule on it yourself, then resume; do not ask the user. " : "") +
    "PROPOSED REWIND: check the finding against the paper — the annotated paper named above marks it at its passage. It is right (a missing hypothesis, a wrong claim, a genuine second reading) → `--resume` (approve). " +
    "The paper already grants it (say where) or the reviewer misread the Lean → `--resume --reject-rewind \"<where the paper grants it>\"`. " +
    "The reviewer misread the PAPER → `--resume --reject-finding \"<the reading>\"` (yours; pinned into the core, binding for the formalization); when only the paper's author could say how it is meant, ask the user first (in the session and on the page: `orch.mjs ask`) and enter their answer. " +
    "A batch is ruled on as one; to approve only some findings, delete the others from `state.verify.cross_stage_rewind.targets` first. leansmith SKILL §'Rewinds are proposed'."
  );
}

/** The verify runner's halt at a patch-loop cap (`state.verify.cap_reached`). */
export function patchCapGuidance(autoMode: boolean): string {
  return (
    (autoMode ? "⚙ AUTO MODE — rule on it yourself, then resume; do not ask the user. " : "") +
    "PATCH CAP: judge the last round (the annotated paper named above marks each finding at its passage). Converging (fewer or narrower findings each round) → `--resume --clear-patch-cap`. " +
    "Oscillating, or the same weaker-condition dispute twice → `--resume --accept-cap`. leansmith SKILL §'Patch caps'."
  );
}

/**
 * The verify runner's halt on SUGGESTED repairs that weaken a MAIN THEOREM of the paper
 * (`state.verify.weakening_repair`). The user's decision, on the paper's page, in every mode: the
 * orchestrating agent recommends on each item and waits. Intermediate results (lemmas,
 * propositions, …) never reach it: their strongest true version is applied automatically and
 * reported "narrowed".
 */
export function weakeningRepairGuidance(autoMode: boolean, fullAuto = false): string {
  if (fullAuto) {
    return (
      "⚙ FULL AUTO — the owner delegated this decision: no one is asked. WEAKENED REPAIR: no repair keeps these main theorems at full strength. Read the annotated paper named above and re-derive each item against the paper's tex, then recommend on EVERY item: " +
      "`node tools/scripts/orch.mjs recommend <slug> --toolkit <toolkit> repair <node> <accept|decline|redo> \"<why>\" [--guidance \"<what to ask of the new repair>\"]` (a redo needs `--guidance`). " +
      "The last recommendation resumes the run with them (`verify --resume --accept-repair / --decline-repair / --redo-repair`, as recommended) and lists each for the owner's review on the page; keep your watcher armed. " +
      "Only a finding that misreads the paper is yours to withdraw instead: `--resume --reject-finding \"<node>: <the reading>\"`. leansmith SKILL §'Who decides'."
    );
  }
  return (
    (autoMode ? "⚙ AUTO MODE — this decision is still the user's: recommend, tell them it waits on the page, and wait; never rule on it yourself. " : "") +
    "WEAKENED REPAIR: no repair keeps these main theorems at full strength (intermediate results were already narrowed automatically — the log lists them; a theorem here may be one whose lemma was narrowed). Read the annotated paper named above — it marks each printed claim red with the proposed weaker claim in blue, the error, witness and what it gives up in the note. " +
    "The USER decides each item on the paper's page (accept / decline / redo with guidance). Re-derive each against the paper's tex and put your recommendation beside it: " +
    "`node tools/scripts/orch.mjs recommend <slug> --toolkit <toolkit> repair <node> <accept|decline|redo> \"<why>\" [--guidance \"<what to ask of the new repair>\"]` (a redo needs `--guidance`). " +
    "Then tell the user it is waiting and keep your watcher armed: their \"Send my decisions\" resumes the run. A ruling they give you in the session you enter for them (`--resume --accept-repair [<node>,…]` · `--decline-repair \"[<node>,…: ]<reason>\"` · `--redo-repair \"<node>: <guidance>\"`; items no answer names are presented again). " +
    "Only a finding that misreads the paper is yours to withdraw: `--resume --reject-finding \"<node>: <the reading>\"` (the printed statement stands under that reading, pinned into the core). leansmith SKILL §'Repairs never weaken the contribution'."
  );
}

/** The verify runner's halt on an annotated paper with blocks that could not be set as TeX
 * (`state.verify.render_checkpoint`; user decision 2026-09-25). A tool defect: checked before any
 * owner decision and F1, in every mode; never waived. */
export function renderCheckpointGuidance(autoMode: boolean): string {
  return (
    (autoMode ? "⚙ AUTO MODE — this is the tool's defect, not a paper judgement: never route it to the owner. " : "") +
    "RENDER CHECKPOINT: the listed blocks of the annotated paper print raw TeX (escaped text, a code point, an odd `$`, a pdflatex error). " +
    "A block that comes from a text in the run's record (transcription, reading, patch) is corrected there; a renderer defect is fixed with a test (`annotate_tex.ts` / `units.ts` / `annotated_paper.ts`) and recorded in `runs/<slug>/pipeline_issues.md`. " +
    "Check the tree with `leansmith lint-annotated <slug>` after `leansmith annotate <slug>`; `--resume` renders again and continues where the run stopped. There is no owner waiver. leansmith SKILL §'Render checkpoint'."
  );
}

/** The verify runner's halt on model-written fragments that still fail their compile check after
 * their producer's pass (`state.verify.render_checkpoint` of kind `contract`; user rule 2026-09-25:
 * a model's text is the model's to fix, never the renderer's). */
export function contractCheckpointGuidance(autoMode: boolean): string {
  return (
    (autoMode ? "⚙ AUTO MODE — this is a model-text defect, not a paper judgement and not the renderer's: never route it to the owner, never repair it in the renderer. " : "") +
    "CONTRACT CHECKPOINT: the listed model-written fragments still do not compile against the paper's preamble after their producer (named per group) wrote them again with the compiler's line. " +
    "Read the compiler lines: a prompt or contract gap is fixed in that producer's prompt / check; a text the run cannot re-ask (the owner's words, the transcription) is corrected in the run's record. " +
    "Then `--resume` routes them back again and continues where the run stopped. leansmith SKILL §'Render checkpoint'."
  );
}

