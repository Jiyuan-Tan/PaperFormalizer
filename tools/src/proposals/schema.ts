// Toolkit promotion: the shared contracts of its two rounds.
//
// Round A (after F1): the results the paper cites without proving are proposed; an accepted one is
// BUILT in the toolkit by the study pipeline, and the paper then uses it instead of assuming it.
// Round B (after the V6 report of a full F run): the proved declarations of the paper's Lean are
// harvested and the reusable main results among them are proposed. Each proposal is ONE main
// result, written for a reader who does not read Lean (a title, a reference, the statement in
// words). A round-B entry takes one of two paths: `move` (the result moves as proved, its helper
// lemmas with it) or `generalize` (the general statement is built in the toolkit by the study
// pipeline and the paper's result is re-proved as its corollary) — a result stated over the
// paper's own types or readings never moves as is. Nothing enters the toolkit without an explicit
// owner decision, and every decision is recorded.
import path from "node:path";
import { z } from "zod";
import type { ToolkitConfig } from "../toolkit/config.js";
import { inNamespace, topicNamespaceOfPath } from "../toolkit/namespaces.js";

/** `A`: cited results, after F1. `B`: the paper's proved results, after the report. */
export const PROPOSAL_ROUNDS = ["A", "B"] as const;
export type ProposalRound = (typeof PROPOSAL_ROUNDS)[number];

/** A proposal id: `<round>-<slug of its source>` (`a-thm-delta-method`, `b-bar-le`). */
export const PROPOSAL_ID_RE = /^[ab]-[a-z0-9]+(?:-[a-z0-9]+)*$/;

/** The id slug of a source ref: lower-case, every non-alphanumeric run a single `-`. */
export function proposalRefSlug(ref: string): string {
  return ref.toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-+|-+$/g, "") || "item";
}

/** Stable ids `<round>-<slug of ref>` in order, so a re-curation keeps each item's id; colliding
 *  slugs get `-2`, `-3`, … in candidate order. */
export function assignProposalIds(refs: readonly string[], round: ProposalRound = "B"): string[] {
  const used = new Set<string>();
  return refs.map((ref) => {
    const base = `${round.toLowerCase()}-${proposalRefSlug(ref)}`;
    let id = base;
    for (let n = 2; used.has(id); n += 1) id = `${base}-${n}`;
    used.add(id);
    return id;
  });
}

export const nearestExistingSchema = z.object({
  name: z.string().min(1),
  library: z.string().min(1),
  why_not_same: z.string().min(1),
});
export type NearestExisting = z.infer<typeof nearestExistingSchema>;

export const proposalSourceSchema = z.object({
  /** `paper_decl`: a proved declaration of the paper's Lean (round B). `cited`: a result the paper
   *  cites without proving (round A). */
  kind: z.enum(["paper_decl", "cited"]),
  /** The declaration's fully-qualified name (round B), or the core statement id (round A). */
  ref: z.string().min(1),
  citation: z.string().optional(),
  /** One of the paper's own stated lemmas / propositions (moves verbatim). */
  is_paper_result: z.boolean().optional(),
  /** The paper statement's env id (`lem:twoforms`), for a paper result. */
  paper_env: z.string().optional(),
});
export type ProposalSource = z.infer<typeof proposalSourceSchema>;

/** The independent checker's judgment of one proposal. */
export const checkerNoteSchema = z.object({
  agrees: z.boolean(),
  note: z.string(),
  /** `move`: the title / content say exactly what the Lean statement proves (not weaker, not
   *  stronger). `generalize`: the content is a general statement the Lean statement is a direct
   *  special case of. Round A: the content says what the cited work states. */
  content_matches: z.boolean().optional(),
  /** An existing declaration that already states the item (up to notation or trivially weaker
   *  hypotheses), or null. A duplicate is declined automatically. */
  duplicate_of: z.string().nullable().optional(),
});

/** The same statement in another paper (`doc/statements.json`): `identical` = the normalized
 *  statement hashes alike; `pattern` = the same shape over each paper's own definitions
 *  (`statementPattern`); `similar` = a lexical match over statement text and docstring. A pattern or
 *  similar match counts as recurrence only when the curator `confirmed` it is the same result. */
export const recurrenceSchema = z.object({
  slug: z.string().min(1),
  name: z.string().min(1),
  kind: z.enum(["identical", "pattern", "similar"]),
  score: z.number().optional(),
  confirmed: z.boolean().optional(),
});

/** Whether a recurrence counts as evidence: identical, or confirmed by the curator. */
export function countsAsRecurrence(r: Recurrence): boolean {
  return r.kind === "identical" || r.confirmed === true;
}

/** Why an entry qualifies for its division: `standard` (a textbook result in base vocabulary —
 *  Foundations), `recurrence` (in ≥ 2 of the owner's papers), `existing_topic` (fits a Tricks topic
 *  other papers already use), `judgement` (the curator's written judgement of a reusable technique). */
export const QUALIFIES_BY = ["standard", "recurrence", "existing_topic", "judgement"] as const;

/** A topic the entry's `target_module` needs that the tree does not have yet; the owner decides it
 *  as its own checklist item before anything moves into it. */
export const newTopicSchema = z.object({ path: z.string().min(1), scope: z.string().min(1) });
export type NewTopic = z.infer<typeof newTopicSchema>;
export type Recurrence = z.infer<typeof recurrenceSchema>;

/** `generalize_first`: build the general form even for an entry proposed to move as is. */
export const DECISION_KINDS = ["accept", "accept_with_edits", "generalize_first", "decline", "defer"] as const;
export type DecisionKind = (typeof DECISION_KINDS)[number];

export const proposalSchema = z.object({
  /** `<round>-<slug of its source>`; unique within a batch. */
  id: z.string().regex(PROPOSAL_ID_RE),
  round: z.enum(PROPOSAL_ROUNDS),
  source: proposalSourceSchema,
  /** `propose`: a main result offered to the owner. `skip`: not offered (`reuse_evidence` says why;
   *  `duplicate_of` set = declined automatically as already available; `part_of` set = a helper
   *  that moves with that main result). */
  verdict: z.enum(["propose", "skip"]),
  /** The mathematical name of the result ("Number of assignments with fixed group counts"). */
  title: z.string().default(""),
  /** The standard source of a known result (book or paper, theorem number), else
   *  "new, from <paper> §…". */
  reference: z.string().default(""),
  /** The statement in plain mathematical English with Unicode mathematics (no TeX): hypotheses,
   *  then conclusion, as a textbook states it. */
  content: z.string().default(""),
  /** How the paper's own result relates to `content` (e.g. the special case it is), shown as its
   *  own line — never part of the statement. */
  relation_to_paper: z.string().optional(),
  division: z.string(),
  /** `<lib>/<Division>/<Topic>/<File>.lean`, relative to the toolkit root. */
  target_module: z.string(),
  /** One-line overview when `target_module` does not exist yet; null for an existing module. */
  new_module_overview: z.string().nullable().default(null),
  proposed_name: z.string(),
  nearest_existing: z.array(nearestExistingSchema).default([]),
  /** Why it is reusable (one line), or on a `skip` why it is not proposed. */
  reuse_evidence: z.string(),
  /** The independent checker's judgment (proposed items only). */
  checker: checkerNoteSchema.optional(),
  /** Set on a `skip` the checker found already available: the existing declaration. */
  duplicate_of: z.string().optional(),
  /** Set on a `skip` that is a helper of a proposed main result: that result's proposal id. */
  part_of: z.string().optional(),
  /** Paper declarations that move into the toolkit with this one (its closure), dependencies first. */
  moves_with: z.array(z.string()).optional(),
  /** The Lean statement as proved, for the "Lean details" block. */
  lean_type: z.string().optional(),
  /** Where it attaches in the toolkit graph (main view), in words. */
  graph_note: z.string().optional(),
  /** The same statement proved in other papers — the primary promotion evidence. */
  recurrence: z.array(recurrenceSchema).optional(),
  /** Round B: how an accepted entry enters the toolkit — `move` (as proved) or `generalize` (the
   *  general statement built by the study pipeline; the paper's result becomes its corollary).
   *  Round A entries are always built. */
  path: z.enum(["move", "generalize"]).optional(),
  /** Round B: what ties the Lean to the paper (its own types, readings, assumptions), in words —
   *  set, the entry cannot move as is and takes the `generalize` path. */
  paper_shaped: z.array(z.string()).optional(),
  /** Round A: the cited work's own text of the result, when it was fetched. */
  source_text: z.string().optional(),
  /** One line: why this division and topic (the bar it meets). */
  division_reason: z.string().optional(),
  /** The toolkit graph's mechanical signal: what the statement leans on (Mathlib alone → Foundations-
   *  shaped; domain-library or toolkit vocabulary → Tricks-shaped). */
  division_signal: z.enum(["Foundations", "Tricks"]).optional(),
  qualifies_by: z.enum(QUALIFIES_BY).optional(),
  /** A topic the target needs that the tree lacks (decided by the owner as its own item). */
  new_topic: newTopicSchema.nullable().optional(),
  /** Hypotheses of the paper's statement its proof never uses: the general form drops them. */
  dropped_hypotheses: z.array(z.string()).optional(),
  /** The same entry deferred before in another paper: it returns with the new evidence. */
  deferred_before: z.array(z.object({ slug: z.string(), proposal_id: z.string() })).optional(),
}).superRefine((p, ctx) => {
  if (p.verdict !== "propose") return;
  for (const key of ["title", "reference", "content", "division", "target_module", "proposed_name", "reuse_evidence"] as const) {
    if (p[key].trim() === "") ctx.addIssue({ code: z.ZodIssueCode.custom, path: [key], message: `a proposed item needs ${key}` });
  }
  if (p.nearest_existing.length === 0) {
    ctx.addIssue({ code: z.ZodIssueCode.custom, path: ["nearest_existing"], message: "a proposed item names its nearest existing declaration" });
  }
});
export type Proposal = z.infer<typeof proposalSchema>;

export const proposalBatchSchema = z.object({
  slug: z.string().min(1),
  round: z.enum(PROPOSAL_ROUNDS),
  created: z.string().min(1),
  proposals: z.array(proposalSchema),
}).superRefine((b, ctx) => {
  const seen = new Set<string>();
  b.proposals.forEach((p, i) => {
    if (seen.has(p.id)) ctx.addIssue({ code: z.ZodIssueCode.custom, path: ["proposals", i, "id"], message: `duplicate proposal id ${p.id}` });
    seen.add(p.id);
  });
});
export type ProposalBatch = z.infer<typeof proposalBatchSchema>;

/** The toolkit docstring of a moved main result: what the owner read on the checklist. */
export function proposalDocstring(p: Pick<Proposal, "title" | "reference" | "content">): string {
  return [`${p.title}.`, p.content.trim(), `Reference: ${p.reference.trim()}.`].join("\n\n");
}

/** Fields the owner may change with `accept_with_edits` (none changes what the Lean proves). */
export const EDITABLE_FIELDS = ["division", "target_module", "proposed_name", "title", "reference", "content"] as const;
export type EditableField = (typeof EDITABLE_FIELDS)[number];

export const proposalEditsSchema = z.object({
  division: z.string().min(1).optional(),
  target_module: z.string().min(1).optional(),
  proposed_name: z.string().min(1).optional(),
  title: z.string().min(1).optional(),
  reference: z.string().min(1).optional(),
  content: z.string().min(1).optional(),
}).strict().refine((e) => Object.keys(e).length > 0, { message: "accept_with_edits needs at least one edit" });

const note = z.string().min(1).optional();

export const decisionSchema = z.discriminatedUnion("kind", [
  z.object({ kind: z.literal("accept"), note }).strict(),
  z.object({ kind: z.literal("accept_with_edits"), edits: proposalEditsSchema, note }).strict(),
  z.object({ kind: z.literal("generalize_first"), note }).strict(),
  z.object({ kind: z.literal("decline"), note }).strict(),
  z.object({ kind: z.literal("defer"), note }).strict(),
]);
export type Decision = z.infer<typeof decisionSchema>;

/** Decisions that bring the item into the toolkit (moved or built). */
export function isMoveDecision(d: Decision): boolean {
  return d.kind === "accept" || d.kind === "accept_with_edits" || d.kind === "generalize_first";
}

/** How an accepted round-B entry enters the toolkit: built in general form when the entry says so,
 *  when it is paper-shaped, or when the owner chose `generalize_first`; else moved as proved. */
export function entersBy(p: Proposal, d: Decision): "move" | "generalize" {
  return d.kind === "generalize_first" || p.path === "generalize" || (p.paper_shaped?.length ?? 0) > 0 ? "generalize" : "move";
}

/** The study run that builds an accepted proposal: `<paper slug>__<proposal id>`. */
export function proposalStudySlug(slug: string, proposalId: string): string {
  return `${slug}__${proposalId}`;
}

export const decisionsFileSchema = z.object({
  slug: z.string().min(1),
  round: z.enum(PROPOSAL_ROUNDS),
  decisions: z.record(z.string(), decisionSchema),
  decided_at: z.string().min(1),
});
export type DecisionsFile = z.infer<typeof decisionsFileSchema>;

/** One decision as the ledger keeps it (`doc/ledger.json` `decisions[]`). Declined, deferred and
 *  automatically declined items are recorded too: a later paper proposing the same item sees that
 *  history as evidence. */
export const proposalDecisionRecordSchema = z.object({
  kind: z.literal("proposal_decision"),
  slug: z.string().min(1),
  round: z.enum(PROPOSAL_ROUNDS),
  proposal_id: z.string().min(1),
  decision: z.object({ kind: z.string(), note: z.string().optional() }).passthrough(),
  proposal: z.object({ proposed_name: z.string().default(""), division: z.string().default(""), target_module: z.string().default("") }).passthrough(),
  decided_at: z.string().min(1),
  /** Fully-qualified toolkit declarations the move produced. */
  promoted: z.array(z.string()).default([]),
  /** `created` of the batch the decision answered (a re-proposed round is a new batch). */
  batch_created: z.string().optional(),
  /** Written by a `--dry-run` apply, which writes only the dry run's own ledger. */
  dry_run: z.boolean().optional(),
}).passthrough();
export type ProposalDecisionRecord = z.infer<typeof proposalDecisionRecordSchema>;

/** Idempotency key of a decision record: one record per item per batch. */
export function proposalDecisionKey(r: unknown): string | null {
  const x = r as Partial<ProposalDecisionRecord>;
  if (x?.kind !== "proposal_decision" || !x.slug || !x.round || !x.proposal_id) return null;
  return `${x.slug}/${x.round}/${x.proposal_id}${x.batch_created ? `@${x.batch_created}` : ""}`;
}

/** A pending batch set aside because the report it was proposed from is re-run. */
export const proposalRoundVoidedRecordSchema = z.object({
  kind: z.literal("proposal_round_voided"),
  slug: z.string().min(1),
  round: z.enum(PROPOSAL_ROUNDS),
  reason: z.string().min(1),
  previous_status: z.enum(["pending_user", "applied", "empty", "deferred"]),
  previous_batch_path: z.string().nullable(),
  promoted: z.array(z.string()).default([]),
  voided_at: z.string().min(1),
  dry_run: z.boolean().optional(),
}).passthrough();
export type ProposalRoundVoidedRecord = z.infer<typeof proposalRoundVoidedRecordSchema>;

/** `state.verify.promotion` (round B) / `state.verify.promotion_a` (round A). `deferred`: the round
 *  was not held (`--defer-proposals`, or a run that was past F1 when round A was introduced). */
export interface ProposalRoundState {
  status: "pending_user" | "applied" | "empty" | "deferred";
  /** `runs/<slug>/proposals/<round>.json`. */
  batch_path: string | null;
  /** `<toolkit>/doc/proposals/<slug>.<round>.md`, null when nothing was proposed. */
  checklist_path: string | null;
  /** Why a `deferred` round was not held. */
  reason?: string;
  created_at?: string;
  applied_at?: string;
  /** Toolkit declarations the apply moved in. */
  promoted: string[];
  /** What the apply moved out of the paper (the report's toolkit section). */
  moves?: RoundBMove[];
}

/** One applied item: the paper declarations it moved and where to. */
export interface RoundBMove {
  proposal_id: string;
  decision: DecisionKind;
  /** Toolkit module the declarations now live in. */
  module: string;
  /** Old paper name → new toolkit name, dependencies first. */
  decls: Array<{ from: string; to: string }>;
}

/** The owner's edits applied to a proposal (the effective proposal the move uses). */
export function applyEdits(p: Proposal, d: Decision): Proposal {
  const eff = d.kind === "accept_with_edits" ? { ...p, ...d.edits } : p;
  // A toolkit declaration lives in its module's topic namespace (`toolkit/namespaces.ts`).
  return { ...eff, proposed_name: inNamespace(eff.proposed_name, topicNamespaceOfPath(eff.target_module)) };
}

// ─── paths ─────────────────────────────────────────────────────────────────

export function proposalsRunDir(cfg: ToolkitConfig, slug: string): string {
  return path.join(cfg.runsDir, slug, "proposals");
}
export function batchPath(cfg: ToolkitConfig, slug: string, round: ProposalRound = "B"): string {
  return path.join(proposalsRunDir(cfg, slug), `${round}.json`);
}
export function decisionsPath(cfg: ToolkitConfig, slug: string, round: ProposalRound = "B"): string {
  return path.join(proposalsRunDir(cfg, slug), `${round}.decisions.json`);
}
/** Where a dry run keeps what the owner-facing side would write into the toolkit. */
export function proposalsDryRunDir(cfg: ToolkitConfig, slug: string): string {
  return path.join(proposalsRunDir(cfg, slug), "dry_run");
}
/** The owner's checklist: `<toolkit>/doc/proposals/<slug>.<round>.md` (a dry run's under its run record). */
export function checklistPath(cfg: ToolkitConfig, slug: string, dryRun = false, round: ProposalRound = "B"): string {
  return dryRun
    ? path.join(proposalsDryRunDir(cfg, slug), `${slug}.${round}.md`)
    : path.join(cfg.toolkitRoot, "doc", "proposals", `${slug}.${round}.md`);
}
/** The ledger decision records go to: the toolkit's, or a dry run's private one. */
export function proposalLedgerPath(cfg: ToolkitConfig, slug: string, dryRun: boolean): string {
  return dryRun ? path.join(proposalsDryRunDir(cfg, slug), "ledger.json") : cfg.ledgerPath;
}
