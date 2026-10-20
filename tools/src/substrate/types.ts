// Study-mode types: agent outputs, round reports, state, and the coordinator manifest.
import { z } from "zod";

export const codexPromptSchema = z.object({
  id: z.string(),
  // Models occasionally summarize a declaration set as one string even though
  // the structured-output schema requests an array.  The filler renders this
  // field as prose only, so preserving that string as a singleton is lossless
  // and avoids discarding an otherwise valid scaffold plan.
  target_decls: z.preprocess(
    (value) => typeof value === "string" ? [value] : value,
    z.array(z.string()).default([]),
  ),
  prompt: z.string(),
});
export type CodexPrompt = z.infer<typeof codexPromptSchema>;

export const scaffolderOutputSchema = z.object({
  decision: z.enum(["build", "review", "escalate"]),
  plan_markdown: z.string(),
  codex_prompts: z.array(codexPromptSchema).default([]),
  escalation: z.object({ reason: z.string() }).optional(),
});
export type ScaffolderOutput = z.infer<typeof scaffolderOutputSchema>;
export function parseScaffolderOutput(value: unknown): ScaffolderOutput {
  return scaffolderOutputSchema.parse(value);
}

export interface FillerReport { id: string; ok: boolean; summary: string }

export interface BuildDiagnostics {
  ok: boolean;
  errors: string[];
  sorryCount: number;
  perFile: Record<string, { sorries: number; errors: number }>;
}

export interface RoundReport {
  round: number;
  fillers: FillerReport[];
  build: BuildDiagnostics;
}

export const reviewVerdictSchema = z.object({
  pass: z.boolean(),
  // Tolerate the shapes the reviewer model actually emits: a single string, a
  // list of finding strings/objects (codex often returns `findings: []` on a
  // clean pass), or null. Normalize everything to one newline-joined string so
  // a benign shape difference never crashes the run.
  findings: z
    .union([z.string(), z.array(z.any()), z.null()])
    .transform((v) =>
      v == null
        ? ""
        : Array.isArray(v)
          ? v.map((x) => (typeof x === "string" ? x : JSON.stringify(x))).join("\n")
          : v,
    ),
  checks: z.object({
    generic: z.boolean(),
    reusable: z.boolean(),
    standard: z.boolean(),
    not_vacuous: z.boolean(),
    fulfills_goal: z.boolean(),
    sorry_free: z.boolean(),
    layered: z.boolean(),
    documented: z.boolean(),
  }),
}).transform((verdict) => {
  // A PASS needs every check; a FAIL may rest on a reason no check names (a library result
  // rebuilt instead of reused), said in `findings`. A reply that contradicts itself is a fail the
  // scaffolder is told about, never an abort of the study run.
  const failed = Object.entries(verdict.checks).filter(([, ok]) => !ok).map(([name]) => name);
  if (verdict.pass && failed.length > 0) {
    return { ...verdict, pass: false, findings: `The reviewer answered pass with failing check(s): ${failed.join(", ")}.${verdict.findings ? `\n${verdict.findings}` : ""}` };
  }
  if (!verdict.pass && failed.length === 0 && !verdict.findings.trim()) {
    return { ...verdict, findings: "The reviewer failed the module without naming a check or a reason: review it again." };
  }
  return verdict;
});
export type ReviewVerdict = z.infer<typeof reviewVerdictSchema>;
export function parseReviewVerdict(value: unknown): ReviewVerdict {
  return reviewVerdictSchema.parse(value);
}

const buildDiagnosticsSchema = z.object({
  ok: z.boolean(),
  errors: z.array(z.string()),
  sorryCount: z.number().int().nonnegative(),
  perFile: z.record(z.object({ sorries: z.number(), errors: z.number() })),
});
const roundReportSchema = z.object({
  round: z.number().int().nonnegative(),
  fillers: z.array(z.object({ id: z.string(), ok: z.boolean(), summary: z.string() })),
  build: buildDiagnosticsSchema,
});

export const substrateStateSchema = z.object({
  slug: z.string(),
  phase: z.enum(["build", "fill", "review", "coordinate", "done", "escalated", "halted"]),
  buildRounds: z.number().int().nonnegative().default(0),
  reviewRounds: z.number().int().nonnegative().default(0),
  // Bounded retry budget for the `coordinate` phase (mirrors reviewRounds): each
  // failed integration gate feeds its log back to the coordinator for another
  // attempt, up to COORD_CAP.
  coordinateRounds: z.number().int().nonnegative().default(0),
  lastCoordinateLog: z.union([z.string(), z.null()]).default(null),
  moduleFiles: z.array(z.string()).default([]),
  // The scaffolder's filler prompts for the current round, persisted at the
  // scaffold→fill checkpoint so a resume re-enters the (codex) proof-fill stage
  // WITHOUT re-running the expensive scaffolder. Cleared once consumed.
  pendingPrompts: z.array(codexPromptSchema).default([]),
  lastReport: z.union([roundReportSchema, z.null()]).default(null),
  lastReview: z.union([reviewVerdictSchema, z.null()]).default(null),
  terminalMessage: z.union([z.string(), z.null()]).default(null),
  /** Exact requirement bytes used by a terminal scaffolder escalation. A changed hash permits
   * one deterministic requirement-correction re-entry; unchanged input remains terminal. */
  terminalRequirementHash: z.union([z.string(), z.null()]).default(null),
  terminalEscalationKind: z.enum(["scaffolder", "coordinate-timeout", "coordinate-recovery"]).nullable().default(null),
  /** The coordinate attempt in flight (set before it starts, cleared when it returns). Still set
   *  on load = the process died mid-apply or mid-gate; the next attempt first restores the toolkit
   *  from the apply's write-ahead journal (`coordinate_journal.json`), so no op is applied twice. */
  pendingApply: z.object({ round: z.number().int().positive(), journal: z.string() }).nullable().default(null),
  requirementVersion: z.number().int().nonnegative().default(0),
});
export type SubstrateState = z.infer<typeof substrateStateSchema>;

// --- Coordinator manifest (the coordinator's structured output) ---------
//
// PARSE-SAFETY BY DESIGN: the manifest carries NO file contents. The coordinator WRITES each
// body / insert patch to a file under its staging dir and the manifest references it by
// `from` (a short relative path), so the JSON stays a few hundred bytes and parses reliably.
//
// Destinations (`target`) are relative to the toolkit root and must be Lean modules under
// `<lib>/<Division>/<Topic>/`; `from` is relative to the staging dir. Op kinds:
//
//   - create_file  a brand-new Lean module; `newModule` names it and the apply layer wires it
//                  into its division barrel.
//   - merge_lean   an INSERT-ONLY patch into an existing Lean file: the staged content goes in
//                  after the line containing `anchor` (empty = append at end of file). The
//                  apply layer asserts byte-preservation, so a merge can never alter a proven decl.
//   - write_file   retained for state compatibility; the toolkit apply layer rejects it (the
//                  toolkit has no hand-written record surfaces; the ledger is system-written).
export const coordOpSchema = z.discriminatedUnion("kind", [
  z.object({
    kind: z.literal("create_file"),
    target: z.string(),
    from: z.string(),
    newModule: z.string().optional(),
  }),
  z.object({
    kind: z.literal("merge_lean"),
    target: z.string(),
    anchor: z.string().default(""),
    from: z.string(),
  }),
  z.object({
    kind: z.literal("write_file"),
    target: z.string(),
    from: z.string(),
  }),
]);

export const coordinationManifestSchema = z.object({
  ops: z.array(coordOpSchema).min(1, "the coordinator's manifest has no op: it found nothing to integrate (its `notes` say what already provides the requirement) — nothing was promoted; settle the requirement and run the study again"),
  // Free-form rationale for the run log (placement decisions, dedup notes).
  notes: z.string().default(""),
});
export type CoordinationManifest = z.infer<typeof coordinationManifestSchema>;
export function parseCoordinationManifest(value: unknown): CoordinationManifest {
  return coordinationManifestSchema.parse(value);
}

/** Ledger provenance of a study that builds an owner-accepted proposal: the promoted
 *  declarations are recorded with this origin instead of `{kind: "study"}`, the proposal's main
 *  result as `tier: "main"` (with its title) and every other declaration the study adds as
 *  `tier: "aux"` owned by it. Persisted as `runs/study_<slug>/provenance.json`, so a resumed study
 *  keeps it. */
export const studyProvenanceSchema = z.object({
  origin: z.object({
    kind: z.literal("proposal"),
    slug: z.string().min(1),
    round: z.enum(["A", "B"]),
    proposal_id: z.string().min(1),
  }),
  decision: z.string().min(1),
  nearest_existing: z.array(z.string()).default([]),
  /** The main result's declaration name (its last component is matched). */
  main: z.string().min(1).optional(),
  /** The main result's title, as the owner read it on the checklist. */
  title: z.string().min(1).optional(),
});
export type StudyProvenance = z.infer<typeof studyProvenanceSchema>;
