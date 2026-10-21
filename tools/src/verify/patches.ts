/**
 * Minimal patches — `discovery/patches.json`.
 *
 * When the V1.5 referee finds an error on a faithful core, V1 runs in PATCH mode: a fixer
 * writes the smallest repair that keeps the paper's key contribution — REPLACEMENTS of the paper's units
 * (`ops.ts`: the statement's and the proof's sentences, items and displays; a hypothesis is added by
 * restating the statement with it) — and a fresh V1.5 pass confirms it before any Lean work. The
 * corrected statement and the amended proof are DERIVED from the ops when the reply is read
 * (`materializeReply`) and stored beside them, so every reader of the file reads text.
 *
 * The patch file is an OVERLAY. `core.transcribed.json` holds the core exactly as V1 copied it
 * from the paper (the user's version); `core.json` = that + the patches (the corrected
 * version), rebuilt whenever either changes. The F stages formalize `core.json` like any core;
 * the report diffs the two to say what was changed. A transcription round never loses a patch.
 * The file may be edited by hand, but its derived texts are re-derived from the ops on every read
 * (`readPatchFile`) and never written back: an edit to a derived field does not stick — edit the ops.
 *
 * This module owns the FILE: its schema, the fixer's reply schema, the mechanical checks on it
 * (coverage, ids, key results), and the on-disk rebuild of `core.json`. How the file changes the
 * core — the edits, the closure, the derived wiring, the invariant — is `core_graph.ts`'s.
 */
import { existsSync } from "node:fs";
import { copyFile, readFile } from "node:fs/promises";
import path from "node:path";
import { z } from "zod";
import { OWNER_EXPLANATION_JSON, OwnerExplanationFieldSchema, TEX_STRING, TEX_STRING_NONEMPTY, TEX_STRING_OR_NULL } from "./owner_text.js";
import { OPS_JSON, PROOF_UNCHANGED, PatchOpSchema, hasDetail, isStatementOp, materializeRepair, nodePassage, resolveOps, revisesProof, supersededNodes, type PassageSources, type PatchOp, type RepairScope } from "./ops.js";
import { RefCoreSchema, type RefCore } from "./ref_core.js";
import { loadUnits } from "./units.js";
import { parseTypedCore } from "../core/core_io.js";
import type { Core } from "../core/schema.js";
import { CoreGraphInputError, buildCore, REVIEW_ADDED_BY, UMBRELLA_PROOF, UMBRELLA_STATEMENT, citedLabels, isUmbrellaPatch, splitCorollaryId, statementBody, statementClosure, type SplitCorollary } from "./core_graph.js";
import { VERIFY_FILES, type EnvsJson, type FindingPatch, type V15SymbolVerdict } from "./types.js";
import { coreEditedSinceWrite, recordCoreWrite, sha256File, writeCoreJson } from "./core_hash.js";

export {
  CoreGraphInputError,
  PROOF_CHANGE_MARKER,
  descopedStatements,
  statementClosure,
} from "./core_graph.js";

/** An optional one-line text field of the fixer's reply: its strict JSON schema makes it required
 * and nullable, so null or blank reads as absent. */
function optionalText() {
  return z.preprocess((v) => (typeof v === "string" && v.trim() ? v.trim() : undefined), z.string().optional());
}

/** An optional id list of the fixer's reply (required and nullable in its strict schema): null or
 * empty reads as absent. */
function optionalIds() {
  return z.preprocess((v) => (Array.isArray(v) && v.length > 0 ? v : undefined), z.array(z.string().min(1)).optional());
}

/** An optional list of texts of the fixer's reply (required and nullable in its strict schema): null,
 * blanks and an empty list read as absent. */
function optionalTexts() {
  return z.preprocess((v) => {
    const xs = Array.isArray(v) ? v.filter((x) => typeof x === "string" && x.trim()).map((x) => (x as string).trim()) : [];
    return xs.length > 0 ? xs : undefined;
  }, z.array(z.string().min(1)).optional());
}

/** One corollary a repair splits off its result (`core_graph.ts` `SplitCorollary`). */
const CorollarySchema = z.object({
  title: optionalText(),
  statement: z.string().trim().min(1),
  follows: z.string().trim().min(1),
  adds: optionalIds(),
});

/** An optional list of corollaries of the fixer's reply (required and nullable in its strict schema):
 * null or empty reads as absent. */
function optionalCorollaries() {
  return z.preprocess((v) => (Array.isArray(v) && v.length > 0 ? v : undefined), z.array(CorollarySchema).optional());
}

/** An optional flag of the fixer's reply (required and nullable in its strict schema): only `true` is kept. */
function optionalFlag() {
  return z.preprocess((v) => (v === true ? true : undefined), z.boolean().optional());
}

const PatchSchema = z.object({
  node: z.string().min(1),
  /** DERIVED from the ops: the node's corrected printed text (a statement's, an assumption's or a
   * definition's); null when no op changes it. */
  corrected_statement: z.string().min(1).nullable(),
  /** The repair as replacements of the paper's units (`ops.ts`), the source of truth for the corrected
   * text and the amended proof. */
  ops: z.array(PatchOpSchema).optional(),
  /** DERIVED (`ops.ts` `supersededNodes`): the node's hypotheses (assumptions) whose printed text the
   * replacement rewrites; the build unwires them from the node. */
  supersedes: z.array(z.string()).optional(),
  /** The fixer's: the nodes the result depends on that the corrected result no longer uses — a
   * hypothesis (assumption, definition) whose condition it states itself, or a result it no longer
   * relies on. Only on a result; the build unwires them from it. Null / empty in a reply = absent. */
  drops: optionalIds(),
  /** The fixer's: the hypotheses (assumptions, definitions) the corrected result uses that it does not
   * depend on yet — a condition its corrected text imposes by citing another result's conditions. Only on
   * a result; the build wires them into it. Null / empty in a reply = absent. */
  adds: optionalIds(),
  /** The fixer's: how a phrase of the node is to be read, each ONE condition in the paper's notation
   * — the specification an ambiguity needed, stated beside the statement instead of written into it.
   * The build pins each (`ass:pin-fix-<hash>`, `core_graph.ts`); the referee grades it with the patch. */
  readings: optionalTexts(),
  /** The fixer's: results the repair SPLITS OFF the node — when the true content of a printed result
   * divides into a general statement and special cases holding under their own conditions, the node
   * keeps the general statement and each case is a corollary, a result of its own. Only on a result.
   * The build adds each as a statement node (`splitCorollaryId`); the referee grades each, and what
   * the repair gives up is judged on the node TOGETHER with them. */
  corollaries: optionalCorollaries(),
  /** The fixer's (or the orchestrator's, `--umbrella`): the result is an UMBRELLA — it mixes several
   * conclusions, each under its own conditions, none its own main claim, so EVERY conclusion is a
   * block of `corollaries` (at least two, all propositions) and the node only says that they hold.
   * It takes no ops: `corrected_statement` and `proof_note` are the pipeline's fixed texts
   * (`UMBRELLA_STATEMENT`, `UMBRELLA_PROOF`; `canonicalUmbrellas`), and the core node depends on its
   * blocks and is established exactly when all of them are. */
  umbrella: optionalFlag(),
  /** DERIVED when an op changes the proof: the printed proof with the ops applied (the runner writes
   * it); the full proof only when the paper prints none. */
  proof_note: z.string().min(1),
  /** The error and what this repair changes, for the paper's author: the note's fields, no node
   * ids, no pipeline vocabulary (`owner_text.ts`). Required in the fixer's reply on a node with a
   * finding; null (absent) on a consequential patch (`consequence_of`); absent on files written before
   * the field. */
  owner_explanation: z.preprocess((v) => (v === null ? undefined : v), OwnerExplanationFieldSchema.optional()),
  /** A CONSEQUENTIAL patch (`consequential.ts`): on a node no finding names, restated or its proof
   * revised only so that it follows the repairs of these nodes (a hypothesis they add). Required then,
   * forbidden on a node with a finding; null / empty in a reply = absent. */
  consequence_of: optionalIds(),
  /** With `consequence_of`: one sentence for the author, in the paper's terms, on what the corrected
   * result now uses (rendered "Changed to follow the repair of …: <reason>"). */
  reason: optionalText(),
  /** Runner-owned (or written by hand): the repair WEAKENS the paper's claim and the owner accepted
   * it (`--accept-repair`, or a hand-written patch followed by `--from-stage V1.5`). The referee then
   * judges only whether it holds, not whether it weakens. */
  accepted_weakening: z.boolean().optional(),
  /** Runner-owned, with `accepted_weakening`: what the weakened version gives up (one line). */
  given_up: z.string().optional(),
  /** Runner-owned, with `given_up`: `referee` when the text is the referee's (a repair it graded
   * weakening whose note gives nothing up); absent: the fixer's note. */
  given_up_by: z.enum(["referee"]).optional(),
  /** Runner-owned, with `accepted_weakening`: who accepted the weakening — `runner` for an
   * intermediate result (not a main theorem) narrowed automatically, `owner` (or absent) for a main
   * theorem the owner ruled on (`weakening.ts`). */
  narrowed_by: z.enum(["owner", "runner"]).optional(),
});

/** The reason prefix of an `unfixable` entry whose only repairs weaken the contribution. */
export const WEAKENS_REASON_PREFIX = "any repair weakens the contribution:";

/** The REPAIR itself — the fields of a patch that travel between a patch and a suggested repair: the
 * node, the author's note and the runner's marks apart. Derived from `PatchSchema`, so a field added
 * there moves with the repair everywhere (`repairBody`). */
const RepairBodySchema = PatchSchema.omit({ node: true, owner_explanation: true, consequence_of: true, reason: true, accepted_weakening: true, given_up: true, given_up_by: true, narrowed_by: true });
export type RepairBody = z.infer<typeof RepairBodySchema>;
const REPAIR_BODY_KEYS = Object.keys(RepairBodySchema.shape) as Array<keyof RepairBody>;

/** The repair of a patch (or of a suggested repair), as a body: every repair field it sets (an unset
 * flag reads as absent). Pure. */
export function repairBody(p: Partial<RepairBody> & { corrected_statement: string | null; proof_note: string }): RepairBody {
  const out: Record<string, unknown> = {};
  for (const k of REPAIR_BODY_KEYS) {
    const v = p[k];
    if (v === undefined || v === false) continue;
    out[k] = v;
  }
  return out as RepairBody;
}

/** The STRONGEST version of a result still available when every repair weakens it: a patch body,
 * plus what it gives up. Recorded and presented to the owner; applied only on `--accept-repair`. */
const SuggestedRepairSchema = RepairBodySchema.extend({
  /** DERIVED from the note's `gives_up`: what the weaker version gives up (absent: nothing). */
  given_up: z.string().min(1).optional(),
  /** `referee` when `given_up` is the referee's text (`convertWeakeningPatches`); absent: the fixer's. */
  given_up_by: z.enum(["referee"]).optional(),
});

const UnfixableSchema = z.object({
  node: z.string().min(1),
  reason: z.string().min(1),
  /** When no repair keeps the claim but a weaker true version exists: that version. Null when nothing
   * of the result survives. */
  suggested_repair: SuggestedRepairSchema.nullable().optional(),
  /** The error and the suggestion for the paper's author (as on a patch). */
  owner_explanation: OwnerExplanationFieldSchema.optional(),
  /** Runner-owned: who suggested it — the fixer, or the referee grading a repair that weakens. */
  suggested_by: z.enum(["fixer", "referee"]).optional(),
  /** Runner-owned: the `consequence_of` and `reason` of the CONSEQUENTIAL patch the suggestion was
   * (`convertWeakeningPatches`) — why the printed statement no longer stands, for the owner's receipt. */
  consequence_of: optionalIds(),
  consequence_reason: optionalText(),
  /** Runner-owned: the owner declined the suggested repair (`--decline-repair`), with this reason. */
  declined: z.string().optional(),
});

/** An owner reading's id: `ass:pin-owner-<n>` (a reading, rendered in the annotated paper) or
 * `ass:bk-owner-<n>` (a side condition every reader takes for granted — rendered as a condition added). */
const OWNER_PIN_ID = /^ass:(pin|bk)-owner-[0-9]+$/;
const OwnerReadingSchema = z.object({
  id: z.string().regex(OWNER_PIN_ID),
  node: z.string().min(1),
  reading: z.string().min(1),
  kind: z.enum(["reading", "bookkeeping"]).optional(),
  withdraws: z
    .array(
      z.object({
        axis: z.enum(["correctness", "clarify", "ambiguity"]),
        stage: z.string(),
        route: z.string(),
        detail: z.string(),
        witness: z.string().nullable().optional(),
        at: z.string(),
      }),
    )
    .optional(),
});

/** What the printed paper gets wrong (`state.verify.paper_errors`). */
export type PaperErrors = NonNullable<import("./types.js").VerifyState["paper_errors"]>;

/** The ledger entries that are errors (or clarifications) of the paper still to be addressed: every
 * entry except those the owner withdrew (`owner_decision: "finding rejected"`). A patch file must
 * address each of these; a withdrawn one is no error of the paper and needs no patch. */
export function openErrorIds(ledger: PaperErrors | undefined): string[] {
  return Object.entries(ledger ?? {}).filter(([, e]) => e.owner_decision !== "finding rejected").map(([id]) => id);
}

/** A ledger entry the owner withdrew (`--reject-finding`). */
export function isWithdrawn(e: { owner_decision?: string } | undefined): boolean {
  return e?.owner_decision === "finding rejected";
}

function FixerRejectionReplySchema() {
  return z.object({ node: z.string().min(1), reason: z.string().min(1), where_the_paper_grants_it: z.string().min(1) });
}

const PatchFileObjectSchema = z.object({
  key_results: z.array(z.string()).default([]),
  key_contribution: z.string().default(""),
  patches: z.array(PatchSchema).default([]),
  unfixable: z.array(UnfixableSchema).default([]),
  /** The fixer's REPLY only (never persisted): F-stage findings it rejects — the paper does grant
   * what the finding says it lacks. Allowed only for F-originated findings; the next V1.5 pass
   * rules on each (`state.verify.fixer_rejections`). */
  rejected: z.array(FixerRejectionReplySchema()).optional(),
  /** Runner-owned (never in the fixer's reply): readings the paper's owner adopted when withdrawing
   * a finding (`--reject-finding`, `owner_rulings.ts`). Each is compiled into an `ass:pin-owner-<n>`
   * wired into its node; a fixer reply cannot drop one (`pinOwnerEntries`). */
  owner_readings: z.array(OwnerReadingSchema).optional(),
  /** Runner-owned (never in the fixer's reply): consequential patches the fixer wrote that follow
   * only a SUGGESTED repair of a main theorem, held until the owner rules on it
   * (`consequential.ts` `setAsideSuggestionConsequences`): applied with the suggestion the owner
   * accepts (`ruleOnReceipt`), dropped with one declined or redone. */
  set_aside: z.array(PatchSchema).optional(),
});
export const PatchFileSchema = PatchFileObjectSchema;
export type PatchFile = z.infer<typeof PatchFileObjectSchema>;
export type Patch = z.infer<typeof PatchSchema>;
export type Unfixable = z.infer<typeof UnfixableSchema>;
export type SuggestedRepair = z.infer<typeof SuggestedRepairSchema>;

/** A repair's corollaries with the id each takes in the core (`splitCorollaryId`), in order. Pure. */
export function corollaryNodes(node: string, body: { corollaries?: readonly SplitCorollary[] | null } | null | undefined): Array<SplitCorollary & { id: string }> {
  return (body?.corollaries ?? []).map((c) => ({ ...c, id: splitCorollaryId(node, c.statement) }));
}

/** The corollaries the repairs of a patch file split off (its patches, and its suggested repairs not
 * declined), by node id: the parent each belongs to and its entry. Pure. */
export function splitCorollaries(file: { patches?: PatchFile["patches"]; unfixable?: PatchFile["unfixable"] } | null | undefined): Map<string, { parent: string; corollary: SplitCorollary }> {
  const bodies = [...(file?.patches ?? []).map((p) => ({ node: p.node, body: p as { corollaries?: SplitCorollary[] } })), ...(file?.unfixable ?? []).flatMap((u) => (u.suggested_repair && u.declined === undefined ? [{ node: u.node, body: u.suggested_repair as { corollaries?: SplitCorollary[] } }] : []))];
  return new Map(bodies.flatMap((b) => corollaryNodes(b.node, b.body).map(({ id, ...corollary }) => [id, { parent: b.node, corollary }] as const)));
}

/**
 * A finding on a corollary a repair split off is a finding on that REPAIR: the corollary is no node
 * the fixer can answer (the paper does not print it), so the finding is put on its parent — whose
 * entry the fixer returns whole, corollaries included — its detail saying which corollary it is
 * about. Every other finding is returned as it is. Pure.
 */
export function onSplitParent<T extends { id: string; detail: string }>(findings: readonly T[], file: Parameters<typeof splitCorollaries>[0]): T[] {
  const split = splitCorollaries(file);
  return findings.map((f) => {
    const s = split.get(f.id);
    if (!s) return f;
    const text = s.corollary.statement.replace(/\s+/gu, " ").trim();
    return { ...f, id: s.parent, detail: `on the corollary${s.corollary.title ? ` "${s.corollary.title}"` : ""} this repair splits off ("${text.length > 200 ? `${text.slice(0, 199)}…` : text}"): ${f.detail}` };
  });
}

/** An unfixable entry that suggests a weakened repair the owner has not ruled on: the run halts. */
export function isPendingSuggestion(u: Unfixable): boolean {
  return !!u.suggested_repair && u.declined === undefined;
}

/** The suggested repair as one line of text (ledger, report). */
export function suggestionText(s: SuggestedRepair): string {
  return [
    s.corrected_statement ? `corrected statement: ${s.corrected_statement}` : "",
    ...(s.corollaries ?? []).map((c, i) => `corollary ${i + 1}${c.title ? ` (${c.title})` : ""}: ${c.statement}`),
    s.umbrella ? "the statement becomes an umbrella over these blocks" : "",
    s.given_up ? `gives up: ${s.given_up}` : "",
  ]
    .filter(Boolean)
    .join(" · ");
}

/** The file with the suggested repairs of `nodes` applied: each unfixable entry becomes the patch it
 * suggests, marked as a weakening the owner accepted. */
export function applySuggestions(file: PatchFile, nodes: ReadonlySet<string>): PatchFile {
  const moved = file.unfixable.filter((u) => nodes.has(u.node) && u.suggested_repair);
  return {
    ...file,
    patches: [
      ...file.patches.filter((p) => !moved.some((u) => u.node === p.node)),
      ...moved.map((u) => {
        const { given_up, given_up_by, ...body } = u.suggested_repair!;
        return { node: u.node, ...body, ...(u.owner_explanation ? { owner_explanation: u.owner_explanation } : {}), accepted_weakening: true, given_up, ...(given_up_by ? { given_up_by } : {}) };
      }),
    ],
    unfixable: file.unfixable.filter((u) => !moved.includes(u)),
  };
}

/** A repair's `drops` / `adds` in the fixer's reply: node ids, or null. */
const HYPOTHESES_JSON: Record<string, unknown> = { anyOf: [{ type: "array", items: { type: "string" } }, { type: "null" }] };
/** A repair's `readings` in the fixer's reply: TeX texts, not ids. */
const READINGS_JSON: Record<string, unknown> = { anyOf: [{ type: "array", items: TEX_STRING }, { type: "null" }] };

/** A repair's `corollaries` in the fixer's reply: `{title, statement, follows, adds}` entries, or null. */
const COROLLARIES_JSON: Record<string, unknown> = {
  anyOf: [
    {
      type: "array",
      items: {
        type: "object",
        additionalProperties: false,
        required: ["title", "statement", "follows", "adds"],
        properties: { title: TEX_STRING_OR_NULL, statement: TEX_STRING_NONEMPTY, follows: TEX_STRING_NONEMPTY, adds: HYPOTHESES_JSON },
      },
    },
    { type: "null" },
  ],
};

/** A repair's `umbrella` in the fixer's reply: true, or null. */
const UMBRELLA_JSON: Record<string, unknown> = { anyOf: [{ type: "boolean" }, { type: "null" }] };

/** `codex exec --output-schema` for the fixer's reply: the whole patch file. */
export const PATCH_REPLY_JSON_SCHEMA: Record<string, unknown> = {
  type: "object",
  additionalProperties: false,
  required: ["key_results", "key_contribution", "patches", "unfixable", "rejected"],
  properties: {
    key_results: { type: "array", items: { type: "string" } },
    key_contribution: { type: "string" },
    patches: {
      type: "array",
      items: {
        type: "object",
        additionalProperties: false,
        required: ["node", "ops", "drops", "adds", "readings", "corollaries", "umbrella", "proof_note", "owner_explanation", "consequence_of", "reason"],
        properties: {
          node: { type: "string" },
          ops: OPS_JSON,
          drops: HYPOTHESES_JSON,
          adds: HYPOTHESES_JSON,
          readings: READINGS_JSON,
          corollaries: COROLLARIES_JSON,
          umbrella: UMBRELLA_JSON,
          proof_note: TEX_STRING_OR_NULL,
          // Null on a consequential patch (`consequence_of`), which explains itself in `reason`.
          owner_explanation: { anyOf: [OWNER_EXPLANATION_JSON, { type: "null" }] },
          consequence_of: { anyOf: [{ type: "array", items: { type: "string" } }, { type: "null" }] },
          reason: TEX_STRING_OR_NULL,
        },
      },
    },
    unfixable: {
      type: "array",
      items: {
        type: "object",
        additionalProperties: false,
        required: ["node", "reason", "suggested_repair", "owner_explanation"],
        properties: {
          node: { type: "string" },
          reason: TEX_STRING_NONEMPTY,
          owner_explanation: OWNER_EXPLANATION_JSON,
          suggested_repair: {
            anyOf: [
              {
                type: "object",
                additionalProperties: false,
                required: ["ops", "drops", "adds", "readings", "corollaries", "umbrella", "proof_note"],
                properties: {
                  ops: OPS_JSON,
                  drops: HYPOTHESES_JSON,
                  adds: HYPOTHESES_JSON,
                  readings: READINGS_JSON,
                  corollaries: COROLLARIES_JSON,
                  umbrella: UMBRELLA_JSON,
                  proof_note: TEX_STRING_OR_NULL,
                },
              },
              { type: "null" },
            ],
          },
        },
      },
    },
    rejected: {
      type: "array",
      items: {
        type: "object",
        additionalProperties: false,
        required: ["node", "reason", "where_the_paper_grants_it"],
        properties: { node: { type: "string" }, reason: { type: "string" }, where_the_paper_grants_it: { type: "string" } },
      },
    },
  },
};

/** Unfixable nodes a key result rests on (the node is key, or in a key result's closure) with nothing
 * of them left to suggest. Any such node stops the run: the paper's key contribution cannot be kept.
 * An entry that suggests a weakened repair is the owner's to rule on instead (`weakening.ts`): it
 * halts until then, and a declined one is descoped with everything resting on it. */
export function blockedUnfixable(core: Core, file: PatchFile): string[] {
  const keyPath = statementClosure(core, file.key_results);
  const nodeIds = new Set([...core.assumptions.map((a) => a.id), ...core.definitions.map((d) => d.id)]);
  return file.unfixable
    .filter((u) => !u.suggested_repair)
    .map((u) => u.node)
    .filter((id) => {
      if (keyPath.has(id)) return true;
      // An unfixable assumption / definition blocks when a key-path statement uses it.
      return nodeIds.has(id) && core.statements.some((s) => keyPath.has(s.id) && s.depends_on.includes(id));
    });
}

/**
 * The file without the `drops` (of a repair or a suggestion) that name a hypothesis of the core the result
 * no longer depends on while another result still does (a re-extraction unwired it since the repair was
 * written): such a drop changes nothing, so it is moot, not wrong. One no result uses any more stays: the
 * build removes that hypothesis from the core by it (`compilePatchEdits`). Returns the file (a copy, or
 * the same object when nothing is moot) and one line per entry removed. Pure.
 */
export function withoutMootDrops<F extends PatchFile>(core: Core, file: F): { file: F; removed: string[] } {
  const statements = new Map(core.statements.map((s) => [s.id, s] as const));
  const hypotheses = new Set([...core.assumptions.map((a) => a.id), ...core.definitions.map((d) => d.id)]);
  const used = new Set(core.statements.flatMap((s) => s.depends_on));
  const removed: string[] = [];
  const next = structuredClone(file);
  const prune = (node: string, x: { drops?: string[] | null } | null | undefined, what: string): void => {
    const st = statements.get(node);
    if (!st || !x?.drops?.length) return;
    const moot = x.drops.filter((d) => hypotheses.has(d) && used.has(d) && !st.depends_on.includes(d));
    if (moot.length === 0) return;
    removed.push(`${what}${node}: ${moot.join(", ")}`);
    const kept = x.drops.filter((d) => !moot.includes(d));
    if (kept.length > 0) x.drops = kept;
    else delete x.drops;
  };
  for (const p of next.patches) prune(p.node, p, "");
  for (const u of next.unfixable) prune(u.node, u.suggested_repair, "the suggestion on ");
  return removed.length > 0 ? { file: next, removed } : { file, removed };
}

/**
 * Mechanical checks on a patch file against the TRANSCRIBED core. `required` = the node ids the
 * referee's findings name (each must be patched or declared unfixable, exactly once). A
 * violation goes back to the fixer; the mathematics is the confirming referee's.
 */
export function validatePatchFile(core: Core, file: PatchFile, required: readonly string[]): string[] {
  const out = validateShape(core, file, required);
  // A suggested repair must be a well-formed patch too: the owner may apply it as one.
  const suggesting = new Set(file.unfixable.filter((u) => u.suggested_repair).map((u) => u.node));
  if (suggesting.size > 0) {
    for (const v of validateShape(core, applySuggestions(file, suggesting), required)) {
      if (!out.includes(v)) out.push(`(suggested repair) ${v}`);
    }
  }
  return out;
}

function validateShape(core: Core, file: PatchFile, required: readonly string[]): string[] {
  const out: string[] = [];
  const statements = new Map(core.statements.map((s) => [s.id, s] as const));
  const coreIds = new Set<string>([
    ...core.statements.map((s) => s.id),
    ...core.assumptions.map((a) => a.id),
    ...core.definitions.map((d) => d.id),
  ]);

  // Coverage: every finding addressed exactly once.
  const addressed = [...file.patches.map((p) => p.node), ...file.unfixable.map((u) => u.node)];
  for (const id of required) {
    const n = addressed.filter((a) => a === id).length;
    if (n === 0) out.push(`node "${id}" has a finding but neither a patch nor an \`unfixable\` entry.`);
  }
  for (const id of new Set(addressed)) {
    if (addressed.filter((a) => a === id).length > 1) out.push(`node "${id}" is addressed more than once (one patch or one unfixable entry per node).`);
    if (!coreIds.has(id)) out.push(`node "${id}" is not a node of the core.`);
  }

  // Key results: existing statements, always named.
  const fixerWrote = file.patches.length > 0 || file.unfixable.length > 0;
  if (fixerWrote && file.key_results.length === 0) out.push("`key_results` is empty: name the paper's headline results.");
  if (fixerWrote && !file.key_contribution.trim()) out.push("`key_contribution` is empty: state what the paper establishes that every patch must keep.");
  for (const id of file.key_results) if (!statements.has(id)) out.push(`key result "${id}" is not a statement of the core.`);

  // Dropped dependencies: only a result drops one, and only one it depends on (a hypothesis, or a
  // result its corrected text no longer relies on) — or a result its text only cites, which the
  // build then leaves unwired (`compilePatchEdits`). A repair of the proof alone drops only a
  // published result that proof invoked by citation (`cited_in`): the step is no longer taken from it.
  const hypotheses = new Set([...core.assumptions.map((a) => a.id), ...core.definitions.map((d) => d.id)]);
  // `adds` takes hypotheses only; a result named there is told where a used result goes instead.
  const notAHypothesis = (a: string): string => {
    const label = statements.get(a)?.tex_locator?.label;
    return (
      "which is not an assumption or definition of the core: `adds` lists only hypotheses (assumptions, definitions)." +
      (statements.has(a) ? ` "${a}" is a result — a result the corrected statement or proof uses is cited by \\ref${label ? `{${label}}` : " of its label"} in the text; remove it from \`adds\`.` : "")
    );
  };
  for (const p of file.patches) {
    if (!p.drops?.length) continue;
    const st = statements.get(p.node);
    if (!st) out.push(`the patch for "${p.node}" gives \`drops\`, but "${p.node}" is not a result: only a result drops a node it no longer uses — set \`drops\` to null.`);
    else if (p.corrected_statement === null && p.drops.some((d) => statements.get(d)?.cited_in !== p.node)) out.push(`the patch for "${p.node}" drops dependencies but leaves the statement as printed: a result drops one only in its corrected statement.`);
    // (a hypothesis no result uses any more may be dropped: the build removes it from the core)
    else for (const d of p.drops) if (!st.depends_on.includes(d) && (!statements.has(d) || d === p.node) && !(hypotheses.has(d) && !core.statements.some((s) => s.depends_on.includes(d)))) out.push(`the patch for "${p.node}" drops "${d}", which "${p.node}" does not depend on.`);
  }
  // Added hypotheses: only a result adds one, stated by its corrected text; one the build would unwire
  // (the replacement rewrites its text) is wired back.
  const unfixable = new Set(file.unfixable.map((u) => u.node));
  for (const p of file.patches) {
    if (!p.adds?.length) continue;
    const st = statements.get(p.node);
    if (!st) out.push(`the patch for "${p.node}" gives \`adds\`, but "${p.node}" is not a result: only a result adds a hypothesis — set \`adds\` to null.`);
    else if (p.corrected_statement === null) out.push(`the patch for "${p.node}" adds hypotheses but leaves the statement as printed: a result adds a hypothesis only by imposing it in its corrected statement.`);
    else
      for (const a of p.adds) {
        if (!hypotheses.has(a)) out.push(`the patch for "${p.node}" adds "${a}", ${notAHypothesis(a)}`);
        else if (unfixable.has(a)) out.push(`the patch for "${p.node}" adds "${a}", which is set aside as unfixable.`);
        else if (p.drops?.includes(a)) out.push(`the patch for "${p.node}" both adds and drops "${a}".`);
      }
  }

  // Corollaries: only a result is split; each is a statement of its own (a fresh id), assuming only
  // hypotheses of the core. A corollary never restates its parent: that is no split.
  const splitIds = new Set<string>();
  for (const p of file.patches) {
    if (p.umbrella) {
      // An umbrella states nothing of its own: at least two blocks, and no text, hypothesis or reading change on the node.
      const what = `the patch for "${p.node}" is an umbrella (\`umbrella: true\`)`;
      if ((p.corollaries?.length ?? 0) < 2) out.push(`${what} but gives ${p.corollaries?.length ?? 0} block(s): an umbrella is a statement mixing several conclusions under different conditions, each a block of \`corollaries\` — give at least two, or set \`umbrella\` to null.`);
      if ((p.ops?.length ?? 0) > 0) out.push(`${what} but gives \`ops\`: an umbrella has no statement or proof of its own (the pipeline writes its sentence) — give no ops and move every conclusion, with its proof, into a block.`);
      if (p.drops?.length || p.adds?.length) out.push(`${what} but gives \`drops\` / \`adds\`: an umbrella uses no hypothesis itself — set both to null and list each block's hypotheses in that block's \`adds\`.`);
      if (p.consequence_of?.length) out.push(`${what} but is a consequential patch: an umbrella follows its blocks by construction.`);
    }
    if (!p.corollaries?.length) continue;
    const st = statements.get(p.node);
    if (!st) {
      out.push(`the patch for "${p.node}" gives \`corollaries\`, but "${p.node}" is not a result: only a result is split — set \`corollaries\` to null.`);
      continue;
    }
    const bare = (t: string): string => t.replace(/\s+/gu, "");
    const label = st.tex_locator?.label?.trim();
    for (const [k, c] of corollaryNodes(p.node, p).entries()) {
      const what = `corollary ${k + 1} of the patch for "${p.node}"`;
      if (splitIds.has(c.id) || coreIds.has(c.id)) out.push(`${what} repeats another corollary: state each once.`);
      splitIds.add(c.id);
      if (p.umbrella) {
        // Under an umbrella every block is a proposition: the umbrella rests on its blocks, so a block
        // resting on it (citing it, or a result that uses it) would be circular.
        if (label && citedLabels(c.follows).includes(label)) out.push(`${what} cites "${p.node}" (\\ref{${label}}) in \`follows\`, but "${p.node}" is an umbrella (\`umbrella: true\`): it only says that its blocks hold, so no block's proof may cite it — prove the block from the results it rests on, or, when the statement has a main claim of its own that this block follows from, set \`umbrella\` to null and keep that claim as the statement.`);
        for (const l of citedLabels(`${c.statement}\n${c.follows}`)) {
          const hit = core.statements.filter((s) => s.tex_locator?.label === l && s.id !== p.node);
          if (hit.length === 1 && statementClosure(core, [hit[0]!.id]).has(p.node)) out.push(`${what} cites "${hit[0]!.id}" (\\ref{${l}}), which rests on "${p.node}" itself: under an umbrella that is circular — a block rests only on results that do not use "${p.node}".`);
        }
        continue;
      }
      if (bare(c.statement) === bare(p.corrected_statement ?? st.statement)) out.push(`${what} restates the result itself: a corollary is a special case holding under its own conditions, stated apart.`);
      for (const a of c.adds ?? []) {
        if (!hypotheses.has(a)) out.push(`${what} adds "${a}", ${notAHypothesis(a)}`);
        else if (unfixable.has(a)) out.push(`${what} adds "${a}", which is set aside as unfixable.`);
      }
    }
  }

  // Owner readings: fresh ids, on nodes of the core, one per node.
  const pinIds = new Set<string>();
  for (const r of file.owner_readings ?? []) {
    if (coreIds.has(r.id) || pinIds.has(r.id)) out.push(`owner reading "${r.id}" collides with another node id.`);
    pinIds.add(r.id);
    if (!coreIds.has(r.node)) out.push(`owner reading "${r.id}" is on "${r.node}", which is not a node of the core.`);
  }
  return out;
}

/** `core.json` = the transcribed core + the patch file (no referee additions). Pure; see
 * `buildCore`. A patched statement's text is replaced by its corrected form and its proof carries
 * the proof change after the paper's own proof; unfixable non-key results (and what rests on
 * them) are removed; everything else of the paper is kept as transcribed. */
export function applyPatchFile(transcribed: Core, file: PatchFile): { core: Core; descoped: Map<string, string> } {
  const { core, descoped } = buildCore(transcribed, { patches: file });
  return { core, descoped };
}

/** The file with every umbrella's derived texts set (`UMBRELLA_STATEMENT`, `UMBRELLA_PROOF`): never
 * the fixer's, never authoritative as stored. A copy when anything changes. Pure. */
export function canonicalUmbrellas(file: PatchFile): PatchFile {
  const fix = <T extends { umbrella?: boolean; corollaries?: unknown[]; corrected_statement: string | null; proof_note: string }>(x: T): T =>
    isUmbrellaPatch(x) && (x.corrected_statement !== UMBRELLA_STATEMENT || x.proof_note !== UMBRELLA_PROOF) ? { ...x, corrected_statement: UMBRELLA_STATEMENT, proof_note: UMBRELLA_PROOF } : x;
  const patches = file.patches.map(fix);
  const unfixable = file.unfixable.map((u) => (u.suggested_repair && fix(u.suggested_repair) !== u.suggested_repair ? { ...u, suggested_repair: fix(u.suggested_repair) } : u));
  return patches.some((p, i) => p !== file.patches[i]) || unfixable.some((u, i) => u !== file.unfixable[i]) ? { ...file, patches, unfixable } : file;
}

/**
 * A split repair converted to the UMBRELLA form without a fixer round (`--umbrella`, the
 * orchestrator's; `owner_rulings.ts` `convertToUmbrella`): what the corrected statement of `node` still
 * states becomes one more proposition block, after the blocks on file — its statement the corrected
 * text (the printed one when the repair left it), its proof the proof the patch holds for the node (the
 * amended proof, or the full proof the fixer wrote; the printed proof when the patch left it as
 * printed), its `adds` the hypotheses the corrected node uses — and the patch becomes the umbrella: no
 * ops, no hypotheses of its own; its readings, note and rulings stay. Throws, saying why, when the node
 * has no applied repair with blocks, is an umbrella already, has a block that is a corollary of it (the
 * statement then has a main claim: the split form stands) or has no proof to give the block. Pure.
 */
export function umbrellaConversion(transcribed: Core, file: PatchFile, node: string, title?: string): { file: PatchFile; block: SplitCorollary & { id: string } } {
  const p = file.patches.find((x) => x.node === node);
  const st = transcribed.statements.find((s) => s.id === node);
  if (!st) throw new Error(`--umbrella ${node}: not a result of the core.`);
  if (!p) throw new Error(`--umbrella ${node}: no applied repair of it in ${VERIFY_FILES.patches} (a suggested repair awaiting the owner is ruled on first).`);
  if (p.umbrella) throw new Error(`--umbrella ${node}: it is an umbrella already.`);
  if (!p.corollaries?.length) throw new Error(`--umbrella ${node}: its repair splits off no block — an umbrella is a statement whose conclusions are ALL blocks; only a repair that already splits is converted.`);
  const label = st.tex_locator?.label?.trim();
  const citing = p.corollaries.map((c, k) => ({ c, k })).filter(({ c }) => !label || citedLabels(c.follows).includes(label));
  if (citing.length > 0) throw new Error(`--umbrella ${node}: block ${citing.map(({ k }) => k + 1).join(", ")} is a corollary of the corrected statement (${label ? `its proof cites \\ref{${label}}` : "the result has no label, so no block can be told apart from one"}) — the statement has a main claim of its own and the split form stands.`);
  const strip = (t: string): string => statementBody(t).replace(/\\label\s*\{[^{}]*\}\s*/gu, "").trim();
  const statement = strip(p.corrected_statement ?? st.statement);
  const proof = p.proof_note !== PROOF_UNCHANGED ? p.proof_note.trim() : (st.proof_tex ?? "").trim();
  if (!proof) throw new Error(`--umbrella ${node}: neither the repair nor the paper holds a proof of what the statement still claims — write that block (statement and proof) into the patch's \`corollaries\` by hand, set \`umbrella: true\` and empty its ops, then --from-stage V1.5.`);
  if (label && citedLabels(proof).includes(label)) throw new Error(`--umbrella ${node}: the proof of the corrected statement cites the result itself (\\ref{${label}}); under an umbrella that is circular.`);
  // The hypotheses the corrected node uses: its wiring in the patched core, of the paper's own nodes.
  const hypotheses = new Set([...transcribed.assumptions, ...transcribed.definitions].map((n) => n.id));
  const built = buildCore(transcribed, { patches: file }).core.statements.find((s) => s.id === node);
  if (!built) throw new Error(`--umbrella ${node}: the result is left out of the core (unfixable or descoped).`);
  const adds = built.depends_on.filter((d) => hypotheses.has(d));
  const block: SplitCorollary = { ...(title?.trim() ? { title: title.trim() } : {}), statement, follows: proof, ...(adds.length > 0 ? { adds } : {}) };
  const id = splitCorollaryId(node, statement);
  if (corollaryNodes(node, p).some((c) => c.id === id)) throw new Error(`--umbrella ${node}: what the statement still states is one of its blocks already.`);
  const { ops: _o, supersedes: _s, drops: _d, adds: _a, ...rest } = p;
  const next: Patch = { ...rest, ops: [], corrected_statement: UMBRELLA_STATEMENT, proof_note: UMBRELLA_PROOF, umbrella: true, corollaries: [...p.corollaries, block] };
  return { file: { ...file, patches: file.patches.map((x) => (x === p ? next : x)) }, block: { ...block, id } };
}

/** The run's patch file, every repair's texts derived from its ops under the current rules
 * (`rederiveRepairs`: a derived text is never authoritative, so every reader sees the same text). A
 * file that does not fit the schema (hand-edited, or an op other than `replace`) is the operator's to
 * fix: a `CoreGraphInputError`, which the stages checkpoint on. */
export async function readPatchFile(runDir: string): Promise<PatchFile | null> {
  const p = path.join(runDir, VERIFY_FILES.patches);
  if (!existsSync(p)) return null;
  const raw = JSON.parse(await readFile(p, "utf8")) as unknown;
  // The format before replacements carried hypothesis edits as `add_assumptions` /
  // `remove_depends_on`; the schema is not strict, so one that carries any is refused by name
  // rather than silently dropped (an empty list carries nothing).
  const legacy = ((raw as { patches?: unknown[] } | null)?.patches ?? []).flatMap((x, k) =>
    ["add_assumptions", "remove_depends_on"]
      .filter((key) => Array.isArray((x as Record<string, unknown> | null)?.[key]) && ((x as Record<string, unknown[]>)[key]!.length > 0))
      .map((key) => `patches.${k}.${key}: the format before replacements; rewrite the patch as replacements`));
  if (legacy.length > 0) throw new CoreGraphInputError("patches.json", legacy);
  const parsed = PatchFileSchema.safeParse(raw);
  if (!parsed.success) throw new CoreGraphInputError("patches.json", parsed.error.issues.map((i) => `${i.path.join(".") || "(file)"}: ${i.message}`));
  const file = canonicalUmbrellas(parsed.data);
  const src = await repairSources(runDir);
  return src ? rederiveOn(file, src).file : file;
}

/** V1 accepted a transcription: keep the unpatched copy, then re-apply any patches on top. A
 * patch file that no longer fits the new transcription (a re-transcription renamed or dropped a
 * node it names) is the operator's to fix: the plain transcription stands as `core.json`, and the
 * problem is returned for the log — V1.5's entry check then checkpoints on the same file. */
export async function snapshotTranscribedCore(runDir: string, verify: { transcribed_written_sha256?: string | null }): Promise<string | null> {
  const corePath = path.join(runDir, VERIFY_FILES.coreJson);
  const transcribed = path.join(runDir, VERIFY_FILES.coreTranscribed);
  await copyFile(corePath, transcribed);
  verify.transcribed_written_sha256 = await sha256File(transcribed);
  try {
    await rebuildPatchedCore(runDir, { detectHandEdits: false });
    return null;
  } catch (err) {
    if (!(err instanceof CoreGraphInputError)) throw err;
    return `${VERIFY_FILES.patches} does not fit the accepted transcription; core.json is the plain transcription until it is fixed. ${err.problems.join(" ")}`;
  }
}

/** A core without what V1.5 adds on acceptance (bookkeeping conditions and pinned readings): the
 * part of `core.json` that is a pure function of the transcription and the patch file. `used_by`
 * is dropped too — it is derived, and the derivation sees the review additions. */
function withoutReviewAdditions(core: Core): Core {
  const added = new Set(core.assumptions.filter((a) => a.bookkeeping?.added_by === REVIEW_ADDED_BY).map((a) => a.id));
  return {
    ...core,
    assumptions: core.assumptions.filter((a) => !added.has(a.id)).map(({ used_by: _u, ...a }) => a as Core["assumptions"][number]),
    statements: core.statements.map((st) => ({ ...st, depends_on: st.depends_on.filter((d) => !added.has(d)) })),
  };
}

/** The transcribed core: `core.transcribed.json`. */
export async function readTranscribedCore(runDir: string): Promise<Core> {
  const transcribed = path.join(runDir, VERIFY_FILES.coreTranscribed);
  if (!existsSync(transcribed)) throw new Error(`${VERIFY_FILES.coreTranscribed} is missing: V1 writes it with every accepted transcription — re-extract with --from-stage V1.`);
  return parseTypedCore(await readFile(transcribed, "utf8"), `verify core ${transcribed}`);
}

/** The symbol referee's verdicts on file (`v1_5_symbols.json`), whose table fixes every build of
 * `core.json` applies; none when absent or unreadable (the next V1.5 re-grades the symbols). */
export async function readSymbolFixes(runDir: string): Promise<V15SymbolVerdict[]> {
  const p = path.join(runDir, VERIFY_FILES.v15Symbols);
  if (!existsSync(p)) return [];
  try {
    const j = JSON.parse(await readFile(p, "utf8")) as { symbols?: V15SymbolVerdict[] };
    return Array.isArray(j?.symbols) ? j.symbols : [];
  } catch {
    return [];
  }
}

/**
 * Rewrite `core.json` from the transcribed core and the patch file (and the symbol table fixes). `core.json` is the RUNNER's:
 * a transcription fix belongs in `core_refs.json` (V1 builds the transcription from it), a repair in `patches.json`, and a
 * deleted patch file leaves the plain transcription. A `core.json` that differs from what these
 * two files give (beyond V1.5's own acceptance additions), and that changed since the runner last
 * wrote it, was edited by hand; it is kept as `core.json.prev` and reported, never silently
 * discarded. A changed patch file (the owner's repair or reading) only makes the rebuild differ.
 */
export async function rebuildPatchedCore(
  runDir: string,
  opts: { detectHandEdits?: boolean } = {},
): Promise<{ patched: boolean; descoped: Map<string, string>; handEdited: boolean | "unknown" }> {
  const corePath = path.join(runDir, VERIFY_FILES.coreJson);
  const file = await readPatchFile(runDir);
  const transcribed = await readTranscribedCore(runDir);
  const { core, descoped } = buildCore(transcribed, { patches: file, symbols: await readSymbolFixes(runDir) });
  // `unknown`: the file differs from its rebuild and no write of the runner's is on record (a run
  // from before that record) — built by an earlier version, or edited; nothing says which.
  let handEdited: boolean | "unknown" = false;
  if (existsSync(corePath)) {
    const onDisk = parseTypedCore(await readFile(corePath, "utf8"), `verify core ${corePath}`);
    // Parse both sides the same way so that schema defaults never read as an edit.
    const built = parseTypedCore(JSON.stringify(core), "rebuilt core");
    // Unchanged content is not rewritten: the file's bytes are what every accepted-core hash
    // is taken over.
    if (JSON.stringify(onDisk) === JSON.stringify(built)) {
      if ((await coreEditedSinceWrite(corePath)) !== false) await recordCoreWrite(corePath);
      return { patched: file !== null, descoped, handEdited };
    }
    const canon = (c: Core): string => JSON.stringify(withoutReviewAdditions(c));
    // Only at a V1.5 entry is a difference an operator's edit; V1 rebuilding after it wrote a new
    // transcription or patch file changes core.json by design.
    const edited = opts.detectHandEdits !== false && canon(onDisk) !== canon(built) ? await coreEditedSinceWrite(corePath) : false;
    if (edited !== false) {
      handEdited = edited ?? "unknown";
      await copyFile(corePath, `${corePath}.prev`);
    }
  }
  await writeCoreJson(corePath, core);
  return { patched: file !== null, descoped, handEdited };
}

/** The report's view of one patch. */
export function findingPatch(p: Patch, confirmed: boolean): FindingPatch {
  return {
    corrected_statement: p.corrected_statement,
    proof_note: p.proof_note,
    confirmed,
    ...(p.corollaries?.length ? { corollaries: corollaryNodes(p.node, p).map((c) => c.id) } : {}),
    ...(isUmbrellaPatch(p) ? { umbrella: true } : {}),
    ...(p.accepted_weakening ? { narrowed: p.given_up ?? "the owner accepted a repair that weakens the claim" } : {}),
    ...(p.accepted_weakening && p.narrowed_by === "runner" ? { narrowed_by: "runner" as const } : {}),
  };
}

/**
 * The fixer's reply (raw JSON) with every repair's texts DERIVED from its ops (`ops.ts`
 * `materializeRepair`): `corrected_statement` (null when no op changes the node's text), `proof_note` (the
 * amended proof when an op changes it; else the fixer's own — the full proof when the paper prints none —
 * or "the proof as printed"), and a suggestion's `given_up` (its note's `gives_up`, when it gives something
 * up). The problems found are contract violations the fixer answers: an op that does not resolve, no
 * proof where one is needed. `scopeOf` resolves a node's passage; `proofGiven` whether a node
 * needs no proof of the fixer's (the paper prints its proof, or it is no result: an assumption or a
 * definition); `supersededOf` the dependencies the replacement rewrites (`supersedes`). Pure.
 */
export function materializeReply(
  raw: unknown,
  scopeOf: (node: string) => RepairScope,
  proofGiven: (node: string) => boolean,
  supersededOf: (node: string, ops: readonly PatchOp[]) => string[] = () => [],
): { raw: unknown; violations: string[] } {
  if (!raw || typeof raw !== "object") return { raw, violations: [] };
  const r = structuredClone(raw) as { patches?: Array<Record<string, unknown>>; unfixable?: Array<Record<string, unknown>> };
  const violations: string[] = [];
  const setGivenUp = (x: Record<string, unknown>, explanation: unknown): void => {
    const g = explanation && typeof explanation === "object" ? (explanation as { gives_up?: unknown }).gives_up : null;
    if (typeof g === "string" && g.trim()) x.given_up = g.trim();
    else delete x.given_up;
  };
  const derive = (x: Record<string, unknown>, node: string, where: string, suggestion: boolean, explanation: unknown): void => {
    const parsed = z.array(PatchOpSchema).safeParse(x.ops ?? []);
    if (!parsed.success) return void violations.push(`${where}: \`ops\` does not parse: ${parsed.error.issues.map((i) => i.message).join("; ")}`);
    x.ops = parsed.data;
    // A detail completes a proof step: the statement, a reading or a block's statement takes none.
    parsed.data.forEach((op, k) => {
      if (isStatementOp(op) && hasDetail(op.tex)) violations.push(`${where}: ops[${k}] (${op.op}) replaces text of the statement and holds a \`\\vsDetail\`: only proof text (proof ops, \`proof_note\`, a block's \`follows\`) takes a detail`);
    });
    const texts = (v: unknown, pick: (e: Record<string, unknown>) => unknown = (e) => e): string[] => (Array.isArray(v) ? v.map((e) => pick(e as Record<string, unknown>)).filter((t): t is string => typeof t === "string") : []);
    if ([...texts(x.readings), ...texts(x.corollaries, (c) => c?.statement)].some(hasDetail)) violations.push(`${where}: a reading or a block's statement holds a \`\\vsDetail\`: only proof text (proof ops, \`proof_note\`, a block's \`follows\`) takes a detail`);
    // An umbrella takes its texts from the pipeline (ops on it are a violation, `validatePatchFile`).
    if (x.umbrella === true && Array.isArray(x.corollaries) && x.corollaries.length > 0 && parsed.data.length === 0) {
      x.corrected_statement = UMBRELLA_STATEMENT;
      x.proof_note = UMBRELLA_PROOF;
      delete x.supersedes;
      if (suggestion) setGivenUp(x, explanation);
      return;
    }
    const m = materializeRepair(parsed.data, scopeOf(node), where);
    violations.push(...m.problems);
    x.corrected_statement = m.corrected_statement;
    const sup = m.problems.length === 0 ? supersededOf(node, parsed.data) : [];
    if (sup.length > 0) x.supersedes = sup;
    else delete x.supersedes;
    const own = typeof x.proof_note === "string" ? x.proof_note.trim() : "";
    if (m.proof !== null) x.proof_note = m.proof;
    else if (own) x.proof_note = own;
    else if (proofGiven(node)) x.proof_note = PROOF_UNCHANGED;
    else violations.push(`${where}: the paper prints no proof of this result — give the full proof in \`proof_note\``);
    if (suggestion) setGivenUp(x, explanation);
  };
  for (const p of r.patches ?? []) if (typeof p?.node === "string") derive(p, p.node, `the patch for "${p.node}"`, false, p.owner_explanation);
  for (const u of r.unfixable ?? []) {
    if (typeof u?.node !== "string" || !u.suggested_repair || typeof u.suggested_repair !== "object") continue;
    derive(u.suggested_repair as Record<string, unknown>, u.node, `the suggested repair for "${u.node}"`, true, u.owner_explanation);
  }
  return { raw: r, violations };
}

/** The repairs of a patch file (patches and suggested repairs) whose ops do not resolve on the paper's
 * units as they stand (a re-transcription moved the passage): one problem per op. Pure. */
export function unresolvedRepairs(file: Pick<PatchFile, "patches" | "unfixable">, src: PassageSources): string[] {
  const bodies = [...file.patches.map((p) => ({ node: p.node, ops: p.ops ?? [] })), ...file.unfixable.flatMap((u) => (u.suggested_repair?.ops ? [{ node: u.node, ops: u.suggested_repair.ops }] : []))];
  return bodies.flatMap((b) => (b.ops.length === 0 ? [] : materializeRepair(b.ops, { units: src.units, passage: nodePassage(src, b.node) }, `the repair of "${b.node}"`).problems));
}

/**
 * The entry of a hypothesis with no printed text of its own (`isTextless`: an assumption or a definition
 * `nodePassage` does not locate — running prose, or inside a result's statement) is bookkeeping: the
 * results using it are restated instead. Whatever the fixer wrote for such a node — a patch, an
 * `unfixable` entry, a suggestion — becomes a patch with no ops whose note (when it has one) gives
 * nothing up. Returns the reply (a copy) and the nodes normalized. Pure.
 */
export function normalizeTextlessEntries(raw: unknown, isTextless: (node: string) => boolean): { raw: unknown; nodes: string[] } {
  if (!raw || typeof raw !== "object") return { raw, nodes: [] };
  const r = structuredClone(raw) as { patches?: Array<Record<string, unknown>>; unfixable?: Array<Record<string, unknown>> };
  const nodes: string[] = [];
  const noteOf = (oe: unknown): unknown => (oe && typeof oe === "object" ? { ...(oe as Record<string, unknown>), gives_up: null } : oe);
  const moved = (r.unfixable ?? []).filter((u) => typeof u?.node === "string" && isTextless(u.node as string));
  r.unfixable = (r.unfixable ?? []).filter((u) => !moved.includes(u));
  for (const u of moved) {
    if (!(r.patches ?? []).some((p) => p.node === u.node)) (r.patches ??= []).push({ node: u.node, ops: [], proof_note: null, owner_explanation: noteOf(u.owner_explanation) ?? null, consequence_of: null, reason: null });
    nodes.push(u.node as string);
  }
  for (const p of r.patches ?? []) {
    if (typeof p?.node !== "string" || !isTextless(p.node) || Array.isArray(p.ops) && p.ops.length > 0) continue;
    p.owner_explanation = noteOf(p.owner_explanation) ?? null;
    if (!nodes.includes(p.node)) nodes.push(p.node);
  }
  return { raw: r, nodes };
}

/** One printed text takes one replacement: two repairs of a patch file (patches and suggested
 * repairs) may replace overlapping printed text only identically. A violation per clashing pair, with
 * both replacements; `locked` (entries the fixer cannot change this round, e.g. a suggestion awaiting
 * the owner): a pair with one side locked asks for the other side to follow it, a pair locked on both
 * sides is not reported (the V1.5 entry check reports it). Pure. */
export function overlapViolations(file: Pick<PatchFile, "patches" | "unfixable">, scopeOf: (node: string) => RepairScope, locked: ReadonlySet<string> = new Set()): string[] {
  // A declined suggestion prints nothing: it takes no printed text.
  const spans = [...file.patches.map((p) => ({ node: p.node, ops: p.ops ?? [] })), ...file.unfixable.flatMap((u) => (u.suggested_repair?.ops && !u.declined ? [{ node: u.node, ops: u.suggested_repair.ops }] : []))]
    .map((x) => ({ node: x.node, changes: resolveOps(x.ops, scopeOf(x.node), x.node).changes }));
  const out: string[] = [];
  for (let i = 0; i < spans.length; i += 1) {
    for (let j = i + 1; j < spans.length; j += 1) {
      const [a, b] = [spans[i]!, spans[j]!];
      if (a.node === b.node) continue;
      if (locked.has(a.node) && locked.has(b.node)) continue;
      const clash = a.changes.find((x) => b.changes.some((y) => x.start < y.end && y.start < x.end && !(x.start === y.start && x.end === y.end && x.text === y.text)));
      if (!clash) continue;
      const other = b.changes.find((y) => clash.start < y.end && y.start < clash.end)!;
      const texts = ` ("${a.node}" writes: ${JSON.stringify(clash.tex)}; "${b.node}" writes: ${JSON.stringify(other.tex)})`;
      const fixed = locked.has(a.node) ? a.node : locked.has(b.node) ? b.node : null;
      const free = fixed === a.node ? b.node : a.node;
      out.push(
        fixed
          ? `the repairs of "${a.node}" and "${b.node}" both replace the printed text at unit ${clash.first.id}, differently${texts} — "${fixed}" awaits the owner and stays as it is: give "${free}" the same replacement of that text, or leave that text to "${fixed}".`
          : `the repairs of "${a.node}" and "${b.node}" both replace the printed text at unit ${clash.first.id}, differently${texts} — one printed passage takes one text: give the same replacement in both, or make the change in one of them.`,
      );
    }
  }
  return out;
}

/**
 * Every stored repair's texts DERIVED AGAIN from its ops with the current rules (design 2026-09-26; on
 * every read, `readPatchFile`): a derived text is never authoritative. For each patch and suggested repair with ops, `corrected_statement`
 * and the amended proof (`proof_note`, when an op changes the proof) are materialized
 * (`materializeRepair`); a text differing only in whitespace or labels is kept as stored. A repair whose
 * ops no longer resolve is left as stored (the fixer's check routes it). Returns the file (a copy) and,
 * per changed repair, the node and whether it is an applied patch (whose change moves `core.json`). Pure.
 */
export function rederiveRepairs(
  file: PatchFile,
  scopeOf: (node: string) => RepairScope,
  supersededOf: (node: string, ops: readonly PatchOp[]) => string[] = () => [],
): { file: PatchFile; changed: Array<{ node: string; applied: boolean; fields: string[] }> } {
  const next = structuredClone(file);
  const changed: Array<{ node: string; applied: boolean; fields: string[] }> = [];
  const derive = (x: { ops?: PatchOp[] | null; corrected_statement?: string | null; proof_note?: string | null; supersedes?: string[] } | null | undefined, node: string, applied: boolean): void => {
    if (!x?.ops || x.ops.length === 0) return;
    const m = materializeRepair(x.ops, scopeOf(node), node);
    if (m.problems.length > 0) return;
    const fields: string[] = [];
    // A difference in whitespace or labels alone is no change (the paper prints neither): the stored
    // text stands, so its basis does not move.
    const bare = (t: string): string => t.replace(/\\label\s*\{[^{}]*\}/gu, "").replace(/\s+/gu, "");
    const same = (a: string | null | undefined, b: string | null | undefined): boolean => (a ?? null) === (b ?? null) || (a != null && b != null && bare(a) === bare(b));
    if (!same(m.corrected_statement, x.corrected_statement)) {
      x.corrected_statement = m.corrected_statement;
      fields.push("corrected_statement");
    }
    if (m.proof !== null && !same(m.proof, x.proof_note)) {
      x.proof_note = m.proof;
      fields.push("proof_note");
    }
    const sup = supersededOf(node, x.ops);
    if (JSON.stringify(sup) !== JSON.stringify(x.supersedes ?? [])) {
      if (sup.length > 0) x.supersedes = sup;
      else delete x.supersedes;
      fields.push("supersedes");
    }
    if (fields.length > 0) changed.push({ node, applied, fields });
  };
  for (const p of next.patches) derive(p, p.node, true);
  for (const u of next.unfixable) derive(u.suggested_repair, u.node, false);
  return { file: next, changed };
}

/**
 * The passage sources a run's stored ops resolve against: the parse of `flat.tex` (never written here),
 * `envs.json`, `core_refs.json` and the transcribed core (its statements and assumptions). Null when the
 * run has no units or no transcription. Reads only.
 */
export async function repairSources(runDir: string): Promise<PassageSources | null> {
  const envsFile = path.join(runDir, VERIFY_FILES.envsJson);
  const units = existsSync(envsFile) ? await loadUnits(runDir, { write: false }) : null;
  if (!units) return null;
  const tr = path.join(runDir, VERIFY_FILES.coreTranscribed);
  if (!existsSync(tr)) return null;
  const transcribed = parseTypedCore(await readFile(tr, "utf8"), `verify core ${tr}`);
  const refsFile = path.join(runDir, "discovery", "core_refs.json");
  const parsed = existsSync(refsFile) ? RefCoreSchema.safeParse(JSON.parse(await readFile(refsFile, "utf8"))) : null;
  const refs: RefCore | null = parsed?.success ? parsed.data : null;
  const envs = JSON.parse(await readFile(envsFile, "utf8")) as EnvsJson;
  return { units, refs, statements: transcribed.statements, envs };
}

/** `rederiveRepairs` on the run's passage sources (`repairSources`). Pure. */
export function rederiveOn(file: PatchFile, src: PassageSources): ReturnType<typeof rederiveRepairs> {
  return rederiveRepairs(file, (n) => ({ units: src.units, passage: nodePassage(src, n) }), (n, ops) => supersededNodes(src, n, ops));
}

export { revisesProof };
