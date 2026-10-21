/**
 * V1.5 referee reply contracts (`referee_shards.ts`, `referee_symbols.ts`): the strict JSON Schemas
 * handed to `codex exec --output-schema`, the zod re-checks, and the prose description of the
 * per-node fields. Kept in one place so a node field is edited once for every call that emits it.
 */
import { z } from "zod";
import { DRIFT_FIX_JSON_SCHEMA, DriftFixSchema } from "./directive_edits.js";
import { CLARITY_RULE, EXPLANATION_CLARITY_JSON, ExplanationClaritySchema, READING_BASIS_RULE, READING_RESULT_NAME_RULE, TEX_MATH_RULE, TEX_STRING_NONEMPTY, TEX_STRING_OR_NULL } from "./owner_text.js";

/** Strict JSON Schema for ONE node verdict (every property required, nullable optionals). */
export const V15_NODE_REPLY: Record<string, unknown> = {
  type: "object",
  additionalProperties: false,
  required: [
    "id",
    "faithfulness",
    "ambiguity",
    "correctness",
    "detail",
    "witness",
    "fix",
    "bookkeeping_assumption",
    "reading",
    "minimality",
    "weakens_contribution",
    "follows_repair",
    "bookkeeping_dropped",
    "explanation_clarity",
    "split",
    "witness_regime",
    "witness_instance",
  ],
  properties: {
    id: { type: "string" },
    faithfulness: { type: "string", enum: ["ok", "drift"] },
    ambiguity: { type: "string", enum: ["ok", "pinned", "unresolvable"] },
    correctness: { type: "string", enum: ["ok", "bookkeeping", "unclear", "error"] },
    detail: { type: "string" },
    witness: { type: ["string", "null"] },
    minimality: { type: "boolean" },
    weakens_contribution: { type: "boolean" },
    follows_repair: { type: "boolean" },
    bookkeeping_dropped: { type: "boolean" },
    explanation_clarity: EXPLANATION_CLARITY_JSON,
    split: { anyOf: [{ type: "object", additionalProperties: false, required: ["why"], properties: { why: { type: "string" } } }, { type: "null" }] },
    witness_regime: { type: ["string", "null"], enum: ["in_scope", "degenerate", null] },
    witness_instance: { type: ["string", "null"] },
    fix: DRIFT_FIX_JSON_SCHEMA,
    bookkeeping_assumption: {
      anyOf: [
        {
          type: "object",
          additionalProperties: false,
          required: ["condition", "reason"],
          properties: { condition: TEX_STRING_NONEMPTY, reason: { type: "string" } },
        },
        { type: "null" },
      ],
    },
    reading: {
      anyOf: [
        {
          type: "object",
          additionalProperties: false,
          required: ["reading", "evidence", "of"],
          properties: { reading: TEX_STRING_NONEMPTY, evidence: { type: "string" }, of: { anyOf: [{ type: "string" }, { type: "null" }] } },
        },
        { type: "null" },
      ],
    },
  },
};

export const PATCH_REVIEW_REPLY: Record<string, unknown> = {
  anyOf: [
    {
      type: "object",
      additionalProperties: false,
      required: ["key_results_ok", "detail"],
      properties: { key_results_ok: { type: "boolean" }, detail: { type: "string" } },
    },
    { type: "null" },
  ],
};

export const REJECTION_VERDICTS_REPLY: Record<string, unknown> = {
  anyOf: [
    {
      type: "array",
      items: {
        type: "object",
        additionalProperties: false,
        required: ["node", "upheld", "detail"],
        properties: { node: { type: "string" }, upheld: { type: "boolean" }, detail: { type: "string" } },
      },
    },
    { type: "null" },
  ],
};

export const NodeVerdictSchema = z.object({
  id: z.string().min(1),
  faithfulness: z.enum(["ok", "drift"]),
  ambiguity: z.enum(["ok", "pinned", "unresolvable"]),
  correctness: z.enum(["ok", "bookkeeping", "unclear", "error"]),
  detail: z.string(),
  witness: z.string().nullable(),
  fix: DriftFixSchema.nullable().optional(),
  bookkeeping_assumption: z
    .object({ condition: z.string().min(1), reason: z.string().min(1) })
    .nullable(),
  reading: z.object({ reading: z.string().min(1), evidence: z.string().min(1), of: z.string().nullable().optional() }).nullable(),
  minimality: z.boolean().optional(),
  weakens_contribution: z.boolean().optional(),
  follows_repair: z.boolean().optional(),
  bookkeeping_dropped: z.boolean().optional(),
  explanation_clarity: ExplanationClaritySchema.nullable().optional(),
  split: z.object({ why: z.string() }).nullable().optional(),
  witness_regime: z.enum(["in_scope", "degenerate"]).nullable().optional(),
  witness_instance: z.string().nullable().optional(),
});

export const PatchReviewSchema = z.object({ key_results_ok: z.boolean(), detail: z.string() });
export const RejectionVerdictsSchema = z.array(z.object({ node: z.string(), upheld: z.boolean(), detail: z.string() }));

/** The per-node fields in prose — the `nodes` entry of every referee reply that grades nodes. */
export const NODE_FIELDS_TEXT = `      id                      the core node id, exactly as it appears in the core.
      faithfulness            "ok" or "drift".
      ambiguity               "ok", "pinned" or "unresolvable".
      reading                 REQUIRED (non-null) when ambiguity is "pinned": {reading,
                              evidence} — the single reading the paper determines, as a
                              condition in the paper's TeX (mathematics inside $…$), and where the paper fixes
                              it (a result named as below). ${READING_BASIS_RULE} Its \`of\`: the
                              id of the assumption or definition whose phrase
                              the reading settles when that is not this node (the
                              reading then binds every result using it), else null.
                              null otherwise.
      correctness             "ok", "bookkeeping", "unclear" or "error".
      detail                  what you found, in one short paragraph (several defects:
                              one short item each, (a), (b), …). For \`drift\` give
                              both meanings; for a \`pinned\` or \`unresolvable\` ambiguity both readings; for
                              \`unclear\` the step you could not close. Say wiring in
                              words ("the core wires it to …", "uses"), never a field
                              name such as depends_on: the paragraph is TeX.
      witness                 REQUIRED and non-empty when correctness is "error": the
                              false step and why it is false, or an explicit
                              counterexample; for several defects, one per item of
                              \`detail\`. null otherwise.
      explanation_clarity     REQUIRED when you confirm a repair (a patched node graded
                              "ok" or "bookkeeping") whose patch carries the fixer's note
                              (owner_explanation, shown as the author reads it): {grade,
                              reason} — grade "ok" or "unclear" by the rule: ${CLARITY_RULE};
                              reason: one line saying why (for "unclear", what the author
                              cannot follow). null otherwise.
      split                   {why} ONLY on a repaired result you confirm ("ok" or
                              "bookkeeping") whose corrected statement should be split (the
                              PATCHES rule, FORM OF A REPAIR): why, in one line naming the
                              general claim and the cases — or that it should be an
                              umbrella, or (on an umbrella) the main claim to restore
                              as its statement. null otherwise — always null on
                              a statement the paper prints.
      witness_regime          REQUIRED when correctness is "error" (not a minimality or
                              weakening grade): "in_scope" or "degenerate", as the brief
                              defines them; a "degenerate" witness also gives the exclusion
                              in \`bookkeeping_assumption\`. With several defects,
                              "degenerate" only when every one is; else "in_scope", the
                              degenerate item noted in \`detail\`. null otherwise.
      witness_instance        REQUIRED with witness_regime: the model / instance the
                              witness lives in, in one line. null otherwise.
      minimality              true EXACTLY when this node is a patch part graded "error"
                              only because it is correct but not minimal (the witness then
                              names the smaller sufficient change: a weaker replacement, or a
                              passage to keep as printed or move into a detail); false
                              otherwise.
      weakens_contribution    true EXACTLY when this node is a patched node graded "error" because the repair, though it
                              holds, weakens what the paper claims (the PATCHES rule).
                              false otherwise.
      follows_repair          true EXACTLY when this node is graded "error" only because a
                              result it uses was repaired (DEPENDENCY VERDICTS: "confirmed
                              repair") and now states less: the step holds with the printed
                              version of that result. false otherwise.
      bookkeeping_dropped     true EXACTLY when CONDITIONS APPENDED EARLIER lists a condition of the node that it
                              no longer needs (say why in the detail); false otherwise. A
                              condition neither restated nor dropped is kept.
      fix                     for "drift" ONLY: when the correction is a MECHANICAL edit of
                              the core's structure, state it as data and the runner applies it
                              without an agent round. Fields (all optional; null otherwise):
                              add_depends_on / remove_depends_on — on a statement: node ids it
                              must (not) depend on; wire_into / unwire_from — on an assumption
                              or definition: the statements that must (not) use it; extend_to —
                              for an assumption or definition
                              whose slice ends too early, the verbatim phrase (in the paper's
                              TeX) the slice must end with; new_assumption — {id "ass:<slug>",
                              env (id, or null for running text), from, to (verbatim anchors of
                              the sentence stating the premise), wire_into [statement ids].
                              Anchors are copied from the source exactly as printed. Leave null
                              when the fix needs judgement the runner cannot make.
      bookkeeping_assumption  REQUIRED when correctness is "bookkeeping", and with a
                              "degenerate" witness_regime (the exclusion):
                              {"condition": "<the single condition, in the paper's
                              TeX, mathematics inside $…$>", "reason": "<the step that silently uses it>"}.
                              null otherwise.
      ${TEX_MATH_RULE}`;

/** A node verdict of a shard call, and its field list: the node fields. */
export const SHARD_NODE_REPLY: Record<string, unknown> = V15_NODE_REPLY;

export const SHARD_NODE_FIELDS_TEXT = NODE_FIELDS_TEXT;

// ---------------------------------------------------------------------------------------------
// The symbol referee (`referee_symbols.ts`): one verdict per symbol of the table
// ---------------------------------------------------------------------------------------------

/** Strict JSON Schema for ONE symbol verdict. */
export const V15_SYMBOL_REPLY: Record<string, unknown> = {
  type: "object",
  additionalProperties: false,
  required: ["name", "keep", "meaning", "fix", "ambiguity", "reading", "redefined_at", "detail"],
  properties: {
    name: { type: "string" },
    keep: { type: "boolean" },
    meaning: { type: "string", enum: ["ok", "drift"] },
    fix: {
      anyOf: [
        {
          type: "object",
          additionalProperties: false,
          required: ["type", "space", "def"],
          properties: { type: TEX_STRING_OR_NULL, space: TEX_STRING_OR_NULL, def: TEX_STRING_OR_NULL },
        },
        { type: "null" },
      ],
    },
    ambiguity: { type: "string", enum: ["ok", "pinned", "unresolvable"] },
    reading: {
      anyOf: [
        {
          type: "object",
          additionalProperties: false,
          required: ["reading", "evidence", "scoped"],
          properties: {
            reading: { ...TEX_STRING_OR_NULL, pattern: TEX_STRING_NONEMPTY.pattern },
            evidence: { type: "string" },
            scoped: {
              type: "array",
              items: {
                type: "object",
                additionalProperties: false,
                required: ["results", "text", "drop"],
                properties: { results: { type: "array", items: { type: "string" } }, text: TEX_STRING_OR_NULL, drop: { type: ["string", "null"] } },
              },
            },
          },
        },
        { type: "null" },
      ],
    },
    redefined_at: { type: ["string", "null"] },
    detail: { type: "string" },
  },
};

export const SymbolVerdictSchema = z.object({
  name: z.string().min(1),
  meaning: z.enum(["ok", "drift"]),
  fix: z.object({ type: z.string().nullable(), space: z.string().nullable().optional(), def: z.string().nullable() }).nullable(),
  ambiguity: z.enum(["ok", "pinned", "unresolvable"]),
  // A null text is a piece KEPT from the grade on file (`referee_symbols.ts` `kept`); `scoped`
  // absent = none (a reply in the shape before the split).
  reading: z
    .object({
      reading: z.string().min(1).nullable(),
      evidence: z.string().min(1),
      scoped: z.array(z.object({ results: z.array(z.string()), text: z.string().nullable(), drop: z.string().nullable().optional() })).optional(),
    })
    .nullable(),
  redefined_at: z.string().nullable(),
  detail: z.string(),
  /** The grade ON FILE still holds: the runner keeps its texts word for word (`referee_symbols.ts`). */
  keep: z.boolean().optional(),
});

/** The per-symbol fields in prose — the `symbols` entry of every symbol-referee reply. */
export const SYMBOL_FIELDS_TEXT = `      name          the symbol's name, exactly as it appears in the symbol table.
      keep          true when the symbol has a grade ON FILE (shown) that still holds for the
                    texts shown: the runner keeps its meaning, fix, ambiguity, reading,
                    redefined_at and detail word for word, and reads nothing else of your
                    entry. false otherwise, then grade it afresh.
      meaning       "ok" or "drift".
      fix           REQUIRED (non-null) when meaning is "drift": {type, space, def} — the corrected
                    type, space and/or definition in the paper's notation, copied from the paper where
                    it defines the symbol; null for a field that is already right. The runner
                    writes it into the symbol table. null otherwise. A fix is general: it
                    holds wherever the symbol is used. With a grade ON FILE and keep false,
                    meaning and fix are graded afresh: restate a fix on file that still
                    applies (null drops it).
      ambiguity     "ok", "pinned" or "unresolvable".
      reading       REQUIRED (non-null) when ambiguity is "pinned": {reading, evidence, scoped},
                    null otherwise.
                    reading: the GENERAL part — the symbol's settled meaning wherever it is
                    used, as ONE statement in the paper's notation that a formalizer can
                    adopt (random or fixed; conditional on what; domain or support; index
                    range; population or sample quantity). It names no particular result.
                    scoped: [{results, text, drop}] — one clause per qualification that holds
                    only in some results: results are their ids (copied from THE TEXT EACH
                    READING DESCRIBES; only results listed there for this symbol), text what
                    additionally holds of the symbol there — which meaning it takes, a
                    restriction a result needs — in its statement or its proof. The text does
                    not name its results (the runner prints "In <their names>:" before it).
                    drop is null. [] when nothing is specific to a result.
                    evidence: where the paper fixes all of it.
                    With a grade ON FILE and keep false, write only the part a changed text
                    makes wrong: reading: null keeps the general part on file, and every
                    clause on file STAYS as it is unless you list it, by exactly its results —
                    with a text (it replaces the clause), or with text null and drop: "<why
                    it no longer holds>" (it removes the clause). A clause you do not list is
                    never removed; one that should now hold in other results is dropped and
                    written again with those results.
                    ${READING_RESULT_NAME_RULE}
                    ${READING_BASIS_RULE}
      redefined_at  the sentence, verbatim, where the paper later gives the symbol another
                    meaning; ambiguity is then "pinned" (the reading says which meaning holds
                    where) or "unresolvable". null otherwise.
      detail        what you found, in one short paragraph: for "drift" the recorded and the
                    paper's meaning; for "pinned" / "unresolvable" the readings in question.`;
