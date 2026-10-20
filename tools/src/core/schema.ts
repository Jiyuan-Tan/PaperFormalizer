// Typed schema for the "core" — the machine-checkable logical skeleton of a paper,
// as the V1 transcription produces it.
//
// Well-formedness beyond the shape is enforced by the structural gate (gate.ts), not
// by a separate schema. Every stage binds to this one file, so changing a producer
// never re-tests a consumer as long as the file still validates.
import { z } from "zod";

// `openendedquestion` is the first-class OPEN/CONSTRUCT-question kind: it poses a
// question + a HANDLE (technique + target object), and the SOLVER derives the
// construction and proves the property — the answer is NOT pre-committed (max
// solver freedom). `conjecture` is DEPRECATED (a conjecture pre-commits a
// candidate answer, which suppresses the solver); it is kept in the enum only so
// legacy/typed consumers do not break.
export const STATEMENT_KINDS = [
  "theorem",
  "lemma",
  "proposition",
  "openendedquestion",
  "conjecture",
] as const;

const idRe = (prefix: string) => new RegExp(`^${prefix}:[a-z0-9-]+$`);

/** What additionally holds of a symbol in some results (`verify/core_graph.ts` `applicableClauses`):
 * `results` are core statement ids; `text` does not name them (rendered with their printed names). */
export const ScopedClauseSchema = z.object({ results: z.array(z.string()), text: z.string() });

/** One typed symbol, defined once. `refs` lists OTHER symbols this symbol's
 * `def` references — the table is kept in defined-before-use order by them (`symbol_order.ts`;
 * G1 checks it), cycles aside: two symbols may be described through each other. `def` is what the symbol
 * means wherever it is used; `scoped` (V1.5's symbol referee) what holds of it in named results only. */
export const SymbolSchema = z.object({
  name: z.string(),
  type: z.string(),
  space: z.string().optional(),
  sig: z.string().optional(),
  def: z.string().optional(),
  role: z.string().optional(),
  ref: z.string().optional(), // e.g. a def id, for a class symbol
  refs: z.array(z.string()).optional(),
  scoped: z.array(ScopedClauseSchema).optional(),
});

export const StandardTagSchema = z.object({ name: z.string(), cite: z.string() });
export const NovelTagSchema = z.object({ flag: z.literal(true), justification: z.string() });
/** ORCHESTRATOR-ONLY sanction (a solver may NEVER emit this). Marks an
 * assumption as a MAINTAINED (disclosed, high-level) condition the note is stated CONDITIONAL on
 * and does NOT derive — the legitimate slot for "proved under condition A, where verifying A is
 * itself the open object" (cf. a DML nuisance-rate condition). Gated:
 * `open_object` is the OEQ it surfaces; `separate_object` justifies that A constrains a SEPARATE
 * object (a functional property / an estimator-/nuisance-side rate) and NOT the target estimand's
 * own asymptotics at the conclusion scale. A `maintained`-dependent headline is CONDITIONAL and
 * tier-capped one notch (never flagship). */
export const MaintainedTagSchema = z.object({
  flag: z.literal(true),
  reason: z.string(),
  open_object: z.string(),
  separate_object: z.string(),
  sanctioned_by: z.literal("orchestrator"),
});

/** VERIFY-MODE ONLY. A harmless regularity / measurability / finiteness condition the paper's
 * proof silently uses, surfaced by the V1.5 referee and applied by the verify runner. It is
 * disclosed in the correctness report, never counted as an error. */
export const BookkeepingTagSchema = z.object({
  flag: z.literal(true),
  // "V1.5": a referee bookkeeping condition or pinned reading; "V1-patch": a hypothesis node a
  // verify-mode repair wrote into a core; "owner": a reading the paper's owner pinned when
  // withdrawing a finding (`verify/owner_rulings.ts`).
  added_by: z.enum(["V1.5", "V1-patch", "owner"]),
  reason: z.string().min(1),
});

/** VERIFY-MODE ONLY. Where a node lives in the user's LaTeX source, in original file
 * coordinates (`file` relative to the run's `source/`, 1-based inclusive lines). Optional on
 * every node kind so research cores are unaffected; the V6 report keys its findings on it. */
export const TexLocatorSchema = z
  .object({
    file: z.string().min(1),
    from: z.number().int().nonnegative(),
    to: z.number().int().nonnegative(),
    env: z.string().min(1),
    label: z.string().nullable(),
  })
  .superRefine((loc, ctx) => {
    // `env: "prose"` marks setup the paper states in running text (no environment). The
    // builder writes `from`/`to` as 0 and the V1 runner fills in the real lines after the
    // transcription lint has located the verbatim slice; every other locator names lines.
    if (loc.env !== "prose" && (loc.from < 1 || loc.to < 1)) {
      ctx.addIssue({ code: z.ZodIssueCode.custom, message: "an environment locator needs 1-based `from`/`to` lines" });
    }
  });

/** An assumption is ONE pure condition. No derived consequences, no where-used
 * pointers (those are `used_by` edges), no disclaimers, no omnibus. */
export const AssumptionSchema = z
  .object({
    id: z.string().regex(idRe("ass")),
    kind: z.string().optional(), // free-form tag (open set); nothing consumes it mechanically
    condition: z.string(),
    // `.optional()`, NOT `.default([])` — the same load-bearing distinction as on
    // StatementSchema/DefinitionSchema below. `undefined` = NEVER DECLARED = "may use any
    // symbol" (conservative); `[]` = "declared, genuinely uses none" (exempt from symbol
    // invalidation). A default collapses them, which turns a solver that simply FORGOT the
    // field into a credible "uses nothing" — and because a statement's invalidation scope is
    // its own declaration UNION its closure's, one such assumption silently narrows every
    // statement depending on it. 994 of 996 real assumptions already declare (80 of them
    // legitimately `[]`), so this changes almost nothing on the existing corpus while making
    // the omission case fail safe.
    free_symbols: z.array(z.string()).optional(),
    constants: z.array(z.string()).optional(),
    standard: StandardTagSchema.optional(),
    novel: NovelTagSchema.optional(),
    maintained: MaintainedTagSchema.optional(),
    bookkeeping: BookkeepingTagSchema.optional(),
    used_by: z.array(z.string()).optional(),
    tex_locator: TexLocatorSchema.optional(),
  })
  // `bookkeeping` is admitted here only so a transcribed core parses. `runStructuralGate`
  // licenses it per call (`allowBookkeeping`, default false) and emits a G6 violation
  // otherwise — see gate.ts.
  .refine(
    (a) => (a.standard ? 1 : 0) + (a.novel ? 1 : 0) + (a.maintained ? 1 : 0) + (a.bookkeeping ? 1 : 0) === 1,
    { message: "assumption must carry exactly one of {standard, novel, maintained, bookkeeping} (G6)" },
  );

/** A definition is EITHER a class (carved by member-properties) OR a
 * proof-internal construction (inputs + construction) — never both. A class is
 * never carved by a witness; class membership of a construction is always a
 * `statement`, never an assumption. (This is what makes A6 unrepresentable.) */
export const DefinitionSchema = z
  .object({
    id: z.string().regex(idRe("def")),
    name: z.string(),
    // REQUIRED on EVERY definition — the explicit defining expression, so the
    // notation is never opaque (e.g. `P_{κ,β,n}`):
    //   • CLASS → a set-builder `{x : φ(x)}` that spells out ALL index parameters
    //     (notably the triangular-array `n`); φ is a predicate over the
    //     member-property assumptions, NEVER the image of a witness construction.
    //   • CONSTRUCTED OBJECT → the explicit formula / algorithm.
    construction: z.string().min(1),
    // The symbol-table names this definition's `construction` uses. Same contract as
    // `AssumptionSchema.free_symbols` (atomic `symbols[].name` keys, one per element):
    // `.optional()`, NOT `.default([])`, and the difference is load-bearing:
    // `undefined` means NEVER DECLARED and is read as "may use ANY symbol", while `[]`
    // means "declared, and genuinely uses none". Defaulting would collapse those two,
    // and since ZERO of the 1269 definitions in the 112 real cores
    // carry the key, every legacy definition would parse as
    // a credible "uses no symbols" and a symbol re-definition would invalidate nothing —
    // silently unsound. Follows the `external_refs` precedent below for the same reason.
    // Consumed by `verify/core_graph.ts` to SCOPE a node's symbols.
    free_symbols: z.array(z.string()).optional(),
    // Present ⟺ this definition is a CLASS, carved by these member-property ids.
    // This is the A6 firewall anchor: a class is carved ONLY by member-properties;
    // the gate (G5) additionally checks neither the member-property list NOR the
    // set-builder `construction` references a witness construction.
    by_member_properties: z.array(z.string()).optional(),
    // Constructed-object metadata: the free inputs the construction consumes.
    inputs: z.array(z.string()).optional(),
    tex_locator: TexLocatorSchema.optional(),
  })
  .refine((d) => !(d.by_member_properties !== undefined && d.inputs !== undefined), {
    message:
      "a class (by_member_properties) declares no construction `inputs`; a constructed object declares no `by_member_properties` (G5/G7)",
  });

/** The external source a `cited` statement is borrowed from: a `cite` bibkey
 * (must resolve in the core `bibliography`) and the exact `locator` (e.g.
 * "Theorem 3.1"). This is the structured provenance that lets F1 mint a `cite:`
 * node and the F2.5 match check verify the Lean def against the real statement —
 * instead of the result being laundered as `status:"proved"` with the citation
 * buried in `proof_tex`. */
export const CitedSourceSchema = z.object({
  cite: z.string(), // bibkey into `bibliography`
  locator: z.string(), // e.g. "Theorem 3.1", "Lemma 4.2", "§5.2"
  // Frozen semantic carrier classification. Logical/mathematical claims are the default
  // and become threaded Prop assumptions in F1. Only genuinely bibliographic
  // scope/provenance/delivery records may select the non-logical metadata carrier.
  // Keeping this in the typed core (not mutable plan prose) prevents F1/F4 from
  // self-attesting a quantitative claim into the metadata exemption.
  carrier: z.enum(["logical-claim", "bibliographic-metadata"]).optional(), // absent legacy value = logical-claim
  // Exact source-of-record when the source can be transcribed lawfully. This is
  // preferred over agent recollection and is copied unchanged into F1's cite:
  // entry. Legacy cores may still carry the transcription in `proof_tex`; F1
  // (`formalization/stage1.ts`) reads that as the fallback.
  verbatim_statement: z.string().min(1).optional(),
  // Stable source handles. arXiv is directly fetchable by the shared resolver;
  // DOI/URL may still require main/user attestation when access is unavailable.
  arxiv: z.string().min(1).optional(),
  doi: z.string().min(1).optional(),
  url: z.string().url().optional(),
  // The PRIMARY source, when the located environment restates a result it credits to
  // an earlier work (papers routinely reprove standard lemmas in their appendices).
  // Absent = the statement was affirmed original to `cite`. A verbatim match does not
  // establish provenance, so this is decided explicitly at attestation time.
  upstream: z.object({
    citation: z.string().min(1),
    locator: z.string().min(1).optional(),
    cite: z.string().min(1).optional(), // bibkey, when the primary is in `bibliography`
  }).optional(),
  attestation: z.object({
    by: z.enum(["d0-agent", "main", "user"]),
    note: z.string().min(1),
    at: z.string().datetime().optional(),
  }).optional(),
});

export const StatementSchema = z
  .object({
    // `oeq:` is the open/construct-question id (the kind the author actually emits);
    // `conj:` is retained as DEPRECATED so any pre-existing conjecture node still
    // validates (see STATEMENT_KINDS).
    id: z.string().regex(/^(thm|lem|prop|oeq|conj):[a-z0-9-]+$/),
    kind: z.enum(STATEMENT_KINDS),
    statement: z.string(),
    // The symbol-table names this statement's `statement` text uses — the DECLARED
    // edge from a claim to the symbols whose meaning it rests on. Symbols are not
    // `depends_on` nodes, so without this a symbol re-definition (say `\bar d` narrowing
    // from ℝ to [0,1]) changed what this node CLAIMS while its text stayed byte-identical
    // and every carried proof survived.
    //
    // `.optional()`, NOT `.default([])`. `undefined` = NEVER DECLARED, read as "may use ANY symbol" ⇒
    // invalidated by ANY symbol change; `[]` = declared, genuinely uses none. Zero of
    // the 1077 statements in the 112 real cores carry
    // the key, so a `.default([])` would make every legacy statement look like a
    // credible "uses no symbols" and scope the invalidation to nothing — strictly worse
    // than the global invalidation it replaces. Same reasoning as `external_refs` below.
    // Consumed by `verify/core_graph.ts`.
    free_symbols: z.array(z.string()).optional(),
    depends_on: z.array(z.string()).default([]),
    route: z.string().optional(), // proof strategy
    // JSON-producing agents commonly spell an inapplicable optional field as
    // `null`.  For cited leaves the citation is the justification, so normalize
    // that representation to the canonical absence used by the rest of the
    // pipeline.  Non-null, non-string values remain validation errors.
    proof_tex: z.preprocess((value) => value === null ? undefined : value, z.string().optional()),
    // `cited` = a result the note INVOKES rather than DERIVES (a published theorem
    // we use for completeness). Its justification IS the citation, so it is NOT
    // `proved` by us — marking such a result `proved` (with the citation as its
    // proof_tex) is laundering. A `cited` statement MUST carry `source` and is a
    // LEAF: it may reference `def:`/`ass:` for notation but must not `depends_on`
    // other `lem:`/`thm:`/`prop:` (cite the theorem, never reconstruct its proof —
    // G-cited). `source.carrier` fixes whether F1 maps it to a logical Prop assumption
    // or a closed bibliographic metadata def; the plan may not reclassify it. A later supported
    // discharge keeps this discovery provenance while mapping the node to an exact
    // proved lemma/theorem and removing it from consumer hypotheses. A delivered
    // headline or headline-support result may not remain conditional on cited debt;
    // only a secondary cited node outside that reverse closure may stay gated.
    status: z.enum(["to-prove", "proved", "cited"]),
    source: CitedSourceSchema.optional(), // REQUIRED ⟺ status === "cited"
    // Results in OTHER papers that this node NAMES but does not depend
    // on — the declared channel for provenance. The D0.5 rubric asks each theorem to
    // position itself against prior in-repository work; a node answers that by
    // RE-PROVING the generic step in this core and crediting the source. That is the
    // opposite of laundering (nothing is borrowed), but the credit line reads as a
    // citation to a regex, so declaring it here makes the distinction data instead of
    // something a prose scan has to infer. Format `<qid>/<node-id>`. This is NOT
    // `source` — `source` is a published paper a `cited` LEAF invokes in place of a
    // proof; `external_refs` is a sibling run's node mentioned by a node we PROVE.
    // Optional, NOT `.default([])`: defaulting would make the key required on every
    // node type and stamp an empty array onto every node of every existing core.
    external_refs: z.array(z.string().regex(/^[a-z0-9_]+\/(thm|lem|prop|oeq|conj|def|ass):[a-z0-9-]+$/)).optional(),
    // Prose fields (motivation only — never load-bearing math; the formal claim is
    // `statement`).
    justification: z.string().optional(), // one-line: why this claim / why it matters
    gap: z.string().optional(), // closest prior art (bibkeys) + why this differs
    consumer: z.string().optional(), // one concrete downstream consumer
    tex_locator: TexLocatorSchema.optional(),
    // VERIFY-MODE ONLY. A corollary a repair SPLIT OFF this statement (`verify/core_graph.ts`
    // `splitCorollaryId`): a result of its own that the paper does not print — no `tex_locator`; it
    // is shown, and located, at the environment of the statement named here.
    split_from: z.string().optional(),
    // VERIFY-MODE ONLY. A cited leaf made from a PROOF (`verify/ref_core.ts` `proof_citations`): the
    // published result the proof of the statement named here invokes by citation. Its `statement`
    // is the passage of that proof, verbatim (the citation and the step it gives), its `tex_locator`
    // that proof's; the named statement depends on it.
    cited_in: z.string().optional(),
    // VERIFY-MODE ONLY. An UMBRELLA (`verify/core_graph.ts` `UMBRELLA_STATEMENT`): a printed result
    // every conclusion of which a repair moved to a block (`split_from` = this id). It states that
    // its blocks hold, depends on them, and has NO Lean declaration of its own — it is established
    // exactly when all its blocks are.
    umbrella: z.boolean().optional(),
    obligation: z.object({
      what_is_open: z.string(),
      obstruction: z.string(),
      attempted: z.string(),
      partial_result: z.string().optional(),
    }).optional(),
  })
  .refine((s) => (s.status === "cited") === (s.source !== undefined), {
    message: "a `cited` statement must carry `source` (bibkey + locator), and only a cited statement may (G-cited)",
  })
  .refine(
    // A `proved` statement with no proof is a hollow result: it renders as established
    // with nothing behind it and passes discharge checks that only read `status`.
    // Verified against all 93 real
    // cores before enforcing: zero violations.
    (s) => s.status !== "proved" || (s.proof_tex ?? "").trim().length > 0,
    {
      message:
        "a `proved` statement must carry a non-empty proof_tex — a proved node with no proof " +
        "renders as an established result with nothing establishing it (use `to-prove`, or " +
        "`cited` with a `source` if the justification is a citation)",
    },
  )
  .refine(
    // `oeq:`/`conj:` belong here too: a cited result resting on an OPEN question is
    // strictly worse than one resting on a proved lemma, yet the original pattern
    // omitted them, so `cited` + `depends_on:["oeq:open"]` validated and the node
    // counted as settled while its support was unresolved.
    (s) => s.status !== "cited" || !s.depends_on.some((d) => /^(lem|thm|prop|oeq|conj):/.test(d)),
    {
      message:
        "a `cited` statement is a LEAF: cite the theorem, do not reconstruct its proof — it must not depends_on other lem:/thm:/prop:/oeq:/conj: nodes (G-cited-leaf)",
    },
  )
  .refine(
    // The id PREFIX and the `kind` were validated independently, so `{id:"thm:headline",
    // kind:"lemma"}` was accepted. That is not cosmetic: reachability keys on `kind`, not
    // on the prefix. Non-lemma nodes are roots and unreachable
    // `kind:"lemma"` nodes are PRUNED, so a headline mislabelled
    // as a lemma is silently deleted from the core.
    //
    // Deliberately NARROW rather than a prefix↔kind bijection. A bijection would outlaw a
    // legitimate pattern: `thm:` with kind `conjecture`, a conjectured headline posed at
    // D-1. (An earlier version of this comment also cited `thm:` with kind `remark`; that
    // was wrong — `remark` is not in STATEMENT_KINDS at all and belongs to the
    // presentation schema, so such a node never reaches this refinement.)
    // Only ONE direction is destructive: a headline-shaped id carrying kind `lemma` is
    // not a root, so once it is unreferenced the orphan pruner DELETES it outright. Every
    // other mismatch merely mis-roots a node, which is recoverable.
    // `conj:` is included: the exemption below is about a conjecture being PROMOTED to
    // theorem/proposition once proved, which is legitimate. Carrying kind `lemma` is not
    // that — the orphan pruner keys on `kind` and would delete a conj: headline exactly as
    // it would a thm: one.
    (s) => !/^(thm|prop|oeq|conj):/.test(s.id) || s.kind !== "lemma",
    {
      message:
        "a thm:/prop:/oeq:/conj: node must not have kind `lemma` — orphan-pruning keys on `kind` and " +
        "DELETES unreferenced lemmas, so a headline mislabelled this way is " +
        "silently removed from the core. Give it its real kind, or use a lem: id.",
    },
  );

export const BibEntrySchema = z.object({ key: z.string(), citation: z.string().optional() });

/** SC6's auditable mapping from published comparator claims to proposal nodes.
 * Both top-level spellings remain supported because early proto producers used
 * `comparator_promises`; new prompts emit `comparator_promise_table`. */
export const ComparatorPromiseSchema = z.object({
  comparator_bibkey: z.string().min(1),
  comparator_claim: z.string().min(1),
  matched_by: z.string().min(1),
  match_kind: z.enum([
    "strict_tightening",
    "iff_frontier",
    "equivalence",
    "non_representability",
    "downgraded_to_informed_by",
    "dropped_from_abstract",
  ]),
});

/** The project-level justification (replaces a free-prose intro): the literature
 * GAP, the NICHE that gap opens, and how this project FILLS it. */
export const ProjectJustificationSchema = z.object({
  gap: z.string(), // what the literature is missing
  niche: z.string(), // the specific opportunity that gap opens
  fill: z.string(), // how this project fills the niche
});

export const CoreSchema = z.object({
  qid: z.string(),
  /** Legacy topical tag; carried through, never used to gate behaviour. */
  cluster: z.string().optional(),
  // The G1 order rule (gate.ts) and semantic-basis traversal both key
  // declarations by name; a duplicate has no well-defined position or meaning.
  symbols: z.array(SymbolSchema).refine(
    (symbols) => new Set(symbols.map((s) => s.name)).size === symbols.length,
    (symbols) => {
      const seen = new Set<string>();
      const dupes = new Set<string>();
      for (const s of symbols) {
        if (seen.has(s.name)) dupes.add(s.name);
        else seen.add(s.name);
      }
      return { message: `duplicate symbol name(s): ${[...dupes].join(", ")} — symbol ordering and semantic traversal require one declaration per name` };
    },
  ),
  assumptions: z.array(AssumptionSchema),
  definitions: z.array(DefinitionSchema).default([]),
  statements: z.array(StatementSchema),
  sampling_model: z.record(z.any()).optional(),
  // The §7 identifying functional, first-class and parallel to the §8
  // target_estimand: ExactID identifying formula, PartialID bounding functional,
  // Panel regression formula, (Stat) the estimator+rate pair, or — for a
  // structure-identification proposal — the recovery map (the functional of P
  // returning the structural target). Added by the non-Stat sanity-check — in
  // the Stat-only schema it had been absorbed into a `def:estimator`
  // construction, which is awkward for an ID/bound formula.
  estimand_functional: z.string().optional(),
  // The §8 causal target. Usually an effect estimand; for a structure-
  // identification proposal it is instead the structural / mechanism parameter
  // to be recovered (DAG / edge set / coefficient matrix), stated with the
  // indeterminacy under which it is identified (exact, sign·permutation, MEC).
  target_estimand: z.string(),
  bibliography: z.array(BibEntrySchema).default([]),
  comparator_promise_table: z.array(ComparatorPromiseSchema).optional(),
  comparator_promises: z.array(ComparatorPromiseSchema).optional(),
  // Top-level prose (motivation/narrative).
  tldr: z.string().optional(), // a one-paragraph summary of the whole proposal
  project_justification: ProjectJustificationSchema.optional(), // gap → niche → fill
  related_work: z.string().optional(),
  interpretation: z.string().optional(),
  // Optional non-contribution diagnostic retained from the accepted proposal.
  // This is deliberately prose, not a StatementSchema node: it may document an
  // internal limitation/counterexample without promoting it to a numbered
  // theorem, novelty claim, or closed open question.
  technical_internal_limitation: z.string().optional(),
  honest_scope: z.string().optional(),
})
  // Statement ids must be UNIQUE. Every consumer collapses them through a Map or Set
  // keyed by id (the structural gate, the apply's `stmtById`/`originalStatements`), so a
  // duplicate silently resolves to ONE record — usually the last — while a sibling code
  // path may edit the other. Two same-id records with different claims therefore let a
  // bundle mutate one copy and render the other, with no error anywhere.
  .refine(
    (c) => new Set(c.statements.map((s) => s.id)).size === c.statements.length,
    (c) => {
      // NB: `!seen.add(id)` is always false — Set.add returns the Set — which is exactly
      // the always-false-predicate class this audit was hunting. Use an explicit has/add.
      const seen = new Set<string>();
      const dupes = new Set<string>();
      for (const s of c.statements) {
        if (seen.has(s.id)) dupes.add(s.id);
        else seen.add(s.id);
      }
      return { message: `duplicate statement id(s): ${[...dupes].join(", ")} — every consumer keys nodes by id, so a duplicate silently resolves to one record` };
    },
  );

export type CoreSymbol = z.infer<typeof SymbolSchema>;
export type ScopedClause = z.infer<typeof ScopedClauseSchema>;
export type CoreAssumption = z.infer<typeof AssumptionSchema>;
export type CoreStatement = z.infer<typeof StatementSchema>;
export type Core = z.infer<typeof CoreSchema>;

/** The set of all addressable core node ids (assumptions ∪ definitions ∪ statements).
 * Shared by `core/dag.ts`, the F1.5 plan gate and the F2 tag reconciliation. */
export function coreNodeIds(core: Core): Set<string> {
  return new Set<string>([
    ...core.assumptions.map((a) => a.id),
    ...core.definitions.map((d) => d.id),
    ...core.statements.map((s) => s.id),
  ]);
}
