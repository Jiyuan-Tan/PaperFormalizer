/**
 * `theoremchecker verify` — shared contracts.
 *
 * Verify mode takes a user's LaTeX paper and produces (1) a typed core (V1), (2) a
 * faithfulness / ambiguity / correctness review of that core (V1.5), (3) the unchanged
 * F1–F5 formalization, and (4) a per-result correctness report (V6). This file pins
 * every interface the V stages share so the stages can be built independently.
 *
 * Nothing here is an LLM contract; the V1 / V1.5 agent reply schemas live next to the
 * stage that owns them (`stage_v1.ts`, `stage_v1_5.ts`).
 */
import type { runCodex } from "../shared/codex.js";
import type { ScopedClause } from "../core/schema.js";
import type { StateJson } from "../types.js";
import type { ExplanationClarity, OwnerExplanationField } from "./owner_text.js";

/** Lifecycle cursor of a verify run, stored at `state.verify.phase`: which RUNNER owns the
 * next step. The linear stage cursor is `state.stage_completed` (`STAGE_ORDER`). */
export type VerifyPhase =
  | "init" // run dir + source prepared, V1 not yet run
  | "v1" // core.json written, structural gate passed, awaiting V1.5
  | "v1_5" // V1.5 PASS applied; `state.stage_completed === "V1.5"`, F1 may enter
  | "formalization" // handed to runPipeline (F1–F5); resumes go there until stage "5"
  | "proposals_A" // F1 planned: toolkit promotion round A on the paper's cited results (stops for the owner's decisions), then F1.5
  | "v6" // F5 done (or V1.5 FAIL): report pending
  | "proposals_B" // report written after a full F run: the toolkit promotion round (stops for the owner's decisions)
  | "done" // report written
  | "failed"; // V1.5 FAIL — report written with the refutation, no F stages run

/** Where a paper object lives in the user's source, in ORIGINAL file coordinates
 * (never the flattened file). `env` is the environment name as written. */
export interface TexLocator {
  file: string; // relative to `<runDir>/source/`
  from: number; // 1-based, inclusive
  to: number; // 1-based, inclusive
  env: string;
  label: string | null;
}

export type EnvKind =
  | "theorem"
  | "lemma"
  | "proposition"
  | "corollary"
  | "definition"
  | "assumption"
  | "remark"
  | "example"
  | "other";

/** Kinds the core builder must map to statement / assumption / definition nodes.
 * `remark` / `example` / `other` are context only. */
export const CORE_BEARING_KINDS: ReadonlySet<EnvKind> = new Set<EnvKind>([
  "theorem",
  "lemma",
  "proposition",
  "corollary",
  "definition",
  "assumption",
]);

/** One theorem-like environment as found by the mechanical parser (V1 step 1). */
export interface TexEnv {
  /** Stable handle: the `\label` when present, else `<kind>-<ordinal>` (1-based, per kind,
   * document order), e.g. `"thm:main"` or `"lemma-3"`. Unique within `envs`. */
  id: string;
  kind: EnvKind;
  /** Environment name as written in the source, e.g. `"thm"`. */
  envName: string;
  label: string | null;
  /** The optional `[...]` title argument, raw TeX, or null. */
  title: string | null;
  /** Raw TeX between `\begin{..}` and `\end{..}`, comments stripped, trimmed. */
  body: string;
  /** Raw TeX of the matched `proof` environment body, or null when the paper gives none.
   * Matching rule: the next `proof` env that directly follows this env (only whitespace /
   * comments between), else any `proof` whose `[...]` title `\ref`s this env's label. */
  proof: string | null;
  /** Locator of the proof env, when `proof` is non-null. */
  proofLines: TexLocator | null;
  lines: TexLocator;
  /** Labels referenced (`\ref`, `\cref`, `\Cref`, `\eqref`, `\autoref`, `\thmref`, …)
   * anywhere in `body` or `proof`, deduplicated, document order. */
  refs: string[];
}

export interface TexBibEntry {
  key: string;
  /** `\bibitem` body, or for a `.bib` entry `"<author> (<year>). <title>"` best-effort. */
  text: string;
}

/** `discovery/envs.json` — the V1 mechanical extraction. Pure function of the source. */
export interface EnvsJson {
  /** Main file, relative to `<runDir>/source/`. */
  main_file: string;
  /** Every file folded into the flattened text, main first, relative to `source/`. */
  files: string[];
  /** `\newtheorem` / `\declaretheorem` map: env name → kind (plus built-in defaults). */
  newtheorem: Record<string, EnvKind>;
  envs: TexEnv[];
  bibliography: TexBibEntry[];
  /** The authors' note macros the paper was read with (`note_macros.ts`): wrappers dropped, hidden text
   * and comments removed from `flat.tex`. Absent: the paper was read as written (a run from before the
   * reading existed, or one with it switched off) — every later read of the source follows it. */
  note_macros?: import("./note_macros.js").NoteMacroTable;
}

/** `discovery/flat.tex` companion: origin of every flattened line. `lineMap[i]` is the
 * source of flat line `i + 1`. Persisted as `discovery/flat.linemap.json`. */
export interface FlatTexLineMap {
  lineMap: Array<{ file: string; line: number }>;
}

/** Result of `prepareSource`: the user's input materialised under `<runDir>/source/`. */
export interface PreparedSource {
  /** Absolute path of `<runDir>/source/`. */
  sourceDir: string;
  /** Main `.tex`, relative to `sourceDir`. */
  mainFile: string;
  /** sha256 over the sorted (relpath, bytes) list of every file under `sourceDir`. */
  sha256: string;
  /** How the input was recognised: a bare `.tex`, a directory, or an archive kind. */
  inputKind: "tex" | "dir" | "zip" | "tar" | "tar.gz" | "gz";
  /** What was done that the input did not say (a bare `.tex` taken with its directory): logged once. */
  note?: string;
}

/** Materialise `input` (a `.tex` file, a directory, a `.zip`, `.tar`, `.tar.gz`/`.tgz`, or a
 * bare gzip as served by arXiv) under `sourceDir` and pick the main file. `mainHint` is the
 * user's `--main <relpath>` override. Must refuse any archive member escaping `sourceDir`. */
export type PrepareSource = (args: {
  input: string;
  sourceDir: string;
  mainHint?: string | null;
}) => Promise<PreparedSource>;

/** V1.5 may send the core back to V1 (a transcription REVISE round) for a drifting node at most this
 * many times: a drift found late on a node no round has touched gets its own rounds (a count per level
 * or per run stopped a paper on the first drift found after earlier ones were fixed). Drift repeated on
 * a node after a round stops at once; the whole-run backstop is the error rounds' (`caps.ts`
 * `patchBackstop`). Drift left at the cap is a checkpoint. */
export const MAX_REVISE_ROUNDS_PER_NODE = 3;
/** A suggested weakening the referee does not confirm goes back to the fixer at most this many times
 * per node; the next rejection halts at a cap, the orchestrating agent's to rule on (`CapReached.suggestions`). */
export const MAX_SUGGESTION_REJECTIONS = 2;

/** ERROR rounds of the minimal-patch loop: V1.5 finds an error on a faithful core → V1 in PATCH
 * mode writes the smallest repair that keeps the key contribution → a fresh V1.5 pass confirms it.
 * Only a round that carries a defect of a PAPER claim counts here: an error on a statement (as
 * printed, or as patched), a proof the referee could not check, a repair it could not confirm or
 * that misfits the paper, a disputed key-result list, an F-stage `correctness` rewind (user
 * decisions 2026-09-22, 2026-09-23). Since 2026-09-26 the cap is PER DEPENDENCY LEVEL (fix as you
 * go spends a round on every defective level, so a large paper must not hit a whole-run cap for
 * being large): 3 rounds per level, and a whole-run backstop of 3 × the core's level count (at
 * least `MIN_PATCH_BACKSTOP`). Reaching a cap never fails the run: it halts with a `cap_reached`
 * receipt for the orchestrator (`caps.ts`). */
export const MAX_PATCH_ROUNDS_PER_LEVEL = 3;
/** The least whole-run backstop on error rounds, whatever the core's level count. */
export const MIN_PATCH_BACKSTOP = 6;

/** REFINEMENT rounds (user decision 2026-09-23): an F-stage `clarify` rewind (the statement admits
 * several readings) and a MINIMALITY-only round (every `error` of the round is on a patch
 * hypothesis the referee graded correct but non-minimal, `minimality: true`). They refine a repair
 * that is already correct, so they have their own cap and never spend an error round. */
export const MAX_REFINEMENT_ROUNDS = 3;

/** Which counter a patch round spends: `error` → `patch_rounds`, `refinement` →
 * `refinement_rounds`. */
export type PatchRoundKind = "error" | "refinement";

/** Where an ERROR round is charged (`caps.ts` `errorScope`): the dependency level of the whole core
 * (`L<k>`, absolute — not the relative tag of a pause) of the nodes that stopped the grading, or
 * `global` (the final global pass, an F-stage rewind); the run's backstop rides along. */
export interface RoundScope {
  level: string;
  nodes: string[];
  backstop: number;
}

/** Per-node verdict of the V1.5 referee. */
export interface V15NodeVerdict {
  /** Core node id (`thm:…`, `lem:…`, `prop:…`, `def:…`, `ass:…`). */
  id: string;
  /** For `drift`: the correction as a mechanical edit the runner applies (see
   * `directive_edits.ts`); null when the fix needs the agent's judgement. */
  fix?: import("./directive_edits.js").DriftFix | null;
  /** Does the node mean what its source environment means? */
  faithfulness: "ok" | "drift";
  /** Does the statement admit more than one formal reading? `pinned`: yes, but the paper
   * itself determines the reading (the proof uses it, the conventions fix it, or the
   * alternative makes a nearby claim false/vacuous) — `reading` names it and the runner adds
   * it to the core as an explicit bookkeeping assumption. `unresolvable`: the text does not
   * determine it and the choice changes the truth or strength of a result in scope — the
   * paper's defect; the run stops at the referee. */
  ambiguity: "ok" | "pinned" | "unresolvable";
  /**
   * `ok`: reproduced. `bookkeeping`: a regularity / measurability / finiteness condition
   * the proof silently uses; `bookkeeping_assumption` supplies it — NOT a failure.
   * `unclear`: the referee could not reproduce a step and has no witness — not an error of the
   * paper, but not a pass either: the step goes to V1 patch mode to be written out in full.
   * `error`: a false step or counterexample; `witness` is REQUIRED.
   */
  correctness: "ok" | "bookkeeping" | "unclear" | "error";
  detail: string;
  witness: string | null;
  bookkeeping_assumption: { condition: string; reason: string } | null;
  /** `true` exactly when this is a patch part graded `error` ONLY because it is correct but
   * non-minimal (the witness names the strictly weaker sufficient replacement). Absent on reviews
   * written before the field. */
  minimality?: boolean;
  /** `true` exactly when this is a patched node graded `error` because the
   * repair, though it holds, WEAKENS what the paper claims (a changed conclusion, limit, rate,
   * constant or object; a substantive hypothesis excluding cases the paper claimed; a descoping).
   * The next patch round turns that patch into a suggested repair for the owner to rule on
   * (`weakening.ts`), never another fixer attempt. Absent on reviews written before the field. */
  weakens_contribution?: boolean;
  /** A FORM remark on a confirmed repair, never a grade: the corrected statement the fixer wrote mixes
   * a general claim with special cases holding under their own conditions, and reads better as a
   * general statement with corollaries. The fixer is asked once to re-emit it so
   * (`stage_v1_5.ts` `splitRequests`); the repair stays confirmed either way. null / absent: none. */
  split?: { why: string } | null;
  /** `true` exactly when this node is graded `error` only because a result it uses was repaired and
   * now states less (the step holds with the printed version): the fixer makes it follow the repair
   * (`stage_v1_5.ts` `followsRepair`). */
  follows_repair?: boolean;
  /** `true` when the referee drops the condition an earlier pass appended to this node (it shows it under
   * CONDITIONS APPENDED EARLIER); otherwise a fresh grade with no condition keeps it (`stage_v1_5.ts`
   * `keepEarlierConditions`). */
  bookkeeping_dropped?: boolean;
  /** REQUIRED when `ambiguity` is `pinned`: the reading the paper determines, as a single
   * condition in the paper's notation, and the evidence in the paper that fixes it; `of`, the
   * assumption / definition whose phrase it settles when that is not this node (it then binds every
   * result using that node — `compileReviewEdits`). */
  reading: { reading: string; evidence: string; of?: string | null } | null;
  /** REQUIRED at a confirmation whose patch carries the fixer's note (`owner_explanation`): the
   * referee's grade of that text for clarity (`CLARITY_RULE`), with a one-line reason; `unclear`
   * sends the note back to the fixer. null otherwise. */
  explanation_clarity?: ExplanationClarity | null;
  /** REQUIRED on an `error` that refutes the node (not a minimality / weakening grade): where the
   * witness lives — `in_scope` (a genuine instance of the paper's setting) or `degenerate` (a case
   * the setting implicitly excludes: a trivial functional, zero variance, an empty class, boundary
   * equality …) — and the instance, in one line. The runner turns a `degenerate` error into a
   * `bookkeeping` grade whose condition is the exclusion (`settleDegenerateWitness`): never an error
   * of the paper, never the fixer's. */
  witness_regime?: "in_scope" | "degenerate" | null;
  witness_instance?: string | null;
  /** Runner-owned: the paper's owner withdrew this finding (`--reject-finding`): the referee's
   * error on the node is overruled — graded `ok` — and `owner_reason` says why. */
  owner_overruled?: boolean;
  owner_reason?: string;
  /** Runner-owned (never in the referee's reply): the basis the verdict was given on
   * (`core_graph.ts` `basisInputs`), and whether this pass graded the node (`fresh`) or kept
   * a clean verdict an earlier pass gave on the same basis (`carried`). */
  basis?: string;
  /** Runner-owned: the scheme of `basis` (`core_graph.ts` `BASIS_SCHEME`; absent = 1) and what it was
   * computed from (`basisInputs`), so a later scheme can be migrated without a snapshot of the core. */
  basis_scheme?: number;
  basis_inputs?: { scheme: number; node: string; closure: string; symbols: Record<string, string>; readings?: Record<string, string>; verdicts?: Record<string, string>; own?: string };
  graded?: "fresh" | "carried";
  /** Runner-owned, sharded referee only (`referee_shards.ts`): the shard that graded the node. */
  shards?: string[];
  /** Runner-owned: an `error` on a result graded clean before, that uses these repaired nodes whose
   * statements changed (`followsRepair`): the result no longer follows from them — the fixer makes
   * it follow (a consequence patch); no error of the paper. */
  follows_repair_of?: string[];
}

/**
 * The symbol referee's grade of one symbol of the core's table (`referee_symbols.ts`), read against
 * where the paper introduces and uses it. Symbol shards run BEFORE the statement referees.
 */
export interface V15SymbolVerdict {
  /** The symbol's `name`, exactly as in the table. */
  name: string;
  /** Does the recorded `type` / `space` / `def` say what the paper's symbol is? `drift` carries `fix`. */
  meaning: "ok" | "drift";
  /** For `drift` (then required): the corrected `type`, `space` and/or `def` in the paper's notation
   * (null = that field is right). The runner applies it to the symbol table (`core_graph.ts`
   * `buildCore`, overlay `symbols`) before the statement referees run. */
  fix: { type: string | null; space?: string | null; def: string | null } | null;
  /** Conventions that live at symbol level: random vs fixed, what it is conditional on, domain /
   * support, index ranges, population vs sample quantity, a changed meaning later in the paper.
   * `pinned`: the paper determines them — `reading` states them and becomes the symbol's entry in the
   * table (binding on the statement referees and the F stages, which read the table): its GENERAL
   * part (`reading`: what the symbol means wherever it is used, naming no result) is the entry's
   * `def`; each SCOPED clause (`scoped`: what additionally holds of it in `results`, core statement
   * ids using the symbol) goes to the entry's `scoped`, and reaches a node only when it applies to it
   * (`core_graph.ts` `applicableClauses`) — so rewording one result's clause re-opens that result's
   * verdicts only. Absent `scoped` = none (every reading graded before the split). A drift `fix`
   * is general: it corrects the entry itself.
   * `unresolvable`: the paper leaves one open and a result's truth or strength depends on it. */
  ambiguity: "ok" | "pinned" | "unresolvable";
  reading: { reading: string; evidence: string; scoped?: ScopedClause[] } | null;
  /** The sentence (verbatim) where the paper later gives the symbol another meaning, else null. */
  redefined_at: string | null;
  detail: string;
  /** Runner-owned: the cache basis (the symbol as transcribed + its introducing passage), the hash
   * of the transcribed symbol a `fix` applies to, fresh or carried, and where it is introduced. */
  basis?: string;
  /** Runner-owned: a hash of each part of `basis` (`symbolBasisParts`), so the pass that grades the
   * symbol afresh can say which part moved. Absent on a verdict from before it was recorded. */
  basis_parts?: Record<string, string>;
  source?: string;
  graded?: "fresh" | "carried";
  introduced_at?: { flat_line: number; file: string | null; line: number | null } | null;
  /** Runner-owned: of the ids its scoped clauses are tagged with, each block a repair split off a
   * result, with that result — a re-worded block is re-keyed, and its successors are the blocks then
   * split from the same result (`referee_symbols.ts` `staleTags`). */
  split_tags?: Record<string, string>;
  /** Runner-owned, as on node verdicts: the shard that graded the symbol. */
  shards?: string[];
}

/** The confirming referee's judgement of the fixer's `key_results` (present exactly when the
 * core carries patches): a headline result the fixer left out would let it descope the part of
 * the paper it could not repair. */
export interface V15PatchReview {
  key_results_ok: boolean;
  detail: string;
  /** Runner-owned: hash of the key results and key contribution judged, so a later pass with no
   * node to grade can carry an approval of the same list. */
  basis?: string;
}

/** `discovery/v1_5_review.json`. `REVISE` = some node drifts (a transcription defect V1 can
 * fix); `FAIL` = some node is an `error` with a witness or an `unresolvable` ambiguity (the
 * paper's defect); else `PASS` (`bookkeeping`, `pinned` and `unclear` never block). */
export interface V15Review {
  verdict: "PASS" | "REVISE" | "FAIL";
  summary: string;
  nodes: V15NodeVerdict[];
  patch_review?: V15PatchReview | null;
  /** The referee's ruling on each pending FIXER rejection of an F-stage finding
   * (`state.verify.fixer_rejections`): `upheld` = the paper does grant what the finding says it
   * lacks (the finding becomes a note); otherwise the fixer must patch. */
  rejection_verdicts?: Array<{ node: string; upheld: boolean; detail: string }> | null;
  /** The symbol referee's grades of the whole symbol table (fresh and carried), graded before the
   * nodes (`referee_symbols.ts`); a pinned symbol reading becomes the symbol's entry in the table. */
  symbols?: V15SymbolVerdict[];
  /** Set when the sharded referee PAUSED its upward grading at a level for the fixer (fix as you go,
   * `stage_v1_5.ts`): the review then holds the levels up to the pause (and the carried verdicts);
   * `ungraded` wait for the next pass, and no global pass ran. */
  paused?: { level: string; ids: string[]; ungraded: string[] } | null;
  /** sha256 of `core.transcribed.json` when a global pass last read the whole paper. While the
   * transcription is that one, a delta global pass reads only the excerpts of the nodes it checks:
   * the wiring of everything else was checked against the whole paper on unchanged text. */
  global_paper?: string | null;
}

/** FIX AS YOU GO (`stage_v1_5.ts`, user decision 2026-09-24): the sharded referee stopped its upward
 * grading at a level whose nodes the fixer (or the owner) must answer first. The next V1.5 pass
 * confirms the repair (the delta, graded first) and continues from there. */
export interface LevelPause {
  /** The tag of the level the grading stopped at (`L2`; `fix-L0` when a delta confirmation failed). */
  level: string;
  /** Each node that stopped it, and the ids of the findings the fixer answers for it. */
  errors: Array<{ id: string; targets: string[] }>;
  /** Who answers: the fixer (an error round, `round` = the directive's round), the owner (a
   * repair that weakens a main theorem) or the runner (an intermediate result it narrowed); `halt`:
   * no one — a pass halted mid-way (no `errors`) and only hands on what it graded (`carry`). */
  via: "fixer" | "owner" | "runner" | "halt";
  round: number;
  /** The verdicts of the paused pass that stand on the next pass while their basis holds, whatever
   * their grade (a clean one is cached in `confirmed` anyway): node → basis. */
  carry: Record<string, string>;
  /** The nodes of `carry` graded since the last complete pass (this paused pass and any paused one
   * before it): the completing pass's global pass checks them (`referee_shards.ts` `amendable`).
   * Absent (a pause recorded before the field): every node of `carry`. */
  graded?: string[];
  at: string;
}

/** A minimal patch, as the report carries it on a `refuted` finding: what was changed so the
 * result holds, and whether an independent referee pass confirmed the patched statement. */
export interface FindingPatch {
  corrected_statement: string | null;
  proof_note: string;
  confirmed: boolean;
  /** The corollaries the repair splits off the result (their node ids): confirmed with it. */
  corollaries?: string[];
  /** The repair makes the result an umbrella over those blocks (`patches.ts` `umbrella`). */
  umbrella?: boolean;
  /** The repair weakens the paper's claim and the owner accepted it (`--accept-repair`): what the
   * weakened version gives up. */
  narrowed?: string;
  /** `runner`: an intermediate result (not a main theorem) whose weakened version the runner applied
   * automatically; absent when the owner accepted it. */
  narrowed_by?: "runner";
}

/** A durable observation the report must carry. Recorded by V1.5 (refutations, unresolvable
 * ambiguities) and by the F stages (refused re-derivation routes, witnessed refutations, cited
 * notes). */
export interface VerifyFinding {
  node: string;
  /** Which stage produced it, e.g. `"V1.5"`, `"F3"`, `"F4"`. */
  stage: string;
  kind: "refuted" | "unresolved" | "note";
  detail: string;
  witness: string | null;
  /** The statement as printed does not say enough to be checked (an ambiguity the paper leaves
   * open): nothing was shown false. On an `unresolved` finding no reading or repair was adopted —
   * the report names it not determined (`not_determined`); a `witness` there is against a repair
   * that was TRIED, never against the printed statement. On a `note` with a confirmed `patch` the
   * repair made it precise. */
  undetermined?: boolean;
  /** A refuted node repaired by a minimal patch (see `FindingPatch`). */
  patch?: FindingPatch | null;
  /** A refuted node the fixer could not repair and that no key result uses: reported, and
   * left out of the Lean formalization (with every non-key result resting on it). */
  descoped?: boolean;
  /** A result no repair keeps at full strength: the weakened repair the fixer suggested (text), never
   * applied, and — when the owner declined it (`--decline-repair`) — the owner's reason. */
  suggested_repair?: string;
  suggestion_declined?: string;
  at: string; // ISO timestamp
}

/** `state.verify`. */
export interface VerifyState {
  phase: VerifyPhase;
  /** Toolkit promotion round B, after the report (`src/proposals/`). */
  promotion?: import("../proposals/schema.js").ProposalRoundState;
  /** Toolkit promotion round A, after F1 (`src/proposals/round_a.ts`). */
  promotion_a?: import("../proposals/schema.js").ProposalRoundState;
  source: {
    /** The `input` argument as given on the command line. */
    input: string;
    main_file: string;
    sha256: string;
    /** The paper's arXiv identifier, as the owner declared it (`report --arxiv`). */
    arxiv?: string;
  };
  /** `--targets` labels, or null = every theorem-like env. */
  targets: string[] | null;
  /** sha256 of `core.json` as accepted by V1.5. The F-stage entry gate in verify mode
   * refuses a core whose hash differs (an edited core must go through V1.5 again). */
  core_sha256: string | null;
  v1_rounds: number;
  /** `true` once V1 extracted this run's core under the inline-citation accounting
   * (`inline_citations.ts`): every later V1 round checks it, whatever the reference core holds.
   * Absent on a run seeded before the accounting: its citations stay warnings. */
  citation_accounting?: boolean;
  /** Revise rounds over the whole run (the backstop's counter) and per drifting node. */
  v1_5_rounds: number;
  v1_5_rounds_by_node?: Record<string, number>;
  /** Suggested weakenings the referee rejected, per node (`MAX_SUGGESTION_REJECTIONS`). */
  suggestion_rejections?: Record<string, number>;
  /** The repaired results the fixer was asked ONCE to state as a general statement with corollaries
   * (the referee's form remark, `V15NodeVerdict.split`): its answer stands, so none is asked again. */
  split_requests?: string[];
  /** The drift the referee graded on the previous REVISE round, node id → the fix it stated
   * (JSON) or "" when it stated none. The SAME drift twice — same node, same fix or no fix —
   * is a structural block, not agent randomness: the loop stops at once rather than at the
   * cap. A node drifting again for a NEW reason is progress and gets its round. */
  last_drift?: Record<string, string>;
  /** Error rounds of the minimal-patch loop used over the whole run (the backstop counter). */
  patch_rounds?: number;
  /** Error rounds per dependency level (`L<k>` / `global`), each capped by
   * `MAX_PATCH_ROUNDS_PER_LEVEL`. Absent (state from before 2026-09-26): `caps.ts` migrates it. */
  patch_rounds_by_level?: Record<string, number>;
  /** Refinement rounds used — clarify rewinds and minimality-only rounds (`MAX_REFINEMENT_ROUNDS`). */
  refinement_rounds?: number;
  /** Set when a patch round was due but its counter is at its cap: the run halts here for the
   * orchestrator (`--resume --clear-patch-cap` grants one more window, `--resume --accept-cap`
   * ends the loop: to F1 with the repair kept at a V1.5 refinement cap, else to V6). Never set = not halted at a cap. */
  cap_reached?: CapReached | null;
  /** F-stage findings the orchestrator (`--reject-rewind`) or a confirmed fixer rejection ruled
   * out, and findings the paper's owner withdrew (`--reject-finding`, at a weakening or rewind halt):
   * the same finding again on the same node (same axis) is a note, never a halt — an owner's
   * withdrawal also overrules the V1.5 referee's re-raised error (`owner_rulings.ts`). */
  rejected_rewinds?: RejectedRewind[];
  /** Fixer rejections of F-stage findings awaiting the next V1.5 pass's ruling. */
  fixer_rejections?: FixerRejection[];
  /** The LEDGER of what the printed paper gets wrong: node → the FIRST correctness or ambiguity
   * finding the referee made on it, kept across every patch round and every V1.5 re-entry (it is
   * a fact about the transcription, so only a V1 re-entry clears it). Runner-owned — it lives here,
   * not in the hand-editable `patches.json`, so no patch file can erase an error. A patch on a node
   * with no entry is a supporting change. An entry of `kind: "clarification"` (an F-stage reviewer
   * found the statement admits more than one reading; the fixer wrote the intended reading into
   * it) is recorded too, but reported as a clarification, never as an error of the paper; an
   * error found later on the same node replaces it. */
  paper_errors?: Record<string, PaperError>;
  /** Set when every repair of some node would weaken the paper's claim: the suggested (weakened)
   * repairs, one decision for the batch. The run halts in every mode while it is `pending`;
   * `--resume --accept-repair` applies them as patches (a V1.5 pass confirms them),
   * `--resume --decline-repair "<reason>"` leaves those results refuted and descoped from Lean with
   * what rests on them (`weakening.ts`). */
  weakening_repair?: WeakeningRepair | null;
  /** The repair texts (patches and pending suggested repairs) the runner sent back to the fixer because
   * they do not compile (`weakening.ts` `restateAllPatches`): one key per node and text, so each is
   * sent back at most once. */
  restatement_rounds?: string[];
  /** Set when an annotated-paper render left blocks that could not be set as TeX, or pdflatex errors
   * (`render_check.ts`; user decision 2026-09-25: rendering fallbacks are a checkpoint, never silent):
   * the run halts BEFORE presenting an owner decision or entering F1 (every mode). Two kinds, never an owner waiver: `renderer` — the renderer is fixed and `--resume`
   * renders again; `contract` — model fragments still fail their compile check after their producer's
   * pass, and `--resume` routes them back again. Cleared by a render with neither. */
  render_checkpoint?: RenderCheckpoint | null;
  /** Owner receipts still awaiting a ruling when a `--from-stage V1|V1.5` re-entry redid the review
   * (`reentry_void.ts`): each was derived from verdicts the new review replaces, so it was set aside
   * (never presented again) and noted here. Owner decisions already taken are never voided. */
  voided_receipts?: VoidedReceipt[];
  /** Verdicts that STICK (user decisions 2026-09-22, 2026-09-23 "rewinds revise"): node → the
   * basis (`core_graph.ts` `basisInputs`: the node, what it is shown of the nodes it uses, the symbol entries those name) of the clean
   * verdict (`ok` / `bookkeeping`) a referee pass last gave it. A later V1.5 pass — in the same
   * patch loop, after `--from-stage V1` / `V1.5`, or after an F-stage rewind — sends only the nodes
   * whose basis moved (or that were never graded clean) to the referee and carries the rest from
   * `v1_5_review.json`. Cleared by a cold re-extraction (the source changed) and by
   * `--fresh-review`. */
  confirmed?: Record<string, string>;
  /** The scheme of the bases in `confirmed` (`core_graph.ts` `BASIS_SCHEME`; absent = 1). A cache under
   * another scheme is dropped at the next V1.5 pass (every node graded afresh) — scheme 4 carried over. */
  confirmed_scheme?: number;
  /** The symbol referee's cache: symbol name → the basis (`referee_symbols.ts` `symbolBasis`: the
   * symbol as transcribed + its introducing passage) of the verdict in `v1_5_symbols.json`. A later
   * V1.5 pass re-grades only the symbols whose basis moved. Cleared with `confirmed`. */
  confirmed_symbols?: Record<string, string>;
  /** Set while the sharded referee's grading is paused at a level for a repair (fix as you go;
   * `LevelPause`). Cleared by the pass that grades to the end and by a `--from-stage V1|V1.5` re-entry. */
  level_pause?: LevelPause | null;
  /** The last F-stage rewind into V1 patch mode (intent `incremental_repair`). The F runner records it as
   * `pending` when an F2.5–F4 proof reviewer escalates a defect in a
   * paper statement (`fix-source` `statement-wrong`, `unclear` on the statement's wording); an F1.5
   * one (`stage_0` / `stage_neg1`) is on file only in runs from before 2026-10-07. The
   * verify runner PRESENTS it and halts (every mode); the orchestrator approves it with `--resume`
   * (the runner writes the patch directive, counts a round, re-enters V1 and marks it `applied`, or
   * `refused` when no core statement can be named) or rejects it with `--reject-rewind` (`rejected`;
   * the F stages continue). A resume never applies it twice. */
  cross_stage_rewind?: CrossStageRewind;
  /** sha256 of `core.transcribed.json` when V1.5 accepted the core: the report's "as printed" text
   * must be the one that was reviewed. */
  transcribed_sha256?: string | null;
  /** sha256 of `core.transcribed.json` as V1 last wrote it: a different file at V1's entry was edited
   * by hand, and V1 would overwrite the edit. */
  transcribed_written_sha256?: string | null;
  findings: VerifyFinding[];
  report_path: string | null;
  /** Set by every `--dry-run` that seeds or advances the run (`verify/dry_run.ts`): its V1.5
   *  acceptance and F stages are synthetic, so the live runners refuse this state. Never unset
   *  except by a live `--from-stage V1`, which re-extracts from scratch. */
  dry_run?: boolean;
}

/** One entry of the paper-error ledger (`state.verify.paper_errors`). */
export interface PaperError {
  detail: string;
  witness: string | null;
  kind?: "error" | "clarification";
  /** The finding is an ambiguity the paper leaves open (no witness): the statement is not determined
   * enough to be checked — nothing was shown false. The fixer answers it like an error; left without
   * a confirmed repair it is reported as not determined, never as refuted. */
  undetermined?: boolean;
  /** Every repair of this node weakens the paper's claim (the fixer said so, or the referee graded
   * its repair `weakens_contribution`). */
  weakens_contribution?: boolean;
  /** The weakened repair suggested for it (text), and the owner's ruling on it. */
  suggested_repair?: string;
  /** An intermediate result (not a main theorem): the runner applied its weakened version
   * automatically (`weakening.ts` `narrowIntermediates`); no owner ruling. */
  auto_narrowed?: boolean;
  /** `finding rejected` (`--reject-finding`): the owner withdrew the finding — the printed
   * statement stands, the owner's reading is pinned (`ass:pin-owner-<n>`), and the entry is no error
   * of the paper (never reported refuted or repaired; `openErrorIds` skips it). */
  owner_decision?: "accepted" | "declined" | "finding rejected" | "redo";
  decision_reason?: string;
  /** Set with `owner_decision: "redo"` (`--redo-repair "<node>: <guidance>"`): the owner discarded the
   * suggested repair and sent the node back to the fixer under this guidance (binding). */
  guidance?: string;
  /** Set with `owner_decision: "finding rejected"`. */
  owner_overruled?: boolean;
}

/** One suggested (weakened) repair presented to the owner (`WeakeningRepair.items`). */
export interface WeakeningItem {
  node: string;
  /** The claim as printed. */
  printed: string;
  /** The weakened claim proposed (the corrected statement). */
  proposed: string;
  /** The corollaries the proposal splits off the statement: part of what is proposed. */
  corollaries?: Array<{ title?: string; statement: string }>;
  /** What the weakened version gives up, in one line. */
  given_up: string;
  /** `referee` when `given_up` is the referee's text; absent: the fixer's note. */
  given_up_by?: "referee";
  /** What is wrong with the PRINTED statement, and its witness: the paper's error on the node (from
   * the ledger), or the corrected results it was changed to follow; empty when no finding is on
   * record — never the grade of the repair (`given_up`). */
  detail: string;
  witness: string | null;
  /** Who found that no repair keeps the claim: the fixer, or the referee grading a repair. */
  source: "fixer" | "referee";
  /** The error and the suggestion for the paper's author (the fixer's note). */
  owner_explanation?: OwnerExplanationField;
  /** The owner's guidance of an earlier `--redo-repair` on this node, when the redo again ended in a
   * suggestion (shown with it). */
  guidance?: string;
}

/** The owner's ruling on one item of the receipt. */
export type WeakeningDecision = "accepted" | "declined" | "finding rejected" | "redo";

/** `state.verify.weakening_repair`: the owner's halt on suggested (weakened) repairs. The owner may
 * delete an item before answering; the answer covers the items listed, and any suggestion left
 * undecided is presented again. */
export interface WeakeningRepair {
  /** `ruled`: the owner ruled on the items differently (one resume, node-scoped answers). */
  status: "pending" | WeakeningDecision | "ruled";
  items: WeakeningItem[];
  /** The owner's ruling per item so far (node-scoped answers); the receipt stays `pending` until every
   * item is ruled on, or the resume closes it (items left unnamed are presented again). */
  decisions?: Record<string, WeakeningDecision>;
  /** The owner's reason (set when declined, or when the finding was rejected). */
  reason?: string;
  /** Not presented yet: the round that wrote it also changed the core elsewhere (patches applied,
   * intermediate results narrowed, statements restated), and a V1.5 pass confirms those first — the
   * receipt's own nodes kept out, as printed. Cleared by the pass that leaves nothing for the fixer
   * but these items; until then no answer to the receipt is taken (`pipeline.ts`). */
  unconfirmed?: boolean;
  at: string;
}

/** `state.verify.cross_stage_rewind`. */
export interface CrossStageRewind {
  intent: "incremental_repair";
  /** `pending` until the orchestrator rules on it: a plain `--resume` after the halt that
   * presented it approves it (`applied`, or `refused` when nothing can be routed);
   * `--resume --reject-rewind "<reason>"` rejects it (`rejected`). */
  status: "pending" | "applied" | "refused" | "rejected";
  /** Set when the runner halted to present it for approval (every mode, `--auto` included). */
  presented?: boolean;
  /** The orchestrator's reason (set when rejected). */
  rejected_reason?: string;
  /** Display id of the stage whose reviewer found it, e.g. `"F1.5"`, `"F2.5"`, `"F4"`. */
  stage: string;
  /** The F route that produced it: an F1.5 D-rewind (`stage_0` / `stage_neg1`) or an F2.5–F4
   * proof-review escalation (`fix-source` / `unclear`). */
  route: "stage_0" | "stage_neg1" | "fix-source" | "unclear";
  /** The finding as recorded (reason, proposed restatement, hypothesis the paper does not grant). */
  detail: string;
  /** The fixer's axis: `correctness` (the statement is wrong as printed; the default) or
   * `clarify` (it admits more than one reading; the fixer writes the intended one into it). */
  axis?: "correctness" | "clarify";
  /** The escalation's kind (`statement-wrong`, `ambiguous-spec`, …), for proof-review routes. */
  kind?: string;
  /** The node the reviewer named (`obj_id`), when it named one (the first target's, for a
   * batch). It must resolve to a node of the core; a Lean declaration is a Lean-side finding. */
  target?: string;
  /** Every paper-statement finding of ONE F-stage review pass, ruled on together (one approval,
   * one round). Absent on an F1.5 D-rewind and on receipts recorded before batching: those are
   * one target read from `target` / `detail` / `axis` (`receiptTargets`). The orchestrator may
   * delete an entry before `--resume` to leave that finding out of the approved batch. */
  targets?: RewindTarget[];
  /** Core statements the directive names (set when presented / applied). */
  nodes?: string[];
  /** The patch round it opened (set when applied). */
  round?: number;
  /** Why it was not applied (set when refused). */
  why?: string;
  at: string;
}

/** One finding of a rewind receipt (`CrossStageRewind.targets`). */
export interface RewindTarget {
  /** The node the reviewer named (core id or graph alias); absent → read from `reason`. */
  obj_id?: string;
  /** The escalation's kind (`statement-wrong`, `ambiguous-spec`, …). */
  kind?: string;
  /** The F route that produced it. */
  route?: "stage_0" | "stage_neg1" | "fix-source" | "unclear";
  axis: "correctness" | "clarify";
  /** The finding as recorded. */
  reason: string;
  /** Set when resolved: the core node it is about, what kind of node that is, and the
   * statements the fixer patches for it (the node itself for a statement; every statement
   * using it for an assumption or definition). */
  node?: string;
  node_kind?: "statement" | "assumption" | "definition";
  users?: string[];
  /** Set when resolved: `routed` (in the batch), `refused` (names no node of the core, or a
   * hypothesis no statement uses), `repeat` (a ruled-out finding raised again: a note). */
  status?: "routed" | "refused" | "repeat";
  why?: string;
}

/** A ruled-out F-stage finding (`state.verify.rejected_rewinds`). */
export interface RejectedRewind {
  node: string;
  axis: "correctness" | "clarify" | "ambiguity";
  stage: string;
  route: string;
  detail: string;
  reason: string;
  /** `owner`: the paper's owner withdrew it (`--reject-finding`); its reading is pinned as `pin`. */
  by: "orchestrator" | "fixer+referee" | "owner";
  /** The owner's reading as pinned into the core (`ass:pin-owner-<n>`), for `by: "owner"`. */
  pin?: string;
  at: string;
}

/** A fixer's rejection of an F-stage finding, pending the next V1.5 ruling. */
export interface FixerRejection {
  node: string;
  axis: "correctness" | "clarify";
  from_stage: string;
  finding: string;
  witness: string | null;
  reason: string;
  where_the_paper_grants_it: string;
}

/** One pending owner receipt a fresh re-entry set aside (`state.verify.voided_receipts`). */
export interface VoidedReceipt {
  kind: "weakening_repair" | "cross_stage_rewind" | "cap_reached";
  /** The nodes (or finding ids) it listed, and how many items. */
  nodes: string[];
  items: number;
  /** Paper-error ledger entries dropped with it (a voided suggestion's node goes back to the
   * referee as printed; its error, if it still holds, is found again). */
  ledger_dropped?: string[];
  /** The re-entry that voided it. */
  reason: string;
  /** Where the receipt (and anything set aside with it) now lives. */
  set_aside: string;
  at: string;
}

/** `state.verify.render_checkpoint`: the blocks the last render could not set as TeX. */
export interface RenderCheckpoint {
  /** `renderer` (absent on a record from before the two kinds): the renderer is fixed. `contract`: model
   * fragments that still do not compile after their producer's pass (`fragment_routing.ts`). */
  kind?: "renderer" | "contract";
  /** The annotated paper's occasion (`V1.5`, `patch cap halt`, …). */
  when: string;
  defects: import("./render_check.js").RenderDefect[];
  at: string;
}

/** `state.verify.cap_reached`: the halt record when a patch round is due at its cap. */
export interface CapReached {
  counter: "patch_rounds" | "refinement_rounds";
  /** Rounds spent on that counter, and its cap (for `patch_rounds`: the level's, or the whole
   * run's when `backstop_hit`). */
  rounds: number;
  cap: number;
  /** An error cap: the level charged, the nodes that stopped the grading there, the whole-run
   * backstop, and whether the backstop (rather than the level's cap) was hit. Absent on a
   * refinement cap and on a receipt from before 2026-09-26. */
  level?: string;
  nodes?: string[];
  backstop?: number;
  backstop_hit?: boolean;
  /** The nodes whose suggested weakening the referee rejected more than `MAX_SUGGESTION_REJECTIONS`
   * times; `suggestions_only` when no round counter is at its cap (`rounds` / `cap` stay the counter's). */
  suggestions?: string[];
  suggestions_only?: boolean;
  /** Where the round was due: a V1.5 pass (its patch directive is already written) or an approved
   * F-stage rewind (the receipt stays pending). */
  origin: "V1.5" | "F-rewind";
  /** The findings the next round would hand the fixer. */
  findings: Array<{ id: string; axis: string; detail: string; witness: string | null }>;
  /** What the fixer's current patch file proposes. */
  proposed: Array<{ node: string; corrected_statement: string | null }>;
  at: string;
}

/** Arguments every V stage receives. `repoRoot` is the toolkit root; `runDir` is `<toolkit>/runs/<slug>/`. */
export interface VerifyStageArgs {
  repoRoot: string;
  qid: string;
  runDir: string;
  state: StateJson;
  deps: { runCodex: typeof runCodex; fetchBytes?: import("../formalization/citation_fetch.js").FetchBytes };
  dryRun: boolean;
  /** `theoremchecker.json` `referee.max_concurrent`: parallel referee calls of the sharded referee
   * (symbol and node shards). Default 6. */
  refereeMaxConcurrent?: number;
  /** `theoremchecker.json` `referee.shard_bytes` / `shard_max_*`: node shard sizes (defaults in
   * `referee_shards.ts` `DEFAULT_SHARD_LIMITS`). */
  refereeShardLimits?: { bytes?: number; hypotheses?: number; lemmas?: number; theorems?: number };
  /** `theoremchecker.json` `referee.symbol_effort`: codex reasoning effort of every symbol-referee
   * call (default "medium"); the statement referee stays at "high". */
  refereeSymbolEffort?: "low" | "medium" | "high";
  /** Fix as you go (sharded referee; default on): a level with an error pauses the upward grading
   * for the fixer. `false` grades every level in one pass — the referee evaluation harness, which
   * scores detection over the whole paper, runs so. */
  refereeFixAsYouGo?: boolean;
  /** DRY RUN only: nodes the synthetic sharded referee grades `error` until they are patched — to
   * exercise the fix-as-you-go interleave without a model. Ignored by a live run. */
  dryRunSyntheticErrors?: readonly string[];
  /** Verbose progress line; the runner prefixes and mirrors it to the pipeline log. */
  log: (msg: string) => void;
}

export interface VerifyStageResult {
  /** `completed`: advance `state.verify.phase`. `checkpoint`: persist and stop for the
   * operator (`--resume` re-enters this stage). `failed`: V1.5 refutation — go to V6.
   * `revise` (V1.5 only): the referee found drift / ambiguity; the stage has written
   * `discovery/v1_revise_directive.json` and the runner re-enters V1, which must consume
   * that file. The stage caps revise rounds per drifting node (`MAX_REVISE_ROUNDS_PER_NODE`).
   * `patch` (V1.5 only): an error (or unresolvable ambiguity) on a faithful core; the stage
   * wrote a `mode: "patch"` directive and the runner re-enters V1 in patch mode, whose
   * repaired core a fresh V1.5 pass then judges.
   * `narrowed` (V1.5 only): the stage applied the weakened version of intermediate results itself
   * (`weakening.ts`) and rebuilt `core.json`; the runner runs a fresh V1.5 pass to confirm it. */
  status: "completed" | "checkpoint" | "failed" | "revise" | "patch" | "narrowed";
  message: string;
  /** For `patch`: which counter the round spends (default `error`). */
  round_kind?: PatchRoundKind;
  /** For an `error` patch: where the round is charged. */
  round_scope?: RoundScope;
}

export type VerifyStage = (args: VerifyStageArgs) => Promise<VerifyStageResult>;

/** Run-dir layout helpers (relative to `runDir`). */
export const VERIFY_FILES = {
  sourceDir: "source",
  envsJson: "discovery/envs.json",
  flatTex: "discovery/flat.tex",
  flatLineMap: "discovery/flat.linemap.json",
  coreJson: "discovery/core.json",
  v15Review: "discovery/v1_5_review.json",
  v1ReviseDirective: "discovery/v1_revise_directive.json",
  /** The core exactly as V1 transcribed it, before any patch; `core.json` = this + patches. */
  coreTranscribed: "discovery/core.transcribed.json",
  /** V1's reference core: the only core edited by hand (the transcription and `core.json` are built
   * from it). */
  coreRefs: "discovery/core_refs.json",
  /** Which environments the core must cover, and why (`stage_v1.ts` `computeScope`). */
  v1Scope: "discovery/v1_scope.json",
  /** Per-pass referee cost record (prompt bytes, wall time, shards). */
  v15RefereeMetrics: "discovery/v1_5_referee_metrics.json",
  /** Stable ids of the referee's additions (`core_graph.ts` `compileReviewEdits`): key → `ass:bk-n` / `ass:pin-n`. */
  addedIds: "discovery/added_ids.json",
  /** The symbol referee's grades (`V15SymbolVerdict[]`): the delta cache, and the symbol-table fixes
   * every core build applies (`patches.ts` `rebuildPatchedCore`). */
  v15Symbols: "discovery/v1_5_symbols.json",
  /** Every live V1.5 referee call's prompt, `v1_5_<tag>__<stamp>.txt` (its reply: `codex_raw/`). */
  v15Prompts: "discovery/prompts",
  /** Minimal repairs (replacements of printed units, proof notes); see `patches.ts`. */
  patches: "discovery/patches.json",
  /** A V1 fixer reply the runner failed on (a runner error, not the fixer's): `{directive_sha256,
   * stdout}`; the next patch-mode entry on the same directive validates it before calling the fixer. */
  v1PendingReply: "discovery/v1_patch_pending_reply.json",
  reportMd: "report.md",
  reportJson: "report.json",
} as const;

