/**
 * V6 — the correctness report, assembled.
 *
 * PURE: `buildReport` takes everything the run produced (the paper's environments, the typed
 * core, the V1.5 review, the findings, the F-stage added premises, the crosswalk, the Lean
 * evidence) and returns `{json, md}`. No I/O, no model call, no clock — the same inputs always
 * give the same bytes, so the report is diffable across re-runs.
 *
 * One row per in-scope THEOREM-LIKE environment of the paper, in document order, each keyed to
 * the core statement transcribed from that environment — followed by one row per block a repair
 * split off that statement (`split_from`, `split_kind`: a corollary of it or a proposition it bundled; a result of its own, certified in Lean like any other). The row's bucket is decided by this
 * rule, evaluated top to bottom:
 *
 *   repaired                  every `refuted` finding on it is repaired by a minimal patch an
 *                             independent referee pass confirmed — before Lean (`not_checked`
 *                             below), or with the rest of this rule certifying the corrected
 *                             statement in Lean (a repair Lean did not certify is `unresolved`)
 *   refuted                   a `refuted` finding names it (V1.5 error with a witness, or an
 *                             F-stage counterexample) and has no confirmed repair
 *   not_determined            an `undetermined` finding names it: the statement as printed could
 *                             not be checked — it does not say enough (an ambiguity the paper
 *                             leaves open) and no reading or repair was adopted. Nothing was
 *                             shown false
 *   unresolved                an `unresolved` finding names it
 *   not_checked               the run stopped before Lean (`earlyStop`)
 *   unresolved                no Lean evidence, no Lean declaration, a crosswalk verdict other
 *                             than `exact`/`equivalent` (the Lean statement is not the paper's),
 *                             the build failed, the soundness scan names its file, or its axioms
 *                             are not clean
 *   conditional               it is itself a result the paper cites and the run left cited; or
 *                             it rests on ≥1 `cited` result, or on ≥1 deferred substrate gate
 *                             the operator chose to leave assumed
 *   verified_with_bookkeeping it rests on ≥1 added condition (a V1.5 bookkeeping assumption or
 *                             an F-stage added premise)
 *   verified                  none of the above
 *
 * Header verdict: `errors_found` when anything is refuted, else `not_determined` when anything is
 * not determined, else `incomplete` when anything is unresolved or not checked, else
 * `no_error_found`. "Unresolved" and "not determined" are never rendered as "wrong",
 * and "verified" is never rendered as unconditional — the disclaimer and the added-conditions /
 * cited-results sections carry what every verdict is conditional on.
 */
import { proseParts, resultWord, type NoteProse } from "./owner_text.js";
import { citedDisclosure, renderPlainSections } from "./report_plain.js";
import type { Core, CoreStatement } from "../core/schema.js";
import type { FormalizationGraph, GraphNode } from "../graph/types.js";
import type { AddedAssumption, CrosswalkEntry, CrosswalkVerdict } from "../types.js";
import type { DeclAxioms, LeanEvidence } from "./lean_evidence.js";
import { PROOF_CHANGE_MARKER } from "./patches.js";
import { fullReadingText, resultTexName, splitKinds, type SplitKind } from "./core_graph.js";
import { locatorKey, THEOREM_LIKE_KINDS } from "./transcription_lint.js";
import { mainTheoremIds } from "./weakening.js";
import type { V1Warnings } from "./lint_warnings.js";
import type { EnvKind, EnvsJson, TexEnv, V15Review, VerifyFinding } from "./types.js";

export type ReportBucket =
  | "verified"
  | "verified_with_bookkeeping"
  | "conditional"
  | "repaired"
  | "unresolved"
  | "refuted"
  | "not_determined"
  | "not_checked";

/** Report order, best to worst. Fixes the summary-table row order. */
export const REPORT_BUCKETS: readonly ReportBucket[] = [
  "verified",
  "verified_with_bookkeeping",
  "conditional",
  "repaired",
  "unresolved",
  "not_checked",
  "not_determined",
  "refuted",
];

export type ReportVerdict = "no_error_found" | "repaired" | "errors_found" | "not_determined" | "incomplete";

/** The paper's grade, on the paper's mathematics alone (Lean's progress is the verdict's): `major` —
 * an error affects a main result or the contribution; `minor` — errors, ambiguities, bookkeeping or
 * corner cases that leave every main result as printed; `error_free` — none of these. */
export type PaperGrade = "error_free" | "minor" | "major";

/** One reason for the grade: the result it is on, and what happened, in a few words. */
export interface GradeItem {
  node: string;
  what: string;
}

export interface ReportPaperGrade {
  grade: PaperGrade;
  major: GradeItem[];
  minor: GradeItem[];
}

const GRADE_TEXT: Record<PaperGrade, string> = {
  error_free: "ERROR-FREE — no error, ambiguity or added condition found",
  minor: "MINOR ISSUES — no main result is shown false or weakened",
  major: "MAJOR ERRORS — a main result or the contribution is affected",
};

const VERDICT_TEXT: Record<ReportVerdict, string> = {
  no_error_found: "NO ERROR FOUND",
  repaired: "ERRORS FOUND — REPAIRED BY MINIMAL PATCHES",
  errors_found: "ERRORS FOUND",
  not_determined: "NOT DETERMINED — RESULTS THAT COULD NOT BE CHECKED AS PRINTED",
  incomplete: "INCOMPLETE",
};

export const REPORT_DISCLAIMER =
  "This is a conditional report. A `verified` result is verified only up to the cited results it " +
  "assumes, the substrate gates left assumed, and the conditions added during formalization — " +
  "all listed in full below. " +
  "`unresolved` means the formalization did not close; it is NOT a claim that the result is " +
  "wrong. A `refuted` row is a result shown false by a positive witness with no confirmed repair; " +
  "a `repaired` row was false as printed, and an independent referee confirmed its minimal repair. " +
  "A `not_determined` row could not be checked as printed: the paper does not say enough to " +
  "determine the claim, and no reading or repair was adopted; it is NOT a claim that the result is wrong.";

/** A V1.5 bookkeeping condition carried by one result. */
export interface ReportBookkeeping {
  id: string;
  condition: string;
  reason: string;

}

/** A `cited` leaf in one result's transitive `depends_on` closure. */
export interface ReportCitedHypothesis {
  id: string;
  cite: string;
  locator: string;
  /** What the citation was checked against (the fetched arXiv source, or a source the user
   * supplied), or null when it was never checked against a source. */
  source_check: string | null;
  /** Why it was not checked, when the user declared the cited work inaccessible. */
  unchecked_reason?: string | null;
  /** What Lean ASSUMES for it: the declaration that carries the citation (`ReportInput.citedLean`).
   * Absent when the run has none (it never reached Lean; the gate was left undelivered). */
  lean?: ReportCitedLean;
  /** A result a PROOF invokes by citation (`cited_in`): the result whose proof it is, and the passage
   * of that proof the node is made of. */
  cited_in?: string;
  passage?: string;
}

/** The Lean declaration of a cited gate: its name, its file (under the run's Lean directory) and
 * line, and its source text — null when the file or the declaration was not found. */
export interface ReportCitedLean {
  decl: string;
  file: string;
  line: number | null;
  statement: string | null;
}

/**
 * A substrate gate still ASSUMED by one result: a dischargeable classical fact the F stages
 * gated rather than proved, and that the operator elected not to build (cap gate cleared). Verify
 * mode builds and promotes substrate — this is the disclosed exception,
 * not the norm.
 */
export interface ReportAssumedGate {
  id: string;
  description: string;
}

/** One result's change record: the user's version against the corrected version the Lean
 * formalizes, diffed from `core.transcribed.json` and `core.json`. */
export interface ReportChange {
  /** The statement as printed (verbatim, whitespace-normalized). */
  printed: string;
  /** The corrected statement, or null when the text is unchanged. */
  corrected: string | null;
  /** Side conditions / readings the confirming referee added to the changed result: part of the
   * corrected version too, so it is complete. */
  referee_conditions: ReportBookkeeping[];
  /** The paper's own dependencies the corrected result no longer uses (its repair supersedes or drops them). */
  dropped_dependencies: string[];
  /** How the proof changes, or null when it does not. */
  proof_change: string | null;
  /** The result was left out of the Lean formalization (unfixable, or rests on one). */
  descoped: boolean;
}

/** The V1.5 referee's three axes for this result, when it reviewed it. */
export interface ReportV15 {
  faithfulness: string;
  ambiguity: string;
  correctness: string;
  detail: string;
}

export interface ReportRow {
  env_id: string;
  label: string | null;
  kind: EnvKind;
  title: string | null;
  /** `file:from-to` in the user's ORIGINAL source coordinates. */
  locator: string;
  node_id: string;
  /** A corollary a repair split off this result (`core_graph.ts`): the paper does not print it; the
   * row stands at its parent's environment (`env_id`, `locator`). Absent on a printed result. */
  split_from?: string;
  /** With `split_from`: what the block is (`core_graph.ts` `splitKind`) — a corollary of the corrected
   * result, or a proposition the printed statement bundled in. Absent in a report written before the
   * kinds were told apart: a corollary. */
  split_kind?: SplitKind;
  /** The corrected result is an UMBRELLA (`core_graph.ts` `UMBRELLA_STATEMENT`): every conclusion of
   * the printed statement is one of its blocks (the rows with `split_from` = this node, all
   * propositions) and it has no Lean declaration of its own (`lean` null). Its `bucket` and `axioms`
   * are DERIVED from its blocks' (`deriveUmbrella`): never better than its worst block. */
  umbrella?: true;
  /** What was actually claimed: the core statement's text (the environment body V1 transcribed
   * verbatim), whitespace-normalized, WITHOUT the bracketed hypothesis list V1 may append. */
  statement: string;
  /** That appended `[Hypotheses: …]` list, contents only, or null when V1 appended none. It is
   * V1's own annotation rather than the paper's words, so it is reported apart from them. */
  appended_hypotheses: string | null;
  bucket: ReportBucket;
  lean: { file: string; decl: string; line: number } | null;
  crosswalk_verdict: CrosswalkVerdict | null;
  bookkeeping: ReportBookkeeping[];
  /** How the corrected version differs from the user's version, or null when unchanged. */
  change: ReportChange | null;
  cited_hypotheses: ReportCitedHypothesis[];
  assumed_substrate: ReportAssumedGate[];
  added_premises: AddedAssumption[];
  findings: VerifyFinding[];
  axioms: DeclAxioms | null;
  v1_5: ReportV15 | null;
  /** For a `refuted` or `not_determined` row: refuted results in its `depends_on` closure. A result
   * that rests on a refuted result is not an independent error — the report groups it under its root(s). */
  inherits_refutation_from: string[];
  /** For such a row: the `not_determined` results in its `depends_on` closure (nothing shown false
   * there). Absent when none. */
  rests_on_undetermined?: string[];
}

/** Which optional inputs the stage found, and why any is missing. Values are free text so the
 * reason ("absent: the run stopped at V1.5") survives into the report instead of a bare null. */
export interface ReportInputStatus {
  v1_5_review: string;
  crosswalk_full: string;
  graph_json: string;
  v1_scope: string;
  lean_evidence: string;
}

export interface VerifyReportJson {
  schema: 1;
  run: {
    qid: string;
    main_file: string;
    source_sha256: string;
    stage_completed: string;
    early_stop: boolean;
  };
  verdict: ReportVerdict;
  /** The paper's grade (`paperGrade`); absent in a report written before it existed. */
  paper_grade?: ReportPaperGrade;
  summary: Record<ReportBucket, number>;
  results: ReportRow[];
  /** Findings on `"run"`, or on a node that maps to no result. */
  run_level_findings: VerifyFinding[];
  /** The confirming referee's judgement of the repair's key results and contribution, when the
   * paper was repaired. */
  patch_review: { key_results_ok: boolean; detail: string } | null;
  /** V1.5 `unclear` observations: never a failure, always disclosed. */
  unclear_notes: Array<{ node: string; detail: string }>;
  /** The symbol readings V1.5 pinned (each the symbol's settled meaning in the table): suggestions
   * to the authors, never errors. Absent before the field. `reading`: the reading in full — its
   * general part, then each scoped clause led by its results' names (`core_graph.ts`
   * `fullReadingText`). */
  symbol_readings?: Array<{ symbol: string; reading: string; evidence: string }>;
  /** Findings the paper's owner withdrew (`--reject-finding`): no error of the paper — never refuted,
   * never repaired — each with the owner's reading and the pin carrying it. Absent before the field. */
  withdrawn_findings?: WithdrawnFinding[];
  /** The structured explanation of each error for the paper's author, by node ("Claim / What is
   * wrong / Why / Proposed fix / Gives up"). Absent when none is on file. */
  explanations?: Record<string, NoteProse>;
  /** V1's non-blocking observations (`discovery/v1_lint_warnings.json`): `lint` about the core,
   * `parser` about the source tree. Disclosed, never a verdict. */
  v1_warnings: { lint: string[]; parser: string[] };
  lean_build: { ok: boolean; log_tail: string } | null;
  sorry_scan: string[] | null;
  flags: { verify_no_d_rewind?: string | null };
  inputs: ReportInputStatus;
  disclaimer: string;
  /** Each result as the paper names it ("Theorem 2"), by node: the plain-language part's names
   * (`report_plain.ts`). Absent before the field. */
  names?: Record<string, string>;
  /** The annotated paper (`annotated/`), as the stage wrote it. */
  annotated?: Record<string, unknown>;
  /** The corrected-paper bundle (`bundle.ts`). Absent before the field. */
  bundle?: ReportBundle;
}

/** Where the corrected-paper bundle is and what its mechanical checks leave open. */
export interface ReportBundle {
  /** Relative to the run. */
  dir: string;
  /** Why it was not written, when it was not. */
  error?: string;
  /** `dir`: its folder in the bundle (absent on a report written when it was `paper`). */
  paper: { dir?: string; main: string; pdf: string | null; pages: number | null; compile: { status: string; tool: string | null; reason: string } };
  /** `TODO.md` of the corrected paper: what keeps the paper from being ready to submit. */
  todo: { total: number; blocking: number };
  /** `lean/`, a standalone Lake project: what it requires, whether it is self-contained, and each
   * base library's local checkout beside the public revision required (`bundle_lean.ts`). */
  lean: {
    files: number;
    toolkit_modules: string[];
    requires: Array<{ name: string; form: "git" | "vendored"; git?: string; rev?: string; /** The catalogue's pin, when `rev` is the toolkit's own and differs. */ catalog_rev?: string; path?: string }>;
    toolchain: string;
    manifest: boolean;
    check: string | null;
    self_contained: { ok: boolean; problems: string[] };
    /** Built against: the local copy's commit and the content hash of each file reached. */
    base: Array<{ name: string; public_git: string; public_rev: string; local_rev: string | null; uncommitted: number; files: Record<string, string>; status: "same" | "differs" | "unverified"; changed: string[]; detail: string }>;
    /** Blocking: what was built differs from what the bundle requires. */
    warnings: string[];
    /** Not blocking: what was not verified. */
    notes: string[];
  } | null;
  /** `f4_seal.json`: the code of the two reviewers' F4 receipts, and what keeps it from certifying a
   * finished F4 (`f4_seal.ts`). Absent when the run has no Lean. */
  f4_seal?: { code: string; problems: string[]; reviews: string | null };
  /** The page snapshot (`ui/page_snapshot.ts`), relative to the bundle; null when it was not written. */
  page?: string | null;
}

/** A finding the paper's owner withdrew (`state.verify.rejected_rewinds`, `by: "owner"`). */
export interface WithdrawnFinding {
  node: string;
  /** Where it was raised (`V1.5`, `F2.5`, …). */
  stage: string;
  finding: string;
  /** The owner's reading / why the finding is wrong. */
  reason: string;
  /** The pinned reading carrying it (`ass:pin-owner-<n>`). */
  pin: string | null;
}

export interface ReportInput {
  /** Findings the paper's owner withdrew; absent = none. */
  withdrawn?: WithdrawnFinding[];
  /** Each error's structured explanation for the author, by node (absent = none on file). */
  explanations?: Record<string, NoteProse>;
  qid: string;
  envs: EnvsJson;
  /** Env ids V1 put in scope (`discovery/v1_scope.json`), else every core-bearing env. */
  scope: string[];
  core: Core;
  review: V15Review | null;
  findings: VerifyFinding[];
  addedAssumptions: AddedAssumption[];
  crosswalk: CrosswalkEntry[] | null;
  graph: FormalizationGraph | null;
  lean: LeanEvidence | null;
  /** The Lean declaration of each cited gate, by core node id (`stage_v6_report.ts`
   * `citedGateDeclarations`); absent = none read. */
  citedLean?: Record<string, ReportCitedLean>;
  /** V1's non-blocking lint + parser warnings, or two empty lists when it left none. */
  warnings: V1Warnings;
  /** Statements of the transcribed core left out of `core` because a minimal patch descoped
   * them (unfixable side results and what rests on them). Rows only; they were not formalized. */
  descoped?: CoreStatement[];
  /** `core.transcribed.json` — the user's version, which `core` corrects. Absent = no patches. */
  transcribed?: Core | null;
  /** The repairs on file (`discovery/patches.json`): the fixer's key results, and which repairs weaken
   * the result they repair (`accepted_weakening`). Absent = none read. */
  patches?: { key_results: readonly string[]; patches: ReadonlyArray<{ node: string; accepted_weakening?: boolean; given_up?: string }>; owner_readings?: ReadonlyArray<{ node: string }> } | null;
  flags: { verify_no_d_rewind?: string | null };
  stageCompleted: string;
  earlyStop: boolean;
  sourceSha256: string;
  inputs: ReportInputStatus;
}

// ---------------------------------------------------------------------------
// assembly
// ---------------------------------------------------------------------------

/**
 * Crosswalk verdicts that certify the Lean declaration states the PAPER's result. `exact` and
 * `equivalent` pass; every other value of `CrosswalkVerdict` (`weaker-in-Lean`,
 * `stronger-in-Lean`, `missing-in-Lean`, `extra-in-Lean`, `encoding-drift`, `drift`, and the
 * pre-review placeholder `unmatched`) says the two statements differ — a proof of a different
 * statement is not evidence for this row, however clean its axioms are.
 */
const CROSSWALK_PASS: ReadonlySet<CrosswalkVerdict> = new Set<CrosswalkVerdict>([
  "exact",
  "equivalent",
]);

/** Does this row's Lean statement match the paper's, per the crosswalk reviewer? */
function crosswalkCertifies(verdict: CrosswalkVerdict | null): boolean {
  return verdict !== null && CROSSWALK_PASS.has(verdict);
}

/** Statement kinds a crosswalk row may anchor a paper result with. */
const STATEMENT_ENTRY_KINDS: ReadonlySet<CrosswalkEntry["kind"]> = new Set([
  "theorem",
  "lemma",
  "proposition",
]);

/** The path a soundness-scan issue names, e.g. `sorry in a/b.lean` → `a/b.lean`. */
function issuePath(issue: string): string | null {
  const m = /([\w./-]+\.lean)/u.exec(issue);
  return m ? m[1] : null;
}

/** Does a soundness-scan issue name this result's Lean file? The scan reports repo-relative
 * paths while the crosswalk records the file relative to the run's Lean dir, so a suffix match
 * on a full path segment is the honest comparison. */
function scanNamesFile(issues: readonly string[], leanFile: string): boolean {
  const target = leanFile.split(/[\\/]+/u).join("/");
  return issues.some((issue) => {
    const p = issuePath(issue);
    return p !== null && (p === target || p.endsWith(`/${target}`));
  });
}

/**
 * A gate node still ASSUMED. Discharge REMOVES a node's gate keys (`withoutGateKeys`) and
 * reclassifies it to a proved lemma, so a node that is STILL `kind:"gate"` is by construction
 * undischarged. `gate_class:"cited"` gates are the literature leaves — reported separately as
 * cited results — so only the non-cited ones count here.
 */
function isAssumedGate(n: GraphNode): boolean {
  // … and a hypothesis the proof filler added to the Lean as a `substrate-gate` (a classical fact
  // assumed, to be built): the reviewers pass it as visible debt, so the result is conditional on it.
  if (isAgentAssumption(n)) return n.assumption?.classification === "substrate-gate";
  if (n.kind !== "gate") return false;
  if (n.gate?.gate_class === "cited") return false;
  return true;
}

/** A hypothesis an F stage added to a result's Lean statement (`proof_filler.ts`: an `assumption`
 * node `agent-introduced`, wired to the result by a `proof-uses` edge). */
function isAgentAssumption(n: GraphNode): boolean {
  return n.kind === "assumption" && n.provenance === "agent-introduced";
}

/**
 * Split a core statement into the paper's own text and the `[Hypotheses: …]` list V1 is allowed
 * to append (`prompts/V1/extract_core.txt`: the body is verbatim, only that one bracket may
 * follow). Whitespace is normalized so the row is one table cell; nothing else is altered.
 */
export function splitStatement(text: string): { statement: string; appended: string | null } {
  const flat = text.replace(/\s+/gu, " ").trim();
  const m = /\s*\[Hypotheses:([^\]]*)\]\s*$/u.exec(flat);
  if (!m) return { statement: flat, appended: null };
  return { statement: flat.slice(0, m.index).trim(), appended: m[1].trim() };
}

/** Short, single-line description of a graph node for the report tables. */
function nodeDescription(n: GraphNode): string {
  const text = (n.nl?.statement ?? "").replace(/\s+/gu, " ").trim();
  return text.length > 240 ? `${text.slice(0, 239)}…` : text || n.id;
}

export function buildReport(input: ReportInput): { json: VerifyReportJson; md: string } {
  const { core, envs, findings, earlyStop } = input;
  const scopeSet = new Set(input.scope);
  const allStatements = [...core.statements, ...(input.descoped ?? [])];
  const transcribedById = new Map((input.transcribed?.statements ?? []).map((s) => [s.id, s] as const));
  const descopedIds = new Set((input.descoped ?? []).map((s) => s.id));
  const stmtById = new Map<string, CoreStatement>(allStatements.map((s) => [s.id, s]));
  const stmtByLocator = new Map<string, CoreStatement>();
  for (const s of allStatements) {
    if (s.tex_locator) stmtByLocator.set(locatorKey(s.tex_locator), s);
  }

  const kinds = splitKinds(core);
  /** Every node id reachable from `root` through `depends_on` (root excluded). */
  const closureOf = (root: CoreStatement): Set<string> => {
    const seen = new Set<string>();
    const queue = [...root.depends_on];
    while (queue.length > 0) {
      const id = queue.shift() as string;
      if (seen.has(id)) continue;
      seen.add(id);
      const s = stmtById.get(id);
      if (s) queue.push(...s.depends_on);
    }
    return seen;
  };

  // --- crosswalk: obj_id (the Lean-side handle F stages key findings on) → core node id.
  const crosswalk = input.crosswalk ?? [];
  // The graph names each core node's obj_id (`L-1` for `lem:…`): the F5 crosswalk keys rows by it.
  const coreIdOfObj = new Map<string, string>(
    (input.graph?.nodes ?? []).flatMap((n) => (n.obj_id ? [[n.obj_id, n.id] as const] : [])),
  );
  const resolveEntryNode = (entry: CrosswalkEntry): string | null => {
    if (stmtById.has(entry.tex.label)) return entry.tex.label;
    if (stmtById.has(entry.obj_id)) return entry.obj_id;
    const viaGraph = coreIdOfObj.get(entry.obj_id);
    if (viaGraph && stmtById.has(viaGraph)) return viaGraph;
    const range = entry.tex.line_range.trim();
    if (range.length > 0) {
      const direct = stmtByLocator.get(range);
      if (direct) return direct.id;
      // A bare `from-to` anchor (no file) resolves only when it is unambiguous.
      const span = allStatements.filter(
        (s) => s.tex_locator && `${s.tex_locator.from}-${s.tex_locator.to}` === range,
      );
      if (span.length === 1) return span[0].id;
    }
    return null;
  };
  const entryForNode = new Map<string, CrosswalkEntry>();
  const objIdToNode = new Map<string, string>();
  // Statement-kind rows first, so a definition/assumption row can never shadow the theorem's
  // own anchor when both resolve to the same node.
  for (const pass of [true, false]) {
    for (const entry of crosswalk) {
      if (STATEMENT_ENTRY_KINDS.has(entry.kind) !== pass) continue;
      const node = resolveEntryNode(entry);
      if (node === null) continue;
      if (!objIdToNode.has(entry.obj_id)) objIdToNode.set(entry.obj_id, node);
      if (!entryForNode.has(node)) entryForNode.set(node, entry);
    }
  }

  // --- graph: the Lean-side dependency structure, used only to find gates a result still
  // ASSUMES. Edges of kind `statement-uses` / `proof-uses` point consumer → dependency;
  // `setup-of` points the other way and is deliberately not followed.
  const graphNodes = input.graph?.nodes ?? [];
  const graphById = new Map<string, GraphNode>(graphNodes.map((n) => [n.id, n]));
  const graphByHandle = new Map<string, GraphNode>();
  for (const n of graphNodes) {
    if (!graphByHandle.has(n.id)) graphByHandle.set(n.id, n);
    if (n.obj_id && !graphByHandle.has(n.obj_id)) graphByHandle.set(n.obj_id, n);
  }
  /** A result the paper cites that the run PROVED (planned as a proved lemma, or its gate discharged
   * later): no gate left on its graph node and its proof complete. It is no cited input of the
   * results using it. */
  const citationDischarged = (id: string): boolean => {
    const g = graphById.get(id);
    return !!g && g.kind !== "gate" && g.gate?.gate_class !== "cited" && g.proof?.state === "complete" && (g.proof.sorry_count ?? 0) === 0;
  };
  const graphDeps = new Map<string, string[]>();
  for (const e of input.graph?.edges ?? []) {
    if (e.kind !== "statement-uses" && e.kind !== "proof-uses") continue;
    graphDeps.set(e.from, [...(graphDeps.get(e.from) ?? []), e.to]);
  }
  const assumedGatesUnder = (start: GraphNode | undefined): ReportAssumedGate[] => {
    if (!start) return [];
    const seen = new Set<string>([start.id]);
    const queue = [...(graphDeps.get(start.id) ?? [])];
    const gates: ReportAssumedGate[] = [];
    while (queue.length > 0) {
      const id = queue.shift() as string;
      if (seen.has(id)) continue;
      seen.add(id);
      const n = graphById.get(id);
      if (!n) continue;
      if (isAssumedGate(n)) gates.push({ id: n.id, description: nodeDescription(n) });
      queue.push(...(graphDeps.get(id) ?? []));
    }
    return gates.sort((a, b) => a.id.localeCompare(b.id));
  };

  const v15ByNode = new Map(
    (input.review?.nodes ?? []).map((n) => [n.id, n] as const),
  );

  // --- rows, in document order.
  const inScope: TexEnv[] = envs.envs.filter(
    (e) => scopeSet.has(e.id) && THEOREM_LIKE_KINDS.has(e.kind),
  );
  const claimedFindings = new Set<VerifyFinding>();
  const rows: ReportRow[] = [];
  for (const env of inScope) {
    const key = locatorKey(env.lines);
    const own = stmtByLocator.get(key);
    if (!own) {
      // V1's transcription lint guarantees exactly one statement per in-scope theorem-like env,
      // so this is a broken core, not a reportable state. Say so rather than emit a row that
      // silently stands for nothing.
      throw new Error(
        `V6: no core statement carries tex_locator ${key} (environment ${env.id}). ` +
          "The core does not match envs.json — re-run V1 (--from-stage V1).",
      );
    }
    // The result, then the corollaries a repair split off it: results of their own that the paper
    // does not print, each a row at its parent's place.
    for (const stmt of [own, ...core.statements.filter((x) => x.split_from === own.id)]) {
      const split = stmt !== own;
      const closure = closureOf(stmt);

      const bookkeeping: ReportBookkeeping[] = core.assumptions
        .filter(
          (a) =>
            (a.bookkeeping?.added_by === "V1.5" || a.bookkeeping?.added_by === "V1-patch") &&
            ((a.used_by ?? []).includes(stmt.id) || closure.has(a.id)),
        )
        .map((a) => ({
          id: a.id,
          condition: a.condition,
          reason: a.bookkeeping?.reason ?? "",
        }))
        .sort((x, y) => x.id.localeCompare(y.id));

      // The result itself when the paper only cites it (a result the paper restates from the
      // literature and the run left cited), then the cited leaves it rests on.
      const cited_hypotheses: ReportCitedHypothesis[] = [stmt.id, ...closure]
        .map((id) => stmtById.get(id))
        .filter((s): s is CoreStatement => !!s && s.status === "cited" && !!s.source && !citationDischarged(s.id))
        .map((s) => {
          const unchecked = findings
            .find((f) => f.node === s.id && f.kind === "note" && f.detail.startsWith("cited source NOT checked: "))
            ?.detail.slice("cited source NOT checked: ".length);
          return {
            id: s.id,
            cite: s.source?.cite ?? "",
            locator: s.source?.locator ?? "",
            source_check:
              findings
                .find((f) => f.node === s.id && f.kind === "note" && f.detail.startsWith("cited source checked: "))
                ?.detail.slice("cited source checked: ".length) ?? null,
            ...(unchecked ? { unchecked_reason: unchecked } : {}),
            ...(input.citedLean?.[s.id] ? { lean: input.citedLean[s.id] } : {}),
            ...(s.cited_in ? { cited_in: s.cited_in, passage: s.statement } : {}),
          };
        })
        .sort((x, y) => x.id.localeCompare(y.id));

      const entry = entryForNode.get(stmt.id) ?? null;
      const lean = entry?.lean ? { file: entry.lean.file, decl: entry.lean.decl, line: entry.lean.line } : null;

      // The graph node this result was formalized as: the crosswalk's obj_id, else the core id.
      const graphNode =
        (entry ? graphByHandle.get(entry.obj_id) : undefined) ?? graphByHandle.get(stmt.id);
      const assumed_substrate = assumedGatesUnder(graphNode);

      // An F-stage premise says which theorem it belongs to through `anchor` / `label`; match on
      // every handle this result is known by. Unmatched premises are still listed run-wide under
      // "Added conditions", so nothing is lost.
      const handles = (split ? [stmt.id, lean?.decl ?? ""] : [stmt.id, env.id, env.label ?? "", lean?.decl ?? ""]).filter((h) => h.length > 0);
      const recorded = input.addedAssumptions.filter((a) => {
        // whole handles only: `lem:rr` is not `lem:rr-exists`
        const named = new Set(`${a.anchor ?? ""} ${a.label ?? ""}`.split(/[\s,;]+/));
        return handles.some((h) => named.has(h));
      });
      // The hypotheses the F stages added to this result's Lean (the graph records each on the
      // result it was added to): always disclosed. One classed `substrate-gate` is listed with the
      // gates the result still assumes (`assumed_substrate`), the others here.
      const inLean: AddedAssumption[] = (graphNode ? (graphDeps.get(graphNode.id) ?? []) : [])
        .map((id) => graphById.get(id))
        .filter((n): n is GraphNode => !!n && isAgentAssumption(n) && n.assumption?.classification !== "substrate-gate")
        .filter((n) => !recorded.some((a) => a.label === n.id))
        .map((n) => ({ label: n.id, statement: n.nl.statement, source: "added to the Lean statement by the proof stage", ...(n.nl.tex_anchor ? { anchor: n.nl.tex_anchor } : {}), ...(n.assumption?.classification ? { classification: n.assumption.classification } : {}) }));
      const added_premises = [...recorded, ...inLean];

      const ownFindings = findings.filter(
        (f) => f.node === stmt.id || objIdToNode.get(f.node) === stmt.id,
      );
      for (const f of ownFindings) claimedFindings.add(f);
      const rowFindings = ownFindings;

      const axioms = lean && input.lean ? (input.lean.axioms[lean.decl] ?? null) : null;
      const verdict = v15ByNode.get(stmt.id);

      const printedStmt = transcribedById.get(stmt.id) ?? stmt;
      const { statement, appended } = splitStatement(printedStmt.statement);
      const change = changeOf(stmt, printedStmt, bookkeeping, descopedIds.has(stmt.id));
      const row: ReportRow = {
        env_id: env.id,
        label: split ? null : env.label,
        kind: env.kind,
        title: !split ? env.title : kinds.get(stmt.id) === "proposition" ? `Proposition stated in ${env.title ?? env.label ?? env.id} (split off by its repair)` : `Corollary of ${env.title ?? env.label ?? env.id} (split off by its repair)`,
        locator: key,
        node_id: stmt.id,
        ...(split ? { split_from: own.id, split_kind: kinds.get(stmt.id) ?? "corollary" } : {}),
        ...(stmt.umbrella ? { umbrella: true as const } : {}),
        statement,
        appended_hypotheses: appended,
        bucket: "verified", // replaced immediately below
        lean,
        crosswalk_verdict: entry?.verdict ?? null,
        bookkeeping,
        change,
        cited_hypotheses,
        assumed_substrate,
        added_premises,
        findings: rowFindings,
        axioms,
        v1_5: verdict
          ? {
              faithfulness: verdict.faithfulness,
              ambiguity: verdict.ambiguity,
              correctness: verdict.correctness,
              detail: verdict.detail,
            }
          : null,
        inherits_refutation_from: [],
      };
      row.bucket = bucketOf(row, input);
      rows.push(row);
    }
  }
  // An umbrella has no declaration: what Lean establishes of it is what it establishes of its blocks.
  for (const r of rows) if (r.umbrella) deriveUmbrella(r, rows.filter((c) => c.split_from === r.node_id), input);
  // A split result is repaired only with its corollaries: one of them left open in Lean leaves it open.
  for (const r of rows) {
    if (r.bucket === "repaired" && rows.some((c) => c.split_from === r.node_id && (c.bucket === "unresolved" || c.bucket === "refuted" || c.bucket === "not_determined"))) r.bucket = "unresolved";
  }
  // Root-cause grouping: a refuted result whose closure contains another refuted result is
  // marked as inheriting it. Independent witnesses on both are still shown; the grouping only
  // says which errors are upstream.
  const hasRefutation = (r: ReportRow): boolean => r.findings.some(isPaperRefutation);
  const refutedIds = new Set(rows.filter(hasRefutation).map((r) => r.node_id));
  const undeterminedIds = new Set(rows.filter((r) => r.bucket === "not_determined").map((r) => r.node_id));
  for (const r of rows) {
    if (!hasRefutation(r) && !undeterminedIds.has(r.node_id)) continue;
    const s = stmtById.get(r.node_id);
    if (!s) continue;
    r.inherits_refutation_from = [...closureOf(s)].filter((id) => refutedIds.has(id)).sort();
    const open = [...closureOf(s)].filter((id) => undeterminedIds.has(id)).sort();
    if (open.length > 0) r.rests_on_undetermined = open;
  }

  const run_level_findings = findings.filter((f) => !claimedFindings.has(f));

  const summary = Object.fromEntries(
    REPORT_BUCKETS.map((b) => [b, rows.filter((r) => r.bucket === b).length]),
  ) as Record<ReportBucket, number>;

  // A run-level refutation/unresolved counts too: the runner's terminal phase is decided by
  // `findings` containing a `refuted` entry, so a header that ignored an unmapped refutation
  // would read `no_error_found` on a run the pipeline itself calls `failed`.
  const allRefutations = [
    ...rows.flatMap((r) => r.findings.filter(isPaperRefutation)),
    ...run_level_findings.filter(isPaperRefutation),
  ];
  const anyRefuted = allRefutations.length > 0;
  const allRepaired = anyRefuted && allRefutations.every(isRepaired);
  // Not determined: nothing shown false, so never `errors_found` on its own.
  const anyUndetermined = summary.not_determined > 0 || run_level_findings.some(isUndetermined);
  const anyOpen =
    summary.unresolved > 0 ||
    summary.not_checked > 0 ||
    run_level_findings.some((f) => f.kind === "unresolved");
  // "Repaired" is a claim about Lean: every error has a referee-confirmed repair AND every
  // repaired result is certified in Lean. Confirmed repairs not (yet) certified are incomplete.
  const repairsCertified = !earlyStop && rows.filter(hasRefutation).every((r) => r.bucket === "repaired");
  const verdict: ReportVerdict = anyRefuted && !allRepaired
    ? "errors_found"
    : anyUndetermined
      ? "not_determined"
      : anyRefuted
        ? repairsCertified && !anyOpen
          ? "repaired"
          : "incomplete"
        : anyOpen
          ? "incomplete"
          : "no_error_found";

  const unclearNodes = new Map<string, string>();
  for (const n of input.review?.nodes ?? []) {
    if (n.correctness === "unclear") unclearNodes.set(n.id, n.detail);
  }
  for (const f of findings) {
    if (f.kind === "note" && !unclearNodes.has(f.node)) unclearNodes.set(f.node, f.detail);
  }
  const unclear_notes = [...unclearNodes]
    .map(([node, detail]) => ({ node, detail }))
    .sort((a, b) => a.node.localeCompare(b.node));

  // A result a symbol reading's clause is tagged with: by its \ref, a split-off block by its parent
  // (`resultTexName`), an unlabelled one by its printed title; an id that is no result any more, not at all.
  const named: Core = { ...core, statements: allStatements };
  const tagName = (id: string): string | null => {
    const st = allStatements.find((x) => x.id === id);
    if (!st) return null;
    const title = rows.find((r) => r.node_id === id)?.title;
    return st.tex_locator?.label || st.split_from || !title ? resultTexName(named, id) : `${resultWord(st)} (${title})`;
  };

  const json: VerifyReportJson = {
    schema: 1,
    run: {
      qid: input.qid,
      main_file: envs.main_file,
      source_sha256: input.sourceSha256,
      stage_completed: input.stageCompleted,
      early_stop: earlyStop,
    },
    verdict,
    paper_grade: paperGrade(rows, run_level_findings, input.review, mainTheoremIds(input.transcribed ?? core, input.patches ?? null), input.patches ?? null, (id) => {
      const st = stmtById.get(id);
      return st ? [...closureOf(st)] : [];
    }),
    summary,
    results: rows,
    run_level_findings,
    patch_review: input.review?.patch_review ?? null,
    unclear_notes,
    symbol_readings: (input.review?.symbols ?? []).flatMap((s) => (s.ambiguity === "pinned" && s.reading ? [{ symbol: s.name, reading: fullReadingText(s.reading, tagName), evidence: s.reading.evidence }] : [])),
    ...(input.withdrawn?.length ? { withdrawn_findings: input.withdrawn } : {}),
    ...(input.explanations && Object.keys(input.explanations).length > 0 ? { explanations: input.explanations } : {}),
    v1_warnings: { lint: input.warnings.lint, parser: input.warnings.parser },
    lean_build: input.lean ? input.lean.build : null,
    sorry_scan: input.lean ? input.lean.sorry_scan : null,
    flags: input.flags,
    inputs: input.inputs,
    disclaimer: REPORT_DISCLAIMER,
  };

  return { json, md: renderReport(json) };
}

/**
 * The paper's grade. MAJOR: a main result (`mainTheoremIds`: the paper's theorems and corollaries, and
 * the fixer's key results; a block split off one counts with it) holds only weakened with its contribution
 * lost (the referee's patch review not finding the key results kept), is false with no
 * repair, is left out of the formalization, or rests (`restsOn`: its dependency closure) on a result
 * still false; or the run holds a refutation with no repair that no result carries. MINOR: an error
 * repaired without weakening a main result, a main result weakened only in constants or corner cases (the
 * contribution kept), an intermediate result narrowed or left false with no main
 * result on it, a reading pinned (by the referee or the owner, of a result or a symbol), a bookkeeping
 * condition, a result not stated precisely enough to check. ERROR-FREE: none of these. Pure.
 */
export function paperGrade(
  rows: readonly ReportRow[],
  runLevel: readonly VerifyFinding[],
  review: V15Review | null,
  mains: ReadonlySet<string>,
  patches: ReportInput["patches"] | null,
  restsOn: (id: string) => readonly string[] = () => [],
): ReportPaperGrade {
  const major: GradeItem[] = [], minor: GradeItem[] = [];
  const add = (to: GradeItem[], node: string, what: string) => { if (!to.some((x) => x.node === node && x.what === what)) to.push({ node, what }); };
  const rowOf = new Map(rows.map((r) => [r.node_id, r]));
  const stillFalse = (id: string): boolean => {
    const r = rowOf.get(id);
    return r ? r.bucket === "refuted" || r.change?.descoped === true : runLevel.some((f) => f.node === id && isPaperRefutation(f) && !isRepaired(f));
  };
  const isMain = (r: ReportRow): boolean => mains.has(r.node_id) || (r.split_from !== undefined && mains.has(r.split_from));
  // A main result weakened only in its constants or corner cases, the referee finding its key results and
  // the contribution kept (`patch_review.key_results_ok`), is minor; weakened otherwise, major.
  const contributionKept = review?.patch_review?.key_results_ok === true;
  for (const p of patches?.patches ?? []) {
    if (!p.accepted_weakening) continue;
    const what = `weakened${p.given_up ? `: ${p.given_up}` : ""}`;
    if (!mains.has(p.node)) add(minor, p.node, what);
    else if (contributionKept) add(minor, p.node, `${what} (the referee found the key results and the contribution kept)`);
    else add(major, p.node, what);
  }
  for (const r of rows) {
    const to = isMain(r) ? major : minor;
    if (r.bucket === "refuted") add(to, r.node_id, "false as printed, no repair holds");
    else if (r.change?.descoped) add(to, r.node_id, "left out of the formalization");
    const under = restsOn(r.node_id).filter((id) => id !== r.node_id && stillFalse(id));
    if (under.length) add(to, r.node_id, `rests on a result false as printed (${[...under].sort().join(", ")})`);
    if (r.findings.some(isRepaired)) add(minor, r.node_id, "error repaired");
    else if (r.change && (r.change.corrected !== null || r.change.proof_change !== null) && !r.findings.some(isPaperRefutation)) add(minor, r.node_id, "corrected");
    if (r.findings.some(isUndetermined)) add(minor, r.node_id, "not stated precisely enough to check");
    if (r.bookkeeping.length) add(minor, r.node_id, "condition added (bookkeeping or a pinned reading)");
  }
  for (const n of review?.nodes ?? []) if (n.ambiguity === "pinned") add(minor, n.id, "ambiguous; a reading was pinned");
  for (const sy of review?.symbols ?? []) if (sy.ambiguity === "pinned") add(minor, sy.name, "notation ambiguous; a reading was pinned");
  for (const o of patches?.owner_readings ?? []) add(minor, o.node, "ambiguous; the owner settled a reading");
  for (const f of runLevel) if (isPaperRefutation(f)) add(isRepaired(f) ? minor : major, f.node, isRepaired(f) ? "error repaired" : "refuted, no repair holds");
  // a main result's own repair stays listed, but under major when the result is major
  const majorNodes = new Set(major.map((x) => x.node));
  const minorLeft = minor.filter((x) => !(majorNodes.has(x.node) && x.what === "error repaired"));
  return { grade: major.length ? "major" : minorLeft.length ? "minor" : "error_free", major, minor: minorLeft };
}

/** The bucket rule. Its order is the contract — see this file's header. */
function bucketOf(row: ReportRow, input: ReportInput): ReportBucket {
  const refutations = row.findings.filter(isPaperRefutation);
  if (refutations.length > 0) {
    // `refuted` is reserved for an error with no confirmed repair.
    if (!refutations.every(isRepaired)) return "refuted";
  }
  // Not determined as printed, with no adopted reading or repair: never refuted, never verified.
  if (row.findings.some(isUndetermined)) return "not_determined";
  if (refutations.length > 0) {
    // A confirmed repair is `repaired` before Lean (`not_checked`) and once Lean certifies the
    // corrected statement; a repair Lean did not certify is unresolved — never refuted.
    return evidenceBucket(row, input) === "unresolved" ? "unresolved" : "repaired";
  }
  return evidenceBucket(row, input);
}

/** How far a block's bucket is from certified, worst last (`deriveUmbrella`). `repaired` is certified
 * (a repair Lean did not certify is `unresolved`, a block before Lean `not_checked` by its own rule). */
const EVIDENCE_ORDER: readonly ReportBucket[] = ["verified", "repaired", "verified_with_bookkeeping", "conditional", "not_checked", "unresolved", "not_determined", "refuted"];

/**
 * The bucket and the axioms of an UMBRELLA row, from its blocks' rows: it is established exactly when
 * every block is. Its Lean evidence is its WORST block's (a refuted or not-determined block leaves it `unresolved`, and
 * so does an umbrella without blocks); its axioms are the union of theirs, clean only when every block
 * was audited clean. Its own findings keep their say: an error with no confirmed repair is `refuted`,
 * a statement left undetermined `not_determined`, an unresolved finding `unresolved`; with a confirmed repair it is `repaired` once every block is
 * certified, as any repaired result (`bucketOf`). Mutates `row`.
 */
export function deriveUmbrella(row: ReportRow, blocks: readonly ReportRow[], input: Pick<ReportInput, "earlyStop">): void {
  const audited = blocks.map((b) => b.axioms);
  row.axioms = blocks.length > 0 && audited.every((a): a is DeclAxioms => !!a)
    ? { axioms: [...new Set(audited.flatMap((a) => a.axioms))].sort(), clean: audited.every((a) => a.clean), ...(audited.some((a) => a.error) ? { error: audited.map((a) => a.error).filter(Boolean).join("; ") } : {}) }
    : null;
  const worst = blocks.map((b) => b.bucket).sort((x, y) => EVIDENCE_ORDER.indexOf(y) - EVIDENCE_ORDER.indexOf(x))[0];
  const evidence: ReportBucket = row.findings.some((f) => f.kind === "unresolved") || worst === undefined || worst === "refuted" || worst === "not_determined" ? "unresolved" : worst === "repaired" ? "verified" : input.earlyStop ? "not_checked" : worst;
  const refutations = row.findings.filter(isPaperRefutation);
  row.bucket = !refutations.every(isRepaired) ? "refuted" : row.findings.some(isUndetermined) ? "not_determined" : refutations.length === 0 ? evidence : evidence === "unresolved" ? "unresolved" : "repaired";
}

/** A refutation of a claim of the PAPER. */
export function isPaperRefutation(f: VerifyFinding): boolean {
  return f.kind === "refuted";
}

/** The statement could not be checked as printed and no reading or repair was adopted: nothing was
 * shown false (`VerifyFinding.undetermined`). */
export function isUndetermined(f: VerifyFinding): boolean {
  return f.kind === "unresolved" && f.undetermined === true;
}

/** A statement the paper left undetermined, made precise by a confirmed repair: no error of the paper. */
export function isMadePrecise(f: VerifyFinding): boolean {
  return f.kind === "note" && f.undetermined === true && f.patch?.confirmed === true;
}

/** A refutation whose statement was repaired by a minimal patch a referee pass confirmed. */
export function isRepaired(f: VerifyFinding): boolean {
  return f.kind === "refuted" && f.patch?.confirmed === true;
}

/** The change record of one result: corrected text, proof change. */
function changeOf(
  stmt: CoreStatement,
  printed: CoreStatement,
  referee: ReportBookkeeping[],
  descoped: boolean,
): ReportChange | null {
  // Compare the claims only: V1's appended hypothesis list is wiring, not the paper's text.
  const was = splitStatement(printed.statement).statement;
  const now = splitStatement(stmt.statement).statement;
  const corrected = now !== was ? now : null;
  const at = (stmt.proof_tex ?? "").indexOf(PROOF_CHANGE_MARKER);
  const proof_change =
    at >= 0 ? (stmt.proof_tex ?? "").slice(at + PROOF_CHANGE_MARKER.length).replace(/\]\s*$/u, "").trim() : null;
  // An umbrella uses nothing itself: what the printed result used, its blocks use.
  const dropped = stmt.umbrella ? [] : printed.depends_on.filter((d) => !stmt.depends_on.includes(d));
  if (!corrected && referee.length === 0 && dropped.length === 0 && !proof_change && !descoped) return null;
  return {
    printed: was,
    corrected,
    referee_conditions: referee,
    dropped_dependencies: descoped ? [] : dropped,
    proof_change,
    descoped,
  };
}

/** The bucket rule below the refutation line: what the Lean evidence says about the row. */
function evidenceBucket(row: ReportRow, input: ReportInput): ReportBucket {
  if (row.findings.some((f) => f.kind === "unresolved")) return "unresolved";
  if (input.earlyStop) return "not_checked";
  // Past this point every remaining condition is Lean evidence. Absent evidence is never a
  // pass: a dry run reports `unresolved`, not `verified`.
  if (!input.lean) return "unresolved";
  // A result the paper cites and the run left cited has no Lean proof by design: it is an input,
  // taken from its source — conditional on that source, never `unresolved`.
  if (row.cited_hypotheses.some((c) => c.id === row.node_id)) return "conditional";
  if (!row.lean) return "unresolved";
  // The crosswalk verdict is the statement-level evidence: it says whether the Lean declaration
  // encodes THIS paper result. Drift (or the unreviewed `unmatched` placeholder) means the proof
  // that follows is about something else, so it can never certify the row.
  if (!crosswalkCertifies(row.crosswalk_verdict)) return "unresolved";
  if (!input.lean.build.ok) return "unresolved";
  if (scanNamesFile(input.lean.sorry_scan, row.lean.file)) return "unresolved";
  if (!row.axioms || !row.axioms.clean) return "unresolved";
  // A cited leaf and a deferred substrate gate are the same kind of debt: the result holds
  // GIVEN something this run did not prove. (Substrate is normally BUILT — see the study
  // hand-off — so a gate lands here only when the operator cleared the cap gate.)
  if (row.cited_hypotheses.length > 0 || row.assumed_substrate.length > 0) return "conditional";
  // Any added condition — a V1.5 bookkeeping node or ANY F-stage premise class — keeps the
  // result out of plain `verified`: it was proved under something the paper did not state.
  if (row.bookkeeping.length > 0 || row.added_premises.length > 0) {
    return "verified_with_bookkeeping";
  }
  return "verified";
}

// ---------------------------------------------------------------------------
// markdown
// ---------------------------------------------------------------------------

const DASH = "—";

/** One line of prose outside a table: newlines collapsed, pipes left alone (a table cell
 * escapes `|`, which would double the backslash of a TeX `\|` in a bullet list). */
function line(text: string): string {
  return text.replace(/\r?\n/gu, " ").trim() || DASH;
}

function cell(text: string): string {
  return text.replace(/\r?\n/gu, " ").replace(/\|/gu, "\\|").trim() || DASH;
}

function axiomText(a: DeclAxioms | null): string {
  if (!a) return DASH;
  if (a.error) return `unknown (${a.error})`;
  if (a.axioms.length === 0) return "clean (no axioms)";
  return `${a.clean ? "clean" : "NOT CLEAN"} — ${a.axioms.map((x) => `\`${x}\``).join(", ")}`;
}

function findingText(f: VerifyFinding): string {
  const w = f.witness ? ` ${isUndetermined(f) ? "witness against the repair tried" : "witness"}: ${f.witness}` : "";
  const p = f.patch ? ` minimal patch (${f.patch.confirmed ? "confirmed" : "NOT confirmed"}): ${patchText(f.patch)}` : "";
  const d = f.descoped ? " (left out of the Lean formalization)" : "";
  const sr = f.suggested_repair ? ` ${suggestionLabel(f)}: ${f.suggested_repair}` : "";
  return `[${isUndetermined(f) ? "not determined" : f.kind}, ${f.stage}] ${f.detail}${w}${p}${sr}${d}`;
}

/** How a suggested (weakened) repair is labelled: never applied, and why. */
function suggestionLabel(f: VerifyFinding): string {
  return f.suggestion_declined !== undefined ? `suggested repair (declined by the owner: ${f.suggestion_declined})` : "suggested repair (not applied)";
}

function patchText(p: NonNullable<VerifyFinding["patch"]>): string {
  const parts = [
    p.corrected_statement ? `corrected statement: ${p.corrected_statement}` : "",
    `proof change: ${p.proof_note}`,
    p.corollaries?.length ? `split off as results of their own: ${p.corollaries.join(", ")}` : "",
    p.narrowed ? (p.narrowed_by === "runner" ? `narrowed: ${p.narrowed}` : `contribution narrowed (accepted by the owner): ${p.narrowed}`) : "",
  ];
  return parts.filter(Boolean).join(" · ");
}


/** The paper's grade under the verdict, each reason by the result's name (`names`). Pure. */
export function renderGrade(json: Pick<VerifyReportJson, "paper_grade" | "names">): string[] {
  const g = json.paper_grade;
  if (!g) return [];
  const L = [`**Paper: ${GRADE_TEXT[g.grade]}**`, ""];
  const name = (id: string) => (id === "run" ? "the run" : json.names?.[id] ?? `\`${id}\``);
  // one line a result, its reasons in order
  const lines = (items: readonly GradeItem[]) => [...new Set(items.map((x) => x.node))].map((n) => `- ${name(n)}: ${items.filter((x) => x.node === n).map((x) => x.what).join("; ")}`);
  for (const [head, items] of [["Major", g.major], ["Minor", g.minor]] as const) if (items.length) L.push(`${head}:`, "", ...lines(items), "");
  return L;
}

/**
 * The report as markdown: the plain-language part first (`report_plain.ts`: what was wrong and what
 * was done, the clarifications, what Lean proves, the corrected paper), then the technical appendix
 * — every row, id, bucket and input the plain part is drawn from. Pure.
 */
export function renderReport(json: VerifyReportJson): string {
  const L: string[] = [];
  L.push(`# Correctness report ${DASH} ${json.run.qid}`, "");
  L.push(`**Verdict: ${VERDICT_TEXT[json.verdict]}**`, "");
  L.push(...renderGrade(json));
  L.push(...renderPlainSections(json));
  L.push("# Technical appendix", "");
  L.push("The records behind the report above, by the run's own identifiers.", "");
  L.push(
    `- paper: \`${json.run.main_file}\` (source sha256 \`${json.run.source_sha256}\`)`,
    `- stage completed: \`${json.run.stage_completed}\`${json.run.early_stop ? " (early stop: the run never reached Lean)" : ""}`,
    `- results in scope: ${json.results.length}`,
    "",
  );
  L.push("| bucket | count |", "| --- | --- |");
  for (const b of REPORT_BUCKETS) L.push(`| ${b} | ${json.summary[b]} |`);
  L.push("", `> ${json.disclaimer}`, "");

  L.push("## Results", "");
  if (json.results.length === 0) L.push("No theorem-like environment was in scope.", "");
  json.results.forEach((r, i) => {
    const heading = r.title ?? r.label ?? r.env_id;
    L.push(
      heading === r.node_id
        ? `### ${i + 1}. \`${r.node_id}\``
        : `### ${i + 1}. ${heading} \`${r.node_id}\``,
      "",
    );
    L.push("| field | value |", "| --- | --- |");
    L.push(`| bucket | \`${r.bucket}\` |`);
    L.push(
      `| source | \`${r.locator}\` (\`${r.kind}\`, label ${r.label ? `\`${r.label}\`` : DASH}) |`,
    );
    // What was actually claimed. Without it the row says a verdict about a result the reader
    // cannot see, and checking it against the paper means opening the paper at the locator.
    L.push(`| statement | ${cell(r.statement)} |`);
    if (r.appended_hypotheses) {
      L.push(`| appended hypothesis list | ${cell(r.appended_hypotheses)} |`);
    }
    L.push(
      `| Lean | ${r.lean ? `\`${r.lean.file}:${r.lean.line}\` ${DASH} \`${r.lean.decl}\`` : "no declaration anchored"} |`,
    );
    L.push(`| crosswalk verdict | ${r.crosswalk_verdict ? `\`${r.crosswalk_verdict}\`` : DASH} |`);
    L.push(`| axioms | ${cell(axiomText(r.axioms))} |`);
    L.push(
      `| V1.5 review | ${
        r.v1_5
          ? cell(
              `faithfulness ${r.v1_5.faithfulness} · ambiguity ${r.v1_5.ambiguity} · correctness ${r.v1_5.correctness}`,
            )
          : DASH
      } |`,
    );
    L.push(
      `| added conditions | ${cell(
        [
          ...r.bookkeeping.map((b) => `\`${b.id}\``),
          ...r.added_premises.map((p) => `\`${p.label}\``),
        ].join(", "),
      )} |`,
    );
    L.push(
      `| cited results | ${cell(
        r.cited_hypotheses.map((c) => `\`${c.id}\` (${c.cite}, ${c.locator})`).join("; "),
      )} |`,
    );
    L.push(
      `| assumed substrate gates | ${cell(r.assumed_substrate.map((g) => `\`${g.id}\``).join(", "))} |`,
    );
    L.push(`| findings | ${cell(r.findings.map(findingText).join(" ／ "))} |`);
    if (r.inherits_refutation_from.length > 0) {
      L.push(
        `| inherits refutation from | ${r.inherits_refutation_from.map((id) => `\`${id}\``).join(", ")} |`,
      );
    }
    if (r.rests_on_undetermined?.length) L.push(`| rests on (not determined) | ${r.rests_on_undetermined.map((id) => `\`${id}\``).join(", ")} |`);
    L.push("");
  });

  // What is actually wrong, at the root. A refuted result that rests on another refuted result
  // is listed under it, so the count of independent errors is visible at a glance.
  const refutedRows = json.results.filter((r) => r.findings.some(isPaperRefutation));
  if (refutedRows.length > 0) {
    const roots = refutedRows.filter((r) => r.inherits_refutation_from.length === 0);
    const refsOf = (r: ReportRow): VerifyFinding[] => r.findings.filter(isPaperRefutation);
    const descopedRoots = roots.filter((r) => refsOf(r).some((f) => f.descoped));
    const patched = roots.filter((r) => !descopedRoots.includes(r) && refsOf(r).every((f) => isRepaired(f)));
    const substantive = roots.filter((r) => !descopedRoots.includes(r) && !patched.includes(r));
    L.push("## Errors by root cause", "");
    L.push(
      `${roots.length} independent error(s) — ${patched.length} repaired by a minimal patch, ${substantive.length} not repaired, ` +
        `${descopedRoots.length} unfixable and left out of Lean; ${refutedRows.length - roots.length} result(s) inherit one.`,
      "",
    );
    const leanStatus = (r: ReportRow): string =>
      json.run.early_stop
        ? "not formalized yet (the run stopped before Lean)"
        : r.umbrella
          ? r.bucket === "repaired" ? "an umbrella: every proposition it is stated as is proved in Lean" : "an umbrella: NOT every proposition it is stated as is certified in Lean"
        : r.bucket === "repaired"
          ? "the corrected statement is proved in Lean"
          : "the corrected statement is NOT certified in Lean";
    const listRoot = (root: ReportRow): void => {
      const dependents = refutedRows.filter((r) => r.inherits_refutation_from.includes(root.node_id));
      const refs = refsOf(root);
      L.push(`- **\`${root.node_id}\`** (\`${root.locator}\`): ${line(refs.map((f) => f.detail).join(" ／ "))}`);
      for (const f of refs) if (f.witness) L.push(`  - witness: ${line(f.witness)}`);
      const ex = json.explanations?.[root.node_id];
      if (ex) for (const p of proseParts(ex)) L.push(`  - ${p.label}: ${line(p.text)}`);
      for (const f of refs) {
        if (!f.patch) continue;
        L.push(
          `  - repair ${f.patch.confirmed ? "confirmed by an independent referee pass" : "NOT confirmed: the confirming referee pass rejected it"}` +
            ` (see Corrected version); ${leanStatus(root)}`,
        );
        if (f.patch.confirmed && f.patch.corrected_statement) L.push(`  - corrected statement: ${line(f.patch.corrected_statement)}`);
        if (f.patch.narrowed) {
          L.push(
            f.patch.narrowed_by === "runner"
              ? `  - narrowed: ${line(f.patch.narrowed)} (an intermediate result: its strongest true version was applied automatically)`
              : `  - contribution narrowed: ${line(f.patch.narrowed)} (the owner accepted the weaker version)`,
          );
        }
      }
      for (const f of refs) if (f.suggested_repair) L.push(`  - ${suggestionLabel(f)}: ${line(f.suggested_repair)}`);
      if (dependents.length > 0) {
        L.push(`  - inherited by: ${dependents.map((d) => `\`${d.node_id}\``).join(", ")}`);
      }
    };
    if (patched.length > 0) {
      L.push("### Errors found — repaired", "");
      L.push(
        "The result as printed is false (the witness shows why). The smallest change that keeps the paper's key contribution was confirmed by an independent referee pass; the F stages formalize it in place of the printed statement.",
        "",
      );
      if (json.patch_review) L.push(`Key contribution, as judged by the confirming referee: ${line(json.patch_review.detail)}`, "");
      for (const root of patched) listRoot(root);
      L.push("");
    }
    if (substantive.length > 0) {
      L.push("### Not repaired", "");
      L.push("No confirmed repair: the result as printed is false and was not formalized.", "");
      for (const root of substantive) listRoot(root);
      L.push("");
    }
    if (descopedRoots.length > 0) {
      L.push("### Unfixable results (left out of Lean)", "");
      L.push(
        "No repair keeps the point of these results at full strength — or the owner declined the weaker version suggested. " +
          "They, and every result resting on them, were left out; the rest of the paper was formalized without them.",
        "",
      );
      for (const root of descopedRoots) listRoot(root);
      const withThem = json.results.filter((r) => !refutedRows.includes(r) && r.change?.descoped);
      if (withThem.length > 0) L.push(`- also left out of Lean (they rest on a result above): ${withThem.map((r) => `\`${r.node_id}\``).join(", ")}`);
      L.push("");
    }
  }

  // What could not be checked as printed: not errors — nothing here was shown false.
  const openRows = json.results.filter((r) => r.bucket === "not_determined");
  if (openRows.length > 0) {
    L.push("## Not determined", "");
    L.push(
      `${openRows.length} result(s) could not be checked as printed: the paper does not say enough to determine the claim, and no reading or repair was adopted. Nothing here was shown false; none was formalized.`,
      "",
    );
    for (const r of openRows) {
      const fs = r.findings.filter(isUndetermined);
      L.push(`- **\`${r.node_id}\`** (\`${r.locator}\`): ${line(fs.map((f) => f.detail).join(" ／ "))}`);
      for (const f of fs) if (f.witness) L.push(`  - witness against the repair tried (not against the printed statement): ${line(f.witness)}`);
      for (const f of fs) if (f.suggested_repair) L.push(`  - ${suggestionLabel(f)}: ${line(f.suggested_repair)}`);
      if (r.rests_on_undetermined?.length) L.push(`  - rests on (not determined): ${r.rests_on_undetermined.map((id) => `\`${id}\``).join(", ")}`);
    }
    L.push("");
  }

  // The corrected version: every result whose statement, hypotheses or proof the patches
  // changed, against the user's version. This is what the Lean formalization proves.
  const changed = json.results.filter((r) => r.change);
  if (changed.length > 0) {
    L.push("## Corrected version", "");
    // Three kinds of change: a REPAIR (the result had an error), a proof WRITTEN OUT (no error —
    // the referee could not check it as printed), a reading or side condition made explicit.
    const kind = (r: ReportRow): "repaired" | "written" | "reading" => {
      const c = r.change!;
      // (a statement made precise is no repair of an error: its reading was made explicit)
      if (r.findings.some((f) => f.kind === "refuted") || ((c.corrected || c.dropped_dependencies.length > 0) && !r.findings.some(isMadePrecise)) || c.descoped) {
        return "repaired";
      }
      return c.proof_change ? "written" : "reading";
    };
    const count = (k: string): number => changed.filter((r) => kind(r) === k).length;
    L.push(
      `${changed.length} of ${json.results.length} result(s) differ from the version you provided — ` +
        `${count("repaired")} repaired, ${count("written")} with the proof completed (no error), ` +
        `${count("reading")} only with a side condition or reading made explicit; ` +
        "the others are as printed. " +
        (json.run.early_stop
          ? "The corrected version is what the F stages formalize; this run stopped before Lean."
          : "The Lean formalization is of the corrected version."),
      "",
    );
    for (const r of changed) {
      const c = r.change!;
      L.push(`### \`${r.node_id}\` (\`${r.locator}\`)`, "");
      L.push(`- as printed: ${line(c.printed)}`);
      if (c.descoped) {
        L.push("- left out of the corrected version and of Lean: it cannot be repaired, or rests on a result that cannot.");
      } else {
        L.push(`- corrected: ${c.corrected ? line(c.corrected) : "statement unchanged"}`);
        if (r.umbrella) L.push(`- an umbrella over ${json.results.filter((x) => x.split_from === r.node_id).map((x) => `\`${x.node_id}\``).join(", ")}: no Lean declaration of its own, established exactly when all of them are`);
        if (kind(r) === "reading") L.push(r.findings.some(isMadePrecise) ? "- no error: the printed statement did not determine the claim; the reading adopted is stated, and a referee pass confirmed it" : "- no error: only a side condition or reading the referee made explicit (see below)");
        if (kind(r) === "written") L.push("- no error: the proof as printed could not be checked, so its steps were completed (below)");
      }
      for (const d of c.dropped_dependencies) L.push(`- no longer uses \`${d}\``);
      for (const h of c.referee_conditions) {
        L.push(`- side condition added by the confirming referee \`${h.id}\`: ${line(h.condition)} — ${line(h.reason)}`);
      }
      if (c.proof_change) L.push(`- proof change: ${line(c.proof_change)}`);
      const why = r.findings.filter((f) => f.kind === "refuted").map((f) => f.detail);
      if (why.length > 0) L.push(`- why: ${line(why.join(" ／ "))}`);
      L.push("");
    }
  }

  // Withdrawn by the owner: listed with the owner's reading, never as refuted or repaired.
  if ((json.withdrawn_findings ?? []).length > 0) {
    L.push("## Findings withdrawn by the owner", "");
    L.push("Not errors: the paper's owner showed each finding misreads the paper. The printed statement stands, under the owner's reading (or side condition), which the formalization adopts.", "");
    for (const w of json.withdrawn_findings!) {
      const what = w.pin?.startsWith("ass:bk-owner-") ? "the owner's side condition" : "the owner's reading";
      L.push(`- \`${w.node}\` (raised at ${w.stage}): ${what}${w.pin ? ` (\`${w.pin}\`)` : ""}: ${cell(w.reason)} — the withdrawn finding: ${cell(w.finding)}`);
    }
    L.push("");
  }

  // Suggestions to the authors: readings the referee had to pin, and conditions it had to add.
  // None of these is an error; each is something the paper could state.
  const pins = json.results.flatMap((r) =>
    r.bookkeeping.filter((b) => b.reason.startsWith("pins reading")).map((b) => ({ r, b })),
  );
  const conditions = json.results.flatMap((r) =>
    r.bookkeeping.filter((b) => !b.reason.startsWith("pins reading")).map((b) => ({ r, b })),
  );
  const pinNotes = json.unclear_notes.filter((n) => n.detail.startsWith("pinned reading:"));
  const symbolReadings = json.symbol_readings ?? [];
  if (pins.length + conditions.length + pinNotes.length + symbolReadings.length > 0) {
    L.push("## Suggestions to the authors", "");
    L.push("Not errors: readings the paper determines but does not state, and side conditions the proofs use silently.", "");
    const seenPin = new Set<string>();
    for (const { r, b } of pins) {
      if (seenPin.has(b.id)) continue;
      seenPin.add(b.id);
      L.push(`- clarification (\`${b.id}\`, used by \`${r.node_id}\`): ${cell(b.condition)} — ${cell(b.reason)}`);
    }
    for (const n of pinNotes) L.push(`- \`${n.node}\`: ${cell(n.detail)}`);
    for (const s of symbolReadings) L.push(`- reading of the symbol \`${s.symbol}\`: ${cell(s.reading)} — ${cell(s.evidence)}`);
    for (const { r, b } of conditions) {
      L.push(`- added condition (\`${b.id}\`, \`${r.node_id}\`): ${cell(b.condition)} — ${cell(b.reason)}`);
    }
    L.push("");
  }

  L.push("## Added conditions", "");
  const anyBk = json.results.some((r) => r.bookkeeping.length > 0);
  const premises = new Map<string, { premise: ReportRow["added_premises"][number]; where: string[] }>();
  for (const r of json.results) {
    for (const p of r.added_premises) {
      const e = premises.get(p.label) ?? { premise: p, where: [] };
      e.where.push(r.node_id);
      premises.set(p.label, e);
    }
  }
  if (!anyBk && premises.size === 0) {
    L.push("None: no condition was added to the paper's own hypotheses.", "");
  } else {
    L.push("| id | where | class | condition |", "| --- | --- | --- | --- |");
    for (const r of json.results) {
      for (const b of r.bookkeeping) {
        L.push(
          `| \`${b.id}\` | \`${r.node_id}\` | V1.5 bookkeeping | ${cell(`${b.condition} (${b.reason})`)} |`,
        );
      }
    }
    for (const [label, e] of premises) {
      L.push(
        `| \`${label}\` | ${cell(e.where.map((w) => `\`${w}\``).join(", "))} | ${cell(e.premise.classification ?? "unclassified")} | ${cell(e.premise.statement)} |`,
      );
    }
    L.push("");
  }

  L.push("## Conditions assumed", "");
  L.push("### Cited results", "");
  const cited = json.results.flatMap((r) =>
    r.cited_hypotheses.map((c) => ({ ...c, node: r.node_id })),
  );
  if (cited.length === 0) {
    L.push("None: no result rests on a theorem imported from the literature.", "");
  } else {
    L.push("| id | used by | citation | locator | checked against |", "| --- | --- | --- | --- | --- |");
    for (const c of cited) {
      L.push(
        `| \`${c.id}\` | \`${c.node}\` | ${cell(c.cite)} | ${cell(c.locator)} | ${cell(c.source_check ?? (c.unchecked_reason ? `**${c.unchecked_reason}**` : "NOT checked against its source"))} |`,
      );
    }
    L.push("");
    // What each stands for in the formalization: the Lean statement assumed, and the paper's passage.
    for (const c of new Map(cited.map((x) => [x.id, x] as const)).values()) {
      const shown = citedDisclosure(c);
      if (shown.length > 0) L.push(`\`${c.id}\` (${c.cite}, ${c.locator})${c.cited_in ? `, invoked in the proof of \`${c.cited_in}\`` : ""}:`, "", ...shown);
    }
  }
  L.push("### Deferred substrate gates", "");
  const gates = json.results.flatMap((r) =>
    r.assumed_substrate.map((g) => ({ ...g, node: r.node_id })),
  );
  if (gates.length === 0) {
    L.push("None: every substrate this run needed was built and proved.", "");
  } else {
    L.push(
      "These are dischargeable classical facts — not gaps in the paper — that a result still ASSUMES: " +
        "a gate the plan left unbuilt, or a hypothesis the proof stage added to the Lean statement and " +
        "the reviewers classed as such. Once a proof of it is in the toolkit, the result can be re-verified.",
      "",
    );
    L.push("| gate | used by | statement |", "| --- | --- | --- |");
    for (const g of gates) {
      L.push(`| \`${g.id}\` | \`${g.node}\` | ${cell(g.description)} |`);
    }
    L.push("");
  }

  L.push("## Unresolved / notes", "");
  const open = json.results.filter(
    (r) => r.bucket === "unresolved" || r.bucket === "not_checked" || r.bucket === "refuted" || r.bucket === "not_determined",
  );
  const warnings = json.v1_warnings;
  if (
    open.length === 0 &&
    json.run_level_findings.length === 0 &&
    json.unclear_notes.length === 0 &&
    warnings.lint.length === 0 &&
    warnings.parser.length === 0
  ) {
    L.push("None.", "");
  } else {
    for (const r of open) {
      const why =
        r.findings.length > 0
          ? r.findings.map(findingText).join(" ／ ")
          : r.bucket === "not_checked"
            ? "the run stopped before the Lean formalization"
            : !r.lean
              ? "no Lean declaration was anchored to it"
              : !crosswalkCertifies(r.crosswalk_verdict)
                ? `the Lean declaration does not state this result (crosswalk verdict \`${
                    r.crosswalk_verdict ?? "none"
                  }\`), so its proof certifies nothing about it`
                : "the Lean evidence did not certify it (see Lean evidence below)";
      L.push(`- \`${r.node_id}\` (${r.bucket}, \`${r.locator}\`): ${cell(why)}`);
    }
    for (const f of json.run_level_findings) L.push(`- run-level \`${f.node}\`: ${cell(findingText(f))}`);
    for (const n of json.unclear_notes) L.push(`- note on \`${n.node}\`: ${cell(n.detail)}`);
    L.push("");
    // V1's own observations. Neither list is a verdict about the paper: the lint warnings are
    // transcription questions the V1.5 referee was asked to settle, the parser warnings are what
    // the mechanical read of the source tree had to decide. Both are disclosed so a reader can
    // check the report's premises rather than trust them.
    if (warnings.lint.length > 0) {
      L.push("### V1 lint warnings", "");
      for (const w of warnings.lint) L.push(`- ${cell(w)}`);
      L.push("");
    }
    if (warnings.parser.length > 0) {
      L.push("### Parser warnings", "");
      for (const w of warnings.parser) L.push(`- ${cell(w)}`);
      L.push("");
    }
  }
  if (json.flags.verify_no_d_rewind) {
    L.push(`Refused rewind: ${cell(json.flags.verify_no_d_rewind)}`, "");
  }

  L.push("## Lean evidence", "");
  if (!json.lean_build) {
    L.push(`Not collected: ${json.inputs.lean_evidence}`, "");
  } else {
    L.push(`- build of the run barrel: **${json.lean_build.ok ? "ok" : "FAILED"}**`);
    L.push(
      `- source scan (sorry / admit / axiom): ${
        (json.sorry_scan ?? []).length === 0
          ? "clean"
          : `${(json.sorry_scan ?? []).length} issue(s)`
      }`,
      "",
    );
    for (const issue of json.sorry_scan ?? []) L.push(`  - ${cell(issue)}`);
    if ((json.sorry_scan ?? []).length > 0) L.push("");
    if (!json.lean_build.ok && json.lean_build.log_tail.trim().length > 0) {
      L.push("```", json.lean_build.log_tail, "```", "");
    }
    L.push("| declaration | axioms |", "| --- | --- |");
    for (const r of json.results) {
      if (!r.lean) continue;
      L.push(`| \`${r.lean.decl}\` | ${cell(axiomText(r.axioms))} |`);
    }
    L.push("");
  }

  L.push("## Inputs", "");
  L.push("| artifact | status |", "| --- | --- |");
  L.push(`| \`discovery/v1_scope.json\` | ${cell(json.inputs.v1_scope)} |`);
  L.push(`| \`discovery/v1_5_review.json\` | ${cell(json.inputs.v1_5_review)} |`);
  L.push(`| \`formalization/crosswalk_full.json\` | ${cell(json.inputs.crosswalk_full)} |`);
  L.push(`| \`graph.json\` | ${cell(json.inputs.graph_json)} |`);
  L.push(`| Lean evidence | ${cell(json.inputs.lean_evidence)} |`);
  L.push("");

  const a = json.annotated as { tex?: string; pdf?: string | null; index?: string; annotations?: number; unlocated?: number; compile?: { status?: string; note?: string }; error?: string } | undefined;
  if (a) {
    L.push("## Annotated paper", "");
    L.push(
      a.error
        ? `Annotated paper: not written (${a.error}).`
        : `Annotated paper: \`${a.tex}\` (${a.annotations} annotation(s), ${a.unlocated} unlocated; index \`${a.index}\`)` +
            (a.pdf ? `; PDF: \`${a.pdf}\`` : a.compile?.note ? `; note: ${a.compile.note}` : a.compile?.status === "failed" ? "; compiling it failed (see the index)" : "; not compiled (no TeX compiler on PATH)"),
      "",
    );
  }

  return L.join("\n");
}
