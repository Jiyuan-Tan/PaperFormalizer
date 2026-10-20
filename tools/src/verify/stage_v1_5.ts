/**
 * V1.5 — faithfulness / ambiguity / correctness review of the V1 core (M3).
 *
 * The referee (`referee_shards.ts`: shards in dependency order, then one global pass) grades every
 * node of the typed core on three axes. The stage is the run's only correctness gate before Lean:
 *
 *   PASS    every `bookkeeping_assumption` is applied to the core as an `ass:bk-<n>`
 *           node wired into the statement that needs it, the structural gate is re-run,
 *           `state.verify.core_sha256` is stamped, `stage_completed` becomes "V1.5", and
 *           F1 may enter.
 *   REVISE  `drift` nodes are written to `discovery/v1_revise_directive.json`
 *           and the runner re-enters V1 (bounded per drifting node by `MAX_REVISE_ROUNDS_PER_NODE`).
 *   FAIL    an `error` node with a witness (or an unresolvable ambiguity): a patch round (V1 patch
 *           mode); a `refuted` finding per node and a jump to V6 only when the patch loop ends with
 *           the error left (`recordFailure`).
 *
 * The verdict is COMPUTED here from the node grades, never taken from the model: a
 * referee that grades one node `error` and then writes `"verdict": "PASS"` must not be
 * able to talk the runner past a refutation. `bookkeeping` never blocks (it is disclosed in the
 * report); an `unclear` step goes to V1 patch mode to be written out in full (see
 * `V15NodeVerdict`).
 *
 * CARRIED VERDICTS (a re-review grades only the delta):
 * every verdict is stored with its BASIS (`core_graph.ts` `basisInputs`: what the node's referee is
 * shown — the node, the text of what it uses directly, the verdict of each result it uses, the
 * symbol-table entries those name, the cited source, the symbol readings binding them). At entry the runner computes the basis of every node of
 * the rebuilt core; a node whose basis matches the clean (`ok` / `bookkeeping`) verdict recorded
 * in `state.verify.confirmed` keeps that verdict (`graded: "carried"`), and only the rest go to
 * the referee. A changed node is never served from the cache; a carried verdict using a result whose
 * verdict changes in the pass is re-opened in that pass (`partitionByBasis`). `--fresh-review` clears the cache.
 *
 * SYMBOL REFEREE (`referee_symbols.ts`), FIRST: every symbol of the table is read against where the
 * paper introduces and uses it, in shards. Its fixes
 * are written into the symbol table and its pinned readings bind every statement using the symbol
 * before any node is graded; its verdicts are cached like node verdicts (`v1_5_symbols.json`).
 *
 * THE REFEREE (`referee_shards.ts`): levels in dependency order (leaves first), each split into
 * shards sized by content, each node graded once under the final verdicts of what it uses, one
 * global pass for what spans nodes; the merged review goes through everything below.
 * FIX AS YOU GO: a settled level with a node the fixer or the owner must answer (`pauseRule`)
 * pauses the upward grading; the partial review is routed like a full one but hands on exactly those
 * nodes (a patch round, a weakening halt, a cap halt), `state.verify.level_pause` records where, and
 * the next pass carries that pass's verdicts, confirms the repair first and continues upward.
 */
import { existsSync } from "node:fs";
import { createHash } from "node:crypto";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import { ORPHANED_RECORDS_FILE, type OrphanedRecord } from "./orphan_records.js";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { saveState } from "../state.js";
import { parseTypedCore } from "../core/core_io.js";
import { runStructuralGate } from "../core/gate.js";
import type { Core, CoreStatement } from "../core/schema.js";
import { MODELS } from "../models.js";
import { expectStringJsonOutput, persistCodexRaw } from "../shared/codex_json.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import type { StateJson } from "../types.js";
import { NOTE_LOSS_WARNING } from "./note_macros.js";
import { sha256File, writeCoreJson } from "./core_hash.js";
import { BASIS_SCHEME, CoreGraphInputError, DERIVED_USER_FIELDS, SYMBOL_PIN_OF, applicableClauses, basisInputs, basisInputsV4, basisOf, bindingReadings, buildCore, isUmbrellaPatch, mergeBasisExtra, regradeCause, symbolUsers, symbolsUsedByNode, type BasisExtra, type BasisExtraValue, type BasisInputs, type RegradeCause, type SymbolReadingBasis } from "./core_graph.js";
import { normalizeBasisText } from "./basis_text.js";
import { hasDriftFix, type DriftFix } from "./directive_edits.js";
import { openFindingKind, recordVerifyFinding } from "./findings.js";
import {
  descopedStatements,
  findingPatch,
  readPatchFile,
  readSymbolFixes,
  readTranscribedCore,
  blockedUnfixable,
  rebuildPatchedCore,
  validatePatchFile,
  withoutMootDrops,
  type PaperErrors,
  type PatchFile,
  isPendingSuggestion,
  isWithdrawn,
  openErrorIds,
  suggestionText,
  repairSources,
  unresolvedRepairs,
  overlapViolations,
  applySuggestions,
  corollaryNodes,
  onSplitParent,
  splitCorollaries,
} from "./patches.js";
import { governByOwnerRulings, ownerRuling } from "./owner_rulings.js";
import { hypothesisRepairLine, hypothesisUsers } from "./cross_stage_rewind.js";
import { FIXER_INSTRUCTIONS, hasExplanation, isStructuredExplanation, renderExplanation, texEscapeProblems, type OwnerExplanationField, type QuoteOf } from "./owner_text.js";
import { isStatementOp, nodePassage, revisesProof } from "./ops.js";
import { texFieldViolations, type TexCheckContext } from "./tex_fragment_check.js";
import { convertWeakeningPatches, settleSuggestions, weakeningDetail, withdrawSuggestions, withdrawnRepair, type WithdrawnRepair } from "./weakening.js";
import { CITED_SOURCES_DIR, resolveCitedSources, settleUnavailableCited, sourceFileKey, UNAVAILABLE_SUFFIX, type CitedSource } from "./cited_sources.js";
import { readV1Warnings, type V1Warnings } from "./lint_warnings.js";
import { repairCitationWarnings } from "./inline_citations.js";
import {
  VERIFY_FILES,
  type EnvsJson,
  type TexLocator,
  type V15NodeVerdict,
  type V15Review,
  type V15SymbolVerdict,
  type FindingPatch,
  type VerifyFinding,
  type VerifyStage,
  type VerifyStageArgs,
  type VerifyState,
  type VerifyStageResult,
  type FixerRejection,
  type FlatTexLineMap,
  type LevelPause,
  type PatchRoundKind,
  MAX_REVISE_ROUNDS_PER_NODE,
  MAX_SUGGESTION_REJECTIONS,
} from "./types.js";
import { atCap, capRecord, errorScope, nextRound, patchBackstop, roundsUsed } from "./caps.js";
import {
  DEFAULT_SHARD_LIMITS,
  GLOBAL_OUTPUT_BLOCK,
  dependencyLine,
  isRefutingError,
  runShardedReferee,
  settleDegenerateWitness,
  shardLogLine,
  syntheticAsk,
  type RefereeCall,
  type ShardedPause,
  type ShardedRefereeInput,
  type ShardedResult,
  type ShardMetrics,
} from "./referee_shards.js";
import type { DependencyVerdict } from "./referee_levels.js";
import { nodeExcerpts, paperIndex, type PaperIndex } from "./referee_slices.js";
import { PROMPT_INPUT_MAX } from "../shared/prompt_budget.js";
import { globalBriefOf, globalCoreText, globalPaperExcerpts, openSymbolsSection, proofChange, symbolsUsedBy, verdictLine, type SymbolReadings } from "./referee_shard_prompts.js";
import { correctionTouchesSymbol, resultsNamedBy, runSymbolPass, symbolLogLine, syntheticSymbolAsk, type SymbolMetrics } from "./referee_symbols.js";
import { appendPipelineLog } from "../log.js";

const PROMPT_DIR = path.join(path.dirname(fileURLToPath(import.meta.url)), "prompts", "V1.5");
const PROMPT_FILE = path.join(PROMPT_DIR, "review.txt");

/**
 * Persist the prompt of one live referee call as `discovery/prompts/v1_5_<tag>__<stamp>.txt` (its
 * reply goes to `codex_raw/` under the same tag), before the call — so what a referee was shown is
 * on disk, never reconstructed. Best effort: returns the path, or null when the write fails.
 */
export async function persistRefereePrompt(runDir: string, tag: string, prompt: string): Promise<string | null> {
  try {
    const dir = path.join(runDir, VERIFY_FILES.v15Prompts);
    await mkdir(dir, { recursive: true });
    const safeTag = `v1_5_${tag}`.replace(/[^A-Za-z0-9._-]+/g, "_").slice(0, 80);
    const stamp = new Date().toISOString().replace(/[:.]/g, "-");
    // Two tags can sanitize alike (`\Delta`, `\Delta'`) and start in the same millisecond: never overwrite.
    for (let n = 1; n <= 50; n += 1) {
      const file = path.join(dir, `${safeTag}__${stamp}${n > 1 ? `-${n}` : ""}.txt`);
      try {
        await writeFile(file, prompt, { encoding: "utf8", flag: "wx" });
        return file;
      } catch (err) {
        if ((err as NodeJS.ErrnoException).code !== "EEXIST") throw err;
      }
    }
    return null;
  } catch {
    return null;
  }
}

function section(header: string, body: string): string {
  return `=== ${header} ===\n\n${body}`;
}

interface PromptInputs {
  base: string;
  flatTex: string;
  targets: string[] | null;
  lintWarnings: V1Warnings;
  patches?: PatchFile | null;
  /** The paper-error ledger (`state.verify.paper_errors`). */
  paperErrors?: PaperErrors;
  /** The source of every cited result (never the paper's own quote). */
  citedSources?: CitedSource[];
  /** The printed statement of each patched node (from the transcribed core). */
  printed?: Map<string, string>;
  /** The printed text of each assumption and definition (from the transcribed core): the hypotheses a
   * repair drops or adds are shown with it. */
  hypotheses?: Map<string, string>;
  /** F-stage findings the fixer rejected, for this pass to rule on. */
  rejections?: FixerRejection[];
  /** The symbol referee's readings (PINNED READINGS, right after the core). */
  symbolReadings?: SymbolReadings;
  /** The texts on file of the nodes to grade that do not compile against the paper's preamble, one
   * line per text with the compiler's line (`storedTexFeedback`). */
  texFeedback?: ReadonlyArray<{ node: string; line: string }>;
  /** Errors recorded on an earlier transcription of a node to grade, set aside when a re-transcription
   * left them no single carrier (`orphan_records.ts`): re-checked against the node as it stands. */
  priorErrors?: ReadonlyArray<{ node: string; line: string }>;
  /** The conditions an earlier pass appended to the nodes to grade (`priorConditionLines`). */
  priorConditions?: ReadonlyArray<{ node: string; line: string }>;
  /** The paper's units, for the steps a fixer note quotes (`patchesSection`). */
  quoteOf?: QuoteOf;
}

/**
 * The texts the referee wrote on file for `ids` — the prior review's detail, reading and bookkeeping
 * condition — that do not compile against the paper's preamble:
 * one line per text, with the compiler's line (`refereeTexViolations`). A node re-opened because its
 * text does not compile (`fragment_routing.ts`) gets it in the prompt that grades it afresh. Empty
 * without a check context.
 */
export async function storedTexFeedback(ids: readonly string[], prior: V15Review | null, ctx: TexCheckContext | null): Promise<Array<{ node: string; line: string }>> {
  if (!ctx) return [];
  const out: Array<{ node: string; line: string }> = [];
  for (const id of ids) {
    const n = prior?.nodes.find((x) => x.id === id);
    for (const line of [...new Set(n ? await refereeTexViolations([n], ctx) : [])]) out.push({ node: id, line });
  }
  return out;
}

/** The errors recorded on an earlier transcription of the nodes to grade (`orphaned_records.json`),
 * one line per error on each node now printing that text. Empty without the file. */
export async function priorErrorLines(runDir: string, toGrade: readonly string[]): Promise<Array<{ node: string; line: string }>> {
  const p = path.join(runDir, ORPHANED_RECORDS_FILE);
  if (!existsSync(p)) return [];
  const records = JSON.parse(await readFile(p, "utf8")) as OrphanedRecord[];
  const grade = new Set(toGrade);
  return records.flatMap((r) => {
    const e = r.paper_error as { detail?: string; witness?: string | null } | null;
    if (!e?.detail) return [];
    return r.candidates.filter((c) => grade.has(c)).map((node) => ({ node, line: `${node}: found on ${r.node} (an earlier transcription of this result): ${e.detail}${e.witness ? ` Witness: ${e.witness}` : ""}` }));
  });
}

/** The ERRORS RECORDED ON AN EARLIER TRANSCRIPTION section; `ids` given (a shard): only those nodes'. */
function priorErrorsSection(pe: PromptInputs["priorErrors"], ids?: readonly string[] | null): string[] {
  const shown = (pe ?? []).filter((x) => !ids || ids.includes(x.node));
  return shown.length > 0
    ? [
        section(
          "ERRORS RECORDED ON AN EARLIER TRANSCRIPTION (check each)",
          "Each error below was found on an earlier transcription of a result you grade, before it was re-transcribed. " +
            "Decide whether it holds of the node as it stands now: if it does, grade the node `error` on it; if it does not, say why in the detail.\n\n" +
            shown.map((x) => `- ${x.line}`).join("\n"),
        ),
      ]
    : [];
}

/** The TEXTS ON FILE THAT DO NOT COMPILE section; `ids` given (a shard): only those nodes' lines. */
function texFeedbackSection(fb: PromptInputs["texFeedback"], ids?: readonly string[] | null): string[] {
  const shown = (fb ?? []).filter((x) => !ids || ids.includes(x.node));
  return shown.length > 0
    ? [
        section(
          "TEXTS ON FILE THAT DO NOT COMPILE (write these afresh so they compile)",
          "Your earlier texts below for nodes you grade do not compile as LaTeX against the paper's preamble " +
            "(the compiler's line is given). Every text you write this time must compile.\n\n" +
            shown.map((x) => `- ${x.line}`).join("\n"),
        ),
      ]
    : [];
}

function scopeLine(targets: string[] | null): string {
  return targets?.length
    ? `Operator scope: the paper results selected with --targets (${targets.join(", ")}); ` +
        "V1 already restricted the core to them."
    : "Operator scope: every theorem-like environment of the paper.";
}

/** Where the paper states and proves the nodes `ids`, as a parser warning names a result: `(file:from-to)`. */
export function sourcePlaces(core: Pick<Core, "statements" | "assumptions" | "definitions">, envs: EnvsJson | null | undefined, ids: readonly string[]): string[] {
  const key = (l: { file: string; from: number; to: number } | null | undefined): string[] => (l ? [`(${l.file}:${l.from}-${l.to})`] : []);
  const nodes = [...core.statements, ...(core.assumptions ?? []), ...(core.definitions ?? [])].filter((n) => ids.includes(n.id));
  return nodes.flatMap((n) => {
    const at = key(n.tex_locator)[0];
    const env = at ? envs?.envs.find((e) => key(e.lines)[0] === at) : undefined;
    return [...key(n.tex_locator), ...key(env?.proofLines)];
  });
}

/** The V1 warnings section. `ids` given (a shard): only the lint lines about those nodes (a line
 * opening `<id>: `; a line without that prefix, when it names one) and the parser's notes of text
 * removed from them;
 * `allIds` (the global pass): the parser notes and the lint lines naming no node of `allIds`;
 * neither: everything. */
export function warningsSection(w: V1Warnings, sel: { ids?: readonly string[]; allIds?: ReadonlySet<string>; places?: readonly string[] } = {}): string[] {
  const names = (line: string, ids: Iterable<string>): boolean => [...ids].some((id) => line.includes(id));
  // A lint line opens with the node it is about (`<id>: …`); a shard gets the lines about its nodes,
  // not every line that mentions one of them in passing (a line without that prefix: any mention).
  const about = (line: string, ids: readonly string[]): boolean => {
    const head = /^([a-z]+:[^\s:]+): /i.exec(line)?.[1];
    return head !== undefined ? ids.includes(head) : names(line, ids);
  };
  const lint = sel.ids ? w.lint.filter((l) => about(l, sel.ids!)) : sel.allIds ? w.lint.filter((l) => !names(l, sel.allIds!)) : w.lint;
  // … and the parser's notes of text removed from the results it grades (`places`: their `(file:from-to)`).
  const parser = sel.ids ? w.parser.filter((l) => l.startsWith(NOTE_LOSS_WARNING) && (sel.places ?? []).some((p) => l.includes(p))) : w.parser;
  const warningBody = [
    lint.length
      ? "The mechanical transcription lint could not settle these against the paper:\n" +
        lint.map((x) => `- ${x}`).join("\n")
      : "",
    parser.length
      ? "The LaTeX parser noted these about the source tree; say whether either changes what a " +
        "node means:\n" +
        parser.map((x) => `- ${x}`).join("\n")
      : "",
  ]
    .filter(Boolean)
    .join("\n\n");
  return warningBody
    ? [
        section(
          "V1 LINT WARNINGS (confirm each)",
          "Each line below is an OBSERVATION, not a defect: confirm or dismiss it on the node it " +
            "names, and say which in that node's `detail`.\n\n" +
            warningBody,
        ),
      ]
    : [];
}

/**
 * The PATCHES section; `ids` given (a shard): only the patches touching those
 * nodes (repairing them, or restating a hypothesis among them), and only their `unfixable` entries; a patch's `printed` statement is left out when
 * `printedShown(node)` (the prompt already carries that node's excerpt as printed). A shard sees each
 * fixer note as the author reads it (`renderExplanation`), the text its clarity is graded on; the
 * global pass, which grades no note, sees none (`global`: a delta global pass's `ids`, with the
 * key-result list it judges).
 *
 * What the core already carries travels once: a patch's `ops` and `corrected_statement` are the
 * patched node's text in the core, and a corollary's `follows` is its node's `proof_tex` — neither is
 * repeated here (the whole file is `discovery/patches.json`). The global pass, which judges the
 * key results and the consistency of the repair set, not a repair's proof or its ledger, sees no
 * `proof_note` and no `repairs` either. A shard whose record of the patched node carries the proof change
 * (`proofChangeOf(node)`: `compactCore`'s `proof_change`) sees no `proof_note` it holds word for word.
 *
 * A shard grading only a hypothesis or result a repair restates or no longer uses (`supersedes`,
 * `drops`) — not the repaired node, nor a corollary it splits off — judges no part of that repair: it
 * is told that the node's repair restates or drops its nodes (the missing edge is no drift), no more.
 */
export function patchesSection(
  args: PatchInputs,
  ids?: readonly string[],
  printedShown: (id: string) => boolean = () => false,
  global = false,
  proofChangeOf: (id: string) => string | null = () => null,
  carried: readonly string[] = [],
): string[] {
  const shown = patchesShown(args, ids, printedShown, global, proofChangeOf, carried);
  if (shown === null) return [];
  return [
    section(
      "PATCHES (discovery/patches.json — applied to the core above)",
      "Minimal repairs of errors a previous referee pass found. Judge them as the PATCHES rule " +
        "of the brief says. Nodes listed under `unfixable` were left out of the core. A patched node's corrected " +
        "text and proof change are its record in the core; a corollary's proof is its node's `proof_tex`." +
        (ids ? (global ? " The patches touching the nodes shown in full are listed whole. Every other repair is one line marked `carried: true` — what it gives up, whether that weakening was accepted, whether it changes the printed statement — its corrected text is the node's text in the core, and discovery/patches.json holds it whole (look it up by `node`). Judge the key-result list on all of them." : " Only the patches touching the nodes you grade are shown (a repair of another node that restates or drops one of yours: by those lists alone); the key-result list is judged by the global pass.") : "") +
        "\n\n" +
        JSON.stringify(shown),
    ),
  ];
}

/** What the PATCHES section reads of the run. */
export type PatchInputs = Pick<PromptInputs, "patches" | "printed" | "hypotheses" | "paperErrors" | "quoteOf">;

/** The PATCHES section's content (`patchesSection`, same arguments), or null when it has nothing to
 * show: the ONE place that decides what of the patch file a call is shown — a shard's section and the
 * verdict basis of each of its nodes (`repairBasis`) are both this. */
export function patchesShown(
  args: PatchInputs,
  ids?: readonly string[],
  printedShown: (id: string) => boolean = () => false,
  global = false,
  proofChangeOf: (id: string) => string | null = () => null,
  carried: readonly string[] = [],
): Record<string, unknown> | null {
  const file = args.patches;
  if (!file || (file.patches.length === 0 && file.unfixable.length === 0)) return null;
  // THE GLOBAL PASS judges the key-result list and the contribution the repairs keep whatever it
  // checks this time (`patch_review` is owed whenever the core carries patches): it is always shown
  // the list, and — beside the patches touching the nodes in full (`ids`) — one line for EVERY other
  // repair, wherever its node is, with what that judgement reads of a repair: an accepted loss on a
  // node that is neither a key result nor shown is a loss of the paper all the same.
  const keyLine = (p: PatchFile["patches"][number]): Record<string, unknown> => ({
    node: p.node,
    carried: true,
    changes_printed_statement: typeof p.corrected_statement === "string",
    ...(p.accepted_weakening !== undefined ? { accepted_weakening: p.accepted_weakening } : {}),
    ...(p.given_up !== undefined ? { given_up: p.given_up } : {}),
    ...(p.corollaries?.length ? { corollaries: corollaryNodes(p.node, p).map((c) => c.id) } : {}),
  });
  const byLine = (_p: PatchFile["patches"][number]): boolean => global && !!ids;
  // A patch touches a node it repairs, and a hypothesis it restates (`supersedes`, `drops`).
  // … and a corollary it splits off (graded as a node of its own, with the repair that wrote it).
  const touches = (p: PatchFile["patches"][number]): boolean => !ids || [p.node, ...(p.supersedes ?? []), ...(p.drops ?? []), ...corollaryNodes(p.node, p).map((c) => c.id)].some((n) => ids.includes(n));
  const shown = file.patches.filter((p) => touches(p) || byLine(p));
  if (ids && !global && shown.length === 0) return null;
  // A shard grades each note's clarity, shown as the author reads it; the global pass grades none.
  const note = <T extends { owner_explanation?: OwnerExplanationField | null }>(x: T): T => {
    if (!ids || global) return (({ owner_explanation: _o, ...r }) => r as T)(x);
    return isStructuredExplanation(x.owner_explanation) ? { ...x, owner_explanation: renderExplanation(x.owner_explanation, { quoteOf: args.quoteOf }) } : x;
  };
  /** A repair body without the texts the core carries (`ops`, `corrected_statement`; the global pass: `proof_note` too). */
  const body = <T extends { node: string; ops?: unknown; corrected_statement?: unknown; proof_note?: unknown }>({ ops: _o, corrected_statement: _c, ...rest }: T): Omit<T, "ops" | "corrected_statement"> =>
    global || (typeof rest.proof_note === "string" && proofChangeOf(rest.node)?.includes(rest.proof_note)) ? (({ proof_note: _p, ...r }) => r as Omit<T, "ops" | "corrected_statement">)(rest) : rest;
  /** The nodes of the shard a repair it does not grade restates or drops, or null (the shard grades the repair). */
  const onlyRestated = (p: PatchFile["patches"][number]): { node: string; supersedes?: string[]; drops?: string[] } | null => {
    if (!ids || global || [p.node, ...corollaryNodes(p.node, p).map((c) => c.id)].some((n) => ids.includes(n))) return null;
    const mine = (xs: readonly string[] | null | undefined): string[] => (xs ?? []).filter((n) => ids.includes(n));
    return { node: p.node, ...(mine(p.supersedes).length ? { supersedes: mine(p.supersedes) } : {}), ...(mine(p.drops).length ? { drops: mine(p.drops) } : {}) };
  };
  /** The ledger entry a repair answers, without the owner's decision on the repair and its reason
   * (`owner_decision`, `decision_reason`: the run's record — an accepted weakening is the patch's own
   * `accepted_weakening`), so ACCEPTING or DECLINING a repair re-opens no verdict by itself. Every
   * other field is shown and keyed: a redo (`guidance`) and a withdrawn finding (`owner_overruled`)
   * change what the node's shard shows, and re-open it. */
  const finding = (e: PaperErrors[string] | undefined): unknown => (e ? (({ owner_decision: _d, decision_reason: _r, ...rest }) => rest)(e as PaperErrors[string] & { owner_decision?: unknown; decision_reason?: unknown }) : null);
  return {
    // A shard does not judge the key-result list (the global pass does).
    ...(ids && !global ? {} : { key_results: file.key_results, key_contribution: file.key_contribution }),
    patches: shown.map((p) => (touches(p) ? null : keyLine(p)) ?? onlyRestated(p) ?? ({
      ...body(note(p)),
      // Each corollary with the id it is graded under (its proof is the node's `proof_tex`).
      ...(p.corollaries?.length ? { corollaries: corollaryNodes(p.node, p).map(({ follows: _f, ...c }) => c) } : {}),
      // The nodes the corrected result no longer uses, each with its printed text.
      ...(p.drops?.length ? { drops: p.drops.map((id) => ({ id, printed: args.hypotheses?.get(id) ?? args.printed?.get(id) ?? null })) } : {}),
      ...(p.adds?.length ? { adds: p.adds.map((id) => ({ id, printed: args.hypotheses?.get(id) ?? null })) } : {}),
      // (left out when the node's text is shown beside it; in a global prompt over its budget, everywhere:
      // the paper prints it)
      ...((ids || global) && printedShown(p.node) ? {} : { printed: args.printed?.get(p.node) ?? null }),
      ...(global ? {} : { repairs: finding(args.paperErrors?.[p.node]) }),
    })),
    // A suggested repair is not in the core: its entry travels whole.
    unfixable: (ids ? file.unfixable.filter((u) => ids.includes(u.node) || (global && (file.key_results.includes(u.node) || carried.includes(u.node)))) : file.unfixable).map(({ consequence_of: _c, consequence_reason: _cr, ...u }) => note(u)),
  };
}

/** A shard's PATCHES arguments for its nodes `ids`: each node it grades is printed as the paper
 * prints it (when located) and carries its proof change in its record (`compactCore`). */
export function shardPatchArgs(core: Core, px: PaperIndex, ids: readonly string[]): [(id: string) => boolean, false, (id: string) => string | null] {
  return [(id) => ids.includes(id) && nodeExcerpts(px, core, id).statement.range !== null, false, (id) => (ids.includes(id) ? proofChange(core.statements.find((st) => st.id === id)?.proof_tex) : null)];
}

/**
 * The repairs a node's shard shows it, as material of the node alone (`basisInputs` `own`): per node,
 * exactly what `patchesShown` gives a shard grading it — the body of each repair of it, of the result
 * it was split off (its sibling blocks with it), the ledger entry and fixer note shown with it, the
 * line saying a repair restates or drops it, a suggestion on it. (A node graded in ONE shard with
 * the node whose repair restates or drops it is shown that repair whole, and keyed on the line: the
 * line's content — which node's repair, which of the lists names it — is in the body shown, and the
 * rest of the body is the repaired node's own material, graded in the same call and keyed there.)
 * A change of any of it re-grades the
 * nodes shown it, never the results using them. No entry for a node shown no repair.
 */
export function repairBasis(args: PatchInputs, core: Core, px: PaperIndex): Map<string, string> {
  const out = new Map<string, string>();
  if (!args.patches) return out;
  for (const n of [...core.statements, ...core.assumptions, ...core.definitions]) {
    const shown = patchesShown(args, [n.id], ...shardPatchArgs(core, px, [n.id]));
    if (shown !== null && ((shown.patches as unknown[]).length > 0 || (shown.unfixable as unknown[]).length > 0)) out.set(n.id, JSON.stringify(shown));
  }
  return out;
}

/** The CITED SOURCES section; `ids` given (a shard): only those nodes' sources. */
function citedSection(sources: CitedSource[] | undefined, ids?: readonly string[]): string[] {
  const shown = (sources ?? []).filter((c) => !ids || ids.includes(c.nodeId));
  return shown.length > 0
    ? [
        section(
          "CITED SOURCES (the cited works themselves — never the paper's quotation of them)",
          shown
            .map((c) =>
              c.mode === "unavailable"
                ? `### ${c.nodeId} — ${c.key} @ ${c.locator}\n${c.text}\nThe cited work could not be accessed, so ` +
                  "check (1) cannot be made: do NOT grade this node `unclear` for want of its source. Grade it `error` only " +
                  "when the statement as the paper prints it is false (exhibit the witness); otherwise `ok`. Check (2), the " +
                  "use, as for any cited result."
                : `### ${c.nodeId} — ${c.key} @ ${c.locator}\n(${c.detail})\n\n${c.text}`,
            )
            .join("\n\n"),
        ),
      ]
    : [];
}

function rejectionsSection(rejections: FixerRejection[] | undefined): string[] {
  return (rejections ?? []).length > 0
    ? [
        section(
          "FIXER REJECTIONS (rule on each in `rejection_verdicts`)",
          "A Lean-stage reviewer found that each statement below lacks a hypothesis, is wrong as stated, or " +
            "admits several readings. The fixer declined to patch it: it says the paper already grants what the " +
            "finding says is missing. Check the finding against the paper and the fixer's pointer. Uphold the " +
            "rejection only when the paper really grants it; otherwise the fixer must patch.\n\n" +
            JSON.stringify(
              rejections!.map((r) => ({ node: r.node, from_stage: r.from_stage, axis: r.axis, finding: r.finding, fixer_reason: r.reason, where_the_paper_grants_it: r.where_the_paper_grants_it })),
              null,
              2,
            ),
        ),
      ]
    : [];
}

/** The global pass's prompt: its brief and `base`, the compact core (its symbol table in the shorter of
 * its two forms: per shown node, or each clause once), the shard verdicts, the paper, the cited sources, the patches, the fixer rejections and the
 * warnings. A delta pass (`scope`) shows only the nodes of `scope.ids`: those it checks (`scope.full`)
 * with their patches and sources and — when `scope.paper` is given — their excerpts in place of the
 * whole paper; the carried neighbours by text, wiring and verdict line alone (`globalCoreText`).
 * Over the budget one call may hold, in turn: the patches leave out each repaired node's printed text
 * (the paper prints it), then the paper is handed over by file (the call reads the run directory):
 * `GLOBAL_BY_FILE`. (The core is never handed over by file: a pass confirming suggestions grades a core
 * built in memory, not discovery/core.json.) */
export function globalPromptText(
  args: PromptInputs,
  core: Core,
  verdicts: string,
  allIds: ReadonlySet<string>,
  scope: { ids: ReadonlySet<string>; full: ReadonlySet<string>; paper: string[] | null } | null = null,
  budget: number = GLOBAL_PROMPT_BUDGET,
): string {
  const ids = scope ? [...scope.full] : undefined;
  const carried = scope ? [...scope.ids].filter((id) => !scope.full.has(id)) : [];
  const coreText = ((a: string, b: string) => (b.length < a.length ? b : a))(globalCoreText(core, scope?.ids, scope?.full), globalCoreText(core, scope?.ids, scope?.full, { compactSymbols: true }));
  const text = (byFile: { printed?: boolean; paper: boolean }): string => [
    args.base.trimEnd(),
    section("TYPED CORE (discovery/core.json)", `${scopeLine(args.targets)}\n\n${coreText}`),
    ...openSymbolsSection(args.symbolReadings),
    verdicts,
    ...(byFile.paper ? [section("PAPER (flattened LaTeX)", GLOBAL_BY_FILE.paper)] : (scope?.paper ?? [section("PAPER (flattened LaTeX)", args.flatTex)])),
    ...citedSection(args.citedSources, ids),
    ...patchesSection(args, ids, () => !!byFile.printed, true, () => null, carried),
    ...rejectionsSection(args.rejections),
    ...warningsSection(args.lintWarnings, { allIds }),
    GLOBAL_OUTPUT_BLOCK,
  ].join("\n\n");
  for (const byFile of [{ paper: false }, { printed: true, paper: false }]) {
    const t = text(byFile);
    if (t.length <= budget) return t;
  }
  return text({ printed: true, paper: true });
}
/** What a global prompt over its budget says in place of the section it hands over by file. */
export const GLOBAL_BY_FILE = {
  paper: "Too long to paste in this prompt: read discovery/flat.tex in your working directory — the whole paper, flattened, the text every locator and excerpt here refers to. Read all of it: its prose (section preambles, standing assumptions, conventions) and the proofs are what item 1 checks.",
} as const;
/** The size past which the global prompt hands sections over by file: under the provider's limit
 * (`PROMPT_INPUT_MAX`), with room for a retry's appended violations. */
const GLOBAL_PROMPT_BUDGET = Math.floor(PROMPT_INPUT_MAX * 0.95);

/** The repaired nodes — the ONE definition every routing decision below uses: each patched node, and
 * each corollary a patch splits off its result (a statement the repair wrote). */
function repairedNodes(patches: PatchFile | null): Set<string> {
  return new Set((patches?.patches ?? []).flatMap((p) => [p.node, ...corollaryNodes(p.node, p).map((c) => c.id)]));
}

/** A verdict the runner may carry: faithful, not unresolvably ambiguous, reproduced. */
function isClean(n: V15NodeVerdict): boolean {
  return n.faithfulness === "ok" && n.ambiguity !== "unresolvable" && (n.correctness === "ok" || n.correctness === "bookkeeping");
}

/** Hash of what a `patch_review` judged (the key results and the contribution every patch keeps). */
function patchReviewBasis(patches: PatchFile): string {
  return createHash("sha256").update(JSON.stringify({ key_results: patches.key_results, key_contribution: patches.key_contribution })).digest("hex");
}

/** The previous pass's review, when it can be read; unreadable is "no cache", never an error. */
/** Whether the review on file is of a COMPLETE pass — the state its owner accepted (owner decision
 * 2026-10-07; a verdict of it keyed under an earlier rule is carried over, statement and symbol
 * alike): no pause is recorded on it (`paused`) and the run holds none (`level_pause`: set by a
 * pause, and by a halt that kept what it had graded). */
export function priorPassComplete(prior: Pick<V15Review, "paused"> | null | undefined, verify: { level_pause?: unknown }): boolean {
  return !prior?.paused && !verify.level_pause;
}

async function readPriorReview(reviewPath: string): Promise<V15Review | null> {
  if (!existsSync(reviewPath)) return null;
  try {
    const r = JSON.parse(await readFile(reviewPath, "utf8")) as V15Review;
    return Array.isArray(r?.nodes) ? r : null;
  } catch {
    return null;
  }
}

/** Why the nodes of a pass are graded afresh (`regradeCause`). */
export interface RegradeBreakdown {
  causes: Partial<Record<RegradeCause | "text does not compile", number>>;
}

/** The delta log's breakdown line: `delta review: why re-graded — <n> content changed, <n> dependency
 * changed, <n> symbol meaning changed[, <n> dependency verdict changed, <n> note rewritten, <n> new, …]`.
 * The first three always; the rest when non-zero. */
export function regradeBreakdownLine(why: RegradeBreakdown): string {
  const n = (c: RegradeCause | "text does not compile"): number => why.causes[c] ?? 0;
  const always: Array<[RegradeCause, string]> = [
    ["content", "content changed"],
    ["dependency", "dependency changed"],
    ["symbol meaning", "symbol meaning changed"],
  ];
  const sometimes: Array<[RegradeCause | "text does not compile", string]> = [
    ["dependency verdict", "dependency verdict changed"],
    ["note", "note rewritten"],
    ["text does not compile", "text does not compile"],
    ["new", "new"],
    ["not clean before", "not clean before"],
    ["no comparable record", "no comparable basis record"],
    ["cache withdrawn", "cache entry withdrawn"],
  ];
  const parts = [...always.map(([c, l]) => `${n(c)} ${l}`), ...sometimes.filter(([c]) => n(c) > 0).map(([c, l]) => `${n(c)} ${l}`)];
  return `delta review: why re-graded — ${parts.join(", ")}`;
}

/** How a result's verdict reads to the results using it (the shard's DEPENDENCY VERDICTS line), for a
 * basis: the line of `dependencyLine`, given whatever repair of the result is on file. */
export type ShownVerdict = (id: string, v: V15NodeVerdict, coreOnly?: boolean) => string;

/** The repair of a statement on file as the results using it are shown it (`DependencyVerdict.repair`):
 * its text in the core is the corrected form; what the printed statement got wrong is the ledger's. */
function repairOnFile(core: Core, patches: PatchFile | null, paperErrors: VerifyState["paper_errors"]): (id: string) => DependencyVerdict["repair"] {
  const statements = new Map(core.statements.map((st) => [st.id, st] as const));
  return (id) => {
    const st = statements.get(id);
    if (!st || !patches?.patches.some((x) => x.node === id)) return null;
    const pe = paperErrors?.[id];
    return { corrected: st.statement, printedError: pe && pe.kind !== "clarification" && !pe.owner_overruled ? (pe.witness ?? pe.detail) : null };
  };
}

/** `ShownVerdict` of a core: the dependency line of each statement, with its repair (`repairOf`);
 * `coreOnly`: the line as the core alone gives it — the repair without what the ledger says of it. */
export function shownVerdictOf(core: Core, repairOf: (id: string) => DependencyVerdict["repair"] = () => null): ShownVerdict {
  const kind = new Map(core.statements.map((st) => [st.id, String(st.kind ?? "statement")] as const));
  return (id, v, coreOnly = false) => {
    const repair = repairOf(id);
    return dependencyLine({ id, kind: kind.get(id) ?? "statement", verdict: v, repair: repair && coreOnly ? { ...repair, printedError: null } : repair });
  };
}

/** The delta partition of a pass (`partitionByBasis`). */
export interface BasisPartition {
  bases: Map<string, string>;
  inputs: Map<string, BasisInputs>;
  carried: V15NodeVerdict[];
  toGrade: string[];
  why: RegradeBreakdown;
  /** THE CHAIN, called once the verdicts of `graded` are final (`final`: every final verdict so far;
   * `referee_shards.ts` `onGraded`): each of them is re-based on the dependency verdicts it was shown,
   * and every CARRIED verdict using one of them directly whose line now reads otherwise than the one
   * that verdict was given under is re-opened — moved to `toGrade`, returned, graded in this pass. */
  onGraded: (final: ReadonlyMap<string, V15NodeVerdict>, graded: readonly string[]) => string[];
  /** The nodes the chain re-opened. One the pass does not reach (a pause, a halt) keeps NO verdict
   * and no cache entry: the verdict on file was given under a line that no longer stands. */
  reopened: Set<string>;
}

/**
 * Split the core into the nodes this pass must grade and the verdicts it carries. A verdict is
 * carried only when (1) `state.verify.confirmed` records a clean grade on the node's CURRENT basis,
 * and (2) the previous review holds that clean verdict (with the same basis, when it recorded
 * one) — the verdict body, bookkeeping condition and pinned reading included, since acceptance
 * re-adds them to the core. Everything else — new nodes, changed nodes, nodes using a node whose text
 * or verdict moved, nodes never graded clean — is graded afresh. `carryAny` (fix as you go,
 * `LevelPause.carry`): a verdict a PAUSED pass gave stands on its unchanged basis whatever its
 * grade — the grading resumes where it stopped instead of re-grading the levels below.
 *
 * A basis holds the verdict of each result the node uses, as shown to it (`shown`). For a result
 * CARRIED here that is its verdict on file; for one GRADED in this pass it is not known yet, so the
 * node is carried on the line its verdict was given under and re-opened as soon as the result's new
 * verdict reads otherwise (`onGraded`): the levels are graded leaves first, so a changed verdict
 * re-opens its direct users in the same pass, and theirs after them. A verdict the global pass or a
 * ruling altered after its users were graded is caught the same way on the next pass.
 *
 * TRANSITION (remove with `basisInputsV4`): a verdict recorded under scheme 4 whose scheme-4 basis
 * (`ownV4`: its own material as scheme 4 read it) still holds is carried and re-keyed — its basis taken
 * on the verdicts on file of the results it uses. Scheme 4 kept no record of the lines a verdict was
 * given under, so that holds only where each of those lines is one the scheme-4 basis PROVES the node
 * was graded with: the result it uses is clean and carried in this pass, and its line is exactly the
 * line the CORE gives a clean result (`coreLine`) — what the scheme-4 basis covered, the result being
 * in the node's closure. Per part of the line (`dependencyLine`):
 *   - `ok` / `bookkeeping` with its condition: proved when the condition is wired into the result as
 *     an `ass:bk-*` of the same meaning (a node of the closure); a condition only on the verdict is not;
 *   - an owner's ruling (`owner_overruled`, its reason): on the verdict only — never proved;
 *   - a confirmed repair's corrected form: the result's text in the core — proved; what the printed
 *     statement got wrong (`printedError`): the ledger's — never proved;
 *   - a pinned reading: proved when wired into the result as an `ass:pin-*` of it, of the same meaning;
 *   - `unclear`, `error`, an unresolvable ambiguity, drift: not clean — never carried over.
 * The test is the line itself against the one built from the proved parts alone, so whatever the
 * line prints beyond them — a part added to it later too — fails it. Otherwise the node is graded
 * afresh ("dependency verdict").
 *
 * That strict rule is for a review left by a pass that did NOT run to its end (`transition.complete`
 * false: paused at a level, or halted — its verdicts are of different moments). A review left by a
 * COMPLETE pass is the state its owner accepted (owner decision 2026-10-07): there every scheme-4
 * verdict whose scheme-4 basis still holds is re-keyed, the lines of the results it uses recorded as
 * they stand now. Under scheme 4 a verdict-only change of a result did not re-open its users either,
 * so this carries over exactly what the old cache held, no more; every verdict given from now on is
 * keyed soundly. In both cases what costs nothing and is stale for sure still forces the users: a
 * used result that is not clean now, rewritten by a ruling (`owner_overruled`), or without a cache
 * entry (withdrawn) — and a used result graded in this pass re-opens them if its line moves (the chain).
 */
export function partitionByBasis(
  core: Core,
  confirmed: Record<string, string>,
  prior: V15Review | null,
  extra: BasisExtra = new Map(),
  carryAny: Readonly<Record<string, string>> = {},
  own: ReadonlyMap<string, string> = new Map(),
  shown: ShownVerdict = shownVerdictOf(core),
  transition: { own?: ReadonlyMap<string, string>; complete?: boolean; earlierExtra?: BasisExtra } = {},
): BasisPartition {
  const ownV4 = transition.own ?? own;
  // The extra as the passes to 2026-10-07 computed it (`earlierExtra`; absent: nothing moved).
  const extraBefore = transition.earlierExtra ?? extra;
  const priorById = new Map((prior?.nodes ?? []).map((n) => [n.id, n] as const));
  const bases = new Map<string, string>();
  const inputs = new Map<string, BasisInputs>();
  const carried: V15NodeVerdict[] = [];
  const toGrade: string[] = [];
  const why: RegradeBreakdown = { causes: {} };
  const count = (c: RegradeCause): void => void (why.causes[c] = (why.causes[c] ?? 0) + 1);
  // The line a verdict shows its users, whoever graded it and whenever (`graded` is not part of it).
  const line = (d: string, v: V15NodeVerdict | undefined): string | undefined =>
    v ? createHash("sha256").update(shown(d, (({ graded: _g, ...rest }) => rest)(v))).digest("hex") : undefined;
  const statements = new Set(core.statements.map((st) => st.id));
  const uses = new Map(core.statements.map((st) => [st.id, [...new Set(st.depends_on)].filter((d) => d !== st.id && statements.has(d))] as const));
  /** The line of a clean result `d` as the core alone gives it (TRANSITION, see above): `ok`, or
   * `bookkeeping` / pinned with the verdict's condition / reading where one of the same meaning is
   * wired into `d` (`bindingReadings`), and the repair without the ledger's words. */
  const coreLine = (d: string, v: V15NodeVerdict): string => {
    const wired = bindingReadings(core, d);
    const has = (kind: "pin" | "bookkeeping", text: string | undefined): boolean => text !== undefined && wired.some((r) => r.kind === kind && (kind === "bookkeeping" || r.of === d) && normalizeBasisText(r.text) === normalizeBasisText(text));
    const bk = v.correctness === "bookkeeping" && has("bookkeeping", v.bookkeeping_assumption?.condition);
    const pin = v.ambiguity === "pinned" && has("pin", v.reading?.reading);
    const proved = { id: d, faithfulness: "ok", ambiguity: pin ? "pinned" : "ok", correctness: bk ? "bookkeeping" : "ok", detail: "", witness: null, bookkeeping_assumption: bk ? v.bookkeeping_assumption : null, reading: pin ? v.reading : null };
    return shown(d, proved as V15NodeVerdict, true);
  };
  /** Per node, decided after the results it uses: its cause when it is graded afresh, null when carried. */
  const decided = new Map<string, RegradeCause | null>();
  const decide = (id: string): boolean => {
    if (decided.has(id)) return decided.get(id) !== null;
    // In a dependency cycle (the structural gate forbids one) the members wait on each other.
    decided.set(id, "new");
    const pv = priorById.get(id);
    const legacy = pv && (pv.basis_scheme ?? 1) === 4;
    const given = pv?.basis_inputs?.verdicts ?? {};
    // A result graded in this pass: the line this verdict was given under, until its new one is known.
    const verdictOf = (d: string): string | undefined => (!legacy && decide(d) ? given[d] : line(d, priorById.get(d)));
    const inp = basisInputs(core, id, extra, own.get(id), verdictOf);
    const basis = basisOf(inp);
    bases.set(id, basis);
    inputs.set(id, inp);
    const stands = (b: string): boolean => !!pv && ((confirmed[id] === b && isClean(pv) && (pv.basis === undefined || pv.basis === b)) || (carryAny[id] === b && pv.basis === b));
    const v4 = legacy ? basisInputsV4(core, id, extraBefore, ownV4.get(id)) : null;
    const held = v4 !== null && stands(basisOf(v4));
    // … of a paused or halted pass, only while what the scheme-4 key never read — the node's own
    // readings, the open symbols its shard lists, of it and of its closure — is nothing: the same key
    // under the extra of today. (A complete pass is carried as it stands.)
    const keyShown = v4 !== null && (transition.complete === true || extraBefore === extra || basisOf(basisInputsV4(core, id, extra, ownV4.get(id))) === basisOf(v4));
    // TRANSITION (remove once every run on file has passed one V1.5 pass with this code): a verdict
    // keyed before a hypothesis's own readings and the open symbols its shard lists were read into
    // its basis (`earlierExtra`) is carried over and re-keyed while that earlier basis holds — of a
    // COMPLETE pass only, as above; a paused or halted pass grades it afresh.
    const heldBefore = !legacy && transition.complete === true && transition.earlierExtra !== undefined && stands(basisOf(basisInputs(core, id, extraBefore, own.get(id), verdictOf)));
    // … carried over only on lines its scheme-4 basis proves it was graded with.
    const linesStood = (): boolean =>
      (uses.get(id) ?? []).every((d) =>
        ((dv) =>
          !!dv && isClean(dv) && !dv.owner_overruled && (transition.complete ? confirmed[d] !== undefined || carryAny[d] !== undefined : !decide(d) && shown(d, (({ graded: _g, ...rest }) => rest)(dv)) === coreLine(d, dv)))(priorById.get(d)),
      );
    const cause = stands(basis) || heldBefore || (held && keyShown && linesStood()) ? null : held && !keyShown ? "no comparable record" : held ? "dependency verdict" : regradeCause(pv ? { inputs: pv.basis_inputs, clean: isClean(pv) || carryAny[id] !== undefined } : null, v4 ?? inp);
    decided.set(id, cause);
    return cause !== null;
  };
  for (const id of indexCore(core).ids) {
    if (decide(id)) {
      toGrade.push(id);
      count(decided.get(id)!);
    } else carried.push({ ...priorById.get(id)!, basis: bases.get(id), basis_scheme: BASIS_SCHEME, basis_inputs: inputs.get(id), graded: "carried" });
  }
  const reopenedAll = new Set<string>();
  const onGraded = (final: ReadonlyMap<string, V15NodeVerdict>, graded: readonly string[]): string[] => {
    for (const id of graded) {
      const inp = basisInputs(core, id, extra, own.get(id), (d) => line(d, final.get(d)));
      inputs.set(id, inp);
      bases.set(id, basisOf(inp));
    }
    const done = new Set(graded);
    const reopened = carried.filter((v) => (uses.get(v.id) ?? []).some((d) => done.has(d) && line(d, final.get(d)) !== inputs.get(v.id)?.verdicts?.[d])).map((v) => v.id);
    for (const id of reopened) {
      carried.splice(carried.findIndex((v) => v.id === id), 1);
      toGrade.push(id);
      reopenedAll.add(id);
      count("dependency verdict");
    }
    return reopened;
  };
  return { bases, inputs, carried, toGrade, why, onGraded, reopened: reopenedAll };
}

/** What the symbol table of `binding` (the graded core: the symbol referee's fixes and readings
 * written into it) cannot show, as basis extra for each node whose shard lists the symbol: a symbol the
 * referee left open, and one the paper later redefines. A pinned reading is the symbol's `def`, so
 * the table itself carries it into the basis — a change of meaning re-opens the statement's verdict,
 * a re-typesetting does not (`basisInputs`). */
export function symbolBasisExtra(binding: Core, verdicts: readonly V15SymbolVerdict[] = [], opts: { earlier?: boolean } = {}): Map<string, BasisExtraValue> {
  const readings = new Map<string, SymbolReadingBasis[]>();
  const add = (id: string, r: SymbolReadingBasis): void => void (readings.get(id) ?? readings.set(id, []).get(id)!).push(r);
  const nodes = [...binding.statements, ...binding.assumptions, ...binding.definitions].map((n) => n.id);
  for (const v of verdicts) {
    if (v.ambiguity !== "unresolvable" && !v.redefined_at) continue;
    const state = v.ambiguity === "unresolvable" ? "open" : "pinned";
    // TRANSITION (`partitionByBasis` `earlierExtra`; remove with it): the extra to 2026-10-07 — on
    // the statements whose statement (or a hypothesis they are stated under) names the symbol, an
    // open symbol's line unread.
    if (opts.earlier) {
      for (const id of symbolUsers(binding, v.name)) add(id, { symbol: v.name, state, text: "", redefined: !!v.redefined_at });
      continue;
    }
    // On every node whose shard shows the symbol when the node is graded or used (`readingsSection`:
    // `symbolsUsedBy` — named in its record, proof included, or referred to by a symbol that is); a
    // basis reads the extra of the node and of each node it uses, as its shard shows theirs. An open
    // symbol with its line as printed there (the symbol referee's `detail`).
    const text = state === "open" ? v.detail : "";
    for (const id of nodes) if (symbolsUsedBy(binding, [id]).has(v.name)) add(id, { symbol: v.name, state, text, redefined: !!v.redefined_at });
  }
  return new Map([...readings].map(([id, rs]) => [id, { readings: rs }] as const));
}

/** The readings of a hypothesis or definition itself (`bindingReadings` `ownOnly`), as basis extra of
 * that node: its shard prints them as BINDING on it (`readingsSection`), and nothing else of its
 * basis reads them — a statement reads a reading through the wiring, a hypothesis has none. No entry
 * for a node with none (its basis stands as it was). */
export function ownReadingsExtra(core: Core): Map<string, BasisExtraValue> {
  return new Map(
    [...core.assumptions, ...core.definitions].flatMap((n) => {
      const own = bindingReadings(core, n.id, { ownOnly: true });
      return own.length > 0 ? [[n.id, `own readings\n${own.map((r) => `${r.id}: ${normalizeBasisText(r.text)}`).join("\n")}`] as const] : [];
    }),
  );
}

/** A verdict on file that carries a condition appended to its node: graded `bookkeeping`, or made an
 * `error` since by a finding moved onto it (`errorsOnHosts`; a degenerate witness's exclusion is not
 * appended until it is settled as `bookkeeping`). */
const appendedCondition = (n: V15NodeVerdict): boolean => !!n.bookkeeping_assumption && (n.correctness === "bookkeeping" || (n.correctness === "error" && n.witness_regime !== "degenerate"));

/**
 * A condition an earlier pass appended to a node is kept when the node is graded afresh and the referee
 * neither restates it nor drops it (`bookkeeping_dropped`): a clean `ok` grade with no condition takes the
 * earlier one back (correctness `bookkeeping`). The Lean the F stages built rests on it, and a re-grade
 * that silently forgets it leaves a hypothesis the core no longer grants (live yang: an AIPW regularity
 * condition vanished on a re-grade).
 */
export function keepEarlierConditions(fresh: readonly V15NodeVerdict[], prior: V15Review | null): V15NodeVerdict[] {
  const before = new Map((prior?.nodes ?? []).filter(appendedCondition).map((n) => [n.id, n.bookkeeping_assumption!] as const));
  return fresh.map((n) => {
    const earlier = before.get(n.id);
    if (!earlier || n.bookkeeping_assumption || n.bookkeeping_dropped || n.correctness !== "ok") return n;
    return { ...n, correctness: "bookkeeping", bookkeeping_assumption: earlier, detail: `[condition kept from an earlier pass] ${n.detail}` };
  });
}

/** The CONDITIONS APPENDED EARLIER of the nodes to grade, from the review on file. */
export function priorConditionLines(prior: V15Review | null, toGrade: readonly string[]): Array<{ node: string; line: string }> {
  const grade = new Set(toGrade);
  return (prior?.nodes ?? [])
    .filter((n) => grade.has(n.id) && appendedCondition(n))
    .map((n) => ({ node: n.id, line: `${n.id}: ${n.bookkeeping_assumption!.condition.replace(/\s+/g, " ").trim()} (${n.bookkeeping_assumption!.reason.replace(/\s+/g, " ").trim()})` }));
}

/** The CONDITIONS APPENDED EARLIER section; `ids` given (a shard): only those nodes'. */
function priorConditionsSection(pc: PromptInputs["priorConditions"], ids?: readonly string[] | null): string[] {
  const shown = (pc ?? []).filter((x) => !ids || ids.includes(x.node));
  return shown.length > 0
    ? [
        section(
          "CONDITIONS APPENDED EARLIER (keep unless no longer needed)",
          "An earlier pass appended each condition below to a node you grade, and the formalization rests on it. If the node still " +
            "needs it, grade `bookkeeping` and restate it (amended if needed) in `bookkeeping_assumption`; if it no longer needs it " +
            "(a repair or the paper now grants it), set `bookkeeping_dropped: true` and say why in the detail. A condition you neither " +
            "restate nor drop is kept as it was.\n\n" +
            shown.map((x) => `- ${x.line}`).join("\n"),
        ),
      ]
    : [];
}

/** The review this pass persists: every node of the core, fresh grades and carried verdicts
 * together; and the cache updated from the fresh grades (a clean one recorded on its
 * basis, any other one withdrawn) and pruned to the nodes the core still has. */
function mergeCarried(
  core: Core,
  fresh: V15NodeVerdict[],
  carried: V15NodeVerdict[],
  part: { bases: Map<string, string>; inputs: Map<string, BasisInputs>; reopened?: ReadonlySet<string> },
  confirmed: Record<string, string>,
  prior: V15Review | null = null,
): { nodes: V15NodeVerdict[]; confirmed: Record<string, string> } {
  const { bases } = part;
  fresh = keepEarlierConditions(fresh, prior);
  const byId = new Map<string, V15NodeVerdict>();
  for (const n of carried) byId.set(n.id, n);
  for (const n of fresh) byId.set(n.id, { ...n, basis: bases.get(n.id), basis_scheme: BASIS_SCHEME, basis_inputs: part.inputs.get(n.id), graded: "fresh" });
  const next: Record<string, string> = {};
  for (const id of bases.keys()) if (confirmed[id] !== undefined) next[id] = confirmed[id]!;
  // A clean verdict the partition carried (its inputs are the partition's own record) is cached on
  // the basis it is carried on: the one on file, but for a verdict carried over from scheme 4, re-keyed here.
  for (const n of carried) if (confirmed[n.id] !== undefined && n.basis !== undefined && n.basis_inputs === part.inputs.get(n.id) && isClean(n)) next[n.id] = n.basis;
  // A verdict the chain re-opened and the pass did not reach stands on nothing: no cache entry.
  for (const id of part.reopened ?? []) delete next[id];
  for (const n of fresh) {
    if (isClean(n)) next[n.id] = bases.get(n.id)!;
    else delete next[n.id];
  }
  // This pass's grades in the referee's order (routing reads them in that order), then the carried
  // verdicts in core order.
  const freshIds = fresh.map((n) => n.id);
  const carriedIds = [...indexCore(core).ids].filter((id) => byId.has(id) && !freshIds.includes(id));
  return { nodes: [...freshIds, ...carriedIds].map((id) => byId.get(id)!), confirmed: next };
}

/** Every addressable node, with the tex coordinates the report and the FAIL message key on. */
interface CoreIndex {
  statements: Map<string, CoreStatement>;
  locators: Map<string, TexLocator | undefined>;
  ids: Set<string>;
}

function indexCore(core: Core): CoreIndex {
  const statements = new Map<string, CoreStatement>();
  const locators = new Map<string, TexLocator | undefined>();
  for (const s of core.statements) {
    statements.set(s.id, s);
    locators.set(s.id, s.tex_locator);
  }
  for (const a of core.assumptions) locators.set(a.id, a.tex_locator);
  for (const d of core.definitions) locators.set(d.id, d.tex_locator);
  return { statements, locators, ids: new Set(locators.keys()) };
}

function locatorText(loc: TexLocator | undefined): string {
  return loc ? `${loc.file}:${loc.from}-${loc.to}` : "no tex_locator";
}

/** Ids listed in a violation message. Capped so one ungraded core does not push a
 * thousand-character list into the retry prompt, but the count is always exact. */
function idList(ids: string[], cap = 40): string {
  const head = ids.slice(0, cap).join(", ");
  return ids.length > cap ? `${head}, … (+${ids.length - cap} more)` : head;
}

/** TRANSITION (remove with `basisInputsV4`) — a node's own material under scheme 4: the fixer note of
 * its patch and the ids of the corollaries split off it. Scheme 5 reads the repairs as shown (`repairBasis`). */
export function noteBasis(patches: PatchFile | null): Map<string, string> {
  const out = new Map<string, string>();
  for (const p of patches?.patches ?? []) {
    // A split result is judged with its corollaries (what the repair gives up is what no block keeps):
    // a corollary added, dropped or reworded re-grades it.
    const split = p.corollaries?.length ? `\ncorollaries: ${JSON.stringify(corollaryNodes(p.node, p).map((c) => c.id).sort())}${isUmbrellaPatch(p) ? "\numbrella" : ""}` : "";
    if (hasExplanation(p.owner_explanation) || split) out.set(p.node, `${hasExplanation(p.owner_explanation) ? JSON.stringify(p.owner_explanation) : ""}${split}`);
  }
  return out;
}

/**
 * The repaired nodes whose fixer note the referee grades for clarity when it confirms the repair: each
 * patch on a node of the core (a statement, an assumption, a definition) answering an open error of the
 * ledger that carries an `owner_explanation`.
 */
export function clarityOwed(core: Core, patches: PatchFile | null, ledger: VerifyState["paper_errors"]): Set<string> {
  const nodes = indexCore(core).ids;
  const open = (id: string): boolean => {
    const e = ledger?.[id];
    return !!e && e.kind !== "clarification" && e.owner_decision !== "finding rejected";
  };
  return new Set((patches?.patches ?? []).filter((p) => nodes.has(p.node) && open(p.node) && hasExplanation(p.owner_explanation)).map((p) => p.node));
}

/**
 * Content checks the output schema cannot express. A violation is the referee's defect,
 * not the paper's, so the caller retries the call ONCE with these lines appended and
 * checkpoints if they survive — a review that addresses a node the core does not have,
 * grades only some of them, or claims an error with no witness, is not evidence about the
 * paper either way.
 */
function contractViolations(
  review: V15Review,
  index: CoreIndex,
  hasPatches = false,
  toGrade: ReadonlySet<string> = index.ids,
  rejections: readonly FixerRejection[] = [],
  patches: PatchFile | null = null,
  /** Check the witness regime of every refuting `error` (a referee's own reply; not the merged
   * sharded review, whose global-pass errors carry none and whose degenerate grades are settled). */
  requireRegime = true,
  /** The repaired statements whose fixer note a confirmation grades for clarity (its own reply
   * only; `clarityOwed`). null: not checked. */
  owed: ReadonlySet<string> | null = null,
): string[] {
  const out: string[] = [];
  // A weakening grade names a repair: a repaired node.
  const repairParts = repairedNodes(patches);
  const ruled = review.rejection_verdicts ?? [];
  for (const r of rejections) {
    const n = ruled.filter((v) => v.node === r.node).length;
    if (n === 0) out.push(`the fixer's rejection on "${r.node}" has no \`rejection_verdicts\` entry — rule on every FIXER REJECTION.`);
    if (n > 1) out.push(`the fixer's rejection on "${r.node}" is ruled on more than once.`);
  }
  for (const v of ruled) {
    if (!rejections.some((r) => r.node === v.node)) out.push(`\`rejection_verdicts\` names "${v.node}", which has no pending fixer rejection.`);
  }
  if (hasPatches && !review.patch_review) {
    out.push("the core carries the fixer's PATCHES but `patch_review` is null — judge the key results and the patches.");
  }
  if (!hasPatches && review.patch_review) {
    out.push("`patch_review` must be null: this core carries no fixer patches.");
  }
  const seen = new Set<string>();
  // COVERAGE. The review is the run's only correctness gate before Lean, and its verdict is
  // computed from the grades present — so a referee that graded three nodes of twenty (or
  // none) would PASS the core and stamp it for F1 while saying nothing about the rest. Every
  // statement, assumption and definition must carry exactly one entry — here or, carried, from an
  // earlier pass on the same basis (`toGrade` is what this pass owes).
  const graded = new Set(review.nodes.map((n) => n.id));
  const ungraded = [...toGrade].filter((id) => !graded.has(id));
  if (ungraded.length > 0) {
    out.push(
      `${ungraded.length} core node(s) carry no verdict: ${idList(ungraded)}. Emit exactly one ` +
        (toGrade === index.ids
          ? "`nodes` entry for EVERY statement, assumption and definition of the core."
          : "`nodes` entry for EVERY node listed under NODES TO GRADE."),
    );
  }
  for (const node of review.nodes) {
    if (!index.ids.has(node.id)) {
      out.push(`node "${node.id}" is not a node of the core (unknown id).`);
    }
    if (seen.has(node.id)) out.push(`node "${node.id}" is graded more than once.`);
    seen.add(node.id);
    if (node.minimality === true && node.correctness !== "error") {
      out.push(`node "${node.id}" is marked minimality but graded correctness "${node.correctness}" — minimality marks an \`error\` that is only non-minimality.`);
    }
    if (node.follows_repair === true && node.correctness !== "error") out.push(`node "${node.id}" is marked follows_repair but graded correctness "${node.correctness}" — follows_repair marks an \`error\` caused only by a repaired result it uses.`);
    if (node.weakens_contribution === true) {
      if (node.correctness !== "error") out.push(`node "${node.id}" is marked weakens_contribution but graded correctness "${node.correctness}" — a weakening repair is graded \`error\`.`);
      if (node.minimality === true) out.push(`node "${node.id}" is marked both minimality and weakens_contribution — a weakening repair is not a minimality dispute; give one.`);
      if (!repairParts.has(node.id)) out.push(`node "${node.id}" is marked weakens_contribution but is not a repaired node — grade the weakening on the repair that causes it.`);
    }
    const degenerate = node.correctness === "error" && node.witness_regime === "degenerate";
    if (requireRegime) {
      // A hypothesis of a cited result is no side condition of the passage citing it: on the leaf it
      // would be appended to a node with no text, and its host would never assume it.
      if (index.statements.get(node.id)?.cited_in && (node.correctness === "bookkeeping" || degenerate)) {
        out.push(
          `node "${node.id}" is a published result a proof invokes by citation: a hypothesis of the cited result that its host's statement and hypotheses do not give is an "error" ` +
            `with an "in_scope" witness (it is repaired on the host), never a bookkeeping condition or a degenerate case — grade it "error" (bookkeeping_assumption null) or "ok".`,
        );
      }
      if (isRefutingError(node)) {
        if (node.witness_regime !== "in_scope" && node.witness_regime !== "degenerate") {
          out.push(
            `node "${node.id}" is graded correctness "error" with no witness_regime — say whether the witness is "in_scope" ` +
              `(a genuine instance of the paper's setting) or "degenerate" (a case the setting implicitly excludes).`,
          );
        }
        if (!(node.witness_instance ?? "").trim()) out.push(`node "${node.id}" is graded correctness "error" with no witness_instance — name the model / instance the witness lives in, in one line.`);
        if (degenerate && !node.bookkeeping_assumption) {
          out.push(`node "${node.id}" has a degenerate witness but no bookkeeping_assumption — state the exclusion as one condition in the paper's notation.`);
        }
        if (degenerate && index.ids.has(node.id) && !index.statements.has(node.id)) {
          out.push(`node "${node.id}" has a degenerate witness but is not a statement — exclude the degenerate case on the statement that uses this node.`);
        }
      } else if ((node.witness_regime ?? null) !== null || (node.witness_instance ?? null) !== null) {
        out.push(`node "${node.id}" carries a witness_regime / witness_instance but is not graded as a refuting "error" — set both to null.`);
      }
    }
    // A CONFIRMED repair: the referee grades the fixer's note the author reads.
    if (owed?.has(node.id) && (node.correctness === "ok" || node.correctness === "bookkeeping") && !(node.explanation_clarity && node.explanation_clarity.reason.trim())) {
      out.push(`node "${node.id}" confirms a repair whose patch carries the fixer's note but gives no explanation_clarity — grade it "ok" or "unclear" with a one-line reason.`);
    }
    if (node.correctness === "error" && !(node.witness ?? "").trim()) {
      out.push(
        `node "${node.id}" is graded correctness "error" with no witness — grade it ` +
          `"unclear" unless you can give the false step or a counterexample.`,
      );
    }
    if (node.correctness === "bookkeeping" && node.bookkeeping_assumption === null) {
      out.push(
        `node "${node.id}" is graded correctness "bookkeeping" with no ` +
          "bookkeeping_assumption — supply the single condition and the step that uses it.",
      );
    }
    // A condition attached to any other grade would be added to the core — silently altering
    // the paper's hypotheses — on the strength of a verdict that never said one was missing.
    if (node.bookkeeping_assumption !== null && node.correctness !== "bookkeeping" && !degenerate) {
      out.push(
        `node "${node.id}" carries a bookkeeping_assumption but is graded correctness ` +
          `"${node.correctness}" — grade it "bookkeeping" if the condition is genuinely ` +
          "needed, otherwise drop the condition.",
      );
    }
    // Text the runner writes into the core or shows the author is never broken TeX (C6).
    if (node.reading?.reading) for (const p of texEscapeProblems(node.reading.reading, "reading")) out.push(`node "${node.id}": its reading ${p}.`);
    if (node.bookkeeping_assumption?.condition) for (const p of texEscapeProblems(node.bookkeeping_assumption.condition, "bookkeeping_assumption")) out.push(`node "${node.id}": its bookkeeping_assumption ${p}.`);
    if (node.ambiguity === "pinned" && node.reading === null) {
      out.push(
        `node "${node.id}" is graded ambiguity "pinned" with no reading — supply the reading the ` +
          `paper determines and the evidence, or grade it "unresolvable".`,
      );
    }
    if (node.reading !== null && node.ambiguity !== "pinned") {
      out.push(
        `node "${node.id}" carries a reading but is graded ambiguity "${node.ambiguity}" — a reading ` +
          `is only pinned on a "pinned" grade.`,
      );
    }
    // The condition is wired in through `depends_on`, which only statements carry.
    if (
      node.bookkeeping_assumption !== null &&
      !degenerate &&
      index.ids.has(node.id) &&
      !index.statements.has(node.id)
    ) {
      out.push(
        `node "${node.id}" carries a bookkeeping_assumption but is not a statement — ` +
          "attach the condition to the statement whose proof silently uses it.",
      );
    }
  }
  return out;
}

/**
 * The texts of the referee's node verdicts the annotated paper prints or the core carries — the
 * detail, the witness, the reading, the bookkeeping condition — compiled against the paper's
 * preamble (`tex_fragment_check.ts`); a violation per text that does not compile, with the compiler's
 * line. The contract's async half (`contractViolations` is the pure half).
 */
export async function refereeTexViolations(nodes: readonly V15NodeVerdict[], ctx: TexCheckContext | null): Promise<string[]> {
  return texFieldViolations(
    nodes.flatMap((n) => [
      { where: `node "${n.id}": its detail`, text: n.detail, kind: "note" as const },
      { where: `node "${n.id}": its witness`, text: n.witness, kind: "note" as const },
      { where: `node "${n.id}": its reading`, text: n.reading?.reading, kind: "note" as const },
      { where: `node "${n.id}": its bookkeeping_assumption`, text: n.bookkeeping_assumption?.condition, kind: "hypothesis" as const },
    ]),
    ctx,
  );
}

/** The verdict is a function of the grades, never of the model's own `verdict` field. */
function computeVerdict(nodes: V15NodeVerdict[]): V15Review["verdict"] {
  // A refutation is only a refutation of the PAPER when the core says what the paper says.
  // While any node drifts or is ambiguous, an `error` may be an error of the transcription
  // (a missing setup definition, a dropped hypothesis), so the core goes back to V1 first
  // and the errors travel with the directive as provisional findings; FAIL is reserved for
  // an error on a faithful, unambiguous core.
  if (nodes.some((n) => n.faithfulness === "drift")) return "REVISE";
  if (nodes.some((n) => n.correctness === "error" || n.ambiguity === "unresolvable")) return "FAIL";
  return "PASS";
}

/** Record one V1.5 observation. ALWAYS through `recordVerifyFinding`: it dedupes on
 * `(node, stage, kind, detail)`, so re-entering the stage (`--from-stage V1.5`) re-states the
 * same refutations and notes instead of stacking a second copy of each into the report. */
function record(
  state: StateJson,
  node: string,
  kind: VerifyFinding["kind"],
  detail: string,
  witness: string | null,
  extra: { patch?: FindingPatch; descoped?: boolean; stage?: string; suggested_repair?: string; suggestion_declined?: string; undetermined?: boolean } = {},
): void {
  recordVerifyFinding(state, {
    node,
    stage: extra.stage ?? "V1.5",
    kind,
    detail,
    witness,
    ...(extra.undetermined ? { undetermined: true } : {}),
    ...(extra.patch ? { patch: extra.patch } : {}),
    ...(extra.descoped ? { descoped: true } : {}),
    ...(extra.suggested_repair ? { suggested_repair: extra.suggested_repair } : {}),
    ...(extra.suggestion_declined ? { suggestion_declined: extra.suggestion_declined } : {}),
  });
}

/** How the finding of a refuted repair of a statement the paper leaves undetermined opens: its
 * witness is against the reading tried, not against the printed statement. */
export const TRIED_REPAIR_REFUTED = "the repair tried for it was refuted";

/** How the note of a statement the paper left undetermined and a confirmed repair made precise opens. */
export const MADE_PRECISE_NOTE = "made precise — the printed statement did not determine the claim; the reading its repair states was confirmed";

/** Record every patch of the file as the refutation it repairs. `confirmedOk` = the node the
 * confirming pass graded without an error (its patch holds). A descoped node is recorded as
 * refuted and descoped; what rests on it as unresolved. */
async function recordPatches(
  args: VerifyStageArgs,
  patches: PatchFile,
  confirmedOk: (node: string) => boolean,
): Promise<void> {
  // A finding the owner withdrew is no error of the paper: its node is recorded as if never found.
  const ledger = Object.fromEntries(Object.entries(args.state.verify!.paper_errors ?? {}).filter(([, e]) => !isWithdrawn(e)));
  const descoped = descopedStatements(await readTranscribedCore(args.runDir), patches);
  for (const p of patches.patches) {
    // A patched result a later round descoped was never reviewed as repaired: it is reported as
    // descoped with its error, never as a confirmed repair.
    if (descoped.has(p.node)) {
      const e = ledger[p.node];
      if (e) record(args.state, p.node, openFindingKind(e).kind, e.detail, e.witness, { patch: findingPatch(p, false), descoped: true, undetermined: openFindingKind(e).undetermined });
      continue;
    }
    const ok = confirmedOk(p.node);
    // A CLARIFICATION (an F-stage reviewer found the statement admits several readings; the patch
    // states the intended one) is no error of the paper: confirmed, it is a note carrying
    // the clarified text; unconfirmed, the reading is still unsettled.
    if (ledger[p.node]?.kind === "clarification") {
      const e = ledger[p.node]!;
      if (ok) record(args.state, p.node, "note", `clarified — the reading the statement means is now stated: ${e.detail}`, null, { patch: findingPatch(p, true) });
      else record(args.state, p.node, "unresolved", `the clarification of this statement was not confirmed: ${e.detail}`, null, { patch: findingPatch(p, false) });
      continue;
    }
    // A SUPPORTING patch (a result that was not wrong as printed — say, one that discharges an
    // inherited hypothesis) is no refutation of the paper: confirmed, it is only a change the
    // report shows; unconfirmed, it leaves the corrected version unverified.
    const e = ledger[p.node];
    if (!e) {
      if (!ok) record(args.state, p.node, "unresolved", `a supporting change to this result was not confirmed: ${p.proof_note}`, null);
      continue;
    }
    // A statement the paper leaves UNDETERMINED was never shown false: its confirmed repair makes it
    // precise (a note carrying the adopted text, as a clarification is); unconfirmed, it stays undetermined.
    if (e.undetermined && ok) {
      record(args.state, p.node, "note", `${MADE_PRECISE_NOTE}: ${e.detail}`, null, { patch: findingPatch(p, true), undetermined: true });
      continue;
    }
    const open = ok ? { kind: "refuted" as const } : openFindingKind(e);
    record(
      args.state,
      p.node,
      open.kind,
      e.detail,
      e.witness,
      { patch: findingPatch(p, ok), undetermined: open.undetermined },
    );
  }
  for (const u of patches.unfixable) {
    const e = ledger[u.node];
    record(
      args.state,
      u.node,
      // No error of the paper on record (a proof the referee could not reproduce) and nothing it
      // follows: not verified, never refuted.
      !e && !u.consequence_of?.length ? "unresolved" : openFindingKind(e).kind,
      `${e ? `${e.detail} — ` : ""}cannot be repaired without losing its point: ${u.reason}`,
      e?.witness ?? null,
      {
        descoped: true,
        undetermined: openFindingKind(e).undetermined,
        ...(u.suggested_repair ? { suggested_repair: suggestionText(u.suggested_repair) } : {}),
        ...(u.declined !== undefined ? { suggestion_declined: u.declined } : {}),
      },
    );
  }
  for (const [id, why] of descoped) {
    if (!patches.unfixable.some((u) => u.node === id)) record(args.state, id, "unresolved", why, null, { descoped: true });
  }
  // An error in the ledger that no patch and no unfixable entry addresses (a hand-written or
  // deleted patch file) is still the paper's error — never dropped, reported unrepaired.
  recordUnaddressed(args, patches);
}

function recordUnaddressed(args: VerifyStageArgs, patches: PatchFile | null): void {
  const addressed = new Set([...(patches?.patches ?? []).map((p) => p.node), ...(patches?.unfixable ?? []).map((u) => u.node)]);
  for (const [node, e] of Object.entries(args.state.verify!.paper_errors ?? {})) {
    if (addressed.has(node) || isWithdrawn(e)) continue;
    if (e.kind === "clarification") record(args.state, node, "unresolved", `${e.detail} (a reading to clarify; no patch writes it into the statement)`, null);
    else record(args.state, node, openFindingKind(e).kind, `${e.detail} (found by an earlier referee pass; no patch addresses it)`, e.witness, { undetermined: openFindingKind(e).undetermined });
  }
}

function counts(nodes: V15NodeVerdict[]): string {
  const by = (grade: V15NodeVerdict["correctness"]): number =>
    nodes.filter((n) => n.correctness === grade).length;
  return `${by("ok")} ok, ${by("bookkeeping")} bookkeeping, ${by("unclear")} unclear`;
}

/** PASS tail: rebuild the core WITH the referee's additions (bookkeeping conditions, pinned
 * readings — see `core_graph.ts`), re-gate, persist, stamp the hash. */
async function acceptCore(
  args: VerifyStageArgs,
  /** The transcribed core as read at STAGE ENTRY — the one the referee's core was built from; never
   * re-read from disk here, so a file edited during the referee call is not accepted unreviewed. */
  transcribed: Core,
  corePath: string,
  review: V15Review,
  patches: PatchFile | null = null,
  citedSources: CitedSource[] = [],
): Promise<VerifyStageResult> {
  // Stable ids for the referee's additions: a condition seen before keeps its id across passes.
  const idsPath = path.join(args.runDir, VERIFY_FILES.addedIds);
  const stableIds: Record<string, string> = existsSync(idsPath) ? JSON.parse(await readFile(idsPath, "utf8")) : {};
  const { core, added } = buildCore(transcribed, { patches, review, symbols: review.symbols ?? null, addedIds: stableIds });
  await writeJsonAtomic(idsPath, stableIds);
  // `allowBookkeeping`: the conditions just added carry the verify-only `bookkeeping` provenance
  // tag, which the gate rejects for every other caller (see gate.ts G6).
  // `verbatim`: the referee writes a pinned reading in the paper's own words, and the
  // builder-facing prose rules (banned connectives) are not a reason to stop a PASS.
  const gate = runStructuralGate(core, { allowBookkeeping: true, verbatim: true });
  const addedIds = added.map((a) => a.id);
  const onAdded = (v: { where: string }): boolean => addedIds.some((id) => v.where.startsWith(id));
  // A residual G2 complaint about a referee-authored condition (an omnibus sentence) is a
  // style note on a suggestion, not a broken core: record it, keep the core.
  const blocking = gate.violations.filter((v) => !(v.code === "G2" && onAdded(v)));
  for (const v of gate.violations.filter((v) => v.code === "G2" && onAdded(v))) {
    args.log(`note: referee-authored ${v.where} — ${v.message} (kept; a suggestion, not a hypothesis of the paper)`);
  }
  if (blocking.length > 0) {
    // Never persist a core the gate rejects: the operator's recovery is to fix the core
    // or the source and re-enter, not to inherit a broken one.
    return {
      status: "checkpoint",
      message:
        `V1.5 PASS but the structural gate rejects the core after adding ${added.length} ` +
        `bookkeeping assumption(s); core.json NOT written. Violations: ` +
        blocking.map((v) => `${v.code} @ ${v.where}: ${v.message}`).join(" | "),
    };
  }
  await writeCoreJson(corePath, core);
  const verify = args.state.verify!;
  verify.core_sha256 = await sha256File(corePath);
  args.state.stage_completed = "V1.5";
  for (const node of review.nodes) {
    if (node.correctness === "unclear") record(args.state, node.id, "note", node.detail, null);
    if (node.ambiguity === "pinned" && node.reading) {
      record(args.state, node.id, "note", `pinned reading: ${node.reading.reading} (${node.reading.evidence})`, null);
    }
  }
  // The symbol table as corrected, and the symbol readings the paper leaves open (a pinned symbol
  // reading is the symbol's entry in the table).
  for (const v of review.symbols ?? []) {
    if (v.meaning === "drift" && v.fix) {
      record(args.state, `${SYMBOL_PIN_OF}${v.name}`, "note", `symbol table corrected: ${[v.fix.type ? `type "${v.fix.type}"` : "", v.fix.space ? `space "${v.fix.space}"` : "", v.fix.def ? `def "${v.fix.def}"` : ""].filter(Boolean).join(", ")} (${v.detail})`, null);
    }
    if (v.ambiguity === "unresolvable") record(args.state, `${SYMBOL_PIN_OF}${v.name}`, "note", `symbol reading left open by the paper: ${v.detail}`, null);
  }
  // Every cited result on record, with what it was checked against.
  for (const c of citedSources ?? []) {
    record(args.state, c.nodeId, "note", c.mode === "unavailable" ? `cited source NOT checked: ${c.detail}` : `cited source checked: ${c.detail}`, null);
  }
  // The confirming pass accepted the patched core: every patch is a confirmed repair.
  if (patches) await recordPatches(args, patches, () => true);
  else recordUnaddressed(args, null);
  // The "as printed" text the report quotes must be the one this review saw.
  const transcribedPath = path.join(args.runDir, VERIFY_FILES.coreTranscribed);
  verify.transcribed_sha256 = existsSync(transcribedPath) ? await sha256File(transcribedPath) : null;
  const unclear = review.nodes.filter((n) => n.correctness === "unclear").length;
  return {
    status: "completed",
    message:
      `PASS over ${review.nodes.length} node(s): ${counts(review.nodes)}; ` +
      (patches ? `${patches.patches.length} patch(es) confirmed, ${patches.unfixable.length} descoped; ` : "") +
      `${added.length} bookkeeping assumption(s) applied` +
      (added.length > 0 ? ` (${added.map((a) => `${a.id}→${a.node}`).join(", ")})` : "") +
      `; ${unclear} unresolved note(s) recorded.`,
  };
}

/**
 * THE SYMBOL PASS (`referee_symbols.ts`), before any node is graded. The table graded is the one V1
 * transcribed (patches never touch it). Its verdicts go to `v1_5_symbols.json` (and the cache to
 * `state.verify.confirmed_symbols`), then `core.json` is rebuilt so the table carries the fixes.
 * Returns the rebuilt core, the readings the statement referees must see, and — per statement — the
 * symbol readings binding it (part of its verdict basis: a changed reading re-opens the verdict).
 */
async function symbolPass(p: {
  args: VerifyStageArgs;
  transcribed: Core;
  patches: PatchFile | null;
  flatTex: string;
  envs: EnvsJson | null;
  lineMap: FlatTexLineMap | null;
  ask: (c: RefereeCall) => Promise<unknown>;
}): Promise<
  | { ok: true; core: Core; symbols: V15SymbolVerdict[]; metrics: SymbolMetrics; readings: SymbolReadings; basisExtra: Map<string, BasisExtraValue>; basisExtraEarlier: Map<string, BasisExtraValue> }
  | { ok: false; message: string; metrics: SymbolMetrics }
> {
  const { args } = p;
  const verify = args.state.verify!;
  const read = (f: string): Promise<string> => readFile(path.join(PROMPT_DIR, f), "utf8");
  const symbolsBrief = await read("symbols.txt");
  const source = buildCore(p.transcribed, { patches: p.patches }).core;
  // A symbol read from a statement a repair corrects is re-graded against the corrected text (C5).
  const corrected = correctedStatements(p.transcribed, p.patches);
  const res = await runSymbolPass({
    core: source,
    corrected,
    px: paperIndex(p.flatTex, p.lineMap, p.envs),
    lineMap: p.lineMap,
    prior: await readSymbolFixes(args.runDir),
    confirmed: verify.confirmed_symbols ?? {},
    priorComplete: priorPassComplete(await readPriorReview(path.join(args.runDir, VERIFY_FILES.v15Review)), verify),
    ...(args.refereeMaxConcurrent ? { concurrency: args.refereeMaxConcurrent } : {}),
    ...(args.refereeSymbolEffort ? { effort: args.refereeSymbolEffort } : {}),
    briefs: { symbols: symbolsBrief },
    scope: scopeLine(verify.targets),
    ask: p.ask,
    tex: { runDir: args.runDir, mainFile: verify.source.main_file, log: args.log },
    log: args.log,
  });
  args.log(symbolLogLine(res.metrics));
  await appendPipelineLog(args, { stage: "V1.5", status: res.ok ? "symbol_pass" : "symbol_pass_failed", duration_ms: res.metrics.wall_ms, message: `${symbolLogLine(res.metrics)}; ${res.metrics.calls.length} call(s), ${res.metrics.shard_bytes} prompt bytes${res.ok ? "" : `; ${res.message}`}` });
  if (!res.ok) return res;
  await writeJsonAtomic(path.join(args.runDir, VERIFY_FILES.v15Symbols), { symbols: res.symbols });
  verify.confirmed_symbols = res.confirmed;
  // The verdicts and their keys go on record together: a crash before the stage's next save would
  // leave the file's new bases under the state's old keys, and every symbol graded again.
  if (!args.dryRun) await saveState(args.repoRoot, args.qid, args.state);
  const drift = res.symbols.filter((v) => v.meaning === "drift" && v.fix);
  const pinned = res.symbols.filter((v) => v.ambiguity === "pinned" && v.reading);
  const open = res.symbols.filter((v) => v.ambiguity === "unresolvable");
  if (drift.length + pinned.length + open.length > 0) {
    args.log(
      `symbol verdicts: ${drift.length} table fix(es)${drift.length ? ` (${drift.map((v) => v.name).join(", ")})` : ""}, ` +
        `${pinned.length} pinned reading(s)${pinned.length ? ` (${pinned.map((v) => v.name).join(", ")})` : ""}, ` +
        `${open.length} left open${open.length ? ` (${open.map((v) => v.name).join(", ")})` : ""}`,
    );
  }
  await rebuildPatchedCore(args.runDir, { detectHandEdits: false });
  // The core graded: the patch file's (as `core.json`), with any suggestion graded as a patch and
  // the symbol verdicts applied to its table — which is also the core the readings bind through
  // (a pinned reading is the symbol's `def`; `compileSymbolEdits`).
  const binding = buildCore(p.transcribed, { patches: p.patches, symbols: res.symbols }).core;
  const core = parseTypedCore(JSON.stringify(binding), "graded core");
  const basisExtra = symbolBasisExtra(binding, res.symbols);
  return { ok: true, core, symbols: res.symbols, metrics: res.metrics, readings: { binding, unresolved: open }, basisExtra, basisExtraEarlier: symbolBasisExtra(binding, res.symbols, { earlier: true }) };
}

/** The `pipeline.jsonl` line of one sharded referee pass: its outcome, wall time, and the call count
 * and prompt bytes the `sharded referee:` log line carries. */
function refereePassEntry(res: ShardedResult): Parameters<typeof appendPipelineLog>[1] {
  const m = res.metrics;
  const status = !res.ok ? "referee_pass_failed" : res.paused ? "referee_pass_paused" : "referee_pass";
  return { stage: "V1.5", status, duration_ms: m.wall_ms, message: `${shardLogLine(m)}; ${m.calls.length} call(s), ${m.total_bytes} prompt bytes${res.ok ? "" : `; ${res.message}`}` };
}

/** What one V1.5 pass cost: prompt bytes and wall time per referee call (`v1_5_referee_metrics.json`;
 * the referee evaluation harness reads it). A pass with no node to grade records no call. */
async function writeRefereeMetrics(runDir: string, m: ShardMetrics | { calls: []; total_bytes: 0; wall_ms: 0; symbols: SymbolMetrics }): Promise<void> {
  await writeJsonAtomic(path.join(runDir, VERIFY_FILES.v15RefereeMetrics), m);
}

/** The sharded referee's inputs for this pass (live or dry: only `ask` differs). */
async function runSharded(p: {
  runDir: string;
  core: Core;
  index: CoreIndex;
  flatTex: string;
  envs: EnvsJson | null;
  prompt: PromptInputs;
  toGrade: string[];
  carried: V15NodeVerdict[];
  patches: PatchFile | null;
  hasPatches: boolean;
  rejections: FixerRejection[];
  ask: (c: RefereeCall) => Promise<unknown>;
  log: (m: string) => void;
  /** A delta global pass reads the whole paper (the transcription changed since a global pass last
   * read it whole), else the excerpts of the nodes it checks. */
  globalPaperWhole: boolean;
  symbolReadings?: SymbolReadings;
  concurrency?: number;
  limits?: VerifyStageArgs["refereeShardLimits"];
  /** The verdicts on file of the nodes to grade (a node set aside past its retry keeps its own). */
  prior?: ReadonlyMap<string, V15NodeVerdict>;
  /** `state.verify.paper_errors`: what a repaired statement's printed form got wrong. */
  paperErrors?: VerifyState["paper_errors"];
  /** Fix as you go (`referee_shards.ts`): the pause rule, and the delta a pass after a pause confirms first. */
  pauseOn?: ShardedRefereeInput["pauseOn"];
  delta?: ShardedRefereeInput["delta"];
  onDelta?: ShardedRefereeInput["onDelta"];
  onHalt?: ShardedRefereeInput["onHalt"];
  settle?: ShardedRefereeInput["settle"];
  amendable?: ShardedRefereeInput["amendable"];
  /** The chain (`BasisPartition.onGraded`): the carried verdicts a level's final verdicts re-open. */
  onGraded?: ShardedRefereeInput["onGraded"];
}): Promise<ShardedResult> {
  const read = (f: string): Promise<string> => readFile(path.join(PROMPT_DIR, f), "utf8");
  const [shard, globalBrief] = await Promise.all([read("shard.txt"), read("global.txt")]);
  const lineMapPath = path.join(p.runDir, VERIFY_FILES.flatLineMap);
  const lineMap = existsSync(lineMapPath) ? (JSON.parse(await readFile(lineMapPath, "utf8")) as FlatTexLineMap) : null;
  const px = paperIndex(p.flatTex, lineMap, p.envs);
  const touched = repairedNodes(p.hasPatches ? p.patches : null);
  const owed = clarityOwed(p.core, p.hasPatches ? p.patches : null, p.paperErrors);
  const shardVerdicts = (vs: V15NodeVerdict[]): string =>
    section(
      "SHARD VERDICTS (every node's grade, one per line, empty fields omitted; `graded: carried` = an earlier pass's verdict on the unchanged node)",
      vs.map(verdictLine).join("\n"),
    );
  return runShardedReferee({
    core: p.core,
    flatTex: p.flatTex,
    envs: p.envs,
    lineMap,
    toGrade: p.toGrade,
    totalNodes: p.index.ids.size,
    scope: scopeLine(p.prompt.targets),
    briefs: { base: p.prompt.base, shard },
    extraSections: (ids) => [
      ...texFeedbackSection(p.prompt.texFeedback, ids),
      ...priorErrorsSection(p.prompt.priorErrors, ids),
      ...priorConditionsSection(p.prompt.priorConditions, ids),
      ...citedSection(p.prompt.citedSources, ids),
      // A shard prints each node it grades as the paper prints it (when located).
      // … and each repaired statement's proof change in its record (`compactCore`), not in PATCHES again.
      ...patchesSection(p.prompt, ids, ...shardPatchArgs(p.core, px, ids)),
      ...warningsSection(p.prompt.lintWarnings, { ids, places: sourcePlaces(p.core, p.envs, ids) }),
    ],
    globalPrompt: (vs, scope) =>
      globalPromptText(
        { ...p.prompt, base: `${globalBrief.trimEnd()}\n\n${globalBriefOf(p.prompt.base, { patches: p.hasPatches })}` },
        p.core,
        shardVerdicts(vs),
        p.index.ids,
        scope ? { ids: scope.shown, full: scope.full, paper: p.globalPaperWhole ? null : globalPaperExcerpts(px, p.core, [...scope.shown].filter((id) => scope.full.has(id))) } : null,
      ),
    keyResults: p.hasPatches ? (p.patches?.key_results ?? []) : [],
    carried: p.carried,
    isPatchPart: (id) => touched.has(id),
    hasPatches: p.hasPatches,
    rejections: p.rejections,
    contract: async (review, owes, o) => [
      ...contractViolations(review, p.index, o.patches, owes, o.rejections, p.hasPatches ? p.patches : null, true, owed),
      ...(await refereeTexViolations(review.nodes, { runDir: p.runDir, log: p.log })),
    ],
    texCheck: (fields) => texFieldViolations(fields.map((f) => ({ ...f, kind: "note" as const })), { runDir: p.runDir, log: p.log }),
    ask: p.ask,
    log: p.log,
    knownIds: p.index.ids,
    ...(p.symbolReadings ? { symbols: p.symbolReadings } : {}),
    ...(p.concurrency ? { concurrency: p.concurrency } : {}),
    ...(p.limits ? { limits: { ...DEFAULT_SHARD_LIMITS, ...p.limits } } : {}),
    ...(p.pauseOn ? { pauseOn: p.pauseOn } : {}),
    ...(p.delta ? { delta: p.delta } : {}),
    ...(p.onDelta ? { onDelta: p.onDelta } : {}),
    ...(p.settle ? { settle: p.settle } : {}),
    ...(p.amendable ? { amendable: p.amendable } : {}),
    ...(p.prior ? { prior: p.prior } : {}),
    ...(p.onHalt ? { onHalt: p.onHalt } : {}),
    ...(p.onGraded ? { onGraded: p.onGraded } : {}),
    // A repair on file: the statement's text in the core is its corrected form.
    repairOf: repairOnFile(p.core, p.hasPatches ? p.patches : null, p.paperErrors),
  });
}

export const runStageV1_5: VerifyStage = async (args) => {
  const { runDir, log } = args;
  const verify = args.state.verify;
  if (!verify) {
    throw new Error("V1.5: state has no `verify` block — it was not seeded by `leansmith verify`.");
  }
  const corePath = path.join(runDir, VERIFY_FILES.coreJson);
  const flatPath = path.join(runDir, VERIFY_FILES.flatTex);
  const reviewPath = path.join(runDir, VERIFY_FILES.v15Review);

  // `core.json` is rebuilt from the transcription and the patch file first, so what gets reviewed
  // is exactly those two files (hand edits of either apply; a deleted patch file leaves the plain
  // transcription). A patch file that no longer fits the transcription, or a transcription that is
  // not a consistent graph, is the operator's to fix: a checkpoint, never a crash.
  const transcribed = await readTranscribedCore(runDir);
  /** A receipt of suggestions awaiting the owner: the pass stops after the symbol pass — unless the
   * round that wrote it changed the core elsewhere too (`unconfirmed`): then this pass grades the nodes
   * as well (the receipt's own nodes stay out of the core, as printed) and the receipt is presented
   * only when it leaves nothing for the fixer (`settledForOwner`). */
  let awaitingOwner: string | null = null;
  const confirming = verify.weakening_repair?.status === "pending" && verify.weakening_repair.unconfirmed === true;
  // The patch file on disk (read once; the settled file replaces it below when a suggestion is
  // applied) and the paper's units (a repair resolves on them; a fixer note quotes its failing step).
  let onFile = await readPatchFile(runDir);
  const unitSrc = await repairSources(runDir);
  // A re-extraction may have unwired a hypothesis a repair drops: that entry is moot and leaves the file.
  if (onFile) {
    const pruned = withoutMootDrops(transcribed, onFile);
    if (pruned.removed.length > 0) {
      log(`V1.5: ${VERIFY_FILES.patches}: a dropped hypothesis the result no longer uses is taken out of its \`drops\` — ${pruned.removed.join("; ")}`);
      await writeJsonAtomic(path.join(runDir, VERIFY_FILES.patches), pruned.file);
      onFile = pruned.file;
    }
  }
  {
    const onDisk = onFile;
    if (onDisk) {
      // Every error in the ledger must still be addressed — a hand-written file cannot drop one — and
      // every repair's ops must still resolve on the paper (its texts are derived from them), and one
      // printed passage takes one replacement.
      const src = unitSrc;
      const bad = [
        ...validatePatchFile(transcribed, onDisk, openErrorIds(verify.paper_errors)),
        ...(src ? unresolvedRepairs(onDisk, src) : []),
        ...(src ? overlapViolations(onDisk, (node) => ({ units: src.units, passage: nodePassage(src, node) })) : []),
      ];
      // The same stop patch mode applies: a hand-edited file may not descope a key result's path.
      const blocked = bad.length === 0 ? blockedUnfixable(transcribed, onDisk) : [];
      if (blocked.length > 0) {
        bad.push(`${blocked.join(", ")} is unfixable on a key result's path, which ends the run — it cannot be descoped.`);
      }
      if (bad.length > 0) {
        return {
          status: "checkpoint",
          message: `${VERIFY_FILES.patches} does not fit the transcribed core: ${bad.join(" ")} Fix or delete it, then --resume.`,
        };
      }
      // A suggested (weakened) repair nobody has ruled on: on an intermediate result the runner
      // applies it now (this pass confirms it); on a main theorem it is the owner's, and no node is
      // reviewed until then — only the symbol table is graded (below), since the paper the owner
      // reads carries its readings.
      if (onDisk.unfixable.some(isPendingSuggestion)) {
        const settled = settleSuggestions(args.state, transcribed, onDisk, log);
        if (settled.narrowed.length > 0) {
          await writeJsonAtomic(path.join(runDir, VERIFY_FILES.patches), settled.file);
          await rebuildPatchedCore(runDir, { detectHandEdits: false });
          onFile = settled.file;
        }
        const rec = settled.receipt;
        if (rec) awaitingOwner = `${rec.items.length} suggested repair(s) that weaken a main theorem await the owner (${rec.items.map((i) => i.node).join(", ")}).`;
      }
    }
    let rebuilt: Awaited<ReturnType<typeof rebuildPatchedCore>>;
    try {
      rebuilt = await rebuildPatchedCore(runDir);
    } catch (err) {
      if (!(err instanceof CoreGraphInputError)) throw err;
      return {
        status: "checkpoint",
        message: `${err.file} cannot be built into a core: ${err.problems.join(" ")} Fix it (a transcription fix belongs in ${VERIFY_FILES.coreRefs}, then --from-stage V1 rebuilds the transcription from it; a repair in ${VERIFY_FILES.patches}, then --resume).`,
      };
    }
    if (rebuilt.handEdited) {
      log(
        `WARNING: ${VERIFY_FILES.coreJson} ${rebuilt.handEdited === "unknown" ? "differs from its rebuild and no write of the runner's is on record (a run from before that record: built by an earlier version, or edited by hand)" : "had been edited by hand"}; it is rebuilt from ${VERIFY_FILES.coreTranscribed}` +
          `${rebuilt.patched ? ` + ${VERIFY_FILES.patches}` : ""} and the file as it was kept as ${VERIFY_FILES.coreJson}.prev. ` +
          `A transcription fix belongs in ${VERIFY_FILES.coreRefs} (then --from-stage V1).`,
      );
    }
  }
  // Fail-closed reads: a missing or unparseable core/paper is an error, never an empty
  // prompt section — a referee handed no paper would grade everything `ok`.
  let core = parseTypedCore(await readFile(corePath, "utf8"), `verify core ${corePath}`);
  const flatTex = await readFile(flatPath, "utf8");
  let index = indexCore(core);
  // A receipt awaiting its confirming pass: each suggested repair on it is graded as a patch (its
  // weakening accepted, its note graded), so the owner is shown only a suggestion the referee checked.
  const receiptNodes = new Set(confirming && verify.weakening_repair?.status === "pending" ? verify.weakening_repair.items.map((i) => i.node) : []);
  const patches = onFile && receiptNodes.size > 0 ? applySuggestions(onFile, receiptNodes) : onFile;
  const hasPatches = !!patches && (patches.patches.length > 0 || patches.unfixable.length > 0);
  // F-stage findings the fixer rejected: this pass rules on each (never skipped, never in a dry run,
  // where no fixer is called).
  const pendingRejections = args.dryRun ? [] : (verify.fixer_rejections ?? []);

  log(
    `reviewing ${core.statements.length} statement(s), ${core.assumptions.length} ` +
      `assumption(s), ${core.definitions.length} definition(s) against ${flatPath}`,
  );

  const envsPath = path.join(runDir, VERIFY_FILES.envsJson);
  const envs = existsSync(envsPath) ? (JSON.parse(await readFile(envsPath, "utf8")) as EnvsJson) : null;
  const lineMapPath = path.join(runDir, VERIFY_FILES.flatLineMap);
  const lineMap = existsSync(lineMapPath) ? (JSON.parse(await readFile(lineMapPath, "utf8")) as FlatTexLineMap) : null;
  const base = await readFile(PROMPT_FILE, "utf8");
  /** One live referee call (a symbol call, a shard, the global pass). */
  const liveAsk = async (c: RefereeCall): Promise<unknown> => {
    const t0 = Date.now();
    const effort = c.effort ?? "high";
    const saved = await persistRefereePrompt(runDir, c.tag, c.prompt);
    log(`referee ${c.tag} (${c.kind}; ${MODELS.codexVerify}, ${effort}): ${Buffer.byteLength(c.prompt, "utf8")} bytes of prompt, ${c.nodes.length} ${c.kind.startsWith("symbol") ? "symbol" : "node"}(s)${saved ? `, prompt ${path.relative(runDir, saved)}` : ", prompt NOT persisted"}`);
    const res = await args.deps.runCodex({
      prompt: c.prompt,
      cwd: runDir,
      model: MODELS.codexVerify,
      reasoningEffort: effort,
      leanLsp: false,
      sandboxMode: "read-only",
      outputSchema: c.schema,
    });
    log(`referee ${c.tag} returned in ${Math.round((Date.now() - t0) / 1000)}s`);
    await persistCodexRaw(runDir, `v1_5_${c.tag}`, res.stdout);
    return expectStringJsonOutput(res.stdout);
  };

  // THE SYMBOL PASS, before any node is graded: the table's fixes are applied (core.json rebuilt)
  // and its pinned readings bind every statement using the symbol.
  /** The cited results' sources, resolved before any node is graded (the level settle reads them). */
  let citedSources: CitedSource[] = [];
  const shardOpts = {
    ...(args.refereeMaxConcurrent ? { concurrency: args.refereeMaxConcurrent } : {}),
    ...(args.refereeShardLimits ? { limits: args.refereeShardLimits } : {}),
    paperErrors: verify.paper_errors ?? {},
    // The owner's rulings bind inside the levels (the same two rules the merged review gets below).
    settle: (vs: V15NodeVerdict[]): V15NodeVerdict[] => {
      // A citation declared inaccessible is taken on the paper's word before the levels above see it.
      vs = settleUnavailableCited(vs, citedSources);
      const g = governByOwnerRulings(args.state, hasPatches ? honourAcceptedWeakening(vs, patches!, receiptNodes) : vs, findingNode(core));
      if (g.overruled.length > 0) log(`the referee re-raised ${g.overruled.length} finding(s) the owner withdrew (${g.overruled.join(", ")}) — overruled, recorded as notes`);
      // A condition kept from an earlier pass is part of the grade the levels above are shown (and
      // their bases hold): kept here, not only on the merged review.
      return keepEarlierConditions(g.nodes, prior);
    },
    // THE CHAIN: a result whose verdict now reads otherwise re-opens the carried verdicts using it.
    onGraded: (final: ReadonlyMap<string, V15NodeVerdict>, graded: readonly string[]): string[] => {
      const reopened = part.onGraded(final, graded);
      if (reopened.length > 0) log(`delta review: ${reopened.length} carried verdict(s) re-opened — a result they use changed its verdict in this pass (${idList(reopened, 12)})`);
      return reopened;
    },
  };
  const sp = await symbolPass({ args, transcribed, patches, flatTex, envs, lineMap, ask: args.dryRun ? syntheticSymbolAsk() : liveAsk });
  if (!sp.ok) {
    await writeRefereeMetrics(runDir, { calls: [], total_bytes: 0, wall_ms: 0, symbols: sp.metrics });
    return { status: "checkpoint", message: `${args.dryRun ? "dry run: " : ""}V1.5 symbol referee: ${sp.message}; no verdict was recorded.` };
  }
  if (awaitingOwner && confirming) log(`${awaitingOwner} This pass grades each suggestion as a repair first (and the round's other changes); the receipt is presented when nothing is left for the fixer.`);
  if (awaitingOwner && !confirming) {
    // The paper the owner reads carries the readings just graded (the review's symbol table, which the
    // annotated paper renders; its node verdicts stand).
    const onFile = await readPriorReview(reviewPath);
    if (onFile) await writeJsonAtomic(reviewPath, { ...onFile, symbols: sp.symbols });
    return { status: "checkpoint", message: `${awaitingOwner} The symbol table is graded (${sp.metrics.graded} afresh, ${sp.metrics.carried} carried); no node is reviewed until the owner rules.` };
  }
  core = sp.core;
  index = indexCore(core);
  const symbolMetrics = sp.metrics;
  /** The confirming pass (each suggestion graded as a repair) leaves nothing for the fixer: in place
   * of the acceptance, the receipt is presented (the verdicts are on file; the pass after the owner's
   * answer carries them). */
  const settledForOwner = (): VerifyStageResult | null => {
    const rec = verify.weakening_repair;
    if (!awaitingOwner || !confirming || rec?.status !== "pending") return null;
    const { unconfirmed: _u, ...presented } = rec;
    verify.weakening_repair = presented;
    return { status: "checkpoint", message: `the suggestions and the round's other changes are confirmed; nothing is left for the fixer. ${awaitingOwner}` };
  };

  let prior = await readPriorReview(reviewPath);
  // A condition is never an inline cited leaf's to carry (the contract refuses the grade): a
  // `bookkeeping` verdict on file for one, from before that rule, is neither carried nor kept — the
  // leaf is graded afresh.
  if (prior) {
    const leaves = inlineLeaves(core);
    const old = new Set(prior.nodes.filter((n) => leaves.has(n.id) && n.correctness === "bookkeeping").map((n) => n.id));
    for (const id of old) if (verify.confirmed) delete verify.confirmed[id];
    if (old.size > 0) prior = { ...prior, nodes: prior.nodes.map((n) => (old.has(n.id) ? { ...n, basis: undefined, correctness: "ok" as const, bookkeeping_assumption: null } : n)) };
  }
  // A delta global pass reads the whole paper only when the transcription moved since a global pass
  // last read it whole (`V15Review.global_paper`).
  const transcribedSha = existsSync(path.join(runDir, VERIFY_FILES.coreTranscribed)) ? await sha256File(path.join(runDir, VERIFY_FILES.coreTranscribed)) : null;
  const priorGlobalPaper = prior?.global_paper ?? null;
  const globalPaperWhole = transcribedSha === null || priorGlobalPaper !== transcribedSha;
  /** What a PATCHES section reads of the run, for every prompt of the pass and for the bases of the
   * nodes shown one (`repairBasis`): a dry run prints no transcribed text beside a repair. */
  const patchInputs: PatchInputs = {
    patches,
    paperErrors: verify.paper_errors ?? {},
    ...(args.dryRun
      ? {}
      : {
          printed: hasPatches ? new Map(transcribed.statements.map((st) => [st.id, st.statement] as const)) : undefined,
          hypotheses: hasPatches ? new Map([...transcribed.assumptions.map((a) => [a.id, a.condition] as const), ...transcribed.definitions.map((d) => [d.id, d.construction] as const)]) : undefined,
        }),
    ...(unitSrc ? { quoteOf: unitSrc.units.textById } : {}),
  };
  /** The delta partition. `cited`: the cited sources' basis extra (the live path; none in a dry run).
   * A cache recorded under another basis scheme reproduces no basis: it is dropped, and every node
   * graded afresh — but scheme 4, whose verdicts are carried over one by one (`partitionByBasis`:
   * TRANSITION; a verdict says which scheme its basis is of, so a pass that stops before it writes
   * the review loses nothing). */
  const partition = async (cited: BasisExtra): Promise<BasisPartition> => {
    const onFile = verify.confirmed_scheme ?? 1;
    if (onFile !== BASIS_SCHEME && Object.keys(verify.confirmed ?? {}).length + Object.keys(verify.level_pause?.carry ?? {}).length > 0) {
      if (onFile === 4) log(`verdict bases: the cache was recorded under basis scheme 4: each verdict whose scheme-4 basis still holds is carried over to scheme ${BASIS_SCHEME}, with no call`);
      else {
        log(`verdict bases: the cache was recorded under basis scheme ${onFile}, not ${BASIS_SCHEME}: every node is graded afresh`);
        verify.confirmed = {};
        if (verify.level_pause) verify.level_pause.carry = {};
      }
    }
    verify.confirmed_scheme = BASIS_SCHEME;
    const extra = mergeBasisExtra(mergeBasisExtra(cited, ownReadingsExtra(core)), sp.basisExtra);
    // A node's own material: the repairs its shard shows it (scheme 4: its fixer note, `noteBasis`).
    const repairs = repairBasis(patchInputs, core, paperIndex(flatTex, lineMap, envs));
    const notes = noteBasis(hasPatches ? patches : null);
    const shown = shownVerdictOf(core, repairOnFile(core, hasPatches ? patches : null, verify.paper_errors ?? {}));
    const legacy = { own: notes, complete: priorPassComplete(prior, verify), earlierExtra: mergeBasisExtra(cited, sp.basisExtraEarlier) };
    const first = partitionByBasis(core, verify.confirmed ?? {}, prior, extra, verify.level_pause?.carry ?? {}, repairs, shown, legacy);
    if (args.dryRun || first.carried.length === 0) return first;
    // A verdict carried on an unchanged basis whose texts do not compile is graded afresh.
    const fellBack = [...new Set((await storedTexFeedback(first.carried.map((n) => n.id), prior, { runDir, mainFile: verify.source.main_file, log })).map((x) => x.node))];
    if (fellBack.length === 0) return first;
    log(`referee texts: ${fellBack.length} carried verdict(s) with a text that does not compile are graded afresh (${idList(fellBack, 8)})`);
    for (const id of fellBack) {
      if (verify.confirmed) delete verify.confirmed[id];
      if (verify.level_pause?.carry) delete verify.level_pause.carry[id];
    }
    const next = partitionByBasis(core, verify.confirmed ?? {}, prior, extra, verify.level_pause?.carry ?? {}, repairs, shown, legacy);
    // The fallen-back nodes re-grade because a text does not compile, whatever else the breakdown says.
    for (const id of fellBack) {
      const c = regradeCause({ inputs: first.inputs.get(id), clean: true }, next.inputs.get(id)!);
      next.why.causes[c] = Math.max(0, (next.why.causes[c] ?? 0) - 1);
      if (next.why.causes[c] === 0) delete next.why.causes[c];
      next.why.causes["text does not compile"] = (next.why.causes["text does not compile"] ?? 0) + 1;
    }
    return next;
  };
  const logPartition = (p: { carried: V15NodeVerdict[]; toGrade: string[]; why: RegradeBreakdown }): void => {
    log(
      `delta review: ${p.toGrade.length} of ${index.ids.size} node(s) to grade afresh` +
        (p.toGrade.length > 0 && p.toGrade.length < index.ids.size ? ` (${idList(p.toGrade, 12)})` : "") +
        `, ${p.carried.length} verdict(s) carried on an unchanged basis`,
    );
    log(regradeBreakdownLine(p.why));
  };

  // FIX AS YOU GO (sharded referee): a level with a node the fixer or the owner must answer stops the
  // upward grading; a pass after a pause grades the repaired nodes first (`referee_shards.ts`).
  const levelPause = verify.level_pause ?? null;
  const fixAsYouGo = {
    ...(args.refereeFixAsYouGo === false ? {} : { pauseOn: pauseRule(verify, core, hasPatches ? patches : null) }),
    // A halt hands on no repair to confirm, only what it graded.
    ...(levelPause && levelPause.errors.length > 0
      ? {
          delta: levelPauseDelta(levelPause, hasPatches ? patches : null),
          onDelta: (final: ReadonlyMap<string, V15NodeVerdict>, stopped: readonly string[]) => log(deltaLine(levelPause, final, stopped, core, hasPatches ? patches : null)),
        }
      : {}),
    ...(levelPause
      ? {
          // Carried on the paused passes' bases (`partitionByBasis` checks it): the global pass of
          // the pass that reaches the top checks them with its own grades.
          amendable: new Set(levelPause.graded ?? Object.keys(levelPause.carry)),
        }
      : {}),
  };
  let part: BasisPartition;
  let review: V15Review;
  /** The sharded referee ran this pass (its global pass too, unless it paused). */
  let refereeRan = false;
  let paused: ShardedPause | null = null;
  /** Nodes set aside past their retry (`referee_shards.ts`): no grade of this pass, their verdict on
   * file kept unconfirmed; the pass goes on, but it neither accepts nor refutes over them. */
  let setAside: Array<{ id: string; why: string }> = [];
  /** A HALT KEEPS WHAT THE PASS GRADED: the verdicts stand on the next pass while their basis holds,
   * whatever their grade (`LevelPause.carry`, the fix-as-you-go machinery; a clean one is cached in
   * `confirmed` too), and its global pass checks them (`graded`). A pause on file keeps its errors. */
  const holdCarry = (ids: readonly string[], at: string): void => {
    const lp = verify.level_pause;
    const carry = { ...(lp?.carry ?? {}) };
    // A verdict this pass carried stands on the basis it was carried on (re-keyed, when carried over
    // from scheme 4), one it graded on the basis it was graded on.
    for (const id of [...part.carried.map((v) => v.id).filter((id) => id in carry), ...ids]) {
      const b = part.bases.get(id);
      if (b) carry[id] = b;
    }
    for (const id of part.reopened) if (!ids.includes(id)) delete carry[id];
    const graded = [...new Set([...(lp ? (lp.graded ?? Object.keys(lp.carry)) : []), ...ids.filter((id) => id in carry)])];
    verify.level_pause = lp ? { ...lp, carry, graded } : { level: at, errors: [], via: "halt", round: 0, carry, graded, at: new Date().toISOString() };
  };
  /** The review and cache of a halted pass: what it graded, fresh, with the verdicts it carried and
   * the ones on file of the nodes it did not reach (those graded afresh next pass), then saved. */
  const keepGraded = async (graded: V15NodeVerdict[], at: string): Promise<void> => {
    if (graded.length === 0) return;
    const done = new Set(graded.map((n) => n.id));
    const toGrade = new Set(part.toGrade);
    // … but for a verdict the chain re-opened: the line it was given under no longer stands.
    const rest = (prior?.nodes ?? []).filter((n) => toGrade.has(n.id) && !done.has(n.id) && !part.reopened.has(n.id));
    const merged = mergeCarried(core, graded, [...part.carried, ...rest], part, verify.confirmed ?? {}, prior);
    verify.confirmed = merged.confirmed;
    verify.confirmed_scheme = BASIS_SCHEME;
    await writeJsonAtomic(reviewPath, { ...(prior ?? { verdict: "FAIL", summary: "" }), nodes: merged.nodes, symbols: sp.symbols });
    holdCarry([...done], at);
    if (!args.dryRun) await saveState(args.repoRoot, args.qid, args.state);
    log(`halted at ${at}: ${graded.length} verdict(s) graded before the halt kept (${idList([...done], 12)}); the next pass carries them and grades the rest`);
  };

  if (args.dryRun) {
    // The same delta rule as a live pass, with a synthetic `ok` in place of the referee's grade
    // (a synthetic `error` on each `dryRunSyntheticErrors` node not yet patched).
    part = await partition(new Map());
    logPartition(part);
    let fresh: V15NodeVerdict[] = [];
    let pausedReview: V15Review | null = null;
    if (part.toGrade.length > 0) {
      const synthetic = new Set(args.dryRunSyntheticErrors ?? []);
      const patchedNodes = new Set((patches?.patches ?? []).map((p) => p.node));
      const noteOwed = clarityOwed(core, hasPatches ? patches : null, verify.paper_errors);
      // The referee's whole wiring (grouping, excerpts, prompts, the global pass, the merge) with a
      // synthetic referee in place of the model.
      const res = await runSharded({
        runDir,
        core,
        index,
        flatTex,
        envs,
        prompt: {
          base,
          flatTex,
          targets: verify.targets,
          lintWarnings: await readV1Warnings(runDir),
          ...patchInputs,
          citedSources: [],
          rejections: [],
          symbolReadings: sp.readings,
        },
        toGrade: part.toGrade,
        carried: part.carried,
        patches,
        hasPatches,
        rejections: [],
        ask: syntheticAsk(hasPatches, {
          errorOn: (id) => synthetic.has(id) && !patchedNodes.has(id),
          gradeNote: (id) => noteOwed.has(id),
        }),
        log,
        globalPaperWhole,
        symbolReadings: sp.readings,
        ...shardOpts,
        ...fixAsYouGo,
      });
      res.metrics.symbols = symbolMetrics;
      log(shardLogLine(res.metrics));
      await appendPipelineLog(args, refereePassEntry(res));
      await writeRefereeMetrics(runDir, res.metrics);
      if (!res.ok) return { status: "checkpoint", message: `dry run: ${res.message}` };
      if ((res.metrics.set_aside ?? []).length > 0) return { status: "checkpoint", message: `dry run: node(s) set aside: ${res.metrics.set_aside!.map((x) => x.id).join(", ")}` };
      fresh = res.review.nodes;
      if (res.paused) {
        paused = res.paused;
        pausedReview = res.review;
      }
    } else {
      await writeRefereeMetrics(runDir, { calls: [], total_bytes: 0, wall_ms: 0, symbols: symbolMetrics });
    }
    if (!pausedReview) {
      delete verify.level_pause;
      const merged = mergeCarried(core, fresh, part.carried, part, verify.confirmed ?? {}, prior);
      verify.confirmed = merged.confirmed;
      verify.confirmed_scheme = BASIS_SCHEME;
      const dryReview: V15Review = {
        verdict: "PASS",
        summary: `dry run — no referee was called; the core is accepted unreviewed (${fresh.length} node(s) graded synthetically, ${part.carried.length} carried).`,
        nodes: merged.nodes,
        symbols: sp.symbols,
      };
      await writeJsonAtomic(reviewPath, dryReview);
      const forOwner = settledForOwner();
      if (forOwner) {
        verify.dry_run = true;
        return forOwner;
      }
      verify.core_sha256 = await sha256File(corePath);
      // The acceptance is synthetic: mark the run so no live stage ever builds on it.
      verify.dry_run = true;
      args.state.stage_completed = "V1.5";
      // The ledger and the patch file are the run's, not the referee's: they are recorded as a live
      // acceptance records them, so a dry report shows what the repairs and descopings would be.
      if (hasPatches) await recordPatches(args, patches!, () => true);
      else recordUnaddressed(args, null);
      return {
        status: "completed",
        message: `dry run: synthetic PASS, core accepted unreviewed (${fresh.length} graded, ${part.carried.length} carried).`,
      };
    }
    // A synthetic error paused the grading: the pause is handed on exactly as a live one.
    verify.dry_run = true;
    review = pausedReview;
  } else {
    // CITED RESULTS are checked against their SOURCE, fail-closed: a citation is where the referee
    // would otherwise take the paper's word, so a result with no checkable source stops here for
    // the user to supply one — it never passes on the paper's quote.
    const resolved = await resolveCitedSources({
      runDir,
      core,
      envs,
      fetchBytes: args.deps.fetchBytes,
    });
    citedSources = resolved.sources;
    const citedMissing = resolved.missing;
    if (citedMissing.length > 0) {
      return {
        status: "checkpoint",
        message:
          `V1.5 needs the source of ${citedMissing.length} cited result(s) before it can review the paper — a cited ` +
          "result is checked against the cited work itself, never against the paper's quotation of it. For each, " +
          "put the cited statement (its text or tex, copied from the cited work) in the file named, then --resume. " +
          `A cited work nobody can access: write what was tried to the same path with \`${UNAVAILABLE_SUFFIX}\` in place of ` +
          "`.txt` — the run then continues with that citation taken as printed, NOT checked, and reported so:\n" +
          citedMissing.map((m) => `  - ${m.nodeId} (${m.key} @ ${m.locator}; ${m.why}) → ${m.file}\n      ${m.citation}`).join("\n"),
      };
    }
    if (citedSources.length > 0) log(`cited sources: ${citedSources.map((c) => `${c.nodeId} (${c.mode})`).join(", ")}`);
    const lintWarnings = await readV1Warnings(runDir);
    // A repair's proof may invoke a published result the paper's proof does not: a fact for the referee.
    // (only on a run that accounts for inline citations: a run from before it is graded as it was)
    if (patches && (verify.citation_accounting === true || inlineLeaves(core).size > 0)) lintWarnings.lint.push(...repairCitationWarnings(core, patches.patches, revisesProof));
    const warningCount = lintWarnings.lint.length + lintWarnings.parser.length;
    if (warningCount > 0) {
      log(
        `${warningCount} V1 warning(s) appended for the referee to confirm ` +
          `(${lintWarnings.lint.length} lint, ${lintWarnings.parser.length} parser)`,
      );
    }
    // THE DELTA. A cited leaf's basis includes the source it is checked against: a changed or newly
    // supplied source re-opens its verdict.
    part = await partition(new Map(citedSources.map((c) => [c.nodeId, `${c.key}@${c.locator}\n${c.text}`] as const)));
    logPartition(part);
    const toGradeSet = new Set(part.toGrade);
    // Nothing moved and the key-result list the last pass approved is the one on file: every verdict
    // is carried and there is nothing to ask the referee.
    const carriedPatchReview =
      hasPatches && prior?.patch_review?.key_results_ok && prior.patch_review.basis === patchReviewBasis(patches!)
        ? prior.patch_review
        : null;
    if (part.toGrade.length === 0 && (!hasPatches || carriedPatchReview) && pendingRejections.length === 0) {
      log("no node changed since the last pass: every verdict is carried, no referee call");
      review = {
        verdict: "PASS",
        summary: "no node changed since the last pass; every verdict is carried.",
        nodes: [],
        patch_review: carriedPatchReview,
      };
      await writeRefereeMetrics(runDir, { calls: [], total_bytes: 0, wall_ms: 0, symbols: symbolMetrics });
    } else {
      const promptInputs: PromptInputs = {
        base,
        flatTex,
        targets: verify.targets,
        lintWarnings,
        ...patchInputs,
        citedSources,
        rejections: pendingRejections,
        symbolReadings: sp.readings,
        texFeedback: await storedTexFeedback(part.toGrade, prior, { runDir, mainFile: verify.source.main_file, log }),
        priorErrors: await priorErrorLines(runDir, part.toGrade),
        // … of every node: a verdict re-opened in the pass is shown its own too (a shard reads its nodes').
        priorConditions: priorConditionLines(prior, [...index.ids]),
      };
      if ((promptInputs.priorErrors ?? []).length > 0) log(`${promptInputs.priorErrors!.length} error(s) recorded on an earlier transcription of the nodes to grade go in the prompt to be checked again`);
      if ((promptInputs.texFeedback ?? []).length > 0) log(`${promptInputs.texFeedback!.length} text(s) on file of the nodes to grade do not compile — the compiler's lines go in the prompt`);
      const res = await runSharded({
        runDir,
        core,
        index,
        flatTex,
        envs,
        prompt: promptInputs,
        toGrade: part.toGrade,
        carried: part.carried,
        patches,
        hasPatches,
        rejections: pendingRejections,
        ask: liveAsk,
        symbolReadings: sp.readings,
        log,
        globalPaperWhole,
        prior: new Map((prior?.nodes ?? []).filter((n) => toGradeSet.has(n.id)).map((n) => [n.id, n] as const)),
        onHalt: keepGraded,
        ...shardOpts,
        ...fixAsYouGo,
      });
      res.metrics.symbols = symbolMetrics;
      log(shardLogLine(res.metrics));
      await appendPipelineLog(args, refereePassEntry(res));
      await writeRefereeMetrics(runDir, res.metrics);
      if (!res.ok) {
        return { status: "checkpoint", message: `V1.5 sharded referee: ${res.message}; the verdicts graded before it are kept for the next pass.` };
      }
      review = res.review;
      refereeRan = true;
      paused = res.paused ?? null;
      setAside = res.metrics.set_aside ?? [];
      const aside = new Set(setAside.map((x) => x.id));
      // A paused pass owes the levels it graded; the key results and the fixer rejections are the
      // global pass's, which runs once the grading reaches the top. A node set aside is owed nothing.
      // (`part.toGrade` as the pass left it: the verdicts it re-opened are owed too.)
      const violations = paused
        ? contractViolations(review, index, false, new Set(review.nodes.map((n) => n.id)), [], hasPatches ? patches : null, false)
        : contractViolations(review, index, hasPatches, new Set(part.toGrade.filter((id) => !aside.has(id))), pendingRejections, hasPatches ? patches : null, false);
      if (violations.length > 0) {
        await keepGraded(review.nodes, "the merged review");
        return { status: "checkpoint", message: `V1.5 sharded referee: the merged review breaks the contract (${violations.join(" ")}); the verdicts graded are kept for the next pass.` };
      }
    }
  }
  // The grading reached the top: no pause stands.
  if (!paused) delete verify.level_pause;

  // A degenerate witness is no error of the paper: its exclusion becomes a bookkeeping condition.
  {
    const settled = review.nodes.map(settleDegenerateWitness);
    const moved = settled.filter((n, i) => n !== review.nodes[i]).map((n) => n.id);
    if (moved.length > 0) log(`${moved.length} error(s) with a degenerate witness recorded as bookkeeping exclusions, not errors: ${moved.join(", ")}`);
    review = { ...review, nodes: settled };
  }
  // A repair the owner accepted as a weakening is judged on whether it holds, not on whether it weakens.
  if (hasPatches) review = { ...review, nodes: honourAcceptedWeakening(review.nodes, patches!, receiptNodes) };
  // A citation declared inaccessible is taken on the paper's word (its verdict says it was not checked).
  review = { ...review, nodes: settleUnavailableCited(review.nodes, citedSources) };
  // A finding the owner withdrew (`--reject-finding`) is not raised again: the error is overruled.
  {
    const g = governByOwnerRulings(args.state, review.nodes, findingNode(core));
    if (g.overruled.length > 0) log(`the referee re-raised ${g.overruled.length} finding(s) the owner withdrew (${g.overruled.join(", ")}) — overruled, recorded as notes`);
    review = { ...review, nodes: g.nodes };
  }
  // The persisted review is the whole core: this pass's fresh grades plus the carried verdicts,
  // each with its basis; the cache records every fresh clean grade and withdraws every other one.
  {
    // A node set aside keeps its verdict on file, without a basis and out of the cache: never carried
    // (nor carried by a pause), so the next pass grades it afresh.
    const aside = new Set(setAside.map((x) => x.id));
    const kept = (prior?.nodes ?? []).filter((n) => aside.has(n.id)).map(({ basis: _b, ...n }) => ({ ...n, graded: "carried" as const }));
    const merged = mergeCarried(core, review.nodes, [...part.carried, ...kept], part, verify.confirmed ?? {}, prior);
    for (const id of aside) delete merged.confirmed[id];
    verify.confirmed = merged.confirmed;
    verify.confirmed_scheme = BASIS_SCHEME;
    review = {
      ...review,
      nodes: merged.nodes,
      ...(review.patch_review && hasPatches ? { patch_review: { ...review.patch_review, basis: patchReviewBasis(patches!) } } : {}),
    };
  }
  // THE one place a finding on an inline cited leaf becomes its host's: everything below — the
  // routing, a revise directive, what halts, what is persisted — reads these verdicts.
  const inline = inlineLeaves(core);
  const onHost = new Map(review.nodes.flatMap((n) => (n.correctness === "error" && inline.has(n.id) ? [[n.id, inline.get(n.id)!.host] as const] : [])));
  review = { ...review, nodes: errorsOnHosts(followsRepair(review.nodes, core, hasPatches ? patches : null), inline, prior?.nodes) };
  const r = routeReview(review, hasPatches ? patches : null, resultIds(core));
  let computed = computeVerdict(review.nodes.map((n) => (r.paperDrift(n) || n.faithfulness !== "drift" ? n : { ...n, faithfulness: "ok" as const })));
  if (computed !== review.verdict && !paused) {
    log(
      `WARNING: referee claimed verdict ${review.verdict}, the node grades give ${computed}; ` +
        "using the computed verdict.",
    );
  }
  // A global pass that ran (no pause) over every node, or over a delta with the whole paper, read it whole.
  const readWhole = refereeRan && !paused && (part.carried.length === 0 || globalPaperWhole);
  review = {
    ...review,
    verdict: computed,
    symbols: sp.symbols,
    ...(paused ? { paused: { level: paused.tag, ids: paused.ids, ungraded: paused.ungraded } } : {}),
    global_paper: readWhole ? transcribedSha : priorGlobalPaper,
  };
  await writeJsonAtomic(reviewPath, review);
  log(`verdict ${computed} over ${review.nodes.length} node(s) (${counts(review.nodes)})${paused ? ` — paused at level ${paused.tag}, ${paused.ungraded.length} node(s) above wait` : ""}`);
  const asideList = setAside.map((x) => `${x.id} — ${x.why}`).join(" | ");
  if (setAside.length > 0) log(`${setAside.length} node(s) set aside this pass, graded afresh next pass: ${asideList}`);
  /** The pass neither accepts nor refutes over a node it could not grade: it halts there instead
   * (every other verdict is on file; the next pass grades only what was set aside). */
  const heldBySetAside = (): { status: "checkpoint"; message: string } | null => {
    if (setAside.length === 0) return null;
    // Every verdict this pass gave stands on the next one, whatever its grade.
    holdCarry(review.nodes.filter((n) => n.graded === "fresh").map((n) => n.id), "the end of the pass");
    return {
      status: "checkpoint",
      message: `${setAside.length} node(s) broke the output contract twice and were set aside (${asideList}); every other verdict is recorded, so the pass would otherwise conclude — --resume grades the set-aside node(s) afresh, the rest carried.`,
    };
  };

  // A paused pass answers exactly the nodes that stopped the grading: the rest of what it graded
  // (an `unclear` step, a minimality grade, an ambiguity) waits for the pass that reaches the top.
  // (An error that stopped it on an inline cited leaf stands on the leaf's host.)
  const pausedIds = new Set((paused?.ids ?? []).flatMap((id) => [id, ...(onHost.has(id) ? [onHost.get(id)!] : [])]));
  const ro = paused ? routeReview({ ...review, nodes: review.nodes.filter((n) => pausedIds.has(n.id)), patch_review: null }, hasPatches ? patches : null, resultIds(core)) : r;
  const { keyObjection, unconfirmed, unchecked, patchDrift, unclearNotes } = ro;
  // A cited result the referee could not check against the source shown (the statement is not in
  // it, or the source is the wrong version) is the user's to settle — only the cited work can.
  const unavailableIds = new Set(citedSources.filter((c) => c.mode === "unavailable").map((c) => c.nodeId));
  const citedIds = new Set(core.statements.filter((st) => st.status === "cited" && !unavailableIds.has(st.id)).map((st) => st.id));
  const citedUnchecked = r.unchecked.filter((n) => citedIds.has(n.id));
  if (citedUnchecked.length > 0) {
    const sourceOf = (id: string): string => {
      const src = core.statements.find((st) => st.id === id)?.source;
      return src ? ` ([${src.cite}, ${src.locator}] → ${CITED_SOURCES_DIR}/${sourceFileKey(src.cite)}.txt)` : "";
    };
    return {
      status: "checkpoint",
      message:
        `the referee could not check ${citedUnchecked.length} cited result(s) against the source shown: ` +
        citedUnchecked.map((n) => `${n.id}${sourceOf(n.id)} — ${n.detail}`).join(" | ") +
        `. Put the exact statement of each result named, copied from the cited work, in its file, then --from-stage V1.5.`,
    };
  }

  // FIXER REJECTIONS of F-stage findings, ruled on by this pass (not by one that sends the core
  // back for transcription: the ruling waits for a faithful core). Upheld: the paper grants what the
  // finding says it lacks — a note, and the same finding on the same statement is a note from now
  // on. Overruled: the finding stands, joins the ledger, and the fixer must patch it (a round).
  const overruled: Objection[] = [];
  if (!paused && computed !== "REVISE" && pendingRejections.length > 0) {
    const rulings = new Map((review.rejection_verdicts ?? []).map((v) => [v.node, v] as const));
    const ledger = { ...(verify.paper_errors ?? {}) };
    for (const fr of pendingRejections) {
      const v = rulings.get(fr.node)!;
      if (v.upheld) {
        record(
          args.state,
          fr.node,
          "note",
          `${fr.from_stage} finding rejected by the fixer, and the referee upheld the rejection: ${fr.reason} ` +
            `(where the paper grants it: ${fr.where_the_paper_grants_it}; referee: ${v.detail}). The finding: ${fr.finding}`,
          null,
          { stage: fr.from_stage },
        );
        verify.rejected_rewinds = [
          ...(verify.rejected_rewinds ?? []),
          { node: fr.node, axis: fr.axis, stage: fr.from_stage, route: "fixer rejection", detail: fr.finding, reason: fr.reason, by: "fixer+referee", at: new Date().toISOString() },
        ];
        log(`fixer rejection of the ${fr.from_stage} finding on ${fr.node} UPHELD by the referee — recorded as a note`);
      } else {
        if (!(fr.node in ledger)) {
          ledger[fr.node] = fr.axis === "clarify" ? { detail: fr.finding, witness: null, kind: "clarification" } : { detail: fr.finding, witness: fr.witness };
        }
        overruled.push({
          id: fr.node,
          axis: fr.axis,
          detail: `${fr.finding} — the fixer rejected it (${fr.reason}); the referee OVERRULED the rejection: ${v.detail}. Patch it.`,
          witness: fr.witness,
          from_stage: fr.from_stage,
          overruled: true,
        });
        log(`fixer rejection of the ${fr.from_stage} finding on ${fr.node} OVERRULED by the referee — the fixer must patch it`);
      }
    }
    verify.paper_errors = ledger;
    verify.fixer_rejections = [];
  }

  const allChecked = unconfirmed.length === 0 && unchecked.length === 0;
  // The form of a repair: asked of the fixer once, in a refinement round — never at that counter's cap
  // (nothing halts for a remark), never while the grading is paused. Else the report notes it.
  const form = splitRequests(r, hasPatches ? patches : null, new Set(verify.split_requests ?? []), receiptNodes);
  const splitDue = paused || atCap(verify, "refinement", null) ? [] : form.ask;
  const umbrellaNodes = new Set((hasPatches ? patches!.patches : []).filter(isUmbrellaPatch).map((p) => p.node));
  const noteSplitRemarks = (): void => {
    for (const n of [...form.noted, ...form.ask.filter((x) => !splitDue.includes(x))]) record(args.state, n.id, "note", `${umbrellaNodes.has(n.id) ? "the result stands as an umbrella over its propositions; the referee would keep a main claim as its statement" : "the corrected statement stands as one statement; the referee would state it as a general statement with corollaries"}: ${n.split!.why.trim()}`, null);
  };
  if (!paused && computed === "PASS" && !keyObjection && allChecked && patchDrift.length === 0 && unclearNotes.length === 0 && overruled.length === 0 && splitDue.length === 0) {
    const held = heldBySetAside();
    if (held) return held;
    noteSplitRemarks();
    return settledForOwner() ?? acceptCore(args, transcribed, corePath, review, hasPatches ? patches : null, citedSources);
  }

  // The revise loop fixes TRANSCRIPTION defects and is bounded. Drift left at the last allowed
  // round is ours (the core could not be made to say what the paper says): a checkpoint, never
  // a verdict about the paper — what the referee graded on that core is provisional.
  // Drift that REPEATS on a node after a revise round is not going to converge: the agent
  // was told exactly what to change and could not, so a lint rule, a prompt clause or the
  // parser is forbidding the correct transcription. Stop now, name the nodes, hand the run
  // to the orchestrator — the cap is for drift that is still moving.
  // The revise cap, per drifting node: the most rounds any of them has had.
  const driftIds = review.nodes.filter(r.paperDrift).map((n) => n.id);
  const reviseSpent = Math.max(0, ...driftIds.map((id) => verify.v1_5_rounds_by_node?.[id] ?? 0));
  const reviseCapped = reviseSpent >= MAX_REVISE_ROUNDS_PER_NODE || verify.v1_5_rounds >= patchBackstop(core);
  // None of this drift was handed to a revise round (`last_drift`): a cap reached then was spent before it.
  const driftUntold = !driftIds.some((id) => id in (verify.last_drift ?? {}));
  if (computed === "REVISE") {
    // Drift held against a node whose words are the paper's, over how a result reads a symbol: the
    // transcriber writes neither the symbol table nor a repair, so a revise round (a transcriber call,
    // and every symbol graded again) would return the same core. The orchestrator rules, at once.
    const unrevisable = readingDrift(review.nodes, r.paperDrift, core, transcribed);
    if (unrevisable.length > 0) {
      log(`drift on ${unrevisable.length} node(s) no transcription round can remove — stopping: ${unrevisable.join(", ")}`);
      for (const id of unrevisable) if (verify.last_drift) delete verify.last_drift[id];
      delete verify.level_pause;
      return {
        status: "checkpoint",
        message:
          `drift on ${unrevisable.join(", ")} with no edit named, on a node whose record is the transcribed one and that a scoped symbol ` +
          `reading of a result using it reaches — no transcription round is started. Read its detail in discovery/v1_5_review.json and rule: ` +
          `it holds a symbol reading or a repair against the node (not a finding of the paper), and they stand → a plain --resume (the node ` +
          `is graded afresh; a pending owner receipt stands) — once: on a second such checkpoint for the node, tag the reading's clauses in ` +
          `discovery/v1_5_symbols.json with the repaired result alone, then --resume; the reading is wrong → correct it there, a repair → ` +
          `discovery/patches.json, then --resume; it names a defect of the transcription itself → discovery/core_refs.json, then --resume --from-stage V1 ` +
          `(that re-entry sets a pending owner receipt aside).`,
      };
    }
    const drift: Record<string, string> = {};
    for (const n of review.nodes) if (r.paperDrift(n)) drift[n.id] = hasDriftFix(n.fix) ? JSON.stringify(n.fix) : "";
    const last = verify.last_drift ?? {};
    const repeated = Object.keys(drift).filter((id) => id in last && last[id] === drift[id]);
    if (repeated.length > 0) {
      log(`drift repeated on ${repeated.length} node(s) after a revise round — stopping: ${repeated.join(", ")}`);
      delete verify.level_pause;
      return {
        status: "checkpoint",
        message:
          `drift REPEATED on ${repeated.join(", ")} after a revise round — the agent was told what to change and ` +
          `could not; a lint rule, prompt clause or parser boundary is blocking the correct transcription. ` +
          `Read the referee's detail in discovery/v1_5_review.json, fix the pipeline (general rule + test) or ` +
          `hand-patch discovery/core_refs.json, then --resume --from-stage V1.`,
      };
    }
    // Recorded only when a revise round will carry it: on the last allowed round no directive is
    // written, so nothing is told to V1 and a later pass must not read this drift as repeated.
    if (reviseCapped) delete verify.last_drift;
    else verify.last_drift = drift;
    // A transcription round comes first: the pass after it grades afresh what it does not carry.
    delete verify.level_pause;
  } else {
    delete verify.last_drift;
  }

  const finalRound = computed === "REVISE" && reviseCapped;
  if (finalRound) {
    const drift = review.nodes.filter(r.paperDrift);
    const unresolvable = review.nodes.filter((n) => n.ambiguity === "unresolvable");
    const errors = review.nodes.filter((n) => n.correctness === "error");
    for (const node of drift) {
      record(args.state, node.id, "note", `transcription drift left after ${verify.v1_5_rounds} revise round(s): ${node.detail}`, null);
    }
    log(
      `revise cap reached (${reviseSpent} of ${MAX_REVISE_ROUNDS_PER_NODE} on a drifting node, ${verify.v1_5_rounds} of ${patchBackstop(core)} in all): ` +
        `${drift.length} drift left, ${errors.length} error(s), ${unresolvable.length} unresolvable`,
    );
    // Drift is never accepted: the errors graded on an unfaithful core are provisional, so the run
    // stops for the operator rather than reporting a verdict.
    return {
      status: "checkpoint",
      message:
        (driftUntold
          ? `drift at ${drift.length} node(s) with no revise round left for it, and none was run on it — ${spentCapLine(drift, verify.v1_5_rounds_by_node ?? {}, verify.v1_5_rounds, patchBackstop(core))}`
          : `V1 could not make the core faithful at ${drift.length} node(s) after ${verify.v1_5_rounds} revise round(s) — ` + drift.map((n) => n.id).join(", ")) +
        `. Read discovery/v1_5_review.json: fix the pipeline if the finding is its own (general rule + test), then --resume --from-stage V1.5; ` +
        `or fix discovery/core_refs.json by hand, then --resume --from-stage V1.` +
        (errors.length + unresolvable.length > 0 ? ` The ${errors.length} error(s) and ${unresolvable.length} unresolvable reading(s) graded on this core are provisional and go to the fixer once it is faithful.` : ""),
    };
  }

  if (computed === "REVISE") {
    const findings = review.nodes.flatMap((node) => {
      const out: Array<{ id: string; axis: "faithfulness" | "correctness (provisional)"; detail: string; fix?: DriftFix | null }> = [];
      if (r.paperDrift(node)) {
        // A structured `fix` is applied by the V1 runner itself; the prose goes to the agent
        // only when no fix is given or it could not be applied.
        const setting = (node.fix?.setting ? ` The setting the core's sampling_model must state for it: ${node.fix.setting}` : "") + (node.fix?.also ? ` ${node.fix.also}` : "");
        out.push({ id: node.id, axis: "faithfulness", detail: `${node.detail}${setting}`, fix: hasDriftFix(node.fix) ? node.fix : null });
      }
      if (node.correctness === "error") {
        out.push({
          id: node.id,
          axis: "correctness (provisional)",
          detail:
            `${node.detail} — refuted under the CURRENT core; make sure every hypothesis and setup ` +
            `definition the paper imposes on this result is transcribed, then the referee re-judges it. ` +
            `witness: ${node.witness ?? ""}`,
        });
      }
      return out;
    });
    // The round is charged here, to each drifting node (the runner only re-enters V1).
    verify.v1_5_rounds += 1;
    verify.v1_5_rounds_by_node = { ...(verify.v1_5_rounds_by_node ?? {}), ...Object.fromEntries(driftIds.map((id) => [id, (verify.v1_5_rounds_by_node?.[id] ?? 0) + 1])) };
    await writeJsonAtomic(path.join(runDir, VERIFY_FILES.v1ReviseDirective), {
      round: verify.v1_5_rounds,
      findings,
    });
    return {
      status: "revise",
      message:
        `REVISE: ${findings.length} finding(s) on ${new Set(findings.map((f) => f.id)).size} ` +
        `node(s) written to ${VERIFY_FILES.v1ReviseDirective}; core.json unchanged (revise round ${reviseSpent + 1}/${MAX_REVISE_ROUNDS_PER_NODE} on its drifting nodes).`,
    };
  }

  const objections = onSplitParent(paused ? routeHypotheses(objectionsOf(ro, core), core) : [...objectionsOf(r, core), ...overruled], patches);
  const drifting = review.nodes.some(r.paperDrift);
  // The pause, recorded with whatever this pass hands on (a round, an owner halt, a cap halt): the
  // next pass carries every verdict it gave on an unchanged basis and confirms the repair first.
  const recordPause = (via: LevelPause["via"], round: number): void => {
    if (!paused) return;
    // An error on a corollary a repair split off is answered on its parent.
    // … and one on a published result a proof invokes by citation, on that proof's result (`errorsOnHosts`).
    const owner = (id: string): string => splitCorollaries(patches).get(id)?.parent ?? onHost.get(id) ?? id;
    const errors = [...new Set(paused.ids.map(owner))].map((id) => ({ id, targets: [id] }));
    const answered = new Set([...paused.ids, ...errors.flatMap((e) => [e.id, ...e.targets])]);
    const carry: Record<string, string> = {};
    for (const n of review.nodes) if (n.basis && !answered.has(n.id)) carry[n.id] = n.basis;
    // Graded in this logical pass: this pass's fresh grades and what the pause before it had graded.
    const before = new Set(levelPause ? (levelPause.graded ?? Object.keys(levelPause.carry)) : []);
    const graded = review.nodes.filter((n) => n.id in carry && (n.graded === "fresh" || before.has(n.id))).map((n) => n.id);
    verify.level_pause = { level: paused.tag, errors, via, round, carry, graded, at: new Date().toISOString() };
    log(`level ${paused.tag}: ${errors.length} error(s) → ${via === "owner" ? "the owner" : via === "runner" ? "the runner's narrowing" : `fixer round ${round}`} (${errors.map((e) => `${e.id}${e.targets.join() === e.id ? "" : ` via ${e.targets.join(", ")}`}`).join("; ")}); the grading resumes there`);
  };
  // A repair that WEAKENS the claim never goes back to the fixer: when it is all this pass objects
  // to, the patch becomes a suggestion here. On an intermediate result the runner applies it (a
  // fresh pass confirms it); on a main theorem the run halts for the owner's ruling.
  const weakening = objections.filter((o) => o.weakens_contribution);
  if (!drifting && weakening.length > 0 && weakening.length === objections.length && ro.unresolvable.length === 0 && !keyObjection && patches) {
    log(`${weakening.length} confirmed repair(s) weaken the claim (${weakening.map((o) => o.id).join(", ")}) — turned into suggestions`);
    // The symbol readings graded against those corrected statements no longer describe the paper
    // (live DFM 2026-09-26): their confirmation goes, so the annotated paper leaves them out and the
    // next pass grades them afresh against what the owner decides.
    // Only a symbol a demoted correction says something of: one whose sentences the correction left
    // as printed reads nothing that goes (`correctionTouchesSymbol`, the test its basis is built on) —
    // or one whose reading NAMES a demoted result (`resultsNamedBy`): it describes the corrected form.
    const demoted = new Set(weakening.map((o) => o.id));
    const correctedNow = correctedStatements(transcribed, patches);
    for (const name of symbolsReadingDemoted(core, demoted, correctedNow, review.symbols ?? (await readSymbolFixes(runDir)))) delete verify.confirmed_symbols?.[name];
    // From the file on disk: a confirming pass grades the receipt's suggestions as applied in memory,
    // but they stay the owner's to decide (live CNS 2026-09-27: written from the in-memory file, a
    // pending suggestion was saved as an accepted weakening).
    const settled = settleSuggestions(args.state, transcribed, convertWeakeningPatches(onFile ?? patches, weakening), log);
    await writeJsonAtomic(path.join(runDir, VERIFY_FILES.patches), settled.file);
    const rec = settled.receipt;
    // A fresh pass confirms the narrowed intermediate results and grades each suggestion on a main
    // theorem before its receipt is presented.
    if (rec) verify.weakening_repair = { ...rec, unconfirmed: true };
    await rebuildPatchedCore(runDir, { detectHandEdits: false });
    verify.core_sha256 = null;
    recordPause("runner", roundsUsed(verify, "error"));
    return {
      status: "narrowed",
      message: `${settled.narrowed.length} intermediate result(s) narrowed${rec ? `, ${rec.items.length} suggestion(s) on a main theorem (${rec.items.map((i) => i.node).join(", ")})` : ""}; a fresh V1.5 pass confirms them${rec ? " before the owner's receipt is presented" : ""}.`,
    };
  }
  // PATCH ROUND. An error the paper does not correct itself, an unresolvable ambiguity, or a
  // disputed key-result list, on a faithful core: V1 in patch mode writes the smallest repair
  // that keeps the key contribution, and a fresh referee pass judges it. A round that only
  // refines a correct repair (every objection a minimality grade on a repaired node, or an
  // overruled clarification) spends a REFINEMENT round; any other spends an ERROR round. A round
  // due at its counter's cap halts for the orchestrator — it never fails the run (`caps.ts`).
  if (!drifting && splitDue.length > 0) {
    objections.push(...splitDue.map((n) => splitObjection(n, umbrellaNodes.has(n.id))));
    verify.split_requests = [...new Set([...(verify.split_requests ?? []), ...splitDue.map((n) => n.id)])];
    log(`${splitDue.length} confirmed repair(s) the referee would state as a general statement with corollaries (${splitDue.map((n) => n.id).join(", ")}) — the fixer is asked once; its answer stands`);
  }
  if (!drifting && (objections.length > 0 || ro.unresolvable.length > 0 || keyObjection)) {
    const findings = [
      ...objections.map(({ minimality: _m, note: _n, ...o }) => o),
      ...ro.unresolvable.map((n) => ({ id: n.id, axis: "ambiguity", detail: n.detail, witness: null })),
      ...(keyObjection ? [{ id: "run", axis: "key_results", detail: keyObjection, witness: null }] : []),
    ];
    const refinement = isRefinementRound(objections, { keyObjection: !!keyObjection, unresolvable: ro.unresolvable.length });
    const kind: PatchRoundKind = refinement ? "refinement" : "error";
    // A suggestion the referee objected to (or whose note it found unclear) leaves the receipt: the
    // fixer answers that node again.
    const back = [...receiptNodes].filter((id) => findings.some((f) => f.id === id));
    const rejectedOutright = (id: string): boolean => objections.some((o) => o.id === id && o.note !== true && o.minimality !== true);
    if (back.length > 0 && onFile) {
      // The suggestion leaves the patch file, so its first finding carries what the fixer answers
      // again: the paper's error the suggestion answered and the statement the referee rejected.
      for (const id of back) {
        const f = findings.find((x) => x.id === id)!;
        const e = verify.paper_errors?.[id];
        f.detail = `${f.detail}\n${FIXER_INSTRUCTIONS.openErrorLabel}${e?.detail ?? "(not recorded)"}${e?.witness ? ` Witness: ${e.witness}` : ""}`;
        // The suggestion as it stood, which the new entry replaces whole (the fixer's prompt shows it).
        const was = withdrawnRepair(onFile, id);
        if (was) (f as { withdrawn_repair?: WithdrawnRepair }).withdrawn_repair = was;
      }
      await withdrawSuggestions(runDir, args.state, onFile, back);
      log(`the suggested repair of ${back.join(", ")} goes back to the fixer: the referee did not confirm it`);
      // Counted when the referee rejected the weakening itself, not only its note or its minimality.
      const rejectedHere = back.filter(rejectedOutright);
      verify.suggestion_rejections = { ...(verify.suggestion_rejections ?? {}), ...Object.fromEntries(rejectedHere.map((id) => [id, (verify.suggestion_rejections?.[id] ?? 0) + 1])) };
    }
    // A suggestion rejected past its limit is the owner's: the round halts at a cap (no round spent).
    const stuck = back.filter((id) => rejectedOutright(id) && (verify.suggestion_rejections?.[id] ?? 0) > MAX_SUGGESTION_REJECTIONS);
    // An error round is charged to the level the grading paused at (the global pass: `global`).
    const scope = kind === "error" ? errorScope(verify, core, paused ? paused.ids : null) : null;
    await writeJsonAtomic(path.join(runDir, VERIFY_FILES.v1ReviseDirective), {
      mode: "patch",
      round: roundsUsed(verify, kind) + 1,
      findings,
    });
    const tally =
      (paused ? `level ${paused.tag}: ` : "") +
      `${ro.refuted.length} error(s)${refinement ? " (minimality only)" : ""}, ${unconfirmed.length} unconfirmed repair(s), ${unchecked.length} proof(s) to write out, ` +
      `${ro.unresolvable.length} unresolvable` +
      (overruled.length > 0 ? `, ${overruled.length} overruled fixer rejection(s)` : "") +
      (keyObjection ? ", key results disputed" : "");
    const capped = atCap(verify, kind, scope);
    if (stuck.length > 0 || capped) {
      verify.cap_reached = capRecord(verify, kind, "V1.5", findings.map((f) => ({ id: f.id, axis: f.axis, detail: f.detail, witness: f.witness ?? null })), patches, scope);
      if (stuck.length > 0) verify.cap_reached = { ...verify.cap_reached, suggestions: stuck, ...(capped ? {} : { suggestions_only: true }) };
      recordPause("fixer", roundsUsed(verify, kind) + 1);
      const why = [
        ...(stuck.length > 0 ? [`the referee rejected the suggested weakening of ${stuck.join(", ")} more than ${MAX_SUGGESTION_REJECTIONS} times`] : []),
        ...(capped ? [`a round is due at its cap: ${nextRound(verify, kind, scope)}`] : []),
      ].join("; ");
      log(`${why} — halting`);
      return {
        status: "checkpoint",
        message: `${tally} — ${why}; the patch directive is written, the run halts at the cap — the orchestrating agent's ruling (--clear-patch-cap / --accept-cap).`,
      };
    }
    log(`${nextRound(verify, kind, scope)}: ${findings.length} finding(s) for the fixer`);
    recordPause("fixer", roundsUsed(verify, kind) + 1);
    return {
      status: "patch",
      round_kind: kind,
      ...(scope ? { round_scope: scope } : {}),
      message: `${tally} — handed to V1 patch mode (${nextRound(verify, kind, scope)}).`,
    };
  }
  // SUBSTANTIVE FAILURE: drift left at the revise cap alongside the paper's errors.
  const held = heldBySetAside();
  if (held) return held;
  delete verify.level_pause;
  return recordFailure(args, r, review, index, onFile, objections, verify.patch_rounds ?? 0);
};

/** One objection the fixer must answer (a patch-directive finding). */
export interface Objection {
  id: string;
  axis: string;
  detail: string;
  witness: string | null;
  /** A repair graded correct but non-minimal. */
  minimality?: boolean;
  /** An F-stage finding whose fixer rejection the referee overruled. */
  overruled?: boolean;
  from_stage?: string;
  /** A repair that holds but weakens the paper's claim: it goes to the owner, not the fixer. */
  weakens_contribution?: boolean;
  /** A confirmed repair the fixer only writes again: its note the referee graded unclear, or its
   * form (`splitObjection`). */
  note?: boolean;
}

/**
 * FIX AS YOU GO — which nodes of a settled level stop the sharded referee's upward grading (user
 * decision 2026-09-24): a refuting `error` with an in-scope witness (not bookkeeping, not a
 * minimality or degenerate grade), and a repair graded as weakening the claim (the owner's). Not
 * one the owner withdrew or declined to repair, nor one the fixer declared unfixable (the error
 * stands; the results using it fall back to `unclear`), nor an error on a paper assumption no
 * statement uses any more (no result rests on it). In the DELTA confirmation, a repair the
 * referee could not reproduce (`unclear` on a repaired node) stops it
 * too: only a confirmed corrected form is used above.
 */
function pauseRule(verify: VerifyState, core: Core, patches: PatchFile | null): (verdicts: readonly V15NodeVerdict[], at: { delta: boolean }) => string[] {
  const touched = repairedNodes(patches);
  const declined = (id: string): boolean =>
    verify.paper_errors?.[id]?.owner_decision === "declined" || (patches?.unfixable ?? []).some((u) => u.node === id);
  const paperHypothesis = new Set([...core.assumptions, ...core.definitions].map((n) => n.id));
  const pendingReceipt = new Set(verify.weakening_repair?.status === "pending" ? verify.weakening_repair.items.map((i) => i.node) : []);
  const on = findingNode(core);
  return (verdicts, at) =>
    verdicts
      .filter((v0) => {
        const v = patches ? honourAcceptedWeakening([v0], patches, pendingReceipt)[0]! : v0;
        if (v.correctness === "error") {
          if (ownerRuling(verify, on(v.id)) || ownerRuling(verify, v.id) || declined(on(v.id)) || declined(v.id)) return false;
          if (v.weakens_contribution) return touched.has(v.id);
          if (v.minimality || v.witness_regime !== "in_scope") return false;
          return !paperHypothesis.has(v.id) || hypothesisUsers(core, v.id).length > 0;
        }
        return at.delta && v.correctness === "unclear" && touched.has(v.id);
      })
      .map((v) => v.id);
}

/** The DELTA a pass after a pause confirms first: the nodes the pause handed on (the repaired
 * nodes) and the results the round restated to follow them (`consequence_of`). */
function levelPauseDelta(lp: LevelPause, patches: PatchFile | null): string[] {
  const answered = new Set(lp.errors.flatMap((e) => [e.id, ...e.targets]));
  const out = new Set(answered);
  for (const p of patches?.patches ?? []) {
    if ((p.consequence_of ?? []).some((c) => answered.has(c))) out.add(p.node);
    // A repaired result is confirmed with the corollaries its repair splits off.
    if (answered.has(p.node)) for (const c of corollaryNodes(p.node, p)) out.add(c.id);
  }
  return [...out];
}

/** `level L2: 2 error(s) → fixer round 3 → confirmed 1/2; continuing`: how the delta settled. An
 * error is confirmed when no node of its repair stops the grading and every statement answering it
 * is still in the core and graded (not unfixable, not descoped). */
function deltaLine(lp: LevelPause, final: ReadonlyMap<string, V15NodeVerdict>, stopped: readonly string[], core: Core, patches: PatchFile | null): string {
  const inCore = new Set(core.statements.map((s) => s.id));
  const stop = new Set(stopped);
  const confirmed = lp.errors.filter((e) => {
    const group = levelPauseDelta({ ...lp, errors: [e] }, patches);
    const statements = e.targets.filter((t) => !t.startsWith("ass:") && !t.startsWith("def:"));
    return !group.some((id) => stop.has(id)) && statements.every((t) => inCore.has(t) && final.has(t));
  }).length;
  const by = lp.via === "owner" ? "the owner's ruling" : lp.via === "runner" ? "the runner's narrowing" : `fixer round ${lp.round}`;
  return (
    `level ${lp.level}: ${lp.errors.length} error(s) → ${by} → confirmed ${confirmed}/${lp.errors.length}; ` +
    (stopped.length > 0 ? `not confirmed: ${stopped.join(", ")} — back to the fixer before any level above` : "continuing")
  );
}

/**
 * A paused error on an assumption or definition of the PAPER is repaired by replacing its own printed
 * text (the fixer's PAPER UNITS show it); when the paper states it only in running prose, by restating
 * each result using it (consequential patches). The node's finding says which results use it. Pure.
 */
function routeHypotheses(objections: Objection[], core: Core): Objection[] {
  return objections.map((o) => {
    const line = hypothesisRepairLine(core, o.id);
    return line ? { ...o, detail: `${o.detail}\n${line}` } : o;
  });
}

/** A weakening grade on a repair accepted as a weakening (`accepted_weakening`: the owner's ruling
 * on a main theorem, the runner's narrowing of an intermediate result, or a suggestion awaiting the
 * owner that the confirming pass grades as applied, `pending`) is no objection: that is exactly what
 * was settled or is asked. It stands as a clean grade, the detail kept. */
function honourAcceptedWeakening(nodes: V15NodeVerdict[], patches: PatchFile, pending: ReadonlySet<string> = new Set()): V15NodeVerdict[] {
  const accepted = new Map<string, string>();
  for (const p of patches.patches) {
    if (!p.accepted_weakening) continue;
    const tag = pending.has(p.node) ? "[suggested weakening, awaiting the owner]" : p.narrowed_by === "runner" ? "[intermediate result narrowed]" : "[weakening accepted by the owner]";
    // The weakening accepted is the result's with its corollaries.
    for (const id of [p.node, ...corollaryNodes(p.node, p).map((c) => c.id)]) accepted.set(id, tag);
  }
  return nodes.map((n) =>
    n.weakens_contribution && n.correctness === "error" && accepted.has(n.id)
      ? { ...n, correctness: "ok" as const, witness: null, weakens_contribution: false, detail: `${accepted.get(n.id)} ${n.detail}` }
      : n,
  );
}

/**
 * The `error`s that follow a repair: the referee says the node fails only because a result it uses
 * was repaired and now states less (`follows_repair`), the node is not repaired itself, and it uses
 * directly a repaired node whose ops change its statement. The fixer makes it follow (a consequence
 * patch). Marked `follows_repair_of`. Pure.
 */
export function followsRepair(nodes: V15NodeVerdict[], core: Core, patches: PatchFile | null): V15NodeVerdict[] {
  const repaired = repairedNodes(patches);
  const restated = new Set((patches?.patches ?? []).filter((p) => (p.ops ?? []).some(isStatementOp)).map((p) => p.node));
  const deps = new Map(([...core.statements, ...core.assumptions, ...core.definitions] as Array<{ id: string; depends_on?: string[] }>).map((n) => [n.id, n.depends_on ?? []] as const));
  return nodes.map((n) => {
    if (n.correctness !== "error" || !n.follows_repair || repaired.has(n.id)) return n;
    const on = (deps.get(n.id) ?? []).filter((d) => restated.has(d));
    return on.length > 0 ? { ...n, follows_repair_of: on } : n;
  });
}

/** What the routing reads off a review of the core under its patches — the ONE classification the
 * live pass and the acceptance at a cap both use. */
interface Routing {
  patchedNodes: Set<string>;
  isPatchPart: (id: string) => boolean;
  paperDrift: (n: V15NodeVerdict) => boolean;
  patchDrift: V15NodeVerdict[];
  keyObjection: string | null;
  unconfirmed: V15NodeVerdict[];
  unchecked: V15NodeVerdict[];
  refuted: V15NodeVerdict[];
  unresolvable: V15NodeVerdict[];
  /** Confirmed repairs whose fixer note the referee graded unclear. */
  unclearNotes: V15NodeVerdict[];
  /** Errors that follow a repair (`follows_repair_of`): the fixer makes the result follow it. */
  consequences: V15NodeVerdict[];
  /** Confirmed repairs whose corrected statement the referee would split (`split`): a form remark. */
  splitRemarks: V15NodeVerdict[];
}

/** Whether a verdict leaves the node confirmed. */
const confirmedGrade = (n: V15NodeVerdict): boolean => n.correctness === "ok" || n.correctness === "bookkeeping";

/**
 * THE FORM OF A REPAIR (owner rule 2026-10-06). A corrected statement the fixer wrote that mixes a
 * general claim with special cases holding under their own conditions reads better as a general
 * statement with corollaries; the referee says so in `split`, on a repair it confirms. It is a remark,
 * never a grade: the repair stays confirmed. `ask` — the fixer is asked ONCE per result to re-emit the
 * same content split (a refinement round: no error round is spent, nothing halts, nothing goes to the
 * owner); `noted` — already asked (`asked`), so the fixer's answer stands and the report notes the
 * remark. Never on a statement the paper prints, on a repair accepted as a weakening (that text is the
 * owner's or the runner's narrowing) or awaiting the owner (`held`). Pure.
 */
export function splitRequests(r: Pick<Routing, "splitRemarks">, patches: PatchFile | null, asked: ReadonlySet<string>, held: ReadonlySet<string> = new Set()): { ask: V15NodeVerdict[]; noted: V15NodeVerdict[] } {
  const settled = new Set((patches?.patches ?? []).filter((p) => p.accepted_weakening).map((p) => p.node));
  const open = r.splitRemarks.filter((n) => !settled.has(n.id) && !held.has(n.id));
  return { ask: open.filter((n) => !asked.has(n.id)), noted: r.splitRemarks.filter((n) => !open.includes(n) || asked.has(n.id)) };
}

/** The fixer's finding for a form remark: the repair is confirmed; only its form is asked for —
 * a statement to separate (into blocks beside its main claim, or, when nothing in it is its own main
 * claim, into an umbrella), or (`umbrella`: the repair is one) an umbrella over a statement that has a
 * main claim, to restore it. */
export function splitObjection(n: V15NodeVerdict, umbrella = false): Objection {
  return {
    id: n.id,
    axis: "split",
    detail: umbrella
      ? `the repair is confirmed, but it states the result as an umbrella (\`umbrella: true\`) although the printed statement has a main claim of its own: ${n.split!.why.trim()} ` +
        "Return the same repair with that claim as the statement (the ops), `umbrella` null, and the other conclusions as its blocks (`corollaries`), nothing dropped; if nothing in the statement is its own main claim after all, return the entry as it is."
      : `the repair is confirmed, but its corrected statement is several results (a general claim with special cases, or conclusions resting on different conditions or results): ${n.split!.why.trim()} ` +
      "Return the same repair with the same content as the statement (the ops), keeping what is not moved, and one block per case, or per group of conclusions resting on the same conditions and results (`corollaries`), nothing dropped; when nothing in the statement is its own main claim (what the ops would keep is one more conclusion among the others), make it an umbrella instead: every conclusion a block, `umbrella: true`, no ops; if it is one claim after all, return the entry as it is.",
    witness: null,
    note: true,
  };
}

/** A patch round that only refines confirmed or correct repairs (a minimality grade, a note to write
 * again, a form remark, an overruled clarification): it spends a REFINEMENT round, never an error round. Pure. */
export function isRefinementRound(objections: readonly Objection[], other: { keyObjection: boolean; unresolvable: number }): boolean {
  return !other.keyObjection && other.unresolvable === 0 && objections.length > 0 && objections.every((o) => o.minimality === true || o.note === true || (o.overruled === true && o.axis === "clarify"));
}

const resultIds = (core: Core): Set<string> => new Set(core.statements.map((s) => s.id));

/** A drift fix that only adds or removes a use of another RESULT: the paper's own wiring, whatever
 * repair the node carries — the V1 runner applies it (a fixer cannot write a result edge). Pure. */
export function resultWiringOnly(fix: DriftFix | null | undefined, results: ReadonlySet<string>): boolean {
  if (!hasDriftFix(fix)) return false;
  const edges = [...(fix.add_depends_on ?? []), ...(fix.remove_depends_on ?? [])];
  return edges.length > 0 && edges.every((d) => results.has(d)) && !fix.wire_into?.length && !fix.unwire_from?.length && !fix.extend_to && !fix.new_assumption;
}

/** The drift a spent revise cap met before any round was run on it: per node, the rounds counted on
 * it (by earlier passes) and what the referee asks (a setting, edges, another edit, none named); then
 * the cap that is spent. Pure. */
export function spentCapLine(drift: readonly V15NodeVerdict[], byNode: Readonly<Record<string, number>>, rounds: number, backstop: number): string {
  const asks = (n: V15NodeVerdict): string =>
    [n.fix?.setting ? "a setting" : "", n.fix?.add_depends_on?.length || n.fix?.remove_depends_on?.length || n.fix?.wire_into?.length || n.fix?.unwire_from?.length ? "wiring" : "", n.fix?.extend_to || n.fix?.new_assumption ? "an edit of the text" : ""].filter(Boolean).join(" and ") || "no edit named";
  const nodes = drift.map((n) => `${n.id} (${byNode[n.id] ?? 0} of ${MAX_REVISE_ROUNDS_PER_NODE} round(s) counted on it by earlier passes; the referee asks ${asks(n)})`).join(", ");
  return `${nodes}; ${rounds} of ${backstop} round(s) in all`;
}

/**
 * Drift no transcription round can remove: on an assumption or definition whose record is the
 * transcribed one (no repair and no referee edit wrote it), with no edit named (`fix`), while a
 * scoped clause of a symbol it uses reaches it through a result using it (`applicableClauses`). The
 * node's words are the paper's; what the referee holds against them is how that result, as printed
 * or as repaired, reads the symbol — the symbol table's or the repair's matter, which V1 writes
 * neither of. Pure.
 */
export function readingDrift(nodes: readonly V15NodeVerdict[], paperDrift: (n: V15NodeVerdict) => boolean, core: Core, transcribed: Core): string[] {
  const record = (k: Core, id: string): string | null => {
    const n = [...k.assumptions, ...k.definitions].find((x) => x.id === id);
    return n ? JSON.stringify(Object.fromEntries(Object.entries(n).filter(([f]) => !(DERIVED_USER_FIELDS as readonly string[]).includes(f)).sort(([x], [y]) => (x < y ? -1 : 1)))) : null;
  };
  return nodes
    .filter((n) => paperDrift(n) && !n.fix?.setting && !hasDriftFix(n.fix) && record(core, n.id) !== null && record(core, n.id) === record(transcribed, n.id))
    .filter((n) => ((used) => core.symbols.some((x) => used.has(x.name) && applicableClauses(core, n.id, x.scoped).length > 0))(symbolsUsedByNode(core, n.id)))
    .map((n) => n.id);
}

/** The inline cited leaves of a core (`cited_in`): each with its host and the result it cites. One
 * whose host the core does not hold has nowhere to put a finding: none. */
export function inlineLeaves(core: Core): Map<string, { host: string; cite: string; locator: string }> {
  const held = new Set(core.statements.map((s) => s.id));
  return new Map(core.statements.flatMap((s) => (s.cited_in && s.source && held.has(s.cited_in) ? [[s.id, { host: s.cited_in, cite: s.source.cite, locator: s.source.locator }] as const] : [])));
}

/** The node a finding graded on `id` stands on: its host for an inline cited leaf (`errorsOnHosts`),
 * else itself — where the owner's rulings on it are looked up before the verdicts are moved. */
export function findingNode(core: Core): (id: string) => string {
  const inline = inlineLeaves(core);
  return (id) => inline.get(id)?.host ?? id;
}

/**
 * An `error` graded on an inline cited leaf is its HOST's: the leaf's text is a passage of the
 * host's proof, with nothing of its own to repair. The verdicts as the routing reads them: the error
 * stands on the host's verdict (one made of the leaf's when the host has none here — the grading
 * paused below it), the leaf is clean. An `unclear` stays: on such a leaf it says the source shown
 * lacks the cited result, which stops the run for the source. Both verdicts are left without a
 * basis, so neither is carried (nor carried by a pause): the leaf's grader reports the failure, so
 * the next pass asks it again and the finding stands exactly while it does. Pure.
 */
export function errorsOnHosts(nodes: readonly V15NodeVerdict[], inline: ReadonlyMap<string, { host: string; cite: string; locator: string }>, onFile: readonly V15NodeVerdict[] = []): V15NodeVerdict[] {
  const out = [...nodes];
  for (const leaf of nodes) {
    const at = inline.get(leaf.id);
    if (!at || leaf.correctness !== "error") continue;
    const detail = `the step its proof takes from [${at.cite}, ${at.locator}] (${leaf.id}) does not hold as the proof uses it: ${leaf.detail}`;
    out[out.findIndex((n) => n.id === leaf.id)] = { ...leaf, basis: undefined, correctness: "ok", witness: null };
    const h = out.findIndex((n) => n.id === at.host);
    const host = out[h] && { ...out[h], basis: undefined };
    // Only the error is the host's: nothing else the leaf's verdict carries (its basis, its flags).
    const theirs = { correctness: "error" as const, witness: leaf.witness, witness_regime: leaf.witness_regime, witness_instance: leaf.witness_instance };
    // (a host the grading did not reach keeps the condition appended to it on file, `onFile`)
    if (!host) out.push({ id: at.host, fix: null, faithfulness: "ok", ambiguity: "ok", reading: null, bookkeeping_assumption: onFile.find((n) => n.id === at.host && appendedCondition(n))?.bookkeeping_assumption ?? null, ...theirs, detail });
    // The host's own refuting error keeps its witness, the leaf's finding beside it.
    else if (isRefutingError(host)) out[h] = { ...host, detail: `${host.detail} Also: ${detail}`, ...(host.witness?.trim() ? {} : theirs) };
    // Any other grade of the host — a repair graded only non-minimal or weakening included — gives way
    // to the refuting error: the repair is not one to accept. (A condition appended to the host stays
    // on its verdict: `keepEarlierConditions`.)
    else out[h] = { ...host, ...theirs, minimality: false, weakens_contribution: false, detail: host.correctness === "unclear" || host.correctness === "error" ? `${detail} Also: ${host.detail}` : detail };
  }
  return out;
}

export function routeReview(review: V15Review, patches: PatchFile | null, results: ReadonlySet<string>): Routing {
  // The parts of the core a patch wrote. Drift THERE is the patch's defect (its text or wiring does
  // not fit the paper around it), so it goes back to the fixer, never to a transcription round —
  // which would edit the user's version to suit the repair.
  const parts = repairedNodes(patches);
  const patchedNodes = parts;
  const isPatchPart = (id: string): boolean => parts.has(id);
  const split = splitCorollaries(patches);
  /** A drift that only asks for a sampling setting of a split corollary (no other correction named). */
  const splitSetting = (n: V15Review["nodes"][number]): boolean =>
    split.has(n.id) && !!n.fix?.setting && !n.fix.add_depends_on?.length && !n.fix.remove_depends_on?.length && !n.fix.wire_into?.length && !n.fix.unwire_from?.length && !n.fix.extend_to && !n.fix.new_assumption;
  // Drift is a mistake in copying the PAPER, fixed in the user's version. A defect a patch
  // introduced is graded as that patch's `error` (the referee brief says so), never as drift.
  const hasPatches = !!patches && (patches.patches.length > 0 || patches.unfixable.length > 0);
  return {
    patchedNodes,
    isPatchPart,
    // A wrong setting is a defect of the transcription's sampling model, whoever wrote the node's text
    // — but a corollary a repair split off is no result of the paper: it lives in its parent's setting,
    // which the transcription cannot list it under, so a setting asked for it alone is no drift at all.
    paperDrift: (n) => n.faithfulness === "drift" && !splitSetting(n) && (!isPatchPart(n.id) || resultWiringOnly(n.fix, results) || !!n.fix?.setting),
    patchDrift: review.nodes.filter((n) => n.faithfulness === "drift" && isPatchPart(n.id) && !resultWiringOnly(n.fix, results) && !n.fix?.setting),
    // A confirming pass that disputes the fixer's key results sends the patch file back, like an
    // error: descoping a headline result is not a repair.
    keyObjection:
      hasPatches && review.patch_review && !review.patch_review.key_results_ok
        ? review.patch_review.detail.trim() || "the referee rejected the key-result list without giving a reason"
        : null,
    // A repair is CONFIRMED only by a grade the referee would stake: `unclear` on a repaired node is
    // no confirmation (for the paper's own nodes it never
    // blocks — there the claim is the paper's, here it is ours).
    unconfirmed: review.nodes.filter((n) => n.correctness === "unclear" && isPatchPart(n.id)),
    // Nothing the referee could not check passes (user decision 2026-09-22): an `unclear` step of
    // the paper's own goes to the fixer, who writes that proof out in full — or, finding it false,
    // repairs it — and a fresh pass checks it.
    unchecked: review.nodes.filter((n) => n.correctness === "unclear" && !isPatchPart(n.id)),
    refuted: review.nodes.filter((n) => n.correctness === "error" && !n.follows_repair_of?.length),
    unresolvable: review.nodes.filter((n) => n.ambiguity === "unresolvable"),
    unclearNotes: review.nodes.filter((n) => isPatchPart(n.id) && (n.correctness === "ok" || n.correctness === "bookkeeping") && n.explanation_clarity?.grade === "unclear"),
    consequences: review.nodes.filter((n) => n.correctness === "error" && !!n.follows_repair_of?.length),
    // Only on a result whose statement a patch rewrote: a statement the paper prints is never restructured.
    splitRemarks: review.nodes.filter((n) => !!n.split?.why?.trim() && confirmedGrade(n) && results.has(n.id) && !!patches?.patches.some((p) => p.node === n.id && p.corrected_statement !== null)),
  };
}

/** The referee's wiring fix of a repaired node, said in the terms of the fixer's reply: on a result, a
 * hypothesis goes in `adds` / `drops`, a result is cited or no longer relied on; on an assumption or a
 * definition, the corrected text itself carries the change. */
function wiringFix(node: string, fix: V15NodeVerdict["fix"], core: Core): string {
  const results = new Set(core.statements.map((s) => s.id));
  const onResult = results.has(node);
  const add = fix?.add_depends_on ?? [];
  const remove = fix?.remove_depends_on ?? [];
  const out: string[] = [];
  if (onResult) {
    const addH = add.filter((d) => !results.has(d));
    const addR = add.filter((d) => results.has(d));
    if (addH.length) out.push(`the corrected result also uses ${addH.join(", ")}: list them in \`adds\``);
    if (addR.length) out.push(`it also uses the result(s) ${addR.join(", ")}: cite them in the corrected text`);
    if (remove.length) out.push(`it no longer uses ${remove.join(", ")}: list them in \`drops\``);
  } else {
    if (add.length) out.push(`the statements using it also depend on ${add.join(", ")}`);
    if (remove.length) out.push(`they do not depend on ${remove.join(", ")}`);
    if (fix?.wire_into?.length) out.push(`${fix.wire_into.join(", ")} also use it`);
    if (fix?.unwire_from?.length) out.push(`${fix.unwire_from.join(", ")} do not use it`);
  }
  if (fix?.new_assumption) out.push(`it relies on the premise the paper prints from "${fix.new_assumption.from}" to "${fix.new_assumption.to}": state it in the corrected text`);
  if (fix?.extend_to) out.push(`its text runs on to "${fix.extend_to}"`);
  return out.length ? ` The referee's fix: ${out.join("; ")}.` : "";
}

/** What the fixer must answer, from the routing. */
function objectionsOf(r: Routing, core: Core): Objection[] {
  return [
    ...r.refuted.map((n) => ({
      id: n.id,
      axis: r.isPatchPart(n.id) ? "patch rejected" : "correctness",
      detail: n.weakens_contribution && r.isPatchPart(n.id) ? weakeningDetail(n.detail) : n.detail,
      witness: n.witness,
      ...(n.minimality && r.isPatchPart(n.id) ? { minimality: true } : {}),
      ...(n.weakens_contribution && r.isPatchPart(n.id) ? { weakens_contribution: true } : {}),
    })),
    ...r.patchDrift.map((n) => ({
      id: n.id,
      axis: "patch rejected",
      detail: `the repaired text does not fit the paper around it: ${n.detail}${wiringFix(n.id, n.fix, core)}`,
      witness: null,
    })),
    ...r.unconfirmed.map((n) => ({
      id: n.id,
      axis: "patch rejected",
      detail: `not confirmed — the referee could not reproduce it: ${n.detail}`,
      witness: null,
    })),
    ...r.unchecked.map((n) => ({
      id: n.id,
      axis: "clarify",
      detail: `the referee could not reproduce this proof: ${n.detail}`,
      witness: null,
    })),
    ...r.consequences.map((n) => ({
      id: n.id,
      axis: "consequence",
      detail: `this result uses ${n.follows_repair_of!.join(", ")}, whose statement a repair changed, and no longer follows: ${n.detail} ${FIXER_INSTRUCTIONS.consequence}`,
      witness: n.witness,
    })),
    ...r.unclearNotes.map((n) => ({
      id: n.id,
      axis: "note",
      detail: `the repair is confirmed, but its note for the paper's author is unclear: ${n.explanation_clarity!.reason.trim()} ${FIXER_INSTRUCTIONS.noteRewrite}`,
      witness: null,
      note: true,
    })),
  ];
}

/**
 * The substantive-failure record: what the report carries when the loop ends with errors left
 * (drift at the revise cap, or the orchestrator accepted an error-round cap). Rejected repairs: the
 * repaired node an objection names. A minimality objection rejects nothing: that repair is correct.
 */
async function recordFailure(
  args: VerifyStageArgs,
  r: Routing,
  review: V15Review,
  index: CoreIndex,
  patches: PatchFile | null,
  objections: Objection[],
  patchRounds: number,
): Promise<VerifyStageResult> {
  const rejected = new Set<string>();
  for (const o of objections) {
    if (o.axis !== "patch rejected" || o.minimality) continue;
    if (r.patchedNodes.has(o.id)) rejected.add(o.id);
  }
  if (patches) await recordPatches(args, patches, (node) => !rejected.has(node));
  // An error on a corollary a repair split off rejects that repair (above): no claim of the paper's.
  const split = splitCorollaries(patches);
  // A witness against the repair TRIED for a statement the paper leaves undetermined is no witness
  // against the printed statement: the result stays undetermined, with the attempt and its witness.
  const ledger = args.state.verify!.paper_errors ?? {};
  const triedOnOpen = r.refuted.filter((n) => !split.has(n.id) && r.patchedNodes.has(n.id) && ledger[n.id]?.undetermined === true && !isWithdrawn(ledger[n.id]));
  for (const node of triedOnOpen) record(args.state, node.id, "unresolved", `${TRIED_REPAIR_REFUTED}: ${node.detail}`, node.witness, { undetermined: true });
  const paperRefuted = r.refuted.filter((n) => !split.has(n.id) && !triedOnOpen.includes(n));
  for (const node of paperRefuted) record(args.state, node.id, "refuted", node.detail, node.witness);
  if (r.keyObjection) record(args.state, "run", "unresolved", `the key results of the patch file are disputed: ${r.keyObjection}`, null);
  for (const node of r.unresolvable) {
    record(args.state, node.id, "unresolved", `ambiguous — the paper does not determine the reading and the choice matters: ${node.detail}`, null, { undetermined: true });
  }
  // Pinned readings are suggestions to the authors whether or not the paper passed; on FAIL
  // the core is not edited, so the report gets them as notes.
  for (const node of review.nodes) {
    if (node.ambiguity === "pinned" && node.reading) {
      record(args.state, node.id, "note", `pinned reading: ${node.reading.reading} (${node.reading.evidence})`, null);
    }
  }
  // A grading that paused for a repair and never resumed left the results above it unreviewed.
  for (const id of review.paused?.ungraded ?? []) {
    record(args.state, id, "unresolved", `not reviewed: the V1.5 grading paused at level ${review.paused!.level} for a repair and the loop ended before it resumed`, null);
  }
  for (const node of r.consequences) {
    record(args.state, node.id, "unresolved", `does not follow the repair of ${node.follows_repair_of!.join(", ")} after ${patchRounds} patch round(s): ${node.detail}`, null);
  }
  // A proof still not checkable after the patch rounds is not verified — reported as such, never
  // as wrong.
  for (const node of r.unchecked) {
    record(args.state, node.id, "unresolved", `could not be verified after ${patchRounds} patch round(s): ${node.detail}`, null);
  }
  return {
    status: "failed",
    message:
      `FAIL: ${paperRefuted.length} refuted result(s)` +
      (paperRefuted.length > 0 ? ` — ${paperRefuted.map((n) => `${n.id} (${locatorText(index.locators.get(n.id))})`).join(", ")}` : "") +
      (triedOnOpen.length > 0 ? `; ${triedOnOpen.length} refuted repair(s) of a statement the paper leaves undetermined — ${triedOnOpen.map((n) => n.id).join(", ")}` : "") +
      (r.unconfirmed.length > 0 ? `; ${r.unconfirmed.length} repair(s) the referee could not confirm — ${r.unconfirmed.map((n) => n.id).join(", ")}` : "") +
      (r.unchecked.length > 0 ? `; ${r.unchecked.length} proof(s) that could not be verified — ${r.unchecked.map((n) => n.id).join(", ")}` : "") +
      (r.unresolvable.length > 0 ? `; ${r.unresolvable.length} unresolvably ambiguous — ${r.unresolvable.map((n) => n.id).join(", ")}` : "") +
      "; no Lean work was attempted.",
  };
}

/**
 * What accepting a refinement cap would lose (empty: nothing): an error the ledger holds with no entry in
 * the patch file (a suggestion the stopped round withdrew), and a repair the owner accepted that is
 * back to a suggestion only. A clarification's entry (an overruled F-stage clarify) needs none. Checked
 * before `--accept-cap` changes anything (`pipeline.ts`), so a refusal leaves the run as it halted. Pure.
 */
export function acceptCapLosses(transcribed: Core, patches: PatchFile | null, ledger: PaperErrors | undefined): string[] {
  const errors = Object.fromEntries(Object.entries(ledger ?? {}).filter(([, e]) => (e as { kind?: string }).kind !== "clarification"));
  const file = patches ?? { key_results: [], key_contribution: "", patches: [], unfixable: [] };
  return [
    ...validatePatchFile(transcribed, file, openErrorIds(errors as PaperErrors)),
    ...Object.entries(errors)
      .filter(([id, e]) => (e as { owner_decision?: string }).owner_decision === "accepted" && !file.patches.some((p) => p.node === id) && file.unfixable.some((u) => u.node === id))
      .map(([id]) => `the owner accepted the weakened repair of "${id}", but ${VERIFY_FILES.patches} holds it as a suggestion only.`),
  ];
}

/**
 * `--resume --accept-cap` on a run halted at a V1.5 cap: the patch loop ends here, read from the
 * review, the core and the patch file that pass left. At the REFINEMENT cap every repair is correct
 * — only minimality or a note's clarity is disputed — so the patched core is ACCEPTED (`completed`:
 * hashed, cursor `V1.5`, F1 next, so Lean certifies the confirmed repair), each patch recorded as a
 * confirmed repair. At the ERROR cap the errors left are the paper's,
 * recorded as a substantive failure (`failed`: V6 reports).
 */
export const acceptV1_5AtCap: VerifyStage = async (args) => {
  const { runDir, state } = args;
  const verify = state.verify!;
  const review = await readPriorReview(path.join(runDir, VERIFY_FILES.v15Review));
  if (!review) throw new Error(`--accept-cap: ${VERIFY_FILES.v15Review} is missing or unreadable — the halting V1.5 pass left no review.`);
  const corePath = path.join(runDir, VERIFY_FILES.coreJson);
  const core = parseTypedCore(await readFile(corePath, "utf8"), `verify core ${corePath}`);
  const patches = await readPatchFile(runDir);
  const hasPatches = !!patches && (patches.patches.length > 0 || patches.unfixable.length > 0);
  // (a review a halted pass left on file holds its verdicts as graded: moved here, as a pass moves them)
  const r = routeReview({ ...review, nodes: errorsOnHosts(review.nodes, inlineLeaves(core)) }, hasPatches ? patches : null, resultIds(core));
  // The loop ends here: a grading paused for a repair does not resume.
  delete verify.level_pause;
  if (verify.cap_reached?.counter === "refinement_rounds") {
    // The acceptance a clean pass gives: the core with the referee's additions, hashed for F1;
    // every patch recorded as a confirmed repair, pins and cited sources as notes.
    const envsPath = path.join(runDir, VERIFY_FILES.envsJson);
    const envs = existsSync(envsPath) ? (JSON.parse(await readFile(envsPath, "utf8")) as EnvsJson) : null;
    const { sources } = await resolveCitedSources({ runDir, core, envs, fetchBytes: args.deps.fetchBytes });
    const accepted = await acceptCore(args, await readTranscribedCore(runDir), corePath, review, hasPatches ? patches : null, sources);
    if (accepted.status !== "completed") return accepted;
    return {
      status: "completed",
      message:
        `refinement cap accepted: every repair is correct — ${accepted.message}`,
    };
  }
  return recordFailure(args, r, review, indexCore(core), hasPatches ? patches : null, onSplitParent(objectionsOf(r, core), patches), verify.patch_rounds ?? 0);
};

/** The symbols whose verdict reads a repair that is demoted to a suggestion (`demoted`, among the
 * statements `corrected`): a user of the symbol whose correction changed a sentence naming it, or a
 * result its reading on file names. Their confirmation is withdrawn. Pure. */
export function symbolsReadingDemoted(core: Core, demoted: ReadonlySet<string>, corrected: ReadonlyMap<string, { printed: string; text: string }>, verdicts: readonly V15SymbolVerdict[]): string[] {
  const gone = (u: string): boolean => demoted.has(u) && corrected.has(u);
  const readingOf = new Map(verdicts.map((v) => [v.name, v.reading] as const));
  return core.symbols
    .filter((x) => symbolUsers(core, x.name).some((u) => gone(u) && correctionTouchesSymbol(x.name, corrected.get(u)!)) || [...resultsNamedBy(readingOf.get(x.name) ?? null, core.statements)].some(gone))
    .map((x) => x.name);
}

/**
 * The statements the symbol referee reads in corrected form (C5), by node: the corrected statement of
 * each PATCH on file, with its printed text. A suggested repair awaiting the owner (`unfixable`) is no
 * patch, so a symbol read from its statement is graded against the printed text (`READING_BASIS_RULE`).
 * Pure.
 */
export function correctedStatements(
  transcribed: { statements: ReadonlyArray<{ id: string; statement: string }> },
  patches: { patches?: ReadonlyArray<{ node: string; corrected_statement?: string | null; readings?: readonly string[] | null }> } | null | undefined,
): Map<string, { printed: string; text: string }> {
  return new Map(
    (patches?.patches ?? []).flatMap((x) => {
      const printed = transcribed.statements.find((st) => st.id === x.node)?.statement;
      const readings = (x.readings ?? []).filter((r) => r.trim());
      if (!printed || (!x.corrected_statement?.trim() && readings.length === 0)) return [];
      // The readings a repair states beside the statement say what its symbols mean as much as its
      // text does: a symbol is read from both, so a sentence moved from one to the other moves nothing.
      const text = `${x.corrected_statement?.trim() ? x.corrected_statement : printed}${readings.length > 0 ? `\n\n${REPAIR_READINGS_HEAD}\n${readings.map((r) => `- ${r}`).join("\n")}` : ""}`;
      return [[x.node, { printed, text }] as const];
    }),
  );
}

/** How the readings of a repair open under its corrected statement, where a symbol is read from it. */
export const REPAIR_READINGS_HEAD = "Readings of this statement, stated by its repair (binding):";
