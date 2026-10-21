/**
 * V6 annotated paper — `runs/<slug>/annotated/`.
 *
 * A copy of the paper's source tree in which every problem the run found is marked where the paper
 * states it: the wrong or ambiguous sentence in red (`\vsOriginal`, "Original:"), the
 * corrected text in blue (`\vsCorrected` / `\vsClarified`: "Corrected:", "Clarified
 * statement:"), and a note in a third colour (`\vsNote`,
 * "PaperFormalizer: …") saying what is wrong, the proposed fix, and — only when the run records it —
 * what the fix gives up. Each part is its own paragraph (the macros break the line). The paper reads
 * as one document (user rules 2026-09-25): only the sentences or list items a corrected statement
 * changes are marked (a repair is replacements of the paper's units, user decision 2026-09-26; a
 * hypothesis is added by restating, and the note says which); a change identical to the printed text
 * as printed is not marked; each result gets one note, after the statement.
 * A corrected proof step's details (`\vsDetail`, the fixer's: what the referee and the Lean proof need
 * beyond the paper's level of detail) are side notes beside the step; a step whose words stand as printed
 * is not marked, its details set after it.
 * Pinned readings still standing as assumptions get a note after their statement (`\vsReading`,
 * "Clarification:"; the owner's `\vsReadingOwner`, "Clarification (author):"; a symbol's
 * `\vsReadingSymbol`, "Clarification (symbol …):").
 * A condition the verified statement carries beyond the printed text (the referee's bookkeeping
 * condition, the owner's side condition) gets a note at the end of every result carrying it
 * (`\vsCondition`, "Bookkeeping condition:"; the owner's `\vsConditionOwner`, "Bookkeeping condition:");
 * nothing printed is marked for it.
 * An assumption or definition no result uses after the repairs (each result that used it was repaired
 * away from it) is crossed out where the paper prints it (`\vsStruck`), with a note naming the results.
 * A repair that splits a result (`patches.ts` `corollaries`) is shown block by block: the printed
 * statement whole in red, the corrected statement whole in blue, then each corollary as a blue block of
 * its own right after the result's environment (`\vsCorollary`, "Corollary of Theorem N:"; pending with
 * the owner, `\vsProposedCorollary`): its statement and its proof. A block whose proof does not cite the
 * result (`core_graph.ts` `splitKind`) is no corollary of it but a proposition the printed statement
 * bundled in: the same block under `\vsSplitProposition` / `\vsProposedSplitProposition`
 * ("Proposition stated in Theorem N:"). In the corrected view a block of a result the
 * paper proves elsewhere is written in two places: its statement after the result, its proof
 * (`\vsCorollaryProof`, `\vsSplitPropositionProof`) after the result's proof.
 * At a halt for the owner (`annotate_run.ts`) the pending decisions are rendered too, under
 * "… (awaiting your decision)" labels (`\vsProposed`, `\vsRewind`, `\vsCap`); V6 has none.
 *
 * Deterministic and model-free: `planAnnotations` is a pure function of the run's records (envs,
 * flat text + line map, reference core, transcribed and accepted core, patches, paper errors,
 * findings, review) and the source files; `writeAnnotatedPaper` copies the tree, applies the plan,
 * injects the colour macros, writes `ANNOTATIONS.md` and, when a TeX compiler is on PATH, compiles.
 * Locators, in order: the reference core (env + sentences / anchor slice / prose slice) aligned
 * onto the original bytes → the whole environment body → a note at the environment's end. Nothing
 * is skipped silently: an unlocated finding is placed at its environment's end, or listed in
 * `ANNOTATIONS.md` when no environment is known, and counted in the log.
 */
import { existsSync } from "node:fs";
import { cp, mkdir, readFile, rm, writeFile } from "node:fs/promises";
import path from "node:path";
import { applyEditsKeepingNotes, unwrapSource } from "./note_macros.js";
import { ANNOTATED_COMPILE_RECORD, compileGuarded, compileTex, sourceFailureNote, type CompileResult, type CompileTex } from "./annotated_compile.js";
import type { Core, CoreStatement } from "../core/schema.js";
import {
  alignToOriginal,
  blueTex,
  type BlueMacro,
  type NoteMacro,
  documentClassOf,
  extendToRegions,
  firstSentences,
  injectPreamble,
  lineStarts,
  loadsXcolor,
  preambleOf,
  braceProblem,
  nonAsciiProblem,
  safeInsertionPoint,
  safeSpan,
  struckMacro,
  MATH_ENV,
  summarizeWitness,
  texRegions,
  trimSpan,
  unsafeRegions,
  type UnsafeRegion,
  verbatimLike, fitDisplays, printedFragment, DISPLAY_TOO_WIDE, COROLLARY_PROOF, SPLIT_MACROS, conditionParagraph, envCuts } from "./annotate_tex.js";
import { envImbalance } from "./tex_balance.js";
import { balancedLikeUnit, bodyDefinitionList, readPaperText, texVerdictKey, texVerdicts, withLocalBodyDefinitions, type TexFragmentKind } from "./tex_fragment_check.js";
import { SYMBOL_PIN_OF, conditionsOn, fullReadingText, pinsOn, splitCorollaryId, splitKind } from "./core_graph.js";
import { PROOF_UNCHANGED, isProofOp, isStatementOp, splitDetails, materializeRepair, nodePassage as unitPassage, resolveOps, sliceOffsets, statementSpan, type PassageSources, type PatchOp } from "./ops.js";
import { PaperUnits, flatLineStart, isControlLine, type Unit } from "./units.js";
import { BUILTIN_ENVS, FURTHER_PROOF_SEPARATOR, parseTheoremCounters } from "./tex_envs.js";
import { blankTexComments } from "../shared/tex_text.js";
import { explanationParts, hasExplanation, isOwnerFacing, isStructuredExplanation, ownerExplanation, ownerFacing, paperLabels, resultWord, sentences, withoutFixerInstructions, type OwnerExplanationField } from "./owner_text.js";
import type { RefCore, SourceRef } from "./ref_core.js";
import type { FragmentProducer, RenderDefect } from "./render_check.js";
import { locatorKey, sentenceSpans } from "./transcription_lint.js";
import type { EnvsJson, TexEnv, V15Review, VerifyFinding } from "./types.js";

export const ANNOTATED_DIR = "annotated";
export const ANNOTATIONS_MD = "ANNOTATIONS.md";

/** `not determined`: a statement the paper leaves undetermined, with no adopted reading or repair
 * (`PaperError.undetermined`) — placed as an unrepaired error is, never named one. */
export type AnnotationKind = "error (repaired)" | "error (not repaired)" | "not determined" | "clarification" | "clarification (reading)" | "condition added" | "corrected proof" | "awaiting decision" | "no longer used";

/**
 * What the run is halted on for the paper's owner, rendered at the passage so the owner decides from
 * the paper (`annotate_run.ts` reads it from `state.verify`). Absent at V6: nothing is pending there.
 */
export interface PendingDecisions {
  /** Suggested repairs that weaken the contribution (`state.verify.weakening_repair`, pending). */
  weakening: Array<{
    node: string;
    corrected_statement: string | null;
    given_up: string;
    /** `referee` when `given_up` is the referee's text; absent: the fixer's. */
    given_up_by?: "referee";
    detail: string;
    witness: string | null;
    /** The error for the paper's author (the fixer's, else the referee's), when one was written. */
    owner_explanation?: OwnerExplanationField | null;
    /** The suggestion's operations on the paper's units (`ops.ts`), when the patch file holds them. */
    ops?: PatchOp[];
    /** The owner's guidance of an earlier `--redo-repair` that again ended in this suggestion. */
    guidance?: string;
    /** The corollaries the suggestion splits off the result. */
    corollaries?: LooseCorollary[];
  }>;
  /** The `weakening` items are not presented yet (the receipt is `unconfirmed`): a V1.5 pass grades
   *  the suggestions first, and until it settles the runner refuses every ruling on them. */
  confirming?: true;
  /** A proposed F-stage rewind (`state.verify.cross_stage_rewind`, pending): its routed findings. */
  rewind: { stage: string; targets: Array<{ node: string; axis: string; kind?: string; reason: string }> } | null;
  /** A patch cap (`state.verify.cap_reached`): the counter and the round it stopped. */
  cap: {
    counter: string;
    rounds: number;
    cap: number;
    origin: string;
    findings: Array<{ id: string; axis: string; detail: string; witness: string | null }>;
    summary: string;
  } | null;
}

export interface AnnotationRecord {
  node: string;
  file: string;
  line: number;
  kind: AnnotationKind;
  /** `sentences` / `slice` / `env` (reference core), `text` (searched), `env-span`, `env-end`, `after-env`. */
  located_by: string;
  summary: string;
  /** Why a span was widened (display math, an environment, a brace group) or merged. */
  extended: string[];
}

export interface UnlocatedRecord {
  node: string;
  kind: AnnotationKind;
  reason: string;
  /** `file:line` of the environment-end note it was written as, or null (listed only). */
  placed: string | null;
}

/** Loose views of the records (optional fields of later schemas read when present). */
interface LooseCorollary { title?: string; statement: string; follows: string }
interface LoosePatch {
  node: string;
  corrected_statement: string | null;
  proof_note?: string;
  accepted_weakening?: boolean;
  given_up?: string;
  given_up_by?: "referee";
  narrowed_by?: "owner" | "runner";
  /** The repair as operations on the paper's units (`ops.ts`): what the paper shows. */
  ops?: PatchOp[];
  /** The node's hypotheses the repair rewrites (`supersedes`) or no longer uses (`drops`). */
  supersedes?: string[];
  drops?: string[];
  owner_explanation?: OwnerExplanationField;
  /** A consequential patch (`consequential.ts`): the repairs its proof follows, and what the step now uses. */
  consequence_of?: string[];
  reason?: string | null;
  /** The corollaries the repair splits off the result (`core_graph.ts` `SplitCorollary`). */
  corollaries?: LooseCorollary[];
  /** The result is an umbrella over those blocks (`patches.ts` `umbrella`): all propositions. */
  umbrella?: boolean;
}
interface LooseSuggestion { corrected_statement: string | null; given_up?: string; given_up_by?: "referee"; proof_note?: string; ops?: PatchOp[]; corollaries?: LooseCorollary[]; umbrella?: boolean }
interface LooseUnfixable { node: string; reason: string; suggested_repair?: LooseSuggestion | null; declined?: string; owner_explanation?: OwnerExplanationField }
export interface LoosePatchFile { patches?: LoosePatch[]; unfixable?: LooseUnfixable[] }
type LooseFinding = VerifyFinding & { suggested_repair?: string; suggestion_declined?: string; patch?: (VerifyFinding["patch"] & { narrowed?: string }) | null };
type PaperErrors = Record<string, { detail: string; witness: string | null; kind?: "error" | "clarification"; undetermined?: boolean; owner_decision?: string }>;

export interface AnnotationInput {
  /** Source files by path relative to `source/` (every `.tex` of `envs.files`). */
  files: Record<string, string>;
  envs: EnvsJson;
  flatText: string;
  lineMap: Array<{ file: string; line: number }>;
  refs: RefCore | null;
  transcribed: Core;
  core: Core;
  patches: LoosePatchFile | null;
  paperErrors: PaperErrors;
  /** Nodes whose suggested weakening the referee rejected: their review verdict may be about the
   * suggestion, not the paper. */
  suggestionRejected?: ReadonlySet<string>;
  findings: VerifyFinding[];
  review: V15Review | null;
  /** Decisions pending with the owner (a halt); null / absent at V6. */
  pending?: PendingDecisions | null;
  /** The fragments that failed the compile check (`tex_fragment_check.ts` `texVerdicts`, by
   * `texVerdictKey`): printed verbatim and reported. Absent: only the ASCII detector runs. */
  texVerdicts?: ReadonlyMap<string, string> | null;
  /** The corrected-only view (`corrected_tex.ts` reads it; never compiled as it is): each blue part,
   * note and proof block is preceded by `\vsAt{node}{kind}` (`; overlapped`: placed after another
   * node's span; `; unlocated`: its printed passage was not found), and a proof block or a reading
   * carries no words about the review; a corollary block is `{node id}{its title, or nothing}{content}`,
   * tagged with the corollary's own id. */
  correctedView?: boolean;
}

/** An insertion of `text` at `at` (`del`: the characters from `at` it replaces). */
interface Edit { at: number; rank: 0 | 1 | 2; text: string; seq: number; del?: number }

export interface AnnotationPlan {
  edits: Record<string, Edit[]>;
  records: AnnotationRecord[];
  unlocated: UnlocatedRecord[];
  log: string[];
  /** Blocks that could not be set as TeX (a model-written fragment with a non-ASCII character or
   * failing the compile check, printed verbatim; a proof-step fragment escaped): defects, which block
   * the run (`render_check.ts`). Nothing is repaired. */
  defects: RenderDefect[];
  /** Every model-written fragment the plan sets, with how it is set: the input of the compile check
   * (`writeAnnotatedPaper` checks them and plans again with `texVerdicts`). */
  fragments: Array<{ kind: TexFragmentKind; text: string }>;
}

/** A span to mark inside one text (an env body / proof, or the flat text): red on `[start, end)`
 * (none when start === end), then the blue text (under `macro`, default `\vsCorrected`) and the note. */
interface Op { start: number; end: number; blue: string | null; macro?: BlueMacro; note: string; noteMacro?: NoteMacro; how: string; redMacro?: "vsOriginal" | "vsStep" | "vsStruck" | "vsStruckRed"; /** The blue text is already set (`renderStepTex`): written as it is. */ blueFinal?: boolean }

type Region = "body" | "proof";

function lineOf(text: string, at: number): number {
  const ls = lineStarts(text);
  let lo = 0;
  let hi = ls.length - 1;
  while (lo < hi) {
    const mid = (lo + hi + 1) >> 1;
    if (ls[mid]! <= at) lo = mid;
    else hi = mid - 1;
  }
  return lo + 1;
}

/** Pipeline words in an explanation, as the author says them: a "confirmed patch" is the repair (the
 * renderer's backstop; the stored text is the fixer's). */
export const authorWords = (t: string): string =>
  t.replace(/\b([Tt])he confirmed patch\b/gu, (_m, T: string) => `${T}he repair`).replace(/\bconfirmed patch\b/gu, "repair");

/** A suggestion stored as one line (`suggestionText`: its parts joined by " · ") as TeX the author reads:
 * the parts joined by "; " (the TeX is plain ASCII) — only before a part's own label, so a "·" in the
 * model's text is left for the render check to refuse. Pure. */
export function suggestionSummaryTex(line: string): string {
  return line.replace(/ \u00b7 (?=corollary \d|gives up: |the statement becomes an umbrella)/gu, "; ");
}

function cleanDetail(d: string): string {
  // (the runner's instructions to the fixer are not the author's to read)
  return withoutFixerInstructions(d).split(/\n\s*Reading\(s\) the referee pinned/u)[0]!.replace(/^(?:\s*\[[^\]]*\]\s*)+/u, "").replace(/\s+/g, " ").trim();
}

const plainLine = (s: string, n = 160): string => {
  const t = s.replace(/\s+/g, " ").replace(/\|/g, "\\|").trim();
  return t.length > n ? `${t.slice(0, n - 1)}…` : t;
};

/** The mandatory arguments of the macro `name` (`\\costSub`) as the paper defines it
 * (`\\newcommand{\\costSub}[2]{…}`; an optional first argument does not count); 0 when the name is not a lone
 * control sequence or the paper does not define it so. A symbol named by such a macro is printed with a
 * placeholder for each: alone, it would take the note's own text as its arguments. Pure. */
export function macroArity(flat: string, name: string): number {
  if (!/^\\[A-Za-z]+$/u.test(name)) return 0;
  const esc = name.replace(/\\/gu, "\\\\");
  const m = new RegExp(String.raw`\\(?:re)?newcommand\*?\s*\{?\s*${esc}\s*\}?\s*\[(\d)\](\[)?`, "u").exec(flat);
  return m ? Number(m[1]) - (m[2] ? 1 : 0) : 0;
}

export function planAnnotations(input: AnnotationInput): AnnotationPlan {
  const { envs, refs, transcribed, core } = input;
  // The paper's own labels are no node-id mention for the owner-facing filter (`nodeIdMentions`).
  const paperLabelSet = paperLabels(input.flatText);
  const bodyDefs = bodyDefinitionList(input.flatText);
  const edits: Record<string, Edit[]> = {};
  const wraps: Record<string, Array<{ start: number; end: number; node: string }>> = {};
  const records: AnnotationRecord[] = [];
  const unlocated: UnlocatedRecord[] = [];
  const log: string[] = [];
  const defects: RenderDefect[] = [];
  let seq = 0;
  const fragments = new Map<string, { kind: TexFragmentKind; text: string }>();
  /**
   * A model-written TeX fragment, set as written (design 2026-09-25: compiled at its source, never
   * repaired here). One with a non-ASCII character (`nonAsciiProblem`), unbalanced braces
   * (`braceProblem`), or that failed the compile
   * check (`input.texVerdicts`) is printed verbatim and reported as a MODEL-TEXT defect naming it and
   * its producer (`render_check.ts`: the runner routes it back to that producer); `block` names the
   * block, `kind` how the fragment is set (the compile check's wrapping), `by` who wrote it (null: not
   * a model's text — the paper's own, whose failure is the renderer's); `ref` what the producer keys
   * it by (a symbol's name, a note's clarity key); `printed` the paper's text a replacement takes the place
   * of, which it is checked balanced like (`balancedLikeUnit`: a unit the paper cuts across an
   * environment), as the fixer's patch check does — the text printed is the fragment as written.
   */
  const fragment = (node: string, block: string, text: string, kind: TexFragmentKind, by: FragmentProducer | null, ref?: string, printed?: string): string => {
    const checked = balancedLikeUnit(text, printed);
    fragments.set(texVerdictKey(kind, checked), { kind, text: checked });
    const bad = nonAsciiProblem(text) ?? braceProblem(text) ?? input.texVerdicts?.get(texVerdictKey(kind, checked)) ?? null;
    // a note may stand before the paper defines a body macro it uses
    if (bad === null) return kind === "note" ? withLocalBodyDefinitions(text, bodyDefs) : text;
    const shown = text.replace(/\s+/g, " ").trim();
    const tooWide = bad.startsWith(DISPLAY_TOO_WIDE);
    defects.push({
      node,
      block,
      reason: `${bad}; ${tooWide ? "printed shrunk" : "printed verbatim"} — the fragment: ${shown.length > 160 ? `${shown.slice(0, 159)}…` : shown}`,
      ...(by ? { fragment: { kind, text, producer: by, error: bad, ...(ref ? { ref } : {}) } } : {}),
    });
    if (tooWide) return text;
    log.push(`annotation ${node}: ${block} printed verbatim (${bad})`);
    return verbatimLike(text);
  };
  /** A symbol's name as the label of its reading: the paper's own notation, set as math when it
   * compiles alone, else printed verbatim (a macro taking arguments, `\expe{…}`) — nobody's defect. */
  const label = (node: string, name: string): string => asWritten(node, "symbol name", `$${name}${"{\\cdot}".repeat(macroArity(input.flatText, name))}$`);
  /** A text no model of the run writes again and the paper does not keep (a symbol's name; an F-stage
   * reviewer's finding awaiting the owner's decision — once decided, the fixer's note or the owner's
   * reason replaces it): set as written when it compiles, else printed verbatim — nobody's defect. */
  function asWritten(node: string, block: string, raw: string): string {
    const text = raw.replace(/\s+/g, " ").trim();
    fragments.set(texVerdictKey("note", text), { kind: "note", text });
    const bad = nonAsciiProblem(text) ?? braceProblem(text) ?? input.texVerdicts?.get(texVerdictKey("note", text)) ?? null;
    if (bad === null) return withLocalBodyDefinitions(text, bodyDefs);
    log.push(`annotation ${node}: ${block} printed verbatim (${bad})`);
    return verbatimLike(text);
  }
  /** A note's text (its whitespace collapsed), written by `by`. */
  const safe = (node: string, block: string, text: string, by: FragmentProducer | null, ref?: string): string => fragment(node, block, text.replace(/\s+/g, " ").trim(), "note", by, ref);
  /** A LaTeX fragment set as written (a statement or hypothesis unless `kind` says otherwise), written by
   * `by`; `printed`: the paper's text it replaces (`fragment`). */
  const latex = (node: string, block: string, text: string, by: FragmentProducer, kind: TexFragmentKind = "statement", printed?: string): string => fragment(node, block, text, kind, by, undefined, printed);
  const envById = new Map(envs.envs.map((e) => [e.id, e] as const));
  // The paper's units (`units.ts`): every statement and proof mark addresses them.
  const units = PaperUnits.parse(input.flatText, envs, flatLineStart(input.flatText, input.lineMap));
  const passageSrc: PassageSources = { units, refs, statements: transcribed.statements, envs };
  const patches = input.patches?.patches ?? [];
  const unfixable = input.patches?.unfixable ?? [];
  const patchOf = new Map(patches.map((p) => [p.node, p] as const));
  const reviewOf = new Map((input.review?.nodes ?? []).map((n) => [n.id, n] as const));

  // --- alignment of an env region onto its original file (cached).
  const alignCache = new Map<string, { file: string; orig: string; map: number[] | null } | null>();
  const aligned = (env: TexEnv, region: Region): { file: string; orig: string; map: number[] | null } | null => {
    const key = `${env.id}/${region}`;
    if (alignCache.has(key)) return alignCache.get(key)!;
    const loc = region === "proof" ? env.proofLines : env.lines;
    const text = region === "proof" ? env.proof : env.body;
    let out: { file: string; orig: string; map: number[] | null } | null = null;
    if (loc && text !== null && input.files[loc.file] !== undefined) {
      const orig = input.files[loc.file]!;
      const ls = lineStarts(orig);
      const from = ls[loc.from - 1] ?? 0;
      const to = ls[loc.to] ?? orig.length;
      out = { file: loc.file, orig, map: alignToOriginal(orig, from, to, text) };
    }
    alignCache.set(key, out);
    return out;
  };

  /** `\begin{…}` … `\end{…}` of an env in its original file. */
  const envBounds = (env: TexEnv): { file: string; bodyStart: number; endStart: number; endEnd: number } | null => {
    const orig = input.files[env.lines.file];
    if (orig === undefined) return null;
    const ls = lineStarts(orig);
    const from = ls[env.lines.from - 1] ?? 0;
    const to = ls[env.lines.to] ?? orig.length;
    const window = orig.slice(from, to);
    const name = env.envName.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    const b = new RegExp(`\\\\begin\\s*\\{${name}\\}(?:\\s*\\[[^\\]]*\\])?`).exec(window);
    const ends = [...window.matchAll(new RegExp(`\\\\end\\s*\\{${name}\\}`, "g"))];
    const e = ends[ends.length - 1];
    if (!b || !e) return null;
    return { file: env.lines.file, bodyStart: from + b.index + b[0].length, endStart: from + e.index, endEnd: from + e.index + e[0].length };
  };
  /** `\begin{…}` … `\end{…}` of an env's printed proof in its original file: the environment of
   * `proofLines`, its first `\begin` closed by its last `\end` (comments blanked). Null for a proof read
   * from plain lines (a segment) or printed in several places. */
  const proofTags = (env: TexEnv): { file: string; start: number; end: number } | null => {
    const loc = env.proofLines;
    const orig = loc ? input.files[loc.file] : undefined;
    if (!loc?.env || orig === undefined || env.proof?.includes(FURTHER_PROOF_SEPARATOR)) return null;
    const ls = lineStarts(orig);
    const from = ls[loc.from - 1] ?? 0;
    const window = blankTexComments(orig.slice(from, ls[loc.to] ?? orig.length));
    const tags = [...window.matchAll(new RegExp(`\\\\(begin|end)\\s*\\{${loc.env.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\}`, "g"))];
    let depth = 0;
    for (const [k, m] of tags.entries()) {
      depth += m[1] === "begin" ? 1 : -1;
      if (depth < 0 || (depth === 0 && k < tags.length - 1)) return null;
    }
    const last = tags[tags.length - 1];
    if (!last || depth !== 0) return null;
    return { file: loc.file, start: from + tags[0]!.index, end: from + last.index + last[0].length };
  };

  // --- every insertion point is checked against the ORIGINAL source (math, groups, comments; cached).
  const regionCache = new Map<string, UnsafeRegion[]>();
  const regionsOf = (file: string): UnsafeRegion[] => {
    let r = regionCache.get(file);
    if (!r) regionCache.set(file, (r = unsafeRegions(input.files[file] ?? "")));
    return r;
  };
  /** Queue an edit. An insertion (rank 1) goes to the first safe position at or after `at`
   * (`safeInsertionPoint`: never inside math, a brace group, a comment); a move is logged and returned. */
  const pushEdit = (file: string, at: number, rank: 0 | 1 | 2, text: string): { at: number; moved: string | null } => {
    let pos = at;
    let moved: string | null = null;
    const orig = input.files[file];
    if (rank === 1 && orig !== undefined) {
      const safe = safeInsertionPoint(orig, at, regionsOf(file));
      if (safe.pos !== at) {
        pos = safe.pos;
        moved = `insertion moved out of ${safe.moved.join(", ")} (${file}:${lineOf(orig, at)} → ${file}:${lineOf(orig, pos)})`;
        // only a comment or verbatim region carries an insertion past a paragraph break: say so, the
        // block then stands away from its passage
        log.push(`annotated paper: ${/\n[ \t]*\n/.test(orig.slice(at, pos)) ? "WARNING: " : ""}${moved}`);
      }
    }
    (edits[file] ??= []).push({ at: pos, rank, text, seq: seq++ });
    return { at: pos, moved };
  };
  /** Wrap `[start, end)` of `file` in `\<macro>{…}` and put `tail` after it: the span is widened
   * until the wrap is well formed (`safeSpan`), the tail goes to the first safe position at or after
   * the wrap's end. Returns the span placed and what was widened or moved. */
  const pushWrap = (file: string, start: number, end: number, macro: string, tail: string, node: string): { start: number; end: number; notes: string[] } => {
    const orig = input.files[file]!;
    const w = safeSpan(orig, start, end, regionsOf(file));
    const notes = w.extended.length > 0 ? [`source span widened over ${w.extended.join(", ")}`] : [];
    // a widening that takes in a paragraph break (an unclosed comment or verbatim) marks more than the passage
    if (w.extended.length > 0) log.push(`annotated paper: ${/\n[ \t]*\n/.test(orig.slice(w.start, start) + orig.slice(end, w.end)) ? "WARNING: " : ""}${node} source span widened over ${w.extended.join(", ")} (${file}:${lineOf(orig, start)}-${lineOf(orig, end)} → ${file}:${lineOf(orig, w.start)}-${lineOf(orig, w.end)})`);
    (wraps[file] ??= []).push({ start: w.start, end: w.end, node });
    pushEdit(file, w.start, 2, `${tagOf(node, "printed")}\\${macro}{`);
    if (!tail || safeInsertionPoint(orig, w.end, regionsOf(file)).pos === w.end) pushEdit(file, w.end, 0, `}${tail}`);
    else {
      pushEdit(file, w.end, 0, "}");
      const r = pushEdit(file, w.end, 1, tail);
      if (r.moved) notes.push(r.moved);
    }
    return { start: w.start, end: w.end, notes };
  };
  /** The blocks after a span: the blue part and the note (each model-written part was checked as it
   * was built; the runner's assembly around them is the runner's). */
  const after = (op: Op, at = ""): string =>
    `${op.blue ? ` ${at}\\${op.macro ?? "vsCorrected"}{${op.blueFinal ? op.blue : laidOut(op.blue)}}` : ""}${op.note ? ` ${at}\\${op.noteMacro ?? "vsNote"}{${displayed(op.note)}}` : ""}`;
  /** The corrected view's tag of a block (`AnnotationInput.correctedView`), else nothing. */
  const tagOf = (node: string, kind: string): string => (input.correctedView ? `\\vsAt{${node}}{${kind}}` : "");
  /** A blue part laid out for reading (`layoutBlue`: paragraphs, one numbered clause per line) —
   * unless the check rendered it verbatim. */
  /** A note's displayed formula (`\[…\]`, a quoted display) as `\vsDisplay`: on its own line, so a long
   * one never runs past the margin as inline math cannot break (live DFM 2026-09-26). */
  const displayed = (note: string): string => fitDisplays(note);
  const laidOut = (tex: string): string => (tex.startsWith("\\texttt{") ? tex : printedFragment(tex, "statement"));

  /** A text leaving an environment open, or closing one it does not open (`envImbalance`). */
  const crossesEnvs = (t: string): boolean => {
    const { close, open } = envImbalance(t);
    return close.length + open.length > 0;
  };
  /** The paper's theorem-like environments and `proof`: where a span crossing environments is cut. */
  const theoremEnvs = new Set(["proof", ...Object.entries({ ...BUILTIN_ENVS, ...(envs.newtheorem ?? {}) }).filter(([, k]) => k !== "other").map(([n]) => n)]);
  /**
   * Place an op whose printed span `[s0, e0)` of `file` the paper cuts across environments (a unit that
   * opens a nested lemma's proof): no block macro may hold one end of an environment, so only the
   * segments between the span's top-level environment markers are marked (`envCuts`: the markers of an
   * environment left open or closed, and of a theorem-like one or `proof`), the markers standing between
   * the blocks as printed. When the corrected text has the same markers, its segment i follows printed
   * segment i (a segment left as printed is not marked; one emptied reads "(removed)"); else, cut at
   * the unmatched markers alone when those agree; else each printed segment is marked and the corrected
   * text follows the last one as one block — verbatim when it crosses environments itself. Returns what
   * was widened or moved.
   */
  const placeCrossing = (file: string, s0: number, e0: number, op: Op, node: string, kind: AnnotationKind): string[] => {
    const orig = input.files[file]!;
    const span = orig.slice(s0, e0);
    const blue = op.blue;
    const keys = (c: ReturnType<typeof envCuts>): string => c.markers.map((m) => m.key).join();
    const cutBy = [(env: string, matched: boolean): boolean => !matched || theoremEnvs.has(env), (_env: string, matched: boolean): boolean => !matched];
    let red = envCuts(span, cutBy[0]!);
    // the corrected text of each printed segment (undefined: none paired with it)
    let pieces: Array<string | undefined> | null = blue === null ? [] : null;
    for (const cut of blue === null ? [] : cutBy) {
      const o = envCuts(span, cut);
      const b = envCuts(blue!, cut);
      if (keys(o) !== keys(b)) continue;
      red = o;
      pieces = b.segments.map((x) => blue!.slice(x.start, x.end));
      break;
    }
    const whole = pieces === null;
    if (whole) red = envCuts(span, cutBy[1]!);
    const last = red.segments.length - 1;
    const words = (x: string): string => x.replace(/\s+/g, " ").trim();
    const labels = [...span.matchAll(/\\label\s*\{([^{}]*)\}/gu)].map((m) => ({ at: s0 + m.index!, label: m[1]!.trim() }));
    const notes: string[] = [];
    red.segments.forEach((seg, k) => {
      const printed = orig.slice(s0 + seg.start, s0 + seg.end);
      const piece = whole ? (k === last ? (crossesEnvs(blue!) ? verbatimLike(blue!) : blue!) : undefined) : pieces![k];
      const t = trimSpan(orig, s0 + seg.start, s0 + seg.end);
      const kept = !whole && piece !== undefined && words(blueTex(printed)) === words(piece);
      // Each label of the printed span stands once in the corrected text: one printed outside this
      // segment's mark stays where it is printed (left unmarked, or carried by the mark it sits in, which
      // keeps the labels its correction drops), so the correction does not set it again.
      const elsewhere = new Set(labels.filter((l) => !t || l.at < t.start || l.at >= t.end).map((l) => l.label));
      const unlabelled = (p: string): string => p.replace(/\\vsLabel\{([^{}]*)\}/gu, (x, l: string) => (elsewhere.has(l.trim()) ? "" : x));
      const text = piece === undefined || kept ? null : unlabelled(piece).trim() || (t ? "\\textit{(removed)}" : null);
      const tail = after({ ...op, blue: text, note: k === last ? op.note : "" }, tagOf(node, kind));
      if (t && !kept) notes.push(...pushWrap(file, t.start, t.end, op.redMacro ?? "vsOriginal", tail, node).notes);
      else if (tail) {
        const r = pushEdit(file, t ? t.end : s0 + seg.start, 1, tail);
        if (r.moved) notes.push(r.moved);
      }
    });
    return notes;
  };

  /** Place one op, given in coordinates of a text whose map onto `file` is known. */
  const placeMapped = (file: string, map: number[], op: Op, node: string, kind: AnnotationKind, summary: string, extended: string[]): void => {
    const orig = input.files[file]!;
    const tail = after(op, tagOf(node, kind));
    if (op.end > op.start) {
      const s0 = map[op.start]!;
      const e0 = map[op.end - 1]! + 1;
      if (!Number.isFinite(s0) || !Number.isFinite(e0)) {
        unlocated.push({ node, kind, reason: "its span did not map onto the source", placed: null });
        return;
      }
      const w = safeSpan(orig, s0, e0, regionsOf(file));
      const clash = (wraps[file] ?? []).find((x) => x.start < w.end && w.start < x.end);
      let line = lineOf(orig, w.start);
      if (clash) {
        // (a corrected text crossing environments cannot stand in a block: verbatim)
        const r = pushEdit(file, clash.end, 1, after(op.blue !== null && crossesEnvs(op.blue) ? { ...op, blue: verbatimLike(op.blue) } : op, tagOf(node, `${kind}; overlapped`)));
        extended = [...extended, `overlaps the span of ${clash.node}; placed after it`, ...(r.moved ? [r.moved] : [])];
        line = lineOf(orig, r.at);
      } else if (crossesEnvs(orig.slice(s0, e0))) {
        extended = [...extended, ...placeCrossing(file, s0, e0, op, node, kind)];
      } else {
        extended = [...extended, ...pushWrap(file, s0, e0, op.redMacro ?? "vsOriginal", tail, node).notes];
      }
      records.push({ node, file, line, kind, located_by: op.how, summary, extended });
    } else {
      const r = pushEdit(file, op.start > 0 ? map[op.start - 1]! + 1 : map[0]!, 1, tail);
      records.push({ node, file, line: lineOf(orig, r.at), kind, located_by: op.how, summary, extended: r.moved ? [...extended, r.moved] : extended });
    }
  };

  /** Place ops given in env-body coordinates, falling back to the env span, then its end. */
  const placeInEnv = (env: TexEnv, region: Region, ops: Op[], node: string, kind: AnnotationKind, summary: string, extended: string[]): void => {
    const al = aligned(env, region);
    if (al?.map) {
      ops.forEach((op, k) => placeMapped(al.file, al.map!, op, node, kind, k === ops.length - 1 ? summary : `${summary} (part ${k + 1})`, k === 0 ? extended : []));
      return;
    }
    const tags = region === "body" ? envBounds(env) : null;
    const tail = ops.map((op) => after(op, tagOf(node, kind))).join("");
    if (!tags) {
      unlocated.push({ node, kind, reason: `environment ${env.id} (${region}) not found in ${env.lines.file}`, placed: null });
      log.push(`annotated paper: ${node} not located (environment ${env.id} not found in the source)`);
      return;
    }
    const orig = input.files[tags.file]!;
    const span = orig.slice(tags.bodyStart, tags.endStart);
    const safe = !/%|\\begin\s*\{(?:comment|verbatim\*?|lstlisting|minted)\}|\\iffalse/.test(span) && ops.some((o) => o.end > o.start);
    const inner = trimSpan(orig, tags.bodyStart, tags.endStart);
    if (safe && inner && !(wraps[tags.file] ?? []).some((w) => w.start < inner.end && inner.start < w.end)) {
      // Crossed-out text stays crossed out (red alone: the whole body may hold what a line cannot cross).
      const struck = ops.some((o) => o.redMacro === "vsStruck" || o.redMacro === "vsStruckRed");
      const r = pushWrap(tags.file, inner.start, inner.end, struck ? "vsStruckRed" : "vsOriginal", tail, node);
      records.push({ node, file: tags.file, line: lineOf(orig, r.start), kind, located_by: "env-span", summary, extended: [...extended, ...r.notes] });
      log.push(`annotated paper: ${node} marked on the whole body of ${env.id} (its sentences did not align with the source)`);
      return;
    }
    const line = lineOf(orig, pushEdit(tags.file, tags.endStart, 1, `${ops.map((op) => after(op, tagOf(node, `${kind}; unlocated`))).join("")} `).at);
    records.push({ node, file: tags.file, line, kind, located_by: "env-end", summary, extended });
    unlocated.push({ node, kind, reason: `the passage in ${env.id} could not be located`, placed: `${tags.file}:${line}` });
    log.push(`annotated paper: ${node} not located inside ${env.id}; written as a note at the end of the environment`);
  };

  // --- where a node's text sits: the paper's units (`units.ts`), whole by construction.
  interface Passage { env: TexEnv | null; region: Region; start: number; end: number; how: string }
  /** A statement's printed passage: the units of its environment's body, in env-body offsets. */
  const statementPassage = (s: CoreStatement): (Passage & { env: TexEnv; units: Unit[] }) | null => {
    const p = unitPassage(passageSrc, s.id);
    const env = p ? envById.get(p.env) : undefined;
    const reg = p ? units.region(p.env) : undefined;
    if (!p || !env || !reg) return null;
    // Its text (`statementSpan`: a list it covers whole is taken with its delimiters).
    const span = statementSpan(units, p);
    return { env, region: "body", start: span.start - reg.start, end: span.end - reg.start, how: "env", units: p.units };
  };
  const hypPassage = (id: string): Passage | { prose: true; start: number; end: number; how: string } | null => {
    const ref = refs?.assumptions.find((a) => a.id === id) ?? refs?.definitions.find((d) => d.id === id);
    const src = ref?.source as SourceRef | undefined;
    if (src && "prose" in src) {
      const o = sliceOffsets(input.flatText, src.slice);
      return o ? { prose: true, ...o, how: "slice" } : null;
    }
    if (src) {
      const env = envById.get(src.env);
      const region: Region = src.region === "proof" ? "proof" : "body";
      const text = env ? (region === "proof" ? env.proof : env.body) : null;
      if (!env || text === null) return null;
      if (src.sentences) {
        const sp = sentenceSpans(text);
        const [a, b] = src.sentences;
        if (sp[a - 1] && sp[b - 1]) return { env, region, start: sp[a - 1]!.start, end: sp[b - 1]!.end, how: "sentences" };
        return null;
      }
      if (src.slice) {
        const o = sliceOffsets(text, src.slice);
        return o ? { env, region, ...o, how: "slice" } : null;
      }
      return { env, region, start: 0, end: text.length, how: "env" };
    }
    // No reference core: search the copied text where its locator points.
    const node = transcribed.assumptions.find((a) => a.id === id) ?? transcribed.definitions.find((d) => d.id === id);
    if (!node) return null;
    const text = ("condition" in node ? node.condition : node.construction).trim();
    const loc = node.tex_locator;
    if (!loc || loc.env === "prose") {
      const at = input.flatText.indexOf(text);
      return at >= 0 ? { prose: true, start: at, end: at + text.length, how: "text" } : null;
    }
    for (const env of envs.envs) {
      for (const region of ["body", "proof"] as const) {
        const l = region === "proof" ? env.proofLines : env.lines;
        const t = region === "proof" ? env.proof : env.body;
        if (!l || t === null || locatorKey(l) !== locatorKey(loc)) continue;
        const at = t.indexOf(text);
        if (at >= 0) return { env, region, start: at, end: at + text.length, how: "text" };
      }
    }
    return null;
  };

  /** Place ops on a prose passage of the flat text: flat lines → original lines → aligned. */
  const placeProse = (p: { start: number; end: number; how: string }, ops: Op[], node: string, kind: AnnotationKind, summary: string): boolean => {
    const firstLine = input.flatText.slice(0, p.start).split("\n").length;
    const lastLine = input.flatText.slice(0, p.end).split("\n").length;
    const a = input.lineMap[firstLine - 1];
    const b = input.lineMap[lastLine - 1];
    if (!a || !b || a.file !== b.file || input.files[a.file] === undefined) return false;
    const orig = input.files[a.file]!;
    const ls = lineStarts(orig);
    const passage = input.flatText.slice(p.start, p.end);
    const map = alignToOriginal(orig, ls[Math.max(0, a.line - 2)] ?? 0, ls[b.line + 1] ?? orig.length, passage);
    if (!map) return false;
    // Only a span inside the passage has a place in the source.
    if (ops.some((op) => op.start < p.start || op.end > p.end || op.start > op.end)) return false;
    ops.forEach((op) => placeMapped(a.file, map, { ...op, start: op.start - p.start, end: op.end - p.start }, node, kind, summary, []));
    return true;
  };

  /** Widen a hypothesis's or definition's source slice to whole regions of `text` (math, environments,
   * brace groups), then shrink past labels; an empty result is an insertion. */
  const fitSpan = (text: string, start: number, end: number): { start: number; end: number; extended: string[] } => {
    const x = extendToRegions(texRegions(text), start, end);
    const t = trimSpan(text, x.start, x.end);
    return t ? { ...t, extended: x.extended } : { start: x.end, end: x.end, extended: x.extended };
  };
  /** A running-text passage of the flattened paper, trimmed. It is never widened to the regions around
   * it: over the whole paper those include the document environment itself, and `placeProse` maps only
   * the passage onto the source; `placeMapped` keeps the mapped span whole against the source file's own
   * regions. */
  const fitProse = (q: { start: number; end: number }): { start: number; end: number; extended: string[] } => {
    const t = trimSpan(input.flatText, q.start, q.end);
    return t ? { ...t, extended: [] } : { start: q.end, end: q.end, extended: [] };
  };

  /** The referee's finding on `id`: its detail and witness — the referee's current error verdict while
   * no repair is on file (a text sent back to the referee is printed as it wrote it again), else the
   * error ledger's record of the paper's error (a verdict on a repair is about the repair). */
  const errorText = (id: string): { detail: string; witness: string | null } | null => {
    const pe = input.paperErrors[id];
    // A finding the owner withdrew is no error of the paper: it is never shown as one.
    if (pe && pe.owner_decision !== "finding rejected") {
      const live = reviewOf.get(id);
      const repaired = patchOf.has(id) || unfixable.some((u) => u.node === id);
      if (!repaired && !input.suggestionRejected?.has(id) && live?.correctness === "error" && !live.owner_overruled) return { detail: cleanDetail(live.detail), witness: live.witness };
      return { detail: cleanDetail(pe.detail), witness: pe.witness };
    }
    const f = input.findings.find((x) => x.node === id && x.kind === "refuted");
    if (f) return { detail: cleanDetail(f.detail), witness: f.witness };
    const r = reviewOf.get(id);
    return r && !r.owner_overruled ? { detail: cleanDetail(r.detail), witness: r.witness } : null;
  };
  /**
   * The error as the paper's author reads it: the fixer's note `own` (a patch's, a suggestion's or an
   * unfixable entry's), else the referee's finding — its detail and the witness's gist — always
   * through the `ownerFacing` backstop. A pending weakening's note shows the receipt's "Gives up"
   * (`givesUp`).
   */
  const explanation = (id: string, own?: OwnerExplanationField | null, fallback?: { detail: string; witness: string | null } | null, opts: { omitGivesUp?: boolean; givesUp?: string } = {}): string => {
    const e = errorText(id) ?? (fallback ? { ...fallback, detail: cleanDetail(fallback.detail) } : null);
    const text = hasExplanation(own) ? own : null;
    if (!e && !text) return "";
    // The structure: labelled lines inside the note — "Claim: … / What is wrong: … (ending with its
    // Counterexample) / Proposed fix: … / Gives up: …".
    if (isStructuredExplanation(text)) {
      const shown = opts.givesUp !== undefined ? { ...text, gives_up: opts.givesUp.trim() || null } : text;
      const parts = explanationParts(shown, { ...opts, labels: paperLabelSet, quoteOf: units.textById });
      // Several defects each on a sub-line of their own (`\\vsSub`): the layout is the note's structure.
      const typeset = (t: string): string => safe(id, "explanation", authorWords(t), "fixer");
      if (parts.length > 0) return parts.map((p) => `\\vsLine\\textbf{${p.label}:} ${p.items && p.items.length > 1 ? p.items.map((t) => `\\vsSub ${typeset(t)}`).join(" ") : typeset(p.text)}`).join(" ");
    }
    const prose = ownerExplanation({ owner_explanation: text, detail: e?.detail ?? "", witness: e?.witness ?? null }, summarizeWitness, 3, { labels: paperLabelSet });
    // Composed from the referee's finding when the fixer wrote no note: the referee writes it again.
    return safe(id, "explanation", authorWords(prose), text ? "fixer" : "referee");
  };
  /** Whether a note text is the structure (labelled "Claim: … / What is wrong: …" lines). */
  const isStructuredNote = (t: string): boolean => t.includes("\\vsLine\\textbf{");
  /** How the author finds another result: "Theorem~\ref{label}", else "another result of the paper". */
  const theoremTitles = parseTheoremCounters(input.flatText).display;
  const refText = (id: string): string => {
    const st = transcribed.statements.find((x) => x.id === id);
    const env = st ? statementPassage(st)?.env : null;
    if (st?.cited_in && st.cited_in !== id) return `a result cited in the proof of ${refText(st.cited_in)}`;
    if (!env?.label) return "another result of the paper";
    // The title the paper declares for the environment, else the word its kind stands for.
    const word = theoremTitles[env.envName.replace(/\*$/u, "")] ?? resultWord({ kind: st?.kind, tex_locator: { env: env.envName } }, { ...BUILTIN_ENVS, ...(envs.newtheorem ?? {}) });
    return `${word}~\\ref{${env.label}}`;
  };
  const sectionLabels = new Map<string, string>();
  /**
   * How the author finds the part of the paper holding line `loc.line` of `loc.file`, by the paper's
   * own heading: "Appendix~\ref{…}" (after `\appendix`) or "Section~\ref{…}" — the heading's own
   * `\label`, else one added after the heading in the annotated copy — or, for an unnumbered heading,
   * its title quoted. Never a source file name (user rule 2026-09-25).
   */
  const sectionRef = (node: string, loc: { file: string; from?: number; line?: number }, envLabel: string | null = null): string => {
    const text = input.files[loc.file];
    const line = loc.from ?? loc.line ?? 1;
    // No heading to name: the page of the result.
    const page = envLabel ? `page~\\pageref{${envLabel}}` : "the paper";
    if (text === undefined) return page;
    const upTo = text.slice(0, lineStarts(text)[line] ?? text.length);
    const heads = [...upTo.matchAll(/\\((?:sub){0,2}section)(\*?)\s*(?:\[[^\]]*\])?\s*\{/gu)].filter((m) => !/%[^\n]*$/u.test(upTo.slice(0, m.index)));
    const h = heads.at(-1);
    if (!h) return page;
    let d = 0;
    let end = h.index! + h[0].length - 1;
    for (; end < text.length; end += 1) {
      if (text[end] === "\\") end += 1;
      else if (text[end] === "{") d += 1;
      else if (text[end] === "}" && --d === 0) break;
    }
    const title = text.slice(h.index! + h[0].length, end).trim();
    const headLine = lineOf(text, h.index!);
    const flatAt = input.lineMap.findIndex((x) => x.file === loc.file && x.line === headLine);
    const flatOffset = flatAt >= 0 ? lineStarts(input.flatText)[flatAt] ?? 0 : -1;
    const appendix = flatOffset >= 0 && /^[^%\n]*\\appendix\b/mu.test(input.flatText.slice(0, flatOffset));
    const word = appendix ? "Appendix" : "Section";
    if (h[2] === "*") return `the ${appendix ? "appendix" : "section"} \`\`${safe(node, "section title", title, null)}''`;
    const own = /^\s*\\label\s*\{([^{}]+)\}/u.exec(text.slice(end + 1));
    const key = `${loc.file}\u0000${h.index}`;
    let label = own?.[1] ?? sectionLabels.get(key);
    if (!label) {
      label = `vsSec${sectionLabels.size + 1}`;
      sectionLabels.set(key, label);
      // The corrected view drops every text that would refer to it.
      if (!input.correctedView) pushEdit(loc.file, end + 1, 1, `\\label{${label}}`);
    }
    return `${word}~\\ref{${label}}`;
  };
  /**
   * The note of a CONSEQUENTIAL patch (`consequential.ts`; user decision 2026-09-25): no defect of its
   * own, so no Claim / What is wrong / Why — one line, "Changed to follow the repair of <the
   * results it follows>: <reason>.", each result as the author finds it (`refText`), the reason's
   * owner-facing sentences. Audited as a prose note of kind "consequential edit".
   */
  const consequenceNote = (id: string, patch: LoosePatch): string => {
    const owners = [...new Set((patch.consequence_of ?? []).filter((o) => o !== id))];
    const refs = owners.map(refText);
    const list = refs.length <= 1 ? refs.join("") : `${refs.slice(0, -1).join(", ")} and ${refs.at(-1)}`;
    const reason = sentences(patch.reason ?? "").filter((x) => isOwnerFacing(x, paperLabelSet)).join(" ").trim();
    const lower = (t: string): string => (/^[A-Z][a-z]+\b/u.test(t) && !/^[A-Z][a-z]+[–-]/u.test(t) ? t.charAt(0).toLowerCase() + t.slice(1) : t);
    const text = `Changed to follow the repair of ${list || "another result of the paper"}${reason ? `: ${lower(stop(reason))}` : "."}`;
    return `\\vsLine ${safe(id, "consequential edit", text, "fixer")}`;
  };
  const weakening = (id: string, p: LoosePatch | null): string | null => {
    if (p?.accepted_weakening) return p.given_up ?? "";
    const f = input.findings.find((x) => x.node === id && (x as LooseFinding).patch?.narrowed) as LooseFinding | undefined;
    if (f?.patch?.narrowed) return f.patch.narrowed;
    const r = reviewOf.get(id);
    if (r?.weakens_contribution === true) return r.detail.replace(/^weakens the contribution:\s*/iu, "");
    return null;
  };
  /** Who wrote `weakening`'s text: the fixer (its accepted `given_up`, a narrowing), else the referee
   * (the review's grade). */
  const weakeningBy = (id: string, p: LoosePatch | null): FragmentProducer =>
    p?.accepted_weakening ? (p.given_up_by ?? "fixer") : input.findings.some((x) => x.node === id && (x as LooseFinding).patch?.narrowed) ? "fixer" : "referee";
  /** An intermediate result the runner narrowed automatically (not a main theorem): its note says
   * "This narrows the lemma: …" rather than that the fix weakens the result. */
  const autoNarrowed = (id: string, p: LoosePatch | null): boolean =>
    p?.accepted_weakening === true
      ? p.narrowed_by === "runner"
      : input.findings.some((x) => x.node === id && (x as LooseFinding).patch?.narrowed && (x as LooseFinding).patch?.narrowed_by === "runner");
  /** What a repair gives up, for the author (user rule 2026-09-25: no pipeline wording): a leading
   * "weakens the contribution:" goes. TeX. */
  const narrowingText = (node: string, w: string, by: FragmentProducer): string => {
    const t = w.replace(/^\s*weakens the contribution:\s*/iu, "").trim();
    return safe(node, "weakening", stop(t.charAt(0).toUpperCase() + authorWords(t).slice(1)), by);
  };
  /** The "Gives up" part of a repair that narrows the lemma or weakens the result (user rule
   * 2026-09-25: under its "Gives up:" label, never a line replacing it); null when it does neither. */
  const givesUpOf = (node: string, w: string | null, p: LoosePatch | null = null, by: FragmentProducer = "fixer"): string | null => {
    if (w === null) return null;
    const lead = autoNarrowed(node, p) ? "This narrows the lemma." : "This fix weakens the result.";
    return w.trim() ? `${narrowingText(node, w, by)} (${lead})` : lead;
  };
  const weakLine = (node: string, w: string | null, p: LoosePatch | null = null, by: FragmentProducer = "fixer"): string => {
    const g = givesUpOf(node, w, p, by);
    return g ? ` \\vsLine\\textbf{Gives up:} ${g}` : "";
  };
  /** `text` then a full stop, unless it already ends a sentence. */
  const stop = (text: string): string => (/[.!?]\s*$/u.test(text) ? text.trimEnd() : `${text}.`);
  /** The units a statement asserts: from the first to the last unit of its passage that is not only the
   * text of one of its hypotheses (every unit when each is). Indices into `p.units`. */
  const assertingUnits = (s: CoreStatement, p: { env: TexEnv; units: Unit[] }): [number, number] => {
    const reg = units.region(p.env.id)!;
    const deps = refs?.statements.find((x) => x.id === s.id)?.hypotheses ?? s.depends_on;
    const hyp = deps.flatMap((d) => {
      const q = hypPassage(d);
      return q && !("prose" in q) && q.env?.id === p.env.id && q.region === "body" ? [q] : [];
    });
    const asserting = p.units.map((u, i) => ({ u, i })).filter(({ u }) => !hyp.some((h) => h.start <= u.start - reg.start + 1 && h.end >= u.end - reg.start - 1));
    return asserting.length > 0 ? [asserting[0]!.i, asserting.at(-1)!.i] : [0, p.units.length - 1];
  };

  // --- decisions awaiting the owner (a halt; never at V6).
  const pendingWeak = new Map((input.pending?.weakening ?? []).map((w) => [w.node, w] as const));
  // A proposed repair's note says what is proposed and what it gives up; that it awaits the owner is
  // the block's label, and the choices are the decision card's (the page) and the halt's (stdout).
  /** The pending weakening's "Gives up": the receipt's `given_up`, what the owner is asked to accept
   * (never a rewrite of the note's), set as every other weakening text is (`narrowingText`: an added
   * hypothesis named by its content, never dropped with the sentence naming it). */
  const givesUpText = (w: PendingDecisions["weakening"][number]): string => narrowingText(w.node, w.given_up.trim(), w.given_up_by ?? "fixer");
  /** The fixer's note on `node` as its patch file holds it (a text sent back is printed as rewritten),
   * else the receipt's copy. */
  const fixerNote = (node: string, copy: OwnerExplanationField | null | undefined): OwnerExplanationField | null | undefined =>
    patchOf.get(node)?.owner_explanation ?? unfixable.find((u) => u.node === node)?.owner_explanation ?? copy;
  const weakNote = (w: PendingDecisions["weakening"][number]): string => {
    const text = explanation(w.node, fixerNote(w.node, w.owner_explanation), w, { omitGivesUp: true, givesUp: w.given_up });
    const confirming = input.pending?.confirming ? " \\vsLine This proposal is still being checked by the review; it can be decided once that pass has settled." : "";
    return `${text} \\vsLine\\textbf{Gives up:} ${givesUpText(w)}${confirming}`;
  };
  const weakSummary = (w: PendingDecisions["weakening"][number]): string =>
    `weakened repair proposed; gives up: ${w.given_up}`;

  // --- repairs are OPERATIONS on the paper's units (`ops.ts`): what the paper shows is the op itself —
  // red on the units a replace / delete takes, blue its TeX, an insertion exactly where it says. Nothing
  // is diffed or widened here: units are whole by construction; runs of a repair that touch are one block.
  /** A result's marks on one region: runs of replaced units (indices into the region's units, and
   * the `flat.tex` span the op replaces; `redOnly` for an unrepaired error's asserting run). */
  interface RangeMark { first: number; last: number; tex: string | null; redOnly?: boolean; start?: number; end?: number }
  /** The marks a repair's ops make on `part` of `env` (`resolveOps`; a repair that fails to resolve — a
   * stale file — marks nothing: it is logged and listed as unlocated, so the TODO list shows it).
   * `tex` is set as TeX for the reader (`texOf`, given the paper's text the op replaces). */
  const opMarks = (id: string, ops: readonly PatchOp[], part: "body" | "proof", texOf: (t: string, printed: string) => string): { ranges: RangeMark[] } => {
    const st = transcribed.statements.find((x) => x.id === id);
    const passage = st ? unitPassage(passageSrc, id) : null;
    const r = resolveOps(ops, { units, passage }, id);
    if (r.problems.length > 0) {
      log.push(`annotated paper: the ops of ${id} do not resolve on the paper's units (${r.problems.join("; ")}); not marked`);
      const kind: AnnotationKind = part === "proof" ? "corrected proof" : "error (repaired)";
      if (!unlocated.some((u) => u.node === id && u.kind === kind)) unlocated.push({ node: id, kind, reason: `its ops do not resolve on the paper's units (${r.problems.join("; ")})`, placed: null });
      return { ranges: [] };
    }
    const region = passage ? units.unitsOf(passage.env, part) : [];
    return { ranges: r.changes.filter((x) => x.part === part).map((c) => ({ first: region.indexOf(c.first), last: region.indexOf(c.last), tex: texOf(c.tex, units.flat.slice(c.start, c.end)), start: c.start, end: c.end })) };
  };
  /**
   * The ops that place a result's `marks` on `part` of `env` (region offsets), for `placeInEnv`.
   * Overlapping runs, and a repair's runs on adjacent units whose joined span cuts no list, are one red run — its units once — and one
   * blue block with the result's text for it (a statement or proof the repair rewrites whole reads as
   * one block, user decision 2026-09-29). A run's red is its text (`PaperUnits.spanOf`: one unit's content — an `\item` head is never
   * wrapped — or several units with every list they touch whole). `macros`: the blue and red macros. A
   * run the result leaves as printed up to spacing and punctuation is no change: nothing is marked.
   */
  const regionOps = (
    env: TexEnv,
    part: "body" | "proof",
    marks: RangeMark[],
    macros: { run: BlueMacro; red: "vsOriginal" | "vsStep" },
    how: string,
  ): Op[] => {
    const reg = units.region(env.id, part);
    const region = units.unitsOf(env.id, part);
    if (!reg) return [];
    const ops: Op[] = [];
    // An unrepaired error's red run takes every list it touches whole (a repair's runs already do: `ops.ts`).
    const closed = (m: RangeMark): RangeMark => {
      if (!m.redOnly || m.first === m.last) return m;
      let { first, last } = m;
      for (const u of region.slice(first, last + 1)) {
        for (const x of units.itemsOf(u)) {
          first = Math.min(first, region.indexOf(x));
          last = Math.max(last, region.indexOf(x));
        }
      }
      return { ...m, first, last };
    };
    // As printed: spacing, punctuation, grouping braces, math delimiters and the order of a
    // superscript and a subscript do not count.
    const bare = (x: string): string =>
      x
        .replace(new RegExp(String.raw`\^${SCRIPT_ARG}_${SCRIPT_ARG}`, "gu"), "_$2^$1")
        .replace(/\\(le|ge|ne)q(?![A-Za-z])/gu, "\\$1")
        .replace(/\\vsLabel\s*\{[^{}]*\}/gu, "")
        .replace(/\\(?:left|right|[Bb]igg?[lrm]?)(?![A-Za-z])|\\[,;:! ]|~|(?<!\\)[{}$]|[\s.,;:]/gu, "");
    /** A run's red span and the result's text for it: the printed units it leaves, its ops' TeX in place. */
    const runText = (members: readonly RangeMark[]): { from: number; to: number; text: string | null } => {
      const a = Math.min(...members.map((m) => m.first));
      const b = Math.max(...members.map((m) => m.last));
      const { start: from, end: to } = units.spanOf(region.slice(a, b + 1));
      const rs = members.filter((m) => !m.redOnly);
      if (rs.length === 0) return { from, to, text: null };
      const pieces = rs.map((m) => ({ start: m.start ?? region[m.first]!.content, end: m.end ?? region[m.last]!.end, text: m.tex ?? "" })).sort((p, q) => p.start - q.start || p.end - q.end);
      let t = "";
      let at = from;
      for (const p of pieces) {
        t += units.flat.slice(at, Math.max(at, p.start)) + p.text;
        at = Math.max(at, p.end);
      }
      return { from, to, text: blueTex(`${t}${units.flat.slice(at, to)}`) || "\\textit{(removed)}" };
    };
    /** A run the result leaves as printed up to spacing and punctuation, its details (`\\vsDetail`) apart: no
     * change. Its details are set unmarked after it, as side notes. */
    const unchanged = (members: readonly RangeMark[]): boolean => {
      if (members.some((m) => m.redOnly)) return false;
      const r = runText(members);
      if (r.text === null) return false;
      const { text, details } = splitDetails(r.text);
      if (bare(text) !== bare(blueTex(units.flat.slice(r.from, r.to)))) return false;
      for (const d of details) ops.push({ start: r.to - reg.start, end: r.to - reg.start, blue: null, note: d, noteMacro: "vsDetail", how });
      return true;
    };
    // A no-change run is dropped before runs are joined, so it never rides in a neighbour's block.
    const runs = marks.filter((m) => m.first >= 0 && m.last >= m.first).map(closed).filter((m) => !unchanged([m]));
    runs.sort((x, y) => x.first - y.first || x.last - y.last);
    const clusters: Array<{ a: number; b: number; members: RangeMark[] }> = [];
    for (const m of runs) {
      const last = clusters.at(-1);
      // Joined only where the joined span keeps every list whole (a block never cuts a list).
      const adjacent = !!last && !m.redOnly && !last.members.some((x) => x.redOnly) && m.first === last.b + 1 && !units.spanOf(region.slice(last.a, m.last + 1)).partial;
      if (last && (m.first <= last.b || adjacent)) {
        last.b = Math.max(last.b, m.last);
        last.members.push(m);
      } else clusters.push({ a: m.first, b: m.last, members: [m] });
    }
    for (const c of clusters) {
      if (unchanged(c.members)) continue;
      const { from, to, text } = runText(c.members);
      ops.push({ start: from - reg.start, end: to - reg.start, blue: text, macro: macros.run, note: "", how, redMacro: macros.red });
    }
    return ops.sort((u, v) => u.start - v.start || u.end - v.end);
  };

  /** One statement's annotation before it is placed: its marks and its note in parts. Env-body offsets. */
  interface StatementAnn {
    s: CoreStatement;
    env: TexEnv;
    how: string;
    kind: AnnotationKind;
    /** The passage the statement is printed on (its environment's body). */
    pStart: number;
    pEnd: number;
    marks: RangeMark[];
    /** The blue macro of its runs. */
    run: BlueMacro;
    summary: string;
    /** The note in parts: what is wrong (for the author), what follows it, what the repair gives
     * up, and the owner's answers. */
    explain: string;
    tail: string;
    givesUp: string | null;
    decision: string | null;
  }
  const noteOf = (a: Pick<StatementAnn, "explain" | "tail" | "givesUp" | "decision">): string =>
    // Each part on its own line: the explanation's fields, what follows it, what is given up, the decision.
    [a.explain, a.tail.trim() ? `\\vsLine ${a.tail.trim()}` : "", a.givesUp ? `\\vsLine\\textbf{Gives up:} ${a.givesUp}` : "", a.decision ? `\\vsLine ${a.decision}` : ""].filter((x) => x.trim()).join(" ").trim();

  const anns: StatementAnn[] = [];
  /** Statements not annotated because another statement node transcribes the same environment (an
   * older transcription the lint's rule (a) sends back to V1 to merge). */
  const shadowed = new Set<string>();
  const annotatedEnv = new Map<string, string>();
  const statementIds = new Set(transcribed.statements.map((s) => s.id));
  /** Whether the confirming check rejected `id`'s repair. */
  const rejectedRepair = (id: string): boolean => {
    const on = input.findings.filter((f) => f.node === id && f.kind !== "note") as LooseFinding[];
    // … or the referee's last word on the repaired node is an error and no finding carries a confirmed patch.
    return on.some((f) => f.patch?.confirmed === false) || (on.some((f) => f.kind === "refuted" && f.stage === "V1.5" && !f.patch) && !input.findings.some((f) => f.node === id && (f as LooseFinding).patch?.confirmed === true));
  };
  /** A published result a proof invokes by citation, repaired on that proof's result with no text of its
   * own (a note only, its patch neither rejected nor pending): the host's repair is what the paper shows. */
  const carriedByHost = (s: CoreStatement): boolean => {
    const patch = patchOf.get(s.id);
    if (!s.cited_in || !patch || patch.corrected_statement || (patch.ops ?? []).length > 0) return false;
    if (rejectedRepair(s.id) || pendingWeak.has(s.id) || unfixable.some((u) => u.node === s.id) || input.findings.some((f) => f.node === s.id && f.kind === "refuted")) return false;
    return (!!patchOf.get(s.cited_in) && !rejectedRepair(s.cited_in)) || pendingWeak.has(s.cited_in);
  };
  const andList = (xs: string[]): string => (xs.length <= 1 ? xs.join("") : `${xs.slice(0, -1).join(", ")} and ${xs.at(-1)}`);
  /** A corrected statement stored without ops (a hand-written file, a receipt): one replacement of the
   * whole printed statement. */
  // (the TeX as stored: the op's resolution keeps the labels the replaced units carry, and `runText`
  // turns it blue)
  const wholeStatement = (p: { units: Unit[] }, corrected: string): PatchOp => ({ op: "replace", unit: p.units[0]!.id, ...(p.units.length > 1 ? { to: p.units.at(-1)!.id } : {}), tex: corrected.trim() });
  for (const s of transcribed.statements) {
    const patch = patchOf.get(s.id) ?? null;
    const unfix = unfixable.find((u) => u.node === s.id) ?? null;
    const refuted = input.findings.filter((f) => f.node === s.id && f.kind === "refuted") as LooseFinding[];
    // The confirming check rejected the repair: whatever the finding it is recorded on (an error, a
    // clarification, a statement the paper leaves undetermined), its text is never shown as adopted.
    const rejectedPatch = rejectedRepair(s.id);
    const weak = pendingWeak.get(s.id) ?? null;
    if (!patch && !unfix && refuted.length === 0 && !weak) continue;
    const p = statementPassage(s);
    // A clarification is what the run recorded as one.
    // … and so is the repair of a statement the paper left undetermined: it states the reading adopted.
    const open = input.paperErrors[s.id]?.undetermined === true && !refuted.some((f) => !f.patch?.confirmed);
    // (one that weakens the claim keeps the repair's note: what it gives up is the owner's to see)
    const clar = !!patch && (input.paperErrors[s.id]?.kind === "clarification" || (open && weakening(s.id, patch) === null));
    // A patch that only follows another repair: no error of this result is on record.
    const consequence = !weak && !!patch && !rejectedPatch && (patch.consequence_of?.length ?? 0) > 0;
    const kind: AnnotationKind = weak ? "awaiting decision" : consequence ? "corrected proof" : patch && !rejectedPatch ? (clar ? "clarification" : "error (repaired)") : open ? "not determined" : "error (not repaired)";
    const err = errorText(s.id);
    if (!p && carriedByHost(s)) continue;
    if (!p) {
      unlocated.push({ node: s.id, kind, reason: "no environment of envs.json carries this statement", placed: null });
      log.push(`annotated paper: ${s.id} not located (no environment carries it)`);
      continue;
    }
    const other = annotatedEnv.get(p.env.id);
    if (other) {
      shadowed.add(s.id);
      unlocated.push({ node: s.id, kind, reason: `${other} already transcribes ${p.env.id} (one printed result is one statement node)`, placed: null });
      log.push(`annotated paper: ${s.id} not annotated — ${other} already transcribes ${p.env.id}`);
      continue;
    }
    annotatedEnv.set(p.env.id, s.id);
    const marks: RangeMark[] = [];
    const statementMarks = (ops: readonly PatchOp[], what: string): void => {
      marks.push(...opMarks(s.id, ops, "body", (t, printed) => latex(s.id, what, t, "fixer", "statement", printed)).ranges);
    };
    /** The unrepaired error's asserting units, red (no repair to show). */
    const assertingRed = (): void => {
      const [a, b] = assertingUnits(s, p);
      const region = units.unitsOf(p.env.id);
      marks.push({ first: region.indexOf(p.units[a]!), last: region.indexOf(p.units[b]!), tex: null, redOnly: true });
    };
    /** A repair's statement ops. One replacement of the whole statement when it is stored without ops,
     * and when the repair splits the result: the corrected statement is then one block, as each
     * corollary after it is (derived from its ops when the file holds only those). */
    const statementOps = (r: { ops?: PatchOp[]; corrected_statement: string | null; corollaries?: LooseCorollary[] }): PatchOp[] => {
      const ops = r.ops ?? [];
      const states = ops.some(isStatementOp);
      const whole = states && !r.corollaries?.length ? null : (r.corrected_statement ?? (states ? materializeRepair(ops, { units, passage: unitPassage(passageSrc, s.id) }, s.id).corrected_statement : null));
      return whole ? [...ops.filter(isProofOp), wholeStatement(p, whole)] : ops;
    };
    let run: BlueMacro = "vsCorrected";
    let summary = "";
    let explain = "";
    let tail = "";
    let givesUp: string | null = null;
    let decision: string | null = null;
    if (weak) {
      // The proposal's replacements, under the "awaiting your decision" labels; a note with the error
      // for the author, what it gives up and the owner's answers.
      run = "vsProposed";
      const ops = statementOps({ ...weak, corollaries: weak.corollaries ?? unfix?.suggested_repair?.corollaries });
      statementMarks(ops, "corrected statement");
      const states = ops.some(isStatementOp);
      // Nothing proposed in the statement's text: its asserting units red.
      if (!states) assertingRed();
      // The note opens at "Claim:" when the structured explanation is on file; only a note without one
      // opens with the proposal in words.
      const ex = explanation(s.id, fixerNote(s.id, weak.owner_explanation), weak, { omitGivesUp: true, givesUp: weak.given_up });
      explain = (isStructuredNote(ex) ? ex : `${states ? "The proposed repair restates the result as in blue." : ""} ${ex}`).trim();
      givesUp = givesUpText(weak);
      decision = weak.guidance ? `\\textbf{Your guidance (redo):} ${safe(s.id, "owner guidance", stop(weak.guidance.trim()), "other")}` : null;
      summary = weakSummary(weak);
    } else if (consequence && patch) {
      // Restated, or its proof corrected, only to follow another repair: the note says which.
      statementMarks(statementOps(patch), "corrected statement");
      explain = consequenceNote(s.id, patch);
      summary = `changed to follow the repair of ${(patch.consequence_of ?? []).join(", ")}`;
    } else if (patch && !rejectedPatch) {
      run = clar ? "vsClarified" : "vsCorrected";
      const ops = statementOps(patch);
      statementMarks(ops, "corrected statement");
      const states = ops.some(isStatementOp);
      if (clar) {
        const fromDetail = /to be written into it:\s*([\s\S]*)$/u.exec(input.paperErrors[s.id]?.detail ?? "")?.[1];
        const adopted = fromDetail ? safe(s.id, "adopted reading", ownerFacing(fromDetail, null, paperLabelSet), "referee") : "the statement in blue";
        const what = hasExplanation(patch.owner_explanation)
          ? explanation(s.id, patch.owner_explanation)
          : err ? safe(s.id, "ambiguity", ownerFacing(firstSentences(err.detail, 2), null, paperLabelSet), "referee") : "the printed wording admits more than one reading.";
        explain = `Ambiguous: ${what} Clarification: ${adopted.replace(/\.\s*$/u, "")}.`;
        summary = `Ambiguous: ${err ? firstSentences(err.detail, 1) : ""} Clarification: the statement in blue`;
      } else {
        const w = weakening(s.id, patch);
        explain = explanation(s.id, patch.owner_explanation, null, { omitGivesUp: w !== null });
        givesUp = givesUpOf(s.id, w, patch, weakeningBy(s.id, patch));
        summary = `${err ? firstSentences(err.detail, 1) : "error"} Proposed fix: ${states ? "restate the result as in blue" : "correct the proof"}` + (w !== null ? (autoNarrowed(s.id, patch) ? " (narrows the lemma)" : " (the fix weakens the result)") : "");
      }
    } else {
      const sug = unfix?.suggested_repair ?? null;
      const fsug = refuted.find((f) => f.suggested_repair)?.suggested_repair;
      const declined = unfix?.declined ?? refuted.find((f) => f.suggestion_declined)?.suggestion_declined;
      if (sug) {
        const cs = sug.corrected_statement ? ` restate it as: ${latex(s.id, "suggested corrected statement", blueTex(sug.corrected_statement), "fixer", "note")}` : "";
        tail = `\\textbf{Suggested repair (not applied):}${stop(cs)}${weakLine(s.id, sug.given_up ?? "", null, sug.given_up_by ?? "fixer")}`;
      } else if (fsug) {
        tail = `\\textbf{Suggested repair (not applied):} ${stop(safe(s.id, "suggested repair", suggestionSummaryTex(fsug), "fixer"))}`;
      } else if (patch && rejectedPatch) {
        tail = `\\textbf{Suggested repair (not applied; the confirming check rejected it):}${stop(patch.corrected_statement ? ` restate it as: ${latex(s.id, "rejected corrected statement", blueTex(patch.corrected_statement), "fixer", "note")}` : "")}`;
      } else if (unfix) {
        tail = `No repair keeps the result: ${safe(s.id, "unfixable reason", ownerFacing(unfix.reason.replace(/^any repair weakens the contribution:\s*/iu, ""), null, paperLabelSet), "fixer")}`;
      }
      if (declined) tail += ` The owner declined the suggested repair: ${safe(s.id, "declined repair", declined, "other")}`;
      explain = explanation(s.id, patch?.owner_explanation ?? unfix?.owner_explanation, null, { omitGivesUp: !!sug });
      assertingRed();
      summary = `${err ? firstSentences(err.detail, 1) : unfix?.reason ?? (kind === "not determined" ? "not determined as printed" : "refuted")}${sug || fsug ? " (a weaker repair is suggested, not applied)" : ""}`;
    }
    anns.push({ s, env: p.env, how: p.how, kind, pStart: p.start, pEnd: p.end, marks, run, summary, explain, tail, givesUp, decision });
  }

  // --- each statement's annotation: its marks, then one note after the statement.
  for (const a of anns) {
    const { env, s: st } = a;
    const ops = regionOps(env, "body", a.marks, { run: a.run, red: "vsOriginal" }, "units");
    const note = noteOf(a);
    if (note) {
      // After the last mark inside the passage when only labels / space follow it, else at the passage's end.
      const inside = ops.filter((o) => o.end <= a.pEnd && o.start >= a.pStart);
      const lastOp = inside.sort((u, v) => u.end - v.end || u.start - v.start).at(-1);
      if (lastOp && !lastOp.note && env.body.slice(lastOp.end, a.pEnd).replace(/\\label\s*\{[^{}]*\}/gu, "").trim() === "") lastOp.note = note;
      else ops.push({ start: a.pEnd, end: a.pEnd, blue: null, note, how: a.how });
    }
    ops.sort((u, v) => u.start - v.start || u.end - v.end);
    if (ops.length === 0) continue;
    const before = records.length;
    placeInEnv(env, "body", ops, st.id, a.kind, a.summary, []);
    // One index row per statement.
    const r0 = records[before];
    if (r0) records.splice(before, records.length - before, { ...r0, summary: a.summary });
  }

  /** Edits placed after the clarifications, at the same offset (a proof block for a result printed without one). */
  const afterReadings: Array<() => void> = [];
  // --- proof corrections (user rules 2026-09-24: every change to the paper is visible; proofs are
  // REVISED, not rewritten, and shown like statements). A repair's proof ops mark the paper's proof
  // itself: each replaced run of units red ("Original:") with its TeX right after in blue
  // ("Corrected:" / "Corrected (for the proposed statement):" — a proof change needs no owner
  // decision, user rule 2026-09-26; an insertion replaces the step it follows) — no note on the proof (the
  // explanation stays on the statement). A repair without proof ops (a result the paper prints no proof of, or a proof left as printed):
  // its proof note in one blue block after the node's PROOF as V1 located it (`TexEnv.proofLines`) —
  // "Corrected proof (confirmed):" / "Proof of the proposed statement:" (ops that do not
  // align with it: the block there, saying so). With no proof located: the block right after the
  // statement, naming the lemmas it rests on, or opening "(the paper's proof could not be located; the
  // corrected proof is given here)".
  {
    type ProofItem = { s: CoreStatement; env: TexEnv; note: string; pending: boolean; proofOnly: boolean; ops: PatchOp[]; umbrella: boolean; fallback?: boolean };
    const items: ProofItem[] = [];
    for (const st of transcribed.statements) {
      if (shadowed.has(st.id)) continue;
      const w = pendingWeak.get(st.id);
      const sug = w ? unfixable.find((u) => u.node === st.id)?.suggested_repair ?? null : null;
      const patch = patchOf.get(st.id);
      const rep = w ? sug : !rejectedRepair(st.id) ? patch : undefined;
      const note = rep?.proof_note?.trim() === PROOF_UNCHANGED ? "" : rep?.proof_note?.trim();
      const ops = (w ? (w.ops ?? sug?.ops ?? []) : (rep?.ops ?? [])).filter(isProofOp);
      if (!note && ops.length === 0) continue;
      const env = statementPassage(st)?.env ?? null;
      const kind: AnnotationKind = w ? "awaiting decision" : "corrected proof";
      if (!env && carriedByHost(st)) continue;
      if (!env) {
        unlocated.push({ node: st.id, kind, reason: "no environment of envs.json carries this statement (proof change)", placed: null });
        continue;
      }
      const proofOnly = w
        ? !w.corrected_statement && !(w.ops ?? sug?.ops ?? []).some(isStatementOp)
        : !patch?.corrected_statement && !(patch?.ops ?? []).some(isStatementOp);
      items.push({ s: st, env, note: note ?? "", pending: !!w, proofOnly, ops, umbrella: !!rep?.umbrella });
    }
    const toBlock: ProofItem[] = [];
    for (const it of items) {
      // An umbrella's printed proof is superseded whole (its blocks carry the proofs): the proof note
      // replaces it, marked like a proof op over every unit of the printed proof.
      const whole = it.ops.length === 0 && it.umbrella && it.note ? units.unitsOf(it.env.id, "proof") : [];
      if (whole.length > 0 && aligned(it.env, "proof")?.map) {
        const status = it.pending ? "proposed" : "corrected";
        const marks: RangeMark[] = [{ first: 0, last: whole.length - 1, tex: latex(it.s.id, `${status} step of the proof`, it.note, "fixer", "step") }];
        const ops = regionOps(it.env, "proof", marks, { run: it.pending ? "vsProposedStep" : "vsCorrectedStep", red: "vsStep" }, "umbrella proof");
        if (ops.length > 0) {
          placeInEnv(it.env, "proof", ops, it.s.id, it.pending ? "awaiting decision" : "corrected proof", `${status} proof of ${it.s.id} (an umbrella: its blocks carry the proofs)`, []);
          continue;
        }
      }
      if (it.ops.length === 0) {
        toBlock.push(it);
        continue;
      }
      const al = it.env.proof !== null && it.env.proofLines ? aligned(it.env, "proof") : null;
      const unresolved = resolveOps(it.ops, { units, passage: unitPassage(passageSrc, it.s.id) }, it.s.id).problems;
      if (!al?.map || unresolved.length > 0) {
        log.push(`annotated paper: the proof ops of ${it.s.id} could not be placed in its printed proof (${unresolved.length > 0 ? unresolved.join("; ") : "it did not align with the source"}); the corrected proof is given as one block`);
        toBlock.push({ ...it, ops: [], fallback: true });
        continue;
      }
      const status = it.pending ? "proposed" : "corrected";
      const marks = opMarks(it.s.id, it.ops, "proof", (t, printed) => latex(it.s.id, `${status} step of the proof`, t, "fixer", "step", printed)).ranges;
      const ops = regionOps(it.env, "proof", marks, { run: it.pending ? "vsProposedStep" : "vsCorrectedStep", red: "vsStep" }, "proof op");
      if (ops.length === 0) continue;
      placeInEnv(it.env, "proof", ops, it.s.id, it.pending ? "awaiting decision" : "corrected proof", `${status} steps of the proof of ${it.s.id}`, []);
    }
    /**
     * "This result prints no proof; it follows from Lemmas …(their corrected proofs are marked in
     * Appendix E.3 and E.4)." for statements the paper prints no proof of (user rule 2026-09-25): the
     * lemmas are EVERY printed result they rest on — their `depends_on` (as printed and as repaired),
     * the results whose repairs wire a hypothesis into them, and the results their proof note names
     * (by id or `\ref`) — in the paper's order; the parenthesis names, by the paper's own section
     * numbers (`sectionRef`), where the corrected proofs among them are marked. Null when there is none.
     */
    const corrected = new Set(items.map((x) => x.s.id));
    const restingLemmas = (of: string, env: TexEnv): string | null => {
      const note = items.find((x) => x.s.id === of)?.note ?? "";
      const labels = new Set(refLabels(note));
      const found = [
        ...(transcribed.statements.find((x) => x.id === of)?.depends_on ?? []),
        ...(input.core.statements.find((x) => x.id === of)?.depends_on ?? []),
        ...[...note.matchAll(/\b(?:lem|prop|thm|cor):[A-Za-z0-9_-]+/gu)].map((m) => m[0]),
        ...transcribed.statements.filter((x) => { const l = statementPassage(x)?.env?.label; return !!l && labels.has(l); }).map((x) => x.id),
      ];
      const byEnvId = new Map<string, { e: TexEnv; corrected: boolean }>();
      for (const id of found) {
        if (id === of) continue;
        const st = transcribed.statements.find((x) => x.id === id);
        const e = st ? statementPassage(st)?.env ?? null : null;
        if (!e?.label || e.id === env.id) continue;
        const prev = byEnvId.get(e.id);
        byEnvId.set(e.id, { e, corrected: (prev?.corrected ?? false) || corrected.has(id) });
      }
      const order = (e: TexEnv): number => envs.envs.indexOf(e);
      const list = [...byEnvId.values()].sort((x, y) => order(x.e) - order(y.e));
      if (list.length === 0) return null;
      const cap = (n: string): string => `${n.charAt(0).toUpperCase()}${n.slice(1)}`;
      const named = (es: TexEnv[]): string => {
        const names = new Set(es.map((e) => e.envName.replace(/\*$/u, "")));
        return names.size === 1
          ? `${cap([...names][0]!)}${es.length > 1 ? "s" : ""}~${andList(es.map((e) => `\\ref{${e.label}}`)).replace(/ and \\ref/u, " and~\\ref")}`
          : andList(es.map((e) => `${cap(e.envName.replace(/\*$/u, ""))}~\\ref{${e.label}}`));
      };
      const fixed = list.filter((x) => x.corrected).map((x) => x.e);
      const inOn = (w: string): string => (w.startsWith("page") ? `on ${w}` : `in ${w}`);
      const refs = [...new Set(fixed.map((e) => sectionRef(of, e.proofLines ?? e.lines, e.label)))];
      // "Appendices~\ref{a} and~\ref{b}" when they share the word.
      const word = /^(Appendix|Section)~/u.exec(refs[0] ?? "")?.[1];
      const where = refs.length > 1 && word && refs.every((r) => r.startsWith(`${word}~`))
        ? [`${word === "Appendix" ? "Appendices" : "Sections"}~${andList(refs.map((r) => r.slice(word.length + 1)))}`]
        : refs;
      const marked =
        fixed.length === 0
          ? ""
          : fixed.length === list.length
            ? ` (${fixed.length > 1 ? "their corrected proofs are" : "its corrected proof is"} marked ${where.map(inOn).join(" and ")})`
            : ` (the corrected proof${fixed.length > 1 ? "s" : ""} of ${named(fixed)} ${fixed.length > 1 ? "are" : "is"} marked ${where.map(inOn).join(" and ")})`;
      return `This result prints no proof; it follows from ${named(list.map((x) => x.e))}${marked}.`;
    };
    // One proof block per result (user rule 2026-09-26), in one place: after its printed proof (in the
    // corrected paper, in its place), else right after the result.
    for (const it of toBlock) {
      const { env } = it;
      const status = it.pending ? "proposed" : "corrected";
      const kind: AnnotationKind = it.pending ? "awaiting decision" : "corrected proof";
      const lead = it.proofOnly && !input.correctedView ? "The statement stands; the proof is completed as follows. " : "";
      const block = (head: string, how = ""): string => `${tagOf(it.s.id, `${kind}; ${how}`)}\\${it.pending ? "vsProposedProof" : "vsProof"}{${input.correctedView ? "" : head}${lead}${printedFragment(latex(it.s.id, "proof note", it.note, "fixer", "note"), "note")}}`;
      const place = (file: string, at: number, text: string, how: string): void => {
        const r = pushEdit(file, at, 1, text);
        records.push({ node: it.s.id, file, line: lineOf(input.files[file]!, r.at), kind, located_by: how, summary: `${status} proof of ${it.s.id}`, extended: r.moved ? [r.moved] : [] });
      };
      const loc = env.proofLines;
      const orig = loc ? input.files[loc.file] : undefined;
      if (loc && orig !== undefined) {
        const ls = lineStarts(orig);
        const at = loc.to < ls.length ? ls[loc.to]! : orig.length;
        const head = it.fallback ? "\\textit{(the corrected steps could not be marked in the printed proof; the corrected proof is given here)} \\vsLine " : "";
        // A block that is a whole proof (the amended one of unplaced steps, an umbrella's) replaces the
        // printed proof: the corrected paper writes it in its place, whose environment its view marks. Any
        // other note beside a printed proof may be partial: both stay, listed.
        const printed = input.correctedView && !it.pending && it.note && (it.fallback || it.umbrella) ? proofTags(env) : null;
        if (printed) {
          pushEdit(printed.file, printed.start, 2, `${tagOf(it.s.id, "printed proof")}\\vsPrintedProof{begin}`);
          pushEdit(printed.file, printed.end, 0, `${tagOf(it.s.id, "printed proof")}\\vsPrintedProof{end}`);
        }
        place(loc.file, at, `${at === orig.length && !orig.endsWith("\n") ? "\n" : ""}${block(head, it.fallback ? "steps unplaced" : "after-proof")}\n`, "after-proof");
        continue;
      }
      const tags = envBounds(env);
      if (!tags) {
        unlocated.push({ node: it.s.id, kind, reason: "neither its proof nor its environment was found (proof change)", placed: null });
        continue;
      }
      // No proof located: right after the result (after its clarifications, placed below) — naming every
      // lemma it rests on when the paper prints none (user rule 2026-09-24), else saying so.
      const restsOn = env.proof === null ? restingLemmas(it.s.id, env) : null;
      const head = restsOn ? `${restsOn} \\vsLine ` : "\\textit{(the paper's proof could not be located; the corrected proof is given here)} \\vsLine ";
      afterReadings.push(() => place(tags.file, tags.endEnd, `\n${block(head, restsOn ? "no printed proof" : "no proof located")}`, restsOn ? "after-env (no printed proof)" : "after-env (no proof located)"));
      log.push(`annotated paper: ${restsOn ? "the paper prints no proof of" : "no proof located for"} ${it.s.id}; the corrected proof follows the result`);
    }
  }


  // --- repairs of a hypothesis or definition of the paper (not a statement): its text replaced.
  for (const patch of patches) {
    if (statementIds.has(patch.node)) continue;
    // A repair that replaces no text of it only pins how it is read: a clarification — its readings are
    // placed as such below, and the passage stands as printed, unmarked.
    if ((patch.ops?.length ?? 0) === 0 && !patch.corrected_statement) continue;
    const err = errorText(patch.node);
    const ex = explanation(patch.node, patch.owner_explanation, null, { omitGivesUp: weakening(patch.node, patch) !== null });
    const note = `${ex}${weakLine(patch.node, weakening(patch.node, patch), patch, weakeningBy(patch.node, patch))}`.trim();
    const alg = (patch.ops?.length ?? 0) > 0 ? unitPassage(passageSrc, patch.node) : null;
    const algReg = alg?.span ? units.region(alg.env) : undefined;
    const blue = patch.corrected_statement && !algReg ? latex(patch.node, "corrected text", blueTex(patch.corrected_statement), "fixer") : null;
    const summary = `${err ? firstSentences(err.detail, 1) : "error"} (hypothesis/definition)`;
    const q = hypPassage(patch.node);
    const kind: AnnotationKind = "error (repaired)";
    if (!q) {
      unlocated.push({ node: patch.node, kind, reason: "its source passage was not found", placed: null });
      log.push(`annotated paper: ${patch.node} not located (its source passage was not found)`);
      continue;
    }
    // An algorithm is marked step by step inside its float (a float cannot sit in a block, and the
    // corrected paper then carries the step in place): the replaced text red, its replacement blue
    // after it, the step's command outside both. A control line opens or closes a block of the
    // algorithm and cannot be wrapped: its replacement is printed after the algorithm, as source.
    if (alg && algReg) {
      const r = resolveOps(patch.ops!, { units, passage: alg }, patch.node);
      if (r.problems.length > 0) {
        unlocated.push({ node: patch.node, kind, reason: `its ops do not resolve on the paper's units (${r.problems.join("; ")})`, placed: null });
        log.push(`annotated paper: the ops of ${patch.node} do not resolve on the paper's units (${r.problems.join("; ")}); not marked`);
        continue;
      }
      // In the passage's coordinates: the running text's (`flat.tex`), or the environment body's.
      const base = "prose" in q ? 0 : algReg.start;
      const tail = ("prose" in q ? q.end : algReg.end) - base;
      const changes = r.changes.filter((c) => c.part === "body").sort((a, b) => a.start - b.start);
      const ops = changes.map((c, k): Op => {
        const last = k === changes.length - 1 ? note : "";
        const printed = input.flatText.slice(c.start, c.end);
        if (isControlLine(printed)) {
          log.push(`annotated paper: ${patch.node}: a control line of the algorithm (${c.first.id}) cannot be marked in place; its replacement is printed after the algorithm`);
          return { start: tail, end: tail, blue: `\\texttt{${verbatimLike(printed).slice("\\texttt{".length, -1)} --- replaced by: ${verbatimLike(c.tex).slice("\\texttt{".length, -1)}}`, macro: "vsCorrected", note: last, how: "units (control line)" };
        }
        return { start: c.start - base, end: c.end - base, blue: latex(patch.node, "corrected step", blueTex(c.tex), "fixer"), macro: "vsCorrected", note: last, how: "units" };
      });
      if ("prose" in q) {
        if (!placeProse(q, ops, patch.node, kind, summary)) {
          unlocated.push({ node: patch.node, kind, reason: "its running-text passage did not align with the source", placed: null });
          log.push(`annotated paper: ${patch.node} not located (running text did not align)`);
        }
      } else placeInEnv(q.env!, q.region, ops, patch.node, kind, summary, []);
      continue;
    }
    if ("prose" in q) {
      const f = fitProse(q);
      const ok = placeProse(q, [{ start: f.start, end: f.end, blue, macro: "vsCorrected", note, how: q.how }], patch.node, kind, summary);
      if (!ok) {
        unlocated.push({ node: patch.node, kind, reason: "its running-text passage did not align with the source", placed: null });
        log.push(`annotated paper: ${patch.node} not located (running text did not align)`);
      }
      continue;
    }
    const text = q.region === "proof" ? q.env!.proof! : q.env!.body;
    const f = fitSpan(text, q.start, q.end);
    placeInEnv(q.env!, q.region, [{ start: f.start, end: f.end, blue, macro: "vsCorrected", note, how: q.how }], patch.node, kind, summary, f.extended);
  }

  // --- an assumption or definition no result uses after the repairs: every result that used it was
  // repaired away from it (its repair supersedes or drops it), so the repaired core leaves it out. Its
  // printed text is crossed out unit by unit, with one line naming those results; whether to delete it
  // is the author's (the paper's discussion may still refer to it). One printed inside a result's
  // statement is marked by that result's repair; one with an entry of its own by that entry.
  const kept = new Set([...core.assumptions, ...core.definitions].map((n) => n.id));
  const ownEntry = new Set([...patches.map((p) => p.node), ...unfixable.map((u) => u.node)]);
  const statementEnvs = new Set(transcribed.statements.flatMap((s) => statementPassage(s)?.env.id ?? []));
  for (const h of [...transcribed.assumptions, ...transcribed.definitions]) {
    if (kept.has(h.id) || ownEntry.has(h.id)) continue;
    const users = transcribed.statements.filter((s) => s.depends_on.includes(h.id));
    const repairedAway = (s: CoreStatement): boolean => [...(patchOf.get(s.id)?.supersedes ?? []), ...(patchOf.get(s.id)?.drops ?? [])].includes(h.id);
    if (users.length === 0 || !users.every(repairedAway)) continue;
    const q = hypPassage(h.id);
    if (q && !("prose" in q) && statementEnvs.has(q.env!.id)) continue;
    const kind: AnnotationKind = "no longer used";
    const summary = `no result uses it after the repairs (${users.map((s) => s.id).join(", ")})`;
    const named = [...new Set(users.map((s) => refText(s.id)))];
    const labelled = named.filter((r) => r !== "another result of the paper");
    const one = users.length === 1;
    const who = labelled.length === 0 ? (one ? "the result that used it" : "the results that used it") : labelled.length < named.length ? `${andList(labelled)} and other results of the paper` : andList(labelled);
    const what = transcribed.assumptions.some((a) => a.id === h.id) ? "assumption" : "definition";
    const note = safe(h.id, "no longer used", `No result uses this ${what} after the repairs: ${who} now ${one ? "states the conditions it uses" : "state the conditions they use"}.`, null);
    if (!q) {
      unlocated.push({ node: h.id, kind, reason: "its source passage was not found", placed: null });
      log.push(`annotated paper: ${h.id} (no longer used) not located (its source passage was not found)`);
      continue;
    }
    if ("prose" in q) {
      const f = fitProse(q);
      const op: Op = { start: f.start, end: f.end, blue: null, note, how: q.how, redMacro: struckMacro(input.flatText.slice(f.start, f.end)) };
      if (!placeProse(q, [op], h.id, kind, summary)) {
        unlocated.push({ node: h.id, kind, reason: "its running-text passage did not align with the source", placed: null });
        log.push(`annotated paper: ${h.id} (no longer used) not located (running text did not align)`);
      }
      continue;
    }
    const env = q.env!;
    const text = q.region === "proof" ? env.proof! : env.body;
    // Unit by unit (an `\item` head is never wrapped), so that a display between sentences breaks no line.
    const reg = units.region(env.id, q.region);
    const inside = reg ? units.unitsOf(env.id, q.region).filter((u) => u.content - reg.start < q.end && u.end - reg.start > q.start) : [];
    const segs = reg && inside.length > 0 ? inside.map((u) => ({ start: Math.max(u.content - reg.start, q.start), end: Math.min(u.end - reg.start, q.end) })) : [fitSpan(text, q.start, q.end)];
    const ops = segs.map((s, k): Op => ({ start: s.start, end: s.end, blue: null, note: k === segs.length - 1 ? note : "", how: q.how, redMacro: struckMacro(text.slice(s.start, s.end)) }));
    placeInEnv(env, q.region, ops, h.id, kind, summary, []);
  }

  // --- refutations on nodes that are no statement or hypothesis of the core.
  const known = new Set([...transcribed.statements, ...transcribed.assumptions, ...transcribed.definitions].map((n) => n.id));
  for (const f of input.findings) {
    if (f.kind !== "refuted" || known.has(f.node)) continue;
    unlocated.push({ node: f.node, kind: "error (not repaired)", reason: `a refutation on a node the core does not carry: ${plainLine(f.detail, 120)}`, placed: null });
    log.push(`annotated paper: refutation on ${f.node} not located (not a node of the core)`);
  }

  /** One op on a node's passage: a statement's asserting sentences (red) or the end of its
   * environment body (`red` false: a note only); a hypothesis or definition's source passage. */
  /** The printed result a statement is shown at: itself, or — a corollary a repair split off, a
   * published result a proof invokes by citation — the result it was split from, whose proof invokes it. */
  const hostOf = (s: CoreStatement): CoreStatement => transcribed.statements.find((x) => x.id === (s.split_from ?? s.cited_in)) ?? s;
  const placeOnNode = (id: string, red: boolean, op: Omit<Op, "start" | "end" | "how">, kind: AnnotationKind, summary: string): void => {
    const miss = (reason: string): void => {
      unlocated.push({ node: id, kind, reason, placed: null });
      log.push(`annotated paper: ${kind} on ${id} not located (${reason})`);
    };
    const st = transcribed.statements.find((x) => x.id === id);
    if (st) {
      const p = statementPassage(st);
      // A published result a proof invokes by citation has no environment: its passage is in that proof.
      const hostEnv = !p && st.cited_in ? statementPassage(hostOf(st))?.env : undefined;
      const at = hostEnv?.proof ? hostEnv.proof.indexOf(st.statement) : -1;
      if (hostEnv && at >= 0) {
        const f = red ? fitSpan(hostEnv.proof!, at, at + st.statement.length) : { start: at + st.statement.length, end: at + st.statement.length, extended: [] };
        return placeInEnv(hostEnv, "proof", [{ ...op, start: f.start, end: f.end, how: "units" }], id, kind, summary, f.extended);
      }
      if (!p) return miss("no environment of envs.json carries this statement");
      if (!red) return placeInEnv(p.env, "body", [{ ...op, start: p.end, end: p.end, how: p.how }], id, kind, summary, []);
      // Its asserting units red — item by item when they take list items (an `\item` head is never
      // wrapped) — the blocks after the last.
      const reg = units.region(p.env.id)!;
      const [a, b] = assertingUnits(st, p);
      const run = p.units.slice(a, b + 1);
      const segs = run.some((u) => u.kind === "item") ? run.map((u) => [u.content, u.end] as const) : [[run[0]!.content, run.at(-1)!.end] as const];
      const ops = segs.map(([s0, e0], k) => (k === segs.length - 1 ? { ...op, start: s0 - reg.start, end: e0 - reg.start, how: "units" } : { start: s0 - reg.start, end: e0 - reg.start, blue: null, note: "", how: "units" }));
      placeInEnv(p.env, "body", ops, id, kind, summary, []);
      return;
    }
    const q = hypPassage(id);
    if (!q) return miss("its source passage was not found");
    if ("prose" in q) {
      const f = red ? fitProse(q) : { start: q.end, end: q.end, extended: [] };
      if (!placeProse(q, [{ ...op, start: f.start, end: f.end, how: q.how }], id, kind, summary)) miss("its running-text passage did not align with the source");
      return;
    }
    const text = q.region === "proof" ? q.env!.proof! : q.env!.body;
    const f = red ? fitSpan(text, q.start, q.end) : { start: q.end, end: q.end, extended: [] };
    placeInEnv(q.env!, q.region, [{ ...op, start: f.start, end: f.end, how: q.how }], id, kind, summary, f.extended);
  };

  // --- a weakened repair pending on a hypothesis or definition (a statement's is placed above).
  for (const w of input.pending?.weakening ?? []) {
    if (statementIds.has(w.node)) continue;
    const blue = w.corrected_statement ? latex(w.node, "corrected statement", blueTex(w.corrected_statement), "fixer") : null;
    placeOnNode(w.node, true, { blue, macro: "vsProposed", note: weakNote(w) }, "awaiting decision", weakSummary(w));
  }

  // --- a proposed F-stage rewind: each routed finding red on its node, the finding in the note.
  const rw = input.pending?.rewind ?? null;
  for (const t of rw?.targets ?? []) {
    const note =
      `${asWritten(t.node, "rewind note", stop(ownerFacing(cleanDetail(t.reason), null, paperLabelSet)))} ` +
      "Awaiting your decision: have this statement repaired, keep it as printed (say where the paper grants what the finding says it lacks), " +
      "or keep it under a reading you state (the finding misreads the paper; your reading binds the formalization).";
    placeOnNode(t.node, true, { blue: null, note, noteMacro: "vsRewind" }, "awaiting decision", `rewind proposed by ${rw!.stage} (${t.axis}): ${firstSentences(cleanDetail(t.reason), 1)}`);
  }

  // --- a patch cap: a note on each node the stopped round would carry.
  const cap = input.pending?.cap ?? null;
  for (const f of cap?.findings ?? []) {
    const note =
      `The repair of this result has not settled within the ${cap!.rounds} attempt(s) allowed. The open finding: ${safe(f.id, "cap note", stop(ownerFacing(cleanDetail(f.detail), null, paperLabelSet)), "referee")} ` +
      "Awaiting your decision: allow further repair attempts, or stop here and report the result as it stands.";
    const summary = `patch cap ${cap!.counter} ${cap!.rounds}/${cap!.cap}: ${firstSentences(cleanDetail(f.detail), 1)}`;
    placeOnNode(f.id, false, { blue: null, note, noteMacro: "vsCap" }, "awaiting decision", summary);
  }

  // --- readings adopted for formalization, still standing as assumptions: once per environment and
  // reading text, the owner's under its own label; a reading of a hypothesis or definition once, under
  // the environment printing it — else under the first result using it (the results after it rest on
  // the same reading).
  const shownReading = new Set<string>();
  const shownPin = new Set<string>();
  // In paper order, so a hypothesis's reading lands under the first result the reader meets using it.
  const envOrder = new Map(envs.envs.map((e, i) => [e.id, i] as const));
  const paperOrder = (s: CoreStatement): number => envOrder.get(statementPassage(hostOf(s))?.env?.id ?? "") ?? Number.MAX_SAFE_INTEGER;
  const resultOfEnv = new Map(core.statements.flatMap((s) => {
    const env = statementPassage(s)?.env;
    return env ? [[env.id, s.id] as const] : [];
  }));
  /** Where a hypothesis or definition is printed: its environment (in a statement, not a proof), and
   * the result printing it there. */
  /** Where a result stated in running text ends (it has no `\\end{…}`): the end of its last line. */
  const proseEnd = (env: TexEnv): { file: string; endEnd: number } | null => {
    const orig = input.files[env.lines.file];
    // … and a result the segmenter cut (one stated inside another's proof): no environment of its own
    // name is in the source either; it ends where its lines end
    if (orig === undefined || !(env.envName.startsWith("prose:") || env.envName === "segment")) return null;
    const next = lineStarts(orig)[env.lines.to];
    return { file: env.lines.file, endEnd: next === undefined ? orig.length : next - 1 };
  };
  const homeOf = (id: string): { env: TexEnv; result: string | null } | null => {
    const h = hypPassage(id);
    return h && "env" in h && h.env && h.region === "body" && envBounds(h.env) ? { env: h.env, result: resultOfEnv.get(h.env.id) ?? null } : null;
  };
  /** The conditions result `id` carries beyond `text`, its statement as it now reads, one per wording
   * (spacing ignored). One is left out only when a whole sentence of the statement is that condition:
   * words found inside another sentence state nothing, and matching them would drop it from the paper. */
  const bare = (t: string): string => t.replace(/\s+/gu, "").replace(/\.$/u, "");
  const conditionsToState = (id: string, text: string): ReturnType<typeof conditionsOn> => {
    const stated = new Set(sentenceSpans(text).map((sp) => bare(text.slice(sp.start, sp.end))));
    return conditionsOn(core, id).filter((c, i, all) => !stated.has(bare(c.condition)) && all.findIndex((x) => bare(x.condition) === bare(c.condition)) === i);
  };
  const conditionText = (node: string, c: { condition: string; by: "referee" | "owner" | "repair" }): string =>
    safe(node, "condition added", c.condition, c.by === "owner" ? "other" : c.by === "repair" ? "fixer" : "referee");
  // --- a repair's corollaries: each a block of its own right after the result it is split from — its
  // statement, then its proof. A proposal's, under the "awaiting your decision" label. The corrected
  // paper follows the paper's own convention for the result: when its proof is printed elsewhere (not
  // right after its statement), the corollary's statement stays here and its proof goes after that proof.
  for (const s of transcribed.statements) {
    if (shadowed.has(s.id)) continue;
    const w = pendingWeak.get(s.id);
    const patch = patchOf.get(s.id);
    const cors = w ? (w.corollaries ?? unfixable.find((u) => u.node === s.id)?.suggested_repair?.corollaries ?? []) : patch && !rejectedRepair(s.id) ? (patch.corollaries ?? []) : [];
    if (cors.length === 0) continue;
    const umbrella = !!(w ? unfixable.find((u) => u.node === s.id)?.suggested_repair : patch)?.umbrella;
    const env = statementPassage(s)?.env ?? null;
    const tags = env ? envBounds(env) ?? proseEnd(env) : null;
    const kind: AnnotationKind = w ? "awaiting decision" : "error (repaired)";
    if (!tags) {
      unlocated.push({ node: s.id, kind, reason: `the environment of the result its ${cors.length} corollar${cors.length === 1 ? "y is" : "ies are"} split from was not found`, placed: null });
      log.push(`annotated paper: the corollaries split off ${s.id} not located (its environment was not found)`);
      continue;
    }
    const named = refText(s.id);
    const of = named === "another result of the paper" ? "the result above" : named;
    // The result's proof, when the paper prints it away from the statement (an appendix, a later section).
    const loc = input.correctedView && !w ? env!.proofLines : null;
    const proofFile = loc ? input.files[loc.file] : undefined;
    const between = loc && loc.file === env!.lines.file && loc.from > env!.lines.to ? input.files[loc.file]!.split("\n").slice(env!.lines.to, loc.from - 1) : null;
    const elsewhere = loc && proofFile !== undefined && !between?.every((l) => l.trim() === "" || l.trim().startsWith("%")) ? { file: loc.file, at: lineStarts(proofFile)[loc.to] ?? proofFile.length, text: proofFile } : null;
    // After the result's own notes and readings (and its proof, when written after it): they are read
    // with the statement, the corollaries after it.
    for (const c of cors) afterReadings.push(() => {
      const id = splitCorollaryId(s.id, c.statement);
      const title = c.title?.trim() ? safe(s.id, "corollary title", stop(c.title.trim()), "fixer") : "";
      const statement = laidOut(latex(s.id, "corollary", blueTex(c.statement), "fixer"));
      const proof = printedFragment(latex(s.id, "corollary proof", c.follows.trim(), "fixer", "note"), "note");
      // The conditions added to the block are the last paragraph of its statement.
      const added = conditionsToState(id, c.statement);
      const stated = added.length > 0 ? `${statement}\\vsPar ${conditionParagraph(added.map((x) => stop(conditionText(s.id, x))))}` : statement;
      const body = elsewhere ? stated : `${stated} ${COROLLARY_PROOF} ${proof}`;
      // The corrected paper never says what a corollary was split from: its view carries the title there.
      const args = input.correctedView ? `{${title}}{${body}}` : `{${of}}{${title ? `\\textbf{${title}} ` : ""}${body}}`;
      // A corollary of the corrected result, or a proposition the printed statement bundled in: its proof says.
      const macros = SPLIT_MACROS[splitKind(c.follows, s.tex_locator?.label, umbrella)];
      const r = pushEdit(tags.file, tags.endEnd, 1, `\n${tagOf(id, kind)}\\${w ? macros.proposed : macros.block}{${id}}${args}`);
      records.push({ node: s.id, file: tags.file, line: lineOf(input.files[tags.file]!, r.at), kind, located_by: "after-env", summary: `corollary ${id} split off by the repair: ${plainLine(c.statement, 120)}`, extended: r.moved ? [r.moved] : [] });
      for (const x of added) records.push({ node: s.id, file: tags.file, line: lineOf(input.files[tags.file]!, r.at), kind: "condition added", located_by: "after-env", summary: `${x.id}: ${x.condition} (condition of corollary ${id})`, extended: [] });
      // A corollary that is not written (its statement does not typeset) has no proof to place.
      if (!elsewhere || statement.trimStart().startsWith("\\texttt{")) return;
      const p = pushEdit(elsewhere.file, elsewhere.at, 1, `${elsewhere.at === elsewhere.text.length && !elsewhere.text.endsWith("\n") ? "\n" : ""}${tagOf(id, kind)}\\${macros.proof}{${id}}{${title}}{${proof}}\n`);
      records.push({ node: s.id, file: elsewhere.file, line: lineOf(elsewhere.text, p.at), kind, located_by: "after-proof", summary: `proof of corollary ${id}, after the proof of ${s.id}`, extended: p.moved ? [p.moved] : [] });
    });
  }
  for (const s of [...core.statements].sort((a, b) => paperOrder(a) - paperOrder(b))) {
    // A symbol's reading is shown once, where the symbol is introduced (below), not under each result.
    const pins = pinsOn(core, s.id).filter((p) => !p.node.startsWith(SYMBOL_PIN_OF));
    if (pins.length === 0) continue;
    const p = statementPassage(hostOf(s));
    const ownTags = p?.env ? envBounds(p.env) ?? proseEnd(p.env) : null;
    for (const pin of pins) {
      const ofOther = pin.node !== s.id;
      const once = ofOther && !statementIds.has(pin.node);
      if (once && shownPin.has(pin.id)) continue;
      // A hypothesis or definition printed in an environment: its reading goes there.
      const home = once ? homeOf(pin.node) : null;
      const under = home ? home.result ?? pin.node : s.id;
      const tags = home ? envBounds(home.env) : ownTags;
      const of = statementIds.has(pin.node) ? refText(pin.node) : transcribed.definitions.some((d) => d.id === pin.node) ? "a definition this result uses" : "one of its hypotheses";
      const note = `${safe(under, pin.by === "owner" ? "owner reading" : "clarification (reading)", pin.reading, pin.by === "owner" ? "other" : "referee", pin.node)}${ofOther && (!home || home.result) && !input.correctedView ? ` (the reading of ${of})` : ""}`;
      const summary = `${pin.id}: ${pin.reading}${pin.node !== under ? ` (reading of ${pin.node})` : ""}`;
      if (!tags) {
        unlocated.push({ node: s.id, kind: "clarification (reading)", reason: `${pin.id}: the statement's environment was not found`, placed: null });
        log.push(`annotated paper: pin ${pin.id} on ${s.id} not located`);
        continue;
      }
      if (once) shownPin.add(pin.id);
      const key = `${tags.file}\u0000${tags.endEnd}\u0000${pin.by}\u0000${pin.reading.trim()}`;
      const at = shownReading.has(key) ? safeInsertionPoint(input.files[tags.file]!, tags.endEnd, regionsOf(tags.file)).pos : pushEdit(tags.file, tags.endEnd, 1, `\\${pin.by === "owner" ? "vsReadingOwner" : "vsReading"}{${note}}`).at;
      shownReading.add(key);
      records.push({ node: under, file: tags.file, line: lineOf(input.files[tags.file]!, at), kind: "clarification (reading)", located_by: "after-env", summary, extended: [] });
    }
  }

  // --- conditions the verified statement carries beyond the printed text (the referee's bookkeeping,
  // the owner's side conditions, a repair's `conditions`): a note at the end of every result carrying one — inside its
  // environment, so the corrected paper states it in the result. Nothing printed is marked.
  for (const s of core.statements) {
    if (s.split_from) continue; // stated in its block (above)
    const added = conditionsToState(s.id, s.statement);
    if (added.length === 0) continue;
    const env = statementPassage(s)?.env ?? null;
    const tags = env ? envBounds(env) : null;
    const end = env && !tags ? proseEnd(env) : null;
    // A published result a proof invokes by citation has no environment: its condition goes after the
    // result whose proof cites it, as its readings do.
    const host = !env && s.cited_in ? statementPassage(hostOf(s))?.env ?? null : null;
    const after = host ? envBounds(host) ?? proseEnd(host) : null;
    const place = tags ? { file: tags.file, at: tags.endStart, how: "env-end" } : end ? { file: end.file, at: end.endEnd, how: "after-env" } : after ? { file: after.file, at: after.endEnd, how: "after-env" } : null;
    for (const c of added) {
      if (!place) {
        unlocated.push({ node: s.id, kind: "condition added", reason: `${c.id}: the statement's environment was not found — the condition: ${plainLine(c.condition)}`, placed: null });
        log.push(`annotated paper: condition ${c.id} on ${s.id} not located`);
        continue;
      }
      // after its host, the note names the cited result it is a condition of (never the host's own hypothesis)
      const said = after && !tags && !end ? { ...c, condition: `For ${refText(s.id)}: ${c.condition}` } : c;
      const r = pushEdit(place.file, place.at, 1, `${tagOf(s.id, "condition added")}\\${c.by === "owner" ? "vsConditionOwner" : "vsCondition"}{${conditionText(s.id, said)}}`);
      records.push({ node: s.id, file: place.file, line: lineOf(input.files[place.file]!, r.at), kind: "condition added", located_by: place.how, summary: `${c.id}: ${c.condition}`, extended: r.moved ? [r.moved] : [] });
    }
  }

  // --- symbol readings (the symbol referee's pins): once each, where the reader first meets the
  // symbol (user rule 2026-09-25) — its first occurrence in math in the flattened paper, or the
  // sentence the referee found introducing it when that comes first — unless the reading names a
  // context ("In …, …") whose symbols that place lacks and a later printed result states: then at that
  // result. After the environment holding the place, else at the end of its paragraph.
  const flatStarts = lineStarts(input.flatText);
  const flatMath = texRegions(input.flatText)
    .filter((r) => r.kind === "math" || r.kind === "display" || (r.kind === "environment" && MATH_ENV.test(/^\\begin\s*\{([^{}]*)\}/u.exec(input.flatText.slice(r.start, r.start + 40))?.[1]?.trim() ?? "")))
    .sort((x, y) => x.start - y.start);
  const squashTex = (t: string): string => t.replace(/\s+/gu, "").replace(/([_^])\{(\\?[A-Za-z0-9])\}/gu, "$1$2");
  const headOf = (name: string): string => squashTex(name.replace(/\(\\cdot\)$/u, ""));
  const symbolRe = (head: string): RegExp => new RegExp(`(?<![A-Za-z\\\\^_])(?<!\\\\[A-Za-z]+\\{)${head.replace(/[.*+?^${}()|[\]\\]/gu, "\\$&")}(?![A-Za-z${/\d$/u.test(head) ? "0-9" : ""}])`, "u");
  // The front matter (title, abstract: before the first sectioning command) introduces nothing.
  const bodyStart = /\\(?:sub)*section\*?\s*[[{]|\\chapter\*?\s*[[{]/u.exec(input.flatText)?.index ?? 0;
  /** The first flat line (1-based) where a symbol occurs inside math, past the front matter. */
  const firstMathLine = (name: string): number | null => {
    const head = headOf(name);
    if (!head) return null;
    const re = symbolRe(head);
    const r = flatMath.find((x) => x.start >= bodyStart && re.test(squashTex(input.flatText.slice(x.start, x.end))));
    return r ? lineOf(input.flatText, r.start) : null;
  };
  /** The flat line (1-based) of a source line. */
  const flatLineOf = (file: string, line: number): number | null => {
    const k = input.lineMap.findIndex((x) => x.file === file && x.line === line);
    return k >= 0 ? k + 1 : null;
  };
  /** The environment (statement or proof) holding a source line. */
  const envAtLine = (file: string, line: number): { env: TexEnv; proof: boolean } | null => {
    const e = envs.envs.find((x) => x.lines.file === file && line >= x.lines.from && line <= x.lines.to);
    if (e) return { env: e, proof: false };
    const q = envs.envs.find((x) => x.proofLines && x.proofLines.file === file && line >= x.proofLines.from && line <= x.proofLines.to);
    return q ? { env: q, proof: true } : null;
  };
  /** The symbols of a reading's context clause ("In <context>, … ;"), without the symbol itself. */
  const contextTokens = (reading: string, name: string): string[] => {
    const first = reading.split(";")[0]!;
    if (!/^\s*In\b/u.test(first)) return [];
    const toks = new Set<string>();
    for (const m of first.matchAll(/\\(?:alpha|beta|gamma|delta|varepsilon|epsilon|zeta|eta|vartheta|theta|iota|kappa|lambda|mu|nu|xi|pi|rho|sigma|tau|upsilon|varphi|phi|chi|psi|omega|Gamma|Delta|Theta|Lambda|Xi|Pi|Sigma|Phi|Psi|Omega)(?![A-Za-z])|\b[A-Z]{2,}(?=\()|\b[A-Za-z]_\{?[A-Za-z0-9]+\}?/gu)) toks.add(squashTex(m[0]));
    toks.delete(headOf(name));
    return [...toks];
  };
  for (const v of input.review?.symbols ?? []) {
    if (v.ambiguity !== "pinned" || !v.reading) continue;
    const node = `${SYMBOL_PIN_OF}${v.name}`;
    // The whole reading in one note: the general part, then each scoped clause led by its results.
    // A result a clause is tagged with, as the author finds it: a printed result by `refText`, a block
    // a repair split off by the result it was split from; an id that is no result any more, not at all.
    const tagName = (id: string): string | null => {
      if (transcribed.statements.some((x) => x.id === id)) return refText(id);
      const parent = input.core.statements.find((x) => x.id === id)?.split_from;
      return parent ? `the result split from ${refText(parent)}` : null;
    };
    const whole = fullReadingText(v.reading, tagName);
    const summary = `reading of ${v.name}: ${whole}`;
    const intro = v.introduced_at;
    const miss = (reason: string): void => {
      unlocated.push({ node, kind: "clarification (reading)", reason, placed: null });
      log.push(`annotated paper: reading of symbol ${v.name} not located (${reason})`);
    };
    // The place: the earlier of the first occurrence in math and the introducing sentence.
    const introFlat = intro?.file && intro.line && input.files[intro.file] !== undefined ? (intro.flat_line ?? flatLineOf(intro.file, intro.line)) : null;
    // A reading scoped to a context ("In Lemma 2, A is …") means the symbol THERE: its first
    // occurrence elsewhere may be another object of the same name.
    const scoped = /^\s*In\b/u.test(v.reading.reading);
    const firstFlat = scoped && introFlat !== null ? null : firstMathLine(v.name);
    let flatLine = introFlat !== null && (firstFlat === null || introFlat <= firstFlat) ? introFlat : firstFlat;
    let loc = flatLine !== null ? input.lineMap[flatLine - 1] ?? null : null;
    if (flatLine !== null && flatLine === introFlat && intro?.file && intro.line) loc = { file: intro.file, line: intro.line };
    if (!loc || input.files[loc.file] === undefined) {
      miss("no introducing sentence was located");
      continue;
    }
    if (flatLine !== introFlat) log.push(`annotated paper: the reading of symbol ${v.name} goes to its first occurrence (${loc.file}:${loc.line}), before the sentence found introducing it`);
    // A context the place lacks, stated by a later result: that result.
    const toks = contextTokens(v.reading.reading, v.name);
    let target = envAtLine(loc.file, loc.line);
    if (toks.length >= 2 && flatLine !== null) {
      const here = target ? `${target.env.body}\n${target.env.proof ?? ""}` : input.flatText.slice(flatStarts[Math.max(0, flatLine - 4)] ?? 0, flatStarts[flatLine + 3] ?? input.flatText.length);
      const hereSq = squashTex(here);
      if (toks.every((t) => !symbolRe(t).test(hereSq))) {
        const later = envs.envs.find((e) => {
          const fl = flatLineOf(e.lines.file, e.lines.from);
          const bodySq = squashTex(e.body);
          return fl !== null && fl > flatLine! && /^(?:theorem|lemma|proposition|corollary|definition|assumption)$/u.test(e.kind) && symbolRe(headOf(v.name)).test(bodySq) && toks.every((t) => symbolRe(t).test(bodySq));
        });
        if (later) {
          target = { env: later, proof: false };
          loc = { file: later.lines.file, line: later.lines.from };
          flatLine = flatLineOf(later.lines.file, later.lines.from);
          log.push(`annotated paper: the reading of symbol ${v.name} names a later result's context; placed at ${later.id}`);
        }
      }
    }
    const note = `\\vsReadingSymbol{${label(node, v.name)}}{${safe(node, "symbol reading", whole, "symbol", v.name)}}`;
    const orig = input.files[loc.file]!;
    const tags = target && !target.proof ? envBounds(target.env) : null;
    if (tags) {
      const r = pushEdit(tags.file, tags.endEnd, 1, note);
      records.push({ node, file: tags.file, line: lineOf(input.files[tags.file]!, r.at), kind: "clarification (reading)", located_by: "after-env", summary, extended: [] });
      continue;
    }
    // Running text (or a proof): the first blank line after the line (the paragraph's end).
    const ls = lineStarts(orig);
    let k = loc.line;
    while (k < ls.length && orig.slice(ls[k]!, ls[k + 1] ?? orig.length).trim() !== "") k += 1;
    const offset = k < ls.length ? ls[k]! : orig.length;
    const r = pushEdit(loc.file, offset, 1, `\n${note}\n`);
    records.push({ node, file: loc.file, line: lineOf(orig, r.at), kind: "clarification (reading)", located_by: "paragraph-end", summary, extended: [] });
  }
  for (const f of afterReadings) f();
  return { edits, records, unlocated, log, defects, fragments: [...fragments.values()] };
}

/** Labels a TeX text references (`\ref`, `\cref{a,b}`, `\Cref`, `\autoref`, `\eqref`, …). Pure. */
function refLabels(tex: string): string[] {
  const out: string[] = [];
  for (const m of tex.matchAll(/\\(?:[cC]?ref|autoref|eqref|thmref|nameref|[cC]refrange)\*?\s*\{([^{}]*)\}/gu)) {
    for (const l of m[1]!.split(",").map((x) => x.trim()).filter(Boolean)) if (!out.includes(l)) out.push(l);
  }
  return out;
}

/** One argument of `^` or `_` in TeX: a group (one level of nesting), a macro with an optional group, or a character. */
const SCRIPT_ARG = String.raw`(\{(?:[^{}]|\{[^{}]*\})*\}|\\[A-Za-z]+(?:\{[^{}]*\})?|[^\\{])`;

/** Apply a file's edits: closes before insertions before opens at one offset, then in plan order. */
export function applyEdits(text: string, edits: readonly Edit[]): string {
  const sorted = [...edits].sort((a, b) => a.at - b.at || a.rank - b.rank || a.seq - b.seq);
  let out = "";
  let last = 0;
  for (const e of sorted) {
    out += text.slice(last, Math.max(last, e.at)) + e.text;
    last = Math.max(last, e.at + (e.del ?? 0));
  }
  return out + text.slice(last);
}

export { compileTex, compileGuarded, paperSideFailure, sourceFailureNote, ANNOTATED_COMPILE_RECORD, type CompileResult, type CompileTex } from "./annotated_compile.js";

// ---------------------------------------------------------------------------
// the stage's entry point
// ---------------------------------------------------------------------------

export interface AnnotatedPaperResult {
  dir: string;
  main: string;
  records: AnnotationRecord[];
  unlocated: UnlocatedRecord[];
  compile: CompileResult;
  files_changed: string[];
  /** Blocks that could not be set as TeX (`AnnotationPlan.defects`). */
  defects: RenderDefect[];
}

export function renderAnnotationsMd(slug: string, main: string, r: Omit<AnnotatedPaperResult, "dir" | "main">, preamble: string): string {
  const awaiting = new Set([...r.records, ...r.unlocated].filter((a) => a.kind === "awaiting decision").map((a) => a.node)).size;
  const L: string[] = [
    `# PaperFormalizer annotations — ${slug}`,
    "",
    `Annotated copy of \`source/\`; main file \`${main}\`. Red (\`\\vsOriginal\`, "Original:"): the paper's text that is wrong or ambiguous (kind \`not determined\`: it does not say enough to be checked, and nothing was shown false). ` +
      "Blue (`\\vsCorrected` / `\\vsClarified`: \"Corrected:\", \"Clarified statement:\"): the corrected text (a hypothesis a repair adds is written into it; the note says which). Proofs (kind `corrected proof`) are revised in place: each printed step a repair changes red (`\\vsStep`, \"Original:\") with its replacement right after (`\\vsCorrectedStep`, \"Corrected:\"); a repair without step edits (or a result whose proof was not located) gets one block per result (`\\vsProof`, \"Corrected proof (confirmed):\"; a pending one `\\vsProposedProof`) after the proof; when the paper prints none, right after the result, naming every lemma it uses and, by the paper's section numbers, where their corrections are marked; else right after the result, saying the proof could not be located. " +
      "Red struck through (`\\vsStruck`; `\\vsStruckRed`, red alone, where a line cannot cross the text), kind `no longer used`: an assumption or definition no result uses after the repairs, with a note naming the results that now state the conditions they use. " +
      "Orange (`\\vsNote`, \"PaperFormalizer: …\"): what is wrong, the proposed fix, and whether the fix weakens the result; `\\vsReading` (\"Clarification:\", kind `clarification (reading)`): a reading pinned for formalization; `\\vsReadingOwner` (\"Clarification (author):\"): the owner's reading of a finding the owner withdrew; `\\vsReadingSymbol` (\"Clarification (symbol …):\"): the reading of a symbol; `\\vsCondition` (\"Bookkeeping condition:\", kind `condition added`; the owner's `\\vsConditionOwner`, \"Bookkeeping condition:\"): a condition the verified statement carries beyond the printed text, at the end of each result carrying it; `\\vsDetail` (\"Proof detail:\"): the fixer's detail of a corrected proof step, for the referee and the Lean proof, beside the step it completes. " +
      "Awaiting your decision (a halt only): `\\vsProposed` (blue, \"Proposed repair (awaiting your decision):\"), `\\vsProposedStep` / `\\vsProposedProof` (blue, \"Corrected (for the proposed statement):\", \"Proof of the proposed statement:\" — the decision is on the statement, never on its proof), `\\vsRewind` (\"Proposed correction (awaiting your decision):\"), `\\vsCap` (\"Repair not settled (awaiting your decision):\"). " +
      "Lines are the ORIGINAL source's.",
    "",
    ...(awaiting > 0 ? [`**Awaiting your decision: ${awaiting} item(s)** (kind \`awaiting decision\` below).`, ""] : []),
    `Preamble: ${preamble}.`,
    "",
    `## Annotations (${r.records.length})`,
    "",
    "| # | node | file:line | kind | located by | note |",
    "|---|---|---|---|---|---|",
    ...r.records.map((a, i) => `| ${i + 1} | \`${a.node}\` | ${a.file}:${a.line} | ${a.kind} | ${a.located_by}${a.extended.length > 0 ? ` (widened: ${a.extended.join("; ")})` : ""} | ${plainLine(a.summary)} |`),
    "",
    `## Unlocated (${r.unlocated.length})`,
    "",
  ];
  if (r.unlocated.length === 0) L.push("Every finding was placed at its passage.");
  else {
    L.push("| node | kind | why | written as |", "|---|---|---|---|");
    for (const u of r.unlocated) L.push(`| \`${u.node}\` | ${u.kind} | ${plainLine(u.reason)} | ${u.placed ? `a note at the end of the environment, ${u.placed}` : "listed here only"} |`);
  }
  L.push("", "## Compile", "");
  const c = r.compile;
  const note = sourceFailureNote(c, "annotated");
  if (note) L.push(`Note: ${note}.`, "", "Log tail:", "", "```", c.log_tail.trimEnd(), "```");
  else if (c.status === "skipped") {
    L.push(`Not compiled: ${c.reason}.`);
    if (c.log_tail.trim()) L.push("", "Log tail of that compile:", "", "```", c.log_tail.trimEnd(), "```");
  }
  else if (c.status === "passed") L.push(`Compiled with ${c.tool}: \`${c.pdf}\`.`);
  else {
    L.push(`Compiling with ${c.tool} FAILED (${c.reason}); the annotated TeX is kept.${c.pdf ? ` A PDF was still written: \`${c.pdf}\`.` : ""}${c.source_failure ? ` The paper's own source does not compile here either (${c.source_failure.error}); the other errors are not the source's.` : ""}`, "", "Log tail:", "", "```", c.log_tail.trimEnd(), "```");
  }
  return `${L.join("\n")}\n`;
}


/** The paper's TeX sources under `src`, normalized, with each file's byte encoding. */
export async function readSourceTex(src: string, mainFile: string, envs: EnvsJson): Promise<{ files: Record<string, string>; enc: Record<string, BufferEncoding> }> {
  const texFiles = [...new Set([mainFile, ...envs.files.filter((f) => /\.tex$/i.test(f))])];
  const files: Record<string, string> = {};
  const enc: Record<string, BufferEncoding> = {};
  for (const f of texFiles) {
    const p = path.join(src, f);
    if (!existsSync(p)) continue;
    const t = await readPaperText(p);
    files[f] = t.text.replace(/\r\n?/g, "\n");
    enc[f] = t.enc;
  }
  return { files, enc };
}

/**
 * Build `runs/<slug>/annotated/`: a fresh copy of `source/`, annotated in place, with the colour
 * macros in the main file's preamble, `ANNOTATIONS.md`, and — when a compiler is on PATH — a PDF.
 * Re-running rebuilds the directory from scratch, so the same records give the same tree.
 */
export async function writeAnnotatedPaper(args: {
  runDir: string;
  slug: string;
  mainFile: string;
  input: Omit<AnnotationInput, "files">;
  compile?: CompileTex;
  /** Where the compile record lives (default `ANNOTATED_COMPILE_RECORD` under the run). */
  compileRecord?: string;
  log?: (msg: string) => void;
}): Promise<AnnotatedPaperResult> {
  const { runDir, slug, mainFile, input } = args;
  const log = args.log ?? (() => {});
  const src = path.join(runDir, "source");
  const dir = path.join(runDir, ANNOTATED_DIR);
  await rm(dir, { recursive: true, force: true });
  await mkdir(dir, { recursive: true });
  // a link in the source becomes the file itself: the annotated text written over it must never
  // reach the link's target (the source, or a file of the owner's)
  await cp(src, dir, { recursive: true, dereference: true });
  const { files, enc } = await readSourceTex(src, mainFile, input.envs);
  // The render check: every model-written fragment compiled against the paper's preamble (cached —
  // a fragment checked at its source is a cache hit); a failing one is planned again as verbatim.
  // The run read the paper with its authors' note macros read away: the plan is made on the source read
  // the same way (offsets kept), and written into the source as the author has it, wrappers and all.
  const notes = input.envs.note_macros ?? null;
  const read = notes ? Object.fromEntries(Object.entries(files).map(([f, t]) => [f, unwrapSource(t, notes, "blank")])) : files;
  let plan = planAnnotations({ ...input, files: read });
  const failing = await texVerdicts(plan.fragments, { runDir, mainFile, log });
  if (failing.size > 0) plan = planAnnotations({ ...input, files: read, texVerdicts: failing });
  for (const m of plan.log) log(m);
  const changed = new Set(Object.keys(plan.edits).filter((f) => plan.edits[f]!.length > 0));
  changed.add(mainFile);
  let preamble = "unchanged";
  for (const f of [...changed].sort()) {
    let text = notes ? applyEditsKeepingNotes(files[f] ?? "", plan.edits[f] ?? [], notes) : applyEdits(files[f] ?? "", plan.edits[f] ?? []);
    if (f === mainFile) {
      const cls = documentClassOf(text);
      const clsFile = cls ? path.join(src, `${cls}.cls`) : null;
      const clsText = clsFile && existsSync(clsFile) ? await readFile(clsFile, "latin1") : null;
      const inj = injectPreamble(text, loadsXcolor(preambleOf(text), clsText, cls));
      text = inj.tex;
      preamble = `${inj.addedXcolor ? "`\\usepackage{xcolor}` added after `\\documentclass`" : "xcolor already loaded (not added)"}; colour macros ${inj.addedBlock ? "defined before `\\begin{document}`" : "already present"}`;
    }
    await writeFile(path.join(dir, f), text, enc[f] ?? "utf8");
  }
  const recFile = args.compileRecord ?? path.join(runDir, ANNOTATED_COMPILE_RECORD);
  const compile = await compileGuarded({ recFile, dir, mainFile, compile: args.compile ?? compileTex, sourceDir: src, log });
  log(
    `annotated paper: ${plan.records.length} annotation(s), ${plan.unlocated.length} unlocated; compile ${compile.status}` +
      (compile.reason ? ` (${compile.reason})` : ""),
  );
  const result: AnnotatedPaperResult = { dir, main: mainFile, records: plan.records, unlocated: plan.unlocated, compile, files_changed: [...changed].sort(), defects: plan.defects };
  await writeFile(path.join(dir, ANNOTATIONS_MD), renderAnnotationsMd(slug, mainFile, result, preamble), "utf8");
  return result;
}
