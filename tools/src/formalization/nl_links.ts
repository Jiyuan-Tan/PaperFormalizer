// F5 paper ↔ Lean links, row by row — a CLOSED-WORLD assignment on the paper's TeX.
//
// Both sides are cut DETERMINISTICALLY before any model call: the paper statement into segments
// (sentences, clauses, list items, the conditions of a displayed formula; a cut never falls inside
// inline math), the Lean statement into the rows of its nested view (`lean_rows.ts`: one per
// binder, one per hypothesis a clause states for itself, one per clause, at every depth, a clause
// written `type_of% @name` as the rows of that theorem's statement). The model then answers a
// closed question by id — for every row, which segments state it, or "unstated"; which segments no
// row states — so it never quotes, paraphrases or cuts text. A second call audits the whole
// assignment. Totality is checked, and so is a blanket answer (many rows given one long list): a
// result that fails is asked once more on its own, told why.
//
// An assumption or a definition is linked the same way, to the rows of its Prop-valued declaration
// (`lean_rows.ts` `propDeclView`).
//
// Advisory: the links feed the report and the paper page; a failure is logged, never a block.

import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { MODEL_PLAN } from "../constants.js";
import type { PipelineContext, StateJson } from "../types.js";
import { artifactPaths, readPrompt, type StageDeps } from "../pipeline_support.js";
import { dispatchAgent, parseAgentJson } from "../framework/agent_dispatch.js";
import { graphPath, loadGraph } from "../graph/store.js";
import { mapLimit } from "./reviewer_verdicts.js";
import { fillTemplate } from "../shared/template.js";
import { completeView, leanScopes, leanStatementView, parseFileDecls, propDeclView, viewRows, type LeanRow, type LeanScopes } from "./lean_rows.js";
import { CLOSERS, OPENERS, squash, unwrapParens as unwrap } from "../presentation/lean_text.js";
import { DECL_NAME, normAwareDepths } from "../presentation/lean_statement.js";
import { extractFullDeclSource } from "../presentation/lean_extract.js";
import { leanNameLeaf } from "../presentation/lean_decl_name.js";

export { leanStatementView, viewRows, type LeanRow };

export const NL_LINKS_ARTIFACT = "nl_links.json";
/** Rows asked in one call (a result with more goes alone). */
const ROWS_PER_CALL = 120;
const CALL_CONCURRENCY = 3;
/** A blanket answer: one identical list of segments on more rows of a result than may share it —
 *  a list of two segments or more, `SHARED_LIST_ROWS` rows (rows that share a whole list were not
 *  linked one by one); a single segment, `sharedLimit` rows: at least `SHARED_ROWS_MIN` (a clause's
 *  quantifier, hypotheses and conclusion may share a phrase), a quarter of its rows, or twice its
 *  rows per segment (one sentence may declare many objects). */
const SHARED_LIST_ROWS = 3;
const SHARED_ROWS_MIN = 4;
/** Below this share of linked rows with a list of their own, the run's summary warns. */
const UNIQUE_SHARE_WARN = 0.5;

export interface NlSegment {
  id: string;
  /** The statement's text in [start, end). */
  text: string;
  start: number;
  end: number;
  /** A part of a displayed formula cut into several: the id of that display's first part. */
  display?: string;
}

// ── paper side ───────────────────────────────────────────────────────────────

const DISPLAY_ENVS = "align|equation|gather|multline|eqnarray|displaymath|flalign";
/** Displayed formulas. */
const DISPLAY_RE = new RegExp(String.raw`\\begin\{(${DISPLAY_ENVS})(\*?)\}[\s\S]*?\\end\{\1\2\}|\\\[[\s\S]*?\\\]|\$\$[\s\S]*?\$\$`, "g");
/** Inline math: never cut inside. */
// (`\x` is read as a pair, so `$\\$` — a formula of one line break — closes at its second `$`)
const INLINE_RE = /\\\([\s\S]*?\\\)|(?<!\\)\$(?:\\[\s\S]|[^$\\])+?\$/g;
/** The graph's trailing "[Hypotheses: …]" annotation is not paper text. */
const HYP_SUFFIX_RE = /\s*\[Hypotheses:[^\]]*\]\s*$/;
/** A relation: what makes a formula a condition of its own. */
const RELATION_RE = /=|<|>|\\(?:leq?|geq?|neq?|to|rightarrow|longrightarrow|in|notin|sim|simeq|lesssim|gtrsim|asymp|approx|perp|subset|subseteq|ll|gg|equiv|prec|succ|preceq|succeq|leqslant|geqslant|rightsquigarrow|leadsto)(?![A-Za-z])/;
/** A display part that only continues the one before: it opens with a relation or an operator. */
const CONTINUES_RE = /^[\s&]*(?:=|<|>|\+|-|\\(?:leq?|geq?|neq?|times|cdot|approx|sim|equiv|leqslant|geqslant|lesssim|gtrsim)(?![A-Za-z]))/;
/** List markup with nothing stated in it. */
const LIST_MARKUP_RE = /\\(?:begin|end)\{[^}]*\}(?:\[[^\]]*\])?|\\item\b(?:\[[^\]]*\])?/g;
const ROMAN = ["i", "ii", "iii", "iv", "v", "vi", "vii", "viii", "ix", "x"];
const ENUM_FAMILIES: ReadonlyArray<readonly string[]> = [[..."abcdefgh"], ROMAN, [..."123456789"]];
/** An inline enumeration marker: `(a)`, `(ii)`, `(2)`, bare or as inline math. */
const MARKER_RE = /\$\s*(?:\\left\s*)?\(\s*([a-z]{1,4}|\d)\s*(?:\\right\s*)?\)\s*\$|\(([a-z]{1,4}|\d)\)/g;

/** Text with no word and no math in it, only markup (`}`, `\emph{`). */
const bare = (shown: string): boolean => !/[\p{L}\p{N}$]|\\[[(]/u.test(shown.replace(/\\[A-Za-z]+\*?/g, ""));

/** Text shown for a segment: labels dropped, whitespace collapsed. */
export function segmentShown(text: string): string {
  return text.replace(/\\label\{[^}]*\}/g, "").replace(/\s+/g, " ").trim();
}

/**
 * Where the displayed formula `tex[a, b)` is cut when it holds several conditions: after each
 * top-level separator (`\quad`, `\qquad`, `\\`, a comma) with a relation on both sides — a part
 * that only continues the one before staying with it, and a list of subjects set off by a space or
 * a line break (`…,\qquad a, b \leq c`) going whole with the relation it opens. Offsets into `tex`. Pure.
 */
function displayCuts(tex: string, a: number, b: number): number[] {
  const open = /^(?:\\begin\{[^}]*\}|\\\[|\$\$)/.exec(tex.slice(a, b));
  const close = /(?:\\end\{[^}]*\}|\\\]|\$\$)\s*$/.exec(tex.slice(a, b));
  if (!open || !close) return [];
  const from = a + open[0].length, to = a + close.index;
  // the end of each run of top-level separators
  const ends: number[] = [];
  // whether the run holds more than commas
  const strong: boolean[] = [];
  let depth = 0, last = -1;
  for (let i = from; i < to; i++) {
    const rest = tex.slice(i, to);
    const word = /^\\(begin|end|left|right|qquad|quad)(?![A-Za-z])|^\\\\(?:\[[^\]]*\])?/.exec(rest);
    const sep = word ? word[1] === "quad" || word[1] === "qquad" || word[1] === undefined : rest[0] === ",";
    if (word && (word[1] === "begin" || word[1] === "left")) depth++;
    else if (word && (word[1] === "end" || word[1] === "right")) depth = Math.max(0, depth - 1);
    else if (!word && "([{".includes(rest[0])) depth++;
    else if (!word && ")]}".includes(rest[0])) depth = Math.max(0, depth - 1);
    else if (sep && depth === 0) {
      const end = i + (word ? word[0].length : 1);
      if (last >= 0 && /^[\s&]*$/.test(tex.slice(ends[last], i))) { ends[last] = end; strong[last] ||= !!word; }
      else { last = ends.push(end) - 1; strong.push(!!word); }
    }
    if (word) i += word[0].length - 1;
    else if (rest[0] === "\\") i++;
  }
  const cuts: number[] = [];
  // `held`: the separator before a list of subjects still waiting for its relation
  let start = from, held = -1;
  ends.forEach((end, k) => {
    const next = tex.slice(end, ends[k + 1] ?? to);
    if (!RELATION_RE.test(tex.slice(start, end))) return;
    if (!RELATION_RE.test(next)) {
      if (strong[k]) held = k + 1 < ends.length && !strong[k + 1] ? k : -1;
      return;
    }
    if (!CONTINUES_RE.test(next)) { start = held >= 0 ? ends[held] : end; cuts.push(start); }
    held = -1;
  });
  return cuts;
}

/** Where a run of inline enumeration markers (`(a) … (b) …`, `(i) … (ii) …`) starts each item. Pure. */
function markerCuts(tex: string, prose: (i: number) => boolean): number[] {
  const found: Array<{ at: number; label: string; lead: string }> = [];
  for (const m of tex.matchAll(MARKER_RE)) {
    if (!prose(m.index!) || /[\w}]$/.test(tex.slice(0, m.index!))) continue;
    found.push({ at: m.index!, label: m[1] ?? m[2], lead: tex.slice(0, m.index!).trimEnd() });
  }
  const cuts: number[] = [];
  for (const family of ENUM_FAMILIES) {
    // a number in running text is an equation's unless it opens a clause
    const opens = (f: (typeof found)[number]) => family !== ENUM_FAMILIES[2] || /(?:^|[:;,.]|\b(?:and|or))$/.test(f.lead);
    const run = found.reduce<number[]>((r, f) => (f.label === family[r.length] && opens(f) ? [...r, f.at] : r), []);
    if (run.length >= 2) cuts.push(...run);
  }
  return cuts;
}

/** Words written with a period that ends no sentence, whatever follows (`cf. Lemma 2`, `Eq. (3)`). */
const ABBREVIATION_RE = /(?<![A-Za-z])(?:cf|resp|vs|viz|approx|Figs?|Eqs?|Secs?|Thms?|Lem|Prop|Cor|Defs?|Rem|Ex|App|Ch|Refs?|Nos?|pp?)$/;

/**
 * Whether the period at `dot` of `tex`, with `next` the first character past the white space after
 * it, ends a sentence: not when what follows continues one (a lower-case word, a digit, a comma or
 * a closing bracket: `e.g. the`, `Fig. 3`), nor after a dotted abbreviation (`i.i.d.`, `a.s.`) or
 * a word of `ABBREVIATION_RE`. Pure.
 */
function endsSentence(tex: string, dot: number, next: number): boolean {
  if (/^[\p{Ll}\p{N},:)\]]/u.test(tex.slice(next, next + 2))) return false;
  const before = tex.slice(Math.max(0, dot - 12), dot);
  return !/(?<![A-Za-z])(?:[A-Za-z]\.)+[A-Za-z]$/.test(before) && !ABBREVIATION_RE.test(before);
}

/**
 * Cut a statement into segments that tile it in order. Prose is cut after a sentence end or
 * semicolon, at a blank line, after the comma before a clause word (if, then, where, and, that,
 * with, provided, whenever), at each `\item` and around a list environment, at each marker of an
 * inline enumeration, and before the `and` between two inline relations — never inside inline
 * math. A displayed formula is one segment, or one per condition it holds (`displayCuts`: their
 * `display` names the formula's first part). A prose piece of at most two words with no math, and
 * list markup stating nothing, join the next piece ("if" + its display; what closes a list, the
 * item before it). Pieces that are empty once labels are dropped are not segments. Pure.
 */
export function segmentStatement(raw: string): NlSegment[] {
  const tex = raw.replace(HYP_SUFFIX_RE, "");
  const protectedSpans: [number, number][] = [];
  const displays: [number, number][] = [];
  for (const m of tex.matchAll(DISPLAY_RE)) displays.push([m.index!, m.index! + m[0].length]);
  const displayAt = (i: number) => displays.find(([a, b]) => i >= a && i < b);
  // inline math is matched with the displays blanked: a `$$` pair read as two `$` would pair the
  // display's last `$` with the next inline one and swap math and prose up to the next display
  const masked = displays.reduce((t, [a, b]) => t.slice(0, a) + " ".repeat(b - a) + t.slice(b), tex);
  for (const m of masked.matchAll(INLINE_RE)) protectedSpans.push([m.index!, m.index! + m[0].length]);
  const isProtected = (i: number) => protectedSpans.some(([a, b]) => i > a && i < b);

  const cuts = new Set<number>([0, tex.length]);
  for (const [a, b] of displays) { cuts.add(a); cuts.add(b); for (const c of displayCuts(tex, a, b)) cuts.add(c); }
  const prose = (i: number) => !displayAt(i) && !isProtected(i);
  for (const m of tex.matchAll(/[.;](\s+)/g)) {
    const at = m.index! + m[0].length;
    if (prose(m.index!) && (m[0][0] === ";" || endsSentence(tex, m.index!, at))) cuts.add(at);
  }
  for (const m of tex.matchAll(/\n\s*\n/g)) if (prose(m.index!)) cuts.add(m.index! + m[0].length);
  for (const m of tex.matchAll(/,\s+(?=(?:if|then|where|and|with|provided|whenever|that(?!\s+is\b))\b)/g)) {
    if (prose(m.index!)) cuts.add(m.index! + m[0].length);
  }
  // a list: each item, and the text around the environment
  const lists = new Set<string>();
  for (const m of tex.matchAll(/\\begin\{([^}]*)\}(?=\s*(?:\[[^\]]*\]\s*)?\\item\b)/g)) if (prose(m.index!)) { lists.add(m[1]); cuts.add(m.index!); }
  for (const m of tex.matchAll(/\\end\{([^}]*)\}/g)) if (lists.has(m[1]) && prose(m.index!)) cuts.add(m.index! + m[0].length);
  for (const m of tex.matchAll(/\\item\b/g)) if (prose(m.index!)) cuts.add(m.index!);
  for (const c of markerCuts(tex, prose)) cuts.add(c);
  // `$a < b$ and $c < d$`: two conditions; `$a > 0$, $b < 1$, and $c = 2$`: a list of three or more,
  // one each (two joined by a comma alone may be one: "for some $\delta>0$, $E|X|<\infty$")
  const related = protectedSpans.filter(([a, b]) => RELATION_RE.test(tex.slice(a, b)));
  const gaps = related.map(([, end], k) => (related[k + 1] ? tex.slice(end, related[k + 1][0]) : ""));
  const and = (g: string) => /^,?\s+and\s+$/.test(g), comma = (g: string) => /^,\s*$/.test(g);
  for (let k = 0; k < gaps.length; k++) {
    let last = k;
    while (last < gaps.length && (and(gaps[last]) || comma(gaps[last]))) last++;
    // gaps k … last-1 join the relations k … last
    if (last - k >= 2) for (let j = k; j < last; j++) cuts.add(and(gaps[j]) ? related[j][1] + gaps[j].indexOf("and") : related[j + 1][0]);
    else if (last - k === 1 && and(gaps[k])) cuts.add(related[k][1] + gaps[k].indexOf("and"));
    k = Math.max(k, last - 1);
  }

  const bounds = [...cuts].sort((a, b) => a - b);
  const pieces: { start: number; end: number }[] = [];
  for (let k = 0; k + 1 < bounds.length; k++) if (bounds[k + 1] > bounds[k]) pieces.push({ start: bounds[k], end: bounds[k + 1] });

  const merged: { start: number; end: number }[] = [];
  let carry: number | null = null;
  for (const p of pieces) {
    const start: number = carry ?? p.start;
    const shown = segmentShown(tex.slice(p.start, p.end));
    const markup = shown !== "" && (shown.replace(LIST_MARKUP_RE, "").trim() === "" || (!displayAt(p.start) && bare(shown)));
    // what closes a list or a group (the `}` of an `\emph{…}` around the statement) stays with the piece before it
    if (markup && carry === null && merged.length > 0 && (shown.startsWith("\\end") || (!displayAt(p.start) && bare(shown)) || p === pieces[pieces.length - 1])) { merged[merged.length - 1].end = p.end; continue; }
    const short = !displayAt(p.start) && shown !== "" && !/[.;]$/.test(shown) && (markup || (!/[$\\]/.test(shown) && shown.split(/\s+/).length <= 2));
    if (short && p !== pieces[pieces.length - 1]) { carry = start; continue; }
    carry = null;
    merged.push({ start, end: p.end });
  }
  // a piece with nothing shown (a label, white space between a display and the next cut) is no
  // segment: it stays with the one before it, so the segments still tile what follows the first
  const kept: { start: number; end: number }[] = [];
  for (const p of merged) {
    if (segmentShown(tex.slice(p.start, p.end)) !== "") kept.push({ ...p });
    else if (kept.length) kept[kept.length - 1].end = p.end;
  }
  const out: NlSegment[] = kept.map((p, i) => ({ id: `s${i + 1}`, text: tex.slice(p.start, p.end), start: p.start, end: p.end }));
  for (const [a, b] of displays) {
    const parts = out.filter((s) => s.end > a && s.start < b);
    if (parts.length > 1) for (const s of parts) s.display = parts[0].id;
  }
  return out;
}

const DISPLAY_OPEN = new RegExp(String.raw`\\begin\{(?:${DISPLAY_ENVS})\*?\}|\\\[|\$\$`);
const DISPLAY_CLOSE = new RegExp(String.raw`\\end\{(?:${DISPLAY_ENVS})\*?\}|\\\]|\$\$`);

/**
 * A part of a displayed formula (`display`) as TeX that renders alone: its own formula in
 * `\[ … \]` — alignment tabs and the row break dropped — with the prose the segment carries around
 * the display. A part is otherwise a fragment no renderer reads as mathematics. Pure.
 */
export function partAlone(seg: Pick<NlSegment, "id" | "text" | "display">): string {
  const open = seg.id === seg.display ? DISPLAY_OPEN.exec(seg.text) : null;
  const from = open ? open.index + open[0].length : 0;
  const close = DISPLAY_CLOSE.exec(seg.text.slice(from));
  const to = close ? from + close.index : seg.text.length;
  const math = seg.text.slice(from, to).replace(/\\label\{[^}]*\}/g, "").replace(/(?<!\\)&/g, " ").replace(/\\\\(?:\[[^\]]*\])?\s*$/, "");
  return `${seg.text.slice(0, open?.index ?? 0)}\\[${math}\\]${close ? seg.text.slice(to + close[0].length) : ""}`;
}

/** The displayed formula its `parts` make up, with the prose they carry, unnumbered (a number is
 *  the page's own count). Pure. */
export function displayWhole(parts: ReadonlyArray<Pick<NlSegment, "text">>): string {
  return parts.map((p) => p.text).join("").replace(/\\(begin|end)\{(align|equation|gather|multline|eqnarray|flalign)\}/g, "\\$1{$2*}").replace(/\\label\{[^}]*\}/g, "");
}

// ── Lean side ────────────────────────────────────────────────────────────────

function stripComments(text: string): string {
  return text.replace(/\/-[\s\S]*?-\//g, (m) => m.replace(/[^\n]/g, " ")).replace(/--[^\n]*/g, (m) => " ".repeat(m.length));
}

const SCOPES = ["fun", "let", "letI", "have", "haveI"];

/** Where `text` is cut at its own level by `sep`: outside every bracket, up to anything that takes
 *  the rest of it (a quantifier, `fun` or `let`, whose body runs to the end); none at all when a looser
 *  connective stands at that level (`stop`), as Lean's precedence reads it. */
function topLevelCuts(text: string, sep: string, stop: string): number[] {
  const depths = normAwareDepths(text);
  const cuts: number[] = [];
  for (let i = 0; i < text.length; i++) {
    if (depths[i] !== 0) continue;
    const c = text[i];
    if (c === sep) cuts.push(i);
    else if (stop.includes(c)) return [];
    else if ("∀∃λ".includes(c) || (!/[\w.']/.test(text[i - 1] ?? "") && SCOPES.some((w) => text.startsWith(w, i) && !/[\w.']/.test(text[i + w.length] ?? "")))) break;
  }
  return cuts;
}

const piecesAt = (text: string, cuts: number[]): string[] =>
  [...cuts, text.length].map((end, k) => text.slice(k === 0 ? 0 : cuts[k - 1] + 1, end).trim()).filter(Boolean);

/** Top-level conjuncts of a conclusion: none where `→`, `↔` or `∨` (looser than `∧`) stands at its level. Pure. */
export function conjuncts(concl: string): string[] {
  return piecesAt(concl, topLevelCuts(concl, "∧", "→↔∨"));
}

/** The pieces of an implication chain, premises first: none where a `↔` (looser than `→`) stands at its level. Pure. */
export function chain(text: string): string[] {
  return piecesAt(text, topLevelCuts(text, "→", "↔"));
}

/**
 * The rows of one conclusion clause `id`: a clause that is an implication chain gives one `premise`
 * row per hypothesis (`<id>.h1`…) and its conclusion split into its conjuncts (`<id>`, or
 * `<id>.1`…); any other clause — a quantified one included, whose scope a split would break — is one
 * row. Pure.
 */
function clauseRows(id: string, clause: string): LeanRow[] {
  const body = unwrap(clause);
  const parts = /^[∀∃λ]|^fun\b/.test(body) ? [body] : chain(body);
  if (parts.length < 2) return [{ id, kind: "conclusion", names: "", lean: clause }];
  const concl = conjuncts(unwrap(parts.at(-1)!));
  return [
    ...parts.slice(0, -1).map((p, j): LeanRow => ({ id: `${id}.h${j + 1}`, kind: "premise", names: "", lean: p })),
    ...concl.map((c, j): LeanRow => ({ id: concl.length === 1 ? id : `${id}.${j + 1}`, kind: "conclusion", names: "", lean: c })),
  ];
}

/**
 * The flat cut, kept for a statement the nested view does not structure and for links written
 * before the view (their ids): one row per binder group, then the top-level conjuncts of the
 * conclusion (`⊢`, or `⊢1`…`⊢k`), each with the hypotheses it states for itself as rows of their
 * own (`clauseRows`) — or, `whole`, each clause one row (the cut of the first links). Null when the
 * shape is not recognised. Pure.
 */
export function flatLeanRows(source: string, clauses: "split" | "whole" = "split"): LeanRow[] | null {
  const s = stripComments(source);
  const m = s.match(new RegExp(String.raw`\b(?:theorem|lemma)\s+${DECL_NAME}(?:\s*\.\{[^}]*\})?`));
  if (!m || m.index === undefined) return null;
  let i = m.index + m[0].length;
  const rows: LeanRow[] = [];
  let inst = 0;
  const skip = () => { while (i < s.length && /\s/.test(s[i])) i++; };
  skip();
  while (i < s.length && OPENERS.includes(s[i])) {
    const open = s[i];
    let depth = 0, j = i;
    for (; j < s.length; j++) {
      if (OPENERS.includes(s[j])) depth++;
      else if (CLOSERS.includes(s[j]) && --depth === 0) break;
    }
    if (j >= s.length) return null;
    const inner = s.slice(i + 1, j).trim();
    let d = 0, colon = -1;
    for (let k = 0; k < inner.length; k++) {
      const c = inner[k];
      if (OPENERS.includes(c)) d++;
      else if (CLOSERS.includes(c)) d--;
      else if (c === ":" && d === 0 && inner[k + 1] !== "=") { colon = k; break; }
    }
    if (open === "[") rows.push({ id: `inst${++inst}`, kind: "instance", names: "", lean: inner.replace(/\s+/g, " ") });
    else if (colon > 0) {
      const names = inner.slice(0, colon).trim().replace(/\s+/g, " ");
      rows.push({ id: names, kind: "binder", names, lean: inner.slice(colon + 1).replace(/\s+/g, " ").trim() });
    }
    i = j + 1;
    skip();
  }
  if (s[i] !== ":") return null;
  // The conclusion runs to the top-level `:=` that opens the proof — not the `:=` of a `let`,
  // `have`, `letI` or `haveI` inside it.
  let depth = 0, end = s.length, lets = 0;
  for (let k = i + 1; k < s.length; k++) {
    const c = s[k];
    if (OPENERS.includes(c)) depth++;
    else if (CLOSERS.includes(c)) depth--;
    else if (depth === 0 && /^(?:let|have|letI|haveI)\b/.test(s.slice(k)) && !/[\w.']/.test(s[k - 1] ?? "")) lets++;
    else if (depth === 0 && c === ":" && s[k + 1] === "=") { if (lets > 0) lets--; else { end = k; break; } }
  }
  const parts = conjuncts(s.slice(i + 1, end).replace(/\s+/g, " ").trim());
  parts.forEach((p, k) => { const id = parts.length === 1 ? "⊢" : `⊢${k + 1}`; rows.push(...(clauses === "split" ? clauseRows(id, p) : [{ id, kind: "conclusion" as const, names: "", lean: p }])); });
  return rows;
}

/** A stored link row, as `nl_links.json` keeps it (only what is needed to place it). */
export interface StoredRow { id: string; names?: string; lean: string; segments?: string[]; unstated?: boolean; coarse?: boolean }

/**
 * Whether links written before the key (`stored`: rows of the flat cut, as it cuts clauses now or
 * as the first links did, each clause whole) are this statement's: its flat cut now is theirs row for row — the same ids (which carry where each row stood: a conjunct,
 * a premise of one, a binder) and the same text — so no bracket moved, no connective changed and
 * nothing was added or dropped (`same`); or theirs is a cut of the statement cut short — their rows
 * are the first rows of its cut now (`truncated`: an older extractor stopped early); else `changed`.
 * The flat cut does not record a binder's bracket, so `{x : T}` made `(x : T)` stays `same`: what
 * each row states is unchanged. Pure.
 */
export function legacyMatch(view: { statement?: string }, stored: StoredRow[]): "same" | "truncated" | "changed" {
  if (!view.statement) return "changed";
  const cuts = (["split", "whole"] as const).map((c) => matchCut(flatLeanRows(view.statement!, c), stored));
  return cuts.includes("same") ? "same" : cuts.includes("truncated") ? "truncated" : "changed";
}

/** `legacyMatch` against one flat cut (`now`): its clauses cut into their premises, or each whole. */
function matchCut(now: ReturnType<typeof flatLeanRows>, stored: StoredRow[]): "same" | "truncated" | "changed" {
  if (!now) return "changed";
  const eq = (k: number) => now[k] !== undefined && now[k].id === stored[k].id && squash(now[k].lean) === squash(stored[k].lean) && squash(now[k].names) === squash(stored[k].names ?? "");
  if (now.length === stored.length && stored.every((_, k) => eq(k))) return "same";
  // the last stored row may be the one cut short
  return stored.length > 0 && stored.length <= now.length && stored.slice(0, -1).every((_, k) => eq(k)) && squash(now[stored.length - 1].lean).startsWith(squash(stored.at(-1)!.lean)) && (stored.length < now.length || !eq(stored.length - 1)) ? "truncated" : "changed";
}

/**
 * The source text of the theorem `decl` in `fileText` (`extractFullDeclSource`, the one extractor
 * the page and the link step share): the declaration of that name at `line` when given, else the
 * one whose namespace makes up `decl`, else the first of that leaf name. Null when there is none.
 */
export function declSource(fileText: string, decl: string, line?: number): string | null {
  const leaf = leanNameLeaf(decl);
  const named = parseFileDecls(fileText).decls.filter((d) => (d.kind === "theorem" || d.kind === "lemma") && leanNameLeaf(d.name) === leaf);
  const full = (d: (typeof named)[number]) => (d.ns ? `${d.ns}.${d.name}` : d.name);
  const at = named.find((d) => d.line === line) ?? named.find((d) => decl === full(d) || decl.endsWith(`.${full(d)}`)) ?? named[0];
  if (!at) return null;
  try { return extractFullDeclSource(fileText, at.name, at.line); } catch { return null; }
}

// ── the closed question ──────────────────────────────────────────────────────

export interface LinkItem {
  obj_id: string;
  node: string;
  decl: string;
  /** What the rows were cut from (`StatementView.key`): the links are that statement's only. */
  key: string;
  segments: NlSegment[];
  rows: LeanRow[];
  /** An assumption or a definition: the rows are those of its Prop-valued declaration (`propDeclView`). */
  declared?: true;
}

export interface RowLink { row: string; segments: string[]; unstated: boolean }
export interface ItemLinks { obj_id: string; rows: RowLink[]; uncovered: string[] }

export const NL_LINKS_SCHEMA: Record<string, unknown> = {
  type: "object", additionalProperties: false, required: ["results", "changes"],
  properties: {
    results: { type: "array", items: {
      type: "object", additionalProperties: false, required: ["obj_id", "rows", "uncovered"],
      properties: {
        obj_id: { type: "string" },
        rows: { type: "array", items: {
          type: "object", additionalProperties: false, required: ["row", "segments", "unstated"],
          properties: { row: { type: "string" }, segments: { type: "array", items: { type: "string" } }, unstated: { type: "boolean" } },
        } },
        uncovered: { type: "array", items: { type: "string" } },
      },
    } },
    changes: { type: "array", items: { type: "string" } },
  },
};

/** The rows the model must answer (instance binders are Lean-only by construction). */
const askedRows = (it: LinkItem) => it.rows.filter((r) => r.kind !== "instance");

/**
 * The rows of a statement as F5 asks them and the page draws them, with the key they are linked
 * under: the nested view's — completed (`completeView`: the section variables it takes, a clause
 * written `type_of% @name` opened into that theorem's rows) when `at` says where the statement
 * stands — or the flat cut when the view cannot structure it. Null
 * when the shape is not recognised.
 */
export async function statementRows(source: string, at?: { file: string; decl: string; lean: LeanScopes; line?: number }): Promise<{ rows: LeanRow[]; key: string } | null> {
  const view = leanStatementView(source);
  if (!view) {
    const rows = flatLeanRows(source);
    return rows && { rows, key: createHash("sha1").update(rows.map((r) => `${r.id}:${squash(r.lean)}`).join("\n")).digest("hex") };
  }
  if (at) await completeView(view, at.file, at.decl, at.lean, new Set(), at.line);
  return { rows: viewRows(view), key: view.key };
}

/** The prompt block for a batch: each result's segments and rows, by id. Pure. */
export function itemsBlock(items: LinkItem[]): string {
  return items.map((it) => [
    `## ${it.obj_id} (${it.node}) — Lean \`${it.decl}\``,
    "Paper segments:",
    ...it.segments.map((s) => `  ${s.id}: ${segmentShown(s.text)}`),
    "Lean rows:",
    ...askedRows(it).map((r) => `  ${r.id}: ${r.kind === "binder" || r.kind === "instance" ? `${r.names} : ${r.lean}` : r.lean}`),
  ].join("\n")).join("\n\n");
}

/** How many rows of a result of `asked` rows and `segments` segments may share one list of `list`
 *  segments (one, unless given). Pure. */
export function sharedLimit(asked: number, segments: number, list = 1): number {
  return list > 1 ? SHARED_LIST_ROWS : Math.max(SHARED_ROWS_MIN, Math.ceil(asked / 4), Math.ceil((2 * asked) / Math.max(1, segments)));
}

/** The rows of one result that share a blanket list: more rows given one identical list of
 *  segments than `sharedLimit` allows a list of that length. Pure. */
export function sharedRows(rows: readonly RowLink[], asked: number, segments: number): string[] {
  const byList = new Map<string, { ids: string[]; list: number }>();
  for (const r of rows) {
    if (r.segments.length === 0) continue;
    const list = [...r.segments].sort();
    const k = list.join(" ");
    (byList.get(k) ?? byList.set(k, { ids: [], list: list.length }).get(k)!).ids.push(r.row);
  }
  return [...byList.values()].filter((g) => g.ids.length > sharedLimit(asked, segments, g.list)).flatMap((g) => g.ids);
}

/**
 * Check a reply against the closed world: every asked row of every item answered exactly once,
 * only known segment ids, `unstated` exactly when no segment is given, no blanket list
 * (`sharedRows`). Returns the items that pass and one problem line per item that does not.
 * `lenient` (the second answer for a result): what is sound is kept — a row answered wrongly or not
 * at all is left out (it stays unlinked), unknown ids are dropped, a blanket list stands and is
 * marked when stored — and the item passes when any row is answered. Pure.
 */
export function checkReply(items: LinkItem[], reply: unknown, lenient = false): { ok: Map<string, ItemLinks>; problems: string[] } {
  const ok = new Map<string, ItemLinks>();
  const problems: string[] = [];
  const results = (reply as { results?: unknown })?.results;
  const byId = new Map<string, ItemLinks>();
  if (Array.isArray(results)) for (const r of results as ItemLinks[]) if (r && typeof r.obj_id === "string") byId.set(r.obj_id, r);
  for (const it of items) {
    const r = byId.get(it.obj_id);
    if (!r || !Array.isArray(r.rows) || !Array.isArray(r.uncovered)) { problems.push(`${it.obj_id}: no answer`); continue; }
    const segIds = new Set(it.segments.map((s) => s.id));
    const want = askedRows(it).map((x) => x.id);
    const seen = new Map<string, RowLink>();
    const bad: string[] = [];
    for (const row of r.rows) {
      const segments = Array.isArray(row?.segments) ? row.segments : [];
      if (!want.includes(row?.row)) { bad.push(`unknown row ${row?.row}`); continue; }
      if (seen.has(row.row)) { bad.push(`row ${row.row} answered twice`); continue; }
      const unknown = segments.filter((x) => !segIds.has(x));
      if (unknown.length) bad.push(`row ${row.row}: unknown segment ${unknown.join(", ")}`);
      const contradicts = row.unstated === segments.length > 0;
      if (contradicts) bad.push(`row ${row.row}: unstated must hold exactly when no segment is given`);
      const known = segments.filter((x) => segIds.has(x));
      // lenient: a row whose answer says nothing sound is left unanswered
      if (!lenient || (!contradicts && (known.length > 0 || unknown.length === 0))) seen.set(row.row, { row: row.row, segments: known, unstated: known.length === 0 });
    }
    const missing = want.filter((x) => !seen.has(x));
    if (missing.length) bad.push(`rows not answered: ${missing.join(", ")}`);
    const badUncovered = r.uncovered.filter((x) => !segIds.has(x));
    if (badUncovered.length) bad.push(`unknown uncovered segment ${badUncovered.join(", ")}`);
    const shared = sharedRows([...seen.values()], want.length, it.segments.length);
    if (shared.length) bad.push(`rows ${shared.join(", ")} (${shared.length} of ${want.length}) carry one identical list of segments: give each row the smallest set of segments that states it`);
    if (bad.length) problems.push(`${it.obj_id}: ${bad.join("; ")}`);
    if (bad.length === 0 || (lenient && seen.size > 0)) ok.set(it.obj_id, { obj_id: it.obj_id, rows: want.filter((x) => seen.has(x)).map((x) => seen.get(x)!), uncovered: [...new Set(r.uncovered.filter((x) => segIds.has(x)))] });
  }
  return { ok, problems };
}

/** What F5 measures of one result's links. `unique`: the share of linked rows whose segment list no
 *  other row of the result has; `shared`: rows under a blanket list (`sharedRows`). */
export interface LinkMetrics { asked: number; linked: number; unstated: number; unanswered: number; unique: number; max_segments: number; shared: number }

export function linkMetrics(item: LinkItem, links: ItemLinks): LinkMetrics {
  const linked = links.rows.filter((r) => r.segments.length > 0);
  const lists = new Map<string, number>();
  for (const r of linked) { const k = [...r.segments].sort().join(" "); lists.set(k, (lists.get(k) ?? 0) + 1); }
  const asked = askedRows(item).length;
  return {
    asked, linked: linked.length, unstated: links.rows.length - linked.length, unanswered: asked - links.rows.length,
    unique: linked.length ? Math.round((100 * linked.filter((r) => lists.get([...r.segments].sort().join(" ")) === 1).length) / linked.length) / 100 : 1,
    max_segments: Math.max(0, ...linked.map((r) => r.segments.length)),
    shared: sharedRows(links.rows, asked, item.segments.length).length,
  };
}

/** Results in calls of at most `budget` asked rows each, in order; a result over it goes alone. Pure. */
export function batchByRows(items: LinkItem[], budget = ROWS_PER_CALL): LinkItem[][] {
  const batches: LinkItem[][] = [];
  let rows = 0;
  for (const it of items) {
    const n = askedRows(it).length;
    if (batches.length === 0 || rows + n > budget) { batches.push([]); rows = 0; }
    batches.at(-1)!.push(it);
    rows += n;
  }
  return batches;
}

// ── F5 entry ─────────────────────────────────────────────────────────────────

const RESULT_KINDS = new Set(["theorem", "proposition", "lemma", "corollary"]);
const DECLARED_KINDS = new Set(["assumption", "definition"]);

/** The paper's results with a Lean theorem to link (from-note graph nodes with a statement and a Lean
 *  decl), and its assumptions and definitions whose Lean is a Prop-valued declaration with rows — one
 *  that has none (a data-valued definition) is not linked, and not reported. */
export async function collectItems(ctx: PipelineContext, state: StateJson): Promise<{ items: LinkItem[]; skipped: Array<{ node: string; label: string }> }> {
  const paths = artifactPaths(ctx, state);
  const graph = await loadGraph(graphPath(paths.formalizationDir));
  const lean = leanScopes({ toolkitRoot: ctx.repoRoot, leanDir: paths.leanDir, read: (abs) => readFile(abs, "utf8").catch(() => null) });
  const items: LinkItem[] = [];
  const skipped: Array<{ node: string; label: string }> = [];
  for (const n of graph.nodes) {
    const statement = n.nl?.statement ?? "";
    const decl = n.lean?.decl_name;
    const file = n.lean?.file;
    // The paper's own results (from-note), not the helper lemmas the formalization introduced.
    const declared = DECLARED_KINDS.has(n.kind);
    if (n.provenance !== "from-note" || !(declared || RESULT_KINDS.has(n.kind)) || !statement.trim() || !decl || !file) continue;
    const segments = segmentStatement(statement);
    if (declared) {
      // the source the page reads (`leanDefs`), cut as the page cuts it
      const site = await lean.siteOf(file, decl);
      const view = site ? propDeclView((await lean.sourceOf(site))?.source ?? "")?.view : null;
      if (view && segments.length > 0) items.push({ obj_id: n.obj_id ?? n.id, node: n.id, decl, key: view.key, segments, rows: viewRows(view), declared: true });
      continue;
    }
    const abs = path.join(paths.leanDir, file);
    const src = existsSync(abs) ? declSource(await readFile(abs, "utf8"), decl) : null;
    const cut = src ? await statementRows(src, { file, decl, lean }) : null;
    if (!cut || segments.length === 0) { skipped.push({ node: n.id, label: `${n.obj_id ?? n.id} (${decl})` }); continue; }
    items.push({ obj_id: n.obj_id ?? n.id, node: n.id, decl, key: cut.key, segments, rows: cut.rows });
  }
  return { items, skipped };
}

/** What the model is told when a result is asked again. */
const retryNote = (problem: string): string => `\n\nYour previous answer for this result was not accepted — ${problem}. Answer it again in full.`;

/**
 * The links of `items`, asked in calls of at most `ROWS_PER_CALL` rows: each call's results are
 * checked (`checkReply`), a result that fails is asked once more on its own with the reason
 * (leniently checked), and what passed is audited by a second call (a verify reply that breaks the
 * closed world keeps the assignment it audited). `ask` sends one prompt and returns the reply; a
 * call that throws is a call with no answer (its results asked again alone, as for any other), so
 * one failed call never loses the links of the others. `prior`: the links on file for a result whose
 * statement and Lean stand as they were linked — such a result is not assigned again: its links go
 * to the audit as the proposal, which revises them (links that no longer pass `checkReply` are no
 * prior).
 */
export async function linkItems(items: LinkItem[], tpl: { assign: string; verify: string }, send: (label: string, prompt: string) => Promise<unknown>, prior: ReadonlyMap<string, ItemLinks> = new Map()): Promise<{ linked: Map<string, ItemLinks>; problems: string[]; changes: string[]; revised: string[]; audited: Set<string> }> {
  const batches = batchByRows(items);
  const problems: string[] = [];
  const changes: string[] = [];
  const linked = new Map<string, ItemLinks>();
  const revised: string[] = [];
  // the results whose links the audit returned whole: only those are settled under their basis
  const audited = new Set<string>();
  const ask = async (label: string, prompt: string): Promise<unknown> => {
    try { return await send(label, prompt); } catch (e) {
      problems.push(`${label}: the call failed (${String((e as Error)?.message ?? e).split("\n")[0]!.slice(0, 200)})`);
      return null;
    }
  };
  const assign = (batch: LinkItem[]) => fillTemplate(tpl.assign, { items: itemsBlock(batch) });
  await mapLimit(batches, CALL_CONCURRENCY, async (batch, b) => {
    const at = `${b + 1}/${batches.length}`;
    const onFile = checkReply(batch.filter((it) => prior.has(it.obj_id)), { results: batch.map((it) => prior.get(it.obj_id)).filter(Boolean) }).ok;
    const toAssign = batch.filter((it) => !onFile.has(it.obj_id));
    const assigned = toAssign.length ? checkReply(toAssign, await ask(`F5 nl-links assign ${at}`, assign(toAssign))) : { ok: new Map<string, ItemLinks>(), problems: [] };
    for (const p of assigned.problems) {
      const it = toAssign.find((x) => p.startsWith(`${x.obj_id}: `))!;
      const again = checkReply([it], await ask(`F5 nl-links assign ${at} again ${it.obj_id}`, assign([it]) + retryNote(p.slice(it.obj_id.length + 2))), true);
      problems.push(`${p} (asked again: ${again.ok.size ? "answered" : "not answered"}${again.problems.length ? `; ${again.problems[0].slice(it.obj_id.length + 2)}` : ""})`);
      if (again.ok.size) assigned.ok.set(it.obj_id, again.ok.get(it.obj_id)!);
    }
    for (const [id, l] of onFile) { assigned.ok.set(id, l); revised.push(id); }
    const done = batch.filter((it) => assigned.ok.has(it.obj_id));
    if (done.length === 0) return;
    const proposal = JSON.stringify({ results: done.map((it) => assigned.ok.get(it.obj_id)) }, null, 1);
    const reply = await ask(`F5 nl-links verify ${at}`, fillTemplate(tpl.verify, { items: itemsBlock(done), assignment: proposal }));
    const verified = checkReply(done, reply);
    for (const it of done) {
      linked.set(it.obj_id, verified.ok.get(it.obj_id) ?? assigned.ok.get(it.obj_id)!);
      if (verified.ok.has(it.obj_id)) audited.add(it.obj_id);
    }
    const said = (reply as { changes?: unknown })?.changes;
    if (Array.isArray(said)) changes.push(...said.filter((c): c is string => typeof c === "string"));
    problems.push(...verified.problems.map((p) => `verify ${p} (assignment kept)`));
  });
  return { linked, problems, changes, revised, audited };
}

/** One result as `nl_links.json` stores it. `unanswered`: no call answered it (the rows were asked,
 *  none was linked); a re-link (`theoremchecker relink`) asks it again. */
export interface StoredResult {
  obj_id: string; node: string; decl: string; key: string;
  segments: NlSegment[];
  rows: Array<LeanRow & { segments: string[]; unstated: boolean; coarse?: true }>;
  uncovered: string[];
  metrics: LinkMetrics;
  unanswered?: true;
  /** What the links were made from (`linkBasis`), once the audit returned them whole: a re-link under the
   *  same basis keeps them as they are. */
  basis?: string;
}

/** What a result's links depend on: its Lean cut, its segments and the two prompts. Pure. */
export const linkBasis = (it: LinkItem, tpl: { assign: string; verify: string }): string =>
  createHash("sha256").update(JSON.stringify([it.key, it.segments.map((x) => x.text), tpl.assign, tpl.verify])).digest("hex").slice(0, 16);

/** A result's links as stored: every row of the statement, a row under a blanket list marked
 *  `coarse`; with no links, every row unanswered. Pure. */
export function storedResult(it: LinkItem, l: ItemLinks | undefined): StoredResult {
  const links = l ?? { obj_id: it.obj_id, rows: [], uncovered: [] };
  const byRow = new Map(links.rows.map((r) => [r.row, r]));
  const shared = new Set(sharedRows(links.rows, askedRows(it).length, it.segments.length));
  return {
    obj_id: it.obj_id, node: it.node, decl: it.decl, key: it.key,
    segments: it.segments,
    rows: it.rows.map((r) => ({
      ...r, segments: byRow.get(r.id)?.segments ?? [],
      // an instance binder is Lean-only; a row left unanswered is neither stated nor unstated
      unstated: r.kind === "instance" || (byRow.get(r.id)?.unstated ?? false),
      ...(shared.has(r.id) ? { coarse: true as const } : {}),
    })),
    uncovered: links.uncovered,
    metrics: linkMetrics(it, links),
    ...(l ? {} : { unanswered: true as const }),
  };
}

/** The links on file for `it`, when they were written for the statement and the Lean it has now
 *  (same key, same segments) and some call answered it; else none. Pure. */
export function priorLinks(it: LinkItem, stored: StoredResult | undefined): ItemLinks | null {
  if (!stored || stored.unanswered || stored.key !== it.key) return null;
  if (stored.segments.length !== it.segments.length || stored.segments.some((x, i) => x.id !== it.segments[i]!.id || x.text !== it.segments[i]!.text)) return null;
  const byId = new Map(stored.rows.map((r) => [r.id, r]));
  return { obj_id: it.obj_id, rows: askedRows(it).flatMap((r) => { const x = byId.get(r.id); return x ? [{ row: r.id, segments: x.segments, unstated: x.unstated }] : []; }), uncovered: stored.uncovered };
}

/**
 * Link every paper result to its Lean theorem row by row and write `<run>/nl_links.json`: per
 * result its segments, its rows with their links, the key of the statement they were cut from and
 * what was measured (`LinkMetrics`); for the run a summary with its warnings. The paper's assumptions
 * and definitions are linked the same way to the rows of their Prop-valued declaration, stored among
 * the results, asked in calls of their own (the prompts with `stage5_nl_links_declared.txt`). `only` (node ids):
 * link those results alone, on the run's current Lean and paper, and keep what is stored for the
 * others. A result whose links on file were made from what it is linked from now (`linkBasis`) keeps
 * them without a call; one whose links still fit its statement and Lean is revised from them
 * (`priorLinks`), not linked from nothing; `fresh` links every result from nothing, as `only` does those it names. Advisory:
 * returns a one-line summary; the file is written whatever the calls do.
 */
export async function emitNlLinks(args: { ctx: PipelineContext; state: StateJson; deps: StageDeps; only?: ReadonlySet<string>; fresh?: boolean }): Promise<string> {
  const paths = artifactPaths(args.ctx, args.state);
  const file = path.join(paths.formalizationDir, NL_LINKS_ARTIFACT);
  const collected = await collectItems(args.ctx, args.state);
  const items = args.only ? collected.items.filter((it) => args.only!.has(it.node)) : collected.items;
  const skipped = args.only ? collected.skipped.filter((s) => args.only!.has(s.node)) : collected.skipped;
  if (items.length === 0) return args.only ? `no result of ${[...args.only].join(", ")} with a Lean theorem to link` : "no paper result with a Lean theorem to link";
  const [assign, verify, declaredNote] = await Promise.all([
    readPrompt(args.ctx, "stage5_nl_links.txt"),
    readPrompt(args.ctx, "stage5_nl_links_verify.txt"),
    items.some((it) => it.declared) ? readPrompt(args.ctx, "stage5_nl_links_declared.txt") : "",
  ]);
  // an assumption's or a definition's prompts: the results' with a note before the items, so the
  // results' own (and the basis of their links) stand as they were
  const noted = (t: string) => t.replace("{{items}}", () => `${declaredNote.trim()}\n\n{{items}}`);
  const tplOf = (it: LinkItem) => (it.declared ? { assign: noted(assign), verify: noted(verify) } : { assign, verify });
  const ask = async (label: string, prompt: string): Promise<unknown> => {
    const out = await dispatchAgent({
      ctx: args.ctx, deps: args.deps, stage: "5", label, prompt,
      promptSources: ["stage5_nl_links.txt", "stage5_nl_links_verify.txt", "stage5_nl_links_declared.txt", "graph.json", "Lean sources"],
      model: MODEL_PLAN.stage5.model, reasoningEffort: "high",
      sandboxMode: "read-only", leanLsp: false, outputSchema: NL_LINKS_SCHEMA,
    });
    return parseAgentJson(out.stdout).json ?? null;
  };
  const onFile = existsSync(file) ? (JSON.parse(await readFile(file, "utf8").catch(() => "{}")) as { results?: StoredResult[]; unlinked?: string[] }) : null;
  const prior = new Map<string, ItemLinks>();
  const kept = new Map<string, StoredResult>();
  // results named by `only` are asked for: linked from nothing, like every result under `fresh`
  if (!args.fresh && !args.only) for (const it of items) {
    const stored = onFile?.results?.find((r) => r.node === it.node), l = priorLinks(it, stored);
    if (l && stored!.basis === linkBasis(it, tplOf(it))) kept.set(it.obj_id, stored!);
    else if (l) prior.set(it.obj_id, l);
  }
  const linked = new Map<string, ItemLinks>(), audited = new Set<string>();
  const problems: string[] = [], changes: string[] = [], revised: string[] = [];
  // the results, then the assumptions and definitions under their own prompts
  for (const declared of [false, true]) {
    const todo = items.filter((it) => !kept.has(it.obj_id) && Boolean(it.declared) === declared);
    if (todo.length === 0) continue;
    try {
      const run = await linkItems(todo, tplOf(todo[0]!), declared ? (label, prompt) => ask(`${label} (assumptions, definitions)`, prompt) : ask, prior);
      for (const [id, l] of run.linked) linked.set(id, l);
      for (const id of run.audited) audited.add(id);
      problems.push(...run.problems); changes.push(...run.changes); revised.push(...run.revised);
    } catch (e) {
      problems.push(`the link step failed: ${String((e as Error)?.message ?? e).split("\n")[0]}`);
    }
  }
  // links the audit did not return whole (its call failed, its reply was refused, no answer) carry no
  // basis: the next link revises or asks them again
  const fresh = items.map((it) => kept.get(it.obj_id) ?? { ...storedResult(it, linked.get(it.obj_id)), ...(audited.has(it.obj_id) ? { basis: linkBasis(it, tplOf(it)) } : {}) });
  // a re-link of some results keeps what is stored for the others
  const before = args.only ? onFile : null;
  const redone = new Set(fresh.map((r) => r.node));
  const results = [...(before?.results ?? []).filter((r) => !redone.has(r.node) && !args.only!.has(r.node)), ...fresh];
  const answered = results.filter((r) => !r.unanswered);
  const unlinked = [...new Set([
    ...(before?.unlinked ?? []).filter((u) => ![...args.only!, ...items.map((it) => it.obj_id)].includes(u.split(" ")[0]!)),
    ...skipped.map((s) => s.label), ...results.filter((r) => r.unanswered).map((r) => r.obj_id),
  ])];
  const sum = (f: (m: LinkMetrics) => number) => results.reduce((n, r) => n + f(r.metrics), 0);
  const rows = { asked: sum((m) => m.asked), linked: sum((m) => m.linked), unstated: sum((m) => m.unstated), unanswered: sum((m) => m.unanswered), shared: sum((m) => m.shared) };
  const unique = rows.linked ? Math.round((100 * sum((m) => m.unique * m.linked)) / rows.linked) / 100 : 1;
  const warnings = [
    ...(unlinked.length ? [`not linked: ${unlinked.join(", ")}`] : []),
    ...(rows.unanswered ? [`${rows.unanswered} row(s) left unanswered`] : []),
    ...(rows.shared ? [`${rows.shared} row(s) under a list shared by more rows than their result allows (${results.filter((r) => r.metrics.shared).map((r) => r.obj_id).join(", ")})`] : []),
    ...(unique < UNIQUE_SHARE_WARN ? [`only ${Math.round(unique * 100)}% of the linked rows have a segment list of their own`] : []),
  ];
  const artifact = { results, unlinked, summary: { results: answered.length, of: results.length + unlinked.length - results.filter((r) => r.unanswered).length, rows, unique, warnings }, problems, changes };
  await writeFile(file, JSON.stringify(artifact, null, 1) + "\n", "utf8");
  for (const r of fresh) {
    if (kept.has(r.obj_id)) continue;
    const m = r.metrics;
    console.log(`[theoremchecker] F5 nl-links ${r.obj_id}: rows asked ${m.asked}, linked ${m.linked}, unstated ${m.unstated}, unanswered ${m.unanswered}; lists of their own ${Math.round(m.unique * 100)}%, most segments on a row ${m.max_segments}${m.shared ? `, under a shared list ${m.shared}` : ""}`);
  }
  const uncovered = answered.filter((r) => r.uncovered.length > 0).map((r) => r.obj_id);
  return `${answered.length}/${artifact.summary.of} result(s) linked row by row${kept.size || revised.length ? ` (${[kept.size ? `${kept.size} kept as linked` : "", revised.length ? `${revised.length} revised from the links on file` : ""].filter(Boolean).join(", ")})` : ""}; rows asked ${rows.asked}, linked ${rows.linked}, unstated ${rows.unstated}; lists of their own ${Math.round(unique * 100)}%` +
    (uncovered.length ? `; paper text no Lean row states in ${uncovered.join(", ")}` : "") +
    (warnings.length ? `; WARNING: ${warnings.join("; ")}` : "");
}
