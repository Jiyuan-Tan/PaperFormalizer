/**
 * Paper excerpts for the sharded V1.5 referee: instead of the whole flattened paper, a shard reads
 * the paper's SETUP (macro definitions and the text up to its first result), the exact statement
 * and proof of each node it grades as they sit in `flat.tex`, and the passages those two reference.
 *
 * Locating a node in `flat.tex`. Every node's `tex_locator` is in the user's ORIGINAL file
 * coordinates; `flat.linemap.json` maps flat lines back to them. A locator that maps through the
 * line map, and whose lines hold the node's text, is used directly. Otherwise (a run whose flat
 * text was rebuilt, a file the line map does not cover) the node's verbatim text — the environment
 * body `envs.json` holds for the locator, or the node's own text — is found in `flat.tex` by its
 * first and last lines. A node found neither way is shown with the core's own text, marked so.
 *
 * Symbols (the symbol referee, `referee_symbols.ts`): `symbolSlices` gives, per symbol of the table,
 * the paragraph that introduces it, any later defining sentence, and one or two places it is used.
 */
import type { Core } from "../core/schema.js";
import { normalizeSymbol } from "../core/symbol_names.js";
import { canonicalTokens, isDefiningOccurrence, symbolOccurrences, symbolPattern, type SymbolPattern } from "./symbol_match.js";
import type { EnvKind, EnvsJson, FlatTexLineMap, TexEnv, TexLocator } from "./types.js";

/** Caps (characters). The shard can always read the rest from `discovery/flat.tex`. */
export const SETUP_MAX = 30_000;
export const MACROS_MAX = 10_000;
export const SLICE_MAX = 60_000;
export const REFS_MAX = 40_000;
const SECTION_REF_MAX = 12_000;
const PARAGRAPH_REF_MAX = 4_000;

export interface PaperIndex {
  lines: string[];
  lineMap: FlatTexLineMap["lineMap"] | null;
  envs: EnvsJson | null;
}

export interface Excerpt {
  /** Where the text came from: `flat.tex lines a–b`, or `core text (not located in flat.tex)`. */
  where: string;
  text: string;
  /** 1-based inclusive flat lines, when located. */
  range: [number, number] | null;
}

export interface NodeExcerpts {
  id: string;
  statement: Excerpt;
  proof: Excerpt | null;
  /** An inline cited leaf (`cited_in`): the proof its passage is a step of — context, never its own proof. */
  context?: { of: string; excerpt: Excerpt };
  /** Labels the statement and proof reference. */
  refs: string[];
}

export function paperIndex(flatTex: string, lineMap: FlatTexLineMap | null, envs: EnvsJson | null): PaperIndex {
  return { lines: flatTex.split("\n"), lineMap: lineMap?.lineMap ?? null, envs };
}

const norm = (s: string): string => s.replace(/\s+/g, " ").trim();

function nonBlankLines(text: string): string[] {
  return text.split("\n").map(norm).filter((l) => l.length > 0);
}

/** The flat lines a locator covers through the line map, or null. */
export function flatRange(px: PaperIndex, loc: TexLocator | undefined): [number, number] | null {
  if (!loc || !px.lineMap || loc.from <= 0) return null;
  let lo = -1;
  let hi = -1;
  px.lineMap.forEach((m, i) => {
    if (m.file === loc.file && m.line >= loc.from && m.line <= loc.to) {
      if (lo === -1) lo = i;
      hi = i;
    }
  });
  return lo === -1 ? null : [lo + 1, hi + 1];
}

/** Find `text` in the flat lines by its first and last non-blank lines (whitespace-insensitive),
 * optionally within `window` (1-based inclusive flat lines). With several matches of the first
 * line, the one nearest `hint` (a 0-based flat line) wins. */
export function findText(px: PaperIndex, text: string, hint = 0, window?: [number, number]): [number, number] | null {
  const tl = nonBlankLines(text);
  if (tl.length === 0) return null;
  const firstKey = tl[0]!.slice(0, 60);
  const lastKey = tl[tl.length - 1]!.slice(-60);
  if (firstKey.length < 8) return null;
  const flat = px.lines.map(norm);
  const lo = window ? window[0] - 1 : 0;
  const hi = window ? window[1] : flat.length;
  const starts: number[] = [];
  for (let i = lo; i < hi; i += 1) if (flat[i]!.includes(firstKey)) starts.push(i);
  if (starts.length === 0) return null;
  starts.sort((a, b) => Math.abs(a - hint) - Math.abs(b - hint));
  const i = starts[0]!;
  // The flat text has at least the text's non-blank lines (it may add comment and blank lines), so
  // the end is no earlier than that: a generic last line (`\end{equation*}`) that also occurs
  // inside the text is not taken for its end.
  const limit = Math.min(hi, i + tl.length * 3 + 50);
  for (let j = i + tl.length - 1; j < limit; j += 1) {
    if (flat[j]!.includes(lastKey)) return [i + 1, j + 1];
  }
  return null;
}

/** Widen a range to the enclosing `\begin{…}` / `\end{…}` lines when they sit just outside it. */
function widenToEnv(px: PaperIndex, [a, b]: [number, number]): [number, number] {
  let lo = a;
  let hi = b;
  for (let k = 1; k <= 3 && lo - k >= 1; k += 1) {
    if (/\\begin\{/.test(px.lines[lo - k - 1]!)) {
      lo -= k;
      break;
    }
  }
  if (!/\\end\{/.test(px.lines[hi - 1]!)) {
    for (let k = 1; k <= 2 && hi + k <= px.lines.length; k += 1) {
      if (/\\end\{/.test(px.lines[hi + k - 1]!)) {
        hi += k;
        break;
      }
    }
  }
  return [lo, hi];
}

function cut(px: PaperIndex, [a, b]: [number, number]): Excerpt {
  let text = px.lines.slice(a - 1, b).join("\n");
  if (text.length > SLICE_MAX) {
    text = `${text.slice(0, SLICE_MAX)}\n[… ${text.length - SLICE_MAX} characters not shown; read discovery/flat.tex lines ${a}–${b} …]`;
  }
  return { where: `flat.tex lines ${a}–${b}`, text, range: [a, b] };
}

/** Locate `text` (hinted by `loc`): within the lines the line map gives for the locator, else
 * anywhere. `widen` (a whole environment body): include the `\begin{…}` / `\end{…}` lines. */
function locate(px: PaperIndex, text: string, loc: TexLocator | undefined, widen: boolean): Excerpt | null {
  const mapped = flatRange(px, loc);
  const found =
    (mapped ? findText(px, text, mapped[0] - 1, mapped) : null) ??
    findText(px, text, mapped ? mapped[0] - 1 : Math.max(0, (loc?.from ?? 1) - 1));
  return found ? cut(px, widen ? widenToEnv(px, found) : found) : null;
}

function envOf(px: PaperIndex, loc: TexLocator | undefined): TexEnv | null {
  if (!loc || !px.envs) return null;
  return (
    px.envs.envs.find((e) => e.lines.file === loc.file && e.lines.from === loc.from && e.lines.to === loc.to) ??
    (loc.label ? px.envs.envs.find((e) => e.label === loc.label) ?? null : null)
  );
}

const REF_RE = /\\(?:[cC]ref|ref|eqref|autoref|thmref|Autoref|nameref)\{([^}]*)\}/g;

export function refsIn(text: string): string[] {
  const out: string[] = [];
  for (const m of text.matchAll(REF_RE)) for (const l of m[1]!.split(",")) if (l.trim() && !out.includes(l.trim())) out.push(l.trim());
  return out;
}

type AnyNode = { id: string; tex_locator?: TexLocator; statement?: string; proof_tex?: string; condition?: string; construction?: string; cited_in?: string };

function nodeById(core: Core, id: string): AnyNode | undefined {
  return ([...core.statements, ...core.assumptions, ...core.definitions] as AnyNode[]).find((n) => n.id === id);
}

/** The statement and proof of one node as they sit in `flat.tex`. */
export function nodeExcerpts(px: PaperIndex, core: Core, id: string): NodeExcerpts {
  const node = nodeById(core, id);
  const own = (node?.statement ?? node?.condition ?? node?.construction ?? "").replace(/\s*\[Hypotheses:[^\]]*\]\s*$/, "");
  const env = envOf(px, node?.tex_locator);
  // A statement is searched by its environment body; an assumption/definition sliced from an
  // environment or from the running text by its own text. A node whose text is its environment's
  // whole body (a statement, an assumption or definition environment) is shown with the
  // environment's `\begin`/`\end` lines; a premise sliced out of a result or the running text,
  // exactly as sliced.
  const wholeBody = !!env && norm(env.body) === norm(own);
  const isStatement = node?.statement !== undefined;
  const statementText = isStatement && env && norm(env.body).includes(norm(own).slice(0, 60)) ? env.body : own;
  const statement =
    locate(px, statementText, node?.tex_locator, wholeBody || statementText === env?.body) ??
    { where: "core text (not located in flat.tex)", text: own, range: null };
  const proofText = isStatement ? (env?.proof ?? node?.proof_tex ?? null) : null;
  let proof: Excerpt | null = null;
  if (proofText && proofText.trim()) {
    proof = locate(px, proofText, env?.proofLines ?? undefined, true) ?? { where: "core proof_tex (not located in flat.tex)", text: proofText, range: null };
  } else if (isStatement && node?.tex_locator?.label) {
    // No proof next to the result: a proof elsewhere that names it (`\begin{proof}[Proof of
    // Theorem \ref{…}]`, `\subsection{Proof of Theorem \ref{…}}`).
    proof = proofByRef(px, node.tex_locator.label);
  }
  const refs = [...new Set([...(env?.refs ?? []), ...refsIn(statement.text), ...refsIn(proof?.text ?? "")])];
  // An inline cited leaf sits at its host's proof locator (no environment of its own): the host's
  // proof is what its passage is read in.
  const host = node?.cited_in ? nodeById(core, node.cited_in) : undefined;
  const hostEnv = envOf(px, host?.tex_locator);
  const hostProof = hostEnv?.proof?.trim() ? locate(px, hostEnv.proof, hostEnv.proofLines ?? undefined, true) : null;
  return { id, statement, proof, ...(host && hostProof ? { context: { of: host.id, excerpt: hostProof } } : {}), refs };
}

/** A proof placed away from its result that names the result's label: a `proof` environment
 * titled with `\ref{label}` (to its matching `\end{proof}`), or a `Proof of … \ref{label}` heading
 * (to the next heading of the same or a higher level). */
export function proofByRef(px: PaperIndex, label: string): Excerpt | null {
  const esc = (t: string): string => t.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const ref = `\\\\(?:[cC]ref|ref|autoref)\\{${esc(label)}\\}`;
  const envRe = new RegExp(`${esc("\\begin{proof}[")}[^\\]]*${ref}`);
  const headRe = new RegExp(`^\\s*\\\\(?:sub)*section\\*?\\{[^}]*[Pp]roof.*${ref}`);
  for (let i = 0; i < px.lines.length; i += 1) {
    const line = px.lines[i]!;
    if (envRe.test(line)) {
      let depth = 0;
      for (let j = i; j < px.lines.length; j += 1) {
        depth += (px.lines[j]!.match(/\\begin\{proof\}/g) ?? []).length - (px.lines[j]!.match(/\\end\{proof\}/g) ?? []).length;
        if (depth <= 0) return cut(px, [i + 1, j + 1]);
      }
      return cut(px, [i + 1, Math.min(px.lines.length, i + 400)]);
    }
    if (headRe.test(line)) {
      const level = LEVEL[line.match(HEADING_RE)?.[1] ?? "subsection"] ?? 3;
      for (let j = i + 1; j < px.lines.length; j += 1) {
        const m = px.lines[j]!.match(HEADING_RE);
        if ((m && LEVEL[m[1]!]! <= level) || /\\end\{document\}/.test(px.lines[j]!)) return cut(px, [i + 1, j]);
      }
      return cut(px, [i + 1, px.lines.length]);
    }
  }
  return null;
}

const RESULT_KINDS: ReadonlySet<EnvKind> = new Set<EnvKind>(["theorem", "lemma", "proposition", "corollary"]);
const DEFAULT_RESULT_ENVS = ["theorem", "thm", "lemma", "lem", "proposition", "prop", "corollary", "cor"];

/** The paper's setup: its macro definitions and the text from `\begin{document}` to its first
 * result, capped (the head and the part nearest the first result are kept). */
export function setupExcerpt(px: PaperIndex): { macros: string; setup: string; where: string } {
  const docStart = px.lines.findIndex((l) => /\\begin\{document\}/.test(l));
  const macroLines = (docStart === -1 ? [] : px.lines.slice(0, docStart)).filter((l) =>
    /\\(newcommand|renewcommand|providecommand|def\b|DeclareMathOperator|newtheorem|let\b)/.test(l),
  );
  let macros = macroLines.join("\n");
  if (macros.length > MACROS_MAX) macros = `${macros.slice(0, MACROS_MAX)}\n[… more macro definitions in discovery/flat.tex …]`;
  const names = new Set(DEFAULT_RESULT_ENVS);
  for (const [name, kind] of Object.entries(px.envs?.newtheorem ?? {})) if (RESULT_KINDS.has(kind)) names.add(name);
  const begin = docStart + 1;
  let end = px.lines.length;
  for (let i = begin; i < px.lines.length; i += 1) {
    const m = px.lines[i]!.match(/\\begin\{([A-Za-z*]+)\}/);
    if (m && names.has(m[1]!.replace(/\*$/, ""))) {
      end = i;
      break;
    }
  }
  let setup = withoutBibliography(px.lines.slice(begin, end)).join("\n");
  if (setup.length > SETUP_MAX) {
    const head = Math.floor(SETUP_MAX / 5);
    setup =
      `${setup.slice(0, head)}\n[… ${setup.length - SETUP_MAX} characters elided; the whole paper is at discovery/flat.tex …]\n` +
      setup.slice(setup.length - (SETUP_MAX - head));
  }
  return { macros, setup, where: `flat.tex lines ${begin + 1}–${end}` };
}

const CITE_RE = /\\(?:cite|citet|citep|citealt|citealp|citeauthor|citeyear|parencite|textcite|autocite)\*?(?:\[[^\]]*\]){0,2}\{([^}]*)\}/g;

/** Lines outside any `thebibliography` environment, without `\bibitem` / `\bibliography…` lines. */
export function withoutBibliography(lines: string[]): string[] {
  const out: string[] = [];
  let inBib = false;
  for (const l of lines) {
    if (/\\begin\{thebibliography\}/.test(l)) inBib = true;
    if (!inBib && !/^\s*\\(bibitem|bibliography|bibliographystyle|bibinfo|newblock)\b/.test(l)) out.push(l);
    if (/\\end\{thebibliography\}/.test(l)) inBib = false;
  }
  return out;
}

/** The keys a text cites. */
export function citesIn(text: string): string[] {
  const out: string[] = [];
  for (const m of text.matchAll(CITE_RE)) for (const k of m[1]!.split(",")) if (k.trim() && !out.includes(k.trim())) out.push(k.trim());
  return out;
}

/** The bibliography entries of `keys` (from `envs.json`, else the `\bibitem`s of `flat.tex`). */
export function bibliographyEntries(px: PaperIndex, keys: readonly string[]): Array<{ key: string; text: string }> {
  const out: Array<{ key: string; text: string }> = [];
  for (const key of keys) {
    const e = px.envs?.bibliography.find((b) => b.key === key);
    if (e) {
      out.push({ key, text: e.text.replace(/\s+/g, " ").trim() });
      continue;
    }
    const at = px.lines.findIndex((l) => new RegExp(`\\\\bibitem(\\[[^\\]]*\\])?\\{${key.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\}`).test(l));
    if (at === -1) continue;
    let end = at + 1;
    while (end < px.lines.length && end - at < 12 && !/\\bibitem|\\end\{thebibliography\}/.test(px.lines[end]!)) end += 1;
    out.push({ key, text: px.lines.slice(at, end).join(" ").replace(/\s+/g, " ").trim().slice(0, 600) });
  }
  return out;
}

const HEADING_RE = /^\s*\\(part|chapter|section|subsection|subsubsection|paragraph)\*?[\[{]/;
const LEVEL: Record<string, number> = { part: 0, chapter: 1, section: 2, subsection: 3, subsubsection: 4, paragraph: 5 };

/** The flat lines (1-based, inclusive) of the section whose heading carries `\label{label}`: to the
 * next heading of the same or a higher level. Null when the label is on no heading. */
export function sectionRange(px: PaperIndex, label: string): [number, number] | null {
  const at = px.lines.findIndex((l) => l.includes(`\\label{${label}}`));
  // On the heading's line, or alone on the next one (never the label of an environment opened there).
  const headAt = at === -1 ? undefined : [at, ...(/\\begin\{/.test(px.lines[at]!) ? [] : [at - 1])].find((i) => i >= 0 && HEADING_RE.test(px.lines[i]!));
  if (headAt === undefined) return null;
  const level = LEVEL[px.lines[headAt]!.match(HEADING_RE)![1]!]!;
  let end = px.lines.length;
  for (let i = headAt + 1; i < px.lines.length; i += 1) {
    const m = px.lines[i]!.match(HEADING_RE);
    if ((m && LEVEL[m[1]!]! <= level) || /\\end\{document\}/.test(px.lines[i]!)) {
      end = i;
      break;
    }
  }
  return [headAt + 1, end];
}

/** The passage a `\label` marks: a section (to the next heading of the same or a higher level), or
 * the paragraph around an equation or a remark (to the nearest blank lines), capped. */
export function labelPassage(px: PaperIndex, label: string): Excerpt | null {
  const at = px.lines.findIndex((l) => l.includes(`\\label{${label}}`));
  if (at === -1) return null;
  const headAt = [at, at - 1].find((i) => i >= 0 && HEADING_RE.test(px.lines[i]!));
  if (headAt !== undefined) {
    const level = LEVEL[px.lines[headAt]!.match(HEADING_RE)![1]!]!;
    let end = px.lines.length;
    for (let i = headAt + 1; i < px.lines.length; i += 1) {
      const m = px.lines[i]!.match(HEADING_RE);
      if ((m && LEVEL[m[1]!]! <= level) || /\\end\{document\}/.test(px.lines[i]!)) {
        end = i;
        break;
      }
    }
    return capped(px, [headAt + 1, end], SECTION_REF_MAX);
  }
  let lo = at;
  let hi = at;
  while (lo > 0 && at - lo < 40 && px.lines[lo - 1]!.trim() !== "") lo -= 1;
  while (hi < px.lines.length - 1 && hi - at < 40 && px.lines[hi + 1]!.trim() !== "") hi += 1;
  return capped(px, [lo + 1, hi + 1], PARAGRAPH_REF_MAX);
}

function capped(px: PaperIndex, [a, b]: [number, number], max: number): Excerpt {
  const e = cut(px, [a, b]);
  if (e.text.length <= max) return e;
  return { ...e, text: `${e.text.slice(0, max)}\n[… read discovery/flat.tex lines ${a}–${b} for the rest …]` };
}

const overlaps = (x: [number, number], y: [number, number]): boolean => x[0] <= y[1] && y[0] <= x[1];

/** The passages the given nodes reference that no node of the core carries (a displayed equation,
 * a remark, a section), deduplicated and capped in total; the labels left out are named. */
export function referencedPassages(
  px: PaperIndex,
  core: Core,
  excerpts: NodeExcerpts[],
): { passages: Array<{ label: string; excerpt: Excerpt }>; omitted: string[] } {
  const coreLabels = new Set(
    ([...core.statements, ...core.assumptions, ...core.definitions] as AnyNode[]).map((n) => n.tex_locator?.label).filter((l): l is string => !!l),
  );
  const shown: Array<[number, number]> = excerpts.flatMap((e) => [e.statement.range, e.proof?.range ?? null]).filter((r): r is [number, number] => !!r);
  const passages: Array<{ label: string; excerpt: Excerpt }> = [];
  const omitted: string[] = [];
  let total = 0;
  for (const label of [...new Set(excerpts.flatMap((e) => e.refs))]) {
    if (coreLabels.has(label)) continue;
    const ex = labelPassage(px, label);
    if (!ex || !ex.range) continue;
    if (shown.some((r) => overlaps(r, ex.range!))) continue;
    if (total + ex.text.length > REFS_MAX) {
      omitted.push(label);
      continue;
    }
    total += ex.text.length;
    shown.push(ex.range);
    passages.push({ label, excerpt: ex });
  }
  return { passages, omitted };
}

// ---------------------------------------------------------------------------------------------
// Symbols: where each symbol of the table is introduced and used
// ---------------------------------------------------------------------------------------------

/** Caps (characters) of a symbol's passages in a symbol shard. */
export const SYMBOL_CAPS = { intro: 3_000, use: 1_500, uses: 2, redefinitions: 2 } as const;
export type SymbolCaps = typeof SYMBOL_CAPS;

/** How far a symbol's introducing paragraph reaches from its defining line, each way. */
const PARAGRAPH_REACH = 25;

export interface SymbolExcerpt extends Excerpt {
  /** The flat line (1-based) of the occurrence the excerpt is centred on. */
  line: number;
}

export interface SymbolSlices {
  name: string;
  /** The passage that introduces the symbol: the paragraph around its first DEFINING occurrence
   * ("where Δ = …", "let", "denote", …), else around its first occurrence; null when the symbol
   * never occurs in the paper's body. */
  intro: (SymbolExcerpt & { how: "defining sentence" | "first occurrence" }) | null;
  /** Other defining occurrences outside the introducing passage (a possible change of meaning). */
  redefinitions: SymbolExcerpt[];
  /** Where it is used: inside the results / hypotheses whose `free_symbols` list it (their
   * located passage), else other occurrences of the paper. */
  uses: Array<SymbolExcerpt & { node: string | null }>;
}

/** The body's lines (0-based indices): after `\begin{document}` and before `\end{document}`, without
 * the bibliography (a `thebibliography` environment, `\bibliography{…}` lines) — appendices after
 * the references included. */
function bodyLines(px: PaperIndex): number[] {
  const start = px.lines.findIndex((l) => /\\begin\{document\}/.test(l)) + 1;
  const out: number[] = [];
  let inBib = false;
  for (let i = start; i < px.lines.length; i += 1) {
    const l = px.lines[i]!;
    if (/\\end\{document\}/.test(l)) break;
    if (/\\begin\{thebibliography\}/.test(l)) inBib = true;
    if (!inBib && !/^\s*\\(bibliography|bibliographystyle)\b/.test(l)) out.push(i);
    if (/\\end\{thebibliography\}/.test(l)) inBib = false;
  }
  return out;
}

/** Per-line canonical tokens, computed once per paper. */
const tokenCache = new WeakMap<PaperIndex, Array<ReturnType<typeof canonicalTokens> | undefined>>();
function lineTokens(px: PaperIndex, i: number): ReturnType<typeof canonicalTokens> {
  let arr = tokenCache.get(px);
  if (!arr) tokenCache.set(px, (arr = []));
  return (arr[i] ??= canonicalTokens(px.lines[i]!));
}

/** Every occurrence of a symbol in the paper's body: flat line index (0-based) and whether it defines it. */
export function symbolLines(px: PaperIndex, pat: SymbolPattern): Array<{ i: number; defining: boolean }> {
  const out: Array<{ i: number; defining: boolean }> = [];
  for (const i of bodyLines(px)) {
    const line = px.lines[i]!;
    if (line.trimStart().startsWith("%")) continue;
    const canon = lineTokens(px, i);
    const occ = symbolOccurrences(line, pat, canon);
    if (occ.length === 0) continue;
    out.push({ i, defining: occ.some((o) => isDefiningOccurrence(line, o, canon)) });
  }
  return out;
}

const HEADING_LINE = /^\s*\\(part|chapter|section|subsection|subsubsection|paragraph)\*?[\[{]/;

/** The paragraph around flat line `i` (0-based): up and down to a blank line or a heading, at most
 * `PARAGRAPH_REACH` lines each way; 1-based inclusive. */
function paragraphAround(px: PaperIndex, i: number): [number, number] {
  let lo = i;
  let hi = i;
  while (lo > 0 && i - lo < PARAGRAPH_REACH && px.lines[lo - 1]!.trim() !== "" && !HEADING_LINE.test(px.lines[lo]!)) lo -= 1;
  while (hi < px.lines.length - 1 && hi - i < PARAGRAPH_REACH && px.lines[hi + 1]!.trim() !== "" && !HEADING_LINE.test(px.lines[hi + 1]!) && !/\\end\{document\}/.test(px.lines[hi + 1]!)) hi += 1;
  return [lo + 1, hi + 1];
}

/** Lines `[a, b]` (1-based) cut to at most `max` characters, keeping whole lines nearest `centre`. */
function centredCut(px: PaperIndex, [a, b]: [number, number], centre: number, max: number): SymbolExcerpt {
  let lo = centre;
  let hi = centre;
  let size = px.lines[centre - 1]!.length + 1;
  for (;;) {
    const up = lo > a ? px.lines[lo - 2]!.length + 1 : Infinity;
    const down = hi < b ? px.lines[hi]!.length + 1 : Infinity;
    const step = Math.min(up, down);
    if (step === Infinity || size + step > max) break;
    if (up <= down) lo -= 1;
    else hi += 1;
    size += step;
  }
  let text = px.lines.slice(lo - 1, hi).join("\n");
  if (text.length > max) text = `${text.slice(0, max)} […]`;
  const clipped = lo > a || hi < b ? `\n[… the paragraph runs over flat.tex lines ${a}–${b} …]` : "";
  return { where: `flat.tex lines ${lo}–${hi}`, text: `${text}${clipped}`, range: [lo, hi], line: centre };
}

/** The clipping marker `centredCut` appends (it carries line numbers). */
const CLIPPED_MARKER = /\n\[… the paragraph runs over flat\.tex lines \d+–\d+ …\]$/;

/** An excerpt's words alone — the clipping marker and its line numbers dropped, whitespace
 * collapsed — for a cache basis: an upstream line shift moves no verdict. */
export function excerptWords(e: Pick<SymbolExcerpt, "text"> | null | undefined): string {
  return (e?.text ?? "").replace(CLIPPED_MARKER, "").replace(/\s+/g, " ").trim();
}

const inside = (line: number, r: [number, number] | null): boolean => !!r && line >= r[0] && line <= r[1];

/**
 * Where symbol `name` is introduced and used in the paper (`caps`: the full or the light form).
 * Introduction: `flat.tex` searched for the symbol as a whole token (`symbol_match.ts`); the first
 * defining occurrence wins, else the first occurrence. Uses: the located passages of the core nodes
 * whose `free_symbols` list the symbol (results first), at the symbol's first occurrence there;
 * else further occurrences of the paper. `excerptOf` locates a node (cached by the caller).
 */
export function symbolSlices(
  px: PaperIndex,
  core: Core,
  name: string,
  caps: SymbolCaps,
  excerptOf: (id: string) => Excerpt,
): SymbolSlices {
  const pat = symbolPattern(name);
  const occ = symbolLines(px, pat);
  const def = occ.find((o) => o.defining);
  const first = def ?? occ[0];
  let intro: SymbolSlices["intro"] = null;
  if (first) {
    const para = paragraphAround(px, first.i);
    intro = { ...centredCut(px, para, first.i + 1, caps.intro), how: def ? "defining sentence" : "first occurrence" };
  }
  const introPara = first ? paragraphAround(px, first.i) : null;
  const redefinitions: SymbolExcerpt[] = [];
  for (const o of occ) {
    if (redefinitions.length >= caps.redefinitions) break;
    if (!o.defining || o === first || inside(o.i + 1, introPara) || redefinitions.some((r) => inside(o.i + 1, r.range))) continue;
    redefinitions.push(centredCut(px, paragraphAround(px, o.i), o.i + 1, caps.use));
  }
  const uses: SlicesUse[] = [];
  const shown = (line: number): boolean => inside(line, introPara) || redefinitions.some((r) => inside(line, r.range)) || uses.some((u) => inside(line, u.range));
  const norm = normalizeSymbol(name);
  const listing = [
    ...core.statements.filter((s) => s.status !== "cited"),
    ...core.statements.filter((s) => s.status === "cited"),
    ...core.assumptions,
    ...core.definitions,
  ].filter((n) => (n.free_symbols ?? []).some((f) => normalizeSymbol(f) === norm));
  const seenRanges = new Set<string>();
  for (const n of listing) {
    if (uses.length >= caps.uses) break;
    const ex = excerptOf(n.id);
    if (!ex.range || seenRanges.has(ex.range.join("-"))) continue;
    seenRanges.add(ex.range.join("-"));
    const hit = occ.find((o) => inside(o.i + 1, ex.range) && !shown(o.i + 1));
    if (!hit) continue;
    uses.push({ ...centredCut(px, [Math.max(ex.range[0], hit.i - 3), Math.min(ex.range[1], hit.i + 5)], hit.i + 1, caps.use), node: n.id });
  }
  for (const o of occ) {
    if (uses.length >= caps.uses) break;
    if (shown(o.i + 1)) continue;
    uses.push({ ...centredCut(px, [Math.max(1, o.i - 2), Math.min(px.lines.length, o.i + 4)], o.i + 1, caps.use), node: null });
  }
  return { name, intro, redefinitions, uses };
}
type SlicesUse = SymbolSlices["uses"][number];
