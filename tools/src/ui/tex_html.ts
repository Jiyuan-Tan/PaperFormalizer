// TeX → HTML for the paper page of the local UI.
//
// Input: a paper's TeX files as the run holds them — `annotated/` (the source with every finding
// marked by `annotate_tex.ts`'s macros) or `source/` before the first halt. The source is never
// changed: the renderer works on a NORMAL FORM derived from it — the author's own macros (with
// arguments) and environments expanded, theorem-like environments named from the preamble, the
// class (via the run's envs.json) or a fallback, `\input` inlined — and numbers the paper itself
// (sections, results, equations line by line, figures, tables) in a first pass, so every `\ref`
// resolves even when the paper was never compiled; a compiled `.aux` wins where present.
//
// Output: the body as HTML with math rendered by KaTeX on the server, figures (images inline, PDF
// figures drawn by pdf.js in the browser), tables as HTML tables, the annotations (red original /
// blue corrected marks in the text, every note a margin comment tied to its result), anchors for
// results stated in prose, and a render check (what could not be resolved or shown).
//
// Every text is HTML-escaped; links are http(s) only; asset URLs point only at files listed by the
// server.

import { createHash } from "node:crypto";
import katex from "katex";
import { renderAlgorithm2e, renderAlgorithmic } from "./algorithms.js";
import { mathjaxRenderer } from "./mathjax.js";
import { UMBRELLA_STATEMENT, umbrellaSentence } from "../verify/core_graph.js";
import { stripIffalse } from "../verify/tex_envs.js";
import { handNumber } from "../verify/report_plain.js";

export interface PaperComment {
  id: string;
  /** The note's identity across renders (`id` is its position): a hash of its kind, environment and
   *  source — and, for a second note with the same three, its order among them (`<hash>-2`). */
  key: string;
  /** How its source begins, for the agent (an issue the owner reports on it). */
  excerpt: string;
  /** note | reading | reading-owner | reading-symbol | condition | rewind | cap */
  kind: string;
  label: string;
  html: string;
  /** Label of the theorem-like environment the note sits in (or follows), when any. */
  env: string | null;
}

export interface PaperEnv { anchor: string; label: string | null; envName: string; heading: string }

/** A formula neither KaTeX nor MathJax reads: left to the orchestrating agent (`ui_math_overrides.json`). */
export interface MathFailure { tex: string; error: string; near: string }

export interface RenderHealth {
  unresolvedRefs: string[];
  unknownCommands: Record<string, number>;
  /** Formulas shown as source (= mathFailures.length). */
  mathErrors: number;
  /** Formulas KaTeX refused and MathJax drew. */
  mathFallbacks: number;
  mathFailures: MathFailure[];
  figures: number;
  missingFigures: string[];
  tables: number;
  omitted: number;
}

export interface RenderedPaper {
  title: string;
  authors: string;
  html: string;
  /** The contents: each heading as text, and as it is drawn (`html`: its formulas typeset). */
  toc: Array<{ id: string; text: string; html: string; level: number }>;
  comments: PaperComment[];
  envs: PaperEnv[];
  /** Core nodes anchored at their source line (`PaperInput.anchors`): node → anchor id. */
  anchors: Record<string, string>;
  /** Pinned readings a note of the page states (`PaperInput.readings`): node → comment id. */
  readings: Record<string, string>;
  marks: number;
  macros: Record<string, string>;
  /** label → page in the compiled PDF (from the .aux), for "view in the PDF". */
  pages: Record<string, string>;
  /** label → the number the paper prints for it, for a `\ref` in text the page sets itself. */
  labels: Record<string, string>;
  health: RenderHealth;
}

export interface PaperInput {
  files: Record<string, string>;
  main: string;
  aux?: string | null;
  bbl?: string | null;
  /** Theorem-like environments the class or a package defines (envs.json `newtheorem`: env → kind). */
  theoremKinds?: Record<string, string> | null;
  /** The kind of each block a repair split off a result, by node, as the core gives it
   * (`core_graph.ts` `splitKinds`): it overrides the block's macro, so an annotated paper written
   * before the kinds were told apart (every block a `\vsCorollary`) is headed right. */
  splitKinds?: Record<string, "corollary" | "proposition"> | null;
  /** Files in the paper's directory (relative, `/`-separated) a figure may point at. */
  assets?: string[];
  /** URL prefix for an asset (`<base>/<relative path>`). */
  assetBase?: string;
  /** The paper's TikZ pictures typeset apart (`tikzPictures`), one to a page of the PDF at `url`, in
   *  the order of `pictures`: each is drawn from its page; absent, a picture is named and left out. */
  tikz?: { url: string; pictures: string[] } | null;
  /** Core nodes to anchor where no labelled environment holds them: the source text they start with. */
  /** `after`: the anchor stands at the end of its line, not before it. */
  anchors?: Array<{ node: string; file: string; line: string; at?: number; after?: true; nth?: [number, number] }>;
  /** Readings pinned on the core, which the paper's text does not print: the text of each and the
   *  labels of the results it is pinned on. A note states the reading whose text opens it. */
  readings?: Array<{ node: string; text: string; labels: string[] }>;
  /** A formula neither renderer reads (its source, trimmed) → the TeX to draw instead (the agent's fix). */
  mathOverrides?: Record<string, string> | null;
}

const emptyHealth = (): RenderHealth => ({ unresolvedRefs: [], unknownCommands: {}, mathErrors: 0, mathFallbacks: 0, mathFailures: [], figures: 0, missingFigures: [], tables: 0, omitted: 0 });

const esc = (s: string): string => s.replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c]!);
/** The text of rendered HTML (a heading for the contents, a result's name): tags dropped, entities decoded. */
const plain = (html: string): string => html.replace(/<[^>]+>/g, "")
  .replace(/&(?:(amp|lt|gt|quot|nbsp)|#x([0-9a-fA-F]+)|#(\d+));/g, (_m, n: string | undefined, hex: string | undefined, dec: string | undefined) =>
    n ? ({ amp: "&", lt: "<", gt: ">", quot: '"', nbsp: "\u00a0" } as Record<string, string>)[n]! : String.fromCodePoint(parseInt(hex ?? dec!, hex ? 16 : 10)));
const slug = (s: string): string => s.toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-|-$/g, "").slice(0, 60);
/** The page's anchor of a `\label` (the environment holding it, or the spot it marks). Pure. */
export const labelAnchor = (label: string): string => `lbl-${slug(label)}`;
/** A label as TeX reads it: a line break or a run of spaces in `\label{…}` / `\ref{…}` is one space. */
const labelKey = (label: string): string => label.replace(/\s+/g, " ").trim();
/** The page's anchor of a core node anchored at its source line (`PaperInput.anchors`). Pure. */
export const nodeAnchor = (node: string): string => `res-${slug(node)}`;

/** Strip `%` comments (an escaped `\%` stays). Pure. */
export function stripComments(tex: string): string {
  return tex.replace(/(^|[^\\])%[^\n]*/g, "$1");
}

/** `stripComments` that keeps a `%` inside a `\url`, `\path` or `\href` target (a percent-encoded link in a
 *  bibliography, `\url{https://x/a%2Fb}`): TeX reads those verbatim. Pure. */
export function stripCommentsKeepingUrls(tex: string): string {
  const KEEP = "\u0000PCT\u0000";
  const kept = tex.replace(/\\(?:url|path|href)\s*\{[^{}]*\}/g, (all) => all.replace(/%/g, KEEP));
  return stripComments(kept).split(KEEP).join("%");
}

/** The text with every `\input{f}` / `\include{f}` replaced by that file's text (depth ≤ 8). Pure. */
/** The text without its `\iffalse … \fi` blocks, as the parser reads it (`stripIffalse`); one left open is kept. */
function skipIffalse(text: string, file: string): string {
  try { return stripIffalse(text, file); } catch { return text; }
}

export function inlineInputs(files: Record<string, string>, main: string, depth = 0): string {
  const text = skipIffalse(stripComments((files[main] ?? "").replace(/\r\n?/g, "\n")), main);
  if (depth > 8) return text;
  return text.replace(/\\(?:input|include|subfile)\s*\{([^}]+)\}/g, (_m, name: string) => {
    const n = name.trim();
    const hit = [n, `${n}.tex`].find((k) => k in files);
    return hit ? inlineInputs(files, hit, depth + 1) : "";
  });
}

/** Read a balanced `{…}` group starting at `i` (which must be `{`). */
function group(s: string, i: number): { body: string; end: number } | null {
  if (s[i] !== "{") return null;
  let d = 0;
  for (let j = i; j < s.length; j++) {
    const c = s[j];
    if (c === "\\") { j++; continue; }
    if (c === "{") d++;
    else if (c === "}" && --d === 0) return { body: s.slice(i + 1, j), end: j + 1 };
  }
  return null;
}
/**
 * The index a `_` or `^` at `i` of text opens. Outside a formula neither is TeX: it is Unicode
 * mathematics (an agent's note), which writes an index it has no character for as `x_{i,j}`,
 * `n^(−1/2)`, `V_t` — one character, on a word that is no name with underscores, no word going on
 * after it. Null when it opens none. (The page's `subsup` reads the same.)
 */
function textIndex(s: string, i: number): { body: string; end: number } | null {
  if (s[i + 1] === "{") return group(s, i + 1);
  if (s[i] === "^" && s[i + 1] === "(") { const m = /^\((?:[^()]|\([^()]*\))*\)/.exec(s.slice(i + 1, i + 400)); return m ? { body: m[0], end: i + 1 + m[0].length } : null; }
  const m = /^[\p{Ll}\p{Lu}\p{Lo}\p{Nd}](?![\p{Ll}\p{Lu}\p{Lo}\p{Nd}_])/u.exec(s.slice(i + 1, i + 6));
  if (!m || i === 0 || /[\s_^]/.test(s[i - 1]!) || (s[i] === "_" && /_[\p{L}\p{N}.']*$/u.test(s.slice(Math.max(0, i - 200), i)))) return null;
  return { body: m[0], end: i + 1 + m[0].length };
}
/** An optional `[…]` argument at `i` (after spaces). */
function optArg(s: string, i: number): { body: string; end: number } | null {
  let j = i;
  while (s[j] === " " || s[j] === "\n") j++;
  if (s[j] !== "[") return null;
  let d = 0;
  for (let k = j; k < s.length; k++) {
    const c = s[k];
    if (c === "\\") { k++; continue; }
    if (c === "{") d++;
    else if (c === "}") d--;
    else if (c === "]" && d === 0) return { body: s.slice(j + 1, k), end: k + 1 };
  }
  return null;
}
/** A mandatory argument at `i` (after spaces): a group, or a single token. */
function arg(s: string, i: number): { body: string; end: number } {
  let j = i;
  while (s[j] === " " || s[j] === "\n") j++;
  const g = group(s, j);
  if (g) return g;
  if (s[j] === "\\") {
    const m = /^\\([A-Za-z]+|.)/.exec(s.slice(j));
    return { body: m ? m[0] : "", end: j + (m ? m[0].length : 1) };
  }
  return { body: s[j] ?? "", end: j + 1 };
}
/** A symbol reading's label as one formula: `$…$` without its delimiters. The annotated paper may have wrapped it
 *  as `{\providecommand{\x}…$…$}` (local definitions of the paper's later body macros): the definitions are
 *  dropped — the page already reads the paper's body macros — and the formula after them is kept. Pure. */
function symbolMath(raw: string): string {
  const t = raw.trim();
  const g = /^\{\\providecommand/.test(t) ? group(t, 0) : null;
  if (!g || g.end !== t.length) return t.replace(/^\$|\$$/g, "");
  const body = g.body;
  let i = 0;
  for (let m = /^\s*\\providecommand\*?/.exec(body); m; m = /^\s*\\providecommand\*?/.exec(body.slice(i))) {
    i += m[0].length;
    i = arg(body, i).end;
    for (let o = optArg(body, i); o; o = optArg(body, i)) i = o.end;
    i = arg(body, i).end;
  }
  return body.slice(i).trim().replace(/^\$|\$$/g, "");
}
/** Split at top-level occurrences of `sep` (outside braces, math and environments). */
function splitTop(s: string, sep: "&" | "\\\\"): string[] {
  const out: string[] = [];
  let d = 0, from = 0, env = 0, math = false;
  for (let i = 0; i < s.length; i++) {
    const c = s[i];
    if (c === "\\") {
      if (sep === "\\\\" && s[i + 1] === "\\" && d === 0 && env === 0 && !math) { out.push(s.slice(from, i)); i++; from = i + 1; continue; }
      if (s.startsWith("\\begin{", i)) env++;
      else if (s.startsWith("\\end{", i)) env--;
      i++; continue;
    }
    if (c === "$") { math = !math; continue; }
    if (c === "{") d++;
    else if (c === "}") d--;
    else if (sep === "&" && c === "&" && d === 0 && env === 0 && !math) { out.push(s.slice(from, i)); from = i + 1; }
  }
  out.push(s.slice(from));
  return out;
}

// ── preamble: the author's definitions ───────────────────────────────────────

interface MacroDef { n: number; dflt: string | null; body: string }
export interface Preamble {
  title: string;
  authors: string;
  /** For KaTeX (math mode): name → body, `#1` … as KaTeX expects. */
  macros: Record<string, string>;
  /** For text mode: name → definition with parameter count and optional default. */
  textMacros: Record<string, MacroDef>;
  /** Macros `\def`ined with a parameter text and no parameter (`\def\p1*{p^{*}}`): name → the text
   *  that must follow the name, and the body (`expandDelimited`). */
  delimited: Record<string, { delim: string; body: string }>;
  envDefs: Record<string, { n: number; dflt: string | null; begin: string; end: string }>;
  theorems: Record<string, { name: string; counter: string; numbered: boolean; within: string | null }>;
  numberWithin: Record<string, string>;
  graphicsPath: string[];
  /** etoolbox toggles as the preamble leaves them (`\newtoggle`, `\toggletrue`, `\togglefalse`, `\settoggle`). */
  toggles: Record<string, boolean>;
  /** cleveref's `capitalize` option (`\cref` names a section "Section" rather than "section"), when loaded. */
  crefCapital: boolean;
}

/** An etoolbox toggle command (`\newtoggle{t}`, `\toggletrue{t}`, `\togglefalse{t}`, `\settoggle{t}{true}`)
 *  with its arguments at `i`, applied to `toggles`; where its arguments end. */
function setToggle(toggles: Record<string, boolean>, cmd: string, s: string, i: number): number {
  const t = arg(s, i);
  const name = t.body.trim();
  if (cmd === "settoggle") { const v = arg(s, t.end); toggles[name] = v.body.trim() === "true"; return v.end; }
  if (cmd === "toggletrue" || cmd === "togglefalse") toggles[name] = cmd === "toggletrue";
  else toggles[name] ??= false;
  return t.end;
}

/** Title, authors, user macros, environments, theorem-like environments, numbering. Pure. */
export function readPreamble(pre: string): Preamble {
  const macros: Record<string, string> = {};
  const textMacros: Preamble["textMacros"] = {};
  const delimited: Preamble["delimited"] = {};
  const envDefs: Preamble["envDefs"] = {};
  const theorems: Preamble["theorems"] = {};
  const numberWithin: Record<string, string> = {};
  let graphicsPath: string[] = [];
  const toggles: Record<string, boolean> = {};
  const re = /\\(newcommand\*?|renewcommand\*?|providecommand\*?|DeclareMathOperator\*?|DeclareRobustCommand\*?|NewDocumentCommand|RenewDocumentCommand|ProvideDocumentCommand|DeclareDocumentCommand|def|gdef|newtheorem\*?|newenvironment\*?|renewenvironment\*?|numberwithin|graphicspath|newtoggle|providetoggle|toggletrue|togglefalse|settoggle)(?![A-Za-z])/g;
  let m: RegExpExecArray | null;
  while ((m = re.exec(pre))) {
    let i = m.index + m[0].length;
    const kind = m[1].replace("*", "");
    const star = m[1].endsWith("*");
    if (kind === "def" || kind === "gdef") {
      // a control word (`\\foo`) or a control symbol (`\\1`, `\\|`: one non-letter character)
      const nm = /^\s*(\\(?:[A-Za-z]+|[^A-Za-z\s{}%]))((?:#\d)*)\s*/.exec(pre.slice(i));
      if (!nm) continue;
      i += nm[0].length;
      // a parameter text of other characters before the body, no `#`: the name stands only before that text
      // (an `@` right after the letters continues the name under \makeatletter, `\def\th@plain`: not a parameter text)
      if (!nm[2] && pre[i] === "@") continue;
      const delim = nm[2] ? null : /^[^\s{}#\\%]+/.exec(pre.slice(i))?.[0] ?? null;
      const g = group(pre, i + (delim?.length ?? 0));
      if (!g) continue;
      // (the last definition of a name is the one TeX uses)
      if (delim) { delimited[nm[1]] = { delim, body: g.body }; delete macros[nm[1]]; delete textMacros[nm[1]]; re.lastIndex = g.end; continue; }
      delete delimited[nm[1]];
      const n = (nm[2].match(/#/g) ?? []).length;
      macros[nm[1]] = g.body;
      textMacros[nm[1]] = { n, dflt: null, body: g.body };
      re.lastIndex = g.end;
      continue;
    }
    if (kind === "graphicspath") {
      const g = arg(pre, i);
      graphicsPath = [...g.body.matchAll(/\{([^{}]*)\}/g)].map((x) => x[1].replace(/^\.\//, "").replace(/\/?$/, "/"));
      re.lastIndex = g.end;
      continue;
    }
    if (kind.includes("toggle")) { re.lastIndex = setToggle(toggles, kind, pre, i); continue; }
    if (kind === "numberwithin") {
      const a = arg(pre, i); const b = arg(pre, a.end);
      numberWithin[a.body.trim()] = b.body.trim();
      re.lastIndex = b.end;
      continue;
    }
    if (kind === "newtheorem") {
      const env = arg(pre, i); i = env.end;
      const shared = optArg(pre, i); if (shared) i = shared.end;
      const name = arg(pre, i); i = name.end;
      const within = optArg(pre, i); if (within) i = within.end;
      const counter = (shared?.body ?? env.body).trim();
      theorems[env.body.trim()] = { name: name.body.trim(), counter, numbered: !star, within: within?.body.trim() ?? null };
      if (within) numberWithin[counter] = within.body.trim();
      re.lastIndex = i;
      continue;
    }
    if (kind === "newenvironment" || kind === "renewenvironment") {
      const nameArg = arg(pre, i); i = nameArg.end;
      const n = optArg(pre, i); if (n) i = n.end;
      const dflt = n ? optArg(pre, i) : null; if (dflt) i = dflt.end;
      const begin = arg(pre, i); i = begin.end;
      const end = arg(pre, i); i = end.end;
      envDefs[nameArg.body.trim()] = { n: Number(n?.body ?? 0) || 0, dflt: dflt?.body ?? null, begin: begin.body, end: end.body };
      re.lastIndex = i;
      continue;
    }
    const nameArg = arg(pre, i); i = nameArg.end;
    const name = nameArg.body.trim();
    if (!name.startsWith("\\")) continue;
    if (kind.endsWith("DocumentCommand")) {
      // xparse: `{\name}{<argument spec>}{body}` — read when every argument is mandatory (`m`, or none)
      const spec = arg(pre, i); const body = arg(pre, spec.end);
      const ms = spec.body.replace(/\s+/g, "");
      if (/^m*$/.test(ms) && (kind !== "ProvideDocumentCommand" || !(name in macros || knownToKatex(name)))) {
        macros[name] = body.body;
        textMacros[name] = { n: ms.length, dflt: null, body: body.body };
      }
      re.lastIndex = body.end;
      continue;
    }
    if (kind === "DeclareMathOperator") {
      const body = arg(pre, i);
      macros[name] = `\\operatorname${star ? "*" : ""}{${body.body}}`;
      re.lastIndex = body.end;
      continue;
    }
    const n = optArg(pre, i); if (n) i = n.end;
    const dflt = n ? optArg(pre, i) : null; if (dflt) i = dflt.end;
    const body = arg(pre, i);
    // `\providecommand` is a fallback for a command the document may lack: it defines nothing when
    // the command exists — already defined above, or one the renderer knows itself (a preamble's
    // makeshift `\lesssim` must not replace the real symbol).
    if (kind !== "providecommand" || !(name in macros || knownToKatex(name))) {
      macros[name] = body.body;
      textMacros[name] = { n: Number(n?.body ?? 0) || 0, dflt: dflt?.body ?? null, body: body.body };
    }
    re.lastIndex = body.end;
  }
  const simple = (cmd: string) => {
    const k = pre.search(new RegExp(String.raw`\\${cmd}\s*[\[{]`));
    if (k < 0) return "";
    let i = k + cmd.length + 1;
    const o = optArg(pre, i); if (o) i = o.end;
    return arg(pre, i).body;
  };
  const crefCapital = [...pre.matchAll(/\\usepackage\s*\[([^\]]*)\]\s*\{[^}]*\bcleveref\b[^}]*\}/gu)].some((m) => /\bcapitali[sz]e\b/u.test(m[1]!));
  return { title: simple("title"), authors: simple("author"), macros, textMacros, delimited, envDefs, theorems, numberWithin, graphicsPath, toggles, crefCapital };
}

// ── aux: numbers and pages of labels, citations ──────────────────────────────

export interface AuxIndex { labels: Record<string, string>; pages: Record<string, string>; cites: Record<string, { num: string; author?: string; year?: string }> }

/** `\newlabel{l}{{num}{page}…}` (a `\tag`ged line's num braced once more, `{{K1}}`) and `\bibcite{k}{…}`
 *  (numeric or natbib author–year). Pure. */
export function readAux(aux: string | null | undefined): AuxIndex {
  const labels: Record<string, string> = {};
  const pages: Record<string, string> = {};
  const cites: AuxIndex["cites"] = {};
  if (!aux) return { labels, pages, cites };
  for (const m of aux.matchAll(/\\newlabel\{([^}]+)\}\{\{(?:\{([^{}\\]*)\}|([^{}]*))\}\{([^{}]*)\}/g)) { labels[m[1]] = m[2] ?? m[3]; pages[m[1]] = m[4]; }
  for (const m of aux.matchAll(/\\bibcite\{([^}]+)\}\{(.*)\}\s*$/gm)) {
    const body = m[2];
    const parts = [...body.matchAll(/\{((?:[^{}]|\{[^{}]*\})*)\}/g)].map((x) => x[1]);
    if (parts.length >= 3) cites[m[1]] = { num: parts[0], year: parts[1], author: parts[2].replace(/\\'\{?([a-zA-Z])\}?/g, "$1́").replace(/[{}]/g, "").normalize("NFC") };
    else cites[m[1]] = { num: body.replace(/[{}]/g, "") };
  }
  return { labels, pages, cites };
}

// ── rendering ────────────────────────────────────────────────────────────────

const MATH_ENVS = new Set(["equation", "equation*", "align", "align*", "gather", "gather*", "multline", "multline*", "eqnarray", "eqnarray*", "displaymath", "flalign", "flalign*", "alignat", "alignat*", "math", "dmath", "dmath*"]);
const FIGURE_ENVS = new Set(["figure", "figure*", "wrapfigure", "SCfigure"]);
const TABLE_ENVS = new Set(["table", "table*", "wraptable"]);
const TABULAR_ENVS = new Set(["tabular", "tabular*", "tabularx", "longtable", "tabulary"]);
const SKIP_ENVS = new Set(["tikzpicture", "picture", "pspicture", "comment"]);
const NOOP = new Set(["xspace", "noindent", "indent", "medskip", "bigskip", "smallskip", "newpage", "clearpage", "cleardoublepage", "centering", "center", "flushright", "flushleft", "raggedleft", "small", "footnotesize", "scriptsize", "tiny", "large", "Large", "LARGE", "huge", "Huge", "normalsize", "normalfont", "raggedright", "par", "maketitle", "tableofcontents", "listoffigures", "listoftables", "protect", "nopagebreak", "pagebreak", "linebreak", "break", "@", "relax", "hfill", "vfill", "displaystyle", "bf", "it", "rm", "sf", "em", "sc", "tt", "sl", "upshape", "itshape", "bfseries", "mdseries", "scshape", "rmfamily", "sffamily", "ttfamily", "selectfont", "frontmatter", "mainmatter", "backmatter", "vsEatCr", "hline", "toprule", "midrule", "bottomrule", "endfirsthead", "endhead", "endfoot", "endlastfoot", "null", "allowbreak", "nolinebreak", "FloatBarrier", "strut", "unskip", "ignorespaces", "leavevmode", "onehalfspacing", "doublespacing", "singlespacing", "sloppy", "fussy", "global", "makeatletter", "makeatother", "printbibliography", "endinput", "qed", "qedhere", "noalign", "baselineskip", "localtableofcontents"]);
const DROP_WITH_ARG = new Set(["etocsettocstyle", "tikzset", "usetikzlibrary", "pgfutil@ifundefined", "pgfdeclarepatternformonly", "pgfdeclarepatterninherentlycolored", "vspace", "hspace", "label", "vsLabel", "bibliographystyle", "pagestyle", "thispagestyle", "color", "setlength", "addtolength", "setcounter", "addtocounter", "stepcounter", "refstepcounter", "addcontentsline", "keywords", "doi", "date", "thanks", "newline", "fontsize", "linespread", "renewcommand", "newcommand", "providecommand", "def", "hypersetup", "captionsetup", "setcitestyle", "theoremstyle", "newtheorem", "numberwithin", "graphicspath", "pdfbookmark", "phantomsection", "cline", "cmidrule", "arrayrulecolor", "rowcolor", "cellcolor", "columncolor", "vskip", "hskip", "kern", "rule", "enlargethispage", "nocite", "usetikzlibrary", "JEL", "MSC", "acks", "address", "email", "affiliation", "institute", "corref", "tnoteref", "fnref", "DeclareMathOperator", "newenvironment", "renewenvironment", "pagenumbering", "psfrag"]);
/** A TeX dimension: a number and its unit, or a length register with its factor (`-.5\baselineskip`). */
const DIMEN = String.raw`-?\s*(?:[\d.]+\s*(?:true\s*)?(?:pt|em|ex|in|cm|mm|bp|sp|pc|dd|cc|mu|fil+)(?![A-Za-z])|[\d.]*\s*\\[A-Za-z@]+)`;
/** The glue after `\vskip`, `\hskip`, `\kern`: a dimension, then its stretch and shrink. */
const GLUE = new RegExp(String.raw`^\s*=?\s*${DIMEN}(?:\s*plus\s*${DIMEN})?(?:\s*minus\s*${DIMEN})?`);
/** A rule's specification after `\vrule`, `\hrule`: its keywords and dimensions, in any order. */
const RULE_SPEC = new RegExp(String.raw`^(?:\s*(?:width|height|depth)\s*${DIMEN})*`);
/** Wrappers: drop the size / position arguments, keep the text. name → number of mandatory groups. */
const WRAPPERS: Record<string, number> = { shortstack: 1, subtable: 1, natexlab: 1, afterpage: 1, subfigure: 1, multirow: 3, putbib: 0, resizebox: 3, scalebox: 2, makebox: 1, parbox: 2, framebox: 1, fbox: 1, mbox: 1, text: 1, textrm: 1, textsf: 1, textnormal: 1, textup: 1, textmd: 1, hbox: 1, vbox: 1, raisebox: 2, centerline: 1, uppercase: 1, MakeUppercase: 1, lowercase: 1, MakeLowercase: 1, hyperref: 1, hyperlink: 2, hypertarget: 2, texorpdfstring: 2, subfloat: 1, subcaptionbox: 2, boxed: 1, colorbox: 2, fcolorbox: 3, smash: 1, footnotetext: 1 };
/** An annotation block longer than this is shown one sentence to a line. */
const SENTENCE_LAYOUT_MIN = 450;
const ABBREV = /(?:\b(?:e\.g|i\.e|cf|resp|Eq|Eqs|Fig|Sec|Thm|Prop|Cor|Def|vs|et al|a\.s|w\.r\.t|[A-Z])\.)$/;

/** A display the annotated paper set at `i` (`annotate_tex.ts`: `\vsFit{…}`, `\vsDisplay{…}`, `\vsFitIn{width}{…}`): its formula and where it ends. */
function displayMacro(tex: string, i: number): { body: string; end: number } | null {
  const m = /^\\vs(FitIn|Fit|Display)(?=\s*\{)/.exec(tex.slice(i, i + 12));
  if (!m) return null;
  const a = arg(tex, i + m[0].length);
  return m[1] === "FitIn" ? arg(tex, a.end) : a;
}
/** Does a display's formula close a sentence: its last character, before the ends of its inner environments, is a full stop. */
const endsSentence = (body: string): boolean => /\.\s*(?:\\end\{[A-Za-z*]+\}\s*)*$/.test(body);

/**
 * The sentences of a TeX passage, in order and verbatim (joined by a space they give the passage
 * back up to spacing): split after a full stop that ends a sentence — outside mathematics, braces
 * and environments (a list is one piece), not after an abbreviation or an initial, and before a
 * capital, a command or a display — and after a display (`\\]`, or one the annotated paper set: `displayMacro`)
 * that itself ends with a full stop. Pure.
 */
export function texSentences(tex: string): string[] {
  const out: string[] = [];
  let from = 0, depth = 0, inline = false, display = 0;
  const cut = (at: number): void => { const t = tex.slice(from, at).trim(); if (t) out.push(t); from = at; };
  for (let i = 0; i < tex.length; i++) {
    const c = tex[i]!;
    if (c === "\\") {
      const two = tex.slice(i, i + 2);
      if (two === "\\[") { display++; i++; continue; }
      if (two === "\\(") { inline = true; i++; continue; }
      if (two === "\\)") { inline = false; i++; continue; }
      if (two === "\\]") {
        display = Math.max(0, display - 1); i++;
        // a display closing a sentence: its last character is a full stop
        if (display === 0 && endsSentence(tex.slice(from, i - 1)) && /^\s+(?=[A-Z\\])/.test(tex.slice(i + 1))) cut(i + 1);
        continue;
      }
      const fit = inline || display ? null : displayMacro(tex, i);
      if (fit) {
        if (depth === 0 && endsSentence(fit.body) && /^\s+(?=[A-Z\\])/.test(tex.slice(fit.end))) cut(fit.end);
        i = fit.end - 1;
        continue;
      }
      const env = /^\\(begin|end)\{(equation\*?|align\*?|gather\*?|multline\*?|eqnarray\*?|displaymath)\}/.exec(tex.slice(i));
      if (env) { display = Math.max(0, display + (env[1] === "begin" ? 1 : -1)); i += env[0].length - 1; continue; }
      // any other environment (a list, a case split) is one piece: a cut inside it would open it in one line and close it in another
      const block = inline || display ? null : /^\\(begin|end)\{[A-Za-z]+\*?\}/.exec(tex.slice(i, i + 40));
      if (block) {
        depth = Math.max(0, depth + (block[1] === "begin" ? 1 : -1));
        const end = i + block[0].length;
        if (block[1] === "end" && depth === 0 && endsSentence(tex.slice(from, i)) && /^\s+(?=[A-Z\\])/.test(tex.slice(end))) cut(end);
        i = end - 1;
        continue;
      }
      i++; // an escaped character or the start of a command name
      continue;
    }
    if (c === "$") { if (tex[i + 1] === "$") { display = display ? 0 : 1; i++; } else if (!display) inline = !inline; continue; }
    if (inline || display) continue;
    if (c === "{") depth++;
    else if (c === "}") depth = Math.max(0, depth - 1);
    else if (c === "." && depth === 0 && /^\s+(?:[A-Z]|\\(?!ref|eqref|cite)[A-Za-z]|\$)/.test(tex.slice(i + 1)) && !ABBREV.test(tex.slice(Math.max(from, i - 8), i + 1))) cut(i + 1);
  }
  cut(tex.length);
  return out;
}

/**
 * The sentences of a statement grouped as a reader lists them: the assumptions (every sentence up to
 * a "Then …"), the conclusion (that sentence and those after it, up to the next "Suppose …"), and a
 * complete "If …, then …" sentence on its own. Order and wording are the text's. Pure.
 */
export function sentenceGroups(sents: readonly string[]): Array<{ kind: "hyp" | "concl" | "claim"; items: string[] }> {
  const out: Array<{ kind: "hyp" | "concl" | "claim"; items: string[] }> = [];
  let state: "hyp" | "concl" = "hyp";
  for (const t of sents) {
    const then = /^\s*(?:Then|Therefore|Consequently|Hence)\b/.test(t);
    const claim = !then && /^\s*If\b[\s\S]*\bthen\b/.test(t);
    if (claim) { out.push({ kind: "claim", items: [t] }); state = "hyp"; continue; }
    if (then) state = "concl";
    else if (state === "concl" && /^\s*(?:Suppose|Assume|Let|Require|Further suppose)\b/.test(t)) state = "hyp";
    const last = out.at(-1);
    if (last && last.kind === state && !(then && last.items.length > 0)) last.items.push(t);
    else out.push({ kind: state, items: [t] });
  }
  return out;
}

/** A formula of a TeX text: where it stands, its source, whether it is displayed, and the brace depth it stands at. */
interface MathChunk { from: number; to: number; body: string; display: boolean; depth: number }
const MATH_AT = /\$\$([\s\S]*?)\$\$|\$((?:\\[\s\S]|[^$\\])*)\$|\\\[([\s\S]*?)\\\]|\\\(([\s\S]*?)\\\)|\\begin\{(equation\*?|align\*?|gather\*?|multline\*?|eqnarray\*?|displaymath)\}([\s\S]*?)\\end\{\5\}/y;
/** The formulas of a TeX text, in order (a display macro of the annotated paper is one). Pure. */
function mathChunks(tex: string): MathChunk[] {
  const out: MathChunk[] = [];
  let depth = 0;
  for (let i = 0; i < tex.length; i++) {
    const c = tex[i]!;
    if (c === "{") depth++;
    else if (c === "}") depth = Math.max(0, depth - 1);
    if (c !== "$" && c !== "\\") continue;
    const fit = c === "\\" ? displayMacro(tex, i) : null;
    if (fit) { out.push({ from: i, to: fit.end, body: fit.body, display: true, depth }); i = fit.end - 1; continue; }
    MATH_AT.lastIndex = i;
    const m = MATH_AT.exec(tex);
    if (m) { out.push({ from: i, to: i + m[0].length, body: m[1] ?? m[2] ?? m[3] ?? m[4] ?? m[6] ?? "", display: m[2] === undefined && m[4] === undefined, depth }); i += m[0].length - 1; }
    else if (c === "\\") i++;
  }
  return out;
}

/**
 * Every word `sentencePart` reads a sentence's display group from — the whole list, in one place.
 * `define`: what opens a sentence that only introduces notation, after at most one phrase opened by a
 * `lead`; `link`: what ties the symbols such a verb names to what they stand for; `assume`: what
 * marks a hypothesis (it wins over every other word); `states`: a verb that says something OF a
 * symbol — a property, unless what follows only says what the symbol is (`names`); `step` with a
 * `change` in the imperative: a sentence that tells the reader to run a step of the method otherwise
 * than printed.
 */
const PART_WORDS = {
  define: "where|write|let|put|fix|define|denote|set|take|select|choose|here",
  lead: "for|with|in|on|at",
  link: "be the|be as in|be defined|be fixed|be given|denotes?|for|is the|are the|stands? for|depends? on",
  assume: "suppose|assum\\w*|holds?|holding|satisf\\w*|provided|requir\\w*|then|such that|must",
  states: "is|are|was|were|has|have",
  names: "the|defined|given|as in|fixed|denoted",
  step: "algorithms?|procedures?|steps?",
  change: "use|replace|read|compute",
} as const;
const PART_RE = {
  assume: new RegExp(`\\b(?:${PART_WORDS.assume})\\b`),
  opens: new RegExp(`^(?:(?:${PART_WORDS.lead})\\s+(?:[^,.;:]*,\\s*|(?:[^\\s,.;:]+\\s+){0,5}))?(?:we\\s+)?(?:${PART_WORDS.define})\\b`),
  names: new RegExp(`\\b(?:${PART_WORDS.define})\\s+(?:[a-z-]+\\s+){0,3}\\$`, "g"),
  link: new RegExp(`^(?:\\s*(?:,\\s*and|,|and)\\s*\\$)*\\s*(?:${PART_WORDS.link})\\b`),
  rule: new RegExp(`\\b(?:${PART_WORDS.define})\\s+[^$,.;:]*?\\bto\\b`),
  states: new RegExp(`\\b(?:${PART_WORDS.states})\\b(?!\\s+(?:${PART_WORDS.names})\\b)`),
  step: new RegExp(`\\b(?:${PART_WORDS.step})\\b`),
  change: new RegExp(`(?:^|[,;:]\\s*|\\band\\s+)(?:${PART_WORDS.change})\\b`),
};
const DEFINES = /=|\\(?:in|coloneqq|equiv|triangleq)(?![A-Za-z])/;
const ORDERS = /[<>]|\\(?:leq?|geq?|leqslant|geqslant|ll|gg|lesssim|gtrsim|neq?|to|rightarrow|longrightarrow)(?![A-Za-z])/;
/**
 * What a formula says at its top level (outside its groups, brackets and cases), part by part (a
 * comma, a row or a `\quad` parts them): `defines` — some part has an `=` or an `∈`; `imposes` — a
 * part goes on from that sign to an order relation ("κ = 1 − αγ > 0": a condition, not only a name). Pure.
 */
function formulaForm(math: string): { defines: boolean; imposes: boolean } {
  let t = math.replace(/\\begin\{cases\}[\s\S]*?\\end\{cases\}/g, " ").replace(/\\\{/g, "(").replace(/\\\}/g, ")");
  for (let prev = ""; prev !== t;) { prev = t; t = t.replace(/\{[^{}]*\}|\([^()]*\)|\[[^[\]]*\]/g, " "); }
  const from = t.split(/,|\\\\|\\q?quad(?![A-Za-z])/).map((p) => { const at = p.search(DEFINES); return at < 0 ? null : p.slice(at); }).filter((p) => p !== null);
  return { defines: from.length > 0, imposes: from.some((p) => ORDERS.test(p)) };
}

/**
 * The part of a statement one of its sentences before the conclusion is DRAWN with, read off the
 * sentence's own form: `setting` — it only introduces notation or fixes objects; `modify` — it tells
 * the reader to run a step of the method otherwise than printed (drawn in the setting);
 * `hyp` — everything else. Conservative on purpose: a sentence is `setting` only when a defining verb
 * governs it (`PART_WORDS.define`, after at most one leading phrase), that verb names a symbol by an
 * `=` / `∈` or a link ("be the", "for", …) or fixes a convention ("define … to be …"), no word of a
 * hypothesis (`PART_WORDS.assume`) and no instruction (`change`) stands in it, it says no property of
 * a symbol (`states`: "… are errors that are decreasing") and none of its formulas imposes a
 * relation (`formulaForm`); a sentence that both defines and assumes is therefore `hyp`,
 * and `modify` asks for a named step (`step`) and that instruction. A definition drawn
 * among the assumptions is how the page read before; a hypothesis drawn as setting is the harm.
 * This is a wording heuristic, which the pipeline never uses to block or grade a model's text: it
 * only picks the group of lines a sentence is drawn with — no sentence is moved, hidden, reworded or
 * judged by it. Pure.
 */
export function sentencePart(tex: string): "setting" | "modify" | "hyp" {
  const math = mathChunks(tex);
  let prose = "", at = 0;
  for (const m of math) { prose += `${tex.slice(at, m.from)} $ `; at = m.to; }
  prose = (prose + tex.slice(at)).replace(/\\(?:[A-Za-z]*ref|cite[A-Za-z]*|label)\*?\s*(?:\[[^\]]*\]\s*)*\{[^{}]*\}/g, " ").replace(/\\[A-Za-z]+\*?|[{}~]|\\./g, " ").replace(/\s+/g, " ").trim().toLowerCase();
  const forms = math.map((m) => formulaForm(m.body));
  // a word of a hypothesis, a relation imposed, or a property said of a symbol ("where … are errors
  // that are decreasing"): an assumption, in whatever sentence it rides
  if (PART_RE.assume.test(prose) || PART_RE.states.test(prose) || forms.some((f) => f.imposes)) return "hyp";
  // an instruction on the method is no notation: of a named step it is a change of the algorithm
  if (PART_RE.change.test(prose)) return PART_RE.step.test(prose) ? "modify" : "hyp";
  if (!PART_RE.opens.test(prose)) return "hyp";
  if (PART_RE.rule.test(prose)) return "setting";
  for (const m of prose.matchAll(PART_RE.names)) {
    const end = m.index + m[0].length;
    if (forms[prose.slice(0, end).split("$").length - 2]?.defines || PART_RE.link.test(prose.slice(end))) return "setting";
  }
  return "hyp";
}

/** One sentence of a statement as the page lays it out: its part, and the group of lines it is set
 *  in (`run`: consecutive sentences of one part, counted through the statement). */
export interface StatementSentence { part: "setting" | "modify" | "hyp" | "concl" | "claim"; run: number; text: string }
/**
 * A statement's sentences, each with its part — in the TEXT's order, every sentence once: the page
 * never moves, drops or rewords one (a definition set above the sentence that introduces what it
 * uses reads wrong, and no reading of a sentence's form can rule that out). `sentenceGroups` tells
 * the conclusions from what stands before them, `sentencePart` the setting from the assumptions
 * there; a sentence that runs a step of the method otherwise is of the setting. Pure.
 */
export function statementParts(sents: readonly string[]): StatementSentence[] {
  const out: StatementSentence[] = [];
  const kind = (p: StatementSentence["part"]): string => (p === "modify" ? "setting" : p);
  for (const g of sentenceGroups(sents)) for (const text of g.items) {
    const part = g.kind === "hyp" ? sentencePart(text) : g.kind, last = out.at(-1);
    out.push({ part, run: !last ? 0 : last.run + Number(part === "claim" || kind(part) !== kind(last.part)), text });
  }
  return out;
}
/** A displayed definition of the setting longer than this (rows of its displays, or their source) is
 *  folded: a very long one only — what a reader needs for the conclusion stays in sight. */
const FOLD_ROWS = 8;
const FOLD_CHARS = 900;

/** `stmt`: the block is a statement — its sentences are laid out as setting, assumptions and conclusion; a
 *  proof or a step is an argument, laid out one sentence to a line with no such headings. */
const ANNOTATION_BLOCKS: Record<string, { cls: string; tag: string; stmt?: true }> = {
  vsOriginal: { cls: "rv del", tag: "Original", stmt: true },
  vsStep: { cls: "rv del", tag: "Original step" },
  vsCorrected: { cls: "rv ins", tag: "Revised", stmt: true },
  vsClarified: { cls: "rv ins", tag: "Clarified statement", stmt: true },
  vsCorrectedStep: { cls: "rv ins", tag: "Revised step" },
  vsProof: { cls: "rv ins", tag: "Revised proof (confirmed)" },
  vsProposed: { cls: "rv ins pending", tag: "Proposed revision — awaiting a ruling", stmt: true },
  vsProposedProof: { cls: "rv ins pending", tag: "Proof of the proposed statement" },
  vsProposedStep: { cls: "rv ins pending", tag: "Revised (for the proposed statement)" },
};
/** The macros of a block a repair split off a result (`annotate_tex.ts` `SPLIT_MACROS`), and what each
 * says of it: its kind and whether it awaits the owner. An annotated paper written before the kinds
 * were told apart uses the corollary macros alone, and renders as it did. */
/** Brackets the index of an umbrella sentence in the rendered text until its blocks are known. */
const UMBRELLA_MARK = "\u0001";
const SPLIT_BLOCKS: Record<string, { kind: "corollary" | "proposition"; pending: boolean }> = {
  vsCorollary: { kind: "corollary", pending: false },
  vsProposedCorollary: { kind: "corollary", pending: true },
  vsSplitProposition: { kind: "proposition", pending: false },
  vsProposedSplitProposition: { kind: "proposition", pending: true },
};
/** Where a corollary block's statement ends and its proof begins (`annotate_tex.ts` `COROLLARY_PROOF`). */
const COROLLARY_PROOF = ["\\vsLine\\textit{Proof.}"];
const ANNOTATION_NOTES: Record<string, { kind: string; label: string }> = {
  vsNote: { kind: "note", label: "PaperFormalizer" },
  vsReading: { kind: "reading", label: "Clarification" },
  vsReadingOwner: { kind: "reading-owner", label: "Clarification (author)" },
  vsCondition: { kind: "condition", label: "Bookkeeping condition" },
  vsConditionOwner: { kind: "condition", label: "Bookkeeping condition" },
  vsDetail: { kind: "detail", label: "Proof detail" },
  vsRewind: { kind: "rewind", label: "Proposed correction — awaiting a ruling" },
  vsCap: { kind: "cap", label: "Revision not settled — awaiting a ruling" },
};
/** Names of common theorem-like environments a class defines without a preamble line. */
const COMMON_THEOREMS: Record<string, string> = {
  theorem: "Theorem", thm: "Theorem", lemma: "Lemma", lem: "Lemma", proposition: "Proposition", prop: "Proposition",
  corollary: "Corollary", cor: "Corollary", coro: "Corollary", definition: "Definition", defn: "Definition", defi: "Definition",
  assumption: "Assumption", assump: "Assumption", ass: "Assumption", condition: "Condition", cond: "Condition",
  remark: "Remark", rem: "Remark", example: "Example", ex: "Example", conjecture: "Conjecture", claim: "Claim", fact: "Fact",
  hypothesis: "Hypothesis", hyp: "Hypothesis", notation: "Notation", observation: "Observation", problem: "Problem",
};
const IMAGE_EXT = [".png", ".jpg", ".jpeg", ".gif", ".svg", ".webp"];
const FIG_EXT = ["", ".pdf", ".png", ".jpg", ".jpeg", ".svg", ".gif", ".eps", ".ps"];

/** Macro and user-environment expansions one render may perform: a self-referencing
 * `\newcommand` otherwise grows without bound (depth alone does not cap `\foo\foo\foo`). */
const EXPANSION_BUDGET = 20_000;

interface Ctx {
  tikz: { url: string; page: Map<string, number> } | null;
  pass: 1 | 2;
  /** Expansions performed so far (see `EXPANSION_BUDGET`). */
  expansions: number;
  pre: Preamble;
  aux: AuxIndex;
  own: Record<string, string>;
  refNames: Record<string, string>;
  /** A label a heading carries (`\section{…}\label{…}`): "section", or "appendix" after `\appendix`. */
  refKinds: Record<string, "section" | "appendix">;
  counters: Record<string, number>;
  sec: number[];
  appendix: boolean;
  target: string;
  toc: RenderedPaper["toc"];
  comments: PaperComment[];
  envs: PaperEnv[];
  anchors: Record<string, string>;
  readings: Record<string, string>;
  /** The pinned readings by their text without white space, the longest first. */
  pinned: Array<{ node: string; key: string; labels: string[] }>;
  envStack: Array<string | null>;
  /** Blocks (corollaries and propositions) split off a result so far, by the result as the block names it: their running number. */
  splits: Record<string, number>;
  /** The umbrella sentences met so far (a corrected statement that is `UMBRELLA_STATEMENT`): the
   *  headings of the proposition blocks after each — the sentence is written from them once the page
   *  is rendered (`UMBRELLA_MARK`). `open`: the one whose blocks are being read, and their result. */
  umbrellas: { names: string[][]; open: { idx: number; of: string | null } | null };
  splitKinds: Record<string, "corollary" | "proposition">;
  lastEnv: string | null;
  /** Where the environment `lastEnv` names ends, in the text being rendered. */
  lastEnvEnd: { s: string; at: number } | null;
  marks: number;
  footnotes: number;
  mathCache: Map<string, string>;
  kinds: Record<string, string>;
  assets: Set<string>;
  assetsLower: Map<string, string>;
  assetBase: string;
  health: RenderHealth;
  depth: number;
  mathMacros: Record<string, string>;
  mathOverrides: Record<string, string>;
  /** etoolbox toggles at the point of the text being rendered (the preamble's, then the body's settings in order). */
  toggles: Record<string, boolean>;
  /** MathJax for this paper's macros, built on the first formula KaTeX refuses. */
  mathjax: () => (tex: string, display: boolean) => string;
}

/**
 * The `\mathpalette` independence idiom (`\mathpalette{\independenT}{\perp}` with a helper that overlays its
 * argument twice, `\rlap{$#1#2$}…{#1#2}`) as KaTeX's ⫫, or its negation when `\not` / `\centernot` occurs in the
 * body or the helper; null for any other `\mathpalette` body (a helper that does not overlay, or one not defined).
 */
function mathpaletteIndependence(body: string, macros: Record<string, string>): string | null {
  if (!/\\mathpalette/.test(body) || !/\\perp(?![A-Za-z])/.test(body)) return null;
  const name = /\\mathpalette\s*\{?\s*(?:\\protect\s*)?(\\[A-Za-z@]+)/.exec(body)?.[1];
  const helper = name ? macros[name] : undefined;
  if (!helper || (helper.match(/#1\s*#2/g) ?? []).length < 2) return null;
  const not = /\\(?:center)?not(?![A-Za-z])/;
  return not.test(body) || not.test(helper) ? "\\not\\perp\\!\\!\\!\\perp" : "\\perp\\!\\!\\!\\perp";
}

/**
 * The author's math macros made KaTeX-safe: box commands KaTeX lacks are unwrapped, `$` inside a
 * math macro dropped; the independence idioms (a rotated ⊨, or `\mathpalette` overlaying two ⊥, and its
 * negation) become the standard ⫫. The LaTeX kernel's `\sp`/`\sb` (`\let\sp=^`, `\let\sb=_`) and the italic
 * correction `\/` (a spacing hint, empty here), which KaTeX lacks, are supplied unless the author redefines them. Pure.
 */
export function katexMacros(macros: Record<string, string>): Record<string, string> {
  const out: Record<string, string> = { "\\sp": "^", "\\sb": "_", "\\/": "" };
  for (const [k, v] of Object.entries(macros)) {
    let b = v;
    if (/\\rotatebox/.test(b) && /\\models/.test(b)) { out[k] = "\\perp\\!\\!\\!\\perp"; continue; }
    const indep = mathpaletteIndependence(b, macros);
    if (indep) { out[k] = indep; continue; }
    for (let guard = 0; guard < 4 && /\\(rotatebox|scalebox|raisebox|resizebox|mbox|hbox|ensuremath)\b/.test(b); guard++) {
      b = b.replace(/\\(?:rotatebox|scalebox|raisebox)\s*(?:\[[^\]]*\])?\s*\{[^{}]*\}\s*/g, "")
        .replace(/\\resizebox\s*\{[^{}]*\}\s*\{[^{}]*\}\s*/g, "")
        .replace(/\\(?:mbox|hbox|ensuremath)\s*(?=\{)/g, "");
    }
    out[k] = b.replace(/(^|[^\\])\$/g, "$1");
  }
  return out;
}

const KATEX_KNOWN = new Map<string, boolean>();
/** Whether KaTeX renders the bare command `name` (`\\lesssim`) by itself. */
function knownToKatex(name: string): boolean {
  let ok = KATEX_KNOWN.get(name);
  if (ok === undefined) {
    try { katex.renderToString(name, { throwOnError: true, strict: "ignore" }); ok = true; } catch { ok = false; }
    KATEX_KNOWN.set(name, ok);
  }
  return ok;
}

/** LaTeX commands KaTeX (and some MathJax) lacks, in terms both read. */
const KATEX_GAPS: Record<string, string> = { "\\xspace": "", "\\Vec": "\\vec{#1}", "\\mbox": "\\text{#1}", "\\hbox": "\\text{#1}", "\\makebox": "\\text{#1}", "\\normalfont": "", "\\offinterlineskip": "", "\\strut": "", "\\mathstrut": "\\vphantom{(}", "\\textsc": "\\text{#1}", "\\textsl": "\\textit{#1}", "\\protect": "", "\\hfill": "\\quad", "\\mathbbm": "\\mathbb{#1}", "\\mathds": "\\mathbb{#1}" };

/** KaTeX first; what it refuses, MathJax; what neither reads is shown as source and recorded. */
function renderMath(ctx: Ctx, tex00: string, display: boolean): string {
  if (ctx.pass === 1) return "";
  // an anchor whose source text starts inside the formula stands before it
  let anchors = "";
  const bare = tex00.replace(/\\tcAnchor\*?\s*\{[^{}]*\}/g, (m) => { anchors += render(ctx, m, true); return ""; });
  if (anchors) return anchors + renderMath(ctx, bare, display);
  const src = tex00.trim();
  const tex0 = ctx.mathOverrides[src] ?? tex00;
  // LyX writes `\text{\ensuremath{X}}`: it is X; KaTeX's array preamble takes no `@{…}`/`!{…}`/`>{…}`/`<{…}`
  // a label a correction keeps (`\vsLabel`, annotate_tex.ts) sets nothing
  const tex = tex0.replace(/\\vsLabel\s*\{[^{}]*\}/g, "").replace(/\\text\s*\{\s*\\ensuremath\s*\{((?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*)\}\s*\}/g, "$1")
    .replace(/\\begin\s*\{array\}\s*\{((?:[^{}]|\{[^{}]*\})*)\}/g, (_, spec: string) => `\\begin{array}{${spec.replace(/[@!<>]\s*\{[^{}]*\}/g, "")}}`)
    // a reference inside math (`\text{in Example~\ref{x}}`): its number, which KaTeX cannot look up, and
    // for \cref its name, as outside math
    .replace(/\\(eqref|ref|cref|Cref|autoref)\s*\{([^{}]*)\}/g, (_, cmd: string, l: string) => {
      const label = labelKey(l); const n = ctx.aux.labels[label] ?? ctx.own[label]; const t = n ? n : "??";
      const name = refName(ctx, cmd, label);
      return cmd === "eqref" ? `(${t})` : name ? `\\text{${name}}~${t}` : t;
    });
  const key = `${display ? "D" : "I"}${tex}`;
  const hit = ctx.mathCache.get(key);
  if (hit !== undefined) return hit;
  let out: string;
  try {
    out = katex.renderToString(tex, {
      displayMode: display, throwOnError: true, strict: "ignore", trust: false, output: "html",
      macros: { ...KATEX_GAPS, ...ctx.mathMacros, "\\label": "\\gobble", "\\gobble": "", "\\nonumber": "", "\\notag": "", "\\ensuremath": "#1" },
    });
  } catch {
    try {
      out = `<span class="mjx${display ? " mjx-d" : ""}">${ctx.mathjax()(tex, display)}</span>`;
      ctx.health.mathFallbacks++;
    } catch (err) {
      out = `<code class="tex-raw" title="neither KaTeX nor MathJax reads this formula">${esc(src)}</code>`;
      ctx.health.mathFailures.push({ tex: src, error: String((err as { message?: unknown })?.message ?? err), near: ctx.envStack.at(-1) ?? ctx.lastEnv ?? ctx.toc.at(-1)?.text ?? "" });
    }
  }
  ctx.mathCache.set(key, out);
  return out;
}

/** The next value of a LaTeX counter, with its parent's number in front when numbered within one. */
function nextNumber(ctx: Ctx, counter: string): string {
  ctx.counters[counter] = (ctx.counters[counter] ?? 0) + 1;
  const parent = ctx.pre.numberWithin[counter];
  const n = String(ctx.counters[counter]);
  if (parent === "section" || parent === "chapter") return `${sectionLabel(ctx, 1)}.${n}`;
  if (parent === "subsection") return `${sectionLabel(ctx, 2)}.${n}`;
  return n;
}
function sectionLabel(ctx: Ctx, level: number): string {
  const first = ctx.appendix ? String.fromCharCode(64 + Math.max(1, ctx.sec[0] ?? 1)) : String(ctx.sec[0] ?? 0);
  return [first, ...ctx.sec.slice(1, level).map((x) => String(x ?? 0))].join(".");
}

function citeText(ctx: Ctx, cmd: string, keys: string, opt: string | null): string {
  const textual = /^(citet|Citet|citeauthor|citealt)$/.test(cmd);
  const parts = keys.split(",").map((k) => k.trim()).filter(Boolean).map((k) => {
    const c = ctx.aux.cites[k];
    if (!c) return esc(k);
    if (c.author && c.year) return textual ? esc(cmd === "citeauthor" ? c.author : `${c.author} (${c.year})`) : esc(`${c.author}, ${c.year}`);
    return esc(c.num);
  });
  const body = parts.join("; ") + (opt ? `, ${esc(opt)}` : "");
  return textual ? `<span class="cite">${body}</span>` : `<span class="cite">[${body}]</span>`;
}

/** The name `\cref` / `\Cref` / `\autoref` gives `label`: its environment's (`refNames`), else a heading's
 *  ("Section", "Appendix"; lower case for `\cref` without cleveref's `capitalize`, hyperref's for `\autoref`). */
function refName(ctx: Ctx, cmd: string, label: string): string | null {
  if (!["cref", "Cref", "autoref"].includes(cmd)) return null;
  const own = ctx.refNames[label];
  if (own) return own;
  const kind = ctx.refKinds[label];
  if (!kind) return null;
  const word = kind === "appendix" ? "Appendix" : "Section";
  return cmd === "Cref" || (cmd === "cref" && ctx.pre.crefCapital) || (cmd === "autoref" && kind === "appendix") ? word : word.toLowerCase();
}

function refText(ctx: Ctx, cmd: string, ref: string): string {
  const label = labelKey(ref);
  const n = ctx.aux.labels[label] ?? ctx.own[label];
  if (ctx.pass === 2 && (n === undefined || n === "") && !ctx.health.unresolvedRefs.includes(label)) ctx.health.unresolvedRefs.push(label);
  const t = n !== undefined && n !== "" ? esc(n) : "??";
  const name = refName(ctx, cmd, label);
  return `<a class="ref" href="#lbl-${esc(slug(label))}">${cmd === "eqref" ? `(${t})` : name ? `${esc(name)} ${t}` : t}</a>`;
}

/** An `algorithm` float: numbered, its caption on top, its pseudocode as lines (algorithmic or algorithm2e). */
function algorithmFloat(ctx: Ctx, body: string, inline: boolean): string {
  let b = body;
  // `[H]` / `[htbp]` place the float; anything else there is its title (a theorem-like
  // algorithm the page could not tell from its preamble)
  let caption = "";
  const o = optArg(b, 0);
  if (o && /^\s*\[/.test(b)) { if (!/^[!htbpH]+$/.test(o.body.trim())) caption = o.body; b = b.slice(o.end); }
  const takeCaption = (t: string): { caption: string | null; rest: string } => {
    const cm = /\\caption\s*(?:\[[^\]]*\])?\s*(?=\{)/.exec(t);
    if (!cm) return { caption: null, rest: t };
    const g = arg(t, cm.index + cm[0].length);
    return { caption: g.body, rest: t.slice(0, cm.index) + t.slice(g.end) };
  };
  const num = nextNumber(ctx, "algorithm");
  const saved = ctx.target; ctx.target = num;
  // labels first: an algorithm2e body is read line by line, not through `render`
  let anchors = "";
  // (algorithm2e or not is the float's: a block of it alone may show too little to tell)
  let uncaptioned = b;
  for (let t = takeCaption(uncaptioned); t.caption !== null; t = takeCaption(uncaptioned)) uncaptioned = t.rest;
  const a2e = !/\\begin\s*\{algorithmic\}/.test(uncaptioned) && /\\;|\\Kw[A-Z]|\\SetAlgo|\\(?:For|ForEach|While|If|eIf)\s*\{[^{}]*\}\s*\{/.test(uncaptioned);
  const pseudocode = (t0: string): string => {
    const t = t0.replace(/\\label\s*\{[^}]*\}/g, (l) => { anchors += render(ctx, l, true); return ""; });
    return a2e ? renderAlgorithm2e(t, (x) => render(ctx, x, true)) : render(ctx, t, true);
  };
  // the annotated paper's printed and corrected pseudocode (`\vsOriginal{…} \vsCorrected{…}`, the
  // float holding nothing else but its caption and label): each block is a whole algorithm body, drawn
  // inside its block with its own caption. A step's blocks, inside the pseudocode, stay in their line.
  const blocks: string[] = [];
  const whole = (() => {
    const found: Array<{ name: string; start: number; end: number }> = [];
    let rest = "", from = 0;
    for (const m of b.matchAll(/\\(vs[A-Za-z]+)\s*(?=\{)/g)) {
      const note = m[1]! in ANNOTATION_NOTES;
      if (m.index! < from || !(note || ANNOTATION_BLOCKS[m[1]!]?.stmt)) continue;
      const a = arg(b, m.index! + m[0].length);
      rest += b.slice(from, m.index);
      // (a note beside the blocks is drawn after them, as anywhere)
      if (!note) found.push({ name: m[1]!, start: m.index!, end: a.end });
      from = a.end;
    }
    rest += b.slice(from);
    const bare = takeCaption(rest).rest.replace(/\\label\s*\{[^}]*\}|\\centering\b|\\(?:small|footnotesize|scriptsize)\b|\s+/g, "");
    return found.length && !bare ? found : [];
  })();
  for (const w of whole) {
    const spec = ANNOTATION_BLOCKS[w.name]!;
    const own = takeCaption(arg(b, b.indexOf("{", w.start + w.name.length + 1)).body);
    blocks.push(`<div class="${spec.cls}" data-mark="${++ctx.marks}"><span class="rv-tag">${esc(spec.tag)}</span>${own.caption !== null ? `<div class="alg-cap">${render(ctx, own.caption, true)}</div>` : ""}${pseudocode(own.rest)}</div>`);
  }
  for (const w of [...whole].reverse()) b = b.slice(0, w.start) + "\u0008" + b.slice(w.end);
  const top = takeCaption(b);
  if (top.caption !== null) caption = top.caption;
  b = top.rest;
  const inner = blocks.length ? b.split("\u0008").map((part, n) => (n ? blocks[n - 1]! : "") + (part.trim() ? render(ctx, part, true) : "")).join("") : pseudocode(b);
  ctx.target = saved;
  const html = `<figure class="alg" id="alg-${esc(num.replace(/\./g, "-"))}">${anchors}<figcaption><b>Algorithm ${esc(num)}.</b> ${render(ctx, caption, true)}</figcaption>${inner}</figure>`;
  return inline ? html : `</div>${html}<div class="p">`;
}

/** A math environment, numbered the way LaTeX numbers it (line by line for align / eqnarray). */
function mathEnv(ctx: Ctx, env: string, body: string): string {
  const base = env.replace("*", "");
  const numbered = !env.endsWith("*") && !["displaymath", "math"].includes(base);
  const anchors: string[] = [];
  // a label in a display with no number (`equation*`) takes the number of what encloses it, as in LaTeX
  const takeLabels = (s: string, num: string | null) => s.replace(/\\label\{([^}]+)\}/g, (_m, l: string) => {
    if (ctx.pass === 1) ctx.own[labelKey(l)] = num ?? ctx.target;
    anchors.push(`<a id="lbl-${esc(slug(l.trim()))}"></a>`);
    return "";
  });
  const unNumbered = (s: string) => /\\(nonumber|notag)\b/.test(s) || /\\tag\*?\s*\{/.test(s);
  // `\tag{X}` numbers its line X, shown "(X)" (`\tag*{X}`: "X"), a `\notag` beside it notwithstanding;
  // the number column shows it (KaTeX takes no `\tag` inside `aligned`)
  const tagOf = (s: string) => { const t = /\\tag(\*?)\s*\{([^{}]*)\}/.exec(s); return t ? { num: t[2]!.trim(), shown: t[1] ? t[2]!.trim() : `(${t[2]!.trim()})` } : null; };
  const untag = (s: string) => s.replace(/\\tag\*?\s*\{[^{}]*\}/g, "");
  // a compiled .aux numbers a labelled line exactly: it wins over the counter
  const auxNum = (s: string, num: string | null) => { const l = /\\label\{([^}]+)\}/.exec(s)?.[1]; return (l && ctx.aux.labels[labelKey(l)]) || num; };
  if (base === "equation" || base === "displaymath" || base === "math" || base === "dmath" || base === "multline") {
    const tag = tagOf(body);
    const num = tag ? tag.num : numbered && !unNumbered(body) ? auxNum(body, nextNumber(ctx, "equation")) : null;
    const tex = untag(takeLabels(body, num));
    const inner = base === "multline" ? `\\begin{gathered}${tex}\\end{gathered}` : tex;
    const shown = tag ? render(ctx, tag.shown, true) : num ? `(${esc(num)})` : "";
    return `<div class="eq">${anchors.join("")}${renderMath(ctx, inner, true)}${shown ? `<span class="eqn">${shown}</span>` : ""}</div>`;
  }
  let inner = body;
  let cols = "";
  if (base === "alignat") { const t = inner.trimStart(); const g = group(t, 0); if (g) { cols = g.body; inner = t.slice(g.end); } }
  const rows = splitTop(inner, "\\\\").filter((r, i, a) => r.trim() !== "" || i < a.length - 1);
  const tags = rows.map(tagOf);
  const nums = rows.map((r, i) => tags[i]?.num ?? (numbered && !unNumbered(r) && r.trim() !== "" ? auxNum(r, nextNumber(ctx, "equation")) : null));
  const shown = (i: number) => (tags[i] ? `\\text{${tags[i]!.shown}}` : nums[i] ? `\\text{(${nums[i]})}` : "");
  // a label on an unnumbered line takes the number the display shows (the next one, else the last)
  const labelNum = (i: number) => nums[i] ?? nums.slice(i + 1).find(Boolean) ?? [...nums.slice(0, i)].reverse().find(Boolean) ?? null;
  const texRows = rows.map((r, i) => untag(takeLabels(r, labelNum(i))));
  const anyNum = nums.some(Boolean);
  if (base === "eqnarray") {
    const tr = texRows.map((r, i) => {
      const cells = splitTop(r, "&").length;
      const pad = "&".repeat(Math.max(0, 3 - cells));
      return `${r}${anyNum ? `${pad}&\\qquad ${shown(i)}` : ""}`;
    });
    return `<div class="eq">${anchors.join("")}${renderMath(ctx, `\\begin{array}{rcl${anyNum ? "r" : ""}}${tr.join("\\\\")}\\end{array}`, true)}</div>`;
  }
  const open = base === "gather" && !anyNum ? "\\begin{gathered}" : base === "alignat" ? `\\begin{alignedat}{${cols || "2"}}` : "\\begin{aligned}";
  const close = base === "gather" && !anyNum ? "\\end{gathered}" : base === "alignat" ? "\\end{alignedat}" : "\\end{aligned}";
  if (!anyNum) return `<div class="eq">${anchors.join("")}${renderMath(ctx, `${open}${texRows.join("\\\\")}${close}`, true)}</div>`;
  // one column of numbers to the right of the rows
  const width = Math.max(...texRows.map((r) => splitTop(r, "&").length));
  const padTo = width % 2 === 0 ? width : width + 1;
  const tr = texRows.map((r, i) => `${base === "gather" ? `&${r}` : r}${"&".repeat(Math.max(1, padTo - splitTop(base === "gather" ? `&${r}` : r, "&").length + 1))}\\qquad ${shown(i)}`);
  return `<div class="eq">${anchors.join("")}${renderMath(ctx, `${open}${tr.join("\\\\")}${close}`, true)}</div>`;
}

function headingNumber(ctx: Ctx, level: number): string {
  ctx.sec.length = Math.max(ctx.sec.length, level);
  ctx.sec[level - 1] = (ctx.sec[level - 1] ?? 0) + 1;
  for (let k = level; k < ctx.sec.length; k++) ctx.sec[k] = 0;
  const name = level === 1 ? "section" : level === 2 ? "subsection" : "subsubsection";
  for (const [c, parent] of Object.entries(ctx.pre.numberWithin)) if (parent === name || (level === 1 && parent === "chapter")) ctx.counters[c] = 0;
  return sectionLabel(ctx, level);
}

/** Expand a user text macro with its arguments; null when `name` is not one. */
function expandMacro(ctx: Ctx, name: string, s: string, i: number): { text: string; end: number } | null {
  const def = ctx.pre.textMacros[`\\${name}`];
  if (!def || ctx.depth > 12 || ctx.expansions >= EXPANSION_BUDGET) return null;
  ctx.expansions++;
  let j = i;
  const args: string[] = [];
  if (def.dflt !== null) {
    const o = optArg(s, j);
    if (o) { args.push(o.body); j = o.end; } else args.push(def.dflt);
  }
  while (args.length < def.n) { const a = arg(s, j); args.push(a.body); j = a.end; }
  const text = def.body.replace(/#(\d)/g, (_m, d: string) => args[Number(d) - 1] ?? "");
  return { text, end: j };
}

function resolveAsset(ctx: Ctx, name: string): string | null {
  const n = name.trim().replace(/^\.\//, "").replace(/\\/g, "/");
  for (const dir of ["", ...ctx.pre.graphicsPath]) {
    for (const ext of FIG_EXT) {
      const p = `${dir}${n}${ext}`.replace(/\/\.\//g, "/");
      if (ctx.assets.has(p)) return p;
      const lower = ctx.assetsLower.get(p.toLowerCase());
      if (lower) return lower;
    }
  }
  return null;
}

function figureHTML(ctx: Ctx, opts: string, name: string): string {
  const p = resolveAsset(ctx, name);
  const width = /width\s*=\s*([\d.]*)\s*\\(?:textwidth|linewidth|columnwidth|hsize)/.exec(opts);
  const style = width ? ` style="width:${Math.min(100, Math.round(Number(width[1] || 1) * 100))}%"` : "";
  if (ctx.pass === 2) ctx.health.figures++;
  if (!p) {
    if (ctx.pass === 2) ctx.health.missingFigures.push(name.trim());
    return `<span class="omitted">Figure file not in the paper's folder: ${esc(name.trim())}</span>`;
  }
  const url = `${ctx.assetBase}/${p.split("/").map(encodeURIComponent).join("/")}`;
  const ext = p.slice(p.lastIndexOf(".")).toLowerCase();
  if (IMAGE_EXT.includes(ext)) return `<img class="fig" loading="lazy" decoding="async" src="${esc(url)}" alt="${esc(p)}"${style}>`;
  if (ext === ".pdf") return `<span class="pdf-fig"${style}><canvas data-pdf="${esc(url)}" aria-label="${esc(p)}"></canvas><a class="pdf-open" href="${esc(url)}" target="_blank" rel="noopener">open</a></span>`;
  return `<span class="omitted">${esc(ext.slice(1).toUpperCase())} figure (browsers cannot draw it): <a href="${esc(url)}" target="_blank" rel="noopener">${esc(p)}</a></span>`;
}

const alignOf = (c: string) => (c === "c" ? "center" : c === "r" ? "right" : "left");

/** A longtable's body as one page shows it: the head repeated on later pages (between `\\endfirsthead` and
 *  `\\endhead`) and the foot of every page but the last (ending at `\\endfoot`) are left out. */
function longtableOnce(body: string): string {
  const mark = (name: string, from = 0) => { const m = new RegExp(`\\\\${name}(?![A-Za-z])`).exec(body.slice(from)); return m ? { start: from + m.index, end: from + m.index + m[0].length } : null; };
  const first = mark("endfirsthead"), head = first && mark("endhead", first.end);
  if (first && head) body = body.slice(0, first.end) + body.slice(head.start);
  const foot = mark("endfoot");
  if (foot) {
    const before = [mark("endhead"), mark("endfirsthead")].filter((m) => m && m.end <= foot.start).map((m) => m!.end);
    const from = before.length ? Math.max(...before) : 0;
    body = body.slice(0, from) + body.slice(foot.end);
  }
  return body;
}

/** A tabular to an HTML table: rules, \multicolumn, \multirow, column alignment. `rest` starts after `\begin{env}`. */
function tableHTML(ctx: Ctx, env: string, rest: string): { html: string; end: number } {
  let i = 0;
  if (env === "tabular*" || env === "tabularx" || env === "tabulary") i = arg(rest, i).end;
  const o = optArg(rest, i); if (o) i = o.end;
  const specArg = arg(rest, i); i = specArg.end;
  const close = findEnd(rest, i, env);
  const body = longtableOnce(rest.slice(i, close.start));
  const aligns: string[] = [];
  const spec = specArg.body.replace(/@\{[^{}]*\}|!\{[^{}]*\}|>\{[^{}]*\}|<\{[^{}]*\}|\|/g, "");
  for (let k = 0; k < spec.length; k++) {
    const c = spec[k]!;
    if (c === "*") {
      const nG = group(spec, k + 1); const what = nG ? group(spec, nG.end) : null;
      if (nG && what) { for (let r = 0; r < Number(nG.body); r++) aligns.push(...what.body.split("").filter((x) => /[lcrpmbXS]/.test(x)).map(alignOf)); k = what.end - 1; }
      continue;
    }
    if (/[lcrXS]/.test(c)) aligns.push(alignOf(c));
    else if (/[pmb]/.test(c)) { aligns.push("left"); const g = group(spec, k + 1); if (g) k = g.end - 1; }
  }
  const rows = splitTop(body, "\\\\");
  const covered: number[] = [];
  let html = `<div class="tbl"><table>`;
  for (const raw of rows) {
    let row = raw;
    let ruleAbove = false;
    for (;;) {
      const m = /^\s*(\\(?:hline|toprule|midrule|bottomrule|cline\s*\{[^}]*\}|cmidrule\s*(?:\([^)]*\))?\s*\{[^}]*\}|endhead|endfirsthead|endfoot|endlastfoot|noalign\s*\{[^}]*\}|caption\s*\{(?:[^{}]|\{[^{}]*\})*\}))/.exec(row);
      if (!m) break;
      ruleAbove = ruleAbove || !m[1].startsWith("\\caption"); row = row.slice(m[0].length);
    }
    if (row.trim() === "") continue;
    const cells = splitTop(row, "&");
    let col = 0;
    html += `<tr${ruleAbove ? ` class="ruled"` : ""}>`;
    for (const cellRaw of cells) {
      while ((covered[col] ?? 0) > 0) { covered[col]!--; col++; }
      let cell = cellRaw.trim();
      let span = 1, rowspan = 1, align = aligns[col] ?? "left";
      const mc = /^\\multicolumn\s*\{(\d+)\}\s*\{([^}]*)\}\s*/.exec(cell);
      if (mc) { span = Number(mc[1]); const al = mc[2].replace(/[|@{}]/g, "").trim(); align = alignOf(al[0] ?? "c"); const g = group(cell, mc[0].length); cell = g ? g.body : cell.slice(mc[0].length); }
      const mr = /^\\multirow\s*(?:\[[^\]]*\])?\s*\{(-?\d+)\}\s*(?:\[[^\]]*\])?\s*\{[^}]*\}\s*/.exec(cell);
      if (mr) { rowspan = Math.max(1, Number(mr[1])); const g = group(cell, mr[0].length); cell = g ? g.body : cell.slice(mr[0].length); for (let s = 0; s < span; s++) covered[col + s] = rowspan - 1; }
      html += `<td${span > 1 ? ` colspan="${span}"` : ""}${rowspan > 1 ? ` rowspan="${rowspan}"` : ""} style="text-align:${align}">${render(ctx, cell, true)}</td>`;
      col += span;
    }
    html += `</tr>`;
  }
  html += `</table></div>`;
  if (ctx.pass === 2) ctx.health.tables++;
  return { html, end: close.end };
}

/**
 * A note set off by blank lines (the annotator writes them between paragraphs) would stand as a
 * paragraph holding only its mark — an empty bullet line. Its marks join the paragraph before it
 * when that one ends in text; otherwise (after a display, a heading, a result) the paragraph keeps
 * them in a line of no height (`.p.marks`).
 */
const MARKS = String.raw`((?:\s*<span class="cmark[^"]*" data-c="[^"]*" title="[^"]*"><\/span>)+)\s*`;
const MARKS_AFTER_TEXT = new RegExp(String.raw`(?<!<\/div>)<\/div><div class="p">${MARKS}<\/div>`, "g");
const MARKS_ALONE = new RegExp(String.raw`<div class="p">${MARKS}<\/div>`, "g");
/** Where a result's environment ends (dropped once the marks are folded): the notes written right
 *  after it are its own, and their marks stand at the end of its text, not before the next paragraph. */
const FORMAL_END = "<!--formal-end-->";
const MARKS_AFTER_FORMAL = new RegExp(String.raw`<\/div>${FORMAL_END}<\/div><div class="p">${MARKS}`, "g");
function foldMarks(html: string): string {
  for (let prev = ""; prev !== html;) { prev = html; html = html.replace(MARKS_AFTER_FORMAL, `$1</div>${FORMAL_END}</div><div class="p">`); }
  html = html.replaceAll(FORMAL_END, "").replace(/<div class="p">\s*<\/div>/g, "");
  for (let prev = ""; prev !== html;) { prev = html; html = html.replace(MARKS_AFTER_TEXT, "$1</div>"); }
  return html.replace(MARKS_ALONE, `<div class="p marks">$1</div>`);
}

const RESULT_KIND: Record<string, string> = { thm: "theorem", lem: "lemma", prop: "proposition", cor: "corollary" };
/**
 * A result the paper states in running text ("\\textbf{Theorem 2.} …", no environment): the paragraph
 * that opens with its anchor is its block — set like an environment's (`formal`), carrying its node,
 * so it has the bar, the badge and the Lean drawer of every other result. A paragraph that holds the
 * anchor alone (or several anchors and nothing else) stands before the result's own environment and is
 * no block. Pure.
 */
function proseResults(html: string): string {
  return html.replace(/<div class="p">(\s*<span class="res-anchor" id="[^"]*" data-node="((thm|lem|prop|cor):[^"]*)"><\/span>)(?!(?:\s*<span class="res-anchor"[^>]*><\/span>)*\s*<\/div>)/g,
    (_, anchor: string, node: string, prefix: string) => `<div class="p formal prose-res k-${RESULT_KIND[prefix]}" tabindex="0" data-res="${node}">${anchor}`);
}

/** Is `tex` nothing but review annotations (`\vs…{…}` with their arguments) and space? Pure. */
function onlyAnnotations(tex: string): boolean {
  let i = 0;
  for (;;) {
    while (i < tex.length && /\s/.test(tex[i]!)) i++;
    if (i >= tex.length) return true;
    const m = /^\\vs[A-Za-z]+/.exec(tex.slice(i, i + 40));
    if (!m) return false;
    i += m[0].length;
    while (tex[i] === "{") i = arg(tex, i).end;
  }
}

/**
 * The pinned readings a note states: those whose text opens it (the longest such text) — of them,
 * the ones pinned on the result the note stands at, when there is one. Pure.
 */
function readingsStated(pinned: Ctx["pinned"], note: string, env: string | null): string[] {
  const said = note.replace(/\s+/g, "");
  const first = pinned.find((r) => said.startsWith(r.key));
  if (!first) return [];
  const same = pinned.filter((r) => r.key === first.key);
  const here = same.filter((r) => env !== null && r.labels.includes(env));
  return (here.length ? here : same).map((r) => r.node);
}

/** The inside of an annotation block: a long statement or step is laid out one sentence to a line —
 *  a statement's (`stmt`) as a paper sets a theorem: in the text's own order, the sentences that set
 *  notation, those that assume and those that conclude each a group of lines with clear space
 *  between the groups (`statementParts`); no heading, bullet or frame — the sentences say "Suppose …",
 *  "Define …", "Then …" themselves. The markup is the same in every view of the page. The text is
 *  the repair's, word for word; only the line breaks and the spacing are the page's. */
function blockInner(ctx: Ctx, body: string, stmt: boolean): string {
  const sents = body.length > SENTENCE_LAYOUT_MIN ? texSentences(body) : [];
  if (sents.length < 3) return render(ctx, body, true);
  if (!stmt) return sents.map((t) => `<span class="rv-s">${render(ctx, t, true)}</span>`).join("");
  return `<div class="rv-parts">${statementParts(sents).map((s, k, all) => {
    const set = s.part === "setting" || s.part === "modify";
    return `<div class="rv-ln rv-${set ? "set" : s.part}${k > 0 && all[k - 1]!.run !== s.run ? " rv-first" : ""}">${set ? settingHTML(ctx, s.text) : render(ctx, s.text, true)}</div>`;
  }).join("")}</div>`;
}
/** A sentence of the setting: one whose displays run long is folded under the words that lead to
 *  them (`details.rv-fold`; the drawer opens a fold that holds a phrase it links). */
function settingHTML(ctx: Ctx, tex: string): string {
  const shown = mathChunks(tex).filter((m) => m.display && m.depth === 0);
  const lead = shown.length ? tex.slice(0, shown[0]!.from) : "";
  const rows = shown.reduce((n, m) => n + m.body.split("\\\\").length, 0), chars = shown.reduce((n, m) => n + m.body.length, 0);
  if (!lead.trim() || (rows <= FOLD_ROWS && chars <= FOLD_CHARS)) return render(ctx, tex, true);
  return `<details class="rv-fold"><summary>${render(ctx, lead, true)}</summary>${render(ctx, tex.slice(shown[0]!.from), true)}</details>`;
}

function render(ctx: Ctx, s: string, inline = false): string {
  let out = "";
  let i = 0;
  const n = s.length;
  const para = () => { if (!inline) out += `</div><div class="p">`; };
  while (i < n) {
    const c = s[i];
    if (c === "\n") {
      const m = /^\n[ \t]*\n\s*/.exec(s.slice(i, i + 200));
      if (m) { para(); i += m[0].length; continue; }
      out += " "; i++; continue;
    }
    if (c === "$") {
      if (s[i + 1] === "$") {
        const e = s.indexOf("$$", i + 2);
        if (e < 0) { out += "$"; i++; continue; }
        out += `<div class="eq">${renderMath(ctx, s.slice(i + 2, e), true)}</div>`;
        i = e + 2; continue;
      }
      // the formula ends at the first `$` that is not escaped (`$\\$` is a line break, closed) and stands in
      // no group of the formula: one in a group is a formula in its text (`$\{\text{$x$ is bad}\}$`); with
      // the groups unbalanced, at the first `$`
      let e = i + 1;
      for (let d = 0; e < n && (s[e] !== "$" || d > 0); e += s[e] === "\\" ? 2 : 1) d += s[e] === "{" ? 1 : s[e] === "}" ? -1 : 0;
      if (e >= n) { e = i + 1; while (e < n && s[e] !== "$") e += s[e] === "\\" ? 2 : 1; }
      out += renderMath(ctx, s.slice(i + 1, e), false);
      i = e + 1; continue;
    }
    if (c === "~") { out += "&nbsp;"; i++; continue; }
    if (c === "{") {
      const g = group(s, i);
      // a group holding a paragraph break scopes a passage (`{\\color{black} … }`): its paragraphs stay paragraphs
      if (g) { out += render(ctx, g.body, inline || !/\n[ \t]*\n/.test(g.body)); i = g.end; continue; }
      i++; continue;
    }
    if (c === "}") { i++; continue; }
    if (c === "`" && s[i + 1] === "`") { out += "“"; i += 2; continue; }
    if (c === "'" && s[i + 1] === "'") { out += "”"; i += 2; continue; }
    if (c === "`") { out += "‘"; i++; continue; }
    if (c === "-" && s.startsWith("---", i)) { out += "—"; i += 3; continue; }
    if (c === "-" && s.startsWith("--", i)) { out += "–"; i += 2; continue; }
    if (c === "&") { out += " "; i++; continue; }
    if (c === "_" || c === "^") {
      const x = textIndex(s, i), tag = c === "_" ? "sub" : "sup";
      if (x) { out += `<${tag}>${render(ctx, x.body, true)}</${tag}>`; i = x.end; continue; }
    }
    if (c !== "\\") { out += esc(c); i++; continue; }

    if (s[i + 1] === "[") {
      const e = s.indexOf("\\]", i + 2);
      if (e >= 0) { out += `<div class="eq">${renderMath(ctx, s.slice(i + 2, e), true)}</div>`; i = e + 2; continue; }
    }
    if (s[i + 1] === "(") {
      const e = s.indexOf("\\)", i + 2);
      if (e >= 0) { out += renderMath(ctx, s.slice(i + 2, e), false); i = e + 2; continue; }
    }
    if (s[i + 1] === "\\") { out += "<br>"; i += 2; if (s[i] === "*") i++; if (/^\s*\[\s*-?[\d.]+\s*[a-z]{2}\s*\]/.test(s.slice(i, i + 20))) i = optArg(s, i)!.end; continue; }
    const sym = /^\\([%&_#${}])/.exec(s.slice(i, i + 2));
    if (sym) { out += esc(sym[1]!); i += 2; continue; }
    const accent = /^\\(['`^"~=.])\{?([A-Za-z])\}?/.exec(s.slice(i, i + 5));
    if (accent) { out += esc((accent[2]! + ({ "'": "́", "`": "̀", "^": "̂", '"': "̈", "~": "̃", "=": "̄", ".": "̇" } as Record<string, string>)[accent[1]!]).normalize("NFC")); i += accent[0].length; continue; }
    if (/^\\[,;:! ]/.test(s.slice(i, i + 2))) { out += " "; i += 2; continue; }
    if (s[i + 1] === "/" || s[i + 1] === "-") { i += 2; continue; }
    const m = /^\\([A-Za-z@]+)(\*?)/.exec(s.slice(i, i + 64));
    if (!m) { i += 2; continue; }
    const name = m[1]!;
    const star = m[2] === "*";
    i += m[0].length;

    if (name === "begin") {
      const envArg = arg(s, i);
      const env = envArg.body.trim();
      if (TABULAR_ENVS.has(env)) { const t = tableHTML(ctx, env, s.slice(envArg.end)); out += t.html; i = envArg.end + t.end; continue; }
      const close = findEnd(s, envArg.end, env);
      const body = s.slice(envArg.end, close.start);
      i = close.end;
      const before = ctx.lastEnv;
      out += renderEnv(ctx, env, body, inline);
      if (ctx.lastEnv !== before) ctx.lastEnvEnd = { s, at: i };
      continue;
    }
    if (name === "end") { const a = arg(s, i); i = a.end; continue; }

    if (name in ANNOTATION_BLOCKS) {
      const a = arg(s, i); i = a.end;
      const b = ANNOTATION_BLOCKS[name]!;
      ctx.marks++;
      // an umbrella's corrected statement: the sentence naming its proposition blocks, which follow
      const umbrella = !!b.stmt && a.body.replace(/\s+/g, " ").trim() === UMBRELLA_STATEMENT;
      if (umbrella) ctx.umbrellas.open = { idx: ctx.umbrellas.names.push([]) - 1, of: null };
      out += `<div class="${b.cls}${umbrella ? " umbrella" : ""}" data-mark="${ctx.marks}"><span class="rv-tag">${esc(b.tag)}</span> ${umbrella ? `${UMBRELLA_MARK}${ctx.umbrellas.open!.idx}${UMBRELLA_MARK}` : blockInner(ctx, a.body, !!b.stmt)}</div>`;
      continue;
    }
    if (name in SPLIT_BLOCKS) {
      // a block a repair splits off a result — a corollary of the corrected result, or a proposition
      // the printed statement bundled in (`SPLIT_BLOCKS`): {node id}{the result}{statement … its proof}. A
      // result of its own the paper does not print — the block is its place on the page (its anchor,
      // its badge, its Lean drawer), right after the result it is split from; blue like the corrected
      // statement before it (`rv ins`), its heading the tag
      const a1 = arg(s, i), a2 = arg(s, a1.end), a3 = arg(s, a2.end); i = a3.end;
      const node = a1.body.trim(), id = nodeAnchor(node), pending = SPLIT_BLOCKS[name]!.pending;
      const kind = ctx.splitKinds[node] ?? SPLIT_BLOCKS[name]!.kind;
      const word = kind === "proposition" ? "Proposition" : "Corollary";
      ctx.anchors[node] = id;
      ctx.marks++;
      const sep = COROLLARY_PROOF.find((x) => a3.body.includes(x));
      const [stmt, why] = sep ? a3.body.split(sep) : [a3.body];
      // a result block like the printed ones (`formal`: its bar, its heading, its Lean drawer on a
      // click), though the paper does not print it; what the review says of it is the small tag
      // numbered under the result it is split from ("Corollary 5.2.1", "Proposition 5.2.2": one running
      // number per result across both kinds): not one of the paper's numbers
      const of = render(ctx, a2.body, true);
      const num = /\s((?:[A-Z]\.?)?\d[\w.]*)$/.exec(of.replace(/<[^>]+>/g, "").replace(/&nbsp;/g, " ").trim())?.[1];
      const k = (ctx.splits[a2.body] = (ctx.splits[a2.body] ?? 0) + 1);
      const head = `<span class="env">${num ? `${word} ${esc(num)}.${k}` : `${word} ${k} of ${of}`}.</span>`;
      const u = ctx.umbrellas.open;
      if (u && kind === "proposition" && (u.of === null || u.of === a2.body)) {
        u.of = a2.body;
        ctx.umbrellas.names[u.idx]!.push(num ? `Proposition ${num}.${k}` : "");
      }
      const tag = `<span class="rv-tag">${pending ? "Proposed — awaiting a ruling" : kind === "proposition" ? "Stated apart by the revision" : "Added by the revision"}</span>`;
      out += `<div class="rv ins cor${pending ? " pending" : ""} formal k-${kind}" tabindex="0" data-res="${esc(node)}" data-mark="${ctx.marks}"><span class="res-anchor" id="${esc(id)}" data-node="${esc(node)}"></span>${head} ${tag} ${blockInner(ctx, (stmt ?? "").trim(), true)}`
        + `${why !== undefined ? `<div class="proof"><span class="env">Proof.</span> ${render(ctx, why.trim(), true)}<span class="qed">∎</span></div>` : ""}</div>`;
      continue;
    }
    if (name in ANNOTATION_NOTES || name === "vsReadingSymbol") {
      const noteAt = i - m[0].length;
      let label: string, kind: string;
      if (name === "vsReadingSymbol") {
        const sym2 = arg(s, i); i = sym2.end;
        kind = "reading-symbol";
        label = `Clarification (symbol ${renderMath(ctx, symbolMath(sym2.body), false)})`;
      } else {
        label = esc(ANNOTATION_NOTES[name]!.label);
        kind = ANNOTATION_NOTES[name]!.kind;
      }
      const a = arg(s, i); i = a.end;
      if (ctx.pass === 1) continue;
      const id = `c${ctx.comments.length + 1}`;
      // A note stands at the environment it is in, or at the one that ends right before it (nothing
      // but other annotations between): a note further on, in running text, stands at no environment.
      const env = ctx.envStack.length ? ctx.envStack[ctx.envStack.length - 1]! : ctx.lastEnvEnd?.s === s && onlyAnnotations(s.slice(ctx.lastEnvEnd.at, noteAt)) ? ctx.lastEnv : null;
      // a note's line breaks separate its items (the counterexample's (a) (b) (c)): set apart, not just broken
      // Two notes of one kind, environment and text (the same clarification under two results of an
      // environment) are told apart by their order: an issue reported on one is not the other's.
      const hash = createHash("sha1").update([kind, env ?? "", label, a.body].join("\0")).digest("hex").slice(0, 12);
      const earlier = ctx.comments.filter((c) => c.key === hash || c.key.startsWith(`${hash}-`)).length;
      const key = earlier ? `${hash}-${earlier + 1}` : hash;
      ctx.comments.push({ id, key, excerpt: a.body.replace(/\s+/g, " ").trim().slice(0, 160), kind, label, html: render(ctx, a.body, true).replace(/<br>/g, '<span class="nl"></span>'), env });
      if (kind === "reading" || kind === "reading-owner") for (const node of readingsStated(ctx.pinned, a.body, env)) ctx.readings[node] ??= id;
      out += `<span class="cmark k-${kind}" data-c="${id}" title="${kind.startsWith("reading") ? "clarification" : kind === "detail" ? "proof detail" : "PaperFormalizer comment"}"></span>`;
      continue;
    }
    if (name === "tcAnchor") {
      // starred: the place a proof invokes a cited result — a label there, never a result's block
      const a = arg(s, i); i = a.end;
      const node = a.body.trim();
      const id = nodeAnchor(node);
      ctx.anchors[node] = id;
      out += `<span class="res-anchor${star ? " cited-site" : ""}" id="${esc(id)}" data-node="${esc(node)}"></span>`;
      continue;
    }
    if (name === "vsStruck" || name === "vsStruckRed") { const a = arg(s, i); i = a.end; ctx.marks++; out += `<span class="rv del struck" data-mark="${ctx.marks}">${render(ctx, a.body, true)}</span>`; continue; }
    if (name === "vsDisplay" || name === "vsFit") { const a = arg(s, i); i = a.end; out += `<div class="eq">${renderMath(ctx, a.body, true)}</div>`; continue; }
    if (name === "vsFitIn") { const a1 = arg(s, i); const a2 = arg(s, a1.end); i = a2.end; out += `<div class="eq">${renderMath(ctx, a2.body, true)}</div>`; continue; }
    if (name === "vsMathEnv") { const a1 = arg(s, i); const a2 = arg(s, a1.end); i = a2.end; out += render(ctx, a2.body, inline); continue; }
    if (name === "vsLine" || name === "vsSub" || name === "vsPar" || name === "vsBreak") { out += "<br>"; continue; }
    if (name === "vsItem") { const a = arg(s, i); i = a.end; out += `<br><span class="vs-item">${render(ctx, a.body, true)}</span> `; continue; }

    if (["section", "subsection", "subsubsection", "paragraph", "subparagraph", "chapter"].includes(name)) {
      const o = optArg(s, i); if (o) i = o.end;
      const a = arg(s, i); i = a.end;
      const level = name === "chapter" || name === "section" ? 1 : name === "subsection" ? 2 : name === "subsubsection" ? 3 : 4;
      if (level === 4) { out += `<strong class="runin">${render(ctx, a.body, true)}</strong> `; continue; }
      const num = star ? "" : headingNumber(ctx, level);
      if (num) ctx.target = num;
      const text = render(ctx, a.body, true);
      const id = `sec-${num ? num.replace(/\./g, "-") + "-" : ""}${slug(a.body.replace(/\\[A-Za-z]+/g, ""))}`;
      const lm = /^\s*\\label\s*\{([^{}]*)\}/u.exec(s.slice(i));
      if (lm) ctx.refKinds[labelKey(lm[1]!)] = ctx.appendix ? "appendix" : "section";
      if (ctx.pass === 2) ctx.toc.push({ id, text: `${num ? num + " " : ""}${plain(text)}`, html: `${num ? esc(num) + " " : ""}${text.replace(/\sid="[^"]*"/g, "").replace(/<a\b[^>]*>|<\/a>/g, "")}`, level });
      out += `</div><h${level + 1} id="${id}">${num ? `<span class="secnum">${num}</span> ` : ""}${text}</h${level + 1}><div class="p">`;
      continue;
    }
    if (name === "appendix") { ctx.appendix = true; ctx.sec = []; for (const [cn, p] of Object.entries(ctx.pre.numberWithin)) if (p === "section") ctx.counters[cn] = 0; continue; }
    if (name === "label") {
      const a = arg(s, i); i = a.end;
      const l = labelKey(a.body);
      if (ctx.pass === 1 && !(l in ctx.own)) ctx.own[l] = ctx.target;
      out += `<a id="lbl-${esc(slug(l))}"></a>`;
      continue;
    }
    if (["ref", "eqref", "cref", "Cref", "autoref", "pageref", "nameref", "vref", "cpageref", "subref"].includes(name)) {
      const a = arg(s, i); i = a.end;
      out += a.body.split(",").map((l) => refText(ctx, name, l.trim())).join(", ");
      continue;
    }
    if (/^[cC]ite[a-z]*$/.test(name) || name === "citet" || name === "citep" || name === "citealp" || name === "citealt") {
      const o1 = optArg(s, i); if (o1) i = o1.end;
      const o2 = o1 ? optArg(s, i) : null; if (o2) i = o2.end;
      const a = arg(s, i); i = a.end;
      out += citeText(ctx, name, a.body, (o2 ?? o1)?.body?.trim() || null);
      continue;
    }
    if (name === "footnote") {
      const o = optArg(s, i); if (o) i = o.end;
      const a = arg(s, i); i = a.end;
      ctx.footnotes++;
      out += `<span class="fn" tabindex="0"><sup>${ctx.footnotes}</sup><span class="fn-body">${render(ctx, a.body, true)}</span></span>`;
      continue;
    }
    if (name === "includegraphics") {
      const o = optArg(s, i); if (o) i = o.end;
      const a = arg(s, i); i = a.end;
      out += figureHTML(ctx, o?.body ?? "", a.body);
      continue;
    }
    if (name === "caption") {
      const o = optArg(s, i); if (o) i = o.end;
      const a = arg(s, i); i = a.end;
      out += `<span class="caption-text">${render(ctx, a.body, true)}</span>`;
      continue;
    }
    if (name === "url" || name === "path") { const a = arg(s, i); i = a.end; const u = a.body.trim(); out += /^https?:\/\//.test(u) ? `<a href="${esc(u)}" target="_blank" rel="noopener">${esc(u)}</a>` : `<code>${esc(u)}</code>`; continue; }
    if (name === "href") { const a = arg(s, i); const b = arg(s, a.end); i = b.end; const u = a.body.trim(); out += /^https?:\/\//.test(u) ? `<a href="${esc(u)}" target="_blank" rel="noopener">${render(ctx, b.body, true)}</a>` : render(ctx, b.body, true); continue; }
    if (name === "emph" || name === "textit" || name === "textsl") { const a = arg(s, i); i = a.end; out += `<em>${render(ctx, a.body, true)}</em>`; continue; }
    if (name === "textbf") { const a = arg(s, i); i = a.end; out += `<strong>${render(ctx, a.body, true)}</strong>`; continue; }
    if (name === "texttt") { const a = arg(s, i); i = a.end; out += `<code>${render(ctx, a.body, true)}</code>`; continue; }
    if (name === "verb") { const d = s[i]; const e = d ? s.indexOf(d, i + 1) : -1; if (e > i) { out += `<code>${esc(s.slice(i + 1, e))}</code>`; i = e + 1; } continue; }
    if (name === "textsc") { const a = arg(s, i); i = a.end; out += `<span class="sc">${render(ctx, a.body, true)}</span>`; continue; }
    if (name === "underline" || name === "uline") { const a = arg(s, i); i = a.end; out += `<u>${render(ctx, a.body, true)}</u>`; continue; }
    if (name === "textcolor") { const o = optArg(s, i); if (o) i = o.end; const a = arg(s, i); const b = arg(s, a.end); i = b.end; out += render(ctx, b.body, true); continue; }
    if (name === "textsuperscript") { const a = arg(s, i); i = a.end; out += `<sup>${render(ctx, a.body, true)}</sup>`; continue; }
    if (name === "textsubscript") { const a = arg(s, i); i = a.end; out += `<sub>${render(ctx, a.body, true)}</sub>`; continue; }
    if (name === "item") { const o = optArg(s, i); if (o) { i = o.end; out += `</li><li><strong>${render(ctx, o.body, true)}</strong> `; } else out += `</li><li>`; continue; }
    if (name === "bibliography") { const a = arg(s, i); i = a.end; continue; }
    // etoolbox: a toggle set in the body holds from there on; `\iftoggle{t}{yes}{no}` is the branch it selects
    if (["newtoggle", "providetoggle", "toggletrue", "togglefalse", "settoggle"].includes(name)) { i = setToggle(ctx.toggles, name, s, i); continue; }
    if (name === "iftoggle" || name === "nottoggle") {
      const t = arg(s, i), yes = arg(s, t.end), no = arg(s, yes.end); i = no.end;
      const b = (ctx.toggles[t.body.trim()] ?? false) === (name === "iftoggle") ? yes.body : no.body;
      out += render(ctx, b, inline || !/\n[ \t]*\n/.test(b));
      continue;
    }
    // \ensuremath in text is a formula; one neither renderer reads (text-mode content, `\hspace*{-\len}`) stays text, as before
    if (name === "ensuremath") {
      const a = arg(s, i); i = a.end;
      const failures = ctx.health.mathFailures.length;
      const m = renderMath(ctx, a.body, false);
      if (m.includes('class="tex-raw"')) { ctx.health.mathFailures.length = failures; out += render(ctx, a.body, true); } else out += m;
      continue;
    }
    // glue and rules set no text: `\vskip \belowdisplayskip`, `\hskip 0pt plus 1fil`, `\vrule width 1pt` (a braced argument: dropped below)
    if ((name === "vskip" || name === "hskip" || name === "kern") && !/^\s*\{/.test(s.slice(i, i + 40))) { i += GLUE.exec(s.slice(i, i + 160))?.[0].length ?? 0; continue; }
    if (name === "vrule" || name === "hrule") { i += RULE_SPEC.exec(s.slice(i, i + 160))![0].length; continue; }
    if (name === "enquote") { const a = arg(s, i); i = a.end; out += `“${render(ctx, a.body, true)}”`; continue; }
    if (name === "penalty" || name === "hangindent" || name === "parindent" || name === "hangafter" || name === "parskip" || name === "leftskip" || name === "rightskip" || name === "itemsep" || name === "topsep") {
      const r = /^\s*=?\s*(-?[\d.]+\s*(pt|em|ex|in|cm|mm|bp|sp)?|\\[A-Za-z]+)/.exec(s.slice(i, i + 40)); if (r) i += r[0].length; continue;
    }
    if (["if", "fi", "else", "long", "ifx", "ifdim", "ifnum", "iftrue", "iffalse", "expandafter", "noexpand", "csname", "endcsname", "arabic", "roman", "Roman", "alph", "Alph", "fnsymbol", "the", "value", "phantom", "hphantom", "vphantom"].includes(name)) {
      if (["arabic", "roman", "Roman", "alph", "Alph", "fnsymbol", "value", "phantom", "hphantom", "vphantom"].includes(name) && /^\s*\{/.test(s.slice(i))) i = arg(s, i).end;
      continue;
    }
    const literal = ({ urlprefix: "URL ", textquotedblleft: "“", textquotedblright: "”", oe: "œ", OE: "Œ", aa: "å", AA: "Å", l: "ł", L: "Ł", textperiodcentered: "·", textbullet: "•", LaTeX: "LaTeX", TeX: "TeX", ldots: "…", dots: "…", bysame: "———", dotsc: "…", S: "§", P: "¶", copyright: "©", textregistered: "®", dag: "†", dagger: "†", ddag: "‡", ss: "ß", o: "ø", O: "Ø", ae: "æ", AE: "Æ", i: "ı", and: ", ", AND: ", ", And: ", ", newblock: " ", textbackslash: "\\", textasciitilde: "~", textendash: "–", textemdash: "—", textquoteright: "’", textquoteleft: "‘", quad: " ", qquad: "  " } as Record<string, string>)[name];
    if (literal !== undefined) { out += esc(literal); continue; }
    if (NOOP.has(name)) continue;
    if (DROP_WITH_ARG.has(name)) {
      if (s[i] === "*") i++;
      if (name === "def" || name === "gdef") { const r = /^\s*\\[A-Za-z]+(?:(?:#\d)+|[^\s{}#\\%]*)/.exec(s.slice(i)); if (r) i += r[0].length; if (/^\s*\{/.test(s.slice(i))) i = arg(s, i).end; continue; }
      const multi = ["etocsettocstyle", "tikzset", "usetikzlibrary", "pgfutil@ifundefined", "pgfdeclarepatternformonly", "pgfdeclarepatterninherentlycolored", "setlength", "addtolength", "setcounter", "addtocounter", "newtheorem", "renewcommand", "newcommand", "providecommand", "numberwithin", "DeclareMathOperator", "newenvironment", "renewenvironment", "cmidrule", "psfrag"].includes(name);
      do {
        const o = optArg(s, i); if (o) { i = o.end; continue; }
        if (s[i] === "(" && name === "cmidrule") { const e = s.indexOf(")", i); if (e > 0) { i = e + 1; continue; } }
        if (/^\s*\{/.test(s.slice(i))) i = arg(s, i).end; else break;
      } while (multi && /^\s*[\[{(]/.test(s.slice(i)));
      continue;
    }
    if (name in WRAPPERS) {
      const want = WRAPPERS[name]!;
      const groups: string[] = [];
      while (groups.length < want) {
        const o = optArg(s, i); if (o) { i = o.end; continue; }
        if (!/^\s*\{/.test(s.slice(i))) {
          // an argument written without braces is one token (`\texorpdfstring{$x$}.`): the PDF string, not text
          const t = name === "texorpdfstring" && groups.length === 1 ? /^\s*(\\[A-Za-z@]+|\\.|[^\s\\{}])/.exec(s.slice(i)) : null;
          if (t) i += t[0].length;
          break;
        }
        const a = arg(s, i); groups.push(a.body); i = a.end;
      }
      const keep = name === "texorpdfstring" ? groups[0] : groups.at(-1);
      if (keep !== undefined) out += render(ctx, keep, true);
      continue;
    }
    // the author's own text macro: expand it (with its arguments) and render the result
    const ex = expandMacro(ctx, name, s, i);
    if (ex) {
      i = ex.end;
      ctx.depth++;
      out += render(ctx, ex.text, true);
      ctx.depth--;
      continue;
    }
    // text accents named by a letter (`\v{c}`, `\c c`), when the paper does not define the name itself
    const letterAccent = ({ v: "̌", c: "̧", u: "̆", H: "̋", k: "̨", r: "̊", d: "̣", b: "̱" } as Record<string, string>)[name];
    const accented = letterAccent ? /^(?:\{\s*(\\i|[A-Za-z])\s*\}|\s+([A-Za-z]))/.exec(s.slice(i, i + 8)) : null;
    if (accented) { const base = accented[1] ?? accented[2]!; out += esc(((base === "\\i" ? "ı" : base) + letterAccent).normalize("NFC")); i += accented[0].length; continue; }
    // ordinals and integer arithmetic (nth, intcalc), as bibliography macros of conference names use them
    if (name === "nth" || name === "intcalcSub" || name === "intcalcAdd") {
      const a = arg(s, i); const b = name === "nth" ? null : arg(s, a.end); i = (b ?? a).end;
      const hx = render(ctx, a.body, true), hy = b ? render(ctx, b.body, true) : "";
      const x = plain(hx).trim(), y = plain(hy).trim();
      if (name === "nth") out += /^\d+$/.test(x) ? x + (/1\d$/.test(x) ? "th" : ({ 1: "st", 2: "nd", 3: "rd" } as Record<string, string>)[x.slice(-1)] ?? "th") : hx;
      else out += /^-?\d+$/.test(x) && /^-?\d+$/.test(y) ? String(name === "intcalcSub" ? Number(x) - Number(y) : Number(x) + Number(y)) : `${hx}${name === "intcalcSub" ? "−" : "+"}${hy}`;
      continue;
    }
    // an algorithm2e block quoted in running text (a note quoting a step): its keywords, as in the float
    const loop = ({ For: ["for", "do"], ForEach: ["foreach", "do"], ForAll: ["forall", "do"], While: ["while", "do"], If: ["if", "then"] } as Record<string, [string, string]>)[name];
    if (loop && /^\s*\{/.test(s.slice(i, i + 4))) {
      const a = arg(s, i); const b = /^\s*\{/.test(s.slice(a.end, a.end + 4)) ? arg(s, a.end) : null; i = (b ?? a).end;
      out += `<b>${loop[0]}</b> ${render(ctx, a.body, true)}${b ? ` <b>${loop[1]}</b> ${render(ctx, b.body, true)}` : ""}`;
      continue;
    }
    // a delimiter sized in text (`\big(in $x$\big)`): TeX's \big sets it as in a formula
    const sized = /^(?:big|Big|bigg|Bigg)[lrm]?$/.test(name) ? /^\s*(\\[A-Za-z]+|\\[{}|]|[()[\]|/.<>])/.exec(s.slice(i, i + 24)) : null;
    if (sized) { out += renderMath(ctx, `\\${name}${sized[1]}`, false); i += sized[0].length; continue; }
    if (name === "part") { const o = optArg(s, i); if (o) i = o.end; const a = arg(s, i); i = a.end; out += `</div><h2 class="part">${render(ctx, a.body, true)}</h2><div class="p">`; continue; }
    if (!/^\s*\{/.test(s.slice(i, i + 4)) && katexSymbol(name)) { out += renderMath(ctx, `\\${name}`, false); continue; }
    if (ctx.pass === 2) ctx.health.unknownCommands[name] = (ctx.health.unknownCommands[name] ?? 0) + 1;
    // anything else: keep the text of its arguments
    while (/^\s*\{/.test(s.slice(i, i + 40))) { const a = arg(s, i); i = a.end; out += render(ctx, a.body, true); }
  }
  return out;
}

const symbolCache = new Map<string, boolean>();
/** Whether KaTeX renders `\name` alone (a symbol such as \beta or \ast written outside math). */
function katexSymbol(name: string): boolean {
  let ok = symbolCache.get(name);
  if (ok === undefined) {
    try { katex.renderToString(`\\${name}`, { throwOnError: true, strict: "ignore" }); ok = true; } catch { ok = false; }
    symbolCache.set(name, ok);
  }
  return ok;
}

function findEnd(s: string, from: number, env: string): { start: number; end: number } {
  const open = `\\begin{${env}}`;
  const close = `\\end{${env}}`;
  let depth = 1;
  let k = from;
  while (k < s.length) {
    const a = s.indexOf(open, k);
    const b = s.indexOf(close, k);
    if (b < 0) return { start: s.length, end: s.length };
    if (a >= 0 && a < b) { depth++; k = a + open.length; continue; }
    if (--depth === 0) return { start: b, end: b + close.length };
    k = b + close.length;
  }
  return { start: s.length, end: s.length };
}

function theoremFor(ctx: Ctx, env: string): Preamble["theorems"][string] | null {
  const own = ctx.pre.theorems[env];
  if (own) return own;
  const kind = ctx.kinds[env];
  if (kind) return { name: COMMON_THEOREMS[kind] ?? kind.charAt(0).toUpperCase() + kind.slice(1), counter: kind, numbered: true, within: null };
  const base = env.replace(/\*$/, "");
  if (COMMON_THEOREMS[base]) return { name: COMMON_THEOREMS[base]!, counter: base, numbered: !env.endsWith("*"), within: null };
  return null;
}

function renderEnv(ctx: Ctx, env: string, body: string, inline: boolean): string {
  if (MATH_ENVS.has(env)) return mathEnv(ctx, env, body);
  if (SKIP_ENVS.has(env)) {
    if (env === "comment") return "";
    const page = env === "tikzpicture" ? ctx.tikz?.page.get(body.replace(/\s+/g, "")) : undefined;
    if (page) return `<span class="pdf-fig"><canvas data-pdf="${esc(ctx.tikz!.url)}" data-page="${page}" aria-label="TikZ picture"></canvas></span>`;
    if (ctx.pass === 2) ctx.health.omitted++;
    return `<div class="omitted">A drawing (${esc(env)}) is not shown here; see the typeset PDF.</div>`;
  }
  if (FIGURE_ENVS.has(env) || TABLE_ENVS.has(env)) {
    const isTable = TABLE_ENVS.has(env);
    let b = body;
    if (env === "wrapfigure" || env === "wraptable") b = b.replace(/^\s*(\[[^\]]*\])?\s*\{[^}]*\}\s*(\[[^\]]*\])?\s*\{[^}]*\}/, "");
    else { const o = optArg(b, 0); if (o && /^\s*\[/.test(b)) b = b.slice(o.end); }
    const num = nextNumber(ctx, isTable ? "table" : "figure");
    const saved = ctx.target; ctx.target = num;
    let inner = render(ctx, b, true);
    ctx.target = saved;
    const word = isTable ? "Table" : "Figure";
    // the figure's own caption (the last one; sub-captions stay where they are)
    const lastCap = inner.lastIndexOf(`<span class="caption-text">`);
    let caption = "";
    if (lastCap >= 0) {
      const end = inner.indexOf("</span>", lastCap);
      const depthEnd = closingSpan(inner, lastCap);
      caption = inner.slice(lastCap + `<span class="caption-text">`.length, depthEnd >= 0 ? depthEnd : end);
      inner = inner.slice(0, lastCap) + inner.slice((depthEnd >= 0 ? depthEnd : end) + "</span>".length);
    }
    const cap = `<figcaption><b>${word} ${esc(num)}.</b> ${caption}</figcaption>`;
    return `</div><figure class="${isTable ? "tab" : "fig"}" id="${isTable ? "tab" : "fig"}-${esc(num.replace(/\./g, "-"))}">${isTable ? cap + inner : inner + cap}</figure><div class="p">`;
  }
  if (env === "subfigure" || env === "subtable" || env === "minipage") {
    const b = body.replace(/^\s*(\[[^\]]*\])?\s*(\[[^\]]*\])?\s*\{[^}]*\}/, "");
    return `<span class="subfig">${render(ctx, b, true)}</span>`;
  }
  if (env === "abstract") return `</div><section class="abstract" id="sec-abstract"><h4>Abstract</h4><div class="p">${render(ctx, body)}</div></section><div class="p">`;
  if (env === "keywords" || env === "keyword") return `</div><p class="keywords"><b>Keywords:</b> ${render(ctx, body, true)}</p><div class="p">`;
  if (env === "proof") {
    let b = body;
    const o = optArg(b, 0);
    let head = "Proof.";
    // amsthm puts the optional argument in place of "Proof"; a paper written for a class that keeps
    // the word writes `[of Theorem 1]`, which is read as that class prints it.
    if (o && /^\s*\[/.test(b)) { head = `${/^\s*of\s/.test(o.body) ? "Proof " : ""}${render(ctx, o.body, true)}.`; b = b.slice(o.end); }
    ctx.envStack.push(ctx.lastEnv);
    const html = `</div><div class="proof"><span class="env">${head}</span> <div class="p">${render(ctx, b)}</div><span class="qed">∎</span></div><div class="p">`;
    ctx.envStack.pop();
    return html;
  }
  if (["itemize", "enumerate", "description", "compactitem", "compactenum", "inparaenum", "asparaenum"].includes(env)) {
    const tag = env.includes("enum") ? "ol" : "ul";
    const o = optArg(body, 0);
    const b = o && /^\s*\[/.test(body) ? body.slice(o.end) : body;
    // enumitem's `label=\alph*.` (and its kin): the list's own numbering
    const kind = tag === "ol" && o && b !== body ? /\\(alph|Alph|roman|Roman)\*/.exec(o.body)?.[1] : undefined;
    const type = kind ? ` type="${{ alph: "a", Alph: "A", roman: "i", Roman: "I" }[kind]}"` : "";
    return `<${tag} class="${env}"${type}><li>${render(ctx, b, true)}</li></${tag}>`.replace(/<li>\s*<\/li>/g, "");
  }
  if (["verbatim", "lstlisting", "Verbatim", "minted"].includes(env)) return `<pre>${esc(body)}</pre>`;
  if (env === "algorithmic") { const html = renderAlgorithmic(body, (t) => render(ctx, t, true)); return inline ? html : `</div>${html}<div class="p">`; }
  if (env === "array") return `<div class="eq">${renderMath(ctx, `\\begin{array}${body}\\end{array}`, true)}</div>`;
  if (["center", "quote", "quotation", "flushleft", "flushright", "adjustbox", "small", "footnotesize", "scriptsize", "landscape", "sidewaystable", "sidewaysfigure", "singlespace", "doublespace", "spacing", "threeparttable", "tablenotes", "frame", "mdframed", "tcolorbox", "framed"].includes(env)) {
    let b = body;
    if (env === "adjustbox" || env === "spacing") b = b.replace(/^\s*\{[^}]*\}/, "");
    if (env === "sidewaystable" || env === "sidewaysfigure") return renderEnv(ctx, env === "sidewaystable" ? "table" : "figure", b, inline);
    return inline ? render(ctx, b, true) : `</div><div class="${env === "center" ? "center" : "quote"}"><div class="p">${render(ctx, b)}</div></div><div class="p">`;
  }
  if (env === "thebibliography") return renderBib(ctx, body);
  if (["acknowledgments", "acknowledgements", "ack", "acks"].includes(env)) return `</div><section class="ack"><h4>Acknowledgements</h4><div class="p">${render(ctx, body)}</div></section><div class="p">`;
  if (["bibunit", "singlespacing", "onehalfspacing", "doublespacing", "centering", "raggedright", "document", "frontmatter", "titlepage", "fullwidth", "widetext", "multicols", "flushleft"].includes(env)) return render(ctx, env === "multicols" ? body.replace(/^\s*\{[^}]*\}/, "") : body, inline);
  const userEnv = ctx.pre.envDefs[env];
  const classified = Boolean(ctx.pre.theorems[env] || ctx.kinds[env]);
  // a pseudocode float (algorithm / algorithm2e packages) — unless the paper declares its own
  // theorem-like `algorithm` (\newtheorem): the run's environment map lists `algorithm` either way
  if ((env === "algorithm" || env === "algorithm*") && !ctx.pre.theorems[env.replace(/\*$/, "")]) return algorithmFloat(ctx, body, inline);
  if (userEnv && ctx.depth < 12 && ctx.expansions < EXPANSION_BUDGET && !classified) {
    ctx.expansions++;
    let b = body;
    const args: string[] = [];
    if (userEnv.dflt !== null) { const o = optArg(b, 0); if (o && /^\s*\[/.test(b)) { args.push(o.body); b = b.slice(o.end); } else args.push(userEnv.dflt); }
    while (args.length < userEnv.n) { const a = arg(b, 0); args.push(a.body); b = b.slice(a.end); }
    const sub = (t: string) => t.replace(/#(\d)/g, (_m, d: string) => args[Number(d) - 1] ?? "");
    ctx.depth++;
    const html = render(ctx, `${sub(userEnv.begin)}${b}${sub(userEnv.end)}`, inline);
    ctx.depth--;
    return html;
  }
  const th = theoremFor(ctx, env);
  if (th) {
    let b = body;
    const o = optArg(b, 0);
    let title = "";
    let note = "";
    if (o && /^\s*\[/.test(b)) { note = o.body; title = render(ctx, o.body, true); b = b.slice(o.end); }
    const label = /\\label\{([^}]+)\}/.exec(b)?.[1]?.trim() ?? null;
    let num = "";
    if (th.numbered) {
      const own = nextNumber(ctx, th.counter);
      num = (label && ctx.aux.labels[labelKey(label)]) || own;
    } else {
      // numbered by hand, `\begin{corollary*}[(3.2)]`: the note is its number
      const hand = handNumber(note);
      if (hand) {
        num = hand;
        title = "";
        // the .aux gives a label in an unnumbered environment the enclosing counter: the note's number wins
        if (label) ctx.aux.labels[labelKey(label)] = hand;
      }
    }
    const saved = ctx.target;
    ctx.target = num;
    const name = plain(render(ctx, th.name, true)).replace(/\s+/g, " ").trim() || env;
    if (label) ctx.refNames[labelKey(label)] = name;
    const heading = `${name}${num ? ` ${num}` : ""}`;
    const anchor = label ? labelAnchor(label) : `env-${slug(env)}-${ctx.envs.length + 1}`;
    if (ctx.pass === 2) ctx.envs.push({ anchor, label, envName: env, heading });
    ctx.envStack.push(label);
    const inner = render(ctx, b);
    ctx.envStack.pop();
    ctx.target = saved;
    ctx.lastEnv = label;
    return `</div><div class="formal k-${esc(slug(env))}" id="${esc(anchor)}" data-label="${esc(label ?? "")}" tabindex="0"><span class="env">${esc(heading)}${title ? ` (${title})` : ""}.</span> <div class="p">${inner}</div>${FORMAL_END}</div><div class="p">`;
  }
  // an environment named by a command (`\newcommand{\proofof}[1]{…}`, then `\begin{proofof}{X} … \end{proofof}`):
  // LaTeX runs `\proofof` at the begin, `\endproofof` (when defined) at the end
  const begin = expandMacro(ctx, env, body, 0);
  if (begin) {
    ctx.depth++;
    const html = render(ctx, begin.text, true) + render(ctx, body.slice(begin.end), inline) + (ctx.pre.textMacros[`\\end${env}`] ? render(ctx, `\\end${env}`, true) : "");
    ctx.depth--;
    return html;
  }
  if (ctx.pass === 2) ctx.health.unknownCommands[`env:${env}`] = (ctx.health.unknownCommands[`env:${env}`] ?? 0) + 1;
  return render(ctx, body, inline);
}

/** Index of the `</span>` closing the span opened at `at` (nested spans counted), or -1. */
function closingSpan(html: string, at: number): number {
  let depth = 0;
  const re = /<span\b|<\/span>/g;
  re.lastIndex = at;
  let m: RegExpExecArray | null;
  while ((m = re.exec(html))) {
    if (m[0] === "</span>") { depth--; if (depth === 0) return m.index; }
    else depth++;
  }
  return -1;
}

function renderBib(ctx: Ctx, body: string): string {
  const items = body.split(/\\bibitem/).slice(1).map((it) => {
    const o = optArg(it, 0);
    let rest = o && /^\s*\[/.test(it) ? it.slice(o.end) : it;
    const k = arg(rest, 0);
    rest = rest.slice(k.end);
    return `<li id="bib-${esc(slug(k.body))}">${render(ctx, rest.replace(/\\newblock/g, " "), true)}</li>`;
  });
  return `</div><section class="references" id="sec-references"><h2>References</h2><ol>${items.join("")}</ol></section><div class="p">`;
}

/** Put `\tcAnchor{node}` before the first occurrence of each anchor's source line (at the end of that
 * line for an anchor marked `after`). Pure. */
function placeAnchors(files: Record<string, string>, anchors: PaperInput["anchors"]): Record<string, string> {
  if (!anchors?.length) return files;
  const out = { ...files };
  for (const a of anchors) {
    const text = out[a.file];
    const needle = a.line.trim();
    if (!text || needle.length < 8) continue;
    const t = text.replace(/\r\n?/g, "\n");
    // the annotated copy may have marked the line up after its first words ("\textbf{Theorem 2.}
    // \vsOriginal{…"): then the longest start of it found once in the file
    const unique = (n: string) => { const i = t.indexOf(n); return i >= 0 && i === t.lastIndexOf(n) ? i : -1; };
    let at = t.indexOf(needle);
    // a line the file holds several times (a bare `\\begin{proof}`): its k-th occurrence when the file holds
    // it as often as the source (`nth`: [k, count] there — the annotated copy's lines have shifted), else the
    // occurrence nearest its line number
    const all: number[] = [];
    for (let i = at; i >= 0; i = t.indexOf(needle, i + 1)) all.push(i);
    if (a.nth && all.length > 1 && all.length === a.nth[1]) at = all[a.nth[0]]!;
    else if (a.at && at >= 0 && at !== t.lastIndexOf(needle)) {
      const lineOf = (i: number) => t.slice(0, i).split("\n").length;
      for (let i = at; i >= 0; i = t.indexOf(needle, i + 1)) if (Math.abs(lineOf(i) - a.at) < Math.abs(lineOf(at) - a.at)) at = i;
    }
    const found = at;
    for (let len = Math.min(needle.length, 80); at < 0 && len >= 12; len -= 4) at = unique(needle.slice(0, len));
    if (at < 0) continue;
    // a line may begin inside a command broken across lines (`\ref{%` / `key}`, `\ref%` / `{key}`):
    // the anchor stands before that command, never in its key or before its argument
    const before = t.slice(0, at);
    const key = /\\(?:(?:eq|c|C|auto|page|name)?ref|label|cite[A-Za-z]*|begin|end|input|include)\*?\s*(?:\[[^\]]*\]\s*)*\{[^{}]*$/.exec(before)
      ?? (/^[{[]/.test(needle) ? /\\[A-Za-z]+\*?(?:\s|%[^\n]*\n|\[[^\]]*\])*$/.exec(before) : null);
    if (key) at = key.index;
    if (a.after) { const nl = t.indexOf("\n", found >= 0 ? found : at); at = nl < 0 ? t.length : nl; }
    out[a.file] = `${t.slice(0, at)}\\tcAnchor${a.after ? "*" : ""}{${a.node.replace(/[{}\\]/g, "")}}${t.slice(at)}`;
  }
  return out;
}

/** Commands in an author block that are no part of a name, with their mandatory-argument count. */
const NOT_NAME: Record<string, number> = {
  thanks: 1, footnote: 1, footnotetext: 1, footnotemark: 0, inst: 1, textsuperscript: 1, affil: 1, affiliation: 1, address: 1,
  email: 1, IEEEauthorrefmark: 1, orcidlink: 1, orcid: 1, url: 1, href: 2, texttt: 1, altaffilmark: 1, protect: 0, date: 1, today: 0,
  medskip: 0, bigskip: 0, smallskip: 0, vspace: 1, vskip: 0,
};
function dropNotName(s: string): string {
  const re = new RegExp(String.raw`\\(${Object.keys(NOT_NAME).join("|")})(?![A-Za-z])\*?`, "g");
  let out = "", last = 0, m: RegExpExecArray | null;
  while ((m = re.exec(s))) {
    let i = m.index + m[0].length;
    const o = optArg(s, i); if (o) i = o.end;
    for (let k = 0; k < NOT_NAME[m[1]!]!; k++) i = arg(s, i).end;
    out += s.slice(last, m.index); last = i; re.lastIndex = i;
  }
  return out + s.slice(last);
}

/**
 * The authors' names from an author block, as TeX joined by ", ": notes, marks ($^{1}$, $^*$),
 * affiliations and addresses (the lines after the first of each author) and contact details go.
 * Pure.
 */
export function authorNames(tex: string): string {
  const s = dropNotName(tex).replace(/\$[^$]*\$/g, "");
  const names: string[] = [];
  for (const part of s.split(/\\(?:and|And|AND)(?![A-Za-z])/)) {
    // the first line that holds anything: an author's name, then their affiliation
    for (const line of part.split(/\\\\(?:\[[^\]]*\])?|\\newline(?![A-Za-z])|\\par(?![A-Za-z])|\n\s*\n/)) {
      const got = line.split(/(?:\\q?quad(?![A-Za-z])|\\hspace\*?\s*\{[^}]*\}|\\hfill(?![A-Za-z])|\\enspace(?![A-Za-z]))+/)
        .map((n) => n.replace(/\\([A-Za-z])\{(\w)\}/g, "\\$1 $2") // \c{c} keeps its letter
          .replace(/\\(?!(?:[cvuHkdbrt]|ss|aa|AA|ae|AE|oe|OE|o|O|l|L|i|j)(?![A-Za-z]))[A-Za-z]+\*?/g, " ")
          .replace(/[{}]/g, "").replace(/\s+/g, " ").replace(/^[\s,;]+|[\s,;]+$/g, ""))
        .filter((n) => n && !n.includes("@"));
      if (got.length) { names.push(...got); break; }
    }
  }
  return names.join(", ");
}

/**
 * Title and authors (TeX). Without a `\title`, the title a paper sets by hand — the first group in a
 * large size before the abstract — with the names after it in its centered block; `span` is that
 * block, for the page to show it once, in its header. Expects comment-free text. Pure.
 */
export function frontMatter(text: string): { title: string; authors: string; span: { from: number; to: number } | null } {
  const args = (cmd: string): string[] => {
    const out: string[] = [];
    const re = new RegExp(String.raw`\\${cmd}(?![A-Za-z])\s*(?=[\[{])`, "g");
    let m: RegExpExecArray | null;
    while ((m = re.exec(text))) { let i = m.index + m[0].length; const o = optArg(text, i); if (o) i = o.end; const a = arg(text, i); out.push(a.body); re.lastIndex = a.end; }
    return out;
  };
  // (journal classes spell the two commands in capitals: INFORMS' `\\TITLE`, `\\AUTHOR`)
  const title = args("title")[0] ?? args("TITLE")[0] ?? "";
  const authors = authorNames((args("author").length ? args("author") : args("AUTHOR")).join(" \\and "));
  if (title) return { title, authors, span: null };
  const start = Math.max(0, text.indexOf("\\begin{document}"));
  const stopAt = text.slice(start).search(/\\begin\{abstract\}|\\section\*?\s*\{|\bABSTRACT\b|\\abstract(?![A-Za-z])/);
  const region = text.slice(start, start + Math.min(stopAt < 0 ? 4000 : stopAt, 4000));
  const m = /\{\s*\\(?:LARGE|Large|huge|Huge)(?![A-Za-z])|\\(?:LARGE|Large|huge|Huge)\s*(?=\{)/.exec(region);
  if (!m) return { title: "", authors, span: null };
  const open = region.indexOf("{", m.index);
  const g = group(region, open);
  if (!g) return { title: "", authors, span: null };
  const handTitle = g.body.replace(/^\s*\\(?:LARGE|Large|huge|Huge)(?![A-Za-z])/, "").trim();
  const center = region.lastIndexOf("\\begin{center}", m.index);
  const cend = center >= 0 ? region.indexOf("\\end{center}", g.end) : -1;
  return {
    title: handTitle,
    authors: authors || authorNames(region.slice(g.end, cend >= 0 ? cend : region.length)),
    span: cend >= 0 ? { from: start + center, to: start + cend + "\\end{center}".length } : { from: start + m.index, to: start + g.end },
  };
}

/**
 * `\if<digit>\switch … \else … \fi` with `\switch` defined as a digit (the journal templates'
 * `\blind`): only the branch that holds. Any other `\if` is left as it is. Pure.
 */
export function resolveDigitIfs(text: string, macros: Preamble["textMacros"]): string {
  return text.replace(/\\if\s*(\d)\s*\\([A-Za-z]+)(?![A-Za-z])([\s\S]*?)\\fi(?![A-Za-z])/g, (m, d: string, name: string, inner: string) => {
    const v = macros[`\\${name}`]?.body.trim();
    if (v === undefined || !/^\d$/.test(v) || /\\if/.test(inner)) return m;
    const [yes, no = ""] = inner.split(/\\else(?![A-Za-z])/);
    return d === v ? yes! : no;
  });
}

/**
 * The text with each use of a `delimited` macro (`\p1*` for `\def\p1*{p^{*}}`) replaced by its body, as
 * TeX expands it, the uses inside bodies too; the definitions stay as written. Pure.
 */
export function expandDelimited(text: string, defs: Preamble["delimited"]): string {
  const names = Object.keys(defs);
  if (!names.length) return text;
  const quote = (x: string) => x.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  // the name (its backslash not an escaped one), the spaces a control word swallows (and one line
  // break), the text it stands before; not the name a `\def` defines
  const use = new RegExp(String.raw`(?<=(?:^|[^\\])(?:\\\\)*)(?<!\\[gex]?def\s*)(?:${names.map((n) => `${quote(n)}(?![A-Za-z])[ \t]*(?:\n[ \t]*)?${quote(defs[n]!.delim)}`).join("|")})`, "g");
  let out = text;
  for (let round = 0; round < 8; round++) {
    const next = out.replace(use, (m, at: number, all: string) => {
      const body = defs[/^\\[A-Za-z]+/.exec(m)![0]]!.body;
      // tokens stay apart, as TeX's are: a control word met by a letter is parted by a space, which it swallows
      const before = /\\[A-Za-z]+$/.test(all.slice(Math.max(0, at - 64), at)) && /^[A-Za-z]/.test(body) ? " " : "";
      const after = /\\[A-Za-z]+$/.test(body) && /^[A-Za-z]/.test(all.slice(at + m.length, at + m.length + 1)) ? " " : "";
      return before + body + after;
    });
    if (next === out) break;
    out = next;
  }
  return out;
}

/** Render a paper (annotated or source) for the paper page. Pure. */
/** The TikZ/PGF setup the paper writes in its body rather than its preamble (`\\tikzset{…}`, a pattern
 *  declared under `\\pgfutil@ifundefined`, `\\usetikzlibrary`, a macro set by `\\def` — a picture's
 *  `\\radius`), each command with its arguments, in the order of the text: the pictures typeset apart
 *  need it. Pure. */
export function tikzSetup(files: Record<string, string>, main: string): string {
  const t = inlineInputs(files, main);
  const body = t.slice(Math.max(0, t.indexOf("\\begin{document}")));
  const out: string[] = [];
  let covered = 0; // a command inside one taken already (a pattern declared under \pgfutil@ifundefined) is in it
  for (const m of body.matchAll(/\\(?:tikzset|usetikzlibrary|pgfutil@ifundefined|pgfdeclarepatternformonly|pgfdeclarepatterninherentlycolored|[gex]?def\s*\\[A-Za-z@]+(?:#\d)*)(?![A-Za-z@])/g)) {
    if (m.index! < covered) continue;
    let i = m.index! + m[0].length;
    // a \def's body is its one group: a later brace group is the text's own
    if (/def\s*\\/.test(m[0])) { if (!/^\s*\{/.test(body.slice(i))) continue; i = arg(body, i).end; covered = i; out.push(body.slice(m.index!, i)); continue; }
    for (;;) {
      const o = optArg(body, i); if (o) { i = o.end; continue; }
      if (/^\s*\{/.test(body.slice(i))) { i = arg(body, i).end; continue; }
      break;
    }
    covered = i;
    out.push(body.slice(m.index!, i));
  }
  return out.join("\n");
}

/** The bodies of the paper's `tikzpicture` environments, in the order of the text (each as the
 *  renderer meets it: what stands between its `\begin` and `\end`). Pure. */
export function tikzPictures(files: Record<string, string>, main: string): string[] {
  const out: string[] = [];
  for (const m of inlineInputs(files, main).matchAll(/\\begin\{tikzpicture\}([\s\S]*?)\\end\{tikzpicture\}/g)) if (!out.includes(m[1]!)) out.push(m[1]!);
  return out;
}

export function renderPaper(input: PaperInput): RenderedPaper {
  return paperRenderer(input).paper;
}

/**
 * The paper, and a renderer for TeX fragments from the run's records (review details, readings,
 * conditions) under the paper's macros and numbering, reporting the formulas neither renderer reads.
 */
export function paperRenderer(input: PaperInput): { paper: RenderedPaper; fragment: (tex: string) => { html: string; failures: MathFailure[] } } {
  const raw = inlineInputs(placeAnchors(input.files, input.anchors), input.main);
  const early = readPreamble(raw);
  const inlined = expandDelimited(resolveDigitIfs(raw, early.textMacros), early.delimited);
  const fm = frontMatter(inlined);
  const full = fm.span ? inlined.slice(0, fm.span.from) + inlined.slice(fm.span.to) : inlined;
  const b = full.indexOf("\\begin{document}");
  const e = full.lastIndexOf("\\end{document}");
  const preText = b >= 0 ? full.slice(0, b) : "";
  let body = b >= 0 ? full.slice(b + "\\begin{document}".length, e > b ? e : undefined) : full;
  const pre = readPreamble(preText);
  // the bibliography's .bbl in its place; its own definitions (`\providecommand{\bysame}…`) are read with the body's
  if (input.bbl && /\\bibliography\{/.test(body)) body = body.replace(/\\bibliography\{[^}]*\}/, () => stripCommentsKeepingUrls(input.bbl!));
  // definitions made inside the body count too (some papers define macros after \begin{document})
  const inBody = readPreamble(body);
  pre.macros = { ...inBody.macros, ...pre.macros };
  pre.textMacros = { ...inBody.textMacros, ...pre.textMacros };
  pre.envDefs = { ...inBody.envDefs, ...pre.envDefs };
  pre.theorems = { ...inBody.theorems, ...pre.theorems };
  pre.numberWithin = { ...inBody.numberWithin, ...pre.numberWithin };
  if (!pre.graphicsPath.length) pre.graphicsPath = inBody.graphicsPath;
  pre.title = fm.title;
  pre.authors = fm.authors;
  body = body.replace(/\\(?:title|author|date)\s*(\[[^\]]*\])?\s*\{/g, (m) => `\\keywords${m.slice(m.indexOf("{"))}`);
  const assets = new Set(input.assets ?? []);
  const health = emptyHealth();
  const aux = readAux(input.aux);
  const mathMacros = katexMacros(pre.macros);
  let mj: ((tex: string, display: boolean) => string) | null = null;
  const mathjax = () => (mj ??= mathjaxRenderer({ ...KATEX_GAPS, ...mathMacros }));
  const refNames: Record<string, string> = {}, refKinds: Record<string, "section" | "appendix"> = {};
  const make = (pass: 1 | 2, own: Record<string, string>, cache: Map<string, string>): Ctx => ({
    pass, pre, aux, own, refNames, refKinds, counters: {}, sec: [], appendix: false, target: "", toc: [], comments: [], envs: [], anchors: {}, readings: {}, pinned,
    envStack: [], splits: {}, umbrellas: { names: [], open: null }, splitKinds: input.splitKinds ?? {}, lastEnv: null, lastEnvEnd: null, marks: 0, footnotes: 0, mathCache: cache, kinds: input.theoremKinds ?? {},
    assets, assetsLower: new Map([...assets].map((a) => [a.toLowerCase(), a])), assetBase: input.assetBase ?? "", tikz: input.tikz ? { url: input.tikz.url, page: new Map(input.tikz.pictures.map((t, k) => [t.replace(/\s+/g, ""), k + 1])) } : null, health, depth: 0, expansions: 0, mathMacros,
    mathOverrides: input.mathOverrides ?? {}, mathjax, toggles: { ...pre.toggles },
  });
  const pinned = (input.readings ?? []).map((r) => ({ node: r.node, key: r.text.replace(/\s+/g, ""), labels: r.labels }))
    .filter((r) => r.key.length >= 8).sort((a, b) => b.key.length - a.key.length);
  // pass 1 numbers every label; pass 2 renders with them
  const own: Record<string, string> = {};
  const cache = new Map<string, string>();
  render(make(1, own, cache), body);
  const ctx = make(2, own, cache);
  const html = proseResults(foldMarks(`<div class="p">${render(ctx, body)}</div>`.replace(/<div class="p">\s*<\/div>/g, "")))
    .replace(new RegExp(`${UMBRELLA_MARK}(\\d+)${UMBRELLA_MARK}`, "g"), (_m, n: string) => esc(umbrellaSentence(ctx.umbrellas.names[Number(n)] ?? [])));
  health.mathErrors = health.mathFailures.length;
  const scratch = emptyHealth();
  const textOf = (t: string) => render({ ...ctx, comments: [], toc: [], envs: [], health: scratch }, t.replace(/\\(?:thanks|footnote)\s*\{(?:[^{}]|\{[^{}]*\})*\}/g, "").replace(/\\\\/g, ", "), true).replace(/<br>/g, ", ").replace(/\s+/g, " ").replace(/(,\s*)+$/, "").replace(/^(,\s*)+/, "").trim();
  const paper: RenderedPaper = {
    title: textOf(pre.title),
    authors: textOf(pre.authors),
    html,
    toc: ctx.toc,
    comments: ctx.comments,
    envs: ctx.envs,
    anchors: ctx.anchors,
    readings: ctx.readings,
    marks: ctx.marks,
    macros: mathMacros,
    pages: aux.pages,
    labels: { ...ctx.own, ...aux.labels },
    health,
  };
  const fragment = (t: string) => {
    const h = emptyHealth();
    const out = render({ ...ctx, counters: { ...ctx.counters }, comments: [], toc: [], envs: [], anchors: {}, envStack: [], health: h }, expandDelimited(t, early.delimited), true);
    return { html: out, failures: h.mathFailures };
  };
  return { paper, fragment };
}
