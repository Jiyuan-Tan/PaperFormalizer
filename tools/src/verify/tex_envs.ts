/**
 * `paperformalizer verify` V1 step 1 — the mechanical LaTeX environment parser.
 *
 * Pure functions over a source tree: flatten `\input`/`\include`, strip comments while
 * keeping a 1:1 line map back to the ORIGINAL files, learn which environment names are
 * theorem-like (`\newtheorem`, thmtools `\declaretheorem`, and `\newenvironment` /
 * `\NewDocumentEnvironment` wrappers around those), and emit every theorem-like
 * environment with its label, title, body, matched proof, section, refs, and a locator
 * in original coordinates. No LLM, no heuristics that fail open: a
 * same-name nesting, or an unterminated `\begin{comment}` is an explicit error.
 *
 * This is regex/state-machine parsing, not a TeX tokenizer. It is deliberately
 * conservative: anything it cannot classify is left out of the environment map rather
 * than guessed at, and everything it does classify carries its source location so the
 * V1.5 referee and the V6 report can point at the paper.
 */
import { mkdir, readFile, rm, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import path from "node:path";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import { blankTexComments } from "../shared/tex_text.js";
import { AUTHOR_NOTES_FILE, NOTE_LOSS_WARNING, NOTE_MACROS_VERSION, loadedPackages, readNotes, type AuthorNotes, type NoteMacroTable, type ShippedFile } from "./note_macros.js";
import { closingPointAfter, openConstructsAt } from "./tex_balance.js";
import {
  VERIFY_FILES,
  type EnvKind,
  type EnvsJson,
  type FlatTexLineMap,
  type TexBibEntry,
  type TexEnv,
  type TexLocator,
} from "./types.js";

/** Origin of one flattened line. */
export interface FlatLine {
  file: string;
  line: number;
}

/** Result of `flattenTex`: the `\input`-folded, comment-stripped document plus the
 * bookkeeping every later step needs. `lineMap[i]` is the origin of flat line `i + 1`,
 * so `text.split("\n").length === lineMap.length` always holds. */
export interface FlatTex {
  text: string;
  lineMap: FlatLine[];
  /** Main file first, then every inlined file in inclusion order, deduplicated. */
  files: string[];
  /** `.bib` file names named by `\bibliography{}` / `\addbibresource{}`, relative to the
   * source dir. */
  bibFiles: string[];
  /** Things the flattener decided NOT to do, in plain words (a repeated `\input`, an
   * `\input` whose name comes from a macro parameter). Never silent, never fatal. */
  warnings: string[];
  /** The authors' note macros read away (`note_macros.ts`); absent: the text is as written. */
  notes?: {
    table: NoteMacroTable;
    /** Null: the flat text on file was kept (`keepFlatOnFile`) — the record on file stands. */
    record: AuthorNotes | null;
    /** For the parse log: one line per macro read. */
    log: string[];
  };
}

/** How the flattener reads the authors' note macros: `true` detects them from the paper's definitions,
 * a table replays the reading a run recorded, `false` reads the paper as written. */
export type NoteMacroSetting = boolean | NoteMacroTable;

// ---------------------------------------------------------------------------
// small TeX scanning helpers
// ---------------------------------------------------------------------------

function skipSpace(text: string, i: number): number {
  while (i < text.length && /\s/.test(text[i]!)) i += 1;
  return i;
}

/** Read one balanced `{…}` / `[…]` group starting at `i` (leading whitespace allowed).
 * `\x` pairs are skipped atomically, and a `{…}` group inside a `[…]` group is skipped
 * whole so a `]` inside braces cannot close it. Returns null when `i` does not open a
 * group of that kind. */
export function readGroup(
  text: string,
  i: number,
  open: "{" | "[",
): { value: string; end: number } | null {
  const close = open === "{" ? "}" : "]";
  const j = skipSpace(text, i);
  if (text[j] !== open) return null;
  let depth = 0;
  for (let k = j; k < text.length; k += 1) {
    const ch = text[k]!;
    if (ch === "\\") {
      k += 1;
      continue;
    }
    if (ch === open) {
      depth += 1;
      continue;
    }
    if (ch === close) {
      depth -= 1;
      if (depth === 0) return { value: text.slice(j + 1, k), end: k + 1 };
      continue;
    }
    if (open === "[" && ch === "{") {
      // skip a brace group atomically
      let d = 0;
      for (; k < text.length; k += 1) {
        const c = text[k]!;
        if (c === "\\") {
          k += 1;
          continue;
        }
        if (c === "{") d += 1;
        else if (c === "}") {
          d -= 1;
          if (d === 0) break;
        }
      }
    }
  }
  return null;
}

// ---------------------------------------------------------------------------
// comment / verbatim / conditional stripping (line-count preserving)
// ---------------------------------------------------------------------------

/**
 * Replace every region a forward scan reports with just its newlines, so every later
 * line keeps its original number.
 *
 * `next(from)` is called with the offset just past the previous region and must return
 * a region starting at or after it. The whole strip is ONE pass with ONE join: the
 * older "search from index 0 and rebuild the string on every hit" loop was quadratic in
 * the number of blocks (and in the document length).
 */
function blankRegions(
  text: string,
  next: (from: number) => { start: number; end: number } | null,
): string {
  const pieces: string[] = [];
  let cursor = 0;
  for (;;) {
    const region = next(cursor);
    if (!region) break;
    if (region.start < cursor || region.end < region.start) {
      throw new Error("internal: blankRegions scanned backwards");
    }
    pieces.push(text.slice(cursor, region.start));
    pieces.push(text.slice(region.start, region.end).replace(/[^\n]/g, ""));
    cursor = region.end;
  }
  pieces.push(text.slice(cursor));
  return pieces.join("");
}

/** Environments whose body is LITERAL TEXT, not TeX. Everything inside one is displayed,
 * not executed: a `\begin{theorem}` in a listing is an example, an `\end{document}` in
 * one does not end the document, a `\newtheorem` in one declares nothing, and an
 * `\input{}` in one includes nothing. Their bodies are blanked before any of those are
 * read. */
const VERBATIM_ENVS = [
  "verbatim",
  "verbatim*",
  "lstlisting",
  "lstlisting*",
  "minted",
  "minted*",
  "alltt",
  "alltt*",
  "Verbatim",
  "Verbatim*",
  "BVerbatim",
  "BVerbatim*",
  "LVerbatim",
  "LVerbatim*",
] as const;

const escapeEnvName = (name: string): string => name.replace(/\*/g, "\\*");

const VERBATIM_BEGIN_RE = new RegExp(
  String.raw`\\begin\s*\{(${VERBATIM_ENVS.map(escapeEnvName).join("|")})\}`,
  "g",
);

/** Blank `\begin{verbatim}…\end{verbatim}` and its relatives, delimiters included. */
function stripVerbatimEnvs(text: string, file: string): string {
  return blankRegions(text, (from) => {
    VERBATIM_BEGIN_RE.lastIndex = from;
    const begin = VERBATIM_BEGIN_RE.exec(text);
    if (!begin) return null;
    const name = begin[1]!;
    const endRe = new RegExp(String.raw`\\end\s*\{${escapeEnvName(name)}\}`, "g");
    endRe.lastIndex = begin.index + begin[0].length;
    const end = endRe.exec(text);
    if (!end) {
      throw new Error(`${file}: unterminated \\begin{${name}} (no \\end{${name}} follows)`);
    }
    return { start: begin.index, end: end.index + end[0].length };
  });
}

/** `\verb<c>…<c>` (and the `\lstinline` / `\mintinline` equivalents, which also accept a
 * braced body): same literal-text rule as the verbatim environments, one line at a time.
 * The trailing lookahead keeps `\verbatim` from reading as `\verb`. */
const INLINE_VERB_RE = /\\(verb|lstinline|mintinline)\*?(?![a-zA-Z@])/g;

function stripInlineVerb(text: string): string {
  return blankRegions(text, (from) => {
    INLINE_VERB_RE.lastIndex = from;
    const m = INLINE_VERB_RE.exec(text);
    if (!m) return null;
    const after = m.index + m[0].length;
    /** Unrecognised shape: blank nothing, but advance past the command so the scan
     * cannot loop on it. */
    const skip = { start: after, end: after };
    let i = after;
    const cmd = m[1]!;
    if (cmd !== "verb") {
      const opts = readGroup(text, i, "[");
      if (opts) i = opts.end;
      if (cmd === "mintinline") {
        const lang = readGroup(text, i, "{");
        if (lang) i = lang.end;
      }
      const braced = readGroup(text, i, "{");
      if (braced) return { start: m.index, end: braced.end };
    }
    const open = text[i];
    if (!open || /\s/.test(open)) return skip;
    const close = text.indexOf(open, i + 1);
    const eol = text.indexOf("\n", i + 1);
    if (close < 0 || (eol >= 0 && close > eol)) return skip;
    return { start: m.index, end: close + 1 };
  });
}

/** Blank `\begin{comment}…\end{comment}` blocks. */
function stripCommentEnvs(text: string, file: string): string {
  const beginRe = /\\begin\s*\{comment\}/g;
  return blankRegions(text, (from) => {
    beginRe.lastIndex = from;
    const begin = beginRe.exec(text);
    if (!begin) return null;
    const endRe = /\\end\s*\{comment\}/g;
    endRe.lastIndex = begin.index + begin[0].length;
    const end = endRe.exec(text);
    if (!end) {
      throw new Error(`${file}: unterminated \\begin{comment} (no \\end{comment} follows)`);
    }
    return { start: begin.index, end: end.index + end[0].length };
  });
}

/** Blank `\iffalse…(\else|\fi)` blocks, honouring nested `\if…\fi` pairs. */
export function stripIffalse(text: string, file: string): string {
  const beginRe = /\\iffalse(?![a-zA-Z@])/g;
  return blankRegions(text, (from) => {
    beginRe.lastIndex = from;
    const begin = beginRe.exec(text);
    if (!begin) return null;
    const token = /\\(if[a-zA-Z@]*|else|fi)(?![a-zA-Z@])/g;
    token.lastIndex = begin.index + begin[0].length;
    let depth = 1;
    for (let m = token.exec(text); m; m = token.exec(text)) {
      const name = m[1]!;
      // `\iff` (amsmath) and `\ifthenelse` (ifthen) are macros, not conditionals: TeX skipping the block does not count them
      if (name === "iff" || name === "ifthenelse") continue;
      if (name.startsWith("if")) depth += 1;
      else if (name === "fi") {
        depth -= 1;
        if (depth === 0) return { start: begin.index, end: m.index + m[0].length };
      } else if (name === "else" && depth === 1) {
        return { start: begin.index, end: m.index + m[0].length };
      }
    }
    throw new Error(`${file}: unterminated \\iffalse (no matching \\else or \\fi)`);
  });
}

/** The etoolbox toggles a text sets: `\newtoggle{t}` (false), `\toggletrue`/`\togglefalse`, `\settoggle{t}{true|false}`;
 *  the last setting of a name wins. Read it from text with its comments and `\iffalse` blocks blanked. */
export function readToggles(text: string): Record<string, boolean> {
  const out: Record<string, boolean> = {};
  for (const m of text.matchAll(/\\(newtoggle|providetoggle|toggletrue|togglefalse|settoggle)\s*\{([^{}]*)\}(?:\s*\{\s*(true|false)\s*\})?/g)) {
    const [, cmd, name, val] = m;
    const t = name!.trim();
    if (cmd === "newtoggle" || cmd === "providetoggle") out[t] ??= false;
    else out[t] = cmd === "toggletrue" || (cmd === "settoggle" && val === "true");
  }
  return out;
}

/** Blank the branch of every `\iftoggle{t}{yes}{no}` / `\nottoggle{t}{yes}{no}` that the toggles do not select,
 *  keeping the line count; the selected branch is left as written. A toggle the text never sets (one set in a
 *  package, or a macro parameter `#1`) blanks neither branch: which one TeX reads is not known here. */
export function blankInactiveToggles(text: string, toggles: Record<string, boolean>): string {
  const span = (from: number): { start: number; end: number } | null => {
    const g = readGroup(text, from, "{");
    return g ? { start: g.end - g.value.length - 2, end: g.end } : null;
  };
  const blank: Array<{ start: number; end: number }> = [];
  for (const m of text.matchAll(/\\(iftoggle|nottoggle)(?![A-Za-z@])/g)) {
    const t = readGroup(text, m.index! + m[0].length, "{");
    const yes = t && span(t.end);
    const no = yes && span(yes.end);
    const on = t ? toggles[t.value.trim()] : undefined;
    if (!yes || !no || on === undefined) continue;
    blank.push(on === (m[1] === "iftoggle") ? no : yes);
  }
  let out = "";
  let at = 0;
  for (const b of blank.sort((x, y) => x.start - y.start)) {
    if (b.start < at) continue;
    out += text.slice(at, b.start) + text.slice(b.start, b.end).replace(/[^\n]/g, " ");
    at = b.end;
  }
  return out + text.slice(at);
}

/**
 * Strip everything that is not document content, keeping the line count intact:
 * `%` comments (with `\%` honoured — `stripTexCommentsJoining` scans escape pairs atomically),
 * literal-text blocks (`verbatim` and relatives, inline `\verb`), `\begin{comment}…`
 * blocks, and `\iffalse…\else|\fi` blocks.
 *
 * Order matters. `%` comments go first, so a commented-out `\begin{verbatim}` never
 * opens a literal block; literal blocks go next, so nothing a listing merely DISPLAYS
 * (`\end{document}`, `\input{}`, `\newtheorem`, `\begin{theorem}`) is read as markup by
 * the passes and callers that follow.
 *
 * A `%` GLUED to the preceding character joins its line with the next, as TeX does
 * (`$%⏎u$` is `$u$`; left split, the escaped form `$\nu$` misreads as a Greek letter). A
 * comment after a space, or on a line of its own, keeps its line break: there the join
 * changes nothing a reader sees. The swallowed break is not re-emitted (a blank line after the
 * joined line would be a paragraph break, which ends a formula split across lines);
 * `origins`, when given, receives each output line's 1-based source line instead, so a
 * locator inside a joined line names the line it starts on.
 */
export function stripCommentary(text: string, file: string, origins?: number[]): string {
  let out = stripTexCommentsJoining(text, origins);
  out = stripVerbatimEnvs(out, file);
  out = stripInlineVerb(out);
  out = stripCommentEnvs(out, file);
  out = stripIffalse(out, file);
  return out;
}

/** Strip TeX `%` comments, with TeX's line join for a `%` glued to the preceding character (see
 * `stripCommentary`); `\%` is honoured by scanning escape pairs atomically. `origins` receives
 * each output line's 1-based source line. */
export function stripTexCommentsJoining(tex: string, origins: number[] = []): string {
  let out = "";
  let line = 1; // the source line being read
  origins.length = 0;
  origins.push(1);
  let glued = false; // the previous character is non-blank text
  for (let i = 0; i < tex.length; i += 1) {
    const ch = tex[i]!;
    if (ch === "\\") {
      // Inside `\verb<c>…<c>` (or `\lstinline`) a `%` is literal: the span is copied whole.
      const span = inlineVerbSpanAt(tex, i);
      if (span > i) {
        out += tex.slice(i, span);
        glued = true;
        i = span - 1;
        continue;
      }
      // `\` ending a line (a control space): the newline is still the line's end, counted below
      if (tex[i + 1] === "\n") {
        out += ch;
        glued = true;
        continue;
      }
      out += tex.slice(i, i + 2);
      glued = true;
      i += 1;
      continue;
    }
    if (ch === "%") {
      while (i < tex.length && tex[i] !== "\n") i += 1;
      if (i >= tex.length) break;
      line += 1;
      if (!glued) {
        out += "\n";
        origins.push(line);
        continue;
      }
      let j = i + 1;
      while (j < tex.length && (tex[j] === " " || tex[j] === "\t")) j += 1;
      i = j - 1;
      continue;
    }
    if (ch === "\n") {
      out += "\n";
      line += 1;
      origins.push(line);
      glued = false;
      continue;
    }
    glued = ch !== " " && ch !== "\t" && ch !== "\r";
    out += ch;
  }
  return out;
}

/** The end (exclusive) of the `\verb<c>…<c>` / `\lstinline[opts]<c>…<c>` span opening at `at`
 * (a `{` delimiter closes with `}`), or `at` when none opens there or it does not close on its line. */
function inlineVerbSpanAt(tex: string, at: number): number {
  const m = /^\\(?:verb|lstinline)\*?(?![a-zA-Z@])(?:\[[^\]\n]*\])?([^\s])/.exec(tex.slice(at, at + 64));
  if (!m) return at;
  const open = m[1]!;
  const from = at + m[0].length;
  const close = tex.indexOf(open === "{" ? "}" : open, from);
  const eol = tex.indexOf("\n", from);
  return close < 0 || (eol >= 0 && close > eol) ? at : close + 1;
}

// ---------------------------------------------------------------------------
// flattening
// ---------------------------------------------------------------------------

/** `\input{x}` / `\include{x}` / `\input x` / `\subfile{x}`. The negative lookahead is
 * load-bearing: without it `\includegraphics` and `\inputencoding` are read as inclusions. */
const INCLUDE_RE = /\\(input|include|subfile)(?![a-zA-Z@])\s*(?:\{([^{}]*)\}|([^\s{}\\%,]+))/;
const BIB_RE = /\\(bibliography|addbibresource)(?![a-zA-Z@])\s*(?:\[[^\]]*\])?\{([^{}]*)\}/g;

function toPosix(rel: string): string {
  return rel.split(path.sep).join("/");
}

/** Resolve an `\input` target against the including file's directory and the source
 * root, appending `.tex` when the name carries no extension. Throws when nothing
 * exists (never fails open) or when the target escapes the source tree. */
function resolveInclude(
  sourceDir: string,
  fromFile: string,
  target: string,
  atLine: number,
): string {
  const raw = target.trim().replace(/^"|"$/g, "");
  const names = /\.[A-Za-z0-9]+$/.test(raw) ? [raw, `${raw}.tex`] : [`${raw}.tex`, raw];
  const bases = [path.dirname(path.resolve(sourceDir, fromFile)), sourceDir];
  for (const base of bases) {
    for (const name of names) {
      const abs = path.resolve(base, name);
      const rel = path.relative(sourceDir, abs);
      if (rel.startsWith("..") || path.isAbsolute(rel)) {
        throw new Error(
          `${fromFile}:${atLine}: \\input{${raw}} resolves outside the source tree (${abs})`,
        );
      }
      if (existsSync(abs)) return toPosix(rel);
    }
  }
  throw new Error(
    `${fromFile}:${atLine}: \\input{${raw}} not found (tried ${names.join(", ")} relative to ` +
      `${toPosix(path.relative(sourceDir, bases[0]!)) || "."} and the source root)`,
  );
}

/** Hard stops, so a pathological source tree fails with a message instead of hanging:
 * how deep `\input` may nest, and how many lines the flattened document may reach. */
const MAX_INPUT_DEPTH = 32;
const MAX_FLAT_LINES = 400_000;

interface FlattenAcc {
  sourceDir: string;
  mainBase: string;
  files: string[];
  bibFiles: string[];
  lines: string[];
  lineMap: FlatLine[];
  bblInlined: Set<string>;
  /** Every file already folded in, for the WHOLE run — not just the current `\input`
   * chain. A file reached by two acyclic paths is inlined ONCE. LaTeX would typeset it
   * twice, but a verify run never wants a theorem to appear twice (it would double
   * every environment and make the ids ambiguous), and on a diamond-shaped include
   * graph re-inlining is exponential: 14 levels of double `\input` is 16384 copies. */
  inlined: Set<string>;
  warnings: string[];
}

function push(acc: FlattenAcc, text: string, file: string, line: number): void {
  if (acc.lines.length >= MAX_FLAT_LINES) {
    throw new Error(
      `flattened source exceeds ${MAX_FLAT_LINES} lines at ${file}:${line} — refusing to ` +
        `continue (a runaway \\input chain?)`,
    );
  }
  acc.lines.push(text);
  acc.lineMap.push({ file, line });
}

async function inlineFile(
  acc: FlattenAcc,
  rel: string,
  stack: string[],
  via: string | null,
): Promise<void> {
  if (stack.includes(rel)) {
    throw new Error(`\\input cycle: ${[...stack, rel].join(" -> ")}`);
  }
  if (acc.inlined.has(rel)) {
    acc.warnings.push(
      `${via ?? "source"}: ${rel} is included more than once; the repeat was skipped ` +
        `(each file is folded in once per run)`,
    );
    return;
  }
  if (stack.length >= MAX_INPUT_DEPTH) {
    throw new Error(
      `\\input nested deeper than ${MAX_INPUT_DEPTH} at ${via ?? rel}: ` +
        `${[...stack, rel].join(" -> ")}`,
    );
  }
  acc.inlined.add(rel);
  const abs = path.resolve(acc.sourceDir, rel);
  if (!existsSync(abs)) throw new Error(`source file not found: ${rel}`);
  const raw = await readFile(abs, "utf8");
  const origins: number[] = [];
  let text = stripCommentary(raw.replace(/\r\n?/g, "\n"), rel, origins);
  if (via !== null && /\\documentclass/.test(text)) {
    // A `subfiles` child (`\documentclass[../main.tex]{subfiles}` … `\begin{document}` …
    // `\end{document}`) compiles alone but is included as a body. Blank its own preamble
    // and closing line rather than delete them, so the line map stays 1:1.
    const begin = /\\begin\s*\{document\}/.exec(text);
    if (begin) {
      const head = text.slice(0, begin.index + begin[0].length);
      text = head.replace(/[^\n]/g, "") + text.slice(head.length);
    }
    text = text.replace(/\\end\s*\{document\}/g, "");
  }
  if (!acc.files.includes(rel)) acc.files.push(rel);
  const nested = [...stack, rel];
  const lines = text.split("\n");
  for (let i = 0; i < lines.length; i += 1) {
    const lineNo = origins[i] ?? i + 1;
    const line = lines[i]!;
    for (const m of line.matchAll(BIB_RE)) {
      for (const name of m[2]!.split(",")) {
        const trimmed = name.trim();
        if (!trimmed) continue;
        const bib = /\.bib$/.test(trimmed) ? trimmed : `${trimmed}.bib`;
        if (!acc.bibFiles.includes(bib)) acc.bibFiles.push(bib);
      }
    }
    if (!INCLUDE_RE.test(line)) {
      push(acc, line, rel, lineNo);
      if (/\\bibliography(?![a-zA-Z@])/.test(line)) await inlineBbl(acc, nested);
      continue;
    }
    let rest = line;
    for (;;) {
      const m = INCLUDE_RE.exec(rest);
      if (!m) {
        if (rest.trim()) push(acc, rest, rel, lineNo);
        break;
      }
      const prefix = rest.slice(0, m.index);
      if (prefix.trim()) push(acc, prefix, rel, lineNo);
      const target = m[2] ?? m[3] ?? "";
      if (target.includes("#")) {
        // `\newcommand{\myinput}[1]{\input{#1}}`: the file name is a macro parameter, so
        // there is nothing to resolve here. Skipping is right; failing the run is not.
        acc.warnings.push(
          `${rel}:${lineNo}: \\${m[1]}{${target}} names its file through a macro parameter; ` +
            `skipped (the parser does not expand macros)`,
        );
        rest = rest.slice(m.index + m[0].length);
        continue;
      }
      let child: string;
      try {
        child = resolveInclude(acc.sourceDir, rel, target, lineNo);
      } catch (err) {
        // A file the bundle does not ship (a converter's macro file such as `tcilatex`, a
        // style fragment) cannot hold the paper's results; say so and go on. A target that
        // escapes the source tree is still an error.
        const msg = err instanceof Error ? err.message : String(err);
        if (!/not found/.test(msg)) throw err;
        acc.warnings.push(`${msg}; skipped (the bundle does not ship it — check that no result lived there)`);
        rest = rest.slice(m.index + m[0].length);
        continue;
      }
      await inlineFile(acc, child, nested, `${rel}:${lineNo}`);
      rest = rest.slice(m.index + m[0].length);
    }
    if (/\\bibliography(?![a-zA-Z@])/.test(line)) await inlineBbl(acc, nested);
  }
}

/** `\bibliography{…}` makes LaTeX read `\jobname.bbl`. arXiv sources ship that file
 * rather than the `.bib`, and it is what carries the `\bibitem` bodies, so fold it in
 * where the `\bibliography` command sits. Absent (a source that ships only the `.bib`),
 * this is a no-op. */
async function inlineBbl(acc: FlattenAcc, stack: string[]): Promise<void> {
  const bbl = `${acc.mainBase}.bbl`;
  if (acc.bblInlined.has(bbl)) return;
  if (!existsSync(path.resolve(acc.sourceDir, bbl))) return;
  acc.bblInlined.add(bbl);
  await inlineFile(acc, bbl, stack, `${acc.mainBase}.tex`);
}

/** The `.sty` / `.cls` files `flat` loads that the source tree ships, in loading order (a shipped
 * package's own loads followed). */
async function shippedStyleFiles(sourceDir: string, flat: string): Promise<ShippedFile[]> {
  const out: ShippedFile[] = [];
  const seen = new Set<string>();
  const visit = async (text: string): Promise<void> => {
    for (const name of loadedPackages(text)) {
      for (const ext of ["sty", "cls"]) {
        const rel = `${name}.${ext}`;
        const abs = path.resolve(sourceDir, rel);
        if (seen.has(rel) || path.relative(sourceDir, abs).startsWith("..") || !existsSync(abs)) continue;
        seen.add(rel);
        const body = blankTexComments((await readFile(abs, "latin1")).replace(/\r\n?/g, "\n"));
        await visit(body);
        out.push({ name: rel, text: body });
      }
    }
  };
  await visit(flat);
  return out;
}

/** Fold `\input`/`\include` into one text, strip commentary, read the authors' note macros away
 * (`noteMacros`, `note_macros.ts`: every line stays where it is), and record where every flat line
 * came from. */
export async function flattenTex(sourceDir: string, mainFile: string, noteMacros: NoteMacroSetting = true): Promise<FlatTex> {
  const main = toPosix(mainFile);
  const acc: FlattenAcc = {
    sourceDir,
    mainBase: main.replace(/\.tex$/i, ""),
    files: [],
    bibFiles: [],
    lines: [],
    lineMap: [],
    bblInlined: new Set(),
    inlined: new Set(),
    warnings: [],
  };
  await inlineFile(acc, main, [], null);
  const flat: FlatTex = {
    text: acc.lines.join("\n"),
    lineMap: acc.lineMap,
    files: acc.files,
    bibFiles: acc.bibFiles,
    warnings: acc.warnings,
  };
  if (noteMacros === false) return flat;
  const read = readNotes(flat.text, flat.lineMap, noteMacros === true ? await shippedStyleFiles(sourceDir, flat.text) : [], noteMacros === true ? undefined : noteMacros);
  return { ...flat, text: read.text, warnings: [...flat.warnings, ...read.warnings], notes: { table: read.table, record: read.notes, log: read.log } };
}

/** The reading a run on file was flattened with (`envs.json` `note_macros`): its table, or `false`
 * for a run read as written — the setting that flattens its source to its `flat.tex` again. */
export async function recordedNoteMacros(runDir: string): Promise<NoteMacroSetting> {
  const file = path.join(runDir, VERIFY_FILES.envsJson);
  if (!existsSync(file)) return false;
  return (JSON.parse(await readFile(file, "utf8")) as EnvsJson).note_macros ?? false;
}

/**
 * A run replaying its recorded reading of the note macros must get the flat text it has: the rules for
 * a use are code, and a transcription on file references that text by position. When this reader
 * replays the table to another text, the text on file is kept (with its line map and its record of
 * removed notes) and a warning says so; the paper is read again only on a cold extraction.
 */
async function keepFlatOnFile(runDir: string, flat: FlatTex): Promise<FlatTex> {
  const file = path.join(runDir, VERIFY_FILES.flatTex);
  const mapFile = path.join(runDir, VERIFY_FILES.flatLineMap);
  if (!flat.notes || !existsSync(file) || !existsSync(mapFile)) return flat;
  const text = await readFile(file, "utf8");
  if (text === flat.text) return flat;
  const { lineMap } = JSON.parse(await readFile(mapFile, "utf8")) as FlatTexLineMap;
  const v = flat.notes.table.version;
  return {
    ...flat,
    text,
    lineMap,
    warnings: [
      ...flat.warnings.filter((w) => !w.startsWith("note macros:") && !w.startsWith("the paper was read with")),
      `note macros: this run was read under ${v === NOTE_MACROS_VERSION ? "another" : `an older (version ${v}; this reader is version ${NOTE_MACROS_VERSION})`} reading of its authors' note macros; ` +
        `its ${VERIFY_FILES.flatTex} on file is kept as it is (the transcription refers to it) — the paper is read again only on a cold extraction`,
    ],
    notes: { table: flat.notes.table, record: null, log: [] },
  };
}

/** Every hidden text or author's comment removed inside a statement or a proof, named by its result
 * (`<id> (<file>:<from>-<to>)`: the V1.5 prompt shows the line to whoever grades that result) — and
 * whether the text lost all, or more than half, of what it had: the author may have wrapped real
 * content in a note macro. */
function noteLossWarnings(envs: readonly TexEnv[], flat: FlatTex): string[] {
  const removed = flat.notes?.record?.removed ?? [];
  const out: string[] = [];
  const size = (t: string): number => t.replace(/\\label\s*\{[^{}]*\}|\{\}|\s/g, "").length;
  for (const e of envs) {
    for (const [what, loc, text] of [["statement", e.lines, e.body], ["proof", e.proofLines, e.proof]] as const) {
      const here = loc ? removed.filter((r) => r.file === loc.file && r.line >= loc.from && r.line <= loc.to) : [];
      if (here.length === 0) continue;
      const gone = here.reduce((n, r) => n + size(r.text), 0);
      const kept = size(text ?? "");
      const lost = kept === 0 ? `; the ${what} has NO text left` : gone > kept ? `; the ${what} lost more than half of its text` : "";
      for (const r of here) {
        const shown = r.text.replace(/\s+/g, " ");
        out.push(
          `${NOTE_LOSS_WARNING} ${what} of ${e.id} (${loc!.file}:${loc!.from}-${loc!.to}): ${r.macro}{…} at line ${r.line} was removed as ${r.class === "hide" ? "hidden text" : "an author's comment"} ` +
            `(${size(r.text)} characters: "${shown.length > 80 ? `${shown.slice(0, 80)}…` : shown}")${lost} — check that none of it is the paper's (${AUTHOR_NOTES_FILE})`,
        );
      }
    }
  }
  return out;
}

// ---------------------------------------------------------------------------
// theorem-environment map
// ---------------------------------------------------------------------------

/** The theorem-like environment names every paper may use without `\\newtheorem`, and the kind each stands for. */
export const BUILTIN_ENVS: Readonly<Record<string, EnvKind>> = {
  theorem: "theorem",
  thm: "theorem",
  lemma: "lemma",
  lem: "lemma",
  proposition: "proposition",
  prop: "proposition",
  corollary: "corollary",
  cor: "corollary",
  definition: "definition",
  defn: "definition",
  def: "definition",
  assumption: "assumption",
  assum: "assumption",
  assump: "assumption",
  ass: "assumption",
  cond: "assumption",
  hyp: "assumption",
  remark: "remark",
  rem: "remark",
  example: "example",
  ex: "example",
  // pseudocode: the `algorithm` float (algorithm / algorithm2e packages) and a bare `algorithmic`
  // block. `other` + an algorithm name makes them core-bearing (`isAlgorithmEnv`): each becomes a
  // definition node.
  algorithm: "other",
  algorithmic: "other",
};

/**
 * Kind implied by a theorem environment's printed title (or, failing that, its name).
 * Case-insensitive; macros and braces are dropped first so `{\bf Theorem}` still reads
 * as a theorem.
 *
 * The house rule for titles amsthm does not name: an environment holding something the
 * paper ASSERTS and expects to be true — a Claim, a Result, a Fact, an Observation — is
 * a `proposition`, because the verify pipeline must carry it into the core and check it.
 * A Conjecture is deliberately NOT one: the paper does not claim to prove it, so it is
 * `other` (context only), like a Remark or an Example.
 */
export function kindFromTitle(title: string): EnvKind {
  const t = title
    .toLowerCase()
    .replace(/\\[a-zA-Z@]+/g, " ")
    .replace(/[{}$*]/g, " ");
  if (/theorem/.test(t)) return "theorem";
  if (/lemma/.test(t)) return "lemma";
  if (/proposition/.test(t)) return "proposition";
  if (/corollar/.test(t)) return "corollary";
  if (/definition/.test(t)) return "definition";
  if (/assumption|condition|hypothes|specification|requirement|postulate/.test(t)) return "assumption";
  if (/conjectur/.test(t)) return "other";
  if (/\bclaims?\b|\bresults?\b|\bfacts?\b|\bobservations?\b/.test(t)) return "proposition";
  if (/remark|note/.test(t)) return "remark";
  if (/example/.test(t)) return "example";
  return "other";
}

/** How an environment takes its arguments, learned from a `\newenvironment` /
 * `\NewDocumentEnvironment` wrapper. */
export interface EnvSignature {
  /** One entry per argument, in order: `m` mandatory, `o` optional, `s` star. */
  argSpec: Array<"m" | "o" | "s">;
  /** `\label{…}` the wrapper emits, with `#k` placeholders, e.g. `obj:#1`. */
  labelTemplate: string | null;
  /** Environment the wrapper opens, e.g. `theorem` — the kind is inherited from it. */
  wraps: string | null;
}

function parseDocumentArgSpec(spec: string): Array<"m" | "o" | "s"> {
  const out: Array<"m" | "o" | "s"> = [];
  for (let i = 0; i < spec.length; i += 1) {
    const ch = spec[i]!;
    if (/\s|[+!]/.test(ch)) continue;
    if (ch === "m") out.push("m");
    else if (ch === "o") out.push("o");
    else if (ch === "s") out.push("s");
    else if (ch === "O") {
      const g = readGroup(spec, i + 1, "{");
      if (g) i = g.end - 1;
      out.push("o");
    } else if (ch === "d" || ch === "D") {
      i += 2;
      if (ch === "D") {
        const g = readGroup(spec, i + 1, "{");
        if (g) i = g.end - 1;
      }
      out.push("o");
    } else if (ch === "r" || ch === "R") {
      i += 2;
      if (ch === "R") {
        const g = readGroup(spec, i + 1, "{");
        if (g) i = g.end - 1;
      }
      out.push("m");
    }
    // e/E (embellishments) and anything else: ignored — the env then parses fewer
    // arguments than it really takes, which only ever leaves extra text in `body`.
  }
  return out;
}

const NEW_DOC_ENV_RE =
  /\\(?:New|Renew|Provide|Declare)DocumentEnvironment\s*\*?\s*\{([^{}]+)\}/g;
const NEW_ENV_RE = /\\(?:new|renew)environment\s*\*?\s*\{([^{}]+)\}/g;

/** Argument signatures of every `\newenvironment` / `\NewDocumentEnvironment` wrapper,
 * so `\begin{theoremv}{anchor}[title]*` can be read the same way as a plain
 * `\begin{theorem}[title]`. */
export function parseEnvSignatures(text: string): Record<string, EnvSignature> {
  const out: Record<string, EnvSignature> = {};
  const record = (
    name: string,
    argSpec: Array<"m" | "o" | "s">,
    begin: string | null,
  ): void => {
    const label = begin ? /\\label\s*\{([^{}]*)\}/.exec(begin) : null;
    const wraps = begin ? /\\begin\s*\{([^{}#]+)\}/.exec(begin) : null;
    out[name.trim()] = {
      argSpec,
      labelTemplate: label ? label[1]! : null,
      wraps: wraps ? wraps[1]!.trim() : null,
    };
  };
  for (const m of text.matchAll(NEW_DOC_ENV_RE)) {
    const after = m.index + m[0].length;
    const spec = readGroup(text, after, "{");
    if (!spec) continue;
    const begin = readGroup(text, spec.end, "{");
    record(m[1]!, parseDocumentArgSpec(spec.value), begin ? begin.value : null);
  }
  for (const m of text.matchAll(NEW_ENV_RE)) {
    let i = m.index + m[0].length;
    const count = readGroup(text, i, "[");
    let argSpec: Array<"m" | "o" | "s"> = [];
    if (count) {
      i = count.end;
      const n = Number.parseInt(count.value.trim(), 10);
      const dflt = readGroup(text, i, "[");
      if (dflt) i = dflt.end;
      if (Number.isFinite(n) && n > 0) {
        argSpec = Array.from({ length: n }, (_, k) => (k === 0 && dflt ? "o" : "m"));
      }
    }
    const begin = readGroup(text, i, "{");
    record(m[1]!, argSpec, begin ? begin.value : null);
  }
  return out;
}

const NEWTHEOREM_RE = /\\newtheorem\s*(\*?)\s*\{([^{}]+)\}/g;
const DECLARETHEOREM_RE = /\\declaretheorem\s*(?=[[{])/g;

/** Read the paper's theorem-environment declarations: `\newtheorem` in all four amsthm
 * shapes, thmtools `\declaretheorem`, and `\newenvironment` wrappers around either.
 * Merged over the built-in defaults, so a paper that declares nothing still parses. */
export function parseNewtheorems(text: string): Record<string, EnvKind> {
  const map: Record<string, EnvKind> = { ...BUILTIN_ENVS };
  for (const m of text.matchAll(NEWTHEOREM_RE)) {
    const name = m[2]!.trim();
    let i = m.index + m[0].length;
    const counter = readGroup(text, i, "["); // \newtheorem{x}[shared]{Title}
    if (counter) i = counter.end;
    const title = readGroup(text, i, "{");
    map[name] = kindFromTitle(title ? title.value : name);
  }
  for (const m of text.matchAll(DECLARETHEOREM_RE)) {
    let i = m.index + m[0].length;
    const opts = readGroup(text, i, "[");
    if (opts) i = opts.end;
    const nameGroup = readGroup(text, i, "{");
    if (!nameGroup) continue;
    const declared = /(?:^|,)\s*(?:name|title|Name)\s*=\s*([^,\]]*)/.exec(opts?.value ?? "");
    for (const name of nameGroup.value.split(",")) {
      const env = name.trim();
      if (!env) continue;
      map[env] = kindFromTitle((declared ? declared[1]! : "").replace(/[{}]/g, "").trim() || env);
    }
  }
  for (const [name, sig] of Object.entries(parseEnvSignatures(text))) {
    if (sig.wraps && map[sig.wraps]) {
      map[name] = map[sig.wraps]!;
    } else if (sig.labelTemplate) {
      // An anchored object environment that does not wrap a theorem env: keep it (it is
      // a numbered, labelled, referenceable object) but classify it only by its name.
      map[name] = kindFromTitle(name);
    }
  }
  return map;
}

/**
 * How the theorem-like environments are NUMBERED: the counter each environment steps, what
 * resets that counter (`[section]`), and the word it prints ("Theorem"). Reproduced only so
 * that a proof announced by printed number — `\begin{proof}[Proof of Theorem 3.1]`,
 * `\subsection{Proof of Lemma 2}` — can be bound to its result when no `\ref` is given.
 */
export interface TheoremCounters {
  /** env name → counter name (`\newtheorem{lem}[thm]{Lemma}` steps `thm`) */
  counterOf: Record<string, string>;
  /** counter name → what resets it */
  resetBy: Record<string, "section" | "subsection" | null>;
  /** env name → printed word */
  display: Record<string, string>;
}

const NUMBERWITHIN_RE = /\\numberwithin\s*\{([^{}]+)\}\s*\{([^{}]+)\}/g;

export function parseTheoremCounters(text: string): TheoremCounters {
  const out: TheoremCounters = { counterOf: {}, resetBy: {}, display: {} };
  const within = (w: string | undefined): "section" | "subsection" | null =>
    w === undefined ? null : /subsection/.test(w) ? "subsection" : /section|chapter/.test(w) ? "section" : null;
  for (const m of text.matchAll(NEWTHEOREM_RE)) {
    const name = m[2]!.trim();
    let i = m.index + m[0].length;
    const shared = readGroup(text, i, "[");
    if (shared) i = shared.end;
    const title = readGroup(text, i, "{");
    if (!title) continue;
    const reset = readGroup(text, title.end, "[");
    out.display[name] = title.value.replace(/\\[a-zA-Z@]+|[{}]/g, "").trim();
    if (m[1] === "*") continue; // unnumbered
    out.counterOf[name] = shared ? shared.value.trim() : name;
    if (!shared) out.resetBy[name] = within(reset?.value);
  }
  for (const m of text.matchAll(DECLARETHEOREM_RE)) {
    let i = m.index + m[0].length;
    const opts = readGroup(text, i, "[");
    if (opts) i = opts.end;
    const nameGroup = readGroup(text, i, "{");
    if (!nameGroup) continue;
    const o = opts?.value ?? "";
    const get = (k: string): string | undefined =>
      new RegExp(`(?:^|,)\\s*${k}\\s*=\\s*([^,\\]]*)`).exec(o)?.[1]?.replace(/[{}]/g, "").trim();
    const sibling = get("sibling") ?? get("numberlike");
    const parent = get("numberwithin") ?? get("within") ?? get("parent");
    for (const raw of nameGroup.value.split(",")) {
      const name = raw.trim();
      if (!name) continue;
      out.display[name] = get("name") ?? get("title") ?? name.charAt(0).toUpperCase() + name.slice(1);
      if (/(?:^|,)\s*unnumbered\b/.test(o)) continue;
      out.counterOf[name] = sibling ?? name;
      if (!sibling) out.resetBy[name] = within(parent);
    }
  }
  for (const m of text.matchAll(NUMBERWITHIN_RE)) out.resetBy[m[1]!.trim()] = within(m[2]!.trim());
  return out;
}

/** "Theorem 3.1", "Lemma~A.2", "Proposition 4" — a result named by its printed number. */
const NUMBERED_MENTION_RE =
  /\b(Theorems?|Lemmas?|Propositions?|Corollar(?:y|ies)|Claims?|Results?|Assumptions?|Conditions?|Definitions?)\s*~?\s*([A-Z]?\d+(?:\.\d+)*)\b/g;

/** True when `text` names a result, by `\ref` or by printed number. */
export function mentionsResult(text: string): boolean {
  NUMBERED_MENTION_RE.lastIndex = 0;
  return refsIn(text).length > 0 || NUMBERED_MENTION_RE.test(text);
}

// ---------------------------------------------------------------------------
// environment extraction
// ---------------------------------------------------------------------------

const PROOF_ENVS = new Set(["proof", "proof*"]);
/** Joins the several proofs a paper gives one result (a sketch, then the full argument). */
export const FURTHER_PROOF_SEPARATOR = "\n\n% --- the paper gives a further proof of this result ---\n\n";
const SECTION_RE = /\\(sub)*section\s*\*?\s*(?=\{)/g;

/**
 * A proof-environment title that announces discussion rather than a proof ("Comments on
 * Theorem 2", "Remarks", "Example 3.1"): the environment is typeset like a proof but is
 * not one, and must not be bound to the result it names.
 */
export function isCommentaryTitle(title: string): boolean {
  const words = title.replace(/\\[a-zA-Z]+\s*|[{}*]/g, " ").trim();
  return /^(?:comments?|remarks?|discussions?|examples?|notes?|illustrations?|intuition)\b/i.test(words);
}

/** Where a proof written in running text ends: a QED mark of any common spelling. */
const QED_RE =
  /\\qed\b|\\blacksquare\b|\\Box\b|\\square\b|\\endproof\b|\\rule\s*\{[^{}]*\}\s*\{[^{}]*\}|\bQ\.?\s?E\.?\s?D\.?(?=\W)/g;

/** `\textbf{…}`, `{\bf …}`, `\paragraph{…}`, `\subsection*{…}`: the constructs that open a
 * proof written in running text when their argument reads "Proof of <result>". */
const PROSE_OPENER_RE = /\\(?:textbf|textsc|textit|emph|paragraph\*?|(?:sub)*section\*?)\s*(?=\{)|\{\s*\\(?:bf|bfseries|sc|scshape|it|itshape|em)\b/g;

/** True when only blanks separate `at` from the start of its line. */
function opensLine(text: string, at: number): boolean {
  return /^[ \t]*$/.test(text.slice(text.lastIndexOf("\n", at - 1) + 1, at));
}

export interface ProseProof {
  /** offset of the opener (`\textbf` or `{`) */
  start: number;
  /** offset just past the opener's group and an optional `:`/`.` */
  bodyStart: number;
  /** the opener's text, e.g. `Proof of Theorem~\ref{thm:a}` */
  title: string;
  /** opened by a sectioning command (`\section`, `\paragraph`) rather than a bold run */
  heading: boolean;
}

/** Where the first `\end{…}` after `from` with no `\begin{…}` of its own in `[from, to)` starts, or
 *  `to`: text read from `from` cannot run past the close of an environment it did not open. Pure. */
export function unmatchedEndBefore(flat: string, from: number, to: number): number {
  const re = /\\(begin|end)\s*\{[^{}]*\}/g;
  re.lastIndex = from;
  let depth = 0;
  for (let m = re.exec(flat); m && m.index < to; m = re.exec(flat)) {
    if (m[1] === "begin") depth += 1;
    else if (depth === 0) return m.index;
    else depth -= 1;
  }
  return to;
}

/**
 * Proofs written without a `proof` environment: a bold or heading run reading "Proof of
 * <Result>~\ref{label}" (any of the constructs in `PROSE_OPENER_RE`), outside every
 * environment. Only the opener is found here; the caller decides where the body ends.
 */
export function proseProofOpeners(text: string, from: number, to: number): ProseProof[] {
  const out: ProseProof[] = [];
  PROSE_OPENER_RE.lastIndex = from;
  for (let m = PROSE_OPENER_RE.exec(text); m && m.index < to; m = PROSE_OPENER_RE.exec(text)) {
    const braceAt = m[0].startsWith("{") ? m.index : m.index + m[0].length;
    const g = readGroup(text, braceAt, "{");
    if (!g) continue;
    const title = g.value.replace(/^\s*\\(?:bf|bfseries|sc|scshape|it|itshape|em)\b\s*/, "").trim();
    const words = title.replace(/\\[a-zA-Z]+\s*/g, "").trim();
    const heading = /section|paragraph/.test(m[0]);
    // An UNTITLED prose proof — `{\sc Proof.}`, `\textbf{Proof:}` — counts only when it is
    // bold or small caps and opens its line: `the \emph{proof} of` in running text is a word,
    // and a heading "Proofs" is a section, not a proof. It binds like an untitled `\begin{proof}`.
    const untitled =
      /^Proof\s*[:.]?$/i.test(words) &&
      !heading &&
      !/^\\(?:textit|emph)|^\{\s*\\(?:it|itshape|em)\b/.test(m[0]) &&
      opensLine(text, m.index);
    if (untitled) {
      const tail = /^\s*[:.]?/.exec(text.slice(g.end))![0].length;
      out.push({ start: m.index, bodyStart: g.end + tail, title: "", heading });
      PROSE_OPENER_RE.lastIndex = g.end;
      continue;
    }
    if (!/^(?:\\[a-zA-Z]+\s*)*Proofs?\s+of\b/i.test(title) || !mentionsResult(title)) continue;
    const tail = /^\s*[:.]?/.exec(text.slice(g.end))![0].length;
    out.push({ start: m.index, bodyStart: g.end + tail, title, heading });
    PROSE_OPENER_RE.lastIndex = g.end;
  }
  return out;
}

const PROSE_RESULT_RE =
  /^(Theorems?|Lemmas?|Propositions?|Corollar(?:y|ies)|Claims?|Assumptions?|Conditions?|Definitions?)\s+([A-Z]?\d+(?:\.\d+)*)\s*[:.]?$/i;

/** True when every `{` opened, every math span (`$…$`, `\[…\]`, `\(…\)`) entered and every
 * `\begin{…}` environment opened in `text[from, at)` is closed again before `at`. */
export function isClosedAt(text: string, from: number, at: number): boolean {
  return openConstructsAt(text, from, at).length === 0;
}

export interface ProseResult {
  /** offset of the opener (`\textsc` or `{`) */
  start: number;
  /** offset just past the opener's group and an optional `:`/`.` */
  bodyStart: number;
  /** the printed word, e.g. `Theorem` */
  word: string;
  /** the printed number, e.g. `3.1` or `A1` */
  number: string;
}

/**
 * Results stated without an environment — `\textsc{Theorem 1:}\textit{ If … then …}`, the
 * house style of Scientific-Word-authored econometrics papers. The opener is an upright
 * (bold, small caps, heading) run reading exactly "<Word> <number>", opening its line. Only
 * the opener is found here; the caller decides where the statement ends.
 */
export function proseResultOpeners(text: string, from: number, to: number): ProseResult[] {
  const out: ProseResult[] = [];
  PROSE_OPENER_RE.lastIndex = from;
  for (let m = PROSE_OPENER_RE.exec(text); m && m.index < to; m = PROSE_OPENER_RE.exec(text)) {
    if (/^\\(?:textit|emph)|^\{\s*\\(?:it|itshape|em)\b/.test(m[0])) continue;
    if (!opensLine(text, m.index)) continue;
    const braceAt = m[0].startsWith("{") ? m.index : m.index + m[0].length;
    const g = readGroup(text, braceAt, "{");
    if (!g) continue;
    const words = g.value.replace(/\\[a-zA-Z]+\s*|[{}~]/g, " ").replace(/\s+/g, " ").trim();
    const hit = PROSE_RESULT_RE.exec(words);
    if (!hit) continue;
    const tail = /^\s*[:.]?/.exec(text.slice(g.end))![0].length;
    out.push({ start: m.index, bodyStart: g.end + tail, word: hit[1]!, number: hit[2]! });
    PROSE_OPENER_RE.lastIndex = g.end;
  }
  return out;
}

/**
 * A proof body that only points elsewhere ("See Appendix~B.", "Deferred to the
 * Supplementary Material.") rather than arguing: short, carries a cross-reference or names
 * an appendix/supplement, and contains no mathematics. Such a stub never counts as the
 * result's proof when a real one is found later in the document.
 */
export function isProofDeferralStub(body: string): boolean {
  const t = body.trim();
  if (t.length === 0 || t.length > 300) return false;
  if (/\$|\\\[|\\\(|\\begin\s*\{/.test(t)) return false;
  // A pointer names a PLACE (appendix, section, supplement) or says the proof is elsewhere;
  // a one-line proof that cites a lemma ("Combine \cref{lem:a} and \cref{lem:b}.") argues.
  const points =
    /\b(?:[Aa]ppendi(?:x|ces)|[Ss]upplement(?:ary|al)?|[Oo]nline [Aa]ppendix|[Ss]ection|[Ss]ec\.|[Ss]ubsection)\b|\b(?:deferred|omitted|relegated|postponed)\b/.test(
      t,
    );
  return points && t.split(/[.!?](?:\s|$)/).filter((x) => x.trim()).length <= 2;
}
const REF_RE =
  /\\(?:ref|cref|Cref|autoref|eqref|nameref|vref|pageref|thmref|lemref|propref|corref|assref|defref|secref|eqnref)\*?\s*(?:\[[^\]]*\])?\{([^{}]*)\}/g;
const REFRANGE_RE = /\\[cC]refrange\*?\s*\{([^{}]*)\}\s*\{([^{}]*)\}/g;

function lineStarts(text: string): number[] {
  const starts = [0];
  for (let i = 0; i < text.length; i += 1) if (text[i] === "\n") starts.push(i + 1);
  return starts;
}

function lineOf(starts: number[], offset: number): number {
  let lo = 0;
  let hi = starts.length - 1;
  while (lo < hi) {
    const mid = (lo + hi + 1) >> 1;
    if (starts[mid]! <= offset) lo = mid;
    else hi = mid - 1;
  }
  return lo; // 0-based flat line index
}

interface RawEnv {
  name: string;
  start: number; // offset of `\begin{name}`
  bodyStart: number;
  bodyEnd: number; // offset of `\end{name}`
  end: number; // offset just past `\end{name}`
  args: Array<{ kind: "m" | "o" | "s"; value: string }>;
}

/** Find the `\end{name}` matching the `\begin{name}` whose arguments end at `from`.
 * `allowNesting` is true only for `proof` (a `\begin{proof}[Proof of Claim 1]` inside a
 * proof is idiomatic); for a theorem-like env a same-name nesting is out of scope and
 * an explicit error rather than a silently truncated body. */
function findEnd(
  text: string,
  name: string,
  from: number,
  allowNesting: boolean,
  where: string,
): { bodyEnd: number; end: number } {
  const token = new RegExp(String.raw`\\(begin|end)\s*\{${name.replace(/\*/g, "\\*")}\}`, "g");
  token.lastIndex = from;
  let depth = 1;
  for (let m = token.exec(text); m; m = token.exec(text)) {
    if (m[1] === "begin") {
      if (!allowNesting) {
        throw new Error(
          `${where}: \\begin{${name}} nested inside \\begin{${name}} — same-name nesting is not supported`,
        );
      }
      depth += 1;
      continue;
    }
    depth -= 1;
    if (depth === 0) return { bodyEnd: m.index, end: m.index + m[0].length };
  }
  throw new Error(`${where}: \\begin{${name}} has no matching \\end{${name}}`);
}

export function refsIn(text: string): string[] {
  const out: string[] = [];
  const add = (raw: string): void => {
    for (const piece of raw.split(",")) {
      const label = piece.trim();
      if (label && !out.includes(label)) out.push(label);
    }
  };
  const hits: Array<{ at: number; raw: string }> = [];
  for (const m of text.matchAll(REF_RE)) hits.push({ at: m.index, raw: m[1]! });
  for (const m of text.matchAll(REFRANGE_RE)) hits.push({ at: m.index, raw: `${m[1]},${m[2]}` });
  hits.sort((a, b) => a.at - b.at);
  for (const h of hits) add(h.raw);
  return out;
}

/**
 * Extract every theorem-like environment from the flattened text.
 *
 * Only the document body is scanned (`\begin{document}` … `\end{document}` when
 * present), so the `\begin{theorem}` inside a `\NewDocumentEnvironment` wrapper in the
 * preamble is never mistaken for a real theorem. Environments nested inside an already
 * extracted environment or proof are skipped — they belong to that body.
 *
 * `warnings` carries every result the parser deliberately left out, so nothing is ever
 * dropped in silence.
 */
export function extractEnvs(
  flat: string,
  lineMap: FlatLine[],
  newtheorem: Record<string, EnvKind>,
  counters: TheoremCounters = parseTheoremCounters(flat),
): { envs: TexEnv[]; warnings: string[] } {
  const warnings: string[] = [];
  const starts = lineStarts(flat);
  const sigs = parseEnvSignatures(flat);
  const beginDoc = /\\begin\s*\{document\}/.exec(flat);
  const from = beginDoc ? beginDoc.index + beginDoc[0].length : 0;
  // The `\end{document}` that closes the body is the first one AFTER `\begin{document}`:
  // a preamble macro whose body happens to contain `\end{document}` (say
  // `\newcommand{\finish}{\end{document}}`) would otherwise collapse the scan window to
  // nothing and the parser would return no environments at all.
  const endDocRe = /\\end\s*\{document\}/g;
  endDocRe.lastIndex = from;
  const endDoc = endDocRe.exec(flat);
  const to = endDoc ? endDoc.index : flat.length;
  if (to <= from) {
    throw new Error(
      `empty document body: \\end{document} does not follow \\begin{document} ` +
        `(scan window ${from}..${to} of ${flat.length} characters)`,
    );
  }

  const locate = (startOffset: number, endOffset: number, env: string, label: string | null): TexLocator => {
    const a = lineMap[lineOf(starts, startOffset)];
    const b = lineMap[lineOf(starts, Math.max(startOffset, endOffset - 1))];
    if (!a || !b) throw new Error("internal: line map shorter than the flattened text");
    return { file: a.file, from: a.line, to: b.file === a.file ? b.line : a.line, env, label };
  };

  // headings, in document order
  const headings: Array<{ at: number; title: string }> = [];
  for (const m of flat.matchAll(SECTION_RE)) {
    const g = readGroup(flat, m.index + m[0].length, "{");
    if (g) headings.push({ at: m.index, title: g.value.trim() });
  }
  const readEnvAt = (start: number, name: string): RawEnv => {
    let i = start + flat.slice(start).match(/^\\begin\s*\{[^{}]*\}/)![0].length;
    const spec = sigs[name]?.argSpec ?? ["o"];
    const args: RawEnv["args"] = [];
    for (const kind of spec) {
      if (kind === "s") {
        const j = skipSpace(flat, i);
        if (flat[j] === "*") {
          args.push({ kind, value: "*" });
          i = j + 1;
        }
        continue;
      }
      const g = readGroup(flat, i, kind === "m" ? "{" : "[");
      if (!g) continue;
      args.push({ kind, value: g.value });
      i = g.end;
    }
    const line = lineMap[lineOf(starts, start)];
    const where = line ? `${line.file}:${line.line}` : `flat:${start}`;
    const { bodyEnd, end } = findEnd(flat, name, i, PROOF_ENVS.has(name), where);
    return { name, start, bodyStart: i, bodyEnd, end, args };
  };

  const raws: RawEnv[] = [];
  const proofs: RawEnv[] = [];
  const beginRe = /\\begin\s*\{([^{}]+)\}/g;
  beginRe.lastIndex = from;
  let covered = from; // end of the last extracted env: nested matches are skipped
  for (let m = beginRe.exec(flat); m && m.index < to; m = beginRe.exec(flat)) {
    if (m.index < covered) continue;
    const name = m[1]!.trim();
    const isProof = PROOF_ENVS.has(name);
    const kind = newtheorem[name] ?? (name.endsWith("*") ? newtheorem[name.slice(0, -1)] : undefined);
    if (isProof && kind) {
      // The paper redeclared `proof` itself as a theorem-like environment. It stays a
      // proof here (that is what `\begin{proof}` means to every reader), but the result
      // it would otherwise have contributed is not extracted — say so.
      const line = lineMap[lineOf(starts, m.index)];
      warnings.push(
        `${line ? `${line.file}:${line.line}` : `flat:${m.index}`}: \\begin{${name}} is also ` +
          `declared as a "${kind}" environment; it is read as a proof, not extracted as a result`,
      );
    }
    if (!isProof && !kind) continue;
    const raw = readEnvAt(m.index, name);
    (isProof ? proofs : raws).push(raw);
    // Inside a result or a proof, nested environments belong to that body. Inside commentary
    // (a remark, an example) they do not: an assumption stated within a remark is still the
    // paper's assumption, so the scan continues into the commentary's body.
    // An algorithm is one environment: its `algorithmic` block is its body, not a second one.
    covered = !isProof && (kind === "remark" || kind === "example" || kind === "other") && !/algorithm/i.test(name) ? raw.bodyStart : raw.end;
  }

  const inside = (at: number, list: RawEnv[]): boolean => list.some((e) => at > e.start && at < e.end);
  // The bibliography ends a prose result or proof as a heading does: it is never part of one.
  const bib = flat.slice(from, to).search(/\\begin\s*\{thebibliography\}|\\(?:bibliography|printbibliography)(?![a-zA-Z@])/);
  const headingStarts = [...headings.map((h) => h.at), ...(bib >= 0 ? [from + bib] : [])].sort((x, y) => x - y);
  const whereAt = (at: number): string => {
    const line = lineMap[lineOf(starts, at)];
    return line ? `${line.file}:${line.line}` : `flat:${at}`;
  };
  // thmtools `\begin{restatable}[title]{env}{macro}` states a result the scan above does not read, and
  // `\macro*` restates it later: say so once, with what to rewrite in the run's source copy.
  if (!newtheorem["restatable"]) {
    const found: Array<{ at: number; env: string; macro: string }> = [];
    const re = /\\begin\s*\{restatable\*?\}/g;
    re.lastIndex = from;
    for (let m = re.exec(flat); m && m.index < to; m = re.exec(flat)) {
      let i = m.index + m[0].length;
      const opt = readGroup(flat, i, "[");
      if (opt) i = opt.end;
      const env = readGroup(flat, i, "{");
      const macro = env ? readGroup(flat, env.end, "{") : null;
      found.push({ at: m.index, env: env?.value.trim() ?? "?", macro: macro?.value.trim() ?? "?" });
    }
    if (found.length > 0) {
      const body = flat.slice(from, to);
      const restated = found.reduce((n, f) => n + (/^[A-Za-z@]+$/.test(f.macro) ? [...body.matchAll(new RegExp(String.raw`\\${f.macro}\s*\*`, "g"))].length : 0), 0);
      const at = found.slice(0, 3).map((f) => `${whereAt(f.at)} {${f.env}}{${f.macro}}`);
      warnings.push(
        `${found.length} result(s) are written in thmtools \`restatable\` (${at.join(", ")}${found.length > 3 ? ", …" : ""}) and restated ` +
          `${restated} time(s) by \\<macro>*: the parser does not read it, so they are not extracted; rewrite each as its \\begin{<env>} … ` +
          `\\end{<env>} environment in the run's source copy, and each \\<macro>* restatement as a copy of the statement keeping its \\label ` +
          `(the parser merges a word-for-word copy under the same label into the original)`,
      );
    }
  }
  /** Typesetting that may sit between a statement and the proof "directly following" it —
   * `\bigskip`, `\noindent`, `\vspace{…}`, a `\par` — which authors sprinkle freely. */
  const TYPESET_SKIP = /^(?:\s|\\(?:big|med|small)skip\b|\\noindent\b|\\par\b|\\vspace\*?\s*\{[^{}]*\}|\\newpage\b|\\clearpage\b)*/;
  const afterSkip = (at: number): number => at + TYPESET_SKIP.exec(flat.slice(at, at + 2000))![0].length;

  // (4b) PROSE results — `\textsc{Theorem 1:}\textit{ If … then …}` — have no environment
  // either. They are read only for a KIND the paper never writes as an environment (a paper
  // with `\begin{theorem}` that also bolds "Theorem 1" at a line start is cross-referencing).
  // The statement runs to the paragraph break, the next such opener, a proof opener, a
  // heading or an environment, whichever comes first; the printed number is its number.
  const kinds: Record<string, EnvKind> = { ...newtheorem };
  const proseNumber = new Map<RawEnv, string>();
  {
    const usedKinds = new Set(raws.map((r) => newtheorem[r.name] ?? newtheorem[r.name.replace(/\*$/, "")]));
    const openers = proseResultOpeners(flat, from, to).filter((o) => !inside(o.start, raws) && !inside(o.start, proofs));
    const proofOpenerStarts = proseProofOpeners(flat, from, to).map((p) => p.start);
    const paragraphBreak = /\n[ \t]*\n/g;
    openers.forEach((o, k) => {
      const kind = kindFromTitle(o.word);
      if (kind === "other" || usedKinds.has(kind)) return;
      const stops = [
        openers[k + 1]?.start,
        proofOpenerStarts.find((p) => p > o.bodyStart),
        headingStarts.find((h) => h > o.bodyStart),
        raws.find((r) => r.start > o.bodyStart)?.start,
        proofs.find((p) => p.start > o.bodyStart)?.start,
        to,
      ].filter((x): x is number => x !== undefined);
      let end = Math.min(...stops);
      // The statement ends at the first paragraph break that is OUTSIDE every brace group and
      // math span opened since the opener: converters wrap long italic runs across blank lines.
      paragraphBreak.lastIndex = o.bodyStart;
      for (let pb = paragraphBreak.exec(flat); pb && pb.index < end; pb = paragraphBreak.exec(flat)) {
        if (!isClosedAt(flat, o.bodyStart, pb.index)) continue;
        // A sentence does not end at a comma: "… for each $\ell$,⏎⏎then …" continues. And a
        // statement set in italics continues through an italic run after the break
        // ("\textit{Furthermore, if …}"): the paper's prose is upright, its statements are not.
        const before = flat.slice(o.bodyStart, pb.index).trimEnd();
        const rawAfter = flat.slice(pb.index + pb[0].length, pb.index + pb[0].length + 60).trimStart();
        const after = rawAfter.replace(/^(?:\\[a-zA-Z]+\s*\{\s*)*/, "");
        const italicStatement = /\\(?:textit|emph)\s*\{|\{\s*\\(?:it|itshape|em)\b/.test(flat.slice(o.bodyStart, Math.min(pb.index, o.bodyStart + 200)));
        const italicAfter = /^(?:\\(?:textit|emph)\s*\{|\{\s*\\(?:it|itshape|em)\b)/.test(rawAfter);
        if (/[,;:]\$?$/.test(before) || /^[a-z]/.test(after) || (italicStatement && italicAfter)) continue;
        end = pb.index;
        break;
      }
      if (flat.slice(o.bodyStart, end).trim().length < 20) return;
      const name = `prose:${kind}`;
      kinds[name] = kind;
      const raw: RawEnv = { name, start: o.start, bodyStart: o.bodyStart, bodyEnd: end, end, args: [{ kind: "o", value: `${o.word} ${o.number}` }] };
      raws.push(raw);
      proseNumber.set(raw, o.number);
      warnings.push(
        `${whereAt(o.start)}: "${o.word} ${o.number}" is stated in running text, not in an environment; ` +
          `read as a ${kind} ending at the paragraph break — check that the statement is whole`,
      );
    });
    raws.sort((a, b) => a.start - b.start);
  }

  // Labels: the environment's own (or the one its signature template builds), and every
  // other `\label` inside its body — a theorem whose parts are `\item \label{thm:a-i}` is
  // proved part by part under those labels.
  const labelOf = new Map<RawEnv, string | null>();
  const innerLabels = new Map<RawEnv, string[]>();
  for (const raw of raws) {
    const sig = sigs[raw.name];
    const body = flat.slice(raw.bodyStart, raw.bodyEnd);
    let label: string | null = null;
    if (sig?.labelTemplate) {
      label = sig.labelTemplate.replace(/#(\d)/g, (_all, d: string) => {
        const arg = raw.args[Number(d) - 1];
        return arg ? arg.value.trim() : "";
      });
      if (!label.trim() || /#/.test(label)) label = null;
    }
    // the environment's own labels, never those belonging to a result or proof nested in it
    // (a list or an align block inside the body is part of the body: `\item \label{thm:a-i}`)
    const own = body.replace(/\\begin\s*\{([^{}]+)\}[\s\S]*?\\end\s*\{\1\}/g, (all, name: string) =>
      (newtheorem[name.trim()] && !isAlgorithmName(name.trim())) || PROOF_ENVS.has(name.trim()) ? " " : all,
    );
    const all = [...own.matchAll(/\\label\s*\{([^{}]*)\}/g)].map((m) => m[1]!.trim()).filter((l) => l);
    // An algorithm is labelled at its caption (algorithm2e also labels lines: `\label{ln:init}`).
    if (!label && isAlgorithmName(raw.name)) label = captionLabel(body) ?? all.find((l) => /alg/i.test(l)) ?? null;
    if (!label) label = all[0] ?? null;
    labelOf.set(raw, label);
    innerLabels.set(raw, all.filter((l) => l !== label));
  }

  // (4c) RESTATEMENTS: an appendix that repeats a theorem word for word under the same
  // `\label` before proving it states nothing new. The copy is dropped, and a proof directly
  // following it is the ORIGINAL's proof.
  const restatements: Array<{ copy: RawEnv; original: RawEnv }> = [];
  {
    const normBody = (r: RawEnv): string => flat.slice(r.bodyStart, r.bodyEnd).replace(/\\label\s*\{[^{}]*\}/g, "").replace(/\s+/g, " ").trim();
    const seen = new Map<string, RawEnv>();
    for (const r of [...raws]) {
      const l = labelOf.get(r);
      if (!l) continue;
      const first = seen.get(l);
      if (first && first.name === r.name && normBody(first) === normBody(r)) {
        restatements.push({ copy: r, original: first });
        raws.splice(raws.indexOf(r), 1);
        warnings.push(`${whereAt(r.start)}: \\begin{${r.name}} restates ${l} (${whereAt(first.start)}) word for word; not a separate result`);
        continue;
      }
      if (!first) seen.set(l, r);
    }
    // The same statement under no label, or another one, is read as a separate result: say so, since
    // only the orchestrator can tell a restatement from a second result.
    const byBody = new Map<string, RawEnv>();
    for (const r of raws) {
      if (r.name.startsWith("prose:") || isAlgorithmName(r.name)) continue;
      const text = normBody(r);
      if (!text) continue;
      const first = byBody.get(text);
      if (!first) {
        byBody.set(text, r);
        continue;
      }
      const [l, own] = [labelOf.get(first), labelOf.get(r)];
      if (l && l === own) continue;
      warnings.push(
        l
          ? `${whereAt(r.start)}: \\begin{${r.name}} states the same as ${l} (${whereAt(first.start)}) but ` +
              `${own ? `under \\label{${own}}, not its \\label` : "without its \\label"}: it is read as a separate result; ` +
              `if it is a restatement, give it \\label{${l}} in the run's source copy${own ? ` (and each \\ref{${own}} the same)` : ""}`
          : `${whereAt(r.start)}: \\begin{${r.name}} states the same as the \\begin{${first.name}} at ${whereAt(first.start)}, ` +
              `which carries no \\label: it is read as a separate result; if it is a restatement, give both the same \\label in the run's source copy`,
      );
    }
  }

  // (5) PROSE proofs — `\textbf{Proof of Theorem~\ref{X}:} …`, `{\sc Proof.}` or a
  // `\subsection*{Proof of …}` heading — have no environment. The body runs to the first QED
  // mark, the next such opener, the next heading, the next prose result, or the end of the
  // document, whichever comes first; a result stated inside that span belongs to the proof, as
  // it would inside `\begin{proof}` — unless it carries a proof of its own there (a section
  // "Proof of Theorem 2" that states and proves three lemmas on the way), in which case it is
  // a result in its own right. Each is synthesised as a proof so the ordinary binding (and
  // stub supersession) applies.
  const openers = proseProofOpeners(flat, from, to).filter(
    (o) => !inside(o.start, raws) && !inside(o.start, proofs),
  );
  const proseResultStarts = raws.filter((r) => r.name.startsWith("prose:")).map((r) => r.start);
  const prose: RawEnv[] = [];
  const headingSpans = new Set<RawEnv>();
  openers.forEach((o, k) => {
    const stops = [openers[k + 1]?.start, headingStarts.find((h) => h > o.bodyStart), proseResultStarts.find((h) => h > o.bodyStart), to].filter(
      (x): x is number => x !== undefined,
    );
    // (…or where an environment opened BEFORE the proof closes: the last proof of an appendix set in
    // `\begin{APPENDICES} … \end{APPENDICES}` ends there, not at the end of the document)
    const sectionEnd = unmatchedEndBefore(flat, o.bodyStart, Math.min(...stops));
    let bodyEnd = sectionEnd;
    let end = bodyEnd;
    // the QED that closes THIS proof, not one inside a nested `\begin{proof}` or result
    QED_RE.lastIndex = o.bodyStart;
    let q = QED_RE.exec(flat);
    while (q && q.index < bodyEnd && (inside(q.index, proofs) || inside(q.index, raws))) q = QED_RE.exec(flat);
    if (q && q.index < bodyEnd) {
      // drop the QED's own decoration (`\hfill$` before `\square$`, `$` before `\blacksquare$`),
      // token by token, as far as the text before it stays whole: the `$$` closing a display just
      // before `\hfill$\square$` is the proof's, not the mark's
      const closed = (at: number): boolean => openConstructsAt(flat, o.bodyStart, at).length === 0;
      let cut = closed(q.index) ? q.index : -1;
      for (let p = q.index; ; ) {
        const d = /(?:\s|\$|\\hfill|\\quad|\\qquad|\\null|\\hspace\*?\{[^{}]*\})$/.exec(flat.slice(o.bodyStart, p));
        if (!d) break;
        p -= d[0].length;
        if (closed(p)) cut = p;
      }
      if (cut >= 0) {
        bodyEnd = cut;
        end = q.index + q[0].length + (/^[\s$}]*/.exec(flat.slice(q.index + q[0].length))?.[0].length ?? 0);
      } else {
        // The mark is set INSIDE the proof's last display (`… = \alpha. \,\Box \end{eqnarray*}`,
        // `$$ … \Box $$`) or another construct the proof opened: the proof ends where that
        // construct closes, the mark kept as printed — never inside math.
        const close = closingPointAfter(flat, o.bodyStart, q.index + q[0].length, sectionEnd);
        if (close !== null) {
          bodyEnd = close;
          end = close;
        } else {
          bodyEnd = q.index;
          end = q.index + q[0].length;
          warnings.push(`${whereAt(q.index)}: the QED mark closing "${o.title || "Proof"}" sits inside a construct that never closes before the proof's section ends; the proof is cut at the mark and is not a balanced fragment`);
        }
      }
    } else if (openConstructsAt(flat, o.bodyStart, bodyEnd).length > 0) {
      warnings.push(`${whereAt(o.start)}: "${o.title || "Proof"}" has no QED mark and its text is not closed where its section ends; the proof is not a balanced fragment`);
    }
    const body = flat.slice(o.bodyStart, bodyEnd);
    // A heading followed (past its `\label`, spacing, a sentence of preamble) by
    // `\begin{proof}` is handled by heading binding below.
    const lead = /^(?:\s|\\label\s*\{[^{}]*\}|\\(?:big|med|small)skip\b|\\noindent\b|\\par\b)*/.exec(body)![0].length;
    const firstProof = body.indexOf("\\begin{proof");
    if (!body.trim() || firstProof === lead || (firstProof >= 0 && firstProof < 400 && !/[$\\]/.test(body.slice(lead, firstProof).replace(/\\(?:ref|cref|Cref|eqref)\s*\{[^{}]*\}/g, "")))) return;
    // A heading "Proof of Theorem 2" over a section that holds `\begin{proof}` environments is a
    // container: those proofs (and the lemmas stated between them) are the section's content,
    // and an untitled one binds by the heading itself.
    if (o.heading && proofs.some((q) => q.start >= o.bodyStart && q.start < sectionEnd)) return;
    const span: RawEnv = { name: "proof", start: o.start, bodyStart: o.bodyStart, bodyEnd, end, args: [{ kind: "o", value: o.title }] };
    prose.push(span);
    if (o.heading) headingSpans.add(span);
  });
  if (prose.length > 0) {
    // Results and proofs stated inside a prose proof are part of it (as inside `\begin{proof}`),
    // except, under a HEADING-opened span (a section is a container, a bold run is a
    // paragraph), a result that is proved there under its own name — by a titled proof naming
    // its label, or an untitled one directly after it — and that proof.
    const swallowed = new Set<RawEnv>();
    const ownProofOf = (r: RawEnv): RawEnv | undefined =>
      proofs.find(
        (q) =>
          q.start > r.end &&
          (refsIn(q.args.find((a) => a.kind === "o")?.value ?? "").includes(labelOf.get(r) ?? "\0") || afterSkip(r.end) === q.start),
      );
    const kept = new Set<RawEnv>();
    for (const r of raws) {
      const span = prose.find((p) => inside(r.start, [p]));
      if (!span) continue;
      const own = headingSpans.has(span) ? ownProofOf(r) : undefined;
      if (own) kept.add(own);
      else swallowed.add(r);
    }
    for (const q of proofs) if (inside(q.start, prose) && !kept.has(q)) swallowed.add(q);
    for (let i = raws.length - 1; i >= 0; i -= 1) if (swallowed.has(raws[i]!)) raws.splice(i, 1);
    for (let i = proofs.length - 1; i >= 0; i -= 1) if (swallowed.has(proofs[i]!)) proofs.splice(i, 1);
    proofs.push(...prose);
    proofs.sort((a, b) => a.start - b.start);
  }

  // proof matching: (1) an UNTITLED proof directly following the env, (2) a proof whose
  // title \ref/\cref's the env's label. A titled proof binds by its title only: papers
  // that collect proofs in an appendix routinely place `\begin{proof}[of Theorem~\ref{X}]`
  // right after some other (often cited, proof-less) lemma, and adjacency would hand X's
  // proof to that lemma and leave X without one.
  //
  // Two further shapes, both common in econometrics papers: (3) an untitled proof sitting
  // under a heading `\section{Proof of Theorem~\ref{X}}` binds to X by that heading; and
  // (4) a proof directly after the statement that is only a pointer ("See Appendix~B.")
  // is a DEFERRAL STUB — the real proof arrives later and supersedes it, so the core is
  // asked to check the actual argument rather than a one-line cross-reference.
  const claimed = new Set<RawEnv>();
  const isDeferralStub = (proof: RawEnv): boolean =>
    isProofDeferralStub(flat.slice(proof.bodyStart, proof.bodyEnd));
  const proofTitle = (proof: RawEnv): string => proof.args.find((a) => a.kind === "o")?.value ?? "";
  const proofOf = new Map<RawEnv, RawEnv>();
  const extraProofs = new Map<RawEnv, RawEnv[]>();

  // Printed numbers, reproduced from the counter layout and the sectioning, so that a proof
  // announced as "Proof of Theorem 3.1" binds when the paper gives no `\ref`.
  const numberOf = new Map<RawEnv, string>();
  {
    type Ev = { at: number; kind: "section" | "subsection" | "appendix" | "env"; raw?: RawEnv };
    const events: Ev[] = [];
    for (const m of flat.matchAll(/\\((?:sub)*)section\s*(\*?)\s*(?=\{)/g)) {
      if (m.index < from || m.index >= to || m[2]) continue;
      events.push({ at: m.index, kind: m[1] ? "subsection" : "section" });
    }
    for (const m of flat.matchAll(/\\appendix\b/g)) if (m.index >= from && m.index < to) events.push({ at: m.index, kind: "appendix" });
    for (const r of raws) events.push({ at: r.start, kind: "env", raw: r });
    events.sort((a, b) => a.at - b.at);
    let sec = 0;
    let sub = 0;
    let appendix = false;
    const counts: Record<string, number> = {};
    const reset = (level: "section" | "subsection"): void => {
      for (const c of Object.keys(counts)) {
        const by = counters.resetBy[c] ?? null;
        if (by === level || (level === "section" && by === "subsection")) counts[c] = 0;
      }
    };
    const secLabel = (): string => (appendix ? String.fromCharCode(64 + Math.max(1, sec)) : String(sec));
    for (const e of events) {
      if (e.kind === "appendix") {
        appendix = true;
        sec = 0;
        sub = 0;
        reset("section");
      } else if (e.kind === "section") {
        sec += 1;
        sub = 0;
        reset("section");
      } else if (e.kind === "subsection") {
        sub += 1;
        reset("subsection");
      } else {
        const r = e.raw!;
        if (r.name.endsWith("*")) continue;
        const c = counters.counterOf[r.name] ?? r.name;
        counts[c] = (counts[c] ?? 0) + 1;
        const by = counters.resetBy[c] ?? null;
        numberOf.set(
          r,
          by === "section" ? `${secLabel()}.${counts[c]}` : by === "subsection" ? `${secLabel()}.${sub}.${counts[c]}` : String(counts[c]),
        );
      }
    }
    for (const [r, n] of proseNumber) numberOf.set(r, n);
  }
  const displayKind = (r: RawEnv): EnvKind => {
    const base = r.name.replace(/\*$/, "");
    const word = counters.display[base];
    return word ? kindFromTitle(word) : (kinds[base] ?? "other");
  };
  /** Results a piece of text names: by `\ref` label, or by printed word + number. */
  const targetsOf = (text: string): RawEnv[] => {
    const out: RawEnv[] = [];
    const labels = refsIn(text);
    for (const r of raws) {
      const l = labelOf.get(r);
      if (l !== null && l !== undefined && labels.includes(l)) out.push(r);
    }
    // a label inside a result's body (a part, a displayed claim) names that result
    for (const l of labels) {
      if (out.some((r) => labelOf.get(r) === l)) continue;
      const holders = raws.filter((r) => innerLabels.get(r)?.includes(l));
      if (holders.length === 1 && !out.includes(holders[0]!)) out.push(holders[0]!);
    }
    NUMBERED_MENTION_RE.lastIndex = 0;
    for (const m of text.matchAll(NUMBERED_MENTION_RE)) {
      const kind = kindFromTitle(m[1]!);
      const hits = raws.filter((r) => numberOf.get(r) === m[2] && displayKind(r) === kind);
      if (hits.length === 1 && !out.includes(hits[0]!)) out.push(hits[0]!);
    }
    return out;
  };
  const titleTargets = (proof: RawEnv): RawEnv[] => targetsOf(proofTitle(proof));
  const headingTargets = (proof: RawEnv): RawEnv[] => {
    let title: string | null = null;
    for (const h of headings) {
      if (h.at > proof.start) break;
      title = h.title;
    }
    // "Proof of Theorem 2" binds; "Density bounds in Proposition 2" is a section ABOUT it.
    return title && /\bproofs?\b/i.test(title) ? targetsOf(title) : [];
  };
  /** An untitled proof preceded by text that announces it ("We now prove Theorem~\ref{X}."):
   * the results named between the previous environment and the proof, when they name one. */
  const announcedTargets = (proof: RawEnv): RawEnv[] => {
    let prevEnd = from;
    for (const r of raws) if (r.end <= proof.start && r.end > prevEnd) prevEnd = r.end;
    for (const q of proofs) if (q.end <= proof.start && q.end > prevEnd) prevEnd = q.end;
    const gap = flat.slice(prevEnd, proof.start);
    const named = [...new Set(targetsOf(gap))];
    return named.length === 1 ? named : [];
  };
  // (1) an untitled proof — `\begin{proof}` or a prose `{\sc Proof.}` — directly following
  // the statement (or a word-for-word restatement of it) is its proof.
  // A float set between a result and its proof (an algorithm placed near its first mention)
  // is stepped over; an algorithm never owns a proof.
  const afterFloats = (at: number): number => {
    let a = afterSkip(at);
    for (let f = raws.find((r) => r.start === a && isAlgorithmName(r.name)); f; f = raws.find((r) => r.start === a && isAlgorithmName(r.name))) a = afterSkip(f.end);
    return a;
  };
  /** Bind `proof` to `owner`; a deferral stub bound before is superseded (it stays claimed: it is
   * nobody else's proof either), and the warning says so. */
  const bind = (owner: RawEnv, proof: RawEnv): void => {
    const stub = proofOf.get(owner);
    if (stub) {
      const line = lineMap[lineOf(starts, stub.start)];
      warnings.push(
        `${line ? `${line.file}:${line.line}` : `flat:${stub.start}`}: the \\begin{${stub.name}} ` +
          `after ${labelOf.get(owner) ?? `${owner.name} ${numberOf.get(owner) ?? "?"}`} only defers to another place; the proof at ` +
          `${lineMap[lineOf(starts, proof.start)]?.line ?? "?"} supersedes it`,
      );
    }
    claimed.add(proof);
    proofOf.set(owner, proof);
  };
  for (const { copy, original } of [...raws.filter((r) => !isAlgorithmName(r.name)).map((r) => ({ copy: r, original: r })), ...restatements]) {
    const at = afterFloats(copy.end);
    const proof = proofs.find(
      (p) => p.start === at && !claimed.has(p) && (p.args.find((a) => a.kind === "o")?.value ?? "").trim() === "",
    );
    if (!proof) continue;
    const current = proofOf.get(original);
    // The proof after a restatement supersedes a deferral stub after the original.
    if (current === undefined || (isDeferralStub(current) && !isDeferralStub(proof))) bind(original, proof);
  }
  for (const proof of proofs) {
    if (claimed.has(proof)) continue;
    if (isCommentaryTitle(proofTitle(proof))) {
      // `\begin{proof}[Comments on Theorem~\ref{X}]` reuses the proof environment for
      // discussion. Binding it would hand X a "proof" that argues nothing and would
      // stop the transcriber from recording a classical X as cited.
      const line = lineMap[lineOf(starts, proof.start)];
      warnings.push(
        `${line ? `${line.file}:${line.line}` : `flat:${proof.start}`}: \\begin{${proof.name}} titled ` +
          `"${proofTitle(proof).trim()}" is commentary, not a proof; it is attached to no result`,
      );
      continue;
    }
    const titled = titleTargets(proof);
    // A titled proof is bound by its title; an untitled one by the heading it sits under,
    // else by the text announcing it.
    let targets = titled.length > 0 ? titled : headingTargets(proof);
    if (targets.length === 0 && proofTitle(proof).trim() === "") targets = announcedTargets(proof);
    let owner = targets.find((r) => {
      const current = proofOf.get(r);
      return current === undefined || isDeferralStub(current);
    });
    // Last resort, said out loud: an untitled proof a short stretch of plain text after a
    // result that has no proof, with no heading or other result in between. Authors' styles
    // vary; this keeps such a proof from being dropped, and the warning lets the
    // orchestrator hand-check the rare misbinding.
    let byProximity = false;
    if (!owner && proofTitle(proof).trim() === "") {
      const before = raws.filter((r) => r.end <= proof.start && !isAlgorithmName(r.name)).sort((a, b) => b.end - a.end);
      const prev = before[0];
      const gap = prev ? flat.slice(prev.end, proof.start) : "";
      // Two proof-less results stacked before the proof (a theorem and its corollary, say)
      // make the owner a guess; then the proof stays unbound and the warning names both.
      const alsoProofless = before[1] !== undefined && !proofOf.has(before[1]!) && flat.slice(before[1]!.end, prev!.start).trim().length < 400;
      const clean =
        prev !== undefined &&
        !proofOf.has(prev) &&
        !alsoProofless &&
        gap.length <= 800 &&
        !headings.some((h) => h.at > prev.end && h.at < proof.start) &&
        !proofs.some((q) => q !== proof && q.start > prev.end && q.start < proof.start);
      if (clean) {
        owner = prev;
        byProximity = true;
      } else if (prev !== undefined && !proofOf.has(prev) && alsoProofless) {
        const line = lineMap[lineOf(starts, proof.start)];
        warnings.push(
          `${line ? `${line.file}:${line.line}` : `flat:${proof.start}`}: untitled \\begin{${proof.name}} follows two proof-less results ` +
            `(${labelOf.get(before[1]!) ?? before[1]!.name}, ${labelOf.get(prev) ?? prev.name}); not bound — say which it proves (hand-fix)`,
        );
        continue;
      }
    }
    if (owner && byProximity) {
      const line = lineMap[lineOf(starts, proof.start)];
      warnings.push(
        `${line ? `${line.file}:${line.line}` : `flat:${proof.start}`}: untitled \\begin{${proof.name}} bound to ` +
          `${labelOf.get(owner) ?? `${owner.name} ${numberOf.get(owner) ?? "?"}`} by proximity (it is the nearest ` +
          `preceding proof-less result, with only a short passage in between); check the binding`,
      );
    }
    if (owner) {
      bind(owner, proof);
      continue;
    }
    // Not attached to anything. Two shapes, both worth saying out loud: a second proof
    // for a result that already has one (the paper proves it twice, and only the first
    // reaches the core), and a proof whose owner the parser could not identify at all.
    const line = lineMap[lineOf(starts, proof.start)];
    const where = line ? `${line.file}:${line.line}` : `flat:${proof.start}`;
    const nameOf = (r: RawEnv): string => labelOf.get(r) ?? `${r.name} ${numberOf.get(r) ?? "?"}`;
    const taken = targets.filter((r) => proofOf.has(r));
    const titleRefs = refsIn(proofTitle(proof));
    if (taken.length > 0) {
      // The paper proves the result twice (a sketch in the text, the full argument in an
      // appendix). Both are its proofs: keep both, in order, so the checker sees the full one.
      const owner = taken[0]!;
      extraProofs.set(owner, [...(extraProofs.get(owner) ?? []), proof]);
      claimed.add(proof);
      warnings.push(
        `${where}: a second \\begin{${proof.name}} for ${nameOf(owner)}; appended to that result's proof ` +
          `(the locator names the first proof only)`,
      );
      continue;
    }
    warnings.push(
      `${where}: \\begin{${proof.name}} is attached to no result (` +
        `${titleRefs.length > 0 ? `its title references ${titleRefs.join(", ")}` : "its title references no label"}` +
        `, and it does not directly follow one)`,
    );
  }

  // A proof that only defers ("See the Supplement.") and was never superseded is no proof:
  // the result is not argued in this source, and the transcriber must be free to record it
  // as proved elsewhere rather than be handed a one-line pointer to check.
  for (const [owner, proof] of [...proofOf]) {
    if (!isDeferralStub(proof)) continue;
    proofOf.delete(owner);
    const line = lineMap[lineOf(starts, proof.start)];
    warnings.push(
      `${line ? `${line.file}:${line.line}` : `flat:${proof.start}`}: the proof of ${labelOf.get(owner) ?? owner.name} ` +
        `only defers to another place and nothing in this source supersedes it; the result is read as proved elsewhere`,
    );
  }

  /** `\ref{a}--\ref{b}` ("Assumptions 1–4 hold") names every result between a and b on the
   * same counter, in document order; the two ends alone would drop the middle ones. */
  const RANGE_RE =
    /\\(?:[cC]ref|ref|autoref)\*?\s*\{([^{}]*)\}\s*(?:-{1,3}|–|—|\s+to\s+|\s+through\s+)\s*\\(?:[cC]ref|ref|autoref)\*?\s*\{([^{}]*)\}/g;
  const byLabelRaw = new Map<string, RawEnv>();
  for (const r of raws) {
    const l = labelOf.get(r);
    if (l) byLabelRaw.set(l, r);
  }
  const expandRefRanges = (refs: string[], text: string): string[] => {
    const out = [...refs];
    for (const m of text.matchAll(RANGE_RE)) {
      const a = byLabelRaw.get(m[1]!.trim());
      const b = byLabelRaw.get(m[2]!.trim());
      if (!a || !b) continue;
      const counter = (r: RawEnv): string => counters.counterOf[r.name.replace(/\*$/, "")] ?? r.name;
      if (counter(a) !== counter(b)) continue;
      for (const r of raws) {
        const l = labelOf.get(r);
        if (l && r.start > a.start && r.start < b.start && counter(r) === counter(a) && !out.includes(l)) out.push(l);
      }
    }
    return out;
  };

  const ordinal: Partial<Record<EnvKind, number>> = {};
  const used = new Set<string>();
  const envs: TexEnv[] = [];
  for (const raw of raws) {
    const kind = (kinds[raw.name] ?? kinds[raw.name.replace(/\*$/, "")])!;
    // algorithms count apart, so adding them moves no other environment's ordinal id
    const idKind = isAlgorithmName(raw.name) ? "algorithm" : kind;
    const n = (ordinal[idKind as EnvKind] ?? 0) + 1;
    ordinal[idKind as EnvKind] = n;
    const label = labelOf.get(raw) ?? null;
    let id = label ?? `${idKind}-${n}`;
    if (used.has(id)) {
      // Duplicate `\label`s happen (a copy-pasted environment). Fall back to the
      // ordinal id, and keep counting until the id is actually free: the suffix must be
      // RE-TESTED, or two envs can still land on the same id.
      const base = `${idKind}-${n}`;
      id = base;
      for (let k = 0; used.has(id); k += 1) id = `${base}-${k + 1}`;
      warnings.push(
        `${locate(raw.start, raw.end, raw.name, label).file}: duplicate id ` +
          `"${label ?? base}"; this environment is recorded as "${id}"`,
      );
    }
    used.add(id);
    const proof = proofOf.get(raw) ?? null;
    const body = flat.slice(raw.bodyStart, raw.bodyEnd).trim();
    const proofBody = proof
      ? [proof, ...(extraProofs.get(raw) ?? [])]
          .map((q) => flat.slice(q.bodyStart, q.bodyEnd).trim())
          .join(FURTHER_PROOF_SEPARATOR)
      : null;
    envs.push({
      id,
      kind,
      envName: raw.name,
      label,
      title: envTitle(raw.name, raw.args.find((a) => a.kind === "o")?.value.trim() ?? null, body),
      body,
      proof: proofBody,
      proofLines: proof
        ? locate(proof.start, proof.end, proof.name, null)
        : null,
      lines: locate(raw.start, raw.end, raw.name, label),
      refs: expandRefRanges(refsIn(proofBody ? `${body}\n${proofBody}` : body), proofBody ? `${body}\n${proofBody}` : body),
    });
  }
  // Pseudocode the paper never refers to (a baseline, an experiment's procedure) is context: an
  // algorithm enters the core when a result, assumption or definition refers to it, or the paper's
  // own text does ("we run Algorithm~\ref{…}" — a procedure stated in prose before the results it
  // serves). A paper's own theorem-like `algorithm` stays, referenced or not.
  const outsideAlgorithms = raws.filter((r) => isAlgorithmName(r.name)).sort((x, y) => y.start - x.start)
    .reduce((t, r) => t.slice(0, r.start) + " ".repeat(r.end - r.start) + t.slice(r.end), flat.slice(0, to));
  const wanted = new Set([...envs.filter((e) => !isAlgorithmName(e.envName)).flatMap((e) => e.refs), ...expandRefRanges(refsIn(outsideAlgorithms), outsideAlgorithms)]);
  const declared = (name: string): boolean =>
    new RegExp(String.raw`\\(?:newtheorem|declaretheorem|newmdtheoremenv)\*?\s*(?:\[[^\]]*\]\s*)?\{\s*${name.replace(/\*$/, "").replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\s*\}`).test(flat);
  return { envs: envs.filter((e) => !isAlgorithmName(e.envName) || declared(e.envName) || (e.label !== null && wanted.has(e.label))), warnings };
}

/** The label set at an algorithm's caption (right after it, or inside it). */
export function captionLabel(body: string): string | null {
  const c = /\\caption\s*(?:\[[^\]]*\])?\s*(?=\{)/.exec(body);
  if (!c) return null;
  const g = readGroup(body, c.index + c[0].length, "{");
  if (!g) return null;
  const inside = /\\label\s*\{([^{}]*)\}/.exec(g.value)?.[1];
  const after = /^\s*\\label\s*\{([^{}]*)\}/.exec(body.slice(g.end))?.[1];
  return (inside ?? after)?.trim() || null;
}

/** Pseudocode: an `algorithm` float, a bare `algorithmic` block (and a paper's own `algorithm` environment). */
const isAlgorithmName = (name: string): boolean => /^algorithm(ic)?\*?$/.test(name);

/** An environment's title: its `[…]` argument — except a float's, which is a placement (`[H]`,
 * `[htbp]`): an algorithm float is named by its `\caption`. */
function envTitle(name: string, opt: string | null, body: string): string | null {
  if (!/^algorithm\*?$/.test(name) || (opt !== null && !/^[!htbpH]+$/.test(opt))) return opt;
  const c = /\\caption\s*(?:\[[^\]]*\])?\s*(?=\{)/.exec(body);
  return c ? readGroup(body, c.index + c[0].length, "{")?.value.trim() ?? null : null;
}

// ---------------------------------------------------------------------------
// bibliography
// ---------------------------------------------------------------------------

const BIBITEM_RE = /\\bibitem\s*(?:\[[^\]]*\])?\s*\{([^{}]*)\}/g;

function parseBibFile(text: string): TexBibEntry[] {
  const out: TexBibEntry[] = [];
  const entryRe = /@([A-Za-z]+)\s*\{\s*([^,\s{}]+)\s*,/g;
  for (const m of text.matchAll(entryRe)) {
    const key = m[2]!.trim();
    if (/^(?:string|comment|preamble)$/i.test(m[1]!)) continue;
    // body: up to the matching close brace of the entry
    let depth = 1;
    let i = m.index + m[0].length;
    for (; i < text.length && depth > 0; i += 1) {
      const ch = text[i]!;
      if (ch === "\\") i += 1;
      else if (ch === "{") depth += 1;
      else if (ch === "}") depth -= 1;
    }
    const body = text.slice(m.index + m[0].length, i - 1);
    const field = (name: string): string => {
      const re = new RegExp(String.raw`(?:^|,)\s*${name}\s*=\s*`, "i");
      const hit = re.exec(body);
      if (!hit) return "";
      const at = hit.index + hit[0].length;
      const braced = readGroup(body, at, "{");
      if (braced) return braced.value.replace(/\s+/g, " ").replace(/[{}]/g, "").trim();
      const quoted = /^\s*"((?:[^"\\]|\\.)*)"/.exec(body.slice(at));
      if (quoted) return quoted[1]!.replace(/\s+/g, " ").trim();
      const bare = /^\s*([^,\s}]+)/.exec(body.slice(at));
      return bare ? bare[1]!.trim() : "";
    };
    const author = field("author") || field("editor");
    const year = field("year") || field("date");
    const title = field("title");
    out.push({ key, text: `${author} (${year || "n.d."}). ${title}`.trim() });
  }
  return out;
}

/**
 * Bibliography entries the paper offers: `\bibitem` bodies from a `thebibliography`
 * environment (an inlined `.bbl` counts), unioned with best-effort `@entry` parses of
 * every `.bib` file named by `\bibliography{}`. A `\bibitem` wins on key collision —
 * it is what the paper actually prints. A named `.bib` that is not shipped (common on
 * arXiv, where only the `.bbl` travels) is skipped, not an error.
 */
export async function parseBibliography(
  flat: string,
  sourceDir: string,
  bibFiles: string[],
): Promise<TexBibEntry[]> {
  const byKey = new Map<string, TexBibEntry>();
  for (const name of bibFiles) {
    const abs = path.resolve(sourceDir, name);
    const rel = path.relative(sourceDir, abs);
    if (rel.startsWith("..") || path.isAbsolute(rel) || !existsSync(abs)) continue;
    for (const entry of parseBibFile(await readFile(abs, "utf8"))) {
      if (!byKey.has(entry.key)) byKey.set(entry.key, entry);
    }
  }
  const hits = [...flat.matchAll(BIBITEM_RE)];
  for (let i = 0; i < hits.length; i += 1) {
    const m = hits[i]!;
    const start = m.index + m[0].length;
    const next = hits[i + 1]?.index ?? flat.length;
    const stop = flat.slice(start, next).search(/\\end\s*\{thebibliography\}/);
    const body = flat.slice(start, stop >= 0 ? start + stop : next);
    byKey.set(m[1]!.trim(), {
      key: m[1]!.trim(),
      text: body.replace(/\s+/g, " ").trim(),
    });
  }
  return [...byKey.values()];
}

// ---------------------------------------------------------------------------
// composition + artifacts
// ---------------------------------------------------------------------------

/** The whole mechanical extraction: flatten, learn the env map, pull the environments,
 * read the bibliography. Pure function of the source tree. `warnings` lists everything
 * the parser left out on purpose (a repeated `\input`, a macro-named `\input`, a proof
 * attached to nothing, a duplicate label) — nothing is dropped silently. `runDir`, with a
 * recorded reading to replay: the run whose flat text on file stands (`keepFlatOnFile`). */
export async function buildEnvsJson(
  sourceDir: string,
  mainFile: string,
  noteMacros: NoteMacroSetting = true,
  runDir?: string,
): Promise<{ envs: EnvsJson; flat: FlatTex; warnings: string[] }> {
  let flat = await flattenTex(sourceDir, mainFile, noteMacros);
  if (runDir && typeof noteMacros === "object") flat = await keepFlatOnFile(runDir, flat);
  const newtheorem = parseNewtheorems(flat.text);
  const { envs, warnings } = extractEnvs(flat.text, flat.lineMap, newtheorem);
  warnings.push(...(await localPackageWarnings(sourceDir, mainFile, flat, newtheorem, envs)));
  const bibliography = await parseBibliography(flat.text, sourceDir, flat.bibFiles);
  return {
    envs: {
      main_file: toPosix(mainFile),
      files: flat.files,
      newtheorem,
      envs,
      bibliography,
      ...(flat.notes ? { note_macros: flat.notes.table } : {}),
    },
    flat,
    warnings: [...flat.warnings, ...warnings, ...noteLossWarnings(envs, flat)],
  };
}

const USEPACKAGE_RE = /\\(usepackage|RequirePackage)\s*(?:\[[^\]]*\])?\s*\{([^{}]*)\}/g;
/** A definition that gives a command its first meaning (a `\renewcommand`, a `\let` or a patch only
 * changes one every reader already has); the name follows, braced or not. */
const NEW_COMMAND_RE = new RegExp(
  String.raw`\\(?:newcommandx?|providecommandx?|DeclareRobustCommand|newrobustcmd|providerobustcmd|DeclareMathOperator|DeclarePairedDelimiter[A-Za-z]*|(?:New|Provide|Declare)(?:Expandable)?DocumentCommand|[egx]?def)\*?(?![A-Za-z@])\s*\{?\s*\\([A-Za-z@]+)`,
  "g",
);

/** One warning per `.sty` the paper loads (`\usepackage` / `\RequirePackage`, a shipped package's own
 * loads followed) that its source tree ships, when the extracted results use a command it introduces
 * or the document opens a theorem environment it declares: the flattener reads no package, so those
 * are undefined to every reader of the flat text (unless the paper defines them too). A citation command (`\cite…`, `\…cite`) is read by
 * its name whatever package defines it, so it does not count. Silent for a shipped style the results
 * never touch. */
async function localPackageWarnings(
  sourceDir: string,
  mainFile: string,
  flat: FlatTex,
  newtheorem: Record<string, EnvKind>,
  envs: readonly TexEnv[],
): Promise<string[]> {
  const out: string[] = [];
  const ownDefs = new Set([...flat.text.matchAll(NEW_COMMAND_RE)].map((d) => d[1]!));
  const used = new Set(envs.flatMap((e) => [...`${e.title ?? ""}\n${e.body}\n${e.proof ?? ""}`.matchAll(/\\([A-Za-z@]+)/g)].map((m) => m[1]!)).filter((n) => !ownDefs.has(n)));
  const beginDoc = /\\begin\s*\{document\}/.exec(flat.text);
  const opened = new Set([...flat.text.slice(beginDoc ? beginDoc.index : 0).matchAll(/\\begin\s*\{([^{}]+)\}/g)].map((m) => m[1]!.trim().replace(/\*$/, "")));
  const starts = lineStarts(flat.text);
  const seen = new Set<string>();
  const bases = [path.dirname(path.resolve(sourceDir, mainFile)), sourceDir];
  const visit = async (text: string, where: (at: number) => string): Promise<void> => {
    for (const m of text.matchAll(USEPACKAGE_RE)) {
      for (const name of m[2]!.split(",").map((x) => x.trim()).filter(Boolean)) {
        const abs = bases.map((b) => path.resolve(b, `${name}.sty`)).find((a) => !path.relative(sourceDir, a).startsWith("..") && existsSync(a));
        if (!abs) continue;
        const rel = toPosix(path.relative(sourceDir, abs));
        if (seen.has(rel)) continue;
        seen.add(rel);
        const body = blankTexComments((await readFile(abs, "latin1")).replace(/\r\n?/g, "\n"));
        const defined = [...new Set([...body.matchAll(NEW_COMMAND_RE)].map((d) => d[1]!))];
        const inResults = defined.filter((n) => used.has(n) && !/^cite|cite$/i.test(n));
        const theorems = Object.keys(parseNewtheorems(body)).filter((n) => !(n in newtheorem) && opened.has(n));
        if (inResults.length > 0 || theorems.length > 0) {
          out.push(
            `${where(m.index)}: \\${m[1]}{${name}} loads ${rel}, which the paper's source ships; the flattener does not read a package, so ` +
              `the agents and the page do not see its definitions — it defines ${defined.length} command(s), ${inResults.length} of them used in ` +
              `the extracted results${inResults.length > 0 ? ` (${inResults.slice(0, 5).map((n) => `\\${n}`).join(", ")}${inResults.length > 5 ? ", …" : ""})` : ""}` +
              `${theorems.length > 0 ? `, and it declares the theorem environment(s) ${theorems.join(", ")} the document opens, whose results are not extracted` : ""}; ` +
              `inline ${rel} into the main file's preamble in place of the \\${m[1]} (between \\makeatletter and \\makeatother) in the run's source copy`,
          );
        }
        await visit(body, () => rel);
      }
    }
  };
  await visit(flat.text, (at) => {
    const line = flat.lineMap[lineOf(starts, at)];
    return line ? `${line.file}:${line.line}` : `flat:${at}`;
  });
  return out;
}

/** Persist the extraction under `runDir`: `discovery/envs.json`, `discovery/flat.tex`,
 * `discovery/flat.linemap.json`, and `discovery/author_notes.json` when note macros were read away. */
export async function writeEnvsArtifacts(
  runDir: string,
  envs: EnvsJson,
  flat: FlatTex,
): Promise<void> {
  const flatPath = path.join(runDir, VERIFY_FILES.flatTex);
  await mkdir(path.dirname(flatPath), { recursive: true });
  await writeJsonAtomic(path.join(runDir, VERIFY_FILES.envsJson), envs);
  await writeFile(flatPath, flat.text, "utf8");
  const map: FlatTexLineMap = { lineMap: flat.lineMap };
  await writeJsonAtomic(path.join(runDir, VERIFY_FILES.flatLineMap), map);
  const notesFile = path.join(runDir, AUTHOR_NOTES_FILE);
  const record = flat.notes ? flat.notes.record : undefined;
  if (record && record.read_with.length + record.left.length > 0) await writeJsonAtomic(notesFile, record);
  else if (record !== null) await rm(notesFile, { force: true });
}
