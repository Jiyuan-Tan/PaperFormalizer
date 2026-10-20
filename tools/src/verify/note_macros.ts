/**
 * Authors' NOTE MACROS — the wrappers co-authors put around edited passages and the comments they leave
 * in the source — read away when the paper is flattened, so that no later stage sees text cut inside one.
 *
 * Deterministic rules only; text the PDF shows is never removed or altered silently, and whatever these
 * rules do not cover is left as written and handed to the orchestrator in a parser warning.
 *
 * A macro DEFINED IN THE PAPER with one mandatory argument is read by its body:
 *  - `keep`    the body is exactly `#1` under colour, highlight or grouping (`{\color{c} #1}`,
 *              `\textcolor{c}{#1}`, `\hl{#1}`): the macro goes, the content stays in its group — the
 *              braces go too only when the content spans several sentences (never inside mathematics);
 *  - `hide`    the body is empty: the use goes;
 *  - `comment` the body passes `#1` to a note command (`\todo`, `\marginpar`, …): the use goes.
 * It is read only when every definition of its name — in the paper and in the `.sty` / `.cls` files the
 * source ships — is parsed, they agree, none sits in a conditional or a group and none comes after
 * `\begin{document}`. A few commands of packages the paper loads are read from a table
 * (`PACKAGE_COMMANDS`), unless anything the source ships defines the name.
 * A use without a braced argument, with an argument that does not close, or holding part of an
 * environment is left as written.
 *
 * Everything removed or dropped is recorded whole (`discovery/author_notes.json`).
 *
 * The edits keep every line where it is (`flat.linemap.json` stays valid): tokens are removed inside
 * their line, removed text leaves its line breaks, and a line a removal empties in the middle of a
 * paragraph keeps an empty group (`{}`), so no paragraph break appears that the PDF does not have. The
 * same edits are replayed on the source files (`unwrapSource`) for what is written from them: the
 * corrected paper, the page, and the annotated paper — which keeps the author's wrappers, a note
 * inserted inside one closing it before the note and opening it again after (`applyEditsKeepingNotes`).
 * Pure.
 */
import { blankTexComments } from "../shared/tex_text.js";
import { sentenceSpans, texStructure } from "./transcription_lint.js";

/** The reading's version, recorded with the table (`envs.json` `note_macros`). The rules for a use are
 * code: a run replays its table, and its flat text on file is kept when the replay differs (2: a group
 * is kept within a sentence, a table command yields to any definition, no class is guessed from a tag;
 * 3: braces are dropped only where the content reads the same without them). */
export const NOTE_MACROS_VERSION = 3;
/** How the parser warning about a text removed from a result opens (`tex_envs.ts` `noteLossWarnings`):
 * the V1.5 prompt shows those to whoever grades the result. */
export const NOTE_LOSS_WARNING = "note macros: removed from the";
/** Where the removed notes are recorded, under the run. */
export const AUTHOR_NOTES_FILE = "discovery/author_notes.json";

export type NoteClass = "keep" | "hide" | "comment";
/** One argument of a use: an optional `[…]`, a mandatory `{…}`. */
export type ArgSpec = "o" | "m";

export interface NoteMacro {
  /** Without the backslash. */
  name: string;
  class: NoteClass;
  args: ArgSpec[];
  /** Index (in `args`) of the argument that is the content. */
  content: number;
  from: "definition" | "package";
  /** In plain words, why it is in its class. */
  why: string;
}

/** What a run was read with (`envs.json` `note_macros`): present = the reading was on. */
export interface NoteMacroTable {
  version: number;
  macros: NoteMacro[];
  /** Macros the detection left as written, and why (said again when the table is replayed). */
  declined?: Declined[];
}

/** A macro left as written: `\name <reason>`. */
export interface Declined { name: string; reason: string }

export type DefinitionClass = NoteClass | "leave";

// ---------------------------------------------------------------------------
// scanning helpers
// ---------------------------------------------------------------------------

/** The balanced `open…close` group at `i` exactly (no leading space): its inside and the offset past
 * it, `\x` pairs skipped. Null when none opens there or it does not close. */
function groupAt(s: string, i: number, open: "{" | "[" = "{"): { value: string; start: number; end: number } | null {
  if (s[i] !== open) return null;
  const close = open === "{" ? "}" : "]";
  let depth = 0;
  let braces = 0;
  for (let k = i; k < s.length; k += 1) {
    const c = s[k]!;
    if (c === "\\") {
      k += 1;
      continue;
    }
    if (open === "[") {
      // a `]` inside braces does not close an optional argument
      if (c === "{") braces += 1;
      else if (c === "}") {
        braces -= 1;
        if (braces < 0) return null;
      }
      if (braces > 0) continue;
    }
    if (c === open) depth += 1;
    else if (c === close) {
      depth -= 1;
      if (depth === 0) return { value: s.slice(i + 1, k), start: i, end: k + 1 };
    }
  }
  return null;
}

/** Past spaces and at most one line break (a blank line ends the search for an argument, as in TeX). */
function skipBlank(s: string, i: number): number {
  let k = i;
  let breaks = 0;
  while (k < s.length) {
    const c = s[k]!;
    if (c === "\n") {
      breaks += 1;
      if (breaks > 1) return i;
    } else if (c !== " " && c !== "\t") break;
    k += 1;
  }
  return k;
}

const VERBATIM_BLOCK = /\\begin\s*\{(verbatim\*?|Verbatim\*?|BVerbatim\*?|LVerbatim\*?|lstlisting\*?|minted\*?|alltt\*?|tcblisting\*?|comment)\}/g;
const INLINE_VERB = /\\(?:verb|lstinline|path|url|nolinkurl|detokenize|mintinline\s*(?:\[[^\]\n]*\])?\s*\{[^{}\n]*\})\*?\s*([^A-Za-z\s*])/g;

/** A source text with what TeX does not read as TeX blanked, offsets kept: `%` comments, verbatim and
 * `comment` environments, `\verb`, `\url{…}`, `\path`, `\detokenize{…}`. Notes are searched for in it, so one
 * inside a comment or a literal text is never met. */
export function scanTextOf(source: string): string {
  const chars = blankTexComments(source).split("");
  const text = chars.join("");
  const blank = (a: number, b: number): void => {
    for (let k = a; k < b; k += 1) if (chars[k] !== "\n") chars[k] = " ";
  };
  let last = 0;
  for (const m of text.matchAll(VERBATIM_BLOCK)) {
    if (m.index < last) continue;
    const close = new RegExp(`\\\\end\\s*\\{${m[1]!.replace(/\*/g, "\\*")}\\}`).exec(text.slice(m.index + m[0].length));
    last = close ? m.index + m[0].length + close.index + close[0].length : text.length;
    blank(m.index, last);
  }
  for (const m of text.matchAll(INLINE_VERB)) {
    const from = m.index + m[0].length;
    const close = m[1] === "{" ? (groupAt(text, from - 1)?.end ?? 0) - 1 : text.indexOf(m[1]!, from);
    const eol = text.indexOf("\n", from);
    if (close >= 0 && (eol < 0 || close < eol)) blank(m.index, close + 1);
  }
  return chars.join("");
}

// ---------------------------------------------------------------------------
// definitions
// ---------------------------------------------------------------------------

export interface MacroDef {
  name: string;
  /** The body of a ONE-argument definition this module parses (`\newcommand{\x}[1]{…}`, `\def\x#1{…}`,
   * `\NewDocumentCommand{\x}{m}{…}`); null for any other definition of the name. */
  body: string | null;
  start: number;
  end: number;
  /** Inside a group or a conditional: it may not be the definition in force. */
  conditional: boolean;
}

/** Every command that gives a control sequence a meaning; the name follows it, braced or not. */
const DEFINER = new RegExp(
  String.raw`\\(` +
    [
      "(?:re)?newcommandx?", "providecommandx?", "DeclareRobustCommand", "(?:re)?newrobustcmd", "providerobustcmd", "DeclareMath[A-Za-z]+", "DeclarePairedDelimiter[A-Za-z]*",
      "DeclareTextFontCommand", "DeclareOldFontCommand", "(?:New|Renew|Provide|Declare)(?:Expandable)?DocumentCommand", "(?:New|Renew|Declare)CommandCopy",
      "[egx]?def", "let", "futurelet", "chardef", "mathchardef", "(?:x?app|x?pre)tocmd", "patchcmd", "g?appto", "g?preto",
    ].join("|") +
    String.raw`)\*?(?![A-Za-z@])`,
  "g",
);
const NAME = /\\([A-Za-z@]+)/y;

/** Every definition of a control sequence in `scan` (comments already blanked), in order — those inside
 * another definition's body or a group too (`conditional`). */
export function parseMacroDefinitions(scan: string): MacroDef[] {
  const out: MacroDef[] = [];
  // `conditional`: brace depth and `\if…\fi` depth at each definition, in one forward pass. An `\if…{`
  // is a macro taking arguments (etoolbox, ifthen), not a conditional `\fi` closes.
  let at = 0;
  let braces = 0;
  let ifs = 0;
  const advance = (to: number): void => {
    for (; at < to; at += 1) {
      const c = scan[at]!;
      if (c === "{") braces += 1;
      else if (c === "}") braces = Math.max(0, braces - 1);
      else if (c === "\\") {
        const m = /^\\(newif\s*\\if[A-Za-z@]*|if[A-Za-z@]*|fi|begingroup|endgroup)(?![A-Za-z@])/.exec(scan.slice(at, at + 48));
        if (m?.[1] === "begingroup") braces += 1;
        else if (m?.[1] === "endgroup") braces = Math.max(0, braces - 1);
        else if (m?.[1] === "fi") ifs = Math.max(0, ifs - 1);
        else if (m && !m[1]!.startsWith("newif") && m[1] !== "iff" && scan[at + m[0].length] !== "{") ifs += 1;
        at += m ? m[0].length - 1 : 1;
      }
    }
  };
  DEFINER.lastIndex = 0;
  for (let m = DEFINER.exec(scan); m; m = DEFINER.exec(scan)) {
    let j = skipBlank(scan, m.index + m[0].length);
    const braced = scan[j] === "{";
    if (braced) j = skipBlank(scan, j + 1);
    NAME.lastIndex = j;
    const nm = NAME.exec(scan);
    if (!nm) continue;
    j += nm[0].length;
    if (braced) {
      j = skipBlank(scan, j);
      if (scan[j] !== "}") continue;
      j += 1;
    }
    if (m.index >= at) advance(m.index);
    // the one-argument signature of each family, then the body
    const how = m[1]!;
    // (a `\providecommand` defines nothing when the name exists; a space after `#1` delimits the argument)
    const sig = /^(?:(?:re)?newcommand|DeclareRobustCommand)$/.test(how) ? /^\s*\[\s*1\s*\]\s*(?=\{)/ : /^(?:New|Renew|Declare)DocumentCommand$/.test(how) ? /^\s*\{\s*\+?m\s*\}\s*(?=\{)/ : /^g?def$/.test(how) ? /^#1(?=\{)/ : null;
    const head = sig?.exec(scan.slice(j, j + 40));
    const body = head ? groupAt(scan, j + head[0].length) : null;
    // the span of a definition this module does not parse: its optional and braced arguments
    let end = j;
    if (!body && !/^(?:let|futurelet|chardef|mathchardef)$/.test(how)) {
      const open = /def$/.test(how) ? /^[^{}\n]*(?=\{)/.exec(scan.slice(end, end + 80)) : null;
      if (open) end += open[0].length;
      for (let g = groupAt(scan, skipBlank(scan, end), "[") ?? groupAt(scan, skipBlank(scan, end)); g; g = groupAt(scan, skipBlank(scan, end), "[") ?? groupAt(scan, skipBlank(scan, end))) end = g.end;
    }
    out.push({ name: nm[1]!, body: body ? body.value : null, start: m.index, end: body ? body.end : end, conditional: braces > 0 || ifs > 0 });
  }
  // a name given a meaning through its letters (`\csdef{x}`, `\@namedef{x}`, `\csname x\endcsname`)
  for (const m of scan.matchAll(/\\(?:cs[egx]?def|cslet|csletcs|@namedef)\s*\{\s*([A-Za-z@]+)\s*\}|\\csname\s*([A-Za-z@]+)\s*\\endcsname/g)) {
    out.push({ name: (m[1] ?? m[2])!, body: null, start: m.index, end: m.index + m[0].length, conditional: false });
  }
  return out.sort((a, b) => a.start - b.start);
}

/** The outermost definition spans of `defs` (a definition inside another's body lies in its span). */
function definitionSpans(defs: readonly MacroDef[]): Array<{ start: number; end: number }> {
  const out: Array<{ start: number; end: number }> = [];
  for (const d of [...defs].sort((a, b) => a.start - b.start || b.end - a.end)) {
    const last = out[out.length - 1];
    if (last && d.start < last.end) last.end = Math.max(last.end, d.end);
    else out.push({ start: d.start, end: d.end });
  }
  return out;
}

// ---------------------------------------------------------------------------
// classification of a definition's body
// ---------------------------------------------------------------------------

/** Commands that print nothing and change nothing a reader sees. */
const NEUTRAL = new Set(["normalcolor", "leavevmode", "relax", "protect"]);
/** Colour / highlight around a text: the number of arguments before the text. */
const COLOUR_WRAP = new Map([["textcolor", 1], ["hl", 0]]);
/** Commands that set their argument beside the text, as a note on it. */
const NOTE_WRAP = new Set(["todo", "marginpar", "marginnote", "fixme", "fxnote", "fxwarning", "fxerror", "fxfatal", "missingfigure"]);
const PARAM = "\u0001";

/** A colour named by a constant other than white (text set in white is text hidden: not this module's to read). */
const visible = (colour: string | null): boolean => colour !== null && /^[A-Za-z0-9!., -]+$/.test(colour) && colour.trim() !== "white";

/** `body` with colour, highlight and grouping read away: `#1` (`PARAM`) and whatever else it prints.
 * `note`: `#1` is the argument of a note command. */
function reduceBody(s: string, f: { note?: boolean }): string {
  let out = "";
  for (let i = 0; i < s.length; ) {
    const c = s[i]!;
    const g = c === "{" ? groupAt(s, i) : null;
    if (g) {
      out += reduceBody(g.value, f);
      i = g.end;
      continue;
    }
    if (s.startsWith("#1", i)) {
      out += PARAM;
      i += 2;
      continue;
    }
    const m = c === "\\" ? /^\\([A-Za-z@]+)\*?/.exec(s.slice(i)) : null;
    if (!m) {
      out += c === "\\" ? s.slice(i, i + 2) : c;
      i += c === "\\" ? 2 : 1;
      continue;
    }
    const name = m[1]!;
    let j = i + m[0].length;
    const opts = (): void => {
      for (let o = groupAt(s, skipBlank(s, j), "["); o; o = groupAt(s, skipBlank(s, j), "[")) j = o.end;
    };
    const arg = (): string | null => {
      const a = groupAt(s, skipBlank(s, j));
      if (a) j = a.end;
      return a ? a.value : null;
    };
    if (NEUTRAL.has(name)) out += " ";
    else if (name === "color") {
      opts();
      out += visible(arg()) ? " " : "\\color";
    } else if (COLOUR_WRAP.has(name) || NOTE_WRAP.has(name)) {
      opts();
      const seen = COLOUR_WRAP.get(name) !== 1 || visible(arg());
      const x = arg();
      const inner = x === null || !seen ? null : reduceBody(x, f);
      // a note command is read only as the note the whole argument is
      if (inner === null || (NOTE_WRAP.has(name) && inner.trim() !== PARAM)) out += `\\${name}`;
      else {
        if (NOTE_WRAP.has(name)) f.note = true;
        out += inner;
      }
    } else out += `\\${name}`;
    i = j;
  }
  return out;
}

/**
 * The class of a one-argument macro from its body: empty → `hide`; exactly `#1` under colour, highlight
 * or grouping → `keep`; exactly `#1` as the argument of a note command → `comment`; anything else — a
 * body that prints any other text or command — → `leave`.
 */
export function classifyBody(body: string): { class: DefinitionClass; why: string } {
  if (body.replace(/[{}\s]/g, "") === "") return { class: "hide", why: "its definition is empty" };
  const f: { note?: boolean } = {};
  if (reduceBody(body, f).trim() !== PARAM) return { class: "leave", why: "its definition prints more than its argument" };
  return f.note ? { class: "comment", why: "its definition sets its argument as a side note" } : { class: "keep", why: "its definition only colours or groups its argument" };
}

// ---------------------------------------------------------------------------
// the table: the paper's definitions + a few commands of packages it loads
// ---------------------------------------------------------------------------

interface PackageCommand { pkg: string | null; class: NoteClass; args: ArgSpec[]; content: number; why: string }
/** Change-tracking and note commands read by name (`pkg: null`: the LaTeX kernel's), only when the
 * paper loads the package and nothing the source ships defines the name. */
export const PACKAGE_COMMANDS: ReadonlyMap<string, PackageCommand> = new Map<string, PackageCommand>([
  ["added", { pkg: "changes", class: "keep", args: ["o", "m"], content: 1, why: "changes: added text" }],
  ["deleted", { pkg: "changes", class: "hide", args: ["o", "m"], content: 1, why: "changes: deleted text" }],
  ["replaced", { pkg: "changes", class: "keep", args: ["o", "m", "m"], content: 1, why: "changes: the new text of a replacement" }],
  ["hl", { pkg: "soul", class: "keep", args: ["m"], content: 0, why: "soul: highlighted text" }],
  ["sout", { pkg: "ulem", class: "hide", args: ["m"], content: 0, why: "ulem: struck-out text" }],
  ["todo", { pkg: "todonotes", class: "comment", args: ["o", "m"], content: 1, why: "todonotes: a to-do note" }],
  ["missingfigure", { pkg: "todonotes", class: "comment", args: ["o", "m"], content: 1, why: "todonotes: a figure placeholder" }],
  ["marginpar", { pkg: null, class: "comment", args: ["o", "m"], content: 1, why: "a margin note" }],
]);

/** A `.sty` / `.cls` file of the source tree the paper loads (comments blanked). */
export interface ShippedFile { name: string; text: string }

const LOADS = /\\(?:usepackage|RequirePackage|documentclass|LoadClass(?:WithOptions)?)\s*(?:\[[^\]]*\])?\s*\{([^{}]*)\}/g;
/** The packages and classes `scan` loads, by name. */
export function loadedPackages(scan: string): string[] {
  const out: string[] = [];
  for (const m of scan.matchAll(LOADS)) for (const n of m[1]!.split(",").map((x) => x.trim()).filter(Boolean)) if (!out.includes(n)) out.push(n);
  return out;
}

/**
 * The note macros a paper is read with. `text`: the flattened paper (comments stripped); `shipped`: the
 * `.sty` / `.cls` files it loads that its source tree ships. A name is read only when every definition
 * of it agrees (see the module comment) and one of them is the paper's or a shipped package's (a
 * class file is the publisher's); `declined`: the names that would have been read otherwise.
 */
export function detectNoteMacros(text: string, shipped: readonly ShippedFile[] = []): NoteMacroTable {
  interface Placed { def: MacroDef; where: string; inDocument: boolean }
  const byName = new Map<string, Placed[]>();
  const begin = /\\begin\s*\{document\}/.exec(text)?.index ?? text.length;
  for (const [where, defs] of [...shipped.map((s) => [s.name, parseMacroDefinitions(s.text)] as const), ["the paper", parseMacroDefinitions(text)] as const]) {
    for (const def of defs) byName.set(def.name, [...(byName.get(def.name) ?? []), { def, where, inDocument: where === "the paper" && def.start > begin }]);
  }
  const loaded = new Set([text, ...shipped.map((s) => s.text)].flatMap((s) => loadedPackages(s)));
  const macros: NoteMacro[] = [];
  const declined: Declined[] = [];
  for (const [name, defs] of byName) {
    const pkg = PACKAGE_COMMANDS.get(name);
    // a shipped copy of the package itself defines its own command: the table reads it
    if (pkg && defs.every((d) => d.where === `${pkg.pkg}.sty`)) continue;
    const classes = defs.map((d) => (d.def.body !== null ? classifyBody(d.def.body) : null));
    const active = pkg !== undefined && (pkg.pkg === null || loaded.has(pkg.pkg));
    // a formatting or note command its body goes through, which the paper or a file it ships defines itself
    const through = defs.flatMap((d) => [...(d.def.body ?? "").matchAll(/\\([A-Za-z@]+)/g)].map((m) => m[1]!)).find((n) => (n === "color" || COLOUR_WRAP.has(n) || NOTE_WRAP.has(n)) && byName.has(n));
    const reason = active
      ? `is also a command of ${pkg.pkg ?? "LaTeX"}, which the paper loads`
      : through !== undefined
        ? `is defined through \\${through}, which the paper or a file it ships defines itself`
        : classes.some((c) => c === null)
      ? "has a definition that is not a one-argument macro this reader parses"
      : defs.some((d) => d.def.conditional)
        ? "is defined inside a conditional or a group"
        : defs.some((d) => d.inDocument)
          ? "is defined after \\begin{document}"
          : new Set(classes.map((c) => c!.class)).size > 1
            ? "has definitions that differ"
            : null;
    const c = classes.find((x) => x !== null && x.class !== "leave");
    if (reason === null && c && defs.some((d) => !/\.cls$/i.test(d.where))) macros.push({ name, class: c.class as NoteClass, args: ["m"], content: 0, from: "definition", why: c.why });
    else if (reason !== null && (c || active)) declined.push({ name, reason });
  }
  for (const [name, p] of PACKAGE_COMMANDS) {
    if ((p.pkg !== null && !loaded.has(p.pkg)) || (byName.get(name) ?? []).some((d) => d.where !== `${p.pkg}.sty`)) continue;
    macros.push({ name, class: p.class, args: [...p.args], content: p.content, from: "package", why: p.why });
  }
  return { version: NOTE_MACROS_VERSION, macros, ...(declined.length > 0 ? { declined } : {}) };
}

/** Offsets of `text` inside mathematics, as a test (the regions are found once, when first asked). */
function mathTest(text: string): (at: number) => boolean {
  let regions: Array<{ start: number; end: number }> | null = null;
  return (at) => (regions ??= texStructure(text).filter((r) => r.math)).some((r) => r.start <= at && at < r.end);
}

// ---------------------------------------------------------------------------
// uses → edits
// ---------------------------------------------------------------------------

/** One change of the text: `drop` a wrapper's tokens (`put`: what stands in their place), or `gone` —
 * text the PDF does not print. */
export interface NoteEdit { start: number; end: number; kind: "drop" | "gone"; put?: string }

/** A wrapper whose content stays and whose group went: `[start, open)` its opening tokens, `[close, end)` its closing ones. */
export interface NoteWrapper { start: number; open: number; close: number; end: number; reopen: string; closer: string }

export interface NoteUse {
  /** `\name`. */
  macro: string;
  class: NoteClass;
  start: number;
  end: number;
  /** The content argument. */
  text: string;
  /** What a kept use drops beside its wrapper: its other arguments (the old text of a replacement). */
  dropped?: string;
}

/** A use left as written. `breaks`: a unit cut inside it would not be balanced TeX. */
export interface NoteLeft { at: number; macro: string; reason: string; breaks: boolean }

export interface NoteScan {
  edits: NoteEdit[];
  wrappers: NoteWrapper[];
  uses: NoteUse[];
  left: NoteLeft[];
}

/** Does a text hold more than one sentence, paragraph or list item (the paper's units are cut at these)? */
export function spansSentences(text: string): boolean {
  return /\n[ \t]*\n/.test(text) || /\\item(?![A-Za-z@])/.test(text) || sentenceSpans(text).length > 1;
}

/** `\begin` and `\end` pair up inside `text`. */
function environmentsBalanced(text: string): boolean {
  const open: string[] = [];
  for (const m of text.matchAll(/\\(begin|end)\s*\{([^{}]*)\}/g)) {
    if (m[1] === "begin") open.push(m[2]!);
    else if (open.pop() !== m[2]) return false;
  }
  return open.length === 0;
}

/**
 * The note-macro uses of `scan` (a text with comments and verbatim material blanked, offsets kept) and the
 * edits that read them away. Definitions are never touched (nor a use whose argument holds a macro
 * parameter); nested uses are read inside a kept argument.
 */
export function scanNotes(scan: string, table: NoteMacroTable): NoteScan {
  const out: NoteScan = { edits: [], wrappers: [], uses: [], left: [] };
  const byName = new Map(table.macros.map((m) => [m.name, m] as const));
  const defs = definitionSpans(parseMacroDefinitions(scan));
  const inMath = mathTest(scan);
  let d = 0;
  const leave = (at: number, macro: string, reason: string, breaks = false): null => {
    out.left.push({ at, macro, reason, breaks });
    return null;
  };

  /** Is `at` inside an optional argument: a `[` of its paragraph and brace level not yet closed? */
  const insideOptional = (at: number): boolean => {
    for (let k = at - 1, depth = 0, closed = 0; k >= 0 && !/^\n[ \t]*\n/.test(scan.slice(k, k + 40)); k -= 1) {
      const c = scan[k]!;
      if (scan[k - 1] === "\\") k -= 1;
      else if (c === "}") depth += 1;
      else if (c === "{") {
        if (depth === 0) return false;
        depth -= 1;
      } else if (depth === 0 && c === "]") closed += 1;
      else if (depth === 0 && c === "[") {
        if (closed === 0) return true;
        closed -= 1;
      }
    }
    return false;
  };

  /**
   * A wrapper around the group `[open - 1, close]` read as `keep` (`end`: past its last argument,
   * `tail`: the mandatory arguments after the content). The macro goes and the group
   * stays — it may be what the mathematics is (`\lp{a \over b}`, `\sqrt\lp{x}`) — unless the content spans
   * several sentences: then the braces go too, never inside mathematics. False: left as written.
   */
  const keep = (macro: string, start: number, open: number, close: number, end: number, tail: number, dropped: string): boolean => {
    const content = scan.slice(open, close);
    const spans = spansSentences(content);
    if (spans && inMath(start)) {
      leave(start, macro, "spans several sentences inside mathematics", true);
      return false;
    }
    // Without its braces the content must read as it did inside them: no `]` to close an optional argument
    // the use sits in (`insideOptional`), no `[` or `*` for a command before it (or a `\\` ending it) to take.
    // … and no command right before the use to take the group as its argument (`\emph\lp{…}`).
    if (spans && ((content.includes("]") && insideOptional(start)) || /^\s*[[*]/.test(content) || /\\\\\s*$/.test(content) || /[[*]/.test(scan[skipBlank(scan, end)] ?? "") || /\\[A-Za-z@]+$/.test(scan.slice(Math.max(0, start - 40), start)))) {
      leave(start, macro, "spans several sentences where its braces cannot be dropped (a `[`, `]`, `*` or `\\\\` at its edge, or a command right before it)", true);
      return false;
    }
    if (spans) {
      out.edits.push({ start, end: open, kind: "drop" });
      range(open, close);
      out.edits.push({ start: close, end: close + 1, kind: "drop" });
      out.wrappers.push({ start, open, close, end, reopen: scan.slice(start, open), closer: `}${"{}".repeat(tail)}` });
    } else {
      out.edits.push({ start, end: open - 1, kind: "drop" });
      range(open, close);
    }
    if (close + 1 < end) out.edits.push({ start: close + 1, end, kind: "gone" });
    out.uses.push({ macro, class: "keep", start, end, text: content, ...(dropped.trim() ? { dropped } : {}) });
    return true;
  };

  const use = (at: number, nameEnd: number, m: NoteMacro): number | null => {
    const macro = `\\${m.name}`;
    let j = nameEnd;
    const spans: Array<{ start: number; end: number } | null> = [];
    for (const a of m.args) {
      const k = skipBlank(scan, j);
      if (a === "o") {
        const g = scan[k] === "[" ? groupAt(scan, k, "[") : null;
        if (g) j = g.end;
        spans.push(g);
        continue;
      }
      if (scan[k] !== "{") return leave(at, macro, "is used without a braced argument");
      const g = groupAt(scan, k);
      if (!g) return leave(at, macro, "has an argument that does not close", true);
      spans.push(g);
      j = g.end;
    }
    const content = spans[m.content]!;
    const whole = scan.slice(at, j);
    const inner = scan.slice(content.start + 1, content.end - 1);
    if (/(?<!\\)#/.test(whole)) return null; // inside a definition
    if (!environmentsBalanced(whole) || !environmentsBalanced(inner)) return leave(at, macro, "has an argument holding part of an environment", true);
    if (m.class === "keep") {
      const dropped = spans.flatMap((s, i) => (s && i !== m.content ? [scan.slice(s.start, s.end)] : [])).join(" ");
      return keep(macro, at, content.start + 1, content.end - 1, j, m.args.slice(m.content + 1).filter((a) => a === "m").length, dropped) ? j : null;
    }
    // alone on its lines after a row break: no token may stand between a `\\` and an `\hline` or `\multicolumn`
    if (/\\\\\s*$/.test(scan.slice(Math.max(0, at - 200), at)) && /^[ \t]*\n/.test(scan.slice(j, j + 80)) && /\n[ \t]*$/.test(scan.slice(Math.max(0, at - 80), at))) {
      return leave(at, macro, "stands alone on its lines after a row break (`\\\\`)");
    }
    // no `[` or `*` is left for an `\item` or a `\\` before the use to take
    out.edits.push({ start: at, end: j, kind: "gone", ...(/[[*]/.test(scan[skipBlank(scan, j)] ?? "") ? { put: "{}" } : {}) });
    out.uses.push({ macro, class: m.class, start: at, end: j, text: inner });
    return j;
  };

  function range(from: number, to: number): void {
    for (let i = from; i < to; ) {
      if (scan[i] !== "\\") {
        i += 1;
        continue;
      }
      while (d < defs.length && defs[d]!.end <= i) d += 1;
      if (d < defs.length && defs[d]!.start <= i) {
        i = defs[d]!.end;
        continue;
      }
      NAME.lastIndex = i;
      const nm = NAME.exec(scan);
      if (!nm) {
        i += 2;
        continue;
      }
      const end = i + nm[0].length;
      // `\string\lp` prints the name
      const m = /\\string\s*$/.test(scan.slice(Math.max(0, i - 12), i)) ? undefined : byName.get(nm[1]!);
      i = (m ? use(i, end, m) : null) ?? end;
    }
  }
  range(0, scan.length);
  out.edits.sort((a, b) => a.start - b.start);
  out.wrappers.sort((a, b) => a.start - b.start);
  out.uses.sort((a, b) => a.start - b.start);
  return out;
}

/** The empty group a source file gets on a line the reading emptied inside a paragraph, marked so that
 * a text written from it can drop the line (`withoutFillerLines`). */
export const SOURCE_FILLER = "{}% line emptied by LeanSmith";

/**
 * `text` with the edits applied. `remove`: tokens are deleted inside their line and removed text leaves
 * its line breaks, so every line keeps its number; a control word the removal would run into the next
 * letter gets a space, and a line the edits empty between two lines of a paragraph an empty group
 * (`filler`: no paragraph break the PDF does not have). `blank`: every removed character becomes a
 * space — the text keeps its offsets.
 */
export function applyNoteEdits(text: string, edits: readonly NoteEdit[], mode: "remove" | "blank", filler = "{}"): string {
  if (edits.length === 0) return text;
  const pieces: string[] = [];
  let tail = ""; // the last characters written (to see a control word the next piece would extend)
  let last = 0;
  let line = 0;
  /** Lines an edit took text from, or lay across. */
  const touched = new Set<number>();
  const breaks = (s: string): number => s.split("\n").length - 1;
  const emit = (s: string): void => {
    if (s === "") return;
    if (mode === "remove" && /(?:^|[^\\])(?:\\\\)*\\[A-Za-z@]+$/.test(tail) && /^[A-Za-z@]/.test(s)) pieces.push(" ");
    pieces.push(s);
    tail = (tail + s).slice(-40);
    line += breaks(s);
  };
  for (const e of edits) {
    if (e.start < last) continue;
    emit(text.slice(last, e.start));
    const cut = text.slice(e.start, e.end);
    const n = breaks(cut);
    for (let k = line; k <= line + n; k += 1) touched.add(k);
    if (mode === "blank") pieces.push(cut.replace(/[^\n]/g, " "));
    else {
      if (e.put) emit(e.put);
      pieces.push("\n".repeat(n));
    }
    line += n;
    if (n > 0) tail = "";
    last = e.end;
  }
  emit(text.slice(last));
  const out = pieces.join("");
  if (mode === "blank") return out;
  // Lines the edits emptied: between two lines of a paragraph they would read as a paragraph break.
  const lines = out.split("\n");
  const blank = (s: string | undefined): boolean => s === undefined || s.trim() === "";
  for (let i = 0; i < lines.length; i += 1) {
    if (!blank(lines[i]) || !touched.has(i)) continue;
    let j = i;
    while (j + 1 < lines.length && blank(lines[j + 1]) && touched.has(j + 1)) j += 1;
    if (i > 0 && !blank(lines[i - 1]) && !blank(lines[j + 1])) for (let k = i; k <= j; k += 1) lines[k] = filler;
    i = j;
  }
  return lines.join("\n");
}

/** A source file (comments and all) read as the flattened paper is: `remove` for a text that is
 * written out or shown, `blank` for one whose offsets must stay the source's. */
export function unwrapSource(source: string, table: NoteMacroTable | null | undefined, mode: "remove" | "blank", filler = "{}"): string {
  if (!table) return source;
  return applyNoteEdits(source, scanNotes(scanTextOf(source), table).edits, mode, filler);
}

/** A text written from a source read with `SOURCE_FILLER`: the emptied lines gone (the lines around
 * them stay one paragraph). */
export function withoutFillerLines(tex: string): string {
  return tex.split("\n").filter((l) => l !== SOURCE_FILLER).join("\n");
}

// ---------------------------------------------------------------------------
// edits planned on the unwrapped text, written into the source that keeps its wrappers
// ---------------------------------------------------------------------------

/** For each position, the kept wrappers open around it with nothing else opened inside them (a group,
 * an environment), outermost first: the ones a text inserted there may close and open again. */
function wrappersAround(scan: string, wrappers: readonly NoteWrapper[], positions: readonly number[]): Map<number, NoteWrapper[]> {
  const out = new Map<number, NoteWrapper[]>();
  const starts = new Map(wrappers.map((w) => [w.start, w] as const));
  const want = [...new Set(positions)].sort((a, b) => a - b);
  const stack: Array<NoteWrapper | "group" | "env"> = [];
  let p = 0;
  const record = (i: number): void => {
    for (; p < want.length && want[p]! <= i; p += 1) {
      let k = stack.length;
      while (k > 0 && typeof stack[k - 1] === "object") k -= 1;
      out.set(want[p]!, stack.slice(k) as NoteWrapper[]);
    }
  };
  for (let i = 0; i <= scan.length; ) {
    record(i);
    if (i >= scan.length) break;
    const top = stack[stack.length - 1];
    if (typeof top === "object" && top.close === i) {
      stack.pop();
      i = top.end;
      continue;
    }
    const w = starts.get(i);
    if (w) {
      stack.push(w);
      i = w.open;
      continue;
    }
    const c = scan[i]!;
    if (c === "\\") {
      const env = /^\\(begin|end)\s*\{[^{}]*\}/.exec(scan.slice(i, i + 80));
      if (env) {
        if (env[1] === "begin") stack.push("env");
        else {
          const k = stack.lastIndexOf("env");
          if (k >= 0) stack.length = k;
        }
        i += env[0].length;
      } else i += 2;
      continue;
    }
    if (c === "{") stack.push("group");
    else if (c === "}" && stack[stack.length - 1] === "group") stack.pop();
    i += 1;
  }
  return out;
}

/**
 * Apply edits planned on `unwrapSource(orig, table, "blank")` (same offsets) to `orig`, which keeps its
 * wrappers. An edit inside the tokens the reading removed moves out of them; one inside a kept wrapper
 * closes the wrapper before its text and opens it again after, so whatever the edits pair up (a
 * `\macro{` and its `}`) pairs up outside every wrapper. Order at one offset as `applyEdits`: by rank,
 * then plan order.
 */
export function applyEditsKeepingNotes(orig: string, edits: ReadonlyArray<{ at: number; rank: number; text: string; seq: number }>, table: NoteMacroTable): string {
  const scan = scanTextOf(orig);
  const notes = scanNotes(scan, table);
  const snap = (at: number): number => {
    let p = at;
    for (let moved = true; moved; ) {
      moved = false;
      for (const w of notes.wrappers) {
        if (w.start < p && p <= w.open) p = w.start;
        else if (w.close <= p && p < w.end) p = w.end;
        else continue;
        moved = true;
      }
      for (const e of notes.edits) {
        if (e.start < p && p < e.end) {
          p = e.kind === "gone" ? e.end : e.start;
          moved = true;
        }
      }
    }
    return p;
  };
  const placed = edits.map((e) => ({ ...e, at: snap(e.at) })).sort((a, b) => a.at - b.at || a.rank - b.rank || a.seq - b.seq);
  const around = wrappersAround(scan, notes.wrappers, placed.map((e) => e.at));
  let out = "";
  let last = 0;
  for (let i = 0; i < placed.length; ) {
    const at = placed[i]!.at;
    const open = around.get(at) ?? [];
    out += orig.slice(last, at) + [...open].reverse().map((w) => w.closer).join("");
    for (; i < placed.length && placed[i]!.at === at; i += 1) out += placed[i]!.text;
    out += open.map((w) => w.reopen).join("");
    last = at;
  }
  return out + orig.slice(last);
}

// ---------------------------------------------------------------------------
// the flattened paper
// ---------------------------------------------------------------------------

/** `discovery/author_notes.json`: what the paper was read with, and every text read away as not the paper's, whole. */
export interface AuthorNotes {
  version: number;
  /** Each macro met, with the number of its uses read. */
  read_with: Array<{ macro: string; class: NoteClass; uses: number; why: string }>;
  /** Text removed: hidden (the PDF prints nothing) or an author's comment. */
  removed: Array<{ macro: string; class: "hide" | "comment"; file: string; line: number; text: string }>;
  /** What a kept use dropped beside its wrapper (the old text of a replacement, an optional argument). */
  dropped: Array<{ macro: string; file: string; line: number; text: string }>;
  /** Macros and uses left as written, and why. */
  left: string[];
}

export interface NoteReading {
  text: string;
  table: NoteMacroTable;
  notes: AuthorNotes;
  /** For the parse log: one line per macro read. */
  log: string[];
  /** The summary and what was left as written: parser warnings. */
  warnings: string[];
}

/** What the orchestrator does about a macro the reader left (the parser-gap wording of V1's checkpoints). */
export const NOTE_MACRO_HANDOFF =
  "This is a parser gap, not a defect of the paper: if it is an authors' note macro, remove it by the smallest neutral edit in the run's copy of the source (source/), record the edit in pipeline_issues.md, and run it from V1 (a changed source is extracted cold)";

/**
 * Read the note macros of a flattened paper away (`table`: the one a run recorded, else detected from
 * `shipped` and the paper's own definitions). What the reader declines and that matters is ONE warning
 * per macro — a one-argument macro of the paper's it does not read whose argument spans several
 * sentences (a unit cut inside it is not balanced TeX), or a use of a macro it reads that it could not
 * take: the macro, its definition, how many such uses and the first one's place, why, and what to do.
 */
export function readNotes(flat: string, lineMap: ReadonlyArray<{ file: string; line: number }>, shipped: readonly ShippedFile[] = [], table?: NoteMacroTable): NoteReading {
  const read = table ?? detectNoteMacros(flat, shipped);
  const scan = scanNotes(scanTextOf(flat), read);
  const text = applyNoteEdits(flat, scan.edits, "remove");
  const starts = [0];
  for (let i = 0; i < flat.length; i += 1) if (flat[i] === "\n") starts.push(i + 1);
  const origin = (at: number): { file: string; line: number } => {
    let lo = 0;
    let hi = starts.length - 1;
    while (lo < hi) {
      const mid = (lo + hi + 1) >> 1;
      if (starts[mid]! <= at) lo = mid;
      else hi = mid - 1;
    }
    return lineMap[lo] ?? { file: "flat.tex", line: lo + 1 };
  };
  const where = (at: number): string => `${origin(at).file}:${origin(at).line}`;
  const why = new Map<string, string>(read.macros.map((m) => [`\\${m.name}`, m.why]));
  const count = new Map<string, { class: NoteClass; uses: number }>();
  const removed: AuthorNotes["removed"] = [];
  const dropped: AuthorNotes["dropped"] = [];
  const warnings: string[] = [];
  for (const u of scan.uses) {
    count.set(u.macro, { class: u.class, uses: (count.get(u.macro)?.uses ?? 0) + 1 });
    if (u.dropped) dropped.push({ macro: u.macro, ...origin(u.start), text: u.dropped });
    if (u.class === "keep") continue;
    removed.push({ macro: u.macro, class: u.class, ...origin(u.start), text: u.text.trim() });
    if (/\\begin\s*\{/.test(u.text)) warnings.push(`note macros: the ${u.class === "hide" ? "hidden text" : "author's comment"} ${u.macro}{…} at ${where(u.start)} holds an environment; it is not read as part of the paper`);
  }

  // --- what the reader declined: one warning per macro and reason.
  const defs = parseMacroDefinitions(flat);
  const spans = definitionSpans(defs);
  const declined = new Map<string, { macro: string; reason: string; uses: number; first: number; breaks: boolean }>();
  const decline = (macro: string, reason: string, at: number, breaks: boolean): void => {
    const d = declined.get(`${macro}\u0000${reason}`);
    if (d) d.uses += 1;
    else declined.set(`${macro}\u0000${reason}`, { macro, reason, uses: 1, first: at, breaks });
  };
  for (const l of scan.left) decline(l.macro, l.reason, l.at, l.breaks);
  // A one-argument macro of the paper's this reader does not read, around several sentences.
  const classified = new Set(read.macros.map((m) => m.name));
  const reasons = new Map((read.declined ?? []).map((d) => [d.name, d.reason] as const));
  // (a definition taking arguments: `\let\footnote\endnote` is none)
  for (const name of new Set(defs.filter((d) => d.body !== null || reasons.has(d.name) || flat.slice(d.start, d.end).includes("#")).map((d) => d.name))) {
    if (classified.has(name)) continue;
    for (const m of flat.matchAll(new RegExp(`\\\\${name}(?![A-Za-z@])`, "g"))) {
      if (spans.some((s) => s.start <= m.index && m.index < s.end)) continue;
      const g = groupAt(flat, skipBlank(flat, m.index + m[0].length));
      if (g && !g.value.includes("#") && spansSentences(g.value)) decline(`\\${name}`, `${reasons.get(name) ?? "is not a macro this reader reads away (its definition prints more than its argument)"}, and its argument spans several sentences`, m.index, true);
    }
  }
  const definition = (macro: string): string => {
    const d = defs.find((x) => macro === `\\${x.name}`);
    const src = d ? flat.slice(d.start, d.end).replace(/\s+/g, " ") : "";
    return src ? ` (defined: ${src.length > 160 ? `${src.slice(0, 159)}…` : src})` : "";
  };
  const left = [...declined.values()]
    .sort((a, b) => a.first - b.first)
    .map(
      (d) =>
        `${d.macro}${definition(d.macro)} ${d.reason}: left as written (${d.uses} such use(s), first at ${where(d.first)})` +
        `${d.breaks ? "; a unit cut inside such a use is not balanced TeX, and V1 or a later stage will stop on it" : ""}. ${NOTE_MACRO_HANDOFF}.`,
    );
  for (const l of left) warnings.push(`note macros: ${l}`);

  const read_with = [...count].map(([macro, v]) => ({ macro, class: v.class, uses: v.uses, why: why.get(macro) ?? "" }));
  const log = read_with.map((r) =>
    r.class === "keep" ? `unwrapped the note macro ${r.macro} (${r.uses} use(s)): ${r.why}` : `removed the ${r.class === "hide" ? "hidden text" : "author's comments"} of ${r.macro} (${r.uses} use(s)): ${r.why}`,
  );
  if (read_with.length > 0) {
    const part = (cls: NoteClass, letter: string, tail = ""): string | null => {
      const of = read_with.filter((r) => r.class === cls);
      return of.length > 0 ? `${letter} ${of.map((r) => `${r.macro} (${r.uses})`).join(", ")}${tail}` : null;
    };
    const parts = [part("keep", "K"), part("hide", "H", " removed"), part("comment", "C", " removed")].filter((x): x is string => x !== null);
    warnings.unshift(
      `the paper was read with its authors' note macros read away — ${parts.join("; ")} (K: wrapper dropped, text kept; H: text the PDF does not print; C: authors' comments, not part of the paper)` +
        (removed.length + dropped.length > 0 ? ` — every removed text is in ${AUTHOR_NOTES_FILE}` : ""),
    );
  }
  return { text, table: read, notes: { version: NOTE_MACROS_VERSION, read_with, removed, dropped, left }, log, warnings };
}
