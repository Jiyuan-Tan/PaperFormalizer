/**
 * V6 annotated paper — the pure TeX layer.
 *
 * Everything here is a pure function of strings: the colour macros and their preamble injection,
 * the alignment of comment-stripped text (`flat.tex`, `envs.json` bodies) back onto the ORIGINAL
 * source bytes, the math / environment / brace regions a coloured span may never split, the
 * sentence diff between a printed and a corrected statement, and the detectors that flag a
 * model-written fragment the renderer cannot set (`nonAsciiProblem`).
 * Model text is TeX checked at its source by compiling it (`tex_fragment_check.ts`); nothing here
 * repairs it. `annotated_paper.ts` decides WHAT to annotate; this module only knows how to do it
 * without breaking the paper's TeX.
 */
import { blankTexComments } from "../shared/tex_text.js";
import { envTags } from "./tex_balance.js";
import { sentenceSpans } from "./transcription_lint.js";

// ---------------------------------------------------------------------------
// preamble
// ---------------------------------------------------------------------------

/** First line of the macro block; its presence makes the injection a no-op. */
export const VS_BLOCK_MARKER = "% PaperFormalizer annotation macros";
const VS_XCOLOR_LINE = "\\usepackage{xcolor}% added by PaperFormalizer";

/**
 * Each part of an annotation is a BLOCK laid out for reading (user rule 2026-09-25): it starts on its
 * own line after a small vertical gap, its bold label in the part's colour on a line of its own, the
 * content below it indented (`\vsIndent`). Inside the content `\vsLine` starts a labelled field of a
 * note, `\vsItem{(k)}` a numbered clause (hanging indent), `\vsSub` an indented sub-line of a field
 * (the (a)/(b) defects, the "It uses: …" parts of a step), `\vsPar` a paragraph break. In restricted
 * horizontal mode (an `\mbox`, a tabular `l` cell) no paragraph can end, so every one of them leaves
 * a quad or a space instead (`\vsIfInner` decides before any argument is read). Parts never sit
 * inside math. Every macro is `\long` (`\newcommand`), so a blank line in the content is a paragraph.
 */
/** The fragment check's error for a display of a model's text too wide to print legibly (`\\vsFit`). It
 * compiles in the annotated paper (shrunk), so the renderer prints it as written while it is routed back. */
export const DISPLAY_TOO_WIDE = "Display too wide";
/** The macros of a block a repair split off a result, by the block's kind (`core_graph.ts`
 * `splitKind`): confirmed, pending with the owner, and its proof set away from it (corrected view).
 * An annotated paper written before the kinds were told apart uses the corollary macros for every block. */
export const SPLIT_MACROS = {
  corollary: { block: "vsCorollary", proposed: "vsProposedCorollary", proof: "vsCorollaryProof" },
  proposition: { block: "vsSplitProposition", proposed: "vsProposedSplitProposition", proof: "vsSplitPropositionProof" },
} as const;
/** The kind of block a macro of `SPLIT_MACROS` opens (null: not one of them). */
export function splitMacroKind(name: string): "corollary" | "proposition" | null {
  return Object.values(SPLIT_MACROS.proposition).includes(name as never) ? "proposition" : Object.values(SPLIT_MACROS.corollary).includes(name as never) ? "corollary" : null;
}
/** In a split-off block (`\\vsCorollary`, `\\vsSplitProposition`): where the statement ends and its proof (`follows`) begins. */
export const COROLLARY_PROOF = "\\vsLine\\textit{Proof.}";
/** The conditions added to a result, as the last paragraph of its statement in the corrected paper
 * (each a sentence): a paragraph of its own reads after any statement — a sentence, a list, a display. */
export const conditionParagraph = (conditions: readonly string[]): string => `\\emph{Additional condition${conditions.length === 1 ? "" : "s"}.} ${conditions.join(" ")}`;
/** A corollary block's content: its statement and its proof (null: the block carries the statement only). */
export function splitCorollaryBlock(body: string): { statement: string; proof: string | null } {
  const cut = body.indexOf(COROLLARY_PROOF);
  return cut >= 0 ? { statement: body.slice(0, cut), proof: body.slice(cut + COROLLARY_PROOF.length) } : { statement: body, proof: null };
}

export const VS_PREAMBLE_BLOCK = [
  VS_BLOCK_MARKER,
  "\\RequirePackage{graphicx}",
  "\\definecolor{vsRed}{rgb}{0.80,0.00,0.00}",
  "\\definecolor{vsBlue}{rgb}{0.00,0.20,0.80}",
  "\\definecolor{vsNote}{rgb}{0.80,0.40,0.00}",
  "\\newcommand{\\vsIndent}{1.5em}",
  "\\newcommand{\\vsFirst}[2]{#1}",
  "\\newcommand{\\vsSecond}[2]{#2}",
  // Restricted horizontal mode (no paragraph can end) → the first branch, else the second.
  "\\newcommand{\\vsIfInner}{\\ifhmode\\ifinner\\expandafter\\expandafter\\expandafter\\vsFirst\\else\\expandafter\\expandafter\\expandafter\\vsSecond\\fi\\else\\expandafter\\vsSecond\\fi}",
  "\\newcommand{\\vsBreak}{\\ifhmode\\ifinner\\quad\\else\\unskip\\par\\fi\\fi}",
  // A block ends the paper's line itself: a `\\` (with its `*` or `[len]`) the paper writes right after
  // the annotated text would find no line to end, so it is swallowed.
  "\\makeatletter\\newcommand{\\vsEatCr}{\\@ifnextchar\\\\{\\vsGobbleCr}{}}\\def\\vsGobbleCr\\\\{\\@ifstar{\\@ifnextchar[\\vsGobbleOpt{}}{\\@ifnextchar[\\vsGobbleOpt{}}}\\def\\vsGobbleOpt[#1]{}\\makeatother",
  // A block: {colour}{font}{label}{content}.
  "\\newcommand{\\vsBlock}[4]{\\vsIfInner{\\quad{\\color{#1}#2\\textbf{#3} #4}\\quad}{\\vsBreak\\par\\smallskip{\\noindent\\color{#1}#2\\textbf{#3}\\par\\nopagebreak{\\leftskip=\\vsIndent\\relax\\parindent=0pt\\noindent #4\\par}}\\smallskip\\vsEatCr}}",
  // A new line inside a note (the labelled parts of an explanation); a quad where no paragraph can end.
  "\\newcommand{\\vsLine}{\\vsBreak\\noindent}",
  // A label the corrected text keeps from the text it replaces: nothing here (the original keeps it),
  // the `\label` itself in the corrected paper (`corrected_tex.ts`).
  "\\newcommand{\\vsLabel}[1]{}",
  "\\newcommand{\\vsSub}{\\vsIfInner{\\ }{\\vsBreak\\noindent\\hangindent=\\vsIndent\\hangafter=0\\relax}}",
  "\\newcommand{\\vsItem}[1]{\\vsIfInner{\\ #1~}{\\vsBreak\\noindent\\hangindent=2.2em\\hangafter=1\\relax\\makebox[2.2em][l]{#1}}}",
  "\\newcommand{\\vsPar}{\\vsIfInner{\\quad}{\\vsBreak}}",
  // A display: {check}{formula}. Set in the block's text column (the display's indent and width less
  // the block's \leftskip / \rightskip), shrunk to that width when it is wider (TeX cannot break a
  // display), inline where no paragraph can end.
  "\\newif\\ifvsCheck",
  "\\newcommand{\\vsFitIn}[2]{\\vsIfInner{$#2$}{\\[\\displayindent=\\dimexpr\\displayindent+\\leftskip\\relax\\displaywidth=\\dimexpr\\displaywidth-\\leftskip-\\rightskip\\relax\\sbox0{$\\displaystyle #2$}#1\\ifdim\\wd0>\\displaywidth\\resizebox{\\displaywidth}{!}{\\usebox0}\\else\\usebox0\\fi\\]}}",
  // A display in text a model writes: in the fragment check (`\vsChecktrue`) one that would print at
  // less than 5/6 of its size is recorded, and an error at the check's end (`\vsCheckEnd`: any other
  // error of the fragment is met first), so its author breaks it over lines.
  "\\newif\\ifvsTooWide",
  `\\newcommand{\\vsFit}[1]{\\vsFitIn{\\ifvsCheck\\ifdim\\wd0>1.2\\displaywidth\\ifvsTooWide\\else\\global\\vsTooWidetrue\\xdef\\vsTooWideMsg{${DISPLAY_TOO_WIDE} (\\the\\wd0, line \\the\\displaywidth): split it into rows (an aligned environment inside the display)}\\fi\\fi\\fi}{#1}}`,
  "\\newcommand{\\vsCheckEnd}{\\ifvsTooWide\\errmessage{\\vsTooWideMsg}\\fi}",
  // A formula a note quotes from the paper: the paper's text, fitted, never an error.
  "\\newcommand{\\vsDisplay}[1]{\\vsFitIn{}{#1}}",
  // A proof step's alignment display (`align*`, `gather*`, …): the environment itself, or where no
  // paragraph can end its rows inline (`\\` as `;`, no `&`) — {inline form}{the environment}.
  "\\newcommand{\\vsMathEnv}[2]{\\vsIfInner{$#1$}{#2}}",
  "\\newcommand{\\vsOriginal}[1]{\\vsBlock{vsRed}{}{Original:}{#1}}",
  "\\newcommand{\\vsCorrected}[1]{\\vsBlock{vsBlue}{}{Revised:}{#1}}",
  "\\newcommand{\\vsClarified}[1]{\\vsBlock{vsBlue}{}{Clarified statement:}{#1}}",
  "\\newcommand{\\vsNote}[1]{\\vsBlock{vsNote}{\\normalfont\\small}{PaperFormalizer:}{#1}}",
  // A clarification: a reading pinned for formalization (the referee's, the owner's, a symbol's).
  "\\newcommand{\\vsReading}[1]{\\vsBlock{vsNote}{\\normalfont\\small}{Clarification:}{#1}}",
  "\\newcommand{\\vsReadingOwner}[1]{\\vsBlock{vsNote}{\\normalfont\\small}{Clarification (author):}{#1}}",
  "\\newcommand{\\vsReadingSymbol}[2]{\\vsBlock{vsNote}{\\normalfont\\small}{Clarification (symbol #1):}{#2}}",
  // A detail of a corrected proof step: what the referee and the Lean proof need beyond the paper's
  // level of detail, beside the step it completes (the fixer writes it in its proof text).
  "\\newcommand{\\vsDetail}[1]{\\vsBlock{vsNote}{\\normalfont\\small}{Proof detail:}{#1}}",
  // A condition the verified statement carries beyond the printed text (the referee's, the owner's).
  "\\newcommand{\\vsCondition}[1]{\\vsBlock{vsNote}{\\normalfont\\small}{Bookkeeping condition:}{#1}}",
  "\\newcommand{\\vsConditionOwner}[1]{\\vsBlock{vsNote}{\\normalfont\\small}{Bookkeeping condition:}{#1}}",
  // A proof correction (the repair's proof note, after the proof it amends) and the step of the
  // printed proof it replaces.
  "\\newcommand{\\vsProof}[1]{\\vsBlock{vsBlue}{}{Revised proof (confirmed):}{#1}}",
  "\\newcommand{\\vsStep}[1]{\\vsBlock{vsRed}{}{Original:}{#1}}",
  // A revised step of the paper's proof, right after the printed step it replaces, and a step added.
  "\\newcommand{\\vsCorrectedStep}[1]{\\vsBlock{vsBlue}{}{Revised:}{#1}}",
  // A block a repair splits off a result, after the result: {node id}{the result}{content} — a
  // corollary of the corrected result, or a proposition the printed statement bundled in
  // (`SPLIT_MACROS`). The id is for the reader of the source (the UI); it prints nothing.
  "\\newcommand{\\vsCorollary}[3]{\\vsBlock{vsBlue}{}{Corollary of #2:}{#3}}",
  "\\newcommand{\\vsProposedCorollary}[3]{\\vsBlock{vsBlue}{}{Proposed corollary of #2 (awaiting your decision):}{#3}}",
  "\\newcommand{\\vsSplitProposition}[3]{\\vsBlock{vsBlue}{}{Proposition stated in #2:}{#3}}",
  "\\newcommand{\\vsProposedSplitProposition}[3]{\\vsBlock{vsBlue}{}{Proposed proposition stated in #2 (awaiting your decision):}{#3}}",
  // A decision pending with the paper's owner (a halt): the proposed repair, a proposed F-stage
  // rewind, a patch cap. V6 never writes them (its tree is rebuilt with nothing pending).
  "\\newcommand{\\vsProposed}[1]{\\vsBlock{vsBlue}{}{Proposed revision (awaiting your decision):}{#1}}",
  "\\newcommand{\\vsProposedProof}[1]{\\vsBlock{vsBlue}{}{Proof of the proposed statement:}{#1}}",
  "\\newcommand{\\vsProposedStep}[1]{\\vsBlock{vsBlue}{}{Revised (for the proposed statement):}{#1}}",
  "\\newcommand{\\vsRewind}[1]{\\vsBlock{vsNote}{\\normalfont\\small}{Proposed correction (awaiting your decision):}{#1}}",
  "\\newcommand{\\vsCap}[1]{\\vsBlock{vsNote}{\\normalfont\\small}{Revision not settled (awaiting your decision):}{#1}}",
  // A hypothesis no result uses after the repairs, crossed out where the paper prints it: red with a
  // line through it (ulem's `\sout`: inline text and math, across line breaks), and red alone for what
  // a line cannot cross (a display, a list, a paragraph break). Unit by unit, never a block.
  "\\makeatletter\\@ifpackageloaded{ulem}{}{\\usepackage[normalem]{ulem}}\\makeatother",
  "\\newcommand{\\vsStruck}[1]{{\\color{vsRed}\\sout{#1}}}",
  "\\newcommand{\\vsStruckRed}[1]{{\\color{vsRed}#1}}",
  // A note may quote the paper's own references (`Example~\ref{…}`, `\cite[…]{…}`, `\citet{…}`,
  // `\eqref{…}`, `\cref{…}`): the ones a paper's packages do not define fall back to
  // the kernel's `\ref` / `\cite`, at `\begin{document}`, after every package.
  "\\AtBeginDocument{\\providecommand{\\eqref}[1]{(\\ref{#1})}\\providecommand{\\cref}{\\ref}\\providecommand{\\Cref}{\\ref}\\providecommand{\\autoref}{\\ref}\\providecommand{\\citet}{\\cite}\\providecommand{\\citep}{\\cite}\\providecommand{\\citeauthor}{\\cite}\\providecommand{\\citeyear}{\\cite}}",
  // Notes may use amssymb's `\mathbb` / `\mathfrak` / `\lesssim` / `\gtrsim`; a paper without amssymb
  // gets a plain fallback, at `\begin{document}`, after every package.
  "\\AtBeginDocument{\\providecommand{\\mathbb}{\\mathbf}\\providecommand{\\mathfrak}{\\mathrm}\\providecommand{\\lesssim}{\\mathrel{\\vcenter{\\offinterlineskip\\hbox{$<$}\\hbox{$\\sim$}}}}\\providecommand{\\gtrsim}{\\mathrel{\\vcenter{\\offinterlineskip\\hbox{$>$}\\hbox{$\\sim$}}}}}",
  "% end of PaperFormalizer annotation macros",
].join("\n");

/** The macro for a blue part: a corrected statement or step, a clarification, a repair awaiting the
 * owner's decision. */
export type BlueMacro = "vsCorrected" | "vsClarified" | "vsProposed" | "vsCorrectedStep" | "vsProposedStep";

/** The macro crossing out printed text (`\vsStruck`), or colouring it red where a line cannot cross it
 * (`\vsStruckRed`: display math, an environment, a paragraph break, a footnote, verbatim, a command
 * with an optional argument such as `\citet[p.~3]{k}`, which a strike line cannot take). Pure. */
export function struckMacro(tex: string): "vsStruck" | "vsStruckRed" {
  return /\\\[|\$\$|\\begin\b|\\par\b|\n[ \t]*\n|\\footnote\b|\\footnotemark\b|\\verb\b|\\item\b|\\[A-Za-z]+\*?\s*\[/u.test(tex) ? "vsStruckRed" : "vsStruck";
}

/** The macro for a note part: the run's note, or a decision awaiting the owner. */
export type NoteMacro = "vsNote" | "vsRewind" | "vsCap" | "vsDetail";

/** Packages (and classes) that load xcolor themselves. */
const XCOLOR_LOADERS = /\\(?:usepackage|RequirePackage)\s*(?:\[[^\]]*\])?\s*\{[^}]*\b(?:xcolor|tikz|pgf|pgfplots|colortbl|beamerarticle)\b[^}]*\}/;
const XCOLOR_CLASSES = new Set(["beamer"]);

const DOCUMENT_CLASS = /\\documentclass\s*(?:\[[^\]]*\])?\s*\{([^}]*)\}/;
const BEGIN_DOCUMENT = /\\begin\s*\{document\}/;

/** The preamble: everything before `\begin{document}` (the whole text when there is none). A
 * commented-out landmark is none: here and below, each is searched for with the comments blanked. */
export function preambleOf(tex: string): string {
  const m = BEGIN_DOCUMENT.exec(blankTexComments(tex));
  return m ? tex.slice(0, m.index) : tex;
}

/** The class a main file loads, or null. */
export function documentClassOf(tex: string): string | null {
  const m = DOCUMENT_CLASS.exec(blankTexComments(tex));
  return m ? m[1]!.trim() : null;
}

const COLOR_DRIVERS = new Set(["dvips", "dvipdf", "dvipdfm", "dvipdfmx", "dvipsone", "dviwin", "dvisvgm", "xdvi", "pdftex", "luatex", "xetex", "textures", "vtex", "oztex"]);

/** The driver options the preamble passes to `color` (alone or in a package list with it). Pure. */
export function colorDriverOptions(preamble: string): string[] {
  const out = new Set<string>();
  for (const m of blankTexComments(preamble).matchAll(/\\(?:usepackage|RequirePackage)\s*\[([^\]]*)\]\s*\{([^}]*)\}/g)) {
    if (!m[2]!.split(",").some((p) => p.trim() === "color")) continue;
    for (const o of m[1]!.split(",")) if (COLOR_DRIVERS.has(o.trim())) out.add(o.trim());
  }
  return [...out];
}

/** Does this preamble (or a class file's text) load xcolor already? */
export function loadsXcolor(preamble: string, classText: string | null = null, className: string | null = null): boolean {
  if (className && XCOLOR_CLASSES.has(className)) return true;
  return XCOLOR_LOADERS.test(blankTexComments(preamble)) || (classText !== null && XCOLOR_LOADERS.test(blankTexComments(classText)));
}

/**
 * Add `\usepackage{xcolor}` after `\documentclass` unless xcolor is loaded already, and the macro
 * block immediately before `\begin{document}` (after every package the paper loads, so a later
 * `\usepackage[...]{xcolor}` of the paper is never clashed with). Idempotent.
 */
export function injectPreamble(tex: string, xcolorLoaded: boolean): { tex: string; addedXcolor: boolean; addedBlock: boolean } {
  let out = tex;
  let addedXcolor = false;
  let addedBlock = false;
  /** Where the class line ends (0: no `\documentclass`). */
  const afterClass = (): number => {
    const dc = DOCUMENT_CLASS.exec(blankTexComments(out));
    return dc ? dc.index + dc[0].length : 0;
  };
  if (!xcolorLoaded && !out.includes(VS_XCOLOR_LINE)) {
    const at = afterClass();
    // A paper loading `color` with a driver option (a dvips paper) asks for it again after our xcolor:
    // the driver is handed on first, so the two loads agree and LaTeX reports no option clash.
    const drivers = colorDriverOptions(preambleOf(out));
    const pass = drivers.length > 0 ? `\\PassOptionsToPackage{${drivers.join(",")}}{color}% added by PaperFormalizer\n` : "";
    out = `${out.slice(0, at)}\n${pass}${VS_XCOLOR_LINE}\n${out.slice(at)}`;
    addedXcolor = true;
  }
  if (!out.includes(VS_BLOCK_MARKER)) {
    const bd = BEGIN_DOCUMENT.exec(blankTexComments(out));
    if (bd) {
      out = `${out.slice(0, bd.index)}${VS_PREAMBLE_BLOCK}\n${out.slice(bd.index)}`;
    } else {
      let at = afterClass();
      // after our xcolor line (and the driver line that may precede it)
      const x = out.indexOf(VS_XCOLOR_LINE, at);
      if (x >= 0 && !out.slice(at, x).replace(/\\PassOptionsToPackage\{[^}]*\}\{color\}% added by PaperFormalizer/, "").trim()) at = x + VS_XCOLOR_LINE.length;
      out = `${out.slice(0, at)}\n${VS_PREAMBLE_BLOCK}\n${out.slice(at)}`;
    }
    addedBlock = true;
  }
  return { tex: out, addedXcolor, addedBlock };
}

// ---------------------------------------------------------------------------
// flat text → original bytes
// ---------------------------------------------------------------------------

/** Offset of the first character of every line (index 0 = line 1). */
export function lineStarts(text: string): number[] {
  const out = [0];
  for (let i = 0; i < text.length; i += 1) if (text[i] === "\n") out.push(i + 1);
  return out;
}

const isWs = (c: string | undefined): boolean => c === " " || c === "\t" || c === "\n" || c === "\r";

/** From `i` at an unescaped `%`: the index of the line break ending the comment (or the end). */
function skipComment(orig: string, i: number): number {
  while (i < orig.length && orig[i] !== "\n") i += 1;
  return i;
}

function alignFrom(orig: string, k: number, limit: number, needle: string): number[] | null {
  const map = new Array<number>(needle.length + 1);
  let i = k;
  let j = 0;
  while (j < needle.length) {
    if (i >= limit) return null;
    const oc = orig[i]!;
    const fc = needle[j]!;
    if (oc === "\\" && fc === "\\") {
      if (orig[i + 1] !== needle[j + 1]) return null;
      map[j] = i;
      if (j + 1 < needle.length) map[j + 1] = i + 1;
      i += 2;
      j += 2;
      continue;
    }
    if (oc === "%") {
      // A comment the flattener removed. Glued to text, TeX joins the next line on.
      i = skipComment(orig, i);
      if (!isWs(fc)) {
        i += 1;
        while (i < limit && (orig[i] === " " || orig[i] === "\t")) i += 1;
      }
      continue;
    }
    if (isWs(fc)) {
      while (j < needle.length && isWs(needle[j])) map[j++] = i;
      for (;;) {
        while (i < limit && isWs(orig[i])) i += 1;
        if (orig[i] === "%") {
          i = skipComment(orig, i);
          continue;
        }
        break;
      }
      continue;
    }
    if (isWs(oc)) {
      i += 1;
      continue;
    }
    if (oc !== fc) {
      // An empty group one of the two texts has alone (a line the note-macro reading emptied) prints nothing.
      if (fc === "{" && needle[j + 1] === "}") {
        map[j] = i;
        map[j + 1] = i;
        j += 2;
        continue;
      }
      if (oc === "{" && orig[i + 1] === "}") {
        i += 2;
        continue;
      }
      return null;
    }
    map[j] = i;
    i += 1;
    j += 1;
  }
  // End: just past the last matched character.
  let last = needle.length - 1;
  while (last >= 0 && isWs(needle[last])) last -= 1;
  map[needle.length] = last >= 0 ? map[last]! + 1 : k;
  return map;
}

/**
 * Map every index of `needle` (comment-stripped TeX copied out of the source) to an index of
 * `orig` inside `[from, to)`: the first start position from which the needle aligns, with
 * comments skipped and whitespace runs matched loosely. `map[needle.length]` is the offset just
 * past the last non-space character. Null when the needle does not align (the flattener also
 * blanks verbatim / `\iffalse` material, which this does not replay).
 */
export function alignToOriginal(orig: string, from: number, to: number, needle: string): number[] | null {
  const lead = needle.search(/\S/);
  if (lead < 0) return null;
  const first = needle[lead]!;
  for (let k = from; k < to; k += 1) {
    if (orig[k] !== first) continue;
    const map = alignFrom(orig, k, to, needle.slice(lead));
    if (!map) continue;
    // Re-index to the untrimmed needle.
    const full = new Array<number>(needle.length + 1);
    for (let j = 0; j < lead; j += 1) full[j] = k;
    for (let j = 0; j <= needle.length - lead; j += 1) full[j + lead] = map[j]!;
    return full;
  }
  return null;
}

// ---------------------------------------------------------------------------
// regions a span may not split
// ---------------------------------------------------------------------------

export interface Region {
  start: number;
  end: number;
  kind: "math" | "display" | "environment" | "group";
}

/** Math (`$…$`, `$$…$$`, `\(…\)`, `\[…\]`), `\begin{X}…\end{X}` and brace groups of a TeX text. */
export function texRegions(text: string): Region[] {
  const out: Region[] = [];
  const braces: number[] = [];
  const envs: Array<{ name: string; start: number }> = [];
  let math: { close: string; start: number; kind: Region["kind"] } | null = null;
  for (let i = 0; i < text.length; i += 1) {
    const c = text[i]!;
    if (c === "\\") {
      const n = text[i + 1];
      if (n === "(" || n === "[") {
        if (!math) math = { close: n === "(" ? "\\)" : "\\]", start: i, kind: n === "(" ? "math" : "display" };
        i += 1;
        continue;
      }
      if ((n === ")" || n === "]") && math && math.close === `\\${n}`) {
        out.push({ start: math.start, end: i + 2, kind: math.kind });
        math = null;
        i += 1;
        continue;
      }
      const be = /^\\(begin|end)\s*\{([^{}]*)\}/.exec(text.slice(i, i + 80));
      if (be && !math) {
        if (be[1] === "begin") envs.push({ name: be[2]!, start: i });
        else {
          for (let k = envs.length - 1; k >= 0; k -= 1) {
            if (envs[k]!.name === be[2]) {
              out.push({ start: envs[k]!.start, end: i + be[0].length, kind: "environment" });
              envs.length = k;
              break;
            }
          }
        }
        i += be[0].length - 1;
        continue;
      }
      i += 1; // an escaped character (`\$`, `\{`, `\%`, …) or a control word's first letter
      continue;
    }
    if (c === "$") {
      const dbl = text[i + 1] === "$";
      if (!math) math = { close: dbl ? "$$" : "$", start: i, kind: dbl ? "display" : "math" };
      else if (math.close === (dbl ? "$$" : "$")) {
        out.push({ start: math.start, end: i + (dbl ? 2 : 1), kind: math.kind });
        math = null;
      }
      if (dbl) i += 1;
      continue;
    }
    if (c === "{") braces.push(i);
    else if (c === "}" && braces.length > 0) out.push({ start: braces.pop()!, end: i + 1, kind: "group" });
  }
  return out;
}

/** Widen `[start, end)` until neither end lies strictly inside a region. Returns the kinds widened over. */
export function extendToRegions(regions: readonly Region[], start: number, end: number): { start: number; end: number; extended: string[] } {
  const extended = new Set<string>();
  let s = start;
  let e = end;
  for (let changed = true; changed; ) {
    changed = false;
    for (const r of regions) {
      if (r.start < s && s < r.end) {
        s = r.start;
        extended.add(r.kind);
        changed = true;
      }
      if (r.start < e && e < r.end) {
        e = r.end;
        extended.add(r.kind);
        changed = true;
      }
    }
  }
  return { start: s, end: e, extended: [...extended].sort() };
}

// ---------------------------------------------------------------------------
// where an annotation block may be inserted into the ORIGINAL source
// ---------------------------------------------------------------------------

/** Environments whose body is math: an annotation block (a paragraph, `\small`) never goes inside. */
export const MATH_ENV = /^(?:equation|align|alignat|flalign|xalignat|gather|multline|eqnarray|displaymath|math|dmath|dseries|dgroup|IEEEeqnarray|IEEEeqnarraybox)\*?$/;
/** Environments whose body TeX does not read as TeX: nothing is inserted there either. */
const VERBATIM_ENV = /\\begin\s*\{(verbatim\*?|Verbatim\*?|lstlisting|minted|comment)\}/g;

/** A region of the original source an insertion may not fall strictly inside. */
export interface UnsafeRegion {
  start: number;
  end: number;
  kind: "math" | "display" | "math environment" | "group" | "comment" | "verbatim";
}

/**
 * The regions of an ORIGINAL TeX source (comments and all) an annotation block may never be
 * inserted strictly inside: math (`$…$`, `$$…$$`, `\(…\)`, `\[…\]`, `equation` / `align` / `gather` / …
 * and their starred forms), brace groups (so also every `\label{…}` / `\ref{…}` / `\cite{…}`
 * argument), comments (to the end of their line, the line break included) and verbatim material.
 * Comments and verbatim are blanked before the math / group scan, so a `$` or a brace in them never
 * pairs; a math region that spans a blank line is a mis-pairing (TeX forbids a paragraph break in
 * math) and is dropped.
 */
export function unsafeRegions(text: string): UnsafeRegion[] {
  const out: UnsafeRegion[] = [];
  const masked = text.split("");
  const blank = (a: number, b: number): void => {
    for (let k = a; k < b; k += 1) if (masked[k] !== "\n") masked[k] = " ";
  };
  for (const m of text.matchAll(VERBATIM_ENV)) {
    const name = m[1]!.replace(/[*]/g, "\\*");
    const close = new RegExp(`\\\\end\\s*\\{${name}\\}`).exec(text.slice(m.index + m[0].length));
    const end = close ? m.index + m[0].length + close.index + close[0].length : text.length;
    if (out.some((r) => r.start <= m.index && m.index < r.end)) continue;
    out.push({ start: m.index, end, kind: "verbatim" });
  }
  const verbatim = [...out].sort((a, b) => a.start - b.start);
  let v = 0;
  for (let i = 0; i < text.length; i += 1) {
    while (v < verbatim.length && verbatim[v]!.end <= i) v += 1;
    if (v < verbatim.length && verbatim[v]!.start <= i) {
      i = verbatim[v]!.end - 1;
      continue;
    }
    const c = text[i]!;
    if (c === "\\") {
      const verb = /^\\verb\*?([^A-Za-z\s*])/.exec(text.slice(i, i + 7));
      if (verb) {
        const close = text.indexOf(verb[1]!, i + verb[0].length);
        const end = close < 0 ? i + verb[0].length : close + 1;
        out.push({ start: i, end, kind: "verbatim" });
        i = end - 1;
        continue;
      }
      i += 1;
      continue;
    }
    if (c === "%") {
      const nl = text.indexOf("\n", i);
      const end = nl < 0 ? text.length : nl + 1;
      out.push({ start: i, end, kind: "comment" });
      i = end - 1;
    }
  }
  for (const r of out) blank(r.start, r.end);
  const flat = masked.join("");
  for (const r of texRegions(flat)) {
    if (r.kind === "environment") {
      const name = /^\\begin\s*\{([^{}]*)\}/.exec(flat.slice(r.start, r.start + 80))?.[1] ?? "";
      // a math environment holds no paragraph break: one that does is a mispairing (a macro that
      // opens it, `\\def\\be{\\begin{align}}`, closed far below), not a region
      if (MATH_ENV.test(name.trim()) && !/\n[ \t]*\n/.test(flat.slice(r.start, r.end))) out.push({ start: r.start, end: r.end, kind: "math environment" });
      continue;
    }
    if ((r.kind === "math" || r.kind === "display") && /\n[ \t]*\n/.test(flat.slice(r.start, r.end))) continue;
    out.push({ start: r.start, end: r.end, kind: r.kind });
  }
  return out;
}

/** Past the brace groups that follow `at` immediately (a command's further arguments: `\frac{a}{b}`). */
function pastSiblingGroups(text: string, at: number, regions: readonly UnsafeRegion[]): number {
  let p = at;
  for (let r = regions.find((x) => x.kind === "group" && x.start === p); r && text[p] === "{"; r = regions.find((x) => x.kind === "group" && x.start === p)) p = r.end;
  return p;
}

/** Back over the brace groups that end at `at` and the control word before them (`\emph{`, `\frac{a}{`). */
function toCommandStart(text: string, at: number, regions: readonly UnsafeRegion[]): number {
  let p = at;
  for (let r = regions.find((x) => x.kind === "group" && x.end === p); r && text[p - 1] === "}"; r = regions.find((x) => x.kind === "group" && x.end === p)) p = r.start;
  const cs = /\\[A-Za-z@]+\*?$/.exec(text.slice(Math.max(0, p - 40), p));
  return cs ? p - cs[0].length : p;
}

const PARAGRAPH_BREAK = /\n[ \t]*\n/;

/**
 * Whether `p` lies strictly inside the one environment a plain brace group holds, blanks aside
 * (`{\begin{algorithm}…\end{algorithm}}`): a group that is no command's argument (no control word,
 * `}`, `]` or parameter `#n` before its brace in the same paragraph, comments aside). Such a group only
 * scopes the environment: inside it the environment's body is what it is without the group (a float
 * stays a float).
 */
function inGroupedEnv(text: string, g: UnsafeRegion, p: number): boolean {
  // what stands before the brace, comments dropped and blanks skipped (a paragraph break ends the look)
  // (a line that is only a comment is no line: it breaks no paragraph)
  const before = text.slice(Math.max(0, g.start - 400), g.start).split("\n").filter((l) => !/^[ \t]*%/.test(l)).map((l) => l.replace(/(^|[^\\])%.*$/, "$1")).join("\n");
  const blanks = /\s*$/.exec(before)![0];
  if (!PARAGRAPH_BREAK.test(blanks) && /(?:\\[A-Za-z@]+\*?|[}\]]|#\d)$/.test(before.slice(0, before.length - blanks.length))) return false;
  const body = text.slice(g.start + 1, g.end - 1);
  const open = /^\s*\\begin\s*\{([^{}]+)\}/.exec(body);
  if (!open) return false;
  const name = open[1]!.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const close = new RegExp(`\\\\end\\s*\\{${name}\\}\\s*$`).exec(body);
  if (!close) return false;
  let depth = 0;
  for (const m of body.matchAll(new RegExp(`\\\\(begin|end)\\s*\\{${name}\\}`, "g"))) {
    depth += m[1] === "begin" ? 1 : -1;
    if (depth === 0 && m.index !== close.index) return false;
  }
  // (inside: after the opening tag and its optional argument, `\begin{algorithm}[t]`)
  const start = g.start + 1 + open[0].length + (/^\s*\[[^\]]*\]/.exec(body.slice(open[0].length))?.[0].length ?? 0);
  return start <= p && p < g.start + 1 + close.index + close[0].trimEnd().length;
}

/**
 * The first position at or after `pos` where an annotation block may be inserted: outside every
 * unsafe region of `text` (`unsafeRegions`) — a position strictly inside one moves to its end (for a
 * brace group, also past the groups right after it: the command's further arguments), until none
 * holds it. A region holds a position back only within ONE paragraph: when a paragraph break lies
 * between the position and the region's end, the region scopes a passage (`{\color{black} … }` around
 * an appendix) and the text at the position is running text, where a block may stand — an insertion
 * is never carried past a paragraph break (a comment or verbatim region excepted: nothing may be
 * written inside one). Nor does a plain group around one environment hold back a position inside that
 * environment (`inGroupedEnv`). `moved` names the regions moved out of (empty: `pos` was safe).
 */
export function safeInsertionPoint(text: string, pos: number, regions: readonly UnsafeRegion[] = unsafeRegions(text)): { pos: number; moved: string[] } {
  const moved = new Set<string>();
  let p = pos;
  for (let changed = true; changed; ) {
    changed = false;
    for (const r of regions) {
      if (r.start < p && p < r.end && (r.kind === "comment" || r.kind === "verbatim" || !PARAGRAPH_BREAK.test(text.slice(p, r.end))) && !(r.kind === "group" && inGroupedEnv(text, r, p))) {
        p = r.kind === "group" ? pastSiblingGroups(text, r.end, regions) : r.end;
        moved.add(r.kind);
        changed = true;
      }
    }
  }
  return { pos: p, moved: [...moved].sort() };
}

/**
 * Widen a span `[start, end)` of the ORIGINAL source that is wrapped (`\vsOriginal{…}`,
 * `\vsStep{…}`) until the wrap is well formed: neither end strictly inside math, a comment or
 * verbatim, and no brace group holding exactly one of its two braces in the span (widened over the
 * whole command: its control word and argument groups). A group holding the whole span is left
 * alone (the wrap then sits inside it, balanced).
 */
export function safeSpan(text: string, start: number, end: number, regions: readonly UnsafeRegion[] = unsafeRegions(text)): { start: number; end: number; extended: string[] } {
  const extended = new Set<string>();
  // A bound that is no position (NaN, undefined) never settles the loop below (NaN !== NaN).
  if (!Number.isFinite(start) || !Number.isFinite(end)) return { start, end, extended: [] };
  let s = start;
  let e = end;
  for (let changed = true; changed; ) {
    changed = false;
    for (const r of regions) {
      let ns = s;
      let ne = e;
      if (r.kind === "group") {
        const openIn = s <= r.start && r.start < e;
        const closeIn = s <= r.end - 1 && r.end - 1 < e;
        if (openIn === closeIn) continue;
        // the whole command: its control word and every argument group
        ns = Math.min(s, toCommandStart(text, r.start, regions));
        ne = Math.max(e, pastSiblingGroups(text, r.end, regions));
      } else {
        if (r.start < s && s < r.end) ns = r.start;
        if (r.start < e && e < r.end) ne = r.end;
      }
      if (ns !== s || ne !== e) {
        s = ns;
        e = ne;
        extended.add(r.kind);
        changed = true;
      }
    }
  }
  return { start: s, end: e, extended: [...extended].sort() };
}

/** The offset past the group opening at `i` of `tex` — an optional argument `[…]` (brackets nest in it
 * outside braces and math, so `[Of $[0,1]$]` is one) or a `{…}` group — or -1 when it does not close.
 * An escaped character is no delimiter. */
function argumentEnd(tex: string, i: number): number {
  const bracket = tex[i] === "[";
  let brackets = 0;
  let braces = 0;
  let math = false;
  for (let k = i; k < tex.length; k += 1) {
    const c = tex[k]!;
    if (c === "\\") k += 1;
    else if (c === "$") math = !math;
    else if (c === "{") braces += 1;
    else if (c === "}" && --braces < 0) return -1;
    else if (bracket && braces === 0 && !math && c === "[") brackets += 1;
    else if (bracket && braces === 0 && !math && c === "]") brackets -= 1;
    if (bracket ? brackets === 0 && braces === 0 && !math : braces === 0) return k + 1;
  }
  return -1;
}

/**
 * A text cut at its environment markers: each `\begin{X}` (with its arguments: an optional `[…]`, after
 * spacing that holds no blank line, and the `{…}` groups right after it) and `\end{X}`
 * met at the text's top level — outside every brace group, math span and environment not cut itself —
 * that `cut(X, matched)` takes (`matched`: the text holds both ends of that environment). `markers`
 * (with `key` the tag and environment, for pairing two texts) and the `segments` between them, one more
 * than the markers. A segment holds no top-level marker cut, so it can be wrapped in a block macro once
 * no environment it holds is left open. Pure.
 */
export function envCuts(tex: string, cut: (env: string, matched: boolean) => boolean): { markers: Array<{ start: number; end: number; key: string }>; segments: Array<{ start: number; end: number }> } {
  const tags = envTags(tex);
  const cuts = (i: number): boolean => cut(tags[i]!.env, tags[i]!.matched);
  const markers = tags.flatMap((t, i) => {
    if (!cuts(i) || !t.outer.every((o) => typeof o === "number" && cuts(o))) return [];
    let end = t.end;
    while (t.begin) {
      const gap = /^[ \t]*(?:\n[ \t]*)?/.exec(tex.slice(end))![0].length;
      const at = tex[end + gap] === "[" ? argumentEnd(tex, end + gap) : tex[end] === "{" ? argumentEnd(tex, end) : -1;
      if (at < 0) break;
      end = at;
    }
    return [{ start: t.start, end, key: `${t.begin ? "begin" : "end"}{${t.env}}` }];
  });
  const segments = [...markers, { start: tex.length, end: tex.length, key: "" }].map((m, k) => ({ start: k === 0 ? 0 : markers[k - 1]!.end, end: m.start }));
  return { markers, segments };
}

const LABEL_AT_START = /^(?:\s|\{\}|\\label\s*\{[^{}]*\})+/;
const LABEL_AT_END = /(?:\s|\\label\s*\{[^{}]*\})+$/;

/** Shrink a span past surrounding whitespace, a leading empty group `{}` and `\label{…}`s, so a
 * label is never wrapped or moved. Null when nothing is left. */
export function trimSpan(text: string, start: number, end: number): { start: number; end: number } | null {
  const piece = text.slice(start, end);
  const lead = LABEL_AT_START.exec(piece)?.[0].length ?? 0;
  const rest = piece.slice(lead);
  const trail = LABEL_AT_END.exec(rest)?.[0].length ?? 0;
  const s = start + lead;
  const e = end - trail;
  return e > s ? { start: s, end: e } : null;
}

/**
 * A model's text as the annotated paper prints it, by how it is set: a statement or hypothesis laid
 * out (`layoutBlue`), a note as written, the displays of either fitted (`fitDisplays`); a proof step as
 * written. The fragment check compiles exactly this (`tex_fragment_check.ts`), so a text that passed
 * prints as it compiled. Pure.
 */
export function printedFragment(text: string, kind: "statement" | "hypothesis" | "step" | "note"): string {
  switch (kind) {
    case "statement":
    case "hypothesis":
      return fitDisplays(layoutBlue(text));
    case "note":
      return fitDisplays(text);
    case "step":
      return text;
  }
}

/** TeX for the blue text: without V1's `[Hypotheses: …]` list and a leading empty group; a `\label{…}`
 * becomes `\vsLabel{…}` (the annotated paper sets the label on the paper's own text, the corrected
 * paper on the correction's, in place — so a display keeps its label, and no line is emptied). */
export function blueTex(tex: string): string {
  return tex
    .replace(/\s*\[Hypotheses:[^\]]*\]\s*$/u, "")
    .replace(/\\label\s*\{([^{}]*)\}/g, "\\vsLabel{$1}")
    .replace(/^\s*\{\}\s*/, "")
    .trim();
}

/** Each `$$…$$` / `\[…\]` display of a text we write fitted to the line (`\vsFit`: TeX cannot break a
 * display), found by the TeX parser (`texRegions`); a display numbered by `\eqno` / `\leqno` is left as
 * it is (its number cannot be boxed). Pure. */
export function fitDisplays(tex: string): string {
  // A display touching a comment is left as printed (the parser does not read comments).
  const comments = [...tex.matchAll(/(?<!\\)%.*$/gmu)].map((m) => ({ start: m.index!, end: m.index! + m[0].length }));
  const displays = texRegions(tex)
    .filter((r) => r.kind === "display" && !comments.some((c) => c.start < r.end && r.start < c.end))
    .sort((a, b) => b.start - a.start);
  let out = tex;
  for (const r of displays) {
    const open = out.startsWith("$$", r.start) ? 2 : out.startsWith("\\[", r.start) ? 2 : 0;
    if (open === 0) continue;
    const body = out.slice(r.start + open, r.end - 2);
    if (/\\l?eqno(?![A-Za-z])/u.test(body)) continue;
    out = `${out.slice(0, r.start)}\\vsFit{${body.trim()}}${out.slice(r.end)}`;
  }
  return out;
}


// ---------------------------------------------------------------------------
// notes: model text is TeX, checked at its source — nothing here repairs it
// ---------------------------------------------------------------------------

const hexOf = (c: string): string => `U+${c.codePointAt(0)!.toString(16).toUpperCase().padStart(4, "0")}`;

/** The characters a model-written TeX fragment may carry: printable ASCII, newline and tab (the JSON
 * schemas' `pattern`, `owner_text.ts` `ASCII_TEX_PATTERN`). */
const ASCII_TEX_CHAR = /[\x20-\x7E\n\t]/u;

/**
 * The detector that replaced the Unicode→TeX converter (design 2026-09-25): the characters of a
 * model-written fragment outside printable ASCII, named (at most four), or null. The fragment is the
 * model's to fix — the producers reject it (`tex_fragment_check.ts`), the renderer prints it verbatim
 * and reports it at the render checkpoint; nothing maps it. Pure.
 */
export function nonAsciiProblem(text: string): string | null {
  const bad = [...new Set([...text].filter((c) => !ASCII_TEX_CHAR.test(c)))];
  if (bad.length === 0) return null;
  const shown = bad.slice(0, 4).map((c) => (/[\p{L}\p{N}\p{P}\p{S}]/u.test(c) ? `${hexOf(c)} (${c})` : hexOf(c)));
  // A control character is a TeX backslash the JSON decoding ate (one backslash before a letter the
  // decoder reads as an escape); a DEL (U+007F) stands where the model wrote "\u007f" for a backslash.
  const eaten = bad.some((c) => c.charCodeAt(0) < 0x20)
    ? ` — a control character is a TeX backslash the JSON ate: write every TeX backslash as "\\\\" in the JSON`
    : bad.some((c) => c.charCodeAt(0) === 0x7f)
      ? ` — U+007F stands where a TeX backslash belongs: write "\\\\" in the JSON, never "\\u007f"`
      : "";
  const quotes = bad.some((c) => /[\u2018\u2019\u201C\u201D]/u.test(c)) ? " — quotation marks are TeX quotes, ``like this''" : "";
  return `a non-ASCII character ${shown.join(", ")}${bad.length > 4 ? `, +${bad.length - 4} more` : ""}${eaten}${quotes} — the text is plain ASCII; every symbol is a TeX command`;
}

/**
 * A fragment's braces unbalanced (unescaped `{` / `}`, a `\\` pair skipped), named, or null: a stray
 * `}` would close the block macro's argument early and a later `{` rebalance it — a fragment that
 * compiles and prints the wrong text — so it is flagged before any compile. Pure.
 */
export function braceProblem(text: string): string | null {
  let depth = 0;
  for (let i = 0; i < text.length; i += 1) {
    const c = text[i]!;
    if (c === "\\") i += 1;
    else if (c === "{") depth += 1;
    else if (c === "}" && --depth < 0) return "a } that closes no { — braces that print are \\{ … \\}";
  }
  return depth > 0 ? "an unclosed { — braces that print are \\{ … \\}" : null;
}

/** A plain text with every TeX special escaped; a character outside printable ASCII printed as its
 * code point (`[U+XXXX]`, which the render check flags). */
function escapeText(s: string): string {
  let out = "";
  for (const ch of s) {
    if (ch === "\\") out += "\\textbackslash{}";
    else if ("{}$&%#_".includes(ch)) out += `\\${ch}`;
    else if (ch === "^") out += "\\^{}";
    else if (ch === "~") out += "\\~{}";
    else if (!ASCII_TEX_CHAR.test(ch)) out += /\s/u.test(ch) ? " " : `[${hexOf(ch)}]`;
    else out += ch;
  }
  return out;
}

/** A fragment printed verbatim-like — every TeX special escaped, typewriter: how the renderer shows
 * a model-written fragment that fails the check (a render-checkpoint defect, never a repair). */
export function verbatimLike(text: string): string {
  return `\\texttt{${escapeText(text.replace(/\s+/g, " ").trim())}}`;
}

/** The first `n` sentences of a plain text. */
export function firstSentences(text: string, n: number): string {
  const t = text.replace(/\s+/g, " ").trim();
  const sp = sentenceSpans(t);
  if (sp.length <= n) return t;
  return t.slice(0, sp[n - 1]!.end).trim();
}

/** A witness in at most two sentences: whole when short, else its first and last sentence. */
export function summarizeWitness(text: string): string {
  const t = text.replace(/\s+/g, " ").trim();
  const sp = sentenceSpans(t);
  if (sp.length <= 2) return t;
  return `${t.slice(sp[0]!.start, sp[0]!.end).trim()} \\dots{} ${t.slice(sp[sp.length - 1]!.start, sp[sp.length - 1]!.end).trim()}`;
}

// ---------------------------------------------------------------------------
// layout for reading (user rule 2026-09-25)
// ---------------------------------------------------------------------------

/** Offsets of `tex` inside math, a display or an environment (`texRegions`). */
function inertAt(tex: string): (i: number) => boolean {
  const regions = texRegions(tex).filter((r) => r.kind !== "group");
  return (i) => regions.some((r) => r.start < i && i < r.end);
}

/** A clause marker's family: `(1)`, `(i)`, `(a)`. */
function markerFamily(m: string): "num" | "roman" | "alpha" | null {
  if (/^\(\d{1,2}\)$/u.test(m)) return "num";
  if (/^\((?:i|ii|iii|iv|v|vi|vii|viii|ix|x)\)$/u.test(m)) return "roman";
  if (/^\([a-h]\)$/u.test(m)) return "alpha";
  return null;
}
const FIRST_OF: Record<string, string> = { num: "(1)", roman: "(i)", alpha: "(a)" };

/**
 * Numbered clauses one per line: every clause marker `(1)` / `(i)` / `(a)` outside math that opens
 * the text or follows a sentence or clause end (`.` `;` `:` `,`, a line break, "then", "and", "or")
 * becomes `\vsItem{(k)}`
 * (a hanging-indent line), when the text lists at least two of one family starting at its first
 * marker. Display math and paragraph breaks are left as they are. Pure.
 */
export function layoutClauses(tex: string): string {
  const inert = inertAt(tex);
  const re = /(^|[.;:,]\s+|\n\s*|\b(?:[Tt]hen|and|or)\s+)(\((?:\d{1,2}|[ivx]{1,4}|[a-h])\))\s+/gu;
  const hits = [...tex.matchAll(re)].map((m) => ({ at: m.index! + m[1]!.length, end: m.index! + m[0].length, marker: m[2]!, fam: markerFamily(m[2]!) })).filter((h) => h.fam && !inert(h.at));
  const counts = new Map<string, number>();
  for (const h of hits) counts.set(h.fam!, (counts.get(h.fam!) ?? 0) + 1);
  const fam = [...counts.entries()].filter(([f, n]) => n >= 2 && hits.find((h) => h.fam === f)!.marker === FIRST_OF[f]).sort((a, b) => b[1] - a[1])[0]?.[0];
  if (!fam) return tex;
  let out = "";
  let last = 0;
  for (const h of hits.filter((x) => x.fam === fam)) {
    out += `${tex.slice(last, h.at)}\\vsItem{${h.marker}}`;
    last = h.end;
  }
  return out + tex.slice(last);
}

/** A blank line of a model's text kept as a paragraph break (`\vsPar`), outside math. Pure. */
export function layoutParagraphs(tex: string): string {
  const inert = inertAt(tex);
  return tex.replace(/[ \t]*\n[ \t]*\n\s*/gu, (m, at: number) => (inert(at) ? m : " \\vsPar "));
}

/** A corrected / proposed statement or added-hypothesis block laid out for reading. Pure. */
export function layoutBlue(tex: string): string {
  return layoutClauses(layoutParagraphs(tex));
}
