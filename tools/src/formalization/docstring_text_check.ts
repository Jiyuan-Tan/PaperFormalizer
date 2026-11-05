// F5 docstring gate, checked from the source text. A docstring pass may change docstrings only;
// whether it did is decided here by comparing a file with every docstring removed before and after
// the pass (character by character, columns included), and each docstring must stand in a slot
// Lean takes one in: on a declaration the index reports, or where the file had one. The one build
// that confirms the edits runs once, after the last pass, and compares the declarations' statement
// fingerprints with those taken before the pass (stage5_docstrings.ts, stage5.ts).
//
// The lexer reads comments as Lean's tokenizer does (`whitespace`, `finishCommentBlock` in
// Lean/Parser/Basic.lean): `/-` and `-/` nest, and the character after an opening `/-` is skipped
// (`/-/-` opens one level, not two); inside a comment nothing else counts (a `"-/"` there closes
// it); a `--` line comment hides the rest of its line; outside comments, string and character
// literals, raw strings and «…» names hide comment openers. Interpolated strings (`s!"…{e}…"`) are
// read as plain strings, so a docstring-like run inside one can be misread; a misread that lands in
// a slot is exotic, and the text check is not the last word on its own: the edit must still build,
// and F5 compares every statement's fingerprint after the build.

/** A run of the source: a docstring (`/-- … -/`), another comment (`--`, `/- … -/`, `/-! … -/`),
 *  or anything else (code, whitespace, literals). */
export interface LeanSegment {
  kind: "doc" | "comment" | "code";
  start: number;
  /** Exclusive. */
  end: number;
}

/** Where a block comment whose body starts at `from` (depth 1) closes: the index past its `-/`,
 *  or the end of the source when it never does (Lean: a parse error). */
function blockEnd(src: string, from: number): number {
  let depth = 1;
  let i = from;
  while (i < src.length) {
    if (src[i] === "-" && src[i + 1] === "/") {
      depth -= 1;
      i += 2;
      if (depth === 0) return i;
    } else if (src[i] === "/" && src[i + 1] === "-") {
      depth += 1;
      i += 2;
    } else {
      i += 1;
    }
  }
  return src.length;
}

/** A character that continues a Lean identifier (λ, Π and Σ are tokens, not letters). */
const IDENT_CHAR = /[\p{L}\p{N}_'!?₀-ₜᵢ-ᵪ]/u;
const isIdentChar = (ch: string | undefined): boolean => !!ch && IDENT_CHAR.test(ch) && !/[λΠΣ]/.test(ch);

/** Whether the character before `i` ends an identifier (so a `'` at `i` is a prime and an `r` a
 *  name): a run of identifier characters that does not start with a digit (`2'a'` is a number and
 *  a character literal). */
function endsIdentifier(src: string, i: number): boolean {
  let j = i;
  while (j > 0 && isIdentChar(src[j - 1])) j -= 1;
  return j < i && !/\p{N}/u.test(src[j]!);
}

const CHAR_LITERAL = /'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^\\'])'/y;

/** The source as docstrings, other comments and the rest, in order, covering every character. Pure. */
export function lexLeanSegments(src: string): LeanSegment[] {
  const out: LeanSegment[] = [];
  let codeStart = 0;
  const push = (kind: "doc" | "comment", start: number, end: number) => {
    if (start > codeStart) out.push({ kind: "code", start: codeStart, end: start });
    out.push({ kind, start, end });
    codeStart = end;
  };
  const n = src.length;
  let i = 0;
  while (i < n) {
    const c = src[i]!;
    if (c === "-" && src[i + 1] === "-") {
      const nl = src.indexOf("\n", i);
      const end = nl < 0 ? n : nl;
      push("comment", i, end);
      i = end;
    } else if (c === "/" && src[i + 1] === "-") {
      // `/--` a docstring, `/-!` a module doc, `/-x` a comment whose x Lean skips: every body
      // starts at i + 3
      const end = blockEnd(src, i + 3);
      push(src[i + 2] === "-" ? "doc" : "comment", i, end);
      i = end;
    } else if (c === '"') {
      i += 1;
      while (i < n && src[i] !== '"') i += src[i] === "\\" ? 2 : 1;
      i += 1;
    } else if (c === "r" && !endsIdentifier(src, i) && /^r#*"/.test(src.slice(i, i + 64))) {
      const hashes = /^r(#*)"/.exec(src.slice(i, i + 64))![1]!;
      const close = src.indexOf(`"${hashes}`, i + 2 + hashes.length);
      i = close < 0 ? n : close + 1 + hashes.length;
    } else if (c === "'" && !endsIdentifier(src, i)) {
      CHAR_LITERAL.lastIndex = i;
      const m = CHAR_LITERAL.exec(src);
      i += m ? m[0].length : 1;
    } else if (c === "«") {
      const close = src.indexOf("»", i + 1);
      i = close < 0 ? n : close + 1;
    } else {
      i += 1;
    }
  }
  if (n > codeStart) out.push({ kind: "code", start: codeStart, end: n });
  return out;
}

interface SourceDocstring {
  start: number;
  end: number;
  /** Between `/--` and `-/`, as Lean stores it. */
  body: string;
  closed: boolean;
}

/**
 * The source with its docstrings taken out, line by line: a docstring and the blanks right after
 * it go, trailing blanks of each line go, and lines left empty go. Per character of the residue:
 * `src` its source offset (-1 at a line break), `col` its column in the source (in code points, as
 * Lean counts), `afterDoc` whether it follows a docstring on the docstring's last line (there the
 * column moves with the docstring's length), `code` whether it is a non-blank character of code
 * (not of a comment).
 */
export interface DocstringResidue {
  text: string;
  /** The residue's characters (code points), `src`, `col`, … index these. */
  chars: string[];
  src: number[];
  col: number[];
  afterDoc: boolean[];
  code: boolean[];
  docs: SourceDocstring[];
  /** Residue indices of the code characters, ascending (their source offsets ascend too). */
  codeAt: number[];
}

/** Pure. */
export function docstringResidue(source: string): DocstringResidue {
  const docs: SourceDocstring[] = [];
  type Line = { chars: string[]; src: number[]; col: number[]; afterDoc: boolean[]; code: boolean[] };
  const fresh = (): Line => ({ chars: [], src: [], col: [], afterDoc: [], code: [] });
  const lines: Line[] = [fresh()];
  let skipBlanks = false;
  let afterDoc = false;
  let col = 0;
  for (const seg of lexLeanSegments(source)) {
    if (seg.kind === "doc") {
      const closed = seg.end - seg.start >= 5 && source.startsWith("-/", seg.end - 2);
      docs.push({ start: seg.start, end: seg.end, body: source.slice(seg.start + 3, closed ? seg.end - 2 : seg.end), closed });
      const text = source.slice(seg.start, seg.end);
      const nl = text.lastIndexOf("\n");
      col = nl < 0 ? col + [...text].length : [...text.slice(nl + 1)].length;
      skipBlanks = true;
      afterDoc = true;
      continue;
    }
    let i = seg.start;
    while (i < seg.end) {
      const ch = String.fromCodePoint(source.codePointAt(i)!);
      if (ch === "\n") {
        lines.push(fresh());
        col = 0;
        skipBlanks = false;
        afterDoc = false;
        i += 1;
        continue;
      }
      if (!(skipBlanks && (ch === " " || ch === "\t"))) {
        skipBlanks = false;
        const line = lines[lines.length - 1]!;
        line.chars.push(ch);
        line.src.push(i);
        line.col.push(col);
        line.afterDoc.push(afterDoc);
        line.code.push(seg.kind === "code" && !/\s/.test(ch));
      }
      col += 1;
      i += ch.length;
    }
  }
  const r: DocstringResidue = { text: "", chars: [], src: [], col: [], afterDoc: [], code: [], docs, codeAt: [] };
  const text = r.chars;
  for (const line of lines) {
    let k = line.chars.length;
    while (k > 0 && /[ \t\r]/.test(line.chars[k - 1]!)) k -= 1;
    if (k === 0) continue;
    if (text.length > 0) {
      text.push("\n");
      r.src.push(-1);
      r.col.push(-1);
      r.afterDoc.push(false);
      r.code.push(false);
    }
    for (let j = 0; j < k; j++) {
      text.push(line.chars[j]!);
      r.src.push(line.src[j]!);
      r.col.push(line.col[j]!);
      r.afterDoc.push(line.afterDoc[j]!);
      r.code.push(line.code[j]!);
    }
  }
  r.text = text.join("");
  for (let i = 0; i < r.code.length; i++) if (r.code[i]) r.codeAt.push(i);
  return r;
}

/** The residue index of the first code character at or after source offset `pos`, or -1. */
function codeAnchor(r: DocstringResidue, pos: number): number {
  let lo = 0;
  let hi = r.codeAt.length;
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    if (r.src[r.codeAt[mid]!]! < pos) lo = mid + 1;
    else hi = mid;
  }
  return lo < r.codeAt.length ? r.codeAt[lo]! : -1;
}

/** The source offset where 1-based line `line` starts (the end of the source past its last line). */
function lineStartOffset(source: string, line: number): number {
  let at = 0;
  for (let l = 1; l < line; l++) {
    const nl = source.indexOf("\n", at);
    if (nl < 0) return source.length;
    at = nl + 1;
  }
  return at;
}

/** The 1-based line of source offset `pos`. */
function lineOf(source: string, pos: number): number {
  let line = 1;
  for (let i = source.indexOf("\n"); i >= 0 && i < pos; i = source.indexOf("\n", i + 1)) line += 1;
  return line;
}

/** Scoping prefixes on a declaration's first line (`open X in theorem …`): its docstring goes after
 *  them, so the slot is the first code after the last one. */
const SCOPE_PREFIXES = /^[ \t]*(?:(?:open|omit|include|set_option)\b[^\n]*?\bin[ \t]+)+/;

/** A declaration of the file before the edit, as the edit left it. */
export interface DeclAfterEdit {
  /** The text of its docstring now (undefined: none in the source). */
  doc: string | undefined;
  /** Whether the file had a docstring in its slot before the edit. */
  hadDoc: boolean;
  /** Its first code line in the edited file. */
  line: number;
}

export type DocstringEditCheck =
  /** The edit changed code, a comment or a column outside docstrings (a declaration's head line
   *  aside): `line` is the first edited line that differs. */
  | { status: "code-changed"; line: number }
  /** Docstrings only, but one stands outside the slots (on a declaration the index reports, where
   *  the file had one), two share a slot, or one is left open. */
  | { status: "unplaced"; line: number }
  /** Docstrings only, each in a slot. `declAt(L)` reads the declaration that started at line L of
   *  the file before the edit. */
  | { status: "ok"; declAt: (line: number) => DeclAfterEdit };

/**
 * Check an edit of one file that may change docstrings only. `before` is the file the index was
 * taken from, `declLines` the 1-based lines its declarations start at (a documented declaration
 * starts at its docstring). Pure.
 */
export function checkDocstringEdit(before: string, after: string, declLines: readonly number[]): DocstringEditCheck {
  const rb = docstringResidue(before);
  const ra = docstringResidue(after);
  const changedAt = (i: number): DocstringEditCheck => {
    let j = Math.min(i, ra.src.length - 1);
    while (j > 0 && ra.src[j]! < 0) j -= 1;
    return { status: "code-changed", line: j >= 0 && ra.src[j]! >= 0 ? lineOf(after, ra.src[j]!) : 1 };
  };
  if (rb.text !== ra.text) {
    let i = 0;
    while (i < rb.chars.length && i < ra.chars.length && rb.chars[i] === ra.chars[i]) i += 1;
    return changedAt(i);
  }
  const slotOfLine = (line: number) => {
    const at = lineStartOffset(before, line);
    const eol = before.indexOf("\n", at);
    const prefix = SCOPE_PREFIXES.exec(before.slice(at, eol < 0 ? before.length : eol));
    return codeAnchor(rb, at + (prefix ? prefix[0].length : 0));
  };
  const docsBefore = new Set(rb.docs.map((d) => codeAnchor(rb, d.end)));
  const slots = new Set<number>([...docsBefore, ...declLines.filter((l) => l > 0).map(slotOfLine)]);
  slots.delete(-1);
  // The same characters: each in the same column, except on a declaration's head line from its
  // slot on (a docstring written inline before it, or moved off its line, shifts it; Lean's
  // position checks read the column of the docstring, which opens the declaration, and what the
  // declaration states is compared by its fingerprint after the build) and where both follow a
  // docstring on its last line.
  const headLine = new Array<boolean>(rb.chars.length).fill(false);
  for (const a of slots) for (let i = a; i < rb.chars.length && rb.src[i]! >= 0; i++) headLine[i] = true;
  const moved = rb.col.findIndex((c, i) => c !== ra.col[i] && !headLine[i] && !(rb.afterDoc[i] && ra.afterDoc[i]));
  if (moved >= 0) return changedAt(moved);
  const docAt = new Map<number, string>();
  for (const d of ra.docs) {
    const a = codeAnchor(ra, d.end);
    if (!d.closed || a < 0 || !slots.has(a) || docAt.has(a)) return { status: "unplaced", line: lineOf(after, d.start) };
    docAt.set(a, d.body);
  }
  return {
    status: "ok",
    declAt: (line) => {
      const a = slotOfLine(line);
      return { doc: docAt.get(a), hadDoc: docsBefore.has(a), line: a >= 0 ? lineOf(after, ra.src[a]!) : line };
    },
  };
}
