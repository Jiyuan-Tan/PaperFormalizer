// Lean source readers for the toolkit: import lists and declared names, over file text only.
// Comments and strings are masked first (offsets preserved), so prose never counts as code.
import { maskLeanCommentsAndStrings } from "../shared/lean_mask.js";
import { LEAN_DECL_HEADER_RE, parseLeanImport, type LeanImport } from "../shared/lean_syntax.js";

export interface LeanImportAt extends LeanImport {
  /** 0-based line index. */
  line: number;
}

/** Every import line of `text`, in source order. */
export function leanImports(text: string): LeanImportAt[] {
  const out: LeanImportAt[] = [];
  maskLeanCommentsAndStrings(text).split("\n").forEach((line, i) => {
    const imp = parseLeanImport(line);
    if (imp) out.push({ ...imp, line: i });
  });
  return out;
}

export interface DeclaredName {
  /** Fully qualified name (namespace prefix applied, `_root_.` stripped). */
  name: string;
  kind: string;
  /** 0-based line index of the declaration header. */
  line: number;
  isPrivate: boolean;
}

const SECTION_OPEN_RE = /^[ \t]*(?:@\[[^\]]*\][ \t]*)*(?:public[ \t]+)?(?:noncomputable[ \t]+)?section\b[ \t]*([^\s]*)/;
const NAMESPACE_RE = /^[ \t]*namespace[ \t]+([^\s]+)/;
const END_RE = /^[ \t]*end\b[ \t]*([^\s]*)/;
const NAME_AFTER_KEYWORD_RE = /^\s+([^\s:({[\]]+)/;

/**
 * Named declarations of `text`. With `range` (character offsets `[from, to)`), only headers
 * starting inside the range are returned, but the namespace context is tracked from the start
 * of the file, so an insert into an open namespace yields correctly qualified names.
 * Anonymous instances and `example`s have no name and are skipped.
 */
export function declaredNames(text: string, range?: { from: number; to: number }): DeclaredName[] {
  const masked = maskLeanCommentsAndStrings(text);
  const lines = masked.split("\n");
  const scopes: Array<{ kind: "namespace" | "section"; name: string }> = [];
  const out: DeclaredName[] = [];
  let offset = 0;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const lineStart = offset;
    offset += line.length + 1;
    const ns = NAMESPACE_RE.exec(line);
    if (ns) {
      scopes.push({ kind: "namespace", name: ns[1] });
      continue;
    }
    const end = END_RE.exec(line);
    if (end) {
      scopes.pop();
      continue;
    }
    const decl = LEAN_DECL_HEADER_RE.exec(line);
    if (decl) {
      const kind = decl[1];
      if (kind === "example") continue;
      const rest = line.slice(decl.index + decl[0].length);
      const m = NAME_AFTER_KEYWORD_RE.exec(rest);
      if (!m) continue; // anonymous instance
      if (range && (lineStart < range.from || lineStart >= range.to)) continue;
      let name = m[1];
      if (name.startsWith("_root_.")) name = name.slice("_root_.".length);
      else {
        const prefix = scopes.filter((s) => s.kind === "namespace").map((s) => s.name).join(".");
        if (prefix) name = `${prefix}.${name}`;
      }
      const head = line.slice(0, decl.index + decl[0].length);
      out.push({ name, kind, line: i, isPrivate: /(?:^|\s)private\s/.test(head) });
      continue;
    }
    const sec = SECTION_OPEN_RE.exec(line);
    if (sec) scopes.push({ kind: "section", name: sec[1] ?? "" });
  }
  return out;
}

/** Module name for a `/`-separated source path relative to the Lake root (`A/B.lean` → `A.B`). */
export function moduleNameFromPath(relPath: string): string {
  return relPath.replace(/\\/g, "/").replace(/\.lean$/, "").split("/").join(".");
}

export interface ForbiddenLeanToken {
  token: "sorry" | "admit" | "axiom";
  /** 0-based line index. */
  line: number;
}

const SORRY_RE = /(?<![A-Za-z0-9_'.])sorry(?![A-Za-z0-9_'!?])/;
const ADMIT_RE = /(?<![A-Za-z0-9_'.])admit(?![A-Za-z0-9_'!?])/;
const AXIOM_DECL_RE = /^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*axiom(?![A-Za-z0-9_'])/;

/**
 * Proof holes and new axioms in `text`, outside comments and strings: a `sorry` or `admit` term /
 * tactic anywhere, and an `axiom` declaration at the start of a line. Promoted toolkit content must
 * have none (the toolkit is axiom-clean by contract).
 */
export function forbiddenLeanTokens(text: string): ForbiddenLeanToken[] {
  const out: ForbiddenLeanToken[] = [];
  maskLeanCommentsAndStrings(text).split("\n").forEach((line, i) => {
    if (SORRY_RE.test(line)) out.push({ token: "sorry", line: i });
    if (ADMIT_RE.test(line)) out.push({ token: "admit", line: i });
    if (AXIOM_DECL_RE.test(line)) out.push({ token: "axiom", line: i });
  });
  return out;
}

// ─── declaration spans (round-B moves) ─────────────────────────────────────

/** A top-level declaration's source span and the scope context it elaborates in. */
export interface DeclSpan {
  /** Fully qualified name (enclosing namespaces applied, `_root_.` stripped). */
  name: string;
  /** The name token as written in the header. */
  written: string;
  kind: string;
  isPrivate: boolean;
  /** 0-based line of the declaration keyword. */
  headerLine: number;
  /** 0-based first line of the span: the attached doc comment / attribute lines. */
  startLine: number;
  /** 0-based line after the span's last non-blank line. */
  endLine: number;
  /** Character offsets of `[startLine, endLine)`. */
  from: number;
  to: number;
  /** Character offsets of the name token in the header. */
  nameFrom: number;
  nameTo: number;
  /** Enclosing namespaces, outermost first. */
  namespaces: string[];
  /** `open` / `variable` / `universe` / `set_option` / `include` / `omit` commands in scope at
   *  the declaration (outer scopes first), verbatim. */
  context: string[];
  /** Whether a `noncomputable section` is open at the declaration. */
  noncomputable: boolean;
}

const CONTEXT_COMMAND_RE = /^(?:open|variable|universe|set_option|include|omit)\b/;
/** A command that scopes only the next one (`open … in`, `set_option … in`, `omit … in`,
 *  `include … in`, `variable … in`): part of the declaration it scopes. */
const SCOPED_IN_START_RE = /^(?:open|set_option|omit|include|variable)\b/;
/** Column-0 tokens that continue the previous declaration rather than start a command. */
const CONTINUATION_RE = /^(?:\||where\b|deriving\b|termination_by\b|decreasing_by\b|with\b|\))/;

/**
 * Every named top-level declaration of `text` with its span, for cutting a declaration out of a
 * file and re-emitting it elsewhere. A span runs from the declaration's attached doc comment and
 * attribute lines (contiguous, no blank line in between) to the line before the next column-0
 * command; column-0 continuations (`| …` equations, `where`, `deriving`, `termination_by`,
 * `decreasing_by`) stay inside. Written for the layout PaperFormalizer's F stages emit (commands at
 * column 0, bodies indented); anything else is caught by the build gate that follows every move.
 */
export function declarationSpans(text: string): DeclSpan[] {
  const masked = maskLeanCommentsAndStrings(text);
  const lines = text.split("\n");
  const mlines = masked.split("\n");
  const offsets: number[] = [];
  let off = 0;
  for (const l of lines) {
    offsets.push(off);
    off += l.length + 1;
  }
  const offsetOf = (line: number) => (line < lines.length ? offsets[line]! : text.length);
  type Scope = { kind: "namespace" | "section"; name: string; context: string[]; noncomputable: boolean };
  const scopes: Scope[] = [{ kind: "section", name: "", context: [], noncomputable: false }];
  const isCommandStart = (i: number): boolean => {
    const m = mlines[i]!;
    return m.length > 0 && !/^\s/.test(m) && !CONTINUATION_RE.test(m);
  };
  /** Line after the command starting at `i` (next column-0 command or column-0 comment). */
  const commandEnd = (i: number): number => {
    let j = i + 1;
    for (; j < lines.length; j += 1) {
      if (isCommandStart(j)) break;
      const raw = lines[j]!;
      if (raw.length > 0 && !/^\s/.test(raw) && mlines[j]!.trim() === "") break; // column-0 comment
    }
    return j;
  };
  const out: DeclSpan[] = [];
  for (let i = 0; i < lines.length; i += 1) {
    const m = mlines[i]!;
    if (!isCommandStart(i)) continue;
    const ns = NAMESPACE_RE.exec(m);
    if (ns) {
      scopes.push({ kind: "namespace", name: ns[1]!, context: [], noncomputable: false });
      continue;
    }
    if (END_RE.test(m)) {
      if (scopes.length > 1) scopes.pop();
      continue;
    }
    const decl = LEAN_DECL_HEADER_RE.exec(m);
    if (decl) {
      const kind = decl[1]!;
      const end = commandEnd(i);
      const rest = m.slice(decl.index + decl[0].length);
      const nm = NAME_AFTER_KEYWORD_RE.exec(rest);
      if (kind !== "example" && nm) {
        let start = i;
        while (start > 0) {
          const prevRaw = lines[start - 1]!;
          const prevMasked = mlines[start - 1]!;
          if (prevRaw.trim() === "") break;
          if (prevRaw.includes("/-!")) break;
          if (prevMasked.trim() === "" && /-\/\s*$/.test(prevRaw)) {
            // A doc comment ending just above: take it whole, blank lines inside it included.
            let k = start - 1;
            while (k > 0 && !lines[k]!.includes("/-")) k -= 1;
            if (lines[k]!.includes("/-!")) break;
            start = k;
            continue;
          }
          if (prevMasked.trim() === "" || /^@\[/.test(prevMasked)) { start -= 1; continue; }
          // A scoping `… in` prefix, possibly over several lines: take it whole.
          if (/\bin\s*$/.test(prevMasked)) {
            let k = start - 1;
            while (k > 0 && /^\s/.test(mlines[k]!)) k -= 1;
            if (SCOPED_IN_START_RE.test(mlines[k]!)) { start = k; continue; }
          }
          break;
        }
        let last = end;
        while (last > i + 1 && lines[last - 1]!.trim() === "") last -= 1;
        const namespaces = scopes.filter((s) => s.kind === "namespace").map((s) => s.name);
        let name = nm[1]!;
        if (name.startsWith("_root_.")) name = name.slice("_root_.".length);
        else if (namespaces.length) name = `${namespaces.join(".")}.${name}`;
        const head = m.slice(0, decl.index + decl[0].length);
        const nameFrom = offsetOf(i) + decl.index + decl[0].length + nm.index + nm[0].length - nm[1]!.length;
        out.push({
          name, written: nm[1]!, kind, isPrivate: /(?:^|\s)private\s/.test(head), headerLine: i,
          startLine: start, endLine: last, from: offsetOf(start), to: offsetOf(last),
          nameFrom, nameTo: nameFrom + nm[1]!.length,
          namespaces, context: scopes.flatMap((s) => s.context), noncomputable: scopes.some((s) => s.noncomputable),
        });
      }
      i = end - 1;
      continue;
    }
    const sec = SECTION_OPEN_RE.exec(m);
    if (sec) {
      scopes.push({ kind: "section", name: sec[1] ?? "", context: [], noncomputable: /\bnoncomputable\s+section\b/.test(m) });
      continue;
    }
    if (CONTEXT_COMMAND_RE.test(m)) {
      const end = commandEnd(i);
      let last = end;
      while (last > i + 1 && lines[last - 1]!.trim() === "") last -= 1;
      const cmd = lines.slice(i, last).join("\n");
      // `set_option … in` / `open … in` scope only the next command, which carries it in its span.
      if (!/\bin\s*$/.test(mlines.slice(i, last).join("\n").trimEnd())) scopes[scopes.length - 1]!.context.push(cmd);
      i = end - 1;
    }
  }
  return out;
}

/** Identifier tokens of `text` outside comments and strings: `[start, end)` offsets and the text. */
export function identifierTokens(text: string): Array<{ from: number; to: number; text: string }> {
  const masked = maskLeanCommentsAndStrings(text);
  const out: Array<{ from: number; to: number; text: string }> = [];
  const re = /(?<![\p{L}\p{N}_'!?.])[\p{L}_][\p{L}\p{N}_'!?]*(?:\.[\p{L}_][\p{L}\p{N}_'!?]*)*/gu;
  for (let m = re.exec(masked); m; m = re.exec(masked)) out.push({ from: m.index, to: m.index + m[0].length, text: text.slice(m.index, m.index + m[0].length) });
  return out;
}
