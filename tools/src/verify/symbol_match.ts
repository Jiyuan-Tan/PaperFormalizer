/**
 * Finding a symbol of the core's table in TeX text — for the V1.5 symbol referee (where a symbol is
 * introduced and used in `flat.tex`) and for the core graph (which statements use a symbol).
 *
 * Both sides are compared as canonical TeX token lists: whitespace and comments dropped; a
 * single-token sub/superscript or accent argument braced (`\hat\theta_0` = `\hat{\theta}_{0}`);
 * `^{a}_{b}` reordered to `_{b}^{a}` (`\alpha^{\min}_0` = `\alpha_0^{\min}`); `\widehat` / `\widetilde`
 * / `\overline` read as `\hat` / `\tilde` / `\bar`. An occurrence is a WHOLE symbol: not the base of
 * a longer one (followed by a subscript, a prime, or a non-numeric superscript: `\Delta` does not
 * occur in `\Delta_h`, `\Delta'` or `\theta_0` in `\theta_0^h`, but does in `\Delta^2`), not inside
 * an accent or script argument (`\sigma` does not occur in `\bar{\sigma}`), and a one-letter name
 * not inside a word.
 */
import { normalizeSymbol } from "../core/symbol_names.js";

const ALIAS: Record<string, string> = { widehat: "hat", widetilde: "tilde", overline: "bar", bm: "boldsymbol" };
/** Commands taking one argument that is part of a symbol's name. */
const ACCENTS = new Set(
  ["hat", "bar", "tilde", "check", "dot", "ddot", "vec", "breve", "acute", "grave", "mathcal", "mathbb", "mathrm", "mathbf", "boldsymbol", "mathsf", "mathfrak", "mathscr", "mathit", "underline", "operatorname"].map((c) => `\\${c}`),
);

export interface TexToken {
  t: string;
  /** Offsets of the token in the text it came from, `[at, end)` (an inserted brace: empty, at its
   * neighbour's edge). */
  at: number;
  end: number;
}

/** Raw TeX tokens: control words (aliased), control symbols, single characters; no whitespace, no comments. */
export function texTokens(s: string): TexToken[] {
  const out: TexToken[] = [];
  let i = 0;
  while (i < s.length) {
    const c = s[i]!;
    if (/\s/.test(c)) {
      i += 1;
      continue;
    }
    if (c === "%") {
      while (i < s.length && s[i] !== "\n") i += 1;
      continue;
    }
    if (c === "\\") {
      const m = /^\\([A-Za-z]+)/.exec(s.slice(i, i + 64));
      if (m) {
        out.push({ t: `\\${ALIAS[m[1]!] ?? m[1]!}`, at: i, end: i + m[0].length });
        i += m[0].length;
        continue;
      }
      out.push({ t: s.slice(i, i + 2), at: i, end: i + 2 });
      i += 2;
      continue;
    }
    out.push({ t: c, at: i, end: i + 1 });
    i += 1;
  }
  return out;
}

/** End (exclusive) of the group starting at `i` (a `{…}` group, else the single token). */
function groupEnd(ts: readonly TexToken[], i: number): number {
  if (ts[i]?.t !== "{") return Math.min(ts.length, i + 1);
  let depth = 0;
  for (let j = i; j < ts.length; j += 1) {
    if (ts[j]!.t === "{") depth += 1;
    else if (ts[j]!.t === "}") {
      depth -= 1;
      if (depth === 0) return j + 1;
    }
  }
  return ts.length;
}

/** The canonical token list (see the module comment). */
export function canonicalTokens(s: string): TexToken[] {
  const raw = texTokens(s);
  // 1. brace single-token arguments of scripts and accents; `^{\prime}` / `^\prime` → `'`.
  const braced: TexToken[] = [];
  for (let i = 0; i < raw.length; i += 1) {
    const tok = raw[i]!;
    const next = raw[i + 1];
    if (tok.t === "^" && next?.t === "\\prime") {
      braced.push({ t: "'", at: tok.at, end: next.end });
      i += 1;
      continue;
    }
    if (tok.t === "^" && next?.t === "{" && raw[i + 2]?.t === "\\prime" && raw[i + 3]?.t === "}") {
      braced.push({ t: "'", at: tok.at, end: raw[i + 3]!.end });
      i += 3;
      continue;
    }
    braced.push(tok);
    if ((tok.t === "_" || tok.t === "^" || ACCENTS.has(tok.t)) && next && next.t !== "{" && next.t !== "}") {
      braced.push({ t: "{", at: next.at, end: next.at }, next, { t: "}", at: next.end, end: next.end });
      i += 1;
    }
  }
  // 2. `^{a}_{b}` → `_{b}^{a}`.
  const out = braced;
  for (let i = 0; i < out.length; i += 1) {
    if (out[i]!.t !== "^") continue;
    const supEnd = groupEnd(out, i + 1);
    if (out[supEnd]?.t !== "_") continue;
    const subEnd = groupEnd(out, supEnd + 1);
    const sup = out.slice(i, supEnd);
    const sub = out.slice(supEnd, subEnd);
    out.splice(i, subEnd - i, ...sub, ...sup);
    i += sub.length - 1;
  }
  return out;
}

const NUMERIC = /^[0-9+\-/.*]$/;

/** Whether the tokens `[i, j)` of `ts` are an occurrence of the whole symbol (see the module comment). */
function wholeAt(ts: readonly TexToken[], i: number, j: number, oneLetter: boolean): boolean {
  const next = ts[j]?.t;
  if (next === "_" || next === "'") return false;
  if (next === "^") {
    const end = groupEnd(ts, j + 1);
    const inner = ts.slice(ts[j + 1]?.t === "{" ? j + 2 : j + 1, ts[j + 1]?.t === "{" ? end - 1 : end);
    if (inner.length === 0 || !inner.every((x) => NUMERIC.test(x.t))) return false;
    if (ts[end]?.t === "_" || ts[end]?.t === "'") return false;
  }
  const prev = ts[i - 1]?.t;
  if (prev === "_" || prev === "^" || (prev !== undefined && ACCENTS.has(prev))) return false;
  if (prev === "{" && i >= 2) {
    const pp = ts[i - 2]!.t;
    if (pp === "_" || pp === "^" || ACCENTS.has(pp)) return false;
  }
  if (oneLetter) {
    const letter = (t: string | undefined): boolean => t !== undefined && /^[A-Za-z]$/.test(t);
    if (letter(prev) || letter(next)) return false;
  }
  return true;
}

/** A symbol name prepared for matching. */
export interface SymbolPattern {
  name: string;
  tokens: string[];
  oneLetter: boolean;
}

export function symbolPattern(name: string): SymbolPattern {
  const tokens = canonicalTokens(normalizeSymbol(name)).map((x) => x.t);
  return { name, tokens, oneLetter: tokens.length === 1 && /^[A-Za-z]$/.test(tokens[0]!) };
}

/** Every occurrence of the symbol in `text`: the offset (in `text`) of its first token and the
 * canonical token range. */
export function symbolOccurrences(text: string, pat: SymbolPattern, canon?: TexToken[]): Array<{ at: number; i: number; j: number }> {
  const ts = canon ?? canonicalTokens(text);
  const n = pat.tokens.length;
  const out: Array<{ at: number; i: number; j: number }> = [];
  if (n === 0) return out;
  for (let i = 0; i + n <= ts.length; i += 1) {
    let ok = true;
    for (let k = 0; k < n; k += 1) {
      if (ts[i + k]!.t !== pat.tokens[k]) {
        ok = false;
        break;
      }
    }
    if (ok && wholeAt(ts, i, i + n, pat.oneLetter)) out.push({ at: ts[i]!.at, i, j: i + n });
  }
  return out;
}

export function mentionsSymbol(text: string, pat: SymbolPattern): boolean {
  return symbolOccurrences(text, pat).length > 0;
}

/** Whether the symbol APPEARS in `text`: as a whole symbol, or decorated or inside a compound — the
 * base of a longer one (`\bar{M}` in `\bar{M}_h`), inside a script or an accent (`h` in `m_h`). What
 * a sentence says of such a compound it says of the symbol too, so a sentence is read for a symbol by
 * this test (`referee_symbols.ts` `sentencesNaming`), never by the stricter whole-symbol one — a
 * result lists a symbol in `free_symbols` that it only writes decorated. A one-letter name still
 * never inside a word. */
export function symbolAppears(text: string, pat: SymbolPattern): boolean {
  const ts = canonicalTokens(text);
  const n = pat.tokens.length;
  const letter = (t: string | undefined): boolean => t !== undefined && /^[A-Za-z]$/.test(t);
  for (let i = 0; n > 0 && i + n <= ts.length; i += 1) {
    if (pat.tokens.every((t, k) => ts[i + k]!.t === t) && !(pat.oneLetter && (letter(ts[i - 1]?.t) || letter(ts[i + n]?.t)))) return true;
  }
  return false;
}

const DEFINING_BEFORE = /\b(let|define[sd]?|denote[sd]?|write|writes|we call|called|where|set|given by|updating|redefine[sd]?)\b[^.;:]*$/i;
const DEFINING_AFTER = /^\s*\$?\s*(?:\\text\{\s*)?(?:denotes?\b|is (?:the|a|an|defined|given)\b|be (?:the|a|an)\b|to be\b|stands for\b|:=)/i;
const DEFINING_RELATION = new Set(["=", "\\coloneqq", "\\equiv", "\\triangleq", "\\defeq", "\\eqqcolon"]);

/** Whether the occurrence `occ` of a symbol on `line` defines it: followed by `=`, `:=`, `\coloneqq`,
 * `\equiv`…; or in a sentence that says so ("let", "define", "denote", "where", "write", "updating
 * … to be"; "… denotes", "… is the", "… to be"). */
export function isDefiningOccurrence(line: string, occ: { at: number; i: number; j: number }, canon: readonly TexToken[]): boolean {
  const next = canon[occ.j]?.t;
  if (next !== undefined && DEFINING_RELATION.has(next)) return true;
  if (next === ":" && canon[occ.j + 1]?.t === "=") return true;
  const endAt = Math.max(occ.at, ...canon.slice(occ.i, occ.j).map((x) => x.end));
  const before = line.slice(Math.max(0, occ.at - 80), occ.at);
  const after = line.slice(endAt, endAt + 60).replace(/^\s*\}/, "");
  return DEFINING_BEFORE.test(before) || DEFINING_AFTER.test(after);
}
