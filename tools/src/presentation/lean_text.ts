// Small text primitives over Lean source shared by the statement structurer (`lean_structure.ts`,
// its PaperFormalizer additions `lean_structure_tc.ts`) and the rows F5 links (`formalization/
// lean_rows.ts`, `nl_links.ts`): ONE set of bracket characters, one whitespace squash, one matcher.

import { normAwareDepths } from "./lean_statement.js";

export const OPENERS = "({[⦃";
export const CLOSERS = ")}]⦄";

/** All whitespace removed — the comparison used to prove a structured view reproduces its source
 *  exactly, modulo layout. */
export function squash(text: string): string {
  return text.replace(/\s+/g, "");
}

/** Index of the closer matching the opener at position 0, or -1. */
export function matchedCloseIndex(text: string): number {
  if (!OPENERS.includes(text[0] ?? "")) return -1;
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    if (OPENERS.includes(text[i])) depth++;
    else if (CLOSERS.includes(text[i])) {
      depth--;
      if (depth === 0) return i;
    }
  }
  return -1;
}

/** `t` without one pair of round brackets that encloses all of it. */
export function unwrapParens(t: string): string {
  return t.startsWith("(") && matchedCloseIndex(t) === t.length - 1 ? t.slice(1, -1).trim() : t;
}

export function topLevelColonIndex(text: string): number {
  const depths = normAwareDepths(text);
  for (let i = 0; i < text.length; i++) {
    if (depths[i] === 0 && text[i] === ":" && text[i + 1] !== "=") return i;
  }
  return -1;
}

/** Whole-word keyword at `i` — `let`, not `letFun`/`S.let`. */
export function keywordAt(text: string, i: number, kw: string): boolean {
  const word = (c: string | undefined) => c != null && /[A-Za-z0-9_'.]/.test(c);
  return text.startsWith(kw, i) && !word(text[i - 1]) && !word(text[i + kw.length]);
}

/** Removes the common indentation of continuation lines, so a binder or conclusion lifted out of a
 *  deeply indented signature reads at the left margin without losing its internal line structure. */
export function dedent(text: string): string {
  const lines = text.replace(/\s+$/, "").split("\n");
  if (lines.length < 2) return text.trim();
  let min = Infinity;
  for (const l of lines.slice(1)) {
    if (!l.trim()) continue;
    min = Math.min(min, l.match(/^ */)![0].length);
  }
  if (!Number.isFinite(min) || min === 0) return lines.join("\n").trimStart();
  return [lines[0].trimStart(), ...lines.slice(1).map((l) => l.slice(min))].join("\n");
}

/** A binder group's name part: identifier-shaped tokens only. */
export const BINDER_NAMES = /^[^\s()[\]{}⦃⦄:∀∃λ,]+(\s+[^\s()[\]{}⦃⦄:∀∃λ,]+)*$/;

/** A bracketed group `(names : type)` (or `{…}`, `⦃…⦄`, `[…]`): its bracket, names and type; null
 *  for anything else (an anonymous instance `[C x]`, a bracketed proposition `(A → B)`). */
export function binderGroup(code: string): { open: string; names: string; type: string } | null {
  const t = code.trim();
  if (!OPENERS.includes(t[0] ?? "") || matchedCloseIndex(t) !== t.length - 1) return null;
  const inner = t.slice(1, -1).trim();
  const colon = topLevelColonIndex(inner);
  if (colon < 0) return null;
  const names = inner.slice(0, colon).trim();
  if (!BINDER_NAMES.test(names)) return null;
  return { open: t[0], names, type: inner.slice(colon + 1).trim() };
}
