/** TeX-aware text heuristics shared across the core gate, the transcription lint,
 * the F-stage reviewers and the graph note.
 *
 * The recurring bug class this module exists for: a mechanical sentence/token
 * heuristic (split on `.`-whitespace, count periods, match a word) applied to
 * text that is LaTeX, where a period is often NOT a sentence boundary (decimal
 * `0.5`, abbreviation `i.i.d.`, `w.r.t.`, `Thm. 2.1`) and a backslash command
 * often follows real boundaries (`. \(`). Each consumer used to hand-roll its
 * own partial guard; keep the shared knowledge here so a fix lands everywhere.
 */

/** Sentinel used to neutralize a period that is NOT a sentence boundary.
 * U+2024 ONE DOT LEADER: visually a period, never emitted by the models, and
 * outside every consumer's split/lookahead classes. */
export const MASKED_PERIOD = "․";

/** Abbreviations whose trailing (and internal) periods are not sentence ends.
 * Multi-dot tokens (`i.i.d.`, `w.r.t.`) are listed whole so their internal
 * periods are masked too. Single bare letters are deliberately absent — `p.`
 * may be a variable ending a real sentence. */
const ABBREVIATION_RE =
  // `No.` and `etc.` are deliberately absent: both routinely END real
  // sentences ("… is no.", "… are bounded, etc."), and losing a genuine
  // boundary (missed omnibus/overclaim detection) costs more than the rare
  // "No. 5" / mid-sentence "etc." false split.
  /\b(?:i\.i\.d|a\.s|a\.e|w\.r\.t|w\.l\.o\.g|u\.i|r\.h\.s|l\.h\.s|s\.t|a\.k\.a|e\.g|i\.e|c\.f|cf|resp|vs|viz|approx|Thm|Thms|Lem|Lems|Prop|Props|Cor|Defn?|Rem|Asm|Ass|Assump|Eqs?|Figs?|Secs?|Chs?|Vols?|pp)\.(?!\w)/gi;

/** Mask every period that provably does not end a sentence: decimal points
 * (`0.5`, `2.1`) and known abbreviations (`i.i.d.`, `w.r.t.`, `Thm.`). The
 * result is only for boundary COUNTING/SPLITTING — never persist it. */
export function maskNonBoundaryPeriods(text: string): string {
  return text
    .replace(/(?<=\d)\.(?=\d)/g, MASKED_PERIOD)
    .replace(ABBREVIATION_RE, (m) => m.replace(/\./g, MASKED_PERIOD));
}

/** Source fragment matching ONE closing token that may sit between a sentence
 * period and the following whitespace: closing TeX math delimiters, an
 * `\end{env}`, closing quotes/brackets, or an inline-math `$`. */
export const SENTENCE_CLOSER_SRC = String.raw`(?:\\[\)\]]|\\end\{[^{}]*\}|[”"'’)\]$])`;

/** True iff the text contains a PLAUSIBLE sentence-ending period strictly
 * before `end` (exclusive): a period (after masking, so not a decimal or
 * abbreviation) followed by optional closers and then whitespace. Callers pass
 * pre-masked text. */
export function hasPlausibleSentenceEnd(maskedText: string): boolean {
  return new RegExp(`\\.${SENTENCE_CLOSER_SRC}*\\s`).test(maskedText);
}

/** `tex` with every `%` comment blanked, offsets kept (`\%` is a percent sign): where a landmark of
 * the source (`\documentclass`, `\begin{document}`, a `\usepackage`) is searched for by position. */
export function blankTexComments(tex: string): string {
  let out = "";
  for (let i = 0; i < tex.length; i += 1) {
    const ch = tex[i]!;
    if (ch === "\\") {
      out += tex.slice(i, i + 2);
      i += 1;
    } else if (ch === "%") {
      let j = i;
      while (j < tex.length && tex[j] !== "\n") j += 1;
      out += " ".repeat(j - i);
      i = j - 1;
    } else out += ch;
  }
  return out;
}

/** Truncate TeX to at most `max` chars without cutting inside an inline/display
 * math segment: if the cut lands inside an unclosed `\(`/`\[`/`$`, back off to
 * just before that opener. Falls back to the hard cut when backing off would
 * drop everything (a single math segment longer than `max`). */
export function truncateTexSafe(text: string, max: number): string {
  if (text.length <= max) return text;
  const cut = text.slice(0, max);
  let mode: "text" | "paren" | "bracket" | "dollar" = "text";
  let openAt = -1;
  for (let i = 0; i < cut.length; i++) {
    const ch = cut[i];
    if (ch === "\\") {
      const next = cut[i + 1];
      if (mode === "text" && (next === "(" || next === "[")) {
        mode = next === "(" ? "paren" : "bracket";
        openAt = i;
      } else if ((mode === "paren" && next === ")") || (mode === "bracket" && next === "]")) {
        mode = "text";
      }
      i++; // skip the escaped char in every mode (also guards `\$`)
      continue;
    }
    if (ch === "$") {
      // `$$…$$` is ONE display toggle — per-`$` toggling read the display body
      // as text mode and let the cut land inside it.
      const isDouble = cut[i + 1] === "$";
      if (mode === "text") {
        mode = "dollar";
        openAt = i;
      } else if (mode === "dollar") {
        mode = "text";
      }
      if (isDouble) i += 1;
    }
  }
  // Back off even from position 0: an empty result is balanced, and every
  // caller has a fallback — a hard cut inside math seals an unbalanced
  // delimiter into a persisted/compiled field.
  if (mode !== "text" && openAt >= 0) return text.slice(0, openAt).trimEnd();
  return cut;
}
