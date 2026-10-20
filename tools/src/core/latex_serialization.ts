/** N-family TeX control words (spelled without the leading `n`) whose under-escaped
 * `\n...` form silently decodes to a newline + remainder. Unlike b/f/r/t, a decoded
 * newline is legitimate content (multi-line TeX must use `\n` escapes in valid JSON),
 * so restoration is dictionary-gated. Multi-char suffixes require a non-letter,
 * non-dot boundary (the dot exclusion keeps a line break before "e.g."/"eg." intact). */
const N_COMMAND_MULTI =
  /^(?:eq|otin|otag|ot|abla|mid|eg|olimits|onumber|atural|earrow|warrow|ewline|cong|leq|geq|gtr|sim|prec|succ|vdash|vDash|Vdash|VDash|Rightarrow|Leftarrow|Leftrightarrow|subseteq|supseteq|triangleleft|triangleright|orm)(?![A-Za-z.])/;
// Deliberately ABSENT from the table: suffixes that are common prose words
// ("exists" for `\nexists`, "less" for `\nless`, "parallel" for `\nparallel`).
// A line break before such a word is far more frequent than an under-escaped
// spelling of the command, so inferring the command there corrupts legitimate
// prose; those three commands must be authored with the doubled backslash.
/** The single-letter suffix `e` (`\ne`) needs the legacy tight boundary: only a
 * delimiter that is natural after the relation but implausible after the letter
 * `e` as ordinary math. Corpus-verified exclusions: `e^`/`e_` (the exponential
 * and subscripted variables, e.g. an mgf bound `\[` + newline + `e^{s\lambda n}`)
 * must stay newlines. `u` (`\nu`) is deliberately NOT inferred at all — accepted
 * papers legitimately open display math with the variable `u` (`u^\alpha`,
 * `u\ge…`), so an under-escaped `\nu` is accepted silent residue instead. */
const N_COMMAND_SHORT = /^e(?=$|[\s\\}\],])/;

/** Normalize raw model-authored JSON bytes BEFORE `JSON.parse`. Post-parse, an
 * under-escaped `\theta` and an intended tab+`heta` are the same characters — the
 * information is destroyed — but in the raw bytes the single backslash is still
 * visible, so repair is exact rather than heuristic. Inside string literals, an
 * odd-count backslash followed by:
 *   - `b`/`f`/`r`/`t` + a letter is an under-escaped TeX control word (`\beta`,
 *     `\frac`, `\rho`, `\theta`, `\to`, …): double the backslash. Intentional
 *     control characters directly before a letter do not occur in this pipeline;
 *     a wrong doubling is visible TeX garbage caught by the render gate, whereas
 *     the alternative was silent data corruption.
 *   - `n` is doubled only for dictionary-listed TeX commands at a word boundary;
 *     every other `\n` stays a genuine line break.
 *   - `u` + 4 hex digits is a genuine `\uXXXX` escape and is preserved; any other
 *     `\u` (`\underline`, …) is doubled.
 *   - any character that is not a valid JSON escape (`\alpha`, `\{`, `\[`, …) is
 *     doubled: JSON.parse would otherwise throw, and the only sane reading of an
 *     isolated invalid escape is a literal TeX backslash.
 * Text outside string literals, even-count backslash runs, `\"`, `\/`, and `\\`
 * are untouched. The transform is idempotent. */
export function normalizeRawModelJson(raw: string): string {
  let out = "";
  let i = 0;
  let inString = false;
  while (i < raw.length) {
    const ch = raw[i];
    if (!inString) {
      if (ch === '"') inString = true;
      out += ch;
      i += 1;
      continue;
    }
    if (ch === '"') {
      inString = false;
      out += ch;
      i += 1;
      continue;
    }
    if (ch !== "\\") {
      out += ch;
      i += 1;
      continue;
    }
    let j = i;
    while (j < raw.length && raw[j] === "\\") j += 1;
    const run = raw.slice(i, j);
    const next = raw[j] ?? "";
    if (run.length % 2 === 0) {
      // Pairs decode to literal backslashes; the following char is plain content.
      out += run;
      i = j;
      continue;
    }
    // Odd run: the final backslash + `next` forms a JSON escape (or an invalid one).
    const keep = () => {
      out += run + next;
      i = j + 1;
    };
    const double = () => {
      out += run + "\\" + next;
      i = j + 1;
    };
    if (next === '"' || next === "\\" || next === "/") keep();
    else if (next === "u") {
      if (/^[0-9a-fA-F]{4}/.test(raw.slice(j + 1))) keep();
      else double();
    } else if (next === "b" || next === "f" || next === "r" || next === "t") {
      if (/^[A-Za-z]/.test(raw.slice(j + 1))) double();
      else keep();
    } else if (next === "n") {
      const rest = raw.slice(j + 1);
      if (N_COMMAND_MULTI.test(rest) || N_COMMAND_SHORT.test(rest)) double();
      else keep();
    } else double();
  }
  return out;
}

/** The backstop of a core read (`parseTypedCore`): no string of a core may hold a control
 * character other than a newline, a CRLF line ending or a tab (the source's indentation; TeX
 * reads it as a space). A core's text is copied from the paper's source, so such a character
 * is in the source file: fail loudly with the field path instead of letting it reach a
 * prompt, the render or proposal comparison. */
export function assertNoDecodedControlChars(value: unknown, source: string): void {
  const offenses: string[] = [];
  const forbidden = /[\u0000-\u0008\u000b\u000c\u000e-\u001f]|\r(?!\n)/;
  const visit = (v: unknown, path: string): void => {
    if (typeof v === "string") {
      const m = forbidden.exec(v);
      if (m) {
        const code = m[0].charCodeAt(0).toString(16).toUpperCase().padStart(4, "0");
        const snippet = JSON.stringify(v.slice(Math.max(0, m.index - 20), m.index + 20));
        offenses.push(`${path || "(root)"}: U+${code} at offset ${m.index} near ${snippet}`);
      }
      return;
    }
    if (Array.isArray(v)) {
      v.forEach((child, idx) => visit(child, `${path}[${idx}]`));
      return;
    }
    if (v !== null && typeof v === "object") {
      for (const [key, child] of Object.entries(v)) visit(child, path ? `${path}.${key}` : key);
    }
  };
  visit(value, "");
  if (offenses.length > 0) {
    throw new Error(
      `${source}: control character(s) in the core's text, copied from the paper's source — ` +
        `the source file holds the character at that place and it must be removed there. ` +
        `Offending field(s):\n` +
        offenses.map((o) => `  - ${o}`).join("\n"),
    );
  }
}
