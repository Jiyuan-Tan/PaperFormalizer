// Import-free on purpose: the public site bundles `presentation/lean_decl_name.ts`, and any
// import chain from there into `graph/types.ts` drags zod into the site build, which does not
// declare it (the CI build broke on exactly that, 2026-09-10).
/**
 * Mask Lean comments, strings, and character literals with spaces while preserving byte offsets
 * and newlines. Parser-like consumers can safely scan the result for declaration/delimiter tokens
 * without being fooled by `"/-"`, `"def fake"`, `-- :=`, or brackets in comments.
 */
export function maskLeanCommentsAndStrings(s: string): string {
  // Built from slices of `s` joined once, not one `+=` per char: that left a rope of one node
  // per char, tens of bytes each, so masking a 10 MB generated module took hundreds of MB.
  const parts: string[] = [];
  let kept = 0; // start of the verbatim run not yet in `parts`
  /** Mask [from, to): every code unit a space, newlines kept. */
  const blank = (from: number, to: number): void => {
    parts.push(s.slice(kept, from), s.slice(from, to).replace(/[^\n]/g, " "));
    kept = to;
  };
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (ch === "/" && s[i + 1] === "-") {
      const start = i;
      let depth = 1;
      for (i += 2; i < s.length && depth > 0; ) {
        if (s[i] === "/" && s[i + 1] === "-") {
          depth++;
          i += 2;
        } else if (s[i] === "-" && s[i + 1] === "/") {
          depth--;
          i += 2;
        } else i++;
      }
      blank(start, i);
      i--;
      continue;
    }
    if (ch === "-" && s[i + 1] === "-") {
      const nl = s.indexOf("\n", i + 2);
      const end = nl < 0 ? s.length : nl;
      blank(i, end);
      i = end - 1;
      continue;
    }
    if (ch === '"') {
      const start = i;
      for (i++; i < s.length; i++) {
        if (s[i] === "\\" && i + 1 < s.length) i++;
        else if (s[i] === '"') break;
      }
      const end = Math.min(i + 1, s.length);
      blank(start, end);
      i = end - 1;
      continue;
    }
    if (ch === "'") {
      const escaped = s[i + 1] === "\\" && s[i + 3] === "'";
      const plain = s[i + 1] !== "\\" && s[i + 1] !== undefined && s[i + 2] === "'";
      if (escaped || plain) {
        const end = escaped ? i + 3 : i + 2;
        parts.push(s.slice(kept, i), " ".repeat(end - i + 1));
        kept = end + 1;
        i = end;
        continue;
      }
    }
  }
  parts.push(s.slice(kept));
  return parts.join("");
}
