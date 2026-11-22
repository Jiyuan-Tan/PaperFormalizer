import { describe, expect, it } from "vitest";
import { maskLeanCommentsAndStrings } from "../../src/shared/lean_mask.js";

/** The char-by-char implementation the slice-joining one replaced (2026-11-08), kept verbatim as
 *  the oracle: the rewrite only changed how the output is built, never what it is. */
function charByCharReference(s: string): string {
  let out = "";
  let depth = 0;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (depth > 0) {
      if (ch === "/" && s[i + 1] === "-") {
        depth++;
        out += "  ";
        i++;
      } else if (ch === "-" && s[i + 1] === "/") {
        depth--;
        out += "  ";
        i++;
      } else out += ch === "\n" ? "\n" : " ";
      continue;
    }
    if (ch === "/" && s[i + 1] === "-") {
      depth = 1;
      out += "  ";
      i++;
      continue;
    }
    if (ch === "-" && s[i + 1] === "-") {
      out += "  ";
      i++;
      while (i + 1 < s.length && s[i + 1] !== "\n") {
        out += " ";
        i++;
      }
      continue;
    }
    if (ch === '"') {
      out += " ";
      for (i++; i < s.length; i++) {
        const q = s[i];
        out += q === "\n" ? "\n" : " ";
        if (q === "\\" && i + 1 < s.length) {
          i++;
          out += s[i] === "\n" ? "\n" : " ";
        } else if (q === '"') break;
      }
      continue;
    }
    if (ch === "'") {
      const escaped = s[i + 1] === "\\" && s[i + 3] === "'";
      const plain = s[i + 1] !== "\\" && s[i + 1] !== undefined && s[i + 2] === "'";
      if (escaped || plain) {
        const end = escaped ? i + 3 : i + 2;
        out += " ".repeat(end - i + 1);
        i = end;
        continue;
      }
    }
    out += ch;
  }
  return out;
}

describe("maskLeanCommentsAndStrings", () => {
  it("masks comments, strings and char literals, keeping offsets and newlines", () => {
    const src = `def a := "x -- y" -- tail\n/- outer /- inner -/ still\n-/ def b := 'c' + '\\n'\n`;
    const out = maskLeanCommentsAndStrings(src);
    expect(out.length).toBe(src.length);
    expect(out).toBe(charByCharReference(src));
    expect(out.split("\n").map((l) => l.trimEnd())).toEqual(["def a :=", "", "   def b :=     +", ""]);
  });

  it("agrees with the char-by-char reference on random delimiter-dense text", () => {
    const alphabet = ["/", "-", "-", '"', "'", "\\", "\n", "\r", "a", " ", "∀", "𝔽", "/-", "-/", "--"];
    let seed = 20261108;
    const rand = (n: number) => ((seed = (seed * 1103515245 + 12345) & 0x7fffffff) % n);
    for (let t = 0; t < 4000; t++) {
      let s = "";
      for (let k = rand(40); k > 0; k--) s += alphabet[rand(alphabet.length)];
      expect(maskLeanCommentsAndStrings(s), JSON.stringify(s)).toBe(charByCharReference(s));
    }
  });
});
