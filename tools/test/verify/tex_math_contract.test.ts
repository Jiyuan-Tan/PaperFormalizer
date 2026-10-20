/**
 * Mathematics in author-facing text is TeX (user rule 2026-09-25): `texMathProblems` — part of every structured explanation's contract — flags any character outside
 * printable ASCII (the reply is plain ASCII; every symbol is a TeX command), plain-text mathematics
 * outside `$…$`, an unclosed delimiter, and JSON escaping slips, on the DECODED string.
 */
import { describe, expect, it } from "vitest";
import { noteProblems, texMathProblems, type OwnerExplanation } from "../../src/verify/owner_text.js";

/** The page-9 note of the live run, as the model wrote it, and in TeX. */
const PAGE9 = "A Gaussian kernel K(u) = e^(−u²/2)/√(2π) puts positive weight on points with |u| > h_0/h.";
const PAGE9_TEX = "A Gaussian kernel $K(u) = e^{-u^2/2}/\\sqrt{2\\pi}$ puts positive weight on points with $|u| > h_0/h$.";

describe("texMathProblems", () => {
  it("the page-9 text fails on its non-ASCII characters (math outside $ is the compile's to catch); its TeX form passes", () => {
    const p = texMathProblems(PAGE9, "why");
    expect(p).toHaveLength(1);
    expect(p[0]).toContain("non-ASCII character U+2212 (−), U+00B2 (²), U+221A (√), U+03C0 (π) in `why`");
    expect(p[0]).toContain("the text is plain ASCII; every symbol is a TeX command");
    expect(texMathProblems(PAGE9_TEX)).toEqual([]);
  });

  it("math inside $…$ in the paper's own macros passes; ASCII accents, dashes and reference labels are prose", () => {
    const t = "By Assumption \\ref{ass:rate_1} and the Berry--Esseen bound (P\\'olya's form), $\\E[\\hat\\tau_n] - \\tau \\lesssim \\bigO(n^{-1/2})$ and \\[ \\Var_n \\to \\sigma^2 . \\]";
    expect(texMathProblems(t)).toEqual([]);
    // The Unicode forms of the same prose are refused: the reply is plain ASCII.
    expect(texMathProblems("the Berry–Esseen bound (Pólya’s form)").join(" ")).toContain("non-ASCII character U+2013 (–), U+00F3 (ó), U+2019 (’)");
  });

  it("JSON escaping: a reply encoding \\\\lesssim decodes to \\lesssim and passes; a doubled or a lost backslash fails", () => {
    const decoded = (JSON.parse(String.raw`{"why": "$a \\lesssim b$"}`) as { why: string }).why;
    expect(decoded).toBe("$a \\lesssim b$");
    expect(texMathProblems(decoded)).toEqual([]);
    // Over-escaped: "\\\\lesssim" in the JSON decodes to two backslashes.
    const doubled = (JSON.parse(String.raw`{"why": "$a \\\\lesssim b$"}`) as { why: string }).why;
    expect(texMathProblems(doubled).join(" ")).toContain("doubled backslash");
    // inside an environment `\\\\` before a letter is a row break, not a command escaped twice (live Yang–Ding)
    expect(texMathProblems("$$\\begin{pmatrix}p_i(H_i-m_i)\\\\s_iQ_i\\delta_i\\end{pmatrix}$$")).toEqual([]);
    // Under-escaped: "\theta" and "\neq" in the JSON decode to a tab and a line break.
    const tab = (JSON.parse(String.raw`{"why": "$a \theta$"}`) as { why: string }).why;
    expect(texMathProblems(tab).join(" ")).toMatch(/control character \(U\+0009\)[^"]*before "heta"/u);
    const nl = (JSON.parse(String.raw`{"why": "$a \neq b$"}`) as { why: string }).why;
    expect(texMathProblems(nl).join(" ")).toMatch(/line break inside \$…\$[^"]*before "eq"/u);
  });

  it("a tab the printed text itself has at that place is the paper's (a source indented with tabs); one a JSON escape left is not", () => {
    const printed = "\\begin{proof}\n\tWlog we suppose $\\theta_0 = 0$.\n\\end{proof}";
    expect(texMathProblems("\tWlog we suppose $\\theta_0 = 0$. Hence the claim.", "amended proof", { reference: printed })).toEqual([]);
    // "\theta" decoded as a tab and "heta": the printed text has no tab there
    expect(texMathProblems("\tWlog we suppose $\theta_0 = 0$.", "amended proof", { reference: printed })).toEqual([
      expect.stringMatching(/^contains a control character \(U\+0009\) in `amended proof` before "heta"/),
    ]);
    // a unit of the printed text replaced: the line's indentation stays, the words after it are new
    expect(texMathProblems("\tFor standard normal data the claim holds.", "corrected_statement", { reference: printed })).toEqual([]);
    expect(texMathProblems("the bound is \tight", "corrected_statement", { reference: printed })).toEqual([expect.stringMatching(/^contains a control character/)]);
    expect(texMathProblems("\tWlog", "f")).toEqual([expect.stringMatching(/^contains a control character \(U\+0009\) in `f` before "Wlog"/)]);
  });

  it("is part of every note's contract, per field, on the decoded object", () => {
    const e = (consequence: string): OwnerExplanation => ({ claim: "The lemma claims $\\|\\ell_h\\|_2 \\ge \\tilde f h^{-1/2}$.", defects: [{ kind: "other", step_unit: "lem:a/proof/1/2", uses: null, assumed_on: null, applied_at: null, detail: "the density step uses the bound off the window" }], why: { objects: ["$K(u) = e^{-u^2/2}/\\sqrt{2\\pi}$"], consequence }, fix: "Restrict to the window.", gives_up: null });
    const p = noteProblems(e(PAGE9));
    expect(p).toHaveLength(1);
    expect(p.every((x) => x.includes("in `why.consequence`"))).toBe(true);
    expect(noteProblems(e(PAGE9_TEX))).toEqual([]);
    expect(noteProblems(JSON.parse(JSON.stringify(e(PAGE9_TEX))))).toEqual([]);
  });
});
