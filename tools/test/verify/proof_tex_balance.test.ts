// A stored statement or proof is a slice of the paper, and it must be WHOLE TeX. The live DFM run
// (2026-09-25) stored the proofs of thm::test-ci and thm::var-kurt without their closing display:
// both are written without a `proof` environment and end at a `\Box` set INSIDE the last display
// (`… = \alpha. \,\Box \end{eqnarray*}`, `$$ … (0, 1).\Box $$`), and the parser cut at the mark.
// Asserted here: the parser ends such a proof where the display closes; the balance helper; the
// transcription lint's rule (m); the parse-level check V1 refuses on; the segmenter's range check.
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { applySegments, SegmentsSchema } from "../../src/verify/segments.js";
import { closingPointAfter, openConstructsAt, texBalanceProblems } from "../../src/verify/tex_balance.js";
import { extractEnvs, isClosedAt, parseNewtheorems, type FlatTex } from "../../src/verify/tex_envs.js";
import { envBalanceProblems, nodeBalanceViolations } from "../../src/verify/transcription_lint.js";
import type { EnvsJson, TexEnv } from "../../src/verify/types.js";

const lineMapFor = (tex: string): Array<{ file: string; line: number }> => tex.split("\n").map((_l, i) => ({ file: "main.tex", line: i + 1 }));
const parse = (lines: string[]): TexEnv[] => {
  const tex = ["\\begin{document}", ...lines, "\\end{document}"].join("\n");
  return extractEnvs(tex, lineMapFor(tex), parseNewtheorems(tex)).envs;
};
const proofOf = (envs: TexEnv[], id: string): string => {
  const e = envs.find((x) => x.id === id);
  if (!e?.proof) throw new Error(`${id} has no proof`);
  return e.proof;
};

describe("texBalanceProblems", () => {
  it("accepts whole fragments and names each construct left open or closed without an opener", () => {
    expect(texBalanceProblems("Let $a = \\{1\\}$ and $$b = c.$$ Then \\[ d \\] and \\( e \\).")).toEqual([]);
    expect(texBalanceProblems("\\begin{align*} a &= b \\\\[2pt] &= c. \\end{align*}")).toEqual([]);
    expect(texBalanceProblems("costs \\$5 % an unclosed $ in a comment\nand {\\bf more}.")).toEqual([]);
    expect(texBalanceProblems("\\verb|$| is a dollar.")).toEqual([]);
    expect(texBalanceProblems("$$ \\text{if $x > 0$} $$")).toEqual([]);
    expect(texBalanceProblems("$a$$b$")).toEqual([]);
    expect(texBalanceProblems("\\begin{eqnarray*}\na &=& b. \\,")).toEqual([expect.stringMatching(/^\\begin\{eqnarray\*\} not closed by \\end\{eqnarray\*\} \(opened line 1/)]);
    expect(texBalanceProblems("we have\n$$\nx \\to y.")).toEqual([expect.stringMatching(/^\$\$ not closed by \$\$ \(opened line 2/)]);
    expect(texBalanceProblems("x = y.\n\\end{align*} Then")).toEqual([expect.stringMatching(/^\\end\{align\*\} with no opener/)]);
    expect(texBalanceProblems("\\begin{enumerate}\\item $a$\\end{itemize}")[0]).toMatch(/\\end\{itemize\} with no opener/);
    expect(texBalanceProblems("for all $\\gamma \\in \\Gamma.")).toEqual([expect.stringMatching(/^\$ not closed by \$/)]);
  });

  it("finds where the constructs open at a mark close; isClosedAt reads a `$$` display as open", () => {
    const t = "Proof. $$ a = b. \\Box $$ After.";
    const mark = t.indexOf("\\Box");
    expect(openConstructsAt(t, 0, mark).map((o) => o.kind)).toEqual(["$$"]);
    expect(closingPointAfter(t, 0, mark, t.length)).toBe(t.indexOf(" After"));
    const u = "Statement $$ a = b\n\nc $$ end";
    expect(isClosedAt(u, 0, u.indexOf("\n\n"))).toBe(false);
    expect(isClosedAt(u, 0, u.indexOf(" end"))).toBe(true);
  });
});

describe("a proof written in running text ends where its last display closes, never inside it", () => {
  const thm = "\\begin{theorem}\\label{thm:a}\nA.\n\\end{theorem}";

  it.each([
    ["a \\Box inside eqnarray* (running text)", ["\\textbf{Proof of Theorem \\ref{thm:a}:} These ingredients give us", "\\begin{eqnarray*}", "a &\\leq & \\alpha. \\,\\Box", "\\end{eqnarray*}", "", "Next paragraph, not the proof."], "\\alpha. \\,\\Box\n\\end{eqnarray*}"],
    ["a \\Box inside a $$ display (running text)", ["\\textbf{Proof of Theorem \\ref{thm:a}:} By Slutsky, we have", "$$", "\\mathcal{N}(0, 1).\\Box", "$$", "", "Next paragraph, not the proof."], "\\mathcal{N}(0, 1).\\Box\n$$"],
    ["a \\Box and $$ inside \\begin{proof}", ["\\begin{proof}", "We have", "$$ a = b.\\Box", "$$", "\\end{proof}", "Next paragraph, not the proof."], "a = b.\\Box\n$$"],
  ] as const)("%s: the proof keeps the display and its close", (_shape, body, ending) => {
    const p = proofOf(parse([thm, ...body]), "thm:a");
    expect(p.endsWith(ending)).toBe(true);
    expect(p).not.toContain("Next paragraph");
    expect(texBalanceProblems(p)).toEqual([]);
  });

  it("a mark inside a construct that never closes is cut at the mark — and reported (the V1 check then refuses it)", () => {
    const tex = ["\\begin{document}", thm, "\\textbf{Proof of Theorem \\ref{thm:a}:} We have $$ a = b. \\Box", "\\section{Next}", "\\end{document}"].join("\n");
    const { envs, warnings } = extractEnvs(tex, lineMapFor(tex), parseNewtheorems(tex));
    expect(texBalanceProblems(proofOf(envs, "thm:a"))).not.toEqual([]);
    expect(warnings).toEqual(expect.arrayContaining([expect.stringMatching(/sits inside a construct that never closes/)]));
    const envsJson = { main_file: "main.tex", files: ["main.tex"], newtheorem: {}, envs, bibliography: [] } as unknown as EnvsJson;
    expect(envBalanceProblems(envsJson, ["thm:a"])).toEqual([expect.stringMatching(/^thm:a proof \(main\.tex:5-5\): \$\$ not closed by \$\$/)]);
    expect(envBalanceProblems(envsJson, [])).toEqual([]);
  });
});

describe("rule (m): every node's text is whole TeX", () => {
  const core = (over: Partial<Core>): Core =>
    ({ qid: "q", symbols: [], assumptions: [], definitions: [], statements: [], target_estimand: "t", bibliography: [], ...over }) as unknown as Core;

  it("flags a proof cut inside its display, a condition cut before its closing $ and a slice starting at a list's \\end; passes whole texts", () => {
    const v = nodeBalanceViolations(
      core({
        statements: [{ id: "prop:test-ci", kind: "proposition", statement: "Claim $x$. [Hypotheses: ass:a]", depends_on: ["ass:a"], status: "to-prove", proof_tex: "give us\n\\begin{eqnarray*}\na &\\leq& b. \\," }],
        assumptions: [
          { id: "ass:a", condition: "for all $\\gamma\\text{ in } \\Gamma." },
          { id: "ass:b", condition: "\\end{enumerate}\nFinally suppose $\\Delta_h \\to 0$." },
        ],
      } as unknown as Partial<Core>),
    );
    expect(v).toEqual([
      expect.stringMatching(/^\(m\) prop:test-ci: `proof_tex` is not a whole TeX fragment — \\begin\{eqnarray\*\} not closed/),
      expect.stringMatching(/^\(m\) ass:a: `condition` .* \$ not closed by \$/),
      expect.stringMatching(/^\(m\) ass:b: `condition` .* \\end\{enumerate\} with no opener/),
    ]);
    expect(
      nodeBalanceViolations(
        core({
          statements: [{ id: "thm:a", kind: "theorem", statement: "Then $$a = b.$$ [Hypotheses: ass:a]", depends_on: ["ass:a"], status: "to-prove", proof_tex: "Clear.\n\\begin{align*} a &= b. \\end{align*}" }],
          assumptions: [{ id: "ass:a", condition: "\\item $a > 0$." }],
          definitions: [{ id: "def:x", name: "x", construction: "$x = \\{1\\}$" }],
        } as unknown as Partial<Core>),
      ),
    ).toEqual([]);
  });
});

describe("the segmenter's ranges hold whole TeX", () => {
  const LINES = ["\\begin{document}", "\\textsc{Theorem 1:} \\textit{If $a = 1$ then}", "$$", "b = 2.", "$$", "\\end{document}"];
  const flat: FlatTex = { text: LINES.join("\n"), lineMap: LINES.map((_l, i) => ({ file: "main.tex", line: i + 1 })), files: ["main.tex"], bibFiles: [], warnings: [] };
  const envs = { main_file: "main.tex", files: ["main.tex"], newtheorem: { theorem: "theorem" }, envs: [], bibliography: [] } as unknown as EnvsJson;

  it("a result whose lines end inside a display is a violation; the whole display is accepted", () => {
    const cut = applySegments(SegmentsSchema.parse({ results: [{ kind: "theorem", lines: [2, 4] }], bindings: [] }), envs, flat);
    expect(cut.violations).toEqual([expect.stringMatching(/^\(segment\) results\[0\]: lines \[2, 4\] cut inside TeX — \$\$ not closed by \$\$/)]);
    const whole = applySegments(SegmentsSchema.parse({ results: [{ kind: "theorem", lines: [2, 5] }], bindings: [] }), envs, flat);
    expect(whole.violations).toEqual([]);
  });
});
