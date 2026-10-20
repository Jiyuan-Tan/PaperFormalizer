import { describe, expect, it } from "vitest";
import { renderPaper } from "../../src/ui/tex_html.js";

describe("page: text commands a bibliography or a heading uses", () => {
  const page = (body: string, pre = "") => renderPaper({ files: { "m.tex": `${pre}\\title{T}\\begin{document}${body}\\end{document}` }, main: "m.tex" });
  it("letter accents, ordinals and integer sums are drawn, not listed as unknown; the paper's own definition of a name wins", () => {
    const r = page(String.raw`Ne\v{s}et\v ril and Fran\c{c}ois; the \nth{\intcalcSub{2020}{1983}} ICML, the \nth{2} and \nth{13} and \nth{23}; NeurIPS \intcalcSub{2020}{1987}. \part*{\Large Appendix} \shortstack{Random \\ geometric} \localtableofcontents \etocsettocstyle{a}{b}`);
    expect(r.health.unknownCommands).toEqual({});
    const text = r.html.replace(/<[^>]+>/g, "");
    expect(text).toContain("Nešetřil and François; the 37th ICML, the 2nd and 13th and 23rd; NeurIPS 33.");
    expect(r.html).toMatch(/<h2 class="part">\s*Appendix<\/h2>/);
    expect(text).toContain("Random");
    expect(text).not.toMatch(/\{a\}|\bab\b/);
    // a note quoting an algorithm2e step
    const q = page(String.raw`the step \For{$i = 1$}{ set $z$ } and \If{$a$}{ stop }`);
    expect(q.health.unknownCommands).toEqual({});
    expect(q.html.replace(/<[^>]+>/g, "").replace(/\s+/g, " ")).toContain("the step for i=1 do set z and if a then stop");
    // plain TeX's line break inside a sentence
    const br = page(String.raw`functions $\chi_n$ and \break $\chi_{n-1}$ is, e.g.\@ here`);
    expect(br.health.unknownCommands).toEqual({});
    // a figure's label substitutions and the page numbering: no text of their own
    const fig = page(String.raw`\pagenumbering{arabic}A \psfrag{r_s}[l][c]{\textcolor{blue}{$r_s = 1$}}\psfrag{f}{$f$} B`);
    expect(fig.health.unknownCommands).toEqual({});
    expect(fig.html.replace(/<[^>]+>/g, "").replace(/\s+/g, " ").trim()).toBe("A B");
    // a longtable shows its first head once: the head repeated on later pages and the running foot are left out
    const lt = page(String.raw`\begin{longtable}{ll}
H1 & H2 \\ \hline
\endfirsthead
\multicolumn{2}{c}{{\bfseries \tablename\ \thetable{} -- continued from previous page}} \\
H1 & H2 \\
\endhead
\multicolumn{2}{r}{continued on next page} \\
\endfoot
\endlastfoot
a & b \\
\end{longtable}`);
    expect(lt.health.unknownCommands).toEqual({});
    const ltText = lt.html.replace(/<[^>]+>/g, " ").replace(/\s+/g, " ").trim();
    expect(ltText).toBe("H1 H2 a b");
    // an \iffalse block is not typeset: a reference in it to a label the paper dropped is no unresolved reference
    const off = page(String.raw`kept \iffalse \subsection{Proof of \ref{thm:gone}} dead \fi after`);
    expect(off.health.unresolvedRefs).toEqual([]);
    expect(off.html.replace(/<[^>]+>/g, "").replace(/\s+/g, " ").trim()).toBe("kept after");
    const own = page(String.raw`a \v{x} b`, String.raw`\newcommand{\v}[1]{vec #1}`);
    expect(own.html.replace(/<[^>]+>/g, "")).toContain("a vec x b");
  });
});
