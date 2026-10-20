import { describe, expect, it } from "vitest";
import { paperRenderer } from "../../src/ui/tex_html.js";

describe("named result references", () => {
  const source = String.raw`\documentclass{article}
\newtheorem{thm}{Theorem}[section]
\newtheorem{cor}[thm]{Corollary}
\newtheorem{claim}[thm]{Key Claim}
\begin{document}
See \cref{first}, \Cref{second}, \autoref{third} and Theorem~\ref{first}.
\section{Results}
\begin{thm}\label{first}A.\end{thm}
\begin{cor}\label{second}B.\end{cor}
\begin{claim}\label{third}C.\end{claim}
\begin{equation}\label{eq:x}x=y\end{equation}
See \cref{first,second}, \ref{second} and \eqref{eq:x}.
\end{document}`;
  const { paper, fragment } = paperRenderer({ files: { "m.tex": source }, main: "m.tex", aux: String.raw`\newlabel{first}{{3.7}{2}}\newlabel{second}{{3.8}{2}}\newlabel{third}{{3.9}{2}}\newlabel{eq:x}{{4}{2}}` });

  it("names forward references by their declared environment, including shared counters and custom names", () => {
    expect(paper.html).toContain('href="#lbl-first">Theorem 3.7</a>');
    expect(paper.html).toContain('href="#lbl-second">Corollary 3.8</a>');
    expect(paper.html).toContain('href="#lbl-third">Key Claim 3.9</a>');
    expect(paper.html).toContain('href="#lbl-first">Theorem 3.7</a>, <a class="ref" href="#lbl-second">Corollary 3.8</a>');
  });

  it("keeps plain references numeric and equation references parenthesized", () => {
    expect(paper.html).toContain('Theorem&nbsp;<a class="ref" href="#lbl-first">3.7</a>');
    expect(paper.html).toContain('href="#lbl-second">3.8</a>');
    expect(paper.html).toContain('href="#lbl-eq-x">(4)</a>');
    expect(paper.health.unresolvedRefs).toEqual([]);
  });

  it("uses the same names in review and message fragments", () => {
    expect(fragment(String.raw`By \Cref{first} and \autoref{second}.`).html).toContain('href="#lbl-first">Theorem 3.7</a>');
    expect(fragment(String.raw`By \cref{second}.`).html).toContain('href="#lbl-second">Corollary 3.8</a>');
  });
});
