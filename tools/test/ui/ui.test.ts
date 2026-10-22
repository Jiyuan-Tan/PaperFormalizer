import { appendFileSync, existsSync, mkdtempSync, mkdirSync, readdirSync, rmSync, statSync, symlinkSync, utimesSync, writeFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { type ChildProcess, spawn, spawnSync } from "node:child_process";
import os, { tmpdir } from "node:os";
import path from "node:path";
import { afterAll, describe, expect, it } from "vitest";
import { buildArgv, displayCommand, setDecisions } from "../../src/ui/actions.js";
import { paperNames, paperUses, parseModule } from "../../src/ui/library_model.js";
import { texCut, closedProofs, liveHeadline, markStarted, ownerReadingsByComment, redoingOf, repairKey, runDetail, newerRuns, runLive, runSummary, stageIndexOf, validSlug } from "../../src/ui/run_model.js";
import { gunzipSync } from "node:zlib";
import { readFileSync } from "node:fs";
import { brotliDecompressSync } from "node:zlib";
import { authorNames, expandDelimited, frontMatter, inlineInputs, katexMacros, paperRenderer, readAux, readPreamble, renderPaper, sentenceGroups, sentencePart, statementParts, texSentences, tikzPictures, tikzSetup } from "../../src/ui/tex_html.js";
import { displayWhole, partAlone, segmentStatement } from "../../src/formalization/nl_links.js";
import http from "node:http";
import { MESSAGE_LIMITS, safeUploadName, startUiServer, type UiServer } from "../../src/ui/server.js";
import { runningUi, writeUiState } from "../../src/ui/cli.js";
import { ChangeWatcher } from "../../src/ui/watch.js";
import { derive, deriveRead } from "../../src/ui/fscache.js";
import { parseChecklist } from "../../src/proposals/checklist.js";
import type { ProposalBatch } from "../../src/proposals/schema.js";
import type { ToolkitConfig } from "../../src/toolkit/config.js";
import { paperUrl, shareWarning, SHARE_SIGN_IN } from "../../src/verify/share.js";
import { fakeService, finishedRun, SERVICE, tmpDirs } from "../verify/share_fake.js";

const PAPER = String.raw`\documentclass{article}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}
\def\ybars{\bar{y}_{\text{S}}}
\title{A Paper \thanks{Funded.}}
\author{Ann Author \and Bo Writer}
\begin{document}
\maketitle
\section{Intro}\label{sec:intro}
See Theorem~\ref{thm:a} and \citet{hajek}. <script>alert(1)</script>
\begin{theorem}\label{thm:a}
If $x \ge 0$ then $\ybars \le 1$.\vsOriginal{the printed text}\vsCorrected{the corrected text}\vsNote{What is wrong: $x$.}
\end{theorem}
\begin{lemma}[Key]
Plain.
\end{lemma}
\begin{align}\label{eq:1} a &= b \end{align}
\input{part}
\end{document}`;
const AUX = String.raw`\newlabel{thm:a}{{7}{3}}
\newlabel{eq:1}{{2.1}{3}}
\bibcite{hajek}{{1}{1960}{{H\'ajek}}{{}}}`;

describe("tex_html: the paper page renderer", () => {
  it("a \\cref to a section or an appendix reads with its name, as cleveref's options print it", () => {
    const body = String.raw`\begin{document}\section{Intro}\label{sec:a}See \cref{sec:a}, \Cref{sec:b} and \cref{app:c}.\section{Model}\label{sec:b}x\appendix\section{Proofs}\label{app:c}y\end{document}`;
    const text = (pre: string) => renderPaper({ files: { "m.tex": pre + body }, main: "m.tex" }).html.replace(/<[^>]+>/g, "");
    expect(text(String.raw`\usepackage[capitalize,noabbrev]{cleveref}`)).toContain("See Section 1, Section 2 and Appendix A.");
    expect(text(String.raw`\usepackage{cleveref}`)).toContain("See section 1, Section 2 and appendix A.");
  });
  it("a \\cref inside math reads with its name, as outside math", () => {
    const tex = String.raw`\newtheorem{assumption}{Assumption}\begin{document}\begin{assumption}\label{asp:a}X.\end{assumption}
Then $y \le 1 \text{ by \cref{asp:a}}$ and $z \text{ by \ref{asp:a}}$.\end{document}`;
    const text = renderPaper({ files: { "m.tex": tex }, main: "m.tex" }).html.replace(/<span class="katex-mathml">[^]*?<\/span>/g, "").replace(/<[^>]+>/g, "");
    expect(text).toMatch(/by\sAssumption\s1(?!\d)/u);
    expect(text).toMatch(/by\s1(?!\d)/u);
  });
  const r = renderPaper({ files: { "main.tex": PAPER, "part.tex": String.raw`\subsection{Inputted}Text from a second file.` }, main: "main.tex", aux: AUX });
  it("reads title, authors (without \\thanks), sections and the numbering in the .aux", () => {
    expect(r.title).toBe("A Paper");
    expect(r.authors).toContain("Ann Author");
    expect(r.toc.map((t) => t.text)).toEqual(["1 Intro", "1.1 Inputted"]);
    expect(r.envs.map((e) => e.heading)).toEqual(["Theorem 7", "Lemma 2"]);
    expect(r.html).toContain(">7</a>");
    expect(r.html).toContain("(2.1)");
    expect(r.html).toContain("Text from a second file.");
  });
  it("a corollary a repair splits off a result is a block of its own after it, carrying its node: its anchor, its statement and its proof under the page's proof heading", () => {
    const tex = String.raw`\begin{document}\begin{theorem}\label{thm:a}X.\vsCorrected{Y.}\end{theorem}
\vsCorollary{thm:cor-fix-0a1b2c3d}{Theorem~\ref{thm:a}}{\textbf{the Gaussian case.} If $x$ is Gaussian, $y \le 1$. \vsLine\textit{Proof.} By Theorem~\ref{thm:a}.}
\vsProposedCorollary{thm:cor-fix-11111111}{the result above}{Z.}\end{document}`;
    const p = renderPaper({ files: { "m.tex": tex }, main: "m.tex", aux: String.raw`\newlabel{thm:a}{{7}{3}}` });
    expect(p.anchors).toMatchObject({ "thm:cor-fix-0a1b2c3d": "res-thm-cor-fix-0a1b2c3d", "thm:cor-fix-11111111": "res-thm-cor-fix-11111111" });
    const at = p.html.indexOf('<div class="rv ins cor formal k-corollary" tabindex="0" data-res="thm:cor-fix-0a1b2c3d"');
    expect(at).toBeGreaterThan(p.html.indexOf('class="rv ins"'));
    const block = p.html.slice(at, p.html.indexOf('<div class="rv ins cor pending formal'));
    expect(block).toContain('<span class="res-anchor" id="res-thm-cor-fix-0a1b2c3d" data-node="thm:cor-fix-0a1b2c3d"></span>');
    // headed like a printed result; the review's word on it is the small tag
    expect(block).toMatch(/<span class="env">Corollary 7\.1\.<\/span> <span class="rv-tag">Added by the revision<\/span>/);
    expect(block).toContain("the Gaussian case.");
    // its proof is headed and closed like a proof of the paper, inside the block
    expect(block).toMatch(/<div class="proof"><span class="env">Proof\.<\/span> By Theorem.*<span class="qed">∎<\/span><\/div><\/div>\s*$/s);
    expect(block).not.toContain("Why it follows");
    expect(p.html).toMatch(/<div class="rv ins cor pending formal k-corollary" tabindex="0" data-res="thm:cor-fix-11111111"[^>]*>.*<span class="env">Corollary 1 of the result above\.<\/span> <span class="rv-tag">Proposed — awaiting a ruling<\/span>/);
    // a block of its own: the parent's corrected text stays the one corrected block of its environment
    expect(block).not.toContain('class="rv ins"');
    expect(p.marks).toBe(3);
  });
  // The finding: `\mathbbm{1}` (the bbm package's indicator), and a paper macro defined through it, printed as source.
  it("sets \\mathbbm and \\mathds, which the math renderer lacks, as blackboard bold", () => {
    const r = renderPaper({ files: { "m.tex": String.raw`\newcommand{\1}{\mathbbm{1}}\begin{document}Let $\sigma = 2\1\{a \in S\} - 1$ and $\mathds{R}$.\end{document}` }, main: "m.tex" });
    expect(r.html).toContain("katex");
    expect(r.html).not.toContain("mathbbm");
  });
  it("a corrected step's detail (\\vsDetail) is a side note beside the step, not text of the step", () => {
    const r = renderPaper({ files: { "m.tex": String.raw`\begin{document}\begin{proof}\vsCorrectedStep{As in the proof of Lemma 1, with $g$ for $f$.\vsDetail{There $f \le c$ was used only through $\|f\|_\infty$; $\|g\|_\infty \le c$ too.}}\end{proof}\end{document}` }, main: "m.tex" });
    expect(r.comments).toHaveLength(1);
    expect(r.comments[0]).toMatchObject({ kind: "detail", label: "Proof detail" });
    expect(r.html).toContain('class="cmark k-detail"');
    expect(r.html).toContain('title="proof detail"');
    expect(r.html.replace(/<[^>]+>/g, "")).not.toContain("was used only through");
  });
  it("renders math with the paper's macros, escapes text, and turns annotations into marks and a comment", () => {
    expect(r.html).toContain("katex");
    expect(r.html).not.toContain("katex-error");
    expect(r.html).not.toContain("<script>");
    expect(r.html).toContain("&lt;script&gt;");
    expect(r.marks).toBe(2);
    expect(r.html).toContain('class="rv del"');
    expect(r.html).toContain('class="rv ins"');
    expect(r.comments).toHaveLength(1);
    expect(r.comments[0]).toMatchObject({ kind: "note", env: "thm:a" });
    expect(r.html).toContain(`data-c="${r.comments[0].id}"`);
    expect(r.macros["\\ybars"]).toBe("\\bar{y}_{\\text{S}}");
    // a mark says what it is: only a reading's is a clarification
    const marks = renderPaper({ files: { "m.tex": String.raw`\begin{document}A.\vsNote{n}\vsRewind{r}\vsCap{c}\vsReading{x}\vsReadingOwner{y}\vsReadingSymbol{$a$}{z}\end{document}` }, main: "m.tex" }).html;
    expect([...marks.matchAll(/class="cmark k-([\w-]+)" data-c="c\d" title="([^"]*)"/g)].map((m) => [m[1], m[2]])).toEqual([
      ["note", "PaperFormalizer comment"], ["rewind", "PaperFormalizer comment"], ["cap", "PaperFormalizer comment"],
      ["reading", "clarification"], ["reading-owner", "clarification"], ["reading-symbol", "clarification"],
    ]);
  });
  it("two notes of one kind, environment and text have different keys: an issue reported on one is not the other's", () => {
    const c = renderPaper({ files: { "m.tex": String.raw`\begin{document}A.\vsReading{same text}B.\vsReading{same text}C.\vsReading{other}\vsReading{same text}\end{document}` }, main: "m.tex" }).comments;
    expect(new Set(c.map((x) => x.key)).size).toBe(4);
    expect(c[1]!.key).toBe(`${c[0]!.key}-2`);
    expect(c[3]!.key).toBe(`${c[0]!.key}-3`);
  });
  it("falls back to the run's environment kinds for class-defined theorems", () => {
    const p = renderPaper({ files: { "m.tex": String.raw`\begin{document}\begin{thm}\label{t}X\end{thm}\end{document}` }, main: "m.tex", theoremKinds: { thm: "theorem" } });
    expect(p.envs[0].heading).toBe("Theorem 1");
  });
  it("reads Windows line endings like Unix ones", () => {
    const p = renderPaper({ files: { "m.tex": "\\begin{document}\r\nOne.\r\n\r\nTwo.\r\n\\end{document}" }, main: "m.tex" });
    expect((p.html.match(/class="p"/g) ?? []).length).toBe(2);
    expect(parseModule("namespace N\r\n\r\n/-- D. -/\r\ndef f : ℕ := 0\r\n")[0]?.name).toBe("N.f");
  });
  it("gives the contents and result names as plain text (no entity shown twice escaped)", () => {
    const p = renderPaper({ files: { "m.tex": String.raw`\newtheorem{ass}{Assumption~A}\begin{document}\section{The "Tudor" Solution~A \& B}\begin{ass}X\end{ass}\end{document}` }, main: "m.tex" });
    expect(p.toc[0]!.text).toBe('1 The "Tudor" Solution\u00a0A & B');
    expect(p.envs[0]!.heading).toBe("Assumption A 1");
  });
  it("keeps a note set off between paragraphs from standing as an empty line of its own", () => {
    const p = renderPaper({ files: { "m.tex": String.raw`\begin{document}\section{S}One $x$.

\vsReadingSymbol{$x$}{Read $x$ as a real.}

\vsReading{Another.}

Two.
\[ y \]

\vsNote{After a display.}

Three.\end{document}` }, main: "m.tex" });
    expect(p.comments).toHaveLength(3);
    expect(p.html).not.toMatch(/<div class="p">\s*<span class="cmark/);
    expect(p.html).toMatch(/One <span class="katex[\s\S]*?\.<span class="cmark[^>]*><\/span>\s*<span class="cmark[^>]*><\/span><\/div>/);
    expect(p.html).toMatch(/<div class="p marks"><span class="cmark k-note"/);
  });
  it("renders an array preamble with @{} (the annotator's stacked display) in KaTeX", () => {
    const p = renderPaper({ files: { "m.tex": String.raw`\begin{document}\vsNote{$\begin{array}{@{}c@{}}\displaystyle a \\ \displaystyle b\end{array}$}\end{document}` }, main: "m.tex" });
    expect(p.comments[0]!.html).toContain("katex");
    expect(p.comments[0]!.html).not.toContain("katex-error");
  });
  it("reads author names only: no affiliations, marks, emails or \\and", () => {
    expect(authorNames(String.raw`Shu Yang$^{*1}$ and Peng Ding$^{*2}$\\ $^{*1}$Department of Statistics, NC State`)).toBe("Shu Yang and Peng Ding");
    expect(authorNames(String.raw`Victor Chernozhukov \\ MIT Economics \\ \texttt{vchern@mit.edu} \And Whitney K. Newey \\ MIT`)).toBe("Victor Chernozhukov, Whitney K. Newey");
    expect(authorNames(String.raw`Pedro H. C. Sant'Anna\thanks{Vanderbilt.} \\ Vanderbilt University \and Jun B. Zhao`)).toBe("Pedro H. C. Sant'Anna, Jun B. Zhao");
  });
  it("finds a title set by hand (no \\title) with its names, and shows that block once", () => {
    const src = String.raw`\newcommand{\blinding}[2]{#1}\begin{document}\begin{center}
{\Large Balancing Covariates via Weighting}

\medskip
\blinding{
Fan Li \quad \quad Kari Lock Morgan \quad \quad Alan M. Zaslavsky
\footnote{Fan Li is professor (email: fli@duke.edu).}
}{}
\end{center}
{\centerline{ABSTRACT} Covariate balance.}\end{document}`;
    expect(frontMatter(src)).toMatchObject({ title: "Balancing Covariates via Weighting", authors: "Fan Li, Kari Lock Morgan, Alan M. Zaslavsky" });
    // a journal class with the commands in capitals (INFORMS): the run's name was shown for the title
    expect(frontMatter(String.raw`\RUNTITLE{Always Valid} \TITLE{Always Valid Inference: Continuous Monitoring} \ARTICLEAUTHORS{\AUTHOR{Ann Lee\thanks{x}} \AFF{Stanford} \AUTHOR{Bo Wu}}`)).toMatchObject({ title: "Always Valid Inference: Continuous Monitoring", authors: "Ann Lee, Bo Wu" });
    const p = renderPaper({ files: { "m.tex": src }, main: "m.tex" });
    expect(p.title).toBe("Balancing Covariates via Weighting");
    expect(p.html).not.toContain("Balancing Covariates");
  });
  it("keeps the branch of a journal template's blind switch that holds", () => {
    const src = String.raw`\newcommand{\blind}{0}\begin{document}\if0\blind {\title{Real Title}\author{A Author}\maketitle} \fi
\if1\blind {\begin{center}{\LARGE Blind Title}\end{center}} \fi
Body.\end{document}`;
    const p = renderPaper({ files: { "m.tex": src }, main: "m.tex" });
    expect(p.title).toBe("Real Title");
    expect(p.html).not.toContain("Blind Title");
    expect(p.html.replace(/<[^>]+>/g, "")).not.toMatch(/\b[01]\b/);
  });
  it("renders \\mbox and a reference inside math (KaTeX has neither)", () => {
    const p = renderPaper({ files: { "m.tex": String.raw`\begin{document}\begin{equation}\label{e}x\end{equation}$a\mbox{ for all } b \text{ in (\ref{e})}$\end{document}` }, main: "m.tex" });
    expect(p.html).not.toContain("#cc0000");
    const text = p.html.replace(/<[^>]+>/g, "|").replace(/&nbsp;|\u00a0/g, " ").replace(/\|+/g, "|");
    expect(text).toContain("for all");
    expect(text).toContain("in (1)");
  });
  it("draws math with KaTeX, then MathJax; records what neither reads, and takes the agent's override", () => {
    const src = String.raw`\def\ybar{\bar{y}}\begin{document}\section{S}$\ybar$ and $\cancelto{0}{x}$ and $\zzundefined x$.\end{document}`;
    const p = renderPaper({ files: { "m.tex": src }, main: "m.tex" });
    expect(p.health.mathFallbacks).toBe(1);
    expect(p.html).toContain("mjx-container");
    expect(p.health.mathFailures).toEqual([expect.objectContaining({ tex: "\\zzundefined x", near: "1 S" })]);
    expect(p.health.mathErrors).toBe(1);
    expect(p.html).toContain('class="tex-raw"');
    // drawn again (the formulas now come from the process's cache): the same page, the same counts
    const again = renderPaper({ files: { "m.tex": src }, main: "m.tex" });
    expect([again.html, again.health.mathFallbacks, again.health.mathFailures]).toEqual([p.html, 1, p.health.mathFailures]);
    const fixed = renderPaper({ files: { "m.tex": src }, main: "m.tex", mathOverrides: { "\\zzundefined x": "z x" } });
    expect(fixed.health.mathFailures).toEqual([]);
    expect(fixed.html).not.toContain("tex-raw");
  });
  it("lets no paper TeX write links, styles or classes into the page through the MathJax fallback", () => {
    // \enclose sends each formula to MathJax (KaTeX refuses it)
    const p = renderPaper({ files: { "m.tex": String.raw`\begin{document}$\href{javascript:alert(1)}{x}\enclose{circle}{y}$ $\style{position:fixed;inset:0}{z}\enclose{box}{w}$ $\bbox[position:fixed]{v}\enclose{box}{u}$ $\class{x}{t}\enclose{box}{s}$\end{document}` }, main: "m.tex" });
    // shown as escaped source at most, never as an attribute
    expect(p.html).not.toMatch(/href="javascript:|style="[^"]*position:\s*fixed|class="x"/);
    expect(p.health.mathFailures).toHaveLength(4);
  });
  it("renders the run records' TeX under the paper's macros and numbering", () => {
    const { fragment } = paperRenderer({ files: { "m.tex": String.raw`\def\ybar{\bar{y}}\begin{document}\begin{equation}\label{e}x\end{equation}\end{document}` }, main: "m.tex" });
    const ok = fragment(String.raw`By \eqref{e}, $\ybar \ge 0$ holds \emph{always}.`);
    expect(ok.html).toContain("(1)");
    expect(ok.html).toContain("<em>");
    expect(ok.html).toContain("katex");
    expect(ok.failures).toEqual([]);
    expect(fragment("$\\zzundefined$").failures).toHaveLength(1);
  });
  it("draws a correction's kept label (\\vsLabel) as nothing, in a display and in text", () => {
    const { fragment } = paperRenderer({ files: { "m.tex": String.raw`\begin{document}x\end{document}` }, main: "m.tex" });
    const r = fragment(String.raw`Then \vsLabel{eq:t} \begin{equation}\vsLabel{eq:a} x=1 \end{equation}`);
    expect(r.failures).toEqual([]);
    expect(r.html).not.toContain("vsLabel");
    expect(r.html).not.toContain("eq:a");
  });
  it("anchors a prose result whose line the annotated copy marked up after its first words", () => {
    const annotated = String.raw`\begin{document}Intro.

\textbf{Theorem 2.} \vsOriginal{\emph{As $n\to\infty$ the variance shrinks.}}\vsClarified{\emph{Under (A), it shrinks.}}
\end{document}`;
    const p = renderPaper({ files: { "m.tex": annotated }, main: "m.tex", anchors: [{ node: "thm:variance", file: "m.tex", line: String.raw`\textbf{Theorem 2.} \emph{As $n\to\infty$ the variance shrinks.}` }] });
    expect(p.anchors["thm:variance"]).toBeDefined();
  });
  it("anchors a condition at its own text, before the formula when that text starts inside one", () => {
    const src = String.raw`\begin{document}First. Assume no ties among the ranks. Then
\[
 a = b,\quad c = d
\]
holds.\end{document}`;
    const p = renderPaper({ files: { "m.tex": src }, main: "m.tex", anchors: [{ node: "ass:no-ties", file: "m.tex", line: "Assume no ties among the ranks." }, { node: "def:ab", file: "m.tex", line: String.raw` a = b,\quad c = d` }] });
    expect(p.html).toContain(`First. <span class="res-anchor" id="res-ass-no-ties" data-node="ass:no-ties"></span>Assume no ties`);
    expect(p.html).toContain(`<div class="eq"><span class="res-anchor" id="res-def-ab" data-node="def:ab"></span><span class="katex`);
    expect(p.anchors).toEqual({ "ass:no-ties": "res-ass-no-ties", "def:ab": "res-def-ab" });
    expect(p.health.mathFailures).toEqual([]);
  });
  // The finding this guards: a result's first source line began inside a `\ref` broken across
  // lines, the anchor went into its key, and the page printed "??thm:…ass:…" where the number stands.
  it("never anchors inside a command broken across lines: the reference keeps its key and its number", () => {
    const src = (tail: string) => String.raw`\newtheorem{corollary}{Corollary}\newtheorem{assumption}{Assumption}\begin{document}
\begin{assumption}\label{ass:a}One.\end{assumption}
\begin{assumption}\label{ass:c}Three.\end{assumption}
\begin{corollary}
\label{cor:v} Let Assumptions \ref{ass:a}-${tail} hold, and assume that $T$ is independent.
\end{corollary}
\end{document}`;
    const fragmentOf = String.raw`Let Assumptions \ref{ass:a}-\ref{ass:c} hold,`;
    for (const [tail, line] of [["\\ref%\n{ass:c}", "{ass:c} hold, and assume that $T$ is independent."], ["\\ref{%\nass:c}", "ass:c} hold, and assume that $T$ is independent."]]) {
      const { paper, fragment } = paperRenderer({ files: { "m.tex": src(tail!) }, main: "m.tex", anchors: [{ node: "thm:cor-v", file: "m.tex", line: line! }] });
      const text = (html: string) => html.replace(/<[^>]+>/g, "").replace(/\s+/g, " ");
      expect(text(paper.html), tail).toContain("Let Assumptions 1-2 hold, and assume");
      expect(paper.html, tail).not.toMatch(/\?\?|thm:cor-v[^"]/);
      expect(paper.health.unresolvedRefs, tail).toEqual([]);
      expect(paper.anchors["thm:cor-v"], tail).toBe("res-thm-cor-v");
      // the page and a fragment of the same statement read alike: a phrase of it is found on the page
      expect(text(paper.html), tail).toContain(text(fragment(fragmentOf).html).trim());
    }
  });
  // What the page relies on to light ONE condition of a display that holds several: a part,
  // rendered as the formula it is by itself (`partAlone`), is a run of the display's text on the
  // page — so the part can be boxed where it stands — or, for the rows of an aligned display (drawn
  // column by column), it is not, and the display whole (`displayWhole`) is.
  it("a part of a displayed formula, rendered alone, stands in the page's text for that formula — a row of an aligned display does not", () => {
    const statement = String.raw`Suppose \[ E[Y^2 \mid W ]\leq \bar{\sigma}^2,\quad \|\alpha_0\|_{\infty}\leq\bar{\alpha},\quad \|\hat\alpha\|_\infty\leq\bar\alpha'. \] and
\begin{align} x &= y \label{eq:x} \\ u &\leq v \end{align}
hold.`;
    const { paper, fragment } = paperRenderer({ files: { "m.tex": String.raw`\newtheorem{theorem}{Theorem}\begin{document}\begin{theorem}\label{t}` + statement + String.raw`\end{theorem}\end{document}` }, main: "m.tex" });
    const seen = (html: string) => html.replace(/<span class="katex-mathml">[\s\S]*?<\/span>(?=<span class="katex-html")/g, "").replace(/<[^>]+>/g, "").replace(/\s+/g, "");
    const page = seen(paper.html);
    const segs = segmentStatement(statement);
    expect(segs.map((s) => s.display ?? "-")).toEqual(["s1", "s1", "s1", "s4", "s4", "-"]);
    expect(segs.slice(0, 5).map(partAlone)).toEqual([
      String.raw`Suppose \[ E[Y^2 \mid W ]\leq \bar{\sigma}^2,\quad\]`, String.raw`\[ \|\alpha_0\|_{\infty}\leq\bar{\alpha},\quad\]`, String.raw`\[ \|\hat\alpha\|_\infty\leq\bar\alpha'. \]`,
      " and\n" + String.raw`\[ x  = y  \]`, String.raw`\[ u  \leq v \]`,
    ]);
    // a part as the fragment it is: no renderer reads it as mathematics
    expect(page).not.toContain(seen(fragment(segs[1]!.text).html));
    // the three conditions of the first display: each found, in order, one after the other
    const alone = segs.slice(0, 3).map((s) => seen(fragment(partAlone(s)).html));
    expect(alone).toEqual(["SupposeE[Y2∣W]≤σˉ2,", "∥α0​∥∞​≤αˉ,", "∥α^∥∞​≤αˉ′."]);
    const at = alone.map((t) => page.indexOf(t));
    expect(at.every((i) => i >= 0) && at[0]! < at[1]! && at[1]! < at[2]!).toBe(true);
    // the rows of the aligned display: not runs of its text; the display whole — its numbers apart — is
    expect(segs.slice(3, 5).map((s) => page.includes(seen(fragment(partAlone(s)).html)))).toEqual([false, false]);
    const whole = displayWhole(segs.slice(3, 5));
    expect(whole).toBe(" and\n" + String.raw`\begin{align*} x &= y  \\ u &\leq v \end{align*}`);
    expect(page).toContain(seen(fragment(whole).html));
  });
  it("finds the note stating a pinned reading by the reading's text, under the result it is pinned on", () => {
    const uniform = "The implied constants are\nuniform.";
    const src = String.raw`\begin{document}\begin{theorem}\label{t1}A.\end{theorem}\vsReading{The implied constants are uniform.}
\begin{lemma}\label{l1}B.\end{lemma}\vsReadingOwner{The implied constants are uniform. (the reading of one of its hypotheses)}\vsReading{The implied constants are uniform over $n$.}\vsNote{The implied constants are uniform.}\end{document}`;
    const p = renderPaper({ files: { "m.tex": src }, main: "m.tex", readings: [
      { node: "ass:pin-1", text: uniform, labels: ["t1"] }, { node: "ass:pin-2", text: uniform, labels: ["l1"] },
      { node: "ass:pin-3", text: "The implied constants are uniform over $n$.", labels: [] }, { node: "ass:pin-4", text: "Never noted.", labels: ["t1"] },
    ] });
    expect(p.comments.map((c) => [c.id, c.kind, c.env])).toEqual([["c1", "reading", "t1"], ["c2", "reading-owner", "l1"], ["c3", "reading", "l1"], ["c4", "note", "l1"]]);
    // the longest text that opens the note; a reading pinned elsewhere, or only found in a finding's note, is not it
    expect(p.readings).toEqual({ "ass:pin-1": "c1", "ass:pin-2": "c2", "ass:pin-3": "c3" });
    expect(renderPaper({ files: { "m.tex": src }, main: "m.tex" }).readings).toEqual({});
  });
  it("renders pseudocode floats (algpseudocode, algorithmic, algorithm2e) as numbered, captioned lines", () => {
    // every formula as "M" (spans counted, so a nested one is removed whole), then the text between tags
    const noMath = (h: string) => {
      let out = "";
      for (let i = 0; i < h.length;) {
        if (!h.startsWith('<span class="katex">', i)) { out += h[i++]; continue; }
        let d = 0, j = i;
        for (; j < h.length; j++) { if (h.startsWith("<span", j)) d++; else if (h.startsWith("</span>", j) && --d === 0) break; }
        out += "M"; i = j + "</span>".length;
      }
      return out;
    };
    const text = (h: string) => noMath(h).replace(/<[^>]+>/g, "|").replace(/&nbsp;|\u200b|\s+/g, " ").replace(/\s*\|[\s|]*/g, "|");
    const alg = renderPaper({ files: { "m.tex": String.raw`\begin{document}\begin{algorithm}\caption{Cross-fitting}\label{alg:cf}
\begin{algorithmic}[1]
\Require data $W$
\For{$k = 1, \dots, K$} \Comment{each fold}
  \State fit $\hat\gamma_{-k}$ \Comment{on the other folds}
  \If{$k > 1$} \State $\theta \gets \theta + 1$ \Else \State $\theta \gets 0$ \EndIf
\EndFor
\State \Return $\hat\theta$
\end{algorithmic}\end{algorithm}
See Algorithm~\ref{alg:cf}.\end{document}` }, main: "m.tex" });
    expect(alg.health.unknownCommands).toEqual({});
    expect(alg.html).toContain('<figure class="alg" id="alg-1">');
    // a requirement is unnumbered and a comment closes the line it follows, as algorithmicx prints them
    expect(text(alg.html)).toContain("|Algorithm 1.|Cross-fitting|Require:|data M|1|for|M|do|▷ each fold|2|fit M|▷ on the other folds|3|if|M|then|4|M|5|else|6|M|7|end if|8|end for|9|return|M|See Algorithm|1|");
    // the body of the inner if sits two levels in
    expect(alg.html).toMatch(/--lvl:2"><span class="ln">4</);
    const old = renderPaper({ files: { "m.tex": String.raw`\begin{document}\begin{algorithm}\caption{Old}\begin{algorithmic}\REQUIRE $x$ \FOR{$i=1$ to $n$} \STATE $y$ \ENDFOR \RETURN $y$\end{algorithmic}\end{algorithm}\end{document}` }, main: "m.tex" });
    expect(old.health.unknownCommands).toEqual({});
    expect(text(old.html)).toContain("|Require:|M|for|M to M|do|M|end for|return|M|");
    const a2e = renderPaper({ files: { "m.tex": String.raw`\begin{document}\begin{algorithm}[H]\SetAlgoLined\SetKwProg{Fn}{Function}{ is}{end}\SetKwFunction{Grad}{Grad}\KwIn{$x$}\KwOut{$y$}
$y \leftarrow 0$\; $z \leftarrow a\;b$\;
\For(\tcc{the main loop}){$i \leftarrow 1$ \KwTo $n$}{ $y \leftarrow y + \Grad{x_i}$\; \tcp{accumulate} \lIf{$y > 9$}{\Return $y$\;} }
\eIf{$y > 0$}{\Return $y$\;}{\Return $0$\;}
\caption{Sum}\end{algorithm}\end{document}` }, main: "m.tex" });
    expect(a2e.health.unknownCommands).toEqual({});
    // setup commands leave nothing behind; a thin space inside math does not end a statement; a block's
    // comment in parentheses joins its head; a one-line \lIf is one line
    expect(text(a2e.html)).toContain("|Algorithm 1.|Sum|Input:|M|Output:|M|M|M|for|M|to|M|do|▷ the main loop|M|▷ accumulate|if|M|then|return|M|if|M|then|return|M|else|return|M|");
    expect(text(a2e.html)).not.toMatch(/ is|end\|/);
  });
  it("draws a float as pseudocode even when the run's environment map lists `algorithm`", () => {
    const p = renderPaper({ files: { "m.tex": String.raw`\begin{document}\begin{algorithm}[H]\caption{GD}\begin{algorithmic}\State $x$\end{algorithmic}\end{algorithm}\end{document}` }, main: "m.tex", theoremKinds: { algorithm: "other", algorithmic: "other" } });
    expect(p.html).toContain('<figure class="alg"');
    expect(p.html).not.toContain("(H)");
  });
  it("keeps a paper's own theorem-like algorithm a result block", () => {
    const p = renderPaper({ files: { "m.tex": String.raw`\newtheorem{algorithm}{Algorithm}\begin{document}\begin{algorithm}[DML]\label{alg:t}Estimate $\theta$.\end{algorithm}\end{document}` }, main: "m.tex" });
    expect(p.envs[0]).toMatchObject({ label: "alg:t", heading: "Algorithm 1" });
    expect(p.html).toContain('class="formal k-algorithm"');
    expect(p.html).not.toContain('figure class="alg"');
  });
  it("pieces: \\input inlining, aux citations, preamble macros", () => {
    expect(inlineInputs({ "a.tex": "x\\input{b} % c", "b.tex": "y" }, "a.tex")).toBe("xy ");
    expect(readAux(AUX).cites.hajek).toMatchObject({ year: "1960" });
    expect(readPreamble(String.raw`\newcommand{\E}[1]{\mathbb{E}[#1]}\DeclareMathOperator{\Var}{Var}`).macros).toMatchObject({ "\\E": "\\mathbb{E}[#1]", "\\Var": "\\operatorname{Var}" });
    // a control symbol (one non-letter character) is a name too: `\def\1{\mathbf{1}}` (live: HodgeRank)
    expect(readPreamble(String.raw`\def\1{\mathbf{1}}\def\foo{x}`).macros).toMatchObject({ "\\1": "\\mathbf{1}", "\\foo": "x" });
    // the LaTeX kernel's \sp / \sb (superscript, subscript), which KaTeX lacks (live: discrete midpoint convexity)
    expect(katexMacros({})).toMatchObject({ "\\sp": "^", "\\sb": "_", "\\/": "" });
    expect(katexMacros({ "\\sp": "\\mathrm{sp}" })["\\sp"]).toBe("\\mathrm{sp}");
    // the `\mathpalette` double-⊥ independence idiom, which KaTeX cannot run (live: softmax policy value), and its
    // negation, whose `\not` may sit in the helper; a `\mathpalette` body whose helper does not overlay stays as it is
    const pre = readPreamble(String.raw`\newcommand\independent{\protect\mathpalette{\protect\independenT}{\perp}}
\def\independenT#1#2{\mathrel{\rlap{$#1#2$}\mkern2mu{#1#2}}}
\newcommand\nindependent{\protect\mathpalette{\protect\nindependenT}{\perp}}
\def\nindependenT#1#2{\mathrel{\rlap{$#1#2$}\mkern2mu{\not#1#2}}}
\newcommand\cnindep{\centernot{\mathpalette{\independenT}{\perp}}}
\newcommand\smallperp{\mathpalette\sperp\perp}
\def\sperp#1#2{\scalebox{.7}{$#1#2$}}`).macros;
    const km = katexMacros(pre);
    expect(km["\\independent"]).toBe("\\perp\\!\\!\\!\\perp");
    expect(km["\\nindependent"]).toBe("\\not\\perp\\!\\!\\!\\perp");
    expect(km["\\cnindep"]).toBe("\\not\\perp\\!\\!\\!\\perp");
    expect(km["\\smallperp"]).not.toMatch(/perp\\!/);
  });
});

describe("tex_html: TeX the page read wrong", () => {
  const page = (body: string, pre = "", aux?: string) => renderPaper({ files: { "m.tex": `${pre}\\begin{document}${body}\\end{document}` }, main: "m.tex", aux });
  const text = (html: string) => html.replace(/<[^>]+>/g, "").replace(/\s+/g, " ");
  // The finding: `$\\$` (a formula of one line break) was read as an escaped `$`, and every formula after it
  // swapped with the text between: `\frac`, `\left` shown as text, the prose sent to KaTeX.
  it("ends a formula at its first unescaped $: $\\\\$ is a formula, the text after it is text", () => {
    const r = page(String.raw`Let $a$. $\\$ and the function $F$ by
\begin{equation}F(p) := \begin{cases} \frac{1}{2} & \text{if $p \leq 1$}, \\ 0 & \text{if $p > 1$}, \end{cases}\end{equation}
where $\frac{1}{p}$ and $\$5$ hold.`);
    expect(r.health.mathFailures).toEqual([]);
    expect(r.health.unknownCommands).toEqual({});
    expect(text(r.html)).toContain("and the function");
  });
  // The finding: `\def\p1*{p^{*}}` (a macro the name `\p` calls only before `1*`) was not read: `\p` undefined.
  it("expands a macro \\def'ined with a parameter text, as TeX does: the last definition of a name, its uses in bodies too", () => {
    const pre = String.raw`\def\p0{p_0}\def\p1*{p^{*}}\def\fracp1*{\frac{\p1*}{1-\p1*}}\def\pt{p_t}`;
    const defs = readPreamble(pre).delimited;
    expect(defs).toEqual({ "\\p": { delim: "1*", body: "p^{*}" }, "\\fracp": { delim: "1*", body: String.raw`\frac{\p1*}{1-\p1*}` } });
    expect(readPreamble(pre).macros["\\pt"]).toBe("p_t");
    // the tokens stay apart (`\leq` then `p`), the definitions and an escaped backslash's `\\p1*` stay as written
    expect(expandDelimited(String.raw`$p\leq\p1*$, $\fracp1*$, \\p1*`, defs)).toBe(String.raw`$p\leq p^{*}$, $\frac{p^{*}}{1-p^{*}}$, \\p1*`);
    expect(expandDelimited(pre, defs)).toBe(String.raw`\def\p0{p_0}\def\p1*{p^{*}}\def\fracp1*{\frac{p^{*}}{1-p^{*}}}\def\pt{p_t}`);
    const r = page(String.raw`For $p\leq\p1*$ and $q = \fracp1*$ at $\pt$.`, pre);
    expect(r.health.mathFailures).toEqual([]);
    expect(r.health.unknownCommands).toEqual({});
    // `\def\th@plain` under \makeatletter is another name, never `\th` with a parameter text `@plain`
    const at = readPreamble(String.raw`\newcommand{\th}{\theta}\makeatletter\def\th@plain{\slshape}\makeatother`);
    expect(at.delimited).toEqual({});
    expect(at.macros["\\th"]).toBe(String.raw`\theta`);
  });
  // The finding: a `\ref` broken over a line (`\ref{s:the` / `model}`) did not find `\label{s:the model}`.
  it("reads a label broken over lines as TeX does: one space", () => {
    const r = page(String.raw`\section{The model}\label{s:the model}
In Section \ref{s:the
  model} and Corollary~\ref{cor:max facets with
  fixed rank}.\newtheorem{cor}{Corollary}\begin{cor}\label{cor:max facets with fixed rank}A.\end{cor}`, String.raw`\newtheorem{cor}{Corollary}`);
    expect(r.health.unresolvedRefs).toEqual([]);
    expect(r.html).toContain('href="#lbl-s-the-model">1</a>');
    expect(r.html).toContain('href="#lbl-cor-max-facets-with-fixed-rank">1</a>');
  });
  // The finding: `\begin{align}\tag{K1}\label{T1} … \\\tag{K2}…` failed in KaTeX (`\tag` inside `aligned`), and its
  // labels had no number: a compiled .aux braces a tag once more (`{{K1}}`), which it did not read.
  it("numbers a line by its \\tag (\\tag* without parentheses), in the number column; reads a tagged label in the .aux", () => {
    const body = String.raw`\begin{align}\tag{K1}\label{T1} a &= b,\\\tag{K2}\label{T2} c &= d, \notag\\ e &= f\end{align}
\begin{equation}\tag*{(A)}\label{A} x = y\end{equation}
By (\ref{T1}), \eqref{T2} and \ref{A}.`;
    const r = page(body);
    expect(r.health.mathFailures).toEqual([]);
    expect(r.health.unresolvedRefs).toEqual([]);
    expect(r.html).toContain('href="#lbl-t1">K1</a>');
    expect(r.html).toContain('href="#lbl-t2">(K2)</a>');
    expect(r.html).toContain('href="#lbl-a">(A)</a>');
    expect(r.html).toContain('<span class="eqn">(A)</span>');
    expect(text(r.html)).toContain("(K1)");
    expect(text(r.html)).toContain("(1)");
    expect(readAux(String.raw`\newlabel{T1}{{{K1}}{5}{}{subsection.2.3}{}}`).labels).toEqual({ T1: "K1" });
  });
  it("sets \\textsl in a formula and the letter \\O in text", () => {
    const r = page(String.raw`{\O}ksendal: $d\textsl{[}X\textsl{]}$.`);
    expect(r.health.mathFailures).toEqual([]);
    expect(r.health.unknownCommands).toEqual({});
    expect(text(r.html)).toContain("Øksendal");
  });
  // The finding: `$\{\textrm{$x$ is bad}\}$` was cut at the `$` inside `\textrm`: three formulas failed.
  it("ends an inline formula at a $ in none of its groups: a formula in its \\text is part of it", () => {
    const r = page(String.raw`The event $\{\textrm{$x$ is bad for $i$}\}$ holds and $y$ too.`);
    expect(r.health.mathFailures).toEqual([]);
    expect(text(r.html)).toContain("holds and");
  });
  // The finding: `\begin{equation*}\label{w}` left `\eqref{w}` unresolved; LaTeX prints the enclosing number.
  it("gives a label in an unnumbered display the number of what encloses it", () => {
    const r = page(String.raw`\section{A}\section{B}\begin{equation*}\label{w} x = y\end{equation*}\begin{align*} a &= b \label{v}\end{align*}By \eqref{w} and \ref{v}.`);
    expect(r.health.unresolvedRefs).toEqual([]);
    expect(r.html).toContain('href="#lbl-w">(2)</a>');
    expect(r.html).toContain('href="#lbl-v">2</a>');
  });
  // The finding: `\vskip \belowdisplayskip` and `\vrule` were shown as unknown commands.
  it("sets nothing for glue and rules: \\vskip, \\hskip, \\kern with a register or a unit, \\vrule with its specification", () => {
    const r = page(String.raw`A\vskip \belowdisplayskip B\hskip 0pt plus 1fil C\kern-.5\baselineskip D\vrule width 1pt height 2cm E\vrule F\vskip{1em}G.`);
    expect(r.health.unknownCommands).toEqual({});
    expect(text(r.html)).toContain("A B C D E FG.");
  });
  // The finding: etoolbox's `\iftoggle` was an unknown command, both branches shown.
  it("reads etoolbox toggles: the branch the toggle selects, set in the preamble or in the body", () => {
    const pre = String.raw`\usepackage{etoolbox}\newtoggle{abs}\newtoggle{full}\toggletrue{full}`;
    const r = page(String.raw`\iftoggle{abs}{SHORT}{LONG} \iftoggle{full}
{FULL}{PART} \nottoggle{abs}{NOTABS}{ABS} \settoggle{abs}{true}\iftoggle{abs}{NOWSHORT}{NOWLONG}`, pre);
    expect(r.health.unknownCommands).toEqual({});
    expect(text(r.html).trim()).toBe("LONG FULL NOTABS NOWSHORT");
    expect(readPreamble(pre).toggles).toEqual({ abs: false, full: true });
  });
  // The finding: `\begin{proofof}{Lemma 1}` for a `\newcommand{\proofof}[1]` was an unknown environment, its argument shown as text.
  it("runs a command named by an environment at its begin, and \\end<name> at its end, as LaTeX does", () => {
    const pre = String.raw`\newcommand{\proofof}[1]{\textit{Proof of #1}:}\newcommand{\aside}{REMARK:}\newcommand{\endaside}{ END}`;
    const r = page(String.raw`\begin{proofof}{Lemma 1}It holds.\end{proofof} \begin{aside}Note.\end{aside}`, pre);
    expect(r.health.unknownCommands).toEqual({});
    expect(text(r.html)).toContain("Proof of Lemma 1:It holds.");
    expect(text(r.html)).toContain("REMARK:Note. END");
  });
  // The finding: `\big(in $z$\big)` in text and `\ensuremath{\mathrm{man}}` met in text showed `big`, `mathrm` as text.
  it("sets \\ensuremath and a sized delimiter in text as formulas", () => {
    const r = page(String.raw`\newcommand{\man}{\ensuremath{\mathrm{man}}}up to a term \big(in $z$\big) at $V_\man$ and V\man.`);
    expect(r.health.unknownCommands).toEqual({});
    expect(r.health.mathFailures).toEqual([]);
    expect(text(r.html)).not.toMatch(/big|mathrm/);
  });
  // The finding: an amsplain .bbl's `% \MRhref is called by …` comment was read as text, and its `\bysame` was unknown.
  it("reads a .bbl without its comments and with its definitions; \\bysame is the rule for the same authors", () => {
    const bbl = String.raw`\providecommand{\bysame}{\leavevmode\hbox to3em{\hrulefill}\thinspace}
% \MRhref is called by the amsart/book/proc definition of \MR.
\providecommand{\bibinfo}[2]{#2}
\begin{thebibliography}{2}
\bibitem{a} A.~B, \emph{One}, 2001.
\bibitem{b} \bysame, \emph{Two}, \bibinfo{year}{2002}.
\end{thebibliography}`;
    const r = renderPaper({ files: { "m.tex": String.raw`\begin{document}See \cite{a}.\bibliography{refs}\end{document}` }, main: "m.tex", bbl });
    expect(r.health.unknownCommands).toEqual({});
    expect(text(r.html)).toContain("———, Two, 2002.");
    expect(text(r.html)).not.toContain("MRhref");
    // a percent-encoded link is not a comment
    const url = renderPaper({ files: { "m.tex": String.raw`\begin{document}\bibliography{refs}\end{document}` }, main: "m.tex", bbl: String.raw`\begin{thebibliography}{1}
\bibitem{k} A. \url{https://x.com/a%2Fb%20c} done.
\end{thebibliography}` });
    expect(text(url.html)).toContain("https://x.com/a%2Fb%20c");
    expect(text(url.html)).toContain("done.");
  });
  // The finding: `\ensuremath{SU\hspace*{-\fixSUBT}BT}` (text-mode content) was sent to the formula renderers and drawn as raw TeX.
  it("keeps an \\ensuremath neither renderer reads as text", () => {
    const r = page(String.raw`\newlength{\fix}(\ensuremath{SU\hspace*{-\fix}BT}) and \ensuremath{x^2}.`);
    expect(r.html).not.toContain("tex-raw");
    expect(r.health.mathFailures).toEqual([]);
  });
});

describe("tex_html: a complete-looking paper without a compile", () => {
  const SRC = String.raw`\documentclass{article}
\numberwithin{equation}{section}
\newtheorem{thm}{Theorem}[section]
\newcommand{\abs}[1]{\lvert #1\rvert}
\newcommand{\pkg}[2][R]{#2 (#1)}
\newenvironment{note}{\begin{quote}\textbf{Note.}}{\end{quote}}
\graphicspath{{figs/}}
\begin{document}
\section{One}
\begin{thm}\label{t:a} $\abs{x}\ge 0$ and \pkg{lme4}.\end{thm}
\begin{align} a &= b \label{e:1}\\ c &= d \nonumber\\ e &= f \label{e:2}\end{align}
See Theorem~\ref{t:a}, (\ref{e:1}), \eqref{e:2}, Figure~\ref{f:x} and Table~\ref{t:x}.
\begin{note}Careful.\end{note}
\begin{figure}\centering\includegraphics[width=0.5\textwidth]{plot}\includegraphics{curve}\caption{Two plots.}\label{f:x}\end{figure}
\begin{table}\caption{Numbers.}\label{t:x}\begin{tabular}{l|cr}\hline A & \multicolumn{2}{c}{B} \\ \hline x & $1$ & 2 \\ \end{tabular}\end{table}
\includegraphics{absent}
Theorem 2 is stated in prose here.
\end{document}`;
  const r = renderPaper({ files: { "m.tex": SRC }, main: "m.tex", assets: ["figs/plot.png", "figs/curve.pdf"], assetBase: "/api/runs/x/asset", anchors: [{ node: "thm:prose", file: "m.tex", line: "Theorem 2 is stated in prose here." }] });
  it("reads \\center (the declaration form of the center environment) as a layout command, as \\centering", () => {
    const q = renderPaper({ files: { "m.tex": "\\documentclass{article}\\begin{document}\\begin{figure}\\center\\includegraphics{plot}\\caption{A plot.}\\end{figure}\\end{document}" }, main: "m.tex", assets: ["plot.png"], assetBase: "/a" });
    expect(q.health.unknownCommands).not.toHaveProperty("center");
    expect(q.html).not.toContain("center");
  });
  it("numbers results within sections, equations line by line, figures and tables — every \\ref resolves", () => {
    expect(r.envs[0]!.heading).toBe("Theorem 1.1");
    expect(r.health.unresolvedRefs).toEqual(["absent-never-referenced"].filter(() => false));
    expect(r.html).toContain('href="#lbl-t-a">1.1</a>');
    expect(r.html).toContain('href="#lbl-e-1">1.1</a>');
    expect(r.html).toContain('href="#lbl-e-2">(1.2)</a>');
    expect(r.html).toContain('href="#lbl-f-x">1</a>');
    expect(r.html).toContain("<b>Figure 1.</b>");
    expect(r.html).toContain("<b>Table 1.</b>");
  });
  it("expands the author's macros (with arguments and defaults) and environments", () => {
    expect(r.html).toContain("lme4 (R)");
    expect(r.html).toContain("<strong>Note.</strong>");
    expect(r.health.mathErrors).toBe(0);
  });
  it("shows figures (images inline, PDFs for pdf.js), reports a missing one, and builds HTML tables", () => {
    expect(r.html).toContain('<img class="fig"');
    expect(r.html).toContain('src="/api/runs/x/asset/figs/plot.png"');
    expect(r.html).toContain('style="width:50%"');
    expect(r.html).toContain('data-pdf="/api/runs/x/asset/figs/curve.pdf"');
    expect(r.health.missingFigures).toEqual(["absent"]);
    expect(r.html).toContain('<td colspan="2" style="text-align:center">B</td>');
    expect(r.health.tables).toBe(1);
  });
  it("anchors a result stated in prose at its source line", () => {
    expect(r.anchors["thm:prose"]).toBe("res-thm-prose");
    expect(r.html).toContain('id="res-thm-prose"');
  });
  it("makes the author's math macros safe for KaTeX", () => {
    const m = katexMacros({ "\\indep": String.raw`\rotatebox[origin=c]{90}{$\models$}`, "\\R": String.raw`\mbox{$\mathbb{R}$}` });
    expect(m["\\indep"]).toBe(String.raw`\perp\!\!\!\perp`);
    expect(m["\\R"]).toBe(String.raw`{\mathbb{R}}`);
  });
  it("renders a real paper whole: tbs_neural_causal_pi's flattened source, numbered by itself", () => {
    const dir = path.resolve(__dirname, "../verify/fixtures/handoff/tbs_neural_causal_pi/discovery");
    const flat = gunzipSync(readFileSync(path.join(dir, "flat.tex.gz"))).toString("utf8");
    const kinds = JSON.parse(gunzipSync(readFileSync(path.join(dir, "envs.json.gz"))).toString("utf8")).newtheorem;
    const p = renderPaper({ files: { "flat.tex": flat }, main: "flat.tex", theoremKinds: kinds });
    expect(p.health.mathErrors).toBe(0);
    expect(p.health.unresolvedRefs).toEqual([]);
    expect(p.envs.length).toBeGreaterThan(20);
    expect(p.toc.length).toBeGreaterThan(8);
  });
});

describe("actions: decisions → the CLI call", () => {
  const ctx = { toolkitRoot: "/tk", slug: "paper_a", source: "/papers/a" };
  it("resumes a run (its rulings are the agent's, at the CLI) and refuses a run without a source", () => {
    expect(buildArgv({ kind: "resume" }, ctx)).toEqual(["verify", "/papers/a", "--toolkit", "/tk", "--slug", "paper_a", "--resume"]);
    expect(displayCommand(["verify", "a b"])).toBe(`paperformalizer verify "a b"`);
    expect(() => buildArgv({ kind: "resume" }, { ...ctx, source: null })).toThrow(/no source/);
  });
  it("the owner's ruling on weakening repairs becomes the resume that carries it", () => {
    expect(buildArgv({ kind: "rule-repairs", accept: ["thm:a", "lem:b-2"], decline: { nodes: ["thm:c"], reason: "it gives up the main case" }, redo: [{ node: "thm:d", guidance: "keep the rate" }] }, ctx)).toEqual([
      "verify", "/papers/a", "--toolkit", "/tk", "--slug", "paper_a", "--resume",
      "--accept-repair", "thm:a,lem:b-2", "--decline-repair", "thm:c: it gives up the main case", "--redo-repair", "thm:d: keep the rate",
    ]);
    expect(() => buildArgv({ kind: "rule-repairs" }, ctx)).toThrow(/no repair was ruled on/);
    expect(() => buildArgv({ kind: "rule-repairs", decline: { nodes: ["thm:c"], reason: " " } }, ctx)).toThrow(/needs a reason/);
    expect(() => buildArgv({ kind: "rule-repairs", accept: ["thm:a; rm -rf"] }, ctx)).toThrow(/not a node id/);
  });
  it("a reading entered for the owner is reworded or removed by its id, as the resume that carries it", () => {
    const head = ["verify", "/papers/a", "--toolkit", "/tk", "--slug", "paper_a", "--resume"];
    expect(buildArgv({ kind: "edit-reading", readings: [{ id: "ass:pin-owner-2", text: " constants depend only on $c$ \n" }, { id: "ass:bk-owner-1", text: "$n \\ge 1$" }] }, ctx)).toEqual([
      ...head, "--edit-reading", "ass:pin-owner-2: constants depend only on $c$", "--edit-reading", "ass:bk-owner-1: $n \\ge 1$",
    ]);
    expect(buildArgv({ kind: "remove-reading", ids: ["ass:pin-owner-2", "ass:pin-owner-3"] }, ctx)).toEqual([...head, "--remove-reading", "ass:pin-owner-2", "--remove-reading", "ass:pin-owner-3"]);
    expect(displayCommand(buildArgv({ kind: "edit-reading", readings: [{ id: "ass:pin-owner-2", text: "on $c$" }] }, ctx))).toContain(`--edit-reading "ass:pin-owner-2: on \\$c\\$"`);
    expect(() => buildArgv({ kind: "edit-reading", readings: [{ id: "ass:pin-owner-2", text: "  " }] }, ctx)).toThrow(/has no text/);
    expect(() => buildArgv({ kind: "edit-reading", readings: [{ id: "ass:pin-2", text: "x" }] }, ctx)).toThrow(/not an owner reading's id/);
    expect(() => buildArgv({ kind: "remove-reading", ids: ["--from-stage"] }, ctx)).toThrow(/not an owner reading's id/);
    expect(() => buildArgv({ kind: "remove-reading", ids: [] }, ctx)).toThrow(/no reading was named/);
  });
  it("promotion and stop; a stop-after token is checked", () => {
    expect(buildArgv({ kind: "apply-promotion", round: "B" }, ctx)).toEqual(["propose", "paper_a", "--round", "B", "--apply", "--toolkit", "/tk"]);
    expect(buildArgv({ kind: "stop" }, ctx).at(-1)).toBe("--stop");
    // the request's words are the page's: another round, or a kind the page does not send, is refused — never a resume
    expect(() => buildArgv({ kind: "apply-promotion", round: "--apply" } as unknown as Parameters<typeof buildArgv>[0], ctx)).toThrow(/A or B/);
    expect(() => buildArgv({ kind: "restart" } as unknown as Parameters<typeof buildArgv>[0], ctx)).toThrow(/not an action: restart/);
  });
  it("writes checklist decisions that the pipeline's own parser reads back", () => {
    const batch = { proposals: [{ id: "b-x", verdict: "propose", source: { kind: "paper_decl", is_paper_result: true } }, { id: "b-y", verdict: "propose", source: { kind: "paper_decl", is_paper_result: false } }] } as unknown as ProposalBatch;
    const md = ["# Checklist", "", "## b-x · First", "text", "```decision", "decision: pending", "```", "", "## b-y · Second", "```decision", "decision: pending", "```", ""].join("\n");
    const next = setDecisions(md, { "b-x": { kind: "accept_with_edits", edits: { target_module: "Toolkit/Foundations/A.lean" } }, "b-y": { kind: "defer" } });
    expect(parseChecklist(next, batch)).toEqual({ "b-x": { kind: "accept_with_edits", edits: { target_module: "Toolkit/Foundations/A.lean" } }, "b-y": { kind: "defer" } });
    expect(next).toContain("text");
    expect(() => setDecisions(md, { "b-z": { kind: "accept" } })).toThrow(/no section/);
  });
  it("decides a proposed new topic in its own section, which the pipeline's parser reads back", () => {
    const batch = { proposals: [{ id: "b-x", verdict: "propose", source: { kind: "paper_decl", is_paper_result: false }, new_topic: { path: "Statistics/Bootstrap", scope: "resampling methods" } }] } as unknown as ProposalBatch;
    const md = ["## topic · Statistics/Bootstrap", "", "A new topic.", "", "```decision", "decision: pending", "```", "", "## b-x · First", "```decision", "decision: pending", "```", ""].join("\n");
    const next = setDecisions(md, { "topic:Statistics/Bootstrap": { kind: "accept" }, "b-x": { kind: "accept" } });
    expect(parseChecklist(next, batch)).toEqual({ "topic:Statistics/Bootstrap": { kind: "accept" }, "b-x": { kind: "accept" } });
  });
});

describe("an owner's reading: which note states which entry on file, and its card", () => {
  const uniform = "The implied constants are uniform.";
  const onFile = [
    { id: "ass:bk-owner-1", node: "lem:l1", reading: "$n \\ge 1$", kind: "bookkeeping", withdraws: [] },
    { id: "ass:pin-owner-1", node: "thm:t1", reading: uniform, withdraws: [{}] },
    { id: "ass:pin-owner-2", node: "lem:l1", reading: uniform, withdraws: [] },
    { id: "ass:pin-owner-3", node: "lem:l2", reading: "Never rendered." },
  ];
  it("one entry per note when the same sentence is pinned on several results; a referee's pin, a side condition and an unrendered reading have none", () => {
    const src = String.raw`\begin{document}\begin{theorem}\label{t1}A.\end{theorem}\vsReadingOwner{The implied constants are uniform.}\vsReading{Read $x$ as real.}
\begin{lemma}\label{l1}B.\end{lemma}\vsReadingOwner{The implied constants are uniform.}\end{document}`;
    const p = renderPaper({ files: { "m.tex": src }, main: "m.tex", readings: [
      { node: "ass:pin-owner-1", text: uniform, labels: ["t1"] }, { node: "ass:pin-owner-2", text: uniform, labels: ["l1"] }, { node: "ass:pin-4", text: "Read $x$ as real.", labels: ["t1"] },
    ] });
    expect(p.readings).toEqual({ "ass:pin-owner-1": "c1", "ass:pin-4": "c2", "ass:pin-owner-2": "c3" });
    expect(ownerReadingsByComment(p.readings, p.comments, onFile)).toEqual({
      c1: [{ id: "ass:pin-owner-1", node: "thm:t1", kind: "reading", text: uniform, withdraws: 1 }],
      c3: [{ id: "ass:pin-owner-2", node: "lem:l1", kind: "reading", text: uniform, withdraws: 0 }],
    });
    expect(ownerReadingsByComment(p.readings, p.comments, undefined)).toEqual({});
  });
  it("the card is tagged as the owner's reading, says what it is, and offers Edit / Remove only for an entry on file while the run is at rest", () => {
    const js = readFileSync(path.join(__dirname, "..", "..", "src", "ui", "static", "app.js"), "utf8").replace(/\r\n/g, "\n");
    const line = (start: string) => js.slice(js.indexOf(start), js.indexOf("\n", js.indexOf(start)));
    const cardHTML = new Function("esc", "envOf", `const SNAP = null;\n${line("const KIND_TAG")}\n${line("const CHIP")}\n${js.slice(js.indexOf("function cardHTML("), js.indexOf("/* Edit / Save / Cancel / Remove"))}; return cardHTML;`)(
      (x: string) => String(x).replace(/&/g, "&amp;").replace(/</g, "&lt;"), () => null,
    ) as (c: unknown, r: unknown, o?: unknown) => string;
    const c = { id: "c3", kind: "reading-owner", label: "Clarification (author)", html: "<i>uniform</i>" };
    const own = [{ id: "ass:pin-owner-2", node: "lem:l1", kind: "reading", text: "uniform in $n$ & <b>", withdraws: 0 }];
    const rest = cardHTML(c, null, { own, atRest: true, draft: null });
    expect(rest).toContain(`<span class="ctag ">Author's reading</span>`);
    expect(rest).toContain("A binding reading entered for the paper's author");
    expect(rest).toContain("You can edit or remove it here.");
    expect(rest).toContain(`data-reading="edit">Edit</button>`);
    expect(rest).toContain(`data-reading="remove">Remove</button>`);
    expect(rest).toContain(`<div class="cbody"><i>uniform</i></div>`);
    // a live run, a run with no entry on file for the note, another kind of note: no buttons
    const live = cardHTML(c, null, { own, atRest: false, draft: null });
    expect(live).toContain("once the run is at rest");
    expect(live).not.toContain("data-reading=");
    const unmatched = cardHTML(c, null, { own: [], atRest: true, draft: null });
    expect(unmatched).toContain("A binding reading entered for the paper's author");
    expect(unmatched).not.toMatch(/data-reading=|edit or remove/);
    const referee = cardHTML({ ...c, kind: "reading", label: "Clarification" }, null);
    expect(referee).toContain(`<span class="ctag ">Clarification</span>`);
    expect(referee).not.toMatch(/cown|data-reading/);
    // the editor: the reading's TeX in a textarea (escaped), Save / Cancel, the rendered text set aside
    const editing = cardHTML(c, null, { own: [...own, { ...own[0]!, id: "ass:pin-owner-3" }], atRest: true, draft: own[0]!.text });
    expect(editing).toContain(`<textarea data-reading-text rows="5" aria-label="The reading, as TeX">uniform in $n$ &amp; &lt;b></textarea>`);
    expect(editing).toContain(`data-reading="save">Save</button>`);
    expect(editing).toContain(`data-reading="cancel">Cancel</button>`);
    expect(editing).toContain("It is pinned on 2 results; a change here applies to each.");
    expect(editing).not.toContain(`class="cbody"`);
    expect(js).not.toContain("Your reading");
  });
});

describe("library and run models", () => {
  it("parseModule reads docstring, kind, name (with namespace) and signature", () => {
    const ds = parseModule("namespace T.A\n\n/-- [The mean](goal) of [y](hyp:y). -/\ndef mean (y : ℕ → ℝ) : ℝ := 0\n\n/-- Doc. -/\n-- @node: x\nlemma l (h : 0 < 1) : True := trivial\n");
    expect(ds.map((d) => [d.name, d.kind, d.sig])).toEqual([["T.A.mean", "def", "(y : ℕ → ℝ) : ℝ"], ["T.A.l", "theorem", "(h : 0 < 1) : True"]]);
    expect(ds[0].doc).toContain("(hyp:y)");
  });
  it("paperUses: a full name anywhere (dot-notation and qualified uses too), the rest of a name only where a prefix of it is opened", () => {
    const n = paperNames([
      "import X\nopen Toolkit.Foundations.Prob in\ntheorem t : True := by\n  exact (Toolkit.Foundations.Prob.Moments.var_le h).mp trivial\n",
      "open Toolkit.Foundations.Opt\nexample := gd_rate₁ x\nexample := (PolyBounded.const 2).add PolyBounded.id\n",
      "example := Foundations.Opt.hidden y -- MyToolkit.Foundations.Prob.other\n",
      "open Toolkit.Foundations.Opt\nexample := (h x).mono (le_refl 0)\nexample := 2.inl\n",
    ]);
    const uses = (name: string) => paperUses(n, name);
    expect(uses("Toolkit.Foundations.Prob.Moments.var_le")).toBe(true);
    expect(uses("Toolkit.Foundations.Opt.gd_rate₁")).toBe(true);
    // partly qualified under an opened namespace
    expect(uses("Toolkit.Foundations.Opt.PolyBounded.const")).toBe(true);
    expect(uses("Toolkit.Foundations.Opt.PolyBounded.id")).toBe(true);
    expect(uses("Foundations.Opt.hidden")).toBe(true);
    // the bare name in a file that does not open the namespace, a name only as part of a longer one,
    // a name written after a `.` (a field or dot-notation on something else)
    expect(uses("Toolkit.Foundations.Prob.hidden")).toBe(false);
    expect(uses("Toolkit.Foundations.Opt.gd_rate")).toBe(false);
    expect(uses("Toolkit.Foundations.Prob.other")).toBe(false);
    expect(uses("Toolkit.Foundations.Opt.mono")).toBe(false);
    expect(uses("Toolkit.Foundations.Opt.add")).toBe(false);
    expect(uses("Toolkit.Foundations.Opt.inl")).toBe(false);
  });
  it("validSlug accepts run names and refuses paths", () => {
    expect(validSlug("tbs_neural_causal_pi")).toBe(true);
    for (const bad of ["../x", "a/b", "", ".hidden", "a\\b"]) expect(validSlug(bad)).toBe(false);
  });
});

describe("tex_html: a long corrected statement is laid out one sentence to a line", () => {
  const T = String.raw`Suppose $K$ has compact support, cf. Lemma~\ref{l:a}. For every $\gamma$ with $E[\{\partial_d\gamma\}^2]<\infty$, i.e. a smooth direction, require
\[
E\{m(W,\ell_h\gamma)\}=E\{\ell_h(W_j)m(W,\gamma)\}.
\]
In the inverse model, $W_j$ is measurable. Then $\kappa_h\lesssim h^{-2/3}$ by J. Doe's bound.`;
  it("splits at sentence ends only: not inside mathematics, after an abbreviation or an initial", () => {
    const s = texSentences(T);
    expect(s.map((x) => x.slice(0, 12))).toEqual(["Suppose $K$ ", "For every $\\", "In the inver", "Then $\\kappa"]);
    expect(s.join(" ").replace(/\s+/g, " ")).toBe(T.replace(/\s+/g, " "));
  });
  it("draws each sentence as its own line and sets a conclusion off; a short block stays as it is", () => {
    const long = `${T} ${T.replace(/compact/g, "bounded")}`;
    const html = renderPaper({ files: { "m.tex": `\\begin{document}\\vsCorrected{${long}}\\vsCorrected{Short. Then done.}\\end{document}` }, main: "m.tex", aux: "" }).html;
    // each sentence a line, each conclusion after its own assumptions; the sentences say which is which: no heading, no bullet
    expect(html.match(/<div class="rv-ln rv-hyp[ "]/g)!.length).toBe(6);
    expect(html.match(/<div class="rv-ln rv-concl[ "]/g)!.length).toBe(2);
    expect(html).not.toMatch(/rv-h"|<li>|•/);
    expect(html.match(/rv-first/g)!.length).toBe(3);
    // a proof is an argument: one sentence to a line, never listed as assumptions and conclusion
    const proof = renderPaper({ files: { "m.tex": `\\begin{document}\\vsProof{${long}}\\end{document}` }, main: "m.tex", aux: "" }).html;
    expect(proof).not.toMatch(/rv-h|rv-list/);
    expect(proof.match(/<span class="rv-s">/g)!.length).toBe(8);
    expect(sentenceGroups(["If $x$, then $y$.", "Suppose A.", "In Example 1, suppose B.", "Then C.", "In Example 1, D.", "Suppose E.", "Then F."]).map((g) => [g.kind, g.items.length]))
      .toEqual([["claim", 1], ["hyp", 2], ["concl", 2], ["hyp", 1], ["concl", 1]]);
    expect(html).toContain("Short. Then done.");
  });
});

describe("tex_html: a statement is laid out as setting, assumptions and conclusion", () => {
  const SETTING = [
    String.raw`where $n_t = \sum_{i = 1}^{n/2} I (\|U_i \|> t)$ and $\pi_t$ is the tail probability.`,
    String.raw`Write $\mathcal T$ for the training split, $\pi_t=\mathbb P(\|U\|>t)$, and $G_t=C+\bar e(t)$, where $C$ bounds $|g|$.`,
    String.raw`Let $\psi_{\text{DR}}$ and $\psi_{\text{IPW}}$ be the individual summands defining the estimators in (\ref{eq:a}) and (\ref{eq:b}), respectively.`,
    String.raw`Let $\bar e(t)=\sup_{r\geq t}e(r)$, let $C$ bound $|g|$, and put $G_t=C+\bar e(t)$.`,
    String.raw`Let $\mathcal T$ denote its training split, put $N_e=n/2$, and write $M_t=\sum_{i\in\mathcal D_2}I\{\|U_i\|>t\}$.`,
    String.raw`For $M>0$, define \vsFit{\begin{aligned} A_t={}&2\bar e(t)+\frac{2G_t}{c}(t^a-1),\\ E_{\text{DR}}={}&\sqrt{\frac{12v}{\delta M}}.\end{aligned}}`,
    String.raw`For $j\in\{1,2\}$ and any $B_j>0$ chosen using only $\mathcal T$, define \[ v_{j,t}=\mathbb E[\psi_j^2 I\{|\psi_j|\leq B_j\}\mid\mathcal T,\|U\|>t]. \]`,
    String.raw`For a generic evaluation observation put \vsFit{\psi=\hat g(X,1)-\hat g(X,0).}`,
    String.raw`With $K$ as in Lemma~\ref{l:a}, define \vsFit{E_n(t)=S_n(t)+H(t).}`,
    String.raw`Define \vsFit{H_n(k)=\frac1k\sum_{j=1}^k\log\frac{R_{(j)}}{R_{(k+1)}},\qquad 1\leq k\leq n.}`,
    String.raw`Define both estimators to be zero if $M=|\mathcal I|=0$, and define both outputs to be zero if $1-\hat\alpha_n\hat\gamma_n=0$.`,
    String.raw`Set the output to zero if $M_t=0$ or $1-\hat\alpha_n\hat\gamma_n=0$.`,
    String.raw`Put $\pi_t=\mathbb P(\|U\|>t)$ and $M=|\mathcal I|$, and set $\hat\eta=0$ when $M=0$.`,
    String.raw`Fix $a_0\in(0,\beta)$ and put $a=R_\alpha(n,\delta/12)$.`,
    String.raw`Here $K$ depends on the radial law and $a_0$.`,
    String.raw`We denote $\sigma^2=\operatorname{Var}(Y)$.`,
  ];
  const MODIFY = [
    String.raw`In the radial step of Algorithm~\ref{alg:nete}, use the full-input adaptive Hill estimator of Lemma~\ref{lemma:mu_rate} at tolerance $\delta/3$.`,
    String.raw`Replace the plug-in variance in Algorithm 2 by its truncated version.`,
    String.raw`In Step 3 of the procedure, compute $\hat\gamma_n$ from the full sample.`,
  ];
  // the safe side: each of these states or imposes something, or is no definition in form
  const HYP = [
    String.raw`Suppose in addition that the conditions of Lemma~\ref{lemma:eta_rate} hold at tolerance $\delta/3$.`,
    String.raw`For sufficiently large $t\geq1$ and $n$, suppose that $a\leq a_0$ and $n\pi_t\geq16\log(12/\delta)$.`,
    String.raw`Assume $\alpha<\beta$.`,
    String.raw`Let $\alpha<\beta$.`,
    String.raw`Let $X_1,\ldots,X_n$ be i.i.d. with finite variance.`,
    String.raw`Let $f$ be Lipschitz.`,
    // a property said of a symbol rides in a definition: an assumption
    String.raw`where $n_t = \sum_{i = 1}^{n/2} I (\|U_i \|> t)$ and $R_p, R_g$ are estimation errors that are monotonically decreasing with respect to sample size.`,
    String.raw`Let $A_n=c\,n^{\gamma}$, where $A_n$ is measurable with respect to the full sample.`,
    String.raw`Write $F$ for the distribution function of $Y$, which is continuous.`,
    // defines and assumes in one sentence
    String.raw`Let $r=\lim_{N\rightarrow\infty}N_1/N$ and suppose $0<r<1$.`,
    String.raw`Write $\gamma=1/\beta$, $\kappa=1-\alpha\gamma>0$, and let $b$ be the bound in Lemma~\ref{l:a}.`,
    String.raw`Put $\rho_n=n_2/n_1\rightarrow\rho\in[0,1]$.`,
    String.raw`Fix $t$ such that $n\pi_t\geq16$.`,
    String.raw`Define $a=R(n)$, provided $n\geq2$.`,
    String.raw`Let $E$ be the event on which the bound holds.`,
    String.raw`Under the assumptions of Theorem~\ref{thm:a}, let $c=2$.`,
    String.raw`Put $a=1$; then $b\leq a$.`,
    String.raw`For sufficiently large $n$, the estimator is consistent and we set $c=1$.`,
    String.raw`In the inverse model, $W_j$ is measurable.`,
    String.raw`With probability at least $1-\delta$, we have $M\geq n\pi_t/4$.`,
    String.raw`The point $\gamma^*$ is interior and $\Sigma$ is nonsingular.`,
    String.raw`For every $\gamma$ with $E[\gamma^2]<\infty$, require \[ E\{m(W,\gamma)\}=0. \]`,
    // an instruction that names no step of the method is no change of the algorithm, and no notation
    String.raw`Use the full-input adaptive Hill estimator of Lemma~\ref{lemma:mu_rate}.`,
    String.raw`Fix $\delta\in(0,1/2)$, put $\tau=\delta/16$, and use that estimator at tolerance $\tau$.`,
    String.raw`In Algorithm~\ref{alg:a}, suppose the step size satisfies $\eta\leq1/L$.`,
    String.raw`Algorithm~\ref{alg:a} uses the full sample.`,
    // a hypothesis word inside a label or a formula is no word of the sentence; one in its prose is
    String.raw`Let $c=1$ as in (\ref{eq:holds}), which we assume throughout.`,
  ];
  it("reads a sentence's part off its own form, and keeps every doubtful one among the assumptions", () => {
    for (const t of SETTING) expect([t, sentencePart(t)]).toEqual([t, "setting"]);
    for (const t of MODIFY) expect([t, sentencePart(t)]).toEqual([t, "modify"]);
    for (const t of HYP) expect([t, sentencePart(t)]).toEqual([t, "hyp"]);
    // a word of a label is not read
    expect(sentencePart(String.raw`Put $a=b$ as in (\ref{eq:suppose}).`)).toBe("setting");
  });

  const WHERE = HYP.find((t) => t.startsWith("where"))!;
  const BODY = [WHERE, HYP[0], MODIFY[0], SETTING[10], SETTING[1], SETTING[5], SETTING[13], HYP[1], SETTING[14],
    String.raw`Then, with probability at least $1-\delta$, we have $M\geq n\pi_t/4$.`, String.raw`Moreover, if $q_n<\kappa$, the bound improves.`].join(" ");
  it("cuts after a display the annotated paper set, and never inside a list", () => {
    expect(texSentences(BODY).length).toBe(11);
    expect(texSentences(String.raw`Define \vsFit{a=b.} Fix $c$. Then \vsFit{x\leq y,} where $K$ is fixed.`).map((x) => x.slice(0, 6))).toEqual(["Define", "Fix $c", "Then \\"]);
    const list = String.raw`Suppose $A$ holds. \begin{enumerate} \item If $s<1$, take $h=1$. With probability one, \vsFit{a\leq b.} \item Else $h=2$. \end{enumerate} Then C.`;
    expect(texSentences(list).map((x) => x.slice(0, 9))).toEqual(["Suppose $", "\\begin{en", "Then C."]);
  });
  it("gives every sentence exactly one part, in the text's order, and groups the consecutive ones of a part", () => {
    const sents = texSentences(BODY), parts = statementParts(sents);
    expect(parts.map((p) => p.text)).toEqual(sents);
    expect(parts.map((p) => p.part)).toEqual(["hyp", "hyp", "modify", "setting", "setting", "setting", "setting", "hyp", "setting", "concl", "concl"]);
    expect(parts.map((p) => p.run)).toEqual([0, 0, 1, 1, 1, 1, 1, 2, 3, 4, 4]);
    expect(statementParts(["Suppose A.", "Then B.", "Let $x=1$.", "Suppose C.", "Then D.", "If $x$, then $y$.", "If $y$, then $z$."]).map((p) => [p.part, p.run]))
      .toEqual([["hyp", 0], ["concl", 1], ["setting", 2], ["hyp", 3], ["concl", 4], ["claim", 5], ["claim", 6]]);
  });
  const page = (macro: string, body = BODY): string => renderPaper({ files: { "m.tex": `\\begin{document}\\${macro}{${body}}\\end{document}` }, main: "m.tex", aux: "" }).html;
  const words = (html: string): string => html.replace(/<span class="rv-tag"[^>]*>[^<]*<\/span>/g, "").replace(/<[^>]+>/g, "").replace(/\s+/g, "");
  const lines = (html: string): string[] => [...html.matchAll(/<div class="rv-ln (rv-\w+)( rv-first)?">/g)].map((m) => `${m[2] ? "/ " : ""}${m[1]!.slice(3)}`);
  it("sets a statement as a paper sets a theorem: its own order, a group of lines per part, nothing added and nothing dropped", () => {
    for (const macro of ["vsCorrected", "vsProposed", "vsOriginal", "vsClarified"]) {
      const html = page(macro);
      // the sentences in the text's order, a new group ("/") where the part changes
      expect(lines(html)).toEqual(["hyp", "hyp", "/ set", "set", "set", "set", "set", "/ hyp", "/ set", "/ concl", "concl"]);
      // no heading, no list (not for one condition, not for several), no reordering
      expect(html).not.toMatch(/rv-h"|<li>|<ul|•|rv-li|order:|Setting|Assumptions|Conclusion/);
    }
    // the same words as the block laid out line by line with no parts (a proof's layout), in the same order
    expect(words(page("vsCorrected"))).toBe(words(page("vsProof")));
    expect(words(page("vsCorrected"))).toContain("where");
  });
  it("sets a statement the same in every view of the marks: no view's style reaches into its layout", () => {
    const css = readFileSync(new URL("../../src/ui/static/app.css", import.meta.url), "utf8").replace(/\/\*[\s\S]*?\*\//g, "");
    const rules = [...css.matchAll(/([^{}]+)\{[^{}]*\}/g)].map((m) => m[1]!.trim()).filter((sel) => /\.m-(?:all|simple|original)\b/.test(sel));
    expect(rules.length).toBeGreaterThan(3);
    for (const sel of rules) expect(sel).not.toMatch(/\.rv-(?:parts|ln|set|hyp|concl|claim|first|fold|s)\b/);
  });
  it("draws a change of the algorithm as a line of the setting, and folds only a very long displayed definition under its lead", () => {
    const html = page("vsCorrected");
    // a sentence that changes a step of the method is a line of the setting like any other: no mark
    expect(html).not.toContain("rv-mark");
    expect(html).toMatch(/<div class="rv-ln rv-set rv-first"> ?In the radial step/);
    const long = BODY.replace(String.raw`E_{\text{DR}}={}&\sqrt{\frac{12v}{\delta M}}.`, String.raw`E_{\text{DR}}={}&\sqrt{\frac{12v}{\delta M}}\\ &+b_t\\ &+c_t\\ &+d_t\\ &+e_t\\ &+f_t\\ &+g_t\\ &+h_t.`);
    // a display of a few rows stays in sight
    expect(page("vsCorrected", BODY.replace(String.raw`E_{\text{DR}}={}&\sqrt{\frac{12v}{\delta M}}.`, String.raw`E_{\text{DR}}={}&\sqrt{\frac{12v}{\delta M}}\\ &+b_t\\ &+c_t.`))).not.toContain("rv-fold");
    const folded = page("vsCorrected", long);
    expect(html).not.toContain("rv-fold");
    expect(folded.match(/<details class="rv-fold">/g)!.length).toBe(1);
    expect(folded).toMatch(/<details class="rv-fold"><summary>For [\s\S]*?, define <\/summary><div class="eq">/);
    expect(words(folded)).toBe(words(page("vsProof", long)));
  });
  it("lays a block split off a result out the same way, and leaves a short or part-less statement as it was", () => {
    const split = renderPaper({ files: { "m.tex": `\\begin{document}\\vsCorollary{cor:x}{Theorem 2}{${BODY}\\vsLine\\textit{Proof.} By the theorem.}\\end{document}` }, main: "m.tex", aux: "" }).html;
    expect(lines(split)).toEqual(lines(page("vsCorrected")));
    expect(split).toContain(`<div class="proof">`);
    // an annotated paper of an earlier run: `\\[ \\]` displays, no display macro, nothing to regroup
    const old = String.raw`Suppose $K$ has compact support and that the first condition of the theorem is in force. Suppose that \[ E\{m(W,\gamma)\}=0 \] for every direction $\gamma$ of the model with a finite second moment. Suppose further that the design is balanced in the sense of Section 2 and that the sample sizes diverge together. Then $\kappa_h\lesssim h^{-2/3}$ and the estimator is consistent at the stated rate, uniformly over the bandwidths of the grid chosen in advance.`;
    const html = page("vsCorrected", old);
    expect(lines(html)).toEqual(["hyp", "hyp", "hyp", "/ concl"]);
    expect(page("vsCorrected", "Let $x=1$. Suppose A. Then B.")).not.toMatch(/rv-parts|rv-ln/);
  });
});

describe("tex_html: a preamble's fallback definitions", () => {
  it("\\providecommand of a symbol the renderer knows changes nothing; of an unknown command it defines it", () => {
    const pre = readPreamble(String.raw`\providecommand{\lesssim}{\mathrel{\vcenter{\offinterlineskip\hbox{$<$}\hbox{$\sim$}}}}
\providecommand{\myop}{\operatorname{op}}
\newcommand{\lesssim}{\preceq}`.split("\n").slice(0, 2).join("\n"));
    expect(pre.macros["\\lesssim"]).toBeUndefined();
    expect(pre.macros["\\myop"]).toBe("\\operatorname{op}");
    const html = renderPaper({ files: { "m.tex": String.raw`\providecommand{\lesssim}{\mathrel{<\sim}}\begin{document}$a\lesssim b$\end{document}` }, main: "m.tex", aux: "" }).html;
    expect(html).toContain("≲");
    expect(html).not.toContain("∼");
  });
});

describe("tex_html: a proof heading", () => {
  it("reads `[of Theorem 1]` as `Proof of Theorem 1.` and keeps any other heading", () => {
    const doc = (opt: string) => renderPaper({ files: { "m.tex": `\\begin{document}\\begin{proof}[${opt}]Trivial.\\end{proof}\\end{document}` }, main: "m.tex", aux: "" }).html;
    expect(doc("of the main theorem")).toContain(">Proof of the main theorem.<");
    expect(doc("Sketch")).toContain(">Sketch.<");
  });
});

describe("run status: who a halt waits on", () => {
  it("says what a live run is doing without prompt sizes or paths", () => {
    const ev = (message: string) => ({ at: "", stage: "3.5", status: "dispatch", message });
    expect(liveHeadline(ev("F3.5 delta reviewer :: batch[ass:pin-1,ass:pin-2,ass:pin-3]: prompt 39767 bytes from [/a/b/c/stage3_5.txt, /x/y/z/brief.md]"))).toBe("F3.5 delta reviewer :: 3 results — working");
    expect(liveHeadline(ev("F3 proof filler: stdout 850 bytes"))).toBe("F3 proof filler — done");
    expect(liveHeadline({ ...ev("statement review completed"), stage: "V1.5" })).toBe("V1.5 · statement review completed");
  });
  const root = mkdtempSync(path.join(tmpdir(), "tc-status-"));
  const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs") } as unknown as ToolkitConfig;
  const halt = (slug: string, stage: string, completed: string) => {
    mkdirSync(path.join(root, "runs", slug), { recursive: true });
    writeFileSync(path.join(root, "runs", slug, "state.json"), JSON.stringify({ stage_completed: completed, verify: { phase: "formalize" } }));
    writeFileSync(path.join(root, "runs", slug, "pipeline.jsonl"), JSON.stringify({ timestamp: "2026-10-03T00:00:00Z", stage, status: "checkpoint", message: "PROOF-REVIEW LOOP ESCALATION" }) + "\n");
  };
  // this process stands in for an attached agent session
  const attach = (slug: string) => writeFileSync(path.join(root, "runs", slug, "orch.json"), JSON.stringify({ agent: "Claude Code", pid: process.pid, started: null, attached_at: "x" }));
  it("a repair is being redone under a mixed ruling too (the receipt closes as `ruled`, not `redo`)", () => {
    expect(redoingOf({ weakening_repair: { status: "redo" } })).toBe(true);
    expect(redoingOf({ weakening_repair: { status: "ruled", decisions: { "thm:a": "accepted", "thm:b": "redo" } } })).toBe(true);
    expect(redoingOf({ weakening_repair: { status: "ruled", decisions: { "thm:a": "accepted", "thm:b": "declined" } } })).toBe(false);
    expect(redoingOf({ weakening_repair: { status: "pending", decisions: { "thm:b": "redo" } } })).toBe(false);
    expect(redoingOf(undefined)).toBe(false);
  });
  it("the proof map marks a result Lean-proved once its proof and the lemmas it uses are closed", () => {
    const node = (id: string, state: string, kind = "lemma") => ({ id, kind, proof: { state } });
    const g = {
      nodes: [node("thm:a", "complete", "theorem"), node("lem:b", "complete"), node("lem:c", "sorry"), node("thm:d", "complete", "theorem"), node("def:e", "sorry", "definition")],
      edges: [{ kind: "proof-uses", from: "thm:a", to: "lem:b" }, { kind: "proof-uses", from: "lem:b", to: "lem:c" }, { kind: "statement-uses", from: "thm:d", to: "def:e" }],
    };
    expect([...closedProofs(g)]).toEqual(["thm:d"]);
    expect(closedProofs(null).size).toBe(0);
  });
  it("a run sent back before F2 marks nothing proved from the graph its earlier state left, and draws no Lean of the old report", async () => {
    const dir = path.join(root, "runs", "oldgraph");
    mkdirSync(path.join(dir, "discovery"), { recursive: true });
    mkdirSync(path.join(root, "Papers", "Old"), { recursive: true });
    writeFileSync(path.join(root, "Papers", "Old", "M.lean"), "theorem main : True := trivial\n");
    writeFileSync(path.join(dir, "discovery", "core.json"), JSON.stringify({ statements: [{ id: "thm:main", kind: "theorem", statement: "s" }] }));
    writeFileSync(path.join(dir, "graph.json"), JSON.stringify({ nodes: [{ id: "thm:main", kind: "theorem", proof: { state: "complete" } }], edges: [] }));
    writeFileSync(path.join(dir, "report.json"), JSON.stringify({ results: [{ node_id: "thm:main", bucket: "verified", lean: { decl: "main", file: "M.lean", line: 1 }, bookkeeping: [] }] }));
    const at = async (completed: string, phase: string) => {
      writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: completed, lean_subdir: "Papers/Old", verify: { phase } }));
      const r = (await runDetail(cfg, "oldgraph")).results[0]!;
      return { proved: r.proved, lean: Boolean(r.rows), bucket: r.bucket };
    };
    // the proof loop at work on the scaffold that stands: the graph speaks
    expect(await at("3", "formalize")).toEqual({ proved: true, lean: false, bucket: null });
    // a new core, a re-plan, a re-scaffold: the graph and the report are the earlier state's
    for (const completed of ["V1", "V1.5", "1", "1.5"]) expect(await at(completed, "formalize")).toEqual({ proved: false, lean: false, bucket: null });
    // the report of the run as it stands
    expect(await at("V6", "done")).toEqual({ proved: true, lean: true, bucket: "verified" });
  });
  it("the stage at work is the last event's when the Lean loop is past the recorded stage", async () => {
    halt("loop", "4", "2");
    expect((await runSummary(cfg, "loop")).stageIndex).toBe(7);
    expect((await runDetail(cfg, "loop")).stages.find((s) => s.id === "4")!.state).toBe("halt");
  });
  it("a run whose log ends on a stage at work, with no runner, reads as ended without a halt — not as stopped after it", async () => {
    const dir = path.join(root, "runs", "crashed");
    mkdirSync(dir, { recursive: true });
    const end = (status: string, phase = "formalization") => {
      writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "2", verify: { phase } }));
      writeFileSync(path.join(dir, "pipeline.jsonl"), JSON.stringify({ timestamp: "2026-10-03T00:00:00Z", stage: "3", status, message: "F3 proof filler: prompt 9 bytes" }) + "\n");
      return new Promise((r) => setTimeout(r, 20)).then(() => runSummary(cfg, "crashed"));
    };
    for (const status of ["dispatch", "dispatch-complete", "failed"]) {
      const s = await end(status);
      expect(s.status).toBe("needs-you");
      expect(s.headline).toBe("ended without a halt (crashed or killed) during F3 — resume the run");
    }
    attach("crashed");
    expect(await end("dispatch")).toMatchObject({ status: "agent", headline: "ended without a halt (crashed or killed) during F3 — the agent resumes the run" });
    // a run that stopped after a stage, or was sent back to the statements since, did not crash there
    expect((await end("completed")).headline).toBe("stopped after F3");
    expect((await end("dispatch", "v1")).headline).toBe("stopped after F3");
  });
  it("an agent session on another machine of the mount is attached while its orch.json is fresh, whatever its pid", async () => {
    const dir = path.join(root, "runs", "far");
    mkdirSync(dir, { recursive: true });
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: { phase: "formalization" } }));
    const file = path.join(dir, "orch.json");
    writeFileSync(file, JSON.stringify({ agent: "Claude Code", pid: 999999999, started: null, host: "another-host", attached_at: "x" }));
    expect((await runSummary(cfg, "far")).orch).toEqual({ agent: "Claude Code", since: "x", watching: false, starts: false });
    // its watcher there is armed while the file it touches every minute is fresh
    writeFileSync(file, JSON.stringify({ agent: "Claude Code", pid: 999999999, started: null, host: "another-host", attached_at: "x", watcher: 5 }));
    expect((await runSummary(cfg, "far")).orch).toMatchObject({ watching: true });
    const idle = new Date(Date.now() - 4 * 60_000);
    utimesSync(file, idle, idle);
    expect((await runSummary(cfg, "far")).orch).toEqual({ agent: "Claude Code", since: "x", watching: false, starts: false });
    // … and gone once it has not been touched for the heartbeat's allowance
    const old = new Date(Date.now() - 31 * 60_000);
    utimesSync(file, old, old);
    expect((await runSummary(cfg, "far")).orch).toBeNull();
    // on this machine the pid decides, as before
    writeFileSync(file, JSON.stringify({ agent: "Claude Code", pid: 999999999, started: null, host: os.hostname(), attached_at: "x" }));
    expect((await runSummary(cfg, "far")).orch).toBeNull();
  });
  it("a promotion round waits on the owner only once its checklist exists", async () => {
    const dir = path.join(root, "runs", "rb");
    mkdirSync(path.join(dir, "proposals"), { recursive: true });
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V6", verify: { phase: "proposals_B", promotion: { status: "pending_user", promoted: [] } } }));
    attach("rb");
    const before = await runSummary(cfg, "rb");
    expect(before).toMatchObject({ status: "agent", pending: { promotion: null } });
    expect(before.headline).toContain("not prepared yet");
    writeFileSync(path.join(dir, "proposals", "B.json"), JSON.stringify({ proposals: [] }));
    const after = await runSummary(cfg, "rb");
    expect(after).toMatchObject({ status: "needs-you", pending: { promotion: "B" } });
    expect(after.headline).toContain("decide which results join your toolkit");
  });
  it("a repair that would weaken a main result waits on the owner, with the agent's recommendation", async () => {
    const dir = path.join(root, "runs", "weak2");
    mkdirSync(dir, { recursive: true });
    const item = { node: "thm:main", printed: "the rate is $n^{-1}$", proposed: "the rate is $n^{-1/2}$", given_up: "the faster rate", detail: "the bound fails", witness: null, source: "fixer" };
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: { phase: "review", weakening_repair: { status: "pending", items: [item], at: "x" } } }));
    writeFileSync(path.join(dir, "repair_recommendations.json"), JSON.stringify({ "thm:main": { kind: "redo", why: "the printed rate is false", guidance: "state the rate for n > 1", of: repairKey(item) } }));
    attach("weak2");
    const d = await runDetail(cfg, "weak2");
    expect(d.summary).toMatchObject({ status: "needs-you" });
    expect(d.summary.headline).toContain("decide each");
    // … and its node carries the "needs you" mark of the proof map (when the core has it)
    writeFileSync(path.join(dir, "discovery.json"), "{}");
    mkdirSync(path.join(dir, "discovery"), { recursive: true });
    writeFileSync(path.join(dir, "discovery", "core.json"), JSON.stringify({ statements: [{ id: "thm:main", kind: "theorem", depends_on: [] }, { id: "lem:x", kind: "lemma", depends_on: [] }] }));
    expect((await runDetail(cfg, "weak2")).results.map((r) => [r.id, r.needs])).toEqual([["thm:main", true], ["lem:x", false]]);
    // where a repair on file changes a result: nowhere yet, its proof only, or its statement
    const place = async (patches: unknown[]) => {
      writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: { phase: "review", paper_errors: { "thm:main": { detail: "false", witness: null } } } }));
      writeFileSync(path.join(dir, "discovery", "patches.json"), JSON.stringify({ patches, unfixable: [] }));
      return (await runDetail(cfg, "weak2")).results.map((r) => r.repair);
    };
    expect(await place([])).toEqual(["none", null]);
    expect(await place([{ node: "thm:main", ops: [{ op: "replace", unit: "thm:main/proof/1/1", text: "x" }] }])).toEqual(["proof", null]);
    expect(await place([{ node: "thm:main", ops: [{ op: "replace", unit: "thm:main/1", text: "x" }] }])).toEqual(["statement", null]);
    expect(d.repairs).toEqual([{ node: "thm:main", printed: item.printed, proposed: item.proposed, given_up: item.given_up, detail: item.detail, witness: null, guidance: null, recommendation: { kind: "redo", why: "the printed rate is false", guidance: "state the rate for n > 1" } }]);
    // a recommendation made on an earlier proposal for the node (a redo since, a later round) is not this repair's
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: { phase: "review", weakening_repair: { status: "pending", items: [{ ...item, proposed: "the rate is $n^{-1/4}$" }], at: "y" } } }));
    await new Promise((r) => setTimeout(r, 20));
    expect((await runDetail(cfg, "weak2")).repairs.map((r) => r.recommendation)).toEqual([null]);
    // a receipt written with the repair's grade as its error (before the receipt kept the two apart) shows no error, not the grade twice
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: { phase: "review", weakening_repair: { status: "pending", items: [{ ...item, detail: "any repair weakens the contribution: the faster rate" }], at: "z" } } }));
    await new Promise((r) => setTimeout(r, 20));
    expect((await runDetail(cfg, "weak2")).repairs[0]).toMatchObject({ given_up: "the faster rate", detail: "" });
    // a proposal that splits the result shows its corollaries with it; an applied corollary is a result of its own, named after its parent
    const cors = [{ title: "the Gaussian case", statement: "if the errors are Gaussian the rate is $n^{-1}$" }];
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: { phase: "review", weakening_repair: { status: "pending", items: [{ ...item, corollaries: cors }], at: "x" } } }));
    writeFileSync(path.join(dir, "discovery", "core.json"), JSON.stringify({ statements: [{ id: "thm:main", kind: "theorem", depends_on: [] }, { id: "thm:cor-fix-0a1b2c3d", kind: "theorem", depends_on: ["thm:main"], split_from: "thm:main" }] }));
    const split = await runDetail(cfg, "weak2");
    expect(split.repairs[0]!.corollaries).toEqual(cors);
    expect(split.results.map((r) => [r.id, r.splitFrom ?? null, r.deps])).toEqual([["thm:main", null, []], ["thm:cor-fix-0a1b2c3d", "thm:main", ["thm:main"]]]);
  });
  it("a finding the owner withdrew is no error of the paper: its result is not marked one, and no repair is said to be missing", async () => {
    const dir = path.join(root, "runs", "withdrawn");
    mkdirSync(path.join(dir, "discovery"), { recursive: true });
    const entry = { detail: "the square is misplaced", witness: null };
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: { phase: "review", paper_errors: {
      "prop:kept": { ...entry, owner_decision: "finding rejected", decision_reason: "a typesetting slip", owner_overruled: true }, "prop:open": entry,
    } } }));
    writeFileSync(path.join(dir, "discovery", "core.json"), JSON.stringify({ statements: [{ id: "prop:kept", kind: "proposition" }, { id: "prop:open", kind: "proposition" }] }));
    writeFileSync(path.join(dir, "discovery", "v1_5_review.json"), JSON.stringify({ nodes: [{ id: "prop:kept", ambiguity: "pinned", correctness: "bookkeeping" }] }));
    expect((await runDetail(cfg, "withdrawn")).results.map((r) => [r.id, r.state, r.repair, r.paperError?.kind ?? null])).toEqual([
      ["prop:kept", "minor", null, null], ["prop:open", "error", "none", "error"],
    ]);
  });
  it("a live runner that has logged nothing since it started is not where the log ends: sent back to repair, it is in V1", async () => {
    const dir = path.join(root, "runs", "back");
    mkdirSync(path.join(dir, "logs"), { recursive: true });
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V1", verify: { phase: "v1" } }));
    writeFileSync(path.join(dir, "pipeline.jsonl"), JSON.stringify({ timestamp: "2026-10-03T00:00:00Z", stage: "4", status: "checkpoint", message: "PROOF-REVIEW LOOP ESCALATION" }) + "\n");
    writeFileSync(path.join(dir, "logs", ".run.active"), `${process.pid} 2026-10-03T01:00:00Z x\n`);
    expect(await runSummary(cfg, "back")).toMatchObject({ status: "running", stageIndex: -1, headline: "V1 · revising the statements sent back", lastEvent: null });
    // once it logs, the log says where it is
    appendFileSync(path.join(dir, "pipeline.jsonl"), JSON.stringify({ timestamp: "2026-10-03T02:00:00Z", stage: "V1.5", status: "dispatch", message: "V1.5 referee" }) + "\n");
    expect((await runSummary(cfg, "back")).headline).toContain("V1.5");
  });
  it("the stage a run is at comes from its phase; the event log only places it within the Lean stages", () => {
    // sent back to V1 or V1.5, whatever its log still ends with
    expect(stageIndexOf("init", "V1", "4")).toBe(-1);
    expect(stageIndexOf("v1", "V1", "4")).toBe(0);
    expect(stageIndexOf("v1_5", "V1.5", "4")).toBe(1);
    // within the Lean stages the last event tells, a referee event never does
    expect(stageIndexOf("formalization", "V1.5", "4")).toBe(7);
    expect(stageIndexOf("formalization", "2", "V1.5")).toBe(4);
    expect(stageIndexOf("formalization", "V1.5", null)).toBe(1);
    expect(stageIndexOf("proposals_B", "5", "4")).toBe(9);
    expect(stageIndexOf("done", "V6", "4")).toBe(10);
    // the Lean loop moves back as well as on (a review sends the scaffold back, a core revision the
    // plan): the stage in progress is the latest event's, whatever stage the state last recorded done
    expect(stageIndexOf("formalization", "3.5", "1")).toBe(1);
    expect(stageIndexOf("formalization", "1.5", "2", "dispatch")).toBe(3);
    // … and done when the event completes it
    expect(stageIndexOf("formalization", "1.5", "2", "completed")).toBe(4);
  });
  it("a receipt its confirming pass has not settled is not the owner's yet: no decision card, the run is to be resumed", async () => {
    const dir = path.join(root, "runs", "unconf");
    mkdirSync(dir, { recursive: true });
    const receipt = { status: "pending", unconfirmed: true, items: [{ node: "thm:a", printed: "x", proposed: "p", given_up: "g", detail: "d", witness: null }], at: "x" };
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V1", verify: { phase: "v1", weakening_repair: receipt } }));
    const d = await runDetail(cfg, "unconf");
    expect(d.repairs).toEqual([]);
    expect(d.summary).toMatchObject({ status: "needs-you", pending: { weakening: 0 } });
    expect(d.summary.headline).toContain("still being confirmed by the review — nothing to decide yet; resume the run");
    attach("unconf");
    expect((await runSummary(cfg, "unconf")).status).toBe("agent");
  });
  it("a render or contract checkpoint is shown as what it is — the agent's, before every ruling: no decision card behind it, no ruling sent into it", async () => {
    const dir = path.join(root, "runs", "rcp");
    mkdirSync(dir, { recursive: true });
    const receipt = { status: "pending", items: [{ node: "thm:a", printed: "x", proposed: "p", given_up: "g", detail: "d", witness: null }], at: "x" };
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: { phase: "v1", weakening_repair: receipt, render_checkpoint: { kind: "contract", when: "V1.5", defects: [{}, {}], at: "x" } } }));
    const d = await runDetail(cfg, "rcp");
    expect(d.repairs).toEqual([]);
    expect(d.summary).toMatchObject({ status: "needs-you", pending: { weakening: 0 } });
    expect(d.summary.headline).toMatch(/^contract checkpoint: 2 block\(s\)[\s\S]*no decision of yours is read until it is cleared/);
    attach("rcp");
    expect((await runSummary(cfg, "rcp")).status).toBe("agent");
    // cleared, the receipt is the owner's again
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: { phase: "v1", weakening_repair: receipt, render_checkpoint: null } }));
    await new Promise((r) => setTimeout(r, 20));
    expect((await runDetail(cfg, "rcp")).repairs).toHaveLength(1);
  });
  it("a report on file from before the run was sent back is not shown as the run's: no verdict, no bucket on a result", async () => {
    const dir = path.join(root, "runs", "rewound");
    mkdirSync(path.join(dir, "discovery"), { recursive: true });
    writeFileSync(path.join(dir, "discovery", "core.json"), JSON.stringify({ statements: [{ id: "thm:main", kind: "theorem", depends_on: [] }] }));
    writeFileSync(path.join(dir, "report.json"), JSON.stringify({ verdict: "no_error_found", summary: { verified: 1 }, results: [{ node_id: "thm:main", bucket: "verified", lean: null, bookkeeping: [{ id: "ass:bk-1", condition: "c", reason: "r" }], added_premises: [{ label: "ass:filler:1", statement: "$X$ is integrable", classification: "regularity-bookkeeping" }], assumed_substrate: [{ id: "gate:g", description: "a concentration bound" }] }] }));
    const at = (stage: string, phase: string) => { writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: stage, verify: { phase } })); return new Promise((r) => setTimeout(r, 20)).then(() => runDetail(cfg, "rewound")); };
    const done = await at("V6", "done");
    expect(done.summary).toMatchObject({ verdict: "no_error_found", buckets: { verified: 1 } });
    expect(done.results.map((r) => r.bucket)).toEqual(["verified"]);
    // the drawer lists every condition the report gives the result under, not V1.5's side conditions alone
    expect(done.results[0]!.conditions.map((c) => c.id)).toEqual(["ass:bk-1", "ass:filler:1", "gate:g"]);
    // a run that ended in its report without Lean (a refutation at V1.5: phase `failed`) is done, with its verdict
    const refuted = await at("V1.5", "failed");
    expect(refuted.summary).toMatchObject({ status: "done", verdict: "no_error_found" });
    const back = await at("V1", "v1");
    expect(back.summary).toMatchObject({ verdict: null, buckets: null });
    expect(back.results.map((r) => r.bucket)).toEqual([null]);
  });
  it("a run the page has just started reads running before its runner's heartbeat — while that process lives", async () => {
    const dir = path.join(root, "runs", "sent");
    mkdirSync(path.join(dir, "logs"), { recursive: true });
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: { phase: "review", weakening_repair: { status: "pending", items: [{ node: "thm:a", proposed: "p", given_up: "g", detail: "d", witness: null }], at: "x" } } }));
    expect((await runSummary(cfg, "sent")).status).toBe("needs-you");
    markStarted(cfg, "sent", process.pid);
    expect(await runSummary(cfg, "sent")).toMatchObject({ status: "running", live: true, headline: "starting — taking up what you sent" });
    // while the runner lives the suggestion is not yet the owner's to rule on: no decision card
    expect((await runDetail(cfg, "sent")).repairs).toEqual([]);
    expect(runLive(cfg, "sent")).toEqual({ live: true, pid: process.pid, starting: true });
    // a start whose process is gone, or an old one, says nothing
    writeFileSync(path.join(dir, "logs", ".ui.started"), `${process.pid} 2020-01-01T00:00:00.000Z\n`);
    expect((await runSummary(cfg, "sent")).status).toBe("needs-you");
  });
  it("the list's title is the paper's though a file the main one inputs sets it", async () => {
    const dir = path.join(root, "runs", "inp");
    mkdirSync(path.join(dir, "source"), { recursive: true });
    mkdirSync(path.join(dir, "discovery"), { recursive: true });
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V1", verify: { phase: "v1_5", source: { main_file: "main.tex" } } }));
    writeFileSync(path.join(dir, "source", "main.tex"), "\\documentclass{article}\n\\begin{document}\n\\input{title}\nText.\n\\end{document}\n");
    writeFileSync(path.join(dir, "source", "title.tex"), "\\title{Set Elsewhere}\n");
    expect((await runSummary(cfg, "inp")).title).toBe("inp");
    writeFileSync(path.join(dir, "discovery", "flat.tex"), "\\documentclass{article}\n\\begin{document}\n\\title{Set Elsewhere}\nText.\n\\end{document}\n");
    expect((await runSummary(cfg, "inp")).title).toBe("Set Elsewhere");
  });
  it("a promotion round being applied reads running, and one stopped part-way is the agent's", async () => {
    const dir = path.join(root, "runs", "app");
    mkdirSync(path.join(dir, "proposals"), { recursive: true });
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V6", verify: { phase: "proposals_B", promotion: { status: "pending_user", promoted: [] } } }));
    writeFileSync(path.join(dir, "proposals", "B.json"), JSON.stringify({ slug: "app", round: "B", created: "x", proposals: [] }));
    attach("app");
    expect((await runSummary(cfg, "app")).status).toBe("needs-you");
    writeFileSync(path.join(dir, "proposals", "apply_B.pid"), `${process.pid}\n`);
    const applying = await runSummary(cfg, "app");
    expect(applying.status).toBe("running");
    expect(applying.headline).toContain("applying promotion round B");
    // the paper is being worked on though no runner beats: the bar's next stage is the current one
    expect((await runDetail(cfg, "app")).stages.filter((s) => s.state === "current")).toHaveLength(1);
    // an apply on another machine of the mount is read by the file's freshness, not by its pid here
    writeFileSync(path.join(dir, "proposals", "apply_B.pid"), "999999999 host=another-host beat=60\n");
    expect((await runSummary(cfg, "app")).headline).toContain("applying promotion round B");
    const stale = new Date(Date.now() - 10 * 60_000);
    utimesSync(path.join(dir, "proposals", "apply_B.pid"), stale, stale);
    expect((await runSummary(cfg, "app")).headline).not.toContain("applying promotion round B");
    // the apply ended without finishing the round
    writeFileSync(path.join(dir, "proposals", "apply_B.pid"), "999999999\n");
    writeFileSync(path.join(dir, "proposals", "B.decisions.json"), JSON.stringify({ decided_at: "y" }));
    await new Promise((r) => setTimeout(r, 30));
    const stopped = await runSummary(cfg, "app");
    expect(stopped.status).toBe("agent");
    expect(stopped.headline).toContain("applied in part");
  });
  it("the decisions of an earlier round, left beside a batch proposed afresh, are no apply of it: the round waits on the owner", async () => {
    const dir = path.join(root, "runs", "again");
    mkdirSync(path.join(dir, "proposals"), { recursive: true });
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V6", verify: { phase: "proposals_B", promotion: { status: "pending_user", promoted: [] } } }));
    writeFileSync(path.join(dir, "proposals", "B.json"), JSON.stringify({ slug: "again", round: "B", created: "2026-10-07T00:00:00.000Z", proposals: [] }));
    writeFileSync(path.join(dir, "proposals", "B.decisions.json"), JSON.stringify({ slug: "again", round: "B", decisions: {}, decided_at: "2026-10-01T00:00:00.000Z" }));
    attach("again");
    const s = await runSummary(cfg, "again");
    expect(s.status).toBe("needs-you");
    expect(s.headline).toContain("decide which results join your toolkit");
    // an apply refused before it recorded a decision: the round still waits, and the page says why
    writeFileSync(path.join(dir, "proposals", "B.decisions.json"), JSON.stringify({ decided_at: "2026-10-01T00:00:00.000Z" }));
    writeFileSync(path.join(dir, "proposals", "apply_failed.json"), JSON.stringify({ round: "B", at: "2026-10-07T00:30:00.000Z", message: "refusing --apply:\n  b-one is still pending" }));
    await new Promise((r) => setTimeout(r, 30));
    const refused = await runDetail(cfg, "again");
    expect(refused.summary).toMatchObject({ status: "needs-you", headline: "promotion round B was not applied — refusing --apply:" });
    expect(refused.promotion).toMatchObject({ applied: false, refusal: "refusing --apply:\n  b-one is still pending" });
    rmSync(path.join(dir, "proposals", "apply_failed.json"));
    // decided after the batch was written, it is this round's apply
    writeFileSync(path.join(dir, "proposals", "B.decisions.json"), JSON.stringify({ decided_at: "2026-10-07T01:00:00.000Z" }));
    await new Promise((r) => setTimeout(r, 30));
    expect((await runSummary(cfg, "again")).headline).toContain("applied in part");
    // the apply completed (the state says so) and the resume after it died before its heartbeat: applied, to resume
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V6", verify: { phase: "proposals_B", promotion: { status: "applied", promoted: [] } } }));
    await new Promise((r) => setTimeout(r, 30));
    expect(await runSummary(cfg, "again")).toMatchObject({ headline: "promotion round B is applied — the agent resumes the run", toResume: true });
  });
  it("a batch an earlier state of the run left is not the round to decide: the run was sent back and stopped before round B was proposed again", async () => {
    const dir = path.join(root, "runs", "oldround");
    mkdirSync(path.join(dir, "proposals"), { recursive: true });
    writeFileSync(path.join(dir, "proposals", "B.json"), JSON.stringify({ slug: "oldround", round: "B", created: "2026-10-01T00:00:00Z", proposals: [] }));
    // (`--from-stage V1 --stop-after V6`: the report is written, the state holds no record of round B)
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V6", verify: { phase: "proposals_B" } }));
    expect((await runSummary(cfg, "oldround")).headline).toContain("promotion round B is not prepared yet");
    expect((await runDetail(cfg, "oldround")).promotion).toMatchObject({ round: "B", waiting: false });
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V6", verify: { phase: "proposals_B", promotion: { status: "pending_user", promoted: [] } } }));
    await new Promise((r) => setTimeout(r, 30));
    expect((await runSummary(cfg, "oldround")).headline).toContain("promotion round B: decide which results join your toolkit");
    expect((await runDetail(cfg, "oldround")).promotion).toMatchObject({ round: "B", waiting: true });
  });
  it("an entry of a promotion round shows the agent's recommendation beside it", async () => {
    const dir = path.join(root, "runs", "rec");
    mkdirSync(path.join(dir, "proposals"), { recursive: true });
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V6", verify: { phase: "proposals_B", promotion: { status: "pending_user", promoted: [] } } }));
    const entry = (id: string) => ({ id, round: "B", source: { kind: "paper_decl", ref: `Papers.X.${id}` }, verdict: "propose", title: id, reference: "r", content: "c", division: "Foundations", target_module: "Toolkit/Foundations/A/B.lean", new_module_overview: null, proposed_name: `Toolkit.Foundations.A.${id}`, nearest_existing: [], reuse_evidence: "e" });
    writeFileSync(path.join(dir, "proposals", "B.json"), JSON.stringify({ slug: "rec", round: "B", created: "2026-10-06T00:00:00Z", proposals: [entry("one"), { ...entry("two"), new_topic: { path: "Foundations/New", scope: "s" } }] }));
    const { recommendationKeys } = await import("../../src/proposals/checklist.js");
    const keys = recommendationKeys(JSON.parse(readFileSync(path.join(dir, "proposals", "B.json"), "utf8")));
    // (one written for another proposal of the same id — or bound to none — is not shown)
    writeFileSync(path.join(dir, "proposals", "B.recommendations.json"), JSON.stringify({ one: { kind: "defer", why: "nearly a one-line fact", of: keys.get("one") }, two: { kind: "accept", why: "on an earlier batch's entry", of: "0000000000000000" }, "topic:Foundations/New": { kind: "accept", why: "nothing else holds it", of: keys.get("topic:Foundations/New") } }));
    const pr = (await runDetail(cfg, "rec")).promotion!;
    expect(pr.proposals.map((p) => p.recommendation)).toEqual([{ kind: "defer", why: "nearly a one-line fact" }, null]);
    // … and so does a new topic the round asks about, recommended by its key
    expect(pr.topics).toMatchObject([{ key: "topic:Foundations/New", recommendation: { kind: "accept", why: "nothing else holds it" } }]);
  });
  it("every halt is the attached agent's; with none attached it asks the owner for one", async () => {
    halt("f3", "3", "2.5");
    halt("v15", "V1.5", "V1");
    expect(await runSummary(cfg, "f3")).toMatchObject({ status: "needs-you", orch: null });
    expect((await runSummary(cfg, "f3")).headline).toContain("no agent attached");
    attach("f3"); attach("v15");
    expect(await runSummary(cfg, "f3")).toMatchObject({ status: "agent", orch: { agent: "Claude Code" } });
    expect((await runDetail(cfg, "f3")).stages.find((s) => s.id === "3")!.state).toBe("halt");
    expect((await runSummary(cfg, "v15")).status).toBe("agent");
  });
  it("a run redone on the same paper is superseded by the later one, and waits on no one", async () => {
    for (const [slug, at] of [["old", 1_000_000], ["redo", 2_000_000]] as const) {
      mkdirSync(path.join(root, "runs", slug), { recursive: true });
      const st = path.join(root, "runs", slug, "state.json");
      writeFileSync(st, JSON.stringify({ stage_completed: "V1", verify: { phase: "v1", source: { sha256: "abc" } } }));
      writeFileSync(path.join(root, "runs", slug, "pipeline.jsonl"), JSON.stringify({ stage: "V1.5", status: "checkpoint", message: "halt" }) + "\n");
      for (const f of [st, path.join(root, "runs", slug, "pipeline.jsonl")]) utimesSync(f, at, at);
    }
    expect(await runSummary(cfg, "old")).toMatchObject({ status: "superseded", supersededBy: "redo" });
    expect(await runSummary(cfg, "redo")).toMatchObject({ status: "needs-you", supersededBy: null });
    // the toolkit's list works the same out for all its runs in one pass
    const newer = await newerRuns(cfg, ["old", "redo"]);
    expect([...newer]).toEqual([["old", "redo"], ["redo", null]]);
    expect(await runSummary(cfg, "old", newer)).toMatchObject({ status: "superseded", supersededBy: "redo" });
  });
  it("sums the run's token ledger, counting the calls whose usage could not be read", async () => {
    halt("tok", "3", "2.5");
    const u = (input: number, cached: number, output: number) => ({ input_tokens: input, cached_input_tokens: cached, cache_creation_input_tokens: 0, output_tokens: output, reasoning_output_tokens: 0, total_tokens: input + output });
    writeFileSync(path.join(root, "runs", "tok", "token_usage.jsonl"), [
      { stage: "V1", usage: u(1000, 400, 50) }, { stage: "F3", usage: u(2000, 1500, 70) }, { stage: "F3", usage: null },
    ].map((r) => JSON.stringify({ timestamp: "x", provider: "codex", model: "m", duration_ms: 1, success: true, ...r })).join("\n") + "\n");
    expect((await runSummary(cfg, "tok")).tokens).toEqual({ calls: 3, uncounted: 1, input: 3000, cached: 1900, output: 120, total: 3120 });
  });
  it("a weakened main result is the owner's to decide on the page; a ruling the agent makes elsewhere waits for the owner's review", async () => {
    mkdirSync(path.join(root, "runs", "weak"), { recursive: true });
    writeFileSync(path.join(root, "runs", "weak", "state.json"), JSON.stringify({ stage_completed: "V1", verify: { phase: "v1", weakening_repair: { status: "pending", at: "x", items: [{ node: "thm:a", proposed: "p", given_up: "g", detail: "d", witness: "w" }] } } }));
    attach("weak");
    expect((await runSummary(cfg, "weak")).status).toBe("needs-you");
    // a ruling of the agent's, once the run went on: the ruling waits for review, the result shows it
    writeFileSync(path.join(root, "runs", "weak", "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: { phase: "formalize" } }));
    writeFileSync(path.join(root, "runs", "weak", "orch_decisions.json"), JSON.stringify([{ id: "d1", node: "thm:a", at: "x", text: "accepted the repair: the bound holds only for n ≥ 2" }]));
    expect(await runSummary(cfg, "weak")).toMatchObject({ status: "needs-you", reviews: [expect.objectContaining({ id: "d1" })] });
    writeFileSync(path.join(root, "runs", "weak", "orch_decisions.json"), JSON.stringify([{ id: "d1", node: "thm:a", at: "x", text: "…", review: { verdict: "approve", at: "y" } }]));
    expect((await runSummary(cfg, "weak")).reviews).toEqual([]);
  });
});

describe("server: 127.0.0.1, a session key, the Host header", () => {
  let ui: UiServer;
  const root = mkdtempSync(path.join(tmpdir(), "tc-ui-"));
  mkdirSync(path.join(root, "runs", "r1", "source"), { recursive: true });
  writeFileSync(path.join(root, "paperformalizer.json"), "{}");
  writeFileSync(path.join(root, "runs", "r1", "state.json"), "{}");
  writeFileSync(path.join(root, "runs", "r1", "source", "Fig.SVG"), "<svg xmlns='http://www.w3.org/2000/svg'><script>alert(1)</script></svg>");
  const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs"), lib: "Toolkit", papersLib: "Papers", divisions: ["Foundations"], baseLibraries: [], owner: { name: "Owner" }, leanToolchain: "leanprover/lean4:v4.33.0" } as unknown as ToolkitConfig;
  afterAll(async () => { await ui?.close(); });
  it("hands the key over once, then serves the API only with the cookie and the right Host", async () => {
    ui = await startUiServer(cfg, { port: 0 });
    const base = new URL(ui.url).origin;
    expect((await fetch(`${base}/api/toolkit`)).status).toBe(403);
    expect((await fetch(`${base}/`)).status).toBe(403);
    const hand = await fetch(ui.url, { redirect: "manual" });
    expect(hand.status).toBe(302);
    const cookie = (hand.headers.get("set-cookie") ?? "").split(";")[0]!;
    // one cookie per port: a second UI on this host does not overwrite this one's key
    expect(cookie.startsWith(`tc_token_${new URL(base).port}=`)).toBe(true);
    expect(hand.headers.get("set-cookie")).toMatch(/HttpOnly; SameSite=Strict/);
    const ok = await fetch(`${base}/api/toolkit`, { headers: { Cookie: cookie } });
    expect(ok.status).toBe(200);
    expect(((await ok.json()) as { runs: Array<{ slug: string }> }).runs.map((r) => r.slug)).toEqual(["r1"]);
    // a paper's figure: its type whatever the extension's case, an SVG sandboxed, nothing outside the folder
    const svg = await fetch(`${base}/api/runs/r1/asset/Fig.SVG`, { headers: { Cookie: cookie } });
    expect(svg.headers.get("content-type")).toBe("image/svg+xml");
    expect(svg.headers.get("content-security-policy")).toContain("sandbox");
    expect((await fetch(`${base}/api/runs/r1/asset/..%2Fstate.json.png`, { headers: { Cookie: cookie } })).status).toBe(404);
    // a run name that is not a directory name is refused; a POST without the page's header too
    expect((await fetch(`${base}/api/runs/a:b/delegate`, { method: "POST", headers: { Cookie: cookie, "X-TC": "1" }, body: "{}" })).status).toBe(404);
    expect((await fetch(`${base}/api/runs/r1/delegate`, { method: "POST", headers: { Cookie: cookie }, body: "{}" })).status).toBe(403);
    const etag = (await fetch(`${base}/api/toolkit`, { headers: { Cookie: cookie } })).headers.get("etag")!;
    expect((await fetch(`${base}/api/toolkit`, { headers: { Cookie: cookie, "If-None-Match": etag } })).status).toBe(304);
    // the list is built again once the watcher sees a change (a new run): the old tag no longer holds
    mkdirSync(path.join(root, "runs", "r2"), { recursive: true });
    writeFileSync(path.join(root, "runs", "r2", "state.json"), "{}");
    let again: Response | null = null;
    for (let k = 0; k < 60 && (again?.status ?? 304) === 304; k++) { await new Promise((r) => setTimeout(r, 100)); again = await fetch(`${base}/api/toolkit`, { headers: { Cookie: cookie, "If-None-Match": etag } }); }
    expect(again!.status).toBe(200);
    expect(((await again!.json()) as { runs: Array<{ slug: string }> }).runs.map((r) => r.slug).sort()).toEqual(["r1", "r2"]);
    rmSync(path.join(root, "runs", "r2"), { recursive: true, force: true });
    // a browser that takes brotli is sent brotli, the same JSON
    const br = await new Promise<{ enc: string | undefined; body: Buffer }>((resolve) => {
      http.get({ host: "127.0.0.1", port: Number(new URL(base).port), path: "/api/toolkit", headers: { Cookie: cookie, "Accept-Encoding": "gzip, br" } }, (res) => {
        const parts: Buffer[] = []; res.on("data", (d: Buffer) => parts.push(d)); res.on("end", () => resolve({ enc: res.headers["content-encoding"], body: Buffer.concat(parts) }));
      });
    });
    expect(br.enc).toBe("br");
    expect((JSON.parse(brotliDecompressSync(br.body).toString("utf8")) as { runs: unknown[] }).runs.length).toBeGreaterThan(0);
    // an SSH forward to another local port is served; a foreign host name (DNS rebinding) is refused
    const viaHost = (host: string) => new Promise<number>((resolve) => {
      const r = http.request({ host: "127.0.0.1", port: Number(new URL(base).port), path: "/api/toolkit", headers: { Host: host, Cookie: cookie } }, (res) => { res.resume(); resolve(res.statusCode ?? 0); });
      r.end();
    });
    expect(await viaHost("localhost:9999")).toBe(200);
    expect(await viaHost(`evil.example:${new URL(base).port}`)).toBe(421);
  });
  it("one UI per toolkit: a second `paperformalizer ui` finds the running one, and not after it stops", async () => {
    writeUiState(cfg, ui);
    expect(await runningUi(cfg)).toBe(ui.url);
    await ui.close();
    ui = undefined as unknown as UiServer;
    expect(await runningUi(cfg)).toBeNull();
  });
});

describe("orch.mjs: an interactive agent session attached to a run", () => {
  const script = path.join(__dirname, "..", "..", "scripts", "orch.mjs");
  it("attaches, asks the owner on the page, records a ruling and wakes on its rejection", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-orch-"));
    const run = path.join(root, "runs", "o1");
    mkdirSync(path.join(run, "logs"), { recursive: true });
    writeFileSync(path.join(run, "state.json"), JSON.stringify({ stage_completed: "2", verify: { phase: "formalization" } }));
    const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs") } as unknown as ToolkitConfig;
    const orch = (...args: string[]) => spawnSync(process.execPath, [script, args[0]!, "o1", "--toolkit", root, ...args.slice(1)], { encoding: "utf8" });
    // nothing to act on: it waits, and says so when its timeout ends
    expect(orch("watch", "--timeout", "1").status).toBe(2);
    expect((await runSummary(cfg, "o1")).orch).not.toBeNull();
    expect(orch("ask", "Please find the cited 1975 book page.").stdout.trim()).toBe("q1");
    // a text the page would set as one runaway formula (a shell ate "$X" in double quotes) is refused
    const eaten = orch("ask", "If $ is atomless then $-\\log S(X)$ is exponential.");
    expect([eaten.status, eaten.stderr]).toEqual([65, expect.stringContaining("unclosed $")]);
    expect(orch("decided", "thm:a", "the bound holds for =1/2$").status).toBe(65);
    expect(await runSummary(cfg, "o1")).toMatchObject({ status: "needs-you", requests: [expect.objectContaining({ id: "q1" })] });
    orch("done", "q1");
    expect((await runSummary(cfg, "o1")).requests).toEqual([]);
    // a ruling for the owner's review; their rejection (with guidance) wakes the watcher at once
    expect(orch("decided", "thm:a", "Accepted the repair: the bound holds for n ≥ 2.").stdout.trim()).toBe("d1");
    expect((await runSummary(cfg, "o1")).reviews).toHaveLength(1);
    const file = path.join(run, "orch_decisions.json");
    const rejected = JSON.parse(readFileSync(file, "utf8")) as Array<Record<string, unknown>>;
    rejected[0]!.review = { verdict: "reject", guidance: "Keep n ≥ 1; prove the bound directly.", at: "y" };
    writeFileSync(file, JSON.stringify(rejected));
    const woke = orch("watch", "--timeout", "30");
    expect(woke.status).toBe(0);
    expect(woke.stdout).toContain("Keep n ≥ 1");
    orch("handled", "d1");
    expect(orch("watch", "--timeout", "1").status).toBe(2);
    // formulas the page could not draw wake the watcher once per list, with the commonest error
    writeFileSync(path.join(run, "logs", "ui_math_failures.json"), JSON.stringify({ failures: [{ tex: "\\indicator(a)", error: "Undefined control sequence \\indicator" }, { tex: "\\indicator(b)", error: "Undefined control sequence \\indicator" }, { tex: "\\odd", error: "Other" }] }));
    const math = orch("watch", "--timeout", "30");
    expect([math.status, math.stdout]).toEqual([0, expect.stringMatching(/cannot draw 3 formula\(s\) of this paper — 2 with "Undefined control sequence \\indicator", e\.g\. \\indicator\(a\)[^]*ui_math_overrides\.json/)]);
    expect(orch("watch", "--timeout", "1").status).toBe(2);
    // anything else the page could not draw wakes it once per list too
    writeFileSync(path.join(run, "logs", "ui_render_problems.json"), JSON.stringify({ unknownCommands: { tikzset: 3 }, unknownEnvironments: {}, missingFigures: ["fig/a.png"], omittedDrawings: 2, tikz: "pdflatex exited 1: ! Package pgfkeys Error", unresolvedRefs: [] }));
    const render = orch("watch", "--timeout", "30");
    expect([render.status, render.stdout]).toEqual([0, expect.stringMatching(/cannot draw parts of this paper — commands it does not read[^]*\\tikzset ×3[^]*fig\/a\.png[^]*2 drawing\(s\) left out[^]*pgfkeys Error/)]);
    expect(orch("watch", "--timeout", "1").status).toBe(2);
    // a finished run whose bundle has blocking TODO items wakes it once per bundle written; a run not
    // finished (an older bundle of a run rewound) is not woken for its bundle
    mkdirSync(path.join(run, "bundle"), { recursive: true });
    writeFileSync(path.join(run, "bundle", "bundle.json"), JSON.stringify({ todo: { total: 3, blocking: 2 } }));
    const stateFile = path.join(run, "state.json");
    const stateNow = existsSync(stateFile) ? readFileSync(stateFile, "utf8") : "{}";
    writeFileSync(stateFile, JSON.stringify({ ...JSON.parse(stateNow), stage_completed: "V1", verify: { phase: "v1" } }));
    expect(orch("watch", "--timeout", "1").status).toBe(2);
    // finished short of F5 (stopped at V1.5, its cursor left there) is finished: it wakes
    writeFileSync(stateFile, JSON.stringify({ ...JSON.parse(stateNow), stage_completed: "V1.5", verify: { phase: "failed" } }));
    expect(orch("watch", "--timeout", "30").stdout).toContain("2 blocking item(s)");
    rmSync(path.join(run, "logs", "bundle_todo.told"), { force: true });
    // … and a round-B promotion waiting for the user does not hold the wake back
    writeFileSync(stateFile, JSON.stringify({ ...JSON.parse(stateNow), stage_completed: "V6", verify: { phase: "proposals_B", promotion: { status: "pending_user" } } }));
    const todo = orch("watch", "--timeout", "30");
    expect([todo.status, todo.stdout]).toEqual([0, expect.stringContaining("2 blocking item(s) in bundle/corrected_paper/TODO.md")]);
    expect(orch("watch", "--timeout", "1").status).toBe(2);
    writeFileSync(path.join(run, "bundle", "bundle.json"), JSON.stringify({ todo: { total: 3, blocking: 1 } }));
    expect(orch("watch", "--timeout", "30").stdout).toContain("1 blocking item(s)");
    writeFileSync(path.join(run, "bundle", "bundle.json"), JSON.stringify({ todo: { total: 1, blocking: 0 } }));
    expect(orch("watch", "--timeout", "1").status).toBe(2);
  });
});

describe("orch.mjs: a run that is not there yet, and --help", () => {
  const script = path.join(__dirname, "..", "..", "scripts", "orch.mjs");
  it("watch waits for a run launched a moment ago; a run that never appears is exit 66", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-orch0-"));
    const env = { ...process.env, PAPERFORMALIZER_ORCH_APPEAR_MS: "20000" };
    const c = spawn(process.execPath, [script, "watch", "late", "--toolkit", root, "--timeout", "1"], { env });
    const exit = new Promise<number | null>((resolve) => c.on("exit", resolve));
    await new Promise((r) => setTimeout(r, 1200));
    expect(c.exitCode).toBeNull();
    mkdirSync(path.join(root, "runs", "late"), { recursive: true });
    writeFileSync(path.join(root, "runs", "late", "state.json"), "{}");
    expect(await exit).toBe(2);
    const never = spawnSync(process.execPath, [script, "watch", "none", "--toolkit", root], { encoding: "utf8", env: { ...env, PAPERFORMALIZER_ORCH_APPEAR_MS: "600" } });
    expect([never.status, never.stderr]).toEqual([66, expect.stringContaining("no run none under")]);
    // another verb does not wait
    const t0 = Date.now();
    expect(spawnSync(process.execPath, [script, "ask", "none", "--toolkit", root, "x"], { encoding: "utf8", env }).status).toBe(66);
    expect(Date.now() - t0).toBeLessThan(10_000);
  }, 60_000);

  it("--help prints what each verb does and exits 0", () => {
    for (const args of [["--help"], ["-h"], ["watch", "--help"]]) {
      const r = spawnSync(process.execPath, [script, ...args], { encoding: "utf8" });
      expect(r.status).toBe(0);
      for (const verb of ["watch", "decided", "handled", "ask", "reply", "recommend", "done", "detach"]) expect(r.stdout).toContain(`orch.mjs ${verb} <slug> --toolkit <path>`);
      expect(r.stdout).toContain("Exit codes:");
      expect(r.stdout).not.toMatch(/^import /m);
    }
  });

  // The finding: an ask naming `\eqref{transrelation}` for the paper's `\label{eq:transrelation}` was drawn "??".
  it("refuses a text that references a label the paper does not have", () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-orchref-"));
    mkdirSync(path.join(root, "runs", "r", "discovery"), { recursive: true });
    writeFileSync(path.join(root, "runs", "r", "state.json"), "{}");
    writeFileSync(path.join(root, "runs", "r", "discovery", "flat.tex"), String.raw`\begin{equation}\label{eq:trans
  relation}x\end{equation}`);
    const bad = spawnSync(process.execPath, [script, "ask", "r", "--toolkit", root, String.raw`see \eqref{transrelation}`], { encoding: "utf8" });
    expect([bad.status, bad.stderr]).toEqual([65, expect.stringContaining(`no label "transrelation"`)]);
    expect(spawnSync(process.execPath, [script, "ask", "r", "--toolkit", root, String.raw`see \eqref{eq:trans relation}`], { encoding: "utf8" }).status).toBe(0);
    // what the page also resolves: a macro wrapping \label, a space before the brace, the .aux, the annotator's sections
    writeFileSync(path.join(root, "runs", "r", "discovery", "flat.tex"), String.raw`\newcommand{\lbl}[1]{\label{#1}}\begin{document}\section{A}\lbl{s:a} \label {s:c}`);
    mkdirSync(path.join(root, "runs", "r", "annotated"), { recursive: true });
    writeFileSync(path.join(root, "runs", "r", "annotated", "main.aux"), String.raw`\newlabel{sup:x}{{3}{4}}`);
    expect(spawnSync(process.execPath, [script, "ask", "r", "--toolkit", root, String.raw`\ref{s:a}, \ref{s:c}, \ref{sup:x}, \ref{vsSec2}`], { encoding: "utf8" }).status).toBe(0);
  });
});

describe("orch.mjs recommend: a recommendation is on one proposal", () => {
  const script = path.join(__dirname, "..", "..", "scripts", "orch.mjs");
  it("is bound to the repair pending on the node, refused when none is, and gone from the page once the repair is another", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-orch-rec-"));
    const run = path.join(root, "runs", "o1");
    mkdirSync(path.join(run, "proposals"), { recursive: true });
    const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs") } as unknown as ToolkitConfig;
    const item = (node: string, proposed: string) => ({ node, printed: "p", proposed, given_up: "g", detail: "d", witness: null });
    const pending = (...items: unknown[]) => writeFileSync(path.join(run, "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: { phase: "review", weakening_repair: { status: "pending", items, at: String(Math.random()) } } }));
    const orch = (...args: string[]) => spawnSync(process.execPath, [script, "recommend", "o1", "--toolkit", root, ...args], { encoding: "utf8" });
    const shown = async () => { await new Promise((r) => setTimeout(r, 20)); return Object.fromEntries((await runDetail(cfg, "o1")).repairs.map((r) => [r.node, r.recommendation?.kind ?? null])); };
    pending(item("thm:a", "rate $n^{-1/2}$"), item("thm:b", "x"));
    expect(orch("repair", "thm:c", "accept", "fine").status).toBe(65);
    expect(orch("repair", "thm:c", "accept", "fine").stderr).toContain("no suggested repair is pending on thm:c (pending: thm:a, thm:b)");
    expect(orch("repair", "thm:a", "accept", "the weaker rate is the paper's point").status).toBe(0);
    expect(orch("repair", "thm:b", "decline", "not worth it").status).toBe(0);
    // a redo is recommended with the guidance the page offers the user
    expect(orch("repair", "thm:b", "redo", "the rate can be kept").status).toBe(64);
    expect(await shown()).toEqual({ "thm:a": "accept", "thm:b": "decline" });
    // the fixer repaired thm:a again: the recommendation was on the earlier proposal
    pending(item("thm:a", "rate $n^{-1/4}$"), item("thm:b", "x"));
    expect(await shown()).toEqual({ "thm:a": null, "thm:b": "decline" });
    // … and the next recommendation written drops it from the file
    expect(orch("repair", "thm:b", "accept", "on reflection").status).toBe(0);
    expect(Object.keys(JSON.parse(readFileSync(path.join(run, "repair_recommendations.json"), "utf8")))).toEqual(["thm:b"]);
    // a promotion entry: of the batch on file only
    const batchB = (content: string) => writeFileSync(path.join(run, "proposals", "B.json"), JSON.stringify({ slug: "o1", round: "B", created: "x", proposals: [{ id: "b-one", verdict: "propose", content, new_topic: { path: "Foundations/New", scope: "s" } }] }));
    batchB("c");
    expect(orch("B", "b-gone", "accept", "w").stderr).toContain("b-gone is no entry or new topic of the round-B batch on file (items: b-one, topic:Foundations/New)");
    expect(orch("B", "b-one", "accept", "w").status).toBe(0);
    expect(orch("B", "topic:Foundations/New", "accept", "w").status).toBe(0);
    // a new topic takes accept or decline, and is one the batch asks about
    expect(orch("B", "topic:Foundations/New", "defer", "w").status).toBe(64);
    expect(orch("B", "topic:Foundations/Other", "accept", "w").status).toBe(65);
    // bound to what the entry proposes: the same id with another statement is another proposal
    const recFile = path.join(run, "proposals", "B.recommendations.json");
    const { recommendationKeys } = await import("../../src/proposals/checklist.js");
    const keysOf = () => recommendationKeys(JSON.parse(readFileSync(path.join(run, "proposals", "B.json"), "utf8")));
    expect(JSON.parse(readFileSync(recFile, "utf8"))["b-one"].of).toBe(keysOf().get("b-one"));
    batchB("another statement");
    expect(JSON.parse(readFileSync(recFile, "utf8"))["b-one"].of).not.toBe(keysOf().get("b-one"));
    expect(orch("B", "topic:Foundations/New", "decline", "w").status).toBe(0);
    expect(Object.keys(JSON.parse(readFileSync(recFile, "utf8")))).toEqual(["topic:Foundations/New"]);
  });
});

describe("orch.mjs: when the watcher wakes, and who holds a run", () => {
  const script = path.join(__dirname, "..", "..", "scripts", "orch.mjs");
  const fresh = () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-orch2-"));
    const run = path.join(root, "runs", "w1");
    mkdirSync(path.join(run, "logs"), { recursive: true });
    writeFileSync(path.join(run, "state.json"), "{}");
    writeFileSync(path.join(run, "pipeline.jsonl"), JSON.stringify({ stage: "3", status: "dispatch", message: "F3 proof filler" }) + "\n");
    return { root, run };
  };
  const env = { ...process.env, PAPERFORMALIZER_ORCH_TICK_MS: "200" };
  const watch = (root: string, ...extra: string[]) => {
    const c = spawn(process.execPath, [script, "watch", "w1", "--toolkit", root, ...extra], { env });
    let out = ""; c.stdout.on("data", (d) => { out += d; }); c.stderr.on("data", (d) => { out += d; });
    return Object.assign(new Promise<{ code: number | null; out: string }>((resolve) => c.on("exit", (code) => resolve({ code, out }))), { pid: c.pid });
  };
  // the watcher has looked at the run and attached: orch.json names it
  const armed = async (root: string, pid: number | undefined) => {
    const f = path.join(root, "runs", "w1", "orch.json");
    for (let k = 0; k < 300; k++) {
      try { if (JSON.parse(readFileSync(f, "utf8")).watcher === pid) return; } catch { /* not yet */ }
      await new Promise((r) => setTimeout(r, 50));
    }
    throw new Error("the watcher never attached");
  };
  // a stand-in runner: its argv is a verify run's (cwd: the tools directory, as the page launches one)
  const ready = new WeakMap<ChildProcess, Promise<void>>();
  const runner = (...args: string[]) => {
    const code = `
if (process.platform === "win32") {
  const fs = require("node:fs"), path = require("node:path"), os = require("node:os");
  const args = process.argv, root = args[args.indexOf("--toolkit") + 1], slug = args[args.indexOf("--slug") + 1];
  fs.writeFileSync(path.join(root, "runs", slug, "logs", ".run.active"), process.pid + " t mock host=" + os.hostname() + " beat=15");
}
process.send("ready");
setTimeout(() => {}, 60_000);
`;
    const child = spawn(process.execPath, ["-e", code, "bin/paperformalizer.ts", "verify", "/x", ...args], { cwd: path.join(__dirname, "..", ".."), stdio: ["ignore", "pipe", "pipe", "ipc"] });
    ready.set(child, new Promise<void>((resolve, reject) => {
      child.once("message", () => resolve());
      child.once("error", reject);
      child.once("exit", () => reject(new Error("the stand-in exited before readiness")));
    }));
    return child;
  };
  // IPC works on Windows too; the production runner's heartbeat supplies its liveness there.
  const execd = async (...cs: ChildProcess[]) => {
    for (const child of cs) {
      const pending = ready.get(child);
      if (pending) await pending;
      else {
        // The Linux-only discovery case also creates raw decoys outside runner().
        for (let k = 0; !readFileSync(`/proc/${child.pid}/cmdline`, "utf8").includes("paperformalizer.ts"); k++) {
          if (k > 300) throw new Error("the stand-in never started");
          await new Promise((r) => setTimeout(r, 20));
        }
      }
    }
  };
  it("wakes when the runner it saw live exits", async () => {
    const { root } = fresh();
    const r1 = runner("--toolkit", root, "--slug", "w1");
    try {
      await execd(r1);
      const pending = watch(root, "--timeout", "20");
      await armed(root, pending.pid);
      r1.kill();
      const r = await pending;
      expect(r.code).toBe(0);
      expect(r.out).toContain("the runner exited");
    } finally { r1.kill(); }
  }, 30_000);
  it("wakes when the apply of a promotion round ends without completing it; an apply that completed is not reported", async () => {
    const { root, run } = fresh();
    mkdirSync(path.join(run, "proposals"), { recursive: true });
    writeFileSync(path.join(run, "proposals", "B.json"), JSON.stringify({ slug: "w1", round: "B", created: "2026-10-01T00:00:00.000Z", proposals: [] }));
    const state = (status: string) => writeFileSync(path.join(run, "state.json"), JSON.stringify({ verify: { phase: "proposals_B", promotion: { status } } }));
    state("pending_user");
    // the apply at work: a live process named by apply_B.pid, which wrote the round's decisions first
    const apply = spawn(process.execPath, ["-e", "setTimeout(() => {}, 60_000)"]);
    try {
      const pending = watch(root, "--timeout", "20");
      await armed(root, pending.pid);
      writeFileSync(path.join(run, "proposals", "apply_B.pid"), `${apply.pid}\n`);
      writeFileSync(path.join(run, "proposals", "B.decisions.json"), JSON.stringify({ decided_at: "2026-10-02T00:00:00.000Z" }));
      await new Promise((r) => setTimeout(r, 600));
      apply.kill();
      const r = await pending;
      expect(r.code).toBe(0);
      expect(r.out).toContain("the apply of promotion round B ended without completing it");
      expect(r.out).toContain("propose w1 --round B --apply");
      // handed over: armed again, the same stopped apply is not news
      expect((await watch(root, "--timeout", "1")).code).toBe(2);
      // an apply that began and ended while no watcher was armed is reported by its record alone …
      writeFileSync(path.join(run, "proposals", "move_pending.json"), "{}");
      expect((await watch(root, "--timeout", "5")).out).toContain("ended without completing it");
      // one refused before it recorded anything is reported with what it said
      rmSync(path.join(run, "proposals", "move_pending.json"));
      writeFileSync(path.join(run, "proposals", "B.decisions.json"), JSON.stringify({ decided_at: "2026-09-01T00:00:00.000Z" }));
      writeFileSync(path.join(run, "proposals", "apply_failed.json"), JSON.stringify({ round: "B", at: "x", message: "refusing --apply:\n  b-one is still pending" }));
      const refused = await watch(root, "--timeout", "5");
      expect(refused.code).toBe(0);
      expect(refused.out).toMatch(/promotion round B was refused and nothing was applied[\s\S]*b-one is still pending/);
      rmSync(path.join(run, "proposals", "apply_failed.json"));
      writeFileSync(path.join(run, "proposals", "move_pending.json"), "{}");
      // … and one that completed the round is not
      rmSync(path.join(run, "proposals", "move_pending.json"));
      writeFileSync(path.join(run, "proposals", "B.decisions.json"), JSON.stringify({ decided_at: "2026-10-03T00:00:00.000Z" }));
      state("applied");
      expect((await watch(root, "--timeout", "1")).code).toBe(2);
    } finally { apply.kill(); }
  }, 30_000);
  it("a session on another machine of the mount holds the run while its orch.json is fresh, whatever its pid here", async () => {
    const { root, run } = fresh();
    const file = path.join(run, "orch.json");
    writeFileSync(file, JSON.stringify({ agent: "Codex", pid: 999999999, started: null, host: "another-host", attached_at: "x" }));
    const held = await watch(root, "--timeout", "1");
    expect(held.code).toBe(3);
    expect(held.out).toContain("attached to another live session (Codex, pid 999999999 on another-host)");
    const old = new Date(Date.now() - 31 * 60_000);
    utimesSync(file, old, old);
    expect((await watch(root, "--timeout", "1")).code).toBe(2);
    expect(JSON.parse(readFileSync(file, "utf8")).host).toBe(os.hostname());
  }, 30_000);
  it("wakes when the owner resumes a run that was waiting for them: the session knows at once that it runs again", async () => {
    const { root } = fresh();
    const pending = watch(root, "--timeout", "20"); // armed on a run at rest
    // the stand-in runner starts only once the watcher has attached (it must see the run at rest first)
    await armed(root, pending.pid);
    const r1 = runner("--toolkit", root, "--slug", "w1");
    try {
      const r = await pending;
      expect(r.code).toBe(0);
      expect(r.out).toContain("the run is running again (resumed on the page, or by a session)");
      // armed again on the live run, it follows it to its exit as before
      const next = watch(root, "--timeout", "20");
      await armed(root, next.pid);
      r1.kill();
      expect((await next).out).toContain("the runner exited");
    } finally { r1.kill(); }
  }, 30_000);
  // Discovery of an unregistered process by argv/cwd uses Linux /proc. Heartbeat cases run everywhere.
  it.skipIf(process.platform !== "linux")("takes for the run's runner only a verify of its slug on its toolkit, not another toolkit's or a shell's that names one", async () => {
    const { root, run } = fresh();
    const other = mkdtempSync(path.join(tmpdir(), "tc-orch2-other-"));
    writeFileSync(path.join(other, "paperformalizer.json"), "{}");
    const decoys = [
      runner("--toolkit", other, "--slug", "w1"), // the same slug on another toolkit
      spawn(process.execPath, ["-e", "setTimeout(() => {}, 60_000)", "bin/paperformalizer.ts", "verify", "/x", "--slug", "w1"], { cwd: other }), // its toolkit by its cwd
      spawn("bash", ["-c", `sleep 30; echo bin/paperformalizer.ts verify /x --toolkit ${root} --slug w1`]), // a shell naming one
      runner("--toolkit", root, "--slug", "w10"), // another slug
    ];
    try {
      await execd(...decoys);
      const r = await watch(root, "--timeout", "2");
      expect(r.code).toBe(2);
      expect(r.out).toContain("waiting for the owner");
      // a verify of this slug whose toolkit is found from its cwd, under the toolkit, is the run's
      writeFileSync(path.join(root, "paperformalizer.json"), "{}");
      const pending = watch(root, "--timeout", "20");
      await armed(root, pending.pid);
      decoys.push(spawn(process.execPath, ["-e", "setTimeout(() => {}, 60_000)", "bin/paperformalizer.ts", "verify", "/x", "--slug", "w1"], { cwd: run, env: { ...process.env, PAPERFORMALIZER_TOOLKIT: "" } }));
      expect((await pending).out).toContain("the run is running again (resumed on the page, or by a session)");
    } finally { for (const d of decoys) d.kill(); }
  }, 30_000);
  it("wakes for a run that started and exited while no watch was armed (its log moved), once", async () => {
    const { root, run } = fresh();
    expect((await watch(root, "--timeout", "1")).code).toBe(2); // attached; the log as it stands is handed over
    appendFileSync(path.join(run, "pipeline.jsonl"), JSON.stringify({ stage: "3", status: "checkpoint", message: "halt" }) + "\n");
    const r = await watch(root, "--timeout", "20");
    expect(r.code).toBe(0);
    expect(r.out).toContain("halt");
    // handed over: the next watch waits for something new
    expect((await watch(root, "--timeout", "1")).code).toBe(2);
  });
  it("reads a fresh heartbeat written on another machine as a live runner, not as an exit", async () => {
    const { root, run } = fresh();
    // the runner's pid is unknown here; the watcher must not report it gone and must not wake
    writeFileSync(path.join(run, "logs", ".run.active"), "0x3ffffffe 2026-01-01T00:00:00.000Z tok host=elsewhere\n");
    const r = await watch(root, "--timeout", "1");
    expect(r.code).toBe(2);
    expect(r.out).toContain("(running)");
  });
  it("leaves a run another live session holds (exit 3) unless told to take it; detach releases it", async () => {
    const { root, run } = fresh();
    const other = spawn("sleep", ["30"]);
    try {
      writeFileSync(path.join(run, "orch.json"), JSON.stringify({ agent: "Codex", pid: other.pid, started: null, attached_at: "x" }));
      expect((await watch(root, "--timeout", "1")).code).toBe(3);
      expect((await watch(root, "--timeout", "1", "--take")).code).toBe(2);
      expect(JSON.parse(readFileSync(path.join(run, "orch.json"), "utf8")).pid).not.toBe(other.pid);
      const detach = () => spawnSync(process.execPath, [script, "detach", "w1", "--toolkit", root], { encoding: "utf8" });
      expect(detach()).toMatchObject({ status: 0, stdout: "detached from w1\n" });
      expect(existsSync(path.join(run, "orch.json"))).toBe(false);
      // nothing of this session's left to detach: said, still exit 0
      expect(detach()).toMatchObject({ status: 0, stdout: "nothing to detach: this session is not attached to w1\n" });
    } finally { other.kill(); }
  });
  it("wakes when the owner reports an issue with a comment, and not for one already acted on; `handled` marks it", async () => {
    const { root, run } = fresh();
    const file = path.join(run, "owner_objections.json");
    const issue = { id: "obj-1", comment: "0123456789ab", node: "thm:a", kind: "reading", excerpt: "Read $x$ as real.", text: "x is complex here", at: "x" };
    writeFileSync(file, JSON.stringify([{ ...issue, id: "obj-0", handled: true }]));
    const pending = watch(root, "--timeout", "20");
    await armed(root, pending.pid);
    writeFileSync(file, JSON.stringify([{ ...issue, id: "obj-0", handled: true }, issue]));
    const r = await pending;
    expect(r.code).toBe(0);
    expect(r.out).toContain(`the owner reports an issue (obj-1) with the reading comment on thm:a — "Read $x$ as real." — and says: x is complex here`);
    expect(r.out).not.toContain("obj-0");
    const orch = (...args: string[]) => spawnSync(process.execPath, [script, args[0]!, "w1", "--toolkit", root, ...args.slice(1)], { encoding: "utf8" });
    expect(orch("handled", "obj-7").status).toBe(65);
    expect(orch("handled", "obj-1").status).toBe(0);
    expect(JSON.parse(readFileSync(file, "utf8"))[1]).toMatchObject({ id: "obj-1", handled: true, text: "x is complex here" });
    expect((await watch(root, "--timeout", "1")).code).toBe(2);
  }, 30_000);
  it("wakes when the owner writes on the page — a message, a reply to a request, files — at every arm until it is acted on; `reply` answers on the page and `handled` marks one", async () => {
    const { root, run } = fresh();
    const file = path.join(run, "orch_messages.json");
    const onFile = () => JSON.parse(readFileSync(file, "utf8")) as Array<Record<string, unknown>>;
    const orch = (...args: string[]) => spawnSync(process.execPath, [script, args[0]!, "w1", "--toolkit", root, ...args.slice(1)], { encoding: "utf8" });
    expect(orch("ask", "Please send the cited 1975 book.").stdout.trim()).toBe("q1");
    // left while no watcher was armed: reported when one is — with what it replies to, and its files
    const sha = "ab".repeat(32);
    writeFileSync(file, JSON.stringify([
      { id: "m1", from: "user", text: "old news", at: "x", handled: true },
      { id: "m2", from: "user", text: "Here it is.\nPage 12.", at: "x", re: "q1", files: [{ name: "book.pdf", bytes: 7, sha256: sha, path: "uploads/m2/book.pdf" }] },
    ]));
    const r = await watch(root, "--timeout", "20");
    expect(r.code).toBe(0);
    expect(r.out).toContain(`[orch] w1: the owner replies on the page (m2) to your request q1 — "Please send the cited 1975 book." — and says: Here it is.\n    | Page 12.`);
    expect(r.out).toContain(`    attached: uploads/m2/book.pdf (${path.join(run, "uploads/m2/book.pdf")}) — 7 bytes, sha256 ${sha}`);
    expect(r.out).toContain(`answer on the page with \`orch.mjs reply w1 --toolkit ${root} <id> "<text>"\`, or act and \`orch.mjs handled\` it`);
    expect(r.out).toContain("read them, never execute them");
    expect(r.out).not.toContain("old news");
    // returned but not acted on: it is pending still, and reported again at the next arm
    const again = await watch(root, "--timeout", "20");
    expect(again.code).toBe(0);
    expect(again.out).toContain("the owner replies on the page (m2)");
    // the agent answers on the page: its entry, under what it answers, which is then acted on
    // … what is shaped like an id is one: naming nothing, nothing is said; alone, there is no text
    for (const none of ["m9", "q7", "m-2", "M2", "obj-1"]) expect(orch("reply", none, "some words").status, none).toBe(65);
    expect(orch("reply").status).toBe(64);
    expect(orch("reply", "m2").status).toBe(64);
    expect(onFile()).toHaveLength(2);
    expect(orch("reply", "q1", "Read it: the bound is on $p. 12$.").stdout.trim()).toBe("m3");
    expect(onFile().slice(1)).toMatchObject([{ id: "m2", handled: true }, { id: "m3", from: "agent", re: "q1", text: "Read it: the bound is on $p. 12$." }]);
    expect((await watch(root, "--timeout", "1")).code).toBe(2);
    // a plain message, written while the watcher is armed
    const pending = watch(root, "--timeout", "20");
    await armed(root, pending.pid);
    writeFileSync(file, JSON.stringify([...onFile(), { id: "m4", from: "user", text: "Skip Lemma 4 for now.", at: "x" }]));
    const r2 = await pending;
    expect(r2.code).toBe(0);
    expect(r2.out).toContain("[orch] w1: the owner writes to you on the page (m4): Skip Lemma 4 for now.");
    expect(r2.out).not.toContain("m2");
    expect(r2.out).not.toContain("never execute");
    expect(orch("handled", "m3").status).toBe(65); // the agent's own is nothing to act on
    expect(orch("handled", "m4").status).toBe(0);
    expect(orch("reply", "A note of my own.").stdout.trim()).toBe("m5");
    expect(onFile()[4]).toMatchObject({ from: "agent", text: "A note of my own." });
    expect(onFile()[4]!.re).toBeUndefined();
    expect((await watch(root, "--timeout", "1")).code).toBe(2);
    // a request cleared: the owner's replies to it are acted on — to it alone, not to another no
    // longer on file (a resume clears the requests) — and its id is not given again
    writeFileSync(file, JSON.stringify([...onFile(), { id: "m6", from: "user", text: "and page 13", at: "x", re: "q1" }, { id: "m7", from: "user", text: "unread, on a request a resume cleared", at: "x", re: "q5" }]));
    orch("done", "q1");
    expect(onFile().slice(5)).toMatchObject([{ id: "m6", handled: true }, { id: "m7" }]);
    expect(onFile()[6]!.handled).toBeUndefined();
    const heard = await watch(root, "--timeout", "20");
    expect(heard.out).toContain("the owner writes to you on the page (m7), in reply to q5: unread, on a request a resume cleared");
    expect(orch("ask", "Another?").stdout.trim()).toBe("q6");
    orch("done");
    expect(onFile()[6]).toMatchObject({ id: "m7", handled: true });
    // a store that is no list is never read as empty, nor written over: every verb says so, and so does the watcher
    writeFileSync(file, `{"oops": `);
    for (const verb of [["reply", "hello"], ["handled", "m7"], ["done"], ["ask", "x"]]) {
      const r = orch(...(verb as [string, ...string[]]));
      expect(r.status, verb[0]).not.toBe(0);
      expect(r.stderr).toContain("orch_messages.json is unreadable");
    }
    expect(readFileSync(file, "utf8")).toBe(`{"oops": `);
    const broken = await watch(root, "--timeout", "20");
    expect(broken.code).toBe(0);
    expect(broken.out).toContain("the owner's messages cannot be read");
    expect(broken.out).toContain("orch_messages.json is unreadable");
  }, 60_000);
  it("hears the owner's message whatever the run is doing: running (its runner alive, its log still), halted, finished", async () => {
    const said = (run: string) => writeFileSync(path.join(run, "orch_messages.json"), JSON.stringify([{ id: "m1", from: "user", text: "A word.", at: "x" }]));
    // running: the runner lives on, and the log does not move
    const live = fresh();
    const r1 = runner("--toolkit", live.root, "--slug", "w1");
    try {
      await execd(r1);
      const pending = watch(live.root, "--timeout", "20");
      await armed(live.root, pending.pid);
      said(live.run);
      const r = await pending;
      expect(r.code).toBe(0);
      expect(r.out).toContain("the owner writes to you on the page (m1): A word.");
      expect(r.out).not.toContain("the runner exited");
      expect(r1.exitCode).toBeNull();
    } finally { r1.kill(); }
    // halted on the owner's decision, and finished: no runner, nothing else to report
    for (const state of [{ stage_completed: "V1.5", verify: { phase: "review", weakening_repair: { status: "pending", items: [{ node: "thm:a" }] } } }, { stage_completed: "V6", verify: { phase: "done" } }]) {
      const { root, run } = fresh();
      writeFileSync(path.join(run, "state.json"), JSON.stringify(state));
      const pending = watch(root, "--timeout", "20");
      await armed(root, pending.pid);
      said(run);
      const r = await pending;
      expect(r.code).toBe(0);
      expect(r.out).toContain("the owner writes to you on the page (m1): A word.");
    }
  }, 60_000);
});

describe("server: the owner writes to the agent on the page", () => {
  it("names an attached file safely", () => {
    expect(safeUploadName("../../etc/pass wd(1).PDF")).toBe("pass_wd_1_.PDF");
    expect(safeUploadName("/abs/path/a.pdf", ["a.pdf", "a-2.pdf"])).toBe("a-3.pdf");
    expect(safeUploadName("C:\\x\\..\\.hidden.tex")).toBe("_hidden.tex");
    expect(safeUploadName("..")).toBe("_");
    expect(safeUploadName(`${"n".repeat(300)}.pdf`)).toHaveLength(100);
  });
  it("stores a message, a reply to a request and their files for the agent; refuses what a message does not carry; changes nothing else in the run", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-ui-msg-"));
    const run = path.join(root, "runs", "p1");
    mkdirSync(path.join(run, "source"), { recursive: true });
    const state = JSON.stringify({ stage_completed: "V1.5", verify: { phase: "formalize", source: { main_file: "m.tex" } } });
    writeFileSync(path.join(run, "state.json"), state);
    writeFileSync(path.join(run, "source", "m.tex"), String.raw`\begin{document}Text.\end{document}`);
    const before = readdirSync(run);
    const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs"), lib: "Toolkit", papersLib: "Papers", divisions: [], baseLibraries: [], owner: { name: "O" }, leanToolchain: "x" } as unknown as ToolkitConfig;
    const ui = await startUiServer(cfg, { port: 0 });
    try {
      const base = new URL(ui.url).origin;
      const Cookie = ((await fetch(ui.url, { redirect: "manual" })).headers.get("set-cookie") ?? "").split(";")[0]!;
      type Answer = { status: number; error?: string; message?: Record<string, unknown>; name?: string; bytes?: number };
      const send = async (sub: string, body: unknown, headers: Record<string, string> = { Cookie, "X-TC": "1" }): Promise<Answer> => { const r = await fetch(`${base}/api/runs/p1/${sub}`, { method: "POST", headers, body: body instanceof Uint8Array ? Buffer.from(body) : JSON.stringify(body) }); return { status: r.status, ...(await r.json().catch(() => ({})) as object) }; };
      const onFile = () => JSON.parse(readFileSync(path.join(run, "orch_messages.json"), "utf8")) as Array<Record<string, unknown>>;
      const detail = async () => (await (await fetch(`${base}/api/runs/p1`, { headers: { Cookie } })).json()) as { summary: { unread: number; status: string; orch: unknown }; messages: Array<Record<string, unknown>>; texHtml: Record<string, string> };
      // protected as every state-changing request is
      expect((await send("message", { text: "hi" }, { "X-TC": "1" })).status).toBe(403);
      expect((await send("message", { text: "hi" }, { Cookie })).status).toBe(403);
      expect((await send("upload?draft=aaaaaaaa&name=a.pdf", new Uint8Array(3), { "X-TC": "1" })).status).toBe(403);
      expect((await send("upload?draft=aaaaaaaa&name=a.pdf", new Uint8Array(3), { Cookie })).status).toBe(403);
      expect((await send("message-seen", {}, { Cookie })).status).toBe(403);
      expect(existsSync(path.join(run, "uploads"))).toBe(false);
      // a message: some words, of bounded length; a reply: to a request the agent has on the page
      expect((await send("message", { text: "  " })).status).toBe(400);
      expect((await send("message", { text: "x".repeat(MESSAGE_LIMITS.chars + 1) })).status).toBe(400);
      expect((await send("message", { text: "yes", re: "../q1" })).status).toBe(400);
      expect(existsSync(path.join(run, "orch_messages.json"))).toBe(false);
      expect((await send("message", { text: " Skip <script>alert(1)</script> Lemma 4.\nPlease. " })).message).toMatchObject({ id: "m1", from: "user", text: "Skip <script>alert(1)</script> Lemma 4.\nPlease." });
      writeFileSync(path.join(run, "orch_requests.json"), JSON.stringify([{ id: "q1", at: "x", text: "which account?" }]));
      expect((await send("message", { text: "the second", re: "q1" })).message).toMatchObject({ id: "m2", re: "q1" });
      // whether the agent hears it now: its session attached (orch.json), and its watcher armed or not
      const attached = async (watcher: number) => { writeFileSync(path.join(run, "orch.json"), JSON.stringify({ agent: "Codex", pid: process.pid, started: null, attached_at: "x", watcher })); return (await detail()).summary.orch; };
      const gone = spawnSync(process.execPath, ["-e", ""]).pid;
      expect(await attached(process.pid)).toMatchObject({ agent: "Codex", watching: true });
      expect(await attached(gone)).toMatchObject({ agent: "Codex", watching: false });
      rmSync(path.join(run, "orch.json"));
      // the agent answers (`orch.mjs reply`): unread until the owner has seen it, or writes back
      writeFileSync(path.join(run, "orch_messages.json"), JSON.stringify([...onFile().map((m) => ({ ...m, handled: true })), { id: "m3", from: "agent", text: "Done: $n \\ge 2$ <script>alert(2)</script>", at: "x", re: "m1" }]));
      let d = await detail();
      expect(d.summary.unread).toBe(1);
      expect(d.messages).toMatchObject([{ id: "m1", from: "user", words: "Skip <script>alert(1)</script> Lemma 4.\nPlease." }, { id: "m2", re: "q1" }, { id: "m3", from: "agent", re: "m1", unseen: true }]);
      expect(d.messages[0]).not.toHaveProperty("text"); // the owner's words are not typeset
      expect(d.messages[0]).not.toHaveProperty("waiting");
      const drawn = d.texHtml[String(d.messages[2]!.text)]!;
      expect(drawn).toContain("katex");
      expect(drawn).not.toContain("<script");
      expect(Object.keys(d.texHtml).some((k) => k.includes("Lemma 4"))).toBe(false);
      expect(((await (await fetch(`${base}/api/toolkit`, { headers: { Cookie } })).json()) as { runs: Array<{ unread: number }> }).runs[0]!.unread).toBe(1);
      expect(await send("message-seen", {})).toMatchObject({ status: 200, seen: 1 });
      expect((await detail()).summary.unread).toBe(0);

      // files: each its own request, kept under a safe name in the draft's folder
      const up = (draft: string, name: string, bytes: Uint8Array | number) => send(`upload?draft=${draft}&name=${encodeURIComponent(name)}`, typeof bytes === "number" ? new Uint8Array(bytes) : bytes);
      expect((await up("../x", "a.pdf", 3)).status).toBe(400);
      for (const bad of ["a.html", "a.svg", "a.js", "a.pdf.htm", "noext", ".pdf", "a.exe"]) expect((await up("d0000001", bad, 3)).status, bad).toBe(400);
      expect((await up("d0000001", "big.pdf", MESSAGE_LIMITS.fileBytes + 1)).status).toBe(413);
      expect(readdirSync(path.join(run, "uploads", "draft-d0000001"))).toEqual([]);
      const pdf = new TextEncoder().encode("%PDF-1.4 the book");
      expect(await up("d0000001", "../../../etc/My Book (1975).pdf", pdf)).toMatchObject({ status: 200, name: "My_Book__1975_.pdf", bytes: pdf.length });
      expect(await up("d0000001", "/abs/My Book (1975).pdf", pdf)).toMatchObject({ status: 200, name: "My_Book__1975_-2.pdf" });
      expect(await up("d0000001", "..\\.notes.txt", 0)).toMatchObject({ status: 200, name: "_notes.txt" });
      expect(readdirSync(path.join(run, "uploads")).sort()).toEqual(["draft-d0000001"]);
      // POSIX mode bits do not describe Windows ACLs; the upload behavior is checked on both.
      if (process.platform !== "win32") expect(statSync(path.join(run, "uploads", "draft-d0000001", "My_Book__1975_.pdf")).mode & 0o777).toBe(0o600);
      for (const n of ["d.png", "e.zip"]) expect((await up("d0000001", n, 2)).status).toBe(200);
      expect((await up("d0000001", "f.pdf", 2)).status).toBe(400); // a sixth
      // … and the message that carries them, with no words: each file's size and hash on record
      expect((await send("message", { draft: "d0000009" })).status).toBe(400);
      expect((await send("message", { draft: "../../source" })).status).toBe(400);
      const sent = (await send("message", { draft: "d0000001", re: "q1" })).message as { id: string; text: string; files: Array<{ name: string; bytes: number; sha256: string; path: string }> };
      expect(sent).toMatchObject({ id: "m4", text: "", re: "q1" });
      expect(sent.files.map((f) => f.path).sort()).toEqual(["uploads/m4/My_Book__1975_-2.pdf", "uploads/m4/My_Book__1975_.pdf", "uploads/m4/_notes.txt", "uploads/m4/d.png", "uploads/m4/e.zip"]);
      expect(sent.files.find((f) => f.name === "My_Book__1975_.pdf")).toMatchObject({ bytes: pdf.length, sha256: createHash("sha256").update(pdf).digest("hex") });
      expect(readFileSync(path.join(run, "uploads", "m4", "My_Book__1975_.pdf"), "utf8")).toBe("%PDF-1.4 the book");
      expect(readdirSync(path.join(run, "uploads"))).toEqual(["m4"]);
      // a reply whose request was cleared while it was written is kept, naming the request
      expect((await send("message", { text: "too late?", re: "q9" })).message).toMatchObject({ id: "m5", re: "q9" });
      // a draft is cleared a day after its last file — never the one a file is arriving in
      const old = new Date(Date.now() - 2 * 86_400_000);
      for (const d of ["draft-d0000007", "draft-d0000008"]) { mkdirSync(path.join(run, "uploads", d)); writeFileSync(path.join(run, "uploads", d, "kept.pdf"), "x"); utimesSync(path.join(run, "uploads", d), old, old); }
      expect((await up("d0000007", "more.pdf", 2)).status).toBe(200);
      expect(readdirSync(path.join(run, "uploads")).sort()).toEqual(["draft-d0000007", "m4"]);
      expect(readdirSync(path.join(run, "uploads", "draft-d0000007")).sort()).toEqual(["kept.pdf", "more.pdf"]);
      rmSync(path.join(run, "uploads", "draft-d0000007"), { recursive: true });
      // a folder left under the next message's number (a store edited by hand) is stepped over
      mkdirSync(path.join(run, "uploads", "m6"));
      expect((await up("d0000010", "a.pdf", 2)).status).toBe(200);
      expect((await send("message", { draft: "d0000010" })).message).toMatchObject({ id: "m7", files: [{ path: "uploads/m7/a.pdf" }] });
      rmSync(path.join(run, "uploads", "m6"), { recursive: true });
      d = await detail();
      expect(d.messages[3]).toMatchObject({ id: "m4", waiting: true, files: expect.arrayContaining([{ name: "d.png", bytes: 2 }]) });
      expect(JSON.stringify(d.messages)).not.toContain("uploads/"); // named on the page, not linked
      // a body that does not say its length is stopped at the limit, and nothing of it is kept
      const streamed = await new Promise<number>((resolve, reject) => {
        const u = new URL(`${base}/api/runs/p1/upload?draft=d0000002&name=s.zip`);
        const rq = http.request({ host: u.hostname, port: u.port, path: u.pathname + u.search, method: "POST", headers: { Cookie, "X-TC": "1" } }, (r) => { r.resume(); resolve(r.statusCode ?? 0); });
        rq.on("error", (e) => (rq.destroyed ? undefined : reject(e)));
        const chunk = Buffer.alloc(1024 * 1024);
        let k = 0;
        const more = () => { while (k++ <= MESSAGE_LIMITS.fileBytes / chunk.length + 1) { if (!rq.write(chunk)) { rq.once("drain", more); return; } } rq.end(); };
        rq.on("socket", more);
      });
      expect(streamed).toBe(413);
      expect(readdirSync(path.join(run, "uploads", "draft-d0000002"))).toEqual([]);
      // the page and the agent write the store at once: every message is on file afterwards
      const script = path.join(__dirname, "..", "..", "scripts", "orch.mjs");
      const child = (...args: string[]) => new Promise<number | null>((resolve) => spawn(process.execPath, [script, args[0]!, "p1", "--toolkit", root, ...args.slice(1)]).on("exit", resolve));
      const had = onFile().length;
      const both = await Promise.all([
        ...Array.from({ length: 12 }, (_, k) => send("message", { text: `at once ${k}` })),
        ...Array.from({ length: 6 }, (_, k) => child("reply", `the agent, at once ${k}`)),
        child("handled", "m5"), child("handled", "m7"),
      ]);
      expect(both.map((r) => (typeof r === "object" && r ? r.status : r))).toEqual([...Array(12).fill(200), ...Array(8).fill(0)]);
      const after = onFile();
      expect(after).toHaveLength(had + 18);
      expect(new Set(after.map((m) => m.id)).size).toBe(after.length);
      for (let k = 0; k < 12; k++) expect(after.some((m) => m.text === `at once ${k}` && m.from === "user")).toBe(true);
      for (let k = 0; k < 6; k++) expect(after.some((m) => m.text === `the agent, at once ${k}` && m.from === "agent")).toBe(true);
      expect(after.filter((m) => m.id === "m5" || m.id === "m7").map((m) => m.handled)).toEqual([true, true]);
      expect(readdirSync(run).filter((f) => /\.tmp$|\.lock$/.test(f))).toEqual([]);
      // a store that is no list: the send is refused naming the file, which stands; the home page still answers
      const good = readFileSync(path.join(run, "orch_messages.json"), "utf8");
      writeFileSync(path.join(run, "orch_messages.json"), `{"not": "a list"}`);
      const refused = await send("message", { text: "lost?" });
      expect(refused.status).toBe(400);
      expect(refused.error).toContain("orch_messages.json is unreadable");
      expect((await send("message-seen", {})).status).toBe(400);
      expect(readFileSync(path.join(run, "orch_messages.json"), "utf8")).toBe(`{"not": "a list"}`);
      expect((await fetch(`${base}/api/toolkit`, { headers: { Cookie } })).status).toBe(200);
      expect((await detail()).messages).toEqual([]);
      writeFileSync(path.join(run, "orch_messages.json"), good);
      // the owner clears the conversation: not while the agent has not acted on a message of theirs …
      const archive = path.join(run, "orch_messages.archive.json");
      const orch = (...args: string[]) => spawnSync(process.execPath, [script, args[0]!, "p1", "--toolkit", root, ...args.slice(1)], { encoding: "utf8", env: { ...process.env, PAPERFORMALIZER_ORCH_TICK_MS: "200" } });
      const top = (ms: Array<Record<string, unknown>>) => Math.max(...ms.map((m) => Number(String(m.id).slice(1))));
      expect((await send("message-clear", {}, { Cookie })).status).toBe(403);
      const waiting = after.filter((m) => m.from === "user" && !m.handled).length;
      expect(waiting).toBeGreaterThan(0);
      const stopped = await send("message-clear", {});
      expect(stopped.status).toBe(409);
      expect(stopped.error).toContain(`The agent has not acted yet on ${waiting} message(s) of yours`);
      expect(onFile()).toHaveLength(after.length);
      expect(existsSync(archive)).toBe(false);
      // … unless they say so again: archived as acted on, the store an empty list, the files where they were
      expect(await send("message-clear", { force: true })).toMatchObject({ status: 200, cleared: after.length });
      expect(onFile()).toEqual([]);
      const kept = JSON.parse(readFileSync(archive, "utf8")) as Array<Record<string, unknown>>;
      expect(kept.map((m) => m.id)).toEqual(after.map((m) => m.id));
      expect(kept.filter((m) => m.cleared).length).toBe(waiting);
      expect(kept.every((m) => m.from !== "user" || m.handled === true)).toBe(true);
      expect(existsSync(path.join(run, "uploads", "m4", "d.png"))).toBe(true);
      expect((await detail()).messages).toEqual([]);
      expect(orch("watch", "--timeout", "1").status).toBe(2); // nothing of it is reported again
      // a new conversation counts on: no id of the archive is given again, by the page or by the agent
      expect((await send("message", { text: "a new question" })).message).toMatchObject({ id: `m${top(kept) + 1}` });
      expect(orch("reply", `m${top(kept) + 1}`, "A new answer.").stdout.trim()).toBe(`m${top(kept) + 2}`);
      // nothing waits on the agent now: cleared at once, appended to what was archived
      expect(await send("message-clear", {})).toMatchObject({ status: 200, cleared: 2 });
      expect(JSON.parse(readFileSync(archive, "utf8"))).toHaveLength(kept.length + 2);
      expect(await send("message-clear", {})).toMatchObject({ status: 200, cleared: 0 });
      // an answer of the agent's the owner has not read is no decision of theirs: the paper does not "need you"
      rmSync(path.join(run, "orch_requests.json"));
      expect(orch("reply", "For your information.").stdout.trim()).toBe(`m${top(kept) + 3}`);
      expect((await detail()).summary).toMatchObject({ unread: 1, status: "idle" });
      // a link where the folder would be is not written through
      symlinkSync(root, path.join(run, "uploads", "draft-d0000003"), process.platform === "win32" ? "junction" : "dir");
      expect((await up("d0000003", "a.pdf", 3)).status).toBe(400);
      expect(existsSync(path.join(root, "a.pdf"))).toBe(false);
      // a message is words for the agent: the run is as it was, and nothing was started
      expect(readFileSync(path.join(run, "state.json"), "utf8")).toBe(state);
      expect(readdirSync(run).filter((f) => !before.includes(f) && f !== "logs").sort()).toEqual(["orch.json", "orch_messages.archive.json", "orch_messages.json", "uploads"]);
    } finally { await ui.close(); }
  }, 60_000);
});

describe("server: the owner reports an issue with a margin comment that asks no decision", () => {
  it("stores it under the comment's key with its node, rewords and withdraws it until the agent acted on it; nothing more waits on the owner", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-ui-issue-"));
    const run = path.join(root, "runs", "p1");
    mkdirSync(path.join(run, "source"), { recursive: true });
    mkdirSync(path.join(run, "discovery"), { recursive: true });
    writeFileSync(path.join(run, "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: { phase: "formalize", source: { main_file: "m.tex" } } }));
    writeFileSync(path.join(run, "discovery", "core.json"), JSON.stringify({ statements: [{ id: "thm:t1", kind: "theorem", depends_on: [], tex_locator: { file: "m.tex", from: 1, label: "t1" } }] }));
    const tex = (reading: string) => String.raw`\begin{document}\begin{theorem}\label{t1}A.\vsNote{The bound fails.}\end{theorem}` + reading + String.raw`\vsReading{Read $x$ as real.}\vsRewind{A proposed correction.}\end{document}`;
    writeFileSync(path.join(run, "source", "m.tex"), tex(""));
    const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs"), lib: "Toolkit", papersLib: "Papers", divisions: [], baseLibraries: [], owner: { name: "O" }, leanToolchain: "x" } as unknown as ToolkitConfig;
    const ui = await startUiServer(cfg, { port: 0 });
    try {
      const base = new URL(ui.url).origin;
      const Cookie = ((await fetch(ui.url, { redirect: "manual" })).headers.get("set-cookie") ?? "").split(";")[0]!;
      const get = async (p: string) => (await fetch(`${base}${p}`, { headers: { Cookie } })).json();
      const send = async (body: unknown, headers: Record<string, string> = { "X-TC": "1" }) => { const r = await fetch(`${base}/api/runs/p1/objection`, { method: "POST", headers: { Cookie, ...headers }, body: JSON.stringify(body) }); return { status: r.status, ...(await r.json() as { objection?: Record<string, unknown> }) }; };
      const onFile = () => JSON.parse(readFileSync(path.join(run, "owner_objections.json"), "utf8")) as Array<Record<string, unknown>>;
      type C = { id: string; key: string; kind: string };
      const comments = ((await get("/api/runs/p1/paper")) as { comments: C[] }).comments;
      const [note, reading, rewind] = ["note", "reading", "rewind"].map((k) => comments.find((c) => c.kind === k)!);
      const summary = ((await get("/api/runs/p1")) as { summary: unknown }).summary;
      // refused: without the page's header, with no text, on no comment of the paper, on a note awaiting a ruling
      expect((await send({ comment: note!.key, text: "wrong" }, {})).status).toBe(403);
      expect((await send({ comment: note!.key, text: "  " })).status).toBe(400);
      expect((await send({ comment: "nope", text: "wrong" })).status).toBe(404);
      expect((await send({ comment: rewind!.key, text: "wrong" })).status).toBe(400);
      expect(existsSync(path.join(run, "owner_objections.json"))).toBe(false);
      // stored: the comment's key, the result it stands at, its kind, how it begins, the owner's words
      expect(await send({ comment: note!.key, text: " The bound holds: <see> Lemma 2. " })).toMatchObject({ status: 200, objection: { id: "obj-1" } });
      expect((await send({ comment: reading!.key, text: "x is complex" })).objection).toMatchObject({ id: "obj-2", node: "thm:t1", kind: "reading" });
      expect(onFile()).toMatchObject([
        { id: "obj-1", comment: note!.key, node: "thm:t1", kind: "note", excerpt: "The bound fails.", text: "The bound holds: <see> Lemma 2." },
        { id: "obj-2", comment: reading!.key, kind: "reading", excerpt: "Read $x$ as real.", text: "x is complex" },
      ]);
      // reworded (by its id; a second report on the same comment is that one too), then withdrawn
      expect((await send({ id: "obj-1", text: "It holds for n > 1." })).status).toBe(200);
      expect((await send({ comment: reading!.key, text: "x is complex here" })).objection).toMatchObject({ id: "obj-2" });
      expect(onFile().map((o) => o.text)).toEqual(["It holds for n > 1.", "x is complex here"]);
      expect((await send({ id: "obj-1", text: "" })).status).toBe(400);
      expect((await send({ id: "obj-9", text: "x" })).status).toBe(404);
      expect((await send({ id: "obj-1", withdraw: true })).status).toBe(200);
      expect(onFile().map((o) => o.id)).toEqual(["obj-2"]);
      // the page gets them with the run; the run waits on the owner no more than before
      const detail = (await get("/api/runs/p1")) as { summary: unknown; objections: unknown[] };
      expect(detail.objections).toMatchObject([{ id: "obj-2", comment: reading!.key }]);
      expect(detail.summary).toEqual(summary);
      // a note keeps its key when another is written before it (its position, `id`, moves)
      writeFileSync(path.join(run, "source", "m.tex"), tex(String.raw`\vsReadingOwner{An earlier note.}`));
      const moved = ((await get("/api/runs/p1/paper")) as { comments: C[] }).comments.find((c) => c.key === reading!.key)!;
      expect(moved).toMatchObject({ kind: "reading" });
      expect(moved.id).not.toBe(reading!.id);
      // acted on by the agent: neither reworded nor withdrawn; a new report on the comment is a new one
      writeFileSync(path.join(run, "owner_objections.json"), JSON.stringify(onFile().map((o) => ({ ...o, handled: true }))));
      expect((await send({ id: "obj-2", text: "again" })).status).toBe(409);
      expect((await send({ id: "obj-2", withdraw: true })).status).toBe(409);
      expect((await send({ comment: reading!.key, text: "still wrong" })).objection).toMatchObject({ id: "obj-3" });
      expect(onFile().map((o) => [o.id, o.text, Boolean(o.handled)])).toEqual([["obj-2", "x is complex here", true], ["obj-3", "still wrong", false]]);
    } finally { await ui.close(); }
  });
  it("the control stands at the foot of a note or a clarification, not of a note awaiting a ruling", () => {
    const js = readFileSync(path.join(__dirname, "..", "..", "src", "ui", "static", "app.js"), "utf8").replace(/\r\n/g, "\n");
    const line = (start: string) => js.slice(js.indexOf(start), js.indexOf("\n", js.indexOf(start)));
    const cardHTML = new Function("esc", "envOf", `const SNAP = null;\n${line("const KIND_TAG")}\n${line("const CHIP")}\n${js.slice(js.indexOf("function cardHTML("), js.indexOf("/* Edit / Save / Cancel / Remove"))}; return cardHTML;`)(
      (x: string) => String(x).replace(/&/g, "&amp;").replace(/</g, "&lt;"), () => null,
    ) as (c: unknown, r: unknown, o?: unknown) => string;
    const c = { id: "c1", key: "k", kind: "note", label: "PaperFormalizer", html: "x" };
    for (const kind of ["note", "reading", "reading-owner", "reading-symbol"]) expect(cardHTML({ ...c, kind }, null)).toContain(`data-flag="open">Report an issue</button>`);
    for (const kind of ["rewind", "cap"]) expect(cardHTML({ ...c, kind }, null)).not.toContain("data-flag");
    // an owner's reading being edited shows its editor alone
    const own = [{ id: "ass:pin-owner-1", node: "thm:a", kind: "reading", text: "t", withdraws: 0 }];
    expect(cardHTML({ ...c, kind: "reading-owner" }, null, { own, atRest: true, draft: "t" })).not.toContain("data-flag");
  });
});

describe("server: formulas no renderer reads go on record for the agent", () => {
  it("lists them, renders the run records' TeX, and applies the agent's override", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-ui-math-"));
    const run = path.join(root, "runs", "p1");
    mkdirSync(path.join(run, "source"), { recursive: true });
    writeFileSync(path.join(run, "state.json"), JSON.stringify({ verify: { source: { main_file: "m.tex" } } }));
    writeFileSync(path.join(run, "source", "m.tex"), String.raw`\begin{document}$\zzundefined x$ and $y$.\end{document}`);
    const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs"), lib: "Toolkit", papersLib: "Papers", divisions: [], baseLibraries: [], owner: { name: "O" }, leanToolchain: "x" } as unknown as ToolkitConfig;
    const ui = await startUiServer(cfg, { port: 0 });
    try {
      const base = new URL(ui.url).origin;
      const Cookie = ((await fetch(ui.url, { redirect: "manual" })).headers.get("set-cookie") ?? "").split(";")[0]!;
      const paper = async () => (await (await fetch(`${base}/api/runs/p1/paper`, { headers: { Cookie } })).json()) as { health: { mathFailures: unknown[] } };
      expect((await paper()).health.mathFailures).toHaveLength(1);
      const record = () => JSON.parse(readFileSync(path.join(run, "logs", "ui_math_failures.json"), "utf8")) as { failures: unknown[] };
      expect(record().failures).toEqual([expect.objectContaining({ tex: "\\zzundefined x", where: "paper" })]);
      // the run records' TeX comes rendered with the page
      mkdirSync(path.join(run, "discovery"), { recursive: true });
      writeFileSync(path.join(run, "discovery", "core.json"), JSON.stringify({ statements: [{ id: "thm:t1", kind: "theorem", tex_locator: { file: "m.tex", from: 1 } }] }));
      writeFileSync(path.join(run, "discovery", "v1_5_review.json"), JSON.stringify({ nodes: [{ id: "thm:t1", correctness: "error", detail: "It fails at $n = 1$." }] }));
      const detail = (await (await fetch(`${base}/api/runs/p1/drawers`, { headers: { Cookie } })).json()) as { texHtml: Record<string, string> };
      expect(detail.texHtml["It fails at $n = 1$."]).toContain("katex");
      // the owner's review of a ruling: approved, or rejected only with guidance
      writeFileSync(path.join(run, "orch_decisions.json"), JSON.stringify([{ id: "d1", node: "thm:t1", at: "x", text: "accepted the repair" }]));
      const review = (body: unknown) => fetch(`${base}/api/runs/p1/review`, { method: "POST", headers: { Cookie, "X-TC": "1" }, body: JSON.stringify(body) });
      expect((await review({ id: "d1", verdict: "reject" })).status).toBe(400);
      expect((await review({ id: "d9", verdict: "approve" })).status).toBe(404);
      expect((await review({ id: "d1", verdict: "reject", guidance: "keep n >= 1" })).status).toBe(200);
      expect(JSON.parse(readFileSync(path.join(run, "orch_decisions.json"), "utf8"))[0].review).toMatchObject({ verdict: "reject", guidance: "keep n >= 1" });
      // the owner takes an answered question of the agent's off the page
      writeFileSync(path.join(run, "orch_requests.json"), JSON.stringify([{ id: "q1", at: "x", text: "which account?" }]));
      const dismiss = (id: string) => fetch(`${base}/api/runs/p1/dismiss`, { method: "POST", headers: { Cookie, "X-TC": "1" }, body: JSON.stringify({ id }) });
      expect((await dismiss("q9")).status).toBe(404);
      expect((await dismiss("q1")).status).toBe(200);
      expect(existsSync(path.join(run, "orch_requests.json"))).toBe(false);
      writeFileSync(path.join(run, "ui_math_overrides.json"), JSON.stringify({ "\\zzundefined x": "z x" }));
      // a result stated in prose, with a label but no environment: anchored at its line, named as the line names it
      mkdirSync(path.join(run, "discovery"), { recursive: true });
      writeFileSync(path.join(run, "source", "m.tex"), "\\begin{document}$\\zzundefined x$ and $y$.\n\\textbf{Theorem 2.} Every bounded sequence converges.\\label{t2}\nWe assume the terms are real. Later, the terms are real.\\vsReading{Bounded means bounded above and below.}\\vsReadingOwner{Convergence is in the usual metric.}\n\\end{document}");
      writeFileSync(path.join(run, "discovery", "patches.json"), JSON.stringify({ owner_readings: [{ id: "ass:pin-owner-1", node: "thm:t2", reading: "Convergence is in the usual metric.", withdraws: [] }] }));
      writeFileSync(path.join(run, "discovery", "core.json"), JSON.stringify({
        statements: [{ id: "thm:t2", tex_locator: { file: "m.tex", from: 2, label: "t2", env: "theorem" } }],
        assumptions: [
          { id: "ass:real", condition: "the terms are real.", tex_locator: { file: "m.tex", from: 3, to: 3, env: "prose", label: null } },
          { id: "ass:late", condition: "the terms are real.", tex_locator: { file: "m.tex", from: 5, to: 5, env: "prose", label: null } },
          { id: "ass:pin-1", condition: "Bounded means bounded above and below.", used_by: ["thm:t2"] },
          { id: "ass:pin-owner-1", condition: "Convergence is in the usual metric.", used_by: ["thm:t2"] },
        ],
      }));
      const named = (await (await fetch(`${base}/api/runs/p1/paper`, { headers: { Cookie } })).json()) as { anchors: Record<string, string>; anchorHeadings: Record<string, string>; readings: Record<string, string>; ownerReadings: Record<string, unknown>; html: string };
      expect(named.anchors["thm:t2"]).toBeDefined();
      expect(named.anchorHeadings["thm:t2"]).toBe("Theorem 2");
      // a condition stated in prose is anchored where its own text begins — not where the same words
      // stand outside the passage the core locates it in; a pinned reading is found in its note
      expect(named.anchors["ass:real"]).toBe("res-ass-real");
      expect(named.html).toContain(`We assume <span class="res-anchor" id="res-ass-real" data-node="ass:real"></span>the terms are real.`);
      expect(named.anchors["ass:late"]).toBeUndefined();
      expect(named.readings).toEqual({ "ass:pin-1": "c1", "ass:pin-owner-1": "c2" });
      // … and the owner's reading comes with the entry of the run's record its note states
      expect(named.ownerReadings).toEqual({ c2: [{ id: "ass:pin-owner-1", node: "thm:t2", kind: "reading", text: "Convergence is in the usual metric.", withdraws: 0 }] });
      // changing it resumes the run: like a resume, only under an attached agent session
      const act = (sub: string, action: unknown) => fetch(`${base}/api/runs/p1/${sub}`, { method: "POST", headers: { Cookie, "X-TC": "1" }, body: JSON.stringify({ action }) });
      expect((await act("preview", { kind: "remove-reading", ids: ["ass:pin-owner-1"] })).status).toBe(409);
      expect((await act("action", { kind: "edit-reading", readings: [{ id: "ass:pin-owner-1", text: "x" }] })).status).toBe(409);
      // a resume from the page needs an attached agent session, which acts at the next halt
      const resume = await fetch(`${base}/api/runs/p1/action`, { method: "POST", headers: { Cookie, "X-TC": "1" }, body: JSON.stringify({ action: { kind: "resume" } }) });
      expect(resume.status).toBe(409);
      expect(((await resume.json()) as { error: string }).error).toBe("no-orch");
      // so does the apply of a promotion round: it resumes the run when it ends
      expect(((await (await act("action", { kind: "apply-promotion", round: "B" })).json()) as { error: string }).error).toBe("no-orch");
      expect((await paper()).health.mathFailures).toEqual([]);
      expect(record().failures).toEqual([]);
    } finally {
      await ui.close();
    }
  });
});

describe("watch: a change reaches the page within about a second", () => {
  it("scans a run that is not live as soon as the platform reports a change in it", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-watch-"));
    mkdirSync(path.join(root, "runs", "idle", "discovery"), { recursive: true });
    writeFileSync(path.join(root, "runs", "idle", "state.json"), "{}");
    const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs"), lib: "Toolkit", papersLib: "Papers", divisions: [] } as unknown as ToolkitConfig;
    const seen: Array<{ scope: string; at: number }> = [];
    const w = new ChangeWatcher(cfg, (scope) => seen.push({ scope, at: Date.now() }));
    w.start();
    try {
      await new Promise((r) => setTimeout(r, 300));
      const t0 = Date.now();
      writeFileSync(path.join(root, "runs", "idle", "discovery", "core.json"), "{}");
      // polling alone rescans an idle run every 5 s; the watch event brings it forward
      for (let i = 0; i < 30 && !seen.some((e) => e.scope === "run:idle"); i++) await new Promise((r) => setTimeout(r, 100));
      const hit = seen.find((e) => e.scope === "run:idle");
      expect(hit).toBeDefined();
      expect(hit!.at - t0).toBeLessThan(3000);
    } finally {
      w.stop();
    }
  });
  it("keeps polling when a pass meets a directory changing under it", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-watch-"));
    for (const r of ["a", "b"]) { mkdirSync(path.join(root, "runs", r, "discovery"), { recursive: true }); writeFileSync(path.join(root, "runs", r, "state.json"), "{}"); }
    const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs"), lib: "Toolkit", papersLib: "Papers", divisions: [] } as unknown as ToolkitConfig;
    const seen: string[] = [];
    const w = new ChangeWatcher(cfg, (scope) => seen.push(scope));
    w.start();
    try {
      writeFileSync(path.join(root, "runs", "a", "annotated"), "not a directory"); // the next pass's readdir throws
      await new Promise((r) => setTimeout(r, 1300));
      writeFileSync(path.join(root, "runs", "b", "discovery", "core.json"), "{}");
      for (let i = 0; i < 30 && !seen.includes("run:b"); i++) await new Promise((r) => setTimeout(r, 100));
      expect(seen).toContain("run:b");
    } finally {
      w.stop();
    }
  });
});

describe("page: a \\ref in text the page sets itself prints the paper's number", () => {
  it("the paper payload carries label → number, and the page's text setter uses it; an unknown label stays visible as written", () => {
    const p = renderPaper({ files: { "m.tex": "\\begin{document}\\begin{lemma}\\label{lem:a}X.\\end{lemma}\\end{document}" }, main: "m.tex", aux: String.raw`\newlabel{lem:a}{{B.5}{3}}` });
    expect(p.labels["lem:a"]).toBe("B.5");
    const js = readFileSync(path.join(__dirname, "..", "..", "src", "ui", "static", "app.js"), "utf8").replace(/\r\n/g, "\n");
    const texText = new Function("P", "esc", `${js.slice(js.indexOf("\nfunction subsup("), js.indexOf("\n}\n", js.indexOf("\nfunction subsup(")) + 2)}${js.slice(js.indexOf("/** The number the paper prints for a label"), js.indexOf("\n}\n", js.indexOf("function texText(t)")) + 2)}; return texText;`)({ paper: p }, (x: string) => x) as (t: string) => string;
    expect(texText("Lemma~\\ref{lem:a} and \\eqref{lem:a}; Lemma~\\ref{lem:zz}")).toBe('Lemma&nbsp;B.5 and (B.5); Lemma&nbsp;<span class="cite">lem:zz</span>');
  });
});

describe("paper page: mathematics written outside a formula, and a heading in the contents", () => {
  const k = (h: string) => h.replace(/<span class="katex">.*?<\/span>(?=[^<]|$)/g, "[K]");
  it("an index outside a formula is no TeX: an agent's Unicode mathematics is set as sub- and superscripts, a name or a label left", () => {
    const { fragment } = paperRenderer({ files: { "m.tex": "\\begin{document}\\section{S}\\label{sec_a}X.\\end{document}" }, main: "m.tex" });
    expect(k(fragment("with ℓ_h ≤ C, x_{i,j}, W^(-1/8), σ²_a, a_i^2, Z_j², d_α(i,j)^r and $a_b$; kept foo_bar_x, a_i_j, h_indep, a\\_b, Section~\\ref{sec_a}").html))
      .toBe('with ℓ<sub>h</sub> ≤ C, x<sub>i,j</sub>, W<sup>(-1/8)</sup>, σ²<sub>a</sub>, a<sub>i</sub><sup>2</sup>, Z<sub>j</sub>², d<sub>α</sub>(i,j)<sup>r</sup> and [K]; kept foo_bar_x, a_i_j, h_indep, a_b, Section&nbsp;<a class="ref" href="#lbl-sec-a">1</a>');
    expect(fragment("\\url{http://a.b/c_d} \\verb|a_b| _x").html).toBe('<a href="http://a.b/c_d" target="_blank" rel="noopener">http://a.b/c_d</a> <code>a_b</code> _x');
  });
  it("the contents carry a heading as it is drawn, its formulas typeset — and no anchor of the heading's", () => {
    const p = renderPaper({ files: { "m.tex": "\\begin{document}\\section{A $2^4$ design\\label{sec:d}}X.\\end{document}" }, main: "m.tex" });
    expect(p.toc[0]!.text).toBe("1 A 24 design");
    expect(p.toc[0]!.html).toMatch(/^1 A <span class="katex">.*<\/span> design/);
    expect(p.toc[0]!.html).not.toContain("id=");
  });
  it("a headline quotes a question cut short, never inside a formula", () => {
    expect(texCut("is $n \\ge 1$?", 160)).toBe("is $n \\ge 1$?");
    expect(texCut("whether $a$ or $b_{n} \\to 0$ is meant", 22)).toBe("whether $a$ or…");
    expect(texCut("a price of \\$5 and more words", 16)).toBe("a price of \\$5 a…");
  });
});

describe("paper page: the author's macros", () => {
  it("an xparse definition with mandatory arguments only is read; one with optional arguments is left", () => {
    const pre = readPreamble(String.raw`\NewDocumentCommand{\indicator}{}{\mathds{1}} \NewDocumentCommand{\pair}{m m}{(#1,#2)} \NewDocumentCommand{\opt}{O{x} m}{#1#2}`);
    expect(pre.macros["\\indicator"]).toBe("\\mathds{1}");
    expect(pre.textMacros["\\pair"]).toEqual({ n: 2, dflt: null, body: "(#1,#2)" });
    expect(pre.macros["\\opt"]).toBeUndefined();
  });
});

describe("paper page: where a note's mark stands and what it stands at", () => {
  it("an anchor marked `after` stands inside the proof it is located at, after the proof's opening", () => {
    const tex = String.raw`\documentclass{article}\newtheorem{lemma}{Lemma}\begin{document}
\begin{lemma}\label{lem:a}A claim.\end{lemma}
\begin{proof}[Proof of Lemma~\ref{lem:a}]
By a cited theorem, done.
\end{proof}
\end{document}`;
    const line = String.raw`\begin{proof}[Proof of Lemma~\ref{lem:a}]`;
    const before = renderPaper({ files: { "m.tex": tex }, main: "m.tex", aux: "", anchors: [{ node: "lem:c", file: "m.tex", line }] }).html;
    const after = renderPaper({ files: { "m.tex": tex }, main: "m.tex", aux: "", anchors: [{ node: "lem:c", file: "m.tex", line, after: true }] }).html;
    const pos = (h: string): [number, number] => [h.indexOf('data-node="lem:c"'), h.indexOf('class="proof"')];
    expect(pos(before)[0]).toBeLessThan(pos(before)[1]);
    expect(pos(after)[0]).toBeGreaterThan(pos(after)[1]);
    expect(after.indexOf('data-node="lem:c"')).toBeLessThan(after.indexOf("By a cited theorem"));
    // a line the file holds twice: the anchor goes to the occurrence nearest its line number
    const two = String.raw`\documentclass{article}\begin{document}
\begin{proof}
First proof, of one result.
\end{proof}
\begin{proof}
Second proof, by a cited lemma.
\end{proof}
\end{document}`;
    const second = renderPaper({ files: { "m.tex": two }, main: "m.tex", aux: "", anchors: [{ node: "lem:d", file: "m.tex", line: String.raw`\begin{proof}`, at: 5, after: true }] }).html;
    expect(second.indexOf('data-node="lem:d"')).toBeGreaterThan(second.indexOf("First proof"));
    expect(second.indexOf('data-node="lem:d"')).toBeLessThan(second.indexOf("Second proof"));
    // the proof's first paragraph stays plain text: it is no block of the cited result
    expect(after).not.toContain('data-res="lem:c"');
    expect(after).not.toContain("prose-res");
  });

  it("TikZ setup the paper writes in its body is no text on the page, and goes to the pictures typeset apart", () => {
    const tex = String.raw`\documentclass{article}\begin{document}
\tikzset{pattern size/.store in=\mcSize, pattern size = 5pt}
\makeatletter
\pgfutil@ifundefined{pgf@pattern@name@_a}{\pgfdeclarepatternformonly[\mcSize]{_a}{\pgfqpoint{0pt}{0pt}}{\pgfpoint{1pt}{1pt}}{\pgfpoint{1pt}{1pt}}{\pgfusepath{stroke}}}
\makeatother
\tikzset{every picture/.style={line width=0.75pt}}
Text after.
\begin{tikzpicture}\draw (0,0) -- (1,1);\end{tikzpicture}
\end{document}`;
    const html = renderPaper({ files: { "m.tex": tex }, main: "m.tex", aux: "" }).html;
    expect(html).not.toMatch(/pattern size|store in|every picture|pgf@pattern|_a/);
    expect(html).toContain("Text after.");
    const setup = tikzSetup({ "m.tex": tex }, "m.tex");
    expect(setup.split("\n")).toEqual([
      String.raw`\tikzset{pattern size/.store in=\mcSize, pattern size = 5pt}`,
      String.raw`\pgfutil@ifundefined{pgf@pattern@name@_a}{\pgfdeclarepatternformonly[\mcSize]{_a}{\pgfqpoint{0pt}{0pt}}{\pgfpoint{1pt}{1pt}}{\pgfpoint{1pt}{1pt}}{\pgfusepath{stroke}}}`,
      String.raw`\tikzset{every picture/.style={line width=0.75pt}}`,
    ]);
    // a macro the body sets with \def before its picture (`\radius`): its body, not the text after it
    const withDef = String.raw`\documentclass{article}\begin{document}
\def\radius{2.6} {Text.}
\begin{tikzpicture}\path (-\radius,0) node {a};\end{tikzpicture}
\end{document}`;
    expect(tikzSetup({ "m.tex": withDef }, "m.tex")).toBe(String.raw`\def\radius{2.6}`);
  });

  it("a TikZ picture is drawn from its page of the PDF typeset for it, and named as left out without one", () => {
    const tex = String.raw`\documentclass{article}\begin{document}
\begin{tikzpicture}[scale=1]\draw (0,0) -- (1,1);\end{tikzpicture}
Text.
\begin{tikzpicture}\node {b};\end{tikzpicture}
\end{document}`;
    const pictures = tikzPictures({ "m.tex": tex }, "m.tex");
    expect(pictures).toEqual([String.raw`[scale=1]\draw (0,0) -- (1,1);`, String.raw`\node {b};`]);
    const drawn = renderPaper({ files: { "m.tex": tex }, main: "m.tex", aux: "", tikz: { url: "/a/_tikz/x.pdf", pictures } }).html;
    expect(drawn).toContain('data-pdf="/a/_tikz/x.pdf" data-page="1"');
    expect(drawn).toContain('data-page="2"');
    expect(drawn).not.toContain("is not shown here");
    expect(renderPaper({ files: { "m.tex": tex }, main: "m.tex", aux: "" }).html).toContain("A drawing (tikzpicture) is not shown here");
  });

  it("a heading's PDF string is not text, and a contents entry is one link: a reference in it is its number", () => {
    const tex = String.raw`\documentclass{article}\newtheorem{assumption}{Assumption}\newcommand{\tps}[1]{\texorpdfstring{#1}.}\begin{document}
\begin{assumption}\label{as:d}A.\end{assumption}
\section{Proof \tps{$D(p)$} satisfies Assumption \ref{as:d}}
Text.
\end{document}`;
    const r = renderPaper({ files: { "m.tex": tex }, main: "m.tex", aux: "" });
    const t = r.toc.find((x) => x.text.includes("Proof"))!;
    expect(t.text).toMatch(/Proof .* satisfies Assumption 1$/);
    expect(t.text).not.toContain(". satisfies");
    expect(t.html).not.toMatch(/<a\b/);
    expect(t.html).toMatch(/satisfies Assumption 1$/);
  });


  it("a brace group around several paragraphs keeps them as paragraphs", () => {
    const tex = String.raw`\documentclass{article}\begin{document}
{\color{black}
Intro para one.

Intro para two.
}
\end{document}`;
    const html = renderPaper({ files: { "m.tex": tex }, main: "m.tex", aux: "" }).html;
    expect(html).not.toContain("one.Intro");
    expect(html).toMatch(/Intro para one\.\s*<\/div>\s*<div class="p">\s*Intro para two\./);
  });

  it("a result stated in running text is a result block; the anchor standing alone before a result's environment is none", () => {
    const tex = String.raw`\documentclass{article}\newtheorem{theorem}{Theorem}\begin{document}
\tcAnchor{thm:b}\textbf{Theorem 2.} In running text, $x=y$.

\tcAnchor{thm:a}\tcAnchor{thm:c}

\begin{theorem}\label{thm:a}A claim.\end{theorem}
\end{document}`;
    const html = renderPaper({ files: { "m.tex": tex }, main: "m.tex", aux: "" }).html;
    expect(html).toMatch(/<div class="p formal prose-res k-theorem" tabindex="0" data-res="thm:b">\s*<span class="res-anchor"[^>]*><\/span>[^]{0,60}Theorem 2\./);
    expect(html).not.toContain(`data-res="thm:a"`);
    expect((html.match(/prose-res/g) ?? []).length).toBe(1);
  });

  it("the notes written right after an environment are its own — their marks end its text; a note further on, in running text, stands at no environment", () => {
    const tex = String.raw`\begin{document}\begin{lemma}\label{lem:a}X holds.\end{lemma}
\vsNote{first} \vsReading{second}

Running text follows. \vsReading{third}

More.\end{document}`;
    const p = renderPaper({ files: { "m.tex": tex }, main: "m.tex", aux: "" });
    expect(p.comments.map((c) => c.env)).toEqual(["lem:a", "lem:a", null]);
    // the two marks close the lemma's text, inside its block; none opens the next paragraph
    expect(p.html).toMatch(/X holds\.\s*<span class="cmark k-note" data-c="c1"[^>]*><\/span>\s*<span class="cmark k-reading" data-c="c2"[^>]*><\/span>\s*<\/div><\/div>/);
    expect(p.html).not.toMatch(/<div class="p">\s*<span class="cmark/);
    expect(p.html).not.toContain("formal-end");
  });
});

// The page's own script: its enumeration cutter, run as written.
describe("page: an inline enumeration is cut into a list", () => {
  const js = readFileSync(path.join(__dirname, "..", "..", "src", "ui", "static", "app.js"), "utf8").replace(/\r\n/g, "\n");
  const enumParts = new Function(`${js.slice(js.indexOf("const ENUM_FAMILIES"), js.indexOf("/** A TeX fragment as HTML, an inline enumeration"))}; return enumParts;`)() as (s: string) => { lead: string; parts: [string, string][] } | null;
  it("from the first marker anywhere, or from a later one that opens the text; never inside mathematics", () => {
    expect(enumParts("Take (a) one; (b) two.")).toEqual({ lead: "Take", parts: [["a", "one;"], ["b", "two."]] });
    expect(enumParts("(b) In the model, $x=1$. (c) Let $X=1$.")!.parts.map((p) => p[0])).toEqual(["b", "c"]);
    expect(enumParts("See clause (b) of it and (c) too.")).toBeNull();
    expect(enumParts("(a) only one.")).toBeNull();
    expect(enumParts("With $f (a) g$ and $h (b) k$.")).toBeNull();
  });
});

describe("fscache: a value is computed again only when what it was made from changed", () => {
  const dir = mkdtempSync(path.join(tmpdir(), "tc-ui-cache-"));
  const file = (name: string, text: string, at = 1_700_000_000) => { const f = path.join(dir, name); writeFileSync(f, text); utimesSync(f, at, at); return f; };

  it("derive: from memory while its files stand, again when one changed; callers that ask meanwhile share the one computation", async () => {
    const a = file("a.txt", "one");
    let runs = 0;
    const get = () => derive("t:derive", [a], "", async () => { runs++; await new Promise((r) => setTimeout(r, 20)); return readFileSync(a, "utf8"); });
    const both = await Promise.all([get(), get()]);
    expect([both.map((x) => x.value), runs]).toEqual([["one", "one"], 1]);
    expect([(await get()).key === both[0]!.key, runs]).toEqual([true, 1]);
    file("a.txt", "three", 1_700_000_100);
    const next = await get();
    expect([next.value, next.key === both[0]!.key, runs]).toEqual(["three", false, 2]);
  });

  it("deriveRead: keyed on the files it read as it went — one changed, one it looked for appearing, or its key", async () => {
    const a = file("r.txt", "x"), missing = path.join(dir, "later.txt");
    let runs = 0;
    const get = (key = "k") => deriveRead("t:read", key, async (read) => { runs++; return `${await read(a)}${(await read(missing)) ?? "-"}`; });
    expect([await get(), await get(), runs]).toEqual(["x-", "x-", 1]);
    file("r.txt", "yy", 1_700_000_100);
    expect([await get(), runs]).toEqual(["yy-", 2]);
    file("later.txt", "!");
    expect([await get(), await get(), runs]).toEqual(["yy!", "yy!", 3]);
    expect([await get("other"), runs]).toEqual(["yy!", 4]);
  });
});

describe("server: a run's views are answered from memory while unchanged", () => {
  it("page detail, drawers and paper: 304 to a client that holds them, anew when an input changed — and only the view it feeds", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-ui-304-"));
    const run = path.join(root, "runs", "p1");
    mkdirSync(path.join(run, "source"), { recursive: true });
    mkdirSync(path.join(run, "discovery"), { recursive: true });
    writeFileSync(path.join(run, "state.json"), JSON.stringify({ verify: { source: { main_file: "m.tex" } } }));
    writeFileSync(path.join(run, "source", "m.tex"), String.raw`\begin{document}Text $y$.\end{document}`);
    writeFileSync(path.join(run, "discovery", "core.json"), JSON.stringify({ statements: [{ id: "thm:t1", kind: "theorem", tex_locator: { file: "m.tex", from: 1 } }] }));
    const review = (detail: string, at: number) => { const f = path.join(run, "discovery", "v1_5_review.json"); writeFileSync(f, JSON.stringify({ nodes: [{ id: "thm:t1", correctness: "error", detail }] })); utimesSync(f, at, at); };
    review("It fails at $n = 1$.", 1_700_000_000);
    const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs"), lib: "Toolkit", papersLib: "Papers", divisions: [], baseLibraries: [], owner: { name: "O" }, leanToolchain: "x" } as unknown as ToolkitConfig;
    const ui = await startUiServer(cfg, { port: 0 });
    try {
      const base = new URL(ui.url).origin;
      const Cookie = ((await fetch(ui.url, { redirect: "manual" })).headers.get("set-cookie") ?? "").split(";")[0]!;
      const views = ["", "/drawers", "/paper"];
      const get = (sub: string, etag?: string) => fetch(`${base}/api/runs/p1${sub}`, { headers: { Cookie, ...(etag ? { "If-None-Match": etag } : {}) } });
      const tags: Record<string, string> = {};
      for (const v of views) { const r = await get(v); expect(r.status).toBe(200); tags[v] = r.headers.get("etag")!; await r.text(); }
      // unchanged: the same tag to a client without one, "not modified" to one that holds it
      for (const v of views) { const r = await get(v); expect([r.status, r.headers.get("etag")]).toEqual([200, tags[v]]); await r.text(); expect((await get(v, tags[v])).status).toBe(304); }
      // the page's detail is what is drawn before a drawer opens; a review's text is the drawers'
      const page = (await (await get("")).json()) as { results: Array<Record<string, unknown>>; texHtml: Record<string, string> };
      expect(page.results).toEqual([expect.objectContaining({ id: "thm:t1", state: "ok", review: { correctness: "error" } })]);
      expect(Object.keys(page.texHtml)).toEqual([]);
      // the referee's text changed: the drawers are answered anew, the page's detail and the paper stand
      review("It fails at $n = 2$.", 1_700_000_100);
      const drawers = await get("/drawers", tags["/drawers"]);
      expect(drawers.status).toBe(200);
      expect(((await drawers.json()) as { texHtml: Record<string, string> }).texHtml["It fails at $n = 2$."]).toContain("katex");
      expect([(await get("", tags[""])).status, (await get("/paper", tags["/paper"])).status]).toEqual([304, 304]);
      // its grade changed: the page's detail too
      const f = path.join(run, "discovery", "v1_5_review.json");
      writeFileSync(f, JSON.stringify({ nodes: [{ id: "thm:t1", correctness: "ok", detail: "It fails at $n = 2$." }] })); utimesSync(f, 1_700_000_200, 1_700_000_200);
      expect((await get("", tags[""])).status).toBe(200);
      // the paper's source changed: the paper, and with it what is rendered under it
      writeFileSync(path.join(run, "source", "m.tex"), String.raw`\begin{document}Other text $z$.\end{document}`);
      utimesSync(path.join(run, "source", "m.tex"), 1_700_000_300, 1_700_000_300);
      const paper = await get("/paper", tags["/paper"]);
      expect(paper.status).toBe(200);
      expect(((await paper.json()) as { html: string }).html).toContain("Other text");
    } finally {
      await ui.close();
    }
  });
});

describe("status: whether a run is running is one reading of its heartbeat, seen in time", () => {
  const root = mkdtempSync(path.join(tmpdir(), "tc-status-"));
  const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs"), lib: "Toolkit", papersLib: "Papers", divisions: [], baseLibraries: [], owner: { name: "Owner" }, leanToolchain: "x" } as unknown as ToolkitConfig;
  const hbFile = (slug: string) => path.join(root, "runs", slug, "logs", ".run.active");
  /** A run in the Lean stages whose log ends at a model call, and no heartbeat. */
  const mk = (slug: string) => {
    mkdirSync(path.join(root, "runs", slug, "logs"), { recursive: true });
    writeFileSync(path.join(root, "runs", slug, "state.json"), JSON.stringify({ stage_completed: "1.5", verify: { phase: "formalization", source: { input: "paper.tex" } } }));
    writeFileSync(path.join(root, "runs", slug, "pipeline.jsonl"), JSON.stringify({ timestamp: "2026-01-01T00:00:00Z", stage: "2", status: "dispatch", message: "F2 scaffolder: prompt 9 bytes from [a.txt]" }) + "\n");
  };
  /** The heartbeat of a runner on another machine, last touched `ageMs` ago. */
  const beatElsewhere = (slug: string, ageMs: number) => {
    writeFileSync(hbFile(slug), "1073741822 2026-01-01T00:00:01.000Z tok host=elsewhere beat=15\n");
    const at = new Date(Date.now() - ageMs); utimesSync(hbFile(slug), at, at);
  };
  const waitFor = async (ok: () => boolean, ms: number) => { for (const t0 = Date.now(); Date.now() - t0 < ms && !ok();) await new Promise((r) => setTimeout(r, 50)); return ok(); };

  it("a fresh heartbeat written on another machine of the mount is a running run — its pid is nobody's here", async () => {
    mk("far");
    expect(await runSummary(cfg, "far")).toMatchObject({ status: "needs-you", live: false });
    beatElsewhere("far", 0);
    expect(runLive(cfg, "far")).toEqual({ live: true, pid: null, since: "2026-01-01T00:00:01.000Z", elsewhere: "elsewhere" });
    expect(await runSummary(cfg, "far")).toMatchObject({ status: "running", live: true, stageIndex: 3 });
    // one that stopped beating (four beats and the margin) is not
    // a runner killed in V1 or V1.5 writes no line the log could end on: its heartbeat, left behind, says so
    mkdirSync(path.join(root, "runs", "v-killed", "logs"), { recursive: true });
    writeFileSync(path.join(root, "runs", "v-killed", "state.json"), JSON.stringify({ stage_completed: "V1", verify: { phase: "v1", source: { input: "paper.tex" } } }));
    expect(await runSummary(cfg, "v-killed")).toMatchObject({ status: "idle" });
    writeFileSync(hbFile("v-killed"), "1073741822 2026-01-01T00:00:01.000Z tok beat=15\n");
    expect(await runSummary(cfg, "v-killed")).toMatchObject({ status: "needs-you", toResume: true, headline: "ended without a halt (crashed or killed) during V1.5 — resume the run" });
    mk("far-gone"); beatElsewhere("far-gone", 91_000);
    expect(await runSummary(cfg, "far-gone")).toMatchObject({ status: "needs-you", live: false });
  });

  it("a runner that dies without a word flips the run to not running, and the page is told — no file changed", async () => {
    mk("killed");
    const runner = spawn("sleep", ["60"]);
    writeFileSync(hbFile("killed"), `${runner.pid} 2026-01-01T00:00:01.000Z tok beat=15\n`);
    // one on another machine, three seconds from stale
    mk("silent"); beatElsewhere("silent", 87_000);
    const seen: string[] = [];
    const w = new ChangeWatcher(cfg, (scope) => seen.push(scope));
    w.start();
    try {
      expect((await runSummary(cfg, "killed")).status).toBe("running");
      expect((await runSummary(cfg, "silent")).status).toBe("running");
      runner.kill("SIGKILL");
      expect(await waitFor(() => seen.includes("run:killed") && seen.includes("run:silent"), 8000)).toBe(true);
      // (its log ends at a model call: it ended without a halt, and is to be resumed)
      expect(await runSummary(cfg, "killed")).toMatchObject({ status: "needs-you", headline: "ended without a halt (crashed or killed) during F2 — resume the run" });
      expect((await runSummary(cfg, "silent")).status).toBe("needs-you");
      // … and a start is told as well: the heartbeat is in a directory no watch covers
      seen.length = 0;
      beatElsewhere("silent", 0);
      expect(await waitFor(() => seen.includes("run:silent"), 4000)).toBe(true);
      // a beat (the file touched again) is no change of state: nothing is pushed for it
      seen.length = 0;
      const now = new Date(); utimesSync(hbFile("silent"), now, now);
      await new Promise((r) => setTimeout(r, 2500));
      expect(seen).toEqual([]);
    } finally {
      w.stop(); runner.kill("SIGKILL");
    }
  }, 30_000);

  it("the view a client holds does not outlive the run's state: asked again with its tag, a run that started since is sent", async () => {
    mk("held");
    const ui = await startUiServer(cfg, { port: 0 });
    try {
      const base = new URL(ui.url).origin;
      const Cookie = ((await fetch(ui.url, { redirect: "manual" })).headers.get("set-cookie") ?? "").split(";")[0]!;
      const get = (etag?: string) => fetch(`${base}/api/runs/held`, { headers: { Cookie, ...(etag ? { "If-None-Match": etag } : {}) } });
      const idle = await get();
      expect((await idle.json()).summary.status).toBe("needs-you");
      const tag = idle.headers.get("etag")!;
      expect((await get(tag)).status).toBe(304);
      beatElsewhere("held", 0);
      const now = await get(tag);
      expect(now.status).toBe(200);
      expect((await now.json()).summary).toMatchObject({ status: "running", live: true });
      // the page cannot stop a runner on another machine: its pid is not a process of this one
      const stop = await fetch(`${base}/api/runs/held/action`, { method: "POST", headers: { Cookie, "X-TC": "1", "Content-Type": "application/json" }, body: JSON.stringify({ action: { kind: "stop" } }) });
      expect(stop.status).toBe(409);
      expect((await stop.json()).error).toContain("runs on elsewhere");
      // the event stream says which page files stand, and pings as events (the page hears a silence)
      const es = await fetch(`${base}/api/events`, { headers: { Cookie } });
      const hello = new TextDecoder().decode((await es.body!.getReader().read()).value);
      expect(hello).toMatch(/^event: hello\ndata: \{"boot":"[^"]+","assets":"[^"]+"\}/);
    } finally {
      await ui.close();
    }
  });
});

describe("server: the owner shares a finished paper on the public site", () => {
  afterAll(() => { for (const d of tmpDirs.splice(0)) rmSync(d, { recursive: true, force: true }); });
  it("shows what would be published; sends only with the session key, the page's header and the confirmation; refuses a run that is not finished; the page's detail then follows the share, without its token", async () => {
    const svc = fakeService();
    const { root, run } = await finishedRun();
    const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs"), lib: "Toolkit", papersLib: "Papers", divisions: [], baseLibraries: [], owner: { name: "O" }, leanToolchain: "x" } as unknown as ToolkitConfig;
    const ui = await startUiServer(cfg, { port: 0, share: { service: SERVICE, fetch: svc.fetch } });
    try {
      const at = `${new URL(ui.url).origin}/api/runs/a_paper`;
      const Cookie = ((await fetch(ui.url, { redirect: "manual" })).headers.get("set-cookie") ?? "").split(";")[0]!;
      const call = async (method: "GET" | "POST", body?: unknown, headers: Record<string, string> = { Cookie, "X-TC": "1" }) => {
        const r = await fetch(`${at}/share`, { method, headers: method === "GET" ? { Cookie } : headers, ...(body === undefined ? {} : { body: JSON.stringify(body) }) });
        return { status: r.status, ...(await r.json() as object) } as { status: number | string; error?: string; nonce?: string; id?: string; claim_url?: string; check_code?: string };
      };
      const stage = (s: string) => writeFileSync(path.join(run, "state.json"), JSON.stringify({ stage_completed: s, verify: { phase: s === "V6" ? "done" : "formalization" } }));

      // what the dialog shows: the paper, what is sent, where it is published, how it is confirmed, and the warning of the command
      const shown = await call("GET");
      expect(shown).toMatchObject({ status: 200, slug: "a_paper", title: "A Paper on Bounds", files: 11, url: paperUrl("a_paper"), signIn: SHARE_SIGN_IN, warning: shareWarning() });
      expect(shown.nonce).toMatch(/^[\w-]{24}$/);
      const key = async () => (await call("GET")).nonce!;
      const again = { status: 400, error: "not shared: open the Share dialog again (its confirmation is good once, for ten minutes)" };
      // nothing is sent without the session key, the page's header, or the confirmation
      expect((await call("POST", { understood: true, nonce: await key() }, { "X-TC": "1" })).status).toBe(403);
      expect((await call("POST", { understood: true, nonce: await key() }, { Cookie })).status).toBe(403);
      expect(await call("POST", { nonce: await key() })).toMatchObject({ status: 400, error: "not shared: the confirmation is missing" });
      expect((await call("POST", { understood: "true", nonce: await key() })).status).toBe(400);
      // … nor without the key the dialog was shown with: none, one made up
      expect(await call("POST", { understood: true })).toMatchObject(again);
      expect(await call("POST", { understood: true, nonce: "x".repeat(24) })).toMatchObject(again);
      // … nor when the bundle is no longer the one shown; the key is then spent
      const stale = await key();
      const report = path.join(run, "bundle", "REPORT.md");
      writeFileSync(report, "# Report, changed after the dialog\n");
      expect(await call("POST", { understood: true, nonce: stale })).toMatchObject({ status: 409, error: "not shared: the bundle changed after it was shown — open the Share dialog again" });
      writeFileSync(report, "# Report\n");
      expect(await call("POST", { understood: true, nonce: stale })).toMatchObject(again);
      // … nor of a run that is not finished
      stage("5");
      expect(await call("GET")).toMatchObject({ status: 400, error: "cannot share a_paper: the run is not finished (its last completed stage is 5, not V6)" });
      expect((await call("POST", { understood: true, nonce: shown.nonce })).error).toMatch(/the run is not finished/);
      expect(svc.calls).toEqual([]);
      expect(existsSync(path.join(run, "share.json"))).toBe(false);
      expect((await fetch(`${at}/share-status`, { headers: { Cookie } })).status).toBe(404);

      stage("V6");
      const once = await key();
      const sent = await call("POST", { understood: true, nonce: once });
      // the answer is where the owner signs in and confirms; the token that reads the share's status stays in the run
      expect(sent).toMatchObject({ status: "awaiting_sign_in", id: expect.any(String), claim_url: `${SERVICE}/claim/${sent.id}`, check_code: "K7PQ" });
      expect(sent).not.toHaveProperty("poll_token");
      // a key is good once
      expect(await call("POST", { understood: true, nonce: once })).toMatchObject(again);
      const detail = async () => ((await (await fetch(at, { headers: { Cookie } })).json()) as { share: Record<string, unknown> | null }).share;
      expect(await detail()).toMatchObject({ status: "awaiting_sign_in", claim_url: sent.claim_url, check_code: "K7PQ" });
      expect(await detail()).not.toHaveProperty("poll_token");
      // the page asks where it stands; the server asks the service and records the outcome
      svc.confirm(sent.id!, "alice");
      svc.finish(sent.id!, { kind: "published", url: paperUrl("a_paper") });
      const status = await (await fetch(`${at}/share-status`, { headers: { Cookie } })).json() as Record<string, unknown>;
      expect(status).toMatchObject({ status: "published", login: "alice", url: paperUrl("a_paper") });
      expect(status).not.toHaveProperty("poll_token");
      expect(await detail()).toMatchObject({ status: "published", login: "alice" });
    } finally {
      await ui.close();
    }
  }, 180_000);
});

// The finding: the proof map drew "Lem ?" for a result in an unlabelled \begin{corollary} and for every
// cited result, and nothing told the orchestrator.
describe("results the page names on the proof map", () => {
  it("takes an unlabelled environment's heading and reports a result it cannot name", async () => {
    const { runPaper } = await import("../../src/ui/page_snapshot.js");
    const dir = mkdtempSync(path.join(tmpdir(), "tc-pm-"));
    mkdirSync(path.join(dir, "source"), { recursive: true });
    mkdirSync(path.join(dir, "discovery"), { recursive: true });
    writeFileSync(path.join(dir, "state.json"), "{}");
    writeFileSync(path.join(dir, "source", "m.tex"), "\\documentclass{article}\\newtheorem{corollary}{Corollary}\n\\begin{document}\n\\begin{corollary}\\label{c1}A.\\end{corollary}\n\\begin{corollary}\nUnder the assumptions the conclusions hold.\n\\end{corollary}\nEarlier work gives an approximation algorithm \\cite{Prior09}.\n\\end{document}\n");
    writeFileSync(path.join(dir, "discovery", "core.json"), JSON.stringify({ statements: [
      { id: "thm:c1", tex_locator: { file: "m.tex", from: 3, label: "c1", env: "corollary" } },
      { id: "thm:c2", tex_locator: { file: "m.tex", from: 4, label: null, env: "corollary" } },
      { id: "thm:x", tex_locator: { file: "m.tex", from: 5, label: null, env: "theorem" } },
      { id: "lem:cit", cited_in: "thm:c1" },
      { id: "lem:prior", kind: "lemma", status: "cited", source: { cite: "Prior09", locator: "Theorem 3" }, tex_locator: { file: "m.tex", from: 7, label: null, env: "segment" } },
      { id: "lem:missing", kind: "lemma", status: "cited", source: { cite: "Prior09" } },
    ] }));
    const { view } = await (await runPaper(dir, "/asset"))!.render();
    expect(view.anchorHeadings["thm:c2"]).toBe("Corollary 2");
    expect(view.anchorHeadings["lem:prior"]).toBe("[Prior09, Theorem 3]");
    expect(view.renderProblems.unnamedResults).toEqual(["thm:x", "lem:missing"]);
  });

  it("names a cited prose result whose label belongs to an equation inside it", async () => {
    const { runPaper } = await import("../../src/ui/page_snapshot.js");
    const dir = mkdtempSync(path.join(tmpdir(), "tc-pm-eq-"));
    mkdirSync(path.join(dir, "source"), { recursive: true });
    mkdirSync(path.join(dir, "discovery"), { recursive: true });
    writeFileSync(path.join(dir, "state.json"), "{}");
    writeFileSync(path.join(dir, "source", "m.tex"), String.raw`\documentclass{article}
\begin{document}
An earlier theorem gives feasibility exactly when
\begin{equation}\label{eq:criterion}a\leq b.\end{equation}
\end{document}
`);
    writeFileSync(path.join(dir, "discovery", "core.json"), JSON.stringify({ statements: [
      { id: "lem:feasibility", kind: "lemma", status: "cited", source: { cite: "Book", locator: "Theorem 3" }, tex_locator: { file: "m.tex", from: 3, to: 4, label: "eq:criterion", env: "segment" } },
    ] }));
    const { view } = await (await runPaper(dir, "/asset"))!.render();
    expect(view.anchors["lem:feasibility"]).toBeTruthy();
    expect(view.labels["eq:criterion"]).toBeTruthy();
    expect(view.anchorHeadings["lem:feasibility"]).toBe("[Book, Theorem 3]");
    expect(view.renderProblems.unnamedResults).toEqual([]);
  });
});

// The finding: an anchor was placed at the occurrence nearest the source line number, but the page renders the
// annotated copy, whose lines have shifted: a result sat at another theorem.
describe("an anchor in a file whose lines have shifted", () => {
  it("goes to the same occurrence of its line as in the source", () => {
    const body = "\\begin{theorem}\nA.\n\\end{theorem}\n\\begin{theorem}\nB.\n\\end{theorem}\n\\begin{theorem}\nC.\n\\end{theorem}\n";
    const shifted = "x\n".repeat(40) + body;
    const r = renderPaper({ files: { "m.tex": `\\documentclass{article}\\newtheorem{theorem}{Theorem}\\begin{document}\n${shifted}\\end{document}` }, main: "m.tex",
      anchors: [{ node: "thm:c", file: "m.tex", line: "\\begin{theorem}", at: 7, nth: [2, 3] }] });
    const at = r.html.indexOf('data-node="thm:c"');
    expect(at).toBeGreaterThan(r.html.indexOf("B."));
    expect(at).toBeLessThan(r.html.indexOf("C."));
  });
});

// The finding: a symbol reading's label the annotated paper wrapped with local definitions
// (`{\providecommand{\fp}[2]{…}$\fp{\s}{x}$}`) was sent whole to the formula renderers and failed.
describe("a symbol label carrying local definitions", () => {
  it("is drawn as one formula with its definitions", () => {
    const r = renderPaper({ files: { "m.tex": String.raw`\documentclass{article}\begin{document}Text.\vsReadingSymbol{{\providecommand{\fp}[2]{z_{1,#1}(#2)}$\fp{a}{x}$}}{A reading.}\end{document}` }, main: "m.tex" });
    expect(r.health.mathFailures).toEqual([]);
    expect(JSON.stringify(r.comments)).toContain("katex");
    // a starred definition, an optional argument and a space before it are skipped, never drawn
    const r2 = renderPaper({ files: { "m.tex": String.raw`\documentclass{article}\begin{document}Text.\vsReadingSymbol{{\providecommand*{\fs} [1][a]{S_{#1}}$\alpha$}}{A reading.}\newcommand*{\fs}[1][a]{S_{#1}}\end{document}` }, main: "m.tex" });
    expect(r2.health.mathFailures).toEqual([]);
    expect(JSON.stringify(r2.comments)).not.toContain("S_");
  });
});
