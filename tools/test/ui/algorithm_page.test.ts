/**
 * An algorithm on the paper page: each line is its number and ONE block of content, so a step's text,
 * its math and a list nested in it flow as in a paragraph; lines are left-aligned and indented by
 * nesting depth; a display scrolls inside its line; a repaired step's printed and corrected blocks
 * stand one under the other in the step's line. The layout is CSS: only the lines are a grid.
 */
import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { renderPaper } from "../../src/ui/tex_html.js";

const TEX = String.raw`\documentclass{article}\begin{document}
\begin{algorithm}[!tb]
  \caption{Algorithm for NETE Estimation}\label{alg:nete}
  \begin{algorithmic}[1]
    \REQUIRE Dataset $\mathcal{D}$, threshold $t$, estimator
    \STATE Randomly split $\mathcal{D}$ into two equal parts $\mathcal{D}_1$ and $\mathcal{D}_2$
    \STATE Using $\mathcal{D}_1$, estimate:
    \begin{enumerate}[label=\alph*.]
      \item Propensity function $\hat p(x)$ via regression of $D$ on $X$
      \item Pseudo-outcome regression $\hat g(x,d,s)$ by regressing $Y/\|U\|^{\hat{\alpha}_{n}}$ on $(X,D,U/\|U\|)$
    \end{enumerate}
      \IF{estimator = IPW}
        \STATE Compute
        \begin{equation}
            \hat\eta_{n,t}^{\mathrm{IPW}} = \frac{1}{|\mathcal{I}|} \sum_{i\in\mathcal{I}} \frac{Y_i}{\|U_i\|^{\hat{\alpha}_n} }.\label{eq:eta_ipw}
        \end{equation}
      \ELSE
        \STATE Compute
        \begin{equation}
            \hat\eta_{n,t}^{\mathrm{DR}} = \frac{1}{|\mathcal{I}|} \sum_{i\in\mathcal{I}}\Bigl[\hat g(X_i,1,S_i)-\hat g(X_i,0,S_i)\Bigr]. \label{eq:eta_dr}
        \end{equation}
      \ENDIF
      \STATE \vsOriginal{Compute adaptive Hill estimator on $\{\|U_i\|:i\in\mathcal{I}\}$:
      \begin{equation}\label{eq:mu}
          \hat\gamma_n = \frac{1}{k} \sum_{j=1}^{k} \log\frac{\|U_{(j)}\|}{\|U_{(j+1)}\|},
      \end{equation}
    \textbf{Return}:  $\hat\eta\cdot\hat\mu_n.$} \vsCorrected{Compute the Hill estimator on all radii: \vsFit{\hat\gamma_n = 1.} Return $\hat\eta\cdot\hat\mu_n$.}
  \end{algorithmic}
\end{algorithm}
\end{document}`;

const html = renderPaper({ files: { "m.tex": TEX }, main: "m.tex", aux: "" }).html;
const fig = html.slice(html.indexOf('<figure class="alg"'), html.indexOf("</figure>"));
/** The algorithm's lines: indent level, number, content. */
const lines = [...fig.matchAll(/<li style="--lvl:(\d)"><span class="ln">(\d*)<\/span><span class="lt">([\s\S]*?)<\/span><\/li>(?=<li style|<\/ol>\s*$)/g)].map((m) => ({ lvl: Number(m[1]), n: m[2]!, body: m[3]! }));

describe("page: an algorithm's lines", () => {
  it("every line is its number and one content block; the body of the if / else is one level in; the input line is unnumbered with its bold label", () => {
    expect(lines.map((l) => `${l.lvl}:${l.n}`)).toEqual(["0:", "0:1", "0:2", "0:3", "1:4", "0:5", "1:6", "0:7", "0:8"]);
    expect(lines[0]!.body).toMatch(/^<b class="kw">Require:<\/b>/);
    expect(lines[3]!.body).toBe('<b class="kw">if</b> estimator = IPW <b class="kw">then</b>');
    expect(lines[7]!.body).toBe('<b class="kw">end if</b>');
  });

  it("a list nested in a step: its items inside the step's block, labelled as the paper labels them, each item's text and math one inline flow", () => {
    const step = lines[2]!.body;
    expect(step).toMatch(/^\s*Using [\s\S]*, estimate:\s*<ol class="enumerate" type="a"><li>/);
    const items = [...step.matchAll(/<li>([\s\S]*?)<\/li>/g)].map((m) => m[1]!);
    expect(items).toHaveLength(2);
    for (const it of items) {
      // nothing but the math renderer's inline spans: no block, no per-word element
      expect(it).not.toMatch(/<(?:div|p|li|ol|ul|table)\b/);
      expect(it.replace(/<span class="katex">[\s\S]*?<\/span>(?= |$)/g, "")).not.toMatch(/<span(?! class="(?:katex|mord|mopen|mclose|base|strut|mspace|mrel|mbin|mpunct|vlist|msupsub|pstrut|sizing|mfrac|frac-line|mop|minner|delimsizing|accent|svg-align|overlay|hide-tail|nulldelimiter|op-symbol)[^"]*"| style=|>)/);
    }
    expect(items[0]!.trimStart().startsWith("Propensity function ")).toBe(true);
    expect(items[0]).toContain(" via regression of ");
    expect(items[1]!.trimStart().startsWith("Pseudo-outcome regression ")).toBe(true);
  });

  it("a display inside a step is in a scroll container inside the step's block", () => {
    for (const k of [4, 6]) expect(lines[k]!.body).toMatch(/^\s*Compute\s*<div class="eq">[\s\S]*<\/div>\s*$/);
  });

  it("a repaired step keeps its printed and its corrected block in the one step line, the corrected right under the printed", () => {
    const step = lines[8]!.body;
    expect(step).toMatch(/^\s*<div class="rv del"[^>]*><span class="rv-tag">Original<\/span>[\s\S]*<div class="eq">[\s\S]*<strong>Return<\/strong>[\s\S]*<\/div>\s*<div class="rv ins"[^>]*><span class="rv-tag">Corrected<\/span>[\s\S]*<\/div>\s*$/);
    expect(fig.match(/class="rv (?:del|ins)"/g)).toHaveLength(2);
  });
});

describe("page: the algorithm's layout", () => {
  const css = readFileSync(new URL("../../src/ui/static/app.css", import.meta.url), "utf8").replace(/\/\*[\s\S]*?\*\//g, "");
  const rule = (sel: string): string => new RegExp(`(?:^|\\n|,\\s*)${sel.replace(/[.*+?^${}()|[\]\\>]/g, "\\$&")}\\s*(?:,[^{]*)?\\{([^}]*)\\}`).exec(css)?.[1] ?? "";
  it("only the lines are a grid — never a list item inside one; the content column may shrink, so a display scrolls instead of running out of the box", () => {
    expect(rule("ol.algo > li")).toContain("display: grid");
    expect(rule("ol.algo > li")).toContain("minmax(0, 1fr)");
    expect(rule("ol.algo > li")).toContain("padding-left: calc(var(--lvl, 0) * 1.3rem)");
    expect(css).not.toMatch(/ol\.algo(?::not\(\.numbered\))? li\s*\{/);
    expect(rule("ol.algo .lt")).toContain("display: block");
    expect(rule("ol.algo .lt")).toContain("min-width: 0");
    expect(rule(".eq")).toContain("overflow-x: auto");
  });
  it("an algorithm is left-aligned (a figure centres its content)", () => {
    expect(rule("figure")).toContain("text-align: center");
    expect(rule("figure.alg")).toContain("text-align: left");
  });
});

describe("an algorithm the annotated paper replaces whole", () => {
  it("draws the printed and the corrected pseudocode each inside its block, each with its own caption", () => {
    const r = renderPaper({ files: { "m.tex": String.raw`\documentclass{article}\begin{document}
\begin{algorithm}[t]
  \vsOriginal{\SetAlgoNoEnd
    \caption{$S(x)$}\label{alg:s}
    \textbf{Input:} $x$\;
    \For{$i = 1, \dots, k$}{ Set $y = x$ \hfill \tcp{a comment} }
    \textbf{return} $y$} \vsCorrected{\SetAlgoNoEnd
\caption{$S(x_m)$}
\textbf{Input:} $x_m$\;
\For{$i=1,\ldots,k$}{ Draw $z$\; }
\textbf{return} $z$}
\end{algorithm}
See Algorithm~\ref{alg:s}.\end{document}` }, main: "m.tex" });
    expect(r.health.unknownCommands).toEqual({});
    const html = r.html.replace(/<span class="katex[\s\S]*?<\/annotation>/g, "M");
    const del = /<div class="rv del"[^>]*>([\s\S]*?)<\/div><div class="rv ins"/.exec(r.html)?.[1] ?? "";
    const ins = /<div class="rv ins"[^>]*>([\s\S]*)<\/figure>/.exec(r.html)?.[1] ?? "";
    // each block holds its whole algorithm: the lines and the return, not only the tag
    expect(del).toContain("Original");
    expect(del).toContain("a comment");
    expect(del).toMatch(/return/);
    expect(ins).toContain("Corrected");
    expect(ins).toContain("Draw");
    expect(ins).toMatch(/return/);
    // the corrected caption is its block's heading, not text run into its first line
    expect(ins).toMatch(/<div class="alg-cap">[\s\S]*?<\/div>/);
    expect(del).toMatch(/<div class="alg-cap">/);
    expect(html).toContain("<b>Algorithm 1.</b>");
    expect(r.html).toContain('id="lbl-alg-s"');
  });
});

describe("a float that holds neither algorithmic nor algorithm2e", () => {
  it("stays a plain list though its caption has a thin space", () => {
    const r = renderPaper({ files: { "m.tex": String.raw`\documentclass{article}\begin{document}\begin{algorithm}\caption{Cost $n\;m$}\begin{enumerate}\item Step one \item Step two\end{enumerate}\end{algorithm}\end{document}` }, main: "m.tex" });
    expect(r.html).not.toContain('<ol class="algo">');
    expect(r.html).toContain("Step two");
  });
});

describe("an algorithm2e comment", () => {
  it("is read to any depth of braces", () => {
    const r = renderPaper({ files: { "m.tex": String.raw`\documentclass{article}\begin{document}\begin{algorithm}\caption{SL}
Set $i = i + 1$ \hfill \tcp{\footnotesize {Continued until $\abs{C^i} = 1$ to define variables}}\;
\For{$j = 1$}{ step\; \tcp*[f]{plain} }
\end{algorithm}\end{document}` }, main: "m.tex" });
    expect(r.health.unknownCommands).toEqual({});
    const text = r.html.replace(/<span class="katex[\s\S]*?<\/annotation>/g, "M").replace(/<[^>]+>/g, "").replace(/\s+/g, " ");
    expect(text).toContain("▷ Continued until");
    expect(text).toContain("to define variables");
    expect(text).toContain("▷ plain");
  });
});

describe("a result numbered by hand", () => {
  it("an unnumbered environment whose note is only a number is named by it, in its heading and its references", () => {
    const r = renderPaper({ files: { "m.tex": String.raw`\documentclass{article}\usepackage{amsthm}\newtheorem*{corollary*}{Corollary}\begin{document}
\section{A}\section{B}\section{C}
\begin{corollary*}[(3.2)]\label{cor:3.2} $x=1$. \end{corollary*}
\begin{corollary*}[Main bound]\label{cor:m} $y=1$. \end{corollary*}
By Corollary~\ref{cor:3.2}.\end{document}` }, main: "m.tex", aux: String.raw`\newlabel{cor:3.2}{{3}{1}}` });
    expect(r.envs.map((e) => e.heading)).toEqual(["Corollary 3.2", "Corollary"]);
    expect(r.html).toContain(`href="#lbl-cor-3-2">3.2</a>`);
    expect(r.html).toContain("Corollary (Main bound).");
  });
});
