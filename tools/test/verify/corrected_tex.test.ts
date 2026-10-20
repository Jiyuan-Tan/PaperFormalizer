import { describe, expect, it } from "vitest";
import { blueTex } from "../../src/verify/annotate_tex.js";
import { auxLabels, correctedTex, envSpanOfLabel, labelsOf, laid, readGroup, refsIn, restoreNumbers } from "../../src/verify/corrected_tex.js";

const OPTS = { proofEnv: true };
const at = (node: string, kind: string): string => `\\vsAt{${node}}{${kind}}`;

describe("correctedTex — the corrected paper's source", () => {
  it("writes a correction in place of the printed passage and drops the note; nothing of the review is left", () => {
    const tagged =
      `\\begin{theorem}\\label{thm:a}${at("thm:a", "printed")}\\vsOriginal{The rate is $n^{-1/2}$.} ${at("thm:a", "error (repaired)")}\\vsCorrected{The rate is $n^{-1/3}$.} ` +
      `${at("thm:a", "error (repaired)")}\\vsNote{\\vsLine\\textbf{Claim:} the rate. \\vsLine\\textbf{What is wrong:} it is slower.}\n\\end{theorem}\nNext.`;
    const r = correctedTex(tagged, OPTS);
    expect(r.tex).toBe("\\begin{theorem}\\label{thm:a} The rate is $n^{-1/3}$.\n\\end{theorem}\nNext.");
    expect(r.tex).not.toMatch(/\\vs[A-Z]|Claim|LeanSmith/u);
    expect(r.items).toEqual([]);
  });

  it("keeps a printed passage that has no correction, and lists a refuted result with no repair at its line", () => {
    const tagged = `Intro.\n\\begin{theorem}${at("thm:b", "printed")}\\vsOriginal{Every $T_n$ is normal.} ${at("thm:b", "error (not repaired)")}\\vsNote{refuted} \\end{theorem}`;
    const r = correctedTex(tagged, OPTS);
    expect(r.tex).toBe("Intro.\n\\begin{theorem}Every $T_n$ is normal. \\end{theorem}");
    expect(r.items).toEqual([{ kind: "not-repaired", node: "thm:b", line: 2, detail: expect.stringContaining("no repair was adopted") }]);
  });

  it("pairs each printed passage with the next correction of ITS node, also when another node's note lies between", () => {
    const tagged =
      `${at("thm:a", "printed")}\\vsOriginal{A.} ${at("ass:x", "error (repaired)")}\\vsNote{on x} ${at("thm:a", "error (repaired)")}\\vsCorrected{A'.} ` +
      `${at("thm:a", "printed")}\\vsOriginal{B.} ${at("thm:a", "error (repaired)")}\\vsNote{n}`;
    expect(correctedTex(tagged, OPTS).tex.trim()).toBe("A'. B.");
  });

  it("does not write a condition's correction that lies inside a restated statement, nor one whose passage was not found", () => {
    const tagged =
      `${at("thm:a", "printed")}\\vsOriginal{Under regularity conditions, P.} ${at("thm:a", "error (repaired)")}\\vsCorrected{Suppose Q. Then P.} ` +
      `${at("ass:r", "error (repaired); overlapped")}\\vsCorrected{Q holds.} ${at("ass:r", "error (repaired); overlapped")}\\vsNote{n} ` +
      `${at("lem:z", "error (repaired); unlocated")}\\vsCorrected{Z'.} ${at("lem:z", "error (repaired); unlocated")}\\vsNote{n}`;
    const r = correctedTex(tagged, OPTS);
    expect(r.tex.trim()).toBe("Suppose Q. Then P.");
    expect(r.items.map((i) => [i.kind, i.node])).toEqual([["superseded", "ass:r"], ["unplaced", "lem:z"]]);
    expect(r.items[1]!.detail).toContain("Z'.");
  });

  it("a correction that could not be typeset (printed verbatim in the annotated paper) is not written: the printed text stays, listed", () => {
    const tagged = `${at("thm:a", "printed")}\\vsOriginal{P.} ${at("thm:a", "error (repaired)")}\\vsCorrected{\\texttt{bad \\textbackslash{}tex}}`;
    const r = correctedTex(tagged, OPTS);
    expect(r.tex.trim()).toBe("P.");
    expect(r.items[0]).toMatchObject({ kind: "unplaced", node: "thm:a" });
  });

  it("the readings set at one place are one remark of the paper, notation apart; no word of the review", () => {
    const tagged =
      "\\end{theorem}\\vsReading{$n\\geq 2$}\\vsReadingOwner{The limit is in probability.}\\vsReading{$n\\geq 2$}\\vsReadingSymbol{$\\beta$}{$\\beta$ is the slope.}\nText after.";
    const r = correctedTex(tagged, OPTS);
    expect(r.tex).toBe("\\end{theorem}\n\n\\noindent\\textit{Remark.} $n\\geq 2$. The limit is in probability.\n\n\\noindent\\textit{Remark (notation).} $\\beta$ is the slope.\n\nText after.");
    expect(r.tex).not.toMatch(/Clarification|owner/u);
  });

  it("the conditions added to a result are the last paragraph of its statement; one that does not typeset is listed, not written", () => {
    const one = correctedTex(`\\begin{theorem}\nThe rate is $n^{-1/2}$.\n${at("thm:a", "condition added")}\\vsCondition{$X$ is measurable}\\end{theorem}\\vsReading{$n\\geq 2$}\nNext.`, OPTS);
    expect(one.tex).toBe("\\begin{theorem}\nThe rate is $n^{-1/2}$.\n\n\\emph{Additional condition.} $X$ is measurable.\n\\end{theorem}\n\n\\noindent\\textit{Remark.} $n\\geq 2$.\n\nNext.");
    expect(one.items).toEqual([]);
    const two = correctedTex(`\\begin{theorem}\nP.\n\\vsCondition{A holds.}\\vsConditionOwner{B holds.}\\vsConditionOwner{A holds.}${at("thm:a", "condition added")}\\vsCondition{\\texttt{raw}}\\end{theorem}`, OPTS);
    expect(two.tex).toBe("\\begin{theorem}\nP.\n\n\\emph{Additional conditions.} A holds. B holds.\n\\end{theorem}");
    expect(two.items).toEqual([expect.objectContaining({ kind: "unplaced", node: "thm:a", detail: expect.stringContaining("the condition added to it was not written into the paper") })]);
    // a result stated in running text: a paragraph after its statement
    expect(correctedTex("\\textbf{Theorem 1.} It is consistent.\\vsCondition{$n \\ge 2$.}\n\nThe next result.", OPTS).tex).toBe("\\textbf{Theorem 1.} It is consistent.\n\n\\emph{Additional condition.} $n \\ge 2$.\n\nThe next result.");
  });

  it("a corrected proof is a proof of the paper; one beside the printed proof, or with no printed proof found, is listed", () => {
    const after = correctedTex(`\\end{proof}\n${at("thm:a", "corrected proof; after-proof")}\\vsProof{Put $x=1$. \\vsFit{x^2=1.} Done.}\n`, OPTS);
    expect(after.tex).toBe("\\end{proof}\n\n\\begin{proof}\nPut $x=1$. \n\\[\nx^2=1.\n\\]\n Done.\n\\end{proof}\n\n");
    expect(after.items.map((i) => i.kind)).toEqual(["second-proof"]);
    const none = correctedTex(`${at("thm:a", "corrected proof; no proof located")}\\vsProof{Trivial.}`, { proofEnv: false });
    expect(none.tex.trim()).toBe("\\noindent\\textit{Proof.} Trivial.");
    expect(none.items.map((i) => i.kind)).toEqual(["proof-added"]);
    expect(correctedTex(`${at("thm:a", "corrected proof; no printed proof")}\\vsProof{Trivial.}`, OPTS).items).toEqual([]);
  });

  it("a corrected proof replaces the printed proof environment the view marks: once, in its place, under the printed title; a label it drops is listed", () => {
    const mark = (end: boolean): string => `${at("thm:a", "printed proof")}\\vsPrintedProof{${end ? "end" : "begin"}}`;
    const printed = "\\begin{proof}[Proof of Theorem~\\ref{thm:a}]\nOld.\n\\begin{equation}\\label{eq:old}x=1\\end{equation}\n\\label{step:a}Done.\n\\end{proof}";
    const tagged = (proof: string): string => `Intro.\n${mark(false)}${printed}${mark(true)}\n${at("thm:a", "corrected proof; steps unplaced")}\\vsProof{${proof}}\nNext.`;
    const r = correctedTex(tagged("New."), OPTS);
    expect(r.tex).toBe("Intro.\n\n\\begin{proof}[Proof of Theorem~\\ref{thm:a}]\nNew.\n\\end{proof}\n\nNext.");
    expect(r.items.map((i) => [i.kind, i.line])).toEqual([["label-lost", 3], ["label-lost", 3], ["numbering", 3]]);
    expect(r.items.map((i) => i.detail)).toEqual([
      "the equation labelled `eq:old` was in the printed proof, which the corrected proof replaces, and is not in it",
      "the label `step:a` was in the printed proof, which the corrected proof replaces, and is not in it",
      "the printed proof had 1 numbered display(s), the corrected proof has 0: equation numbers after this point shift",
    ]);
    // the equation number a display of the corrected proof takes over keeps its label
    const kept = correctedTex(tagged("New. \\vsFit{x=2} \\label{step:a}Done."), OPTS);
    expect(kept.tex).toContain("\\begin{equation}\\label{eq:old}\nx=2\n\\end{equation}");
    expect(kept.items).toEqual([]);
    // an umbrella's note (after-proof: its printed proof did not align) likewise
    expect(correctedTex(tagged("New.").replace("steps unplaced", "after-proof"), OPTS).tex).toBe(r.tex);
    // a printed proof that holds a block of ours, or a corrected proof that does not typeset: both proofs stay, listed
    const inner = correctedTex(tagged("New.").replace("Old.", `Old.${at("thm:b", "clarification (reading)")}\\vsReading{$n\\geq 2$}`), OPTS);
    expect(inner.tex).toContain("Old.");
    expect(inner.tex).toContain("\\begin{proof}\nNew.\n\\end{proof}");
    expect(inner.items.map((i) => i.kind)).toContain("second-proof");
    // marks that are not acted on leave the text as it is without them
    const bare = (t: string): string => t.replace(/\\vsAt\{thm:a\}\{printed proof\}\\vsPrintedProof\{(?:begin|end)\}/gu, "");
    expect(inner.tex).toBe(correctedTex(bare(tagged("New.").replace("Old.", `Old.${at("thm:b", "clarification (reading)")}\\vsReading{$n\\geq 2$}`)), OPTS).tex);
    expect(correctedTex(tagged("\\texttt{bad}"), OPTS).items.map((i) => i.kind)).toEqual(["second-proof"]);
    // a corollary held after its result follows the corrected proof
    const cor = `${at("thm:cor-fix-1a2b3c4d", "error (repaired)")}\\vsCorollary{thm:cor-fix-1a2b3c4d}{}{Q holds. \\vsLine\\textit{Proof.} Immediate.}`;
    const held = correctedTex(`\\end{theorem}\n${cor}\n${tagged("New.").slice("Intro.\n".length)}`, { proofEnv: false });
    expect(held.tex).toBe("\\end{theorem}\n\n\\begin{proof}[Proof of Theorem~\\ref{thm:a}]\nNew.\n\\end{proof}\n\n\\noindent\\textit{Corollary.} Q holds.\n\n\\noindent\\textit{Proof.} Immediate.\n\nNext.");
  });

  it("a corollary a repair split off is a corollary of the paper after its result: the paper's environment, a label from its id, its proof after it", () => {
    const cor = `\\end{thm}\n${at("thm:cor-fix-1a2b3c4d", "error (repaired)")}\\vsCorollary{thm:cor-fix-1a2b3c4d}{the Gaussian case.}{If $X$ is Gaussian, \\vsFit{a=b.} \\vsLine\\textit{Proof.} By Theorem~\\ref{thm:a}.}\nNext.`;
    const r = correctedTex(cor, { proofEnv: true, corollaryEnv: { name: "cor", numbered: true } });
    expect(r.tex).toBe("\\end{thm}\n\n\\begin{cor}[the Gaussian case]\\label{thm:cor-fix-1a2b3c4d}\nIf $X$ is Gaussian, \n\\[\na=b.\n\\]\n\\end{cor}\n\n\\begin{proof}\nBy Theorem~\\ref{thm:a}.\n\\end{proof}\n\nNext.");
    expect(r.tex).not.toMatch(/\\vs[A-Z]|split/u);
    // a numbered environment moves the numbers after it: listed, at the corollary's line
    expect(r.items).toEqual([{ kind: "numbering", node: "thm:cor-fix-1a2b3c4d", line: 3, detail: expect.stringContaining("shift by one") }]);
    // an unnumbered environment has no number to refer to, and shifts nothing
    const star = correctedTex(cor, { proofEnv: true, corollaryEnv: { name: "cor", numbered: false } });
    expect(star.tex).toContain("\\begin{cor}[the Gaussian case]\nIf $X$ is Gaussian,");
    expect(star.items).toEqual([]);
  });

  it("a corollary follows what belongs to its result: the readings and the proof set after it, and the printed proof that comes next", () => {
    const cor = `${at("thm:cor-fix-1a2b3c4d", "error (repaired)")}\\vsCorollary{thm:cor-fix-1a2b3c4d}{}{Q holds. \\vsLine\\textit{Proof.} Immediate.}`;
    const ours = correctedTex(`\\end{theorem}\n${cor}\n\\vsReading{$n\\geq 2$}\n${at("thm:a", "corrected proof; no printed proof")}\\vsProof{Trivial.}\nNext.`, { proofEnv: false });
    expect(ours.tex).toBe("\\end{theorem}\n\n\\noindent\\textit{Remark.} $n\\geq 2$.\n\n\\noindent\\textit{Proof.} Trivial.\n\n\\noindent\\textit{Corollary.} Q holds.\n\n\\noindent\\textit{Proof.} Immediate.\n\nNext.");
    expect(ours.corollaries).toEqual([{ node: "thm:cor-fix-1a2b3c4d", from: 7, to: 9 }]);
    const printed = correctedTex(`\\end{theorem}\n${cor}\n\n\\begin{proof}\nBy ${at("thm:a", "printed")}\\vsStep{A.} ${at("thm:a", "error (repaired)")}\\vsCorrectedStep{B.}\n\\end{proof}\n\nNext.`, { proofEnv: false });
    expect(printed.tex).toBe("\\end{theorem}\n\n\\begin{proof}\nBy B.\n\\end{proof}\n\n\\noindent\\textit{Corollary.} Q holds.\n\n\\noindent\\textit{Proof.} Immediate.\n\n\nNext.");
    // text that is not its result's proof: the corollary comes first
    expect(correctedTex(`\\end{theorem}\n${cor}\nNext.`, { proofEnv: false }).tex).toBe("\\end{theorem}\n\n\\noindent\\textit{Corollary.} Q holds.\n\n\\noindent\\textit{Proof.} Immediate.\n\nNext.");
  });

  it("a corollary of a result proved elsewhere: the statement alone at the result, its proof after that result's proof, named by its number or its title", () => {
    const id = "thm:cor-fix-1a2b3c4d";
    const tag = at(id, "error (repaired)");
    const tagged = `\\end{theorem}\n${tag}\\vsCorollary{${id}}{the case $a[1]$.}{Q holds.}\nText.\n\\begin{proof}\nA.\n\\end{proof}\n${tag}\\vsCorollaryProof{${id}}{the case $a[1]$.}{By \\vsFit{a=b.}}\nMore.`;
    const r = correctedTex(tagged, { proofEnv: true, corollaryEnv: { name: "cor", numbered: true } });
    expect(r.tex).toBe(`\\end{theorem}\n\n\\begin{cor}[{the case $a[1]$}]\\label{${id}}\nQ holds.\n\\end{cor}\n\nText.\n\\begin{proof}\nA.\n\\end{proof}\n\n\\begin{proof}[Proof of Corollary~\\ref{${id}}]\nBy \n\\[\na=b.\n\\]\n\\end{proof}\n\nMore.`);
    expect(r.corollaries).toEqual([{ node: id, from: 3, to: 5 }]);
    expect(correctedTex(tagged, OPTS).tex).toContain("\\begin{proof}[Proof of {the corollary (the case $a[1]$)}]\nBy ");
    expect(correctedTex(tagged, { proofEnv: false }).tex).toContain("\\noindent\\textit{Proof of the corollary (the case $a[1]$).} By ");
    // a proof that does not typeset is not written, listed
    const bad = correctedTex(`${tag}\\vsCorollaryProof{${id}}{}{\\texttt{bad}}`, OPTS);
    expect(bad.tex.trim()).toBe("");
    expect(bad.items).toEqual([expect.objectContaining({ kind: "unplaced", node: id, detail: expect.stringContaining("its proof") })]);
  });

  it("a paper with no corollary environment gets the corollary and its proof as paragraphs; a proposed corollary is not written", () => {
    const body = "{thm:cor-fix-1a2b3c4d}{}{P holds. \\vsLine\\textit{Proof.} Immediate.}";
    const r = correctedTex(`\\end{theorem}\n${at("thm:cor-fix-1a2b3c4d", "error (repaired)")}\\vsCorollary${body}\nNext.`, { proofEnv: false });
    expect(r.tex).toBe("\\end{theorem}\n\n\\noindent\\textit{Corollary.} P holds.\n\n\\noindent\\textit{Proof.} Immediate.\n\nNext.");
    expect(r.items).toEqual([]);
    const pending = correctedTex(`\\end{theorem}\n${at("thm:cor-fix-1a2b3c4d", "awaiting decision")}\\vsProposedCorollary${body}\nNext.`, OPTS);
    expect(pending.tex).toBe("\\end{theorem}\n\nNext.");
    expect(pending.items).toEqual([]);
  });

  it("a corollary whose text does not typeset is not written, listed; one whose proof does not is written without it", () => {
    const tag = at("thm:cor-fix-1a2b3c4d", "error (repaired)");
    const none = correctedTex(`${tag}\\vsCorollary{thm:cor-fix-1a2b3c4d}{}{\\texttt{bad} \\vsLine\\textit{Proof.} Immediate.}`, OPTS);
    expect(none.tex.trim()).toBe("");
    expect(none.items).toEqual([expect.objectContaining({ kind: "unplaced", node: "thm:cor-fix-1a2b3c4d" })]);
    const half = correctedTex(`${tag}\\vsCorollary{thm:cor-fix-1a2b3c4d}{}{P holds. \\vsLine\\textit{Proof.} \\texttt{bad}}`, OPTS);
    expect(half.tex.trim()).toBe("\\noindent\\textit{Corollary.} P holds.");
    expect(half.items).toEqual([expect.objectContaining({ kind: "unplaced", detail: expect.stringContaining("its proof") })]);
  });

  it("writes the layout macros out and keeps a text nobody uses any more as printed, listed once", () => {
    expect(laid("A \\vsItem{(i)} one; \\vsItem{(ii)} two. \\vsPar B \\vsDisplay{y=1}")).toBe("A \n\n\\noindent (i) one; \n\n\\noindent (ii) two. \n\nB \n\\[\ny=1\n\\]\n");
    const r = correctedTex(`${at("def:d", "printed")}\\vsStruck{Let $d=1$.} ${at("def:d", "printed")}\\vsStruckRed{\\[ d=1 \\]} ${at("def:d", "no longer used")}\\vsNote{No result uses this.}`, OPTS);
    expect(r.tex.trim()).toBe("Let $d=1$. \\[ d=1 \\]");
    expect(r.items).toEqual([{ kind: "no-longer-used", node: "def:d", line: 1, detail: expect.any(String) }]);
  });

  it("leaves the paper's own \\vskip / \\vspace and a macro without its argument alone", () => {
    const tex = "a\\vskip 2pt b\\vspace{1em} c \\vsOriginal";
    expect(correctedTex(tex, OPTS).tex).toBe(tex);
  });

  it("writes reference commands the paper's packages do not define with the kernel's", () => {
    const r = correctedTex(`${at("t", "error (repaired)")}\\vsCorrected{By \\eqref{e}, \\cref{l} and \\citet{k}.}`, { proofEnv: true, plain: { eqref: true, cref: true, natbib: true } });
    expect(r.tex.trim()).toBe("By (\\ref{e}), \\ref{l} and \\cite{k}.");
  });

  it("carries a label of the replaced text the correction lacks; an equation's label and number are restored one for one", () => {
    const printed = "\\label{thm:x}We have\n\\begin{equation}\na=b,\\label{eq:ab}\n\\end{equation}\nalways.";
    const r = correctedTex(`${at("t", "printed")}\\vsOriginal{${printed}} ${at("t", "error (repaired)")}\\vsCorrected{We have \\vsFit{a\\leq b,} always.}`, OPTS);
    expect(r.tex).toContain("\\label{thm:x}We have");
    expect(r.tex).toContain("\\begin{equation}\\label{eq:ab}\na\\leq b,\n\\end{equation}");
    expect(r.items).toEqual([]);
  });

  it("a display of the correction keeps the label the replaced text carried, in place (blueTex's \\vsLabel), and no line is emptied", () => {
    const printed = "Then\n\\begin{equation}\n\\label{eq:clt}\nX\\Rightarrow N(0,\\sigma^2),\n\\end{equation}";
    const blue = blueTex("Then\n\\begin{equation}\n\\label{eq:clt}\n\\sqrt{n}X\\Rightarrow N(0,\\sigma^2),\n\\end{equation}");
    expect(blue).toBe("Then\n\\begin{equation}\n\\vsLabel{eq:clt}\n\\sqrt{n}X\\Rightarrow N(0,\\sigma^2),\n\\end{equation}");
    const r = correctedTex(`${at("t", "printed")}\\vsOriginal{${printed}} ${at("t", "error (repaired)")}\\vsCorrected{${blue}}`, OPTS);
    expect(r.tex.trim()).toBe("Then\n\\begin{equation}\n\\label{eq:clt}\n\\sqrt{n}X\\Rightarrow N(0,\\sigma^2),\n\\end{equation}");
    expect(r.items).toEqual([]);
  });

  it("lists an equation label and a change of numbering it cannot restore", () => {
    const printed = "\\begin{eqnarray}\na&=&b,\\label{eq:1}\\\\\nc&=&d.\\label{eq:2}\n\\end{eqnarray}";
    const r = correctedTex(`${at("t", "printed")}\\vsOriginal{${printed}} ${at("t", "error (repaired)")}\\vsCorrected{\\begin{eqnarray*}\na&=&d.\n\\end{eqnarray*}}`, OPTS);
    expect(r.items.map((i) => i.kind)).toEqual(["label-lost", "label-lost", "numbering"]);
    expect(r.tex).not.toContain("\\label");
  });
});

describe("restoreNumbers", () => {
  it("unstars a starred display and numbers only its last row", () => {
    expect(restoreNumbers("\\begin{align}\\label{e} x&=1 \\end{align}", "So \\begin{align*} x&\\leq 1 \\\\ &\\leq 2 \\end{align*} holds."))
      .toBe("So \\begin{align}\\label{e} x&\\leq 1 \\nonumber\\\\ &\\leq 2 \\end{align} holds.");
  });
  it("leaves the text alone when the displays do not match one for one", () => {
    const text = "\\[ a \\] and \\[ b \\]";
    expect(restoreNumbers("\\begin{equation}\\label{e} x \\end{equation}", text)).toBe(text);
    expect(restoreNumbers("no display", "\\[ a \\]")).toBe("\\[ a \\]");
  });
});

describe("the corrected paper's checks", () => {
  it("readGroup reads a group as TeX does: escaped braces and comments are no delimiters", () => {
    expect(readGroup("{a \\{ b % }\n c}d", 0)).toEqual({ body: "a \\{ b % }\n c", end: 15 });
    expect(readGroup("x", 0)).toBeNull();
  });
  it("refsIn lists every reference with its line, comment lines left out", () => {
    expect(refsIn("See \\ref{a} and \\eqref{b}.\n% \\ref{c}\n\\cref{d,e} 50\\% \\autoref{f}")).toEqual([
      { label: "a", line: 1, command: "ref" },
      { label: "b", line: 1, command: "eqref" },
      { label: "d", line: 3, command: "cref" },
      { label: "e", line: 3, command: "cref" },
      { label: "f", line: 3, command: "autoref" },
    ]);
  });
  it("labelsOf tells an equation's label from a result's", () => {
    expect(labelsOf("\\label{t} x \\begin{align} y \\label{e} \\end{align} \\[ z \\label{d} \\]")).toEqual({ equation: ["e", "d"], other: ["t"] });
  });
  it("auxLabels reads label → number", () => {
    expect(auxLabels("\\newlabel{thm:a}{{2}{7}{Main}{theorem.2}{}}\n\\newlabel{eq:x}{{A.1}{9}}\n")).toEqual(new Map([["thm:a", "2"], ["eq:x", "A.1"]]));
  });
  it("envSpanOfLabel gives a result's own lines", () => {
    const tex = "Intro \\ref{t}.\n\\begin{theorem}\\label{t}\nP \\begin{equation} x \\end{equation}\n\\end{theorem}\n\n\\begin{proof}\nBy \\ref{t}.\n\\end{proof}\nLater \\ref{t}.\n\\begin{proof}[Proof of Lemma~\\ref{l}]\nq\n\\end{proof}";
    expect(envSpanOfLabel(tex, "t")).toEqual({ from: 2, to: 4 });
    expect(envSpanOfLabel(tex, "missing")).toBeNull();
  });
});
