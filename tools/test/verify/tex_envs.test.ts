// The V1 mechanical parser must recover a paper's theorem-like environments EXACTLY,
// in the user's own file coordinates, with no silent losses.
//
// Everything asserted here is a failure mode that would otherwise be invisible
// downstream: a `\input` that does not resolve (the core would silently miss a whole
// section), a `%` comment that swallows a formula's `\%`, a `\begin{comment}` block whose
// theorem gets formalized as if it were real, a proof parked in an appendix that never
// gets attached to its theorem, and `lines` that point at the FLATTENED text instead of
// the file the user will open. The fixture under `fixtures/paper/` is a miniature
// arXiv-style multi-file source carrying one instance of each.

import { describe, it, expect } from "vitest";
import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import {
  parseTheoremCounters,
  buildEnvsJson,
  extractEnvs,
  flattenTex,
  kindFromTitle,
  parseNewtheorems,
  blankInactiveToggles,
  readToggles,
  stripIffalse,
  stripTexCommentsJoining,
  writeEnvsArtifacts,
} from "../../src/verify/tex_envs.js";
import type { EnvsJson, TexEnv } from "../../src/verify/types.js";
import { VERIFY_FILES } from "../../src/verify/types.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const PAPER = path.join(here, "fixtures", "paper");

async function paper(): Promise<EnvsJson> {
  return (await buildEnvsJson(PAPER, "main.tex")).envs;
}

function byId(envs: TexEnv[], id: string): TexEnv {
  const hit = envs.find((e) => e.id === id);
  if (!hit) throw new Error(`no env ${id} in ${envs.map((e) => e.id).join(", ")}`);
  return hit;
}

/** A throwaway source tree: `{ "sec/a.tex": "…" }` written under a fresh temp dir. */
async function tree(files: Record<string, string>): Promise<string> {
  const dir = await mkdtemp(path.join(os.tmpdir(), "verify-tex-"));
  for (const [rel, text] of Object.entries(files)) {
    const abs = path.join(dir, rel);
    await mkdir(path.dirname(abs), { recursive: true });
    await writeFile(abs, text);
  }
  return dir;
}

/** Line map for a single-file document handed straight to `extractEnvs`. */
function lineMapFor(tex: string): Array<{ file: string; line: number }> {
  return tex.split("\n").map((_l, i) => ({ file: "main.tex", line: i + 1 }));
}

describe("flattenTex", () => {
  it("inlines \\input and \\include in inclusion order and keeps a 1:1 line map", async () => {
    const flat = await flattenTex(PAPER, "main.tex");
    expect(flat.files).toEqual(["main.tex", "sec/intro.tex", "sec/results.tex", "appendix.tex"]);
    expect(flat.text.split("\n").length).toBe(flat.lineMap.length);
    const lines = flat.text.split("\n");
    const at = lines.findIndex((l) => l.includes("\\begin{thm}[Consistency]"));
    expect(flat.lineMap[at]).toEqual({ file: "sec/results.tex", line: 3 });
  });

  it("strips comments without touching an escaped \\% and without shifting line numbers", async () => {
    const flat = await flattenTex(PAPER, "main.tex");
    expect(flat.text).toContain("At most \\(5\\%\\) of units are missing.");
    expect(flat.text).not.toContain("the escaped percent above is data");
    expect(flat.text).not.toContain("Preamble. This whole line is a comment");
    // The commented-out line is blank, not deleted: the map stays aligned.
    const lines = flat.text.split("\n");
    const idx = flat.lineMap.findIndex((m) => m.file === "main.tex" && m.line === 2);
    expect(lines[idx]!.trim()).toBe("");
  });

  it("records the .bib files \\bibliography names, reads the brace-less \\input form, and folds in the .bbl", async () => {
    const flat = await flattenTex(PAPER, "main.tex");
    expect(flat.bibFiles).toEqual(["refs.bib"]);

    const dir = await mkdtemp(path.join(os.tmpdir(), "verify-bbl-"));
    await writeFile(
      path.join(dir, "ms.tex"),
      [
        "\\documentclass{article}",
        "\\begin{document}",
        "\\input results",
        "\\bibliography{refs}",
        "\\end{document}",
        "",
      ].join("\n"),
    );
    await writeFile(
      path.join(dir, "results.tex"),
      "\\begin{theorem}\\label{thm:b}\nBrace-less include.\n\\end{theorem}\n",
    );
    await writeFile(
      path.join(dir, "ms.bbl"),
      "\\begin{thebibliography}{1}\n\\bibitem{x2020} X, Y. (2020). A title.\n\\end{thebibliography}\n",
    );
    const { envs } = await buildEnvsJson(dir, "ms.tex");
    expect(envs.files).toEqual(["ms.tex", "results.tex", "ms.bbl"]);
    expect(envs.envs.map((e) => e.id)).toEqual(["thm:b"]);
    expect(envs.bibliography).toEqual([{ key: "x2020", text: "X, Y. (2020). A title." }]);
  });

  it.each<[string, () => unknown]>([
    [
      "a missing \\input is skipped with a warning naming the including file and line",
      async () => {
        const flat = await flattenTex(path.join(here, "fixtures", "broken_input"), "main.tex");
        expect(flat.warnings).toEqual([expect.stringMatching(/main\.tex:3: \\input\{sec\/missing\} not found.*skipped/)]);
      },
    ],
    [
      "a file reached twice is folded in ONCE, and the run says so",
      async () => {
        const dir = await tree({
          "main.tex": [
            "\\documentclass{article}",
            "\\begin{document}",
            "\\input{shared}",
            "\\input{sec/a}",
            "\\end{document}",
            "",
          ].join("\n"),
          "sec/a.tex": "Section A.\n\\input{shared}\n",
          "shared.tex": "\\begin{theorem}\\label{thm:shared}\nShared.\n\\end{theorem}\n",
        });
        const { envs, warnings } = await buildEnvsJson(dir, "main.tex");
        // LaTeX would typeset the theorem twice; a verify run wants exactly one of it.
        expect(envs.envs.map((e) => e.id)).toEqual(["thm:shared"]);
        expect(warnings).toEqual([
          expect.stringMatching(/sec\/a\.tex:2: shared\.tex is included more than once/),
        ]);
      },
    ],
    [
      "a nesting depth cap stops an \\input chain instead of recursing without end",
      async () => {
        const files: Record<string, string> = {
          "main.tex": "\\documentclass{article}\n\\begin{document}\n\\input{g0}\n\\end{document}\n",
          "g39.tex": "Bottom.\n",
        };
        for (let k = 0; k < 39; k += 1) files[`g${k}.tex`] = `\\input{g${k + 1}}\n`;
        const dir = await tree(files);
        await expect(buildEnvsJson(dir, "main.tex")).rejects.toThrow(/\\input nested deeper than 32/);
      },
    ],
  ])("%s", async (_name, run) => {
    await run();
  });
});

describe("parseNewtheorems", () => {
  it("reads every \\newtheorem shape, thmtools declarations, the built-in aliases, and a wrapper's inner kind", async () => {
    const text = await readFile(path.join(PAPER, "main.tex"), "utf8");
    const map = parseNewtheorems(text);
    expect(map.thm).toBe("theorem"); // \newtheorem{thm}{Theorem}[section]
    expect(map.lem).toBe("lemma"); // \newtheorem{lem}[thm]{Lemma}
    expect(map.cor).toBe("corollary"); // \newtheorem*{cor}{Corollary}
    expect(map.defn).toBe("definition");
    expect(map.assump).toBe("assumption"); // \declaretheorem[name=Assumption]{assump}
    expect(map.rmk).toBe("remark");
    // defaults survive for a paper that declares nothing
    expect(parseNewtheorems("").proposition).toBe("proposition");
    expect(parseNewtheorems("").hyp).toBe("assumption");

    const wrapped = parseNewtheorems(
      "\\newtheorem{theorem}{Theorem}\n" +
        "\\NewDocumentEnvironment{theoremv}{m o s}{\\begin{theorem}\\label{obj:#1}}{\\end{theorem}}\n",
    );
    expect(wrapped.theoremv).toBe("theorem");
  });

  // A Claim / Result / Fact / Observation is something the paper ASSERTS, so it has to
  // reach the core as a result; a Conjecture is exactly the thing the paper does not
  // claim to prove, so it stays context.
  it("classifies by the printed title, not the environment name", () => {
    expect(kindFromTitle("Hypothesis")).toBe("assumption");
    expect(kindFromTitle("Setting")).toBe("other");
    expect(parseNewtheorems("\\newtheorem{claim}{Proposition}").claim).toBe("proposition");
    expect(kindFromTitle("Claim")).toBe("proposition");
    expect(kindFromTitle("Result")).toBe("proposition");
    expect(kindFromTitle("Cited result")).toBe("proposition");
    expect(kindFromTitle("Fact")).toBe("proposition");
    expect(kindFromTitle("Observation")).toBe("proposition");
    expect(kindFromTitle("Conjecture")).toBe("other");
    expect(kindFromTitle("Conjectured result")).toBe("other");
    // whole words only: "Factorization" is no more a Fact than "Resultant" is a Result
    expect(kindFromTitle("Factorization")).toBe("other");
    expect(kindFromTitle("Resultant")).toBe("other");
    expect(parseNewtheorems("\\newtheorem{clm}{Claim}").clm).toBe("proposition");
    expect(parseNewtheorems("\\newtheorem{conj}{Conjecture}").conj).toBe("other");
    expect(kindFromTitle("Specification")).toBe("assumption");
    expect(kindFromTitle("Requirement")).toBe("assumption");
    expect(kindFromTitle("Postulate")).toBe("assumption");
  });
});

describe("stripCommentary", () => {
  it("joins a glued % without a paragraph break inside a formula, and maps each line to its source line", async () => {
    const dir = await tree({
      "main.tex": [
        "\\documentclass{article}",
        "\\begin{document}",
        "\\end{eqnarray*}%",
        "where $V=\\mathbb{E}\\left[ \\eta \\left( W;\\gamma",
        "^{\\ast}\\right) \\right] $.",
        "\\begin{theorem}\\label{thm:after}",
        "A claim.",
        "\\end{theorem}",
        "\\end{document}",
        "",
      ].join("\n"),
    });
    const flat = await flattenTex(dir, "main.tex");
    expect(flat.text).toContain("\\end{eqnarray*}where $V=\\mathbb{E}\\left[ \\eta \\left( W;\\gamma\n^{\\ast}");
    expect(flat.text).not.toMatch(/\\gamma\n\n/);
    const { envs } = await buildEnvsJson(dir, "main.tex");
    expect(byId(envs.envs, "thm:after").lines.from).toBe(6);
  });
  it("blanks a verbatim block, so nothing it merely DISPLAYS is read as markup, and refuses an unterminated one", async () => {
    const dir = await tree({
      "main.tex": [
        "\\documentclass{article}",
        "\\begin{document}",
        "\\begin{verbatim}",
        "\\newtheorem{shown}{Theorem}",
        "\\begin{theorem}\\label{thm:fake}",
        "A theorem printed as an example.",
        "\\end{theorem}",
        "\\input{does-not-exist}",
        "\\end{document}",
        "\\end{verbatim}",
        "Inline \\verb|\\begin{theorem}\\label{thm:verb}| too.",
        "\\begin{theorem}\\label{thm:real}",
        "The real one, after the listing.",
        "\\end{theorem}",
        "\\end{document}",
        "",
      ].join("\n"),
    });
    const { envs } = await buildEnvsJson(dir, "main.tex");
    expect(envs.envs.map((e) => e.id)).toEqual(["thm:real"]);
    expect(envs.newtheorem.shown).toBeUndefined(); // the displayed \newtheorem declares nothing
    // the line count survives the blanking, so locators still point at the source
    expect(byId(envs.envs, "thm:real").lines.from).toBe(12);
    const broken = await tree({
      "main.tex": "\\documentclass{article}\n\\begin{document}\n\\begin{verbatim}\nx\n\\end{document}\n",
    });
    await expect(buildEnvsJson(broken, "main.tex")).rejects.toThrow(
      /unterminated \\begin\{verbatim\}/,
    );
  });
  it("a % inside \\verb or \\lstinline is literal text, not a comment that glues the next line on", () => {
    const origins: number[] = [];
    expect(stripTexCommentsJoining("a\\verb|%|b\nc", origins)).toBe("a\\verb|%|b\nc");
    expect(origins).toEqual([1, 2]);
    expect(stripTexCommentsJoining("x \\lstinline{50%} y % gone\nz")).toBe("x \\lstinline{50%} y \nz");
    expect(stripTexCommentsJoining("\\verb*+%+%\nnext")).toBe("\\verb*+%+next");
    // an unclosed \verb on its line is no span: the % after it is a comment as before
    expect(stripTexCommentsJoining("\\verb|open %c\nd")).toBe("\\verb|open \nd");
  });
  it("a line ending in a backslash (a control space) still ends there: every later line keeps its origin", () => {
    // santanna_zhao_drdid_r2: `…\textquotedblright\` then `\cite%`-joined lines; each such line
    // shifted every later origin by one, and results were looked for below their \begin
    const origins: number[] = [];
    const src = ["a \\textquotedblright\\", "see \\cite%", "{F}, and \\cite%", "{T}. As so,", "next"].join("\n");
    expect(stripTexCommentsJoining(src, origins)).toBe("a \\textquotedblright\\\nsee \\cite{F}, and \\cite{T}. As so,\nnext");
    expect(origins).toEqual([1, 2, 5]);
    // `\\` (a line break) and `\%` keep their meaning; a plain file maps 1:1
    const plain: number[] = [];
    expect(stripTexCommentsJoining("x \\\\\ny \\% z % c\nw", plain)).toBe("x \\\\\ny \\% z \nw");
    expect(plain).toEqual([1, 2, 3]);
  });
});

describe("extractEnvs", () => {
  // The exact list also proves the \begin{comment} / \iffalse fakes (thm:fake, lem:fake)
  // in the fixture are never extracted.
  it("returns every theorem-like env in document order with ids, kinds and titles", async () => {
    const envs = await paper();
    expect(envs.envs.map((e) => [e.id, e.kind, e.envName])).toEqual([
      ["def:po", "definition", "defn"],
      ["ass:unconf", "assumption", "assump"],
      ["thm:main", "theorem", "thm"],
      ["lemma-1", "lemma", "lem"], // unlabeled: `<kind>-<ordinal>`
      ["cor:rate", "corollary", "cor"],
    ]);
    expect(byId(envs.envs, "def:po").title).toBe("Potential outcome");
    expect(byId(envs.envs, "thm:main").title).toBe("Consistency");
    expect(byId(envs.envs, "lemma-1").title).toBeNull();
    expect(byId(envs.envs, "lemma-1").label).toBeNull();
  });

  it("keeps the body verbatim (comments already stripped) and drops the [title] argument", async () => {
    const envs = await paper();
    const def = byId(envs.envs, "def:po");
    expect(def.body).not.toContain("Potential outcome");
    expect(def.body).toContain("At most \\(5\\%\\) of units are missing.");
    expect(def.body).not.toContain("%!"); // no stray comment text
    expect(def.body.endsWith("missing.")).toBe(true); // trimmed
  });

  it.each<[string, () => unknown]>([
    [
      "an adjacent proof, and an appendix \\begin{proof}[Proof of \\ref{..}]; an orphan proof is reported",
      async () => {
        const envs = await paper();
        const thm = byId(envs.envs, "thm:main");
        expect(thm.proof).toBe("Combine \\cref{def:po,ass:unconf} and apply dominated convergence.");
        expect(thm.proofLines).toEqual({ file: "appendix.tex", from: 3, to: 5, env: "proof", label: null });
        const cor = byId(envs.envs, "cor:rate");
        expect(cor.proof).toBe("Immediate from \\cref{thm:main}.");
        expect(cor.proofLines!.file).toBe("sec/results.tex");
        // a proof matched to nobody (\cref{lem:orphan}) is ignored, not attached at random
        expect(envs.envs.filter((e) => e.proof !== null).map((e) => e.id)).toEqual(["thm:main", "cor:rate"]);
        // …and it is REPORTED: a proof the parser drops is never dropped in silence
        const built = await buildEnvsJson(PAPER, "main.tex");
        expect(built.warnings).toEqual([
          expect.stringMatching(
            /appendix\.tex:7: \\begin\{proof\} is attached to no result \(its title references lem:orphan/,
          ),
        ]);
      },
    ],
    [
      "a proof given as the last section of an appendix environment ends where that environment closes",
      async () => {
        const tex = [
          "\\begin{document}",
          "\\begin{theorem}\\label{thm:a}\nA.\n\\end{theorem}",
          "\\begin{APPENDICES}",
          "\\subsection{Proof of Theorem \\ref{thm:a}}",
          "First the display \\begin{equation} x = y \\end{equation} and then the claim follows.",
          "\\end{APPENDICES}",
          "\\end{document}",
        ].join("\n");
        const { envs } = extractEnvs(tex, lineMapFor(tex), parseNewtheorems(tex));
        const proof = byId(envs, "thm:a").proof ?? "";
        expect(proof).toContain("\\end{equation} and then the claim follows.");
        expect(proof).not.toContain("APPENDICES");
      },
    ],
    [
      "a titled proof to the result its title names, never to the env it follows",
      async () => {
        const tex = [
          "\\begin{document}",
          "\\begin{theorem}\\label{thm:a}\nA.\n\\end{theorem}",
          "\\begin{lemma}[Berry Esseen \\cite{shevtsova}]\\label{lem:cited}\nCited.\n\\end{lemma}",
          "\\begin{proof}[of Theorem~\\ref{thm:a}]\nProof of A.\n\\end{proof}",
          "\\begin{lemma}\\label{lem:b}\nB.\n\\end{lemma}",
          "\\begin{proof}\nProof of B.\n\\end{proof}",
          "\\end{document}",
        ].join("\n");
        const { envs, warnings } = extractEnvs(tex, lineMapFor(tex), parseNewtheorems(tex));
        expect(byId(envs, "thm:a").proof).toBe("Proof of A.");
        expect(byId(envs, "lem:cited").proof).toBeNull();
        expect(byId(envs, "lem:b").proof).toBe("Proof of B.");
        expect(warnings).toEqual([]);
      },
    ],
    [
      "an untitled proof under a `Proof of \\ref{X}` heading to X, superseding a deferral stub",
      async () => {
        const tex = [
          "\\begin{document}",
          "\\begin{proposition}\\label{prop:main}\nMain.\n\\end{proposition}",
          "\\begin{proof}\nSee Appendix \\ref{sec:app}.\n\\end{proof}",
          "\\begin{lemma}\\label{lem:inline}\nInline.\n\\end{lemma}",
          "\\begin{proof}\nInline proof.\n\\end{proof}",
          "\\appendix",
          "\\section{Proof of Proposition \\ref{prop:main}\\label{sec:app}}",
          "\\begin{proof}\nThe real argument: $x = y$.\n\\end{proof}",
          "\\begin{lemma}\\label{lem:helper}\nHelper.\n\\end{lemma}",
          "\\begin{proof}\nHelper proof.\n\\end{proof}",
          "\\end{document}",
        ].join("\n");
        const { envs, warnings } = extractEnvs(tex, lineMapFor(tex), parseNewtheorems(tex));
        expect(byId(envs, "prop:main").proof).toBe("The real argument: $x = y$.");
        expect(byId(envs, "lem:inline").proof).toBe("Inline proof.");
        expect(byId(envs, "lem:helper").proof).toBe("Helper proof.");
        expect(warnings).toEqual([expect.stringMatching(/main\.tex:5: the \\begin\{proof\} after prop:main only defers .* proof at 16 supersedes/)]);
      },
    ],
    [
      "an untitled proof directly after the appendix restatement of X to X, superseding the deferral stub after the original",
      async () => {
        const tex = [
          "\\begin{document}",
          "\\begin{theorem}\\label{thm:main}\nMain.\n\\end{theorem}",
          "\\begin{proof}\nSee Appendix \\ref{sec:app}.\n\\end{proof}",
          "\\appendix",
          "\\section{Omitted proofs\\label{sec:app}}",
          "\\begin{theorem}\\label{thm:main}\nMain.\n\\end{theorem}",
          "\\begin{proof}\nThe real argument: $x = y$.\n\\end{proof}",
          "\\end{document}",
        ].join("\n");
        const { envs, warnings } = extractEnvs(tex, lineMapFor(tex), parseNewtheorems(tex));
        expect(envs.map((e) => e.id)).toEqual(["thm:main"]);
        expect(byId(envs, "thm:main").proof).toBe("The real argument: $x = y$.");
        expect(warnings).toEqual([
          expect.stringMatching(/restates thm:main .* word for word/),
          expect.stringMatching(/main\.tex:5: the \\begin\{proof\} after thm:main only defers .* proof at 13 supersedes/),
        ]);
      },
    ],
  ])("binds %s", async (_name, run) => {
    await run();
  });

  it("a prose proof with no QED mark ends at the bibliography, never inside it", () => {
    const tex = [
      "\\begin{document}",
      "\\begin{theorem}\\label{thm:a}\nA.\n\\end{theorem}",
      "\\section*{Appendix}",
      "\\noindent \\textbf{Proof of Theorem \\ref{thm:a}.} Take $a = 1$.",
      "",
      "\\begin{thebibliography}{9}",
      "\\bibitem{x} Author (2000). \\enquote{A title}.",
      "\\end{thebibliography}",
      "\\end{document}",
    ].join("\n");
    const { envs } = extractEnvs(tex, lineMapFor(tex), parseNewtheorems(tex));
    expect(byId(envs, "thm:a").proof).toBe("Take $a = 1$.");
  });

  it.each<[string, () => unknown]>([
    [
      "proofs written in running text: bold opener + QED, and a heading opener",
      async () => {
        const tex = [
          "\\begin{document}",
          "\\begin{lemma}\\label{lem:a}\nA.\n\\end{lemma}",
          "\\begin{theorem}\\label{thm:b}\nB.\n\\end{theorem}",
          "\\begin{lemma}\\label{lem:c}\nC.\n\\end{lemma}",
          "\\begin{proof}\nSee the Supplementary Material.\n\\end{proof}",
          "\\section{Proofs}",
          "\\noindent{\\bf Proof of Lemma \\ref{lem:a}:} By definition, $a = 1$. $\\square$",
          "Some interlude text.",
          "\\textbf{Proof of Theorem \\ref{thm:b}}: Take $b$.",
          "\\begin{lemma}\\label{lem:inner}\nInner.\n\\end{lemma}",
          "\\begin{proof}\nInner proof.\n\\end{proof}",
          "Hence $b = 2$. \\hfill$\\square$",
          "\\subsection*{Proof of Lemma \\ref{lem:c}}",
          "Heading-opened proof, $c = 3$.",
          "\\section{Next}",
          "Not part of any proof.",
          "\\end{document}",
        ].join("\n");
        const { envs, warnings } = extractEnvs(tex, lineMapFor(tex), parseNewtheorems(tex));
        expect(byId(envs, "lem:a").proof).toBe("By definition, $a = 1$.");
        expect(byId(envs, "thm:b").proof).toContain("Take $b$.");
        expect(byId(envs, "thm:b").proof).toContain("Inner proof.");
        expect(byId(envs, "thm:b").proof).toContain("Hence $b = 2$.");
        expect(byId(envs, "thm:b").proof).not.toContain("square");
        expect(envs.find((e) => e.id === "lem:inner")).toBeUndefined();
        expect(byId(envs, "lem:c").proof).toBe("Heading-opened proof, $c = 3$.");
        expect(warnings).toEqual([expect.stringMatching(/main\.tex:11: the \\begin\{proof\} after lem:c only defers/)]);
      },
    ],
    [
      "proofs announced by printed number (title, heading) and by the text before an untitled proof",
      async () => {
        const tex = [
          "\\newtheorem{theorem}{Theorem}[section]",
          "\\newtheorem{lemma}[theorem]{Lemma}",
          "\\newtheorem{prop}{Proposition}",
          "\\begin{document}",
          "\\section{One}",
          "\\begin{theorem}\\label{thm:a}\nA.\n\\end{theorem}",
          "\\begin{lemma}\nB (unlabeled, prints as Lemma 1.2).\n\\end{lemma}",
          "\\begin{prop}\\label{prop:c}\nC (Proposition 1).\n\\end{prop}",
          "Before proving Proposition \\ref{prop:c} we remark on it at length.",
          "\\begin{proof}\nAnnounced proof of C.\n\\end{proof}",
          "\\section{Two}",
          "\\begin{theorem}\\label{thm:d}\nD (Theorem 2.1).\n\\end{theorem}",
          "\\appendix",
          "\\section{Proofs}",
          "\\begin{proof}[Proof of Theorem 1.1]\nProof of A.\n\\end{proof}",
          "\\subsection{Proof of Lemma 1.2}",
          "\\begin{proof}\nProof of B.\n\\end{proof}",
          "\\textbf{Proof of Theorem 2.1.} Prose proof of D. $\\square$",
          "\\end{document}",
        ].join("\n");
        const { envs, warnings } = extractEnvs(tex, lineMapFor(tex), parseNewtheorems(tex));
        expect(byId(envs, "thm:a").proof).toBe("Proof of A.");
        expect(byId(envs, "lemma-1").proof).toBe("Proof of B.");
        expect(byId(envs, "prop:c").proof).toBe("Announced proof of C.");
        expect(byId(envs, "thm:d").proof).toBe("Prose proof of D.");
        expect(warnings).toEqual([]);
        const c = parseTheoremCounters(tex);
        expect(c.counterOf).toEqual({ theorem: "theorem", lemma: "theorem", prop: "prop" });
        expect(c.resetBy).toEqual({ theorem: "section", prop: null });
        expect(c.display.lemma).toBe("Lemma");
      },
    ],
    [
      "no proof when two proof-less results are stacked above it; it warns instead of guessing",
      async () => {
        const tex = [
          "\\begin{document}",
          "\\begin{theorem}\\label{thm:t}\nT.\n\\end{theorem}",
          "\\begin{corollary}\\label{cor:c}\nC.\n\\end{corollary}",
          "Some words.",
          "\\begin{proof}\nWhich one?\n\\end{proof}",
          "\\end{document}",
        ].join("\n");
        const { envs, warnings } = extractEnvs(tex, lineMapFor(tex), parseNewtheorems(tex));
        expect(byId(envs, "thm:t").proof).toBeNull();
        expect(byId(envs, "cor:c").proof).toBeNull();
        expect(warnings).toEqual([expect.stringMatching(/follows two proof-less results \(thm:t, cor:c\); not bound/)]);
      },
    ],
  ])("binds %s", async (_name, run) => {
    await run();
  });

  it("locates every env in the ORIGINAL file, not the flattened text", async () => {
    const envs = await paper();
    expect(byId(envs.envs, "def:po").lines).toEqual({
      file: "sec/intro.tex",
      from: 2,
      to: 5,
      env: "defn",
      label: "def:po",
    });
    expect(byId(envs.envs, "ass:unconf").lines.from).toBe(7);
    expect(byId(envs.envs, "thm:main").lines).toEqual({
      file: "sec/results.tex",
      from: 3,
      to: 5,
      env: "thm",
      label: "thm:main",
    });
    expect(byId(envs.envs, "cor:rate").lines.from).toBe(13);
  });

  it("collects refs from the body and the proof, splitting \\cref{a,b} and deduplicating", async () => {
    const envs = await paper();
    expect(byId(envs.envs, "thm:main").refs).toEqual(["def:po", "ass:unconf"]);
    expect(byId(envs.envs, "cor:rate").refs).toEqual(["thm:main"]);
    expect(byId(envs.envs, "def:po").refs).toEqual([]);
  });

  it("refuses same-name nesting rather than truncating the body at the inner \\end", async () => {
    await expect(buildEnvsJson(path.join(here, "fixtures", "nested_env"), "main.tex")).rejects.toThrow(
      /same-name nesting is not supported/,
    );
  });

  it("closes the body at the \\end{document} that FOLLOWS \\begin{document}, and refuses an empty or inverted window", () => {
    // A preamble macro whose body carries `\end{document}` used to collapse the scan
    // window to nothing, and the parser then returned zero envs without a word.
    const tex = [
      "\\documentclass{article}",
      "\\newcommand{\\finish}{\\end{document}}",
      "\\begin{document}",
      "\\begin{theorem}\\label{thm:real}",
      "Real.",
      "\\end{theorem}",
      "\\end{document}",
    ].join("\n");
    const { envs } = extractEnvs(tex, lineMapFor(tex), parseNewtheorems(tex));
    expect(envs.map((e) => e.id)).toEqual(["thm:real"]);

    const empty = "\\documentclass{article}\n\\begin{document}\\end{document}\n";
    expect(() => extractEnvs(empty, lineMapFor(empty), parseNewtheorems(empty))).toThrow(
      /empty document body/,
    );
    const inverted = "\\end{document}\n\\begin{theorem}\\label{t}\nX.\n\\end{theorem}\n\\begin{document}";
    expect(() => extractEnvs(inverted, lineMapFor(inverted), parseNewtheorems(inverted))).toThrow(
      /empty document body/,
    );
  });

  it("gives every env a UNIQUE id even when the paper repeats a \\label", () => {
    // `theorem-3-3` is exactly the id the old third-tier fallback would have minted for
    // the last theorem — it was never re-tested against the ids already handed out.
    const tex = [
      "\\begin{document}",
      "\\begin{theorem}\\label{theorem-3-3}\nA.\n\\end{theorem}",
      "\\begin{theorem}\\label{theorem-3}\nB.\n\\end{theorem}",
      "\\begin{theorem}\\label{theorem-3}\nC.\n\\end{theorem}",
      "\\end{document}",
    ].join("\n");
    const { envs, warnings } = extractEnvs(tex, lineMapFor(tex), parseNewtheorems(tex));
    const ids = envs.map((e) => e.id);
    expect(new Set(ids).size).toBe(ids.length);
    expect(ids).toEqual(["theorem-3-3", "theorem-3", "theorem-3-1"]);
    expect(warnings).toEqual([expect.stringMatching(/duplicate id "theorem-3"/)]);
  });
});

describe("parseBibliography", () => {
  it("unions \\bibitem bodies with .bib entries, \\bibitem winning on a shared key", async () => {
    const envs = await paper();
    const keys = envs.bibliography.map((b) => b.key).sort();
    expect(keys).toEqual(["knight2006", "lehmann2005", "vdv1998"]);
    const byKey = new Map(envs.bibliography.map((b) => [b.key, b.text]));
    expect(byKey.get("vdv1998")).toContain("Cambridge."); // the \bibitem body, not the .bib row
    expect(byKey.get("lehmann2005")).toBe(
      "Lehmann, E. L. and Romano, J. P. (2005). Testing Statistical Hypotheses",
    );
  });
});

describe("writeEnvsArtifacts", () => {
  it("writes envs.json, flat.tex and the line map under the run dir", async () => {
    const runDir = await mkdtemp(path.join(os.tmpdir(), "verify-envs-"));
    const { envs, flat } = await buildEnvsJson(PAPER, "main.tex");
    await writeEnvsArtifacts(runDir, envs, flat);
    const written = JSON.parse(
      await readFile(path.join(runDir, VERIFY_FILES.envsJson), "utf8"),
    ) as EnvsJson;
    expect(written.main_file).toBe("main.tex");
    expect(written.envs).toHaveLength(5);
    const flatText = await readFile(path.join(runDir, VERIFY_FILES.flatTex), "utf8");
    expect(flatText).toBe(flat.text);
    const map = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.flatLineMap), "utf8")) as {
      lineMap: Array<{ file: string; line: number }>;
    };
    expect(map.lineMap).toHaveLength(flatText.split("\n").length);
  });
});

describe("extractEnvs: authors' styles", () => {
  const parse = (tex: string) => extractEnvs(tex, lineMapFor(tex), parseNewtheorems(tex));

  it.each<[string, () => unknown]>([
    [
      "reads results stated in running text (\\textsc{Theorem 1:} …) and binds their prose proofs by printed number",
      async () => {
        const tex = [
          "\\newtheorem{theorem}{Theorem}[section]",
          "\\begin{document}",
          "\\section{Results}",
          "\\textsc{Theorem 1:}\\textit{ If i) $a = 1$ then }$b = 2$\\textit{.}",
          "",
          "The proof is in the appendix. \\textbf{Theorem 1} is sharp.",
          "",
          "\\textsc{Assumption 1: }$E[\\|X\\|^2] < \\infty$.",
          "",
          "\\textsc{Lemma A1:} \\textit{If Assumption 1 holds then $c = 3$.}",
          "",
          "\\section{Appendix A: Proofs}",
          "\\textbf{Proof of Theorem 1:} By i), $b = 2$. $Q.E.D.$",
          "",
          "\\textbf{Proof of Lemma A1:} Immediate.",
          "\\end{document}",
        ].join("\n");
        const { envs, warnings } = parse(tex);
        expect(envs.map((e) => [e.id, e.kind, e.title])).toEqual([
          ["theorem-1", "theorem", "Theorem 1"],
          ["assumption-1", "assumption", "Assumption 1"],
          ["lemma-1", "lemma", "Lemma A1"],
        ]);
        expect(byId(envs, "theorem-1").body).toBe("\\textit{ If i) $a = 1$ then }$b = 2$\\textit{.}");
        expect(byId(envs, "theorem-1").proof).toBe("By i), $b = 2$.");
        expect(byId(envs, "lemma-1").proof).toBe("Immediate.");
        expect(byId(envs, "assumption-1").body).toBe("$E[\\|X\\|^2] < \\infty$.");
        expect(warnings.filter((w) => /stated in running text/.test(w))).toHaveLength(3);
      },
    ],
    [
      "does not end a prose result at a paragraph break inside an open \\textit{…}, math span or display",
      async () => {
        const tex = [
          "\\begin{document}",
          "\\textsc{Theorem 22:} \\textit{If i) $a$ holds; either iv) Assumption B1 is",
          "",
          "satisfied and }$\\sqrt{n}\\longrightarrow",
          "0$\\textit{ then}\\[",
          "",
          "b = 2.",
          "\\]",
          "",
          "This result depends on the rate.",
          "\\end{document}",
        ].join("\n");
        const { envs } = parse(tex);
        expect(envs).toHaveLength(1);
        expect(envs[0]!.body.endsWith("b = 2.\n\\]")).toBe(true);
        expect(envs[0]!.body).not.toContain("This result depends");
        // …nor inside an open display environment
        const tex2 = "\\begin{document}\n\\textsc{Assumption 1: }$E[\\psi^2]<\\infty$\\textit{ and }\\begin{align*}\n\nE[\\psi] &= 0.\n\\end{align*}\n\nProse after.\n\\end{document}";
        const r2 = parse(tex2);
        expect(r2.envs).toHaveLength(1);
        expect(r2.envs[0]!.body.endsWith("\\end{align*}")).toBe(true);
        // …nor at a paragraph break after a comma, where the sentence continues with "then"
        const tex3 = "\\begin{document}\n\\textsc{Lemma 16:} \\textit{If Assumption 1 is satisfied for each }$(\\ell=1,...,L),$\n\n\\textit{then }$\\hat{\\Psi}\\overset{p}{\\longrightarrow}\\Psi.$\n\nThe proof is in Appendix A.\n\\end{document}";
        const r3 = parse(tex3);
        expect(r3.envs).toHaveLength(1);
        expect(r3.envs[0]!.body.endsWith("\\longrightarrow}\\Psi.$")).toBe(true);
        expect(r3.envs[0]!.body).not.toContain("The proof is");
        // …and an italic statement continues through an italic "Furthermore" after a display
        const tex4 = "\\begin{document}\n\\textsc{Theorem 3:} \\textit{If i) holds then }\\begin{equation}\n\n\\bar\\psi=0.\n\\end{equation}\n\n\\textit{Furthermore, if ii) holds then }$\\|\\bar\\psi\\|\\le C\\|\\gamma\\|^2.$\n\nThis result shows orthogonality.\n\\end{document}";
        const r4 = parse(tex4);
        expect(r4.envs).toHaveLength(1);
        expect(r4.envs[0]!.body.endsWith("\\|^2.$")).toBe(true);
        expect(r4.envs[0]!.body).not.toContain("This result shows");
      },
    ],
    [
      "does not read a bold cross-reference as a result when the paper writes that kind as an environment",
      async () => {
        const tex = [
          "\\begin{document}",
          "\\begin{theorem}\\label{thm:a}\nA.\n\\end{theorem}",
          "",
          "\\textbf{Theorem 1} is the main result.",
          "\\end{document}",
        ].join("\n");
        const { envs } = parse(tex);
        expect(envs.map((e) => e.id)).toEqual(["thm:a"]);
      },
    ],
  ])("%s", async (_name, run) => {
    await run();
  });
});

describe("flattenTex: subfiles", () => {
  it("folds a \\subfile child in, blanking its own preamble and \\end{document} so the line map stays 1:1", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "verify-subfile-"));
    await mkdir(path.join(dir, "versions"));
    await writeFile(path.join(dir, "main.tex"), "\\documentclass{article}\n\\usepackage{subfiles}\n\\begin{document}\n\\subfile{versions/body.tex}\n\\end{document}\n");
    await writeFile(
      path.join(dir, "versions", "body.tex"),
      "\\documentclass[../main.tex]{subfiles}\n\\graphicspath{{../img/}}\n\\begin{document}\n\\begin{theorem}\\label{thm:s}\nS.\n\\end{theorem}\n\\end{document}\n",
    );
    const flat = await flattenTex(dir, "main.tex");
    expect(flat.files).toEqual(["main.tex", "versions/body.tex"]);
    expect(flat.text.match(/\\begin\s*\{document\}/g)).toHaveLength(1);
    expect(flat.text.match(/\\end\s*\{document\}/g)).toHaveLength(1);
    const lines = flat.text.split("\n");
    const at = lines.findIndex((l) => l.includes("\\begin{theorem}"));
    expect(flat.lineMap[at]).toEqual({ file: "versions/body.tex", line: 4 });
    const { envs } = extractEnvs(flat.text, flat.lineMap, parseNewtheorems(flat.text));
    expect(envs.map((e) => e.id)).toEqual(["thm:s"]);
  });
});
describe("algorithms", () => {
  const flat = String.raw`\documentclass{article}
\newtheorem{theorem}{Theorem}
\begin{document}
\begin{algorithm}[H]
\caption{Gradient descent}\label{alg:gd}
\begin{algorithmic}[1]
\Require $x_0$, $\eta>0$
\For{$k = 0, 1, \dots$} \State $x_{k+1} \gets x_k - \eta \nabla f(x_k)$ \EndFor
\end{algorithmic}
\end{algorithm}
\begin{algorithmic}
\State $y \gets 0$
\end{algorithmic}
\begin{theorem}\label{thm:rate} The iterates of Algorithm~\ref{alg:gd} converge.\end{theorem}
\end{document}`;
  const lineMap = flat.split("\n").map((_, i) => ({ file: "m.tex", line: i + 1 }));
  it("extracts an algorithm a result refers to as one environment named by its caption; unreferenced pseudocode stays context", () => {
    const { envs } = extractEnvs(flat, lineMap as never, parseNewtheorems(flat));
    expect(envs.map((e) => [e.envName, e.kind, e.label, e.title])).toEqual([
      ["algorithm", "other", "alg:gd", "Gradient descent"],
      ["theorem", "theorem", "thm:rate", null],
    ]);
    expect(envs[0]!.body).toContain("\\begin{algorithmic}");
  });
  const parse = (src: string) => extractEnvs(src, src.split("\n").map((_, i) => ({ file: "m.tex", line: i + 1 })) as never, parseNewtheorems(src)).envs;
  it("extracts an algorithm the paper's text refers to; one nothing refers to stays context", () => {
    const envs = parse(String.raw`\newtheorem{theorem}{Theorem}\begin{document}
We run Algorithm~\ref{alg:gd} on the sample.
\begin{algorithm}[t]\caption{GD}\label{alg:gd}\begin{algorithmic}\State $x$\end{algorithmic}\end{algorithm}
\begin{algorithm}[t]\caption{Baseline}\label{alg:base}\begin{algorithmic}\State $y$ (see Algorithm~\ref{alg:base})\end{algorithmic}\end{algorithm}
\begin{theorem}\label{thm:a} The output is close to the optimum.\end{theorem}
\end{document}`);
    expect(envs.map((e) => e.id)).toEqual(["alg:gd", "thm:a"]);
  });
  it("hands a theorem its proof across an algorithm float set between them", () => {
    const envs = parse(String.raw`\newtheorem{theorem}{Theorem}\begin{document}
\begin{theorem}\label{thm:a} Algorithm~\ref{alg:gd} converges.\end{theorem}
\begin{algorithm}[t]\caption{GD}\label{alg:gd}\begin{algorithmic}\State $x$\end{algorithmic}\end{algorithm}
\begin{proof} By telescoping. \end{proof}
\end{document}`);
    expect(envs.find((e) => e.label === "thm:a")!.proof).toContain("telescoping");
    expect(envs.find((e) => e.label === "alg:gd")!.proof).toBeNull();
  });
  it("labels an algorithm2e float at its caption, not at a line label, and moves no other environment's id", () => {
    const envs = parse(String.raw`\newtheorem{theorem}{Theorem}\newtheorem{conjecture}{Conjecture}\begin{document}
\begin{algorithm}\KwIn{$x$} $y \leftarrow 0$\;\label{ln:init} \caption{Sum}\label{alg:sum}\end{algorithm}
\begin{conjecture} Sums are fast. \end{conjecture}
\begin{theorem}\label{thm:s} Algorithm~\ref{alg:sum} returns the sum.\end{theorem}
\end{document}`);
    expect(envs.map((e) => e.id)).toEqual(["alg:sum", "other-1", "thm:s"]);
  });
  it("keeps a paper's own theorem-like algorithm and its title", () => {
    const src = String.raw`\newtheorem{algorithm}{Algorithm}\begin{document}\begin{algorithm}[Debiased estimation]\label{alg:t} Estimate it.\end{algorithm}\end{document}`;
    const { envs } = extractEnvs(src, [{ file: "m.tex", line: 1 }] as never, parseNewtheorems(src));
    expect(envs.map((e) => [e.envName, e.kind, e.title])).toEqual([["algorithm", "other", "Debiased estimation"]]);
  });
});

// A construct the parser does not read is left as written, with ONE warning naming it and what
// the orchestrator can do in the run's source copy — and nothing is said when it is absent.
describe("the parser names what it does not read", () => {
  const warningsOf = (tex: string): string[] => extractEnvs(tex, lineMapFor(tex), parseNewtheorems(tex)).warnings;

  it("thmtools restatable: once per paper, with the count, the first places and the restatements", () => {
    const tex = [
      "\\usepackage{thmtools}",
      "\\begin{document}",
      "\\begin{restatable}[Main]{theorem}{thmmain}\\label{thm:main}",
      "Main.",
      "\\end{restatable}",
      "\\begin{restatable*}{lemma}{lemkey}",
      "Key.",
      "\\end{restatable*}",
      "\\appendix",
      "\\thmmain*",
      "\\begin{proof}\nArgument.\n\\end{proof}",
      "\\end{document}",
    ].join("\n");
    const warnings = warningsOf(tex).filter((w) => /restatable/.test(w));
    expect(warnings).toEqual([
      expect.stringMatching(/^2 result\(s\) are written in thmtools `restatable` \(main\.tex:3 \{theorem\}\{thmmain\}, main\.tex:6 \{lemma\}\{lemkey\}\) and restated 1 time\(s\) by \\<macro>\*: the parser does not read it/),
    ]);
    expect(warnings[0]).toMatch(/run's source copy/);
    expect(warningsOf("\\begin{document}\n\\begin{theorem}\\label{thm:a}\nA.\n\\end{theorem}\n\\end{document}")).toEqual([]);
  });

  it("a statement repeated word for word without its \\label: a separate result, said so; a same-label restatement is merged as before", () => {
    const unlabelled = [
      "\\begin{document}",
      "\\begin{theorem}\\label{thm:main}\nFor every $x$, $x = x$.\n\\end{theorem}",
      "\\appendix",
      "\\begin{theorem}\nFor every   $x$,\n$x = x$.\n\\end{theorem}",
      "\\begin{proof}\nTrivial.\n\\end{proof}",
      "\\end{document}",
    ].join("\n");
    const { envs, warnings } = extractEnvs(unlabelled, lineMapFor(unlabelled), parseNewtheorems(unlabelled));
    expect(envs.map((e) => e.id)).toEqual(["thm:main", "theorem-2"]);
    expect(warnings).toEqual([
      "main.tex:6: \\begin{theorem} states the same as thm:main (main.tex:2) but without its \\label: it is read as a separate result; " +
        "if it is a restatement, give it \\label{thm:main} in the run's source copy",
    ]);
    const relabelled = unlabelled.replace("\\begin{theorem}\nFor every   $x$", "\\begin{theorem}\\label{thm:copy}\nFor every   $x$");
    expect(warningsOf(relabelled)).toEqual([expect.stringMatching(/^main\.tex:6: .* but under \\label\{thm:copy\}, not its \\label:/)]);
    const neither = unlabelled.replace("\\label{thm:main}", "");
    expect(warningsOf(neither)).toEqual([expect.stringMatching(/^main\.tex:6: .* the \\begin\{theorem\} at main\.tex:2, which carries no \\label: .* give both the same \\label/)]);
    const sameLabel = unlabelled.replace("\\begin{theorem}\nFor every   $x$", "\\begin{theorem}\\label{thm:main}\nFor every   $x$");
    expect(warningsOf(sameLabel)).toEqual([expect.stringMatching(/restates thm:main .* word for word; not a separate result$/)]);
  });

  it("a macro package the source ships, when the results use it: the file, its definitions, and to inline it", async () => {
    const main = [
      "\\documentclass{article}",
      "\\usepackage{amsmath}",
      "\\usepackage[final]{macros,neurips}",
      "\\begin{document}",
      "\\begin{theorem}\\label{thm:a}\n$\\R \\subseteq \\R$, $\\hat{x} = \\tilde{x}$ and $\\KL(p, p) = 0$ \\citep{a}.\n\\end{theorem}",
      "\\begin{claim}\nC.\n\\end{claim}",
      "\\end{document}",
    ].join("\n");
    const dir = await tree({
      "main.tex": main,
      "macros.sty": "\\newcommand{\\R}{\\mathbb{R}}\n\\DeclareMathOperator{\\KL}{KL}\n\\def\\eps{\\varepsilon} % \\def\\gone{x}\n\\newtheorem{claim}{Claim}\n",
      // a style no result touches is not worth a word, nor one that only redefines a command or defines a citation
      "neurips.sty": "\\newcommand{\\And}{and}\n\\def\\@maketitle{}\n\\let\\hat\\widehat\n\\renewcommand{\\tilde}{\\widetilde}\n\\DeclareRobustCommand\\citep{}\n",
    });
    const { warnings } = await buildEnvsJson(dir, "main.tex");
    expect(warnings).toEqual([
      "main.tex:3: \\usepackage{macros} loads macros.sty, which the paper's source ships; the flattener does not read a package, so the agents " +
        "and the page do not see its definitions — it defines 3 command(s), 2 of them used in the extracted results (\\R, \\KL), and it declares " +
        "the theorem environment(s) claim the document opens, whose results are not extracted; inline macros.sty into the main file's preamble " +
        "in place of the \\usepackage (between \\makeatletter and \\makeatother) in the run's source copy",
    ]);
    // no local amsmath.sty: amsmath is the installed package, not the paper's
    const plain = await tree({ "main.tex": main.replace("\\usepackage[final]{macros,neurips}\n", "") });
    expect((await buildEnvsJson(plain, "main.tex")).warnings).toEqual([]);
  });
});

describe("stripIffalse", () => {
  it("does not count \\iff or \\ifthenelse as conditionals: a disabled proof using them ends at its own \\fi", () => {
    const text = "a\n\\iffalse\n$p\\iff q$ \\ifthenelse{x}{y}{z}\n\\fi\nb \\ref{l}";
    const out = stripIffalse(text, "main.tex");
    expect(out.split("\n")).toEqual(["a", "", "", "", "b \\ref{l}"]);
  });
});

describe("etoolbox toggles", () => {
  it("reads the toggles a paper sets, the last setting winning", () => {
    expect(readToggles("\\newtoggle{abs}\\newtoggle{long}\\toggletrue{long}\\settoggle{abs}{false}")).toEqual({ abs: false, long: true });
  });
  it("blanks the branch the toggle does not select, keeping lines; \\nottoggle the other way round", () => {
    const t = "a\n\\iftoggle{abs}\n{see \\ref{x}}\n{see \\ref{y}}\nb";
    const off = blankInactiveToggles(t, { abs: false });
    expect(off).toContain("\\ref{y}");
    expect(off).not.toContain("\\ref{x}");
    expect(off.split("\n")).toHaveLength(t.split("\n").length);
    expect(blankInactiveToggles(t, { abs: true })).not.toContain("\\ref{y}");
    expect(blankInactiveToggles("\\nottoggle{abs}{P}{Q}", { abs: false })).toContain("P");
    expect(blankInactiveToggles("\\nottoggle{abs}{P}{Q}", { abs: false })).not.toContain("Q");
 
    // a toggle the text never sets (a package, a macro parameter) blanks neither branch
    expect(blankInactiveToggles("\\iftoggle{#1}{P}{Q}", {})).toBe("\\iftoggle{#1}{P}{Q}");
    // escaped braces inside a branch do not close it
    expect(blankInactiveToggles("\\iftoggle{a}{x\\}y}{z}", { a: false })).toContain("z");
    expect(blankInactiveToggles("\\iftoggle{a}{x\\}y}{z}", { a: false })).not.toContain("y");
  });
});
