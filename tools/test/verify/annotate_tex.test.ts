import { existsSync } from "node:fs";
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { colorDriverOptions, envCuts, injectPreamble, verbatimLike } from "../../src/verify/annotate_tex.js";
import { compileTex, planAnnotations, type AnnotationInput } from "../../src/verify/annotated_paper.js";
import { findExecutable } from "../../src/shared/program.js";

/**
 * Model-written note text is TeX checked at its source (design 2026-09-25): nothing in the renderer
 * maps Unicode, balances braces, reconciles `\left`/`\right`, rewrites `^(` / `√(`, or escapes a part.
 * These live notes (cns_simple_dml `discovery/owner_explanations.json`), which the removed sanitizer
 * used to repair, are now FLAGGED: a non-ASCII character by `nonAsciiProblem`, a fragment that does not
 * compile by the compile check (`tex_fragment_check.test.ts`); the renderer prints either verbatim and
 * reports it at the render checkpoint.
 */
const LOCAL_CLAUSE_WHAT =
  "(a) Step: |\\omega - f_V(v)| =  \\left|    h \\int   K(u) \\partial_v f_V(v- u \\tilde h) u \\mathsf{d} u \\right |  \\leq   h \\bar f' \\int |u|| K(u)| du. It uses: the derivative bound on $f_V$ in Lemma~\\ref{lemma:local} which the paper assumes only on: $N_{h_0}(v)$. But the step applies it at: $v-u\\tilde h$ over the full support of $K$. (b) Step: The standard argument to control the bias of the higher order kernels employs the Taylor expansion of order $\\mathsf{v}$ in $h$ around $h=0$; see e.g. \\cite[Lemma B2]{newey1994kernel}. It uses: the differentiability and derivative bounds in Lemma~\\ref{lemma:approx} which the paper assumes only on: $N_{h_0}(v)$. But the step applies it at: $v-hu$ wherever $K(u)$ is nonzero.";
const LEM_LOCAL = {
  claim: "The local oracle standard deviation and representer norm are of order h⁻¹ᐟ², with the stated bounds for κ_h and ζ_h.",
  what_is_wrong:
    "(a) Step: “\\leq  h^{-(q - 1)/q}  \\bar f^{1/q}  \\left(\\tiny{\\int} |K|^q\\right)^{1/q}.” It uses: f_V(v−hu)≤f̄ which the paper assumes only on: v−hu∈N_{h₀}(v). But the step applies it at: every u in the kernel integral. (b) Step: “\\leq   h \\bar f' \\int |u|| K(u)| du.” It uses: |∂f_V(v−u h̃)|≤f̄′ which the paper assumes only on: v−u h̃∈N_{h₀}(v). But the step applies it at: every u contributing to the normalizer.",
  why: "For the stated pulse kernel and density singularity outside N_{h₀}(0), ω_{h_n} grows at least as u_n¹ᐟ² and h_nσ²_{h_n}→0, contradicting σ_h≍h⁻¹ᐟ².",
  fix: "Require a uniform upper bound on |ω_h| and on ∫|K(u)|^q f_V(v−hu)du for q=2,3,4, together with a positive uniform lower bound on |ω_h|; these conditions yield the displayed h orders.",
};
const APPROX_CLAIM = "The lemma asserts both |θ₀ʰ−θ₀ˡⁱᵐ| ≤ Chᵛ and Δₕ ≲ √n hᵛ⁺¹ᐟ².";
const RESID2_WHAT_B =
  "(b) Step: “&\\leq \\bar{\\sigma}^2 \\mathcal{R}(\\hat{\\alpha}_{\\ell}).” It uses: a bound on the conditional second moment of Y−γ₀(W), which the paper assumes only on: the square of its conditional mean. But the step applies it at: E[{Y−γ₀(W)}²∣W].";
const RR_WHY = "For uniform W on (0,1), a(t)=t⁻¹ᐟ⁸, m(w,γ)=∫₀¹a(t)γ(t)dt, γ₀=0.";

const GAUSS_WHY = "For a Gaussian kernel K(u)=e^(−u²/2)/√(2π), K(2h_0/h)>0 at v−hu=v−2h_0.";

const hasPdflatex = findExecutable("pdflatex", { nativeOnly: true }) !== null;
const hasBibtex = findExecutable("bibtex", { nativeOnly: true }) !== null;

describe("annotate_tex — a flagged fragment is printed verbatim, one defect naming it", () => {
  const FLAT = ["\\documentclass{article}\\usepackage{amsthm}", "\\newtheorem{theorem}{Theorem}", "\\begin{document}", "\\begin{theorem}\\label{thm:a}", "The constant is positive.", "\\end{theorem}", "\\end{document}"].join("\n");
  const core = (): Core =>
    ({
      qid: "ts",
      symbols: [],
      assumptions: [],
      definitions: [],
      statements: [{ id: "thm:a", kind: "theorem", statement: "The constant is positive.", depends_on: [], status: "to-prove", tex_locator: { file: "main.tex", from: 4, to: 6, env: "theorem", label: "thm:a" } }],
      target_estimand: "t",
      bibliography: [],
    }) as unknown as Core;
  const input = (why: string, texVerdicts: Map<string, string> | null = null): AnnotationInput =>
    ({
      files: { "main.tex": FLAT },
      envs: {
        main_file: "main.tex",
        files: ["main.tex"],
        newtheorem: {},
        envs: [{ id: "thm:a", kind: "theorem", envName: "theorem", label: "thm:a", title: null, body: "The constant is positive.", proof: null, proofLines: null, section: null, lines: { file: "main.tex", from: 4, to: 6 }, refs: [] }],
        bibliography: [],
      },
      flatText: FLAT,
      lineMap: FLAT.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 })),
      refs: null,
      transcribed: core(),
      core: core(),
      patches: {
        patches: [
          {
            node: "thm:a",
            corrected_statement: "The constant is nonnegative.",
            add_assumptions: [],
            remove_depends_on: [],
            proof_note: null,
            // The field under test is `fix`: the prose sets it as written (the other fields generate sentences).
            owner_explanation: { claim: "The theorem asserts the constant is positive.", defects: [{ kind: "other", step_unit: "thm:a/1/1", uses: null, assumed_on: null, applied_at: null, detail: "the bound fails" }], why: { objects: ["$n = 1$"], consequence: "the bound fails" }, fix: why, gives_up: "strict positivity" },
          },
        ],
        unfixable: [],
      },
      paperErrors: {},
      findings: [],
      review: null,
      texVerdicts,
    }) as unknown as AnnotationInput;
  const noteOf = (plan: ReturnType<typeof planAnnotations>): string => plan.edits["main.tex"]!.map((e) => e.text).join("");

  it("a Unicode Why: printed verbatim, the defect names the characters and the fragment; nothing is logged as repaired", () => {
    const plan = planAnnotations(input(GAUSS_WHY));
    expect(plan.defects).toEqual([{ node: "thm:a", block: "explanation", reason: expect.stringMatching(/^a non-ASCII character U\+2212 \(−\), U\+00B2 \(²\), U\+221A \(√\), U\+03C0 \(π\) — the text is plain ASCII; every symbol is a TeX command; printed verbatim — the fragment: For a Gaussian kernel/u), fragment: expect.objectContaining({ kind: "note", producer: "fixer", text: GAUSS_WHY }) }]);
    expect(noteOf(plan)).toContain(verbatimLike(GAUSS_WHY));
    expect(noteOf(plan)).not.toContain("\\sqrt{2\\pi}");
    expect(plan.log.some((l) => /repaired/u.test(l))).toBe(false);
  });

  it("an ASCII TeX Why is set byte for byte, and listed among the fragments the compile check takes", () => {
    const why = "For the Gaussian kernel $K(u)=e^{-u^2/2}/\\sqrt{2\\pi}$, $K(2h_0/h)>0$.";
    const plan = planAnnotations(input(why));
    expect(plan.defects).toEqual([]);
    expect(noteOf(plan)).toContain(why);
    expect(plan.fragments).toContainEqual({ kind: "note", text: why });
  });

  it("a fragment the compile check failed (texVerdicts): printed verbatim, the compiler's line in the defect", () => {
    const why = "It fails when e_n tends to zero.";
    const verdicts = new Map([[`note\u0000${why}`, "Missing $ inserted. (at: \\vsNote{It fails when e_)"]]);
    const plan = planAnnotations(input(why, verdicts));
    // A model-text defect: the fixer's note goes back to the fixer, with the compiler's line.
    expect(plan.defects).toEqual([{ node: "thm:a", block: "explanation", reason: `Missing $ inserted. (at: \\vsNote{It fails when e_); printed verbatim — the fragment: ${why}`, fragment: expect.objectContaining({ kind: "note", text: why, producer: "fixer", error: "Missing $ inserted. (at: \\vsNote{It fails when e_)" }) }]);
    expect(noteOf(plan)).toContain(verbatimLike(why));
  });

  it.skipIf(!hasPdflatex)("a block right before the paper's own line break compiles: the block ends the line", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "vs-cr-"));
    try {
      const body = [
        "$(i)$ first \\vsOriginal{old} \\vsCorrected{new}", "\\\\", "$(ii)$ second \\vsNote{note}\\\\[2pt] third \\vsNote{n}\\\\* fourth \\\\ fifth",
      ].join("\n");
      const doc = injectPreamble(["\\documentclass{article}", "\\begin{document}", body, "\\end{document}", ""].join("\n"), false).tex;
      await writeFile(path.join(dir, "main.tex"), doc, "utf8");
      const r = await compileTex({ dir, mainFile: "main.tex", timeoutMs: 120_000 });
      const log = await readFile(path.join(dir, "main.log"), "latin1");
      expect(log.split("\n").filter((l) => /^!|^\.\/[^:]+:\d+: /.test(l))).toEqual([]);
      expect(r.status).toBe("passed");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  }, 120_000);

  it("colorDriverOptions: the drivers a preamble passes to color, nothing else; injected once", () => {
    expect(colorDriverOptions("\\usepackage[dvips]{graphicx,epsfig,color}")).toEqual(["dvips"]);
    expect(colorDriverOptions("\\usepackage[dvipsnames]{color}\n\\usepackage[dvips]{xcolor}\n% \\usepackage[dvips]{color}")).toEqual([]);
    expect(colorDriverOptions("\\usepackage[ final , pdftex ]{ color }\n\\RequirePackage[pdftex]{graphicx,color}")).toEqual(["pdftex"]);
    const once = injectPreamble("\\documentclass{article}\n\\usepackage[dvips]{color}\n\\begin{document}\nx\n\\end{document}\n", false).tex;
    expect(injectPreamble(once, false).tex).toBe(once);
    expect(once.match(/PassOptionsToPackage/g)).toHaveLength(1);
    // with no \begin{document}, the macro block still follows our xcolor line
    const bare = injectPreamble("\\documentclass{article}\n\\usepackage[dvips]{color}\nx\n", false).tex;
    expect(bare.indexOf("\\usepackage{xcolor}")).toBeLessThan(bare.indexOf("\\newcommand"));
  });

  it.skipIf(!hasPdflatex)("a dvips paper loading color with a driver option: our xcolor hands the driver on, no option clash (live Eisenbrand–Shmonin, 2026-10-14)", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "vs-drv-"));
    try {
      const doc = injectPreamble(["\\documentclass{article}", "\\usepackage[dvips]{graphicx,color}", "\\begin{document}", "Text \\vsNote{note}.", "\\end{document}", ""].join("\n"), false).tex;
      expect(doc).toMatch(/\\PassOptionsToPackage\{dvips\}\{color\}% added by LeanSmith\n\\usepackage\{xcolor\}/);
      await writeFile(path.join(dir, "main.tex"), doc, "utf8");
      await compileTex({ dir, mainFile: "main.tex", timeoutMs: 120_000 });
      expect(await readFile(path.join(dir, "main.log"), "latin1")).not.toMatch(/Option clash/);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  }, 120_000);

  it.skipIf(!hasPdflatex || !hasBibtex)("a paper that ships a .bib and no .bbl gets its bibliography built; a shipped .bbl is used as it is", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "vs-bib-"));
    try {
      const doc = ["\\documentclass{article}", "\\begin{document}", "As shown in \\cite{knuth}.", "\\bibliographystyle{plain}", "\\bibliography{refs}", "\\end{document}", ""].join("\n");
      await writeFile(path.join(dir, "main.tex"), doc, "utf8");
      await writeFile(path.join(dir, "refs.bib"), "@book{knuth, author={Donald Knuth}, title={The TeXbook}, year={1984}, publisher={Addison-Wesley}}\n", "utf8");
      const r = await compileTex({ dir, mainFile: "main.tex", timeoutMs: 120_000 });
      expect(r).toMatchObject({ status: "passed", reason: "" });
      expect(await readFile(path.join(dir, "main.bbl"), "utf8")).toContain("TeXbook");
      expect(await readFile(path.join(dir, "main.log"), "latin1")).not.toMatch(/Citation .* undefined/);
      // a shipped .bbl is the paper's: bibtex is not run over it
      await rm(path.join(dir, "refs.bib"));
      await writeFile(path.join(dir, "main.bbl"), "\\begin{thebibliography}{1}\\bibitem{knuth} Shipped entry.\\end{thebibliography}\n", "utf8");
      expect(await compileTex({ dir, mainFile: "main.tex", timeoutMs: 120_000 })).toMatchObject({ status: "passed", reason: "" });
      expect(await readFile(path.join(dir, "main.bbl"), "utf8")).toContain("Shipped entry");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  }, 120_000);

  it.skipIf(!hasPdflatex)("an error of the first pass only (natbib reading a shipped .bbl before the .aux exists) is no failure; one every pass has is", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "vs-first-pass-"));
    try {
      const doc = (body: string) => ["\\documentclass{article}", "\\usepackage{natbib}", "\\begin{document}", body, "\\bibliographystyle{abbrv}", "\\bibliography{refs}", "\\end{document}", ""].join("\n");
      await writeFile(path.join(dir, "main.tex"), doc("As shown in \\cite{knuth}."), "utf8");
      await writeFile(path.join(dir, "main.bbl"), "\\begin{thebibliography}{1}\\bibitem{knuth} D. Knuth. The TeXbook.\\end{thebibliography}\n", "utf8");
      const first = await compileTex({ dir, mainFile: "main.tex", timeoutMs: 120_000 });
      expect(first.status).toBe("passed");
      // an error that stays in the last pass is the compile's
      await writeFile(path.join(dir, "main.tex"), doc("Broken \\undefinedcommandhere."), "utf8");
      expect((await compileTex({ dir, mainFile: "main.tex", timeoutMs: 120_000 })).status).toBe("failed");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  }, 120_000);

  it.skipIf(!hasPdflatex)("verbatim printouts compile in every block, also in restricted horizontal mode", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "vs-verbatim-"));
    try {
      const note = [LOCAL_CLAUSE_WHAT, ...Object.values(LEM_LOCAL), APPROX_CLAIM, RESID2_WHAT_B, RR_WHY, GAUSS_WHY, "a % b # c & d ~ e ^ f _ g \\ h { i"].map((t) => `\\vsLine \\vsSub ${verbatimLike(t)}`).join(" ");
      const doc = injectPreamble(["\\documentclass{article}", "\\begin{document}", "Text.", `\\vsNote{${note}}`, `\\mbox{\\vsNote{${note}}}`, "\\end{document}", ""].join("\n"), false).tex;
      await writeFile(path.join(dir, "main.tex"), doc, "utf8");
      const r = await compileTex({ dir, mainFile: "main.tex", timeoutMs: 120_000 });
      const log = await readFile(path.join(dir, "main.log"), "latin1");
      expect(log.split("\n").filter((l) => /^!|^\.\/[^:]+:\d+: /.test(l))).toEqual([]);
      expect(r.status).toBe("passed");
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  }, 120_000);
});

describe("envCuts: a text cut at its top-level environment markers", () => {
  it("cuts where asked, outside groups, math and environments not cut; a \\begin takes its optional argument", () => {
    const tex = String.raw`a \end{lemma} b \begin{proof}[Of it] c {\begin{x}} \begin{enumerate}\item \begin{proof}\end{proof}\end{enumerate} $\begin{y}$ d`;
    const c = envCuts(tex, (env, matched) => !matched || env === "proof");
    expect(c.markers.map((m) => tex.slice(m.start, m.end))).toEqual([String.raw`\end{lemma}`, String.raw`\begin{proof}[Of it]`]);
    expect(c.markers.map((m) => m.key)).toEqual(["end{lemma}", "begin{proof}"]);
    expect(c.segments.map((x) => tex.slice(x.start, x.end))).toEqual(["a ", " b ", tex.slice(tex.indexOf(" c "))]);
    // an optional argument is read as a group (brackets in math, braces); a cut environment's `{…}`
    // arguments go with it; the spacing before `[` never crosses a blank line
    const args = String.raw`\begin{proof}[Of $[0,1]$ and {a]}] It. \begin{minipage}[t]{3cm}{x} y \begin{proof}` + "\n\n" + "[z] w";
    const a = envCuts(args, () => true);
    expect(a.markers.map((m) => args.slice(m.start, m.end))).toEqual([String.raw`\begin{proof}[Of $[0,1]$ and {a]}]`, String.raw`\begin{minipage}[t]{3cm}{x}`, String.raw`\begin{proof}`]);
    expect(a.segments.map((x) => args.slice(x.start, x.end))).toEqual(["", " It. ", " y ", "\n\n[z] w"]);
    // a matched environment not cut is no marker; nothing cut: one segment
    expect(envCuts(String.raw`a \begin{x}b\end{x} c`, (_e, matched) => !matched)).toEqual({ markers: [], segments: [{ start: 0, end: 21 }] });
  });
});
