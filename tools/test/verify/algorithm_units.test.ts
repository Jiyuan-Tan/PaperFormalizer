/**
 * An algorithm is repaired like any other definition: its float is cut step by step (`units.ts`
 * `algorithmUnits`), one step is replaced in place (`ops.ts`), the build keeps the results wired and
 * re-opens them (`core_graph.ts`), the annotated paper marks the step inside the float and the corrected
 * paper carries it there (`annotated_paper.ts`, `corrected_tex.ts`), and the page draws the marks
 * (`ui/algorithms.ts`). The fixture is a paper whose algorithm no result refers to by label: `envs.json`
 * leaves it out and the definition is transcribed from the running text.
 */
import { execFileSync } from "node:child_process";
import { existsSync, readFileSync } from "node:fs";
import { findExecutable } from "../../src/shared/program.js";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { renderPaper } from "../../src/ui/tex_html.js";
import { applyEdits, planAnnotations, type AnnotationInput } from "../../src/verify/annotated_paper.js";
import { injectPreamble } from "../../src/verify/annotate_tex.js";
import { basisInputs, basisOf } from "../../src/verify/core_graph.js";
import { correctedTex } from "../../src/verify/corrected_tex.js";
import { PatchOpSchema, materializeRepair, nodePassage, unitsBlock, type PassageSources, type PatchOp } from "../../src/verify/ops.js";
import { PatchFileSchema, applyPatchFile, normalizeTextlessEntries, rederiveOn } from "../../src/verify/patches.js";
import { repairTextViolations } from "../../src/verify/stage_v1.js";
import { RefCoreSchema, materializeRefCore } from "../../src/verify/ref_core.js";
import { patchFileTexFields } from "../../src/verify/tex_fragment_check.js";
import { buildEnvsJson } from "../../src/verify/tex_envs.js";
import { PaperUnits, UNITS_VERSION, algorithmUnits, flatLineStart, loadUnits, regionUnits } from "../../src/verify/units.js";
import { VERIFY_FILES, type EnvsJson } from "../../src/verify/types.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

/** The algorithm of the paper that surfaced the gap, as printed (a float with an `algorithmic` body). */
const FLOAT_BODY = String.raw`
  \caption{Algorithm for NETE Estimation}\label{alg:nete}
  \begin{algorithmic}[1]
    \REQUIRE Dataset $\mathcal{D}=\{(X_i,D_i,Y_i,U_i)\}_{i=1}^n$, threshold $t$, exponent estimation $ \hat{\alpha}_{n} $, estimator
    \STATE Randomly split $\mathcal{D}$ into two equal parts $\mathcal{D}_1$ and $\mathcal{D}_2$
    \STATE Using $\mathcal{D}_1$, estimate:
    \begin{enumerate}[label=\alph*.]
      \item Propensity function $\hat p(x)$ via regression of $D$ on $X$
      \item Pseudo-outcome regression $\hat g(x,d,s)$ by regressing $Y/\|U\|^{\hat{\alpha}_{n}}$ on $(X,D,U/\|U\|)$
    \end{enumerate}
    \STATE Define index set $\mathcal{I}=\{i:\|U_i\|>t, (X_i,D_i,Y_i,U_i)\in\mathcal{D}_2\}$ and set $S_i=U_i/\|U_i\|$ for $i\in\mathcal{I}$

      \IF{estimator = IPW}
        \STATE Compute
        \begin{equation}
            \hat\eta_{n,t}^{\mathrm{IPW}}
          = \frac{1}{|\mathcal{I}|} \sum_{i\in\mathcal{I}} \frac{Y_i}{\|U_i\|^{\hat{\alpha}_n} } \Bigl(\frac{D_i}{\hat p(X_i)} - \frac{1-D_i}{1-\hat p(X_i)}\Bigr).\label{eq:eta_ipw}
        \end{equation}
      \ELSE
        \STATE Compute
        \begin{equation}
            \hat\eta_{n,t}^{\mathrm{DR}} = \frac{1}{|\mathcal{I}|} \sum_{i\in\mathcal{I}}\Bigl[\hat g(X_i,1,S_i)-\hat g(X_i,0,S_i)
          + \frac{D_i-\hat p(X_i)}{\hat p(X_i)(1-\hat p(X_i))}\bigl(Y_i/\|U_i\|^{\hat{\alpha}_{n}}-\hat g(X_i,D_i,S_i)\bigr)\Bigr]. \label{eq:eta_dr}
        \end{equation}
      \ENDIF
      \STATE Compute adaptive Hill estimator on $\{\|U_i\|:i\in\mathcal{I}\}$:
      \begin{equation}\label{eq:mu}
          \hat\gamma_n = \frac{1}{k} \sum_{j=1}^{k} \log\frac{\|U_{(j)}\|}{\|U_{(j+1)}\|}, \quad
        \hat\mu_n = \frac{1}{1-\hat{\alpha}_{n}\hat\gamma_n},
      \end{equation}
      where $\|U_{(1)}\|\ge\dots\ge\|U_{(k+1)}\|$ and $k$ is chosen by
      \begin{equation}
           k  = \max \left\{ k \in \{l_n, \cdots, n\} \  \text{and} \  \forall i \in \{l_n,\cdots, n\}, | \hat{\gamma}_i - \hat{\gamma}_k | \leqslant \frac{\hat{\gamma}_i r_n (\delta)}{\sqrt{i}} \right\}, \notag
      \end{equation}
    \textbf{Return}:  $\widehat{\theta}_{n,t}^{\mathrm{estimator}} =  \hat\eta_{n,t}^{\mathrm{estimator}}\cdot\hat\mu_n.$
  \end{algorithmic}
`;
const FLOAT = `\\begin{algorithm}[!tb]${FLOAT_BODY}\\end{algorithm}`;

/** What lies between the units of a cut: only blanks, labels and list delimiters may. */
const GLUE = /^(?:\s|\\label\s*\{[^{}]*\}|\\(?:begin|end)\s*\{(?:enumerate|itemize|description)\}(?:\[[^\]]*\])?)*$/u;
const shown = (text: string, bare = false, max = 40): string[] => {
  const r = algorithmUnits(text, bare);
  return (r.units ?? []).map((u) => `${u.p}/${u.u} ${u.kind} ${text.slice(u.start, u.content).trim()}|${text.slice(u.content, u.end).replace(/\s+/gu, " ").slice(0, max)}`);
};

describe("the algorithm cutter: one paragraph per step, every unit whole", () => {
  it("the real algorithm: input line, steps, the items of a nested list under their step, control lines; caption and delimiters stay between units", () => {
    expect(shown(FLOAT_BODY)).toEqual([
      "1/1 sentence \\REQUIRE|Dataset $\\mathcal{D}=\\{(X_i,D_i,Y_i,U_i)",
      "2/1 sentence \\STATE|Randomly split $\\mathcal{D}$ into two eq",
      "3/1 sentence \\STATE|Using $\\mathcal{D}_1$, estimate:",
      "3/2 item \\item|Propensity function $\\hat p(x)$ via regr",
      "3/3 item \\item|Pseudo-outcome regression $\\hat g(x,d,s)",
      "4/1 sentence \\STATE|Define index set $\\mathcal{I}=\\{i:\\|U_i\\",
      "5/1 sentence |\\IF{estimator = IPW}",
      "6/1 sentence \\STATE|Compute \\begin{equation} \\hat\\eta_{n,t}^",
      "7/1 sentence |\\ELSE",
      "8/1 sentence \\STATE|Compute \\begin{equation} \\hat\\eta_{n,t}^",
      "9/1 sentence |\\ENDIF",
      "10/1 sentence \\STATE|Compute adaptive Hill estimator on $\\{\\|",
    ]);
  });

  it("the units tile the algorithmic block verbatim: the gaps hold only blanks, labels and list delimiters", () => {
    const { units } = algorithmUnits(FLOAT_BODY);
    const block = { start: FLOAT_BODY.indexOf("[1]") + 3, end: FLOAT_BODY.indexOf("\\end{algorithmic}") };
    let at = block.start;
    for (const u of units!) {
      expect(FLOAT_BODY.slice(at, u.start)).toMatch(GLUE);
      expect(u.content).toBeGreaterThanOrEqual(u.start);
      at = u.end;
    }
    expect(FLOAT_BODY.slice(at, block.end)).toMatch(GLUE);
    // the caption is no unit
    expect(units!.every((u) => u.start > FLOAT_BODY.indexOf("\\begin{algorithmic}"))).toBe(true);
    // the last step runs to the end of the block: its displays and the return line stay with it
    expect(FLOAT_BODY.slice(units!.at(-1)!.content, units!.at(-1)!.end)).toMatch(/^Compute adaptive Hill[\s\S]*\\hat\\mu_n\.\$$/u);
  });

  it("algpseudocode (mixed case), a bare algorithmic block, a command inside math or a brace group never cuts", () => {
    const alg = "\\caption{Loop}\n\\begin{algorithmic}\n\\Require $n \\ge 1$\n\\Ensure $x$\n\\State $x \\gets 0$\n\\For{$i = 1, \\dots, n$}\n  \\State $x \\gets x + i$ \\Comment{add}\n  \\If{$x > 5$} \\State \\Return $x$ \\EndIf\n\\EndFor\n\\State \\textbf{output {\\STATE} $x$} and $\\text{\\IF} y$\n\\end{algorithmic}\n";
    expect(shown(alg, false, 80)).toEqual([
      "1/1 sentence \\Require|$n \\ge 1$",
      "2/1 sentence \\Ensure|$x$",
      "3/1 sentence \\State|$x \\gets 0$",
      "4/1 sentence |\\For{$i = 1, \\dots, n$}",
      "5/1 sentence \\State|$x \\gets x + i$ \\Comment{add}",
      "6/1 sentence |\\If{$x > 5$}",
      "7/1 sentence \\State|\\Return $x$",
      "8/1 sentence |\\EndIf",
      "9/1 sentence |\\EndFor",
      "10/1 sentence \\State|\\textbf{output {\\STATE} $x$} and $\\text{\\IF} y$",
    ]);
    expect(shown("[1]\n\\STATE a\n\\STATE b", true)).toEqual(["1/1 sentence \\STATE|a", "2/1 sentence \\STATE|b"]);
  });

  it("a procedure in prose inside a float (no algorithmic block): its sentences and items, the caption left out", () => {
    const t = "\\caption{A procedure. In two steps.}\\label{alg:p}\nProceed as follows.\n\\begin{enumerate}\n\\item Split the sample.\n\\item Estimate.\n\\end{enumerate}\n";
    expect(shown(t)).toEqual(["1/1 sentence |Proceed as follows.", "1/2 item \\item|Split the sample.", "1/3 item \\item|Estimate."]);
  });

  it("markup it does not know is not cut: algorithm2e, text before the first step", () => {
    expect(algorithmUnits("\\caption{c}\n\\KwIn{$x$}\n$y \\gets x$\\;\n\\For{$i$}{ $y \\gets y+1$\\; }\n")).toEqual({ units: null, why: "algorithm2e markup" });
    expect(algorithmUnits("\\begin{algorithmic}\n\\MyStep do this\n\\STATE that\n\\end{algorithmic}")).toEqual({ units: null, why: "text before the first step command" });
    expect(algorithmUnits("\\begin{algorithmic}\n\\item one\n\\end{algorithmic}")).toEqual({ units: null, why: "no step command in its algorithmic block" });
  });
});

// ---------------------------------------------------------------------------------------------
// a paper whose algorithm no result refers to
// ---------------------------------------------------------------------------------------------

const PAPER = [
  "\\documentclass{article}",
  "\\usepackage{amsmath,amssymb,amsthm,enumitem,algorithm,algorithmic}",
  "\\newtheorem{theorem}{Theorem}",
  "\\newtheorem{lemma}{Lemma}",
  "\\begin{document}",
  "",
  "We estimate the effect as follows.",
  "",
  FLOAT,
  "",
  "We summarize our estimators above.",
  "",
  "\\begin{lemma}\\label{lem:mu}",
  "The estimator $\\hat\\gamma_n$ is consistent.",
  "\\end{lemma}",
  "\\begin{proof}",
  "By the law of large numbers.",
  "\\end{proof}",
  "",
  "\\begin{theorem}\\label{thm:rate}",
  "The estimator $\\widehat{\\theta}_{n,t}^{\\mathrm{estimator}}$ is consistent.",
  "\\end{theorem}",
  "",
  "\\end{document}",
  "",
].join("\n");

const REF = {
  qid: "alg_paper",
  target_estimand: "the effect",
  symbols: [],
  assumptions: [],
  definitions: [{ id: "def:nete-algorithm", name: "Algorithm for NETE Estimation", source: { prose: true, slice: { from: "\\begin{algorithm}[!tb]", to: "\\end{algorithm}" } }, inputs: ["t"] }],
  statements: [
    { id: "lem:mu", kind: "lemma", env: "lem:mu", depends_on: ["def:nete-algorithm"] },
    { id: "thm:rate", kind: "theorem", env: "thm:rate", depends_on: ["def:nete-algorithm", "lem:mu"] },
  ],
};
const STEP = "Compute the adaptive Hill estimator on all $n$ radii:\n\\begin{equation}\\label{eq:mu}\n\\hat\\gamma_n = \\frac{1}{k} \\sum_{j=1}^{k} \\log\\frac{\\|U_{(j)}\\|}{\\|U_{(k+1)}\\|}, \\quad \\hat\\mu_n = \\frac{1}{1-\\hat{\\alpha}_{n}\\hat\\gamma_n}.\n\\end{equation}\nReturn $\\widehat{\\theta}_{n,t}^{\\mathrm{estimator}} = \\hat\\eta_{n,t}^{\\mathrm{estimator}}\\cdot\\hat\\mu_n$.";
const ops = (x: unknown[]): PatchOp[] => x.map((o) => PatchOpSchema.parse(o));
const STEP_OPS = ops([{ op: "replace", unit: "alg:nete/10/1", tex: STEP }]);

async function seed(): Promise<{ dir: string; src: PassageSources; envs: EnvsJson; flat: Awaited<ReturnType<typeof buildEnvsJson>>["flat"]; transcribed: ReturnType<typeof materializeRefCore>["core"] }> {
  const dir = await mkdtemp(path.join(os.tmpdir(), "verify-alg-"));
  tmp.push(dir);
  await mkdir(path.join(dir, "source"), { recursive: true });
  await writeFile(path.join(dir, "source", "main.tex"), PAPER, "utf8");
  const { envs, flat } = await buildEnvsJson(path.join(dir, "source"), "main.tex");
  const refs = RefCoreSchema.parse(REF);
  const { core: transcribed, violations } = materializeRefCore(refs, envs, flat.text);
  expect(violations).toEqual([]);
  const units = PaperUnits.parse(flat.text, envs, flatLineStart(flat.text, flat.lineMap));
  return { dir, src: { units, refs, statements: transcribed.statements, envs }, envs, flat, transcribed };
}

describe("units of an algorithm the paper's results do not refer to", () => {
  it("envs.json leaves the float out; the units file still holds it as a region under its caption's label, ids <label>/<step>/<unit>", async () => {
    const { src, envs, transcribed } = await seed();
    expect(envs.envs.map((e) => e.id)).toEqual(["lem:mu", "thm:rate"]);
    expect(transcribed.definitions[0]!.construction).toBe(FLOAT);
    expect(transcribed.definitions[0]!.tex_locator?.env).toBe("prose");
    const reg = src.units.region("alg:nete")!;
    expect(reg.algorithm).toBe(true);
    expect(src.units.flat.slice(reg.start, reg.end)).toBe(FLOAT_BODY);
    expect(src.units.unitsOf("alg:nete").map((u) => u.id)).toEqual(["alg:nete/1/1", "alg:nete/2/1", "alg:nete/3/1", "alg:nete/3/2", "alg:nete/3/3", "alg:nete/4/1", "alg:nete/5/1", "alg:nete/6/1", "alg:nete/7/1", "alg:nete/8/1", "alg:nete/9/1", "alg:nete/10/1"]);
    expect(src.units.textById("alg:nete/2/1")).toBe("Randomly split $\\mathcal{D}$ into two equal parts $\\mathcal{D}_1$ and $\\mathcal{D}_2$");
    expect(src.units.itemsOf(src.units.unitById("alg:nete/3/2")!).map((u) => u.id)).toEqual(["alg:nete/3/2", "alg:nete/3/3"]);
    expect(src.units.file.warnings).toBeUndefined();
    // the units of every listed environment are what they were
    expect(src.units.unitsOf("lem:mu").map((u) => src.units.textOf(u))).toEqual(["The estimator $\\hat\\gamma_n$ is consistent."]);
  });

  it("the definition transcribed from the running text is located in it: a passage, its span the whole float — no longer a node without printed text", async () => {
    const { src } = await seed();
    const p = nodePassage(src, "def:nete-algorithm")!;
    expect(p.env).toBe("alg:nete");
    expect(p.units).toHaveLength(12);
    expect(src.units.flat.slice(p.span!.start, p.span!.end)).toBe(FLOAT);
    const isTextless = (n: string): boolean => n === "def:nete-algorithm" && nodePassage(src, n) === null;
    const raw = { patches: [{ node: "def:nete-algorithm", ops: STEP_OPS, proof_note: null }], unfixable: [] };
    expect(normalizeTextlessEntries(raw, isTextless)).toEqual({ raw, nodes: [] });
    // the fixer is shown the algorithm with a result that uses it, step by step
    const block = unitsBlock(src, ["lem:mu"]);
    expect(block).toContain("def:nete-algorithm — printed text (env alg:nete; an algorithm, step by step: each step with its command, which stays):");
    expect(block).toContain("[alg:nete/2/1] \\STATE Randomly split");
    expect(block).toContain("[alg:nete/5/1] \\IF{estimator = IPW}");
    expect(block).not.toContain("no proof of env alg:nete");
  });

  it("a paper's own theorem-like `algorithm` (prose, a list) and an algorithm2e float keep today's cut; the latter is reported", () => {
    const body = "\\label{alg:t}\nPartition the sample. Denote the folds.\n\\begin{enumerate}\n\\item Estimate.\n\\item Average.\n\\end{enumerate}\n";
    const a2e = "\\caption{Loop}\\label{alg:two}\n\\KwIn{$x$}\n$y \\gets x$\\;\n";
    const flat = `\\begin{algorithm}[Target]${body}\\end{algorithm}\nText.\n\\begin{algorithm}[H]\n${a2e}\\end{algorithm}\n`;
    const envs = { envs: [{ id: "alg:t", kind: "other", envName: "algorithm", label: "alg:t", title: "Target", body, proof: null, proofLines: null, lines: { file: "m", from: 1, to: 8 }, refs: [] }] } as unknown as EnvsJson;
    const u = PaperUnits.parse(flat, envs);
    expect(u.unitsOf("alg:t").map((x) => `${x.id} ${x.kind}`)).toEqual(regionUnits(body).map((x) => `alg:t/${x.p}/${x.u} ${x.kind}`));
    expect(u.region("alg:t")!.algorithm).toBeUndefined();
    expect(u.file.regions.map((r) => r.id)).toEqual(["alg:t"]);
    expect(u.file.warnings).toEqual(["alg:two: the algorithm is not cut into steps (algorithm2e markup); it has no units"]);
  });

  it("a units.json of an earlier cut is parsed again; the ids of the listed environments do not move", async () => {
    const { dir, envs, flat, src } = await seed();
    await mkdir(path.join(dir, "discovery"), { recursive: true });
    await writeFile(path.join(dir, VERIFY_FILES.flatTex), flat.text, "utf8");
    await writeFile(path.join(dir, VERIFY_FILES.envsJson), JSON.stringify(envs), "utf8");
    const { version: _v, ...old } = src.units.file;
    const before = { ...old, regions: old.regions.filter((r) => !r.algorithm), units: old.units.filter((u) => u.env !== "alg:nete") };
    await writeFile(path.join(dir, "discovery", "units.json"), JSON.stringify(before), "utf8");
    const now = (await loadUnits(dir))!;
    expect(now.file.version).toBe(UNITS_VERSION);
    expect(now.unitsOf("alg:nete")).toHaveLength(12);
    expect(now.file.units.filter((u) => u.env !== "alg:nete")).toEqual(before.units);
    expect(JSON.parse(readFileSync(path.join(dir, "discovery", "units.json"), "utf8")).version).toBe(UNITS_VERSION);
  });
});

describe("one step replaced in place", () => {
  it("the corrected algorithm is the float with that step's text replaced: every other step, the caption and the delimiters verbatim", async () => {
    const { src } = await seed();
    const scope = { units: src.units, passage: nodePassage(src, "def:nete-algorithm") };
    const m = materializeRepair(STEP_OPS, scope, "def");
    expect(m.problems).toEqual([]);
    const cut = FLOAT.indexOf("Compute adaptive Hill");
    expect(m.corrected_statement).toBe(`${FLOAT.slice(0, cut)}${STEP}\n  \\end{algorithmic}\n\\end{algorithm}`);
    // an item of the list nested in a step, and a control line
    const two = materializeRepair(ops([{ op: "replace", unit: "alg:nete/3/2", tex: "Propensity $\\hat p$ by logistic regression" }, { op: "replace", unit: "alg:nete/5/1", tex: "\\IF{estimator is IPW}" }]), scope, "def");
    expect(two.problems).toEqual([]);
    expect(two.corrected_statement).toBe(FLOAT.replace("Propensity function $\\hat p(x)$ via regression of $D$ on $X$", "Propensity $\\hat p$ by logistic regression").replace("\\IF{estimator = IPW}", "\\IF{estimator is IPW}"));
  });

  it("an op stays inside one step and keeps the algorithm's structure", async () => {
    const { src } = await seed();
    const scope = { units: src.units, passage: nodePassage(src, "def:nete-algorithm") };
    const problems = (o: unknown[]): string => materializeRepair(ops(o), scope, "def").problems.join("\n");
    expect(problems([{ op: "replace", unit: "alg:nete/2/1", to: "alg:nete/4/1", tex: "Split.\n\\STATE Estimate." }])).toContain("crosses steps of an algorithm — replace each step by an op of its own");
    expect(problems([{ op: "replace", unit: "alg:nete/2/1", tex: "\\STATE Split the sample" }])).toContain("is a step of an algorithm: `tex` is the step's text, with no step or control command (\\STATE)");
    expect(problems([{ op: "replace", unit: "alg:nete/5/1", tex: "estimator is IPW" }])).toContain("is a control line of an algorithm: `tex` is the one control line that replaces it");
    expect(problems([{ op: "replace", unit: "alg:nete/3/2", tex: "\\item Propensity" }])).toContain("is a list item");
    // the whole nested list of a step, as for any list
    expect(problems([{ op: "replace", unit: "alg:nete/3/2", to: "alg:nete/3/3", tex: "\\begin{enumerate}\n\\item Both nuisances by regression\n\\end{enumerate}" }])).toBe("");
  });

  it("the build: the definition's construction is the corrected algorithm, the results using it stay wired and their basis moves; the compile check takes the step, not the float", async () => {
    const { src, transcribed } = await seed();
    const stored = PatchFileSchema.parse({ key_results: ["thm:rate"], key_contribution: "c", patches: [{ node: "def:nete-algorithm", corrected_statement: null, ops: STEP_OPS, proof_note: "The proof as printed proves the repaired statement; no step changes.", consequence_of: ["lem:mu"], reason: "Lemma~\\ref{lem:mu} uses the full-sample statistic." }], unfixable: [] });
    const { file, changed } = rederiveOn(stored, src);
    expect(changed).toEqual([{ node: "def:nete-algorithm", applied: true, fields: ["corrected_statement"] }]);
    const { core } = applyPatchFile(transcribed, file);
    const def = core.definitions.find((d) => d.id === "def:nete-algorithm")!;
    expect(def.construction).toBe(file.patches[0]!.corrected_statement);
    expect(def.construction).toContain("\\STATE Compute the adaptive Hill estimator on all $n$ radii:");
    expect(def.construction).toContain("\\STATE Randomly split $\\mathcal{D}$ into two equal parts");
    expect(def.construction).not.toContain("\\|U_{(j+1)}\\|");
    for (const id of ["lem:mu", "thm:rate"]) {
      expect(core.statements.find((s) => s.id === id)!.depends_on).toContain("def:nete-algorithm");
      expect(core.statements.find((s) => s.id === id)!.statement).toBe(transcribed.statements.find((s) => s.id === id)!.statement);
      expect(basisOf(basisInputs(core, id))).not.toBe(basisOf(basisInputs(transcribed, id)));
    }
    // the paper's own characters in the steps left as printed are no defect of the repair
    const hyphen = (t: string): string => t.replace("Pseudo-outcome", "Pseudo\u2010outcome");
    const printedCore = { ...transcribed, definitions: transcribed.definitions.map((d) => ({ ...d, construction: hyphen(d.construction ?? "") })) };
    const derived = { ...file, patches: file.patches.map((x) => ({ ...x, corrected_statement: hyphen(x.corrected_statement ?? "") })) };
    expect(repairTextViolations(printedCore, derived, null)).toEqual([]);
    const fields = patchFileTexFields(file).filter((f) => f.text);
    expect(fields.map((f) => f.where)).toEqual(['the patch for "def:nete-algorithm": ops[0] (replace)', 'the patch for "def:nete-algorithm": its proof_note', 'the patch for "def:nete-algorithm": its reason']);
    expect(patchFileTexFields(rederiveOn(PatchFileSchema.parse({ ...stored, patches: [{ ...stored.patches[0]!, ops: ops([{ op: "replace", unit: "alg:nete/5/1", tex: "\\IF{estimator is IPW}" }]) }] }), src).file).find((f) => f.where.includes("ops[0]"))!.text).toBe("estimator is IPW");
  });
});

// ---------------------------------------------------------------------------------------------
// the annotated paper, the corrected paper, the page
// ---------------------------------------------------------------------------------------------

async function plans(patchOps: PatchOp[]): Promise<{ annotated: string; corrected: ReturnType<typeof correctedTex>; plan: ReturnType<typeof planAnnotations>; dir: string }> {
  const { dir, src, envs, flat, transcribed } = await seed();
  const { file } = rederiveOn(PatchFileSchema.parse({ key_results: ["thm:rate"], key_contribution: "c", patches: [{ node: "def:nete-algorithm", corrected_statement: null, ops: patchOps, proof_note: "unchanged" }], unfixable: [] }), src);
  const { core } = applyPatchFile(transcribed, file);
  const input: AnnotationInput = {
    envs,
    flatText: flat.text,
    lineMap: flat.lineMap,
    refs: src.refs,
    transcribed,
    core,
    patches: file as AnnotationInput["patches"],
    paperErrors: { "def:nete-algorithm": { detail: "The radial step uses the wrong sample.", witness: null } } as never,
    findings: [],
    review: null,
    files: { "main.tex": PAPER },
  };
  const plan = planAnnotations(input);
  const view = planAnnotations({ ...input, correctedView: true });
  return { annotated: applyEdits(PAPER, plan.edits["main.tex"] ?? []), corrected: correctedTex(applyEdits(PAPER, view.edits["main.tex"] ?? []), { proofEnv: true }), plan, dir };
}

describe("a repaired step in the annotated paper, the corrected paper and the page", () => {
  it("inside the float: the step's command, its printed text red, the replacement blue; every other line as printed; the float is never wrapped", async () => {
    const { annotated, plan } = await plans(STEP_OPS);
    expect(plan.unlocated).toEqual([]);
    expect(annotated).toContain("\\STATE \\vsOriginal{Compute adaptive Hill estimator on $\\{\\|U_i\\|:i\\in\\mathcal{I}\\}$:");
    expect(annotated).toMatch(/\\cdot\\hat\\mu_n\.\$\} \\vsCorrected\{Compute the adaptive Hill estimator on all \$n\$ radii:[\s\S]*?\} \\vsNote\{[\s\S]*?\}\n {2}\\end\{algorithmic\}\n\\end\{algorithm\}/u);
    expect(annotated).not.toMatch(/\\vs[A-Za-z]+\{\s*\\begin\{algorithm\}/u);
    expect(annotated).toContain("\\begin{algorithm}[!tb]\n  \\caption{Algorithm for NETE Estimation}\\label{alg:nete}\n  \\begin{algorithmic}[1]\n    \\REQUIRE Dataset");
    expect(annotated).toContain("    \\STATE Randomly split $\\mathcal{D}$ into two equal parts $\\mathcal{D}_1$ and $\\mathcal{D}_2$\n");
    // the float is balanced: what the marks add opens and closes inside one step
    const float = annotated.slice(annotated.indexOf("\\begin{algorithm}"), annotated.indexOf("\\end{algorithm}"));
    expect(float.split("{").length).toBe(float.split("}").length);
    expect(plan.records.filter((r) => r.node === "def:nete-algorithm").map((r) => r.located_by)).toEqual(["units"]);
  });

  it("the corrected paper carries the step in place, in the source float; nothing of the review is left", async () => {
    const { corrected } = await plans(STEP_OPS);
    const a = corrected.tex.indexOf("\\begin{algorithm}");
    const float = corrected.tex.slice(a, corrected.tex.indexOf("\\end{algorithm}", a) + "\\end{algorithm}".length);
    expect(float).not.toMatch(/\\vs[A-Z]/u);
    expect(float).toContain("\\ENDIF\n      \\STATE Compute the adaptive Hill estimator on all $n$ radii:");
    expect(float).not.toContain("Compute adaptive Hill estimator on $\\{");
    expect(float.replace(/\\STATE Compute the adaptive Hill[\s\S]*$/u, "")).toBe(FLOAT.slice(0, FLOAT.indexOf("\\STATE Compute adaptive Hill")));
    expect(corrected.items.filter((i) => i.kind === "unplaced")).toEqual([]);
  });

  it("a control line cannot be wrapped: its replacement is printed after the algorithm as source, and the corrected paper lists it as not written (never dropped)", async () => {
    const { annotated, corrected, plan } = await plans(ops([{ op: "replace", unit: "alg:nete/5/1", tex: "\\IF{estimator is IPW}" }]));
    expect(annotated).toContain("      \\IF{estimator = IPW}\n");
    expect(annotated).toMatch(/\\end\{algorithm\} \\vsCorrected\{\\texttt\{\\textbackslash\{\}IF\\\{estimator = IPW\\\} --- replaced by: \\textbackslash\{\}IF\\\{estimator is IPW\\\}\}\}/u);
    expect(plan.log.join("\n")).toContain("a control line of the algorithm (alg:nete/5/1) cannot be marked in place");
    expect(corrected.tex).toContain("\\IF{estimator = IPW}");
    expect(corrected.items.filter((i) => i.node === "def:nete-algorithm").map((i) => i.kind)).toEqual(["unplaced"]);
  });

  it("the page draws the marks inside the step's line, and a command inside a mark starts no line", async () => {
    const { annotated } = await plans(STEP_OPS);
    const html = renderPaper({ files: { "main.tex": annotated }, main: "main.tex", aux: "" }).html;
    const fig = html.slice(html.indexOf('<figure class="alg"'), html.indexOf("</figure>"));
    expect(fig.match(/<li style="--lvl:\d">/gu)).toHaveLength(10);
    expect(fig).toMatch(/<span class="ln">9<\/span><span class="lt">\s*<div class="rv del"[^>]*><span class="rv-tag">Original<\/span> Compute adaptive Hill estimator/u);
    expect(fig).toMatch(/<div class="rv ins"[^>]*><span class="rv-tag">Revised<\/span> Compute the adaptive Hill estimator on all/u);
    const inMark = renderPaper({ files: { "m.tex": "\\begin{document}\\begin{algorithmic}[1]\n\\State \\vsOriginal{\\Return $x$ \\Comment{old}} \\vsCorrected{$y$}\n\\State done\n\\end{algorithmic}\\end{document}" }, main: "m.tex", aux: "" }).html;
    expect(inMark.match(/<li style="--lvl:\d">/gu)).toHaveLength(2);
  });

  const hasTex = ((): boolean => {
    try {
      return findExecutable("pdflatex", { nativeOnly: true }) !== null && execFileSync("kpsewhich", ["algorithmic.sty"], { encoding: "utf8" }).trim() !== "";
    } catch {
      return false;
    }
  })();
  it.skipIf(!hasTex)("the annotated float compiles with pdflatex (marks inside an algorithmic step, a display in each)", async () => {
    const { annotated, dir } = await plans(ops([{ op: "replace", unit: "alg:nete/3/2", tex: "Propensity $\\hat p$ by logistic regression" }, { op: "replace", unit: "alg:nete/5/1", tex: "\\IF{estimator is IPW}" }, ...STEP_OPS]));
    const out = path.join(dir, "build");
    await mkdir(out, { recursive: true });
    await writeFile(path.join(out, "main.tex"), injectPreamble(annotated, false).tex, "utf8");
    let log = "";
    try {
      log = execFileSync("pdflatex", ["-interaction=nonstopmode", "-halt-on-error", "main.tex"], { cwd: out, encoding: "utf8" });
    } catch (e) {
      log = String((e as { stdout?: string }).stdout ?? e);
    }
    expect(log.split("\n").filter((l) => l.startsWith("!"))).toEqual([]);
    expect(existsSync(path.join(out, "main.pdf"))).toBe(true);
  }, 120_000);
});

describe("an algorithm2e float the paper sets in a brace group, its whole body replaced", () => {
  const BODY = "\\caption{Loop}\\label{alg:two}\n  \\SetAlgoNoEnd\n  \\KwIn{$x$}\n  $y \\gets x$\\;\n  \\For{$i = 1, \\dots, n$}{\n    $y \\gets y + i$\\;\n  }\n\\textbf{return} $y$";
  const GROUPED = `{\\begin{algorithm}[t]${BODY}\n\\end{algorithm}}`;
  const PAPER2 = ["\\documentclass{article}", "\\usepackage{amsmath,amssymb,amsthm}", "\\usepackage[ruled]{algorithm2e}", "\\newtheorem{theorem}{Theorem}", "\\begin{document}", "", GROUPED, "", "\\begin{theorem}\\label{thm:loop}", "Algorithm~\\ref{alg:two} returns $x + n(n+1)/2$.", "\\end{theorem}", "", "\\end{document}", ""].join("\n");
  const REF2 = {
    qid: "alg2e_paper",
    target_estimand: "the sum",
    symbols: [],
    assumptions: [],
    definitions: [{ id: "def:loop", name: "Loop", source: { env: "alg:two" }, inputs: ["x"] }],
    statements: [{ id: "thm:loop", kind: "theorem", env: "thm:loop", depends_on: ["def:loop"] }],
  };
  const FIXED = BODY.replace("$y \\gets y + i$", "$y \\gets y + 2i$");
  async function plans2(): Promise<{ annotated: string; corrected: ReturnType<typeof correctedTex>; plan: ReturnType<typeof planAnnotations>; dir: string }> {
    const dir = await mkdtemp(path.join(os.tmpdir(), "verify-alg2e-"));
    tmp.push(dir);
    await mkdir(path.join(dir, "source"), { recursive: true });
    await writeFile(path.join(dir, "source", "main.tex"), PAPER2, "utf8");
    const { envs, flat } = await buildEnvsJson(path.join(dir, "source"), "main.tex");
    const refs = RefCoreSchema.parse(REF2);
    const { core: transcribed, violations } = materializeRefCore(refs, envs, flat.text);
    expect(violations).toEqual([]);
    const units = PaperUnits.parse(flat.text, envs, flatLineStart(flat.text, flat.lineMap));
    // algorithm2e is not cut into steps: the body is one unit, replaced whole
    expect(units.unitsOf("alg:two").map((u) => u.id)).toEqual(["alg:two/1/1"]);
    const src = { units, refs, statements: transcribed.statements, envs };
    const { file } = rederiveOn(PatchFileSchema.parse({ key_results: ["thm:loop"], key_contribution: "c", patches: [{ node: "def:loop", corrected_statement: null, ops: ops([{ op: "replace", unit: "alg:two/1/1", tex: FIXED }]), proof_note: "unchanged" }], unfixable: [] }), src);
    const { core } = applyPatchFile(transcribed, file);
    const input: AnnotationInput = {
      envs,
      flatText: flat.text,
      lineMap: flat.lineMap,
      refs,
      transcribed,
      core,
      patches: file as AnnotationInput["patches"],
      paperErrors: { "def:loop": { detail: "The loop adds $i$ once.", witness: null } } as never,
      findings: [],
      review: null,
      files: { "main.tex": PAPER2 },
    };
    const plan = planAnnotations(input);
    const view = planAnnotations({ ...input, correctedView: true });
    return { annotated: applyEdits(PAPER2, plan.edits["main.tex"] ?? []), corrected: correctedTex(applyEdits(PAPER2, view.edits["main.tex"] ?? []), { proofEnv: true }), plan, dir };
  }

  it("the annotated paper marks it inside the float: the printed body red, the corrected one blue, both before \\end{algorithm}; the label stays once", async () => {
    const { annotated, plan } = await plans2();
    expect(plan.unlocated).toEqual([]);
    const float = annotated.slice(annotated.indexOf("{\\begin{algorithm}"), annotated.indexOf("\\end{algorithm}}"));
    expect(float).toContain("\\vsOriginal{\\caption{Loop}\\label{alg:two}");
    expect(float).toContain("\\vsCorrected{\\caption{Loop}\\vsLabel{alg:two}");
    expect(float).toContain("$y \\gets y + 2i$");
    expect(annotated.slice(annotated.indexOf("\\end{algorithm}}"))).not.toContain("\\vsCorrected");
    expect(annotated.match(/\\label\{alg:two\}/gu)).toHaveLength(1);
  });

  it("the corrected paper prints one algorithm, the corrected one, in the paper's float and brace group", async () => {
    const { corrected } = await plans2();
    expect(corrected.tex.match(/\\begin\{algorithm\}/gu)).toHaveLength(1);
    expect(corrected.tex.match(/\\label\{alg:two\}/gu)).toHaveLength(1);
    const float = corrected.tex.slice(corrected.tex.indexOf("{\\begin{algorithm}[t]"), corrected.tex.indexOf("\\end{algorithm}}"));
    expect(float).toContain("$y \\gets y + 2i$");
    expect(float).toContain("\\caption{Loop}\\label{alg:two}");
    expect(corrected.tex).not.toContain("$y \\gets y + i$");
    expect(corrected.tex).not.toMatch(/\\vs[A-Z]/u);
    expect(corrected.items.filter((i) => i.kind === "unplaced")).toEqual([]);
  });

  const hasA2e = ((): boolean => {
    try {
      return findExecutable("pdflatex", { nativeOnly: true }) !== null && execFileSync("kpsewhich", ["algorithm2e.sty"], { encoding: "utf8" }).trim() !== "";
    } catch {
      return false;
    }
  })();
  it.skipIf(!hasA2e)("the annotated paper and the corrected paper compile with pdflatex", async () => {
    const { annotated, corrected, dir } = await plans2();
    for (const [name, tex] of [["annotated", injectPreamble(annotated, false).tex], ["corrected", corrected.tex]] as const) {
      const out = path.join(dir, name);
      await mkdir(out, { recursive: true });
      await writeFile(path.join(out, "main.tex"), tex, "utf8");
      let log = "";
      try {
        log = execFileSync("pdflatex", ["-interaction=nonstopmode", "-halt-on-error", "main.tex"], { cwd: out, encoding: "utf8" });
      } catch (e) {
        log = String((e as { stdout?: string }).stdout ?? e);
      }
      expect(log.split("\n").filter((l) => l.startsWith("!"))).toEqual([]);
      expect(existsSync(path.join(out, "main.pdf"))).toBe(true);
    }
  }, 120_000);
});

describe("the prompts", () => {
  const prompt = (rel: string): string => readFileSync(new URL(`../../src/verify/prompts/${rel}`, import.meta.url), "utf8").replace(/\s+/gu, " ");
  it("the fixer repairs a wrong step in the algorithm; the transcriber never restates a procedure in a setting; the referee judges against the algorithm as corrected", () => {
    expect(prompt("V1/patch.txt")).toContain("A wrong step of an algorithm PAPER UNITS lists step by step is repaired in the algorithm — that step's units replaced, once — never by restating the results that use it.");
    expect(prompt("V1/patch.txt")).toContain("for a step of an algorithm its text (its step command stays; one op per step, a control line replaced by a control line)");
    expect(prompt("V1/extract_core.txt")).toContain("A setting says how the data arise and which objects are random; a procedure the paper states as an algorithm or a definition is referred to by its node id, never restated in the setting.");
    expect(prompt("V1/extract_core.txt")).toContain("(one SCOPE does not list: a `prose` slice from its `\\begin` to its `\\end`)");
    expect(prompt("V1.5/review.txt")).toContain("is judged against the algorithm as printed (as corrected, when its definition carries a repair), or as the result's own corrected statement restates it");
  });
});
