/**
 * Compile-at-source (design 2026-09-25, P1): a model-written TeX fragment is checked by compiling it
 * against the paper's own preamble (`tex_fragment_check.ts`), and every producer but the V1 fixer
 * sends a fragment that does not compile back through its feedback loop with the compiler's line —
 * the V1.5 referee's readings and conditions, the symbol referee's readings and table fixes. The
 * reply schemas constrain every TeX-bearing string to printable ASCII.
 */
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import { existsSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { afterEach, describe, expect, it } from "vitest";
import { ASCII_TEX_PATTERN, OWNER_EXPLANATION_JSON } from "../../src/verify/owner_text.js";
import { PATCH_REPLY_JSON_SCHEMA } from "../../src/verify/patches.js";
import { refereeTexViolations } from "../../src/verify/stage_v1_5.js";
import { envImbalance } from "../../src/verify/tex_balance.js";
import { PaperUnits } from "../../src/verify/units.js";
import { balancedLikeUnit, bodyDefinitionList, bodyDefinitions, checkTexFragment, compileOutcome, envKeepProblem, firstLatexError, mathModeHint, patchFileTexFields, scratchDocument, texFieldViolations, unknownRefs, withLocalBodyDefinitions, withoutMissingInputs } from "../../src/verify/tex_fragment_check.js";
import type { V15NodeVerdict } from "../../src/verify/types.js";
import { V15_NODE_REPLY, V15_SYMBOL_REPLY } from "../../src/verify/v1_5_schema.js";
import { findExecutable } from "../../src/shared/program.js";

const dirs: string[] = [];
afterEach(async () => {
  for (const d of dirs.splice(0)) await rm(d, { recursive: true, force: true });
});

const hasPdflatex = findExecutable("pdflatex", { nativeOnly: true }) !== null;

const PAPER = [
  "\\documentclass{article}",
  "\\usepackage{amsmath,amssymb,amsthm}",
  "\\newtheorem{theorem}{Theorem}",
  "\\newcommand{\\E}{\\mathbb{E}}",
  "\\begin{document}",
  "\\begin{theorem}\\label{thm:a}The bound holds.\\end{theorem}",
  "\\begin{proof}By the moment bound, $\\E|U_1|^q \\le \\bar c$.\\end{proof}",
  "\\end{document}",
  "",
].join("\n");

/** A run directory with the paper under `source/` and `discovery/envs.json` naming its main file. */
async function paperRun(tex = PAPER): Promise<string> {
  const dir = await mkdtemp(path.join(os.tmpdir(), "texcheck-"));
  dirs.push(dir);
  await mkdir(path.join(dir, "source"), { recursive: true });
  await mkdir(path.join(dir, "discovery"), { recursive: true });
  await writeFile(path.join(dir, "source", "main.tex"), tex, "utf8");
  await writeFile(path.join(dir, "discovery", "envs.json"), JSON.stringify({ main_file: "main.tex" }), "utf8");
  return dir;
}

/** Run `f` with pdflatex off PATH. */
async function withoutPdflatex<T>(f: () => Promise<T>): Promise<T> {
  const saved = process.env.PATH;
  process.env.PATH = (saved ?? "").split(path.delimiter).filter((d) => {
    const directory = process.platform === "win32" ? d.replace(/^"(.*)"$/, "$1") : d;
    return !d || !findExecutable(path.resolve(directory, "pdflatex"), { nativeOnly: true });
  }).join(path.delimiter);
  try {
    return await f();
  } finally {
    process.env.PATH = saved;
  }
}

describe("checkTexFragment", () => {
  it("pure parts: the scratch document wraps the fragment as the paper sets it; the first log error with its context", () => {
    const doc = scratchDocument("\\documentclass{article}\n", false, "FRAG", "statement");
    expect(doc).toContain("\\begin{vsCheckStatement}\\vsCorrected{FRAG}\n\\end{vsCheckStatement}");
    expect(doc).toContain("\\@ifundefined{theorem}");
    expect(doc).toContain("% TheoremChecker annotation macros");
    expect(scratchDocument("\\documentclass{article}\n", false, "FRAG", "note")).toContain("\\vsNote{FRAG}");
    expect(scratchDocument("\\documentclass{article}\n", false, "FRAG", "step")).toContain("\\begin{vsCheckProof}\\vsCorrectedStep{FRAG}");
    const log = "This is pdfTeX\n./frag.tex:31: Missing $ inserted.\n<inserted text> \n                $\nl.31 \\vsNote{It fails when e_\n                              n tends to zero.}\n";
    expect(firstLatexError(log)).toBe("Missing $ inserted. (at: \\vsNote{It fails when e_)");
    expect(firstLatexError("no error here")).toBeNull();
    // an error line the log wrapped at 79 columns is read whole
    const long = "./frag.tex:12: Display too wide (605.06154pt, line 382.48499pt): break it over lines";
    expect(firstLatexError(`${long.slice(0, 79)}\n${long.slice(79)}\nl.12 x\n`)).toBe("Display too wide (605.06154pt, line 382.48499pt): break it over lines (at: x)");
    // a clean exit is a pass even when an overfull box's dump wraps onto a "! " line (live CNS thm:ci)
    const dump = readFileSync(path.join(path.dirname(fileURLToPath(import.meta.url)), "fixtures", "overfull_box_bang.log"), "latin1");
    expect(firstLatexError(dump)).not.toBeNull();
    expect(compileOutcome(false, dump)).toEqual({ ok: true });
    expect(compileOutcome(true, log)).toMatchObject({ ok: false, error: expect.stringContaining("Missing $ inserted") });
    expect(compileOutcome(true, "")).toMatchObject({ ok: false, cacheable: false });
  });

  it("a non-ASCII character or unbalanced braces fail before any compile (with or without a paper)", async () => {
    const run = await mkdtemp(path.join(os.tmpdir(), "texcheck-nopaper-"));
    dirs.push(run);
    expect(await checkTexFragment("the bound σ ≥ c", "note", { runDir: run })).toEqual({ ok: false, error: "a non-ASCII character U+03C3 (σ), U+2265 (≥) — the text is plain ASCII; every symbol is a TeX command" });
    expect(await checkTexFragment("the set \\{x : f(x} > 0 of {positive values", "note", { runDir: run })).toEqual({ ok: false, error: "a } that closes no { — braces that print are \\{ … \\}" });
  });

  it("without pdflatex on PATH the compile is skipped (ok, logged); the render checkpoint still guards", async () => {
    const run = await paperRun();
    const logs: string[] = [];
    const r = await withoutPdflatex(() => checkTexFragment("It fails when e_n tends to zero.", "note", { runDir: run, log: (m) => logs.push(m) }));
    expect(r).toEqual({ ok: true, skipped: "pdflatex is not on PATH" });
    expect(logs).toEqual(["tex check: skipped — pdflatex is not on PATH (the annotated paper's compile still guards)"]);
  });

  it.skipIf(!hasPdflatex)("ok and fail against the paper's preamble (its macros count); the compiler's first line with its context", async () => {
    const run = await paperRun();
    expect(await checkTexFragment("By the moment bound, $\\E|U_1|^q \\le \\bar c$ for $q \\le 4$.", "note", { runDir: run })).toEqual({ ok: true });
    expect(await checkTexFragment("$f_0:\\mathbb{R}\\rightarrow[0,\\infty)$ is the density of $Y(0)$.", "note", { runDir: run })).toEqual({ ok: true });
    expect(await checkTexFragment("The rate is $n^{-1/3}$ under Theorem~\\ref{thm:a}.", "statement", { runDir: run })).toEqual({ ok: true });
    expect(await checkTexFragment("Take $\\E Y = 0$.", "hypothesis", { runDir: run })).toEqual({ ok: true });
    expect(await checkTexFragment("Hence $a \\le b$.", "step", { runDir: run })).toEqual({ ok: true });
    const bad = await checkTexFragment("It fails when e_n tends to zero.", "note", { runDir: run });
    expect(bad).toEqual({ ok: false, error: expect.stringMatching(/^Missing \$ inserted\. \(at: .*It fails when e_/u) });
    expect(await checkTexFragment("the class $\\Gammaa$ is finite", "note", { runDir: run })).toEqual({ ok: false, error: expect.stringMatching(/^Undefined control sequence\. \(at: .*\\Gammaa/u) });
    // a macro the paper does not define is an error: the check is against THIS paper
    const other = await paperRun(PAPER.replace("\\newcommand{\\E}{\\mathbb{E}}\n", ""));
    expect(await checkTexFragment("$\\E Y$", "note", { runDir: other })).toMatchObject({ ok: false, error: expect.stringContaining("Undefined control sequence") });
    // a macro the paper defines in its BODY counts (read from the flattened paper)
    const body = PAPER.replace("\\begin{proof}", "\\newcommand{\\fp}[2]{z_{1,#1}(#2)}\\begin{proof}");
    const withBody = await paperRun(body);
    await writeFile(path.join(withBody, "discovery", "flat.tex"), body, "utf8");
    expect(await checkTexFragment("Here $\\fp{y}{x}$ is the first choice.", "note", { runDir: withBody })).toEqual({ ok: true });
    // body definitions that break the preamble are dropped, never the check: the fragment is still checked
    const broken = body.replace("\\begin{proof}", "\\renewcommand{\\nosuchmacro}{x}\\begin{proof}");
    const withBroken = await paperRun(broken);
    await writeFile(path.join(withBroken, "discovery", "flat.tex"), broken, "utf8");
    const said: string[] = [];
    expect(await checkTexFragment("It fails when e_n tends to zero.", "note", { runDir: withBroken, log: (m) => said.push(m) })).toMatchObject({ ok: false, error: expect.stringContaining("Missing $ inserted") });
    expect(said.some((m) => m.includes("checked without them"))).toBe(true);
    // the scratch directories are removed
    expect(existsSync(path.join(run, "logs", "tex_check")) ? (await import("node:fs")).readdirSync(path.join(run, "logs", "tex_check")) : []).toEqual([]);
  }, 120_000);
});

describe("the V1 fixer's texts (its wiring is separate: patchFileTexFields is what it checks)", () => {
  it("every TeX text of a patch and a suggested repair, with how it is set", () => {
    const oe = { claim: "c", defects: [{ kind: "other", step_unit: "lem:a/1/1", uses: null, assumed_on: null, applied_at: null, detail: "w" }], why: { objects: ["$n=1$"], consequence: "y" }, fix: "f", gives_up: null };
    const ops = [
      { op: "replace", unit: "lem:a/1/1", tex: "E" },
      { op: "replace", unit: "lem:a/proof/1/1", tex: "I" },
    ];
    const fields = patchFileTexFields({
      patches: [{ node: "lem:a", corrected_statement: "S", ops, proof_note: "P", owner_explanation: oe }],
      unfixable: [{ node: "thm:b", reason: "U", owner_explanation: oe, suggested_repair: { corrected_statement: "SS", ops: [{ op: "replace", unit: "thm:b/1/1", tex: "T" }], proof_note: "PP", given_up: "G" } }],
    } as never);
    const by = (text: string) => fields.filter((f) => f.text === text).map((f) => `${f.kind} ${f.where}`);
    // Each op's TeX in its unit's context; the corrected statement it derives as a statement.
    expect(by("S")).toEqual(['statement the patch for "lem:a": its corrected statement (derived from its ops)']);
    expect(by("E")).toEqual(['statement the patch for "lem:a": ops[0] (replace)']);
    expect(by("I")).toEqual(['step the patch for "lem:a": ops[1] (replace)']);
    // An amended printed proof (the patch has a proof op) is the paper's own text around the ops: not
    // compiled whole; a proof note written whole (no proof op: the suggestion) is.
    expect(by("P")).toEqual([]);
    expect(by("PP")).toEqual(['note the suggested repair for "thm:b": its proof_note']);
    expect(by("y")).toEqual(['note the owner_explanation for "lem:a" `why.consequence`', 'note the owner_explanation for "thm:b" `why.consequence`']);
    expect(by("w")).toEqual(['note the owner_explanation for "lem:a" `defects[0].detail`', 'note the owner_explanation for "thm:b" `defects[0].detail`']);
    expect(by("U")).toEqual(['note the unfixable entry for "thm:b": its reason']);
    expect(by("SS")).toEqual(['statement the suggested repair for "thm:b": its corrected statement (derived from its ops)']);
    expect(by("T")).toEqual(['statement the suggested repair for "thm:b": ops[0] (replace)']);
    // what a suggestion gives up is its note's field (checked with the note), not a text of its own
    expect(by("G")).toEqual([]);
  });
});

describe("a replacement of a unit the paper cuts across an environment", () => {
  // a proof holding a nested lemma: one unit opens the lemma's proof, a later one closes it
  const printed = String.raw`\begin{lemma}\label{l} $x\le1$. \end{lemma}\begin{proof} It holds.`;
  it("the environments a text leaves open or closes, read as the balance scanner reads (comments, \\verb, a row break \\\\end)", () => {
    expect(envImbalance(printed)).toEqual({ close: [], open: ["proof"] });
    expect(envImbalance(String.raw`a \end{proof} b \begin{x}\end{x}`)).toEqual({ close: ["proof"], open: [] });
    // nesting order: closed in the order met (innermost first), opened innermost last
    expect(envImbalance(String.raw`x.\end{proof}\end{lemma}\end{proof} Next. \begin{lemma}[A]\begin{proof} It`)).toEqual({ close: ["proof", "lemma", "proof"], open: ["lemma", "proof"] });
    expect(envImbalance(String.raw`$a \\end{x}$ % \begin{proof}` + "\n" + String.raw`\verb|\end{lemma}| done`)).toEqual({ close: [], open: [] });
  });
  it("is checked with the same environments closed around it, in their nesting order; any other imbalance is left for the compiler", () => {
    const fixed = String.raw`\begin{lemma}\label{l} $x\le2$. \end{lemma}\begin{proof} It holds, as shown.`;
    expect(balancedLikeUnit(fixed, printed)).toBe(`${fixed}\\end{proof}`);
    const both = String.raw`x.\end{proof}\end{lemma} Next. \begin{lemma}\begin{proof} It`;
    expect(balancedLikeUnit(both.replace("Next", "Then"), both)).toBe(String.raw`\begin{lemma}\begin{proof}` + both.replace("Next", "Then") + String.raw`\end{proof}\end{lemma}`);
    // a replacement that loses an environment the printed unit closes is not patched over
    const lost = String.raw`\begin{lemma} $x\le2$. \begin{proof} It holds.`;
    expect(balancedLikeUnit(lost, printed)).toBe(lost);
    // a balanced unit, and no printed text: unchanged
    expect(balancedLikeUnit("$x$", "$y$")).toBe("$x$");
    expect(balancedLikeUnit(fixed, null)).toBe(fixed);
    // the patch file's op is set balanced like the text it replaces
    const file = { patches: [{ node: "thm:a", ops: [{ op: "replace" as const, unit: "thm:a/proof/1/1", tex: fixed }], corrected_statement: null, proof_note: null }], unfixable: [] };
    const fields = patchFileTexFields(file as never, (op) => (op.unit === "thm:a/proof/1/1" ? printed : null));
    expect(fields.find((f) => f.where.includes("ops[0]"))?.text).toBe(`${fixed}\\end{proof}`);
  });
  it("a replacement that does not keep the printed text's crossing environments is a violation, never compiled alone", async () => {
    // dropping every marker (balanced on its own), and the same markers in another order
    const dropped = String.raw`$x\le2$. It holds.`;
    expect(envKeepProblem(dropped, printed)).toBe(String.raw`does not keep the environments of the printed text it replaces: that text closes or opens without its other end \begin{proof}, the replacement none — a replacement keeps those unmatched \begin / \end markers, in the same order (the paper's text around it holds their other ends), and changes the text between them.`);
    const unit = String.raw`x.\end{lemma} \begin{proof} y`;
    expect(envKeepProblem(String.raw`\begin{proof} y \end{lemma}`, unit)).toContain(String.raw`the replacement \begin{proof} \end{lemma}`);
    expect(envKeepProblem(String.raw`z.\end{lemma} \begin{proof} y`, unit)).toBeNull();
    expect(envKeepProblem(dropped, "$x$")).toBeNull();
    const file = { patches: [{ node: "thm:a", ops: [{ op: "replace" as const, unit: "thm:a/proof/1/1", tex: dropped }], corrected_statement: null, proof_note: null }], unfixable: [] };
    const fields = patchFileTexFields(file as never, () => printed);
    const op = fields.find((f) => f.where.includes("ops[0]"))!;
    expect(op.problem).toMatch(/^does not keep the environments/u);
    const run = await mkdtemp(path.join(os.tmpdir(), "texcheck-keep-"));
    dirs.push(run);
    expect(await texFieldViolations([op], { runDir: run })).toEqual([`the patch for "thm:a": ops[0] (replace) ${op.problem}`]);
  });
  it("a range op: compared with the printed text of its run of units", () => {
    const proof = "We need a bound.\n\\begin{lemma}\\label{lem:in}\nThe event $E$ has probability at least $1/2$.\n\\end{lemma}\n\\begin{proof}\nThe event $E$ holds when $X \\le 1$. Hence it has probability $1/2$.\n\\end{proof}\nThe theorem follows.";
    const flat = `\\begin{theorem}\\label{thm:a}It holds.\\end{theorem}\n\\begin{proof}\n${proof}\n\\end{proof}\n`;
    const units = PaperUnits.parse(flat, { envs: [{ id: "thm:a", envName: "theorem", body: "It holds.", proof, lines: { file: "main.tex", from: 1, to: 1 } }] } as never);
    // the run "\begin{lemma} … 1/2$." … "\end{lemma} \begin{proof} The event … X \le 1$." leaves the inner proof open
    const run = units.textOfRun("thm:a/proof/1/2", "thm:a/proof/1/3")!;
    expect(run).toBe("\\begin{lemma}\\label{lem:in}\nThe event $E$ has probability at least $1/2$.\n\\end{lemma}\n\\begin{proof}\nThe event $E$ holds when $X \\le 1$.");
    expect(units.textOfRun("thm:a/proof/1/3")).toBe(units.textById("thm:a/proof/1/3"));
    expect(units.textOfRun("thm:a/proof/1/3", "thm:a/proof/1/2")).toBeNull();
    const tex = run.replace("1/2", "1/4");
    const file = { patches: [{ node: "thm:a", ops: [{ op: "replace" as const, unit: "thm:a/proof/1/2", to: "thm:a/proof/1/3", tex }], corrected_statement: null, proof_note: null }], unfixable: [] };
    const fields = patchFileTexFields(file as never, (op) => units.textOfRun(op.unit, op.to));
    expect(fields.find((f) => f.where.includes("ops[0]"))?.text).toBe(`${tex}\\end{proof}`);
  });
  it.skipIf(!hasPdflatex)("the balanced fragment compiles as a step; the unbalanced one does not", async () => {
    const run = await paperRun(PAPER.replace("\\newtheorem{theorem}{Theorem}", "\\newtheorem{theorem}{Theorem}\\newtheorem{lemma}{Lemma}"));
    const printedUnit = "\\end{lemma}\n\\begin{proof}\nThe event $E$ holds when $X \\le 1$.";
    const tex = "\\end{lemma}\n\\begin{proof}\nThe event $E$ holds when $X \\le 1$, by Markov's inequality.";
    expect(await checkTexFragment(balancedLikeUnit(tex, printedUnit), "step", { runDir: run })).toEqual({ ok: true });
    expect(await checkTexFragment(tex, "step", { runDir: run })).toMatchObject({ ok: false });
  }, 60_000);
});

describe("the paper's macros defined in its body", () => {
  it("are read with their arguments, in order, and only from the body", () => {
    const flat = String.raw`\documentclass{article}\newcommand{\pre}{x}\begin{document}
Text \newcommand{\fp}[2]{z_{1,#1}(#2)} more \renewcommand{\sp}[2]{z_{2,#1}(#2)}
\providecommand\opt[1][a]{#1} \DeclareMathOperator*{\argmax}{arg\,max} \def\radius{2.6} \gdef\pair#1#2{(#1,#2)}
\end{document}`;
    expect(bodyDefinitions(flat).split("\n")).toEqual([
      String.raw`\makeatletter`,
      String.raw`\newcommand{\fp}[2]{z_{1,#1}(#2)}`,
      String.raw`\renewcommand{\sp}[2]{z_{2,#1}(#2)}`,
      String.raw`\providecommand\opt[1][a]{#1}`,
      String.raw`\DeclareMathOperator*{\argmax}{arg\,max}`,
      String.raw`\def\radius{2.6}`,
      String.raw`\gdef\pair#1#2{(#1,#2)}`,
      String.raw`\makeatother`,
    ]);
    expect(bodyDefinitions("no document")).toBe("");
  });
  // The finding: a symbol reading placed in the introduction used \man, which the paper defines sections later.
  it("give a note that uses them local definitions, closed under use", () => {
    const flat = String.raw`\begin{document}\newcommand{\man}{\ensuremath{\mathrm{man}}}\newcommand{\Vm}{V_\man}\DeclareMathOperator{\op}{op}\def\a@b{x}\end{document}`;
    const defs = bodyDefinitionList(flat);
    expect(withLocalBodyDefinitions(String.raw`$G=(\Vm,E)$`, defs)).toBe(String.raw`{\providecommand{\man}{\ensuremath{\mathrm{man}}}\providecommand{\Vm}{V_\man}$G=(\Vm,E)$}`);
    expect(withLocalBodyDefinitions(String.raw`$\op(x)$ and \a@b, \mantissa`, defs)).toBe(String.raw`$\op(x)$ and \a@b, \mantissa`);
    // a \def (and a \gdef, which would leave the group) is not carried
    expect(withLocalBodyDefinitions(String.raw`$\x$`, bodyDefinitionList(String.raw`\begin{document}\gdef\x{A}\end{document}`))).toBe(String.raw`$\x$`);
  });
  it("take a definition inside another as part of it, skip a \\csname name, and keep each name once", () => {
    const flat = String.raw`\begin{document}
\newcommand{\setr}[1]{\def\r{#1}} \expandafter\def\csname foo\endcsname{1}
\begin{proof}\newcommand{\T}{a}\end{proof}\begin{proof}\newcommand{\T}{b}\end{proof} \def\@foo{x}
\end{document}`;
    expect(bodyDefinitions(flat).split("\n")).toEqual([
      String.raw`\makeatletter`,
      String.raw`\newcommand{\setr}[1]{\def\r{#1}}`,
      String.raw`\newcommand{\T}{a}`,
      String.raw`\def\@foo{x}`,
      String.raw`\makeatother`,
    ]);
  });
});

describe("the reply schemas: every TeX-bearing string is printable ASCII", () => {
  const pattern = (x: unknown): unknown => (x as { pattern?: string }).pattern;
  it("the pattern, and the fields that carry it", () => {
    expect(ASCII_TEX_PATTERN).toBe("^[\\x20-\\x7E\\n\\t]*$");
    expect(new RegExp(ASCII_TEX_PATTERN, "u").test("a $\\le$ b\n\tc")).toBe(true);
    expect(new RegExp(ASCII_TEX_PATTERN, "u").test("a ≤ b")).toBe(false);
    const oe = (OWNER_EXPLANATION_JSON as { properties: Record<string, { items?: { properties: Record<string, unknown> }; properties?: Record<string, { items?: unknown }> }> }).properties;
    for (const k of ["claim", "fix", "gives_up"]) expect(pattern(oe[k])).toBe(ASCII_TEX_PATTERN);
    for (const k of ["uses", "assumed_on", "applied_at", "detail"]) expect(pattern(oe.defects!.items!.properties[k])).toBe(ASCII_TEX_PATTERN);
    expect(pattern(oe.why!.properties!.consequence)).toBe(ASCII_TEX_PATTERN);
    expect(pattern(oe.why!.properties!.objects!.items)).toBe(ASCII_TEX_PATTERN);
    const node = (V15_NODE_REPLY as { properties: Record<string, { anyOf?: Array<{ properties?: Record<string, unknown> }> }> }).properties;
    // (the two the zod schema refuses empty: the same characters, at least one)
    const nonEmpty = ASCII_TEX_PATTERN.replace("]*$", "]+$");
    expect(pattern(node.reading!.anyOf![0]!.properties!.reading)).toBe(nonEmpty);
    expect(pattern(node.bookkeeping_assumption!.anyOf![0]!.properties!.condition)).toBe(nonEmpty);
    const sym = (V15_SYMBOL_REPLY as { properties: Record<string, { anyOf?: Array<{ properties?: Record<string, unknown> }> }> }).properties;
    expect(pattern(sym.reading!.anyOf![0]!.properties!.reading)).toBe(nonEmpty);
    expect(pattern(sym.fix!.anyOf![0]!.properties!.type)).toBe(ASCII_TEX_PATTERN);
    expect(pattern(sym.fix!.anyOf![0]!.properties!.def)).toBe(ASCII_TEX_PATTERN);
    const patch = (PATCH_REPLY_JSON_SCHEMA as { properties: { patches: { items: { properties: Record<string, unknown> } } } }).properties.patches.items.properties;
    for (const k of ["proof_note", "reason"]) expect(pattern(patch[k])).toBe(ASCII_TEX_PATTERN);
    // a repair's readings are TeX texts too (they were typed as an id list)
    expect(pattern((patch.readings as { anyOf: Array<{ items?: unknown }> }).anyOf[0]!.items)).toBe(ASCII_TEX_PATTERN);
    // The one op (a replacement): its TeX is ASCII; a unit id is a locator.
    const op = (patch.ops as { items: { properties: Record<string, unknown> } }).items;
    expect(Object.keys(op.properties).sort()).toEqual(["op", "tex", "to", "unit"]);
    expect(pattern(op.properties.tex)).toBe(nonEmpty); // (zod refuses an empty replacement)
    expect(pattern(op.properties.unit)).toBeUndefined();
  });
});

const NODE = (over: Partial<V15NodeVerdict>): V15NodeVerdict =>
  ({ id: "thm:a", faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "d", witness: null, bookkeeping_assumption: null, reading: null, ...over }) as V15NodeVerdict;

describe.skipIf(!hasPdflatex)("each producer rejects a fragment that does not compile, with the compiler's line", () => {
  it("V1.5 referee: the detail (the paper prints it), the reading, the bookkeeping condition", async () => {
    const run = await paperRun();
    const v = await refereeTexViolations([NODE({ reading: { reading: "h_0 is fixed", evidence: "e" }, bookkeeping_assumption: { condition: "$c > 0$", reason: "r" }, detail: "plain e_n detail" })], { runDir: run });
    expect(v).toHaveLength(2);
    expect(v[0]).toMatch(/^node "thm:a": its detail does not compile: Missing \$ inserted/u);
    expect(v[1]).toMatch(/^node "thm:a": its reading does not compile: Missing \$ inserted\. .* — the fragment must compile as LaTeX against the paper's preamble\.$/u);
    expect(await refereeTexViolations([NODE({ bookkeeping_assumption: { condition: "c_0 > 0", reason: "r" } })], { runDir: run })).toEqual([expect.stringContaining('node "thm:a": its bookkeeping_assumption does not compile: Missing $ inserted')]);
  });
});

describe("mathModeHint", () => {
  it("names a `_` outside math for a Missing $ error; nothing for one inside math or a \\ref argument", () => {
    expect(mathModeHint("Missing $ inserted.", "the core wires it via `depends_on` here")).toContain("a `_` outside math, at …");
    expect(mathModeHint("Missing $ inserted.", "bound $x_1<\\infty$ by Lemma~\\ref{lemma:bounded_RR}")).toBe("");
    expect(mathModeHint("Undefined control sequence.", "a_b")).toBe("");
    // legal `_` is skipped, so the hint names the real one; the snippet is the text's own
    const m = (t: string): string => mathModeHint("Missing $ inserted.", t);
    expect(m("costs \\$5 and $y_1$ fine")).toBe("");
    expect(m("\\begin{equation} x_1 = 2 \\end{equation} and depends_on")).toContain("…quation} and depends_on…");
    expect(m("see \\citep[p.~3]{smith_2020}, \\verb|a_b| % note a_b\nok")).toBe("");
  });
});

describe("withoutMissingInputs", () => {
  it("drops an \\input of a file the bundle does not ship and keeps one it does", () => {
    const dir = mkdtempSync(path.join(os.tmpdir(), "vs-pre-"));
    writeFileSync(path.join(dir, "macros.tex"), "\\newcommand{\\x}{x}\n");
    const pre = "\\documentclass{article}\n\\input{tcilatex}\n\\input{macros}\n";
    expect(withoutMissingInputs(pre, dir)).toBe("\\documentclass{article}\n\n\\input{macros}\n");
    rmSync(dir, { recursive: true, force: true });
  });
});

// The finding: a fixer's proof note named \ref{lemma-2} (the core id) for a lemma the paper leaves unlabelled.
describe("references in a patch text", () => {
  it("name only labels the paper or the patch file defines", () => {
    const flat = String.raw`\newcommand{\lbl}[1]{\label{#1}}\begin{document}\begin{lemma}\label{lem:a}x\end{lemma}\section{S}\lbl{s:b}\end{document}`;
    const unknown = unknownRefs(flat, [String.raw`a new block \label{cor:new}`]);
    expect(unknown(String.raw`By Lemma~\ref{lemma-2} and \ref{lem:a}, \eqref{s:b}, \cref{cor:new,lem:a}.`)).toEqual(["lemma-2"]);
    // a label the paper refers to itself (set by a package's own macro) is not refused
    expect(unknownRefs(String.raw`\begin{document}see (\ref{degreecons})\end{document}`, [])(String.raw`by (\ref{degreecons})`)).toEqual([]);
  });
});
