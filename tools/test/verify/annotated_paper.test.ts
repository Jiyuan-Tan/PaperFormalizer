import { existsSync, readFileSync } from "node:fs";
import { cp, mkdir, mkdtemp, readdir, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { findExecutable } from "../../src/shared/program.js";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { verifyRunDir } from "../../src/paths.js";
import { createVerifyInitialState } from "../../src/state.js";
import type { StateJson } from "../../src/types.js";
import {
  VS_BLOCK_MARKER,
  VS_PREAMBLE_BLOCK,
  documentClassOf,
  injectPreamble,
  preambleOf,
  loadsXcolor,
  safeInsertionPoint,
  safeSpan,
  nonAsciiProblem,
  struckMacro,
  verbatimLike,
} from "../../src/verify/annotate_tex.js";
import { texMathProblems, type OwnerExplanation } from "../../src/verify/owner_text.js";
import { applyEdits, compileTex, macroArity, planAnnotations, type AnnotationInput, type CompileTex } from "../../src/verify/annotated_paper.js";
import { annotateRun, annotationInput } from "../../src/verify/annotate_run.js";
import { sha256File } from "../../src/verify/core_hash.js";
import { applyPatchFile, PatchFileSchema } from "../../src/verify/patches.js";
import { materializeRefCore, RefCoreSchema } from "../../src/verify/ref_core.js";
import { makeStageV6 } from "../../src/verify/stage_v6_report.js";
import { buildEnvsJson, writeEnvsArtifacts } from "../../src/verify/tex_envs.js";
import { VERIFY_FILES, type V15Review, type VerifyFinding, type VerifyState } from "../../src/verify/types.js";

const FIXTURE = path.join(path.dirname(fileURLToPath(import.meta.url)), "fixtures", "annot_paper");
const QID = "annot_paper";
const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

const novel = { flag: true, justification: "the paper's" };
const REF = {
  qid: QID,
  target_estimand: "the rate",
  symbols: [],
  assumptions: [
    { id: "ass:overlap", source: { env: "thm:rate", sentences: [1, 1] }, novel },
    { id: "ass:bounded", source: { env: "lem:bound", sentences: [1, 1] }, novel },
    { id: "ass:indep", source: { env: "thm:clt", sentences: [1, 1] }, novel },
  ],
  definitions: [],
  statements: [
    { id: "thm:rate", kind: "theorem", env: "thm:rate", depends_on: ["ass:overlap"], hypotheses: ["ass:overlap"] },
    { id: "lem:bound", kind: "lemma", env: "lem:bound", depends_on: ["ass:bounded"], hypotheses: ["ass:bounded"] },
    { id: "thm:clt", kind: "theorem", env: "thm:clt", depends_on: ["ass:indep"], hypotheses: ["ass:indep"] },
    { id: "prop:mono", kind: "proposition", env: "prop:mono" },
    { id: "thm:disp", kind: "theorem", env: "thm:disp" },
  ],
};

const PATCHES = {
  key_results: ["thm:rate"],
  key_contribution: "the rate",
  patches: [
    {
      node: "thm:rate",
      corrected_statement: "Assume the propensity score is bounded away from zero. The estimator converges at rate $n^{-1/3}$. It is efficient.",
      ops: [{ op: "replace" as const, unit: "thm:rate/1/2", tex: "The estimator converges at rate $n^{-1/3}$." }],
      proof_note: "the bias term is of order $h^2$",
    },
    {
      node: "lem:bound",
      // the hypothesis added by restating the sentence that states the lemma's hypotheses
      corrected_statement: "Suppose $X$ is bounded and measurable. Then $E[X]$ exists.",
      ops: [{ op: "replace" as const, unit: "lem:bound/1/1", tex: "Suppose $X$ is bounded and measurable." }],
      proof_note: "integrate",
    },
    {
      node: "prop:mono",
      corrected_statement: "The map $h$ is strictly increasing on $[0,1]$.",
      ops: [{ op: "replace" as const, unit: "prop:mono/1/1", tex: "The map $h$ is strictly increasing on $[0,1]$." }],
      proof_note: "unchanged",
    },
    {
      node: "thm:disp",
      corrected_statement: "Let $Y$ be given. We have\n\\[ T \\to N(0,2). \\quad \\text{Also } S \\to 0. \\]\nas $n \\to \\infty$.",
      ops: [{ op: "replace" as const, unit: "thm:disp/1/2", tex: "We have\n\\[ T \\to N(0,2). \\quad \\text{Also } S \\to 0. \\]\nas $n \\to \\infty$." }],
      proof_note: "variance two",
      // narrowing-gate fields: an owner-accepted weakening
      accepted_weakening: true,
      given_up: "the unit limiting variance",
    },
  ],
  unfixable: [
    {
      node: "thm:clt",
      reason: "no CLT holds without a moment condition",
      suggested_repair: {
        corrected_statement: "Assume the sample is independent with finite variance. The statistic $T_n$ is asymptotically normal.",
        ops: [{ op: "replace" as const, unit: "thm:clt/1/1", tex: "Assume the sample is independent with finite variance." }],
        proof_note: "Lindeberg",
        given_up: "the moment-free claim",
      },
    },
  ],
};

const PAPER_ERRORS = {
  "thm:rate": { detail: "The rate is $n^{-1/3}$, not $n^{-1/2}$.", witness: "Take $X_i \\sim U[0,1]$ with $e(x)=x$; the MSE is of order $n^{-2/3}$." },
  "lem:bound": { detail: "[F2.5 reviewer] [statement-wrong] E[X] needs measurability.", witness: "a bounded non-measurable X" },
  "prop:mono": {
    detail: "[F2.5 reviewer] Increasing may mean weakly or strictly.\nReading(s) the referee pinned for this statement, to be written into it: h strictly increasing.",
    witness: null,
    kind: "clarification" as const,
  },
  "thm:disp": { detail: "The limiting variance is 2.", witness: "$T = \\sqrt{2} Z$" },
  "thm:clt": { detail: "The CLT fails without finite variance.", witness: "Cauchy samples" },
};

const FINDINGS: VerifyFinding[] = [
  { node: "thm:clt", stage: "V1.5", kind: "refuted", detail: "The CLT fails without finite variance.", witness: "Cauchy samples", at: "2026-09-24T00:00:00.000Z" },
];

/** A run whose V1 / V1.5 records annotate the fixture paper (an early stop, so no Lean is needed). */
async function seedRun(opts: { source?: string } = {}): Promise<{ repoRoot: string; runDir: string; state: StateJson }> {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-annot-"));
  tmpDirs.push(repoRoot);
  const runDir = verifyRunDir(repoRoot, QID);
  const src = path.join(runDir, "source");
  await mkdir(runDir, { recursive: true });
  await cp(opts.source ?? FIXTURE, src, { recursive: true });
  const { envs, flat } = await buildEnvsJson(src, "main.tex");
  await writeEnvsArtifacts(runDir, envs, flat);
  const ref = RefCoreSchema.parse(REF);
  const { core: transcribed, violations } = materializeRefCore(ref, envs, flat.text);
  expect(violations).toEqual([]);
  const { core } = applyPatchFile(transcribed, PatchFileSchema.parse(PATCHES));
  core.assumptions.push({
    id: "ass:pin-1",
    kind: "regularity",
    condition: "$n \\ge 2$ with $\\mu \\in \\mathbb{R}$",
    bookkeeping: { flag: true, added_by: "V1.5", reason: "pins reading of ass:overlap: the proof uses it" },
  } as Core["assumptions"][number]);
  core.statements.find((s) => s.id === "thm:rate")!.depends_on.push("ass:pin-1");
  const write = (rel: string, v: unknown): Promise<void> => writeFile(path.join(runDir, rel), JSON.stringify(v, null, 2), "utf8");
  await write("discovery/core_refs.json", REF);
  await write(VERIFY_FILES.coreTranscribed, transcribed);
  await write(VERIFY_FILES.coreJson, core);
  await write(VERIFY_FILES.patches, PATCHES);
  const state = createVerifyInitialState(QID, {
    phase: "v6",
    source: { input: "main.tex", main_file: "main.tex", sha256: "deadbeef" },
    targets: null,
    core_sha256: await sha256File(path.join(runDir, VERIFY_FILES.coreJson)),
    transcribed_sha256: await sha256File(path.join(runDir, VERIFY_FILES.coreTranscribed)),
    v1_rounds: 1,
    v1_5_rounds: 1,
    findings: FINDINGS,
    report_path: null,
    paper_errors: PAPER_ERRORS,
  } as never);
  state.stage_completed = "1.5";
  return { repoRoot, runDir, state };
}

const passed: CompileTex = async () => ({ status: "passed", tool: "pdflatex", pdf: "main.pdf", log_tail: "Output written on main.pdf", reason: "" });

async function runV6(run: { repoRoot: string; runDir: string; state: StateJson }, compile: CompileTex = passed): Promise<void> {
  const stage = makeStageV6({ collectLeanEvidence: async () => { throw new Error("no Lean on an early stop"); }, compileTex: compile });
  const res = await stage({
    repoRoot: run.repoRoot,
    qid: QID,
    runDir: run.runDir,
    state: run.state,
    deps: { runCodex: (() => { throw new Error("V6 never calls a model"); }) as never },
    dryRun: true,
    log: () => {},
  });
  expect(res.status).toBe("completed");
}

const read = (runDir: string, rel: string): Promise<string> => readFile(path.join(runDir, rel), "utf8");

/** Undo the annotation: drop the preamble additions and every blue / note group, unwrap red. */
function unannotate(tex: string): string {
  const group = (s: string, at: number): number => {
    let d = 0;
    for (let i = at; i < s.length; i += 1) {
      if (s[i] === "\\") { i += 1; continue; }
      if (s[i] === "{") d += 1;
      else if (s[i] === "}" && --d === 0) return i + 1;
    }
    throw new Error("unbalanced");
  };
  let out = tex.replace(/\n\\usepackage\{xcolor\}% added by TheoremChecker\n/, "").replace(/% TheoremChecker annotation macros[\s\S]*?% end of TheoremChecker annotation macros\n/, "");
  // a proof block inserted on its own line takes its newline with it
  for (const macro of ["\\vsProof", "\\vsProposedProof"]) {
    for (let at = out.indexOf(`${macro}{`); at >= 0; at = out.indexOf(`${macro}{`)) {
      let end = group(out, at + macro.length);
      if (out[at - 1] === "\n" && out[end] === "\n") end += 1;
      out = out.slice(0, at) + out.slice(end);
    }
  }
  for (const macro of ["\\vsReading", " \\vsCorrected", " \\vsClarified", " \\vsNote"]) {
    for (let at = out.indexOf(macro); at >= 0; at = out.indexOf(macro)) out = out.slice(0, at) + out.slice(group(out, at + macro.length));
  }
  for (const wrap of ["\\vsOriginal{", "\\vsStep{"]) {
    for (let at = out.indexOf(wrap); at >= 0; at = out.indexOf(wrap)) {
      const end = group(out, at + wrap.length - 1);
      out = out.slice(0, at) + out.slice(at + wrap.length, end - 1) + out.slice(end);
    }
  }
  return out;
}

describe("annotated paper (V6)", () => {
  it("marks each finding at its sentence, in the main file and the \\input-ed one, and changes nothing else", async () => {
    const run = await seedRun();
    await runV6(run);
    const main = await read(run.runDir, "annotated/main.tex");
    const sec = await read(run.runDir, "annotated/sec/results.tex");

    // error with a repair: only the sentence that differs is red, the correction follows in blue; the
    // note after the whole statement (2026-09-25)
    expect(main).toContain(
      "Assume the propensity score is bounded away from zero. % the paper's own comment\n" +
        "\\vsOriginal{The estimator converges at rate $n^{-1/2}$.} \\vsCorrected{The estimator converges at rate $n^{-1/3}$.} It is efficient. " +
        "\\vsNote{The rate is $n^{-1/3}$, not $n^{-1/2}$. Counterexample: Take $X_i \\sim U[0,1]$ with $e(x)=x$; the MSE is of order $n^{-2/3}$.}",
    );
    // a hypothesis added by restating the sentence that states the hypotheses: that sentence red, its
    // restatement blue, never an insertion mark (replacement-only repairs, 2026-09-26)
    expect(main).toContain(
      "\\vsOriginal{Suppose $X$ is bounded.} \\vsCorrected{Suppose $X$ is bounded and measurable.} Then $E[X]$ exists. " +
        "\\vsNote{E[X] needs measurability. Counterexample: a bounded non-measurable X.}",
    );
    expect(main).not.toContain("\\vsAdded");
    // a pinned reading still standing: a note after the statement, no red
    // (no proof located: the proof note right after the result and its clarification, saying so — 2026-09-26)
    expect(main).toContain("\\end{thm}\\vsReading{$n \\ge 2$ with $\\mu \\in \\mathbb{R}$ (the reading of one of its hypotheses)}\n\\vsProof{\\textit{(the paper's proof could not be located; the corrected proof is given here)} \\vsLine the bias term is of order $h^2$}");
    // refuted, no accepted repair: the asserting sentence red, the suggestion and its weakening in the note
    expect(sec).toContain(
      "Assume the sample is independent. \\vsOriginal{The statistic $T_n$ is asymptotically normal.} \\vsNote{The CLT fails without finite variance. " +
        "Counterexample: Cauchy samples. \\vsLine \\textbf{Suggested repair (not applied):} restate it as: Assume the sample is independent with finite variance. " +
        "The statistic $T_n$ is asymptotically normal. \\vsLine\\textbf{Gives up:} The moment-free claim. (This fix weakens the result.)}",
    );
    // clarification: ambiguous sentence red, clarified blue, the finding and the pinned reading
    expect(sec).toContain(
      "\\vsOriginal{The map $h$ is increasing on its domain.} \\vsClarified{The map $h$ is strictly increasing on $[0,1]$.} " +
        "\\vsNote{Ambiguous: Increasing may mean weakly or strictly. Clarification: h strictly increasing.}",
    );
    // a period inside display math is no sentence boundary, and a display followed by lowercase text
    // continues its sentence: the whole sentence is red, and blue
    expect(sec).toContain(
      "\\vsOriginal{We have\n\\[ T \\to N(0,1). \\quad \\text{Also } S \\to 0. \\]\nas $n \\to \\infty$.} \\vsCorrected{We have\n\\vsFit{T \\to N(0,2). \\quad \\text{Also } S \\to 0.}\nas $n \\to \\infty$.} " +
        "\\vsNote{The limiting variance is 2. Counterexample: $T = \\sqrt{2} Z$. \\vsLine\\textbf{Gives up:} The unit limiting variance. (This fix weakens the result.)}",
    );
    // no weakening line where the run records none
    expect(main).not.toContain("weakens");
    // labels untouched, and removing the annotation gives back the paper byte for byte
    for (const l of ["thm:rate", "lem:bound"]) expect(main.split(`\\label{${l}}`).length).toBe(2);
    expect(unannotate(main)).toBe(await read(run.runDir, "source/main.tex"));
    expect(unannotate(sec)).toBe(await read(run.runDir, "source/sec/results.tex"));

    const md = await read(run.runDir, "annotated/ANNOTATIONS.md");
    expect(md).toContain("## Annotations (10)");
    // every applied patch's proof note, after the statement (the fixture prints no proofs)
    expect(md).toMatch(/\| `thm:rate` \| main\.tex:\d+ \| corrected proof \| after-env \(no proof located\) \|/);
    expect(md).toMatch(/\| `thm:rate` \| main\.tex:13 \| error \(repaired\) \| units \|/);
    expect(md).toMatch(/\| `lem:bound` \| main\.tex:17 \| error \(repaired\) \| units \|/);
    expect(md).toMatch(/\| `thm:clt` \| sec\/results\.tex:2 \| error \(not repaired\) \| units \|/);
    expect(md).toMatch(/\| `prop:mono` \| sec\/results\.tex:6 \| clarification \|/);
    expect(md).toMatch(/\| `thm:disp` \| sec\/results\.tex:10 \| error \(repaired\) \| units \| The limiting variance is 2\..* .*\(the fix weakens the result\) \|/);
    expect(md).toMatch(/\| `thm:rate` \| main\.tex:14 \| clarification \(reading\) \| after-env \|/);
    expect(md).toContain("## Unlocated (0)");
    expect(md).toContain("Compiled with pdflatex: `main.pdf`.");
    // the preamble: xcolor after \documentclass, the macros before \begin{document}
    expect(main.startsWith("\\documentclass{article}\n\\usepackage{xcolor}% added by TheoremChecker\n")).toBe(true);
    expect(main.indexOf(VS_BLOCK_MARKER)).toBeLessThan(main.indexOf("\\begin{document}"));
    expect(main.indexOf(VS_BLOCK_MARKER)).toBeGreaterThan(main.indexOf("\\newtheorem{prop}"));
    // each part is a block laid out for reading: its bold label on its own line, the content indented below
    const macro = (name: string): string => main.split("\n").find((l) => l.startsWith(`\\newcommand{\\${name}}`)) ?? "";
    for (const [name, colour, font, label] of [["vsOriginal", "vsRed", "", "Original:"], ["vsCorrected", "vsBlue", "", "Corrected:"], ["vsClarified", "vsBlue", "", "Clarified statement:"], ["vsNote", "vsNote", "\\normalfont\\small", "TheoremChecker:"], ["vsReading", "vsNote", "\\normalfont\\small", "Clarification:"], ["vsReadingOwner", "vsNote", "\\normalfont\\small", "Clarification (author):"]] as const) {
      expect(macro(name)).toBe(`\\newcommand{\\${name}}[1]{\\vsBlock{${colour}}{${font}}{${label}}{#1}}`);
    }
    expect(macro("vsReadingSymbol")).toBe("\\newcommand{\\vsReadingSymbol}[2]{\\vsBlock{vsNote}{\\normalfont\\small}{Clarification (symbol #1):}{#2}}");
    expect(macro("vsBlock")).toContain("\\par\\smallskip{\\noindent\\color{#1}#2\\textbf{#3}\\par\\nopagebreak{\\leftskip=\\vsIndent");
    expect(macro("vsBreak")).toBe("\\newcommand{\\vsBreak}{\\ifhmode\\ifinner\\quad\\else\\unskip\\par\\fi\\fi}");

    // the report points at it
    const report = await read(run.runDir, VERIFY_FILES.reportMd);
    expect(report).toContain("Annotated paper: `annotated/main.tex` (10 annotation(s), 0 unlocated; index `annotated/ANNOTATIONS.md`); PDF: `annotated/main.pdf`");
    const json = JSON.parse(await read(run.runDir, VERIFY_FILES.reportJson)) as { annotated: { tex: string; pdf: string; annotations: number } };
    expect(json.annotated).toMatchObject({ tex: "annotated/main.tex", pdf: "annotated/main.pdf", annotations: 10 });
  });

  it("a repaired error shows the fixer's note; an error with no fixer note shows the referee's plain finding; no note is read from the ledger", async () => {
    const E: OwnerExplanation = { claim: "The estimator is claimed to converge at rate $n^{-1/2}$.", defects: [{ kind: "out_of_domain", step_unit: "thm:rate/1/2", uses: "a second-order kernel bound", assumed_on: "smooth propensities", applied_at: "$e(x) = x$", detail: null }], why: { objects: ["$e(x) = x$"], consequence: "the mean squared error is of order $n^{-2/3}$" }, fix: "The corrected statement gives the rate $n^{-1/3}$.", gives_up: null };
    const R: OwnerExplanation = { claim: "A ledger note's claim.", defects: [{ kind: "other", step_unit: "thm:rate/1/2", uses: null, assumed_on: null, applied_at: null, detail: "A ledger note's account" }], why: { objects: ["$n = 1$"], consequence: "a ledger note's consequence" }, fix: "A ledger note's fix.", gives_up: null };
    const run = await seedRun();
    const patches = { ...PATCHES, patches: PATCHES.patches.map((p) => (p.node === "thm:rate" ? { ...p, owner_explanation: E } : p)) };
    await writeFile(path.join(run.runDir, VERIFY_FILES.patches), JSON.stringify(patches, null, 2), "utf8");
    // a note left on the ledger entries by an older writer (no longer part of the ledger's shape)
    run.state.verify!.paper_errors = { ...PAPER_ERRORS, "thm:rate": { ...PAPER_ERRORS["thm:rate"], owner_explanation: R }, "lem:bound": { ...PAPER_ERRORS["lem:bound"], owner_explanation: R } } as never;
    await runV6(run);
    const main = await read(run.runDir, "annotated/main.tex");
    // the repaired thm:rate: the fixer's note, as labelled lines
    expect(main).toContain("\\vsLine\\textbf{Claim:} The estimator is claimed to converge at rate $n^{-1/2}$.");
    expect(main).toContain("\\textbf{What is wrong:} \\vsSub ``The estimator converges at rate $n^{-1/2}$.'' This clause uses a second-order kernel bound");
    expect(main).toContain("\\vsLine\\textbf{Proposed fix:} The corrected statement gives the rate $n^{-1/3}$.");
    // the repaired lem:bound carries no fixer note: the referee's detail and the witness's gist
    expect(main).toContain("\\vsNote{E[X] needs measurability. Counterexample: a bounded non-measurable X.}");
    expect(main).not.toContain("ledger note");
  });

  it("is idempotent: a second V6 run rebuilds the same tree", async () => {
    const run = await seedRun();
    const snapshot = async (): Promise<Record<string, string>> => {
      const out: Record<string, string> = {};
      const walk = async (dir: string, rel: string): Promise<void> => {
        for (const e of await readdir(dir, { withFileTypes: true })) {
          if (e.isDirectory()) await walk(path.join(dir, e.name), `${rel}${e.name}/`);
          else out[`${rel}${e.name}`] = await readFile(path.join(dir, e.name), "utf8");
        }
      };
      await walk(path.join(run.runDir, "annotated"), "");
      return out;
    };
    await runV6(run);
    const first = await snapshot();
    await runV6(run);
    expect(await snapshot()).toEqual(first);
    expect(Object.keys(first).sort()).toEqual(["ANNOTATIONS.md", "main.tex", "sec/results.tex"]);
  });

  it("records a failed or skipped compile in ANNOTATIONS.md and never fails V6", async () => {
    const run = await seedRun();
    const failing: CompileTex = async () => ({ status: "failed", tool: "pdflatex", pdf: null, log_tail: "! Undefined control sequence.\nl.12 \\foo", reason: "pdflatex exited with 1" });
    // the annotated copy alone fails: the unmodified source (compiled in a scratch copy) does not
    await runV6(run, async (a) => (a.dir.startsWith(run.runDir) ? failing(a) : passed(a)));
    const md = await read(run.runDir, "annotated/ANNOTATIONS.md");
    expect(md).toContain("Compiling with pdflatex FAILED (pdflatex exited with 1); the annotated TeX is kept.");
    expect(md).toContain("! Undefined control sequence.");
    expect(await read(run.runDir, VERIFY_FILES.reportMd)).toContain("compiling it failed (see the index)");
    expect(existsSync(path.join(run.runDir, "annotated/main.tex"))).toBe(true);

    // the unmodified source fails the same way: a note, in the index and in the report
    const own = await seedRun();
    await runV6(own, failing);
    const note = "ote: the paper's own source does not compile here (pdflatex: ! Undefined control sequence.); the annotated PDF could not be built — the annotated TeX and the page are unaffected";
    expect(await read(own.runDir, "annotated/ANNOTATIONS.md")).toContain(`N${note}.`);
    expect(await read(own.runDir, VERIFY_FILES.reportMd)).toContain(`; n${note}`);

    await runV6(run, async () => ({ status: "skipped", tool: null, pdf: null, log_tail: "", reason: "no pdflatex or latexmk on PATH" }));
    expect(await read(run.runDir, "annotated/ANNOTATIONS.md")).toContain("Not compiled: no pdflatex or latexmk on PATH.");
    expect(await read(run.runDir, VERIFY_FILES.reportMd)).toContain("not compiled (no TeX compiler on PATH)");

    await runV6(run, async () => { throw new Error("compiler exploded"); });
    expect(await read(run.runDir, VERIFY_FILES.reportMd)).toContain("Annotated paper: not written (compiler exploded).");
  });

  const hasPdflatex = findExecutable("pdflatex", { nativeOnly: true }) !== null;
  it.skipIf(!hasPdflatex)("the annotated fixture compiles with pdflatex", async () => {
    const run = await seedRun();
    await runV6(run, compileTex);
    const md = await read(run.runDir, "annotated/ANNOTATIONS.md");
    expect(md).toContain("Compiled with pdflatex: `main.pdf`.");
    expect(existsSync(path.join(run.runDir, "annotated/main.pdf"))).toBe(true);
    // and at a halt, with every awaiting-decision macro in use
    run.state.verify!.weakening_repair = { status: "pending", at: "t", items: [{ node: "thm:clt", printed: "…", proposed: "p", given_up: "the moment-free claim", detail: "d", witness: "w", source: "fixer" }] };
    run.state.verify!.cross_stage_rewind = { intent: "incremental_repair", status: "pending", presented: true, stage: "F3", route: "unclear", detail: "Increasing is ambiguous_here & 50%.", axis: "clarify", nodes: ["prop:mono"], at: "t" };
    run.state.verify!.cap_reached = { counter: "patch_rounds", rounds: 3, cap: 3, origin: "F-rewind", findings: [{ id: "lem:bound", axis: "correctness", detail: "x", witness: null }], proposed: [], at: "t" };
    const out = await annotateRun({ runDir: run.runDir, qid: QID, state: run.state, when: "halt", compile: compileTex, log: () => {} });
    expect(out.result!.compile.status).toBe("passed");
    expect(out.path).toBe(path.join(run.runDir, "annotated", "main.pdf"));
    for (const m of ["\\vsProposed{", "\\vsRewind{", "\\vsCap{"]) expect(`${await read(run.runDir, "annotated/main.tex")}${await read(run.runDir, "annotated/sec/results.tex")}`).toContain(m);
  }, 60_000);
});

describe("annotated paper at an owner halt", () => {
  const halt = async (run: { runDir: string; state: StateJson }, compile: CompileTex = passed): Promise<Awaited<ReturnType<typeof annotateRun>>> =>
    annotateRun({ runDir: run.runDir, qid: QID, state: run.state, when: "halt", compile, log: () => {} });

  it("a proposal that adds a hypothesis restates the sentence stating the hypotheses: that restatement is the whole proposal, no added-hypothesis block (2026-09-26)", async () => {
    const run = await seedRun();
    const restated = "Assume the sample is independent with finite variance and the Lindeberg condition holds.";
    const sr = { ...PATCHES.unfixable[0]!.suggested_repair, corrected_statement: `${restated} The statistic $T_n$ is asymptotically normal.`, ops: [{ op: "replace" as const, unit: "thm:clt/1/1", tex: restated }] };
    await writeFile(path.join(run.runDir, VERIFY_FILES.patches), JSON.stringify({ ...PATCHES, unfixable: [{ ...PATCHES.unfixable[0]!, suggested_repair: sr }] }, null, 2), "utf8");
    run.state.verify!.weakening_repair = {
      status: "pending",
      at: "t",
      items: [{ node: "thm:clt", printed: "…", proposed: sr.corrected_statement, given_up: "the moment-free claim", detail: "The CLT fails without finite variance.", witness: "Cauchy samples", source: "fixer" }],
    };
    await halt(run);
    const sec = await read(run.runDir, "annotated/sec/results.tex");
    expect(sec).toContain(`\\vsOriginal{Assume the sample is independent.} \\vsProposed{${restated}} The statistic $T_n$ is asymptotically normal. \\vsNote{The proposed repair restates the result as in blue. The CLT fails`);
    expect(sec).not.toMatch(/vsProposedAdded|vsAdded/u);
    expect(sec.slice(0, sec.indexOf("\\vsProposedProof")).match(/Lindeberg/gu)).toHaveLength(1);
  });

  it("a weakened repair: the printed sentence red, the proposal blue under its awaiting label, the note with what it gives up and the three answers", async () => {
    const run = await seedRun();
    run.state.verify!.weakening_repair = {
      status: "pending",
      at: "t",
      items: [{ node: "thm:clt", printed: "…", proposed: PATCHES.unfixable[0]!.suggested_repair.corrected_statement, given_up: "the moment-free claim", detail: "The CLT fails without finite variance.", witness: "Cauchy samples", source: "fixer" }],
    };
    const out = await halt(run);
    expect(out.path).toBe(path.join(run.runDir, "annotated", "main.pdf"));
    const sec = await read(run.runDir, "annotated/sec/results.tex");
    expect(sec).toContain(
      "\\vsOriginal{Assume the sample is independent.} \\vsProposed{Assume the sample is independent with finite variance.} The statistic $T_n$ is asymptotically normal. " +
        `\\vsNote{The proposed repair restates the result as in blue. The CLT fails without finite variance. Counterexample: Cauchy samples. \\vsLine\\textbf{Gives up:} The moment-free claim.}`,
    );
    // not also rendered as a V6 "suggested repair (not applied)"
    expect(sec).not.toContain("Suggested repair (not applied)");
    const main = await read(run.runDir, "annotated/main.tex");
    expect(main).toContain("\\newcommand{\\vsProposed}[1]{\\vsBlock{vsBlue}{}{Proposed repair (awaiting your decision):}{#1}}");
    // confirmed repairs render as at V6
    expect(main).toContain("\\vsOriginal{The estimator converges at rate $n^{-1/2}$.} \\vsCorrected{The estimator converges at rate $n^{-1/3}$.}");
    const md = await read(run.runDir, "annotated/ANNOTATIONS.md");
    expect(md).toContain("**Awaiting your decision: 1 item(s)**");
    expect(md).toMatch(/\| `thm:clt` \| sec\/results\.tex:2 \| awaiting decision \| units \|/);

    // idempotent: the same halt regenerates the same tree; V6 rebuilds it with nothing awaiting
    const first = { sec, md };
    await halt(run);
    expect({ sec: await read(run.runDir, "annotated/sec/results.tex"), md: await read(run.runDir, "annotated/ANNOTATIONS.md") }).toEqual(first);
    run.state.verify!.weakening_repair = { ...run.state.verify!.weakening_repair!, status: "declined", reason: "no" };
    await runV6(run);
    for (const f of ["annotated/main.tex", "annotated/sec/results.tex"]) {
      const t = await read(run.runDir, f);
      for (const m of ["\\vsProposed{", "\\vsRewind{", "\\vsCap{", "awaiting your decision):} " + "The"]) expect(t).not.toContain(m);
    }
    expect(await read(run.runDir, "annotated/ANNOTATIONS.md")).not.toMatch(/awaiting decision \||Awaiting your decision: /);
  });

  it("a proposed rewind's finding that is not TeX (a Lean reviewer's curly quotes) is printed verbatim, nobody's defect (2026-09-30)", async () => {
    const run = await seedRun();
    run.state.verify!.cross_stage_rewind = {
      intent: "incremental_repair",
      status: "pending",
      presented: true,
      stage: "F2.5",
      route: "fix-source",
      detail: "d",
      targets: [{ obj_id: "ass:indep", kind: "statement-wrong", route: "fix-source", axis: "clarify", reason: "[statement-wrong] The phrase “independent” admits two readings.", node: "ass:indep", node_kind: "assumption", users: ["thm:clt"], status: "routed" }],
      nodes: ["thm:clt"],
      at: "t",
    };
    const r = await halt(run);
    expect(await read(run.runDir, "annotated/sec/results.tex")).toContain("\\vsRewind{\\texttt{The phrase [U+201C]independent[U+201D] admits two readings.} Awaiting your decision:");
    expect(r.result!.defects).toEqual([]);
    expect(r.render).toEqual([]);
  });

  it("a proposed rewind: its node red with the finding and axis; a cap: a note on each node of the stopped round", async () => {
    const run = await seedRun();
    run.state.verify!.cross_stage_rewind = {
      intent: "incremental_repair",
      status: "pending",
      presented: true,
      stage: "F2.5",
      route: "fix-source",
      detail: "d",
      targets: [{ obj_id: "ass:indep", kind: "statement-wrong", route: "fix-source", axis: "correctness", reason: "[F2.5 reviewer] Independence alone does not give normality.", node: "ass:indep", node_kind: "assumption", users: ["thm:clt"], status: "routed" }],
      nodes: ["thm:clt"],
      at: "t",
    };
    run.state.verify!.cap_reached = {
      counter: "refinement_rounds",
      rounds: 2,
      cap: 2,
      origin: "V1.5",
      findings: [{ id: "prop:mono", axis: "clarify", detail: "Still two readings of the domain.", witness: null }],
      proposed: [{ node: "prop:mono", corrected_statement: "x" }],
      at: "t",
    };
    await halt(run);
    const sec = await read(run.runDir, "annotated/sec/results.tex");
    expect(sec).toContain(
      "\\vsOriginal{Assume the sample is independent.} \\vsRewind{Independence alone does not give normality. " +
        "Awaiting your decision: have this statement repaired, keep it as printed (say where the paper grants what the finding says it lacks), " +
        "or keep it under a reading you state (the finding misreads the paper; your reading binds the formalization).}",
    );
    expect(sec).toContain(
      "\\vsCap{The repair of this result has not settled within the 2 attempt(s) allowed. The open finding: Still two readings of the domain. " +
        "Awaiting your decision: allow further repair attempts, or stop here and report the result as it stands.}\n\\end{prop}",
    );
    const md = await read(run.runDir, "annotated/ANNOTATIONS.md");
    expect(md).toContain("**Awaiting your decision: 2 item(s)**");
    expect(md).toMatch(/\| `ass:indep` \| sec\/results\.tex:2 \| awaiting decision \|/);
    expect(md).toMatch(/\| `prop:mono` \| sec\/results\.tex:6 \| awaiting decision \|/);
    for (const [name, label] of [["vsRewind", "Proposed correction (awaiting your decision):"], ["vsCap", "Repair not settled (awaiting your decision):"]] as const) {
      expect(await read(run.runDir, "annotated/main.tex")).toContain(`\\newcommand{\\${name}}[1]{\\vsBlock{vsNote}{\\normalfont\\small}{${label}}{#1}}`);
    }
  });

  it("names the TeX when the compile fails, and skips a recompile of the same tree that failed on the paper's own TeX", async () => {
    const run = await seedRun();
    let calls = 0;
    // A failure at \\section{Results} (a line of the paper, far from any annotation).
    const failing: CompileTex = async ({ dir, mainFile }) => {
      calls += 1;
      const lines = (await readFile(path.join(dir, mainFile), "utf8")).split("\n");
      const n = lines.findIndex((l) => l.startsWith("\\section{Results}")) + 1;
      await writeFile(path.join(dir, "main.log"), `./main.tex:${n}: Undefined control sequence.\n`, "utf8");
      return { status: "failed", tool: "pdflatex", pdf: null, log_tail: `./main.tex:${n}: Undefined control sequence.\n`, reason: "pdflatex exited with 1" };
    };
    // The unmodified source fails the same way (compiled once, in a scratch copy): a note, no render defect.
    const note = "note: the paper's own source does not compile here (pdflatex: main.tex:";
    const a = await halt(run, failing);
    expect(calls).toBe(2);
    expect(a.path).toBe(path.join(run.runDir, "annotated", "main.tex"));
    expect(a.line).toContain(note);
    expect(a.line).toContain("Undefined control sequence.); the annotated PDF could not be built — the annotated TeX and the page are unaffected");
    expect(a.render).toEqual([]);
    const b = await halt(run, failing);
    expect(calls).toBe(2);
    expect(b.result!.compile).toMatchObject({ status: "skipped", reason: expect.stringContaining("failed on the paper's own TeX") });
    expect(b.line).toContain(note);
    expect(b.render).toEqual([]);
    expect(await read(run.runDir, "annotated/ANNOTATIONS.md")).toContain("Note: the paper's own source does not compile here");
    // a different tree (a new pending item) compiles again; the source's compile is on record
    run.state.verify!.cap_reached = { counter: "patch_rounds", rounds: 3, cap: 3, origin: "V1.5", findings: [{ id: "thm:rate", axis: "correctness", detail: "x", witness: null }], proposed: [], at: "t" };
    await halt(run, failing);
    expect(calls).toBe(3);
  });
});

describe("annotate_tex helpers", () => {
  it.each<[string, () => void]>([
    ["injects xcolor only when nothing loads it, and the macro block once", () => {
      const bare = "\\documentclass[11pt]{article}\n\\usepackage{amsmath}\n\\begin{document}\nx\n\\end{document}\n";
      const once = injectPreamble(bare, loadsXcolor(bare));
      expect(once.addedXcolor && once.addedBlock).toBe(true);
      expect(once.tex).toMatch(/^\\documentclass\[11pt\]\{article\}\n\\usepackage\{xcolor\}% added by TheoremChecker\n/);
      expect(injectPreamble(once.tex, loadsXcolor(once.tex)).tex).toBe(once.tex);

      const withX = "\\documentclass{article}\n\\usepackage[dvipsnames]{xcolor}\n\\begin{document}\nx\n\\end{document}\n";
      expect(loadsXcolor(withX)).toBe(true);
      const r = injectPreamble(withX, loadsXcolor(withX));
      expect(r.addedXcolor).toBe(false);
      expect(r.tex).not.toContain("\\usepackage{xcolor}%");
      expect(r.tex.indexOf(VS_BLOCK_MARKER)).toBeGreaterThan(r.tex.indexOf("dvipsnames"));
      // a class that loads xcolor itself, and tikz
      expect(loadsXcolor("\\documentclass{jasa}", "\\RequirePackage[table]{xcolor}")).toBe(true);
      expect(loadsXcolor("\\usepackage{tikz}")).toBe(true);
      expect(loadsXcolor("\\usepackage{color}")).toBe(false);
    }],
    ["a commented-out \\documentclass, \\usepackage{xcolor} or \\begin{document} is none", () => {
      const tpl = "%\\documentclass[blindrev]{informs3}\n\\documentclass[nonblindrev]{informs4} % the default\n%\\usepackage{xcolor}\n% \\begin{document}\n\\usepackage{natbib}\n\\begin{document}\n50\\% of $x$\n\\end{document}\n";
      expect(documentClassOf(tpl)).toBe("informs4");
      expect(preambleOf(tpl)).toContain("natbib");
      expect(loadsXcolor(preambleOf(tpl))).toBe(false);
      expect(loadsXcolor("", "% \\RequirePackage{xcolor}\n")).toBe(false);
      const once = injectPreamble(tpl, loadsXcolor(preambleOf(tpl)));
      expect(once.addedXcolor && once.addedBlock).toBe(true);
      expect(once.tex).toContain("\\documentclass[nonblindrev]{informs4}\n\\usepackage{xcolor}% added by TheoremChecker\n % the default\n");
      expect(once.tex.indexOf(VS_BLOCK_MARKER)).toBeGreaterThan(once.tex.indexOf("natbib"));
      expect(injectPreamble(once.tex, loadsXcolor(preambleOf(once.tex))).tex).toBe(once.tex);
      // no \\begin{document}: the block follows the real class line and the added xcolor line
      const frag = "%\\documentclass{a}\n\\documentclass{b}\nText.\n";
      const f = injectPreamble(frag, false);
      expect(f.tex.startsWith(`%\\documentclass{a}\n\\documentclass{b}\n\\usepackage{xcolor}% added by TheoremChecker\n${VS_PREAMBLE_BLOCK}\n`)).toBe(true);
      expect(injectPreamble(f.tex, false).tex).toBe(f.tex);
    }],
    ["moves an insertion point out of math, math environments, brace groups, labels and comments", () => {
      const at = (text: string, marker: string): number => text.indexOf(marker);
      const safe = (text: string, pos: number): { pos: number; moved: string[] } => safeInsertionPoint(text, pos);
      // $$ … $$: inside the display → right after its closing $$
      const dd = "Formally,\n$$\nx \\rightarrow 1-a.\n$$\nFor local.";
      expect(safe(dd, at(dd, "1-a.") + 4)).toEqual({ pos: at(dd, "\nFor"), moved: ["display"] });
      // \[ … \]
      const br = "Then \\[ T \\to N(0,1). \\] as n grows.";
      expect(safe(br, at(br, "N(0,1).") + 7)).toEqual({ pos: at(br, " as n"), moved: ["display"] });
      // equation (with a label inside) and align*
      const eq = "We have\n\\begin{equation}\\label{eq:a}\n  y = 1.\n\\end{equation}\nso.";
      expect(safe(eq, at(eq, "y = 1.") + 6)).toEqual({ pos: at(eq, "\nso."), moved: ["math environment"] });
      expect(safe(eq, at(eq, "eq:a") + 2)).toEqual({ pos: at(eq, "\nso."), moved: ["group", "math environment"] });
      const al = "Hence\n\\begin{align*}\n a &= b. \\\\\n c &= d.\n\\end{align*}\nDone.";
      expect(safe(al, at(al, "b.") + 2)).toEqual({ pos: at(al, "\nDone."), moved: ["math environment"] });
      // nested brace groups: out of the outermost holding it, and past a command's further arguments
      const nb = "\\textbf{a {b c} d} e and \\frac{x {y}}{z} w";
      expect(safe(nb, at(nb, "c}"))).toEqual({ pos: at(nb, " e and"), moved: ["group"] });
      expect(safe(nb, at(nb, "y}"))).toEqual({ pos: at(nb, " w"), moved: ["group"] });
      // a region holds a position back within one paragraph only: a group around several paragraphs
      // (whatever stands before its brace) scopes a passage, and the block stays by the text
      for (const before of ["\\end{proof}\n\n", "\\end{proof}\n", "\\section{A}\\label{s}\n", "\\appendix\n", "text ", ""]) {
        const bg = `${before}{\\color{black}\nFirst \\emph{x y} claim.\n\nSecond para.\n}\nAfter.`;
        expect(safe(bg, at(bg, "claim.") + 6)).toEqual({ pos: at(bg, "claim.") + 6, moved: [] });
        expect(safe(bg, at(bg, "x y") + 1)).toEqual({ pos: at(bg, " claim."), moved: ["group"] });
        // in the group's last paragraph the group's end is the paragraph's end
        expect(safe(bg, at(bg, "para.") + 5)).toEqual({ pos: at(bg, "\nAfter."), moved: ["group"] });
      }
      const fn = "Text\\footnote{One.\n\nTwo.} more";
      expect(safe(fn, at(fn, "One.") + 4)).toEqual({ pos: at(fn, "One.") + 4, moved: [] });
      expect(safe(fn, at(fn, "Two") + 1)).toEqual({ pos: at(fn, " more"), moved: ["group"] });
      // a math environment whose \end is far below (a mispaired macro) carries nothing past a paragraph
      const me = "\\begin{align}\n a &= b\nText goes on here.\n\nNext paragraph.\n\\end{align}\nEnd.";
      expect(safe(me, at(me, "goes"))).toEqual({ pos: at(me, "goes"), moved: [] });
      // … and is no region for a span either: a wrap on a later line is not widened back to the macro
      const mp = "\\def\\be{\\begin{align}}\nIntro.\n\nA claim here.\n\nMore.\n\\be x \\end{align}\nEnd.";
      expect(safeSpan(mp, at(mp, "A claim"), at(mp, "A claim") + 13)).toMatchObject({ start: at(mp, "A claim"), end: at(mp, "A claim") + 13, extended: [] });
      // nothing is written inside a comment or a verbatim region, however long
      const vb = "\\begin{verbatim}\nline one\n\nline two\n\\end{verbatim}\nEnd.";
      expect(safe(vb, at(vb, "one"))).toEqual({ pos: at(vb, "\nEnd."), moved: ["verbatim"] });
      // \label{…} / \cite{…} arguments
      const lb = "Theorem.\\label{thm:x} More, see \\cite{a,b}.";
      expect(safe(lb, at(lb, ":x"))).toEqual({ pos: at(lb, " More"), moved: ["group"] });
      expect(safe(lb, at(lb, ",b"))).toEqual({ pos: lb.length - 1, moved: ["group"] });
      // a comment (a $ in it never pairs), an escaped \$, inline math
      const cm = "cost % $5 here\nis $x$ and \\$3 net.";
      expect(safe(cm, at(cm, "5 here"))).toEqual({ pos: at(cm, "is $x$"), moved: ["comment"] });
      expect(safe(cm, at(cm, " and"))).toEqual({ pos: at(cm, " and"), moved: [] });
      expect(safe(cm, at(cm, "x$ and"))).toEqual({ pos: at(cm, " and"), moved: ["math"] });
      expect(safe(cm, at(cm, "3 net"))).toEqual({ pos: at(cm, "3 net"), moved: [] });
      // a plain group around one environment holds back no position inside it (a float stays a float);
      // after the environment, a command's argument or a group holding more than it, it does
      for (const before of ["", "\\label{s}\n\n", "Text.\n\n"]) {
        const fl = `${before}{\\begin{algorithm}[t]\\caption{c}\n  $y \\gets x$\\;\n\\end{algorithm}}\nAfter.`;
        expect(safe(fl, at(fl, "\\;") + 2)).toEqual({ pos: at(fl, "\\;") + 2, moved: [] });
        expect(safe(fl, at(fl, "{c}") + 1)).toEqual({ pos: at(fl, "{c}") + 3, moved: ["group"] });
        expect(safe(fl, at(fl, "}\nAfter."))).toEqual({ pos: at(fl, "\nAfter."), moved: ["group"] });
      }
      // … an argument also behind a macro's parameter text, a comment line or wide indentation
      for (const fl of ["\\fbox{\\begin{minipage}{3cm}x y\\end{minipage}} z", "{\\small\\begin{minipage}{3cm}x y\\end{minipage}} z", "{\\begin{minipage}{3cm}x\\end{minipage}\\begin{minipage}{3cm}y\\end{minipage}} z",
        "\\def\\x#1{\\begin{center}x y\\end{center}} z", "\\newcommand{\\body}%\n{\\begin{center}x y\\end{center}} z", "\\newcommand{\\body}\n% a comment line\n{\\begin{center}x y\\end{center}} z", `\\fbox${" ".repeat(60)}{\\begin{center}x y\\end{center}} z`]) {
        expect(safe(fl, at(fl, "x y") + 2)).toEqual({ pos: at(fl, " z"), moved: ["group"] });
      }
      // a position between the opening tag and its placement is not inside the environment
      const tag = "{\\begin{algorithm}[t]x y\\end{algorithm}} z";
      expect(safe(tag, at(tag, "[t]"))).toEqual({ pos: at(tag, " z"), moved: ["group"] });
      expect(safe(tag, at(tag, "x y"))).toEqual({ pos: at(tag, "x y"), moved: [] });
    }],
    ["widens a red span of the source so its end never falls inside math and it never crosses a group", () => {
      // the confidence-interval case: the statement's clause ends inside the closing display
      const ci = "Then the interval is valid. Formally,\n$$\n\\hat\\theta=\\theta_0+o_p(1),\\quad \\Pr\\{\\theta_0 \\in C\\}\\rightarrow 1-a.\n$$\nFor local functionals, the same holds.";
      const w = safeSpan(ci, 0, ci.indexOf("1-a.") + 4);
      expect(ci.slice(w.start, w.end)).toBe(ci.slice(0, ci.indexOf("\nFor local")));
      expect(w.extended).toEqual(["display"]);
      // a start inside math widens back to the math's start
      const s2 = safeSpan(ci, ci.indexOf("\\quad"), ci.indexOf("For local") + 3);
      expect(ci.slice(s2.start, s2.start + 2)).toBe("$$");
      // a bound that is no position returns at once (it never settles the widening loop)
      expect(safeSpan(ci, Number.NaN, 10)).toEqual({ start: Number.NaN, end: 10, extended: [] });
      expect(safeSpan(ci, 0, undefined as unknown as number).extended).toEqual([]);
      // a span crossing a group takes the whole command (control word and arguments)
      const g = "Say \\emph{b c} d and \\frac{x}{y} z.";
      const x = safeSpan(g, g.indexOf("c}"), g.indexOf(" and"));
      expect(g.slice(x.start, x.end)).toBe("\\emph{b c} d");
      const f = safeSpan(g, g.indexOf("y}"), g.indexOf("."));
      expect(g.slice(f.start, f.end)).toBe("\\frac{x}{y} z");
      // a group holding the whole span is left alone
      expect(safeSpan(g, g.indexOf("b c"), g.indexOf("b c") + 3)).toEqual({ start: g.indexOf("b c"), end: g.indexOf("b c") + 3, extended: [] });
    }],
  ])("%s", (_name, check) => check());
});

describe("annotated paper — a statement ending in a display (never inside math)", () => {
  // The confidence-interval shape: the statement ends inside a closing `$$` display.
  const CI_TEX =
    "\\documentclass{article}\n\\usepackage{amsmath,amsthm}\n\\newtheorem{cor}{Corollary}\n\\begin{document}\n\n" +
    "\\begin{cor}[Confidence interval]\\label{cor:ci}\n" +
    "Suppose the rates hold. Then the interval is valid. Formally,\n" +
    "$$\n\\hat\\theta=\\theta_0+o_p(1),\\quad \\Pr\\{\\theta_0 \\in C\\}\\rightarrow 1-a.\n$$\n" +
    "\\end{cor}\n" +
    "\\begin{proof}\nBy the oracle limit,\n$$\n\\sqrt{n}(\\hat\\theta-\\theta_0) = Z + o_p(1).\n$$\nThe remainder vanishes.\n\\end{proof}\n\n\\end{document}\n";
  const CI_REF = {
    qid: QID,
    target_estimand: "the interval",
    symbols: [],
    // a hypothesis quoted from inside the display (its slice ends before the closing $$)
    assumptions: [{ id: "ass:ci-limit", source: { env: "cor:ci", slice: { from: "\\hat\\theta=\\theta_0", to: "1-a." } }, novel: { flag: true, justification: "the paper's" } }],
    definitions: [],
    statements: [{ id: "thm:ci", kind: "theorem", env: "cor:ci" }],
  };
  const ERR = { "thm:ci": { detail: "The rates may refer to one fold or to all folds, with $\\sigma$ fixed.", witness: null } };

  async function seedCi(patches: unknown, mutateEnvs?: (envs: { envs: Array<{ id: string; proofLines: { to: number } | null }> }) => void): Promise<{ runDir: string; state: StateJson }> {
    logs.length = 0;
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-annot-ci-"));
    tmpDirs.push(repoRoot);
    const runDir = verifyRunDir(repoRoot, QID);
    const src = path.join(runDir, "source");
    await mkdir(src, { recursive: true });
    await writeFile(path.join(src, "main.tex"), CI_TEX, "utf8");
    const { envs, flat } = await buildEnvsJson(src, "main.tex");
    await writeEnvsArtifacts(runDir, envs, flat);
    const { core: transcribed, violations } = materializeRefCore(RefCoreSchema.parse(CI_REF), envs, flat.text);
    expect(violations).toEqual([]);
    const { core } = applyPatchFile(transcribed, PatchFileSchema.parse(patches));
    const write = (rel: string, v: unknown): Promise<void> => writeFile(path.join(runDir, rel), JSON.stringify(v, null, 2), "utf8");
    if (mutateEnvs) {
      const e = JSON.parse(await read(runDir, VERIFY_FILES.envsJson));
      mutateEnvs(e);
      await write(VERIFY_FILES.envsJson, e);
    }
    await write("discovery/core_refs.json", CI_REF);
    await write(VERIFY_FILES.coreTranscribed, transcribed);
    await write(VERIFY_FILES.coreJson, core);
    await write(VERIFY_FILES.patches, patches);
    const state = createVerifyInitialState(QID, {
      phase: "v1",
      source: { input: "main.tex", main_file: "main.tex", sha256: "x" },
      targets: null,
      core_sha256: null,
      v1_rounds: 1,
      v1_5_rounds: 1,
      findings: [],
      report_path: null,
      paper_errors: ERR,
    } as never);
    return { runDir, state };
  }
  const logs: string[] = [];
  const annotate = (run: { runDir: string; state: StateJson }, compile: CompileTex = passed) => annotateRun({ runDir: run.runDir, qid: QID, state: run.state, when: "halt", compile, log: (m) => logs.push(m) });
  const patchFile = (p: Record<string, unknown>) => ({ key_results: ["thm:ci"], key_contribution: "c", patches: [{ node: "thm:ci", ...p }], unfixable: [] });
  /** The display of the statement, as printed: no annotation macro may sit inside it. */
  const display = (tex: string): string => {
    const a = tex.indexOf("$$\n\\hat\\theta");
    return tex.slice(a, tex.indexOf("$$", a + 2) + 2);
  };
  const capOn = (run: { state: StateJson }, id: string): void => {
    run.state.verify!.cap_reached = { counter: "patch_rounds", rounds: 3, cap: 3, origin: "F-rewind", findings: [{ id, axis: "correctness", detail: "x", witness: null }], proposed: [], at: "t" } as never;
  };

  it("a note at a statement or a hypothesis ending inside the display goes after the display's closing $$; idempotent", async () => {
    const run = await seedCi(patchFile({ corrected_statement: null, proof_note: "cross-fitting fixes the fold." }));
    const out = await annotate(run);
    const tex = await read(run.runDir, "annotated/main.tex");
    expect(out.error).toBeNull();
    expect(display(tex)).not.toContain("\\vs");
    expect(tex).toContain("\\rightarrow 1-a.\n$$ \\vsNote{The rates may refer to one fold or to all folds, with $\\sigma$ fixed.");
    expect(unannotate(tex)).toBe(CI_TEX);
    const md = await read(run.runDir, "annotated/ANNOTATIONS.md");
    expect(md).toMatch(/\| `thm:ci` \| main\.tex:10 \| error \(repaired\) \| env \|/);
    // the proof block after the proof, outside its display
    expect(tex).toContain("\\end{proof}\n\\vsProof{The statement stands; the proof is completed as follows. cross-fitting fixes the fold.}\n");
    // the same records give the same tree
    const first = tex;
    await annotate(run);
    expect(await read(run.runDir, "annotated/main.tex")).toBe(first);
    // a note-only annotation on the hypothesis quoted from inside the display: the insertion moves out
    capOn(run, "ass:ci-limit");
    logs.length = 0;
    await annotate(run);
    const capped = await read(run.runDir, "annotated/main.tex");
    expect(display(capped)).not.toContain("\\vs");
    expect(capped).toMatch(/\\rightarrow 1-a\.\n\$\$ \\vsNote\{[^}]*\} \\vsCap\{/);
    expect(logs).toContain("annotated paper: insertion moved out of display (main.tex:9 → main.tex:10)");
  });
});

describe("annotated paper — a reading pinned on a result stated in running text (live Li–Morgan–Zaslavsky)", () => {
  const PROSE_TEX =
    "\\documentclass{article}\n\\begin{document}\n\n" +
    "\\textbf{Theorem 1.} \\emph{The estimator $\\hat\\tau$ is consistent.}\n\n" +
    "The next result is about variance.\n\n\\end{document}\n";

  it("goes at the end of the statement, which has no environment to follow", async () => {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-annot-prose-"));
    tmpDirs.push(repoRoot);
    const runDir = verifyRunDir(repoRoot, QID);
    const src = path.join(runDir, "source");
    await mkdir(src, { recursive: true });
    await writeFile(path.join(src, "main.tex"), PROSE_TEX, "utf8");
    const { envs, flat } = await buildEnvsJson(src, "main.tex");
    await writeEnvsArtifacts(runDir, envs, flat);
    const env = envs.envs.find((e) => e.envName.startsWith("prose:"))!;
    const ref = { qid: QID, target_estimand: "the estimand", symbols: [], assumptions: [], definitions: [], statements: [{ id: "thm:one", kind: "theorem", env: env.id }] };
    const { core, violations } = materializeRefCore(RefCoreSchema.parse(ref), envs, flat.text);
    expect(violations).toEqual([]);
    core.assumptions.push({
      id: "ass:pin-1",
      kind: "regularity",
      condition: "consistency is convergence in probability",
      bookkeeping: { flag: true, added_by: "V1.5", reason: "pins reading of thm:one: the proof uses it" },
    } as Core["assumptions"][number]);
    core.statements[0]!.depends_on.push("ass:pin-1");
    const write = (rel: string, v: unknown): Promise<void> => writeFile(path.join(runDir, rel), JSON.stringify(v, null, 2), "utf8");
    await write("discovery/core_refs.json", ref);
    await write(VERIFY_FILES.coreTranscribed, core);
    await write(VERIFY_FILES.coreJson, core);
    const state = createVerifyInitialState(QID, {
      phase: "v1", source: { input: "main.tex", main_file: "main.tex", sha256: "x" }, targets: null, core_sha256: null,
      v1_rounds: 1, v1_5_rounds: 1, findings: [], report_path: null,
    } as never);
    const out = await annotateRun({ runDir, qid: QID, state, when: "halt", compile: passed, log: () => {} });
    expect(out.error).toBeNull();
    const tex = await read(runDir, "annotated/main.tex");
    expect(tex).toContain("is consistent.}\\vsReading{consistency is convergence in probability}\n\nThe next result");
    expect(await read(runDir, "annotated/ANNOTATIONS.md")).not.toContain("environment was not found");
    // a condition added to it: a note there too, listed by its kind
    core.assumptions.push({ id: "ass:bk-1", kind: "regularity", condition: "$n \\ge 2$", bookkeeping: { flag: true, added_by: "V1.5", reason: "the proof divides by $n-1$" } } as Core["assumptions"][number]);
    core.statements[0]!.depends_on.push("ass:bk-1");
    await write(VERIFY_FILES.coreJson, core);
    expect((await annotateRun({ runDir, qid: QID, state, when: "halt", compile: passed, log: () => {} })).error).toBeNull();
    expect(await read(runDir, "annotated/main.tex")).toContain("is consistent.}\\vsReading{consistency is convergence in probability}\\vsCondition{$n \\ge 2$}\n\nThe next result");
    expect(await read(runDir, "annotated/ANNOTATIONS.md")).toMatch(/\| `thm:one` \| main\.tex:4 \| condition added \| after-env \| ass:bk-1: \$n \\ge 2\$ \|/u);
  });
});

describe("annotated paper — model-written text is set as written; the compile check decides, nothing is repaired", () => {
  // Symbol readings verbatim from the CNS / DFM runs' `discovery/v1_5_symbols.json`: the first two in
  // plain notation (commands outside $…$) — they used to be split into math groups by the sanitizer;
  // the third, `f_0:\mathbb{R}\rightarrow[0,\infty)`, the sanitizer escaped (it read `[0,\infty)` as an
  // unclosed optional argument of \rightarrow) although it compiles.
  const LIVE = [
    {
      name: "\\gamma",
      reading:
        "\\gamma is an arbitrary fixed, real-valued, square-integrable member of the analyst-known linear class \\Gamma\\subset\\mathbb L_2, acting on W in the general framework and on W_1 in the inverse-problem notation (with W_1=(D,X) in the elasticity example); it is distinct from the population solution \\gamma_0 and its estimator.",
    },
    { name: "\\tilde{c}", reading: "\\tilde c is a fixed strictly positive lower bound on the conditional q-moment norm of Y-\\gamma_0(W) given W for q\\in\\{2,3,4\\}, in both the global and local lemmas." },
    { name: "f_0", reading: "$f_0:\\mathbb{R}\\rightarrow[0,\\infty)$ is the density of $Y(0)$." },
  ];
  const BROKEN = [
    { name: "S", reading: "the set \\{x : f(x} > 0 of {positive values" }, // a stray } and an unclosed {
    { name: "p", reading: "costs $5 per unit, with $a_1$ known" }, // a lone $
    { name: "t", reading: "the last word is $\\tilde$" }, // a command awaiting its argument
    { name: "u", reading: "$\\mu \\in \\mathbb R$ with μ ≠ 0" }, // Unicode mathematics
  ];
  const FLAT = [
    "\\documentclass{article}\\usepackage{amssymb,amsthm}", // 1
    "\\newtheorem{theorem}{Theorem}", // 2
    "\\begin{document}", // 3
    "Let $S$, $p$, $t$, $u$, $f_0$ and $\\gamma$ be given.", // 4
    "", // 5
    "\\begin{theorem}\\label{thm:a}", // 6
    "The constant $\\tilde{c}$ is positive.", // 7
    "\\end{theorem}", // 8
    "\\begin{proof}", // 9
    "Immediate.", // 10
    "\\end{proof}", // 11
    "\\end{document}", // 12
  ].join("\n");
  const core = (): Core =>
    ({
      qid: "ts",
      symbols: [],
      assumptions: [],
      definitions: [],
      statements: [{ id: "thm:a", kind: "theorem", statement: "The constant is positive.", depends_on: [], status: "to-prove", tex_locator: { file: "main.tex", from: 6, to: 8, env: "theorem", label: "thm:a" } }],
      target_estimand: "t",
      bibliography: [],
    }) as unknown as Core;
  const input = (texVerdicts: Map<string, string> | null = null): AnnotationInput => ({
    files: { "main.tex": FLAT },
    envs: {
      main_file: "main.tex",
      files: ["main.tex"],
      newtheorem: {},
      envs: [{ id: "thm:a", kind: "theorem", envName: "theorem", label: "thm:a", title: null, body: "The constant $\\tilde{c}$ is positive.", proof: "Immediate.", proofLines: { file: "main.tex", from: 9, to: 11 }, section: null, lines: { file: "main.tex", from: 6, to: 8 }, refs: [] }],
      bibliography: [],
    } as never,
    flatText: FLAT,
    lineMap: FLAT.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 })),
    refs: null,
    transcribed: core(),
    core: core(),
    // a fixer proof note in LaTeX with an unclosed group
    patches: { patches: [{ node: "thm:a", corrected_statement: null, proof_note: "by $\\frac{a}{b$ the bound" }], unfixable: [] },
    paperErrors: {},
    findings: [],
    review: {
      verdict: "PASS",
      summary: "",
      nodes: [],
      symbols: [...LIVE, ...BROKEN].map((v) => ({
        name: v.name,
        meaning: "ok",
        fix: null,
        ambiguity: "pinned",
        reading: { reading: v.reading, evidence: "" },
        redefined_at: null,
        detail: "",
        introduced_at: v.name === "\\tilde{c}" ? { flat_line: 7, file: "main.tex", line: 7 } : { flat_line: 4, file: "main.tex", line: 4 },
      })),
    } as never,
    texVerdicts,
  });

  it("without verdicts every ASCII text with balanced braces is set byte for byte (no repair, no log of one); the others are flagged, printed verbatim", () => {
    const plan = planAnnotations(input());
    const tex = applyEdits(FLAT, plan.edits["main.tex"] ?? []);
    for (const v of [...LIVE, ...BROKEN.slice(1, 3)]) expect(tex).toContain(`{${v.reading}}`);
    expect(tex).toContain(verbatimLike("by $\\frac{a}{b$ the bound"));
    expect(plan.log.some((l) => /repaired/u.test(l))).toBe(false);
    expect(plan.defects).toHaveLength(3);
    expect(plan.defects).toContainEqual({ node: "thm:a", block: "proof note", reason: expect.stringMatching(/^an unclosed \{/u), fragment: expect.objectContaining({ producer: "fixer", kind: "note" }) });
    expect(plan.defects).toEqual(expect.arrayContaining([
      { node: "symbol S", block: "symbol reading", reason: expect.stringMatching(/^a \} that closes no \{ — braces that print are \\\{ … \\\}; printed verbatim — the fragment: the set/u), fragment: expect.objectContaining({ producer: "symbol", ref: "S" }) },
      { node: "symbol u", block: "symbol reading", reason: expect.stringMatching(/^a non-ASCII character U\+03BC \(μ\), U\+2260 \(≠\) — the text is plain ASCII/u), fragment: expect.objectContaining({ producer: "symbol", ref: "u" }) },
    ]));
    expect(tex).toContain(verbatimLike(BROKEN[0]!.reading));
    expect(tex).toContain(verbatimLike(BROKEN[3]!.reading));
  });

  it("a symbol reading with scoped clauses is printed in full: the general part, then each clause led by its results as the paper names them", () => {
    const base = input();
    const one = { ...(base.review as never as { symbols: Array<{ reading: object }> }).symbols[2]!, reading: { reading: "$f_0$ is a density.", evidence: "", scoped: [{ results: ["thm:a"], text: "$f_0$ is bounded." }] } };
    const plan = planAnnotations({ ...base, review: { ...(base.review as object), symbols: [one] } as never });
    expect(applyEdits(FLAT, plan.edits["main.tex"] ?? [])).toContain("\\vsReadingSymbol{$f_0$}{$f_0$ is a density. In Theorem~\\ref{thm:a}: $f_0$ is bounded.}");
  });

  it("a symbol named by a macro with arguments is printed with a placeholder for each", () => {
    const flat = String.raw`\newcommand{\costSub}[2]{{\mathsf{cost}}_{#2}(#1)}\newcommand\opt[2][x]{#1#2}\newcommand{\cX}{\mathcal X}`;
    expect(macroArity(flat, String.raw`\costSub`)).toBe(2);
    expect(macroArity(flat, String.raw`\opt`)).toBe(1);
    expect(macroArity(flat, String.raw`\cX`)).toBe(0);
    expect(macroArity(flat, String.raw`\cost`)).toBe(0);
    expect(macroArity(flat, "f_0")).toBe(0);
  });

  it("a repair whose ops no longer resolve on the paper's units marks nothing and is listed as unlocated, so the TODO list shows it", () => {
    const stale = { node: "thm:a", corrected_statement: "The constant is positive.", proof_note: null, ops: [{ op: "replace", unit: "thm:a/1/9", tex: "The constant is positive." }] };
    const plan = planAnnotations({ ...input(), patches: { patches: [stale], unfixable: [] } as never });
    expect(plan.log.some((l) => /the ops of thm:a do not resolve on the paper's units/u.test(l))).toBe(true);
    expect(plan.unlocated).toContainEqual({ node: "thm:a", kind: "error (repaired)", reason: expect.stringMatching(/^its ops do not resolve on the paper's units/u), placed: null });
  });

  it("a repair of a hypothesis or definition that replaces no text only pins a reading: its passage is not marked as an error", () => {
    const pinned = { node: "ass:scale", corrected_statement: null, proof_note: null, ops: [], readings: ["$S_T^2$ is the variance of the sum from $t=2$."] };
    const plan = planAnnotations({ ...input(), patches: { patches: [pinned], unfixable: [] } as never });
    expect(plan.unlocated.filter((u) => u.node === "ass:scale")).toEqual([]);
    expect(plan.records.filter((r) => r.node === "ass:scale" && r.kind === "error (repaired)")).toEqual([]);
    // … while one that does replace text is still an error to place
    const replaced = { ...pinned, corrected_statement: "A new text." };
    expect(planAnnotations({ ...input(), patches: { patches: [replaced], unfixable: [] } as never }).unlocated.map((u) => u.node)).toContain("ass:scale");
  });

  it("a symbol name that does not compile alone (live Roth–Sant'Anna \\expe{…}, a macro taking an argument) is printed verbatim — the paper's notation, no defect", () => {
    const base = input();
    const named = { ...base, review: { ...(base.review as object), symbols: [{ ...(base.review as never as { symbols: object[] }).symbols[0]!, name: "\\expe" }] } as never };
    const plan = planAnnotations({ ...named, texVerdicts: new Map([["note\u0000$\\expe$", "Missing \\right. inserted."]]) });
    expect(plan.defects.filter((d) => d.block === "symbol name")).toEqual([]);
    expect(applyEdits(FLAT, plan.edits["main.tex"] ?? [])).toContain(verbatimLike("$\\expe$"));
    expect(plan.log).toContain("annotation symbol \\expe: symbol name printed verbatim (Missing \\right. inserted.)");
  });
});

describe("annotated paper — control and invisible characters in model text (live CNS thm:ci note)", () => {
  // Verbatim from cns_simple_dml `discovery/owner_explanations.json` (JSON-decoded): the model put a
  // DEL (U+007F) before most TeX words, and wrote single backslashes JSON decoded into tab / backspace
  // (`\theta`, `\bar`, `\to`). Nothing restores them now: the source check sends such a reply back, the
  // renderer flags one on file.
  const LIVE = JSON.parse(String.raw`{
    "what_is_wrong": "The proof needs to show that $\u007f\\sigma/\u007f\\sqrt n=o(1)$ in order to pass from a standardized Gaussian approximation to consistency.",
    "claim": "The displayed identity asserts that $n_{\\ell}^{1/2}(\u007f\theta_{\\ell}-\bar{\theta}_{\\ell})=\u007f\\Delta_{1\\ell}$."
  }`) as Record<string, string>;

  it("the renderer flags the DEL; the source check names the JSON-escape damage", () => {
    expect(nonAsciiProblem(LIVE.what_is_wrong!)).toMatch(/^a non-ASCII character U\+007F — U\+007F stands where a TeX backslash belongs/u);
    expect(texMathProblems(LIVE.claim!, "claim").join(" ")).toMatch(/control character \(U\+0009\) in `claim` before "heta"/u);
    expect(texMathProblems(LIVE.claim!, "claim").join(" ")).toContain("a non-ASCII character U+007F, U+0008 in `claim`");
  });
});

describe("annotated paper — hypotheses added by restatement; no no-op changes (live CNS, 2026-09-26)", () => {
  // cns_simple_dml: Lemma B.10 marked with red/blue pairs identical as printed. Since replacement-only
  // repairs (2026-09-26) a repair adds a hypothesis by restating its own statement, and a result using
  // the repaired one is never marked with a hypothesis it did not state.
  const LIVE = JSON.parse(readFileSync(path.join(path.dirname(fileURLToPath(import.meta.url)), "fixtures", "cns_carried_hypotheses.json"), "utf8")) as {
    bodies: Record<string, string>;
    titles: Record<string, string | null>;
    hyps: Record<string, string>;
    global_ops: unknown[];
    global_proof_note: string;
    global_given_up: string;
    approx_ops: unknown[];
  };
  const envTex = (name: string, id: string, title: string | null = LIVE.titles[id] ?? null): string => `\\begin{${name}}${title ? `[${title}]` : ""}${LIVE.bodies[id]}\n\\end{${name}}\n\n`;
  const TEX =
    "\\documentclass{article}\n\\usepackage{amsmath,amssymb,amsthm}\n\\newtheorem{theorem}{Theorem}\n\\newtheorem{lemma}{Lemma}\n\\newtheorem{proposition}{Proposition}\n\\begin{document}\n\\section{Results}\n\n" +
    envTex("proposition", "prop:resid2") + envTex("theorem", "thm:dml") + envTex("theorem", "thm:var") + envTex("proposition", "prop:Delta2") +
    "\\begin{lemma}[Bounded Riesz representer for local functionals]\\label{lemma:bounded_RR_local}\nSuppose $\\alpha_0^{\\min}$ exists and $\\Gamma\\subset \\mathbb{L}_2$. Then the finite sample bound in the proof holds.\n\\end{lemma}\n\n" +
    envTex("lemma", "lemma:cont_local") + envTex("theorem", "thm:local") + envTex("lemma", "lemma:RR_exists") + envTex("lemma", "lemma:approx", "Approximation error from localization") +
    "\\end{document}\n";
  const hyp = (id: string): string => LIVE.hyps[id]!;
  const st = (id: string, kind: string, env: string, extra: Record<string, unknown> = {}) => ({ id, kind, env, ...extra });
  const REF = {
    qid: QID,
    target_estimand: "the functional",
    symbols: [],
    assumptions: [],
    definitions: [],
    statements: [
      st("prop:resid2", "proposition", "prop:resid2"),
      st("thm:dml", "theorem", "thm:dml"),
      st("thm:var", "theorem", "thm:var"),
      st("prop:delta2", "proposition", "prop:Delta2"),
      st("lem:bounded-rr-local", "lemma", "lemma:bounded_RR_local"),
      st("lem:cont-local", "lemma", "lemma:cont_local"),
      st("thm:local", "theorem", "thm:local"),
      st("lem:rr-exists", "lemma", "lemma:RR_exists"),
      st("lem:approx", "lemma", "lemma:approx"),
    ],
  };
  const patch = (node: string, p: Record<string, unknown>) => ({ node, corrected_statement: null, proof_note: "The proof is unchanged.", ...p });
  const PATCHES = {
    key_results: ["thm:dml"],
    key_contribution: "c",
    patches: [
      // Proposition D.9 restates its hypothesis sentence with the two hypotheses its proof needs (Theorems
      // 5.1 and 5.3 and Proposition D.10 use it: none is marked)
      patch("prop:resid2", { ops: [{ op: "replace" as const, unit: "prop:resid2/1/1", tex: `Suppose Assumption~\\ref{assumption:cont} holds and\n$$\n\\|\\hat{\\alpha}_{\\ell}\\|_{\\infty}\\leq\\bar{\\alpha}'.\n$$\nSuppose in addition that ${hyp("ass:patch-resid2-conditional-second-moment")} ${hyp("ass:patch-fitted-errors-in-gamma")}` }] }),
      // Lemma B.8 restates its hypothesis sentence
      patch("lem:bounded-rr-local", { ops: [{ op: "replace" as const, unit: "lemma:bounded_RR_local/1/1", tex: `Suppose $\\alpha_0^{\\min}$ exists and $\\Gamma\\subset \\mathbb{L}_2$. ${hyp("ass:patch-local-normalizer")}` }] }),
      // Lemma B.10: the preamble, item 3 and item 4 restated as printed; item 1 really changed
      patch("lem:approx", { ops: LIVE.approx_ops }),
    ],
    // Theorem 5.2's global conclusion (thm:local/1/3) replaced: a weakened repair awaiting the owner
    unfixable: [{ node: "thm:local", reason: "any repair weakens the contribution: the global bound on the representer is lost", suggested_repair: { corrected_statement: null, ops: [{ op: "replace" as const, unit: "thm:local/1/3", tex: (LIVE.global_ops[0] as { tex: string }).tex }], given_up: LIVE.global_given_up, proof_note: LIVE.global_proof_note } }],
  };
  const err = (detail: string) => ({ detail, witness: "w" });
  async function seed(): Promise<{ runDir: string; state: StateJson }> {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-annot-carried-"));
    tmpDirs.push(repoRoot);
    const runDir = verifyRunDir(repoRoot, QID);
    const src = path.join(runDir, "source");
    await mkdir(src, { recursive: true });
    await writeFile(path.join(src, "main.tex"), TEX, "utf8");
    const { envs, flat } = await buildEnvsJson(src, "main.tex");
    await writeEnvsArtifacts(runDir, envs, flat);
    const { core: transcribed, violations } = materializeRefCore(RefCoreSchema.parse(REF), envs, flat.text);
    expect(violations).toEqual([]);
    const { core } = applyPatchFile(transcribed, PatchFileSchema.parse(PATCHES));
    const write = (rel: string, v: unknown): Promise<void> => writeFile(path.join(runDir, rel), JSON.stringify(v, null, 2), "utf8");
    await write("discovery/core_refs.json", REF);
    await write(VERIFY_FILES.coreTranscribed, transcribed);
    await write(VERIFY_FILES.coreJson, core);
    await write(VERIFY_FILES.patches, PATCHES);
    const state = createVerifyInitialState(QID, {
      phase: "v1",
      source: { input: "main.tex", main_file: "main.tex", sha256: "x" },
      targets: null,
      core_sha256: null,
      v1_rounds: 1,
      v1_5_rounds: 1,
      findings: [],
      report_path: null,
      paper_errors: {
        "prop:resid2": err("The fitted errors may leave the space."),
        "lem:bounded-rr-local": err("The normalizer may vanish."),
        "lem:approx": err("The neighborhood is misstated."),
      },
    } as never);
    state.verify!.weakening_repair = {
      status: "pending",
      at: "t",
      items: [{ node: "thm:local", printed: "…", proposed: "p", given_up: LIVE.global_given_up, detail: "The representer bound is not implied.", witness: "w", source: "fixer" }],
    } as never;
    return { runDir, state };
  }
  const envOf = (tex: string, label: string, end: string): string => {
    const a = tex.indexOf(`\\label{${label}}`);
    return tex.slice(a, tex.indexOf(`\\end{${end}}`, a));
  };
  let tex = "";
  let md = "";
  async function render(): Promise<void> {
    if (tex) return;
    const run = await seed();
    const out = await annotateRun({ runDir: run.runDir, qid: QID, state: run.state, when: "halt", compile: passed, log: () => {} });
    expect(out.error).toBeNull();
    tex = await read(run.runDir, "annotated/main.tex");
    md = await read(run.runDir, "annotated/ANNOTATIONS.md");
  }
  const count = (t: string, s: string): number => t.split(s).length - 1;

  it.each<[string, () => void]>([
    ["rules 1 and 3: a hypothesis is added by its result's own restatement (red / blue); a result using it is never marked, and no page pointer or 'this result uses' line anywhere; a note holds only its explanation", () => {
      for (const [label, end] of [["thm:dml", "theorem"], ["thm:var", "theorem"], ["prop:Delta2", "proposition"], ["lemma:cont_local", "lemma"]] as const) {
        expect(envOf(tex, label, end)).not.toMatch(/\\vs[A-Z]/u);
      }
      const d9 = envOf(tex, "prop:resid2", "proposition");
      expect(count(d9, "\\vsOriginal{")).toBe(1);
      expect(d9).toMatch(/\\vsCorrected\{Suppose Assumption[\s\S]*For every fold \$\\ell\$, \$\\hat\\gamma_\\ell-\\gamma_0\\in\\Gamma\$ almost surely\.\}/u);
      expect(tex).not.toMatch(/vsAdded|added by the repair|its note is on|this result uses|Hypothes[ie]s added by/u);
      for (const m of tex.matchAll(/\\vsNote\{/gu)) {
        let d = 0;
        let i = m.index! + "\\vsNote{".length - 1;
        for (; i < tex.length; i += 1) if (tex[i] === "{" && tex[i - 1] !== "\\") d += 1; else if (tex[i] === "}" && tex[i - 1] !== "\\" && --d === 0) break;
        expect(tex.slice(m.index!, i)).not.toMatch(/added by the repair|Added hypothes|Proposed added hypothes/u);
      }
    }],
    ["rule 7: a change identical to the printed text up to spacing, punctuation, braces and script order is not marked; a real change is", () => {
      const b10 = envOf(tex, "lemma:approx", "lemma");
      expect(count(b10, "\\vsOriginal{")).toBe(1);
      expect(b10).toMatch(/\\vsOriginal\{Valid neighborhood\. There exists \$N_\{h_0\}\(v\)=\(v':\|v'-v\|\\leq h\)\\subset \\mathcal\{V\}\$\.\} \\vsCorrected\{Valid neighborhood\. There exists \$N_\{h_0\}\(v\)=\\\{v':\|v'-v\|\\leq h_0\\\}\\subset\\mathcal V\$\.\}/u);
    }],
  ])("%s", async (_name, check) => {
    await render();
    check();
  });
});

describe("annotated paper — the render rules, on repairs cut from the live CNS run (2026-09-25)", () => {
  // R1 a result with no repair of its own is not marked, whatever another repair changes; the repaired
  //    result's own units are red / blue.
  // R2 a corrected statement differing in part: only the replaced units red and blue.
  // R4 a result printed without a proof: right after it, every lemma it uses, the corrections by the
  //    paper's own section numbers.
  // The live patches are in the text format of their day: `live()` strips its added-hypothesis records and
  // text proof edits, and each test gives the repair as replacements of the paper's units.
  const LIVE = JSON.parse(readFileSync(path.join(path.dirname(fileURLToPath(import.meta.url)), "fixtures", "render_rules_live.json"), "utf8")) as {
    cns: {
      resid2_env: string;
      tex: Record<string, string>;
      refs: { statements: Array<{ id: string; env: string; hypotheses?: string[]; depends_on?: string[] }>; assumptions: Array<{ id: string; source: { env: string } }> };
      patches: Array<{ node: string; add_assumptions?: Array<{ id: string; wire_into: string[] }>; consequence_of?: string[] }>;
      paper_errors: Record<string, unknown>;
    };
    dfm: {
      var_kurt_tex: string;
      twoforms_tex: string;
      unfixable: unknown[];
      weakening_item: Record<string, unknown>;
      paper_errors: Record<string, unknown>;
      refs: { statements: Array<{ id: string; env: string }>; assumptions: Array<{ id: string; source: { env: string } }> };
      symbol_A: Record<string, unknown>;
    };
  };

  const QID = "render_rules";
  const tmpDirs: string[] = [];
  afterEach(async () => {
    for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
  });
  const passed: CompileTex = async () => ({ status: "passed", tool: "pdflatex", pdf: "main.pdf", log_tail: "", reason: "" });
  const PREAMBLE = "\\documentclass{article}\n\\usepackage{amsmath,amssymb,amsthm}\n\\newtheorem{theorem}{Theorem}\n\\newtheorem{lemma}{Lemma}\n\\newtheorem{proposition}{Proposition}\n\\newtheorem{corollary}{Corollary}\n\\newtheorem{thm}{Theorem}\n\\begin{document}\n\n";

  interface Seed { tex: string; envs: string[]; nodes: string[]; errors: Record<string, unknown>; patches?: unknown[]; unfixable?: unknown[]; refs?: typeof LIVE.cns.refs | typeof LIVE.dfm.refs; review?: unknown; weakening?: unknown[] }

  /** A run over a mini paper cut from a live one: its reference core restricted to the printed envs. */
  async function seed(s: Seed): Promise<{ runDir: string; state: StateJson }> {
    const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-render-rules-"));
    tmpDirs.push(repoRoot);
    const runDir = verifyRunDir(repoRoot, QID);
    const src = path.join(runDir, "source");
    await mkdir(src, { recursive: true });
    await writeFile(path.join(src, "main.tex"), s.tex, "utf8");
    const { envs, flat } = await buildEnvsJson(src, "main.tex");
    await writeEnvsArtifacts(runDir, envs, flat);
    const refs = s.refs ?? LIVE.cns.refs;
    const assumptions = refs.assumptions.filter((a) => s.envs.includes(a.source.env));
    const known = new Set(assumptions.map((a) => a.id));
    const statements = (refs.statements as Array<{ id: string; env: string; hypotheses?: string[]; depends_on?: string[] }>).filter((x) => s.envs.includes(x.env) && s.nodes.includes(x.id)).map((x) => ({
      ...x,
      ...(x.hypotheses ? { hypotheses: x.hypotheses.filter((h) => known.has(h)) } : {}),
      ...(x.depends_on ? { depends_on: x.depends_on.filter((h) => known.has(h) || s.nodes.includes(h)) } : {}),
    }));
    const REF = { qid: QID, target_estimand: "t", symbols: [], assumptions, definitions: [], statements };
    const { core: transcribed, violations } = materializeRefCore(RefCoreSchema.parse(REF), envs, flat.text);
    expect(violations).toEqual([]);
    const patches = {
      key_results: [s.nodes[0]],
      key_contribution: "c",
      patches: s.patches ?? [],
      unfixable: s.unfixable ?? [],
    };
    const { core } = applyPatchFile(transcribed, PatchFileSchema.parse(patches));
    const write = (rel: string, v: unknown): Promise<void> => writeFile(path.join(runDir, rel), JSON.stringify(v, null, 2), "utf8");
    await write("discovery/core_refs.json", REF);
    await write(VERIFY_FILES.coreTranscribed, transcribed);
    await write(VERIFY_FILES.coreJson, core);
    await write(VERIFY_FILES.patches, patches);
    if (s.review) await write(VERIFY_FILES.v15Review, s.review);
    const state = createVerifyInitialState(QID, {
      phase: "v1",
      source: { input: "main.tex", main_file: "main.tex", sha256: "x" },
      targets: null,
      core_sha256: null,
      v1_rounds: 1,
      v1_5_rounds: 1,
      findings: [],
      report_path: null,
      paper_errors: s.errors,
    } as never);
    if (s.weakening) state.verify!.weakening_repair = { status: "pending", at: "t", items: s.weakening } as never;
    return { runDir, state };
  }
  const logs: string[] = [];
  const annotate = (run: { runDir: string; state: StateJson }, compile: CompileTex = passed) => {
    logs.length = 0;
    return annotateRun({ runDir: run.runDir, qid: QID, state: run.state, when: "halt", compile, log: (m) => logs.push(m) });
  };
  const read = (runDir: string, rel: string): Promise<string> => readFile(path.join(runDir, rel), "utf8");
  const count = (t: string, macro: string): number => t.split(`\\${macro}{`).length - 1;
  /** The printed environment holding `\label{label}`, up to its `\end{…}` (and `extra` characters after). */
  const envText = (tex: string, label: string, extra = 0): string => {
    const at = tex.indexOf(`\\label{${label}}`);
    const begin = tex.lastIndexOf("\\begin{", at);
    const name = /^\\begin\{([^}]*)\}/.exec(tex.slice(begin))![1]!;
    const end = tex.indexOf(`\\end{${name}}`, at);
    return tex.slice(begin, end + `\\end{${name}}`.length + extra);
  };
  /** The `\macro{…}` groups of a text, their contents. */
  const groups = (tex: string, macro: string): string[] => {
    const out: string[] = [];
    for (let at = tex.indexOf(`\\${macro}{`); at >= 0; at = tex.indexOf(`\\${macro}{`, at + 1)) {
      let d = 0;
      for (let k = at + macro.length + 1; k < tex.length; k += 1) {
        if (tex[k] === "\\") k += 1;
        else if (tex[k] === "{") d += 1;
        else if (tex[k] === "}" && --d === 0) {
          out.push(tex.slice(at + macro.length + 2, k));
          break;
        }
      }
    }
    return out;
  };

  /** A live repair record without its text-format fields (added hypotheses, removed dependencies, text
   * proof edits): the replacement form keeps the rest. */
  const live = <T extends object>(p: T): Omit<T, "add_assumptions" | "remove_depends_on" | "proof_edits" | "insert_after" | "serves_check"> => {
    const { add_assumptions: _a, remove_depends_on: _r, proof_edits: _p, insert_after: _i, serves_check: _s, ...rest } = p as Record<string, unknown>;
    return rest as never;
  };
  type Op = { op: "replace"; unit: string; to?: string; tex: string };
  const C = LIVE.cns;
  /** The live repair of `node` as replacements `ops` (none: a proof note only). */
  const patch = (node: string, ops: Op[] = [], over: Record<string, unknown> = {}) => ({ ...live(C.patches.find((p) => p.node === node)!), ops, ...over });

  describe("R1: a result with no repair of its own beside a repaired one (live CNS Theorem 5.1 and Proposition D.9)", () => {
    const nodes = ["thm:dml-alt1", "prop:resid2"];
    /** D.9 restated with the hypothesis its proof needs, the noise premise rewritten in place. */
    const D9 =
      "Suppose Assumption~\\ref{assumption:cont} holds and\n$$\nE[\\{Y-\\gamma_0(W)\\}^2\\mid W]\\leq\\bar{\\sigma}^2,\\quad\\|\\hat{\\alpha}_{\\ell}\\|_{\\infty}\\leq\\bar{\\alpha}'.\n$$\nSuppose in addition that, for every fold $\\ell$, $\\hat{\\gamma}_{\\ell}-\\gamma_0\\in\\Gamma$ almost surely.";
    const GIVES_UP = "That every fitted $\\hat\\gamma_\\ell$ lies in $\\Gamma$: the paper allows black-box estimators with mean-square rates.";
    const mk = () =>
      seed({
        tex: `${PREAMBLE}\\section{Validity}\n${C.tex["thm:dml"]}\n\n\\appendix\n\\section{Proofs}\n${C.tex[C.resid2_env]}\n\n\\end{document}\n`,
        envs: ["thm:dml", C.resid2_env],
        nodes,
        errors: { "prop:resid2": C.paper_errors["prop:resid2"] },
        patches: [patch("prop:resid2", [{ op: "replace", unit: "prop:resid2/1/1", tex: D9 }], { given_up: GIVES_UP })],
      });

    it("the unrepaired theorem is not marked at all; D.9's replaced sentence red, its restatement blue", async () => {
      const run = await mk();
      const out = await annotate(run);
      expect(out.error).toBeNull();
      const tex = await read(run.runDir, "annotated/main.tex");
      const thm = envText(tex, "thm:dml");
      for (const m of ["vsOriginal", "vsCorrected", "vsProposed", "vsNote"]) expect(count(thm, m)).toBe(0);
      expect(thm).not.toMatch(/vsAdded|pageref|this result uses|added by the repair/u);
      const d9 = envText(tex, "prop:resid2");
      expect(groups(d9, "vsOriginal")).toHaveLength(1);
      expect(groups(d9, "vsOriginal")[0]).toMatch(/^Suppose Assumption/u);
      expect(groups(d9, "vsCorrected").join(" ")).toContain("for every fold $\\ell$, $\\hat{\\gamma}_{\\ell}-\\gamma_0\\in\\Gamma$ almost surely.");
    });
  });

  describe("R2: only the changed sentences / items (live CNS Lemma B.2, re-typed hypothesis list)", () => {
    it("the hypothesis list once and unmarked; the conclusion red and blue", async () => {
      // the conclusion ("Then … In summary, …") replaced; the hypothesis list untouched
      const CONCLUSION =
        "Put $A=\\|\\alpha_0^{\\min}\\|_{\\text{\\normalfont pr},2}$. Then\n$$[\\tilde cA-\\bar c]_+\\leq\\sigma\\leq\\bar c(1+A),\\quad\\kappa,\\zeta\\leq\\bar c\\{1+c(A^2\\vee1)\\}.$$\nIn summary,\n$$\\sigma<\\infty,\\quad\\kappa,\\zeta<\\infty.$$";
      const run = await seed({ tex: `${PREAMBLE}${C.tex["lemma:global"]}\n\\end{document}\n`, envs: ["lemma:global"], nodes: ["lem:global"], errors: { "lem:global": C.paper_errors["lem:global"] }, patches: [patch("lem:global", [{ op: "replace", unit: "lemma:global/1/7", to: "lemma:global/1/8", tex: CONCLUSION }])] });
      await annotate(run);
      const lem = envText(await read(run.runDir, "annotated/main.tex"), "lemma:global");
      const red = groups(lem, "vsOriginal");
      const blue = groups(lem, "vsCorrected");
      expect(red).toHaveLength(1);
      expect(blue).toHaveLength(1);
      expect(red[0]).toMatch(/^Then\n[\s\S]*In summary,[\s\S]*\$\$$/u);
      expect(blue[0]).toMatch(/^Put \$A=/u);
      expect(lem.match(/Further suppose there exist/gu)).toHaveLength(1);
      expect(lem.match(/Control of representer moments/gu)).toHaveLength(1);
      expect(blue[0]).not.toContain("\\begin{enumerate}");
    });
  });

  describe("R2b: adjacent replaced units are one block, never cutting a list (user decision 2026-09-29)", () => {
    const render = async (ops: Op[]): Promise<string> => {
      const run = await seed({ tex: `${PREAMBLE}${C.tex["lemma:global"]}\n\\end{document}\n`, envs: ["lemma:global"], nodes: ["lem:global"], errors: { "lem:global": C.paper_errors["lem:global"] }, patches: [patch("lem:global", ops)] });
      await annotate(run);
      return envText(await read(run.runDir, "annotated/main.tex"), "lemma:global");
    };
    it("two adjacent sentences replaced one by one read as one red and one blue block", async () => {
      const lem = await render([
        { op: "replace", unit: "lemma:global/1/7", tex: "Put $A=1$. Then $\\sigma\\leq 2$." },
        { op: "replace", unit: "lemma:global/1/8", tex: "In summary, $\\sigma<\\infty$." },
      ]);
      expect(groups(lem, "vsOriginal")).toHaveLength(1);
      expect(groups(lem, "vsCorrected")).toHaveLength(1);
      expect(groups(lem, "vsCorrected")[0]).toMatch(/^Put \$A=1\$\. Then [\s\S]*In summary/u);
    });
    it("items of a list, or a sentence and the item after it, are never joined: each block keeps the list whole", async () => {
      for (const ops of [
        [{ op: "replace" as const, unit: "lemma:global/1/4", tex: "First item, revised." }, { op: "replace" as const, unit: "lemma:global/1/5", tex: "Second item, revised." }],
        [{ op: "replace" as const, unit: "lemma:global/1/3", tex: "A revised lead sentence." }, { op: "replace" as const, unit: "lemma:global/1/4", tex: "First item, revised." }],
      ]) {
        const lem = await render(ops);
        expect(groups(lem, "vsOriginal")).toHaveLength(2);
        for (const g of [...groups(lem, "vsOriginal"), ...groups(lem, "vsCorrected")]) {
          expect(g).not.toMatch(/\\item|\\begin\{enumerate\}|\\end\{enumerate\}/u);
        }
        expect(lem.match(/\\begin\{enumerate\}/gu)).toHaveLength(1);
      }
    });
  });

  describe("R4: a result the paper prints no proof of (live CNS Theorem 5.2, local clause)", () => {
    const lemmas = ["lemma:local", "lemma:cont_local", "lemma:bounded_RR_local", "lemma:approx"];
    const proofs = lemmas.map((l) => `\\begin{proof}[of Lemma~\\ref{${l}}]\nThe bound follows.\n\\end{proof}`).join("\n\n");
    const nodes = ["thm:local-local-clause", "lem:local", "lem:cont-local", "lem:bounded-rr-local-alt1", "lem:approx"];
    const mk = () =>
      seed({
        tex: `${PREAMBLE}\\section{Validity}\n${C.tex["thm:local"]}\n\nText after the theorem.\n\n\\appendix\n\\section{Characterization}\n${lemmas.map((l) => C.tex[l]).join("\n\n")}\n\n\\section{Proofs of lemmas}\n\\subsection{Local functionals}\n${proofs}\n\n\\end{document}\n`,
        envs: ["thm:local", ...lemmas],
        nodes,
        errors: { "thm:local-local-clause": C.paper_errors["thm:local-local-clause"] },
        patches: [
          patch("thm:local-local-clause"),
          ...["lem:local", "lem:bounded-rr-local-alt1", "lem:approx"].map((node) => ({ node, corrected_statement: null, proof_note: "The bound follows from the normalizer bound." })),
        ],
      });

    it("right after the result, no heading: every lemma it uses, where the corrected proofs are by the paper's section numbers, never a file name", async () => {
      const run = await mk();
      const out = await annotate(run);
      expect(out.error).toBeNull();
      const tex = await read(run.runDir, "annotated/main.tex");
      const after = tex.slice(tex.indexOf("\\end{theorem}", tex.indexOf("\\label{thm:local}")));
      expect(after).toMatch(/^\\end\{theorem\}\n\\vsProof\{This result prints no proof; it follows from Lemmas~\\ref\{lemma:local\}, \\ref\{lemma:cont_local\}, \\ref\{lemma:bounded_RR_local\} and~\\ref\{lemma:approx\} \(the corrected proofs of Lemmas~\\ref\{lemma:local\}, \\ref\{lemma:bounded_RR_local\} and~\\ref\{lemma:approx\} are marked in Appendix~\\ref\{vsSec1\}\)\. \\vsLine /u);
      expect(after.slice(0, after.indexOf("Text after the theorem."))).not.toMatch(/\\texttt|\.tex|\\textbf\{Theorem/u);
      expect(tex).toContain("\\subsection{Local functionals}\\label{vsSec1}");
    });
  });
});

describe("annotated paper — an assumption no result uses after the repairs", () => {
  const TEX = [
    "\\documentclass{article}", // 1
    "\\begin{document}", // 2
    "\\begin{assumption}\\label{as:mom}", // 3
    "The score has a finite fourth moment, $E[\\psi^4] < \\infty$.", // 4
    "\\end{assumption}", // 5
    "\\begin{assumption}\\label{as:iid}", // 6
    "The data are i.i.d.", // 7
    "\\end{assumption}", // 8
    "\\begin{theorem}\\label{thm:a}", // 9
    "Under Assumptions~\\ref{as:mom} and~\\ref{as:iid}, $T_n \\to N(0,1)$.", // 10
    "\\end{theorem}", // 11
    "\\begin{theorem}\\label{thm:b}", // 12
    "Under Assumption~\\ref{as:iid}, $S_n \\to 0$.", // 13
    "\\end{theorem}", // 14
    "\\end{document}", // 15
  ].join("\n");
  const body = (line: number): string => TEX.split("\n")[line - 1]!;
  const loc = (label: string, from: number, env: string) => ({ file: "main.tex", from, to: from + 2, env, label });
  const env = (id: string, kind: string, from: number) => ({ id, kind, envName: kind, label: id, title: null, body: body(from + 1), proof: null, proofLines: null, section: null, lines: { file: "main.tex", from, to: from + 2 }, refs: [] });
  const transcribed = {
    qid: QID,
    symbols: [],
    assumptions: [
      { id: "ass:mom", condition: body(4), novel, tex_locator: loc("as:mom", 3, "assumption") },
      { id: "ass:iid", condition: body(7), novel, tex_locator: loc("as:iid", 6, "assumption") },
    ],
    definitions: [],
    statements: [
      { id: "thm:a", kind: "theorem", statement: body(10), depends_on: ["ass:mom", "ass:iid"], status: "to-prove", tex_locator: loc("thm:a", 9, "theorem") },
      { id: "thm:b", kind: "theorem", statement: body(13), depends_on: ["ass:iid"], status: "to-prove", tex_locator: loc("thm:b", 12, "theorem") },
    ],
    target_estimand: "t",
  } as unknown as Core;
  // Theorem thm:a states its own conditions and drops both assumptions; thm:b still uses as:iid.
  const tex = "Suppose $E[\\psi^2] < \\infty$ and the data are i.i.d. Then $T_n \\to N(0,1)$.";
  const PATCHES = PatchFileSchema.parse({
    key_results: ["thm:a"],
    key_contribution: "c",
    patches: [{ node: "thm:a", corrected_statement: tex, ops: [{ op: "replace", unit: "thm:a/1/1", tex }], drops: ["ass:mom", "ass:iid"], proof_note: "p" }],
    unfixable: [],
  });

  it("is crossed out in red where the paper prints it, with a note naming the result that now states its conditions; one another result still uses is left as printed", () => {
    const { core } = applyPatchFile(transcribed, PATCHES);
    expect(core.assumptions.map((a) => a.id)).toEqual(["ass:iid"]);
    const plan = planAnnotations({
      files: { "main.tex": TEX },
      envs: { main_file: "main.tex", files: ["main.tex"], newtheorem: {}, bibliography: [], envs: [env("as:mom", "assumption", 3), env("as:iid", "assumption", 6), env("thm:a", "theorem", 9), env("thm:b", "theorem", 12)] } as never,
      flatText: TEX,
      lineMap: TEX.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 })),
      refs: null,
      transcribed,
      core,
      patches: PATCHES,
      paperErrors: { "thm:a": { detail: "the fourth moment is not needed", witness: "w" } },
      findings: [],
      review: null,
    });
    const out = applyEdits(TEX, plan.edits["main.tex"] ?? []);
    expect(out).toContain(`\\vsStruck{${body(4)}} \\vsNote{No result uses this assumption after the repairs: Theorem~\\ref{thm:a} now states the conditions it uses.}`);
    // a command with an optional argument (a page citation) cannot be struck through: red only
    expect([struckMacro("as in \\citet[Assumption 2]{X}"), struckMacro("as in \\citet{X}")]).toEqual(["vsStruckRed", "vsStruck"]);
    expect(out).toContain(`\\label{as:iid}\n${body(7)}\n\\end{assumption}`);
    expect(plan.records.filter((r) => r.kind === "no longer used").map((r) => r.node)).toEqual(["ass:mom"]);
    expect(plan.defects).toEqual([]);
  });
});

describe("the annotation's input", () => {
  it("is built once for V6 and the halts: a symbol reading only while its verdict is confirmed, the rejected suggestions named", () => {
    const core = { qid: "q", symbols: [], assumptions: [], definitions: [], statements: [] } as unknown as Core;
    const review = { verdict: "PASS", summary: "", nodes: [], symbols: [{ name: "\\alpha" }, { name: "\\beta" }] } as unknown as V15Review;
    const records = { refs: null, patches: null, flatText: "flat", lineMap: [] };
    const verify = (over: Partial<VerifyState>): VerifyState => ({ phase: "v6", source: { input: "m.tex", main_file: "m.tex", sha256: "s" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 1, findings: [], report_path: null, ...over });
    const confirmed = annotationInput({ envs: { main_file: "m.tex" } as never, verify: verify({ confirmed_symbols: { "\\alpha": "h" }, suggestion_rejections: { "thm:clt": 2 } }), core, transcribed: null, review, records });
    expect(confirmed.review?.symbols?.map((s) => s.name)).toEqual(["\\alpha"]);
    expect([...confirmed.suggestionRejected!]).toEqual(["thm:clt"]);
    expect(confirmed).toMatchObject({ core, transcribed: core, flatText: "flat", patches: null, paperErrors: {} });
    // no confirmation record yet (an older run): the review as written
    expect(annotationInput({ envs: { main_file: "m.tex" } as never, verify: verify({}), core, transcribed: null, review, records }).review).toBe(review);
  });
});

describe("a suggestion stored as one line", () => {
  it("is set as ASCII TeX: its parts joined by a semicolon", async () => {
    const { suggestionSummaryTex } = await import("../../src/verify/annotated_paper.js");
    expect(suggestionSummaryTex("corrected statement: $x\\leq1$ \u00b7 gives up: the case $x>1$")).toBe("corrected statement: $x\\leq1$; gives up: the case $x>1$");
    // a "·" inside the model's text is not a separator: left for the render check to refuse
    expect(suggestionSummaryTex("corrected statement: $a \u00b7 b\\leq1$ \u00b7 corollary 1: $c$")).toBe("corrected statement: $a \u00b7 b\\leq1$; corollary 1: $c$");
  });
});

