import { existsSync } from "node:fs";
import { cp, lstat, mkdir, mkdtemp, readdir, readFile, rename, rm, symlink, writeFile } from "node:fs/promises";
import { FILE_SYMLINKS } from "../platform.js";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { findExecutable } from "../../src/shared/program.js";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { verifyRunDir } from "../../src/paths.js";
import { createVerifyInitialState } from "../../src/state.js";
import type { StateJson } from "../../src/types.js";
import { compileTex, planAnnotations, readSourceTex, type CompileTex } from "../../src/verify/annotated_paper.js";
import { readAnnotationRecords } from "../../src/verify/annotate_run.js";
import { loadCatalog } from "../../src/toolkit/init.js";
import { isBlockingTodo, renderTodo, userPathIn, writeBundle, type TodoItem } from "../../src/verify/bundle.js";
import { currentStatements, nodeTags, renderMatch } from "../../src/verify/bundle_match.js";
import { buildF4Seal, checkF4Seal, runSealCli, sha256, type F4Seal } from "../../src/verify/f4_seal.js";
import type { PageSnapshot } from "../../src/ui/page_snapshot.js";
import { createEmptyGraph } from "../../src/graph/store.js";
import { splitCorollaryId } from "../../src/verify/core_graph.js";
import { sha256File } from "../../src/verify/core_hash.js";
import { applyPatchFile, PatchFileSchema } from "../../src/verify/patches.js";
import { materializeRefCore, RefCoreSchema } from "../../src/verify/ref_core.js";
import { evidenceOnFile, parseReportArgs } from "../../src/verify/report_cli.js";
import { axiomWords, formalStatus, handNumber, renderPlainSections, resultNames } from "../../src/verify/report_plain.js";
import type { ReportRow, VerifyReportJson } from "../../src/verify/report.js";
import { makeStageV6 } from "../../src/verify/stage_v6_report.js";
import { buildEnvsJson, writeEnvsArtifacts } from "../../src/verify/tex_envs.js";
import { VERIFY_FILES, type EnvsJson, type VerifyFinding } from "../../src/verify/types.js";

const FIXTURE = path.join(path.dirname(fileURLToPath(import.meta.url)), "fixtures", "annot_paper");
const QID = "annot_paper";
const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});
const hasPdflatex = findExecutable("pdflatex", { nativeOnly: true }) !== null;

const novel = { flag: true, justification: "the paper's" };
const REF = {
  qid: QID,
  target_estimand: "the rate",
  symbols: [],
  assumptions: [{ id: "ass:overlap", source: { env: "thm:rate", sentences: [1, 1] }, novel }],
  definitions: [],
  statements: [
    { id: "thm:rate", kind: "theorem", env: "thm:rate", depends_on: ["ass:overlap"], hypotheses: ["ass:overlap"] },
    { id: "lem:bound", kind: "lemma", env: "lem:bound" },
    { id: "thm:clt", kind: "theorem", env: "thm:clt" },
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
      proof_note: "The bias term is of order $h^2$.",
      accepted_weakening: true,
      given_up: "the root-$n$ rate",
    },
  ],
  unfixable: [{ node: "thm:clt", reason: "no CLT holds without a moment condition" }],
};
const FINDINGS: VerifyFinding[] = [
  {
    node: "thm:rate", stage: "V1.5", kind: "refuted", detail: "The rate is $n^{-1/3}$, not $n^{-1/2}$.", witness: "Take $e(x)=x$.", at: "t",
    patch: { corrected_statement: PATCHES.patches[0]!.corrected_statement, proof_note: "The bias term is of order $h^2$.", confirmed: true, narrowed: "the root-$n$ rate" },
  },
  { node: "thm:clt", stage: "V1.5", kind: "refuted", detail: "The CLT fails without finite variance.", witness: "Cauchy samples", at: "t", suggested_repair: "assume finite variance", suggestion_declined: "not the paper's point" },
];

const COR = { title: "the Gaussian case", statement: "If the design is Gaussian, the estimator of Theorem~\\ref{thm:rate} converges at rate $n^{-1/2}$.", follows: "Under a Gaussian design the bias term of Theorem~\\ref{thm:rate} vanishes." };
const COR_ID = splitCorollaryId("thm:rate", COR.statement);
/** Conditions the verified statements carry beyond the printed text: the referee's on a lemma, the
 * owner's on the repaired theorem — one of them in the words its repair already states — and one on
 * the corollary a repair splits off. */
const CONDITIONS = [
  { id: "ass:bk-1", on: "lem:bound", condition: "$X$ is measurable" },
  { id: "ass:bk-owner-1", on: "thm:rate", condition: "The sample is i.i.d." },
  { id: "ass:bk-owner-2", on: "thm:rate", condition: "Assume the propensity score is  bounded away from zero." },
  { id: "ass:bk-2", on: COR_ID, condition: "The design has full rank." },
];
/** The same repair and suggestion, each splitting a corollary off its result. */
const SPLIT = {
  ...PATCHES,
  patches: [{ ...PATCHES.patches[0]!, corollaries: [COR] }],
  unfixable: [{ ...PATCHES.unfixable[0]!, suggested_repair: { corrected_statement: "Assume finite variance. The statistic $T_n$ is tight.", proof_note: "Chebyshev.", given_up: "asymptotic normality", corollaries: [{ statement: "If the sample is Gaussian, $T_n$ is normal.", follows: "A sum of Gaussians is Gaussian." }] }, declined: "not the paper's point" }],
};

/** A run that stopped at V1.5 (no Lean): one result repaired by a weaker statement, one refuted with
 * its suggested repair declined, one reading pinned. `split`: the repair and the suggestion each split
 * a corollary off (`SPLIT`); `preamble`: lines added to the paper's preamble; `conditions`: conditions
 * added beyond the printed text (`CONDITIONS`); `printedProof`: a proof of the repaired theorem, printed after it;
 * `amended`: that proof's repair, the whole amended proof, by a step op that cannot be placed. */
async function seedRun(opts: { split?: boolean; preamble?: string; printedProof?: string; amended?: string; undetermined?: boolean; rejected?: "unconfirmed" | "refuted"; conditions?: boolean; conditionText?: Record<string, string> } = {}): Promise<{ repoRoot: string; runDir: string; state: StateJson }> {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-bundle-"));
  tmpDirs.push(repoRoot);
  const runDir = verifyRunDir(repoRoot, QID);
  const src = path.join(runDir, "source");
  await mkdir(runDir, { recursive: true });
  await cp(FIXTURE, src, { recursive: true });
  if (opts.preamble) await writeFile(path.join(src, "main.tex"), (await readFile(path.join(src, "main.tex"), "utf8")).replace("\n\\begin{document}", `${opts.preamble}\n\n\\begin{document}`), "utf8");
  if (opts.printedProof) await writeFile(path.join(src, "main.tex"), (await readFile(path.join(src, "main.tex"), "utf8")).replace("\\end{thm}\n", `\\end{thm}\n${opts.printedProof}\n`), "utf8");
  const patches = opts.amended
    ? { ...PATCHES, patches: [{ ...PATCHES.patches[0]!, proof_note: opts.amended, ops: [...PATCHES.patches[0]!.ops, { op: "replace" as const, unit: "thm:rate/proof/1/9", tex: "x" }] }] }
    : opts.split ? SPLIT : PATCHES;
  // `undetermined`: thm:clt is no error — the paper leaves it undetermined, and nobody repaired it.
  // `rejected`: thm:rate is left undetermined by the paper, and the repair on file for it was rejected —
  // not confirmed, or refuted by the referee (a witness against the repair, not the printed statement).
  const und = { node: "thm:rate", stage: "V1.5", kind: "unresolved" as const, undetermined: true, witness: null, at: "t" };
  const findings = opts.rejected
    ? [
        { ...und, detail: "The norm of the rate is not named.", patch: { ...FINDINGS[0]!.patch!, confirmed: false } },
        ...(opts.rejected === "refuted" ? [{ ...und, detail: "the repair tried for it was refuted: the repaired rate fails", witness: "Take $e(x)=x$." }] : []),
        FINDINGS[1]!,
      ]
    : opts.undetermined
    ? [FINDINGS[0]!, { node: "thm:clt", stage: "V1.5", kind: "unresolved" as const, undetermined: true, detail: "The mode of convergence is not named.", witness: null, at: "t", descoped: true }]
    : opts.split ? FINDINGS.map((f) => (f.node === "thm:rate" ? { ...f, patch: { ...f.patch!, corollaries: [COR_ID] } } : f)) : FINDINGS;
  const { envs, flat } = await buildEnvsJson(src, "main.tex");
  await writeEnvsArtifacts(runDir, envs, flat);
  const { core: transcribed, violations } = materializeRefCore(RefCoreSchema.parse(REF), envs, flat.text);
  expect(violations).toEqual([]);
  const { core } = applyPatchFile(transcribed, PatchFileSchema.parse(patches));
  core.assumptions.push({
    id: "ass:pin-1",
    kind: "regularity",
    condition: "$n \\ge 2$",
    bookkeeping: { flag: true, added_by: "V1.5", reason: "pins reading of ass:overlap: the proof uses it" },
  } as Core["assumptions"][number]);
  core.statements.find((s) => s.id === "thm:rate")!.depends_on.push("ass:pin-1");
  if (opts.conditions) for (const c of CONDITIONS.map((x) => ({ ...x, condition: opts.conditionText?.[x.id] ?? x.condition }))) {
    core.assumptions.push({ id: c.id, kind: "regularity", condition: c.condition, bookkeeping: { flag: true, added_by: c.id.includes("owner") ? "owner" : "V1.5", reason: "a side condition" } } as Core["assumptions"][number]);
    core.statements.find((s) => s.id === c.on)?.depends_on.push(c.id);
  }
  const write = (rel: string, v: unknown): Promise<void> => writeFile(path.join(runDir, rel), JSON.stringify(v, null, 2), "utf8");
  await write("discovery/core_refs.json", REF);
  await write(VERIFY_FILES.coreTranscribed, transcribed);
  await write(VERIFY_FILES.coreJson, core);
  await write(VERIFY_FILES.patches, patches);
  const state = createVerifyInitialState(QID, {
    phase: "v6",
    source: { input: "main.tex", main_file: "main.tex", sha256: "deadbeef" },
    targets: null,
    core_sha256: await sha256File(path.join(runDir, VERIFY_FILES.coreJson)),
    transcribed_sha256: await sha256File(path.join(runDir, VERIFY_FILES.coreTranscribed)),
    v1_rounds: 1,
    v1_5_rounds: 1,
    findings,
    report_path: null,
    paper_errors: { "thm:rate": opts.rejected ? { detail: "The norm of the rate is not named.", witness: null, undetermined: true } : { detail: "The rate is $n^{-1/3}$.", witness: "Take $e(x)=x$." }, "thm:clt": opts.undetermined ? { detail: "The mode of convergence is not named.", witness: null, undetermined: true } : { detail: "The CLT fails.", witness: "Cauchy samples" } },
  } as never);
  state.stage_completed = "1.5";
  return { repoRoot, runDir, state };
}

const passed: CompileTex = async () => ({ status: "passed", tool: "pdflatex", pdf: "main.pdf", log_tail: "", reason: "" });
const runV6 = async (run: { repoRoot: string; runDir: string; state: StateJson }, deps: Parameters<typeof makeStageV6>[0] = {}): Promise<void> => {
  const stage = makeStageV6({ collectLeanEvidence: async () => { throw new Error("no Lean on an early stop"); }, compileTex: passed, ...deps });
  const res = await stage({ repoRoot: run.repoRoot, qid: QID, runDir: run.runDir, state: run.state, deps: { runCodex: (() => { throw new Error("no model"); }) as never }, dryRun: true, log: () => {} });
  expect(res.status).toBe("completed");
};
const files = async (dir: string, rel = ""): Promise<string[]> => {
  const out: string[] = [];
  for (const e of await readdir(path.join(dir, rel), { withFileTypes: true })) {
    if (e.isDirectory()) out.push(...(await files(dir, `${rel}${e.name}/`)));
    else out.push(`${rel}${e.name}`);
  }
  return out.sort();
};

describe("the corrected-paper bundle (V6)", () => {
  it("corrected_paper/ is the author's source with the corrections written in: no macro, colour or word of the review", async () => {
    const run = await seedRun();
    await writeFile(path.join(run.runDir, "state.json"), JSON.stringify(run.state), "utf8");
    await runV6(run);
    const read = (rel: string): Promise<string> => readFile(path.join(run.runDir, "bundle", rel), "utf8");
    const main = await read("corrected_paper/main.tex");
    const sec = await read("corrected_paper/sec/results.tex");
    for (const t of [main, sec]) expect(t).not.toMatch(/\\vs[A-Z]|TheoremChecker|xcolor|Corrected:|Original:/u);
    expect(main).toContain("The estimator converges at rate $n^{-1/3}$.");
    expect(main).not.toContain("$n^{-1/2}$");
    // the author's preamble, comment and layout stand
    expect(main).toContain("\\documentclass{article}\n\\usepackage{amsmath,amsthm}");
    expect(main).toContain("% the paper's own comment");
    expect(main).toContain("\\input{sec/results}");
    // the pinned reading: a remark of the paper at its statement
    expect(main).toMatch(/\\end\{thm\}\n\n\\noindent\\textit\{Remark\.\} \$n \\ge 2\$\./u);
    // the refuted result with no repair is printed as in the original — and listed, never marked in the paper
    expect(sec).toBe(await readFile(path.join(FIXTURE, "sec/results.tex"), "utf8"));
    const todo = await read("corrected_paper/TODO.md");
    expect(todo).toContain("## Results that are not established");
    expect(todo).toMatch(/`sec\/results\.tex:\d+` — Theorem labelled `thm:clt`: the review refuted this result and no repair was adopted/u);
    // the prose around the results is the authors': nothing of it is listed
    expect(todo).not.toMatch(/abstract|refers to/u);
    // nothing of the review is copied in
    expect(await files(path.join(run.runDir, "bundle", "corrected_paper"))).toEqual(["TODO.md", "main.tex", "sec/results.tex"]);
    expect(await files(path.join(run.runDir, "bundle"))).toEqual(["MATCH.md", "README.md", "REPORT.md", "bundle.json", "corrected_paper/TODO.md", "corrected_paper/main.tex", "corrected_paper/sec/results.tex", "page/page.json"]);
    // the page snapshot: the results with what their drawers show, the paper as drawn, nothing of a run at work
    const text = await read("page/page.json");
    const page = JSON.parse(text) as PageSnapshot;
    const json = JSON.parse(await readFile(path.join(run.runDir, VERIFY_FILES.reportJson), "utf8")) as VerifyReportJson;
    expect(Object.keys(page)).toEqual(["schema", "slug", "title", "authors", "verdict", "buckets", "tokens", "main", "leanDir", "results", "leanDefs", "places", "paper", "texHtml"]);
    expect(page).toMatchObject({ schema: 1, slug: QID, main: "main.tex", leanDir: null, verdict: json.verdict });
    expect(page.results.find((r) => r.id === "thm:rate")).toMatchObject({ kind: "theorem", state: "error", repair: "statement", key: true, paperError: { detail: "The rate is $n^{-1/3}$." } });
    expect(page.results.find((r) => r.id === "thm:rate")).not.toHaveProperty("needs");
    expect(page.texHtml["The rate is $n^{-1/3}$."]).toContain("katex");
    expect(page.paper!.html).toContain("converges at rate");
    expect(page.paper!.comments.length).toBeGreaterThan(0);
    expect(page.paper).toMatchObject({ pdf: "corrected_paper/main.pdf", pages: {} });
    expect(json.bundle!.page).toBe("page/page.json");
    expect(json.bundle!.paper.dir).toBe("corrected_paper");
    // no path of this machine, and the same bytes when the report is written again
    for (const p of [run.repoRoot, os.tmpdir(), os.homedir(), "/api/"]) expect(text).not.toContain(p);
    await runV6(run);
    expect(await read("page/page.json")).toBe(text);
  });

  it.skipIf(!FILE_SYMLINKS)("a linked source file is copied as the file itself, so the seal can name it", async () => {
    const run = await seedRun();
    const outside = await mkdtemp(path.join(os.tmpdir(), "verify-bundle-link-"));
    tmpDirs.push(outside);
    const sec = path.join(run.runDir, "source", "sec", "results.tex");
    await rename(sec, path.join(outside, "results.tex"));
    await symlink(path.join(outside, "results.tex"), sec);
    await runV6(run);
    const fixture = await readFile(path.join(FIXTURE, "sec/results.tex"), "utf8");
    // the annotated paper, written first, went through a copy of the source too: the link's target
    // (the source itself) is as the author left it
    expect(await readFile(path.join(outside, "results.tex"), "utf8")).toBe(fixture);
    for (const copied of [path.join(run.runDir, "bundle", "corrected_paper", "sec", "results.tex"), path.join(run.runDir, "annotated", "sec", "results.tex")]) {
      expect((await lstat(copied)).isSymbolicLink()).toBe(false);
    }
    expect(await readFile(path.join(run.runDir, "bundle", "corrected_paper", "sec", "results.tex"), "utf8")).toBe(fixture);
  });

  it("the report leads with what was wrong and what was done, in the paper's own names; the appendix keeps the ids", async () => {
    const run = await seedRun();
    await runV6(run);
    const md = await readFile(path.join(run.runDir, "report.md"), "utf8");
    const json = JSON.parse(await readFile(path.join(run.runDir, "report.json"), "utf8")) as VerifyReportJson;
    expect(json.bundle).toMatchObject({ dir: "bundle", paper: { main: "main.tex", pdf: "main.pdf", compile: { status: "passed" } }, lean: null });
    expect(json.bundle!.todo.blocking).toBeGreaterThan(0);
    expect(json.names).toMatchObject({ "thm:rate": "Theorem (Rate)", "thm:clt": "Theorem labelled `thm:clt`" });
    const [plain, appendix] = md.split("\n# Technical appendix\n");
    expect(plain).toContain("## What was wrong and what was done");
    expect(plain).toContain("### Theorem (Rate) — corrected; the corrected statement is weaker");
    expect(plain).toContain("- **Counterexample.** Take $e(x)=x$.");
    expect(plain).toContain("- **Correction.** Assume the propensity score is bounded away from zero. The estimator converges at rate $n^{-1/3}$. It is efficient.");
    expect(plain).toContain("- **What the correction gives up.** the root-$n$ rate (The paper's owner accepted the weaker statement.)");
    expect(plain).toContain("### Theorem labelled `thm:clt` — not repaired");
    expect(plain).toContain("- **Suggested repair (not applied).** assume finite variance");
    expect(plain).toContain("- **Owner's decision.** Declined: not the paper's point");
    expect(plain).toContain("## Clarifications (not errors)");
    expect(plain).toContain("- **Theorem (Rate).** $n \\ge 2$");
    expect(plain).toContain("## What was proved in Lean, and what was not");
    expect(plain).toContain("## The corrected paper");
    // no run identifier, stage or bucket in the plain part
    expect(plain).not.toMatch(/`thm:rate`|ass:pin-1|V1\.5|not_checked|bucket/u);
    expect(appendix).toContain("`thm:rate`");
    expect(appendix).toContain("## Annotated paper");
    expect(await readFile(path.join(run.runDir, "bundle", "REPORT.md"), "utf8")).toBe(md);
  });

  it("a condition added beyond the printed text is the last paragraph of the statement carrying it, once; a pinned reading stays a remark", async () => {
    const run = await seedRun({ conditions: true, split: true, preamble: "\\newtheorem{cor}[thm]{Corollary}" });
    await runV6(run);
    const read = (rel: string): Promise<string> => readFile(path.join(run.runDir, rel), "utf8");
    const main = await read("bundle/corrected_paper/main.tex");
    // the owner's, in the repaired theorem; the one its corrected statement already states is not written again
    expect(main).toMatch(/It is efficient\.\n\n\\emph\{Additional condition\.\} The sample is i\.i\.d\.\n\\end\{thm\}\n\n\\noindent\\textit\{Remark\.\} \$n \\ge 2\$\./u);
    expect(main.split("bounded away from zero").length).toBe(2);
    // the referee's, in a lemma printed as in the original
    expect(main).toContain("Suppose $X$ is bounded. Then $E[X]$ exists.\n\n\\emph{Additional condition.} $X$ is measurable.\n\\end{lem}");
    // the corollary's, in its own statement
    expect(main).toContain(`${COR.statement}\n\n\\emph{Additional condition.} The design has full rank.\n\\end{cor}`);
    expect(main).not.toMatch(/\\vs[A-Z]|Condition added/u);
    expect(await read("bundle/corrected_paper/TODO.md")).not.toContain("## Corrections not written into the paper");
    // the annotated paper: a note at the end of each result, nothing printed marked for it
    const annotated = await read("annotated/main.tex");
    expect(annotated).toContain("\\vsConditionOwner{The sample is i.i.d.}\\end{thm}\\vsReading{$n \\ge 2$");
    expect(annotated).toContain("Suppose $X$ is bounded. Then $E[X]$ exists.\n\\vsCondition{$X$ is measurable}\\end{lem}");
    expect(annotated).toContain("\\vsPar \\emph{Additional condition.} The design has full rank.");
    expect([annotated.split("\\vsCondition{").length, annotated.split("\\vsConditionOwner{").length]).toEqual([2, 2]);
    const index = await read("annotated/ANNOTATIONS.md");
    expect(index).toMatch(/\| `lem:bound` \| main\.tex:\d+ \| condition added \| env-end \| ass:bk-1: \$X\$ is measurable \|/u);
    expect(index).toMatch(/\| `thm:rate` \| main\.tex:\d+ \| condition added \| env-end \| ass:bk-owner-1: The sample is i\.i\.d\. \|/u);
    expect(index).not.toContain("ass:bk-owner-2");
  });

  it("a condition whose words stand inside another sentence of the statement is still written", async () => {
    const run = await seedRun({ conditions: true, split: true, preamble: "\\newtheorem{cor}[thm]{Corollary}", conditionText: { "ass:bk-1": "$X$ is bounded" } });
    await runV6(run);
    // "Suppose $X$ is bounded." holds the words, and is another sentence: nothing is dropped
    expect(await readFile(path.join(run.runDir, "bundle/corrected_paper/main.tex"), "utf8")).toContain("\\emph{Additional condition.} $X$ is bounded.\n\\end{lem}");
  });

  it("a corollary a repair split off: a corollary of the paper after its result, in the paper's environment and labelled; its numbering and a suggestion's corollaries are listed", async () => {
    const run = await seedRun({ split: true, preamble: "\\newtheorem{cor}[thm]{Corollary}" });
    await runV6(run);
    const read = (rel: string): Promise<string> => readFile(path.join(run.runDir, "bundle", rel), "utf8");
    const main = await read("corrected_paper/main.tex");
    const cor = `\\begin{cor}[the Gaussian case]\\label{${COR_ID}}\n${COR.statement}\n\\end{cor}\n\n\\begin{proof}\n${COR.follows}\n\\end{proof}`;
    expect(main).toContain(cor);
    // after its result, that result's remark and proof; before the next result
    expect(main.indexOf(cor)).toBeGreaterThan(main.indexOf("\\begin{proof}\nThe bias term is of order $h^2$.\n\\end{proof}"));
    expect(main.indexOf(cor)).toBeLessThan(main.indexOf("\\begin{lem}"));
    expect(main).not.toMatch(/\\vs[A-Z]|Why it follows|split/u);
    // the suggestion that was not adopted writes nothing into the paper
    expect(await read("corrected_paper/sec/results.tex")).toBe(await readFile(path.join(FIXTURE, "sec/results.tex"), "utf8"));
    const todo = await read("corrected_paper/TODO.md");
    expect(todo).toMatch(/## Numbers and labels \(to check\)[\s\S]*`main\.tex:\d+` — Corollary 1 of Theorem \(Rate\): it is a new numbered `cor`: the numbers of the results after it that share its counter shift by one/u);
    expect(todo).toMatch(/Theorem labelled `thm:clt`: the review refuted this result and no repair was adopted; it is printed as in the original; the suggested repair, which was not adopted, would state it with 1 proposition: it is not written into the paper/u);
    const line = Number(/`main\.tex:(\d+)` — Corollary 1 of Theorem \(Rate\)/u.exec(todo)![1]);
    expect(main.split("\n")[line - 1]).toContain("\\begin{cor}");
  });

  it("a whole corrected proof replaces the printed proof in the corrected paper, under its title, once; the annotated paper keeps both; a label it drops is only to check", async () => {
    const printed = "\\begin{proof}[Proof of Theorem~\\ref{thm:rate}]\nBy the variance bound,\n\\begin{equation}\\label{eq:var} v = O(n^{-1}).\\end{equation}\n\\end{proof}";
    const amended = "By the variance bound and the bias bound, the error is $O(n^{-1/3})$.";
    const run = await seedRun({ printedProof: printed, amended });
    await runV6(run);
    const read = (rel: string): Promise<string> => readFile(path.join(run.runDir, rel), "utf8");
    const main = await read("bundle/corrected_paper/main.tex");
    expect(main).toContain(`\\begin{proof}[Proof of Theorem~\\ref{thm:rate}]\n${amended}\n\\end{proof}`);
    expect(main.split("\\begin{proof}").length).toBe(2);
    expect(main).not.toMatch(/O\(n\^\{-1\}\)|eq:var|\\vs[A-Z]/u);
    const todo = await read("bundle/corrected_paper/TODO.md");
    expect(todo).not.toContain("## Two proofs of one result");
    expect(todo).toMatch(/## Numbers and labels \(to check\)[\s\S]*`main\.tex:\d+` — Theorem \(Rate\): the equation labelled `eq:var` was in the printed proof, which the corrected proof replaces, and is not in it/u);
    const line = Number(/`main\.tex:(\d+)` — Theorem \(Rate\): the equation labelled/u.exec(todo)![1]);
    expect(main.split("\n")[line - 1]).toContain("\\begin{proof}[Proof of Theorem~\\ref{thm:rate}]");
    const annotated = await read("annotated/main.tex");
    expect(annotated).toContain("v = O(n^{-1})");
    expect(annotated).toMatch(/\\end\{proof\}\n\\vsProof\{[^\n]*the error is \$O\(n\^\{-1\/3\}\)\$\.\}/u);
  });

  it("a proof note beside a printed proof that is not a whole proof replaces nothing: both proofs stay, and the TODO blocks on it", async () => {
    const printed = "\\begin{proof}[Proof of Theorem~\\ref{thm:rate}]\nBy the variance bound.\n\\end{proof}";
    const run = await seedRun({ printedProof: printed });
    await runV6(run);
    const main = await readFile(path.join(run.runDir, "bundle/corrected_paper/main.tex"), "utf8");
    expect(main).toContain(`${printed}\n\n\\begin{proof}\nThe bias term is of order $h^2$.\n\\end{proof}`);
    const todo = await readFile(path.join(run.runDir, "bundle/corrected_paper/TODO.md"), "utf8");
    expect(todo).toMatch(/## Two proofs of one result\n\n[^\n]*\n\n- `main\.tex:\d+` — Theorem \(Rate\): the corrected proof follows the printed proof/u);
  });

  it("without a corollary environment the corollary and its proof are paragraphs of the paper, and nothing is renumbered", async () => {
    const run = await seedRun({ split: true });
    await runV6(run);
    const main = await readFile(path.join(run.runDir, "bundle", "corrected_paper", "main.tex"), "utf8");
    expect(main).toContain(`\\noindent\\textit{Corollary (the Gaussian case).} ${COR.statement}\n\n\\begin{proof}\n${COR.follows}\n\\end{proof}`);
    expect(main).not.toContain(COR_ID);
    expect(await readFile(path.join(run.runDir, "bundle", "corrected_paper", "TODO.md"), "utf8")).not.toContain("## Numbers and labels");
  });

  it("the report and MATCH.md set a corollary after its parent, named after it; the parent's entry says the repair split it and that nothing moved to a corollary is given up", async () => {
    const run = await seedRun({ split: true });
    await runV6(run);
    const json = JSON.parse(await readFile(path.join(run.runDir, "report.json"), "utf8")) as VerifyReportJson;
    expect(json.names).toMatchObject({ "thm:rate": "Theorem (Rate)", [COR_ID]: "Corollary 1 of Theorem (Rate)" });
    expect(json.results.map((r) => r.node_id).slice(0, 2)).toEqual(["thm:rate", COR_ID]);
    const plain = (await readFile(path.join(run.runDir, "report.md"), "utf8")).split("\n# Technical appendix\n")[0]!;
    expect(plain).toContain("5 result(s) of the paper were examined, and 1 corollary a correction split off them.");
    expect(plain).toContain("- **Split.** The correction states this result as the statement above and 1 corollary, each a result of its own. Nothing moved to one of them counts as given up.");
    expect(plain).toContain(`  - **Corollary 1 of Theorem (Rate).** ${COR.statement} Formal check: not formalized: the run stopped before the Lean formalization.`);
    expect(plain.indexOf("- **Split.**")).toBeGreaterThan(plain.indexOf("### Theorem (Rate) — corrected"));
    expect(plain.indexOf("- **Split.**")).toBeLessThan(plain.indexOf("### Theorem labelled `thm:clt`"));
    expect(plain).not.toContain(COR_ID);
    const match = await readFile(path.join(run.runDir, "bundle", "MATCH.md"), "utf8");
    expect(match).toContain("The correction states this result with 1 corollary, set out after it.");
    expect(match).toContain(`## Corollary 1 of Theorem (Rate)\n\n**Statement (a corollary the correction of Theorem (Rate) splits off; the original paper does not state it).** ${COR.statement}`);
    expect(match.indexOf("## Corollary 1 of Theorem (Rate)")).toBeGreaterThan(match.indexOf("## Theorem (Rate)"));
    expect(match.indexOf("## Corollary 1 of Theorem (Rate)")).toBeLessThan(match.indexOf("## Lemma"));
    expect(match.split("## Identifiers")[1]).toContain(`| Corollary 1 of Theorem (Rate) | \`${COR_ID}\` | — |`);
  });

  it("is rebuilt from scratch: a second V6 gives the same bundle", async () => {
    const run = await seedRun();
    await runV6(run);
    const snap = async (): Promise<Record<string, string>> => Object.fromEntries(await Promise.all((await files(path.join(run.runDir, "bundle"))).map(async (f) => [f, await readFile(path.join(run.runDir, "bundle", f), "utf8")] as const)));
    const first = await snap();
    await writeFile(path.join(run.runDir, "bundle", "stale.txt"), "x");
    await runV6(run);
    expect(await snap()).toEqual(first);
  });

  it("with an output directory the report and bundle go there and the run is left as it was", async () => {
    const run = await seedRun();
    const before = await files(run.runDir);
    const out = await mkdtemp(path.join(os.tmpdir(), "verify-bundle-out-"));
    tmpDirs.push(out);
    await runV6(run, { outDir: out });
    expect(await files(run.runDir)).toEqual(before);
    expect(run.state.verify!.report_path).toBeNull();
    expect((await files(out)).filter((f) => !f.startsWith("bundle/"))).toEqual(["bundle_compile.json", "report.json", "report.md"]);
    expect(existsSync(path.join(out, "bundle", "corrected_paper", "main.tex"))).toBe(true);
  });

  it("a compile failure is the first TODO item and never fails the stage", async () => {
    const run = await seedRun();
    // the corrected paper alone fails: the unmodified source (compiled in a scratch copy) does not
    const failing: CompileTex = async ({ dir }) => {
      if (!dir.startsWith(run.runDir)) return passed({ dir, mainFile: "main.tex", timeoutMs: 0 });
      await writeFile(path.join(dir, "main.log"), "! LaTeX Error: File `missing.sty' not found.\n./main.tex:2: Emergency stop.\n", "utf8");
      return { status: "failed", tool: "pdflatex", pdf: null, log_tail: "", reason: "pdflatex exited with 1" };
    };
    await runV6(run, { compileTex: failing });
    const todo = await readFile(path.join(run.runDir, "bundle", "corrected_paper", "TODO.md"), "utf8");
    expect(todo).toContain("## The paper does not compile");
    expect(todo).not.toContain("The original source does not compile");
    expect(todo).toContain("`main.tex:2` — the source needs `missing.sty`");
    expect(existsSync(path.join(run.runDir, "bundle", "corrected_paper", "main.log"))).toBe(false);
    expect(await readFile(path.join(run.runDir, "bundle", "README.md"), "utf8")).toContain("NOT ready to submit");
  });

  it("a reference inside an \\iffalse block the author disabled is not listed: TeX never reads it", async () => {
    const block = "\\iffalse\n\\begin{equation}\\label{eq:old}x\\end{equation}\nby~\\eqref{eq:old} and \\ref{lem:gone}\n\\fi";
    const run = await seedRun({ printedProof: block });
    // the compile defines every label outside the disabled block, as pdflatex does
    const compiled: CompileTex = async ({ dir }) => {
      const texts = await Promise.all(["main.tex", "sec/results.tex"].map((f) => readFile(path.join(dir, f), "utf8").catch(() => "")));
      const labels = texts.join("\n").replace(block, "").matchAll(/\\label\{([^{}]*)\}/gu);
      await writeFile(path.join(dir, "main.aux"), [...labels].map((m) => `\\newlabel{${m[1]}}{{1}{1}}`).join("\n"), "utf8");
      return passed({ dir, mainFile: "main.tex", timeoutMs: 0 });
    };
    await runV6(run, { compileTex: compiled });
    const todo = await readFile(path.join(run.runDir, "bundle", "corrected_paper", "TODO.md"), "utf8");
    expect(todo).not.toContain("eq:old");
    expect(todo).not.toContain("lem:gone");
  });

  // live swz: `\\iftoggle{abs}{… Appendix \\ref{sec:figs} …}{…}` with abs false: a blocking TODO item for text TeX never reads
  it("a reference in the branch of an \\iftoggle the paper's toggles do not select is not listed", async () => {
    const run = await seedRun({ preamble: "\\usepackage{etoolbox}\\newtoggle{abs}", printedProof: "\\iftoggle{abs}{see \\ref{sec:gone}}{see the figure.}" });
    await runV6(run, { compileTex: passed });
    const todo = await readFile(path.join(run.runDir, "bundle", "corrected_paper", "TODO.md"), "utf8");
    expect(todo).not.toContain("sec:gone");
  });

  it("a toggle setting inside an \\iffalse block does not count: the branch TeX reads is still checked", async () => {
    const run = await seedRun({ preamble: "\\usepackage{etoolbox}\\newtoggle{abs}\\iffalse\\toggletrue{abs}\\fi", printedProof: "\\iftoggle{abs}{see the appendix.}{see \\ref{sec:live-missing}}" });
    await runV6(run, { compileTex: passed });
    const todo = await readFile(path.join(run.runDir, "bundle", "corrected_paper", "TODO.md"), "utf8");
    expect(todo).toContain("sec:live-missing");
  });

  it("a commented \\iffalse toggles nothing: references in the live text it would wrap are still listed", async () => {
    const run = await seedRun({ printedProof: "%\\iffalse\nsee \\ref{lem:missing}\n%\\fi" });
    await runV6(run, { compileTex: passed });
    const todo = await readFile(path.join(run.runDir, "bundle", "corrected_paper", "TODO.md"), "utf8");
    expect(todo).toContain("`\\ref{lem:missing}` does not resolve");
  });

  it("a compile failure the unmodified source has too is listed as the original source's, not as a correction's", async () => {
    const run = await seedRun();
    const failing: CompileTex = async ({ dir, mainFile }) => {
      const n = (await readFile(path.join(dir, mainFile), "utf8")).split("\n").findIndex((l) => l.startsWith("\\begin{document}")) + 1;
      await writeFile(path.join(dir, "main.log"), `./main.tex:${n}: LaTeX Error: Command \\theHalgorithm already defined.\n`, "utf8");
      return { status: "failed", tool: "pdflatex", pdf: null, log_tail: "", reason: "pdflatex exited with 1" };
    };
    await runV6(run, { compileTex: failing });
    const todo = await readFile(path.join(run.runDir, "bundle", "corrected_paper", "TODO.md"), "utf8");
    expect(todo).not.toContain("## The paper does not compile");
    expect(todo).toContain("## The original source does not compile on this installation\n\nNot caused by a correction");
    expect(todo).toMatch(/`main\.tex:\d+` — pdflatex: LaTeX Error: Command \\theHalgorithm already defined\./u);
    const json = JSON.parse(await readFile(path.join(run.runDir, "bundle", "bundle.json"), "utf8")) as { todo_items: TodoItem[] };
    const item = json.todo_items.find((i) => i.group === "compile-original")!;
    expect(isBlockingTodo(item)).toBe(true);
    expect(json.todo_items.some((i) => i.group === "compile")).toBe(false);
    expect(await readFile(path.join(run.runDir, "bundle", "README.md"), "utf8")).toContain("does not compile on this installation (nor does its original source)");
  });

  it.skipIf(!hasPdflatex)("the corrected fixture compiles with pdflatex: results take their printed numbers, by-products do not stay", async () => {
    const run = await seedRun();
    await runV6(run, { compileTex });
    const json = JSON.parse(await readFile(path.join(run.runDir, "report.json"), "utf8")) as VerifyReportJson;
    expect(json.bundle!.paper).toMatchObject({ pdf: "main.pdf", pages: 1, compile: { status: "passed" } });
    expect(json.names).toMatchObject({ "thm:rate": "Theorem 1", "lem:bound": "Lemma 2", "thm:clt": "Theorem 3" });
    expect(await files(path.join(run.runDir, "bundle", "corrected_paper"))).toEqual(["TODO.md", "main.pdf", "main.tex", "sec/results.tex"]);
    const todo = await readFile(path.join(run.runDir, "bundle", "corrected_paper", "TODO.md"), "utf8");
    expect(todo).not.toContain("does not resolve");
    expect(todo).toContain("Theorem 3: the review refuted this result");
  }, 60_000);

  it.skipIf(!hasPdflatex)("the corrected fixture with a corollary compiles: the corollary takes a number of the paper's, its references resolve, the results after it are renumbered", async () => {
    const run = await seedRun({ split: true, preamble: "\\newtheorem{cor}[thm]{Corollary}" });
    await runV6(run, { compileTex });
    const json = JSON.parse(await readFile(path.join(run.runDir, "report.json"), "utf8")) as VerifyReportJson;
    expect(json.bundle!.paper.compile.status).toBe("passed");
    expect(json.names).toMatchObject({ "thm:rate": "Theorem 1", [COR_ID]: "Corollary 1.1", "lem:bound": "Lemma 3" });
    const todo = await readFile(path.join(run.runDir, "bundle", "corrected_paper", "TODO.md"), "utf8");
    expect(todo).not.toContain("does not resolve");
    expect(todo).toContain("Corollary 1.1: it is a new numbered `cor`");
  }, 60_000);
});

describe("lean/ and MATCH.md", () => {
  const row = (over: Partial<ReportRow>): ReportRow => ({
    env_id: "thm:rate", label: "thm:rate", kind: "theorem", title: null, locator: "main.tex:11-14", node_id: "thm:rate", statement: "The rate is $n^{-1/2}$.", appended_hypotheses: null,
    bucket: "repaired", lean: { file: "Basic.lean", decl: "Papers.Demo.rate", line: 7 }, crosswalk_verdict: "equivalent", bookkeeping: [{ id: "ass:pin-1", condition: "$n \\ge 2$", reason: "pins reading of ass:overlap" }],
    change: { printed: "The rate is $n^{-1/2}$.", corrected: "The rate is $n^{-1/3}$.", referee_conditions: [], dropped_dependencies: [], proof_change: null, descoped: false },
    cited_hypotheses: [], assumed_substrate: [], added_premises: [], findings: [], axioms: { axioms: ["propext", "Classical.choice"], clean: true }, v1_5: null, inherits_refutation_from: [], ...over,
  });
  const report = (rows: ReportRow[], over: Partial<VerifyReportJson> = {}): VerifyReportJson => ({
    schema: 1, run: { qid: "demo", main_file: "main.tex", source_sha256: "x", stage_completed: "V6", early_stop: false }, verdict: "repaired",
    summary: { verified: 0, verified_with_bookkeeping: 0, conditional: 0, repaired: 1, unresolved: 0, refuted: 0, not_determined: 0, not_checked: 0 }, results: rows, run_level_findings: [], patch_review: null, unclear_notes: [],
    v1_warnings: { lint: [], parser: [] }, lean_build: { ok: true, log_tail: "" }, sorry_scan: [], flags: {}, inputs: { v1_5_review: "", crosswalk_full: "", graph_json: "", v1_scope: "", lean_evidence: "" }, disclaimer: "", ...over,
  });

  it("nodeTags reads each tag's declaration, past its docstring and attributes", () => {
    const text = "-- @node: ass:overlap\n/-- Overlap. -/\n@[simp]\nnoncomputable def Overlap (e : ℝ) : Prop := 0 < e\n\n-- @node: thm:rate\ntheorem rate : True := trivial\n-- @node: orphan\n-- @node: lem:x\nprivate lemma x_aux {n : ℕ} : n = n := rfl\n";
    expect(Object.fromEntries(nodeTags("Basic.lean", text))).toEqual({
      "ass:overlap": { decl: "Overlap", file: "Basic.lean", line: 4 },
      "thm:rate": { decl: "rate", file: "Basic.lean", line: 7 },
      "lem:x": { decl: "x_aux", file: "Basic.lean", line: 10 },
    });
  });

  it("MATCH.md sets each result beside its declaration: status, axioms, the phrase-by-phrase rows and the definitions carrying its conditions", () => {
    const core = { statements: [{ id: "thm:rate", depends_on: ["ass:overlap", "ass:pin-1"] }], assumptions: [{ id: "ass:overlap", condition: "The propensity score is bounded away from zero." }], definitions: [] } as unknown as Core;
    const cited = row({ node_id: "lem:lit", label: "lem:lit", kind: "lemma", bucket: "conditional", lean: null, change: null, bookkeeping: [], axioms: null, cited_hypotheses: [{ id: "lem:lit", cite: "Hajek (1960)", locator: "Thm 1", source_check: null }] });
    const md = renderMatch({
      report: report([row({ added_premises: [{ label: "ass:filler:1", statement: "$X$ is integrable", classification: "regularity-bookkeeping" }], assumed_substrate: [{ id: "ass:filler:2", description: "a concentration bound" }] }), cited], { names: { "thm:rate": "Theorem 1", "lem:lit": "Lemma 2" } }),
      links: [{
        obj_id: "T-1", node: "thm:rate", decl: "Papers.Demo.rate",
        segments: [{ id: "s1", text: "Under overlap, ", start: 0, end: 15 }, { id: "s2", text: "the rate is $n^{-1/3}$.\\label{x}", start: 15, end: 40 }],
        rows: [
          { id: "Ω", kind: "binder", names: "Ω", lean: "Type*", segments: [], unstated: true },
          { id: "inst1", kind: "instance", names: "", lean: "Fintype Ω", segments: [], unstated: true },
          { id: "h", kind: "binder", names: "h", lean: "Overlap e", segments: ["s1"], unstated: false },
          { id: "he", kind: "binder", names: "he", lean: "e < 1", segments: [], unstated: true },
          { id: "hcov", kind: "binder", names: "hcov", lean: "", segments: ["s1"], unstated: false },
          { id: "⊢1.h1", kind: "premise", names: "", lean: "∀ n : ℕ", segments: [], unstated: true },
          { id: "⊢1.h2", kind: "premise", names: "", lean: "2 ≤ n", segments: [], unstated: true },
          { id: "⊢1", kind: "conclusion", names: "", lean: "Rate (1/3)", segments: ["s2"], unstated: false },
          { id: "⊢2", kind: "conclusion", names: "", lean: "Measurable rate", segments: [], unstated: true },
        ],
      }],
      tags: new Map([["ass:overlap", { decl: "Overlap", file: "Basic.lean", line: 4 }]]),
      core,
      leanDir: "lean/Papers/Demo",
    });
    expect(md).toContain("## Theorem 1\n\n**Statement (corrected).** The rate is $n^{-1/3}$.");
    expect(md).toContain("**Lean.** `Papers.Demo.rate` — `lean/Papers/Demo/Basic.lean:7`");
    expect(md).toContain("**Status.** proved in Lean (the corrected statement), given 1 standard fact(s) left assumed, under 2 condition(s) made explicit. **Axioms.** the standard ones only (propext, Classical.choice).");
    expect(md).toContain("| Under overlap, | `h : Overlap e` |\n| the rate is $n^{-1/3}$. | then `Rate (1/3)` |");
    // what no phrase states is said for what it is: objects apart from the conditions Lean adds and what it concludes besides;
    // a row with no text (a hypothesis's bare name, once stored as a row) is not printed
    expect(md).toContain("Lean also declares what the paper leaves implicit (the objects and their types): `Ω : Type*`, `Fintype Ω`, `∀ n : ℕ`.");
    expect(md).toContain("Lean assumes conditions that the paper's text does not state: `he : e < 1`, `2 ≤ n`.");
    expect(md).toContain("Lean concludes what the paper's text does not state: `Measurable rate`.");
    expect(md).not.toContain("hcov");
    expect(md).toContain("- reading: $n \\ge 2$ → no declaration is tagged with it");
    // what the report discloses as added in Lean or still assumed is in MATCH.md too
    expect(md).toContain("- hypothesis added to the Lean statement (regularity-bookkeeping): $X$ is integrable");
    expect(md).toContain("- assumed, not proved (the result is conditional on it): a concentration bound");
    expect(md).toContain("- condition of the paper: The propensity score is bounded away from zero. → `Overlap` (`lean/Papers/Demo/Basic.lean:4`)");
    expect(md).toContain("## Lemma 2\n\n**Statement.** The rate is $n^{-1/2}$.\n\n**Lean.** no declaration\n\n**Status.** taken from the literature as cited; not proved here.");
    // the run's ids only in the table at the end
    expect(md.split("## Identifiers")[0]).not.toMatch(/thm:rate|ass:pin-1|T-1/u);
    expect(md.split("## Identifiers")[1]).toContain("| Theorem 1 | `thm:rate` | `thm:rate` | `main.tex:11-14` | `Papers.Demo.rate` |");
  });

  // The finding this guards: MATCH.md printed stored rows whose statement had changed since, and a
  // row under one list F5 gave many rows at once as if it were that row's own.
  it("MATCH.md prints a result's links only when written for its statement as it stands, and marks a blanket list", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "verify-match-current-"));
    tmpDirs.push(root);
    await mkdir(path.join(root, "Papers", "Demo"), { recursive: true });
    await writeFile(path.join(root, "Papers", "Demo", "Basic.lean"), "namespace Papers.Demo\n\ntheorem rate (h : Overlap e) : Rate (1/3) := by\n  sorry\n\nend Papers.Demo\n");
    const core = { statements: [{ id: "thm:rate", depends_on: [] }], assumptions: [], definitions: [] } as unknown as Core;
    const rep = report([row({ bookkeeping: [], lean: { file: "Basic.lean", decl: "Papers.Demo.rate", line: 3 } })], { names: { "thm:rate": "Theorem 1" } });
    const current = await currentStatements(rep, root, path.join(root, "Papers", "Demo"));
    const segments = [{ id: "s1", text: "Under overlap, ", start: 0, end: 15 }, { id: "s2", text: "the rate is $n^{-1/3}$.", start: 15, end: 38 }];
    const flat = [
      { id: "h", kind: "binder", names: "h", lean: "Overlap e", segments: ["s1"], unstated: false },
      { id: "⊢", kind: "conclusion", names: "", lean: "Rate (1/3)", segments: ["s2"], unstated: false, coarse: true },
    ];
    const md = (links: NonNullable<Parameters<typeof renderMatch>[0]["links"]>) => renderMatch({ report: rep, links, tags: new Map(), core, leanDir: "lean/Papers/Demo", current });
    // links of the flat cut that is this statement's: printed, the blanket row marked
    const kept = md([{ obj_id: "T-1", node: "thm:rate", decl: "Papers.Demo.rate", segments, rows: flat }]);
    expect(kept).toContain("| Under overlap, | `h : Overlap e` |\n| the rate is $n^{-1/3}$. | ≈ then `Rate (1/3)` |");
    expect(kept).toContain("A row marked ≈ was given these phrases with many rows of its result at once");
    // a statement changed since (a binder's type), or links under another key: not printed
    for (const links of [
      [{ obj_id: "T-1", node: "thm:rate", decl: "Papers.Demo.rate", segments, rows: [{ ...flat[0]!, lean: "Overlap f" }, flat[1]!] }],
      [{ obj_id: "T-1", node: "thm:rate", decl: "Papers.Demo.rate", key: "0".repeat(40), segments, rows: flat }],
    ]) {
      const out = md(links);
      expect(out).not.toContain("Overlap e` |");
      expect(out).toContain("was written for another version of this Lean statement, so it is not shown");
    }
    // under the statement's own key: printed
    expect(md([{ obj_id: "T-1", node: "thm:rate", decl: "Papers.Demo.rate", key: current.get("thm:rate")!.key, segments, rows: flat }])).toContain("| Under overlap, | `h : Overlap e` |");
  });

  it("MATCH.md gives a corollary a repair split off its declaration, status, axioms and link table like any result", () => {
    const core = { statements: [{ id: "thm:rate", depends_on: [] }, { id: "thm:cor-fix-1", depends_on: ["thm:rate"], split_from: "thm:rate" }], assumptions: [], definitions: [] } as unknown as Core;
    const cor = row({ node_id: "thm:cor-fix-1", label: null, split_from: "thm:rate", statement: "If $X$ is Gaussian, the rate is $n^{-1/2}$.", bucket: "verified", change: null, bookkeeping: [], lean: { file: "Basic.lean", decl: "Papers.Demo.rate_gauss", line: 20 } });
    const rows = [row({}), cor, row({ node_id: "thm:cor-fix-2", label: null, split_from: "thm:rate", lean: null, axioms: null, change: null, bookkeeping: [], bucket: "unresolved" })];
    const names = resultNames(rows, () => "1");
    expect(names).toEqual({ "thm:rate": "Theorem 1", "thm:cor-fix-1": "Corollary 1.1", "thm:cor-fix-2": "Corollary 1.2" });
    const md = renderMatch({
      report: report(rows, { names }),
      links: [{ obj_id: "T-2", node: "thm:cor-fix-1", decl: "Papers.Demo.rate_gauss", segments: [{ id: "s1", text: "If $X$ is Gaussian, ", start: 0, end: 20 }], rows: [{ id: "h", kind: "binder", names: "h", lean: "IsGaussian X", segments: ["s1"], unstated: false }] }],
      tags: new Map(), core, leanDir: "lean/Papers/Demo",
    });
    expect(md).toContain("The correction states this result with 2 corollaries, set out after it.");
    const own = md.slice(md.indexOf("## Corollary 1.1"), md.indexOf("## Corollary 1.2"));
    expect(own).toContain("**Lean.** `Papers.Demo.rate_gauss` — `lean/Papers/Demo/Basic.lean:20`");
    expect(own).toContain("**Status.** proved in Lean. **Axioms.** the standard ones only (propext, Classical.choice).");
    expect(own).toContain("| If $X$ is Gaussian, | `h : IsGaussian X` |");
    expect(md).toContain("## Corollary 1.2\n\n**Statement (a corollary the correction of Theorem 1 splits off; the original paper does not state it).** The rate is $n^{-1/2}$.\n\n**Lean.** no declaration\n\n**Status.** not certified");
    // the plain-language table lists it after its parent
    const plain = renderPlainSections(report(rows, { names })).join("\n");
    expect(plain).toMatch(/\| Theorem 1 \|[^\n]*\n\| Corollary 1\.1 \| proved in Lean \| `Papers\.Demo\.rate_gauss` \(`Basic\.lean:20`\) \| the standard ones only/u);
  });

  it("lean/ holds the paper's modules without tmp/, the toolkit modules they import (and theirs), the pin and a README", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "verify-bundle-lean-"));
    tmpDirs.push(root);
    const w = async (rel: string, text: string): Promise<void> => {
      await mkdir(path.dirname(path.join(root, rel)), { recursive: true });
      await writeFile(path.join(root, rel), text, "utf8");
    };
    await w("Papers/Demo/Basic.lean", "module\npublic import Mathlib.Data.Real.Basic\npublic import Toolkit.A\n\n-- @node: thm:rate\ntheorem rate : True := trivial\n");
    await w("Papers/Demo/tmp/Scratch.lean", "import Toolkit.Unused\n");
    await w("Papers/Demo/notes.md", "x");
    await w("Papers/Demo.lean", "module\npublic import Papers.Demo.Basic\n");
    await w("Toolkit.lean", "import Toolkit.A\n");
    await w("Toolkit/A.lean", "import Toolkit.B\nimport Mathlib.Order.Basic\n");
    await w("Toolkit/B.lean", "-- leaf\n");
    await w("Toolkit/Unused.lean", "-- not imported\n");
    await w("lean-toolchain", "leanprover/lean4:v4.33.0\n");
    await w("lakefile.toml", "name = \"t\"\n");
    const pin = loadCatalog();
    await w("lake-manifest.json", JSON.stringify({ packages: [{ name: "mathlib", url: "https://github.com/leanprover-community/mathlib4", rev: pin.mathlib_rev }] }));
    const runDir = path.join(root, "runs", "demo");
    await mkdir(path.join(runDir, "source"), { recursive: true });
    await writeFile(path.join(runDir, "source", "main.tex"), "\\documentclass{article}\n\\begin{document}\nHello.\n\\end{document}\n", "utf8");
    const envs: EnvsJson = { main_file: "main.tex", files: ["main.tex"], newtheorem: {}, envs: [], bibliography: [] } as unknown as EnvsJson;
    const core = { qid: "demo", symbols: [], assumptions: [], definitions: [], statements: [] } as unknown as Core;
    await mkdir(path.join(runDir, "logs"), { recursive: true });
    await writeFile(path.join(runDir, "logs", "_reviewer_calls.log"), `\n===== reviewer delta/codex :: high :: w =====\n--- codex stdout ---\nd\n\n===== reviewer convergence/dual :: high :: w =====\n--- codex stdout ---\nread ${root}/Papers/Demo/Basic.lean\n--- claude stdout ---\nmatched\n`, "utf8");
    const pass = { verdict: "matched" as const, evidence_hash: "e" };
    const seal = buildF4Seal({ slug: "demo", paperSha256: "x", arxiv: "2301.01234", graph: { ...createEmptyGraph("demo"), symbolReview: { "sym:K": { verdict: "matched", hash: "k" } }, convergenceReview: { "sym:K": { codex: pass, claude: pass } } } });
    const args = {
      runDir, toolkitRoot: root, slug: "demo", mainFile: "main.tex", leanSubdir: "Papers/Demo",
      input: { envs, flatText: "", lineMap: [], refs: null, transcribed: core, core, patches: null, paperErrors: {}, findings: [], review: null },
      report: report([]), promoted: ["Toolkit.A.moved_lemma"], compile: passed, checkFragments: false, seal,
    };
    const r = await writeBundle(args);
    // the F4 seal and the reviews it names are files of the bundle, its code in bundle.json and the README
    const reviews = await readFile(path.join(runDir, "bundle", "f4_reviews.log"), "utf8");
    expect(reviews).toBe("===== reviewer convergence/dual :: high :: w =====\n--- codex stdout ---\nread <local>/Papers/Demo/Basic.lean\n--- claude stdout ---\nmatched\n");
    const sealed = JSON.parse(await readFile(path.join(runDir, "bundle", "f4_seal.json"), "utf8")) as F4Seal;
    expect(sealed.reviews_sha256).toBe(sha256(reviews));
    // every file of lean/, corrected_paper/ and page/ is named with its hash
    const named = [...(await files(path.join(runDir, "bundle", "lean"))).map((f) => `lean/${f}`), ...(await files(path.join(runDir, "bundle", "corrected_paper"))).map((f) => `corrected_paper/${f}`)].sort();
    named.push("page/page.json");
    expect(sealed.files.map((f) => f.path)).toEqual(named);
    expect(await readFile(path.join(runDir, "bundle", "page", "page.json"), "utf8")).not.toContain(root);
    expect(named).toContain("lean/Papers/Demo/Basic.lean");
    const onDisk = new Map(await Promise.all(named.map(async (f) => [f, sha256(await readFile(path.join(runDir, "bundle", f)))] as const)));
    expect(checkF4Seal(sealed, { reviews, files: onDisk })).toEqual([]);
    expect(sealed.arxiv).toBe("2301.01234");
    expect(r.bundle.f4_seal).toEqual({ code: sealed.code, problems: [], reviews: "f4_reviews.log" });
    expect(await readFile(path.join(runDir, "bundle", "README.md"), "utf8")).toContain(sealed.code);
    expect(r.bundle.lean).toMatchObject({ files: 2, toolkit_modules: ["Toolkit.A", "Toolkit.B"], manifest: false, self_contained: { ok: true, problems: [] }, warnings: [], requires: [{ name: "mathlib", form: "git", rev: pin.mathlib_rev }] });
    // the toolkit's lakefile and manifest are not copied: the lakefile is generated, Lake resolves the rest
    expect(await files(path.join(runDir, "bundle", "lean"))).toEqual(["Papers.lean", "Papers/Demo.lean", "Papers/Demo/Basic.lean", "README.md", "Toolkit.lean", "Toolkit/A.lean", "Toolkit/B.lean", "lakefile.toml", "lean-toolchain"]);
    const lean = (f: string): Promise<string> => readFile(path.join(runDir, "bundle", "lean", f), "utf8");
    expect(await lean("Papers.lean")).toBe("module\n\npublic import Papers.Demo\n");
    expect(await lean("Toolkit.lean")).toBe("import Toolkit.A\nimport Toolkit.B\n");
    expect(await lean("lean-toolchain")).toBe(`${pin.lean_toolchain}\n`);
    const readme = await lean("README.md");
    expect(readme).toContain("lake exe cache get");
    expect(readme).toContain(`Lean toolchain: \`${pin.lean_toolchain}\``);
    expect(readme).toContain(`\`https://github.com/leanprover-community/mathlib4\` at \`${pin.mathlib_rev}\``);
    expect(readme).toContain("Checked when this directory was written: every import of every file resolves");
    expect(readme).toContain("copied here (2 module(s)): `Toolkit.A`, `Toolkit.B`");
    expect(readme).toContain("`Mathlib` (2 module(s))");
    expect(readme).toContain("- `Toolkit.A.moved_lemma`");
    // the bundle as written passes `theoremchecker seal`; a page snapshot changed afterwards does not
    await runSealCli([path.join(runDir, "bundle")], { log: () => {} });
    const snapshot = path.join(runDir, "bundle", "page", "page.json");
    await writeFile(snapshot, (await readFile(snapshot, "utf8")).replace('"schema":1', '"schema":1,"verdict":"x"'), "utf8");
    await expect(runSealCli([path.join(runDir, "bundle")])).rejects.toThrow(/changed after the seal was written: page\/page\.json/u);
    // nothing to correct: the paper is the source, and nothing is left to do
    expect(await readFile(path.join(runDir, "bundle", "corrected_paper", "main.tex"), "utf8")).toBe(await readFile(path.join(runDir, "source", "main.tex"), "utf8"));
    expect(r.todo).toEqual([]);
    const readmeTop = await readFile(path.join(runDir, "bundle", "README.md"), "utf8");
    expect(readmeTop).toContain("Ready to submit as far as the mechanical checks go.");
    expect(readmeTop).toContain("The files at this directory's root (`REPORT.md`, `MATCH.md`, `bundle.json`, this file) are outside the seal.");
    // a link in the Lean tree is refused: the bundle holds regular files only, and the seal names each
    if (FILE_SYMLINKS) {
      await symlink(path.join(root, "Papers/Demo/Basic.lean"), path.join(root, "Papers/Demo/Link.lean"));
      await expect(writeBundle(args)).rejects.toThrow(/Link\.lean is a link: the bundle holds regular files only/u);
    }
  });
});

describe("a result the paper leaves undetermined", () => {
  it("is listed as not checked, never as refuted: the report, the TODO and the annotation index", async () => {
    const run = await seedRun({ undetermined: true });
    await writeFile(path.join(run.runDir, "state.json"), JSON.stringify(run.state), "utf8");
    await runV6(run);
    const json = JSON.parse(await readFile(path.join(run.runDir, "report.json"), "utf8")) as VerifyReportJson;
    expect(json.results.find((r) => r.node_id === "thm:clt")!.bucket).toBe("not_determined");
    expect(json.summary).toMatchObject({ not_determined: 1, refuted: 0 });
    const todo = await readFile(path.join(run.runDir, "bundle/corrected_paper/TODO.md"), "utf8");
    expect(todo).toMatch(/Theorem labelled `thm:clt`: this result could not be checked as printed \(the paper does not determine what is claimed\) and no reading or repair was adopted/u);
    expect(todo).not.toContain("refuted this result");
    const index = await readFile(path.join(run.runDir, "annotated/ANNOTATIONS.md"), "utf8");
    expect(index).toMatch(/`thm:clt` \| [^|]* \| not determined \|/u);
    expect(index).not.toContain("error (not repaired)");
  });
});

describe("a rejected repair of a statement the paper leaves undetermined", () => {
  it.each(["unconfirmed", "refuted"] as const)("is never written into the corrected paper as adopted (%s)", async (rejected) => {
    const run = await seedRun({ rejected });
    await writeFile(path.join(run.runDir, "state.json"), JSON.stringify(run.state), "utf8");
    await runV6(run);
    const read = (rel: string): Promise<string> => readFile(path.join(run.runDir, rel), "utf8");
    const json = JSON.parse(await read("report.json")) as VerifyReportJson;
    expect(json.results.find((r) => r.node_id === "thm:rate")!.bucket).toBe("not_determined");
    // the annotation and the report agree, and the rejected text is shown as rejected, never as the correction
    const index = await read("annotated/ANNOTATIONS.md");
    expect(index).toMatch(/`thm:rate` \| [^|]* \| not determined \|/u);
    const annotated = (await read("annotated/main.tex")).split("\\begin{document}")[1]!;
    expect(annotated).not.toMatch(/\\vsCorrected\{/u);
    expect(annotated).toContain("the confirming check rejected it");
    // the corrected paper prints the result as in the original, as its TODO says
    const main = await read("bundle/corrected_paper/main.tex");
    expect(main).toContain("$n^{-1/2}$");
    expect(main).not.toContain("$n^{-1/3}$");
    expect(await read("bundle/corrected_paper/TODO.md")).toMatch(/could not be checked as printed \(the paper does not determine what is claimed\) and no reading or repair was adopted; it is printed as in the original/u);
    const plain = (await read("report.md")).split("# Technical appendix")[0]!;
    expect(plain).not.toContain("Restated to follow a correction above");
    expect(plain).toContain("- **A repair was tried and rejected by the confirming check.**");
    if (rejected === "refuted") expect(plain).toContain("Counterexample to the reading tried (not to the printed statement): Take $e(x)=x$.");
  });
});

describe("the corrected view of the annotation plan", () => {
  it("tags every block with its node and kind, and writes no word about the review into a reading", async () => {
    const run = await seedRun();
    const rec = await readAnnotationRecords(run.runDir, () => {});
    const envs = JSON.parse(await readFile(path.join(run.runDir, VERIFY_FILES.envsJson), "utf8")) as EnvsJson;
    const load = async (rel: string): Promise<Core> => JSON.parse(await readFile(path.join(run.runDir, rel), "utf8")) as Core;
    const { files: src } = await readSourceTex(path.join(run.runDir, "source"), "main.tex", envs);
    const input = { files: src, envs, flatText: rec.flatText, lineMap: rec.lineMap, refs: rec.refs, transcribed: await load(VERIFY_FILES.coreTranscribed), core: await load(VERIFY_FILES.coreJson), patches: rec.patches, paperErrors: {}, findings: FINDINGS, review: null };
    const text = (view: boolean): string => Object.values(planAnnotations({ ...input, correctedView: view }).edits).flat().map((e) => e.text).join("\n");
    const tagged = text(true);
    expect(tagged).toContain("\\vsAt{thm:rate}{printed}\\vsOriginal{");
    expect(tagged).toContain("\\vsAt{thm:rate}{error (repaired)}\\vsCorrected{");
    expect(tagged).toContain("\\vsAt{thm:clt}{error (not repaired)}\\vsNote{");
    expect(tagged).toContain("\\vsReading{$n \\ge 2$}");
    // a condition on a result whose statement has no place in the source is listed, never dropped
    const ghost = structuredClone(input.core);
    ghost.assumptions.push({ id: "ass:bk-9", kind: "regularity", condition: "$m \\ge 1$", bookkeeping: { flag: true, added_by: "V1.5", reason: "a side condition" } } as Core["assumptions"][number]);
    ghost.statements.push({ ...ghost.statements[0]!, id: "thm:ghost", depends_on: ["ass:bk-9"] });
    expect(planAnnotations({ ...input, core: ghost, correctedView: true }).unlocated).toContainEqual({ node: "thm:ghost", kind: "condition added", reason: "ass:bk-9: the statement's environment was not found — the condition: $m \\ge 1$", placed: null });
    // the annotated paper itself is unchanged by the option's existence
    expect(text(false)).not.toContain("\\vsAt");
    expect(text(false)).toContain("\\vsReading{$n \\ge 2$ (the reading of one of its hypotheses)}");
  });
});

describe("the plain-language words", () => {
  it("names a result by its number, else its title, its label, its place", () => {
    const r = (o: Partial<ReportRow>): ReportRow => ({ node_id: "n", kind: "lemma", label: null, title: null, locator: "a.tex:3-5", ...o }) as ReportRow;
    const num = (l: string): string | undefined => ({ "lem:a": "A.2" })[l];
    expect(resultNames([r({ node_id: "1", label: "lem:a" }), r({ node_id: "2", title: "Fraser  bound", label: "x" }), r({ node_id: "3", label: "lem:z" }), r({ node_id: "4" })], num)).toEqual({
      1: "Lemma A.2", 2: "Lemma (Fraser bound)", 3: "Lemma labelled `lem:z`", 4: "Lemma at a.tex, line 3",
    });
  });
  it("names a result numbered by hand (`\\begin{corollary*}[(3.2)]`) by its note's number, over the .aux's section number", () => {
    const r = { node_id: "c", kind: "corollary", label: "cor:3.2", title: "(3.2)", locator: "a.tex:3-5" } as ReportRow;
    expect(resultNames([r], () => "3", () => true)).toEqual({ c: "Corollary 3.2" });
    // a numbered environment keeps its own number, its note a title: `\\begin{assumption}[A1]` is "Assumption 1"
    expect(resultNames([{ ...r, kind: "assumption", title: "A1" }], () => "1", () => false)).toEqual({ c: "Assumption 1" });
    expect(handNumber("(A.1)")).toBe("A.1");
    expect(handNumber("Main bound")).toBeNull();
  });
  it("says what the axioms are and what Lean establishes", () => {
    expect(axiomWords({ axioms: ["propext", "Quot.sound"], clean: true })).toBe("the standard ones only (propext, Quot.sound)");
    expect(axiomWords({ axioms: ["propext", "my_axiom"], clean: false })).toBe("NOT standard: `my_axiom`");
    expect(axiomWords({ axioms: [], clean: true })).toBe("none");
    const base = { node_id: "t", change: null, bookkeeping: [], added_premises: [], assumed_substrate: [], cited_hypotheses: [] } as unknown as ReportRow;
    expect(formalStatus({ ...base, bucket: "verified" }, false)).toEqual({ status: "proved", words: "proved in Lean" });
    expect(formalStatus({ ...base, bucket: "unresolved" }, false).status).toBe("not certified");
    expect(formalStatus({ ...base, bucket: "refuted" }, false).status).toBe("not formalized");
    expect(formalStatus({ ...base, bucket: "verified" }, true).status).toBe("not formalized");
    expect(formalStatus({ ...base, bucket: "conditional", cited_hypotheses: [{ id: "t" }] } as unknown as ReportRow, false).status).toBe("cited");
    expect(formalStatus({ ...base, bucket: "conditional", cited_hypotheses: [{ id: "u" }] } as unknown as ReportRow, false).words).toBe("proved in Lean, given 1 cited result(s)");
  });
  it("a paper with no finding says so, and keeps clarifications apart", () => {
    const json = {
      run: { early_stop: false }, results: [], run_level_findings: [], symbol_readings: [{ symbol: "\\beta", reading: "the slope", evidence: "" }], lean_build: { ok: true, log_tail: "" }, sorry_scan: [],
    } as unknown as VerifyReportJson;
    const md = renderPlainSections(json).join("\n");
    expect(md).toContain("## What was wrong and what was done\n\nNo error was found in the results examined.");
    expect(md).toContain("**Notation.**\n\n- $\\beta$: the slope");
    expect(md).toContain("The Lean development builds; it contains no `sorry`, `admit` or added axiom.");
  });
  it("the TODO list groups what blocks a submission before what is only to check", () => {
    const md = renderTodo("demo", [
      { group: "numbering", file: "main.tex", line: 40, text: "a numbered display was replaced" },
      { group: "references", file: "main.tex", line: 12, text: "`\\ref{eq:x}` does not resolve" },
    ], null);
    expect(md).toContain("2 item(s), 1 of them blocking.");
    expect(md.indexOf("## Unresolved references")).toBeLessThan(md.indexOf("## Numbers and labels (to check)"));
    expect(md).toContain("- `main.tex:12` — `\\ref{eq:x}` does not resolve");
    expect(renderTodo("demo", [], null)).toContain("The mechanical checks leave nothing open");
  });
});

describe("theoremchecker report", () => {
  it("parses its arguments", () => {
    expect(parseReportArgs(["my_paper", "--toolkit", "/t", "--out", "/tmp/o"])).toEqual({ slug: "my_paper", toolkit: "/t", out: path.resolve("/tmp/o") });
    expect(() => parseReportArgs([])).toThrow(/Usage: theoremchecker report/u);
    expect(() => parseReportArgs(["a", "--out"])).toThrow(/--out needs a value/u);
    expect(() => parseReportArgs(["a", "--fast"])).toThrow(/unknown flag --fast/u);
  });
  it("takes the Lean evidence from the report on file", () => {
    const ax = { axioms: ["propext"], clean: true };
    const json = { lean_build: { ok: true, log_tail: "ok" }, sorry_scan: ["sorry in A.lean"], results: [{ lean: { decl: "D.a" }, axioms: ax }, { lean: null, axioms: null }] } as unknown as VerifyReportJson;
    expect(evidenceOnFile(json)).toEqual({ build: { ok: true, log_tail: "ok" }, sorry_scan: ["sorry in A.lean"], axioms: { "D.a": ax } });
    expect(evidenceOnFile({ ...json, lean_build: null })).toBeNull();
  });
});

describe("the page snapshot keeps the machine's user out only where a path names it", () => {
  it("a path names the user; the same word in prose does not", () => {
    // the page is dropped when it names the user in a path, Unix or Windows (its backslashes doubled in JSON)
    expect(userPathIn('"read /home/root/tk/Papers/X.lean"', "root")).toBe("/root");
    expect(userPathIn('{"f":"C:\\\\Users\\\\Mark\\\\tk\\\\x.tex"}', "mark")).toBe("\\Mark");
    expect(userPathIn("see ~lean/notes and more", "lean")).toBe("~lean");
    expect(userPathIn('"/Users/mark"', "mark")).toBe("/mark");
    // prose, or the name inside a longer one, is kept: a machine whose user is `root` once dropped every page saying "root-n"
    expect(userPathIn('"the root-$n$ rate, a square root"', "root")).toBeNull();
    expect(userPathIn('"/home/rooted/x"', "root")).toBeNull();
    expect(userPathIn('"/opt/lean4/bin"', "lean")).toBeNull();
    // a name too short to tell is not looked for
    expect(userPathIn('"/home/jj/x"', "jj")).toBeNull();
  });
});
