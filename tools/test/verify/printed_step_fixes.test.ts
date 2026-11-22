/**
 * Printed proof steps the Lean proof had to depart from (e.g. the
 * filler "corrected the configuration sign to z=bx−ay", escalate null, and the report and corrected paper
 * kept the wrong step). The F-stage filler lists them in `printed_step_fixes` (the V1.5 `typos` shape plus
 * the node); the runner records them through the typo channel (`patches.json` `typo_fixes`, `source:
 * "lean"`): located exactly once → corrected in the paper, else reported only. Never a round, a rewind or a
 * stop. Corrected steps carry their own labels: "Corrected typo" (the referee's), "Corrected (Lean proof)".
 */
import { existsSync, mkdtempSync, rmSync } from "node:fs";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { afterAll, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { FILLER_OUTPUT_SCHEMA, runFiller } from "../../src/formalization/proof_filler.js";
import { addNode, setProof } from "../../src/graph/mutate.js";
import { createEmptyGraph } from "../../src/graph/store.js";
import { verifyRunDir } from "../../src/paths.js";
import { renderPaper } from "../../src/ui/tex_html.js";
import { applyEdits, planAnnotations } from "../../src/verify/annotated_paper.js";
import { VS_PREAMBLE_BLOCK } from "../../src/verify/annotate_tex.js";
import { correctedTex } from "../../src/verify/corrected_tex.js";
import { readPatchFile, repairSources, type PatchFile } from "../../src/verify/patches.js";
import { buildReport } from "../../src/verify/report.js";
import { VERIFY_FILES } from "../../src/verify/types.js";
import { writeToyPaper } from "./owner_explained.js";

const roots: string[] = [];
afterAll(() => {
  for (const r of roots) rmSync(r, { recursive: true, force: true });
});
const realPromptPath = path.join(process.cwd(), "src/formalization/prompts/F4/proof_filler.txt");

const SUM_PROOF = "By the moment bound, $a_n \\le C n^{-2}$ for every $n$.\nSumming from left to right gives $\\sum_n a_n < \\infty$.";
function core(): Core {
  return {
    qid: "slips",
    symbols: [],
    assumptions: [],
    definitions: [],
    statements: [{ id: "thm:sum", kind: "theorem", statement: "The series $\\sum_n a_n$ converges.", depends_on: [], proof_tex: SUM_PROOF, status: "to-prove" }],
    target_estimand: "t",
    bibliography: [],
  } as unknown as Core;
}

/** A verify run (its paper units, transcription and accepted core) and a graph whose theorem has the paper alias T-1. */
async function setup(): Promise<{ ctx: { repoRoot: string; qid: string }; runDir: string; graph: ReturnType<typeof createEmptyGraph> }> {
  const repoRoot = mkdtempSync(path.join(tmpdir(), "printed-steps-"));
  roots.push(repoRoot);
  const qid = "slips";
  const runDir = verifyRunDir(repoRoot, qid);
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  for (const f of [VERIFY_FILES.coreJson, VERIFY_FILES.coreTranscribed]) await writeFile(path.join(runDir, f), JSON.stringify(core(), null, 2));
  await writeToyPaper(runDir, core());
  let g = createEmptyGraph(qid);
  g = addNode(g, { id: "thm:sum", kind: "theorem", provenance: "from-note", nl_statement: "the series converges", tex_anchor: "L1" });
  g = { ...g, nodes: g.nodes.map((n) => (n.id === "thm:sum" ? { ...n, obj_id: "T-1", lean: { decl_name: "sum_thm", file: "T1.lean" } } : n)) };
  g = setProof(g, "thm:sum", "sorry", 1);
  return { ctx: { repoRoot, qid }, runDir, graph: g };
}

const reply = (fixes: unknown) => ({ added_assumptions: [], escalate: null, printed_step_fixes: fixes, summary: "corrected the summation step. Statements unchanged." });
const fill = (s: Awaited<ReturnType<typeof setup>>, out: object) =>
  runFiller({ ctx: s.ctx, promptPath: realPromptPath, leanDir: path.join(s.runDir, "lean"), graph: s.graph, deps: { runCodex: async () => ({ stdout: JSON.stringify(out), stderr: "" }) } });

const SIGN = { node: "T-1", printed: "Summing from left to right", intended: "Summing over $n$", reason: "the sum has no direction" };
const TWICE = { node: "thm:sum", printed: "a_n", intended: "b_n", reason: "printed in both steps" };

describe("the filler's printed_step_fixes", () => {
  it("is in the reply contract, beside escalate; the prompt asks for it and keeps escalate for wrong statements", async () => {
    expect(FILLER_OUTPUT_SCHEMA.required as string[]).toEqual(expect.arrayContaining(["escalate", "printed_step_fixes"]));
    const prompt = (await readFile(realPromptPath, "utf8")).replace(/\s+/gu, " ");
    expect(prompt).toContain("List in `printed_step_fixes` every printed proof step your proof had to depart from because it is wrong as printed");
    expect(prompt).toContain("It never replaces `escalate`");
    // a reply in the shape before the field fills as before
    const s = await setup();
    const r = await fill(s, { added_assumptions: [], escalate: null, summary: "s" });
    expect(r.escalate).toBeNull();
    expect(existsSync(path.join(s.runDir, VERIFY_FILES.patches))).toBe(false);
  });

  it("one located and one not: one op on the step, one entry reported only, both from the Lean proof; the core is untouched", async () => {
    const s = await setup();
    const coreBefore = await readFile(path.join(s.runDir, VERIFY_FILES.coreJson), "utf8");
    const r = await fill(s, reply([SIGN, TWICE]));
    expect(r.escalate).toBeNull();
    const file = (await readPatchFile(s.runDir))!;
    const fix = file.typo_fixes!.find((t) => t.node === "thm:sum")!;
    expect(fix.typos.map((t) => [t.printed, t.unit !== null, t.source])).toEqual([
      ["Summing from left to right", true, "lean"],
      ["a_n", false, "lean"],
    ]);
    expect(fix.ops).toHaveLength(1);
    expect(fix.ops[0]!.tex).toContain("Summing over $n$ gives");
    expect(fix.proof_note).toBe(SUM_PROOF.replace("Summing from left to right", "Summing over $n$"));
    // no round, no rewind: the core the F stages formalize stays as accepted
    expect(await readFile(path.join(s.runDir, VERIFY_FILES.coreJson), "utf8")).toBe(coreBefore);
    // listed again on a later fill: nothing new
    await fill(s, reply([SIGN]));
    expect((await readPatchFile(s.runDir))!.typo_fixes).toEqual(file.typo_fixes);

    // the report: both, apart, marked as the Lean proof's
    const { json, md } = buildReport({
      qid: "slips",
      envs: { main_file: "main.tex", files: [], envs: [] } as never,
      scope: [],
      core: core(),
      transcribed: core(),
      review: null,
      findings: [],
      addedAssumptions: [],
      crosswalk: null,
      graph: null,
      lean: null,
      warnings: { lint: [], parser: [] },
      flags: {},
      stageCompleted: "F4",
      earlyStop: false,
      sourceSha256: "h",
      inputs: { v1_5_review: "", crosswalk_full: "", graph_json: "", v1_scope: "", lean_evidence: "" },
      patches: file,
    } as never);
    expect(json.typos!.map((t) => [t.printed, t.corrected, t.source])).toEqual([
      ["Summing from left to right", true, "lean"],
      ["a_n", false, "lean"],
    ]);
    expect(md).toContain("## Proof slips corrected");
    expect(md).toContain("- `thm:sum`: Summing from left to right → Summing over $n$ — the sum has no direction (from the Lean proof)");
    expect(md).toContain("- `thm:sum`: a_n → b_n — printed in both steps (from the Lean proof) (not corrected:");
  });

  it("a malformed field never stops the fill: logged, nothing recorded", async () => {
    const s = await setup();
    for (const bad of ["oops", { node: "thm:sum" }, [{ node: 5, printed: "x" }], [{ node: "thm:nope", printed: "Summing", intended: "x", reason: "r" }]]) {
      const r = await fill(s, reply(bad));
      expect(r.escalate).toBeNull();
      expect(r.summary).toContain("Statements unchanged");
    }
    expect(existsSync(path.join(s.runDir, VERIFY_FILES.patches))).toBe(false);
  });

  it("a run that is no verify run: the field is ignored", async () => {
    const repoRoot = mkdtempSync(path.join(tmpdir(), "printed-steps-plain-"));
    roots.push(repoRoot);
    let g = createEmptyGraph("plain");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "x", tex_anchor: "L1" });
    const r = await runFiller({ ctx: { repoRoot, qid: "plain" }, promptPath: realPromptPath, leanDir: "/nowhere", graph: g, deps: { runCodex: async () => ({ stdout: JSON.stringify(reply([SIGN])), stderr: "" }) } });
    expect(r.escalate).toBeNull();
  });
});

describe("the labels of corrected steps", () => {
  it("the annotated paper sets the Lean proof's as \\vsLeanStep and the referee's as \\vsTypoStep; the corrected paper prints both; the page labels them apart", async () => {
    const s = await setup();
    await fill(s, reply([SIGN]));
    const src = (await repairSources(s.runDir))!;
    const file = (await readPatchFile(s.runDir))! as PatchFile;
    const flat = src.units.flat;
    const lineMap = JSON.parse(await readFile(path.join(s.runDir, VERIFY_FILES.flatLineMap), "utf8")).lineMap;
    const input = (patches: PatchFile, correctedView = false) => ({ files: { "main.tex": flat }, envs: src.envs, flatText: flat, lineMap, refs: src.refs, transcribed: core(), core: core(), patches, paperErrors: {}, findings: [], review: null, correctedView });
    const lean = applyEdits(flat, planAnnotations(input(file)).edits["main.tex"] ?? []);
    expect(lean).toMatch(/\\vsLeanStep\{Summing over \$n\$ gives/u);
    expect(lean).not.toMatch(/\\vsCorrectedStep\{|\\vsTypoStep\{/u);
    const referee: PatchFile = { ...file, typo_fixes: file.typo_fixes!.map((t) => ({ ...t, typos: t.typos.map(({ source: _s, ...x }) => x) })) };
    expect(applyEdits(flat, planAnnotations(input(referee)).edits["main.tex"] ?? [])).toMatch(/\\vsTypoStep\{Summing over \$n\$ gives/u);
    const view = applyEdits(flat, planAnnotations(input(file, true)).edits["main.tex"] ?? []);
    const corrected = correctedTex(view, { proofEnv: true });
    expect(corrected.tex).toContain("Summing over $n$ gives");
    expect(corrected.tex).not.toContain("left to right");
    expect(corrected.tex).not.toMatch(/\\vs[A-Z]/u);
    // the macros are defined for the compiled annotated paper, beside \vsCorrectedStep
    expect(VS_PREAMBLE_BLOCK).toContain("\\newcommand{\\vsTypoStep}[1]{\\vsBlock{vsBlue}{}{Corrected typo:}{#1}}");
    expect(VS_PREAMBLE_BLOCK).toContain("\\newcommand{\\vsLeanStep}[1]{\\vsBlock{vsBlue}{}{Corrected (Lean proof):}{#1}}");
    // the web page: the same blue "rv ins" block, under its own label; the red original stays "Original step"
    const page = (body: string): string => renderPaper({ files: { "m.tex": `\\begin{document}${body}\\end{document}` }, main: "m.tex", aux: "" }).html;
    const typo = page("\\vsStep{Summing from left to right.}\\vsTypoStep{Summing over $n$.}");
    expect(typo).toContain("Corrected typo");
    expect(typo).toContain("Original step");
    expect(typo).toMatch(/class="rv ins/u);
    expect(page("\\vsLeanStep{Summing over $n$.}")).toContain("Corrected (Lean proof)");
    expect(typo).not.toContain("Revised step");
  });
});
