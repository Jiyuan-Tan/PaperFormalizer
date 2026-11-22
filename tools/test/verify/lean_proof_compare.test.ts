// The comparator of F5's Lean Proof in English on a verify run: a printed step the Lean proof
// corrects becomes a correction of the paper from the Lean proof (`patches.json` `typo_fixes`, source
// "lean": blue, "Corrected (Lean proof)"), a snippet the runner cannot place is asked for once more,
// and the report lists the comparison beside the corrected slips.
import { mkdtempSync, rmSync } from "node:fs";
import { copyFile, mkdir, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { afterAll, describe, expect, it, vi } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { emitLeanProofEnglish, readLeanProofEnglish } from "../../src/formalization/lean_proof_english.js";
import { addNode, setLean } from "../../src/graph/mutate.js";
import { createEmptyGraph, graphPath, saveGraph } from "../../src/graph/store.js";
import { verifyRunDir } from "../../src/paths.js";
import { artifactPaths, type StageDeps } from "../../src/pipeline_support.js";
import { createVerifyInitialState } from "../../src/state.js";
import type { PipelineContext } from "../../src/types.js";
import { readPatchFile } from "../../src/verify/patches.js";
import { buildReport } from "../../src/verify/report.js";
import { VERIFY_FILES } from "../../src/verify/types.js";
import { writeToyPaper } from "./owner_explained.js";

const roots: string[] = [];
afterAll(() => { for (const r of roots) rmSync(r, { recursive: true, force: true }); });

const PROOF = "Put $z = bx + ay$. Then $z \\ne 0$ since $x \\notin F$.\nHence $z$ spans the line, and $z$ is fixed.";
function core(): Core {
  return {
    qid: "lines", symbols: [], assumptions: [], definitions: [], target_estimand: "t", bibliography: [],
    statements: [{ id: "prop:lines", kind: "proposition", statement: "Every compatible map preserves lines.", depends_on: [], proof_tex: PROOF, status: "to-prove" }],
  } as unknown as Core;
}
const LEAN = ["namespace Papers.Lines", "", "theorem lines_preserved : True := by", "  -- z = b x - a y", "  trivial", "", "end Papers.Lines", ""].join("\n");

async function setup() {
  const repoRoot = mkdtempSync(path.join(tmpdir(), "lean-compare-"));
  roots.push(repoRoot);
  const qid = "lines";
  const ctx = { repoRoot, qid, resume: true, dryRun: false } as PipelineContext;
  const state = createVerifyInitialState(qid, {
    phase: "formalization", source: { input: "main.tex", main_file: "main.tex", sha256: "0".repeat(64) },
    targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 1, findings: [], report_path: null,
  });
  state.lean_subdir = "Papers/Lines";
  const runDir = verifyRunDir(repoRoot, qid);
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  for (const f of [VERIFY_FILES.coreJson, VERIFY_FILES.coreTranscribed]) await writeFile(path.join(runDir, f), JSON.stringify(core(), null, 2));
  await writeToyPaper(runDir, core());
  const leanDir = artifactPaths(ctx, state).leanDir;
  await mkdir(leanDir, { recursive: true });
  await writeFile(path.join(leanDir, "Lines.lean"), LEAN);
  let g = createEmptyGraph(qid);
  g = addNode(g, { id: "prop:lines", kind: "theorem", provenance: "from-note", nl_statement: "lines", tex_anchor: "" });
  g = setLean(g, "prop:lines", "Papers.Lines.lines_preserved", "Lines.lean");
  await saveGraph(graphPath(runDir), g);
  const prompts = path.join(repoRoot, "tools", "src", "formalization", "prompts", "F5");
  await mkdir(prompts, { recursive: true });
  for (const f of ["stage5_proof_english.txt", "stage5_proof_english_review.txt", "stage5_proof_compare.txt"]) await copyFile(path.join(process.cwd(), "src/formalization/prompts/F5", f), path.join(prompts, f));
  return { ctx, state, runDir };
}

describe("the comparator on a verify run", () => {
  it("records the printed step the Lean proof corrects (placed: blue), takes an error that leaves a step out as an unclear step (never marked), and the report counts both", async () => {
    const s = await setup();
    const compares: string[] = [];
    const deps = { runCodex: async ({ prompt }: { prompt: string }) => {
      if (prompt.includes("You are auditing the Lean Proof in English")) return { stdout: JSON.stringify({ reviews: [{ id: "prop:lines", faithful: true, issues: [], readability: [] }] }), stderr: "" };
      if (prompt.includes("You are checking a paper's printed proofs")) {
        compares.push(prompt);
        // the sign (wrong as printed), and a step left out, given as an error: an omission is no error
        const differences = [
          { kind: "error", missing: false, lean: "z = bx − ay", printed: "$z = bx + ay$", suggestion: "$z = bx - ay$", reason: "Lean takes z = bx − ay; with + the step fails" },
          { kind: "error", missing: true, lean: "the map fixes b and a", printed: "and $z$ is fixed.", suggestion: "and $z$ is fixed, since the map fixes $b$ and $a$.", reason: "Lean proves it from the fixed coefficients" },
        ];
        return { stdout: JSON.stringify({ results: [{ id: "prop:lines", summary: "Same route; the printed sign is wrong.", differences }] }), stderr: "" };
      }
      return { stdout: JSON.stringify({ entries: [{ id: "prop:lines", statement: null, proof: "[Put $z = bx - ay$; it is nonzero and fixed](lean:4-5)." }] }), stderr: "" };
    } } as unknown as StageDeps;
    vi.spyOn(console, "log").mockImplementation(() => {});
    const summary = await emitLeanProofEnglish({ ctx: s.ctx, state: s.state, deps });
    expect(compares).toHaveLength(1);
    expect(compares[0]).toContain(`The paper's full source: ${path.join(s.runDir, VERIFY_FILES.flatTex)}`);
    expect(summary).toContain("1 departure(s) from the printed proof: 1 corrected in the paper, 0 wrong step(s) reported only; 1 ambiguous printed step(s) noted");
    const file = (await readPatchFile(s.runDir))!;
    const typos = file.typo_fixes!.find((f) => f.node === "prop:lines")!.typos;
    expect(typos.map((t) => [t.printed, t.unit !== null, t.source])).toEqual([["$z = bx + ay$", true, "lean"]]);
    const stored = (await readLeanProofEnglish(s.runDir))!;
    expect(stored.results[0]!.comparison!.departures.map((d) => [d.kind, d.placed])).toEqual([["printed-wrong", true]]);
    expect(stored.results[0]!.comparison!.unclear).toEqual([{ printed: "and $z$ is fixed.", lean: "the map fixes b and a", suggestion: "and $z$ is fixed, since the map fixes $b$ and $a$." }]);

    const { md } = buildReport({
      qid: "lines", envs: { main_file: "main.tex", files: [], envs: [] } as never, scope: [], core: core(), transcribed: core(), review: null,
      findings: [], addedAssumptions: [], crosswalk: null, graph: null, lean: null, warnings: { lint: [], parser: [] }, flags: {},
      stageCompleted: "5", earlyStop: false, sourceSha256: "h", inputs: { v1_5_review: "", crosswalk_full: "", graph_json: "", v1_scope: "", lean_evidence: "" },
      patches: file, leanProofEnglish: stored,
    } as never);
    expect(md).toContain("- `prop:lines`: $z = bx + ay$ → $z = bx - ay$ — wrong as printed: Lean takes z = bx − ay; with + the step fails (from the Lean proof)");
    expect(md).toContain("## Lean Proof in English");
    expect(md).toContain("- `prop:lines`: corrects the printed proof (1 step(s) corrected; 1 step(s) left unclear in print) — Same route; the printed sign is wrong.");
    // a gap an earlier version stored (listed only) is still read: counted apart, never as a correction
    const legacy = structuredClone(stored);
    legacy.results[0]!.comparison!.departures.push({ kind: "printed-gap", printed: "and $z$ is fixed.", intended: "and $z$ is fixed, since the map fixes $b$ and $a$.", reason: "gap in the printed proof", placed: false });
    const old = buildReport({
      qid: "lines", envs: { main_file: "main.tex", files: [], envs: [] } as never, scope: [], core: core(), transcribed: core(), review: null,
      findings: [], addedAssumptions: [], crosswalk: null, graph: null, lean: null, warnings: { lint: [], parser: [] }, flags: {},
      stageCompleted: "5", earlyStop: false, sourceSha256: "h", inputs: { v1_5_review: "", crosswalk_full: "", graph_json: "", v1_scope: "", lean_evidence: "" },
      patches: file, leanProofEnglish: legacy,
    } as never);
    expect(old.md).toContain("- `prop:lines`: corrects the printed proof (1 step(s) corrected; 1 step(s) left out in print; 1 step(s) left unclear in print)");

    // F5 again: the comparator, told of the recorded corrections, lists none — the comparison still
    // carries them (the paper prints them), and nothing is recorded twice
    const again = { runCodex: async ({ prompt }: { prompt: string }) => {
      if (prompt.includes("You are checking a paper's printed proofs")) {
        expect(prompt).toContain('Corrections already recorded on it: "$z = bx + ay$" → "$z = bx - ay$"');
        return { stdout: JSON.stringify({ results: [{ id: "prop:lines", summary: "Same route.", differences: [{ kind: "error", missing: false, lean: "z = bx − ay", printed: "$z = bx + ay$", suggestion: "$z = bx - ay$", reason: "again" }] }] }), stderr: "" };
      }
      return (deps as unknown as { runCodex: (a: { prompt: string }) => Promise<unknown> }).runCodex({ prompt });
    } } as unknown as StageDeps;
    await emitLeanProofEnglish({ ctx: s.ctx, state: s.state, deps: again });
    const after = (await readLeanProofEnglish(s.runDir))!.results[0]!.comparison!;
    expect(after.verdict).toBe("departs");
    expect(after.departures.map((d) => [d.kind, d.placed])).toEqual([["printed-wrong", true]]);
    expect((await readPatchFile(s.runDir))!.typo_fixes!.find((f) => f.node === "prop:lines")!.typos).toHaveLength(1);
  });
});
