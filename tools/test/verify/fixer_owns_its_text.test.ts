/**
 * The fixer is judged on what it wrote: a suggestion the runner settled (here converted from a
 * referee's weakening grade, its `reason` the referee's prose) is not the fixer's text, so a check
 * that fails on it is never sent back to the fixer; and a repair turned into a suggestion is not
 * asked of the fixer again for any other finding on it. Fake codex; the TeX check faked.
 */
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it, vi } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState } from "../../src/state.js";
import { PatchFileSchema } from "../../src/verify/patches.js";
import { runStageV1 } from "../../src/verify/stage_v1.js";
import { VERIFY_FILES } from "../../src/verify/types.js";
import { cannedExplanation, withOwnerExplanations, writeToyPaper } from "./owner_explained.js";

/** Any TeX field holding the internal field name does not compile, wherever it came from. */
vi.mock("../../src/verify/tex_fragment_check.js", async (importOriginal) => {
  const real = await importOriginal<typeof import("../../src/verify/tex_fragment_check.js")>();
  return {
    ...real,
    texFieldViolations: async (fields: ReadonlyArray<{ where: string; text?: string | null }>) =>
      fields.filter((f) => typeof f.text === "string" && f.text.includes("depends_on")).map((f) => `${f.where} does not compile: Missing $ inserted.`),
  };
});

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

const core = (): Core =>
  ({
    qid: "own",
    symbols: [],
    assumptions: [],
    definitions: [],
    statements: [
      { id: "lem:b", kind: "lemma", statement: "the bound is $2$", depends_on: [], status: "to-prove" },
      { id: "thm:a", kind: "theorem", statement: "the rate is $n^{-1/2}$", depends_on: ["lem:b"], status: "to-prove" },
    ],
    target_estimand: "t",
  }) as unknown as Core;

const REFEREE_PROSE = "weakens the contribution: the rate becomes $n^{-1/4}$; the proof cites a lemma missing from `depends_on`.";

async function fixture(directiveFindings: unknown[], priorPatches: unknown[], priorUnfixable: unknown[] = []) {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "fixer-owns-"));
  tmp.push(repoRoot);
  const runDir = path.join(repoRoot, "runs", "own");
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  for (const f of [VERIFY_FILES.coreJson, VERIFY_FILES.coreTranscribed]) await writeFile(path.join(runDir, f), JSON.stringify(core(), null, 2));
  await writeToyPaper(runDir, core());
  const state = createVerifyInitialState("own", { phase: "init", source: { input: "p.tex", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
  state.verify!.paper_errors = { "thm:a": { detail: "the rate fails", witness: "w" }, "lem:b": { detail: "the bound fails", witness: "w" } };
  const prior = PatchFileSchema.parse({ key_results: ["thm:a"], key_contribution: "the rate", patches: priorPatches, unfixable: priorUnfixable });
  await writeFile(path.join(runDir, VERIFY_FILES.patches), JSON.stringify(prior, null, 2));
  await writeFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), JSON.stringify({ mode: "patch", round: 1, findings: directiveFindings }));
  const calls: CodexRunInput[] = [];
  const lines: string[] = [];
  const run = (reply: unknown) =>
    runStageV1({
      repoRoot,
      qid: "own",
      runDir,
      state,
      deps: { runCodex: (async (input: CodexRunInput) => (calls.push(input), { stdout: JSON.stringify(withOwnerExplanations(reply)), stderr: "" })) as typeof runCodex },
      dryRun: false,
      log: (m: string) => lines.push(m),
    });
  return { run, calls, lines };
}

const LEM_B = { node: "lem:b", ops: [{ op: "replace", unit: "lem:b/1/1", to: null, tex: "the bound is $3$" }], proof_note: "By the triangle inequality the bound is $3$." };
const weakPatch = { node: "thm:a", corrected_statement: "the rate is $n^{-1/4}$", ops: [{ op: "replace", unit: "thm:a/1/1", to: null, tex: "the rate is $n^{-1/4}$" }], proof_note: "The proof is unchanged.", owner_explanation: cannedExplanation("thm:a") };

describe("the fixer is judged on what it wrote", () => {
  it("a repair turned into a suggestion is not asked again for its other findings: no fixer call, the owner's halt", async () => {
    const { run, calls } = await fixture(
      [
        { id: "thm:a", axis: "patch rejected", detail: REFEREE_PROSE, witness: "w", weakens_contribution: true },
        { id: "thm:a", axis: "patch rejected", detail: `the repaired text does not fit the paper around it: ${REFEREE_PROSE}`, witness: null },
      ],
      [weakPatch],
    );
    const res = await run({});
    expect(calls).toHaveLength(0);
    expect(res.status).toBe("checkpoint");
    expect(res.message).not.toContain("not clean");
  });

  it("a weakening repair whose text does not compile is the fixer's to write again, never locked into a suggestion", async () => {
    const { run, calls, lines } = await fixture(
      [{ id: "thm:a", axis: "patch rejected", detail: REFEREE_PROSE, witness: "w", weakens_contribution: true, restatement: ['the corrected statement the paper prints for "thm:a" does not compile: Missing $ inserted.'] }],
      [weakPatch],
    );
    await run({ key_results: ["thm:a"], key_contribution: "the rate", patches: [LEM_B], unfixable: [{ node: "thm:a", reason: "any repair weakens the contribution: the rate needs more", suggested_repair: { ops: weakPatch.ops, proof_note: "The proof is unchanged." } }], rejected: [] });
    expect(lines.join("\n")).not.toMatch(/violation/);
    expect(calls).toHaveLength(1);
    expect(calls[0]!.prompt).toContain("does not compile: Missing $ inserted.");
  });

  it("a check failing on a settled suggestion's text (the referee's prose) is not sent to the fixer", async () => {
    const settled = { node: "thm:a", reason: `any repair weakens the contribution: ${REFEREE_PROSE}`, suggested_by: "referee", suggested_repair: { corrected_statement: weakPatch.corrected_statement, ops: weakPatch.ops, proof_note: "The proof is unchanged." }, owner_explanation: cannedExplanation("thm:a") };
    // The directive still names thm:a and the reply answers it: the settled entry stands whatever it says.
    const { run, calls, lines } = await fixture(
      [
        { id: "lem:b", axis: "correctness", detail: "the bound fails", witness: "w" },
        { id: "thm:a", axis: "patch rejected", detail: "the proof cites a lemma", witness: null },
      ],
      [],
      [settled],
    );
    const res = await run({ key_results: ["thm:a"], key_contribution: "the rate", patches: [{ node: "thm:a", ops: weakPatch.ops, proof_note: "The proof is unchanged." }, { node: "lem:b", ops: [{ op: "replace", unit: "lem:b/1/1", to: null, tex: "the bound is $3$" }], proof_note: "By the triangle inequality the bound is $3$." }], unfixable: [], rejected: [] });
    if (calls.length !== 1) console.log(lines.join("\n"));
    expect(calls).toHaveLength(1);
    expect(lines.join("\n")).not.toMatch(/violation/);
    expect(res.message ?? "").not.toContain("not clean");
  });
});
