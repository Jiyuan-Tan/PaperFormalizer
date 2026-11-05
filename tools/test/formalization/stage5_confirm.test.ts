// F5 waits for the build that confirms the docstring edits: a block it finds is the stage's halt,
// and the paper enters the papers barrel only once it is green.
import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { beforeEach, describe, expect, it, vi } from "vitest";

const confirmResult = { value: null as string | null, settled: false };
vi.mock("../../src/formalization/stage5_docstrings.js", async (orig) => ({
  ...(await orig<typeof import("../../src/formalization/stage5_docstrings.js")>()),
  ensureDocstringCoverage: async () => ({
    block: null,
    confirm: async () => {
      await new Promise((r) => setTimeout(r, 20));
      confirmResult.settled = true;
      return confirmResult.value;
    },
  }),
}));
vi.mock("../../src/formalization/statement_fingerprints.js", async (orig) => ({
  ...(await orig<typeof import("../../src/formalization/statement_fingerprints.js")>()),
  takeStatementFingerprints: async () => null,
}));

const { runStage5 } = await import("../../src/formalization/stage5.js");
const { artifactPaths } = await import("../../src/pipeline_support.js");
const { coreJsonPath } = await import("../../src/core/core_io.js");
const { createEmptyGraph, graphPath, saveGraph } = await import("../../src/graph/store.js");
const { createVerifyInitialState } = await import("../../src/state.js");
const { BARREL, leanModule, tk } = await import("../toolkit/helpers.js");
import type { StageDeps } from "../../src/pipeline_support.js";
import type { PipelineContext } from "../../src/types.js";

async function seedLiveRun() {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "stage5-confirm-"));
  const qid = "user_paper";
  const ctx: PipelineContext = { repoRoot, toolkit: tk(repoRoot), qid, resume: true, dryRun: false };
  const state = createVerifyInitialState(qid, {
    phase: "formalization",
    source: { input: "paper.tex", main_file: "paper.tex", sha256: "0".repeat(64) },
    targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 1, findings: [], report_path: null,
  });
  state.lean_subdir = "Papers/UserPaper";
  const paths = artifactPaths(ctx, state);
  await mkdir(path.dirname(coreJsonPath(ctx)), { recursive: true });
  await writeFile(coreJsonPath(ctx), JSON.stringify({ qid, symbols: [], assumptions: [], definitions: [], statements: [], target_estimand: "none" }));
  await mkdir(path.dirname(paths.plan), { recursive: true });
  await writeFile(paths.plan, JSON.stringify({ qid, nodes: {} }));
  await saveGraph(graphPath(paths.formalizationDir), createEmptyGraph(qid));
  await mkdir(path.dirname(paths.md), { recursive: true });
  await writeFile(paths.md, "# note\n");
  await mkdir(paths.leanDir, { recursive: true });
  await writeFile(path.join(paths.leanDir, "Main.lean"), leanModule({ doc: "Main", body: "theorem t : True := trivial" }), "utf8");
  await writeFile(path.join(repoRoot, "Papers.lean"), BARREL("Papers", ["Papers.Other"]), "utf8");
  const deps = {
    runCodex: async () => { throw new Error("F5 must not dispatch an agent here"); },
    runClaude: async () => { throw new Error("F5 must not dispatch an agent here"); },
  } as unknown as StageDeps;
  return { repoRoot, ctx, state, deps };
}

describe("runStage5 and the confirming build", () => {
  beforeEach(() => {
    confirmResult.value = null;
    confirmResult.settled = false;
  });

  it("a red confirmation is the stage's halt, and the paper stays out of the barrel", async () => {
    const { repoRoot, ctx, state, deps } = await seedLiveRun();
    confirmResult.value = "F5 docstring pass broke the build; its edits were restored byte-for-byte";
    const result = await runStage5({ ctx, state, deps });
    expect(confirmResult.settled).toBe(true);
    expect(result).toMatchObject({ stage: "5", status: "checkpoint", advance: false });
    expect(result.message).toContain("docstring pass broke the build");
    expect(await readFile(path.join(repoRoot, "Papers.lean"), "utf8")).toBe(BARREL("Papers", ["Papers.Other"]));
  });

  it("a green confirmation completes the stage and registers the paper", async () => {
    const { repoRoot, ctx, state, deps } = await seedLiveRun();
    const result = await runStage5({ ctx, state, deps });
    expect(confirmResult.settled).toBe(true);
    expect(result, result.message).toMatchObject({ stage: "5", status: "completed" });
    expect(await readFile(path.join(repoRoot, "Papers.lean"), "utf8")).toContain("public import Papers.UserPaper");
  });
});
