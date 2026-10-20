// F5 writes only per-run artifacts (no library doc `doc/API.md`, no research ledgers) plus, on a
// live completion, the paper's line in the root papers barrel.
import { mkdir, mkdtemp, readFile, readdir, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { registerInPapersBarrel, runStage5 } from "../../src/formalization/stage5.js";
import { artifactPaths, type StageDeps } from "../../src/pipeline_support.js";
import { coreJsonPath } from "../../src/core/core_io.js";
import { createEmptyGraph, graphPath, saveGraph } from "../../src/graph/store.js";
import { createVerifyInitialState } from "../../src/state.js";
import type { PipelineContext } from "../../src/types.js";
import { BARREL, leanModule, tk } from "../toolkit/helpers.js";

async function listTree(dir: string): Promise<string[]> {
  return (await readdir(dir, { recursive: true })).map(String);
}

async function seedRun(dryRun: boolean) {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "stage5-out-"));
  const qid = "user_paper";
  const ctx: PipelineContext = { repoRoot, toolkit: tk(repoRoot), qid, resume: true, dryRun };
  const state = createVerifyInitialState(qid, {
    phase: "formalization",
    source: { input: "paper.tex", main_file: "paper.tex", sha256: "0".repeat(64) },
    targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 1, findings: [], report_path: null,
  });
  state.lean_subdir = "Papers/UserPaper";
  const paths = artifactPaths(ctx, state);
  await mkdir(path.dirname(coreJsonPath(ctx)), { recursive: true });
  await writeFile(coreJsonPath(ctx), JSON.stringify({
    qid, symbols: [], assumptions: [], definitions: [], statements: [], target_estimand: "none",
  }));
  await mkdir(path.dirname(paths.plan), { recursive: true });
  await writeFile(paths.plan, JSON.stringify({ qid, nodes: {} }));
  await saveGraph(graphPath(paths.formalizationDir), createEmptyGraph(qid));
  await mkdir(path.dirname(paths.md), { recursive: true });
  await writeFile(paths.md, "# note\n");
  await mkdir(paths.leanDir, { recursive: true });
  const deps = {
    runCodex: async () => { throw new Error("F5 must not dispatch an agent here"); },
    runClaude: async () => { throw new Error("F5 must not dispatch an agent here"); },
  } as unknown as StageDeps;
  return { repoRoot, ctx, state, paths, deps };
}

describe("runStage5 outputs", () => {
  it("completes without dispatching an agent and writes no API.md or ledger file", async () => {
    const { repoRoot, ctx, state, paths, deps } = await seedRun(true);
    const before = new Set(await listTree(repoRoot));
    const result = await runStage5({ ctx, state, deps });

    expect(result, result.message).toMatchObject({ stage: "5", status: "completed", completedStage: "5" });
    const written = (await listTree(repoRoot)).filter((f) => !before.has(f));
    expect(written.some((f) => /API\.md$|SUBSTRATE_DEBT|CITED_DEPENDENCIES/.test(f))).toBe(false);
    expect(written.every((f) => f.startsWith(path.relative(repoRoot, paths.formalizationDir)) || f.startsWith(path.relative(repoRoot, path.dirname(paths.crosswalkFullJson))))).toBe(true);
    // A dry run never touches the papers barrels.
    expect(written.some((f) => f.startsWith("Papers"))).toBe(false);
  });

  it("registers a completed paper in the root papers barrel (live), never in a dry run", async () => {
    const { repoRoot, ctx, state, paths } = await seedRun(false);
    await writeFile(path.join(repoRoot, "Papers.lean"), BARREL("Papers", ["Papers.Other"]), "utf8");
    await writeFile(path.join(paths.leanDir, "Main.lean"), leanModule({ doc: "Main", body: "theorem t : True := trivial" }), "utf8");

    expect(await registerInPapersBarrel({ ...ctx, dryRun: true }, state, paths.leanDir)).toEqual({});
    expect(await readFile(path.join(repoRoot, "Papers.lean"), "utf8")).toBe(BARREL("Papers", ["Papers.Other"]));

    expect(await registerInPapersBarrel(ctx, state, paths.leanDir)).toEqual({ changed: path.join(repoRoot, "Papers.lean") });
    const root = await readFile(path.join(repoRoot, "Papers.lean"), "utf8");
    expect(root.split("\n").filter((l) => l.startsWith("public import"))).toEqual([
      "public import Papers.Other", "public import Papers.UserPaper",
    ]);
    expect(await readFile(path.join(repoRoot, "Papers", "UserPaper.lean"), "utf8")).toContain("public import Papers.UserPaper.Main");
    expect(await registerInPapersBarrel(ctx, state, paths.leanDir)).toEqual({});
  });
});
