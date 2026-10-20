// `leansmith relink <slug>`: F5's link step alone on a finished run — the model stubbed here.
import { mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { parseRelinkArgs, runRelinkCli } from "../../src/formalization/relink_cli.js";
import { NL_LINKS_ARTIFACT } from "../../src/formalization/nl_links.js";
import { artifactPaths, type StageDeps } from "../../src/pipeline_support.js";
import { createEmptyGraph, graphPath, saveGraph } from "../../src/graph/store.js";
import { addNode, setLean } from "../../src/graph/mutate.js";
import { createVerifyInitialState, saveState } from "../../src/state.js";
import type { PipelineContext } from "../../src/types.js";
import { TOOLKIT_JSON } from "../toolkit/helpers.js";

describe("relink", () => {
  it("parses a slug, --toolkit and --only", () => {
    expect(parseRelinkArgs(["p", "--only", "thm:a, thm:b", "--toolkit", "/tk"])).toEqual({ slug: "p", toolkit: "/tk", only: ["thm:a", "thm:b"], fresh: false });
    expect(parseRelinkArgs(["p", "--fresh"])).toEqual({ slug: "p", toolkit: null, only: null, fresh: true });
    expect(() => parseRelinkArgs([])).toThrow(/Usage: leansmith relink/);
    expect(() => parseRelinkArgs(["p", "--only"])).toThrow(/--only needs a value/);
    expect(() => parseRelinkArgs(["p", "--bogus"])).toThrow(/unknown flag --bogus/);
  });

  it("links the run's results on its Lean as it stands and writes nl_links.json", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "relink-"));
    await writeFile(path.join(root, "leansmith.json"), JSON.stringify(TOOLKIT_JSON));
    const slug = "user_paper";
    const state = createVerifyInitialState(slug, {
      phase: "formalization", source: { input: "paper.tex", main_file: "paper.tex", sha256: "0".repeat(64) },
      targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 1, findings: [], report_path: null,
    });
    state.lean_subdir = "Papers/UserPaper";
    const ctx = { repoRoot: root, qid: slug, resume: true, dryRun: false } as PipelineContext;
    const paths = artifactPaths(ctx, state);
    await mkdir(paths.leanDir, { recursive: true });
    await mkdir(paths.formalizationDir, { recursive: true });
    await saveState(root, slug, state);
    await writeFile(path.join(paths.leanDir, "T.lean"), "namespace Papers.UserPaper\n\ntheorem plain (x : ℕ) (hx : 0 < x) : D x := by\n  sorry\n\nend Papers.UserPaper\n");
    let g = createEmptyGraph(slug);
    g = addNode(g, { id: "thm:plain", kind: "theorem", provenance: "from-note", nl_statement: String.raw`If $x>0$ then $D_x$.`, tex_anchor: "" });
    g = setLean(g, "thm:plain", "Papers.UserPaper.plain", "T.lean");
    await saveGraph(graphPath(paths.formalizationDir), g);
    const prompts: string[] = [];
    const stageDeps = () => ({ runCodex: async ({ prompt }: { prompt: string }) => {
      prompts.push(prompt);
      const rows = [...prompt.split("Lean rows:\n")[1]!.split("\n\n")[0]!.matchAll(/^  (\S+): /gm)].map((m) => m[1]!);
      return { stdout: JSON.stringify({ results: [{ obj_id: "thm:plain", uncovered: [], rows: rows.map((row) => ({ row, segments: ["s1"], unstated: false })) }], changes: [] }), stderr: "" };
    } }) as unknown as StageDeps;
    const said: string[] = [];
    const summary = await runRelinkCli([slug, "--toolkit", root, "--only", "thm:plain"], { stageDeps, log: (m) => said.push(m) });
    expect(prompts).toHaveLength(2);
    expect(summary).toMatch(/^1\/1 result\(s\) linked row by row; rows asked 3, linked 3/);
    expect(said).toEqual([summary]);
    const nl = JSON.parse(await readFile(path.join(paths.formalizationDir, NL_LINKS_ARTIFACT), "utf8"));
    expect(nl.results.map((r: { node: string; key: string }) => [r.node, r.key.length])).toEqual([["thm:plain", 40]]);
    await expect(runRelinkCli(["nope", "--toolkit", root], { stageDeps })).rejects.toThrow(/no run nope/);
  });
});
