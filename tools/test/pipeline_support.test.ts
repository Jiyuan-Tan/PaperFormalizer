import { describe, expect, it, vi } from "vitest";
import { mkdir, mkdtemp, readdir, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import type { ModelTokenUsage } from "../src/token_usage.js";

const usage: ModelTokenUsage = { input_tokens: 100, cached_input_tokens: 0, cache_creation_input_tokens: 0, output_tokens: 10, reasoning_output_tokens: 0, total_tokens: 110 };
vi.mock("../src/shared/codex.js", async (importOriginal) => {
  const mod = await importOriginal<typeof import("../src/shared/codex.js")>();
  return {
    ...mod,
    // two attempts of one call (a transient retry), each reporting its own session usage
    runCodex: async (input: { onUsage?: (u: ModelTokenUsage) => void }) => { input.onUsage?.(usage); input.onUsage?.(usage); return { stdout: "{}", stderr: "" }; },
  };
});

import { defaultDeps, logicalStageId, readPrompt, watchToolkitSources } from "../src/pipeline_support.js";
import { formalizationDir, logsDir, pipelineLogPath, promptPath } from "../src/paths.js";
import { createInitialState } from "../src/state.js";
import { tk } from "./toolkit/helpers.js";

describe("prompt checkout line endings", () => {
  it.each(["\n", "\r\n"])("reads instructions with canonical LF from %j", async (newline) => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "tc-prompt-eol-"));
    try {
      const file = promptPath(repoRoot, "stage2_head_revise.txt");
      await mkdir(path.dirname(file), { recursive: true });
      await writeFile(file, ["=== REVISE MODE ===", "{{CONTEXT}}", ""].join(newline));
      expect(await readPrompt({ repoRoot } as Parameters<typeof readPrompt>[0], "stage2_head_revise.txt")).toBe("=== REVISE MODE ===\n{{CONTEXT}}\n");
    } finally {
      await rm(repoRoot, { recursive: true, force: true });
    }
  });
});

describe("agent-call accounting", () => {
  it("a prompt names its logical stage on its first line; anything else keeps the slot's label", () => {
    expect(logicalStageId("F2.5", "=== F3 PROOF FILL ===")).toBe("F3");
    expect(logicalStageId("F2.5", "=== F4 CONVERGENCE REVIEW ===")).toBe("F4");
    expect(logicalStageId("F2.5", "=== F2.5 DELTA REVIEW ===")).toBe("F2.5");
    expect(logicalStageId("F2", "=== SCAFFOLD ===")).toBe("F2");
  });

  it("a loop call is ledgered under its logical stage with every attempt's usage, its transcript written once and indexed centrally", async () => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "tc-support-"));
    const ctx = { repoRoot, qid: "q", toolkit: tk(repoRoot), dryRun: false, resume: false };
    const state = createInitialState("q");
    const deps = defaultDeps(ctx, "2.5", state);
    await deps.runCodex({ prompt: "=== F3 PROOF FILL ===\nprove t1", cwd: repoRoot, model: "gpt-x", reasoningEffort: "medium" });
    const [row] = (await readFile(path.join(formalizationDir(repoRoot, "q"), "token_usage.jsonl"), "utf8")).trim().split("\n").map((l) => JSON.parse(l));
    expect(row).toMatchObject({ stage: "F3", success: true, usage: { ...usage, input_tokens: 200, output_tokens: 20, total_tokens: 220 } });
    const logs = logsDir(repoRoot, "q");
    const index = await readFile(path.join(logs, "agent_calls.log"), "utf8");
    expect(index.trim().split("\n")).toHaveLength(1);
    expect(index).not.toContain("prove t1"); // an index line, not a second copy of the prompt
    expect(index).toContain(path.join("stages", "_f3__f3-proof-fill.log"));
    const stages = await readdir(path.join(logs, "stages"));
    expect(stages).toEqual(["_f3__f3-proof-fill.log"]);
    expect(await readFile(path.join(logs, "stages", stages[0]), "utf8")).toContain("prove t1");
  });
});

// While shared builds may run, a toolkit-source change during a formalization worker call is recorded
// (console, pipeline log; never the authors' notes, never attributed) and the stage goes on.
describe("watchToolkitSources", () => {
  const fixture = async (sharedOn = true) => {
    const repoRoot = await mkdtemp(path.join(tmpdir(), "tc-watch-"));
    if (sharedOn) {
      await mkdir(path.join(repoRoot, ".lake", "paperformalizer"), { recursive: true });
      await writeFile(path.join(repoRoot, ".lake", "paperformalizer", "lake-shared-mode"), "");
    }
    await mkdir(path.join(repoRoot, "Toolkit"), { recursive: true });
    await mkdir(path.join(repoRoot, "Papers", "P"), { recursive: true });
    await writeFile(path.join(repoRoot, "Toolkit.lean"), "module\n");
    await writeFile(path.join(repoRoot, "Toolkit", "A.lean"), "module\n");
    await writeFile(path.join(repoRoot, "Papers", "P", "Main.lean"), "module\n");
    return { repoRoot, qid: "watch_run" };
  };
  const notes = (ctx: { repoRoot: string; qid: string }) => readFile(path.join(ctx.repoRoot, "runs", ctx.qid, "orchestrator_notes.md"), "utf8").catch(() => "");
  const logged = (ctx: { repoRoot: string; qid: string }) => readFile(pipelineLogPath(ctx.repoRoot, ctx.qid), "utf8").catch(() => "");

  it("a worker that edits only its paper's files (or a study's Staging) is silent", async () => {
    const ctx = await fixture();
    try {
      const lines: string[] = [];
      const warn = vi.spyOn(console, "warn").mockImplementation((l: string) => { lines.push(l); });
      expect(await watchToolkitSources(ctx, "4", async () => {
        await writeFile(path.join(ctx.repoRoot, "Papers", "P", "Main.lean"), "module\ntheorem t : True := trivial\n");
        await mkdir(path.join(ctx.repoRoot, "Toolkit", "Staging"), { recursive: true });
        await writeFile(path.join(ctx.repoRoot, "Toolkit", "Staging", "S.lean"), "module\n");
        return 7;
      })).toBe(7);
      warn.mockRestore();
      expect(lines).toEqual([]);
      expect(await logged(ctx)).toBe("");
      expect(await notes(ctx)).toBe("");
    } finally {
      await rm(ctx.repoRoot, { recursive: true, force: true });
    }
  });

  it("with the switch off nothing is watched", async () => {
    const ctx = await fixture(false);
    try {
      const lines: string[] = [];
      const warn = vi.spyOn(console, "warn").mockImplementation((l: string) => { lines.push(l); });
      expect(await watchToolkitSources(ctx, "4", async () => {
        await writeFile(path.join(ctx.repoRoot, "Toolkit", "A.lean"), "module\n-- a promotion's write\n");
        return 1;
      })).toBe(1);
      warn.mockRestore();
      expect(lines).toEqual([]);
      expect(await logged(ctx)).toBe("");
    } finally {
      await rm(ctx.repoRoot, { recursive: true, force: true });
    }
  });

  it("a worker that changes a toolkit source is reported loudly, and the stage goes on (or its error does)", async () => {
    const ctx = await fixture();
    try {
      const lines: string[] = [];
      const warn = vi.spyOn(console, "warn").mockImplementation((l: string) => { lines.push(l); });
      expect(await watchToolkitSources(ctx, "4", async () => {
        await writeFile(path.join(ctx.repoRoot, "Toolkit", "A.lean"), "module\n-- edited by a worker\n");
        return "done";
      })).toBe("done");
      expect(lines.join("\n")).toMatch(/\(F4\b.*toolkit sources changed during this worker call: Toolkit\/A\.lean \(by a promotion or study apply, or by the worker/);
      expect(lines.join("\n")).not.toMatch(/undo/);
      expect(await logged(ctx)).toMatch(/"status":"toolkit-sources-changed".*Toolkit\/A\.lean/);
      // never in the authors' notes
      expect(await notes(ctx)).toBe("");
      // one that edits and then fails: reported, and its error goes on
      await expect(watchToolkitSources(ctx, "4", async () => {
        await rm(path.join(ctx.repoRoot, "Toolkit", "A.lean"));
        throw new Error("worker died");
      })).rejects.toThrow(/worker died/);
      expect((await logged(ctx)).trim().split("\n").filter((l) => l.includes("toolkit-sources-changed"))).toHaveLength(2);
      warn.mockRestore();
    } finally {
      await rm(ctx.repoRoot, { recursive: true, force: true });
    }
  });
});

