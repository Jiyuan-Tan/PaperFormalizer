import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, readFile } from "node:fs/promises";
import path from "node:path";
import os from "node:os";
import { dispatchAgent } from "../../src/framework/agent_dispatch.js";
import { pipelineLogPath } from "../../src/paths.js";
import type { PipelineContext } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import { tk } from "../toolkit/helpers.js";

let tmp: string;
let ctx: PipelineContext;

beforeEach(async () => {
  tmp = await mkdtemp(path.join(os.tmpdir(), "dispatch-test-"));
  ctx = { repoRoot: tmp, toolkit: tk(tmp), qid: "stat_demo", dryRun: false, resume: false } as PipelineContext;
});
afterEach(async () => {
  await rm(tmp, { recursive: true, force: true });
});

describe("dispatchAgent", () => {
  it("logs resolved prompt size+sources before the call and stdout size after", async () => {
    const deps = {
      runCodex: async () => ({ stdout: '{"ok":true}', stderr: "" }),
    } as unknown as StageDeps;
    const out = await dispatchAgent({
      ctx,
      deps,
      stage: "2",
      label: "lit-review",
      prompt: "PROMPT BODY",
      promptSources: ["prompts/F2/stage2_scaffold.txt"],
      model: "gpt-5.6-terra",
      reasoningEffort: "high",
    });
    expect(out.stdout).toBe('{"ok":true}');
    const log = await readFile(pipelineLogPath(tmp, "stat_demo"), "utf8");
    const lines = log
      .trim()
      .split("\n")
      .map((l) => JSON.parse(l));
    const dispatch = lines.find((l) => l.status === "dispatch");
    const complete = lines.find((l) => l.status === "dispatch-complete");
    expect(dispatch.message).toContain("lit-review");
    expect(dispatch.message).toContain(`${Buffer.byteLength("PROMPT BODY", "utf8")} bytes`);
    expect(dispatch.message).toContain("stage2_scaffold.txt");
    expect(complete.message).toContain(`${Buffer.byteLength('{"ok":true}', "utf8")} bytes`);
  });

  it("a prompt past what one message holds goes by file, whole, and the agent is told to read it first", async () => {
    let got = "";
    const deps = { runCodex: async (o: { prompt: string }) => { got = o.prompt; return { stdout: "{}", stderr: "" }; } } as unknown as StageDeps;
    const long = "LINE\n".repeat(210_000);
    await dispatchAgent({ ctx, deps, stage: "2", label: "scaffold", prompt: long, promptSources: ["x"], model: "m", reasoningEffort: "high" });
    expect(got.length).toBeLessThan(1000);
    const file = /they are the file\n(\S+)\n/.exec(got)![1];
    expect(await readFile(file, "utf8")).toBe(long);
    expect(got).toContain(`(${long.length} characters, 210001 lines)`);
    expect(got).toContain("Read that file WHOLE");
  });

  it("refuses an empty prompt — the fail-open-to-empty-prompt class, made structural", async () => {
    const deps = { runCodex: async () => ({ stdout: "", stderr: "" }) } as unknown as StageDeps;
    await expect(
      dispatchAgent({
        ctx,
        deps,
        stage: "2",
        label: "x",
        prompt: "  \n",
        promptSources: ["p"],
        model: "m",
        reasoningEffort: "high",
      }),
    ).rejects.toThrow(/empty prompt/i);
  });
});
