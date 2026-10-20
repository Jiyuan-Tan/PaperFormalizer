// No call dies of length at the provider: a prompt over the budget is refused before dispatch,
// with the stage, the size and what filled it.

import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, readFile } from "node:fs/promises";
import path from "node:path";
import os from "node:os";
import { PROMPT_INPUT_MAX, PromptTooLongError, assertPromptFits, promptSections } from "../../src/shared/prompt_budget.js";
import { dispatchAgent, dispatchClaudeAgent } from "../../src/framework/agent_dispatch.js";
import { runCodex } from "../../src/shared/codex.js";
import { runClaude } from "../../src/workers/claude.js";
import { pipelineLogPath } from "../../src/paths.js";
import type { PipelineContext } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";

const overlong = (): string =>
  [
    "=== REVISE MODE ===",
    "patch the plan",
    "=== END REVISE MODE ===",
    "Formalization plan (plan.json — the contract):",
    JSON.stringify({ nodes: "p".repeat(700_000) }),
    "",
    "Typed core JSON (structural ground truth):",
    JSON.stringify({ statements: "c".repeat(400_000) }),
    "Return JSON.",
  ].join("\n");

describe("promptSections / assertPromptFits", () => {
  it("names the pasted artifacts by the line that introduces them, largest first", () => {
    const sections = promptSections(overlong());
    expect(sections[0]!.name).toContain("Formalization plan (plan.json");
    expect(sections[0]!.chars).toBeGreaterThan(700_000);
    expect(sections[1]!.name).toContain("Typed core JSON");
    expect(sections.some((s) => s.name === "=== REVISE MODE ===")).toBe(true);
    expect(sections.reduce((n, s) => n + s.chars, 0)).toBe(overlong().length + 1);
  });

  it("an artifact pasted on its label's own line is named by that label", () => {
    const sections = promptSections(`intro\nPlan to review: ${"x".repeat(30_000)}\nend`);
    expect(sections[0]!.name.startsWith("Plan to review:")).toBe(true);
  });

  it("passes a prompt within the budget and refuses one over it, naming caller, size and sections", () => {
    expect(() => assertPromptFits("x".repeat(PROMPT_INPUT_MAX), "F2 scaffold")).not.toThrow();
    let err: unknown;
    try {
      assertPromptFits(overlong(), "dispatch 'F2 scaffold' (stage 2)");
    } catch (e) {
      err = e;
    }
    expect(err).toBeInstanceOf(PromptTooLongError);
    const msg = (err as Error).message;
    expect(msg).toContain("dispatch 'F2 scaffold' (stage 2)");
    expect(msg).toContain(`${overlong().length} characters`);
    expect(msg).toMatch(/- 7000\d\d chars: Formalization plan \(plan\.json/);
    expect(msg).toContain("Typed core JSON");
  });
});

describe("the dispatch guard", () => {
  let tmp: string;
  let ctx: PipelineContext;
  beforeEach(async () => {
    tmp = await mkdtemp(path.join(os.tmpdir(), "prompt-budget-"));
    ctx = { repoRoot: tmp, qid: "q", dryRun: false, resume: false } as PipelineContext;
  });
  afterEach(async () => {
    await rm(tmp, { recursive: true, force: true });
  });

  it("a codex agent gets an over-long prompt by file, a claude agent's call is refused; both are in pipeline.jsonl with the largest sections", async () => {
    let got = "";
    let claudeCalls = 0;
    const deps = {
      runCodex: async (o: { prompt: string }) => ((got = o.prompt), { stdout: "{}", stderr: "" }),
      runClaude: async () => (claudeCalls++, "{}"),
    } as unknown as StageDeps;
    await dispatchAgent({ ctx, deps, stage: "2", label: "F2 scaffold", prompt: overlong(), promptSources: ["plan.json"], model: "m", reasoningEffort: "high" });
    expect(got.length).toBeLessThan(1000);
    expect(await readFile(/they are the file\n(\S+)\n/.exec(got)![1]!, "utf8")).toBe(overlong());
    await expect(
      dispatchClaudeAgent({ ctx, deps, stage: "1", label: "F1 plan author", promptSources: ["core.json"], input: { prompt: overlong(), model: "opus", cwd: tmp } }),
    ).rejects.toThrow(/dispatch 'F1 plan author' \(stage 1\): the prompt is \d+ characters/);
    expect(claudeCalls).toBe(0);
    const lines = (await readFile(pipelineLogPath(tmp, "q"), "utf8")).trim().split("\n").map((l) => JSON.parse(l));
    const byFile = lines.find((l) => l.status === "dispatch-by-file");
    expect(byFile.message).toContain(`${overlong().length} characters`);
    expect(byFile.message).toMatch(/Largest sections: 7000\d\d chars: Formalization plan \(plan\.json/);
    expect(byFile.message).toContain("Sources: [plan.json]");
    const refused = lines.find((l) => l.status === "dispatch-refused");
    expect(refused.message).toContain("Largest sections");
    expect(refused.message).toContain("Sources: [core.json]");
  });

  it("the runners themselves refuse it too (a call no dispatcher wraps), before any process starts", async () => {
    await expect(runCodex({ prompt: overlong(), cwd: tmp, model: "m" } as never)).rejects.toThrow(PromptTooLongError);
    await expect(runClaude({ prompt: overlong(), cwd: tmp, model: "opus" } as never)).rejects.toThrow(PromptTooLongError);
  });
});
