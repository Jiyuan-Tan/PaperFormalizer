import { afterEach, describe, expect, it, vi } from "vitest";
import { mkdtemp, readFile, readdir } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import type { CodexRunInput } from "../src/shared/codex.js";
import type { ModelTokenUsage } from "../src/token_usage.js";

const usage: ModelTokenUsage = { input_tokens: 100, cached_input_tokens: 0, cache_creation_input_tokens: 0, output_tokens: 10, reasoning_output_tokens: 0, total_tokens: 110 };
/** Every call the real codex runner would have received in this file. */
const codexCalls: CodexRunInput[] = [];
vi.mock("../src/shared/codex.js", async (importOriginal) => {
  const mod = await importOriginal<typeof import("../src/shared/codex.js")>();
  return {
    ...mod,
    runCodex: async (input: CodexRunInput) => { codexCalls.push(input); input.onUsage?.(usage); return { stdout: "{\"items\":[]}", stderr: "" }; },
  };
});

import { AuthConfigError, claudeRolesSetting, resolveAuth } from "../src/auth.js";
import { claudeRoles, decideClaudeRoles, describeClaudeRoles, probeResult, setClaudeRolesForTest, type ProbeResult, type RolesProbe } from "../src/claude_roles.js";
import { MODELS } from "../src/models.js";
import { runClaude, runClaudeRoleOnCodex, type ClaudeRunInput } from "../src/workers/claude.js";
import { defaultDeps } from "../src/pipeline_support.js";
import { claudeAsker } from "../src/proposals/curator.js";
import { formalizationDir, logsDir } from "../src/paths.js";
import { createInitialState } from "../src/state.js";
import { tk } from "./toolkit/helpers.js";

/** A machine with the `claude` CLI installed or not, logged in or not; `asked` collects the probes. */
const machine = (installed: boolean, loggedIn: boolean, asked: string[] = []): RolesProbe => (bin, args) => {
  asked.push(`${bin} ${args.join(" ")}`);
  if (args[0] === "auth") return loggedIn ? "ok" : "exit";
  return installed ? "ok" : "missing";
};
const NONE = { env: {}, config: {} };
const CODEX = { runner: "codex", explicit: false, reason: "its CLI is not installed" } as const;

afterEach(() => {
  vi.unstubAllEnvs();
  setClaudeRolesForTest(null);
  codexCalls.length = 0;
  vi.restoreAllMocks();
});

describe("which CLI runs the claude roles", () => {
  it("an explicit setting wins, the environment over local.json, and no CLI is asked", () => {
    const asked: string[] = [];
    expect(decideClaudeRoles(machine(true, true, asked), { env: {}, config: { claudeRoles: "codex" } }))
      .toEqual({ runner: "codex", explicit: true, reason: "set by local.json claudeRoles" });
    expect(decideClaudeRoles(machine(false, false, asked), { env: { PAPERFORMALIZER_CLAUDE_ROLES: "claude" }, config: { claudeRoles: "codex" } }))
      .toEqual({ runner: "claude", explicit: true, reason: "set by PAPERFORMALIZER_CLAUDE_ROLES" });
    expect(asked).toEqual([]);
    expect(() => claudeRolesSetting({ env: { PAPERFORMALIZER_CLAUDE_ROLES: "gpt" }, config: {} })).toThrow(AuthConfigError);
    expect(claudeRolesSetting(NONE)).toBeUndefined();
  });

  it("with no setting: claude when its CLI is installed and logged in, else codex, with the reason", () => {
    expect(decideClaudeRoles(machine(true, true), NONE)).toEqual({ runner: "claude", explicit: false, reason: "claude is available" });
    expect(decideClaudeRoles(machine(false, false), NONE)).toEqual(CODEX);
    expect(decideClaudeRoles(machine(true, false), NONE)).toEqual({ runner: "codex", explicit: false, reason: "it is not logged in" });
  });

  it("only a CLI that does not exist, or a login check that itself exits non-zero, counts against claude", () => {
    // how a probe ended, from what spawnSync returns
    expect(probeResult({ status: 0 })).toBe("ok");
    expect(probeResult({ status: 1 })).toBe("exit");
    expect(probeResult({ error: Object.assign(new Error("spawnSync claude ENOENT"), { code: "ENOENT" }), status: null })).toBe("missing");
    expect(probeResult({ error: Object.assign(new Error("spawnSync claude ETIMEDOUT"), { code: "ETIMEDOUT" }), status: null, signal: "SIGTERM" })).toBe("unknown");
    expect(probeResult({ error: Object.assign(new Error("spawn EAGAIN"), { code: "EAGAIN" }), status: null })).toBe("unknown");
    expect(probeResult({ status: null, signal: "SIGKILL" })).toBe("unknown");
    // and what each means for the roles: (version probe, login probe) → runner
    const ends = (version: ProbeResult, login: ProbeResult): RolesProbe => (_bin, args) => (args[0] === "auth" ? login : version);
    const runner = (version: ProbeResult, login: ProbeResult) => decideClaudeRoles(ends(version, login), NONE);
    expect(runner("missing", "ok")).toEqual(CODEX);
    expect(runner("ok", "exit")).toEqual({ runner: "codex", explicit: false, reason: "it is not logged in" });
    for (const [version, login] of [["ok", "ok"], ["unknown", "ok"], ["exit", "ok"], ["ok", "unknown"], ["unknown", "unknown"]] as const) {
      expect(runner(version, login)).toEqual({ runner: "claude", explicit: false, reason: "claude is available" });
    }
  });

  it("a run keeps the runner it recorded: a later process asks no CLI; an explicit setting still wins, with one warning", () => {
    const asked: string[] = [];
    expect(decideClaudeRoles(machine(true, true, asked), NONE, "codex")).toEqual({ runner: "codex", explicit: false, recorded: true, reason: "as recorded for this run" });
    expect(decideClaudeRoles(machine(false, false, asked), NONE, "claude").runner).toBe("claude");
    expect(asked).toEqual([]);
    expect(decideClaudeRoles(machine(true, true), { env: { PAPERFORMALIZER_CLAUDE_ROLES: "claude" }, config: {} }, "codex")).toMatchObject({ runner: "claude", explicit: true });

    const log = vi.spyOn(console, "log").mockImplementation(() => {});
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    // the suite pins the roles to claude: a run recorded on codex changes runner, and is told so once
    expect(claudeRoles("codex").runner).toBe("claude");
    claudeRoles("codex");
    expect(log.mock.calls).toHaveLength(1);
    expect(warn.mock.calls).toEqual([["[paperformalizer] WARN this run's claude roles ran on codex so far: from now on they run on claude (set by PAPERFORMALIZER_CLAUDE_ROLES)."]]);
    // with no setting the record is honoured; a codex no setting chose is said on stderr
    setClaudeRolesForTest(null);
    warn.mockClear();
    log.mockClear();
    vi.stubEnv("PAPERFORMALIZER_CLAUDE_ROLES", "");
    expect(claudeRoles("codex")).toMatchObject({ runner: "codex", recorded: true });
    expect(log.mock.calls).toEqual([]);
    expect(warn.mock.calls).toEqual([[`[paperformalizer] the claude roles (F1 plan, second F4 reviewer, curator, gardener, study coordinator) run on codex (${MODELS.codexKernel}), as recorded for this run`]]);
  });

  it("in api mode the Anthropic key decides, and the login is not asked", () => {
    const asked: string[] = [];
    const api = { anthropicAuth: "api" };
    expect(decideClaudeRoles(machine(true, false, asked), { env: {}, config: { ...api, anthropicApiKey: "sk-ant-test" } }).runner).toBe("claude");
    expect(decideClaudeRoles(machine(true, true, asked), { env: {}, config: api }))
      .toEqual({ runner: "codex", explicit: false, reason: "api mode is selected with no Anthropic API key" });
    expect(asked).toEqual(["claude --version", "claude --version"]);
  });

  it("api mode with no Anthropic key resolves keyless, and is refused once the roles are pinned to claude", () => {
    const config = { authMode: "api", openaiApiKey: "sk-oai-test" };
    expect(resolveAuth({ env: {}, config })).toEqual({ anthropic: { mode: "api" }, openai: { mode: "api", apiKey: "sk-oai-test" } });
    expect(() => resolveAuth({ env: {}, config: { ...config, claudeRoles: "claude" } })).toThrow(/no API key is configured/);
  });

  it("says which and why in one plain line, and logs it once per process", () => {
    expect(describeClaudeRoles(CODEX)).toBe(
      `claude is not available on this machine (its CLI is not installed): its roles (F1 plan, second F4 reviewer, curator, gardener, study coordinator) run on codex (${MODELS.codexKernel})`,
    );
    expect(describeClaudeRoles({ runner: "codex", explicit: true, reason: "set by local.json claudeRoles" })).toBe(
      `the claude roles (F1 plan, second F4 reviewer, curator, gardener, study coordinator) run on codex (${MODELS.codexKernel}), set by local.json claudeRoles`,
    );
    const log = vi.spyOn(console, "log").mockImplementation(() => {});
    // The suite's environment pins the roles to claude (vitest.config.ts): no CLI is asked.
    expect(claudeRoles()).toMatchObject({ runner: "claude", explicit: true });
    claudeRoles();
    expect(log.mock.calls).toEqual([[`[paperformalizer] the claude roles (F1 plan, second F4 reviewer, curator, gardener, study coordinator) run on claude (${MODELS.claudeMain}), set by PAPERFORMALIZER_CLAUDE_ROLES`]]);
  });
});

describe("a claude role's call", () => {
  const input: ClaudeRunInput = {
    prompt: "curate", model: "opus", cwd: "/toolkit", jsonSchema: { type: "object" },
    allowedTools: ["Read", "Grep", "Glob"], allowSubagents: false, webSearch: false, leanLsp: false, inactivityTimeoutMs: 5,
  };
  const via = (runner: "claude" | "codex", seen: string[]) => ({
    runner: () => runner,
    claude: async () => { seen.push("claude"); return "from claude"; },
    codex: async () => { seen.push("codex"); return "from codex"; },
  });

  it("is run by the claude CLI by default, and by codex when the roles are on codex", async () => {
    const seen: string[] = [];
    expect(await runClaude(input, via("claude", seen))).toBe("from claude");
    expect(await runClaude(input, via("codex", seen))).toBe("from codex");
    expect(seen).toEqual(["claude", "codex"]);
  });

  it("on codex: the kernel model at high effort, the schema, a read-only sandbox for a read-only tool set, the reply text back", async () => {
    const got: CodexRunInput[] = [];
    const models: string[] = [];
    const usages: ModelTokenUsage[] = [];
    const out = await runClaudeRoleOnCodex(
      { ...input, onResolvedModel: (m) => models.push(m), onUsage: (u) => usages.push(u) },
      async (o) => { got.push(o); o.onUsage?.(usage); return { stdout: "{\"ok\":true}", stderr: "" }; },
    );
    expect(out).toBe("{\"ok\":true}");
    const { onUsage, ...sent } = got[0]!;
    expect(sent).toEqual({
      prompt: "curate", cwd: "/toolkit", model: MODELS.codexKernel, reasoningEffort: "high", multiAgent: false,
      sandboxMode: "read-only", leanLsp: false, webSearch: false, outputSchema: { type: "object" }, inactivityTimeoutMs: 5,
    });
    expect(onUsage).toBeTypeOf("function");
    expect(models).toEqual([MODELS.codexKernel]);
    expect(usages).toEqual([usage]);
  });

  it("on codex: a role that writes runs in the configured sandbox, with lean-lsp on the Lean project", async () => {
    const got: CodexRunInput[] = [];
    await runClaudeRoleOnCodex(
      { prompt: "plan", model: "opus", cwd: "/toolkit/P/tmp", leanProjectPath: "/toolkit", mcpConfigPath: "/x/lean_mcp.json", allowedTools: ["Read", "Write", "Edit", "mcp__lean-lsp__lean_loogle"] },
      async (o) => { got.push(o); return { stdout: "{}", stderr: "" }; },
    );
    expect(got[0]).toEqual({ prompt: "plan", cwd: "/toolkit/P/tmp", model: MODELS.codexKernel, reasoningEffort: "high", multiAgent: false, leanProjectPath: "/toolkit" });
  });

  it("a failed codex call stays a failure, under the codex model", async () => {
    const models: string[] = [];
    await expect(runClaudeRoleOnCodex({ ...input, onResolvedModel: (m) => models.push(m) }, async () => { throw new Error("codex exited 1"); })).rejects.toThrow("codex exited 1");
    expect(models).toEqual([MODELS.codexKernel]);
  });
});

describe("the records of a claude role run on codex", () => {
  it("a stage call is ledgered and transcribed under codex and its model, rooted at the Lean project", async () => {
    setClaudeRolesForTest(CODEX);
    const repoRoot = await mkdtemp(path.join(tmpdir(), "tc-roles-"));
    const ctx = { repoRoot, qid: "q", toolkit: tk(repoRoot), dryRun: false, resume: false };
    const deps = defaultDeps(ctx, "2.5", createInitialState("q"));
    expect(await deps.runClaude({ prompt: "=== F4 CONVERGENCE REVIEW ===\nreview t1", cwd: repoRoot, model: "opus", allowedTools: ["Read", "Grep", "Glob"] })).toBe("{\"items\":[]}");
    expect(codexCalls).toHaveLength(1);
    expect(codexCalls[0]).toMatchObject({ model: MODELS.codexKernel, reasoningEffort: "high", sandboxMode: "read-only", leanProjectPath: repoRoot });
    expect(codexCalls[0]!.cwd).not.toBe(repoRoot); // the paper's scratch directory, as for the claude CLI
    const [row] = (await readFile(path.join(formalizationDir(repoRoot, "q"), "token_usage.jsonl"), "utf8")).trim().split("\n").map((l) => JSON.parse(l));
    expect(row).toMatchObject({ provider: "codex", model: MODELS.codexKernel, stage: "F4", success: true, usage });
    const stages = path.join(logsDir(repoRoot, "q"), "stages");
    const transcript = await readFile(path.join(stages, (await readdir(stages))[0]!), "utf8");
    expect(transcript).toContain(`===== codex model=${MODELS.codexKernel} effort=high`);
  });

  it("a curator call is ledgered under codex and its model; under claude, as before", async () => {
    const runDir = await mkdtemp(path.join(tmpdir(), "tc-roles-ledger-"));
    const cfg = tk(runDir);
    const rows = async () => (await readFile(path.join(runDir, "token_usage.jsonl"), "utf8")).trim().split("\n").map((l) => JSON.parse(l));
    setClaudeRolesForTest(CODEX);
    const asker = claudeAsker(cfg, undefined, { runDir, stage: "promotion B" });
    expect(asker.model).toBe(MODELS.codexKernel);
    await asker.ask("p", { type: "object" });
    expect(codexCalls[0]).toMatchObject({ outputSchema: { type: "object" }, sandboxMode: "read-only", leanLsp: false, webSearch: false, model: MODELS.codexKernel });
    expect((await rows())[0]).toMatchObject({ provider: "codex", model: MODELS.codexKernel, stage: "promotion B", usage });
    // every attempt the runner reports is summed
    await claudeAsker(cfg, async (o) => { o.onUsage?.(usage); o.onUsage?.(usage); return "{}"; }, { runDir, stage: "garden" }).ask("p", {});
    expect((await rows())[1]).toMatchObject({ stage: "garden", usage: { ...usage, input_tokens: 200, output_tokens: 20, total_tokens: 220 } });
    setClaudeRolesForTest({ runner: "claude", explicit: true, reason: "set by PAPERFORMALIZER_CLAUDE_ROLES" });
    await claudeAsker(cfg, async () => "{}", { runDir, stage: "promotion B" }).ask("p", {});
    expect((await rows())[2]).toMatchObject({ provider: "claude", model: MODELS.claudeMain });
  });
});
