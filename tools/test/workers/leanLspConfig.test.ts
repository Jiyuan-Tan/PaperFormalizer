import { afterEach, describe, it, expect } from "vitest";
import { readFileSync } from "node:fs";
import { claudeQuotaReason, writeLeanLspMcpConfig, writeLeanLspSharedConfig } from "../../src/workers/claude.js";
import { SHARED_LEAN_LSP_URL_ENV } from "../../src/shared/shared_lean_lsp_env.js";

// The claude allow-list grants `mcp__lean-lsp__*`, so BOTH the stdio (per-call)
// and the shared (HTTP) MCP configs MUST register the server under the exact name
// `lean-lsp` — otherwise the tools are advertised under a different prefix and
// claude is never permitted to call them. These guard that contract.
describe("lean-lsp MCP config writers", () => {
  const url = "http://127.0.0.1:54321/mcp";
  it.each([
    ["stdio", () => writeLeanLspMcpConfig("/some/repo")],
    ["shared", () => writeLeanLspSharedConfig(url)],
  ] as const)("the %s config registers the server as `lean-lsp`", (kind, write) => {
    const cfg = JSON.parse(readFileSync(write(), "utf8"));
    expect(Object.keys(cfg.mcpServers)).toEqual(["lean-lsp"]);
    if (kind === "stdio") {
      expect(typeof cfg.mcpServers["lean-lsp"].command).toBe("string");
      expect(cfg.mcpServers["lean-lsp"].url).toBeUndefined();
    } else {
      // No stdio command → attaches to the shared server, does not spawn its own.
      expect(cfg.mcpServers["lean-lsp"]).toEqual({ type: "http", url });
    }
  });

  it("writes one stdio config per project, so two toolkits never overwrite each other's path", () => {
    const a = writeLeanLspMcpConfig("/toolkit/a");
    const b = writeLeanLspMcpConfig("/toolkit/b");
    expect(a).not.toBe(b);
    expect(JSON.parse(readFileSync(a, "utf8")).mcpServers["lean-lsp"].args).toContain("/toolkit/a");
    expect(JSON.parse(readFileSync(b, "utf8")).mcpServers["lean-lsp"].args).toContain("/toolkit/b");
  });

  describe("with a shared server booted", () => {
    const previous = process.env[SHARED_LEAN_LSP_URL_ENV];
    afterEach(() => {
      if (previous === undefined) delete process.env[SHARED_LEAN_LSP_URL_ENV];
      else process.env[SHARED_LEAN_LSP_URL_ENV] = previous;
    });
    it("the stdio writer attaches to it instead of spawning a cold server beside it", () => {
      process.env[SHARED_LEAN_LSP_URL_ENV] = url;
      const cfg = JSON.parse(readFileSync(writeLeanLspMcpConfig("/some/repo"), "utf8"));
      expect(cfg.mcpServers["lean-lsp"]).toEqual({ type: "http", url });
    });
  });
});

describe("claude failures the operator must act on", () => {
  it("names a spent usage window and a missing login; anything else is not classified", () => {
    expect(claudeQuotaReason('{"type":"result","is_error":true,"result":"api_error_status: 429 You\'ve hit your weekly limit"}')).toMatch(/usage limit/);
    expect(claudeQuotaReason("Not logged in · Please run /login")).toMatch(/not logged in/);
    expect(claudeQuotaReason("Error: ENOENT no such file")).toBeNull();
  });
});
