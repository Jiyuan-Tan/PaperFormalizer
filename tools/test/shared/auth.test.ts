import { mkdtempSync, rmSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it, vi } from "vitest";
import {
  codexHome,
  resolveAuthMode,
  resolveProviderAuth,
  workerEnv,
} from "../../src/auth.js";
import { claudeAuthArgs } from "../../src/workers/claude.js";

const NO_CONFIG = { env: {} as NodeJS.ProcessEnv, config: {} };

const tempDirs: string[] = [];
function tempDir(): string {
  const dir = mkdtempSync(path.join(os.tmpdir(), "causalsmith-auth-"));
  tempDirs.push(dir);
  return dir;
}

afterEach(() => {
  vi.resetModules();
  vi.doUnmock("../../src/local_config.js");
  while (tempDirs.length > 0) {
    rmSync(tempDirs.pop() as string, { recursive: true, force: true });
  }
});

/**
 * Load `src/auth.ts` against a STUBBED `local.json`.
 *
 * This is the regression harness for the defect the first cut of this feature
 * shipped with: every resolver defaulted its config to `{}`, so the dispatchers
 * — which call `resolveProviderAuth("anthropic")` with NO arguments — never saw
 * a file-configured mode, and a `local.json` saying `authMode: "api"` silently
 * produced subscription flags while the startup banner claimed `api`. Tests that
 * always pass `config:` explicitly cannot see that; these must not.
 */
async function authWithLocalJson(file: Record<string, string>) {
  vi.resetModules();
  vi.doMock("../../src/local_config.js", () => ({
    localConfig: () => file,
    leanProjectPathFor: (root: string) => root,
    applyWorkerEnv: () => {},
  }));
  return import("../../src/auth.js");
}

describe("resolveAuthMode", () => {
  it("keeps the subscription login as the default", () => {
    expect(resolveAuthMode("anthropic", NO_CONFIG)).toBe("subscription");
    expect(resolveAuthMode("openai", NO_CONFIG)).toBe("subscription");
  });

  it("lets the environment override the file", () => {
    expect(
      resolveAuthMode("anthropic", {
        env: { LEANSMITH_AUTH_MODE: "api" },
        config: { authMode: "subscription" },
      }),
    ).toBe("api");
  });

  it("fails closed on an unrecognized mode", () => {
    expect(() =>
      resolveAuthMode("anthropic", { env: { LEANSMITH_AUTH_MODE: "oauth" }, config: {} }),
    ).toThrow(/must be "subscription" or "api"/);
  });
});

describe("resolveProviderAuth", () => {
  it("refuses api mode with no key rather than billing the subscription", () => {
    expect(() =>
      resolveProviderAuth("anthropic", { env: { LEANSMITH_AUTH_MODE: "api" }, config: {} }),
    ).toThrow(/no API key is configured/);
  });

  it("carries no key in subscription mode even when one is configured", () => {
    expect(
      resolveProviderAuth("anthropic", { env: {}, config: { anthropicApiKey: "sk-x" } }),
    ).toEqual({ mode: "subscription" });
  });
});

describe("local.json reaches the dispatchers (no-argument resolution)", () => {
  it("turns a file-configured api mode into the claude flag that actually bills the key", async () => {
    const auth = await authWithLocalJson({
      anthropicAuth: "api",
      anthropicApiKey: "sk-ant-file",
    });
    // The composition that shipped wrong: resolution said `api` in isolation while
    // the dispatcher still emitted subscription flags. Assert the whole chain.
    expect(claudeAuthArgs(auth.resolveProviderAuth("anthropic", { env: {} }).mode)).toEqual([
      "--bare",
    ]);
  });

  it("refuses to bootstrap the operator's own codex home", async () => {
    const auth = await authWithLocalJson({
      openaiAuth: "api",
      openaiApiKey: "sk-oai-file",
      codexApiHome: "~/.codex",
    });
    // Logging into ~/.codex with an API key deletes the stored ChatGPT credentials —
    // the exact loss the separate-home design exists to prevent.
    expect(() => auth.codexHome({ env: {} })).toThrow(/must NOT be the operator's codex home/);
  });
});

describe("codexHome", () => {
  it("uses a separate home in api mode so the ChatGPT login is not evicted", () => {
    const home = codexHome({
      env: { LEANSMITH_OPENAI_AUTH: "api" },
      config: { openaiApiKey: "sk-x" },
    });
    expect(home).toBe(path.join(os.homedir(), ".codex-leansmith-api"));
    expect(home).not.toBe(path.join(os.homedir(), ".codex"));
  });
});

describe("workerEnv", () => {
  it("redirects CODEX_HOME only when the codex side is on api billing", () => {
    const out = workerEnv({
      env: { PATH: "/usr/bin" },
      config: { authMode: "api", anthropicApiKey: "sk-ant", openaiApiKey: "sk-oai" },
    });
    expect(out.ANTHROPIC_API_KEY).toBe("sk-ant");
    expect(out.OPENAI_API_KEY).toBe("sk-oai");
    expect(out.CODEX_HOME).toBe(path.join(os.homedir(), ".codex-leansmith-api"));
    expect(out.PATH).toBe("/usr/bin");
    const claudeOnly = workerEnv({
      env: { PATH: "/usr/bin" },
      config: { anthropicAuth: "api", anthropicApiKey: "sk-ant" },
    });
    expect(claudeOnly.ANTHROPIC_API_KEY).toBe("sk-ant");
    expect(claudeOnly.CODEX_HOME).toBeUndefined();
  });
});

describe("claudeConfigDir", () => {
  it("is an account switch, not a billing switch: it does not imply api mode", () => {
    const dir = tempDir();
    const inputs = { env: {} as NodeJS.ProcessEnv, config: { claudeConfigDir: dir } };
    expect(resolveAuthMode("anthropic", inputs)).toBe("subscription");
    expect(workerEnv(inputs).ANTHROPIC_API_KEY).toBeUndefined();
  });
});
