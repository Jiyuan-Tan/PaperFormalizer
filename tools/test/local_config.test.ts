import { afterEach, describe, expect, it, vi } from "vitest";

async function localConfigWith(file: string | null) {
  vi.resetModules();
  vi.doMock("node:fs", async (importOriginal) => {
    const actual = await importOriginal<typeof import("node:fs")>();
    const mockedFs = {
      ...actual,
      existsSync: () => file !== null,
      readFileSync: () => file ?? "",
    };
    return {
      ...mockedFs,
      default: mockedFs,
    };
  });
  return import("../src/local_config.js");
}

const realPlatform = process.platform;
const realGitBashEnv = process.env.CLAUDE_CODE_GIT_BASH_PATH;
function setPlatform(p: NodeJS.Platform) {
  Object.defineProperty(process, "platform", { value: p, configurable: true });
}

afterEach(() => {
  vi.restoreAllMocks();
  vi.resetModules();
  vi.doUnmock("node:fs");
  setPlatform(realPlatform);
  if (realGitBashEnv === undefined) delete process.env.CLAUDE_CODE_GIT_BASH_PATH;
  else process.env.CLAUDE_CODE_GIT_BASH_PATH = realGitBashEnv;
});

describe("bashBinary", () => {
  const cfg = '{"gitBashPath": "C:/Program Files/Git/bin/bash.exe"}';

  it.each([
    ["CLAUDE_CODE_GIT_BASH_PATH wins over the file on Windows", "win32", "D:/Git/bin/bash.exe", "D:/Git/bin/bash.exe"],
    ["the configured git-bash is spawned on Windows", "win32", undefined, "C:/Program Files/Git/bin/bash.exe"],
    ["gitBashPath is ignored off Windows", "linux", undefined, "bash"],
  ] as const)("%s", async (_label, platform, envPath, expected) => {
    if (envPath === undefined) delete process.env.CLAUDE_CODE_GIT_BASH_PATH;
    else process.env.CLAUDE_CODE_GIT_BASH_PATH = envPath;
    setPlatform(platform);
    expect((await localConfigWith(cfg)).bashBinary()).toBe(expected);
  });
});

describe("localConfig obsolete keys", () => {
  it("ignores the retired module-system key with a one-line warning", async () => {
    const obsoleteKey = ["module", "System"].join("");
    const warn = vi.spyOn(console, "warn").mockImplementation(() => {});
    const { localConfig } = await localConfigWith(JSON.stringify({ [obsoleteKey]: false }));
    expect(localConfig().codexSandbox).toBe("workspace-write");
    expect(warn).toHaveBeenCalledOnce();
    expect(warn.mock.calls[0]?.[0]).toMatch(/ignoring obsolete .*always enabled/);
    expect(String(warn.mock.calls[0]?.[0])).not.toContain("\n");
  });
});
