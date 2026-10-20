import { execFile, execSync, spawnSync } from "node:child_process";
import { promisify } from "node:util";
import { existsSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { execaSync } from "execa";
import { describe, expect, it } from "vitest";

describe("test model CLI isolation", () => {
  it.each(["codex", "claude", "codex.exe", "claude.cmd"])("refuses %s without an explicit fake", (command) => {
    expect(() => spawnSync(command, ["--version"])).toThrow("Tests refuse to launch the model CLI");
  });

  it("keeps the guard in spawned Node processes", () => {
    const code = `
const { spawnSync } = require("node:child_process");
try { spawnSync("codex", ["--version"]); process.exit(1); }
catch (error) { console.log(error.message); }
`;
    const result = spawnSync(process.execPath, ["-e", code], { encoding: "utf8" });
    expect(result.status, result.stderr).toBe(0);
    expect(result.stdout).toContain("Tests refuse to launch the model CLI");
  });

  it("also blocks shell wrappers and shell execution APIs", () => {
    for (const command of ["cmd.exe", "bash", "powershell.exe"]) {
      expect(() => spawnSync(command, ["-c", "echo codex --version"])).toThrow("through a shell");
    }
    expect(() => execSync("echo claude --version")).toThrow("through a shell");
  });

  it("preserves promisified execFile's output and isolation", async () => {
    const run = promisify(execFile);
    const result = await run(process.execPath, ["-e", "console.log('fixture')"]);
    expect(result.stdout.trim()).toBe("fixture");
    expect(result.stderr).toBe("");
    await expect(run("codex", ["--version"])).rejects.toThrow("Tests refuse to launch the model CLI");
  });

  it.skipIf(process.platform !== "win32")("blocks execa's npm shim wrapper before a harmless fake can execute", () => {
    const dir = mkdtempSync(path.join(tmpdir(), "tc-model-guard-"));
    const shim = path.join(dir, "codex.cmd"), marker = path.join(dir, "executed");
    try {
      writeFileSync(shim, `@echo off\r\necho executed > "${marker}"\r\n`);
      expect(() => execaSync(shim, ["--version"])).toThrow(/Tests refuse/);
      expect(existsSync(marker)).toBe(false);
    } finally {
      rmSync(dir, { recursive: true, force: true });
    }
  });
});
