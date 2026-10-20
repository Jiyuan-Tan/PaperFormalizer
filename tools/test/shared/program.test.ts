import { chmodSync, mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterAll, describe, expect, it } from "vitest";
import { findExecutable, probeProgram } from "../../src/shared/program.js";
import { probeResult } from "../../src/claude_roles.js";

const tmp = mkdtempSync(path.join(os.tmpdir(), "tc-program-"));
afterAll(() => rmSync(tmp, { recursive: true, force: true }));
const windows = process.platform === "win32";
const envAt = (directory: string): NodeJS.ProcessEnv => {
  const env = Object.fromEntries(Object.entries(process.env).filter(([key]) => !["PATH", "PATHEXT"].includes(key.toUpperCase())));
  return { ...env, [windows ? "Path" : "PATH"]: directory, PATHEXT: ".COM;.EXE;.BAT;.CMD" };
};

describe("program lookup", () => {
  it("finds an executable by its absolute path without PATH", () => {
    expect(findExecutable(process.execPath, { env: envAt("") })).toBe(process.execPath);
    expect(findExecutable("no-such-leansmith-program", { env: envAt(tmp) })).toBeNull();
  });

  it.skipIf(!windows)("finds .exe files in quoted Windows Path entries with PATHEXT", () => {
    const bin = path.join(tmp, "TeX tools");
    mkdirSync(bin);
    const executable = path.join(bin, "pdflatex.exe");
    writeFileSync(executable, "fixture");
    const env = envAt(`"${bin}"`);
    expect(findExecutable("pdflatex", { env, nativeOnly: true })).toBe(executable);
    expect(findExecutable(executable, { env })).toBe(executable);
    expect(findExecutable("latexmk", { env })).toBeNull();
  });

  it.skipIf(!windows)("does not treat directories or npm batch shims as native executables", () => {
    const bin = path.join(tmp, "shims");
    mkdirSync(bin);
    mkdirSync(path.join(bin, "pdflatex.exe"));
    writeFileSync(path.join(bin, "claude.cmd"), "@exit /b 0\r\n");
    expect(findExecutable("pdflatex", { env: envAt(bin) })).toBeNull();
    expect(findExecutable("claude", { env: envAt(bin) })).toBe(path.join(bin, "claude.cmd"));
    expect(findExecutable("claude", { env: envAt(bin), nativeOnly: true })).toBeNull();
  });

  it.skipIf(windows)("requires executable permission on POSIX", () => {
    const executable = path.join(tmp, "posix-tool");
    writeFileSync(executable, "#!/bin/sh\nexit 0\n", { mode: 0o644 });
    expect(findExecutable("posix-tool", { env: envAt(tmp) })).toBeNull();
    chmodSync(executable, 0o755);
    expect(findExecutable("posix-tool", { env: envAt(tmp) })).toBe(executable);
  });
});

describe("program probes", () => {
  it("preserves the distinction between missing programs and programs that fail", () => {
    const missing = probeProgram("no-such-leansmith-program", [], envAt(tmp));
    expect(probeResult(missing)).toBe("missing");
    const failed = probeProgram(process.execPath, ["-e", "process.exit(7)"]);
    expect(probeResult(failed)).toBe("exit");
    expect(failed.status).toBe(7);
  });

  it.skipIf(!windows)("runs npm-style .cmd probes and rejects shell syntax before launching", () => {
    const bin = path.join(tmp, "npm tools");
    mkdirSync(bin);
    const script = path.join(bin, "args.cjs");
    writeFileSync(script, "console.log(JSON.stringify(process.argv.slice(2)));\n");
    writeFileSync(path.join(bin, "claude.cmd"), `@echo off\r\n"${process.execPath}" "${script}" %*\r\n`);
    const args = ["--version", "two words"];
    const result = probeProgram("claude", args, { ...envAt(bin), LEANSMITH_TEST_MODEL_SHIM: path.join(bin, "claude.cmd") });
    expect(probeResult(result), result.stderr).toBe("ok");
    expect(JSON.parse(result.stdout)).toEqual(args);
    expect(result.stderr).toBe("");
    for (const unsafe of ["a&echo injected", "quoted\"value", "a|b", "%PATH%", "x\ny", "!PATH!"]) {
      const rejected = probeProgram("claude", [unsafe], envAt(bin));
      expect(probeResult(rejected)).toBe("unknown");
      expect(rejected.error).toMatchObject({ code: "EINVAL" });
      expect(rejected.stdout).toBe("");
    }
  });
});
