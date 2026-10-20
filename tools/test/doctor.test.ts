import { describe, expect, it, vi } from "vitest";
import { existsSync } from "node:fs";
import os from "node:os";
import { doctorChecks, doctorReport, versionAtLeast, type Probe } from "../src/doctor.js";
import { helpText, parseLeanSmithCommand, LEANSMITH_USAGE } from "../bin/leansmith.js";

/** A machine on which only the programs in `have` work, and only the logins in `loggedIn`. */
const machine = (have: string[], loggedIn: string[] = []): Probe => (bin, args) => {
  if (args[0] === "login" || args[0] === "auth") return { ok: loggedIn.includes(bin), out: "" };
  return { ok: have.includes(bin), out: `${bin} 1.0` };
};
/** The settings a test names, so that this machine's `config/local.json` is not what is tested. */
const HERE = { leanLspMcpBinary: "lean-lsp-mcp", codexSandbox: "danger-full-access", platform: "linux" as const };
const byName = (checks: ReturnType<typeof doctorChecks>) => Object.fromEntries(checks.map((c) => [c.name, c]));

describe("leansmith doctor", () => {
  it("checks the configured Git Bash on Windows and gives Windows prerequisite instructions", () => {
    const options = { ...HERE, platform: "win32" as const, gitBashPath: "E:/Git/bin/bash.exe" };
    const absent = byName(doctorChecks(machine([]), "18.0.0", options));
    expect(absent["Git Bash"]).toMatchObject({ required: true, ok: false, fix: expect.stringContaining("gitBashPath") });
    expect(absent.node!.fix).toContain("https://nodejs.org/en/download");
    expect(absent["elan (Lean)"]!.fix).toContain("elan-init.ps1");
    const present = byName(doctorChecks(machine([options.gitBashPath]), "22.0.0", options));
    expect(present["Git Bash"]).toMatchObject({ required: true, ok: true });
  });

  it("compares dotted versions", () => {
    expect(versionAtLeast("22.1.0", "20.20.2")).toBe(true);
    expect(versionAtLeast("v20.20.2", "20.20.2")).toBe(true);
    expect(versionAtLeast("20.9.0", "20.20.2")).toBe(false);
  });

  it("is ready when every required program is present and logged in; optional ones do not block", () => {
    const checks = doctorChecks(machine(["git", "elan", "lean-lsp-mcp", "codex", "claude"], ["codex", "claude"]), "22.0.0", HERE);
    expect(checks.filter((c) => c.required && !c.ok)).toEqual([]);
    expect(byName(checks).pdflatex).toMatchObject({ required: false, ok: false });
    expect(doctorReport(checks)).toContain("Ready: every required item is present.");
  });

  it("names each missing program, an old Node and a missing login, each with how to get it", () => {
    const checks = byName(doctorChecks(machine(["git", "codex", "claude"], ["claude"]), "18.0.0", HERE));
    expect(checks["elan (Lean)"]).toMatchObject({ ok: false, fix: expect.stringContaining("elan-init.sh") });
    expect(checks["lean-lsp-mcp"]).toMatchObject({ ok: false, fix: expect.stringContaining("pipx install lean-lsp-mcp") });
    expect(checks.node).toMatchObject({ ok: false, fix: expect.stringContaining("node_env.sh") });
    expect(checks["codex login"]).toMatchObject({ ok: false, fix: expect.stringContaining("codex login") });
    expect(checks["claude login"]!.ok).toBe(true);
    const report = doctorReport(Object.values(checks));
    expect(report).toMatch(/MISSING elan \(Lean\)/);
    expect(report).toContain("Not ready: node, elan (Lean), lean-lsp-mcp, codex login.");
  });

  describe("claude, when its roles can run on codex", () => {
    const rest = ["git", "elan", "lean-lsp-mcp", "codex"];
    const AUTO = { ...HERE, claudeRoles: null };

    it("with no setting: a missing or logged-out claude is optional, noted as running on codex, and the machine is ready", () => {
      const missing = doctorChecks(machine(rest, ["codex"]), "22.0.0", AUTO);
      expect(byName(missing).claude).toMatchObject({ required: false, ok: false, detail: expect.stringContaining("its roles will run on codex") });
      expect(byName(missing)["claude login"]).toBeUndefined();
      const report = doctorReport(missing, "codex");
      expect(report).toContain("Ready: every required item is present.");
      expect(report).toMatch(/absent {2}claude .*its roles will run on codex \(optional\)/);
      expect(report).toMatch(/Models called .*; the claude roles run on codex \S+\.$/m);
      expect(report).not.toMatch(/; claude \S+\.$/m);

      const loggedOut = doctorChecks(machine([...rest, "claude"], ["codex"]), "22.0.0", AUTO);
      expect(byName(loggedOut)["claude login"]).toMatchObject({ required: false, ok: false, detail: expect.stringContaining("its roles will run on codex") });
      expect(doctorReport(loggedOut, "codex")).toContain("Ready: every required item is present.");
    });

    it("with `claudeRoles: claude` a missing claude is MISSING; with `codex` it is not asked", () => {
      const pinned = doctorChecks(machine(rest, ["codex"]), "22.0.0", { ...HERE, claudeRoles: "claude" });
      expect(byName(pinned).claude).toMatchObject({ required: true, ok: false, fix: expect.stringContaining("claude-code") });
      expect(doctorReport(pinned)).toContain("Not ready: claude.");
      expect(doctorReport(pinned)).toMatch(/; claude \S+\.$/m);

      const asked: string[] = [];
      const run: Probe = (bin, args, env, cwd) => { asked.push(bin); return machine(rest, ["codex"])(bin, args, env, cwd); };
      const onCodex = doctorChecks(run, "22.0.0", { ...HERE, claudeRoles: "codex" });
      expect(byName(onCodex).claude).toMatchObject({ required: false, ok: true, detail: expect.stringContaining("its roles run on codex") });
      expect(asked).not.toContain("claude");
      expect(doctorReport(onCodex, "codex")).toContain("Ready: every required item is present.");
    });
  });

  it("an invalid `claudeRoles` value is a MISSING line naming the allowed values", () => {
    vi.stubEnv("LEANSMITH_CLAUDE_ROLES", "gpt");
    try {
      const checks = doctorChecks(machine(["git", "elan", "lean-lsp-mcp", "codex", "claude"], ["codex", "claude"]), "22.0.0", HERE);
      expect(byName(checks).claudeRoles).toMatchObject({ required: true, ok: false, detail: expect.stringContaining('must be "claude" or "codex"; got "gpt"') });
      expect(doctorReport(checks)).toContain("Not ready: claudeRoles.");
    } finally {
      vi.unstubAllEnvs();
    }
  });

  it("does not ask a missing CLI for its login", () => {
    expect(byName(doctorChecks(machine(["git"]), "22.0.0", HERE))["codex login"]).toBeUndefined();
  });

  describe("the Codex sandbox (codexSandbox: workspace-write)", () => {
    const all = ["git", "elan", "lean-lsp-mcp", "codex", "claude"];
    /** A machine whose `codex sandbox` prints `help` (null: no such command) and whose sandbox says `said` (null: it starts). */
    const sandboxed = (help: string | null, said: string | null, calls: string[][] = []): Probe => (bin, args, env, cwd) => {
      if (bin !== "codex" || args[0] !== "sandbox") return machine(all, ["codex", "claude"])(bin, args, env, cwd);
      calls.push([...args, cwd ?? ""]);
      if (args[1] === "--help") return { ok: help !== null, out: "", all: help ?? "error: unrecognized subcommand 'sandbox'" };
      return { ok: said === null, out: "", all: said ?? "ok" };
    };
    const sandbox = (run: Probe, platform: NodeJS.Platform = "linux", codexSandbox = "workspace-write") =>
      byName(doctorChecks(run, "22.0.0", { ...HERE, codexSandbox, platform }))["codex sandbox"];

    it("is ok when a command runs under it, in a scratch directory of the OS temp dir", () => {
      const calls: string[][] = [];
      expect(sandbox(sandboxed("Usage: codex sandbox [OPTIONS] [COMMAND]...", null, calls))).toMatchObject({ required: true, ok: true, detail: expect.stringContaining("starts") });
      expect(calls[1]!.slice(0, 4)).toEqual(["sandbox", "--", "/bin/sh", "-c"]);
      expect(calls[1]!.at(-1)).toContain(os.tmpdir());
      expect(existsSync(calls[1]!.at(-1)!)).toBe(false);
      // a CLI whose `sandbox` names the platform
      const older: string[][] = [];
      const help = "Usage: codex sandbox <COMMAND>\n\nCommands:\n  macos    Run under Seatbelt\n  linux    Run under Landlock\n";
      expect(sandbox(sandboxed(help, null, older), "darwin")!.ok).toBe(true);
      expect(older[1]!.slice(0, 3)).toEqual(["sandbox", "macos", "--"]);
    });

    it("is a missing REQUIRED item when the sandbox cannot start: its first error line, and the two ways out", () => {
      const checks = doctorChecks(sandboxed("Usage: codex sandbox [OPTIONS] [COMMAND]...", "WARNING: stale temp dirs\nbwrap: Can't mkdir parents for /scr/x: Permission denied\nmore"), "22.0.0", { ...HERE, codexSandbox: "workspace-write", platform: "linux" });
      const c = byName(checks)["codex sandbox"]!;
      expect(c).toMatchObject({ required: true, ok: false, detail: "cannot start: bwrap: Can't mkdir parents for /scr/x: Permission denied" });
      expect(c.fix).toMatch(/bubblewrap \/ user namespaces \/ a writable temp directory/);
      expect(c.fix).toMatch(/set `codexSandbox` to `danger-full-access` in tools\/config\/local\.json — which lets the model workers read and write anywhere your user can; that choice is the machine owner's/);
      expect(doctorReport(checks)).toContain("Not ready: codex sandbox.");
    });

    it("is ok with a note when this codex cannot be asked; not checked at all under danger-full-access", () => {
      for (const run of [sandboxed(null, "never run"), sandboxed("Commands:\n  macos    Run under Seatbelt\n", "never run")]) {
        expect(sandbox(run)).toMatchObject({ ok: true, detail: expect.stringContaining("could not check") });
      }
      expect(sandbox(sandboxed("x", "broken"), "linux", "danger-full-access")).toBeUndefined();
      expect(byName(doctorChecks(machine(["git"]), "22.0.0", { ...HERE, codexSandbox: "workspace-write" }))["codex sandbox"]).toBeUndefined();
    });
  });

  it("--help prints a command's usage instead of running it, for every command", async () => {
    expect(await helpText(["--help"])).toBe(LEANSMITH_USAGE);
    const modes = /<([a-z|-]+)> <args/.exec(LEANSMITH_USAGE)![1]!.split("|");
    expect(modes.length).toBeGreaterThan(10);
    for (const mode of modes) {
      for (const args of [["--help"], ["x", "-h"]]) expect(await helpText([mode, ...args])).toMatch(new RegExp(`^Usage: leansmith ${mode}\\b`));
      expect(await helpText([mode, "x"])).toBeNull();
    }
    expect(await helpText(["ui", "--help"])).toContain("--port N");
  }, 60_000);

  it("is a command of the CLI", () => {
    expect(parseLeanSmithCommand(["doctor"]).mode).toBe("doctor");
  });
});
