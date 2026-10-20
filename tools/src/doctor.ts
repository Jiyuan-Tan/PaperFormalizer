// `leansmith doctor`: what this machine needs before `init` and `verify`, each checked, with
// how to get what is missing. It reads versions and login states only: no model call, no build.
import { existsSync, mkdtempSync, readFileSync, rmSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { claudeRolesSetting, resolveAuth, workerEnv, type ClaudeRolesRunner } from "./auth.js";
import { codexRoleModel, decideClaudeRoles } from "./claude_roles.js";
import { localConfig } from "./local_config.js";
import { MODELS } from "./models.js";
import { leanSmithToolsDir } from "./toolkit/config.js";
import { probeProgram } from "./shared/program.js";

export interface DoctorCheck {
  name: string;
  required: boolean;
  ok: boolean;
  /** The version found, or what is wrong. */
  detail: string;
  /** How to get it, when it is missing. */
  fix?: string;
}

/** Run a program (in `cwd`, when given); `ok` when it started and exited 0, `out` the first line it
 *  printed, `all` everything it printed (stdout, then stderr). Injected in tests. */
export type Probe = (bin: string, args: string[], env?: NodeJS.ProcessEnv, cwd?: string) => { ok: boolean; out: string; all?: string };

const probe: Probe = (bin, args, env, cwd) => {
  const r = probeProgram(bin, args, env, cwd);
  const out = `${r.stdout ?? ""}`.trim().split(/\r?\n/)[0] ?? "";
  return { ok: !r.error && r.status === 0, out: out.startsWith("usage") ? "found" : out.trim(), all: `${r.stdout ?? ""}\n${r.stderr ?? ""}` };
};

/** How to get past a Codex sandbox that cannot start. Widening it is the machine owner's choice. */
export const CODEX_SANDBOX_FIX =
  "the sandbox the Codex workers run in cannot start on this machine, so they can neither read the paper nor write their output: " +
  "either repair it (bubblewrap / user namespaces / a writable temp directory) or, if this machine is itself a sandbox you trust, " +
  "set `codexSandbox` to `danger-full-access` in tools/config/local.json — which lets the model workers read and write anywhere " +
  "your user can; that choice is the machine owner's";

/**
 * Whether Codex's local sandbox starts here: a command run under `codex sandbox` in a scratch
 * directory, no model call (it writes nothing: the command's default policy may be read-only). `null`: this codex cannot be asked (no `sandbox` command, or none for
 * this platform). Older CLIs name the platform (`codex sandbox linux -- …`); newer ones do not.
 */
function codexSandboxCheck(run: Probe, env: NodeJS.ProcessEnv, platform: NodeJS.Platform): { ok: boolean; detail: string } | null {
  const help = run("codex", ["sandbox", "--help"], env);
  if (!help.ok || platform === "win32") return null;
  const subcommands = [...(help.all ?? "").matchAll(/^\s+(macos|linux|windows)\b/gm)].map((m) => m[1]!);
  const mine = platform === "darwin" ? "macos" : "linux";
  if (subcommands.length > 0 && !subcommands.includes(mine)) return null;
  const scratch = mkdtempSync(path.join(os.tmpdir(), "leansmith-doctor-"));
  try {
    const r = run("codex", ["sandbox", ...(subcommands.length > 0 ? [mine] : []), "--", "/bin/sh", "-c", "echo ok"], env, scratch);
    if (r.ok) return { ok: true, detail: "starts (a command ran in a scratch directory)" };
    const said = (r.all ?? r.out).split(/\r?\n/).map((l) => l.trim()).find((l) => l && !/^warning:/i.test(l));
    return { ok: false, detail: `cannot start${said ? `: ${said}` : ""}` };
  } finally {
    rmSync(scratch, { recursive: true, force: true });
  }
}

/** `a >= b` for dotted versions. */
export function versionAtLeast(a: string, b: string): boolean {
  const [x, y] = [a, b].map((v) => v.replace(/^v/, "").split(".").map(Number));
  for (let i = 0; i < Math.max(x!.length, y!.length); i++) {
    if ((x![i] ?? 0) !== (y![i] ?? 0)) return (x![i] ?? 0) > (y![i] ?? 0);
  }
  return true;
}

export function doctorChecks(
  run: Probe = probe,
  nodeVersion = process.versions.node,
  /** The sandbox the Codex workers are configured to run in, the platform, and the `claudeRoles`
   *  setting (null: none) (tests). */
  machine: { codexSandbox?: string; platform?: NodeJS.Platform; leanLspMcpBinary?: string; claudeRoles?: ClaudeRolesRunner | null; gitBashPath?: string } = {},
): DoctorCheck[] {
  const platform = machine.platform ?? process.platform;
  const windows = platform === "win32";
  const tools = leanSmithToolsDir();
  const floor = /">=\s*([0-9.]+)"/.exec(readFileSync(path.join(tools, "package.json"), "utf8"))?.[1] ?? "20.20.2";
  const out: DoctorCheck[] = [];
  const program = (name: string, required: boolean, bin: string, args: string[], fix: string, absent = ""): boolean => {
    const r = run(bin, args);
    out.push({ name, required, ok: r.ok, detail: r.ok ? r.out : `\`${bin}\` not found or not working${absent}`, ...(r.ok ? {} : { fix }) });
    return r.ok;
  };

  program("git", true, "git", ["--version"], "install git (https://git-scm.com/downloads)");
  if (windows) {
    const bash = machine.gitBashPath ?? localConfig().gitBashPath;
    const fix = "install Git for Windows and set gitBashPath to its bin/bash.exe in config/local.json (README \"Windows setup\")";
    if (bash) program("Git Bash", true, bash, ["--version"], fix);
    else out.push({ name: "Git Bash", required: true, ok: false, detail: "gitBashPath is not configured", fix });
  }
  const nodeOk = versionAtLeast(nodeVersion, floor);
  out.push({
    name: "node", required: true, ok: nodeOk, detail: `v${nodeVersion} (needs >= ${floor})`,
    ...(nodeOk ? {} : { fix: windows
      ? `install Node ${floor} or newer for Windows (https://nodejs.org/en/download), then reopen Git Bash`
      : `install Node ${floor} or newer (\`nvm install ${floor.split(".")[0]}\`), then \`source scripts/node_env.sh\`` }),
  });
  program("elan (Lean)", true, "elan", ["--version"], windows
    ? "install elan with elan-init.ps1 (https://github.com/leanprover/elan#installation), then reopen Git Bash"
    : "curl https://elan.lean-lang.org/elan-init.sh -sSf | sh   (then open a new shell)");
  const lsp = machine.leanLspMcpBinary ?? localConfig().leanLspMcpBinary;
  program("lean-lsp-mcp", true, lsp, ["--help"], "pipx install lean-lsp-mcp   (or `uv tool install lean-lsp-mcp`; or set leanLspMcpBinary in config/local.json)");

  // The model CLIs, and the account each one's calls are billed to.
  let auth: ReturnType<typeof resolveAuth> | null = null;
  let env: NodeJS.ProcessEnv = process.env;
  try {
    auth = resolveAuth();
    env = workerEnv();
  } catch (err) {
    out.push({ name: "billing", required: true, ok: false, detail: err instanceof Error ? err.message : String(err), fix: "fix config/local.json (README \"Accounts and cost\")" });
  }
  const login = (name: string, bin: string, account: { mode: "subscription" | "api"; apiKey?: string } | undefined, args: string[], fix: string, required = true, absent = ""): void => {
    if (account?.mode === "api") {
      const ok = Boolean(account.apiKey);
      out.push({ name, required, ok, detail: ok ? "API key configured" : `api mode with no API key${absent}`, ...(ok ? {} : { fix }) });
    } else if (account) {
      const r = run(bin, args, env);
      out.push({ name, required, ok: r.ok, detail: r.ok ? "logged in" : `not logged in (\`${bin} ${args.join(" ")}\` failed)${absent}`, ...(r.ok ? {} : { fix }) });
    }
  };
  if (program("codex", true, "codex", ["--version"], "npm install -g @openai/codex")) {
    login("codex login", "codex", auth?.openai, ["login", "status"], "run `codex login` (or bill an API key: README \"Accounts and cost\")");
    // Under `danger-full-access` no sandbox is started: nothing to check.
    if ((machine.codexSandbox ?? localConfig().codexSandbox) === "workspace-write") {
      const sandbox = codexSandboxCheck(run, env, platform);
      if (sandbox) out.push({ name: "codex sandbox", required: true, ...sandbox, ...(sandbox.ok ? {} : { fix: CODEX_SANDBOX_FIX }) });
      else out.push({ name: "codex sandbox", required: true, ok: true, detail: "could not check (this codex has no `sandbox` command for this platform)" });
    }
  }
  // claude is required only when its roles are pinned to it (`claudeRoles`); with no setting a
  // machine without a usable claude runs those roles on codex (`claude_roles.ts`).
  let pinned: ClaudeRolesRunner | null = machine.claudeRoles ?? null;
  if (machine.claudeRoles === undefined) {
    try {
      pinned = claudeRolesSetting()?.runner ?? null;
    } catch (err) {
      out.push({ name: "claudeRoles", required: true, ok: false, detail: err instanceof Error ? err.message : String(err), fix: "set `claudeRoles` (config/local.json) or LEANSMITH_CLAUDE_ROLES to \"claude\" or \"codex\", or remove it" });
    }
  }
  if (pinned === "codex") {
    out.push({ name: "claude", required: false, ok: true, detail: "not used: `claudeRoles` is `codex`, so its roles run on codex" });
  } else {
    const required = pinned === "claude";
    const absent = required ? "" : " — its roles will run on codex";
    if (program("claude", required, "claude", ["--version"], "npm install -g @anthropic-ai/claude-code", absent)) {
      login("claude login", "claude", auth?.anthropic, ["auth", "status"], "run `claude`, then `/login` (or bill an API key: README \"Accounts and cost\")", required, absent);
    }
  }

  const local = existsSync(path.join(tools, "config", "local.json"));
  out.push({ name: "config/local.json", required: false, ok: local, detail: local ? "present" : "absent (the defaults apply)", ...(local ? {} : { fix: "cp config/local.example.json config/local.json" }) });
  program("pdflatex", false, "pdflatex", ["--version"], "install TeX Live (or MacTeX): without it the annotated paper is written as TeX only, no PDF");
  for (const [bin, args] of [["curl", ["--version"]], ["tar", ["--version"]], ["zstd", ["--version"]]] as const) {
    program(bin, false, bin, [...args], "only for a library's prebuilt cache (Causalean, StatLean): without it Lake compiles that library from source — your package manager");
  }
  return out;
}

export function doctorReport(checks: readonly DoctorCheck[], claudeRoles: ClaudeRolesRunner = "claude"): string {
  const lines = checks.map((c) => {
    const mark = c.ok ? "ok     " : c.required ? "MISSING" : "absent ";
    return `  ${mark} ${c.name.padEnd(18)} ${c.detail}${c.required ? "" : " (optional)"}${c.fix ? `\n          -> ${c.fix}` : ""}`;
  });
  const missing = checks.filter((c) => c.required && !c.ok).map((c) => c.name);
  return [
    "LeanSmith prerequisites:",
    ...lines,
    `Models called (the accounts need access; tools/src/models.ts): codex ${[...new Set([MODELS.codexKernel, MODELS.codexVerify, MODELS.codexMechanical])].join(", ")}; ${claudeRoles === "codex" ? `the claude roles run on codex ${codexRoleModel()}` : `claude ${MODELS.claudeMain}`}.`,
    missing.length ? `Not ready: ${missing.join(", ")}.` : "Ready: every required item is present.",
  ].join("\n");
}

export const DOCTOR_USAGE = "Usage: leansmith doctor\n  check this machine's prerequisites (programs, versions, logins); exit 1 when a required one is missing.";

export function runDoctorCli(args: string[]): void {
  if (args.length > 0) throw new Error(DOCTOR_USAGE);
  const checks = doctorChecks();
  // The same rule the pipeline applies at its first claude-role call; a broken billing setting is
  // already a MISSING line above, and the roles are then reported on their default.
  let roles: ClaudeRolesRunner = "claude";
  try {
    roles = decideClaudeRoles().runner;
  } catch { /* reported by the `billing` check */ }
  console.log(doctorReport(checks, roles));
  if (checks.some((c) => c.required && !c.ok)) process.exitCode = 1;
}
