// Which CLI runs the claude roles: the F1 plan author, the second F4 reviewer, the promotion-round
// curator, the gardener and the study coordinator. By default the pipeline runs on two accounts
// (codex and claude); on a machine with codex alone those roles run on codex. The choice is made
// ONCE per process and logged once — a claude call that fails mid-run fails as it always did, it
// never moves the run to the other runner.
import { probeProgram } from "./shared/program.js";
import {
  claudeRolesSetting,
  resolveApiKey,
  resolveAuthMode,
  workerEnv,
  type AuthInputs,
  type ClaudeRolesRunner,
} from "./auth.js";
import { MODELS } from "./models.js";

export type { ClaudeRolesRunner };

export interface ClaudeRoles {
  runner: ClaudeRolesRunner;
  /** True when the operator set it (`claudeRoles` / `LEANSMITH_CLAUDE_ROLES`). */
  explicit: boolean;
  /** True when it is the runner the run recorded at its first decision (`state.json` `claude_roles`). */
  recorded?: boolean;
  /** Why, in plain words: the setting's source, the run's record, or what this machine has. */
  reason: string;
}

/**
 * How a probed program ended: `ok` (exit 0), `missing` (no such program: ENOENT), `exit` (it ran
 * and exited non-zero by itself), `unknown` (anything else: a timeout, a signal, EAGAIN, a spawn
 * failure) — which says nothing about the program and never moves the roles off claude.
 */
export type ProbeResult = "ok" | "missing" | "exit" | "unknown";

/** Run a program and say how it ended. Injected in tests. */
export type RolesProbe = (bin: string, args: string[], env?: NodeJS.ProcessEnv) => ProbeResult;

/** What `spawnSync` returned, as a `ProbeResult`. */
export function probeResult(r: { error?: Error; status: number | null; signal?: string | null }): ProbeResult {
  if (r.error) return (r.error as NodeJS.ErrnoException).code === "ENOENT" ? "missing" : "unknown";
  if (r.status === 0) return "ok";
  return typeof r.status === "number" && !r.signal ? "exit" : "unknown";
}

const probe: RolesProbe = (bin, args, env) =>
  probeResult(probeProgram(bin, args, env));

/** Why `claude` cannot run its roles on this machine, or null when it can — the checks `doctor`
 *  prints. Only two findings count against it: its CLI does not exist, or `claude auth status`
 *  itself says it is logged out (in api mode: no key is configured). */
export function claudeUnavailable(run: RolesProbe = probe, inputs: AuthInputs = {}): string | null {
  if (run("claude", ["--version"]) === "missing") return "its CLI is not installed";
  if (resolveAuthMode("anthropic", inputs) === "api") {
    return resolveApiKey("anthropic", inputs) ? null : "api mode is selected with no Anthropic API key";
  }
  return run("claude", ["auth", "status"], workerEnv(inputs)) === "exit" ? "it is not logged in" : null;
}

/**
 * The rule: an explicit setting wins; with none, the runner this run recorded at its first
 * decision (`recorded`: a resume is a new process and keeps it, asking no CLI — a recorded claude
 * that has since gone fails as any claude call does); with neither, claude when it is usable
 * here, else codex.
 */
export function decideClaudeRoles(run: RolesProbe = probe, inputs: AuthInputs = {}, recorded?: ClaudeRolesRunner): ClaudeRoles {
  const setting = claudeRolesSetting(inputs);
  if (setting) return { runner: setting.runner, explicit: true, reason: `set by ${setting.source}` };
  if (recorded) return { runner: recorded, explicit: false, recorded: true, reason: "as recorded for this run" };
  const missing = claudeUnavailable(run, inputs);
  return missing
    ? { runner: "codex", explicit: false, reason: missing }
    : { runner: "claude", explicit: false, reason: "claude is available" };
}

/** The model a claude role runs on under codex (high effort). */
export function codexRoleModel(): string {
  return MODELS.codexKernel;
}

const ROLES = "F1 plan, second F4 reviewer, curator, gardener, study coordinator";

/** The decision in one plain line, for the log and `doctor`. */
export function describeClaudeRoles(roles: ClaudeRoles): string {
  const said = roles.explicit || roles.recorded ? `, ${roles.reason}` : "";
  if (roles.runner === "claude") return `the claude roles (${ROLES}) run on claude (${MODELS.claudeMain})${said}`;
  if (said) return `the claude roles (${ROLES}) run on codex (${codexRoleModel()})${said}`;
  return `claude is not available on this machine (${roles.reason}): its roles (${ROLES}) run on codex (${codexRoleModel()})`;
}

let decided: ClaudeRoles | null = null;

/**
 * This process's decision: made at the first ask, logged then, the same for every later call.
 * `recorded` is the runner the run's state holds (a verify run passes it before its first model
 * call; the caller then records the returned runner). An explicit setting that differs from the
 * record wins, with one warning that the run changes runner. A codex that no setting chose is
 * logged on stderr, where a detached run's log shows it apart.
 */
export function claudeRoles(recorded?: ClaudeRolesRunner): ClaudeRoles {
  if (!decided) {
    decided = decideClaudeRoles(probe, {}, recorded);
    const line = `[leansmith] ${describeClaudeRoles(decided)}`;
    if (decided.runner === "codex" && !decided.explicit) console.warn(line);
    else console.log(line);
    if (recorded && recorded !== decided.runner) {
      console.warn(`[leansmith] WARN this run's claude roles ran on ${recorded} so far: from now on they run on ${decided.runner} (${decided.reason}).`);
    }
  }
  return decided;
}

/** Test hook: fix this process's decision (null: decide afresh at the next ask). */
export function setClaudeRolesForTest(roles: ClaudeRoles | null): void {
  decided = roles;
}

/** The model a claude role's call really runs on, for records: `claudeModel` under claude. */
export function claudeRoleModel(claudeModel: string): string {
  return claudeRoles().runner === "codex" ? codexRoleModel() : claudeModel;
}
