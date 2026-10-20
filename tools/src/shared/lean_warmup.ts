// Bounded warm-up of the toolkit's `.lake` before a `verify` run.
import process from "node:process";

/** Env var holding the warm-up wall-clock cap in ms (default 10 min; 0 disables the guard). */
export const LEANLSP_WARMUP_ENV = "THEOREMCHECKER_LEANLSP_WARMUP_MS";

/**
 * Run `lake build` in the Lean project with a wall-clock cap, so a cold `.lake` is detected up
 * front instead of a lean-lsp stage silently parking on a from-scratch `lake serve` compile. A
 * cap breach throws with a "warm the .lake first" message. A non-timeout build failure is NOT
 * fatal (the tree may carry a pre-existing error unrelated to this run): warn and let the
 * pipeline's own targeted builds surface real errors.
 */
export async function warmUpLeanOrThrow(projectPath: string, mode: "verify" | "study"): Promise<void> {
  const rawCapMs = process.env[LEANLSP_WARMUP_ENV] ?? String(10 * 60_000);
  const capMs = Number(rawCapMs);
  if (!Number.isFinite(capMs)) {
    // why: a typo here used to disable the warm-up guard by producing NaN.
    throw new Error(`Invalid ${LEANLSP_WARMUP_ENV}: ${rawCapMs} (expected a number of milliseconds)`);
  }
  if (!(capMs > 0)) return; // opted out: cold compile intended, operator will wait
  const { spawnWithInactivityTimeout } = await import("../workers/spawn.js");
  // Inactivity is set beyond the cap: a cold build emits steady progress, so ONLY the
  // wall-clock cap should fire; the shared helper tree-kills the whole `lake → lean` group.
  const r = await spawnWithInactivityTimeout("lake", ["build"], {
    cwd: projectPath,
    env: process.env,
    inactivityTimeoutMs: capMs + 60_000,
    maxTotalMs: capMs,
  });
  if (r.killedDueToTotalTimeout) {
    throw new Error(
      `lean-lsp cold-start guard: \`lake build\` in ${projectPath} exceeded ` +
        `${Math.round(capMs / 60_000)} min — the toolkit's .lake is COLD (a from-scratch compile). ` +
        `Warm it first (\`lake build\` to completion), then rerun \`theoremchecker ${mode}\`. ` +
        `Set ${LEANLSP_WARMUP_ENV} to raise the cap, or 0 to disable this guard.`,
    );
  }
  if (r.exitCode !== 0) {
    console.warn(
      `[${mode}] warm-up \`lake build\` failed (exit ${r.exitCode}) — proceeding; the ` +
        `pipeline's targeted builds will surface real errors. ${r.stderr.trim().slice(-300)}`,
    );
  }
}
