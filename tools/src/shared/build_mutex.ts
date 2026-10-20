/**
 * Cross-process mutex around `lake build` for the toolkit's Lake project.
 *
 * Once per-qid parallel runs are allowed (see `shared/run_heartbeat.ts`), two
 * concurrent pipelines can independently call `lake build`. Both
 * invocations target the same `.lake/build` directory, which is not safe under
 * parallel lake invocations — `.olean` writes race and the cache can end up
 * inconsistent. Wrap `lake build` in an exclusive file lock so the LLM stages
 * remain parallel but compilation is serialized.
 *
 * Lock file: `<repoRoot>/.lake-build.lock` (gitignore this).
 *
 * Uses `proper-lockfile`. A 60-min stale window
 * accommodates Mathlib-scale rebuilds; in practice each acquisition completes
 * in seconds-to-minutes and the lock is released promptly.
 */
import lockfile from "proper-lockfile";
import { stat, writeFile } from "node:fs/promises";
import path from "node:path";

const STALE_MS = 60 * 60_000;
// A waiter outlasts the longest queue: a promotion's gate builds the toolkit and the paper under
// this lock (many minutes), several papers in their Lean stages at once each build behind it (a
// paper's build runs up to an hour, `buildRunModules`), and a build that gives up early fails its
// whole stage with "Lock file is already being held". About five hours of waiting in all — six
// papers' builds ahead of it.
export const LAKE_LOCK_RETRIES = { retries: 1_800, factor: 1.5, minTimeout: 200, maxTimeout: 10_000 };
const RETRIES = LAKE_LOCK_RETRIES;

async function ensureLockfileTarget(target: string): Promise<void> {
  try {
    await stat(target);
  } catch {
    await writeFile(target, "{}\n", "utf8");
  }
}

export async function withLakeBuildLock<T>(
  repoRoot: string,
  action: () => Promise<T>,
): Promise<T> {
  const lockPath = path.join(repoRoot, ".lake-build.lock");
  await ensureLockfileTarget(lockPath);
  const release = await lockfile.lock(lockPath, {
    stale: STALE_MS,
    retries: RETRIES,
    realpath: false,
  });
  try {
    return await action();
  } finally {
    await release();
  }
}

// Promotion holds the lock across a full build + lint + index chain, so a run waiting to promote
// behind another may wait many minutes — and the promotion itself waits for the lake lock inside
// this one (`gate.ts`), up to `LAKE_LOCK_RETRIES`' budget. A queued promotion waits at least that
// long (≈ 5h: 600 × 30s) before it errors out.
const PROMOTE_RETRIES = { retries: 600, factor: 1.3, minTimeout: 1_000, maxTimeout: 30_000 };

/**
 * Cross-process mutex serializing the WHOLE promotion step across concurrent `study` runs.
 * Unlike `withLakeBuildLock` (per-cwd, per-command), this wraps the entire promotion — barrel
 * edit + `lake build` + lints + index — so two runs can never interleave their toolkit edits or
 * race on the shared `.lake` build dir.
 *
 * Keyed on the toolkit root (the shared resource every promotion mutates); the study runner
 * passes `ToolkitConfig.lockPath` (`<toolkit>/.toolkit-promote.lock`, gitignore it).
 */
export async function withPromotionLock<T>(
  toolkitRoot: string,
  action: () => Promise<T>,
  lockPath: string = path.join(toolkitRoot, ".toolkit-promote.lock"),
): Promise<T> {
  await ensureLockfileTarget(lockPath);
  const release = await lockfile.lock(lockPath, {
    stale: STALE_MS,
    retries: PROMOTE_RETRIES,
    realpath: false,
  });
  try {
    return await action();
  } finally {
    await release();
  }
}
