// The cold-start guard of the toolkit's `.lake` before a `verify` or `study` run.
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import process from "node:process";

/** Env var of the guard: `0` disables it (any other number: on, the default). */
export const LEANLSP_WARMUP_ENV = "PAPERFORMALIZER_LEANLSP_WARMUP_MS";

/**
 * What the toolkit's `.lake` lacks for a run to start without a from-scratch compile: its own
 * build output, a dependency checkout the manifest names (a dangling link on a node whose local
 * package cache was never synced), or Mathlib's build output (hours to rebuild). Empty when warm.
 * Reads only.
 */
export function coldLakeParts(projectPath: string): string[] {
  const missing: string[] = [];
  const built = (dir: string) => existsSync(path.join(dir, ".lake", "build", "lib", "lean"));
  if (!built(projectPath)) missing.push(`the toolkit's own build (${path.join(projectPath, ".lake", "build")})`);
  let manifest: { packagesDir?: string; packages?: { type?: string; name?: string; dir?: string }[] };
  try {
    manifest = JSON.parse(readFileSync(path.join(projectPath, "lake-manifest.json"), "utf8"));
  } catch {
    return missing; // no manifest: no dependency to check
  }
  const pkgs = path.resolve(projectPath, manifest.packagesDir ?? path.join(".lake", "packages"));
  for (const p of manifest.packages ?? []) {
    if (!p.name) continue;
    const dir = p.type === "path" && p.dir ? path.resolve(projectPath, p.dir) : path.join(pkgs, p.name);
    if (!existsSync(dir)) missing.push(`dependency ${p.name} (${dir})`);
    else if (p.name.toLowerCase() === "mathlib" && !built(dir)) missing.push(`Mathlib's build (${path.join(dir, ".lake", "build")})`);
  }
  return missing;
}

/**
 * Fail fast on a COLD toolkit `.lake`, so a lean-lsp stage does not silently park on a
 * from-scratch `lake serve` compile: a run started on it throws with a "warm the .lake first"
 * message. That was the guard's only job — no stage relies on it for a build (each builds what it
 * needs, under the Lake lock). It used to run `lake build` of the default target for up to 10 min
 * here, unlocked (racing every other run's build) and, once locked, queuing every runner start
 * behind the lock before even V1; now it only looks at what is on disk, writes nothing and takes no lock.
 */
export async function warmUpLeanOrThrow(projectPath: string, mode: "verify" | "study"): Promise<void> {
  const raw = process.env[LEANLSP_WARMUP_ENV] ?? String(10 * 60_000);
  const on = Number(raw);
  if (!Number.isFinite(on)) {
    // why: a typo here used to disable the guard by producing NaN.
    throw new Error(`Invalid ${LEANLSP_WARMUP_ENV}: ${raw} (expected a number; 0 disables the guard)`);
  }
  if (!(on > 0)) return; // opted out: cold compile intended, operator will wait
  const missing = coldLakeParts(projectPath);
  if (missing.length > 0) {
    throw new Error(
      `lean-lsp cold-start guard: the toolkit's .lake in ${projectPath} is COLD — missing ${missing.join("; ")}. ` +
        `Warm it first (sync the node's package cache if it uses one, then \`lake build\` to completion), ` +
        `then rerun \`paperformalizer ${mode}\`. Set ${LEANLSP_WARMUP_ENV}=0 to disable this guard.`,
    );
  }
}
