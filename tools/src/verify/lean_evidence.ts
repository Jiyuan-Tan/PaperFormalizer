/**
 * V6 — the Lean half of the correctness report.
 *
 * Three mechanical checks, in this order, over the run's Lean output:
 *
 *   1. a FULL `lake build` of the run BARREL module (`writeRunBarrel`). A targeted build of a
 *      single module can "Replay" a stale olean and report green over a live error, so the per-run
 *      barrel (`<papers_lib>/<Pascal>.lean`) is the only trustworthy target.
 *   2. `bankSoundnessIssues` — the comment-aware source scan for `sorry` / `admit` / `axiom` /
 *      `opaque` / `unsafe` over the run's files AND their reachable toolkit closure.
 *   3. `#print axioms` for every delivered declaration, run ONCE through `lake env lean` on a
 *      single generated probe file under the run's paper tmp dir.
 *
 * Never lean-lsp: the LSP answers from whatever olean it last loaded, which lies in both
 * directions. `exec` is injectable so the report
 * tests never spawn lake.
 */
import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";
import { leanProjectPathFor } from "../local_config.js";
import { paperTmpDir } from "../paths.js";

/** Axioms Lean's own kernel needs; anything else is a real extra assumption. */
export const CLEAN_AXIOMS: ReadonlySet<string> = new Set([
  "propext",
  "Classical.choice",
  "Quot.sound",
]);

/** `#print axioms <decl>` for one declaration. `error` is set when the probe produced no line
 * for this declaration at all (a rename, a failed elaboration, a build that never got there). */
export interface DeclAxioms {
  axioms: string[];
  clean: boolean;
  error?: string;
}

export interface LeanEvidence {
  build: { ok: boolean; log_tail: string };
  /** `bankSoundnessIssues` strings, e.g. `sorry in Papers/Foo/Basic.lean`. */
  sorry_scan: string[];
  /** Keyed by the fully-qualified declaration name as given in `declNames`. */
  axioms: Record<string, DeclAxioms>;
}

/** Injectable process runner: `(cmd, args, opts) => {code, stdout, stderr}`. */
export type LeanExec = (
  cmd: string,
  args: string[],
  opts: { cwd: string },
) => Promise<{ code: number; stdout: string; stderr: string }>;

export interface CollectLeanEvidenceArgs {
  repoRoot: string;
  /** Absolute path of the run's Lean directory (`leanTheoremDir(repoRoot, state.lean_subdir)`). */
  leanDir: string;
  /** Fully-qualified decl names to audit, typically the crosswalk's `lean.decl` values. */
  declNames: readonly string[];
  exec?: LeanExec;
}

export type CollectLeanEvidence = (args: CollectLeanEvidenceArgs) => Promise<LeanEvidence>;

/** Lines of build output kept in the report. */
const LOG_TAIL_LINES = 40;

/** Name of the generated probe. One file, one `lake env lean`, all declarations. */
const AXIOM_PROBE_FILE = "V6Axioms.lean";

function tailOf(text: string): string {
  const lines = text.split(/\r?\n/).filter((l) => l.trim().length > 0);
  return lines.slice(-LOG_TAIL_LINES).join("\n");
}

/** Dotted lake module name of a `.lean` file, as `leanModuleTargets` derives it. */
function moduleNameFor(repoRoot: string, leanFile: string): string {
  return path
    .relative(repoRoot, leanFile)
    .replace(/\.lean$/u, "")
    .split(path.sep)
    .join(".");
}

async function defaultExec(
  cmd: string,
  args: string[],
  opts: { cwd: string },
): Promise<{ code: number; stdout: string; stderr: string }> {
  const { spawnWithInactivityTimeout } = await import("../workers/spawn.js");
  const r = await spawnWithInactivityTimeout(cmd, args, {
    cwd: opts.cwd,
    env: process.env,
    inactivityTimeoutMs: 30 * 60_000,
    maxTotalMs: 60 * 60_000,
  });
  return { code: r.exitCode ?? 1, stdout: r.stdout, stderr: r.stderr };
}

/**
 * Parse one `lake env lean` run of a `#print axioms` probe into a per-declaration verdict.
 *
 * Lean prints either `'X' depends on axioms: [a, b]` or `'X' does not depend on any axioms`, and
 * wraps long lists across lines — so the whole output is whitespace-flattened and each KNOWN
 * declaration name is looked up by its own anchored pattern. Keying on the known names (rather
 * than scraping every quoted token) is what makes primed names (`foo'`) and namespace suffixes
 * (`X.Foo.bar` vs `Foo.bar`) unambiguous. A declaration with no line gets `error` — never a
 * silent clean verdict.
 */
export function parseAxiomReport(
  output: string,
  declNames: readonly string[],
  execError?: string | null,
): Record<string, DeclAxioms> {
  const flat = output.replace(/\s+/gu, " ");
  const out: Record<string, DeclAxioms> = {};
  for (const name of declNames) {
    const esc = name.replace(/[.*+?^${}()|[\]\\]/gu, "\\$&");
    if (new RegExp(`'${esc}' does not depend on any axioms`, "u").test(flat)) {
      out[name] = { axioms: [], clean: true };
      continue;
    }
    const m = new RegExp(`'${esc}' depends on axioms: \\[([^\\]]*)\\]`, "u").exec(flat);
    if (m) {
      const axioms = m[1]
        .split(",")
        .map((a) => a.trim())
        .filter((a) => a.length > 0);
      out[name] = { axioms, clean: axioms.every((a) => CLEAN_AXIOMS.has(a)) };
      continue;
    }
    out[name] = {
      axioms: [],
      clean: false,
      error:
        `no \`#print axioms\` line for ${name} in the lean output` +
        (execError ? ` (${execError})` : ""),
    };
  }
  return out;
}

/**
 * Build, scan, and axiom-audit the run's Lean. Returns evidence; never throws on a red tree —
 * a failed build is a reportable fact, not a crash — but never reports a clean verdict it did
 * not observe either.
 */
export const collectLeanEvidence: CollectLeanEvidence = async (args) => {
  const { repoRoot, leanDir } = args;
  const exec = args.exec ?? defaultExec;
  // The Lake project root: the toolkit.
  const cwd = leanProjectPathFor(repoRoot);
  // Loaded lazily: the F-stage loop, the lockfile, and the scanner are heavy, and the pure
  // parser above must stay importable on its own.
  const [{ writeRunBarrel }, { bankSoundnessIssues }, { withLakeBuildLock }] = await Promise.all([
    import("../formalization/proof_review_loop.js"),
    import("../formalization/bank_soundness.js"),
    import("../shared/build_mutex.js"),
  ]);

  const barrelPath = await writeRunBarrel(repoRoot, leanDir);
  const barrelModule = barrelPath ? moduleNameFor(repoRoot, barrelPath) : null;

  let build: LeanEvidence["build"];
  if (!barrelModule) {
    build = {
      ok: false,
      log_tail: `no Lean modules found under ${leanDir} — nothing could be built or verified`,
    };
  } else {
    const r = await withLakeBuildLock(repoRoot, () =>
      exec("lake", ["build", barrelModule], { cwd }),
    );
    build = { ok: r.code === 0, log_tail: tailOf(`${r.stdout}\n${r.stderr}`) };
  }

  const sorry_scan = await bankSoundnessIssues(leanDir, repoRoot);

  const declNames = [...new Set(args.declNames)].sort();
  let axioms: Record<string, DeclAxioms> = {};
  if (declNames.length > 0) {
    if (!barrelModule) {
      axioms = Object.fromEntries(
        declNames.map((d) => [
          d,
          { axioms: [], clean: false, error: "the run has no Lean modules to import" } as DeclAxioms,
        ]),
      );
    } else {
      // The run's disposable workspace: `isPaperTmpPath` keeps it out of `leanModuleTargets`,
      // the barrel, and the soundness scan, so the probe can never be mistaken for run output.
      const leanSubdir = path.relative(repoRoot, leanDir).split(path.sep).join("/");
      const probeDir = paperTmpDir(repoRoot, leanSubdir);
      await mkdir(probeDir, { recursive: true });
      const probe = path.join(probeDir, AXIOM_PROBE_FILE);
      await writeFile(
        probe,
        `import ${barrelModule}\n\n` + declNames.map((d) => `#print axioms ${d}`).join("\n") + "\n",
        "utf8",
      );
      const r = await withLakeBuildLock(repoRoot, () =>
        exec("lake", ["env", "lean", probe.split(path.sep).join("/")], { cwd }),
      );
      axioms = parseAxiomReport(
        `${r.stdout}\n${r.stderr}`,
        declNames,
        r.code === 0 ? null : `lake env lean exited ${r.code}`,
      );
    }
  }

  return { build, sorry_scan, axioms };
};
