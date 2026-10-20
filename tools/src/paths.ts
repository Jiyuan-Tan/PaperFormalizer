import path from "node:path";
import { existsSync, mkdirSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { TOOLKIT_RUNS_DIRNAME, toolkitConfigFileIn } from "./toolkit/config.js";

/**
 * Path helpers for LeanSmith runs.
 *
 * Two roots:
 *   TOOL_ROOT     this repository's `tools/` directory. Prompts and templates resolve here,
 *                 relative to the source (`import.meta.url`), never to the cwd.
 *   TOOLKIT_ROOT  the user's toolkit (`ToolkitConfig.toolkitRoot`): the Lean project, the run
 *                 records, and the per-paper Lean output. Every `repoRoot` parameter below is
 *                 the toolkit root (the parameter keeps its old name because the F-stage code
 *                 passes `ctx.repoRoot`).
 *
 * Layout under the toolkit root:
 *   runs/<slug>/                       run record (state.json, pipeline.jsonl, source/,
 *                                      discovery/, formalization/, reviews/, logs/, report.md)
 *   <papers_lib>/<Pascal>/             Lean output of the run (module `<papers_lib>.<Pascal>.*`)
 *   <papers_lib>/<Pascal>.lean         the run's barrel
 *
 * The run id IS the slug (`leansmith verify … --slug <slug>`, default from the file name).
 */

/** This repository's `tools/` directory. */
export const TOOL_ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");

/** Library name of the per-paper output when a caller has no toolkit config at hand. Every
 *  runner passes `ToolkitConfig.papersLib` instead. */
export const DEFAULT_PAPERS_LIB = "Papers";

function assertSlug(label: "qid", value: string): string {
  // why: run ids become path SEGMENTS, so this guard exists to block path TRAVERSAL — not to
  // normalize the id. Reject `/ \ . .. `/absolute/empty; otherwise pass the value through
  // UNCHANGED, so the directory name and the persisted `state.qid` stay in sync.
  if (
    value === "" ||
    value === "." ||
    value === ".." ||
    value.includes("..") ||
    path.isAbsolute(value) ||
    value.includes("/") ||
    value.includes("\\")
  ) {
    throw new Error(`Invalid ${label} slug: ${value}`);
  }
  return value;
}

/**
 * Public form of the run-id path-segment guard. Callers that MINT a run id (the verify slug
 * derivation) validate it here so a bad id fails at argument-parse time with the same rule the
 * path builders enforce.
 */
export function assertQidSlug(qid: string): string {
  return assertSlug("qid", qid);
}

/**
 * PascalCase Lean segment for a run slug: split on every non-alphanumeric run, capitalize each
 * part, join. A slug whose result is empty or starts with a digit (not a legal Lean identifier
 * start) gets a `Paper` prefix.
 *
 *   lee_bounds_2009 → LeeBounds2009
 *   2026_note       → Paper2026Note
 */
export function slugToPascal(slug: string): string {
  return pascalIdentifier(slug, "Paper");
}

/** PascalCase Lean identifier of a slug: split on non-alphanumerics, capitalize each part, join;
 *  a digit-leading or empty result gets `prefix` (papers use `Paper`). */
export function pascalIdentifier(slug: string, prefix: string): string {
  const tail = slug
    .split(/[^A-Za-z0-9]+/)
    .filter(Boolean)
    .map((part) => part.charAt(0).toUpperCase() + part.slice(1))
    .join("");
  return tail === "" || /^[0-9]/.test(tail) ? `${prefix}${tail}` : tail;
}

/** Paper Lean directory of a run, relative to the toolkit root (posix): `<papersLib>/<Pascal>`. */
export function canonicalLeanSubdir(qid: string, papersLib: string = DEFAULT_PAPERS_LIB): string {
  return path.posix.join(papersLib, slugToPascal(assertSlug("qid", qid)));
}

/**
 * Whether `leanSubdir` is a legal paper directory for `qid`: exactly two segments, a Lean
 * identifier (the papers library) followed by `slugToPascal(qid)`. The library name comes
 * from the toolkit config, which the state layer does not load, so it is checked for shape only.
 */
export function isPaperLeanSubdir(qid: string, leanSubdir: string): boolean {
  const parts = leanSubdir.split(/[\\/]+/).filter(Boolean);
  return parts.length === 2 && /^[A-Za-z_][A-Za-z0-9_']*$/.test(parts[0]) && parts[1] === slugToPascal(qid);
}

/** Lean module prefix of a paper directory: `Papers/Foo` → `Papers.Foo`. */
export function leanModulePrefix(leanSubdir: string): string {
  return leanSubdir.split(/[\\/]+/).filter(Boolean).join(".");
}

/** Absolute path of a run's barrel: `<toolkit>/<papersLib>/<Pascal>.lean`. */
export function paperBarrelPath(repoRoot: string, leanSubdir: string): string {
  return `${leanTheoremDir(repoRoot, leanSubdir)}.lean`;
}

/** Root of every run record: `<toolkit>/runs/`. */
export function runsRoot(repoRoot: string): string {
  return path.join(repoRoot, TOOLKIT_RUNS_DIRNAME);
}

/** Run directory: `<toolkit>/runs/<slug>/`. */
export function formalizationDir(repoRoot: string, qid: string): string {
  return path.join(runsRoot(repoRoot), assertSlug("qid", qid));
}

/** Named alias of {@link formalizationDir} for the verify code. */
export function verifyRunDir(repoRoot: string, qid: string): string {
  return formalizationDir(repoRoot, qid);
}

/**
 * Per-run LOG directory: `<run>/logs/`. Holds every transient run-log artifact (agent
 * transcripts under `logs/stages/`, the central agent-call log, run-liveness files) so the run
 * root keeps only the durable artifacts. Use `ensureLogsDir` to also create it.
 */
export function logsDir(repoRoot: string, qid: string): string {
  return path.join(formalizationDir(repoRoot, qid), "logs");
}

/** `logsDir(...)`, created (recursively) if absent. */
export function ensureLogsDir(repoRoot: string, qid: string): string {
  const dir = logsDir(repoRoot, qid);
  mkdirSync(dir, { recursive: true });
  return dir;
}

/** Live child processes of the run's runner (`shared/child_registry.ts`; read by `verify --stop`). */
export function childrenPath(repoRoot: string, qid: string): string {
  return path.join(logsDir(repoRoot, qid), "children.json");
}

/** Which subfolder of the run directory an artifact belongs to (`root` = the run dir itself). */
export type ArtifactPhase = "discovery" | "formalization" | "root";

/**
 * Resolve an artifact path under the run directory. `discovery/` holds the V-stage outputs
 * (source flattening, the typed core, the referee review), `formalization/` the F-stage outputs.
 * Resolution prefers the nested bare name, then the flat bare name; the first existing candidate wins, else the nested bare path is returned
 * (a new write). Writers must mkdir the dirname.
 */
export function artifactPath(
  repoRoot: string,
  qid: string,
  phase: ArtifactPhase,
  filename: string,
): string {
  const dir = formalizationDir(repoRoot, qid);
  const candidates: string[] = [];
  if (phase === "root") {
    candidates.push(path.join(dir, filename));
  } else {
    candidates.push(path.join(dir, phase, filename));
    candidates.push(path.join(dir, filename));
  }
  for (const c of candidates) if (existsSync(c)) return c;
  return candidates[0];
}

export function statePath(repoRoot: string, qid: string): string {
  return artifactPath(repoRoot, qid, "root", "state.json");
}

export function pipelineLogPath(repoRoot: string, qid: string): string {
  return artifactPath(repoRoot, qid, "root", "pipeline.jsonl");
}

/** The `reviews/` subfolder holding a run's review artifacts (`reviews.jsonl`, verdict files). */
export function reviewsDir(repoRoot: string, qid: string): string {
  return path.join(formalizationDir(repoRoot, qid), "reviews");
}

export function reviewsLogPath(repoRoot: string, qid: string): string {
  return path.join(reviewsDir(repoRoot, qid), "reviews.jsonl");
}

/**
 * Per-run substrate-debt ledger (`<toolkit>/runs/<slug>/SUBSTRATE_DEBT.md`): `bin/gate.ts` appends
 * one row per REGISTERED assumed-but-should-be-proven named hypothesis (and removes it on
 * discharge). The gates the F4 reviewers flag are recorded separately in
 * `formalization/gates.json` (`formalization/run_gates.ts`). Both live in the run record; the
 * toolkit ledger, `doc/ledger.json`, records only admitted toolkit declarations.
 */
export function substrateDebtPath(repoRoot: string, qid: string): string {
  return path.join(formalizationDir(repoRoot, qid), "SUBSTRATE_DEBT.md");
}

/** Per-run missing-architecture ledger. */
export function missingArchitecturePath(repoRoot: string, qid: string): string {
  return path.join(formalizationDir(repoRoot, qid), "MISSING_ARCHITECTURE.md");
}

export function mdPath(repoRoot: string, qid: string): string {
  return artifactPath(repoRoot, qid, "formalization", "formalization.md");
}

/** F1 formalization plan: the machine-checkable map from every typed-core node to the Lean
 *  object that realizes it. F1 authors it, F2 syncs deviations back. */
export function planPath(repoRoot: string, qid: string): string {
  return artifactPath(repoRoot, qid, "formalization", "plan.json");
}

/** The typed core the plan on disk was written from (F1 records it with every schema-valid plan),
 *  so a re-plan is told what moved since (`formalization/core_delta.ts`). */
export function planCorePath(repoRoot: string, qid: string): string {
  return artifactPath(repoRoot, qid, "formalization", "plan_core.json");
}

/** The plan and core F1.5 last passed: the review of a re-plan covers what moved since. */
export function planReviewedPath(repoRoot: string, qid: string): string {
  return artifactPath(repoRoot, qid, "formalization", "plan_reviewed.json");
}

/** The plan and core the scaffold on disk realizes (F2 records them when it completes): a
 *  re-scaffold after a re-plan covers what moved since. */
export function scaffoldBasisPath(repoRoot: string, qid: string): string {
  return artifactPath(repoRoot, qid, "formalization", "scaffold_basis.json");
}

/** F5 COMPLETE crosswalk: the lemma-inclusive, line-final tex↔Lean correspondence. */
export function crosswalkFullJsonPath(repoRoot: string, qid: string): string {
  return artifactPath(repoRoot, qid, "formalization", "crosswalk_full.json");
}

/** Human-readable rendering of the F5 complete crosswalk (sibling of the JSON). */
export function crosswalkFullMdPath(repoRoot: string, qid: string): string {
  return artifactPath(repoRoot, qid, "formalization", "crosswalk_full.md");
}

/** Absolute paper Lean directory: `<toolkit>/<leanSubdir>`. */
export function leanTheoremDir(repoRoot: string, leanSubdir: string): string {
  return path.join(repoRoot, ...leanSubdir.split("/"));
}

/**
 * Per-paper scratch directory for disposable agent probes (for example `Main.lean` and one-off
 * `#check` files). It lives beside the paper's source so concurrent papers never share scratch
 * names. Not part of the formalization: callers which inventory, review, or build a paper must
 * exclude it.
 */
export const PAPER_TMP_DIR = "tmp";

export function paperTmpDir(repoRoot: string, leanSubdir: string): string {
  return path.join(leanTheoremDir(repoRoot, leanSubdir), PAPER_TMP_DIR);
}

/** Create and return a paper's disposable agent workspace. */
export function ensurePaperTmpDir(repoRoot: string, leanSubdir: string): string {
  const dir = paperTmpDir(repoRoot, leanSubdir);
  mkdirSync(dir, { recursive: true });
  return dir;
}

/** Whether a recursive path below a paper belongs to its disposable workspace. */
export function isPaperTmpPath(relativePath: string): boolean {
  return relativePath.split(/[\\/]+/).includes(PAPER_TMP_DIR);
}

/**
 * Per-stage subfolder of an F-stage prompt under `src/formalization/prompts/`. Prefix-based, so
 * it resolves identically for reading a real prompt and for writing a test stub. Order matters
 * (`stage1_5` before `stage1`). Returns "" for anything unmapped.
 */
export function promptSubfolder(name: string): string {
  if (name.startsWith("stage1_5")) return "F1.5";
  if (name.startsWith("stage1")) return "F1";
  if (name.startsWith("stage2")) return "F2";
  if (name.startsWith("stage5")) return "F5";
  if (name.startsWith("proof_")) return "F4";
  return "";
}

/** An F-stage prompt in this repository: `<TOOL_ROOT>/src/formalization/prompts/<Fx>/<name>`. */
export function toolPromptPath(name: string): string {
  return path.join(TOOL_ROOT, "src", "formalization", "prompts", promptSubfolder(name), name);
}

/**
 * An F-stage prompt. `root` is the run's toolkit root: when it holds `leansmith.json` the
 * prompt resolves under TOOL_ROOT ({@link toolPromptPath}). Any
 * other `root` is a test fixture tree and resolves to `<root>/tools/src/formalization/prompts/…`,
 * so a fixture that writes a stub prompt there can never overwrite a real prompt of this repository.
 */
export function promptPath(root: string, name: string): string {
  if (toolkitConfigFileIn(root) !== null) return toolPromptPath(name);
  return path.join(root, "tools", "src", "formalization", "prompts", promptSubfolder(name), name);
}
