// Study-mode paths inside a PaperFormalizer toolkit. `root` is always the toolkit root.
import path from "node:path";
import { TOOLKIT_RUNS_DIRNAME, TOOLKIT_STAGING_SEGMENT } from "../toolkit/config.js";
import { pascalIdentifier } from "../paths.js";

const SUBSTRATE_SLUG_RE = /^[A-Za-z0-9][A-Za-z0-9_-]*$/;
export const STUDY_RUN_PREFIX = "study_";

function assertValidSlug(slug: string): void {
  // why: slugs are used in filesystem paths and Lean module names.
  if (!SUBSTRATE_SLUG_RE.test(slug)) throw new Error(`invalid substrate slug: ${slug}`);
}

/** The study's staging directory name: the paper rule (`pascalIdentifier`), so a digit-leading
 *  slug still yields a Lean identifier (`2sls_bounds` → `Study2slsBounds`). */
export function slugToPascal(slug: string): string {
  assertValidSlug(slug);
  return pascalIdentifier(slug, "Study");
}

/** Run id of a study: `study_<slug>` (its run-record directory name under `runs/`). */
export function studyRunId(slug: string): string {
  assertValidSlug(slug);
  return `${STUDY_RUN_PREFIX}${slug}`;
}

// Each study keeps its run record (requirement, plan, state, rounds, agent I/O) in its own
// directory `<toolkit>/runs/study_<slug>/`.
export function substrateRunDir(root: string, slug: string): string {
  return path.join(root, TOOLKIT_RUNS_DIRNAME, studyRunId(slug));
}
export function requirementPath(root: string, slug: string): string {
  return path.join(substrateRunDir(root, slug), "requirement.md");
}
/** Where a study keeps its state, plan, rounds and agent I/O: the run directory, or its
 *  `dry_run/` subdirectory for a dry run (a dry run never reads or writes the live record). */
export function substrateRecordDir(root: string, slug: string, dryRun = false): string {
  const runDir = substrateRunDir(root, slug);
  return dryRun ? path.join(runDir, "dry_run") : runDir;
}
export function substrateStatePath(root: string, slug: string, dryRun = false): string {
  return path.join(substrateRecordDir(root, slug, dryRun), "state.json");
}
/** Staging Lean sources: `<toolkit>/<lib>/Staging/<Pascal>/`. Never imported by the barrel. */
export function substrateLeanDir(root: string, slug: string, lib = "Toolkit"): string {
  return path.join(root, lib, TOOLKIT_STAGING_SEGMENT, slugToPascal(slug));
}
/** Staging module prefix: `<lib>.Staging.<Pascal>`. */
export function substrateModulePrefix(slug: string, lib = "Toolkit"): string {
  return `${lib}.${TOOLKIT_STAGING_SEGMENT}.${slugToPascal(slug)}`;
}
