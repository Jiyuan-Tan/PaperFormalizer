// `theoremchecker study`: build a reusable, proved Lean module for the owner's toolkit from a
// plain-English requirement (`runs/study_<slug>/requirement.md`, which the first run writes as a
// template). The run record, the staging Lean (`<lib>/Staging/<Slug>/`) and the Lake project all
// live in the toolkit resolved by `toolkit/config.ts`. A promotion round's accepted entries are
// built the same way (`proposals/build.ts`).
import { STUDY_SYNOPSIS } from "./constants.js";
import { applyWorkerEnv, assertLeanProjectOverride } from "./local_config.js";
import { applyAuthEnv } from "./auth.js";
import { claudeRoles } from "./claude_roles.js";
import { loadToolkitConfig } from "./toolkit/config.js";
import { assertToolkitLakefile } from "./toolkit/lakefile.js";
import { warmUpLeanOrThrow } from "./shared/lean_warmup.js";
import { clearSharedLeanLspUrl, setSharedLeanLspUrl, sharedLeanLspUrl } from "./shared/shared_lean_lsp_env.js";

interface StudyArgs {
  slug: string;
  /** Value of `--toolkit <path>`, when given. */
  toolkit: string | null;
  resume: boolean;
  dryRun: boolean;
  clearBuildCap: boolean;
  clearCoordinateCap: boolean;
  clearReviewCap: boolean;
}

export const STUDY_USAGE = `Usage: ${STUDY_SYNOPSIS}`;

function parseStudyArgs(argv: string[]): StudyArgs {
  const args = [...argv];
  let toolkit: string | null = null;
  const toolkitIndex = args.indexOf("--toolkit");
  if (toolkitIndex !== -1) {
    const value = args[toolkitIndex + 1];
    if (value === undefined || value.startsWith("--")) throw new Error(`--toolkit needs a path\n${STUDY_USAGE}`);
    toolkit = value;
    args.splice(toolkitIndex, 2);
    if (args.includes("--toolkit")) throw new Error(`--toolkit given twice\n${STUDY_USAGE}`);
  }
  const resumeIndex = args.indexOf("--resume");
  const resume = resumeIndex !== -1;
  if (resume) args.splice(resumeIndex, 1);
  const dryRunIndex = args.indexOf("--dry-run");
  const dryRun = dryRunIndex !== -1;
  if (dryRun) args.splice(dryRunIndex, 1);
  const clearCoordinateCapIndex = args.indexOf("--clear-coordinate-cap");
  const clearCoordinateCap = clearCoordinateCapIndex !== -1;
  if (clearCoordinateCap) args.splice(clearCoordinateCapIndex, 1);
  const clearBuildCapIndex = args.indexOf("--clear-build-cap");
  const clearBuildCap = clearBuildCapIndex !== -1;
  if (clearBuildCap) args.splice(clearBuildCapIndex, 1);
  const clearReviewCapIndex = args.indexOf("--clear-review-cap");
  const clearReviewCap = clearReviewCapIndex !== -1;
  if (clearReviewCap) args.splice(clearReviewCapIndex, 1);
  const [slug, extra] = args;
  if (!slug || extra || slug.startsWith("-")) {
    throw new Error(STUDY_USAGE);
  }
  if (clearCoordinateCap && !resume) {
    throw new Error("--clear-coordinate-cap requires --resume");
  }
  if (clearBuildCap && !resume) {
    throw new Error("--clear-build-cap requires --resume");
  }
  if (clearReviewCap && !resume) {
    throw new Error("--clear-review-cap requires --resume");
  }
  return { slug, toolkit, resume, dryRun, clearBuildCap, clearCoordinateCap, clearReviewCap };
}

/** Run the toolkit-module builder behind `theoremchecker study`. */
export async function runStudyCli(argv: string[]): Promise<void> {
  applyWorkerEnv();
  applyAuthEnv();
  const parsed = parseStudyArgs(argv);
  const toolkit = loadToolkitConfig({ explicit: parsed.toolkit });
  const repoRoot = toolkit.toolkitRoot;
  // The toolkit IS the Lean project; a differing machine-level override is refused.
  assertLeanProjectOverride(toolkit);
  // Fail closed before any work: the study gate runs `lake exe toolkit_index`.
  assertToolkitLakefile(toolkit);
  console.log(`[study] toolkit: ${repoRoot} (from ${toolkit.source})`);
  // Which CLI runs the claude roles (the coordinator): decided and logged once, ahead of the first
  // model call. A study run keeps no record of it: each process decides from the setting or the machine.
  if (!parsed.dryRun) claudeRoles();
  const { runSubstratePipeline } = await import("./substrate/pipeline.js");
  const { studyExit } = await import("./substrate/state.js");
  const { startSharedLeanLsp } = await import("./shared/lean_lsp_server.js");
  const leanProject = toolkit.leanProjectPath;

  // Fail fast before a cold lean-lsp stage parks on a from-scratch build.
  if (!parsed.dryRun) await warmUpLeanOrThrow(leanProject, "study");

  // Pay the lean-lsp cold start once and share it across the entire study run.
  let shared: Awaited<ReturnType<typeof startSharedLeanLsp>> | null = null;
  const ownsSharedLeanLsp = !sharedLeanLspUrl();
  if (ownsSharedLeanLsp && !parsed.dryRun) {
    try {
      shared = await startSharedLeanLsp(repoRoot);
      setSharedLeanLspUrl(shared.url);
    } catch {
      shared = null;
    }
  }
  try {
    const finalState = await runSubstratePipeline({
      toolkit, slug: parsed.slug, resume: parsed.resume, dryRun: parsed.dryRun,
      clearBuildCap: parsed.clearBuildCap,
      clearCoordinateCap: parsed.clearCoordinateCap,
      clearReviewCap: parsed.clearReviewCap,
    });
    console.log(`TheoremChecker study ${parsed.slug} finished in phase ${finalState.phase}.`);
    if (finalState.phase !== "done") {
      if (finalState.terminalMessage) console.log(finalState.terminalMessage);
      console.log(studyExit(finalState, parsed.slug, repoRoot));
    }
  } finally {
    if (ownsSharedLeanLsp && shared) {
      try {
        await shared.stop();
      } catch {
        /* best-effort teardown */
      }
      clearSharedLeanLspUrl();
    }
  }
}

