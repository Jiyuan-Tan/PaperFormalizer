// tools/src/substrate/pipeline.ts
import { mkdir, writeFile, readdir, readFile } from "node:fs/promises";
import path from "node:path";
import { createHash } from "node:crypto";
import { ensureRequirement } from "./requirement.js";
import { substrateRecordDir, substrateRunDir, substrateLeanDir, substrateModulePrefix, substrateStatePath } from "./paths.js";
import { withPromotionLock } from "../shared/build_mutex.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import {
  clearStudyCap, createInitialSubstrateState, loadSubstrateState, saveSubstrateState, substrateStateExists,
} from "./state.js";
import { runScaffolder as realScaffolder } from "./scaffolder.js";
import { runFillers as realFillers } from "./filler.js";
import { runReviewer as realReviewer } from "./reviewer.js";
import { buildTargets as realBuild } from "./build.js";
import { coordinate as realCoordinate, coordinateJournalPath, describeCoordinatePlan } from "./coordinate.js";
import {
  buildCoordinatorPrompt, buildFillerPrompt, buildReviewerPrompt, buildScaffolderPrompt, toolkitPromptContext,
} from "./prompts.js";
import { studyProvenanceSchema, type RoundReport, type StudyProvenance, type SubstrateState } from "./types.js";

export const BUILD_CAP = 10;
export const REVIEW_CAP = 3;
export const COORD_CAP = 3;
// Study prompts commonly target modules in one import chain.  Until prompt
// dependencies are represented explicitly, concurrent fillers can compile or
// edit against an imported file that another filler is changing.  Serialize
// the batch; dependency-aware parallel batches can be added later.
export const FILLER_CONCURRENCY = 1;

export interface SubstratePipelineDeps {
  runScaffolder: typeof realScaffolder;
  runFillers: typeof realFillers;
  runReviewer: typeof realReviewer;
  buildTargets: typeof realBuild;
  coordinate: typeof realCoordinate;
  writePlan?: (runDir: string, md: string) => Promise<void>;
}

const realDeps: SubstratePipelineDeps = {
  runScaffolder: realScaffolder, runFillers: realFillers, runReviewer: realReviewer,
  buildTargets: realBuild, coordinate: realCoordinate,
  writePlan: async (runDir, md) => { await mkdir(runDir, { recursive: true }); await writeFile(path.join(runDir, "plan.md"), md, "utf8"); },
};

/**
 * Canned no-op deps for `--dry-run`: drive one clean build→review→coordinate→done
 * cycle with NO side effects outside the run record (no real workers, no lake, no toolkit
 * mutation). The requirement gate, state, and artifact writes still run — that is the
 * mechanics we want to exercise. `coordinate` only DESCRIBES the attempt (placement rules and
 * the gate chain it would run); the real `coordinate()` is never invoked under dry-run.
 */
export function dryRunDeps(): SubstratePipelineDeps {
  let scaffoldCalls = 0;
  // Each canned agent still RESOLVES its real prompt and writes it to the run record, so a dry
  // run shows exactly what the model would receive (and that no template token is left over).
  const record = async (runDir: string, name: string, prompt: string) => {
    const dir = path.join(runDir, "dry_run_prompts");
    await mkdir(dir, { recursive: true });
    await writeFile(path.join(dir, `${name}.txt`), prompt, "utf8");
    console.log(`[dry-run] ${name}: prompt resolved (${Buffer.byteLength(prompt)} bytes) → ${path.join(dir, `${name}.txt`)}`);
  };
  return {
    runScaffolder: async (args) => {
      scaffoldCalls += 1;
      await record(args.runDir, `scaffolder_round_${args.buildRounds + 1}`,
        buildScaffolderPrompt({ ...args, toolkit: toolkitPromptContext(args.toolkit) }));
      return scaffoldCalls === 1
        ? { decision: "build", plan_markdown: "[dry-run]", codex_prompts: [{ id: "d", target_decls: [], prompt: "dry" }] }
        : { decision: "review", plan_markdown: "[dry-run]", codex_prompts: [] };
    },
    runFillers: async (args) => {
      const ctx = toolkitPromptContext(args.toolkit);
      for (const p of args.prompts) {
        await record(args.runDir, `filler_round_${args.round}_${p.id}`,
          buildFillerPrompt({ toolkit: ctx, leanDir: args.leanDir, modulePrefix: args.modulePrefix, prompt: p }));
      }
      return [];
    },
    buildTargets: async (root, modules) => {
      console.log(`[dry-run] would run \`lake build ${modules.join(" ")}\` in ${root} (skipped)`);
      return { ok: true, errors: [], sorryCount: 0, perFile: {} };
    },
    runReviewer: async (args) => {
      await record(args.runDir, `reviewer_round_${args.round}`,
        buildReviewerPrompt({ ...args, toolkit: toolkitPromptContext(args.toolkit) }));
      return {
        pass: true, findings: "",
        checks: { generic: true, reusable: true, standard: true, not_vacuous: true, fulfills_goal: true, sorry_free: true, layered: true, documented: true },
      };
    },
    coordinate: async (args) => {
      await record(args.runDir, `coordinator_round_${args.round}`, buildCoordinatorPrompt({
        ...args, toolkit: toolkitPromptContext(args.toolkit), stagingDir: path.join(args.runDir, "coordinate_staging", `round_${args.round}`),
      }));
      return { ok: true, log: await describeCoordinatePlan(args) };
    },
  };
}

async function listLeanFiles(leanDir: string): Promise<string[]> {
  const entries = await readdir(leanDir, { withFileTypes: true }).catch(() => []);
  const files: string[] = [];
  for (const entry of entries) {
    const abs = path.join(leanDir, entry.name);
    if (entry.isDirectory()) files.push(...await listLeanFiles(abs));
    else if (entry.isFile() && entry.name.endsWith(".lean")) files.push(abs);
  }
  return files.sort();
}

function leanModuleTargets(leanDir: string, modulePrefix: string, files: string[]): string[] {
  // why: nested Lean files map to dotted module path segments, not basenames.
  return files.map((f) =>
    `${modulePrefix}.${path.relative(leanDir, f).replace(/\.lean$/, "").split(path.sep).join(".")}`);
}

export async function runSubstratePipeline(
  opts: {
    toolkit: ToolkitConfig;
    slug: string;
    resume: boolean;
    dryRun?: boolean;
    clearCoordinateCap?: boolean;
    clearBuildCap?: boolean;
    clearReviewCap?: boolean;
    /** Ledger provenance when this study builds an owner-accepted proposal; persisted in the run
     *  record so a later `--resume` keeps it. */
    provenance?: StudyProvenance;
  },
  deps?: SubstratePipelineDeps,
): Promise<SubstrateState> {
  const { toolkit, slug } = opts;
  const repoRoot = toolkit.toolkitRoot;
  // Honor an explicitly-passed deps bundle; otherwise pick canned dry-run deps
  // (no real agents / no real promotion) when dryRun, else the real deps.
  const d: SubstratePipelineDeps = deps ?? (opts.dryRun ? dryRunDeps() : realDeps);
  const dryRun = opts.dryRun === true;
  // The live run directory holds the requirement (the study's input). A dry run keeps its own
  // state, plan, rounds and prompt dumps under `dry_run/` and never reads or writes the live ones.
  const liveRunDir = substrateRunDir(repoRoot, slug);
  const runDir = substrateRecordDir(repoRoot, slug, dryRun);
  const leanDir = substrateLeanDir(repoRoot, slug, toolkit.lib);
  const modulePrefix = substrateModulePrefix(slug, toolkit.lib);
  const writePlan = d.writePlan ?? realDeps.writePlan!;

  // 1. Requirement gate.
  const req = await ensureRequirement(repoRoot, slug);
  if (req.status === "bootstrapped") {
    const msg = `Wrote a blank requirement.md to ${liveRunDir}/requirement.md — fill it in and re-run \`paperformalizer study ${slug}\`.`;
    console.log(msg);
    return { ...createInitialSubstrateState(slug), phase: "halted", terminalMessage: msg };
  }
  if (req.status === "invalid") {
    const msg = `requirement.md is missing/empty sections: ${req.check?.missingSections.join(", ")}. Fill them in and re-run.`;
    console.log(msg);
    return { ...createInitialSubstrateState(slug), phase: "halted", terminalMessage: msg };
  }
  const requirement = req.text!;
  const provenance = await resolveProvenance(runDir, opts.provenance);
  const requirementHash = createHash("sha256").update(requirement, "utf8").digest("hex");

  // 2. State.
  if (dryRun && opts.resume && !(await substrateStateExists(repoRoot, slug, true))
    && (await substrateStateExists(repoRoot, slug))) {
    throw new Error(
      `--resume --dry-run: ${substrateStatePath(repoRoot, slug)} is a live study; a dry run never ` +
        `reads or writes it. Start a dry run without --resume (it keeps its record under ${runDir}).`,
    );
  }
  if (!opts.resume && (await substrateStateExists(repoRoot, slug, dryRun))) {
    throw new Error(`substrate state already exists for ${slug} at ${substrateStatePath(repoRoot, slug, dryRun)}; use --resume`);
  }
  let state = opts.resume ? await loadSubstrateState(repoRoot, slug, dryRun) : createInitialSubstrateState(slug);
  // (a clearing flag for a cap the study is not at is refused before anything below is saved)
  clearStudyCap(structuredClone(state), opts);
  if (state.phase === "escalated") {
    // A scaffolder escalation re-opens when the requirement was corrected since.
    const changed = state.terminalRequirementHash != null && state.terminalRequirementHash !== requirementHash;
    if (state.terminalEscalationKind === "scaffolder" && changed) {
      // Preserve useful staged Lean and the on-disk audit history, but reset budgets whose
      // meaning is scoped to the requirement bytes. Carrying a nearly exhausted build/review
      // budget into a materially corrected contract makes this recovery lane unusable.
      state.phase = "build";
      state.buildRounds = 0;
      state.reviewRounds = 0;
      state.pendingPrompts = [];
      state.lastReport = null;
      state.lastReview = null;
      state.terminalMessage = null;
      state.terminalRequirementHash = null;
      state.terminalEscalationKind = null;
      state.requirementVersion += 1;
      await saveSubstrateState(repoRoot, slug, state, dryRun);
    }
  }
  // One more window on a study halted at a cap. A cap exists to stop a loop, not to declare a
  // substrate unbuildable: a study can be one `sorry` from done when it runs out. Staged Lean and
  // audit history are preserved; only the round budget resets. Granting this twice is the signal
  // to stop instead.
  if (clearStudyCap(state, opts)) await saveSubstrateState(repoRoot, slug, state, dryRun);
  let planMarkdown: string | null = null;

  // On resume, reload the plan ledger so the scaffolder regains its status
  // context. Best-effort — ignore read errors.
  if (opts.resume) {
    planMarkdown = await readFile(path.join(runDir, "plan.md"), "utf8").catch(() => null);
  }

  // 3. Loop.
  for (;;) {
    if (state.phase === "build") {
      // Scaffold step: the scaffolder plans + emits filler prompts (or decides
      // review/escalate). On a `build` decision we PERSIST the prompts and
      // advance to the resumable `fill` phase — a crash/stop/parse-failure after
      // this checkpoint resumes into filling WITHOUT re-running the (expensive)
      // scaffolder.
      const out = await d.runScaffolder({
        repoRoot, toolkit, runDir, slug, requirement, leanDir, modulePrefix,
        planMarkdown, lastReport: state.lastReport, lastReview: state.lastReview,
        buildRounds: state.buildRounds, buildCap: BUILD_CAP,
      });
      planMarkdown = out.plan_markdown;
      await writePlan(runDir, out.plan_markdown);
      state.lastReview = null; // consumed

      if (out.decision === "escalate") {
        state.phase = "escalated";
        state.terminalMessage = `Scaffolder escalated: ${out.escalation?.reason ?? "(no reason)"}`;
        state.terminalRequirementHash = requirementHash;
        state.terminalEscalationKind = "scaffolder";
      } else if (out.decision === "review") {
        state.phase = "review";
      } else {
        state.pendingPrompts = out.codex_prompts;
        state.phase = "fill";
      }
      await saveSubstrateState(repoRoot, slug, state, dryRun);
    } else if (state.phase === "fill") {
      // Proof-fill step (resumable): run the codex fillers on the persisted
      // prompts, rebuild, then hand control back to the scaffolder (phase
      // `build`) so it assesses the build and decides review vs. another round.
      const reports = await d.runFillers({ repoRoot, toolkit, runDir, round: state.buildRounds + 1, leanDir, modulePrefix, prompts: state.pendingPrompts, concurrency: FILLER_CONCURRENCY });
      const files = await listLeanFiles(leanDir);
      const targets = files.length > 0
        ? leanModuleTargets(leanDir, modulePrefix, files)
        : [modulePrefix];
      const build = await d.buildTargets(repoRoot, targets);
      const report: RoundReport = { round: state.buildRounds + 1, fillers: reports, build };
      state.lastReport = report;
      state.buildRounds += 1;
      state.moduleFiles = files;
      state.pendingPrompts = []; // consumed
      await saveRound(runDir, report, state.requirementVersion);
      if (build.ok && build.sorryCount === 0) {
        // Deterministic proof closure is sufficient to enter the semantic
        // reviewer. In particular, do not strand a clean result when the last
        // filler happens to consume BUILD_CAP.
        state.phase = "review";
        state.terminalMessage = null;
      } else if (state.buildRounds >= BUILD_CAP) {
        state.phase = "halted";
        state.terminalMessage = `Reached BUILD_CAP (${BUILD_CAP}) without the scaffolder requesting review.`;
      } else {
        state.phase = "build";
      }
      await saveSubstrateState(repoRoot, slug, state, dryRun);
    } else if (state.phase === "review") {
      const verdict = await d.runReviewer({ repoRoot, toolkit, runDir, round: state.reviewRounds + 1, slug, requirement, leanDir, modulePrefix });
      state.lastReview = verdict;
      let reviewPassed = verdict.pass;
      if (verdict.pass) {
        const files = await listLeanFiles(leanDir);
        const targets = files.length > 0
          ? leanModuleTargets(leanDir, modulePrefix, files)
          : [modulePrefix];
        const build = await d.buildTargets(repoRoot, targets);
        // A model PASS is not enough; deterministic Lean diagnostics must also be sorry-free.
        if (!build.ok || build.sorryCount !== 0) {
          state.moduleFiles = files;
          state.lastReport = { round: state.buildRounds, fillers: [], build };
          state.lastReview = {
            ...verdict,
            pass: false,
            findings: [`deterministic build gate rejected reviewer PASS: ok=${build.ok}, sorryCount=${build.sorryCount}`, verdict.findings].filter(Boolean).join("\n"),
            checks: { ...verdict.checks, sorry_free: false }, // why: saved verdict must reflect deterministic build failure, not only sorry count.
          };
          reviewPassed = false;
        }
      }
      if (reviewPassed) {
        state.phase = "coordinate";
      } else {
        state.reviewRounds += 1;
        if (state.reviewRounds >= REVIEW_CAP) {
          state.phase = "halted";
          state.terminalMessage = `Reached REVIEW_CAP (${REVIEW_CAP}); last findings: ${state.lastReview?.findings ?? verdict.findings}`;
        } else {
          state.phase = "build";
        }
      }
    } else if (state.phase === "coordinate") {
      const files = await listLeanFiles(leanDir);
      // Serialize coordination across concurrent study runs on one toolkit: the whole step
      // (barrel edits + merges into shared modules + ledger + lake build + lints) mutates the
      // shared toolkit, so two runs must never interleave — otherwise they clobber each
      // other's snapshots and race on the `.lake` build dir. A queued run waits here. A dry
      // run mutates nothing, so it takes no lock (and writes nothing outside its run record).
      const attempt = () => d.coordinate({
        toolkit, slug, leanDir, requirement, modulePrefix, runDir,
        leanFiles: files, round: state.coordinateRounds + 1,
        lastFailureLog: state.lastCoordinateLog,
        ...(provenance ? { provenance } : {}),
      });
      if (!opts.dryRun) {
        if (state.pendingApply) {
          console.log(`[study] coordinate round ${state.pendingApply.round} was interrupted; its journal is recovered first.`);
        }
        state.pendingApply = { round: state.coordinateRounds + 1, journal: coordinateJournalPath(toolkit, slug) };
        await saveSubstrateState(repoRoot, slug, state, dryRun);
      }
      const res = opts.dryRun
        ? await attempt()
        : await withPromotionLock(toolkit.toolkitRoot, attempt, toolkit.lockPath);
      state.pendingApply = null;
      if (opts.dryRun) console.log(res.log);
      if (res.conflict) {
        // The interrupted promotion cannot be undone automatically: a human resolves it.
        state.phase = "escalated";
        state.terminalRequirementHash = requirementHash;
        state.terminalEscalationKind = "coordinate-recovery";
        state.terminalMessage = res.log;
      } else if (res.ok) {
        state.phase = "done";
        state.terminalMessage = opts.dryRun ? "Dry run: coordination described, toolkit untouched." : "Coordinated into the toolkit.";
      } else if (res.timedOut) {
        // The gate chain (build/axioms/lints/index) was watchdog-killed AFTER the
        // study files were promoted into the toolkit — it went silent for the
        // full timeout without exiting (a genuine hang, or killed mid-flight). We
        // do NOT roll back (that destroys already-promoted work and a mid-build
        // rollback is unsafe) and do NOT burn a retry. Escalate: a human verifies
        // and keeps or reverts. The promotion is UNVERIFIED until then.
        state.phase = "escalated";
        state.terminalRequirementHash = requirementHash;
        state.terminalEscalationKind = "coordinate-timeout";
        state.terminalMessage =
          `Coordinate gate timed out (watchdog kill after going silent) AFTER the study files were ` +
          `promoted into the toolkit at ${toolkit.toolkitRoot}. NOT rolled back and NOT retried — a ` +
          "rollback would destroy already-promoted work, and the gate step may have hung or been " +
          "mid-compile. The promotion is UNVERIFIED: a human must re-run the FULL gate — " +
          `\`lake build ${toolkit.lib}\` (toolkit root) → \`lake env lean runs/study_${slug}/promotion_axioms.lean\` ` +
          "(every promoted declaration axiom-clean) → `bin/lint_module_headers.ts --strict` over " +
          "the toolkit library → `bin/lint_toolkit_layout.ts --scope toolkit` → the toolkit index step " +
          "when one exists — then either keep the promotion (and its ledger entries) or revert it " +
          "manually. Last log tail:\n" +
          res.log.slice(-2000);
      } else {
        state.coordinateRounds += 1;
        state.lastCoordinateLog = res.log.slice(-4000);
        if (state.coordinateRounds >= COORD_CAP) {
          state.phase = "halted";
          state.terminalMessage = `Reached COORD_CAP (${COORD_CAP}); coordination failed and was rolled back; toolkit restored. Last failing log:\n${res.log.slice(-2000)}`;
        } else {
          // Retry: re-enter coordinate with the failure log fed back to the coordinator.
          state.phase = "coordinate";
        }
      }
    } else {
      // done | halted | escalated
      await saveSubstrateState(repoRoot, slug, state, dryRun);
      return state;
    }
    await saveSubstrateState(repoRoot, slug, state, dryRun);
  }
}

/** The study's ledger provenance: the one passed in (written to `provenance.json`), else the one
 *  a previous invocation recorded, else none (a plain study). */
async function resolveProvenance(runDir: string, given: StudyProvenance | undefined): Promise<StudyProvenance | null> {
  const file = path.join(runDir, "provenance.json");
  if (given) {
    const parsed = studyProvenanceSchema.parse(given);
    await mkdir(runDir, { recursive: true });
    await writeFile(file, `${JSON.stringify(parsed, null, 2)}\n`, "utf8");
    return parsed;
  }
  const text = await readFile(file, "utf8").catch(() => null);
  return text === null ? null : studyProvenanceSchema.parse(JSON.parse(text));
}

async function saveRound(runDir: string, report: RoundReport, requirementVersion: number): Promise<void> {
  await mkdir(runDir, { recursive: true });
  // Corrected requirements receive a versioned ledger so their fresh round numbers do not
  // overwrite the evidence that motivated the correction.
  const name = requirementVersion === 0
    ? `round_${report.round}.json`
    : `round_v${requirementVersion}_${report.round}.json`;
  await writeFile(path.join(runDir, name), `${JSON.stringify(report, null, 2)}\n`, "utf8");
}
