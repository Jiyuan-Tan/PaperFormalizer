import { appendFile, mkdir, readdir, readFile, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import path from "node:path";
import { formatStageLabel } from "./constants.js";
import {
  extractJsonObject,
  reviewResultSchema,
  stageOutputSchema,
  type ReviewResult,
} from "./judgment.js";
import { appendReviewLog } from "./log.js";
import type { ReviewLogEntry } from "./log.js";
import {
  crosswalkFullJsonPath,
  crosswalkFullMdPath,
  formalizationDir,
  ensurePaperTmpDir,
  leanModulePrefix,
  leanTheoremDir,
  logsDir,
  mdPath,
  planPath,
  promptPath,
  PAPER_TMP_DIR,
  reviewsDir,
} from "./paths.js";
import type { PipelineContext, Stage, StateJson } from "./types.js";
import {
  addTokenUsage,
  appendTokenUsageRecord,
  markTokenUsageIncomplete,
  type ModelTokenUsage,
} from "./token_usage.js";
import { runClaude } from "./workers/claude.js";
import { claudeRoles } from "./claude_roles.js";
import { resolveCodexReasoningEffort, runCodex } from "./shared/codex.js";

export interface StageDeps {
  runCodex: typeof runCodex;
  runClaude: typeof runClaude;
}

/** Central per-run agent-call INDEX (chronological, ALL stages in one file):
 *  `runs/<slug>/logs/agent_calls.log` — one line per call naming the per-stage transcript that
 *  holds its full prompt and output. The transcript used to be written here too, in full: two
 *  copies of every prompt, 184 MB for one run. */
function centralAgentLogPath(ctx: PipelineContext): string {
  return path.join(logsDir(ctx.repoRoot, ctx.qid), "agent_calls.log");
}

/** The LOGICAL stage of a call: the proof loop runs every review and fill in the F2.5 slot, so
 *  the physical stage mislabels F3 and F4 work. A prompt whose first line is `=== F<stage> …`
 *  names its own stage (the reviewer and the filler do); anything else keeps the slot's label. */
export function logicalStageId(stageId: string, promptHead: string): string {
  const m = promptHead.match(/^=== F(2\.5|3|3\.5|4)\b/);
  return m ? `F${m[1]}` : stageId;
}

/** Slugify a label into a safe, compact filename component (lowercase, `[^a-z0-9]`→`-`). */
function slugifyLabel(s: string, max: number): string {
  const slug = s.toLowerCase().replace(/[^a-z0-9]+/g, "-").replace(/^-+|-+$/g, "").slice(0, max);
  return slug || "misc";
}

/** Per-STAGE transcript file, co-located with the run under `<qid>/logs/stages/`:
 *  `<stageId>__<sub-stage>.log`. The `stageId` (e.g. `F3`, from `formatStageLabel`) groups
 *  by pipeline stage; the sub-stage slug (first prompt line) separates the DISTINCT calls made under
 *  one coarse handler stage — e.g. the F2.5–F4 review loop's faithfulness reviewer vs. filler
 *  each get their own file, with successive rounds appended chronologically.
 *  Leading underscore matches the run-log convention (`_reviewer_calls.log`) so the `_*.log`
 *  .gitignore rule keeps these transient transcripts out of commits. */
function perStageLogPath(ctx: PipelineContext, stageId: string, promptHint: string): string {
  const name = `_${slugifyLabel(stageId, 12)}__${slugifyLabel(promptHint, 48)}.log`;
  return path.join(logsDir(ctx.repoRoot, ctx.qid), "stages", name);
}

async function logAgentCall(
  ctx: PipelineContext,
  stageId: string,
  agent: string,
  prompt: string,
  model: string,
  effort: string,
  ms: number,
  output: string,
): Promise<void> {
  // First non-empty prompt line is the stage/prompt header (e.g. "=== F2.5 DELTA REVIEW ===").
  const stageHint = (prompt.split("\n").find((l) => l.trim().length > 0) ?? "").trim().slice(0, 110);
  const logical = logicalStageId(stageId, stageHint);
  // Log the FULL assembled input prompt (base prompt + sources + graph context) alongside the output,
  // so a wrong/empty base prompt or a mis-assembled source block is directly inspectable — not inferred
  // from the model's behaviour. (An empty base prompt is the failure that motivated this.)
  const header = `===== ${agent} model=${model} effort=${effort} dur=${(ms / 1000).toFixed(0)}s :: ${stageHint} =====`;
  const entry =
    `\n${header}\n` +
    `----- INPUT (${prompt.length} chars) -----\n${prompt}\n` +
    `----- OUTPUT -----\n${output}\n`;
  // The transcript goes to the per-stage file under the run's `logs/stages/` (grouped +
  // discoverable); the central file is a one-line index pointing at it. Best-effort; never throws.
  const central = centralAgentLogPath(ctx);
  const perStage = perStageLogPath(ctx, logical, stageHint);
  const index = `${new Date().toISOString()} ${logical} ${header} input=${prompt.length} output=${output.length} → ${path.relative(path.dirname(central), perStage)}\n`;
  await mkdir(path.dirname(central), { recursive: true }).catch(() => {});
  await mkdir(path.dirname(perStage), { recursive: true }).catch(() => {});
  await Promise.all([
    appendFile(central, index).catch(() => {}),
    appendFile(perStage, entry).catch(() => {}),
  ]);
}

async function logTokenCall(
  ctx: PipelineContext,
  stage: string,
  prompt: string,
  provider: "codex" | "claude",
  model: string,
  durationMs: number,
  success: boolean,
  usage: ModelTokenUsage | null,
): Promise<void> {
  const runDir = formalizationDir(ctx.repoRoot, ctx.qid);
  await appendTokenUsageRecord(runDir, {
    timestamp: new Date().toISOString(),
    provider,
    model,
    stage: logicalStageId(stage, (prompt.split("\n").find((l) => l.trim().length > 0) ?? "").trim()),
    duration_ms: durationMs,
    success,
    usage,
  }).catch(async (err) => {
    console.warn(`[token-usage] could not append call record: ${String(err)}`);
    await markTokenUsageIncomplete(runDir, String(err)).catch((markerErr) => {
      console.warn(`[token-usage] could not mark accounting incomplete: ${String(markerErr)}`);
    });
  });
}

export function defaultDeps(ctx: PipelineContext, currentStage?: Stage, state?: StateJson): StageDeps {
  // Stage label for the per-stage log filename. `liveStageHandler` builds a fresh StageDeps per
  // stage iteration and passes the stage it is running, so every call routes to that stage's file.
  let stageId = "misc";
  if (currentStage !== undefined) {
    try {
      stageId = formatStageLabel(currentStage);
    } catch {
      stageId = String(currentStage);
    }
  }
  // Every source-producing formalization agent is told where scratch belongs.
  // F2 itself stays at the package root because it is the source-emission
  // stage and legacy scaffold prompts still use root-relative production
  // paths. F2.5 onward additionally receives the paper-local cwd, so a
  // relative `Main.lean` cannot pollute the toolkit root.
  const formalizationScratch = state && currentStage !== undefined && Number(currentStage) >= 2;
  const paperTmp =
    formalizationScratch
      ? ensurePaperTmpDir(ctx.repoRoot, state.lean_subdir)
      : undefined;
  // F2.5–F4 run in the paper-local scratch directory. F5 keeps the toolkit-root
  // cwd: it writes run-record artifacts under `runs/<slug>/` as well as paper
  // source, and a paper-tmp cwd would put the run record outside Codex's
  // workspace-write sandbox.
  const usePaperTmpAsCwd =
    currentStage !== undefined && Number(currentStage) >= 2.5 && Number(currentStage) < 5;
  const scratchInstruction = paperTmp
    ? [
        "",
        "Scratch-work boundary:",
        `- Your cwd is this paper's disposable workspace: ${paperTmp}`,
        "- Put every intermediate Lean probe, check file, generated test, and temporary script here (including Main.lean).",
        `- Do not create scratch files at the toolkit root (${ctx.repoRoot}).`,
        "- This tmp/ directory is excluded from the paper's build/review inventory. Write intended paper source only to the explicit production paths named in the task.",
      ].join("\n")
    : "";
  return {
    // Wrap both agents so EVERY stage's call is transcribed (raw output logged on return, before
    // any caller parses it). Logging never throws into the call path (best-effort append).
    runCodex: async (input) => {
      const t0 = Date.now();
      let usage: ModelTokenUsage | null = null;
      const effectiveInput = {
        ...input,
        reasoningEffort: resolveCodexReasoningEffort(input.reasoningEffort),
      };
      try {
        const out = await runCodex({
          ...effectiveInput,
          prompt: effectiveInput.prompt + scratchInstruction,
          cwd: resolveCodexWorkingDirectory({
            requestedCwd: input.cwd,
            paperTmp,
            usePaperTmpAsCwd,
            productionWrite: input.productionWrite,
          }),
          leanProjectPath: usePaperTmpAsCwd ? ctx.repoRoot : input.leanProjectPath,
          // Summed across the runner's transient-retry attempts: each was paid for.
          onUsage: (u) => {
            usage = addTokenUsage(usage, u);
            input.onUsage?.(u);
          },
        });
        const duration = Date.now() - t0;
        await logAgentCall(ctx, stageId, "codex", effectiveInput.prompt, effectiveInput.model ?? "?", effectiveInput.reasoningEffort, duration, out.stdout);
        await logTokenCall(ctx, stageId, effectiveInput.prompt, "codex", effectiveInput.model ?? "?", duration, true, usage);
        return out;
      } catch (err) {
        // "Not lost": a crashed/timed-out call still gets a log entry (with any
        // partial stdout the error carries) before the throw propagates.
        const partial = (err as { stdout?: string })?.stdout ?? "";
        const duration = Date.now() - t0;
        await logAgentCall(ctx, stageId, "codex", effectiveInput.prompt, effectiveInput.model ?? "?", effectiveInput.reasoningEffort, duration, `[CALL THREW: ${err instanceof Error ? err.message : String(err)}]\n${partial}`);
        await logTokenCall(ctx, stageId, effectiveInput.prompt, "codex", effectiveInput.model ?? "?", duration, false, usage);
        throw err;
      }
    },
    runClaude: async (input) => {
      const t0 = Date.now();
      // The runner the role really runs on (`claude_roles.ts`), so the transcript and the ledger name it.
      const runner = claudeRoles().runner;
      // `input.model` may be an alias ("opus"), or the role may run on codex; log the id it
      // resolved to so the run record pins the concrete model (see ClaudeRunInput.onResolvedModel).
      let resolvedModel: string | undefined;
      let usage: ModelTokenUsage | null = null;
      const effort = runner === "codex" ? resolveCodexReasoningEffort("high") : "-";
      try {
        const out = await runClaude({
          ...input,
          prompt: input.prompt + scratchInstruction,
          cwd: usePaperTmpAsCwd ? paperTmp! : input.cwd,
          ...(usePaperTmpAsCwd ? { leanProjectPath: ctx.repoRoot } : {}),
          onResolvedModel: (m) => {
            resolvedModel = m;
            input.onResolvedModel?.(m);
          },
          onUsage: (u) => {
            usage = addTokenUsage(usage, u);
            input.onUsage?.(u);
          },
        });
        const duration = Date.now() - t0;
        await logAgentCall(ctx, stageId, runner, input.prompt, resolvedModel ?? input.model, effort, duration, out);
        await logTokenCall(ctx, stageId, input.prompt, runner, resolvedModel ?? input.model, duration, true, usage);
        return out;
      } catch (err) {
        const partial = (err as { stdout?: string })?.stdout ?? "";
        const duration = Date.now() - t0;
        await logAgentCall(ctx, stageId, runner, input.prompt, resolvedModel ?? input.model, effort, duration, `[CALL THREW: ${err instanceof Error ? err.message : String(err)}]\n${partial}`);
        await logTokenCall(ctx, stageId, input.prompt, runner, resolvedModel ?? input.model, duration, false, usage);
        throw err;
      }
    },
  };
}

/** Resolve the Codex sandbox root for an F-stage call.
 *
 * Read-only reviewers stay in paper-local tmp/. Nested source producers retain
 * their explicit production cwd so workspace-write can reach the Lean modules.
 */
export function resolveCodexWorkingDirectory(args: {
  requestedCwd: string;
  paperTmp?: string;
  usePaperTmpAsCwd: boolean;
  productionWrite?: boolean;
}): string {
  return args.usePaperTmpAsCwd && !args.productionWrite ? args.paperTmp! : args.requestedCwd;
}

export async function readPrompt(ctx: PipelineContext, name: string): Promise<string> {
  return (await readFile(promptPath(ctx.repoRoot, name), "utf8")).replace(/\r\n/g, "\n");
}

export async function readIfExists(file: string): Promise<string> {
  if (!existsSync(file)) return "";
  return readFile(file, "utf8");
}

/** Fail-loud read for a stage-REQUIRED artifact (a
 *  missing required input is a fault, never an empty prompt section). Use
 *  readIfExists only for genuinely optional inputs. */
export async function readRequired(file: string, requiredBy: string): Promise<string> {
  if (!existsSync(file)) {
    throw new Error(`${requiredBy}: required input missing at ${file} — refusing to degrade the prompt/gate`);
  }
  return readFile(file, "utf8");
}

export function artifactPaths(ctx: PipelineContext, state: StateJson) {
  return {
    md: mdPath(ctx.repoRoot, ctx.qid),
    plan: planPath(ctx.repoRoot, ctx.qid),
    formalizationDir: formalizationDir(ctx.repoRoot, ctx.qid),
    leanDir: leanTheoremDir(ctx.repoRoot, state.lean_subdir),
    crosswalkFullJson: crosswalkFullJsonPath(ctx.repoRoot, ctx.qid),
    crosswalkFullMd: crosswalkFullMdPath(ctx.repoRoot, ctx.qid),
  };
}

export function correctionBlock(prior: ReviewResult | null, attempt: number): string {
  if (!prior || prior.status === "pass" || prior.status === "accept") return "";
  const rows = prior.perItemFindings
    .map((item) => `- ${item.label} | ${item.verdict} | ${item.one_line}`)
    .join("\n");
  return [
    `=== CORRECTION (round ${attempt}, prior review classification: ${prior.classification}) ===`,
    `Previous attempt received status ${prior.status}. Fix the items below and what each entails for the entries that depend on it; change nothing else, and do not regress on items that previously passed.`,
    "",
    "Per-item findings:",
    rows || "(none)",
    "",
    "Verbatim critique:",
    prior.verbatim_critique,
    "=== END CORRECTION ===",
    "",
  ].join("\n");
}

// Defense-in-depth: drop keys starting with "_" recursively, so a scaffolding
// key a reviewer leaves in its output cannot trip reviewResultSchema validation.
function stripReviewTemplateKeys(value: unknown): unknown {
  if (Array.isArray(value)) return value.map(stripReviewTemplateKeys);
  if (value && typeof value === "object") {
    const out: Record<string, unknown> = {};
    for (const [k, v] of Object.entries(value as Record<string, unknown>)) {
      if (k.startsWith("_")) continue;
      out[k] = stripReviewTemplateKeys(v);
    }
    return out;
  }
  return value;
}

export function parseReview(stdout: string): ReviewResult {
  try {
    return reviewResultSchema.parse(stripReviewTemplateKeys(extractJsonObject(stdout)));
  } catch (err) {
    const reason = err instanceof Error ? err.message : String(err);
    console.warn(
      `[paperformalizer] parseReview fallback: ${reason}. stdout-tail=${stdout.trim().slice(-300)}`,
    );
    // Synthesize a reject so the boundary halts for the orchestrator instead of
    // crashing. The raw model output is preserved in verbatim_critique so the
    // appendReview log keeps the reviewer's actual text for triage.
    return {
      status: "reject",
      classification: "parse_failure",
      perItemFindings: [],
      verbatim_critique: stdout.trim().slice(0, 4000),
    } as ReviewResult;
  }
}

export function parseStageOutput(stdout: string) {
  try {
    return stageOutputSchema.parse(extractJsonObject(stdout));
  } catch (err) {
    const reason = err instanceof Error ? err.message : String(err);
    console.warn(
      `[paperformalizer] parseStageOutput fallback: ${reason}. stdout-tail=${stdout.trim().slice(-300)}`,
    );
    // why: malformed worker stdout is a hard parse result; never fabricate completion.
    return { status: "parse_failed", message: stdout.trim().slice(0, 500) };
  }
}

export async function appendReview(
  ctx: PipelineContext,
  stage: string,
  attempt: number,
  review: ReviewResult,
): Promise<void> {
  const entry: Omit<Extract<ReviewLogEntry, { kind: "review" }>, "timestamp"> = {
    kind: "review",
    stage,
    attempt,
    status: review.status,
    classification:
      review.status === "reject" || review.status === "revise" ? review.classification : undefined,
    report_summary:
      review.status === "pass" || review.status === "accept"
        ? review.notes
        : review.perItemFindings.map((item) => `${item.label}:${item.verdict}`).join(", "),
    review,
  };
  await appendReviewLog(ctx, entry);
  await persistReviewBoundaryJson(ctx, stage, attempt, review);
}

/**
 * Persist per-attempt review JSON to `reviews/<boundary>_attempt<N>.json` (the run's
 * `reviews/` folder) so review history is greppable as standalone files instead of
 * buried inside reviews.jsonl. Best-effort: errors are logged but never block the pipeline.
 */
async function persistReviewBoundaryJson(
  ctx: PipelineContext,
  boundary: string,
  attempt: number,
  review: ReviewResult,
): Promise<void> {
  try {
    const dir = reviewsDir(ctx.repoRoot, ctx.qid);
    await mkdir(dir, { recursive: true });
    // Sanitize boundary for filesystem (e.g. "stage_1.5_to_1").
    const safe = boundary.replace(/[^A-Za-z0-9._-]/g, "_");
    const file = path.join(dir, `${safe}_attempt${attempt}.json`);
    await writeFile(file, `${JSON.stringify(review, null, 2)}\n`, "utf8");
  } catch (err) {
    const reason = err instanceof Error ? err.message : String(err);
    console.warn(
      `[paperformalizer] persistReviewBoundaryJson failed for ${boundary} attempt ${attempt}: ${reason}`,
    );
  }
}

export async function listLeanFiles(dir: string): Promise<string[]> {
  const out: string[] = [];
  async function walk(current: string) {
    const entries = await readdir(current, { withFileTypes: true }).catch(() => []);
    for (const entry of entries) {
      const full = path.join(current, entry.name);
      // The paper's disposable agent workspace (`<leanDir>/tmp`) is NOT part of the
      // formalization: scratch probes there must never feed the bank-soundness scan,
      // the @node coverage/duplicate gates, or the F2 revise inventory.
      if (entry.isDirectory() && entry.name !== PAPER_TMP_DIR) await walk(full);
      if (entry.isFile() && entry.name.endsWith(".lean")) out.push(full);
    }
  }
  await walk(dir);
  return out;
}

/** Where the run's Lean may come from: the base libraries and the toolkit, from `paperformalizer.json`. */
function libraryContextBlock(ctx: PipelineContext): string {
  const t = ctx.toolkit;
  const bases = t.baseLibraries.map((b) =>
    `- ${b.kind === "path" && b.path ? `${b.name} (source at ${b.path})` : `${b.name} (Lake dependency)`}${b.summary ? `: ${b.summary}` : ""}`,
  );
  return [
    `Base libraries (read-only; reuse what they prove before proving it again):\n${bases.join("\n") || "(none)"}`,
    `Toolkit library (read-only for this run): ${t.lib} at ${t.toolkitLibDir} — divisions ${t.divisions.join(", ")}`,
    `Paper output library: ${t.papersLib} (this run writes only under its own paper directory)`,
    "Path base: cwd-relative Glob/ls of a base library can miss it (base sources live outside the toolkit); " +
      "confirm presence/absence with `lean_local_search` / `lean_leansearch`, which see every Lake dependency.",
  ].join("\n");
}

// Shared definition of a "bookkeeping premise" (a.k.a. regularity side-condition).
// Referenced verbatim by F2 and the F1.5 review so the bookkeeping-vs-content line is
// drawn ONCE and never drifts. The whole point: a regularity side-condition is
// honest scope, NOT content — so adding one must NOT be treated as illegitimate
// assumption-strengthening — while a content assumption dressed as regularity is
// still forbidden (that is the assume-the-conclusion laundering the gate exists to
// stop). Conservative by construction.
export const BOOKKEEPING_PREMISE_NOTE = [
  "BOOKKEEPING PREMISE (regularity side-condition) — definition and policy.",
  "",
  "A hypothesis is BOOKKEEPING iff it is a measurability / integrability /",
  "finiteness / summability / a.e.-definedness / σ-finiteness side-condition whose",
  "ONLY role is to make an object well-defined or to let a Mathlib lemma fire",
  "(`integral_add`, `integral_sub`, `MeasureTheory.integrable_*`, `Measurable.*`,",
  "etc.). It carries no quantitative content: it states nothing about a rate, a",
  "bound, a separation, an identity, or the value of the estimand.",
  "",
  "Bookkeeping premises are LEGITIMATE to add to a lemma OR a theorem signature —",
  "they are honest scope, not assumption-strengthening. Do NOT flag/reject them as",
  "stronger-in-Lean. Two tiers:",
  "  • FREE bookkeeping — follows from hypotheses already present (e.g. a bounded",
  "    measurable function on a probability/finite measure is integrable). PREFER",
  "    TO DERIVE it inline rather than assume it; assuming a derivable side-condition",
  "    is wasteful but never wrong.",
  "  • GENUINE-SCOPE bookkeeping — not derivable from current hypotheses (e.g. an",
  "    unbounded integrand whose integrability is a real restriction). Admissible as",
  "    an added premise.",
  "",
  "NOT bookkeeping (still forbidden as a smuggled premise) — a hypothesis that:",
  "  (a) substitutes for a quantitative step the proof is supposed to perform, or",
  "  (b) encodes the conclusion, a rate, a bound, or a separation, or",
  "  (c) could make the statement VACUOUS (a premise no law in the class satisfies).",
  "",
  "TAIL-CONDITION CARVE-OUT — integrability/finiteness of an UNBOUNDED quantity (an",
  "inverse weight, a score, a ratio) that the paper controls through a tail / moment /",
  "overlap assumption is NOT free bookkeeping: it is tied to (and should be DERIVED",
  "from) that assumption, and for a CONVERSE the explicitly-constructed laws must be",
  "CHECKED to satisfy it — never blanket-assumed, or the converse risks vacuity.",
  "",
  "PREMISE-THREADING (a helper inheriting a premise its caller already has) — adding a",
  "hypothesis to a NON-T-BLOCK helper's signature is a LOCAL, T-block-preserving fix",
  "(handle in place; never a rewind/escalation) EVEN IF the hypothesis is",
  "content-bearing (a rate / tail / overlap / separation / identification condition),",
  "PROVIDED the consuming declaration (the T-block or decl that calls the helper)",
  "ALREADY carries that hypothesis. You are only PROPAGATING an existing assumption",
  "down to the helper, not strengthening the theorem — the T-block's assumption set is",
  "UNCHANGED. Thread it into the helper signature and pass it at every call site. This",
  "counts as content-strengthening (forbidden / structural) ONLY when the premise must",
  "be added to a T-BLOCK itself, or when NO caller in scope already supplies it.",
  "",
  "REFLECT-BACK RULE — whenever a bookkeeping premise is added at the Lean level, it",
  "MUST also be written into the NL note (the .md assumption table / P-entry) as an",
  "explicit regularity assumption, so the Lean signature and the note stay",
  "consistent and the drift-watch does not re-flag it as extra-in-Lean.",
].join("\n");

/** Wrap {@link BOOKKEEPING_PREMISE_NOTE} as a delimited prompt block. Injected by
 *  the F2 and F1.5 builders so both of
 *  them share one definition of the bookkeeping-vs-content line. */
export function bookkeepingPolicyBlock(): string {
  return [
    "=== BOOKKEEPING PREMISE POLICY (shared — applies to every hypothesis you add or judge) ===",
    BOOKKEEPING_PREMISE_NOTE,
    "=== END BOOKKEEPING PREMISE POLICY ===",
  ].join("\n");
}

export function baseBrief(ctx: PipelineContext, state: StateJson): string {
  const paths = artifactPaths(ctx, state);
  return [
    `Toolkit root: ${ctx.repoRoot}`,
    `Run: ${ctx.qid}`,
    `Lean target subdirectory: ${state.lean_subdir} (module prefix ${leanModulePrefix(state.lean_subdir)})`,
    libraryContextBlock(ctx),
    "Library-survey rule: BEFORE drafting or scaffolding, search the base libraries and the toolkit (`lean_local_search` / `lean_leansearch`) for the primitives you need, and reuse an existing structure when it fits the paper's abstraction level. When the library analogue sits at a different abstraction (e.g. a measure-theoretic version where the paper is purely algebraic), scaffolding over Mathlib alone is fine — say why in one line of the plan entry's `notes`; the reviews flag only an unexplained bypass.",
    `NL artifact: ${paths.md}`,
    `Lean artifact directory: ${paths.leanDir}`,
    `Design decisions: ${JSON.stringify(state.design_decisions, null, 2)}`,
    `Added assumptions: ${JSON.stringify(state.added_assumptions, null, 2)}`,
  ].join("\n");
}
