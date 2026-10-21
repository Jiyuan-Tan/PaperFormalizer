// Prompt builders for study mode. The static prompt text lives in editable `.txt` templates
// under `./prompts/`; these builders load a template once at module init and substitute
// `{{TOKEN}}` placeholders with the per-call context, including the toolkit context (root,
// library and division names, base libraries, search instructions) rendered from the
// toolkit's `paperformalizer.json`.
import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { paperFormalizerToolsDir, type ToolkitConfig } from "../toolkit/config.js";
import { renderSearchBlock, toolkitSearchSources } from "../toolkit/search.js";
import type { CodexPrompt, RoundReport, ReviewVerdict } from "./types.js";
import { docstringContract } from "../shared/docstring_contract.js";
import { fillTemplate } from "../shared/template.js";

const PROMPT_DIR = path.join(path.dirname(fileURLToPath(import.meta.url)), "prompts");
const SCAFFOLDER_TEMPLATE = readFileSync(path.join(PROMPT_DIR, "scaffolder.txt"), "utf8");
const FILLER_TEMPLATE = readFileSync(path.join(PROMPT_DIR, "filler.txt"), "utf8");
const REVIEWER_TEMPLATE = readFileSync(path.join(PROMPT_DIR, "reviewer.txt"), "utf8");
const COORDINATOR_TEMPLATE = readFileSync(path.join(PROMPT_DIR, "coordinator.txt"), "utf8");

/** Toolkit facts every study prompt needs. */
export interface ToolkitPromptContext {
  toolkitRoot: string;
  lib: string;
  papersLib: string;
  divisions: readonly string[];
  baseNames: string;
  searchBlock: string;
}

export function toolkitPromptContext(
  cfg: ToolkitConfig,
  toolsDir: string = paperFormalizerToolsDir(),
  exists?: (p: string) => boolean,
): ToolkitPromptContext {
  return {
    toolkitRoot: cfg.toolkitRoot,
    lib: cfg.lib,
    papersLib: cfg.papersLib,
    divisions: cfg.divisions,
    baseNames: cfg.baseLibraries.map((b) => (b.summary ? `${b.name} (${b.summary})` : b.name)).join(", ") || "(none)",
    searchBlock: renderSearchBlock(toolkitSearchSources(cfg, toolsDir, exists)),
  };
}

// Admission tests by division name. A division without an entry is described by its barrel's
// `/-! -/` overview.
const ADMISSION_TESTS: Record<string, string> = {
  Foundations:
    "statable in base + toolkit vocabulary; a standard or named result, or a general fact a textbook would state; the base lacks it (search first); axiom-clean.",
  Tricks:
    "a general statement over base + toolkit vocabulary; reusable along the owner's line of work; axiom-clean; may import Foundations.",
};

function admissionTests(ctx: ToolkitPromptContext): string {
  return ctx.divisions
    .map((d) => `   - ${d}: ${ADMISSION_TESTS[d] ?? `see the \`/-! -/\` overview of \`${ctx.lib}/${d}.lean\`.`}`)
    .join("\n");
}

function headerContract(): string {
  return "HEADER CONTRACT — Start each new Lean module with `module`, one contiguous sorted block of `public import` lines, a `/-! ... -/` module docstring, then exactly one blanket `@[expose] public section` when it contains a def-like declaration or `public section` when it is theorem-only; keep declarations bare. Nothing imports a staging module; the coordinator wires promoted modules into their division barrel.";
}

function toolkitVars(ctx: ToolkitPromptContext): Record<string, string> {
  return {
    TOOLKIT_ROOT: ctx.toolkitRoot,
    LIB: ctx.lib,
    PAPERS_LIB: ctx.papersLib,
    DIVISIONS: ctx.divisions.join(" → "),
    BASE_LIBS: ctx.baseNames,
    SEARCH_BLOCK: ctx.searchBlock,
    HEADER_CONTRACT: headerContract(),
    DOCSTRING_CONTRACT: docstringContract(),
  };
}

export function buildScaffolderPrompt(args: {
  toolkit: ToolkitPromptContext;
  slug: string; requirement: string; leanDir: string; modulePrefix: string;
  planMarkdown: string | null; lastReport: RoundReport | null;
  lastReview: ReviewVerdict | null; buildRounds: number; buildCap: number;
}): string {
  const reportBlock = args.lastReport
    ? `\n## Previous round report (round ${args.lastReport.round})\n` +
      `Build ok: ${args.lastReport.build.ok}; sorries remaining: ${args.lastReport.build.sorryCount}.\n` +
      `Build errors:\n${args.lastReport.build.errors.join("\n") || "(none)"}\n` +
      `Filler reports:\n${args.lastReport.fillers.map((f) => `- [${f.id}] ${f.ok ? "ok" : "FAILED"}: ${f.summary}`).join("\n")}\n`
    : "";
  const reviewBlock = args.lastReview
    ? `\n## Reviewer findings to address (the module FAILED review)\n${args.lastReview.findings}\n`
    : "";
  const planBlock = args.planMarkdown ? `\n## Your current plan\n${args.planMarkdown}\n` : "";
  return fillTemplate(SCAFFOLDER_TEMPLATE, {
    ...toolkitVars(args.toolkit),
    REQUIREMENT: args.requirement,
    LEAN_DIR: args.leanDir,
    MODULE_PREFIX: args.modulePrefix,
    ROUND: String(args.buildRounds + 1),
    BUILD_CAP: String(args.buildCap),
    PLAN_BLOCK: planBlock,
    REPORT_BLOCK: reportBlock,
    REVIEW_BLOCK: reviewBlock,
  });
}

export function buildFillerPrompt(args: {
  toolkit: ToolkitPromptContext; leanDir: string; modulePrefix: string; prompt: CodexPrompt;
}): string {
  return fillTemplate(FILLER_TEMPLATE, {
    ...toolkitVars(args.toolkit),
    LEAN_DIR: args.leanDir,
    MODULE_PREFIX: args.modulePrefix,
    TARGET_DECLS: args.prompt.target_decls.join(", ") || "(see instructions)",
    INSTRUCTIONS: args.prompt.prompt,
  });
}

export function buildReviewerPrompt(args: {
  toolkit: ToolkitPromptContext; requirement: string; leanDir: string; modulePrefix: string;
}): string {
  return fillTemplate(REVIEWER_TEMPLATE, {
    ...toolkitVars(args.toolkit),
    REQUIREMENT: args.requirement,
    LEAN_DIR: args.leanDir,
    MODULE_PREFIX: args.modulePrefix,
  });
}

export function buildCoordinatorPrompt(args: {
  toolkit: ToolkitPromptContext; slug: string;
  requirement: string; leanDir: string; modulePrefix: string;
  leanFiles: string[]; stagingDir: string; lastFailureLog: string | null;
  /** The toolkit's topic tree, one `- path: scope` line per topic. */
  topicTree?: string;
}): string {
  const failureBlock = args.lastFailureLog
    ? `\n## Previous attempt FAILED the integration gate — fix and retry\n` +
      "Your last manifest was applied then rolled back because a step below failed. " +
      "Read the log, find the cause (bad placement, missing/duplicate import, a dedup " +
      "rewire that broke a proof, a merge anchor that did not exist), and emit a corrected " +
      `manifest.\n\n\`\`\`\n${args.lastFailureLog}\n\`\`\`\n`
    : "";
  return fillTemplate(COORDINATOR_TEMPLATE, {
    ...toolkitVars(args.toolkit),
    ADMISSION_TESTS: admissionTests(args.toolkit),
    SLUG: args.slug,
    REQUIREMENT: args.requirement,
    LEAN_DIR: args.leanDir,
    MODULE_PREFIX: args.modulePrefix,
    LEAN_FILES: args.leanFiles.map((f) => `- ${f}`).join("\n") || "(none)",
    STAGING_DIR: args.stagingDir,
    FAILURE_BLOCK: failureBlock,
    TOPIC_TREE: args.topicTree ?? "(none: any topic directory)",
  });
}
