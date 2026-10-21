// `paperformalizer docstrings`: bring the toolkit's docstrings to the docstring contract
// (shared/prompts/docstring_contract.txt) — the same batched codex pass F5 runs on a paper's
// modules, pointed at the toolkit library. Docstring edits only; a build failure restores them.
import { readdir } from "node:fs/promises";
import path from "node:path";
import { documentModules } from "../formalization/stage5_docstrings.js";
import { defaultDeps } from "../pipeline_support.js";
import { ensureLogsDir, formalizationDir } from "../paths.js";
import type { PipelineContext } from "../types.js";
import { loadToolkitConfig, type ToolkitConfig } from "./config.js";
import { assertToolkitLakefile } from "./lakefile.js";

export const DOCSTRINGS_USAGE =
  "Usage: paperformalizer docstrings [--toolkit <path>] [--modules M1,M2,…]\n" +
  "  document the toolkit's declarations to the docstring contract (NL translation + crosslinks);\n" +
  "  default: every module of the toolkit's divisions. Records under runs/toolkit_docstrings/.";

/** The run id the pass records under (`runs/<id>/`). */
export const TOOLKIT_DOCSTRINGS_RUN = "toolkit_docstrings";

/** Dotted module names of every `.lean` file under the toolkit's divisions (barrels included). Sorted. */
export async function toolkitModules(cfg: ToolkitConfig): Promise<string[]> {
  const out: string[] = [];
  for (const div of cfg.divisions) {
    const dir = path.join(cfg.toolkitRoot, cfg.lib, div);
    const files = (await readdir(dir, { recursive: true }).catch(() => [] as string[])).map(String);
    out.push(`${cfg.lib}.${div}`);
    for (const f of files) {
      if (f.endsWith(".lean")) out.push(`${cfg.lib}.${div}.${f.slice(0, -5).split(path.sep).join(".")}`);
    }
  }
  return [...new Set(out)].sort();
}

export async function runDocstringsCli(argv: string[]): Promise<void> {
  const value = (flag: string): string | null => {
    const i = argv.indexOf(flag);
    if (i < 0) return null;
    const v = argv[i + 1];
    if (!v || v.startsWith("--")) throw new Error(`${flag} needs a value\n${DOCSTRINGS_USAGE}`);
    return v;
  };
  const cfg = loadToolkitConfig({ explicit: value("--toolkit") });
  assertToolkitLakefile(cfg);
  const modules = value("--modules")?.split(",").map((m) => m.trim()).filter(Boolean) ?? await toolkitModules(cfg);
  const ctx: PipelineContext = { repoRoot: cfg.toolkitRoot, toolkit: cfg, qid: TOOLKIT_DOCSTRINGS_RUN, dryRun: false, resume: false };
  ensureLogsDir(ctx.repoRoot, ctx.qid);
  console.log(`[docstrings] ${modules.length} module(s) of ${cfg.toolkitRoot}`);
  const block = await documentModules({
    ctx, deps: defaultDeps(ctx), modules, prefix: cfg.lib,
    outDir: formalizationDir(ctx.repoRoot, ctx.qid), label: "toolkit",
  });
  if (block) {
    console.error(block);
    process.exitCode = 1;
    return;
  }
  console.log("[docstrings] every declaration meets the docstring contract — review the diff and commit the toolkit");
}
