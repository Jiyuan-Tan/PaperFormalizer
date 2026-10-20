/**
 * `leansmith relink <slug>` — run F5's paper ↔ Lean link step alone (`nl_links.ts`
 * `emitNlLinks`) on the run's Lean and paper as they now stand, and write `nl_links.json`: what
 * brings links back for a statement edited since F5 (the page shows such a statement unlinked),
 * written against a statement cut short, or one no call answered. `--only <node>,…` links those
 * results alone and keeps what is stored for the others. A result linked from the same
 * statement, Lean and prompts keeps its links without a call; one whose links still fit its statement
 * and Lean is revised from them (one audit call); `--fresh` links every result from nothing. Model calls: yes (the F5 model); no stage
 * runs, no `lake`; the run's state is only read.
 */
import { existsSync } from "node:fs";
import { applyWorkerEnv } from "../local_config.js";
import { assertQidSlug, statePath } from "../paths.js";
import { defaultDeps, type StageDeps } from "../pipeline_support.js";
import { loadState } from "../state.js";
import { loadToolkitConfig } from "../toolkit/config.js";
import type { PipelineContext } from "../types.js";
import { emitNlLinks } from "./nl_links.js";

export const RELINK_USAGE =
  "Usage: leansmith relink <slug> [--toolkit <path>] [--only <node>,<node>…] [--fresh]\n" +
  "  link the run's results to their Lean statements row by row again (F5's link step alone, on the Lean and\n" +
  "  paper as they now stand) and write runs/<slug>/nl_links.json; --only: those results, the others kept as stored.\n" +
  "  Links made from the same statement, Lean and prompts and returned whole by the audit are kept; links that still fit are revised, not redone; --fresh: link from nothing.\n" +
  "  Calls the F5 model; runs no stage and no lake; state.json is only read.";

export interface RelinkArgs { slug: string; toolkit: string | null; only: string[] | null; fresh: boolean }

export function parseRelinkArgs(argv: string[]): RelinkArgs {
  let slug: string | null = null, toolkit: string | null = null, only: string[] | null = null, fresh = false;
  for (let i = 0; i < argv.length; i += 1) {
    const a = argv[i]!;
    if (a === "--toolkit" || a === "--only") {
      const v = argv[i + 1];
      if (!v || v.startsWith("--")) throw new Error(`${a} needs a value.\n${RELINK_USAGE}`);
      if (a === "--toolkit") toolkit = v;
      else only = v.split(",").map((s) => s.trim()).filter(Boolean);
      i += 1;
    } else if (a === "--fresh") fresh = true;
    else if (a.startsWith("--")) throw new Error(`unknown flag ${a}.\n${RELINK_USAGE}`);
    else if (slug === null) slug = a;
    else throw new Error(`one slug only.\n${RELINK_USAGE}`);
  }
  if (!slug) throw new Error(RELINK_USAGE);
  assertQidSlug(slug);
  if (only && only.length === 0) throw new Error(`--only names no result.\n${RELINK_USAGE}`);
  return { slug, toolkit, only, fresh };
}

/** `deps.stageDeps`: the model calls (tests stub them); `deps.log`: where the summary and the
 *  per-result metrics go. */
export async function runRelinkCli(argv: string[], deps: { stageDeps?: (ctx: PipelineContext) => StageDeps; log?: (m: string) => void } = {}): Promise<string> {
  applyWorkerEnv();
  const a = parseRelinkArgs(argv);
  const toolkit = loadToolkitConfig({ explicit: a.toolkit });
  if (!existsSync(statePath(toolkit.toolkitRoot, a.slug))) throw new Error(`no run ${a.slug} under ${toolkit.toolkitRoot} (no state.json).`);
  const state = await loadState(toolkit.toolkitRoot, a.slug);
  const ctx: PipelineContext = { repoRoot: toolkit.toolkitRoot, toolkit, qid: a.slug, dryRun: false, resume: true };
  const summary = await emitNlLinks({ ctx, state, deps: (deps.stageDeps ?? ((c) => defaultDeps(c, "5", state)))(ctx), ...(a.only ? { only: new Set(a.only) } : {}), fresh: a.fresh });
  (deps.log ?? ((m: string) => console.log(`[relink] ${m}`)))(summary);
  return summary;
}
