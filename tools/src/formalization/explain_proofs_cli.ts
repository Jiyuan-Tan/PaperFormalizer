/**
 * `paperformalizer explain-proofs <slug>` — run F5's Lean Proof in English step alone
 * (`lean_proof_english.ts` `emitLeanProofEnglish`) on the run's Lean and paper as they now stand:
 * writes `runs/<slug>/lean_proof_english.json` and records the printed proof steps the Lean proof
 * shows wrong as corrections in `patches.json` (a gap is listed with the result only). `paperformalizer report <slug>` then writes the
 * report and the corrected paper with them. Model calls: yes (the F5 model); no stage runs, no
 * `lake`; the run's state is only read.
 */
import { existsSync } from "node:fs";
import { applyWorkerEnv } from "../local_config.js";
import path from "node:path";
import { assertQidSlug, statePath, verifyRunDir } from "../paths.js";
import { defaultDeps, type StageDeps } from "../pipeline_support.js";
import { loadState } from "../state.js";
import { loadToolkitConfig } from "../toolkit/config.js";
import type { PipelineContext } from "../types.js";
import { heartbeatLiveness } from "../shared/run_heartbeat.js";
import { emitLeanProofEnglish } from "./lean_proof_english.js";

export const EXPLAIN_PROOFS_USAGE =
  "Usage: paperformalizer explain-proofs <slug> [--toolkit <path>] [--only <node>,<node>…]\n" +
  "  write the run's Lean Proof in English again (F5's step alone, on the Lean and paper as they now stand) to\n" +
  "  runs/<slug>/lean_proof_english.json, and record the printed proof steps the Lean proof shows wrong as\n" +
  "  corrections of the paper; then `paperformalizer report <slug>` writes the report and corrected paper with them.\n" +
  "  --only: those results alone (the file then holds them alone; a plain run or F5 writes every result again).\n" +
  "  Calls the F5 model; runs no stage and no lake; state.json is only read.";

export function parseExplainProofsArgs(argv: string[]): { slug: string; toolkit: string | null; only: string[] | null } {
  let slug: string | null = null, toolkit: string | null = null, only: string[] | null = null;
  for (let i = 0; i < argv.length; i += 1) {
    const a = argv[i]!;
    if (a === "--toolkit" || a === "--only") {
      const v = argv[i + 1];
      if (!v || v.startsWith("--")) throw new Error(`${a} needs a value.\n${EXPLAIN_PROOFS_USAGE}`);
      if (a === "--toolkit") toolkit = v;
      else only = v.split(",").map((x) => x.trim()).filter(Boolean);
      i += 1;
    } else if (a.startsWith("--")) throw new Error(`unknown flag ${a}.\n${EXPLAIN_PROOFS_USAGE}`);
    else if (slug === null) slug = a;
    else throw new Error(`one slug only.\n${EXPLAIN_PROOFS_USAGE}`);
  }
  if (!slug) throw new Error(EXPLAIN_PROOFS_USAGE);
  assertQidSlug(slug);
  if (only && only.length === 0) throw new Error(`--only names no result.\n${EXPLAIN_PROOFS_USAGE}`);
  return { slug, toolkit, only };
}

/** `deps.stageDeps`: the model calls (tests stub them); `deps.log`: where the summary goes. */
export async function runExplainProofsCli(argv: string[], deps: { stageDeps?: (ctx: PipelineContext) => StageDeps; log?: (m: string) => void } = {}): Promise<string> {
  applyWorkerEnv();
  const a = parseExplainProofsArgs(argv);
  const toolkit = loadToolkitConfig({ explicit: a.toolkit });
  if (!existsSync(statePath(toolkit.toolkitRoot, a.slug))) throw new Error(`no run ${a.slug} under ${toolkit.toolkitRoot} (no state.json).`);
  // a runner at work on the run writes patches.json too: this step waits until it is not
  if (heartbeatLiveness(path.join(verifyRunDir(toolkit.toolkitRoot, a.slug), "logs", ".run.active")).live) throw new Error(`run ${a.slug} is running: explain-proofs records corrections in its patches.json, so run it once the run has halted or finished.`);
  const state = await loadState(toolkit.toolkitRoot, a.slug);
  const ctx: PipelineContext = { repoRoot: toolkit.toolkitRoot, toolkit, qid: a.slug, dryRun: false, resume: true };
  const summary = await emitLeanProofEnglish({ ctx, state, deps: (deps.stageDeps ?? ((c) => defaultDeps(c, "5", state)))(ctx), ...(a.only ? { only: new Set(a.only) } : {}) });
  (deps.log ?? ((m: string) => console.log(`[explain-proofs] ${m}`)))(summary);
  return summary;
}
