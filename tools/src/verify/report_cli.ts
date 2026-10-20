/**
 * `theoremchecker report <slug>` — write a run's report (`report.md`, `report.json`) and its
 * corrected-paper bundle (`bundle/`) again from the run's records, without running any stage: no model
 * call, no `lake`. The Lean evidence (build, source scan, axioms) is the one the report on file
 * recorded when V6 last ran; everything else is read as V6 reads it, under the same identity gates.
 * What other steps added to the report on file (its Toolkit section, the results a promotion round
 * moved) is carried over. `--out <dir>` writes both there and leaves the run untouched.
 */
import { existsSync } from "node:fs";
import { mkdir, readFile } from "node:fs/promises";
import path from "node:path";
import { applyWorkerEnv } from "../local_config.js";
import { assertQidSlug, statePath, verifyRunDir } from "../paths.js";
import type { RoundBMove } from "../proposals/schema.js";
import type { ReuseReport } from "../proposals/reuse.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import { loadState, saveState } from "../state.js";
import { loadToolkitConfig } from "../toolkit/config.js";
import type { CompileTex } from "./annotated_paper.js";
import { githubTree } from "./bundle_lean.js";
import { ARXIV_ID } from "./f4_seal.js";
import type { CollectLeanEvidence, LeanEvidence } from "./lean_evidence.js";
import { writeReportToolkitSection } from "./report_toolkit.js";
import type { ReportRow, VerifyReportJson } from "./report.js";
import { makeStageV6 } from "./stage_v6_report.js";
import { VERIFY_FILES } from "./types.js";

export const REPORT_USAGE =
  "Usage: theoremchecker report <slug> [--toolkit <path>] [--out <dir>] [--verify-public] [--arxiv <id>]\n" +
  "  write the run's report and corrected-paper bundle again from its records (no stage runs, no model call, no lake:\n" +
  "  the Lean evidence is the one the report on file recorded). --out <dir>: write them there and leave the run untouched.\n" +
  "  --verify-public: compare, over the network, the base-library files the paper was built against with the public\n" +
  "  revisions bundle/lean requires (the GitHub API; nothing is cloned).\n" +
  "  --arxiv <id>: the paper's arXiv identifier (2301.01234v2), recorded in the run and under the bundle's F4 seal.";

export function parseReportArgs(argv: string[]): { slug: string; toolkit: string | null; out: string | null; verifyPublic?: true; arxiv?: string } {
  let verifyPublic = false;
  let slug: string | null = null;
  let toolkit: string | null = null;
  let out: string | null = null;
  let arxiv: string | null = null;
  for (let i = 0; i < argv.length; i += 1) {
    const a = argv[i]!;
    if (a === "--toolkit" || a === "--out" || a === "--arxiv") {
      const v = argv[i + 1];
      if (!v || v.startsWith("--")) throw new Error(`${a} needs a value.\n${REPORT_USAGE}`);
      if (a === "--toolkit") toolkit = v;
      else if (a === "--arxiv") arxiv = v.replace(/^arxiv:/iu, "");
      else out = path.resolve(v);
      i += 1;
    } else if (a === "--verify-public") verifyPublic = true;
    else if (a.startsWith("--")) throw new Error(`unknown flag ${a}.\n${REPORT_USAGE}`);
    else if (slug === null) slug = a;
    else throw new Error(`one slug only.\n${REPORT_USAGE}`);
  }
  if (!slug) throw new Error(REPORT_USAGE);
  assertQidSlug(slug);
  if (arxiv !== null && !ARXIV_ID.test(arxiv)) throw new Error(`--arxiv: ${JSON.stringify(arxiv)} is not an arXiv identifier (2301.01234, 2301.01234v2, math.ST/0601001).\n${REPORT_USAGE}`);
  return { slug, toolkit, out, ...(verifyPublic ? { verifyPublic: true as const } : {}), ...(arxiv !== null ? { arxiv } : {}) };
}

type MovedRow = ReportRow & { moved_to_toolkit?: boolean; moved_from?: string };
type OnFile = VerifyReportJson & { toolkit?: { reuse?: ReuseReport | null; moves?: RoundBMove[]; main_results_used?: string[] } };

/** The Lean evidence a report recorded: its build, its source scan, each anchored declaration's axioms. */
export function evidenceOnFile(report: VerifyReportJson): LeanEvidence | null {
  if (!report.lean_build) return null;
  return {
    build: report.lean_build,
    sorry_scan: report.sorry_scan ?? [],
    axioms: Object.fromEntries(report.results.flatMap((r) => (r.lean && r.axioms ? [[r.lean.decl, r.axioms] as const] : []))),
  };
}

export async function runReportCli(argv: string[], deps: { log?: (m: string) => void; compileTex?: CompileTex } = {}): Promise<void> {
  applyWorkerEnv();
  const a = parseReportArgs(argv);
  const toolkit = loadToolkitConfig({ explicit: a.toolkit });
  const log = deps.log ?? ((m: string) => console.log(`[report] ${m}`));
  if (!existsSync(statePath(toolkit.toolkitRoot, a.slug))) throw new Error(`no run ${a.slug} under ${toolkit.toolkitRoot} (no state.json).`);
  const state = await loadState(toolkit.toolkitRoot, a.slug);
  if (!state.verify) throw new Error(`${a.slug} is not a verify run (state.json has no verify block).`);
  const runDir = verifyRunDir(toolkit.toolkitRoot, a.slug);
  if (a.arxiv) state.verify.source.arxiv = a.arxiv;
  const onFile = path.join(runDir, VERIFY_FILES.reportJson);
  if (!existsSync(onFile)) throw new Error(`${a.slug} has no report yet (${VERIFY_FILES.reportJson}): V6 writes the first one — continue the run with --resume.`);
  const prior = JSON.parse(await readFile(onFile, "utf8")) as OnFile;
  const evidence = evidenceOnFile(prior);
  if (!prior.run.early_stop && !evidence) throw new Error(`the report on file of ${a.slug} records no Lean evidence; re-run V6 (verify --from-stage V6) to collect it.`);
  const collect: CollectLeanEvidence = async () => evidence!;
  if (a.out) await mkdir(a.out, { recursive: true });
  const stage = makeStageV6({ collectLeanEvidence: collect, ...(deps.compileTex ? { compileTex: deps.compileTex } : {}), ...(a.out ? { outDir: a.out } : {}), ...(a.verifyPublic ? { publicTree: githubTree() } : {}) });
  const r = await stage({ repoRoot: toolkit.toolkitRoot, qid: a.slug, runDir, state, deps: { runCodex: (() => { throw new Error("report: no model call"); }) as never }, dryRun: false, log });
  // What the promotion round added to the report on file.
  const dir = a.out ?? runDir;
  const moved = new Map((prior.results as MovedRow[]).filter((x) => x.moved_to_toolkit).map((x) => [x.node_id, x] as const));
  if (moved.size > 0) {
    const obj = JSON.parse(await readFile(path.join(dir, VERIFY_FILES.reportJson), "utf8")) as VerifyReportJson;
    for (const row of obj.results as MovedRow[]) {
      const m = moved.get(row.node_id);
      if (m) Object.assign(row, { moved_to_toolkit: true, moved_from: m.moved_from });
    }
    await writeJsonAtomic(path.join(dir, VERIFY_FILES.reportJson), obj);
  }
  // The declared identifier is the run's from here on, once its report and bundle carry it.
  if (a.arxiv && !a.out) await saveState(toolkit.toolkitRoot, a.slug, state);
  if (prior.toolkit) await writeReportToolkitSection(dir, prior.toolkit.reuse ?? null, prior.toolkit.moves, prior.toolkit.main_results_used);
  log(`${r.message}; bundle at ${path.join(dir, "bundle")}`);
}
