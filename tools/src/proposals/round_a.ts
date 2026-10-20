// Round A: toolkit proposals after F1, before anything is proved.
//
// Round A proposes ONLY what the paper relies on without proving: its CITED results (core statements
// with `status: "cited"`), skipping those the F1 plan already maps to an existing declaration
// (`disposition: "reuse"`) and undelivered ones. The paper's own lemmas wait for round B (after they
// are proved) and its theorems stay in the paper. Each candidate carries the cited work's own text
// when V1.5 fetched it (`discovery/cited_sources/`) and the owner's other runs citing the same
// theorem (its recurrence). The curator writes each proposed result as a textbook entry, the checker
// re-judges it (a result the base libraries or the toolkit already state is declined), and the
// round writes `runs/<slug>/proposals/A.json` and the owner's checklist
// `<toolkit>/doc/proposals/<slug>.A.md`. Accepted entries are BUILT by the study pipeline
// (`leansmith propose <slug> --round A --apply`, `apply_a.ts`).
import { existsSync } from "node:fs";
import { mkdir, readFile, readdir } from "node:fs/promises";
import path from "node:path";
import { parseTypedCore } from "../core/core_io.js";
import type { Core } from "../core/schema.js";
import { PlanSchema, type Plan } from "../formalization/plan/schema.js";
import { planPath } from "../paths.js";
import type { runCodex as RunCodex } from "../shared/codex.js";
import { writeJsonAtomic, writeTextAtomic } from "../shared/json_atomic.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { ensureTaxonomy } from "../toolkit/taxonomy.js";
import type { ClaudeRunInput } from "../workers/claude.js";
import { CITED_SOURCES_DIR, excerptAround, sourceFileKey } from "../verify/cited_sources.js";
import { VERIFY_FILES } from "../verify/types.js";
import { renderChecklist, ROUND_IS_DELEGATED, ROUND_IS_THE_OWNERS } from "./checklist.js";
import { runChecker } from "./checker.js";
import { runCurator, type ProposalCandidate } from "./curator.js";
import { archiveEarlierRound, readRunCore } from "./round_b.js";
import { batchPath, checklistPath, type ProposalBatch, type ProposalRoundState, type Recurrence } from "./schema.js";
import { healthSummary, readToolkitGraph, toolkitHealth } from "./toolkit_graph.js";

const STATEMENT_ID_RE = /^(thm|lem|prop|cor|conj):/;
/** Cited-source excerpt shown to the curator and the checker. */
const SOURCE_EXCERPT_MAX = 4000;

type Statement = Core["statements"][number];

function citationOf(core: Core, s: Statement): string | undefined {
  if (!s.source) return undefined;
  const bib = core.bibliography.find((b) => b.key === s.source!.cite);
  return `${bib ? bib.citation : s.source.cite}, ${s.source.locator}`;
}

/** The cited work's text of `s` that V1.5 fetched or the user supplied, as an excerpt around its locator. */
export async function citedSourceText(runDir: string, s: Statement): Promise<string | undefined> {
  if (!s.source) return undefined;
  const base = path.join(runDir, CITED_SOURCES_DIR, sourceFileKey(s.source.cite));
  for (const ext of [".txt", ".tex", ".arxiv.tex"]) {
    if (existsSync(base + ext)) return excerptAround(await readFile(base + ext, "utf8"), s.source.locator, SOURCE_EXCERPT_MAX);
  }
  return undefined;
}

const words = (t: string): Set<string> => new Set(t.toLowerCase().split(/[^a-z0-9]+/).filter((w) => w.length > 2));
function jaccard(a: Set<string>, b: Set<string>): number {
  if (a.size === 0 || b.size === 0) return 0;
  let both = 0;
  for (const w of a) if (b.has(w)) both += 1;
  return both / (a.size + b.size - both);
}

/** The owner's other runs citing the same result: `identical` = the same locator in a work whose
 *  citation largely agrees; `similar` = a statement whose words largely agree. */
export async function citedRecurrence(cfg: ToolkitConfig, qid: string, core: Core, s: Statement): Promise<Recurrence[]> {
  const out: Recurrence[] = [];
  const cite = words(citationOf(core, s) ?? "");
  const locator = (s.source?.locator ?? "").toLowerCase().replace(/\s+/g, "");
  const stmt = words(s.statement);
  const runs = await readdir(cfg.runsDir, { withFileTypes: true }).catch(() => []);
  for (const r of runs) {
    if (!r.isDirectory() || r.name === qid || r.name.startsWith("_")) continue;
    const p = path.join(cfg.runsDir, r.name, VERIFY_FILES.coreJson);
    if (!existsSync(p)) continue;
    let other: Core;
    try {
      other = parseTypedCore(await readFile(p, "utf8"), `recurrence: ${p}`);
    } catch {
      continue;
    }
    for (const t of other.statements) {
      if (t.status !== "cited") continue;
      const sameLoc = locator !== "" && (t.source?.locator ?? "").toLowerCase().replace(/\s+/g, "") === locator;
      if (sameLoc && jaccard(cite, words(citationOf(other, t) ?? "")) >= 0.6) {
        out.push({ slug: r.name, name: t.id, kind: "identical" });
        continue;
      }
      const score = jaccard(stmt, words(t.statement));
      if (score >= 0.5) out.push({ slug: r.name, name: t.id, kind: "similar", score: Math.round(score * 100) / 100 });
    }
  }
  return out;
}

/** Round-A candidates from the typed core and the F1 plan (`null` = no plan: dry run only): the
 *  cited results only, never one of the paper's own. */
export async function roundACandidates(cfg: ToolkitConfig, qid: string, core: Core, plan: Plan | null): Promise<ProposalCandidate[]> {
  const runDir = path.join(cfg.runsDir, qid);
  const out: ProposalCandidate[] = [];
  const listed = new Set<string>();
  for (const s of core.statements) {
    if (!STATEMENT_ID_RE.test(s.id) || s.status !== "cited") continue;
    const n = plan?.nodes[s.id];
    if (plan && (!n || n.disposition === "reuse" || n.delivery_status === "undelivered")) continue;
    // A published result several proofs invoke is a cited leaf of each (`cited_in`): one candidate.
    const result = s.source ? `${s.source.cite}\u0000${s.source.locator}` : s.id;
    if (s.cited_in && listed.has(result)) continue;
    listed.add(result);
    const citation = citationOf(core, s);
    const sourceText = await citedSourceText(runDir, s);
    out.push({
      candidate_id: s.id,
      source: { kind: "cited", ref: s.id, ...(citation ? { citation } : {}) },
      kind: s.kind,
      statement: s.statement,
      context: {
        depends_on: s.depends_on,
        ...(n ? { plan: { lean_name: n.lean_name, lean_kind: n.lean_kind, notes: n.notes ?? null } } : {}),
        ...(sourceText ? { source_text: sourceText } : {}),
      },
      search_words: `${s.source?.locator ?? ""} ${s.statement.split(/[.\n]/)[0]}`.trim(),
      ...(sourceText ? { source_text: sourceText } : {}),
      recurrence: await citedRecurrence(cfg, qid, core, s),
    });
  }
  return out;
}

async function readPlan(cfg: ToolkitConfig, qid: string, dryRun: boolean, log: (m: string) => void): Promise<Plan | null> {
  const p = planPath(cfg.toolkitRoot, qid);
  if (!existsSync(p)) {
    if (dryRun) {
      log("promotion A: no plan.json (dry-run F stages write none) — every cited result is a candidate");
      return null;
    }
    throw new Error(`promotion A: F1 completed but ${p} does not exist; round A needs the plan (a runner bug).`);
  }
  const parsed = PlanSchema.safeParse(JSON.parse(await readFile(p, "utf8")));
  if (!parsed.success) throw new Error(`promotion A: ${p} does not validate against the plan schema: ${parsed.error.message}`);
  return parsed.data as Plan;
}

/** The plan-schema violations of the plan on file, one per line (`<path>: <message>`), or null when
 *  it validates or no plan is written. Round A reads the plan, so a plan that breaks the schema goes
 *  back to F1 with these before the round is held. */
export async function planSchemaViolations(toolkitRoot: string, qid: string): Promise<string | null> {
  const p = planPath(toolkitRoot, qid);
  if (!existsSync(p)) return null;
  let raw: unknown;
  try {
    raw = JSON.parse(await readFile(p, "utf8"));
  } catch (err) {
    return `plan.json: not valid JSON (${err instanceof Error ? err.message : String(err)})`;
  }
  const parsed = PlanSchema.safeParse(raw);
  return parsed.success ? null : parsed.error.issues.map((i) => `${i.path.join(".")}: ${i.message}`).join("\n");
}

/** Run round A for a verify run whose F1 has completed: candidates, curator, checker, batch and
 *  (when anything is proposed) the owner's checklist. */
export async function runRoundA(args: {
  toolkit: ToolkitConfig;
  qid: string;
  dryRun: boolean;
  /** The checker (codex). */
  runCodex: typeof RunCodex;
  /** The curator (Claude); default: the claude CLI worker. */
  runClaude?: (o: ClaudeRunInput) => Promise<string>;
  log: (msg: string) => void;
  now?: () => Date;
}): Promise<ProposalRoundState> {
  const { toolkit: cfg, qid, log, dryRun } = args;
  const created = (args.now ?? (() => new Date()))().toISOString();
  const core = await readRunCore(cfg, qid);
  if (!dryRun) await ensureTaxonomy(cfg, log);
  // A cited result is a standard result: built in general form in Mathlib's vocabulary unless it
  // needs a domain library's.
  const candidates = (await roundACandidates(cfg, qid, core, await readPlan(cfg, qid, dryRun, log)))
    .map((c) => ({ division_signal: "Foundations" as const, ...c }));
  log(`promotion A: ${candidates.length} cited result(s) the paper assumes${candidates.length ? `: ${candidates.map((c) => c.candidate_id).join(", ")}` : ""}`);
  let proposals = candidates.length === 0
    ? []
    : await runCurator({ toolkit: cfg, slug: qid, round: "A", candidates, dryRun, log, ...(args.runClaude ? { runClaude: args.runClaude } : {}) });
  proposals = await runChecker({ toolkit: cfg, slug: qid, round: "A", proposals, candidates, dryRun, runCodex: args.runCodex, log });
  const batch: ProposalBatch = { slug: qid, round: "A", created, proposals };
  const bp = batchPath(cfg, qid, "A");
  await mkdir(path.dirname(bp), { recursive: true });
  const earlier = await archiveEarlierRound(cfg, qid, batch);
  if (earlier.length > 0) log(`promotion A: an earlier round A left ${earlier.join(", ")} — moved under proposals/voided/`);
  await writeJsonAtomic(bp, batch);
  const proposed = proposals.filter((p) => p.verdict === "propose");
  if (proposed.length === 0) {
    log(`promotion A: nothing proposed (${candidates.length} candidate(s)) — continuing to F1.5; batch ${bp}`);
    return { status: "empty", batch_path: bp, checklist_path: null, created_at: created, promoted: [] };
  }
  const cp = checklistPath(cfg, qid, dryRun, "A");
  await mkdir(path.dirname(cp), { recursive: true });
  const graph = dryRun ? null : await readToolkitGraph(cfg).catch(() => null);
  const health = graph ? healthSummary(toolkitHealth(graph)) : undefined;
  await writeTextAtomic(cp, renderChecklist(batch, { toolkitRoot: cfg.toolkitRoot, dryRun, ...(health ? { health } : {}) }));
  const dup = proposals.filter((p) => p.duplicate_of).length;
  const disagreements = proposed.filter((p) => p.checker && !p.checker.agrees).length;
  log(
    `promotion A: ${proposed.length} cited result(s) proposed for the toolkit${dup ? `, ${dup} declined as already available` : ""}` +
      `${disagreements ? `, checker disagrees on ${disagreements}` : ""}; batch ${bp}`,
  );
  return { status: "pending_user", batch_path: bp, checklist_path: cp, created_at: created, promoted: [] };
}

/** The stop message of a pending round A. */
export function roundAStopMessage(cfg: ToolkitConfig, qid: string, rec: ProposalRoundState, count: number, dryRun = false, fullAuto = false): string {
  return `promotion A: ${count} cited result(s) proposed for the toolkit — ${fullAuto ? ROUND_IS_DELEGATED : ROUND_IS_THE_OWNERS}; the checklist is ${rec.checklist_path}, applied by: ` +
    `leansmith propose ${qid} --round A --apply --toolkit ${cfg.toolkitRoot}${dryRun ? " --dry-run" : ""}`;
}
