// Round A apply: carry out the owner's decisions on the cited results.
//
// Every accepted entry is BUILT by the study pipeline (`build.ts`): scaffolded, proved, reviewed and
// coordinated into the toolkit under its own gate, and recorded in the ledger as the entry's main
// result. The F1 plan is then pointed at what was built — the cited node becomes a reuse of the
// toolkit declaration, so the F stages prove nothing for it and the paper no longer assumes it —
// and the plan's graph and bridge note are re-emitted. An entry declined automatically because a
// base library or the toolkit already states it is pointed at that declaration the same way.
// Declined and deferred entries stay cited assumptions of the paper. Every decision is appended to
// the ledger (a dry run appends to its own ledger under the run record). Around the builds the
// toolkit graph is re-derived and what the builds made worse is reported (never undone).
import { existsSync } from "node:fs";
import { readFile, writeFile } from "node:fs/promises";
import { applyBuiltDeclsToPlan } from "../formalization/plan/discharge.js";
import { PlanSchema } from "../formalization/plan/schema.js";
import { buildGraphFromCorePlan } from "../graph/from_core.js";
import { renderBridgeNote } from "../graph/render_note.js";
import { graphPath, saveGraph } from "../graph/store.js";
import { indexSourcesFromToolkit } from "../library/sources.js";
import { formalizationDir, mdPath, planPath } from "../paths.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import type { runSubstratePipeline as RunStudy } from "../substrate/pipeline.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { appendDecisionRecords } from "../toolkit/ledger.js";
import { addTopics, effectiveTaxonomy } from "../toolkit/taxonomy.js";
import { readOwnerDecisions, topicDecisionProblems } from "./apply_b.js";
import { buildProposal } from "./build.js";
import { readRunCore } from "./round_b.js";
import {
  applyEdits,
  decisionsPath,
  isMoveDecision,
  proposalBatchSchema,
  proposalDecisionKey,
  proposalLedgerPath,
  type Decision,
  type DecisionsFile,
  type Proposal,
  type ProposalDecisionRecord,
} from "./schema.js";
import { healthRegressions, refreshToolkitGraph, toolkitHealth, type ToolkitGraph } from "./toolkit_graph.js";

export interface ApplyRoundAResult {
  decisions: DecisionsFile;
  records: ProposalDecisionRecord[];
  /** Toolkit declarations the builds recorded. */
  promoted: string[];
  /** Plan nodes pointed at a toolkit or base declaration. */
  planRewrites: Array<{ node: string; decl: string; module: string }>;
  /** What the builds made worse in the toolkit graph, in words (reported, not undone). */
  regressions: string[];
}

/** The module of `name` in the indexes the toolkit names (base libraries and the toolkit), or null. */
export async function declModule(cfg: ToolkitConfig, name: string): Promise<string | null> {
  for (const src of indexSourcesFromToolkit(cfg)) {
    const idx = JSON.parse(await readFile(src.indexPath, "utf8")) as { entries?: Array<{ name?: string; module?: string }> };
    const hit = idx.entries?.find((e) => e.name === name);
    if (hit?.module) return hit.module;
  }
  return null;
}

export async function applyRoundA(args: {
  toolkit: ToolkitConfig;
  qid: string;
  batchFile: string;
  dryRun: boolean;
  log: (msg: string) => void;
  /** The study pipeline (tests inject a fake). */
  runStudy?: typeof RunStudy;
  now?: () => Date;
  /** The toolkit graph (tests); default: re-derived from the Lean (live), none (dry run). */
  graph?: () => Promise<ToolkitGraph | null>;
}): Promise<ApplyRoundAResult> {
  const { toolkit: cfg, qid, log, dryRun } = args;
  const now = args.now ?? (() => new Date());
  const runStudy = args.runStudy ?? (await import("../substrate/pipeline.js")).runSubstratePipeline;
  const batch = proposalBatchSchema.parse(JSON.parse(await readFile(args.batchFile, "utf8")));
  if (batch.round !== "A") throw new Error(`${args.batchFile} is a round-${batch.round} batch, not round A`);
  const owner = await readOwnerDecisions(cfg, qid, batch, dryRun);
  const topics = topicDecisionProblems(cfg, batch, owner, await effectiveTaxonomy(cfg));
  if (topics.problems.length) throw new Error(`refusing --apply:\n  ${topics.problems.join("\n  ")}`);
  if (!dryRun && topics.accepted.length) {
    await addTopics(cfg, topics.accepted);
    log(`topic tree: added ${topics.accepted.map((t) => t.path).join(", ")}`);
  }
  const decidedAt = now().toISOString();
  const decisions: DecisionsFile = { slug: qid, round: "A", decisions: owner, decided_at: decidedAt };
  await writeJsonAtomic(decisionsPath(cfg, qid, "A"), decisions);
  const ledgerFile = proposalLedgerPath(cfg, qid, dryRun);
  const baseRecord = (p: Proposal, d: Decision): ProposalDecisionRecord => ({
    kind: "proposal_decision", slug: qid, round: "A", proposal_id: p.id, decision: d, proposal: p,
    decided_at: decidedAt, batch_created: batch.created, promoted: [], ...(dryRun ? { dry_run: true } : {}),
  });

  const graphOf = args.graph ?? (dryRun ? async () => null : () => refreshToolkitGraph({ toolkit: cfg, log }));
  const proposed = batch.proposals.filter((p) => p.verdict === "propose");
  const accepted = proposed.filter((p) => isMoveDecision(owner[p.id]!));
  const before = accepted.length ? await graphOf().catch(() => null) : null;

  const records: ProposalDecisionRecord[] = [];
  const rewrites: Array<{ node: string; decl: string; module: string; note: string }> = [];
  for (const p of proposed) {
    const d = owner[p.id]!;
    if (!isMoveDecision(d)) {
      log(`${p.id} (${p.source.ref}): ${d.kind} — stays a cited assumption of the paper`);
      records.push(baseRecord(p, d));
      continue;
    }
    const built = await buildProposal({ toolkit: cfg, qid, p: applyEdits(p, d), decision: d, dryRun, runStudy, log });
    const rec = { ...baseRecord(p, d), promoted: built.promoted, study_run: built.studyRun };
    records.push(rec);
    await appendDecisionRecords(ledgerFile, [rec], proposalDecisionKey);
    if (built.main) rewrites.push({ node: p.source.ref, decl: built.main.name, module: built.main.module, note: `built in the toolkit (round-A proposal ${p.id})` });
    else if (dryRun) log(`[dry-run] ${p.id}: nothing built; a live apply points plan node ${p.source.ref} at \`${p.proposed_name}\``);
    else log(`WARNING ${p.id}: the study recorded no main declaration named ${p.proposed_name}; plan node ${p.source.ref} left as F1 planned it`);
  }
  // Already available: the paper uses the existing declaration instead of assuming the result.
  for (const p of batch.proposals.filter((x) => x.duplicate_of)) {
    records.push(baseRecord(p, { kind: "decline", note: `already available as ${p.duplicate_of}` }));
    const module = dryRun ? null : await declModule(cfg, p.duplicate_of!);
    if (module) rewrites.push({ node: p.source.ref, decl: p.duplicate_of!, module, note: `already available (round-A proposal ${p.id})` });
    else if (!dryRun) log(`${p.id}: ${p.duplicate_of} is in no index the toolkit names; plan node ${p.source.ref} left as F1 planned it`);
  }
  const { added, skipped } = await appendDecisionRecords(ledgerFile, records, proposalDecisionKey);
  log(`ledger: ${added.length} decision record(s) appended${skipped.length ? `, ${skipped.length} already recorded` : ""} → ${ledgerFile}`);

  let regressions: string[] = [];
  const after = before ? await graphOf().catch(() => null) : null;
  if (before && after) {
    regressions = healthRegressions(toolkitHealth(before), toolkitHealth(after), records.flatMap((r) => r.promoted));
    for (const r of regressions) log(`toolkit graph: ${r}`);
  }
  if (rewrites.length > 0 && !dryRun) await rewritePlan(cfg, qid, rewrites, log);
  return {
    decisions, records,
    promoted: records.flatMap((r) => r.promoted),
    planRewrites: rewrites.map(({ node, decl, module }) => ({ node, decl, module })),
    regressions,
  };
}

/** Point plan nodes at toolkit / base declarations and re-emit the plan's graph and bridge note
 *  (no stage after F1 has run, so both are rebuilt from the core and the rewritten plan). */
async function rewritePlan(
  cfg: ToolkitConfig,
  qid: string,
  rewrites: ReadonlyArray<{ node: string; decl: string; module: string; note: string }>,
  log: (m: string) => void,
): Promise<void> {
  const p = planPath(cfg.toolkitRoot, qid);
  if (!existsSync(p)) throw new Error(`cannot point the plan at the built declarations: ${p} does not exist`);
  const planObj = JSON.parse(await readFile(p, "utf8")) as unknown;
  applyBuiltDeclsToPlan(planObj, rewrites.map((r) => ({ gate_id: r.node, decl_name: r.decl, module: r.module, note: r.note })));
  const parsed = PlanSchema.safeParse(planObj);
  if (!parsed.success) throw new Error(`the rewritten plan ${p} no longer validates: ${parsed.error.message}`);
  await writeFile(p, JSON.stringify(planObj, null, 2), "utf8");
  for (const r of rewrites) log(`plan: ${r.node} → reuse ${r.decl} (${r.module})`);
  const graph = buildGraphFromCorePlan(await readRunCore(cfg, qid), parsed.data);
  await saveGraph(graphPath(formalizationDir(cfg.toolkitRoot, qid)), graph);
  await writeFile(mdPath(cfg.toolkitRoot, qid), renderBridgeNote(graph), "utf8");
}
