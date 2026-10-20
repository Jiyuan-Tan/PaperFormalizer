// Round B apply: carry out the owner's decisions on the proposed main results.
//
//   accept / accept_with_edits  MOVE the result and its closure (`moves_with`: the helper lemmas
//                               and definitions it needs) out of the paper into the target toolkit
//                               module (`move.ts`), under the promotion lock, gated by
//                               `lake build <lib>`, `lake build <paper>`, `#print axioms` (moved
//                               declarations clean, the paper's headline results unchanged), the
//                               layout lints, statement invariance and the toolkit index. A move
//                               that fails its gate is left as written and escalated: the
//                               orchestrator repairs it by hand and the next `--apply` runs the
//                               gate on the files as they stand. The result is recorded `tier: main`, its closure
//                               `tier: aux` owned by it.
//   decline / defer             recorded only (with the items declined automatically as already
//                               available).
//
// Items are applied one at a time in dependency order; each successful item is recorded in the
// ledger at once, so a failure part-way leaves the earlier items applied and recorded and a re-run
// continues with the rest. Before any write the paper is re-scanned: an accepted item that is no
// longer a clean candidate, or whose closure changed, refuses the apply (re-propose with
// `--from-stage V6`). Around the moves the toolkit graph is re-derived: before, a duplicate of a
// toolkit result refuses its item; after, what the moves made worse (a result used by nothing, a
// module falling apart) is reported — never undone. A dry run records decisions (in its own ledger)
// and describes the moves; it never touches Lean.
import { existsSync, readFileSync } from "node:fs";
import { mkdir, readdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { crosswalkFullJsonPath, leanModulePrefix, leanTheoremDir, PAPER_TMP_DIR } from "../paths.js";
import { withPromotionLock } from "../shared/build_mutex.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import { loadState } from "../state.js";
import { theoremCheckerToolsDir, type ToolkitConfig } from "../toolkit/config.js";
import { appendDecisionRecords, loadLedger, type LedgerDeclaration } from "../toolkit/ledger.js";
import { parseAxiomReport } from "../verify/lean_evidence.js";
import { writeReportToolkitSection, loadRunReuse } from "../verify/report_toolkit.js";
import { VERIFY_FILES } from "../verify/types.js";
import { buildProposal, builtByOwnStudy, reproveAsCorollary, type CorollaryDeps } from "./build.js";
import { indexNameTable, nameProblems } from "./curator.js";
import { carryReceipts, fingerprintScanCmd, parseFingerprints, receiptsBefore, statementInvarianceFailure, takeFingerprints } from "./invariance.js";
import { candidatesPath, filterCandidates, obtainScan, paperObjects, paperShapedReasons, reportHeadlineDecls, type CandidateScan, type CandidatesFile } from "./candidate_scan.js";
import type { runSubstratePipeline as RunStudy } from "../substrate/pipeline.js";
import { newTopics, parseChecklist, pendingIds, topicKey, type ChecklistDecision } from "./checklist.js";
import { addTopics, effectiveTaxonomy, topicOfModulePath, type Taxonomy, type Topic } from "../toolkit/taxonomy.js";
import { axiomsProbeText, classifyTarget, detectToolkitIndexStep, realApplyDeps, type ApplyDeps, type GateStep } from "./gate.js";
import { applyMoveItem, planMove, verifyKeptMove, type MoveDecl, type MoveTarget } from "./move.js";
import {
  applyEdits,
  checklistPath,
  decisionsPath,
  entersBy,
  isMoveDecision,
  proposalBatchSchema,
  proposalDecisionKey,
  proposalDecisionRecordSchema,
  proposalDocstring,
  proposalLedgerPath,
  proposalsRunDir,
  type Decision,
  type DecisionKind,
  type DecisionsFile,
  type Proposal,
  type ProposalBatch,
  type ProposalDecisionRecord,
  type RoundBMove,
} from "./schema.js";
import { recordDecisions, statementStoreLockPath, statementStorePath } from "./statements.js";
import { healthRegressions, refreshToolkitGraph, toolkitHealth, type ToolkitGraph } from "./toolkit_graph.js";

/** The owner's decisions from the checklist of the batch's round; every item must be decided
 *  (`defer` is a decision). */
export async function readOwnerDecisions(cfg: ToolkitConfig, qid: string, batch: ProposalBatch, dryRun = false): Promise<Record<string, Decision>> {
  const cp = checklistPath(cfg, qid, dryRun, batch.round);
  if (!existsSync(cp)) throw new Error(`no checklist at ${cp}; re-render it with \`theoremchecker propose ${qid} --round ${batch.round}${dryRun ? " --dry-run" : ""}\``);
  const parsed: Record<string, ChecklistDecision> = parseChecklist(await readFile(cp, "utf8"), batch);
  const pending = pendingIds(parsed, batch);
  if (pending.length > 0) {
    throw new Error(
      `refusing --apply: ${pending.length} result(s) still pending (${pending.join(", ")}) in ${cp}. ` +
        "Decide every one (`defer` is a decision), then re-run.",
    );
  }
  return parsed as Record<string, Decision>;
}

export interface ApplyRoundBArgs {
  toolkit: ToolkitConfig;
  qid: string;
  batchFile: string;
  dryRun: boolean;
  log: (msg: string) => void;
  now?: () => Date;
  /** Gate commands and file IO (tests mock `run`). */
  deps?: ApplyDeps;
  /** Fresh scan of the paper (tests); default `obtainScan`. */
  scan?: () => Promise<CandidateScan>;
  toolsDir?: string;
  /** Toolkit-index gate step; `undefined` = detect from the lakefile. */
  indexStep?: GateStep | null;
  /** Run `fn` under the toolkit promotion lock (tests may pass an identity). */
  withLock?: <T>(fn: () => Promise<T>) => Promise<T>;
  /** The toolkit graph (tests); default: re-derived from the Lean. Null = no graph checks. */
  graph?: () => Promise<ToolkitGraph | null>;
  /** The study pipeline that builds a `generalize` entry (tests inject a fake). */
  runStudy?: typeof RunStudy;
  /** The corollary re-proof's agent and build (tests). */
  corollary?: Partial<CorollaryDeps>;
}

export interface ApplyRoundBResult {
  decisions: DecisionsFile;
  records: ProposalDecisionRecord[];
  /** Toolkit declarations the moves produced. */
  promoted: string[];
  moves: RoundBMove[];
  /** What the moves made worse in the toolkit graph (main view), in words; reported, not undone. */
  regressions: string[];
}

const LEAN_NAME_RE = /^[A-Za-z_][A-Za-z0-9_'!?]*(\.[A-Za-z_][A-Za-z0-9_'!?]*)*$/;
const nsOf = (n: string) => (n.includes(".") ? n.slice(0, n.lastIndexOf(".")) : "");
const leafOf = (n: string) => n.slice(n.lastIndexOf(".") + 1);

export function movesProgressPath(cfg: ToolkitConfig, qid: string): string {
  return path.join(proposalsRunDir(cfg, qid), "B.moves.json");
}
/** A move left as written after its gate failed, for the orchestrator: what the gate needs to run
 *  again on the repaired files (`runs/<slug>/proposals/move_pending.json`). */
export interface PendingMove {
  proposal_id: string;
  decls: MoveDecl[];
  target: Omit<MoveTarget, "existingText">;
  /** Headline declarations and their axioms before the move. */
  baseline: Array<[string, string[]]>;
  /** The statement hashes before the move (a file of `invariance.ts`), or null when not taken. */
  statements_before: string | null;
  /** The F4 targets current before the move. */
  cleared: string[];
  /** The gate step that failed. */
  failed: string;
}
export function pendingMovePath(cfg: ToolkitConfig, qid: string): string {
  return path.join(proposalsRunDir(cfg, qid), "move_pending.json");
}

/**
 * The statement hashes a pending move recorded before it wrote anything, or null when it took none.
 * They are what its gate compares with: a snapshot on record that is gone is a refusal, never a gate
 * run without the comparison.
 */
export function pendingMoveSnapshot(pend: PendingMove, where: { pendingFile: string; journal: string; voided: string }): Map<string, string> | null {
  if (!pend.statements_before) return null;
  const before = existsSync(pend.statements_before) ? parseFingerprints(readFileSync(pend.statements_before, "utf8")) : null;
  if (!before) {
    throw new Error(
      `${pend.proposal_id}: a move is pending (${where.pendingFile}) and the statement snapshot taken before it is missing or holds no statement hashes (${pend.statements_before}) — ` +
        `its gate cannot check that no statement changed. Put the file back (a re-proposed round keeps earlier files under ${where.voided}), ` +
        `or undo the move by hand (${where.journal} holds the original bytes), delete ${where.pendingFile} and apply again.`,
    );
  }
  return before;
}

export function moveJournalPath(cfg: ToolkitConfig, qid: string): string {
  return path.join(proposalsRunDir(cfg, qid), "move_journal.json");
}

function decisionLabel(d: Decision): string {
  return d.kind === "accept" ? "accepted" : "accepted-with-edits";
}

/** Accepted items first after the items they need (an accepted item whose declaration another
 *  accepted item's closure contains moves first, under its own proposal). */
export function orderByClosure(items: readonly Proposal[]): Proposal[] {
  const out: Proposal[] = [];
  const placed = new Set<string>();
  const visit = (p: Proposal, stack: Set<string>) => {
    if (placed.has(p.id) || stack.has(p.id)) return;
    stack.add(p.id);
    for (const dep of items) if (dep !== p && (p.moves_with ?? []).includes(dep.source.ref)) visit(dep, stack);
    placed.add(p.id);
    out.push(p);
  };
  for (const p of items) visit(p, new Set());
  return out;
}

/**
 * The topic tree against the owner's decisions: every accepted entry's target sits under a topic
 * of the tree or under a new topic the owner accepted. Returns the problems and the accepted new
 * topics (added to the tree before anything moves).
 */
export function topicDecisionProblems(
  cfg: Pick<ToolkitConfig, "lib" | "divisions">,
  batch: ProposalBatch,
  owner: Readonly<Record<string, Decision>>,
  taxonomy: Taxonomy,
): { problems: string[]; accepted: Topic[] } {
  const problems: string[] = [];
  const known = new Set(taxonomy.topics.map((t) => t.path));
  const accepted = newTopics(batch).filter((t) => owner[topicKey(t.path)]?.kind === "accept").map((t) => ({ path: t.path, scope: t.scope }));
  for (const t of accepted) known.add(t.path);
  for (const p of batch.proposals.filter((x) => x.verdict === "propose")) {
    const d = owner[p.id];
    if (!d || !isMoveDecision(d)) continue;
    const eff = applyEdits(p, d);
    const topic = topicOfModulePath(eff.target_module, cfg);
    if (topic === null) problems.push(`${p.id}: target_module ${eff.target_module} is not ${cfg.lib}/<Division>/<topic>/<File>.lean`);
    else if (!known.has(topic)) {
      problems.push(`${p.id}: its topic "${topic}" is not in the topic tree${p.new_topic?.path === topic ? " (you declined it)" : ""} — accept the topic, or decide accept_with_edits with a target_module under a listed topic`);
    }
  }
  return { problems, accepted };
}

/** Consistency of the owner's decisions (checked before anything is written). */
export function roundBDecisionProblems(proposals: readonly Proposal[], owner: Readonly<Record<string, Decision>>): string[] {
  const out: string[] = [];
  const byRef = new Map(proposals.map((p) => [p.source.ref, p] as const));
  for (const p of proposals) {
    const d = owner[p.id];
    if (!d || !isMoveDecision(d)) continue;
    if (p.source.is_paper_result && d.kind === "accept_with_edits" && d.edits.content !== undefined) {
      out.push(`${p.id}: one of the paper's stated results (${p.source.paper_env ?? p.source.ref}) keeps what it proves — accept_with_edits may change its placement and presentation, not content`);
    }
    const eff = applyEdits(p, d);
    if (!LEAN_NAME_RE.test(eff.proposed_name)) out.push(`${p.id}: proposed_name "${eff.proposed_name}" is not a Lean identifier`);
    // A general form is built from scratch: nothing of the paper moves with it.
    if (entersBy(p, d) === "generalize") continue;
    for (const m of p.moves_with ?? []) {
      const q = byRef.get(m);
      const dq = q ? owner[q.id] : undefined;
      if (q && dq && !isMoveDecision(dq)) out.push(`${p.id} is accepted but ${m}, which must move with it, is ${q.id} with decision ${dq.kind}; decide the two consistently`);
    }
  }
  return out;
}

async function listPaperFiles(dir: string): Promise<string[]> {
  const out: string[] = [];
  const walk = async (d: string): Promise<void> => {
    for (const e of await readdir(d, { withFileTypes: true }).catch(() => [])) {
      const abs = path.join(d, e.name);
      if (e.isDirectory()) { if (!(d === dir && e.name === PAPER_TMP_DIR)) await walk(abs); }
      else if (e.isFile() && e.name.endsWith(".lean")) out.push(abs);
    }
  };
  await walk(dir);
  return out.sort();
}

/** `#print axioms` of the headline declarations as the paper stands (the move gate's baseline). */
async function headlineBaseline(cfg: ToolkitConfig, paperModule: string, headlines: readonly string[], probe: string, d: ApplyDeps): Promise<Map<string, string[]>> {
  const out = new Map<string, string[]>();
  if (headlines.length === 0) return out;
  await d.writeFile(probe, axiomsProbeText([paperModule], headlines));
  const r = await d.run(`lake env lean ${probe.split(path.sep).join("/")}`, cfg.toolkitRoot);
  const report = parseAxiomReport(r.log, [...headlines]);
  const bad = Object.entries(report).filter(([, v]) => v.error);
  if (r.code !== 0 || bad.length) {
    throw new Error(`cannot take the headline \`#print axioms\` baseline before moving (${bad.map(([k, v]) => `${k}: ${v.error}`).join("; ") || `exit ${r.code}`}); does the paper build?\n${r.log.split("\n").slice(-20).join("\n")}`);
  }
  for (const [k, v] of Object.entries(report)) out.set(k, v.axioms);
  return out;
}

export async function applyRoundB(args: ApplyRoundBArgs): Promise<ApplyRoundBResult> {
  const { toolkit: cfg, qid, log, dryRun } = args;
  const d = args.deps ?? realApplyDeps;
  const now = args.now ?? (() => new Date());
  const batch = proposalBatchSchema.parse(JSON.parse(await readFile(args.batchFile, "utf8")));
  const owner = await readOwnerDecisions(cfg, qid, batch, dryRun);
  const proposed = batch.proposals.filter((p) => p.verdict === "propose");
  const topics = topicDecisionProblems(cfg, batch, owner, await effectiveTaxonomy(cfg));
  const problems = [...roundBDecisionProblems(proposed, owner), ...topics.problems];
  if (problems.length) throw new Error(`refusing --apply:\n  ${problems.join("\n  ")}`);
  if (!dryRun && topics.accepted.length) {
    await addTopics(cfg, topics.accepted);
    log(`topic tree: added ${topics.accepted.map((t) => t.path).join(", ")}`);
  }
  const decidedAt = now().toISOString();
  const decisions: DecisionsFile = { slug: qid, round: "B", decisions: owner, decided_at: decidedAt };
  await writeJsonAtomic(decisionsPath(cfg, qid), decisions);

  const ledgerFile = proposalLedgerPath(cfg, qid, dryRun);
  const baseRecord = (p: Proposal, dec: Decision) => ({
    kind: "proposal_decision" as const, slug: qid, round: "B" as const, proposal_id: p.id, decision: dec, proposal: p,
    decided_at: decidedAt, batch_created: batch.created,
    promoted: [] as string[], ...(dryRun ? { dry_run: true } : {}),
  });
  // Items a previous (interrupted or failed) apply already carried out.
  const done = new Set(
    (await loadLedger(ledgerFile)).decisions.map((r) => proposalDecisionRecordSchema.safeParse(r))
      .filter((r) => r.success && r.data.slug === qid && r.data.round === "B" && r.data.batch_created === batch.created)
      .map((r) => r.data!.proposal_id),
  );
  const moves: RoundBMove[] = existsSync(movesProgressPath(cfg, qid)) && !dryRun
    ? (JSON.parse(await readFile(movesProgressPath(cfg, qid), "utf8")) as RoundBMove[]).filter((m) => done.has(m.proposal_id))
    : [];
  const records: ProposalDecisionRecord[] = [];
  const recordNow = async (rec: ProposalDecisionRecord) => {
    records.push(rec);
    await appendDecisionRecords(ledgerFile, [rec], proposalDecisionKey);
  };

  const accepted = orderByClosure(proposed.filter((p) => isMoveDecision(owner[p.id]!) && !done.has(p.id)));
  // Moved as proved, or built in general form (the paper's result then becomes its corollary).
  const build = accepted.filter((p) => entersBy(p, owner[p.id]!) === "move");
  const generalize = accepted.filter((p) => entersBy(p, owner[p.id]!) === "generalize");
  let regressions: string[] = [];
  if (dryRun) {
    for (const p of build) {
      const eff = applyEdits(p, owner[p.id]!);
      log(`[dry-run] ${p.id}: ${owner[p.id]!.kind} — a live apply would move \`${p.source.ref}\`${p.moves_with?.length ? ` (+ ${p.moves_with.join(", ")})` : ""} to \`${eff.proposed_name}\` in ${eff.target_module}; nothing moved`);
      await recordNow(baseRecord(p, owner[p.id]!));
    }
  } else if (build.length > 0) {
    const state = await loadState(cfg.toolkitRoot, qid);
    const paperModule = leanModulePrefix(state.lean_subdir);
    const leanDir = leanTheoremDir(cfg.toolkitRoot, state.lean_subdir);
    const toolsDir = args.toolsDir ?? theoremCheckerToolsDir();
    const indexStep = args.indexStep !== undefined ? args.indexStep : await detectToolkitIndexStep(cfg, d);
    const withLock = args.withLock ?? (<T,>(fn: () => Promise<T>) => withPromotionLock(cfg.toolkitRoot, fn, cfg.lockPath));
    const journal = moveJournalPath(cfg, qid);
    const pendingFile = pendingMovePath(cfg, qid);
    const probe = path.join(proposalsRunDir(cfg, qid), "move_axioms.lean");
    await mkdir(path.dirname(probe), { recursive: true });
    const fpDir = proposalsRunDir(cfg, qid);
    const fpAfterFile = (id: string) => path.join(fpDir, `statements_after_${id}.json`);
    // What a move that passed its gate leaves behind: the run's records, and its receipts carried.
    const completeMove = async (p: Proposal, dec: Decision, decls: readonly MoveDecl[], module: string, cleared: readonly string[], checked: boolean) => {
      const repointed = await repointMovedResults(cfg, qid, decls);
      if (repointed.length) log(`${p.id}: crosswalk / report now point ${repointed.join(", ")} at the toolkit`);
      moves.push({ proposal_id: p.id, decision: dec.kind, module, decls: decls.map((x) => ({ from: x.from, to: x.to })) });
      await writeJsonAtomic(movesProgressPath(cfg, qid), moves);
      await recordNow({ ...baseRecord(p, dec), promoted: decls.map((x) => x.to) });
      const carried = await carryReceipts(cfg, qid, leanDir, cleared, fpAfterFile(p.id)).catch(() => 0);
      log(`${p.id}: moved and gated (${decls.length} declaration(s))${checked ? `; every statement unchanged${carried ? `, ${carried} F4 receipt(s) carried over` : ""}` : ""}`);
    };
    const invarianceOf = (id: string, fpBefore: ReadonlyMap<string, string>, movedNames: readonly { from: string; to: string }[]) => {
      const fpAfter = fpAfterFile(id);
      return {
        cmd: fingerprintScanCmd(cfg, paperModule, fpAfter),
        check: (): string | null => {
          const after = existsSync(fpAfter) ? parseFingerprints(readFileSync(fpAfter, "utf8")) : null;
          return after ? statementInvarianceFailure(fpBefore, after, movedNames) : "the scan after the move reported no statement hashes";
        },
      };
    };
    const escalation = (id: string, logFile: string, tail: string) =>
      `${id}: the move did not pass its gate and nothing was restored — every file is as the move wrote it (log: ${logFile}):\n${tail}\n` +
        `This is the orchestrator's to settle. Repair the Lean by hand (the target toolkit module, the paper files that used the result), then re-run ` +
        `\`theoremchecker propose ${qid} --round B --apply\`: it runs the gate again on the files as they stand and goes on with the rest. ` +
        `To give the move up instead, put back by hand the files it wrote (${journal} holds each one's original bytes), delete that journal and ${pendingFile}, and change the entry's decision. ` +
        `Items applied before it stay applied and recorded.`;
    // A move a previous apply left as written: the gate again, on the files as they stand.
    let settled: string | null = null;
    if (existsSync(pendingFile)) {
      const pend = JSON.parse(await readFile(pendingFile, "utf8")) as PendingMove;
      const p = build.find((x) => x.id === pend.proposal_id);
      if (!p) throw new Error(`${pend.proposal_id}: a move is pending (${pendingFile}) but its entry is no longer accepted as a move; undo it by hand (${journal} holds the original bytes) and delete ${pendingFile}`);
      const fpBefore = pendingMoveSnapshot(pend, { pendingFile, journal, voided: path.join(fpDir, "voided") });
      const movedNames = pend.decls.map((x) => ({ from: x.from, to: x.to }));
      log(`${p.id}: a move left as written after its gate failed (${pend.failed}) — running the gate on the files as they stand`);
      const indexStep0 = args.indexStep !== undefined ? args.indexStep : await detectToolkitIndexStep(cfg, d);
      const res = await withLock<{ ok: boolean; log: string; timedOut?: boolean }>(() => verifyKeptMove({
        cfg, toolsDir, proposalId: p.id, paperModule, target: { ...pend.target, existingText: null }, decls: pend.decls,
        headlineBaseline: new Map(pend.baseline), probeFile: probe, indexStep: indexStep0, journalFile: journal,
        ...(fpBefore ? { invariance: invarianceOf(p.id, fpBefore, movedNames) } : {}),
      }, d));
      const logFile = path.join(fpDir, `move_${p.id}.log`);
      await writeFile(logFile, res.log, "utf8");
      if (!res.ok) throw new Error(escalation(p.id, logFile, res.log.split("\n").slice(-25).join("\n")));
      await completeMove(p, owner[p.id]!, pend.decls, pend.target.module, pend.cleared, fpBefore !== null);
      await d.removeFile(pendingFile);
      settled = p.id;
    }
    if (settled) build.splice(build.findIndex((x) => x.id === settled), 1);

    // Re-scan: the batch must still describe the paper.
    const scan = args.scan ? await args.scan() : await obtainScan({ toolkit: cfg, qid, leanSubdir: state.lean_subdir, log });
    const fresh = filterCandidates(scan, await paperObjects(cfg, qid));
    const freshByName = new Map(fresh.candidates.map((c) => [c.name, c] as const));
    const alreadyMoved = new Map<string, { to: string; module: string }>(moves.flatMap((m) => m.decls.map((x) => [x.from, { to: x.to, module: m.module }] as const)));
    // The toolkit graph before the moves: a statement the toolkit already states is not moved twice.
    const graphOf = args.graph ?? (() => refreshToolkitGraph({ toolkit: cfg, log }));
    const before = await graphOf().catch((err: unknown) => {
      log(`promotion: toolkit graph not built (${err instanceof Error ? err.message : String(err)}); moving without the graph checks`);
      return null;
    });
    if (before) {
      const hashes = new Map(before.nodes.filter((n) => n.layer === "toolkit" && n.statement_hash).map((n) => [n.statement_hash!, n.id] as const));
      const own = new Map(before.nodes.filter((n) => n.layer === "paper").map((n) => [n.id, n.statement_hash] as const));
      for (const p of build) {
        const h = own.get(p.source.ref);
        const dup = h ? hashes.get(h) : undefined;
        if (dup) throw new Error(`${p.id}: the toolkit already states ${p.source.ref} as \`${dup}\`; decline it (the paper can use \`${dup}\`), then re-run`);
      }
    }
    for (const p of build) {
      const c = freshByName.get(p.source.ref);
      if (!c) throw new Error(`${p.id}: ${p.source.ref} is no longer a clean round-B candidate in the paper as it stands; re-propose with \`theoremchecker verify … --from-stage V6\``);
      // A result stated over the paper's own setting never moves into the toolkit as is.
      const shaped = paperShapedReasons(c, scan);
      if (shaped.length) {
        throw new Error(`${p.id}: ${p.source.ref} is stated over the paper's own setting (${shaped.join("; ")}); it cannot move as is — decide \`generalize_first\` (its general form is built and the paper's result becomes its corollary), then re-run`);
      }
      const want = [...(p.moves_with ?? [])].filter((n) => !alreadyMoved.has(n)).sort().join(",");
      const have = [...c.moves_with].sort().join(",");
      if (want !== have) {
        throw new Error(`${p.id}: what must move with ${p.source.ref} changed since the round was proposed ([${want}] → [${have}]); re-propose with \`--from-stage V6\``);
      }
    }
    // The name each accepted result takes must be free and follow the type it is about.
    const names = await indexNameTable(cfg);
    const declared = (await loadLedger(ledgerFile)).declarations;
    for (const p of build) {
      const name = applyEdits(p, owner[p.id]!).proposed_name;
      if (builtByOwnStudy(declared, qid, p, name)) continue;
      const problems = nameProblems(name, names);
      if (problems.length) throw new Error(`${p.id}: ${problems.join("; ")} — decide accept_with_edits with a proposed_name that fixes it, then re-run`);
    }
    const headlines = await reportHeadlineDecls(cfg, qid);
    const baseline = await headlineBaseline(cfg, paperModule, headlines, probe, d);
    log(`promotion: headline \`#print axioms\` baseline taken for ${baseline.size} declaration(s)`);
    const byName = new Map(scan.declarations.map((x) => [x.name, x] as const));

    for (const p of build) {
      const dec = owner[p.id]!;
      const eff = applyEdits(p, dec);
      const placement = classifyTarget(eff.target_module, cfg);
      if (placement.division !== eff.division) throw new Error(`${p.id}: target_module ${eff.target_module} is not in division ${eff.division}`);
      const closure = (freshByName.get(p.source.ref)?.moves_with ?? []).filter((n) => !alreadyMoved.has(n));
      const ns = nsOf(eff.proposed_name);
      const decls: MoveDecl[] = [
        ...closure.map((n) => ({ from: n, to: ns ? `${ns}.${leafOf(n)}` : leafOf(n), kind: byName.get(n)?.kind ?? "theorem" })),
        { from: p.source.ref, to: eff.proposed_name, kind: byName.get(p.source.ref)?.kind ?? "theorem" },
      ];
      const targetAbs = path.join(cfg.toolkitRoot, ...eff.target_module.split("/"));
      const target: MoveTarget = {
        rel: eff.target_module, module: placement.module, division: placement.division,
        overview: eff.new_module_overview ?? `${eff.division} results proved in verified papers.`,
        existingText: (await d.exists(targetAbs)) ? await d.readFile(targetAbs) : null,
      };
      const files = await listPaperFiles(leanDir);
      const paperFiles = new Map<string, string>();
      for (const f of files) paperFiles.set(f, await d.readFile(f));
      const toolkitModulesUsed = [...new Set(decls.flatMap((x) => {
        const s = byName.get(x.from);
        return s ? [...s.type_constants, ...s.body_constants].filter((c) => c.class === "toolkit").map((c) => c.module) : [];
      }))];
      // The target imports what the moved declarations use; the source files' imports only as the
      // fallback when that minimal header does not build.
      const movedNames = new Set(decls.map((x) => x.from));
      const usedConstants = [...new Map(decls.flatMap((x) => {
        const s = byName.get(x.from);
        return s ? [...s.type_constants, ...s.body_constants].filter((c) => (c.class === "base" || c.class === "toolkit") && !movedNames.has(c.name)) : [];
      }).map((c) => [c.name, { name: c.name, module: c.module }] as const)).values()];
      const planFor = (importMode: "minimal" | "source") => planMove({
        cfg, paperFiles, decls, mainFrom: p.source.ref,
        docstringOverride: dec.kind === "accept_with_edits" && (dec.edits.title || dec.edits.content || dec.edits.reference) ? proposalDocstring(eff) : null,
        fallbackDocstring: proposalDocstring(eff),
        target, alreadyMoved, toolkitModulesUsed, usedConstants, importMode,
        readModule: (m) => paperFiles.get(path.join(cfg.toolkitRoot, ...m.split(".")) + ".lean") ?? null,
      });
      const plan = planFor("minimal");
      const alsoIn = [...new Set((p.recurrence ?? []).filter((r) => r.kind === "identical").map((r) => r.slug))];
      const date = now().toISOString().slice(0, 10);
      // The main result and its closure: one main node, the rest auxiliaries it owns.
      const ledgerEntries: LedgerDeclaration[] = decls.map((x) => ({
        name: x.to, module: placement.module, division: placement.division,
        origin: { kind: "proposal", slug: qid, round: "B", proposal_id: p.id, run_id: qid },
        date, decision: decisionLabel(dec), nearest_existing: eff.nearest_existing.map((n) => n.name), used_by: [qid],
        moved_from: x.from,
        ...(x.from === p.source.ref
          ? { tier: "main", title: eff.title, ...(alsoIn.length ? { also_in: alsoIn } : {}) }
          : { tier: "aux", owners: [eff.proposed_name] }),
      }));
      // Paper results moving now leave the paper: the headline gate compares what remains.
      const itemBaseline = new Map([...baseline].filter(([h]) => !decls.some((x) => sameDecl(h, x.from))));
      log(`${p.id}: moving ${decls.map((x) => (x.from === x.to ? x.to : `${x.from} → ${x.to}`)).join(", ")} into ${placement.module}${target.existingText === null ? " (new module)" : ""}`);
      // What every declaration of the paper and the toolkit states now, under the names this move
      // gives: the gate requires the same after it. The run's current F4 receipts are carried over.
      const movedNames_ = decls.map((x) => ({ from: x.from, to: x.to }));
      const fpBeforeFile = path.join(fpDir, `statements_before_${p.id}.json`);
      const fpBefore = await withLock(() => takeFingerprints(d, cfg, paperModule, fpBeforeFile, movedNames_));
      if (!fpBefore) log(`${p.id}: statement invariance not checked — the scan reported no statement hashes (update the toolkit's CandidateScan.lean from the template)`);
      const invariance = fpBefore ? invarianceOf(p.id, fpBefore, movedNames_) : undefined;
      const cleared = fpBefore ? await receiptsBefore(cfg, qid, leanDir, fpBeforeFile) : [];
      const attempt = (pl: ReturnType<typeof planMove>) => withLock(() => applyMoveItem({
        cfg, toolsDir, slug: qid, proposalId: p.id, paperModule, plan: pl, target, decls, headlineBaseline: itemBaseline,
        ledgerEntries, journalFile: journal, probeFile: probe, indexStep, now: now(), ...(invariance ? { invariance } : {}),
      }, d));
      // On record before the first write: an apply that dies part-way leaves a move to settle, too.
      const pend: PendingMove = {
        proposal_id: p.id, decls,
        target: { rel: target.rel, module: target.module, division: target.division, overview: target.overview },
        baseline: [...itemBaseline].map(([h, ax]) => [h, [...ax]]),
        statements_before: fpBefore ? fpBeforeFile : null, cleared: [...cleared], failed: "the apply was interrupted",
      };
      await writeJsonAtomic(pendingFile, pend);
      let res = await attempt(plan);
      if (!res.ok && !res.timedOut) {
        // Once more with the source files' imports (a tactic no used constant brings in), written over the first.
        log(`${p.id}: the minimal header (${plan.importsAdded.length} import(s) of what the declarations use) did not pass the gate; retrying with the source files' imports`);
        const first = res.log;
        res = await attempt(planFor("source"));
        res = { ...res, log: `${first}\n\n--- retry with the source files' imports ---\n${res.log}` };
      }
      const logFile = path.join(fpDir, `move_${p.id}.log`);
      await writeFile(logFile, res.log, "utf8");
      if (!res.ok) {
        const tail = res.log.split("\n").slice(-25).join("\n");
        if (!res.kept) {
          await d.removeFile(pendingFile);
          throw new Error(`${p.id}: the move could not be written (log: ${logFile}):\n${tail}\nNothing was written. Items applied before it stay applied and recorded.`);
        }
        await writeJsonAtomic(pendingFile, { ...pend, failed: (/gate step '([^']+)'/.exec(res.log.split("\n").slice(-3).join("\n")) ?? [])[1] ?? "apply error" });
        throw new Error(escalation(p.id, logFile, tail));
      }
      for (const x of decls) alreadyMoved.set(x.from, { to: x.to, module: placement.module });
      for (const h of [...baseline.keys()]) if (!itemBaseline.has(h)) baseline.delete(h);
      // The move is on record before its pending marker goes (as a settled pending move is): an
      // apply that dies between the two leaves a move to settle, never one that was applied and lost.
      await completeMove(p, dec, decls, placement.module, cleared, fpBefore !== null);
      await d.removeFile(pendingFile);
    }
    // The toolkit graph after the moves: what they made worse is reported to the owner.
    const after = before ? await graphOf().catch(() => null) : null;
    if (before && after) {
      regressions = healthRegressions(toolkitHealth(before), toolkitHealth(after), moves.flatMap((m) => m.decls.map((x) => x.to)));
      for (const r of regressions) log(`toolkit graph: ${r}`);
    }
  }

  // Built in general form by the study pipeline; the paper's result is re-proved as its corollary.
  if (generalize.length > 0) {
    const runStudy = args.runStudy ?? (await import("../substrate/pipeline.js")).runSubstratePipeline;
    const graphOf = args.graph ?? (() => refreshToolkitGraph({ toolkit: cfg, log }));
    const before = dryRun ? null : await graphOf().catch(() => null);
    const files = existsSync(candidatesPath(cfg, qid))
      ? new Map((JSON.parse(await readFile(candidatesPath(cfg, qid), "utf8")) as CandidatesFile).candidates.map((c) => [c.name, c.file] as const))
      : new Map<string, string>();
    const built: string[] = [];
    for (const p of generalize) {
      const dec = owner[p.id]!;
      const eff = { ...applyEdits(p, dec), path: "generalize" as const };
      const b = await buildProposal({
        toolkit: cfg, qid, p: eff, decision: dec, dryRun, runStudy, log,
        ...(p.lean_type ? { instance: { decl: p.source.ref, lean_type: p.lean_type } } : {}),
      });
      built.push(...b.promoted);
      let corollary: boolean | undefined;
      const file = files.get(p.source.ref);
      if (!dryRun && b.main && file) {
        // The re-proof may change the proof of that one result and nothing any declaration states.
        const state = await loadState(cfg.toolkitRoot, qid);
        const paperModule = leanModulePrefix(state.lean_subdir);
        const leanDir = leanTheoremDir(cfg.toolkitRoot, state.lean_subdir);
        const fpDir = proposalsRunDir(cfg, qid);
        const fpFile = (when: "before" | "after") => path.join(fpDir, `statements_${when}_${p.id}.json`);
        const fpBefore = args.corollary ? null : await takeFingerprints(d, cfg, paperModule, fpFile("before"));
        const cleared = fpBefore ? await receiptsBefore(cfg, qid, leanDir, fpFile("before")) : [];
        corollary = (await reproveAsCorollary({
          toolkit: cfg, qid, proposalId: p.id, decl: p.source.ref, file: path.join(cfg.toolkitRoot, file), general: b.main, log,
          ...(args.corollary ? { deps: args.corollary } : {}),
          ...(fpBefore ? {
            verify: async () => {
              const after = await takeFingerprints(d, cfg, paperModule, fpFile("after"));
              return after ? statementInvarianceFailure(fpBefore, after) : "the scan after the re-proof reported no statement hashes";
            },
          } : {}),
        })).ok;
        if (corollary && fpBefore) {
          const carried = await carryReceipts(cfg, qid, leanDir, cleared, fpFile("after")).catch(() => 0);
          log(`${p.id}: every statement unchanged${carried ? `; ${carried} F4 receipt(s) carried over` : ""}`);
        }
      } else if (!dryRun) {
        log(`${p.id}: ${b.main ? `no source file on record for ${p.source.ref}` : "the study recorded no main declaration"}; the paper keeps its own proof`);
      }
      await recordNow({ ...baseRecord(p, dec), promoted: b.promoted, study_run: b.studyRun, ...(corollary !== undefined ? { corollary } : {}) });
      // One general version serves every paper that proved it: the entries deferred before are covered.
      if (b.main && !dryRun) {
        for (const e of p.deferred_before ?? []) {
          await appendDecisionRecords(ledgerFile, [{
            kind: "proposal_decision", slug: e.slug, round: "B", proposal_id: e.proposal_id,
            decision: { kind: "covered", note: `built in general form as ${b.main.name} from ${qid} (${p.id}); that paper keeps its own proof` },
            proposal: { proposed_name: b.main.name, division: eff.division, target_module: eff.target_module }, decided_at: decidedAt, batch_created: batch.created, promoted: [],
          }], proposalDecisionKey);
          log(`${p.id}: covers ${e.slug}'s deferred ${e.proposal_id} (built once for both)`);
        }
      }
    }
    const after = before ? await graphOf().catch(() => null) : null;
    if (before && after) {
      const more = healthRegressions(toolkitHealth(before), toolkitHealth(after), built);
      for (const r of more) log(`toolkit graph: ${r}`);
      regressions = [...regressions, ...more];
    }
  }

  // Declined / deferred items, and those declined automatically as already available: recorded only.
  for (const p of proposed.filter((x) => !isMoveDecision(owner[x.id]!) && !done.has(x.id))) {
    log(`${p.id} (${p.source.ref}): ${owner[p.id]!.kind} — stays in the paper`);
    records.push(baseRecord(p, owner[p.id]!));
  }
  for (const p of batch.proposals.filter((x) => x.duplicate_of && !done.has(x.id))) {
    records.push(baseRecord(p, { kind: "decline", note: `already available as ${p.duplicate_of}` }));
  }
  const { added, skipped } = await appendDecisionRecords(ledgerFile, records, proposalDecisionKey);
  log(`ledger: ${added.length} decision record(s) appended${skipped.length ? `, ${skipped.length} already recorded` : ""} → ${ledgerFile}`);
  await recordDecisions(statementStorePath(cfg, qid, dryRun), qid, new Map(proposed.map((p) => [p.id, owner[p.id]!.kind as DecisionKind] as const)), statementStoreLockPath(cfg, qid, dryRun));
  if (!dryRun) await writeReportToolkitSection(path.join(cfg.runsDir, qid), await loadRunReuse(path.join(cfg.runsDir, qid)), moves);
  return { decisions, records, promoted: [...moves.flatMap((m) => m.decls.map((x) => x.to)), ...records.filter((r) => generalize.some((p) => p.id === r.proposal_id)).flatMap((r) => r.promoted)], moves, regressions };
}

// ─── paper results moved to the toolkit ──────────────────────────────────────

/** Whether two declaration names denote the same declaration (exact, or one is a namespace-relative
 *  suffix of the other, as crosswalk anchors may be). */
function sameDecl(a: string, b: string): boolean {
  return a === b || a.endsWith(`.${b}`) || b.endsWith(`.${a}`);
}

const TOOLKIT_SECTION_START = "<!-- toolkit:start -->";

/**
 * Re-point the paper results among `moved` at their toolkit declarations: each crosswalk
 * (`crosswalk_full.json`) entry and V6 report row anchored to a moved declaration gets the toolkit
 * name, `moved_to_toolkit: true` and `moved_from`; in `report.md` (outside the Toolkit section) the
 * old name gains a "(moved to `<new>`)" note, so the report keeps the result as verified. Returns the
 * re-pointed paper statement ids.
 */
export async function repointMovedResults(cfg: ToolkitConfig, qid: string, moved: ReadonlyArray<{ from: string; to: string }>): Promise<string[]> {
  const ids = new Set<string>();
  type Row = { obj_id?: string; node_id?: string; lean?: { decl?: string } | null; moved_to_toolkit?: boolean; moved_from?: string };
  const repoint = (row: Row): boolean => {
    const m = row.lean?.decl && !row.moved_to_toolkit ? moved.find((x) => sameDecl(row.lean!.decl!, x.from)) : undefined;
    if (!m) return false;
    row.moved_from = row.lean!.decl!;
    row.lean!.decl = m.to;
    row.moved_to_toolkit = true;
    ids.add(row.obj_id ?? row.node_id ?? m.from);
    return true;
  };
  const cw = crosswalkFullJsonPath(cfg.toolkitRoot, qid);
  if (existsSync(cw)) {
    const rows = JSON.parse(await readFile(cw, "utf8")) as Row[];
    if (rows.map(repoint).some(Boolean)) await writeJsonAtomic(cw, rows);
  }
  const runDir = path.join(cfg.runsDir, qid);
  const rj = path.join(runDir, VERIFY_FILES.reportJson);
  const notes: Array<{ from: string; to: string }> = [];
  if (existsSync(rj)) {
    const obj = JSON.parse(await readFile(rj, "utf8")) as { results?: Row[] };
    let changed = false;
    for (const r of obj.results ?? []) if (repoint(r)) { changed = true; notes.push({ from: r.moved_from!, to: r.lean!.decl! }); }
    if (changed) await writeJsonAtomic(rj, obj);
  }
  const rm = path.join(runDir, VERIFY_FILES.reportMd);
  if (notes.length && existsSync(rm)) {
    const text = await readFile(rm, "utf8");
    const cut = text.includes(TOOLKIT_SECTION_START) ? text.indexOf(TOOLKIT_SECTION_START) : text.length;
    let head = text.slice(0, cut);
    for (const n of notes) {
      const tick = `\`${n.from}\``;
      head = head.split(tick).join(`${tick} (moved to \`${n.to}\`)`);
    }
    if (head !== text.slice(0, cut)) await writeFile(rm, head + text.slice(cut), "utf8");
  }
  return [...ids].sort();
}
