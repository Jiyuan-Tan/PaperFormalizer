// Round B apply: carry out the owner's decisions on the proposed main results.
//
//   accept / accept_with_edits  MOVE the result and its closure (`moves_with`: the helper lemmas
//                               and definitions it needs) out of the paper into the target toolkit
//                               module (`move.ts`). The run's moves are prepared in a private
//                               workspace and committed (`local_moves.ts`): written and gated there
//                               as one batch — `lake build <lib>`, `lake build <paper>`, `#print
//                               axioms` (moved declarations clean, the paper's headline results
//                               unchanged), the layout lints, statement invariance and the toolkit
//                               index — then one at a time after a batch that does not pass,
//                               stopping at the first that fails; what passed is committed to the
//                               shared toolkit (`shared/commit.ts`). A move that fails its gate
//                               reaches nothing of the shared toolkit and is escalated. The result
//                               is recorded `tier: main`, its closure `tier: aux` owned by it.
//   decline / defer             recorded only (with the items declined automatically as already
//                               available).
//
// A run that died after its commit records its moves at its next apply (its landed records). A
// gate builds the toolkit and the moving paper only; the whole library is built by the daily
// library check (`libraryCheck`), never by an apply. Before any write the paper is re-scanned: an
// accepted item that is no longer a clean candidate, or whose closure changed, refuses the apply
// (re-propose with `--from-stage V6`). Around the moves the toolkit graph is re-derived in the
// workspace: before, a duplicate of a toolkit result refuses its item; after, what the moves made
// worse (a result used by nothing, a module falling apart) is reported — never undone. A dry run
// records decisions (in its own ledger) and describes the moves; it never touches Lean.
import { execFile } from "node:child_process";
import { existsSync } from "node:fs";
import { appendFile, mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { crosswalkFullJsonPath, leanModulePrefix, leanTheoremDir, PAPER_TMP_DIR } from "../paths.js";
import { withPromotionLock } from "../shared/build_mutex.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import { loadState } from "../state.js";
import { paperFormalizerToolsDir, type ToolkitConfig } from "../toolkit/config.js";
import { declaredNames } from "../toolkit/lean_source.js";
import { appendDecisionRecords, loadLedger, type LedgerDeclaration } from "../toolkit/ledger.js";
import { parseAxiomReport } from "../verify/lean_evidence.js";
import { writeReportToolkitSection, loadRunReuse } from "../verify/report_toolkit.js";
import { VERIFY_FILES } from "../verify/types.js";
import { buildProposal, builtByOwnStudy, type CorollaryDeps } from "./build.js";
import { indexNameTable, nameProblems } from "./curator.js";
import { carryReceipts } from "./invariance.js";
import { candidatesPath, filterCandidates, obtainScan, paperObjects, paperShapedReasons, reportHeadlineDecls, type CandidateScan, type CandidatesFile } from "./candidate_scan.js";
import type { runSubstratePipeline as RunStudy } from "../substrate/pipeline.js";
import { newTopics, parseChecklist, pendingIds, topicKey, type ChecklistDecision } from "./checklist.js";
import { addTopics, effectiveTaxonomy, topicOfModulePath, type Taxonomy, type Topic } from "../toolkit/taxonomy.js";
import { axiomsProbeText, classifyTarget, detectToolkitIndexStep, realApplyDeps, type ApplyDeps, type GateStep } from "./gate.js";
import { findImporters, NO_IMPORTERS } from "./importers.js";
import { commitOnFile, honourCommit } from "../shared/commit.js";
import { landedRecords, localCommitMoves, localCorollary, type LocalLanded, type MoveSpec } from "./local_moves.js";
import { failingModules, killedModules, type BatchRecord, type MoveDecl, type MoveTarget } from "./move.js";
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
  if (!existsSync(cp)) throw new Error(`no checklist at ${cp}; re-render it with \`paperformalizer propose ${qid} --round ${batch.round}${dryRun ? " --dry-run" : ""}\``);
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
  /** The toolkit graph (tests); default: re-derived from the Lean. Null = no graph checks. */
  graph?: () => Promise<ToolkitGraph | null>;
  /** The study pipeline that builds a `generalize` entry (tests inject a fake). */
  runStudy?: typeof RunStudy;
  /** The corollary re-proof's agent and build (tests). */
  corollary?: Partial<CorollaryDeps>;
  /** The toolkit graph of the toolkit and this paper in the promotion's workspace (`local_moves.ts`;
   *  tests); default re-derived there, or `graph` when given. */
  graphIn?: (cfgP: ToolkitConfig) => Promise<ToolkitGraph | null>;
}

export interface ApplyRoundBResult {
  decisions: DecisionsFile;
  records: ProposalDecisionRecord[];
  /** Toolkit declarations the moves produced. */
  promoted: string[];
  moves: RoundBMove[];
  /** What the moves made worse in the toolkit graph (main view), in words; reported, not undone. */
  regressions: string[];
  // compat 2026-11-11: remove after the processes started before this merge have exited (≤2 days)
  // (a `cli.ts` loaded before the merge reads them: always empty — the library check is the daily one's)
  libraryBreaks: string[];
  libraryBreaksMaybeOlder: boolean;
}

const LEAN_NAME_RE = /^[A-Za-z_][A-Za-z0-9_'!?]*(\.[A-Za-z_][A-Za-z0-9_'!?]*)*$/;
const nsOf = (n: string) => (n.includes(".") ? n.slice(0, n.lastIndexOf(".")) : "");
const leafOf = (n: string) => n.slice(n.lastIndexOf(".") + 1);

export function movesProgressPath(cfg: ToolkitConfig, qid: string): string {
  return path.join(proposalsRunDir(cfg, qid), "B.moves.json");
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

/** `#print axioms` of the headline declarations as the paper stands (the move gate's baseline),
 *  taken in the promotion's workspace (`cfg` rebased to it; the probe imports the paper alone). */
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
    // Prepared in a private workspace and committed briefly (`local_moves.ts`).
    log("promotion: the moves are prepared in a workspace of their own and committed");
    const state = await loadState(cfg.toolkitRoot, qid);
    const paperModule = leanModulePrefix(state.lean_subdir);
    const leanDir = leanTheoremDir(cfg.toolkitRoot, state.lean_subdir);
    const toolsDir = args.toolsDir ?? paperFormalizerToolsDir();
    const indexStep = args.indexStep !== undefined ? args.indexStep : await detectToolkitIndexStep(cfg, d);
    const fpDir = proposalsRunDir(cfg, qid);
    await mkdir(fpDir, { recursive: true });
    const fpAfterFile = (id: string) => path.join(fpDir, `statements_after_${id}.json`);
    // What a move that passed its gate leaves behind: the run's records, and its receipts carried.
    const completeMove = async (p: Proposal, dec: Decision, decls: ReadonlyArray<{ from: string; to: string }>, module: string, cleared: readonly string[], checked: boolean, afterFile = fpAfterFile(p.id)) => {
      const repointed = await repointMovedResults(cfg, qid, decls);
      if (repointed.length) log(`${p.id}: crosswalk / report now point ${repointed.join(", ")} at the toolkit`);
      moves.push({ proposal_id: p.id, decision: dec.kind, module, decls: decls.map((x) => ({ from: x.from, to: x.to })) });
      await writeJsonAtomic(movesProgressPath(cfg, qid), moves);
      await recordNow({ ...baseRecord(p, dec), promoted: decls.map((x) => x.to) });
      const carried = await carryReceipts(cfg, qid, leanDir, cleared, afterFile).catch(() => 0);
      log(`${p.id}: moved and gated (${decls.length} declaration(s))${checked ? `; every statement unchanged${carried ? `, ${carried} F4 receipt(s) carried over` : ""}` : ""}`);
    };
    // The moves of a passed batch, recorded (`file`: the landed record they came from).
    const recordLanded = async (file: string, rec: BatchRecord, fresh = false) => {
      for (const m of rec.moves.filter((x) => x.slug === qid)) {
        if (done.has(m.proposal_id)) continue;
        const p = build.find((x) => x.id === m.proposal_id);
        if (!p) throw new Error(`${m.proposal_id}: its batch passed the gate (${file}), but its entry is no longer accepted as a move; record or undo it by hand (the batch's log is move_batch.log beside it) and delete ${path.basename(file)}`);
        log(fresh ? `${p.id}: committed — recording it` : `${p.id}: its batch passed the gate before the last apply ended — recording it`);
        await completeMove(p, owner[p.id]!, m.decls, m.module, m.cleared ?? [], m.checked ?? rec.checked, fpAfterFile("batch"));
        build.splice(build.indexOf(p), 1);
      }
    };
    // What a commit of this run's moves landed (`local_moves.ts`), recorded now: after the commit, or
    // at the next apply of a run that died before it recorded them.
    const recordLocal = async (file: string, rec: LocalLanded, fresh = false) => {
      for (const c of rec.covered) {
        if (done.has(c.proposal_id)) continue;
        const p = build.find((x) => x.id === c.proposal_id);
        if (!p) continue;
        const repointed = await repointMovedResults(cfg, qid, [{ from: c.from, to: c.existing }]);
        await recordNow({ ...baseRecord(p, owner[p.id]!), decision: { kind: "covered", note: `covered by ${c.existing}: the toolkit already states it (the paper keeps its own proof)` }, promoted: [] });
        log(`${p.id}: covered by \`${c.existing}\`${repointed.length ? `; crosswalk / report now point ${repointed.join(", ")} at it` : ""}`);
        done.add(p.id);
        build.splice(build.indexOf(p), 1);
      }
      // (the graph after the moves was taken in the workspace, before the commit)
      for (const r of rec.regressions ?? []) log(`toolkit graph: ${r}`);
      regressions = [...regressions, ...(rec.regressions ?? [])];
      if (rec.batch.moves.length) await recordLanded(file, rec.batch, fresh);
      await d.removeFile(file);
    };
    // A toolkit commit on file (this run's, interrupted after its commit point, or another's): rolled
    // forward under the promotion lock before anything is planned — never planned on the old base.
    if (await commitOnFile(cfg.toolkitRoot)) await withPromotionLock(cfg.toolkitRoot, () => honourCommit(cfg.toolkitRoot, log), cfg.lockPath, log);
    for (const { file, landed } of await landedRecords(cfg, qid)) await recordLocal(file, landed);

    // Other papers that use this one (papers may build on each other): a move rewrites their
    // references to what it moves, as in this paper, and its gate builds the modules it rewrote —
    // those that built just before it (`brokenBefore`: a live run's paper may be mid-edit; what it
    // breaks is not the move's, and the daily library check reports it).
    const imp = dryRun || build.length === 0 ? NO_IMPORTERS : await findImporters(cfg, paperModule).catch((err) => {
      log(`other papers' use of ${paperModule} not read (${err instanceof Error ? err.message : String(err)}); the moves rewrite this paper only — the daily library check reports what breaks`);
      return NO_IMPORTERS;
    });
    if (imp.files.length) log(`other papers: ${imp.files.length} file(s) of ${[...imp.declared.keys()].join(", ")} name this paper — the moves rewrite their references too`);

    // Re-scan (in a workspace, `withScanRoot`): the batch must still describe the paper.
    const scan = args.scan ? await args.scan() : await obtainScan({ toolkit: cfg, qid, leanSubdir: state.lean_subdir, log });
    const fresh = filterCandidates(scan, await paperObjects(cfg, qid));
    const freshByName = new Map(fresh.candidates.map((c) => [c.name, c] as const));
    const alreadyMoved = new Map<string, { to: string; module: string }>(moves.flatMap((m) => m.decls.map((x) => [x.from, { to: x.to, module: m.module }] as const)));
    // (the toolkit graph before the moves, the duplicate and paper-name checks and the graph after
    // the moves are taken in the workspace, of each base: `local_moves.ts`)
    for (const p of build) {
      const c = freshByName.get(p.source.ref);
      if (!c) throw new Error(`${p.id}: ${p.source.ref} is no longer a clean round-B candidate in the paper as it stands; re-propose with \`paperformalizer verify … --from-stage V6\``);
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
    // (the headline baseline is taken in the workspace, of each base)
    const headlines = await reportHeadlineDecls(cfg, qid);
    const byName = new Map(scan.declarations.map((x) => [x.name, x] as const));
    // What one move is, given what moved before it: its declarations, its place, its records.
    const prepare = (p: Proposal, movedBefore: ReadonlyMap<string, { to: string; module: string }>) => {
      const dec = owner[p.id]!;
      const eff = applyEdits(p, dec);
      const placement = classifyTarget(eff.target_module, cfg);
      if (placement.division !== eff.division) throw new Error(`${p.id}: target_module ${eff.target_module} is not in division ${eff.division}`);
      const closure = (freshByName.get(p.source.ref)?.moves_with ?? []).filter((n) => !movedBefore.has(n));
      const ns = nsOf(eff.proposed_name);
      const decls: MoveDecl[] = [
        ...closure.map((n) => ({ from: n, to: ns ? `${ns}.${leafOf(n)}` : leafOf(n), kind: byName.get(n)?.kind ?? "theorem" })),
        { from: p.source.ref, to: eff.proposed_name, kind: byName.get(p.source.ref)?.kind ?? "theorem" },
      ];
      const targetAbs = path.join(cfg.toolkitRoot, ...eff.target_module.split("/"));
      const place: Omit<MoveTarget, "existingText"> = {
        rel: eff.target_module, module: placement.module, division: placement.division,
        overview: eff.new_module_overview ?? `${eff.division} results proved in verified papers.`,
      };
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
      return { dec, eff, placement, decls, targetAbs, place, toolkitModulesUsed, usedConstants, ledgerEntries };
    };
    type Prepared = ReturnType<typeof prepare>;
    // What `planMove` needs of a move besides the files (planned from the files as they stand: `plannerFor`).
    const specOf = (p: Proposal, m: Prepared, movedBefore: ReadonlyMap<string, { to: string; module: string }>): MoveSpec => ({
      proposalId: p.id, mainFrom: p.source.ref, decls: m.decls, ledgerEntries: m.ledgerEntries, place: m.place,
      alreadyMoved: [...movedBefore].map(([k, v]) => [k, { ...v }] as [string, { to: string; module: string }]),
      toolkitModulesUsed: m.toolkitModulesUsed, usedConstants: m.usedConstants,
      docstringOverride: m.dec.kind === "accept_with_edits" && (m.dec.edits.title || m.dec.edits.content || m.dec.edits.reference) ? proposalDocstring(m.eff) : null,
      fallbackDocstring: proposalDocstring(m.eff),
    });

    // The moves, prepared in the run's workspace as one batch and committed (`local_moves.ts`).
    if (build.length > 0) {
      const out = await localCommitMoves({
        cfg, d, qid, log, toolsDir, indexStep, leanSubdir: state.lean_subdir, paperModule, imp, headlines,
        moves: (skip) => {
          const sim = new Map(alreadyMoved);
          return build.filter((p) => !skip.has(p.id)).map((p) => {
            const movedBefore = new Map(sim);
            const m = prepare(p, movedBefore);
            for (const x of m.decls) sim.set(x.from, { to: x.to, module: m.placement.module });
            return { proposalId: p.id, mainFrom: p.source.ref, spec: specOf(p, m, movedBefore), module: m.placement.module, ledgerEntries: m.ledgerEntries };
          });
        },
        graphIn: args.graphIn ?? (args.graph ? () => args.graph!() : (c) => refreshToolkitGraph({ toolkit: c, log, scope: { qid, papers: [paperModule] } })),
        baselineIn: (c, probeFile) => headlineBaseline(c, paperModule, headlines, probeFile, d),
        ownName: (id, name) => { const p = build.find((x) => x.id === id); return !!p && builtByOwnStudy(declared, qid, p, name); },
        scanBefore: path.join(fpDir, "statements_before_batch.json"), scanAfter: fpAfterFile("batch"),
        // compat 2026-11-11: remove after the processes started before this merge have exited (≤2 days)
        localScans: true,
      });
      if (out.landed) {
        const rec = (JSON.parse(await readFile(out.landed, "utf8")) as { record: LocalLanded }).record;
        for (const m of rec.batch.moves) for (const x of m.decls) alreadyMoved.set(x.from, { to: x.to, module: m.module });
        await recordLocal(out.landed, rec, true);
      }
      if (out.failed) {
        throw new Error(`${out.failed}\nNothing of it reached the shared toolkit (the moves before it that passed are committed and recorded). ` +
          `This is the orchestrator's to settle: repair the Lean of the paper (or decide the entry again), then re-run \`paperformalizer propose ${qid} --round B --apply\`.`);
      }
    }
  }

  // The gates built the moving paper only: the whole library is built by the daily library check
  // the operator schedules (`libraryCheck`), never after an apply — an exclusive build of every paper
  // stops every other build for as long as it takes. What the moves broke is reported there.
  if (!dryRun && moves.length > 0) log(`library check: left to the daily build of ${cfg.papersLib}; a break the moves caused is reported there`);
  // Built in general form by the study pipeline; the paper's result is re-proved as its corollary.
  if (generalize.length > 0) {
    const runStudy = args.runStudy ?? (await import("../substrate/pipeline.js")).runSubstratePipeline;
    // the toolkit and this paper (which uses the general results as its corollaries' proofs)
    const papers = dryRun ? [] : [leanModulePrefix((await loadState(cfg.toolkitRoot, qid)).lean_subdir)];
    const graphOf = args.graph ?? (() => refreshToolkitGraph({ toolkit: cfg, log, scope: { qid, papers } }));
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
        // The re-proof may change the proof of that one result and nothing any declaration states:
        // re-proved in the run's workspace and committed (`local_moves.ts`).
        const state = await loadState(cfg.toolkitRoot, qid);
        const paperModule = leanModulePrefix(state.lean_subdir);
        const leanDir = leanTheoremDir(cfg.toolkitRoot, state.lean_subdir);
        const fpDir = proposalsRunDir(cfg, qid);
        const fpFile = (when: "before" | "after") => path.join(fpDir, `statements_${when}_${p.id}.json`);
        const r = await localCorollary({
          cfg, d, qid, log, paperModule, leanSubdir: state.lean_subdir, proposalId: p.id, decl: p.source.ref, file: path.join(cfg.toolkitRoot, file), general: b.main,
          ...(args.corollary ? { deps: args.corollary } : {}), scans: !args.corollary, scanFile: fpFile,
        });
        corollary = r.ok;
        if (r.ok && r.cleared.length) {
          const carried = await carryReceipts(cfg, qid, leanDir, r.cleared, fpFile("after")).catch(() => 0);
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
  return { decisions, records, promoted: [...moves.flatMap((m) => m.decls.map((x) => x.to)), ...records.filter((r) => generalize.some((p) => p.id === r.proposal_id)).flatMap((r) => r.promoted)], moves, regressions, libraryBreaks: [], libraryBreaksMaybeOlder: false };
}

/** Of `names`, those a paper's source declares (fully qualified): the files that mention a name's
 *  last component (one `grep` over the papers' sources, their `tmp/` scratch left out), parsed for
 *  their declarations. (`declaredNames` reads declaration headers: a structure's fields or an
 *  inductive's constructors, and a name on a header split over several lines, are not seen — the
 *  daily library check is what catches those.) */
export async function paperDeclaredNames(cfg: ToolkitConfig, names: readonly string[]): Promise<Set<string>> {
  const out = new Set<string>();
  const leaves = [...new Set(names.map(leafOf))];
  const dir = path.join(cfg.toolkitRoot, cfg.papersLib);
  if (!leaves.length || !existsSync(dir)) return out;
  // grep: 0 = matches, 1 = none, anything else = it could not read the sources
  const stdout = await new Promise<string>((resolve, reject) => {
    execFile("grep", ["-rlF", "--include=*.lean", `--exclude-dir=${PAPER_TMP_DIR}`, ...leaves.flatMap((l) => ["-e", l]), dir], { encoding: "utf8", maxBuffer: 256 * 1024 * 1024 }, (err, so, se) => {
      if (!err || (err as { code?: unknown }).code === 1) resolve(err ? "" : so);
      else reject(new Error(`the papers' sources could not be searched for the target names (grep: ${se.trim() || err.message}); re-run once the toolkit graph builds`));
    });
  });
  const wanted = new Set(names);
  for (const f of stdout.split("\n").filter(Boolean)) {
    for (const x of declaredNames(await readFile(f, "utf8"))) if (wanted.has(x.name)) out.add(x.name);
  }
  return out;
}

/** What the library check found: `breaks`, the modules that do not build; `killed`, those whose Lean
 *  was still killed by a signal (out of memory) after the re-builds — resources, not breaks. */
export interface LibraryCheck { breaks: string[]; killed: string[] }

/** The daily library check: build every paper (`lake build <papers_lib>`, under the Lake build lock
 *  as any build; a scheduled daily check runs it in a workspace of its own): the modules
 *  that fail, as Lake names them (or the command itself when it names none); empty when it passes.
 *  (2026-11-11) A module whose Lean was killed (137, the OOM killer on a loaded node): the library is
 *  built again with less parallelism (`LEAN_NUM_THREADS` 2, then 1: Lake 4.33 has no `-j`), two
 *  rounds at most; still killed, it is reported as `killed`. Each round's output is appended to `logFile`. */
export async function libraryCheck(cfg: ToolkitConfig, d: ApplyDeps, logFile: string): Promise<LibraryCheck> {
  const cmd = `lake build ${cfg.papersLib}`;
  const r = await d.run(cmd, cfg.toolkitRoot);
  await writeFile(logFile, `$ (${cfg.toolkitRoot}) ${cmd}\n${r.log}`, "utf8");
  if (r.code === 0 && !r.timedOut) return { breaks: [], killed: [] };
  let killed = killedModules(r.log);
  const breaks = new Set(failingModules(r.log).filter((m) => !killed.includes(m)));
  if (!breaks.size && !killed.length) return { breaks: [r.timedOut ? `${cmd} (watchdog-killed)` : cmd], killed: [] };
  // the whole target again, not the killed modules alone: Lake builds no dependent of a module that
  // failed, so a break further on shows only now (what is built already is skipped)
  for (const threads of ["2", "1"]) {
    if (!killed.length) break;
    const again = `LEAN_NUM_THREADS=${threads} ${cmd}`;
    const rr = await d.run(cmd, cfg.toolkitRoot, { env: { LEAN_NUM_THREADS: threads } });
    await appendFile(logFile, `\n$ (${cfg.toolkitRoot}) ${again}\n${rr.log}`, "utf8");
    if (rr.code === 0 && !rr.timedOut) { killed = []; break; }
    const stillKilled = killedModules(rr.log);
    const failing = failingModules(rr.log).filter((m) => !stillKilled.includes(m));
    for (const m of failing) breaks.add(m);
    // failed, naming nothing: never a pass
    if (!rr.timedOut && !failing.length && !stillKilled.length) breaks.add(again);
    // watchdog-killed: what it did not finish is still out of resources
    killed = rr.timedOut ? [...new Set([...killed, ...stillKilled])].filter((m) => !breaks.has(m)).sort() : stillKilled;
  }
  return { breaks: [...breaks].sort(), killed };
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
