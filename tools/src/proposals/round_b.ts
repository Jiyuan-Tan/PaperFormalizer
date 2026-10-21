// Round B: toolkit promotion after the V6 report (the harvest).
//
// The declarations the F stages proved inside the paper's Lean are scanned (`candidate_scan` exe; a
// dry run uses a synthetic scan of the core), filtered mechanically (`candidate_scan.ts`:
// axiom-clean, no sorry, statement over base + toolkit vocabulary, closure moves together, the
// paper's theorems excluded; its lemmas / propositions admitted and flagged), and recorded in the
// toolkit's statement store (`doc/statements.json`). Each candidate carries
// its recurrence in the owner's other papers (identical, or the same pattern), entries deferred
// before that it matches, the Foundations/Tricks signal, the hypotheses its proof never uses, and
// where it attaches in the toolkit graph; the curator (Claude) names the MAIN results and writes each
// as a textbook entry with its division, topic and bar; a helper of a main result is folded into that
// entry (it moves with it); the checker (codex) re-judges each entry (a duplicate is declined
// automatically). The result is `runs/<slug>/proposals/B.json` and the owner's checklist
// `<toolkit>/doc/proposals/<slug>.B.md`; the toolkit's reuse history gains this paper's line, and
// when its health has findings a gardening list is written beside it (`garden.ts`). Accepted entries
// are moved by `paperformalizer propose <slug> --apply` (`apply_b.ts`).
import { existsSync } from "node:fs";
import { mkdir, readdir, readFile, rename } from "node:fs/promises";
import path from "node:path";
import { parseTypedCore } from "../core/core_io.js";
import type { Core } from "../core/schema.js";
import { leanModulePrefix } from "../paths.js";
import type { runCodex as RunCodex } from "../shared/codex.js";
import { writeJsonAtomic, writeTextAtomic } from "../shared/json_atomic.js";
import { loadState } from "../state.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { appendDecisionRecords } from "../toolkit/ledger.js";
import { ensureTaxonomy } from "../toolkit/taxonomy.js";
import { lintUnusedHypotheses } from "../formalization/unused_hypothesis_lint.js";
import type { LeanExec } from "../verify/lean_evidence.js";
import { mainResultsUsed, writeReportToolkitSection } from "../verify/report_toolkit.js";
import { VERIFY_FILES } from "../verify/types.js";
import type { ClaudeRunInput } from "../workers/claude.js";
import { obtainScan, paperObjects, paperShapedReasons, syntheticScan, writeCandidates, type CandidateScan, type CandidatesFile, type ScanDecl } from "./candidate_scan.js";
import { recommendationKeys, renderChecklist, ROUND_IS_DELEGATED, ROUND_IS_THE_OWNERS } from "./checklist.js";
import { runChecker } from "./checker.js";
import { runCurator, type ProposalCandidate } from "./curator.js";
import { appendReuseHistory, runGardenRound } from "./garden.js";
import {
  batchPath,
  checklistPath,
  decisionsPath,
  proposalLedgerPath,
  proposalsRunDir,
  type Proposal,
  type ProposalBatch,
  type ProposalRound,
  type ProposalRoundState,
  type ProposalRoundVoidedRecord,
} from "./schema.js";
import { measureReuse } from "./reuse.js";
import { findRecurrence, loadStatementStore, recordProposals, recordScan, recurrenceWorkDir, statementStoreLockPath, statementStorePath, type StatementStore } from "./statements.js";
import { attachNote, healthSummary, refreshToolkitGraph, toolkitHealth, type ToolkitGraph } from "./toolkit_graph.js";

/** The name a candidate is known by inside its paper: the declaration name without the paper's
 *  module prefix (`Papers.Foo.bar_le` → `bar_le`). Proposal ids derive from it (`b-bar-le`). */
export function paperLocalName(name: string, prefix: string): string {
  return name.startsWith(`${prefix}.`) ? name.slice(prefix.length + 1) : name;
}

function firstParagraph(doc: string | null): string {
  return (doc ?? "").split(/\n\s*\n/)[0]!.replace(/\s+/g, " ").trim();
}

export async function readRunCore(cfg: ToolkitConfig, qid: string): Promise<Core> {
  const p = path.join(cfg.runsDir, qid, VERIFY_FILES.coreJson);
  return parseTypedCore(await readFile(p, "utf8"), `proposals: core.json at ${p}`);
}

/** Libraries at Mathlib's level: a statement over them alone is in "base vocabulary". */
const MATHLIB_LEVEL = new Set(["Mathlib", "Init", "Std", "Batteries", "Lean", "Aesop", "Qq", "Plausible"]);

/**
 * The toolkit graph's Foundations/Tricks signal for a declaration: what its statement and proof lean
 * on. Mathlib-level constants alone → Foundations-shaped; a domain library's (Causalean, …) or the
 * toolkit's → Tricks-shaped. The paper's own constants do not count (a paper-shaped result is built
 * in general form).
 */
export function divisionSignal(d: Pick<ScanDecl, "type_constants" | "body_constants">): "Foundations" | "Tricks" {
  const leans = [...d.type_constants, ...d.body_constants].some((c) =>
    c.class === "toolkit" || (c.class === "base" && !MATHLIB_LEVEL.has(c.module.split(".")[0]!)));
  return leans ? "Tricks" : "Foundations";
}

/** Hypotheses each declaration's proof never uses (definite findings of the unused-hypothesis
 *  lint over its source file), by declaration leaf name. */
export async function unusedHypothesesByLeaf(cfg: ToolkitConfig, files: readonly string[]): Promise<Map<string, string[]>> {
  const out = new Map<string, string[]>();
  for (const f of [...new Set(files)]) {
    const abs = path.join(cfg.toolkitRoot, f);
    if (!existsSync(abs)) continue;
    for (const x of lintUnusedHypotheses(await readFile(abs, "utf8")).findings) {
      if (x.severity !== "definite") continue;
      const leaf = x.theoremName.split(".").pop()!;
      out.set(leaf, [...new Set([...(out.get(leaf) ?? []), x.hypothesisName])]);
    }
  }
  return out;
}

/** The gardening list's path, or null when there is none. The list is a by-product of the round: a
 *  gardener that fails (its reply breaks its contract twice) costs the list, never the round. */
export async function gardenListOrNull(run: () => Promise<{ path: string } | null>, log: (m: string) => void): Promise<string | null> {
  try {
    return (await run())?.path ?? null;
  } catch (err) {
    log(`gardening list: not written — ${(err instanceof Error ? err.message : String(err)).slice(0, 300)}`);
    return null;
  }
}

/** Curator candidates from the filtered scan (+ recurrence, + what ties each to the paper, + the
 *  Foundations/Tricks signal, + hypotheses the proof never uses, + earlier deferrals). */
export function roundBCandidates(
  file: CandidatesFile,
  recurrence: ReadonlyMap<string, ProposalCandidate["recurrence"]>,
  scan?: Pick<CandidateScan, "declarations">,
  extra: {
    unused?: ReadonlyMap<string, string[]>;
    deferred?: ReadonlyMap<string, Array<{ slug: string; proposal_id: string }>>;
  } = {},
): ProposalCandidate[] {
  const byName = new Map((scan?.declarations ?? []).map((d) => [d.name, d] as const));
  // A candidate another candidate carries in its closure is a helper of that candidate.
  const users = new Map<string, string[]>();
  for (const c of file.candidates) for (const m of c.moves_with) users.set(m, [...(users.get(m) ?? []), c.name]);
  return file.candidates.map((c) => {
    const helperOf = [...new Set([...c.used_by, ...(users.get(c.name) ?? [])])].filter((u) => u !== c.name);
    const local = paperLocalName(c.name, file.paper);
    const shaped = scan ? paperShapedReasons(c, scan) : [];
    const decl = byName.get(c.name);
    const unused = extra.unused?.get(c.name.split(".").pop()!) ?? [];
    const deferred = extra.deferred?.get(c.name) ?? [];
    return {
      candidate_id: c.name,
      source: {
        kind: "paper_decl" as const, ref: c.name,
        ...(c.paper_result ? { is_paper_result: true, paper_env: c.paper_result.obj_id } : {}),
      },
      kind: c.kind,
      statement: firstParagraph(c.doc) || c.type,
      context: {
        lean_type: c.type,
        // The statement above is the docstring's first paragraph; the rest only when there is more.
        ...(c.doc && c.doc.trim() !== firstParagraph(c.doc) ? { docstring: c.doc } : {}),
        module: c.module, moves_with_count: c.moves_with.length,
        ...(Object.keys(c.paper_objects).length ? { paper_objects_moving_with_it: [...new Set(Object.values(c.paper_objects))].sort() } : {}),
        ...(shaped.length ? { paper_shaped: shaped } : {}),
        ...(unused.length ? { hypotheses_the_proof_never_uses: unused } : {}),
      },
      ...(shaped.length ? { paper_shaped: shaped } : {}),
      ...(decl ? { division_signal: divisionSignal(decl) } : {}),
      ...(unused.length ? { dropped_hypotheses: unused } : {}),
      ...(deferred.length ? { deferred_before: deferred } : {}),
      ...(helperOf.length && !c.paper_result ? { helper_of: helperOf } : {}),
      search_words: `${local.split(".").pop() ?? local} ${firstParagraph(c.doc)}`.trim(),
      id_ref: local,
      moves_with: c.moves_with,
      lean_type: c.type,
      recurrence: recurrence.get(c.name) ?? [],
    };
  });
}

/** For each candidate: entries of other papers it recurs with that the owner deferred. */
export function deferredMatches(
  store: Pick<StatementStore, "entries">,
  recurrence: ReadonlyMap<string, ProposalCandidate["recurrence"]>,
): Map<string, Array<{ slug: string; proposal_id: string }>> {
  const deferred = new Map(store.entries.filter((e) => e.decision === "defer" && e.proposal_id).map((e) => [`${e.slug}::${e.name}`, e] as const));
  const out = new Map<string, Array<{ slug: string; proposal_id: string }>>();
  for (const [name, recs] of recurrence) {
    const hits = (recs ?? []).flatMap((r) => {
      const e = deferred.get(`${r.slug}::${r.name}`);
      return e ? [{ slug: e.slug, proposal_id: e.proposal_id! }] : [];
    });
    if (hits.length) out.set(name, hits);
  }
  return out;
}

/**
 * One entry per main result: a proposed item whose declaration another proposed item carries in its
 * closure is a helper of that item — it becomes a `skip` with `part_of` naming the entry it moves
 * with. When two proposed items carry each other (a cycle), the earlier stays the entry.
 */
export function foldHelpers(proposals: readonly Proposal[]): Proposal[] {
  const proposed = proposals.filter((p) => p.verdict === "propose");
  const ownerOf = new Map<string, Proposal>();
  for (const p of proposed) {
    for (const q of proposed) {
      if (p === q || ownerOf.has(q.id)) continue;
      if ((p.moves_with ?? []).includes(q.source.ref) && !(q.moves_with ?? []).includes(p.source.ref)) ownerOf.set(q.id, p);
    }
  }
  return proposals.map((p) => {
    const owner = ownerOf.get(p.id);
    return owner
      ? { ...p, verdict: "skip" as const, part_of: owner.id, reuse_evidence: `helper of ${owner.title || owner.source.ref}; moves with it` }
      : p;
  });
}

export interface RunRoundBArgs {
  toolkit: ToolkitConfig;
  qid: string;
  dryRun: boolean;
  /** The checker (codex). */
  runCodex: typeof RunCodex;
  /** The curator and the gardener (Claude); default: the claude CLI worker. */
  runClaude?: (o: ClaudeRunInput) => Promise<string>;
  log: (msg: string) => void;
  now?: () => Date;
  /** Injectable scan (tests); default: the exe (`obtainScan`), or `syntheticScan` in a dry run. */
  scan?: () => Promise<CandidateScan>;
  /** Injectable toolkit graph (tests); default: re-derived from the Lean (live), none (dry run). */
  graph?: () => Promise<ToolkitGraph | null>;
  exec?: LeanExec;
  /** Re-open only these candidates (`propose --reopen-deferred`): the entries the owner deferred. */
  only?: ReadonlySet<string>;
}

/** Run round B for a verify run whose V6 report is written. */
export async function runRoundB(args: RunRoundBArgs): Promise<ProposalRoundState> {
  const { toolkit: cfg, qid, log, dryRun } = args;
  const created = (args.now ?? (() => new Date()))().toISOString();
  const state = await loadState(cfg.toolkitRoot, qid);
  const prefix = leanModulePrefix(state.lean_subdir);
  let scan: CandidateScan;
  if (args.scan) scan = await args.scan();
  else if (dryRun) {
    log("promotion: dry run — synthetic scan (every core statement as a clean declaration of the paper)");
    scan = syntheticScan(await readRunCore(cfg, qid), prefix);
  } else {
    scan = await obtainScan({ toolkit: cfg, qid, leanSubdir: state.lean_subdir, log, ...(args.exec ? { exec: args.exec } : {}) });
  }
  // What the paper already uses from the toolkit (the report's toolkit section; the ledger's used_by),
  // and the line it adds to the toolkit's reuse history.
  let reuse: Awaited<ReturnType<typeof measureReuse>> | null = null;
  if (!dryRun) {
    reuse = await measureReuse({ toolkit: cfg, qid, leanSubdir: state.lean_subdir, log, scan: async () => scan });
    await writeReportToolkitSection(path.join(cfg.runsDir, qid), reuse, undefined, await mainResultsUsed(cfg, reuse));
    await ensureTaxonomy(cfg, log);
  }
  const file = await writeCandidates(cfg, qid, scan, await paperObjects(cfg, qid));
  log(
    `promotion: scanned ${scan.declarations.length} declaration(s) of ${prefix}: ${file.candidates.length} candidate result(s), ` +
      `${file.movable.length - file.candidates.length} travelling definition(s), ${file.rejected.length} rejected`,
  );

  const store = statementStorePath(cfg, qid, dryRun);
  const storeLock = statementStoreLockPath(cfg, qid, dryRun);
  await recordScan(store, qid, scan, file, created, storeLock);
  const storeNow = await loadStatementStore(store);
  const recurrence = await findRecurrence(storeNow, qid, file.candidates, recurrenceWorkDir(cfg, qid), cfg.papersLib);
  const recurring = [...recurrence.values()].filter((r) => r.some((x) => x.kind === "identical")).length;
  const patterned = [...recurrence.values()].filter((r) => r.some((x) => x.kind === "pattern")).length;
  log(`promotion: statements recorded in ${store}; ${recurring} candidate(s) recur identically in another paper, ${patterned} by pattern`);
  const deferred = deferredMatches(storeNow, recurrence);
  if (deferred.size) log(`promotion: ${deferred.size} candidate(s) match an entry deferred in another paper — they return with the new evidence`);

  // The toolkit graph: where each candidate attaches, and the toolkit's health (both on the main view).
  let graph: ToolkitGraph | null = null;
  try {
    graph = args.graph ? await args.graph() : dryRun ? null : await refreshToolkitGraph({ toolkit: cfg, log });
  } catch (err) {
    log(`promotion: toolkit graph not built (${err instanceof Error ? err.message : String(err)}); the checklist goes without it`);
  }
  const unused = await unusedHypothesesByLeaf(cfg, file.candidates.map((c) => c.file));
  let candidates = roundBCandidates(file, recurrence, scan, { unused, deferred });
  if (args.only) candidates = candidates.filter((c) => args.only!.has(c.candidate_id));
  const dropping = candidates.filter((c) => c.dropped_hypotheses?.length).length;
  if (dropping) log(`promotion: ${dropping} candidate(s) carry hypotheses their proof never uses — offered in general form without them`);

  let proposals = candidates.length === 0
    ? []
    : await runCurator({
      toolkit: cfg, slug: qid, candidates, dryRun, log,
      ...(args.runClaude ? { runClaude: args.runClaude } : {}),
    });
  // where each proposed result attaches in the toolkit graph (shown on the checklist)
  const notes = new Map(graph ? candidates.map((c) => [c.candidate_id, attachNote(graph!, [c.candidate_id, ...(c.moves_with ?? [])])] as const) : []);
  proposals = foldHelpers(proposals).map((p) => (notes.has(p.source.ref) && p.verdict === "propose" ? { ...p, graph_note: notes.get(p.source.ref)! } : p));
  proposals = await runChecker({ toolkit: cfg, slug: qid, proposals, candidates, dryRun, runCodex: args.runCodex, log });
  const batch: ProposalBatch = { slug: qid, round: "B", created, proposals };
  const bp = batchPath(cfg, qid);
  await mkdir(path.dirname(bp), { recursive: true });
  const earlier = await archiveEarlierRound(cfg, qid, batch);
  if (earlier.length > 0) log(`promotion: an earlier round B left ${earlier.join(", ")} — moved under proposals/voided/`);
  await writeJsonAtomic(bp, batch);
  await recordProposals(store, qid, proposals, storeLock);
  const proposed = proposals.filter((p) => p.verdict === "propose");
  // The toolkit as it stands: its reuse history gains this paper's line, and when its health has
  // findings the gardener writes the owner a gardening list (one Claude call; none otherwise).
  const healthNow = graph ? toolkitHealth(graph) : null;
  let garden: string | null = null;
  if (!dryRun && graph && healthNow && !args.only) {
    await appendReuseHistory(cfg, { slug: qid, at: created, reuse, health: healthNow });
    garden = await gardenListOrNull(() => runGardenRound({
      toolkit: cfg, graph, log, now: args.now, ledger: { runDir: path.join(cfg.runsDir, qid), stage: "garden" },
      ...(args.runClaude ? { runClaude: args.runClaude } : {}),
    }), log);
  }
  if (proposed.length === 0) {
    log(`promotion: nothing proposed (${candidates.length} candidate(s)) — finishing; batch ${bp}`);
    return { status: "empty", batch_path: bp, checklist_path: null, created_at: created, promoted: [] };
  }
  const cp = checklistPath(cfg, qid, dryRun);
  await mkdir(path.dirname(cp), { recursive: true });
  const health = healthNow ? healthSummary(healthNow) : undefined;
  await writeTextAtomic(cp, renderChecklist(batch, { toolkitRoot: cfg.toolkitRoot, dryRun, ...(health ? { health } : {}), ...(garden ? { garden } : {}) }));
  const folded = proposals.filter((p) => p.part_of).length;
  const dup = proposals.filter((p) => p.duplicate_of).length;
  const disagreements = proposed.filter((p) => p.checker && !p.checker.agrees).length;
  log(
    `promotion: ${proposed.length} main result(s) proposed` +
      `${folded ? `, ${folded} helper(s) folded into them` : ""}${dup ? `, ${dup} declined as already available` : ""}` +
      `${disagreements ? `, checker disagrees on ${disagreements}` : ""}; batch ${bp}`,
  );
  return { status: "pending_user", batch_path: bp, checklist_path: cp, created_at: created, promoted: [] };
}

/**
 * A new batch of `round` is about to be written: what an earlier round of it left in the run's
 * proposals directory is not this batch's. Its batch, decisions, the list of the moves it made
 * (`B.moves.json`), move logs and statement snapshots, and the agent's recommendations on items
 * the new batch does not hold as they were recommended on, move under `proposals/voided/<stamp>/` (an applied round followed by
 * a rewind is not set aside by `voidRoundB`, which handles a round still pending). A move the
 * toolkit is still half-way through stays whole: `move_pending.json`, the journal of the bytes it
 * replaced (`move_journal.json`), and the statement snapshot and log it names — its gate runs again
 * on them at the next apply. Returns the names moved.
 */
export async function archiveEarlierRound(cfg: ToolkitConfig, qid: string, batch: ProposalBatch): Promise<string[]> {
  const dir = proposalsRunDir(cfg, qid);
  if (!existsSync(dir)) return [];
  const round = batch.round;
  // (unreadable: nothing of a move is archived — the next apply reports the file)
  let pending: { proposal_id?: string; statements_before?: string | null } | null = null;
  const pendingFile = path.join(dir, "move_pending.json");
  if (existsSync(pendingFile)) {
    try { pending = JSON.parse(await readFile(pendingFile, "utf8")) as typeof pending; } catch { pending = {}; }
  }
  const ofPending = (f: string): boolean =>
    pending !== null && (!pending.proposal_id || f === `move_${pending.proposal_id}.log` || f === `statements_before_${pending.proposal_id}.json` ||
      f === `statements_after_${pending.proposal_id}.json` || f === path.basename(pending.statements_before ?? ""));
  const left = (await readdir(dir)).filter((f) =>
    f === `${round}.json` || f === `${round}.decisions.json` ||
    (round === "B" && (f === "B.moves.json" || ((/^move_.*\.log$/.test(f) || /^statements_(before|after)_.*\.json$/.test(f)) && !ofPending(f)))));
  const recsFile = path.join(dir, `${round}.recommendations.json`);
  const recs = existsSync(recsFile) ? (JSON.parse(await readFile(recsFile, "utf8")) as Record<string, { of?: string }>) : {};
  // A recommendation stays only on the item it was written for (`recommendationKeys`): the same id
  // in the new batch may hold another statement.
  const keys = recommendationKeys(batch);
  const ids = { has: (id: string): boolean => keys.has(id) && recs[id]?.of === keys.get(id) };
  const stale = Object.keys(recs).filter((id) => !ids.has(id));
  if (left.length === 0 && stale.length === 0) return [];
  const to = path.join(dir, "voided", batch.created.replace(/[:.]/g, "-"));
  await mkdir(to, { recursive: true });
  for (const f of left) await rename(path.join(dir, f), path.join(to, f));
  if (stale.length > 0) {
    await writeJsonAtomic(path.join(to, `${round}.recommendations.json`), Object.fromEntries(stale.map((id) => [id, recs[id]])));
    await writeJsonAtomic(recsFile, Object.fromEntries(Object.entries(recs).filter(([id]) => ids.has(id))));
  }
  return [...left, ...(stale.length > 0 ? [`${round}.recommendations.json (${stale.length} entr${stale.length === 1 ? "y" : "ies"})`] : [])];
}

/** The stop message of a pending round. */
export function roundBStopMessage(cfg: ToolkitConfig, qid: string, rec: ProposalRoundState, count: number, dryRun = false, fullAuto = false): string {
  return `promotion: ${count} result(s) proposed for the toolkit — ${fullAuto ? ROUND_IS_DELEGATED : ROUND_IS_THE_OWNERS}; the checklist is ${rec.checklist_path}, applied by: ` +
    `paperformalizer propose ${qid} --apply --toolkit ${cfg.toolkitRoot}${dryRun ? " --dry-run" : ""}`;
}

/** Set a pending round aside (its plan or report is re-made, so it is proposed afresh): the batch,
 *  the decisions and the checklist move under `runs/<slug>/proposals/voided/<stamp>/`, and the
 *  ledger records the void. Promotions an applied round made stay in the toolkit. */
export async function voidRoundB(args: {
  toolkit: ToolkitConfig;
  qid: string;
  rec: ProposalRoundState;
  reason: string;
  dryRun: boolean;
  log: (msg: string) => void;
  now?: () => Date;
  /** Default `B`. */
  round?: ProposalRound;
}): Promise<ProposalRoundVoidedRecord> {
  const { toolkit: cfg, qid, rec } = args;
  const round = args.round ?? "B";
  const voidedAt = (args.now ?? (() => new Date()))().toISOString();
  const dir = path.join(proposalsRunDir(cfg, qid), "voided", voidedAt.replace(/[:.]/g, "-"));
  const setAside = async (from: string | null, name: string): Promise<string | null> => {
    if (!from || !existsSync(from)) return null;
    await mkdir(dir, { recursive: true });
    const to = path.join(dir, name);
    await rename(from, to);
    return to;
  };
  const previousBatch = await setAside(rec.batch_path, `${round}.json`);
  await setAside(decisionsPath(cfg, qid, round), `${round}.decisions.json`);
  await setAside(rec.checklist_path, rec.checklist_path ? path.basename(rec.checklist_path) : "");
  const record: ProposalRoundVoidedRecord = {
    kind: "proposal_round_voided", slug: qid, round, reason: args.reason, previous_status: rec.status,
    previous_batch_path: previousBatch, promoted: rec.promoted ?? [], voided_at: voidedAt,
    ...(args.dryRun ? { dry_run: true } : {}),
  };
  await appendDecisionRecords(proposalLedgerPath(cfg, qid, args.dryRun), [record], () => null);
  args.log(`promotion ${round}: the round is set aside (${args.reason})${previousBatch ? `; batch moved to ${previousBatch}` : ""}`);
  return record;
}
