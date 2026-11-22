// Round-B moves prepared in a private workspace and committed briefly (`shared/commit.ts`). Every round-B apply's moves, and a
// generalized result's corollary re-proof (`localCorollary`), take this path.
//
// The run prepares ITS OWN moves as one batch: a workspace `P` pinned to the current generation
// (`prepareWorkspace`: the moving paper and the papers that use it copied, the ledger and the index
// private), and there, against the toolkit's config rebased to `P` (`cfgAt`): the base checks (a
// moved result whose statement the base toolkit already states refuses the apply, as a target name
// a paper declares already does — both of each base), the statement scan and the headline baseline,
// then `gateMoveBatch` (one at a time after a batch that does not pass, stopping at the first that
// fails), and the toolkit graph after the moves, taken in `P` before its commit (its regressions in
// the landed record). Nothing of the shared tree is written before the verdict; a failing gate leaves
// it untouched (and `P` as the gate left it, for a look). Then `commitToolkit`: landed — the run
// records its moves from the landed record the commit wrote (`runs/<slug>/proposals/landed/`);
// base-moved — prepared again on the new generation; after `LOCAL_MOVES.rebasesBeforeLock` rebases,
// prepared under the promotion lock and committed (guaranteed progress; `withRebases`).
import { existsSync, readFileSync } from "node:fs";
import { mkdir, readdir, readFile, rm, unlink } from "node:fs/promises";
import path from "node:path";
import { leanTheoremDir, PAPER_TMP_DIR } from "../paths.js";
import { stampedClean, withPromotionLock } from "../shared/build_mutex.js";
import { writeTextAtomic } from "../shared/json_atomic.js";
import { currentGeneration } from "../shared/workspace.js";
import { reproveAsCorollary, type CorollaryDeps } from "./build.js";
import { commitToolkit, dropArchive, honourCommit, prepareCommit, readCommitJournal, SEED_LOCK_WAIT_HELD_S, withPromoWorkspace, type CommitOutcome } from "../shared/commit.js";
// compat 2026-11-11: remove after the processes started before this merge have exited (≤2 days)
// (a feature read off the module: a `commit.ts` loaded before the merge has no `recheck`)
import * as commitModule from "../shared/commit.js";
import { toolkitConfigFromJson, toolkitConfigFileIn, type ToolkitConfig } from "../toolkit/config.js";
import type { LedgerDeclaration } from "../toolkit/ledger.js";
import { indexNameTable, nameProblems } from "./curator.js";
import type { ApplyDeps, GateStep } from "./gate.js";
import { paperOfFile, type Importers } from "./importers.js";
import { fingerprintScanCmd, parseFingerprints, receiptsBefore, statementInvarianceFailure, takeFingerprints } from "./invariance.js";
import { gateMoveBatch, planMove, readBatchRecord, type BatchMove, type BatchRecord, type MoveDecl, type MoveTarget } from "./move.js";
import { proposalsRunDir } from "./schema.js";
import { duplicateStatementHash, healthRegressions, toolkitHealth, type ToolkitGraph } from "./toolkit_graph.js";

/** `wait` (the shared tree not its generation: an old-code promotion not published yet) is asked
 *  again every `waitPollMs`, for `waitMaxMs` at most; prepared under the promotion lock after
 *  `rebasesBeforeLock` rebases; refused after `baseMovedUnderLock` base-moveds under it (`withRebases`);
 *  an agent asked again outside the locks `reasksBeforeRefusal` times at most (`localCorollary`,
 *  `localCoordinate`). (2026-11-11: 4 rebases, was 2 — the fallback's hold stalls every promotion;
 *  the re-asks kept at 2, so an agent's cost does not double.) */
export const LOCAL_MOVES = { waitPollMs: 60_000, waitMaxMs: 60 * 60_000, rebasesBeforeLock: 4, baseMovedUnderLock: 2, reasksBeforeRefusal: 2 };
/** The commit directory a run's record lands in (`commit.ts` step 9). */
export const landedDir = (cfg: ToolkitConfig, qid: string) => path.join(proposalsRunDir(cfg, qid), "landed");

/** The toolkit's config rebased to the workspace `ws` (every path under it; `runs/` is the shared
 *  tree's through the workspace's link). */
export function cfgAt(cfg: ToolkitConfig, ws: string): ToolkitConfig {
  const file = toolkitConfigFileIn(cfg.toolkitRoot);
  if (!file) throw new Error(`no toolkit config in ${cfg.toolkitRoot}`);
  return toolkitConfigFromJson(ws, JSON.parse(readFileSync(file, "utf8")));
}

/** One move, as data: what `planMove` needs besides the files, and what the gate records. */
export interface MoveSpec {
  proposalId: string;
  /** The accepted declaration (the paper's name). */
  mainFrom: string;
  decls: MoveDecl[];
  ledgerEntries: LedgerDeclaration[];
  place: Omit<MoveTarget, "existingText">;
  /** Moves of this paper before it (in this batch or earlier): their references are rewritten. */
  alreadyMoved: Array<[string, { to: string; module: string }]>;
  toolkitModulesUsed: string[];
  usedConstants: Array<{ name: string; module: string }>;
  docstringOverride: string | null;
  fallbackDocstring: string | null;
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

/**
 * A move's plan, made from the files as they stand when it is called: the target as it is now (an
 * earlier move of the batch may have appended to it), the paper's files, and the files of the papers
 * that use it. Returns the target and the plan for either header mode.
 */
export function plannerFor(cfg: ToolkitConfig, d: ApplyDeps, leanDir: string, imp: Importers, m: MoveSpec) {
  return async () => {
    const targetAbs = path.join(cfg.toolkitRoot, ...m.place.rel.split("/"));
    const target: MoveTarget = { ...m.place, existingText: (await d.exists(targetAbs)) ? await d.readFile(targetAbs) : null };
    const paperFiles = new Map<string, string>();
    for (const f of await listPaperFiles(leanDir)) paperFiles.set(f, await d.readFile(f));
    // (a file a live run removed since is skipped; one it added since is not rewritten — the library check reports it)
    for (const f of imp.files) if (await d.exists(f)) paperFiles.set(f, await d.readFile(f));
    const alreadyMoved = new Map(m.alreadyMoved);
    const planFor = (importMode: "minimal" | "source") => planMove({
      cfg, paperFiles, decls: m.decls, mainFrom: m.mainFrom, shadowOf: (f) => imp.declared.get(paperOfFile(cfg, f)),
      docstringOverride: m.docstringOverride, fallbackDocstring: m.fallbackDocstring,
      target, alreadyMoved, toolkitModulesUsed: m.toolkitModulesUsed, usedConstants: m.usedConstants, importMode,
      readModule: (mod) => paperFiles.get(path.join(cfg.toolkitRoot, ...mod.split(".")) + ".lean") ?? null,
    });
    return { target, planFor };
  };
}

/** One accepted move, given which of the batch are not moved (`covered`): what the plan and the
 *  gate need (`MoveSpec`) and its records. */
export interface LocalMove { proposalId: string; mainFrom: string; spec: MoveSpec; module: string; ledgerEntries: LedgerDeclaration[] }

/** What a run's landed record holds (`CommitRecord.record`): the batch record of its moves, the
 *  accepted results its base already stated (not moved; the paper repoints to them), and what the
 *  moves made worse in the toolkit graph (reported, as a run that dies after its commit records them later). */
export interface LocalLanded { batch: BatchRecord; covered: Array<{ proposal_id: string; from: string; existing: string }>; regressions?: string[] }

export interface LocalMovesArgs {
  cfg: ToolkitConfig;
  d: ApplyDeps;
  qid: string;
  log: (msg: string) => void;
  toolsDir: string;
  indexStep: GateStep | null;
  leanSubdir: string;
  paperModule: string;
  /** Other papers' files that use this paper, in the shared tree (`findImporters`). */
  imp: Importers;
  /** The paper's headline declarations (the gate's axioms baseline is taken of them, in `P`). */
  headlines: readonly string[];
  /** The accepted moves in order, the ones in `skip` left out (planned as if they did not move). */
  moves: (skip: ReadonlySet<string>) => LocalMove[];
  /** The toolkit graph of the toolkit and this paper in a workspace (the base checks), or null. */
  graphIn: (cfgP: ToolkitConfig) => Promise<ToolkitGraph | null>;
  /** The headline `#print axioms` baseline of the paper in a workspace. */
  baselineIn: (cfgP: ToolkitConfig, probe: string) => Promise<Map<string, string[]>>;
  /** Names the owner accepted for a study's own built declaration (never refused as taken). */
  ownName: (proposalId: string, name: string) => boolean;
  /** Where the statement scans go (as the batch path's). */
  scanBefore: string;
  scanAfter: string;
  // compat 2026-11-11: remove after the processes started before this merge have exited (≤2 days)
  // (passed `true` to a `local_moves` loaded before the merge: its paper-name check and graph after)
  localScans?: boolean;
}

/** What came of the run's local moves: the landed record to record from (null: nothing landed),
 *  and why a move did not pass its gate (the moves after it not tried), or null. */
export interface LocalMovesOutcome { landed: string | null; failed: string | null }

const sameDecl = (a: string, b: string) => a === b || a.endsWith(`.${b}`) || b.endsWith(`.${a}`);
const sleep = (ms: number) => new Promise<void>((r) => setTimeout(r, ms));

/** Prepare the run's moves in its workspace and commit them (see the header). */
export async function localCommitMoves(a: LocalMovesArgs): Promise<LocalMovesOutcome> {
  return withRebases(a.cfg, a.log, `${a.qid}'s moves`, (held) => attempt(a, held));
}

/** One preparation on the current generation and its commit: what came of it, or `base-moved`.
 *  `P` is the attempt's (its lock, `withPromoWorkspace`) until the commit is prepared. */
async function attempt(a: LocalMovesArgs, held: boolean): Promise<LocalMovesOutcome | "base-moved"> {
  const { cfg, qid, log } = a;
  const r = await withPromoWorkspace(cfg.toolkitRoot, qid, [a.paperModule, ...a.imp.declared.keys()], { log, ...heldPrepare(held) }, (w) => prepareMoves(a, w));
  if (!("C" in r)) return r;
  // (2026-11-11, step 2) the target names once more against the papers' sources, under the locks: a
  // commit may land on a later generation without a new prepare, and a paper that declared one since
  // refuses the moves as the prepare would
  const out = await commitPrepared(cfg, r.C, held, log, `${qid}'s moves`, () => recheckPaperNames(cfg, r.C, r.targets, r.leaving));
  if (out === "base-moved") return out;
  log(`promotion: ${qid}'s ${r.passed} move(s) committed as generation ${out.gen}${out.slow ? " (built for real in the shared tree)" : ""}`);
  return { landed: path.join(landedDir(cfg, qid), `${path.basename(r.C)}.json`), failed: r.failed };
}

/** The moves prepared in `P` (`w`), gated, and their commit prepared (`C`), or what came of them. */
async function prepareMoves(a: LocalMovesArgs, w: { path: string; gen: number }): Promise<LocalMovesOutcome | { C: string; passed: number; failed: string | null; targets: Array<{ id: string; names: string[] }>; leaving: string[] }> {
  const { cfg, d, qid, log } = a;
  const own = a.paperModule;
  const P = w.path;
  const cfgP = cfgAt(cfg, P);
  log(`promotion: ${qid}'s moves prepared in ${P} (generation ${w.gen})`);
  const leanDirP = leanTheoremDir(P, a.leanSubdir);
  const impP: Importers = { files: a.imp.files.map((f) => path.join(P, path.relative(cfg.toolkitRoot, f))), declared: a.imp.declared };
  const priv = path.join(P, ".pf-promo");
  await rm(priv, { recursive: true, force: true });
  await mkdir(priv, { recursive: true });

  // The base checks, against THIS base.
  const all = a.moves(new Set());
  const graph = await a.graphIn(cfgP).catch((err: unknown) => {
    log(`promotion: toolkit graph of the workspace not built (${err instanceof Error ? err.message : String(err)}); no duplicate check against the base`);
    return null;
  });
  // A moved theorem whose statement THIS base already states (the scan's statement hash): refused —
  // the owner's decision again, never a result dropped on a hash match.
  const covered: LocalLanded["covered"] = [];
  if (graph) {
    const hashes = new Map(graph.nodes.filter((n) => n.layer === "toolkit" && duplicateStatementHash(n)).map((n) => [duplicateStatementHash(n)!, n.id] as const));
    const ownHash = new Map(graph.nodes.filter((n) => n.layer === "paper").map((n) => [n.id, duplicateStatementHash(n)] as const));
    for (const m of all) {
      const h = ownHash.get(m.mainFrom);
      const existing = h ? hashes.get(h) : undefined;
      if (existing) throw new Error(`${m.proposalId}: duplicate of \`${existing}\` (statement hash match) in the toolkit of generation ${w.gen} — decide it again (decline it: the paper can use \`${existing}\`), then re-run`);
    }
  }
  // A target name a paper declares already: refused — this paper's declarations from THIS base's
  // graph, every paper's from the shared tree's sources.
  const { paperDeclaredNames } = await import("./apply_b.js");
  const leaving = new Set(all.flatMap((m) => m.spec.decls.map((x) => x.from)));
  const declared = new Set([
    ...(graph ? graph.nodes.filter((n) => n.layer === "paper").map((n) => n.id) : []),
    ...await paperDeclaredNames(cfg, all.flatMap((m) => m.spec.decls.map((x) => x.to))),
  ]);
  if (!graph) log("promotion: no toolkit graph — the target names were checked against the papers' sources only");
  for (const m of all) {
    const clash = m.spec.decls.map((x) => x.to).filter((n) => declared.has(n) && !leaving.has(n));
    if (clash.length) throw new Error(`${m.proposalId}: ${clash.map((n) => `\`${n}\``).join(", ")} is declared in a paper already; decide accept_with_edits with another proposed_name, then re-run`);
  }
  const skip = new Set<string>();
  const moves = a.moves(skip);
  const names = await indexNameTable(cfgP);
  for (const m of moves) {
    const main = m.spec.decls.find((x) => x.from === m.mainFrom)!.to;
    if (a.ownName(m.proposalId, main)) continue;
    const problems = nameProblems(main, names);
    if (problems.length) throw new Error(`${m.proposalId}: ${problems.join("; ")} — decide accept_with_edits with a proposed_name that fixes it, then re-run`);
  }
  if (moves.length === 0) return { landed: await landedRecord(a, P, null, covered), failed: null };

  // The statement scan and the headline baseline, in the workspace (a rebase takes them again).
  const movedOf = (ms: readonly LocalMove[]) => ms.flatMap((m) => m.spec.decls.map((x) => ({ from: x.from, to: x.to })));
  const moved = movedOf(moves);
  const fpAll = await takeFingerprints(d, cfgP, own, a.scanBefore, moved);
  if (!fpAll) log(`promotion: statement invariance not checked — the scan reported no statement hashes (update the toolkit's CandidateScan.lean from the template)`);
  // (the run's F4 receipts: of the paper as it stands in the shared tree, the same bytes as the copy)
  const cleared = fpAll ? await receiptsBefore(cfg, qid, leanTheoremDir(cfg.toolkitRoot, a.leanSubdir), a.scanBefore) : [];
  const baseline = await a.baselineIn(cfgP, path.join(priv, "headline_axioms.lean"));
  const indexStep = a.indexStep ? { ...a.indexStep, cwd: P } : null;
  const journal = path.join(priv, "move_batch_journal.json");
  let carried = false;
  /** `batch` written over what passed before it and gated once, its statements compared with `fp`
   *  (a scan taken with the batch's renames). Passed: its moves on record, its journal dropped. */
  const gate = async (batch: readonly LocalMove[], mode: "minimal" | "source", fp: Map<string, string> | null) => {
    const names = movedOf(batch);
    const r = await gateMoveBatch({
      cfg: cfgP, toolsDir: a.toolsDir, journalFile: journal, probeFile: path.join(priv, "move_axioms.lean"), indexStep,
      headlineBaseline: new Map([...baseline].filter(([h]) => !moved.some((x) => sameDecl(h, x.from)))),
      invariance: fp ? [{
        cmd: fingerprintScanCmd(cfgP, own, a.scanAfter),
        check: (): string | null => {
          const after = existsSync(a.scanAfter) ? parseFingerprints(readFileSync(a.scanAfter, "utf8")) : null;
          return after ? statementInvarianceFailure(fp, after, names) : "the scan after the move reported no statement hashes";
        },
      }] : [],
      moves: batch.map((m, i): BatchMove => ({
        slug: qid, proposalId: m.proposalId, paperModule: own, decls: m.spec.decls, ledgerEntries: m.ledgerEntries, checked: fp !== null,
        ...(i === batch.length - 1 && cleared.length && !carried ? { cleared } : {}),
        plan: async () => {
          const { target, planFor } = await plannerFor(cfgP, d, leanDirP, impP, m.spec)();
          log(`${m.proposalId}: moving ${m.spec.decls.map((x) => (x.from === x.to ? x.to : `${x.from} → ${x.to}`)).join(", ")} into ${m.module}${target.existingText === null ? " (new module)" : ""} (in the workspace)`);
          return { plan: planFor(mode), target };
        },
      })),
    }, d);
    if (r.ok) {
      passed.push(...((await readBatchRecord(journal, d))?.moves ?? []));
      await unlink(journal).catch(() => {});
      carried = true;
    }
    return r;
  };
  const logFile = path.join(proposalsRunDir(cfg, qid), "move_batch.log");
  const passed: BatchRecord["moves"] = [];
  let failed: string | null = null;
  const first = await gate(moves, "minimal", fpAll);
  const logs = [first.log];
  if (!first.ok && (first.timedOut || !first.restored)) {
    failed = `the gate in the workspace ${first.timedOut ? "was watchdog-killed (unverified)" : "failed and could not be undone there"} (log: ${logFile})`;
  } else if (!first.ok) {
    // one at a time (each planned from what passed before it), each with the source files' imports
    // when the minimal header does not pass, stopping at the first that fails
    if (moves.length > 1) log("promotion: the batch did not pass in the workspace and was undone there; the moves are gated one at a time");
    for (const [i, m] of moves.entries()) {
      const fp = moves.length === 1 ? fpAll : await takeFingerprints(d, cfgP, own, a.scanBefore, movedOf([m]));
      let one = moves.length === 1 && i === 0 ? first : await gate([m], "minimal", fp);
      if (one !== first) logs.push(one.log);
      if (!one.ok && !one.timedOut && one.restored) {
        one = await gate([m], "source", fp);
        logs.push(`--- ${m.proposalId}: again with the source files' imports ---\n${one.log}`);
      }
      if (!one.ok) {
        failed = `${m.proposalId}: the move did not pass its gate in the workspace (log: ${logFile})${i + 1 < moves.length ? `; ${moves.slice(i + 1).map((x) => x.proposalId).join(", ")} not tried` : ""}`;
        break;
      }
    }
  }
  const { writeFile } = await import("node:fs/promises");
  await writeFile(logFile, logs.join("\n\n"), "utf8").catch(() => {});
  if (failed) log(`promotion: ${failed}\nNothing of it reached the shared toolkit; the workspace keeps the files as its gate left them (${P}).`);
  if (passed.length === 0 && covered.length === 0) return { landed: null, failed };

  const batch: BatchRecord = { passed: true, checked: fpAll !== null, moves: passed };
  if (passed.length === 0) return { landed: await landedRecord(a, P, batch, covered), failed };
  // The toolkit graph after the moves, before the commit: `P` is then the tree that becomes the next
  // generation. What the moves made worse goes in the landed record.
  let regressions: string[] = [];
  if (graph) {
    const after = await a.graphIn(cfgP).catch((err: unknown) => {
      log(`promotion: toolkit graph after the moves not built in the workspace (${err instanceof Error ? err.message.split("\n")[0] : String(err)}); no health comparison`);
      return null;
    });
    if (after) regressions = healthRegressions(toolkitHealth(graph), toolkitHealth(after), passed.flatMap((m) => m.decls.map((x) => x.to)));
  }
  const ledger = moves.filter((m) => passed.some((x) => x.proposal_id === m.proposalId)).flatMap((m) => m.ledgerEntries);
  // (2026-11-11) what the moves add, with the base graph's statement hashes (its paper nodes, as the
  // duplicate check above reads them): for a later additive commit, inert now; one unknown, none
  const hashOf = new Map((graph?.nodes ?? []).filter((n) => n.layer === "paper" && n.statement_hash).map((n) => [n.id, n.statement_hash!] as const));
  const adds = passed.flatMap((m) => m.decls).map((x) => ({ name: x.to, hash: hashOf.get(x.from) }));
  const known = adds.every((x) => x.hash !== undefined) ? adds.map((x) => ({ name: x.name, hash: x.hash! })) : null;
  const C = await prepareCommit(cfg.toolkitRoot, P, { ledger, records: [{ slug: qid, record: { batch, covered, ...(regressions.length ? { regressions } : {}) } satisfies LocalLanded }], ...(known ? { adds: known } : {}), log });
  return { C, passed: passed.length, failed, targets: passed.map((m) => ({ id: m.proposal_id, names: m.decls.map((x) => x.to) })), leaving: [...leaving] };
}

/** (2026-11-11, step 2) A commit's target names (`targets`, per proposal) checked against the
 *  papers' sources once more (`paperDeclaredNames`), the names leaving a paper aside: one a paper
 *  declares now refuses it, as at the prepare — `C` removed, nothing committed (an error named
 *  `PaperNameClash`). Run under the locks, as `commitToolkit`'s `recheck` (`commitPrepared`). */
export async function recheckPaperNames(cfg: ToolkitConfig, C: string, targets: ReadonlyArray<{ id: string; names: readonly string[] }>, leaving: readonly string[]): Promise<void> {
  const { paperDeclaredNames } = await import("./apply_b.js");
  const gone = new Set(leaving);
  const declared = await paperDeclaredNames(cfg, targets.flatMap((x) => x.names));
  for (const x of targets) {
    const clash = x.names.filter((n) => declared.has(n) && !gone.has(n));
    if (!clash.length) continue;
    await rm(C, { recursive: true, force: true });
    const err = new Error(`${x.id}: ${clash.map((n) => `\`${n}\``).join(", ")} is declared in a paper already (since its move was prepared); decide accept_with_edits with another proposed_name, then re-run`);
    err.name = "PaperNameClash";
    throw err;
  }
}

/** How an attempt prepares its workspace (`withPromoWorkspace`) under the promotion lock (`held`):
 *  briefly waiting for the run's workspace's build lock (the seed) and for `P`'s own — `P` held
 *  elsewhere is `HeldWait` (`withRebases` releases the promotion lock and re-queues), never a long
 *  wait that stalls every promotion. */
export const heldPrepare = (held: boolean) =>
  held ? { seedWaitS: SEED_LOCK_WAIT_HELD_S, lockWaitS: SEED_LOCK_WAIT_HELD_S, lockBusy: (why: string) => new HeldWait(why) } : {};

/** Under the promotion lock (`withRebases`' fallback), the commit found the base moved (`HeldBaseMoved`)
 *  or had to wait (`HeldWait`): `C` removed, `withRebases` decides. */
export class HeldBaseMoved extends Error { constructor(readonly why: string) { super(`the toolkit moved on under the promotion lock (${why})`); } }
export class HeldWait extends Error { constructor(readonly why: string) { super(`the commit must wait under the promotion lock (${why})`); } }

/** Commit `C`: landed, or `base-moved` (`C` removed); `wait` asked again (`LOCAL_MOVES`), except
 *  with the line stopped, which throws: nothing reached the shared toolkit. `held`: the caller holds
 *  the promotion lock (the commit takes the exclusive Lake hold itself); then a base-moved or a wait
 *  throws `HeldBaseMoved` / `HeldWait` for `withRebases`. */
export async function commitPrepared(cfg: ToolkitConfig, C: string, held: boolean, log: (m: string) => void, what: string, recheck?: () => Promise<void>): Promise<Extract<CommitOutcome, { kind: "landed" }> | "base-moved">;
// compat 2026-11-11: remove after the processes started before this merge have exited (≤2 days)
// (the old arity: an `ApplyDeps` in position 2, unused — a caller loaded before the merge passes it)
export async function commitPrepared(cfg: ToolkitConfig, d: ApplyDeps, C: string, held: boolean, log: (m: string) => void, what: string, recheck?: () => Promise<void>): Promise<Extract<CommitOutcome, { kind: "landed" }> | "base-moved">;
export async function commitPrepared(cfg: ToolkitConfig, ...rest: unknown[]): Promise<Extract<CommitOutcome, { kind: "landed" }> | "base-moved"> {
  // compat 2026-11-11: remove after the processes started before this merge have exited (≤2 days)
  if (typeof rest[0] !== "string") rest.shift();
  const [C, held, log, what, recheck] = rest as [string, boolean, (m: string) => void, string, (() => Promise<void>) | undefined];
  // (2026-11-11, step 2) `recheck` runs under the locks (`commitToolkit`); a `commit.ts` loaded before
  // the merge takes none — then it runs here, before them
  const underLock = (commitModule as { COMMIT_RECHECK_UNDER_LOCK?: boolean }).COMMIT_RECHECK_UNDER_LOCK === true;
  if (recheck && !underLock) await recheck();
  for (let waited = 0; ; waited += LOCAL_MOVES.waitPollMs) {
    const out: CommitOutcome = await commitToolkit(cfg.toolkitRoot, C, { log, ...(held ? { held: "promotion" as const } : {}), ...(recheck && underLock ? { recheck } : {}) });
    if (out.kind === "landed") return out;
    if (out.kind === "base-moved") {
      await rm(C, { recursive: true, force: true });
      // (under the promotion lock: a writer that does not take it — a flux session's hand edits,
      // then the publisher — moved the base: `withRebases` prepares again, a bounded number of times)
      if (held) throw new HeldBaseMoved(out.why);
      return "base-moved";
    }
    // this very commit past its commit point (its line stopped, or its build killed): its files ARE installed
    const j = await readCommitJournal(cfg.toolkitRoot);
    if (j?.id === path.basename(C)) {
      throw new Error(`promotion: ${what}: commit ${j.id} installed its files in the shared toolkit, but ${j.stopped ? "Lake could not build it after them — the line is stopped" : "its build there did not finish"} (${out.why.split("\n")[0]}); CURRENT is unchanged and the toolkit stays in flux. ` +
        `${j.stopped ? `Settle it by hand: fix the tree and \`paperformalizer toolkit-commit clear ${j.id}\` (or \`undo\`)` : "The next holder of the promotion lock rolls it forward"}; the next apply then records the moves.`);
    }
    // (under the promotion lock: never waited for holding it — `withRebases` releases it and re-queues)
    if (held && !/line is stopped/.test(out.why)) {
      await rm(C, { recursive: true, force: true });
      throw new HeldWait(out.why);
    }
    if (/line is stopped/.test(out.why) || waited >= LOCAL_MOVES.waitMaxMs) {
      // (2026-11-11) refused: its archive goes now (a re-run prepares anew); the rest of `C` stays a day
      await dropArchive(cfg.toolkitRoot, C);
      throw new Error(`promotion: ${what} passed their checks but could not be committed (${out.why}); nothing of them reached the shared toolkit — re-run the apply once it can (the prepared commit ${C}, its archive removed, is removed after a day)`);
    }
    log(`promotion: commit waits — ${out.why}`);
    await sleep(LOCAL_MOVES.waitPollMs);
  }
}

/**
 * Rebases first without the locks, then (`LOCAL_MOVES.rebasesBeforeLock`) under the promotion lock
 * ALONE: the attempt re-pins, prepares, builds and gates in its workspace holding only it (`held`),
 * and the exclusive Lake hold is taken by the commit for its checks and install, as by any commit
 * (`commitToolkit` `held: "promotion"`) — papers' builds in the shared tree go on meanwhile.
 *
 * Why the promotion lock alone pins the base. Every writer that moves `CURRENT` along a toolkit
 * change of its own takes it: a commit (`commitToolkit`, `toolkit-commit recover|undo|clear`) and
 * the roll-forward of a commit on file (`honourCommit`, under it). The writers that do not take it: a flux session's hand edits
 * (`toolkit-flux on|off`: gardening's carry-out, a library check's repair, a git checkout of the
 * library; the `docstrings` pass, `withToolkitFlux`), a hand edit without one, the stamp its
 * `toolkit-flux off` writes, and the publisher (`toolkit-gen publish`: the clean toolkit as it stands,
 * under a Lake hold) — which publishes nothing unless such a writer changed the tree. Each of them
 * the commit's own base checks catch, under its exclusive hold: `CURRENT` not the base → base-moved;
 * a flux session open → wait; the live signature not `CURRENT`'s → base-moved when stamped clean (it
 * publishes it), else wait; a file it writes changed since read → base-moved.
 *
 * Liveness. A base-moved under the lock is prepared again under it, `LOCAL_MOVES.baseMovedUnderLock`
 * times at most: then refused (`refuse`, default a throw), naming what moved it. A wait is never
 * waited for holding the lock: released, and the rebase cycle starts again from the top (a re-pin
 * and a re-seed: cheap), after `waitPollMs`; past `waitMaxMs` of waits, refused (a flux session that
 * lasts hours ends in a refusal, not a spin).
 */
export async function withRebases<T>(
  cfg: ToolkitConfig, log: (m: string) => void, what: string, attempt: (held: boolean) => Promise<T | "base-moved">,
  refuse: (why: string) => T = (why) => { throw new Error(why); },
): Promise<T> {
  const movedUnderLock: string[] = [];
  let waitingSince: number | null = null;
  for (let rebases = 0; ; rebases += 1) {
    const underLock = rebases >= LOCAL_MOVES.rebasesBeforeLock;
    if (underLock) log(`promotion: ${rebases} rebases — ${what} prepared under the promotion lock this time`);
    let r: T | "base-moved";
    try {
      r = underLock
        ? await withPromotionLock(cfg.toolkitRoot, async () => {
          // (a commit on file finished first)
          await honourCommit(cfg.toolkitRoot, log);
          return attempt(true);
        }, cfg.lockPath, log)
        : await attempt(false);
    } catch (err) {
      if (err instanceof HeldBaseMoved) {
        movedUnderLock.push(err.why);
        if (movedUnderLock.length >= LOCAL_MOVES.baseMovedUnderLock) {
          return refuse(`promotion: ${what}: the toolkit moved on ${movedUnderLock.length} times under the promotion lock, by a writer that does not take it (a flux session's hand edits and the publisher, or a hand edit): ${movedUnderLock.join("; ")} — refused, nothing committed; the owner's to settle (end those edits, then re-run)`);
        }
        log(`promotion: ${what}: the toolkit moved on under the promotion lock (${err.why}) — a writer outside it; prepared again`);
        continue;
      }
      if (err instanceof HeldWait) {
        waitingSince ??= Date.now();
        const waited = Date.now() - waitingSince;
        if (waited >= LOCAL_MOVES.waitMaxMs) {
          return refuse(`promotion: ${what}: its commit has waited ${Math.round(waited / 60_000)} min (${err.why}) — refused, nothing committed; the owner's to settle (a flux session or a hand edit left open: close it, then re-run)`);
        }
        log(`promotion: ${what}: the commit must wait (${err.why}) — the promotion lock released; the rebase cycle starts again`);
        await sleep(LOCAL_MOVES.waitPollMs);
        rebases = -1;
        continue;
      }
      throw err;
    }
    if (r !== "base-moved") return r;
    log(`promotion: the toolkit moved on while ${what} were prepared — prepared again on the new generation`);
  }
}

/**
 * A generalized result's corollary re-proof (`reproveAsCorollary`) in the run's workspace, then
 * committed (the paper's file alone): whether it held. On a rebase the agent's file is reused when
 * the paper's file is still as the agent read it (its build and the statement check run again).
 * The agent never runs under a lock: an under-lock attempt (`withRebases`' fallback, the promotion
 * lock) whose paper file changed releases it ("ask-again"), the agent is asked
 * outside and the rebases start again. Every run of the agent after the first (the paper's file
 * changed since it read it, on any attempt) is a re-ask; past `LOCAL_MOVES.reasksBeforeRefusal`,
 * refused (`why`: the paper keeps its own proof, the owner's to settle). (2026-11-11: re-asks on
 * every attempt counted, so 4 rebases cost no more agent runs than 2 did.)
 * The workspace's generation must hold the general result: the start waits for the published
 * generation to be the clean toolkit's (the study's promotion published).
 */
export async function localCorollary(a: {
  cfg: ToolkitConfig; d: ApplyDeps; qid: string; log: (m: string) => void; paperModule: string; leanSubdir: string;
  proposalId: string; decl: string; file: string; general: { name: string; module: string };
  deps?: Partial<CorollaryDeps>; scans: boolean; scanFile: (when: "before" | "after") => string;
}): Promise<{ ok: boolean; cleared: string[]; why?: string }> {
  const { cfg, d, qid, log } = a;
  await untilPublished(cfg, log);
  const rel = path.relative(cfg.toolkitRoot, a.file);
  const what = `${a.proposalId}'s corollary`;
  // the agent's file, and the paper file's bytes it read
  let saved: string | null = null;
  let readBy: string | null = null;
  let reasks = 0;
  type Done = { ok: boolean; cleared: string[]; why?: string };
  const refused = (): Done => {
    const why = `${what}: the paper's file changed again on every generation, also after ${reasks} re-asks of the agent outside the locks (it never runs under them): refused, nothing committed — the paper keeps its own proof; the owner's to settle (rerun the corollary when the paper is quiet)`;
    log(why);
    return { ok: false, cleared: [], why };
  };
  // `P` the attempt's (its lock, `withPromoWorkspace`) until the commit is prepared
  const attempt = async (held: boolean): Promise<Done | "base-moved" | "ask-again"> => {
    const r = await withPromoWorkspace(cfg.toolkitRoot, qid, [a.paperModule], { log, ...heldPrepare(held) }, (w) => prepareIn(held, w));
    if (typeof r === "string" || !("C" in r)) return r;
    const out = await commitPrepared(cfg, r.C, held, log, `${a.proposalId}'s corollary`);
    if (out === "base-moved") return out;
    log(`${a.proposalId}: the corollary committed as generation ${out.gen}`);
    return { ok: true, cleared: r.cleared };
  };
  const prepareIn = async (held: boolean, w: { path: string }): Promise<Done | "ask-again" | { C: string; cleared: string[] }> => {
    const cfgP = cfgAt(cfg, w.path);
    const fileP = path.join(w.path, rel);
    const basis = await readFile(fileP, "utf8");
    const reuse = saved !== null && basis === readBy;
    if (!reuse && held) {
      log(`${a.proposalId}: the paper's file changed since the corollary agent read it; the agent never runs under the locks — releasing them`);
      return "ask-again";
    }
    if (!reuse && readBy !== null) {
      if (reasks >= LOCAL_MOVES.reasksBeforeRefusal) return refused();
      reasks += 1;
      log(`${a.proposalId}: the paper's file changed since the corollary agent read it — the agent is asked again outside the locks (re-ask ${reasks})`);
    }
    const fpBefore = a.scans ? await takeFingerprints(d, cfgP, a.paperModule, a.scanFile("before"), []) : null;
    const cleared = fpBefore ? await receiptsBefore(cfg, qid, leanTheoremDir(cfg.toolkitRoot, a.leanSubdir), a.scanFile("before")) : [];
    if (!reuse) { saved = null; readBy = basis; }
    const r = await reproveAsCorollary({
      toolkit: cfgP, qid, proposalId: a.proposalId, decl: a.decl, file: fileP, general: a.general, log,
      deps: { ...a.deps, ...(reuse ? { runCodex: (async () => { await writeTextAtomic(fileP, saved!); return { stdout: "", stderr: "" }; }) as never } : {}) },
      ...(fpBefore ? {
        verify: async () => {
          const after = await takeFingerprints(d, cfgP, a.paperModule, a.scanFile("after"), []);
          return after ? statementInvarianceFailure(fpBefore, after) : "the scan after the re-proof reported no statement hashes";
        },
      } : {}),
    });
    if (!r.ok) return { ok: false, cleared: [] };
    saved = await readFile(fileP, "utf8");
    return { C: await prepareCommit(cfg.toolkitRoot, w.path, { log }), cleared };
  };
  // (an under-lock attempt that must ask again: the locks released, the rebases start again —
  // the re-ask itself is counted where the agent runs)
  for (;;) {
    const r = await withRebases(cfg, log, what, attempt, (why) => { log(why); return { ok: false, cleared: [], why }; });
    if (r !== "ask-again") return r;
    log(`${a.proposalId}: the locks released — the corollary agent is asked again outside them`);
  }
}

/** Until the published generation is the clean toolkit's (`LOCAL_MOVES` bounds the wait; past it
 *  the workspace takes what is published, and a corollary that needs more fails its build). */
async function untilPublished(cfg: ToolkitConfig, log: (m: string) => void): Promise<void> {
  for (let waited = 0; waited < LOCAL_MOVES.waitMaxMs; waited += LOCAL_MOVES.waitPollMs) {
    const [cur, clean] = await Promise.all([currentGeneration(cfg.toolkitRoot), stampedClean(cfg.toolkitRoot)]);
    if (!cur || !("sig" in clean) || clean.sig === cur.sig) return;
    if (waited === 0) log(`promotion: waiting for the toolkit's generation to be published (generation ${cur.gen} is behind its clean state)`);
    await sleep(LOCAL_MOVES.waitPollMs);
  }
}

/** A landed record written by the run itself (nothing to commit: every result covered, or none
 *  passed but some covered). */
async function landedRecord(a: LocalMovesArgs, P: string, batch: BatchRecord | null, covered: LocalLanded["covered"]): Promise<string> {
  const { writeJsonAtomic } = await import("../shared/json_atomic.js");
  const file = path.join(landedDir(a.cfg, a.qid), `covered-${Date.now().toString(36)}.json`);
  await writeJsonAtomic(file, { id: path.basename(file, ".json"), gen: null, left: [], record: { batch: batch ?? { passed: true, checked: false, moves: [] }, covered } satisfies LocalLanded, ws: P });
  return file;
}

/** The landed records on file for the run, oldest first (a run that died after its commit records
 *  them at its next apply). */
export async function landedRecords(cfg: ToolkitConfig, qid: string): Promise<Array<{ file: string; landed: LocalLanded }>> {
  const dir = landedDir(cfg, qid);
  const out: Array<{ file: string; landed: LocalLanded }> = [];
  for (const e of (await readdir(dir).catch(() => [] as string[])).filter((n) => n.endsWith(".json")).sort()) {
    const j = JSON.parse(await readFile(path.join(dir, e), "utf8")) as { record?: LocalLanded };
    if (j.record?.batch) out.push({ file: path.join(dir, e), landed: j.record });
  }
  return out;
}
