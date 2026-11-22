// A study's coordinate step prepared in a private workspace and committed briefly (`shared/commit.ts`). Every study's coordinate step takes
// this path (`pipeline.ts`).
//
// Each study commits alone: no cross-run batch. Every study's gate runs in a workspace of its own,
// beside the others', and only the commit — about a minute — is shared, so there is nothing to
// amortize, and a study's failing manifest never undoes another's (round B made the same choice).
//
// The step: a workspace `P` (`prepareWorkspace(<toolkit>, <study's run id>)`), pinned to the current
// generation; the coordinator agent runs against `P` — a stable snapshot, never a tree in motion —
// and stages its bodies as always; its manifest is applied and gated in `P` (`applyManifest` with the
// config rebased to `P`, a journal of its own, the staging kept); a declaration it adds that the
// base already states (the scan's statement hash) refuses the step, for the owner (escalated, as a
// round-B duplicate is refused); then `commitToolkit`. Base-moved: prepared again on the new
// generation — the same manifest re-applied when every file it writes still has the bytes the agent
// read, else the agent asked again; after `LOCAL_MOVES.rebasesBeforeLock` rebases, under the promotion
// lock (`withRebases`) — but the agent never runs under it: an under-lock attempt whose targets changed releases it,
// the agent is asked outside and the rebases start again (`LOCAL_MOVES.reasksBeforeRefusal` re-asks, then refused for the owner).
// Landed: the staging sources removed (the shared staging tree: after the commit), then the landed
// record; a study that died after its commit finds its landed record (`runs/<id>/proposals/landed/`)
// at its next attempt and records it (the one mechanism: no staging and no record is not landed — the
// normal path decides, and a step that truly landed is refused there, for the owner). A failing gate
// reaches nothing of the shared tree: the step fails, its log fed back to the agent (the pipeline's
// retry).
// `P` stays for a rebase or a retry; once the step ends for good (committed, refused, halted) the
// pipeline releases it on this machine (`workspace.releaseStudyPromo`, 2026-11-11).
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { mkdir, readdir, readFile, rm, unlink } from "node:fs/promises";
import path from "node:path";
import { realApplyDeps as gateApplyDeps } from "../proposals/gate.js";
import { cfgAt, commitPrepared, heldPrepare, LOCAL_MOVES, withRebases } from "../proposals/local_moves.js";
import { duplicateStatementHash, type ToolkitGraph } from "../proposals/toolkit_graph.js";
import { withPromotionLock } from "../shared/build_mutex.js";
import { commitOnFile, honourCommit, prepareCommit, withPromoWorkspace } from "../shared/commit.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { loadLedger } from "../toolkit/ledger.js";
import { coordinateStagingDir, realApplyDeps, removeStaging, type CoordinateArgs, type CoordinateApplyDeps, type CoordinateDeps } from "./coordinate.js";
import { studyRunId, substrateRunDir } from "./paths.js";

/** The name of the error `recheckPaperNames` refuses with (matched by name: a module of another load). */
const PAPER_NAME_CLASH = "PaperNameClash";
import type { CoordinationManifest } from "./types.js";

/** What a study's landed record holds (`CommitRecord.record`). */
export interface StudyLandedRecord { kind: "study"; slug: string; round: number; requirementVersion: number; decls: string[] }

export interface LocalCoordinateDeps extends CoordinateDeps {
  log?: (msg: string) => void;
  /** The toolkit graph of the workspace's toolkit (the duplicate check; tests), or null. Default:
   *  re-derived there (`refreshToolkitGraph`, the toolkit alone). */
  graphIn?: (cfgP: ToolkitConfig) => Promise<ToolkitGraph | null>;
}

const sha256 = (text: string) => createHash("sha256").update(text, "utf8").digest("hex");

// compat 2026-11-11: remove after the processes started before this merge have exited (≤2 days)
// (a `coordinate_batch.ts` loaded before the merge asks for it and takes this path when it exists)
export const localCommitStudiesSwitch = (cfg: Pick<ToolkitConfig, "toolkitRoot">) => path.join(cfg.toolkitRoot, ".lake", "paperformalizer", "local-commit-studies");

/** Each file a manifest writes (relative to the toolkit) and the sha256 of its bytes in `cfg`'s tree
 *  (null: absent). */
async function targetsIn(cfg: ToolkitConfig, manifest: CoordinationManifest): Promise<Map<string, string | null>> {
  const out = new Map<string, string | null>();
  for (const op of manifest.ops) {
    const abs = path.resolve(cfg.toolkitRoot, op.target);
    out.set(op.target, existsSync(abs) ? sha256(await readFile(abs, "utf8")) : null);
  }
  return out;
}

/** The landed records of the study on file (its run directory's), for this attempt. */
async function landedOf(cfg: ToolkitConfig, args: CoordinateArgs): Promise<string[]> {
  const dir = path.join(substrateRunDir(cfg.toolkitRoot, args.slug), "proposals", "landed");
  const out: string[] = [];
  for (const e of (await readdir(dir).catch(() => [] as string[])).filter((n) => n.endsWith(".json"))) {
    const j = JSON.parse(await readFile(path.join(dir, e), "utf8")) as { record?: Partial<StudyLandedRecord> };
    if (j.record?.kind === "study" && j.record.round === args.round && j.record.requirementVersion === (args.requirementVersion ?? 0)) out.push(path.join(dir, e));
  }
  return out;
}

/** One coordinate attempt of a study through a private workspace and a commit (see the header). */
export async function localCoordinate(args: CoordinateArgs, deps: LocalCoordinateDeps): Promise<{ ok: boolean; log: string; timedOut?: boolean; conflict?: boolean }> {
  const cfg = args.toolkit;
  const root = cfg.toolkitRoot;
  const log = deps.log ?? ((m: string) => console.log(`[study] ${m}`));
  const d: CoordinateApplyDeps = deps.applyDeps ?? realApplyDeps;
  const runId = studyRunId(args.slug);
  // Landed: the staging removed FIRST, then the landed records — a death between the two leaves the
  // record, and the next attempt records the step from it (never the agent again on a base that
  // already has the study).
  const done = async (why: string) => {
    await removeStaging(args.leanFiles, d);
    for (const f of await landedOf(cfg, args)) await unlink(f).catch(() => {});
    return { ok: true, log: why };
  };
  // A commit of this attempt landed before the last run ended: recorded (its staging removed).
  if ((await landedOf(cfg, args)).length) {
    log(`${args.slug}: its coordinate step was committed before the last run ended — recording it`);
    return done("[coordinate] committed (recorded from its landed record).");
  }
  // A commit on file (another's, or this study's interrupted after its commit point): finished first.
  if (await commitOnFile(root)) await withPromotionLock(root, () => honourCommit(root, log), cfg.lockPath, log);
  if ((await landedOf(cfg, args)).length) return localCoordinate(args, deps);
  const stagingDir = coordinateStagingDir(args.runDir, args.round);
  let manifest: CoordinationManifest | null = null;
  let seen: Map<string, string | null> | null = null;
  // The coordinator agent never runs under a lock: an under-lock attempt (the promotion lock,
  // `withRebases`) whose targets changed releases it ("ask-again"), the agent is asked outside,
  // and the rebases start again. Every run of the agent after the first (its targets changed, on any
  // attempt) is a re-ask; past `LOCAL_MOVES.reasksBeforeRefusal`, refused for the owner (the shared
  // modules it writes keep moving under it). (2026-11-11: counted on every attempt, so 4 rebases
  // cost no more agent runs than 2 did.)
  const what = `${args.slug}'s coordinate step`;
  let asked = false;
  let reasks = 0;
  for (;;) {
    const r = await withRebases(cfg, log, what, attempt, (why) => ({ ok: false, conflict: true, log: `[coordinate] ${why}` }));
    if (r !== "ask-again") return r;
    log(`${args.slug}: the locks released — the coordinator is asked again outside them`);
  }

  type Done = { ok: boolean; log: string; conflict?: boolean };
  // `P` the attempt's (its lock, `withPromoWorkspace`) until the commit is prepared
  async function attempt(held: boolean): Promise<Done | "base-moved" | "ask-again"> {
    // (no paper copied, so nothing seeded from the study's own workspace: its gate builds the
    // toolkit's modules on the pinned generation, and its staging modules' outputs there are of
    // other module names — `prepareWorkspace` seeds whatever papers a prepare copies)
    const p = await withPromoWorkspace(root, runId, [], { log, ...heldPrepare(held) }, (w) => prepareIn(held, w));
    if (typeof p === "string" || !("C" in p)) return p;
    // (2026-11-11, step 2) the names it adds against the papers' sources, under the locks (it may land
    // on a later generation without a new prepare, after a long wait): one a paper declares refuses it
    // compat 2026-11-11: remove after the processes started before this merge have exited (≤2 days)
    // (read off the module, not imported by name: a `local_moves` loaded before the merge has none — then no re-check)
    const lm = (await import("../proposals/local_moves.js")) as Partial<typeof import("../proposals/local_moves.js")>;
    const recheck = lm.recheckPaperNames ? () => lm.recheckPaperNames!(cfg, p.C, [{ id: `${args.slug}'s coordinate step`, names: p.decls }], []) : undefined;
    let out: Awaited<ReturnType<typeof commitPrepared>>;
    try {
      // compat 2026-11-11: remove after the processes started before this merge have exited (≤2 days)
      // (the old arity: a `local_moves` loaded before the merge takes only it — and ignores `recheck`; the new one takes both)
      out = await commitPrepared(cfg, gateApplyDeps, p.C, held, log, `${args.slug}'s coordinate step`, recheck);
    } catch (err) {
      if (err instanceof Error && err.name === PAPER_NAME_CLASH) return { ok: false, conflict: true, log: `[coordinate] ${err.message}: refused, nothing committed — the owner's to settle` };
      throw err;
    }
    if (out === "base-moved") return out;
    log(`${args.slug}: its coordinate step committed as generation ${out.gen}${out.slow ? " (built for real in the shared tree)" : ""}`);
    return done(`${p.log}\n\n[coordinate] committed as generation ${out.gen}.`);
  }

  async function prepareIn(held: boolean, w: { path: string; gen: number }): Promise<Done | "ask-again" | { C: string; log: string; decls: string[] }> {
    const cfgP = cfgAt(cfg, w.path);
    // the agent's manifest, on this base: reused when every file it writes has the bytes it read
    if (manifest && seen) {
      const now = await targetsIn(cfgP, manifest);
      const moved = [...seen].find(([f, sha]) => now.get(f) !== sha);
      if (moved) {
        log(`${args.slug}: ${moved[0]} changed on the new generation since the coordinator read it — asking it again`);
        manifest = null;
      } else {
        log(`${args.slug}: every file the manifest writes is as the coordinator read it — re-applied on generation ${w.gen}`);
      }
    }
    if (!manifest && held) {
      log(`${args.slug}: the coordinator must be asked again, which never happens under the locks — releasing them`);
      return "ask-again";
    }
    if (!manifest && asked) {
      if (reasks >= LOCAL_MOVES.reasksBeforeRefusal) {
        return { ok: false, conflict: true, log: `[coordinate] ${what}: the files its manifest writes changed again on every generation, also after ${reasks} re-asks of the coordinator outside the locks (the agent never runs under them): refused, nothing committed — the owner's to settle (rerun the step when the shared modules it extends are quiet)` };
      }
      reasks += 1;
      log(`${args.slug}: the coordinator is asked again outside the locks (re-ask ${reasks})`);
    }
    if (!manifest) {
      asked = true;
      try {
        manifest = await deps.runCoordinator({
          toolkit: cfgP, toolsDir: args.toolsDir ?? (await import("../toolkit/config.js")).paperFormalizerToolsDir(), runDir: args.runDir, round: args.round,
          slug: args.slug, requirement: args.requirement, leanDir: args.leanDir, modulePrefix: args.modulePrefix, leanFiles: args.leanFiles,
          stagingDir, lastFailureLog: args.lastFailureLog,
        });
      } catch (err) {
        return { ok: false, log: `[coordinate] coordinator agent/parse failed: ${err instanceof Error ? err.message : String(err)}` };
      }
      seen = await targetsIn(cfgP, manifest);
    }
    const priv = path.join(w.path, ".pf-promo");
    await rm(priv, { recursive: true, force: true });
    await mkdir(priv, { recursive: true });
    const before = new Set((await loadLedger(cfgP.ledgerPath)).declarations.map((x) => x.name));
    const r = await deps.apply({
      toolkit: cfgP, toolsDir: args.toolsDir ?? (await import("../toolkit/config.js")).paperFormalizerToolsDir(), stagingDir, leanFiles: args.leanFiles, manifest,
      slug: args.slug, modulePrefix: args.modulePrefix, journalFile: path.join(priv, "coordinate_journal.json"), keepStaging: true,
      ...(args.provenance ? { provenance: args.provenance } : {}),
    }, d);
    // (a failure, rolled back in the workspace — or a gate killed there: nothing of it is shared)
    if (!r.ok) return { ok: false, log: `${r.log}\n\n[coordinate] in the workspace ${w.path}: nothing of it reached the shared toolkit.` };
    const decls = (await loadLedger(cfgP.ledgerPath)).declarations.map((x) => x.name).filter((n) => !before.has(n));
    // A theorem the base toolkit already states: refused, the owner's to decide. The graph hashes
    // only types, so a definition or inductive predicate needs more evidence than this scan has.
    const graphIn = deps.graphIn ?? (async (c: ToolkitConfig) => {
      const { refreshToolkitGraph } = await import("../proposals/toolkit_graph.js");
      return refreshToolkitGraph({ toolkit: c, log, scope: { qid: runId, papers: [] } });
    });
    const graph = await graphIn(cfgP).catch((err: unknown) => {
      log(`${args.slug}: toolkit graph of the workspace not built (${err instanceof Error ? err.message : String(err)}); no duplicate check`);
      return null;
    });
    if (graph) {
      const added = new Set(decls);
      const byHash = new Map(graph.nodes.filter((n) => n.layer === "toolkit" && duplicateStatementHash(n) && !added.has(n.id)).map((n) => [duplicateStatementHash(n)!, n.id] as const));
      const dup = graph.nodes.find((n) => added.has(n.id) && duplicateStatementHash(n) && byHash.has(duplicateStatementHash(n)!));
      if (dup) {
        return { ok: false, conflict: true, log: `[coordinate] \`${dup.id}\` is a duplicate of \`${byHash.get(dup.statement_hash!)}\` (statement hash match) in the toolkit of generation ${w.gen}: refused, nothing committed — the owner's to decide (the requirement again, or use \`${byHash.get(dup.statement_hash!)}\`)` };
      }
    }
    // (2026-11-11) what it adds, with the graph's statement hashes: for a later additive commit, inert
    // now; no graph, or one unknown: none
    const hashOf = new Map((graph?.nodes ?? []).filter((n) => n.layer === "toolkit" && n.statement_hash).map((n) => [n.id, n.statement_hash!] as const));
    const adds = decls.length && decls.every((n) => hashOf.has(n)) ? decls.map((name) => ({ name, hash: hashOf.get(name)! })) : null;
    const C = await prepareCommit(root, w.path, {
      ...(adds ? { adds } : {}), log, records: [{ slug: runId, record: { kind: "study", slug: args.slug, round: args.round, requirementVersion: args.requirementVersion ?? 0, decls } satisfies StudyLandedRecord }],
    });
    return { C, log: r.log, decls };
  }
}
