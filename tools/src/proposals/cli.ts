// `theoremchecker propose <slug>`: the owner's side of a promotion round (`--round A|B`; default:
// the round awaiting decisions, else B).
//
// Without `--apply`, (re)render the checklist from the batch JSON, keeping any decisions already
// written in it. With `--apply`, read the owner's decisions (refused while any item is pending) and
// carry them out — round A builds the accepted cited results in the toolkit and points the F1
// plan at them (`apply_a.ts`); round B moves or builds the accepted results (`apply_b.ts`) — record
// every decision in the ledger, and resume the verify run (round A: into F1.5; round B: it finishes).
//
// Mode follows the run: `--dry-run` is required for a dry-run state and refused for a live one
// (`dryRunRefusal`, the verify runner's rule). A dry run writes its checklist and ledger records
// only under `runs/<slug>/proposals/dry_run/`; the toolkit's `doc/` is never touched.
import { existsSync, mkdirSync, readFileSync, rmSync, utimesSync, writeFileSync } from "node:fs";
import { APPLY_BEAT_S, applyPidLine } from "../shared/run_heartbeat.js";
import { mkdir, readFile, rename } from "node:fs/promises";
import path from "node:path";
import { loadState, saveState } from "../state.js";
import { writeTextAtomic } from "../shared/json_atomic.js";
import { loadToolkitConfig, type ToolkitConfig } from "../toolkit/config.js";
import { assertToolkitLakefile } from "../toolkit/lakefile.js";
import { loadLedger } from "../toolkit/ledger.js";
import { dryRunRefusal } from "../verify/dry_run.js";
import { parseChecklist, pendingIds, recommendedDecisions, renderChecklist, setDecisions, type ChecklistDecision, type ItemRecommendation } from "./checklist.js";
import {
  batchPath,
  checklistPath,
  decisionsPath,
  isMoveDecision,
  proposalBatchSchema,
  proposalDecisionRecordSchema,
  proposalLedgerPath,
  proposalsRunDir,
  type ProposalDecisionRecord,
  type ProposalRound,
} from "./schema.js";
import { healthSummary, readToolkitGraph, toolkitHealth } from "./toolkit_graph.js";

export const PROPOSE_USAGE =
  "Usage: theoremchecker propose <slug> [--round A|B] [--apply [--recommended] | --reopen-deferred] [--toolkit <path>] [--dry-run]\n" +
  "  --reopen-deferred: propose again the round-B entries deferred for this run (with the current rules:\n" +
  "           a paper-shaped result in general form), as a new checklist for the owner\n" +
  "  --round: A = the cited results proposed after F1, B = the proved results proposed after the report\n" +
  "           (default: the round awaiting decisions, else B)\n" +
  "  without --apply: (re)render <toolkit>/doc/proposals/<slug>.<round>.md from the batch, keeping your decisions\n" +
  "  --apply: carry out the decisions (round A: build the accepted results in the toolkit; round B: move them,\n" +
  "           or build their general form), record every decision in the ledger, and resume the run\n" +
  "  --recommended (with --apply): every item still pending takes the agent's recommendation on it first\n" +
  "           (orch.mjs recommend; refused while an item has none) — a full-auto run's apply\n" +
  "  --dry-run (required for a dry-run verify run): checklist and ledger records under runs/<slug>/proposals/dry_run/";

export interface ProposeArgs {
  slug: string;
  round: ProposalRound | null;
  apply: boolean;
  /** `--recommended` (with `--apply`): the pending items take the agent's recommendations first. */
  recommended: boolean;
  reopenDeferred: boolean;
  toolkit: string | null;
  dryRun: boolean;
}

export function parseProposeArgs(argv: string[]): ProposeArgs {
  const args = [...argv];
  const take = (flag: string): boolean => {
    const i = args.indexOf(flag);
    if (i === -1) return false;
    args.splice(i, 1);
    if (args.includes(flag)) throw new Error(`${flag} given more than once\n${PROPOSE_USAGE}`);
    return true;
  };
  const value = (flag: string): string | null => {
    const i = args.indexOf(flag);
    if (i === -1) return null;
    const v = args[i + 1];
    if (v === undefined || v.startsWith("-")) throw new Error(`${flag} requires a value\n${PROPOSE_USAGE}`);
    args.splice(i, 2);
    return v;
  };
  const apply = take("--apply");
  const recommended = take("--recommended");
  if (recommended && !apply) throw new Error(`--recommended fills the pending decisions of an apply; it needs --apply\n${PROPOSE_USAGE}`);
  const reopenDeferred = take("--reopen-deferred");
  const dryRun = take("--dry-run");
  const toolkit = value("--toolkit");
  const round = value("--round");
  if (round !== null && round !== "A" && round !== "B") throw new Error(`--round ${round}: the rounds are A and B\n${PROPOSE_USAGE}`);
  if (reopenDeferred && (apply || round === "A")) throw new Error(`--reopen-deferred re-proposes round-B entries; it combines with neither --apply nor --round A\n${PROPOSE_USAGE}`);
  const [slug, extra] = args;
  if (!slug || slug.startsWith("-") || extra !== undefined) throw new Error(PROPOSE_USAGE);
  return { slug, round, apply, recommended, reopenDeferred, toolkit, dryRun };
}

export interface ProposeDeps {
  /** Resume the verify run (default: the `theoremchecker verify` CLI with `--resume`). */
  resumeVerify?: (argv: string[]) => Promise<void>;
  log?: (msg: string) => void;
  now?: () => Date;
  /** Apply overrides (gate commands, scan, lock, graph) for tests. */
  applyB?: Partial<Pick<import("./apply_b.js").ApplyRoundBArgs, "deps" | "scan" | "toolsDir" | "indexStep" | "withLock" | "graph" | "runStudy" | "corollary">>;
  /** Round-A apply overrides (tests). */
  applyA?: Partial<Pick<Parameters<typeof import("./apply_a.js").applyRoundA>[0], "runStudy" | "graph">>;
  /** `--reopen-deferred` overrides (tests: scan, graph, models). */
  reopen?: Partial<Pick<import("./round_b.js").RunRoundBArgs, "scan" | "graph" | "runCodex" | "runClaude">>;
}

/** The round-B entries of `slug` whose latest owner decision is `defer`: proposal id → declaration. */
export async function deferredEntries(cfg: ToolkitConfig, slug: string, dryRun: boolean): Promise<Map<string, string>> {
  const ledger = await loadLedger(proposalLedgerPath(cfg, slug, dryRun));
  const latest = new Map<string, ProposalDecisionRecord>();
  for (const r of ledger.decisions) {
    const p = proposalDecisionRecordSchema.safeParse(r);
    if (!p.success || p.data.slug !== slug || p.data.round !== "B") continue;
    latest.set(p.data.proposal_id, p.data);
  }
  const out = new Map<string, string>();
  for (const [id, r] of latest) {
    const ref = (r.proposal as { source?: { ref?: string } }).source?.ref;
    if (r.decision.kind === "defer" && ref) out.set(id, ref);
  }
  return out;
}

/** Why the last `--apply` of a run ended without applying its round (`runs/<slug>/proposals/apply_failed.json`):
 *  the page shows it to the owner and the agent's watcher returns on it. Removed by an apply that completes. */
export interface ApplyFailure { round: ProposalRound | null; at: string; message: string }
export function applyFailurePath(cfg: ToolkitConfig, slug: string): string {
  return path.join(proposalsRunDir(cfg, slug), "apply_failed.json");
}

/**
 * `theoremchecker propose`. An `--apply`, however it ends — refused before anything is read,
 * failed part-way, or done — leaves no `apply_<R>.pid` (the page writes one as it launches the
 * apply), and one that did not apply the round leaves why (`ApplyFailure`).
 */
export async function runProposeCli(argv: string[], deps: ProposeDeps = {}): Promise<void> {
  const parsed = parseProposeArgs(argv);
  if (!parsed.apply || parsed.dryRun) return propose(parsed, deps, () => undefined);
  const cfg = loadToolkitConfig({ explicit: parsed.toolkit });
  const dir = proposalsRunDir(cfg, parsed.slug);
  const failure = applyFailurePath(cfg, parsed.slug);
  let ended = false;
  const end = (): void => {
    ended = true;
    for (const r of parsed.round ? [parsed.round] : (["A", "B"] as const)) rmSync(path.join(dir, `apply_${r}.pid`), { force: true });
  };
  // The beat a page or a watcher on another machine of the mount reads the apply by.
  const beat = setInterval(() => {
    // (its own file only: the other round's may be another apply's, or a dead one's left behind)
    for (const r of ["A", "B"]) {
      const file = path.join(dir, `apply_${r}.pid`);
      try { if (Number(readFileSync(file, "utf8").trim().split(/\s+/)[0]) === process.pid) utimesSync(file, new Date(), new Date()); } catch { /* not there */ }
    }
  }, APPLY_BEAT_S * 1000);
  beat.unref();
  try {
    await propose(parsed, deps, () => { clearInterval(beat); end(); rmSync(failure, { force: true }); });
    if (!ended) end(); // (a round with nothing to decide)
  } catch (err) {
    // (an error after the round was applied is the resumed run's, not the apply's)
    if (!ended && existsSync(path.join(cfg.runsDir, parsed.slug))) {
      end();
      mkdirSync(dir, { recursive: true });
      const rec: ApplyFailure = { round: (parsed.round as ProposalRound | null) ?? null, at: (deps.now ?? (() => new Date()))().toISOString(), message: err instanceof Error ? err.message : String(err) };
      writeFileSync(failure, `${JSON.stringify(rec, null, 2)}\n`);
    }
    throw err;
  } finally {
    clearInterval(beat);
  }
}

async function propose(parsed: ReturnType<typeof parseProposeArgs>, deps: ProposeDeps, applyEnded: () => void): Promise<void> {
  const log = deps.log ?? ((m: string) => console.log(`[propose] ${m}`));
  const cfg = loadToolkitConfig({ explicit: parsed.toolkit });
  const { slug } = parsed;
  const state = await loadState(cfg.toolkitRoot, slug);
  if (!state.verify) throw new Error(`run ${slug} has no verify block; the promotion round belongs to verify runs`);
  const refusal = dryRunRefusal(state, parsed.dryRun);
  if (refusal) throw new Error(`propose ${slug}: ${refusal}`);
  if (parsed.reopenDeferred) {
    // A round waits in its phase: only a run at rest past its report can take one. Re-entered (a
    // Lean stage at work or halted), the phase is the re-formalization's, and round B follows it.
    if (state.verify.phase !== "done" && state.verify.phase !== "failed") {
      throw new Error(`propose ${slug} --reopen-deferred: the run is not finished (phase ${state.verify.phase}); finish it first — deferred entries are re-proposed on a run at rest past its report`);
    }
    const rec0 = state.verify.promotion;
    if (rec0?.status === "pending_user") throw new Error(`promotion round B of ${slug} is awaiting decisions; decide and apply it before re-opening deferred entries`);
    const deferred = await deferredEntries(cfg, slug, parsed.dryRun);
    if (deferred.size === 0) {
      log(`no round-B entry of ${slug} is deferred; nothing to re-open.`);
      return;
    }
    log(`re-opening ${deferred.size} deferred entr${deferred.size === 1 ? "y" : "ies"}: ${[...deferred.keys()].join(", ")}`);
    // The applied round's files stay on record; the re-opened round writes a fresh batch and checklist.
    const stamp = (deps.now ?? (() => new Date()))().toISOString().replace(/[:.]/g, "-");
    const keep = path.join(proposalsRunDir(cfg, slug), "history", stamp);
    for (const f of [batchPath(cfg, slug), decisionsPath(cfg, slug), checklistPath(cfg, slug, parsed.dryRun)]) {
      if (!existsSync(f)) continue;
      await mkdir(keep, { recursive: true });
      await rename(f, path.join(keep, path.basename(f)));
    }
    const { runRoundB } = await import("./round_b.js");
    const runCodex = deps.reopen?.runCodex ?? (await import("../shared/codex.js")).runCodex;
    const rec = await runRoundB({
      toolkit: cfg, qid: slug, dryRun: parsed.dryRun, runCodex, log, only: new Set(deferred.values()),
      ...(deps.now ? { now: deps.now } : {}), ...(deps.reopen?.runClaude ? { runClaude: deps.reopen.runClaude } : {}),
      ...(deps.reopen?.scan ? { scan: deps.reopen.scan } : {}), ...(deps.reopen?.graph ? { graph: deps.reopen.graph } : {}),
    });
    const after = await loadState(cfg.toolkitRoot, slug);
    after.verify!.promotion = rec;
    // (the phase a round waits in: the page and the runner read the round from it; the run was at rest)
    if (rec.status === "pending_user") after.verify!.phase = "proposals_B";
    await saveState(cfg.toolkitRoot, slug, after);
    log(rec.status === "pending_user"
      ? `re-proposed — decide each in ${rec.checklist_path}, then run: theoremchecker propose ${slug} --apply --toolkit ${cfg.toolkitRoot}${parsed.dryRun ? " --dry-run" : ""}`
      : "the re-opened entries are no longer proposed (see the batch's \"Not proposed\" reasons).");
    return;
  }
  const round: ProposalRound = parsed.round ?? (state.verify.promotion_a?.status === "pending_user" ? "A" : "B");
  const rec = round === "A" ? state.verify.promotion_a : state.verify.promotion;
  if (!rec) {
    throw new Error(
      round === "A"
        ? `run ${slug} has no round A (phase ${state.verify.phase}); it is held after F1.`
        : `run ${slug} has no promotion round B yet (phase ${state.verify.phase}); it starts after the V6 report of a full F run — ` +
          `\`theoremchecker verify ${state.verify.source.input} --slug ${slug} --resume\` starts it on a finished run.`,
    );
  }
  if (rec.status === "empty" || rec.status === "deferred") {
    log(`promotion round ${round} of ${slug} ${rec.status === "empty" ? "proposed nothing" : `was not held (${rec.reason ?? "deferred"})`}; nothing to decide.`);
    return;
  }
  if (!rec.batch_path || !existsSync(rec.batch_path)) throw new Error(`promotion round ${round} of ${slug}: batch file ${rec.batch_path ?? "(none)"} is missing`);
  const batch = proposalBatchSchema.parse(JSON.parse(await readFile(rec.batch_path, "utf8")));
  const cp = checklistPath(cfg, slug, parsed.dryRun, round);

  if (!parsed.apply) {
    let decisions: Record<string, ChecklistDecision> | undefined;
    if (existsSync(cp)) {
      try {
        decisions = parseChecklist(await readFile(cp, "utf8"), batch);
      } catch (err) {
        throw new Error(`not re-rendering ${cp}: it does not parse (${err instanceof Error ? err.message : String(err)}). Fix the named block, or delete the file to start from a blank checklist.`);
      }
    }
    const graph = await readToolkitGraph(cfg);
    await mkdir(path.dirname(cp), { recursive: true });
    await writeTextAtomic(cp, renderChecklist(batch, {
      toolkitRoot: cfg.toolkitRoot, dryRun: parsed.dryRun,
      ...(decisions ? { decisions } : {}),
      ...(graph ? { health: healthSummary(toolkitHealth(graph)) } : {}),
    }));
    const pending = decisions ? pendingIds(decisions, batch) : batch.proposals.filter((p) => p.verdict === "propose").map((p) => p.id);
    log(`rendered ${cp} (${pending.length} pending${pending.length ? `: ${pending.join(", ")}` : ""})`);
    return;
  }

  if (rec.status === "applied") {
    applyEnded(); // (no failed apply: the round is applied)
    throw new Error(`promotion round ${round} of ${slug} was already applied at ${rec.applied_at}; continue the run with \`theoremchecker verify ${state.verify.source.input} --slug ${slug} --resume\`.`);
  }
  if (parsed.recommended) {
    // a full-auto run's apply: what is still pending takes the agent's recommendation, written into
    // the checklist (checked by its own parser first) as the page's "Accept all recommendations" does
    const text = await readFile(cp, "utf8");
    let recs: Record<string, ItemRecommendation> = {};
    try { recs = JSON.parse(await readFile(path.join(proposalsRunDir(cfg, slug), `${round}.recommendations.json`), "utf8")); } catch { /* none given */ }
    const { decisions, missing } = recommendedDecisions(batch, parseChecklist(text, batch), recs);
    if (missing.length) throw new Error(`--recommended: no recommendation on ${missing.join(", ")} as it stands — recommend on each (orch.mjs recommend ${slug} … ${round} <id> <kind> "<why>") first`);
    const next = setDecisions(text, decisions);
    parseChecklist(next, batch);
    await writeTextAtomic(cp, next);
    log(`--recommended: ${Object.keys(decisions).length} pending item(s) take the agent's recommendation`);
  }
  const { applyRoundB, readOwnerDecisions } = await import("./apply_b.js");
  // Decisions are checked (pending refused) before anything expensive.
  const owner = await readOwnerDecisions(cfg, slug, batch, parsed.dryRun);
  if (!parsed.dryRun && Object.values(owner).some(isMoveDecision)) assertToolkitLakefile(cfg);
  const fresh = await loadState(cfg.toolkitRoot, slug);
  let summary: { decisions: Record<string, { kind: string }>; promoted: string[]; regressions: string[] };
  // The apply at work, for the page: it shows "applying", not "needs you", while this process lives.
  const applying = path.join(proposalsRunDir(cfg, slug), `apply_${round}.pid`);
  if (!parsed.dryRun) { await mkdir(path.dirname(applying), { recursive: true }); writeFileSync(applying, applyPidLine(process.pid)); }
  try {
  if (round === "A") {
    const { applyRoundA } = await import("./apply_a.js");
    const result = await applyRoundA({ toolkit: cfg, qid: slug, batchFile: rec.batch_path, dryRun: parsed.dryRun, log, ...(deps.now ? { now: deps.now } : {}), ...(deps.applyA ?? {}) });
    const after = await loadState(cfg.toolkitRoot, slug);
    after.verify!.promotion_a = { ...rec, status: "applied", applied_at: result.decisions.decided_at, promoted: result.promoted };
    await saveState(cfg.toolkitRoot, slug, after);
    summary = { decisions: result.decisions.decisions, promoted: result.promoted, regressions: result.regressions };
  } else {
    const result = await applyRoundB({ toolkit: cfg, qid: slug, batchFile: rec.batch_path, dryRun: parsed.dryRun, log, ...(deps.now ? { now: deps.now } : {}), ...(deps.applyB ?? {}) });
    const after = await loadState(cfg.toolkitRoot, slug);
    after.verify!.promotion = { ...rec, status: "applied", applied_at: result.decisions.decided_at, promoted: result.promoted, moves: result.moves };
    await saveState(cfg.toolkitRoot, slug, after);
    summary = { decisions: result.decisions.decisions, promoted: result.promoted, regressions: result.regressions };
  }
  } finally {
    rmSync(applying, { force: true });
  }
  applyEnded();
  const counts = Object.values(summary.decisions).reduce<Record<string, number>>((acc, d) => ({ ...acc, [d.kind]: (acc[d.kind] ?? 0) + 1 }), {});
  log(`promotion ${round} applied: ${Object.entries(counts).map(([k, n]) => `${n} ${k}`).join(", ")}; ${summary.promoted.length} declaration(s) entered the toolkit`);
  if (summary.regressions.length) log(`toolkit graph afterwards (for the owner, not undone): ${summary.regressions.join("; ")}`);

  const resumeArgv = [
    fresh.verify!.source.input, "--slug", slug, "--toolkit", cfg.toolkitRoot, "--resume",
    ...(fresh.auto_mode ? ["--auto"] : []), ...(parsed.dryRun ? ["--dry-run"] : []),
  ];
  log(`resuming the run: theoremchecker verify ${resumeArgv.join(" ")}`);
  const resume = deps.resumeVerify ?? (async (a: string[]) => (await import("../verify/cli.js")).runVerifyCli(a));
  await resume(resumeArgv);
}

export const TOOLKIT_HEALTH_USAGE =
  "Usage: theoremchecker toolkit-health [--toolkit <path>] [--all] [--json] [--no-rebuild]\n" +
  "  re-derive <toolkit>/doc/toolkit_graph.json from the Lean (one `lake exe candidate_scan -- --graph` pass)\n" +
  "  and report the toolkit's health on its main results (--all: helpers too); --no-rebuild reads the graph on file";

/** `theoremchecker toolkit-health`: the graph and its measures. Gardening findings are suggestions. */
export async function runToolkitHealthCli(argv: string[], log: (m: string) => void = (m) => console.log(m)): Promise<void> {
  const i = argv.indexOf("--toolkit");
  const cfg = loadToolkitConfig({ explicit: i >= 0 ? argv[i + 1] ?? null : null });
  const { refreshToolkitGraph } = await import("./toolkit_graph.js");
  const graph = argv.includes("--no-rebuild")
    ? await readToolkitGraph(cfg)
    : await refreshToolkitGraph({ toolkit: cfg, log });
  if (!graph) throw new Error(`no toolkit graph on file; run without --no-rebuild\n${TOOLKIT_HEALTH_USAGE}`);
  const health = toolkitHealth(graph, { view: argv.includes("--all") ? "full" : "main" });
  const { readReuseHistory, reuseTrendText } = await import("./garden.js");
  const history = await readReuseHistory(cfg);
  log(argv.includes("--json") ? JSON.stringify({ ...health, reuse_history: history }, null, 2) : `${healthSummary(health)}\n${reuseTrendText(history)}`);
}

export const GARDEN_USAGE =
  "Usage: theoremchecker garden [--toolkit <path>] [--no-rebuild] [--dry-run]\n" +
  "       theoremchecker garden --verify <toolkit>/doc/proposals/garden-<stamp>.md [--items g-1,g-4] [--toolkit <path>]\n" +
  "  without --verify: re-derive the toolkit graph (unless --no-rebuild) and write gardening suggestions\n" +
  "  (one Claude call) for the orchestrator to decide (an item that retires or removes a result goes to the\n" +
  "  owner). The orchestrator carries out each ACCEPTED item by editing the\n" +
  "  Lean (the toolkit committed first); --verify then checks the edits against the committed toolkit and\n" +
  "  records them in the ledger (--items: the accepted items carried out; default every accepted item)";

/** `theoremchecker garden`: suggestions from the toolkit's graph, or the hand-applied items verified. */
export async function runGardenCli(argv: string[], log: (m: string) => void = (m) => console.log(`[garden] ${m}`)): Promise<void> {
  const value = (flag: string): string | null => {
    const i = argv.indexOf(flag);
    if (i < 0) return null;
    const v = argv[i + 1];
    if (!v || v.startsWith("--")) throw new Error(`${flag} needs a value\n${GARDEN_USAGE}`);
    return v;
  };
  if (argv.includes("--apply")) {
    throw new Error(`garden --apply is gone: carry out each accepted item by editing the Lean (the toolkit committed first), then run garden --verify <checklist>\n${GARDEN_USAGE}`);
  }
  const cfg = loadToolkitConfig({ explicit: value("--toolkit") });
  const garden = await import("./garden.js");
  const verify = value("--verify");
  if (verify) {
    assertToolkitLakefile(cfg);
    const { verifyGarden } = await import("./garden_verify.js");
    const items = value("--items")?.split(",").map((x) => x.trim()).filter(Boolean);
    const r = await verifyGarden({ toolkit: cfg, md: path.resolve(verify), log, ...(items ? { items } : {}) });
    for (const p of r.problems) log(`FAIL ${p}`);
    for (const g of r.regressions) log(`toolkit graph: ${g}`);
    if (r.renames.size) log(`renamed: ${[...r.renames].map(([a, b]) => `${a} → ${b}`).join(", ")}`);
    if (r.moved.size) log(`moved: ${[...r.moved].map(([a, m]) => `${a} → ${m}`).join(", ")}`);
    log(r.ok
      ? `verified against ${r.baseline.slice(0, 7)}; ${r.recorded} decision(s) recorded in the ledger — commit the toolkit`
      : `NOT verified (${r.problems.length} problem(s); logs in ${r.logDir}) — fix the edits, or revert them with git to ${r.baseline.slice(0, 7)}`);
    if (!r.ok) process.exitCode = 1;
    return;
  }
  const { refreshToolkitGraph } = await import("./toolkit_graph.js");
  const graph = argv.includes("--no-rebuild") ? await readToolkitGraph(cfg) : await refreshToolkitGraph({ toolkit: cfg, log });
  if (!graph) throw new Error(`no toolkit graph on file; run without --no-rebuild\n${GARDEN_USAGE}`);
  const out = await garden.runGardenRound({ toolkit: cfg, graph, log, dryRun: argv.includes("--dry-run") });
  if (out) log(`decide each item in ${out.path} (retire/remove items go to the owner); carry out the accepted ones by hand, then: theoremchecker garden --verify ${out.path} --toolkit ${cfg.toolkitRoot}`);
}
