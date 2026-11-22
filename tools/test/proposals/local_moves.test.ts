// Round-B moves (`local_moves.ts`): prepared in the run's own workspace, gated there by the gate
// code against the config rebased to it, committed (`shared/commit.ts`). Lake and the scan are
// stand-ins on the files of the directory they run in (the shared tree or the workspace).
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { chmod, mkdir, mkdtemp, readdir, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterAll, afterEach, beforeAll, describe, expect, it } from "vitest";
import { applyRoundB, movesProgressPath, type ApplyRoundBArgs } from "../../src/proposals/apply_b.js";
import type { CandidateScan, ScanDecl } from "../../src/proposals/candidate_scan.js";
import { renderChecklist, setDecisions } from "../../src/proposals/checklist.js";
import { realApplyDeps, type ApplyDeps } from "../../src/proposals/gate.js";
import { landedDir, LOCAL_MOVES, localCorollary } from "../../src/proposals/local_moves.js";
import { batchPath, checklistPath, proposalBatchSchema, proposalsRunDir, type ProposalBatch } from "../../src/proposals/schema.js";
import type { ToolkitGraph } from "../../src/proposals/toolkit_graph.js";
import { lakeHoldMode } from "../../src/shared/build_mutex.js";
import { toolkitLayout, toolkitSignature } from "../../src/shared/build_inputs.js";
import { clearCommit, COMMIT_LAKE, COMMIT_STEP, commitJournalFile, commitsDir, readCommitJournal, strictBaseSwitch } from "../../src/shared/commit.js";
import { writeTextAtomic } from "../../src/shared/json_atomic.js";
import { addsRecordFile, currentGeneration, gensDir, publishGeneration } from "../../src/shared/workspace.js";
import { createVerifyInitialState, saveState } from "../../src/state.js";
import { declarationSpans } from "../../src/toolkit/lean_source.js";
import { loadLedger } from "../../src/toolkit/ledger.js";
import { writeSkeleton } from "../toolkit/helpers.js";
import { PAPER_MAIN } from "./helpers.js";

const haveTools = (() => { try { execFileSync("bash", ["-c", "command -v zstd && command -v flock"]); return true; } catch { return false; } })();
const tmp: string[] = [];
let bin: string;
let PATH: string | undefined;
const realLake = COMMIT_LAKE.run;
const realStep = COMMIT_STEP.at;
const timing = { ...LOCAL_MOVES };
beforeAll(async () => {
  bin = await mkdtemp(path.join(os.tmpdir(), "local-moves-bin-"));
  await writeFile(path.join(bin, "lean"), "#!/bin/sh\necho 'Lean (version 4.0.0, test)'\n");
  await chmod(path.join(bin, "lean"), 0o755);
  PATH = process.env.PATH;
  process.env.PATH = `${bin}:${PATH}`;
  COMMIT_LAKE.run = async () => ({ code: 0, out: "All targets up-to-date" });
});
afterAll(async () => {
  process.env.PATH = PATH;
  COMMIT_LAKE.run = realLake;
  await rm(bin, { recursive: true, force: true });
});
afterEach(async () => {
  Object.assign(LOCAL_MOVES, timing);
  delete process.env.PAPERFORMALIZER_LEAN_LOCAL_ROOT;
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

const REF = "Papers.Fix.uses_k";
const NAME = "Toolkit.Tricks.Arith.le_succ_self";
const TARGET = "Toolkit/Tricks/Arith/Basic.lean";

function statementsIn(text: string): Array<[string, string]> {
  return declarationSpans(text).map((s) => {
    const stmt = text.slice(s.nameTo, s.to).split(":=")[0]!.replace(/\s+/g, " ").trim();
    return [s.name, createHash("sha256").update(stmt).digest("hex").slice(0, 16)];
  });
}
async function leanFilesUnder(dir: string): Promise<string[]> {
  const out: string[] = [];
  for (const e of await readdir(dir, { withFileTypes: true }).catch(() => [])) {
    const abs = path.join(dir, e.name);
    if (e.isDirectory()) out.push(...(await leanFilesUnder(abs)));
    else if (e.name.endsWith(".lean")) out.push(abs);
  }
  return out.sort();
}

type Fail = (cmd: string, cwd: string) => Promise<{ code: number; log: string; timedOut?: boolean } | null>;
/** Lake, the scan and the lints on the files of the directory they run in. */
function fakeLake(calls: Array<{ cmd: string; cwd: string }>, opts: { fail?: Fail; onRun?: (cmd: string, cwd: string) => Promise<void> } = {}): ApplyDeps {
  return {
    ...realApplyDeps,
    holdLake: async (_root, fn) => fn(),
    run: async (cmd, cwd) => {
      calls.push({ cmd, cwd });
      await opts.onRun?.(cmd, cwd);
      const failed = await opts.fail?.(cmd, cwd);
      if (failed) return failed;
      if (cmd.startsWith("lake env lean ")) {
        const probe = await readFile(cmd.slice("lake env lean ".length).replace(/^'|'$/g, ""), "utf8");
        return { code: 0, log: [...probe.matchAll(/#print axioms (\S+)/g)].map((m) => `'${m[1]}' depends on axioms: [propext]`).join("\n") };
      }
      if (cmd.startsWith("lake exe candidate_scan")) {
        const out = /--out '?([^' ]+)'?/.exec(cmd)![1]!;
        const paper = /--modules '?Toolkit,Papers\.(\w+)'?/.exec(cmd)![1]!;
        const files = [...(await leanFilesUnder(path.join(cwd, "Toolkit"))), ...(await leanFilesUnder(path.join(cwd, "Papers", paper)))];
        const declarations = [];
        for (const f of files) for (const [name, stmt_hash] of statementsIn(await readFile(f, "utf8"))) declarations.push({ name, stmt_hash });
        await writeFile(out, JSON.stringify({ declarations }));
        return { code: 0, log: "scanned" };
      }
      if (cmd.includes("toolkit_index")) await writeTextAtomic(path.join(cwd, "doc", "toolkit_index.json"), "{\"entries\":[]}\n");
      return { code: 0, log: "ok" };
    },
  };
}

/** A toolkit with generations on, and run `fix` with its accepted move, ready to apply. */
async function setup(opts: { fail?: Fail; onRun?: (cmd: string, cwd: string) => Promise<void>; graphIn?: ApplyRoundBArgs["graphIn"]; importsHix?: boolean } = {}) {
  const dir = await mkdtemp(path.join(os.tmpdir(), "local-moves-"));
  tmp.push(dir);
  const root = path.join(dir, "tk");
  process.env.PAPERFORMALIZER_LEAN_LOCAL_ROOT = path.join(dir, "local");
  const cfg = await writeSkeleton(root);
  await writeFile(path.join(root, "doc", "taxonomy.json"), JSON.stringify({ version: 1, topics: [{ path: "Arith", scope: "arithmetic facts" }] }));
  await mkdir(path.join(root, ".lake", "build", "lib", "lean"), { recursive: true });
  await writeFile(path.join(root, ".lake", "build", "lib", "lean", "Toolkit.olean"), "olean\n");
  const paperDir = path.join(root, "Papers", "Fix");
  await mkdir(paperDir, { recursive: true });
  const main = path.join(paperDir, "Main.lean");
  await writeFile(main, PAPER_MAIN);
  await writeFile(path.join(root, "Papers", "Fix.lean"), `module\n\npublic import Papers.Fix.Main\n${opts.importsHix ? "public import Papers.Hix.Main\n" : ""}`);
  if (opts.importsHix) {
    await mkdir(path.join(root, "Papers", "Hix"), { recursive: true });
    await writeFile(path.join(root, "Papers", "Hix", "Main.lean"), "module\n\n-- a paper Fix imports\n");
    await writeFile(path.join(root, "Papers", "Hix.lean"), "module\n\npublic import Papers.Hix.Main\n");
  }
  const qid = "fix";
  await saveState(root, qid, createVerifyInitialState(qid, {
    phase: "proposals_B", source: { input: "/p.tex", main_file: "main.tex", sha256: "x" }, targets: null, core_sha256: null,
    v1_rounds: 0, v1_5_rounds: 0, findings: [], report_path: null,
  }, cfg.papersLib));
  await writeFile(path.join(cfg.runsDir, qid, "report.json"), JSON.stringify({ results: [{ node_id: "thm:main", kind: "theorem", lean: { decl: "Papers.Fix.main_result" } }] }));
  const batch: ProposalBatch = proposalBatchSchema.parse({
    slug: qid, round: "B", created: "2026-11-10T12:00:00.000Z",
    proposals: [{
      id: "b-uses-k", round: "B", source: { kind: "paper_decl", ref: REF }, verdict: "propose", path: "move",
      title: "Title", reference: "standard", content: "A fact.", division: "Tricks", target_module: TARGET,
      new_module_overview: "Facts proved in a verified paper.", proposed_name: NAME,
      nearest_existing: [{ name: "Nat.le_succ", library: "Mathlib", why_not_same: "other" }], reuse_evidence: "reusable", moves_with: [],
    }],
  });
  await mkdir(proposalsRunDir(cfg, qid), { recursive: true });
  await writeFile(batchPath(cfg, qid), JSON.stringify(batch, null, 2));
  await mkdir(path.dirname(checklistPath(cfg, qid)), { recursive: true });
  await writeFile(checklistPath(cfg, qid), setDecisions(renderChecklist(batch, { toolkitRoot: root }), { "b-uses-k": { kind: "accept" as const } }));
  const decl = (name: string): ScanDecl => ({
    name, kind: "theorem", module: "Papers.Fix.Main", file: "Main.lean", line: 1, end_line: 2, is_private: false, type: "", doc: null,
    axioms: ["propext"], has_sorry: false, type_constants: [], body_constants: [{ name: "Nat.le_succ", class: "base", module: "Init.Prelude" }],
  });
  const scan: CandidateScan = { schema: 1, paper: "Papers.Fix", toolkit_prefix: "Toolkit", papers_prefix: "Papers", modules: [], declarations: [decl(REF), decl("Papers.Fix.main_result")] };
  // generations on, the first published
  await mkdir(gensDir(root), { recursive: true });
  await publishGeneration(root, await toolkitSignature(await toolkitLayout(root)), () => {});
  const calls: Array<{ cmd: string; cwd: string }> = [];
  const logs: string[] = [];
  const args: ApplyRoundBArgs = {
    toolkit: cfg, qid, batchFile: batchPath(cfg, qid), dryRun: false, log: (m) => logs.push(m), now: () => new Date("2026-11-10T12:30:00Z"),
    deps: fakeLake(calls, opts), scan: async () => scan, toolsDir: "/tools", graph: async () => null,
    indexStep: { label: "toolkit index", cmd: "lake exe toolkit_index", cwd: root },
    ...(opts.graphIn ? { graphIn: opts.graphIn } : {}),
  };
  return { root, cfg, qid, main, args, logs, calls };
}
type Setup = Awaited<ReturnType<typeof setup>>;

/** Every file of the shared tree's library and papers, and the ledger. */
async function snapshot(t: Setup): Promise<Record<string, string>> {
  const out: Record<string, string> = {};
  for (const f of [...(await leanFilesUnder(path.join(t.root, "Toolkit"))), ...(await leanFilesUnder(path.join(t.root, "Papers")))]) out[path.relative(t.root, f)] = await readFile(f, "utf8");
  out.ledger = await readFile(t.cfg.ledgerPath, "utf8");
  return out;
}
/** Another commit lands meanwhile: the shared toolkit gains a module, published as the next generation. */
async function anotherLands(t: Setup, n: number): Promise<void> {
  const f = path.join(t.root, "Toolkit", "Tricks", "Arith", `Other${n}.lean`);
  await mkdir(path.dirname(f), { recursive: true });
  await writeFile(f, `module\n\npublic section\n\nnamespace Toolkit.Tricks.Arith\n\ntheorem other_${n} : ${n} = ${n} := rfl\n\nend Toolkit.Tricks.Arith\n`);
  await publishGeneration(t.root, await toolkitSignature(await toolkitLayout(t.root)), () => {});
}
const inWorkspace = (t: Setup) => t.calls.filter((c) => c.cwd !== t.root && c.cwd.includes(`${path.sep}ws${path.sep}fix.promo`));
/** Whether the promotion lock is held (its lockfile directory; the queue's tickets go once it is taken). */
const promotionHeld = (t: Setup) => existsSync(`${t.cfg.lockPath}.lock`);

describe.skipIf(process.platform === "win32" || !haveTools)("round-B moves prepared locally and committed", () => {
  it("gates the run's moves in its workspace and commits them: the shared tree written only by the commit", async () => {
    const t = await setup();
    const before = await snapshot(t);
    let sharedSeenDuringGate: Record<string, string> | null = null;
    // (the gate's last step, in the workspace: everything written there by then)
    t.args.deps = fakeLake(t.calls, { onRun: async (cmd, cwd) => { if (cmd.includes("toolkit_index") && cwd !== t.root && !sharedSeenDuringGate) sharedSeenDuringGate = await snapshot(t); } });
    const r = await applyRoundB(t.args);
    expect(r.moves.map((m) => m.proposal_id)).toEqual(["b-uses-k"]);
    // compat 2026-11-11: remove after the processes started before this merge have exited (≤2 days)
    expect(r).toMatchObject({ libraryBreaks: [], libraryBreaksMaybeOlder: false });
    // the gate ran in the workspace and wrote nothing of the shared tree
    expect(sharedSeenDuringGate).toEqual(before);
    expect(inWorkspace(t).some((c) => c.cmd === "lake build Toolkit")).toBe(true);
    expect(t.calls.filter((c) => c.cwd === t.root && c.cmd === "lake build Toolkit")).toEqual([]);
    // landed: the module, the paper rewritten, a new generation; recorded as after a batch
    expect(await readFile(path.join(t.root, TARGET), "utf8")).toContain("theorem le_succ_self");
    expect(await readFile(t.main, "utf8")).not.toContain("theorem uses_k");
    expect((await currentGeneration(t.root))?.gen).toBe(2);
    const ledger = await loadLedger(t.cfg.ledgerPath);
    expect(ledger.declarations.map((d) => d.name)).toEqual([NAME]);
    expect((ledger.decisions as Array<{ proposal_id: string; promoted: string[] }>).map((x) => `${x.proposal_id}:${x.promoted.join(",")}`)).toEqual([`b-uses-k:${NAME}`]);
    expect(JSON.parse(await readFile(movesProgressPath(t.cfg, t.qid), "utf8"))).toHaveLength(1);
    expect(t.logs.some((l) => /moved and gated .* every statement unchanged/.test(l))).toBe(true);
    // no journal, no landed record left
    expect(existsSync(commitJournalFile(t.root))).toBe(false);
    expect(await readdir(landedDir(t.cfg, t.qid)).catch(() => [])).toEqual([]);
  });

  it("a move that fails its gate leaves the shared tree untouched", async () => {
    const t = await setup({ fail: async (cmd, cwd) => (cmd.startsWith("lake build Papers.Fix") && cwd !== t.root ? { code: 1, log: "error: Papers/Fix/Main.lean:30:2: unknown identifier" } : null) });
    const before = await snapshot(t);
    await expect(applyRoundB(t.args)).rejects.toThrow(/b-uses-k: the move did not pass its gate in the workspace[\s\S]*Nothing of it reached the shared toolkit/);
    expect(await snapshot(t)).toEqual(before);
    expect((await currentGeneration(t.root))?.gen).toBe(1);
    expect(existsSync(commitJournalFile(t.root))).toBe(false);
    expect((await loadLedger(t.cfg.ledgerPath)).decisions).toEqual([]);
  });

  it("a result its base toolkit already states (statement hash match) is refused as a duplicate, never dropped", async () => {
    const hash = "same-statement";
    const graphIn = async (): Promise<ToolkitGraph> => ({
      version: 1, built_at: "x", toolkit_prefix: "Toolkit", papers_prefix: "Papers", edges: [],
      nodes: [
        { id: "Toolkit.Tricks.Arith.le_succ_existing", layer: "toolkit", kind: "theorem", module: "Toolkit.Tricks.Arith.Basic", statement_hash: hash },
        { id: REF, layer: "paper", kind: "theorem", module: "Papers.Fix.Main", statement_hash: hash },
      ],
    });
    const t = await setup({ graphIn });
    const before = await snapshot(t);
    await expect(applyRoundB(t.args)).rejects.toThrow(/b-uses-k: duplicate of `Toolkit\.Tricks\.Arith\.le_succ_existing` \(statement hash match\)/);
    expect(await snapshot(t)).toEqual(before);
    expect((await currentGeneration(t.root))?.gen).toBe(1);
  });

  it("copies into the workspace the papers a moving paper imports", async () => {
    let seen = false;
    const t: Setup = await setup({ importsHix: true, onRun: async (cmd, cwd) => { if (cmd === "lake build Toolkit" && cwd !== t.root) seen = existsSync(path.join(cwd, "Papers", "Hix", "Main.lean")); } });
    const r = await applyRoundB(t.args);
    expect(r.moves).toHaveLength(1);
    expect(seen).toBe(true);
  });

  it("a commit interrupted after its commit point: the next apply rolls it forward under the lock first, then records it", async () => {
    const t = await setup();
    COMMIT_STEP.at = async (s) => { if (s === "sources") throw new Error("killed at sources"); };
    try {
      await expect(applyRoundB(t.args)).rejects.toThrow("killed at sources");
    } finally { COMMIT_STEP.at = realStep; }
    expect(existsSync(commitJournalFile(t.root))).toBe(true);
    const r = await applyRoundB(t.args);
    expect(r.moves.map((m) => m.proposal_id)).toEqual(["b-uses-k"]);
    expect(existsSync(commitJournalFile(t.root))).toBe(false);
    expect((await currentGeneration(t.root))?.gen).toBe(2);
    const ledger = await loadLedger(t.cfg.ledgerPath);
    expect(ledger.declarations.map((d) => d.name)).toEqual([NAME]);
    expect((ledger.decisions as Array<{ proposal_id: string }>).map((x) => x.proposal_id)).toEqual(["b-uses-k"]);
  });

  it("its own commit's line stopped: reported as installed; the next apply refuses over it; cleared, the next apply records it", async () => {
    const t = await setup();
    const lake = COMMIT_LAKE.run;
    COMMIT_LAKE.run = async (cwd, args) => (cwd === t.root ? { code: args.includes("--no-build") ? 3 : 1, out: "error: the shared tree does not build" } : { code: 0, out: "ok" });
    try {
      await expect(applyRoundB(t.args)).rejects.toThrow(/installed its files in the shared toolkit, but Lake could not build it after them — the line is stopped[\s\S]*toolkit-commit clear/);
    } finally { COMMIT_LAKE.run = lake; }
    const id = (await readCommitJournal(t.root))!.id;
    // the next apply honours the commit on file — it refuses, never builds over it
    await expect(applyRoundB(t.args)).rejects.toThrow(/no promotion goes on over it/);
    expect(await clearCommit(t.root, id, () => {})).toMatchObject({ kind: "landed" });
    const r = await applyRoundB(t.args);
    expect(r.moves.map((m) => m.proposal_id)).toEqual(["b-uses-k"]);
    expect(t.logs.some((l) => /is declared in a paper already|already declared/.test(l))).toBe(false);
    const ledger = await loadLedger(t.cfg.ledgerPath);
    expect(ledger.declarations.map((d) => d.name)).toEqual([NAME]);
    expect((ledger.decisions as Array<{ proposal_id: string; promoted: string[] }>).map((x) => `${x.proposal_id}:${x.promoted.join(",")}`)).toEqual([`b-uses-k:${NAME}`]);
  });

  it("prepares again on the new generation when another commit landed meanwhile (base-moved)", async () => {
    let landedOnce = false;
    const t: Setup = await setup({
      onRun: async (cmd, cwd) => {
        if (!landedOnce && cmd.includes("toolkit_index") && cwd !== t.root) { landedOnce = true; await anotherLands(t, 1); }
      },
    });
    const r = await applyRoundB(t.args);
    expect(r.moves.map((m) => m.proposal_id)).toEqual(["b-uses-k"]);
    expect(t.logs.filter((l) => /the toolkit moved on while fix's moves were prepared/.test(l))).toHaveLength(1);
    expect((await currentGeneration(t.root))?.gen).toBe(3);
    // both: the other commit's module and this one
    expect(existsSync(path.join(t.root, "Toolkit", "Tricks", "Arith", "Other1.lean"))).toBe(true);
    expect(await readFile(path.join(t.root, TARGET), "utf8")).toContain("theorem le_succ_self");
    expect(inWorkspace(t).filter((c) => c.cmd === "lake build Toolkit")).toHaveLength(2);
  });

  it("after four rebases, prepares under the promotion lock: it lands", async () => {
    let n = 0;
    const t: Setup = await setup({
      onRun: async (cmd, cwd) => {
        if (n < 4 && cmd.includes("toolkit_index") && cwd !== t.root) { n += 1; await anotherLands(t, n); }
      },
    });
    const r = await applyRoundB(t.args);
    expect(r.moves.map((m) => m.proposal_id)).toEqual(["b-uses-k"]);
    expect(t.logs.some((l) => /3 rebases — fix's moves prepared under the promotion lock/.test(l))).toBe(false);
    expect(t.logs.some((l) => /4 rebases — fix's moves prepared under the promotion lock this time/.test(l))).toBe(true);
    expect((await currentGeneration(t.root))?.gen).toBe(6);
    expect(await readFile(path.join(t.root, TARGET), "utf8")).toContain("theorem le_succ_self");
  });

  it.skipIf(!haveTools)("under the promotion lock, its workspace held by another process: a short wait, then HeldWait — the lock released, re-queued; it lands once P is free", async () => {
    LOCAL_MOVES.waitPollMs = 200;
    let n = 0;
    let holder: string | null = null;
    const free = () => { if (holder) execFileSync("bash", ["-c", `pkill -P "$1"; kill "$1" 2>/dev/null; true`, "_", holder]); holder = null; };
    const t: Setup = await setup({
      onRun: async (cmd, cwd) => {
        if (n < 4 && cmd.includes("toolkit_index") && cwd !== t.root) {
          n += 1;
          await anotherLands(t, n);
          // (another process for the same run: it takes P as soon as this attempt lets it go)
          if (n === 4) {
            const lockFile = path.join(path.dirname(t.root), "local", "ws", "fix.promo", ".pf-promo.flock");
            holder = execFileSync("bash", ["-c", `flock "$1" -c 'exec sleep 300' >/dev/null 2>&1 & echo $!`, "_", lockFile], { encoding: "utf8" }).trim();
          }
        }
      },
    });
    const log = t.args.log!;
    const heldAtRelease: boolean[] = [];
    t.args.log = (m: string) => {
      log(m);
      if (/the promotion lock released; the rebase cycle starts again/.test(m)) { heldAtRelease.push(promotionHeld(t)); free(); }
    };
    try {
      const t0 = Date.now();
      const r = await applyRoundB(t.args);
      expect(r.moves.map((m) => m.proposal_id)).toEqual(["b-uses-k"]);
      expect(Date.now() - t0).toBeLessThan(90_000);
    } finally { free(); }
    expect(t.logs.some((l) => /4 rebases — fix's moves prepared under the promotion lock this time/.test(l))).toBe(true);
    expect(t.logs.some((l) => /fix\.promo .*held by another process — waiting for it \(10 s at most\)/.test(l))).toBe(true);
    expect(t.logs.some((l) => /the commit must wait \(fix\.promo .*still held by another process after 10 s.*\) — the promotion lock released; the rebase cycle starts again/.test(l))).toBe(true);
    expect(heldAtRelease).toEqual([false]);
    expect(promotionHeld(t)).toBe(false);
    expect(await readFile(path.join(t.root, TARGET), "utf8")).toContain("theorem le_succ_self");
  }, 120_000);

  it("the fallback prepares, builds and gates holding the promotion lock alone: the exclusive Lake hold is its commit's", async () => {
    let n = 0;
    const promoted = async (t: Setup) => promotionHeld(t);
    const seen: Array<{ promoted: boolean; mode: string | null; mutex: boolean }> = [];
    const t: Setup = await setup({
      onRun: async (cmd, cwd) => {
        if (cwd === t.root) return;
        seen.push({ promoted: await promoted(t), mode: lakeHoldMode(t.root), mutex: existsSync(`${path.join(t.root, ".lake-build.lock")}.lock`) });
        if (n < 4 && cmd.includes("toolkit_index")) { n += 1; await anotherLands(t, n); }
      },
    });
    const commitLake: Array<string | null> = [];
    COMMIT_LAKE.run = async (cwd) => { if (cwd === t.root) commitLake.push(lakeHoldMode(t.root)); return { code: 0, out: "All targets up-to-date" }; };
    try {
      const r = await applyRoundB(t.args);
      expect(r.moves.map((m) => m.proposal_id)).toEqual(["b-uses-k"]);
    } finally {
      COMMIT_LAKE.run = async () => ({ code: 0, out: "All targets up-to-date" });
    }
    const fallback = seen.filter((x) => x.promoted);
    expect(fallback.length).toBeGreaterThan(0);
    expect(fallback.every((x) => x.mode === null && !x.mutex)).toBe(true);
    expect(commitLake.length).toBeGreaterThan(0);
    expect(commitLake.every((m) => m === "exclusive")).toBe(true);
    expect((await currentGeneration(t.root))?.gen).toBe(6);
  });

  /** Four rebases (another commit lands at each of the first four gates), then the fallback under the
   *  promotion lock; `underLock(t)` runs at each gate of a fallback attempt (a writer outside the lock). */
  async function fallback(underLock: (t: Setup) => Promise<void>) {
    let n = 0;
    const t: Setup = await setup({
      onRun: async (cmd, cwd) => {
        if (cwd === t.root || !cmd.includes("toolkit_index")) return;
        if (n < 4) { n += 1; await anotherLands(t, n); return; }
        if (promotionHeld(t)) await underLock(t);
      },
    });
    return t;
  }
  const handEdit = async (t: Setup, name: string) => {
    await writeFile(path.join(t.root, "Toolkit", "Tricks", "Arith", `${name}.lean`), `module\n\npublic section\n\ntheorem ${name.toLowerCase()} : 1 = 1 := rfl\n`);
  };

  it("a commit that must wait under the promotion lock releases it and re-enters the rebase cycle; it lands once the edit is published", async () => {
    LOCAL_MOVES.waitPollMs = 200;
    let edits = 0;
    const t = await fallback(async (t) => { if (edits === 0) { edits += 1; await handEdit(t, "ByHand"); } });
    // (the hand edit published — its flux session closed, the publisher run — once the lock is released)
    const log = t.args.log!;
    const releasedHeld: boolean[] = [];
    let published: Promise<unknown> | null = null;
    t.args.log = (m: string) => {
      log(m);
      if (/the promotion lock released/.test(m)) {
        releasedHeld.push(promotionHeld(t));
        published ??= (async () => publishGeneration(t.root, await toolkitSignature(await toolkitLayout(t.root)), () => {}))();
      }
    };
    const r = await applyRoundB(t.args);
    expect(r.moves.map((m) => m.proposal_id)).toEqual(["b-uses-k"]);
    expect(edits).toBe(1);
    expect(releasedHeld).toEqual([false]);
    expect(t.logs.some((l) => /the commit must wait \(the toolkit as it stands is not generation 5.*the promotion lock released; the rebase cycle starts again/.test(l))).toBe(true);
    expect(t.logs.some((l) => /commit waits/.test(l))).toBe(false);
    expect(await readFile(path.join(t.root, TARGET), "utf8")).toContain("theorem le_succ_self");
    expect(existsSync(path.join(t.root, "Toolkit", "Tricks", "Arith", "ByHand.lean"))).toBe(true);
  });

  it("a wait that never ends: refused within the time bound, never polled holding the promotion lock", async () => {
    LOCAL_MOVES.waitPollMs = 100;
    LOCAL_MOVES.waitMaxMs = 600;
    let edits = 0;
    const t = await fallback(async (t) => { if (edits === 0) { edits += 1; await handEdit(t, "LeftOpen"); } });
    const t0 = Date.now();
    await expect(applyRoundB(t.args)).rejects.toThrow(/could not be committed|its commit has waited/);
    expect(Date.now() - t0).toBeLessThan(60_000);
    expect(promotionHeld(t)).toBe(false);
    expect(t.logs.some((l) => /the promotion lock released; the rebase cycle starts again/.test(l))).toBe(true);
    expect(existsSync(path.join(t.root, TARGET))).toBe(false);
    // (2026-11-11) a refused commit keeps no archive (its manifest stays a day)
    const left = await readdir(commitsDir(t.root)).catch(() => [] as string[]);
    expect(left.filter((c) => existsSync(path.join(commitsDir(t.root), c, "gen.tar.zst")))).toEqual([]);
  });

  it("a base moved under the promotion lock again and again by a writer outside it: refused after two, naming it, the lock released", async () => {
    let k = 0;
    const t = await fallback(async (t) => { k += 1; await anotherLands(t, 40 + k); });
    await expect(applyRoundB(t.args)).rejects.toThrow(/moved on 2 times under the promotion lock, by a writer that does not take it .*the toolkit is generation \d+, not \d+.*refused, nothing committed/);
    expect(k).toBe(2);
    expect(promotionHeld(t)).toBe(false);
    expect(t.logs.some((l) => /moved on under the promotion lock .* a writer outside it; prepared again/.test(l))).toBe(true);
    expect(existsSync(path.join(t.root, TARGET))).toBe(false);
  });

  // (2026-11-11) a paper's file alone: it lands on the generation another commit made meanwhile when
  // nothing it read changed (I1′); with the off-switch `strict-base`, a rebase reuses the agent's file
  for (const strict of [false, true]) it(`re-proves a corollary in the workspace and commits the paper's file; ${strict ? "strict: a rebase reuses the agent's file" : "an unrelated commit meanwhile: no rebase"}`, async () => {
    const t = await setup();
    if (strict) await writeFile(strictBaseSwitch(t.root), "");
    let agent = 0;
    let moved = false;
    const file = t.main;
    const r = await localCorollary({
      cfg: t.cfg, d: t.args.deps!, qid: t.qid, log: (m) => t.logs.push(m), paperModule: "Papers.Fix", leanSubdir: "Papers/Fix",
      proposalId: "b-uses-k", decl: REF, file, general: { name: "Nat.le_succ", module: "Init" }, scans: false, scanFile: (w) => path.join(proposalsRunDir(t.cfg, t.qid), `statements_${w}_c.json`),
      deps: {
        runCodex: (async (input: { cwd?: string }) => {
          agent += 1;
          const f = path.join(input.cwd!, "Papers", "Fix", "Main.lean");
          await writeTextAtomic(f, (await readFile(f, "utf8")).replace("theorem uses_k : k ≤ k + 1 := Nat.le_succ k", "theorem uses_k : k ≤ k + 1 := by exact Nat.le_succ k"));
          return { stdout: "", stderr: "" };
        }) as never,
        build: async () => {
          // the first time, another commit lands while it builds
          if (!moved) { moved = true; await anotherLands(t, 7); }
          return { ok: true, log: "" };
        },
      },
    });
    expect(r.ok).toBe(true);
    expect(agent).toBe(1);
    expect(await readFile(file, "utf8")).toContain(":= by exact Nat.le_succ k");
    // (a paper's file alone: the toolkit's signature, and so its generation, unchanged — the other commit's stands)
    expect((await currentGeneration(t.root))?.gen).toBe(2);
    expect(t.logs.filter((l) => /the toolkit moved on while b-uses-k's corollary were prepared/.test(l))).toHaveLength(strict ? 1 : 0);
    expect(t.logs.some((l) => /off its base, its read set unchanged/.test(l))).toBe(!strict);
  });
});

describe.skipIf(process.platform === "win32" || !haveTools)("a corollary's agent never runs under the locks", () => {
  /** While the n-th build runs, another commit lands (`interfere(n)`: "land"), and the paper's file is
   *  edited in the shared tree too ("edit"); the agent records whether the promotion lock was held.
   *  `strict`: the off-switch on (every landing rebases). */
  async function corollary(interfere: (n: number) => "land" | "edit" | null, strict = false) {
    const t = await setup();
    if (strict) await writeFile(strictBaseSwitch(t.root), "");
    const underLock: boolean[] = [];
    const releasing: boolean[] = [];
    let builds = 0;
    const r = await localCorollary({
      cfg: t.cfg, d: t.args.deps!, qid: t.qid, log: (m) => { t.logs.push(m); if (/releasing them/.test(m)) releasing.push(promotionHeld(t)); }, paperModule: "Papers.Fix", leanSubdir: "Papers/Fix",
      proposalId: "b-uses-k", decl: REF, file: t.main, general: { name: "Nat.le_succ", module: "Init" }, scans: false, scanFile: (w) => path.join(proposalsRunDir(t.cfg, t.qid), `statements_${w}_c.json`),
      deps: {
        runCodex: (async (input: { cwd?: string }) => {
          underLock.push(promotionHeld(t));
          const f = path.join(input.cwd!, "Papers", "Fix", "Main.lean");
          await writeTextAtomic(f, (await readFile(f, "utf8")).replace("theorem uses_k : k ≤ k + 1 := Nat.le_succ k", "theorem uses_k : k ≤ k + 1 := by exact Nat.le_succ k"));
          return { stdout: "", stderr: "" };
        }) as never,
        build: async () => {
          builds += 1;
          const what = interfere(builds);
          if (what === "edit") await writeFile(t.main, `${await readFile(t.main, "utf8")}\n-- edited meanwhile ${builds}\n`);
          if (what) await anotherLands(t, 20 + builds);
          return { ok: true, log: "" };
        },
      },
    });
    return { t, r, underLock, releasing };
  }

  it("under the lock fallback with the paper's file changed: the locks released, the agent asked outside them, then it lands", async () => {
    // (strict: four rebases over other commits, the agent's file reused; the paper edited at the fourth)
    const { t, r, underLock, releasing } = await corollary((n) => (n <= 3 ? "land" : n === 4 ? "edit" : null), true);
    expect(r.ok).toBe(true);
    expect(t.logs.some((l) => /the agent never runs under the locks — releasing them/.test(l))).toBe(true);
    expect(releasing).toEqual([true]);
    expect(t.logs.some((l) => /asked again outside the locks \(re-ask 1\)/.test(l))).toBe(true);
    expect(underLock).toEqual([false, false]);
    const text = await readFile(t.main, "utf8");
    expect(text).toContain(":= by exact Nat.le_succ k");
    expect(text).toContain("-- edited meanwhile 4");
  });

  it("a paper's file that changes on every generation: after the re-asks, refused — the agent never under the locks", async () => {
    const { t, r, underLock } = await corollary(() => "edit");
    expect(r.ok).toBe(false);
    // (every run of the agent after the first is a re-ask, on any attempt: no more runs than with 2 rebases)
    expect(r.why).toMatch(/after 2 re-asks of the agent outside the locks/);
    expect(underLock.length).toBe(3);
    expect(underLock.every((x) => !x)).toBe(true);
    expect(await readFile(t.main, "utf8")).not.toContain(":= by exact Nat.le_succ k");
  });
});

describe.skipIf(process.platform === "win32" || !haveTools)("round-B moves: the toolkit graphs and the paper-name check in the workspace", () => {
  /** A graph of the toolkit (and, after the move, the moved result: used by nothing). */
  const graphOf = (moved: boolean): ToolkitGraph => ({
    version: 1, built_at: "x", toolkit_prefix: "Toolkit", papers_prefix: "Papers", edges: [],
    nodes: [{ id: REF, layer: "paper", kind: "theorem", module: "Papers.Fix.Main" }, ...(moved ? [{ id: NAME, layer: "toolkit" as const, kind: "theorem", module: "Toolkit.Tricks.Arith.Basic", tier: "main" as const }] : [])],
  });
  /** Each graph taken: where, on which generation, whether the move had reached the shared tree. */
  type Taken = { root: string; gen: number; landed: boolean };
  const recorder = (taken: Taken[], t: () => Setup) => async (cfgP: { toolkitRoot: string }): Promise<ToolkitGraph> => {
    const gen = (JSON.parse(await readFile(path.join(cfgP.toolkitRoot, ".pf-gen"), "utf8")) as { gen: number }).gen;
    const moved = existsSync(path.join(cfgP.toolkitRoot, TARGET));
    taken.push({ root: cfgP.toolkitRoot, gen, landed: existsSync(path.join(t().root, TARGET)) });
    return graphOf(moved);
  };

  it("both graphs in the workspace, the one after the moves before the commit; its regressions recorded; no graph of the shared tree", async () => {
    const taken: Taken[] = [];
    let shared = 0;
    const t: Setup = await setup({ graphIn: (c) => recorder(taken, () => t)(c) });
    t.args.graph = async () => { shared += 1; return null; };
    const r = await applyRoundB(t.args);
    expect(r.moves.map((m) => m.proposal_id)).toEqual(["b-uses-k"]);
    expect(shared).toBe(0);
    expect(taken.map((x) => [x.gen, x.landed])).toEqual([[1, false], [1, false]]);
    expect(taken.every((x) => x.root !== t.root && x.root.includes(`${path.sep}ws${path.sep}fix.promo`))).toBe(true);
    expect(r.regressions).toEqual(["now used by nothing: le_succ_self"]);
    expect(t.logs).toContain("toolkit graph: now used by nothing: le_succ_self");
    expect((await currentGeneration(t.root))?.gen).toBe(2);
  });

  it("a base that moved: both graphs taken again on the new generation", async () => {
    const taken: Taken[] = [];
    let landedOnce = false;
    const t: Setup = await setup({
      graphIn: (c) => recorder(taken, () => t)(c),
      onRun: async (cmd, cwd) => {
        if (!landedOnce && cmd.includes("toolkit_index") && cwd !== t.root) { landedOnce = true; await anotherLands(t, 1); }
      },
    });
    const r = await applyRoundB(t.args);
    expect(r.moves.map((m) => m.proposal_id)).toEqual(["b-uses-k"]);
    expect(taken.map((x) => x.gen)).toEqual([1, 1, 2, 2]);
    expect(taken.every((x) => !x.landed)).toBe(true);
    expect(r.regressions).toEqual(["now used by nothing: le_succ_self"]);
  });

  it("a target name another paper declares: refused in the workspace, of its base; nothing committed", async () => {
    const t = await setup({ graphIn: async () => graphOf(false) });
    await mkdir(path.join(t.root, "Papers", "Other"), { recursive: true });
    await writeFile(path.join(t.root, "Papers", "Other", "Main.lean"), "module\n\nnamespace Toolkit.Tricks.Arith\n\ntheorem le_succ_self : True := trivial\n\nend Toolkit.Tricks.Arith\n");
    const before = await snapshot(t);
    await expect(applyRoundB(t.args)).rejects.toThrow(/b-uses-k: `Toolkit\.Tricks\.Arith\.le_succ_self` is declared in a paper already/);
    expect(t.logs.some((l) => /fix's moves prepared in .* \(generation 1\)/.test(l))).toBe(true);
    expect(await snapshot(t)).toEqual(before);
    expect((await currentGeneration(t.root))?.gen).toBe(1);
  });

  it("its commit carries what the moves add, with the base graph's statement hashes, recorded beside the generation; no graph, no record", async () => {
    const graph = graphOf(false);
    const t = await setup({ graphIn: async () => ({ ...graph, nodes: graph.nodes.map((n) => (n.id === REF ? { ...n, statement_hash: "h-ref" } : n)) }) });
    await applyRoundB(t.args);
    expect(JSON.parse(await readFile(addsRecordFile(t.root, 2), "utf8"))).toMatchObject({ gen: 2, base: 1, adds: [{ name: NAME, hash: "h-ref" }] });
    const bare = await setup({ graphIn: async () => null });
    await applyRoundB(bare.args);
    expect((await currentGeneration(bare.root))?.gen).toBe(2);
    expect(existsSync(addsRecordFile(bare.root, 2))).toBe(false);
  });
});
