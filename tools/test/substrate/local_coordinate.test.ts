// A study's coordinate step (`local_coordinate.ts`): the coordinator
// run against the study's own workspace, its manifest applied and gated there (the real
// `applyManifest`, its Lake a stand-in on the files of the directory it runs in), committed
// (`shared/commit.ts`).
import { execFileSync } from "node:child_process";
import { existsSync } from "node:fs";
import { chmod, mkdir, mkdtemp, readdir, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterAll, afterEach, beforeAll, describe, expect, it } from "vitest";
import type { ToolkitGraph } from "../../src/proposals/toolkit_graph.js";
import { LOCAL_MOVES } from "../../src/proposals/local_moves.js";
import { toolkitLayout, toolkitSignature } from "../../src/shared/build_inputs.js";
import { COMMIT_LAKE, COMMIT_STEP, commitJournalFile } from "../../src/shared/commit.js";
import { addsRecordFile, currentGeneration, gensDir, publishGeneration } from "../../src/shared/workspace.js";
import { applyManifest, realApplyDeps, type CoordinateApplyDeps, type CoordinatorArgs } from "../../src/substrate/coordinate.js";
import { localCoordinate, type LocalCoordinateDeps } from "../../src/substrate/local_coordinate.js";
import { substrateLeanDir, substrateRunDir } from "../../src/substrate/paths.js";
import type { CoordinationManifest } from "../../src/substrate/types.js";
import { loadLedger } from "../../src/toolkit/ledger.js";
import { leanModule, writeSkeleton } from "../toolkit/helpers.js";

const haveTools = (() => { try { execFileSync("bash", ["-c", "command -v zstd && command -v flock"]); return true; } catch { return false; } })();
const tmp: string[] = [];
let bin: string;
let PATH: string | undefined;
const realLake = COMMIT_LAKE.run;
const realStep = COMMIT_STEP.at;
const timing = { ...LOCAL_MOVES };
beforeAll(async () => {
  bin = await mkdtemp(path.join(os.tmpdir(), "local-coord-bin-"));
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
  COMMIT_STEP.at = realStep;
  delete process.env.PAPERFORMALIZER_LEAN_LOCAL_ROOT;
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

type Fail = (cmd: string, cwd: string) => Promise<{ code: number; log: string; timedOut?: boolean } | null>;
/** Lake, the lints and the index on the files of the directory they run in. */
function fakeLake(calls: Array<{ cmd: string; cwd: string }>, opts: { fail?: Fail; onRun?: (cmd: string, cwd: string) => Promise<void> } = {}): CoordinateApplyDeps {
  return {
    ...realApplyDeps,
    run: async (cmd, cwd) => {
      calls.push({ cmd, cwd });
      await opts.onRun?.(cmd, cwd);
      const failed = await opts.fail?.(cmd, cwd);
      if (failed) return failed;
      const probe = /^lake env lean '?([^'\s]+)'?/.exec(cmd)?.[1];
      if (probe) return { code: 0, log: [...(await readFile(probe, "utf8")).matchAll(/#print axioms (\S+)/g)].map((m) => `'${m[1]}' depends on axioms: [propext]`).join("\n") };
      if (cmd.includes("toolkit_index")) await writeFile(path.join(cwd, "doc", "toolkit_index.json"), "{\"entries\":[]}\n");
      return { code: 0, log: "ok" };
    },
  };
}

const TARGET = "Toolkit/Foundations/Alpha/Basic.lean";
async function setup(opts: { fail?: Fail; onRun?: (cmd: string, cwd: string) => Promise<void>; graphIn?: LocalCoordinateDeps["graphIn"]; target?: (n: number) => string; body?: string } = {}) {
  const dir = await mkdtemp(path.join(os.tmpdir(), "local-coord-"));
  tmp.push(dir);
  const root = path.join(dir, "tk");
  process.env.PAPERFORMALIZER_LEAN_LOCAL_ROOT = path.join(dir, "local");
  const cfg = await writeSkeleton(root);
  await writeFile(path.join(root, "lakefile.toml"), 'name = "t"\n\n[[lean_lib]]\nname = "Toolkit"\n\n[[lean_exe]]\nname = "toolkit_index"\nroot = "ToolkitIndex"\n');
  await mkdir(path.join(root, ".lake", "build", "lib", "lean"), { recursive: true });
  await writeFile(path.join(root, ".lake", "build", "lib", "lean", "Toolkit.olean"), "olean\n");
  const slug = "alpha";
  const runDir = substrateRunDir(root, slug);
  await mkdir(runDir, { recursive: true });
  const leanDir = substrateLeanDir(root, slug, cfg.lib);
  await mkdir(leanDir, { recursive: true });
  const staged = path.join(leanDir, "Main.lean");
  await writeFile(staged, "module\n\npublic import Mathlib.Tactic\n\ntheorem staged_alpha : True := trivial\n");
  await mkdir(gensDir(root), { recursive: true });
  await publishGeneration(root, await toolkitSignature(await toolkitLayout(root)), () => {});
  const calls: Array<{ cmd: string; cwd: string }> = [];
  const logs: string[] = [];
  const agent = { calls: 0, cwds: [] as string[] };
  const runCoordinator = async (a: CoordinatorArgs): Promise<CoordinationManifest> => {
    agent.calls += 1;
    agent.cwds.push(a.toolkit.toolkitRoot);
    await rm(a.stagingDir, { recursive: true, force: true });
    await mkdir(a.stagingDir, { recursive: true });
    await writeFile(path.join(a.stagingDir, "body.lean"), leanModule({ imports: ["Mathlib.Tactic"], doc: "alpha facts", body: opts.body ?? "/-- A fact. -/\ntheorem alpha_fact : True := trivial" }));
    const target = opts.target?.(agent.calls) ?? TARGET;
    return { ops: [{ kind: "create_file", target, from: "body.lean", newModule: target.replace(/\.lean$/, "").split("/").join(".") }], notes: "" };
  };
  const deps: LocalCoordinateDeps = { runCoordinator, apply: applyManifest, applyDeps: fakeLake(calls, opts), log: (m) => logs.push(m), ...(opts.graphIn ? { graphIn: opts.graphIn } : { graphIn: async () => null }) };
  const args = {
    toolkit: cfg, toolsDir: "/tools", slug, leanDir, requirement: "r", modulePrefix: `${cfg.lib}.Staging.Alpha`, runDir,
    leanFiles: [staged], round: 1, lastFailureLog: null, requirementVersion: 0,
  };
  return { root, cfg, slug, staged, runDir, args, deps, calls, logs, agent };
}
type Setup = Awaited<ReturnType<typeof setup>>;

async function snapshot(t: Setup): Promise<Record<string, string>> {
  const out: Record<string, string> = {};
  const walk = async (d: string): Promise<void> => {
    for (const e of await readdir(d, { withFileTypes: true }).catch(() => [])) {
      const abs = path.join(d, e.name);
      if (e.isDirectory()) { if (e.name !== "Staging") await walk(abs); } else if (e.name.endsWith(".lean")) out[path.relative(t.root, abs)] = await readFile(abs, "utf8");
    }
  };
  await walk(path.join(t.root, "Toolkit"));
  out["Toolkit.lean"] = await readFile(path.join(t.root, "Toolkit.lean"), "utf8");
  out.ledger = await readFile(t.cfg.ledgerPath, "utf8");
  return out;
}
/** Another commit lands meanwhile: a module of its own (or `file`), published as the next generation. */
async function anotherLands(t: Setup, n: number, file = `Toolkit/Tricks/Other${n}.lean`): Promise<void> {
  const f = path.join(t.root, file);
  await mkdir(path.dirname(f), { recursive: true });
  await writeFile(f, `module\n\npublic section\n\ntheorem other_${n} : ${n} = ${n} := rfl\n`);
  await publishGeneration(t.root, await toolkitSignature(await toolkitLayout(t.root)), () => {});
}
const inWorkspace = (t: Setup) => t.calls.filter((c) => c.cwd.includes(`${path.sep}ws${path.sep}study_alpha.promo`));

describe.skipIf(process.platform === "win32" || !haveTools)("a study's coordinate step prepared locally and committed", () => {
  it("runs the coordinator against the workspace, gates there, and commits: the shared tree written only by the commit", async () => {
    let seenDuringGate: Record<string, string> | null = null;
    const t: Setup = await setup({ onRun: async (cmd, cwd) => { if (cmd.includes("toolkit_index") && cwd !== t.root && !seenDuringGate) seenDuringGate = await snapshot(t); } });
    const before = await snapshot(t);
    const r = await localCoordinate(t.args, t.deps);
    expect(r).toMatchObject({ ok: true });
    expect(seenDuringGate).toEqual(before);
    expect(t.agent.cwds[0]).toContain(`${path.sep}ws${path.sep}study_alpha.promo`);
    expect(inWorkspace(t).some((c) => c.cmd.startsWith("lake build Toolkit"))).toBe(true);
    expect(t.calls.filter((c) => c.cwd === t.root)).toEqual([]);
    expect(await readFile(path.join(t.root, TARGET), "utf8")).toContain("alpha_fact");
    expect((await loadLedger(t.cfg.ledgerPath)).declarations.map((d) => d.name)).toEqual(["Toolkit.Foundations.Alpha.alpha_fact"]);
    expect((await currentGeneration(t.root))?.gen).toBe(2);
    expect(existsSync(t.staged)).toBe(false);
    expect(existsSync(commitJournalFile(t.root))).toBe(false);
    expect(existsSync(path.join(t.runDir, "coordinate_journal.json"))).toBe(false);
  });

  it("its commit carries what it adds with the graph's statement hashes, recorded beside the generation; no graph, no record", async () => {
    const node = { id: "Toolkit.Foundations.Alpha.alpha_fact", layer: "toolkit" as const, kind: "theorem", module: "Toolkit.Foundations.Alpha.Basic", statement_hash: "h-alpha" };
    const t = await setup({ graphIn: async (): Promise<ToolkitGraph> => ({ version: 1, built_at: "x", toolkit_prefix: "Toolkit", papers_prefix: "Papers", edges: [], nodes: [node] }) });
    expect(await localCoordinate(t.args, t.deps)).toMatchObject({ ok: true });
    expect(JSON.parse(await readFile(addsRecordFile(t.root, 2), "utf8"))).toMatchObject({ gen: 2, base: 1, adds: [{ name: node.id, hash: "h-alpha" }] });
    const bare = await setup();
    expect(await localCoordinate(bare.args, bare.deps)).toMatchObject({ ok: true });
    expect((await currentGeneration(bare.root))?.gen).toBe(2);
    expect(existsSync(addsRecordFile(bare.root, 2))).toBe(false);
  });

  it("a gate that fails in the workspace leaves the shared tree untouched (and the staging)", async () => {
    const t = await setup({ fail: async (cmd, cwd) => (cmd.startsWith("lake build Toolkit") && cwd !== t.root ? { code: 1, log: "error: unknown identifier" } : null) });
    const before = await snapshot(t);
    const r = await localCoordinate(t.args, t.deps);
    expect(r).toMatchObject({ ok: false });
    expect(r.log).toMatch(/nothing of it reached the shared toolkit/);
    expect(await snapshot(t)).toEqual(before);
    expect(existsSync(t.staged)).toBe(true);
    expect((await currentGeneration(t.root))?.gen).toBe(1);
  });

  it("base-moved: the same manifest re-applied when its files are as the coordinator read them (no second agent run)", async () => {
    let n = 0;
    const t: Setup = await setup({ onRun: async (cmd, cwd) => { if (n < 1 && cmd.includes("toolkit_index") && cwd !== t.root) { n += 1; await anotherLands(t, n); } } });
    const r = await localCoordinate(t.args, t.deps);
    expect(r).toMatchObject({ ok: true });
    expect(t.agent.calls).toBe(1);
    expect(t.logs.some((l) => /re-applied on generation 2/.test(l))).toBe(true);
    expect((await currentGeneration(t.root))?.gen).toBe(3);
  });

  it("base-moved with a file the manifest writes changed meanwhile: the coordinator asked again", async () => {
    let n = 0;
    const t: Setup = await setup({
      target: (k) => (k === 1 ? TARGET : "Toolkit/Foundations/Alpha/More.lean"),
      onRun: async (cmd, cwd) => { if (n < 1 && cmd.includes("toolkit_index") && cwd !== t.root) { n += 1; await anotherLands(t, n, TARGET); } },
    });
    const r = await localCoordinate(t.args, t.deps);
    expect(r).toMatchObject({ ok: true });
    expect(t.agent.calls).toBe(2);
    expect(t.logs.some((l) => /changed on the new generation since the coordinator read it — asking it again/.test(l))).toBe(true);
    expect(await readFile(path.join(t.root, "Toolkit/Foundations/Alpha/More.lean"), "utf8")).toContain("alpha_fact");
  });

  it("after four rebases, prepares under the promotion lock: it lands", async () => {
    let n = 0;
    const t: Setup = await setup({ onRun: async (cmd, cwd) => { if (n < 4 && cmd.includes("toolkit_index") && cwd !== t.root) { n += 1; await anotherLands(t, n); } } });
    const r = await localCoordinate(t.args, t.deps);
    expect(r).toMatchObject({ ok: true });
    expect(t.logs.some((l) => /3 rebases — alpha's coordinate step prepared under the promotion lock/.test(l))).toBe(false);
    expect(t.logs.some((l) => /4 rebases — alpha's coordinate step prepared under the promotion lock this time/.test(l))).toBe(true);
    expect((await currentGeneration(t.root))?.gen).toBe(6);
  });

  it("a declaration its base already states (statement hash match) is refused for the owner, nothing committed", async () => {
    const graphIn = async (): Promise<ToolkitGraph> => ({
      version: 1, built_at: "x", toolkit_prefix: "Toolkit", papers_prefix: "Papers", edges: [],
      nodes: [
        { id: "Toolkit.Foundations.Beta.beta_fact", layer: "toolkit", kind: "theorem", module: "Toolkit.Foundations.Beta.Basic", statement_hash: "h" },
        { id: "Toolkit.Foundations.Alpha.alpha_fact", layer: "toolkit", kind: "theorem", module: "Toolkit.Foundations.Alpha.Basic", statement_hash: "h" },
      ],
    });
    const t = await setup({ graphIn });
    const before = await snapshot(t);
    const r = await localCoordinate(t.args, t.deps);
    expect(r).toMatchObject({ ok: false, conflict: true });
    expect(r.log).toMatch(/`Toolkit\.Foundations\.Alpha\.alpha_fact` is a duplicate of `Toolkit\.Foundations\.Beta\.beta_fact` \(statement hash match\)/);
    expect(await snapshot(t)).toEqual(before);
  });

  it("commits a new predicate structure sharing only its type with an existing inductive predicate", async () => {
    const graphIn = async (): Promise<ToolkitGraph> => ({
      version: 1, built_at: "x", toolkit_prefix: "Toolkit", papers_prefix: "Papers", edges: [],
      nodes: [
        { id: "Toolkit.Foundations.Beta.beta_predicate", layer: "toolkit", kind: "inductive", module: "Toolkit.Foundations.Beta.Basic", statement_hash: "predicate-type" },
        { id: "Toolkit.Foundations.Alpha.alpha_fact", layer: "toolkit", kind: "structure", module: "Toolkit.Foundations.Alpha.Basic", statement_hash: "predicate-type" },
      ],
    });
    const t = await setup({ graphIn, body: "/-- A positive input. -/\nstructure alpha_fact (n : Nat) : Prop where\n  positive : 0 < n" });
    expect(await localCoordinate(t.args, t.deps)).toMatchObject({ ok: true });
    expect(await readFile(path.join(t.root, TARGET), "utf8")).toContain("structure alpha_fact");
    expect((await currentGeneration(t.root))?.gen).toBe(2);
  });

  it("a commit interrupted after its commit point: the next attempt rolls it forward and records it", async () => {
    const t = await setup();
    COMMIT_STEP.at = async (s) => { if (s === "sources") throw new Error("killed at sources"); };
    await expect(localCoordinate(t.args, t.deps)).rejects.toThrow("killed at sources");
    COMMIT_STEP.at = realStep;
    const r = await localCoordinate(t.args, t.deps);
    expect(r).toMatchObject({ ok: true });
    expect(r.log).toMatch(/recorded from its landed record/);
    expect(t.agent.calls).toBe(1);
    expect(existsSync(t.staged)).toBe(false);
    expect((await loadLedger(t.cfg.ledgerPath)).declarations.map((d) => d.name)).toEqual(["Toolkit.Foundations.Alpha.alpha_fact"]);
  });

  it("a death between removing the staging and unlinking the landed record: the next attempt records it from the record (no agent)", async () => {
    const t = await setup();
    let killed = false;
    const d = t.deps.applyDeps!;
    t.deps.applyDeps = { ...d, removeFile: async (p) => { await d.removeFile(p); if (p === t.staged && !killed) { killed = true; throw new Error("killed after the staging"); } } };
    await expect(localCoordinate(t.args, t.deps)).rejects.toThrow("killed after the staging");
    const landed = path.join(substrateRunDir(t.root, t.slug), "proposals", "landed");
    expect(existsSync(t.staged)).toBe(false);
    expect((await readdir(landed)).filter((n) => n.endsWith(".json"))).toHaveLength(1);
    const r = await localCoordinate(t.args, t.deps);
    expect(r).toMatchObject({ ok: true });
    expect(r.log).toMatch(/recorded from its landed record/);
    expect(t.agent.calls).toBe(1);
    expect((await readdir(landed)).filter((n) => n.endsWith(".json"))).toEqual([]);
    expect((await currentGeneration(t.root))?.gen).toBe(2);
  });

  it("staging gone and no landed record is not landed: the normal path decides (no inference from the ledger)", async () => {
    const t = await setup();
    expect(await localCoordinate(t.args, t.deps)).toMatchObject({ ok: true });
    const landed = path.join(substrateRunDir(t.root, t.slug), "proposals", "landed");
    expect((await readdir(landed).catch(() => [])).filter((n) => n.endsWith(".json"))).toEqual([]);
    // the pipeline died before recording the step: it lists the (removed) staging again
    const r = await localCoordinate({ ...t.args, leanFiles: [] }, t.deps);
    expect(r.log).not.toMatch(/recorded from/);
    expect(t.agent.calls).toBe(2);
    expect((await loadLedger(t.cfg.ledgerPath)).declarations.map((d) => d.name)).toEqual(["Toolkit.Foundations.Alpha.alpha_fact"]);
  });

  /** Each agent call writes a module of its own; `interfere(n)` at the n-th gate in the workspace:
   *  another commit rewrites the module the current manifest writes ("target"), or lands a module of
   *  its own ("other"). The agent records whether the promotion lock was held (its lockfile
   *  directory) when it ran. */
  async function movingTargets(interfere: (n: number) => "target" | "other" | null) {
    let n = 0;
    const tgt = (k: number) => `Toolkit/Foundations/Alpha/T${k}.lean`;
    const t: Setup = await setup({
      target: tgt,
      onRun: async (cmd, cwd) => {
        if (!cmd.includes("toolkit_index") || cwd === t.root) return;
        n += 1;
        const what = interfere(n);
        if (what) await anotherLands(t, n, what === "target" ? tgt(t.agent.calls) : undefined);
      },
    });
    const underLock: boolean[] = [];
    const held = () => existsSync(`${t.cfg.lockPath}.lock`);
    const run = t.deps.runCoordinator;
    t.deps.runCoordinator = async (a) => {
      underLock.push(held());
      return run(a);
    };
    // (the check sees the lock: held where the under-lock attempt releases it)
    const releasing: boolean[] = [];
    const log = t.deps.log!;
    t.deps.log = (m) => { log(m); if (/releasing them/.test(m)) releasing.push(held()); };
    return { t, underLock, tgt, releasing };
  }

  it("under the lock fallback with the targets changed: the locks released, the agent asked outside them, then it lands", async () => {
    // (four rebases over other commits, the manifest re-applied; its target rewritten at the fourth)
    const { t, underLock, tgt, releasing } = await movingTargets((n) => (n <= 3 ? "other" : n === 4 ? "target" : null));
    const r = await localCoordinate(t.args, t.deps);
    expect(r).toMatchObject({ ok: true });
    expect(t.logs.some((l) => /never happens under the locks — releasing them/.test(l))).toBe(true);
    expect(t.logs.some((l) => /asked again outside the locks \(re-ask 1\)/.test(l))).toBe(true);
    expect(underLock).toEqual([false, false]);
    expect(releasing).toEqual([true]);
    expect(await readFile(path.join(t.root, tgt(2)), "utf8")).toContain("alpha_fact");
  });

  it("targets that change on every generation: after the re-asks, refused for the owner — the agent never under the locks", async () => {
    const { t, underLock, releasing } = await movingTargets(() => "target");
    const r = await localCoordinate(t.args, t.deps);
    expect(r).toMatchObject({ ok: false, conflict: true });
    // (every run of the agent after the first is a re-ask, on any attempt: no more runs than with 2 rebases)
    expect(r.log).toMatch(/after 2 re-asks of the coordinator outside the locks/);
    expect(underLock.length).toBe(3);
    expect(underLock.every((x) => !x)).toBe(true);
    expect(releasing).toEqual([]);
    expect((await loadLedger(t.cfg.ledgerPath)).declarations).toEqual([]);
    expect(existsSync(t.staged)).toBe(true);
  });
});
