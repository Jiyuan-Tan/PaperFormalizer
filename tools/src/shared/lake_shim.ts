// The locking half of the workers' `lake` shim (`scripts/lake_shim/lake`, which decides what needs
// the lock): runs the real lake under the toolkit's Lake build lock, in turn with the pipeline's
// own builds, and passes its exit status on. A command that builds or elaborates one paper's
// modules and nothing else (`paperScope`) asks for a shared hold, beside other papers' builds.
// Under a shared hold of its own, lake is paused for a writer (`lakeWriterWaiting`): stopped, the
// group gone, the hold let go, asked for again, and the same command re-run (Lake reuses what is
// still up to date).
//
//   node --import tsx lake_shim.ts <project dir> <real lake> <lake args…>
import { spawn, type ChildProcess } from "node:child_process";
import os from "node:os";
import process from "node:process";
import path from "node:path";
import {
  inheritedLakeHold, LAKE_SHIM_DIR, lakeHoldCurrent, lakeHoldMode, lakeLockChildEnv, lakeWriterWaiting, refusedInside, withLakeBuildLock, type LakeLockOptions,
} from "./build_mutex.js";
import { toolkitLayout, unitOf } from "./build_inputs.js";

const LAKE_GROUP = path.join(LAKE_SHIM_DIR, "lake_group");

/** How often a lake running inside an inherited hold checks that the hold still stands; it is
 *  stopped after `HOLD_MISSES` checks in a row find it gone (one failed NFS read is not enough). */
const HOLD_CHECK_MS = Number(process.env.PAPERFORMALIZER_LAKE_SHIM_CHECK_MS ?? 2_000);
const HOLD_MISSES = 3;
/** A build is paused for writers this many times at most; after that it runs to its end (a worker
 *  is not starved by a stream of them). */
const MAX_PAUSES = 3;
/** After lake is stopped, how long the shim waits at most for its process group to be gone before
 *  it lets the hold go. */
const GROUP_GONE_MS = 10_000;

const [root, real, ...args] = process.argv.slice(2);
if (!root || !real) {
  console.error("usage: lake_shim.ts <project dir> <real lake> <lake args…>");
  process.exit(2);
}
const signo = (s: NodeJS.Signals) => 128 + (os.constants.signals[s] ?? 0);

let child: ChildProcess | null = null;
/** Signal the real lake's whole process group: its `lean` workers too, which would otherwise go on
 *  writing .oleans after the lock has moved on. */
const signalLake = (s: NodeJS.Signals) => {
  if (child?.pid === undefined) return;
  try { process.kill(-child.pid, s); } catch { /* gone */ }
};
/** Whether a process of the group `pgid` is still there. */
const groupAlive = (pgid: number | undefined) => {
  if (pgid === undefined) return false;
  try { process.kill(-pgid, 0); return true; } catch (err) { return (err as NodeJS.ErrnoException).code !== "ESRCH"; }
};
let stopped: NodeJS.Signals | null = null;
for (const s of ["SIGTERM", "SIGINT", "SIGHUP"] as const) {
  process.on(s, () => {
    stopped ??= s;
    // Running: lake stops, and the lock is released on the way out. Still waiting: leave now.
    if (child) signalLake(s);
    else process.exit(signo(s));
  });
}

/** How a run of the real lake ended: its exit status, or (`writer`) paused for that writer. */
type Run = { code: number } | { writer: string };

/** Run the real lake (polled every `HOLD_CHECK_MS`): once `holdLost` says so, stop it — the hold it
 *  ran inside ended; once `writer` names a writer waiting, stop it (SIGTERM) and say so. */
const runLake = ({ holdLost, writer }: { holdLost?: () => Promise<boolean>; writer?: () => Promise<string | null> } = {}) => new Promise<Run>((resolve) => {
  if (stopped) return resolve({ code: signo(stopped) });
  // Its children (a `lake env` command calling lake again) run inside this hold. It runs under
  // `lake_group`, the leader of a group of its own (detached), so the whole tree can be stopped at
  // once; and `lake_group` stops that group itself within half a second of this shim's death (a
  // tool timeout SIGKILLs the shim's group, which lake's is not part of).
  const c = spawn(LAKE_GROUP, [String(process.pid), real, ...args], { stdio: "inherit", detached: true, env: { ...process.env, ...lakeLockChildEnv() } });
  child = c;
  let lost = false;
  let misses = 0;
  let pausedFor: string | null = null;
  const watch = (holdLost || writer) && setInterval(() => {
    void holdLost?.().then((gone) => {
      misses = gone ? misses + 1 : 0;
      if (misses < HOLD_MISSES || lost) return;
      lost = true;
      console.error(`lake shim: the Lake lock hold this ran inside has ended — stopping \`lake ${args.join(" ")}\` (it would build unlocked)`);
      signalLake("SIGKILL");
    });
    void writer?.().then((w) => {
      if (w === null || pausedFor !== null || lost || stopped) return;
      pausedFor = w;
      signalLake("SIGTERM");
    }, () => {});
  }, HOLD_CHECK_MS);
  let finished = false;
  const done = async (code: number) => {
    if (finished) return;
    finished = true;
    if (watch) clearInterval(watch);
    // nothing of the tree outlives the hold (a straggler of a lake that exited or was stopped):
    // killed, and gone before the hold is let go
    signalLake("SIGKILL");
    for (const t0 = Date.now(); groupAlive(c.pid) && Date.now() - t0 < GROUP_GONE_MS;) await new Promise((r) => setTimeout(r, 100));
    child = null;
    // paused: unless lake had finished cleanly first, or this shim is being stopped
    resolve(lost ? { code: 75 } : pausedFor !== null && code !== 0 && !stopped ? { writer: pausedFor } : { code });
  };
  c.on("error", (err) => { console.error(`lake shim: ${err.message}`); void done(127); });
  c.on("exit", (code, s) => void done(code ?? (s ? signo(s) : 1)));
});

/** Options that change nothing but what lake prints. */
const QUIET = new Set(["-v", "--verbose", "-q", "--quiet", "--ansi", "--no-ansi", "--wfail", "--iofail", "--json"]);
const quiet = (a: string) => QUIET.has(a) || /^--(log|fail)-level=/.test(a);

/**
 * The papers whose modules the command builds or elaborates, and nothing else (a shared hold), or
 * null (an exclusive one): `build` of modules of papers (`Papers.Foo…`, not the papers' barrel) or
 * of a study's staging tree (`Toolkit.Staging.Foo…`), or `lean <file>` of a file of one (its
 * imports are built). Any option but `-d`
 * and those that change only what lake prints makes it null, as does any other command (`env lean
 * … -o …` writes wherever it is told).
 */
async function paperScope(): Promise<LakeLockOptions | null> {
  const t = await toolkitLayout(path.resolve(root!)).catch(() => null);
  if (!t) return null;
  let i = 0;
  for (; i < args.length && args[i]!.startsWith("-"); i++) {
    if (args[i] === "-d" || args[i] === "--dir") i++;
    else if (!args[i]!.startsWith("--dir=") && !quiet(args[i]!)) return null;
  }
  const [cmd, ...rest] = args.slice(i);
  const name = (p: string) => /^[\p{L}\p{N}_'!?]+$/u.test(p);
  // the unit (a paper, a study's staging tree) of a module or of a file, wherever lake or lean
  // resolves the file from (the shell's directory, the project)
  const unitOfModule = (mod: string) => (mod.split(".").every(name) ? unitOf(t, mod) : null);
  const unitOfFile = (file: string) => {
    const abs = path.resolve(file);
    if (abs !== path.resolve(root!, file)) return null;
    const rel = path.relative(t.root, abs);
    return rel.startsWith("..") ? null : unitOfModule(rel.replace(/\.lean$/, "").split(path.sep).join("."));
  };
  if (cmd === "build") {
    const papers = new Set<string>();
    // each target's own source too: one in a unit's `tmp/` is not among the unit's files
    const files: string[] = [];
    for (const a of rest) {
      if (quiet(a)) continue;
      const mod = a.replace(/^\+/, "");
      const unit = unitOfModule(mod);
      if (!unit) return null;
      papers.add(unit);
      files.push(`${path.join(t.root, ...mod.split("."))}.lean`);
    }
    return papers.size > 0 ? { papers: [...papers], files } : null;
  }
  if (cmd === "lean") {
    const [file, ...opts] = rest;
    const unit = file?.endsWith(".lean") ? unitOfFile(file) : null;
    return unit && opts.every(quiet) ? { papers: [unit], files: [path.resolve(file!)] } : null;
  }
  return null;
}

// Spawned inside a hold (a pipeline gate's command): runs inside it, only while it lasts — one left
// running after its parent released the lock is stopped, never left building unlocked. Inside a
// shared hold only a command of the papers it locked runs; anything else is refused.
const inherited = await inheritedLakeHold(root);
if (inherited) {
  const scope = inherited.mode === "shared" ? await paperScope() : null;
  const refused = refusedInside(inherited, scope?.papers ?? null, `worker: lake ${args.join(" ")}`);
  if (refused) {
    console.error(`lake shim: ${refused}`);
    process.exit(1);
  }
}
/** Under a hold of its own: lake in turn; under a shared one, paused for a writer up to
 *  `MAX_PAUSES` times — the hold let go, asked for again (a re-run, `resumed`), the command re-run.
 *  Output read by a machine (`--json`) is never cut short: such a command is not paused. */
const ownHold = async (): Promise<number> => {
  const scope = (await paperScope()) ?? {};
  for (let pauses = 0; ; pauses++) {
    const pausable = pauses < MAX_PAUSES && !args.includes("--json");
    // the one caller a model worker's process may be
    const opts: LakeLockOptions = { ...scope, viaShim: true, ...(pausable ? { pausable } : {}), ...(pauses > 0 ? { resumed: true } : {}) };
    const r = await withLakeBuildLock(root, () => runLake(pausable && lakeHoldMode(root) === "shared" ? { writer: () => lakeWriterWaiting(root) } : {}),
      `worker: lake ${args.join(" ")}`,
      (line) => console.error(/^\[lake-lock\] (waiting for |holding \S+, waiting )/.test(line) ? `${line} — another run is building; this is a wait, not a hang` : line),
      // the hold was broken (someone else may hold the lock now): lake must not build on unlocked
      (err) => {
        console.error(`lake shim: the Lake lock was lost (${err.message}) — stopping \`lake ${args.join(" ")}\``);
        signalLake("SIGKILL");
        process.exit(75);
      },
      opts);
    if ("code" in r) return r.code;
    console.error(`lake shim: \`lake ${args.join(" ")}\` paused for a writer of the toolkit's build (${r.writer}), pause ${pauses + 1} of ${MAX_PAUSES} — it re-runs once the writer is done (Lake reuses what is still up to date)`);
  }
};
const code = inherited
  // inside an inherited hold it watches no writer: never paused
  ? await runLake({ holdLost: async () => !(await lakeHoldCurrent(root, inherited.token)) }).then((r) => ("code" in r ? r.code : 1))
  : await ownHold();
process.exit(code);
