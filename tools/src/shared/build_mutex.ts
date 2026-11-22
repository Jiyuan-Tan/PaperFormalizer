/**
 * Cross-process lock around `lake` for the toolkit's Lake project.
 *
 * Once per-qid parallel runs are allowed (see `shared/run_heartbeat.ts`), concurrent pipelines
 * call `lake build` on one toolkit. Their builds share the `.lake/build` directory, which is not
 * safe under parallel lake invocations that write the same module — `.olean` writes race and the
 * cache can end up inconsistent. Every Lake command that writes build output runs under this
 * lock, so the LLM stages remain parallel but no two builds ever make the same module at once.
 *
 * Lock file: `<repoRoot>/.lake-build.lock` (gitignore this).
 *
 * Two modes. An EXCLUSIVE hold (the default) runs alone. A SHARED hold (`opts.papers`: the call
 * builds or elaborates those papers' modules — or a study's own staging modules,
 * `Toolkit.Staging.Foo`, outside the toolkit's signature and locked as a paper is — and nothing
 * else) runs beside the shared holds of other papers and studies. That is safe because a shared hold runs only while the toolkit is CLEAN — its
 * library (`Staging` aside) and its path dependencies' libraries built from the sources as they
 * stand (`toolkit-clean.json`, below) — and only when every module its papers import outside
 * them is one of those: its lake then makes no module but its papers' (and those of the papers
 * they import, which it locks as well), and only reads the rest.
 *
 * The mutex is `proper-lockfile`'s (the `<lock>.lock` directory), so a process running older code,
 * which knows nothing else, is still excluded. In front of it waiters take a ticket
 * (`.lake/paperformalizer/lake-lock-queue/`) and only the oldest live ticket tries the mutex: the
 * lock is handed over in arrival order, and a waiter waits as long as the queue takes (it logs its
 * progress) instead of failing its stage after a fixed budget. A ticket whose process died expires
 * (its owner refreshes it every 30 s; one not refreshed for 5 min, or whose process is gone from
 * this host, is dropped). The holder writes a record beside the mutex
 * (`.lake/paperformalizer/lake-lock-holder.json`) and refreshes the mutex every 30 s: a lock with
 * that record is stale after 10 min without a refresh (a SIGKILLed holder — its lake child may
 * build on a while, so its death alone frees nothing); a lock without it (taken by older code,
 * refreshed every 30 min) after 60 min, as before.
 *
 * Shared holds. A shared request first locks each paper (or study) it reads modules of: those it
 * names and every paper a paper imports, transitively, by the import lines of their `.lean` files
 * (`tmp/` aside; a study importing another study's staging or a paper, a paper importing any
 * staging, runs exclusive) — `proper-lockfile` locks in `.lake/paperformalizer/paper-locks/`, taken in sorted order,
 * waited for without a limit, refreshed and stale as the mutex. It then takes the mutex — past
 * the queue: it takes no ticket and tries the mutex every second, unless a promotion's ticket is
 * first in line, or the ticket first in line has lost the mutex to later holds for over two minutes
 * (`sharedYieldMs`; one that only waits out the hold it found has lost nothing), when it stops trying
 * until that one has it (no writer starves: an exclusive request first in line takes the mutex
 * between two shared requests' moments under it; a shared request never queues behind the line) — and holding it looks again: the toolkit is clean and not in flux (below), its papers
 * import no paper it did not lock and nothing a build would make outside its papers but what the
 * clean stamp vouches for (no `Staging` module). Then it writes its record
 * (`.lake/paperformalizer/lake-shared/<token>.json`, refreshed every 30 s), lists the token in
 * `.lake/paperformalizer/lake-shared.json` and lets the mutex go: its action runs under the shared
 * hold. Otherwise (or when a paper lock cannot be taken) it runs as an exclusive hold. An exclusive holder, the mutex taken, waits until no listed shared hold stands
 * (one whose record went unrefreshed for 10 min is dead: as for the mutex, a holder's death alone
 * ends nothing; one that cannot be read for another reason stands) before its action runs; a new
 * shared request needs the mutex too, so none slips in meanwhile, and both modes keep their turn.
 * The list is the one record of who holds a shared hold: written only under the mutex and read by
 * name — an NFS client revalidates a file it opens, while another host's directory listing may lag
 * a minute behind a new record; one that does not parse is rebuilt from the records' directory
 * (logged), never waited on. Inside a shared hold (a nested call, a child with its token) only
 * a request of papers it locked runs; any other is refused, never run inside it nor upgraded.
 *
 * Scanners (`withScannerHold`): a scan of papers' modules runs under a shared hold of them when
 * its exe is up to date — the papers' modules built, then `lake --no-build exe …` (it builds
 * nothing: a run that would build exits 3 and the scan runs exclusive).
 *
 * The clean toolkit. `stampToolkitClean`, called by `toolkit-flux off` — and nowhere else (a
 * toolkit commit records its own stamp, `recordToolkitClean`, once Lake found the shared tree up to
 * date: `shared/commit.ts`) — runs `lake build <the library> <the path dependencies' libraries>` when the
 * toolkit is not clean (its signature, `build_inputs.toolkitSignature`, or its root `.olean`s are
 * not the stamp's). A green build is stamped (`.lake/paperformalizer/toolkit-clean.json`) with the
 * signature taken before it — a source written meanwhile leaves the stamp stale — and the modules
 * it makes, read off the import lines (`build_inputs.toolkitScope`); a red one, or a toolkit whose
 * build reaches outside the signature, is stamped failed; one killed (a timeout) stamps nothing.
 * Without a clean stamp every request runs exclusive, as before shared holds existed. Each clean
 * stamp also publishes the toolkit's generation for the runs' own workspaces, while generations are
 * on (`workspace.ts`).
 *
 * The toolkit in flux. Its Lean is written outside a Lake hold by hand (gardening, a git checkout
 * of the library or a path dependency). A promotion writes the shared tree only through a toolkit
 * commit, whose install is made under an exclusive hold inside a flux session of its own
 * (`shared/commit.ts`); its gates and their journals are in its promotion workspace. While the
 * marker `.lake/paperformalizer/toolkit-flux` exists, no shared hold begins and nothing is stamped
 * clean (a source written meanwhile also changes the signature the stamp holds: the toolkit is
 * clean again only once stamped anew). Hand edits, and the `docstrings`
 * command's pass, go inside a flux session: `paperformalizer toolkit-flux on` (an exclusive hold:
 * the shared holds drained, a session's file `toolkit-flux.d/<id>` and its id in the marker, the
 * stamp dropped) to `toolkit-flux off --id <id>` (its session closed; the last one closed lifts the
 * marker and builds the toolkit clean) — `toolkitFluxOn`, `toolkitFluxOff`, `withToolkitFlux`.
 * The marker stays while any session is open: older code looks for it alone.
 *
 * What shared holds rest on, besides: a paper gains no import of another paper or a `Staging`
 * module while its own shared hold runs (its imports are read as the hold begins); the git
 * dependencies (Mathlib, …) come built (`lake exe cache get`).
 *
 * The signature names the toolchain (`build_inputs.toolchainOf`: one `lean --version` a process
 * once it answers; while it does not, the signature is a doubt and the toolkit is not clean), read
 * before a request queues, never while it holds the mutex.
 *
 * The switch. Older code knows only the mutex: it neither waits for shared holds nor builds the
 * toolkit clean, so shared holds are safe only once no process runs it. Shared mode is on only
 * while the file `.lake/paperformalizer/lake-shared-mode` exists (looked for at each request, and
 * again under the mutex): without it every request, `opts.papers` or not, is exclusive in turn as
 * before (no paper lock, no shared record), and nothing builds the toolkit clean — the code alone
 * changes nothing. Create it once every process on the toolkit runs this code; removing it again
 * lets the shared holds that stand run out (an exclusive holder still waits for them).
 *
 * Writers first. A model worker's `lake build` of its paper under a shared hold of its own (the
 * workers' lake shim, `lake_shim.ts`) may recompile hundreds of modules after a toolkit change —
 * over an hour — while an exclusive holder drains, and every other request with it. So an
 * exclusive holder that has drained longer than `LAKE_LOCK_TIMING.preemptGraceMs`, every shared
 * hold it still waits for pausable (`opts.pausable`: the shim's own, its record says so), says so
 * in its holder record (`drainingSince`; `lakeWriterWaiting`): the shim then stops its lake (its
 * process group, lean workers too), waits for that group to be gone, releases its hold, asks again
 * and re-runs the same command once it has a hold — Lake reuses what is still up to date: a
 * module's trace is written only after its compile succeeded, its `.olean` by rename. A shim build
 * pauses a few times at most, then runs to its end unpausable; the pipeline's shared holds (gates,
 * scans, a build inside a pipeline's hold) run on, and while one stands nothing pauses.
 *
 * Holding off. A worker's build (the shim's, `opts.viaShim`) that would run shared does not run
 * exclusive while the toolkit is in flux — an exclusive worker build holds the lock as long as it
 * builds, `toolkit-flux off` needs it, and the fleet would build one at a time — nor, the re-run of
 * a paused build (`opts.resumed`), while the toolkit is not clean (the writer it paused for leaves
 * it so until stamped). It holds off, taking nothing (no paper lock, no mutex), and looks again
 * every `fluxWaitMs`, for `fluxWaitMaxMs` at most (a flux session never expires): then it runs
 * exclusive, as any request would, and says so.
 */
import { AsyncLocalStorage } from "node:async_hooks";
import { randomBytes } from "node:crypto";
import { readFileSync, readlinkSync, unlinkSync } from "node:fs";
import { mkdir, open, readdir, readFile, rename, stat, unlink, utimes, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import lockfile from "proper-lockfile";
import type { ToolkitLayout, ToolkitScope } from "./build_inputs.js";
import { isStopping } from "./child_registry.js";
import { recordLockHold, RUN_SLUG_ENV } from "./lock_holds.js";

export { RUN_SLUG_ENV };

/** A lock without our holder record (older code refreshes it every 30 min) is stale after this. */
const STALE_MS = 60 * 60_000;
/** A lock with our holder record (refreshed every `LAKE_LOCK_TIMING.updateMs`) is stale after this: a holder whose
 *  host's NFS stalls longer loses it (as a store lock does after 5 min). A paper lock and a shared
 *  hold's record, refreshed as often, are stale after it too. */
const HELD_STALE_MS = 10 * 60_000;

/** The waiting loop's clock (tests shorten it). */
export const LAKE_LOCK_TIMING = {
  /** How often a waiter looks at the queue (and the head of it tries the mutex). */
  pollMs: 1_000,
  /** How often a worker's build holding off (the toolkit in flux, or not clean for a paused build's
   *  re-run) looks again; and for how long at most before it runs exclusive. */
  fluxWaitMs: 15_000,
  fluxWaitMaxMs: 25 * 60_000,
  /** How often a waiter refreshes its ticket. */
  ticketRefreshMs: 30_000,
  /** A ticket not refreshed for this long belongs to a dead waiter. NFS attribute caching (up to a
   *  minute) and clock skew keep a live ticket well inside it. */
  ticketStaleMs: 5 * 60_000,
  /** A waiter says it waits after this long, then again every `progressMs`. */
  firstLogMs: 30_000,
  progressMs: 10 * 60_000,
  /** How often a holder refreshes the mutex (a holder record's lock is stale after `HELD_STALE_MS`),
   *  its paper locks and its shared record. */
  updateMs: 30_000,
  /** A shared request passes the queue (it takes the mutex whenever it is free) unless the ticket
   *  first in line has lost the mutex to later holds for longer than this (shared requests' moments
   *  keep beating it), or a promotion's is first: then it waits until that one has the mutex. */
  sharedYieldMs: 120_000,
  /** An exclusive holder that has waited this long for the shared holds to end marks its record
   *  (`drainingSince`): the workers' builds under shared holds of their own pause for it. */
  preemptGraceMs: 60_000,
};

/** The build that makes the toolkit clean (tests replace it): `lake build <targets>` in `root`,
 *  stopped once `lost` says the hold ended. `killed`: it did not exit on its own (a timeout, the
 *  hold lost); `log`: its error lines, when it fails. */
export const LAKE_LOCK_CLEAN_BUILD = {
  run: async (root: string, targets: readonly string[], lost: () => boolean): Promise<{ ok: boolean; killed?: boolean; log: string }> => {
    const { spawnWithInactivityTimeout } = await import("../workers/spawn.js");
    const r = await spawnWithInactivityTimeout("lake", ["build", ...targets], {
      cwd: root,
      env: process.env,
      inactivityTimeoutMs: 30 * 60_000,
      maxTotalMs: 60 * 60_000,
      liveness: { intervalMs: 10_000, check: async () => (lost() ? { ok: false, reason: "the Lake lock hold ended" } : { ok: true }) },
    });
    const errors = `${r.stdout}\n${r.stderr}`.split("\n").filter((l) => /error/i.test(l)).slice(0, 5).join("\n");
    const killed = r.killedDueToInactivity || r.killedDueToLiveness != null || r.killedDueToTotalTimeout === true || r.exitCode === null;
    return { ok: r.exitCode === 0 && !killed, ...(killed ? { killed } : {}), log: (killed ? "killed (a timeout or the hold lost)" : errors || `exit ${r.exitCode}`).slice(0, 1_000) };
  },
};

/** Set on every child a holding call chain spawns (`lakeLockChildEnv`): the holds' tokens. A
 *  process that finds its lock held under one of them runs inside that hold, never behind it — a
 *  gate's child (or a worker's `lake`, through the shim) would otherwise wait on its own parent. */
export const LAKE_LOCK_HELD_ENV = "PAPERFORMALIZER_LAKE_LOCK_HELD";

/** Set in every model worker's environment (`auth.workerEnv`): in such a process the Lake lock is
 *  taken only by the workers' `lake` shim (`opts.viaShim`). A worker's own script that imports the
 *  lock (one hold around a hundred builds, an hour long) would stop every other paper's builds. */
export const LAKE_LOCK_WORKER_ENV = "PAPERFORMALIZER_MODEL_WORKER";

/** Where the workers' `lake` shim lives (`scripts/lake_shim/lake`). */
export const LAKE_SHIM_DIR = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..", "scripts", "lake_shim");

/** PATH and LAKE for a model worker: its `lake` commands that write build output take this lock
 *  (the shim), as the pipeline's own do. `PAPERFORMALIZER_LAKE_SHIM=0` leaves them unlocked. */
export function lakeShimEnv(env: NodeJS.ProcessEnv): NodeJS.ProcessEnv {
  if (process.platform === "win32" || env.PAPERFORMALIZER_LAKE_SHIM === "0") return {};
  const rest = (env.PATH ?? "").split(path.delimiter).filter((d) => d && d !== LAKE_SHIM_DIR);
  return { PATH: [LAKE_SHIM_DIR, ...rest].join(path.delimiter), LAKE: path.join(LAKE_SHIM_DIR, "lake") };
}

/** Set in a run's environment when it builds in a Lake workspace of its own (`workspace.ts`): the
 *  workspace's directory. Its lake commands go there (the lake shim takes them there),
 *  never to the shared tree, and take no shared-tree lock. Empty: cleared for a child. */
export const LEAN_WS_ENV = "PAPERFORMALIZER_LEAN_WS";

/** The toolkit roots a workspace stands for (`<ws>/.pf-toolkit`: the root, then its real path). */
const wsRoots = new Map<string, string[]>();
function workspaceRoots(ws: string): string[] {
  let roots = wsRoots.get(ws);
  if (!roots) {
    try { roots = readFileSync(path.join(ws, ".pf-toolkit"), "utf8").split("\n").filter(Boolean); } catch { roots = []; }
    if (roots.length > 0) wsRoots.set(ws, roots);
  }
  return roots;
}

/**
 * This call chain's run workspace, or null: none set, or the chain is the shared tree's — inside the
 * promotion lock (a commit and its roll-forward build in the shared tree, under its locks), a
 * promotion round's apply (`withSharedTree`), inside a hold of a Lake lock, or a child of one.
 * With `repoRoot`: only a workspace of that toolkit.
 */
export function leanWorkspaceFor(repoRoot?: string): string | null {
  const ws = process.env[LEAN_WS_ENV];
  if (!ws) return null;
  if (sharedTree.getStore() || promotionHolds.getStore() || (heldLakeLocks.getStore()?.size ?? 0) > 0 || process.env[LAKE_LOCK_HELD_ENV]) return null;
  if (repoRoot !== undefined && !workspaceRoots(ws).includes(path.resolve(repoRoot))) return null;
  return ws;
}

/** Set across a call chain that writes the shared tree outside the promotion lock (a promotion
 *  round's apply: its moves' tail, the clean stamp, the graph after them): never a workspace's. */
const sharedTree = new AsyncLocalStorage<true>();
export const withSharedTree = <T,>(fn: () => Promise<T>): Promise<T> => sharedTree.run(true, fn);

/** What a child spawned now adds to its environment for the run's workspace: the lake shim first
 *  on its PATH (its lake commands go to the workspace) — or, in the shared tree's call chain, the
 *  workspace cleared. Nothing at all for a run without one. */
export function leanWsChildEnv(base: NodeJS.ProcessEnv = process.env): Record<string, string> {
  if (!process.env[LEAN_WS_ENV] && !base[LEAN_WS_ENV]) return {};
  const ws = leanWorkspaceFor();
  if (!ws) return { [LEAN_WS_ENV]: "" };
  return { [LEAN_WS_ENV]: ws, ...(lakeShimEnv(base) as Record<string, string>) };
}

/** This process's host, with its pid namespace (a pid means nothing across namespaces). */
export const LOCK_HOST = (() => {
  let ns = "";
  try { ns = readlinkSync("/proc/self/ns/pid").replace(/\D+/g, ""); } catch { /* not Linux */ }
  return `${os.hostname()}${ns ? `~${ns}` : ""}`.replace(/[^A-Za-z0-9_~-]+/g, "_");
})();

const sleep = (ms: number) => new Promise<void>((r) => setTimeout(r, ms));
const message = (err: unknown) => (err instanceof Error ? err.message : String(err));

function pidAlive(pid: number): boolean {
  try {
    process.kill(pid, 0);
    return true;
  } catch (err) {
    return (err as NodeJS.ErrnoException).code === "EPERM";
  }
}

async function ensureLockfileTarget(target: string): Promise<void> {
  try {
    await stat(target);
  } catch {
    await writeFile(target, "{}\n", "utf8");
  }
}

/** A file's attributes, read once it is open (an NFS client revalidates a file it opens: another
 *  host's write or delete is seen, not a cached view), or null when it is not there. */
const openStat = (file: string) => open(file, "r").then(async (fh) => { try { return await fh.stat(); } finally { await fh.close(); } }).catch(() => null);

/** Replace `file` with `value` at once (temp file + rename): a reader sees the old or the new. */
async function writeAtomic(file: string, value: unknown): Promise<void> {
  const tmp = `${file}.${process.pid}.${randomBytes(4).toString("hex")}.tmp`;
  await writeFile(tmp, `${JSON.stringify(value)}\n`);
  await rename(tmp, file).catch(async (err) => { await unlink(tmp).catch(() => {}); throw err; });
}

/** A hold a call chain runs inside: its token, its mode, (shared) the papers it locked and (an
 *  exclusive hold this process took) whether it was lost. */
interface Hold { token: string; mode: "shared" | "exclusive"; papers: readonly string[]; lost?: () => boolean }

/** The lake locks the current async call chain holds, each with its hold: a nested
 *  `withLakeBuildLock` on one of them runs at once (a promotion's gate holds the lock across its
 *  whole chain of Lake commands, each of which asks for it again). Calls outside that chain —
 *  another run, another paper — still queue. */
const heldLakeLocks = new AsyncLocalStorage<ReadonlyMap<string, Hold>>();

/** Set across a promotion-lock hold (`withPromotionLock`): only one process holds it, and every
 *  other promotion waits for it — so its Lake requests go to the head of the queue (`PRIORITY_STAMP`)
 *  instead of waiting behind every paper's build while the toolkit's promotions stand still. */
const promotionHolds = new AsyncLocalStorage<true>();
/** The arrival stamp of a promotion holder's ticket: earlier than any real one, so every version of
 *  the queue (which hands the lock over in ticket-name order) serves it first. Order changes, never
 *  exclusion. */
const PRIORITY_STAMP = "000000000000000";

/** The environment a child spawned now inherits: the tokens of the holds this call chain is in. */
export function lakeLockChildEnv(): Record<string, string> {
  const held = heldLakeLocks.getStore();
  return held && held.size > 0 ? { [LAKE_LOCK_HELD_ENV]: [...held.values()].map((h) => h.token).join(",") } : {};
}

/** `drainingSince` (ms): an exclusive holder has waited for the shared holds since then, past
 *  `LAKE_LOCK_TIMING.preemptGraceMs` (`drainShared`). */
interface Holder { ino: string; token: string; host: string; pid: number; slug?: string; what?: string; got?: string; drainingSince?: number }
/** A shared hold's record (`lake-shared/<token>.json`). */
interface SharedRecord { token: string; host: string; pid: number; slug?: string; what: string; got: string; papers: string[]; pausable?: true }
/** The clean toolkit on record (`toolkit-clean.json`): the signature its last build was taken of and
 *  what it made, or that it failed (`why`). */
type CleanStamp = { sig: string; at: string } & (
  | { ok: true; targets: string[]; libs: string[]; modules: string[]; outputs: string[]; outputsSig: string }
  | { ok: false; why: string });

const sidecarDir = (lockPath: string) => path.join(path.dirname(lockPath), ".lake", "paperformalizer");
const holderFile = (lockPath: string) => path.join(sidecarDir(lockPath), "lake-lock-holder.json");
/** The waiters' tickets of a lake lock. */
export const lakeLockQueueDir = (lockPath: string) => path.join(sidecarDir(lockPath), "lake-lock-queue");
/** The per-paper locks of shared holds. */
export const lakePaperLocksDir = (lockPath: string) => path.join(sidecarDir(lockPath), "paper-locks");
/** The shared holds' records. */
export const lakeSharedDir = (lockPath: string) => path.join(sidecarDir(lockPath), "lake-shared");
const sharedFile = (lockPath: string, token: string) => path.join(lakeSharedDir(lockPath), `${token}.json`);
const sharedIndexFile = (lockPath: string) => path.join(sidecarDir(lockPath), "lake-shared.json");
/** The clean toolkit's stamp. */
export const lakeCleanStampFile = (lockPath: string) => path.join(sidecarDir(lockPath), "toolkit-clean.json");
/** The toolkit is in flux (hand edits of its Lean) while this file exists: it lists the open flux
 *  sessions (`toolkitFluxOn`), whose files are in `lakeFluxSessionsDir`. */
export const lakeFluxFile = (lockPath: string) => path.join(sidecarDir(lockPath), "toolkit-flux");
export const lakeFluxSessionsDir = (lockPath: string) => path.join(sidecarDir(lockPath), "toolkit-flux.d");
/** Shared mode is on while this file exists (see the header). */
export const lakeSharedModeFile = (lockPath: string) => path.join(sidecarDir(lockPath), "lake-shared-mode");
/** Whether shared mode is on (the file looked for once open: another host's create or delete is seen). */
const sharedModeOn = async (lockPath: string) => (await openStat(lakeSharedModeFile(lockPath))) !== null;
/** Whether shared mode is on for `repoRoot`'s Lake lock (a caller takes no hold to stamp the
 *  toolkit clean while it is off). */
export const lakeSharedModeOn = (repoRoot: string) => sharedModeOn(path.resolve(repoRoot, ".lake-build.lock"));
const mutexDir = (lockPath: string) => `${lockPath}.lock`;
const TOKEN_RE = /^[0-9a-f]{24}$/;

/** The mutex as it stands: absent, held by older code (`holder` null), or held with our record. */
async function mutexState(lockPath: string): Promise<{ held: false } | { held: true; holder: Holder | null }> {
  const st = await stat(mutexDir(lockPath), { bigint: true }).catch(() => null);
  if (!st) return { held: false };
  const h = await readFile(holderFile(lockPath), "utf8").then((t) => JSON.parse(t) as Holder).catch(() => null);
  // The record names the directory it was written for: one left by a holder whose lock another
  // process broke (and re-took, perhaps with older code) is not this lock's.
  return { held: true, holder: h && h.ino === String(st.ino) ? h : null };
}

/** One try at the mutex; null while someone holds it. A holder's death alone never frees it: a
 *  SIGKILLed holder's lake child may still be building, so only the refresh stopping does. */
async function tryMutex(lockPath: string, onCompromised?: (err: Error) => void): Promise<(() => Promise<void>) | null> {
  const state = await mutexState(lockPath);
  try {
    return await lockfile.lock(lockPath, {
      ...(onCompromised ? { onCompromised } : {}),
      // The short window only for a lock seen with our record (refreshed every 30 s); anything else
      // — older code's lock, or one that appeared since the look — gets the hour.
      stale: state.held && state.holder ? HELD_STALE_MS : STALE_MS,
      update: LAKE_LOCK_TIMING.updateMs,
      retries: 0,
      realpath: false,
    });
  } catch (err) {
    if ((err as NodeJS.ErrnoException).code === "ELOCKED") return null;
    throw err;
  }
}

/** Let the mutex go: the holder record first (once the mutex is free another holder writes its own). */
async function letGo(lockPath: string, token: string, release: () => Promise<void>): Promise<void> {
  const mine = await readFile(holderFile(lockPath), "utf8").then((t) => (JSON.parse(t) as Holder).token === token).catch(() => false);
  if (mine) await unlink(holderFile(lockPath)).catch(() => {});
  await release();
}

/** This process's tickets, removed even when it exits while waiting (a signal, `process.exit`). */
const liveTickets = new Set<string>();
let exitHook = false;

/** A ticket of older code (no `headSince` in its body) makes shared requests wait once it is first in line and has waited this long. */
const OLDER_TICKET_YIELD_MS = 60_000;

const TICKET_RE = /^(\d{15})\.([A-Za-z0-9_~-]+)\.(\d+)\.[0-9a-f]+$/;

/** The oldest live ticket ahead of `mine` (dead ones are removed on the way), or null; and how
 *  many tickets are ahead in all. Rewrites `mine` when it went missing (it keeps its place). */
async function aheadOf(queue: string, mine: string, body: string): Promise<{ first: string | null; count: number }> {
  const names = (await readdir(queue).catch(() => [] as string[])).filter((n) => TICKET_RE.test(n)).sort();
  if (!names.includes(mine)) await writeFile(path.join(queue, mine), body).catch(() => {});
  const ahead = names.filter((n) => n < mine);
  for (const n of ahead) {
    const [, , host, pid] = TICKET_RE.exec(n)!;
    // opened, not just stat-ed: a ticket deleted on another host (a waiter that got the lock) is
    // seen gone, not listed from a cache for a minute
    const st = await openStat(path.join(queue, n));
    if (!st) continue;
    const dead = Date.now() - st.mtimeMs > LAKE_LOCK_TIMING.ticketStaleMs || (host === LOCK_HOST && !pidAlive(Number(pid)));
    if (!dead) return { first: n, count: ahead.length };
    await unlink(path.join(queue, n)).catch(() => {});
  }
  return { first: null, count: 0 };
}

/** One try at the mutex with the holder record written: the release and the hold's token, or null
 *  (the mutex is held, or the record could not be written: `unwritten` hears why, and the mutex is
 *  let go — without the record the hold's children could not run inside it, they would queue
 *  behind their own parent). */
async function mutexWithRecord(
  lockPath: string,
  what: string,
  unwritten: (err: unknown) => void,
  onCompromised?: (err: Error) => void,
): Promise<{ release: () => Promise<void>; token: string } | null> {
  const release = await tryMutex(lockPath, onCompromised);
  if (!release) return null;
  const token = randomBytes(12).toString("hex");
  const slug = process.env[RUN_SLUG_ENV];
  try {
    const st = await stat(mutexDir(lockPath), { bigint: true });
    const rec: Holder = { ino: String(st.ino), token, host: LOCK_HOST, pid: process.pid, ...(slug ? { slug } : {}), what, got: new Date().toISOString() };
    const tmp = `${holderFile(lockPath)}.${process.pid}.${token}.tmp`;
    await writeFile(tmp, `${JSON.stringify(rec)}\n`);
    await rename(tmp, holderFile(lockPath));
    return { release, token };
  } catch (err) {
    unwritten(err);
    await release().catch(() => {});
    return null;
  }
}

/** The live ticket first in line when shared requests must let it go first, or null: a
 *  promotion's (stamped first), or one that has lost the mutex to later holds, first in line, for
 *  longer than `LAKE_LOCK_TIMING.sharedYieldMs` (`headSince` in its body) — an exclusive request
 *  losing the mutex to shared requests time after time — or older code's (no `headSince` key) that
 *  has waited longer than `OLDER_TICKET_YIELD_MS`. Any other exclusive request waits only for the mutex
 *  to be free (it takes it between two shared requests' moments under it, then lets the shared
 *  holds end): shared requests never queue behind a long line of exclusive ones. */
async function longWaiter(queue: string): Promise<string | null> {
  for (const n of (await readdir(queue).catch(() => [] as string[])).filter((x) => TICKET_RE.test(x)).sort()) {
    const [, stamp, host, pid] = TICKET_RE.exec(n)!;
    const st = await openStat(path.join(queue, n));
    if (!st || Date.now() - st.mtimeMs > LAKE_LOCK_TIMING.ticketStaleMs || (host === LOCK_HOST && !pidAlive(Number(pid)))) continue; // dead: not the head
    if (stamp === PRIORITY_STAMP) return n;
    const body = await readFile(path.join(queue, n), "utf8").then((t) => JSON.parse(t) as { headSince?: number | null }, () => null).catch(() => null);
    // older code's ticket (no `headSince` key): it never says it loses the mutex — yield once it has waited a minute, as older code's shared requests do
    if (body === null || typeof body !== "object") return null; // unreadable (being written): no pause this poll
    if (!("headSince" in body)) return Date.now() - Number(stamp) > OLDER_TICKET_YIELD_MS ? n : null;
    return typeof body?.headSince === "number" && Date.now() - body.headSince > LAKE_LOCK_TIMING.sharedYieldMs ? n : null;
  }
  return null;
}

/**
 * A shared request's way to the mutex: no ticket — it tries the mutex every `pollMs` and takes it
 * whenever it is free, past the exclusive requests queued (it holds the mutex a moment: its checks,
 * its record). While a promotion's ticket is queued, or the ticket first in line has lost the mutex
 * to later holds for longer than `sharedYieldMs` (`longWaiter`), it does not try the mutex until that
 * one has it (it takes no ticket, which would put it behind the whole line): writers are never starved.
 */
async function acquireShared(
  lockPath: string,
  what: string,
  log: (line: string) => void,
  onCompromised?: (err: Error) => void,
): Promise<{ release: () => Promise<void>; token: string }> {
  const queue = lakeLockQueueDir(lockPath);
  const asked = Date.now();
  let nextLog = asked + LAKE_LOCK_TIMING.firstLogMs;
  let recordLogged = 0;
  for (;;) {
    // while one does, it does not try the mutex (it takes no ticket: it would queue behind the whole line)
    const waiter = await longWaiter(queue);
    if (!waiter) {
      const got = await mutexWithRecord(lockPath, what, (err) => {
        if (Date.now() - recordLogged >= 60_000) {
          recordLogged = Date.now();
          log(`[lake-lock] ${lockPath}: holder record not written (${message(err)}) — releasing and retrying`);
        }
      }, onCompromised);
      if (got) return got;
    }
    if (Date.now() >= nextLog) {
      log(`[lake-lock] waiting for ${lockPath} for ${Math.round((Date.now() - asked) / 60_000)} min (${what}): a shared request, ${waiter ? `letting ${waiter} go first` : "the lock is held"}`);
      nextLog = Date.now() + LAKE_LOCK_TIMING.progressMs;
    }
    await sleep(LAKE_LOCK_TIMING.pollMs);
  }
}

/** Wait in the queue for the mutex: no time limit (progress is logged). Returns the release and
 *  the hold's token, with the holder record written. */
async function acquireInTurn(
  lockPath: string,
  what: string,
  log: (line: string) => void,
  onCompromised?: (err: Error) => void,
): Promise<{ release: () => Promise<void>; token: string }> {
  const queue = lakeLockQueueDir(lockPath);
  await mkdir(queue, { recursive: true });
  const asked = Date.now();
  const priority = promotionHolds.getStore() === true;
  const mine = `${priority ? PRIORITY_STAMP : String(asked).padStart(15, "0")}.${LOCK_HOST}.${process.pid}.${randomBytes(4).toString("hex")}`;
  const ticket = path.join(queue, mine);
  const slug = process.env[RUN_SLUG_ENV];
  const fields = { host: LOCK_HOST, pid: process.pid, ...(slug ? { slug } : {}), what };
  // `headSince`: since when this ticket, first in line, has lost the mutex to another (null: it has not); the key marks this code's ticket
  const bodyOf = (headSince: number | null) => `${JSON.stringify({ ...fields, headSince })}\n`;
  let body = bodyOf(null);
  await writeFile(ticket, body);
  liveTickets.add(ticket);
  if (!exitHook) {
    exitHook = true;
    process.once("exit", () => { for (const t of liveTickets) { try { unlinkSync(t); } catch { /* gone */ } } });
  }
  const refresh = setInterval(() => {
    const now = new Date();
    utimes(ticket, now, now).catch(() => writeFile(ticket, body).catch(() => {}));
  }, LAKE_LOCK_TIMING.ticketRefreshMs);
  refresh.unref();
  try {
    let nextLog = asked + LAKE_LOCK_TIMING.firstLogMs;
    let recordLogged = 0;
    // first in line: the hold it found (its holder record's token), and since when it lost the mutex to a later one
    let found: string | null = null;
    let headSince: number | null = null;
    const markHead = async (v: number | null) => {
      headSince = v;
      body = bodyOf(v);
      await writeFile(ticket, body).catch(() => {});
    };
    for (;;) {
      const ahead = await aheadOf(queue, mine, body);
      if (ahead.first !== null) {
        found = null;
        if (headSince !== null) await markHead(null);
      } else {
        const got = await mutexWithRecord(lockPath, what, (err) => {
          if (Date.now() - recordLogged >= 60_000) {
            recordLogged = Date.now();
            log(`[lake-lock] ${lockPath}: holder record not written (${message(err)}) — releasing and retrying`);
          }
        }, onCompromised);
        if (got) return got;
        // the mutex held: by the hold found when this ticket came first (it waits that out), or by a
        // later one that took it first — lost (shared requests yield once that is long, `longWaiter`)
        if (headSince === null) {
          const state = await mutexState(lockPath).catch(() => null);
          const holder = state?.held ? state.holder?.token ?? null : null;
          if (holder !== null && found === null) found = holder;
          else if (holder !== null && holder !== found) await markHead(Date.now());
        }
      }
      if (Date.now() >= nextLog) {
        const head = ahead.first ? await readFile(path.join(queue, ahead.first), "utf8").catch(() => "") : "";
        log(`[lake-lock] waiting for ${lockPath} for ${Math.round((Date.now() - asked) / 60_000)} min (${what}): ` +
          (ahead.first ? `${ahead.count} waiter(s) ahead, first ${head.trim() || ahead.first}` : "first in line; the lock is held"));
        nextLog = Date.now() + LAKE_LOCK_TIMING.progressMs;
      }
      await sleep(LAKE_LOCK_TIMING.pollMs);
    }
  } finally {
    clearInterval(refresh);
    liveTickets.delete(ticket);
    await unlink(ticket).catch(() => {});
  }
}

/** Lock each of `papers` (sorted) for a shared hold: waited for without a limit (progress is
 *  logged). Returns the release of them all, or null when a lock could not be taken for another
 *  reason than its being held (the request then runs exclusive). */
async function lockPapers(
  lockPath: string,
  papers: readonly string[],
  what: string,
  log: (line: string) => void,
  onCompromised: (err: Error) => void,
): Promise<(() => Promise<void>) | null> {
  const dir = lakePaperLocksDir(lockPath);
  const releases: Array<() => Promise<void>> = [];
  const unlock = async () => { for (const r of releases.splice(0).reverse()) await r().catch(() => {}); };
  try {
    await mkdir(dir, { recursive: true });
    for (const paper of [...papers].sort()) {
      const asked = Date.now();
      let nextLog = asked + LAKE_LOCK_TIMING.firstLogMs;
      for (;;) {
        const release = await lockfile.lock(path.join(dir, paper), {
          onCompromised, stale: HELD_STALE_MS, update: LAKE_LOCK_TIMING.updateMs, retries: 0, realpath: false,
        }).catch((err: NodeJS.ErrnoException) => { if (err.code === "ELOCKED") return null; throw err; });
        if (release) { releases.push(release); break; }
        if (Date.now() >= nextLog) {
          log(`[lake-lock] waiting for ${paper}'s paper lock for ${Math.round((Date.now() - asked) / 60_000)} min (${what}): another build of its modules holds it`);
          nextLog = Date.now() + LAKE_LOCK_TIMING.progressMs;
        }
        await sleep(LAKE_LOCK_TIMING.pollMs);
      }
    }
  } catch (err) {
    await unlock();
    log(`[lake-lock] ${what}: a paper lock could not be taken (${message(err)}) — running exclusive`);
    return null;
  }
  return unlock;
}

/** Whether the shared hold `token` stands: its record is there and refreshed within
 *  `HELD_STALE_MS`. Only a record that is gone (ENOENT) or stale has ended: one that cannot be
 *  read for another reason (an NFS error) stands. */
async function sharedStands(lockPath: string, token: string): Promise<boolean> {
  const fh = await open(sharedFile(lockPath, token), "r").catch((err: NodeJS.ErrnoException) => (err.code === "ENOENT" ? null : "unreadable" as const));
  if (fh === null) return false;
  if (fh === "unreadable") return true;
  try {
    return Date.now() - (await fh.stat()).mtimeMs <= HELD_STALE_MS;
  } catch {
    return true;
  } finally {
    await fh.close().catch(() => {});
  }
}

/** The record of the shared hold `token` while it stands, else null (read for a child's hold and
 *  for the log: an unreadable record is no hold to run inside). */
async function sharedRecord(lockPath: string, token: string): Promise<SharedRecord | null> {
  if (!TOKEN_RE.test(token)) return null;
  const fh = await open(sharedFile(lockPath, token), "r").catch(() => null);
  if (!fh) return null;
  try {
    if (Date.now() - (await fh.stat()).mtimeMs > HELD_STALE_MS) return null;
    return JSON.parse(await fh.readFile("utf8")) as SharedRecord;
  } catch {
    return null;
  } finally {
    await fh.close().catch(() => {});
  }
}

/** The shared holds that stand, read under the mutex from the list (the one record of who holds
 *  a shared hold: written only under the mutex); stale records are removed. A list that does not
 *  parse, or is not a list of tokens, is rebuilt from the records' directory (`rebuilt`: the
 *  caller writes it again) — never waited on. Throws when the list cannot be read (absent is
 *  empty). `listed`: the list as it was. */
async function liveSharedHolds(lockPath: string, log: (line: string) => void): Promise<{ live: string[]; listed: string[]; rebuilt: boolean }> {
  const text = await readFile(sharedIndexFile(lockPath), "utf8").catch((err: NodeJS.ErrnoException) => {
    if (err.code === "ENOENT") return null;
    throw err;
  });
  let listed: string[] | null = [];
  if (text !== null) {
    try {
      const tokens = (JSON.parse(text) as { tokens?: unknown }).tokens;
      listed = Array.isArray(tokens) && tokens.every((x) => typeof x === "string" && TOKEN_RE.test(x)) ? (tokens as string[]) : null;
    } catch {
      listed = null;
    }
  }
  const rebuilt = listed === null;
  if (listed === null) {
    listed = (await readdir(lakeSharedDir(lockPath)).catch(() => [] as string[])).filter((n) => n.endsWith(".json")).map((n) => n.slice(0, -5)).filter((t) => TOKEN_RE.test(t));
    log(`[lake-lock] ${sharedIndexFile(lockPath)} does not parse as a list of shared holds: rebuilt from their records (${listed.length})`);
  }
  const live: string[] = [];
  for (const token of listed) {
    if (await sharedStands(lockPath, token)) live.push(token);
    else await unlink(sharedFile(lockPath, token)).catch(() => {});
  }
  return { live, listed, rebuilt };
}

/** Holding the mutex (`token`): wait until no shared hold stands (progress is logged; a list that
 *  cannot be read is waited out). The list loses the holds that ended. Past
 *  `LAKE_LOCK_TIMING.preemptGraceMs`, once every shared hold it waits for is pausable (looked at
 *  each poll), the holder record says so (`drainingSince`): the workers' builds under shared holds
 *  of their own pause (`lakeWriterWaiting`). */
async function drainShared(lockPath: string, token: string, what: string, log: (line: string) => void): Promise<void> {
  const since = Date.now();
  let nextLog = since + LAKE_LOCK_TIMING.firstLogMs;
  let marked = false;
  for (;;) {
    const state = await liveSharedHolds(lockPath, log).catch((err) => message(err));
    if (typeof state !== "string") {
      if (state.rebuilt || state.listed.length !== state.live.length) await writeAtomic(sharedIndexFile(lockPath), { tokens: state.live }).catch(() => {});
      if (state.live.length === 0) return;
    }
    if (!marked && typeof state !== "string" && Date.now() - since >= LAKE_LOCK_TIMING.preemptGraceMs &&
      (await Promise.all(state.live.map((t) => sharedRecord(lockPath, t)))).every((r) => r?.pausable === true)) {
      // the record rewritten whole (only its holder writes it), when it is this lock's and ours
      const m = await mutexState(lockPath).catch(() => null);
      if (m?.held && m.holder?.token === token) marked = await writeAtomic(holderFile(lockPath), { ...m.holder, drainingSince: since } satisfies Holder).then(() => true, () => false);
    }
    if (Date.now() >= nextLog) {
      const first = typeof state === "string" ? null : await sharedRecord(lockPath, state.live[0]!);
      log(`[lake-lock] holding ${lockPath}, waiting ${Math.round((Date.now() - since) / 60_000)} min for the shared holds to end (${what}): ` +
        (typeof state === "string" ? `their list cannot be read (${state})`
          : `${state.live.length}, first ${first ? `${first.what} (${first.papers.join(", ")}; ${first.host} pid ${first.pid}${first.slug ? `, ${first.slug}` : ""})` : state.live[0]}`));
      nextLog = Date.now() + LAKE_LOCK_TIMING.progressMs;
    }
    await sleep(LAKE_LOCK_TIMING.pollMs);
  }
}

/** Holding the mutex: write the shared hold's record and list it. */
async function registerShared(lockPath: string, rec: SharedRecord, log: (line: string) => void): Promise<void> {
  await mkdir(lakeSharedDir(lockPath), { recursive: true });
  await writeAtomic(sharedFile(lockPath, rec.token), rec);
  try {
    const { live } = await liveSharedHolds(lockPath, log);
    await writeAtomic(sharedIndexFile(lockPath), { tokens: [...new Set([...live, rec.token])].sort() });
  } catch (err) {
    await unlink(sharedFile(lockPath, rec.token)).catch(() => {});
    throw err;
  }
}

async function readStamp(lockPath: string): Promise<CleanStamp | null> {
  const s = await readFile(lakeCleanStampFile(lockPath), "utf8").then((t) => JSON.parse(t) as CleanStamp).catch(() => null);
  if (!s || typeof s.sig !== "string") return null;
  if (s.ok === true) return Array.isArray(s.modules) && Array.isArray(s.libs) && Array.isArray(s.outputs) && typeof s.outputsSig === "string" ? s : null;
  return s.ok === false ? s : null;
}

/** Why the toolkit's sources are in flux — a flux session is open (`toolkit-flux on`: the marker,
 *  or a session's file) — or null. A promotion's or a study's journal is not flux: every automated
 *  toolkit write (moves, batches, study applies, their undo and recovery) happens inside an
 *  exclusive hold, which no shared hold overlaps; a journal kept for repair or left by a crash
 *  leaves its files as written, which the clean stamp vouches for only once they build (and its
 *  signature then covers them); only a hand edit needs more, and hand edits go inside a flux
 *  session. Each file is looked for once open. */
async function toolkitInFlux(lockPath: string, t: ToolkitLayout): Promise<string | null> {
  if ((await openStat(lakeFluxFile(lockPath))) !== null) return "the toolkit is in flux (`paperformalizer toolkit-flux on`)";
  const sessions = (await readdir(lakeFluxSessionsDir(lockPath)).catch(() => [] as string[])).filter((n) => FLUX_ID_RE.test(n));
  return sessions.length > 0 ? `the toolkit is in flux (\`paperformalizer toolkit-flux on\`: ${sessions.join(", ")})` : null;
}

/** The clean stamp of the toolkit as it stands, or why it is not clean (in flux, no stamp, a stale
 *  or failed one). */
async function cleanStamp(lockPath: string, t: ToolkitLayout): Promise<{ stamp: Extract<CleanStamp, { ok: true }> } | { why: string }> {
  const { signatureOf, toolkitSignature } = await import("./build_inputs.js");
  const flux = await toolkitInFlux(lockPath, t);
  if (flux) return { why: flux };
  const stamp = await readStamp(lockPath);
  if (!stamp) return { why: "no clean build of the toolkit on record" };
  if (stamp.sig !== (await toolkitSignature(t))) return { why: "the toolkit changed since its last clean build" };
  if (!stamp.ok) return { why: `the toolkit's last clean build failed (${stamp.why.split("\n")[0]})` };
  if ((await signatureOf(stamp.outputs)) !== stamp.outputsSig) return { why: "the toolkit's build output changed since its last clean build" };
  return { stamp };
}

/** Holding the mutex: why `asks` may not run under a shared hold with `locked` (the papers whose
 *  locks it holds), or null when it may. */
async function whyNotShared(lockPath: string, t: ToolkitLayout, locked: readonly string[], asks: readonly string[], files: readonly string[]): Promise<string | null> {
  try {
    const { paperImports, uncoveredImport } = await import("./build_inputs.js");
    if (!(await sharedModeOn(lockPath))) return "shared mode was switched off";
    const clean = await cleanStamp(lockPath, t);
    if ("why" in clean) return clean.why;
    const { stamp } = clean;
    const c = await paperImports(t, asks, files);
    if (c.why) return c.why;
    const more = c.papers.filter((p) => !locked.includes(p));
    if (more.length > 0) return `it imports ${more.join(", ")} now, not locked`;
    const out = uncoveredImport(t, stamp, c.imports);
    return out ? `it imports ${out}, which the toolkit's clean build does not make` : null;
  } catch (err) {
    return message(err);
  }
}

/** What came of `stampToolkitClean`: stamped clean, or why not. */
export type CleanOutcome = { clean: true } | { clean: false; why: string };

/**
 * Build the toolkit clean and stamp it (see the header), inside an exclusive hold of `repoRoot`'s
 * Lake lock this call chain holds — the end of a promotion's moves or a study's apply, once their
 * gates passed, and `toolkit-flux off`. Nothing else builds it. Nothing is built while shared mode
 * is off, while the toolkit is in flux, or when the stamp is of the sources and build output as
 * they stand. A build that exits non-zero is stamped failed; one killed (a timeout, the hold lost)
 * stamps nothing. Never throws.
 */
export async function stampToolkitClean(repoRoot: string, log: (line: string) => void = (l) => console.warn(l)): Promise<CleanOutcome> {
  const lockPath = path.resolve(repoRoot, ".lake-build.lock");
  const not = (why: string): CleanOutcome => ({ clean: false, why });
  try {
    if (!(await sharedModeOn(lockPath))) return not("shared mode is off");
    const hold = heldLakeLocks.getStore()?.get(lockPath);
    if (hold?.mode !== "exclusive" || !hold.lost) return not("not inside an exclusive hold of the Lake lock");
    const lost = hold.lost;
    if (isStopping()) return not("the process is stopping");
    const { isDoubt, signatureOf, toolkitLayout, toolkitScope, toolkitSignature } = await import("./build_inputs.js");
    const t = await toolkitLayout(path.dirname(lockPath));
    const flux = await toolkitInFlux(lockPath, t);
    if (flux) return not(flux);
    // a toolkit commit on file (`commit.ts`): never stamped over — the commit stamps, or its roll-forward
    if ((await openStat(commitJournalOf(lockPath))) !== null) return not("a toolkit commit is on file (`paperformalizer toolkit-commit status`)");
    const sig = await toolkitSignature(t);
    if (isDoubt(sig)) return not(sig);
    const stamp = await readStamp(lockPath);
    if (stamp?.sig === sig && stamp.ok && (await signatureOf(stamp.outputs)) === stamp.outputsSig) return await published(t.root, sig, log);
    const scope = await toolkitScope(t);
    if ("why" in scope) {
      log(`[lake-lock] the toolkit's build cannot be vouched for (${scope.why}): every Lake command runs exclusive`);
      await writeAtomic(lakeCleanStampFile(lockPath), { sig, ok: false, why: scope.why, at: new Date().toISOString() } satisfies CleanStamp);
      return not(scope.why);
    }
    const cmd = `lake build ${scope.targets.join(" ")}`;
    log(`[lake-lock] building the toolkit clean: \`${cmd}\``);
    const t0 = Date.now();
    const r = await LAKE_LOCK_CLEAN_BUILD.run(t.root, scope.targets, lost);
    if (lost() || r.killed) return not(`\`${cmd}\` was stopped (${lost() ? "the hold was lost" : r.log}); nothing stamped`);
    if (!r.ok) {
      log(`[lake-lock] \`${cmd}\` failed: every Lake command runs exclusive until the toolkit is built clean\n${r.log}`);
      await writeAtomic(lakeCleanStampFile(lockPath), { sig, ok: false, why: `\`${cmd}\` failed: ${r.log}`, at: new Date().toISOString() } satisfies CleanStamp);
      return not(`\`${cmd}\` failed`);
    }
    await writeAtomic(lakeCleanStampFile(lockPath), {
      sig, ok: true, at: new Date().toISOString(), targets: scope.targets, libs: scope.libs, modules: scope.modules,
      outputs: scope.outputs, outputsSig: await signatureOf(scope.outputs),
    } satisfies CleanStamp);
    log(`[lake-lock] the toolkit is clean (\`${cmd}\`, ${Math.round((Date.now() - t0) / 6_000) / 10} min): builds of different papers' modules run side by side`);
    return await published(t.root, sig, log);
  } catch (err) {
    log(`[lake-lock] the toolkit's clean build was not settled (${message(err)})`);
    return not(message(err));
  }
}

/** The toolkit clean (inside the exclusive hold that stamped it): its generation published for the
 *  runs' workspaces, when generations are on (`workspace.ts`) — by a process of its own, after this
 *  hold, under a shared hold of no paper (`toolkit-gen publish`): never inside this one. A failed
 *  start is logged, never thrown: the runs keep the generation they have. */
async function published(root: string, sig: string, log: (line: string) => void): Promise<CleanOutcome> {
  try {
    const { spawnPublisher } = await import("./workspace.js");
    spawnPublisher(root, sig, log);
  } catch (err) {
    log(`[lake-lock] the toolkit's generation was not published (${message(err)})`);
  }
  return { clean: true };
}

/** The toolkit's signature when its clean stamp vouches for its sources and build output as they
 *  stand (not in flux), else why not. Reads only. */
export async function stampedClean(repoRoot: string): Promise<{ sig: string } | { why: string }> {
  const lockPath = path.resolve(repoRoot, ".lake-build.lock");
  const { toolkitLayout } = await import("./build_inputs.js");
  const c = await cleanStamp(lockPath, await toolkitLayout(path.dirname(lockPath)));
  return "why" in c ? c : { sig: c.stamp.sig };
}

/** Why a flux session is open on `repoRoot`'s toolkit, or null. Reads only. */
export async function toolkitFluxWhy(repoRoot: string): Promise<string | null> {
  const lockPath = path.resolve(repoRoot, ".lake-build.lock");
  const { toolkitLayout } = await import("./build_inputs.js");
  return toolkitInFlux(lockPath, await toolkitLayout(path.dirname(lockPath)));
}

/** A commit (`commit.ts`), inside its exclusive hold, once Lake itself found the toolkit's targets
 *  up to date: the clean stamp of `sig` and `scope`, as `stampToolkitClean` writes it after its build. */
export async function recordToolkitClean(repoRoot: string, sig: string, scope: ToolkitScope): Promise<void> {
  const lockPath = path.resolve(repoRoot, ".lake-build.lock");
  const { signatureOf } = await import("./build_inputs.js");
  await writeAtomic(lakeCleanStampFile(lockPath), {
    sig, ok: true, at: new Date().toISOString(), targets: scope.targets, libs: scope.libs, modules: scope.modules,
    outputs: scope.outputs, outputsSig: await signatureOf(scope.outputs),
  } satisfies CleanStamp);
}

/** A toolkit commit's flux session (`commit.ts`: its id) and its journal. */
const COMMIT_SESSION_RE = /^commit[0-9a-z]+-[0-9a-f]{6}$/;
const commitJournalOf = (lockPath: string) => path.join(sidecarDir(lockPath), "commit.json");
/** Whether a toolkit commit is on file for `lockPath`'s toolkit: its journal, or its flux session. */
async function commitOnFileAt(lockPath: string): Promise<boolean> {
  return (await openStat(commitJournalOf(lockPath))) !== null || (await fluxSessions(lockPath)).some((s) => COMMIT_SESSION_RE.test(s));
}
/** Set across a toolkit commit's own call chain (`commit.ts`): its exclusive holds are allowed while
 *  its journal is on file. */
const commitChain = new AsyncLocalStorage<true>();
export const withinCommit = <T,>(fn: () => Promise<T>): Promise<T> => commitChain.run(true, fn);

/** A flux session's id (`toolkitFluxOn`). */
const FLUX_ID_RE = /^[0-9a-z]+-[0-9a-f]{6}$/;
/** The flux sessions on record: the marker's list (written only under an exclusive hold, read by
 *  name) with the sessions' files; a marker without a list (older code's `on`) is one session,
 *  `legacy`. */
async function fluxSessions(lockPath: string): Promise<string[]> {
  const marker = await readFile(lakeFluxFile(lockPath), "utf8").then((t) => {
    try {
      const ids = (JSON.parse(t) as { sessions?: unknown }).sessions;
      return Array.isArray(ids) ? ids.filter((x): x is string => typeof x === "string" && (x === "legacy" || FLUX_ID_RE.test(x))) : ["legacy"];
    } catch {
      return ["legacy"];
    }
  }, () => [] as string[]);
  const files = (await readdir(lakeFluxSessionsDir(lockPath)).catch(() => [] as string[])).filter((n) => FLUX_ID_RE.test(n));
  return [...new Set([...marker, ...files])].sort();
}

/** Holding the Lake lock exclusive: write the sessions' list into the marker, or remove it (and
 *  then the clean stamp is the caller's to make) when none remains. The marker exists exactly
 *  while a session does: older code looks for it alone. */
async function writeFluxSessions(lockPath: string, ids: readonly string[]): Promise<void> {
  if (ids.length > 0) await writeAtomic(lakeFluxFile(lockPath), { sessions: [...new Set(ids)].sort() });
  else await unlink(lakeFluxFile(lockPath)).catch((err: NodeJS.ErrnoException) => { if (err.code !== "ENOENT") throw err; });
}

/** A commit (`commit.ts`), inside its exclusive hold, before its first write of the shared tree: the
 *  flux session `id` opened (as `toolkitFluxOn` opens one: the session's file, the marker, the stamp
 *  dropped). While it is open no shared hold begins, nothing is stamped clean and no generation is
 *  published — a commit that crashes leaves it open until its roll-forward. */
export async function openFluxSession(repoRoot: string, id: string, what: string): Promise<void> {
  if (!FLUX_ID_RE.test(id)) throw new Error(`not a flux session id: ${id}`);
  const lockPath = path.resolve(repoRoot, ".lake-build.lock");
  await mkdir(lakeFluxSessionsDir(lockPath), { recursive: true });
  await writeFile(path.join(lakeFluxSessionsDir(lockPath), id), `${JSON.stringify({ id, host: LOCK_HOST, pid: process.pid, what, at: new Date().toISOString() })}\n`);
  await writeFluxSessions(lockPath, [...(await fluxSessions(lockPath)), id]);
  await writeAtomic(lakeCleanStampFile(lockPath), { sig: "flux", ok: false, why: "the toolkit is in flux", at: new Date().toISOString() } satisfies CleanStamp);
}

/** The commit's flux session `id` closed (inside its exclusive hold), its own clean stamp already
 *  written: no build, no stamp here. */
export async function closeFluxSession(repoRoot: string, id: string): Promise<void> {
  const lockPath = path.resolve(repoRoot, ".lake-build.lock");
  await unlink(path.join(lakeFluxSessionsDir(lockPath), id)).catch((err: NodeJS.ErrnoException) => { if (err.code !== "ENOENT") throw err; });
  await writeFluxSessions(lockPath, (await fluxSessions(lockPath)).filter((s) => s !== id));
}

/** The flux sessions on record, each with what opened it (its file's `what`; "" when unreadable). */
export async function fluxSessionsOpen(repoRoot: string): Promise<Array<{ id: string; what: string }>> {
  const lockPath = path.resolve(repoRoot, ".lake-build.lock");
  const out: Array<{ id: string; what: string }> = [];
  for (const id of await fluxSessions(lockPath)) {
    const what = await readFile(path.join(lakeFluxSessionsDir(lockPath), id), "utf8").then((t) => {
      try { return String((JSON.parse(t) as { what?: unknown }).what ?? ""); } catch { return ""; }
    }, () => "");
    out.push({ id, what });
  }
  return out;
}

/**
 * `paperformalizer toolkit-flux on`: open a flux session — hand edits of the toolkit's Lean (a kept
 * move's repair, gardening, a git checkout touching the library or a path dependency, the
 * `docstrings` command's pass) go between it and its `toolkitFluxOff`. Under an exclusive hold (no
 * shared hold runs past it): the session's file (`toolkit-flux.d/<id>`), its id in the marker
 * (`toolkit-flux`), and the clean stamp dropped (read by name: a host whose cache still misses the
 * marker finds the toolkit not clean). Returns the session's id.
 */
export async function toolkitFluxOn(repoRoot: string, what: string, log: (line: string) => void = (l) => console.log(l)): Promise<string> {
  const lockPath = path.resolve(repoRoot, ".lake-build.lock");
  const id = `${Date.now().toString(36)}-${randomBytes(3).toString("hex")}`;
  await withLakeBuildLock(repoRoot, async () => {
    // never beside a toolkit commit on file (`commit.ts`): it is finished, or settled by hand, first
    if ((await openStat(commitJournalOf(lockPath))) !== null || (await fluxSessions(lockPath)).some((s) => COMMIT_SESSION_RE.test(s))) {
      throw new Error("a toolkit commit is on file or in progress: finish it first (`paperformalizer toolkit-commit status`, then `recover`, `clear <id>` or `undo`)");
    }
    await mkdir(lakeFluxSessionsDir(lockPath), { recursive: true });
    await writeFile(path.join(lakeFluxSessionsDir(lockPath), id), `${JSON.stringify({ id, host: LOCK_HOST, pid: process.pid, what, at: new Date().toISOString() })}\n`);
    await writeFluxSessions(lockPath, [...(await fluxSessions(lockPath)), id]);
    await writeAtomic(lakeCleanStampFile(lockPath), { sig: "flux", ok: false, why: "the toolkit is in flux", at: new Date().toISOString() } satisfies CleanStamp);
  }, `toolkit-flux on (${what})`, log);
  return id;
}

/**
 * `paperformalizer toolkit-flux off [--id <id>]`: close the flux session `id` — without one, the
 * only session on record (several: refused, naming them). Under an exclusive hold; the last
 * session closed lifts the marker and builds the toolkit clean (`stampToolkitClean`), one closed
 * while others remain leaves the toolkit in flux. `clean` is null when nothing was stamped.
 */
export async function toolkitFluxOff(repoRoot: string, id: string | null, log: (line: string) => void = (l) => console.log(l)): Promise<{ closed: string | null; remaining: string[]; clean: CleanOutcome | null }> {
  const lockPath = path.resolve(repoRoot, ".lake-build.lock");
  return withLakeBuildLock(repoRoot, async () => {
    const sessions = await fluxSessions(lockPath);
    let closed: string | null = null;
    if (id !== null) {
      if (!sessions.includes(id)) throw new Error(`no flux session ${id} on record (${sessions.length > 0 ? `sessions: ${sessions.join(", ")}` : "none"})`);
      if (COMMIT_SESSION_RE.test(id)) throw new Error(`flux session ${id} is a toolkit commit's: \`paperformalizer toolkit-commit recover\`, \`clear ${id}\` or \`undo\` closes it`);
      closed = id;
    } else if (sessions.some((s) => COMMIT_SESSION_RE.test(s))) {
      throw new Error(`a toolkit commit's flux session is open (${sessions.filter((s) => COMMIT_SESSION_RE.test(s)).join(", ")}): close yours with \`toolkit-flux off --id <id>\`; the commit's is closed by \`toolkit-commit\``);
    } else if (sessions.length > 1) {
      throw new Error(`${sessions.length} flux sessions are open (${sessions.join(", ")}): close yours with \`toolkit-flux off --id <id>\``);
    } else {
      closed = sessions[0] ?? null;
    }
    if (closed && closed !== "legacy") await unlink(path.join(lakeFluxSessionsDir(lockPath), closed)).catch((err: NodeJS.ErrnoException) => { if (err.code !== "ENOENT") throw err; });
    const remaining = sessions.filter((s) => s !== closed);
    await writeFluxSessions(lockPath, remaining);
    return { closed, remaining, clean: remaining.length > 0 ? null : await stampToolkitClean(repoRoot, log) };
  }, `toolkit-flux off${id ? ` (${id})` : ""}`, log);
}

/** Run `fn` inside a flux session of its own (`toolkitFluxOn`, then `toolkitFluxOff` whatever
 *  `fn` does): for a command that rewrites the toolkit's Lean outside a Lake hold. */
export async function withToolkitFlux<T>(repoRoot: string, what: string, fn: () => Promise<T>, log: (line: string) => void = (l) => console.log(l)): Promise<T> {
  const id = await toolkitFluxOn(repoRoot, what, log);
  log(`[lake-lock] ${what}: the toolkit is in flux (session ${id}) until it ends`);
  try {
    return await fn();
  } finally {
    const r = await toolkitFluxOff(repoRoot, id, log);
    if (r.remaining.length > 0) log(`[lake-lock] ${what}: flux session ${id} closed; still in flux (${r.remaining.join(", ")})`);
  }
}

/** Whether the hold `token` of the Lake lock of `repoRoot` is still the current one (the holder
 *  record names it, or its shared record stands). Once released it never is again. */
export async function lakeHoldCurrent(repoRoot: string, token: string): Promise<boolean> {
  const lockPath = path.resolve(repoRoot, ".lake-build.lock");
  const state = await mutexState(lockPath);
  return (state.held && state.holder?.token === token) || (await sharedRecord(lockPath, token)) !== null;
}

/** What holds `repoRoot`'s Lake lock exclusive and has waited past `LAKE_LOCK_TIMING.preemptGraceMs`
 *  for the shared holds to end (its record's `what`), or null: a worker's build under a shared hold
 *  of its own pauses for it (`lake_shim.ts`). */
export async function lakeWriterWaiting(repoRoot: string): Promise<string | null> {
  const state = await mutexState(path.resolve(repoRoot, ".lake-build.lock")).catch(() => null);
  return state?.held && typeof state.holder?.drainingSince === "number" ? state.holder.what ?? "an exclusive hold" : null;
}

/** A hold of a Lake lock: its token, its mode and (shared) the papers it locked. */
export type LakeHold = Pick<Hold, "token" | "mode" | "papers">;

/** The hold of `repoRoot`'s Lake lock this process runs inside, or null. */
export const inheritedLakeHold = async (repoRoot: string): Promise<LakeHold | null> => inheritedHold(path.resolve(repoRoot, ".lake-build.lock"));

/** The hold this process runs inside (an ancestor's, named by `LAKE_LOCK_HELD_ENV` and still
 *  current: the mutex's holder, or a shared hold that stands), or null. */
async function inheritedHold(lockPath: string): Promise<Hold | null> {
  const tokens = (process.env[LAKE_LOCK_HELD_ENV] ?? "").split(",").filter(Boolean);
  if (tokens.length === 0) return null;
  const state = await mutexState(lockPath);
  if (state.held && state.holder && tokens.includes(state.holder.token)) return { token: state.holder.token, mode: "exclusive", papers: [] };
  for (const token of tokens) {
    const rec = await sharedRecord(lockPath, token);
    if (rec) return { token, mode: "shared", papers: Array.isArray(rec.papers) ? rec.papers : [] };
  }
  return null;
}

/** Why a request may not run inside the hold `h` it finds, or null: inside a shared hold only a
 *  request of papers it locked runs — an exclusive one, or one of another paper, is never run
 *  inside it, nor upgraded. */
export function refusedInside(h: LakeHold, papers: readonly string[] | null, what: string): string | null {
  if (h.mode !== "shared") return null;
  const missing = papers?.filter((p) => !h.papers.includes(p)) ?? null;
  if (missing?.length === 0) return null;
  return `[lake-lock] ${what}: refused — it runs inside a shared hold of ${h.papers.join(", ") || "the toolkit alone"}, which covers ${missing ? `not ${missing.join(", ")}` : "no exclusive Lake command"} (a shared hold is never upgraded)`;
}

export interface LakeLockOptions {
  /** The papers (`Papers.Foo`) or studies' staging trees (`Toolkit.Staging.Foo`) whose own modules
   *  `action` builds or elaborates, and nothing else: a shared hold is asked for. Without it the
   *  hold is exclusive. */
  papers?: readonly string[];
  /** Lean files besides the papers' own that `action` builds or elaborates (a scratch file in a
   *  paper's `tmp/`): their imports count as the papers' do. */
  files?: readonly string[];
  /** The call is the workers' `lake` shim's: the one caller a model worker's process may be. */
  viaShim?: boolean;
  /** With no `papers`: `action` only reads the toolkit's build (a scan of the toolkit alone, its
   *  turns `lake --no-build`): a shared hold of no paper is asked for — beside papers' builds while
   *  the toolkit is clean, never beside a write of it. */
  toolkitOnly?: boolean;
  /** The caller (the shim) stops its action once `lakeWriterWaiting` names a writer: its shared
   *  record says so, and a writer draining only such holds marks itself. */
  pausable?: boolean;
  /** The re-run of a build paused for a writer: it holds off while the toolkit is not clean (see
   *  the header), not only while it is in flux. */
  resumed?: boolean;
}

/**
 * Run `action` holding the toolkit's Lake lock. `what` names the caller for the waiting log and
 * the hold record (`lock_holds.ts`). Waits as long as the queue ahead takes. With `opts.papers`
 * the hold is shared when shared mode is on and the toolkit is clean, else exclusive (see the
 * header). Inside a hold of this chain (or of the process's parent) it runs at once — but inside
 * a shared hold only for papers that hold locked: anything else throws (`refusedInside`). In a
 * model worker's process (`LAKE_LOCK_WORKER_ENV`) only the lake shim may call it.
 */
export async function withLakeBuildLock<T>(
  repoRoot: string,
  action: () => Promise<T>,
  what = "lake",
  log: (line: string) => void = (l) => console.warn(l),
  /** Called when the hold is found broken (proper-lockfile's default throws from a timer). */
  onCompromised?: (err: Error) => void,
  opts: LakeLockOptions = {},
): Promise<T> {
  if (process.env[LAKE_LOCK_WORKER_ENV] === "1" && !opts.viaShim) {
    throw new Error(`[lake-lock] ${what}: refused — this is a model worker's process (${LAKE_LOCK_WORKER_ENV}=1), which never takes the toolkit's build lock itself. ` +
      "Run `lake` commands directly: each queues for the lock by itself (through the pipeline's lake shim). One hold around many builds stops every other paper's builds.");
  }
  // A run that builds in its own workspace: its lake commands go there (the shim), where nothing
  // but this run builds — no shared-tree lock, no hold record.
  if (!opts.viaShim && leanWorkspaceFor(repoRoot)) return action();
  const lockPath = path.resolve(repoRoot, ".lake-build.lock");
  const asks = opts.papers && opts.papers.length > 0 ? [...new Set(opts.papers)].sort() : opts.toolkitOnly ? [] : null;
  const held = heldLakeLocks.getStore();
  const outer = held?.get(lockPath);
  if (outer) {
    const refused = refusedInside(outer, asks, what);
    if (refused) throw new Error(refused);
    return action();
  }
  await ensureLockfileTarget(lockPath);
  const within = (h: Hold) => heldLakeLocks.run(new Map([...(held ?? []), [lockPath, h]]), action);
  const inherited = await inheritedHold(lockPath);
  if (inherited) {
    const refused = refusedInside(inherited, asks, what);
    if (refused) throw new Error(refused);
    return within(inherited);
  }
  const asked = new Date();
  let lost = false;
  const compromised = (err: Error) => {
    lost = true;
    if (onCompromised) onCompromised(err);
    else throw err;
  };
  const { paperImports, toolkitLayout, unitOf } = await import("./build_inputs.js");
  let layout: ToolkitLayout | null = null;
  // a shared request: the papers it reads modules of, each locked before it queues
  let papers: string[] = [];
  let fallback: string | null = null;
  // shared mode off: exclusive, as before shared holds existed
  if (asks && (await sharedModeOn(lockPath))) {
    try {
      const t = await toolkitLayout(path.dirname(lockPath));
      layout = t;
      // a paper (`Papers.Foo`) or a study's staging tree (`Toolkit.Staging.Foo`)
      const notPaper = asks.find((p) => unitOf(t, p) !== p || !/^[\p{L}\p{N}_'!?]+$/u.test(p.split(".").at(-1)!));
      if (notPaper) fallback = `${notPaper} is no paper or study of the toolkit`;
      else papers = (await paperImports(t, asks, opts.files)).papers;
    } catch (err) {
      fallback = message(err);
    }
  }
  // Shared mode on: the toolchain the signature names is read now (a `lean --version`, once per
  // process), not while holding the mutex.
  if (await sharedModeOn(lockPath)) await (await import("./build_inputs.js")).toolchainOf(path.dirname(lockPath));
  // a shared request: papers to hold, or (`toolkitOnly`) none — the toolkit's build alone is read
  const sharedAsk = () => layout !== null && fallback === null && (papers.length > 0 || (asks !== null && asks.length === 0));
  // A worker's build holds off (see the header): why, or null — not (or no longer) holding off.
  let heldOffLog = 0;
  const holdOff = async (): Promise<string | null> => {
    if (!opts.viaShim || !layout || !sharedAsk()) return null;
    const why = opts.resumed ? await cleanStamp(lockPath, layout).then((c) => ("why" in c ? c.why : null)) : await toolkitInFlux(lockPath, layout);
    if (why === null) return null;
    const min = Math.round((Date.now() - asked.getTime()) / 60_000);
    if (Date.now() - asked.getTime() >= LAKE_LOCK_TIMING.fluxWaitMaxMs) {
      if (heldOffLog >= 0) log(`[lake-lock] ${what}: ${why}, still after ${min} min held off — running exclusive`);
      heldOffLog = -1;
      return null;
    }
    if (Date.now() - heldOffLog >= LAKE_LOCK_TIMING.progressMs) {
      heldOffLog = Date.now();
      log(`[lake-lock] ${what}: ${why} — holding off before building (${min} min so far, ${Math.round(LAKE_LOCK_TIMING.fluxWaitMaxMs / 60_000)} min at most; a worker's build does not run exclusive meanwhile)`);
    }
    return why;
  };
  for (;;) {
    // holding off, nothing taken
    while ((await holdOff()) !== null) await sleep(LAKE_LOCK_TIMING.fluxWaitMs);
    let unlockPapers = async () => {};
    if (papers.length > 0) {
      const unlock = await lockPapers(lockPath, papers, what, log, compromised);
      if (unlock) unlockPapers = unlock;
      else { fallback = "a paper lock could not be taken"; papers = []; }
    }
    try {
      // a shared request passes the queue while no ticket there has waited long (`acquireShared`)
      const shared = sharedAsk();
      const { release, token } = shared ? await acquireShared(lockPath, what, log, compromised) : await acquireInTurn(lockPath, what, log, compromised);
      if (shared && layout) {
        const got = new Date();
        // a flux session opened (or the toolkit left unclean) since the look: let go (its paper
        // locks too), hold off again
        if ((await holdOff()) !== null) {
          await letGo(lockPath, token, release);
          continue;
        }
        fallback = await whyNotShared(lockPath, layout, papers, asks!, opts.files ?? []);
        const rec: SharedRecord = { token, host: LOCK_HOST, pid: process.pid, ...(process.env[RUN_SLUG_ENV] ? { slug: process.env[RUN_SLUG_ENV] } : {}), what, got: got.toISOString(), papers, ...(opts.pausable ? { pausable: true as const } : {}) };
        if (!fallback) fallback = await registerShared(lockPath, rec, log).then(() => null, (err) => `its shared record was not written (${message(err)})`);
        if (!fallback) {
          // the record stands before the mutex goes: an exclusive holder after it waits for it
          let ended = false;
          const file = sharedFile(lockPath, token);
          const refresh = setInterval(() => {
            const now = new Date();
            utimes(file, now, now).catch((err: NodeJS.ErrnoException) => {
              if (err.code === "ENOENT" && !ended && !lost) compromised(new Error(`the shared hold's record ${file} was removed (unrefreshed for ${HELD_STALE_MS / 60_000} min)`));
            });
          }, LAKE_LOCK_TIMING.updateMs);
          refresh.unref();
          try {
            await letGo(lockPath, token, release);
            return await within({ token, mode: "shared", papers });
          } finally {
            ended = true;
            clearInterval(refresh);
            await unlink(file).catch(() => {});
            await recordLockHold(path.dirname(lockPath), { lock: "lake", what, asked, got, released: new Date(), mode: "shared" });
          }
        }
      }
      // exclusive: once no shared hold stands
      let got = new Date();
      try {
        await drainShared(lockPath, token, what, log);
        // Never an exclusive hold over a toolkit commit on file (`commit.ts`), but a commit's own call
        // chain (its commit, recovery, `clear`/`undo`, a promotion's `honourCommit`): every builder,
        // stamp, flux session and promotion path waits for it to be finished — and a shared hold never
        // begins beside its flux session.
        if (!commitChain.getStore() && (await commitOnFileAt(lockPath))) {
          throw new Error(`[lake-lock] ${what}: refused — a toolkit commit is on file (\`paperformalizer toolkit-commit status\`): the next promotion rolls it forward, or settle it by hand (\`recover\`, \`clear <id>\`, \`undo\`)`);
        }
        got = new Date();
        return await within({ token, mode: "exclusive", papers: [], lost: () => lost });
      } finally {
        try {
          await letGo(lockPath, token, release);
        } finally {
          await recordLockHold(path.dirname(lockPath), { lock: "lake", what, asked, got, released: new Date(), mode: "exclusive", ...(fallback ? { fallback } : {}) });
        }
      }
    } finally {
      await unlockPapers();
    }
  }
}

/** The mode of the hold of `repoRoot`'s Lake lock this call chain is in, or null. */
export function lakeHoldMode(repoRoot: string): "shared" | "exclusive" | null {
  return heldLakeLocks.getStore()?.get(path.resolve(repoRoot, ".lake-build.lock"))?.mode ?? null;
}

/** What a scanner's shared turn returns when its `lake --no-build` run found something to build. */
export const WOULD_BUILD = "lake-would-build" as const;
/** `lake --no-build`'s exit code when a target is not up to date (nothing was built). */
export const LAKE_NO_BUILD_EXIT = 3;

/**
 * A scanner's Lake turns — a build of some papers' modules, then an exe that only reads oleans
 * (`candidate_scan`, `paper_index`) — under a shared hold of `papers` when that is safe, else as
 * before (`exclusive`: its own holds). Shared only when this chain holds no hold, shared mode is
 * on, the exe is up to date (`exeFresh`: `lake build --no-build <exe>`, asked before queueing) and
 * the hold granted is shared (the toolkit clean, the papers' imports covered: `whyNotShared`);
 * `shared` then builds the papers' modules alone and runs the exe as `lake --no-build exe …`, so
 * nothing but the papers' modules can be built under the hold — a run that finds something to
 * build returns `WOULD_BUILD` and the turns run `exclusive` after it. A hold granted exclusive
 * runs `exclusive` inside it.
 */
export async function withScannerHold<T>(
  repoRoot: string,
  /** The papers the scan reads besides the toolkit; [] for the toolkit alone; null: more than the
   *  shared hold can vouch for (every paper — the whole library's scan), always exclusive. */
  papers: readonly string[] | null,
  what: string,
  turns: { exeFresh: () => Promise<boolean>; shared: () => Promise<T | typeof WOULD_BUILD>; exclusive: () => Promise<T> },
  log: (line: string) => void = (l) => console.warn(l),
  /** Lean files besides the papers' own the shared turn elaborates (a probe importing them): their
   *  imports count as the papers' do (`LakeLockOptions.files`). */
  files: readonly string[] = [],
): Promise<T> {
  if (papers === null || lakeHoldMode(repoRoot) !== null || !(await lakeSharedModeOn(repoRoot)) || !(await turns.exeFresh().catch(() => false))) {
    return turns.exclusive();
  }
  let wouldBuild = false;
  const r = await withLakeBuildLock(repoRoot, async (): Promise<T | null> => {
    // granted exclusive (not clean, …): the turns as before, their holds this one (reentrant)
    if (lakeHoldMode(repoRoot) !== "shared") return turns.exclusive();
    const out = await turns.shared();
    if (out === WOULD_BUILD) { wouldBuild = true; return null; }
    return out;
  }, `${what} (shared)`, log, undefined, papers.length > 0 ? { papers, ...(files.length ? { files } : {}) } : { toolkitOnly: true });
  if (wouldBuild) {
    log(`[lake-lock] ${what}: the scanner would have built something under a shared hold — running it exclusive`);
    return turns.exclusive();
  }
  return r as T;
}

// Promotion holds the lock across a full build + lint + index chain, its Lake requests served
// first (`promotionHolds`); promotions waiting for it are served in arrival order
// (`promotionInTurn`), with no time limit.
/** A wait for the promotion lock at least this long is logged. */
export const PROMOTION_WAIT_LOG_MS = 60_000;

/**
 * Cross-process mutex serializing the WHOLE promotion step across concurrent `study` runs.
 * Unlike `withLakeBuildLock` (per-cwd, per-command), this wraps the entire promotion — barrel
 * edit + `lake build` + lints + index — so two runs can never interleave their toolkit edits or
 * race on the shared `.lake` build dir.
 *
 * Keyed on the toolkit root (the shared resource every promotion mutates); the study runner
 * passes `ToolkitConfig.lockPath` (`<toolkit>/.toolkit-promote.lock`, gitignore it).
 */
/** The promotion lock's waiters' tickets: served in arrival order, as the Lake lock's are. */
export const promotionQueueDir = (lockPath: string) => path.join(path.dirname(lockPath), ".lake", "paperformalizer", "promote-lock-queue");

/**
 * Wait in the promotion queue, then take the promotion lock: only the oldest live ticket tries it.
 * (Retrying it with back-off, as before, starved a long waiter — polling every 30 s — behind every
 * newcomer polling every second: promotions waited up to 3 h for a lock held minutes at a time.)
 * The lock itself is the same proper-lockfile lock, so older code waiting the old way is still
 * excluded (it may still take the lock out of turn). No time limit; progress is logged.
 */
async function promotionInTurn(lockPath: string, log?: (line: string) => void, until?: () => Promise<boolean>): Promise<(() => Promise<void>) | null> {
  const queue = promotionQueueDir(lockPath);
  await mkdir(queue, { recursive: true });
  const asked = Date.now();
  const mine = `${String(asked).padStart(15, "0")}.${LOCK_HOST}.${process.pid}.${randomBytes(4).toString("hex")}`;
  const ticket = path.join(queue, mine);
  const slug = process.env[RUN_SLUG_ENV];
  const body = `${JSON.stringify({ host: LOCK_HOST, pid: process.pid, ...(slug ? { slug } : {}), what: "promotion" })}\n`;
  await writeFile(ticket, body);
  liveTickets.add(ticket);
  if (!exitHook) {
    exitHook = true;
    process.once("exit", () => { for (const t of liveTickets) { try { unlinkSync(t); } catch { /* gone */ } } });
  }
  const refresh = setInterval(() => {
    const now = new Date();
    utimes(ticket, now, now).catch(() => writeFile(ticket, body).catch(() => {}));
  }, LAKE_LOCK_TIMING.ticketRefreshMs);
  refresh.unref();
  try {
    let nextLog = asked + LAKE_LOCK_TIMING.firstLogMs;
    for (;;) {
      // (`withPromotionLockUntil`: the wait is over without the lock)
      if (until && (await until())) return null;
      const ahead = await aheadOf(queue, mine, body);
      if (ahead.first === null) {
        try {
          return await lockfile.lock(lockPath, { stale: STALE_MS, retries: 0, realpath: false });
        } catch (err) {
          if ((err as NodeJS.ErrnoException).code !== "ELOCKED") throw err;
        }
      }
      if (log && Date.now() >= nextLog) {
        log(`promotion lock: waiting for ${Math.round((Date.now() - asked) / 60_000)} min — ${ahead.first ? `${ahead.count} promotion(s) ahead` : "first in line; the lock is held"}`);
        nextLog = Date.now() + LAKE_LOCK_TIMING.progressMs;
      }
      await sleep(LAKE_LOCK_TIMING.pollMs);
    }
  } finally {
    clearInterval(refresh);
    liveTickets.delete(ticket);
    await unlink(ticket).catch(() => {});
  }
}

export async function withPromotionLock<T>(
  toolkitRoot: string,
  action: () => Promise<T>,
  lockPath: string = path.join(toolkitRoot, ".toolkit-promote.lock"),
  log?: (line: string) => void,
): Promise<T> {
  await ensureLockfileTarget(lockPath);
  const asked = Date.now();
  const release = (await promotionInTurn(lockPath, log))!;
  // How long the queue held this promotion back (the measure of whether promotions contend).
  const got = Date.now();
  const waited = got - asked;
  if (log && waited >= PROMOTION_WAIT_LOG_MS) log(`promotion lock: waited ${Math.round(waited / 60_000)} min`);
  try {
    // its Lake requests are served first (`promotionHolds`)
    return await promotionHolds.run(true, action);
  } finally {
    try {
      await release();
    } finally {
      await recordLockHold(toolkitRoot, { lock: "promote", what: "promotion", asked: new Date(asked), got: new Date(got), released: new Date() });
    }
  }
}

/**
 * `withPromotionLock`, except that the wait ends WITHOUT the lock once `until` says so (asked before
 * every look at the queue): null then, the ticket withdrawn. A commit bound to its base waits so
 * (`shared/commit.ts`): for the lock, or until the base moved past it.
 */
export async function withPromotionLockUntil<T>(
  toolkitRoot: string,
  action: () => Promise<T>,
  lockPath: string,
  log: ((line: string) => void) | undefined,
  until: () => Promise<boolean>,
): Promise<{ value: T } | null> {
  await ensureLockfileTarget(lockPath);
  const asked = Date.now();
  const release = await promotionInTurn(lockPath, log, until);
  if (!release) return null;
  const got = Date.now();
  if (log && got - asked >= PROMOTION_WAIT_LOG_MS) log(`promotion lock: waited ${Math.round((got - asked) / 60_000)} min`);
  try {
    return { value: await promotionHolds.run(true, action) };
  } finally {
    try {
      await release();
    } finally {
      await recordLockHold(toolkitRoot, { lock: "promote", what: "promotion", asked: new Date(asked), got: new Date(got), released: new Date() });
    }
  }
}

// A store's read-modify-write holds its lock briefly (the ledger: about a second; the statement
// store: about 10 s on 210 MB): waiters poll briefly and often, up to about 2.7 hours in all.
const STORE_RETRIES = { retries: 5_000, factor: 1.2, minTimeout: 50, maxTimeout: 2_000 };
// A holder killed mid-update (a job cancelled) frees the lock after STORE_STALE_MS, not the hour a
// build lock waits. Its holder refreshes the lock every STORE_UPDATE_MS, so another node — whose NFS
// attribute cache may show the lock up to a minute old, its clock a few seconds off — sees it at most
// about 1.5 min old while it is held: well inside 5 min, even with the event loop blocked for tens
// of seconds by a 210 MB JSON parse.
export const STORE_STALE_MS = 5 * 60_000;
const STORE_UPDATE_MS = 30_000;

/** Exclusive hold of `lockPath` for a short read-modify-write of a shared file (the toolkit ledger,
 *  the statement store). */
export async function withStoreLock<T>(lockPath: string, action: () => Promise<T>): Promise<T> {
  await ensureLockfileTarget(lockPath);
  const release = await lockfile.lock(lockPath, { stale: STORE_STALE_MS, update: STORE_UPDATE_MS, retries: STORE_RETRIES, realpath: false });
  try {
    return await action();
  } finally {
    await release();
  }
}
