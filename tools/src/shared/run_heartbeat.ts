/**
 * Per-run heartbeat for LeanSmith pipelines.
 *
 * A per-qid concurrency lock. Two invocations on distinct runs
 * can run side by side; a second invocation on the same qid is refused.
 *
 * Heartbeat file: `<formalizationDir(qid)>/logs/.run.active`
 *   line 1: `<pid> <iso-timestamp> <unique-owner-token> host=<hostname> beat=<seconds>
 *   start=<process start>` (an older file carries an extra run-coordinate token after
 *   the pid, which the reader skips, and none of the `key=` tokens). The host lets a reader on
 *   another machine of the shared mount tell a run that is live elsewhere (its pid means nothing
 *   here) from a stale file: elsewhere, the heartbeat's mtime — refreshed every `beat` seconds —
 *   is the only liveness signal. On the owner's host the pid decides, and `start` tells the
 *   owner from a later process that got its pid.
 *
 * `heartbeatLiveness` is the one reading of the file: the runner's own busy check, the UI and
 * (restated in plain JS) `scripts/orch.mjs` all decide by its rule.
 *
 * The actual mutex is `proper-lockfile`'s atomic sibling lock directory; the
 * heartbeat file is owner metadata for operators. This makes stale recovery
 * and simultaneous contenders single-writer safe.
 *
 * Legacy migration: a live PID recorded by the former heartbeat-only scheme is
 * still honored even when no sibling lock directory exists.
 *
 * Re-entrant within one process: the verify runner holds the lock for its whole life and the
 * F-stage pipeline it calls takes the same lock again — a call nested inside the holder's action
 * (same async context) just runs; a concurrent call from elsewhere in the process is refused.
 */
import { closeSync, existsSync, fstatSync, mkdirSync, openSync, readFileSync, unlinkSync, utimesSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import process from "node:process";
import { randomUUID } from "node:crypto";
import { AsyncLocalStorage } from "node:async_hooks";
import lockfile from "proper-lockfile";

import { ensureLogsDir } from "../paths.js";

const LOCK_STALE_MS = 30 * 60 * 1000;
/** The lock of an owner whose heartbeat is on file and dead (proper-lockfile's floor is 2 s). */
const LOCK_DEAD_OWNER_STALE_MS = 2000;
// proper-lockfile refreshes its own mutex mtime at this pace.
const LOCK_UPDATE_MS = 5 * 60 * 1000;
/** How often the owner touches its heartbeat (recorded in it as `beat=`): on a timer, so a long
 *  model call beats like any other time. */
export const HEARTBEAT_INTERVAL_MS = 15_000;

/**
 * How old a heartbeat may be before a reader that cannot see its owner's pid takes the owner for
 * gone: four missed beats and the mount's attribute cache. A file that records no beat is from a
 * runner that touched it every 5 min.
 */
export function heartbeatStaleMs(beatMs: number | null): number {
  return beatMs == null ? LOCK_STALE_MS : 4 * beatMs + 30_000;
}

/** Heartbeat paths held by the enclosing async context (re-entrancy). */
const held = new AsyncLocalStorage<ReadonlySet<string>>();

function isPidAlive(pid: number): boolean {
  if (!Number.isFinite(pid) || pid <= 0) return false;
  try {
    process.kill(pid, 0);
    return true;
  } catch (err) {
    // EPERM: alive, another user's process
    return (err as NodeJS.ErrnoException).code === "EPERM";
  }
}

/** When `pid` started (Linux: clock ticks since boot; null elsewhere): a reused pid has another. */
function processStart(pid: number): string | null {
  try {
    return readFileSync(`/proc/${pid}/stat`, "utf8").split(") ").pop()!.split(" ")[19] ?? null;
  } catch {
    return null;
  }
}

export interface ExistingHeartbeat {
  pid: number;
  timestamp: string;
  ownerToken: string;
  /** Machine the owner runs on; null for a file written before the host was recorded. */
  host: string | null;
  /** The owner's refresh interval; null for a file written before it was recorded (5 min then). */
  beatMs: number | null;
  /** The owner's start time on its host (`processStart`), when recorded. */
  start: string | null;
  mtimeMs: number;
  path: string;
}

/** How often an apply of a promotion round touches its `apply_<R>.pid` (seconds, recorded as `beat=`). */
export const APPLY_BEAT_S = 60;

/** The line of an `apply_<R>.pid`: a heartbeat without a timestamp — the pid, its host and its
 *  beat — so its liveness is read by the runner's rule (`heartbeatLiveness`), on any machine of the mount. */
export function applyPidLine(pid: number): string {
  return `${pid} host=${os.hostname()} beat=${APPLY_BEAT_S}\n`;
}

/** The heartbeat's text parsed (null when it names no pid: empty, or being written). */
export function parseHeartbeat(text: string, mtimeMs: number, hbPath = ""): ExistingHeartbeat | null {
  const all = text.trim().split(/\s+/);
  const token = (key: string): string | null => all.find((f) => f.startsWith(`${key}=`))?.slice(key.length + 1) ?? null;
  const [pidStr, ...rest] = all.filter((f) => !/^(host|beat|start)=/.test(f));
  const [timestamp = "", ownerToken = ""] = rest.length >= 3 ? rest.slice(1) : rest;
  const pid = Number(pidStr);
  if (!pidStr || !Number.isFinite(pid)) return null;
  const beat = Number(token("beat"));
  return { pid, timestamp, ownerToken, host: token("host"), beatMs: Number.isFinite(beat) && beat > 0 ? beat * 1000 : null, start: token("start"), mtimeMs, path: hbPath };
}

/** Read through an open file: on NFS the open revalidates the attributes a bare stat may answer from cache. */
function readHeartbeat(hbPath: string): ExistingHeartbeat | null {
  let fd: number;
  try {
    fd = openSync(hbPath, "r");
  } catch {
    return null;
  }
  try {
    return parseHeartbeat(readFileSync(fd, "utf8"), fstatSync(fd).mtimeMs, hbPath);
  } catch {
    return null;
  } finally {
    closeSync(fd);
  }
}

/** Per heartbeat file: the mtime last seen, when this process's clock says it appeared, and when it was last looked at. */
const beatsSeen = new Map<string, { mtimeMs: number; at: number; looked: number }>();

/**
 * The heartbeat's age on THIS process's clock. Its mtime is the owner host's time, and the two
 * clocks may differ: a beat seen to arrive between two looks is placed between them, so a process
 * that keeps looking (the UI's watcher, every second) measures by its own clock alone. Only a
 * beat never seen to change is aged by its mtime (never negative).
 */
export function heartbeatAgeMs(hbPath: string, mtimeMs: number, now: number = Date.now()): number {
  const seen = beatsSeen.get(hbPath);
  if (seen && seen.mtimeMs === mtimeMs) {
    seen.looked = now;
    return Math.max(0, now - seen.at);
  }
  // (an mtime that moved back is no beat: a file put back, aged like one first seen)
  const at = Math.min(now, Math.max(seen && mtimeMs > seen.mtimeMs ? seen.looked : -Infinity, mtimeMs));
  beatsSeen.set(hbPath, { mtimeMs, at, looked: now });
  return now - at;
}

export interface Liveness {
  live: boolean;
  /** The owner's pid when it runs on this host (the only place it can be signalled). */
  pid: number | null;
  /** The owner's host when it is another machine. */
  elsewhere: string | null;
  /** When the owner took the run (the heartbeat's timestamp). */
  since: string;
  why: "no-heartbeat" | "pid-alive" | "pid-gone" | "pid-reused" | "fresh" | "stale";
}

/**
 * Whether a heartbeat's owner is alive. On the host that wrote it (or a file with no host): its
 * pid lives and, where both are known, started when the owner did. Elsewhere a pid can be neither
 * signalled nor trusted: the file is fresher than `heartbeatStaleMs` of its beat. Pure — `probe`
 * is this machine.
 */
export function livenessOf(
  hb: ExistingHeartbeat | null,
  ageMs: number,
  probe: { host: string; alive: (pid: number) => boolean; start: (pid: number) => string | null },
): Liveness {
  if (!hb) return { live: false, pid: null, elsewhere: null, since: "", why: "no-heartbeat" };
  if (hb.host != null && hb.host !== probe.host) {
    const live = ageMs < heartbeatStaleMs(hb.beatMs);
    return { live, pid: null, elsewhere: hb.host, since: hb.timestamp, why: live ? "fresh" : "stale" };
  }
  const here = { pid: hb.pid > 0 ? hb.pid : null, elsewhere: null, since: hb.timestamp };
  if (!probe.alive(hb.pid)) return { live: false, ...here, why: "pid-gone" };
  const now = hb.start == null ? null : probe.start(hb.pid);
  if (now != null && now !== hb.start) return { live: false, ...here, why: "pid-reused" };
  return { live: true, ...here, why: "pid-alive" };
}

/** `livenessOf` the heartbeat file at `hbPath`, as this machine sees it now. */
export function heartbeatLiveness(hbPath: string, now: number = Date.now()): Liveness {
  const hb = readHeartbeat(hbPath);
  return livenessOf(hb, hb ? heartbeatAgeMs(hbPath, hb.mtimeMs, now) : 0, { host: os.hostname(), alive: isPidAlive, start: processStart });
}

export async function withRunHeartbeat<T>(
  repoRoot: string,
  qid: string,
  action: () => Promise<T>,
): Promise<T> {
  return withRunHeartbeatAt(ensureLogsDir(repoRoot, qid), qid, action);
}

/**
 * Run a single-writer heartbeat in an explicit log directory.
 */
export async function withRunHeartbeatAt<T>(
  logDirectory: string,
  qid: string,
  action: () => Promise<T>,
): Promise<T> {
  // The heartbeat is colocated with the durable per-run logs, so a stale lock
  // is visible to the operator alongside the agent-call transcript.
  mkdirSync(logDirectory, { recursive: true });
  const hbPath = path.join(logDirectory, ".run.active");
  const outer = held.getStore();
  if (outer?.has(hbPath)) return action();

  // Honor a live owner from the former heartbeat-only implementation. New
  // contenders are serialized by the sibling `.run.active.lock` directory.
  const existing = readHeartbeat(hbPath);
  if (existing && heartbeatLiveness(hbPath).live) {
    const ageS = Math.round((Date.now() - existing.mtimeMs) / 1000);
    throw Object.assign(
      new Error(
        `another leansmith run is active on qid ${qid} ` +
          `(PID ${existing.pid}${existing.host ? ` on ${existing.host}` : ""}, ` +
          `heartbeat age ${ageS}s at ${hbPath}). ` +
          `Wait for it to finish, kill PID ${existing.pid} and remove the ` +
          `heartbeat if you are certain it is stale.`,
      ),
      { code: "leansmith_run_busy" },
    );
  }

  if (!existsSync(hbPath)) {
    try {
      writeFileSync(hbPath, "\n", { flag: "wx" });
    } catch {
      // Another contender created the lock target.
    }
  }
  let release: (() => Promise<void>) | null = null;
  try {
    // A heartbeat on file that the one liveness rule calls dead (a runner killed with its job, on
    // this host or another) leaves its lock behind: that lock is stale now, not in half an hour.
    release = await lockfile.lock(hbPath, {
      stale: existing ? LOCK_DEAD_OWNER_STALE_MS : LOCK_STALE_MS,
      update: LOCK_UPDATE_MS,
      retries: 0,
      realpath: false,
    });
  } catch (err) {
    if ((err as NodeJS.ErrnoException).code === "ELOCKED") {
      const winner = readHeartbeat(hbPath);
      throw Object.assign(
        new Error(
          `another leansmith run just claimed qid ${qid}` +
            `${winner ? ` (PID ${winner.pid})` : ""}.`,
        ),
        { code: "leansmith_run_busy" },
      );
    }
    throw err;
  }

  const ownerToken = randomUUID();
  const start = processStart(process.pid);
  const payload = `${process.pid} ${new Date().toISOString()} ${ownerToken} host=${os.hostname()} beat=${HEARTBEAT_INTERVAL_MS / 1000}${start ? ` start=${start}` : ""}\n`;
  writeFileSync(hbPath, payload);
  const drop = (): void => {
    try {
      // Only unlink if we still own it. A unique token (not merely PID) also
      // distinguishes overlapping calls made by the same long-lived process.
      if (readHeartbeat(hbPath)?.ownerToken === ownerToken) unlinkSync(hbPath);
    } catch {
      // best-effort
    }
  };
  // A stop (SIGTERM → `process.exit` in the stop handlers) or a fatal error unwinds no `finally`:
  // the file goes on exit, so a reader on another host need not wait for it to go stale.
  process.once("exit", drop);
  // The beat: the file's mtime, the only sign of life a reader on another host has.
  const refreshTimer = setInterval(() => {
    try {
      if (readHeartbeat(hbPath)?.ownerToken !== ownerToken) return;
      const now = new Date();
      utimesSync(hbPath, now, now);
    } catch {
      // best-effort: heartbeat may have been stolen or deleted out-of-band.
    }
  }, HEARTBEAT_INTERVAL_MS);
  // Don't keep the event loop alive solely on this timer.
  if (typeof refreshTimer.unref === "function") refreshTimer.unref();
  try {
    return await held.run(new Set([...(outer ?? []), hbPath]), action);
  } finally {
    clearInterval(refreshTimer);
    process.removeListener("exit", drop);
    drop();
    if (release) await release();
  }
}
