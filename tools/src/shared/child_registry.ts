/**
 * Registry of every child process the runner spawns (codex exec, claude workers, lake/lean,
 * lean-lsp and MCP servers, latex/unzip helpers), and the stop path that tears them down.
 *
 * Why it exists: `spawnWithInactivityTimeout` starts each child DETACHED (its own process
 * group, so an inactivity kill can reap the whole tree). The same detachment means a
 * `kill -TERM -<runner pgid>` never reaches those children: they are reparented to init and
 * keep running (and billing) until killed by hand. So the runner kills them itself:
 *
 *   - every spawn registers here and unregisters when it settles;
 *   - `installStopHandlers` (once, at CLI start) turns SIGTERM/SIGINT/SIGHUP into: stop
 *     spawning, SIGTERM each child's process group (or the pid when it leads none), SIGKILL
 *     what is left after a grace period, log `stopped N child process(es)`, exit 128+signo;
 *     a normal exit SIGKILLs any straggler synchronously;
 *   - while a run is known, the live set is persisted to `runs/<slug>/logs/children.json`
 *     so `theoremchecker verify … --stop` can clean up after a crash or an external SIGKILL
 *     (`stopRecordedRun`), matching each recorded pid by its start time so a reused pid is
 *     never signalled.
 */
import { execFile, execFileSync, type ChildProcess } from "node:child_process";
import { existsSync, mkdirSync, readdirSync, readFileSync, renameSync, rmSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";

/** What kind of process a child is (free text; the runner uses codex|claude|lake|lean-lsp|mcp|…). */
export type ChildKind = string;

/** One live child, as held in memory and persisted to `children.json`. */
export interface ChildRecord {
  pid: number;
  kind: ChildKind;
  /** Caller-chosen label (codex marker, lake targets, …) for the log. */
  tag: string;
  /** ISO time the child was spawned. */
  started: string;
  /** Kernel start time of the pid (`<boot id>:<ticks>` on Linux, `ps lstart` elsewhere); null if unreadable. */
  startId: string | null;
  /** True when the child leads its own process group (spawned detached). */
  groupLeader: boolean;
  /** The command that was run (for the log and the cmdline fallback match). */
  cmd: string;
}

/** Shape of `runs/<slug>/logs/children.json`. */
export interface ChildrenFile {
  /** `host`: the machine the runner runs on — pids of another host of a shared mount are not ours to signal. */
  runner: { pid: number; startId: string | null; cmd: string; host?: string };
  /** Value of `THEOREMCHECKER_RUN_TAG` in every child's environment (identifies a leaderless group's members). */
  runTag: string;
  children: ChildRecord[];
}

/** Environment variable every child inherits, naming the runner that spawned it. */
export const RUN_TAG_ENV = "THEOREMCHECKER_RUN_TAG";
/** Grace between SIGTERM and SIGKILL. */
export const STOP_GRACE_MS = 2_000;

const children = new Map<number, ChildRecord>();
let stopping = false;
let childrenFile: string | null = null;
let handlersInstalled = false;

/** True once a stop signal has arrived: no new child may start. */
export function isStopping(): boolean {
  return stopping;
}

/**
 * Resolves at once unless the runner is stopping, in which case it NEVER resolves: a spawn or a
 * `mapLimit` slot that reaches it parks until the stop handler exits the process. Parking (not
 * throwing) keeps the pipeline from reacting to its own shutdown — no retry, no failure written
 * into the run state during the grace period.
 */
export function haltIfStopping(): Promise<void> {
  return stopping ? new Promise<void>(() => {}) : Promise.resolve();
}

/** Snapshot of the live children. */
export function liveChildren(): ChildRecord[] {
  return [...children.values()];
}

function writeChildrenFile(): void {
  if (!childrenFile) return;
  const body: ChildrenFile = {
    runner: { pid: process.pid, startId: processStartId(process.pid), cmd: process.argv.slice(1).join(" "), host: os.hostname() },
    runTag: process.env[RUN_TAG_ENV] ?? "",
    children: liveChildren(),
  };
  try {
    mkdirSync(path.dirname(childrenFile), { recursive: true });
    const tmp = `${childrenFile}.${process.pid}.tmp`;
    writeFileSync(tmp, `${JSON.stringify(body, null, 2)}\n`, "utf8");
    renameSync(tmp, childrenFile);
  } catch {
    /* best-effort: a failed write must never fail a spawn */
  }
}

/** Persist the live set to `file` from now on (null stops persisting and removes nothing). */
export function setChildrenFile(file: string | null): void {
  childrenFile = file;
  writeChildrenFile();
}

/** Remove the persisted file (the run is exiting and holds no children). */
export function clearChildrenFile(): void {
  if (childrenFile) rmSync(childrenFile, { force: true });
}

/**
 * Register a spawned child; returns its unregister function (idempotent). `groupLeader` is
 * true when the child was spawned detached (POSIX: its own process group).
 */
export function registerChild(
  pid: number | undefined,
  meta: { kind: ChildKind; tag?: string; groupLeader: boolean; cmd: string },
): () => void {
  if (pid == null) return () => {};
  const rec: ChildRecord = {
    pid,
    kind: meta.kind,
    tag: meta.tag ?? "",
    started: new Date().toISOString(),
    startId: processStartId(pid),
    groupLeader: meta.groupLeader && process.platform !== "win32",
    cmd: meta.cmd,
  };
  children.set(pid, rec);
  writeChildrenFile();
  let done = false;
  return () => {
    if (done) return;
    done = true;
    if (children.get(pid) === rec) children.delete(pid);
    writeChildrenFile();
  };
}

/** Register a `ChildProcess` and unregister it when it exits or fails to spawn. */
export function trackChild(
  child: ChildProcess,
  meta: { kind: ChildKind; tag?: string; groupLeader?: boolean; cmd: string },
): void {
  const unregister = registerChild(child.pid, { ...meta, groupLeader: meta.groupLeader ?? false });
  child.once("exit", unregister);
  child.once("error", unregister);
}

/** `execFile` (promise form), registered in the registry and refused once stopping. */
export async function execFileTracked(
  kind: ChildKind,
  cmd: string,
  args: string[],
  opts: { cwd?: string; timeout?: number; maxBuffer?: number; env?: NodeJS.ProcessEnv } = {},
): Promise<{ stdout: string; stderr: string }> {
  await haltIfStopping();
  return await new Promise((resolve, reject) => {
    const child = execFile(cmd, args, { ...opts, encoding: "utf8" }, (err, stdout, stderr) => {
      if (err) reject(Object.assign(err, { stdout, stderr }));
      else resolve({ stdout, stderr });
    });
    trackChild(child, { kind, tag: path.basename(cmd), cmd: [cmd, ...args].join(" ") });
  });
}

// ─── process identity ─────────────────────────────────────────────────────────

let bootIdCache: string | null | undefined;
function bootId(): string | null {
  if (bootIdCache === undefined) {
    try {
      bootIdCache = readFileSync("/proc/sys/kernel/random/boot_id", "utf8").trim();
    } catch {
      bootIdCache = null;
    }
  }
  return bootIdCache;
}

/** Fields of `/proc/<pid>/stat` after the `(comm)` field; index k-3 is field k of proc(5). */
function procStatFields(pid: number): string[] | null {
  try {
    const stat = readFileSync(`/proc/${pid}/stat`, "utf8");
    return stat.slice(stat.lastIndexOf(")") + 2).split(" ");
  } catch {
    return null;
  }
}

/** Start time of `pid` as a stable string (a reused pid gets a different one), or null. */
export function processStartId(pid: number): string | null {
  if (existsSync("/proc/self/stat")) {
    const f = procStatFields(pid);
    return f && f[19] ? `${bootId() ?? "boot"}:${f[19]}` : null;
  }
  if (process.platform === "win32") return null;
  try {
    const out = execFileSync("ps", ["-o", "lstart=", "-p", String(pid)], { encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] }).trim();
    return out || null;
  } catch {
    return null;
  }
}

/** Command line of `pid`, or null when it is gone/unreadable. */
export function processCmdline(pid: number): string | null {
  try {
    return readFileSync(`/proc/${pid}/cmdline`, "utf8").split("\0").filter(Boolean).join(" ");
  } catch {
    /* no /proc */
  }
  if (process.platform === "win32") return null;
  try {
    return execFileSync("ps", ["-o", "command=", "-p", String(pid)], { encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] }).trim() || null;
  } catch {
    return null;
  }
}

function pidAlive(pid: number): boolean {
  try {
    process.kill(pid, 0);
    return true;
  } catch (err) {
    return (err as NodeJS.ErrnoException).code === "EPERM";
  }
}

/** A leader-led group is alive while any member is; a plain child while its pid is. */
function recordAlive(r: Pick<ChildRecord, "pid" | "groupLeader">): boolean {
  if (r.groupLeader) {
    try {
      process.kill(-r.pid, 0);
      return true;
    } catch {
      /* group gone, or never a group: fall through to the pid */
    }
  }
  return pidAlive(r.pid);
}

function signalRecord(r: Pick<ChildRecord, "pid" | "groupLeader">, sig: NodeJS.Signals): void {
  if (r.groupLeader) {
    try {
      process.kill(-r.pid, sig);
      return;
    } catch {
      /* not (or no longer) a group: signal the pid */
    }
  }
  try {
    process.kill(r.pid, sig);
  } catch {
    /* already gone */
  }
}

const sleep = (ms: number) => new Promise<void>((r) => setTimeout(r, ms));

/** SIGTERM `targets`, wait up to `graceMs` for them to go, SIGKILL the rest; returns how many were alive. */
async function terminate(targets: Array<Pick<ChildRecord, "pid" | "groupLeader">>, graceMs: number): Promise<number> {
  const alive = targets.filter(recordAlive);
  for (const r of alive) signalRecord(r, "SIGTERM");
  const deadline = Date.now() + graceMs;
  while (Date.now() < deadline && alive.some(recordAlive)) await sleep(50);
  for (const r of alive) if (recordAlive(r)) signalRecord(r, "SIGKILL");
  return alive.length;
}

/**
 * Processes (other than this one) whose environment carries `RUN_TAG_ENV=runTag`, optionally only
 * those outside the process groups `exceptGroups` (Linux only; elsewhere none). Every child
 * inherits the tag, so this finds descendants that left their group (setsid) and survivors of a
 * group whose leader is gone.
 */
function taggedProcesses(runTag: string | undefined, exceptGroups: Set<number> = new Set()): number[] {
  if (!runTag || !existsSync("/proc/self/stat")) return [];
  const needle = `${RUN_TAG_ENV}=${runTag}`;
  const out: number[] = [];
  for (const name of readdirSync("/proc")) {
    const pid = Number(name);
    if (!Number.isInteger(pid) || pid <= 0 || pid === process.pid) continue;
    const pgrp = Number(procStatFields(pid)?.[2]);
    if (!Number.isInteger(pgrp) || exceptGroups.has(pgrp)) continue;
    try {
      if (readFileSync(`/proc/${pid}/environ`, "utf8").split("\0").includes(needle)) out.push(pid);
    } catch {
      /* gone, or another user's process */
    }
  }
  return out;
}

/**
 * Terminate every registered child (SIGTERM, grace, SIGKILL), plus any descendant carrying this
 * runner's tag outside the registered groups; returns how many were alive.
 */
export async function terminateChildren(graceMs: number = STOP_GRACE_MS): Promise<number> {
  const reg = liveChildren();
  const groups = new Set(reg.filter((r) => r.groupLeader).map((r) => r.pid));
  const escaped = taggedProcesses(process.env[RUN_TAG_ENV], groups)
    .filter((pid) => !reg.some((r) => r.pid === pid))
    .map((pid) => ({ pid, groupLeader: false }));
  return await terminate([...reg, ...escaped], graceMs);
}

/**
 * Terminate the live registered children of one kind (SIGTERM, grace, SIGKILL), leaving the
 * runner and its other children alone; returns how many were alive. Used when every in-flight
 * child of that kind is bound to fail the same way (a dead codex login).
 */
export async function terminateChildrenOfKind(kind: ChildKind, graceMs: number = STOP_GRACE_MS): Promise<number> {
  return await terminate(liveChildren().filter((r) => r.kind === kind), graceMs);
}

/**
 * Install the stop handlers once. SIGTERM/SIGINT/SIGHUP: set the stopping flag, terminate the
 * registry, log, clear `children.json`, exit 128+signo (a second signal during the grace period
 * SIGKILLs at once). Normal exit: SIGKILL any straggler synchronously and clear the file.
 */
export function installStopHandlers(opts: { graceMs?: number; log?: (line: string) => void } = {}): void {
  if (handlersInstalled) return;
  handlersInstalled = true;
  process.env[RUN_TAG_ENV] = `${process.pid}-${processStartId(process.pid) ?? Date.now()}`;
  const log = opts.log ?? ((line: string) => console.error(line));
  const onSignal = (sig: NodeJS.Signals): void => {
    const code = 128 + (os.constants.signals[sig] ?? 15);
    if (stopping) {
      for (const r of liveChildren()) signalRecord(r, "SIGKILL");
      process.exit(code);
    }
    stopping = true;
    void terminateChildren(opts.graceMs ?? STOP_GRACE_MS).then(
      (n) => {
        log(`[theoremchecker] ${sig}: stopped ${n} child process(es)`);
        children.clear();
        clearChildrenFile();
        process.exit(code);
      },
      () => process.exit(code),
    );
  };
  for (const sig of ["SIGTERM", "SIGINT", "SIGHUP"] as const) process.on(sig, onSignal);
  process.on("exit", () => {
    const left = liveChildren().filter(recordAlive);
    for (const r of left) signalRecord(r, "SIGKILL");
    if (left.length > 0) log(`[theoremchecker] exit: stopped ${left.length} child process(es)`);
    clearChildrenFile();
  });
}

// ─── `verify --stop`: clean up after a crashed or externally killed runner ────────

/** Whether a live pid is still the process that was recorded (start time; cmdline when no start time). */
function sameProcess(pid: number, startId: string | null, cmd: string): { ok: boolean; why: string } {
  const now = processStartId(pid);
  if (startId && now) return startId === now ? { ok: true, why: "" } : { ok: false, why: `start time differs (recorded ${startId}, now ${now})` };
  const bin = path.basename(cmd.split(" ")[0] ?? "");
  const line = processCmdline(pid) ?? "";
  return bin && line.includes(bin) ? { ok: true, why: "" } : { ok: false, why: `no start time to compare and the command line does not match '${bin}'` };
}

/**
 * Stop what `children.json` records: the runner first when it is still alive (its own handler
 * then tears its children down), then every recorded child still alive AND still the same
 * process, then any process carrying the run's tag in its environment (a descendant whose group
 * leader is gone, or that left its group).
 * A pid whose start time no longer matches is refused (reported, never signalled). The file is
 * removed at the end.
 */
export async function stopRecordedRun(
  file: string,
  opts: { graceMs?: number; log?: (line: string) => void } = {},
): Promise<{ stopped: number; refused: string[] }> {
  const log = opts.log ?? ((line: string) => console.log(line));
  const graceMs = opts.graceMs ?? STOP_GRACE_MS;
  const read = (): ChildrenFile | null => {
    try {
      return JSON.parse(readFileSync(file, "utf8")) as ChildrenFile;
    } catch {
      return null;
    }
  };
  const first = read();
  if (!first) {
    log(`[theoremchecker] --stop: no ${file}; nothing recorded to stop.`);
    return { stopped: 0, refused: [] };
  }
  const refused: string[] = [];
  let stopped = 0;
  const { runner } = first;
  // Recorded on another machine of a shared mount: its pids are not ours to read or signal,
  // and the file is its runner's to remove.
  if (runner.host && runner.host !== os.hostname()) {
    log(`[theoremchecker] --stop: ${file} was written on ${runner.host}, not ${os.hostname()}; stop the run there.`);
    return { stopped: 0, refused: [`runner pid ${runner.pid}: recorded on ${runner.host}`] };
  }
  if (runner.pid !== process.pid && pidAlive(runner.pid)) {
    const same = sameProcess(runner.pid, runner.startId, runner.cmd);
    if (same.ok) {
      log(`[theoremchecker] --stop: runner ${runner.pid} still alive; sending SIGTERM`);
      process.kill(runner.pid, "SIGTERM");
      const deadline = Date.now() + graceMs + 5_000;
      while (Date.now() < deadline && pidAlive(runner.pid)) await sleep(100);
      if (pidAlive(runner.pid)) process.kill(runner.pid, "SIGKILL");
      stopped += 1;
    } else refused.push(`runner pid ${runner.pid}: ${same.why}`);
  }
  // The runner's handler removes the file once it has stopped its children; whatever is still
  // recorded (the runner crashed, or was SIGKILLed) is ours to stop.
  const rec = read() ?? { ...first, children: [] };
  const targets: Array<Pick<ChildRecord, "pid" | "groupLeader">> = [];
  for (const c of rec.children) {
    if (!pidAlive(c.pid)) continue;
    const same = sameProcess(c.pid, c.startId, c.cmd);
    if (same.ok) targets.push(c);
    else refused.push(`${c.kind} pid ${c.pid}: ${same.why}`);
  }
  // Survivors of a group whose leader is gone, or that left their group: only processes
  // carrying this run's tag are ours.
  const groups = new Set(targets.filter((t) => t.groupLeader).map((t) => t.pid));
  for (const pid of taggedProcesses(rec.runTag, groups)) {
    if (!targets.some((t) => t.pid === pid)) targets.push({ pid, groupLeader: false });
  }
  stopped += await terminate(targets, graceMs);
  for (const r of refused) log(`[theoremchecker] --stop: left alone — ${r}`);
  rmSync(file, { force: true });
  log(`[theoremchecker] --stop: stopped ${stopped} process(es)`);
  return { stopped, refused };
}

/** Test-only: forget all state (no handlers are removed). */
export function resetChildRegistryForTest(): void {
  children.clear();
  stopping = false;
  childrenFile = null;
}

/** Test-only: flip the stopping flag without a signal. */
export function setStoppingForTest(v: boolean): void {
  stopping = v;
}
