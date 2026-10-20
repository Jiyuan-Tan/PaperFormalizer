import { mkdtemp, rm, writeFile, utimes } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { spawnSync } from "node:child_process";
import { existsSync, readFileSync, statSync } from "node:fs";
import { createRequire } from "node:module";
import { hostname } from "node:os";
import { HEARTBEAT_INTERVAL_MS, heartbeatAgeMs, heartbeatLiveness, heartbeatStaleMs, livenessOf, parseHeartbeat, withRunHeartbeatAt } from "../src/shared/run_heartbeat.js";

const dirs: string[] = [];

afterEach(async () => {
  await Promise.all(dirs.splice(0).map((dir) => rm(dir, { recursive: true, force: true })));
});

describe("run heartbeat", () => {
  it("keeps same-qid ownership while the parallel flag permits different qids", async () => {
    const previous = process.env.THEOREMCHECKER_ALLOW_PARALLEL;
    process.env.THEOREMCHECKER_ALLOW_PARALLEL = "1";
    const logsA = await mkdtemp(join(tmpdir(), "causalsmith-heartbeat-flag-a-"));
    const logsB = await mkdtemp(join(tmpdir(), "causalsmith-heartbeat-flag-b-"));
    dirs.push(logsA, logsB);

    let release!: () => void;
    const held = new Promise<void>((resolve) => { release = resolve; });
    try {
      const first = withRunHeartbeatAt(logsA, "qid-a", async () => { await held; });
      const second = withRunHeartbeatAt(logsB, "qid-b", async () => undefined);
      await second;
      await expect(
        withRunHeartbeatAt(logsA, "qid-a", async () => undefined),
      ).rejects.toMatchObject({ code: "theoremchecker_run_busy" });
      release();
      await first;
    } finally {
      if (previous === undefined) delete process.env.THEOREMCHECKER_ALLOW_PARALLEL;
      else process.env.THEOREMCHECKER_ALLOW_PARALLEL = previous;
    }
  });

  it("honours a fresh heartbeat written on another machine of the mount, and ignores a stale one", async () => {
    const logs = await mkdtemp(join(tmpdir(), "theoremchecker-heartbeat-host-"));
    dirs.push(logs);
    const hb = join(logs, ".run.active");
    // a pid this host cannot see: the owner runs elsewhere, so the pid proves nothing
    await writeFile(hb, "0x3ffffffe 2026-01-01T00:00:00.000Z tok host=elsewhere\n");
    await expect(
      withRunHeartbeatAt(logs, "paper", async () => undefined),
    ).rejects.toMatchObject({ code: "theoremchecker_run_busy", message: expect.stringContaining("on elsewhere") });
    // the same file an hour old: its owner stopped refreshing it
    const old = new Date(Date.now() - 60 * 60 * 1000);
    await utimes(hb, old, old);
    expect(await withRunHeartbeatAt(logs, "paper", async () => "ran")).toBe("ran");
  });

  it("lets the holder take its own lock again (the verify runner, then its F stages)", async () => {
    const logs = await mkdtemp(join(tmpdir(), "causalsmith-heartbeat-reentrant-"));
    dirs.push(logs);
    const inner = await withRunHeartbeatAt(logs, "paper", () =>
      withRunHeartbeatAt(logs, "paper", async () => "inner ran"),
    );
    expect(inner).toBe("inner ran");
    // released once the outer action ends
    await expect(withRunHeartbeatAt(logs, "paper", async () => "again")).resolves.toBe("again");
  });

  it("never steals an old heartbeat while its PID is still alive", async () => {
    const logs = await mkdtemp(join(tmpdir(), "causalsmith-heartbeat-live-old-"));
    dirs.push(logs);
    const lock = join(logs, ".run.active");
    await writeFile(lock, `${process.pid} spec 2000-01-01T00:00:00.000Z old-owner\n`);
    const old = new Date("2000-01-01T00:00:00.000Z");
    await utimes(lock, old, old);
    await expect(withRunHeartbeatAt(logs, "paper", async () => undefined))
      .rejects.toMatchObject({ code: "theoremchecker_run_busy" });
  });

  it("reclaims a heartbeat whose PID is dead", async () => {
    const logs = await mkdtemp(join(tmpdir(), "causalsmith-heartbeat-dead-"));
    dirs.push(logs);
    await writeFile(join(logs, ".run.active"), `999999999 spec 2000-01-01T00:00:00.000Z dead-owner\n`);
    let entered = false;
    await withRunHeartbeatAt(logs, "paper", async () => { entered = true; });
    expect(entered).toBe(true);
  });

  it("a dead owner's lock goes with it: a runner killed with its job on another machine left a fresh lock directory behind", async () => {
    const logs = await mkdtemp(join(tmpdir(), "causalsmith-heartbeat-deadlock-"));
    dirs.push(logs);
    const hb = join(logs, ".run.active");
    // a heartbeat of another host, long past its four beats, and the lock its runner last touched 5 minutes ago
    await writeFile(hb, `4242 2026-01-01T00:00:00.000Z tok host=elsewhere.example beat=15\n`);
    const old = new Date(Date.now() - 20 * 60 * 1000), lockAt = new Date(Date.now() - 5 * 60 * 1000);
    await utimes(hb, old, old);
    const { mkdirSync, utimesSync } = await import("node:fs");
    mkdirSync(`${hb}.lock`);
    utimesSync(`${hb}.lock`, lockAt, lockAt);
    await expect(withRunHeartbeatAt(logs, "qid-dead", async () => "ran")).resolves.toBe("ran");
  });

  it("allows only one of two simultaneous dead-owner reclaimers", async () => {
    const logs = await mkdtemp(join(tmpdir(), "causalsmith-heartbeat-dead-race-"));
    dirs.push(logs);
    await writeFile(join(logs, ".run.active"), `999999999 spec 2000-01-01T00:00:00.000Z dead-owner\n`);
    let entered = 0;
    let enteredOnce!: () => void;
    const oneEntered = new Promise<void>((resolve) => { enteredOnce = resolve; });
    let rejectedOnce!: (error: unknown) => void;
    const oneRejected = new Promise<unknown>((resolve) => { rejectedOnce = resolve; });
    let release!: () => void;
    const held = new Promise<void>((resolve) => { release = resolve; });
    const run = () => withRunHeartbeatAt(logs, "paper", async () => {
      entered += 1;
      enteredOnce();
      await held;
    });
    const wrap = (p: Promise<void>) => p.then(
      () => ({ status: "fulfilled" as const }),
      (error: unknown) => { rejectedOnce(error); return { status: "rejected" as const, error }; },
    );
    const first = wrap(run());
    const second = wrap(run());
    await oneEntered;
    expect(await oneRejected).toMatchObject({ code: "theoremchecker_run_busy" });
    expect(entered).toBe(1);
    release();
    const results = await Promise.all([first, second]);
    expect(results.filter((r) => r.status === "rejected")).toHaveLength(1);
  });

  it("the heartbeat names its host, its beat and its process's start; it is gone when the action ends", async () => {
    const logs = await mkdtemp(join(tmpdir(), "theoremchecker-heartbeat-tokens-"));
    dirs.push(logs);
    const hb = join(logs, ".run.active");
    await withRunHeartbeatAt(logs, "paper", async () => {
      const read = parseHeartbeat(readFileSync(hb, "utf8"), statSync(hb).mtimeMs)!;
      expect(read).toMatchObject({ pid: process.pid, host: hostname(), beatMs: HEARTBEAT_INTERVAL_MS });
      expect(read.ownerToken).toMatch(/^[0-9a-f-]{36}$/);
      expect(heartbeatLiveness(hb)).toMatchObject({ live: true, pid: process.pid, elsewhere: null, why: "pid-alive" });
    });
    expect(heartbeatLiveness(hb)).toMatchObject({ live: false, why: "no-heartbeat" });
  });

  it("a heartbeat of this host whose pid now belongs to a process started at another time is not its owner", async () => {
    const logs = await mkdtemp(join(tmpdir(), "theoremchecker-heartbeat-reuse-"));
    dirs.push(logs);
    const hb = join(logs, ".run.active");
    await writeFile(hb, `${process.pid} 2026-01-01T00:00:00.000Z tok host=${hostname()} beat=15 start=1\n`);
    if (process.platform === "linux") expect(heartbeatLiveness(hb)).toMatchObject({ live: false, why: "pid-reused" });
    // with no start on record the pid alone decides
    await writeFile(hb, `${process.pid} 2026-01-01T00:00:00.000Z tok host=${hostname()}\n`);
    expect(heartbeatLiveness(hb)).toMatchObject({ live: true, why: "pid-alive" });
  });
});

describe("run heartbeat: a runner that exits without unwinding", () => {
  it("takes its heartbeat with it (a stop ends the process from a signal handler: no finally runs)", async () => {
    const logs = await mkdtemp(join(tmpdir(), "theoremchecker-heartbeat-exit-"));
    dirs.push(logs);
    const script = join(logs, "runner.mts");
    await writeFile(script, `import { existsSync } from "node:fs";
import { withRunHeartbeatAt } from ${JSON.stringify(new URL("../src/shared/run_heartbeat.ts", import.meta.url).href)};
await withRunHeartbeatAt(${JSON.stringify(logs)}, "paper", async () => { if (!existsSync(${JSON.stringify(join(logs, ".run.active"))})) process.exit(1); process.exit(7); });
`);
    const r = spawnSync(process.execPath, [createRequire(import.meta.url).resolve("tsx/cli"), script], { encoding: "utf8" });
    expect(r.status).toBe(7);
    expect(existsSync(join(logs, ".run.active"))).toBe(false);
  }, 60_000);
});

describe("liveness: one rule", () => {
  const probe = (alivePids: number[], starts: Record<number, string> = {}) => ({ host: "here", alive: (pid: number) => alivePids.includes(pid), start: (pid: number) => starts[pid] ?? null });
  const hb = (text: string) => parseHeartbeat(text, 0);
  const stale = heartbeatStaleMs(15_000);
  it("the threshold follows the beat the file records: four missed beats and a margin; 30 min for a file that records none", () => {
    expect(stale).toBe(90_000);
    expect(heartbeatStaleMs(null)).toBe(30 * 60_000);
  });
  it.each([
    // heartbeat, its age, pids alive here (→ start) : live, why, pid, elsewhere
    ["no file", null, 0, [], {}, false, "no-heartbeat", null, null],
    ["being written (empty)", "\n", 0, [7], {}, false, "no-heartbeat", null, null],
    ["this host, pid alive", "7 t tok host=here beat=15", 0, [7], {}, true, "pid-alive", 7, null],
    ["this host, pid alive, however old the file (a blocked beat is not a death)", "7 t tok host=here beat=15", 10 * stale, [7], {}, true, "pid-alive", 7, null],
    ["this host, pid gone, however fresh the file", "7 t tok host=here beat=15", 0, [], {}, false, "pid-gone", 7, null],
    ["this host, same start", "7 t tok host=here beat=15 start=100", 0, [7], { 7: "100" }, true, "pid-alive", 7, null],
    ["this host, pid reused (another start)", "7 t tok host=here beat=15 start=100", 0, [7], { 7: "999" }, false, "pid-reused", 7, null],
    ["this host, start unknown here (not Linux)", "7 t tok host=here beat=15 start=100", 0, [7], {}, true, "pid-alive", 7, null],
    ["no host on record: read as this host", "7 t tok", 0, [7], {}, true, "pid-alive", 7, null],
    ["the older layout (a token after the pid)", "7 spec t tok", 0, [7], {}, true, "pid-alive", 7, null],
    ["another host, fresh — the pid, though alive here, is not asked", "7 t tok host=there beat=15", stale - 1, [], {}, true, "fresh", null, "there"],
    ["another host, stale — though that pid lives here", "7 t tok host=there beat=15", stale, [7], {}, false, "stale", null, "there"],
    ["another host, no beat on record: fresh within 30 min", "7 t tok host=there", 29 * 60_000, [], {}, true, "fresh", null, "there"],
    ["another host, no beat on record: stale after", "7 t tok host=there", 31 * 60_000, [], {}, false, "stale", null, "there"],
  ] as const)("%s", (_name, text, ageMs, alive, starts, live, why, pid, elsewhere) => {
    expect(livenessOf(text === null ? null : hb(text), ageMs, probe([...alive], starts))).toMatchObject({ live, why, pid, elsewhere });
  });
  it("reads the owner's timestamp and token past the key=value tokens, in any order", () => {
    expect(hb("7 2026-01-01T00:00:00.000Z tok host=h beat=15 start=3")).toMatchObject({ pid: 7, timestamp: "2026-01-01T00:00:00.000Z", ownerToken: "tok", host: "h", beatMs: 15_000, start: "3" });
    expect(hb("7 start=3 2026-01-01T00:00:00.000Z host=h tok")).toMatchObject({ timestamp: "2026-01-01T00:00:00.000Z", ownerToken: "tok", beatMs: null });
  });
  it("ages a heartbeat by this process's clock once it has seen it beat: the owner host's clock may be off either way", () => {
    const t = 1_000_000_000;
    // first seen: only the mtime tells (never negative — a clock ahead of ours)
    expect(heartbeatAgeMs("skew/behind", t - 600_000, t)).toBe(600_000);
    expect(heartbeatAgeMs("skew/ahead", t + 600_000, t)).toBe(0);
    // the owner's clock runs 10 min behind: a beat seen to arrive came since the last look, whatever its mtime says
    expect(heartbeatAgeMs("skew/behind", t - 600_000 + 15_000, t + 1000)).toBe(1000);
    expect(heartbeatAgeMs("skew/behind", t - 600_000 + 15_000, t + 16_000)).toBe(16_000);
    // … and 10 min ahead: one that stops beating ages from when it was last seen to beat, not from its mtime
    expect(heartbeatAgeMs("skew/ahead", t + 600_000, t + 100_000)).toBe(100_000);
    // a beat that arrived between two looks far apart is no older than the first of them
    expect(heartbeatAgeMs("skew/sparse", t, t)).toBe(0);
    expect(heartbeatAgeMs("skew/sparse", t + 50_000, t + 60_000)).toBe(10_000);
  });
});
