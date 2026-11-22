// The Lake build lock: reentrant within one call chain (a gate holds it across its commands), still
// exclusive between independent callers; handed over in arrival order, waited for without a time
// limit, excluding older code that only knows the mutex; dead waiters and dead holders do not block
// it for long; every hold is recorded. Shared holds (below). The promotion lock logs a long wait.
import { execFile } from "node:child_process";
import { existsSync } from "node:fs";
import { chmod, mkdir, mkdtemp, readdir, readFile, rm, stat, utimes, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import lockfile from "proper-lockfile";
import { afterAll, afterEach, beforeAll, beforeEach, describe, expect, it } from "vitest";
import {
  LAKE_LOCK_CLEAN_BUILD, LAKE_LOCK_HELD_ENV, LAKE_LOCK_TIMING, LOCK_HOST, lakeCleanStampFile, lakeFluxFile, lakeLockChildEnv, lakeLockQueueDir,
  lakeFluxSessionsDir, lakePaperLocksDir, lakeSharedDir, stampToolkitClean, toolkitFluxOff, toolkitFluxOn, withLakeBuildLock, withPromotionLock,
  lakeHoldMode, lakeWriterWaiting, WOULD_BUILD, withScannerHold, withToolkitFlux,
} from "../../src/shared/build_mutex.js";
import { readLockHolds, summarizeLockHolds } from "../../src/shared/lock_holds.js";

const tmp: string[] = [];
const timing = { ...LAKE_LOCK_TIMING };
beforeEach(() => Object.assign(LAKE_LOCK_TIMING, { pollMs: 20, ticketRefreshMs: 50, ticketStaleMs: 5 * 60_000, firstLogMs: 100, progressMs: 200, fluxWaitMs: 50 }));
afterEach(async () => {
  Object.assign(LAKE_LOCK_TIMING, timing);
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});
const tempRoot = async () => {
  const root = await mkdtemp(path.join(os.tmpdir(), "lake-lock-"));
  tmp.push(root);
  return root;
};
const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));
/** Whether `p` is still pending after `ms`. */
const pendingAfter = async (p: Promise<unknown>, ms: number) => Promise.race([p.then(() => false), sleep(ms).then(() => true)]);
const quiet = () => {};

describe("withLakeBuildLock", () => {
  it("a nested call in the holder's chain runs at once; an independent caller waits for the holder", async () => {
    const root = await tempRoot();
    const order: string[] = [];
    let release!: () => void;
    const gate = new Promise<void>((r) => { release = r; });
    const holder = withLakeBuildLock(root, async () => {
      order.push("outer");
      await withLakeBuildLock(root, async () => { order.push("nested"); });
      await gate;
      order.push("outer done");
    });
    // let the holder take the lock
    await sleep(300);
    const other = withLakeBuildLock(root, async () => { order.push("other"); }, "other", quiet);
    await sleep(500);
    expect(order).toEqual(["outer", "nested"]);
    release();
    await Promise.all([holder, other]);
    expect(order).toEqual(["outer", "nested", "outer done", "other"]);
  }, 20_000);

  it("promotions are handed the promotion lock in arrival order, a newcomer never ahead of a long waiter", async () => {
    const root = await tempRoot();
    const order: string[] = [];
    let release!: () => void;
    const gate = new Promise<void>((r) => { release = r; });
    const first = withPromotionLock(root, async () => { order.push("holder"); await gate; });
    await sleep(100);
    const early = withPromotionLock(root, async () => { order.push("early"); });
    await sleep(300);
    const late = withPromotionLock(root, async () => { order.push("late"); });
    await sleep(100);
    const queue = await readdir(path.join(root, ".lake", "paperformalizer", "promote-lock-queue"));
    expect(queue).toHaveLength(2);
    release();
    await Promise.all([first, early, late]);
    expect(order).toEqual(["holder", "early", "late"]);
    expect(await readdir(path.join(root, ".lake", "paperformalizer", "promote-lock-queue"))).toEqual([]);
  });

  it("a promotion holder's Lake request goes to the head of the queue; the rest keep arrival order", async () => {
    const root = await tempRoot();
    const order: string[] = [];
    let release!: () => void;
    const gate = new Promise<void>((r) => { release = r; });
    const first = withLakeBuildLock(root, async () => { order.push("holder"); await gate; }, "holder", () => {});
    await sleep(100);
    const paperA = withLakeBuildLock(root, async () => { order.push("paperA"); }, "paperA", () => {});
    await sleep(60);
    const paperB = withLakeBuildLock(root, async () => { order.push("paperB"); }, "paperB", () => {});
    await sleep(60);
    const promo = withPromotionLock(root, () => withLakeBuildLock(root, async () => { order.push("promotion"); }, "promotion gate", () => {}));
    await sleep(200);
    const names = (await readdir(lakeLockQueueDir(path.join(root, ".lake-build.lock")))).sort();
    expect(names[0]).toMatch(/^000000000000000\./);
    release();
    await Promise.all([first, paperA, paperB, promo]);
    expect(order).toEqual(["holder", "promotion", "paperA", "paperB"]);
  });

  it("hands the lock over in arrival order, whatever order the mutex would pick", async () => {
    const root = await tempRoot();
    const order: string[] = [];
    let release!: () => void;
    const gate = new Promise<void>((r) => { release = r; });
    const holder = withLakeBuildLock(root, () => gate);
    await sleep(100);
    const waiters: Promise<void>[] = [];
    for (const name of ["a", "b", "c", "d", "e"]) {
      waiters.push(withLakeBuildLock(root, async () => { order.push(name); await sleep(30); }, name, quiet));
      await sleep(15); // distinct arrival times
    }
    await sleep(200);
    expect(order).toEqual([]);
    release();
    await Promise.all([holder, ...waiters]);
    expect(order).toEqual(["a", "b", "c", "d", "e"]);
    expect(await readdir(lakeLockQueueDir(path.join(root, ".lake-build.lock")))).toEqual([]);
  }, 20_000);

  it("a live ticket ahead holds a waiter back; a dead one (not refreshed, or its process gone) does not", async () => {
    const root = await tempRoot();
    const queue = lakeLockQueueDir(path.join(root, ".lake-build.lock"));
    await mkdir(queue, { recursive: true });
    const early = String(Date.now() - 60_000).padStart(15, "0");
    // another host's waiter, refreshed just now: first in line
    const other = path.join(queue, `${early}.otherhost.4242.00aa`);
    await writeFile(other, "{}\n");
    let ran = false;
    const w = withLakeBuildLock(root, async () => { ran = true; }, "w", quiet);
    expect(await pendingAfter(w, 400)).toBe(true);
    expect(ran).toBe(false);
    // it stops refreshing its ticket: expired, dropped
    const old = new Date(Date.now() - 10 * 60_000);
    await utimes(other, old, old);
    await w;
    expect(ran).toBe(true);
    await expect(stat(other)).rejects.toThrow();
    // a waiter of this host whose process is gone is dropped at once
    const dead = path.join(queue, `${early}.${LOCK_HOST}.${2 ** 22 + 7}.00bb`);
    await writeFile(dead, "{}\n");
    await withLakeBuildLock(root, async () => {}, "w2", quiet);
    await expect(stat(dead)).rejects.toThrow();
  }, 20_000);

  it("waits out a long hold by code that knows only the mutex, logging, and never throws", async () => {
    const root = await tempRoot();
    const lockPath = path.join(root, ".lake-build.lock");
    await writeFile(lockPath, "{}\n");
    // an older process: proper-lockfile only, no ticket, no holder record
    const releaseOld = await lockfile.lock(lockPath, { stale: 60 * 60_000, realpath: false });
    const lines: string[] = [];
    let ran = false;
    const w = withLakeBuildLock(root, async () => { ran = true; return 5; }, "long wait", (l) => lines.push(l));
    expect(await pendingAfter(w, 1_500)).toBe(true);
    expect(ran).toBe(false);
    expect(lines.length).toBeGreaterThanOrEqual(3);
    expect(lines[0]).toMatch(/\[lake-lock\] waiting for .*\(long wait\): first in line; the lock is held/);
    await releaseOld();
    expect(await w).toBe(5);
  }, 20_000);

  it("breaks a lock with our record once unrefreshed for 10 min (its holder's death alone frees nothing), older code's after an hour", async () => {
    const root = await tempRoot();
    const lockPath = path.join(root, ".lake-build.lock");
    await writeFile(lockPath, "{}\n");
    const mutex = `${lockPath}.lock`;
    const holderFile = path.join(root, ".lake", "paperformalizer", "lake-lock-holder.json");
    await mkdir(path.dirname(holderFile), { recursive: true });
    const age = async (min: number) => {
      const t = new Date(Date.now() - min * 60_000);
      await utimes(mutex, t, t);
    };
    const plant = async (host: string, pid: number, ageMin: number, record = true) => {
      await mkdir(mutex);
      const st = await stat(mutex, { bigint: true });
      if (record) await writeFile(holderFile, JSON.stringify({ ino: String(st.ino), token: "t", host, pid, what: "planted" }));
      else await rm(holderFile, { force: true });
      await age(ageMin);
    };
    // killed on this host a minute ago: its lake child may still be building — held
    await plant(LOCK_HOST, 2 ** 22 + 9, 1);
    const w0 = withLakeBuildLock(root, async () => {}, "after a dead holder", quiet);
    expect(await pendingAfter(w0, 400)).toBe(true);
    await age(11);
    await w0;
    // another host's holder, refreshed a minute ago: held; 11 minutes ago: stale
    await plant("otherhost", 4242, 1);
    const w = withLakeBuildLock(root, async () => {}, "w", quiet);
    expect(await pendingAfter(w, 400)).toBe(true);
    await age(11);
    await w;
    // older code's lock (no record), 20 minutes old: still held; 61: stale
    await plant("otherhost", 4242, 20, false);
    const w2 = withLakeBuildLock(root, async () => {}, "w2", quiet);
    expect(await pendingAfter(w2, 400)).toBe(true);
    await age(61);
    await w2;
  }, 20_000);

  it.skipIf(process.platform === "win32" || process.getuid?.() === 0)("never holds without its record: an unwritable record releases the mutex and tries again", async () => {
    const root = await tempRoot();
    const side = path.join(root, ".lake", "paperformalizer");
    await mkdir(path.join(side, "lake-lock-queue"), { recursive: true });
    await chmod(side, 0o555); // the record (and its temp file) cannot be written; the queue can
    const lines: string[] = [];
    let ran = false;
    const w = withLakeBuildLock(root, async () => { ran = true; }, "w", (l) => lines.push(l));
    const said = () => lines.some((l) => /holder record not written .* releasing and retrying/.test(l));
    for (let i = 0; i < 200 && !said(); i++) await sleep(50);
    expect(said()).toBe(true);
    expect(ran).toBe(false);
    // Not left held: each retry takes the mutex for a few ms (to find the record unwritable) and
    // lets it go, so it is seen only now and then — never a single look, which can land in a retry.
    let seen = 0;
    let looks = 0;
    for (const t0 = Date.now(); Date.now() - t0 < 1_000; looks++) {
      if (await stat(path.join(root, ".lake-build.lock.lock")).then(() => true, () => false)) seen++;
      await sleep(5);
    }
    expect(seen).toBeLessThan(looks / 2);
    expect(await pendingAfter(w, 0)).toBe(true);
    expect(ran).toBe(false);
    await chmod(side, 0o755);
    await w;
    expect(ran).toBe(true);
  }, 20_000);

  it("tells the holder when its hold is broken, through the handler it gives", async () => {
    LAKE_LOCK_TIMING.updateMs = 1_000;
    const root = await tempRoot();
    const lost: string[] = [];
    await withLakeBuildLock(root, async () => {
      // someone removes the mutex under the holder
      await rm(path.join(root, ".lake-build.lock.lock"), { recursive: true });
      for (let i = 0; i < 60 && lost.length === 0; i++) await sleep(100);
    }, "victim", quiet, (err) => lost.push(err.message)).catch(() => {});
    expect(lost.length).toBeGreaterThan(0);
  }, 20_000);

  it("a child process spawned inside a hold runs inside it; one outside it waits", async () => {
    const root = await tempRoot();
    const tools = path.resolve(import.meta.dirname, "..", "..");
    const script = `import { withLakeBuildLock } from ${JSON.stringify(path.join(tools, "src/shared/build_mutex.ts"))};
      await withLakeBuildLock(${JSON.stringify(root)}, async () => { console.log("child ran"); }, "child");`;
    const child = (env: NodeJS.ProcessEnv) => new Promise<string>((resolve, reject) => {
      execFile(process.execPath, ["--import", path.join(tools, "node_modules/tsx/dist/loader.mjs"), "--input-type=module", "-e", script],
        { env, cwd: tools }, (err, stdout) => (err ? reject(err) : resolve(stdout)));
    });
    const base = { ...process.env };
    delete base[LAKE_LOCK_HELD_ENV];
    let outside: Promise<string> = Promise.resolve("");
    await withLakeBuildLock(root, async () => {
      expect(lakeLockChildEnv()[LAKE_LOCK_HELD_ENV]).toBeTruthy();
      expect(await child({ ...base, ...lakeLockChildEnv() })).toContain("child ran");
      // without the token: behind this hold
      outside = child(base);
      expect(await pendingAfter(outside, 3_000)).toBe(true);
    });
    expect(lakeLockChildEnv()).toEqual({});
    // its turn once the hold ends (and it is done before the root is removed)
    expect(await outside).toContain("child ran");
  }, 30_000);

  it("records every hold, one line each, and summarizes wait and hold per day", async () => {
    const root = await tempRoot();
    process.env.PAPERFORMALIZER_RUN_SLUG = "toy_run";
    try {
      await withLakeBuildLock(root, async () => { await sleep(50); }, "compile gate: lake build 2 module(s)");
      await withLakeBuildLock(root, async () => {
        await withLakeBuildLock(root, async () => {}, "nested"); // not a hold of its own
      }, "F4 fingerprints: lake build");
      await withPromotionLock(root, async () => {});
    } finally {
      delete process.env.PAPERFORMALIZER_RUN_SLUG;
    }
    const holds = await readLockHolds(root);
    expect(holds.map((h) => [h.lock, h.what, h.slug, h.pid])).toEqual([
      ["lake", "compile gate: lake build 2 module(s)", "toy_run", process.pid],
      ["lake", "F4 fingerprints: lake build", "toy_run", process.pid],
      ["promote", "promotion", "toy_run", process.pid],
    ]);
    for (const h of holds) expect(Date.parse(h.asked) <= Date.parse(h.got) && Date.parse(h.got) <= Date.parse(h.released)).toBe(true);
    const [lake, promote] = summarizeLockHolds(holds);
    expect(lake).toMatchObject({ lock: "lake", holds: 2 });
    expect(lake!.top.map((t) => t.what).sort()).toEqual(["F4 fingerprints", "compile gate"]);
    expect(promote).toMatchObject({ lock: "promote", holds: 1 });
  }, 20_000);
});

// A model worker's process never takes the Lake lock itself: only the lake shim does, for it.
describe("withLakeBuildLock in a model worker's process", () => {
  const WORKER = "PAPERFORMALIZER_MODEL_WORKER";
  afterEach(() => { delete process.env[WORKER]; });

  it("refuses a direct call, with what to do instead; lets the shim's call and any other process's through", async () => {
    const root = await tempRoot();
    process.env[WORKER] = "1";
    let ran = false;
    await expect(withLakeBuildLock(root, async () => { ran = true; }, "serial-build.mjs", quiet))
      .rejects.toThrow(/serial-build\.mjs: refused — this is a model worker's process .*Run `lake` commands directly/);
    expect(ran).toBe(false);
    expect(existsSync(path.join(root, ".lake-build.lock.lock"))).toBe(false);
    expect(await withLakeBuildLock(root, async () => 1, "worker: lake build", quiet, undefined, { viaShim: true })).toBe(1);
    delete process.env[WORKER];
    expect(await withLakeBuildLock(root, async () => 2, "pipeline", quiet)).toBe(2);
  }, 20_000);
});

describe("withPromotionLock", () => {
  it("logs nothing for a short wait", async () => {
    const root = await tempRoot();
    const lines: string[] = [];
    expect(await withPromotionLock(root, async () => 7, undefined, (l) => lines.push(l))).toBe(7);
    expect(lines).toEqual([]);
  });
});

// Shared holds: builds of different papers' modules run side by side while the toolkit is clean
// and not in flux; anything else is exclusive and waits for them; inside a shared hold nothing
// else runs; the switch file keeps it all off until set; only an explicit call builds the toolkit.
describe("withLakeBuildLock: shared holds", () => {
  const clean = { ...LAKE_LOCK_CLEAN_BUILD };
  let builds: string[][] = [];
  let outcome: { ok: boolean; killed?: boolean; log: string } = { ok: true, log: "" };
  beforeEach(() => {
    builds = [];
    outcome = { ok: true, log: "" };
    LAKE_LOCK_CLEAN_BUILD.run = async (_root, targets) => { builds.push([...targets]); return outcome; };
  });
  afterEach(() => { Object.assign(LAKE_LOCK_CLEAN_BUILD, clean); });
  // a `lean` that answers `--version` (the signature names the toolchain; without one it is a doubt)
  const PATH = process.env.PATH;
  let leanBin = "";
  beforeAll(async () => {
    leanBin = await mkdtemp(path.join(os.tmpdir(), "lake-lock-lean-"));
    await writeFile(path.join(leanBin, "lean"), "#!/bin/sh\necho 'Lean (version 4.0.0, test)'\n");
    await chmod(path.join(leanBin, "lean"), 0o755);
    process.env.PATH = `${leanBin}:${PATH}`;
  });
  afterAll(async () => {
    process.env.PATH = PATH;
    await rm(leanBin, { recursive: true, force: true });
  });

  /** A toolkit with a barrel, a Staging module and papers Foo, Bar, Baz (imports Foo) and Stg (imports Staging). */
  const toolkit = async (on = true) => {
    const root = await tempRoot();
    const w = async (rel: string, text: string) => { await mkdir(path.dirname(path.join(root, rel)), { recursive: true }); await writeFile(path.join(root, rel), text); };
    await w("Toolkit.lean", "module\n-- import Toolkit.Staging.S (a comment)\npublic import Toolkit.A\n");
    await w("Toolkit/A.lean", "module\nimport Mathlib.Data.Nat\n");
    await w("Toolkit/Staging/S.lean", "module\n");
    await w("Papers/Foo/Main.lean", "module\npublic import Toolkit.A\n");
    await w("Papers/Bar/Main.lean", "module\nimport Toolkit.A\n");
    await w("Papers/Baz/Main.lean", "module\nimport«Papers».Foo.Main\n");
    await w("Papers/Stg/Main.lean", "module\nimport Toolkit.Staging.S\n");
    // studies' staging trees: Stu (its own and the toolkit's modules), Two (another study's), Three (a paper)
    await w("Toolkit/Staging/Stu/A.lean", "module\nimport Toolkit.A\nimport Toolkit.Staging.Stu.B\n");
    await w("Toolkit/Staging/Stu/B.lean", "module\n");
    await w("Toolkit/Staging/Two/A.lean", "module\nimport Toolkit.Staging.Stu.A\n");
    await w("Toolkit/Staging/Three/A.lean", "module\nimport Papers.Foo.Main\n");
    if (on) await w(".lake/paperformalizer/lake-shared-mode", "");
    return root;
  };
  const lockOf = (root: string) => path.join(root, ".lake-build.lock");
  /** The toolkit built clean, as a promotion's end does: inside an exclusive hold. */
  const settle = (root: string) => withLakeBuildLock(root, () => stampToolkitClean(root, quiet), "settle", quiet);
  const shared = (root: string, paper: string, body: () => Promise<void>, what = paper) =>
    withLakeBuildLock(root, body, what, quiet, undefined, { papers: [`Papers.${paper}`] });
  const gate = () => { let open!: () => void; const p = new Promise<void>((r) => { open = r; }); return { p, open }; };
  const holds = async (root: string) => (await readLockHolds(root)).map((h) => [h.what, h.mode, h.fallback ? "fallback" : ""]);
  const holdOf = async (root: string, what: string) => (await readLockHolds(root)).find((h) => h.what === what)!;

  it("switched off (no lake-shared-mode file): every request is exclusive, in turn, and nothing builds the toolkit", async () => {
    const root = await toolkit(false);
    expect(await settle(root)).toEqual({ clean: false, why: "shared mode is off" });
    const order: string[] = [];
    const g = gate();
    const a = shared(root, "Foo", async () => { order.push("Foo"); await g.p; order.push("Foo done"); });
    await sleep(200);
    const b = shared(root, "Bar", async () => { order.push("Bar"); });
    expect(await pendingAfter(b, 300)).toBe(true);
    g.open();
    await Promise.all([a, b]);
    expect(order).toEqual(["Foo", "Foo done", "Bar"]);
    expect(builds).toEqual([]);
    expect(existsSync(lakePaperLocksDir(lockOf(root)))).toBe(false);
    expect(await holds(root)).toEqual([["settle", "exclusive", ""], ["Foo", "exclusive", ""], ["Bar", "exclusive", ""]]);
  }, 20_000);

  it("no release builds the toolkit: shared requests run exclusive until it is stamped clean; then holds of different papers overlap", async () => {
    const root = await toolkit();
    await shared(root, "Foo", async () => {}, "first");
    await withLakeBuildLock(root, async () => {}, "an exclusive one", quiet);
    expect(builds).toEqual([]);
    expect(existsSync(lakeCleanStampFile(lockOf(root)))).toBe(false);
    // outside an exclusive hold, nothing is built
    expect(await stampToolkitClean(root, quiet)).toMatchObject({ clean: false, why: expect.stringMatching(/exclusive hold/) });
    expect(await settle(root)).toEqual({ clean: true });
    expect(builds).toEqual([["Toolkit"]]);
    expect(JSON.parse(await readFile(lakeCleanStampFile(lockOf(root)), "utf8"))).toMatchObject({ ok: true, targets: ["Toolkit"], libs: ["Toolkit"], modules: ["Toolkit", "Toolkit.A"] });
    expect(await settle(root)).toEqual({ clean: true }); // clean already: not built again
    expect(builds).toHaveLength(1);
    const order: string[] = [];
    const g = gate();
    const a = shared(root, "Foo", async () => { order.push("Foo"); await g.p; order.push("Foo done"); });
    await sleep(300);
    await shared(root, "Bar", async () => { order.push("Bar"); });
    g.open();
    await a;
    expect(order).toEqual(["Foo", "Bar", "Foo done"]);
    expect((await holds(root)).slice(-2)).toEqual([["Bar", "shared", ""], ["Foo", "shared", ""]]);
    expect((await holdOf(root, "first")).fallback).toMatch(/no clean build/);
    const day = summarizeLockHolds(await readLockHolds(root))[0]!;
    expect(day).toMatchObject({ shared: 2, fallbacks: 1, concurrent: { peak: 2 } });
  }, 20_000);

  it("a toolkit source changed since the stamp: shared requests run exclusive", async () => {
    const root = await toolkit();
    await settle(root);
    await sleep(20);
    await writeFile(path.join(root, "Toolkit", "A.lean"), "module\n-- changed\n");
    await shared(root, "Foo", async () => {}, "Foo");
    expect((await holdOf(root, "Foo")).fallback).toMatch(/changed since its last clean build/);
  }, 20_000);

  it("two shared requests of one paper do not overlap; a paper importing another locks both", async () => {
    const root = await toolkit();
    await settle(root);
    const order: string[] = [];
    const g = gate();
    const a = shared(root, "Baz", async () => { order.push("Baz"); await g.p; order.push("Baz done"); });
    await sleep(300);
    const foo = shared(root, "Foo", async () => { order.push("Foo"); });
    const baz = shared(root, "Baz", async () => { order.push("Baz 2"); });
    await shared(root, "Bar", async () => { order.push("Bar"); });
    expect(await pendingAfter(Promise.race([foo, baz]), 300)).toBe(true);
    expect(order).toEqual(["Baz", "Bar"]);
    g.open();
    await Promise.all([a, foo, baz]);
    expect(order.slice(0, 3)).toEqual(["Baz", "Bar", "Baz done"]);
    expect(order.slice(3).sort()).toEqual(["Baz 2", "Foo"]);
    expect((await holdOf(root, "Baz")).mode).toBe("shared");
  }, 20_000);

  it("an exclusive request waits for the shared holds that stand, and a shared one after it waits for it (arrival order)", async () => {
    const root = await toolkit();
    await settle(root);
    const order: string[] = [];
    const g = gate();
    const a = shared(root, "Foo", async () => { order.push("Foo"); await g.p; order.push("Foo done"); });
    await sleep(300);
    const ex = withLakeBuildLock(root, async () => { order.push("exclusive"); await sleep(200); order.push("exclusive done"); }, "exclusive", quiet);
    await sleep(300);
    const b = shared(root, "Bar", async () => { order.push("Bar"); });
    expect(await pendingAfter(Promise.race([ex, b]), 500)).toBe(true);
    expect(order).toEqual(["Foo"]);
    g.open();
    await Promise.all([a, ex, b]);
    expect(order).toEqual(["Foo", "Foo done", "exclusive", "exclusive done", "Bar"]);
  }, 20_000);

  /** A worker's build, as the shim asks for it (`pausable`: it stops when a writer waits). */
  const worker = (root: string, paper: string, body: () => Promise<void>, more: { pausable?: boolean; resumed?: boolean } = {}, log: (l: string) => void = quiet) =>
    withLakeBuildLock(root, body, `worker ${paper}`, log, undefined, { papers: [`Papers.${paper}`], viaShim: true, ...more });

  it("an exclusive holder draining past preemptGraceMs says so in its record once every hold it waits for is pausable; a pipeline's shared hold is not stopped", async () => {
    const root = await toolkit();
    await settle(root);
    LAKE_LOCK_TIMING.preemptGraceMs = 400;
    const order: string[] = [];
    const gFoo = gate();
    const gBar = gate();
    const foo = worker(root, "Foo", async () => { order.push("Foo"); await gFoo.p; order.push("Foo done"); }, { pausable: true });
    const bar = shared(root, "Bar", async () => { order.push("Bar"); await gBar.p; order.push("Bar done"); });
    await sleep(300);
    // the worker's record says it is pausable, the pipeline's does not
    const recs = await Promise.all((await readdir(lakeSharedDir(lockOf(root)))).map(async (n) => JSON.parse(await readFile(path.join(lakeSharedDir(lockOf(root)), n), "utf8"))));
    expect(Object.fromEntries(recs.map((r) => [r.what, r.pausable ?? false]))).toEqual({ "worker Foo": true, Bar: false });
    const ex = withLakeBuildLock(root, async () => { order.push("writer"); }, "writer", quiet);
    await sleep(150);
    expect(await lakeWriterWaiting(root)).toBeNull(); // within the grace
    await sleep(600);
    // past it, but a pipeline's hold (Bar) still stands: no build is paused for nothing
    expect(await lakeWriterWaiting(root)).toBeNull();
    gBar.open();
    await bar;
    await sleep(200);
    expect(await lakeWriterWaiting(root)).toBe("writer");
    expect(await pendingAfter(ex, 200)).toBe(true);
    const t0 = Date.now();
    gFoo.open();
    await Promise.all([foo, ex]);
    expect(Date.now() - t0).toBeLessThan(1_000);
    expect(order.slice(-3)).toEqual(["Bar done", "Foo done", "writer"]);
    expect(await lakeWriterWaiting(root)).toBeNull();
    // a writer that finds no shared hold standing, however long it holds the lock, marks nothing
    await withLakeBuildLock(root, async () => { await sleep(600); expect(await lakeWriterWaiting(root)).toBeNull(); }, "alone", quiet);
  }, 20_000);

  /** A shared record of `token` listed, refreshed `ageMin` minutes ago, its process gone. */
  const plant = async (root: string, token: string, ageMin: number) => {
    const f = path.join(lakeSharedDir(lockOf(root)), `${token}.json`);
    await mkdir(path.dirname(f), { recursive: true });
    await writeFile(f, JSON.stringify({ token, host: LOCK_HOST, pid: 2 ** 22 + 11, what: "planted", got: new Date().toISOString(), papers: ["Papers.Foo"] }));
    await writeFile(path.join(root, ".lake", "paperformalizer", "lake-shared.json"), JSON.stringify({ tokens: [token] }));
    const t = new Date(Date.now() - ageMin * 60_000);
    await utimes(f, t, t);
    return f;
  };
  const age = async (f: string, min: number) => { const t = new Date(Date.now() - min * 60_000); await utimes(f, t, t); };

  it("a shared record unrefreshed for 10 min is dead; a fresh one whose process is gone still holds (its lake may build on)", async () => {
    const root = await toolkit();
    const old = await plant(root, "a".repeat(24), 11);
    await withLakeBuildLock(root, async () => {}, "after a dead one", quiet);
    expect(existsSync(old)).toBe(false);
    const fresh = await plant(root, "b".repeat(24), 1);
    const w = withLakeBuildLock(root, async () => {}, "behind a fresh one", quiet);
    expect(await pendingAfter(w, 500)).toBe(true);
    await age(fresh, 11);
    await w;
  }, 20_000);

  it.skipIf(process.platform === "win32" || process.getuid?.() === 0)("a listed record that cannot be read (not gone, not stale) still holds", async () => {
    const root = await toolkit();
    const f = await plant(root, "c".repeat(24), 11);
    // unreadable: its age cannot be read either
    await chmod(path.dirname(f), 0o311);
    await chmod(f, 0o000);
    const w = withLakeBuildLock(root, async () => {}, "behind an unreadable one", quiet);
    expect(await pendingAfter(w, 600)).toBe(true);
    await chmod(f, 0o644);
    await chmod(path.dirname(f), 0o755);
    await w;
  }, 20_000);

  it("a build that fails is stamped failed (and tried again by the next explicit call); one killed stamps nothing", async () => {
    const root = await toolkit();
    outcome = { ok: false, log: "error: boom" };
    expect(await settle(root)).toMatchObject({ clean: false });
    expect(JSON.parse(await readFile(lakeCleanStampFile(lockOf(root)), "utf8"))).toMatchObject({ ok: false, why: expect.stringMatching(/boom/) });
    await shared(root, "Foo", async () => {}, "Foo");
    expect(await holdOf(root, "Foo")).toMatchObject({ mode: "exclusive", fallback: expect.stringMatching(/clean build failed/) });
    // killed (a timeout): nothing stamped, the failed stamp stands
    outcome = { ok: false, killed: true, log: "killed" };
    const before = await readFile(lakeCleanStampFile(lockOf(root)), "utf8");
    expect(await settle(root)).toMatchObject({ clean: false, why: expect.stringMatching(/stopped/) });
    expect(await readFile(lakeCleanStampFile(lockOf(root)), "utf8")).toBe(before);
    await rm(lakeCleanStampFile(lockOf(root)));
    expect(await settle(root)).toMatchObject({ clean: false });
    expect(existsSync(lakeCleanStampFile(lockOf(root)))).toBe(false);
    outcome = { ok: true, log: "" };
    expect(await settle(root)).toEqual({ clean: true });
    expect(builds).toHaveLength(4);
  }, 20_000);

  it("a paper importing a Staging module (outside the clean build) runs exclusive", async () => {
    const root = await toolkit();
    await settle(root);
    await shared(root, "Stg", async () => {}, "Stg");
    expect(await holdOf(root, "Stg")).toMatchObject({ mode: "exclusive", fallback: expect.stringMatching(/Toolkit\.Staging\.S/) });
  }, 20_000);

  it("a paper lock that cannot be taken (not merely held) runs the request exclusive", async () => {
    const root = await toolkit();
    await settle(root);
    await writeFile(lakePaperLocksDir(lockOf(root)), "not a directory\n");
    const lines: string[] = [];
    let ran = false;
    await withLakeBuildLock(root, async () => { ran = true; }, "Foo", (l) => lines.push(l), undefined, { papers: ["Papers.Foo"] });
    expect(ran).toBe(true);
    expect(await holdOf(root, "Foo")).toMatchObject({ mode: "exclusive", fallback: expect.stringMatching(/paper lock/) });
    expect(lines.join("\n")).toMatch(/a paper lock could not be taken .* running exclusive/);
  }, 20_000);

  it("a journal on file (kept for repair, or left by a crash) is no flux; the marker is — it admits no shared hold and is not stamped", async () => {
    const root = await toolkit();
    await settle(root);
    for (const rel of ["runs/paper_x/proposals/move_journal.json", "runs/paper_x/proposals/move_batch_journal.json", "runs/study_y/coordinate_journal.json"]) {
      const f = path.join(root, rel);
      await mkdir(path.dirname(f), { recursive: true });
      await writeFile(f, "{}\n");
      await shared(root, "Foo", async () => {}, rel);
      expect((await holdOf(root, rel)).mode).toBe("shared");
      expect(await settle(root)).toMatchObject({ clean: true });
      await rm(f);
    }
    await shared(root, "Foo", async () => {}, "no journal");
    expect((await holdOf(root, "no journal")).mode).toBe("shared");
    // the marker
    await writeFile(lakeFluxFile(lockOf(root)), "{}\n");
    await shared(root, "Foo", async () => {}, "marked");
    expect(await holdOf(root, "marked")).toMatchObject({ mode: "exclusive", fallback: expect.stringMatching(/in flux/) });
    expect(await settle(root)).toMatchObject({ clean: false, why: expect.stringMatching(/in flux/) });
  }, 20_000);

  it("a worker's build (the shim's) while a flux session is open waits for it to end, never running exclusive; off gets the lock past it", async () => {
    const root = await toolkit();
    await settle(root);
    const id = await toolkitFluxOn(root, "hand edit", quiet);
    let ran = false;
    const worker = withLakeBuildLock(root, async () => { ran = true; }, "worker: lake build Papers.Foo.A", quiet, undefined, { papers: ["Papers.Foo"], viaShim: true });
    expect(await pendingAfter(worker, 500)).toBe(true);
    expect(ran).toBe(false);
    // closing the session is not stuck behind the worker
    expect(await toolkitFluxOff(root, id, quiet)).toMatchObject({ closed: id, remaining: [] });
    await worker;
    expect(ran).toBe(true);
    expect((await holdOf(root, "worker: lake build Papers.Foo.A")).mode).toBe("shared");
    // a pipeline's own request in flux is exclusive, as before: it does not hold off
    const id2 = await toolkitFluxOn(root, "hand edit 2", quiet);
    await shared(root, "Foo", async () => {}, "pipeline in flux");
    expect(await holdOf(root, "pipeline in flux")).toMatchObject({ mode: "exclusive", fallback: expect.stringMatching(/in flux/) });
    await toolkitFluxOff(root, id2, quiet);
  }, 30_000);

  it("a worker's build holding off takes no paper lock nor the mutex, and after fluxWaitMaxMs runs exclusive, saying so", async () => {
    const root = await toolkit();
    await settle(root);
    LAKE_LOCK_TIMING.fluxWaitMaxMs = 1_000;
    await toolkitFluxOn(root, "orphaned", quiet); // never closed
    const lines: string[] = [];
    const t0 = Date.now();
    const w = worker(root, "Foo", async () => {}, {}, (l) => lines.push(l));
    await sleep(400);
    expect(existsSync(path.join(lakePaperLocksDir(lockOf(root)), "Papers.Foo.lock"))).toBe(false);
    expect(existsSync(`${lockOf(root)}.lock`)).toBe(false);
    await w;
    expect(Date.now() - t0).toBeGreaterThanOrEqual(1_000);
    expect(await holdOf(root, "worker Foo")).toMatchObject({ mode: "exclusive", fallback: expect.stringMatching(/in flux/) });
    expect(lines.filter((l) => /holding off before building/.test(l)).length).toBeGreaterThan(0);
    expect(lines.filter((l) => /running exclusive/.test(l))).toHaveLength(1);
    expect(lines.some((l) => /\bwaiting\b/.test(l))).toBe(false);
  }, 20_000);

  it("a worker's build does not hold off for a toolkit not clean (a failed stamp); a paused build's re-run does, a writer getting in meanwhile, until it is clean", async () => {
    const root = await toolkit();
    outcome = { ok: false, log: "error: boom" };
    await settle(root);
    const t0 = Date.now();
    await worker(root, "Foo", async () => {});
    expect(Date.now() - t0).toBeLessThan(2_000);
    expect(await holdOf(root, "worker Foo")).toMatchObject({ mode: "exclusive", fallback: expect.stringMatching(/clean build failed/) });
    let ran = false;
    const rerun = worker(root, "Bar", async () => { ran = true; }, { resumed: true, pausable: true });
    expect(await pendingAfter(rerun, 500)).toBe(true);
    await withLakeBuildLock(root, async () => {}, "another writer", quiet);
    expect(ran).toBe(false);
    outcome = { ok: true, log: "" };
    expect(await settle(root)).toEqual({ clean: true });
    await rerun;
    expect(ran).toBe(true);
    expect(await holdOf(root, "worker Bar")).toMatchObject({ mode: "shared" });
  }, 30_000);

  it("toolkit-flux on waits for the shared holds and opens a session; the marker stays while any is open; the last off builds clean", async () => {
    const root = await toolkit();
    await settle(root);
    const marker = lakeFluxFile(lockOf(root));
    const g = gate();
    const a = shared(root, "Foo", async () => { await g.p; });
    await sleep(300);
    const on = toolkitFluxOn(root, "test", quiet);
    expect(await pendingAfter(on, 400)).toBe(true);
    expect(existsSync(marker)).toBe(false);
    g.open();
    const [, first] = await Promise.all([a, on]);
    const second = await toolkitFluxOn(root, "test 2", quiet);
    expect(first).not.toBe(second);
    expect((await readdir(lakeFluxSessionsDir(lockOf(root)))).sort()).toEqual([first, second].sort());
    expect(JSON.parse(await readFile(marker, "utf8"))).toEqual({ sessions: [first, second].sort() });
    expect(JSON.parse(await readFile(lakeCleanStampFile(lockOf(root)), "utf8"))).toMatchObject({ ok: false });
    await shared(root, "Foo", async () => {}, "in flux");
    expect((await holdOf(root, "in flux")).mode).toBe("exclusive");
    // two open: an off without an id is refused; one closed leaves the other, the marker and no stamp
    await expect(toolkitFluxOff(root, null, quiet)).rejects.toThrow(/2 flux sessions are open/);
    await expect(toolkitFluxOff(root, "zz-000000", quiet)).rejects.toThrow(/no flux session zz-000000/);
    expect(await toolkitFluxOff(root, first, quiet)).toEqual({ closed: first, remaining: [second], clean: null });
    expect(existsSync(marker)).toBe(true);
    expect(builds).toHaveLength(1);
    await shared(root, "Foo", async () => {}, "still in flux");
    expect((await holdOf(root, "still in flux")).mode).toBe("exclusive");
    // the last one (the only one: no id needed)
    expect(await toolkitFluxOff(root, null, quiet)).toEqual({ closed: second, remaining: [], clean: { clean: true } });
    expect(existsSync(marker)).toBe(false);
    expect(builds).toHaveLength(2);
    await shared(root, "Foo", async () => {}, "after");
    expect((await holdOf(root, "after")).mode).toBe("shared");
    // a session's file alone (its marker lost) is flux too
    const id = await toolkitFluxOn(root, "test 3", quiet);
    await rm(marker);
    await shared(root, "Foo", async () => {}, "file alone");
    expect(await holdOf(root, "file alone")).toMatchObject({ mode: "exclusive", fallback: expect.stringContaining(id) });
    expect(await toolkitFluxOff(root, id, quiet)).toMatchObject({ remaining: [], clean: { clean: true } });
  }, 30_000);

  it("older code's marker (no session list) is one session, closed by a plain off; one opened beside it keeps it", async () => {
    const root = await toolkit();
    const marker = lakeFluxFile(lockOf(root));
    await mkdir(path.dirname(marker), { recursive: true });
    await writeFile(marker, JSON.stringify({ host: "h", pid: 1, at: "x" }));
    const id = await toolkitFluxOn(root, "beside", quiet);
    expect(JSON.parse(await readFile(marker, "utf8"))).toEqual({ sessions: [id, "legacy"].sort() });
    expect(await toolkitFluxOff(root, id, quiet)).toMatchObject({ remaining: ["legacy"], clean: null });
    expect(await toolkitFluxOff(root, null, quiet)).toMatchObject({ closed: "legacy", remaining: [], clean: { clean: true } });
    expect(existsSync(marker)).toBe(false);
  }, 20_000);

  it("withToolkitFlux holds a session across its work, and closes it when the work throws", async () => {
    const root = await toolkit();
    await settle(root);
    await withToolkitFlux(root, "docstrings", async () => {
      expect(existsSync(lakeFluxFile(lockOf(root)))).toBe(true);
      await shared(root, "Foo", async () => {}, "during");
    }, quiet);
    expect((await holdOf(root, "during")).mode).toBe("exclusive");
    expect(existsSync(lakeFluxFile(lockOf(root)))).toBe(false);
    await expect(withToolkitFlux(root, "docstrings", async () => { throw new Error("pass failed"); }, quiet)).rejects.toThrow(/pass failed/);
    expect(existsSync(lakeFluxFile(lockOf(root)))).toBe(false);
    expect(await readdir(lakeFluxSessionsDir(lockOf(root)))).toEqual([]);
    await shared(root, "Foo", async () => {}, "after");
    expect((await holdOf(root, "after")).mode).toBe("shared");
  }, 30_000);

  it("a list of shared holds that does not parse is rebuilt from their records, never waited on — switched off too", async () => {
    for (const on of [false, true]) {
      const root = await toolkit(on);
      const index = path.join(root, ".lake", "paperformalizer", "lake-shared.json");
      await mkdir(path.dirname(index), { recursive: true });
      // garbage: no record at all — the exclusive request goes on at once
      await writeFile(index, "{ not json");
      const lines: string[] = [];
      await withLakeBuildLock(root, async () => {}, "after garbage", (l) => lines.push(l));
      expect(lines.join("\n")).toMatch(/does not parse as a list of shared holds: rebuilt from their records \(0\)/);
      expect(JSON.parse(await readFile(index, "utf8"))).toEqual({ tokens: [] });
      // ill-shaped, with a live record on disk: found, and waited for until it is stale
      const f = await plant(root, "d".repeat(24), 1);
      await writeFile(index, JSON.stringify({ tokens: "nope" }));
      const w = withLakeBuildLock(root, async () => {}, "behind a found one", quiet);
      expect(await pendingAfter(w, 500)).toBe(true);
      expect(JSON.parse(await readFile(index, "utf8"))).toEqual({ tokens: ["d".repeat(24)] });
      await age(f, 11);
      await w;
    }
  }, 30_000);

  it.skipIf(process.platform === "win32")("the toolchain is read before a request queues, not while it holds the mutex", async () => {
    const root = await toolkit();
    // a `lean` that says when it was asked
    const bin = path.join(root, "bin");
    await mkdir(bin);
    const asked = path.join(root, "lean-asked");
    await writeFile(path.join(bin, "lean"), `#!/bin/sh\necho asked >> ${JSON.stringify(asked)}\necho "Lean (version 4.0.0, test)"\n`);
    await chmod(path.join(bin, "lean"), 0o755);
    const PATH = process.env.PATH;
    process.env.PATH = `${bin}:${PATH}`;
    try {
      // the mutex held (by code that knows only the mutex: it reads no toolchain)
      await writeFile(lockOf(root), "{}\n");
      const releaseOld = await lockfile.lock(lockOf(root), { stale: 60 * 60_000, realpath: false });
      const w = shared(root, "Foo", async () => {}, "queued");
      for (let i = 0; i < 100 && !existsSync(asked); i++) await sleep(20);
      expect(await pendingAfter(w, 0)).toBe(true);
      expect(existsSync(asked)).toBe(true);
      await releaseOld();
      await w;
      expect((await readFile(asked, "utf8")).trim().split("\n")).toHaveLength(1);
    } finally {
      process.env.PATH = PATH;
    }
  }, 20_000);

  /** A ticket in the queue from a live waiter on another host, asked `ageMs` ago (or a promotion's). */
  /** `headForMs`: this code's ticket that has lost the mutex for that long; null: this code's that has
   *  lost nothing; absent: older code's (no `headSince` key). */
  const ticket = async (root: string, ageMs: number | "promotion", headForMs?: number | null, id = "00aa") => {
    const queue = lakeLockQueueDir(lockOf(root));
    await mkdir(queue, { recursive: true });
    const stamp = ageMs === "promotion" ? "0".repeat(15) : String(Date.now() - ageMs).padStart(15, "0");
    const f = path.join(queue, `${stamp}.otherhost.4242.${id}`);
    await writeFile(f, `${JSON.stringify(headForMs === undefined ? {} : { headSince: headForMs === null ? null : Date.now() - headForMs })}\n`);
    return f;
  };

  it("a shared request passes the queue while no ticket there has waited long", async () => {
    const root = await toolkit();
    await settle(root);
    // another host's exclusive request, just queued (its waiter is alive: the queue holds behind it)
    const young = await ticket(root, 0);
    const ex = withLakeBuildLock(root, async () => {}, "exclusive behind it", quiet);
    let ran = false;
    await shared(root, "Foo", async () => { ran = true; }, "passes");
    expect(ran).toBe(true);
    expect((await holdOf(root, "passes")).mode).toBe("shared");
    expect(await pendingAfter(ex, 200)).toBe(true);
    await rm(young);
    await ex;
  }, 20_000);

  it("a ticket first in line trying the mutex longer than sharedYieldMs, or a promotion's, makes new shared requests queue behind it", async () => {
    const root = await toolkit();
    await settle(root);
    LAKE_LOCK_TIMING.sharedYieldMs = 300;
    for (const age of [1_000, "promotion"] as const) {
      const old = await ticket(root, age, age === "promotion" ? undefined : 1_000);
      let ran = false;
      const s1 = shared(root, "Foo", async () => { ran = true; }, `behind ${age}`);
      expect(await pendingAfter(s1, 500)).toBe(true);
      expect(ran).toBe(false);
      await rm(old);
      await s1;
      expect((await holdOf(root, `behind ${age}`)).mode).toBe("shared");
    }
  }, 20_000);

  it("a line of exclusive requests that waited long, none of them losing the mutex, does not hold a shared request back", async () => {
    const root = await toolkit();
    await settle(root);
    LAKE_LOCK_TIMING.sharedYieldMs = 300;
    // this code's tickets, waited a minute each, none of them losing the mutex (headSince null)
    const olds = [await ticket(root, 60_000, null, "00aa"), await ticket(root, 50_000, null, "00ab"), await ticket(root, 40_000, null, "00ac")];
    let ran = false;
    await sleep(400); // past sharedYieldMs: only a head that lost the mutex would make it wait
    await shared(root, "Foo", async () => { ran = true; }, "past the line");
    expect(ran).toBe(true);
    expect((await holdOf(root, "past the line")).mode).toBe("shared");
    for (const f of olds) await rm(f);
  }, 20_000);

  /** The mutex held as by another host's holder with our record, `token` (rewriting it with another token: a later hold took it). */
  const holdMutex = async (root: string) => {
    const release = await lockfile.lock(lockOf(root), { stale: 60 * 60_000, realpath: false });
    const file = path.join(root, ".lake", "paperformalizer", "lake-lock-holder.json");
    const as = async (token: string) => writeFile(file, `${JSON.stringify({ ino: String((await stat(`${lockOf(root)}.lock`, { bigint: true })).ino), token, host: "otherhost", pid: 4242 })}\n`);
    return { as, release: async () => { await rm(file, { force: true }); await release(); } };
  };
  const ticketsOf = async (root: string) => {
    const queue = lakeLockQueueDir(lockOf(root));
    return Promise.all((await readdir(queue)).filter((n) => !n.includes("otherhost")).map(async (n) => JSON.parse(await readFile(path.join(queue, n), "utf8")) as { headSince?: number | null }));
  };

  it("no writer starves: once the request first in line has lost the mutex to later holds for sharedYieldMs, shared requests let it go first", async () => {
    const root = await toolkit();
    await settle(root);
    LAKE_LOCK_TIMING.sharedYieldMs = 300;
    const m = await holdMutex(root);
    await m.as("a".repeat(24));
    const order: string[] = [];
    const ex = withLakeBuildLock(root, async () => { order.push("exclusive"); }, "exclusive", quiet);
    await sleep(200);
    await m.as("b".repeat(24)); // a later hold took the mutex before it
    await sleep(600);
    expect((await ticketsOf(root)).map((b) => typeof b.headSince)).toEqual(["number"]);
    const s1 = shared(root, "Foo", async () => { order.push("shared"); });
    await sleep(200);
    await m.release();
    await Promise.all([ex, s1]);
    expect(order).toEqual(["exclusive", "shared"]);
  }, 20_000);

  it("a request first in line behind one long hold has lost nothing: shared requests do not wait for it, nor queue behind the line", async () => {
    const root = await toolkit();
    await settle(root);
    LAKE_LOCK_TIMING.sharedYieldMs = 300;
    const m = await holdMutex(root);
    await m.as("a".repeat(24));
    const ex = withLakeBuildLock(root, async () => {}, "exclusive", quiet);
    await sleep(100);
    const behind = await ticket(root, 0); // another host's exclusive request, after it, that will not move
    await sleep(600);
    expect((await ticketsOf(root)).map((b) => b.headSince)).toEqual([null]);
    let ran = false;
    const s1 = shared(root, "Foo", async () => { ran = true; }, "past the line");
    await sleep(200);
    await m.release();
    expect(await pendingAfter(s1, 3_000)).toBe(false);
    expect(ran).toBe(true);
    expect((await holdOf(root, "past the line")).mode).toBe("shared");
    await rm(behind);
    await ex;
  }, 20_000);

  it("a study's own staging build is a shared hold, beside papers'; one study at a time; another study's staging or a paper imported is exclusive", async () => {
    const root = await toolkit();
    await settle(root);
    const study = (name: string, body: () => Promise<void>, what = name) =>
      withLakeBuildLock(root, body, what, quiet, undefined, { papers: [`Toolkit.Staging.${name}`] });
    const order: string[] = [];
    const g = gate();
    const a = study("Stu", async () => { order.push("Stu"); await g.p; order.push("Stu done"); });
    await sleep(300);
    await shared(root, "Foo", async () => { order.push("Foo"); });
    const again = study("Stu", async () => { order.push("Stu 2"); });
    expect(await pendingAfter(again, 300)).toBe(true);
    expect(order).toEqual(["Stu", "Foo"]);
    g.open();
    await Promise.all([a, again]);
    expect(order).toEqual(["Stu", "Foo", "Stu done", "Stu 2"]);
    expect((await holdOf(root, "Stu")).mode).toBe("shared");
    await study("Two", async () => {});
    expect(await holdOf(root, "Two")).toMatchObject({ mode: "exclusive", fallback: expect.stringMatching(/imports Toolkit\.Staging\.Stu\.A/) });
    await study("Three", async () => {});
    expect(await holdOf(root, "Three")).toMatchObject({ mode: "exclusive", fallback: expect.stringMatching(/imports Papers\.Foo\.Main/) });
    // the staging root itself is no study
    await withLakeBuildLock(root, async () => {}, "staging root", quiet, undefined, { papers: ["Toolkit.Staging"] });
    expect(await holdOf(root, "staging root")).toMatchObject({ mode: "exclusive", fallback: expect.stringMatching(/no paper or study/) });
  }, 30_000);

  it("a scanner's turns run under a shared hold when shared mode is on, the toolkit clean and the exe up to date; else exclusive", async () => {
    const root = await toolkit();
    await settle(root);
    const seen: string[] = [];
    let fresh = true;
    let wouldBuild = false;
    const run = () => withScannerHold<string>(root, ["Papers.Foo"], "scan", {
      exeFresh: async () => { seen.push(`check ${lakeHoldMode(root)}`); return fresh; },
      shared: async () => { seen.push(`shared ${lakeHoldMode(root)}`); return wouldBuild ? WOULD_BUILD : "s"; },
      exclusive: async () => {
        seen.push(`exclusive ${lakeHoldMode(root)}`);
        return withLakeBuildLock(root, async () => { seen.push(`exclusive turn ${lakeHoldMode(root)}`); return "e"; }, "scan exclusive", quiet);
      },
    }, quiet);
    expect(await run()).toBe("s");
    expect(seen.splice(0)).toEqual(["check null", "shared shared"]);
    fresh = false;
    expect(await run()).toBe("e");
    expect(seen.splice(0)).toEqual(["check null", "exclusive null", "exclusive turn exclusive"]);
    fresh = true;
    wouldBuild = true;
    expect(await run()).toBe("e");
    expect(seen.splice(0)).toEqual(["check null", "shared shared", "exclusive null", "exclusive turn exclusive"]);
    wouldBuild = false;
    // the toolkit changed: the hold granted is exclusive, the turns as before inside it
    await sleep(20);
    await writeFile(path.join(root, "Toolkit", "A.lean"), "module\n-- changed\n");
    expect(await run()).toBe("e");
    expect(seen.splice(0)).toEqual(["check null", "exclusive exclusive", "exclusive turn exclusive"]);
    // inside a hold already: no check, the turns as before
    await withLakeBuildLock(root, async () => { expect(await run()).toBe("e"); }, "outer", quiet);
    expect(seen.splice(0)).toEqual(["exclusive exclusive", "exclusive turn exclusive"]);
    // shared mode off: no check
    await rm(path.join(root, ".lake", "paperformalizer", "lake-shared-mode"));
    expect(await run()).toBe("e");
    expect(seen.splice(0)).toEqual(["exclusive null", "exclusive turn exclusive"]);
  }, 30_000);

  it("a scan of the toolkit alone runs under a shared hold of no paper, beside a paper's shared build; the whole library's scan is exclusive", async () => {
    const root = await toolkit();
    await settle(root);
    const g = gate();
    const order: string[] = [];
    const paper = shared(root, "Foo", async () => { order.push("Foo"); await g.p; order.push("Foo done"); }, "paper build");
    await sleep(300);
    const turns = (tag: string) => ({
      exeFresh: async () => true,
      shared: async () => { order.push(`${tag} shared ${lakeHoldMode(root)}`); return tag; },
      exclusive: async () => withLakeBuildLock(root, async () => { order.push(`${tag} exclusive ${lakeHoldMode(root)}`); return tag; }, `${tag} exclusive`, quiet),
    });
    // the toolkit alone: runs while the paper's build still holds
    expect(await withScannerHold<string>(root, [], "toolkit scan", turns("toolkit"), quiet)).toBe("toolkit");
    expect(order).toEqual(["Foo", "toolkit shared shared"]);
    expect((await holdOf(root, "toolkit scan (shared)")).mode).toBe("shared");
    // the whole library: exclusive, after the paper's build
    const whole = withScannerHold<string>(root, null, "library scan", turns("library"), quiet);
    expect(await pendingAfter(whole, 300)).toBe(true);
    g.open();
    await Promise.all([paper, whole]);
    expect(order).toEqual(["Foo", "toolkit shared shared", "Foo done", "library exclusive exclusive"]);
  }, 30_000);

  it("inside a shared hold, a request of its papers runs; an exclusive one or another paper's is refused, nested or in a child", async () => {
    const root = await toolkit();
    await settle(root);
    const tools = path.resolve(import.meta.dirname, "..", "..");
    const script = `import { withLakeBuildLock } from ${JSON.stringify(path.join(tools, "src/shared/build_mutex.ts"))};
      const papers = process.env.CHILD_PAPERS ? { papers: process.env.CHILD_PAPERS.split(",") } : {};
      await withLakeBuildLock(${JSON.stringify(root)}, async () => { console.log("child ran"); }, "child", undefined, undefined, papers);`;
    const child = (env: NodeJS.ProcessEnv) => new Promise<{ code: number; out: string; err: string }>((resolve) => {
      execFile(process.execPath, ["--import", path.join(tools, "node_modules/tsx/dist/loader.mjs"), "--input-type=module", "-e", script],
        { env, cwd: tools }, (e, out, err) => resolve({ code: e ? (typeof e.code === "number" ? e.code : 1) : 0, out, err }));
    });
    const base = { ...process.env };
    delete base[LAKE_LOCK_HELD_ENV];
    delete base.CHILD_PAPERS;
    await withLakeBuildLock(root, async () => {
      // nested in this chain
      let ran = false;
      await withLakeBuildLock(root, async () => { ran = true; }, "nested Foo", quiet, undefined, { papers: ["Papers.Foo"] });
      expect(ran).toBe(true);
      await expect(withLakeBuildLock(root, async () => {}, "nested exclusive", quiet)).rejects.toThrow(/refused .* shared hold of Papers\.Foo/);
      await expect(withLakeBuildLock(root, async () => {}, "nested Bar", quiet, undefined, { papers: ["Papers.Bar"] })).rejects.toThrow(/not Papers\.Bar/);
      // a child with the hold's token
      const inside = await child({ ...base, ...lakeLockChildEnv(), CHILD_PAPERS: "Papers.Foo" });
      expect(inside.out).toContain("child ran");
      const refused = await child({ ...base, ...lakeLockChildEnv() });
      expect(refused.code).not.toBe(0);
      expect(refused.out).not.toContain("child ran");
      expect(refused.err).toMatch(/refused/);
      // without the token: an exclusive request, behind this shared hold
      expect(await pendingAfter(child(base), 3_000)).toBe(true);
    }, "Foo", quiet, undefined, { papers: ["Papers.Foo"] });
    expect((await holdOf(root, "Foo")).mode).toBe("shared");
  }, 30_000);
});
