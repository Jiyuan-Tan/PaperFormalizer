// The workers' `lake` shim: a command that writes build output runs the real lake under the
// toolkit's Lake build lock (queued with the pipeline's builds, recorded as a hold); `serve`, a
// plain `env`, `--version` and anything outside a Lake project pass straight through. The real
// lake's exit status comes back unchanged. A build of one paper's modules only asks for a shared hold.
import { execFile, spawn } from "node:child_process";
import { existsSync } from "node:fs";
import { chmod, mkdir, mkdtemp, readFile, rename, rm, symlink, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import {
  LAKE_LOCK_TIMING, LAKE_SHIM_DIR, lakeHoldMode, lakeLockChildEnv, lakePaperLocksDir, lakeWriterWaiting, stampToolkitClean, toolkitFluxOff, toolkitFluxOn, withLakeBuildLock,
} from "../../src/shared/build_mutex.js";
import { readLockHolds } from "../../src/shared/lock_holds.js";

let dir: string;
let project: string;
let log: string;
beforeAll(async () => {
  dir = await mkdtemp(path.join(os.tmpdir(), "lake-shim-"));
  project = path.join(dir, "toolkit");
  await mkdir(project);
  await writeFile(path.join(project, "lakefile.toml"), 'name = "t"\n');
  log = path.join(dir, "calls.log");
  // the "real" lake: says what it was asked and whether the build lock was held, exits 3 on `fail`
  await mkdir(path.join(dir, "bin"));
  const fake = path.join(dir, "bin", "lake");
  await writeFile(fake, `#!/usr/bin/env bash\n[[ "$1" == env && "$2" == bash ]] && { shift; exec "$@"; }\nroot="$PWD"; for ((i=1;i<=$#;i++)); do [[ "\${!i}" == -d ]] && { j=$((i+1)); root="\${!j}"; }; done\n` +
    `if [[ -d "$root/.lake-build.lock.lock" ]]; then l=locked; elif compgen -G "$root/.lake/paperformalizer/paper-locks/*.lock" > /dev/null; then l=shared; else l=free; fi\necho "$l $*" >> ${JSON.stringify(log)}\n[[ "$*" == *fail* ]] && exit 3\n[[ "$*" == *blip* ]] && sleep 2\n[[ "$*" == *orphan* ]] && { echo $$ > ${JSON.stringify(path.join(dir, "lake.pid"))}; sleep 60 & echo $! > ${JSON.stringify(path.join(dir, "orphan.pid"))}; wait; }\n[[ "$*" == *slow* ]] && { sleep 60 & echo $! > ${JSON.stringify(path.join(dir, "grandchild.pid"))}; wait; }\n` +
    // a build that runs (with a `lean` child) until `<target>.go` exists; each run logs its pid in `<target>.runs`
    `[[ "$*" == *Pausable* ]] && { d=${JSON.stringify(dir)}; t="\${@: -1}"; echo $$ >> "$d/$t.runs"; sleep 300 & echo $! > "$d/$t.child"; while [[ ! -f "$d/$t.go" ]]; do sleep 0.1; done; kill $! 2>/dev/null; }\nexit 0\n`);
  await chmod(fake, 0o755);
  // and a `lean` that answers `--version` (the toolkit's signature names the toolchain)
  await writeFile(path.join(dir, "bin", "lean"), "#!/bin/sh\necho 'Lean (version 4.0.0, test)'\n");
  await chmod(path.join(dir, "bin", "lean"), 0o755);
});
afterAll(async () => { await rm(dir, { recursive: true, force: true }); });

const shim = (args: string[], cwd = project, extraEnv: NodeJS.ProcessEnv = {}) => new Promise<number>((resolve) => {
  const env: NodeJS.ProcessEnv = { ...process.env, ...extraEnv, PATH: [LAKE_SHIM_DIR, path.join(dir, "bin"), path.dirname(process.execPath), "/usr/bin", "/bin"].join(":") };
  if (!extraEnv.PAPERFORMALIZER_LAKE_LOCK_HELD) delete env.PAPERFORMALIZER_LAKE_LOCK_HELD;
  execFile(path.join(LAKE_SHIM_DIR, "lake"), args, { cwd, env }, (err) => resolve(err ? (typeof err.code === "number" ? err.code : 1) : 0));
});
const lastCall = async () => (await readFile(log, "utf8")).trim().split("\n").at(-1);

describe.skipIf(process.platform === "win32")("lake shim", () => {
  it("locks what writes build output and passes the rest through", async () => {
    const cases: [string[], string][] = [
      [["build", "Papers.Toy"], "locked build Papers.Toy"],
      [[], "locked "],
      [["exe", "candidate_scan"], "locked exe candidate_scan"],
      [["lean", "Foo.lean"], "locked lean Foo.lean"],
      [["setup-file", "Foo.lean"], "locked setup-file Foo.lean"],
      [["env", "lean", "-o", "x.olean", "Foo.lean"], "locked env lean -o x.olean Foo.lean"],
      [["env", "lean", "Foo.lean"], "free env lean Foo.lean"],
      // a program under `lake env` that may call lake (the real one, first on its PATH): locked
      [["env", "lake", "build"], "locked env lake build"],
      [["env", "./build.sh"], "locked env ./build.sh"],
      [["env", "printenv", "LEAN_PATH"], "free env printenv LEAN_PATH"],
      [["env"], "free env"],
      [["serve"], "free serve"],
      [["--version"], "free --version"],
      [["check-build"], "free check-build"],
    ];
    for (const [args, seen] of cases) {
      expect(await shim(args)).toBe(0);
      expect(await lastCall()).toBe(seen.trimEnd());
    }
    // a lake command's own lake calls come back through the shim
    expect(await shim(["env", "bash", "-c", "lake build Inner"])).toBe(0);
    expect(await lastCall()).toBe("locked build Inner");
    // `-d <project>` from elsewhere locks that project; a directory with no lakefile is no project
    expect(await shim(["-d", project, "build"], dir)).toBe(0);
    expect(await lastCall()).toBe(`locked -d ${project} build`);
    expect(await shim(["build"], dir)).toBe(0);
    expect(await lastCall()).toBe("free build");
    // switched off
    expect(await shim(["build"], project, { PAPERFORMALIZER_LAKE_SHIM: "0" })).toBe(0);
    expect(await lastCall()).toBe("free build");
  }, 180_000);

  it("passes the exit status on, records the hold, and waits its turn behind the pipeline's own hold", async () => {
    expect(await shim(["build", "fail"])).toBe(3);
    expect(await shim(["serve", "fail"])).toBe(3);
    const holds = await readLockHolds(project);
    expect(holds.some((h) => h.what === "worker: lake build fail")).toBe(true);
    let shimDone = false;
    let run: Promise<number> = Promise.resolve(-1);
    await withLakeBuildLock(project, async () => {
      run = shim(["build", "Papers.Waiting"]).then((c) => { shimDone = true; return c; });
      await new Promise((r) => setTimeout(r, 3_000));
      expect(shimDone).toBe(false);
    }, "pipeline", () => {});
    expect(await run).toBe(0);
    expect(await lastCall()).toBe("locked build Papers.Waiting");
    // spawned from inside a hold (its token in the environment): runs inside it, at once
    await withLakeBuildLock(project, async () => {
      expect(await shim(["build", "Papers.Inside"], project, lakeLockChildEnv())).toBe(0);
    }, "pipeline", () => {});
    expect(await lastCall()).toBe("locked build Papers.Inside");
    // a hold record that cannot be read for a moment (an NFS blip) does not stop a build inside it
    const record = path.join(project, ".lake", "paperformalizer", "lake-lock-holder.json");
    await withLakeBuildLock(project, async () => {
      const blip = shim(["build", "Papers.blip"], project, { ...lakeLockChildEnv(), PAPERFORMALIZER_LAKE_SHIM_CHECK_MS: "200" });
      await new Promise((r) => setTimeout(r, 700));
      await rename(record, `${record}.away`);
      await new Promise((r) => setTimeout(r, 250));
      await rename(`${record}.away`, record);
      expect(await blip).toBe(0);
    }, "pipeline", () => {});
    // one left running (backgrounded) after the hold it ran inside is released: stopped, not left
    // building unlocked
    let outlived: Promise<number> = Promise.resolve(-1);
    const started = path.join(dir, "grandchild.pid");
    await rm(started, { force: true });
    await withLakeBuildLock(project, async () => {
      outlived = shim(["build", "Papers.slow"], project, { ...lakeLockChildEnv(), PAPERFORMALIZER_LAKE_SHIM_CHECK_MS: "200" });
      // released only once lake runs inside it (the shim's start takes seconds under load)
      for (let i = 0; i < 600 && !existsSync(started); i++) await new Promise((r) => setTimeout(r, 100));
    }, "pipeline", () => {});
    const t0 = Date.now();
    expect(await outlived).toBe(75);
    expect(Date.now() - t0).toBeLessThan(30_000);
    // lake's own children (its `lean` workers) are stopped with it
    const gc = Number(await readFile(path.join(dir, "grandchild.pid"), "utf8"));
    expect(gc).toBeGreaterThan(0);
    let alive = true;
    for (let i = 0; i < 50 && alive; i++) {
      try { process.kill(gc, 0); await new Promise((r) => setTimeout(r, 100)); } catch { alive = false; }
    }
    expect(alive).toBe(false);
  }, 180_000);

  it("in a model worker's process the shim still takes the lock; a worker's own script that imports it is refused", async () => {
    const worker = { PAPERFORMALIZER_MODEL_WORKER: "1" };
    expect(await shim(["build", "Papers.Worker"], project, worker)).toBe(0);
    expect(await lastCall()).toBe("locked build Papers.Worker");
    const tools = path.resolve(import.meta.dirname, "..", "..");
    const script = `import { withLakeBuildLock } from ${JSON.stringify(path.join(tools, "src/shared/build_mutex.ts"))};
      await withLakeBuildLock(${JSON.stringify(project)}, async () => { console.log("held"); }, "serial build");`;
    const r = await new Promise<{ code: number; out: string; err: string }>((resolve) => execFile(process.execPath,
      ["--import", path.join(tools, "node_modules/tsx/dist/loader.mjs"), "--input-type=module", "-e", script],
      { env: { ...process.env, ...worker }, cwd: tools }, (e, out, err) => resolve({ code: e ? (typeof e.code === "number" ? e.code : 1) : 0, out, err })));
    expect(r.code).not.toBe(0);
    expect(r.out).not.toContain("held");
    expect(r.err).toMatch(/refused — this is a model worker's process/);
  }, 180_000);

  it("a tool timeout that SIGKILLs the shim's process group leaves no lake or lean running", async () => {
    await rm(path.join(dir, "orphan.pid"), { force: true });
    const env: NodeJS.ProcessEnv = { ...process.env, PATH: [LAKE_SHIM_DIR, path.join(dir, "bin"), path.dirname(process.execPath), "/usr/bin", "/bin"].join(":") };
    delete env.PAPERFORMALIZER_LAKE_LOCK_HELD;
    // the worker's command: a process group of its own, as a tool runs it
    const cmd = spawn(path.join(LAKE_SHIM_DIR, "lake"), ["build", "Papers.orphan"], { cwd: project, env, detached: true, stdio: "ignore" });
    const pidFile = path.join(dir, "orphan.pid");
    for (let i = 0; i < 300 && !existsSync(pidFile); i++) await new Promise((r) => setTimeout(r, 100));
    await new Promise((r) => setTimeout(r, 200));
    const lean = Number(await readFile(pidFile, "utf8"));
    const lake = Number(await readFile(path.join(dir, "lake.pid"), "utf8"));
    process.kill(-cmd.pid!, "SIGKILL");
    for (const pid of [lake, lean]) {
      let alive = true;
      for (let i = 0; i < 100 && alive; i++) {
        try { process.kill(pid, 0); await new Promise((r) => setTimeout(r, 100)); } catch { alive = false; }
      }
      expect(alive, `pid ${pid}`).toBe(false);
    }
  }, 180_000);

  it("asks for a shared hold for a build or elaboration of one paper's modules only, once shared mode is on and the toolkit clean; refuses anything else inside one", async () => {
    // a project of its own: the test before leaves its mutex held (a SIGKILLed holder, stale in 10 min)
    const project = path.join(dir, "toolkit2");
    await mkdir(path.join(project, "Papers", "Toy"), { recursive: true });
    await mkdir(path.join(project, ".lake", "paperformalizer"), { recursive: true });
    await writeFile(path.join(project, "lakefile.toml"), 'name = "t2"\n');
    await writeFile(path.join(project, "Toolkit.lean"), "module\n");
    await writeFile(path.join(project, "Papers", "Toy", "A.lean"), "module\nimport Toolkit\n");
    await mkdir(path.join(project, "Toolkit", "Staging", "Stu"), { recursive: true });
    await writeFile(path.join(project, "Toolkit", "Staging", "Stu", "A.lean"), "module\nimport Toolkit\n");
    const modeFile = path.join(project, ".lake", "paperformalizer", "lake-shared-mode");
    await writeFile(modeFile, "");
    try {
      // the toolkit built clean, by a process with the workers' PATH (the toolchain it resolves is
      // part of the signature): its `lake build Toolkit` goes through the shim, inside its hold
      const tools = path.resolve(import.meta.dirname, "..", "..");
      const script = `import { stampToolkitClean, withLakeBuildLock } from ${JSON.stringify(path.join(tools, "src/shared/build_mutex.ts"))};
        console.log(JSON.stringify(await withLakeBuildLock(${JSON.stringify(project)}, () => stampToolkitClean(${JSON.stringify(project)}, () => {}), "settle", () => {})));`;
      const env: NodeJS.ProcessEnv = { ...process.env, PATH: [LAKE_SHIM_DIR, path.join(dir, "bin"), path.dirname(process.execPath), "/usr/bin", "/bin"].join(":") };
      delete env.PAPERFORMALIZER_LAKE_LOCK_HELD;
      const settled = await new Promise<string>((resolve, reject) => execFile(process.execPath,
        ["--import", path.join(tools, "node_modules/tsx/dist/loader.mjs"), "--input-type=module", "-e", script], { env, cwd: tools }, (e, out) => (e ? reject(e) : resolve(out))));
      expect(JSON.parse(settled.trim().split("\n").at(-1)!)).toEqual({ clean: true });
      expect(await lastCall()).toBe("locked build Toolkit");
      const cases: [string[], string][] = [
        [["build", "Papers.Toy.A"], "shared build Papers.Toy.A"],
        [["-d", project, "build", "-v", "+Papers.Toy.A"], `shared -d ${project} build -v +Papers.Toy.A`],
        [["lean", "Papers/Toy/A.lean"], "shared lean Papers/Toy/A.lean"],
        // a study's own staging modules, as a paper's
        [["build", "Toolkit.Staging.Stu.A"], "shared build Toolkit.Staging.Stu.A"],
        [["build", "Toolkit.Staging"], "locked build Toolkit.Staging"],
        // not one paper's modules only: exclusive (`env lean -o` writes wherever it is told)
        [["env", "lean", "-o", path.join(os.tmpdir(), "a.olean"), "Papers/Toy/A.lean"], `locked env lean -o ${path.join(os.tmpdir(), "a.olean")} Papers/Toy/A.lean`],
        [["build", "Papers"], "locked build Papers"],
        [["build", "Papers.Toy.A", "Toolkit"], "locked build Papers.Toy.A Toolkit"],
        [["build", "-R", "Papers.Toy.A"], "locked build -R Papers.Toy.A"],
      ];
      for (const [args, seen] of cases) {
        expect(await shim(args, project)).toBe(0);
        expect(await lastCall()).toBe(seen);
      }
      const holds = await readLockHolds(project);
      expect(holds.find((h) => h.what === "worker: lake build Papers.Toy.A")).toMatchObject({ mode: "shared" });
      expect(holds.find((h) => h.what === "worker: lake build Papers")).toMatchObject({ mode: "exclusive" });
      // spawned inside a shared hold: a command of its paper runs inside it; any other is refused
      // (the hold taken with the workers' PATH too: the toolchain it resolves is the stamp's)
      const PATH = process.env.PATH;
      process.env.PATH = env.PATH;
      await withLakeBuildLock(project, async () => {
        process.env.PATH = PATH;
        expect(await shim(["build", "Papers.Toy.A"], project, lakeLockChildEnv())).toBe(0);
        expect(await lastCall()).toBe("shared build Papers.Toy.A");
        expect(await shim(["build", "Toolkit"], project, lakeLockChildEnv())).toBe(1);
        expect(await lastCall()).toBe("shared build Papers.Toy.A"); // lake never ran
      }, "pipeline", () => {}, undefined, { papers: ["Papers.Toy"] }).finally(() => { process.env.PATH = PATH; });
      expect(holds.length).toBeGreaterThan(0);
      expect((await readLockHolds(project)).find((h) => h.what === "pipeline")).toMatchObject({ mode: "shared" });
      // switched off: exclusive again
      await rm(modeFile);
      expect(await shim(["build", "Papers.Toy.A"], project)).toBe(0);
      expect(await lastCall()).toBe("locked build Papers.Toy.A");
    } finally {
      await rm(modeFile, { force: true });
    }
  }, 180_000);
});

describe.skipIf(process.platform === "win32")("lake shim: a worker's build paused for a writer", () => {
  let project = "";
  let env: NodeJS.ProcessEnv = {};
  const PATH = process.env.PATH;
  const grace = LAKE_LOCK_TIMING.preemptGraceMs;
  beforeAll(async () => {
    // a toolkit in shared mode, built clean (as in the test above) by a process with the workers' PATH
    project = path.join(dir, "toolkit3");
    await mkdir(path.join(project, ".lake", "paperformalizer"), { recursive: true });
    await writeFile(path.join(project, "lakefile.toml"), 'name = "t3"\n');
    await writeFile(path.join(project, "Toolkit.lean"), "module\n");
    for (const p of ["PausableA", "PausableB", "PausableC", "PausableD", "PausableE", "PausableF", "PausableG", "PausableH"]) {
      await mkdir(path.join(project, "Papers", p), { recursive: true });
      await writeFile(path.join(project, "Papers", p, "M.lean"), "module\nimport Toolkit\n");
    }
    await writeFile(path.join(project, ".lake", "paperformalizer", "lake-shared-mode"), "");
    env = { ...process.env, PATH: [LAKE_SHIM_DIR, path.join(dir, "bin"), path.dirname(process.execPath), "/usr/bin", "/bin"].join(":") };
    delete env.PAPERFORMALIZER_LAKE_LOCK_HELD;
    const tools = path.resolve(import.meta.dirname, "..", "..");
    const script = `import { stampToolkitClean, withLakeBuildLock } from ${JSON.stringify(path.join(tools, "src/shared/build_mutex.ts"))};
      console.log(JSON.stringify(await withLakeBuildLock(${JSON.stringify(project)}, () => stampToolkitClean(${JSON.stringify(project)}, () => {}), "settle", () => {})));`;
    const settled = await new Promise<string>((resolve, reject) => execFile(process.execPath,
      ["--import", path.join(tools, "node_modules/tsx/dist/loader.mjs"), "--input-type=module", "-e", script], { env, cwd: tools }, (e, out) => (e ? reject(e) : resolve(out))));
    expect(JSON.parse(settled.trim().split("\n").at(-1)!)).toEqual({ clean: true });
    // this process's holds resolve the toolchain the stamp names; a writer counts as waiting after 0.5 s
    process.env.PATH = env.PATH;
    LAKE_LOCK_TIMING.preemptGraceMs = 500;
  }, 180_000);
  afterAll(() => {
    process.env.PATH = PATH;
    LAKE_LOCK_TIMING.preemptGraceMs = grace;
  });

  /** The shim's exit status and stderr, its holds watched every 200 ms. */
  const run = (args: string[], extraEnv: NodeJS.ProcessEnv = {}) => new Promise<{ code: number; err: string }>((resolve) => {
    const e: NodeJS.ProcessEnv = { ...env, ...extraEnv, PAPERFORMALIZER_LAKE_SHIM_CHECK_MS: "200" };
    execFile(path.join(LAKE_SHIM_DIR, "lake"), args, { cwd: project, env: e }, (err, _out, stderr) =>
      resolve({ code: err ? (typeof err.code === "number" ? err.code : 1) : 0, err: stderr }));
  });
  /** The shim run as `run` does, its stderr read as it comes. */
  const start = (args: string[]) => {
    const c = spawn(path.join(LAKE_SHIM_DIR, "lake"), args, { cwd: project, env: { ...env, PAPERFORMALIZER_LAKE_SHIM_CHECK_MS: "200" } });
    let err = "";
    c.stderr.on("data", (d) => { err += d; });
    const exit = new Promise<number | null>((r) => c.on("exit", (code, s) => r(code ?? (s ? -1 : null))));
    return { c, err: () => err, exit };
  };
  const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));
  const until = async (what: string, f: () => Promise<boolean>) => {
    for (const t0 = Date.now(); !(await f()); await sleep(100)) if (Date.now() - t0 > 60_000) throw new Error(`timed out: ${what}`);
  };
  const runs = async (t: string) => (await readFile(path.join(dir, `${t}.runs`), "utf8").catch(() => "")).split("\n").filter(Boolean).length;
  const gone = async (pid: number) => {
    for (let i = 0; i < 50; i++) {
      try { process.kill(pid, 0); } catch { return true; }
      await sleep(100);
    }
    return false;
  };
  const pendingAfter = async (p: Promise<unknown>, ms: number) => Promise.race([p.then(() => false), sleep(ms).then(() => true)]);

  it("a build under a shared hold of its own is stopped (lean children too) for a writer draining past the grace, which gets in; then it re-runs and exits 0", async () => {
    const t = "Papers.PausableA.M";
    const build = run(["build", t]);
    await until("lake runs", async () => existsSync(path.join(dir, `${t}.child`)));
    expect(await lastCall()).toBe(`shared build ${t}`);
    const lean = Number(await readFile(path.join(dir, `${t}.child`), "utf8"));
    const asked = Date.now();
    let inside = -1;
    await withLakeBuildLock(project, async () => {
      inside = await runs(t);
      await writeFile(path.join(dir, `${t}.go`), "");
    }, "writer", () => {});
    // in seconds: the grace, the shim's look, the drain's
    expect(Date.now() - asked).toBeLessThan(20_000);
    expect(inside).toBe(1);
    expect(await gone(lean)).toBe(true);
    const r = await build;
    expect(r.code).toBe(0);
    expect(await runs(t)).toBe(2);
    expect(await lastCall()).toBe(`shared build ${t}`);
    expect(r.err.match(/paused for a writer/g)).toHaveLength(1);
    expect(r.err).toContain(`\`lake build ${t}\` paused for a writer of the toolkit's build (writer), pause 1 of 3 — it re-runs once the writer is done (Lake reuses what is still up to date)`);
    const holds = (await readLockHolds(project)).filter((h) => h.what === `worker: lake build ${t}` || h.what === "writer").map((h) => `${h.what} ${h.mode}`).sort();
    // the worker's command held twice (before and after its pause), shared both times
    expect(holds).toEqual([`worker: lake build ${t} shared`, `worker: lake build ${t} shared`, "writer exclusive"]);
  }, 180_000);

  it("pauses one build 3 times at most: the next writer waits for it to end", async () => {
    const t = "Papers.PausableB.M";
    const build = run(["build", t]);
    for (let k = 1; k <= 3; k++) {
      await until(`run ${k}`, async () => (await runs(t)) === k);
      await withLakeBuildLock(project, async () => {}, `writer ${k}`, () => {});
    }
    await until("run 4", async () => (await runs(t)) === 4);
    const last = withLakeBuildLock(project, async () => {}, "writer 4", () => {});
    // past the grace and many looks of the shim: not paused (its hold is not pausable: no writer marks)
    expect(await pendingAfter(last, 4_000)).toBe(true);
    expect(await lakeWriterWaiting(project)).toBeNull();
    expect(await runs(t)).toBe(4);
    await writeFile(path.join(dir, `${t}.go`), "");
    const r = await build;
    await last;
    expect(r.code).toBe(0);
    expect(await runs(t)).toBe(4);
    expect(r.err.match(/paused for a writer/g)).toHaveLength(3);
    expect(r.err).toMatch(/pause 3 of 3/);
  }, 180_000);

  it("a build inside a pipeline's shared hold is never paused: the writer waits for that hold to end", async () => {
    const t = "Papers.PausableC.M";
    let started!: () => void;
    const inLake = new Promise<void>((r) => { started = r; });
    const hold = withLakeBuildLock(project, async () => {
      expect(lakeHoldMode(project)).toBe("shared");
      const b = run(["build", t], lakeLockChildEnv());
      await until("lake runs", async () => (await runs(t)) === 1);
      started();
      return b;
    }, "pipeline", () => {}, undefined, { papers: ["Papers.PausableC"] });
    await inLake;
    const writer = withLakeBuildLock(project, async () => {}, "writer C", () => {});
    expect(await pendingAfter(writer, 4_000)).toBe(true);
    expect(await lakeWriterWaiting(project)).toBeNull();
    expect(await runs(t)).toBe(1);
    await writeFile(path.join(dir, `${t}.go`), "");
    const r = await hold;
    await writer;
    expect(r.code).toBe(0);
    expect(r.err).not.toMatch(/paused/);
    expect(await runs(t)).toBe(1);
  }, 180_000);

  // the auditor's PROBE1: a writer that still waits for a pipeline's hold pauses no worker's build
  it("a worker's build is not paused while the writer still waits for a pipeline's shared hold; once only pausable holds stand, it is", async () => {
    const tG = "Papers.PausableG.M";
    const endPipe = (() => { let open!: () => void; const p = new Promise<void>((r) => { open = r; }); return { p, open }; })();
    let pipeIn!: () => void;
    const pipeStarted = new Promise<void>((r) => { pipeIn = r; });
    const pipe = withLakeBuildLock(project, async () => { pipeIn(); await endPipe.p; }, "pipeline scan", () => {}, undefined, { papers: ["Papers.PausableF"] });
    await pipeStarted;
    const build = run(["build", tG]);
    await until("G runs", async () => (await runs(tG)) === 1);
    const lean = Number(await readFile(path.join(dir, `${tG}.child`), "utf8"));
    const writer = withLakeBuildLock(project, async () => {}, "writer P1", () => {});
    expect(await pendingAfter(writer, 3_000)).toBe(true);
    expect(await lakeWriterWaiting(project)).toBeNull();
    let alive = true;
    try { process.kill(lean, 0); } catch { alive = false; }
    expect(alive).toBe(true);
    expect(await runs(tG)).toBe(1);
    endPipe.open();
    await pipe;
    expect(await gone(lean)).toBe(true);
    await writer;
    await writeFile(path.join(dir, `${tG}.go`), "");
    const r = await build;
    expect(r.code).toBe(0);
    expect(await runs(tG)).toBe(2);
    expect(r.err.match(/paused for a writer/g)).toHaveLength(1);
  }, 180_000);

  // the auditor's PROBE2: the re-run after a writer that left the toolkit unclean holds off (a writer gets in meanwhile) until it is clean, then runs shared
  it("a paused build's re-run holds off while the writer left the toolkit not clean, then runs shared and pausable", async () => {
    const t = "Papers.PausableD.M";
    const src = path.join(project, "Toolkit.lean");
    const orig = await readFile(src, "utf8");
    try {
      const build = start(["build", t]);
      await until("D runs", async () => (await runs(t)) === 1);
      await withLakeBuildLock(project, async () => { await writeFile(src, `${orig}-- edited by the writer\n`); }, "writer P2", () => {});
      // held off: no re-run, and another writer is not stuck behind it
      await until("D holds off", async () => /the toolkit changed since its last clean build — holding off before building/.test(build.err()));
      const t0 = Date.now();
      await withLakeBuildLock(project, async () => {}, "writer P2b", () => {});
      expect(Date.now() - t0).toBeLessThan(10_000);
      expect(await runs(t)).toBe(1);
      expect(await withLakeBuildLock(project, () => stampToolkitClean(project, () => {}), "settle P2", () => {})).toEqual({ clean: true });
      await until("D re-run", async () => (await runs(t)) === 2);
      expect(await lastCall()).toBe(`shared build ${t}`);
      await writeFile(path.join(dir, `${t}.go`), "");
      expect(await build.exit).toBe(0);
      expect(build.err()).not.toMatch(/holding off[^\n]*another run is building/);
    } finally {
      await writeFile(src, orig);
      await withLakeBuildLock(project, () => stampToolkitClean(project, () => {}), "settle P2 again", () => {});
    }
  }, 180_000);

  // the auditor's PROBE3: a worker's build in flux holds off without its paper lock or the mutex, leaves at once on SIGTERM, and builds once the session ends
  it("a worker's build in flux holds off, taking nothing; SIGTERM ends it at once; the session's end lets it build shared", async () => {
    const t = "Papers.PausableE.M";
    const id = await toolkitFluxOn(project, "orphan", () => {});
    try {
      const { c, err, exit } = start(["build", t]);
      await until("holding off", async () => /holding off before building/.test(err()));
      expect(existsSync(path.join(lakePaperLocksDir(path.join(project, ".lake-build.lock")), "Papers.PausableE.lock"))).toBe(false);
      expect(existsSync(path.join(project, ".lake-build.lock.lock"))).toBe(false);
      const t0 = Date.now();
      c.kill("SIGTERM");
      expect(await exit).toBe(143);
      expect(Date.now() - t0).toBeLessThan(5_000);
      expect(await runs(t)).toBe(0);
      // again, and the session closed: it builds, shared
      const build = run(["build", t]);
      await sleep(2_000);
      expect(await runs(t)).toBe(0);
      await toolkitFluxOff(project, id, () => {});
      await until("E runs", async () => (await runs(t)) === 1);
      expect(await lastCall()).toBe(`shared build ${t}`);
      await writeFile(path.join(dir, `${t}.go`), "");
      expect((await build).code).toBe(0);
    } finally {
      await toolkitFluxOff(project, id, () => {}).catch(() => {});
    }
  }, 180_000);

  it("a command whose output a machine reads (--json) is never paused", async () => {
    const t = "Papers.PausableH.M";
    const build = run(["build", "--json", t]);
    await until("H runs", async () => (await runs(t)) === 1);
    const writer = withLakeBuildLock(project, async () => {}, "writer H", () => {});
    expect(await pendingAfter(writer, 3_000)).toBe(true);
    expect(await lakeWriterWaiting(project)).toBeNull();
    await writeFile(path.join(dir, `${t}.go`), "");
    const r = await build;
    await writer;
    expect(r.code).toBe(0);
    expect(await runs(t)).toBe(1);
    expect(r.err).not.toMatch(/paused/);
  }, 180_000);
});

// A run with a Lake workspace of its own (`src/shared/workspace.ts`, $PAPERFORMALIZER_LEAN_WS): the
// shim runs a command on the shared toolkit in the workspace — its directory, `-d`/`--dir` and the
// paths under the toolkit (but its `.lake`) rewritten — with no shared-tree lock; one that writes
// build output under the workspace's own lock. Cleared, or inside a hold, it is the shared tree's.
describe.skipIf(process.platform === "win32")("lake shim in a run's workspace", () => {
  let tk: string;
  let ws: string;
  let wslog: string;
  beforeAll(async () => {
    tk = path.join(dir, "wstk");
    ws = path.join(dir, "ws", "r", "wstk");
    await mkdir(path.join(tk, "Papers"), { recursive: true });
    await mkdir(path.join(tk, ".lake", "build", "paperformalizer"), { recursive: true });
    await writeFile(path.join(tk, "lakefile.toml"), 'name = "wstk"\n');
    await writeFile(path.join(tk, "Papers", "X.lean"), "\n");
    await mkdir(path.join(ws, ".lake"), { recursive: true });
    for (const e of ["lakefile.toml", "Papers"]) await symlink(path.join(tk, e), path.join(ws, e));
    await writeFile(path.join(ws, ".pf-toolkit"), `${tk}\n`);
    // the toolkit stamped clean (its path dependencies built): a build in the workspace runs
    await mkdir(path.join(tk, ".lake", "paperformalizer"), { recursive: true });
    // pretty-printed, as the live stamp is (a compact one is written mid-wait in the hold-off test)
    await writeFile(path.join(tk, ".lake", "paperformalizer", "toolkit-clean.json"), `${JSON.stringify({ sig: "s", ok: true }, null, 2)}\n`);
    wslog = path.join(dir, "ws-calls.log");
    // the "real" lake: where it ran, whether the workspace's lock and the shared tree's were held
    await mkdir(path.join(dir, "wsbin"));
    await writeFile(path.join(dir, "wsbin", "lake"), `#!/usr/bin/env bash\n[[ "$1" == env && "$2" == bash ]] && { shift; exec "$@"; }\n` +
      `w="\${PAPERFORMALIZER_LEAN_WS:-}"\nif [[ -n "$w" ]] && ! flock -n "$w/.lake/build.lock" true 2>/dev/null; then l=wslocked; else l=wsfree; fi\n` +
      `[[ -d ${JSON.stringify(tk)}/.lake-build.lock.lock ]] && l="$l+shared"\necho "$l $PWD $*" >> ${JSON.stringify(wslog)}\n`);
    await chmod(path.join(dir, "wsbin", "lake"), 0o755);
  });
  const wsShim = (args: string[], cwd = tk, extraEnv: NodeJS.ProcessEnv = {}) => new Promise<number>((resolve) => {
    const env: NodeJS.ProcessEnv = { ...process.env, PAPERFORMALIZER_LEAN_WS: ws, ...extraEnv, PATH: [LAKE_SHIM_DIR, path.join(dir, "wsbin"), path.dirname(process.execPath), "/usr/bin", "/bin"].join(":") };
    if (!extraEnv.PAPERFORMALIZER_LAKE_LOCK_HELD) delete env.PAPERFORMALIZER_LAKE_LOCK_HELD;
    execFile(path.join(LAKE_SHIM_DIR, "lake"), args, { cwd, env, timeout: 60_000 }, (err) => resolve(err ? (typeof err.code === "number" ? err.code : 1) : 0));
  });
  const wsLast = async () => (await readFile(wslog, "utf8")).trim().split("\n").at(-1);

  it("runs the toolkit's commands in the workspace, paths rewritten, under its own lock and never the shared tree's", async () => {
    const out = path.join(tk, ".lake", "build", "paperformalizer", "x.json");
    const cases: [string[], string, string][] = [
      [["build", "Papers.X"], tk, `wslocked ${ws} build Papers.X`],
      [[], tk, `wslocked ${ws}`],
      [["-d", tk, "build"], dir, `wslocked ${dir} -d ${ws} build`],
      [[`--dir=${tk}`, "build"], dir, `wslocked ${dir} --dir=${ws} build`],
      [["env", "lean", path.join(tk, "Papers", "X.lean")], tk, `wsfree ${ws} env lean ${path.join(ws, "Papers", "X.lean")}`],
      // the toolkit's `.lake` is not the workspace's: an output path there stays the shared tree's
      [["exe", "candidate_scan", "--", "--out", out], tk, `wslocked ${ws} exe candidate_scan -- --out ${out}`],
      [["serve"], tk, `wsfree ${ws} serve`],
      [["build", "Papers.X"], path.join(tk, "Papers"), `wslocked ${path.join(ws, "Papers")} build Papers.X`],
      // a lake under the workspace's lock passes it by (never waits on its own parent)
      [["env", "bash", "-c", "lake build Inner"], tk, `wslocked ${ws} build Inner`],
    ];
    for (const [args, cwd, seen] of cases) {
      expect(await wsShim(args, cwd), args.join(" ")).toBe(0);
      expect(await wsLast()).toBe(seen);
    }
    expect((await readLockHolds(tk)).filter((h) => h.lock === "lake")).toEqual([]);
    expect(existsSync(path.join(tk, ".lake-build.lock"))).toBe(false);
  }, 180_000);

  it("holds off a build while the toolkit is in flux or not stamped clean, then does not build (75); a read runs", async () => {
    const pf = path.join(tk, ".lake", "paperformalizer");
    const quick = { PAPERFORMALIZER_LAKE_FLUX_WAIT_S: "1", PAPERFORMALIZER_LAKE_FLUX_WAIT_MAX_S: "2" };
    const calls = async () => (await readFile(wslog, "utf8")).trim().split("\n").length;
    const n = await calls();
    // a flux session (the marker, or a session's file): its path dependencies may be mid-change
    await writeFile(path.join(pf, "toolkit-flux"), "{}");
    expect(await wsShim(["build", "Papers.X"], tk, quick)).toBe(75);
    await rm(path.join(pf, "toolkit-flux"));
    await mkdir(path.join(pf, "toolkit-flux.d"), { recursive: true });
    await writeFile(path.join(pf, "toolkit-flux.d", "m1abc-0a1b2c"), "{}");
    expect(await wsShim(["setup-file", path.join(tk, "Papers", "X.lean")], tk, quick)).toBe(75);
    // a read builds nothing: it runs
    expect(await wsShim(["serve"], tk, quick)).toBe(0);
    expect(await calls()).toBe(n + 1);
    await rm(path.join(pf, "toolkit-flux.d"), { recursive: true });
    // the stamp dropped (a flux session's, or a failed clean build)
    const stamp = path.join(pf, "toolkit-clean.json");
    await writeFile(stamp, '{"sig":"flux","ok":false,"why":"the toolkit is in flux"}\n');
    expect(await wsShim(["build", "Papers.X"], tk, quick)).toBe(75);
    expect(await calls()).toBe(n + 1);
    // stamped again while it holds off: it builds
    const late = wsShim(["build", "Papers.X"], tk, { PAPERFORMALIZER_LAKE_FLUX_WAIT_S: "1", PAPERFORMALIZER_LAKE_FLUX_WAIT_MAX_S: "60" });
    await new Promise((r) => setTimeout(r, 1_500));
    await writeFile(stamp, '{"sig":"s","ok":true}\n');
    expect(await late).toBe(0);
    expect(await wsLast()).toBe(`wslocked ${ws} build Papers.X`);
  }, 180_000);

  it("is the shared tree's when the workspace is cleared, inside a hold, or the command is not on the toolkit", async () => {
    expect(await wsShim(["build", "Papers.X"], tk, { PAPERFORMALIZER_LEAN_WS: "" })).toBe(0);
    expect(await wsLast()).toBe(`wsfree+shared ${tk} build Papers.X`);
    expect(await wsShim(["build", "Papers.Y"], tk, { PAPERFORMALIZER_LAKE_LOCK_HELD: "notaholdtoken" })).toBe(0);
    expect(await wsLast()).toBe(`wsfree+shared ${tk} build Papers.Y`);
    expect(await wsShim(["build"], dir)).toBe(0);
    expect(await wsLast()).toBe(`wsfree ${dir} build`);
    expect((await readLockHolds(tk)).filter((h) => h.lock === "lake").map((h) => h.what)).toEqual(["worker: lake build Papers.X", "worker: lake build Papers.Y"]);
  }, 180_000);
});
