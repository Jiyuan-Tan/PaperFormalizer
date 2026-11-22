// Per-run Lake workspaces: generations published only once turned on, a workspace made
// and re-pinned idempotently, its build outputs hard links but for what Lake writes in place, the
// pipeline's own lake calls taken there with no shared-tree lock, and a run without the switch as
// before.
import { execFile, execFileSync } from "node:child_process";
import { existsSync, lstatSync, readFileSync, readlinkSync, statSync } from "node:fs";
import { chmod, mkdir, mkdtemp, readFile, readdir, rm, symlink, unlink, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterAll, afterEach, beforeAll, describe, expect, it } from "vitest";
import { LAKE_SHIM_DIR, LEAN_WS_ENV, leanWorkspaceFor, leanWsChildEnv, withLakeBuildLock, withPromotionLock, withSharedTree } from "../../src/shared/build_mutex.js";
import { readLockHolds } from "../../src/shared/lock_holds.js";
import { greenBuildCurrent, recordGreenBuild, recordScan, scanCurrent, sourceSignature } from "../../src/shared/build_inputs.js";
import { WORKSPACE_SWEEP, WORKSPACE_TIMING, currentGeneration, enableRunWorkspace, ensureWorkspace, gensDir, publishGeneration, spawnPublisher, workspacePath } from "../../src/shared/workspace.js";
import { TOOLKIT_JSON } from "../toolkit/helpers.js";
import { spawnWithInactivityTimeout } from "../../src/workers/spawn.js";

const SCRIPT = path.resolve(LAKE_SHIM_DIR, "..", "lean_workspace.sh");
const haveTools = (() => { try { execFileSync("bash", ["-c", "command -v zstd && command -v flock"]); return true; } catch { return false; } })();

let dir: string;
let root: string;
let local: string;
const quiet = () => {};
const put = async (rel: string, text: string, base = root) => {
  await mkdir(path.dirname(path.join(base, rel)), { recursive: true });
  await writeFile(path.join(base, rel), text);
};
const ino = (p: string) => statSync(p).ino;

beforeAll(async () => {
  dir = await mkdtemp(path.join(os.tmpdir(), "lean-ws-"));
  // the toolkit two levels down, as its path dependencies need (`../../Dep/Dep`, `../third/Lib`)
  root = path.join(dir, "top", "TC", "tk");
  local = path.join(dir, "local");
  await put("lakefile.toml", 'name = "tk"\n[[require]]\nname = "Dep"\npath = "../../Dep/Dep"\n[[require]]\nname = "Lib"\npath = "../third/Lib"\n');
  await put("lean-toolchain", "leanprover/lean4:v4.33.0\n");
  await put("lake-manifest.json", "{}\n");
  for (const f of ["Toolkit.lean", "CandidateScan.lean", "Papers.lean", "Toolkit/A.lean", "Toolkit/Staging/S.lean", "Papers/P.lean", "runs/r1/state.json"]) await put(f, `-- ${f}\n`);
  for (const f of ["lib/lean/Toolkit.olean", "lib/lean/Toolkit.olean.hash", "lib/lean/Toolkit.trace", "lib/lean/Toolkit/A.olean", "lib/lean/Toolkit/A.olean.hash",
    "lib/lean/Toolkit/A.trace", "lib/lean/Toolkit/A.ilean", "lib/lean/Toolkit/Staging/S.olean", "ir/Toolkit/A.c", "ir/Toolkit/A.setup.json", "ir/Toolkit.setup.json",
    "lib/lean/CandidateScan.olean", "lib/lean/Papers/P.olean", "bin/candidate_scan", "bin/candidate_scan.trace", "bin/candidate_scan.rsp"]) {
    await put(path.join(".lake", "build", f), `${f} v1\n`);
  }
  await put(".lake/config/tk/lakefile.olean", "config\n");
  await mkdir(path.join(dir, "pkgs", "mathlib"), { recursive: true });
  await mkdir(path.join(root, ".lake", "packages", ".pf-shared", "mathlib"), { recursive: true });
  await symlink(path.join(dir, "pkgs", "mathlib"), path.join(root, ".lake", "packages", "mathlib"));
  await mkdir(path.join(dir, "top", "Dep", "Dep"), { recursive: true });
  await mkdir(path.join(dir, "top", "TC", "third", "Lib"), { recursive: true });
  // the machine's local Lean root (else read from `.lake/packages/.pf-local-root`)
  process.env.PAPERFORMALIZER_LEAN_LOCAL_ROOT = local;
});
afterAll(async () => {
  delete process.env.PAPERFORMALIZER_LEAN_LOCAL_ROOT;
  // the generations' linked files are read-only: rm needs their directories writable only
  await rm(dir, { recursive: true, force: true });
});
afterEach(() => { delete process.env[LEAN_WS_ENV]; });

describe.skipIf(process.platform === "win32" || !haveTools)("lean workspaces", () => {
  it("publishes nothing until generations are turned on, then one generation per signature", async () => {
    expect(await publishGeneration(root, "s1", quiet)).toBeNull();
    expect(existsSync(gensDir(root))).toBe(false);
    await mkdir(gensDir(root), { recursive: true });
    const g1 = await publishGeneration(root, "s1", quiet);
    expect(g1?.gen).toBe(1);
    expect(existsSync(path.join(gensDir(root), "1.tar.zst"))).toBe(true);
    expect((await publishGeneration(root, "s1", quiet))?.gen).toBe(1);
    expect((await readdir(gensDir(root))).sort()).toEqual(["1.tar.zst", "CURRENT.json"]);
    // the archive: pinned sources and their outputs, never the staging tree or the papers'
    const names = execFileSync("bash", ["-c", `zstd -dc "$1" | tar -t`, "_", path.join(gensDir(root), "1.tar.zst")], { encoding: "utf8" }).split("\n");
    expect(names).toEqual(expect.arrayContaining(["Toolkit/A.lean", "Toolkit.lean", "CandidateScan.lean", "lakefile.toml", ".lake/build/lib/lean/Toolkit/A.olean", ".lake/build/bin/candidate_scan"]));
    expect(names.filter((n) => /Staging|Papers|runs\//.test(n))).toEqual([]);
    // never a module's `.setup.json` (Lake writes it anew before each compile; nothing reads it after)
    expect(names.filter((n) => n.endsWith(".setup.json"))).toEqual([]);
  }, 60_000);

  it("makes a run's workspace: pinned files linked, Lake's in-place files copied, the rest the shared tree's", async () => {
    const r = await ensureWorkspace(root, "r1", { localRoot: local });
    const ws = r.path;
    expect(ws).toBe(path.join(local, "ws", "r1", "TC", "tk"));
    expect(ws).toBe(workspacePath(root, "r1", local));
    expect(r).toMatchObject({ gen: 1, repinned: true });
    const gen = path.join(local, "gens", "1");
    // pinned sources: own files, links into the machine's generation, read-only
    expect(lstatSync(path.join(ws, "Toolkit")).isDirectory()).toBe(true);
    expect(ino(path.join(ws, "Toolkit", "A.lean"))).toBe(ino(path.join(gen, "Toolkit", "A.lean")));
    expect(statSync(path.join(ws, "Toolkit", "A.lean")).mode & 0o222).toBe(0);
    expect(ino(path.join(ws, "Toolkit.lean"))).toBe(ino(path.join(gen, "Toolkit.lean")));
    expect(lstatSync(path.join(ws, "lakefile.toml")).isSymbolicLink()).toBe(false);
    // the staging tree and every other entry: the shared tree's
    expect(readlinkSync(path.join(ws, "Toolkit", "Staging"))).toBe(path.join(root, "Toolkit", "Staging"));
    for (const e of ["Papers", "Papers.lean", "runs"]) expect(readlinkSync(path.join(ws, e))).toBe(path.join(root, e));
    // the build outputs: compiler outputs linked, what Lake rewrites in place copied
    const b = (rel: string) => path.join(ws, ".lake", "build", rel);
    const g = (rel: string) => path.join(gen, ".lake", "build", rel);
    for (const f of ["lib/lean/Toolkit/A.olean", "lib/lean/Toolkit/A.ilean", "lib/lean/Toolkit.olean", "ir/Toolkit/A.c", "lib/lean/CandidateScan.olean", "bin/candidate_scan"]) {
      expect(ino(b(f)), f).toBe(ino(g(f)));
    }
    for (const f of ["lib/lean/Toolkit/A.trace", "lib/lean/Toolkit/A.olean.hash", "lib/lean/Toolkit.trace", "bin/candidate_scan.trace", "bin/candidate_scan.rsp"]) {
      expect(ino(b(f)), f).not.toBe(ino(g(f)));
      expect(readFileSync(b(f), "utf8")).toBe(readFileSync(g(f), "utf8"));
    }
    expect(existsSync(b("ir/Toolkit/A.setup.json"))).toBe(false);
    expect(existsSync(b("lib/lean/Toolkit/Staging"))).toBe(false);
    expect(existsSync(b("lib/lean/Papers"))).toBe(false);
    // packages: the shared tree's links, not its archives; the config a copy; the path dependencies' anchors
    expect(readlinkSync(path.join(ws, ".lake", "packages", "mathlib"))).toBe(path.join(dir, "pkgs", "mathlib"));
    expect(existsSync(path.join(ws, ".lake", "packages", ".pf-shared"))).toBe(false);
    expect(readFileSync(path.join(ws, ".lake", "config", "tk", "lakefile.olean"), "utf8")).toBe("config\n");
    expect(readlinkSync(path.join(local, "ws", "r1", "Dep"))).toBe(path.join(dir, "top", "Dep"));
    expect(readlinkSync(path.join(local, "ws", "r1", "TC", "third"))).toBe(path.join(dir, "top", "TC", "third"));
    expect(existsSync(path.join(ws, "..", "..", "Dep", "Dep"))).toBe(true);
    expect(readFileSync(path.join(ws, ".pf-toolkit"), "utf8").split("\n")[0]).toBe(root);
    expect(JSON.parse(readFileSync(path.join(ws, ".pf-gen"), "utf8"))).toMatchObject({ gen: 1, slug: "r1", toolkit: root });
  }, 60_000);

  it("is idempotent, and re-pins to a newer generation keeping the workspace's own build", async () => {
    const ws = workspacePath(root, "r1", local);
    // again on the same generation: nothing re-pinned; an entry new in the shared tree is linked
    await put("NEW.md", "new\n");
    const again = await ensureWorkspace(root, "r1", { localRoot: local });
    expect(again).toMatchObject({ gen: 1, repinned: false });
    expect(readlinkSync(path.join(ws, "NEW.md"))).toBe(path.join(root, "NEW.md"));
    // the run built its paper in the workspace
    await put(".lake/build/lib/lean/Papers/P.olean", "P built in ws\n", ws);
    // a promotion lands: the shared tree's library and its outputs change (each output replaced, as Lake does)
    await put("Toolkit/A.lean", "-- A v2\n");
    for (const f of ["lib/lean/Toolkit/A.olean", "lib/lean/Toolkit/A.trace"]) {
      await unlink(path.join(root, ".lake", "build", f));
      await put(path.join(".lake", "build", f), `${f} v2\n`);
    }
    expect((await publishGeneration(root, "s2", quiet))?.gen).toBe(2);
    // not re-pinned until its safe point: the run sees generation 1 meanwhile
    expect(readFileSync(path.join(ws, "Toolkit", "A.lean"), "utf8")).toBe("-- Toolkit/A.lean\n");
    const r = await ensureWorkspace(root, "r1", { localRoot: local });
    expect(r).toMatchObject({ gen: 2, repinned: true });
    expect(readFileSync(path.join(ws, "Toolkit", "A.lean"), "utf8")).toBe("-- A v2\n");
    expect(readFileSync(path.join(ws, ".lake", "build", "lib/lean/Toolkit/A.olean"), "utf8")).toBe("lib/lean/Toolkit/A.olean v2\n");
    expect(readFileSync(path.join(ws, ".lake", "build", "lib/lean/Toolkit/A.trace"), "utf8")).toBe("lib/lean/Toolkit/A.trace v2\n");
    expect(readFileSync(path.join(ws, ".lake", "build", "lib/lean/Papers/P.olean"), "utf8")).toBe("P built in ws\n");
    expect(readlinkSync(path.join(ws, "Toolkit", "Staging"))).toBe(path.join(root, "Toolkit", "Staging"));
    // generation 1 on this machine is as it was
    expect(readFileSync(path.join(local, "gens", "1", ".lake", "build", "lib/lean/Toolkit/A.olean"), "utf8")).toBe("lib/lean/Toolkit/A.olean v1\n");
    expect(JSON.parse(readFileSync(path.join(ws, ".pf-gen"), "utf8")).gen).toBe(2);
  }, 60_000);

  it("re-pins a file that is already the generation's very file (one inode): left as it is, no staged name left", async () => {
    // (2026-11-11) `mv` refused the staged link onto itself: "… are the same file", and the run was kept on its generation
    const gen = path.join(dir, "same", "gens", "7");
    const ws = path.join(dir, "same", "ws");
    await put("CandidateScan.lean", "-- scan\n", gen);
    await put(".pf-complete", "", gen);
    await mkdir(path.join(ws, ".lake", "build"), { recursive: true });
    execFileSync("ln", [path.join(gen, "CandidateScan.lean"), path.join(ws, "CandidateScan.lean")]);
    execFileSync("bash", [SCRIPT, "pin", gen, ws, root, "Toolkit/Staging"], { stdio: "pipe" });
    expect(ino(path.join(ws, "CandidateScan.lean"))).toBe(ino(path.join(gen, "CandidateScan.lean")));
    expect((await readdir(ws)).filter((e) => e.startsWith(".pf-new."))).toEqual([]);
  });

  it("never pins or seeds a `.setup.json`, from a generation packed before they were left out too", async () => {
    // (2026-11-11) 60% of a generation, copied into every workspace; Lake writes one anew before each compile
    const gen = path.join(dir, "olds", "gens", "5");
    const ws = path.join(dir, "olds", "ws");
    const to = path.join(dir, "olds", "promo");
    for (const f of [".lake/build/ir/Toolkit.setup.json", ".lake/build/ir/Toolkit.c", ".lake/build/ir/Toolkit/A.setup.json", ".lake/build/ir/Toolkit/A.c", ".lake/build/ir/Toolkit/A.c.hash"]) await put(f, `${f}\n`, gen);
    await put(".pf-complete", "", gen);
    await mkdir(path.join(ws, ".lake", "build"), { recursive: true });
    execFileSync("bash", [SCRIPT, "pin", gen, ws, root, "Toolkit/Staging"], { stdio: "pipe" });
    const b = (base: string, rel: string) => path.join(base, ".lake", "build", rel);
    for (const f of ["ir/Toolkit.c", "ir/Toolkit/A.c", "ir/Toolkit/A.c.hash"]) expect(existsSync(b(ws, f)), f).toBe(true);
    for (const f of ["ir/Toolkit.setup.json", "ir/Toolkit/A.setup.json"]) {
      expect(existsSync(b(ws, f)), f).toBe(false);
      expect(existsSync(b(gen, f)), f).toBe(true);
    }
    // a run's own (Lake wrote them in its workspace): never seeded into another
    await put(".lake/build/ir/Papers/P/Main.setup.json", "setup\n", ws);
    await put(".lake/build/ir/Papers/P/Main.c", "c\n", ws);
    await put(".lake/build/ir/Papers/P.setup.json", "setup\n", ws);
    await mkdir(path.join(to, ".lake", "build"), { recursive: true });
    execFileSync("bash", [SCRIPT, "seed", ws, to, "ir/Papers/P", "ir/Papers/P.setup.json"], { stdio: "pipe" });
    expect(existsSync(b(to, "ir/Papers/P/Main.c"))).toBe(true);
    expect(existsSync(b(to, "ir/Papers/P/Main.setup.json"))).toBe(false);
    expect(existsSync(b(to, "ir/Papers/P.setup.json"))).toBe(false);
    expect(existsSync(b(ws, "ir/Papers/P/Main.setup.json"))).toBe(true);
  });

  it("unpacks a generation's unchanged files as links to the previous one's, never one that differs", async () => {
    // (2026-11-11) a workspace pinned to a pruned generation held the sole copy of every file, the exes too
    const at = path.join(dir, "dedupe");
    const gens = path.join(at, "gens");
    const pack = async (n: number, files: Record<string, string>) => {
      const src = path.join(at, `src${n}`);
      for (const [rel, text] of Object.entries(files)) await put(rel, text, src);
      execFileSync("bash", ["-c", `tar -c -C "$1" . | zstd -q -f -o "$2"`, "_", src, path.join(at, `${n}.tar.zst`)]);
    };
    const v1 = {
      "Toolkit/A.lean": "-- A\n", ".lake/build/lib/lean/Toolkit/A.olean": "olean A\n", ".lake/build/lib/lean/Toolkit/A.olean.hash": "1111",
      ".lake/build/lib/lean/Toolkit/B.olean": "olean B1\n", ".lake/build/lib/lean/Toolkit/B.olean.hash": "2222",
      ".lake/build/lib/lean/Toolkit/C.olean": "olean C1\n", ".lake/build/lib/lean/Toolkit/C.olean.hash": "3333",
      ".lake/build/bin/candidate_scan": "exe\n", ".lake/build/lib/lean/Toolkit/A.trace": "trace\n",
    };
    // B: other bytes of the same size behind a stale sidecar; C: other bytes and sidecar; D: new
    await pack(1, v1);
    await pack(2, { ...v1, ".lake/build/lib/lean/Toolkit/B.olean": "olean B2\n", ".lake/build/lib/lean/Toolkit/C.olean": "olean C2\n",
      ".lake/build/lib/lean/Toolkit/C.olean.hash": "4444", ".lake/build/lib/lean/Toolkit/D.olean": "olean D\n" });
    const unpack = (n: number, archive = n) => execFileSync("bash", [SCRIPT, "unpack", path.join(at, `${archive}.tar.zst`), path.join(gens, String(n))], { stdio: "pipe" });
    unpack(1);
    unpack(2);
    const g = (n: number, rel: string) => path.join(gens, String(n), rel);
    for (const rel of ["Toolkit/A.lean", ".lake/build/lib/lean/Toolkit/A.olean", ".lake/build/bin/candidate_scan"]) expect(ino(g(2, rel)), rel).toBe(ino(g(1, rel)));
    for (const rel of [".lake/build/lib/lean/Toolkit/B.olean", ".lake/build/lib/lean/Toolkit/C.olean", ".lake/build/lib/lean/Toolkit/A.trace", ".lake/build/lib/lean/Toolkit/A.olean.hash"]) {
      expect(ino(g(2, rel)), rel).not.toBe(ino(g(1, rel)));
    }
    expect(readFileSync(g(2, ".lake/build/lib/lean/Toolkit/B.olean"), "utf8")).toBe("olean B2\n");
    expect(readFileSync(g(2, ".lake/build/lib/lean/Toolkit/D.olean"), "utf8")).toBe("olean D\n");
    // still read-only, and whole once the generations before are pruned
    expect(statSync(g(2, ".lake/build/bin/candidate_scan")).mode & 0o222).toBe(0);
    for (const n of [3, 4, 5]) unpack(n, 2);
    expect((await readdir(gens)).filter((n) => /^\d+$/.test(n)).sort()).toEqual(["3", "4", "5"]);
    expect(ino(g(5, ".lake/build/bin/candidate_scan"))).toBe(ino(g(3, ".lake/build/bin/candidate_scan")));
    expect(statSync(g(5, ".lake/build/bin/candidate_scan")).nlink).toBe(3);
    expect(readFileSync(g(5, ".lake/build/lib/lean/Toolkit/A.olean"), "utf8")).toBe("olean A\n");
  });

  it("never lets a rebuild in the workspace reach the generation's files", async () => {
    const ws = workspacePath(root, "r1", local);
    const gen = path.join(local, "gens", "2", ".lake", "build");
    const b = path.join(ws, ".lake", "build");
    // which kinds are linked (the rest is copied)
    const linked = (n: string) => { try { execFileSync("bash", [SCRIPT, "linked", n]); return true; } catch { return false; } };
    for (const n of ["x/A.olean", "x/A.olean.server", "x/A.olean.private", "x/A.ilean", "x/A.ir", "x/A.c", "x/A.c.o.export", "x/A.lean", "b/bin/candidate_scan"]) expect(linked(n), n).toBe(true);
    for (const n of ["x/A.trace", "x/A.olean.hash", "x/A.setup.json", "b/bin/candidate_scan.rsp", "x/A.trace.nobuild", "x/A.log", "lakefile.toml", "lake-manifest.json"]) expect(linked(n), n).toBe(false);
    // an in-place write of a linked output fails (read-only): it could not reach the generation
    await expect(writeFile(path.join(b, "lib/lean/Toolkit/A.olean"), "in place")).rejects.toMatchObject({ code: "EACCES" });
    // what Lake writes in place is the workspace's own copy
    await writeFile(path.join(b, "lib/lean/Toolkit/A.trace"), "rebuilt in ws");
    await writeFile(path.join(b, "lib/lean/Toolkit/A.olean.hash"), "rebuilt in ws");
    // a rebuild replaces its outputs (unlink, then a new file): the generation's stay
    await unlink(path.join(b, "lib/lean/Toolkit/A.olean"));
    await writeFile(path.join(b, "lib/lean/Toolkit/A.olean"), "rebuilt in ws");
    expect(readFileSync(path.join(gen, "lib/lean/Toolkit/A.olean"), "utf8")).toBe("lib/lean/Toolkit/A.olean v2\n");
    expect(readFileSync(path.join(gen, "lib/lean/Toolkit/A.trace"), "utf8")).toBe("lib/lean/Toolkit/A.trace v2\n");
    expect(readFileSync(path.join(gen, "lib/lean/Toolkit/A.olean.hash"), "utf8")).toBe("lib/lean/Toolkit/A.olean.hash v1\n");
  }, 60_000);

  it("keeps the newest 3 generations, on the shared disk and on the machine", async () => {
    for (const s of ["s3", "s4", "s5"]) {
      await publishGeneration(root, s, quiet);
      await ensureWorkspace(root, "r1", { localRoot: local });
    }
    expect((await currentGeneration(root))?.gen).toBe(5);
    expect((await readdir(gensDir(root))).filter((n) => n.endsWith(".tar.zst")).sort()).toEqual(["3.tar.zst", "4.tar.zst", "5.tar.zst"]);
    expect((await readdir(path.join(local, "gens"))).filter((n) => /^\d+$/.test(n)).sort()).toEqual(["3", "4", "5"]);
    // the workspace holds its own links: an older generation's removal leaves it whole
    expect(readFileSync(path.join(workspacePath(root, "r1", local), "Toolkit", "A.lean"), "utf8")).toBe("-- A v2\n");
  }, 120_000);

  it("is off for a run opted out: nothing changes", async () => {
    await mkdir(path.join(root, "runs", "r1"), { recursive: true });
    await writeFile(path.join(root, "runs", "r1", "no-workspace"), "");
    try {
      expect(await enableRunWorkspace(root, "r1", quiet)).toBeNull();
    } finally {
      await unlink(path.join(root, "runs", "r1", "no-workspace"));
    }
    expect(process.env[LEAN_WS_ENV]).toBeUndefined();
    expect(leanWsChildEnv()).toEqual({});
    expect(leanWorkspaceFor(root)).toBeNull();
    // the shared tree's lock, recorded, as ever
    const before = (await readLockHolds(root)).length;
    await withLakeBuildLock(root, async () => {
      expect(existsSync(path.join(root, ".lake-build.lock.lock"))).toBe(true);
    }, "off path", quiet);
    expect((await readLockHolds(root)).length).toBe(before + 1);
    // a child's environment is the caller's
    const r = await spawnWithInactivityTimeout("bash", ["-c", 'echo "ws=${PAPERFORMALIZER_LEAN_WS-unset} path=$PATH"'], { cwd: root, env: process.env, inactivityTimeoutMs: 30_000 });
    expect(r.stdout).toContain("ws=unset");
    expect(r.stdout).not.toContain(LAKE_SHIM_DIR);
  }, 60_000);

  it("the run's lake calls go to its workspace, with no shared-tree lock; the promotion chain stays shared", async () => {
    await mkdir(path.join(root, "runs", "r1"), { recursive: true });
    // a run whose workspace cannot be made (its local root under a file) builds in the shared tree: never refused
    const savedLocal = process.env.PAPERFORMALIZER_LEAN_LOCAL_ROOT;
    await writeFile(path.join(dir, "not-a-dir"), "");
    process.env.PAPERFORMALIZER_LEAN_LOCAL_ROOT = path.join(dir, "not-a-dir", "local");
    try {
      process.env[LEAN_WS_ENV] = "/elsewhere/another-run";
      expect(await enableRunWorkspace(root, "r-none", quiet, async () => [])).toBeNull();
      expect(process.env[LEAN_WS_ENV]).toBeUndefined();
    } finally {
      if (savedLocal === undefined) delete process.env.PAPERFORMALIZER_LEAN_LOCAL_ROOT;
      else process.env.PAPERFORMALIZER_LEAN_LOCAL_ROOT = savedLocal;
    }
    // the workspace lacks something of the run's own: the start waits, then the shared tree
    const saved = { ...WORKSPACE_TIMING };
    Object.assign(WORKSPACE_TIMING, { lagWaitMs: 50, lagPollMs: 10 });
    let looks = 0;
    try {
      expect(await enableRunWorkspace(root, "r1", quiet, async () => (looks++, ["Toolkit.A.x"]))).toBeNull();
      expect(looks).toBeGreaterThan(1);
      // caught up while it waits: the workspace
      looks = 0;
      Object.assign(WORKSPACE_TIMING, { lagWaitMs: 60_000 });
      expect(await enableRunWorkspace(root, "r1", quiet, async () => (++looks > 2 ? [] : ["Toolkit.A.x"]))).toBe(workspacePath(root, "r1", local));
    } finally {
      Object.assign(WORKSPACE_TIMING, saved);
    }
    // an inherited workspace (another run's) is never kept: opted out, this run has none
    await writeFile(path.join(root, "runs", "r1", "no-workspace"), "");
    expect(await enableRunWorkspace(root, "r1", quiet, async () => [])).toBeNull();
    expect(process.env[LEAN_WS_ENV]).toBeUndefined();
    await unlink(path.join(root, "runs", "r1", "no-workspace"));
    // the real check: the run's own declaration, in the shared Toolkit but not in the generation, is waited for;
    // another run's, or one the shared Toolkit no longer declares, is not
    const sharedA = readFileSync(path.join(root, "Toolkit", "A.lean"), "utf8");
    await mkdir(path.join(root, "doc"), { recursive: true });
    await writeFile(path.join(root, "doc", "ledger.json"), JSON.stringify({ declarations: [
      { name: "Toolkit.A.ownNew", module: "Toolkit.A", origin: { kind: "proposal", slug: "r1" } },
      { name: "Toolkit.A.usedNew", module: "Toolkit.A", origin: { kind: "proposal", slug: "r3" }, used_by: ["r1"] },
      { name: "Toolkit.A.otherNew", module: "Toolkit.A", origin: { kind: "proposal", slug: "r2" } },
      { name: "Toolkit.Gone.retired", module: "Toolkit.Gone", origin: { kind: "proposal", slug: "r1" } },
    ] }));
    const saved2 = { ...WORKSPACE_TIMING };
    Object.assign(WORKSPACE_TIMING, { lagWaitMs: 50, lagPollMs: 10 });
    try {
      await writeFile(path.join(root, "Toolkit", "A.lean"), `${sharedA}theorem ownNew : True := trivial\ntheorem otherNew : True := trivial\n`);
      expect(await enableRunWorkspace(root, "r1", quiet)).toBeNull();
      // declared dotted (`theorem A.ownNew`): still found, still waited for
      await writeFile(path.join(root, "Toolkit", "A.lean"), `${sharedA}theorem A.ownNew : True := trivial\n`);
      expect(await enableRunWorkspace(root, "r1", quiet)).toBeNull();
      // only another run's is new: the lagging generation serves
      await writeFile(path.join(root, "Toolkit", "A.lean"), `${sharedA}theorem otherNew : True := trivial\ntheorem ownNewer : True := trivial\n`);
      expect(await enableRunWorkspace(root, "r1", quiet)).toBe(workspacePath(root, "r1", local));
      // another run's move that this run's paper now uses (`used_by`): waited for
      await writeFile(path.join(root, "Toolkit", "A.lean"), `${sharedA}theorem usedNew : True := trivial\n`);
      expect(await enableRunWorkspace(root, "r1", quiet)).toBeNull();
    } finally {
      Object.assign(WORKSPACE_TIMING, saved2);
      await writeFile(path.join(root, "Toolkit", "A.lean"), sharedA);
      await rm(path.join(root, "doc", "ledger.json"), { force: true });
    }
    const ws = await enableRunWorkspace(root, "r1", quiet, async () => []);
    expect(ws).toBe(workspacePath(root, "r1", local));
    expect(process.env[LEAN_WS_ENV]).toBe(ws);
    expect(leanWorkspaceFor(root)).toBe(ws);
    // another toolkit's lock is not the workspace's
    expect(leanWorkspaceFor(dir)).toBeNull();
    const env = leanWsChildEnv();
    expect(env[LEAN_WS_ENV]).toBe(ws);
    expect(env.PATH!.split(":")[0]).toBe(LAKE_SHIM_DIR);
    // a fake real lake behind the shim: where it ran, and whether the workspace's lock was held
    const bin = path.join(dir, "fakebin");
    await mkdir(bin, { recursive: true });
    const log = path.join(dir, "fake-lake.log");
    await writeFile(path.join(bin, "lake"), `#!/usr/bin/env bash\nif ! flock -n "$PAPERFORMALIZER_LEAN_WS/.lake/build.lock" true 2>/dev/null; then l=wslocked; else l=wsfree; fi\necho "$l $PWD $*" >> ${JSON.stringify(log)}\n`);
    await chmod(path.join(bin, "lake"), 0o755);
    const savedPath = process.env.PATH;
    process.env.PATH = [bin, path.dirname(process.execPath), "/usr/bin", "/bin"].join(":");
    try {
      const lakeHolds = async () => (await readLockHolds(root)).filter((h) => h.lock === "lake").length;
      const holds = await lakeHolds();
      await rm(path.join(root, ".lake-build.lock"), { force: true });
      // stamped clean (a build in the workspace holds off otherwise: the lake shim)
      await put(".lake/paperformalizer/toolkit-clean.json", '{"sig":"s","ok":true}\n');
      // the pipeline's own call, as its stages make it: the lock helper, then lake in the toolkit
      await withLakeBuildLock(root, async () => {
        expect(existsSync(path.join(root, ".lake-build.lock.lock"))).toBe(false);
        const r = await spawnWithInactivityTimeout("lake", ["build", "Papers.P"], { cwd: root, env: process.env, inactivityTimeoutMs: 60_000 });
        expect(r.exitCode).toBe(0);
      }, "lean evidence: lake build Papers.P", quiet, undefined, { papers: ["Papers.P"] });
      expect((await readFile(log, "utf8")).trim().split("\n").at(-1)).toBe(`wslocked ${ws} build Papers.P`);
      expect(await lakeHolds()).toBe(holds);
      expect(existsSync(path.join(root, ".lake-build.lock"))).toBe(false);
      // inside the promotion lock: the shared tree, its lock, the workspace cleared for children
      await withPromotionLock(root, async () => {
        expect(leanWorkspaceFor(root)).toBeNull();
        expect(leanWsChildEnv()).toEqual({ [LEAN_WS_ENV]: "" });
        await withLakeBuildLock(root, async () => {
          expect(existsSync(path.join(root, ".lake-build.lock.lock"))).toBe(true);
        }, "promotion gate", quiet);
      }, undefined, quiet);
      expect(await lakeHolds()).toBe(holds + 1);
      // a promotion round's apply, outside the promotion lock: the shared tree's too
      await withSharedTree(async () => {
        expect(leanWorkspaceFor(root)).toBeNull();
        expect(leanWsChildEnv()).toEqual({ [LEAN_WS_ENV]: "" });
      });
      expect(leanWorkspaceFor(root)).toBe(ws);
    } finally {
      process.env.PATH = savedPath;
    }
  }, 120_000);

  it("keeps a workspace's green builds and scans under its generation: never the shared tree's, never past a re-pin", async () => {
    const ws = workspacePath(root, "r1", local);
    const leanDir = path.join(root, "Papers");
    const out = path.join(root, ".lake", "build", "paperformalizer", "scan.json");
    await put(".lake/build/paperformalizer/scan.json", "{}\n");
    const pinFile = path.join(ws, ".pf-gen");
    const pin = readFileSync(pinFile, "utf8");
    try {
      process.env[LEAN_WS_ENV] = ws;
      await recordGreenBuild(root, leanDir, ["Papers.P"], "S");
      await recordScan(out, { sig: "S", modules: ["Papers.P"] });
      expect(await greenBuildCurrent(root, leanDir, ["Papers.P"], "S")).toBe(true);
      expect(await scanCurrent(out, ["Papers.P"], "S")).toBe(true);
      // the shared tree's reader: built against another toolkit
      delete process.env[LEAN_WS_ENV];
      expect(await greenBuildCurrent(root, leanDir, ["Papers.P"], "S")).toBe(false);
      expect(await scanCurrent(out, ["Papers.P"], "S")).toBe(false);
      // and the workspace never takes the shared tree's record for its own
      await recordGreenBuild(root, leanDir, ["Papers.P"], "S2");
      process.env[LEAN_WS_ENV] = ws;
      expect(await greenBuildCurrent(root, leanDir, ["Papers.P"], "S2")).toBe(false);
      // inside the promotion lock the record is the shared tree's
      await withPromotionLock(root, async () => {
        expect(await greenBuildCurrent(root, leanDir, ["Papers.P"], "S2")).toBe(true);
      }, undefined, quiet);
      // re-pinned: its records from before are not current
      await recordGreenBuild(root, leanDir, ["Papers.P"], "S3");
      expect(await greenBuildCurrent(root, leanDir, ["Papers.P"], "S3")).toBe(true);
      await writeFile(pinFile, JSON.stringify({ ...JSON.parse(pin), gen: 99 }));
      expect(await greenBuildCurrent(root, leanDir, ["Papers.P"], "S3")).toBe(false);
    } finally {
      await writeFile(pinFile, pin);
    }
  }, 60_000);

  it("publishes from a process of its own, one at a time, only a toolkit that is clean as it stands", async () => {
    const tk = path.join(dir, "pubtk");
    await put("paperformalizer.json", JSON.stringify(TOOLKIT_JSON), tk);
    await put("lakefile.toml", 'name = "pubtk"\n', tk);
    // generations off: no publisher
    spawnPublisher(tk, "s", quiet);
    expect(existsSync(gensDir(tk))).toBe(false);
    await mkdir(gensDir(tk), { recursive: true });
    const logFile = path.join(gensDir(tk), "publish.log");
    const logged = () => (existsSync(logFile) ? readFileSync(logFile, "utf8") : "");
    // another publisher running: this one does not start
    const holder = execFile("flock", [path.join(gensDir(tk), ".publish.lock"), "sleep", "4"]);
    await new Promise((r) => setTimeout(r, 500));
    spawnPublisher(tk, "s", quiet);
    await new Promise((r) => holder.on("exit", r));
    await new Promise((r) => setTimeout(r, 500));
    expect(logged()).toBe("");
    // not stamped clean: nothing published
    spawnPublisher(tk, "s", quiet);
    for (let i = 0; i < 1200 && !/current generation/.test(logged()); i++) await new Promise((r) => setTimeout(r, 100));
    expect(logged()).toMatch(/not stamped clean[\s\S]*current generation: none/);
    expect(await currentGeneration(tk)).toBeNull();
  }, 180_000);

  it("drops a restarted run's release marker, and sweeps the machine's released runs once per process, never the one ensured", async () => {
    await put("runs/r1/logs/workspace_released.json", "{}");
    await put("runs/gone1/state.json", JSON.stringify({ verify: { phase: "done" } }));
    await put("runs/gone1/logs/workspace_released.json", "{}");
    await mkdir(path.join(local, "ws", "gone1.promo", "TC", "tk"), { recursive: true });
    WORKSPACE_SWEEP.done = false;
    const said: string[] = [];
    const r = await ensureWorkspace(root, "r1", { localRoot: local, log: (l) => said.push(l) });
    expect(existsSync(path.join(root, "runs", "r1", "logs", "workspace_released.json"))).toBe(false);
    expect(said.join("\n")).toContain("r1: live again");
    expect(existsSync(path.join(local, "ws", "gone1.promo"))).toBe(false);
    expect(existsSync(r.path)).toBe(true);
    // once per process: a run released later stays until the next process's sweep
    await mkdir(path.join(local, "ws", "gone1", "TC", "tk"), { recursive: true });
    await ensureWorkspace(root, "r1", { localRoot: local });
    expect(existsSync(path.join(local, "ws", "gone1"))).toBe(true);
    // (a promotion's ensure is the run's: its marker goes too)
    await put("runs/gone1/logs/workspace_released.json", "{}");
    await ensureWorkspace(root, "gone1.promo", { localRoot: local });
    expect(existsSync(path.join(root, "runs", "gone1", "logs", "workspace_released.json"))).toBe(false);
  }, 60_000);
});

// The hard-link assumptions against Lake itself, when a toolchain is at hand (`lake` on PATH):
// a workspace on a generation is up to date as it stands, and a rebuild in it leaves the
// generation's files byte for byte as they were.
const haveLake = (() => { try { execFileSync("lake", ["--version"], { timeout: 60_000, stdio: "ignore" }); return haveTools; } catch { return false; } })();
describe.skipIf(process.platform === "win32" || !haveLake)("lean workspaces with Lake", () => {
  it("builds nothing on a fresh workspace, and a rebuild there leaves the generation intact", async () => {
    const top = await mkdtemp(path.join(os.tmpdir(), "lean-ws-lake-"));
    try {
      const tk = path.join(top, "TC", "tk");
      await put("lakefile.toml", 'name = "tk"\ndefaultTargets = ["Toolkit"]\n[[lean_lib]]\nname = "Toolkit"\n[[lean_lib]]\nname = "Papers"\n', tk);
      await put("lean-toolchain", `${readFileSync(path.join(root, "lean-toolchain"), "utf8")}`, tk);
      await put("Toolkit.lean", "import Toolkit.A\n", tk);
      await put("Toolkit/A.lean", "def a : Nat := 1\n", tk);
      await put("Papers.lean", "import Papers.P\n", tk);
      await put("Papers/P.lean", "import Toolkit.A\ntheorem p : a = 1 := rfl\n", tk);
      const lake = (cwd: string, ...args: string[]) => new Promise<{ code: number; out: string }>((resolve) => {
        execFile("lake", args, { cwd, timeout: 600_000 }, (err, so, se) => resolve({ code: err ? (typeof err.code === "number" ? err.code : 1) : 0, out: `${so}${se}` }));
      });
      expect((await lake(tk, "build", "Toolkit")).code).toBe(0);
      await mkdir(gensDir(tk), { recursive: true });
      await publishGeneration(tk, "lake-s1", quiet);
      const loc = path.join(top, "local");
      const { path: ws } = await ensureWorkspace(tk, "lk", { localRoot: loc });
      const nob = await lake(ws, "build", "--no-build", "Toolkit");
      expect(nob.code, nob.out).toBe(0);
      const gen = path.join(loc, "gens", "1", ".lake", "build");
      const sums = () => execFileSync("bash", ["-c", `cd "$1" && find . -type f -print0 | sort -z | xargs -0 sha256sum`, "_", gen], { encoding: "utf8" });
      const before = sums();
      // the paper built in the workspace; then the library rebuilt there (its trace made stale)
      expect((await lake(ws, "build", "Papers.P")).code).toBe(0);
      await writeFile(path.join(ws, ".lake", "build", "lib", "lean", "Toolkit", "A.trace"), "{}");
      const rebuilt = await lake(ws, "build", "Toolkit");
      expect(rebuilt.code, rebuilt.out).toBe(0);
      expect(ino(path.join(ws, ".lake", "build", "lib", "lean", "Toolkit", "A.olean"))).not.toBe(ino(path.join(gen, "lib", "lean", "Toolkit", "A.olean")));
      expect(sums()).toBe(before);
      expect(existsSync(path.join(tk, ".lake", "build", "lib", "lean", "Papers"))).toBe(false);
    } finally {
      await rm(top, { recursive: true, force: true });
    }
  }, 900_000);

  // The audit's probes P2–P5: a path dependency, the module system and an exe, against real Lake.
  it("never rebuilds a shared path dependency, never keeps a green record across generations, and catches up by re-pinning", async () => {
    const top = await mkdtemp(path.join(os.tmpdir(), "lean-ws-probe-"));
    try {
      const tk = path.join(top, "TC", "tk");
      const dep = path.join(top, "Dep");
      const tc = readFileSync(path.join(root, "lean-toolchain"), "utf8");
      await put("lakefile.toml", 'name = "Dep"\n[[lean_lib]]\nname = "Dep"\n', dep);
      await put("lean-toolchain", tc, dep);
      await put("Dep.lean", "module\npublic def d : Nat := 1\n", dep);
      await put("lakefile.toml", 'name = "tk"\ndefaultTargets = ["Toolkit"]\n[[require]]\nname = "Dep"\npath = "../../Dep"\n' +
        '[[lean_lib]]\nname = "Toolkit"\nrequiresModuleSystem = true\n[[lean_lib]]\nname = "Papers"\nrequiresModuleSystem = true\n[[lean_exe]]\nname = "candidate_scan"\nroot = "CandidateScan"\n', tk);
      await put("lean-toolchain", tc, tk);
      await put("Toolkit.lean", "module\npublic import Toolkit.A\n", tk);
      await put("Toolkit/A.lean", "module\npublic import Dep\npublic def a : Nat := d\n", tk);
      await put("CandidateScan.lean", "import Toolkit\ndef main : IO Unit := IO.println s!\"{a}\"\n", tk);
      await put("Papers.lean", "module\npublic import Papers.P\n", tk);
      await put("Papers/P.lean", "module\npublic import Toolkit.A\npublic def p : Nat := a\n", tk);
      const stamp = (ok: boolean) => put(".lake/paperformalizer/toolkit-clean.json", ok ? '{"sig":"s","ok":true}\n' : '{"sig":"flux","ok":false,"why":"in flux"}\n', tk);
      const env0 = { ...process.env };
      delete env0.PAPERFORMALIZER_LAKE_LOCK_HELD;
      delete env0[LEAN_WS_ENV];
      const lake = (cwd: string, args: string[], env: NodeJS.ProcessEnv = env0) => new Promise<{ code: number; out: string }>((resolve) => {
        execFile("lake", args, { cwd, env, timeout: 900_000 }, (err, so, se) => resolve({ code: err ? (typeof err.code === "number" ? err.code : 1) : 0, out: `${so}${se}` }));
      });
      const b = await lake(tk, ["build", "Toolkit", "candidate_scan"]);
      expect(b.code, b.out).toBe(0);
      await stamp(true);
      await mkdir(gensDir(tk), { recursive: true });
      await publishGeneration(tk, "sig-1", quiet);
      const loc = path.join(top, "local");
      const { path: ws } = await ensureWorkspace(tk, "pr", { localRoot: loc });
      const shimEnv = { ...env0, [LEAN_WS_ENV]: ws, PATH: `${LAKE_SHIM_DIR}:${env0.PATH}`, PAPERFORMALIZER_LAKE_FLUX_WAIT_S: "1", PAPERFORMALIZER_LAKE_FLUX_WAIT_MAX_S: "2" };
      const gen = path.join(loc, "gens", "1", ".lake", "build");
      const sums = () => execFileSync("bash", ["-c", `cd "$1" && find . -type f -print0 | sort -z | xargs -0 sha256sum`, "_", gen], { encoding: "utf8" });
      const before = sums();
      // P1: up to date in the workspace (the module system and an exe)
      const nob = await lake(ws, ["build", "--no-build", "Toolkit", "candidate_scan"]);
      expect(nob.code, nob.out).toBe(0);
      // P3: the exe relinked and a library module rebuilt in the workspace: the generation unchanged
      await writeFile(path.join(ws, ".lake", "build", "bin", "candidate_scan.trace"), "{}");
      await writeFile(path.join(ws, ".lake", "build", "lib", "lean", "Toolkit", "A.trace"), "{}");
      const rb = await lake(ws, ["build", "Toolkit", "candidate_scan"]);
      expect(rb.code, rb.out).toBe(0);
      expect(sums()).toBe(before);
      // P2: a path dependency changed in a flux session: a build in the workspace holds off and
      // then does not build — the shared dependency's build is never written from the workspace
      const depOlean = path.join(dep, ".lake", "build", "lib", "lean", "Dep.olean");
      const st = (p: string) => { const x = statSync(p); return `${x.ino}:${x.mtimeMs}`; };
      const depBefore = st(depOlean);
      await put(".lake/paperformalizer/toolkit-flux", "{}", tk);
      await stamp(false);
      await put("Dep.lean", "module\npublic def d : Nat := 1\npublic def d2 : Nat := 2\n", dep);
      expect((await lake(tk, ["build", "Papers.P"], shimEnv)).code).toBe(75);
      expect(st(depOlean)).toBe(depBefore);
      expect((await readLockHolds(tk)).filter((h) => h.lock === "lake")).toEqual([]);
      // the flux session closed: the toolkit (its dependency with it) built clean in the shared tree
      await rm(path.join(tk, ".lake", "paperformalizer", "toolkit-flux"));
      expect((await lake(tk, ["build", "Toolkit"])).code).toBe(0);
      await stamp(true);
      // P4: the workspace lags the shared toolkit (a promotion landed mid-stage): its green record
      // is of its generation, so after the re-pin it vouches for nothing
      const cfg = { toolkitRoot: tk, toolkitLibDir: path.join(tk, "Toolkit") };
      const leanDir = path.join(tk, "Papers");
      await put("Toolkit/A.lean", "module\npublic import Dep\npublic def a2 : Nat := d\n", tk);
      await put("CandidateScan.lean", "import Toolkit\ndef main : IO Unit := IO.println s!\"{a2}\"\n", tk);
      const sigLag = await sourceSignature(cfg, leanDir);
      const w1 = await lake(tk, ["build", "Papers.P"], shimEnv);
      expect(w1.code, w1.out).toBe(0);
      process.env[LEAN_WS_ENV] = ws;
      await recordGreenBuild(tk, leanDir, ["Papers.P"], sigLag);
      expect(await greenBuildCurrent(tk, leanDir, ["Papers.P"], sigLag)).toBe(true);
      delete process.env[LEAN_WS_ENV];
      expect(await greenBuildCurrent(tk, leanDir, ["Papers.P"], sigLag)).toBe(false);
      expect((await lake(tk, ["build", "Toolkit"])).code).toBe(0);
      await publishGeneration(tk, "sig-2", quiet);
      await ensureWorkspace(tk, "pr", { localRoot: loc });
      const sigNow = await sourceSignature(cfg, leanDir);
      expect(sigNow).toBe(sigLag);
      process.env[LEAN_WS_ENV] = ws;
      expect(await greenBuildCurrent(tk, leanDir, ["Papers.P"], sigNow)).toBe(false);
      delete process.env[LEAN_WS_ENV];
      expect((await lake(tk, ["build", "Papers.P"], shimEnv)).code).not.toBe(0);
      expect((await lake(tk, ["build", "Papers.P"])).code).not.toBe(0);
      // P5: a paper edit that needs a newer toolkit fails in the lagging workspace; its re-pin fixes it
      await put("Toolkit/A.lean", "module\npublic import Dep\npublic def a2 : Nat := d\npublic def b : Nat := d\n", tk);
      expect((await lake(tk, ["build", "Toolkit"])).code).toBe(0);
      await publishGeneration(tk, "sig-3", quiet);
      await put("Papers/P.lean", "module\npublic import Toolkit.A\npublic def p : Nat := b\n", tk);
      expect((await lake(tk, ["build", "Papers.P"], shimEnv)).code).not.toBe(0);
      expect((await lake(tk, ["build", "Papers.P"])).code).toBe(0);
      await ensureWorkspace(tk, "pr", { localRoot: loc });
      const w3 = await lake(tk, ["build", "Papers.P"], shimEnv);
      expect(w3.code, w3.out).toBe(0);
    } finally {
      delete process.env[LEAN_WS_ENV];
      await rm(top, { recursive: true, force: true });
    }
  }, 1_800_000);
});
