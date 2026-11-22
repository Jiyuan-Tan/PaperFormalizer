// Workspaces on by default: a toolkit with no generations gets shared mode, a clean build and its
// first generation at a run's start (where the machine can have workspaces), its workspace under the
// toolkit's own disk when no local root is set; a run done for good leaves none behind.
import { createHash } from "node:crypto";
import { execFileSync } from "node:child_process";
import { existsSync, readFileSync } from "node:fs";
import { chmod, mkdir, mkdtemp, readdir, readFile, rm, unlink, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { LAKE_LOCK_CLEAN_BUILD, LEAN_WS_ENV, lakeCleanStampFile } from "../../src/shared/build_mutex.js";
import { toolkitLayout, toolkitSignature } from "../../src/shared/build_inputs.js";
import { withRunHeartbeat } from "../../src/shared/run_heartbeat.js";
import { GENERATION_TIMING, currentGeneration, markKnowsShared, enableRunWorkspace, ensureGenerations, gensDir, localLeanRoot, releasedMarker, workspacePath, workspacesUnsupported } from "../../src/shared/workspace.js";
import { releaseDoneRun } from "../../src/verify/cli.js";
import { TOOLKIT_JSON } from "../toolkit/helpers.js";

const haveTools = (() => { try { execFileSync("bash", ["-c", "command -v zstd && command -v flock && command -v tar"]); return true; } catch { return false; } })();
const sha = (s: string | Buffer) => createHash("sha256").update(s).digest("hex");
const quiet = () => {};

let dir: string;
let root: string;
let PATH: string | undefined;
const realClean = LAKE_LOCK_CLEAN_BUILD.run;
const timing = { ...GENERATION_TIMING };
const put = async (rel: string, text: string, base = root) => {
  await mkdir(path.dirname(path.join(base, rel)), { recursive: true });
  await writeFile(path.join(base, rel), text);
};
/** A stand-in `lake build`: each library module's `.olean`, `.olean.hash` and `.trace` named by its source. */
async function build(cwd: string): Promise<void> {
  const mods = ["Toolkit.lean", "CandidateScan.lean", ...(await readdir(path.join(cwd, "Toolkit"))).map((f) => path.join("Toolkit", f))].filter((f) => f.endsWith(".lean"));
  for (const m of mods) {
    const s = sha(await readFile(path.join(cwd, m)));
    const base = path.join(".lake", "build", "lib", "lean", m.slice(0, -".lean".length));
    await put(`${base}.olean`, `olean ${s}`, cwd);
    await put(`${base}.olean.hash`, sha(`olean ${s}`), cwd);
    await put(`${base}.trace`, s, cwd);
  }
}

beforeAll(async () => {
  dir = await mkdtemp(path.join(os.tmpdir(), "ws-default-"));
  root = path.join(dir, "top", "tk");
  await put("paperformalizer.json", JSON.stringify(TOOLKIT_JSON));
  await put("lakefile.toml", 'name = "tk"\n[[lean_lib]]\nname = "Toolkit"\n[[lean_lib]]\nname = "Papers"\n[[lean_exe]]\nname = "candidate_scan"\nroot = "CandidateScan"\n');
  await put("lean-toolchain", "leanprover/lean4:v4.33.0\n");
  await put("lake-manifest.json", "{}\n");
  await put("Toolkit.lean", "module\npublic import Toolkit.A\n");
  await put("Toolkit/A.lean", "-- A v1\n");
  await put("CandidateScan.lean", "-- scan\n");
  await put("Papers.lean", "-- papers\n");
  await put("doc/ledger.json", JSON.stringify({ version: 1, declarations: [], decisions: [] }));
  await mkdir(path.join(root, "runs"), { recursive: true });
  await mkdir(path.join(root, ".lake", "packages"), { recursive: true });
  // a `lean` that answers `--version` (the signature names the toolchain); the publisher's process inherits it
  await put("bin/lean", "#!/bin/sh\necho 'Lean (version 4.0.0, test)'\n", dir);
  await chmod(path.join(dir, "bin", "lean"), 0o755);
  PATH = process.env.PATH;
  process.env.PATH = `${path.join(dir, "bin")}:${PATH}`;
  delete process.env.PAPERFORMALIZER_LEAN_LOCAL_ROOT;
  LAKE_LOCK_CLEAN_BUILD.run = async (cwd) => { await build(cwd); return { ok: true, log: "" }; };
});
afterAll(async () => {
  process.env.PATH = PATH;
  Object.assign(GENERATION_TIMING, timing);
  LAKE_LOCK_CLEAN_BUILD.run = realClean;
  delete process.env[LEAN_WS_ENV];
  await rm(dir, { recursive: true, force: true });
});

describe("workspaces by default", () => {
  it("are refused where they cannot be made, saying why", async () => {
    process.env.PAPERFORMALIZER_WORKSPACES = "off";
    try {
      expect(workspacesUnsupported()).toMatch(/PAPERFORMALIZER_WORKSPACES is off/);
      expect(await ensureGenerations(root, quiet)).toEqual({ why: expect.stringMatching(/off/) });
      // nothing turned on
      expect(existsSync(gensDir(root))).toBe(false);
      expect(existsSync(path.join(root, ".lake", "paperformalizer", "lake-shared-mode"))).toBe(false);
    } finally {
      delete process.env.PAPERFORMALIZER_WORKSPACES;
    }
    const saved = process.env.PATH;
    process.env.PATH = path.join(dir, "bin");
    try {
      expect(workspacesUnsupported()).toMatch(/flock, zstd, tar not found on the PATH/);
    } finally {
      process.env.PATH = saved;
    }
  });

  it("puts the machine's local root on the toolkit's own disk when none is set", () => {
    expect(localLeanRoot(root)).toBe(path.join(root, ".lake", "paperformalizer", "local"));
  });

  it.skipIf(process.platform === "win32" || !haveTools)("leaves shared builds off while a run of older code is live, and a failed clean build is not tried again", async () => {
    const mode = path.join(root, ".lake", "paperformalizer", "lake-shared-mode");
    // a live run that never marked it knows shared holds: nothing turned on
    await mkdir(path.join(root, "runs", "old", "logs"), { recursive: true });
    await withRunHeartbeat(root, "old", async () => {
      expect(await ensureGenerations(root, quiet)).toEqual({ why: expect.stringMatching(/older code is live \(old\)/) });
      expect(existsSync(mode)).toBe(false);
    });
    // the toolkit's clean build failed for these very sources: refused at once, nothing built
    const stampFile = lakeCleanStampFile(path.join(root, ".lake-build.lock"));
    await mkdir(path.dirname(stampFile), { recursive: true });
    await writeFile(stampFile, JSON.stringify({ sig: await toolkitSignature(await toolkitLayout(root)), ok: false, why: "`lake build Toolkit` failed: error", at: "" }));
    let built = 0;
    LAKE_LOCK_CLEAN_BUILD.run = async (cwd) => { built++; await build(cwd); return { ok: true, log: "" }; };
    try {
      expect(await ensureGenerations(root, quiet)).toEqual({ why: expect.stringMatching(/clean build failed for its sources as they stand/) });
      expect(built).toBe(0);
    } finally {
      await unlink(stampFile);
      await rm(mode, { force: true });
      await rm(gensDir(root), { recursive: true, force: true });
      LAKE_LOCK_CLEAN_BUILD.run = async (cwd) => { await build(cwd); return { ok: true, log: "" }; };
    }
  }, 60_000);

  it.skipIf(process.platform === "win32" || !haveTools)("turns a fresh toolkit's generations on at a run's start, and a run done for good leaves no workspace", async () => {
    Object.assign(GENERATION_TIMING, { pollMs: 200 });
    await put("runs/r1/state.json", JSON.stringify({ verify: { phase: "formalization" } }));
    // beside a live run of this code (marked): turned on all the same
    const ws = await withRunHeartbeat(root, "old", async () => {
      await markKnowsShared(root, "old");
      return enableRunWorkspace(root, "r1", quiet, async () => []);
    });
    expect(existsSync(path.join(root, ".lake", "paperformalizer", "lake-shared-mode"))).toBe(true);
    expect((await currentGeneration(root))?.gen).toBe(1);
    expect(ws).toBe(workspacePath(root, "r1", path.join(root, ".lake", "paperformalizer", "local")));
    expect(readFileSync(path.join(ws!, "Toolkit", "A.lean"), "utf8")).toBe("-- A v1\n");
    // already on: the same generation, nothing built again
    let built = 0;
    LAKE_LOCK_CLEAN_BUILD.run = async (cwd) => { built++; await build(cwd); return { ok: true, log: "" }; };
    expect((await ensureGenerations(root, quiet)) as { gen: number }).toMatchObject({ gen: 1 });
    expect(built).toBe(0);
    // a switch off turns workspaces off again, generation or not
    process.env.PAPERFORMALIZER_WORKSPACES = "off";
    try {
      expect(await ensureGenerations(root, quiet)).toEqual({ why: expect.stringMatching(/off/) });
      expect(await enableRunWorkspace(root, "r1", quiet, async () => [])).toBeNull();
      expect(process.env[LEAN_WS_ENV]).toBeUndefined();
      // a scan only reads: with no workspace, the shared tree (never a refusal)
      const { withScanRoot } = await import("../../src/proposals/candidate_scan.js");
      const { loadToolkitConfig } = await import("../../src/toolkit/config.js");
      expect(await withScanRoot(loadToolkitConfig({ explicit: root }), "r1", [], quiet, undefined, async (at) => at)).toBeNull();
      // a promotion is refused, saying why
      const { prepareWorkspace } = await import("../../src/shared/commit.js");
      await expect(prepareWorkspace(root, "r1", [])).rejects.toThrow(/moving results into the shared library needs per-run Lean workspaces[^]*PAPERFORMALIZER_WORKSPACES is off/);
    } finally {
      delete process.env.PAPERFORMALIZER_WORKSPACES;
    }
    // not done: kept; done: released and removed, its marker written (not under a batch job: its driver releases)
    delete process.env[LEAN_WS_ENV];
    const batch = { job: process.env.PAPERFORMALIZER_BATCH_JOB, slurm: process.env.SLURM_JOB_ID };
    delete process.env.PAPERFORMALIZER_BATCH_JOB;
    delete process.env.SLURM_JOB_ID;
    await releaseDoneRun(root, "r1");
    expect(existsSync(ws!)).toBe(true);
    await put("runs/r1/state.json", JSON.stringify({ verify: { phase: "done" } }));
    await releaseDoneRun(root, "r1");
    expect(existsSync(releasedMarker(root, "r1"))).toBe(true);
    for (let i = 0; i < 50 && existsSync(path.dirname(path.dirname(ws!))); i++) await new Promise((r) => setTimeout(r, 100));
    expect(existsSync(path.join(root, ".lake", "paperformalizer", "local", "ws", "r1"))).toBe(false);
    await unlink(releasedMarker(root, "r1"));
    if (batch.job !== undefined) process.env.PAPERFORMALIZER_BATCH_JOB = batch.job;
    if (batch.slurm !== undefined) process.env.SLURM_JOB_ID = batch.slurm;
  }, 180_000);
});
