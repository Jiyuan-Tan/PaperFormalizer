// Promotions prepared in a private workspace and committed briefly (`src/shared/commit.ts`): what a
// prepared commit holds, a commit that lands, a base that moved, a tree that is not its generation,
// Lake's verdict (the slow path, the stopped line and its undo), and the roll-forward of a commit
// interrupted at each step. Lake is a stand-in that judges by the sources' bytes, as Lake does.
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, lstatSync, readdirSync, readFileSync, statSync } from "node:fs";
import { chmod, mkdir, mkdtemp, readdir, readFile, rm, unlink, utimes, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterAll, beforeAll, beforeEach, describe, expect, it } from "vitest";
import { LAKE_LOCK_CLEAN_BUILD, openFluxSession, recordToolkitClean, stampedClean, stampToolkitClean, toolkitFluxOff, toolkitFluxOn, toolkitFluxWhy, withinCommit, withLakeBuildLock, withPromotionLock, withToolkitFlux } from "../../src/shared/build_mutex.js";
import { appendLedgerDeclarations } from "../../src/toolkit/ledger.js";
import { toolkitLayout, toolkitScope, toolkitSignature } from "../../src/shared/build_inputs.js";
import {
  clearCommit, COMMIT_LAKE, commitOnFile, dropArchive, honourCommit, COMMIT_ORPHAN_MS, COMMIT_STEP, commitJournalFile, commitToolkit, prepareCommit, prepareWorkspace, readCommitJournal, recoverCommit, strictBaseSwitch, undoCommit, withPromoWorkspace,
  type CommitManifest,
} from "../../src/shared/commit.js";
import { readCommitEvents } from "../../src/shared/lock_holds.js";
import { writeTextAtomic } from "../../src/shared/json_atomic.js";
import { addsRecordFile, currentGeneration, gensDir, KEEP_GENERATIONS, publishGeneration, runToolkitGenCli } from "../../src/shared/workspace.js";
import { TOOLKIT_JSON } from "../toolkit/helpers.js";

const haveTools = (() => { try { execFileSync("bash", ["-c", "command -v zstd && command -v flock"]); return true; } catch { return false; } })();
const sha = (s: string | Buffer) => createHash("sha256").update(s).digest("hex");
const quiet = () => {};

let dir: string;
let root: string;
let local: string;
let PATH: string | undefined;
const realLake = COMMIT_LAKE.run;
const realStep = COMMIT_STEP.at;
const put = async (rel: string, text: string, base = root) => {
  await mkdir(path.dirname(path.join(base, rel)), { recursive: true });
  await writeFile(path.join(base, rel), text);
};
const read = (rel: string, base = root) => readFileSync(path.join(base, rel), "utf8");

// ─── a stand-in Lake ──────────────────────────────────────────────────────────────────────────────
// Each module (the root `.lean` files and the library's tree, its staging aside) has an `.olean`
// naming its source's bytes, an `.olean.hash` and a `.trace` naming them too; the exe names every
// module's. `--no-build` exits 3 unless all of that matches the sources; a build rewrites what does
// not (unlinking an output first, the trace last).
const lakeCalls: { cwd: string; args: string[] }[] = [];
const lakeFaults = { noBuild: 0, build: 0, kill: 0 };
async function moduleFiles(cwd: string): Promise<string[]> {
  const out = ["Toolkit.lean", "CandidateScan.lean"];
  const walk = async (rel: string) => {
    for (const e of await readdir(path.join(cwd, rel), { withFileTypes: true })) {
      const r = path.join(rel, e.name);
      if (e.isDirectory() && e.name !== "Staging") await walk(r);
      else if (e.isFile() && e.name.endsWith(".lean")) out.push(r);
    }
  };
  await walk("Toolkit");
  return out.sort();
}
async function expected(cwd: string): Promise<Map<string, string>> {
  const files = new Map<string, string>();
  const shas: string[] = [];
  for (const m of await moduleFiles(cwd)) {
    const s = sha(await readFile(path.join(cwd, m)));
    shas.push(s);
    const base = path.join(".lake", "build", "lib", "lean", m.slice(0, -".lean".length));
    files.set(`${base}.olean`, `olean ${s}`);
    files.set(`${base}.olean.hash`, sha(`olean ${s}`));
    files.set(`${base}.trace`, s);
  }
  files.set(path.join(".lake", "build", "bin", "candidate_scan"), `exe ${sha(shas.join())}`);
  return files;
}
async function fakeLake(cwd: string, args: string[]): Promise<{ code: number | null; out: string }> {
  lakeCalls.push({ cwd, args });
  const want = await expected(cwd);
  const stale: string[] = [];
  for (const [f, text] of want) if ((await readFile(path.join(cwd, f), "utf8").catch(() => null)) !== text) stale.push(f);
  if (args.includes("--no-build")) {
    if (lakeFaults.noBuild > 0) { lakeFaults.noBuild--; return { code: 3, out: "error: target is out of date and needs to be rebuilt" }; }
    return stale.length ? { code: 3, out: `error: ${stale[0]} is out of date` } : { code: 0, out: "All targets up-to-date" };
  }
  if (lakeFaults.kill > 0) { lakeFaults.kill--; return { code: null, out: "killed" }; }
  if (lakeFaults.build > 0) { lakeFaults.build--; return { code: 1, out: "error: build failed" }; }
  const rank = (f: string) => (f.endsWith(".trace") ? 2 : f.endsWith(".hash") ? 1 : 0);
  for (const f of stale.sort((a, b) => rank(a) - rank(b))) {
    // (a compile's input, written in place before it, as Lake does; no `--no-build` verdict reads it)
    const lib = path.join(".lake", "build", "lib", "lean") + path.sep;
    if (f.startsWith(lib) && f.endsWith(".olean")) await put(path.join(".lake", "build", "ir", `${f.slice(lib.length, -".olean".length)}.setup.json`), "{}\n", cwd);
    await unlink(path.join(cwd, f)).catch(() => {});
    await put(f, want.get(f)!, cwd);
  }
  return { code: 0, out: "Build completed successfully" };
}
const upToDate = async (cwd: string) => (await fakeLake(cwd, ["build", "--no-build"])).code === 0;
const liveSig = async () => toolkitSignature(await toolkitLayout(root));

/** Run `slug`'s promotion: a workspace for `papers`, `edit` in it, built; its prepared commit. */
async function promotion(slug: string, papers: string[], edit: (ws: string) => Promise<void>, extra: Parameters<typeof prepareCommit>[2] = {}) {
  const w = await prepareWorkspace(root, slug, papers, { localRoot: local });
  await edit(w.path);
  await fakeLake(w.path, ["build"]);
  return { ws: w.path, C: await prepareCommit(root, w.path, extra) };
}
/** Shared mode on, with a stand-in clean build (what old code's stamp needs to run at all). */
async function sharedOn(): Promise<() => Promise<void>> {
  const mode = path.join(root, ".lake", "paperformalizer", "lake-shared-mode");
  await writeFile(mode, "");
  const run = LAKE_LOCK_CLEAN_BUILD.run;
  LAKE_LOCK_CLEAN_BUILD.run = async () => ({ ok: true, log: "" });
  return async () => { LAKE_LOCK_CLEAN_BUILD.run = run; await unlink(mode).catch(() => {}); };
}
/** The symbolic links under `dir`. */
function linksUnder(dir: string): string[] {
  const out: string[] = [];
  for (const e of readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, e.name);
    if (e.isSymbolicLink()) out.push(p);
    else if (e.isDirectory()) out.push(...linksUnder(p));
  }
  return out;
}
const manifest = (C: string) => JSON.parse(readFileSync(path.join(C, "manifest.json"), "utf8")) as CommitManifest;

beforeAll(async () => {
  dir = await mkdtemp(path.join(os.tmpdir(), "commit-"));
  root = path.join(dir, "top", "tk");
  local = path.join(dir, "local");
  // a base library's index outside the toolkit, as the live config names `../tools/data/…`
  await put("paperformalizer.json", JSON.stringify({ ...TOOLKIT_JSON, base: TOOLKIT_JSON.base.map((b) => (b.name === "Base" ? { ...b, index: "../tools/data/libraries.json" } : b)) }));
  // (the shared toolkit's own ../tools: never what a workspace reaches)
  await put("tools/data/libraries.json", "{\"the\":\"shared one\"}\n", path.join(dir, "top"));
  await put("lakefile.toml", 'name = "tk"\n[[lean_lib]]\nname = "Toolkit"\n[[lean_lib]]\nname = "Papers"\n[[lean_exe]]\nname = "candidate_scan"\nroot = "CandidateScan"\n');
  await put("lean-toolchain", "leanprover/lean4:v4.33.0\n");
  await put("lake-manifest.json", "{}\n");
  await put("Toolkit.lean", "module\npublic import Toolkit.A\npublic import Toolkit.B\n");
  await put("Toolkit/A.lean", "-- A v1\n");
  await put("Toolkit/B.lean", "-- B v1\n");
  await put("Toolkit/Staging/S.lean", "-- a study's staging\n");
  await put("CandidateScan.lean", "-- scan\n");
  await put("Papers.lean", "-- papers\n");
  await put("Papers/P.lean", "import Papers.P.Main\n");
  await put("Papers/P/Main.lean", "-- P v1\n");
  await put("Papers/P/tmp/scratch.lean", "-- scratch\n");
  await put("Papers/Q.lean", "import Papers.Q.Main\n");
  await put("Papers/Q/Main.lean", "-- Q v1\n");
  await put("doc/ledger.json", JSON.stringify({ version: 1, declarations: [], decisions: [] }));
  await put("doc/toolkit_index.json", '{"v":1}\n');
  await put("doc/taxonomy.json", "{}\n");
  await put("doc/statements/r1.json", JSON.stringify({ version: 1, entries: [] }));
  await mkdir(path.join(root, "runs"), { recursive: true });
  await put(".toolkit-promote.lock", "1\n");
  await mkdir(path.join(root, ".lake", "packages"), { recursive: true });
  // a `lean` that answers `--version` (the signature names the toolchain)
  await put("bin/lean", "#!/bin/sh\necho 'Lean (version 4.0.0, test)'\n", dir);
  await chmod(path.join(dir, "bin", "lean"), 0o755);
  PATH = process.env.PATH;
  process.env.PATH = `${path.join(dir, "bin")}:${PATH}`;
  COMMIT_LAKE.run = fakeLake;
  await fakeLake(root, ["build"]);
  await mkdir(gensDir(root), { recursive: true });
  expect((await publishGeneration(root, await liveSig(), quiet))?.gen).toBe(1);
});
afterAll(async () => {
  process.env.PATH = PATH;
  COMMIT_LAKE.run = realLake;
  await rm(dir, { recursive: true, force: true });
});
beforeEach(() => {
  lakeCalls.length = 0;
  lakeFaults.noBuild = lakeFaults.build = lakeFaults.kill = 0;
  COMMIT_STEP.at = realStep;
});

describe.skipIf(process.platform === "win32" || !haveTools)("toolkit commits", () => {
  it("prepares in a detached workspace and lands as the next generation, Lake finding the shared tree up to date", async () => {
    const decl = { name: "Toolkit.A.thm", module: "Toolkit.A", division: "Foundations", origin: { kind: "proposal" as const, slug: "r1" }, date: "2026-11-10", decision: "accept", used_by: [] };
    const { ws, C } = await promotion("r1", ["Papers.P"], async (ws) => {
      // detached: the paper written is a copy (its scratch left out), the others the shared tree's; the docs private
      expect(lstatSync(path.join(ws, "Papers")).isSymbolicLink()).toBe(false);
      expect(lstatSync(path.join(ws, "Papers", "P")).isSymbolicLink()).toBe(false);
      expect(existsSync(path.join(ws, "Papers", "P", "tmp"))).toBe(false);
      // no other paper; the docs and the papers' barrel copies: nothing under Papers/ or doc/ leads into the shared tree
      expect(existsSync(path.join(ws, "Papers", "Q"))).toBe(false);
      // what the config names under ../tools: a copy of the RUNNING checkout's, never a link, never the shared toolkit's
      const named = path.join(ws, "..", "tools", "data", "libraries.json");
      expect(lstatSync(named).isSymbolicLink()).toBe(false);
      expect(lstatSync(path.join(ws, "..", "tools")).isSymbolicLink()).toBe(false);
      expect(readFileSync(named, "utf8")).toBe(readFileSync(new URL("../../data/libraries.json", import.meta.url), "utf8"));
      expect(lstatSync(path.join(ws, "Papers.lean")).isSymbolicLink()).toBe(false);
      expect(linksUnder(path.join(ws, "Papers"))).toEqual([]);
      expect(linksUnder(path.join(ws, "doc"))).toEqual([]);
      // no lock file of the shared tree is linked: the workspace's code takes its own
      expect(readdirSync(ws).filter((e) => /lock/.test(e) && lstatSync(path.join(ws, e)).isSymbolicLink())).toEqual([]);
      expect(lstatSync(path.join(ws, "doc", "ledger.json")).isSymbolicLink()).toBe(false);
      expect(readFileSync(path.join(ws, "doc", "taxonomy.json"), "utf8")).toBe("{}\n");
      // the statement store's shards are left out (no gate reads or writes them)
      expect(existsSync(path.join(ws, "doc", "statements"))).toBe(false);
      await writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A v2\n");
      await writeTextAtomic(path.join(ws, "Toolkit", "C.lean"), "-- C new\n");
      await writeTextAtomic(path.join(ws, "Toolkit.lean"), "module\npublic import Toolkit.A\npublic import Toolkit.B\npublic import Toolkit.C\n");
      await writeTextAtomic(path.join(ws, "Papers", "P", "Main.lean"), "-- P v2: uses Toolkit.C\n");
      await writeTextAtomic(path.join(ws, "doc", "toolkit_index.json"), '{"v":2}\n');
      await writeTextAtomic(path.join(ws, "doc", "ledger.json"), "never installed\n");
    }, { ledger: [decl], records: [{ slug: "r1", record: { moves: ["m1"] } }] });
    // nothing shared written before the commit
    expect(read("Toolkit/A.lean")).toBe("-- A v1\n");
    expect(read("Papers/P/Main.lean")).toBe("-- P v1\n");
    const m = manifest(C);
    expect(m.base.gen).toBe(1);
    expect(m.targets).toEqual(["Toolkit", "candidate_scan"]);
    expect(m.sources.map((s) => s.rel)).toEqual(["Papers/P/Main.lean", "Toolkit.lean", "Toolkit/A.lean", "Toolkit/C.lean", "doc/toolkit_index.json"]);
    expect(m.sources.find((s) => s.rel === "Toolkit/C.lean")?.before).toBeNull();
    expect(m.sources.find((s) => s.rel === "Toolkit/A.lean")).toMatchObject({ before: sha("-- A v1\n"), after: sha("-- A v2\n") });
    // the delta: what the build changed, never what it left (B), never a paper's
    const rels = m.build.map((b) => b.rel);
    expect(rels).toEqual(expect.arrayContaining(["lib/lean/Toolkit/A.olean", "lib/lean/Toolkit/A.trace", "lib/lean/Toolkit/C.olean", "lib/lean/Toolkit.trace", "bin/candidate_scan"]));
    expect(rels.filter((r) => r.includes("Toolkit/B.") || r.includes("Papers"))).toEqual([]);
    // never a `.setup.json` (the build in the workspace wrote them): not in the delta, nor the generation
    expect(existsSync(path.join(ws, ".lake", "build", "ir", "Toolkit", "C.setup.json"))).toBe(true);
    expect(rels.filter((r) => r.endsWith(".setup.json"))).toEqual([]);
    expect(execFileSync("bash", ["-c", `zstd -dc "$1" | tar -t`, "_", path.join(C, "gen.tar.zst")], { encoding: "utf8" }).split("\n").filter((n) => n.endsWith(".setup.json"))).toEqual([]);
    expect(readFileSync(path.join(C, "orig", "Toolkit", "A.lean"), "utf8")).toBe("-- A v1\n");

    const r = await commitToolkit(root, C, { log: quiet });
    expect(r).toMatchObject({ kind: "landed", gen: 2, slow: false, left: [] });
    // Lake judged the shared tree once, built nothing
    expect(lakeCalls.filter((c) => c.cwd === root).map((c) => c.args[1])).toEqual(["--no-build"]);
    expect(await upToDate(root)).toBe(true);
    expect(read("Toolkit/A.lean")).toBe("-- A v2\n");
    expect(read("Papers/P/Main.lean")).toBe("-- P v2: uses Toolkit.C\n");
    expect(read("doc/toolkit_index.json")).toBe('{"v":2}\n');
    // the generation is the tree as it stands, stamped clean; the ledger, the run's record
    const sig = await liveSig();
    expect(await currentGeneration(root)).toMatchObject({ gen: 2, sig });
    expect(await stampedClean(root)).toEqual({ sig });
    const names = execFileSync("bash", ["-c", `zstd -dc "$1" | tar -t`, "_", path.join(gensDir(root), "2.tar.zst")], { encoding: "utf8" }).split("\n");
    expect(names).toEqual(expect.arrayContaining(["Toolkit/C.lean", ".lake/build/lib/lean/Toolkit/C.olean"]));
    expect(JSON.parse(read("doc/ledger.json")).declarations.map((d: { name: string }) => d.name)).toEqual(["Toolkit.A.thm"]);
    expect(JSON.parse(read(`runs/r1/proposals/landed/${m.id}.json`))).toMatchObject({ gen: 2, record: { moves: ["m1"] } });
    expect(existsSync(commitJournalFile(root))).toBe(false);
    expect(existsSync(C)).toBe(false);
    expect(existsSync(ws)).toBe(true);
  }, 120_000);

  it("refuses a commit prepared on an older generation (base-moved); re-prepared on the new one, it lands", async () => {
    const edit = (ws: string) => writeTextAtomic(path.join(ws, "Toolkit", "B.lean"), "-- B v2\n");
    const first = await promotion("r2", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A v3\n"));
    const second = await promotion("r3", [], edit);
    const landed = await commitToolkit(root, first.C, { log: quiet });
    expect(landed.kind).toBe("landed");
    expect(await commitToolkit(root, second.C, { log: quiet })).toMatchObject({ kind: "base-moved" });
    expect(read("Toolkit/B.lean")).toBe("-- B v1\n");
    // the rebase: re-pinned (the other commit's sources and outputs come with the generation), redone
    const again = await promotion("r3", [], edit);
    expect(manifest(again.C).sources.map((s) => s.rel)).toEqual(["Toolkit/B.lean"]);
    expect(await commitToolkit(root, again.C, { log: quiet })).toMatchObject({ kind: "landed", gen: 4 });
    expect(read("Toolkit/A.lean")).toBe("-- A v3\n");
    expect(read("Toolkit/B.lean")).toBe("-- B v2\n");
    expect(await upToDate(root)).toBe(true);
  }, 120_000);

  it("takes the real build when Lake would build after the install, and packs the shared tree", async () => {
    const { C } = await promotion("r4", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A v4\n"));
    lakeFaults.noBuild = 1;
    const lines: string[] = [];
    const r = await commitToolkit(root, C, { log: (l) => lines.push(l) });
    expect(r).toMatchObject({ kind: "landed", slow: true });
    expect(lines.join("\n")).toMatch(/LAKE WOULD BUILD/);
    expect(lakeCalls.filter((c) => c.cwd === root).map((c) => c.args[1] ?? null)).toEqual(["--no-build", "Toolkit"]);
    expect(await currentGeneration(root)).toMatchObject({ sig: await liveSig() });
  }, 120_000);

  it("waits while the tree is not its generation or is in flux, and finds a paper changed since it was read", async () => {
    const { C } = await promotion("r5", ["P"], (ws) => writeTextAtomic(path.join(ws, "Papers", "P", "Main.lean"), "-- P v3\n"));
    const flux = path.join(root, ".lake", "paperformalizer", "toolkit-flux");
    await writeFile(flux, "{}");
    expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "wait", why: expect.stringMatching(/flux/) });
    await unlink(flux);
    // the paper's run edited it meanwhile
    await writeTextAtomic(path.join(root, "Papers", "P", "Main.lean"), "-- P edited by its run\n");
    expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/Papers\/P\/Main.lean/) });
    // a hand edit of the library, not published: never committed onto
    const { C: C2 } = await promotion("r6", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A v5\n"));
    await writeTextAtomic(path.join(root, "Toolkit", "B.lean"), "-- B by hand\n");
    expect(await commitToolkit(root, C2, { log: quiet })).toMatchObject({ kind: "wait", why: expect.stringMatching(/not generation/) });
    expect(read("Toolkit/A.lean")).toBe("-- A v4\n");
    // published again (as a clean stamp would)
    await fakeLake(root, ["build"]);
    await publishGeneration(root, await liveSig(), quiet);
  }, 120_000);

  it("stops the line when the shared tree does not build: CURRENT stays, every commit waits, until undo", async () => {
    const before = await currentGeneration(root);
    const { C } = await promotion("r7", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A v6\n"));
    const { C: C2 } = await promotion("r8", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "B.lean"), "-- B v3\n"));
    lakeFaults.noBuild = 1;
    lakeFaults.build = 1;
    const lines: string[] = [];
    const r = await commitToolkit(root, C, { log: (l) => lines.push(l) });
    expect(r).toMatchObject({ kind: "wait", why: expect.stringMatching(/line is stopped/) });
    expect(lines.join("\n")).toMatch(/STOP THE LINE/);
    expect(await currentGeneration(root)).toEqual(before);
    expect((await readCommitJournal(root))?.stopped).toBeTruthy();
    expect(read("Toolkit/A.lean")).toBe("-- A v6\n");
    expect(await commitToolkit(root, C2, { log: quiet })).toMatchObject({ kind: "wait", why: expect.stringMatching(/line is stopped/) });
    // the owner's undo: the sources as they were, built, published
    expect(await undoCommit(root, quiet)).toMatchObject({ kind: "landed" });
    expect(read("Toolkit/A.lean")).toBe(read("Toolkit/A.lean", path.join(local, "gens", String(before!.gen))));
    expect(existsSync(commitJournalFile(root))).toBe(false);
    expect(await currentGeneration(root)).toMatchObject({ gen: before!.gen + 1, sig: await liveSig() });
    expect(await commitToolkit(root, C2, { log: quiet })).toMatchObject({ kind: "base-moved" });
  }, 120_000);

  for (const step of ["journaled", "sources", "build-half", "build-files", "stamped", "published"]) {
    it(`rolls forward a commit interrupted at "${step}"`, async () => {
      const { C } = await promotion(`k-${step}`, ["P"], async (ws) => {
        await writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), `-- A at ${step}\n`);
        await writeTextAtomic(path.join(ws, "Toolkit", `K${step.replace(/-/g, "")}.lean`), "-- new\n");
        await writeTextAtomic(path.join(ws, "Papers", "P", "Main.lean"), `-- P at ${step}\n`);
      }, { records: [{ slug: `k-${step}`, record: {} }] });
      const id = manifest(C).id;
      const base = (await currentGeneration(root))!;
      COMMIT_STEP.at = async (s) => { if (s === step) throw new Error(`killed at ${s}`); };
      await expect(commitToolkit(root, C, { log: quiet })).rejects.toThrow(`killed at ${step}`);
      expect((await readCommitJournal(root))?.id).toBe(id);
      COMMIT_STEP.at = realStep;
      // the next holder finishes it: forward, with the real build, the shared tree packed
      expect(await recoverCommit(root, quiet)).toMatchObject({ kind: "landed" });
      expect(existsSync(commitJournalFile(root))).toBe(false);
      expect(read("Toolkit/A.lean")).toBe(`-- A at ${step}\n`);
      expect(read("Papers/P/Main.lean")).toBe(`-- P at ${step}\n`);
      expect(await upToDate(root)).toBe(true);
      const sig = await liveSig();
      expect(await stampedClean(root)).toEqual({ sig });
      expect(await currentGeneration(root)).toMatchObject({ sig });
      expect((await currentGeneration(root))!.gen).toBeGreaterThan(base.gen);
      expect(existsSync(path.join(root, "runs", `k-${step}`, "proposals", "landed", `${id}.json`))).toBe(true);
    }, 120_000);
  }

  it("never sweeps the commit being committed, only orphans a day old", async () => {
    const { C } = await promotion("s1", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "B.lean"), "-- B swept?\n"));
    const orphan = path.join(path.dirname(C), "commitzz000-abcdef");
    await mkdir(orphan, { recursive: true });
    const old = new Date(Date.now() - COMMIT_ORPHAN_MS - 60_000);
    await utimes(orphan, old, old);
    await utimes(C, old, old);
    expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "landed" });
    expect(existsSync(orphan)).toBe(false);
    expect(read("Toolkit/B.lean")).toBe("-- B swept?\n");
  }, 120_000);

  it("drops the archive of a prepared commit the base moved past, keeping its manifest; never the journal's", async () => {
    // (2026-11-11) 10 GB of `gen.tar.zst` on the shared disk for commits that could never land
    const first = await promotion("d1", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "B.lean"), "-- B d1\n"));
    const stale = await promotion("d2", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A d2\n"));
    expect(await commitToolkit(root, first.C, { log: quiet })).toMatchObject({ kind: "landed" });
    expect(existsSync(path.join(stale.C, "gen.tar.zst"))).toBe(true);
    // named by a journal: kept (a roll-forward reads its directory)
    await writeFile(commitJournalFile(root), JSON.stringify({ id: path.basename(stale.C), dir: stale.C }));
    await dropArchive(root, stale.C);
    expect(existsSync(path.join(stale.C, "gen.tar.zst"))).toBe(true);
    await unlink(commitJournalFile(root));
    // the next commit's sweep: its base is behind CURRENT — the archive goes, the manifest and sources stay
    const next = await promotion("d3", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "B.lean"), "-- B d3\n"));
    expect(await commitToolkit(root, next.C, { log: quiet })).toMatchObject({ kind: "landed" });
    expect(existsSync(path.join(stale.C, "gen.tar.zst"))).toBe(false);
    expect(existsSync(path.join(stale.C, "manifest.json"))).toBe(true);
    expect(existsSync(path.join(stale.C, "delta.tar"))).toBe(true);
    // and it is refused as ever: base-moved, then removed by its caller
    expect(await commitToolkit(root, stale.C, { log: quiet })).toMatchObject({ kind: "base-moved" });
  }, 120_000);

  it("refuses a prepared commit that is not complete, before writing anything", async () => {
    const { C } = await promotion("s2", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A s2\n"));
    await writeFile(path.join(C, "src", "Toolkit", "A.lean"), "-- tampered\n");
    await expect(commitToolkit(root, C, { log: quiet })).rejects.toThrow(/not complete \(src\/Toolkit\/A.lean\)/);
    expect(existsSync(commitJournalFile(root))).toBe(false);
    expect(read("Toolkit/A.lean")).not.toBe("-- A s2\n");
    expect(await toolkitFluxWhy(root)).toBeNull();
  }, 120_000);

  it("resets a reused workspace to its generation: an abandoned preparation's edits never go with the next", async () => {
    const w = await prepareWorkspace(root, "s3", [], { localRoot: local });
    await writeTextAtomic(path.join(w.path, "Toolkit", "B.lean"), "-- abandoned\n");
    await writeTextAtomic(path.join(w.path, "Toolkit", "Abandoned.lean"), "-- abandoned\n");
    // (never prepared) — the next preparation on the same generation starts from it again
    const { C } = await promotion("s3", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A s3\n"));
    expect(manifest(C).sources.map((x) => x.rel)).toEqual(["Toolkit/A.lean"]);
    expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "landed" });
    expect(existsSync(path.join(root, "Toolkit", "Abandoned.lean"))).toBe(false);
  }, 120_000);

  it("holds a run's promotion workspace for one user at a time: a second waits for it (bounded), never resetting it under the first", async () => {
    const lockFile = path.join(local, "ws", "s40.promo", ".pf-promo.flock");
    // two users of P (as two processes: each holds it by its own `flock`): the second's prepare
    // waits for the first's last use, then resets P and goes on
    const order: string[] = [];
    let release!: () => void;
    const gate = new Promise<void>((r) => { release = r; });
    let reached!: () => void;
    const inFirst = new Promise<void>((r) => { reached = r; });
    const first = withPromoWorkspace(root, "s40", [], { localRoot: local }, async (w) => {
      await writeTextAtomic(path.join(w.path, "Toolkit", "Mid.lean"), "-- the first's edit\n");
      reached();
      await gate;
      order.push(`first sees ${existsSync(path.join(w.path, "Toolkit", "Mid.lean")) ? "its edit" : "a reset"}`);
    });
    await inFirst;
    const lines: string[] = [];
    const second = withPromoWorkspace(root, "s40", [], { localRoot: local, log: (l) => lines.push(l) }, async (w) => {
      order.push(`second prepared ${existsSync(path.join(w.path, "Toolkit", "Mid.lean")) ? "over the edit" : "afresh"}`);
    });
    await new Promise((r) => setTimeout(r, 1500));
    expect(order).toEqual([]);
    expect(lines.some((l) => /s40\.promo .*held by another process — waiting for it \(14400 s at most\)/.test(l))).toBe(true);
    release();
    await Promise.all([first, second]);
    expect(order).toEqual(["first sees its edit", "second prepared afresh"]);
    // a holder that outlasts the bound: a clear failure, nothing prepared, P as the holder left it
    const P = await withPromoWorkspace(root, "s40", [], { localRoot: local }, async (w) => w.path);
    await writeTextAtomic(path.join(P, "Toolkit", "Mid.lean"), "-- held\n");
    const holder = execFileSync("bash", ["-c", `flock "$1" -c 'exec sleep 30' >/dev/null 2>&1 & echo $!`, "_", lockFile], { encoding: "utf8" }).trim();
    try {
      for (let i = 0; i < 50 && execFileSync("bash", ["-c", `flock -n "$1" true && echo free || echo busy`, "_", lockFile], { encoding: "utf8" }).trim() === "free"; i++) await new Promise((r) => setTimeout(r, 100));
      let ran = false;
      await expect(withPromoWorkspace(root, "s40", [], { localRoot: local, lockWaitS: 1, log: quiet }, async () => { ran = true; })).rejects.toThrow(/s40\.promo .*still held by another process after 1 s — gave up, nothing done/);
      expect(ran).toBe(false);
      expect(read("Toolkit/Mid.lean", P)).toBe("-- held\n");
    } finally {
      execFileSync("bash", ["-c", `pkill -P "$1"; kill "$1" 2>/dev/null; true`, "_", holder]);
    }
  }, 120_000);

  it("refuses a workspace that wrote a paper it did not copy; the shared paper is untouched", async () => {
    const w = await prepareWorkspace(root, "s4", ["P"], { localRoot: local });
    await writeTextAtomic(path.join(w.path, "Papers", "Q", "Main.lean"), "-- Q rewritten\n");
    expect(read("Papers/Q/Main.lean")).toBe("-- Q v1\n");
    await fakeLake(w.path, ["build"]);
    await expect(prepareCommit(root, w.path)).rejects.toThrow(/wrote Papers\/Q\/Main.lean, which it did not copy/);
  }, 120_000);

  it("commits the declarations a workspace's private ledger gained (by hand, no ledger given)", async () => {
    const decl = { name: "Toolkit.A.by_hand", module: "Toolkit.A", division: "Foundations", origin: { kind: "proposal" as const, slug: "s5" }, date: "2026-11-10", decision: "by hand", used_by: [] };
    const { C } = await promotion("s5", [], async (ws) => {
      await writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A s5\n");
      await appendLedgerDeclarations(path.join(ws, "doc", "ledger.json"), [decl]);
    });
    expect(manifest(C).ledger.map((d) => d.name)).toEqual(["Toolkit.A.by_hand"]);
    expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "landed" });
    expect(JSON.parse(read("doc/ledger.json")).declarations.filter((d: { name: string }) => d.name === "Toolkit.A.by_hand")).toHaveLength(1);
  }, 120_000);

  it("rejects signatures that vouch for nothing: CURRENT's or the live toolkit's", async () => {
    const { C } = await promotion("s6", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A s6\n"));
    const cur = (await currentGeneration(root))!;
    const file = path.join(gensDir(root), "CURRENT.json");
    await writeFile(file, JSON.stringify({ ...cur, sig: "doubt:test:x" }));
    expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "wait", why: expect.stringMatching(/vouches for nothing/) });
    await writeFile(file, JSON.stringify(cur));
    // a manifest the signature cannot read: a doubt
    const manifestText = read("lake-manifest.json");
    await writeFile(path.join(root, "lake-manifest.json"), "{not json");
    expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "wait", why: expect.stringMatching(/cannot be read/) });
    await writeTextAtomic(path.join(root, "lake-manifest.json"), manifestText);
    await publishGeneration(root, await liveSig(), quiet);
    expect(read("Toolkit/A.lean")).not.toBe("-- A s6\n");
  }, 120_000);

  it("a build killed by its cap is no verdict: the commit waits, unstopped, and the next holder rolls it forward", async () => {
    const { C } = await promotion("s7", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A s7\n"));
    lakeFaults.noBuild = 1;
    lakeFaults.kill = 1;
    expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "wait", why: expect.stringMatching(/killed/) });
    const j = await readCommitJournal(root);
    expect(j?.stopped).toBeUndefined();
    // the same commit asked again: rolled forward, and reported landed
    expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "landed" });
    expect(read("Toolkit/A.lean")).toBe("-- A s7\n");
    expect(await toolkitFluxWhy(root)).toBeNull();
  }, 120_000);

  it("never rolls forward over a moved base: a toolkit file changed after a crash stops the line", async () => {
    const before = (await currentGeneration(root))!;
    const { C } = await promotion("s8", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A s8\n"));
    COMMIT_STEP.at = async (s) => { if (s === "sources") throw new Error("killed"); };
    await expect(commitToolkit(root, C, { log: quiet })).rejects.toThrow("killed");
    COMMIT_STEP.at = realStep;
    // an old-code holder after the crash: in flux, so it stamps nothing clean and publishes nothing
    const undoShared = await sharedOn();
    try {
      expect(await stampedClean(root)).toMatchObject({ why: expect.stringMatching(/in flux/) });
      // every exclusive hold outside a commit's own chain is refused while it is on file
      await expect(withLakeBuildLock(root, () => stampToolkitClean(root, quiet), "test: old code's stamp", quiet)).rejects.toThrow(/refused — a toolkit commit is on file/);
      expect(await withinCommit(() => withLakeBuildLock(root, () => stampToolkitClean(root, quiet), "test: inside a commit's chain", quiet))).toMatchObject({ clean: false });
      const lines: string[] = [];
      await expect(runToolkitGenCli(["publish", "--locked", "--toolkit", root], (l) => lines.push(l))).rejects.toThrow(/a toolkit commit is on file/);
      expect(await currentGeneration(root)).toEqual(before);
      // ... but a process older than the merge, which knows nothing of commits, may still write the library
      await writeTextAtomic(path.join(root, "Toolkit", "B.lean"), "-- B by old code\n");
      const r = await recoverCommit(root, quiet);
      expect(r).toMatchObject({ kind: "wait", why: expect.stringMatching(/Toolkit\/B.lean changed since .*never rolled forward over a moved base/) });
      expect((await readCommitJournal(root))?.stopped).toBeTruthy();
      expect(await currentGeneration(root)).toEqual(before);
    } finally {
      await undoShared();
    }
    // the owner's way out: the commit undone (its files as they were; the old code's write stands), built, published
    expect(await recoverCommit(root, quiet)).toMatchObject({ kind: "wait" });
    expect(await undoCommit(root, quiet)).toMatchObject({ kind: "landed" });
    expect(read("Toolkit/A.lean")).toBe(read("Toolkit/A.lean", path.join(local, "gens", String(before.gen))));
    expect(read("Toolkit/B.lean")).toBe("-- B by old code\n");
    expect(await toolkitFluxWhy(root)).toBeNull();
    expect(await currentGeneration(root)).toMatchObject({ sig: await liveSig() });
  }, 120_000);

  it("appends the ledger once across a roll-forward", async () => {
    const decl = { name: "Toolkit.A.once", module: "Toolkit.A", division: "Foundations", origin: { kind: "proposal" as const, slug: "s9" }, date: "2026-11-10", decision: "accept", used_by: [] };
    const { C } = await promotion("s9", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A s9\n"), { ledger: [decl] });
    COMMIT_STEP.at = async (s) => { if (s === "stamped") throw new Error("killed"); };
    await expect(commitToolkit(root, C, { log: quiet })).rejects.toThrow("killed");
    COMMIT_STEP.at = realStep;
    expect(await recoverCommit(root, quiet)).toMatchObject({ kind: "landed" });
    expect(JSON.parse(read("doc/ledger.json")).declarations.filter((d: { name: string }) => d.name === "Toolkit.A.once")).toHaveLength(1);
  }, 120_000);

  it("an in-place write in the workspace never reaches the shared tree, and a doc written there is refused", async () => {
    const w = await prepareWorkspace(root, "s10", ["P"], { localRoot: local });
    // (fs.writeFile writes in place: through a link it would write the shared file)
    await writeFile(path.join(w.path, "doc", "taxonomy.json"), "{\"in\":\"place\"}\n");
    await writeFile(path.join(w.path, "Papers", "P", "Main.lean"), "-- in place\n");
    expect(read("doc/taxonomy.json")).toBe("{}\n");
    expect(read("Papers/P/Main.lean")).not.toBe("-- in place\n");
    await fakeLake(w.path, ["build"]);
    await expect(prepareCommit(root, w.path)).rejects.toThrow(/wrote doc\/taxonomy.json, which it did not copy/);
  }, 120_000);

  it("inserts the imports a workspace added to the papers' barrel into its bytes at the commit (no compare-and-swap)", async () => {
    await writeTextAtomic(path.join(root, "Papers.lean"), "module\n\npublic import Papers.P\npublic import Papers.Q\n");
    const { C } = await promotion("s11", [], async (ws) => {
      await writeTextAtomic(path.join(ws, "Papers.lean"), "module\n\npublic import Papers.N\npublic import Papers.P\npublic import Papers.Q\n");
    });
    expect(manifest(C).sources.map((x) => x.rel)).toEqual([]);
    expect(manifest(C).barrel).toEqual({ rel: "Papers.lean", imports: ["public import Papers.N"] });
    // a paper registered meanwhile: no rebase, both stand
    await writeTextAtomic(path.join(root, "Papers.lean"), "module\n\npublic import Papers.P\npublic import Papers.Q\npublic import Papers.Z\n");
    expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "landed" });
    expect(read("Papers.lean")).toBe("module\n\npublic import Papers.N\npublic import Papers.P\npublic import Papers.Q\npublic import Papers.Z\n");
  }, 120_000);

  it("copies the papers a copied paper imports, transitively", async () => {
    await put("Papers/R.lean", "import Papers.R.Main\n");
    await put("Papers/R/Main.lean", "import Papers.Q.Main\n-- R\n");
    const w = await prepareWorkspace(root, "s14", ["R"], { localRoot: local });
    expect(read("Papers/R/Main.lean", w.path)).toBe("import Papers.Q.Main\n-- R\n");
    expect(read("Papers/Q/Main.lean", w.path)).toBe(read("Papers/Q/Main.lean"));
    expect(existsSync(path.join(w.path, "Papers", "P"))).toBe(false);
  }, 120_000);

  it("other promotion paths honour a commit on file: rolled forward first, refused when it cannot be; flux and stamps refuse beside it", async () => {
    const { C } = await promotion("s15", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A s15\n"));
    COMMIT_STEP.at = async (s) => { if (s === "sources") throw new Error("killed"); };
    await expect(commitToolkit(root, C, { log: quiet })).rejects.toThrow("killed");
    COMMIT_STEP.at = realStep;
    expect(await commitOnFile(root)).toBe(true);
    // what an old-path holder meets: no flux session opens, the commit's is not closed, no stamp
    await expect(toolkitFluxOn(root, "a hand edit", quiet)).rejects.toThrow(/toolkit commit is on file/);
    await expect(toolkitFluxOff(root, null, quiet)).rejects.toThrow(/toolkit commit/);
    // the docstrings pass (and every hand edit) opens its flux session first: refused, its pass never runs
    let ran = false;
    await expect(withToolkitFlux(root, "docstrings", async () => { ran = true; })).rejects.toThrow(/toolkit commit is on file/);
    expect(ran).toBe(false);
    const undoShared = await sharedOn();
    try {
      await expect(withLakeBuildLock(root, () => stampToolkitClean(root, quiet), "test: stamp", quiet)).rejects.toThrow(/a toolkit commit is on file/);
    } finally { await undoShared(); }
    // a promotion path, under the promotion lock: the commit finished first
    await withPromotionLock(root, () => honourCommit(root, quiet));
    expect(await commitOnFile(root)).toBe(false);
    expect(read("Toolkit/A.lean")).toBe("-- A s15\n");
    // a stopped line: refused
    const { C: C2 } = await promotion("s16", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A s16\n"));
    lakeFaults.noBuild = 1;
    lakeFaults.build = 1;
    expect(await commitToolkit(root, C2, { log: quiet })).toMatchObject({ kind: "wait" });
    await expect(withPromotionLock(root, () => honourCommit(root, quiet))).rejects.toThrow(/no promotion goes on over it/);
    expect(await clearCommit(root, manifest(C2).id, quiet)).toMatchObject({ kind: "landed" });
  }, 120_000);

  it("closes a commit's flux session left empty by a crash (known by its name), and commits", async () => {
    const id = "commitzz0crash-abcdef";
    await withLakeBuildLock(root, () => openFluxSession(root, id, "toolkit-commit test"), "test: a crashed commit's session", quiet);
    await writeFile(path.join(root, ".lake", "paperformalizer", "toolkit-flux.d", id), "");
    expect(await toolkitFluxWhy(root)).toMatch(/in flux/);
    const { C } = await promotion("s12", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A s12\n"));
    expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "landed" });
    expect(await toolkitFluxWhy(root)).toBeNull();
  }, 120_000);

  it("a stopped line cleared by hand: the tree as it stands built, published, its flux session closed, its records and declarations written", async () => {
    const decl = { name: "Toolkit.A.cleared", module: "Toolkit.A", division: "Foundations", origin: { kind: "proposal" as const, slug: "s13" }, date: "2026-11-10", decision: "accept", used_by: [] };
    const { C } = await promotion("s13", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A s13\n"), { ledger: [decl], records: [{ slug: "s13", record: { batch: "b" } }] });
    lakeFaults.noBuild = 1;
    lakeFaults.build = 1;
    const lines: string[] = [];
    expect(await commitToolkit(root, C, { log: (l) => lines.push(l) })).toMatchObject({ kind: "wait", why: expect.stringMatching(/line is stopped/) });
    const id = manifest(C).id;
    expect(lines.join("\n")).toMatch(new RegExp(`toolkit-commit clear ${id}`));
    // the owner's fix by hand, then clear
    await writeTextAtomic(path.join(root, "Toolkit", "A.lean"), "-- A fixed by hand\n");
    expect(await clearCommit(root, id, quiet)).toMatchObject({ kind: "landed" });
    expect(existsSync(commitJournalFile(root))).toBe(false);
    expect(await toolkitFluxWhy(root)).toBeNull();
    expect(await currentGeneration(root)).toMatchObject({ sig: await liveSig() });
    expect(read("Toolkit/A.lean")).toBe("-- A fixed by hand\n");
    expect(JSON.parse(read("doc/ledger.json")).declarations.filter((d: { name: string }) => d.name === "Toolkit.A.cleared")).toHaveLength(1);
    expect(JSON.parse(read(`runs/s13/proposals/landed/${id}.json`))).toMatchObject({ cleared: true, record: { batch: "b" } });
  }, 120_000);

  it("publishes, inside its locks, a toolkit stamped clean but not published yet, and returns base-moved; never an unstamped one", async () => {
    const { C } = await promotion("s30", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A s30\n"));
    const before = (await currentGeneration(root))!;
    // an old-path promotion lands: the library written and built, stamped clean, its publisher not run yet
    await writeTextAtomic(path.join(root, "Toolkit", "B.lean"), "-- B by an old-path promotion\n");
    await fakeLake(root, ["build"]);
    const t = await toolkitLayout(root);
    const scope = await toolkitScope(t);
    if ("why" in scope) throw new Error(scope.why);
    await recordToolkitClean(root, await liveSig(), scope);
    const lines: string[] = [];
    expect(await commitToolkit(root, C, { log: (l) => lines.push(l) })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/stamped clean and is published now/) });
    expect(await currentGeneration(root)).toMatchObject({ gen: before.gen + 1, sig: await liveSig() });
    expect(read("Toolkit/A.lean")).not.toBe("-- A s30\n");
    // a hand edit since the stamp: not published, the commit waits
    const { C: C2 } = await promotion("s31", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A s31\n"));
    await writeTextAtomic(path.join(root, "Toolkit", "B.lean"), "-- B by hand\n");
    const gen = (await currentGeneration(root))!.gen;
    expect(await commitToolkit(root, C2, { log: quiet })).toMatchObject({ kind: "wait", why: expect.stringMatching(/not generation/) });
    expect((await currentGeneration(root))!.gen).toBe(gen);
    await fakeLake(root, ["build"]);
    await publishGeneration(root, await liveSig(), quiet);
  }, 120_000);

  it("seeds a promotion's workspace with the papers' outputs of the run's own workspace on the same generation, when Lake finds them up to date there", async () => {
    const { ensureWorkspace } = await import("../../src/shared/workspace.js");
    const W = (await ensureWorkspace(root, "s20", { localRoot: local })).path;
    const out = (ws: string, rel: string) => path.join(ws, ".lake", "build", rel);
    await put(".lake/build/lib/lean/Papers/P/Main.olean", "P olean\n", W);
    await put(".lake/build/lib/lean/Papers/P/Main.trace", "P trace\n", W);
    await put(".lake/build/lib/lean/Papers/P.olean", "P barrel olean\n", W);
    await put(".lake/build/lib/lean/Papers/Q/Main.olean", "Q olean\n", W);
    const lines: string[] = [];
    const w = await prepareWorkspace(root, "s20", ["P"], { localRoot: local, log: (l) => lines.push(l) });
    expect(w.seeded).toEqual(["Papers.P"]);
    expect(lakeCalls.some((c) => c.cwd === W && c.args.join(" ") === "build --no-build Papers.P")).toBe(true);
    // compiler outputs hard links, what Lake writes in place copies; another paper's never
    expect(statSync(out(w.path, "lib/lean/Papers/P/Main.olean")).ino).toBe(statSync(out(W, "lib/lean/Papers/P/Main.olean")).ino);
    expect(statSync(out(w.path, "lib/lean/Papers/P/Main.trace")).ino).not.toBe(statSync(out(W, "lib/lean/Papers/P/Main.trace")).ino);
    expect(readFileSync(out(w.path, "lib/lean/Papers/P/Main.trace"), "utf8")).toBe("P trace\n");
    expect(existsSync(out(w.path, "lib/lean/Papers/P.olean"))).toBe(true);
    expect(existsSync(out(w.path, "lib/lean/Papers/Q"))).toBe(false);
    // P's own outputs then (the gate's build), prepared again on the same generation: P's own kept
    await put(".lake/build/lib/lean/Papers/P/Main.trace", "P trace, built in P\n", w.path);
    const lines1: string[] = [];
    expect((await prepareWorkspace(root, "s20", ["P"], { localRoot: local, log: (l) => lines1.push(l) })).seeded).toEqual([]);
    expect(lines1.join("\n")).toMatch(/its own paper outputs prepared on \d+: kept/);
    expect(read(".lake/build/lib/lean/Papers/P/Main.trace", w.path)).toBe("P trace, built in P\n");
    // not up to date in the run's workspace: not seeded
    await rm(path.join(w.path, ".pf-papers-gen.json"));
    lakeFaults.noBuild = 1;
    expect((await prepareWorkspace(root, "s20", ["P"], { localRoot: local })).seeded).toEqual([]);
    // a rebase: P re-pinned forward, the run's workspace on the older generation — P's own kept
    await fakeLake(root, ["build"]);
    await writeTextAtomic(path.join(root, "Toolkit", "B.lean"), "-- B s20\n");
    await fakeLake(root, ["build"]);
    await publishGeneration(root, await liveSig(), quiet);
    const lines2: string[] = [];
    const w2 = await prepareWorkspace(root, "s20", ["P"], { localRoot: local, log: (l) => lines2.push(l) });
    expect(w2.repinned).toBe(true);
    expect(w2.seeded).toEqual([]);
    expect(lines2.join("\n")).toMatch(/not seeded \(the run's workspace is on generation \d+, this one on \d+, its own paper outputs prepared on \d+: kept\)/);
    expect(read(".lake/build/lib/lean/Papers/P/Main.trace", w2.path)).toBe("P trace, built in P\n");
    // a fresh P: seeded from the run's workspace on an older generation too (Lake judges)
    await rm(path.join(w2.path, ".pf-papers-gen.json"));
    const lines3: string[] = [];
    expect((await prepareWorkspace(root, "s20", ["P"], { localRoot: local, log: (l) => lines3.push(l) })).seeded).toEqual(["Papers.P"]);
    expect(lines3.join("\n")).toMatch(/generation \d+, this one on \d+: Lake rebuilds what changed/);
    // the next rebase, with the run's workspace re-pinned to the new generation: seeded again
    await writeTextAtomic(path.join(root, "Toolkit", "B.lean"), "-- B s20 again\n");
    await fakeLake(root, ["build"]);
    await publishGeneration(root, await liveSig(), quiet);
    expect((await ensureWorkspace(root, "s20", { localRoot: local })).repinned).toBe(true);
    const w4 = await prepareWorkspace(root, "s20", ["P"], { localRoot: local });
    expect(w4.repinned).toBe(true);
    expect(w4.seeded).toEqual(["Papers.P"]);
    // a pin that moved back: P's own outputs dropped (then seeded)
    await put(".lake/build/lib/lean/Papers/P/Extra.olean", "P's own\n", w4.path);
    await writeFile(path.join(w4.path, ".pf-papers-gen.json"), JSON.stringify({ gen: 999 }));
    const lines5: string[] = [];
    expect((await prepareWorkspace(root, "s20", ["P"], { localRoot: local, log: (l) => lines5.push(l) })).seeded).toEqual(["Papers.P"]);
    expect(lines5.join("\n")).toMatch(/its pin moved back from generation 999 to \d+ — its own paper outputs dropped/);
    expect(existsSync(out(w4.path, "lib/lean/Papers/P/Extra.olean"))).toBe(false);
    // asked not to
    expect((await prepareWorkspace(root, "s21", ["P"], { localRoot: local, seed: false })).seeded).toEqual([]);
  }, 120_000);

  it("seeds each paper the run's workspace has up to date when not all are", async () => {
    const { ensureWorkspace } = await import("../../src/shared/workspace.js");
    const W = (await ensureWorkspace(root, "s22", { localRoot: local })).path;
    await put(".lake/build/lib/lean/Papers/P/Main.olean", "P olean\n", W);
    await put(".lake/build/lib/lean/Papers/R/Main.olean", "R olean\n", W);
    // (both together out of date, then P alone: R alone is up to date)
    lakeFaults.noBuild = 2;
    const w = await prepareWorkspace(root, "s22", ["P", "R", "S"], { localRoot: local });
    expect(w.seeded).toEqual(["Papers.R"]);
    expect(lakeCalls.filter((c) => c.cwd === W).map((c) => c.args.join(" "))).toEqual(["build --no-build Papers.P Papers.R", "build --no-build Papers.P", "build --no-build Papers.R"]);
    expect(existsSync(path.join(w.path, ".lake", "build", "lib", "lean", "Papers", "R", "Main.olean"))).toBe(true);
    expect(existsSync(path.join(w.path, ".lake", "build", "lib", "lean", "Papers", "P"))).toBe(false);
  }, 120_000);

  // ─── a paper-only commit off its base (I1′, 2026-11-11) ─────────────────────────────────────────
  describe("a paper-only commit lands on a later generation when nothing it read changed", () => {
    const mainD = (v: string) => `import Toolkit.Deep.X\nimport Papers.E.Main\nimport Mathlib.Tactic\n-- D ${v}\n`;
    /** A toolkit commit (one source written) prepared and landed: the next generation. */
    const toolkitLands = async (slug: string, rel: string, text: string) => {
      const { C } = await promotion(slug, [], (ws) => writeTextAtomic(path.join(ws, rel), text));
      expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "landed" });
    };
    /** Run `slug`'s paper-only commit of paper D (its main file at `v`). */
    const paperCommit = (slug: string, v: string, extra: Parameters<typeof prepareCommit>[2] = {}) =>
      promotion(slug, ["D"], (ws) => writeTextAtomic(path.join(ws, "Papers", "D", "Main.lean"), mainD(v)), extra);
    const archive = (gen: number) => statSync(path.join(gensDir(root), `${gen}.tar.zst`));
    const events = async (id: string) => (await readCommitEvents(root)).filter((e) => e.id === id).map((e) => [e.event, e.file ?? null]);
    beforeAll(async () => {
      // paper D imports a module that imports another (Y two imports away), and paper E
      await put("Toolkit/Deep/Y.lean", "-- Y v1\n");
      await put("Toolkit/Deep/X.lean", "import Toolkit.Deep.Y\n-- X v1\n");
      await put("Papers/D.lean", "import Papers.D.Main\n");
      await put("Papers/D/Main.lean", mainD("v1"));
      await put("Papers/E.lean", "import Papers.E.Main\n");
      await put("Papers/E/Main.lean", "-- E v1\n");
      await fakeLake(root, ["build"]);
      await publishGeneration(root, await liveSig(), quiet);
    });

    it("its read set: the papers copied and not written, their import closure, the pinned top-level files but the library's barrel", async () => {
      const { C } = await paperCommit("d0", "v0");
      const m = manifest(C);
      expect(m.sources.map((x) => x.rel)).toEqual(["Papers/D/Main.lean"]);
      expect(m.build).toEqual([]);
      expect(m.reads?.map((r) => r.rel)).toEqual([
        "CandidateScan.lean", "Papers/D.lean", "Papers/E.lean", "Papers/E/Main.lean", "Toolkit/Deep/X.lean", "Toolkit/Deep/Y.lean", "lake-manifest.json", "lakefile.toml", "lean-toolchain",
      ]);
      expect(m.reads?.find((r) => r.rel === "Toolkit/Deep/Y.lean")?.sha).toBe(sha("-- Y v1\n"));
      await rm(C, { recursive: true, force: true });
    }, 120_000);

    it("prepared on N, it lands after an unrelated toolkit commit: CURRENT and its archive untouched, the journal's base N+1", async () => {
      const { C } = await paperCommit("d1", "v2");
      const id = manifest(C).id;
      const N = (await currentGeneration(root))!.gen;
      await toolkitLands("d1t", "Toolkit/B.lean", "-- B d1\n");
      const cur = (await currentGeneration(root))!;
      expect(cur.gen).toBe(N + 1);
      const before = archive(cur.gen);
      let journaled: number | null = null;
      COMMIT_STEP.at = async (s) => { if (s === "journaled") journaled = (await readCommitJournal(root))!.base.gen; };
      lakeCalls.length = 0;
      const lines: string[] = [];
      expect(await commitToolkit(root, C, { log: (l) => lines.push(l) })).toMatchObject({ kind: "landed", gen: N + 1, slow: false });
      expect(journaled).toBe(N + 1);
      expect(await currentGeneration(root)).toEqual(cur);
      expect(archive(cur.gen)).toMatchObject({ ino: before.ino, mtimeMs: before.mtimeMs });
      expect(existsSync(path.join(gensDir(root), `${N + 2}.tar.zst`))).toBe(false);
      expect(read("Papers/D/Main.lean")).toBe(mainD("v2"));
      expect(lakeCalls.filter((c) => c.cwd === root).map((c) => c.args[1])).toEqual(["--no-build"]);
      expect(lines.join("\n")).toMatch(new RegExp(`${id} landed as generation ${N + 1} \\(prepared on generation ${N}: off its base`));
      expect(await events(id)).toEqual([["off-base", null]]);
    }, 120_000);

    it("base-moved when a module two imports away changed, naming it", async () => {
      const { C } = await paperCommit("d2", "v3");
      await toolkitLands("d2t", "Toolkit/Deep/Y.lean", "-- Y v2\n");
      expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/Toolkit\/Deep\/Y.lean, which it read on generation \d+, changed since/) });
      expect(read("Papers/D/Main.lean")).toBe(mainD("v2"));
      expect(await events(manifest(C).id)).toEqual([["reads-miss", "Toolkit/Deep/Y.lean"]]);
    }, 120_000);

    it("base-moved when a paper it copied and did not write changed", async () => {
      const { C } = await paperCommit("d3", "v4");
      await writeTextAtomic(path.join(root, "Papers", "E", "Main.lean"), "-- E edited by its run\n");
      await toolkitLands("d3t", "Toolkit/B.lean", "-- B d3\n");
      expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/^Papers\/E\/Main.lean, which it read/) });
      expect(read("Papers/D/Main.lean")).toBe(mainD("v2"));
    }, 120_000);

    it("a commit that writes the toolkit or carries a declaration stays strict, even with its read set intact", async () => {
      const decl = { name: "Papers.D.thm", module: "Toolkit.A", division: "Foundations", origin: { kind: "proposal" as const, slug: "d4" }, date: "2026-11-11", decision: "accept", used_by: [] };
      const ledgered = await paperCommit("d4", "v5", { ledger: [decl] });
      const writesToolkit = await promotion("d5", ["D"], async (ws) => {
        await writeTextAtomic(path.join(ws, "Papers", "D", "Main.lean"), mainD("v5"));
        await writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A d5\n");
      });
      // (each has its read set, intact: still strict — the commit checks what it writes)
      for (const { C } of [ledgered, writesToolkit]) expect(manifest(C).reads?.length).toBeGreaterThan(0);
      await toolkitLands("d4t", "Toolkit/B.lean", "-- B d4\n");
      for (const { C } of [ledgered, writesToolkit]) expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/the toolkit is generation \d+, not \d+/) });
      expect(read("Papers/D/Main.lean")).toBe(mainD("v2"));
    }, 120_000);

    it("a manifest without a read set is strict; the off-switch makes every commit strict, read at each commit", async () => {
      const bare = await paperCommit("d7", "v6");
      const { reads: _, ...rest } = manifest(bare.C);
      await writeFile(path.join(bare.C, "manifest.json"), JSON.stringify(rest));
      const switched = await paperCommit("d8", "v6");
      await toolkitLands("d7t", "Toolkit/B.lean", "-- B d7\n");
      expect(await commitToolkit(root, bare.C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/the toolkit is generation/) });
      await writeFile(strictBaseSwitch(root), "");
      try {
        expect(await commitToolkit(root, switched.C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/the toolkit is generation/) });
      } finally { await unlink(strictBaseSwitch(root)); }
      expect(await commitToolkit(root, switched.C, { log: quiet })).toMatchObject({ kind: "landed" });
      expect(read("Papers/D/Main.lean")).toBe(mainD("v6"));
    }, 120_000);

    it("an open flux session still gives wait", async () => {
      const { C } = await paperCommit("d9", "v7");
      await toolkitLands("d9t", "Toolkit/B.lean", "-- B d9\n");
      const flux = path.join(root, ".lake", "paperformalizer", "toolkit-flux");
      await writeFile(flux, "{}");
      try {
        expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "wait", why: expect.stringMatching(/flux/) });
      } finally { await unlink(flux); }
      expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "landed" });
    }, 120_000);

    it("queued off its base, it keeps its archive through another commit's sweep, and lands without one (2026-11-11)", async () => {
      const { C } = await paperCommit("dq", "vq");
      const strict = await promotion("dqs", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A dq\n"));
      await toolkitLands("dq1", "Toolkit/B.lean", "-- B dq1\n");
      // this one's sweep sees CURRENT past both bases: the strict commit's archive goes, the paper-only one's stays
      await toolkitLands("dq2", "Toolkit/B.lean", "-- B dq2\n");
      expect(manifest(C).base.gen).toBeLessThan((await currentGeneration(root))!.gen);
      expect(existsSync(path.join(C, "gen.tar.zst"))).toBe(true);
      expect(existsSync(path.join(strict.C, "gen.tar.zst"))).toBe(false);
      expect(existsSync(path.join(strict.C, "manifest.json"))).toBe(true);
      // off its base it never needs it
      await rm(path.join(C, "gen.tar.zst"));
      expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "landed" });
      expect(read("Papers/D/Main.lean")).toBe(mainD("vq"));
      await rm(strict.C, { recursive: true, force: true });
    }, 120_000);

    it("a toolkit stamped clean but not published: published inside its locks, then the paper-only commit lands onto it", async () => {
      const { C } = await paperCommit("d10", "v8");
      const N = (await currentGeneration(root))!.gen;
      await writeTextAtomic(path.join(root, "Toolkit", "B.lean"), "-- B by an old-path promotion, d10\n");
      await fakeLake(root, ["build"]);
      const scope = await toolkitScope(await toolkitLayout(root));
      if ("why" in scope) throw new Error(scope.why);
      await recordToolkitClean(root, await liveSig(), scope);
      const lines: string[] = [];
      expect(await commitToolkit(root, C, { log: (l) => lines.push(l) })).toMatchObject({ kind: "landed", gen: N + 1 });
      expect(lines.join("\n")).toMatch(/stamped clean but not published — published as generation/);
      expect(await currentGeneration(root)).toMatchObject({ gen: N + 1, sig: await liveSig() });
      expect(read("Papers/D/Main.lean")).toBe(mainD("v8"));
    }, 120_000);

    it("a toolkit commit's read set and adds: the new module's closure read; its adds recorded beside the generation it made, pruned with the archives; none without", async () => {
      const adds = [{ name: "Toolkit.Deep.z", hash: "h-z" }];
      const { C } = await promotion("a1", [], async (ws) => {
        await writeTextAtomic(path.join(ws, "Toolkit", "Deep", "Z.lean"), "import Toolkit.Deep.Y\n-- Z new\n");
      }, { adds });
      const m = manifest(C);
      expect(m.adds).toEqual(adds);
      expect(m.reads?.map((r) => r.rel)).toEqual(expect.arrayContaining(["Toolkit/Deep/Y.lean", "lakefile.toml"]));
      expect(m.reads?.map((r) => r.rel)).not.toContain("Toolkit/Deep/Z.lean");
      const N = (await currentGeneration(root))!.gen;
      expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "landed", gen: N + 1 });
      expect(JSON.parse(readFileSync(addsRecordFile(root, N + 1), "utf8"))).toEqual({ gen: N + 1, id: m.id, base: N, adds });
      // without adds: no record; a paper-only commit makes no generation: none either
      await toolkitLands("a2", "Toolkit/B.lean", "-- B a2\n");
      expect(existsSync(addsRecordFile(root, N + 2))).toBe(false);
      const { C: Cp } = await paperCommit("a3", "a3", { adds });
      expect(await commitToolkit(root, Cp, { log: quiet })).toMatchObject({ kind: "landed", gen: N + 2 });
      expect(readdirSync(path.join(gensDir(root), "adds"))).toEqual([`${N + 1}.json`]);
      // pruned with its archive
      for (let k = 0; k < KEEP_GENERATIONS; k++) await toolkitLands(`a4-${k}`, "Toolkit/B.lean", `-- B a4 ${k}\n`);
      expect(existsSync(path.join(gensDir(root), `${N + 1}.tar.zst`))).toBe(false);
      expect(existsSync(addsRecordFile(root, N + 1))).toBe(false);
    }, 120_000);

    for (const step of ["journaled", "sources"]) {
      it(`off its base, killed at "${step}": the roll-forward lands it and never publishes its archive`, async () => {
        const { C } = await paperCommit(`dk-${step}`, `at ${step}`);
        await toolkitLands(`dk-${step}t`, "Toolkit/B.lean", `-- B dk ${step}\n`);
        const cur = (await currentGeneration(root))!;
        const before = archive(cur.gen);
        COMMIT_STEP.at = async (s) => { if (s === step) throw new Error(`killed at ${s}`); };
        await expect(commitToolkit(root, C, { log: quiet })).rejects.toThrow(`killed at ${step}`);
        COMMIT_STEP.at = realStep;
        expect((await readCommitJournal(root))?.base.gen).toBe(cur.gen);
        expect(await recoverCommit(root, quiet)).toMatchObject({ kind: "landed" });
        expect(read("Papers/D/Main.lean")).toBe(mainD(`at ${step}`));
        expect(await currentGeneration(root)).toEqual(cur);
        expect(archive(cur.gen)).toMatchObject({ ino: before.ino, mtimeMs: before.mtimeMs });
        expect(existsSync(path.join(gensDir(root), `${cur.gen + 1}.tar.zst`))).toBe(false);
        expect(existsSync(commitJournalFile(root))).toBe(false);
      }, 120_000);
    }

    describe("a path dependency", () => {
      const mainG = (v: string) => `import Dep.Basic\n-- G ${v}\n`;
      const dep = (rel: string) => path.join(dir, "top", "dep", rel);
      const publishLive = async () => { await fakeLake(root, ["build"]); await publishGeneration(root, await liveSig(), quiet); };
      beforeAll(async () => {
        // the toolkit requires `../dep` by path; paper G imports its module
        await put("lakefile.toml", `${read("lakefile.toml")}[[require]]\nname = "Dep"\npath = "../dep"\n`);
        await put("lake-manifest.json", JSON.stringify({ packages: [{ type: "path", name: "Dep", dir: "../dep" }] }));
        await put("dep/lakefile.toml", 'name = "Dep"\n[[lean_lib]]\nname = "Dep"\n', path.join(dir, "top"));
        await put("dep/Dep/Basic.lean", "import Dep.More\n-- dep v1\n", path.join(dir, "top"));
        await put("dep/Dep/More.lean", "-- more v1\n", path.join(dir, "top"));
        await put("Papers/G.lean", "import Papers.G.Main\n");
        await put("Papers/G/Main.lean", mainG("v1"));
        await publishLive();
      });

      it("is in the read set, its lakefile and manifest too; its lakefile changed: base-moved", async () => {
        await put("dep/lake-manifest.json", "{}\n", path.join(dir, "top"));
        await publishLive();
        const { C } = await promotion("g1", ["G"], (ws) => writeTextAtomic(path.join(ws, "Papers", "G", "Main.lean"), mainG("v2")));
        expect(manifest(C).reads?.map((r) => r.rel)).toEqual(expect.arrayContaining(["../dep/Dep/Basic.lean", "../dep/Dep/More.lean", "../dep/lakefile.toml", "../dep/lake-manifest.json"]));
        await writeTextAtomic(dep("lakefile.toml"), 'name = "Dep"\n[leanOptions]\nautoImplicit = false\n[[lean_lib]]\nname = "Dep"\n');
        await publishLive();
        expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/^\.\.\/dep\/lakefile\.toml, which it read/) });
        expect(read("Papers/G/Main.lean")).toBe(mainG("v1"));
      }, 120_000);

      it("edited during the verdict (after the prepare, before the commit is prepared): no read set — refused off its base", async () => {
        const w = await prepareWorkspace(root, "g2", ["G"], { localRoot: local });
        await writeTextAtomic(path.join(w.path, "Papers", "G", "Main.lean"), mainG("v3"));
        // (P's dependency is a live link: the edit is seen there, and published as the next generation)
        await writeTextAtomic(dep("Dep/More.lean"), "-- more v2\n");
        await publishLive();
        await fakeLake(w.path, ["build"]);
        const lines: string[] = [];
        const C = await prepareCommit(root, w.path, { log: (l) => lines.push(l) });
        expect(manifest(C).reads).toBeUndefined();
        expect(lines.join("\n")).toMatch(/a path dependency changed during its verdict \(\.\.\/dep\/Dep\/More\.lean\)/);
        expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/the toolkit is generation/) });
        expect(read("Papers/G/Main.lean")).toBe(mainG("v1"));
      }, 120_000);

      it("a paper-only commit that registers a paper in the papers' barrel lands off its base, the barrel merged", async () => {
        const { C } = await promotion("g3", ["G"], async (ws) => {
          await writeTextAtomic(path.join(ws, "Papers", "G", "Main.lean"), mainG("v4"));
          await writeTextAtomic(path.join(ws, "Papers.lean"), `${read("Papers.lean", ws)}import Papers.G\n`);
        });
        expect(manifest(C).barrel).toEqual({ rel: "Papers.lean", imports: ["import Papers.G"] });
        expect(manifest(C).reads).toBeDefined();
        await toolkitLands("g3t", "Toolkit/B.lean", "-- B g3\n");
        // (a paper registered meanwhile stands beside it)
        await writeTextAtomic(path.join(root, "Papers.lean"), `${read("Papers.lean")}import Papers.Z\n`);
        const N = (await currentGeneration(root))!.gen;
        expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "landed", gen: N });
        expect(read("Papers.lean")).toMatch(/import Papers\.G\n[\s\S]*import Papers\.Z/);
        expect(read("Papers/G/Main.lean")).toBe(mainG("v4"));
      }, 120_000);
    });

    it("a queued commit bound to its base leaves the queue, base-moved, once CURRENT moves — never when the journal names it", async () => {
      const settled = (p: Promise<unknown>) => { const s = { done: false }; void p.then(() => { s.done = true; }, () => { s.done = true; }); return s; };
      const pause = (ms: number) => new Promise((r) => setTimeout(r, ms));
      const { C } = await promotion("q1", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A q1\n"));
      await withPromotionLock(root, async () => {
        const p = commitToolkit(root, C, { log: quiet });
        const s = settled(p);
        await pause(1500);
        expect(s.done).toBe(false);
        // another writer publishes (a hand edit's publisher): the queued commit gives up, the lock still held here
        await writeTextAtomic(path.join(root, "Toolkit", "B.lean"), "-- B q1\n");
        await fakeLake(root, ["build"]);
        await publishGeneration(root, await liveSig(), quiet);
        expect(await p).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/seen before the promotion lock/) });
      });
      // asked when CURRENT has moved already: never queued
      expect(await commitToolkit(root, C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/seen before the promotion lock/) });
      // its own journal on file (killed past its commit point): it waits for the lock however CURRENT moves
      const { C: C2 } = await promotion("q2", [], (ws) => writeTextAtomic(path.join(ws, "Toolkit", "A.lean"), "-- A q2\n"));
      COMMIT_STEP.at = async (st) => { if (st === "journaled") throw new Error("killed"); };
      await expect(commitToolkit(root, C2, { log: quiet })).rejects.toThrow("killed");
      COMMIT_STEP.at = realStep;
      const file = path.join(gensDir(root), "CURRENT.json");
      const cur = readFileSync(file, "utf8");
      let queued: Promise<unknown> = Promise.resolve();
      await withPromotionLock(root, async () => {
        queued = commitToolkit(root, C2, { log: quiet });
        const s = settled(queued);
        await writeFile(file, JSON.stringify({ ...JSON.parse(cur), gen: 999 }));
        await pause(2500);
        expect(s.done).toBe(false);
        await writeFile(file, cur);
      });
      // (the lock released: it takes it and rolls its own commit forward)
      expect(await queued).toMatchObject({ kind: "landed" });
      expect(read("Toolkit/A.lean")).toBe("-- A q2\n");
    }, 120_000);
  });
});
