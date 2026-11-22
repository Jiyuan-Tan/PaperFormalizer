// Additive toolkit commits (`src/shared/commit.ts`, 2026-11-11, step 2): a commit that adds new
// modules — its barrels and the index changed by additions alone — lands on a later generation
// without a rebase, its barrels and index merged into the live ones; a clash with what landed since
// (a name, a statement hash, an import), a generation without an adds record, an edit to an existing
// module or the off-switch keep it strict (base-moved). Lake is the stand-in of `commit.test.ts`; the
// toolkit index is made by a stand-in of `toolkit_index` (one entry per `-- decl` line of a module the
// root reaches, sorted as Lean sorts strings); the import pre-check is a stand-in that fails when two
// modules it imports declare the same name (an `-- instance` line too, which no index lists).
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, readFileSync } from "node:fs";
import { chmod, mkdir, mkdtemp, readdir, readFile, rm, unlink, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterAll, beforeAll, beforeEach, describe, expect, it } from "vitest";
import { stampedClean } from "../../src/shared/build_mutex.js";
import { headerImports, toolkitLayout, toolkitSignature } from "../../src/shared/build_inputs.js";
import {
  ADDITIVE_LIMITS, additiveShape, COMMIT_LAKE, COMMIT_PRECHECK, noAdditiveSwitch, overlayLib, COMMIT_STEP, commitJournalFile, commitToolkit, prepareCommit, prepareWorkspace, readCommitJournal, recoverCommit, strictBaseSwitch,
  type CommitAdd, type CommitManifest,
} from "../../src/shared/commit.js";
import { readCommitEvents } from "../../src/shared/lock_holds.js";
import { writeTextAtomic } from "../../src/shared/json_atomic.js";
import { addsRecordFile, currentGeneration, gensDir, publishGeneration } from "../../src/shared/workspace.js";
import { insertImportSorted } from "../../src/toolkit/barrels.js";
import { recheckPaperNames } from "../../src/proposals/local_moves.js";
import { TOOLKIT_JSON, tk } from "../toolkit/helpers.js";

const haveTools = (() => { try { execFileSync("bash", ["-c", "command -v zstd && command -v flock"]); return true; } catch { return false; } })();
const sha = (s: string | Buffer) => createHash("sha256").update(s).digest("hex");
const quiet = () => {};

let dir: string;
let root: string;
let local: string;
let PATH: string | undefined;
const realLake = COMMIT_LAKE.run;
const realStep = COMMIT_STEP.at;
const realPrecheck = COMMIT_PRECHECK.run;
const put = async (rel: string, text: string, base = root) => {
  await mkdir(path.dirname(path.join(base, rel)), { recursive: true });
  await writeFile(path.join(base, rel), text);
};
const read = (rel: string, base = root) => readFileSync(path.join(base, rel), "utf8");

// ─── a stand-in Lake (as `commit.test.ts`'s, its exe of CandidateScan alone) ──────────────────────────────────────────────────────
const lakeCalls: { cwd: string; args: string[]; cap?: number }[] = [];
/** `killCapped`: the next real builds run under a cap (an additive commit's) are killed, as by it. */
const lakeFaults = { killCapped: 0 };
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
  for (const m of await moduleFiles(cwd)) {
    const s = sha(await readFile(path.join(cwd, m)));
    const base = path.join(".lake", "build", "lib", "lean", m.slice(0, -".lean".length));
    files.set(`${base}.olean`, `olean ${s}`);
    files.set(`${base}.olean.hash`, sha(`olean ${s}`));
    files.set(`${base}.trace`, s);
  }
  // (the exe imports no toolkit module, as the live ones: a new module never relinks it)
  files.set(path.join(".lake", "build", "bin", "candidate_scan"), `exe ${sha(await readFile(path.join(cwd, "CandidateScan.lean")))}`);
  return files;
}
async function fakeLake(cwd: string, args: string[], cap: { maxTotalMs?: number } = {}): Promise<{ code: number | null; out: string }> {
  lakeCalls.push({ cwd, args, ...(cap.maxTotalMs !== undefined ? { cap: cap.maxTotalMs } : {}) });
  if (!args.includes("--no-build") && cap.maxTotalMs !== undefined && lakeFaults.killCapped > 0) { lakeFaults.killCapped--; return { code: null, out: "killed (its cap)" }; }
  const want = await expected(cwd);
  const stale: string[] = [];
  for (const [f, text] of want) if ((await readFile(path.join(cwd, f), "utf8").catch(() => null)) !== text) stale.push(f);
  if (args.includes("--no-build")) return stale.length ? { code: 3, out: `error: ${stale[0]} is out of date` } : { code: 0, out: "All targets up-to-date" };
  const rank = (f: string) => (f.endsWith(".trace") ? 2 : f.endsWith(".hash") ? 1 : 0);
  for (const f of stale.sort((a, b) => rank(a) - rank(b))) {
    await unlink(path.join(cwd, f)).catch(() => {});
    await put(f, want.get(f)!, cwd);
  }
  return { code: 0, out: "Build completed successfully" };
}
const upToDate = async (cwd: string) => (await fakeLake(cwd, ["build", "--no-build"])).code === 0;
const liveSig = async () => toolkitSignature(await toolkitLayout(root));

// ─── a stand-in `toolkit_index` ───────────────────────────────────────────────────────────────────
/** The modules the root `Toolkit` reaches in `cwd` (their sources), each once. */
async function reached(cwd: string, srcOf: (mod: string) => string = (mod) => path.join(cwd, ...mod.split(".")) + ".lean"): Promise<Map<string, string>> {
  const out = new Map<string, string>();
  const go = async (mod: string) => {
    if (out.has(mod) || !(mod === "Toolkit" || mod.startsWith("Toolkit."))) return;
    const text = await readFile(srcOf(mod), "utf8");
    out.set(mod, text);
    for (const imp of headerImports(text)) await go(imp);
  };
  await go("Toolkit");
  return out;
}
/** `doc/toolkit_index.json` of `cwd` as `toolkit_index` writes it: one entry per `-- decl <name> <kind>`
 *  line of a module the root reaches, sorted by name as Lean sorts strings (by code point). */
async function genIndex(cwd: string): Promise<string> {
  const mods = await reached(cwd);
  const modules: Record<string, string | null> = {};
  const entries: Array<Record<string, unknown>> = [];
  for (const [mod, text] of mods) {
    modules[mod] = /^-- doc (.*)$/m.exec(text)?.[1] ?? null;
    for (const m of text.matchAll(/^-- decl (\S+) (\S+)$/gm)) entries.push({ name: m[1], module: mod, kind: m[2], statement: `stmt of ${m[1]}`, line: 1 });
  }
  entries.sort((a, b) => Buffer.compare(Buffer.from(a.name as string), Buffer.from(b.name as string)));
  return `${JSON.stringify({ commit: "c0ffee", toolchain: "leanprover/lean4:v4.33.0", modules, entries }, null, 2)}\n`;
}
/** An index without its `commit`, its modules as a set: what a regenerated one must equal. */
const indexValue = (text: string) => {
  const j = JSON.parse(text) as { modules: Record<string, unknown>; entries: unknown[]; toolchain: string };
  return { toolchain: j.toolchain, modules: Object.fromEntries(Object.entries(j.modules).sort(([a], [b]) => (a < b ? -1 : 1))), entries: j.entries };
};

// ─── a stand-in import pre-check ──────────────────────────────────────────────────────────────────
const prechecks: string[] = [];
async function fakePrecheck(r: string, C: string, text: string): Promise<{ code: number | null; out: string }> {
  prechecks.push(text);
  // (a new module's source is the commit's: `C/src`; else the shared tree's)
  const srcOf = (mod: string) => {
    const rel = path.join(...mod.split(".")) + ".lean";
    return existsSync(path.join(C, "src", rel)) ? path.join(C, "src", rel) : path.join(r, rel);
  };
  const seen = new Map<string, string>();
  const mods = new Map<string, string>();
  const go = async (mod: string) => {
    if (mods.has(mod) || !mod.startsWith("Toolkit")) return;
    const t = await readFile(srcOf(mod), "utf8");
    mods.set(mod, t);
    for (const imp of headerImports(t)) await go(imp);
  };
  for (const imp of headerImports(text)) await go(imp);
  for (const [mod, t] of mods) {
    for (const m of t.matchAll(/^-- (?:decl|instance) (\S+)/gm)) {
      const was = seen.get(m[1]!);
      if (was && was !== mod) return { code: 1, out: `error: import failed, environment already contains '${m[1]}' from ${was}` };
      seen.set(m[1]!, mod);
    }
  }
  return { code: 0, out: "" };
}

/** Run `slug`'s promotion: a workspace, `edit` in it, built, its index regenerated; its prepared commit. */
async function promotion(slug: string, edit: (ws: string) => Promise<void>, extra: Parameters<typeof prepareCommit>[2] = {}) {
  const w = await prepareWorkspace(root, slug, [], { localRoot: local });
  await edit(w.path);
  await writeTextAtomic(path.join(w.path, "doc", "toolkit_index.json"), await genIndex(w.path));
  await fakeLake(w.path, ["build"]);
  return { ws: w.path, C: await prepareCommit(root, w.path, extra) };
}
/** A study's edit: a new module `Toolkit.<division>.<name>` (importing A), its lines, the barrel's import. */
const addModule = (division: "Foundations" | "Tricks", name: string, lines: string[]) => async (ws: string) => {
  const dep = division === "Foundations" ? "Toolkit.Foundations.A" : "Toolkit.Tricks.T";
  await writeTextAtomic(path.join(ws, "Toolkit", division, `${name}.lean`), `module\n\npublic import ${dep}\n-- doc ${name}\n${lines.join("\n")}\n`);
  const barrel = path.join(ws, "Toolkit", `${division}.lean`);
  await writeTextAtomic(barrel, insertImportSorted(await readFile(barrel, "utf8"), `public import Toolkit.${division}.${name}`));
};
/** An additive study: a new module declaring `decls` (name → statement hash), its adds those. */
const study = (slug: string, division: "Foundations" | "Tricks", name: string, decls: Record<string, string>, more: string[] = []) => {
  const adds: CommitAdd[] = Object.entries(decls).map(([n, hash]) => ({ name: n, hash }));
  return promotion(slug, addModule(division, name, [...adds.map((a) => `-- decl ${a.name} theorem`), ...more]), { adds });
};
const manifest = (C: string) => JSON.parse(readFileSync(path.join(C, "manifest.json"), "utf8")) as CommitManifest;
const events = async (id: string) => (await readCommitEvents(root)).filter((e) => e.id === id).map((e) => e.event);

beforeAll(async () => {
  dir = await mkdtemp(path.join(os.tmpdir(), "commit-additive-"));
  root = path.join(dir, "top", "tk");
  local = path.join(dir, "local");
  await put("paperformalizer.json", JSON.stringify({ ...TOOLKIT_JSON, base: TOOLKIT_JSON.base.map((b) => (b.name === "Base" ? { ...b, index: "../tools/data/libraries.json" } : b)) }));
  await put("tools/data/libraries.json", "{}\n", path.join(dir, "top"));
  await put("lakefile.toml", 'name = "tk"\n[[lean_lib]]\nname = "Toolkit"\n[[lean_lib]]\nname = "Papers"\n[[lean_exe]]\nname = "candidate_scan"\nroot = "CandidateScan"\n');
  await put("lean-toolchain", "leanprover/lean4:v4.33.0\n");
  await put("lake-manifest.json", "{}\n");
  await put("Toolkit.lean", "module\n\npublic import Toolkit.Foundations\npublic import Toolkit.Tricks\n\n/-! # Toolkit -/\n");
  await put("Toolkit/Foundations.lean", "module\n\npublic import Toolkit.Foundations.A\n\n/-!\n# Foundations\n\nBarrel.\n-/\n\npublic section\n");
  await put("Toolkit/Foundations/A.lean", "module\n-- doc A\n-- decl Toolkit.Foundations.a theorem\n-- decl Toolkit.Foundations.b' theorem\n");
  await put("Toolkit/Tricks.lean", "module\n\npublic import Toolkit.Tricks.T\n\npublic section\n");
  await put("Toolkit/Tricks/T.lean", "module\n-- doc T\n-- decl Toolkit.Tricks.t theorem\n");
  await put("Toolkit/Staging/S.lean", "-- a study's staging\n");
  await put("CandidateScan.lean", "-- scan\n");
  await put("Papers.lean", "-- papers\n");
  await put("Papers/P.lean", "import Papers.P.Main\n");
  await put("Papers/P/Main.lean", "-- P v1\n");
  await put("doc/ledger.json", JSON.stringify({ version: 1, declarations: [], decisions: [] }));
  await put("doc/toolkit_index.json", await genIndex(root));
  await mkdir(path.join(root, "runs"), { recursive: true });
  await put(".toolkit-promote.lock", "1\n");
  await mkdir(path.join(root, ".lake", "packages"), { recursive: true });
  await put("bin/lean", "#!/bin/sh\necho 'Lean (version 4.0.0, test)'\n", dir);
  await chmod(path.join(dir, "bin", "lean"), 0o755);
  PATH = process.env.PATH;
  process.env.PATH = `${path.join(dir, "bin")}:${PATH}`;
  COMMIT_LAKE.run = fakeLake;
  COMMIT_PRECHECK.run = fakePrecheck;
  await fakeLake(root, ["build"]);
  await mkdir(gensDir(root), { recursive: true });
  expect((await publishGeneration(root, await liveSig(), quiet))?.gen).toBe(1);
});
afterAll(async () => {
  process.env.PATH = PATH;
  COMMIT_LAKE.run = realLake;
  COMMIT_PRECHECK.run = realPrecheck;
  await rm(dir, { recursive: true, force: true });
});
beforeEach(() => {
  lakeCalls.length = 0;
  prechecks.length = 0;
  lakeFaults.killCapped = 0;
  COMMIT_STEP.at = realStep;
  COMMIT_PRECHECK.run = fakePrecheck;
});

describe.skipIf(process.platform === "win32" || !haveTools)("additive toolkit commits", () => {
  it("three studies prepared on one base all land: the second and third merged onto the newer generations, built for real, the index a regenerated one", async () => {
    const G = (await currentGeneration(root))!.gen;
    // (names Lean and JavaScript sort differently: ﬀ U+FB00 before 𝓝 U+1D4DD by code point, after it by UTF-16 unit)
    const x = await study("x", "Foundations", "X", { "Toolkit.Foundations.bﬀ": "hx", "Toolkit.Foundations.x": "hx2" });
    const y = await study("y", "Tricks", "Y", { "Toolkit.Tricks.y": "hy" });
    const z = await study("z", "Foundations", "Z", { "Toolkit.Foundations.b𝓝": "hz", "Toolkit.Foundations.b'z": "hz2" });
    for (const s of [x, y, z]) expect(manifest(s.C)).toMatchObject({ base: { gen: G }, reads: expect.any(Array), adds: expect.any(Array) });
    expect(await additiveShape(root, await toolkitLayout(root), z.C, manifest(z.C))).toEqual({ modules: ["Toolkit.Foundations.Z"], barrels: ["Toolkit/Foundations.lean"], index: true });
    const [yid, zid] = [manifest(y.C).id, manifest(z.C).id];
    // x on its base: the strict path (its archive published)
    expect(await commitToolkit(root, x.C, { log: quiet })).toMatchObject({ kind: "landed", gen: G + 1, slow: false });
    expect(existsSync(addsRecordFile(root, G + 1))).toBe(true);
    // y: additive onto G+1 — merged, built for real, then Lake finds the tree up to date
    lakeCalls.length = 0;
    const lines: string[] = [];
    expect(await commitToolkit(root, y.C, { log: (l) => lines.push(l) })).toMatchObject({ kind: "landed", gen: G + 2, slow: false, additive: true });
    expect(lakeCalls.filter((c) => c.cwd === root).map((c) => c.args.slice(0, 2).join(" "))).toEqual(["build Toolkit", "build --no-build"]);
    expect(lines.join("\n")).toMatch(new RegExp(`${yid}: prepared on generation ${G}, additive — rebased onto generation ${G + 1}`));
    expect(lines.join("\n")).toMatch(new RegExp(`${yid} landed as generation ${G + 2} \\(additive: prepared on generation ${G}, merged onto ${G + 1}`));
    // z: additive onto G+2, the same barrel as x's
    expect(await commitToolkit(root, z.C, { log: quiet })).toMatchObject({ kind: "landed", gen: G + 3, additive: true });
    // the pre-check imported the merged Foundations barrel (x's and z's modules) beside the live Tricks barrel
    expect(prechecks.at(-1)).toBe("module\n\npublic import Toolkit.Foundations.A\npublic import Toolkit.Foundations.X\npublic import Toolkit.Foundations.Z\npublic import Toolkit.Tricks\n");
    expect(read("Toolkit/Foundations.lean")).toBe("module\n\npublic import Toolkit.Foundations.A\npublic import Toolkit.Foundations.X\npublic import Toolkit.Foundations.Z\n\n/-!\n# Foundations\n\nBarrel.\n-/\n\npublic section\n");
    expect(read("Toolkit/Tricks.lean")).toBe("module\n\npublic import Toolkit.Tricks.T\npublic import Toolkit.Tricks.Y\n\npublic section\n");
    // the merged index is the one `toolkit_index` makes of the tree now (entries in Lean's order)
    expect(indexValue(read("doc/toolkit_index.json"))).toEqual(indexValue(await genIndex(root)));
    expect((JSON.parse(read("doc/toolkit_index.json")) as { entries: Array<{ name: string }> }).entries.map((e) => e.name).filter((n) => n.startsWith("Toolkit.Foundations.b")))
      .toEqual(["Toolkit.Foundations.b'", "Toolkit.Foundations.b'z", "Toolkit.Foundations.bﬀ", "Toolkit.Foundations.b𝓝"]);
    // Lake: the shared tree up to date; stamped; CURRENT its signature, packed; each one's adds recorded
    expect(await upToDate(root)).toBe(true);
    const sig = await liveSig();
    expect(await stampedClean(root)).toEqual({ sig });
    expect(await currentGeneration(root)).toMatchObject({ gen: G + 3, sig });
    expect(existsSync(path.join(gensDir(root), `${G + 3}.tar.zst`))).toBe(true);
    expect(JSON.parse(read(path.relative(root, addsRecordFile(root, G + 3))))).toMatchObject({ gen: G + 3, id: zid, base: G + 2 });
    expect(await events(yid)).toEqual(["additive"]);
    expect(await events(zid)).toEqual(["additive"]);
    expect(existsSync(y.C)).toBe(false);
    expect(existsSync(commitJournalFile(root))).toBe(false);
  }, 180_000);

  it("base-moved when a name it adds landed since (the live index), its barrel and index untouched", async () => {
    const d1 = await study("d1", "Foundations", "D1", { "Toolkit.Foundations.dup": "hd1" });
    const d2 = await study("d2", "Foundations", "D2", { "Toolkit.Foundations.dup": "hd2" });
    expect(await commitToolkit(root, d1.C, { log: quiet })).toMatchObject({ kind: "landed" });
    const [barrel, index] = [read("Toolkit/Foundations.lean"), read("doc/toolkit_index.json")];
    expect(await commitToolkit(root, d2.C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/Toolkit\.Foundations\.dup, which its index adds, is in the live index/) });
    expect([read("Toolkit/Foundations.lean"), read("doc/toolkit_index.json")]).toEqual([barrel, index]);
    expect(existsSync(path.join(root, "Toolkit", "Foundations", "D2.lean"))).toBe(false);
    expect(await events(manifest(d2.C).id)).toEqual(["additive-miss"]);
    // (the prepared commit untouched: never rebased)
    expect(existsSync(path.join(d2.C, "manifest.prepared.json"))).toBe(false);
  }, 180_000);

  it("base-moved when a statement it adds landed since under another name (the adds record's hash)", async () => {
    const h1 = await study("h1", "Tricks", "H1", { "Toolkit.Tricks.h1": "same-statement" });
    const h2 = await study("h2", "Foundations", "H2", { "Toolkit.Foundations.h2": "same-statement" });
    expect(await commitToolkit(root, h1.C, { log: quiet })).toMatchObject({ kind: "landed" });
    expect(await commitToolkit(root, h2.C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/Toolkit\.Foundations\.h2 states what Toolkit\.Tricks\.h1 states \(statement hash\), added by generation \d+/) });
    expect(read("Toolkit/Foundations.lean")).not.toMatch(/H2/);
  }, 180_000);

  it("base-moved when Lean does not import the merged barrels together (a clash no index lists)", async () => {
    const i1 = await study("i1", "Foundations", "I1", { "Toolkit.Foundations.i1": "hi1" }, ["-- instance Toolkit.instClash"]);
    const i2 = await study("i2", "Tricks", "I2", { "Toolkit.Tricks.i2": "hi2" }, ["-- instance Toolkit.instClash"]);
    expect(await commitToolkit(root, i1.C, { log: quiet })).toMatchObject({ kind: "landed" });
    const lines: string[] = [];
    expect(await commitToolkit(root, i2.C, { log: (l) => lines.push(l) })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/Lean does not import the merged barrels with its modules \(exit 1\): .*environment already contains 'Toolkit.instClash'/) });
    expect(read("Toolkit/Tricks.lean")).not.toMatch(/I2/);
    expect(existsSync(path.join(root, "Toolkit", "Tricks", "I2.lean"))).toBe(false);
    expect(await currentGeneration(root)).toMatchObject({ sig: await liveSig() });
  }, 180_000);

  it("strict when a generation since its base has no adds record (a strict commit, gardening, the publisher)", async () => {
    const n1 = await study("n1", "Foundations", "N1", { "Toolkit.Foundations.n1": "hn1" });
    // a toolkit commit without adds: its generation has no record
    const s = await promotion("n1s", addModule("Tricks", "NS", ["-- decl Toolkit.Tricks.ns theorem"]));
    expect(await commitToolkit(root, s.C, { log: quiet })).toMatchObject({ kind: "landed" });
    const g = (await currentGeneration(root))!.gen;
    expect(existsSync(addsRecordFile(root, g))).toBe(false);
    // (seen before the promotion lock: it never queues; under the locks — a caller holding them — the same)
    expect(await commitToolkit(root, n1.C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/the toolkit is generation \d+, not \d+ \(seen before the promotion lock\)/) });
    expect(await commitToolkit(root, n1.C, { log: quiet, held: "promotion" })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(new RegExp(`generation ${g} has no record of what it added`)) });
  }, 180_000);

  it("strict when it edits an existing module, or its barrel beyond an import, or has no adds", async () => {
    const e1 = await promotion("e1", async (ws) => {
      await addModule("Foundations", "E1", ["-- decl Toolkit.Foundations.e1 theorem"])(ws);
      await writeTextAtomic(path.join(ws, "Toolkit", "Foundations", "A.lean"), `${read("Toolkit/Foundations/A.lean")}-- edited\n`);
    }, { adds: [{ name: "Toolkit.Foundations.e1", hash: "he1" }] });
    const e2 = await promotion("e2", async (ws) => {
      await addModule("Foundations", "E2", ["-- decl Toolkit.Foundations.e2 theorem"])(ws);
      const b = path.join(ws, "Toolkit", "Foundations.lean");
      await writeTextAtomic(b, (await readFile(b, "utf8")).replace("Barrel.", "Barrel, edited."));
    }, { adds: [{ name: "Toolkit.Foundations.e2", hash: "he2" }] });
    const e3 = await promotion("e3", addModule("Foundations", "E3", ["-- decl Toolkit.Foundations.e3 theorem"]));
    const t = await toolkitLayout(root);
    expect(await additiveShape(root, t, e1.C, manifest(e1.C))).toEqual({ strict: "it writes Toolkit/Foundations/A.lean, neither a new module nor a barrel nor the index" });
    expect(await additiveShape(root, t, e3.C, manifest(e3.C))).toEqual({ strict: "it names no declaration it adds (no adds)" });
    const other = await study("e0", "Tricks", "E0", { "Toolkit.Tricks.e0": "he0" });
    expect(await commitToolkit(root, other.C, { log: quiet })).toMatchObject({ kind: "landed" });
    // (bound to its base: refused before the promotion lock)
    expect(await commitToolkit(root, e1.C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/the toolkit is generation \d+, not \d+ \(seen before the promotion lock\)/) });
    expect(await commitToolkit(root, e3.C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/the toolkit is generation \d+, not \d+/) });
    // (shaped as additive: its contents checked under the locks)
    expect(await commitToolkit(root, e2.C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/its change to Toolkit\/Foundations.lean is not imports inserted, alone/) });
    expect(read("Toolkit/Foundations/A.lean")).not.toMatch(/edited/);
  }, 180_000);

  it("the off-switch strict-base makes it strict", async () => {
    const o1 = await study("o1", "Foundations", "O1", { "Toolkit.Foundations.o1": "ho1" });
    const o2 = await study("o2", "Tricks", "O2", { "Toolkit.Tricks.o2": "ho2" });
    expect(await commitToolkit(root, o1.C, { log: quiet })).toMatchObject({ kind: "landed" });
    await writeFile(strictBaseSwitch(root), "");
    try {
      expect(await additiveShape(root, await toolkitLayout(root), o2.C, manifest(o2.C))).toEqual({ strict: "the off-switch strict-base is on file" });
      expect(await commitToolkit(root, o2.C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/the toolkit is generation \d+, not \d+/) });
    } finally { await unlink(strictBaseSwitch(root)); }
    expect(read("Toolkit/Tricks.lean")).not.toMatch(/O2/);
  }, 180_000);

  it("the off-switch no-additive makes a toolkit commit strict (before the lock too), a paper-only one still lands off its base", async () => {
    const a1 = await study("na1", "Foundations", "NA1", { "Toolkit.Foundations.na1": "hna1" });
    const a2 = await study("na2", "Tricks", "NA2", { "Toolkit.Tricks.na2": "hna2" });
    expect(await commitToolkit(root, a1.C, { log: quiet })).toMatchObject({ kind: "landed" });
    await writeFile(noAdditiveSwitch(root), "");
    try {
      expect(await additiveShape(root, await toolkitLayout(root), a2.C, manifest(a2.C))).toEqual({ strict: "the off-switch no-additive is on file" });
      expect(await commitToolkit(root, a2.C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/\(seen before the promotion lock\)/) });
      expect(await commitToolkit(root, a2.C, { log: quiet, held: "promotion" })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/strict: the off-switch no-additive is on file/) });
    } finally { await unlink(noAdditiveSwitch(root)); }
    // (off again: it lands, read at the commit)
    expect(await commitToolkit(root, a2.C, { log: quiet })).toMatchObject({ kind: "landed", additive: true });
  }, 180_000);

  it("strict when its barrel gains an import of a module not its own", async () => {
    const f1 = await promotion("f1", async (ws) => {
      await addModule("Foundations", "F1", ["-- decl Toolkit.Foundations.f1 theorem"])(ws);
      const b = path.join(ws, "Toolkit", "Foundations.lean");
      await writeTextAtomic(b, insertImportSorted(await readFile(b, "utf8"), "public import Toolkit.Tricks.T"));
    }, { adds: [{ name: "Toolkit.Foundations.f1", hash: "hf1" }] });
    const other = await study("f0", "Tricks", "F0", { "Toolkit.Tricks.f0": "hf0" });
    expect(await commitToolkit(root, other.C, { log: quiet })).toMatchObject({ kind: "landed" });
    expect(await commitToolkit(root, f1.C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/Toolkit\/Foundations.lean gains public import Toolkit.Tricks.T, not one of its own new modules/) });
  }, 180_000);

  it("its pre-check killed (over its cap): base-moved before the commit point, the event with its laps", async () => {
    const p1 = await study("pk1", "Foundations", "PK1", { "Toolkit.Foundations.pk1": "hpk1" });
    const p2 = await study("pk2", "Tricks", "PK2", { "Toolkit.Tricks.pk2": "hpk2" });
    expect(await commitToolkit(root, p1.C, { log: quiet })).toMatchObject({ kind: "landed" });
    expect(ADDITIVE_LIMITS).toEqual({ precheckMs: 300_000, buildMs: 600_000 });
    const chains: string[][] = [];
    COMMIT_PRECHECK.run = async (_r, _c, _t, chain = []) => { chains.push([...chain]); return { code: null, out: "killed" }; };
    expect(await commitToolkit(root, p2.C, { log: quiet })).toMatchObject({ kind: "base-moved", why: expect.stringMatching(/its import pre-check was killed \(over 300 s/) });
    // (the barrel chain's staged outputs never laid over the shared ones)
    expect(chains).toEqual([["Toolkit.Tricks", "Toolkit"]]);
    expect(existsSync(commitJournalFile(root))).toBe(false);
    expect(read("Toolkit/Tricks.lean")).not.toMatch(/PK2/);
    const ev = (await readCommitEvents(root)).filter((e) => e.id === manifest(p2.C).id);
    expect(ev).toMatchObject([{ event: "additive-miss", why: expect.stringMatching(/^strict: its import pre-check was killed/), ms: { precheck: expect.any(Number), merge: expect.any(Number) } }]);
  }, 180_000);

  it("its real build killed (over its cap): no verdict, the journal unstopped; the next holder rolls it forward with one build", async () => {
    const b1 = await study("bk1", "Foundations", "BK1", { "Toolkit.Foundations.bk1": "hbk1" });
    const b2 = await study("bk2", "Foundations", "BK2", { "Toolkit.Foundations.bk2": "hbk2" });
    const G = (await currentGeneration(root))!.gen;
    expect(await commitToolkit(root, b1.C, { log: quiet })).toMatchObject({ kind: "landed" });
    const id = manifest(b2.C).id;
    lakeFaults.killCapped = 1;
    lakeCalls.length = 0;
    expect(await commitToolkit(root, b2.C, { log: quiet })).toMatchObject({ kind: "wait", why: expect.stringMatching(/killed/) });
    expect(lakeCalls.filter((c) => c.cwd === root)).toEqual([{ cwd: root, args: expect.arrayContaining(["build", "Toolkit"]), cap: ADDITIVE_LIMITS.buildMs }]);
    expect(await readCommitJournal(root)).toMatchObject({ id });
    expect((await readCommitJournal(root))!.stopped).toBeUndefined();
    expect(await currentGeneration(root)).toMatchObject({ gen: G + 1 });
    // the next holder: forward, its real build uncapped and once
    lakeCalls.length = 0;
    expect(await recoverCommit(root, quiet)).toMatchObject({ kind: "landed", gen: G + 2 });
    expect(lakeCalls.filter((c) => c.cwd === root && !c.args.includes("--no-build")).map((c) => c.cap ?? null)).toEqual([null]);
    expect(read("Toolkit/Foundations.lean")).toMatch(/BK1\npublic import Toolkit.Foundations.BK2\n/);
    expect(await upToDate(root)).toBe(true);
    const ev = (await readCommitEvents(root)).filter((e) => e.id === id);
    expect(ev).toMatchObject([{ event: "additive-miss", why: expect.stringMatching(/^killed: its real build over the cap/), ms: { "lake-build": expect.any(Number) } }]);
  }, 180_000);

  it("landed additive: its event names the laps under the locks", async () => {
    const l1 = await study("lm1", "Foundations", "LM1", { "Toolkit.Foundations.lm1": "hlm1" });
    const l2 = await study("lm2", "Tricks", "LM2", { "Toolkit.Tricks.lm2": "hlm2" });
    expect(await commitToolkit(root, l1.C, { log: quiet })).toMatchObject({ kind: "landed" });
    const id = manifest(l2.C).id;
    expect(await commitToolkit(root, l2.C, { log: quiet })).toMatchObject({ kind: "landed", additive: true });
    const ev = (await readCommitEvents(root)).filter((e) => e.id === id);
    expect(ev).toMatchObject([{ event: "additive", ms: { precheck: expect.any(Number), rebase: expect.any(Number), "lake-build": expect.any(Number), publish: expect.any(Number) } }]);
  }, 180_000);

  for (const later of [false, true]) {
    it(`a crash after its rebase, before its journal: nothing shared written; again on ${later ? "a newer" : "the same"} CURRENT, it lands`, async () => {
      const slug = later ? "cr2" : "cr1";
      const c1 = await study(`${slug}a`, "Foundations", `${slug}A`, { [`Toolkit.Foundations.${slug}a`]: `h${slug}a` });
      const c2 = await study(`${slug}b`, "Tricks", `${slug}B`, { [`Toolkit.Tricks.${slug}b`]: `h${slug}b` });
      const c3 = await study(`${slug}c`, "Foundations", `${slug}C`, { [`Toolkit.Foundations.${slug}c`]: `h${slug}c` });
      const G = (await currentGeneration(root))!.gen;
      expect(await commitToolkit(root, c1.C, { log: quiet })).toMatchObject({ kind: "landed", gen: G + 1 });
      const [tricks, index] = [read("Toolkit/Tricks.lean"), read("doc/toolkit_index.json")];
      COMMIT_STEP.at = async (s) => { if (s === "rebased") throw new Error("killed at rebased"); };
      await expect(commitToolkit(root, c2.C, { log: quiet })).rejects.toThrow("killed at rebased");
      COMMIT_STEP.at = realStep;
      expect(await readCommitJournal(root)).toBeNull();
      expect([read("Toolkit/Tricks.lean"), read("doc/toolkit_index.json")]).toEqual([tricks, index]);
      expect(existsSync(path.join(root, "Toolkit", "Tricks", `${slug}B.lean`))).toBe(false);
      expect(manifest(c2.C)).toMatchObject({ base: { gen: G + 1 }, rebased: { from: { gen: G } } });
      expect(existsSync(path.join(c2.C, "precheck"))).toBe(false);
      if (later) expect(await commitToolkit(root, c3.C, { log: quiet })).toMatchObject({ kind: "landed", gen: G + 2 });
      const out = await commitToolkit(root, c2.C, { log: quiet });
      expect(out).toMatchObject({ kind: "landed", gen: later ? G + 3 : G + 2, additive: true });
      expect(read("Toolkit/Tricks.lean")).toMatch(new RegExp(`public import Toolkit.Tricks.${slug}B\n`));
      if (later) expect(read("Toolkit/Foundations.lean")).toMatch(new RegExp(`${slug}A\npublic import Toolkit.Foundations.${slug}C\n`));
      expect(indexValue(read("doc/toolkit_index.json"))).toEqual(indexValue(await genIndex(root)));
      expect(await upToDate(root)).toBe(true);
      expect(await currentGeneration(root)).toMatchObject({ sig: await liveSig() });
      if (!later) await rm(c3.C, { recursive: true, force: true });
    }, 180_000);
  }

  it("a rebased journal rolled forward by old code (which knows no `rebased`): the slow path lands it", async () => {
    const o1 = await study("old1", "Foundations", "Old1", { "Toolkit.Foundations.old1": "hold1" });
    const o2 = await study("old2", "Foundations", "Old2", { "Toolkit.Foundations.old2": "hold2" });
    const G = (await currentGeneration(root))!.gen;
    expect(await commitToolkit(root, o1.C, { log: quiet })).toMatchObject({ kind: "landed" });
    COMMIT_STEP.at = async (s) => { if (s === "journaled") throw new Error("killed at journaled"); };
    await expect(commitToolkit(root, o2.C, { log: quiet })).rejects.toThrow("killed at journaled");
    COMMIT_STEP.at = realStep;
    // what old code reads: the manifest without the field it does not know
    const { rebased: _, ...plain } = manifest(o2.C);
    await writeFile(path.join(o2.C, "manifest.json"), JSON.stringify(plain));
    lakeCalls.length = 0;
    expect(await recoverCommit(root, quiet)).toMatchObject({ kind: "landed", gen: G + 2, slow: true });
    expect(lakeCalls.filter((c) => c.cwd === root).map((c) => c.args[1])).toEqual(["Toolkit"]);
    expect(read("Toolkit/Foundations.lean")).toMatch(/Old1\npublic import Toolkit.Foundations.Old2\n/);
    expect(indexValue(read("doc/toolkit_index.json"))).toEqual(indexValue(await genIndex(root)));
    expect(await upToDate(root)).toBe(true);
    expect(await stampedClean(root)).toEqual({ sig: await liveSig() });
  }, 180_000);

  it("its caller's recheck runs under the locks, before anything: a refusal there writes nothing", async () => {
    const r1 = await study("rc1", "Foundations", "RC1", { "Toolkit.Foundations.rc1": "hrc1" });
    let calls = 0;
    let at = 0;
    await expect(commitToolkit(root, r1.C, { log: quiet, recheck: async () => { calls++; at = Date.now(); throw Object.assign(new Error("rc1: declared in a paper"), { name: "PaperNameClash" }); } })).rejects.toThrow(/declared in a paper/);
    // (inside a hold of the promotion lock: its record spans the recheck)
    const { readLockHolds } = await import("../../src/shared/lock_holds.js");
    expect((await readLockHolds(root)).some((h) => h.lock === "promote" && Date.parse(h.got) <= at && at <= Date.parse(h.released))).toBe(true);
    expect(calls).toBe(1);
    expect(existsSync(path.join(root, "Toolkit", "Foundations", "RC1.lean"))).toBe(false);
    expect(existsSync(commitJournalFile(root))).toBe(false);
    expect(await commitToolkit(root, r1.C, { log: quiet, recheck: async () => { calls++; } })).toMatchObject({ kind: "landed" });
    expect(calls).toBe(2);
  }, 180_000);

  for (const step of ["journaled", "sources", "build-files"]) {
    it(`rolls forward an additive commit killed at "${step}": its rebased manifest, the merged barrel and index, built and published`, async () => {
      const slug = `k${step.replace(/-/g, "")}`;
      const k1 = await study(`${slug}1`, "Foundations", `${slug}One`, { [`Toolkit.Foundations.${slug}1`]: `h${slug}1` });
      const k2 = await study(`${slug}2`, "Foundations", `${slug}Two`, { [`Toolkit.Foundations.${slug}2`]: `h${slug}2` }, ["-- the second"]);
      const G = (await currentGeneration(root))!.gen;
      expect(await commitToolkit(root, k1.C, { log: quiet })).toMatchObject({ kind: "landed", gen: G + 1 });
      const id = manifest(k2.C).id;
      COMMIT_STEP.at = async (s) => { if (s === step) throw new Error(`killed at ${s}`); };
      await expect(commitToolkit(root, k2.C, { log: quiet })).rejects.toThrow(`killed at ${step}`);
      COMMIT_STEP.at = realStep;
      // the journal names it, on G+1; its C rebased onto G+1, the prepared manifest kept, no archive
      expect(await readCommitJournal(root)).toMatchObject({ id, base: { gen: G + 1 } });
      const m = manifest(k2.C);
      expect(m).toMatchObject({ base: { gen: G + 1 }, rebased: { from: { gen: G } } });
      expect(JSON.parse(read("manifest.prepared.json", k2.C))).toMatchObject({ base: { gen: G } });
      expect(existsSync(path.join(k2.C, "gen.tar.zst"))).toBe(false);
      expect(m.build.map((b) => b.rel).filter((r) => /Toolkit(\/Foundations)?\.(olean|trace)/.test(r))).toEqual([]);
      expect(m.sources.find((s) => s.rel === "Toolkit/Foundations.lean")?.before).toBe(sha(read(path.join("orig", "Toolkit", "Foundations.lean"), k2.C)));
      // the next holder rolls it forward: the real build, the shared tree packed
      expect(await recoverCommit(root, quiet)).toMatchObject({ kind: "landed", gen: G + 2 });
      expect(existsSync(commitJournalFile(root))).toBe(false);
      expect(read("Toolkit/Foundations.lean")).toMatch(new RegExp(`public import Toolkit.Foundations.${slug}One\npublic import Toolkit.Foundations.${slug}Two\n`));
      expect(read(`Toolkit/Foundations/${slug}Two.lean`)).toMatch(/the second/);
      expect(indexValue(read("doc/toolkit_index.json"))).toEqual(indexValue(await genIndex(root)));
      expect(await upToDate(root)).toBe(true);
      const sig = await liveSig();
      expect(await stampedClean(root)).toEqual({ sig });
      expect(await currentGeneration(root)).toMatchObject({ gen: G + 2, sig });
      expect(JSON.parse(read(path.relative(root, addsRecordFile(root, G + 2))))).toMatchObject({ id, base: G + 1 });
    }, 180_000);
  }

  it("the pre-check's library: the shared one with the staged outputs laid over it, only their directories made, nothing shared written", async () => {
    const shared = path.join(dir, "ov", "shared");
    const delta = path.join(dir, "ov", "delta");
    await put("Toolkit.olean", "root", shared);
    await put("Toolkit/Foundations.olean", "barrel", shared);
    await put("Toolkit/Foundations/A.olean", "A", shared);
    await put("Toolkit/Foundations/Deep/D.olean", "D", shared);
    await put("Toolkit/Tricks/T.olean", "T", shared);
    await put("Toolkit/Foundations/New.olean", "new", delta);
    await put("Toolkit/Foundations/Sub/N2.olean.server", "new2", delta);
    const out = path.join(dir, "ov", "out");
    await put("Toolkit/Foundations.olean", "stale barrel", delta);
    await overlayLib(shared, delta, out, { skip: (rel) => rel === path.join("Toolkit", "Foundations.olean") });
    expect(read("Toolkit/Foundations.olean", out)).toBe("barrel");
    const { lstat: ls, readlink } = await import("node:fs/promises");
    for (const [rel, text] of [["Toolkit.olean", "root"], ["Toolkit/Foundations/A.olean", "A"], ["Toolkit/Foundations/Deep/D.olean", "D"], ["Toolkit/Tricks/T.olean", "T"], ["Toolkit/Foundations/New.olean", "new"], ["Toolkit/Foundations/Sub/N2.olean.server", "new2"]]) {
      expect(read(rel!, out)).toBe(text);
    }
    expect((await ls(path.join(out, "Toolkit"))).isDirectory()).toBe(true);
    expect((await ls(path.join(out, "Toolkit", "Foundations"))).isDirectory()).toBe(true);
    expect(await readlink(path.join(out, "Toolkit", "Tricks"))).toBe(path.join(shared, "Toolkit", "Tricks"));
    expect(await readlink(path.join(out, "Toolkit", "Foundations", "Deep"))).toBe(path.join(shared, "Toolkit", "Foundations", "Deep"));
    expect(existsSync(path.join(shared, "Toolkit", "Foundations", "New.olean"))).toBe(false);
  });

  it("the target names checked against the papers once more before the lock: one a paper declares since refuses the commit", async () => {
    const q = await study("q1", "Foundations", "Q1", { "Toolkit.Foundations.q1": "hq1" });
    await expect(recheckPaperNames(tk(root), q.C, [{ id: "q1", names: ["Toolkit.Foundations.q1"] }], [])).resolves.toBeUndefined();
    await put("Papers/P/Main.lean", "-- P v1\ntheorem Toolkit.Foundations.q1 : True := trivial\n");
    try {
      await expect(recheckPaperNames(tk(root), q.C, [{ id: "q1", names: ["Toolkit.Foundations.q1"] }], [])).rejects.toThrow(/q1: `Toolkit.Foundations.q1` is declared in a paper already/);
      expect(existsSync(q.C)).toBe(false);
    } finally { await put("Papers/P/Main.lean", "-- P v1\n"); }
  }, 180_000);
});
