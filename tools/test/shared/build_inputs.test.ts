// A build is skipped only when every input it reads is provably unchanged since a green build of the
// same targets: the paper's Lean, the toolkit's, the path dependencies' libraries, the lakefiles,
// manifest and toolchain. Any write changes the signature; anything it cannot vouch for (an import
// of another paper, a dependency whose libraries it cannot locate) is a doubt, and doubt builds.
import { chmod, mkdir, mkdtemp, readFile, rename, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { buildRunModules } from "../../src/formalization/proof_review_loop.js";
import { TOOLKIT_JSON } from "../toolkit/helpers.js";
import { greenBuildCurrent, headerImports, isDoubt, readClosure, recordGreenBuild, sourceSignature, TOOLCHAIN_RETRY, toolchainOf, toolkitLayout, toolkitSignature } from "../../src/shared/build_inputs.js";

let root: string;
let cfg: { toolkitRoot: string; toolkitLibDir: string };
let paper: string;
const write = async (rel: string, text: string) => {
  await mkdir(path.dirname(path.join(root, rel)), { recursive: true });
  await writeFile(path.join(root, rel), text);
};
beforeEach(async () => {
  root = await mkdtemp(path.join(os.tmpdir(), "build-inputs-"));
  cfg = { toolkitRoot: path.join(root, "tk"), toolkitLibDir: path.join(root, "tk", "Toolkit") };
  paper = path.join(root, "tk", "Papers", "Toy");
  await write("tk/lakefile.toml", 'name = "t"\n[[lean_lib]]\nname = "Toolkit"\n[[lean_lib]]\nname = "Papers"\n');
  await write("tk/lean-toolchain", "leanprover/lean4:v4.33.0\n");
  await write("tk/lake-manifest.json", JSON.stringify({ packages: [{ type: "path", name: "Dep", dir: "../dep" }, { type: "git", name: "mathlib", rev: "abc" }] }));
  await write("dep/lakefile.toml", 'name = "Dep"\n[[lean_lib]]\nname = "Dep"\n');
  await write("dep/Dep/Basic.lean", "def d : Nat := 0\n");
  await write("dep/Scratch/Unused.lean", "-- not a library of the package\n");
  await write("tk/Toolkit.lean", "import Toolkit.A\n");
  await write("tk/Toolkit/A.lean", "def a : Nat := 0\n");
  await write("tk/Papers/Toy.lean", "import Papers.Toy.Main\n");
  await write("tk/Papers/Toy/Main.lean", "import Mathlib.Data.Nat.Basic\nimport Toolkit.A\nimport Dep.Basic\nimport Papers.Toy.Aux\ntheorem t : True := trivial\n");
  await write("tk/Papers/Toy/Aux.lean", "def x : Nat := 0\n");
  await write("tk/Papers/Toy/tmp/Probe.lean", "-- scratch\n");
  await write("tk/Papers/Other/Main.lean", "def o : Nat := 0\n");
});
afterEach(async () => { await rm(root, { recursive: true, force: true }); });

describe("sourceSignature", () => {
  it("is the same while nothing is written, and moves with any input the build reads", async () => {
    const sig = await sourceSignature(cfg, paper);
    expect(isDoubt(sig)).toBe(false);
    expect(await sourceSignature(cfg, paper)).toBe(sig);
    // what the build of the paper does not read leaves it alone
    await write("tk/Papers/Other/Main.lean", "def o : Nat := 1\n");
    await write("tk/Papers/Toy/tmp/Probe.lean", "-- scratch 2\n");
    await write("dep/Scratch/Unused.lean", "-- still not a library\n");
    expect(await sourceSignature(cfg, paper)).toBe(sig);
    let prev = sig;
    for (const rel of ["tk/Papers/Toy/Aux.lean", "tk/Papers/Toy.lean", "tk/Toolkit/A.lean", "tk/Toolkit.lean", "dep/Dep/Basic.lean",
      "dep/lakefile.toml", "tk/lakefile.toml", "tk/lake-manifest.json", "tk/lean-toolchain"]) {
      // the same text, written again (an atomic write: a new inode)
      const abs = path.join(root, rel);
      const text = await readFile(abs, "utf8");
      await writeFile(`${abs}.tmp`, text);
      await rename(`${abs}.tmp`, abs);
      const now = await sourceSignature(cfg, paper);
      expect(now, rel).not.toBe(prev);
      prev = now;
    }
    await write("tk/Toolkit/New.lean", "def n : Nat := 0\n");
    expect(await sourceSignature(cfg, paper)).not.toBe(prev);
    prev = await sourceSignature(cfg, paper);
    const saved = process.env.ELAN_TOOLCHAIN;
    process.env.ELAN_TOOLCHAIN = "pf-local";
    try {
      expect(await sourceSignature(cfg, paper)).not.toBe(prev);
    } finally {
      if (saved === undefined) delete process.env.ELAN_TOOLCHAIN; else process.env.ELAN_TOOLCHAIN = saved;
    }
  });

  it("is a doubt, equal to nothing, for an import of another paper or a root module, or a dependency it cannot read", async () => {
    await write("tk/Papers/Toy/Aux.lean", "public import Papers.Other.Main\ndef x : Nat := 0\n");
    const a = await sourceSignature(cfg, paper);
    expect(isDoubt(a)).toBe(true);
    expect(await sourceSignature(cfg, paper)).not.toBe(a);
    await write("tk/Papers/Toy/Aux.lean", "import PaperFormalizerIndexCore\n");
    await write("tk/PaperFormalizerIndexCore.lean", "-- a root module\n");
    expect(isDoubt(await sourceSignature(cfg, paper))).toBe(true);
    // the paper's own tmp/ scratch is outside the signature
    await write("tk/Papers/Toy/Aux.lean", "import Papers.Toy.tmp.Probe\n");
    expect(isDoubt(await sourceSignature(cfg, paper))).toBe(true);
    await write("tk/Papers/Toy/Aux.lean", "def x : Nat := 0\n");
    expect(isDoubt(await sourceSignature(cfg, paper))).toBe(false);
    await write("dep/lakefile.toml", 'name = "Dep"\n[[lean_lib]]\nname = "Dep"\nsrcDir = "src"\n');
    expect(isDoubt(await sourceSignature(cfg, paper))).toBe(true);
    await rm(path.join(root, "dep", "lakefile.toml"));
    expect(isDoubt(await sourceSignature(cfg, paper))).toBe(true);
    await write("dep/lakefile.lean", "import Lake\nopen Lake DSL\npackage Dep\nlean_lib «Dep» where\n");
    expect(isDoubt(await sourceSignature(cfg, paper))).toBe(false);
  });
});

describe("green build records", () => {
  it("vouch for the targets built under the same signature only", async () => {
    const tk = cfg.toolkitRoot;
    const sig = await sourceSignature(cfg, paper);
    const mods = ["Papers.Toy.Aux", "Papers.Toy.Main"];
    expect(await greenBuildCurrent(tk, paper, mods, sig)).toBe(false);
    await recordGreenBuild(tk, paper, mods, sig);
    expect(await greenBuildCurrent(tk, paper, mods, sig)).toBe(true);
    expect(await greenBuildCurrent(tk, paper, ["Papers.Toy.Main"], sig)).toBe(true);
    expect(await greenBuildCurrent(tk, paper, [...mods, "Papers.Toy.New"], sig)).toBe(false);
    expect(await greenBuildCurrent(tk, paper, mods, `${sig}0`)).toBe(false);
    const doubt = "doubt:x:y";
    await recordGreenBuild(tk, paper, mods, doubt);
    expect(await greenBuildCurrent(tk, paper, mods, doubt)).toBe(false);
  });
});

describe.skipIf(process.platform === "win32")("buildRunModules", () => {
  it("builds again only when an input changed since its last green build", async () => {
    const tk = cfg.toolkitRoot;
    await write("tk/paperformalizer.json", JSON.stringify(TOOLKIT_JSON));
    const calls = path.join(root, "lake-calls.log");
    await write("bin/lake", `#!/usr/bin/env bash\necho "$*" >> ${JSON.stringify(calls)}\n[[ -f ${JSON.stringify(path.join(root, "red"))} ]] && { echo "error: red"; exit 1; }\nexit 0\n`);
    await chmod(path.join(root, "bin", "lake"), 0o755);
    const savedPath = process.env.PATH;
    process.env.PATH = `${path.join(root, "bin")}:${savedPath}`;
    const count = async () => (await readFile(calls, "utf8").catch(() => "")).split("\n").filter(Boolean).length;
    try {
      expect((await buildRunModules(tk, paper)).ok).toBe(true);
      expect(await count()).toBe(1);
      // the resume's gate on the tree it left: green, not built again
      expect((await buildRunModules(tk, paper)).ok).toBe(true);
      expect(await count()).toBe(1);
      // a write to the paper: built again, and red
      await write("red", "");
      await write("tk/Papers/Toy/Aux.lean", "def x : Nat := 1\n");
      expect((await buildRunModules(tk, paper)).ok).toBe(false);
      expect(await count()).toBe(2);
      // red is never recorded: built again while red
      expect((await buildRunModules(tk, paper)).ok).toBe(false);
      expect(await count()).toBe(3);
      await rm(path.join(root, "red"));
      expect((await buildRunModules(tk, paper)).ok).toBe(true);
      expect(await count()).toBe(4);
      // a write to the toolkit: built again
      await write("tk/Toolkit/A.lean", "def a : Nat := 1\n");
      expect((await buildRunModules(tk, paper)).ok).toBe(true);
      expect(await count()).toBe(5);
      expect((await buildRunModules(tk, paper)).ok).toBe(true);
      expect(await count()).toBe(5);
    } finally {
      process.env.PATH = savedPath;
    }
  }, 30_000);
});

describe("headerImports", () => {
  it("reads the header as Lake does: comments and strings aside, ending at the first other token", () => {
    const text = "/- import Fake.InBlock -/\nmodule\n-- import Fake.InLine\npublic import A.B\nmeta import C import all D.«e f»\nprivate import E\n\n/-! doc -/\npublic section\nimport Fake.After\n";
    expect(headerImports(text)).toEqual(["A.B", "C", "D.e f", "E"]);
    // the keyword run into a quoted name
    expect(headerImports("module\nimport«Papers».Bar\npublic import all«X».Y\n")).toEqual(["Papers.Bar", "X.Y"]);
  });
});

describe("readClosure (a paper-only commit's read set)", () => {
  it("is transitive, follows the path dependencies (their lakefiles too) and the papers, leaves other packages, and is null when it cannot be resolved", async () => {
    const tk = path.join(root, "tk");
    await write("tk/Toolkit/A.lean", "module\npublic import Toolkit.B\npublic import Mathlib.Data.Nat.Basic\n");
    await write("tk/Toolkit/B.lean", "import Dep.Basic\n");
    await write("tk/Toolkit/Unused.lean", "-- imported by nothing\n");
    await write("dep/Dep/Basic.lean", "import Dep.More\n");
    await write("dep/Dep/More.lean", "def m : Nat := 0\n");
    const t = await toolkitLayout(tk);
    const files = await readClosure(t, [path.join(tk, "Papers", "Toy", "Main.lean")]);
    expect(files?.map((f) => path.relative(tk, f)).sort()).toEqual([
      "../dep/Dep/Basic.lean", "../dep/Dep/More.lean", "../dep/lakefile.toml", "Papers/Toy/Aux.lean", "Papers/Toy/Main.lean", "Toolkit/A.lean", "Toolkit/B.lean",
    ]);
    // a source not found, the staging tree, a paper's scratch: none
    await write("tk/Toolkit/B.lean", "import Toolkit.Missing\n");
    expect(await readClosure(t, [path.join(tk, "Papers", "Toy", "Main.lean")])).toBeNull();
    await write("tk/Toolkit/B.lean", "import Toolkit.Staging.S\n");
    await write("tk/Toolkit/Staging/S.lean", "-- a study's\n");
    expect(await readClosure(t, [path.join(tk, "Papers", "Toy", "Main.lean")])).toBeNull();
    await write("tk/Papers/Toy/Aux.lean", "import Papers.Toy.tmp.Gone\n");
    expect(await readClosure(t, [path.join(tk, "Papers", "Toy", "Aux.lean")])).toBeNull();
    // a dependency whose libraries are not read off its lakefile
    await write("dep/lakefile.toml", 'name = "Dep"\n[[lean_lib]]\nname = "Dep"\nsrcDir = "src"\n');
    expect(await readClosure(t, [path.join(tk, "Toolkit", "Unused.lean")])).toBeNull();
  });
});

describe("toolkitSignature's toolchain", () => {
  it.skipIf(process.platform === "win32")("a `lean --version` that fails makes it a doubt; it is asked again only after a pause, and a version read is kept", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "tk-toolchain-"));
    const bin = path.join(root, "bin");
    await mkdir(bin);
    const failing = path.join(root, "fail");
    const asked = path.join(root, "asked");
    await writeFile(path.join(bin, "lean"), `#!/bin/sh\necho x >> ${JSON.stringify(asked)}\n[ -e ${JSON.stringify(failing)} ] && exit 1\necho "Lean (version 4.0.0, test)"\n`);
    await chmod(path.join(bin, "lean"), 0o755);
    await writeFile(failing, "");
    await writeFile(path.join(root, "Toolkit.lean"), "module\n");
    const PATH = process.env.PATH;
    process.env.PATH = `${bin}:${PATH}`;
    try {
      const t = await toolkitLayout(root);
      expect(await toolchainOf(root)).toBeNull();
      // within the pause a failure is not asked again (a hanging lean is not waited on twice)
      expect(isDoubt(await toolkitSignature(t))).toBe(true);
      expect((await readFile(asked, "utf8")).trim().split("\n")).toHaveLength(1);
      await rm(failing);
      expect(isDoubt(await toolkitSignature(t))).toBe(true);
      // after the pause it is asked again, and the version read is kept
      TOOLCHAIN_RETRY.ms = 0;
      const sig = await toolkitSignature(t);
      expect(isDoubt(sig)).toBe(false);
      expect(await toolchainOf(root)).toMatch(/lean=Lean \(version 4\.0\.0, test\)/);
      expect(await toolkitSignature(t)).toBe(sig);
      expect((await readFile(asked, "utf8")).trim().split("\n")).toHaveLength(2);
    } finally {
      TOOLCHAIN_RETRY.ms = 5 * 60_000;
      process.env.PATH = PATH;
      await rm(root, { recursive: true, force: true });
    }
  });
});

