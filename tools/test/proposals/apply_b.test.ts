// Round-B apply helpers: the library check (the daily one's build of every paper) and the papers'
// declared names (the paper-name check of a move). The apply itself, end to end: local_moves.test.ts.
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { libraryCheck, paperDeclaredNames } from "../../src/proposals/apply_b.js";
import type { ApplyDeps } from "../../src/proposals/gate.js";
import type { ToolkitConfig } from "../../src/toolkit/config.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

describe("the library check", () => {
  it("a module killed for memory (137): the library is built again with less parallelism, twice at most; still killed, it is `killed`, not a break", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "libcheck-"));
    const killed = (m: string) => `✖ [1/9] Building ${m} (300s)\nerror: Lean exited with code 137\n`;
    const broken = (m: string) => `✖ [4/9] Building ${m}\nerror: ${m.split(".").join("/")}.lean:1:1: x\n`;
    const logs = [
      `${killed("Papers.A.Big")}${killed("Papers.B.Huge")}${killed("Papers.C.Real")}${broken("Papers.D.Bad")}error: build failed`,
      // a dependent of a killed module, built only now, breaks
      `${killed("Papers.B.Huge")}${broken("Papers.C.Real")}${broken("Papers.D.Bad")}${broken("Papers.A.Dep")}error: build failed`,
      `${killed("Papers.B.Huge")}${broken("Papers.C.Real")}${broken("Papers.D.Bad")}${broken("Papers.A.Dep")}error: build failed`,
    ];
    const calls: Array<[string, string | undefined]> = [];
    const d = {
      run: async (cmd: string, _cwd: string, opts?: { env?: Record<string, string> }) => {
        calls.push([cmd, opts?.env?.LEAN_NUM_THREADS]);
        return { code: 1, log: logs[calls.length - 1]! };
      },
    } as unknown as ApplyDeps;
    const cfg = { toolkitRoot: dir, papersLib: "Papers" } as ToolkitConfig;
    const r = await libraryCheck(cfg, d, path.join(dir, "library.log"));
    expect(calls).toEqual([["lake build Papers", undefined], ["lake build Papers", "2"], ["lake build Papers", "1"]]);
    expect(r).toEqual({ breaks: ["Papers.A.Dep", "Papers.C.Real", "Papers.D.Bad"], killed: ["Papers.B.Huge"] });
    expect(await readFile(path.join(dir, "library.log"), "utf8")).toContain("LEAN_NUM_THREADS=1 lake build Papers");
    // the re-build passes: nothing left
    const ok = { run: async (_cmd: string, _cwd: string, opts?: { env?: Record<string, string> }) => (opts?.env ? { code: 0, log: "" } : { code: 1, log: killed("Papers.A.Big") }) } as unknown as ApplyDeps;
    expect(await libraryCheck(cfg, ok, path.join(dir, "library.log"))).toEqual({ breaks: [], killed: [] });
    // a re-build that fails naming nothing is no pass
    const mute = { run: async (_cmd: string, _cwd: string, opts?: { env?: Record<string, string> }) => ({ code: 1, log: opts?.env ? "error: build failed" : killed("Papers.A.Big") }) } as unknown as ApplyDeps;
    expect(await libraryCheck(cfg, mute, path.join(dir, "library.log"))).toEqual({ breaks: ["LEAN_NUM_THREADS=2 lake build Papers"], killed: [] });
    await rm(dir, { recursive: true, force: true });
  });
});

describe("paperDeclaredNames", () => {
  it("finds a name a paper's source declares; a paper's tmp/ scratch is not one of its sources", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "paper-names-"));
    tmp.push(root);
    const decl = "namespace Toolkit.Tricks.Arith\n\ntheorem le_succ_self (n : ℕ) : n ≤ n + 1 := Nat.le_succ n\n\nend Toolkit.Tricks.Arith\n";
    await mkdir(path.join(root, "Papers", "Other", "tmp"), { recursive: true });
    await writeFile(path.join(root, "Papers", "Other", "tmp", "Try.lean"), decl);
    const cfg = { toolkitRoot: root, papersLib: "Papers" } as ToolkitConfig;
    expect(await paperDeclaredNames(cfg, ["Toolkit.Tricks.Arith.le_succ_self"])).toEqual(new Set());
    await writeFile(path.join(root, "Papers", "Other", "Mod.lean"), `module\n\n${decl}`);
    expect(await paperDeclaredNames(cfg, ["Toolkit.Tricks.Arith.le_succ_self", "Toolkit.Tricks.Arith.other"])).toEqual(new Set(["Toolkit.Tricks.Arith.le_succ_self"]));
  });
});
