// compat 2026-11-11: remove after the processes started before this merge have exited (≤2 days)
// The shims for modules loaded before the stale-cleanup merge, called the old way: each takes the
// path the switches selected (they were all on).
import { mkdtemp, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { localScansOn, localScansSwitch } from "../../src/proposals/candidate_scan.js";
import { realApplyDeps } from "../../src/proposals/gate.js";
import { commitPrepared } from "../../src/proposals/local_moves.js";
import { commitToolkit } from "../../src/shared/commit.js";
import { localCommitStudiesSwitch } from "../../src/substrate/local_coordinate.js";
import type { ToolkitConfig } from "../../src/toolkit/config.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

describe("compat shims (one deploy)", () => {
  it("the retired switches: their paths as before, local scans always on", () => {
    const cfg = { toolkitRoot: "/tk" };
    expect(localCommitStudiesSwitch(cfg)).toBe(path.join("/tk", ".lake", "paperformalizer", "local-commit-studies"));
    expect(localScansSwitch(cfg)).toBe(path.join("/tk", ".lake", "paperformalizer", "local-scans"));
    expect(localScansOn(cfg)).toBe(true);
  });

  it("commitPrepared takes the old arity (an ApplyDeps in position 2) as the new: the same commit asked for", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "compat-"));
    tmp.push(root);
    const cfg = { toolkitRoot: root } as ToolkitConfig;
    const C = path.join(root, "no-such-commit");
    const quiet = () => {};
    // no prepared commit there: both arities reach commitToolkit with `C`, never with the deps shifted in
    await expect(commitPrepared(cfg, C, false, quiet, "x")).rejects.toThrow(`${C} is no prepared commit`);
    await expect(commitPrepared(cfg, realApplyDeps, C, false, quiet, "x")).rejects.toThrow(`${C} is no prepared commit`);
  });

  it("commitToolkit still takes the old `settle` option", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "compat-"));
    tmp.push(root);
    await expect(commitToolkit(root, path.join(root, "none"), { log: () => {}, settle: async () => {} })).rejects.toThrow(/is no prepared commit/);
  });
});
