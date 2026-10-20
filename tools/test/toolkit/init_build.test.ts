import { spawnSync } from "node:child_process";
import { mkdtempSync, rmSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterAll, expect, it, vi } from "vitest";
import { initToolkit } from "../../src/toolkit/init.js";

vi.mock("node:child_process", () => ({ spawnSync: vi.fn(() => ({ status: 0, stdout: "", stderr: "" })) }));
vi.mock("../../src/local_config.js", () => ({ bashBinary: () => "E:/Git/bin/bash.exe" }));

const tmp = mkdtempSync(path.join(os.tmpdir(), "tc-init-build-"));
afterAll(() => rmSync(tmp, { recursive: true, force: true }));

it("fetches a library's cache through the configured Git Bash before building", () => {
  initToolkit({ dir: tmp, domains: ["causal"], owner: { name: "Test" }, build: true, log: () => {} });
  const calls = vi.mocked(spawnSync).mock.calls;
  const cache = calls.findIndex(([bin]) => bin === "E:/Git/bin/bash.exe");
  expect(calls[cache]).toEqual(["E:/Git/bin/bash.exe", ["scripts/fetch_build_cache.sh"], { cwd: path.join(tmp, ".lake/packages/Causalean"), stdio: "inherit" }]);
  expect(calls.slice(0, cache).some(([bin, args]) => bin === "lake" && JSON.stringify(args) === JSON.stringify(["exe", "cache", "get"]))).toBe(true);
  expect(calls.slice(cache + 1).some(([bin, args]) => bin === "lake" && JSON.stringify(args) === JSON.stringify(["build"]))).toBe(true);
});
