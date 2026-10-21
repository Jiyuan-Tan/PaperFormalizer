// bin/search.ts: sources from `--index <any path>` (repeatable) or `--toolkit <root>`.
import { execFile } from "node:child_process";
import { mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { promisify } from "node:util";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";

const exec = promisify(execFile);
const TOOLS = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const TSX_CLI = path.resolve(TOOLS, "node_modules", "tsx", "dist", "cli.mjs");
const SEARCH = path.resolve(TOOLS, "bin", "search.ts");

function writeIndex(file: string, lib: string, name: string, doc: string): void {
  mkdirSync(path.dirname(file), { recursive: true });
  writeFileSync(file, JSON.stringify({
    commit: "abcdef1234", toolchain: "t", modules: { [`${lib}.Stat.Boot`]: "Bootstrap intervals." },
    entries: [{
      name: `${lib}.Stat.${name}`, kind: "theorem", module: `${lib}.Stat.Boot`, file: `${lib}/Stat/Boot.lean`,
      line: 1, statement: "coverage ≥ 1 - α", doc, refs: [], axioms: [], usesSorry: false,
    }],
  }));
}

function search(args: string[], cwd: string, env: NodeJS.ProcessEnv = {}) {
  const e = { ...process.env, ...env };
  delete e.PAPERFORMALIZER_TOOLKIT;
  delete e.INIT_CWD;
  return exec(process.execPath, [TSX_CLI, SEARCH, ...args], { cwd, env: e });
}

describe("bin/search.ts", () => {
  it("accepts index files at arbitrary paths and tags hits by library", async () => {
    const dir = mkdtempSync(path.join(os.tmpdir(), "search-idx-"));
    const a = path.join(dir, "one", "decls.json");
    const b = path.join(dir, "two", "whatever_index.json");
    writeIndex(a, "Alpha", "percentile_interval", "The bootstrap percentile interval covers.");
    writeIndex(b, "Beta", "percentile_bound", "A percentile interval bound.");
    const { stdout } = await search(["--index", a, "--index", b, "bootstrap percentile interval"], dir);
    expect(stdout).toContain("Alpha.Stat.percentile_interval   [Alpha]");
    expect(stdout).toContain("Beta.Stat.percentile_bound   [Beta]");
    expect(stdout).toMatch(/scope: Alpha, Beta only/);
  });

  it("derives the sources from a toolkit's paperformalizer.json (relative index path)", async () => {
    const dir = mkdtempSync(path.join(os.tmpdir(), "search-tk-"));
    writeIndex(path.join(dir, "base", "doc", "library_index.json"), "Base", "percentile_interval", "Bootstrap percentile interval.");
    const tk = path.join(dir, "tk");
    mkdirSync(tk, { recursive: true });
    writeFileSync(path.join(tk, "paperformalizer.json"), JSON.stringify({
      version: 1, owner: { name: "T" },
      toolkit: { lib: "Toolkit", papers_lib: "Papers", divisions: ["Foundations"] },
      base: [{ name: "Base", kind: "path", path: "../base", index: "../base/doc/library_index.json" }],
      lean: { toolchain: "leanprover/lean4:v4.33.0" },
    }));
    const { stdout } = await search(["--toolkit", tk, "percentile interval"], dir);
    expect(stdout).toContain("Base.Stat.percentile_interval   [Base]");
  });

  it("refuses --index together with --toolkit", async () => {
    const dir = mkdtempSync(path.join(os.tmpdir(), "search-both-"));
    await expect(search(["--index", "x.json", "--toolkit", dir, "q"], dir)).rejects.toMatchObject({ code: 1 });
  });
});
