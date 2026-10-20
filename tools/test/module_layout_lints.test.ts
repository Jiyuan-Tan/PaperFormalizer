import { afterEach, describe, expect, it } from "vitest";
import { execFile } from "node:child_process";
import { mkdtemp, mkdir, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { promisify } from "node:util";
import { TOOLKIT_JSON } from "./toolkit/helpers.js";

const exec = promisify(execFile);
const TOOLS = path.resolve(import.meta.dirname, "..");
const HEADERS = path.join(TOOLS, "bin", "lint_module_headers.ts");
const temporary: string[] = [];

async function tree(files: Record<string, string>): Promise<string> {
  const root = await mkdtemp(path.join(os.tmpdir(), "module-layout-lint-"));
  temporary.push(root);
  for (const [name, source] of Object.entries(files)) {
    const target = path.join(root, name);
    await mkdir(path.dirname(target), { recursive: true });
    await writeFile(target, source, "utf8");
  }
  return root;
}
async function run(script: string, args: string[], cwd = TOOLS) {
  return exec(process.execPath, ["--import", "tsx/esm", script, ...args], { cwd, env: process.env });
}
async function jsonFailure(script: string, args: string[]): Promise<unknown> {
  try { await run(script, args); throw new Error("expected lint failure"); }
  catch (error) { return JSON.parse((error as { stdout: string }).stdout); }
}
afterEach(async () => { await Promise.all(temporary.splice(0).map((dir) => rm(dir, { recursive: true, force: true }))); });

describe("lint_module_headers", () => {
  it("checks header, imports, blanket section placement, and exposure comment-aware", async () => {
    const root = await tree({
      "Causalean/Good.lean": "module\npublic import Mathlib.Data.Nat.Basic\n\n/-! Good. -/\n\n@[expose] public section\n-- def hidden : Nat := 0\ndef visible : Nat := 0\n",
      "Causalean/Bad.lean": "module\nimport Mathlib.Data.Nat.Basic\n/-! Bad. -/\npublic section\npublic section\ndef x : Nat := 0\n",
      "Causalean/Unexposed.lean": "module\npublic import Mathlib.Data.Nat.Basic\n/-! Unexposed. -/\npublic section\ndef x : Nat := 0\n",
      "Causalean/Private.lean": "module\n-- private import\nimport Mathlib.Tactic\n/-! Private imports. -/\n\npublic section\ntheorem x : True := trivial\n",
      "Causalean/Barrel.lean": "module\npublic import Mathlib.Data.Nat.Basic\n/-! Barrel with no declarations. -/\n",
      "Causalean/Theorems.lean": "module\npublic import Mathlib.Data.Nat.Basic\n/-! Theorems. -/\n@[expose] public section\ntheorem x : True := trivial\n",
      "Causalean/CommentImports.lean": "module\npublic import Mathlib.Data.Nat.Basic\n/-! Example only: import Fake.DocExample -/\npublic section\ntheorem x : True := trivial\n",
      "Causalean/Legacy.lean": "import Mathlib\ntheorem old : True := trivial\n",
    });
    const result = await jsonFailure(HEADERS, ["--paths", path.join(root, "Causalean"), "--strict", "--json"] as string[]) as { findings: { rule: string }[] };
    expect(result.findings.map((f) => f.rule)).toEqual(expect.arrayContaining([
      "missing-module-header", "non-public-import", "blanket-public-section", "expose-section",
    ]));
    expect(result.findings).toContainEqual(expect.objectContaining({ path: expect.stringContaining("Theorems.lean"), rule: "expose-section", severity: "warning" }));
    expect(result.findings.some((f) => String((f as { path?: string }).path).includes("Barrel.lean"))).toBe(false);
    expect(result.findings.some((f) => String((f as { path?: string }).path).includes("CommentImports.lean"))).toBe(false);
    const allowed = await run(HEADERS, ["--paths", path.join(root, "Causalean", "Legacy.lean"), "--json"]);
    expect(JSON.parse(allowed.stdout)).toMatchObject({ findings: [], legacyCount: 1 });
  });

});

describe("lint_module_headers — default inputs", () => {
  it("lints the toolkit library and the papers library of the toolkit found from the cwd", async () => {
    const root = await tree({
      "leansmith.json": JSON.stringify(TOOLKIT_JSON),
      "Toolkit.lean": "module\n\n/-! # Toolkit -/\n\npublic section\n",
      "Toolkit/Foundations/Bad.lean": "module\nimport A\n\n/-! docs -/\n\npublic section\n",
      "Papers.lean": "module\n\n/-! # Papers -/\n\npublic section\n",
      "runs/x/Stray.lean": "not a module",
    });
    const result = await jsonFailure(HEADERS, ["--json", "--strict", "--toolkit", root]) as {
      findings: { path: string; rule: string }[];
    };
    expect(result.findings.map((f) => path.relative(root, path.resolve(TOOLS, f.path)))).toEqual([path.join("Toolkit", "Foundations", "Bad.lean")]);
  });
});
