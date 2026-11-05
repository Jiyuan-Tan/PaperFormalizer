// documentModules end to end, with lake and the model replaced: a pass is checked from the source
// text, and one build confirms it after the last pass.
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { documentModules, type DocstringTarget, type LakeRun } from "../../src/formalization/stage5_docstrings.js";
import { promptPath } from "../../src/paths.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import type { PipelineContext } from "../../src/types.js";

const FILE = "Papers/T/A.lean";
const ORIGINAL = [
  "theorem foo (x : Nat) (h : 0 < x) : 0 < x := by",
  "  exact h",
  "",
  "theorem bar : True := trivial",
  "",
].join("\n");
const FOO_DOC = "/-- For [a natural number](hyp:x) with [x above zero](hyp:h), [x is above zero](goal). -/\n";
const BAR_DOC = "/-- [Truth holds](goal). -/\n";
const documented = (src: string) => src.replace("theorem foo", `${FOO_DOC}theorem foo`).replace("theorem bar", `${BAR_DOC}theorem bar`);

/** A paper index over the file as it is now: each theorem starts at its docstring when it has one. */
function fakeIndex(src: string) {
  const lines = src.split("\n");
  const entries: object[] = [];
  lines.forEach((l, i) => {
    const m = /^theorem (\w+)/.exec(l);
    if (!m) return;
    let start = i;
    let doc: string | null = null;
    if (i > 0 && lines[i - 1]!.endsWith("-/")) {
      start = i - 1;
      while (start > 0 && !lines[start]!.includes("/--")) start -= 1;
      doc = lines.slice(start, i).join("\n").replace(/^\s*\/--/, "").replace(/-\/\s*$/, "");
    }
    let end = i;
    while (end + 1 < lines.length && lines[end + 1]!.trim() !== "") end += 1;
    entries.push({ name: `Papers.T.${m[1]}`, file: FILE, line: start + 1, kind: "theorem", doc, source: lines.slice(start, end + 1).join("\n") });
  });
  return { entries };
}

let root: string;
let lakeCalls: string[];
let breaks: (src: string) => boolean;

beforeEach(async () => {
  root = await mkdtemp(path.join(tmpdir(), "pf-docgate-"));
  await mkdir(path.join(root, "Papers/T"), { recursive: true });
  await writeFile(path.join(root, FILE), ORIGINAL);
  const prompt = promptPath(root, "stage5_docstrings.txt");
  await mkdir(path.dirname(prompt), { recursive: true });
  await writeFile(prompt, "Document {{decl_list}} under {{package_root}}.\n");
  lakeCalls = [];
  breaks = () => false;
});
afterEach(async () => rm(root, { recursive: true, force: true }));

const runLake: LakeRun = async (args) => {
  lakeCalls.push(args[0]!);
  const src = await readFile(path.join(root, FILE), "utf8");
  if (args[0] === "build" && breaks(src)) {
    return { stdout: `${FILE}:2:3: error: unexpected token '/--'`, stderr: "build failed", exitCode: 1, killedDueToInactivity: false };
  }
  if (args[0] === "exe") await writeFile(args[args.indexOf("--out") + 1]!, JSON.stringify(fakeIndex(src)));
  return { stdout: "", stderr: "", exitCode: 0, killedDueToInactivity: false };
};

function target(edits: ((src: string) => string)[]): DocstringTarget & { calls: () => number } {
  let n = 0;
  return {
    ctx: { repoRoot: root, qid: "t" } as unknown as PipelineContext,
    deps: {} as StageDeps,
    modules: ["Papers.T.A"],
    prefix: "Papers.T",
    outDir: path.join(root, "out"),
    label: "F5",
    builtModules: ["Papers.T.A"],
    runLake,
    dispatch: async () => {
      const edit = edits[Math.min(n, edits.length - 1)]!;
      n += 1;
      const abs = path.join(root, FILE);
      await writeFile(abs, edit(await readFile(abs, "utf8")));
      return { stdout: "", stderr: "" };
    },
    calls: () => n,
  };
}

describe("documentModules: text-checked passes, one confirming build", () => {
  it("a docstring-only pass needs no build until the one that confirms it", async () => {
    const t = target([documented]);
    const out = await documentModules(t);
    expect(out.block).toBeNull();
    expect(lakeCalls).toEqual(["exe"]); // the index only: the tree was already built
    expect(out.confirm).toBeDefined();
    expect(await out.confirm!()).toBeNull();
    expect(lakeCalls).toEqual(["exe", "build", "exe"]);
    expect(await readFile(path.join(root, FILE), "utf8")).toBe(documented(ORIGINAL));
    // recorded clean: the next entry skips the gate
    lakeCalls = [];
    expect(await documentModules(target([documented]))).toEqual({ block: null });
    expect(lakeCalls).toEqual([]);
  });

  it("an edit that changes code is undone and its declarations go to the next pass", async () => {
    const t = target([(s) => documented(s).replace("exact h", "exact h.le"), documented]);
    const out = await documentModules(t);
    expect(t.calls()).toBe(2);
    expect(out.block).toBeNull();
    expect(await readFile(path.join(root, FILE), "utf8")).toBe(documented(ORIGINAL));
    expect(existsSync(path.join(root, "out/docstring_rejected/pass1", FILE))).toBe(true);
    expect(await out.confirm!()).toBeNull();
  });

  it("a code change on both passes leaves the file as it was and halts with the declarations", async () => {
    const out = await documentModules(target([(s) => documented(s).replace("trivial", "True.intro")]));
    expect(out.block).toMatch(/docstring coverage: 2 declaration\(s\) still undocumented/);
    expect(await readFile(path.join(root, FILE), "utf8")).toBe(ORIGINAL);
    expect(lakeCalls).toEqual(["exe"]);
  });

  it("a docstring outside the declarations' slots is undone like a code change, with no build", async () => {
    const t = target([(s) => documented(s).replace("  exact h", "  /-- inside -/\n  exact h"), documented]);
    const out = await documentModules(t);
    expect(t.calls()).toBe(2);
    expect(lakeCalls).toEqual(["exe"]);
    expect(out.block).toBeNull();
    expect(await readFile(path.join(root, FILE), "utf8")).toBe(documented(ORIGINAL));
    expect(existsSync(path.join(root, "out/docstring_rejected/pass1", FILE))).toBe(true);
  });

  it("pass 2 is told each declaration's line in the file as pass 1 left it", async () => {
    const prompts: string[] = [];
    const t = target([(s) => s.replace("theorem foo", `${FOO_DOC}theorem foo`), documented]);
    const inner = t.dispatch!;
    t.dispatch = async (args) => { prompts.push(args.prompt); return inner(args); };
    const out = await documentModules(t);
    expect(out.block).toBeNull();
    expect(prompts[0]).toContain("L4 theorem Papers.T.bar");
    expect(prompts[1]).toContain("L5 theorem Papers.T.bar");
    expect(prompts[1]).not.toContain("Papers.T.foo");
  });

  it("a pass that throws leaves none of its edits", async () => {
    const t = target([documented]);
    const inner = t.dispatch!;
    t.dispatch = async (args) => { await inner(args); throw new Error("worker exploded"); };
    await expect(documentModules(t)).rejects.toThrow("worker exploded");
    expect(await readFile(path.join(root, FILE), "utf8")).toBe(ORIGINAL);
  });

  it("a statement the confirming build reports changed restores the files", async () => {
    const t = target([documented]);
    t.statements = { before: async () => null, after: async () => ({ changed: "Papers.T.foo (Papers/T/A.lean) states something else" }) };
    const out = await documentModules(t);
    const block = await out.confirm!();
    expect(block).toMatch(/docstring pass changed what a declaration states; its edits were restored byte-for-byte/);
    expect(block).toContain("Papers.T.foo");
    expect(await readFile(path.join(root, FILE), "utf8")).toBe(ORIGINAL);
    expect(existsSync(path.join(root, "out/docstring_clean.json"))).toBe(false);
  });

  it("statements that cannot be checked after the build halt and keep the edits", async () => {
    const t = target([documented]);
    t.statements = { before: async () => null, after: async () => ({ unavailable: "the scan failed" }) };
    const out = await documentModules(t);
    expect(await out.confirm!()).toMatch(/docstring pass could not be validated — the scan failed \(the edits are kept\)/);
    expect(await readFile(path.join(root, FILE), "utf8")).toBe(documented(ORIGINAL));
    expect(existsSync(path.join(root, "out/docstring_clean.json"))).toBe(false);
  });

  it("statements that cannot be checked before the pass: no pass runs, nothing is edited", async () => {
    const t = target([documented]);
    t.statements = { before: async () => "the scan failed", after: async () => null };
    const out = await documentModules(t);
    expect(out.block).toMatch(/docstring pass not started — the scan failed; nothing was edited/);
    expect(t.calls()).toBe(0);
    expect(await readFile(path.join(root, FILE), "utf8")).toBe(ORIGINAL);
  });

  it("an inline docstring before a declaration is accepted", async () => {
    const out = await documentModules(target([(s) => s.replace("theorem bar", `${BAR_DOC.trimEnd()} theorem bar`).replace("theorem foo", `${FOO_DOC}theorem foo`)]));
    expect(out.block).toBeNull();
    expect(out.confirm).toBeDefined();
  });

  it("an extraction error in the confirmation is a block, not a throw, and keeps the edits", async () => {
    const t = target([documented]);
    let exe = 0;
    t.runLake = async (args) => {
      if (args[0] === "exe" && ++exe === 2) {
        await writeFile(args[args.indexOf("--out") + 1]!, "{}");
        return { stdout: "", stderr: "", exitCode: 0, killedDueToInactivity: false };
      }
      return runLake(args);
    };
    const out = await documentModules(t);
    expect(await out.confirm!()).toMatch(/docstring coverage could not be computed/);
    expect(await readFile(path.join(root, FILE), "utf8")).toBe(documented(ORIGINAL));
  });

  it("the confirming build failing restores the files as the last green build had them", async () => {
    breaks = (s) => s.includes("Truth");
    const out = await documentModules(target([documented]));
    expect(out.block).toBeNull();
    const block = await out.confirm!();
    expect(block).toMatch(/docstring pass broke the build/);
    expect(await readFile(path.join(root, FILE), "utf8")).toBe(ORIGINAL);
    expect(existsSync(path.join(root, "out/docstring_clean.json"))).toBe(false);
  });

  it("a confirming build stopped at its time limit keeps the edits and says so", async () => {
    const t = target([documented]);
    t.runLake = async (args) => {
      if (args[0] === "build") return { stdout: "", stderr: "", exitCode: null, killedDueToInactivity: false, killedDueToTotalTimeout: true };
      return runLake(args);
    };
    const out = await documentModules(t);
    const block = await out.confirm!();
    expect(block).toMatch(/could not be validated — lake did not finish \(the edits are kept\)/);
    expect(block).toContain("[f5-time-limit]");
    expect(await readFile(path.join(root, FILE), "utf8")).toBe(documented(ORIGINAL));
  });
});
