import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import {
  loadToolkitConfig, resolveToolkitRoot, toolkitConfigFromJson, TOOLKIT_ENV_VAR,
} from "../../src/toolkit/config.js";
import { TOOLKIT_JSON } from "./helpers.js";

let tmp: string;
beforeEach(async () => { tmp = await mkdtemp(path.join(os.tmpdir(), "tkcfg-")); });
afterEach(async () => { await rm(tmp, { recursive: true, force: true }); });

async function makeToolkit(name: string, json: unknown = TOOLKIT_JSON): Promise<string> {
  const root = path.join(tmp, name);
  await mkdir(root, { recursive: true });
  await writeFile(path.join(root, "theoremchecker.json"), JSON.stringify(json), "utf8");
  return root;
}

describe("toolkit root resolution", () => {
  it.each(["arg", "env", "cwd"] as const)("resolves the toolkit by precedence: %s", async (source) => {
    const a = await makeToolkit("a");
    const b = await makeToolkit("b");
    const deep = path.join(a, "runs", "study_x", "agent_io");
    await mkdir(deep, { recursive: true });
    const opts =
      source === "arg" ? { explicit: a, env: { [TOOLKIT_ENV_VAR]: b }, cwd: b }
      : source === "env" ? { env: { [TOOLKIT_ENV_VAR]: a }, cwd: b }
      : { env: {}, cwd: deep };
    expect(resolveToolkitRoot(opts)).toEqual({ root: a, source });
  });

  it("fails closed, naming all three ways, when nothing resolves; a named path without config never falls back", async () => {
    expect(() => resolveToolkitRoot({ env: {}, cwd: tmp })).toThrow(
      /--toolkit <path>.*THEOREMCHECKER_TOOLKIT=<path>.*theoremchecker\.json/,
    );
    const a = await makeToolkit("a");
    expect(() => resolveToolkitRoot({ explicit: tmp, cwd: a })).toThrow(/--toolkit .*no theoremchecker\.json/);
    expect(() => resolveToolkitRoot({ env: { [TOOLKIT_ENV_VAR]: tmp }, cwd: a })).toThrow(/THEOREMCHECKER_TOOLKIT=.*no theoremchecker\.json/);
  });
});

describe("toolkit config parsing", () => {
  it("rejects malformed configs", () => {
    const bad = (patch: (j: any) => void) => {
      const j = structuredClone(TOOLKIT_JSON) as any;
      patch(j);
      return () => toolkitConfigFromJson(tmp, j);
    };
    expect(bad((j) => { delete j.base[1].path; })).toThrow(/kind "path" but no path/);
    expect(bad((j) => { j.toolkit.divisions = ["Foundations", "Foundations"]; })).toThrow(/duplicate division/);
    expect(bad((j) => { j.toolkit.divisions = ["Staging"]; })).toThrow(/reserved/);
    expect(bad((j) => { j.toolkit.papers_lib = "Toolkit"; })).toThrow(/must differ/);
    expect(bad((j) => { j.version = 2; })).toThrow(/version/);
    expect(bad((j) => { j.toolkit.lib = "Tool.kit"; })).toThrow(/Lean identifier/);
  });
});

describe("toolkit config: configured base-library files are validated at load", () => {
  const withBase = (extra: Record<string, unknown>) => ({
    ...TOOLKIT_JSON,
    base: TOOLKIT_JSON.base.map((b) => (b.name === "Base" ? { ...b, ...extra } : b)),
  });

  it("fails closed on a missing or malformed alias file and an unreadable notes file", async () => {
    const missing = await makeToolkit("missing", withBase({ alias_file: "nope.json" }));
    expect(() => loadToolkitConfig({ explicit: missing }))
      .toThrow(/base library Base: alias_file: cannot read alias file .*nope\.json.*fix or remove it in .*theoremchecker\.json/);
    const bad = await makeToolkit("bad", withBase({ alias_file: "bad.json" }));
    await writeFile(path.join(bad, "bad.json"), "{ not json", "utf8");
    expect(() => loadToolkitConfig({ explicit: bad })).toThrow(/alias_file: alias file .*bad\.json is not JSON/);
    const shape = await makeToolkit("shape", withBase({ alias_file: "shape.json" }));
    await writeFile(path.join(shape, "shape.json"), JSON.stringify({ version: 2, entries: [] }), "utf8");
    expect(() => loadToolkitConfig({ explicit: shape })).toThrow(/invalid alias file .*shape\.json/);
    const notes = await makeToolkit("notes", withBase({ prompt_notes: "gone.md" }));
    expect(() => loadToolkitConfig({ explicit: notes })).toThrow(/base library Base: prompt_notes .*gone\.md is unreadable/);
  });
});

describe("referee options", () => {
  it("the concurrency cap and shard limits default; each is read when set", () => {
    const json = { version: 1, owner: { name: "o" }, toolkit: { lib: "Toolkit", papers_lib: "Papers", divisions: ["Foundations"] }, lean: { toolchain: "t" } };
    const d = { max_concurrent: 6, shard_bytes: 70_000, shard_max_hypotheses: 10, shard_max_lemmas: 6, shard_max_theorems: 3, symbol_effort: "medium" };
    expect(toolkitConfigFromJson("/tk", json).referee).toEqual(d);
    expect(toolkitConfigFromJson("/tk", { ...json, referee: { max_concurrent: 2, shard_bytes: 5000, shard_max_theorems: 1 } }).referee).toEqual({ ...d, max_concurrent: 2, shard_bytes: 5000, shard_max_theorems: 1 });
    expect(() => toolkitConfigFromJson("/tk", { ...json, referee: { max_concurrent: 0 } })).toThrow(/referee/);
  });
});
