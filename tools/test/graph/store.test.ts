import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, readFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { createEmptyGraph, graphPath, loadGraph, saveGraph } from "../../src/graph/store.js";
import { statementHash } from "../../src/graph/hash.js";

let dir: string;
beforeEach(async () => {
  dir = await mkdtemp(path.join(tmpdir(), "graph-store-"));
});
afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

describe("store", () => {
  it("save then load round-trips", async () => {
    const g = createEmptyGraph("stat_demo");
    expect(g).toMatchObject({ qid: "stat_demo", nodes: [], edges: [] });
    g.nodes.push({
      id: "t1",
      kind: "theorem",
      provenance: "from-note",
      nl: { statement: "x", tex_anchor: "tex:L1", frozen: true },
      lean: { decl_name: null, file: null },
      review: { status: "unreviewed", passed_hash: null },
      proof: { state: "sorry", sorry_count: 1 },
    });
    const p = graphPath(dir);
    await saveGraph(p, g);
    const back = await loadGraph(p);
    expect(back).toEqual(g);
  });

  it("loadGraph throws on a schema-invalid file", async () => {
    const p = graphPath(dir);
    await saveGraph(p, createEmptyGraph("stat_demo"));
    await readFile(p, "utf8"); // file exists
    await rm(p);
    const { writeFile } = await import("node:fs/promises");
    await writeFile(p, JSON.stringify({ qid: "x" }), "utf8");
    await expect(loadGraph(p)).rejects.toThrow();
  });
});

describe("statementHash", () => {
  it("is a hex digest that ignores whitespace but not content", () => {
    expect(statementHash("theorem  t1 :\n  A → B")).toBe(statementHash("theorem t1 : A → B"));
    expect(statementHash("A → B")).not.toBe(statementHash("A → C"));
    expect(statementHash("A → B")).toMatch(/^[0-9a-f]{40}$/);
  });
});
