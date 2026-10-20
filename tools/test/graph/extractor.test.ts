import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode, addEdge } from "../../src/graph/mutate.js";
import { extractFromLean } from "../../src/graph/extractor.js";

let dir: string;
beforeEach(async () => {
  dir = await mkdtemp(path.join(tmpdir(), "graph-ex-"));
});
afterEach(async () => {
  await rm(dir, { recursive: true, force: true });
});

const LEAN = `
-- @node: p1
def overlapBound (x : ℝ) : Prop := 0 < x

-- @node: t1
theorem t1_main (h : overlapBound 1) : True := by
  sorry
`;

describe("extractFromLean", () => {
  it("links annotated decls, refreshes proof state, and reports decls with no graph node as unlinked", async () => {
    await writeFile(path.join(dir, "T1.lean"), LEAN, "utf8");
    await writeFile(path.join(dir, "T2.lean"), "-- @node: ghost\ntheorem ghost_thm : True := trivial\n", "utf8");
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "p1", kind: "definition", provenance: "from-note", nl_statement: "overlap bound", tex_anchor: "" });
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });

    const { graph, hashes, unlinked } = await extractFromLean(g, dir);

    const t1 = graph.nodes.find((n) => n.id === "t1")!;
    expect(t1.lean).toEqual({ decl_name: "t1_main", file: "T1.lean" });
    expect(t1.proof).toEqual({ state: "sorry", sorry_count: 1 });
    expect(hashes["t1"]).toMatch(/^[0-9a-f]{40}$/);
    expect(graph.edges).toContainEqual({ kind: "statement-uses", from: "t1", to: "p1", source: "extracted" });
    expect(unlinked).toEqual([{ id: "ghost", decl_name: "ghost_thm", file: "T2.lean" }]);
  });

  // A scratch COPY of a real file under the paper tmp/ workspace (agents are told to put
  // Lean probes there) duplicates its `-- @node:` tags; extraction must ignore tmp/ or the
  // duplicate makes every graph refresh fail the node as unlinked.
  it("ignores the paper tmp/ workspace (a scratch copy must not duplicate @node tags)", async () => {
    await writeFile(path.join(dir, "T1.lean"), LEAN, "utf8");
    const scratch = path.join(dir, "tmp");
    await (await import("node:fs/promises")).mkdir(scratch, { recursive: true });
    await writeFile(path.join(scratch, "T1.lean"), LEAN, "utf8");
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "p1", kind: "definition", provenance: "from-note", nl_statement: "overlap bound", tex_anchor: "" });
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });

    const { graph, unlinked } = await extractFromLean(g, dir);
    expect(unlinked).toEqual([]);
    expect(graph.nodes.find((n) => n.id === "t1")!.lean).toEqual({ decl_name: "t1_main", file: "T1.lean" });
  });

  it("rejects duplicate annotations for one graph node instead of linking first-wins", async () => {
    await writeFile(
      path.join(dir, "T1.lean"),
      [
        "-- @node: t1",
        "def t1Primary : Prop := True",
        "",
        "-- @node: t1",
        "def t1Companion : Prop := True",
      ].join("\n"),
      "utf8",
    );
    let g = createEmptyGraph("q");
    g = addNode(g, {
      id: "t1",
      kind: "definition",
      provenance: "from-note",
      nl_statement: "one canonical declaration",
      tex_anchor: "",
    });

    const { graph, hashes, unlinked } = await extractFromLean(g, dir);

    expect(graph).toEqual(g);
    expect(hashes).toEqual({});
    expect(unlinked).toEqual([
      { id: "t1", decl_name: "t1Primary", file: "T1.lean" },
      { id: "t1", decl_name: "t1Companion", file: "T1.lean" },
    ]);
  });

  it("overwrites prior extracted edges but preserves declared edges", async () => {
    await writeFile(path.join(dir, "T1.lean"), LEAN, "utf8");
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "p1", kind: "definition", provenance: "from-note", nl_statement: "ob", tex_anchor: "" });
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
    g = addEdge(g, { kind: "proof-uses", from: "t1", to: "p1", source: "declared" });
    g = addEdge(g, { kind: "statement-uses", from: "t1", to: "p1", source: "extracted" }); // stale, rebuilt
    const { graph } = await extractFromLean(g, dir);
    expect(graph.edges.filter((e) => e.source === "declared")).toHaveLength(1);
    expect(graph.edges.filter((e) => e.kind === "statement-uses")).toHaveLength(1);
  });

  it("draws a statement-uses edge to a library-backed node (preset decl_name, no annotation)", async () => {
    await writeFile(path.join(dir, "T1.lean"), "-- @node: t1\ntheorem t1_main (h : HolderWith 1 2 f) : True := by sorry\n", "utf8");
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });
    g = addNode(g, { id: "hclass", kind: "definition", provenance: "library", nl_statement: "Hölder class", tex_anchor: "" });
    g = { ...g, nodes: g.nodes.map((n) => (n.id === "hclass" ? { ...n, lean: { decl_name: "HolderWith", file: null } } : n)) };

    const { graph } = await extractFromLean(g, dir);
    expect(graph.edges).toContainEqual({ kind: "statement-uses", from: "t1", to: "hclass", source: "extracted" });
  });
});
