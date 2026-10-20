import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile, mkdir } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { refreshGraphForGate, applyVerdictsToGraph } from "../../src/graph/refresh.js";
import { createEmptyGraph, saveGraph, graphPath } from "../../src/graph/store.js";
import { buildGraphFromMd } from "../../src/graph/from_note.js";
import { addNode } from "../../src/graph/mutate.js";

let dir: string;
beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "refresh-")); });
afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

const MD = `### T-block: t1 — Rate theorem
**Statement.** the rate bound holds.
`;
const LEAN = `
def rateBound : ℝ := 1

-- @node: t1
theorem t1_thm : rateBound = 1 := by sorry
`;

async function scaffold() {
  await writeFile(path.join(dir, "q_v1.md"), MD, "utf8");
  await saveGraph(graphPath(dir), await buildGraphFromMd("q", path.join(dir, "q_v1.md")));
  const leanDir = path.join(dir, "lean");
  await mkdir(leanDir, { recursive: true });
  await writeFile(path.join(leanDir, "T1.lean"), LEAN, "utf8");
  return leanDir;
}

describe("refreshGraphForGate", () => {
  it("returns no graph when only a legacy Markdown note exists", async () => {
    await writeFile(path.join(dir, "q_v1.md"), MD);
    const r = await refreshGraphForGate({ formalizationDir: dir, qid: "q", leanDir: path.join(dir, "lean") });
    expect(r).toEqual({ graph: null, skeleton: [], dirty: [], hashes: {}, coverage: null });
  });

  it("loads the persisted graph, extracts, mints hidden defs, returns skeleton+dirty+coverage", async () => {
    const leanDir = await scaffold();
    const r = await refreshGraphForGate({ formalizationDir: dir, qid: "q", leanDir });
    expect(r.graph).not.toBeNull();
    const t1 = r.graph!.nodes.find((n) => n.id === "t1")!;
    expect(t1.lean.decl_name).toBe("t1_thm");
    expect(r.graph!.nodes.some((n) => n.id === "aux_rateBound")).toBe(true);
    expect(r.skeleton.some((row) => row.obj_id === "T-1")).toBe(true);
    expect(r.dirty).toContain("t1");
    expect(r.coverage).not.toBeNull();
  });

  it("hard-fails refresh when two declarations reuse one @node id", async () => {
    const leanDir = await scaffold();
    await writeFile(
      path.join(leanDir, "T1.lean"),
      [
        "-- @node: t1",
        "theorem t1_thm : True := by trivial",
        "",
        "-- @node: t1",
        "theorem t1_companion : True := by trivial",
      ].join("\n"),
      "utf8",
    );

    const r = await refreshGraphForGate({
      formalizationDir: dir,
      qid: "q",
      leanDir,
    });

    expect(r.graph).toBeNull();
    expect(r.error).toMatch(/unlinked Lean @node annotations/);
    expect(r.error).toContain("t1->t1_thm@T1.lean");
    expect(r.error).toContain("t1->t1_companion@T1.lean");
  });

});

const cw = (obj_id: string, verdict: string) =>
  ({ obj_id, kind: "theorem", title: "", tex: { label: "", line_range: "" }, lean: null, verdict }) as any;

describe("applyVerdictsToGraph", () => {
  it("maps verdicts → node status (exact/equivalent→matched, drift family→drift, unmatched→skip)", () => {
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
    g = addNode(g, { id: "p2", kind: "definition", provenance: "from-note", nl_statement: "d", tex_anchor: "" });
    g = addNode(g, { id: "l3", kind: "lemma", provenance: "from-note", nl_statement: "h", tex_anchor: "" });
    g = applyVerdictsToGraph(g, [cw("T-1", "equivalent"), cw("P-2", "weaker-in-Lean"), cw("L-3", "unmatched")], { t1: "h1" });
    expect(g.nodes.find((n) => n.id === "t1")!.review).toEqual({ status: "matched", passed_hash: "h1" });
    expect(g.nodes.find((n) => n.id === "p2")!.review.status).toBe("drift");
    expect(g.nodes.find((n) => n.id === "l3")!.review.status).toBe("unreviewed"); // unmatched → skipped
  });

  it("fails closed on an ambiguous, missing or unbound target, validating the whole batch before applying any row", () => {
    let ambiguous = createEmptyGraph("q");
    ambiguous = addNode(ambiguous, { id: "a1", kind: "assumption", provenance: "from-note", nl_statement: "legacy", tex_anchor: "" });
    ambiguous = addNode(ambiguous, { id: "ass:other", kind: "assumption", provenance: "from-note", nl_statement: "core", tex_anchor: "" });
    ambiguous = {
      ...ambiguous,
      nodes: ambiguous.nodes.map((n) => n.id === "ass:other" ? { ...n, obj_id: "A-1" } : n),
    };
    expect(() => applyVerdictsToGraph(ambiguous, [cw("A-1", "equivalent")], {}))
      .toThrow('review verdict target resolution failed for "A-1": ambiguous aliases: a1, ass:other');
    expect(() => applyVerdictsToGraph(createEmptyGraph("q"), [cw("missing_Target", "equivalent")], {}))
      .toThrow('review verdict target resolution failed for "missing_Target": no graph node or unambiguous legacy/from-note alias');

    let g = createEmptyGraph("q");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "theorem", tex_anchor: "" });
    const owners = new Map<string, string | null>([
      ["T-1", "t1"],
      ["missing", "does-not-exist"],
    ]);

    expect(() => applyVerdictsToGraph(
      g,
      [cw("T-1", "equivalent"), cw("missing", "equivalent")],
      { t1: "h1" },
      owners,
    )).toThrow('review verdict target resolution failed for "missing": bound graph node "does-not-exist" is missing');
    expect(g.nodes[0].review.status).toBe("unreviewed");
  });
});
