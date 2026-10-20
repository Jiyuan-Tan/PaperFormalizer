import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { createEmptyGraph } from "../../src/graph/store.js";
import { addNode } from "../../src/graph/mutate.js";
import { extractFromLean } from "../../src/graph/extractor.js";
import { mintAnnotatedNodes, mintHiddenDefNodes } from "../../src/graph/hidden.js";
import { statementHash } from "../../src/graph/hash.js";

let dir: string;
beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "hidden-")); });
afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

// t1's CONCLUSION names `rateBound` (an ℝ-valued build-inline quantity with no
// node/annotation) — surfaced by findHiddenStatementDefs (a direct-hypothesis def
// would instead be excluded as already covered by the H.1 matrix).
const HIDDEN_LEAN = `
def rateBound : ℝ := 1

-- @node: t1
theorem t1_thm : rateBound = 1 := by sorry
`;

describe("mintHiddenDefNodes", () => {
  it("mints an auto definition node for a build-inline def reached from a statement, idempotently", async () => {
    await writeFile(path.join(dir, "T1.lean"), HIDDEN_LEAN, "utf8");
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "m", tex_anchor: "" });
    ({ graph: g } = await extractFromLean(g, dir));
    g = await mintHiddenDefNodes(g, dir);
    const aux = g.nodes.find((n) => n.lean.decl_name === "rateBound");
    expect(aux?.kind).toBe("definition");
    expect(aux?.provenance).toBe("agent-introduced");
    expect(aux?.id).toBe("aux_rateBound");
    // idempotent
    const n1 = g.nodes.length;
    g = await mintHiddenDefNodes(g, dir);
    expect(g.nodes.length).toBe(n1);
  });
});

// A from-note theorem t1 (already a node) whose proof introduced two tagged helpers
// (a lemma + a build-inline def) that are NOT yet graph nodes.
const ANNOTATED_LEAN = `import Mathlib

-- @node: t1
theorem t1_thm : True := by trivial

-- @node: smoothedInverseWeightLaw_klDiv_le
private lemma smoothedInverseWeightLaw_klDiv_le : True := by trivial

-- @node: smoothInverseWeightProfile
noncomputable def smoothInverseWeightProfile : Nat := 0
`;

describe("mintAnnotatedNodes", () => {
  it("mints agent-introduced nodes for tagged helpers absent from the graph, leaves from-note nodes untouched, idempotently", async () => {
    await writeFile(path.join(dir, "T2.lean"), ANNOTATED_LEAN, "utf8");
    let g = createEmptyGraph("q");
    g = addNode(g, { id: "t1", kind: "theorem", provenance: "from-note", nl_statement: "main", tex_anchor: "" });

    g = await mintAnnotatedNodes(g, dir);

    const lemma = g.nodes.find((n) => n.id === "smoothedInverseWeightLaw_klDiv_le");
    const def = g.nodes.find((n) => n.id === "smoothInverseWeightProfile");
    expect(lemma).toBeDefined();
    expect(lemma!.kind).toBe("lemma");
    expect(lemma!.provenance).toBe("agent-introduced");
    expect(lemma!.nl.frozen).toBe(false); // never relabelled from-note
    expect(lemma!.lean.decl_name).toBe("smoothedInverseWeightLaw_klDiv_le");
    expect(lemma!.proof.state).toBe("complete");
    expect(lemma!.review).toEqual({
      status: "unreviewed",
      passed_hash: statementHash("private lemma smoothedInverseWeightLaw_klDiv_le : True"),
    });
    expect(def!.kind).toBe("definition");
    expect(def!.provenance).toBe("agent-introduced");
    const t1 = g.nodes.find((n) => n.id === "t1")!;
    expect(t1.provenance).toBe("from-note");
    expect(t1.kind).toBe("theorem");

    const after1 = g.nodes.length;
    g = await mintAnnotatedNodes(g, dir);
    expect(g.nodes.length).toBe(after1);
  });
});
