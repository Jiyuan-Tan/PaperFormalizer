import { describe, expect, it } from "vitest";
import { readFileSync } from "node:fs";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { nodeConvergenceEvidence, REVIEW_STANDARD } from "../../src/formalization/convergence_evidence.js";
import { parseStatementFingerprints } from "../../src/formalization/statement_fingerprints.js";
import { addNode, setLean, setNodeReview } from "../../src/graph/mutate.js";
import { createEmptyGraph, graphPath, loadGraph, saveGraph } from "../../src/graph/store.js";
import { carryReceipts, fingerprintScanCmd, nameAfterMove, parseFingerprints, receiptsBefore, statementInvarianceFailure } from "../../src/proposals/invariance.js";
import { tk } from "../toolkit/helpers.js";

const scan = (decls: Array<[string, string]>) => JSON.stringify({ declarations: decls.map(([name, stmt_hash]) => ({ name, stmt_hash })) });

describe("statement invariance of a promotion", () => {
  const moved = [{ from: "Papers.Foo.bound_le", to: "Toolkit.Foundations.Analysis.Bounds.sum_le" }];
  const before = new Map([["Papers.Foo.bound_le", "11"], ["Papers.Foo.main", "22"], ["Papers.Foo.Class", "33"], ["Toolkit.Foundations.X.old", "44"]]);

  it("passes when every declaration states what it stated, the moved one under its new name", () => {
    const after = new Map([["Toolkit.Foundations.Analysis.Bounds.sum_le", "11"], ["Papers.Foo.main", "22"], ["Papers.Foo.Class", "33"], ["Toolkit.Foundations.X.old", "44"], ["Papers.Foo.new_helper", "99"]]);
    expect(statementInvarianceFailure(before, after, moved)).toBeNull();
    expect(nameAfterMove("Papers.Foo.bound_le.aux", moved)).toBe("Toolkit.Foundations.Analysis.Bounds.sum_le.aux");
  });

  it("names a statement that changed and one that disappeared", () => {
    const after = new Map([["Toolkit.Foundations.Analysis.Bounds.sum_le", "12"], ["Papers.Foo.main", "22"], ["Toolkit.Foundations.X.old", "44"]]);
    const why = statementInvarianceFailure(before, after, moved)!;
    expect(why).toContain("no longer states what it stated before: Toolkit.Foundations.Analysis.Bounds.sum_le (was Papers.Foo.bound_le)");
    expect(why).toContain("no longer declared: Papers.Foo.Class");
  });

  it("reads the hashes of a scan, and none from a scan made by an older scan program", () => {
    expect(parseFingerprints(scan([["A.b", "7"]]))).toEqual(new Map([["A.b", "7"]]));
    expect(parseFingerprints(JSON.stringify({ declarations: [{ name: "A.b", type: "True" }] }))).toBeNull();
    expect(parseFingerprints("not json")).toBeNull();
  });

  it("scans the toolkit and the one paper, under the move's names", () => {
    const cmd = fingerprintScanCmd({ lib: "Toolkit", papersLib: "Papers" }, "Papers.Foo", "/run/out.json", moved);
    expect(cmd).toBe("lake exe candidate_scan -- --graph --fingerprints --toolkit-prefix Toolkit --papers-prefix Papers --modules 'Toolkit,Papers.Foo' --rename Papers.Foo.bound_le=Toolkit.Foundations.Analysis.Bounds.sum_le --out /run/out.json");
    expect(fingerprintScanCmd({ lib: "Toolkit", papersLib: "Papers" }, "Papers.Foo", "/run/out.json")).not.toContain("--rename");
  });
});

describe("the run's F4 receipts across a promotion step", () => {
  it("are read off the gate's two scans: current before the step, restamped on the closure hashes after it", async () => {
    const root = await mkdtemp(join(tmpdir(), "invariance-carry-"));
    try {
      const cfg = tk(root);
      const leanDir = join(root, "Papers", "Toy");
      await mkdir(leanDir, { recursive: true });
      await writeFile(join(leanDir, "Main.lean"), "def helper : Nat := 1\n-- @node: thm:a\ntheorem a : helper = 1 := rfl\n-- @node: thm:b\ntheorem b : True := trivial\n");
      let g = createEmptyGraph("q");
      for (const id of ["thm:a", "thm:b"]) {
        g = addNode(g, { id, kind: "theorem", provenance: "from-note", nl_statement: id, tex_anchor: "" });
        g = setLean(g, id, id.slice(4), "Main.lean");
        g = setNodeReview(g, id, "matched", "h");
      }
      const scanText = (hashes: Record<string, string>) => JSON.stringify({ declarations: Object.entries(hashes).map(([name, closure_hash]) => ({ name, file: "Papers/Toy/Main.lean", stmt_hash: "s", closure_hash })) });
      const before = join(root, "before.json");
      const after = join(root, "after.json");
      await writeFile(before, scanText({ helper: "h0", a: "a0", b: "b0" }));
      // the step moved `helper` under a new name: `a`, which states it, has another closure
      await writeFile(after, scanText({ a: "a1", b: "b0" }));
      const evidence = (file: string, id: string) => nodeConvergenceEvidence({ graph: g, fingerprints: parseStatementFingerprints(readFileSync(file, "utf8"), "Papers/Toy"), core: null, rubricHash: REVIEW_STANDARD, nodeId: id })!;
      const receipt = (h: string) => ({ codex: { verdict: "matched" as const, evidence_hash: h }, claude: { verdict: "matched" as const, evidence_hash: h } });
      const gp = graphPath(join(cfg.runsDir, "q"));
      await mkdir(join(cfg.runsDir, "q"), { recursive: true });
      await saveGraph(gp, { ...g, convergenceReview: { "thm:a": receipt(evidence(before, "thm:a")), "thm:b": receipt("an-older-statement") } });
      const cleared = await receiptsBefore(cfg, "q", leanDir, before);
      expect(cleared).toEqual(["thm:a"]);
      expect(await receiptsBefore(cfg, "q", leanDir, join(root, "missing.json"))).toEqual([]);
      expect(await carryReceipts(cfg, "q", leanDir, cleared, after)).toBe(1);
      const ledger = (await loadGraph(gp)).convergenceReview!;
      expect(ledger["thm:a"]).toEqual(receipt(evidence(after, "thm:a")));
      expect(ledger["thm:b"]).toEqual(receipt("an-older-statement"));
      // a scan with no closure hashes carries nothing
      await writeFile(after, JSON.stringify({ declarations: [{ name: "a", file: "Papers/Toy/Main.lean", stmt_hash: "s" }] }));
      expect(await carryReceipts(cfg, "q", leanDir, ["thm:b"], after)).toBe(0);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });
});
