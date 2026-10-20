// The toolkit graph on a tiny fixture: a scan of a toy toolkit (`double`, `double_eq`, `lonely`) and
// a toy paper whose main result uses its helper and two toolkit declarations
// (`fixtures/toolkit_graph/graph_scan.json`, written by `candidate_scan --graph`).
import { readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { candidateScanSchema } from "../../src/proposals/candidate_scan.js";
import { attachNote, buildToolkitGraph, healthRegressions, healthSummary, mainView, toolkitHealth } from "../../src/proposals/toolkit_graph.js";

const scan = candidateScanSchema.parse(JSON.parse(readFileSync(path.join(__dirname, "../fixtures/toolkit_graph/graph_scan.json"), "utf8")));
const graph = buildToolkitGraph({ scan, paperMain: new Set(["Papers.Toy.main_result"]), now: () => new Date("2026-10-01") });
const node = (id: string) => graph.nodes.find((n) => n.id === id)!;

describe("toolkit graph", () => {
  it("is derived from the scan: uses-edges, base leaves only under toolkit declarations, tiers with owners", () => {
    expect(graph.edges).toContainEqual(["Papers.Toy.main_result", "Papers.Toy.helper"]);
    expect(graph.edges).toContainEqual(["Papers.Toy.main_result", "Toolkit.double_eq"]);
    expect(graph.nodes.filter((n) => n.layer === "base").every((b) => graph.edges.some(([a, c]) => c === b.id && node(a).layer === "toolkit"))).toBe(true);
    expect(node("Papers.Toy.main_result")).toMatchObject({ tier: "main", paper: "Papers.Toy" });
    expect(node("Papers.Toy.helper")).toMatchObject({ tier: "aux", owners: ["Papers.Toy.main_result"] });
    expect(node("Toolkit.double")).toMatchObject({ layer: "toolkit", tier: "main", division: "Tricks", topic: "Algebra" });
  });

  it("main view: an auxiliary collapses into its owner, edges lifted", () => {
    const v = mainView(graph);
    expect(v.nodes.map((n) => n.id)).not.toContain("Papers.Toy.helper");
    expect(v.edges).toContainEqual(["Papers.Toy.main_result", "Toolkit.double"]);
    expect(v.edges.some(([a, b]) => a === b)).toBe(false);
  });

  it("measures: isolated results, reuse, a module falling apart, and where a new group attaches", () => {
    const h = toolkitHealth(graph);
    expect(h.isolated).toEqual(["Toolkit.lonely"]);
    expect(h.reuse_rate).toBe(1);
    expect(h.papers).toEqual([{ paper: "Papers.Toy", nodes: 1, reaching_toolkit: 1 }]);
    expect(h.split_suggestions).toEqual([{ module: "Toolkit.Tricks.Algebra.Basic", components: [["Toolkit.double", "Toolkit.double_eq"], ["Toolkit.lonely"]] }]);
    expect(h.fan_in[0]).toEqual({ id: "Toolkit.double", papers: 1 });
    expect(healthSummary(h)).toMatch(/1 of your 1 verified paper\(s\) use the toolkit \(100%\)[\s\S]*Used by nothing yet: lonely/);
    expect(attachNote(graph, ["Papers.Toy.main_result", "Papers.Toy.helper"])).toMatch(/builds on your toolkit's double, double_eq \(in Toolkit\.Tricks\.Algebra\.Basic\)/);
    // A result moved in that nothing uses is a regression the owner hears about.
    const after = buildToolkitGraph({ scan: { ...scan, declarations: scan.declarations.filter((d) => d.name !== "Papers.Toy.main_result") }, now: () => new Date("2026-10-01") });
    expect(healthRegressions(h, toolkitHealth(after), ["Toolkit.double_eq"])).toEqual(["now used by nothing: double_eq"]);
  });
});
