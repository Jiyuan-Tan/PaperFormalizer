// The toolkit graph on a tiny fixture: a scan of a toy toolkit (`double`, `double_eq`, `lonely`) and
// a toy paper whose main result uses its helper and two toolkit declarations
// (`fixtures/toolkit_graph/graph_scan.json`, the compact form `candidate_scan --graph` writes), and
// running that scan: refused before any Lake call with a `CandidateScan.lean` that predates the form.
import { existsSync, readFileSync } from "node:fs";
import { chmod, copyFile, mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { graphScanPath, graphScanSchema, graphScanSupported, runGraphScan, scopedGraphScanPath } from "../../src/proposals/candidate_scan.js";
import { toolkitTemplateDir } from "../../src/toolkit/lakefile.js";
import { cleanSharedToolkit, writeSkeleton } from "../toolkit/helpers.js";
import { LEAN_WS_ENV, lakeHoldMode, leanWsChildEnv } from "../../src/shared/build_mutex.js";
import { attachNote, buildToolkitGraph, duplicateStatementHash, healthRegressions, healthSummary, mainView, refreshToolkitGraph, toolkitGraphPath, toolkitHealth } from "../../src/proposals/toolkit_graph.js";

const scan = graphScanSchema.parse(JSON.parse(readFileSync(path.join(__dirname, "../fixtures/toolkit_graph/graph_scan.json"), "utf8")));
const graph = buildToolkitGraph({ scan, paperMain: new Set(["Papers.Toy.main_result"]), now: () => new Date("2026-10-01") });
const node = (id: string) => graph.nodes.find((n) => n.id === id)!;

describe("toolkit graph", () => {
  it("equal predicate types do not identify definitions or inductive predicates as duplicates", () => {
    const g = buildToolkitGraph({ scan: { ...scan, declarations: [
      { name: "Toolkit.IsBargainingSet", kind: "structure", module: "Toolkit.Tricks.Algebra.Basic", type: "{ι : Type u_1} → Set (ι → ℝ) → Prop", uses: [] },
      { name: "Toolkit.IsSemialgebraic", kind: "inductive", module: "Toolkit.Tricks.Algebra.Basic", type: "{ι : Type u_1} → Set (ι → ℝ) → Prop", uses: [] },
    ] } });
    expect(g.nodes[0]!.statement_hash).toBe(g.nodes[1]!.statement_hash);
    expect(toolkitHealth(g).duplicates).toEqual([]);
    for (const kind of ["def", "structure", "inductive", "instance", "opaque", "axiom"]) {
      expect(duplicateStatementHash({ ...g.nodes[0]!, kind })).toBeUndefined();
    }
    expect(duplicateStatementHash({ ...g.nodes[0]!, kind: "theorem" })).toBe(g.nodes[0]!.statement_hash);
    const theorems = { ...g, nodes: g.nodes.map((n) => ({ ...n, kind: "theorem" })) };
    expect(toolkitHealth(theorems).duplicates).toEqual([["Toolkit.IsBargainingSet", "Toolkit.IsSemialgebraic"]]);
  });

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

describe("the graph scan", () => {
  it("reads only names, kinds, modules, types and uses; base constants and docstrings for toolkit declarations", () => {
    const paperDecls = scan.declarations.filter((d) => d.module.startsWith("Papers."));
    expect(paperDecls.every((d) => d.base === undefined && d.doc === undefined)).toBe(true);
    expect(scan.declarations.find((d) => d.name === "Toolkit.double")?.base?.map((b) => b.name)).toContain("HAdd.hAdd");
    // a statement hash for the nodes of a paper whose types the scan reports (apply_b's duplicate
    // check reads it, `--types-of`), none for one whose types it leaves out
    expect(node("Papers.Toy.main_result").statement_hash).toMatch(/^[0-9a-f]{40}$/);
    const untyped = buildToolkitGraph({ scan: { ...scan, declarations: scan.declarations.map(({ type, ...d }) => (d.module.startsWith("Papers.") ? d : { ...d, type })) }, now: () => new Date("2026-10-01") });
    expect(untyped.nodes.find((n) => n.id === "Papers.Toy.main_result")!.statement_hash).toBeUndefined();
    expect(untyped.nodes.find((n) => n.id === "Toolkit.double")!.statement_hash).toBe(node("Toolkit.double").statement_hash);
    expect(untyped.edges).toEqual(graph.edges);
    // the old form (every constant of every declaration) is not a graph scan
    expect(graphScanSchema.safeParse({ ...scan, declarations: [{ name: "x", kind: "theorem", module: "Papers.X", type: "T", type_constants: [], body_constants: [] }] }).success).toBe(false);
  });

  const toolkitWithExe = async (scanSource: string | null) => {
    const root = await mkdtemp(path.join(os.tmpdir(), "graph-scan-"));
    const cfg = await writeSkeleton(root);
    await writeFile(path.join(root, "lakefile.toml"), 'name = "t"\n\n[[lean_lib]]\nname = "Toolkit"\n\n[[lean_exe]]\nname = "candidate_scan"\nroot = "CandidateScan"\n');
    if (scanSource === null) await copyFile(path.join(toolkitTemplateDir(), "CandidateScan.lean"), path.join(root, "CandidateScan.lean"));
    else await writeFile(path.join(root, "CandidateScan.lean"), scanSource);
    return { root, cfg };
  };

  it("an apply's graph (scoped) is returned, never written over the whole library's doc/toolkit_graph.json", async () => {
    const { root, cfg } = await toolkitWithExe(null);
    try {
      const g = await refreshToolkitGraph({ toolkit: cfg, log: () => undefined, scope: { qid: "toy", papers: ["Papers.Toy"] }, scan: async () => scan, now: () => new Date("2026-10-01") });
      expect(g.edges).toEqual(graph.edges);
      expect(existsSync(toolkitGraphPath(cfg))).toBe(false);
      await refreshToolkitGraph({ toolkit: cfg, log: () => undefined, scan: async () => scan, now: () => new Date("2026-10-01") });
      expect(existsSync(toolkitGraphPath(cfg))).toBe(true);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it("is refused, before any Lake call, with a CandidateScan.lean that predates the compact form", async () => {
    const { root, cfg } = await toolkitWithExe("-- an older scanner: every constant of every declaration\n");
    try {
      const calls: string[][] = [];
      const exec = async (cmd: string, argv: string[]) => { calls.push([cmd, ...argv]); return { code: 0, stdout: "", stderr: "" }; };
      await expect(runGraphScan({ toolkit: cfg, exec, log: () => undefined })).rejects.toThrow(/predates the compact `--graph` scan[\s\S]*copy .*CandidateScan\.lean/);
      expect(calls).toEqual([]);
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it.skipIf(process.platform === "win32")("a scoped scan in the shared tree (`local` false) runs under a shared hold of its papers when shared mode is on, the toolkit clean and the exe up to date; else exclusive", async () => {
    const { root, cfg } = await toolkitWithExe(null);
    await mkdir(path.join(root, "Papers", "Toy"), { recursive: true });
    await writeFile(path.join(root, "Papers", "Toy.lean"), "module\npublic import Papers.Toy.Main\n");
    await writeFile(path.join(root, "Papers", "Toy", "Main.lean"), "module\n");
    const undo = await cleanSharedToolkit(root);
    try {
      const calls: string[] = [];
      let fresh = 0;
      let wouldBuild = false;
      const exec = async (_cmd: string, argv: string[]) => {
        calls.push(`${argv.filter((a) => a !== "--").slice(0, 3).join(" ")} [${lakeHoldMode(root)}]`);
        if (argv[0] === "build" && argv[1] === "--no-build") return { code: fresh, stdout: "", stderr: "" };
        if (argv.includes("exe")) {
          if (wouldBuild && argv[0] === "--no-build") return { code: 3, stdout: "", stderr: "error: target is out-of-date and needs to be rebuilt" };
          const out = argv[argv.indexOf("--out") + 1]!;
          await mkdir(path.dirname(out), { recursive: true });
          await writeFile(out, JSON.stringify(scan));
        }
        return { code: 0, stdout: "", stderr: "" };
      };
      let edits = 0;
      const scoped = async () => {
        // a paper source written: never the scan on record
        await writeFile(path.join(root, "Papers", "Toy", "Main.lean"), `module\n${"-- edit\n".repeat(++edits)}`);
        calls.length = 0;
        await runGraphScan({ toolkit: cfg, scope: { qid: "toy", papers: ["Papers.Toy"] }, exec, log: () => undefined, local: false });
        return [...calls];
      };
      // the exe up to date: its papers' modules built and the scan run under a shared hold, nothing else built
      expect(await scoped()).toEqual(["build --no-build candidate_scan [null]", "build Papers.Toy [shared]", "--no-build exe candidate_scan [shared]"]);
      // the exe not up to date: exclusive, as before
      fresh = 1;
      expect(await scoped()).toEqual(["build --no-build candidate_scan [null]", "build Toolkit Papers.Toy [exclusive]", "exe candidate_scan --graph [exclusive]"]);
      // the scan would build something under the shared hold: run again exclusive
      fresh = 0;
      wouldBuild = true;
      expect(await scoped()).toEqual(["build --no-build candidate_scan [null]", "build Papers.Toy [shared]", "--no-build exe candidate_scan [shared]",
        "build Toolkit Papers.Toy [exclusive]", "exe candidate_scan --graph [exclusive]"]);
      wouldBuild = false;
    } finally {
      await undo();
      await rm(root, { recursive: true, force: true });
    }
  });

  it.skipIf(process.platform === "win32")("an apply's scan is reused while the toolkit and its paper are unchanged, and taken again once either changes", async () => {
    const { root, cfg } = await toolkitWithExe(null);
    const bin = path.join(root, "fakebin");
    await mkdir(bin, { recursive: true });
    await writeFile(path.join(bin, "lean"), "#!/bin/sh\necho 'Lean (version 4.0.0, test)'\n");
    await chmod(path.join(bin, "lean"), 0o755);
    const PATH = process.env.PATH;
    process.env.PATH = `${bin}:${PATH}`;
    try {
      await mkdir(path.join(root, "Toolkit", "Foundations"), { recursive: true });
      await writeFile(path.join(root, "Toolkit.lean"), "module\n");
      await writeFile(path.join(root, "Toolkit", "Foundations", "A.lean"), "module\ntheorem a : True := trivial\n");
      await mkdir(path.join(root, "Papers", "Toy"), { recursive: true });
      await writeFile(path.join(root, "Papers", "Toy.lean"), "module\n");
      await writeFile(path.join(root, "Papers", "Toy", "Main.lean"), "module\ntheorem m : True := trivial\n");
      const calls: string[][] = [];
      const exec = async (cmd: string, argv: string[]) => {
        calls.push([cmd, ...argv]);
        if (argv[0] === "exe") {
          const out = argv[argv.indexOf("--out") + 1]!;
          await mkdir(path.dirname(out), { recursive: true });
          await writeFile(out, JSON.stringify(scan));
        }
        return { code: 0, stdout: "", stderr: "" };
      };
      const logs: string[] = [];
      const scoped = () => runGraphScan({ toolkit: cfg, scope: { qid: "toy", papers: ["Papers.Toy"] }, exec, log: (m) => logs.push(m), local: false });
      await scoped();
      expect(calls).toHaveLength(2);
      // unchanged: reused, no Lake turn
      expect((await scoped()).declarations).toHaveLength(scan.declarations.length);
      expect(calls).toHaveLength(2);
      expect(logs.at(-1)).toMatch(/toolkit graph: reusing .*unchanged since it was taken/);
      // the paper changed: scanned again
      await writeFile(path.join(root, "Papers", "Toy", "Main.lean"), "module\ntheorem m : True := trivial\ntheorem n : True := trivial\n");
      await scoped();
      expect(calls).toHaveLength(4);
      // the toolkit changed (a promotion appended to a module): scanned again
      await writeFile(path.join(root, "Toolkit", "Foundations", "A.lean"), "module\ntheorem a : True := trivial\ntheorem b : True := trivial\n");
      await scoped();
      expect(calls).toHaveLength(6);
      // a Staging write does not count (no scanned module imports Staging)
      await mkdir(path.join(root, "Toolkit", "Staging"), { recursive: true });
      await writeFile(path.join(root, "Toolkit", "Staging", "S.lean"), "module\n");
      await scoped();
      expect(calls).toHaveLength(6);
      // a paper importing a Staging module is always scanned afresh
      await writeFile(path.join(root, "Papers", "Toy", "Main.lean"), "module\nimport Toolkit.Staging.S\ntheorem m : True := trivial\n");
      await scoped();
      await scoped();
      expect(calls).toHaveLength(10);
    } finally {
      process.env.PATH = PATH;
      await rm(root, { recursive: true, force: true });
    }
  });

  /** A fake Lake for the whole library's scan: `codes` maps a command (its argv joined) to its exit
   *  code (0 otherwise); the exe writes the fixture scan. Each call is recorded with the hold mode. */
  const fakeLake = (root: string, codes: Record<string, number>) => {
    const calls: string[] = [];
    const exec = async (_cmd: string, argv: string[]) => {
      const label = argv[0] === "exe" ? `exe --modules ${argv[argv.indexOf("--modules") + 1]}` : argv.join(" ");
      calls.push(`${label} [${lakeHoldMode(root)}]`);
      if (argv[0] === "exe") {
        const out = argv[argv.indexOf("--out") + 1]!;
        await mkdir(path.dirname(out), { recursive: true });
        await writeFile(out, JSON.stringify(scan));
        return { code: 0, stdout: "", stderr: "" };
      }
      const code = codes[label] ?? 0;
      return { code, stdout: "", stderr: code ? `error: ${label} failed` : "" };
    };
    return { calls, exec };
  };
  const threePapers = "module\npublic import Papers.Alpha\npublic import Papers.Beta.Sub\nimport Papers.Gamma\n";

  it.skipIf(process.platform === "win32")("in a workspace the whole library's scan builds only the toolkit, the exe and the papers the barrel lacks, leaves out what does not build, takes no shared-tree lock, and puts the scan in the shared toolkit", async () => {
    const { root, cfg } = await toolkitWithExe(null);
    const ws = await mkdtemp(path.join(os.tmpdir(), "graph-scan-ws-"));
    const prior = process.env[LEAN_WS_ENV];
    try {
      await writeFile(path.join(root, "Papers.lean"), threePapers);
      // a run in progress, not in the barrel yet (built on its own), and a directory without a barrel
      await mkdir(path.join(root, "Papers"), { recursive: true });
      await writeFile(path.join(root, "Papers", "Delta.lean"), "module\n");
      await mkdir(path.join(root, "Papers", "Eps"), { recursive: true });
      await writeFile(path.join(root, "Papers", "Eps", "Main.lean"), "module\n");
      await writeFile(path.join(ws, ".pf-toolkit"), `${root}\n`);
      await writeFile(path.join(ws, ".pf-gen"), JSON.stringify({ gen: 7 }));
      process.env[LEAN_WS_ENV] = ws;
      // the default exec's lake (`spawnWithInactivityTimeout`) goes to the workspace through the shim
      expect(leanWsChildEnv()[LEAN_WS_ENV]).toBe(ws);
      const { calls, exec } = fakeLake(root, { "build --no-build Papers": 3, "build --no-build Papers.Gamma": 3 });
      const outs: string[] = [];
      const logs: string[] = [];
      const got = await runGraphScan({ toolkit: cfg, exec: async (c, a, o) => { if (a[0] === "exe") outs.push(a[a.indexOf("--out") + 1]!); return exec(c, a); }, log: (m) => logs.push(m) });
      expect(calls).toEqual([
        "build Toolkit candidate_scan [null]",
        "build --no-build Papers [null]",
        "build --no-build Papers.Alpha [null]", "build --no-build Papers.Beta [null]", "build --no-build Papers.Gamma [null]",
        "build Papers.Delta [null]",
        "exe --modules Toolkit,Papers.Alpha,Papers.Beta,Papers.Delta [null]",
      ]);
      expect(got.excluded_papers).toEqual(["Papers.Eps", "Papers.Gamma"]);
      expect(got.generation).toBe(7);
      expect(logs.join("\n")).toContain("2 paper(s) left out — their modules do not build in the workspace: Papers.Eps, Papers.Gamma");
      expect(existsSync(path.join(root, ".lake-build.lock"))).toBe(false);
      // the exe writes inside the workspace; the scan is put in place in the shared toolkit
      expect(outs[0]!.startsWith(ws)).toBe(true);
      const onFile = JSON.parse(readFileSync(graphScanPath(cfg), "utf8"));
      expect(onFile).toMatchObject({ excluded_papers: ["Papers.Eps", "Papers.Gamma"], generation: 7 });
      expect(graphScanPath(cfg).startsWith(root)).toBe(true);
      const g = await refreshToolkitGraph({ toolkit: cfg, log: () => undefined, scan: async () => got });
      expect(g).toMatchObject({ excluded_papers: ["Papers.Eps", "Papers.Gamma"], generation: 7 });
      expect(JSON.parse(readFileSync(toolkitGraphPath(cfg), "utf8")).excluded_papers).toEqual(["Papers.Eps", "Papers.Gamma"]);
      // every barrel paper up to date there: one check
      const ok = fakeLake(root, {});
      await runGraphScan({ toolkit: cfg, exec: ok.exec, log: () => undefined });
      expect(ok.calls).toEqual(["build Toolkit candidate_scan [null]", "build --no-build Papers [null]", "build Papers.Delta [null]",
        "exe --modules Toolkit,Papers.Alpha,Papers.Beta,Papers.Delta,Papers.Gamma [null]"]);
      // the toolkit does not build there: fatal
      const bad = fakeLake(root, { "build Toolkit candidate_scan": 1 });
      await expect(runGraphScan({ toolkit: cfg, exec: bad.exec, log: () => undefined })).rejects.toThrow(/`lake build Toolkit candidate_scan` failed/);
      expect(bad.calls).toEqual(["build Toolkit candidate_scan [null]"]);
      // the shim held off (the toolkit in flux): no paper is judged by it
      const held = fakeLake(root, { "build --no-build Papers": 3, "build --no-build Papers.Beta": 75 });
      await expect(runGraphScan({ toolkit: cfg, exec: held.exec, log: () => undefined })).rejects.toThrow(/`lake build --no-build Papers\.Beta` failed/);
      expect(held.calls.some((c) => c.startsWith("exe"))).toBe(false);
    } finally {
      if (prior === undefined) delete process.env[LEAN_WS_ENV];
      else process.env[LEAN_WS_ENV] = prior;
      await rm(ws, { recursive: true, force: true });
      await rm(root, { recursive: true, force: true });
    }
  });

  it("a paper left out keeps the uses the last graph on file had for it, carried from graph to graph", async () => {
    const { root, cfg } = await toolkitWithExe(null);
    try {
      // the last graph: the paper in it, using two toolkit declarations
      await refreshToolkitGraph({ toolkit: cfg, log: () => undefined, scan: async () => scan });
      const uses = graph.edges.filter(([a, b]) => a.startsWith("Papers.Toy.") && node(b).layer === "toolkit").map(([, b]) => b).sort();
      expect(uses.length).toBeGreaterThan(0);
      // now it does not build: left out, its uses carried
      const without = { ...scan, declarations: scan.declarations.filter((d) => !d.module.startsWith("Papers.")), excluded_papers: ["Papers.Toy"] };
      const g1 = await refreshToolkitGraph({ toolkit: cfg, log: () => undefined, scan: async () => without });
      expect(g1.excluded_paper_uses).toEqual({ "Papers.Toy": [...new Set(uses)] });
      // still out next time: the uses the last graph carried
      const g2 = await refreshToolkitGraph({ toolkit: cfg, log: () => undefined, scan: async () => without });
      expect(g2.excluded_paper_uses).toEqual({ "Papers.Toy": [...new Set(uses)] });
      // back in: nothing carried
      const g3 = await refreshToolkitGraph({ toolkit: cfg, log: () => undefined, scan: async () => scan });
      expect(g3.excluded_paper_uses).toBeUndefined();
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });

  it("runs with the template's CandidateScan.lean and returns the compact scan", async () => {
    expect(graphScanSupported(path.join(toolkitTemplateDir()))).toBe(true);
    const { root, cfg } = await toolkitWithExe(null);
    try {
      const calls: string[][] = [];
      const exec = async (cmd: string, argv: string[]) => {
        calls.push([cmd, ...argv]);
        if (argv[0] === "exe") {
          const out = argv[argv.indexOf("--out") + 1]!;
          await mkdir(path.dirname(out), { recursive: true });
          await writeFile(out, JSON.stringify(scan));
        }
        return { code: 0, stdout: "", stderr: "" };
      };
      // the whole library's graph: in a workspace only, never built in the shared tree
      await expect(runGraphScan({ toolkit: cfg, exec, log: () => undefined })).rejects.toThrow(/the whole library's graph is built in a workspace only/);
      expect(calls).toEqual([]);
      // an apply's graph: the toolkit and its paper only, typed, in the run's own file
      const got = await runGraphScan({ toolkit: cfg, scope: { qid: "toy", papers: ["Papers.Toy"] }, exec, log: () => undefined, local: false });
      expect(calls[0]).toEqual(["lake", "build", "Toolkit", "Papers.Toy", "candidate_scan"]);
      expect(calls[1]).toEqual(expect.arrayContaining(["--modules", "Toolkit,Papers.Toy", "--types-of", "Papers.Toy", "--out", scopedGraphScanPath(cfg, "toy")]));
      expect(got.declarations.map((d) => d.name)).toEqual(scan.declarations.map((d) => d.name));
      // a round-A apply's: the toolkit alone
      calls.length = 0;
      await runGraphScan({ toolkit: cfg, scope: { qid: "toy", papers: [] }, exec, log: () => undefined, local: false });
      expect(calls[0]).toEqual(["lake", "build", "Toolkit", "candidate_scan"]);
      expect(calls[1]).toEqual(expect.arrayContaining(["--modules", "Toolkit"]));
      expect(calls[1]).not.toContain("--types-of");
    } finally {
      await rm(root, { recursive: true, force: true });
    }
  });
});
