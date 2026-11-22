// Gardening: findings from the toolkit graph, what the gardener reads, the owner's list, and the
// verification of the items the orchestrator carried out by hand.
import { spawnSync } from "node:child_process";
import { chmod, copyFile, mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { appendReuseHistory, paperOfSlug, gardenerSources, gardenerViolations, gardenFindings, gardenPaths, parseGardenChecklist, readReuseHistory, renderGardenChecklist, runGardenRound, settledFindings, type GardenBatch, type GardenFinding } from "../../src/proposals/garden.js";
import { baselineDiffers, papersReached, realBaselineWorkspace, realVerifyDeps, verifyGarden } from "../../src/proposals/garden_verify.js";
import { LAKE_SHIM_DIR, LEAN_WS_ENV, leanWorkspaceFor, leanWsChildEnv } from "../../src/shared/build_mutex.js";
import { sha256 } from "../../src/proposals/gate.js";
import { buildToolkitGraph, type ToolkitGraph, type ToolkitHealth } from "../../src/proposals/toolkit_graph.js";
import type { GraphScan } from "../../src/proposals/candidate_scan.js";
import { shq } from "../../src/proposals/gate.js";
import { toolkitTemplateDir } from "../../src/toolkit/lakefile.js";
import { effectiveTaxonomy } from "../../src/toolkit/taxonomy.js";
import type { ClaudeRunInput } from "../../src/workers/claude.js";
import { BARREL, leanModule, tk, writeSkeleton } from "../toolkit/helpers.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

function graph(): ToolkitGraph {
  const n = (id: string, module: string, extra: Record<string, unknown> = {}) => ({ id, layer: "toolkit" as const, kind: "theorem", module, division: module.split(".")[1], topic: module.split(".")[2], tier: "main" as const, ...extra });
  return {
    version: 1, built_at: "t", toolkit_prefix: "Toolkit", papers_prefix: "Papers",
    nodes: [
      n("Toolkit.cond_indep", "Toolkit.Foundations.Probability.Conditioning"),
      n("Toolkit.design_mean", "Toolkit.Foundations.Probability.Conditioning"),
      n("Toolkit.weird", "Toolkit.Foundations.Astrology.Stars"),
      { id: "Causalean.FiniteDesign.E", layer: "base" as const, kind: "base", module: "Causalean.Stat.FiniteDesign" },
      { id: "Papers.P.thm", layer: "paper" as const, kind: "theorem", module: "Papers.P.Main", paper: "Papers.P", tier: "main" as const },
    ],
    edges: [["Toolkit.design_mean", "Causalean.FiniteDesign.E"], ["Papers.P.thm", "Toolkit.cond_indep"], ["Papers.P.thm", "Toolkit.design_mean"], ["Papers.P.thm", "Toolkit.weird"]],
  };
}

const git = (cwd: string, ...args: string[]) => {
  const r = spawnSync("git", args, { cwd, encoding: "utf8" });
  if (r.status !== 0) throw new Error(`git ${args.join(" ")}: ${r.stderr}`);
  return r.stdout;
};

describe("gardening", () => {
  it("a split that lists a helper, drops a main result or places one twice is told which", async () => {
    const taxonomy = await effectiveTaxonomy({ toolkitRoot: "/none" });
    const topic = taxonomy.topics[0]!.path;
    const mod = (f: string) => `Toolkit/${topic}/${f}.lean`;
    const finding = { id: "g-1", kind: "split", modules: [mod("Tails")], decls: ["T.a", "T.b"], detail: "two subjects" } as never;
    const item = (parts: Array<{ module: string; decls: string[] }>) => ({
      finding_id: "g-1", title: "Split Tails", finding: "two subjects", reason: "unrelated", recommendation: "accept", action: "split",
      target_module: null, modules: [mod("Tails")], parts, replacement: null, new_topic: null,
    }) as never;
    const check = (parts: Array<{ module: string; decls: string[] }>) => gardenerViolations([item(parts)], [finding], { lib: "Toolkit", divisions: [topic.split("/")[0]!] }, taxonomy).filter((x) => x.includes("split"));
    expect(check([{ module: mod("Tails"), decls: ["T.a"] }, { module: mod("Forms"), decls: ["T.b"] }])).toEqual([]);
    expect(check([{ module: mod("Tails"), decls: ["T.a"] }, { module: mod("Forms"), decls: ["T.b", "T.helper"] }]).join(" ")).toContain("split lists T.helper, which is not among the module's main results (T.a, T.b) — a helper moves with the result it serves; leave it out.");
    expect(check([{ module: mod("Tails"), decls: ["T.a"] }, { module: mod("Forms"), decls: ["T.a"] }]).join(" ")).toMatch(/leaves T\.b in no part.*places T\.a in more than one part/);
  });

  it("finds what the graph and the modules show — one direction finding per applied module, aimed at the most basic module building on it", async () => {
    const g = graph();
    g.nodes.push(
      { id: "Toolkit.Tricks.Probability.trick", layer: "toolkit", kind: "theorem", module: "Toolkit.Tricks.Probability.T", division: "Tricks", topic: "Probability", tier: "main" },
      { id: "Toolkit.inst", layer: "toolkit", kind: "instance", module: "Toolkit.Foundations.Probability.Conditioning", division: "Foundations", topic: "Probability", tier: "aux", owners: ["Toolkit.cond_indep"] },
      { id: "Toolkit.Foundations.Design.counts", layer: "toolkit", kind: "def", module: "Toolkit.Foundations.Design.D", division: "Foundations", topic: "Design", tier: "aux", owners: [] },
      { id: "Toolkit.Foundations.Design.base", layer: "toolkit", kind: "def", module: "Toolkit.Foundations.Design.D", division: "Foundations", topic: "Design", tier: "aux", owners: [] },
      { id: "Toolkit.Foundations.Combinatorics.Counting.card", layer: "toolkit", kind: "theorem", module: "Toolkit.Foundations.Combinatorics.Counting.C", division: "Foundations", topic: "Combinatorics", tier: "main" },
      { id: "Toolkit.Foundations.Probability.Independence.exch", layer: "toolkit", kind: "theorem", module: "Toolkit.Foundations.Probability.Independence.E", division: "Foundations", topic: "Probability", tier: "main" },
    );
    g.edges.push(
      ["Toolkit.cond_indep", "Toolkit.Tricks.Probability.trick"], ["Toolkit.inst", "Causalean.FiniteDesign.E"],
      ["Toolkit.Foundations.Combinatorics.Counting.card", "Toolkit.Foundations.Design.counts"],
      ["Toolkit.Foundations.Probability.Independence.exch", "Toolkit.Foundations.Design.counts"],
      ["Toolkit.Foundations.Design.counts", "Toolkit.Foundations.Design.base"],
    );
    const texts = new Map([
      ["Toolkit.Foundations.Combinatorics.Counting.C", leanModule({ imports: ["Toolkit.Foundations.Design.D"], body: "namespace Toolkit.Foundations.Design\n\ntheorem card : True := trivial\n\nend Toolkit.Foundations.Design" })],
      ["Toolkit.Foundations.Probability.Independence.E", leanModule({ imports: ["Toolkit.Foundations.Design.D"], body: "namespace Toolkit.Foundations.Probability.Independence\n\ntheorem exch : True := trivial\n\nend Toolkit.Foundations.Probability.Independence" })],
      ["Toolkit.Foundations.Design.D", leanModule({ imports: ["Mathlib.Tactic"], body: "namespace Toolkit.Foundations.Design\n\ndef base : Nat := 0\n\ndef counts : Nat := base\n\nend Toolkit.Foundations.Design" })],
    ]);
    const f = gardenFindings({ cfg: tk("/tk"), graph: g, taxonomy: await effectiveTaxonomy({ toolkitRoot: "/none" }), moduleTexts: texts });
    expect(f.map((x) => [x.kind, x.modules[0]])).toEqual(expect.arrayContaining([
      ["outside_topic_tree", "Toolkit/Foundations/Astrology/Stars.lean"],
      ["layering", "Toolkit/Foundations/Probability/Conditioning.lean"],
      ["namespace", "Toolkit/Foundations/Combinatorics/Counting/C.lean"],
      ["umbrella_import", "Toolkit/Foundations/Design/D.lean"],
    ]));
    const direction = f.filter((x) => x.kind === "direction");
    expect(direction).toHaveLength(1);
    expect(direction[0]).toMatchObject({
      modules: ["Toolkit/Foundations/Design/D.lean", "Toolkit/Foundations/Combinatorics/Counting/C.lean", "Toolkit/Foundations/Probability/Independence/E.lean"],
      // What the dependents use, with what it needs inside the module.
      shared: ["Toolkit.Foundations.Design.base", "Toolkit.Foundations.Design.counts"],
      target: "Toolkit/Foundations/Combinatorics/Counting/C.lean",
    });
    expect(f.find((x) => x.kind === "layering")!.decls).toEqual(["Toolkit.cond_indep"]);
    expect(f.some((x) => x.decls.includes("Toolkit.design_mean") || x.decls.includes("Toolkit.inst"))).toBe(false);
  });

  it("the gardener reads in full the modules a finding names and those changed since the last list, within a cap", () => {
    const texts = new Map([
      ["Toolkit.Foundations.A.X", "module X -- unchanged, named by a finding"],
      ["Toolkit.Foundations.B.Y", "module Y -- changed"],
      ["Toolkit.Foundations.C.Z", "module Z -- unchanged"],
    ]);
    const last = { "Toolkit.Foundations.A.X": sha256(texts.get("Toolkit.Foundations.A.X")!), "Toolkit.Foundations.B.Y": "old", "Toolkit.Foundations.C.Z": sha256(texts.get("Toolkit.Foundations.C.Z")!) };
    const findings = [{ id: "g-1", kind: "namespace" as const, modules: ["Toolkit/Foundations/A/X.lean"], decls: [], detail: "d" }];
    const s = gardenerSources(texts, last, findings);
    expect(s.included.map((x) => [x.module, x.why])).toEqual([["Toolkit.Foundations.A.X", "finding"], ["Toolkit.Foundations.B.Y", "changed"]]);
    expect(gardenerSources(texts, null, []).included.map((x) => x.module)).toEqual([...texts.keys()].sort());
    expect(gardenerSources(texts, null, [], 30).omitted.length).toBeGreaterThan(0);
  });

  it("a finding the last list's gardener judged fine is settled while its modules stand: same kind and detail over the same content", () => {
    const f = (id: string, kind: GardenFinding["kind"], module: string, detail: string): GardenFinding => ({ id, kind, modules: [module], decls: [], detail });
    const hashes = { "Toolkit.Foundations.A.X": sha256("x"), "Toolkit.Foundations.B.Y": sha256("y") };
    const last = {
      findings: [f("g-1", "unused", "Toolkit/Foundations/A/X.lean", "x_thm is used by nothing"), f("g-2", "unused", "Toolkit/Foundations/B/Y.lean", "y_thm is used by nothing"), f("g-3", "umbrella_import", "Toolkit/Foundations/A/X.lean", "imports all")],
      left_as_is: [{ finding_id: "g-1", title: "Keep x", reason: "a textbook fact" }, { finding_id: "g-2", title: "Keep y", reason: "fine" }],
      module_hashes: hashes,
    };
    const now = [f("g-1", "unused", "Toolkit/Foundations/A/X.lean", "x_thm is used by nothing"), f("g-2", "unused", "Toolkit/Foundations/B/Y.lean", "y_thm is used by nothing"), f("g-3", "umbrella_import", "Toolkit/Foundations/A/X.lean", "imports all")];
    // the same toolkit: the two kept findings are settled, the one the gardener acted on is not
    expect([...settledFindings(now, last, hashes)].map(([x, p]) => [x.id, p.title])).toEqual([["g-1", "Keep x"], ["g-2", "Keep y"]]);
    // Y changed since: its finding is judged afresh; X's stands
    expect([...settledFindings(now, last, { ...hashes, "Toolkit.Foundations.B.Y": sha256("y2") })].map(([x]) => x.id)).toEqual(["g-1"]);
    // a module whose content is unknown, or no list before: nothing is settled
    expect(settledFindings(now, last, { "Toolkit.Foundations.A.X": sha256("x") }).size).toBe(1);
    expect(settledFindings(now, null, hashes).size).toBe(0);
  });

  it("the gardener is not asked again about findings it judged fine on the last list; a changed module brings its findings back, the rest are carried", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "garden-round-"));
    tmp.push(root);
    const cfg = await writeSkeleton(root);
    const g = graph();
    g.nodes.push({ id: "Toolkit.lonely", layer: "toolkit", kind: "theorem", module: "Toolkit.Foundations.Probability.Conditioning", division: "Foundations", topic: "Probability", tier: "main" });
    const stars = (note: string) => leanModule({ imports: ["Mathlib.Tactic"], body: `namespace Toolkit.Foundations.Astrology\n\n${note}\ntheorem weird : True := trivial\n\nend Toolkit.Foundations.Astrology` });
    const texts = (note: string) => new Map([
      ["Toolkit.Foundations.Probability.Conditioning", leanModule({ imports: ["Mathlib.Tactic"], body: "namespace Toolkit.Foundations.Probability\n\ntheorem lonely : True := trivial\n\nend Toolkit.Foundations.Probability" })],
      ["Toolkit.Foundations.Astrology.Stars", stars(note)],
    ]);
    // the gardener keeps every finding it is shown
    const shown: GardenFinding[][] = [];
    const keepAll = async (o: ClaudeRunInput): Promise<string> => {
      const text = o.prompt.slice(o.prompt.indexOf("=== FINDINGS ===\n") + "=== FINDINGS ===\n".length, o.prompt.indexOf("\n=== END FINDINGS ==="));
      const findings = (text.trim() === "(none)" ? [] : JSON.parse(text)) as GardenFinding[];
      shown.push(findings);
      return JSON.stringify({
        items: findings.map((f) => ({ finding_id: f.id, title: `Keep ${f.id}`, finding: f.detail, reason: "fine as it is", recommendation: "decline", action: "keep", target_module: null, modules: [], parts: [], replacement: null, new_topic: null })),
        extra: [],
      });
    };
    const logs: string[] = [];
    const round = (day: number, note: string) => runGardenRound({ toolkit: cfg, graph: g, log: (m) => logs.push(m), now: () => new Date(`2026-10-0${day}T00:00:00.000Z`), runClaude: keepAll, scan: null, moduleTexts: texts(note) });
    const batchOf = async (day: number): Promise<GardenBatch> => JSON.parse(await readFile(gardenPaths(cfg, `2026-10-0${day}T00:00:00.000Z`).json, "utf8")) as GardenBatch;

    expect(await round(1, "")).toBeNull();
    const first = await batchOf(1);
    const n = first.findings.length;
    expect(n).toBeGreaterThanOrEqual(2);
    expect(first.findings.some((f) => f.kind === "outside_topic_tree")).toBe(true);
    expect(first.findings.some((f) => f.kind === "unused" && f.decls.includes("Toolkit.lonely"))).toBe(true);
    expect(first.left_as_is).toHaveLength(n);
    expect(shown).toHaveLength(1);

    // the same toolkit again: no call, no list
    expect(await round(2, "")).toBeNull();
    expect(shown).toHaveLength(1);
    expect(logs.at(-1)).toMatch(/no new findings and no new main results since the last list \(\d+ judged fine on it, unchanged since\) — nothing to garden/);

    // the Astrology module changed: its finding is sent again, the others stand with their earlier judgement
    expect(await round(3, "-- a comment")).toBeNull();
    expect(shown).toHaveLength(2);
    const fresh = shown[1]!;
    expect(fresh.map((f) => [f.id, f.kind, f.modules])).toEqual([["g-1", "outside_topic_tree", ["Toolkit/Foundations/Astrology/Stars.lean"]], ["g-2", "umbrella_import", ["Toolkit/Foundations/Astrology/Stars.lean"]]]);
    expect(fresh.length).toBeLessThan(n);
    const third = await batchOf(3);
    expect(third.findings).toHaveLength(n);
    expect(new Set(third.findings.map((f) => f.id)).size).toBe(n);
    expect(third.left_as_is).toHaveLength(n);
    expect(third.findings.map((f) => [f.kind, f.modules[0]]).sort()).toEqual(first.findings.map((f) => [f.kind, f.modules[0]]).sort());
    // the carried ones keep the earlier judgement, under the ids they now have on the list
    const carried = third.left_as_is!.filter((x) => !fresh.some((f) => f.id === x.finding_id));
    expect(carried).toHaveLength(n - fresh.length);
    for (const c of carried) expect(third.findings.some((f) => f.id === c.finding_id && f.modules[0] !== "Toolkit/Foundations/Astrology/Stars.lean")).toBe(true);
    expect(logs.join("\n")).toContain(`gardening: ${n - fresh.length} finding(s) judged fine on the last list and unchanged since are not sent again`);
  });

  it("a result the ledger records as used by a paper left out of the graph is not reported unused; the list names the papers left out", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "garden-excluded-"));
    tmp.push(root);
    const cfg = await writeSkeleton(root);
    const mod = "Toolkit.Foundations.Probability.Conditioning";
    const tkNode = (id: string, extra: Record<string, unknown> = {}) => ({ id, layer: "toolkit" as const, kind: "theorem", module: mod, division: "Foundations", topic: "Probability", tier: "main" as const, ...extra });
    // Toolkit.fourth: no ledger record, but the last graph that had Papers.GammaPaper saw it use it
    const g: ToolkitGraph = { ...graph(), excluded_papers: ["Papers.BetaPaper", "Papers.GammaPaper"], excluded_paper_uses: { "Papers.GammaPaper": ["Toolkit.fourth", "Toolkit.oldname"] }, generation: 7 };
    g.nodes.push(tkNode("Toolkit.alone"), tkNode("Toolkit.lonely"), tkNode("Toolkit.third"), tkNode("Toolkit.fourth"), tkNode("Toolkit.fifth"), tkNode("Toolkit.owner"), tkNode("Toolkit.helper", { tier: "aux", owners: ["Toolkit.owner"] }));
    g.edges.push(["Toolkit.owner", "Toolkit.helper"]);
    const rec = (name: string, used_by: string[]) => ({ name, module: mod, division: "Foundations", origin: { kind: "proposal", slug: "seed" }, date: "2026-10-01", decision: "accepted", used_by });
    await writeFile(cfg.ledgerPath, JSON.stringify({ version: 1, declarations: [
      rec("Toolkit.alone", ["alpha_paper"]), // its paper is in the graph: unused stands
      rec("Toolkit.lonely", ["beta_paper"]), // runs/beta_paper/state.json lean_subdir
      rec("Toolkit.third", ["gamma_paper"]), // no state.json: the canonical Papers/<Pascal>
      rec("Toolkit.helper", ["beta_paper"]), // a helper: its owner's use
      { ...rec("Toolkit.fifth", []), renamed_from: "Toolkit.oldname" }, // the last graph saw its old name used
    ], decisions: [] }));
    await mkdir(path.join(cfg.runsDir, "beta_paper"), { recursive: true });
    await writeFile(path.join(cfg.runsDir, "beta_paper", "state.json"), JSON.stringify({ qid: "beta_paper", lean_subdir: "Papers/BetaPaper" }));
    expect(await paperOfSlug(cfg, "beta_paper")).toBe("Papers.BetaPaper");
    expect(await paperOfSlug(cfg, "gamma_paper")).toBe("Papers.GammaPaper");
    const prompts: string[] = [];
    const gardener = async (o: ClaudeRunInput): Promise<string> => {
      prompts.push(o.prompt);
      const text = o.prompt.slice(o.prompt.indexOf("=== FINDINGS ===\n") + "=== FINDINGS ===\n".length, o.prompt.indexOf("\n=== END FINDINGS ==="));
      const findings = JSON.parse(text) as GardenFinding[];
      return JSON.stringify({
        items: findings.map((f) => ({ finding_id: f.id, title: `Item ${f.id}`, finding: f.detail, reason: "r", recommendation: f.kind === "unused" ? "accept" : "decline",
          action: f.kind === "unused" ? "remove" : "keep", target_module: null, modules: [], parts: [], replacement: null, new_topic: null })),
        extra: [],
      });
    };
    const logs: string[] = [];
    const out = await runGardenRound({ toolkit: cfg, graph: g, log: (m) => logs.push(m), now: () => new Date("2026-10-05T00:00:00.000Z"), runClaude: gardener, scan: null, moduleTexts: new Map() });
    expect(out).not.toBeNull();
    const batch = JSON.parse(await readFile(gardenPaths(cfg, "2026-10-05T00:00:00.000Z").json, "utf8")) as GardenBatch;
    const unused = batch.findings.filter((f) => f.kind === "unused").flatMap((f) => f.decls);
    expect(unused).toContain("Toolkit.alone");
    expect(unused).not.toContain("Toolkit.lonely");
    expect(unused).not.toContain("Toolkit.third");
    expect(unused).not.toContain("Toolkit.owner");
    expect(unused).not.toContain("Toolkit.fourth");
    expect(unused).not.toContain("Toolkit.fifth");
    expect(batch.excluded_papers).toEqual(["Papers.BetaPaper", "Papers.GammaPaper"]);
    expect(batch.generation).toBe(7);
    expect(prompts[0]).toContain("PAPERS NOT IN THE GRAPH");
    expect(logs.join("\n")).toContain("2 paper(s) left out of the graph (they do not build): Papers.BetaPaper, Papers.GammaPaper; 5 toolkit declaration(s)");
    const md = await readFile(out!.path, "utf8");
    expect(md.indexOf("**Papers left out of the graph**")).toBeGreaterThan(0);
    expect(md.indexOf("**Papers left out of the graph**")).toBeLessThan(md.indexOf("## g-"));
    expect(md).toContain("Papers.BetaPaper, Papers.GammaPaper");
    // the list lands in the toolkit's own doc/proposals (where the orchestrator reads it)
    expect(path.dirname(out!.path)).toBe(path.join(root, "doc", "proposals"));
  });

  it("the reuse history keeps one line per paper: a round B run again replaces the paper's line", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "reuse-history-"));
    tmp.push(root);
    const health = { toolkit_nodes: 3, reuse_rate: 0.5 } as ToolkitHealth;
    await appendReuseHistory({ toolkitRoot: root }, { slug: "a", at: "t1", reuse: null, health });
    await appendReuseHistory({ toolkitRoot: root }, { slug: "b", at: "t2", reuse: null, health });
    await appendReuseHistory({ toolkitRoot: root }, { slug: "a", at: "t3", reuse: null, health: { ...health, toolkit_nodes: 4 } });
    expect((await readReuseHistory({ toolkitRoot: root })).map((l) => [l.slug, l.at, l.toolkit_main_results])).toEqual([["b", "t2", 3], ["a", "t3", 4]]);
  });

  it("verifies the items carried out by hand against the committed toolkit, follows renames, refuses a changed paper statement", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "garden-verify-"));
    tmp.push(root);
    const cfg = await writeSkeleton(root);
    const mod = "Toolkit.Foundations.Probability.Conditioning";
    const modPath = path.join(root, "Toolkit/Foundations/Probability/Conditioning.lean");
    await mkdir(path.dirname(modPath), { recursive: true });
    await writeFile(modPath, leanModule({ doc: mod, body: "namespace IndepFun\n\n/-- Survives. -/\ntheorem cond_preimage (n : Nat) : n = n := rfl\n\nend IndepFun" }));
    await writeFile(path.join(root, "Toolkit/Foundations.lean"), BARREL("Toolkit.Foundations", [mod]));
    const paper = path.join(root, "Papers/P/Main.lean");
    await mkdir(path.dirname(paper), { recursive: true });
    await writeFile(paper, leanModule({ imports: [mod], body: "namespace Papers.P\n\ntheorem thm (n : Nat) : n = n := IndepFun.cond_preimage n\n\nend Papers.P" }));
    await writeFile(cfg.ledgerPath, JSON.stringify({ version: 1, declarations: [{ name: "IndepFun.cond_preimage", module: mod, division: "Foundations", origin: { kind: "proposal", slug: "p" }, date: "2026-10-01", decision: "accepted", used_by: [] }], decisions: [] }));
    const batch: GardenBatch = {
      created: "2026-10-02T00:00:00.000Z",
      findings: [{ id: "g-1", kind: "namespace", modules: ["Toolkit/Foundations/Probability/Conditioning.lean"], decls: ["IndepFun.cond_preimage"], detail: "outside" }],
      items: [{ finding_id: "g-1", title: "Name it in its topic", finding: "outside", reason: "consistent", recommendation: "accept", action: "rename",
        target_module: null, modules: [], parts: [], replacement: null, new_topic: null }],
      left_as_is: [{ finding_id: "g-2", title: "Keep the pair formula", reason: "a textbook fact" }],
    };
    const p = gardenPaths(cfg, batch.created);
    await mkdir(path.dirname(p.md), { recursive: true });
    await writeFile(p.json, JSON.stringify(batch));
    const md = renderGardenChecklist(batch, { toolkitRoot: root });
    expect(md).toContain(`paperformalizer garden --verify ${p.md}`);
    expect(md).toContain("Also reviewed and fine as they are (nothing to decide): Keep the pair formula — a textbook fact.");
    await writeFile(p.md, md);
    git(root, "init", "-q");
    git(root, "-c", "user.email=t@t", "-c", "user.name=t", "add", "-A");
    git(root, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "toolkit");
    // Every command passes; the axioms probe answers each `#print axioms` line with the standard three.
    const deps = {
      ...realVerifyDeps,
      run: async (cmd: string) => {
        if (!cmd.startsWith("lake env lean")) return { code: 0, log: "ok" };
        const probe = await readFile(cmd.slice("lake env lean ".length).replace(/^'|'$/g, ""), "utf8");
        const names = [...probe.matchAll(/^#print axioms (\S+)$/gm)].map((m) => m[1]!);
        return { code: 0, log: names.map((n) => `'${n}' depends on axioms: [propext, Classical.choice, Quot.sound]`).join("\n") };
      },
    };
    const run = () => verifyGarden({ toolkit: cfg, md: p.md, log: () => {}, deps, indexStep: null, toolsDir: "/tools", graphAfter: async () => null });

    await expect(run()).rejects.toThrow(/still pending/);
    await writeFile(p.md, md.replace("decision: pending", "decision: accept"));
    expect(parseGardenChecklist(await readFile(p.md, "utf8"), batch)).toEqual({ "g-1": { kind: "accept" } });
    await expect(run()).rejects.toThrow(/nothing in the toolkit's Lean changed/);
    await expect(verifyGarden({ toolkit: cfg, md: p.md, log: () => {}, deps, items: ["g-9"], indexStep: null, toolsDir: "/tools", graphAfter: async () => null })).rejects.toThrow(/not accepted on the checklist/);

    // The orchestrator's hand edit: the declaration into its topic namespace, the paper's reference with it.
    await writeFile(modPath, leanModule({ doc: mod, body: "namespace Toolkit.Foundations.Probability\n\n/-- Survives. -/\ntheorem cond_preimage (n : Nat) : n = n := rfl\n\nend Toolkit.Foundations.Probability" }));
    await writeFile(paper, leanModule({ imports: [mod], body: "namespace Papers.P\n\ntheorem thm (n : Nat) : n = n := Toolkit.Foundations.Probability.cond_preimage n\n\nend Papers.P" }));
    const ok = await run();
    expect(ok.problems).toEqual([]);
    expect(ok.ok).toBe(true);
    expect([...ok.renames]).toEqual([["IndepFun.cond_preimage", "Toolkit.Foundations.Probability.cond_preimage"]]);
    const ledger = JSON.parse(await readFile(cfg.ledgerPath, "utf8")) as { declarations: Array<{ name: string; renamed_from?: string }>; decisions: Array<{ kind: string; item?: string; applied?: boolean }> };
    expect(ledger.declarations[0]).toMatchObject({ name: "Toolkit.Foundations.Probability.cond_preimage", renamed_from: "IndepFun.cond_preimage" });
    expect(ledger.decisions.filter((x) => x.kind === "garden_decision").map((x) => [x.item, x.applied])).toEqual([["g-1", true]]);

    // A paper statement changed, and a file outside the toolkit's Lean: both refused; nothing recorded.
    await writeFile(paper, leanModule({ imports: [mod], body: "namespace Papers.P\n\ntheorem thm (n : Nat) (h : 0 < n) : n = n := Toolkit.Foundations.Probability.cond_preimage n\n\nend Papers.P" }));
    await writeFile(path.join(root, "lakefile.toml"), "# edited\n");
    const bad = await run();
    expect(bad.ok).toBe(false);
    expect(bad.problems.join("\n")).toMatch(/the statement of Papers\.P\.thm changed/);
    expect(bad.problems.join("\n")).toMatch(/lakefile\.toml changed .* not part of the toolkit's Lean/);
  });

  it("verify runs in the shared tree even in a workspace; the papers the edits reach must build, the others are reported", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "garden-verify-reach-"));
    tmp.push(root);
    const ws = await mkdtemp(path.join(os.tmpdir(), "garden-verify-ws-"));
    tmp.push(ws);
    const cfg = await writeSkeleton(root);
    const mod = "Toolkit.Foundations.Probability.Conditioning";
    const modPath = path.join(root, "Toolkit/Foundations/Probability/Conditioning.lean");
    await mkdir(path.dirname(modPath), { recursive: true });
    const tkText = (ns: string) => leanModule({ doc: mod, body: `namespace ${ns}\n\n/-- Survives. -/\ntheorem cond_preimage (n : Nat) : n = n := rfl\n\nend ${ns}` });
    await writeFile(modPath, tkText("IndepFun"));
    await writeFile(path.join(root, "Toolkit/Foundations.lean"), BARREL("Toolkit.Foundations", [mod]));
    await writeFile(path.join(root, "Toolkit.lean"), BARREL("Toolkit", ["Toolkit.Foundations"]));
    // P uses the module through the toolkit's barrel; Q uses nothing of it; R is a run in progress importing it
    const paperText = (name: string, imports: string[], ref: string | null) =>
      leanModule({ imports, body: `namespace Papers.${name}\n\ntheorem thm (n : Nat) : n = n := ${ref ? `${ref} n` : "rfl"}\n\nend Papers.${name}` });
    // S: in progress (a barrel, not in the papers' barrel), still naming the old name after the edit
    for (const [name, imports, ref] of [["P", ["Toolkit"], null], ["Q", [], null], ["R", [mod], "IndepFun.cond_preimage"], ["S", [mod], "IndepFun.cond_preimage"]] as const) {
      await mkdir(path.join(root, "Papers", name), { recursive: true });
      await writeFile(path.join(root, "Papers", name, "Main.lean"), paperText(name, [...imports], ref));
      await writeFile(path.join(root, "Papers", `${name}.lean`), BARREL(`Papers.${name}`, [`Papers.${name}.Main`]));
    }
    await writeFile(path.join(root, "Papers.lean"), BARREL("Papers", ["Papers.P", "Papers.Q"]));
    expect([...(await papersReached(cfg, [mod], []))].sort()).toEqual(["Papers.P", "Papers.R", "Papers.S"]);
    // the toolkit graph after the edits: a scan of the toolkit alone, by a fake lake on PATH
    await writeFile(path.join(root, "lakefile.toml"), 'name = "t"\n\n[[lean_lib]]\nname = "Toolkit"\n\n[[lean_exe]]\nname = "candidate_scan"\nroot = "CandidateScan"\n');
    await copyFile(path.join(toolkitTemplateDir(), "CandidateScan.lean"), path.join(root, "CandidateScan.lean"));
    const fixture = path.join(__dirname, "../fixtures/toolkit_graph/graph_scan.json");
    const fixtureScan = JSON.parse(await readFile(fixture, "utf8")) as GraphScan;
    await mkdir(path.join(root, "doc"), { recursive: true });
    await writeFile(path.join(root, "doc", "toolkit_graph.json"), JSON.stringify(buildToolkitGraph({ scan: fixtureScan, now: () => new Date("2026-10-01") })));
    const bin = path.join(ws, "bin");
    await mkdir(bin, { recursive: true });
    const lakeLog = path.join(ws, "lake.log");
    await writeFile(path.join(bin, "lake"), `#!/bin/sh\necho "$*" >> ${shq(lakeLog)}\nout=""; prev=""\nfor a in "$@"; do [ "$prev" = "--out" ] && out="$a"; prev="$a"; done\n[ -n "$out" ] && mkdir -p "$(dirname "$out")" && cp ${shq(fixture)} "$out"\nexit 0\n`);
    await chmod(path.join(bin, "lake"), 0o755);
    expect([...(await papersReached(cfg, [], ["Papers.Q.Main"]))]).toEqual(["Papers.Q"]);
    await writeFile(cfg.ledgerPath, JSON.stringify({ version: 1, declarations: [], decisions: [] }));
    const batch: GardenBatch = {
      created: "2026-10-02T00:00:00.000Z",
      findings: [{ id: "g-1", kind: "namespace", modules: ["Toolkit/Foundations/Probability/Conditioning.lean"], decls: ["IndepFun.cond_preimage"], detail: "outside" }],
      items: [{ finding_id: "g-1", title: "Name it in its topic", finding: "outside", reason: "consistent", recommendation: "accept", action: "rename",
        target_module: null, modules: [], parts: [], replacement: null, new_topic: null }],
    };
    const p = gardenPaths(cfg, batch.created);
    await mkdir(path.dirname(p.md), { recursive: true });
    const writeBatch = async (b: GardenBatch) => {
      await writeFile(p.json, JSON.stringify(b));
      await writeFile(p.md, renderGardenChecklist(b, { toolkitRoot: root }).replace("decision: pending", "decision: accept"));
    };
    await writeBatch(batch);
    git(root, "init", "-q");
    git(root, "-c", "user.email=t@t", "-c", "user.name=t", "add", "-A");
    git(root, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "toolkit");
    // the edit: the declaration into its topic namespace, R's reference with it
    await writeFile(modPath, tkText("Toolkit.Foundations.Probability"));
    await writeFile(path.join(root, "Papers", "R", "Main.lean"), paperText("R", [mod], "Toolkit.Foundations.Probability.cond_preimage"));

    // a workspace set: never used by verify
    await writeFile(path.join(ws, ".pf-toolkit"), `${root}\n`);
    const prior = process.env[LEAN_WS_ENV];
    process.env[LEAN_WS_ENV] = ws;
    try {
      expect(leanWorkspaceFor(root)).toBe(ws);
      let fail: string[] = [];
      const cmds: string[] = [];
      const probes: string[] = [];
      // the baseline workspace (the toolkit before the edits) and what a build there gives
      const bws = path.join(ws, "baseline");
      let baselineFails = true;
      let heldOff = false;
      let baselineWhy: string | null = null;
      let baselineAsked = 0;
      let removed = 0;
      const slugs: string[] = [];
      // the baseline workspace's pin: the toolkit and generation 4
      await mkdir(bws, { recursive: true });
      await writeFile(path.join(bws, ".pf-toolkit"), `${root}\n`);
      const pinGen = (gen: number) => writeFile(path.join(bws, ".pf-gen"), JSON.stringify({ gen }));
      await pinGen(4);
      const deps = {
        ...realVerifyDeps,
        baselineWorkspace: async (_c: unknown, _rev: string, slug: string) => {
          baselineAsked += 1;
          slugs.push(slug);
          return baselineWhy ? { why: baselineWhy } : { path: bws, gen: 4, remove: async () => { removed += 1; } };
        },
        run: async (cmd: string) => {
          // in the shared tree: no workspace for this chain, and cleared for every child
          expect(leanWorkspaceFor(root)).toBeNull();
          expect(leanWsChildEnv()[LEAN_WS_ENV]).toBe("");
          cmds.push(cmd);
          if (cmd.includes(`${LEAN_WS_ENV}=`)) return heldOff ? { code: 1, log: "PF_LAKE_SHIM_HELD_OFF" } : { code: baselineFails ? 1 : 0, log: "baseline" };
          if (fail.some((x) => cmd.split(" ").includes(x))) return { code: 1, log: "error" };
          if (!cmd.startsWith("lake env lean")) return { code: 0, log: "ok" };
          const probe = await readFile(cmd.slice("lake env lean ".length).replace(/^'|'$/g, ""), "utf8");
          probes.push(probe);
          const names = [...probe.matchAll(/^#print axioms (\S+)$/gm)].map((m) => m[1]!);
          return { code: 0, log: names.map((n) => `'${n}' depends on axioms: [propext, Classical.choice, Quot.sound]`).join("\n") };
        },
      };
      const run = () => verifyGarden({ toolkit: cfg, md: p.md, log: () => {}, deps, indexStep: null, toolsDir: "/tools", graphAfter: async () => null });

      const ok = await run();
      expect(ok.problems).toEqual([]);
      expect(cmds.filter((c) => c.startsWith("lake build"))).toEqual(["lake build Toolkit", "lake build Papers.P Papers.R Papers.S", "lake build Papers.Q"]);
      expect(ok.reported).toEqual([]);

      // a paper the edits do not reach fails: reported, not fatal
      fail = ["Papers.Q"];
      const q = await run();
      expect(q.ok).toBe(true);
      expect(q.reported.join("\n")).toMatch(/papers the edits do not reach .* do not all build/);

      // a paper the edits CHANGED that does not build: fatal outright, no baseline asked
      fail = ["Papers.R"];
      baselineAsked = 0;
      const r = await run();
      expect(r.ok).toBe(false);
      expect(r.problems.join("\n")).toMatch(/lake build papers the edits reach failed \(Papers\.R: changed by the edits and does not build\)/);
      expect(baselineAsked).toBe(0);

      // an unchanged paper the edits reach fails after them: built against the toolkit as it was
      fail = ["Papers.S"];
      baselineFails = true;
      const pre = await run();
      expect(pre.problems).toEqual([]);
      expect(pre.ok).toBe(true);
      expect(pre.reported.join("\n")).toMatch(/Papers\.S does not build, before the edits too \(generation 4\)/);
      // its own baseline workspace, removed when it ends
      expect(slugs.at(-1)).toMatch(new RegExp(`^garden-baseline-\\w+-${process.pid}$`));
      expect(removed).toBe(1);
      const baselineCmd = cmds.find((c) => c.includes(`${LEAN_WS_ENV}=`))!;
      expect(baselineCmd).toContain(`${LEAN_WS_ENV}=${shq(bws)}`);
      expect(baselineCmd).toContain(`${shq(path.join(LAKE_SHIM_DIR, "lake"))} build Papers.S;`);
      // it built before the edits: they broke it
      baselineFails = false;
      const broke = await run();
      expect(broke.ok).toBe(false);
      expect(broke.problems.join("\n")).toMatch(/Papers\.S: builds against the toolkit before the edits \(generation 4\) but not after/);
      // the shim would not build there (the toolkit in flux): cannot be told, fatal
      baselineFails = true;
      heldOff = true;
      expect((await run()).problems.join("\n")).toMatch(/Papers\.S: does not build, and its baseline build did not run to an end/);
      heldOff = false;
      // the workspace is not pinned to that generation (the shim could build elsewhere): cannot be told, fatal
      await pinGen(3);
      const unpinned = await run();
      expect(unpinned.ok).toBe(false);
      expect(unpinned.problems.join("\n")).toMatch(/Papers\.S: does not build, and whether it did before the edits cannot be told — .*\.pf-gen is not generation 4 \(generation 3\)/);
      await pinGen(4);
      await writeFile(path.join(bws, ".pf-toolkit"), "/elsewhere\n");
      expect((await run()).problems.join("\n")).toMatch(/\.pf-toolkit does not name/);
      await writeFile(path.join(bws, ".pf-toolkit"), `${root}\n`);
      // no generation is the toolkit at HEAD: cannot be told, fatal
      baselineWhy = "no published generation is the toolkit at HEAD";
      expect((await run()).problems.join("\n")).toMatch(/Papers\.S: does not build, and whether it did before the edits cannot be told — no published generation/);
      baselineWhy = null;

      // a reached paper directory without a barrel: its modules built like any paper's
      fail = [];
      await mkdir(path.join(root, "Papers", "T"), { recursive: true });
      await writeFile(path.join(root, "Papers", "T", "Main.lean"), paperText("T", [mod], "IndepFun.cond_preimage"));
      cmds.length = 0;
      expect((await run()).ok).toBe(true);
      expect(cmds).toContain("lake build Papers.P Papers.R Papers.S Papers.T.Main");
      await rm(path.join(root, "Papers", "T"), { recursive: true, force: true });

      // the health comparison without a given graph: a scan of the toolkit alone, nothing else built
      const PATH = process.env.PATH;
      process.env.PATH = `${bin}:${PATH}`;
      try {
        const logs: string[] = [];
        const h = await verifyGarden({ toolkit: cfg, md: p.md, log: (m) => logs.push(m), deps, indexStep: null, toolsDir: "/tools" });
        expect(h.ok).toBe(true);
        const lakeCalls = (await readFile(lakeLog, "utf8")).trim().split("\n");
        expect(lakeCalls.some((c) => /\bPapers\b/.test(c.replace(/--papers-prefix Papers/, "")))).toBe(false);
        expect(lakeCalls.at(-1)).toMatch(/exe candidate_scan .*--modules Toolkit --out /);
        expect(logs.join("\n")).not.toMatch(/health comparison is skipped/);
      } finally {
        process.env.PATH = PATH;
      }
    } finally {
      if (prior === undefined) delete process.env[LEAN_WS_ENV];
      else process.env[LEAN_WS_ENV] = prior;
    }
  });

  it("a baseline workspace must hold the toolkit's files exactly as at the commit checked against", async () => {
    const ws = await mkdtemp(path.join(os.tmpdir(), "garden-baseline-"));
    tmp.push(ws);
    await mkdir(path.join(ws, "Toolkit", "Foundations"), { recursive: true });
    await mkdir(path.join(ws, "Toolkit", "Staging"), { recursive: true });
    await writeFile(path.join(ws, "Toolkit", "Foundations", "A.lean"), "a");
    await writeFile(path.join(ws, "Toolkit", "Staging", "S.lean"), "staging is not compared");
    await writeFile(path.join(ws, "Toolkit.lean"), "barrel");
    const want = new Map([["Toolkit/Foundations/A.lean", "a"], ["Toolkit.lean", "barrel"]]);
    expect(await baselineDiffers(ws, "Toolkit", want)).toBeNull();
    expect(await baselineDiffers(ws, "Toolkit", new Map([...want, ["Toolkit.lean", "edited"]]))).toBe("Toolkit.lean differs");
    expect(await baselineDiffers(ws, "Toolkit", new Map([...want, ["lean-toolchain", "x"]]))).toBe("lean-toolchain is missing");
    await writeFile(path.join(ws, "Toolkit", "Foundations", "B.lean"), "b");
    expect(await baselineDiffers(ws, "Toolkit", want)).toBe("Toolkit/Foundations/B.lean is not in the toolkit at the baseline");
    // no generation published: cannot be told
    const root = await mkdtemp(path.join(os.tmpdir(), "garden-baseline-tk-"));
    tmp.push(root);
    const cfg = await writeSkeleton(root);
    expect(await realBaselineWorkspace(cfg, "HEAD", realVerifyDeps.git, "garden-baseline-x", () => {})).toEqual({ why: "no toolkit generation is published" });
  });
});
