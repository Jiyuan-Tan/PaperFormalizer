// Gardening: findings from the toolkit graph, what the gardener reads, the owner's list, and the
// verification of the items the orchestrator carried out by hand.
import { spawnSync } from "node:child_process";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { appendReuseHistory, gardenerSources, gardenerViolations, gardenFindings, gardenPaths, parseGardenChecklist, readReuseHistory, renderGardenChecklist, runGardenRound, settledFindings, type GardenBatch, type GardenFinding } from "../../src/proposals/garden.js";
import { realVerifyDeps, verifyGarden } from "../../src/proposals/garden_verify.js";
import { sha256 } from "../../src/proposals/gate.js";
import type { ToolkitGraph, ToolkitHealth } from "../../src/proposals/toolkit_graph.js";
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
    expect(md).toContain(`theoremchecker garden --verify ${p.md}`);
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
});
