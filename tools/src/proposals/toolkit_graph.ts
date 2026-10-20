// The toolkit dependency graph, `<toolkit>/doc/toolkit_graph.json`: DERIVED from the Lean (one
// `lake exe candidate_scan -- --graph` pass), never authored. Nodes are declarations — the
// toolkit's, the papers' (as consumers), and the base libraries' as leaves (only those a toolkit
// declaration uses; never expanded). One stored edge direction: `uses` (A → B: A's type or proof
// references B); "used by" is the reversal.
//
// Two tiers. A MAIN node is a result a textbook would state (a promoted main result, a toolkit
// declaration the owner put there, a paper's own theorem / lemma / definition); an AUXILIARY node
// is a helper that exists to prove main node(s), its `owners`. The MAIN VIEW — the default of every
// report — collapses each auxiliary into its owners and lifts the edges (main A uses main B when any
// declaration of A's group uses any of B's group). The measures read the main view; `view: "full"`
// keeps the auxiliaries.
//
// The measures are evidence for the owner: isolated results, duplicates, how much each paper
// reuses the toolkit, base attachment, module cohesion (split / merge suggestions), fan-in and
// staleness. They never edit the toolkit.
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import type { ToolkitConfig } from "../toolkit/config.js";
import { loadLedger } from "../toolkit/ledger.js";
import { type CandidateScan } from "./candidate_scan.js";

export type NodeLayer = "toolkit" | "paper" | "base";
export type NodeTier = "main" | "aux";

export interface GraphNode {
  id: string;
  layer: NodeLayer;
  kind: string;
  module: string;
  /** Toolkit: its division and topic (`<lib>.<Division>.<Topic>.…`). */
  division?: string;
  topic?: string;
  /** Paper: its module prefix (`Papers.<Pascal>`). */
  paper?: string;
  /** Toolkit and paper nodes. Base leaves have none. */
  tier?: NodeTier;
  /** Auxiliary: the main node(s) it exists to prove. */
  owners?: string[];
  /** sha1 of the whitespace-normalized statement with the node's own name removed. */
  statement_hash?: string;
  /** Toolkit: where it came from (the ledger), when recorded. */
  origin?: { kind: string; slug: string; date?: string };
}

export interface ToolkitGraph {
  version: 1;
  built_at: string;
  toolkit_prefix: string;
  papers_prefix: string;
  nodes: GraphNode[];
  /** `[from, to]`: `from` uses `to`. */
  edges: Array<[string, string]>;
}

export function statementHash(name: string, type: string): string {
  const leaf = name.slice(name.lastIndexOf(".") + 1);
  const norm = type.replace(new RegExp(`\\b${leaf.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\b`, "g"), "_").replace(/\s+/g, " ").trim();
  return createHash("sha1").update(norm).digest("hex");
}

export interface GraphInputs {
  scan: CandidateScan;
  /** Toolkit declarations' tier, owners and origin, from the ledger (`declarations[]`). */
  toolkitRecords?: ReadonlyMap<string, { tier?: NodeTier; owners?: string[]; origin?: { kind: string; slug: string }; date?: string }>;
  /** Paper declarations a paper statement maps to (its theorems, lemmas and definitions): main. */
  paperMain?: ReadonlySet<string>;
  now?: () => Date;
}

/**
 * Build the graph from a `--graph` scan. Tiers: a toolkit declaration takes its ledger tier (main
 * when unrecorded: the owner put it there); a paper declaration is main when a paper statement maps
 * to it; any other declaration of a toolkit or paper is auxiliary, owned by the main nodes of its
 * own layer (and paper) that reach it. An auxiliary no main node reaches is shown as main (it is
 * nobody's helper — the isolated measure reports it).
 */
export function buildToolkitGraph(inp: GraphInputs): ToolkitGraph {
  const { scan } = inp;
  const tk = scan.toolkit_prefix;
  const pp = scan.papers_prefix;
  const nodes = new Map<string, GraphNode>();
  const edges = new Set<string>();
  const paperOf = (module: string): string => module.split(".").slice(0, 2).join(".");
  for (const d of scan.declarations) {
    const layer: NodeLayer = d.module === tk || d.module.startsWith(`${tk}.`) ? "toolkit" : "paper";
    const segs = d.module.split(".");
    const rec = inp.toolkitRecords?.get(d.name);
    nodes.set(d.name, {
      id: d.name, layer, kind: d.kind, module: d.module,
      ...(layer === "toolkit" ? { division: segs[1] ?? "", topic: segs[2] ?? "" } : { paper: paperOf(d.module) }),
      statement_hash: statementHash(d.name, d.type),
      ...(layer === "toolkit" && rec?.origin ? { origin: { ...rec.origin, ...(rec.date ? { date: rec.date } : {}) } } : {}),
    });
  }
  for (const d of scan.declarations) {
    const from = nodes.get(d.name)!;
    for (const c of [...d.type_constants, ...d.body_constants]) {
      if (c.name === d.name) continue;
      if (c.class === "base") {
        // Base leaves only where a toolkit declaration attaches to the base libraries.
        if (from.layer !== "toolkit") continue;
        if (!nodes.has(c.name)) nodes.set(c.name, { id: c.name, layer: "base", kind: "base", module: c.module });
      } else if (!nodes.has(c.name)) continue;
      edges.add(`${d.name}\u0000${c.name}`);
    }
  }
  const edgeList = [...edges].map((e) => e.split("\u0000") as [string, string]);
  // Tiers. An unrecorded toolkit declaration is a helper when it is an instance or sits in a module
  // the ledger records promotions into; otherwise the owner put it there by hand (main).
  const recordedModules = new Set([...nodes.values()].filter((n) => n.layer === "toolkit" && inp.toolkitRecords?.has(n.id)).map((n) => n.module));
  for (const n of nodes.values()) {
    if (n.layer === "base") continue;
    if (n.layer === "toolkit") {
      const rec = inp.toolkitRecords?.get(n.id);
      n.tier = rec?.tier ?? (n.kind === "instance" || recordedModules.has(n.module) ? "aux" : "main");
      if (rec?.owners?.length) n.owners = [...rec.owners];
    } else {
      n.tier = inp.paperMain?.has(n.id) ? "main" : "aux";
    }
  }
  // Owners of auxiliaries without recorded ones: the main nodes of the same layer and paper reaching them.
  const out = adjacency(edgeList);
  for (const m of nodes.values()) {
    if (m.tier !== "main") continue;
    const seen = new Set<string>([m.id]);
    const stack = [...(out.get(m.id) ?? [])];
    while (stack.length) {
      const x = stack.pop()!;
      if (seen.has(x)) continue;
      seen.add(x);
      const n = nodes.get(x);
      if (!n || n.tier !== "aux" || n.layer !== m.layer || n.paper !== m.paper) continue;
      if (inp.toolkitRecords?.get(n.id)?.owners?.length) continue;
      n.owners = [...new Set([...(n.owners ?? []), m.id])].sort();
      stack.push(...(out.get(x) ?? []));
    }
  }
  for (const n of nodes.values()) if (n.tier === "aux" && !(n.owners?.length)) n.tier = "main";
  return {
    version: 1,
    built_at: (inp.now ?? (() => new Date()))().toISOString(),
    toolkit_prefix: tk,
    papers_prefix: pp,
    nodes: [...nodes.values()].sort((a, b) => a.id.localeCompare(b.id)),
    edges: edgeList.sort((a, b) => a[0].localeCompare(b[0]) || a[1].localeCompare(b[1])),
  };
}

function adjacency(edges: ReadonlyArray<readonly [string, string]>): Map<string, string[]> {
  const m = new Map<string, string[]>();
  for (const [a, b] of edges) {
    if (!m.has(a)) m.set(a, []);
    m.get(a)!.push(b);
  }
  return m;
}

/** The main view: each auxiliary collapsed into its owners, edges lifted between groups. */
export function mainView(g: ToolkitGraph): ToolkitGraph {
  const groupsOf = new Map<string, string[]>();
  for (const n of g.nodes) groupsOf.set(n.id, n.tier === "aux" ? (n.owners ?? [n.id]) : [n.id]);
  const edges = new Set<string>();
  for (const [a, b] of g.edges) {
    for (const ga of groupsOf.get(a) ?? [a]) {
      for (const gb of groupsOf.get(b) ?? [b]) if (ga !== gb) edges.add(`${ga}\u0000${gb}`);
    }
  }
  return {
    ...g,
    nodes: g.nodes.filter((n) => n.tier !== "aux"),
    edges: [...edges].map((e) => e.split("\u0000") as [string, string]).sort((a, b) => a[0].localeCompare(b[0]) || a[1].localeCompare(b[1])),
  };
}

export interface ToolkitHealth {
  view: "main" | "full";
  toolkit_nodes: number;
  /** Toolkit nodes no other node (paper or toolkit) uses. */
  isolated: string[];
  /** Groups of toolkit nodes with the same normalized statement. */
  duplicates: string[][];
  /** Per paper: its nodes, and how many reach a toolkit node. */
  papers: Array<{ paper: string; nodes: number; reaching_toolkit: number }>;
  /** Share of papers using any toolkit node. */
  reuse_rate: number;
  /** Per toolkit node: base leaves and toolkit nodes it uses; `shape` = what its edges suggest. */
  attachment: Array<{ id: string; division: string; base: number; toolkit: number; shape: "foundation" | "trick" }>;
  /** Modules whose nodes fall apart into several unconnected parts (a split suggestion). */
  split_suggestions: Array<{ module: string; components: string[][] }>;
  /** Module pairs of one topic with dense cross-use (a merge suggestion). */
  merge_suggestions: Array<{ modules: [string, string]; cross_edges: number }>;
  /** Toolkit nodes used by the most papers. */
  fan_in: Array<{ id: string; papers: number }>;
  /** Toolkit nodes no paper uses, recorded long enough ago to have been needed. */
  stale: string[];
}

const STALE_DAYS = 180;

/** The measures, on the main view unless `view: "full"`. */
export function toolkitHealth(full: ToolkitGraph, opts: { view?: "main" | "full"; now?: Date } = {}): ToolkitHealth {
  const view = opts.view ?? "main";
  const g = view === "main" ? mainView(full) : full;
  const byId = new Map(g.nodes.map((n) => [n.id, n] as const));
  const toolkit = g.nodes.filter((n) => n.layer === "toolkit");
  const users = new Map<string, string[]>();
  for (const [a, b] of g.edges) {
    if (!users.has(b)) users.set(b, []);
    users.get(b)!.push(a);
  }
  const out = adjacency(g.edges);
  const isolated = toolkit.filter((n) => (users.get(n.id) ?? []).every((u) => u === n.id)).map((n) => n.id);
  const byHash = new Map<string, string[]>();
  for (const n of toolkit) if (n.statement_hash) byHash.set(n.statement_hash, [...(byHash.get(n.statement_hash) ?? []), n.id]);
  const duplicates = [...byHash.values()].filter((xs) => xs.length > 1);
  const reachesToolkit = (id: string): boolean => {
    const seen = new Set<string>();
    const stack = [id];
    while (stack.length) {
      const x = stack.pop()!;
      if (seen.has(x)) continue;
      seen.add(x);
      for (const y of out.get(x) ?? []) {
        if (byId.get(y)?.layer === "toolkit") return true;
        if (byId.get(y)?.layer === "paper") stack.push(y);
      }
    }
    return false;
  };
  const paperIds = [...new Set(g.nodes.filter((n) => n.layer === "paper").map((n) => n.paper!))].sort();
  const papers = paperIds.map((p) => {
    const ns = g.nodes.filter((n) => n.paper === p);
    return { paper: p, nodes: ns.length, reaching_toolkit: ns.filter((n) => reachesToolkit(n.id)).length };
  });
  const attachment = toolkit.map((n) => {
    const deps = (out.get(n.id) ?? []).map((d) => byId.get(d)).filter((d): d is GraphNode => !!d);
    const base = deps.filter((d) => d.layer === "base").length;
    const tk = deps.filter((d) => d.layer === "toolkit").length;
    return { id: n.id, division: n.division ?? "", base, toolkit: tk, shape: (tk === 0 ? "foundation" : "trick") as "foundation" | "trick" };
  });
  const split_suggestions: ToolkitHealth["split_suggestions"] = [];
  for (const mod of [...new Set(toolkit.map((n) => n.module))].sort()) {
    const ids = toolkit.filter((n) => n.module === mod).map((n) => n.id);
    const comps = components(ids, g.edges);
    if (comps.length > 1 && ids.length > 2) split_suggestions.push({ module: mod, components: comps });
  }
  const merge_suggestions: ToolkitHealth["merge_suggestions"] = [];
  const modsByTopic = new Map<string, string[]>();
  for (const n of toolkit) {
    const key = `${n.division}.${n.topic}`;
    const mods = modsByTopic.get(key) ?? [];
    if (!mods.includes(n.module)) mods.push(n.module);
    modsByTopic.set(key, mods);
  }
  for (const mods of modsByTopic.values()) {
    for (let i = 0; i < mods.length; i += 1) {
      for (let j = i + 1; j < mods.length; j += 1) {
        const a = mods[i]!, b = mods[j]!;
        const sizeA = toolkit.filter((n) => n.module === a).length;
        const sizeB = toolkit.filter((n) => n.module === b).length;
        const cross = g.edges.filter(([x, y]) => (byId.get(x)?.module === a && byId.get(y)?.module === b) || (byId.get(x)?.module === b && byId.get(y)?.module === a)).length;
        if (cross > 0 && cross >= Math.min(sizeA, sizeB)) merge_suggestions.push({ modules: [a, b], cross_edges: cross });
      }
    }
  }
  const fan_in = toolkit
    .map((n) => ({ id: n.id, papers: new Set((users.get(n.id) ?? []).map((u) => byId.get(u)?.paper).filter(Boolean)).size }))
    .filter((x) => x.papers > 0)
    .sort((a, b) => b.papers - a.papers || a.id.localeCompare(b.id))
    .slice(0, 10);
  const now = opts.now ?? new Date();
  const stale = toolkit.filter((n) => {
    const usedByPaper = (users.get(n.id) ?? []).some((u) => byId.get(u)?.layer === "paper");
    const date = n.origin?.date ? new Date(n.origin.date) : null;
    return !usedByPaper && date !== null && (now.getTime() - date.getTime()) / 86_400_000 > STALE_DAYS;
  }).map((n) => n.id);
  return {
    view,
    toolkit_nodes: toolkit.length,
    isolated,
    duplicates,
    papers,
    reuse_rate: paperIds.length ? papers.filter((p) => p.reaching_toolkit > 0).length / paperIds.length : 0,
    attachment,
    split_suggestions,
    merge_suggestions,
    fan_in,
    stale,
  };
}

/** Weakly connected components of `ids` under the edges among them. */
function components(ids: readonly string[], edges: ReadonlyArray<readonly [string, string]>): string[][] {
  const inSet = new Set(ids);
  const parent = new Map(ids.map((i) => [i, i] as const));
  const find = (x: string): string => (parent.get(x) === x ? x : (parent.set(x, find(parent.get(x)!)), parent.get(x)!));
  for (const [a, b] of edges) if (inSet.has(a) && inSet.has(b)) parent.set(find(a), find(b));
  const groups = new Map<string, string[]>();
  for (const i of ids) groups.set(find(i), [...(groups.get(find(i)) ?? []), i]);
  return [...groups.values()].map((g) => g.sort()).sort((a, b) => a[0]!.localeCompare(b[0]!));
}

const local = (n: string): string => n.slice(n.lastIndexOf(".") + 1);

/** The health report in words (the checklist's "Your toolkit now", `toolkit-health`). */
export function healthSummary(h: ToolkitHealth): string {
  const lines: string[] = [];
  lines.push(`- ${h.toolkit_nodes} result(s) in the toolkit${h.view === "main" ? " (main results; helpers counted with them)" : " (helpers included)"}.`);
  if (h.papers.length) {
    const using = h.papers.filter((p) => p.reaching_toolkit > 0).length;
    lines.push(`- ${using} of your ${h.papers.length} verified paper(s) use the toolkit (${Math.round(h.reuse_rate * 100)}%).`);
  }
  if (h.isolated.length) lines.push(`- Used by nothing yet: ${h.isolated.map(local).join(", ")}.`);
  if (h.duplicates.length) lines.push(`- Stated twice: ${h.duplicates.map((g) => g.map(local).join(" = ")).join("; ")}.`);
  if (h.fan_in.length) lines.push(`- Most reused: ${h.fan_in.slice(0, 5).map((f) => `${local(f.id)} (${f.papers} paper${f.papers === 1 ? "" : "s"})`).join(", ")}.`);
  for (const s of h.split_suggestions) lines.push(`- Gardening: ${s.module} holds ${s.components.length} unrelated groups of results — consider splitting it.`);
  for (const m of h.merge_suggestions) lines.push(`- Gardening: ${m.modules[0]} and ${m.modules[1]} use each other heavily — consider merging them.`);
  const misplaced = h.attachment.filter((a) => (a.division === "Foundations" && a.shape === "trick"));
  if (misplaced.length) lines.push(`- Gardening: ${misplaced.map((a) => local(a.id)).join(", ")} in Foundations build on other toolkit results, as Tricks usually do.`);
  if (h.stale.length) lines.push(`- Not used by any paper for over ${STALE_DAYS} days: ${h.stale.map(local).join(", ")}.`);
  return lines.join("\n");
}

/** Where a candidate group (a main result and what moves with it) attaches, in words. */
export function attachNote(g: ToolkitGraph, group: readonly string[]): string {
  const { byId, out } = attachIndex(g);
  const members = new Set(group);
  const uses = new Set<string>();
  for (const a of group) {
    for (const b of out.get(a) ?? []) {
      if (members.has(b)) continue;
      const t = byId.get(b);
      if (t?.layer !== "toolkit") continue;
      for (const owner of t.tier === "aux" ? (t.owners ?? [b]) : [b]) uses.add(owner);
    }
  }
  if (uses.size === 0) return "it uses no result of your toolkit yet — it would start a new topic or sit beside related results.";
  const mods = [...new Set([...uses].map((u) => byId.get(u)?.module).filter(Boolean))];
  return `it builds on your toolkit's ${[...uses].map(local).join(", ")} (in ${mods.join(", ")}), so that topic is its natural home.`;
}

/** A graph's nodes by id and its edges by source, built once per graph: `attachNote` is asked for
 *  every candidate of a paper over a graph of tens of thousands of edges. */
const attachIndexes = new WeakMap<ToolkitGraph, { byId: Map<string, GraphNode>; out: Map<string, string[]> }>();
function attachIndex(g: ToolkitGraph): { byId: Map<string, GraphNode>; out: Map<string, string[]> } {
  let idx = attachIndexes.get(g);
  if (!idx) {
    const out = new Map<string, string[]>();
    for (const [a, b] of g.edges) out.set(a, [...(out.get(a) ?? []), b]);
    idx = { byId: new Map(g.nodes.map((n) => [n.id, n] as const)), out };
    attachIndexes.set(g, idx);
  }
  return idx;
}

/** What a promotion made worse, in words (empty = nothing): compared on the main view. */
export function healthRegressions(before: ToolkitHealth, after: ToolkitHealth, moved: readonly string[]): string[] {
  const out: string[] = [];
  const movedSet = new Set(moved);
  const newIsolated = after.isolated.filter((x) => !before.isolated.includes(x) && movedSet.has(x));
  if (newIsolated.length) out.push(`now used by nothing: ${newIsolated.map(local).join(", ")}`);
  const beforeSplit = new Map(before.split_suggestions.map((s) => [s.module, s.components.length] as const));
  for (const s of after.split_suggestions) {
    if (s.components.length > (beforeSplit.get(s.module) ?? 1)) out.push(`${s.module} now falls apart into ${s.components.length} unrelated groups`);
  }
  const dupBefore = new Set(before.duplicates.flat());
  const newDup = after.duplicates.filter((gr) => gr.some((x) => !dupBefore.has(x)));
  if (newDup.length) out.push(`stated twice: ${newDup.map((gr) => gr.map(local).join(" = ")).join("; ")}`);
  return out;
}

// ─── IO ────────────────────────────────────────────────────────────────────

export function toolkitGraphPath(cfg: ToolkitConfig): string {
  return path.join(cfg.toolkitRoot, "doc", "toolkit_graph.json");
}

/** Ledger declarations as graph records (tier, owners, origin, date). */
export async function toolkitRecords(cfg: ToolkitConfig): Promise<NonNullable<GraphInputs["toolkitRecords"]>> {
  const ledger = await loadLedger(cfg.ledgerPath);
  return new Map(ledger.declarations.map((d) => {
    const x = d as typeof d & { tier?: NodeTier; owners?: string[] };
    return [d.name, {
      ...(x.tier ? { tier: x.tier } : {}),
      ...(x.owners ? { owners: x.owners } : {}),
      origin: { kind: d.origin.kind, slug: d.origin.slug },
      date: d.date,
    }] as const;
  }));
}

/** Paper declarations a paper statement maps to: the from-note nodes of every run's formalization
 *  graph (`runs/<slug>/graph.json`). */
export async function paperMainDecls(cfg: ToolkitConfig): Promise<Set<string>> {
  const out = new Set<string>();
  for (const e of await readdir(cfg.runsDir, { withFileTypes: true }).catch(() => [])) {
    if (!e.isDirectory()) continue;
    const f = path.join(cfg.runsDir, e.name, "graph.json");
    if (!existsSync(f)) continue;
    try {
      const g = JSON.parse(await readFile(f, "utf8")) as { nodes?: Array<{ provenance?: string; lean?: { decl_name?: string | null } }> };
      for (const n of g.nodes ?? []) if (n.provenance === "from-note" && n.lean?.decl_name) out.add(n.lean.decl_name);
    } catch {
      // An unreadable run graph contributes no main nodes.
    }
  }
  return out;
}

/**
 * Re-derive `doc/toolkit_graph.json` from the Lean (one `candidate_scan --graph` pass, or a scan
 * given by a test) and the ledger's tiers. Returns the graph written.
 */
export async function refreshToolkitGraph(args: {
  toolkit: ToolkitConfig;
  log: (m: string) => void;
  scan?: () => Promise<CandidateScan>;
  now?: () => Date;
}): Promise<ToolkitGraph> {
  const { runGraphScan } = await import("./candidate_scan.js");
  const scan = args.scan ? await args.scan() : await runGraphScan({ toolkit: args.toolkit, log: args.log });
  const graph = buildToolkitGraph({
    scan,
    toolkitRecords: await toolkitRecords(args.toolkit),
    paperMain: await paperMainDecls(args.toolkit),
    ...(args.now ? { now: args.now } : {}),
  });
  const { writeJsonAtomic } = await import("../shared/json_atomic.js");
  await writeJsonAtomic(toolkitGraphPath(args.toolkit), graph);
  const count = (layer: NodeLayer) => graph.nodes.filter((n) => n.layer === layer).length;
  args.log(`toolkit graph: ${count("toolkit")} toolkit and ${count("paper")} paper declaration(s), ${graph.edges.length} edge(s) → ${toolkitGraphPath(args.toolkit)}`);
  return graph;
}

/** The graph on file, or null. */
export async function readToolkitGraph(cfg: ToolkitConfig): Promise<ToolkitGraph | null> {
  const f = toolkitGraphPath(cfg);
  if (!existsSync(f)) return null;
  return JSON.parse(await readFile(f, "utf8")) as ToolkitGraph;
}
