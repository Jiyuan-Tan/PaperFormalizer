// Gardening: keeping the personal toolkit structured as it grows.
//
// The toolkit graph's health (main view) yields mechanical FINDINGS — a module holding unrelated
// groups (split), two modules of a topic using each other heavily (merge), a result nothing uses,
// one stated twice, one a base library now states (after a Mathlib pin bump), a module outside the
// topic tree, a result whose dependencies sit in the other division. Only when there are findings,
// the GARDENER (one Claude call) turns them into a short list in plain words, each with an
// action and a recommendation, saved as `<toolkit>/doc/proposals/garden-<stamp>.md` (with its batch
// `.json` beside it). The gardener reads the full source of every toolkit module changed since the
// last list and of every module a finding names; the rest it sees as the one-line main view. The
// orchestrator decides each item — one that retires or removes a result goes to the owner (the
// toolkit would no longer hold it) — and carries out each ACCEPTED item by editing the Lean by
// hand (the toolkit committed first), and `leansmith garden --verify <file>` (`garden_verify.ts`)
// checks the edits against the committed toolkit and records them in the ledger. Nothing is ever
// changed without a decision on its item.
//
// The toolkit's reuse history (`doc/toolkit_reuse_history.jsonl`) gains one line per verified paper
// (how much of it reached the toolkit), so `toolkit-health` can show whether reuse is growing.
import { existsSync } from "node:fs";
import { mkdir, readdir, readFile } from "node:fs/promises";
import path from "node:path";
import { indexSourcesFromToolkit } from "../library/sources.js";
import { MODELS } from "../models.js";
import { claudeRoleModel } from "../claude_roles.js";
import { writeJsonAtomic, writeTextAtomic } from "../shared/json_atomic.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { leanImports } from "../toolkit/lean_source.js";
import { loadLedger } from "../toolkit/ledger.js";
import { namesOutsideTopic, topicNamespace, umbrellaImports } from "../toolkit/namespaces.js";
import { effectiveTaxonomy, ensureTaxonomy, newTopicProblem, taxonomyPromptText, topicOfModulePath, type Taxonomy } from "../toolkit/taxonomy.js";
import type { ClaudeRunInput } from "../workers/claude.js";
import type { CandidateScan } from "./candidate_scan.js";
import { parseDecisionBlock, type ChecklistDecision } from "./checklist.js";
import { askJson, claudeAsker, listToolkitModules, readProposalPrompt, recordPrompt, section, TEX_RE, type TokenLedger } from "./curator.js";
import { sha256 } from "./gate.js";
import { normalizeType } from "./statements.js";
import { mainView, toolkitHealth, type ToolkitGraph, type ToolkitHealth } from "./toolkit_graph.js";
import type { ReuseReport } from "./reuse.js";
import type { NewTopic } from "./schema.js";

// ─── reuse history ─────────────────────────────────────────────────────────

export function reuseHistoryPath(cfg: Pick<ToolkitConfig, "toolkitRoot">): string {
  return path.join(cfg.toolkitRoot, "doc", "toolkit_reuse_history.jsonl");
}

export interface ReuseHistoryLine {
  at: string;
  slug: string;
  /** Toolkit declarations the paper's proofs used, and its obligations touching the toolkit. */
  toolkit_decls_used: number | null;
  obligations_touching_toolkit: number | null;
  paper_obligations: number | null;
  /** The toolkit then: main results, and the share of verified papers reaching it. */
  toolkit_main_results: number;
  reuse_rate: number;
}

/** Record this paper's line: one per paper, so a round B run again replaces the paper's earlier line. */
export async function appendReuseHistory(cfg: Pick<ToolkitConfig, "toolkitRoot">, x: { slug: string; at: string; reuse: ReuseReport | null; health: ToolkitHealth }): Promise<void> {
  const ok = x.reuse && !x.reuse.error;
  const line: ReuseHistoryLine = {
    at: x.at, slug: x.slug,
    toolkit_decls_used: ok ? x.reuse!.toolkit_decls_used.length : null,
    obligations_touching_toolkit: ok ? x.reuse!.obligations_touching_toolkit : null,
    paper_obligations: ok ? x.reuse!.paper_obligations : null,
    toolkit_main_results: x.health.toolkit_nodes,
    reuse_rate: Math.round(x.health.reuse_rate * 1000) / 1000,
  };
  const kept = (await readReuseHistory(cfg)).filter((l) => l.slug !== x.slug);
  await mkdir(path.dirname(reuseHistoryPath(cfg)), { recursive: true });
  await writeTextAtomic(reuseHistoryPath(cfg), [...kept, line].map((l) => JSON.stringify(l)).join("\n") + "\n");
}

export async function readReuseHistory(cfg: Pick<ToolkitConfig, "toolkitRoot">): Promise<ReuseHistoryLine[]> {
  if (!existsSync(reuseHistoryPath(cfg))) return [];
  return (await readFile(reuseHistoryPath(cfg), "utf8")).split("\n").filter((l) => l.trim()).map((l) => JSON.parse(l) as ReuseHistoryLine);
}

/** The reuse trend in words (last `n` papers). */
export function reuseTrendText(lines: readonly ReuseHistoryLine[], n = 8): string {
  if (lines.length === 0) return "- Reuse history: no verified paper recorded yet.";
  const last = lines.slice(-n);
  const rows = last.map((l) => `  - ${l.at.slice(0, 10)} ${l.slug}: ${l.toolkit_decls_used === null ? "not measured" : `${l.toolkit_decls_used} toolkit declaration(s) used, ${l.obligations_touching_toolkit} of ${l.paper_obligations} obligation(s) touch the toolkit`}; toolkit then ${l.toolkit_main_results} result(s), ${Math.round(l.reuse_rate * 100)}% of papers reaching it`);
  return [`- Reuse history (last ${last.length} paper(s)):`, ...rows].join("\n");
}

// ─── findings ──────────────────────────────────────────────────────────────

export type GardenFindingKind =
  | "split" | "merge" | "unused" | "stale" | "duplicate" | "duplicate_of_base" | "outside_topic_tree"
  | "layering" | "namespace" | "umbrella_import" | "direction"
  /** Raised by the gardener itself from the main view (wrong topic, two forms of one fact). */
  | "judgement";

export interface GardenFinding {
  id: string;
  kind: GardenFindingKind;
  /** Module paths (`<lib>/…/<File>.lean`) concerned. */
  modules: string[];
  /** Declarations concerned (main results). */
  decls: string[];
  /** What the graph shows, in words. */
  detail: string;
  /** `split`: the unrelated groups of main results. */
  components?: string[][];
  /** `duplicate_of_base` / `duplicate`: the declaration already stating it. */
  existing?: string;
  /** `direction`: the declarations of the module that more basic topics' modules use (any tier),
   *  closed under what they use inside the module. */
  shared?: string[];
  /** `direction`: the most basic module using them — where they should go (extended). */
  target?: string;
}

/** How basic a top-level topic is: a module may build on its own level and lower ones. A module
 *  using one of a more applied topic (Counting on Design) has its shared definitions in the wrong
 *  place. Unlisted topics are not ranked. */
const TOPIC_LEVEL: Readonly<Record<string, number>> = {
  Order: 0, Algebra: 0, Combinatorics: 0,
  LinearAlgebra: 1, Topology: 1,
  Analysis: 2, MeasureTheory: 2,
  Probability: 3,
  Statistics: 4, Design: 4, Optimization: 4,
};

export function moduleRel(module: string): string {
  return `${module.split(".").join("/")}.lean`;
}
export function moduleOfRel(rel: string): string {
  return rel.replace(/\.lean$/, "").split("/").join(".");
}

/** Toolkit declarations a base library already states (the same normalized statement in an indexed
 *  base library): flagged after a pin bump, when the base gains what the toolkit proved. */
export async function baseDuplicates(cfg: ToolkitConfig, scan: Pick<CandidateScan, "declarations"> | null): Promise<Map<string, string>> {
  const out = new Map<string, string>();
  if (!scan) return out;
  const mine = scan.declarations.filter((d) => d.module === cfg.lib || d.module.startsWith(`${cfg.lib}.`));
  if (mine.length === 0) return out;
  const want = new Map(mine.map((d) => [normalizeType(d.type), d.name] as const));
  for (const src of indexSourcesFromToolkit(cfg)) {
    if (path.resolve(src.indexPath) === path.resolve(cfg.indexPath)) continue;
    const idx = JSON.parse(await readFile(src.indexPath, "utf8")) as { entries?: Array<{ name?: string; statement?: string }> };
    for (const e of idx.entries ?? []) {
      if (!e.name || !e.statement) continue;
      const hit = want.get(normalizeType(e.statement));
      if (hit && !out.has(hit)) out.set(hit, e.name);
    }
  }
  return out;
}

/** The mechanical findings of the toolkit's graph (main view), its topic tree and its base duplicates. */
export function gardenFindings(args: {
  cfg: Pick<ToolkitConfig, "lib" | "divisions">;
  graph: ToolkitGraph;
  health?: ToolkitHealth;
  taxonomy: Taxonomy | null;
  baseDups?: ReadonlyMap<string, string>;
  /** Toolkit division modules (dotted) → their text: namespace, umbrella-import and direction findings. */
  moduleTexts?: ReadonlyMap<string, string>;
}): GardenFinding[] {
  const { cfg, graph } = args;
  const h = args.health ?? toolkitHealth(graph);
  const byId = new Map(graph.nodes.map((n) => [n.id, n] as const));
  const relOf = (id: string) => moduleRel(byId.get(id)?.module ?? id);
  const local = (id: string) => id.slice(id.lastIndexOf(".") + 1);
  const out: Omit<GardenFinding, "id">[] = [];
  for (const s of h.split_suggestions) {
    out.push({ kind: "split", modules: [moduleRel(s.module)], decls: s.components.flat(), components: s.components,
      detail: `${moduleRel(s.module)} holds ${s.components.length} groups of results that never use each other: ${s.components.map((c) => c.map(local).join(", ")).join(" | ")}` });
  }
  for (const m of h.merge_suggestions) {
    out.push({ kind: "merge", modules: m.modules.map(moduleRel), decls: [],
      detail: `${moduleRel(m.modules[0])} and ${moduleRel(m.modules[1])}, in one topic, use each other ${m.cross_edges} time(s)` });
  }
  const dupOfBase = args.baseDups ?? new Map<string, string>();
  for (const [decl, existing] of dupOfBase) {
    out.push({ kind: "duplicate_of_base", modules: [relOf(decl)], decls: [decl], existing, detail: `${local(decl)} states what ${existing} (a base library) already states` });
  }
  for (const g of h.duplicates) {
    out.push({ kind: "duplicate", modules: [...new Set(g.map(relOf))], decls: g, existing: g[0], detail: `the same statement is in the toolkit ${g.length} times: ${g.map(local).join(", ")}` });
  }
  const stale = new Set(h.stale);
  for (const id of h.isolated.filter((x) => !stale.has(x) && !dupOfBase.has(x))) {
    out.push({ kind: "unused", modules: [relOf(id)], decls: [id], detail: `${local(id)} is used by no paper and no other toolkit result yet` });
  }
  for (const id of h.stale.filter((x) => !dupOfBase.has(x))) {
    out.push({ kind: "stale", modules: [relOf(id)], decls: [id], detail: `${local(id)} has not been used by any paper for a long time` });
  }
  if (args.taxonomy) {
    const topics = new Set(args.taxonomy.topics.map((t) => t.path));
    for (const mod of [...new Set(graph.nodes.filter((n) => n.layer === "toolkit").map((n) => n.module))].sort()) {
      const topic = topicOfModulePath(moduleRel(mod), cfg);
      if (topic === null || !topics.has(topic)) {
        out.push({ kind: "outside_topic_tree", modules: [moduleRel(mod)], decls: [], detail: `${moduleRel(mod)} is not under a topic of the tree (${topic ?? "no topic directory"})` });
      }
    }
  }
  // Layering: a Foundations declaration may use any base library and other Foundations results, but
  // never a Tricks one.
  const mainOf = (id: string): string => {
    const n = byId.get(id);
    return n?.tier === "aux" && n.owners?.length ? n.owners[0]! : id;
  };
  const layered = new Map<string, Set<string>>();
  for (const [a, b] of graph.edges) {
    const na = byId.get(a);
    const nb = byId.get(b);
    if (na?.layer !== "toolkit" || nb?.layer !== "toolkit" || na.division !== "Foundations" || nb.division !== "Tricks") continue;
    layered.set(mainOf(a), new Set([...(layered.get(mainOf(a)) ?? []), mainOf(b)]));
  }
  for (const [a, bs] of layered) {
    out.push({ kind: "layering", modules: [relOf(a)], decls: [a], detail: `${local(a)} is in Foundations but uses Tricks results (${[...bs].map(local).join(", ")})` });
  }
  // The toolkit's conventions (`toolkit/namespaces.ts`), from the module texts.
  const texts = args.moduleTexts ?? new Map<string, string>();
  const mains = (module: string) => graph.nodes.filter((n) => n.module === module && n.layer === "toolkit" && n.tier !== "aux").map((n) => n.id);
  for (const [module, text] of [...texts].sort()) {
    const outside = namesOutsideTopic(module, text);
    if (outside.length) {
      out.push({ kind: "namespace", modules: [moduleRel(module)], decls: outside.filter((n) => byId.get(n)?.tier !== "aux"),
        detail: `${moduleRel(module)} declares ${outside.map(local).join(", ")} outside its topic namespace ${topicNamespace(module)}` });
    }
    const umbrella = umbrellaImports(text);
    if (umbrella.length) {
      out.push({ kind: "umbrella_import", modules: [moduleRel(module)], decls: [], detail: `${moduleRel(module)} imports the whole of ${umbrella.join(", ")} instead of the modules it uses` });
    }
  }
  // Direction: modules building on a module of a more applied topic (its shared definitions belong
  // in the more basic topic). ONE finding per applied module, whatever builds on it: the shared
  // declarations (closed under what they use inside that module, so what moves carries what it
  // needs) and, as the natural destination, the most basic module building on it — extended, not a
  // new module beside it.
  const topTopic = (module: string) => module.split(".")[2] ?? "";
  const dependents = new Map<string, string[]>();
  for (const [a, text] of [...texts].sort()) {
    for (const imp of leanImports(text)) {
      const b = imp.module;
      if (!texts.has(b)) continue;
      const la = TOPIC_LEVEL[topTopic(a)];
      const lb = TOPIC_LEVEL[topTopic(b)];
      if (la === undefined || lb === undefined || lb <= la) continue;
      dependents.set(b, [...(dependents.get(b) ?? []), a]);
    }
  }
  for (const [b, as] of [...dependents].sort()) {
    const inB = (id: string) => byId.get(id)?.module === b;
    const shared = new Set(graph.edges.filter(([x, y]) => as.includes(byId.get(x)?.module ?? "") && inB(y)).map(([, y]) => y));
    for (let grew = true; grew;) {
      grew = false;
      for (const [x, y] of graph.edges) if (shared.has(x) && inB(y) && !shared.has(y)) { shared.add(y); grew = true; }
    }
    const target = [...as].sort((x, y) => (TOPIC_LEVEL[topTopic(x)]! - TOPIC_LEVEL[topTopic(y)]!) || x.localeCompare(y))[0]!;
    const sh = [...shared].sort();
    out.push({ kind: "direction", modules: [moduleRel(b), ...as.map(moduleRel)], decls: mains(b), shared: sh, target: moduleRel(target),
      detail: `${as.map((a) => `${moduleRel(a)} (${topTopic(a)})`).join(" and ")} build${as.length === 1 ? "s" : ""} on ${moduleRel(b)} (${topTopic(b)}), a more applied topic` +
        `${sh.length ? `; the declarations they need from it: ${sh.map(local).join(", ")} — their natural home is ${moduleRel(target)}, which already builds on them` : ""}` });
  }
  return out.map((f, i) => ({ ...f, id: `g-${i + 1}` }));
}

// ─── the gardener ──────────────────────────────────────────────────────────

export const GARDEN_ACTIONS = ["keep", "relocate", "merge", "split", "retire", "remove", "rename", "trim_imports", "cross_reference"] as const;
export type GardenAction = (typeof GARDEN_ACTIONS)[number];

export interface GardenItem {
  finding_id: string;
  title: string;
  finding: string;
  reason: string;
  recommendation: "accept" | "decline";
  action: GardenAction;
  /** relocate: the new path; merge: the kept module's path. */
  target_module: string | null;
  /** merge: [kept, folded]. */
  modules: string[];
  /** split: the new modules and the declarations each receives. */
  parts: Array<{ module: string; decls: string[] }>;
  /** retire: the declaration already stating it. */
  replacement: string | null;
  new_topic: NewTopic | null;
}

/** An item the gardener raises itself from the main view (wrong topic, two forms of one fact). */
export interface GardenExtra extends Omit<GardenItem, "finding_id"> {
  /** The main results concerned. */
  decls: string[];
}

const STR = { type: "string" } as const;
const ITEM_PROPS = {
  title: STR, finding: STR, reason: STR,
  recommendation: { type: "string", enum: ["accept", "decline"] },
  action: { type: "string", enum: [...GARDEN_ACTIONS] },
  target_module: { type: ["string", "null"] },
  modules: { type: "array", items: STR },
  parts: {
    type: "array",
    items: { type: "object", additionalProperties: false, required: ["module", "decls"], properties: { module: STR, decls: { type: "array", items: STR } } },
  },
  replacement: { type: ["string", "null"] },
  new_topic: {
    anyOf: [
      { type: "null" },
      { type: "object", additionalProperties: false, required: ["path", "scope"], properties: { path: STR, scope: STR } },
    ],
  },
} as const;
const ITEM_REQUIRED = ["title", "finding", "reason", "recommendation", "action", "target_module", "modules", "parts", "replacement", "new_topic"];
export const GARDENER_REPLY: Record<string, unknown> = {
  type: "object",
  additionalProperties: false,
  required: ["items", "extra"],
  properties: {
    items: {
      type: "array",
      items: { type: "object", additionalProperties: false, required: ["finding_id", ...ITEM_REQUIRED], properties: { finding_id: STR, ...ITEM_PROPS } },
    },
    extra: {
      type: "array",
      items: { type: "object", additionalProperties: false, required: [...ITEM_REQUIRED, "decls"], properties: { ...ITEM_PROPS, decls: { type: "array", items: STR } } },
    },
  },
};

const MODULE_PATH_RE = /^[A-Z][A-Za-z0-9]*(\/[A-Z][A-Za-z0-9]*)+\.lean$/;

/** Structural problems of a gardener reply (empty = acceptable). `extra` items arrive as findings
 *  of kind `judgement` (`judgementFindings`). */
export function gardenerViolations(items: readonly GardenItem[], findings: readonly GardenFinding[], cfg: Pick<ToolkitConfig, "lib" | "divisions">, taxonomy: Taxonomy): string[] {
  const v: string[] = [];
  const byId = new Map(findings.map((f) => [f.id, f] as const));
  const seen = new Set<string>();
  const topics = new Set(taxonomy.topics.map((t) => t.path));
  const placed = (at: string, rel: string, it: GardenItem) => {
    const topic = topicOfModulePath(rel, cfg);
    if (!MODULE_PATH_RE.test(rel) || topic === null) { v.push(`${at}: "${rel}" must be ${cfg.lib}/<Division>/<topic path>/<File>.lean.`); return; }
    if (!topics.has(topic) && it.new_topic?.path !== topic) v.push(`${at}: "${topic}" is not a topic of the tree — choose one, or set new_topic {path: "${topic}", scope}.`);
    if (it.new_topic?.path === topic) {
      const why = newTopicProblem(topic, taxonomy);
      if (why) v.push(`${at}: ${why}.`);
    }
  };
  for (const it of items) {
    const at = `item ${it.finding_id}`;
    const f = byId.get(it.finding_id);
    if (!f) { v.push(`${at}: not a finding id.`); continue; }
    if (seen.has(it.finding_id)) v.push(`${at}: judged twice.`);
    seen.add(it.finding_id);
    for (const key of ["title", "finding", "reason"] as const) {
      if (it[key].trim() === "") v.push(`${at}: ${key} is empty.`);
      else if (TEX_RE.test(it[key])) v.push(`${at}: ${key} contains TeX — write the mathematics in Unicode.`);
    }
    if (it.action === "relocate") {
      if (!it.target_module) v.push(`${at}: relocate needs target_module.`);
      else placed(at, it.target_module, it);
      if (f.modules.length < 1) v.push(`${at}: relocate moves one module; the finding names none.`);
    } else if (it.action === "merge") {
      if (it.modules.length !== 2 || !it.modules.every((m) => f.modules.includes(m))) v.push(`${at}: merge names the finding's two modules, kept one first.`);
    } else if (it.action === "split") {
      const mains = new Set(f.decls);
      const movable = new Set([...f.decls, ...(f.shared ?? [])]);
      const given = it.parts.flatMap((p) => p.decls);
      if (it.parts.length < 2) v.push(`${at}: split needs at least two parts.`);
      // say which rule broke: a reply that also lists a result's helpers reads "exactly one part" as met
      const extra = [...new Set(given.filter((d) => !movable.has(d)))];
      const missing = [...mains].filter((d) => !given.includes(d));
      const twice = [...new Set(given.filter((d, k) => given.indexOf(d) !== k))];
      if (extra.length) v.push(`${at}: split lists ${extra.join(", ")}, which ${extra.length === 1 ? "is" : "are"} not among the module's main results (${[...mains].join(", ")})${f.shared?.length ? ` or the shared ${f.shared.join(", ")}` : ""} — a helper moves with the result it serves; leave it out.`);
      if (missing.length) v.push(`${at}: split leaves ${missing.join(", ")} in no part — every main result of the module goes in exactly one.`);
      if (twice.length) v.push(`${at}: split places ${twice.join(", ")} in more than one part.`);
      for (const p of it.parts) if (p.module !== f.modules[0]) placed(at, p.module, it);
    } else if (it.action === "retire") {
      if (!it.replacement) v.push(`${at}: retire needs the replacement declaration.`);
      if (f.decls.length !== 1 && f.kind !== "duplicate") v.push(`${at}: retire drops one result.`);
    } else if (it.action === "remove") {
      if (f.decls.length !== 1) v.push(`${at}: remove drops one result.`);
    } else if (it.action === "rename" || it.action === "trim_imports") {
      if (f.modules.length < 1) v.push(`${at}: ${it.action} works on one module; the finding names none.`);
    } else if (it.action === "cross_reference") {
      if (f.decls.length < 2) v.push(`${at}: cross_reference links two or more results; the finding names ${f.decls.length}.`);
    }
  }
  for (const f of findings) if (!seen.has(f.id)) v.push(`finding ${f.id} was not judged.`);
  return v;
}

/** The gardener's own items as `judgement` findings (ids after the mechanical ones) and items. */
export function judgementFindings(extra: readonly GardenExtra[], from: number, graph: ToolkitGraph): { findings: GardenFinding[]; items: GardenItem[] } {
  const mod = new Map(graph.nodes.map((n) => [n.id, n.module] as const));
  const findings: GardenFinding[] = [];
  const items: GardenItem[] = [];
  extra.forEach((x, k) => {
    const id = `g-${from + k + 1}`;
    const { decls, ...rest } = x;
    const modules = [...new Set([...x.modules, ...decls.flatMap((d) => (mod.get(d) ? [moduleRel(mod.get(d)!)] : []))])];
    findings.push({ id, kind: "judgement", modules, decls, detail: x.finding });
    items.push({ ...rest, finding_id: id, modules: x.action === "merge" ? x.modules : modules });
  });
  return { findings, items };
}

export interface GardenBatch {
  created: string;
  findings: GardenFinding[];
  items: GardenItem[];
  /** Items the gardener judged fine as they are: one line each in the checklist, nothing to decide. */
  left_as_is?: Array<{ finding_id: string; title: string; reason: string }>;
  /** The main results the gardener saw (a later round calls it again only when they changed). */
  main_results?: string[];
  /** sha256 of every toolkit module's text when the list was made: the next gardener reads in full
   *  the modules changed since. */
  module_hashes?: Record<string, string>;
}

/** What the gardener reads in full, at most this many bytes of Lean (findings' modules first). */
export const GARDENER_SOURCE_CAP = 160_000;

/**
 * The toolkit modules the gardener reads in full: every module a finding names, then every module
 * added or changed since the last list (`lastHashes`; all of them on a first list), within `cap`
 * bytes. Unaffected unchanged modules stay as their main-view lines; `omitted` lists what the cap
 * left out.
 */
export function gardenerSources(
  texts: ReadonlyMap<string, string>,
  lastHashes: Readonly<Record<string, string>> | null,
  findings: readonly GardenFinding[],
  cap = GARDENER_SOURCE_CAP,
): { included: Array<{ module: string; why: "finding" | "changed"; text: string }>; omitted: string[] } {
  const named = [...new Set(findings.flatMap((f) => f.modules.map(moduleOfRel)))].filter((m) => texts.has(m)).sort();
  const changed = [...texts.keys()].filter((m) => !named.includes(m) && (!lastHashes || lastHashes[m] !== sha256(texts.get(m)!))).sort();
  const included: Array<{ module: string; why: "finding" | "changed"; text: string }> = [];
  const omitted: string[] = [];
  let used = 0;
  for (const [module, why] of [...named.map((m) => [m, "finding"] as const), ...changed.map((m) => [m, "changed"] as const)]) {
    const text = texts.get(module)!;
    if (used + text.length > cap) { omitted.push(module); continue; }
    used += text.length;
    included.push({ module, why, text });
  }
  return { included, omitted };
}

/** The main view in a few lines per main result, for the gardener: name, title, topic and module,
 *  the main results it uses, and the first sentence of its docstring. */
export function mainViewSummary(graph: ToolkitGraph, docs: ReadonlyMap<string, string | null>, titles: ReadonlyMap<string, string>): string {
  const main = mainView(graph);
  const uses = new Map<string, string[]>();
  for (const [a, b] of main.edges) uses.set(a, [...(uses.get(a) ?? []), b]);
  const lines: string[] = [];
  for (const n of main.nodes.filter((x) => x.layer === "toolkit")) {
    const used = (uses.get(n.id) ?? []).filter((u) => main.nodes.find((x) => x.id === u)?.layer === "toolkit");
    const doc = (docs.get(n.id) ?? "").replace(/\s+/g, " ").trim();
    const sentence = doc.split(/(?<=\.)\s/)[0]?.slice(0, 240) ?? "";
    lines.push(`- ${n.id}${titles.get(n.id) ? ` — ${titles.get(n.id)}` : ""}\n  topic ${n.division ?? "?"} › ${(n.module.split(".").slice(2, -1)).join(" › ")}; module ${moduleRel(n.module)}` +
      (used.length ? `; uses ${used.join(", ")}` : "") + (sentence ? `\n  ${sentence}` : ""));
  }
  return lines.join("\n") || "(no main results yet)";
}

/** One Claude call over the findings and the main view; a dry run keeps every finding (`keep`). */
export async function runGardener(args: {
  toolkit: ToolkitConfig;
  findings: readonly GardenFinding[];
  taxonomy: Taxonomy;
  graph: ToolkitGraph;
  docs?: ReadonlyMap<string, string | null>;
  titles?: ReadonlyMap<string, string>;
  /** The modules the gardener reads in full (`gardenerSources`). */
  sources?: ReturnType<typeof gardenerSources>;
  dryRun?: boolean;
  runClaude?: (o: ClaudeRunInput) => Promise<string>;
  /** The run's token ledger the call is recorded in (none from `leansmith garden`). */
  ledger?: TokenLedger;
  log: (m: string) => void;
}): Promise<{ findings: GardenFinding[]; items: GardenItem[] }> {
  const cfg = args.toolkit;
  const [rules, modules] = await Promise.all([readProposalPrompt("gardener.txt"), listToolkitModules(cfg)]);
  const prompt = [
    rules,
    section("TOOLKIT", JSON.stringify({ lib: cfg.lib, divisions: cfg.divisions }, null, 2)),
    section("TOPIC TREE (doc/taxonomy.json)", taxonomyPromptText(args.taxonomy)),
    section("EXISTING TOOLKIT MODULES", modules.length ? modules.map((m) => `- ${m.path}: ${m.overview}`).join("\n") : "(none yet)"),
    section("MAIN RESULTS (the main view: what each states, where it sits, what it uses)", mainViewSummary(args.graph, args.docs ?? new Map(), args.titles ?? new Map())),
    section("FINDINGS", args.findings.length ? JSON.stringify(args.findings, null, 1) : "(none)"),
    section(
      "SOURCE (the full Lean of every module a finding names and of every module added or changed since the last list)",
      args.sources?.included.length
        ? [...args.sources.included.map((x) => `### ${moduleRel(x.module)} (${x.why === "finding" ? "named by a finding" : "changed since the last list"})\n\n\`\`\`lean\n${x.text.replace(/\n*$/, "")}\n\`\`\``),
          ...(args.sources.omitted.length ? [`Not shown (size cap; read them in the toolkit): ${args.sources.omitted.map(moduleRel).join(", ")}`] : [])].join("\n\n")
        : "(no module changed since the last list)",
    ),
  ].join("\n\n");
  if (args.dryRun) {
    await recordPrompt(cfg, "_garden", "gardener", prompt, true, args.log, claudeRoleModel(MODELS.claudeMain));
    return {
      findings: [...args.findings],
      items: args.findings.map((f) => ({
        finding_id: f.id, title: `[dry-run] ${f.kind}`, finding: f.detail, reason: "[dry-run] no gardener was called",
        recommendation: "decline", action: "keep", target_module: null, modules: [], parts: [], replacement: null, new_topic: null,
      })),
    };
  }
  const reply = await askJson<{ items: GardenItem[]; extra: GardenExtra[] }>({
    cfg, slug: "_garden", name: "gardener", prompt, schema: GARDENER_REPLY, asker: claudeAsker(cfg, args.runClaude, args.ledger), log: args.log,
    violations: (r) => {
      const j = judgementFindings(r.extra ?? [], args.findings.length, args.graph);
      return gardenerViolations([...(r.items ?? []), ...j.items], [...args.findings, ...j.findings], cfg, args.taxonomy);
    },
  });
  const j = judgementFindings(reply.extra ?? [], args.findings.length, args.graph);
  return { findings: [...args.findings, ...j.findings], items: [...reply.items, ...j.items] };
}

// ─── the owner's checklist ─────────────────────────────────────────────────

export function gardenPaths(cfg: Pick<ToolkitConfig, "toolkitRoot">, created: string): { md: string; json: string } {
  const stamp = created.replace(/[:.]/g, "-");
  const dir = path.join(cfg.toolkitRoot, "doc", "proposals");
  return { md: path.join(dir, `garden-${stamp}.md`), json: path.join(dir, `garden-${stamp}.json`) };
}

function actionText(it: GardenItem): string {
  switch (it.action) {
    case "keep": return "Leave it as it is.";
    case "relocate": return `Move the module to \`${it.target_module}\`; everything using it is updated.`;
    case "merge": return `Fold \`${it.modules[1]}\` into \`${it.modules[0]}\`; everything using it is updated.`;
    case "split": return `Split it into ${it.parts.map((p) => `\`${p.module}\` (${p.decls.map((d) => d.slice(d.lastIndexOf(".") + 1)).join(", ")})`).join(" and ")}.`;
    case "retire": return `Drop it; its users switch to \`${it.replacement}\`, which already states it.`;
    case "remove": return "Drop it (nothing uses it).";
    case "rename": return "Put its declarations in the namespace of its topic; everything using them is updated.";
    case "trim_imports": return "Import only the modules it uses instead of the whole library.";
    case "cross_reference": return "Keep both, and have each one's description point to the other.";
  }
}

export function renderGardenChecklist(batch: GardenBatch, opts: { toolkitRoot: string; decisions?: Readonly<Record<string, ChecklistDecision>> }): string {
  const md = gardenPaths({ toolkitRoot: opts.toolkitRoot }, batch.created).md;
  const head = [
    "# Gardening suggestions for your toolkit",
    "",
    `Created ${batch.created} from the toolkit's dependency graph. Each item is a suggestion; the orchestrator`,
    "decides it (an item that retires or removes a result goes to the owner) on its `decision:` line:",
    "",
    "- `accept` — the change is carried out by editing the Lean as described (the toolkit committed first),",
    "  then checked: everything builds, axioms standard, no paper statement changed, lints, index, graph.",
    "- `decline` — leave the toolkit as it is.",
    "- `defer` — not now.",
    "",
    "Once the accepted items are carried out:",
    "",
    `    leansmith garden --verify ${md} --toolkit ${opts.toolkitRoot}`,
    "",
  ];
  const body = batch.items.map((it) => {
    const d = opts.decisions?.[it.finding_id] ?? { kind: "pending" as const };
    return [
      `## ${it.finding_id} · ${it.title}`,
      "",
      `**What the graph shows.** ${it.finding}`,
      "",
      `**Suggested change.** ${actionText(it)}`,
      ...(it.new_topic ? ["", `**New topic.** ${it.new_topic.path} — ${it.new_topic.scope} (accepting the item adds it to the topic tree).`] : []),
      "",
      `**Why.** ${it.reason}`,
      "",
      `**Recommendation.** ${it.recommendation}${it.action === "keep" ? " (nothing to apply)" : ""}`,
      "",
      "```decision",
      `decision: ${d.kind}`,
      ...(d.kind !== "pending" && d.note ? [`note: ${d.note}`] : []),
      "```",
      "",
    ].join("\n");
  });
  const fine = batch.left_as_is ?? [];
  const tail = fine.length
    ? ["", `Also reviewed and fine as they are (nothing to decide): ${fine.map((x) => `${x.title.replace(/\.$/, "")} — ${x.reason.replace(/\.$/, "")}`).join("; ")}.`, ""]
    : [];
  return [...head, ...body, ...tail].join("\n");
}

const GARDEN_SECTION_RE = /^## (g-[0-9]+) · /;

/** The decisions on a garden checklist (accept | decline | defer | pending). */
export function parseGardenChecklist(text: string, batch: GardenBatch): Record<string, ChecklistDecision> {
  const ids = new Set(batch.items.map((i) => i.finding_id));
  const lines = text.split(/\r?\n/);
  const out: Record<string, ChecklistDecision> = {};
  for (let i = 0; i < lines.length; i += 1) {
    const m = lines[i]!.match(GARDEN_SECTION_RE);
    if (!m) continue;
    const id = m[1]!;
    if (!ids.has(id)) throw new Error(`garden item ${id}: not an item of this list`);
    let j = i + 1;
    while (j < lines.length && lines[j]!.trim() !== "```decision" && !/^## /.test(lines[j]!)) j += 1;
    if (j >= lines.length || lines[j]!.trim() !== "```decision") throw new Error(`garden item ${id}: no \`\`\`decision block`);
    let end = j + 1;
    while (end < lines.length && lines[end]!.trim() !== "```") end += 1;
    const d = parseDecisionBlock(id, lines.slice(j + 1, end));
    if (!["pending", "accept", "decline", "defer"].includes(d.kind)) throw new Error(`garden item ${id}: decide accept, decline or defer (not ${d.kind})`);
    out[id] = d;
    i = end;
  }
  for (const id of ids) if (!(id in out)) throw new Error(`garden item ${id}: missing from the checklist`);
  return out;
}

/** The toolkit's division modules (dotted name → text), staging excluded. */
export async function toolkitModuleTexts(cfg: ToolkitConfig): Promise<Map<string, string>> {
  const out = new Map<string, string>();
  for (const abs of await libraryFiles(cfg)) {
    const rel = path.relative(cfg.toolkitRoot, abs).split(path.sep).join("/");
    const parts = rel.replace(/\.lean$/, "").split("/");
    if (parts[0] !== cfg.lib || !cfg.divisions.includes(parts[1] ?? "") || parts.length < 4) continue;
    out.set(parts.join("."), await readFile(abs, "utf8"));
  }
  return out;
}

/** The latest gardening list on file (null: none yet). */
async function lastGardenBatch(cfg: ToolkitConfig): Promise<GardenBatch | null> {
  const dir = path.join(cfg.toolkitRoot, "doc", "proposals");
  const latest = (await readdir(dir).catch(() => [] as string[])).filter((f) => /^garden-.*\.json$/.test(f)).sort().pop();
  return latest ? (JSON.parse(await readFile(path.join(dir, latest), "utf8")) as GardenBatch) : null;
}

/** A finding's identity across lists: its kind, what it says, and the content of each module it
 *  names (hashes); null when a module's content is unknown. */
function findingKey(f: GardenFinding, hashes: Readonly<Record<string, string>>): string | null {
  const hs = f.modules.map((m) => hashes[moduleOfRel(m)]);
  return hs.some((h) => h === undefined) ? null : [f.kind, f.detail, ...hs].join("\u0000");
}

/**
 * The findings the last list's gardener judged fine as they are (`left_as_is`), unchanged since: the
 * same kind and detail over the same module content. A mechanical finding (a result nothing uses, two
 * modules using each other) stands until the toolkit changes, so these are not sent to the gardener
 * again; they are carried on the new list with their earlier judgement.
 */
export function settledFindings(
  findings: readonly GardenFinding[],
  last: Pick<GardenBatch, "findings" | "left_as_is" | "module_hashes"> | null,
  hashes: Readonly<Record<string, string>>,
): Map<GardenFinding, { title: string; reason: string }> {
  const out = new Map<GardenFinding, { title: string; reason: string }>();
  if (!last?.module_hashes || !last.left_as_is?.length) return out;
  const prior = new Map<string, { title: string; reason: string }>();
  for (const x of last.left_as_is) {
    const f = last.findings.find((y) => y.id === x.finding_id);
    const key = f ? findingKey(f, last.module_hashes) : null;
    if (key) prior.set(key, { title: x.title, reason: x.reason });
  }
  for (const f of findings) {
    const key = findingKey(f, hashes);
    const p = key ? prior.get(key) : undefined;
    if (p) out.set(f, p);
  }
  return out;
}

/**
 * Write the gardening list (batch + checklist). The gardener is called when the graph has findings
 * it has not judged (`settledFindings`) or the main results changed since the last list (a new
 * result may sit in the wrong topic or restate another); otherwise there is nothing to garden and no
 * model call. Items the gardener leaves as they are become one summary line; null when nothing is
 * left to decide.
 */
export async function runGardenRound(args: {
  toolkit: ToolkitConfig;
  graph: ToolkitGraph;
  log: (m: string) => void;
  now?: () => Date;
  dryRun?: boolean;
  runClaude?: (o: ClaudeRunInput) => Promise<string>;
  /** The run's token ledger the gardener's call is recorded in. */
  ledger?: TokenLedger;
  /** The `--graph` scan the graph was built from (base duplicates, docstrings); default: the one on file. */
  scan?: Pick<CandidateScan, "declarations"> | null;
  /** Toolkit module texts (namespace, imports, direction); default: read from the toolkit. */
  moduleTexts?: ReadonlyMap<string, string>;
}): Promise<{ path: string; items: number } | null> {
  const cfg = args.toolkit;
  const taxonomy = args.dryRun ? await effectiveTaxonomy(cfg) : await ensureTaxonomy(cfg, args.log);
  const scan = args.scan !== undefined ? args.scan : await readGraphScan(cfg);
  const moduleTexts = args.moduleTexts ?? (await toolkitModuleTexts(cfg));
  const module_hashes = Object.fromEntries([...moduleTexts].map(([m, t]) => [m, sha256(t)] as const));
  const all = gardenFindings({ cfg, graph: args.graph, taxonomy, baseDups: await baseDuplicates(cfg, scan), moduleTexts });
  const mains = mainView(args.graph).nodes.filter((n) => n.layer === "toolkit").map((n) => n.id).sort();
  const last = await lastGardenBatch(cfg);
  const settled = settledFindings(all, last, module_hashes);
  // the findings the gardener sees, numbered afresh; the settled ones follow them on the list
  const findings = all.filter((f) => !settled.has(f)).map((f, i) => ({ ...f, id: `g-${i + 1}` }));
  const before = last?.main_results ?? null;
  if (findings.length === 0 && before !== null && before.join(",") === mains.join(",")) {
    args.log(`gardening: no ${settled.size ? "new " : ""}findings and no new main results since the last list${settled.size ? ` (${settled.size} judged fine on it, unchanged since)` : ""} — nothing to garden`);
    return null;
  }
  if (settled.size) args.log(`gardening: ${settled.size} finding(s) judged fine on the last list and unchanged since are not sent again`);
  const docs = new Map((scan?.declarations ?? []).map((d) => [d.name, (d as { doc?: string | null }).doc ?? null] as const));
  const ledger = await loadLedger(cfg.ledgerPath).catch(() => null);
  const titles = new Map(((ledger?.declarations ?? []) as Array<{ name: string; title?: string }>).flatMap((x) => (x.title ? [[x.name, x.title] as const] : [])));
  const sources = gardenerSources(moduleTexts, last?.module_hashes ?? null, findings);
  const judged = await runGardener({
    toolkit: cfg, findings, taxonomy, graph: args.graph, docs, titles, sources, log: args.log,
    ...(args.dryRun ? { dryRun: true } : {}), ...(args.runClaude ? { runClaude: args.runClaude } : {}), ...(args.ledger ? { ledger: args.ledger } : {}),
  });
  const items = judged.items.filter((it) => it.action !== "keep");
  const carried = [...settled].map(([f, p], i) => ({ finding: { ...f, id: `g-${judged.findings.length + i + 1}` }, ...p }));
  const left = [
    ...judged.items.filter((it) => it.action === "keep").map((it) => ({ finding_id: it.finding_id, title: it.title, reason: it.reason })),
    ...carried.map((c) => ({ finding_id: c.finding.id, title: c.title, reason: c.reason })),
  ];
  const created = (args.now ?? (() => new Date()))().toISOString();
  const batch: GardenBatch = { created, findings: [...judged.findings, ...carried.map((c) => c.finding)], items, left_as_is: left, main_results: mains, module_hashes };
  const p = gardenPaths(cfg, created);
  await mkdir(path.dirname(p.md), { recursive: true });
  await writeJsonAtomic(p.json, batch);
  if (items.length === 0) {
    args.log(`gardening: nothing to change${left.length ? ` (${left.length} finding(s) fine as they are)` : ""} — recorded in ${p.json}`);
    return null;
  }
  await writeTextAtomic(p.md, renderGardenChecklist(batch, { toolkitRoot: cfg.toolkitRoot }));
  args.log(`gardening: ${items.length} suggestion(s) for you to decide → ${p.md}`);
  return { path: p.md, items: items.length };
}

/** The scan `refreshToolkitGraph` last wrote (`.lake/build/leansmith/graph_scan.json`), or null. */
export async function readGraphScan(cfg: Pick<ToolkitConfig, "toolkitRoot">): Promise<CandidateScan | null> {
  const p = path.join(cfg.toolkitRoot, ".lake", "build", "leansmith", "graph_scan.json");
  return existsSync(p) ? (JSON.parse(await readFile(p, "utf8")) as CandidateScan) : null;
}

// ─── files ─────────────────────────────────────────────────────────────────

/** Every Lean file of the toolkit library and the papers (absolute paths). */
async function libraryFiles(cfg: ToolkitConfig): Promise<string[]> {
  const out: string[] = [];
  const walk = async (dir: string): Promise<void> => {
    for (const e of await readdir(dir, { withFileTypes: true }).catch(() => [])) {
      const abs = path.join(dir, e.name);
      if (e.isDirectory()) { if (e.name !== ".lake" && e.name !== "tmp" && abs !== cfg.stagingDir) await walk(abs); }
      else if (e.isFile() && e.name.endsWith(".lean")) out.push(abs);
    }
  };
  await walk(cfg.toolkitLibDir);
  await walk(cfg.papersDir);
  for (const f of [path.join(cfg.toolkitRoot, `${cfg.lib}.lean`), path.join(cfg.toolkitRoot, `${cfg.papersLib}.lean`)]) if (existsSync(f)) out.push(f);
  return [...new Set(out)].sort();
}

