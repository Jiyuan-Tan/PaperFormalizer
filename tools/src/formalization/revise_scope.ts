// What a REVISE call carries. A re-plan (F1), the review of a re-plan (F1.5) and a re-scaffold
// (F2) each change a handful of nodes of a core and a plan that are otherwise settled; pasting
// both whole into every such call took the three prompts of a 220-entry paper to 0.36, 1.05 and
// 1.13 MB — the last two past what the provider accepts. A revise prompt carries instead: its
// change block, the AFFECTED nodes in full (`reviseAffectedNodeIds`), one reference line for every
// other node (`nodeReferenceIndex`), and where to look up what the affected set missed
// (`reviseLookupBlock`). A first plan, a first review and a first scaffold still get everything.

import { existsSync } from "node:fs";
import { readFile, writeFile } from "node:fs/promises";
import type { Core } from "../core/schema.js";
import { PIN_REASON_PREFIX } from "../verify/core_graph.js";
import { refsIn } from "../verify/referee_slices.js";
import type { Plan } from "./plan/schema.js";

type Rec = Record<string, unknown>;
type PlanNodes = Pick<Plan, "nodes">;

/** A typed-core node id in free text (a reviewer's finding, a directive). */
const NODE_ID_RE = /\b(?:thm|lem|prop|oeq|conj|def|ass):[a-z0-9-]+/g;

/** The core node ids `texts` name (a correction, a directive, a finding's label), in order. Pure. */
export function namedNodeIds(core: Core, texts: ReadonlyArray<string | null | undefined>): string[] {
  const ids = new Set([...core.assumptions, ...core.definitions, ...core.statements].map((n) => n.id));
  const out = new Set<string>();
  for (const t of texts) for (const m of (t ?? "").match(NODE_ID_RE) ?? []) if (ids.has(m)) out.add(m);
  return [...out];
}

/** The plan entries `texts` name: core node ids (`namedNodeIds`) and the ids of the plan's S-blocks
 *  and citations, in order. What a finding can be applied to — a review naming none has no entry to re-plan. Pure. */
export function namedPlanEntries(core: Core, plan: Pick<Plan, "env" | "citations"> | null, texts: ReadonlyArray<string | null | undefined>): string[] {
  const envIds = new Set([...(plan?.env ?? []), ...(plan?.citations ?? [])].map((e) => e.id));
  const out = new Set(namedNodeIds(core, texts));
  for (const t of texts) for (const m of (t ?? "").match(/\bS[0-9]+\b|\bcite:[A-Za-z0-9_-]+/g) ?? []) if (envIds.has(m)) out.add(m);
  return [...out];
}

/**
 * The nodes a revise must have in full: the SEEDS — the nodes its change block names (a core
 * delta, a correction, a directive, a redirect's "Declarations to edit", a changed plan entry) —
 * and what must move with them. THE RULE, applied to the seeds and to every node it adds:
 *
 *  1. USERS OF A CHANGED PREMISE. When X is an assumption, a definition, or a statement the plan
 *     threads as a hypothesis (its entry is a `gate` or has `lean_kind:"assumption"`), every
 *     statement with X in its core `depends_on`, every class with X in `by_member_properties` and
 *     every construction with X in `inputs` is affected. Whatever X is, every plan entry citing X
 *     in `hyps` or `members` is affected. (So a changed atom reaches the classes bundling it, and
 *     through them the statements taking those classes.)
 *
 * and then, once, without closing again:
 *
 *  2. PIN SUBJECTS. The node an affected pinned reading (`ass:pin-*`) is a reading of — its
 *     meaning is fixed by the pin wherever it is used. (The results the pin is wired into are
 *     its users, rule 1.)
 *  3. SPLIT BLOCKS. The statement an affected block was split from, and every block split from
 *     an affected statement or from the same parent as an affected block.
 *
 * What the rule deliberately does NOT follow: from a changed ordinary statement to the statements
 * that USE it as a lemma (their plan entries and signatures do not cite it; their proofs are the
 * proof loop's to redo), and from a node to its unchanged prerequisites (the reference index
 * names those). It is a mechanical lower bound: a change whose effect travels by wording alone
 * (a symbol's meaning, a renamed notion) is not seen, so every revise prompt keeps the agent's
 * duty to trace further, by lookup. Ids that are not core nodes are dropped.
 *
 * `flagged` are nodes whose RECORD did not change — a reviewer flagged their Lean, a directive
 * names them. Rule 1 is about a changed premise and rule 3 about a re-split statement, so neither
 * starts from them: a flagged node is carried alone, with the subject of a flagged pinned reading
 * (rule 2). Its users take the corrected declaration by name; `nodeNeighbours` names them. Pure.
 */
export function reviseAffectedNodeIds(core: Core, plan: PlanNodes | null, seeds: Iterable<string>, flagged: Iterable<string> = []): Set<string> {
  const statementIds = new Set(core.statements.map((s) => s.id));
  const nodeIds = new Set([...core.assumptions.map((a) => a.id), ...core.definitions.map((d) => d.id), ...statementIds]);
  const coreUsers = new Map<string, Set<string>>();
  const planUsers = new Map<string, Set<string>>();
  const link = (into: Map<string, Set<string>>, user: string, premise: string): void => {
    if (!nodeIds.has(user) || !nodeIds.has(premise)) return;
    if (!into.has(premise)) into.set(premise, new Set());
    into.get(premise)!.add(user);
  };
  for (const s of core.statements) for (const d of s.depends_on) link(coreUsers, s.id, d);
  for (const d of core.definitions) for (const m of [...(d.by_member_properties ?? []), ...(d.inputs ?? [])]) link(coreUsers, d.id, m);
  for (const [id, entry] of Object.entries(plan?.nodes ?? {})) {
    for (const h of [...(entry.hyps ?? []), ...(entry.members ?? [])]) link(planUsers, id, h);
  }
  const isPremise = (id: string): boolean => {
    if (!statementIds.has(id)) return true;
    const entry = plan?.nodes[id];
    return !!entry && (entry.gate === true || entry.lean_kind === "assumption");
  };
  const affected = new Set<string>();
  const queue = [...seeds].filter((id) => nodeIds.has(id));
  while (queue.length > 0) {
    const id = queue.pop()!;
    if (affected.has(id)) continue;
    affected.add(id);
    for (const u of planUsers.get(id) ?? []) queue.push(u);
    if (isPremise(id)) for (const u of coreUsers.get(id) ?? []) queue.push(u);
  }
  const closed = [...affected];
  for (const id of flagged) if (nodeIds.has(id)) affected.add(id);
  for (const a of core.assumptions) {
    const reason = a.bookkeeping?.reason ?? "";
    if (!affected.has(a.id) || !a.id.startsWith("ass:pin-") || !reason.startsWith(PIN_REASON_PREFIX)) continue;
    const subject = reason.slice(PIN_REASON_PREFIX.length).split(": ")[0]!.trim();
    if (nodeIds.has(subject)) affected.add(subject);
  }
  const parents = new Set<string>();
  for (const s of core.statements) {
    if (closed.includes(s.id)) parents.add(s.id);
    if (s.split_from && closed.includes(s.id)) parents.add(s.split_from);
  }
  for (const s of core.statements) if (s.split_from && parents.has(s.split_from)) affected.add(s.id);
  for (const p of parents) if (nodeIds.has(p)) affected.add(p);
  return affected;
}

/**
 * The nodes the TEXT of a node of `ids` names and `ids` lacks: by `\ref` label (`refsIn`: the
 * statement carrying the label, or — a label no statement carries — the assumptions and
 * definitions stated under it) or by core id, in its statement / condition / construction or in
 * the reason of a condition V1.5 added. No graph edge records such a mention, and a condition that
 * reads "the conditions of Lemma X hold" has X's hypotheses for its content. Pure.
 */
export function referencedNodeIds(core: Core, ids: ReadonlySet<string>): Set<string> {
  type Rec = { id: string; statement?: string; condition?: string; construction?: string | null; bookkeeping?: { reason?: string } | null; tex_locator?: { label?: string | null } | null };
  const nodes = [...core.statements, ...core.assumptions, ...core.definitions] as Rec[];
  const known = new Set(nodes.map((n) => n.id));
  const statementOf = new Map<string, string[]>();
  const statedUnder = new Map<string, string[]>();
  for (const n of nodes) {
    const label = n.tex_locator?.label;
    if (!label) continue;
    const into = core.statements.some((s) => s.id === n.id) ? statementOf : statedUnder;
    into.set(label, [...(into.get(label) ?? []), n.id]);
  }
  const out = new Set<string>();
  for (const n of nodes) {
    if (!ids.has(n.id)) continue;
    const text = [n.statement, n.condition, n.construction, n.bookkeeping?.reason].filter(Boolean).join("\n");
    for (const label of refsIn(text)) for (const id of statementOf.get(label) ?? statedUnder.get(label) ?? []) out.add(id);
    for (const id of text.match(NODE_ID_RE) ?? []) if (known.has(id)) out.add(id);
  }
  for (const id of ids) out.delete(id);
  return out;
}

/** Derived or locator-only fields of a core record: a change in one alone moves nothing. */
const QUIET_CORE_FIELDS = ["used_by", "tex_locator"];

const shape = (x: Rec, quiet: readonly string[]): string =>
  JSON.stringify(Object.fromEntries(Object.entries(x).filter(([k]) => !quiet.includes(k))));

const recs = (x: unknown): Rec[] => (Array.isArray(x) ? (x as Rec[]) : []);

/**
 * The seeds a changed core gives: every node of `cur` that `prev` lacks or records differently
 * (locator-only fields apart), and for a changed or added SYMBOL the definition it names (`ref`)
 * and the results of each `scoped` clause that is new or gone — the symbol itself is returned in
 * `symbols`. A removed node has no record left; the statements that cited it changed with it.
 * `prev`/`cur` are cores or prompt views of cores (`formalizationCoreContextValue`). Pure.
 */
export function coreChangeSeeds(prev: unknown, cur: unknown): { nodes: string[]; symbols: string[] } {
  const p = (prev ?? {}) as Rec;
  const c = (cur ?? {}) as Rec;
  const nodes = new Set<string>();
  for (const key of ["assumptions", "definitions", "statements"]) {
    const before = new Map(recs(p[key]).map((n) => [String(n.id), shape(n, QUIET_CORE_FIELDS)] as const));
    for (const n of recs(c[key])) if (before.get(String(n.id)) !== shape(n, QUIET_CORE_FIELDS)) nodes.add(String(n.id));
  }
  const symbols: string[] = [];
  const before = new Map(recs(p.symbols).map((s) => [String(s.name), s] as const));
  for (const s of recs(c.symbols)) {
    const old = before.get(String(s.name));
    if (old && shape(old, []) === shape(s, [])) continue;
    symbols.push(String(s.name));
    if (typeof s.ref === "string") nodes.add(s.ref);
    // A clause on one side only (added, dropped, or reworded: on both sides, differently).
    const had = new Set(recs(old?.scoped).map((cl) => JSON.stringify(cl)));
    const has = new Set(recs(s.scoped).map((cl) => JSON.stringify(cl)));
    for (const [cls, other] of [[recs(s.scoped), had], [recs(old?.scoped), has]] as const) {
      for (const cl of cls) if (!other.has(JSON.stringify(cl))) for (const r of Array.isArray(cl.results) ? cl.results : []) nodes.add(String(r));
    }
  }
  return { nodes: [...nodes], symbols };
}

/**
 * The plan entries of `cur` that `prev` lacks or records differently: node ids, S-block ids, and
 * `other` when something else of the plan moved (citations, feasibility, a top-level field).
 * An entry's `notes` count: F1 records the statement shape and the encoding decisions there. Pure.
 */
export function planChangeSeeds(prev: unknown, cur: unknown): { nodes: string[]; envs: string[]; other: boolean } {
  const quiet: string[] = [];
  const p = (prev ?? {}) as Rec;
  const c = (cur ?? {}) as Rec;
  const pn = (p.nodes ?? {}) as Record<string, Rec>;
  const nodes = Object.entries((c.nodes ?? {}) as Record<string, Rec>)
    .filter(([id, entry]) => !pn[id] || shape(pn[id]!, quiet) !== shape(entry, quiet))
    .map(([id]) => id);
  const pe = new Map(recs(p.env).map((e) => [String(e.id), shape(e, quiet)] as const));
  const envs = recs(c.env).filter((e) => pe.get(String(e.id)) !== shape(e, quiet)).map((e) => String(e.id));
  const rest = (x: Rec): string => shape(x, ["nodes", "env"]);
  return { nodes, envs, other: rest(p) !== rest(c) };
}

/**
 * One line per core node NOT in `shown` — what a revise needs to REFER to a node it does not
 * carry: `<id> | <what it is> | <lean_kind> <lean_name> | <target_file>` (the plan columns are
 * absent for a node the plan does not map yet), and for a result the paper labels, how a text
 * cites it: `| \ref{<label>}`. Pure.
 */
export function nodeReferenceIndex(core: Core, plan: PlanNodes | null, shown: ReadonlySet<string>): string[] {
  const line = (id: string, what: string, label?: string | null): string | null => {
    if (shown.has(id)) return null;
    const e = plan?.nodes[id];
    return [id, what, ...(e ? [`${e.lean_kind} ${e.lean_name}`, ...(e.target_file ? [e.target_file] : [])] : ["no plan entry"]), ...(label ? [`\\ref{${label}}`] : [])].join(" | ");
  };
  return [
    ...core.assumptions.map((a) => line(a.id, "assumption")),
    ...core.definitions.map((d) => line(d.id, d.by_member_properties ? "class" : "construction")),
    ...core.statements.map((s) => line(s.id, s.kind, s.tex_locator?.label)),
  ].filter((l): l is string => l !== null);
}

/**
 * The nodes one hop from `shown` and not in it: what a shown node rests on (its core `depends_on`,
 * a class's members, a construction's inputs, its plan `hyps` / `members`, a block's parent) and
 * what uses a shown node the same way. An edit to a shown node's declaration reads the first and
 * must still compile under the second. Pure.
 */
export function nodeNeighbours(core: Core, plan: PlanNodes | null, shown: ReadonlySet<string>): Set<string> {
  const out = new Set<string>();
  const edge = (user: string, premise: string): void => {
    if (shown.has(user) && !shown.has(premise)) out.add(premise);
    if (shown.has(premise) && !shown.has(user)) out.add(user);
  };
  for (const s of core.statements) for (const d of [...s.depends_on, ...(s.split_from ? [s.split_from] : [])]) edge(s.id, d);
  for (const d of core.definitions) for (const m of [...(d.by_member_properties ?? []), ...(d.inputs ?? [])]) edge(d.id, m);
  for (const [id, entry] of Object.entries(plan?.nodes ?? {})) for (const h of [...(entry.hyps ?? []), ...(entry.members ?? [])]) edge(id, h);
  return out;
}

/** The reply marker under which an agent names what it looked up beyond the affected set. */
export const BEYOND_SCOPE_KEY = "looked_up_beyond_scope";

/**
 * The block every scoped revise prompt ends its context with: the reference index, where the
 * whole core and plan are, how to look a node up, and the duty to report having done so.
 * `replyField` says where in the reply the report goes. `neighboursOnly`: the prompt already
 * holds a line for EVERY node, and `index` is the ids of the nodes one hop from the affected set
 * (`nodeNeighbours`). Pure.
 */
export function reviseLookupBlock(args: { index: string[]; shown: number; total: number; corePath: string; planPath: string; replyField: string; neighboursOnly?: boolean }): string {
  return [
    ...(args.neighboursOnly
      ? [
          `=== NEIGHBOURS OF THE AFFECTED NODES (${args.index.length} of the ${args.total - args.shown} nodes not shown in full) ===`,
          "What an affected node rests on or is used by, unchanged — the lines of these ids in EVERY NODE are the ones to read first:",
          args.index.join(", ") || "(none)",
          "=== END NEIGHBOURS OF THE AFFECTED NODES ===",
        ]
      : [
          `=== EVERY OTHER NODE (${args.total - args.shown} of ${args.total}; reference only) ===`,
          "Unchanged, and not shown in full: `<id> | <what it is> | <lean_kind> <lean_name> | <target_file>`.",
          ...args.index,
          "=== END EVERY OTHER NODE ===",
        ]),
    "",
    "=== BEYOND THE AFFECTED SET ===",
    "The affected set above was computed mechanically (the nodes the change names, the users of a changed",
    "assumption or definition, the subjects of a changed pinned reading, the blocks of a split statement).",
    "It can UNDER-REACH: a change that travels by meaning rather than by a cited id is not in it. Trace the",
    "change yourself, and when it reaches a node not shown in full — a hypothesis, a result a text cites",
    "(`Lemma~\\ref{<label>}`: the reference lines give each result's label), a definition — look that node up",
    "BY ID: search the file for `\"id\": \"<id>\"` (the plan: `\"<id>\":`) and read only that record;",
    "never read either file whole. A result a text names in words, with no label (\"the conditions of the",
    "continuity lemma\"), is found the same way: resolve it through the reference lines, then look it up.",
    "The symbol entries shown are those of the nodes to change; a symbol another shown node uses is under",
    "`symbols` in the typed core, by its `name`:",
    `  typed core (READ-ONLY): ${args.corePath}`,
    `  plan: ${args.planPath}`,
    `Then SAY SO: list every node you had to look up in ${args.replyField} (an empty list when the set sufficed).`,
    "=== END BEYOND THE AFFECTED SET ===",
    "",
  ].join("\n");
}

/** The ids a reply reports under `BEYOND_SCOPE_KEY` (a JSON field, or the same word in prose
 *  followed by a list); empty when it reports none. Pure. */
export function beyondScopeReported(reply: string): string[] {
  const m = new RegExp(`${BEYOND_SCOPE_KEY}"?\\s*[:=]?\\s*\\[([^\\]]*)\\]`).exec(reply);
  if (!m) return [];
  return [...new Set((m[1]!.match(/[A-Za-z]+:[A-Za-z0-9_.-]+|S[0-9]+/g) ?? []))];
}

/** The plan (as written) and the core view (`formalizationCoreContextValue`) a stage last carried
 *  through — what F1.5 passed, what F2 scaffolded. The next revise diffs against it. */
export interface ReviseBasis {
  plan: unknown;
  core: unknown;
}

export async function writeReviseBasis(file: string, basis: ReviseBasis): Promise<void> {
  await writeFile(file, JSON.stringify(basis), "utf8");
}

/** The recorded basis, or null (a run older than the record, or an unreadable file: the stage
 *  then keeps its whole-context prompt). */
export async function readReviseBasis(file: string): Promise<ReviseBasis | null> {
  if (!existsSync(file)) return null;
  try {
    const b = JSON.parse(await readFile(file, "utf8")) as ReviseBasis;
    return b && typeof b === "object" && b.plan && b.core ? b : null;
  } catch {
    return null;
  }
}
