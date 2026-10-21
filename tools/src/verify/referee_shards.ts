/**
 * The V1.5 referee (`stage_v1_5.ts`): every node read closely, in shards.
 *
 *   1. SHARDS. The nodes to grade (after the delta partition: a carried verdict is never re-graded)
 *      are split into shards sized by review cost (`ShardLimits`: a content budget and per-kind
 *      node ceilings), a statement's hypotheses and definitions travelling together where they fit. A shard call sees the whole core as compact read-only
 *      context (proofs only for its own nodes), the paper's setup, and the statement and proof of
 *      each of its nodes as they sit in `flat.tex` (`referee_slices.ts`) — not the whole paper — and
 *      grades them on the three axes.
 *   2. ONE GRADING. Every node is graded once, in one shard (user decision 2026-09-26).
 *   DEPENDENCY ORDER (`referee_levels.ts`). The nodes are graded level by level, leaves first:
 *      definitions and assumptions, then the statements using no statement still to grade, then
 *      those using only earlier levels, up to the root. Steps 1–2 run per level (its shards in
 *      parallel); a shard is shown the final verdicts of the statements its nodes use and judges
 *      under them — a node using a result graded `error` with no confirmed repair is `unclear`.
 *   THE CHAIN (`onGraded`). A carried verdict was given under the verdicts of the results its node
 *      uses, as shown to it. Once a level settles, each carried verdict using one of its results
 *      whose verdict now reads otherwise is RE-OPENED: its node joins the nodes to grade, at the
 *      level above, in this pass — and its own users after it, if its verdict moves too. So the
 *      levels are laid out again after each one (`nextLevel`), over the nodes still to grade.
 *   FIX AS YOU GO (`pauseOn`, `delta`; user decision 2026-09-24). After each level settles, the
 *      runner's `pauseOn` names the nodes that stop the upward grading (a refuting error with an
 *      in-scope witness, a repair that weakens the claim): the run returns `paused` with the
 *      verdicts so far and no global pass, and the stage hands exactly those to the fixer. The next
 *      pass grades the `delta` (the repaired nodes) FIRST, as its own
 *      levels graded the same way, and continues upward only once `pauseOn` stops none of
 *      it — so no result is graded over an unrepaired error; the errored-dependency rule stays as
 *      the fallback for an error nobody repairs.
 *   3. GLOBAL PASS, after the last level. One call with the whole paper and the shard verdicts decides only what spans
 *      nodes: wiring across the paper (`cross_node` kind "wiring" → drift with its fix), the
 *      key-result list (`patch_review`), the consistency of the patch set (kind
 *      "patch_consistency", on a patch part only → `unclear`, or `error` with a witness), and the
 *      fixer rejections. It never re-grades a node on its own axes.
 *
 * The runner then applies to the merged review the contract, verdict computation, routing, patch
 * confirmation, minimality and drift rules (`stage_v1_5.ts`).
 */
import type { Core } from "../core/schema.js";
import { mapLimit } from "../formalization/reviewer_verdicts.js";
import type { DriftFix } from "./directive_edits.js";
import { nodeExcerpts, paperIndex, setupExcerpt } from "./referee_slices.js";
import {
  GLOBAL_REPLY,
  GlobalReplySchema,
  SHARD_REPLY,
  ShardReplySchema,
  buildShardPrompt,
  globalScope,
  dependencyLine,
  isMalformedReply,
  section,
  type CrossNode,
  type ShardContext,
} from "./referee_shard_prompts.js";
import type { EnvsJson, FixerRejection, FlatTexLineMap, V15NodeVerdict, V15Review } from "./types.js";
import type { SymbolMetrics } from "./referee_symbols.js";
import type { SymbolReadings } from "./referee_shard_prompts.js";
import { dependencyVerdicts, gradedBelow, refereeLevels, refutes, settleOnErroredDependencies, type DependencyVerdict } from "./referee_levels.js";

export {
  GLOBAL_OUTPUT_BLOCK,
  GLOBAL_REPLY,
  SHARD_REPLY,
  UNRELATED_TEXT_MAX,
  buildShardPrompt,
  compactCore,
  dependencyLine,
  dependencyVerdictsSection,
  type CrossNode,
  type ShardContext,
  type SymbolReadings,
} from "./referee_shard_prompts.js";

/** Parallel referee calls unless `paperformalizer.json`
 * `referee.max_concurrent` says otherwise. */
export const SHARD_CONCURRENCY = 6;

// ---------------------------------------------------------------------------------------------
// Grouping
// ---------------------------------------------------------------------------------------------

/** Shard capacities: `ceil(n / max)` shards, sizes as equal as possible (for `max` 6: 4–6 for
 * n ≥ 8, a 7-node set 4 + 3, a set of at most 6 one shard). Used by the symbol shards
 * (`referee_symbols.ts`, `SYMBOL_SHARD_MAX`); node shards are sized by `ShardLimits`. */
export function shardCapacities(n: number, max: number): number[] {
  if (n <= 0) return [];
  const k = Math.ceil(n / max);
  return Array.from({ length: k }, (_, i) => Math.floor(n / k) + (i < n % k ? 1 : 0));
}

/**
 * How big a node shard may be. A shard is filled by a CONTENT BUDGET — the bytes of its nodes' paper
 * slices (statement + proof as printed) at most `bytes` — and a node-count ceiling per kind:
 * definitions and assumptions up to `hypotheses`, lemmas / propositions (any statement not a theorem
 * or corollary) up to `lemmas`, theorems and corollaries up to `theorems`. In a mixed shard each node
 * takes `1 / ceiling` of the room (so every per-kind ceiling holds). A node over the budget alone
 * gets a shard of its own.
 */
export interface ShardLimits {
  bytes: number;
  hypotheses: number;
  lemmas: number;
  theorems: number;
  /** A node's content bytes (`referee_slices.ts` excerpts); unknown → 0 (only the ceilings bind). */
  sizeOf: (id: string) => number;
}

/** `paperformalizer.json` `referee.shard_bytes` / `shard_max_hypotheses` / `shard_max_lemmas` /
 * `shard_max_theorems` defaults. */
export const DEFAULT_SHARD_LIMITS: Omit<ShardLimits, "sizeOf"> = { bytes: 70_000, hypotheses: 10, lemmas: 6, theorems: 3 };

const defaultLimits = (): ShardLimits => ({ ...DEFAULT_SHARD_LIMITS, sizeOf: () => 0 });

/** The node-count ceiling of a node's kind. */
export function kindCeiling(core: Core, id: string, lim: Omit<ShardLimits, "sizeOf" | "bytes">): number {
  const st = core.statements.find((s) => s.id === id);
  if (!st) return lim.hypotheses;
  return /^(theorem|corollary)$/i.test(String(st.kind ?? "")) || /^(thm|cor):/.test(id) ? lim.theorems : lim.lemmas;
}

const EPS = 1e-9;

/**
 * Split `toGrade` into shards within `limits`. Units first: each statement (core order) with the hypotheses and definitions it depends on directly that are still unassigned
 * (also for a statement not graded here, so what one result uses is read together); then every node
 * left over, alone. The number of shards starts at what the room and the budget need; each unit goes
 * whole into the emptiest shard it fits in (so sizes stay even), else a new shard; a unit no shard
 * can hold whole is placed as its longest prefix that fits (the statement first), then the rest; a
 * node over the budget sits alone.
 */
export function groupShards(core: Core, toGrade: readonly string[], limits: ShardLimits = defaultLimits()): string[][] {
  if (toGrade.length === 0) return [];
  const grade = new Set(toGrade);
  const assigned = new Set<string>();
  const units: string[][] = [];
  const statements = core.statements;
  const isStatement = new Set(core.statements.map((s) => s.id));
  for (const s of statements) {
    const unit = grade.has(s.id) ? [s.id] : [];
    if (grade.has(s.id)) assigned.add(s.id);
    for (const d of s.depends_on) {
      if (grade.has(d) && !assigned.has(d) && !isStatement.has(d)) {
        unit.push(d);
        assigned.add(d);
      }
    }
    if (unit.length > 0) units.push(unit);
  }
  for (const id of toGrade.filter((id) => !assigned.has(id))) units.push([id]);
  const load = (id: string): number => 1 / Math.max(1, kindCeiling(core, id, limits));
  const size = (id: string): number => Math.max(0, limits.sizeOf(id));
  const sum = (ids: readonly string[], f: (id: string) => number): number => ids.reduce((a, id) => a + f(id), 0);
  type Shard = { ids: string[]; load: number; bytes: number; solo: boolean };
  const k0 = Math.max(1, Math.ceil(sum(toGrade, load) - EPS), Math.ceil(sum(toGrade, size) / Math.max(1, limits.bytes) - EPS));
  const shards: Shard[] = Array.from({ length: k0 }, () => ({ ids: [], load: 0, bytes: 0, solo: false }));
  // Within the room and the budget; a single node over the budget only into an empty shard.
  const fits = (sh: Shard, n: number, l: number, b: number): boolean =>
    !sh.solo && sh.load + l <= 1 + EPS && (sh.bytes + b <= limits.bytes || (sh.ids.length === 0 && n === 1));
  const place = (ids: string[]): boolean => {
    const l = sum(ids, load);
    const b = sum(ids, size);
    let best: Shard | null = null;
    for (const sh of shards) if (fits(sh, ids.length, l, b) && (!best || sh.load < best.load - EPS || (Math.abs(sh.load - best.load) <= EPS && sh.bytes < best.bytes))) best = sh;
    if (!best) {
      if (l > 1 + EPS || (b > limits.bytes && ids.length > 1)) return false;
      best = { ids: [], load: 0, bytes: 0, solo: false };
      shards.push(best);
    }
    best.ids.push(...ids);
    best.load += l;
    best.bytes += b;
    // A node over the budget has its shard to itself.
    if (best.bytes > limits.bytes) best.solo = true;
    return true;
  };
  // A unit no shard can hold whole: its longest prefix that fits (the statement first), then the rest.
  const placeUnit = (unit: string[]): void => {
    for (let n = unit.length; n >= 1; n -= 1) {
      if (place(unit.slice(0, n))) {
        if (n < unit.length) placeUnit(unit.slice(n));
        return;
      }
    }
  };
  for (const unit of units) placeUnit(unit);
  return shards.map((sh) => sh.ids).filter((ids) => ids.length > 0);
}

/** Pack units into shards of the given capacities: each unit whole into the fullest shard it still
 * fits in (best fit); a unit no shard has room for is split over the roomiest shards, in order. */
export function packUnits(units: readonly string[][], caps: readonly number[]): string[][] {
  const shards: string[][] = caps.map(() => []);
  const room = [...caps];
  for (const unit of units) {
    // Best fit: the fullest shard the whole unit still fits in; none → split, into the roomiest.
    let whole = -1;
    for (let i = 0; i < room.length; i += 1) if (room[i]! >= unit.length && (whole === -1 || room[i]! < room[whole]!)) whole = i;
    if (whole !== -1) {
      shards[whole]!.push(...unit);
      room[whole]! -= unit.length;
      continue;
    }
    let rest = unit;
    while (rest.length > 0) {
      let best = 0;
      for (let i = 1; i < room.length; i += 1) if (room[i]! > room[best]!) best = i;
      const take = Math.min(rest.length, room[best]!);
      shards[best]!.push(...rest.slice(0, take));
      room[best]! -= take;
      rest = rest.slice(take);
    }
  }
  return shards.filter((s) => s.length > 0);
}

// ---------------------------------------------------------------------------------------------
// Degenerate witnesses
// ---------------------------------------------------------------------------------------------

/** Whether a grade is an `error` refuting the node (not a minimality or weakening grade on a repair). */
export const isRefutingError = refutes;

/**
 * A paper is not stopped for a case every competent reader excludes (owner decision 2026-09-24): an
 * `error` whose witness is `degenerate` (a trivial or identically-zero functional, zero variance, an
 * empty class, boundary equality in a strict inequality …) becomes a `bookkeeping` grade whose
 * condition is the exclusion the referee stated — an `ass:bk-*` on the statement on acceptance,
 * listed with the report's bookkeeping conditions, never an error of the paper, never the fixer's.
 * Every other grade is returned as it is.
 */
export function settleDegenerateWitness(n: V15NodeVerdict): V15NodeVerdict {
  if (!isRefutingError(n) || n.witness_regime !== "degenerate" || !n.bookkeeping_assumption) return n;
  const { minimality: _m, weakens_contribution: _w, ...rest } = n;
  return {
    ...rest,
    correctness: "bookkeeping",
    bookkeeping_assumption: {
      condition: n.bookkeeping_assumption.condition,
      reason: `excludes a degenerate case the paper's setting implicitly rules out (witness: ${(n.witness_instance ?? n.witness ?? "").replace(/\s+/g, " ").trim()})`,
    },
    witness: null,
    detail: `[degenerate witness — recorded as a bookkeeping exclusion, not an error] ${n.detail}${n.witness ? ` (witness: ${n.witness})` : ""}`,
  };
}

// ---------------------------------------------------------------------------------------------
// Merging the global pass
// ---------------------------------------------------------------------------------------------

/** Two fixes on one node as one, field by field: the id lists united; of a single-valued field the
 * one that is set (a reply carries every key, most of them null: a null never replaces a value); the
 * two settings joined. Two DIFFERENT values of `extend_to` or `new_assumption` cannot both be applied
 * by the runner: the first stays the mechanical edit and the second goes to the transcriber as prose
 * (`also`) — never dropped. Exported for tests. */
export function mergeFix(a: DriftFix | null | undefined, b: DriftFix | null | undefined): DriftFix | null {
  if (!a) return b ?? null;
  if (!b) return a;
  const union = (x?: string[] | null, y?: string[] | null): string[] | null => (x?.length || y?.length ? [...new Set([...(x ?? []), ...(y ?? [])])] : null);
  const unmerged: string[] = [];
  const one = <K extends "extend_to" | "new_assumption">(k: K): DriftFix[K] => {
    if (a[k] != null && b[k] != null && JSON.stringify(a[k]) !== JSON.stringify(b[k])) unmerged.push(`${k}: ${JSON.stringify(b[k])}`);
    return a[k] ?? b[k] ?? null;
  };
  const prose = (x?: string | null, y?: string | null): string | null => [...new Set([x, y].filter((t): t is string => !!t?.trim()))].join("\n") || null;
  const fix: DriftFix = {
    add_depends_on: union(a.add_depends_on, b.add_depends_on),
    remove_depends_on: union(a.remove_depends_on, b.remove_depends_on),
    wire_into: union(a.wire_into, b.wire_into),
    unwire_from: union(a.unwire_from, b.unwire_from),
    extend_to: one("extend_to"),
    new_assumption: one("new_assumption"),
    setting: prose(a.setting, b.setting),
  };
  const also = prose(prose(a.also, b.also), unmerged.length > 0 ? `A second structural edit asked for this node, which the runner cannot merge with the first — make it yourself: ${unmerged.join("; ")}` : null);
  return also ? { ...fix, also } : fix;
}

/** Apply the global pass's cross-node entries to the shard verdicts. The pass owns wiring and the
 * consistency of the patch set only: a "wiring" entry makes the node drift (its fix merged); a
 * "patch_consistency" entry can only lower a patch part's correctness (`unclear`, or `error` with
 * a witness). Nothing else of a node's grade is the global pass's. */
export function applyCrossNode(nodes: V15NodeVerdict[], entries: readonly CrossNode[]): V15NodeVerdict[] {
  const byId = new Map<string, V15NodeVerdict>(nodes.map((n) => [n.id, { ...n }]));
  for (const e of entries) {
    const n = byId.get(e.id);
    if (!n) continue;
    if (e.kind === "wiring") {
      n.faithfulness = "drift";
      n.detail = `${n.detail}${n.detail ? " " : ""}[global pass, wiring] ${e.detail}`;
      n.fix = mergeFix(n.fix, e.fix);
    } else {
      n.detail = `${n.detail}${n.detail ? " " : ""}[global pass, patch consistency] ${e.detail}`;
      if (e.witness && e.witness.trim()) {
        if (n.correctness !== "error") {
          n.minimality = false;
          n.weakens_contribution = false;
        }
        n.witness = n.correctness === "error" && n.witness ? `${n.witness} | ${e.witness}` : e.witness;
        n.correctness = "error";
        n.bookkeeping_assumption = null;
      } else if (n.correctness === "ok" || n.correctness === "bookkeeping") {
        n.correctness = "unclear";
        n.bookkeeping_assumption = null;
      }
    }
  }
  return nodes.map((n) => byId.get(n.id)!);
}

// ---------------------------------------------------------------------------------------------
// The run
// ---------------------------------------------------------------------------------------------

export interface RefereeCall {
  tag: string;
  /** The symbol referee's calls (`referee_symbols.ts`) carry the symbol names in `nodes`. */
  kind: "shard" | "global" | "symbol_shard";
  prompt: string;
  schema: Record<string, unknown>;
  nodes: string[];
  /** Codex reasoning effort of this call (default "high"; the symbol referee's calls carry
   *  `referee.symbol_effort`). */
  effort?: "low" | "medium" | "high";
}

export interface RefereeCallMetric {
  tag: string;
  kind: RefereeCall["kind"];
  bytes: number;
  ms: number;
  nodes: number;
}

/** One level of the dependency order: its nodes, shards, calls, prompt bytes and wall time. */
export interface LevelMetrics {
  level: number;
  nodes: string[];
  shards: string[][];
  /** Content bytes (statement + proof excerpts) of each shard. */
  content_bytes: number[];
  /** Shard calls of this level (retries included). */
  calls: number;
  bytes: number;
  /** Nodes graded `unclear` because a statement they use is graded `error` (`referee_levels.ts`). */
  dependency_unclear: string[];
  wall_ms: number;
  /** A level of the DELTA confirmation (the repaired nodes of the last fixer round, graded first). */
  delta?: boolean;
  /** The nodes of this level that stopped the upward grading (`pauseOn`). */
  paused?: string[];
}

export interface ShardMetrics {
  /** Every level's shards, level after level (per level: `levels`). */
  shards: string[][];
  /** The dependency order, leaves first (`referee_levels.ts`). */
  levels: LevelMetrics[];
  /** Dependency cycles among the statements graded, each graded as one level. */
  cycles: string[][];
  calls: RefereeCallMetric[];
  shard_bytes: number;
  global_bytes: number;
  total_bytes: number;
  wall_ms: number;
  /** The symbol referee's pass, which ran first (`referee_symbols.ts`). */
  symbols?: SymbolMetrics;
  /** Nodes whose grading broke the contract past its retry:
   * set aside, their verdict on file kept (or none), graded afresh next pass. */
  set_aside?: Array<{ id: string; why: string }>;
}

export interface ShardedRefereeInput {
  core: Core;
  flatTex: string;
  envs: EnvsJson | null;
  lineMap: FlatTexLineMap | null;
  toGrade: string[];
  totalNodes: number;
  scope: string;
  /** `review.txt`, `shard.txt`. */
  briefs: { base: string; shard: string };
  extraSections: (ids: readonly string[]) => string[];
  /** The global pass's prompt, given the shard verdicts (fresh + carried) and, on a delta pass (some
   * verdict carried), the nodes it is shown (`globalScope`) and, of those, the ones it checks — shown
   * in full; the rest are carried neighbours, shown by text and verdict; `null` = every node, in full. */
  globalPrompt: (verdicts: V15NodeVerdict[], scope: { shown: ReadonlySet<string>; full: ReadonlySet<string> } | null) => string;
  /** The patch file's key results: always in a delta global pass's scope. */
  keyResults?: readonly string[];
  carried: V15NodeVerdict[];
  isPatchPart: (id: string) => boolean;
  hasPatches: boolean;
  rejections: readonly FixerRejection[];
  /** Contract check of a (partial) review against the nodes it owes (`stage_v1_5.ts`). */
  contract: (review: V15Review, owes: ReadonlySet<string>, opts: { patches: boolean; rejections: readonly FixerRejection[] }) => string[] | Promise<string[]>;
  /** The TeX check of texts the pass writes outside a node grade (the global pass's cross-node
   * details, which join the node's detail): one violation per text that does not compile. */
  texCheck?: (fields: Array<{ where: string; text: string }>) => Promise<string[]>;
  /** One referee call; returns the parsed JSON reply. */
  ask: (call: RefereeCall) => Promise<unknown>;
  log: (msg: string) => void;
  knownIds: ReadonlySet<string>;
  /** The symbol referee's readings, shown to every shard under PINNED READINGS. */
  symbols?: SymbolReadings;
  /** Parallel referee calls (`paperformalizer.json` `referee.max_concurrent`; default `SHARD_CONCURRENCY`). */
  concurrency?: number;
  /** Shard sizes (`paperformalizer.json` `referee.shard_bytes`, `shard_max_*`; default
   * `DEFAULT_SHARD_LIMITS`); a node's content bytes are its excerpts'. */
  limits?: Omit<ShardLimits, "sizeOf">;
  /** A repair of a statement on file (its core text is the corrected form) and what the printed
   * statement got wrong: shown with the statement's verdict to the results using it. */
  repairOf?: (id: string) => DependencyVerdict["repair"];
  /** FIX AS YOU GO: the nodes of a settled level (its final verdicts) that stop the upward grading.
   * Unset or empty → the grading goes on (the errored-dependency rule then covers the rest). */
  pauseOn?: (verdicts: readonly V15NodeVerdict[], at: { delta: boolean }) => string[];
  /** The repaired nodes of the last fixer round: graded first, as their
   * own levels (tags `fix-L<k>-…`), before any other node. A node using a statement still to grade
   * outside the delta is graded at its own level instead. */
  delta?: readonly string[];
  /** Called once the delta has settled, with the final verdicts so far and the nodes it stopped. */
  onDelta?: (final: ReadonlyMap<string, V15NodeVerdict>, stopped: readonly string[]) => void;
  /** The owner's rulings on a level's settled grades (a withdrawn finding overruled, an accepted
   * weakening honoured), applied before the errored-dependency rule and before the level's verdicts
   * are final — so the levels above, their prompts and the pause rule see the ruled grade. */
  settle?: (verdicts: V15NodeVerdict[]) => V15NodeVerdict[];
  /** Carried nodes graded earlier in the same logical pass (a paused pass since the last complete
   * one, `LevelPause.graded`): the global pass checks them as it checks this pass's grades, and its
   * wiring / patch-consistency entries amend their verdicts. */
  amendable?: ReadonlySet<string>;
  /** The verdicts on file of the nodes to grade: a node set aside past its retry keeps its own as
   * context for the levels above and the global pass (the runner persists it unconfirmed). */
  prior?: ReadonlyMap<string, V15NodeVerdict>;
  /** THE CHAIN. Called once the verdicts of a level (`graded`: its nodes with a grade of this pass)
   * are final, with every final verdict so far — what each was shown of the results it uses. Returns
   * the CARRIED nodes whose verdict was given under a line that no longer reads the same: each is
   * graded in this pass, at a level above. Also called for the part of a level graded before a halt
   * (its return ignored: the pass is over). */
  onGraded?: (final: ReadonlyMap<string, V15NodeVerdict>, graded: readonly string[]) => string[];
  /** A pass that halts (a contract failure, a failed call, any error) hands on what it graded first:
   * every node of a finished level, and each node of the level in progress already graded — ruled and
   * settled on its errored dependencies as a finished level's are. Awaited before the halt is returned or rethrown. */
  onHalt?: (graded: V15NodeVerdict[], at: string) => Promise<void>;
}

/** Where a paused grading stopped: the level (its tag) and the nodes `pauseOn` named. */
export interface ShardedPause {
  level: number;
  tag: string;
  delta: boolean;
  ids: string[];
  /** Nodes to grade not yet graded (above the pause). */
  ungraded: string[];
}

export type ShardedResult =
  | { ok: true; review: V15Review; metrics: ShardMetrics; paused?: ShardedPause }
  | { ok: false; message: string; metrics: ShardMetrics };

class ContractFailure extends Error {}

const bytesOf = (s: string): number => Buffer.byteLength(s, "utf8");

/** Run the sharded referee: level by level (leaves first), each level's shards in parallel; after
 * the last level, the global pass. */
export async function runShardedReferee(inp: ShardedRefereeInput): Promise<ShardedResult> {
  const t0 = Date.now();
  const concurrency = Math.max(1, inp.concurrency ?? SHARD_CONCURRENCY);
  // The nodes to grade and the verdicts carried, as the pass stands: a carried verdict the chain
  // re-opens (`onGraded`) moves from the second to the first.
  const toGrade = [...inp.toGrade];
  let carried = [...inp.carried];
  const reopenedPrior = new Map<string, V15NodeVerdict>();
  const whole = refereeLevels(inp.core, toGrade);
  const metrics: ShardMetrics = {
    shards: [],
    levels: [],
    cycles: whole.cycles,
    calls: [],
    shard_bytes: 0,
    global_bytes: 0,
    total_bytes: 0,
    set_aside: [],
    wall_ms: 0,
  };
  for (const c of whole.cycles) inp.log(`dependency cycle among the statements to grade (graded as one level): ${c.join(", ")}`);
  // The final verdicts so far: carried ones, then each level's as it settles.
  const final = new Map<string, V15NodeVerdict>(inp.carried.map((v) => [v.id, v] as const));
  const depsOf = (id: string): DependencyVerdict[] => dependencyVerdicts(inp.core, id, final, inp.repairOf);
  const px = paperIndex(inp.flatTex, inp.lineMap, inp.envs);
  const sizes = new Map<string, number>();
  const sizeOf = (id: string): number => {
    if (!sizes.has(id)) {
      const ex = nodeExcerpts(px, inp.core, id);
      sizes.set(id, bytesOf(ex.statement.text) + bytesOf(ex.proof?.text ?? ""));
    }
    return sizes.get(id)!;
  };
  const limits: ShardLimits = { ...DEFAULT_SHARD_LIMITS, ...(inp.limits ?? {}), sizeOf };
  const ctx: ShardContext = {
    core: inp.core,
    px,
    setup: setupExcerpt(px),
    extraSections: inp.extraSections,
    totalNodes: inp.totalNodes,
    scope: inp.scope,
    dependencies: depsOf,
    ...(inp.symbols ? { symbols: inp.symbols } : {}),
  };
  const retrySection = (v: string[]): string =>
    section(
      "CONTRACT VIOLATIONS IN YOUR PREVIOUS REPLY",
      "Your previous reply broke the output contract. Re-review and emit a corrected JSON object; every point below must be fixed.\n\n" +
        v.map((x) => `- ${x}`).join("\n"),
    );

  /** The nodes with a final grade of this pass (a re-opened one only once it is graded again). */
  const graded = new Set<string>();
  // ONE NODE NEVER HALTS THE PASS: a node whose grading still breaks the contract after the retry
  // is set aside — its verdict on file kept as context (or none), never confirmed, so the next pass
  // grades it afresh — and logged; the other nodes' grades stand.
  const setAside = new Map<string, string>();
  const putAside = (id: string, why: string): void => {
    if (setAside.has(id)) return;
    setAside.set(id, why);
    metrics.set_aside!.push({ id, why });
    const pv = inp.prior?.get(id) ?? reopenedPrior.get(id);
    if (pv) final.set(id, { ...pv, graded: "carried" });
    inp.log(`node ${id}: its grading broke the output contract twice — set aside (${pv ? "its verdict on file kept, not confirmed" : "no verdict on file: left ungraded"}; graded afresh next pass): ${why}`);
  };
  const live = (ids: readonly string[]): string[] => ids.filter((id) => !setAside.has(id));
  /** The level in progress: its tag, nodes and the verdicts graded so far. */
  let current: { tag: string; ids: string[]; fresh: Map<string, V15NodeVerdict> } | null = null;
  /** What a halted pass graded (`onHalt`). */
  const haltedGrades = (): V15NodeVerdict[] => {
    const out = live(toGrade).filter((id) => graded.has(id)).map((id) => final.get(id)!);
    if (!current) return out;
    const settled: V15NodeVerdict[] = [];
    for (const id of live(current.ids)) {
      const done = current.fresh.get(id);
      if (!graded.has(id) && done) settled.push(done);
    }
    const part = (inp.settle ? inp.settle(settled) : settled).map((v) => settleOnErroredDependencies(v, depsOf(v.id)).verdict);
    // … each on the basis of what it was shown (the chain's bookkeeping; nothing is re-opened now).
    inp.onGraded?.(new Map([...final, ...part.map((v) => [v.id, v] as const)]), part.map((v) => v.id));
    return [...out, ...part];
  };

  /** One call with one retry on a contract violation; the retry shows the violations.
   * Past the retry, `salvage` keeps what complies (none: the
   * pass fails). A reply that is no JSON or fails the reply schema is a contract violation like
   * any other (`isMalformedReply`): retried once; past the retry `salvage` sees no reply (null). */
  const call = async <T>(c: RefereeCall, parse: (raw: unknown) => T, check: (r: T) => string[] | Promise<string[]>, salvage?: (r: T | null) => Promise<T>): Promise<T> => {
    let prompt = c.prompt;
    for (let attempt = 1; attempt <= 2; attempt += 1) {
      const tag = attempt === 1 ? c.tag : `${c.tag}_retry`;
      const t = Date.now();
      let recorded = false;
      const record = (): void => {
        if (recorded) return;
        recorded = true;
        const m: RefereeCallMetric = { tag, kind: c.kind, bytes: bytesOf(prompt), ms: Date.now() - t, nodes: c.nodes.length };
        metrics.calls.push(m);
        if (c.kind === "shard") metrics.shard_bytes += m.bytes;
        else metrics.global_bytes += m.bytes;
      };
      let r: T | null = null;
      let v: string[];
      try {
        const raw = await inp.ask({ ...c, tag, prompt });
        record();
        r = parse(raw);
        v = await check(r);
      } catch (err) {
        const why = isMalformedReply(err);
        if (why === null) throw err;
        record();
        r = null;
        v = [why];
      }
      if (v.length === 0) return r!;
      inp.log(`referee ${tag}: contract violations${attempt === 1 ? ", retrying once" : " survived the retry"}: ${v.join(" ")}`);
      if (attempt === 2) {
        if (salvage) return salvage(r);
        throw new ContractFailure(`referee ${c.tag} broke the output contract twice: ${v.join(" ")}`);
      }
      prompt = `${c.prompt}\n\n${retrySection(v)}`;
    }
    throw new Error("unreachable");
  };

  const done = (): void => {
    metrics.total_bytes = metrics.shard_bytes + metrics.global_bytes;
    metrics.wall_ms = Date.now() - t0;
  };

  /** Grade one level: its shards, in parallel. `lt`: the level's tag
   * (`L<k>`, or `fix-L<k>` for a level of the delta confirmation). */
  const gradeLevel = async (level: number, ids: string[], lt = `L${level}`, delta = false): Promise<void> => {
    const lt0 = Date.now();
    const callsBefore = metrics.calls.length;
    // Bounded by content bytes and per-kind counts (`groupShards`): the fixed context is sent once per shard.
    const plan = groupShards(inp.core, ids, limits);
    metrics.shards.push(...plan);
    const jobs = plan.map((ids, i) => ({ tag: `${lt}-${i + 1}`, ids }));
    for (const j of jobs) inp.log(`shard ${j.tag}: ${j.ids.join(", ")}`);
    const fresh = new Map<string, V15NodeVerdict>();
    current = { tag: lt, ids, fresh };
    // A failing shard does not cut its siblings short (`mapLimit` cancels nothing): every shard of
    // the level runs to its end and records its grades, then the first failure is rethrown — so a
    // halt hands on all the level graded (`onHalt`), not only what finished before the failure.
    /** One shard's reply: its grades on its own nodes, checked and, past the retry, salvaged. */
    const gradeShard = (j: { tag: string; ids: string[] }): Promise<{ summary: string; nodes: V15NodeVerdict[] }> => {
      const own = new Set(j.ids);
      return call(
        { tag: `shard_${j.tag}`, kind: "shard", prompt: buildShardPrompt(ctx, inp.briefs.base, inp.briefs.shard, j.ids), schema: SHARD_REPLY, nodes: j.ids },
        (raw) => {
          const r = ShardReplySchema.parse(raw);
          // A grade on a node outside this shard is not asked for; an unknown id stays, for the contract.
          const extra = r.nodes.filter((n) => inp.knownIds.has(n.id) && !own.has(n.id)).map((n) => n.id);
          if (extra.length > 0) inp.log(`shard ${j.tag} also graded ${extra.length} node(s) outside it; ignored: ${extra.join(", ")}`);
          return { ...r, nodes: r.nodes.filter((n) => !extra.includes(n.id)) as V15NodeVerdict[] };
        },
        (r) => inp.contract({ verdict: "PASS", summary: r.summary, nodes: r.nodes }, own, { patches: false, rejections: [] }),
        // Past the retry: each owned grade checked on its own; a noncompliant, repeated or missing one
        // is set aside (a reply that did not parse: every node of the shard). What is left must
        // comply as a whole, or the shard's reply is unusable.
        async (r) => {
          if (r === null) {
            for (const id of own) putAside(id, `referee shard_${j.tag}: its reply did not parse twice.`);
            return { summary: "", nodes: [] };
          }
          const count = new Map<string, number>();
          for (const n of r.nodes) count.set(n.id, (count.get(n.id) ?? 0) + 1);
          const bad = new Map<string, string>();
          for (const n of r.nodes) {
            if (!own.has(n.id) || bad.has(n.id)) continue;
            if (count.get(n.id)! > 1) bad.set(n.id, `node "${n.id}" is graded more than once.`);
            else {
              const p = await inp.contract({ verdict: "PASS", summary: r.summary, nodes: [n] }, new Set([n.id]), { patches: false, rejections: [] });
              if (p.length > 0) bad.set(n.id, p.join(" "));
            }
          }
          for (const id of own) if (!count.has(id)) bad.set(id, `node "${id}" carries no verdict.`);
          const kept = r.nodes.filter((n) => own.has(n.id) && !bad.has(n.id));
          const rest = await inp.contract({ verdict: "PASS", summary: r.summary, nodes: kept }, new Set([...own].filter((id) => !bad.has(id))), { patches: false, rejections: [] });
          if (rest.length > 0) throw new ContractFailure(`referee shard_${j.tag} broke the output contract twice: ${rest.join(" ")}`);
          for (const [id, why] of bad) putAside(id, `referee shard_${j.tag}: ${why}`);
          return { ...r, nodes: kept };
        },
      );
    };
    const failures: unknown[] = [];
    await mapLimit(jobs, concurrency, async (j) => {
      let reply: { summary: string; nodes: V15NodeVerdict[] };
      try {
        reply = await gradeShard(j);
      } catch (err) {
        failures.push(err);
        return;
      }
      for (const raw of reply.nodes) fresh.set(raw.id, { ...settleDegenerateWitness(raw), shards: [j.tag] });
    });
    if (failures.length > 0) throw failures[0];

    // THE OWNER'S RULINGS, then THE RULE ON AN ERRORED DEPENDENCY; then the level's verdicts are final.
    const settled = live(ids).filter((id) => fresh.has(id));
    if (inp.settle) for (const v of inp.settle(settled.map((id) => fresh.get(id)!))) fresh.set(v.id, v);
    const dependencyUnclear: string[] = [];
    for (const id of settled) {
      const deps = depsOf(id);
      const { verdict, on } = settleOnErroredDependencies(fresh.get(id)!, deps);
      if (on.length > 0) {
        dependencyUnclear.push(id);
        inp.log(`${id}: unclear — depends on ${on.join(", ")}, graded error (${deps.filter((d) => on.includes(d.id)).map(dependencyLine).join(" | ")})`);
      }
      fresh.set(id, verdict);
    }
    for (const id of settled) (final.set(id, fresh.get(id)!), graded.add(id));
    // (The contract owes every node of a shard a grade; one left with neither a grade nor set aside
    // would be laid out again forever.)
    const lost = live(ids).filter((id) => !graded.has(id));
    if (lost.length > 0) throw new Error(`referee level ${lt}: no grade for ${lost.join(", ")}`);
    current = null;
    // THE CHAIN: the carried verdicts given under a line of these results that no longer reads the same.
    const carriedBy = new Map(carried.map((v) => [v.id, v] as const));
    const reopened = (inp.onGraded?.(final, settled) ?? []).filter((id) => carriedBy.has(id));
    for (const id of reopened) {
      reopenedPrior.set(id, carriedBy.get(id)!);
      toGrade.push(id);
    }
    if (reopened.length > 0) carried = carried.filter((v) => !reopenedPrior.has(v.id));
    const levelCalls = metrics.calls.slice(callsBefore);
    metrics.levels.push({
      level,
      nodes: ids,
      shards: plan,
      content_bytes: plan.map((sh) => sh.reduce((a, id) => a + sizeOf(id), 0)),
      calls: levelCalls.length,
      bytes: levelCalls.reduce((a, c) => a + c.bytes, 0),
      dependency_unclear: dependencyUnclear,
      wall_ms: Date.now() - lt0,
      ...(delta ? { delta: true } : {}),
    });
    inp.log(`level ${lt} graded: ${ids.length} node(s), ${plan.length} shard(s), ${levelCalls.length} call(s) in all, ${Math.round((Date.now() - lt0) / 1000)}s`);
  };

  /** The nodes of a settled level that stop the upward grading (recorded on its metrics). */
  const answered = new Set(inp.delta ?? []);
  const stopsAt = (all: readonly string[], delta: boolean): string[] => {
    // A node set aside has no grade of this pass: it stops nothing.
    const ids = live(all);
    // A node of the delta is judged as one wherever it is graded (a repair graded at its own level
    // because it uses a statement still to grade outside the delta included).
    const [inDelta, rest] = delta ? [ids, []] : [ids.filter((id) => answered.has(id)), ids.filter((id) => !answered.has(id))];
    const ask = (xs: readonly string[], d: boolean): string[] => (inp.pauseOn && xs.length > 0 ? inp.pauseOn(xs.map((id) => final.get(id)!), { delta: d }) : []);
    const stopped = [...ask(inDelta, true), ...ask(rest, false)];
    if (stopped.length > 0) metrics.levels.at(-1)!.paused = [...stopped];
    return stopped;
  };
  const pausedResult = (level: number, tag: string, delta: boolean, ids: string[]): ShardedResult => {
    done();
    const gradedIds = live(toGrade).filter((id) => graded.has(id));
    const ungraded = live(toGrade).filter((id) => !graded.has(id));
    inp.log(`level ${tag}: ${ids.length} node(s) stop the upward grading (${ids.join(", ")}) — paused for the fixer; ${ungraded.length} node(s) above wait, no global pass yet`);
    return {
      ok: true,
      metrics,
      paused: { level, tag, delta, ids, ungraded },
      review: {
        verdict: "FAIL",
        summary: `[sharded, paused at level ${tag}: ${ids.join(", ")} stop the upward grading; ${gradedIds.length} node(s) graded, ${ungraded.length} wait]`,
        nodes: gradedIds.map((id) => final.get(id)!),
        patch_review: null,
        rejection_verdicts: null,
      },
    };
  };

  try {
    // 0. THE DELTA CONFIRMATION: the repaired nodes of the last fixer round, first. A node using a
    // statement still to grade outside the delta waits for its own level.
    const deltaSet = new Set((inp.delta ?? []).filter((id) => toGrade.includes(id)));
    /** The delta still to grade: without the nodes that rest on a statement still to grade outside
     * it (`gradedBelow`; one the chain re-opened since included) — those wait for their own level. */
    const deltaLeft = (): string[] => {
      const below = gradedBelow(inp.core, new Set(toGrade.filter((id) => !graded.has(id))));
      for (let changed = true; changed; ) {
        changed = false;
        for (const id of [...deltaSet]) {
          if ((below.get(id) ?? []).some((d) => d !== id && !deltaSet.has(d))) {
            deltaSet.delete(id);
            changed = true;
          }
        }
      }
      return toGrade.filter((id) => deltaSet.has(id) && !graded.has(id) && !setAside.has(id));
    };
    /** The lowest level of `ids` (the nodes still to grade, laid out afresh: the chain may have added
     * some), numbered past the last level graded so that level numbers only rise. */
    const nextLevel = (ids: readonly string[], last: number): { level: number; ids: string[] } | null => {
      const levels = refereeLevels(inp.core, ids).levels;
      const at = levels.findIndex((l) => l.length > 0);
      return at < 0 ? null : { level: Math.max(at, last + 1), ids: levels[at]! };
    };
    const deltaIds = deltaLeft();
    let stopped: string[] = [];
    let at = { level: 0, tag: "fix-L0" };
    if (deltaIds.length > 0) {
      inp.log(`delta confirmation first: ${deltaIds.length} repaired node(s) (${deltaIds.join(", ")})`);
      for (let next = nextLevel(deltaIds, -1); next; next = nextLevel(deltaLeft(), next.level)) {
        await gradeLevel(next.level, next.ids, `fix-L${next.level}`, true);
        stopped = stopsAt(next.ids, true);
        at = { level: next.level, tag: `fix-L${next.level}` };
        if (stopped.length > 0) break;
      }
    }
    if (inp.delta) inp.onDelta?.(final, stopped);
    if (stopped.length > 0) return pausedResult(at.level, at.tag, true, stopped);
    // 1–2. LEVEL BY LEVEL, leaves first; a level with a node `pauseOn` names stops the grading.
    const left = (): string[] => toGrade.filter((id) => !graded.has(id) && !setAside.has(id));
    for (let next = nextLevel(left(), -1); next; next = nextLevel(left(), next.level)) {
      await gradeLevel(next.level, next.ids);
      const stopped = stopsAt(next.ids, false);
      if (stopped.length > 0) return pausedResult(next.level, `L${next.level}`, false, stopped);
    }
    const shardNodes = live(toGrade).map((id) => final.get(id)!);
    // A node set aside is shown with its verdict on file (as carried); the global pass never amends it.
    const keptAside = [...setAside.keys()].flatMap((id) => (final.has(id) ? [final.get(id)!] : []));

    // 3. GLOBAL PASS — cross-node items only, after the last level. It checks every node graded in
    // this logical pass: this pass's grades and those a paused pass before it gave (`amendable`,
    // shown without the `carried` mark); a verdict from an earlier COMPLETE pass is not re-opened.
    const amendable = carried.filter((v) => inp.amendable?.has(v.id));
    const grading = new Set([...live(toGrade), ...amendable.map((v) => v.id)]);
    // A delta pass (some verdict carried) checks only the nodes graded in this logical pass and their
    // neighbours (`globalScope`): every other node was checked by an earlier global pass on unchanged
    // text, and a carried verdict is never re-opened.
    // Of those, the nodes in focus carry their full material (record, excerpts, patches, sources); a
    // carried neighbour or key result only its text, wiring and verdict line.
    const focus = [...grading, ...keptAside.map((v) => v.id), ...inp.rejections.map((r) => r.node)];
    const scope = carried.length > 0 ? globalScope(inp.core, focus, inp.keyResults) : null;
    const shownCarried = carried
      .filter((v) => !scope || scope.has(v.id))
      .map((v) => (inp.amendable?.has(v.id) ? { ...v, graded: undefined } : v));
    if (scope) inp.log(`global pass: delta scope — ${scope.size} of ${inp.totalNodes} node(s) shown (${new Set(focus).size} in full: graded this pass, the fixer rejections; their neighbours and the key results by text and verdict)`);
    const global = await call(
      { tag: "global", kind: "global", prompt: inp.globalPrompt([...shardNodes, ...keptAside, ...shownCarried], scope ? { shown: scope, full: new Set(focus) } : null), schema: GLOBAL_REPLY, nodes: [] },
      (raw) => GlobalReplySchema.parse(raw),
      async (r) => {
        const v = await inp.contract(
          { verdict: r.verdict, summary: r.summary, nodes: [], patch_review: r.patch_review ?? null, rejection_verdicts: r.rejection_verdicts ?? null },
          new Set(),
          { patches: inp.hasPatches, rejections: inp.rejections },
        );
        if (inp.texCheck) v.push(...(await inp.texCheck(r.cross_node.map((e) => ({ where: `cross_node on "${e.id}": its detail`, text: e.detail })))));
        for (const e of r.cross_node) {
          if (!inp.knownIds.has(e.id)) v.push(`cross_node names "${e.id}", which is not a node of the core.`);
          else if (e.kind === "patch_consistency" && !inp.isPatchPart(e.id)) {
            v.push(`cross_node "patch_consistency" on "${e.id}", which is not a patched node — that kind sits only on a repaired node.`);
          }
        }
        return v;
      },
    );
    const onCarried = global.cross_node.filter((e) => !grading.has(e.id));
    if (onCarried.length > 0) inp.log(`global pass named ${onCarried.length} carried node(s); a carried verdict is not re-opened: ${onCarried.map((e) => e.id).join(", ")}`);
    const onAmendable = new Set(global.cross_node.filter((e) => inp.amendable?.has(e.id) && !toGrade.includes(e.id)).map((e) => e.id));
    if (onAmendable.size > 0) inp.log(`global pass amends ${onAmendable.size} verdict(s) graded before this logical pass's pause: ${[...onAmendable].join(", ")}`);
    // An amended verdict of a paused pass joins this pass's grades (the runner re-records its basis).
    const nodes = applyCrossNode([...shardNodes, ...amendable.filter((v) => onAmendable.has(v.id))], global.cross_node.filter((e) => grading.has(e.id)));
    done();
    return {
      ok: true,
      metrics,
      review: {
        verdict: global.verdict,
        summary: `${global.summary} [sharded: ${levelsText(metrics)}; ${metrics.shards.length} shard(s), ${global.cross_node.length} cross-node item(s)]`,
        nodes,
        patch_review: global.patch_review ?? null,
        rejection_verdicts: global.rejection_verdicts ?? null,
      },
    };
  } catch (err) {
    done();
    if (inp.onHalt) await inp.onHalt(haltedGrades(), (current as { tag: string } | null)?.tag ?? "the global pass");
    if (err instanceof ContractFailure) return { ok: false, message: err.message, metrics };
    throw err;
  }
}

/** The dependency order in words: `levels: L0 3 · L1 2 · L2 1` (nodes graded per level). */
export function levelsText(m: Pick<ShardMetrics, "levels" | "cycles">, opts: { plan?: boolean } = {}): string {
  const kb = (b: number): string => `${Math.round(b / 1000)} KB`;
  const plan = (l: LevelMetrics): string =>
    ` (${l.shards.length} shard(s) ${l.shards.map((s) => s.length).join("+")} nodes, ${kb(l.content_bytes.reduce((a, b) => a + b, 0))} content)`;
  const body = m.levels.map((l) => `L${l.level} ${l.nodes.length}${opts.plan ? plan(l) : ""}`).join(" · ") || "none";
  return `levels: ${body}${m.cycles.length ? ` (${m.cycles.length} dependency cycle(s), each one level)` : ""}`;
}

/** The cost/size line: shards, nodes per shard, prompt bytes. */
export function shardLogLine(m: ShardMetrics): string {
  const sizes = (g: string[][]): string => g.map((s) => s.length).join("+") || "0";
  const kb = (b: number): string => `${Math.round(b / 1000)} KB`;
  return (
    `sharded referee: ${levelsText(m, { plan: true })}; ${m.shards.length} shard(s) (${sizes(m.shards)} nodes), 1 global pass; prompt bytes ${kb(m.total_bytes)} total ` +
    `(shards ${kb(m.shard_bytes)}, global ${kb(m.global_bytes)}); ${m.calls.length} call(s) in ${Math.round(m.wall_ms / 1000)}s` +
    (m.set_aside?.length ? `; ${m.set_aside.length} node(s) set aside past the retry (${m.set_aside.map((x) => x.id).join(", ")})` : "") +
    (m.symbols ? `; ${symbolLogPart(m.symbols)}` : "")
  );
}

/** The symbol pass in words: symbols graded / carried, shard sizes, prompt bytes and calls (the `sharded referee:` line's tail, and the
 * `symbol referee:` line). */
export function symbolLogBody(m: SymbolMetrics): string {
  const sizes = (g: string[][]): string => g.map((s) => s.length).join("+") || "0";
  const kb = (b: number): string => `${Math.round(b / 1000)} KB`;
  if (m.graded === 0) return `all ${m.symbols} carried, no call`;
  return `${m.graded} of ${m.symbols} graded (${m.carried} carried), ${m.shards.length} shard(s) (${sizes(m.shards)} symbols); prompt bytes ${kb(m.shard_bytes)} in ${m.calls.length} call(s), ${Math.round(m.wall_ms / 1000)}s${m.set_aside?.length ? `; ${m.set_aside.length} set aside past the retry (${m.set_aside.map((x) => x.name).join(", ")})` : ""}${m.regrade_why ? `; ${m.regrade_why}` : ""}`;
}

export function symbolLogPart(m: SymbolMetrics): string {
  return `symbols: ${symbolLogBody(m)}`;
}

/** A synthetic referee for a dry run: every shard grades its nodes `ok`, the global pass finds
 * nothing (and approves the key results when patches are present). No model is called.
 * `errorOn`: nodes graded a (synthetic, in-scope) `error` instead — to exercise the fix-as-you-go
 * interleave in a dry run; the caller stops naming a node once it is repaired. */
export function syntheticAsk(
  hasPatches: boolean,
  opts: {
    errorOn?: (id: string) => boolean;
    /** The repaired statements whose fixer note a clean grade grades for clarity (`clarityOwed`). */
    gradeNote?: (id: string) => boolean;
  } = {},
): (c: RefereeCall) => Promise<unknown> {
  return async (c) => {
    const ok = (id: string) => ({
      id,
      faithfulness: "ok",
      ambiguity: "ok",
      correctness: "ok",
      detail: "dry run: synthetic grade, no referee was called",
      witness: null,
      fix: null,
      bookkeeping_assumption: null,
      reading: null,
      minimality: false,
      weakens_contribution: false,
      follows_repair: false,
    });
    const confirmed = (id: string) => (opts.gradeNote?.(id) ? { ...ok(id), explanation_clarity: { grade: "ok", reason: "dry run: synthetic clarity grade" } } : ok(id));
    const grade = (id: string) =>
      opts.errorOn?.(id)
        ? {
            ...ok(id),
            correctness: "error",
            detail: "dry run: synthetic error, no referee was called",
            witness: "dry run: synthetic witness",
            witness_regime: "in_scope",
            witness_instance: "dry run: synthetic instance",
          }
        : confirmed(id);
    if (c.kind === "shard") return { summary: "dry run", nodes: c.nodes.map(grade) };
    return {
      verdict: "PASS",
      summary: "dry run — no referee was called",
      patch_review: hasPatches ? { key_results_ok: true, detail: "dry run" } : null,
      rejection_verdicts: null,
      cross_node: [],
    };
  };
}
