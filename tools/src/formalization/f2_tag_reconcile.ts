// F2 revise tag reconciliation (deterministic, no model).
//
// V1.5 pin/bookkeeping ids are POSITIONAL (`ass:pin-N`, `ass:bk-N`) and are renumbered on every
// V1.5 pass. A revise re-entry into F2 therefore finds a scaffold whose `-- @node:` tags name ids
// the current plan no longer has, while the plan delivers ids the scaffold never tagged. Left
// alone, the scaffolder is not told about either and the post-F2 P7 gate refuses. Before the
// scaffolder runs we:
//   1. retag a stale tag to the current node it is the same object as (same Lean name in the
//      current plan, the same reading text in the previous core, or a docstring that carries the
//      current reading text) — the declaration and its proof are kept;
//   2. remove the declaration (and its carry-over comment) of a stale tag no other declaration
//      references; a stale declaration that another declaration still uses is kept and reported;
//   3. list every delivered plan node left without a tag as a NEW node for the scaffolder.
// A repair's hashed ids (a reading it states, a corollary it splits off) go stale the same way when the
// repair is revised or withdrawn, and are reconciled with them.
// "Stale" = a positional or repair id in neither the current plan nor the current core. Other plan-less tags
// (agent-introduced helpers, which P7 exempts when unchanged) are never touched here.
import { existsSync } from "node:fs";
import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import type { Core } from "../core/schema.js";
import { coreNodeIds } from "../core/schema.js";
import type { Plan } from "./plan/schema.js";
import { maskLeanCommentsAndStrings } from "../shared/lean_mask.js";
import {
  LEAN_ATTRS_PREFIX_SRC,
  LEAN_DECL_HEADER_RE,
  LEAN_DECL_KEYWORDS,
  LEAN_MODIFIERS_PREFIX_SRC,
} from "../shared/lean_syntax.js";
import { listLeanFiles } from "../pipeline_support.js";

/** Block-comment nesting depth at the START of each line (Lean `/- -/` nest;
 *  `/--`,`/-!` are block comments too).  `--` is a line comment.  Minimal string
 *  handling so a `"…/-…"` literal does not open a comment. */
function commentDepthAtLineStart(lines: string[]): number[] {
  const depths: number[] = [];
  let depth = 0;
  for (const line of lines) {
    depths.push(depth);
    let i = 0;
    let inStr = false;
    while (i < line.length) {
      const two = line.slice(i, i + 2);
      if (depth > 0) {
        if (two === '-/') { depth--; i += 2; continue; }
        if (two === '/-') { depth++; i += 2; continue; }
        i++; continue;
      }
      // depth === 0
      if (inStr) {
        if (line[i] === '\\') { i += 2; continue; }
        if (line[i] === '"') { inStr = false; i++; continue; }
        i++; continue;
      }
      if (two === '--') break; // line comment: rest of line irrelevant to depth
      if (two === '/-') { depth++; i += 2; continue; }
      if (line[i] === '"') { inStr = true; i++; continue; }
      i++;
    }
  }
  return depths;
}

// A declaration, its tags and its attributes may be indented (inside a `namespace`/`section`
// the scaffolder indents): every line test here allows leading whitespace.
const NODE_TAG_RE = /^\s*--\s*@node:\s*([A-Za-z0-9:._-]+)\s*$/;
const ENV_TAG_RE = /^\s*--\s*@env:\s*([A-Za-z0-9:._-]+)\s*$/;
const DECL_NAME_RE = new RegExp(
  String.raw`^[ \t]*${LEAN_ATTRS_PREFIX_SRC}${LEAN_MODIFIERS_PREFIX_SRC}(?:${LEAN_DECL_KEYWORDS})\s+([^\s({:[]+)`,
);
const CARRYOVER_TAG = "PRIOR PROOF (carry-over: auto";
/** V1.5's positional pin / bookkeeping ids. */
export const POSITIONAL_ID_RE = /^ass:(?:pin|bk)-\d+$/;

/** A repair's hashed ids (`verify/core_graph.ts`): a reading it states (`ass:pin-fix-<hash>`) and a
 * corollary it splits off (`<thm|lem|prop>:cor-fix-<hash>`). Only the runner writes such an id, and a
 * repair revised or withdrawn drops it: its tag is then stale like a renumbered positional one (retagged
 * only by Lean name; else its declaration removed, or kept and reported when still referenced). */
export const REPAIR_ID_RE = /^(?:ass:pin-fix|(?:thm|lem|prop):cor-fix)-[0-9a-f]{8}$/;

export type RetagBasis = "lean-name" | "prev-core-text" | "docstring-text";

export interface TagReconciliation {
  retagged: { from: string; to: string; decl: string; file: string; basis: RetagBasis }[];
  /** Stale declarations deleted. `untagged` = only the stale tag line was deleted, because the
   *  declaration also carries a live node's tag. */
  removed: { id: string; decl: string | null; file: string; untagged?: boolean }[];
  /** Stale tags kept because another declaration still references their declaration. */
  staleReferenced: { id: string; decl: string; file: string; referencedBy: string[] }[];
  /** Delivered plan nodes with no `@node` tag after reconciliation. */
  newNodes: { id: string; lean_kind: string; lean_name: string; target_file?: string }[];
}

export interface LeanSource {
  file: string;
  text: string;
}

interface DeclBlock {
  file: string;
  /** first line of the block (docstring / tag / attribute), inclusive */
  start: number;
  headerLine: number;
  /** last line, inclusive (carry-over comments included) */
  end: number;
  name: string;
  nodeTags: { id: string; line: number }[];
  docstring: string;
}

function isBoundary(line: string): boolean {
  if (line.trim() === "") return false;
  // An indented line continues the declaration above — unless it is itself a declaration
  // header or a tag (an indented declaration is not part of its predecessor).
  if (/^\s/.test(line)) return LEAN_DECL_HEADER_RE.test(line) || NODE_TAG_RE.test(line) || ENV_TAG_RE.test(line);
  if (line.startsWith("|")) return false;
  if (line.startsWith("--")) return NODE_TAG_RE.test(line) || ENV_TAG_RE.test(line);
  return true;
}

function parseBlocks(file: string, text: string): { lines: string[]; blocks: DeclBlock[]; danglingTags: { id: string; line: number }[] } {
  const lines = text.split(/\r?\n/);
  const depth = commentDepthAtLineStart(lines);
  const blocks: DeclBlock[] = [];
  const claimedTagLines = new Set<number>();
  for (let h = 0; h < lines.length; h++) {
    if (depth[h] !== 0 || !LEAN_DECL_HEADER_RE.test(lines[h])) continue;
    const name = DECL_NAME_RE.exec(lines[h])?.[1];
    if (!name) continue;
    // Walk up over attributes, @node tags and one docstring.
    let start = h;
    const nodeTags: { id: string; line: number }[] = [];
    let docstring = "";
    let k = h - 1;
    for (; k >= 0; k--) {
      const ln = lines[k];
      const tag = NODE_TAG_RE.exec(ln);
      if (tag) { nodeTags.unshift({ id: tag[1], line: k }); start = k; continue; }
      if (depth[k] === 0 && /^\s*@\[/.test(ln)) { start = k; continue; }
      break;
    }
    if (k >= 0 && /-\/\s*$/.test(lines[k]) && !ENV_TAG_RE.test(lines[k])) {
      let s = k;
      while (s > 0 && !(depth[s] === 0 && /^\s*\/-/.test(lines[s]))) s--;
      if (/^\s*\/--/.test(lines[s])) {
        docstring = lines.slice(s, k + 1).join("\n").replace(/^\s*\/--/, "").replace(/-\/\s*$/, "").trim();
        start = s;
        // tags above the docstring also belong to this declaration
        for (let t = s - 1; t >= 0 && NODE_TAG_RE.test(lines[t]); t--) {
          nodeTags.unshift({ id: NODE_TAG_RE.exec(lines[t])![1], line: t });
          start = t;
        }
      }
    }
    let end = h;
    for (let j = h + 1; j < lines.length; j++) {
      if (depth[j] !== 0 || !isBoundary(lines[j])) {
        // A line comment between declarations is not part of the previous one.
        if (lines[j].trim() !== "" && !(depth[j] === 0 && lines[j].trimStart().startsWith("--"))) end = j;
        continue;
      }
      if (lines[j].trimStart().startsWith("/-") && lines[j].includes(CARRYOVER_TAG)) {
        // The carry-over comment injected after a declaration belongs to it.
        let c = j;
        while (c + 1 < lines.length && depth[c + 1] > 0) c++;
        end = c;
        j = c;
        continue;
      }
      break;
    }
    for (const t of nodeTags) claimedTagLines.add(t.line);
    blocks.push({ file, start, headerLine: h, end, name, nodeTags, docstring });
  }
  const danglingTags: { id: string; line: number }[] = [];
  lines.forEach((ln, i) => {
    const m = NODE_TAG_RE.exec(ln);
    if (m && !claimedTagLines.has(i)) danglingTags.push({ id: m[1], line: i });
  });
  return { lines, blocks, danglingTags };
}

function shortName(name: string): string {
  return name.split(".").at(-1) ?? name;
}

function normalizeReading(s: string): string {
  return s
    .toLowerCase()
    .replace(/\\[a-z]+/g, " ")
    .replace(/[^\p{L}\p{N}]+/gu, " ")
    .trim();
}

function textMatches(docstring: string, reading: string): boolean {
  const d = normalizeReading(docstring);
  const r = normalizeReading(reading);
  if (!d || !r) return false;
  return d === r || (r.split(" ").length >= 5 && d.includes(r));
}

function readingOf(core: Pick<Core, "assumptions"> | null | undefined, id: string): string | undefined {
  return core?.assumptions?.find((a) => a.id === id)?.condition;
}

function referencePattern(decl: string): RegExp {
  const esc = shortName(decl).replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  return new RegExp(String.raw`(?<![A-Za-z0-9_'.])(?:[A-Za-z0-9_']+\.)*${esc}(?![A-Za-z0-9_'])`);
}

/**
 * Pure reconciliation over in-memory sources. Returns the rewritten sources (only changed files)
 * and what was done. `prevCore` / `prevPlan` are the pre-rewind artifacts when the run kept them.
 */
export function reconcileScaffoldTagsInMemory(args: {
  sources: LeanSource[];
  plan: Plan;
  core: Core;
  prevCore?: Pick<Core, "assumptions"> | null;
  prevPlan?: Pick<Plan, "nodes"> | null;
  /** Ids of the accepted core that take no declaration any more (its umbrellas, `core_io.ts`
   * `formalizationView`): a tag on one is stale like a withdrawn repair's. */
  retired?: ReadonlySet<string>;
}): { result: TagReconciliation; changed: LeanSource[] } {
  const { plan, core } = args;
  const planIds = new Set(Object.keys(plan.nodes));
  const coreIds = coreNodeIds(core);
  const parsed = args.sources.map((s) => ({ file: s.file, ...parseBlocks(s.file, s.text) }));
  const allTagged = new Set<string>();
  for (const p of parsed) {
    for (const b of p.blocks) for (const t of b.nodeTags) allTagged.add(t.id);
    for (const t of p.danglingTags) allTagged.add(t.id);
  }
  // Only the runner's own ids are reconciled: V1.5's positional ones and a repair's hashed ones. Any
  // other plan-less tag is left to P7, which keeps its exemption for exact completed
  // agent-introduced helpers (tagged ids outside plan and core).
  const isStale = (id: string) => (POSITIONAL_ID_RE.test(id) || REPAIR_ID_RE.test(id) || !!args.retired?.has(id)) && !planIds.has(id) && !coreIds.has(id);
  const delivered = (id: string) => plan.nodes[id]?.delivery_status !== "undelivered";
  const untaggedDelivered = new Set([...planIds].filter((id) => delivered(id) && !allTagged.has(id)));

  const result: TagReconciliation = { retagged: [], removed: [], staleReferenced: [], newNodes: [] };
  // line edits per file: replace (retag) or delete ranges
  const retagLines = new Map<string, Map<number, string>>();
  const deleteRanges = new Map<string, [number, number][]>();
  const pushDelete = (file: string, a: number, b: number) => {
    const list = deleteRanges.get(file) ?? [];
    list.push([a, b]);
    deleteRanges.set(file, list);
  };

  type Stale = { id: string; line: number; block: DeclBlock | null; file: string };
  const stale: Stale[] = [];
  for (const p of parsed) {
    for (const b of p.blocks) for (const t of b.nodeTags) if (isStale(t.id)) stale.push({ id: t.id, line: t.line, block: b, file: p.file });
    for (const t of p.danglingTags) if (isStale(t.id)) stale.push({ id: t.id, line: t.line, block: null, file: p.file });
  }

  // 1. Retag. Each candidate basis must give a UNIQUE unclaimed target.
  const claimed = new Set<string>();
  const unresolved: Stale[] = [];
  for (const s of stale) {
    const pick = (cands: string[]): string | undefined => {
      const free = cands.filter((c) => !claimed.has(c));
      return free.length === 1 ? free[0] : undefined;
    };
    let target: string | undefined;
    let basis: RetagBasis | undefined;
    if (s.block) {
      const byName = [...untaggedDelivered].filter((id) => shortName(plan.nodes[id].lean_name) === shortName(s.block!.name));
      const prevName = args.prevPlan?.nodes?.[s.id]?.lean_name;
      const byPrevName = prevName
        ? [...untaggedDelivered].filter((id) => shortName(plan.nodes[id].lean_name) === shortName(prevName))
        : [];
      target = pick([...new Set([...byName, ...byPrevName])]);
      if (target) basis = "lean-name";
    }
    if (!target && POSITIONAL_ID_RE.test(s.id)) {
      const positional = [...untaggedDelivered].filter((id) => POSITIONAL_ID_RE.test(id));
      const prevText = readingOf(args.prevCore, s.id);
      if (prevText) {
        target = pick(positional.filter((id) => {
          const r = readingOf(core, id);
          return r !== undefined && normalizeReading(r) === normalizeReading(prevText);
        }));
        if (target) basis = "prev-core-text";
      }
      if (!target && s.block?.docstring) {
        target = pick(positional.filter((id) => {
          const r = readingOf(core, id);
          return r !== undefined && textMatches(s.block!.docstring, r);
        }));
        if (target) basis = "docstring-text";
      }
    }
    if (target && basis) {
      claimed.add(target);
      untaggedDelivered.delete(target);
      const edits = retagLines.get(s.file) ?? new Map<number, string>();
      edits.set(s.line, `-- @node: ${target}`);
      retagLines.set(s.file, edits);
      result.retagged.push({ from: s.id, to: target, decl: s.block?.name ?? "(no declaration)", file: s.file, basis });
    } else {
      unresolved.push(s);
    }
  }

  // 2. Remove unreferenced stale declarations (fixpoint: a stale decl used only by removed ones goes too).
  const retagged = (file: string, line: number) => retagLines.get(file)?.has(line) === true;
  const liveTag = (b: DeclBlock) => b.nodeTags.some((t) => !isStale(t.id) || retagged(b.file, t.line));
  const blockKey = (b: DeclBlock) => `${b.file}:${b.headerLine}`;
  const removedBlocks = new Set<string>();
  const candidates = unresolved.filter((s) => s.block && !liveTag(s.block));
  const masked = new Map(parsed.map((p) => [p.file, maskLeanCommentsAndStrings(p.lines.join("\n")).split("\n")] as const));
  const referencers = (b: DeclBlock): string[] => {
    const re = referencePattern(b.name);
    const out = new Set<string>();
    for (const p of parsed) {
      const m = masked.get(p.file)!;
      for (const other of p.blocks) {
        if (blockKey(other) === blockKey(b) || removedBlocks.has(blockKey(other))) continue;
        const body = m.slice(other.headerLine, other.end + 1).join("\n");
        if (re.test(body)) {
          const t = other.nodeTags[0];
          out.add(t ? retagLines.get(other.file)?.get(t.line)?.replace(/^--\s*@node:\s*/, "") ?? t.id : other.name);
        }
      }
    }
    return [...out].sort();
  };
  let progress = true;
  const pending = new Map(candidates.map((s) => [blockKey(s.block!), s] as const));
  while (progress) {
    progress = false;
    for (const [key, s] of pending) {
      if (referencers(s.block!).length > 0) continue;
      removedBlocks.add(key);
      pending.delete(key);
      progress = true;
    }
  }
  for (const s of unresolved) {
    if (!s.block) {
      pushDelete(s.file, s.line, s.line);
      result.removed.push({ id: s.id, decl: null, file: s.file, untagged: true });
    } else if (liveTag(s.block)) {
      pushDelete(s.file, s.line, s.line);
      result.removed.push({ id: s.id, decl: s.block.name, file: s.file, untagged: true });
    } else if (removedBlocks.has(blockKey(s.block))) {
      if (!result.removed.some((r) => r.decl === s.block!.name && r.file === s.file && !r.untagged)) {
        pushDelete(s.file, s.block.start, s.block.end);
      }
      result.removed.push({ id: s.id, decl: s.block.name, file: s.file });
    } else {
      result.staleReferenced.push({ id: s.id, decl: s.block.name, file: s.file, referencedBy: referencers(s.block) });
    }
  }

  // 3. New nodes: still-untagged delivered plan nodes.
  for (const id of [...untaggedDelivered].sort()) {
    const n = plan.nodes[id];
    result.newNodes.push({ id, lean_kind: n.lean_kind, lean_name: n.lean_name, ...(n.target_file ? { target_file: n.target_file } : {}) });
  }

  const changed: LeanSource[] = [];
  for (const p of parsed) {
    const edits = retagLines.get(p.file);
    const dels = deleteRanges.get(p.file) ?? [];
    if (!edits && dels.length === 0) continue;
    const drop = new Set<number>();
    for (const [a, b] of dels) {
      for (let i = a; i <= b; i++) drop.add(i);
      // swallow one following blank line so no double gap is left behind
      if (a !== b && p.lines[b + 1]?.trim() === "" && (a === 0 || p.lines[a - 1]?.trim() === "")) drop.add(b + 1);
    }
    const out: string[] = [];
    p.lines.forEach((ln, i) => {
      if (drop.has(i)) return;
      out.push(edits?.get(i) ?? ln);
    });
    changed.push({ file: p.file, text: out.join("\n") });
  }
  return { result, changed };
}

/** True when reconciliation did or reported anything. */
export function reconciliationIsEmpty(r: TagReconciliation): boolean {
  return r.retagged.length + r.removed.length + r.staleReferenced.length + r.newNodes.length === 0;
}

/** One-line-per-item summary for logs and gate failures. */
export function describeTagReconciliation(r: TagReconciliation): string {
  const parts: string[] = [];
  if (r.retagged.length) parts.push(`retagged ${r.retagged.map((x) => `${x.from}→${x.to} (${x.decl}, ${x.basis})`).join(", ")}`);
  if (r.removed.length) parts.push(`removed ${r.removed.map((x) => `${x.id}${x.decl ? ` (${x.decl}${x.untagged ? ", tag only" : ""})` : " (dangling tag)"}`).join(", ")}`);
  if (r.staleReferenced.length) parts.push(`kept stale ${r.staleReferenced.map((x) => `${x.id} (${x.decl}, referenced by ${x.referencedBy.join(", ")})`).join(", ")}`);
  if (r.newNodes.length) parts.push(`listed as new ${r.newNodes.map((x) => x.id).join(", ")}`);
  return parts.length ? parts.join("; ") : "nothing to reconcile";
}

/** Directive for the scaffolder. Empty when there is nothing it must act on or know. */
export function tagReconciliationBlock(r: TagReconciliation): string {
  if (reconciliationIsEmpty(r)) return "";
  const rel = (f: string) => path.basename(f);
  const lines = [
    "=== F2 TAG RECONCILIATION (applied by the runner before this pass) ===",
    "V1.5 pin/bookkeeping ids (ass:pin-N, ass:bk-N) are positional and were renumbered since the",
    "scaffold on disk was written. The runner reconciled the `-- @node:` tags against the current plan:",
  ];
  if (r.retagged.length) {
    lines.push("Retagged (same declaration and proof, new id):");
    for (const x of r.retagged) lines.push(`  • ${x.from} → ${x.to}: ${x.decl} in ${rel(x.file)}`);
  }
  if (r.removed.length) {
    lines.push("Removed (node no longer in the plan or core; nothing else used it):");
    for (const x of r.removed) lines.push(`  • ${x.id}${x.decl ? `: ${x.decl}${x.untagged ? " (tag line only)" : ""}` : ""} in ${rel(x.file)}`);
  }
  if (r.newNodes.length) {
    lines.push(
      "NEW NODES TO SCAFFOLD — delivered plan nodes with no declaration on disk. Add each one as its",
      "plan entry specifies, with its `-- @node:` tag, and wire it into its consumers per the plan",
      "`hyps` and the core `depends_on`:",
    );
    for (const x of r.newNodes) lines.push(`  • ${x.id}: ${x.lean_kind} ${x.lean_name}${x.target_file ? ` in ${x.target_file}` : ""}`);
  }
  if (r.staleReferenced.length) {
    lines.push(
      "STALE BUT REFERENCED — the tag names a node no longer in the plan or core, and another",
      "declaration still uses it. Update the users to the current plan and core, then delete the stale",
      "declaration and its tag (or retag it if the plan maps it to a current node):",
    );
    for (const x of r.staleReferenced) lines.push(`  • ${x.id}: ${x.decl} in ${rel(x.file)}, used by ${x.referencedBy.join(", ")}`);
  }
  lines.push("=== END F2 TAG RECONCILIATION ===", "");
  return lines.join("\n");
}

async function readJsonIfExists(file: string): Promise<unknown> {
  if (!existsSync(file)) return null;
  try {
    return JSON.parse(await readFile(file, "utf8"));
  } catch {
    return null;
  }
}

/** Reconcile the on-disk scaffold under `leanDir` and write the changed files. */
export async function reconcileScaffoldTags(args: {
  leanDir: string;
  plan: Plan;
  core: Core;
  /** `<plan>.prev` / `<core>.prev` paths; read when present. */
  prevPlanPath?: string;
  prevCorePath?: string;
  retired?: ReadonlySet<string>;
  write?: boolean;
}): Promise<TagReconciliation> {
  const files = existsSync(args.leanDir) ? (await listLeanFiles(args.leanDir)).sort() : [];
  const sources = await Promise.all(files.map(async (file) => ({ file, text: await readFile(file, "utf8") })));
  const prevPlan = args.prevPlanPath ? (await readJsonIfExists(args.prevPlanPath)) as Pick<Plan, "nodes"> | null : null;
  const prevCore = args.prevCorePath ? (await readJsonIfExists(args.prevCorePath)) as Pick<Core, "assumptions"> | null : null;
  const { result, changed } = reconcileScaffoldTagsInMemory({ sources, plan: args.plan, core: args.core, prevPlan, prevCore, retired: args.retired });
  if (args.write !== false) {
    for (const c of changed) await writeFile(c.file, c.text, "utf8");
  }
  return result;
}
