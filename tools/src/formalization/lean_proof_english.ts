// F5 "Lean Proof in English": what the run's Lean proofs prove and how, written as a paper writes a
// proof, and the paper's printed proofs checked against it.
//
// The F stages audit Lean STATEMENTS against the paper, never the proofs: a Lean proof may take
// another route than the printed one, or quietly correct a printed step that is wrong as printed, and
// nothing would say so. Three model calls close that:
//
// 1. The translator writes, from the Lean alone (never the paper's proofs), one account per paper
//    result: its proof, with every helper lemma of the formalization that only this result uses proved
//    inside it, where the argument needs it. A helper two or more results use is a SHARED piece
//    (`A<n>`): written once, with its own statement and proof (its own helpers inside it), and cited
//    from each account that uses it; so is a part of an account too long for one call (cited from
//    it). Which helpers belong to which account is decided on the Lean alone (`planTasks`: the
//    dominator tree of the declarations the results reach), never by the paper; nothing is cut, so
//    every helper's proof is written somewhere. Definitions are not written (the F stages audited
//    them against the paper; a proof says in a sentence what an object of the formalization is where
//    it first uses one). One call per result, the shared pieces packed by size; the translator reads
//    the Lean it is pointed at. References are ids in double brackets (⟦thm:main⟧, ⟦A3⟧), which the page
//    prints as the paper names them; anchors `[phrase](lean:A-B)` (or `lean:FILE:A-B` for a helper in
//    another file) tie the text to the Lean lines, and every declaration of an account must carry one.
// 2. A reviewer checks each account against the Lean alone: faithfulness first, then readability and
//    self-containment (which never make it unfaithful). One with a defect of either kind is written
//    revised from them and reviewed again, up to three times; then it is kept, shown on the page as not
//    confirmed faithful with its issues, and readability notes left are shown beside it.
// 3. The comparator reads each result's printed proof beside its English account (its proof and the
//    shared pieces it cites), for a result whose account the review found faithful, piece by piece;
//    any other result is not compared. It lists the places where the two differ in substance, each a
//    `difference` (another route, the printed text enough for its own), an `ambiguity` (a detail or
//    an argument left out, loose wording, or a weaker reading) or an `error` (the printed text is false
//    in the paper's setting, or concludes what its stated reason does not yield). An error is a
//    departure; a step left out is an ambiguity, whatever kind the reply gives it. A printed step that
//    is wrong is a correction of the paper through the typo channel (`verify/patches.ts`
//    `recordLeanStepFixes`, `source: "lean"`): blue in the corrected paper and on the page
//    ("Corrected (Lean proof)"), listed in the report; a snippet the runner cannot place is asked for
//    once more before it is recorded unplaced (reported only). A gap recorded by an earlier version (a
//    needed step left out) is still listed with the result, never marked in the paper. Only the proof the
//    paper prints (its transcription's) is compared. An ambiguity is a note for the reader with its
//    suggested wording; a difference, a route.
//
// Written whole on every F5 pass (and by `paperformalizer explain-proofs`; with `--only`, for those
// results alone). Advisory: a failure is logged and F5 goes on.

import { existsSync } from "node:fs";
import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { MODEL_PLAN } from "../constants.js";
import type { PipelineContext, StateJson } from "../types.js";
import { artifactPaths, listLeanFiles, readPrompt, type StageDeps } from "../pipeline_support.js";
import { dispatchAgent, parseAgentJson } from "../framework/agent_dispatch.js";
import { graphPath, loadGraph } from "../graph/store.js";
import type { GraphNode } from "../graph/types.js";
import { maskLeanCommentsAndStrings } from "../graph/extractor.js";
import { mapLimit } from "./reviewer_verdicts.js";
import { fillTemplate } from "../shared/template.js";
import { parseFileDecls } from "./lean_rows.js";
import { declSourceFrom, extractFullDeclSource } from "../presentation/lean_extract.js";
import { leanNameLeaf } from "../presentation/lean_decl_name.js";
import { verifyRunDir } from "../paths.js";
import { coreJsonPath, readTypedCore } from "../core/core_io.js";
import { readPatchFile, recordLeanStepFixes, repairSources, sameWords, withRefereeTypos, type PatchFile } from "../verify/patches.js";
import type { PassageSources } from "../verify/ops.js";
import { VERIFY_FILES } from "../verify/types.js";

export const LEAN_PROOF_ENGLISH_ARTIFACT = "lean_proof_english.json";
/** Characters of printed proof and English account one comparator call reads (a result with more goes alone). */
const COMPARE_CHARS_PER_CALL = 120_000;
const CALL_CONCURRENCY = 4;
/** Lean lines one account may span before its largest part becomes an account of its own (one call
 *  wrote ~6,900 lines faithfully; one of ~19,600 failed; the call now carries its Lean, ~60 chars a line, and a
 *  review carries it with the English, under the agent's ~200k-token compaction limit). */
const MAX_ACCOUNT_LINES = 4000;
/** Shared lemmas packed into one call: at most this many Lean lines, and tasks. */
const PACK_LINES = 1500;
const PACK_TASKS = 25;
/** Times an account the review finds a defect in (unfaithful, or a reader would stumble) is revised from its findings, each revision reviewed again. */
const MAX_REWRITES = 3;
/** The paper's definitions shown in a call's prompt, at most this many lines (the rest read on demand). */
const DEF_LINES = 600;

/** Lean declarations with a proof (and the graph kinds of the paper's results). */
const PROOF_KINDS = new Set(["theorem", "lemma"]);
const DEF_KINDS = new Set(["def", "abbrev", "structure", "inductive", "class"]);

// ── the run's Lean ───────────────────────────────────────────────────────────

/** One declaration of the run's Lean: its full name, where it stands (`file` relative to the paper's
 *  Lean directory; lines `line`–`end`, 1-based), its source and the first paragraph of its docstring
 *  (crosslink markup dropped). */
export interface LeanDecl { name: string; leaf: string; kind: string; file: string; line: number; end: number; source: string; doc: string }

const IDENT_RE = /[\p{L}_][\p{L}\p{N}_'!?]*/gu;

/** The docstring standing right above line `line` (1-based) of `text`, its first paragraph with the
 *  crosslink markup and tag lines dropped; "" when there is none. Pure. */
export function docAbove(text: string, line: number): string {
  const before = text.split("\n").slice(0, line - 1).join("\n");
  // the last docstring, only attributes and modifiers between it and the declaration
  const m = /\/--((?:(?!-\/)[\s\S])*?)-\/\s*(?:@\[[^\]]*\]\s*|(?:private|protected|public|noncomputable|nonrec|partial|unsafe)\s+)*$/.exec(before);
  if (!m) return "";
  const first = m[1]!.trim().split(/\n\s*\n/)[0] ?? "";
  return first.replace(/\[([^\]]*)\]\((?:hyp|goal|step)[^)]*\)/g, "$1").replace(/^\s*@(?:realizes|node|env)\b.*$/gm, "").replace(/\s+/g, " ").trim();
}

/** The declarations of one file (`rel`, its text `text`) that take a proof or define an object. Pure. */
export function fileDecls(rel: string, text: string): LeanDecl[] {
  const out: LeanDecl[] = [];
  const lines = text.split("\n");
  for (const d of parseFileDecls(text).decls) {
    if (!PROOF_KINDS.has(d.kind) && !DEF_KINDS.has(d.kind)) continue;
    let source: string;
    // cut at the line the parser gives (re-locating each declaration re-parses the file: quadratic)
    try { source = lines[d.line - 1]?.includes(leanNameLeaf(d.name)) ? declSourceFrom(lines, d.line - 1) : extractFullDeclSource(text, d.name, d.line); } catch { continue; }
    const name = d.ns && !d.name.startsWith(`${d.ns}.`) ? `${d.ns}.${d.name}` : d.name;
    out.push({ name, leaf: leanNameLeaf(name), kind: d.kind, file: rel, line: d.line, end: d.line + source.split("\n").length - 1, source, doc: docAbove(text, d.line) });
  }
  return out;
}

/** Every declaration of the paper's Lean directory, files in sorted order (`tmp/` left out). */
export async function readLeanDecls(leanDir: string): Promise<LeanDecl[]> {
  const out: LeanDecl[] = [];
  for (const abs of (await listLeanFiles(leanDir)).sort()) {
    const text = await readFile(abs, "utf8").catch(() => null);
    if (text !== null) out.push(...fileDecls(path.relative(leanDir, abs).replaceAll(path.sep, "/"), text));
  }
  return out;
}

/** The declarations `d` mentions, other than itself, in the order its source first mentions them
 *  (by leaf name: declarations sharing a leaf are all taken). Pure. */
export function mentions(d: LeanDecl, byLeaf: ReadonlyMap<string, readonly LeanDecl[]>): LeanDecl[] {
  const seen = new Set<LeanDecl>();
  for (const tok of maskLeanCommentsAndStrings(d.source).match(IDENT_RE) ?? []) {
    for (const x of byLeaf.get(tok) ?? []) if (x !== d) seen.add(x);
  }
  return [...seen];
}

// ── what is written, and in which calls ──────────────────────────────────────

/** A paper node the English may cite (⟦id⟧): a result, an assumption or a definition of the paper, or a
 *  result it cites (`cite`). */
export interface PaperRef { id: string; kind: string; label: string | null; statement: string; cite?: string }

/** One account: the proof of a paper result (`id` its node), or a shared helper lemma (`id` `A<n>`),
 *  with the helper lemmas proved inside it (`inline`, in the order the walk reaches them). */
export interface Task { id: string; role: "result" | "shared"; decl: LeanDecl; inline: LeanDecl[]; statement?: string }

export interface Plan {
  /** The paper results with a Lean proof, in the paper's order. */
  results: Task[];
  /** The shared helper lemmas, by id `A<n>` (numbered in the order the results' Lean reaches them). */
  shared: Task[];
  /** The translator calls: one result each, or several shared lemmas. */
  calls: Task[][];
  /** For each account, the paper nodes and shared ids it may cite. */
  uses: Map<string, { refs: string[]; aux: string[] }>;
  /** A result whose Lean declaration an earlier result already has: its id → that result's (one account, written once). */
  aliases: Map<string, string>;
  /** For each account, the shared lemmas split off from it that its own Lean uses: it must cite them. */
  parts: Map<string, string[]>;
}

/** The immediate dominator of each vertex of a graph rooted at 0 (`succ`: edges; -1: unreached).
 *  Cooper–Harvey–Kennedy. Pure. */
export function dominators(succ: readonly (readonly number[])[]): Int32Array {
  const n = succ.length;
  const post: number[] = [];
  const seen = new Uint8Array(n);
  const stack: Array<[number, number]> = [[0, 0]];
  seen[0] = 1;
  while (stack.length) {
    const top = stack.at(-1)!;
    const [v, i] = top;
    if (i < succ[v]!.length) {
      top[1] = i + 1;
      const w = succ[v]![i]!;
      if (!seen[w]) { seen[w] = 1; stack.push([w, 0]); }
    } else { post.push(v); stack.pop(); }
  }
  const order = new Int32Array(n).fill(-1);
  post.forEach((v, k) => { order[v] = k; });
  const preds: number[][] = Array.from({ length: n }, () => []);
  succ.forEach((s, u) => { if (seen[u]) for (const v of s) preds[v]!.push(u); });
  const idom = new Int32Array(n).fill(-1);
  idom[0] = 0;
  const rpo = [...post].reverse().filter((v) => v !== 0);
  const meet = (a: number, b: number) => {
    while (a !== b) {
      while (order[a]! < order[b]!) a = idom[a]!;
      while (order[b]! < order[a]!) b = idom[b]!;
    }
    return a;
  };
  for (let changed = true; changed;) {
    changed = false;
    for (const b of rpo) {
      let nd = -1;
      for (const p of preds[b]!) if (idom[p] !== -1) nd = nd === -1 ? p : meet(p, nd);
      if (idom[b] !== nd) { idom[b] = nd; changed = true; }
    }
  }
  return idom;
}

/**
 * The accounts and the calls. `nodeOfDecl`: the paper node each declaration of a node formalizes (its
 * graph `lean.decl_name`); `results`: the paper results with a Lean declaration, in order, each with
 * the paper nodes it depends on (`deps`: the cited results its proof uses among them). The helpers are
 * the lemmas of the run's Lean that are no paper node, reached from the results through the
 * declarations their Lean mentions (a paper node's stops the walk: it is cited; a definition is not
 * entered). A helper every path to which from the results passes through one result, or through one
 * shared helper, is proved inside that account; a helper reached from two or more results by paths
 * with no such common point is shared (`A<n>`), and so is the largest part of an account too long for
 * one call. One call per result; the shared lemmas packed by size. Pure.
 */
export function planTasks(decls: readonly LeanDecl[], nodeOfDecl: ReadonlyMap<string, string>, results: ReadonlyArray<{ id: string; decl: string; statement: string; deps?: readonly string[] }>): Plan {
  const byName = new Map(decls.map((d) => [d.name, d] as const));
  const byLeaf = new Map<string, LeanDecl[]>();
  for (const d of decls) (byLeaf.get(d.leaf) ?? byLeaf.set(d.leaf, []).get(d.leaf)!).push(d);
  const find = (name: string): LeanDecl | undefined => {
    const same = byLeaf.get(leanNameLeaf(name)) ?? [];
    return byName.get(name) ?? same.find((d) => name.endsWith(`.${d.name}`) || d.name.endsWith(`.${name}`)) ?? (same.length === 1 ? same[0] : undefined);
  };
  const nodeOf = new Map<LeanDecl, string>();
  for (const [name, node] of nodeOfDecl) { const d = find(name); if (d && !nodeOf.has(d)) nodeOf.set(d, node); }
  const mention = new Map<LeanDecl, LeanDecl[]>();
  const mentionsOf = (d: LeanDecl) => mention.get(d) ?? mention.set(d, mentions(d, byLeaf)).get(d)!;
  const isHelper = (d: LeanDecl) => PROOF_KINDS.has(d.kind) && !nodeOf.has(d);

  const resultTasks: Task[] = [];
  const depsOf = new Map<string, readonly string[]>();
  const aliases = new Map<string, string>();
  const aliasTasks: Task[] = [];
  for (const r of results) {
    const d = find(r.decl);
    if (!d || !PROOF_KINDS.has(d.kind)) continue;
    const first = resultTasks.find((t) => t.decl === d);
    // two paper results formalized by one declaration: one account, written once, compared for each
    if (first) { aliases.set(r.id, first.id); aliasTasks.push({ id: r.id, role: "result", decl: d, inline: first.inline, statement: r.statement }); depsOf.set(r.id, r.deps ?? []); continue; }
    resultTasks.push({ id: r.id, role: "result", decl: d, inline: [], statement: r.statement });
    depsOf.set(r.id, r.deps ?? []);
  }
  // the graph: a root (0) before every result; each declaration to the helpers its Lean mentions,
  // vertices numbered in the order the walk (breadth first) reaches them
  const vertex: LeanDecl[] = [];
  const index = new Map<LeanDecl, number>();
  const succ: number[][] = [[]];
  const queue: LeanDecl[] = [];
  const at = (d: LeanDecl): number => {
    let k = index.get(d);
    if (k === undefined) { k = succ.length; index.set(d, k); vertex[k] = d; succ.push([]); queue.push(d); }
    return k;
  };
  for (const r of resultTasks) succ[0]!.push(at(r.decl));
  while (queue.length) {
    const d = queue.shift()!;
    const k = index.get(d)!;
    succ[k] = [...new Set(mentionsOf(d).filter(isHelper).map(at))].filter((x) => x !== k);
  }
  const idom = dominators(succ);
  // the accounts: each result, and each helper reached from two or more results by paths with no
  // common point (its immediate dominator is the root); an account over MAX_ACCOUNT_LINES of Lean
  // gives a part (a helper it dominates, with what that helper dominates) its own account, cited from
  // it, until it fits — every helper is still written once. A dominator is reached before what it
  // dominates, so sizes add up in reverse walk order.
  const n = succ.length;
  const lines = (k: number) => vertex[k]!.end - vertex[k]!.line + 1;
  const kids: number[][] = Array.from({ length: n }, () => []);
  for (let k = 1; k < n; k++) if (idom[k]! > 0) kids[idom[k]!]!.push(k);
  const root = new Uint8Array(n);
  for (let k = 1; k < n; k++) if (idom[k] === 0) root[k] = 1;
  const size = new Float64Array(n); // Lean lines of k and what it dominates, down to other accounts
  for (let k = n - 1; k >= 1; k--) { if (idom[k] === -1) continue; size[k]! += lines(k); if (idom[k]! > 0 && !root[k]) size[idom[k]!]! += size[k]!; }
  const promote = (v: number) => { root[v] = 1; for (let u = idom[v]!; u > 0; u = idom[u]!) { size[u]! -= size[v]!; if (root[u]) break; } };
  const largest = (k: number): number => kids[k]!.reduce((x, c) => (root[c] || (x !== -1 && size[x]! >= size[c]!) ? x : c), -1);
  for (const work = [...root.keys()].filter((k) => root[k]); work.length;) {
    const a = work.pop()!;
    if (lines(a) > MAX_ACCOUNT_LINES) continue; // its own declaration does not fit: splitting cannot help
    while (size[a]! > MAX_ACCOUNT_LINES) {
      let part = largest(a);
      if (part === -1) break;
      // a part itself too long gives its largest part instead (a result whose Lean is a short wrapper
      // keeps the argument), unless its own declaration does not fit
      for (let below = largest(part); size[part]! > MAX_ACCOUNT_LINES && lines(part) <= MAX_ACCOUNT_LINES && below !== -1; below = largest(part)) part = below;
      promote(part); work.push(part);
    }
  }
  // each helper's account: its nearest dominator that is an account
  const owner = new Int32Array(n);
  const owners = () => { for (let k = 1; k < n; k++) owner[k] = idom[k] === -1 ? -1 : root[k] ? k : owner[idom[k]!]!; };
  owners();
  // a part split off may use a helper left in the account above it, which it could neither prove nor
  // cite: such a helper is an account of its own (until none is left)
  for (let changed = true; changed;) {
    changed = false;
    for (let u = 1; u < n; u++) for (const v of succ[u]!) if (owner[u] !== -1 && !root[v] && owner[v] !== owner[u]) { root[v] = 1; changed = true; }
    if (changed) owners();
  }
  const resultAt = new Map(resultTasks.map((t) => [index.get(t.decl)!, t] as const));
  const shared: Task[] = [];
  const sharedAt = new Map<number, Task>();
  for (let k = 1; k < n; k++) {
    if (!root[k] || resultAt.has(k)) continue;
    const t: Task = { id: `A${shared.length + 1}`, role: "shared", decl: vertex[k]!, inline: [] };
    shared.push(t); sharedAt.set(k, t);
  }
  const taskAt = (k: number) => resultAt.get(k) ?? sharedAt.get(k)!;
  for (let k = 1; k < n; k++) if (owner[k] !== -1 && owner[k] !== k) taskAt(owner[k]!).inline.push(vertex[k]!);
  // what each account may cite: the paper nodes its declarations mention (a result: its own paper
  // dependencies too), and the shared helpers they mention
  const uses = new Map<string, { refs: string[]; aux: string[] }>();
  for (const t of [...resultTasks, ...aliasTasks, ...shared]) {
    const refs = new Set<string>(t.role === "result" ? depsOf.get(t.id) : []), aux = new Set<string>();
    for (const d of [t.decl, ...t.inline]) for (const m of mentionsOf(d)) {
      const node = nodeOf.get(m);
      if (node) { if (node !== t.id) refs.add(node); continue; }
      const s = index.has(m) ? sharedAt.get(index.get(m)!) : undefined;
      if (s && s !== t) aux.add(s.id);
    }
    uses.set(t.id, { refs: [...refs], aux: [...aux] });
  }
  const inOrder = results.map((r) => resultTasks.find((t) => t.id === r.id) ?? aliasTasks.find((t) => t.id === r.id)).filter((t): t is Task => Boolean(t));
  // one call per result; shared lemmas packed in walk order (related ones together) by their Lean
  const calls: Task[][] = resultTasks.map((t) => [t]);
  let pack: Task[] = [], packed = 0;
  for (const t of shared) {
    const n = declsOf(t).reduce((m, d) => m + d.end - d.line + 1, 0);
    if (pack.length && (packed + n > PACK_LINES || pack.length >= PACK_TASKS)) { calls.push(pack); pack = []; packed = 0; }
    pack.push(t); packed += n;
  }
  if (pack.length) calls.push(pack);
  // the parts split off from an account that its own Lean uses: its English must cite them
  const parts = new Map<string, string[]>();
  for (const [k, t] of sharedAt) {
    if (idom[k]! <= 0) continue;
    const of = taskAt(owner[idom[k]!]!).id;
    if (uses.get(of)?.aux.includes(t.id)) (parts.get(of) ?? parts.set(of, []).get(of)!).push(t.id);
  }
  for (const [id, of] of aliases) if (parts.has(of)) parts.set(id, parts.get(of)!);
  return { results: inOrder, shared, calls, uses, aliases, parts };
}

// ── the translator's answer ──────────────────────────────────────────────────

export interface Entry { id: string; statement: string | null; proof: string | null }

export const PROOF_ENGLISH_SCHEMA: Record<string, unknown> = {
  type: "object", additionalProperties: false, required: ["entries"],
  properties: {
    entries: { type: "array", items: {
      type: "object", additionalProperties: false, required: ["id", "statement", "proof"],
      properties: { id: { type: "string" }, statement: { type: ["string", "null"] }, proof: { type: ["string", "null"] } },
    } },
  },
};

/** `[phrase](lean:A-B)`, `[phrase](lean:A)` or `[phrase](lean:FILE:A-B)`: an anchor of the English
 *  text on lines A–B of the Lean (of the account's own declaration's file, or of FILE). */
export const ANCHOR_RE = /\[((?:\$\$[^$]+\$\$|\$[^$]+\$|\\\[(?:[^\\]|\\[^\]])*\\\]|\\\((?:[^\\]|\\[^)])*\\\)|\\[^[\]()]|[^[\]$\\]|\[[^[\]$\\]*\])*)\]\(lean:(?:([^\s():]+\.lean):)?(\d+)(?:-(\d+))?\)/g;
/** `⟦id⟧`: a reference to a paper node or a shared helper. */
export const REF_RE = /⟦([^⟦⟧\s]+)⟧/g;
/** Lean's own words, which an English proof never uses. */
const LEAN_WORDS = /\b(?:simp|simpa|linarith|nlinarith|omega|aesop|norm_num|ring_nf|field_simp|gcongr|rfl|sorry|Mathlib|Finset|Real\.\w+|Nat\.\w+)\b/;

/** `text` with its mathematics blanked (`$…$`, `\[…\]`, `\(…\)`, display environments). Pure. */
export function proseOnly(text: string): string {
  return text
    .replace(/\\begin\{(equation|align|gather|multline|eqnarray|displaymath|flalign)(\*?)\}[\s\S]*?\\end\{\1\2\}/g, " ")
    .replace(/\$\$[\s\S]*?\$\$|\\\[[\s\S]*?\\\]|\\\([\s\S]*?\\\)|(?<!\\)\$(?:\\[\s\S]|[^$\\])+?\$/g, " ");
}

/** The declarations an account renders: its own, then the helpers proved inside it. */
const declsOf = (t: Task) => [t.decl, ...t.inline];
/** The declaration of account `t` an anchor (FILE as written, or none: the account's own file) lies in. */
function anchored(t: Task, file: string | undefined, a: number, b: number, leanRel: (f: string) => string): LeanDecl | undefined {
  const f = file ?? leanRel(t.decl.file);
  return a <= b ? declsOf(t).find((d) => leanRel(d.file) === f && a >= d.line && b <= d.end) : undefined;
}

/**
 * The problems of one entry against its account: the parts it must carry, references it may not make
 * (`mayCite`), anchors that are malformed or on no declaration of the account (or none on a proof), a
 * helper of the account its anchors never reach, and Lean in the prose (backticks, a tactic or library
 * word, a declaration name of the run's: `leanNames`). Pure.
 */
export function entryProblems(e: Entry, t: Task, mayCite: ReadonlySet<string>, leanNames: ReadonlySet<string>, leanRel: (f: string) => string, mustCite: readonly string[] = []): string[] {
  const bad: string[] = [];
  if (!e.proof?.trim()) bad.push(t.role === "result" ? "a paper result needs its proof" : "a shared lemma needs its proof");
  if (t.role === "shared" && !e.statement?.trim()) bad.push("a shared lemma needs its statement");
  const reached = new Set<LeanDecl>();
  for (const [part, text] of [["statement", e.statement], ["proof", e.proof]] as const) {
    if (!text) continue;
    for (const m of text.matchAll(REF_RE)) {
      const id = m[1]!;
      if (id === t.id) bad.push(`${part}: ⟦${id}⟧ cites itself`);
      else if (!mayCite.has(id)) bad.push(`${part}: ⟦${id}⟧ is no id you may cite`);
    }
    for (const m of text.matchAll(ANCHOR_RE)) {
      const d = anchored(t, m[2], Number(m[3]), Number(m[4] ?? m[3]), leanRel);
      if (d) reached.add(d);
      else bad.push(`${part}: anchor lean:${m[2] ? `${m[2]}:` : ""}${m[3]}${m[4] ? `-${m[4]}` : ""} is on no declaration of this account (the lines listed under its task)`);
    }
    const unanchored = text.replace(ANCHOR_RE, "$1");
    if (/\]\(lean:/.test(unanchored)) bad.push(`${part}: anchor markup that does not parse (keep brackets inside a phrase balanced; intervals go in math)`);
    const prose = proseOnly(unanchored);
    if (prose.includes("`")) bad.push(`${part}: backticks (Lean) in the text`);
    const word = LEAN_WORDS.exec(prose)?.[0];
    if (word) bad.push(`${part}: "${word}" is Lean, not English`);
    const name = (prose.match(IDENT_RE) ?? []).find((w) => leanNames.has(w));
    if (name) bad.push(`${part}: "${name}" is a Lean declaration name`);
  }
  if (e.proof?.trim()) {
    if (!reached.has(t.decl)) bad.push(`proof: no anchor on its own declaration (lines ${t.decl.line}-${t.decl.end})`);
    for (const d of t.inline) if (!reached.has(d)) bad.push(`proof: the helper \`${d.name}\` (${leanRel(d.file)} lines ${d.line}-${d.end}) is not proved in it (no anchor on its lines)`);
    const cites = new Set([...`${e.statement ?? ""} ${e.proof}`.matchAll(REF_RE)].map((m) => m[1]!));
    for (const id of mustCite) if (!cites.has(id)) bad.push(`proof: ⟦${id}⟧, a part of this proof written separately, is never cited where the Lean uses it`);
  }
  return bad;
}

/** Names of the run's Lean declarations a prose text could carry by mistake: those that read as no
 *  English word (an underscore, an inner capital). Pure. */
export function leanNameSet(decls: readonly LeanDecl[]): Set<string> {
  return new Set(decls.map((d) => d.leaf).filter((n) => n.length >= 4 && (/_/.test(n) || /[a-z][A-Z]/.test(n))));
}

/** An entry as kept: the parts its account carries (a result's statement is the paper's), each anchor
 *  on no declaration of the account left as its phrase. Pure. */
function kept(e: Entry, t: Task, leanRel: (f: string) => string): Entry {
  const clean = (s: string | null) => s?.replace(ANCHOR_RE, (all, phrase: string, f: string | undefined, a: string, b?: string) => (anchored(t, f, Number(a), Number(b ?? a), leanRel) ? all : phrase)) ?? null;
  return { id: e.id, statement: t.role === "result" ? null : clean(e.statement), proof: clean(e.proof) };
}

/** The entries of a reply for `tasks` that pass (`entryProblems`), and one problem line per account that
 *  does not. `lenient` (the second answer): an entry is kept when it carries its proof, its problems
 *  noted. `mayCite(t)`: the ids account `t` may cite. Pure. */
export function checkEntries(tasks: readonly Task[], reply: unknown, mayCite: (t: Task) => ReadonlySet<string>, leanNames: ReadonlySet<string>, leanRel: (f: string) => string, lenient = false, mustCite: (t: Task) => readonly string[] = () => []): { ok: Map<string, Entry>; problems: string[] } {
  const ok = new Map<string, Entry>();
  const problems: string[] = [];
  const got = new Map<string, Entry>();
  const entries = (reply as { entries?: unknown })?.entries;
  if (Array.isArray(entries)) for (const e of entries as Entry[]) if (e && typeof e.id === "string" && !got.has(e.id)) got.set(e.id, { id: e.id, statement: typeof e.statement === "string" ? e.statement : null, proof: typeof e.proof === "string" ? e.proof : null });
  for (const t of tasks) {
    const e = got.get(t.id);
    if (!e) { problems.push(`${t.id}: no entry`); continue; }
    const bad = entryProblems(e, t, mayCite(t), leanNames, leanRel, mustCite(t));
    if (bad.length) problems.push(`${t.id}: ${bad.join("; ")}`);
    if (bad.length === 0 || (lenient && e.proof?.trim())) ok.set(t.id, kept(e, t, leanRel));
  }
  return { ok, problems };
}

// ── prompts ──────────────────────────────────────────────────────────────────

const flat = (s: string) => s.replace(/\\label\{[^}]*\}/g, "").replace(/\s+/g, " ").trim();
const nodeWord = (r: PaperRef) => `${r.kind}${r.label ? ` \`${r.label}\`` : ""}`;
const where = (d: LeanDecl, leanRel: (f: string) => string) => `Lean \`${d.name}\` (${d.kind}), ${leanRel(d.file)} lines ${d.line}-${d.end}`;
/** A declaration's source with its file's line numbers, as the prompts show it. Pure. */
export const numbered = (d: LeanDecl, leanRel: (f: string) => string): string =>
  `${leanRel(d.file)}:\n\`\`\`lean\n${d.source.split("\n").map((l, i) => `${d.line + i}| ${l}`).join("\n")}\n\`\`\``;
/** A declaration's statement: its source up to the first `:=`, or up to a pattern match's first line
 *  (`| … =>`), outside brackets, comments and strings. Pure. */
export function statementOf(d: LeanDecl): string {
  const m = maskLeanCommentsAndStrings(d.source);
  let depth = 0;
  for (let i = 0; i < m.length; i++) {
    const ch = m[i]!;
    if ("([{⟨".includes(ch)) depth++;
    else if (")]}⟩".includes(ch)) depth = Math.max(0, depth - 1);
    else if (depth > 0) continue;
    else if (ch === ":" && m[i + 1] === "=") return d.source.slice(0, i).trimEnd();
    else if (ch === "\n") {
      const end = m.indexOf("\n", i + 1);
      if (/^[ \t]*\|.*=>/.test(m.slice(i + 1, end === -1 ? m.length : end))) return d.source.slice(0, i).trimEnd();
    }
  }
  return d.source.trimEnd();
}
/** The paper's definitions the declarations `ds` mention (none of `ds`), in order, at most `cap` lines in all. */
export function usedDefs(ds: readonly LeanDecl[], byLeaf: ReadonlyMap<string, readonly LeanDecl[]>, cap = DEF_LINES): LeanDecl[] {
  const out: LeanDecl[] = [];
  let n = 0;
  for (const d of ds) for (const x of mentions(d, byLeaf)) {
    if (!DEF_KINDS.has(x.kind) || ds.includes(x) || out.includes(x) || n + x.end - x.line + 1 > cap) continue;
    out.push(x); n += x.end - x.line + 1;
  }
  return out;
}

/** The context and the account of one translator (or review) call. `leanRel`: a file of the paper's
 *  Lean as the toolkit root names it. Pure. */
export function translatorBlocks(call: readonly Task[], plan: Plan, refs: ReadonlyMap<string, PaperRef>, leanRel: (file: string) => string, defs: readonly LeanDecl[] = []): { context: string; tasks: string } {
  const inCall = new Set(call.map((t) => t.id));
  const refIds = new Set<string>(), auxIds = new Set<string>();
  for (const t of call) for (const x of plan.uses.get(t.id)?.refs ?? []) refIds.add(x);
  for (const t of call) for (const x of plan.uses.get(t.id)?.aux ?? []) if (!inCall.has(x)) auxIds.add(x);
  const paper = [...refIds].map((id) => refs.get(id)).filter((r): r is PaperRef => Boolean(r));
  const sharedById = new Map(plan.shared.map((a) => [a.id, a] as const));
  const context = [
    "PAPER NODES the tasks may cite (as ⟦id⟧; each task only the ids listed under it):",
    ...(paper.length ? paper.map((r) => `- ⟦${r.id}⟧ ${nodeWord(r)}${r.cite ? ` — cited from ${r.cite}; Lean assumes it` : ""}: ${flat(r.statement)}`) : ["(none)"]),
    "",
    "SHARED LEMMAS written in other calls (cite as ⟦A<n>⟧; do not restate or reprove them):",
    ...(auxIds.size ? [...auxIds].map((id) => { const a = sharedById.get(id)!; return `- ⟦${id}⟧ (${where(a.decl, leanRel)})${a.decl.doc ? `: ${a.decl.doc}` : ""}\n\`\`\`lean\n${statementOf(a.decl)}\n\`\`\``; }) : ["(none)"]),
    "",
    "DEFINITIONS of the paper's Lean that the tasks use (others: read them in the sources):",
    ...(defs.length ? defs.map((d) => numbered(d, leanRel)) : ["(none)"]),
  ].join("\n");
  const tasks = call.map((t) => {
    const head = t.role === "result"
      ? `### ⟦${t.id}⟧ — the proof of the paper's ${nodeWord(refs.get(t.id) ?? { id: t.id, kind: "result", label: null, statement: "" })}; ${where(t.decl, leanRel)}\nIts statement (the paper's): ${flat(t.statement ?? refs.get(t.id)?.statement ?? "")}`
      : `### ⟦${t.id}⟧ — a shared lemma: its statement and its proof; ${where(t.decl, leanRel)}`;
    const helpers = t.inline.length ? `\nHelpers to prove inside it (${t.inline.length}):\n${t.inline.map((d) => `- ${where(d, leanRel)}`).join("\n")}` : "\nHelpers to prove inside it: none";
    const may = [...(plan.uses.get(t.id)?.refs ?? []), ...(plan.uses.get(t.id)?.aux ?? [])];
    const must = plan.parts.get(t.id) ?? [];
    return `${head}${helpers}\nIt may cite: ${may.length ? may.map((x) => `⟦${x}⟧`).join(", ") : "none"}${must.length ? `\nParts of it written separately (cite each where the Lean uses it): ${must.map((x) => `⟦${x}⟧`).join(", ")}` : ""}\nIts Lean:\n${declsOf(t).map((d) => numbered(d, leanRel)).join("\n")}`;
  }).join("\n\n");
  return { context, tasks };
}

/** An English text for the comparator: references by name, anchors as their phrase. Pure. */
export function readable(text: string, refs: ReadonlyMap<string, PaperRef>): string {
  return text.replace(ANCHOR_RE, "$1").replace(REF_RE, (_, id: string) => (/^A\d+$/.test(id) ? `Auxiliary ${id}` : refs.get(id) ? `${refs.get(id)!.kind} ${refs.get(id)!.label ?? id}` : id));
}

/** The shared ids an account takes: those its proof cites, and theirs, in order of first citation. Pure. */
export function auxClosure(proof: string, aux: ReadonlyMap<string, Entry>): string[] {
  const out: string[] = [];
  const visit = (text: string | null) => {
    for (const m of (text ?? "").matchAll(REF_RE)) {
      const id = m[1]!;
      if (!/^A\d+$/.test(id) || out.includes(id) || !aux.has(id)) continue;
      out.push(id);
      visit(aux.get(id)!.statement);
      visit(aux.get(id)!.proof);
    }
  };
  visit(proof);
  return out;
}

/** Every shared id an account cites, directly or through the shared lemmas it cites, written or not. Pure. */
export function citedShared(proof: string, aux: ReadonlyMap<string, Entry>): string[] {
  const out: string[] = [];
  const visit = (text: string | null) => {
    for (const m of (text ?? "").matchAll(REF_RE)) {
      const id = m[1]!;
      if (!/^A\d+$/.test(id) || out.includes(id)) continue;
      out.push(id);
      visit(aux.get(id)?.statement ?? null);
      visit(aux.get(id)?.proof ?? null);
    }
  };
  visit(proof);
  return out;
}

// ── the review of the English ────────────────────────────────────────────────

/** The reviewer's verdict on one account, judged against the Lean alone: faithful or not (`issues`),
 *  and, second, what a reader would stumble on (`readability`: self-containment, structure, notation),
 *  which never makes it unfaithful. `rewritten`: written again from an earlier review's findings. */
export interface Review { faithful: boolean; issues: string[]; readability: string[]; rewritten?: true }

export const PROOF_REVIEW_SCHEMA: Record<string, unknown> = {
  type: "object", additionalProperties: false, required: ["reviews"],
  properties: {
    reviews: { type: "array", items: {
      type: "object", additionalProperties: false, required: ["id", "faithful", "issues", "readability"],
      properties: { id: { type: "string" }, faithful: { type: "boolean" }, issues: { type: "array", items: { type: "string" } }, readability: { type: "array", items: { type: "string" } } },
    } },
  },
};

/** The entries block of one review call: each account with where its Lean stands. Pure. */
export function reviewBlock(tasks: readonly Task[], entries: ReadonlyMap<string, Entry>, leanRel: (file: string) => string): string {
  return tasks.filter((t) => entries.has(t.id)).map((t) => {
    const e = entries.get(t.id)!;
    const what = t.role === "result" ? "the proof of a paper result (its statement is the paper's, audited separately)" : "a shared lemma";
    const helpers = t.inline.length ? [`Helpers it proves inside (${t.inline.length}):`, ...t.inline.map((d) => `- ${where(d, leanRel)}`)] : [];
    return [`### ⟦${t.id}⟧ — ${what}; ${where(t.decl, leanRel)}`, ...helpers, "Its Lean:", ...declsOf(t).map((d) => numbered(d, leanRel)), ...(e.statement ? ["Statement:", e.statement] : []), ...(e.proof ? ["Proof:", e.proof] : [])].join("\n");
  }).join("\n\n");
}

/** The reviews of a reply for the accounts `ids`; an id with no well-formed review is absent. A review
 *  that says unfaithful with no issue reads as faithful. Pure. */
export function checkReviews(ids: readonly string[], reply: unknown): Map<string, Review> {
  const out = new Map<string, Review>();
  const reviews = (reply as { reviews?: unknown })?.reviews;
  if (!Array.isArray(reviews)) return out;
  for (const r of reviews as Array<Record<string, unknown>>) {
    if (!r || typeof r.id !== "string" || !ids.includes(r.id) || out.has(r.id) || typeof r.faithful !== "boolean") continue;
    const lines = (v: unknown) => (Array.isArray(v) ? v : []).filter((x): x is string => typeof x === "string" && x.trim() !== "").map((x) => x.replace(/\s+/g, " ").trim());
    const issues = lines(r.issues);
    out.set(r.id, { faithful: r.faithful || issues.length === 0, issues: r.faithful ? [] : issues, readability: lines(r.readability) });
  }
  return out;
}

// ── the comparator ───────────────────────────────────────────────────────────

export type Verdict = "follows" | "other-route" | "departs";
export interface Departure { kind: "printed-wrong" | "printed-gap"; printed: string; intended: string; reason: string }
/** `routes`: printed steps the Lean argues another way (the printed text enough for its own way).
 *  `unclear`: printed steps that leave out an argument or a detail the step needs (a reply's `error`
 *  with `missing` among them), or whose wording is loose or admits a weaker reading, with what the Lean uses there (`lean`) and the wording suggested (`suggestion`) — notes for
 *  the reader, never corrections of the paper. */
export interface Comparison { verdict: Verdict; summary: string; routes: Array<{ printed: string; lean: string }>; unclear: Array<{ printed: string; lean: string; suggestion?: string }>; departures: Departure[] }

export const PROOF_COMPARE_SCHEMA: Record<string, unknown> = {
  type: "object", additionalProperties: false, required: ["results"],
  properties: {
    results: { type: "array", items: {
      type: "object", additionalProperties: false, required: ["id", "summary", "differences"],
      properties: {
        id: { type: "string" },
        summary: { type: "string" },
        differences: { type: "array", items: {
          type: "object", additionalProperties: false, required: ["printed", "lean", "kind", "missing", "suggestion", "reason"],
          properties: {
            printed: { type: "string" }, lean: { type: "string" }, kind: { type: "string", enum: ["difference", "ambiguity", "error"] },
            missing: { type: "boolean" }, suggestion: { type: "string" }, reason: { type: "string" },
          },
        } },
      },
    } },
  },
};

/** One result for the comparator: its proof as printed (what a snippet is copied from), as the referee
 *  corrected it when that differs, the corrections already recorded on it, the printed statements of
 *  the paper nodes it cites, and its English account, every piece of it confirmed faithful by the
 *  review. */
export interface CompareItem { id: string; ref: PaperRef; printed: string; corrected: string | null; recorded: Array<{ printed: string; intended: string }>; cited: PaperRef[]; account: string }

/** The prompt block of one result. Pure. */
export function compareBlock(it: CompareItem): string {
  return [
    `## ${it.id} (${nodeWord(it.ref)})`,
    `Statement: ${flat(it.ref.statement)}`,
    "Printed proof:",
    it.printed.trim(),
    ...(it.corrected ? ["The proof as the paper's referee corrected it (the Lean formalizes this one; its changes are no difference):", it.corrected.trim()] : []),
    `Corrections already recorded on it: ${it.recorded.length ? it.recorded.map((r) => `"${flat(r.printed)}" → "${flat(r.intended)}"`).join("; ") : "none"}`,
    ...(it.cited.length ? ["Printed statements of the paper's nodes it cites:", ...it.cited.map((r) => `- ${nodeWord(r)}${r.cite ? ` (cited from ${r.cite})` : ""}: ${flat(r.statement)}`)] : []),
    "Lean Proof in English:",
    it.account,
  ].join("\n");
}

/** The comparisons of a reply for `items` that are well formed, and one problem line per item that is
 *  not. An error becomes a departure, one with no snippet or no suggested text dropped (noted); an
 *  error that leaves the step out (`missing`) is an unclear step, as an ambiguity is; a difference is a
 *  route. Verdict: `departs` with a departure, else `other-route` with a route, else `follows`. Pure. */
export function checkComparisons(items: readonly CompareItem[], reply: unknown): { ok: Map<string, Comparison>; problems: string[] } {
  const ok = new Map<string, Comparison>();
  const problems: string[] = [];
  const results = (reply as { results?: unknown })?.results;
  const byId = new Map<string, Record<string, unknown>>();
  if (Array.isArray(results)) for (const r of results as Array<Record<string, unknown>>) if (r && typeof r.id === "string" && !byId.has(r.id)) byId.set(r.id, r);
  const str = (v: unknown) => (typeof v === "string" ? v : "");
  for (const it of items) {
    const r = byId.get(it.id);
    if (!r || !Array.isArray(r.differences)) { problems.push(`${it.id}: no answer`); continue; }
    const diffs = (r.differences as Array<Record<string, unknown>>).filter((d) => d && ["difference", "ambiguity", "error"].includes(str(d.kind))).map((d) => ({
      kind: str(d.kind), printed: str(d.printed).trim(), lean: str(d.lean).trim(), missing: d.missing === true, suggestion: str(d.suggestion).trim(), reason: str(d.reason).replace(/\s+/g, " ").trim(),
    }));
    // an omission is no error: a step the printed proof leaves out is an unclear step, whatever its kind
    const omitted = diffs.filter((d) => d.kind === "error" && d.missing);
    const errors = diffs.filter((d) => d.kind === "error" && !d.missing);
    const good = errors.filter((d) => d.printed && d.suggestion);
    if (good.length < errors.length) problems.push(`${it.id}: ${errors.length - good.length} error(s) with no snippet or no suggested text dropped`);
    const departures: Departure[] = good.map((d) => ({ kind: "printed-wrong", printed: d.printed, intended: d.suggestion, reason: d.reason }));
    const routes = diffs.filter((d) => d.kind === "difference" && (d.printed || d.lean)).map((d) => ({ printed: d.printed, lean: d.lean }));
    const unclear = [...diffs.filter((d) => d.kind === "ambiguity"), ...omitted].filter((d) => d.printed || d.lean).map((d) => ({ printed: d.printed, lean: d.lean, ...(d.suggestion ? { suggestion: d.suggestion } : {}) }));
    const verdict: Verdict = departures.length ? "departs" : routes.length ? "other-route" : "follows";
    ok.set(it.id, { verdict, summary: str(r.summary).trim(), routes, unclear, departures });
  }
  return { ok, problems };
}

/** Results in calls of at most `budget` characters of printed proof and account, in order; one over it
 *  goes alone. Pure. */
export function batchByChars<T extends { printed: string; account: string }>(items: readonly T[], budget = COMPARE_CHARS_PER_CALL): T[][] {
  const out: T[][] = [];
  let used = 0;
  for (const it of items) {
    const n = it.printed.length + it.account.length;
    if (out.length === 0 || used + n > budget) { out.push([]); used = 0; }
    out.at(-1)!.push(it);
    used += n;
  }
  return out;
}

const GAP_PREFIX = "gap in the printed proof: ";
const isWrong = (d: Departure): boolean => d.kind === "printed-wrong";
const WRONG_PREFIX = "wrong as printed: ";

/** The departures of a node as the paper now carries them: every correction from the Lean recorded on
 *  its proof (this pass's, an earlier pass's, the proof filler's), `placed` when the corrected paper
 *  prints it (blue). Pure. */
export function leanCorrections(file: PatchFile | null, node: string): StoredDeparture[] {
  return (file?.typo_fixes ?? []).filter((f) => f.node === node).flatMap((f) => f.typos).filter((t) => t.source === "lean").map((t) => ({
    kind: t.reason.startsWith(GAP_PREFIX) ? "printed-gap" as const : "printed-wrong" as const,
    printed: t.printed, intended: t.intended, reason: t.reason.replace(GAP_PREFIX, "").replace(WRONG_PREFIX, ""), placed: t.unit !== null,
  }));
}

/** Where the runner would place a node's new departures in its printed proof (one dry run of
 *  `withRefereeTypos` with all of them): the snippets it cannot place. Pure; never throws. */
export function unplaced(file: PatchFile | null, src: PassageSources, node: string, deps: readonly Departure[]): string[] {
  try {
    const added = withRefereeTypos(file, [{ id: node, typos: deps }], src, "lean").added;
    return deps.filter((d) => added.find((a) => sameWords(a.printed, d.printed))?.unit == null).map((d) => d.printed);
  } catch { return deps.map((d) => d.printed); }
}

// ── the artifact ─────────────────────────────────────────────────────────────

/** A departure as stored: `placed` when the corrected paper carries it (blue), else reported only. */
export interface StoredDeparture extends Departure { placed: boolean }
/** A helper proved inside an account: where its Lean stands (what an anchor on its lines opens). */
export interface StoredInline { decl: string; kind: string; file: string; line: number; end: number; source: string }
/** One account as stored. `inline`: the helpers proved inside it. */
export interface StoredPiece { id: string; decl: string; kind: string; file: string; line: number; end: number; source: string; statement: string | null; proof: string | null; review: Review | null; inline?: StoredInline[] }
export interface StoredResult extends StoredPiece {
  /** The shared ids its account takes, in order (`auxClosure`). */
  aux: string[];
  /** Null: no printed proof to compare (`no_printed_proof`), or no comparator answer. */
  comparison: (Omit<Comparison, "departures"> & { departures: StoredDeparture[] }) | null;
  no_printed_proof?: true;
  /** A block a repair split off this printed result: the printed proof is that result's, not compared
   *  block by block. */
  split_from?: string;
}
export interface LeanProofEnglish {
  written: string;
  results: StoredResult[];
  /** The shared helper lemmas. */
  auxiliary: StoredPiece[];
  /** The paper nodes the accounts cite, as the page names them when it has no heading for one. */
  refs: Record<string, { kind: string; label: string | null }>;
  problems: string[];
}

/** One retry's note to the model. */
const retryNote = (problems: readonly string[]): string => `\n\nYour previous answer was not accepted:\n${problems.map((p) => `- ${p}`).join("\n")}\nAnswer these ids again in full.`;

type CoreStmt = { id: string; kind: string; statement: string; depends_on?: readonly string[]; tex_locator?: { label?: string | null } | null; source?: { cite?: string; locator?: string } | null; proof_tex?: string | null; umbrella?: boolean; split_from?: string };

/** The paper's nodes the English may cite — the core's results (a cited one with its citation), the
 *  graph's from-note nodes and cited gates — and the paper node each Lean declaration formalizes. */
function paperNodes(nodes: readonly GraphNode[], statements: readonly CoreStmt[]): { refs: Map<string, PaperRef>; nodeOfDecl: Map<string, string> } {
  const refs = new Map<string, PaperRef>();
  const nodeOfDecl = new Map<string, string>();
  const cite = (s: CoreStmt | undefined) => (s?.source?.cite ? `${s.source.cite}${s.source.locator ? `, ${s.source.locator}` : ""}` : undefined);
  for (const s of statements) refs.set(s.id, { id: s.id, kind: s.kind, label: s.tex_locator?.label ?? null, statement: s.statement, ...(cite(s) ? { cite: cite(s) } : {}) });
  const st = new Map(statements.map((s) => [s.id, s] as const));
  for (const n of nodes) {
    // a helper the F stages introduced is no node of the paper: it is a helper lemma of an account
    if (n.provenance !== "from-note" && n.kind !== "gate") continue;
    if (n.lean?.decl_name) nodeOfDecl.set(n.lean.decl_name, n.id);
    if (refs.has(n.id)) continue;
    const c = cite(st.get(n.id)) ?? (n.kind === "gate" ? n.gate?.source ?? n.standard?.citation : undefined);
    refs.set(n.id, { id: n.id, kind: n.kind, label: null, statement: n.nl?.statement ?? "", ...(c ? { cite: c } : {}) });
  }
  return { refs, nodeOfDecl };
}

/**
 * Write the run's Lean Proof in English, review it against the Lean and compare it with the printed
 * proofs: `<run>/lean_proof_english.json` (written on every path, so no earlier pass's stays);
 * wrong printed steps recorded as corrections from the Lean proof (`recordLeanStepFixes`). Returns a one-line
 * summary. A failing call or step is a problem in the artifact, never a throw past here; `only` naming
 * no result with a Lean proof throws before anything is written.
 */
export async function emitLeanProofEnglish(args: { ctx: PipelineContext; state: StateJson; deps: StageDeps; only?: ReadonlySet<string> }): Promise<string> {
  const paths = artifactPaths(args.ctx, args.state);
  const file = path.join(paths.formalizationDir, LEAN_PROOF_ENGLISH_ARTIFACT);
  const problems: string[] = [];
  const write = (a: Omit<LeanProofEnglish, "written" | "problems">) => writeFile(file, JSON.stringify({ written: new Date().toISOString(), ...a, problems }, null, 1) + "\n", "utf8");
  const graph = await loadGraph(graphPath(paths.formalizationDir));
  const core = await readTypedCore(coreJsonPath(args.ctx));
  const statements = core.statements as unknown as CoreStmt[];
  const { refs, nodeOfDecl } = paperNodes(graph.nodes, statements);
  const coreOf = new Map(statements.map((s) => [s.id, s] as const));
  const resultNodes = graph.nodes.filter((n) => n.provenance === "from-note" && PROOF_KINDS.has(n.kind) && n.lean?.decl_name && !coreOf.get(n.id)?.umbrella && (!args.only || args.only.has(n.id)));
  // a misspelled `only` leaves the artifact as it is
  const unknown = [...(args.only ?? [])].filter((id) => !resultNodes.some((n) => n.id === id));
  if (unknown.length) throw new Error(`${unknown.join(", ")}: no paper result with a Lean proof in this run; nothing written`);
  const decls = await readLeanDecls(paths.leanDir);
  const plan = planTasks(decls, nodeOfDecl, resultNodes.map((n) => ({ id: n.id, decl: n.lean.decl_name!, statement: refs.get(n.id)?.statement ?? n.nl.statement, deps: (coreOf.get(n.id)?.depends_on ?? []).filter((d) => refs.has(d)) })));
  if (plan.results.length === 0) {
    await write({ results: [], auxiliary: [], refs: {} });
    return "no paper result with a Lean proof to write in English";
  }
  const leanRel = (f: string) => path.relative(args.ctx.repoRoot, path.join(paths.leanDir, f)).replaceAll(path.sep, "/");
  const [tplEnglish, tplReview, tplCompare] = await Promise.all(["stage5_proof_english.txt", "stage5_proof_english_review.txt", "stage5_proof_compare.txt"].map((n) => readPrompt(args.ctx, n)));
  const ask = async (label: string, prompt: string, schema: Record<string, unknown>, source: string, leanLsp: boolean): Promise<unknown> => {
    try {
      const out = await dispatchAgent({
        ctx: args.ctx, deps: args.deps, stage: "5", label, prompt, promptSources: [source, "graph.json", "core.json", "Lean sources"],
        model: MODEL_PLAN.stage5.model, reasoningEffort: "high", sandboxMode: "read-only", leanLsp, outputSchema: schema,
      });
      return parseAgentJson(out.stdout).json ?? null;
    } catch (e) {
      problems.push(`${label}: the call failed (${String((e as Error)?.message ?? e).split("\n")[0]!.slice(0, 200)})`);
      return null;
    }
  };

  // 1–2. the translator, and the review of what it wrote against the Lean: an account the review finds
  // unfaithful, or a reader would stumble on, is revised from its findings and reviewed again, up to MAX_REWRITES times
  const leanNames = leanNameSet(decls);
  const byLeaf = new Map<string, LeanDecl[]>();
  for (const d of decls) (byLeaf.get(d.leaf) ?? byLeaf.set(d.leaf, []).get(d.leaf)!).push(d);
  const blocks = (ts: readonly Task[]) => translatorBlocks(ts, plan, refs, leanRel, usedDefs(ts.flatMap(declsOf), byLeaf));
  const mayCite = (t: Task) => new Set([...(plan.uses.get(t.id)?.refs ?? []), ...(plan.uses.get(t.id)?.aux ?? [])]);
  const mustCite = (t: Task) => plan.parts.get(t.id) ?? [];
  const entries = new Map<string, Entry>();
  const reviews = new Map<string, Review>();
  /** `note`: what the prompt for the tasks asked about ends with (a revision's findings and earlier text). */
  const translate = async (tasks: readonly Task[], label: string, note: (ts: readonly Task[]) => string = () => ""): Promise<Map<string, Entry>> => {
    const prompt = (ts: readonly Task[]) => fillTemplate(tplEnglish, blocks(ts)) + note(ts);
    const first = checkEntries(tasks, await ask(label, prompt(tasks), PROOF_ENGLISH_SCHEMA, "stage5_proof_english.txt", true), mayCite, leanNames, leanRel, false, mustCite);
    if (first.problems.length === 0) return first.ok;
    const again = tasks.filter((t) => !first.ok.has(t.id));
    const second = again.length ? checkEntries(again, await ask(`${label} again`, prompt(again) + retryNote(first.problems), PROOF_ENGLISH_SCHEMA, "stage5_proof_english.txt", true), mayCite, leanNames, leanRel, true, mustCite) : { ok: new Map(), problems: [] };
    problems.push(...first.problems.map((p) => `english ${p}`), ...second.problems.map((p) => `english (asked again) ${p}`));
    return new Map([...first.ok, ...second.ok]);
  };
  const review = async (tasks: readonly Task[], label: string): Promise<Map<string, Review>> => {
    const done = tasks.filter((t) => entries.has(t.id));
    if (done.length === 0) return new Map();
    const once = async (ts: readonly Task[], l: string) => checkReviews(ts.map((t) => t.id), await ask(l, fillTemplate(tplReview, { context: blocks(ts).context, entries: reviewBlock(ts, entries, leanRel) }), PROOF_REVIEW_SCHEMA, "stage5_proof_english_review.txt", true));
    const got = await once(done, label);
    // asked again for an entry with no review (a failed call leaves a whole pack unreviewed)
    const lost = done.filter((t) => !got.has(t.id));
    if (lost.length) for (const [id, r] of await once(lost, `${label} again`)) got.set(id, r);
    const missing = done.filter((t) => !got.has(t.id)).map((t) => t.id);
    if (missing.length) problems.push(`${label}: no review of ${missing.join(", ")}`);
    return got;
  };
  await mapLimit(plan.calls, CALL_CONCURRENCY, async (call) => {
    const at = call.map((t) => t.id).join(", ");
    for (const [id, e] of await translate(call, `F5 Lean proof in English ${at}`)) entries.set(id, e);
    let last = await review(call, `F5 Lean proof in English review ${at}`);
    // the last text of each account a review confirmed faithful, with that review
    const kept = new Map<string, { entry: Entry; review: Review }>();
    const keep = (id: string) => { const e = entries.get(id), r = reviews.get(id); if (e && r?.faithful === true) kept.set(id, { entry: e, review: r }); };
    for (const [id, r] of last) { reviews.set(id, r); keep(id); }
    // revised from the review's findings and reviewed again, up to MAX_REWRITES times: an account found
    // unfaithful, or one a reader would stumble on
    let pending: readonly Task[] = call;
    for (let round = 1; round <= MAX_REWRITES; round++) {
      const flagged = pending.filter((t) => last.get(t.id)?.faithful === false || (last.get(t.id)?.readability.length ?? 0) > 0);
      if (flagged.length === 0) return;
      const found = new Map(flagged.map((t) => { const r = last.get(t.id)!; return [t.id, `${t.id}: ${[...r.issues.map((x) => `unfaithful — ${x}`), ...r.readability.map((x) => `for the reader — ${x}`)].join("; ")}`] as const; }));
      // a revision: the earlier text with what the review found, the rest kept as it is
      const earlier = (t: Task) => { const e = entries.get(t.id); return [`Earlier text of ⟦${t.id}⟧:`, ...(e?.statement ? ["Statement:", e.statement] : []), ...(e?.proof ? ["Proof:", e.proof] : [])].join("\n"); };
      const note = (ts: readonly Task[]) => `\n\nA review of your earlier text against the Lean found these defects (faithfulness first; never trade it for readability):\n${ts.map((t) => `- ${found.get(t.id)}`).join("\n")}\n\nRevise your earlier text, given below: correct each defect where it occurs, and keep everything else as it is. Answer each of these ids again in full.\n\nYOUR EARLIER TEXT:\n\n${ts.map(earlier).join("\n\n")}`;
      const tag = round === 1 ? "rewrite" : `rewrite ${round}`;
      const redone = await translate(flagged, `F5 Lean proof in English ${at} ${tag}`, note);
      for (const [id, e] of redone) entries.set(id, e);
      last = await review(flagged.filter((t) => redone.has(t.id)), `F5 Lean proof in English review ${at} ${tag}`);
      const restored: string[] = [];
      for (const t of flagged) {
        if (!redone.has(t.id)) continue; // not written again: the earlier review stands on the earlier text
        // a revision for the reader that is not confirmed faithful: the faithful earlier text stands
        const k = kept.get(t.id);
        if (k && last.get(t.id)?.faithful !== true) { entries.set(t.id, k.entry); reviews.set(t.id, k.review); restored.push(t.id); continue; }
        // the text now is the rewrite: only a review of it says anything about it
        if (last.has(t.id)) reviews.set(t.id, { ...last.get(t.id)!, rewritten: true });
        else reviews.delete(t.id);
        keep(t.id);
      }
      if (restored.length) problems.push(`F5 Lean proof in English ${at} ${tag}: the revision of ${restored.join(", ")} was not confirmed faithful; the earlier faithful text stands`);
      pending = flagged.filter((t) => redone.has(t.id) && last.has(t.id) && !restored.includes(t.id));
    }
  });

  // a result sharing its declaration with an earlier one takes that result's account and review
  for (const [id, of] of plan.aliases) {
    const e = entries.get(of), r = reviews.get(of);
    if (e) entries.set(id, { ...e, id });
    if (r) reviews.set(id, r);
  }

  // 3. the comparator
  const sharedIds = new Set(plan.shared.map((a) => a.id));
  const aux = new Map([...entries].filter(([id]) => sharedIds.has(id)));
  const compared = new Map<string, Comparison>();
  let notConfirmed = 0;
  const runDir = verifyRunDir(args.ctx.repoRoot, args.ctx.qid);
  let patchFile: PatchFile | null = null;
  // the transcription's proofs, whenever the run has one (it is read here, not only through the
  // passage sources, so a run whose units do not read still compares only what the paper prints)
  const transcribedFile = path.join(runDir, VERIFY_FILES.coreTranscribed);
  let printedOf: Map<string, string> | null = null;
  try {
    if (existsSync(transcribedFile)) printedOf = new Map((JSON.parse(await readFile(transcribedFile, "utf8")).statements as CoreStmt[]).map((s) => [s.id, s.proof_tex ?? ""] as const));
  } catch (e) { problems.push(`compare: ${VERIFY_FILES.coreTranscribed} does not read (${String((e as Error)?.message ?? e).slice(0, 160)}); the core's proofs are compared`); }
  /** The proof the paper prints: the transcription's; the core's only on a run with no transcription
   *  (a proof the paper omits and a repair wrote is never a printed one). */
  const printedProof = (id: string) => (printedOf ? printedOf.get(id) : coreOf.get(id)?.proof_tex) ?? "";
  const hasPrinted = (id: string) => Boolean(printedProof(id).trim());
  try {
    const src = existsSync(path.join(runDir, VERIFY_FILES.envsJson)) ? await repairSources(runDir) : null;
    patchFile = existsSync(path.join(runDir, VERIFY_FILES.patches)) ? await readPatchFile(runDir) : null;
    /** The corrections already recorded on a node's proof (the referee's typos, earlier Lean corrections). */
    const recordedOn = (node: string) => (patchFile?.typo_fixes ?? []).filter((f) => f.node === node).flatMap((f) => f.typos);
    const accountOf = (id: string): string => {
      const proof = entries.get(id)?.proof ?? "";
      return [readable(proof, refs), ...auxClosure(proof, aux).map((a) => { const e = aux.get(a)!; return `Auxiliary ${a}. ${readable(e.statement ?? "", refs)}\nProof. ${readable(e.proof ?? "", refs)}`; })].join("\n\n");
    };
    const printable = plan.results.filter((t) => entries.get(t.id)?.proof && hasPrinted(t.id));
    // compared only on an account the review confirmed faithful, piece by piece
    // (a shared lemma it cites with no entry, or none reviewed faithful, leaves it unconfirmed)
    const confirmed = (t: Task) => [t.id, ...citedShared(entries.get(t.id)!.proof!, aux)].every((id) => reviews.get(id)?.faithful === true);
    notConfirmed = printable.filter((t) => !confirmed(t)).length;
    const items: CompareItem[] = printable.filter(confirmed).map((t) => {
      const corrected = coreOf.get(t.id)?.proof_tex ?? "";
      const printed = printedProof(t.id);
      return {
        id: t.id, ref: refs.get(t.id)!, printed, corrected: corrected && !sameWords(corrected, printed) ? corrected : null, account: accountOf(t.id),
        recorded: recordedOn(t.id).map((x) => ({ printed: x.printed, intended: x.intended })),
        cited: [...new Set([t.id, ...auxClosure(entries.get(t.id)!.proof!, aux)].flatMap((x) => plan.uses.get(x)?.refs ?? []))].filter((r) => r !== t.id).map((r) => refs.get(r)).filter((r): r is PaperRef => Boolean(r?.statement)),
      };
    });
    // a departure already recorded on the proof is no new one
    const fresh = (node: string, c: Comparison): Comparison => ({ ...c, departures: c.departures.filter((d) => !recordedOn(node).some((x) => sameWords(x.printed, d.printed))) });
    const flatTex = path.join(runDir, VERIFY_FILES.flatTex);
    const paperAt = existsSync(flatTex) ? flatTex : null;
    const batches = batchByChars(items);
    await mapLimit(batches, CALL_CONCURRENCY, async (batch, k) => {
      const at = `${k + 1}/${batches.length}`;
      const prompt = (b: readonly CompareItem[]) => fillTemplate(tplCompare, { items: [...(paperAt ? [`The paper's full source: ${paperAt}`] : []), ...b.map(compareBlock)].join("\n\n") });
      const first = checkComparisons(batch, await ask(`F5 proof compare ${at}`, prompt(batch), PROOF_COMPARE_SCHEMA, "stage5_proof_compare.txt", false));
      problems.push(...first.problems.map((p) => `compare ${p}`));
      for (const [id, c] of first.ok) compared.set(id, fresh(id, c));
      // asked again: a result with no answer, and one with a snippet the runner cannot place
      for (const it of batch) {
        const c = compared.get(it.id);
        const lost = c && src ? unplaced(patchFile, src, it.id, c.departures.filter(isWrong)) : [];
        if (c && lost.length === 0) continue;
        const why = c ? lost.map((p) => `the snippet "${flat(p).slice(0, 160)}" is not printed exactly once, in one passage, in the printed proof shown: copy a longer verbatim snippet of the printed proof`).join("; ") : "no answer";
        const again = checkComparisons([it], await ask(`F5 proof compare ${at} again ${it.id}`, prompt([it]) + retryNote([`${it.id}: ${why}`]), PROOF_COMPARE_SCHEMA, "stage5_proof_compare.txt", false));
        if (again.ok.has(it.id)) compared.set(it.id, fresh(it.id, again.ok.get(it.id)!));
        problems.push(...again.problems.map((p) => `compare (asked again) ${p}`));
      }
    });
    // departures are corrections of the paper from the Lean proof (blue where placed)
    const fixes = [...compared].flatMap(([node, c]) => c.departures.filter(isWrong).map((d) => ({ node, printed: d.printed, intended: d.intended, reason: `${WRONG_PREFIX}${d.reason}` })));
    if (src && fixes.length) {
      await recordLeanStepFixes(runDir, fixes, (m) => problems.push(`record: ${m}`));
      patchFile = await readPatchFile(runDir);
    }
  } catch (e) {
    problems.push(`compare: ${String((e as Error)?.message ?? e).split("\n")[0]!.slice(0, 300)}`);
  }

  const piece = (t: Task): StoredPiece => ({
    id: t.id, decl: t.decl.name, kind: t.decl.kind, file: leanRel(t.decl.file), line: t.decl.line, end: t.decl.end, source: t.decl.source,
    statement: entries.get(t.id)?.statement ?? null, proof: entries.get(t.id)?.proof ?? null, review: reviews.get(t.id) ?? null,
    inline: t.inline.map((d) => ({ decl: d.name, kind: d.kind, file: leanRel(d.file), line: d.line, end: d.end, source: d.source })),
  });
  const results: StoredResult[] = plan.results.map((t) => {
    const c = compared.get(t.id);
    // what the paper now carries from the Lean (this pass's departures among them), or, on a run with
    // no paper to correct, this pass's departures unplaced
    // (an earlier version's gaps among them), then this pass's departures not recorded
    const recorded = existsSync(path.join(runDir, VERIFY_FILES.envsJson)) ? leanCorrections(patchFile, t.id) : [];
    // (a wrong step not recorded — no passage sources, or the recording failed — is listed unplaced)
    const listed = (c?.departures ?? []).filter((d) => !recorded.some((x) => sameWords(x.printed, d.printed))).map((d) => ({ ...d, placed: false }));
    const corrections = [...recorded, ...listed];
    const comparison = c || corrections.length ? { verdict: corrections.length ? "departs" as const : c!.verdict === "departs" ? (c!.routes.length ? "other-route" as const : "follows" as const) : c!.verdict, summary: c?.summary ?? "", routes: c?.routes ?? [], unclear: c?.unclear ?? [], departures: corrections } : null;
    return {
      ...piece(t), aux: auxClosure(entries.get(t.id)?.proof ?? "", aux), comparison,
      ...(hasPrinted(t.id) ? {} : { no_printed_proof: true as const, ...(coreOf.get(t.id)?.split_from ? { split_from: coreOf.get(t.id)!.split_from! } : {}) }),
    };
  });
  const cited = new Set<string>();
  for (const e of entries.values()) for (const text of [e.statement, e.proof]) for (const m of (text ?? "").matchAll(REF_RE)) if (refs.has(m[1]!)) cited.add(m[1]!);
  const auxiliary = plan.shared.map(piece);
  await write({ results, auxiliary, refs: Object.fromEntries([...cited].map((id) => [id, { kind: refs.get(id)!.kind, label: refs.get(id)!.label }])) });

  const pieces = [...results, ...auxiliary].filter((p) => p.statement || p.proof);
  const unconfirmed = pieces.filter((p) => p.review?.faithful === false).map((p) => p.id);
  const unreviewed = pieces.filter((p) => !p.review).length;
  const hard = pieces.filter((p) => p.review?.faithful && p.review.readability.length > 0).length;
  const count = (v: Verdict) => results.filter((r) => r.comparison?.verdict === v).length;
  const deps = results.flatMap((r) => r.comparison?.departures ?? []);
  const unclear = results.reduce((n, r) => n + (r.comparison?.unclear.length ?? 0), 0);
  const inlineCount = [...plan.results, ...plan.shared].reduce((n, t) => n + t.inline.length, 0);
  return `${results.filter((r) => r.proof).length}/${results.length} result(s) written in English (${inlineCount} helper(s) proved inside them, ${auxiliary.filter((a) => a.proof).length}/${auxiliary.length} shared lemma(s); ${plan.calls.length} call(s))` +
    `; review: ${unconfirmed.length ? `${unconfirmed.length} not confirmed faithful (${unconfirmed.slice(0, 8).join(", ")}${unconfirmed.length > 8 ? ", …" : ""})` : "none found unfaithful"}${hard ? `, ${hard} with readability notes left` : ""}${unreviewed ? `, ${unreviewed} not reviewed` : ""}` +
    `; compared ${compared.size}${notConfirmed ? ` (${notConfirmed} not compared: English not confirmed faithful)` : ""}: follows ${count("follows")}, other route ${count("other-route")}, departs ${count("departs")}` +
    (deps.length ? `; ${deps.length} departure(s) from the printed proof: ${deps.filter((d) => d.placed).length} corrected in the paper, ${deps.some((d) => !isWrong(d)) ? `${deps.filter((d) => !d.placed && !isWrong(d)).length} gap(s) listed only, ` : ""}${deps.filter((d) => !d.placed && isWrong(d)).length} wrong step(s) reported only` : "") +
    (unclear ? `; ${unclear} ambiguous printed step(s) noted` : "") +
    (problems.length ? `; ${problems.length} problem(s) (see ${LEAN_PROOF_ENGLISH_ARTIFACT})` : "");
}

/** The run's stored Lean Proof in English (`<run>/lean_proof_english.json`), or null when none was
 *  written or it does not read. */
export async function readLeanProofEnglish(runDir: string): Promise<LeanProofEnglish | null> {
  const file = path.join(runDir, LEAN_PROOF_ENGLISH_ARTIFACT);
  if (!existsSync(file)) return null;
  try {
    const j = JSON.parse(await readFile(file, "utf8")) as LeanProofEnglish;
    return Array.isArray(j?.results) ? j : null;
  } catch { return null; }
}
