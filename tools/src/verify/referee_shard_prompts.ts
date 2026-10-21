/**
 * Prompts and reply contracts of the sharded V1.5 referee (`referee_shards.ts`): the compact core a
 * shard reads, the paper excerpts block, the shard prompt, and the strict reply schemas of the two
 * call kinds (shard, global pass). Also the symbol referee's prompts and replies
 * (`referee_symbols.ts`: symbol shards) and the PINNED READINGS section that carries its readings to
 * the statement referees.
 */
import { z } from "zod";
import type { Core, CoreAssumption, CoreSymbol } from "../core/schema.js";
import { normalizeSymbol } from "../core/symbol_names.js";
import { symbolAppears, symbolPattern } from "./symbol_match.js";
import { PATCH_BK_PREFIX, PATCH_PIN_PREFIX, PROOF_CHANGE_MARKER, bindingReadingItem, isReadingAddition, bindingReadings, symbolEntryShown, symbolEntryView, symbolUsers, symbolsUsedByNode, hostParts } from "./core_graph.js";
import { DRIFT_FIX_JSON_SCHEMA, DriftFixSchema } from "./directive_edits.js";
import {
  bibliographyEntries,
  citesIn,
  excerptWords,
  nodeExcerpts,
  referencedPassages,
  setupExcerpt,
  type Excerpt,
  type NodeExcerpts,
  type PaperIndex,
  type SymbolSlices,
} from "./referee_slices.js";
import { repairConfirmed, refutes, type DependencyVerdict } from "./referee_levels.js";
import type { V15NodeVerdict, V15SymbolVerdict } from "./types.js";
import {
  NodeVerdictSchema,
  SHARD_NODE_FIELDS_TEXT,
  SHARD_NODE_REPLY,
  PATCH_REVIEW_REPLY,
  PatchReviewSchema,
  REJECTION_VERDICTS_REPLY,
  RejectionVerdictsSchema,
  SYMBOL_FIELDS_TEXT,
  SymbolVerdictSchema,
  V15_SYMBOL_REPLY,
} from "./v1_5_schema.js";
import { resultWord } from "./owner_text.js";

export function section(header: string, body: string): string {
  return `=== ${header} ===\n\n${body}`;
}

/** Characters of a context node's text shown in the compact core (the full node is in
 * `discovery/core.json`). */
export const UNRELATED_TEXT_MAX = 120;
/** Byte caps of a prompt's paper slices: the setup of a statement shard, the setup of a shard
 * grading only hypotheses and definitions (their full text is shown anyway), the setup of a symbol
 * shard (symbols are introduced there), one node's proof. */
export const SETUP_SHARD_MAX = 8_000;
export const SETUP_HYPOTHESES_MAX = 5_000;
export const SETUP_SYMBOL_MAX = 15_000;
export const PROOF_EXCERPT_MAX = 12_000;

const bytes = (t: string): number => Buffer.byteLength(t, "utf8");

/**
 * `text` cut to at most `max` bytes at a sentence (or line) boundary, with a
 * `[… n lines omitted …]` marker naming where the rest is; unchanged when it fits.
 */
export function capText(text: string, max: number, rest = "discovery/flat.tex"): string {
  if (bytes(text) <= max) return text;
  const room = Math.max(0, max - 120);
  let head = Buffer.from(text, "utf8").subarray(0, room).toString("utf8").replace(/\uFFFD+$/, "");
  const cut = Math.max(head.lastIndexOf(". "), head.lastIndexOf(".\n"), head.lastIndexOf("\n\n"));
  if (cut > room / 2) head = head.slice(0, cut + 1);
  else if (head.lastIndexOf("\n") > room / 2) head = head.slice(0, head.lastIndexOf("\n"));
  const omitted = text.split("\n").length - head.split("\n").length + 1;
  return `${head.trimEnd()}\n[… ${omitted} line${omitted === 1 ? "" : "s"} omitted; read them in ${rest} …]`;
}

/** The symbols of the table that the nodes `ids` use — the core graph's one notion of use
 * (`symbolsUsedByNode`: listed in a node's `free_symbols`, or found as a whole symbol in its text or
 * proof), closed under the entries' `refs`: the same set a node's verdict basis reads. */
export function symbolsUsedBy(core: Core, ids: Iterable<string>): Set<string> {
  const table = new Map(core.symbols.map((x) => [x.name, x] as const));
  const used = new Set([...ids].flatMap((id) => [...symbolsUsedByNode(core, id)]));
  const todo = [...used];
  while (todo.length > 0) {
    for (const r of table.get(todo.pop()!)?.refs ?? []) if (table.has(r) && !used.has(r)) (used.add(r), todo.push(r));
  }
  return used;
}

/** A reply that is no JSON (`codex_malformed_output`) or fails the reply schema (a Zod error) is a
 * contract violation of the call, retried like any other; any other error is the runner's. Returns
 * the violation line, or null. */
export function isMalformedReply(err: unknown): string | null {
  if (err instanceof z.ZodError) return `the reply does not fit the output schema: ${err.issues.map((i) => `${i.path.join(".") || "(root)"}: ${i.message}`).slice(0, 5).join("; ")}. Emit exactly the JSON object the OUTPUT block describes.`;
  if ((err as { code?: string } | null)?.code === "codex_malformed_output") return `the reply was not one JSON object: ${err instanceof Error ? err.message : String(err)}. Emit exactly the JSON object the OUTPUT block describes, and nothing else.`;
  return null;
}

/** A repair's proof change inside a statement's `proof_tex` (from `PROOF_CHANGE_MARKER` on), or null. */
export function proofChange(proofTex: string | null | undefined): string | null {
  const at = typeof proofTex === "string" ? proofTex.indexOf(PROOF_CHANGE_MARKER) : -1;
  return at >= 0 ? proofTex!.slice(at) : null;
}

const flatText = (n: Record<string, unknown>): string => String(n.statement ?? n.condition ?? n.construction ?? "");
const squash = (t: string): string => t.replace(/\s*\[Hypotheses:[^\]]*\]\s*$/, "").replace(/\s+/g, "");

/** Characters of a used node's text shown in the compact core (the whole record is in
 * `discovery/core.json`). */
export const USED_TEXT_MAX = 2_500;

/**
 * The core as a shard sees it. The shard's own nodes carry their whole record: the text stays
 * unless the paper excerpt below prints it (then `(as printed, below)`, the appended hypothesis list
 * kept), the proof only when the excerpt shows none (else only a patch's proof change), readings
 * under PINNED READINGS. The nodes they use: one line each, id, kind and text (the first
 * `USED_TEXT_MAX` characters). Every other node
 * — the statements using them included — one line: id and the first `UNRELATED_TEXT_MAX`
 * characters, grouped by kind, no wiring; `idsOnly` (a node shard: what it grades and uses is shown
 * in full, the rest is in `discovery/core.json`): their ids, one line per kind. No bibliography.
 * `excerpts`: the shard nodes' paper excerpts.
 * The host of an inline cited leaf (`cited_in`) graded without it: its line, those of the hypotheses
 * and definitions it is stated under, and a repair's change to its proof (`core_graph.ts`
 * `basisInputs` reads the same). The symbol table entries the shard's OWN nodes use
 * (`symbolsUsedBy`) lead — not those of every node they use, which read the whole table in — each
 * with the scoped clauses applicable to those nodes only (`symbolEntryShown`).
 */
export function compactCore(core: Core, own: ReadonlySet<string>, excerpts: ReadonlyMap<string, NodeExcerpts> = new Map(), opts: { idsOnly?: boolean } = {}): string {
  const uses = new Set<string>();
  for (const s of [...core.statements, ...core.assumptions, ...core.definitions] as Array<{ id: string; depends_on?: string[] }>) {
    if (own.has(s.id)) for (const d of s.depends_on ?? []) if (!own.has(d)) uses.add(d);
  }
  const all = [
    ...core.assumptions.map((n) => [n as unknown as Record<string, unknown>, "assumption"] as const),
    ...core.definitions.map((n) => [n as unknown as Record<string, unknown>, "definition"] as const),
    ...core.statements.map((n) => [n as unknown as Record<string, unknown>, resultWord(n).toLowerCase()] as const),
  ];
  // A used node (its kind given) with its paper label: what a `\ref` in the nodes graded resolves to.
  const line = (n: Record<string, unknown>, kind: string | null, max: number): string => {
    const text = flatText(n).replace(/\s+/g, " ").trim();
    const label = kind ? (n.tex_locator as { label?: string | null } | undefined)?.label : null;
    return `- ${n.id as string}${kind ? ` (${kind}${label ? `, \\label{${label}}` : ""})` : ""}: ${text.length > max ? `${text.slice(0, max)} …` : text}`;
  };
  // Every other node, grouped by kind (the kind once, in the group's header).
  const grouped = (xs: ReadonlyArray<readonly [Record<string, unknown>, string]>): string[] => {
    const kinds = [...new Set(xs.map(([, k]) => k))];
    // (ids alone, by the list they are in: a result's kind word is part of what its USERS are shown)
    if (opts.idsOnly) return ["assumption", "definition", "result"].flatMap((k) => ((ids) => (ids.length ? [`${k}: ${ids.join(", ")}`] : []))(xs.filter(([, kk]) => (kk === "assumption" || kk === "definition" ? kk : "result") === k).map(([n]) => n.id as string)));
    return kinds.flatMap((k) => [`${k}:`, ...xs.filter(([, kk]) => kk === k).map(([n]) => line(n, null, UNRELATED_TEXT_MAX))]);
  };
  const full = (n: Record<string, unknown>): string => {
    const { proof_tex, pinned_readings_binding: _p, ...rest } = n;
    const out: Record<string, unknown> = { ...rest };
    const ex = excerpts.get(n.id as string);
    const k = "statement" in n ? "statement" : "condition" in n ? "condition" : "construction";
    const text = String(n[k] ?? "");
    // Only an excerpt that IS the node's text stands in for it: a printed line also carrying a
    // neighbouring sentence would be read as the node (live CNS 2026-09-27: a false truncation drift).
    // (An environment's own \begin/\end lines around it do not count.)
    const printed = ex?.statement.text.split("\n").filter((l) => !/^\s*\\(?:begin|end)\{[^}]*\}/u.test(l)).join("\n");
    if (ex?.statement.range && squash(printed ?? "") === squash(text)) {
      const hyp = /\[Hypotheses:[^\]]*\]\s*$/.exec(text)?.[0].trim();
      out[k] = hyp ? `(as printed, below) ${hyp}` : "(as printed, below)";
    }
    if (typeof proof_tex === "string" && proof_tex.trim()) {
      // A repair's proof change is shown whole and here only (PATCHES does not repeat it): never under
      // the cap of the proof it amends.
      const change = proofChange(proof_tex);
      const printedProof = change === null ? proof_tex : proof_tex.slice(0, proof_tex.length - change.length);
      if (!ex?.proof && printedProof.trim()) out.proof_tex = capText(printedProof.trimEnd(), PROOF_EXCERPT_MAX, "discovery/core.json");
      if (change !== null) out.proof_change = change;
    }
    return JSON.stringify(out);
  };
  const c = core as unknown as Record<string, unknown>;
  const { bibliography: _b, assumptions: _a, definitions: _d, statements: _s, symbols: _y, ...head } = c;
  const mine = all.filter(([n]) => own.has(n.id as string));
  const used = all.filter(([n]) => uses.has(n.id as string));
  // The host of an inline cited leaf graded here without it: the leaf is checked against the host
  // as it stands (a repair of the host is how a finding on the leaf is answered).
  // (… with the blocks a repair split off it: they are the host now, `hostParts`.)
  const hosts = [...new Set(mine.flatMap(([n]) => (typeof n.cited_in === "string" ? hostParts(core, n.cited_in) : [])))].filter((h) => !own.has(h)).map((h) => core.statements.find((st) => st.id === h)!);
  const hostLines = hosts.flatMap((h) => {
    const change = proofChange(h.proof_tex);
    return [
      ...all.filter(([n]) => n.id === h.id || (h.depends_on.includes(n.id as string) && !own.has(n.id as string) && !uses.has(n.id as string) && !core.statements.some((st) => st.id === n.id))).map(([n, k]) => line(n, k, USED_TEXT_MAX)),
      ...(change !== null ? [`  ${h.id}, a repair's change to its proof: ${change}`] : []),
    ];
  });
  // The id list is the vocabulary of a wiring fix: a condition V1.5 itself appended (a pinned reading, a
  // bookkeeping condition) is never one's target, so it is not listed.
  const rest = all.filter(([n]) => !own.has(n.id as string) && !uses.has(n.id as string) && !(opts.idsOnly && isReadingAddition(n as unknown as CoreAssumption)));
  const symbols = mine.length ? symbolsUsedBy(core, own) : new Set<string>();
  return [
    JSON.stringify(head),
    ...(symbols.size ? ["Symbols the nodes you grade use (the entry of a symbol only a node they use names is in discovery/core.json):", ...core.symbols.filter((x) => symbols.has(x.name)).map((x) => JSON.stringify(symbolEntryShown(core, x, own)))] : []),
    ...(mine.length ? ["The nodes you grade (the whole record):", ...mine.map(([n]) => full(n))] : []),
    ...(used.length ? [`What they use (text; a line cut at ${USED_TEXT_MAX} characters continues in discovery/core.json):`, ...used.map(([n, k]) => line(n, k, USED_TEXT_MAX))] : []),
    ...(hostLines.length ? ["The result whose proof invokes a cited result you grade (`cited_in`), as it stands now (with the blocks a repair split off it), and the hypotheses and definitions each is stated under:", ...hostLines] : []),
    opts.idsOnly ? "Every other node of the paper, by kind (the ids a wiring fix names):" : `${mine.length ? "Every other node" : "Every node"} (id and the first ${UNRELATED_TEXT_MAX} characters, by kind):`,
    ...grouped(rest),
  ].join("\n");
}

/** `ex` with the proof an inline cited leaf is read in capped as a proof is. */
function cappedContext(ex: NodeExcerpts): NodeExcerpts {
  const c = ex.context;
  return c ? { ...ex, context: { ...c, excerpt: { ...c.excerpt, text: capText(c.excerpt.text, PROOF_EXCERPT_MAX, `discovery/flat.tex (${c.excerpt.where})`) } } } : ex;
}

const within = (r: [number, number] | null, outer: [number, number]): boolean => !!r && r[0] >= outer[0] && r[1] <= outer[1];

/** The excerpts of a node set, each passage shown once: a node sliced out of a passage already
 * shown (a premise inside a result's statement) is pointed at it and shown with its own words. */
function excerptBlocks(ex: NodeExcerpts[]): string {
  const shown: Array<{ id: string; range: [number, number] }> = [];
  const blocks: string[] = [];
  for (const e of ex) {
    const host = shown.find((s) => within(e.statement.range, s.range));
    const parts = [
      host
        ? `### ${e.id}\n\nStatement (${e.statement.where}, inside the passage shown for ${host.id}):\n\n${e.statement.text}`
        : `### ${e.id}\n\nStatement (${e.statement.where}):\n\n${e.statement.text}`,
    ];
    if (e.statement.range && !host) shown.push({ id: e.id, range: e.statement.range });
    if (e.proof) {
      const pHost = shown.find((s) => within(e.proof!.range, s.range));
      parts.push(pHost ? `Proof (${e.proof.where}): shown above, under ${pHost.id}.` : `Proof (${e.proof.where}):\n\n${e.proof.text}`);
      if (e.proof.range && !pHost) shown.push({ id: e.id, range: e.proof.range });
    } else if (e.context) {
      // A result a proof invokes by citation: the proof is the HOST's, shown as what the step is read in.
      const cHost = shown.find((s) => within(e.context!.excerpt.range, s.range));
      const what = `Context — the proof of ${e.context.of}, which invokes this cited result at the passage above (${e.context.excerpt.where})`;
      parts.push(cHost ? `${what}: shown above, under ${cHost.id}.` : `${what}; it is not a proof of the cited result:\n\n${e.context.excerpt.text}`);
    } else if (e.id.match(/^(thm|lem|prop):/)) {
      parts.push("Proof: none located next to this result (a cited result, or a proof given elsewhere — search discovery/flat.tex).");
    }
    blocks.push(parts.join("\n\n"));
  }
  return blocks.join("\n\n");
}

export interface ShardContext {
  core: Core;
  /** The symbol referee's readings (`referee_symbols.ts`): the core with its symbol verdicts applied,
   * and the symbols it graded `unresolvable`. Absent: no symbol pass ran. */
  symbols?: SymbolReadings;
  px: PaperIndex;
  setup: ReturnType<typeof setupExcerpt>;
  /** Sections the stage renders for a node set: cited sources, patches, lint warnings. */
  extraSections: (ids: readonly string[]) => string[];
  totalNodes: number;
  scope: string;
  /** Dependency order (`referee_levels.ts`): the final verdicts of the statements a node uses,
   * settled at a lower level or carried. Absent: no dependency section. */
  dependencies?: (id: string) => DependencyVerdict[];
}

/** Characters of a dependency's detail / witness / reading / corrected form shown in DEPENDENCY
 * VERDICTS (its full text is in the core section). */
export const DEP_TEXT_MAX = 160;

const clip = (t: string, max: number): string => (t.length > max ? `${t.slice(0, max)} …` : t);

const oneLine = (t: string | null | undefined, max = DEP_TEXT_MAX): string => clip(String(t ?? "").replace(/\s+/g, " ").trim(), max);

/** One dependency's final verdict, in words, on one line: its correctness, a pinned reading, a
 * drift, a repair (each text at most `DEP_TEXT_MAX` characters). */
export function dependencyLine(d: DependencyVerdict): string {
  const v = d.verdict;
  const parts: string[] = [];
  if (v.correctness === "ok") parts.push(v.owner_overruled ? `ok (owner ruling: the paper's owner withdrew the finding — ${oneLine(v.owner_reason)})` : "ok");
  else if (v.correctness === "bookkeeping") parts.push(`bookkeeping — holds under the added condition ${oneLine(v.bookkeeping_assumption?.condition)}`);
  else if (v.correctness === "unclear") parts.push(`unclear — a step was not reproduced (not an error): ${oneLine(v.detail)}`);
  else if (refutes(v)) parts.push(`ERROR — ${oneLine(v.witness ?? v.detail)}`);
  else parts.push(`error on its repair only (${v.minimality ? "not minimal" : "weakens the claim"}) — the corrected form holds`);
  if (d.repair && repairConfirmed(d)) {
    parts.push(`confirmed repair: use its corrected form, ${oneLine(d.repair.corrected)}${d.repair.printedError ? ` (the printed statement was an error: ${oneLine(d.repair.printedError)})` : ""}`);
  } else if (refutes(v)) parts.push("no confirmed repair");
  if (v.ambiguity === "pinned" && v.reading) parts.push(`pinned reading: ${oneLine(v.reading.reading)}`);
  else if (v.ambiguity === "unresolvable") parts.push(`unresolvable ambiguity: ${oneLine(v.detail)}`);
  if (v.faithfulness === "drift") parts.push(`drift (a transcription defect; the grade is provisional): ${oneLine(v.detail)}`);
  return `${d.id} (${d.kind}): ${parts.join("; ")}`;
}

/**
 * The DEPENDENCY VERDICTS section: every statement the nodes `ids` use, ONCE, one line with its
 * final verdict and the nodes using it (its text is in the core section), then the rule that binds
 * them. The rule on an errored dependency is stated once; the runner imposes it on the grades
 * (`referee_levels.ts` `settleOnErroredDependencies`), so no per-node directive is written. Empty
 * when none of the nodes uses a graded statement.
 */
export function dependencyVerdictsSection(ctx: ShardContext, ids: readonly string[]): string[] {
  if (!ctx.dependencies) return [];
  const used = new Map<string, { d: DependencyVerdict; by: string[] }>();
  for (const id of ids) {
    for (const d of ctx.dependencies(id)) {
      const u = used.get(d.id);
      if (u) u.by.push(id);
      else used.set(d.id, { d, by: [id] });
    }
  }
  if (used.size === 0) return [];
  return [
    section(
      "DEPENDENCY VERDICTS (binding — the final grades of the results your nodes use, settled before this call)",
      "Every statement a node below uses was graded first, and its final grade is BINDING here. Judge each node under " +
        "the graded form of what it uses: a result graded ok, bookkeeping or pinned is used as graded (with its added " +
        "condition or reading); a result graded error is used in its corrected form if a repair is confirmed, else the " +
        "node's own correctness is `unclear` with detail \"depends on <id>, graded error\" (unless it fails for a reason " +
        "of its own); a result graded unclear is used " +
        "as stated. Do not re-derive a result used; grade the node's own step.\n\n" +
        [...used.values()].map(({ d, by }) => `- ${dependencyLine(d)} — used by ${by.join(", ")}`).join("\n"),
    ),
  ];
}

/** The PAPER SETUP body — the preamble's macro definitions and the text up to the first result —
 * within `max` bytes (the text cut at a sentence boundary). */
export function setupText(setup: ReturnType<typeof setupExcerpt>, max: number): string {
  const macros = setup.macros ? `Macro definitions (preamble):\n\n${setup.macros}\n\n` : "";
  const head = `${macros}Text up to the first result (${setup.where}):\n\n`;
  return head + capText(setup.setup, Math.max(1_000, max - bytes(head)));
}

/** Whether a shard grades only hypotheses and definitions (level 0: no statement among them). */
export function gradesOnlyHypotheses(core: Core, ids: readonly string[]): boolean {
  return ids.every((id) => !core.statements.some((st) => st.id === id));
}

/** The shard nodes' paper excerpts, each proof capped at `PROOF_EXCERPT_MAX` bytes. */
function shardExcerpts(ctx: ShardContext, ids: readonly string[]): NodeExcerpts[] {
  return ids.map((id) => {
    const ex = cappedContext(nodeExcerpts(ctx.px, ctx.core, id));
    return ex.proof ? { ...ex, proof: { ...ex.proof, text: capText(ex.proof.text, PROOF_EXCERPT_MAX, `discovery/flat.tex (${ex.proof.where})`) } } : ex;
  });
}

function paperContext(ctx: ShardContext, ids: readonly string[], ex: NodeExcerpts[]): string[] {
  const { passages, omitted } = referencedPassages(ctx.px, ctx.core, ex);
  const setupBody = setupText(ctx.setup, gradesOnlyHypotheses(ctx.core, ids) ? SETUP_HYPOTHESES_MAX : SETUP_SHARD_MAX);
  const refs =
    passages.length > 0 || omitted.length > 0
      ? [
          section(
            "REFERENCED PASSAGES (what the statements and proofs above cite that no core node carries)",
            [...passages.map((p) => `### \\label{${p.label}} (${p.excerpt.where})\n\n${p.excerpt.text}`), ...(omitted.length ? [`Not shown (size cap; read them in discovery/flat.tex): ${omitted.join(", ")}`] : [])].join("\n\n"),
          ),
        ]
      : [];
  // Bibliography entries only for what the shard's own statements and proofs cite.
  const bib = bibliographyEntries(ctx.px, [...new Set(ex.flatMap((e) => [...citesIn(e.statement.text), ...citesIn(e.proof?.text ?? "")]))]);
  const bibSection = bib.length > 0 ? [section("BIBLIOGRAPHY ENTRIES CITED BY THE NODES YOU GRADE", bib.map((b) => `- [${b.key}] ${b.text}`).join("\n"))] : [];
  return [
    section("PAPER SETUP", setupBody),
    section("PAPER EXCERPTS FOR THE NODES YOU GRADE (verbatim from discovery/flat.tex)", excerptBlocks(ex)),
    ...refs,
    ...bibSection,
  ];
}

/** The node fields in prose, each field on one line (the reply schema is enforced separately). */
const SHARD_FIELDS = SHARD_NODE_FIELDS_TEXT.replace(/\n {20,}/g, " ").replace(/^( {6}\S+) {2,}/gm, "$1  ");

const SHARD_OUTPUT_BLOCK = `=== SHARD OUTPUT ===

Emit ONE JSON object and nothing else:

  summary  two or three sentences: what you reproduced, and what you found.
  nodes    exactly one entry per node listed under NODES TO GRADE, and no other:
${SHARD_FIELDS}`;

/**
 * A shard call's prompt: the referee brief cut to the blocks its nodes need (`shardBrief`), the
 * shard brief, the compact core, the readings and dependency verdicts binding its nodes (each once),
 * the nodes to grade, the paper slices (setup capped, proofs capped), the stage's own sections for
 * these nodes, and the output fields.
 */
export function buildShardPrompt(ctx: ShardContext, base: string, shardBrief: string, ids: readonly string[]): string {
  const own = new Set(ids);
  const ex = shardExcerpts(ctx, ids);
  const extra = ctx.extraSections(ids);
  const uses = [...new Set(ids.flatMap((id) => nodeDeps(ctx.core, id)))].filter((d) => !own.has(d));
  return [
    shardBriefOf(base, {
      statements: !gradesOnlyHypotheses(ctx.core, ids),
      patches: extra.some((x) => x.startsWith("=== PATCHES")),
      cited: extra.some((x) => x.startsWith("=== CITED SOURCES")) || ctx.core.statements.some((st) => own.has(st.id) && st.status === "cited"),
    }).trimEnd(),
    shardBrief.trimEnd(),
    section(
      "TYPED CORE (discovery/core.json: the nodes you grade in full, what they use in full text, every other node by id; a text given as `(as printed, below)` is the core's text, word for word the excerpt shown for that node under PAPER EXCERPTS)",
      `${ctx.scope}\n\n${compactCore(ctx.core, own, new Map(ex.map((e) => [e.id, e] as const)), { idsOnly: true })}`,
    ),
    ...readingsSection(ctx.core, ctx.symbols, ids, uses),
    ...dependencyVerdictsSection(ctx, ids),
    section(`NODES TO GRADE (${ids.length} of ${ctx.totalNodes})`, ids.map((id) => `- ${id}`).join("\n")),
    ...paperContext(ctx, ids, ex),
    ...extra,
    SHARD_OUTPUT_BLOCK,
  ].join("\n\n");
}

const nodeDeps = (core: Core, id: string): string[] =>
  (([...core.statements, ...core.assumptions, ...core.definitions] as Array<{ id: string; depends_on?: string[] }>).find((n) => n.id === id)?.depends_on ?? []);

// ---------------------------------------------------------------------------------------------
// The referee brief, cut to what one call needs
// ---------------------------------------------------------------------------------------------

/** The blocks of the referee brief (`review.txt`), by the paragraph that opens each. */
const BRIEF_BLOCKS: ReadonlyArray<readonly [string, RegExp]> = [
  ["faithfulness", /^FAITHFULNESS — /m],
  ["ambiguity", /^AMBIGUITY — /m],
  ["conventions", /^CONVENTIONS TO SETTLE\./m],
  ["patches", /^PATCHES\. /m],
  ["correctness", /^CORRECTNESS — /m],
  ["howto", /^=== HOW TO CHECK CORRECTNESS/m],
  ["cited", /^CITED STANDARD RESULTS\./m],
];

/** The brief's opening and the blocks `want`, in the brief's order, then `note`. A brief whose
 * blocks cannot be found (a heading edited in `review.txt`) is a prompt-contract bug: it throws,
 * never falls back to the whole brief silently. */
function briefBlocks(base: string, want: ReadonlySet<string>, note: string): string {
  const at = BRIEF_BLOCKS.map(([k, re]) => ({ k, i: base.search(re) }));
  const broken = at.find((x, n) => x.i < 0 || (n > 0 && x.i <= at[n - 1]!.i));
  if (broken) throw new Error(`V1.5 brief (review.txt): its "${broken.k}" block is missing or out of order (${BRIEF_BLOCKS.find(([k]) => k === broken.k)![1]}); the sharded referee cuts the brief by these blocks.`);
  const blocks = at.filter((x) => want.has(x.k)).map((x) => base.slice(x.i, at[at.findIndex((y) => y.k === x.k) + 1]?.i ?? base.length).trimEnd());
  // Hanging-indent continuation lines joined to their line (the words unchanged).
  return [base.slice(0, at[0]!.i).trimEnd(), ...blocks, note].join("\n\n").replace(/\n {6,}(?=\S)/g, " ");
}

/**
 * The referee brief cut to what one SHARD needs: faithfulness, ambiguity with the conventions
 * checklist, and correctness always; how to check correctness when it grades a statement; PATCHES
 * when a patch touches its nodes; CITED STANDARD RESULTS when it grades a cited result. The call's
 * scope is the shard brief's (`shard.txt`). Throws on a brief whose blocks cannot be found.
 */
export function shardBriefOf(base: string, has: { statements: boolean; patches: boolean; cited: boolean }): string {
  const want = new Set(["faithfulness", "ambiguity", "conventions", "correctness"]);
  if (has.statements) want.add("howto");
  if (has.patches) want.add("patches");
  if (has.cited) want.add("cited");
  return briefBlocks(base, want, "(The brief's scope is the shard's, below; blocks no node of this shard needs are omitted.)");
}

/**
 * The referee brief cut to what the GLOBAL pass needs (`global.txt` names its three items): the
 * FAITHFULNESS block (wiring across nodes is a faithfulness defect, stated in the shape of a drift
 * fix) and, when the core carries patches, the PATCHES block (`patch_review`, the consistency
 * rules). Ambiguity and correctness are the shards'. Throws like `shardBriefOf`.
 */
export function globalBriefOf(base: string, has: { patches: boolean }): string {
  const want = new Set(["faithfulness"]);
  if (has.patches) want.add("patches");
  return briefBlocks(base, want, "(The brief's other blocks are the shards': the global pass re-grades no node on its own axes.)");
}

/**
 * The core as the global pass reads it, beside the whole paper: its head, the symbol table (an
 * entry's scoped clauses: those applicable to the nodes shown, `symbolEntryShown`) and
 * every node one per line, each node with every field but its proof (the paper prints it; a patch's
 * proof change is kept as `proof_change`). No bibliography (the paper carries it).
 *
 * A delta pass (`shown`: `globalScope`) shows the nodes it checks in full (`full`) and each
 * NEIGHBOUR carried from an earlier pass by what a neighbour is read for — its id, kind, paper label
 * (what a `\ref` in a node in full resolves to), text, `depends_on` (wiring spans a node and its
 * neighbours) and its place in a split (`split_from`, `umbrella`) — never its proof change or other
 * fields: its verdict is not re-opened. The symbol entries are those the nodes in full use.
 */
export function globalCoreText(core: Core, shown?: ReadonlySet<string>, full: ReadonlySet<string> | undefined = shown, opts: { compactSymbols?: boolean } = {}): string {
  const c = core as unknown as Record<string, unknown>;
  const { bibliography: _b, assumptions: _a, definitions: _d, statements: _s, symbols: _y, ...head } = c;
  const whole = (n: Record<string, unknown>): string => {
    const { proof_tex, ...rest } = n;
    const change = proofChange(proof_tex as string | undefined);
    return JSON.stringify(change !== null ? { ...rest, proof_change: change } : rest);
  };
  const neighbour = (n: Record<string, unknown>): string => {
    const k = "statement" in n ? "statement" : "condition" in n ? "condition" : "construction";
    const label = (n.tex_locator as { label?: string | null } | undefined)?.label;
    return JSON.stringify({
      id: n.id,
      ...(n.kind !== undefined ? { kind: n.kind } : {}),
      ...(label ? { label } : {}),
      [k]: n[k],
      ...(Array.isArray(n.depends_on) ? { depends_on: n.depends_on } : {}),
      ...(n.split_from !== undefined ? { split_from: n.split_from } : {}),
      ...(n.umbrella !== undefined ? { umbrella: n.umbrella } : {}),
      carried: true,
    });
  };
  const node = (n: Record<string, unknown>): string => (!full || full.has(n.id as string) ? whole(n) : neighbour(n));
  const rec = (xs: unknown[]): Array<Record<string, unknown>> =>
    (xs as Array<Record<string, unknown>>).filter((n) => !shown || shown.has(n.id as string));
  const all = [...core.assumptions, ...core.definitions, ...core.statements].map((n) => n.id);
  const hidden = shown ? all.filter((id) => !shown.has(id)) : [];
  const symbols = full ? symbolsUsedBy(core, full) : null;
  const brief = shown && full ? [...shown].some((id) => !full.has(id)) : false;
  return [
    JSON.stringify(head),
    "symbols:",
    // (compact: each clause once, naming its results, as a whole-paper pass shows it — not once per set of
    // shown nodes it applies to; the global prompt takes whichever form is shorter)
    ...core.symbols.filter((x) => !symbols || symbols.has(x.name)).map((x) => JSON.stringify(symbolEntryShown(core, x, opts.compactSymbols ? null : (full ?? null)))),
    ...(brief ? ["A node marked `carried: true` is a neighbour of the nodes this pass graded, carried from an earlier pass: shown by its label, text and wiring only, its verdict not re-opened. When a finding on a node in full needs more of it, its whole record is in discovery/core.json (look it up by its id)."] : []),
    "assumptions:",
    ...rec(core.assumptions).map(node),
    "definitions:",
    ...rec(core.definitions).map(node),
    "statements:",
    ...rec(core.statements).map(node),
    ...(hidden.length
      ? [`Not shown (unchanged since an earlier global pass checked them; their verdicts stand): ${hidden.join(", ")}`]
      : []),
  ].join("\n");
}

/** The nodes a delta global pass is shown: those graded this pass (`grading`, with the nodes of the
 * fixer rejections it rules on), the nodes they use and
 * the nodes using them (one step each way — wiring spans a node and its neighbours), and the key
 * results (the patch review judges the key-result list). Everything else was checked by an earlier
 * global pass on unchanged text, and a carried verdict is never re-opened: of the nodes shown, only
 * `grading` is shown in full (`globalCoreText`). */
export function globalScope(core: Core, grading: Iterable<string>, keyResults: readonly string[] = []): Set<string> {
  const focus = new Set(grading);
  const out = new Set([...focus, ...keyResults]);
  for (const n of [...core.statements, ...core.assumptions, ...core.definitions] as Array<{ id: string; depends_on?: string[] }>) {
    const deps = n.depends_on ?? [];
    if (focus.has(n.id)) deps.forEach((d) => out.add(d));
    if (deps.some((d) => focus.has(d))) out.add(n.id);
  }
  return out;
}

/** A delta global pass's paper: the setup (capped) and the excerpts of the nodes it checks (`ids`:
 * those shown in full, not the carried neighbours), in place of the whole paper — shown when the
 * transcription is the one an earlier global pass checked against the whole paper. */
export function globalPaperExcerpts(px: PaperIndex, core: Core, ids: readonly string[]): string[] {
  const ex = ids.map((id) => {
    const e = cappedContext(nodeExcerpts(px, core, id));
    return e.proof ? { ...e, proof: { ...e.proof, text: capText(e.proof.text, PROOF_EXCERPT_MAX, `discovery/flat.tex (${e.proof.where})`) } } : e;
  });
  return [
    section("PAPER SETUP", setupText(setupExcerpt(px), SETUP_SHARD_MAX)),
    section(
      "PAPER EXCERPTS FOR THE NODES SHOWN IN FULL (verbatim from discovery/flat.tex; the paper's transcription is unchanged since an earlier global pass read it whole)",
      excerptBlocks(ex),
    ),
  ];
}

/** A verdict on one line without its empty fields (null, false, empty lists) and without the
 * runner's bookkeeping (basis, shard tag) — the SHARD VERDICTS the global pass reads. A CARRIED
 * verdict is never re-opened there (`referee_shards.ts`): it shows its grades, its reading and its
 * appended condition (what a neighbour's wiring or a patch may conflict with), not its detail,
 * witness or fix; so is a verdict clean on every axis, whose reasons the global pass does not need. */
export function verdictLine(v: V15NodeVerdict): string {
  const { basis: _b, basis_scheme: _s, basis_inputs: _i, shards: _sh, ...rest } = v as V15NodeVerdict & Record<string, unknown>;
  const { detail: _d, witness: _w, witness_instance: _wi, fix: _f, explanation_clarity: _e, split: _sp, owner_reason: _o, ...brief } = rest;
  // A node graded clean on every axis needs no reasons in the global pass, which re-grades no node:
  // its grades are shown as for a carried one. A flagged node keeps its detail and witness.
  const clean = v.faithfulness === "ok" && v.ambiguity === "ok" && v.correctness === "ok";
  const shown = v.graded === "carried" || clean ? brief : rest;
  return JSON.stringify(Object.fromEntries(Object.entries(shown).filter(([, x]) => x !== null && x !== undefined && x !== false && !(Array.isArray(x) && x.length === 0))));
}

export const GLOBAL_OUTPUT_BLOCK = `=== GLOBAL OUTPUT ===

Emit ONE JSON object and nothing else:

  verdict  the verdict over the SHARD VERDICTS with your cross_node
           entries applied: REVISE when some node drifts; otherwise FAIL when some node is
           \`error\` or \`unresolvable\`; otherwise PASS. The runner recomputes it.
  summary  two or three sentences: what spans nodes, and what you found.
  patch_review  null unless a PATCHES section is present (it then names key_results, and every
           repair of a key result — whole, or by one line when carried); then
           {key_results_ok, detail} as the brief says.
  rejection_verdicts  null unless a FIXER REJECTIONS section is present; then one
           {node, upheld, detail} per rejection listed there, as that section says.
  cross_node  [] or entries {id, kind, detail, fix, witness}:
      id      the core node the defect sits on (exactly as in the core).
      kind    "wiring" (a faithfulness defect spanning nodes; \`fix\` = the mechanical edit,
              as the reply schema shapes it — add_depends_on / remove_depends_on on a
              statement, wire_into / unwire_from on an assumption or definition: node ids;
              new_assumption for a premise no node carries: {id "ass:<slug>" (lower-case
              letters, digits and hyphens after "ass:"), env (the id of the environment
              holding the sentence, or null for running text), from, to (verbatim anchors
              of the sentence, copied from the paper), wire_into [statement ids]} —
              or null) or "patch_consistency"
              (only on a patched node; \`fix\` null).
      detail  the defect in one short paragraph, naming the other node(s) involved. It is
              TeX: mathematics inside $…$, wiring said in words, never a field name such
              as depends_on.
      witness for "patch_consistency": the conflict shown, or null when you cannot show
              it; null for "wiring".`;

const CrossNodeSchema = z.object({
  id: z.string().min(1),
  kind: z.enum(["wiring", "patch_consistency"]),
  detail: z.string(),
  fix: DriftFixSchema.nullable().optional(),
  witness: z.string().nullable(),
});
export type CrossNode = z.infer<typeof CrossNodeSchema>;

export const GLOBAL_REPLY: Record<string, unknown> = {
  type: "object",
  additionalProperties: false,
  required: ["verdict", "summary", "patch_review", "rejection_verdicts", "cross_node"],
  properties: {
    verdict: { type: "string", enum: ["PASS", "REVISE", "FAIL"] },
    summary: { type: "string" },
    patch_review: PATCH_REVIEW_REPLY,
    rejection_verdicts: REJECTION_VERDICTS_REPLY,
    cross_node: {
      type: "array",
      items: {
        type: "object",
        additionalProperties: false,
        required: ["id", "kind", "detail", "fix", "witness"],
        properties: {
          id: { type: "string" },
          kind: { type: "string", enum: ["wiring", "patch_consistency"] },
          detail: { type: "string" },
          fix: DRIFT_FIX_JSON_SCHEMA,
          witness: { type: ["string", "null"] },
        },
      },
    },
  },
};
export const GlobalReplySchema = z.object({
  verdict: z.enum(["PASS", "REVISE", "FAIL"]),
  summary: z.string(),
  patch_review: PatchReviewSchema.nullable().optional(),
  rejection_verdicts: RejectionVerdictsSchema.nullable().optional(),
  cross_node: z.array(CrossNodeSchema),
});

export const SHARD_REPLY: Record<string, unknown> = {
  type: "object",
  additionalProperties: false,
  required: ["summary", "nodes"],
  properties: { summary: { type: "string" }, nodes: { type: "array", items: SHARD_NODE_REPLY } },
};
export const ShardReplySchema = z.object({ summary: z.string(), nodes: z.array(NodeVerdictSchema) });


// ---------------------------------------------------------------------------------------------
// Symbol readings shown to the statement referees
// ---------------------------------------------------------------------------------------------

/** What the symbol referee settled, as the statement referees read it. */
export interface SymbolReadings {
  /** The core with the symbol verdicts applied (`buildCore`, overlay `symbols`): a pinned reading
   * is the symbol's `def` in its table (`core_graph.ts` `compileSymbolEdits`), never a hypothesis,
   * so the readings reach every node through the table the shards are shown. */
  binding: Core;
  /** Symbols graded `unresolvable`. */
  unresolved: V15SymbolVerdict[];
}

/**
 * The SYMBOLS LEFT OPEN section of the global pass: the symbols the symbol referees graded
 * `unresolvable`, each with the statements using it. (A pinned reading is the symbol's `def` in
 * the table and needs no section.) Empty when none.
 */
export function openSymbolsSection(sr: SymbolReadings | undefined): string[] {
  if (!sr || sr.unresolved.length === 0) return [];
  const open = sr.unresolved.map((v) => ({ v, users: symbolUsers(sr.binding, v.name) }));
  return [
    section(
      "SYMBOLS LEFT OPEN (graded unresolvable by the symbol referees)",
      "The paper leaves each symbol's reading open; the statements using it carry the ambiguity in their grades.\n\n" +
        open.map(({ v, users }) => `- ${v.name}: ${v.detail.replace(/\s+/g, " ").trim()} (used by ${users.join(", ") || "no statement"})`).join("\n"),
    ),
  ];
}

/**
 * The PINNED READINGS section of a shard: every reading binding the nodes `ids`,
 * ONCE, with the nodes it binds — a statement's readings as wired into it; a hypothesis's or
 * definition's own; the own readings of `context` (the nodes they use). The symbols the paper
 * leaves open are shown only when a node of `ids` or `context` uses the symbol (`symbolsUsedBy`).
 * Readings come from the symbol referee's binding core when it ran, else from the core (a symbol
 * reading is in the table, never a reading node). Empty when there is nothing to show.
 */
export function readingsSection(core: Core, sr: SymbolReadings | undefined, ids: readonly string[], context: readonly string[] = []): string[] {
  const b = sr?.binding ?? core;
  const usedNorm = new Set([...symbolsUsedBy(b, [...ids, ...context])].map(normalizeSymbol));
  const isStatement = (id: string): boolean => b.statements.some((st) => st.id === id);
  const shown = new Map<string, { r: ReturnType<typeof bindingReadings>[number]; binds: string[] }>();
  const add = (id: string, r: ReturnType<typeof bindingReadings>[number]): void => {
    if (!isStatement(id) && r.of !== id) return;
    const s = shown.get(r.id);
    if (s) {
      if (!s.binds.includes(id)) s.binds.push(id);
    } else shown.set(r.id, { r, binds: [id] });
  };
  for (const id of ids) for (const r of bindingReadings(b, id)) add(id, r);
  for (const id of context) for (const r of bindingReadings(b, id, { ownOnly: true })) add(id, r);
  const open = (sr?.unresolved ?? []).filter((v) => usedNorm.has(normalizeSymbol(v.name)));
  if (shown.size === 0 && open.length === 0) return [];
  const body = [
    shown.size > 0
      ? "Readings settled before this pass (by the symbol referees, an earlier pass, or the paper's owner), each once with the " +
        "nodes it binds. They are BINDING: judge those nodes under them, and do not grade a node for a defect that only " +
        "another reading has." +
        ([...shown.keys()].some((id) => id.startsWith(PATCH_PIN_PREFIX) || id.startsWith(PATCH_BK_PREFIX)) ? " A reading or side condition stated by a repair is part of that patch: grade it with the patch (the PATCHES rule), then judge the node under it." : "") +
        "\n\n" +
        [...shown.values()].map(({ r, binds }) => `- ${bindingReadingItem(r)} — binds ${binds.join(", ")}`).join("\n")
      : "",
    open.length > 0
      ? "Symbols whose reading the paper leaves open (graded unresolvable by the symbol referees) — grade the ambiguity of " +
        "each node here that depends on the choice:\n\n" +
        open.map((v) => `- ${v.name}: ${v.detail.replace(/\s+/g, " ").trim()}`).join("\n")
      : "",
  ]
    .filter(Boolean)
    .join("\n\n");
  return [section("PINNED READINGS (binding)", body)];
}

// ---------------------------------------------------------------------------------------------
// The symbol referee's prompts
// ---------------------------------------------------------------------------------------------

export interface SymbolContext {
  /** The core as transcribed: its symbol table is what is graded. */
  core: Core;
  setup: ReturnType<typeof setupExcerpt>;
  slices: ReadonlyMap<string, SymbolSlices>;
  /** Per symbol, the statements it is read from that a repair corrects, each with what the symbol
   * reads of it (`referee_symbols.ts` `correctedReading`: the sentences naming it; `whole`: the
   * statement, the symbol not found in it) — exactly what the symbol's basis hashes. */
  corrected?: ReadonlyMap<string, ReadonlyArray<{ node: string; sentences: readonly string[]; whole: boolean }>>;
  totalSymbols: number;
  scope: string;
}

/** The core nodes whose `free_symbols` list symbol `name` (the line under its heading). */
function symbolListing(core: Core, name: string): string[] {
  const norm = normalizeSymbol(name);
  return [...core.statements, ...core.assumptions, ...core.definitions].filter((n) => (n.free_symbols ?? []).some((f) => normalizeSymbol(f) === norm)).map((n) => n.id);
}

/**
 * What `buildSymbolPrompt` shows its referee of symbol `name` beside the introducing passage and the
 * corrected statements (`referee_symbols.ts` `symbolBasis` hashes those apart) — the part of the
 * symbol's verdict basis that makes shown = hashed: its whole entry (`space`, `sig`, `role`, `refs`
 * with `type` and `def`), the entries of the symbols it refers to, the SETTINGS (the sampling model,
 * shown to every symbol call), the core nodes listing it, and the passages where it is defined again
 * and used. Entries by their meaning (`symbolEntryView`), passages by their words (`excerptWords`: a
 * line shift moves nothing). Not the PAPER SETUP: the paper's own text, the same for every symbol
 * while the transcription stands (as on the statement side).
 */
export function symbolShownBasis(ctx: Pick<SymbolContext, "core" | "slices">, name: string, legacy = false): string {
  return JSON.stringify(symbolShownParts(ctx, name, legacy));
}

/** The parts of `symbolShownBasis`, each on its own (the symbol pass records a hash of each with
 *  the verdict, so a later pass can say which part moved when it grades the symbol afresh). Of the
 *  settings, those that NAME the symbol (`symbolAppears`, as a corrected statement is read by the
 *  sentences naming it): every setting is printed to every call, and hashing them whole re-graded
 *  every symbol when a revise round reworded one (live CKL, 2026-10-13: 153 of 153, three times).
 *  The listing and the uses by their set, not their order: a definition added or moved re-keyed
 *  every symbol listed after it. `legacy`: the key of the passes before, settings whole and both in
 *  core order (`referee_symbols.ts` carries a verdict keyed under it over, once). */
export function symbolShownParts(ctx: Pick<SymbolContext, "core" | "slices">, name: string, legacy = false): Record<string, unknown> {
  const byName = new Map(ctx.core.symbols.map((x) => [x.name, x] as const));
  const entry = (x: CoreSymbol | undefined): unknown => (x ? { ...symbolEntryView(x), ...(x.scoped ? { scoped: x.scoped } : {}) } : { name });
  const sl = ctx.slices.get(name);
  const sorted = <T,>(xs: T[], key: (x: T) => string): T[] => (legacy ? xs : [...xs].sort((a, b) => key(a).localeCompare(key(b))));
  return {
    entry: entry(byName.get(name)),
    refs: [...new Set(byName.get(name)?.refs ?? [])].filter((r) => r !== name && byName.has(r)).sort().map((r) => entry(byName.get(r))),
    settings: legacy ? (ctx.core.sampling_model ?? null) : settingsNaming(ctx.core, name),
    listing: sorted(symbolListing(ctx.core, name), (id) => id),
    redefinitions: (sl?.redefinitions ?? []).map((r) => excerptWords(r)),
    uses: sorted((sl?.uses ?? []).map((u) => [u.node, excerptWords(u)] as [string, string]), ([node, words]) => `${node}\n${words}`),
  };
}

/** The settings (`sampling_model`) a verdict on symbol `name` can rest on, by key: those in which
 *  the symbol appears (`symbolAppears`, in any string of the setting), those naming a result that
 *  uses the symbol (`symbolUsers`; a result using an assumption or definition that uses it) — a
 *  setting says what is random in the results it governs, in words as often as in TeX — and those
 *  naming no result at all (a global convention). A setting of other results only is left out. Pure. */
export function settingsNaming(core: Pick<Core, "sampling_model" | "statements" | "assumptions" | "definitions">, name: string): Record<string, unknown> {
  const pat = symbolPattern(name);
  const strings = (v: unknown): string[] => (typeof v === "string" ? [v] : v && typeof v === "object" ? Object.values(v as object).flatMap(strings) : []);
  const users = new Set(symbolUsers(core as Core, name));
  const results = core.statements.filter((st) => users.has(st.id) || st.depends_on.some((d) => users.has(d) && !core.statements.some((s) => s.id === d)));
  const handles = (st: { id: string; tex_locator?: { label?: string | null } | null }): string[] => [st.id, ...(st.tex_locator?.label ? [st.tex_locator.label] : [])];
  // (a result is named by its paper label or core id, as `applicableSettings` reads a setting)
  const names = (text: string, h: string): boolean => {
    for (let i = text.indexOf(h); i >= 0; i = text.indexOf(h, i + 1)) {
      if (!/[\w:-]/.test(text[i - 1] ?? " ") && !/[\w:-]/.test(text[i + h.length] ?? " ")) return true;
    }
    return false;
  };
  const mine = new Set(results.flatMap(handles));
  const any = core.statements.flatMap(handles);
  const rests = (v: unknown): boolean => {
    const texts = strings(v);
    if (texts.some((t) => symbolAppears(t, pat))) return true;
    if (texts.some((t) => [...mine].some((h) => names(t, h)))) return true;
    return !texts.some((t) => any.some((h) => names(t, h)));
  };
  return Object.fromEntries(
    Object.entries(core.sampling_model ?? {})
      .filter(([, v]) => rests(v))
      .sort(([a], [b]) => a.localeCompare(b)),
  );
}

/** The introductions and uses of the symbols `names`, each passage shown once. */
function symbolPassages(ctx: SymbolContext, names: readonly string[]): string {
  const shown: Array<{ name: string; range: [number, number] }> = [];
  const shownCorrected = new Map<string, string>();
  const passage = (label: string, e: Excerpt, name: string): string => {
    const host = e.range ? shown.find((x) => e.range![0] >= x.range[0] && e.range![1] <= x.range[1]) : undefined;
    if (host) return `${label} (${e.where}): inside the passage shown above for ${host.name}.`;
    if (e.range) shown.push({ name, range: e.range });
    return `${label} (${e.where}):\n\n${e.text}`;
  };
  return names
    .map((name) => {
      const sl = ctx.slices.get(name);
      const listing = symbolListing(ctx.core, name);
      const parts = [`### ${name}`, `Core nodes listing it in free_symbols: ${listing.join(", ") || "none"}.`];
      if (!sl?.intro) parts.push("Introduced: not found as a whole symbol in the paper's body — search discovery/flat.tex (it may be written differently).");
      else parts.push(passage(`Introduced — ${sl.intro.how} at flat.tex line ${sl.intro.line}`, sl.intro, name));
      for (const r of sl?.redefinitions ?? []) parts.push(passage(`Defined again at flat.tex line ${r.line} (a possible change of meaning)`, r, name));
      for (const u of sl?.uses ?? []) parts.push(passage(`Used${u.node ? ` in ${u.node}` : ""} at flat.tex line ${u.line}`, u, name));
      for (const c of ctx.corrected?.get(name) ?? []) {
        const lead = `Corrected by a repair: ${c.node}, a statement this symbol is read from — the corrected statement replaces the printed one, so the reading is the one it uses.`;
        const key = `${c.node}\n${c.sentences.join("\n")}`;
        if (c.sentences.length === 0) parts.push(`${lead} It no longer names this symbol.`);
        else if (shownCorrected.has(key)) parts.push(`Corrected by a repair: ${c.node} (what it now says of this symbol is shown above, for ${shownCorrected.get(key)}).`);
        else {
          shownCorrected.set(key, name);
          parts.push(c.whole ? `${lead} It now reads:\n\n${c.sentences[0]}` : `${lead} Its sentences that name this symbol now read:\n\n${c.sentences.map((x) => `- ${x}`).join("\n")}`);
        }
      }
      return parts.join("\n\n");
    })
    .join("\n\n");
}

const SYMBOL_OUTPUT_BLOCK = `=== SYMBOL OUTPUT ===

Emit ONE JSON object and nothing else:

  summary  two or three sentences: what you checked, and what you found.
  symbols  exactly one entry per symbol listed under SYMBOLS TO GRADE, and no other:
${SYMBOL_FIELDS_TEXT}`;

/** A symbol call's prompt: the brief (`symbols.txt`, with its own list of the conventions that live
 * at symbol level; the referee brief's statement-level checklist is the node shards'), the symbols
 * to grade (and those they refer to), the paper's setup, and where each is introduced and used
 * (with the core nodes listing it). No core section: a symbol is graded against the paper, and the
 * one-line-per-node core cost a quarter of every symbol shard (CNS: 21 of 77 KB) for text the
 * passages already show in place; the whole core is `discovery/core.json` in the working directory. */
export function buildSymbolPrompt(ctx: SymbolContext, brief: string, names: readonly string[]): string {
  const own = new Set(names);
  const byName = new Map(ctx.core.symbols.map((x) => [x.name, x] as const));
  const referred = [...new Set(names.flatMap((n) => byName.get(n)?.refs ?? []))].filter((r) => !own.has(r) && byName.has(r));
  return [
    brief.trimEnd(),
    section(
      `SYMBOLS TO GRADE (${names.length} of ${ctx.totalSymbols})`,
      "Grade exactly these symbols; every other symbol of the table is context.\n\n" + names.map((n) => JSON.stringify(byName.get(n) ?? { name: n })).join("\n"),
    ),
    ...(referred.length > 0 ? [section("SYMBOLS THEY REFER TO (context, not graded here)", referred.map((n) => JSON.stringify(byName.get(n))).join("\n"))] : []),
    ...(ctx.core.sampling_model ? [section("SETTINGS (the sampling model as transcribed: in each setting, what is random, what is fixed, and which results use it)", Object.entries(ctx.core.sampling_model).map(([k, v]) => `- ${k}: ${typeof v === "string" ? v : JSON.stringify(v)}`).join("\n"))] : []),
    section("PAPER SETUP", setupText(ctx.setup, SETUP_SYMBOL_MAX)),
    section("WHERE EACH SYMBOL IS INTRODUCED AND USED (verbatim from discovery/flat.tex)", symbolPassages(ctx, names)),
    SYMBOL_OUTPUT_BLOCK,
  ].join("\n\n");
}

export const SYMBOL_REPLY: Record<string, unknown> = {
  type: "object",
  additionalProperties: false,
  required: ["summary", "symbols"],
  properties: { summary: { type: "string" }, symbols: { type: "array", items: V15_SYMBOL_REPLY } },
};
export const SymbolReplySchema = z.object({ summary: z.string(), symbols: z.array(SymbolVerdictSchema) });

