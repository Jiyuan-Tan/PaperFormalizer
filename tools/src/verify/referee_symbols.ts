/**
 * The V1.5 SYMBOL REFEREE: every symbol of the core's table read against the paper, BEFORE the
 * statement referees run. A symbol's meaning — random or fixed, what it is conditional on, its
 * domain, its index range, a meaning that changes later — is a property of the symbol, not of any
 * one result, and a statement referee that misreads it misjudges every result using it.
 *
 *   1. SLICES. Per symbol (`referee_slices.ts` `symbolSlices`): the paragraph that introduces it in
 *      `flat.tex` (its first defining sentence, else its first occurrence), any later defining
 *      sentence, and one or two places it is used (inside the results listing it in
 *      `free_symbols`).
 *   2. GRADING. The symbols to grade are split into shards of about `SYMBOL_SHARD_MAX`, a symbol
 *      travelling with the symbols it refers to; each symbol is graded once (user decision 2026-09-26).
 *      Each symbol: `meaning` ok | drift (+ `fix`, the corrected type / def), `ambiguity` ok |
 *      pinned (+ `reading`: a general part, and scoped clauses tagged with the results they hold
 *      in) | unresolvable, `redefined_at`.
 *   3. DELTA. A verdict is cached on its basis (`symbolBasis`: the symbol as recorded + its
 *      introducing passage + what it reads of each statement it is read from that a repair corrects,
 *      `correctedSources` + the line saying which results use it and how each is described) in
 *      `v1_5_symbols.json` / `state.verify.confirmed_symbols`; a later pass
 *      re-grades only the symbols whose basis moved (`--fresh-review` clears the cache). The corrected
 *      statements a symbol is read from are each one it is introduced in, each one its reading on file
 *      names (`resultsNamedBy`) and each one using it whose correction changed a sentence the symbol
 *      is in (`correctedSources`); a block a repair states apart counts as corrected. Of a result the
 *      reading names the basis holds — and the prompt shows — the WHOLE statement (a reading that
 *      describes a result goes stale with any sentence of it); of any other, the sentences that name
 *      the symbol (`correctedReading`), so an edit elsewhere in a repaired statement re-grades none of
 *      its other symbols. A verdict on file is
 *      carried only while its texts compile and every scoped clause is tagged with results that
 *      still use the symbol (`staleTags`: a block a repair re-keyed leaves a dead id); else the symbol
 *      is graded afresh, shown what broke. A grade
 *      on file that still holds is kept word for word (`keep`), so a re-grade moves no node basis;
 *      one that holds in part keeps those parts word for word (`keptReading`: the general part, each
 *      scoped clause — a clause the reply does not mention stays, only an explicit `drop` removes
 *      one), so only the results a reworded clause applies to are graded afresh.
 *   4. WHAT A READING DESCRIBES (user findings 2026-09-26). Each call lists, per symbol, every result
 *      it appears in with the text its reading describes — as printed, or as corrected by a confirmed
 *      repair — and the results with a PENDING suggestion, described as printed. Whether a reading does
 *      so is the referee's to judge (no text heuristic, user decision 2026-09-26).
 *
 * What the runner does with the grades (`stage_v1_5.ts`): the fixes are written into the symbol
 * table (`core_graph.ts` `buildCore`, overlay `symbols`) before the statement referees run; every
 * pinned reading is the symbol's entry in the table (its general part the `def`, its scoped clauses
 * `scoped`), which the statement referees read for the nodes naming the symbol, and is rendered once
 * in the annotated paper after the sentence introducing the symbol.
 */
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import { parseTypedCore } from "../core/core_io.js";
import type { Core, CoreSymbol, ScopedClause } from "../core/schema.js";
import { mapLimit } from "../formalization/reviewer_verdicts.js";
import { DEFAULT_REFEREE_OPTIONS, type SymbolEffort } from "../toolkit/config.js";
import type { z } from "zod";
import { resultTexName, resultsUsingSymbol, symbolSourceHash, symbolUsers } from "./core_graph.js";
import { isPendingSuggestion, readPatchFile, type Unfixable } from "./patches.js";
import { texEscapeProblems, resultWord } from "./owner_text.js";
import { mentionsSymbol, symbolAppears, symbolPattern, type SymbolPattern } from "./symbol_match.js";
import { texFieldViolations, type TexCheckContext } from "./tex_fragment_check.js";
import { excerptWords, nodeExcerpts, sectionRange, setupExcerpt, symbolSlices, SYMBOL_CAPS, type SymbolCaps, type Excerpt, type PaperIndex, type SymbolSlices } from "./referee_slices.js";
import {
  SYMBOL_REPLY,
  SymbolReplySchema,
  buildSymbolPrompt,
  symbolShownBasis,
  symbolShownParts,
  isMalformedReply,
  section,
  type SymbolContext,
} from "./referee_shard_prompts.js";
import {
  SHARD_CONCURRENCY,
  packUnits,
  shardCapacities,
  symbolLogBody,
  type RefereeCall,
  type RefereeCallMetric,
} from "./referee_shards.js";
import { VERIFY_FILES, type FlatTexLineMap, type V15SymbolVerdict } from "./types.js";
import type { SymbolVerdictSchema } from "./v1_5_schema.js";

/** Symbols per shard (at most; sizes as equal as possible). */
export const SYMBOL_SHARD_MAX = 10;

// ---------------------------------------------------------------------------------------------
// Grouping
// ---------------------------------------------------------------------------------------------

/**
 * Split the symbols `toGrade` into shards of at most `max`. Units first: in reverse table order
 * (a symbol before the symbols it refers to), each symbol with the symbols it
 * refers to, transitively, that are still unassigned (at most `max`); then best-fit packing
 * (`packUnits`), so a symbol travels with what it refers to whenever it fits.
 */
export function groupSymbolShards(symbols: readonly CoreSymbol[], toGrade: readonly string[], max = SYMBOL_SHARD_MAX): string[][] {
  const caps = shardCapacities(toGrade.length, max);
  if (caps.length === 0) return [];
  const grade = new Set(toGrade);
  const byName = new Map(symbols.map((x) => [x.name, x] as const));
  const order = symbols.filter((x) => grade.has(x.name)).map((x) => x.name).reverse();
  const assigned = new Set<string>();
  const units: string[][] = [];
  for (const name of order) {
    if (assigned.has(name)) continue;
    const unit: string[] = [];
    const queue = [name];
    while (queue.length > 0 && unit.length < max) {
      const n = queue.shift()!;
      if (assigned.has(n) || !grade.has(n)) continue;
      assigned.add(n);
      unit.push(n);
      queue.push(...(byName.get(n)?.refs ?? []));
    }
    units.push(unit);
  }
  return packUnits(units, caps).filter((s) => s.length > 0);
}

// ---------------------------------------------------------------------------------------------
// Results with a pending suggestion (user finding 2026-09-26, DFM)
// ---------------------------------------------------------------------------------------------

/**
 * A result whose repair is only SUGGESTED, awaiting the owner: a reading describes it as printed,
 * never with the hypotheses the suggestion adds (the prompt lists them).
 */
export interface PendingScope {
  node: string;
  /** Its paper label (a reading names it by `\ref{<label>}`), or null. */
  label: string | null;
  /** The environment word it is printed under ("Theorem"), for the prompt. */
  kind: string;
  /** Its printed node (the transcribed core's): the core the symbol referee grades against leaves a
   * result with no repair out, so the symbols it uses are found here. */
  statement: Core["statements"][number] | null;
}

/** The results with a pending suggestion (`patches.ts` `isPendingSuggestion`) among `unfixable`, read
 * against the printed `statements` (the transcribed core: printed text, label, kind). Pure. */
export function pendingScopes(statements: Core["statements"], unfixable: readonly Unfixable[]): PendingScope[] {
  return unfixable.filter(isPendingSuggestion).map((u) => {
    const st = statements.find((x) => x.id === u.node);
    return { node: u.node, label: st?.tex_locator?.label ?? null, kind: resultWord(st), statement: st ?? null };
  });
}

/** `pendingScopes` of the run on file: `patches.json`'s pending suggestions against the transcribed
 * core; none when either is missing. */
export async function readPendingScopes(runDir: string): Promise<PendingScope[]> {
  const file = await readPatchFile(runDir).catch(() => null);
  if (!file || !file.unfixable.some(isPendingSuggestion)) return [];
  const tr = path.join(runDir, VERIFY_FILES.coreTranscribed);
  if (!existsSync(tr)) return [];
  const core = parseTypedCore(await readFile(tr, "utf8"), `verify core ${tr}`);
  return pendingScopes(core.statements, file.unfixable);
}


/** A reading as the referee replies it: a null text is a piece kept from the grade on file. */
type ReplyReading = NonNullable<z.infer<typeof SymbolVerdictSchema>["reading"]>;

const clauseKey = (results: readonly string[]): string => [...new Set(results)].sort().join("\n");

/** The scoped clauses of a reading on file tagged with an id that is no result using the symbol
 * (`users`: `resultsUsingSymbol`) — a block a repair re-keyed (`core_graph.ts` `splitCorollaryId`), a
 * result left out of the core, one that no longer names the symbol — each with those ids. */
export function staleTags(reading: V15SymbolVerdict["reading"], users: ReadonlySet<string>): Array<{ clause: ScopedClause; gone: string[] }> {
  return (reading?.scoped ?? []).flatMap((clause) => ((gone) => (gone.length > 0 ? [{ clause, gone }] : []))(clause.results.filter((id) => !users.has(id))));
}

/**
 * A replied reading merged onto the reading on file (`on`), word for word where it is kept: a null
 * general part is the general part on file. The clauses on file come first, in their order, each
 * found in the reply by its results (the same set): a null text keeps it, a text replaces it, a
 * `drop` (the reason) removes it — and one the reply does NOT mention is KEPT: omission never
 * deletes. An unmentioned clause with a tag that is `live` no more (`staleTags`) is kept for its live
 * results, the dead tags cut; with no live tag left it is kept AS IT IS, which the contract refuses
 * (its tags name no result): the referee says where it goes — re-tagged, or dropped with a reason.
 * Then the reply's new clauses; one whose results overlap an unmentioned clause on file would leave
 * both binding the shared result: `problem` is told (a contract violation — the referee replaces or
 * drops the old one, or keeps it by listing it). A piece with nothing on file to keep comes out
 * EMPTY, which the contract refuses (`symbolContract`). `dropped` is told each removal. Pure.
 */
export function keptReading(
  r: ReplyReading,
  on: V15SymbolVerdict["reading"],
  opts: { live?: (id: string) => boolean; dropped?: (c: ScopedClause, why: string) => void; problem?: (why: string) => void } = {},
): NonNullable<V15SymbolVerdict["reading"]> {
  const reply = r.scoped ?? [];
  const taken = new Set<number>();
  const scoped: ScopedClause[] = [];
  const unmentioned: ScopedClause[] = [];
  for (const c of on?.scoped ?? []) {
    const i = reply.findIndex((x, k) => !taken.has(k) && clauseKey(x.results) === clauseKey(c.results));
    const x = i >= 0 ? reply[i]! : null;
    if (x === null) {
      const live = c.results.filter((id) => opts.live?.(id) ?? true);
      const kept = live.length > 0 && live.length < c.results.length ? { results: live, text: c.text } : c;
      scoped.push(kept);
      unmentioned.push(kept);
      continue;
    }
    taken.add(i);
    if (x.drop?.trim()) opts.dropped?.(c, x.drop.trim());
    else scoped.push(x.text === null ? c : { results: [...new Set(x.results)], text: x.text });
  }
  // A `drop` of a clause that is not on file drops nothing.
  reply.forEach((x, k) => {
    if (taken.has(k) || x.drop?.trim()) return;
    const results = [...new Set(x.results)];
    for (const c of unmentioned) {
      const shared = c.results.filter((id) => results.includes(id));
      if (shared.length > 0) opts.problem?.(`its new scoped clause [${results.join(", ")}] and the clause on file [${c.results.join(", ")}], which the reply does not list, would both hold in ${shared.join(", ")} — list the clause on file too: with a text (it replaces it), with text null (it stays beside the new one) or with \`drop\`.`);
    }
    scoped.push({ results, text: x.text ?? "" });
  });
  return { reading: r.reading ?? on?.reading ?? "", evidence: r.evidence, ...(scoped.length > 0 ? { scoped } : {}) };
}

/** Exact checks a symbol reply must pass (the schema cannot express them): one entry per owed
 * symbol; drift ⇔ a fix with a corrected type or def; pinned ⇔ a reading; a change of meaning is
 * pinned or unresolvable; unresolvable says why; a reading has a general part, and each scoped clause
 * a text and results that use the symbol (`users`: `resultsUsingSymbol`; absent: not
 * checked), no two clauses the same results; a reading or fix is well-formed TeX. What a reading
 * says is the referee's to judge, never a text heuristic (user decision 2026-09-26). */
export function symbolContract(
  verdicts: readonly V15SymbolVerdict[],
  owes: ReadonlySet<string>,
  known: ReadonlySet<string>,
  users?: (name: string) => ReadonlySet<string>,
): string[] {
  const out: string[] = [];
  const seen = new Set<string>();
  for (const v of verdicts) {
    if (!known.has(v.name)) out.push(`symbol "${v.name}" is not in the symbol table (unknown name — copy the name exactly).`);
    if (seen.has(v.name)) out.push(`symbol "${v.name}" is graded more than once.`);
    seen.add(v.name);
    const fixed = !!(v.fix && ((v.fix.type ?? "").trim() || (v.fix.space ?? "").trim() || (v.fix.def ?? "").trim()));
    if (v.meaning === "drift" && !fixed) out.push(`symbol "${v.name}" is graded meaning "drift" with no fix — give the corrected type, space and/or def.`);
    if (v.meaning !== "drift" && v.fix) out.push(`symbol "${v.name}" carries a fix but is graded meaning "${v.meaning}" — a fix goes with "drift" only.`);
    if (v.ambiguity === "pinned" && !v.reading) out.push(`symbol "${v.name}" is graded ambiguity "pinned" with no reading — supply it, or grade "unresolvable".`);
    if (v.ambiguity !== "pinned" && v.reading) out.push(`symbol "${v.name}" carries a reading but is graded ambiguity "${v.ambiguity}" — a reading goes with "pinned" only.`);
    if (v.redefined_at && v.ambiguity === "ok") out.push(`symbol "${v.name}" has redefined_at but ambiguity "ok" — a change of meaning is "pinned" (say which meaning holds where) or "unresolvable".`);
    if (v.reading) {
      if (!v.reading.reading.trim()) out.push(`symbol "${v.name}": its reading has no general part — write it (null keeps the general part of a grade on file; there is none to keep).`);
      const use = users?.(v.name);
      const keys = new Set<string>();
      for (const c of v.reading.scoped ?? []) {
        const at = `symbol "${v.name}": its reading's scoped clause [${c.results.join(", ")}]`;
        if (c.results.length === 0) out.push(`${at} names no result — tag it with the ids of the results it holds in, or move it to the general part.`);
        if (!c.text.trim()) out.push(`${at} has no text — write it (null keeps the clause ON FILE with exactly these results; there is none).`);
        const unknown = use ? c.results.filter((id) => !use.has(id)) : [];
        if (unknown.length > 0) out.push(`${at} is tagged with ${unknown.join(", ")}, not the id of a result using the symbol — copy the ids from THE TEXT EACH READING DESCRIBES.`);
        if (keys.has(clauseKey(c.results))) out.push(`${at} repeats the results of another clause — one clause per set of results.`);
        keys.add(clauseKey(c.results));
      }
    }
    // A reading or fix is written into the core and shown to the author: never broken TeX (C6).
    for (const [field, text] of [["reading", v.reading?.reading], ...(v.reading?.scoped ?? []).map((c) => [`reading's scoped clause [${c.results.join(", ")}]`, c.text] as const), ["fix", `${v.fix?.type ?? ""} ${v.fix?.space ?? ""} ${v.fix?.def ?? ""}`.trim()]] as const) {
      if (text) for (const p of texEscapeProblems(text, field)) out.push(`symbol "${v.name}": its ${field} ${p}.`);
    }
    if (v.ambiguity === "unresolvable" && !v.detail.trim()) out.push(`symbol "${v.name}" is graded "unresolvable" with an empty detail — give the readings in question.`);
  }
  const missing = [...owes].filter((n) => !seen.has(n));
  if (missing.length > 0) out.push(`${missing.length} symbol(s) carry no verdict: ${missing.join(", ")}. Emit exactly one entry per symbol listed under SYMBOLS TO GRADE.`);
  return out;
}


/** What a symbol retry shows of the previous reply: each text a violation names (`symbol "<name>": its
 * reading …` / `its fix …`), verbatim as the model wrote it, so the retry corrects that text. Pure. */
export function symbolRetryEcho(verdicts: readonly V15SymbolVerdict[], violations: readonly string[]): string {
  const parts: string[] = [];
  for (const v of verdicts) {
    const vs = violations.filter((x) => x.startsWith(`symbol "${v.name}"`));
    if (vs.length === 0) continue;
    const texts: string[] = [];
    if (v.reading && vs.some((x) => x.includes("its reading"))) texts.push(`  reading: ${v.reading.reading}`, ...(v.reading.scoped ?? []).map((c) => `  scoped [${c.results.join(", ")}]: ${c.text}`));
    if (v.fix && vs.some((x) => x.includes("its fix"))) texts.push(`  fix type: ${v.fix.type ?? "null"}`, `  fix space: ${v.fix.space ?? "null"}`, `  fix def: ${v.fix.def ?? "null"}`);
    if (texts.length > 0) parts.push(`symbol "${v.name}", your previous text, verbatim:\n${texts.join("\n")}`);
  }
  return parts.join("\n\n");
}

/** The symbol verdicts' texts the core and the annotated paper take — the reading, the table fix —
 * compiled against the paper's preamble (`tex_fragment_check.ts`): the contract's async half. */
export function symbolTexViolations(verdicts: readonly V15SymbolVerdict[], ctx: TexCheckContext | null | undefined): Promise<string[]> {
  return texFieldViolations(
    verdicts.flatMap((v) => [
      { where: `symbol "${v.name}": its reading`, text: v.reading?.reading, kind: "note" as const },
      ...(v.reading?.scoped ?? []).map((c) => ({ where: `symbol "${v.name}": its reading's scoped clause [${c.results.join(", ")}]`, text: c.text, kind: "note" as const })),
      { where: `symbol "${v.name}": its fix type`, text: v.fix?.type, kind: "note" as const },
      { where: `symbol "${v.name}": its fix space`, text: v.fix?.space, kind: "note" as const },
      { where: `symbol "${v.name}": its fix def`, text: v.fix?.def, kind: "note" as const },
    ]),
    ctx,
  );
}

// ---------------------------------------------------------------------------------------------
// The pass
// ---------------------------------------------------------------------------------------------

/** The cache basis of a symbol's verdict — what its referee is shown, no less: the symbol as
 * recorded (its type and def by their meaning, `symbolSourceHash`), the words of its introducing
 * passage (`excerptWords`: no line numbers, so an upstream line shift moves nothing), — when a
 * repair corrects a statement it is read from (`correctedSources`) — what the verdict reads of each
 * (`corrected`, one text per statement: `correctedBasisText`; the repair's words verbatim: a change
 * to them is real), and `shown`, the rest of what its call prints of it (`symbolShownBasis`: the
 * whole entry, the entries it refers to, the settings, its other passages). `shown` absent: the
 * basis of the passes before 2026-10-07, which hashed none of that (`runSymbolPass` carries it over
 * from a complete pass only). */
export function symbolBasis(sym: CoreSymbol, intro: Pick<Excerpt, "text"> | string | null | undefined, corrected: readonly string[] = [], shown?: string): string {
  const words = excerptWords(typeof intro === "string" ? { text: intro } : intro);
  return createHash("sha256").update(`${symbolSourceHash(sym)}\n${words}${corrected.map((c) => `\n${c}`).join("")}${shown === undefined ? "" : `\nshown\n${shown}`}`).digest("hex");
}

/** The parts of `symbolBasis`, each hashed on its own: `source` (the entry's type and def),
 * `intro` (its introducing passage), `corrected` (what the verdict reads of corrected statements)
 * and each part of what else the call shows (`symbolShownParts`). Recorded with the verdict
 * (`basis_parts`); a pass that grades the symbol afresh names the parts that moved. Pure. */
export function symbolBasisParts(sym: CoreSymbol, intro: Pick<Excerpt, "text"> | string | null | undefined, corrected: readonly string[], shown: Record<string, unknown>): Record<string, string> {
  const sha = (s: string): string => createHash("sha256").update(s).digest("hex").slice(0, 16);
  const words = excerptWords(typeof intro === "string" ? { text: intro } : intro);
  return {
    source: sha(symbolSourceHash(sym)),
    intro: sha(words),
    corrected: sha(corrected.join("\n")),
    ...Object.fromEntries(Object.entries(shown).map(([k, v]) => [k, sha(JSON.stringify(v))])),
  };
}

/** `why re-graded — …`: of the symbols graded afresh, how many moved on each part of their basis
 * (a symbol counts under every part that moved), how many are new to the table, how many have a
 * verdict with no parts on record (graded before they were recorded). Pure. */
export function symbolRegradeLine(toGrade: readonly string[], parts: (name: string) => Record<string, string>, prior: (name: string) => Pick<V15SymbolVerdict, "basis_parts"> | undefined): string {
  const moved = new Map<string, number>();
  let fresh = 0;
  let unrecorded = 0;
  for (const name of toGrade) {
    const pv = prior(name);
    if (!pv) {
      fresh += 1;
      continue;
    }
    if (!pv.basis_parts) {
      unrecorded += 1;
      continue;
    }
    for (const [k, h] of Object.entries(parts(name))) if (pv.basis_parts[k] !== h) moved.set(k, (moved.get(k) ?? 0) + 1);
  }
  const counts = [...moved.entries()].sort((a, b) => b[1] - a[1]).map(([k, n]) => `${n} ${k}`);
  if (fresh > 0) counts.push(`${fresh} new`);
  if (unrecorded > 0) counts.push(`${unrecorded} no parts on record`);
  return `why re-graded — ${counts.join(", ") || "nothing moved"}`;
}

/** A statement a repair corrects: its printed text and its corrected text. */
export interface CorrectedStatement {
  printed: string;
  text: string;
}

/** The sentences of `text`, verbatim and in order: cut after `.` or `;` and at a blank line — a
 * lead-in travels with what it introduces (a piece ending in `:`, or in `;` before a display, is one
 * sentence with the next: "for every $h$:" quantifies the display it opens). `legacy`: the cut of the
 * earlier bases (`transitionBases`), after `:` too, nothing joined. */
export function sentencesOf(text: string, legacy = false): string[] {
  const pieces = text.split(/(?<=[.;:])\s+|\n\s*\n/).map((s) => s.trim()).filter(Boolean);
  if (legacy) return pieces;
  const out: string[] = [];
  let lead = "";
  for (const [i, s] of pieces.entries()) {
    const cur = lead ? `${lead} ${s}` : s;
    const next = pieces[i + 1];
    const opens = next !== undefined && (s.endsWith(":") || (s.endsWith(";") && /^(?:\\\[|\$\$|\\begin\{)/.test(next)));
    if (opens) lead = cur;
    else (out.push(cur), (lead = ""));
  }
  return out;
}

/** The sentences of `text` that name the symbol (`sentencesOf`): it appears in them, whole, decorated
 * or inside a compound (`symbol_match.ts` `symbolAppears`). `legacy`: as the earlier bases read them —
 * the whole symbol only, the earlier cut. */
export function sentencesNaming(text: string, pat: SymbolPattern, legacy = false): string[] {
  return sentencesOf(text, legacy).filter((s) => (legacy ? mentionsSymbol(s, pat) : symbolAppears(s, pat)));
}

const REF_LABELS = /\\[A-Za-z]*ref\*?\s*\{([^{}]*)\}/g;

/**
 * The results a reading is ABOUT — those it names: a scoped clause's `results`, and in its general
 * part, its clauses' texts and its evidence a `\ref{<label>}` (any `\…ref`) of a result, a result's
 * id, or — with the paper (`px`) — the `\ref` of a section ("the results of Section~\ref{…}"): every
 * result printed in it (`labelPassage`). A named result names the blocks a repair split off it too
 * (`split_from`: a label-less block is printed "the result split from <its parent>"; an umbrella's
 * blocks). A reading that describes a result is read from that result WHOLE (`correctedReading`): it
 * goes stale when the result changes in a sentence that does not name the symbol (live CNS: a
 * reading said a theorem "states bounds using …" after a repair removed them). RESIDUAL: a result
 * named only by its heading in words is not seen — the symbol prompt asks for `\ref` or the id. Pure.
 */
export function resultsNamedBy(
  reading: V15SymbolVerdict["reading"],
  statements: ReadonlyArray<{ id: string; split_from?: string; tex_locator?: { label?: string | null } | null }>,
  px?: PaperIndex,
): Set<string> {
  const out = new Set<string>();
  if (!reading) return out;
  const text = [reading.reading, reading.evidence, ...(reading.scoped ?? []).map((c) => c.text)].join("\n");
  const labels = new Set([...text.matchAll(REF_LABELS)].flatMap((m) => m[1]!.split(",").map((l) => l.trim())));
  const tags = new Set((reading.scoped ?? []).flatMap((c) => c.results));
  const ownLabels = new Set(statements.flatMap((st) => st.tex_locator?.label ?? []));
  const sections = px ? [...labels].filter((l) => !ownLabels.has(l)).flatMap((l) => ((r) => (r ? [r] : []))(sectionRange(px, l))) : [];
  const lineOf = (label: string): number => (px ? px.lines.findIndex((l) => l.includes(`\\label{${label}}`)) + 1 : 0);
  for (const st of statements) {
    const label = st.tex_locator?.label;
    const byId = new RegExp(`(?<![A-Za-z0-9:-])${st.id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}(?![A-Za-z0-9-])`).test(text);
    const at = label && sections.length > 0 ? lineOf(label) : 0;
    if (tags.has(st.id) || (label && labels.has(label)) || byId || (at > 0 && sections.some(([a, b]) => at >= a && at <= b))) out.add(st.id);
  }
  for (const st of statements) if (st.split_from && out.has(st.split_from)) out.add(st.id);
  return out;
}

/** The `\ref` labels of a reading that the paper holds nowhere (no result's label, no `\label` in
 * `flat.tex`): what they name cannot be found, so the reading may be about any result the symbol is
 * used in — the caller reads those whole (the safe side). */
/** The results a symbol's reading is about (`resultsNamedBy`); with a `\ref` the paper holds
 * nowhere, every result the symbol is used in (`users`). Pure. */
export function readingAbout(
  reading: V15SymbolVerdict["reading"],
  statements: ReadonlyArray<{ id: string; split_from?: string; tex_locator?: { label?: string | null } | null }>,
  px: PaperIndex,
  users: () => Iterable<string>,
): Set<string> {
  const named = resultsNamedBy(reading, statements, px);
  return unresolvedRefs(reading, statements, px).length > 0 ? new Set([...named, ...users()]) : named;
}

export function unresolvedRefs(reading: V15SymbolVerdict["reading"], statements: ReadonlyArray<{ tex_locator?: { label?: string | null } | null }>, px: PaperIndex): string[] {
  if (!reading) return [];
  const text = [reading.reading, reading.evidence, ...(reading.scoped ?? []).map((c) => c.text)].join("\n");
  const own = new Set(statements.flatMap((st) => st.tex_locator?.label ?? []));
  return [...new Set([...text.matchAll(REF_LABELS)].flatMap((m) => m[1]!.split(",").map((l) => l.trim())))].filter((l) => l && !own.has(l) && !px.lines.some((line) => line.includes(`\\label{${l}}`)));
}

/**
 * What a symbol's verdict READS of a corrected statement it is read from — what its prompt shows and
 * its basis hashes, the same text: the statement WHOLE when the reading on file is about that result
 * (`about`, `resultsNamedBy`), or when the symbol is found in neither the printed nor the corrected
 * text (listed in `free_symbols` under another spelling), so it cannot be placed; else the sentences
 * of the corrected statement that name the symbol (`sentencesNaming`; none: the correction removed
 * it) — an edit elsewhere in a result the reading does not describe re-grades none of its symbols.
 */
export function correctedReading(name: string, c: CorrectedStatement, about = false, legacy = false): { sentences: string[]; whole: boolean } {
  if (about) return { sentences: [c.text], whole: true };
  const pat = symbolPattern(name);
  const sentences = sentencesNaming(c.text, pat, legacy);
  if (sentences.length === 0 && sentencesNaming(c.printed, pat, legacy).length === 0) return { sentences: [c.text], whole: true };
  return { sentences, whole: false };
}

/** One corrected statement in a symbol's basis (`symbolBasis` `corrected`): which statement, and what
 * the verdict reads of it (`correctedReading`; a sentence without its whitespace). */
export function correctedBasisText(node: string, r: { sentences: readonly string[]; whole: boolean }): string {
  return `${node}\n${r.whole ? r.sentences[0] : r.sentences.map((x) => x.replace(/\s+/g, "")).join("\n")}`;
}

/** Whether a correction changed a sentence that names the symbol (one added, dropped or
 * reworded; `sentencesNaming`): a repair that touches only sentences the symbol is not in leaves its
 * reading alone. A symbol found in neither text (listed in `free_symbols` under another
 * spelling) cannot be placed: any change to the text then counts. */
export function correctionTouchesSymbol(name: string, c: CorrectedStatement, legacy = false): boolean {
  const pat = symbolPattern(name);
  const squeezed = (t: string): string[] => sentencesNaming(t, pat, legacy).map((s) => s.replace(/\s+/g, "")).sort();
  const before = squeezed(c.printed);
  const after = squeezed(c.text);
  if (before.length === 0 && after.length === 0) return c.printed.replace(/\s+/g, "") !== c.text.replace(/\s+/g, "");
  return before.length !== after.length || before.some((s, i) => s !== after[i]);
}

/**
 * The corrected statements a symbol is READ FROM (C5, user finding 2026-09-25: a symbol's reading kept
 * indexing a process as the printed theorem did while the corrected theorem changed it): each
 * statement of `corrected` whose printed passage holds the symbol's introduction or a redefinition,
 * or a line of its slices; each one the reading on file is about (`about`, `resultsNamedBy`); and each
 * statement using the symbol (`symbolUsers`, user finding
 * 2026-09-26: a reading kept the printed probability model after a confirmed correction changed it
 * in a result that uses the symbol without introducing it) whose correction changed a sentence the
 * symbol is in (`correctionTouchesSymbol`) — a repair elsewhere in a result the reading does not
 * describe re-grades none of its symbols. Their ids, sorted. What the symbol reads of each
 * (`correctedReading`) is part of its verdict basis (`symbolBasis`), so a correction of that re-grades
 * the symbol. `legacy`: as the earlier bases chose them (`transitionBases`). Pure.
 */
export function correctedSources(
  px: PaperIndex,
  core: Core,
  sl: SymbolSlices | undefined,
  corrected: ReadonlyMap<string, CorrectedStatement>,
  about: ReadonlySet<string> = new Set(),
  legacy = false,
): string[] {
  if (!sl || corrected.size === 0) return [];
  // Located by the PRINTED text: the passage the slices were cut from.
  const printedCore: Core = { ...core, statements: core.statements.map((st) => (corrected.has(st.id) ? { ...st, statement: corrected.get(st.id)!.printed } : st)) };
  const lines = [sl.intro?.line, ...sl.redefinitions.map((r) => r.line)].filter((l): l is number => typeof l === "number");
  const used = new Set(sl.uses.map((u) => u.node).filter((n): n is string => !!n));
  const users = new Set(symbolUsers(core, sl.name));
  const squeeze = (t: string): string => t.replace(/\s+/g, "");
  // A slice line whose text is in the printed statement (the statement located or not): the
  // introduction's and redefinitions' lines, and the lines of the use slices.
  const lineTexts = (ls: readonly number[]): string[] => ls.map((l) => squeeze(px.lines[l - 1] ?? "")).filter((t) => t.length >= 12);
  const defines = lineTexts(lines);
  const uses = lineTexts(sl.uses.map((u) => u.line));
  const out: string[] = [];
  for (const [id, c] of corrected) {
    const printed = squeeze(c.printed);
    // A block a repair states apart has no printed passage to hold an introduction.
    const range = printed ? nodeExcerpts(px, printedCore, id).statement.range : null;
    const introduces = !!printed && ((!!range && lines.some((l) => l >= range[0] && l <= range[1])) || defines.some((t) => printed.includes(t)));
    const usesIt = used.has(id) || users.has(id) || (!!printed && uses.some((t) => printed.includes(t)));
    if (introduces || about.has(id) || (usesIt && correctionTouchesSymbol(sl.name, c, legacy))) out.push(id);
  }
  return out.sort();
}

export interface SymbolMetrics {
  /** Codex reasoning effort of every symbol call (`referee.symbol_effort`). */
  effort: SymbolEffort;
  /** Symbols in the table / graded this pass / carried. */
  symbols: number;
  graded: number;
  carried: number;
  shards: string[][];
  calls: RefereeCallMetric[];
  /** Prompt bytes of every call (retries included). */
  shard_bytes: number;
  /** Symbols whose new grading broke the contract past its retry: set aside, their verdict on file
   * kept (or none), graded afresh next pass. */
  set_aside?: Array<{ name: string; why: string }>;
  /** Why the graded symbols were not carried (`symbolRegradeLine`); absent when none was graded. */
  regrade_why?: string;
  wall_ms: number;
}

export interface SymbolPassInput {
  /** The core as transcribed and patched, WITHOUT the symbol fixes: its table is what is graded. */
  core: Core;
  px: PaperIndex;
  lineMap: FlatTexLineMap | null;
  /** The verdicts on file (`v1_5_symbols.json`) and the cache (`state.verify.confirmed_symbols`). */
  prior: readonly V15SymbolVerdict[];
  confirmed: Readonly<Record<string, string>>;
  /** The verdicts on file are of a COMPLETE V1.5 pass (`stage_v1_5.ts` `priorPassComplete`): the state
   * the owner accepted — one keyed under an earlier rule is carried while that key holds, whatever
   * its reading names. Absent: not complete. */
  priorComplete?: boolean;
  /** The statements the file's repairs correct, by node (`correctedSources`): a symbol read from one
   * is re-graded when a sentence naming it changes, shown those sentences. */
  corrected?: ReadonlyMap<string, CorrectedStatement>;
  /** Parallel calls (`theoremchecker.json` `referee.max_concurrent`; default `SHARD_CONCURRENCY`). */
  concurrency?: number;
  /** The results with a pending suggestion (`pendingScopes`): a reading describes them as printed (the
   * prompt lists them). Absent: read from the run (`tex.runDir`), else none. */
  pending?: readonly PendingScope[];
  /** Codex reasoning effort of every symbol shard (`theoremchecker.json` `referee.symbol_effort`;
   * default "medium"). */
  effort?: SymbolEffort;
  /** `symbols.txt` (its own conventions list; the referee brief's statement-level checklist is the
   * node shards'). */
  briefs: { symbols: string };
  scope: string;
  ask: (c: RefereeCall) => Promise<unknown>;
  /** The run, for the compile check of every reading and fix (`symbolTexViolations`); absent: none. */
  tex?: TexCheckContext;
  log: (m: string) => void;
}

export type SymbolPassResult =
  | { ok: true; symbols: V15SymbolVerdict[]; confirmed: Record<string, string>; metrics: SymbolMetrics }
  | { ok: false; message: string; metrics: SymbolMetrics };

class SymbolContractFailure extends Error {}

const bytesOf = (s: string): number => Buffer.byteLength(s, "utf8");

/** Where each symbol is introduced and used, in the given form; one node-location cache. */
export function allSymbolSlices(px: PaperIndex, core: Core, caps: SymbolCaps = SYMBOL_CAPS): Map<string, SymbolSlices> {
  const cache = new Map<string, Excerpt>();
  const excerptOf = (id: string): Excerpt => {
    if (!cache.has(id)) cache.set(id, nodeExcerpts(px, core, id).statement);
    return cache.get(id)!;
  };
  return new Map(core.symbols.map((x) => [x.name, symbolSlices(px, core, x.name, caps, excerptOf)] as const));
}

/** Grade the symbol table (the delta only), in shards. */
export async function runSymbolPass(inp: SymbolPassInput): Promise<SymbolPassResult> {
  const t0 = Date.now();
  const table = inp.core.symbols;
  const known = new Set(table.map((x) => x.name));
  const full = allSymbolSlices(inp.px, inp.core);
  const pending = inp.pending ?? (inp.tex?.runDir ? await readPendingScopes(inp.tex.runDir) : []);
  // A block a repair states apart (`split_from`) is the repair's text like a corrected statement, with
  // nothing printed: the symbols it uses are read from it too.
  const corrected = new Map<string, CorrectedStatement>([
    ...inp.core.statements.flatMap((st) => (st.split_from && !inp.corrected?.has(st.id) ? [[st.id, { printed: "", text: st.statement }] as const] : [])),
    ...(inp.corrected ?? []),
  ]);
  const priorBy = new Map(inp.prior.map((v) => [v.name, v] as const));
  // The results each symbol is used in (`resultsUsingSymbol`), those with a pending suggestion included
  // (the core graded leaves a result with no repair out): what a clause may be tagged with.
  const withPending: Core = { ...inp.core, statements: [...inp.core.statements, ...pending.flatMap((x) => (x.statement && !inp.core.statements.some((st) => st.id === x.node) ? [x.statement] : []))] };
  const users = new Map<string, Set<string>>();
  const usersOf = (n: string): ReadonlySet<string> => users.get(n) ?? users.set(n, new Set(resultsUsingSymbol(withPending, n))).get(n)!;
  const byNode = new Map(withPending.statements.map((st) => [st.id, st] as const));
  const pendingBy = new Map(pending.map((x) => [x.node, x] as const));
  const nameOf = (id: string): string => {
    const st = byNode.get(id);
    const label = st?.tex_locator?.label ?? pendingBy.get(id)?.label ?? null;
    const kind = resultWord(st);
    if (label) return `${kind}~\\ref{${label}}`;
    return st?.split_from ? `${resultTexName(withPending, id)} (a repair states it apart; the paper does not print it)` : `${kind} ${id} (no label: name it by this id)`;
  };
  const aboutOf = (n: string, reading: V15SymbolVerdict["reading"]): Set<string> => readingAbout(reading, withPending.statements, inp.px, () => usersOf(n));
  /** What a verdict of symbol `x` with `reading` on file READS, shown and hashed alike: of each
   * corrected statement it is read from (`correctedSources`; whole when the reading is about it),
   * what `correctedReading` gives; and the line of THE TEXT EACH READING DESCRIBES — every result the
   * symbol is used in, as printed, corrected or pending. */
  const readsOf = (x: CoreSymbol, reading: V15SymbolVerdict["reading"]): { sources: string[]; reads: Array<{ node: string; sentences: string[]; whole: boolean }>; describes: string; basis: string; unshown: string; legacyShown: string; parts: Record<string, string> } => {
    const about = aboutOf(x.name, reading);
    const sources = correctedSources(inp.px, inp.core, full.get(x.name), corrected, about);
    const reads = sources.map((id) => ({ node: id, ...correctedReading(x.name, corrected.get(id)!, about.has(id)) }));
    const how = (id: string): string =>
      corrected.has(id)
        ? `${byNode.get(id)?.split_from ? "as a confirmed repair states it" : "as corrected by a confirmed repair"} (${sources.includes(id) ? "what it now says of the symbol is shown above" : "its text is in discovery/core.json; the repair changed no sentence the symbol is in"})`
        : pendingBy.has(id)
          ? "AS PRINTED — its repair is only suggested, awaiting the owner"
          : "as printed";
    const uses = [...usersOf(x.name)];
    const describes = `- ${x.name}: ${uses.length > 0 ? uses.map((id) => `${nameOf(id)} [${id}] ${how(id)}`).join("; ") : "no result uses it"}`;
    const read = [...reads.map((r) => correctedBasisText(r.node, r)), `describes\n${describes}`];
    const intro = full.get(x.name)?.intro;
    const ctx = { core: inp.core, slices: full };
    return {
      sources,
      reads,
      describes,
      basis: symbolBasis(x, intro, read, symbolShownBasis(ctx, x.name)),
      unshown: symbolBasis(x, intro, read),
      // (the key of the passes to 2026-10-13: every setting, the listing and the uses in core order)
      legacyShown: symbolBasis(x, intro, read, symbolShownBasis(ctx, x.name, true)),
      parts: symbolBasisParts(x, intro, read, symbolShownParts(ctx, x.name)),
    };
  };
  const read = new Map(table.map((x) => [x.name, readsOf(x, priorBy.get(x.name)?.reading ?? null)] as const));
  const bases = new Map(table.map((x) => [x.name, read.get(x.name)!.basis] as const));
  // TRANSITION (remove once every run on file has passed one V1.5 pass with this code): a verdict
  // recorded on an earlier basis is carried while that basis still holds — nothing it read changed
  // under the rule it was graded by — and re-keyed to the basis above, no call; of a COMPLETE pass
  // only (`priorComplete`, below). The earlier bases: the one above without what else the call shows
  // (`unshown`, to 2026-10-07); each corrected statement the symbol was read from WHOLE; then its
  // sentences naming the whole symbol only (`legacy`), with no line of what the reading describes
  // and no block. (The key with every setting, the listing and the uses in core order — to
  // 2026-10-13, when one reworded setting re-graded every symbol — hashes a superset of the basis
  // above, so it is carried from any pass, paused or not: `legacyShown`, in the carry below.)
  const transitionBases = new Map(
    table.map((x) => {
      const old = inp.corrected ?? new Map<string, CorrectedStatement>();
      const ids = correctedSources(inp.px, inp.core, full.get(x.name), old, new Set(), true);
      const intro = full.get(x.name)?.intro;
      const whole = ids.map((id) => `\n${id}\n${old.get(id)!.text}`).join("");
      const everyUser = [...new Set([...ids, ...symbolUsers(inp.core, x.name).filter((id) => old.has(id))])].sort().map((id) => `\n${id}\n${old.get(id)!.text}`).join("");
      return [
        x.name,
        [
          read.get(x.name)!.unshown,
          symbolBasis(x, intro, ids.map((id) => `${id}\n${old.get(id)!.text}`)),
          symbolBasis(x, intro, ids.map((id) => correctedBasisText(id, correctedReading(x.name, old.get(id)!, false, true)))),
          // … and, before the introducing passage was read by its words alone (2026-10-06), verbatim —
          // with those sources, or (earlier still) with every corrected statement using the symbol.
          createHash("sha256").update(`${symbolSourceHash(x)}\n${intro?.text ?? ""}${whole}`).digest("hex"),
          createHash("sha256").update(`${symbolSourceHash(x)}\n${intro?.text ?? ""}${everyUser}`).digest("hex"),
        ],
      ] as const;
    }),
  );
  // That carry is of a pass on file that is COMPLETE (`priorComplete`: the state its owner accepted,
  // carried over as it stands, owner decision 2026-10-07). A paused or halted pass grades afresh
  // every verdict on an earlier basis: none of them covers all its referee was shown (the entry's
  // other fields, the settings, the entries referred to), and nothing says those stood still.
  // A verdict on file whose reading or fix does not compile is graded afresh: the check at the source
  // holds for what is carried too (the annotated paper prints it).
  const staleWhy = new Map((await Promise.all(inp.prior.map(async (v) => [v.name, await symbolTexViolations([v], inp.tex)] as const))).filter(([, w]) => w.length > 0));
  const stale = new Set(staleWhy.keys());
  if (stale.size > 0) inp.log(`symbol delta: ${stale.size} verdict(s) whose texts do not compile are graded afresh: ${[...stale].join(", ")}`);
  // A verdict on file with a clause tagged with an id that is no result using the symbol any more is
  // graded afresh too (a carried verdict passes the tag half of the contract, like a new one): the
  // clause would reach no node. Shown which ids are gone and, for a block a repair re-keyed, the
  // blocks now split from the same result.
  const tagWhy = new Map(
    inp.prior.flatMap((v) => {
      if (!known.has(v.name)) return [];
      const lines = staleTags(v.reading, usersOf(v.name)).map(({ clause, gone }) => {
        const parents = [...new Set(gone.flatMap((id) => v.split_tags?.[id] ?? []))];
        const heirs = withPending.statements.filter((st) => st.split_from && parents.includes(st.split_from) && usersOf(v.name).has(st.id) && !clause.results.includes(st.id)).map((st) => st.id);
        return `symbol "${v.name}": the clause on file scoped [${clause.results.join(", ")}] is tagged with ${gone.join(", ")}, no longer a result using the symbol${heirs.length > 0 ? ` — now split from the same result (${parents.map((p) => resultTexName(withPending, p)).join(", ")}): ${heirs.join(", ")}` : ""}.`;
      });
      return lines.length > 0 ? [[v.name, lines] as const] : [];
    }),
  );
  if (tagWhy.size > 0) inp.log(`symbol delta: ${tagWhy.size} verdict(s) with a scoped clause tagged with a result that is gone are graded afresh: ${[...tagWhy.keys()].join(", ")}`);
  const carried: V15SymbolVerdict[] = [];
  const toGrade: string[] = [];
  for (const x of table) {
    const pv = priorBy.get(x.name);
    const basis = bases.get(x.name)!;
    const key = inp.confirmed[x.name];
    // A verdict is carried while all its referee was shown stands — an `unresolvable` one too, word
    // for word: its line is printed to the shard of every node listing the symbol and read into
    // their bases (`stage_v1_5.ts` `symbolBasisExtra`), so asking again on an unchanged basis only
    // reworded it and re-graded those nodes every pass. (It was graded afresh each pass "as for
    // nodes"; a node's open verdict moves nobody else's basis.) A changed basis asks again.
    // (a carried verdict takes the parts of the basis it is carried on: a record for the next pass)
    if (key !== undefined && (key === basis || key === read.get(x.name)!.legacyShown || (inp.priorComplete === true && transitionBases.get(x.name)!.includes(key))) && pv && pv.basis === key && !stale.has(x.name) && !tagWhy.has(x.name)) carried.push({ ...pv, basis, basis_parts: read.get(x.name)!.parts, graded: "carried" });
    else toGrade.push(x.name);
  }
  const regradeWhy = toGrade.length > 0 ? symbolRegradeLine(toGrade, (name) => read.get(name)!.parts, (name) => priorBy.get(name)) : undefined;
  if (regradeWhy) inp.log(`symbol delta: ${regradeWhy}`);
  const plan = groupSymbolShards(table, toGrade);
  const effort = inp.effort ?? DEFAULT_REFEREE_OPTIONS.symbol_effort;
  const metrics: SymbolMetrics = {
    effort,
    symbols: table.length,
    graded: toGrade.length,
    carried: carried.length,
    shards: plan,
    calls: [],
    shard_bytes: 0,
    set_aside: [],
    ...(regradeWhy ? { regrade_why: regradeWhy } : {}),
    wall_ms: 0,
  };
  const done = (): void => {
    metrics.wall_ms = Date.now() - t0;
  };
  inp.log(`symbol delta: ${toGrade.length} of ${table.length} symbol(s) to grade afresh, ${carried.length} carried on an unchanged basis`);
  const fresh = new Map<string, V15SymbolVerdict>();
  // ONE SYMBOL NEVER HALTS THE PASS: a symbol whose new grading still breaks the contract after the
  // retry is set aside — its verdict on file kept (or none), its cache entry dropped so the next pass
  // grades it afresh — and logged; the other symbols' gradings stand.
  const setAside = new Map<string, string>();
  const putAside = (name: string, why: string): void => {
    if (setAside.has(name)) return;
    setAside.set(name, why);
    metrics.set_aside!.push({ name, why });
    inp.log(`symbol ${name}: its new grading broke the contract twice — set aside (${priorBy.has(name) ? "its verdict on file kept" : "no verdict on file: left ungraded"}; graded afresh next pass): ${why}`);
  };
  try {
    if (toGrade.length > 0) {
      const setup = setupExcerpt(inp.px);
      const ctx: SymbolContext = {
        core: inp.core,
        setup,
        slices: full,
        corrected: new Map([...read].map(([n, r]) => [n, r.reads] as const)),
        totalSymbols: table.length,
        scope: inp.scope,
      };
      const retrySection = (v: string[], echo: string): string =>
        section(
          "CONTRACT VIOLATIONS IN YOUR PREVIOUS REPLY",
          "Your previous reply broke the output contract. Re-grade and emit a corrected JSON object; every point below must be fixed.\n\n" +
            v.map((x) => `- ${x}`).join("\n") +
            (echo ? `\n\n${echo}` : ""),
        );
      /** One call, retried once with the violations and the texts they name (`echo`); past the retry,
       * `salvage` keeps what complies (null: the pass fails). A reply that is no JSON or fails the
       * schema is a contract violation like any other (retried once; past the retry, `salvage` sees
       * no reply: every symbol of the call is set aside). */
      const call = async <T>(
        c: RefereeCall,
        parse: (raw: unknown) => T,
        check: (r: T) => string[] | Promise<string[]>,
        opts: { echo?: (r: T, v: string[]) => string; salvage?: (r: T | null) => Promise<T> } = {},
      ): Promise<T> => {
        let prompt = c.prompt;
        for (let attempt = 1; attempt <= 2; attempt += 1) {
          const tag = attempt === 1 ? c.tag : `${c.tag}_retry`;
          const t = Date.now();
          let recorded = false;
          const record = (): void => {
            if (recorded) return;
            recorded = true;
            metrics.calls.push({ tag, kind: c.kind, bytes: bytesOf(prompt), ms: Date.now() - t, nodes: c.nodes.length });
            metrics.shard_bytes += bytesOf(prompt);
          };
          let r: T | null = null;
          let v: string[];
          try {
            const raw = await inp.ask({ ...c, tag, prompt, effort });
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
          inp.log(`symbol referee ${tag}: contract violations${attempt === 1 ? ", retrying once" : " survived the retry"}: ${v.join(" ")}`);
          if (attempt === 2) {
            if (opts.salvage) return opts.salvage(r);
            throw new SymbolContractFailure(`symbol referee ${c.tag} broke the output contract twice: ${v.join(" ")}`);
          }
          prompt = `${c.prompt}\n\n${retrySection(v, r ? (opts.echo?.(r, v) ?? "") : "")}`;
        }
        throw new Error("unreachable");
      };
      /** The verdicts on file of `names` graded afresh because their texts do not compile: the
       * compiler's lines, so the call writes them so they compile. */
      const staleSection = (names: readonly string[]): string => {
        const why = names.flatMap((n) => staleWhy.get(n) ?? []);
        const tags = names.flatMap((n) => tagWhy.get(n) ?? []);
        return (
          (why.length > 0
            ? `\n\n${section("TEXTS ON FILE THAT DO NOT COMPILE (write these afresh so they compile)", "Earlier readings or fixes of symbols you grade do not compile as LaTeX against the paper's preamble (the compiler's line is given). Every text you write this time must compile.\n\n" + why.map((x) => `- ${x}`).join("\n"))}`
            : "") +
          (tags.length > 0
            ? `\n\n${section("CLAUSES ON FILE TAGGED WITH A RESULT THAT IS GONE (re-tag or drop each)", "A scoped clause on file names a result that is no longer one using the symbol (a repair replaced or re-stated it). Such a grade cannot be kept whole (`keep: true` is refused). Say where each clause below goes: list it by exactly its results with `drop` and the reason, and — if it still holds somewhere — write it again as a new clause tagged with the results it now holds in (ids from THE TEXT EACH READING DESCRIBES). A clause below that your reply does not list keeps its results that are still there; one with none left is refused. Every other part can be kept by a null text.\n\n" + tags.map((x) => `- ${x}`).join("\n"))}`
            : "")
        );
      };
      /** What each reading of `names` describes (user finding 2026-09-26): for every result a symbol
       * is used in, the printed statement or a confirmed repair's corrected statement; the results with
       * a pending suggestion, to be described as printed. Each symbol's line is in its basis (`readsOf`). */
      const describesSection = (names: readonly string[]): string => {
        const pend = pending.filter((x) => names.some((n) => usersOf(n).has(x.node)));
        return `\n\n${section(
          "THE TEXT EACH READING DESCRIBES",
          "For every result each symbol is used in — its statement or proof names it, or a hypothesis or definition it is stated under does — with its id in brackets (what a scoped clause is tagged with): the text its reading describes. A confirmed correction that changes the probability model or a symbol's meaning in some results is a scoped clause tagged with those results.\n\n" +
            names.map((n) => read.get(n)?.describes ?? `- ${n}: no result uses it`).join("\n") +
            (pend.length > 0 ? `\n\nResults with a pending suggestion — describe them as printed, never with a hypothesis only the suggestion adds: ${pend.map((x) => nameOf(x.node)).join(", ")}.` : ""),
        )}`;
      };
      /** The grades on file of `names` (not stale): a grade that still holds is kept word for word
       * (`keep`), so a symbol re-graded because a result using it changed rewords nothing — its
       * reading is what the statement verdicts' bases read. */
      // Offered only for an entry graded as it stands (a changed entry drops its old fix, `source`)
      // and only for a settled grade: an `unresolvable` verdict whose basis moved is graded afresh,
      // never offered for keeping (on an unchanged basis it is carried, above).
      const tableBy = new Map(table.map((x) => [x.name, x] as const));
      const onFile = (n: string): V15SymbolVerdict | null => {
        const pv = priorBy.get(n);
        const x = tableBy.get(n);
        return pv && x && !stale.has(n) && pv.ambiguity !== "unresolvable" && pv.source === symbolSourceHash(x) ? pv : null;
      };
      const onFileSection = (names: readonly string[]): string => {
        const on = names.flatMap((n) => {
          const pv = onFile(n);
          return pv ? [{ n, pv }] : [];
        });
        if (on.length === 0) return "";
        const lines = on.map(({ n, pv }) =>
          [
            `- ${n}: meaning ${pv.meaning}${pv.fix ? `; fix: type ${pv.fix.type ?? "(unchanged)"}, space ${pv.fix.space ?? "(unchanged)"}, def ${pv.fix.def ?? "(unchanged)"}` : ""}; ambiguity ${pv.ambiguity}`,
            ...(pv.reading ? [`  reading (general part): ${pv.reading.reading}`, ...(pv.reading.scoped ?? []).map((c) => `  scoped [${c.results.join(", ")}]: ${c.text}`), `  evidence: ${pv.reading.evidence}`] : []),
            ...(pv.redefined_at ? [`  redefined at: ${pv.redefined_at}`] : []),
          ].join("\n"),
        );
        return `\n\n${section(
          "GRADES ON FILE (the symbols below were graded before; a text they are read from changed since)",
          "If a grade below still holds for the texts shown, answer `keep: true`: it is kept word for word. Answer `keep: false` and grade afresh only when a text shown makes it wrong or incomplete — then write only the part that changed: a null general part keeps the one on file, and every scoped clause on file stays as it is unless your reply lists it (by exactly its results) with a new text or with `drop`.\n\n" + lines.join("\n"),
        )}`;
      };
      const keepWhy = new WeakMap<V15SymbolVerdict, string[]>();
      /** A `keep` verdict takes its texts from the grade on file, any other the pieces of its
       * reading it keeps (`keptReading`) — before the contract is checked. */
      const kept = (v: z.infer<typeof SymbolVerdictSchema>): V15SymbolVerdict => {
        const pv = onFile(v.name);
        const { keep, reading, ...rest } = v;
        const problems: string[] = [];
        const out: V15SymbolVerdict = keep && pv
          ? { ...rest, meaning: pv.meaning, fix: pv.fix, ambiguity: pv.ambiguity, reading: pv.reading, redefined_at: pv.redefined_at, detail: pv.detail }
          : {
              ...rest,
              reading: reading
                ? keptReading(reading, pv?.reading ?? null, {
                    live: (id) => usersOf(v.name).has(id),
                    dropped: (c, why) => inp.log(`symbol ${v.name}: the scoped clause [${c.results.join(", ")}] on file is dropped — ${why}`),
                    problem: (why) => problems.push(`symbol "${v.name}": ${why}`),
                  })
                : null,
            };
        if (problems.length > 0) keepWhy.set(out, problems);
        return out;
      };
      /** The contract of a reply, with what merging it onto the grade on file found (`keptReading` `problem`). */
      const violations = async (vs: readonly V15SymbolVerdict[], owes: ReadonlySet<string>): Promise<string[]> => [...symbolContract(vs, owes, known, usersOf), ...vs.flatMap((v) => keepWhy.get(v) ?? []), ...(await symbolTexViolations(vs, inp.tex))];
      /** One symbol call over `names`; grades outside it are dropped (logged). */
      const grade = async (tag: string, names: string[]): Promise<V15SymbolVerdict[]> => {
        const own = new Set(names);
        const reply = await call(
          { tag, kind: "symbol_shard", prompt: `${buildSymbolPrompt(ctx, inp.briefs.symbols, names)}${describesSection(names)}${onFileSection(names)}${staleSection(names)}`, schema: SYMBOL_REPLY, nodes: names },
          (raw) => {
            const r = SymbolReplySchema.parse(raw);
            const extra = r.symbols.filter((v) => known.has(v.name) && !own.has(v.name)).map((v) => v.name);
            if (extra.length > 0) inp.log(`symbol referee ${tag} also graded ${extra.length} symbol(s) outside it; ignored: ${extra.join(", ")}`);
            return r.symbols.filter((v) => !extra.includes(v.name)).map(kept);
          },
          (vs) => violations(vs, own),
          {
            echo: (vs, v) => symbolRetryEcho(vs, v),
            // Past the retry: each verdict checked on its own; a noncompliant, repeated or missing one
            // set aside (a reply that did not parse: every symbol of the call).
            salvage: async (vs) => {
              if (vs === null) {
                for (const n of own) putAside(n, `symbol referee ${tag}: its reply did not parse twice.`);
                return [];
              }
              const count = new Map<string, number>();
              for (const x of vs) count.set(x.name, (count.get(x.name) ?? 0) + 1);
              const bad = new Map<string, string>();
              for (const x of vs) {
                const p = await violations([x], new Set([x.name]));
                if (p.length > 0) bad.set(x.name, p.join(" "));
                else if (count.get(x.name)! > 1) bad.set(x.name, `symbol "${x.name}" is graded more than once.`);
              }
              for (const n of own) if (!count.has(n)) bad.set(n, `symbol "${n}" carries no verdict.`);
              for (const [n, why] of bad) if (own.has(n)) putAside(n, why);
              return vs.filter((x) => !bad.has(x.name));
            },
          },
        );
        return reply;
      };
      const jobs = plan.map((names, i) => ({ tag: `${i + 1}`, names }));
      for (const j of jobs) inp.log(`symbol shard ${j.tag}: ${j.names.join(", ")}`);
      await mapLimit(jobs, Math.max(1, inp.concurrency ?? SHARD_CONCURRENCY), async (j) => {
        for (const v of await grade(`symbols_${j.tag}`, j.names)) fresh.set(v.name, { ...v, shards: [j.tag] });
      });
    }
  } catch (err) {
    done();
    if (err instanceof SymbolContractFailure) return { ok: false, message: err.message, metrics };
    throw err;
  }
  done();
  const carriedBy = new Map(carried.map((v) => [v.name, v] as const));
  const confirmed: Record<string, string> = {};
  /** The parent of each split-off block a clause is tagged with: who its successors are, once a
   * repair re-keys it (`tagWhy`). */
  const parentOf = new Map(withPending.statements.flatMap((st) => (st.split_from ? [[st.id, st.split_from] as const] : [])));
  const splitTags = (v: V15SymbolVerdict): Pick<V15SymbolVerdict, "split_tags"> => {
    const tags = (v.reading?.scoped ?? []).flatMap((c) => c.results).flatMap((id) => (parentOf.has(id) ? [[id, parentOf.get(id)!] as const] : []));
    return tags.length > 0 ? { split_tags: Object.fromEntries(tags) } : {};
  };
  const symbols = table.flatMap((x): V15SymbolVerdict[] => {
    // Set aside: the verdict on file, as it was; no cache entry, so the next pass grades it afresh.
    if (setAside.has(x.name)) {
      const pv = priorBy.get(x.name);
      return pv ? [{ ...pv, graded: "carried" as const }] : [];
    }
    const c = carriedBy.get(x.name);
    if (c) return [((confirmed[x.name] = c.basis!), c)];
    const v = fresh.get(x.name)!;
    // Keyed on what the NEW reading is about: a result it names for the first time is read whole from
    // here on (its referee was pointed to that result's text), so the next pass finds the same basis.
    const keyed = readsOf(x, v.reading);
    const basis = (confirmed[x.name] = keyed.basis);
    const intro = full.get(x.name)?.intro ?? null;
    const at = intro ? inp.lineMap?.lineMap[intro.line - 1] : undefined;
    return [
      {
        ...v,
        ...splitTags(v),
        basis,
        basis_parts: keyed.parts,
        source: symbolSourceHash(x),
        graded: "fresh" as const,
        introduced_at: intro ? { flat_line: intro.line, file: at?.file ?? null, line: at?.line ?? null } : null,
      },
    ];
  });
  return { ok: true, symbols, confirmed, metrics };
}

/** `symbol referee: …` — what the symbol pass graded and cost, and at which codex effort. */
export function symbolLogLine(m: SymbolMetrics): string {
  return `symbol referee: ${symbolLogBody(m)}; effort ${m.effort}`;
}

/** A synthetic symbol referee for a dry run: every symbol graded `ok`. No model is called. */
export function syntheticSymbolAsk(): (c: RefereeCall) => Promise<unknown> {
  const ok = (name: string) => ({ name, meaning: "ok", fix: null, ambiguity: "ok", reading: null, redefined_at: null, detail: "dry run: synthetic grade, no referee was called" });
  return async (c) => ({ summary: "dry run", symbols: c.nodes.map(ok) });
}
