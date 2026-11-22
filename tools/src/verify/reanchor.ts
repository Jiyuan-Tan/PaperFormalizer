/**
 * REANCHOR — a revised paper read with the transcription of the version before it (2026-11-10).
 *
 * The reference core (`ref_core.ts`) names WHERE each node's text is, never the text: an environment
 * id (the `\label`, else `<kind>-<ordinal>`), a run of its numbered sentences, two verbatim anchor
 * phrases, a slice of the running text. Most of that survives an author's revision — a re-worded
 * proof, a sentence added, a section moved — so V1 re-points the reference core at the revised
 * source instead of transcribing it again: the node ids stay, and with them everything keyed on them
 * downstream (the V1.5 verdicts on an unchanged basis, the repairs, the owner's rulings, the plan,
 * the F-stage review ledger, the Lean).
 *
 *   - Environments are matched by `\label`, then (an unlabeled one, whose ordinal id moves when an
 *     environment of its kind is added before it) by kind and text.
 *   - A run of sentences in an environment whose text changed is re-numbered on the sentences left
 *     unchanged around it; when the run itself was rewritten, it becomes an anchor slice cut by its
 *     old first and last words, which either still delimit it or fail to cut — a violation for the
 *     V1 agent, never a silently different passage.
 *   - An inline cited leaf follows its passage into the revised proof's units, or is dropped (the
 *     lint then lists the citation for the agent).
 *
 * What does not re-point is left to V1's own revise path: the materialized core goes through the
 * gate and the lint, and their violations reach the agent, with one line per node not located
 * (`lostNodeViolations`). However much does not re-point, what does is kept (owner, 2026-11-21:
 * reuse whenever possible; the 50% cut-off that read a revision afresh is gone).
 */
import type { Core } from "../core/schema.js";
import { materializeRefCore, type RefCore, type SourceRef } from "./ref_core.js";
import { labelPassage, refsIn, setupExcerpt, type PaperIndex } from "./referee_slices.js";
import { sentenceSpans } from "./transcription_lint.js";
import type { EnvsJson, TexEnv } from "./types.js";
import { regionUnits } from "./units.js";

/** The least text similarity (`dice`) at which an unlabeled environment is the same one revised. */
export const ENV_MATCH_MIN = 0.6;
/** Words of the old passage an anchor slice is cut by, at each end. */
const ANCHOR_WORDS = 6;

/** The version a revision is read against: its environments and its flattened text. */
export interface ReadPaper {
  envs: Pick<EnvsJson, "envs">;
  flat: string;
}

export interface ReanchorResult {
  /** The reference core re-pointed at the revised paper (node ids unchanged). */
  refs: RefCore;
  /** Old environment id → new, for every environment the reference core uses that moved id. */
  renamed: Record<string, string>;
  /** Node ids by what the revision did to their text: identical, changed, or no longer found. */
  same: string[];
  changed: string[];
  broken: string[];
  /** `broken` over every node of the old transcription. */
  brokenShare: number;
  /** One line per re-pointing decision worth the log. */
  notes: string[];
}

const norm = (s: string): string => s.replace(/\s+/g, " ").trim();
const words = (s: string): string[] => norm(s).split(" ").filter((w) => w.length > 0);

/** Multiset Dice coefficient of the two texts' words: 1 identical, 0 nothing shared. Pure. */
export function dice(a: string, b: string): number {
  const wa = words(a);
  const wb = words(b);
  if (wa.length + wb.length === 0) return 1;
  const count = new Map<string, number>();
  for (const w of wa) count.set(w, (count.get(w) ?? 0) + 1);
  let shared = 0;
  for (const w of wb) {
    const c = count.get(w) ?? 0;
    if (c > 0) (shared += 1), count.set(w, c - 1);
  }
  return (2 * shared) / (wa.length + wb.length);
}

/**
 * Old environment id → new, for the environments `needed`. A labeled environment keeps its label
 * (its id is the label); every other one goes to the unclaimed environment of the same kind whose
 * STATEMENT is closest, at least `ENV_MATCH_MIN` alike (a proof reworded leaves the result the same
 * one; the proofs only break a tie) — best pairs first, so an unchanged environment is never taken by
 * a neighbour. An environment with no such match is absent from the map. Pure.
 */
export function matchEnvs(before: readonly TexEnv[], after: readonly TexEnv[], needed: ReadonlySet<string>): Map<string, string> {
  const out = new Map<string, string>();
  const claimed = new Set<string>();
  const byLabel = new Map(after.filter((e) => e.label).map((e) => [e.label!, e] as const));
  const rest: TexEnv[] = [];
  for (const e of before) {
    if (!needed.has(e.id)) continue;
    const hit = e.label ? byLabel.get(e.label) : undefined;
    if (hit && !claimed.has(hit.id)) {
      out.set(e.id, hit.id);
      claimed.add(hit.id);
    } else rest.push(e);
  }
  const pairs: Array<{ from: string; to: string; score: number; proof: number }> = [];
  for (const e of rest) {
    for (const f of after) {
      if (f.kind !== e.kind || claimed.has(f.id)) continue;
      const score = norm(e.body) === norm(f.body) ? 1 : dice(e.body, f.body);
      if (score >= ENV_MATCH_MIN) pairs.push({ from: e.id, to: f.id, score, proof: dice(e.proof ?? "", f.proof ?? "") });
    }
  }
  pairs.sort((x, y) => y.score - x.score || y.proof - x.proof || x.from.localeCompare(y.from));
  for (const p of pairs) {
    if (out.has(p.from) || claimed.has(p.to)) continue;
    out.set(p.from, p.to);
    claimed.add(p.to);
  }
  return out;
}

/** The sentences of a region, whitespace-normalized. */
const sentencesOf = (text: string): string[] => sentenceSpans(text).map((sp) => norm(text.slice(sp.start, sp.end)));

/** Longest-common-subsequence pairs (old index → new index) of two sentence lists. Pure. */
function lcsPairs(a: readonly string[], b: readonly string[]): Map<number, number> {
  const n = a.length;
  const m = b.length;
  const dp: number[][] = Array.from({ length: n + 1 }, () => new Array<number>(m + 1).fill(0));
  for (let i = n - 1; i >= 0; i -= 1) for (let j = m - 1; j >= 0; j -= 1) dp[i]![j] = a[i] === b[j] ? dp[i + 1]![j + 1]! + 1 : Math.max(dp[i + 1]![j]!, dp[i]![j + 1]!);
  const out = new Map<number, number>();
  let i = 0;
  let j = 0;
  while (i < n && j < m) {
    if (a[i] === b[j]) (out.set(i, j), (i += 1), (j += 1));
    else if (dp[i + 1]![j]! >= dp[i]![j + 1]!) i += 1;
    else j += 1;
  }
  return out;
}

/**
 * Sentences [a, b] (1-based) of `before`, as a run of `after`'s sentences: while both ends are
 * sentences the revision left as they were, the run between them. Null when an end was rewritten.
 * Pure.
 */
export function renumberSentences(before: string, after: string, run: readonly [number, number]): [number, number] | null {
  const pairs = lcsPairs(sentencesOf(before), sentencesOf(after));
  const a = pairs.get(run[0] - 1);
  const b = pairs.get(run[1] - 1);
  return a !== undefined && b !== undefined && a <= b ? [a + 1, b + 1] : null;
}

/** An anchor slice cut by the first and the last words of `text` (a one-phrase slice when short). */
function sliceOf(text: string): { from: string; to: string } {
  const w = words(text);
  if (w.length <= ANCHOR_WORDS) return { from: w.join(" "), to: w.join(" ") };
  return { from: w.slice(0, ANCHOR_WORDS).join(" "), to: w.slice(-ANCHOR_WORDS).join(" ") };
}

/** The node ids of a materialized core. */
function nodeIds(core: Core): string[] {
  return [...core.assumptions, ...core.definitions, ...core.statements].map((n) => n.id);
}

/** The text fields of a node, whitespace-normalized (statement, proof, condition, construction); null
 * when the core has no such node. Pure. */
export function nodeFields(core: Core, id: string): Record<(typeof TEXT_FIELDS)[number], string> | null {
  const n = [...core.assumptions, ...core.definitions, ...core.statements].find((x) => x.id === id) as Record<string, unknown> | undefined;
  if (!n) return null;
  return Object.fromEntries(TEXT_FIELDS.map((k) => [k, typeof n[k] === "string" ? norm(n[k] as string) : ""])) as Record<(typeof TEXT_FIELDS)[number], string>;
}
const TEXT_FIELDS = ["statement", "proof_tex", "condition", "construction"] as const;

/** The nodes a setup-change check reads (`prompts/V1/setup_change.txt`): one line each, `id: text`. Pure. */
export function setupChangeNodes(core: Core, ids?: ReadonlySet<string>): string {
  return [...core.assumptions, ...core.definitions, ...core.statements].filter((n) => !ids || ids.has(n.id)).map((n) => {
    const f = nodeFields(core, n.id)!;
    const text = f.statement || f.condition || f.construction;
    return `${n.id}: ${text.length > 400 ? `${text.slice(0, 400)}…` : text}`;
  }).join("\n");
}

/** The macros whose definition a revision changed (added, removed or redefined), by name, from the
 * preamble of each flat text (`\\newcommand`, `\\renewcommand`, `\\providecommand`, `\\def` and its
 * kin, `\\let`, `\\DeclareMathOperator`, `\\DeclarePairedDelimiter`, the `…DocumentCommand`s). Pure. */
export function changedMacros(before: PaperIndex, after: PaperIndex): string[] {
  // each definition runs to the next one (or the document's start): a body over several lines, or a
  // second definition on its line, is its own (text between definitions is read with the one before:
  // a change there re-grades more, never less)
  const DEF = /\\(?:(?:re)?newcommand|providecommand|DeclareMathOperator|DeclarePairedDelimiter|(?:New|Renew|Provide|Declare)DocumentCommand)\*?\s*\{?\s*\\([A-Za-z@]+)|\\(?:[gex]?def|let)\s*\\([A-Za-z@]+)/g;
  const defs = (px: PaperIndex): Map<string, string> => {
    const end = px.lines.findIndex((l) => /\\begin\{document\}/.test(l));
    const pre = px.lines.slice(0, end === -1 ? 0 : end).map((l) => l.replace(/(^|[^\\])%.*$/, "$1")).join("\n");
    const hits = [...pre.matchAll(DEF)];
    const out = new Map<string, string>();
    hits.forEach((m, k) => {
      const name = m[1] ?? m[2]!;
      const text = norm(pre.slice(m.index!, k + 1 < hits.length ? hits[k + 1]!.index! : pre.length));
      out.set(name, `${out.get(name) ?? ""}\n${text}`);
    });
    return out;
  };
  const [a, b] = [defs(before), defs(after)];
  return [...new Set([...a.keys(), ...b.keys()])].filter((n) => a.get(n) !== b.get(n)).sort();
}

/** The nodes of `core` whose text (statement, proof, condition, construction) uses one of `macros`. Pure. */
export function nodesUsingMacros(core: Core, macros: readonly string[]): string[] {
  if (macros.length === 0) return [];
  const re = new RegExp(`\\\\(?:${macros.map((m) => m.replace(/[@]/g, "\\@")).join("|")})(?![A-Za-z@])`);
  return [...core.assumptions, ...core.definitions, ...core.statements].filter((n) => {
    const f = nodeFields(core, n.id)!;
    return re.test(`${f.statement}\n${f.proof_tex}\n${f.condition}\n${f.construction}`);
  }).map((n) => n.id);
}

/** Whether a setup excerpt a referee reads was cut short (`setupExcerpt`): a change in what it leaves
 * out would be invisible to a check that reads it. Pure. */
export function setupExcerptCut(px: PaperIndex): boolean {
  const e = setupExcerpt(px);
  return /\[… \d+ characters elided|\[… more macro definitions/.test(`${e.macros}\n${e.setup}`);
}

/** The answer of a setup-change check, read strictly: `all`, or the nodes it names (each an id of
 * the core); null when it is no such answer — then every result is checked again, as without it. Pure. */
export function readSetupChangeAnswer(reply: unknown, ids: ReadonlySet<string>): { all: true } | { all: false; affected: string[] } | null {
  const r = reply as { all?: unknown; affected?: unknown } | null;
  if (!r || typeof r.all !== "boolean") return null;
  if (r.all) return { all: true };
  if (!Array.isArray(r.affected)) return null;
  const affected = (r.affected as Array<{ id?: unknown }>).map((a) => a?.id);
  if (affected.some((id) => typeof id !== "string" || !ids.has(id))) return null;
  return { all: false, affected: [...new Set(affected as string[])] };
}

/** One line for V1's agent per node of the version before that is not located in the revision
 * (`broken`): what it read, and what to do — re-point it, keeping its id, or remove it. Pure. */
export function lostNodeViolations(before: Core, broken: readonly string[]): string[] {
  return broken.map((id) => {
    const f = nodeFields(before, id);
    const text = f ? f.statement || f.condition || f.construction : "";
    const excerpt = text.length > 240 ? `${text.slice(0, 240)}…` : text;
    return `(reanchor) ${id} was not located in the revised paper${excerpt ? `; it read: "${excerpt}"` : ""}. In discovery/core_refs.json, point it at its text in the revised paper, keeping the id ${id}; if the revision removed it, remove the node and say so in your reply.`;
  });
}
const nodeText = (core: Core, id: string): string | null => ((f) => (f ? TEXT_FIELDS.map((k) => f[k]).join("\n§\n") : null))(nodeFields(core, id));

/**
 * Re-point `ref` (written against `before`) at the revised paper `after`. Pure.
 */
export function reanchorRefs(ref: RefCore, before: ReadPaper, after: ReadPaper): ReanchorResult {
  const notes: string[] = [];
  const oldById = new Map(before.envs.envs.map((e) => [e.id, e] as const));
  const newById = new Map(after.envs.envs.map((e) => [e.id, e] as const));
  const needed = new Set<string>([
    ...ref.statements.map((s) => s.env),
    ...[...ref.assumptions, ...ref.definitions].flatMap((n) => ("env" in n.source ? [n.source.env] : [])),
    ...(ref.proof_citations ?? []).flatMap((c) => (c.sites ?? [c.site!]).map((s) => s.split(" | ")[0]!)),
    ...(ref.dismissed_citations ?? []).map((d) => d.site.split(" | ")[0]!),
  ]);
  const map = matchEnvs(before.envs.envs, after.envs.envs, needed);
  const renamed: Record<string, string> = {};
  for (const [a, b] of map) if (a !== b) renamed[a] = b;
  for (const [a, b] of Object.entries(renamed)) notes.push(`reanchor: environment ${a} is ${b} in the revised paper`);
  for (const id of needed) if (oldById.has(id) && !map.has(id)) notes.push(`reanchor: environment ${id} has no counterpart in the revised paper`);
  /** An environment id moved to the revised paper. One with no counterpart takes an id no
   *  environment has — never its old one, which an unlabeled environment's ordinal gives another
   *  environment of the revision — so materializing the node reports it to V1's agent. */
  const to = (id: string): string => map.get(id) ?? (oldById.has(id) ? `${id} (no counterpart in the revised paper)` : id);
  const siteTo = (site: string): string => ((parts) => [to(parts[0]!), ...parts.slice(1)].join(" | "))(site.split(" | "));

  const source = (id: string, src: SourceRef): SourceRef => {
    if ("prose" in src) return src;
    const was = oldById.get(src.env);
    const now = newById.get(to(src.env));
    const moved = { ...src, env: to(src.env) };
    if (!src.sentences || !was || !now) return moved;
    const region = (e: TexEnv): string | null => (src.region === "proof" ? e.proof : e.body);
    const a = region(was);
    const b = region(now);
    if (a === null || b === null || norm(a) === norm(b)) return moved;
    const run = renumberSentences(a, b, src.sentences);
    if (run) return { ...moved, sentences: run };
    // The run itself was rewritten: cut it by its old ends, or fail to cut.
    const spans = sentenceSpans(a);
    const [first, last] = src.sentences;
    if (last > spans.length) return moved;
    const { sentences: _s, ...rest } = moved;
    notes.push(`reanchor: ${id}: sentences [${first}, ${last}] of ${src.env} ${src.region} were rewritten — re-pointed by their first and last words`);
    return { ...rest, slice: sliceOf(a.slice(spans[first - 1]!.start, spans[last - 1]!.end)) };
  };

  const proofCitations = (ref.proof_citations ?? []).flatMap((c) => {
    const host = (c.sites ?? [c.site!])[0]!.split(" | ")[0]!;
    const was = oldById.get(host);
    const now = newById.get(to(host));
    const site = c.site !== undefined ? { site: siteTo(c.site) } : { sites: c.sites!.map(siteTo) };
    if (!was?.proof || !now?.proof) return [{ ...c, ...site }];
    const oldUnits = regionUnits(was.proof);
    const index = (u: string): number => oldUnits.findIndex((x) => `${host}/proof/${x.p}/${x.u}` === u);
    const [i, j] = c.units.map(index);
    if (i! < 0 || j! < 0) return [{ ...c, ...site }];
    const passage = norm(was.proof.slice(oldUnits[i!]!.start, oldUnits[j!]!.end));
    const newUnits = regionUnits(now.proof);
    for (let s = 0; s < newUnits.length; s += 1) {
      for (let e = s; e < newUnits.length; e += 1) {
        const text = norm(now.proof.slice(newUnits[s]!.start, newUnits[e]!.end));
        if (text.length > passage.length) break;
        if (text === passage) {
          const id = (x: { p: number; u: number }): string => `${now.id}/proof/${x.p}/${x.u}`;
          return [{ ...c, ...site, units: [id(newUnits[s]!), id(newUnits[e]!)] as [string, string] }];
        }
      }
    }
    notes.push(`reanchor: ${c.id}: the passage it was cut from is no longer in the proof of ${now.id} — dropped (the citation is listed for V1)`);
    return [];
  });

  const refs: RefCore = {
    ...ref,
    assumptions: ref.assumptions.map((a) => ({ ...a, source: source(a.id, a.source) })),
    definitions: ref.definitions.map((d) => ({ ...d, source: source(d.id, d.source) })),
    statements: ref.statements.map((s) => ({ ...s, env: to(s.env) })),
    ...(ref.proof_citations !== undefined ? { proof_citations: proofCitations } : {}),
    ...(ref.dismissed_citations !== undefined ? { dismissed_citations: ref.dismissed_citations.map((d) => ({ ...d, site: siteTo(d.site) })) } : {}),
  };

  const was = materializeRefCore(ref, before.envs as EnvsJson, before.flat).core;
  const now = materializeRefCore(refs, after.envs as EnvsJson, after.flat).core;
  const same: string[] = [];
  const changed: string[] = [];
  const broken: string[] = [];
  for (const id of nodeIds(was)) {
    const b = nodeText(now, id);
    if (b === null) broken.push(id);
    else if (b === nodeText(was, id)) same.push(id);
    else changed.push(id);
  }
  // (An anchor that no longer cuts, or no longer cuts one place, drops its node from the
  // materialized core: broken, until V1 re-points it.)
  const total = same.length + changed.length + broken.length;
  return { refs, renamed, same, changed, broken, brokenShare: total === 0 ? 0 : broken.length / total, notes };
}

/**
 * A flat line range (1-based, inclusive) of `before`, where the same lines now are in `after`: the
 * one place the block of lines occurs whole. Null when it occurs nowhere or in several places. Pure.
 */
export function relocateLines(before: readonly string[], after: readonly string[], range: readonly [number, number]): [number, number] | null {
  const block = before.slice(range[0] - 1, range[1]);
  if (block.length === 0 || range[1] > before.length) return null;
  let hit: number | null = null;
  for (let i = 0; i + block.length <= after.length; i += 1) {
    if (after[i] !== block[0]) continue;
    if (block.every((l, k) => after[i + k] === l)) {
      if (hit !== null) return null;
      hit = i;
    }
  }
  return hit === null ? null : [hit + 1, hit + block.length];
}

/**
 * The segmenter's file (`segments.ts`: flat LINE ranges of what the parser missed) re-pointed at the
 * revised flat text: every range follows its lines; an entry whose lines are not found once — or a
 * binding whose environment no longer reads as it did (`sameEnv`) — is dropped: its gap is the
 * parser's warning again, and the segmenter answers it. Pure.
 */
export function reanchorSegments<S extends { results: Array<{ lines: [number, number]; proof_lines?: [number, number] | null }>; bindings: Array<{ result: string; proof_lines: [number, number] }>; extend?: Array<{ lines: [number, number] }> }>(
  seg: S,
  before: string,
  after: string,
  /** Whether a binding's environment is still the one it named (`bindings[].result`). */
  sameEnv: (id: string) => boolean = () => true,
): { seg: S; dropped: number } {
  const a = before.split("\n");
  const b = after.split("\n");
  const at = (r: readonly [number, number]): [number, number] | null => relocateLines(a, b, r);
  let dropped = 0;
  const keep = <T>(x: T | null): x is T => (x === null ? ((dropped += 1), false) : true);
  const results = seg.results
    .map((r) => {
      const lines = at(r.lines);
      const proof = r.proof_lines ? at(r.proof_lines) : null;
      return lines && (!r.proof_lines || proof) ? { ...r, lines, ...(r.proof_lines ? { proof_lines: proof } : {}) } : null;
    })
    .filter(keep);
  const bindings = seg.bindings.map((x) => ((p) => (p && sameEnv(x.result) ? { ...x, proof_lines: p } : null))(at(x.proof_lines))).filter(keep);
  const extend = seg.extend?.map((x) => ((l) => (l ? { ...x, lines: l } : null))(at(x.lines))).filter(keep);
  return { seg: { ...seg, results, bindings, ...(extend !== undefined ? { extend } : {}) }, dropped };
}

/**
 * What a node's referee reads of the paper beyond the node's own text and the nodes it uses: the
 * passages its `\ref`s name that no node of the core carries (an equation, a remark, a section;
 * `referee_slices.ts` `referencedPassages`). Per node, the ids whose passages read otherwise in the
 * revision — a verdict on such a node is not carried, though its own record is unchanged. Pure.
 */
export function referencedContextChanged(before: { px: PaperIndex; core: Core }, after: { px: PaperIndex; core: Core }, ids: readonly string[]): string[] {
  const labels = (core: Core): Set<string> => new Set([...core.statements, ...core.assumptions, ...core.definitions].map((n) => n.tex_locator?.label).filter((l): l is string => !!l));
  const inCore = new Set([...labels(before.core), ...labels(after.core)]);
  const passage = (px: PaperIndex, label: string): string => norm(labelPassage(px, label)?.text ?? "");
  const memo = new Map<string, boolean>();
  const moved = (label: string): boolean => {
    if (!memo.has(label)) memo.set(label, passage(before.px, label) !== passage(after.px, label));
    return memo.get(label)!;
  };
  return ids.filter((id) => {
    const f = nodeFields(after.core, id);
    if (!f) return false;
    const refs = new Set([...refsIn(f.statement), ...refsIn(f.proof_tex), ...refsIn(f.condition), ...refsIn(f.construction)]);
    return [...refs].some((l) => !inCore.has(l) && moved(l));
  });
}

/**
 * Whether the revision changed the paper's SETUP as every referee reads it (`setupExcerpt`: its
 * macro definitions, the text before its first result) — whitespace aside, any change: a word of
 * prose can carry a hypothesis ("convex" → "strongly convex"). Then no verdict is carried and V1
 * re-reads the settings. Pure.
 */
export function setupChanged(before: PaperIndex, after: PaperIndex): boolean {
  const a = setupExcerpt(before);
  const b = setupExcerpt(after);
  return norm(a.macros) !== norm(b.macros) || norm(a.setup) !== norm(b.setup);
}
