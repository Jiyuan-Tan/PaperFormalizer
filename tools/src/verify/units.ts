/**
 * The paper's ADDRESSABLE UNITS (design 2026-09-25, P2: "the model emits operations on addressable units
 * of the paper, not blobs").
 *
 * `flat.tex` is parsed once into a tree — environment (its `envs.json` id: the label, or the id V1 gave an
 * unlabelled one) > region (the environment's body, or the proof V1 bound to it) > paragraph > unit — where a
 * unit is WHOLE by construction:
 *
 *  - a sentence (`sentenceSpans`: never cut inside math; a lead-in without terminal punctuation keeps the
 *    display that follows it, so "we have $$ … $$" is ONE unit, and so is a display followed by lowercase
 *    text);
 *  - a list item: `\item …` up to the next item of the same list or its `\end` (a nested list stays inside
 *    its item);
 *  - a display standing alone (`$$…$$`, `\[…\]`, `align*` / `equation*` / … — never split at its rows).
 *
 * A unit never starts or ends with a `\label{…}` and never ends with an end-of-proof mark: those stay between units
 * (the paper's own), so an insertion after the last step of a proof lands before its QED mark. Ids are
 * `<env>/<p>/<u>` for the body and `<env>/proof/<p>/<u>` for the proof (1-based paragraph and unit
 * indices); offsets are into `flat.tex` (a JS string). Paragraphs are separated by blank lines outside any
 * math or environment. The runner caches the parse in `discovery/units.json`, keyed by the cut's version
 * and the sha256 of `flat.tex` and of `envs.json`, so the ids the fixer was shown stay the ids its ops
 * resolve against.
 *
 * An ALGORITHM (an `algorithm` float or a bare `algorithmic` block — algorithmic / algpseudocode commands)
 * is cut step by step (`algorithmUnits`): paragraph `p` is the step — an input / output line, a `\STATE`
 * line, a control line (`\IF{…}`, `\ENDFOR`) — and its units are the step's own sentences, displays and
 * the items of a list nested in it; the caption, the labels and the delimiters stay between units. A
 * float `envs.json` does not list (no result refers to it) is a region all the same, under its caption's
 * label (else `algorithm-<n>`), so a definition transcribed from the running text as that float has
 * units. Markup the cutter does not know (algorithm2e, text before the first step) gets no step units
 * and a `warnings` line.
 * Pure except `loadUnits`.
 */
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import { captionLabel } from "./tex_envs.js";
import { sentenceSpans, texStructure, type TexStructure } from "./transcription_lint.js";
import { VERIFY_FILES, type EnvsJson } from "./types.js";

export type UnitKind = "sentence" | "item" | "display";
export type UnitPart = "body" | "proof";

export interface Unit {
  id: string;
  env: string;
  part: UnitPart;
  /** 1-based paragraph and unit (within the paragraph) indices. */
  p: number;
  u: number;
  kind: UnitKind;
  /** `[start, end)` in `flat.tex`. */
  start: number;
  end: number;
  /** An item's text starts after its `\item[…]` head: `[content, end)` is what an op on it replaces. */
  content: number;
  /** The list an item belongs to (`<region>/L<k>`), null for a sentence or display. */
  list: string | null;
  /** An item's list starts here (at its `\begin{…}`) and ends here (after its `\end{…}`); null for a
   * sentence or display. */
  list_start: number | null;
  list_end: number | null;
}

export interface UnitRegion {
  /** `<env>` (body) or `<env>/proof`. */
  id: string;
  env: string;
  part: UnitPart;
  start: number;
  end: number;
  /** An algorithm cut step by step: a node printed as it is the whole float (caption and delimiters
   * around the units), wherever its reference-core source takes the text from. */
  algorithm?: true;
}

/** The cut's version: a cache of an earlier one is parsed again (2: algorithms step by step). */
export const UNITS_VERSION = 2;

export interface UnitsFile {
  version?: number;
  flat_sha256: string;
  envs_sha256: string;
  regions: UnitRegion[];
  units: Unit[];
  /** Algorithms left without step units (markup the cutter does not know). */
  warnings?: string[];
}

/** `runs/<slug>/<this>`: the cached parse. */
export const UNITS_FILE = "discovery/units.json";

const LIST_ENV = /^(?:enumerate|itemize|description)$/u;
const LABEL_HEAD = /^(?:\s|\\label\s*\{[^{}]*\}|\{\})+/u;
const LABEL_TAIL = /(?:\s|\\label\s*\{[^{}]*\})+$/u;
/** An end-of-proof mark (with the spacing before it), alone or ending a unit. */
const QED_TAIL = /(?:\s|~|\\(?:hfill|hspace\*?\{[^{}]*\}|qquad|quad|,|;))*(?:\\qed(?:symbol)?|\$\s*\\(?:Box|square|blacksquare|qedsymbol)\s*\$|\\(?:Box|blacksquare))\s*$/u;

const sha = (s: string): string => createHash("sha256").update(s).digest("hex");

/** A unit of one region, in the region's own coordinates (no id yet). */
export interface RegionUnit {
  kind: UnitKind;
  start: number;
  end: number;
  content: number;
  p: number;
  u: number;
  /** Index (0-based, region order) of the list an item belongs to, or null. */
  list: number | null;
  /** The start (at its `\begin{…}`) and end (after its `\end{…}`) of that list, or null. */
  listStart: number | null;
  listEnd: number | null;
}

const envName = (text: string, r: TexStructure): string => /^\\begin\s*\{([^{}]*)\}/u.exec(text.slice(r.start, r.start + 80))?.[1]?.trim() ?? "";
const inside = (r: TexStructure, p: number): boolean => r.start + r.openLen <= p && p < r.end - r.closeLen;

/** The units of one region's TeX, in its coordinates. Pure. */
export function regionUnits(text: string): RegionUnit[] {
  const structure = texStructure(text);
  // Paragraphs: blank lines outside every math region and environment.
  const breaks: Array<[number, number]> = [];
  for (const m of text.matchAll(/\n[^\S\n]*\n\s*/gu)) {
    const at = m.index!;
    if (structure.some((r) => r.start < at && at < r.end)) continue;
    breaks.push([at, at + m[0].length]);
  }
  const paragraphs: Array<[number, number]> = [];
  let from = 0;
  for (const [a, b] of breaks) {
    paragraphs.push([from, a]);
    from = b;
  }
  paragraphs.push([from, text.length]);
  const lists = structure.filter((r) => r.kind === "env" && !r.math && LIST_ENV.test(envName(text, r)));
  const outerLists = lists.filter((l) => !lists.some((o) => o !== l && o.start < l.start && l.end <= o.end));
  const out: RegionUnit[] = [];
  let p = 0;
  for (const [ps, pe] of paragraphs) {
    const raw: Array<{ kind: UnitKind; start: number; end: number; content: number; list: number | null; listStart: number | null; listEnd: number | null }> = [];
    const here = outerLists.filter((l) => l.start >= ps && l.end <= pe);
    // Items of the outermost lists: `\item` up to the next item of the same list (or its `\end`).
    for (const l of here) {
      const inner = lists.filter((x) => x !== l && l.start < x.start && x.end <= l.end);
      const heads = [...text.slice(l.start, l.end).matchAll(/\\item\b/gu)]
        .map((m) => l.start + m.index!)
        .filter((h) => !inner.some((x) => x.start < h && h < x.end) && !structure.some((r) => r.math && inside(r, h)));
      const bodyEnd = l.end - l.closeLen;
      heads.forEach((h, k) => {
        const end = k + 1 < heads.length ? heads[k + 1]! : bodyEnd;
        const head = /^\\item\b\s*(?:\[[^\]]*\])?\s*/u.exec(text.slice(h, end))![0].length;
        raw.push({ kind: "item", start: h, end, content: h + head, list: lists.indexOf(l), listStart: l.start, listEnd: l.end });
      });
    }
    // Sentences outside those lists.
    for (const s of sentenceSpans(text.slice(ps, pe))) {
      const start = s.start + ps;
      const end = s.end + ps;
      if (here.some((l) => l.start < end && start < l.end)) continue;
      raw.push({ kind: "sentence", start, end, content: start, list: null, listStart: null, listEnd: null });
    }
    raw.sort((x, y) => x.start - y.start);
    let u = 0;
    for (const r of raw) {
      // Whole, but never a label at its head, an end-of-proof mark at its tail, or blanks at either end.
      let start = r.start;
      let content = r.content;
      if (r.kind !== "item") {
        start += LABEL_HEAD.exec(text.slice(start, r.end))?.[0].length ?? 0;
        content = start;
      } else content += LABEL_HEAD.exec(text.slice(content, r.end))?.[0].length ?? 0;
      let end = r.end;
      for (let changed = true; changed; ) {
        const before = end;
        const q = QED_TAIL.exec(text.slice(content, end)) ?? LABEL_TAIL.exec(text.slice(content, end));
        if (q) end = content + q.index;
        while (end > content && /\s/u.test(text[end - 1]!)) end -= 1;
        changed = end !== before;
      }
      if (end <= content) continue;
      const display = r.kind === "sentence" && structure.some((m) => m.math && m.start === start && (m.kind === "env" || text.startsWith("$$", m.start) || text.startsWith("\\[", m.start)) && /^[\s.,;:]*$/u.test(text.slice(m.end, end)));
      if (u === 0) p += 1;
      u += 1;
      out.push({ kind: display ? "display" : r.kind, start, end, content, p, u, list: r.list, listStart: r.listStart, listEnd: r.listEnd });
    }
  }
  return out;
}

/** An algorithm float or a bare pseudocode block, by its environment name. */
const ALGORITHM_ENV = /^algorithm(?:ic)?\*?$/u;
/** Step commands whose text is the step (the command stays, as an `\item` does): algorithmic and
 * algpseudocode, and the input / output lines papers define beside them. */
const STEP_HEAD = /^(?:STATEX?|Statex?|REQUIRE|Require|ENSURE|Ensure|INPUT|Input|OUTPUT|Output|RETURN|PRINT)$/u;
/** Control lines: each is one unit, command and condition together. */
const CONTROL_HEAD = /^(?:IF|ELSIF|ELSE|ENDIF|FOR|FORALL|ENDFOR|WHILE|ENDWHILE|REPEAT|UNTIL|LOOP|ENDLOOP|If|ElsIf|Else|EndIf|For|ForAll|EndFor|While|EndWhile|Repeat|Until|Loop|EndLoop|Function|EndFunction|Procedure|EndProcedure)$/u;
/** The step and control commands a TeX text holds, in order. */
export const algorithmCommands = (tex: string): string[] => [...tex.matchAll(/\\([A-Za-z]+)/gu)].map((m) => m[1]!).filter((n) => STEP_HEAD.test(n) || CONTROL_HEAD.test(n));
/** Is the text a control line of an algorithm (`\IF{…}`, `\ENDFOR`)? */
export const isControlLine = (tex: string): boolean => CONTROL_HEAD.test(/^\s*\\([A-Za-z]+)/u.exec(tex)?.[1] ?? "");
/** algorithm2e's own markup (its lines end with `\;`, its blocks are arguments): not cut. */
const ALGORITHM2E = /\\(?:Kw[A-Z][A-Za-z]*|SetAlgo[A-Za-z]*|SetKw[A-Za-z]*|DontPrintSemicolon|[eul]If|[ul]?ElseIf|[ul]?Else|ForEach|ForAll|[ul]For|[ul]While|Repeat|Return|BlankLine)(?![A-Za-z])|\\;\s*(?:\n|$)/u;

/** The `\caption{…}` spans of a float's body. */
function captionSpans(text: string): Array<[number, number]> {
  const out: Array<[number, number]> = [];
  for (const m of text.matchAll(/\\caption\s*(?:\[[^\]]*\])?\s*\{/gu)) {
    let depth = 0;
    for (let i = m.index! + m[0].length - 1; i < text.length; i += 1) {
      if (text[i] === "\\") i += 1;
      else if (text[i] === "{") depth += 1;
      else if (text[i] === "}" && --depth === 0) {
        out.push([m.index!, i + 1]);
        break;
      }
    }
  }
  return out;
}

/**
 * The units of an algorithm's TeX (a float's body, or with `bare` the body of an `algorithmic` block), in
 * its coordinates: per step, the units of its text (`regionUnits`), the first one starting at the step's
 * command and its content after it; a control line whole. A float with no `algorithmic` block that is no
 * algorithm2e body is a procedure in prose: its units as any text's, the caption left out. Null (with
 * `why`) for markup this does not cut. A step command is read only outside math, environments and brace
 * groups, so no unit is cut inside one. Pure.
 */
export function algorithmUnits(text: string, bare = false): { units: RegionUnit[] } | { units: null; why: string } {
  const structure = texStructure(text);
  const blocks = bare
    ? [{ start: 0, end: text.length }]
    : structure.filter((r) => r.kind === "env" && envName(text, r) === "algorithmic" && r.closeLen > 0).map((r) => ({ start: r.start + r.openLen, end: r.end - r.closeLen }));
  if (blocks.length === 0) {
    if (ALGORITHM2E.test(text)) return { units: null, why: "algorithm2e markup" };
    // The text around the caption, piece by piece: the caption takes no index and ends no sentence.
    const kept: RegionUnit[] = [];
    let from = 0;
    let p = 0;
    let lists = 0;
    for (const [a, b] of [...captionSpans(text), [text.length, text.length] as [number, number]]) {
      const piece = regionUnits(text.slice(from, a));
      for (const u of piece) kept.push({ ...u, start: from + u.start, end: from + u.end, content: from + u.content, p: p + u.p, list: u.list === null ? null : lists + u.list, listStart: u.listStart === null ? null : from + u.listStart, listEnd: u.listEnd === null ? null : from + u.listEnd });
      p += Math.max(0, ...piece.map((u) => u.p));
      lists += Math.max(0, ...piece.map((u) => (u.list ?? -1) + 1));
      from = b;
    }
    return { units: kept };
  }
  const out: RegionUnit[] = [];
  let p = 0;
  let lists = 0;
  for (const b of blocks) {
    const from = b.start + (/^\s*\[[^\]]*\]/u.exec(text.slice(b.start, b.end))?.[0].length ?? 0);
    // Step and control commands at the block's own level.
    const inner = structure.filter((r) => b.start <= r.start && r.end <= b.end);
    const heads: Array<{ at: number; end: number; control: boolean }> = [];
    let depth = 0;
    for (let i = from; i < b.end; i += 1) {
      const c = text[i]!;
      if (c === "%") {
        const nl = text.indexOf("\n", i);
        i = nl < 0 || nl > b.end ? b.end : nl;
      } else if (c === "{") depth += 1;
      else if (c === "}") depth = Math.max(0, depth - 1);
      else if (c === "\\") {
        const word = /^\\([A-Za-z]+)/u.exec(text.slice(i, i + 40));
        if (!word) {
          i += 1;
          continue;
        }
        const name = word[1]!;
        if (depth === 0 && (STEP_HEAD.test(name) || CONTROL_HEAD.test(name)) && !inner.some((r) => r.start <= i && i < r.end)) heads.push({ at: i, end: i + word[0].length, control: CONTROL_HEAD.test(name) });
        i += word[0].length - 1;
      }
    }
    if (heads.length === 0 || text.slice(from, heads[0]!.at).trim() !== "") return { units: null, why: heads.length === 0 ? "no step command in its algorithmic block" : "text before the first step command" };
    heads.forEach((h, k) => {
      let end = k + 1 < heads.length ? heads[k + 1]!.at : b.end;
      while (end > h.end && /\s/u.test(text[end - 1]!)) end -= 1;
      if (h.control) {
        p += 1;
        out.push({ kind: "sentence", start: h.at, end, content: h.at, p, u: 1, list: null, listStart: null, listEnd: null });
        return;
      }
      const at = h.end + (/^\s*/u.exec(text.slice(h.end, end))?.[0].length ?? 0);
      const sub = regionUnits(text.slice(at, end));
      if (sub.length === 0) return;
      p += 1;
      const first = lists;
      sub.forEach((s, i) => {
        if (s.list !== null) lists = Math.max(lists, first + s.list + 1);
        out.push({
          ...s,
          start: i === 0 && s.kind !== "item" ? h.at : at + s.start,
          end: at + s.end,
          content: at + s.content,
          p,
          u: i + 1,
          list: s.list === null ? null : first + s.list,
          listStart: s.listStart === null ? null : at + s.listStart,
          listEnd: s.listEnd === null ? null : at + s.listEnd,
        });
      });
    });
  }
  return { units: out };
}

/** The algorithm floats and bare pseudocode blocks of `flat` (outermost; `[start, end)` is the body,
 * after the float's placement or the block's `\begin`), with the label each is known by. */
function algorithmFloats(flat: string): Array<{ name: string; start: number; end: number; label: string | null }> {
  const out: Array<{ name: string; start: number; end: number; label: string | null }> = [];
  const open = /\\begin\s*\{(algorithm\*?|algorithmic)\}/gu;
  for (let m = open.exec(flat); m; m = open.exec(flat)) {
    const name = m[1]!;
    const close = new RegExp(String.raw`\\end\s*\{${name.replace("*", "\\*")}\}`, "u").exec(flat.slice(open.lastIndex));
    if (!close) continue;
    const bodyEnd = open.lastIndex + close.index;
    // a float's `[placement]` is no text of it; a bare block's `[1]` is the cutter's
    const start = open.lastIndex + (name === "algorithmic" ? 0 : (/^\s*\[[^\]]*\]/u.exec(flat.slice(open.lastIndex, bodyEnd))?.[0].length ?? 0));
    const body = flat.slice(start, bodyEnd);
    out.push({ name, start, end: bodyEnd, label: (captionLabel(body) ?? /\\label\s*\{([^{}]*)\}/u.exec(body)?.[1]?.trim()) || null });
    open.lastIndex = bodyEnd + close[0].length;
  }
  return out;
}

/**
 * The text a run of consecutive units `run` (of one region, in order) stands for: one unit is its
 * content (an item without its `\item` head); several units take every list they cover whole — from its
 * `\begin{…}` to its `\end{…}` — so the text never cuts a list. `partial`: the run takes several units
 * and only some items of a list (such a run cannot be replaced as one text). Pure.
 */
export function runSpan<U extends { kind: UnitKind; start: number; end: number; content: number; list: unknown; list_start?: number | null; list_end?: number | null; listStart?: number | null; listEnd?: number | null }>(
  run: readonly U[],
  items: (u: U) => readonly U[],
): { start: number; end: number; partial: boolean } {
  const first = run[0]!;
  const last = run.at(-1)!;
  if (run.length === 1) return { start: first.content, end: first.end, partial: false };
  const whole = (u: U): boolean => items(u).every((x) => run.includes(x));
  const partial = run.some((u) => u.kind === "item" && !whole(u));
  const ls = first.list_start ?? first.listStart ?? null;
  const le = last.list_end ?? last.listEnd ?? null;
  return { start: first.kind === "item" && whole(first) && ls !== null ? ls : first.content, end: last.kind === "item" && whole(last) && le !== null ? le : last.end, partial };
}

/** The body and proof of every environment located in `flat` (`envs.json`'s texts are verbatim slices of
 * it; the first occurrence at or after where the line map puts the environment, else the first). Pure. */
export function parseUnits(flat: string, envs: EnvsJson, lineStart: (file: string, line: number) => number | null = () => null): UnitsFile {
  const regions: UnitRegion[] = [];
  const units: Unit[] = [];
  const warnings: string[] = [];
  const push = (id: string, env: string, part: UnitPart, at: number, cut: readonly RegionUnit[]): void => {
    for (const r of cut) {
      units.push({
        id: `${id}/${r.p}/${r.u}`,
        env,
        part,
        p: r.p,
        u: r.u,
        kind: r.kind,
        start: at + r.start,
        end: at + r.end,
        content: at + r.content,
        list: r.list === null ? null : `${id}/L${r.list + 1}`,
        list_start: r.listStart === null ? null : at + r.listStart,
        list_end: r.listEnd === null ? null : at + r.listEnd,
      });
    }
  };
  const locate = (text: string, hint: number): number => {
    if (!text) return -1;
    const near = hint >= 0 ? flat.indexOf(text, hint) : -1;
    return near >= 0 ? near : flat.indexOf(text);
  };
  for (const env of envs.envs ?? []) {
    const hint = lineStart(env.lines.file, env.lines.from) ?? -1;
    const bodyAt = locate(env.body, hint);
    const parts: Array<{ part: UnitPart; text: string | null; at: number }> = [{ part: "body", text: env.body, at: bodyAt }];
    if (env.proof) {
      const ph = env.proofLines ? (lineStart(env.proofLines.file, env.proofLines.from) ?? -1) : bodyAt >= 0 ? bodyAt + env.body.length : -1;
      parts.push({ part: "proof", text: env.proof, at: locate(env.proof, ph) });
    }
    for (const { part, text, at } of parts) {
      if (text === null || at < 0) continue;
      const id = part === "body" ? env.id : `${env.id}/proof`;
      // Pseudocode step by step; a paper's own theorem-like `algorithm` (prose, a list) as any text.
      const bare = env.envName === "algorithmic";
      const steps = part === "body" && ALGORITHM_ENV.test(env.envName ?? "") && (bare || /\\begin\s*\{algorithmic\}/u.test(text)) ? algorithmUnits(text, bare) : null;
      if (steps && steps.units === null) warnings.push(`${env.id}: the algorithm is not cut into steps (${steps.why}); its units are its sentences`);
      regions.push({ id, env: env.id, part, start: at, end: at + text.length, ...(steps?.units ? { algorithm: true as const } : {}) });
      push(id, env.id, part, at, steps?.units ?? regionUnits(text));
    }
  }
  // The algorithm floats `envs.json` leaves out (no result refers to them): a region each.
  const used = new Set((envs.envs ?? []).map((e) => e.id));
  algorithmFloats(flat).forEach((f, k) => {
    if (regions.some((r) => r.start < f.end && f.start < r.end)) return;
    const base = f.label ?? `algorithm-${k + 1}`;
    let id = base;
    for (let n = 1; used.has(id); n += 1) id = `${base}-${n}`;
    used.add(id);
    const steps = algorithmUnits(flat.slice(f.start, f.end), f.name === "algorithmic");
    if (steps.units === null) return void warnings.push(`${id}: the algorithm is not cut into steps (${steps.why}); it has no units`);
    regions.push({ id, env: id, part: "body", start: f.start, end: f.end, algorithm: true });
    push(id, id, "body", f.start, steps.units);
  });
  return { version: UNITS_VERSION, flat_sha256: sha(flat), envs_sha256: sha(JSON.stringify(envs)), regions, units, ...(warnings.length > 0 ? { warnings } : {}) };
}

/** The parsed units with the text they index. */
export class PaperUnits {
  readonly byId: Map<string, Unit>;
  constructor(
    readonly flat: string,
    readonly file: UnitsFile,
  ) {
    this.byId = new Map(file.units.map((u) => [u.id, u] as const));
  }
  static parse(flat: string, envs: EnvsJson, lineStart?: (file: string, line: number) => number | null): PaperUnits {
    return new PaperUnits(flat, parseUnits(flat, envs, lineStart));
  }
  /** The units of an environment's body (`part` "proof": of its proof), in order. */
  unitsOf(env: string, part: UnitPart = "body"): Unit[] {
    return this.file.units.filter((u) => u.env === env && u.part === part);
  }
  unitById(id: string): Unit | undefined {
    return this.byId.get(id);
  }
  region(env: string, part: UnitPart = "body"): UnitRegion | undefined {
    return this.file.regions.find((r) => r.env === env && r.part === part);
  }
  /** A unit's text as printed (an item with its `\item` head). */
  textOf(u: Unit): string {
    return this.flat.slice(u.start, u.end);
  }
  /** What an op on the unit replaces: its text after an item's head. */
  contentOf(u: Unit): string {
    return this.flat.slice(u.content, u.end);
  }
  /** What an op on the unit `id` replaces (`contentOf`), null when there is no such unit: the text a
   * note quotes for a step (`owner_text.ts` `noteProse`). */
  textById = (id: string): string | null => {
    const u = this.byId.get(id);
    return u ? this.contentOf(u) : null;
  };
  /** What an op on the units `unit` … `to` (`to` absent: `unit` alone) replaces: the text of the run
   * between them in their region (`spanOf`); null when either is not a unit, they lie in different
   * regions, or `to` comes before `unit`. */
  textOfRun(unit: string, to?: string | null): string | null {
    const first = this.byId.get(unit);
    const last = to ? this.byId.get(to) : first;
    if (!first || !last || first.env !== last.env || first.part !== last.part) return null;
    const region = this.unitsOf(first.env, first.part);
    const i = region.indexOf(first);
    const j = region.indexOf(last);
    if (j < i) return null;
    const s = this.spanOf(region.slice(i, j + 1));
    return this.flat.slice(s.start, s.end);
  }
  /** The items of the list `u` is an item of (none for a sentence or display). */
  itemsOf(u: Unit): Unit[] {
    return u.list === null ? [] : this.file.units.filter((x) => x.list === u.list);
  }
  /** The span of a run of consecutive units (`runSpan`). */
  spanOf(run: readonly Unit[]): { start: number; end: number; partial: boolean } {
    return runSpan(run, (u) => this.itemsOf(u));
  }
}

/** A line-start resolver over `flat.linemap.json` (original file line → offset in `flat.tex`). */
export function flatLineStart(flat: string, lineMap: ReadonlyArray<{ file: string; line: number }>): (file: string, line: number) => number | null {
  const starts = [0];
  for (let i = 0; i < flat.length; i += 1) if (flat[i] === "\n") starts.push(i + 1);
  const at = new Map<string, number>();
  lineMap.forEach((l, k) => {
    const key = `${l.file}\u0000${l.line}`;
    if (!at.has(key) && starts[k] !== undefined) at.set(key, starts[k]!);
  });
  return (file, line) => at.get(`${file}\u0000${line}`) ?? null;
}

/** The run's units: `discovery/units.json` when it was parsed from the current `flat.tex` and `envs.json`,
 * else parsed afresh and cached. Null when either file is missing. */
export async function loadUnits(runDir: string, opts: { write?: boolean } = {}): Promise<PaperUnits | null> {
  const flatFile = path.join(runDir, VERIFY_FILES.flatTex);
  const envsFile = path.join(runDir, VERIFY_FILES.envsJson);
  if (!existsSync(flatFile) || !existsSync(envsFile)) return null;
  const flat = await readFile(flatFile, "utf8");
  const envsText = await readFile(envsFile, "utf8");
  const envs = JSON.parse(envsText) as EnvsJson;
  const cacheFile = path.join(runDir, UNITS_FILE);
  if (existsSync(cacheFile)) {
    try {
      const c = JSON.parse(await readFile(cacheFile, "utf8")) as UnitsFile;
      if (c.version === UNITS_VERSION && c.flat_sha256 === sha(flat) && c.envs_sha256 === sha(JSON.stringify(envs))) return new PaperUnits(flat, c);
    } catch {
      // an unreadable cache is parsed again
    }
  }
  const mapFile = path.join(runDir, VERIFY_FILES.flatLineMap);
  const lineMap = existsSync(mapFile) ? ((JSON.parse(await readFile(mapFile, "utf8")) as { lineMap?: Array<{ file: string; line: number }> }).lineMap ?? []) : [];
  const units = PaperUnits.parse(flat, envs, flatLineStart(flat, lineMap));
  if (opts.write !== false) await writeJsonAtomic(cacheFile, units.file);
  return units;
}
