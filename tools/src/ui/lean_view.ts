// A result's Lean statement as the paper page's drawer draws it: the nested view F5 links
// (`formalization/lean_rows.ts`: one cut for the link step and the page) with each row's paper
// phrases on it, plus the paper's own Prop-valued declarations its rows name, each structured the
// same way and held once per run (upstream: `paperLean.ts` — the structured statement,
// `declSources`, the component closure).
//
// Narrower than the upstream project's closure on purpose: only `def`/`abbrev … : Prop` and Prop-valued
// `structure`/`class` declarations of the run's own Lean directory are expanded (a data definition,
// a library or toolkit declaration is not), and a name is looked up among the files the theorem's
// file imports from that directory — never outside it.

import { identifierTokens } from "../presentation/lean_statement.js";
import type { ConclusionCard, HypRow, StructuredView } from "../presentation/lean_structure.js";
import {
  binderChip, binderGroup, completeView, eachRow as eachViewRow, leanScopes, propDeclView, resolveName, squash, statementBody, typeTarget, viewRows,
  type Candidate, type StatementOf, type StatementView,
} from "../formalization/lean_rows.js";
import { legacyMatch } from "../formalization/nl_links.js";
import path from "node:path";
import { derive, readCached, signature } from "./fscache.js";

/** A hypothesis row on the page: the upstream project's row, its paper segments in `xl` (space-separated),
 *  `unstated` when the links say no segment states it, and the declarations it names (`refs`: keys
 *  of the run's `leanDefs`). `coarse`: its link is not one F5 gave this row alone — it is that of
 *  the stored row or clause it was cut from, of the `type_of%` clause it expands, or a list F5 gave
 *  many rows at once. */
export interface PageRow extends Omit<HypRow, "sub"> { unstated?: boolean; coarse?: boolean; refs?: string[]; sub?: PageCard[] }
/** `of`: the card is a clause written `type_of% @name`; its rows (`hyps`, `sub`) are the statement
 *  of that theorem and its own line names it. */
export interface PageCard extends Omit<ConclusionCard, "hyps" | "sub"> { hyps: PageRow[]; sub?: PageCard[]; unstated?: boolean; coarse?: boolean; refs?: string[]; of?: PageOf }
export type PageOf = StatementOf;
/** `statement`, `key`: what stored links are checked against — a theorem's view (`StatementView`); a
 *  declaration's has the `key` alone (`DeclView`). */
export interface PageView extends Omit<StructuredView, "sharedHyps" | "conclusions" | "defRow"> { sharedHyps: PageRow[]; conclusions: PageCard[]; defRow?: PageCard; statement?: string; key?: string }

/** One Prop-valued declaration of the paper's Lean: `definition` reads parameters · def · given by,
 *  `assumption` (a Prop-valued record) parameters · assumes. `source` only when it has no view;
 *  `node` when a `-- @node:` tag above it names the core node it formalizes. `segments`,
 *  `uncovered`: the paper's phrases its rows are linked to (the page model's, as a result's), when
 *  that node's links on file are this declaration's. */
export interface PageDef {
  name: string;
  kind: string;
  file: string;
  line: number;
  role: "definition" | "assumption";
  view: PageView | null;
  source: string;
  node?: string;
  segments?: PageSegment[];
  uncovered?: string[];
}

/** A phrase of the paper a row is linked to. `display`: a part of the displayed formula whose first
 *  part has that id — `alone` is the part as TeX that renders by itself, and the first part carries
 *  the formula `whole`. */
export interface PageSegment { id: string; text: string; display?: string; alone?: { text: string }; whole?: { text: string } }

export { propDeclView };
export type { StoredRow } from "../formalization/nl_links.js";
import type { StoredRow } from "../formalization/nl_links.js";

/** Every row of a view in reading order with its text (`lean_rows.ts` `eachRow`). `into` false: a
 *  clause that is another theorem's statement is visited as the one line the source has. */
export const eachRow = eachViewRow as (view: Pick<PageView, "sharedHyps" | "conclusions" | "defRow">, visit: (row: PageRow | PageCard, content: string) => void, into?: boolean) => void;

const put = (row: PageRow | PageCard, links: StoredRow[], coarse: boolean): void => {
  const xl = [...new Set(links.flatMap((s) => s.segments ?? []))];
  if (xl.length) row.xl = xl.join(" ");
  else if (links.some((s) => s.unstated)) row.unstated = true;
  else return;
  if (coarse || links.some((s) => s.coarse)) row.coarse = true;
};

/**
 * Put the stored links on the view's rows. False — and the view untouched — when they are not this
 * statement's (`linksRefusal` says why): written under another key (`StatementView.key`), or, for
 * links written before the key (the flat cut's), when the flat cut of this statement is not the one
 * they were written for, row for row (`legacyMatch`). Links of this statement's own rows go row by
 * row, by id; links written for another cut of the same statement are placed by where their rows
 * stand in it (`placeLinks`). A declaration's view (no `statement`) takes links under its key only.
 * Pure but for `view`.
 */
export function applyLinks(view: PageView, stored: StoredRow[], key?: string): boolean {
  if (key === undefined) return legacyMatch(view, stored) === "same" && placeLinks(view, stored);
  if (key !== view.key) return false;
  const byId = new Map(stored.map((s) => [s.id, s]));
  const rows = viewRows(view as StatementView);
  if (rows.length !== stored.length || rows.some((r) => !byId.has(r.id))) return Boolean(view.statement) && placeLinks(view, stored);
  eachRow(view, (row) => put(row, [byId.get(row.id!)!], false));
  return true;
}

/** Why stored links are not put on `view`: the statement changed since they were written (under
 *  their key); links of the flat cut were written against the statement cut short, or for a cut
 *  that is not its cut now (`recut`: it changed since, or the earlier cut read it otherwise). Pure. */
export function linksRefusal(view: Pick<PageView, "statement" | "key">, stored: StoredRow[], key?: string): "changed" | "truncated" | "recut" {
  if (key !== undefined) return "changed";
  return legacyMatch(view, stored) === "truncated" ? "truncated" : "recut";
}

/**
 * Links written for another cut of this same statement (the flat cut, or an older nested one): a
 * stored row and a row of the view each stand at one place in the statement's text, and a row
 * takes the links of the stored rows it overlaps — `coarse` unless it is the only row of one stored
 * row. The rows of a `type_of%` clause take the clause's; the section's variables (`section`), no
 * row of the statement's text, take none. False — and the view untouched — when a row of either
 * cut is not found in the statement, in order.
 */
function placeLinks(view: PageView, stored: StoredRow[]): boolean {
  const text = squash(statementBody(view.statement!));
  const locate = (codes: string[]): Array<[number, number]> | null => {
    const out: Array<[number, number]> = [];
    let pos = 0;
    for (const code of codes) {
      const at = text.indexOf(code, pos);
      if (at < 0) return null;
      out.push([at, pos = at + code.length]);
    }
    return out;
  };
  const rows: Array<PageRow | PageCard> = [], codes: string[] = [];
  eachRow(view, (row, content) => { if (!(row as PageRow).section) { rows.push(row); codes.push(squash(content)); } }, false);
  const own = stored.filter((s) => !s.id.includes("/") && !/^v\d+$/.test(s.id));
  const at = locate(codes);
  const was = locate(own.map((s) => squash(s.names ? `${s.names}:${s.lean}` : s.lean)));
  if (!at || !was) return false;
  const over = (k: number): number[] => was.flatMap(([c, d], j) => (Math.max(at[k][0], c) < Math.min(at[k][1], d) ? [j] : []));
  const shared = new Map<number, number>();
  rows.forEach((_, k) => { for (const j of over(k)) shared.set(j, (shared.get(j) ?? 0) + 1); });
  rows.forEach((row, k) => {
    const js = over(k);
    const links = js.map((j) => own[j]);
    put(row, links, js.length !== 1 || shared.get(js[0]) !== 1);
    const card = row as PageCard;
    if (card.of) eachRow({ sharedHyps: card.hyps, conclusions: card.sub ?? [] }, (r) => put(r, links, true));
  });
  return true;
}

const NAME = /^[^\s()[\]{}⦃⦄:∀∃λ,]+$/;

/** The names a view's rows bind (binder groups, `∀`/`∃` headers, `let`s): not references. Pure. */
export function boundNames(view: PageView): Set<string> {
  const out = new Set<string>();
  const names = (t: string) => { for (const n of t.split(/\s+/)) if (NAME.test(n)) out.add(n); };
  const header = (t: string) => {
    // a quantifier's own binders end at its first comma outside brackets
    let depth = 0, end = t.length;
    for (let i = 0; i < t.length; i++) {
      if ("({[⦃".includes(t[i])) depth++;
      else if (")}]⦄".includes(t[i])) depth--;
      else if (t[i] === "," && depth === 0) { end = i; break; }
    }
    const h = t.slice(0, end);
    // `(x y : T) {z : U}` — the names before each group's colon; bare `x y : T` — before the colon
    let hit = false;
    for (const m of h.matchAll(/[({[⦃]\s*([^:(){}[\]⦃⦄]*?)\s*:/g)) { hit = true; names(m[1]); }
    if (!hit) names(h.split(/:|∈/)[0]);
  };
  eachRow(view, (_row, content) => {
    const t = content.trim();
    if ("({[⦃".includes(t[0] ?? "")) { const m = /^.\s*([^:(){}[\]⦃⦄]*?)\s*:/.exec(t); if (m) names(m[1]); return; }
    if (/^let\s/.test(t)) { names(t.slice(3).trim().split(/[\s:]/)[0]); return; }
    for (const q of t.split(/(?=[∀∃])/)) if (/^[∀∃]/.test(q)) header(q.slice(1));
  });
  return out;
}

// ── the paper's own declarations ─────────────────────────────────────────────

/** Nesting of expansions followed from a statement (the upstream project's closure depth). */
const MAX_DEF_DEPTH = 6;
const MAX_DEFS = 300;
const MAX_SOURCE = 8000;
const DEF_KINDS = new Set(["def", "abbrev", "structure", "class"]);

const parsedDefs = new Map<string, { role: PageDef["role"]; view: StructuredView | null; source: string; node: string | null } | null>();

/**
 * The declarations of one run's Lean directory that its results' statements name. `annotate` first
 * completes the view as F5 does (`completeView`: the section variables the statement takes, each
 * clause written `type_of% @name` opened into the statement of the run's theorem `name`). It then stamps `refs` on the view's rows, files each
 * named Prop-valued declaration (and, to `MAX_DEF_DEPTH`, the ones its own rows name) once in
 * `defs`, and lets what a binder's type names decide its chip: a hypothesis when it is one of these
 * declarations, an object when it is a record of the paper that is not Prop-valued. `cited`: the
 * names of the run's cited results (`leanStatementView`). `read`: how the run's Lean files are read.
 */
export function leanDefs(toolkitRoot: string, leanDir: string, cited: ReadonlySet<string> = new Set(), read: (abs: string) => Promise<string | null> = readCached): { defs: Record<string, PageDef>; include: (file: string, decl: string) => Promise<void>; annotate: (view: PageView, file: string, decl: string, line?: number) => Promise<void> } {
  const defs: Record<string, PageDef> = {};
  // `read` sees every file used, also one whose parse is taken from memory (a caller may key on them)
  const lean = leanScopes({ toolkitRoot, leanDir, read, memo: async (name, abs, compute) => { await read(abs); return (await derive(`${name}:${abs}`, [abs], "", compute)).value; } });

  /** The Prop-valued declaration at `c`, parsed once per version of its file; null when it is not one. */
  const loadDef = async (c: Candidate): Promise<PageDef | null> => {
    const abs = path.join(leanDir, c.file);
    const key = `${abs}|${signature(abs)}|${c.line}|${c.name}`;
    if (!parsedDefs.has(key)) {
      const src = await lean.sourceOf(c);
      const pv = src ? propDeclView(src.source) : null;
      parsedDefs.set(key, src && pv ? { ...pv, source: src.source, node: src.node } : null);
    }
    const hit = parsedDefs.get(key);
    if (!hit) return null;
    // a copy: the run's table annotates its rows
    const view = hit.view ? structuredClone(hit.view) as PageView : null;
    return { name: c.name, kind: c.kind, file: c.file, line: c.line, role: hit.role, view, source: view ? "" : hit.source.slice(0, MAX_SOURCE), ...(hit.node ? { node: hit.node } : {}) };
  };

  const visit = async (v: PageView, site: Candidate, depth: number): Promise<void> => {
    const scope = await lean.scopeOf(site.file);
    const self = `${site.file}#${site.name}`;
    const bound = boundNames(v);
    const rows: Array<[PageRow | PageCard, string]> = [];
    eachRow(v, (row, content) => rows.push([row, content]));
    for (const [row, content] of rows) {
      const refs: string[] = [];
      const what = new Map<string, "prop" | "data">();
      for (const tok of new Set(identifierTokens(content))) {
        if (bound.has(tok) || bound.has(tok.split(".")[0])) continue;
        const c = resolveName(scope, tok, DEF_KINDS, site);
        const d = c ? await loadDef(c) : null;
        if (c && (d || c.kind === "structure" || c.kind === "class")) what.set(tok, d ? "prop" : "data");
        const key = c ? `${c.file}#${c.name}` : "";
        if (!c || !d || key === self) continue;
        if (!defs[key]) {
          if (Object.keys(defs).length >= MAX_DEFS) continue;
          defs[key] = d;
          if (d.view && depth < MAX_DEF_DEPTH) await visit(d.view, c, depth + 1);
        }
        refs.push(key);
      }
      if (refs.length) row.refs = refs;
      const g = "hyps" in row ? null : binderGroup(content);
      if (g?.open === "(" && !("hyps" in row) && row.chip !== "cited") row.chip = binderChip(g.names, g.type, what.get(identifierTokens(typeTarget(g.type))[0] ?? ""));
    }
  };

  const annotate = async (view: PageView, file: string, decl: string, line?: number): Promise<void> => {
    const site = await lean.siteOf(file, decl, line);
    if (!site) return;
    if (view.statement) await completeView(view as StatementView, file, decl, lean, cited, line);
    await visit(view, site, 1);
  };
  /** A declaration no drawn statement names (an assumption no result takes whole): in the table all the same. */
  const include = async (file: string, decl: string): Promise<void> => {
    const c = await lean.siteOf(file, decl);
    const key = c ? `${c.file}#${c.name}` : "";
    if (!c || defs[key] || Object.keys(defs).length >= MAX_DEFS) return;
    const d = await loadDef(c);
    if (!d) return;
    defs[key] = d;
    if (d.view) await visit(d.view, c, 2);
  };
  return { defs, annotate, include };
}
