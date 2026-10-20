// LeanSmith's additions to the statement structurer ported from the upstream project
// (`lean_structure.ts`). Kept out of the port so it re-syncs by re-copying: the port calls these at
// the places marked `LeanSmith` there, handing in its own `buildCard` (`Build`) where a piece is
// cut like a clause.
//
//   - a quantifier header that opens a binder of its own (`∃ h : ∀ t, …`) is not read as one
//     (`bindsInside`); a run of `∃` and filter quantifiers (`∀ᵐ x ∂μ,`) is hoisted (`stripScopeRun`);
//   - a case split (`if … then … else`, `match … with | … =>`) is one card per branch
//     (`branchSplit`); a disjunction of claims with parts is one card per alternative
//     (`disjunctSplit`, "either / or");
//   - a lifted `∀` header written as binder groups is one row per group (`forallRows`); a premise
//     that states a claim with parts is cut like a clause (`premiseRow`), and so is a NAMED
//     hypothesis whose type has parts (`namedRow`);
//   - no implication is read where a top-level `↔` makes the arrow the iff's side (`iffAtLevel`);
//   - a Prop record's parameters are its groups as written (`recordGroups`), a field is cut like a
//     clause (`fieldCard`).

import { normAwareDepths, parseBinderGroup, stripLeadingQuantifier, stripLeanComments } from "./lean_statement.js";
import { binderGroup, dedent, keywordAt, matchedCloseIndex, OPENERS, squash } from "./lean_text.js";
import type { ConclusionCard, HypRow } from "./lean_structure.js";

/** The port's `buildCard`: one clause cut recursively, with the text it reproduces (`recon`) and
 *  the length, squashed, of what its own line(s) take before its body (`lead`: the telescope lifted
 *  and the `∃` run hoisted). */
export interface BuiltCard { card: ConclusionCard; recon: string; lead?: number }
export type Build = (raw: string, depth: number) => BuiltCard | null;

/** `∀ᵐ x ∂μ,` / `∀ᶠ n in l,` / `∃ᶠ …,`: a quantifier that is a proposition of its own, not a
 *  telescope — hoisted like an `∃` when what it scopes has parts (`stripScopeRun`). */
export const FILTER_QUANTIFIER = /^(?:∀ᵐ|∀ᶠ|∃ᶠ|∃ᵐ)/;
/** Big-operator binders (`∑ x : T, …`): like `∀`, they scope the rest of the clause. */
const BIG_OPERATORS = new Set(["∑", "∏", "⨆", "⨅", "∫", "⨍", "⋃", "⋂", "⨁", "∮"]);
const SCOPE_WORDS = ["let", "letI", "have", "haveI", "fun", "match", "if", "do"];

/** The first index outside every bracket at which `test` holds, or -1. */
export function topLevelIndex(text: string, test: (i: number) => boolean, from = 0): number {
  const depths = normAwareDepths(text);
  for (let i = from; i < text.length; i++) if (depths[i] === 0 && test(i)) return i;
  return -1;
}

/** A quantifier header whose own text opens another binder (`∃ h : ∀ t`): the comma that ended it
 *  is that binder's, so the header is not read as one. */
export function bindsInside(header: string): boolean {
  return topLevelIndex(header, (i) => "∀∃λ".includes(header[i]) || keywordAt(header, i, "fun"), 1) >= 0;
}

/**
 * Whether `text` holds a `↔` at its own level, from `from` on, before anything that takes the rest
 * of it (a quantifier, a binder's colon or comma, a scope keyword). `↔` binds looser than `→`
 * (Lean: `infix:20 " ↔ "`, the arrow `checkPrec 25`), so `P → Q ↔ R` is `(P → Q) ↔ R` and
 * `P ↔ Q → R` is `P ↔ (Q → R)`: neither is an implication at this level. Pure.
 */
export function iffAtLevel(text: string, from = 0): boolean {
  const depths = normAwareDepths(text);
  for (let i = from; i < text.length; i++) {
    if (depths[i] !== 0) continue;
    const c = text[i];
    if (c === "↔") return true;
    if (c === "∀" || c === "∃" || c === "λ" || c === "," || c === ";" || c === "↦" || BIG_OPERATORS.has(c)) return false;
    if (c === ":" && text[i + 1] !== "=") return false;
    if (SCOPE_WORDS.some((kw) => keywordAt(text, i, kw))) return false;
  }
  return false;
}

/**
 * A leading run of `∃` binder groups and filter quantifiers, taken verbatim through each trailing
 * comma (replaces the upstream project's `stripExistsRun`), with how many headers it holds.
 */
export function stripScopeRun(text: string): { intro: string; rest: string; headers: number } | null {
  let t = text.trim();
  const headers: string[] = [];
  for (;;) {
    let q: { header: string; rest: string } | null = null;
    if (FILTER_QUANTIFIER.test(t)) {
      const comma = topLevelIndex(t, (i) => t[i] === ",");
      if (comma > 0) q = { header: t.slice(0, comma).trim(), rest: t.slice(comma + 1).trim() };
    } else if (t.startsWith("∃")) q = stripLeadingQuantifier(t);
    if (!q || !q.rest.trim() || bindsInside(q.header)) break;
    headers.push(dedent(q.header));
    t = q.rest;
  }
  if (headers.length === 0) return null;
  return { intro: headers.map((h) => `${h},`).join(" "), rest: t, headers: headers.length };
}

/** The cards a built clause contributes under a heading line: its conjuncts when it only
 *  branches, itself otherwise. */
export function partsOf(card: ConclusionCard): ConclusionCard[] {
  return card.hyps.length === 0 && !card.intro && card.sub ? card.sub : [card];
}

/**
 * A clause that is a case split — `if c then A else B`, `match x with | p => A | q => B` — as one
 * sub-card per branch, headed by its condition or pattern line (`intro`); a `match` keeps its own
 * head line. Every keyword stays in a row, so the rows still reproduce the source. Null — the
 * clause stays one leaf — for any shape not read with confidence.
 */
export function branchSplit(text: string, depth: number, build: Build): { intro?: string; cards: ConclusionCard[]; recon: string } | null {
  const t = text.trim();
  const depths = normAwareDepths(t);
  const kw = (i: number, word: string) => depths[i] === 0 && keywordAt(t, i, word);
  const branch = (head: string, body: string): BuiltCard | null => {
    const built = build(body, depth + 1);
    return built && { card: { hyps: [], intro: dedent(head), sub: partsOf(built.card) }, recon: head + built.recon };
  };
  if (keywordAt(t, 0, "if")) {
    // the `then` and `else` of the leading `if`, past any `if` nested between them
    let level = 0, then = -1, els = -1;
    for (let i = 0; i < t.length && els < 0; i++) {
      if (kw(i, "if")) level++;
      else if (kw(i, "then") && level === 1 && then < 0) then = i;
      else if (kw(i, "else") && --level === 0) els = i;
    }
    if (then < 0 || els < then) return null;
    const yes = branch(t.slice(0, then + 4), t.slice(then + 4, els));
    const no = branch("else", t.slice(els + 4));
    return yes && no ? { cards: [yes.card, no.card], recon: yes.recon + no.recon } : null;
  }
  if (!keywordAt(t, 0, "match")) return null;
  const w = topLevelIndex(t, (i) => keywordAt(t, i, "with"));
  if (w < 0) return null;
  const built: BuiltCard[] = [];
  let i = w + 4;
  for (;;) {
    while (i < t.length && /\s/.test(t[i])) i++;
    if (i >= t.length) break;
    if (t[i] !== "|") return null;
    let arrow = -1;
    for (let j = i + 1; j < t.length - 1 && arrow < 0; j++) {
      if (depths[j] !== 0) continue;
      if (t[j] === "|") return null;
      if (t[j] === "=" && t[j + 1] === ">") arrow = j;
    }
    if (arrow < 0) return null;
    // the alternative's body: to the next alternative — or to the end, when a `match` of its
    // own takes every alternative after it
    let end = t.length;
    for (let j = arrow + 2; j < t.length; j++) {
      if (kw(j, "match")) break;
      if (depths[j] === 0 && t[j] === "|") { end = j; break; }
    }
    const alt = branch(t.slice(i, arrow + 2), t.slice(arrow + 2, end));
    if (!alt) return null;
    built.push(alt);
    i = end;
  }
  if (built.length === 0) return null;
  const head = t.slice(0, w + 4);
  return { intro: dedent(head), cards: built.map((b) => b.card), recon: head + built.map((b) => b.recon).join("") };
}

/**
 * A disjunction at this level whose alternatives have parts of their own (`A ∧ B ∨ C ∧ D`: `∨`
 * binds looser than `∧`) as one card per alternative, marked `either` / `or`; the `∨` between them
 * is glue. Null for a plain `A ∨ B` (one leaf) and wherever `→`/`↔` or a binder takes the level.
 */
export function disjunctSplit(text: string, depth: number, build: Build): { cards: ConclusionCard[]; recon: string } | null {
  const t = text.trim();
  const depths = normAwareDepths(t);
  const cuts: number[] = [];
  for (let i = 0; i < t.length; i++) {
    if (depths[i] !== 0) continue;
    const c = t[i];
    if (c === "∨") { cuts.push(i); continue; }
    if (c === "→" || c === "↔" || c === ";" || c === "↦" || (c === "=" && t[i + 1] === ">")) return null;
    // a binder takes the rest: the alternatives before it stand
    if (c === "∀" || c === "∃" || c === "λ" || BIG_OPERATORS.has(c) || (c === ":" && t[i + 1] !== "=") || SCOPE_WORDS.some((kw) => keywordAt(t, i, kw))) break;
  }
  if (cuts.length === 0) return null;
  const pieces = [...cuts, t.length].map((end, k) => t.slice(k === 0 ? 0 : cuts[k - 1] + 1, end));
  const built: BuiltCard[] = [];
  for (const p of pieces) {
    const b = p.trim() ? build(p, depth + 1) : null;
    if (!b) return null;
    built.push(b);
  }
  if (!built.some((b) => b.card.sub || b.card.hyps.length > 0)) return null;
  return {
    cards: built.map((b, k) => ({ ...b.card, alt: k === 0 ? "either" : "or" })),
    recon: built.map((b) => b.recon).join("∨"),
  };
}

/** A type that ends in a sort, a number system or a container: an object's, not a proposition. */
const DATA_END = /(?:^|→\s*)(?:Type\*?|Sort\b|Prop|[ℝℕℤℚℂ](?:≥0∞?)?|Bool|Set\b|Finset\b|Fin\b|List\b|Measure\b|Matrix\b)[^→]*$/;

/** Where the `n`-th non-space character of `text` ends. */
function afterSquashed(text: string, n: number): number {
  let k = 0;
  for (let i = 0; i < text.length; i++) {
    if (k === n) return i;
    if (!/\s/.test(text[i])) k++;
  }
  return text.length;
}

/**
 * A named hypothesis `(h : T)` as a row — cut, when `T` has parts, like a premise with parts: its
 * head line (`head`) keeps the name and what `T` quantifies or assumes (`(h : ∀ k,`,
 * `(h : kind = .cate →`, `(h : ∃ δ,`), and the parts follow as cards with rows of their own (`sub`).
 * `T` is cut when it is an implication, a quantified or existential claim with two parts or more,
 * a conjunction of three or more (a two-sided bound `0 ≤ ρ ∧ ρ ≤ 1` is one phrase and stays whole),
 * or an either / or. The row's `code` keeps the binder whole. A head that is the name alone
 * (`(h :` over a conjunction) states nothing: it labels its parts and is no row (`bareHead`).
 */
export function namedRow(raw: string, chip: HypRow["chip"], depth: number, build: Build, maxDepth: number): HypRow {
  const row: HypRow = { chip, code: dedent(raw) };
  const g = binderGroup(raw);
  // a hypothesis only: `(m : Bool → X → ℝ)` is a function, its arrows no implication
  const propShaped = chip === "hyp" || /^[∀∃¬]/.test(g?.type ?? "") || (g !== null && topLevelIndex(g.type, (i) => "∧∨↔".includes(g.type[i])) >= 0);
  if (!g || g.open !== "(" || !propShaped || DATA_END.test(g.type) || depth + 1 >= maxDepth) return row;
  const built = build(g.type, depth + 1);
  if (!built || squash(built.recon) !== squash(g.type)) return row;
  const c = built.card;
  const parts = c.sub?.length ?? 0;
  const premise = c.hyps.some((h) => !h.code.trimStart().startsWith("∀") && !/^let[I]?\s|^haveI\s/.test(h.code.trimStart()));
  const scoped = c.hyps.length > 0 || Boolean(c.intro);
  const cut = (premise && (parts > 0 || Boolean(c.code))) || (scoped && parts >= 2) || parts >= 3 || Boolean(c.sub?.some((s) => s.alt));
  if (!cut) return row;
  // the group ends in its type and the closing bracket
  const t = raw.trim(), typeAt = t.slice(0, -1).trimEnd().length - g.type.length;
  const head = (t.slice(0, typeAt) + g.type.slice(0, afterSquashed(g.type, built.lead ?? 0))).trimEnd();
  const body: ConclusionCard[] = c.sub ? c.sub : [{ hyps: [], code: c.code ?? "" }];
  return { ...row, head: dedent(head), sub: body };
}

/** Whether a named hypothesis's head line is its name alone (`(h :`). */
export const bareHead = (head: string): boolean => /:\s*$/.test(head);

/**
 * A premise as a row. One that states a claim with parts of its own is also cut like a
 * conclusion clause (`HypRow.sub`); a binder written as a premise (`(h : A) → …`) is cut as a named
 * hypothesis is (`namedRow`).
 */
export function premiseRow(premise: string, depth: number, build: Build, maxDepth: number): HypRow {
  const g = binderGroup(premise);
  if (g) return namedRow(premise, parseBinderGroup(premise.trim())?.chip ?? "hyp", depth, build, maxDepth);
  const row: HypRow = { chip: "hyp", code: dedent(premise) };
  const built = depth + 1 >= maxDepth ? null : build(premise, depth + 1);
  if (built && (built.card.hyps.length > 0 || built.card.sub) && squash(built.recon) === squash(premise)) row.sub = partsOf(built.card);
  return row;
}

/**
 * The rows of a lifted `∀` header. One written as binder groups
 * (`∀ {α : Type*} [Fintype α] (x : α) (hx : P x)`) is cut as a signature's telescope is — one row
 * per group, as written, chipped by `parseBinderGroup`, a named hypothesis with parts cut by
 * `namedRow` — so a clause that carries a long telescope reads like a theorem's own hypotheses. Any
 * other header (`∀ n : ℕ`, `∀ x ∈ s`, `∀ k (i : Fin k)`) stays one row, chipped by `fallback`.
 */
export function forallRows(header: string, depth: number, build: Build, maxDepth: number, fallback: (header: string) => HypRow["chip"]): HypRow[] {
  const rows: HypRow[] = [];
  let rest = header.replace(/^∀/, "").trimStart();
  while (rest) {
    const close = matchedCloseIndex(rest);
    const parsed = close > 0 ? parseBinderGroup(rest.slice(0, close + 1)) : null;
    if (!parsed) return [{ chip: fallback(header), code: dedent(header) }];
    rows.push(namedRow(rest.slice(0, close + 1), parsed.chip, depth, build, maxDepth));
    rest = rest.slice(close + 1).trimStart();
  }
  return rows;
}

/** The binder groups of a `structure`/`class` head, each as written; null when unbalanced. */
export function recordGroups(rawSource: string): string[] | null {
  const cleaned = stripLeanComments(rawSource);
  const m = cleaned.match(/\b(?:structure|class)\s+[^\s({[⦃:]+/);
  if (!m || m.index === undefined) return null;
  const out: string[] = [];
  let rest = cleaned.slice(m.index + m[0].length).trimStart();
  while (OPENERS.includes(rest[0] ?? "")) {
    const close = matchedCloseIndex(rest);
    if (close < 0) return null;
    out.push(rest.slice(0, close + 1));
    rest = rest.slice(close + 1).trimStart();
  }
  return out;
}

/** A record field `name : type`. A type with parts of its own (a telescope, a conjunction, a case
 *  split) is cut like a clause under the line `name :`; any other is one leaf. */
export function fieldCard(name: string, type: string, build: Build): ConclusionCard {
  const built = build(type, 1);
  if (built && (built.card.hyps.length > 0 || built.card.sub) && squash(built.recon) === squash(type)) {
    return { hyps: [], intro: `${name} :`, sub: partsOf(built.card) };
  }
  return { hyps: [], code: `${name} : ${type}` };
}
