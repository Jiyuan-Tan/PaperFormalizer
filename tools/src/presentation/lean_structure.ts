// PORTED from the upstream project's `tools/src/presentation/lean_structure.ts` (the "structured
// (hypotheses / conclusions) view" of its site's `paperLean.ts`, plus `assignRowIds`): a statement
// as shared hypothesis rows and nested conclusion cards, a Prop-valued definition or record the
// same way. Re-sync by re-copying that file, then re-apply the TheoremChecker changes, each a call
// marked `TheoremChecker` into `lean_structure_tc.ts` (what those additions are is said there) or a
// one-line change so marked; the text primitives (`squash`, `dedent`, the bracket matcher, …) live
// in `lean_text.ts`. The chips are set again by TheoremChecker's own rule outside this file
// (`formalization/lean_rows.ts` `chipRows`).
//
// `assignRowIds` stamps a stable `id` ("r1", "r2", … in reading order) on every hypothesis row and
// every conclusion card's content row: the ids F5 links paper segments to and the page draws
// (`formalization/lean_rows.ts`).
//
// NOT brought over from the upstream project (they live in its site, not in this file): the component
// closure and its classes (`paperLean.ts` `enrichSnippets`), cited-result bookkeeping beyond the
// `citedNames` parameter, and Lean highlighting/linkify. `xl` on a row is unused here.

import {
  classifyChip,
  identifierTokens,
  isBinderRow,
  isChain,
  normAwareDepths,
  parseBinderGroup,
  scanDefinitionSignature,
  scanPropDefinitionSignature,
  splitWhereFields,
  scanPropositionSignature,
  structureRecordSource,
  stripLeadingQuantifier,
  stripLeanComments,
  topLevelConjuncts,
  type StmtBody,
} from "./lean_statement.js";
import { LEAN_DECL_MODIFIERS } from "../shared/lean_syntax.js";
import { dedent, keywordAt, matchedCloseIndex, OPENERS, squash, topLevelColonIndex } from "./lean_text.js";
import {
  bareHead, bindsInside, branchSplit, disjunctSplit, fieldCard, forallRows, iffAtLevel, namedRow, partsOf, premiseRow, recordGroups, stripScopeRun,
  type BuiltCard,
} from "./lean_structure_tc.js";

export interface HypRow {
  /** Stable row id within this block's structured view ("r1", "r2", … in
   *  reading order) — the handle the artifact's assignments refer to. */
  id?: string;
  /** `cited` marks a hypothesis whose type is an ASSUMED external result — an
   *  input to the theorem, not something this development proves. */
  chip: "hyp" | "decl" | "cited";
  code: string;
  /** Space-separated NL↔Lean crosslink ids (HTML-class style; word-match
   *  with `[data-xl~="…"]`). A row can be covered by several links. */
  xl?: string;
  /** TheoremChecker: a premise that states a claim with parts of its own — `(A → B)`,
   *  `(∀ x ∈ s, P x ∧ Q x)`, `(A ∧ B)` — cut like a conclusion clause. `code` keeps the premise
   *  whole; its rows are `sub`'s, and the premise has no row of its own. */
  sub?: ConclusionCard[];
  /** TheoremChecker: a NAMED hypothesis with parts (`lean_structure_tc.ts` `namedRow`): its own
   *  line — the name and what its type quantifies or assumes (`(h : ∀ k,`); `sub` holds the parts. */
  head?: string;
  /** TheoremChecker: a binder of the enclosing section's `variable`s the statement uses
   *  (`formalization/lean_rows.ts` `withSectionVariables`), not one of the declaration's own. */
  section?: true;
}

/**
 * One clause of a theorem's goal, recursively fine-grained: the telescope
 * lifted at THIS level, an optional non-liftable prefix, and then EITHER a leaf
 * statement or a further split. Exactly one of `code` / `sub` is present.
 */
export interface ConclusionCard {
  /** Stable row id for this card's own content row (see HypRow.id). */
  id?: string;
  /** `∀` binders and `premise →` prefixes lifted at this level. */
  hyps: HypRow[];
  /** A leading run of `∃` binder groups, verbatim through its trailing comma —
   *  it scopes everything below, but is not a hypothesis. Only ever set
   *  alongside `sub`: an `∃` whose body doesn't split stays inside `code`.
   *  TheoremChecker: also a run of filter quantifiers (`∀ᵐ x ∂μ,`), the head of a
   *  case split (`match x with`), a branch's condition or pattern (`if c then`,
   *  `else`, `| p =>`) and a record field's name (`name :`). */
  intro?: string;
  /** Leaf statement. */
  code?: string;
  /** Nested split of a conjunction at this level. */
  sub?: ConclusionCard[];
  /** Space-separated NL↔Lean crosslink ids for the card's own content row:
   *  its `intro` when it nests, its `code` when it is a leaf. */
  xl?: string;
  /** TheoremChecker: one alternative of a disjunction cut into its alternatives (`disjunctSplit`). */
  alt?: "either" | "or";
}

export interface StructuredView {
  sharedHyps: HypRow[];
  conclusions: ConclusionCard[];
  /** Definitions only: the `name params : type` row between the parameters
   *  and the given-by clauses (`structureDefinitionView`). Carries an id /
   *  crosslink token like any content row. */
  defRow?: ConclusionCard;
  /** What the name row declares — labels the drawer (`def` by default). */
  role?: "def" | "instance" | "inductive";
}

/** Whether this is an explicitly Prop-valued `structure`/`class`. The final
 * `: Prop` check is made on the declaration header (before `where`), so a
 * parameter whose own type is `Prop` cannot trigger it. */
export function isPropRecord(statement: string): boolean {
  const cleaned = stripLeanComments(statement);
  const where = cleaned.search(/\bwhere\b/);
  if (where < 0) return false;
  const header = cleaned.slice(0, where).trimEnd();
  return /\b(structure|class)\b/.test(header) && /:\s*Prop\s*$/.test(header);
}

const stmtLinesText = (lines: Array<{ indent: number; text: string }>): string =>
  lines.map((line) => `${"  ".repeat(Math.max(0, line.indent))}${line.text}`).join("\n");

/** Reconstructs the readable type of a record parameter/field. This is only a
 * display tree—the conservative record parser has already proved that every
 * field was consumed. */
function stmtBodyText(body: StmtBody): string {
  if (!isChain(body)) return stmtLinesText(body);
  const parts: string[] = [];
  if (body.header?.length) parts.push(`${stmtLinesText(body.header)},`);
  parts.push(...body.premises.map((premise) => `${stmtLinesText(premise)} →`));
  parts.push(stmtLinesText(body.conclusion));
  return parts.join("\n");
}

/** A Prop-valued record is a conjunction-like assumption/definition: its
 * telescope supplies parameters and each `where` field is one defining clause.
 * Convert the existing conservative record parse into the same view P4 emits
 * for a `def … : Prop := A ∧ B`, without changing the site's artifact schema. */
export function structurePropRecordView(rawSource: string): StructuredView | null {
  if (!isPropRecord(rawSource)) return null;
  const record = structureRecordSource(rawSource);
  if (!record?.fields) return null;

  // TheoremChecker: the parameters are the binder groups as written (the record parse folds an
  // instance into the parameter it constrains, which no bracket pair can quote back).
  const groups = recordGroups(rawSource);
  if (!groups) return null;
  const sharedHyps: HypRow[] = [];
  for (const raw of groups) {
    const parsed = parseBinderGroup(raw);
    if (!parsed) return null;
    sharedHyps.push({ chip: parsed.chip, code: dedent(raw) });
  }
  const conclusions: ConclusionCard[] = [];
  for (const item of record.rows) {
    if (!isBinderRow(item) || item.names !== "extends") continue;
    const body = stmtBodyText(item.body);
    if (!body) return null;
    conclusions.push({ hyps: [], code: `extends ${body}` });
  }
  for (const item of record.fields) {
    if (!isBinderRow(item)) continue;
    const body = stmtBodyText(item.body);
    if (!body) return null;
    conclusions.push(fieldCard(item.names, body, buildCard)); // TheoremChecker
  }
  return conclusions.length > 0 ? { sharedHyps, conclusions } : null;
}

/**
 * One declaration's source, held ONCE per paper in `Bundle.declSources` rather
 * than inlined into every drawer that reaches it. The same helper is pulled in
 * by dozens of statements — inlining it multiplied the payload roughly threefold.
 */
// ---------------------------------------------------------------------------
// structured (hypotheses / conclusions) view
// ---------------------------------------------------------------------------

// TheoremChecker: `letI`/`haveI` scope the rest of the clause as `let`/`have` do.
const SCOPE_KEYWORDS = ["let", "letI", "have", "haveI", "fun", "match", "if", "do"];
/** Big-operator binders (`∑ x : T, …`): like `∀`, they scope the rest of the clause. */
const BIG_OPERATORS = new Set(["∑", "∏", "⨆", "⨅", "∫", "⨍", "⋃", "⋂", "⨁", "∮"]);

/**
 * Index of the leading implication arrow — the `→` that separates a premise
 * from the rest — or -1 when there is none, or when reading one would be
 * unsound. It is unsound as soon as a binder opens first: in `∃ f : α → β, P f`
 * the depth-0 `→` belongs to `f`'s TYPE, not to an implication, and splitting
 * there would invent the hypothesis `∃ f : α`.
 */
function leadingImplicationIndex(text: string): number {
  const depths = normAwareDepths(text);
  for (let i = 0; i < text.length; i++) {
    if (depths[i] !== 0) continue;
    const c = text[i];
    // TheoremChecker: `P → Q ↔ R` is `(P → Q) ↔ R`, `P ↔ Q → R` is `P ↔ (Q → R)`: no premise here
    if (c === "↔") return -1;
    if (c === "→") return iffAtLevel(text, i + 1) ? -1 : i;
    // Binders scope everything to their right: quantifiers, big operators, and
    // — generically — anything that has opened a binder: a depth-0 `:` (not
    // `:=`) can only be a binder's type colon (`∑ d : Fin n → κ × Bool, …`,
    // `⨆ i : ι → ℝ, …`, `fun x : A → B => …`), so a later `→` is that type's.
    if (c === "∀" || c === "∃" || c === "," || c === ";" || c === "↦" || BIG_OPERATORS.has(c)) return -1;
    if (c === ":" && text[i + 1] !== "=") return -1;
    if (c === "=" && text[i + 1] === ">") return -1;
    if (SCOPE_KEYWORDS.some((kw) => keywordAt(text, i, kw))) return -1;
  }
  return -1;
}

/**
 * True when splitting `text` at its depth-0 `∧`s is faithful to Lean's
 * precedence. `∧` binds tighter than `→`, `∨` and `↔`, so a depth-0 occurrence
 * of any of those means the `∧`s are nested INSIDE a larger connective and
 * splitting on them would rewrite the statement (`A ∧ B → C` is
 * `(A ∧ B) → C`, not `A ∧ (B → C)`).
 *
 * The scan stops at the first depth-0 `∀`/`∃`, because those extend as far
 * right as the grammar allows: everything after one is its body, so `A ∧ B ∧
 * ∀ n, P n → Q n` really is three conjuncts and its `→` is not this level's.
 * `topLevelConjuncts` stops in the same place, so the two agree.
 */
function conjunctionSplitLimit(text: string): number {
  const depths = normAwareDepths(text);
  let sawConjunction = false;
  for (let i = 0; i < text.length; i++) {
    if (depths[i] !== 0) continue;
    const c = text[i];
    if (c === "∀" || c === "∃" || BIG_OPERATORS.has(c)) return text.length;
    if (c === ":" && text[i + 1] !== "=") return text.length; // a binder opened: its body owns the rest
    if (c === "∧") {
      sawConjunction = true;
      continue;
    }
    // A depth-zero comma is also the binder separator in `∑ x in s, f x` and
    // `sup x, f x`; it does not change the connective level. Quantifiers were
    // handled above, while `fun`/`match`/etc. are rejected by SCOPE_KEYWORDS.
    if (c === "→" || c === "∨" || c === "↔" || c === ";" || c === "↦") return -1;
    if (c === "=" && text[i + 1] === ">") return -1;
    if (SCOPE_KEYWORDS.some((kw) => keywordAt(text, i, kw))) {
      // `A ∧ let x := v; B ∧ C` may be split immediately before `let`, but
      // not at the later conjunction: that one is inside the let's body. The
      // resulting suffix card peels the let first and can then split B/C.
      return sawConjunction ? i : -1;
    }
  }
  return text.length;
}

/** The depth-0 conjuncts of `text`, or `null` when it is not a conjunction at
 *  this level (or splitting it would misread Lean's precedence). */
function conjunctsOf(text: string): string[] | null {
  const limit = conjunctionSplitLimit(text);
  if (limit < 0) return null;
  let parts: string[];
  if (limit === text.length) {
    parts = topLevelConjuncts(text);
  } else {
    parts = [];
    const depths = normAwareDepths(text);
    let start = 0;
    for (let i = 0; i < limit; i++) {
      if (depths[i] === 0 && text[i] === "∧") {
        parts.push(text.slice(start, i).trim());
        start = i + 1;
      }
    }
    parts.push(text.slice(start).trim());
  }
  return parts.length > 1 && parts.every((p) => p.trim()) ? parts : null;
}

function forallChip(header: string): "hyp" | "decl" {
  const body = header.replace(/^∀/, "").trim();
  if (OPENERS.includes(body[0] ?? "")) {
    const close = matchedCloseIndex(body);
    if (close > 0) {
      const parsed = parseBinderGroup(body.slice(0, close + 1));
      if (parsed) return parsed.chip;
    }
  }
  const colon = topLevelColonIndex(body);
  const names = colon >= 0 ? body.slice(0, colon).trim() : body;
  const type = colon >= 0 ? body.slice(colon + 1).trim() : "";
  return classifyChip(names, "explicit", type);
}

interface Lift {
  hyps: HypRow[];
  /** Everything peeled off the FRONT, concatenated verbatim (modulo layout). */
  prefix: string;
  inner: string;
  /** Everything peeled off the BACK (closing parens of an unwrapped clause). */
  suffix: string;
}

interface LetRun {
  rows: HypRow[];
  /** The let declarations, used only by the losslessness reconstruction. */
  prefix: string;
  rest: string;
}

/**
 * Peels a layout-delimited run of conclusion-local `let` declarations.
 *
 * Lean's common theorem shape
 *
 *     : let W := ...
 *       let denominator := ...
 *       P W denominator ∧ Q W
 *
 * has no punctuation between the declarations and the proposition: layout is
 * the delimiter. After `dedent`, each declaration and the body starts in
 * column zero while continuation lines remain indented. We only act on that
 * unambiguous shape; unusual inline/layout forms remain a single leaf.
 */
// TheoremChecker: `letI := inst` / `haveI := inst` are peeled like `let`.
const LET_KEYWORDS = ["let", "letI", "haveI"];

function stripLetRun(text: string): LetRun | null {
  let rest = dedent(text).trimStart();
  let prefix = "";
  const rows: HypRow[] = [];
  for (let guard = 0; guard < 64 && LET_KEYWORDS.some((kw) => keywordAt(rest, 0, kw)); guard++) {
    const depths = normAwareDepths(rest);
    let semicolon = -1;
    for (let i = 0; i < rest.length; i++) {
      if (depths[i] === 0 && rest[i] === ";") {
        semicolon = i;
        break;
      }
    }

    let layout = -1;
    let offset = 0;
    const lines = rest.split("\n");
    for (let i = 0; i < lines.length; i++) {
      if (i > 0 && lines[i].trim() && (lines[i].match(/^ */)?.[0].length ?? 0) === 0) {
        layout = offset;
        break;
      }
      offset += lines[i].length + (i < lines.length - 1 ? 1 : 0);
    }

    const useSemicolon = semicolon >= 0 && (layout < 0 || semicolon < layout);
    const boundary = useSemicolon ? semicolon : layout;
    if (boundary <= 0) return null;
    const code = rest.slice(0, boundary).trim();
    if (!/^(?:let|letI|haveI)\b[\s\S]*:=/.test(code)) return null;
    rows.push({ chip: "decl", code: dedent(code) });
    const consumed = useSemicolon ? boundary + 1 : boundary;
    prefix += rest.slice(0, consumed);
    rest = rest.slice(consumed).trimStart();
  }
  return rows.length > 0 && rest ? { rows, prefix, rest } : null;
}

/**
 * A clause prefix may alternate scopes: `let B := ...; ∀ L, premise → let C :=
 * ...; body`. Peel the whole run in source order so every local declaration and
 * governed hypothesis becomes a row before the body is recursively split.
 */
function liftCardPrefix(raw: string, depth: number): Lift {
  let inner = raw.trim();
  const hyps: HypRow[] = [];
  let prefix = "";
  let suffix = "";
  for (let guard = 0; guard < 64; guard++) {
    const lift = liftTelescope(inner, depth);
    hyps.push(...lift.hyps);
    prefix += lift.prefix;
    suffix = lift.suffix + suffix;
    inner = lift.inner;

    const lets = stripLetRun(inner);
    if (!lets) break;
    hyps.push(...lets.rows);
    prefix += lets.prefix;
    inner = lets.rest;
  }
  return { hyps, prefix, inner, suffix };
}

/**
 * Peels a clause's own leading telescope — `∀` binders and `premise →`
 * prefixes, through any parentheses wrapping the whole clause — into
 * hypothesis rows, leaving the proposition they govern as `inner`.
 * `prefix + inner + suffix` reproduces the input modulo whitespace, which the
 * caller checks.
 */
function liftTelescope(raw: string, depth: number): Lift {
  let t = raw.trim();
  const prefix: string[] = [];
  const suffix: string[] = [];
  const hyps: HypRow[] = [];
  for (let guard = 0; guard < 64; guard++) {
    if (t.startsWith("(") && matchedCloseIndex(t) === t.length - 1) {
      prefix.push("(");
      suffix.unshift(")");
      t = t.slice(1, -1).trim();
      continue;
    }
    if (t.startsWith("∀")) {
      const q = stripLeadingQuantifier(t);
      if (!q || bindsInside(q.header)) break; // TheoremChecker: `∀ h : ∀ t, …` is not cut at the inner comma
      hyps.push(...forallRows(q.header, depth, buildCard, MAX_CARD_DEPTH, forallChip)); // TheoremChecker
      prefix.push(q.header, ",");
      t = q.rest;
      continue;
    }
    const arrow = leadingImplicationIndex(t);
    if (arrow > 0) {
      const premise = t.slice(0, arrow).trim();
      hyps.push(premiseRow(premise, depth, buildCard, MAX_CARD_DEPTH)); // TheoremChecker
      prefix.push(premise, "→");
      t = t.slice(arrow + 1).trim();
      continue;
    }
    break;
  }
  return { hyps, prefix: prefix.join(""), inner: t, suffix: suffix.join("") };
}

/** How many levels of conclusion nesting are split. Six covers the deepest
 * accepted-paper statements while the renderer's inset rules still make the
 * scope visible; the losslessness check remains the final guard. */
const MAX_CARD_DEPTH = 6;

/**
 * One clause of a goal, fine-grained recursively: lift this level's
 * `∀`/`premise →` telescope, hoist any leading `∃` run, then split a
 * conjunction into nested cards — or stop at a leaf.
 */
function buildCard(raw: string, depth: number): BuiltCard | null {
  const lift = liftCardPrefix(raw, depth);
  if (!lift.inner.trim()) return null;
  const localHyps = lift.hyps;
  const inner = lift.inner;
  const localPrefix = lift.prefix;
  const leaf = (): BuiltCard => ({
    card: { hyps: localHyps, code: dedent(inner) },
    recon: localPrefix + inner + lift.suffix,
    lead: squash(localPrefix).length, // TheoremChecker
  });
  if (depth >= MAX_CARD_DEPTH) return leaf();

  const ex = stripScopeRun(inner);
  // An `∃` prefix earns its own row only if hoisting it actually reveals a
  // split; otherwise the clause reads better whole, `∃` and all.
  const parts = conjunctsOf(ex ? ex.rest : inner);
  if (!parts) {
    // TheoremChecker: what the run scopes may have parts without being a conjunction (a telescope,
    // a case split), and a run of several quantifiers is a line of its own; a clause that is a
    // case split is one sub-card per branch.
    const scoped = ex ? buildCard(ex.rest, depth + 1) : null;
    if (ex && scoped && (ex.headers > 1 || scoped.card.hyps.length > 0 || scoped.card.sub)) {
      return {
        card: { hyps: localHyps, intro: ex.intro, sub: partsOf(scoped.card) },
        recon: localPrefix + ex.intro + scoped.recon + lift.suffix,
        lead: squash(localPrefix + ex.intro).length,
      };
    }
    const split: { intro?: string; cards: ConclusionCard[]; recon: string } | null = ex ? null : branchSplit(inner, depth, buildCard) ?? disjunctSplit(inner, depth, buildCard);
    if (!split) return leaf();
    const intro = split.intro;
    return {
      card: { hyps: localHyps, ...(intro ? { intro } : {}), sub: split.cards },
      recon: localPrefix + split.recon + lift.suffix,
      lead: squash(localPrefix + (intro ?? "")).length,
    };
  }

  const subs: BuiltCard[] = [];
  for (const p of parts) {
    const built = buildCard(p, depth + 1);
    if (!built) return null;
    subs.push(built);
  }
  const card: ConclusionCard = { hyps: localHyps };
  if (ex) card.intro = ex.intro;
  card.sub = subs.map((s) => s.card);
  return {
    card,
    recon: localPrefix + (ex?.intro ?? "") + subs.map((s) => s.recon).join("∧") + lift.suffix,
    lead: squash(localPrefix + (ex?.intro ?? "")).length, // TheoremChecker
  };
}

/**
 * The type half of a binder row: `(hZeng : ZengOneArmMinimaxLower epsilon)` →
 * `ZengOneArmMinimaxLower epsilon`. A lifted `∀` header or `premise →` row has
 * no name half, so it is its own type.
 */
function binderTypeText(code: string): string {
  if (!OPENERS.includes(code[0] ?? "")) return code;
  const close = matchedCloseIndex(code);
  const inner = close > 0 ? code.slice(1, close) : code.slice(1);
  const colon = topLevelColonIndex(inner);
  return colon >= 0 ? inner.slice(colon + 1) : inner;
}

/**
 * Re-chips hypothesis rows whose type names an assumed external result.
 *
 * `(hZeng : ZengOneArmMinimaxLower epsilon)` is not a condition the paper
 * establishes — it is an input it takes on faith from the cited literature.
 * Showing it in the Hypotheses block chipped exactly like a proved side
 * condition hides the one thing a reader most needs to see. Only rows already
 * read as hypotheses are re-chipped; a type-class or type parameter is not an
 * assumption however its type reads.
 */
function markCitedHyps(rows: readonly HypRow[], citedNames: ReadonlySet<string>): void {
  if (citedNames.size === 0) return;
  for (const row of rows) {
    if (row.chip !== "hyp") continue;
    for (const tok of identifierTokens(binderTypeText(row.code))) {
      if (citedNames.has(tok)) {
        row.chip = "cited";
        break;
      }
    }
  }
}

/** Every hypothesis row of a structured view, at any nesting depth. */
function allHypRows(view: StructuredView): HypRow[] {
  const out: HypRow[] = [...view.sharedHyps];
  const walk = (c: ConclusionCard) => {
    out.push(...c.hyps);
    for (const sub of c.sub ?? []) walk(sub);
  };
  for (const c of view.conclusions) walk(c);
  return out;
}

/**
 * A theorem/lemma or Prop-valued definition as shared parameters plus one card
 * per top-level conjunct of its proposition, each card recursively fine-grained. Returns `null` —
 * the caller then shows the raw statement — for anything it cannot reproduce
 * exactly.
 *
 * `citedNames` (short and fully-qualified names of the paper's cited external
 * results) re-chips the hypotheses that assume one.
 */
export function structureStatementView(
  rawSource: string,
  citedNames: ReadonlySet<string> = new Set(),
): StructuredView | null {
  const scan = scanPropositionSignature(rawSource);
  if (!scan) return null;

  const sharedHyps: HypRow[] = [];
  for (const g of scan.groups) {
    const parsed = parseBinderGroup(g.raw);
    if (!parsed) return null; // one unparseable binder aborts the whole view
    sharedHyps.push(namedRow(g.raw, parsed.chip, 0, buildCard, MAX_CARD_DEPTH)); // TheoremChecker
  }

  const goal = scan.cleaned.slice(
    scan.conclusionStart,
    scan.conclusionEnd < 0 ? undefined : scan.conclusionEnd,
  );
  if (!goal.trim()) return null;

  // A goal's own leading `∀`/`premise →` prefix is as much a hypothesis of the
  // theorem as a binder group is, so it joins the shared rows; what remains is
  // the proposition that may split into conjuncts.
  const outer = liftTelescope(goal, 0);
  sharedHyps.push(...outer.hyps);

  const conclusions: ConclusionCard[] = [];
  const recons: string[] = [];
  for (const c of conjunctsOf(outer.inner) ?? [outer.inner]) {
    const built = buildCard(c, 0);
    if (!built) return null;
    conclusions.push(built.card);
    recons.push(built.recon);
  }
  if (conclusions.length === 0) return null;

  // Nothing may be dropped. Rebuild the signature from exactly the pieces the
  // view will render — recursively, through every nested card — and require it
  // to match the source token for token; a structured view that silently loses
  // a conjunct or a binder is worse than no structured view at all.
  const rebuilt = scan.groups.map((g) => g.raw).join("") + scan.goalPrefix + outer.prefix + recons.join("∧") + outer.suffix;
  const original = scan.cleaned.slice(
    scan.telescopeStart,
    scan.conclusionEnd < 0 ? undefined : scan.conclusionEnd,
  );
  if (squash(rebuilt) !== squash(original)) return null;
  const view = { sharedHyps, conclusions };
  markCitedHyps(allHypRows(view), citedNames);
  return view;
}

/**
 * What the shared table stores for a declaration.
 *
 * The drawer's job is a CHECKABLE STATEMENT, so a theorem/lemma keeps its
 * docstring and signature through the goal and drops the proof: the proofs of
 * helpers a reader was pulled into are noise, the verification badges already
 * say they went through, and each row carries file+line to the real source. A
 * `def`/`abbrev`/`structure`/`instance`/`inductive` keeps its whole source,
 * because there the body IS the statement.
 */

// ---------------------------------------------------------------------------
// row identity (added for the P4 artifact; not part of the ported code)

/** Every addressable row of a structured view, in READING order: shared
 *  hypotheses first, then each conclusion card's own hypotheses and its content
 *  row (its `intro` when it nests, its `code` when it is a leaf), depth-first.
 *  Stamps `id` in place and returns the rows in the same order. */
export type RowKind = "hyp" | "conclusion" | "param" | "def" | "value";

export function assignRowIds(view: StructuredView): Array<{ id: string; kind: RowKind; code: string }> {
  const out: Array<{ id: string; kind: RowKind; code: string }> = [];
  let n = 0;
  const next = () => `r${++n}`;
  // A definition's rows are named for what they are — parameters, the def row,
  // its value clauses — so the assignment prompt reads them correctly; a
  // theorem's keep hypothesis / conclusion.
  const isDef = view.defRow !== undefined;
  const hypKind: RowKind = isDef ? "param" : "hyp";
  const clauseKind: RowKind = isDef ? "value" : "conclusion";
  const hyp = (row: HypRow) => {
    // TheoremChecker: a premise cut into rows of its own is those rows (after its head line, for a
    // named one whose head states something)
    if (row.sub) {
      if (row.head && !bareHead(row.head)) {
        row.id = next();
        out.push({ id: row.id, kind: hypKind, code: row.head });
      }
      for (const c of row.sub) walk(c);
      return;
    }
    row.id = next();
    out.push({ id: row.id, kind: hypKind, code: row.code });
  };
  const walk = (card: ConclusionCard) => {
    for (const h of card.hyps) hyp(h);
    // A purely BRANCHING card — one that only splits into `sub`, with neither an
    // `intro` nor a `code` of its own — has no content row for the renderer to
    // draw, so giving it an id would invent a row nothing can highlight.
    const content = card.intro ?? card.code;
    if (content !== undefined && content.length > 0) {
      card.id = next();
      out.push({ id: card.id, kind: clauseKind, code: content });
    }
    for (const c of card.sub ?? []) walk(c);
  };
  for (const h of view.sharedHyps) hyp(h);
  if (view.defRow) {
    view.defRow.id = next();
    out.push({ id: view.defRow.id, kind: "def", code: view.defRow.code ?? "" });
  }
  for (const c of view.conclusions) walk(c);
  return out;
}


// ---------------------------------------------------------------------------
// definitions: parameters · def · given by
// ---------------------------------------------------------------------------

/** A `def`/`abbrev` head (past docstring/attributes/modifiers). */
export function isDefinitionLike(statement: string): boolean {
  const head = statement
    .replace(/\/--[\s\S]*?-\/|\/-[\s\S]*?-\//g, " ")
    // leading `-- …` line comments (`-- @realizes …` markers) precede many
    // composite components' declarations
    .replace(/^(?:\s*--[^\n]*\n)+/, "")
    .replace(/@\[[^\]]*\]/g, " ")
    .trimStart();
  return new RegExp(String.raw`^(?:(?:${LEAN_DECL_MODIFIERS})\s+)*(def|abbrev)\b`).test(head);
}

/** Explicit binder names of a telescope, in order (`(x y : T)` → x, y). */
function explicitNames(groups: readonly { raw: string }[]): string[] {
  const out: string[] = [];
  for (const g of groups) {
    if (g.raw[0] !== "(") continue;
    const inner = g.raw.slice(1, -1);
    const colon = topLevelColonIndex(inner);
    const names = (colon >= 0 ? inner.slice(0, colon) : inner).trim();
    if (names) out.push(...names.split(/\s+/).filter(Boolean));
  }
  return out;
}

/**
 * A definition as shared parameter rows, a `def` row (the declaration applied
 * to its explicit parameters, with its type), and given-by clause(s):
 *
 *   `:= v`            a leading run of `let` steps becomes rows on the clause,
 *                     the final expression its leaf; anything else one leaf;
 *   `| pat => v`      one leaf per equation alternative;
 *   `where …`         one leaf holding the block;
 *   `def … : Prop`    the proposition split exactly as a theorem's goal is
 *                     (`structureStatementView`), plus the `def` row.
 *
 * `result` (the index's elaborated result type) fills the type of an
 * unannotated `abbrev Foo (V) := …`. Returns `null` — the caller shows the raw
 * source — when the head is not confidently parsed or a split would lose text.
 */
export function structureDefinitionView(rawSource: string, result = ""): StructuredView | null {
  const def = scanDefinitionSignature(rawSource);
  if (!def) return null;
  const leaf = def.name.split(".").pop() ?? def.name;
  const head = [leaf, ...explicitNames(def.scan.groups)].join(" ");
  const propView = scanPropDefinitionSignature(rawSource) ? structureStatementView(rawSource) : null;
  if (propView) {
    return { ...propView, defRow: { hyps: [], code: `${head} : Prop` } };
  }
  const sharedHyps: HypRow[] = [];
  for (const g of def.scan.groups) {
    const parsed = parseBinderGroup(g.raw);
    if (!parsed) return null;
    sharedHyps.push({ chip: parsed.chip, code: dedent(g.raw) });
  }
  const type = def.scan.conclusionText || result;
  const defRow: ConclusionCard = { hyps: [], code: type ? `${head} : ${dedent(type)}` : head };
  const conclusions: ConclusionCard[] = [];
  if (def.body?.kind === "value") {
    const lets = stripLetRun(def.body.text);
    if (lets && squash(lets.prefix + lets.rest) === squash(def.body.text)) {
      conclusions.push({ hyps: lets.rows, code: dedent(lets.rest) });
    } else {
      conclusions.push({ hyps: [], code: dedent(def.body.text) });
    }
  } else if (def.body?.kind === "alternatives") {
    const alts: string[] = [];
    for (const line of dedent(def.body.text).split("\n")) {
      if (/^\s*\|/.test(line) || alts.length === 0) alts.push(line.trim());
      else alts[alts.length - 1] += " " + line.trim();
    }
    if (squash(alts.join("")) !== squash(def.body.text)) return null;
    for (const a of alts) conclusions.push({ hyps: [], code: a });
  } else if (def.body?.kind === "where") {
    const fields = splitWhereFields(def.body.text);
    if (fields) for (const f of fields) conclusions.push({ hyps: [], code: `${f.head} := ${f.value}` });
    else conclusions.push({ hyps: [], code: dedent(def.body.text) });
  }
  return { sharedHyps, conclusions, defRow };
}

/** A `structure`/`class` head (past docstring/attributes/modifiers). */
export function isRecordLike(statement: string): boolean {
  const head = statement
    .replace(/\/--[\s\S]*?-\/|\/-[\s\S]*?-\//g, " ")
    // leading `-- …` line comments (`-- @realizes …` markers) precede many
    // composite components' declarations
    .replace(/^(?:\s*--[^\n]*\n)+/, "")
    .replace(/@\[[^\]]*\]/g, " ")
    .trimStart();
  return new RegExp(String.raw`^(?:(?:${LEAN_DECL_MODIFIERS})\s+)*(structure|class)\b`).test(head);
}
