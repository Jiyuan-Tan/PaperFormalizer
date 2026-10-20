/**
 * V1 transcription lint — the deterministic check that the core builder TRANSCRIBED the
 * paper rather than restated it.
 *
 * The structural gate (`runStructuralGate`) checks that a core is well-formed; it knows
 * nothing about the paper the core came from. This lint is the other half: it binds every
 * node back to the LaTeX environment it claims to transcribe, through the node's
 * `tex_locator`, and refuses a core that paraphrases a statement, loses a proof, invents a
 * hypothesis that is not in the source text, or reaches outside the extraction scope.
 *
 * The rules, reported with their letter so a violation string tells the agent exactly
 * which contract it broke:
 *
 *   (a) every in-scope theorem-like env ↦ exactly one statement node at its `lines`, and
 *       every non-cited statement node sits at some such locator (a statement parked at a
 *       definition env or at a proof is a violation, because it would otherwise escape
 *       every text check below). For that node: `statement` is the env body VERBATIM,
 *       optionally followed by ONE hypothesis list `[Hypotheses: ass:x, def:y]` whose ids
 *       all exist in the core and all appear in the node's `depends_on`; `kind` matches the
 *       env kind; `status` is `to-prove`; `proof_tex` equals the env's proof body when the
 *       paper gives one and is ABSENT when it does not. An env whose body normalizes to
 *       nothing fails here too — the verbatim rule would otherwise be vacuous;
 *   (b) every in-scope assumption env ↦ at least one assumption node; every assumption
 *       node's `condition` is a verbatim slice of the env text it points at (so an inline
 *       hypothesis lifted out of a theorem body points at the THEOREM's locator); the slice
 *       may not drop a negation / disjunction / scope word that governs it earlier in the
 *       same SENTENCE; and the nodes of one assumption ENV must together cover at least
 *       half of that env's text, so a multi-condition assumption cannot be transcribed by
 *       quoting only the convenient clause;
 *   (c) every in-scope definition / algorithm env ↦ at least one definition node (no text
 *       rule: a definition is restated as a construction);
 *   (d) every node — cited leaves included — carries a locator matching some env's `lines`
 *       or `proofLines`. For a cited leaf that is the env where the PAPER INVOKES it;
 *   (e) a `cited` node is exempt from (a)–(c) and always carries `source`; one that sits at a
 *       theorem-like env's own locator (the paper restates an imported result as a proof-less
 *       lemma) is also checked verbatim by (a), which requires the env to have no proof;
 *   (f) no node points outside the scope;
 *   (g) dependency edges vs. the source's `\ref` graph — WARNINGS ONLY, both ways. Whether a
 *       `\ref` is a hypothesis, a proof use or a mention is the referee's reading; it grades
 *       drift and states the edge as a mechanical fix. FORWARD: a referenced in-scope env whose
 *       nodes are not all in `depends_on` is reported. CONVERSE
 *       (warning only — papers invoke results in plain prose without `\ref`): an `ass:`
 *       dependency that the env neither states inline nor references is reported for the
 *       V1.5 referee to confirm;
 *   (h) in phase `v1`, no assumption may carry a `bookkeeping` tag: only the V1.5 referee
 *       adds bookkeeping conditions, and `added_by:"V1.5"` is a string the V1 agent can
 *       type. In phase `v1_5` the tag is honoured and exempts the node from (b) / (d);
 *   (m) every node's text (a statement without its hypothesis list, a proof, a condition, a
 *       construction) is a balanced TeX fragment (`tex_balance.ts`): no slice starts or ends
 *       inside math, a display or an environment.
 *
 * Comparison is up to `norm`: `\label{…}` removed (the parser leaves it in the body) and
 * whitespace collapsed. Nothing else is normalized — a changed symbol, a dropped clause or
 * a "clarified" quantifier is exactly what this lint exists to catch.
 */
import type { Core } from "../core/schema.js";
import { maskNonBoundaryPeriods } from "../shared/tex_text.js";
import { CORE_BEARING_KINDS, type EnvKind, type EnvsJson, type TexEnv } from "./types.js";
import { texBalanceProblems } from "./tex_balance.js";
import { mentionsSymbol, symbolPattern } from "./symbol_match.js";

/** Env kinds that must become a `statement` node. */
export const THEOREM_LIKE_KINDS: ReadonlySet<EnvKind> = new Set<EnvKind>([
  "theorem",
  "lemma",
  "proposition",
  "corollary",
]);

/**
 * Env kind → `StatementSchema.kind`. `STATEMENT_KINDS` has no `corollary`, so a corollary
 * is transcribed as a `theorem`: it is a delivered result of the paper, and `lemma` is the
 * one wrong answer — reachability keys on `kind`, unreferenced `kind:"lemma"` nodes are
 * orphan-pruned, and `CoreSchema` itself forbids a `thm:` id carrying `kind:"lemma"`.
 */
export const STATEMENT_KIND_OF_ENV: Readonly<
  Record<"theorem" | "lemma" | "proposition" | "corollary", "theorem" | "lemma" | "proposition">
> = {
  theorem: "theorem",
  lemma: "lemma",
  proposition: "proposition",
  corollary: "theorem",
};

/** Which half of the pipeline is running the lint. A `bookkeeping` assumption is a V1.5
 * artefact; in `v1` its presence is itself the violation (rule (h)). */
export interface TranscriptionLintOptions {
  phase: "v1" | "v1_5";
  /** `discovery/flat.tex` — the text a `prose` locator's node is checked against. */
  flatText?: string;
}

/** A locator for setup stated in running text rather than in an environment. */
export function isProseLocator(loc: { env: string } | undefined | null): boolean {
  return loc?.env === "prose";
}

/** Blocking `violations` and non-blocking `warnings`. A warning is an observation the V1.5
 * referee must settle against the paper — it never fails a V1 round. */
export interface TranscriptionLintResult {
  violations: string[];
  warnings: string[];
}

/**
 * The ONLY text that may follow the verbatim environment body in a `statement`: a list of
 * core node ids naming the hypotheses the theorem is stated under. Anything else — an extra
 * clause, a "clarified" quantifier, a negated conclusion — is a rule (a) violation.
 */
export const HYPOTHESIS_SUFFIX_RE =
  /^\[Hypotheses:\s*([a-z]+:[a-z0-9-]+)(\s*,\s*[a-z]+:[a-z0-9-]+)*\s*\]$/;

/**
 * Words that GOVERN what follows them in a sentence. A `condition` slice taken from after
 * one of these, without it, means something the paper never said ("We do not require that
 * X" sliced to "X"; "either X or Y" sliced to "X"; "for all t, X" is caught by the
 * quantifier entries). Longest / most specific first, so the message names the real token.
 */
const GOVERNING_TOKENS: ReadonlyArray<{ token: string; re: RegExp }> = [
  "neither",
  "never",
  "need not",
  "does not",
  "do not",
  "without",
  "unless",
  "fails",
  "rather than",
  "instead of",
  "nor",
  "not",
  "either",
  "or",
  "no",
].map((token) => ({ token, re: new RegExp(`\\b${token.replace(/ /g, "\\s+")}\\b`, "i") }));

/** True when `text` closes a bracket group (`)` `]` `}`) it did not open. */
function closesGroup(text: string): boolean {
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    const c = text[i]!;
    if (c === "\\") {
      i++;
      continue;
    }
    if (c === "(" || c === "[" || c === "{") depth++;
    else if (c === ")" || c === "]" || c === "}") {
      if (depth === 0) return true;
      depth--;
    }
  }
  return false;
}

/** An `other` env whose name reads as an algorithm/procedure: an estimator definition. */
export function isAlgorithmEnv(env: TexEnv): boolean {
  return env.kind === "other" && /algorithm/i.test(env.envName);
}

/** An `other` env whose name reads as an imported result: a `cited` leaf. */
export function isCitedEnv(env: TexEnv): boolean {
  return env.kind === "other" && /cited/i.test(env.envName);
}

/** Envs that must appear in the core: the core-bearing kinds plus the two `other`
 * conventions above. `remark` / `example` / every other `other` is context only. */
export function isCoreBearingEnv(env: TexEnv): boolean {
  return CORE_BEARING_KINDS.has(env.kind) || isAlgorithmEnv(env) || isCitedEnv(env);
}

/**
 * Does `body` INVOKE the result labelled `label` as a hypothesis, rather than merely mention
 * it? Invocation is read from the words around the `\ref`: "under", "assume/suppose …
 * hold(s)", "given", "satisf…", "impose", "maintain", or a "\ref … hold(s)" tail. A range
 * `\ref{a}–\ref{b}` counts for both ends.
 */


export function invokesRef(body: string, label: string): boolean {
  const esc = label.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const ref = `\\\\(?:[cC]ref|ref|autoref|Cref)\\*?\\s*\\{${esc}\\}`;
  const lead = `\\b(?:[Uu]nder|[Aa]ssum(?:e|ing)|[Ss]uppos(?:e|ing)|[Gg]iven|[Ii]mpos(?:e|ing)|[Mm]aintain(?:ing)?|[Ss]atisf(?:y|ies|ying)|[Ii]f|[Ww]hen(?:ever)?|[Pp]rovided|[Rr]equir(?:e|ing))\\b[^.;]{0,120}?${ref}`;
  const tail = `${ref}[^.;]{0,60}?\\b(?:holds?|is satisfied|are satisfied|be satisfied|is in force|are in force)\\b`;
  return new RegExp(lead).test(body) || new RegExp(tail).test(body);
}

/** Text as compared by this lint: `\label{…}` stripped, whitespace collapsed, trimmed. Every
 * text field is copied out of the source by the runner, so nothing else needs forgiving. */
export function norm(text: string): string {
  return text
    .replace(/\\label\s*\{[^{}]*\}/g, " ")
    .replace(/\s+/g, " ")
    .trim();
}

/** Sticky scanners of `sentenceSpans`. */
const WS = /\s*/y;
const TAG = /\\(?:notag|nonumber\b|label\s*\{[^{}]*\})/y;
const GAP = /\s+(?=[A-Z(\\$])/y;
const CAP = /\s+(?=[A-Z])/y;

/**
 * Sentence spans of `text`: the numbered sentences the transcriber and the referee prompts show, the
 * reference core's sentence sources resolve against, and the paper's units (`units.ts`) are cut from. Periods that cannot end a sentence (decimals, `i.i.d.`, `Thm.`) are masked;
 * a remaining period followed by whitespace and a capital / opener is a boundary — but NEVER inside
 * math: a display or math environment belongs to the sentence it is in. A period inside math ends a
 * sentence only when nothing but the math's own closers (`$`, `$$`, `\]`, `\)`, `\end{…}`, `\notag`)
 * follows it; the boundary then falls AFTER those closers, and only when a capital / opener follows
 * (a display followed by lowercase text continues the sentence). A display followed by a capital ends
 * its sentence even without a period, so a lead-in ("we have", "is") always keeps its display. A list's `\begin{…}` / `\end{…}` lie
 * between sentences (no sentence starts or ends inside a list's delimiters), and each `\item` starts
 * a sentence. Every span keeps its terminating period and closers; offsets are offsets into `text`.
 */
export function sentenceSpans(text: string): Array<{ start: number; end: number }> {
  const masked = maskNonBoundaryPeriods(text);
  const regions = texStructure(text);
  const inside = (r: TexStructure, p: number): boolean => r.start + r.openLen <= p && p < r.end - r.closeLen;
  const inMath = (p: number): boolean => regions.some((r) => r.math && inside(r, p));
  const skipWs = (p: number): number => {
    WS.lastIndex = p;
    return p + (WS.exec(text)?.[0].length ?? 0);
  };
  const trimBack = (p: number): number => {
    let e = p;
    while (e > 0 && /\s/.test(text[e - 1]!)) e -= 1;
    return e;
  };
  /** Sentence breaks: [end of the sentence before, start of the next]. */
  const breaks: Array<[number, number]> = [];
  for (let p = masked.indexOf("."); p >= 0; p = masked.indexOf(".", p + 1)) {
    const holding = regions.filter((r) => r.math && inside(r, p));
    const closed = new Set<TexStructure>();
    let q = p + 1;
    for (;;) {
      const w = skipWs(q);
      const r = holding.find((x) => !closed.has(x) && x.closeLen > 0 && x.end - x.closeLen === w);
      if (r) {
        closed.add(r);
        q = r.end;
        continue;
      }
      TAG.lastIndex = w;
      const tag = TAG.exec(text);
      if (tag && holding.some((x) => !closed.has(x))) {
        q = w + tag[0].length;
        continue;
      }
      break;
    }
    if (holding.some((x) => !closed.has(x))) continue;
    GAP.lastIndex = q;
    const gap = GAP.exec(text);
    if (gap) breaks.push([q, q + gap[0].length]);
  }
  // A display ends its sentence when a capital follows it, period or not ("we have $$ … $$ The
  // difference …"); lowercase text after it ("where …", "and …") continues the sentence.
  const outer = regions.filter((r) => r.math && !regions.some((o) => o !== r && o.math && o.start <= r.start && r.end <= o.end && (o.start < r.start || r.end < o.end)));
  for (const r of outer) {
    const display = r.kind === "env" || text.startsWith("$$", r.start) || text.startsWith("\\[", r.start);
    if (!display || r.closeLen === 0) continue;
    CAP.lastIndex = r.end;
    const gap = CAP.exec(text);
    if (gap) breaks.push([r.end, r.end + gap[0].length]);
  }
  // A list's `\begin` / `\end` lie between sentences; each of its `\item`s starts one.
  const lists = regions.filter((r) => r.kind === "env" && !r.math && /\\item\b/.test(text.slice(r.start + r.openLen, r.end - r.closeLen)));
  for (const r of lists) {
    let open = r.start + r.openLen;
    const arg = /^\s*(?:\[[^\]]*\]|\{[^{}]*\})/.exec(text.slice(open));
    if (arg) open += arg[0].length;
    breaks.push([trimBack(r.start), skipWs(open)]);
    if (r.closeLen > 0) breaks.push([trimBack(r.end - r.closeLen), skipWs(r.end)]);
  }
  for (const m of text.matchAll(/\\item\b/g)) {
    const t = m.index!;
    if (inMath(t)) continue;
    const list = regions.filter((r) => r.kind === "env" && inside(r, t)).sort((a, b) => b.start - a.start)[0];
    if (list && lists.includes(list)) breaks.push([trimBack(t), t]);
  }
  const spans: Array<{ start: number; end: number }> = [];
  let start = 0;
  for (const [end, next] of breaks.sort((x, y) => x[0] - y[0] || x[1] - y[1])) {
    if (end <= start) {
      start = Math.max(start, next);
      continue;
    }
    spans.push({ start, end });
    start = next;
  }
  spans.push({ start, end: text.length });
  return spans.filter((sp) => sp.end > sp.start && text.slice(sp.start, sp.end).trim().length > 0);
}

/** A delimited region of TeX: math (`$…$`, `$$…$$`, `\(…\)`, `\[…\]`, a math environment, and
 * anything nested in one: `math`) or another environment (`env`). `openLen` / `closeLen`: the
 * delimiters' lengths (`closeLen` 0 when the text ends before the region closes). */
export interface TexStructure {
  start: number;
  end: number;
  openLen: number;
  closeLen: number;
  kind: "math" | "env";
  math: boolean;
}

const MATH_ENV_NAME = /^(?:equation|align|alignat|flalign|xalignat|gather|multline|eqnarray|displaymath|math|dmath|dseries|dgroup|IEEEeqnarray|IEEEeqnarraybox|split|aligned|gathered|cases)\*?$/;

/** The math regions and environments of a TeX text (comments skipped; an inline `$` whose partner
 * lies past a blank line is not math — TeX forbids a paragraph break there). Pure. */
export function texStructure(text: string): TexStructure[] {
  const out: TexStructure[] = [];
  type Open = { start: number; openLen: number; close: string; kind: "math" | "env"; math: boolean };
  const stack: Open[] = [];
  const inMath = (): boolean => stack.some((o) => o.math);
  const closeTop = (k: number, end: number, closeLen: number): void => {
    const o = stack[k]!;
    out.push({ start: o.start, end, openLen: o.openLen, closeLen, kind: o.kind, math: o.math });
    stack.length = k;
  };
  for (let i = 0; i < text.length; i += 1) {
    const c = text[i]!;
    if (c === "%") {
      const nl = text.indexOf("\n", i);
      i = nl < 0 ? text.length : nl;
      continue;
    }
    if (c === "\\") {
      const n = text[i + 1];
      if ((n === "(" || n === "[") && !inMath()) {
        stack.push({ start: i, openLen: 2, close: n === "(" ? "\\)" : "\\]", kind: "math", math: true });
        i += 1;
        continue;
      }
      if (n === ")" || n === "]") {
        const k = stack.length - 1;
        if (k >= 0 && stack[k]!.close === `\\${n}`) closeTop(k, i + 2, 2);
        i += 1;
        continue;
      }
      const be = /^\\(begin|end)\s*\{([^{}]*)\}/.exec(text.slice(i, i + 80));
      if (be) {
        const name = be[2]!.trim();
        if (be[1] === "begin") stack.push({ start: i, openLen: be[0].length, close: `env:${name}`, kind: "env", math: inMath() || MATH_ENV_NAME.test(name) });
        else {
          for (let k = stack.length - 1; k >= 0; k -= 1) {
            if (stack[k]!.close !== `env:${name}`) continue;
            // anything left open inside closes with it
            for (let j = stack.length - 1; j > k; j -= 1) closeTop(j, i, 0);
            closeTop(k, i + be[0].length, be[0].length);
            break;
          }
        }
        i += be[0].length - 1;
        continue;
      }
      i += 1; // an escaped character or a control word's first letter
      continue;
    }
    if (c === "$") {
      const k = stack.length - 1;
      const top = stack[k];
      if (top?.close === "$") {
        closeTop(k, i + 1, 1); // `$a$$b$`: two inline formulas
        continue;
      }
      const dbl = text[i + 1] === "$";
      if (top && top.close === (dbl ? "$$" : "$")) closeTop(k, i + (dbl ? 2 : 1), dbl ? 2 : 1);
      else if (!inMath()) {
        if (dbl) stack.push({ start: i, openLen: 2, close: "$$", kind: "math", math: true });
        else {
          let j = i + 1;
          for (; j < text.length; j += 1) {
            if (text[j] === "\\") j += 1;
            else if (text[j] === "$") break;
          }
          if (j < text.length && !/\n[^\S\n]*\n/.test(text.slice(i, j))) stack.push({ start: i, openLen: 1, close: "$", kind: "math", math: true });
        }
      }
      if (dbl) i += 1;
    }
  }
  for (let k = stack.length - 1; k >= 0; k -= 1) closeTop(k, text.length, 0);
  return out.sort((a, b) => a.start - b.start);
}

/** Identity of a source region: file + line span. `env` / `label` are descriptive. */
export function locatorKey(loc: { file: string; from: number; to: number }): string {
  return `${loc.file}:${loc.from}-${loc.to}`;
}

/** Where two normalized texts first part ways — the one thing a builder needs to fix a
 * verbatim violation, and the one thing a prefix excerpt never shows. */
export function divergence(expected: string, got: string): string {
  let i = 0;
  while (i < expected.length && i < got.length && expected[i] === got[i]) i += 1;
  const around = (t: string): string => `${t.slice(Math.max(0, i - 60), i)}⟨HERE⟩${t.slice(i, i + 60)}`;
  return (
    `first difference at character ${i}: expected …${around(expected)}… — got …${around(got)}…` +
    ` (expected, as a JSON string: ${JSON.stringify(expected.slice(Math.max(0, i - 20), i + 40))})`
  );
}

/** Divergence for a "must be a substring" rule: anchor on the needle's first 30 characters
 * inside the haystack, then diff from there. */
export function substringDivergence(haystack: string, needle: string): string {
  const anchor = needle.slice(0, 30);
  const at = anchor.length >= 10 ? haystack.indexOf(anchor) : -1;
  if (at < 0) return `no 30-character prefix of the quoted text occurs in the source — the quote does not start where the source does`;
  return divergence(haystack.slice(at, at + needle.length + 60), needle);
}

const REF_LABEL_RE = /\\(?:eq|c|C|auto|name|page)?ref\*?\s*\{([^{}]*)\}/g;

/** Labels a text refers to (`\ref`, `\eqref`, `\cref{a,b}`). */
export function refLabels(text: string): string[] {
  const out: string[] = [];
  for (const m of text.matchAll(REF_LABEL_RE)) for (const l of m[1]!.split(",")) if (l.trim() && !out.includes(l.trim())) out.push(l.trim());
  return out;
}


function excerpt(text: string, max = 160): string {
  return text.length <= max ? text : `${text.slice(0, max)}…`;
}

/** Total length covered by a set of possibly overlapping [start, end) intervals. */
function unionLength(intervals: ReadonlyArray<{ start: number; end: number }>): number {
  const sorted = [...intervals].sort((x, y) => x.start - y.start);
  let total = 0;
  let cursor = -1;
  for (const iv of sorted) {
    const from = Math.max(iv.start, cursor);
    if (iv.end > from) {
      total += iv.end - from;
      cursor = iv.end;
    }
  }
  return total;
}

/**
 * Check `core` against the environments it was transcribed from. Returns one string per
 * violation (each naming the rule letter and the env / node it is about) plus the
 * non-blocking warnings the V1.5 referee must settle; empty `violations` is a pass. `scope`
 * is the list of env ids V1 asked the builder to transcribe.
 */
export function lintTranscription(
  core: Core,
  envs: EnvsJson,
  scope: readonly string[],
  options: TranscriptionLintOptions,
): TranscriptionLintResult {
  const out: string[] = [];
  const warnings: string[] = [];
  const scopeIds = new Set(scope);
  const byId = new Map(envs.envs.map((e) => [e.id, e] as const));
  const byLabel = new Map(
    envs.envs.filter((e) => e.label !== null).map((e) => [e.label as string, e] as const),
  );

  // A scope id that names no env is a caller bug, not an agent one — report it rather
  // than silently checking a smaller scope.
  for (const id of scope) {
    if (!byId.has(id)) out.push(`(scope) ${id}: not an environment in envs.json`);
  }

  // Locator → the env that owns that source region. An env owns both its own `lines` and,
  // when the paper proves it elsewhere, its `proofLines` (a node lifted out of a proof is
  // attributed to the env that proof belongs to).
  const ownerByLocator = new Map<string, { env: TexEnv; region: "body" | "proof" }>();
  for (const env of envs.envs) {
    ownerByLocator.set(locatorKey(env.lines), { env, region: "body" });
    if (env.proofLines) {
      const key = locatorKey(env.proofLines);
      if (!ownerByLocator.has(key)) ownerByLocator.set(key, { env, region: "proof" });
    }
  }

  const statementsAt = (key: string) =>
    core.statements.filter((s) => s.tex_locator && locatorKey(s.tex_locator) === key);
  const assumptionsAt = (key: string) =>
    core.assumptions.filter((a) => a.tex_locator && locatorKey(a.tex_locator) === key);
  const definitionsAt = (key: string) =>
    core.definitions.filter((d) => d.tex_locator && locatorKey(d.tex_locator) === key);
  /** Every core node transcribed from one source region — what a `\ref` to it demands. */
  const nodeIdsAt = (key: string): string[] => [
    ...assumptionsAt(key).map((a) => a.id),
    ...definitionsAt(key).map((d) => d.id),
    ...statementsAt(key).map((s) => s.id),
  ];
  const assumptionById = new Map(core.assumptions.map((a) => [a.id, a] as const));
  const envNames = new Set(envs.envs.map((e) => e.envName));
  const definitionIds = new Set(core.definitions.map((d) => d.id));

  // (h) A bookkeeping assumption is V1.5's to add. `added_by:"V1.5"` is a string the V1
  // agent can type, so the PHASE — not the tag — is what decides whether it is legitimate.
  const bookkeepingIsLegal = options.phase === "v1_5";
  if (!bookkeepingIsLegal) {
    for (const a of core.assumptions) {
      if (a.bookkeeping) {
        out.push(
          `(h) ${a.id}: carries a \`bookkeeping\` tag — only V1.5 may add bookkeeping assumptions. ` +
            `Transcribe the paper's own conditions, or leave the gap for the referee.`,
        );
      }
    }
  }
  /** Bookkeeping nodes are exempt from the source rules ONLY once V1.5 owns them. */
  const isExempt = (a: { bookkeeping?: unknown }): boolean =>
    bookkeepingIsLegal && a.bookkeeping !== undefined;

  // (a) theorem-like envs.
  const theoremLikeBodyKeys = new Set<string>();
  for (const id of scope) {
    const env = byId.get(id);
    if (!env || !THEOREM_LIKE_KINDS.has(env.kind)) continue;
    const key = locatorKey(env.lines);
    theoremLikeBodyKeys.add(key);
    const nodes = statementsAt(key);
    if (nodes.length === 0) {
      out.push(`(a) ${id}: expected a statement node with tex_locator ${key}, found none`);
      continue;
    }
    // One printed result, one node: its cases, clauses and alternative hypothesis sets stay in
    // its own words, never split into several nodes.
    if (nodes.length > 1) {
      out.push(
        `(a) ${id}: found ${nodes.length} statement nodes at one environment (${nodes.map((n) => n.id).join(", ")}) ` +
          `— one result, one node: transcribe the whole body once, wired to every hypothesis any of its cases or clauses uses`,
      );
      continue;
    }
    const node = nodes[0]!;
    const wantKind = STATEMENT_KIND_OF_ENV[env.kind as keyof typeof STATEMENT_KIND_OF_ENV];
    if (node.kind !== wantKind) {
      out.push(
        `(a) ${id} -> ${node.id}: kind '${node.kind}' must be '${wantKind}' for a ${env.kind} environment`,
      );
    }
    // A theorem-like env the paper states WITHOUT a proof may be a result it imports and
    // restates ("Lemma (Berry–Esseen) [cite] …"): that node is a cited leaf, and its
    // statement is still checked verbatim against the env below. An env the paper proves
    // is the paper's own result and is never cited.
    if (node.status === "cited") {
      if (env.proof !== null) {
        out.push(
          `(a) ${id} -> ${node.id}: status 'cited' but the paper PROVES this environment ` +
            `(proof at ${env.proofLines ? locatorKey(env.proofLines) : "?"}) — a proved result is "to-prove"`,
        );
      }
    } else if (node.status !== "to-prove") {
      out.push(
        `(a) ${id} -> ${node.id}: status '${node.status}' must be "to-prove" — V1 never marks the paper's own result proved`,
      );
    }
    const body = norm(env.body);
    const statement = norm(node.statement);
    if (body.length === 0) {
      // Without this the verbatim rule below is vacuous: every string starts with "".
      out.push(
        `(a) ${id}: environment has no statement text; check the source ` +
          `(a label-only environment cannot be transcribed, and nothing the node says can be checked against it)`,
      );
    } else if (!statement.startsWith(body)) {
      out.push(
        `(a) ${id} -> ${node.id}: \`statement\` does not BEGIN with the environment body verbatim ` +
          `(the materialized text diverges from the environment; only a hypothesis list may follow it). ${divergence(body, statement)}`,
      );
    } else {
      // The suffix is the ONLY place a builder can append text, so it is grammar-checked
      // rather than merely allowed to exist.
      const suffix = statement.slice(body.length).trim();
      if (suffix.length > 0 && !HYPOTHESIS_SUFFIX_RE.test(suffix)) {
        out.push(
          `(a) ${id} -> ${node.id}: the only text that may follow the environment body is a hypothesis ` +
            `list of core node ids, spelled exactly \`[Hypotheses: ass:x, def:y]\` — got: "${excerpt(suffix)}"`,
        );
      } else if (suffix.length > 0) {
        const inner = /^\[Hypotheses:\s*([\s\S]*?)\s*\]$/.exec(suffix)?.[1] ?? "";
        const deps = new Set(node.depends_on);
        for (const listed of inner.split(/\s*,\s*/).filter((x) => x.length > 0)) {
          if (!assumptionById.has(listed) && !definitionIds.has(listed)) {
            out.push(
              `(a) ${id} -> ${node.id}: the hypothesis list names '${listed}', which is not an ` +
                `\`ass:\`/\`def:\` node of this core`,
            );
          } else if (!deps.has(listed)) {
            out.push(
              `(a) ${id} -> ${node.id}: the hypothesis list names '${listed}', which is missing from ` +
                `\`depends_on\` — a listed hypothesis must also be a declared dependency`,
            );
          }
        }
      }
    }
    if (env.proof !== null) {
      const want = norm(env.proof);
      const got = norm(node.proof_tex ?? "");
      if (got !== want) {
        out.push(
          `(a) ${id} -> ${node.id}: \`proof_tex\` must equal the environment's proof body verbatim. ` +
            `expected: "${excerpt(want)}" — got: "${excerpt(got)}"`,
        );
      }
    } else if ((node.proof_tex ?? "").trim().length > 0) {
      // The paper gives no proof for this environment, so any proof text is the agent's own.
      out.push(
        `(a) ${id} -> ${node.id}: the environment has NO proof in the source, so \`proof_tex\` must be ` +
          `absent — V1 transcribes, it never writes a proof. got: "${excerpt(norm(node.proof_tex ?? ""))}"`,
      );
    }
  }
  // Every transcribed statement must sit at one of those locators. A statement parked at a
  // definition env's or a proof's locator would otherwise never be compared with any text.
  for (const s of core.statements) {
    if (s.status === "cited" || !s.tex_locator) continue; // (d)/(e) own those
    const key = locatorKey(s.tex_locator);
    if (theoremLikeBodyKeys.has(key)) continue;
    const owner = ownerByLocator.get(key);
    const where = owner ? `${owner.env.id}'s ${owner.region}` : "no environment";
    out.push(
      `(a) ${s.id}: tex_locator ${key} (${where}) is not the \`lines\` of an in-scope theorem-like ` +
        `environment — a statement node must sit at the theorem / lemma / proposition / corollary it transcribes`,
    );
  }

  // (p) prose nodes: a `def:`/`ass:` node may point at running text instead of an
  // environment (a symbol's definition, a standing convention, a section-level premise).
  // Its text must still be a verbatim slice — of the flattened paper. A statement never is
  // prose: results live in environments.
  const flatNorm = options.flatText === undefined ? null : norm(options.flatText);
  const proseNodes: Array<{ id: string; text: string; kind: string }> = [
    ...core.assumptions
      .filter((a) => isProseLocator(a.tex_locator))
      .map((a) => ({ id: a.id, text: a.condition, kind: "assumption" })),
    ...core.definitions
      .filter((d) => isProseLocator(d.tex_locator))
      .map((d) => ({ id: d.id, text: d.construction, kind: "definition" })),
  ];
  for (const s of core.statements) {
    if (isProseLocator(s.tex_locator)) {
      out.push(`(p) ${s.id}: a statement may not carry a \`prose\` locator — results are transcribed from their environments`);
    }
  }
  for (const node of proseNodes) {
    if (flatNorm === null) {
      out.push(`(p) ${node.id}: prose locator but the runner supplied no flattened text to check it against`);
      continue;
    }
    const text = norm(node.text);
    // Running text stops where an environment begins: a slice that runs into a theorem or
    // assumption is two sources spliced together, whatever the paper says next.
    const crossed = /\\begin\s*\{([^{}]+)\}/.exec(node.text);
    if (crossed && envNames.has(crossed[1]!.trim())) {
      out.push(
        `(p) ${node.id}: the ${node.kind} text runs into \\begin{${crossed[1]!.trim()}} — a prose slice ends where an ` +
          `environment begins; transcribe that environment as its own node`,
      );
      continue;
    }
    if (text.length === 0 || !flatNorm.includes(text)) {
      out.push(
        `(p) ${node.id}: the ${node.kind} text is not a verbatim slice of the paper's running text ` +
          `— quote the sentence the paper writes, do not restate it. ${substringDivergence(flatNorm, text)}`,
      );
    }
  }

  // (b) assumption envs, and the slice rules on every assumption node.
  for (const id of scope) {
    const env = byId.get(id);
    if (!env || env.kind !== "assumption") continue;
    const key = locatorKey(env.lines);
    if (assumptionsAt(key).length === 0) {
      out.push(`(b) ${id}: no assumption node carries this environment's locator ${key}`);
    }
  }
  /** First occurrence of each node's condition inside its env text, for the coverage rule. */
  const sliceOf = new Map<string, { start: number; end: number }>();
  for (const assumption of core.assumptions) {
    if (isExempt(assumption)) continue; // supplied by V1.5, has no source env
    if (assumption.bookkeeping) continue; // already reported by (h) in phase v1
    if (!assumption.tex_locator) continue; // reported by (d)
    if (isProseLocator(assumption.tex_locator)) continue; // (p) owns those
    const owner = ownerByLocator.get(locatorKey(assumption.tex_locator));
    if (!owner) continue; // reported by (d)
    const source = norm(owner.region === "body" ? owner.env.body : (owner.env.proof ?? ""));
    const condition = norm(assumption.condition);
    const at = source.indexOf(condition);
    if (at < 0) {
      out.push(
        `(b) ${assumption.id}: \`condition\` is not a verbatim substring of ${owner.env.id}'s ` +
          `${owner.region} text at ${locatorKey(assumption.tex_locator)} (the materialized text is not a slice of the environment). ` +
          `${substringDivergence(source, condition)}`,
      );
      continue;
    }
    sliceOf.set(assumption.id, { start: at, end: at + condition.length });
    // A verbatim slice can still LIE, by leaving behind the word that governs it: the
    // negation, the disjunction or the quantifier earlier in the same sentence.
    const span =
      sentenceSpans(source).find((s) => at >= s.start && at < s.end) ??
      { start: 0, end: source.length };
    const before = source.slice(span.start, at);
    // Adjacent only: a token in a DIFFERENT clause of the sentence ("continuous or piecewise
    // continuous, and $\sigma^2<\infty$"; "There is no interference: $Y_i(d)=Y_i(d_i)$") does
    // not govern the slice. A clause break (`,` `;` `:` or the word "and") between the token
    // and the slice start clears it. So does a group closing between them: a token inside a
    // bracketed title or aside ("{\sc (No Testable Restrictions)} Suppose …") governs only the
    // group it sits in.
    const governing = GOVERNING_TOKENS.find((t) =>
      [...before.matchAll(new RegExp(t.re.source, "gi"))].some((m) => {
        const between = before.slice(m.index + m[0].length);
        return !/[,;:]|\band\b/i.test(between) && !closesGroup(between);
      }),
    );
    if (governing) {
      out.push(
        `(b) ${assumption.id}: the slice starts AFTER '${governing.token}' in "${excerpt(source.slice(span.start, span.end))}" ` +
          `— transcribe the whole clause, a slice that drops the word governing it states something the paper does not. ` +
          `condition: "${excerpt(condition)}"`,
      );
    }
  }
  // An assumption ENV states conditions; quoting only the convenient one silently drops
  // the rest, and every dropped condition weakens the hypothesis of every theorem using it.
  for (const id of scope) {
    const env = byId.get(id);
    if (!env || env.kind !== "assumption") continue;
    const key = locatorKey(env.lines);
    const nodes = assumptionsAt(key).filter((a) => !isExempt(a) && !a.bookkeeping);
    if (nodes.length === 0) continue; // already reported above
    const body = norm(env.body);
    if (body.length === 0) continue;
    const covered = unionLength(nodes.flatMap((a) => {
      const slice = sliceOf.get(a.id);
      return slice ? [slice] : [];
    }));
    // A WARNING, not a violation: assumption environments routinely end with an explanatory
    // remark that must NOT become a hypothesis, so low coverage is for the V1.5 referee to
    // settle (did a condition go missing, or is the rest commentary?).
    if (covered * 2 < body.length) {
      const pct = Math.round((covered / body.length) * 100);
      warnings.push(
        `${id}: the assumption node(s) at ${key} (${nodes.map((a) => a.id).join(", ")}) quote only ` +
          `${pct}% of the environment's text; V1.5 must confirm the rest is commentary, not a dropped condition. ` +
          `environment: "${excerpt(body)}"`,
      );
    }
  }

  // (c) definition / algorithm envs.
  for (const id of scope) {
    const env = byId.get(id);
    if (!env || !(env.kind === "definition" || isAlgorithmEnv(env))) continue;
    const key = locatorKey(env.lines);
    if (definitionsAt(key).length === 0) {
      out.push(`(c) ${id}: no definition node carries this environment's locator ${key}`);
    }
  }

  // (d) / (e) / (f) — every node's locator resolves to an env, and that env is in scope.
  // A cited leaf is exempt from the TEXT rules (a)–(c), never from the locator rules: its
  // locator is the environment where the PAPER invokes it, which is what stops a fabricated
  // leaf with a real bibkey from handing a theorem its conclusion.
  const nodes: Array<{
    id: string;
    locator?: { file: string; from: number; to: number; env: string };
    cited: boolean;
    hasSource: boolean;
    exempt: boolean;
  }> = [
    ...core.assumptions.map((a) => ({
      id: a.id,
      locator: a.tex_locator,
      cited: false,
      hasSource: true,
      exempt: isExempt(a) || a.bookkeeping !== undefined,
    })),
    ...core.definitions.map((d) => ({
      id: d.id,
      locator: d.tex_locator,
      cited: false,
      hasSource: true,
      exempt: false,
    })),
    ...core.statements.map((s) => ({
      id: s.id,
      locator: s.tex_locator,
      cited: s.status === "cited",
      hasSource: s.source !== undefined,
      exempt: false,
    })),
  ];
  for (const node of nodes) {
    if (node.cited && !node.hasSource) {
      out.push(`(e) ${node.id}: a \`cited\` node must carry \`source\` (bibkey + locator)`);
    }
    if (node.exempt) continue;
    if (isProseLocator(node.locator)) continue; // (p) owns those
    if (!node.locator) {
      out.push(
        `(d) ${node.id}: no \`tex_locator\` — every node must point at its source environment` +
          (node.cited ? " (for a cited leaf: the environment where THIS paper invokes it)" : ""),
      );
      continue;
    }
    const key = locatorKey(node.locator);
    const owner = ownerByLocator.get(key);
    if (!owner) {
      out.push(
        `(d) ${node.id}: tex_locator ${key} matches no environment's \`lines\` or \`proofLines\` in envs.json`,
      );
      continue;
    }
    if (!scopeIds.has(owner.env.id)) {
      out.push(
        `(f) ${node.id}: tex_locator ${key} points at ${owner.env.id}, which is OUTSIDE the extraction scope`,
      );
    }
  }

  // (r) a hypothesis that is only a pointer. "Suppose (3) holds" carries nothing a formalizer
  // can realize unless some node quotes the displayed equation (3) — its `\label` travels with
  // the verbatim quote, which is how we know it was transcribed.
  {
    // An environment's own label, and every label INSIDE its body (`\item \label{overlap}` in
    // an assumption's list): a `\ref` to either points at that environment, whose coverage
    // rules (a)/(b) already check — it is not a pointer to text nobody quoted.
    const envLabels = new Set(byLabel.keys());
    for (const e of envs.envs) for (const m of e.body.matchAll(/\\label\s*\{([^{}]*)\}/g)) envLabels.add(m[1]!.trim());
    const quoted = new Set<string>();
    const texts = [
      ...core.statements.map((n) => n.statement),
      ...core.assumptions.map((a) => a.condition),
      ...core.definitions.map((d) => d.construction),
    ];
    for (const t of texts) for (const m of t.matchAll(/\\label\s*\{([^{}]*)\}/g)) quoted.add(m[1]!.trim());
    const unresolved = (text: string): string[] =>
      refLabels(text).filter((l) => !envLabels.has(l) && !quoted.has(l) && !/^(?:sec|section|app|appendix|fig|figure|tab|table|foot|fn|alg|algorithm|ch|chap)[:_-]/i.test(l));
    for (const a of core.assumptions) {
      if (isExempt(a) || a.bookkeeping) continue;
      for (const l of unresolved(a.condition)) {
        out.push(
          `(r) ${a.id}: \`condition\` refers to \\ref{${l}}, which no core node quotes — transcribe the displayed ` +
            `equation or sentence it points to (with its \\label) as a prose assumption/definition, so the hypothesis is stated, not pointed at`,
        );
      }
    }
    // Labels of DISPLAYED equations in the paper: a result that points at one ("suppose (3)
    // holds", "where M is defined in (12)") needs that equation quoted as a prose node.
    const displayedLabels = new Set<string>();
    if (options.flatText) {
      for (const m of options.flatText.matchAll(/\\begin\s*\{(equation\*?|align\*?|gather\*?|multline\*?|eqnarray\*?|flalign\*?|alignat\*?)\}([\s\S]*?)\\end\s*\{\1\}/g)) {
        for (const l of m[2]!.matchAll(/\\label\s*\{([^{}]*)\}/g)) displayedLabels.add(l[1]!.trim());
      }
    }
    for (const n of core.statements) {
      if (n.status === "cited") continue;
      for (const l of unresolved(n.statement)) {
        const must = invokesRef(n.statement, l) || displayedLabels.has(l);
        (must ? out : warnings).push(
          `(r) ${n.id}: \`statement\` refers to \\ref{${l}}, which no core node quotes — ` +
            (invokesRef(n.statement, l)
              ? `it is invoked as a hypothesis, so quote what it states as a prose assumption`
              : displayedLabels.has(l)
                ? `it is a displayed equation the result relies on, so quote it (\\label included) as a prose definition or assumption`
                : `V1.5 must confirm the referenced object is defined somewhere in the core`),
        );
      }
    }
  }

  // (g) dependency edges vs. the source's `\ref` graph.
  for (const statement of core.statements) {
    if (statement.status === "cited" || !statement.tex_locator) continue;
    const owner = ownerByLocator.get(locatorKey(statement.tex_locator));
    if (!owner || owner.region !== "body") continue; // reported by (a)/(d)
    const env = owner.env;
    const deps = new Set(statement.depends_on);
    // FORWARD: what the paper points at, the node must depend on.
    for (const ref of env.refs) {
      const target = byLabel.get(ref);
      if (!target || target.id === env.id) continue;
      if (!scopeIds.has(target.id) || !isCoreBearingEnv(target)) continue;
      const missing = nodeIdsAt(locatorKey(target.lines)).filter((n) => n !== statement.id && !deps.has(n));
      // Which of a paper's `\ref`s are hypotheses, which are proof uses, and which are mere
      // mentions is the REFEREE's call: it reads the words, grades `drift`, and states the edge
      // to add or drop as a mechanical fix the runner applies. The lint only points.
      if (missing.length > 0) {
        warnings.push(
          `${statement.id}: ${env.id} references \\ref{${ref}} (${target.id}) but \`depends_on\` lacks ` +
            `${missing.join(", ")}; V1.5 must confirm whether the paper assumes it or merely mentions it`,
        );
      }
    }
    // CONVERSE: a dependency the environment never mentions. Papers invoke assumptions in
    // plain prose, so this is an observation for V1.5, never a blocking violation.
    const ownKeys = new Set([
      locatorKey(env.lines),
      ...(env.proofLines ? [locatorKey(env.proofLines)] : []),
    ]);
    for (const dep of statement.depends_on) {
      const a = assumptionById.get(dep);
      if (!a || a.bookkeeping || !a.tex_locator) continue; // (G4)/(h)/(d) own those
      if (isProseLocator(a.tex_locator)) continue; // standing setup is invoked without a \ref
      const depKey = locatorKey(a.tex_locator);
      if (ownKeys.has(depKey)) continue; // stated inline in this very environment
      const depOwner = ownerByLocator.get(depKey);
      if (depOwner?.env.label && env.refs.includes(depOwner.env.label)) continue;
      warnings.push(
        `${statement.id}: depends on ${dep} which the environment never references; ` +
          `V1.5 must confirm the paper actually assumes it`,
      );
    }
  }

  // (s) the symbol table and the settings, as the F stages read them: each symbol's carrier
  // (`space`) and meaning (`def`), and the sampling model they derive their worlds from.
  for (const sym of core.symbols) {
    const missing = (["space", "def"] as const).filter((k) => !sym[k]?.trim());
    if (missing.length > 0) out.push(`(s) symbol ${sym.name}: no ${missing.join(" and no ")}`);
    // `refs`: the other symbols its def names (in its mathematics); the order is the runner's
    // (`orderSymbolsByRefs`), and symbols naming each other list each other.
    const math = (sym.def ?? "").match(/\$[^$]*\$|\\\(.*?\\\)|\\\[.*?\\\]/gs)?.join(" ") ?? "";
    // The symbol's own name is not a use of the symbols written inside it (`Y(a)` names neither
    // `Y` nor `a`): a def that writes its own name must not be told to list them.
    const others = math.split(sym.name).join(" ");
    const named = core.symbols.filter((o) => o.name !== sym.name && mentionsSymbol(others, symbolPattern(o.name))).map((o) => o.name);
    const unlisted = named.filter((n) => !(sym.refs ?? []).includes(n));
    if (unlisted.length > 0) out.push(`(s) symbol ${sym.name}: its def names ${unlisted.join(", ")} — list ${unlisted.length > 1 ? "them" : "it"} in refs`);
  }
  if (!core.sampling_model || Object.keys(core.sampling_model).length === 0) out.push("(s) sampling_model: missing — one entry per setting the paper works in");

  // (m) whole TeX.
  out.push(...nodeBalanceViolations(core));

  return { violations: out, warnings };
}

/** A statement's text without the printed `[Hypotheses: …]` list the transcription appends. */
const withoutHypothesisList = (s: string): string => s.replace(/\s*\[Hypotheses:[^\]]*\]\s*$/u, "");

/**
 * Rule (m): every node's text — a statement (its printed hypothesis list aside), a proof, a
 * condition, a construction — is a balanced TeX fragment. A text that starts or ends inside a
 * display, a math span or an environment reaches the referee, the fixer and the renderer as a
 * fragment of the paper: a proof cut at a QED mark set inside its last display loses that display.
 */
export function nodeBalanceViolations(core: Core): string[] {
  const out: string[] = [];
  const check = (id: string, field: string, text: string | null | undefined): void => {
    if (!text) return;
    const probs = texBalanceProblems(text);
    if (probs.length === 0) return;
    out.push(
      `(m) ${id}: \`${field}\` is not a whole TeX fragment — ${probs.join("; ")}. A node's text never starts or ends ` +
        `inside math, a display or an environment: widen its range to the whole display (or narrow it to leave the display out)`,
    );
  };
  for (const s of core.statements) {
    check(s.id, "statement", withoutHypothesisList(s.statement));
    check(s.id, "proof_tex", s.proof_tex);
  }
  for (const a of core.assumptions) check(a.id, "condition", a.condition);
  for (const d of core.definitions) check(d.id, "construction", d.construction);
  return out;
}

/**
 * The in-scope environments whose parsed body or proof is not a balanced TeX fragment. The
 * parser, not the transcriber, produced such a text (`proof_tex` must equal the proof verbatim),
 * so no agent round can fix it: V1 refuses the transcription at a checkpoint instead.
 */
export function envBalanceProblems(envs: EnvsJson, scope: readonly string[]): string[] {
  const inScope = new Set(scope);
  const out: string[] = [];
  for (const e of envs.envs) {
    if (!inScope.has(e.id)) continue;
    for (const [field, text] of [["body", e.body], ["proof", e.proof]] as const) {
      if (!text) continue;
      const probs = texBalanceProblems(text);
      const loc = field === "proof" && e.proofLines ? e.proofLines : e.lines;
      if (probs.length > 0) out.push(`${e.id} ${field} (${loc.file}:${loc.from}-${loc.to}): ${probs.join("; ")}`);
    }
  }
  return out;
}
