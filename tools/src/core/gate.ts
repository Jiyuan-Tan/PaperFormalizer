// The typed-core structural gate.
//
// Mechanical, no LLM. Runs on the core the V1 transcription produces, so a whole class of
// structural defects never reaches an LLM reviewer. Checks G1–G7; returns every violation
// with its gate code + location.
import { CoreSchema } from "./schema.js";
import { normalizeSymbol } from "./symbol_names.js";
import { symbolRefsReach } from "./symbol_order.js";
import { hasPlausibleSentenceEnd, maskNonBoundaryPeriods } from "../shared/tex_text.js";

export interface GateViolation {
  code: "schema" | "G1" | "G2" | "G3" | "G4" | "G5" | "G6" | "G7";
  where: string;
  message: string;
}

export interface GateResult {
  ok: boolean;
  violations: GateViolation[];
  /** Verbatim mode only: observations for the referee that do not block (the paper's own
   * sentence structure is not the transcriber's to change). */
  notes?: GateViolation[];
}

export interface GateOptions {
  /** Every statement must be discharged (status === "proved"). The V1 transcription
   * leaves false: the paper's proofs are not re-derived at that point. */
  requireDischarged?: boolean;
  /** Allow `bookkeeping`-tagged assumptions (the V1.5 referee's silent side conditions). The
   * schema admits the tag as a fourth alternative of the G6 xor so a transcribed core parses;
   * the gate is the place the tag is licensed: false (the default) makes any `bookkeeping`
   * assumption a G6 violation; only the V1/V1.5 transcription passes true. */
  allowBookkeeping?: boolean;
  /** The conditions are verbatim slices of a source text (the V-stage transcription), not LLM-authored
   *  prose: the G2 banned-connective check ("moreover", "in addition", …) targets an author
   *  padding a condition and would only reject the paper's own words here. The one-relation
   *  (sentence-count) half of G2 still applies. */
  verbatim?: boolean;
}

// G2: an assumption.condition is a SINGLE pure relation. These tokens mark
// derived consequences, where-used pointers, disclaimers, or meta-prose. Do not
// ban adjectives used inside legitimate named mathematical conditions (for
// example, "standard Borel"); the standard/novel metadata checks provenance.
const BANNED_TOKENS: RegExp[] = [
  /\bthus\b/i,
  /\bconsequently\b/i,
  /\bhence\b/i,
  /\bmoreover\b/i,
  /\bin addition\b/i,
  /\b(and )?likewise\b/i,
  /\bis used (by|for|in)\b/i,
  /\bused (by|for|in) the\b/i,
  /\bwe assume\b/i,
  /\bno .* is claimed\b/i,
];

// Provability-commentary forbidden in a frozen definition's `construction` (G7
// provability firewall). Targets editorializing phrases only — NOT bare "open"
// (legitimate in "open interval/ball"), so a real construction formula is safe.
const PROVABILITY_COMMENTARY: RegExp[] = [
  /\bleft open\b/i,
  /\bremains? open\b/i,
  /\bopen (problem|question)\b/i,
  /\bnot derivable\b/i,
  /\bun-?derivable\b/i,
  /\bcannot be (derived|determined|fixed|proven|established|pinned)\b/i,
  /\bnot (fixed|determined|derived|pinned) by the [^.]{0,30}primitives\b/i,
  /\bunprovable\b/i,
];

function escapeRe(s: string): string {
  return s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

/** Match a construction name as a standalone token, not as a substring. A bare
 *  `new RegExp(escapeRe(name))` lets a short name (`g`, `T`, `mu`) fire inside
 *  ordinary English words ("desi*g*nated", "satisfyin*g*"), which reads as a
 *  witness reference that is not there. The guard is applied per side and only
 *  where the name's own edge character is alphanumeric, so names that already
 *  begin or end in punctuation (`\hat{g}`) keep matching after a letter.
 *
 *  `_` is deliberately NOT a boundary character here. This text is LaTeX, where
 *  `_` is the subscript delimiter rather than part of a name: with `_` in the
 *  class, construction `Omega` stops matching `\Omega_n` and `g` stops matching
 *  `g_n` — both GENUINE witness carves. G5 is a soundness firewall, so a false
 *  negative is the costly direction; excluding `_` still blocks the English-word
 *  case this guard exists for. */
function constructionNameRe(name: string): RegExp {
  // `(?<!\\[,;:!]\s?)` — a TeX spacing command directly before a single letter
  // is the differential idiom (`\,d\mu`, `\; d x`): that `d` is the measure
  // differential, never a witness reference. Scoped to the spacing commands so
  // a genuine reference after `\colon`/`\{` etc. still matches (G5 is a
  // soundness firewall; false negatives are the costly direction).
  const left = /^[A-Za-z0-9]/.test(name) ? "(?<![A-Za-z0-9])(?<!\\\\[,;:!]\\s?)" : "";
  const right = /[A-Za-z0-9]$/.test(name) ? "(?![A-Za-z0-9])" : "";
  return new RegExp(`${left}${escapeRe(name)}${right}`);
}

export function runStructuralGate(coreInput: unknown, opts: GateOptions = {}): GateResult {
  const violations: GateViolation[] = [];
  const notes: GateViolation[] = [];

  const parsed = CoreSchema.safeParse(coreInput);
  if (!parsed.success) {
    for (const issue of parsed.error.issues) {
      violations.push({
        code: "schema",
        where: issue.path.join(".") || "<root>",
        message: issue.message,
      });
    }
    return { ok: false, violations };
  }
  const core = parsed.data;

  const symbolNames = new Set(core.symbols.map((s) => s.name));
  const classDefs = core.definitions.filter((d) => d.by_member_properties !== undefined);
  const constructionDefs = core.definitions.filter((d) => d.by_member_properties === undefined);
  const classNames = classDefs.map((d) => d.name);
  const constructionNames = constructionDefs.map((d) => d.name);
  const assumptionIds = new Set<string>(core.assumptions.map((a) => a.id));
  const nodeIds = new Set<string>([
    ...core.assumptions.map((a) => a.id),
    ...core.definitions.map((d) => d.id),
    ...core.statements.map((s) => s.id),
  ]);
  const bibKeys = new Set(core.bibliography.map((b) => b.key));

  // G1: every declared free symbol is in the symbol table; symbol def-refs are
  // defined before use (array order is the definition order), except within a cycle of
  // `refs` — symbols described through each other, which no order satisfies
  // (`symbol_order.ts`: the V1 runner orders the table, the transcriber does not).
  //
  // Definitions and statements are checked alongside assumptions because they now
  // declare `free_symbols` too, and the declaration is what SCOPES a node's symbols
  // (`verify/core_graph.ts`). An UNRESOLVABLE name there is worse than on an
  // assumption: the scope reads the list as the complete set of symbols the claim rests
  // on, so a name matching no symbol contributes nothing while the symbol it was meant to
  // name goes unwatched — a re-definition of it would leave the proof standing. This gate
  // is also what keeps the declarations exact rather than merely normalizable: under it,
  // all 2832 assumption declarations in the 42 real cores resolve without normalization,
  // and the same pressure now applies to the two node kinds that had none. Legacy cores
  // are unaffected — no statement or definition on disk carries the key, and absent is
  // read as "may use any symbol" (fail-safe), never as a violation.
  const declaringNodes: Array<{ id: string; free_symbols?: string[] }> = [
    ...core.assumptions,
    ...core.definitions,
    ...core.statements,
  ];
  // Delimiter-normalized on both sides via `normalizeSymbol`, matching every other
  // free-symbol consumer: `\(\eta\)` and `\eta` name the same table entry everywhere else,
  // so raw equality here rejected an already-accepted core.
  const normalizedSymbolNames = new Set(core.symbols.map((s) => normalizeSymbol(s.name)));
  for (const node of declaringNodes) {
    for (const fs of node.free_symbols ?? []) {
      if (!normalizedSymbolNames.has(normalizeSymbol(fs))) {
        violations.push({
          code: "G1",
          where: node.id,
          message:
            `free symbol '${fs}' not in symbol table; each free_symbols element must name ` +
            `exactly one declared symbol (split comma-separated groups)`,
        });
      }
    }
  }
  const seenSymbols = new Set<string>();
  const refsReach = symbolRefsReach(core.symbols);
  for (const s of core.symbols) {
    if (s.ref !== undefined && !nodeIds.has(s.ref)) {
      violations.push({
        code: "G1",
        where: `symbol:${s.name}`,
        message: `ref '${s.ref}' does not resolve to a surviving definition, assumption, or statement`,
      });
    }
    for (const r of s.refs ?? []) {
      if (!symbolNames.has(r)) {
        violations.push({
          code: "G1",
          where: `symbol:${s.name}`,
          message: `refs names '${r}', which is no symbol of the table; \`refs\` lists symbol names only (add the symbol, or drop the name)`,
        });
      } else if (r !== s.name && !seenSymbols.has(r) && !refsReach.get(r)!.has(s.name)) {
        violations.push({
          code: "G1",
          where: `symbol:${s.name}`,
          message: `references symbol '${r}' before it is defined`,
        });
      }
    }
    seenSymbols.add(s.name);
  }

  // G2: single relation, no forbidden prose.
  for (const a of core.assumptions) {
    for (const re of opts.verbatim ? [] : BANNED_TOKENS) {
      if (re.test(a.condition)) {
        violations.push({
          code: "G2",
          where: a.id,
          message: `condition contains forbidden prose (${re.source})`,
        });
      }
    }
    // Preserve the pre-existing sentence heuristic, but make it TeX-aware:
    // (1) mask periods that provably do not end a sentence (decimals `0.5`,
    //     abbreviations `i.i.d.` / `w.r.t.` / `Thm.`) — without this, the split
    //     fires on `i.i.d. \(N(0,\sigma^2)\)` and the terminal-closer guard
    //     below disables itself on any decimal constant;
    // (2) protect a period whose entire remaining suffix is only closing TeX
    //     math delimiters (terminal `.\n\\]`, `.\n$` and `.$$` included: papers
    //     write display math as `$ … $` too) — UNLESS
    //     an earlier plausible sentence end exists, in which case the terminal
    //     period is a real boundary after a lowercase-led second sentence.
    const masked = maskNonBoundaryPeriods(a.condition);
    const terminalCloserPeriod = /\.(?=\s*(?:(?:\\(?:\]|\)|end\{[^{}]+\})|\${1,2})\s*)+$)/.exec(masked);
    const earlierPlausibleEnd = terminalCloserPeriod
      ? hasPlausibleSentenceEnd(masked.slice(0, terminalCloserPeriod.index))
      : false;
    const sentenceScan = terminalCloserPeriod && !earlierPlausibleEnd
      ? `${masked.slice(0, terminalCloserPeriod.index)}∯${masked.slice(terminalCloserPeriod.index + 1)}`
      : masked;
    const clauses = sentenceScan.split(/\.\s+(?=[A-Z(\\$])/).filter((x) => x.trim().length > 0);
    // A verbatim quote of a DISPLAYED equation (the paper's own "(3)") is one relation however
    // its lead-in and the display punctuate; the sentence count is for authored prose.
    const quotesDisplay =
      opts.verbatim === true &&
      /\\begin\s*\{(?:equation|align|gather|multline|eqnarray|flalign|alignat)\*?\}|(?<!\\)\\\[|\$\$/.test(a.condition);
    if (clauses.length > 1 && !quotesDisplay) {
      // Verbatim: a several-sentence condition is the paper's own structure — a disjunction
      // of alternatives, a definition with its qualifier — which no slice can split without
      // changing its meaning. The referee judges whether it is one condition; it never blocks.
      (opts.verbatim ? notes : violations).push({
        code: "G2",
        where: a.id,
        message: opts.verbatim
          ? `condition reads as ${clauses.length} sentences — one condition, or several the paper states together? (referee)`
          : `condition reads as ${clauses.length} sentences (omnibus?) — split into atomic conditions`,
      });
    }
  }

  // G3: no assumption asserts membership in a CLASS (A6). Class membership of a
  // construction is always a statement, never an assumption.
  for (const a of core.assumptions) {
    for (const cn of classNames) {
      // `\\in(?![A-Za-z])` — without the boundary, `\in` matches the prefix of
      // `\int`/`\inf`/`\infty` and a short class name then falsely matches the
      // command's tail (`\int T` fired G3 for class `T`). The optional wrapper
      // lets the plain-named class `C` still be caught when written
      // `\\in \\mathcal{C}` — the idiomatic spelling — but is restricted to the
      // CLASS fonts: accepting any command let `x \\in \\mathbb{R}^d` (ambient
      // reals, ubiquitous) fire for a class named `R`.
      const re = new RegExp(
        `(∈|\\\\in(?![A-Za-z])|belongs to|lies in)\\s*\\$?\\s*(?:\\\\(?:mathcal|mathscr|mathfrak)\\s*\\{\\s*)?${escapeRe(cn)}`,
        "i",
      );
      if (re.test(a.condition)) {
        violations.push({
          code: "G3",
          where: a.id,
          message: `assumption asserts membership in class '${cn}' — must be a derived statement, not an assumption`,
        });
      }
    }
  }

  // G4: deps exist; statement DAG acyclic; (optionally) all discharged.
  for (const s of core.statements) {
    for (const d of s.depends_on) {
      if (!nodeIds.has(d)) {
        violations.push({ code: "G4", where: s.id, message: `depends_on '${d}' does not exist` });
      }
    }
  }
  const stmtIds = new Set(core.statements.map((s) => s.id));
  const adj = new Map<string, string[]>();
  for (const s of core.statements) {
    adj.set(
      s.id,
      s.depends_on.filter((d) => stmtIds.has(d)),
    );
  }
  // Every back edge of the DFS is one cycle: reported at the statement whose dependency
  // closes it, all of them in one pass (no early exit, so the author fixes them together).
  const color = new Map<string, number>(); // 0 unvisited, 1 in-stack, 2 done
  const dfs = (u: string): void => {
    color.set(u, 1);
    for (const v of adj.get(u) ?? []) {
      const c = color.get(v) ?? 0;
      if (c === 1) violations.push({ code: "G4", where: u, message: `dependency cycle: '${u}' depends on '${v}', which depends back on it` });
      else if (c === 0) dfs(v);
    }
    color.set(u, 2);
  };
  for (const s of core.statements) if ((color.get(s.id) ?? 0) === 0) dfs(s.id);
  if (opts.requireDischarged) {
    for (const s of core.statements) {
      // An OPEN-ENDED QUESTION may be a LEGITIMATELY OPEN residual (a tightness / matching
      // question the note poses but does not resolve). Whether an open OEQ is an acceptable
      // residual is not a structural-discharge requirement — so do
      // not fail the discharge gate on an unproved OEQ. Theorems/lemmas/props must still be
      // proved.
      if (s.kind === "openendedquestion" && s.id.startsWith("oeq:")) continue; // why: theorem-id nodes must not inherit the OEQ discharge exemption by kind alone.
      // A `cited` statement is DISCHARGED by its citation — it is an invoked classical
      // result, not a leaf we owe a proof for (its source⟺status xor + leaf rule are
      // enforced by the schema, and the bibkey by G6). Requiring `proved` here would
      // force re-deriving a published theorem; treat `cited` as discharged like `proved`.
      if (s.status !== "proved" && s.status !== "cited") {
        violations.push({
          code: "G4",
          where: s.id,
          message: `node left undischarged (status='${s.status}') after PROVE`,
        });
      }
    }
  }

  // G5: a class is carved only by member-properties. Its `construction` is the
  // explicit set-builder (required by the schema), but it must NOT take
  // construction `inputs`, and NEITHER the member-property list NOR the
  // set-builder text may reference a witness construction — that is the A6
  // firewall (carve a class by a membership predicate, never by a witness image).
  for (const d of classDefs) {
    if (d.inputs !== undefined) {
      violations.push({
        code: "G5",
        where: d.id,
        message: `class '${d.name}' must not carry construction inputs — its \`construction\` is the membership set-builder, not a parametrized construction`,
      });
    }
    // Every member property must be an ASSUMPTION id. The F1.5 plan gate (P2) demands
    // both that a plan class mirror this list exactly AND that each entry be an
    // assumption, so a def-valued entry here makes P2 unsatisfiable: mirroring trips
    // "is not an assumption", flattening trips "omits core member". The producer cannot
    // see the conflict and burns its cap. Enforce it where it is
    // fixable — at production. A class built from other classes carves by the UNION of
    // their member properties (its set-builder text still names the components).
    for (const mp of d.by_member_properties ?? []) {
      if (nodeIds.has(mp) && !assumptionIds.has(mp)) {
        violations.push({
          code: "G5",
          where: d.id,
          message:
            `class '${d.name}' member property '${mp}' is not an assumption — \`by_member_properties\` ` +
            `takes assumption ids only. If this class is carved from other classes, list the union of ` +
            `THEIR member properties here (the set-builder text already names the component classes).`,
        });
      }
    }
    const witnessSites: Array<[string, string]> = [
      ...(d.by_member_properties ?? []).map((mp) => ["member-property", mp] as [string, string]),
      ["set-builder", d.construction],
    ];
    for (const [site, text] of witnessSites) {
      for (const cn of constructionNames) {
        if (constructionNameRe(cn).test(text)) {
          violations.push({
            code: "G5",
            where: d.id,
            message: `class '${d.name}' ${site} references construction '${cn}' — carve a class by a membership predicate, not a witness image`,
          });
        }
      }
    }
  }

  // G6: a `bookkeeping` provenance tag is authored only by the V1/V1.5 transcription. The
  // schema's xor accepts it so a transcribed core parses at all; any other caller rejects it.
  if (!opts.allowBookkeeping) {
    for (const a of core.assumptions) {
      if (a.bookkeeping) {
        violations.push({
          code: "G6",
          where: a.id,
          message:
            "assumption carries a `bookkeeping` tag, which only the V1/V1.5 transcription may " +
            "author — use standard / novel / maintained",
        });
      }
    }
  }
  // G6: standard.cite resolves to a bibliography entry (the xor is enforced by
  // the schema refine; this checks the citation is real).
  for (const a of core.assumptions) {
    if (a.standard && !bibKeys.has(a.standard.cite)) {
      violations.push({
        code: "G6",
        where: a.id,
        message: `standard.cite '${a.standard.cite}' not in bibliography`,
      });
    }
  }
  // G6 (cited statements): a `status:"cited"` statement's `source.cite` resolves to
  // a bibliography entry (the cited⟺source xor and the leaf rule are enforced by the
  // schema refine; this checks the citation is real). This is the structured
  // provenance F1 turns into a `cite:` node, so the bibkey must exist.
  for (const s of core.statements) {
    if (s.status === "cited" && s.source && !bibKeys.has(s.source.cite)) {
      violations.push({
        code: "G6",
        where: s.id,
        message: `source.cite '${s.source.cite}' not in bibliography`,
      });
    }
  }

  // G7: a construction definition carries no by_member_properties (the schema
  // refine enforces it; double-check for robustness if the schema is loosened).
  for (const d of constructionDefs) {
    if (d.by_member_properties !== undefined) {
      violations.push({
        code: "G7",
        where: d.id,
        message: `construction '${d.name}' must not carry by_member_properties`,
      });
    }
  }

  // G7 (provability firewall): a frozen definition NAMES a construction or fixes
  // a quantity — it must NEVER editorialize about whether a target is provable.
  // A def asserting "left open / not derivable / not fixed by the primitives" is a
  // self-fulfilling prophecy: the solver respects the frozen core and dutifully
  // reports the target open. The freeze binds the QUESTION, never the answer's
  // existence.
  for (const d of core.definitions) {
    for (const re of PROVABILITY_COMMENTARY) {
      if (re.test(d.construction)) {
        violations.push({
          code: "G7",
          where: d.id,
          message: `definition '${d.name}' \`construction\` editorializes about provability (${re.source}) — a frozen def names a construction or fixes a quantity, it must not assert a target is open/underivable; the solver derives the answer`,
        });
      }
    }
  }

  return { ok: violations.length === 0, violations, ...(opts.verbatim ? { notes } : {}) };
}
