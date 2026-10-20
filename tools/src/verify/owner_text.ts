/**
 * Text written for the paper's AUTHOR (user rule 2026-09-24: the annotated paper states the
 * mistake plainly and contains only the error; user verdict 2026-09-24: from the note alone the
 * author must see WHY the statement needs correcting and WHAT is wrong).
 *
 * The fixer writes an `owner_explanation` for every error it answers, as FIELDS
 * (design 2026-09-25, P3: fields, not templates): `claim`, `defects` (each a kind, the unit of the failing
 * step and the phrases its kind needs), `why` (the objects of a failing instance and the failing
 * consequence), `fix` and `gives_up` — with no node ids and no pipeline vocabulary. The checks are content
 * checks on the fields (`noteProblems`); the sentences the author reads are generated from them in ONE
 * place (`noteProse`: the step quoted from the paper's unit, one plain sentence per kind). Files written
 * before notes had any structure carry a free-prose string (`OwnerExplanationField`), still read.
 * `ownerFacing` is the deterministic backstop applied to every such text (each field of a note) before it
 * reaches the author: it drops each sentence that names a node id or talks about the transcription
 * machinery, and falls back to one sentence built from the witness when nothing survives. Pure.
 */
import { z } from "zod";
import { nonAsciiProblem, texRegions } from "./annotate_tex.js";
import { BUILTIN_ENVS } from "./tex_envs.js";
import { sentenceSpans } from "./transcription_lint.js";

/**
 * The node-id rule, the ONE predicate every author-facing check and filter applies (the V1 fixer's
 * `owner_explanation`, the V1.5 referee's, the rendering backstop).
 *
 * A node id is a pipeline handle the author never wrote, so text for the author must not name one.
 * But core ids reuse the paper's own `\label`s (`thm:local`), so two forms are the PAPER's way of
 * referring and are never a mention:
 *  - the argument of a LaTeX reference macro (`\ref{thm:local}`, `\eqref`, `\cref`/`\Cref`,
 *    `\autoref`, `\nameref`, `\pageref`, `\hyperref[…]`, `\label`, `\cite…`) — masked first;
 *  - a bare token equal to one of the paper's labels (`paperLabels` of the flattened paper), when
 *    the caller supplies them.
 * Anything else shaped `<kind>:<slug>` is a mention, matched as a WHOLE token (never a prefix:
 * `cor:CI` is not `thm:ci`, `thm:local-local-clause` is not `thm:local`). Without labels every
 * bare token counts. Pure.
 */
export type PaperLabels = ReadonlySet<string>;

/**
 * The paper's labels carrying the flattened paper they were read from (`paperLabels`).
 */
export class PaperLabelSet extends Set<string> {
  constructor(
    labels: Iterable<string>,
    readonly paper: string,
  ) {
    super(labels);
  }
}

/** Node-id kinds as they appear in prose (the core's, plus `cor`). */
const ID_KINDS = "ass|thm|lem|prop|def|cor|oeq|conj";
/** A whole id token; the slug admits `_` and `.` so a paper label (`cor:CI_local`) is read whole. */
const ID_TOKEN = new RegExp(String.raw`(?<![A-Za-z0-9_\\-])(?:${ID_KINDS}):[A-Za-z0-9](?:[A-Za-z0-9_.-]*[A-Za-z0-9_])?`, "giu");
/** A LaTeX reference macro with its label arguments (starred, optional args, several brace args). */
const REF_MACRO = /\\(?:[cC]ref\w*|ref|eqref|autoref|nameref|pageref|vref|label|cite\w*|hyperref)\*?(?:\s*\[[^\]]*\])*(?:\s*\{[^{}]*\})*/gu;
/** Words about the pipeline rather than the paper's mathematics. An edge, a node or a core is the
 * paper's own word in a graph or a game, so those count only in the pipeline's phrases. */
const PIPELINE_WORD = /\b(?:dependency\s+edges?|core(?:[._]json|\s+(?:nodes?|file|json))|node[_-]ids?|wired|wiring|depends_on|transcri\w*|pipeline|referee|fixer|scaffold\w*)\b/iu;

/** Every `\label{…}` of the flattened paper (the paper's own names for its results). */
export function paperLabels(flatTex: string): PaperLabelSet {
  return new PaperLabelSet([...flatTex.matchAll(/\\label\s*\{([^{}]*)\}/gu)].map((m) => m[1]!.trim()).filter(Boolean), flatTex);
}

/** The node ids `text` names (whole tokens, first-seen order): none inside a reference macro, and
 * none that is one of the paper's `labels`. */
export function nodeIdMentions(text: string, labels?: PaperLabels): string[] {
  const masked = text.replace(new RegExp(REF_MACRO.source, "gu"), (m) => " ".repeat(m.length));
  const lower = labels ? new Set([...labels].map((l) => l.toLowerCase())) : null;
  const out: string[] = [];
  for (const m of masked.matchAll(new RegExp(ID_TOKEN.source, "giu"))) {
    const id = m[0].replace(/[._-]+$/u, "");
    if (lower && lower.has(id.toLowerCase())) continue;
    if (!out.includes(id)) out.push(id);
  }
  return out;
}

/** Why `text` is not fit for the author, sentence by sentence (empty = fit). */
export function ownerFacingProblems(text: string, labels?: PaperLabels): string[] {
  return sentences(text).flatMap((s) => {
    const ids = nodeIdMentions(s, labels);
    const w = PIPELINE_WORD.exec(s);
    return ids.length > 0 || w ? [`"${s.length > 80 ? `${s.slice(0, 79)}…` : s}" names ${ids.length > 0 ? `a node id (${ids.join(", ")})` : `"${w![0]}"`}`] : [];
  });
}

export function sentences(text: string): string[] {
  const t = text.replace(/\s+/g, " ").trim();
  if (!t) return [];
  return sentenceSpans(t).map((sp) => t.slice(sp.start, sp.end).trim()).filter(Boolean);
}

/** Does this sentence speak to the author about the paper (no node id, no pipeline word)? */
export function isOwnerFacing(sentence: string, labels?: PaperLabels): boolean {
  return nodeIdMentions(sentence, labels).length === 0 && !PIPELINE_WORD.test(sentence);
}

/**
 * `text` with every sentence that names a node id or a pipeline word removed. When nothing
 * survives: "The statement as printed does not hold: <the first owner-facing sentence of the
 * witness>." (or without the colon clause when the witness has none either).
 */
export function ownerFacing(text: string, witness: string | null = null, labels?: PaperLabels): string {
  const fit = (s: string): boolean => isOwnerFacing(s, labels);
  const kept = sentences(text).filter(fit);
  if (kept.length > 0) return kept.join(" ");
  const w = sentences(witness ?? "").find(fit);
  return w ? `The statement as printed does not hold: ${lowerFirst(w.replace(/[.!?]\s*$/u, ""))}.` : "The statement as printed does not hold.";
}

function lowerFirst(s: string): string {
  // Keep a capital that starts a name or a symbol ("Berry–Esseen", "W", "Y"): only a plain word is lowered.
  return /^[A-Z][a-z]+\b/u.test(s) && !/^[A-Z][a-z]+[–-]/u.test(s) ? s[0]!.toLowerCase() + s.slice(1) : s;
}

/**
 * The explanation for the author of one error: the model's `owner_explanation` when there is one
 * (the structure as labelled parts, `renderExplanation`; legacy prose filtered), else the error's detail (both through `ownerFacing`), with the witness's gist appended to a detail
 * that survives the filter.
 */
export function ownerExplanation(
  e: { owner_explanation?: OwnerExplanationField | null; detail: string; witness: string | null },
  witnessGist: (w: string) => string = (w) => w,
  /** At most this many sentences of the detail (the model's explanation is never cut). */
  maxDetailSentences = Infinity,
  opts: { omitGivesUp?: boolean; labels?: PaperLabels } = {},
): string {
  const oe = e.owner_explanation;
  const fit = (s: string): boolean => isOwnerFacing(s, opts.labels);
  if (oe && typeof oe === "object") {
    const t = renderExplanation(oe, opts);
    if (t) return t;
  } else if (oe?.trim()) return ownerFacing(oe, e.witness, opts.labels);
  const kept = sentences(e.detail).filter(fit).slice(0, maxDetailSentences);
  if (kept.length === 0) return ownerFacing("", e.witness, opts.labels);
  const w = e.witness ? sentences(witnessGist(e.witness)).filter((s) => fit(s) || s === "\\dots{}").join(" ").replace(/^\\dots\{\}\s*|\s*\\dots\{\}$/gu, "") : "";
  return `${kept.join(" ")}${w ? ` Counterexample: ${/[.!?]$/u.test(w.trim()) ? w.trim() : `${w.trim()}.`}` : ""}`;
}

// ---------------------------------------------------------------------------------------------
// The note: fields, not templates (design 2026-09-25, P3)
// ---------------------------------------------------------------------------------------------

/** The kinds of defect a note names; the kind decides the fields a defect carries (`KIND_FIELDS`) and
 * the sentence it reads as (`noteProse`). */
export const DEFECT_KINDS = ["out_of_domain", "undefined_case", "missing_hypothesis", "wrong_constant", "dropped_case", "other"] as const;
export type DefectKind = (typeof DEFECT_KINDS)[number];

/** The TeX fields of a defect. */
export const DEFECT_TEXT_FIELDS = ["uses", "assumed_on", "applied_at", "detail"] as const;
type DefectTextField = (typeof DEFECT_TEXT_FIELDS)[number];

/** The fields each kind requires, non-empty; its other TeX fields are null. */
export const KIND_FIELDS: Record<DefectKind, readonly DefectTextField[]> = {
  out_of_domain: ["uses", "assumed_on", "applied_at"],
  undefined_case: ["detail"],
  missing_hypothesis: ["detail"],
  wrong_constant: ["detail"],
  dropped_case: ["detail"],
  other: ["detail"],
};

const OptTex = z.string().nullable().optional();
/** One defect of the printed proof (of the printed statement when the paper prints no proof):
 * `step_unit` is the unit of the failing step (`units.ts`). */
export const DefectSchema = z.object({
  kind: z.enum(DEFECT_KINDS),
  step_unit: z.string(),
  uses: OptTex,
  assumed_on: OptTex,
  applied_at: OptTex,
  detail: OptTex,
});
export type Defect = z.infer<typeof DefectSchema>;

/** The error for the paper's author, as fields; every sentence the author reads is generated from them
 * (`noteProse`). `why.objects` each define one object of a failing instance, `why.consequence` states
 * the failing quantity or relation. */
export const OwnerExplanationSchema = z.object({
  claim: z.string(),
  defects: z.array(DefectSchema),
  why: z.object({ objects: z.array(z.string()), consequence: z.string() }),
  fix: z.string(),
  gives_up: z.string().nullable(),
});
export type OwnerExplanation = z.infer<typeof OwnerExplanationSchema>;

/** What a record on disk may carry: the note, or (written before notes had fields) free prose. */
export const OwnerExplanationFieldSchema = z.union([OwnerExplanationSchema, z.string()]);
export type OwnerExplanationField = OwnerExplanation | string;

/** The JSON Schema `pattern` of every TeX-bearing string a model writes: printable ASCII, newline and
 * tab — constrained decoding then cannot emit Unicode mathematics (`TEX_MATH_RULE`). */
/** Typographic characters an owner types (or a page pastes) and their plain-TeX spelling. */
const TYPED: ReadonlyArray<[RegExp, string]> = [
  [/\u2014/g, "---"], [/\u2013/g, "--"], [/[\u201C\u201F]/g, "``"], [/\u201D/g, "''"], [/[\u2018\u201B]/g, "`"], [/\u2019/g, "'"],
  [/\u2026/g, "\\ldots{}"], [/\u00A0/g, "~"], [/\u2264/g, "$\\leq$"], [/\u2265/g, "$\\geq$"], [/\u2260/g, "$\\neq$"],
  [/\u00D7/g, "$\\times$"], [/\u2192/g, "$\\to$"], [/\u00B1/g, "$\\pm$"], [/\u221E/g, "$\\infty$"], [/\u2208/g, "$\\in$"],
];
/**
 * The owner's words as plain-ASCII TeX: the dashes, quotes, ellipsis and common signs a keyboard or
 * a web page produces, in their TeX spelling. The owner's texts are printed in the annotated paper,
 * whose contract is plain ASCII — and no model of the run can be asked to re-write them. Pure.
 */
export function ownerWordsTex(text: string): string {
  return TYPED.reduce((t, [re, tex]) => t.replace(re, tex), text);
}

export const ASCII_TEX_PATTERN = "^[\\x20-\\x7E\\n\\t]*$";
/** A TeX-bearing string field of a reply schema (`ASCII_TEX_PATTERN`). */
export const TEX_STRING: Record<string, unknown> = { type: "string", pattern: ASCII_TEX_PATTERN };
/** A TeX-bearing string field the reply's zod schema refuses empty (`min(1)`): the wire schema says so too. */
export const TEX_STRING_NONEMPTY: Record<string, unknown> = { type: "string", pattern: ASCII_TEX_PATTERN.replace("]*$", "]+$") };
/** A nullable TeX-bearing string field. */
export const TEX_STRING_OR_NULL: Record<string, unknown> = { type: ["string", "null"], pattern: ASCII_TEX_PATTERN };

/** Strict JSON Schema of the note, for every model reply that carries one. */
export const OWNER_EXPLANATION_JSON: Record<string, unknown> = {
  type: "object",
  additionalProperties: false,
  required: ["claim", "defects", "why", "fix", "gives_up"],
  properties: {
    claim: TEX_STRING,
    defects: {
      type: "array",
      items: {
        type: "object",
        additionalProperties: false,
        required: ["kind", "step_unit", ...DEFECT_TEXT_FIELDS],
        properties: { kind: { type: "string", enum: [...DEFECT_KINDS] }, step_unit: { type: "string" }, ...Object.fromEntries(DEFECT_TEXT_FIELDS.map((f) => [f, TEX_STRING_OR_NULL])) },
      },
    },
    why: {
      type: "object",
      additionalProperties: false,
      required: ["objects", "consequence"],
      properties: { objects: { type: "array", items: TEX_STRING }, consequence: TEX_STRING },
    },
    fix: TEX_STRING,
    gives_up: TEX_STRING_OR_NULL,
  },
};

/** The note as the author reads it (`noteProse`): claim, one sentence per defect (its step quoted), the
 * instance, the fix and what is given up. */
export interface NoteProse {
  claim: string;
  what_is_wrong: string[];
  why: string;
  fix: string;
  gives_up: string | null;
}

/** The prose, in the order the author reads it, with its printed labels. The instance (`why`) is the
 * last line of "What is wrong", as "Counterexample: …" (user decision 2026-09-26: one section). */
export const OWNER_EXPLANATION_LABELS: ReadonlyArray<readonly [keyof NoteProse, string]> = [
  ["claim", "Claim"],
  ["what_is_wrong", "What is wrong"],
  ["fix", "Proposed fix"],
  ["gives_up", "Gives up"],
];

/**
 * The math contract of every author-facing text a model writes (user rule 2026-09-25: explanations
 * write math as TeX directly, not Unicode a converter renders): stated once here and quoted by every
 * prompt that asks for an explanation or a corrected statement (`NOTE_FIELDS_TEXT`, the
 * referee's `NODE_FIELDS_TEXT`); checked by
 * `texMathProblems` on the DECODED reply.
 */
export const TEX_MATH_RULE = String.raw`All mathematics in these texts (every field of a note, a reading, a condition, a quoted step, a corrected statement, an added hypothesis, a proof edit) is LaTeX inside $…$ (or a display \[…\]), in the paper's own macros and notation: no Unicode math symbols (Greek letters, ≤, √, ∫, ≍, …), no super- or subscript characters (², ₙ, ⁻¹ᐟ²) and no plain-text forms such as ^(, _( or √(. Every delimiter opened is closed, and braces that print are \{ … \} (a bare { … } only groups). Each text is compiled as LaTeX against the paper's preamble; the reply is plain ASCII; every symbol is a TeX command, and quotation marks are TeX quotes, ${"``"}like this'', never curly quotes. In the JSON reply each TeX backslash is written as the JSON escape \\ ("\\alpha" in the JSON is \alpha in the text), so the decoded string is the TeX, with one backslash per command.`;

/** The word the paper names a result by: the kind its printed environment stands for (`envKinds`, a
 * run's `envs.json` `newtheorem` map, else the built-in one: "cor" and "corollary" are "Corollary" for a
 * result the core records as a theorem), else its recorded kind. Pure. */
export function resultWord(st: { kind?: string; tex_locator?: { env?: string | null } | null } | null | undefined, envKinds: Readonly<Record<string, string>> = BUILTIN_ENVS): string {
  const env = st?.tex_locator?.env?.replace(/\*$/u, "");
  if (env && /^algorithm/i.test(env)) return "Algorithm"; // a float or a pseudocode block: its own word
  const k = env && env !== "prose" ? envKinds[env] : undefined;
  const w = (k && k !== "other" ? k : undefined) ?? st?.kind ?? "result";
  return w[0]!.toUpperCase() + w.slice(1);
}

/**
 * How every author-facing text names a result of the paper (user rule 2026-09-25: readings said "the
 * scaling theorem", "the lemma about …", "Lemma A.2" where the paper prints "Theorem 2", "Lemma 2"):
 * by the environment word and `\ref`, which typesets to the paper's own number. Quoted by the
 * note's field text (`NOTE_FIELDS_TEXT`); a symbol's reading takes
 * `READING_RESULT_NAME_RULE`.
 */
export const RESULT_NAME_RULE = String.raw`Name a result by its environment word and \ref{<its label>} ("Lemma~\ref{lemma:rp}"), never by a nickname ("the variance lemma", "the lemma about ...") or a section number the paper does not print; an unlabelled one by its printed heading; a group of results by listing each ("Lemmas~\ref{a} and~\ref{b}") or by the section that holds them ("the results of Section~\ref{sec:x}", or its printed heading).`;

/**
 * `RESULT_NAME_RULE` for a symbol's reading, which may not name an unlabelled result by its heading:
 * the runner re-reads a reading when a result it names changes, and finds a result by `\ref` or by
 * its id, never by words (`referee_symbols.ts`). Quoted by `SYMBOL_FIELDS_TEXT`; stated once more, in
 * the same terms, by `prompts/V1.5/symbols.txt`.
 */
export const READING_RESULT_NAME_RULE = String.raw`Name a result by its environment word and \ref{<its label>} ("Lemma~\ref{lemma:rp}"), never by a nickname, a typed number or a heading in words; an unlabelled one by its id as listed under THE TEXT EACH READING DESCRIBES; a group of results by listing each ("Lemmas~\ref{a} and~\ref{b}") or by the section that holds them, by its label ("the results of Section~\ref{sec:x}").`;

/**
 * What a reading or a note describes (user rule 2026-09-25: symbol readings spoke of "the repaired
 * variance theorem" while that repair was a suggestion awaiting the owner): the paper as printed, or as
 * changed by a confirmed repair. Quoted by `prompts/V1.5/symbols.txt` and the reading field texts
 * (`NODE_FIELDS_TEXT`, `SYMBOL_FIELDS_TEXT`).
 */
export const READING_BASIS_RULE = String.raw`A reading describes the paper as printed, or as changed by a confirmed repair — never a suggested repair awaiting the owner — and never names a result "repaired" or "corrected".`;


/** What follows a line break that ate the `\n` of a TeX command (`\neq` → break + "eq"). */
const EATEN_N = /^(?:eq?|u|abla|ot(?:in)?|ewline|ormalfont|oindent|leq|geq|mid|parallel|subseteq|ewcommand)$/u;
const MATH_ENV_OPEN = /^\\begin\s*\{((?:equation|align|alignat|flalign|gather|multline|eqnarray|displaymath|math)\*?)\}/u;

/** The math regions of `t` (`$…$`, `$$…$$`, `\(…\)`, `\[…\]`, a math environment), each `[start, end)`
 * with whether it is inline, and the delimiter left open (null when every one closes). Pure. */
function mathSpans(t: string): { spans: Array<{ start: number; end: number; inline: boolean }>; open: string | null } {
  const spans: Array<{ start: number; end: number; inline: boolean }> = [];
  /** The next unescaped `d` at or after `from`, or -1. */
  const next = (d: string, from: number): number => {
    for (let j = from; j < t.length; j += 1) {
      if (t[j] === "\\" && d !== "\\)" && d !== "\\]") j += 1;
      else if (t.startsWith(d, j)) return j;
    }
    return -1;
  };
  for (let i = 0; i < t.length; ) {
    if (t[i] === "\\") {
      const env = MATH_ENV_OPEN.exec(t.slice(i));
      if (t[i + 1] === "(" || t[i + 1] === "[" || env) {
        const close = env ? `\\end{${env[1]}}` : t[i + 1] === "(" ? "\\)" : "\\]";
        const j = t.indexOf(close, i + 2);
        if (j < 0) return { spans, open: env ? `\\begin{${env[1]}}` : t.slice(i, i + 2) };
        spans.push({ start: i, end: j + close.length, inline: t[i + 1] === "(" });
        i = j + close.length;
      } else i += 2;
      continue;
    }
    if (t[i] === "$") {
      const d = t[i + 1] === "$" ? "$$" : "$";
      const j = next(d, i + d.length);
      if (j < 0) return { spans, open: d };
      spans.push({ start: i, end: j + d.length, inline: d === "$" });
      i = j + d.length;
      continue;
    }
    i += 1;
  }
  return { spans, open: null };
}


/**
 * Why `text` breaks `TEX_MATH_RULE` (empty = it does not), on the DECODED string (the JSON reply
 * parsed), before and besides its compile (`tex_fragment_check.ts`): (a) a character outside
 * printable ASCII (`nonAsciiProblem`); (b) a math delimiter left open; (c) a TeX command with a
 * doubled backslash (the model escaped twice); (d) a control character, or a line break inside inline
 * math — a JSON escape the model meant as TeX (`"\theta"` decodes to a tab and `heta`, `"\neq"` to a
 * line break and `eq`) — (c)–(d) compile and print the wrong text. Mathematics outside `$…$` is the
 * compile's to catch (exact checks only, user decision 2026-09-26). `field` names where, in the message;
 * `reference` (the printed text a repair copies — the statement, the proof) exempts what it writes
 * itself. Nothing here repairs. Pure.
 */
export function texMathProblems(text: string, field?: string, opts: { reference?: string } = {}): string[] {
  const where = field ? ` in \`${field}\`` : "";
  const out: string[] = [];
  // What the printed text itself writes is the paper's, not a slip (a repair copies it verbatim).
  const refSq = opts.reference ? opts.reference.replace(/\s+/g, "") : null;
  const inReference = (frag: string): boolean => refSq !== null && refSq.includes(frag.replace(/\s+/g, ""));
  const refChars = new Set(opts.reference ?? "");
  const ascii = nonAsciiProblem([...text].filter((c) => !refChars.has(c)).join(""));
  if (ascii) out.push(`contains ${ascii.replace(" — ", () => `${where} — `)}`);
  // (the printed text's own: a tab or the like it has at that very place, or indenting a line when
  // the printed text indents with it — a source indented with tabs, a unit of it replaced)
  const indents = (i: number, c: string): boolean => refChars.has(c) && /(?:^|\n)[ \t]*$/u.test(text.slice(0, i));
  const ctrl =
    [...text.matchAll(/[\u0000-\u0008\u000B\u000C\u000E-\u001F\t\r]/gu)].find(
      (m) => !opts.reference?.includes(text.slice(m.index, m.index + 9)) && !indents(m.index, m[0]),
    ) ?? null;
  const t = text;
  const { spans, open } = mathSpans(t);
  // A line break inside inline math is legal TeX, and a printed statement or proof has them (the
  // `reference` case): there only a break that ate a command's `\n` counts ("\neq" decoded as a
  // break and "eq").
  const inline = spans.filter((s) => s.inline).map((s) => t.slice(s.start, s.end));
  const inlineBreak: RegExpMatchArray | undefined =
    opts.reference === undefined
      ? (inline.map((x) => /\n\s*([A-Za-z]*)/u.exec(x)).find((m) => m) ?? undefined)
      : inline.flatMap((x) => [...x.matchAll(/\n([A-Za-z]+)/gu)]).find((m) => EATEN_N.test(m[1]!));
  if (ctrl || inlineBreak) {
    const at = ctrl ? ctrl.index + 1 : -1;
    const after = ctrl ? (/^[A-Za-z]*/u.exec(text.slice(at))?.[0] ?? "") : inlineBreak![1]!;
    const what = ctrl ? `a control character (U+${ctrl[0].codePointAt(0)!.toString(16).toUpperCase().padStart(4, "0")})` : "a line break inside $…$";
    out.push(
      `contains ${what}${where}${after ? ` before "${after}"` : ""} — a TeX backslash was not escaped in the JSON (a JSON "\\t" or "\\n" decodes to a tab or a line break): write every TeX backslash as "\\\\" in the JSON, and keep inline math on one line`,
    );
  }
  // Inside an environment `\\` before a letter is a row break (a matrix or aligned row starting with
  // a letter), not a command escaped twice.
  const inEnvironment = (at: number): boolean => {
    const before = t.slice(0, at);
    return (before.match(/\\begin\s*\{/gu)?.length ?? 0) > (before.match(/\\end\s*\{/gu)?.length ?? 0);
  };
  const doubled = [...t.matchAll(/\\\\[A-Za-z]+/gu)].find((m) => !inReference(m[0]) && !inEnvironment(m.index!));
  if (doubled) out.push(`writes a TeX command with a doubled backslash${where} ("${doubled[0]}") — the decoded text has ONE backslash per command: in the JSON write "\\\\${doubled[0].slice(2)}", which decodes to \\${doubled[0].slice(2)}`);
  if (open && !(opts.reference !== undefined && mathSpans(opts.reference).open === open)) out.push(`leaves "${open}" unclosed${where} — close every math delimiter (a literal dollar sign is \\$)`);
  return out;
}

/**
 * The part of `texMathProblems` that is breakage in ANY notation, for a text the referee writes into
 * the core in the paper's notation (a pinned reading, a bookkeeping condition, a symbol fix): a
 * non-ASCII character, a control character or a line break a JSON escape ate, a doubled backslash, a
 * brace group whose backslash was lost (`f{Y(1)}`). Its compile (`tex_fragment_check.ts`) judges the
 * rest. Pure.
 */
export function texEscapeProblems(text: string, field?: string): string[] {
  return texMathProblems(text, field).filter((p) => /^(?:contains a|writes a TeX command with a doubled)/u.test(p));
}

// ---------------------------------------------------------------------------------------------
// The sentences, generated from the fields (the ONLY place a note's prose is made)
// ---------------------------------------------------------------------------------------------

/** A unit's printed text by its id (`PaperUnits.textById`), null when the paper has no such unit. */
export type QuoteOf = (unitId: string) => string | null;

/** At most this many characters of a quoted step (cut at a clause end outside mathematics). */
export const QUOTE_MAX = 200;

/** A display environment of the paper, kept displayed in a quote (`\[…\]`). */
const DISPLAY_ENV = /\\begin\{(equation|align|alignat|gather|multline|flalign|eqnarray|displaymath)(\*?)\}(?:\{[^{}]*\})?([\s\S]*?)\\end\{\1\2\}/gu;

/** A display environment's body as one formula: its alignment marks dropped; several rows kept as rows
 * (a core-LaTeX `array`, each row in display style — one flattened line ran 489pt past the margin,
 * live DFM 2026-09-26). */
function displayRows(body: string): string {
  const rows = body.split(/\\\\(?:\s*\[[^\]]*\])?/u).map((r) => r.replace(/(?<!\\)&/gu, " ").trim()).filter(Boolean);
  return rows.length <= 1 ? ` ${rows[0] ?? ""} ` : `\\begin{array}{@{}c@{}}${rows.map((r) => `\\displaystyle ${r}`).join(" \\\\ ")}\\end{array}`;
}

/**
 * A printed unit's text with its braces balanced, by counting unescaped `{` / `}` alone: a group the
 * paper opens in an earlier step and closes in this one loses its `}`, a group this step opens and a
 * later step closes (`\textcolor{black}{…` over a whole proof) gets its `}` at the end — a quote is
 * read alone. A trailing unescaped `\` (a control space whose space the quote trimmed: `robust\ `)
 * is dropped, else it would escape that `}`. Pure.
 */
export function balancedBraces(tex: string): string {
  const trailing = /\\+$/u.exec(tex)?.[0].length ?? 0;
  if (trailing % 2 === 1) tex = tex.slice(0, -1);
  let depth = 0;
  let out = "";
  for (let i = 0; i < tex.length; i += 1) {
    const c = tex[i]!;
    if (c === "\\") {
      out += tex.slice(i, i + 2);
      i += 1;
      continue;
    }
    if (c === "}" && depth === 0) continue;
    if (c === "{") depth += 1;
    else if (c === "}") depth -= 1;
    out += c;
  }
  return out + "}".repeat(depth);
}

/**
 * A unit's printed text as a note quotes it: labels, tags and `\nonumber` dropped, a display kept
 * displayed as `\[…\]` (`displayRows`: alignment marks dropped, rows kept; the annotated paper sets it with
 * `\vsDisplay`, since inline math cannot break at the margin), whitespace collapsed; longer than `max`, only its
 * last clauses — from the earliest clause start (after ".", ";", ":", "," outside mathematics) that leaves
 * at most `max` characters, else its last clause whole — marked `\dots` (a step's claim closes its
 * sentence: "Since …, we have $…$"). Whole by construction: never cut inside mathematics or a brace group. Pure.
 */
export function stepQuote(tex: string, max: number = QUOTE_MAX): string {
  const t = balancedBraces(tex
    .replace(/\\label\s*\{[^{}]*\}|\\(?:nonumber|notag)(?![A-Za-z])|\\tag\*?\s*\{[^{}]*\}/gu, "")
    .replace(DISPLAY_ENV, (_a, _e, _s, body: string) => `\\[${displayRows(body)}\\]`)
    .replace(/\$\$([\s\S]*?)\$\$/gu, (_a, b: string) => `\\[${b}\\]`)
    .replace(/\s+/gu, " ")
    .trim());
  if (t.length <= max) return t;
  const { spans } = mathSpans(t);
  // brace depth before each character: a clause never starts inside a group (`{\citetext{…, Theorem 2}}`)
  const depth: number[] = [];
  for (let i = 0, d = 0; i < t.length; i++) {
    depth.push(d);
    if (t[i] === "\\") { depth.push(d); i++; } else if (t[i] === "{") d++; else if (t[i] === "}") d = Math.max(0, d - 1);
  }
  const starts = [...t.matchAll(/[.;:,] (?=\S)/gu)].map((m) => m.index! + 2).filter((i) => !spans.some((s) => s.start < i && i < s.end) && depth[i] === 0 && i < t.length - 1);
  const at = starts.find((i) => t.length - i <= max) ?? starts.at(-1);
  return at === undefined ? t : `\\dots ${t.slice(at)}`;
}

const stop = (t: string): string => {
  const s = t.trim();
  return !s || /[.!?]$/u.test(s) ? s : `${s}.`;
};
/** A field set inside a sentence: its final full stop dropped. */
const inner = (t: string | null | undefined): string => (t ?? "").trim().replace(/[.;]+$/u, "");
const upperFirst = (s: string): string => (/^[a-z]/u.test(s) ? s[0]!.toUpperCase() + s.slice(1) : s);

/** The sentence a defect reads as; `subject` is "This step", or "This clause" for a unit of the
 * statement (the paper prints no proof). Only out_of_domain composes a sentence from its three short
 * slots; every other kind's `detail` is a complete sentence, printed as written — model text is never
 * spliced into a sentence frame (a clause written as a sentence garbled it: "This step needs The …",
 * live DFM 2026-09-26). */
const defectSentence = (kind: DefectKind, d: Record<DefectTextField, string>, subject: string): string =>
  kind === "out_of_domain"
    ? `${subject} uses ${slot(d.uses)}, which the paper assumes only for ${slot(d.assumed_on)}, but applies it to ${slot(d.applied_at)}.`
    : stop(upperFirst(d.detail));

/** A slot's leading article lowercased: it continues a sentence ("uses the order bounds", not "uses The …"). */
const slot = (t: string): string => t.replace(/^(The|A|An)(?= )/u, (w) => w.toLowerCase());

/** A defect's quoted step and its sentence (`subject` names the step), or null when a field its kind
 * needs is empty. */
function defectParts(d: Defect, quoteOf: QuoteOf, keep: (t: string) => string): { unit: string; kind: DefectKind; quote: string; sentence: (subject: string) => string; proof: boolean } | null {
  const f = Object.fromEntries(DEFECT_TEXT_FIELDS.map((k) => [k, inner(keep(d[k] ?? ""))])) as Record<DefectTextField, string>;
  if (KIND_FIELDS[d.kind].some((k) => !f[k])) return null;
  const unit = d.step_unit.trim();
  const printed = quoteOf(unit);
  return { unit, kind: d.kind, quote: printed?.trim() ? stepQuote(printed) : "", sentence: (subject) => defectSentence(d.kind, f, subject), proof: /\/proof\/\d+\/\d+$/u.test(unit) };
}

/** The defects' prose: each step quoted once; a later defect in a step already quoted names it by that
 * defect's letter instead of quoting it again. */
function defectsProse(ds: readonly Defect[], quoteOf: QuoteOf, keep: (t: string) => string): string[] {
  const parts = ds.map((d) => defectParts(d, quoteOf, keep)).filter((x): x is NonNullable<typeof x> => x !== null);
  const first = new Map<string, number>();
  return parts.map((x, i) => {
    const what = x.proof ? "step" : "clause";
    const at = x.quote ? first.get(x.unit) : undefined;
    if (at !== undefined) {
      const same = `the ${what} quoted in (${String.fromCharCode(97 + at)})`;
      return x.kind === "out_of_domain" ? x.sentence(upperFirst(same)) : `In ${same}: ${x.sentence("")}`;
    }
    if (x.quote) first.set(x.unit, i);
    const sentence = x.sentence(x.proof ? "This step" : "This clause");
    return x.quote ? `${quoted(x.quote)} ${sentence}` : sentence;
  });
}

/** A quote from the paper in TeX quotation marks, its displays set as quoted formulas (`\vsDisplay`); a
 * mark next to a display goes inside it, so no line opens or closes on a lone mark. Pure. */
export function quoted(q: string): string {
  // a quote is cut by sentence, so a layout box of the paper (`minipage`) may open in it and close after
  // it: in a note it lays nothing out, and left open it would swallow the rest of the page
  const t = q.replace(/\\begin\s*\{minipage\}(?:\s*\[[^\]]*\])*\s*\{[^{}]*\}|\\end\s*\{minipage\}|\\hfill\b/gu, " ").replace(/[ \t]{2,}/gu, " ").trim();
  // Its displays as the TeX parser finds them (`stepQuote` sets each as `\[…\]`).
  const displays = texRegions(t).filter((r) => r.kind === "display" && t.startsWith("\\[", r.start) && t.startsWith("\\]", r.end - 2));
  let out = t;
  for (const r of [...displays].sort((a, b) => b.start - a.start)) {
    const body = `${r.start === 0 ? "\\mbox{``}" : ""}${t.slice(r.start + 2, r.end - 2).trim()}${r.end === t.length ? "\\mbox{''}" : ""}`;
    out = `${out.slice(0, r.start)}\\vsDisplay{${body}}${out.slice(r.end)}`;
  }
  const opens = displays.some((r) => r.start === 0);
  const closes = displays.some((r) => r.end === t.length);
  return `${opens ? "" : "``"}${out}${closes ? "" : "''"}`;
}

function proseOf(e: OwnerExplanation, quoteOf: QuoteOf, keep: (t: string) => string): NoteProse {
  // Each object and the consequence is its own sentence, printed as written (never spliced).
  const why = [...e.why.objects, e.why.consequence].map((t) => inner(keep(t))).filter(Boolean).map((t) => stop(upperFirst(t))).join(" ");
  return {
    claim: stop(keep(e.claim)),
    what_is_wrong: defectsProse(e.defects, quoteOf, keep),
    why,
    fix: stop(keep(e.fix)),
    gives_up: e.gives_up === null ? null : stop(keep(e.gives_up)) || null,
  };
}

/**
 * The note as the author reads it — the ONE function that makes its prose (design 2026-09-25, P3): each
 * defect is its step quoted from the paper (`stepQuote` of the unit `quoteOf` gives; no quote when the
 * unit is unknown) and its sentence (`defectSentence`); the counterexample (`why`) is its objects and consequence, each a
 * sentence as written; claim, fix and gives up as written. The annotated paper and the V6 report
 * read this. Pure.
 */
export function noteProse(e: OwnerExplanation, quoteOf: QuoteOf = () => null): NoteProse {
  return proseOf(e, quoteOf, (t) => t);
}

/** The runner's instructions to the fixer appended to a finding's detail (`stage_v1_5.ts`): the fixer
 * reads them; an author-facing note quoting the finding leaves them out (`withoutFixerInstructions`). */
export const FIXER_INSTRUCTIONS = {
  noteRewrite: "Keep the ops; write owner_explanation again.",
  consequence: "Restate it or revise its proof so that it follows that repair (consequence_of).",
  // (a label, not an instruction: what follows it is the paper's error, which the author does read)
  openErrorLabel: "The error of the paper this node still answers: ",
} as const;

/** `detail` without the runner's instructions to the fixer (`FIXER_INSTRUCTIONS`): what an author-facing
 * note may quote of a finding. Pure. */
export function withoutFixerInstructions(detail: string): string {
  let out = detail;
  for (const t of Object.values(FIXER_INSTRUCTIONS)) out = out.split(t).join("");
  return out.replace(/[ \t]+\n/gu, "\n").replace(/ {2,}/gu, " ").trim();
}

/** The description of the note's fields every prompt that asks for one shows, beside its schema. */
export const NOTE_FIELDS_TEXT = String.raw`owner_explanation is the error for the paper's AUTHOR, as FIELDS; the runner writes the sentences the author reads from them, each field is printed as written (only out_of_domain's three slots are composed into a sentence), in the paper's notation, never a quotation of the step:
  claim      what the printed statement asserts, one sentence.
  defects    one entry per independent defect of the PRINTED proof (of the printed statement when the paper prints no proof), never about the repair; a phrase of the statement that admits more than one reading (the readings a finding names) is one, kind other, its detail naming the readings, even when the paper's proof settles which is meant:
    kind       out_of_domain: the step uses a property outside where the paper grants it (it reads "This step uses U, which the paper assumes only for A, but applies it to T."); undefined_case: the step is undefined in a case; missing_hypothesis: the step needs a condition the statement does not assume; wrong_constant: the step states a wrong constant, rate or display; dropped_case: the statement omits a case; other.
    step_unit  the id of the failing step's unit as PAPER UNITS shows it ("<env>/proof/<p>/<u>"): a unit of the result's printed proof, or of its statement when the paper prints no proof; the runner quotes that unit.
    uses, assumed_on, applied_at   out_of_domain only (null otherwise): U what the step uses, named as the paper names it; A the domain, class or condition under which the paper grants it (a real condition — when the paper grants it nowhere, the hypotheses the step would have to derive it from; never "nothing" or "not stated"); T where the step applies it instead.
    detail     every other kind (null for out_of_domain): ONE complete sentence saying what is wrong with the step (e.g. "The step divides by $\hat\sigma_0$, which is zero with positive probability.").
  why        a concrete instance where the PRINTED statement fails (for a phrase that admits more than one reading: an instance on which the readings differ): objects — a list, each ONE complete sentence defining one object of the instance ("Let $X \sim U[0,1]$.", "Take $f(x) = x^{-1/2}$."), together satisfying every hypothesis of the statement (or clause) it refutes; consequence — one complete sentence giving the failing quantity or relation against what the statement claims ("Then $E\{f(X)^2\} = \infty$, while the statement bounds it by $4$."). They are printed in order, as written.
  fix        what the repair changes: the display corrected, the hypothesis added (which), or the conclusion weakened (to what).
  gives_up   optional: exactly what the corrected statement no longer claims, nothing else, or null (the JSON value, never a word for it) when nothing is lost — a repair of the proof alone, or one that only adds a hypothesis, gives nothing up.
Every field present; claim, fix, each object and consequence non-empty. No node ids and no words about the checking process (a dependency edge, wiring, depends_on, the core file, transcription, pipeline, referee, fixer) — an edge, a node or a core of the paper's own mathematics is named as the paper names it; the defect fields never mention the repair (no "repair", "fix", "added", "adding", "recorded", "proposed", "suggested", "patch"). An item of a printed list is named by quoting its opening words verbatim, never by a bare number; a purely notational inconsistency is no defect.
${RESULT_NAME_RULE}
${TEX_MATH_RULE}`;

// ---------------------------------------------------------------------------------------------
// Content checks on the fields
// ---------------------------------------------------------------------------------------------


/** Is this a note with fields (not legacy free prose)? */
export function isStructuredExplanation(x: unknown): x is OwnerExplanation {
  return OwnerExplanationSchema.safeParse(x).success;
}

/** Every non-empty TeX field of a note, by its path ("claim", "defects[0].uses", "why.objects[1]", …). */
export function noteFields(e: OwnerExplanation): Array<[string, string]> {
  const out: Array<[string, string | null | undefined]> = [["claim", e.claim]];
  e.defects.forEach((d, i) => DEFECT_TEXT_FIELDS.forEach((f) => out.push([`defects[${i}].${f}`, d[f]])));
  e.why.objects.forEach((o, i) => out.push([`why.objects[${i}]`, o]));
  out.push(["why.consequence", e.why.consequence], ["fix", e.fix], ["gives_up", e.gives_up]);
  return out.filter((x): x is [string, string] => typeof x[1] === "string" && x[1].trim() !== "");
}

const clip = (t: string, n: number): string => (t.length > n ? `${t.slice(0, n - 1)}…` : t);

/** Why one defect breaks the contract (`at` names it; `units`: the unit ids its step may name). */
function defectProblems(d: Defect, at: string, units: ReadonlySet<string> | null | undefined): string[] {
  const out: string[] = [];
  const need = KIND_FIELDS[d.kind];
  for (const f of DEFECT_TEXT_FIELDS) {
    const has = !!d[f]?.trim();
    if (need.includes(f) && !has) out.push(`has no \`${at}.${f}\` — a ${d.kind} defect gives ${need.join(", ")}`);
    if (!need.includes(f) && has) out.push(`gives \`${at}.${f}\`, which a ${d.kind} defect does not carry — set it null (a ${d.kind} defect gives ${need.join(", ")})`);
  }
  const u = d.step_unit.trim();
  if (!u) out.push(`has no \`${at}.step_unit\` — the id of the failing step's unit`);
  else if (units && units.size > 0 && !units.has(u)) out.push(`\`${at}.step_unit\` ("${clip(u, 60)}") is not a unit of this result's statement or proof (or of a result it uses) — give the id of the failing step as PAPER UNITS shows it`);
  return out;
}

/** What a note is checked against. */
export interface NoteContext {
  /** The flattened paper: results are named as it prints them, and its labels are no node ids. */
  paper?: string | null;
  /** The paper's labels, when the paper itself is not given. */
  labels?: PaperLabels;
  /** The unit ids a defect's `step_unit` may name (`ops.ts` `noteUnitIds`); absent, null or empty (a paper
   * without units): not checked. */
  units?: ReadonlySet<string> | null;
  /** false: node ids are left to the rendering backstop (`ownerFacing`) — a note on file as shown, whose
   * parts a runner may have filled (a pending receipt's "Gives up"). Default: checked. */
  ids?: boolean;
}

/**
 * Why `x` breaks the note contract (empty = it does not) — content checks on the fields: the object itself; claim and fix
 * non-empty; `gives_up` null or a real text; at least one defect, each with
 * the fields its kind requires and no other (`KIND_FIELDS`)
 * and a `step_unit` among `ctx.units`; at least one instance object
 * and a non-empty consequence; in every field no node id and TeX mathematics
 * (`texMathProblems`). Pure.
 */
export function noteProblems(x: unknown, ctx: NoteContext = {}): string[] {
  if (typeof x === "string") return ["is free prose — give the fields {claim, defects, why, fix, gives_up}"];
  const parsed = OwnerExplanationSchema.safeParse(x);
  if (!parsed.success) return [`is not the object {claim, defects, why, fix, gives_up} (${parsed.error.issues.slice(0, 3).map((i) => `${i.path.join(".") || "(root)"}: ${i.message}`).join("; ")})`];
  const e = parsed.data;
  const labels = ctx.labels ?? (ctx.paper ? paperLabels(ctx.paper) : undefined);
  const out: string[] = [];
  for (const k of ["claim", "fix"] as const) if (!e[k].trim()) out.push(`has an empty \`${k}\``);
  if (e.gives_up !== null && !e.gives_up.trim()) out.push("has an empty `gives_up` — give what is lost, or null");
  if (e.defects.length === 0) out.push("has no `defects` — one entry per independent defect of the printed proof or statement; a phrase that admits more than one reading is one (kind other, its detail naming the readings)");
  e.defects.forEach((d, i) => out.push(...defectProblems(d, `defects[${i}]`, ctx.units)));
  if (e.why.objects.length === 0) out.push("has no `why.objects` — define each object of the failing instance");
  if (!e.why.consequence.trim()) out.push("has an empty `why.consequence` — state the failing quantity or relation against what the statement claims");
  for (const [field, text] of noteFields(e)) {
    const ids = ownerFacingProblems(text, labels).filter((p) => p.includes("a node id"));
    if (ids.length > 0 && ctx.ids !== false) out.push(`names node ids in \`${field}\` (${ids.join("; ")}) — refer to results as the paper does`);
    out.push(...texMathProblems(text, field));
  }
  return out;
}

/**
 * Why a note's `gives_up` contradicts the repair it explains (empty = it does not): a repair of the proof
 * alone — no corrected statement — keeps the printed statement, so it gives nothing
 * up (C4, user finding 2026-09-25). `repair` null (no patch on file): nothing to compare. Pure.
 */
export function givesUpProblems(e: Pick<OwnerExplanation, "gives_up">, repair: { corrected_statement?: string | null } | null | undefined): string[] {
  if (!repair || e.gives_up === null || !e.gives_up.trim()) return [];
  const proofOnly = !repair.corrected_statement?.trim();
  return proofOnly
    ? [`gives something up in \`gives_up\` ("${clip(e.gives_up.trim(), 80)}") but the repair changes the proof alone (no corrected statement), which keeps the printed statement — \`gives_up\` is exactly what the corrected statement no longer claims, so here it is null`]
    : [];
}

// ---------------------------------------------------------------------------------------------
// The note for the author
// ---------------------------------------------------------------------------------------------

/** One field for the author: its owner-facing sentences, or "" when none survives. */
function fieldText(v: string, labels?: PaperLabels): string {
  return sentences(v).filter((s) => isOwnerFacing(s, labels)).join(" ");
}

/** How a note is laid out for the author. */
export interface NoteOptions {
  omitGivesUp?: boolean;
  labels?: PaperLabels;
  /** The paper's units, for the quoted steps (absent: the sentences alone). */
  quoteOf?: QuoteOf;
}

/** One labelled part of a note; "What is wrong" also as its defects, `(a)`, `(b)`, … when several. */
export interface NotePart {
  label: string;
  text: string;
  items?: string[];
}

/**
 * The prose as labelled parts (`gives_up` omitted when null or when `omitGivesUp`: the caller prints what
 * is lost itself); an empty part is omitted. Several defects are marked `(a)`, `(b)`, …. Pure.
 */
export function proseParts(p: NoteProse, opts: { omitGivesUp?: boolean } = {}): NotePart[] {
  return OWNER_EXPLANATION_LABELS.flatMap(([k, label]): NotePart[] => {
    if (k === "gives_up" && opts.omitGivesUp) return [];
    if (k === "what_is_wrong") {
      const defects = p.what_is_wrong.filter((t) => t.trim()).map((t, i, all) => (all.length > 1 ? `(${String.fromCharCode(97 + i)}) ${t}` : t));
      const items = [...defects, ...(p.why.trim() ? [`Counterexample: ${stop(p.why.trim())}`] : [])];
      return items.length > 0 ? [{ label, text: items.join(" "), items }] : [];
    }
    const t = p[k]?.trim() ?? "";
    return t ? [{ label, text: stop(t) }] : [];
  });
}

/**
 * The note as labelled parts for the author (`proseParts` of `noteProse`), every field it is made from
 * through the owner-facing filter first — the paper's quoted step is the paper's own and is not filtered. Pure.
 */
export function explanationParts(e: OwnerExplanation, opts: NoteOptions = {}): NotePart[] {
  return proseParts(proseOf(e, opts.quoteOf ?? (() => null), (t) => fieldText(t, opts.labels)), opts);
}

/** The note as plain text: "Claim: … What is wrong: … Counterexample: … Proposed fix: … Gives up: …". */
export function renderExplanation(e: OwnerExplanation, opts: NoteOptions = {}): string {
  return explanationParts(e, opts).map((p) => `${p.label}: ${p.text}`).join(" ");
}

/** Is a note present (fields, or non-blank legacy prose)? */
export function hasExplanation(x: OwnerExplanationField | null | undefined): x is OwnerExplanationField {
  return typeof x === "string" ? x.trim().length > 0 : isStructuredExplanation(x);
}

/** The referee's grade of the fixer's explanation of a repair it confirms. */
export const ExplanationClaritySchema = z.object({ grade: z.enum(["ok", "unclear"]), reason: z.string() });
export type ExplanationClarity = z.infer<typeof ExplanationClaritySchema>;

export const EXPLANATION_CLARITY_JSON: Record<string, unknown> = {
  anyOf: [
    {
      type: "object",
      additionalProperties: false,
      required: ["grade", "reason"],
      properties: { grade: { type: "string", enum: ["ok", "unclear"] }, reason: { type: "string" } },
    },
    { type: "null" },
  ],
};

/** When an explanation is clear — the rule the referee grades the fixer's explanation by. */
export const CLARITY_RULE =
  "an explanation is clear when an author of the paper, reading only it, can locate the step and see why it fails";

