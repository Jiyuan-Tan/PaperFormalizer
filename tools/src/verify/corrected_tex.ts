/**
 * The corrected paper's TeX — the pure layer of the V6 bundle (`bundle.ts`).
 *
 * `correctedTex` reads the annotated paper as `planAnnotations` plans it in its corrected view
 * (`AnnotationInput.correctedView`: every block tagged `\vsAt{node}{kind}`) and writes the paper as it
 * reads after the repairs, as plain source the author keeps editing: a printed passage with a
 * correction is replaced by the correction, a correction without a printed passage is inserted, every
 * note is dropped, a reading becomes a remark of the paper at its statement, a condition added to a
 * result the last paragraph of its statement ("Additional condition."), a corrected proof a
 * proof (in place of the printed proof it replaces, when the view marks that one: `\vsPrintedProof`), a corollary a repair split off a result a corollary of the paper after that result, its
 * readings and its proof (in the paper's own corollary environment when it has one, labelled by its
 * node id when numbered; its proof follows it — or, when the paper proves that result elsewhere, follows
 * that proof under a heading naming the corollary, `\vsCorollaryProof`; a block that is a proposition
 * the printed statement bundled in, `\vsSplitProposition`, likewise in the paper's proposition
 * environment, else as a "Proposition" paragraph), and the layout macros of the annotated paper
 * (`\vsFit`, `\vsItem`, `\vsPar`, …) are written out. No `\vs…` macro, colour or word of the review is
 * left. What the mechanics cannot settle (a result with no repair, a correction that found no place, a
 * second proof beside a printed one it could not replace, a label or number a correction removes, a numbered
 * corollary added) is returned as items, each at its line of the output, for the bundle's TODO list —
 * never written into the paper.
 */
import { MATH_ENV, SPLIT_MACROS, conditionParagraph, splitCorollaryBlock, splitMacroKind } from "./annotate_tex.js";
import { UMBRELLA_STATEMENT } from "./core_graph.js";

export type CorrectedItemKind =
  | "not-repaired" // a refuted result with no repair, or one that could not be checked as printed: printed as in the original
  | "unplaced" // a correction whose printed passage was not found, or that could not be typeset
  | "superseded" // a condition's correction inside a statement that is itself restated
  | "no-longer-used" // an assumption or definition no corrected result uses, kept as printed
  | "second-proof" // a corrected proof beside the printed proof it replaces
  | "proof-added" // a corrected proof written after its result: the paper's own proof of it was not located
  | "label-lost" // an equation label of the replaced text the correction does not carry
  | "numbering"; // numbered displays of the replaced text and of the correction differ in number, or a numbered corollary is added

export interface CorrectedItem {
  kind: CorrectedItemKind;
  /** The core node the block belongs to (the technical appendix names it; the prose never does). */
  node: string | null;
  /** 1-based line of the corrected file. */
  line: number;
  detail: string;
}

export interface CorrectedOptions {
  /** The paper has a `proof` environment (amsthm, or its own). */
  proofEnv: boolean;
  /** The paper's corollary environment and whether it is numbered; absent: a corollary is a paragraph. */
  corollaryEnv?: { name: string; numbered: boolean } | null;
  /** Likewise the paper's proposition environment, for a block that is a proposition (`\vsSplitProposition`). */
  propositionEnv?: { name: string; numbered: boolean } | null;
  /** Reference commands the paper's packages do not define: written with the kernel's `\ref` / `\cite`. */
  plain?: { eqref?: boolean; cref?: boolean; autoref?: boolean; natbib?: boolean };
}

const RED = new Set(["vsOriginal", "vsStep"]);
const STRUCK = new Set(["vsStruck", "vsStruckRed"]);
const BLUE = new Set(["vsCorrected", "vsClarified", "vsCorrectedStep", "vsProposed", "vsProposedStep"]);
const NOTE = new Set(["vsNote", "vsRewind", "vsCap"]);
const READING = new Set(["vsReading", "vsReadingOwner", "vsReadingSymbol"]);
const CONDITION = new Set(["vsCondition", "vsConditionOwner"]);
const PROOF = new Set(["vsProof", "vsProposedProof"]);
/** `\vsPrintedProof{begin}` … `{end}`: the printed proof environment a corrected proof replaces. */
const PRINTED = new Set(["vsPrintedProof"]);
/** Arguments each macro of the annotated paper takes. */
const ARITY: Record<string, number> = {
  vsAt: 2, vsOriginal: 1, vsStep: 1, vsStruck: 1, vsStruckRed: 1, vsCorrected: 1, vsClarified: 1, vsCorrectedStep: 1,
  vsProposed: 1, vsProposedStep: 1, vsNote: 1, vsRewind: 1, vsCap: 1, vsReading: 1, vsReadingOwner: 1, vsReadingSymbol: 2, vsCondition: 1, vsConditionOwner: 1,
  vsProof: 1, vsProposedProof: 1, vsPrintedProof: 1, vsCorollary: 3, vsProposedCorollary: 3, vsCorollaryProof: 3, vsSplitProposition: 3, vsProposedSplitProposition: 3, vsSplitPropositionProof: 3, vsFit: 1, vsDisplay: 1, vsFitIn: 2, vsMathEnv: 2, vsItem: 1, vsPar: 0, vsLine: 0, vsSub: 0, vsBreak: 0, vsLabel: 1,
};
const VS = new RegExp(String.raw`\\(${Object.keys(ARITY).sort((a, b) => b.length - a.length).join("|")})(?![A-Za-z])`, "gu");

/** The brace group opening at or after `i` (spaces skipped): its body and the offset past its `}`.
 * TeX's own reading: `\{`, `\}` and `\%` are no delimiters, a comment runs to the end of its line. */
export function readGroup(s: string, i: number): { body: string; end: number } | null {
  let k = i;
  while (k < s.length && /\s/u.test(s[k]!)) k += 1;
  if (s[k] !== "{") return null;
  let depth = 0;
  for (let j = k; j < s.length; j += 1) {
    const c = s[j];
    if (c === "\\") j += 1;
    else if (c === "%") {
      const nl = s.indexOf("\n", j);
      j = nl < 0 ? s.length : nl;
    } else if (c === "{") depth += 1;
    else if (c === "}") {
      depth -= 1;
      if (depth === 0) return { body: s.slice(k + 1, j), end: j + 1 };
    }
  }
  return null;
}

type Token =
  | { t: "text"; text: string }
  | { t: "macro"; name: string; args: string[]; node: string | null; kind: string };

/** `s` as running text and the annotated paper's macros, each with the tag before it. */
function tokens(s: string): Token[] {
  const out: Token[] = [];
  let last = 0;
  let tag: { node: string; kind: string } | null = null;
  VS.lastIndex = 0;
  for (let m = VS.exec(s); m; m = VS.exec(s)) {
    const name = m[1]!;
    const args: string[] = [];
    let end = m.index + m[0].length;
    let ok = true;
    for (let a = 0; a < ARITY[name]!; a += 1) {
      const g = readGroup(s, end);
      if (!g) { ok = false; break; }
      args.push(g.body);
      end = g.end;
    }
    if (!ok) continue; // not ours (no argument where one is due): the paper's text
    if (m.index > last) out.push({ t: "text", text: s.slice(last, m.index) });
    if (name === "vsAt") tag = { node: args[0]!, kind: args[1]! };
    else {
      // A macro without arguments eats the spaces after it, as TeX does.
      if (ARITY[name] === 0) while (end < s.length && (s[end] === " " || s[end] === "\t")) end += 1;
      out.push({ t: "macro", name, args, node: tag?.node ?? null, kind: tag?.kind ?? "" });
      tag = null;
    }
    last = end;
    VS.lastIndex = end;
  }
  if (last < s.length) out.push({ t: "text", text: s.slice(last) });
  return out;
}

/** Math spans of a text a `\label` binds an equation number in. */
function mathSpans(tex: string): Array<[number, number]> {
  const spans: Array<[number, number]> = [];
  for (const m of tex.matchAll(/\\begin\s*\{([^{}]*)\}/gu)) {
    if (!MATH_ENV.test(m[1]!.trim())) continue;
    const end = tex.indexOf(`\\end{${m[1]}}`, m.index);
    spans.push([m.index, end < 0 ? tex.length : end]);
  }
  for (const m of tex.matchAll(/\\\[[\s\S]*?\\\]|\$\$[\s\S]*?\$\$/gu)) spans.push([m.index, m.index + m[0].length]);
  return spans;
}

/** Labels of a text, apart: those binding an equation number and the others. */
export function labelsOf(tex: string): { equation: string[]; other: string[] } {
  const spans = mathSpans(tex);
  const out = { equation: [] as string[], other: [] as string[] };
  for (const m of tex.matchAll(/\\label\s*\{([^{}]*)\}/gu)) {
    (spans.some(([a, b]) => m.index >= a && m.index < b) ? out.equation : out.other).push(m[1]!);
  }
  return out;
}

/** How many displays of a text take an equation number (one per numbered environment; a count for
 * comparing a printed passage with its correction, not the number of equation numbers). */
export function numberedDisplays(tex: string): number {
  return [...tex.matchAll(/\\begin\s*\{([^{}]*)\}/gu)].filter((m) => MATH_ENV.test(m[1]!.trim()) && !m[1]!.trim().endsWith("*") && !/^(?:math|displaymath)$/u.test(m[1]!.trim())).length;
}

/** A text of the run (a correction, a reading, a proof, a note) as plain TeX: the annotated paper's
 * layout macros written out, its other macros reduced to their content. Pure. */
export function laid(s: string): string {
  return     tokens(s)
    .map((k) => {
      if (k.t === "text") return k.text;
      switch (k.name) {
        case "vsFit": case "vsDisplay": return `\n\\[\n${laid(k.args[0]!).trim()}\n\\]\n`;
        case "vsFitIn": return `\n\\[\n${laid(k.args[1]!).trim()}\n\\]\n`;
        case "vsMathEnv": return laid(k.args[1]!);
        case "vsLabel": return `\\label{${k.args[0]!.trim()}}`;
        case "vsItem": return `\n\n\\noindent ${k.args[0]!.trim()}`;
        case "vsPar": case "vsLine": case "vsSub": case "vsBreak": return "\n\n";
        case "vsPrintedProof": return "";
        default: return k.args.map(laid).join(" ");
      }
    })
    .join("")
    .replace(/\n{3,}/gu, "\n\n");
}

/** The displays of a text: numbered math environments, starred ones and \[ … \], in order. */
function displays(tex: string): Array<{ start: number; end: number; env: string | null; body: string }> {
  const out: Array<{ start: number; end: number; env: string | null; body: string }> = [];
  for (const m of tex.matchAll(/\\begin\s*\{([^{}]*)\}/gu)) {
    const env = m[1]!.trim();
    if (!MATH_ENV.test(env) || /^(?:math|displaymath)$/u.test(env)) continue;
    const close = `\\end{${m[1]}}`;
    const end = tex.indexOf(close, m.index);
    if (end < 0 || out.some((d) => m.index < d.end)) continue;
    out.push({ start: m.index, end: end + close.length, env, body: tex.slice(m.index + m[0].length, end) });
  }
  for (const m of tex.matchAll(/(?<!\\)\\\[([\s\S]*?)\\\]/gu)) if (!out.some((d) => m.index >= d.start && m.index < d.end)) out.push({ start: m.index, end: m.index + m[0].length, env: null, body: m[1]! });
  return out.sort((a, b) => a.start - b.start);
}

/**
 * A correction whose displays lost the equation numbers of the text it replaces (a repair's TeX
 * creates no number and no label of its own): when the printed passage has as many numbered displays,
 * each of one number and one label, as the correction has displays, each takes the number and the label
 * of its printed counterpart, in order — so the paper's equation numbers and its references to them
 * stand. Anything else is left as it is (the caller lists the lost labels). Pure.
 */
export function restoreNumbers(printed: string, text: string): string {
  const was = displays(printed).filter((d) => d.env !== null && !d.env.endsWith("*"));
  const now = displays(text);
  if (was.length === 0 || was.length !== now.length || now.some((d) => d.env !== null && !d.env.endsWith("*"))) return text;
  const labels: string[] = [];
  for (const d of was) {
    const ls = labelsDefined(d.body);
    const rows = d.body.split(/\\\\(?![A-Za-z])/u);
    if (ls.length !== 1 || /\\begin\s*\{/u.test(d.body) || rows.filter((r) => !/\\(?:nonumber|notag)\b/u.test(r) && r.trim() !== "").length !== 1) return text;
    labels.push(ls[0]!);
  }
  if (now.some((d) => /\\begin\s*\{|\\label\s*\{/u.test(d.body))) return text;
  let out = text;
  for (let k = now.length - 1; k >= 0; k -= 1) {
    const d = now[k]!;
    const env = d.env === null ? "equation" : d.env.slice(0, -1);
    const rows = d.body.split(/(\\\\(?![A-Za-z])(?:\s*\[[^\]]*\])?)/u);
    // One number per display: every row but the last is unnumbered.
    const body = rows.map((r, i) => (i % 2 === 1 && !/\\(?:nonumber|notag)\b/u.test(rows[i - 1]!) ? `\\nonumber${r}` : r)).join("");
    out = `${out.slice(0, d.start)}\\begin{${env}}\\label{${labels[k]}}${body}\\end{${env}}${out.slice(d.end)}`;
  }
  return out;
}

/** The head of an environment as printed — `\begin{name}` and its `[…]` title, if any — or null. */
function envHead(tex: string): { name: string; head: string } | null {
  const m = /^\\begin\s*\{([^{}]*)\}/u.exec(tex);
  if (!m) return null;
  let end = m[0].length;
  const o = /^[ \t]*\n?[ \t]*\[/u.exec(tex.slice(end));
  if (o) {
    let depth = 0;
    for (let j = end + o[0].length; j < tex.length; j += 1) {
      const c = tex[j];
      if (c === "\\") j += 1;
      else if (c === "{") depth += 1;
      else if (c === "}") depth -= 1;
      else if (c === "]" && depth === 0) {
        end = j + 1;
        break;
      }
    }
  }
  return { name: m[1]!, head: tex.slice(0, end) };
}

const stopped = (t: string): string => (/[.!?]\s*(?:\$\$|\\\])?\s*$/u.test(t.trim()) ? t.trim() : `${t.trim()}.`);

/**
 * The corrected paper's text of one annotated file (see the module doc), what it leaves open, and the
 * lines of each corollary it wrote (statement and proof). Pure.
 */
export function correctedTex(tagged: string, opts: CorrectedOptions): { tex: string; items: CorrectedItem[]; corollaries: Array<{ node: string; from: number; to: number }> } {
  const items: Array<Omit<CorrectedItem, "line"> & { at: number }> = [];
  const plain = (t: string): string => {
    let o = t;
    if (opts.plain?.eqref) o = o.replace(/\\eqref\s*\{([^{}]*)\}/gu, "(\\ref{$1})");
    if (opts.plain?.cref) o = o.replace(/\\[cC]ref(?![A-Za-z])/gu, "\\ref");
    if (opts.plain?.autoref) o = o.replace(/\\autoref(?![A-Za-z])/gu, "\\ref");
    if (opts.plain?.natbib) o = o.replace(/\\cite(?:t|p|author|year)\*?(?![A-Za-z])/gu, "\\cite");
    return o;
  };
  const own = (s: string): string => plain(laid(s)).trim();

  const toks = tokens(tagged);
  const printedBetween = (i: number, j: number): string => toks.slice(i + 1, j).map((t) => (t.t === "text" ? t.text : "")).join("");
  const isMacro = (k: Token | undefined, set: ReadonlySet<string>): k is Extract<Token, { t: "macro" }> => !!k && k.t === "macro" && set.has(k.name);
  const typeset = (t: string): boolean => !t.trimStart().startsWith("\\texttt{");
  const usable = (k: Extract<Token, { t: "macro" }>): boolean => !/; (?:overlapped|unlocated)$/u.test(k.kind) && typeset(k.args[0]!);
  // A printed passage is replaced by the next correction of its node (before that node's next passage).
  const replacedBy = new Map<number, number>();
  toks.forEach((k, i) => {
    if (!isMacro(k, RED)) return;
    for (let j = i + 1; j < toks.length; j += 1) {
      const n = toks[j]!;
      if (n.t !== "macro" || n.node !== k.node) continue;
      if (RED.has(n.name) || STRUCK.has(n.name)) return;
      if (BLUE.has(n.name)) {
        if (usable(n)) replacedBy.set(i, j);
        return;
      }
    }
  });
  const replaces = new Map([...replacedBy].map(([i, j]) => [j, i] as const));
  // A printed proof environment the corrected view marks (nothing of ours inside) is replaced by the next
  // corrected proof of its node written after it, when that one typesets: in its place.
  const swapped = new Map<number, { end: number; proof: number; head: { name: string; head: string } }>();
  toks.forEach((k, i) => {
    if (!isMacro(k, PRINTED) || k.args[0] !== "begin") return;
    const end = toks.findIndex((n, j) => j > i && n.t === "macro");
    const e = toks[end];
    if (!isMacro(e, PRINTED) || e.args[0] !== "end" || e.node !== k.node) return;
    const proof = toks.findIndex((n, j) => j > end && isMacro(n, PROOF) && n.node === k.node);
    const p = toks[proof];
    const head = envHead(printedBetween(i, end));
    if (head && isMacro(p, PROOF) && /; (?:after-proof|steps unplaced)$/u.test(p.kind) && typeset(p.args[0]!)) swapped.set(i, { end, proof, head });
  });
  const written = new Set([...swapped.values()].map((x) => x.proof));

  let out = "";
  const flagged = new Set<string>();
  const item = (kind: CorrectedItemKind, node: string | null, detail: string, once = false): void => {
    if (once && flagged.has(`${kind}\u0000${node}`)) return;
    flagged.add(`${kind}\u0000${node}`);
    items.push({ kind, node, at: out.length, detail });
  };
  /** A block the annotation set after a space: the space goes with it. */
  const dropSpace = (): void => {
    out = out.replace(/[ \t]+$/u, "");
  };
  /** The paragraph before ends here. */
  const gap = (): void => {
    out = `${out.replace(/[ \t]+$/u, "").replace(/\n*$/u, "")}\n\n`;
  };
  const para = (text: string): void => {
    gap();
    out += `${text}\n\n`;
  };
  /** A proof; `of` names what it proves when it does not follow it (a corollary's, after its result's proof). */
  const proof = (text: string, of = ""): void => para(opts.proofEnv ? `\\begin{proof}${of ? `[Proof of ${/[[\]]/u.test(of) ? `{${of}}` : of}]` : ""}\n${text}\n\\end{proof}` : `\\noindent\\textit{Proof${of ? ` of ${of}` : ""}.} ${text}`);
  /** The corrected proof `text` of `node` in place of the printed proof environment `printed`, under its
   * head (its title kept); a label of the printed proof the corrected one does not define, and a change
   * in the number of numbered displays, listed. */
  const replaceProof = (printed: string, head: { name: string; head: string }, node: string | null, text: string): void => {
    const body = restoreNumbers(printed, text);
    gap();
    const was = labelsOf(printed);
    const now = new Set(labelsDefined(body));
    for (const l of [...was.equation, ...was.other].filter((x) => !now.has(x))) item("label-lost", node, `${was.equation.includes(l) ? "the equation labelled" : "the label"} \`${l}\` was in the printed proof, which the corrected proof replaces, and is not in it`);
    const [n0, n1] = [numberedDisplays(printed), numberedDisplays(body)];
    if (n0 !== n1) item("numbering", node, `the printed proof had ${n0} numbered display(s), the corrected proof has ${n1}: equation numbers after this point shift`);
    para(`${head.head}\n${body}\n\\end{${head.name}}`);
  };
  const titleOf = (title: string): string => (typeset(title) ? own(title).replace(/\.$/u, "") : "");
  /** The paper's own text; after a block of ours that ended a paragraph, it starts on its own line. */
  const text = (t: string): void => {
    out += out.endsWith("\n\n") ? t.replace(/^[ \t]*\n?/u, "") : t;
  };
  const spans: Array<{ node: string; at: number; end: number }> = [];
  /** A split-off block's macro: the environment the paper has for its kind, and the kind's word. */
  const splitWords = (macro: string): { env: CorrectedOptions["corollaryEnv"]; word: string } =>
    splitMacroKind(macro) === "proposition" ? { env: opts.propositionEnv, word: "Proposition" } : { env: opts.corollaryEnv, word: "Corollary" };
  const BLOCKS = new Set<string>([SPLIT_MACROS.corollary.block, SPLIT_MACROS.proposition.block]);
  const PROPOSED = new Set<string>([SPLIT_MACROS.corollary.proposed, SPLIT_MACROS.proposition.proposed]);
  const REMOTE = new Set<string>([SPLIT_MACROS.corollary.proof, SPLIT_MACROS.proposition.proof]);
  const corollary = (k: Extract<Token, { t: "macro" }>): void => {
    const [id, title, body] = k.args as [string, string, string];
    // No proof in the block: it is written after the proof of the result (`\vsCorollaryProof`).
    const { statement, proof: follows } = splitCorollaryBlock(body);
    if (!typeset(statement)) {
      item("unplaced", id, `it was not written into the paper (its text does not typeset): ${own(statement).replace(/\s+/gu, " ").slice(0, 200)}`);
      return;
    }
    const name = titleOf(title);
    const { env, word } = splitWords(k.name);
    gap();
    const at = out.length;
    if (env?.numbered) item("numbering", id, `it is a new numbered \`${env.name}\`: the numbers of the results after it that share its counter shift by one`);
    para(
      env
        ? `\\begin{${env.name}}${name ? `[${/[[\]]/u.test(name) ? `{${name}}` : name}]` : ""}${env.numbered ? `\\label{${id}}` : ""}\n${own(statement)}\n\\end{${env.name}}`
        : `\\noindent\\textit{${word}${name ? ` (${name})` : ""}.} ${own(statement)}`,
    );
    if (follows !== null && typeset(follows)) proof(own(follows));
    else if (follows !== null) item("unplaced", id, `its proof was not written into the paper (its text does not typeset): ${own(follows).replace(/\s+/gu, " ").slice(0, 200)}`);
    spans.push({ node: id, at, end: out.trimEnd().length });
  };
  /** The umbrella sentence of the result `node` (the corrected statement at token `at`) by `\ref` to
   * its proposition blocks — the block macros that follow, up to the next text of another result —
   * when the paper numbers its propositions and every block is written; else null (the sentence
   * stands as it is: "The following propositions hold, …"). */
  const umbrellaRefs = (at: number, node: string): string | null => {
    if (!opts.propositionEnv?.numbered) return null;
    const ids: string[] = [];
    for (let j = at + 1; j < toks.length; j += 1) {
      const n = toks[j]!;
      if (n.t !== "macro") continue;
      if ((RED.has(n.name) || BLUE.has(n.name) || STRUCK.has(n.name)) && n.node !== node) break;
      if (n.name !== SPLIT_MACROS.proposition.block) continue;
      const [id, , body] = n.args as [string, string, string];
      if (!typeset(splitCorollaryBlock(body).statement)) return null;
      ids.push(id);
    }
    if (ids.length === 0) return null;
    const ref = (id: string): string => `\\ref{${id}}`;
    if (ids.length === 1) return `Proposition~${ref(ids[0]!)} holds under the conditions stated in it.`;
    return `Propositions~${ids.length === 2 ? `${ref(ids[0]!)} and~${ref(ids[1]!)}` : `${ref(ids[0]!)}--${ref(ids[ids.length - 1]!)}`} hold, each under the conditions stated in it.`;
  };
  // A corollary is written after what belongs to the result it is split from: the readings and the
  // proof set after that result, and the printed proof that opens the text after them.
  let held: Array<Extract<Token, { t: "macro" }>> = [];
  let inProof = false;
  const flush = (): void => {
    held.forEach(corollary);
    held = [];
  };
  for (let i = 0; i < toks.length; i += 1) {
    const k = toks[i]!;
    if (k.t === "text") {
      let t = k.text;
      if (held.length > 0) {
        if (!inProof && /^\s*\\begin\s*\{proof\}/u.test(t)) inProof = true;
        const end = inProof ? /\\end\s*\{proof\}/u.exec(t) : null;
        if (end) {
          text(t.slice(0, end.index + end[0].length));
          t = t.slice(end.index + end[0].length);
          inProof = false;
        }
        if (!inProof && t.trim() !== "") flush();
      }
      text(t);
      continue;
    }
    if (PRINTED.has(k.name)) {
      const s = swapped.get(i);
      if (s) {
        const p = toks[s.proof] as Extract<Token, { t: "macro" }>;
        replaceProof(printedBetween(i, s.end), s.head, p.node, own(p.args[0]!));
        i = s.end;
      }
      continue;
    }
    if (written.has(i)) continue;
    if (held.length > 0 && !inProof && !(READING.has(k.name) || PROOF.has(k.name) || NOTE.has(k.name) || BLOCKS.has(k.name) || PROPOSED.has(k.name))) flush();
    const a = k.args[0] ?? "";
    if (RED.has(k.name)) {
      if (!replacedBy.has(i)) out += a;
      continue;
    }
    if (STRUCK.has(k.name)) {
      item("no-longer-used", k.node, "no corrected result uses this assumption or definition; it is kept as printed", true);
      out += a;
      continue;
    }
    if (BLUE.has(k.name)) {
      dropSpace();
      if (!usable(k)) {
        const why = k.kind.endsWith("; overlapped")
          ? "superseded"
          : "unplaced";
        item(why, k.node, why === "superseded" ? "its correction lies inside a statement that is restated as a whole; the restated statement carries it" : `its correction was not written into the paper (${k.kind.endsWith("; unlocated") ? "the printed passage was not found" : "the corrected text does not typeset"}): ${own(a).replace(/\s+/gu, " ").slice(0, 200)}`);
        continue;
      }
      let text = own(a);
      // An umbrella's sentence names its propositions by their numbers where the paper numbers them.
      if (text.replace(/\s+/gu, " ").trim() === UMBRELLA_STATEMENT) text = umbrellaRefs(i, k.node ?? "") ?? text;
      const from = replaces.get(i);
      if (from !== undefined) {
        const printed = (toks[from] as Extract<Token, { t: "macro" }>).args[0]!;
        text = restoreNumbers(printed, text);
        const was = labelsOf(printed);
        const now = new Set([...labelsOf(text).equation, ...labelsOf(text).other]);
        const keep = was.other.filter((l) => !now.has(l));
        if (keep.length > 0) text = `${keep.map((l) => `\\label{${l}}`).join("")}${text}`;
        for (const l of was.equation.filter((x) => !now.has(x))) item("label-lost", k.node, `the equation labelled \`${l}\` was in the replaced text and is not in the correction`);
        const [n0, n1] = [numberedDisplays(printed), numberedDisplays(text)];
        if (n0 !== n1) item("numbering", k.node, `the replaced text had ${n0} numbered display(s), the correction has ${n1}: equation numbers after this point shift`);
      }
      out += `${out.length > 0 && !/\s$/u.test(out) ? " " : ""}${text}`;
      continue;
    }
    if (NOTE.has(k.name)) {
      dropSpace();
      if (k.kind.startsWith("error (not repaired)")) item("not-repaired", k.node, "the review refuted this result and no repair was adopted; it is printed as in the original", true);
      if (k.kind.startsWith("not determined")) item("not-repaired", k.node, "this result could not be checked as printed (the paper does not determine what is claimed) and no reading or repair was adopted; it is printed as in the original", true);
      continue;
    }
    if (READING.has(k.name)) {
      // The readings set at one place: one remark of the paper.
      const texts: string[] = [];
      const notation = k.name === "vsReadingSymbol";
      let j = i;
      for (; j < toks.length; j += 1) {
        const n = toks[j]!;
        if (isMacro(n, READING) && (n.name === "vsReadingSymbol") === notation) {
          const t = stopped(own(n.args[n.args.length - 1]!));
          if (!texts.includes(t)) texts.push(t);
        } else if (!(n.t === "text" && n.text.trim() === "")) break;
      }
      i = j - 1;
      para(`\\noindent\\textit{Remark${notation ? " (notation)" : ""}.} ${texts.join(" ")}`);
      continue;
    }
    if (CONDITION.has(k.name)) {
      // The conditions set at one place: the last paragraph of the statement they end.
      const texts: string[] = [];
      let j = i;
      for (; j < toks.length; j += 1) {
        const n = toks[j]!;
        if (isMacro(n, CONDITION)) {
          const t = stopped(own(n.args[0]!));
          if (!typeset(n.args[0]!)) item("unplaced", n.node, `the condition added to it was not written into the paper (its text does not typeset): ${t.replace(/\s+/gu, " ").slice(0, 200)}`);
          else if (!texts.includes(t)) texts.push(t);
        } else if (!(n.t === "text" && n.text.trim() === "")) break;
      }
      i = j - 1;
      if (texts.length > 0) {
        gap();
        const next = toks[j];
        out += `${conditionParagraph(texts)}${next?.t === "text" && next.text.startsWith("\n") ? "" : "\n"}`;
      }
      continue;
    }
    if (PROOF.has(k.name)) {
      const how = k.kind.split("; ")[1] ?? "";
      if (how === "after-proof" || how === "steps unplaced") item("second-proof", k.node, "the corrected proof follows the printed proof, which it replaces: remove the superseded one");
      if (how === "no proof located") item("proof-added", k.node, "its corrected proof is written here, after the result; the paper's own proof of it was not located — if the paper prints one elsewhere, remove it");
      proof(own(a));
      continue;
    }
    if (PROPOSED.has(k.name)) {
      // Part of a repair awaiting the owner: not the paper's (the bundle lists it with that repair).
      dropSpace();
      continue;
    }
    if (REMOTE.has(k.name)) {
      // The proof of a block whose result the paper proves here, away from its statement: after
      // that proof, named — by its number when the block has one, else by its title.
      const [id, title, body] = k.args as [string, string, string];
      const name = titleOf(title);
      const { env, word } = splitWords(k.name);
      if (typeset(body)) proof(own(body), env?.numbered ? `${word}~\\ref{${id}}` : `the ${word.toLowerCase()}${name ? ` (${name})` : ""}`);
      else item("unplaced", id, `its proof was not written into the paper (its text does not typeset): ${own(body).replace(/\s+/gu, " ").slice(0, 200)}`);
      continue;
    }
    if (BLOCKS.has(k.name)) {
      // It is set on a line of its own: that line goes with it.
      out = out.replace(/[ \t]*\n?[ \t]*$/u, "");
      held.push(k);
      continue;
    }
    // A layout macro outside a block of ours: written out like inside one.
    out += laid(`\\${k.name}${k.args.map((x) => `{${x}}`).join("")}`);
  }
  flush();
  const lineAt = (at: number): number => out.slice(0, at).split("\n").length;
  return { tex: out, items: items.map(({ at, ...r }) => ({ ...r, line: lineAt(at) })), corollaries: spans.map((c) => ({ node: c.node, from: lineAt(c.at), to: lineAt(c.end) })) };
}

/** Every reference of a text: its label and 1-based line (comment lines left out). */
export function refsIn(tex: string): Array<{ label: string; line: number; command: string }> {
  const out: Array<{ label: string; line: number; command: string }> = [];
  tex.split("\n").forEach((raw, i) => {
    const line = raw.replace(/(^|[^\\])%.*$/u, "$1");
    for (const m of line.matchAll(/\\((?:[cC]|eq|auto|page|name|thm|v)?ref|[cC]refrange)\*?\s*\{([^{}]*)\}/gu)) {
      for (const l of m[2]!.split(",").map((x) => x.trim()).filter(Boolean)) out.push({ label: l, line: i + 1, command: m[1]! });
    }
  });
  return out;
}

/** Every label a text defines. */
export function labelsDefined(tex: string): string[] {
  return [...tex.matchAll(/\\label\s*\{([^{}]*)\}/gu)].map((m) => m[1]!);
}

/** `label → number` of a LaTeX `.aux` file (`\newlabel{l}{{2.1}{7}…}`). */
export function auxLabels(aux: string): Map<string, string> {
  const out = new Map<string, string>();
  for (const m of aux.matchAll(/\\newlabel\{([^{}]*)\}\{\{((?:[^{}]|\{[^{}]*\})*)\}/gu)) out.set(m[1]!, m[2]!.replace(/[{}]/gu, ""));
  return out;
}

/** The 1-based line span of the environment holding `\label{label}`, or null. */
export function envSpanOfLabel(tex: string, label: string): { from: number; to: number } | null {
  const at = tex.indexOf(`\\label{${label}}`);
  if (at < 0) return null;
  const begins = [...tex.slice(0, at).matchAll(/\\begin\s*\{([^{}]*)\}/gu)];
  for (let k = begins.length - 1; k >= 0; k -= 1) {
    const name = begins[k]![1]!;
    if (name === "document" || MATH_ENV.test(name.trim())) continue;
    const end = tex.indexOf(`\\end{${name}}`, begins[k]!.index);
    if (end < at) continue; // closed before the label
    const line = (o: number): number => tex.slice(0, o).split("\n").length;
    return { from: line(begins[k]!.index), to: line(end) };
  }
  return null;
}
