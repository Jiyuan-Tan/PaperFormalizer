/**
 * Repairs as REPLACEMENTS (user decision 2026-09-26: the one operation): `replace {unit, to, tex}` puts
 * `tex` in place of the paper's units `unit`…`to` (one when `to` is null) — sentences, list items or
 * displays of a result's statement or proof, or of an assumption's or a definition's own printed text.
 * An insertion is a replacement of the unit it follows (its text plus the new one); a hypothesis is added
 * by restating the statement with it (the note says which). An op on an item replaces its CONTENT: the
 * item's `\item[…]` head stays. The corrected text is DERIVED by applying the ops to the printed text
 * (`materializeRepair`, deterministic); the annotated paper renders the ops themselves (red = the units
 * replaced, blue = their TeX). Pure.
 */
import { z } from "zod";
import type { CoreStatement } from "../core/schema.js";
import { TEX_STRING_NONEMPTY } from "./owner_text.js";
import { anchorMatches, closedCutEnd, type AnchorSlice, type RefCore } from "./ref_core.js";
import { locatorKey, sentenceSpans } from "./transcription_lint.js";
import type { EnvsJson } from "./types.js";
import { algorithmCommands, isControlLine, type PaperUnits, type Unit } from "./units.js";

const Id = z.string().min(1);
const OptId = z.preprocess((v) => (typeof v === "string" && v.trim() ? v.trim() : undefined), z.string().optional());

export const PatchOpSchema = z.object({ op: z.literal("replace"), unit: Id, to: OptId, tex: z.string().min(1) });
export type PatchOp = z.infer<typeof PatchOpSchema>;

const opJson = (op: string, props: Record<string, unknown>): Record<string, unknown> => ({
  type: "object",
  additionalProperties: false,
  required: ["op", ...Object.keys(props)],
  properties: { op: { type: "string", enum: [op] }, ...props },
});
const ID_JSON = { type: "string" };
const ID_OR_NULL = { type: ["string", "null"] };
/** Strict JSON Schema of an ops list, for the fixer's reply. */
export const OPS_JSON: Record<string, unknown> = {
  type: "array",
  items: opJson("replace", { unit: ID_JSON, to: ID_OR_NULL, tex: TEX_STRING_NONEMPTY }),
};

/** The `proof_note` of a repair whose printed proof stands as it is (the annotated paper shows no proof block). */
export const PROOF_UNCHANGED = "The proof as printed proves the repaired statement; no step changes.";

/** A proof unit's id: `<env>/proof/<p>/<u>`. */
export const isProofUnitId = (id: string): boolean => /\/proof\/\d+\/\d+$/u.test(id);
/** Does the op change a proof (a unit of a proof)? */
export const isProofOp = (op: PatchOp): boolean => isProofUnitId(op.unit);
/** Does the op change the statement's text? */
export const isStatementOp = (op: PatchOp): boolean => !isProofOp(op);
/** Does this repair revise the printed proof? */
export const revisesProof = (r: { ops?: readonly PatchOp[] | null }): boolean => (r.ops ?? []).some(isProofOp);

/** Does `tex` hold a DETAIL (`\vsDetail{…}`, the fixer's): what the referee and the Lean proof need of a
 * proof step beyond the paper's level of detail, shown to the author beside the step (`annotate_tex.ts`)
 * and left out of the corrected paper (`corrected_tex.ts`). Only proof text takes one. */
export const hasDetail = (tex: string): boolean => /\\vsDetail(?![A-Za-z])/u.test(tex);

/** `tex` apart from its details: the text the author reads, and each detail's content, in order (a use
 * whose argument does not close is left in the text). Pure. */
export function splitDetails(tex: string): { text: string; details: string[] } {
  const re = /\\vsDetail(?![A-Za-z])\s*\{/gu;
  const details: string[] = [];
  let text = "";
  let at = 0;
  for (let m = re.exec(tex); m; m = re.exec(tex)) {
    let depth = 1;
    let j = m.index + m[0].length;
    for (; j < tex.length && depth > 0; j += 1) {
      if (tex[j] === "\\") j += 1;
      else if (tex[j] === "{") depth += 1;
      else if (tex[j] === "}") depth -= 1;
    }
    if (depth > 0) break;
    text += tex.slice(at, m.index);
    details.push(tex.slice(m.index + m[0].length, j - 1).trim());
    at = j;
    re.lastIndex = j;
  }
  return { text: text + tex.slice(at), details };
}

/** The TeX an op writes. */
export const opTex = (op: PatchOp): string => op.tex;

const LABEL_RE = /\\label\s*\{([^{}]*)\}/gu;
/** The labels set in a TeX text, in order. */
export const texLabels = (tex: string): string[] => [...tex.matchAll(LABEL_RE)].map((m) => m[1]!.trim());

/** The shortest `from … to` slice of `text` (as `cutSlice` resolves it), as offsets. */
export function sliceOffsets(text: string, slice: AnchorSlice): { start: number; end: number } | null {
  const tos = anchorMatches(text, slice.to);
  const cands: Array<{ start: number; end: number }> = [];
  for (const f of anchorMatches(text, slice.from)) {
    const t = tos.find((m) => m.end >= f.end);
    if (t) cands.push({ start: f.start, end: t.end });
  }
  cands.sort((a, b) => a.end - a.start - (b.end - b.start) || a.start - b.start);
  const best = cands[0];
  return best ? { start: best.start, end: closedCutEnd(text, best.start, best.end) } : null;
}

/** Where a node is printed: its environment, and the body units its passage covers. */
export interface NodePassage {
  env: string;
  units: Unit[];
  /** The node's whole printed text when it is more than its units: an algorithm, with its caption and
   * delimiters (`UnitRegion.algorithm`). The corrected text is this span with the ops applied. */
  span?: { start: number; end: number };
}

/** What resolving a node's passage needs. */
export interface PassageSources {
  units: PaperUnits;
  refs: RefCore | null;
  statements: ReadonlyArray<Pick<CoreStatement, "id"> & { tex_locator?: { file: string; from: number; to: number } | null; depends_on?: readonly string[] }>;
  envs: EnvsJson;
}

/** Where an assumption's or a definition's text sits in `flat.tex` (its reference-core `source`): the
 * environment it is taken from and its span there, or the running-text span (`env` null; an algorithm
 * float taken from the running text: its units' region). Null when the reference core does not locate
 * it. Pure. */
export function sourceSpan(src: PassageSources, node: string): { env: string | null; start: number; end: number } | null {
  const source = (src.refs?.assumptions.find((a) => a.id === node) ?? src.refs?.definitions.find((d) => d.id === node))?.source;
  if (!source) return null;
  if ("prose" in source) {
    const o = sliceOffsets(src.units.flat, source.slice);
    return o ? { env: src.units.file.regions.find((r) => r.algorithm && r.part === "body" && r.start < o.end && o.start < r.end)?.env ?? null, ...o } : null;
  }
  const part = source.region === "proof" ? "proof" : "body";
  const reg = src.units.region(source.env, part);
  const env = src.envs.envs.find((e) => e.id === source.env);
  const text = env ? (part === "proof" ? env.proof : env.body) : null;
  if (!reg || text === null || text === undefined) return null;
  const sp = sentenceSpans(text);
  const o = source.sentences
    ? sp[source.sentences[0] - 1] && sp[source.sentences[1] - 1]
      ? { start: sp[source.sentences[0] - 1]!.start, end: sp[source.sentences[1] - 1]!.end }
      : null
    : source.slice
      ? sliceOffsets(text, source.slice)
      : { start: 0, end: text.length };
  return o ? { env: source.env, start: reg.start + o.start, end: reg.start + o.end } : null;
}

/**
 * The node's printed passage: a statement's environment (its whole body); an assumption's or a
 * definition's own environment units its text covers (`sourceSpan`). Null when none is found: a text in
 * the running prose, or inside the environment of a result, has no passage of its own — it is repaired
 * where the results state it.
 */
export function nodePassage(src: PassageSources, node: string): NodePassage | null {
  if (!src.statements.some((x) => x.id === node)) {
    const own = textUnits(src, node);
    return own && !src.statements.some((st) => statementEnv(src, st.id)?.id === own.env) ? own : null;
  }
  const env = statementEnv(src, node);
  if (!env) return null;
  const all = src.units.unitsOf(env.id);
  return src.units.region(env.id) && all.length > 0 ? { env: env.id, units: all } : null;
}

/** The environment units an assumption's or a definition's text covers (`sourceSpan`), wherever it is
 * printed; null in running prose or when not located. */
function textUnits(src: PassageSources, node: string): NodePassage | null {
  const at = sourceSpan(src, node);
  if (!at?.env) return null;
  const hit = src.units.unitsOf(at.env).filter((u) => u.end > at.start && u.start < at.end);
  if (hit.length === 0) return null;
  return src.units.region(at.env)?.algorithm ? { env: at.env, units: hit, span: { start: at.start, end: at.end } } : { env: at.env, units: hit };
}

/** The environment printing statement `node`: its reference-core environment, else the one its
 * `tex_locator` names. */
function statementEnv(src: PassageSources, node: string): EnvsJson["envs"][number] | undefined {
  const r = src.refs?.statements.find((x) => x.id === node);
  const st = src.statements.find((x) => x.id === node);
  return (r && src.envs.envs.find((e) => e.id === r.env)) ?? (st?.tex_locator ? src.envs.envs.find((e) => locatorKey(e.lines) === locatorKey(st.tex_locator!)) : undefined);
}

/**
 * One op resolved on the paper: `[start, end)` of `flat.tex` replaced by `text` (the materialized text),
 * its first and last unit; `tex` is the op's own TeX as the reader sees it; `part` says whether it changes
 * the statement (or the assumption's, the definition's text) or the proof.
 */
export interface ResolvedOp {
  k: number;
  part: "body" | "proof";
  start: number;
  end: number;
  text: string;
  first: Unit;
  last: Unit;
  tex: string;
}

/** What a repair's ops derive to. */
export interface Materialized {
  /** The corrected statement (null: no op changes the statement). */
  corrected_statement: string | null;
  /** The amended proof (null: no op changes the proof). */
  proof: string | null;
  problems: string[];
}

/** The repair's ops as they bear on one node: its passage, and the proof of its environment. */
export interface RepairScope {
  units: PaperUnits;
  passage: NodePassage | null;
}

const NUMBERED_ENV = /\\begin\{(equation|align|gather|multline|eqnarray|flalign|alignat|xalignat)\}([\s\S]*?)\\end\{\1\}/gu;
/**
 * An op's TeX as the paper prints it: it never creates an equation number or a label (design
 * 2026-09-26) — a numbered display environment becomes starred and a `\label` is dropped, except a label
 * of `keep` (one the units the op replaces carried: that display keeps its number and label). Pure.
 */
export function unnumberedTex(tex: string, keep: ReadonlySet<string> = new Set()): string {
  return tex
    .replace(NUMBERED_ENV, (all, env: string, body: string) => (texLabels(body).some((l) => keep.has(l)) ? all : `\\begin{${env}*}${body}\\end{${env}*}`))
    .replace(LABEL_RE, (all, l: string) => (keep.has(l.trim()) ? all : ""));
}

/** Apply `changes` to `flat.slice(from, to)`. */
function apply(flat: string, from: number, to: number, changes: readonly ResolvedOp[]): string {
  let out = "";
  let at = from;
  for (const c of [...changes].sort((a, b) => a.start - b.start || a.end - b.end || a.k - b.k)) {
    out += flat.slice(at, c.start) + c.text;
    at = Math.max(at, c.end);
  }
  return out + flat.slice(at, to);
}

/** Every op of a repair resolved on the paper (see `ResolvedOp`) and every problem found (each a contract
 * violation the fixer answers; `where` prefixes it). Two ops may not replace overlapping units. Pure. */
export function resolveOps(ops: readonly PatchOp[], scope: RepairScope, where: string): { changes: ResolvedOp[]; problems: string[] } {
  const { units, passage } = scope;
  const problems: string[] = [];
  const bad = (k: number, msg: string): void => void problems.push(`${where}: ops[${k}] (${ops[k]!.op}): ${msg}`);
  const env = passage?.env ?? null;
  const inPassage = new Set((passage?.units ?? []).map((u) => u.id));
  const proofUnits = env ? units.unitsOf(env, "proof") : [];
  const inProof = new Set(proofUnits.map((u) => u.id));
  const listLabel = passage ? `its printed units are ${passage.units[0]!.id} … ${passage.units.at(-1)!.id}` : "the node is not located in the paper";
  const changes: ResolvedOp[] = [];
  ops.forEach((op, k) => {
    const first = units.unitById(op.unit);
    if (!first) return bad(k, `"${op.unit}" is not a unit id of the paper — use an id from the PAPER UNITS block`);
    const isProof = isProofUnitId(op.unit);
    if (isProof ? !inProof.has(op.unit) : !inPassage.has(op.unit)) {
      return bad(k, isProof ? `"${op.unit}" is not a unit of this result's proof${env ? ` (the proof of ${env})` : ""}` : `"${op.unit}" is not a unit of this node's printed text (${listLabel})`);
    }
    const last = op.to ? units.unitById(op.to) : first;
    if (!last) return bad(k, `\`to\` "${op.to}" is not a unit id of the paper`);
    const pool = isProof ? proofUnits : passage!.units;
    const i = pool.indexOf(first);
    const j = pool.indexOf(last);
    if (j < i) return bad(k, `\`to\` "${op.to}" is not a unit at or after "${op.unit}" in the same ${isProof ? "proof" : "text"}`);
    const span = units.spanOf(pool.slice(i, j + 1));
    if (span.partial) return bad(k, `the run "${op.unit}" … "${op.to}" takes some items of a list and not others — replace one item, or the whole list (its first item to its last, and its tex gives the list environment)`);
    if (first === last && first.kind === "item" && /^\s*\\item\b/u.test(op.tex)) bad(k, `"${first.id}" is a list item: \`tex\` is its content — the runner keeps its \\item`);
    // An algorithm is repaired one step at a time: the step's command stays, as an item's \\item does;
    // a control line is replaced by a control line (the block it opens or closes stays).
    if (units.region(first.env, isProof ? "proof" : "body")?.algorithm) {
      if (first.p !== last.p) return bad(k, `the run "${op.unit}" … "${op.to}" crosses steps of an algorithm — replace each step by an op of its own`);
      const control = isControlLine(units.contentOf(first));
      const commands = algorithmCommands(op.tex);
      if (control ? !(first === last && isControlLine(op.tex) && commands.length === 1) : commands.length > 0) {
        return bad(k, control ? `"${first.id}" is a control line of an algorithm: \`tex\` is the one control line that replaces it` : `"${first.id}" is a step of an algorithm: \`tex\` is the step's text, with no step or control command (${commands.map((c) => `\\${c}`).join(", ")}) — the runner keeps the step's command`);
      }
    }
    const tex = unnumberedTex(op.tex.trim(), new Set(texLabels(units.flat.slice(span.start, span.end))));
    changes.push({ k, part: isProof ? "proof" : "body", start: span.start, end: span.end, text: tex, first, last, tex });
  });
  for (const part of ["body", "proof"] as const) {
    const sorted = changes.filter((c) => c.part === part).sort((a, b) => a.start - b.start || a.end - b.end);
    for (let i = 1; i < sorted.length; i += 1) {
      if (sorted[i]!.start < sorted[i - 1]!.end) problems.push(`${where}: ops[${sorted[i - 1]!.k}] and ops[${sorted[i]!.k}] replace overlapping units — give one op for them`);
    }
  }
  return { changes, problems };
}

/** Whitespace-normalized text, without an environment's leading `{}`. */
const flatWords = (t: string): string => t.replace(/^\s*\{\}/u, "").replace(/\s+/gu, " ").trim();

/** The first token of `t` (a word, else one character); `lastToken` the last. Empty when there is none. */
const firstToken = (t: string): string => /^\s*([A-Za-z]+|\S)?/u.exec(t)?.[1] ?? "";
const lastToken = (t: string): string => /([A-Za-z]+|\S)?\s*$/u.exec(t)?.[1] ?? "";

/** A clause boundary: no token, or punctuation. */
const boundary = (tok: string): boolean => tok === "" || /^[.,;:]$/u.test(tok);

/** `text` holds `condition` word for word, bounded on each side by a clause boundary or by the token the
 * paper prints there (`before`, `after`): a qualifier attached to it ("… on N", "if moreover …") rewrites
 * the condition. */
function keptWhole(text: string, condition: string, before: string, after: string): boolean {
  if (!condition) return false;
  for (let at = text.indexOf(condition); at >= 0; at = text.indexOf(condition, at + 1)) {
    const b = lastToken(text.slice(0, at));
    const a = firstToken(text.slice(at + condition.length));
    if ((boundary(b) || b === before) && (boundary(a) || a === after)) return true;
  }
  return false;
}

/** The node's own hypotheses (the assumptions in its `depends_on`; definitions stay wired) whose printed
 * units (`textUnits`, from their `sourceSpan`) lie inside units one of its replacements rewrites, and whose
 * printed text that replacement does not keep word for word in place (`keptWhole`; closing punctuation may
 * differ): the repaired node does not use them — its corrected text says what it assumes instead (the build
 * unwires them, `core_graph.ts`). A hypothesis printed inside a longer sentence that the replacement
 * rewrites around it stays wired. Compared unit by unit, not by raw offsets: a source span may carry the
 * environment's leading `{}` / whitespace that the unit trims. Pure. */
export function supersededNodes(src: PassageSources, node: string, ops: readonly PatchOp[]): string[] {
  const passage = nodePassage(src, node);
  if (!passage) return [];
  const r = resolveOps(ops, { units: src.units, passage }, "");
  if (r.problems.length > 0) return [];
  const spans = r.changes.filter((c) => c.part === "body");
  const deps = src.statements.find((s) => s.id === node)?.depends_on ?? [];
  return deps.filter((d) => {
    if (!src.refs?.assumptions.some((a) => a.id === d)) return false;
    const at = textUnits(src, d);
    if (!at || !at.units.every((u) => spans.some((c) => u.start >= c.start && u.end <= c.end))) return false;
    const span = sourceSpan(src, d);
    if (!span) return true;
    const own = flatWords(src.units.flat.slice(span.start, span.end));
    const printed = own.replace(/[\s.,;:]+$/u, "");
    const before = lastToken(src.units.flat.slice(0, span.start));
    const after = firstToken(own.slice(printed.length) + src.units.flat.slice(span.end));
    // the replacement holding the hypothesis's units must keep it; one elsewhere in the repair does not count
    const holding = spans.filter((c) => at.units.every((u) => u.start >= c.start && u.end <= c.end));
    return !holding.some((c) => keptWhole(flatWords(c.text), printed, before, after));
  });
}

/**
 * The unit ids a node's note may name as a defect's `step_unit` (design 2026-09-25, P3): the units of the
 * node's environment — its statement and its proof — and of the environments of the results it uses
 * directly (a defect may sit in the proof of a result it rests on). Every unit of the paper when the node
 * is not located. Pure.
 */
export function noteUnitIds(src: PassageSources, node: string): Set<string> {
  const own = nodePassage(src, node);
  if (!own) return new Set(src.units.file.units.map((u) => u.id));
  const deps = src.statements.find((s) => s.id === node)?.depends_on ?? [];
  const envs = new Set([own.env, ...deps.flatMap((d) => nodePassage(src, d)?.env ?? [])]);
  return new Set(src.units.file.units.filter((u) => envs.has(u.env)).map((u) => u.id));
}


/** The printed text a statement's passage stands for (`PaperUnits.spanOf`: a list it covers whole is
 * taken with its delimiters; an algorithm whole, `NodePassage.span`). */
export function statementSpan(units: PaperUnits, passage: NodePassage): { start: number; end: number } {
  const s = units.spanOf(passage.units);
  return passage.span ? { start: Math.min(s.start, passage.span.start), end: Math.max(s.end, passage.span.end) } : { start: s.start, end: s.end };
}

/**
 * The corrected statement and the amended proof, derived from `ops` (`resolveOps`), with
 * every problem found. The statement is its passage's text (`statementSpan`) with the ops applied; the
 * proof is the environment's printed proof, the ops applied, trimmed. Pure.
 */
export function materializeRepair(ops: readonly PatchOp[], scope: RepairScope, where: string): Materialized {
  const { units, passage } = scope;
  const r = resolveOps(ops, scope, where);
  if (r.problems.length > 0) return { corrected_statement: null, proof: null, problems: r.problems };
  const stmt = r.changes.filter((c) => c.part === "body");
  const proof = r.changes.filter((c) => c.part === "proof");
  const base = passage ? statementSpan(units, passage) : null;
  const statement = stmt.length > 0 && base ? apply(units.flat, base.start, base.end, stmt).trim() : null;
  let amended: string | null = null;
  const reg = passage ? units.region(passage.env, "proof") : undefined;
  if (proof.length > 0 && reg) amended = apply(units.flat, reg.start, reg.end, proof).trim();
  return { corrected_statement: statement, proof: amended, problems: [] };
}

/** A unit as the fixer's prompt lists it: `[id] (kind) text` (a step of an algorithm with its command). */
function unitLine(units: PaperUnits, u: Unit): string {
  return `[${u.id}]${u.kind === "sentence" ? "" : ` (${u.kind})`} ${units.textOf(u).replace(/\s+/gu, " ").trim()}`;
}

/**
 * The PAPER UNITS block of the fixer's prompt: for each environment printing a node to repair, its
 * printed units (those of each node's passage) and its proof units, each with its id; an algorithm a
 * node to repair uses is listed with it (a wrong step is replaced there). Pure.
 */
export function unitsBlock(src: PassageSources, nodes: readonly string[]): string {
  const byEnv = new Map<string, { nodes: string[]; passage: Set<string>; algorithm: boolean }>();
  const unlocated: string[] = [];
  const used = nodes.flatMap((n) => src.statements.find((s) => s.id === n)?.depends_on ?? []).filter((d) => nodePassage(src, d)?.span);
  for (const node of new Set([...nodes, ...used])) {
    const p = nodePassage(src, node);
    if (!p) {
      if (src.statements.some((s) => s.id === node)) unlocated.push(node);
      continue;
    }
    const e = byEnv.get(p.env) ?? byEnv.set(p.env, { nodes: [], passage: new Set(), algorithm: p.span !== undefined }).get(p.env)!;
    e.nodes.push(node);
    for (const u of p.units) e.passage.add(u.id);
  }
  const lines: string[] = [];
  for (const [env, e] of byEnv) {
    lines.push(`${e.nodes.join(", ")} — printed text (env ${env}${e.algorithm ? "; an algorithm, step by step: each step with its command, which stays" : ""}):`);
    for (const u of src.units.unitsOf(env)) if (e.passage.has(u.id)) lines.push(unitLine(src.units, u));
    const proof = src.units.unitsOf(env, "proof");
    if (proof.length > 0) {
      lines.push(`proof of env ${env}:`);
      for (const u of proof) lines.push(unitLine(src.units, u));
    } else if (!e.algorithm) lines.push(`(the paper prints no proof of env ${env}: give the full proof in \`proof_note\`, no proof ops)`);
    lines.push("");
  }
  if (unlocated.length > 0) lines.push(`${unlocated.join(", ")} — not located in the paper's units (give no ops on their statement).`);
  return lines.join("\n").trim();
}


