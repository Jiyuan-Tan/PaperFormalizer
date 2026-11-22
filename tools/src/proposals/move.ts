// Round-B MOVE: cut a declaration closure out of the paper's Lean and put it into a toolkit
// module, with the paper rewired to import it. `planMove` is the pure text transformation;
// `gateMoveBatch` carries a batch of moves out: journal, writes, one gate; a batch that does not pass
// is undone.
//
// The rules:
//   - every declaration of the item (the accepted one and its `moves_with` closure) is cut from its
//     paper file with its attached doc comment and attribute lines, and re-emitted, in dependency
//     order, in ONE block appended to the target module: `namespace <NS>` (the namespace of the
//     proposed name) → `section` (`@[expose]` when a definition moves, `noncomputable` when the
//     paper had a `noncomputable section` open) → the scope commands the declarations need
//     (`neededContext`: an `open` whose names they use, the `variable` binders they mention and do
//     not bind themselves, the non-linter `set_option`s, `universe`s) → the declarations → `end`s;
//   - names: the accepted declaration takes the proposed name; each closure member keeps its own
//     last component under NS. References to moved declarations are rewritten — in every file of
//     the paper to the new fully-qualified name, in the moved block to the name relative to NS —
//     with resolution following the use site's namespaces and `open`s, so no re-export is needed;
//   - the target module's imports: the modules of the base-library and toolkit constants the moved
//     declarations use (from the scan) and of earlier moves they reference — nothing the paper
//     file imported for its other declarations. `importMode: "source"` (the fallback when that
//     minimal header does not build, e.g. a tactic no used constant brings in) adds the source
//     files' non-paper imports, a paper module import replaced by its own (transitive) non-paper
//     imports. An existing target gains only missing import lines (sorted) and the appended block
//     (and, when a definition moves into a theorem-only module, `@[expose]` on its blanket section);
//   - every paper file that lost a declaration or references a moved one gains
//     `public import <target module>`.
import { createHash } from "node:crypto";
import path from "node:path";
import { insertImportSorted } from "../toolkit/barrels.js";
import { divisionBarrelPath, type ToolkitConfig } from "../toolkit/config.js";
import { lintModuleHeader, formatLayoutFinding } from "../toolkit/layout_lint.js";
import { declarationSpans, forbiddenLeanTokens, identifierTokens, leanImports, type DeclSpan } from "../toolkit/lean_source.js";
import { appendLedgerDeclarations, type LedgerDeclaration } from "../toolkit/ledger.js";
import { maskLeanCommentsAndStrings } from "../shared/lean_mask.js";
import { isLeanModuleFile } from "../shared/lean_syntax.js";
import { axiomsProbeText, restoreJournal, toolkitGateChain, type ApplyDeps, type PromotionJournal, type GateStep } from "./gate.js";
import { parseAxiomReport, CLEAN_AXIOMS } from "../verify/lean_evidence.js";
import { DEFINITION_KINDS } from "./candidate_scan.js";

export interface MoveDecl {
  /** Fully-qualified paper name. */
  from: string;
  /** Fully-qualified toolkit name. */
  to: string;
  kind: string;
}

export interface MoveTarget {
  /** `<lib>/<Division>/<Topic>/<File>.lean`, relative to the toolkit root. */
  rel: string;
  module: string;
  division: string;
  /** One-line overview for a new module. */
  overview: string | null;
  /** Current text of an existing target; null = the module is created. */
  existingText: string | null;
}

export interface MovePlanInput {
  cfg: Pick<ToolkitConfig, "lib" | "papersLib" | "toolkitRoot">;
  /** Every `.lean` file of the paper (run barrel and `tmp/` excluded), and the files of other
   *  papers that may use its declarations (`findImporters`): absolute path → text. */
  paperFiles: ReadonlyMap<string, string>;
  /** For a file of another paper: the declarations that paper declares (they shadow). */
  shadowOf?: (file: string) => ReadonlySet<string> | undefined;
  /** Declarations of the item, dependencies first; the accepted one is `mainFrom`. */
  decls: readonly MoveDecl[];
  mainFrom: string;
  /** The owner's edited docstring for the accepted declaration (replaces the paper's). */
  docstringOverride: string | null;
  /** Used when the accepted declaration has no docstring in the paper. */
  fallbackDocstring: string | null;
  target: MoveTarget;
  /** Moves applied by earlier items (their references are already rewritten in the paper). */
  alreadyMoved: ReadonlyMap<string, { to: string; module: string }>;
  /** Toolkit modules the moved declarations use (scan constants of class `toolkit`). */
  toolkitModulesUsed: readonly string[];
  /** Base-library and toolkit constants the moved declarations use (scan `type_constants` /
   *  `body_constants`): their modules are the target's imports, their names decide which `open`s
   *  the block keeps. Absent: the source files' imports and every `open` (`importMode: "source"`). */
  usedConstants?: ReadonlyArray<{ name: string; module: string }>;
  /** `minimal` (default when `usedConstants` is given): import what the declarations use.
   *  `source`: also the source files' imports (the fallback when the minimal header does not build). */
  importMode?: "minimal" | "source";
  /** Source text of a module (paper modules, for transitive imports), or null. */
  readModule: (module: string) => string | null;
}

export interface MovePlan {
  /** Absolute path → new text, for the target module and every changed paper file. */
  writes: Map<string, string>;
  /** The text each paper file in `writes` (this paper's or another's) held when the plan read it:
   *  `writeMove` writes none of them over a change made since (a live run's edit). */
  read?: Map<string, string>;
  targetAbs: string;
  created: boolean;
  /** The block appended to (or forming the body of) the target module. */
  block: string;
  importsAdded: string[];
}

const nsOf = (name: string) => (name.includes(".") ? name.slice(0, name.lastIndexOf(".")) : "");
const leafOf = (name: string) => name.slice(name.lastIndexOf(".") + 1);

// ─── scope-aware reference rewriting ───────────────────────────────────────

interface Scope { namespaces: string[]; opens: string[] }

/** The namespace chain and `open`ed namespaces in effect at each line of `text`. */
export function lineScopes(text: string): Scope[] {
  const mlines = maskLeanCommentsAndStrings(text).split("\n");
  const stack: Array<{ ns: string | null; opens: string[] }> = [{ ns: null, opens: [] }];
  let pendingIn: string[] = [];
  let pendingLive = false;
  const out: Scope[] = [];
  const openNames = (line: string) => openedIn([line.replace(/\s+in\s*$/, "")]);
  for (const m of mlines) {
    const colZero = m.length > 0 && !/^\s/.test(m);
    if (colZero && pendingLive && !/^(?:\||where\b|deriving\b|termination_by\b|decreasing_by\b)/.test(m)) { pendingIn = []; pendingLive = false; }
    const ns = /^namespace\s+(\S+)/.exec(m);
    const end = /^end\b/.test(m);
    const sec = /^(?:@\[[^\]]*\]\s*)*(?:public\s+)?(?:noncomputable\s+)?section\b/.test(m);
    const open = /^open\b/.test(m);
    if (ns) stack.push({ ns: ns[1]!, opens: [] });
    else if (sec) stack.push({ ns: null, opens: [] });
    else if (end && stack.length > 1) stack.pop();
    else if (open && /\bin\s*$/.test(m)) { pendingIn = openNames(m.trim()); pendingLive = false; }
    else if (open) stack[stack.length - 1]!.opens.push(...openNames(m.trim()));
    else if (colZero && pendingIn.length) pendingLive = true;
    const namespaces = stack.flatMap((s) => (s.ns ? s.ns.split(".") : []));
    out.push({ namespaces, opens: [...stack.flatMap((s) => s.opens), ...pendingIn] });
  }
  return out;
}

/** What a written identifier prefix `p` may denote at a use site. */
function resolutions(p: string, scope: Scope): string[] {
  if (p.startsWith("_root_.")) return [p.slice("_root_.".length)];
  const out: string[] = [];
  for (let k = scope.namespaces.length; k >= 0; k -= 1) out.push([...scope.namespaces.slice(0, k), p].join("."));
  for (const o of scope.opens) out.push(`${o}.${p}`);
  return out;
}

/**
 * Rewrite references to renamed declarations in `text` (comments and strings untouched): an
 * identifier whose longest resolvable dotted prefix denotes a key of `renames` at its use site
 * becomes the new fully-qualified name (a trailing field access is kept); one that already
 * resolves to the new name first, as written, is left alone. `skip` ranges (the
 * header name tokens of moved declarations) are left alone; `scopeOverride` gives the scope of
 * text that was lifted out of its file.
 */
export function rewriteReferences(
  text: string,
  renames: ReadonlyMap<string, string>,
  opts: {
    skip?: ReadonlyArray<[number, number]>; scopeOverride?: Scope; relativeTo?: string;
    /** Declarations the file's own paper declares (another paper that uses the moving one): a name
     *  that denotes one of these first at its use site is that paper's own, never rewritten. */
    shadow?: ReadonlySet<string>;
  } = {},
): { text: string; count: number } {
  if (renames.size === 0) return { text, count: 0 };
  const scopeAt = opts.scopeOverride ? () => opts.scopeOverride! : scopeLookup(text);
  const edits: Array<{ from: number; to: number; text: string }> = [];
  for (const tok of identifierTokens(text)) {
    if (opts.skip?.some(([a, b]) => tok.from >= a && tok.to <= b)) continue;
    const parts = tok.text.split(".");
    const r = resolvedPrefix(parts, scopeAt(tok.from), (n) => renames.has(n), opts.shadow);
    if (!r) continue;
    const rest = parts.slice(r.k).join(".");
    const full = renames.get(r.hit)!;
    // Written as it stands, the name already resolves to the new one first (a declaration's own
    // header, or a sibling's short name, inside the namespace it moved to): nothing to rewrite.
    const now = r.cands.indexOf(full);
    if (now >= 0 && now < r.cands.indexOf(r.hit)) continue;
    // Inside the moved block's own namespace a sibling is written by its short name.
    const name = opts.relativeTo && full.startsWith(`${opts.relativeTo}.`) ? full.slice(opts.relativeTo.length + 1) : full;
    edits.push({ from: tok.from, to: tok.to, text: `${name}${rest ? `.${rest}` : ""}` });
  }
  let out = text;
  for (const e of edits.sort((a, b) => b.from - a.from)) out = out.slice(0, e.from) + e.text + out.slice(e.to);
  return { text: out, count: edits.length };
}

/** Of `names` (fully qualified), those `text` refers to — resolved at each use site as
 *  `rewriteReferences` resolves them (with the same `shadow`), so what this finds is what a move
 *  would rewrite. */
export function referencedNames(text: string, names: ReadonlySet<string>, shadow?: ReadonlySet<string>): Set<string> {
  const out = new Set<string>();
  if (names.size === 0) return out;
  const scopeAt = scopeLookup(text);
  for (const tok of identifierTokens(text)) {
    const r = resolvedPrefix(tok.text.split("."), scopeAt(tok.from), (n) => names.has(n), shadow);
    if (r) out.add(r.hit);
  }
  return out;
}

/** The scope in effect at each offset of `text`. */
function scopeLookup(text: string): (offset: number) => Scope {
  const scopes = lineScopes(text);
  const lineStarts: number[] = [0];
  for (let i = 0; i < text.length; i += 1) if (text[i] === "\n") lineStarts.push(i + 1);
  return (off) => {
    let lo = 0;
    let hi = lineStarts.length - 1;
    while (lo < hi) {
      const mid = (lo + hi + 1) >> 1;
      if (lineStarts[mid]! <= off) lo = mid;
      else hi = mid - 1;
    }
    return scopes[lo]!;
  };
}

/** The longest dotted prefix of an identifier (`parts`) that denotes a `known` name at its use
 *  site: that name, how many parts it spans, and every name the prefix may denote there. A prefix
 *  whose first resolution that exists is a `shadow` name (the file's own paper declares it) denotes
 *  that declaration: none. */
function resolvedPrefix(parts: readonly string[], scope: Scope, known: (n: string) => boolean, shadow?: ReadonlySet<string>): { hit: string; k: number; cands: string[] } | null {
  for (let k = parts.length; k >= 1; k -= 1) {
    const cands = resolutions(parts.slice(0, k).join("."), scope);
    const first = cands.find((c) => known(c) || shadow?.has(c));
    if (first && known(first)) return { hit: first, k, cands };
    if (first) return null;
  }
  return null;
}

// ─── the plan ──────────────────────────────────────────────────────────────

function docComment(doc: string): string {
  return `/-- ${doc.trim()} -/`;
}

/** Replace (or insert) the doc comment of a declaration's span text. */
function withDocstring(spanText: string, headerOffset: number, doc: string): string {
  const pre = spanText.slice(0, headerOffset);
  const m = /\/--[\s\S]*?-\/\s*\n/.exec(pre);
  if (m) return spanText.slice(0, m.index) + `${docComment(doc)}\n` + spanText.slice(m.index + m[0].length);
  return `${docComment(doc)}\n${spanText}`;
}

function hasDocComment(spanText: string, headerOffset: number): boolean {
  return /\/--[\s\S]*?-\//.test(spanText.slice(0, headerOffset));
}

function removeRanges(text: string, ranges: ReadonlyArray<[number, number]>): string {
  let out = text;
  for (const [a, b] of [...ranges].sort((x, y) => y[0] - x[0])) {
    out = out.slice(0, a) + out.slice(b);
    // Drop the blank line that separated the declaration from what follows (no double blank).
    if (out[a] === "\n" && (a === 0 || out.slice(Math.max(0, a - 2), a) === "\n\n")) out = out.slice(0, a) + out.slice(a + 1);
  }
  return out;
}

/** Binder groups of a `variable` command (`(a b : T)`, `{α : Type*}`, `[inst : C α]`, `[C α]`). */
function variableGroups(cmd: string): string[] {
  const body = cmd.replace(/^variable\s*/, "");
  const out: string[] = [];
  const close: Record<string, string> = { "(": ")", "{": "}", "[": "]", "⦃": "⦄" };
  for (let i = 0; i < body.length; i += 1) {
    const open = body[i]!;
    if (!close[open]) continue;
    let depth = 0;
    let j = i;
    for (; j < body.length; j += 1) {
      if (close[body[j]!]) depth += 1;
      else if (Object.values(close).includes(body[j]!)) { depth -= 1; if (depth === 0) break; }
    }
    out.push(body.slice(i, j + 1));
    i = j;
  }
  return out;
}

/** The names a binder group binds: every word before its colon an identifier, else none (an anonymous
 *  instance with a typed binder inside, `[Fact ((m : ℕ) < 5)]`, binds nothing). */
function groupNames(g: string): string[] {
  const inner = g.slice(1, -1);
  const colon = inner.indexOf(" : ") >= 0 ? inner.indexOf(" : ") : inner.indexOf(":");
  if (colon < 0) return [];
  const words = inner.slice(0, colon).trim().split(/\s+/);
  return words.every((n) => /^[\p{L}_][\p{L}\p{N}_'!?]*$/u.test(n)) ? words : [];
}

/** The type of a binder group: after its colon when it binds names, else the whole group. */
const groupType = (g: string): string => (groupNames(g).length ? g.slice(g.indexOf(":") + 1, -1) : g.slice(1, -1));

/** Whether every text that mentions `name` binds it itself (`(name : …)`, `{… name … : …}`), so a
 *  section variable of that name adds nothing. */
function boundByEveryUse(name: string, texts: readonly string[]): boolean {
  const esc = name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const binder = new RegExp(`[({⦃\\[][^:()\\[\\]{}⦃⦄]*(?<![\\p{L}\\p{N}_'])${esc}(?![\\p{L}\\p{N}_'])[^:()\\[\\]{}⦃⦄]*:`, "u");
  const uses = texts.filter((t) => identifierTokens(t).some((x) => x.text === name));
  return uses.length > 0 && uses.every((t) => binder.test(t));
}

/**
 * `open` commands as they must read inside `namespace ns`: a namespace whose first component is
 * also a component of `ns` (`open MeasureTheory` inside `Toolkit.Foundations.MeasureTheory.Integral`)
 * would open the toolkit's namespace of that name and silently not Mathlib's, so it is written
 * `_root_.<name>`. Plain `open A B` and `open scoped A B` lines only; every other line is kept. Pure.
 */
export function rootedOpens(context: readonly string[], ns: string): string[] {
  const own = new Set(ns.split(".").filter(Boolean));
  return context.map((c) => {
    const m = /^(open(?:\s+scoped)?)((?:\s+[A-Za-z_][\w.']*)+)\s*$/.exec(c);
    if (!m) return c;
    const names = m[2]!.trim().split(/\s+/).map((n) => (own.has(n.split(".")[0]!) ? `_root_.${n}` : n));
    return `${m[1]} ${names.join(" ")}`;
  });
}

/**
 * The scope commands a moved block needs, and only those: an `open` keeps the namespaces some used
 * constant is written under by its short name (`usedConstants`; without them, every namespace
 * outside the papers library); `open scoped`, `universe` and non-linter `set_option`s stay; linter
 * `set_option`s go (they change no meaning); a `variable` command keeps only the binder groups the
 * moved declarations mention and do not bind themselves (a named binder whose name occurs in them
 * or in a kept binder's type; an instance binder, named or not, whose variables are all kept) — a section variable over a paper-only
 * type must not follow the declarations into the toolkit.
 */
export function neededContext(
  context: readonly string[],
  texts: readonly string[],
  papersLib: string,
  usedConstants?: ReadonlyArray<{ name: string }>,
  /** The toolkit's own library and the constants the block uses: an `open` of a namespace under
   *  that library stays only when one of them is written relative to it, whatever `usedConstants`
   *  says — a toolkit module is imported only when used, so an unneeded one is an unknown namespace. */
  own?: { lib: string; used: ReadonlyArray<{ name: string }> },
): string[] {
  const tokens = new Set(texts.flatMap((t) => identifierTokens(t).map((x) => x.text.split(".")[0]!)));
  const fullTokens = new Set(texts.flatMap((t) => identifierTokens(t).map((x) => x.text)));
  const allNames = new Set(context.filter((c) => /^variable\b/.test(c)).flatMap((c) => variableGroups(c).flatMap(groupNames)));
  // A namespace is needed when a constant under it is written by the name relative to it.
  const writtenUnder = (ns: string, used: ReadonlyArray<{ name: string }>): boolean =>
    used.some((k) => k.name.startsWith(`${ns}.`) && fullTokens.has(k.name.slice(ns.length + 1)));
  const openNeeded = (ns: string): boolean =>
    own && ns.split(".")[0] === own.lib ? writtenUnder(ns, own.used) : !usedConstants || writtenUnder(ns, usedConstants);
  // The section variables to keep, over every `variable` command at once (Lean's own inclusion rule): a
  // binder whose name the moved text uses and does not bind itself; then, to a fixpoint, a binder whose
  // name a kept binder's type mentions, and an instance binder — named (`[mΩ : MeasurableSpace Ω]`) or
  // not, found by instance search and not by its name — whose type's variables are all kept.
  const allGroups = context.filter((c) => /^variable\b/.test(c)).flatMap(variableGroups);
  const varsOf = (t: string): string[] => identifierTokens(t).map((x) => x.text.split(".")[0]!).filter((x) => allNames.has(x));
  const keptGroups = new Set(allGroups.filter((g) => groupNames(g).some((n) => tokens.has(n) && !boundByEveryUse(n, texts))));
  const keptNames = (): Set<string> => new Set([...keptGroups].flatMap(groupNames));
  for (let grew = true; grew; ) {
    grew = false;
    const kept = keptNames();
    const needed = new Set([...keptGroups].flatMap((g) => varsOf(groupType(g))));
    for (const g of allGroups) {
      if (keptGroups.has(g)) continue;
      const names = groupNames(g);
      const vars = g[0] === "[" ? varsOf(groupType(g)) : [];
      if (names.some((n) => needed.has(n)) || (vars.length > 0 && vars.every((v) => kept.has(v)))) {
        keptGroups.add(g);
        grew = true;
      }
    }
  }
  const out: string[] = [];
  for (const c of context) {
    if (/^open\s+scoped\b/.test(c)) {
      out.push(c);
      continue;
    }
    if (/^open\b/.test(c)) {
      const names = openedIn([c]).filter((n) => n.split(".")[0] !== papersLib && openNeeded(n));
      if (names.length === 0) continue;
      out.push(names.length === openedIn([c]).length ? c : `open ${names.join(" ")}`);
      continue;
    }
    if (/^set_option\s+linter\./.test(c)) continue;
    if (!/^variable\b/.test(c)) {
      out.push(c);
      continue;
    }
    const groups = variableGroups(c);
    const keep = groups.filter((g) => keptGroups.has(g));
    if (keep.length) out.push(`variable ${keep.join(" ")}`);
  }
  return out;
}

function transitiveBaseImports(module: string, input: MovePlanInput, seen = new Set<string>()): string[] {
  if (seen.has(module)) return [];
  seen.add(module);
  const text = input.readModule(module);
  if (text === null) return [];
  const out: string[] = [];
  for (const imp of leanImports(text)) {
    const root = imp.module.split(".")[0];
    if (root === input.cfg.papersLib) out.push(...transitiveBaseImports(imp.module, input, seen));
    else if (root !== input.cfg.lib) out.push(imp.module);
  }
  return out;
}

export function planMove(input: MovePlanInput): MovePlan {
  const { cfg, target } = input;
  const main = input.decls.find((d) => d.from === input.mainFrom);
  if (!main) throw new Error(`move: the accepted declaration ${input.mainFrom} is not among the declarations to move`);
  const ns = nsOf(main.to);
  for (const d of input.decls) {
    if (nsOf(d.to) !== ns) throw new Error(`move: ${d.to} is not in the namespace ${ns || "(root)"} of ${main.to}`);
  }
  // Locate every declaration.
  const spansByFile = new Map<string, DeclSpan[]>();
  for (const [f, t] of input.paperFiles) spansByFile.set(f, declarationSpans(t));
  const located = input.decls.map((d) => {
    const hits = [...spansByFile].flatMap(([f, spans]) => spans.filter((s) => s.name === d.from).map((s) => ({ file: f, span: s })));
    if (hits.length === 0) throw new Error(`move: cannot find the declaration ${d.from} in the paper's Lean files`);
    if (hits.length > 1) throw new Error(`move: ${d.from} is declared more than once (${hits.map((h) => path.basename(h.file)).join(", ")})`);
    return { decl: d, ...hits[0]! };
  });
  const renames = new Map<string, string>([...[...input.alreadyMoved].map(([k, v]) => [k, v.to] as const), ...input.decls.map((d) => [d.from, d.to] as const)]);

  // The moved texts.
  const context: string[] = [];
  let noncomputable = false;
  const texts: string[] = [];
  for (const { decl, file, span } of located) {
    const src = input.paperFiles.get(file)!;
    let text = src.slice(span.from, span.to).replace(/\s+$/, "");
    const headerOffset = src.slice(span.from, span.to).split("\n").slice(0, span.headerLine - span.startLine).join("\n").length + (span.headerLine > span.startLine ? 1 : 0);
    // Header name → the new last component (the block opens namespace NS).
    const headerLine = text.slice(headerOffset).split("\n")[0]!;
    const nameAt = headerOffset + headerLine.search(new RegExp(`(?<=\\s)${span.written.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}(?=[\\s:({\\[]|$)`));
    if (nameAt < headerOffset) throw new Error(`move: cannot find the name of ${decl.from} in its header line`);
    text = text.slice(0, nameAt) + leafOf(decl.to) + text.slice(nameAt + span.written.length);
    const skipTo = nameAt + leafOf(decl.to).length;
    text = rewriteReferences(text, renames, {
      skip: [[nameAt, skipTo]], relativeTo: ns || undefined,
      scopeOverride: { namespaces: span.namespaces.flatMap((n) => n.split(".")), opens: openedIn(span.context) },
    }).text;
    if (decl.from === input.mainFrom) {
      if (input.docstringOverride) text = withDocstring(text, headerOffset, input.docstringOverride);
      else if (!hasDocComment(text, headerOffset) && input.fallbackDocstring) text = withDocstring(text, headerOffset, input.fallbackDocstring);
    }
    for (const c of span.context) if (!context.includes(c)) context.push(c);
    noncomputable ||= span.noncomputable;
    texts.push(text);
  }
  const needed = neededContext(
    context,
    texts,
    cfg.papersLib,
    input.importMode === "source" ? undefined : input.usedConstants,
    input.usedConstants ? { lib: cfg.lib, used: input.usedConstants } : undefined,
  );
  const hasDef = input.decls.some((d) => DEFINITION_KINDS.has(d.kind));
  const secLine = `${hasDef ? "@[expose] " : ""}${noncomputable ? "noncomputable " : ""}section`;
  const block = [
    ...(ns ? [`namespace ${ns}`, ""] : []),
    secLine, "",
    ...(needed.length ? [...rootedOpens(needed, ns), ""] : []),
    texts.join("\n\n"), "",
    "end", "",
    ...(ns ? [`end ${ns}`] : []),
  ].join("\n").replace(/\n*$/, "\n");

  // Imports of the target: the modules of what the declarations use; the source files' imports
  // too in `source` mode (or when the constants used are unknown).
  const sourceFiles = [...new Set(located.map((l) => l.file))];
  const imports = new Set<string>();
  const minimal = input.usedConstants !== undefined && input.importMode !== "source";
  if (minimal) {
    for (const k of input.usedConstants!) {
      const root = k.module.split(".")[0];
      // `Init` is imported by every Lean file; a paper or staging module is never importable.
      if (k.module && root !== "Init" && root !== cfg.papersLib && !(root === cfg.lib && k.module.split(".")[1] === "Staging")) imports.add(k.module);
    }
  } else {
    for (const f of sourceFiles) {
      for (const imp of leanImports(input.paperFiles.get(f)!)) {
        const root = imp.module.split(".")[0];
        if (root === cfg.papersLib) for (const m of transitiveBaseImports(imp.module, input)) imports.add(m);
        else if (root !== cfg.lib) imports.add(imp.module);
      }
    }
  }
  for (const m of input.toolkitModulesUsed) imports.add(m);
  for (const [from, v] of input.alreadyMoved) if (texts.some((t) => t.includes(v.to)) && from) imports.add(v.module);
  imports.delete(target.module);
  const importList = [...imports].sort();
  const targetAbs = path.join(cfg.toolkitRoot, ...target.rel.split("/"));

  let targetText: string;
  let importsAdded: string[];
  if (target.existingText === null) {
    targetText = [
      "module", "",
      ...importList.map((m) => `public import ${m}`), ...(importList.length ? [""] : []),
      "/-!", `# ${target.module}`, "", (target.overview ?? "").trim() || "Results proved in a verified paper.", "-/", "",
      `${hasDef ? "@[expose] " : ""}public section`, "",
      block,
    ].join("\n");
    importsAdded = importList;
  } else {
    let t = target.existingText;
    const have = new Set(leanImports(t).map((i) => i.module));
    importsAdded = importList.filter((m) => !have.has(m));
    for (const m of importsAdded) t = insertImportSorted(t, `public import ${m}`);
    // A definition moving into a theorem-only module: its blanket section becomes
    // `@[expose] public section` (the header contract for def-bearing files; it only widens what
    // the module exports, so nothing that elaborated before stops elaborating).
    if (hasDef) t = t.replace(/^public section[ \t]*$/m, "@[expose] public section");
    targetText = `${t.replace(/\n*$/, "")}\n\n${block}`;
  }

  // Paper edits: cut, rewrite references, import the target.
  const writes = new Map<string, string>([[targetAbs, targetText]]);
  const read = new Map<string, string>();
  const cutByFile = new Map<string, Array<[number, number]>>();
  for (const l of located) cutByFile.set(l.file, [...(cutByFile.get(l.file) ?? []), [l.span.from, l.span.to]]);
  const newRenames = new Map(input.decls.map((d) => [d.from, d.to] as const));
  for (const [f, text] of input.paperFiles) {
    const cut = cutByFile.get(f);
    let t = cut ? removeRanges(text, cut) : text;
    const shadow = input.shadowOf?.(f);
    const r = rewriteReferences(t, newRenames, shadow ? { shadow } : {});
    t = r.text;
    if (cut || r.count > 0) t = insertImportSorted(t, `public import ${target.module}`);
    if (t !== text) { writes.set(f, t); read.set(f, text); }
  }
  return { writes, read, targetAbs, created: target.existingText === null, block, importsAdded };
}

function openedIn(context: readonly string[]): string[] {
  return context.filter((c) => /^open\b/.test(c)).flatMap((c) =>
    c.replace(/^open\s+(?:scoped\s+)?/, "").split(/\s*(?:\(|hiding\b|renaming\b)/)[0]!.trim().split(/\s+/).filter(Boolean));
}

// ─── writing a move, and its gate ──────────────────────────────────────────

/** What writing one planned move needs (`writeMove`). */
interface MoveWriteArgs {
  cfg: ToolkitConfig;
  plan: MovePlan;
  target: MoveTarget;
  ledgerEntries: LedgerDeclaration[];
  /** Index step; null = none (the lakefile check guarantees one on a live toolkit). */
  indexStep: GateStep | null;
}

function sha256(text: string): string {
  return createHash("sha256").update(text, "utf8").digest("hex");
}

/** Why a move's axioms probe fails: a moved declaration that is not clean, or a headline whose
 *  axioms differ from its baseline (or has no line). Null when the probe passes. */
export function moveAxiomsFailure(log: string, moved: readonly string[], baseline: ReadonlyMap<string, readonly string[]>): string | null {
  const names = [...new Set([...moved, ...baseline.keys()])].sort();
  const report = parseAxiomReport(log, names);
  const bad: string[] = [];
  for (const m of moved) {
    const r = report[m]!;
    if (r.error) bad.push(`${m}: ${r.error}`);
    else if (!r.axioms.every((a) => CLEAN_AXIOMS.has(a))) bad.push(`${m} depends on ${r.axioms.join(", ")}`);
  }
  for (const [h, before] of baseline) {
    const r = report[h]!;
    const after = [...r.axioms].sort().join(", ");
    if (r.error) bad.push(`headline ${h}: ${r.error}`);
    else if (after !== [...before].sort().join(", ")) bad.push(`headline ${h}: axioms changed from [${[...before].sort().join(", ")}] to [${after}]`);
  }
  return bad.length ? bad.join("\n  ") : null;
}

/**
 * Of other papers' `modules` — the ones a move is about to rewrite — those that do not build now:
 * one `lake build` per paper, run inside the move's Lake hold before its first write (so it is
 * current, and usually up to date). A failure counts every module asked of that paper: Lake names
 * the module that fails, never one whose import it breaks (in that paper or a third one).
 */
export async function brokenBefore(cfg: Pick<ToolkitConfig, "toolkitRoot">, d: Pick<ApplyDeps, "run">, modules: readonly string[]): Promise<Set<string>> {
  const byPaper = new Map<string, string[]>();
  for (const m of modules) {
    const paper = m.split(".").slice(0, 2).join(".");
    byPaper.set(paper, [...(byPaper.get(paper) ?? []), m]);
  }
  const broken = new Set<string>();
  for (const mods of byPaper.values()) {
    const r = await d.run(`lake build ${mods.join(" ")}`, cfg.toolkitRoot);
    if (r.code !== 0 || r.timedOut) for (const m of mods) broken.add(m);
  }
  return broken;
}

/** Of other papers' modules a move rewrote, those its gate builds: not the ones broken before it. */
export function gatedOthers(modules: readonly string[], broken?: ReadonlySet<string>): string[] {
  return broken ? modules.filter((m) => !broken.has(m)) : [...modules];
}

/**
 * The modules that fail in a `lake build` log, as Lake names them: `✖ [i/n] … <Module>` lines and
 * `error: <path>.lean:<line>` diagnostics (the path read as a module; Lake writes it `./././Papers/…`). Sorted.
 */
export function failingModules(log: string): string[] {
  const failing = new Set<string>();
  for (const m of log.matchAll(/✖\s*\[\d+\/\d+\]\s+\S+\s+([A-Za-z_][\w'.]*)/g)) failing.add(m[1]!);
  for (const m of log.matchAll(/^error: ([^\s:]+)\.lean:\d+/gm)) failing.add(m[1]!.split(/[\\/]/).filter((x) => x !== "" && x !== ".").join("."));
  return [...failing].sort();
}

/** (2026-11-11) The failing modules (`✖` in Lake's log) whose Lean was SIGKILLed (`Lean exited with
 *  code 137`: the OOM killer on a loaded node) — out of resources, not broken. Only 137: 134 (abort)
 *  and 139 (a stack overflow) are Lean's own, deterministic. A job's own log follows its status
 *  line, up to the next one. Sorted. */
export function killedModules(log: string): string[] {
  const killed = new Set<string>();
  let cur: string | null = null;
  for (const line of log.split("\n")) {
    const st = /^([✔⚠✖ℹ])\s*\[\d+\/\d+\]\s+\S+\s+([A-Za-z_][\w'.]*)/.exec(line);
    if (st) { cur = st[1] === "✖" ? st[2]! : null; continue; }
    const ex = /exited with code (\d+)/.exec(line);
    if (cur && ex && Number(ex[1]) === 137) killed.add(cur);
  }
  return [...killed].sort();
}

/**
 * The modules of other papers among `paths` (absolute): files a move rewrote because they use a
 * moved declaration (papers may import each other). The move's gate builds each of them — the
 * module itself, not its whole paper: the rewrite changes only references, never what a module
 * declares. Sorted.
 */
export function otherPaperModules(cfg: Pick<ToolkitConfig, "toolkitRoot" | "papersLib">, paths: Iterable<string>, paperModule: string): string[] {
  const out = new Set<string>();
  for (const abs of paths) {
    const rel = path.relative(cfg.toolkitRoot, abs).split(path.sep);
    if (rel[0] !== cfg.papersLib || rel.length < 2 || !rel[rel.length - 1]!.endsWith(".lean")) continue;
    const mod = rel.join(".").replace(/\.lean$/, "");
    if (mod === paperModule || mod.startsWith(`${paperModule}.`)) continue;
    out.add(mod);
  }
  return [...out].sort();
}

/** What one gate checks: one move, or a batch of moves (of one paper or several). */
export interface GateUnit {
  cfg: ToolkitConfig;
  toolsDir: string;
  /** The papers whose files the moves rewired (each built), and the modules of other papers the
   *  moves rewrote (`otherPaperModules`; each built). Nothing else of the library is. */
  paperModules: readonly string[];
  /** The toolkit modules the moves wrote. */
  targetModules: readonly string[];
  /** Every moved declaration's toolkit name. */
  moved: readonly string[];
  headlineBaseline: ReadonlyMap<string, readonly string[]>;
  probeFile: string;
  indexStep: GateStep | null;
  /** One statement-invariance check per paper. */
  invariance: ReadonlyArray<{ cmd: string; check: () => string | null }>;
}

/**
 * The gate, on the files as they stand: `lake build <lib>`, `lake build <paper>…` (the moving
 * papers, and the modules of other papers the moves rewrote that built before them; the rest of
 * the library is built by the daily library check — `libraryCheck`), statement invariance, `#print axioms` (moved
 * declarations clean, headlines unchanged), module headers, toolkit layout, toolkit index. Stops
 * at the first failing step. The whole chain holds the Lake build lock once (`holdLake`): its
 * commands do not queue again behind other papers' builds between steps.
 */
export async function runGate(u: GateUnit, d: ApplyDeps, logs: string[]): Promise<{ ok: true } | { ok: false; timedOut?: boolean; why: string }> {
  const { cfg } = u;
  await d.writeFile(u.probeFile, axiomsProbeText([...u.targetModules, ...u.paperModules], [...u.moved, ...u.headlineBaseline.keys()]));
  const axiomsStep: GateStep = {
    label: "print axioms",
    cmd: `lake env lean ${u.probeFile.split(path.sep).join("/")}`,
    cwd: cfg.toolkitRoot,
    check: (log) => moveAxiomsFailure(log, u.moved, u.headlineBaseline),
  };
  const chain = toolkitGateChain(cfg, u.toolsDir, u.indexStep, axiomsStep);
  chain.splice(1, 0, { label: "lake build paper", cmd: `lake build ${[...new Set(u.paperModules)].join(" ")}`, cwd: cfg.toolkitRoot });
  // Everything builds: now every statement of the papers and the toolkit must be what it was.
  chain.splice(2, 0, ...u.invariance.map(({ cmd, check }) => ({ label: "statement invariance", cmd, cwd: cfg.toolkitRoot, check: () => check() })));
  return holdLake(d, cfg.toolkitRoot, async () => {
    for (const step of chain) {
      const r = await d.run(step.cmd, step.cwd);
      logs.push(`$ (${step.cwd}) ${step.cmd}\n${r.log}`);
      if (r.timedOut) return { ok: false as const, timedOut: true, why: `gate step '${step.label}' was watchdog-killed (unverified)` };
      const why = r.code !== 0 ? null : step.check?.(r.log) ?? null;
      if (r.code !== 0 || why) return { ok: false as const, why: `gate step '${step.label}' failed${why ? `: ${why}` : ""}` };
    }
    return { ok: true as const };
  });
}

/** Hold the toolkit's Lake build lock across `fn` (reentrant: a gate inside holds it again at once).
 *  A promotion holds it from its first source write to its verdict (and undo): no other paper's
 *  build compiles a toolkit module half-written or not yet gated. */
export function holdLake<T>(d: ApplyDeps, toolkitRoot: string, fn: () => Promise<T>): Promise<T> {
  return d.holdLake ? d.holdLake(toolkitRoot, fn) : fn();
}

/** A promotion's write-ahead journal as it is being written: the journal, its file, and whether
 *  anything was written yet. An existing journal (an earlier attempt) is carried on. */
interface JournalCtx { journal: PromotionJournal; file: string; wrote: boolean }

async function openJournal(file: string, slug: string, d: ApplyDeps): Promise<JournalCtx> {
  const earlier = (await d.exists(file)) ? (JSON.parse(await d.readFile(file)) as PromotionJournal) : null;
  const journal: PromotionJournal = earlier ?? { version: 1, slug, entries: [], created_dirs: [] };
  return { journal, file, wrote: journal.entries.length > 0 || (journal.ledger_added?.length ?? 0) > 0 };
}

const persistJournal = (j: JournalCtx, d: ApplyDeps) => d.writeFile(j.file, `${JSON.stringify(j.journal, null, 2)}\n`);

/**
 * Write one planned move: forbidden-token scan, then the writes (target module, division barrel for
 * a new module, paper files, ledger), each journaled before it is made (the original bytes, every
 * state written; the ledger by the names it records). Throws when the move is refused.
 */
async function writeMove(args: MoveWriteArgs, j: JournalCtx, d: ApplyDeps, logs: string[]): Promise<void> {
  const { cfg, plan } = args;
  const { journal } = j;
  const snap = async (abs: string, afterSha: string | null) => {
    let e = journal.entries.find((x) => x.path === abs);
    if (!e) {
      e = { path: abs, orig: (await d.exists(abs)) ? await d.readFile(abs) : null, after_sha: [] };
      journal.entries.push(e);
    }
    if (afterSha === null) e.generated = true;
    else if (!e.after_sha.includes(afterSha)) e.after_sha.push(afterSha);
    await persistJournal(j, d);
  };
  const write = async (abs: string, text: string) => {
    await snap(abs, sha256(text));
    await d.writeFile(abs, text);
    j.wrote = true;
  };
  // A paper file that changed since the plan read it (a live run saved an edit — another paper's
  // run, mid-way through its own work) is never written over: nothing of this move is written (an
  // earlier move of a batch is undone with it), and the next apply plans from the files as they
  // are. What this move wrote on an earlier attempt is its own.
  for (const [abs, was] of plan.read ?? []) {
    const now = (await d.exists(abs)) ? await d.readFile(abs) : null;
    const ours = now !== null && (journal.entries.find((x) => x.path === abs)?.after_sha.includes(sha256(now)) ?? false);
    if (now !== was && !ours) throw new Error(`${path.relative(cfg.toolkitRoot, abs)} changed since the move was planned (another run's edit?); nothing of the move was written — apply again`);
  }
  // Nothing unproved enters the toolkit; the paper gains nothing unproved either.
  for (const [abs, text] of plan.writes) {
    const now = forbiddenLeanTokens(text);
    if (abs === plan.targetAbs) {
      if (now.length) throw new Error(`the moved block contains ${now.map((h) => `\`${h.token}\` at line ${h.line + 1}`).join(", ")}`);
    } else {
      const orig = journal.entries.find((x) => x.path === abs)?.orig;
      const before = orig !== undefined ? forbiddenLeanTokens(orig ?? "").length : (await d.exists(abs)) ? forbiddenLeanTokens(await d.readFile(abs)).length : 0;
      if (now.length > before) throw new Error(`the rewritten paper file ${path.relative(cfg.toolkitRoot, abs)} gains a sorry / admit / axiom`);
    }
  }
  if (plan.created) {
    const header = lintModuleHeader(args.target.rel, plan.writes.get(plan.targetAbs)!);
    if (header.length) throw new Error(`new module ${args.target.rel} breaks the header contract:\n  ${header.map(formatLayoutFinding).join("\n  ")}`);
    // ours, from an earlier attempt at this move, is written over
    const ours = journal.entries.some((x) => x.path === plan.targetAbs && x.orig === null);
    if (!ours && (await d.exists(plan.targetAbs))) throw new Error(`target ${args.target.rel} appeared since the plan was made`);
    for (let cur = path.dirname(plan.targetAbs); cur.startsWith(`${cfg.toolkitRoot}${path.sep}`) && !(await d.exists(cur)); cur = path.dirname(cur)) {
      if (!journal.created_dirs.includes(cur)) journal.created_dirs.push(cur);
    }
  }
  for (const [abs, text] of plan.writes) await write(abs, text);
  if (plan.created) {
    const barrel = divisionBarrelPath(cfg, args.target.division);
    if (!(await d.exists(barrel))) throw new Error(`division barrel missing: ${path.relative(cfg.toolkitRoot, barrel)}`);
    const text = await d.readFile(barrel);
    if (!isLeanModuleFile(text)) throw new Error(`division barrel is not a module-system file: ${path.relative(cfg.toolkitRoot, barrel)}`);
    await write(barrel, insertImportSorted(text, `public import ${args.target.module}`));
  }
  // The ledger is shared with every paper's decision records: appended under its own lock, never
  // journaled as bytes; the journal lists what the append adds, under that lock, before it writes,
  // so an undo removes just those.
  const { added } = await appendLedgerDeclarations(cfg.ledgerPath, args.ledgerEntries, async (fresh) => {
    const have = new Set((journal.ledger_added ?? []).map((a) => `${a.slug}\u0000${a.name}`));
    journal.ledger_added = [...(journal.ledger_added ?? []), ...fresh.filter((a) => !have.has(`${a.slug}\u0000${a.name}`))];
    await persistJournal(j, d);
    j.wrote = true;
  });
  logs.push(`[ledger] ${added.length} declaration(s) recorded: ${added.map((e) => e.name).join(", ")}`);
  if (args.indexStep) await snap(cfg.indexPath, null);
}

// ─── a batch of moves, one gate ──────────────────────────────────────────────

/** One move of a batch. Nothing in it is tied to one run: a batch may carry several papers' moves. */
export interface BatchMove {
  slug: string;
  proposalId: string;
  paperModule: string;
  decls: readonly MoveDecl[];
  ledgerEntries: LedgerDeclaration[];
  /** Planned when its turn comes, under the caller's lock, from the files as the batch's earlier
   *  moves left them; returns the plan and the target as it then stood. */
  plan: () => Promise<{ plan: MovePlan; target: MoveTarget }>;
  /** Kept on record with the move, for whoever records it after a crash (its run's F4 receipts). */
  cleared?: readonly string[];
  /** Kept on record too: whether the gate checks its paper's statement invariance (a batch of
   *  several papers may check one and not another). Absent: the batch's `checked`. */
  checked?: boolean;
}

/** What a batch journal records beside the files: the moves, whether their gate checks statement
 *  invariance, and whether it passed. */
export interface BatchRecord {
  passed: boolean;
  checked: boolean;
  moves: Array<{ slug: string; proposal_id: string; module: string; decls: Array<{ from: string; to: string }>; cleared?: string[]; checked?: boolean }>;
}

export interface MoveBatchArgs {
  cfg: ToolkitConfig;
  toolsDir: string;
  moves: readonly BatchMove[];
  /** The batch's write-ahead journal; must not exist (a journal left behind is settled first). */
  journalFile: string;
  probeFile: string;
  indexStep: GateStep | null;
  /** The headlines of every paper in the batch, without the declarations that move. */
  headlineBaseline: ReadonlyMap<string, readonly string[]>;
  /** One statement-invariance check per paper of the batch. */
  invariance: ReadonlyArray<{ cmd: string; check: () => string | null }>;
}

type BatchJournal = PromotionJournal & { batch?: BatchRecord };

/** The batch record of a journal, or null (no journal, or a single move's). */
export async function readBatchRecord(file: string, d: Pick<ApplyDeps, "exists" | "readFile">): Promise<BatchRecord | null> {
  if (!(await d.exists(file))) return null;
  return (JSON.parse(await d.readFile(file)) as BatchJournal).batch ?? null;
}

export type BatchOutcome = { ok: boolean; log: string; timedOut?: boolean; restored?: boolean; conflict?: string[] };

/**
 * Write every move of a batch, in order, then gate them all once (`runGate`: the toolkit and each
 * moving paper built once, one invariance check per paper, one axioms probe). All or nothing: when a
 * move is refused, or the gate fails, throws or is watchdog-killed (`timedOut`: the caller escalates
 * it as unverified), every file is restored from the batch journal (`restoreJournal`). On a pass the
 * journal is marked `passed` and kept: the caller reads what passed (`readBatchRecord`) and then
 * drops it.
 */
export async function gateMoveBatch(args: MoveBatchArgs, d: ApplyDeps): Promise<BatchOutcome> {
  const { cfg } = args;
  const logs: string[] = [];
  if (await d.exists(args.journalFile)) throw new Error(`a batch journal is on file (${args.journalFile}); settle it first`);
  const j = await openJournal(args.journalFile, args.moves.map((m) => m.slug).filter((x, i, a) => a.indexOf(x) === i).join(","), d);
  const record: BatchRecord = { passed: false, checked: args.invariance.length > 0, moves: [] };
  (j.journal as BatchJournal).batch = record;
  const undo = async (why: string, timedOut = false): Promise<BatchOutcome> => {
    const r = await restoreJournal(cfg, args.journalFile, d, "batch");
    return {
      ok: false, ...(timedOut ? { timedOut: true } : {}), restored: r?.ok ?? true, ...(r?.conflict ? { conflict: r.conflict } : {}),
      log: `${logs.join("\n\n")}\n\n[batch] ${why}; ${r === null ? "nothing was written" : r.log}`,
    };
  };
  // the Lake lock from the first write to the verdict, the undo included
  return holdLake(d, cfg.toolkitRoot, async (): Promise<BatchOutcome> => {
    const targets: string[] = [];
    // other papers' modules the moves rewrite, and those of them that did not build before
    const others = new Set<string>();
    const broken = new Set<string>();
    try {
      for (const m of args.moves) {
        let { plan, target } = await m.plan();
        const fresh = otherPaperModules(cfg, plan.writes.keys(), m.paperModule).filter((o) => !others.has(o));
        for (const b of await brokenBefore(cfg, d, fresh)) broken.add(b);
        for (const o of fresh) others.add(o);
        // planned again from the files as they are after that build (a live run may have saved meanwhile)
        if (fresh.length) {
          ({ plan, target } = await m.plan());
          // a module only the new plan rewrites was not built before it: rewritten, not gated
          for (const o of otherPaperModules(cfg, plan.writes.keys(), m.paperModule)) if (!others.has(o)) { others.add(o); broken.add(o); }
        }
        if (broken.size) logs.push(`[batch] other papers' modules that did not build before the moves — rewritten, not gated: ${[...broken].sort().join(", ")}`);
        record.moves.push({
          slug: m.slug, proposal_id: m.proposalId, module: target.module, decls: m.decls.map((x) => ({ from: x.from, to: x.to })),
          ...(m.cleared?.length ? { cleared: [...m.cleared] } : {}), ...(m.checked !== undefined ? { checked: m.checked } : {}),
        });
        await persistJournal(j, d);
        await writeMove({ cfg, plan, target, ledgerEntries: m.ledgerEntries, indexStep: args.indexStep }, j, d, logs);
        targets.push(target.module);
        logs.push(`[batch] ${m.proposalId}: written (${m.decls.map((x) => x.to).join(", ")} into ${target.module})`);
      }
    } catch (err) {
      return undo(`apply error: ${err instanceof Error ? err.message : String(err)}`);
    }
    let g: Awaited<ReturnType<typeof runGate>>;
    try {
      g = await runGate({
        cfg, toolsDir: args.toolsDir, paperModules: [...args.moves.map((m) => m.paperModule), ...gatedOthers([...others].sort(), broken)], targetModules: targets,
        moved: args.moves.flatMap((m) => m.decls.map((x) => x.to)), headlineBaseline: args.headlineBaseline,
        probeFile: args.probeFile, indexStep: args.indexStep, invariance: args.invariance,
      }, d, logs);
    } catch (err) {
      return undo(`gate error: ${err instanceof Error ? err.message : String(err)}`);
    }
    if (!g.ok) return undo(g.why, g.timedOut === true);
    record.passed = true;
    await persistJournal(j, d);
    return { ok: true, log: `${logs.join("\n\n")}\n\n[batch] ${args.moves.length} move(s) passed one gate.` };
  });
}
