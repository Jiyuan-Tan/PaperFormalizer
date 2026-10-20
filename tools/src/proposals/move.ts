// Round-B MOVE: cut a declaration closure out of the paper's Lean and put it into a toolkit
// module, with the paper rewired to import it. `planMove` is the pure text transformation;
// `applyMoveItem` carries one item out: journal, writes, gate. A failed gate restores nothing.
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
import { appendDeclarations, emptyLedger, parseLedger, serializeLedger, type LedgerDeclaration } from "../toolkit/ledger.js";
import { maskLeanCommentsAndStrings } from "../shared/lean_mask.js";
import { isLeanModuleFile } from "../shared/lean_syntax.js";
import { axiomsProbeText, toolkitGateChain, type ApplyDeps, type PromotionJournal, type GateStep } from "./gate.js";
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
  /** Every `.lean` file of the paper (run barrel and `tmp/` excluded): absolute path → text. */
  paperFiles: ReadonlyMap<string, string>;
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
  opts: { skip?: ReadonlyArray<[number, number]>; scopeOverride?: Scope; relativeTo?: string } = {},
): { text: string; count: number } {
  if (renames.size === 0) return { text, count: 0 };
  const scopes = opts.scopeOverride ? null : lineScopes(text);
  const lineStarts: number[] = [0];
  for (let i = 0; i < text.length; i += 1) if (text[i] === "\n") lineStarts.push(i + 1);
  const lineAt = (off: number) => {
    let lo = 0;
    let hi = lineStarts.length - 1;
    while (lo < hi) {
      const mid = (lo + hi + 1) >> 1;
      if (lineStarts[mid]! <= off) lo = mid;
      else hi = mid - 1;
    }
    return lo;
  };
  const edits: Array<{ from: number; to: number; text: string }> = [];
  for (const tok of identifierTokens(text)) {
    if (opts.skip?.some(([a, b]) => tok.from >= a && tok.to <= b)) continue;
    const parts = tok.text.split(".");
    const scope = opts.scopeOverride ?? scopes![lineAt(tok.from)]!;
    for (let k = parts.length; k >= 1; k -= 1) {
      const p = parts.slice(0, k).join(".");
      const cands = resolutions(p, scope);
      const hit = cands.find((r) => renames.has(r));
      if (hit) {
        const rest = parts.slice(k).join(".");
        const full = renames.get(hit)!;
        // Written as it stands, the name already resolves to the new one first (a declaration's own
        // header, or a sibling's short name, inside the namespace it moved to): nothing to rewrite.
        const now = cands.indexOf(full);
        if (now >= 0 && now < cands.indexOf(hit)) break;
        // Inside the moved block's own namespace a sibling is written by its short name.
        const name = opts.relativeTo && full.startsWith(`${opts.relativeTo}.`) ? full.slice(opts.relativeTo.length + 1) : full;
        edits.push({ from: tok.from, to: tok.to, text: `${name}${rest ? `.${rest}` : ""}` });
        break;
      }
    }
  }
  let out = text;
  for (const e of edits.sort((a, b) => b.from - a.from)) out = out.slice(0, e.from) + e.text + out.slice(e.to);
  return { text: out, count: edits.length };
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
  const cutByFile = new Map<string, Array<[number, number]>>();
  for (const l of located) cutByFile.set(l.file, [...(cutByFile.get(l.file) ?? []), [l.span.from, l.span.to]]);
  const newRenames = new Map(input.decls.map((d) => [d.from, d.to] as const));
  for (const [f, text] of input.paperFiles) {
    const cut = cutByFile.get(f);
    let t = cut ? removeRanges(text, cut) : text;
    const r = rewriteReferences(t, newRenames);
    t = r.text;
    if (cut || r.count > 0) t = insertImportSorted(t, `public import ${target.module}`);
    if (t !== text) writes.set(f, t);
  }
  return { writes, targetAbs, created: target.existingText === null, block, importsAdded };
}

function openedIn(context: readonly string[]): string[] {
  return context.filter((c) => /^open\b/.test(c)).flatMap((c) =>
    c.replace(/^open\s+(?:scoped\s+)?/, "").split(/\s*(?:\(|hiding\b|renaming\b)/)[0]!.trim().split(/\s+/).filter(Boolean));
}

// ─── carrying one item out ─────────────────────────────────────────────────

export interface MoveItemArgs {
  cfg: ToolkitConfig;
  toolsDir: string;
  slug: string;
  proposalId: string;
  /** The run barrel module (`Papers.<Pascal>`). */
  paperModule: string;
  plan: MovePlan;
  target: MoveTarget;
  decls: readonly MoveDecl[];
  /** Headline declarations and their axioms before any move (`#print axioms` must not change). */
  headlineBaseline: ReadonlyMap<string, readonly string[]>;
  ledgerEntries: LedgerDeclaration[];
  /** Write-ahead journal of this apply (`runs/<slug>/proposals/move_journal.json`). */
  journalFile: string;
  /** Where the axioms probe is written (the run record, never the toolkit). */
  probeFile: string;
  /** Index step; null = none (the lakefile check guarantees one on a live toolkit). */
  indexStep: GateStep | null;
  /** Statement invariance (`invariance.ts`): the scan to run once everything builds, and what it
   *  must show — a failure reason, or null. Absent: not checked (no hashes before the move). */
  invariance?: { cmd: string; check: () => string | null };
  now?: Date;
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

/** What the gate needs of a move: where it went, what must stay true. */
export type MoveGateArgs = Pick<MoveItemArgs, "cfg" | "toolsDir" | "proposalId" | "paperModule" | "target" | "decls" | "headlineBaseline" | "probeFile" | "indexStep" | "invariance">;

/**
 * The gate of a move, on the files as they stand: `lake build <lib>`, `lake build <paper>
 * <papers_lib>`, statement invariance, `#print axioms` (moved declarations clean, headlines
 * unchanged), module headers, toolkit layout, toolkit index. Stops at the first failing step.
 */
export async function runMoveGate(args: MoveGateArgs, d: ApplyDeps, logs: string[]): Promise<{ ok: true } | { ok: false; timedOut?: boolean; why: string }> {
  const { cfg } = args;
  const moved = args.decls.map((x) => x.to);
  await d.writeFile(args.probeFile, axiomsProbeText([args.target.module, args.paperModule], [...moved, ...args.headlineBaseline.keys()]));
  const axiomsStep: GateStep = {
    label: "print axioms",
    cmd: `lake env lean ${args.probeFile.split(path.sep).join("/")}`,
    cwd: cfg.toolkitRoot,
    check: (log) => moveAxiomsFailure(log, moved, args.headlineBaseline),
  };
  const chain = toolkitGateChain(cfg, args.toolsDir, args.indexStep, axiomsStep);
  chain.splice(1, 0, { label: "lake build paper", cmd: `lake build ${args.paperModule} ${cfg.papersLib}`, cwd: cfg.toolkitRoot });
  // Everything builds: now every statement of the paper and the toolkit must be what it was.
  if (args.invariance) {
    const { cmd, check } = args.invariance;
    chain.splice(2, 0, { label: "statement invariance", cmd, cwd: cfg.toolkitRoot, check: () => check() });
  }
  for (const step of chain) {
    const r = await d.run(step.cmd, step.cwd);
    logs.push(`$ (${step.cwd}) ${step.cmd}\n${r.log}`);
    if (r.timedOut) return { ok: false, timedOut: true, why: `gate step '${step.label}' was watchdog-killed (unverified)` };
    const why = r.code !== 0 ? null : step.check?.(r.log) ?? null;
    if (r.code !== 0 || why) return { ok: false, why: `gate step '${step.label}' failed${why ? `: ${why}` : ""}` };
  }
  return { ok: true };
}

/**
 * The gate alone, on a move whose files were left as written after it failed and that the
 * orchestrator has since repaired by hand. Passing drops the journal: the move stands.
 */
export async function verifyKeptMove(args: MoveGateArgs & { journalFile: string }, d: ApplyDeps): Promise<{ ok: boolean; log: string; timedOut?: boolean }> {
  const logs: string[] = [];
  const g = await runMoveGate(args, d, logs);
  if (!g.ok) return { ok: false, ...(g.timedOut ? { timedOut: true } : {}), log: `${logs.join("\n\n")}\n\n[move ${args.proposalId}] ${g.why}; the files are left as they are.` };
  await d.removeFile(args.journalFile);
  return { ok: true, log: `${logs.join("\n\n")}\n\n[move ${args.proposalId}] the repaired move passes the gate.` };
}

/**
 * Apply one planned move: forbidden-token scan, the writes (target module, division barrel for a
 * new module, paper files, ledger), then the gate (`runMoveGate`). Nothing is ever restored: a move
 * that does not pass its gate leaves every file as written (`kept`) for the orchestrator to repair
 * by hand and gate again (`verifyKeptMove`). The journal beside the run records the original bytes
 * of every file the move wrote, for whoever wants to undo it; it is dropped once the gate passes. A
 * second attempt at the same move (another header) writes over the first and keeps its originals.
 */
export async function applyMoveItem(args: MoveItemArgs, d: ApplyDeps): Promise<{ ok: boolean; log: string; timedOut?: boolean; kept?: boolean }> {
  const { cfg, plan } = args;
  const logs: string[] = [];
  const earlier = (await d.exists(args.journalFile)) ? (JSON.parse(await d.readFile(args.journalFile)) as PromotionJournal) : null;
  const journal: PromotionJournal = earlier ?? { version: 1, slug: args.slug, entries: [], created_dirs: [] };
  let wrote = journal.entries.length > 0;
  const persistJournal = () => d.writeFile(args.journalFile, `${JSON.stringify(journal, null, 2)}\n`);
  const snap = async (abs: string, afterSha: string | null) => {
    let e = journal.entries.find((x) => x.path === abs);
    if (!e) {
      e = { path: abs, orig: (await d.exists(abs)) ? await d.readFile(abs) : null, after_sha: [] };
      journal.entries.push(e);
    }
    if (afterSha === null) e.generated = true;
    else if (!e.after_sha.includes(afterSha)) e.after_sha.push(afterSha);
    await persistJournal();
  };
  const write = async (abs: string, text: string) => {
    await snap(abs, sha256(text));
    await d.writeFile(abs, text);
    wrote = true;
  };
  const failed = (why: string, timedOut = false) => ({
    ok: false, ...(wrote ? { kept: true } : {}), ...(timedOut ? { timedOut: true } : {}),
    log: `${logs.join("\n\n")}\n\n[move ${args.proposalId}] ${why}; ${wrote ? "the files are left as written" : "nothing written"}.`,
  });
  try {
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
    const ledgerText = (await d.exists(cfg.ledgerPath)) ? await d.readFile(cfg.ledgerPath) : null;
    const { ledger, added } = appendDeclarations(ledgerText === null ? emptyLedger() : parseLedger(ledgerText, cfg.ledgerPath), args.ledgerEntries);
    if (added.length) await write(cfg.ledgerPath, serializeLedger(ledger));
    logs.push(`[ledger] ${added.length} declaration(s) recorded: ${added.map((e) => e.name).join(", ")}`);
    if (args.indexStep) await snap(cfg.indexPath, null);

    const g = await runMoveGate(args, d, logs);
    if (!g.ok) return failed(g.why, g.timedOut === true);
    await d.removeFile(args.journalFile);
    return { ok: true, log: `${logs.join("\n\n")}\n\n[move ${args.proposalId}] moved ${args.decls.map((x) => x.to).join(", ")} into ${args.target.module}.` };
  } catch (err) {
    return failed(`apply error: ${err instanceof Error ? err.message : String(err)}`);
  }
}
