// A theorem's Lean statement as the rows F5 links and the paper page draws — ONE cut for both.
//
// `leanStatementView` is the nested view of `presentation/lean_structure.ts` with what
// LeanSmith adds to it: a stable id on every row, the chip saying whether a binder is an
// object or a hypothesis, and the statement's own text (what the links are checked against).
// `expandTypeOf` puts, in place of a clause written `type_of% @name`, the statement of the run's
// theorem `name`: its rows are rows of this statement, with ids under the clause's (`r3/r7`). The
// link step and the page call the same two functions, so a row the page draws is a row F5 was asked.
//
// A name is resolved as Lean resolves it, among the declarations of the run's own Lean directory
// that the using file can see (itself and the run's files it imports): in the namespaces
// enclosing the use, innermost first, then in the namespaces opened there.

import { createHash } from "node:crypto";
import path from "node:path";
import { nodeTagAbove } from "../graph/extractor.js";
import { leanNameLeaf, leanSourceDeclarations } from "../presentation/lean_decl_name.js";
import { extractFullDeclSource } from "../presentation/lean_extract.js";
import { DECL_NAME, identifierTokens, normAwareDepths, scanDefinitionSignature, scanPropositionSignature, stripLeadingQuantifier } from "../presentation/lean_statement.js";
import {
  assignRowIds, isDefinitionLike, isPropRecord, isRecordLike, structureDefinitionView, structurePropRecordView, structureStatementView,
  type ConclusionCard, type HypRow, type StructuredView,
} from "../presentation/lean_structure.js";
import { bareHead, topLevelIndex } from "../presentation/lean_structure_tc.js";
import { BINDER_NAMES, binderGroup, CLOSERS, keywordAt, matchedCloseIndex as closeOf, OPENERS, squash } from "../presentation/lean_text.js";
import { maskLeanCommentsAndStrings } from "../shared/lean_mask.js";

export { binderGroup, squash };

export interface LeanRow {
  /** The row's id in the statement's nested view (`r1`, `r2`, … in reading order; `r3/r7` for row
   *  r7 of the theorem whose statement clause r3 is); a statement the view cannot structure keeps
   *  the flat cut's ids (`flatLeanRows`). */
  id: string;
  /** `premise`: what a clause states for itself before concluding (`∀ x, A → B → C`: `∀ x`, `A`,
   *  `B`); `conclusion`: a clause's own line — what it concludes, or the line its parts share. */
  kind: "binder" | "instance" | "premise" | "conclusion";
  /** A binder of the section's `variable`s the statement uses (`withSectionVariables`). */
  section?: true;
  /** Binder names ("" for an instance binder, a premise or a conclusion clause). */
  names: string;
  /** The binder's type, the premise, or the conclusion clause. */
  lean: string;
}

/** The theorem a clause is the statement of (`written`: the clause as the source has it); `node`
 *  when a `-- @node:` tag above it names a core node. */
export interface StatementOf { name: string; kind: string; file: string; line: number; node?: string; written: string }
export interface StatementRow extends HypRow { sub?: StatementCard[] }
/** `of`: the card is a clause written `type_of% @name`; its rows (`hyps`, `sub`) are that theorem's. */
export interface StatementCard extends Omit<ConclusionCard, "hyps" | "sub"> { hyps: StatementRow[]; sub?: StatementCard[]; of?: StatementOf }
/** `statement`: the declaration from its keyword through its goal, comments blanked. `key`: a hash
 *  of it and of every statement `expandTypeOf` put in — what links are written under. */
export interface StatementView extends Omit<StructuredView, "sharedHyps" | "conclusions"> {
  sharedHyps: StatementRow[];
  conclusions: StatementCard[];
  statement: string;
  key: string;
}

const hash = (text: string): string => createHash("sha1").update(text).digest("hex");

// ── chips ────────────────────────────────────────────────────────────────────

/** What a type ends in: past its `∀ …,` headers, its `→` arguments and the brackets around it (the
 *  arrow of a bundled map, `→L[ℝ]`, is no argument arrow). */
export function typeTarget(type: string): string {
  let t = type.trim();
  for (let guard = 0; guard < 32; guard++) {
    if (t.startsWith("(") && closeOf(t) === t.length - 1) { t = t.slice(1, -1).trim(); continue; }
    const q = t.startsWith("∀") ? stripLeadingQuantifier(t) : null;
    if (q) { t = q.rest; continue; }
    const depths = normAwareDepths(t);
    let arrow = -1;
    for (let i = 0; i < t.length; i++) if (t[i] === "→" && depths[i] === 0 && /\s/.test(t[i + 1] ?? "")) arrow = i;
    if (arrow < 0) break;
    t = t.slice(arrow + 1).trim();
  }
  return t;
}

/** A relation or connective outside every bracket, or a quantifier that states something. */
function isPropShaped(target: string): boolean {
  const t = target.replace(/ℝ≥0∞?/g, "ℝ");
  if (/^(?:∃|¬|∀ᵐ|∀ᶠ)/.test(t)) return true;
  const depths = normAwareDepths(t);
  for (let i = 0; i < t.length; i++) {
    if (depths[i] !== 0) continue;
    if ("≤≥≠↔∧∨∈∉⊆⊂≈∣".includes(t[i])) return true;
    if ((t[i] === "<" || t[i] === ">") && /\s/.test(t[i - 1] ?? "") && /\s/.test(t[i + 1] ?? "")) return true;
    if (t[i] === "=" && !":<>=!".includes(t[i - 1] ?? "") && t[i + 1] !== "=" && t[i + 1] !== ">") return true;
  }
  return false;
}

/** A sort, a number system, a container or a bundled map: what an object has for a type. */
const DATA_TARGET = /^(?:(?:Type|Sort|Prop)(?![\w.'])|[ℝℕℤℚℂ]|(?:Set|Finset|Fin|List|Multiset|Option|Matrix|Measure|Bool|Nat|Int|Real|String)(?![\w.']))|→\S|[≃↪]/;

/**
 * Whether the binder `(names : type)` is a hypothesis (`hyp`) or an object (`decl`): a type that is
 * syntactically a proposition is one whatever its name; a type that ends in a sort, a number system
 * or a container is an object whatever its name (`(h : ℝ)`, `(hseq : ℕ → ℝ)`); `known` says what
 * the type's head is when it is a declaration of the paper; otherwise the name decides (`h…`,
 * `_h…`). Pure.
 */
export function binderChip(names: string, type: string, known?: "prop" | "data" | null): "hyp" | "decl" {
  const target = typeTarget(type);
  if (isPropShaped(target)) return "hyp";
  if (DATA_TARGET.test(target)) return "decl";
  if (known) return known === "prop" ? "hyp" : "decl";
  return names.split(/\s+/).every((n) => /^_?h/.test(n)) ? "hyp" : "decl";
}

/**
 * Set every hypothesis row's chip by LeanSmith's rule (the ported structurer reads a name
 * starting with `h` as a hypothesis and any `∀` type as a proposition): a typed binder group by
 * `binderChip` (an implicit one is an object), a `∀` header as the quantifier it is; a hypothesis
 * naming one of `cited` is an assumed external result. Pure but for `view`.
 */
export function chipRows(view: { sharedHyps: StatementRow[]; conclusions: StatementCard[]; defRow?: ConclusionCard }, cited: ReadonlySet<string> = new Set()): void {
  eachRow(view, (row, content) => {
    if ("hyps" in row || /^let[I]?\s|^haveI\s/.test(content)) return;
    const g = binderGroup(content);
    if (g) row.chip = g.open === "(" ? binderChip(g.names, g.type) : "decl";
    else if (content.trimStart().startsWith("∀")) row.chip = forallHeaderChip(content);
    if (row.chip === "hyp" && identifierTokens(g ? g.type : content).some((tok) => cited.has(tok))) row.chip = "cited";
  });
}

/** A `∀` header's chip: `∀ x : T` binds an object, unless `T` is a proposition (`∀ ha : MemLp f p μ`
 *  quantifies over a proof: an assumption); `∀ x ∈ s`, `∀ ε > 0` bind an object. Pure. */
export function forallHeaderChip(header: string): "hyp" | "decl" {
  const m = /^∀\s*([^:(){}[\]⦃⦄,∈<>≤≥≠]+?)\s*:(?!=)([\s\S]*)$/.exec(header.trim());
  return m && BINDER_NAMES.test(m[1].trim()) ? binderChip(m[1].trim(), m[2].replace(/,\s*$/, "").trim()) : "decl";
}

// ── the view and its rows ────────────────────────────────────────────────────

type AnyRow = { id?: string; code: string; head?: string; sub?: AnyCard[] };
type AnyCard = { id?: string; hyps: AnyRow[]; intro?: string; code?: string; sub?: AnyCard[]; of?: { written: string } };

/**
 * Every row of a view in reading order with its text: a hypothesis row — or, when it is cut into
 * rows of its own, those (after its head line, for a named one — unless the head is the name alone,
 * `bareHead`: a label, no row) — then each card's own line (its `intro` when it nests, its `code`
 * when it is a leaf) and its sub-cards. A card with no line of its own (one that only branches, or a clause
 * that is another theorem's statement) is not a row; with `into` false such a clause is visited as
 * the one line the source has, its rows left out.
 */
export function eachRow<R extends AnyRow, C extends AnyCard>(view: { sharedHyps: R[]; conclusions: C[]; defRow?: AnyCard }, visit: (row: R | C, content: string) => void, into = true): void {
  const hyp = (h: AnyRow) => {
    if (!h.sub) { visit(h as R, h.code); return; }
    if (h.head && !bareHead(h.head)) visit(h as R, h.head);
    h.sub.forEach(walk);
  };
  const walk = (c: AnyCard) => {
    if (c.of && !into) { visit(c as C, c.of.written); return; }
    c.hyps.forEach(hyp);
    const content = c.intro ?? c.code;
    if (content) visit(c as C, content);
    (c.sub ?? []).forEach(walk);
  };
  view.sharedHyps.forEach(hyp);
  if (view.defRow?.code) visit(view.defRow as C, view.defRow.code);
  view.conclusions.forEach(walk);
}

/**
 * A row of the nested view as a link row. A bracketed group `(names : type)` is a binder and
 * `[…]` an instance; anything else a clause lifted for itself — a `∀ x` header, a `let`, a premise
 * (a bracketed premise has no identifier-only name part before a top-level colon).
 */
function viewRow(id: string, hyp: boolean, code: string, head: boolean): LeanRow {
  const lean = code.replace(/\s+/g, " ").trim();
  if (!hyp) return { id, kind: "conclusion", names: "", lean };
  // a named hypothesis with parts: its head line `(h : ∀ k,`
  const named = head ? /^\(\s*([^:]+?)\s*:(?!=)\s*([\s\S]*)$/.exec(lean) : null;
  if (named) return { id, kind: "binder", names: named[1], lean: named[2] };
  if (lean[0] === "[" && closeOf(lean) === lean.length - 1) return { id, kind: "instance", names: "", lean: lean.slice(1, -1).trim() };
  const g = binderGroup(lean);
  return g ? { id, kind: "binder", names: g.names, lean: g.type } : { id, kind: "premise", names: "", lean };
}

/** A declaration's keyword and name, its universe parameters with it: up to where its binders start. */
const HEAD = String.raw`(?:theorem|lemma|def)\s+${DECL_NAME}\s*(?:\.\{[^}]*\}\s*)?`;
/** A statement (`StatementView.statement`) past its keyword and name: its binders and its goal. */
export const statementBody = (statement: string): string => statement.replace(new RegExp(String.raw`^\s*${HEAD}`), "");

/**
 * The statement as its nested view (shared hypothesis rows, then conclusion cards that carry their
 * own hypothesis rows and split further), every row stamped with its id and chip — the ONE source of
 * row identity for the links and the page. `cited`: the names of the run's cited results (a
 * hypothesis assuming one is chipped so). Null when the statement does not structure. Pure.
 */
export function leanStatementView(source: string, cited: ReadonlySet<string> = new Set()): StatementView | null {
  const scan = scanPropositionSignature(source);
  const view = scan ? structureStatementView(source) : null;
  if (!scan || !view) return null;
  assignRowIds(view);
  chipRows(view, cited);
  const head = scan.cleaned.slice(0, scan.telescopeStart).search(new RegExp(String.raw`\b${HEAD}$`));
  const statement = scan.cleaned.slice(Math.max(0, head), scan.conclusionEnd < 0 ? undefined : scan.conclusionEnd).trim();
  // the key is the statement's, not its name's: a theorem renamed keeps its links
  const body = scan.cleaned.slice(scan.telescopeStart, scan.conclusionEnd < 0 ? undefined : scan.conclusionEnd);
  return Object.assign(view, { statement, key: hash(squash(body)) });
}

/** The rows of a nested view in reading order, as link rows; a row inside a hypothesis's parts is a
 *  `premise`, not a conclusion. Pure. */
export function viewRows(view: { sharedHyps: StatementRow[]; conclusions: StatementCard[]; defRow?: ConclusionCard }): LeanRow[] {
  const inHyp = new Set<object>();
  const under = (c: StatementCard) => { inHyp.add(c); c.hyps.forEach((h) => h.sub?.forEach(under)); c.sub?.forEach(under); };
  const scan = (c: StatementCard) => { c.hyps.forEach((h) => h.sub?.forEach(under)); c.sub?.forEach(scan); };
  view.sharedHyps.forEach((h) => h.sub?.forEach(under));
  view.conclusions.forEach(scan);
  const out: LeanRow[] = [];
  eachRow(view, (row, content) => {
    if (!row.id) return;
    const hyp = !("hyps" in row);
    const r = viewRow(row.id, hyp, content, hyp && (row as StatementRow).head === content);
    out.push((row as StatementRow).section ? { ...r, section: true } : !hyp && inHyp.has(row) ? { ...r, kind: "premise" } : r);
  });
  return out;
}

/** A Prop-valued declaration's view: `key`, a hash of its rows — what its links are written under. */
export interface DeclView extends StructuredView { key: string }

/**
 * A declaration's source as a Prop-valued definition (`def`/`abbrev … : Prop`) or record
 * (`structure`/`class … : Prop`) with its view, or null when it is neither: its parameters, the row
 * of its name, then its clauses (a record's fields), every row stamped with its id and chip as a
 * statement's are — the rows F5 links and the page draws. Pure.
 */
export function propDeclView(source: string): { role: "definition" | "assumption"; view: DeclView | null } | null {
  // `Sort 0` is `Prop` written out (the spelling the Lean stages give a cited result's statement): read as `Prop`
  if (isDefinitionLike(source)) source = source.replace(/:\s*Sort\s+0\s*:=/, ": Prop :=");
  const rowed = (view: StructuredView | null): DeclView | null => {
    if (!view) return null;
    assignRowIds(view);
    chipRows(view);
    return Object.assign(view, { key: hash(viewRows(view).map((r) => `${r.id}:${r.names}:${squash(r.lean)}`).join("\n")) });
  };
  if (isDefinitionLike(source)) {
    const def = scanDefinitionSignature(source);
    if (!def || def.scan.conclusionText.replace(/\s+/g, "") !== "Prop") return null;
    return { role: "definition", view: rowed(structureDefinitionView(source)) };
  }
  if (isRecordLike(source) && isPropRecord(source)) return { role: "assumption", view: rowed(structurePropRecordView(source)) };
  return null;
}

// ── the run's declarations, and what a name written in one of them means ─────

/** A declaration as its file has it: `ns` the namespace it is declared in, `scopes` the namespaces
 *  Lean looks a name written there up in (those enclosing it, innermost first, then none), `opened`
 *  the namespaces open there. */
export interface FileDecl { name: string; kind: string; line: number; ns: string; scopes: string[]; opened: string[] }
export interface FileDecls { imports: string[]; decls: FileDecl[] }
export interface Candidate extends FileDecl { file: string; full: string }

/** A file's imports and declarations, each with the namespaces in force where it stands. Pure. */
export function parseFileDecls(text: string): FileDecls {
  const imports = [...text.matchAll(/^[ \t]*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([^\s]+)/gm)].map((m) => m[1]);
  const lines = maskLeanCommentsAndStrings(text).split("\n");
  const frames: Array<{ ns: string | null; opened: string[] }> = [{ ns: null, opened: [] }];
  const found = leanSourceDeclarations(text);
  const decls: FileDecl[] = [];
  let next = 0;
  for (let k = 0; k < lines.length; k++) {
    for (; next < found.length && found[next].line === k + 1; next++) {
      const chain = frames.flatMap((f) => (f.ns ? f.ns.split(".") : []));
      const scopes = chain.map((_, i) => chain.slice(0, chain.length - i).join(".")).concat("");
      const opened = frames.flatMap((f) => f.opened).flatMap((o) => scopes.map((s) => (s ? `${s}.${o}` : o)));
      decls.push({ ...found[next], ns: chain.join("."), scopes, opened });
    }
    const line = lines[k];
    const ns = /^\s*namespace\s+(\S+)/.exec(line);
    const open = /^\s*open\s+(?:scoped\s+)?(.*)$/.exec(line);
    if (ns) frames.push({ ns: ns[1], opened: [] });
    else if (/^\s*(?:(?:public|noncomputable)\s+)*section\b/.test(line)) frames.push({ ns: null, opened: [] });
    else if (/^\s*end\b/.test(line)) { if (frames.length > 1) frames.pop(); }
    else if (open) {
      for (const tok of open[1].split(/\s+/)) {
        if (!tok || tok === "in" || tok === "hiding" || tok === "renaming" || tok.startsWith("(")) break;
        frames.at(-1)!.opened.push(tok);
      }
    }
  }
  return { imports, decls };
}

/** Where the run's Lean lives and how its files are read. `memo` keeps a value computed from one
 *  file while that file is unchanged (the UI's cache); without it each file is parsed once here. */
export interface LeanFiles {
  toolkitRoot: string;
  leanDir: string;
  read(abs: string): Promise<string | null>;
  memo?<T>(name: string, abs: string, compute: () => Promise<T>): Promise<T>;
}

const MAX_FILES = 600;
/** Statements opened inside one another. */
const MAX_OF_DEPTH = 6;
const THEOREM_KINDS: ReadonlySet<string> = new Set(["theorem", "lemma"]);
/** A clause that is the statement of another declaration, whole. */
const TYPE_OF = /^type_of%\s+@?([^\s()]+)$/;

const insideDir = (dir: string, file: string): boolean => {
  const rel = path.relative(dir, file);
  return rel !== "" && !rel.startsWith("..") && !path.isAbsolute(rel);
};

/**
 * The declaration of one of `kinds` that `tok`, written at `site`, names: in the namespaces
 * enclosing the use, innermost first (`_root_.` : none), then in those opened there. Null when
 * nothing in `scope` has that name, or two opened namespaces both do. Pure.
 */
export function resolveName(scope: Map<string, Candidate[]>, tok: string, kinds: ReadonlySet<string>, site: Pick<FileDecl, "scopes" | "opened">): Candidate | null {
  const rooted = tok.startsWith("_root_."), name = rooted ? tok.slice(7) : tok;
  const cands = (scope.get(leanNameLeaf(name)) ?? []).filter((c) => kinds.has(c.kind));
  for (const s of rooted ? [""] : site.scopes) {
    const hit = cands.filter((c) => c.full === (s ? `${s}.${name}` : name));
    if (hit.length) return hit[0];
  }
  const hit = rooted ? [] : cands.filter((c) => site.opened.some((o) => c.full === `${o}.${name}`));
  return hit.length === 1 ? hit[0] : null;
}

export interface LeanScopes {
  /** The declarations visible from `file`: its own and those of the run's files it imports, by leaf name. */
  scopeOf(file: string): Promise<Map<string, Candidate[]>>;
  /** The declaration `decl` of `file` (by its leaf name, the one at `line` when given), or null. */
  siteOf(file: string, decl: string, line?: number): Promise<Candidate | null>;
  /** The source of the declaration at `c` with its `-- @node:` tag, or null. */
  sourceOf(c: Candidate): Promise<{ source: string; node: string | null } | null>;
  /** The text of the run's file `file`, or null. */
  textOf(file: string): Promise<string | null>;
}

export function leanScopes(files: LeanFiles): LeanScopes {
  // nothing is read outside the run's Lean directory, itself inside the toolkit
  const ok = insideDir(path.resolve(files.toolkitRoot), path.resolve(files.leanDir));
  const within = (file: string) => ok && insideDir(files.leanDir, path.join(files.leanDir, file));
  const own = new Map<string, Promise<unknown>>();
  const memo = <T>(name: string, abs: string, compute: () => Promise<T>): Promise<T> => {
    if (files.memo) return files.memo(name, abs, compute);
    const key = `${name}:${abs}`;
    if (!own.has(key)) own.set(key, compute());
    return own.get(key) as Promise<T>;
  };
  const declsOf = (abs: string) => memo<FileDecls | null>("lean-decls", abs, async () => {
    const text = await files.read(abs);
    return text === null ? null : parseFileDecls(text);
  });
  const candidates = async (file: string): Promise<Candidate[]> =>
    (within(file) ? (await declsOf(path.join(files.leanDir, file)))?.decls ?? [] : []).map((d) => ({ ...d, file, full: d.ns ? `${d.ns}.${d.name}` : d.name }));
  const scopes = new Map<string, Promise<Map<string, Candidate[]>>>();
  const scopeOf = (file: string): Promise<Map<string, Candidate[]>> => {
    const cached = scopes.get(file);
    if (cached) return cached;
    const built = (async () => {
      const byLeaf = new Map<string, Candidate[]>();
      if (!within(file)) return byLeaf;
      const seen = new Set<string>([path.join(files.leanDir, file)]);
      const todo = [...seen];
      while (todo.length && seen.size <= MAX_FILES) {
        const abs = todo.pop()!;
        const fd = await declsOf(abs);
        if (!fd) continue;
        for (const c of await candidates(path.relative(files.leanDir, abs).split(path.sep).join("/"))) {
          const leaf = leanNameLeaf(c.name);
          (byLeaf.get(leaf) ?? byLeaf.set(leaf, []).get(leaf)!).push(c);
        }
        for (const mod of fd.imports) {
          const next = path.join(files.toolkitRoot, ...mod.split(".")) + ".lean";
          if (insideDir(files.leanDir, next) && !seen.has(next)) { seen.add(next); todo.push(next); }
        }
      }
      return byLeaf;
    })();
    scopes.set(file, built);
    return built;
  };
  const siteOf = async (file: string, decl: string, line?: number): Promise<Candidate | null> => {
    const leaf = leanNameLeaf(decl);
    const named = (await candidates(file)).filter((c) => leanNameLeaf(c.name) === leaf);
    return named.find((c) => c.line === line) ?? named.find((c) => decl === c.full || decl.endsWith(`.${c.full}`)) ?? named[0] ?? null;
  };
  const sourceOf = async (c: Candidate): Promise<{ source: string; node: string | null } | null> => {
    const text = within(c.file) ? await files.read(path.join(files.leanDir, c.file)) : null;
    if (text === null) return null;
    try { return { source: extractFullDeclSource(text, c.name, c.line), node: nodeTagAbove(text.split(/\r?\n/), c.line - 1) }; } catch { return null; }
  };
  const textOf = async (file: string): Promise<string | null> => (within(file) ? files.read(path.join(files.leanDir, file)) : null);
  return { scopeOf, siteOf, sourceOf, textOf };
}

/**
 * Put, in place of each clause of `view` written `type_of% @name`, the statement of the run's
 * theorem `name` (`of`; to `MAX_OF_DEPTH`, a theorem met again on the way down left as written): its
 * rows become the clause's, their ids under the clause's own (`r3/r7`), and `view.key` takes that
 * statement in. `file`, `decl`: where the statement of `view` stands. `cited` as `leanStatementView`.
 */
export async function expandTypeOf(view: StatementView, file: string, decl: string, lean: LeanScopes, cited: ReadonlySet<string> = new Set(), line?: number): Promise<void> {
  const expand = async (card: StatementCard, at: Candidate, above: string[]): Promise<void> => {
    const written = card.hyps.length === 0 && !card.intro ? (card.code ?? "").trim() : "";
    const m = TYPE_OF.exec(written);
    const c = m && above.length < MAX_OF_DEPTH ? resolveName(await lean.scopeOf(at.file), m[1], THEOREM_KINDS, at) : null;
    const key = c ? `${c.file}#${c.full}` : "";
    const src = c && !above.includes(key) ? await lean.sourceOf(c) : null;
    const st = src ? leanStatementView(src.source, cited) : null;
    // `type_of% @name` is the whole type of `name`: the section variables it takes included
    if (c && st) withSectionVariables(st, (await lean.textOf(c.file)) ?? "", c.line);
    if (c && st) {
      eachRow(st, (row) => { if (row.id) row.id = `${card.id}/${row.id}`; });
      view.key = hash(`${view.key}\n${c.full}\n${st.key}`);
      delete card.code;
      Object.assign(card, { of: { name: c.name, kind: c.kind, file: c.file, line: c.line, ...(src!.node ? { node: src!.node } : {}), written }, hyps: st.sharedHyps, sub: st.conclusions });
    }
    const [inner, innerAbove] = c && st ? [c, [...above, key]] : [at, above];
    for (const h of card.hyps) for (const s of h.sub ?? []) await expand(s, inner, innerAbove);
    for (const s of card.sub ?? []) await expand(s, inner, innerAbove);
  };
  const site = await lean.siteOf(file, decl, line);
  if (!site) return;
  for (const h of view.sharedHyps) for (const s of h.sub ?? []) await expand(s, site, []);
  for (const c of view.conclusions) await expand(c, site, []);
}

// ── the section's `variable`s ────────────────────────────────────────────────

/** A binder group of a `variable` command: as written (comments dropped), its bracket and names. */
export interface SectionVar { raw: string; open: string; names: string[]; type: string }

const COMMENTS = /\/-[\s\S]*?-\/|--[^\n]*/g;

/** The bracketed groups that open `masked` at `from` (whitespace between them), with where they end. */
function groupsAt(masked: string, text: string, from: number): { groups: string[]; end: number } {
  const groups: string[] = [];
  let i = from;
  for (;;) {
    while (i < masked.length && /\s/.test(masked[i])) i++;
    if (!OPENERS.includes(masked[i] ?? "")) break;
    const close = closeOf(masked.slice(i));
    if (close < 0) break;
    groups.push(text.slice(i, i + close + 1).replace(COMMENTS, " ").replace(/[ \t]+\n/g, "\n").trim());
    i += close + 1;
  }
  return { groups, end: i };
}

/** A group as a section variable: `(x y : T)`, `{α : Type*}`, `[inst : C x]`, `[C x]`, `{x}`. */
function sectionVar(raw: string): SectionVar | null {
  const g = binderGroup(raw);
  if (g) return { raw, open: g.open, names: g.names.split(/\s+/), type: g.type };
  const inner = raw.slice(1, -1).trim();
  if (raw[0] === "[") return { raw, open: "[", names: [], type: inner };
  return BINDER_NAMES.test(inner) ? { raw, open: raw[0], names: inner.split(/\s+/), type: "" } : null;
}

/**
 * The `variable` groups in force where the declaration at line `line` (1-based) of `text` stands:
 * those of the enclosing `section`s and `namespace`s, in order, and of a `variable … in` right
 * before it; a names-only group (`variable {x}`) re-brackets a variable already there. `include` /
 * `omit` (also as `… in`) say which are forced in or left out. Pure.
 */
export function sectionScope(text: string, line: number): { vars: SectionVar[]; include: Set<string>; omit: Set<string> } {
  const masked = maskLeanCommentsAndStrings(text);
  const lines = masked.split("\n");
  const starts: number[] = [];
  for (let k = 0, at = 0; k < lines.length; k++) { starts.push(at); at += lines[k].length + 1; }
  type Frame = { vars: SectionVar[]; include: string[]; omit: string[]; rebracket: SectionVar[] };
  const frames: Frame[] = [{ vars: [], include: [], omit: [], rebracket: [] }];
  let pending: Frame | null = null;
  for (let k = 0; k < Math.min(line - 1, lines.length); k++) {
    const l = lines[k];
    if (!l.trim() || /^\s/.test(l)) continue; // a continuation, or nothing
    const word = /^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|public|private|protected)\s+)*(\w+)/.exec(l)?.[1] ?? "";
    // a command consumes what a `… in` before it scoped
    const scoped: Frame | null = pending;
    pending = null;
    if (word === "namespace" || word === "section") { frames.push({ vars: [], include: [], omit: [], rebracket: [] }); continue; }
    if (word === "end") { if (frames.length > 1) frames.pop(); continue; }
    if (word !== "variable" && word !== "include" && word !== "omit") {
      if (scoped && /^\s*(?:@\[|$)/.test(l)) pending = scoped; // an attribute line belongs to the next command
      continue;
    }
    const from = starts[k] + l.indexOf(word) + word.length;
    const into: Frame = { vars: [], include: [], omit: [], rebracket: [] };
    let end = from;
    if (word === "variable") {
      const { groups, end: e } = groupsAt(masked, text, from);
      end = e;
      for (const raw of groups) {
        const v = sectionVar(raw);
        if (!v) continue;
        // `variable {x}`: the variable `x` re-bracketed, not a new one
        const was = !v.type && v.open !== "[" && frames.some((f) => f.vars.some((u) => v.names.some((n) => u.names.includes(n))));
        (was ? into.rebracket : into.vars).push(v);
      }
    } else {
      const rest = masked.slice(from, starts[k + 1] ?? masked.length);
      const names = rest.replace(/\bin\s*$/, "").trim();
      end = from + rest.length;
      for (const m of names.matchAll(/\[([^\]]*)\]|([^\s[\]]+)/g)) (word === "include" ? into.include : into.omit).push(m[1] !== undefined ? squash(m[1]) : m[2]);
    }
    const isIn = word === "variable" ? /^\s*in\b/.test(masked.slice(end)) : /\bin\s*$/.test(masked.slice(from, end));
    if (isIn) pending = into;
    else {
      const f = frames.at(-1)!;
      f.vars.push(...into.vars); f.include.push(...into.include); f.omit.push(...into.omit);
      for (const r of into.rebracket) frames.forEach((fr) => { fr.vars = rebracketed(fr.vars, r); });
    }
    // skip the lines the command took
    while (k + 1 < lines.length && starts[k + 1] < end) k++;
  }
  const all = [...frames, ...(pending ? [pending] : [])];
  let vars = all.flatMap((f) => f.vars);
  for (const r of pending?.rebracket ?? []) vars = rebracketed(vars, r);
  return { vars, include: new Set(all.flatMap((f) => f.include)), omit: new Set(all.flatMap((f) => f.omit)) };
}

/** `vars` with the variables `r` names put in `r`'s bracket (`variable {x}`), as copies. */
const rebracketed = (vars: SectionVar[], r: SectionVar): SectionVar[] =>
  vars.map((u) => (r.names.some((n) => u.names.includes(n)) ? { ...u, open: r.open, raw: `${r.open}${u.raw.slice(1, -1)}${CLOSE_OF[r.open]}` } : u));
const CLOSE_OF: Record<string, string> = { "(": ")", "{": "}", "[": "]", "⦃": "⦄" };

/** The names a statement uses, by their first component (`W.n2` uses `W`). */
const usedNames = (text: string): Set<string> => new Set(identifierTokens(text).map((tok) => tok.split(".")[0]!));

/**
 * The section variables a theorem's statement takes, as Lean decides from its source (Lean 4: a
 * theorem takes the variables its statement mentions, those their types mention, the `include`d
 * ones, and an instance binder all of whose variables it takes). Approximated from the text:
 * `free` is what the statement names outside its own binders (`freeNames`: a name it only binds
 * itself is its own, not the section's); an instance binder is taken when it names at least one
 * variable taken and none not taken; a group `(x y : T)` of which only some names are used is cut
 * to those. Pure.
 */
export function usedSectionVars(scope: ReturnType<typeof sectionScope>, free: ReadonlySet<string>): SectionVar[] {
  const vars = scope.vars.filter((v) => !scope.omit.has(squash(v.type)) && !v.names.some((n) => scope.omit.has(n)));
  const declared = new Set(vars.flatMap((v) => v.names));
  const want = new Set([...free].filter((n) => declared.has(n)));
  for (const n of scope.include) if (declared.has(n)) want.add(n);
  // what a taken variable's type names is taken too
  for (let grew = true; grew;) {
    grew = false;
    for (const v of vars) {
      if (!v.names.some((n) => want.has(n))) continue;
      for (const n of usedNames(v.type)) if (declared.has(n) && !want.has(n)) { want.add(n); grew = true; }
    }
  }
  const out: SectionVar[] = [];
  for (const v of vars) {
    if (v.open === "[") {
      const named = [...usedNames(v.type)].filter((n) => declared.has(n));
      if (named.length && named.every((n) => want.has(n))) out.push(v);
      continue;
    }
    const taken = v.names.filter((n) => want.has(n));
    if (taken.length === v.names.length) out.push(v);
    else if (taken.length) out.push({ ...v, names: taken, raw: `${v.open}${taken.join(" ")} : ${v.type}${CLOSE_OF[v.open]}` });
  }
  return out;
}

/** The names a quantifier's header binds: `x y : T`, `(x : T) {y : U}`, `x ∈ s`, `ε > 0`. */
function headerNames(header: string): string[] {
  const out: string[] = [];
  const add = (s: string) => { for (const n of s.split(/\s+/)) if (/^[^\d\s]/.test(n) && BINDER_NAMES.test(n)) out.push(n); };
  let bare = "";
  for (let i = 0; i < header.length && !/[:∈∉⊆<>≤≥=≠]/.test(bare); i++) {
    const close = closeOf(header.slice(i));
    if (close < 0) { bare += header[i]; continue; }
    add(header.slice(i + 1, i + close).split(":")[0]!);
    bare += " ";
    i += close;
  }
  add(bare.split(/[:∈∉⊆<>≤≥=≠]/)[0]!);
  return out;
}

/**
 * The names `body` (a statement past its name: `statementBody`) uses outside its own binders, by
 * their first component (`W.n2` uses `W`). A binder group of the signature binds its names in all
 * that follows it; a `∀`/`∃`/`λ`/`fun` binds its header's to the end of the bracket it stands in.
 * So a name bound in one clause and used free in another is used. Pure.
 */
export function freeNames(body: string): Set<string> {
  const bound: Array<{ names: string[]; from: number; to: number }> = [];
  for (let i = body.search(/\S/); i >= 0 && OPENERS.includes(body[i] ?? "");) {
    const close = closeOf(body.slice(i));
    if (close < 0) break;
    const v = sectionVar(body.slice(i, i + close + 1));
    if (v) bound.push({ names: v.names, from: i, to: body.length });
    i += close + 1;
    while (/\s/.test(body[i] ?? "")) i++;
  }
  for (let from = 0; from < body.length; from++) {
    const word = "∀∃λ".includes(body[from]) ? 1 : keywordAt(body, from, "fun") ? 3 : 0;
    if (!word) continue;
    const rest = body.slice(from + word);
    const end = topLevelIndex(rest, (i) => rest[i] === "," || rest[i] === "↦" || rest.startsWith("=>", i));
    let depth = 0, to = from;
    for (; to < body.length; to++) {
      if (OPENERS.includes(body[to])) depth++;
      else if (CLOSERS.includes(body[to]) && --depth < 0) break;
    }
    bound.push({ names: headerNames(end < 0 ? rest : rest.slice(0, end)), from, to });
  }
  const out = new Set<string>();
  let at = 0;
  for (const tok of identifierTokens(body)) {
    const i = body.indexOf(tok, at), name = tok.split(".")[0]!;
    at = i + tok.length;
    if (!bound.some((b) => b.from <= i && i < b.to && b.names.includes(name))) out.add(name);
  }
  return out;
}

/**
 * Prepend to `view` the section variables its statement takes (`usedSectionVars`) as shared rows of
 * their own — `section` set, ids `v1`, `v2`, …, chipped by the binder rule — and take them into its
 * key. `text`: the file the statement stands in; `line`: where (1-based). Pure but for `view`.
 */
export function withSectionVariables(view: StatementView, text: string, line: number): void {
  const used = usedSectionVars(sectionScope(text, line), freeNames(statementBody(view.statement)));
  if (used.length === 0) return;
  const rows: StatementRow[] = used.map((v, k) => ({
    id: `v${k + 1}`, section: true, code: v.raw,
    chip: v.open === "(" ? binderChip(v.names.join(" "), v.type) : "decl",
  }));
  view.sharedHyps.unshift(...rows);
  view.key = hash(`${view.key}\n${used.map((v) => squash(v.raw)).join("\n")}`);
}

/**
 * The view F5 links and the page draws, complete: the section variables the statement takes
 * (`withSectionVariables`), then each clause written `type_of% @name` opened (`expandTypeOf`).
 * `file`, `decl`, `line`: where the statement stands.
 */
export async function completeView(view: StatementView, file: string, decl: string, lean: LeanScopes, cited: ReadonlySet<string> = new Set(), line?: number): Promise<void> {
  const site = await lean.siteOf(file, decl, line);
  const text = site ? await lean.textOf(file) : null;
  if (site && text !== null) withSectionVariables(view, text, site.line);
  await expandTypeOf(view, file, decl, lean, cited, line);
}
