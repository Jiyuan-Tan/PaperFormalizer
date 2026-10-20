/**
 * The core graph — every change to the typed core after transcription goes through here.
 *
 * Two editors change a verify core once V1 has copied it from the paper: the fixer (minimal
 * repairs: replaced texts, the dependencies a replacement supersedes or drops, descoped results) and the
 * referee on acceptance (`ass:bk-n` bookkeeping conditions, `ass:pin-n` pinned readings — of nodes
 * and of symbols — and symbol-table fixes). Until 2026-09-23 each had its own
 * code path that patched derived structure in place — `used_by`, the printed `[Hypotheses: …]`
 * list — and nine of the 29 verify-mode fixes since 2026-09-18 were one of those paths missing a case.
 *
 * Here instead:
 *   • one EDIT LANGUAGE (`GraphEdit`) and one pure applier (`applyEdits`);
 *   • wiring is stored ONCE, in `depends_on`; `used_by` and the printed hypothesis list are
 *     DERIVED by `normalizeCore` after every build, never maintained;
 *   • one INVARIANT (`checkCoreInvariants`) is checked after every build, before any referee
 *     call — a violation is a runner bug and `buildCore` throws;
 *   • one REMAP (`remapNodeIds`) rewrites every id-keyed artifact when a V1 round removes or
 *     renames a node that carries records.
 */
import { revisesProof, type PatchOp } from "./ops.js";
import { createHash } from "node:crypto";
import type { Core, CoreAssumption, CoreStatement, CoreSymbol, ScopedClause } from "../core/schema.js";
import { normalizeSymbol } from "../core/symbol_names.js";
import { normalizeBasisText } from "./basis_text.js";
import { resultWord } from "./owner_text.js";
import { canonicalTokens, mentionsSymbol, symbolOccurrences, symbolPattern } from "./symbol_match.js";
import type { V15Review, V15SymbolVerdict } from "./types.js";

/** Provenance tag of a condition the referee added on acceptance. */
export const REVIEW_ADDED_BY = "V1.5";
/** Provenance tag of a reading the paper's OWNER pinned when withdrawing a finding
 * (`--reject-finding`, `owner_rulings.ts`); its id is `ass:pin-owner-<n>`. */
export const OWNER_ADDED_BY = "owner";
/** The id prefix of an owner-pinned reading. */
export const OWNER_PIN_PREFIX = "ass:pin-owner-";
/** Provenance tag of a reading a REPAIR states beside its statement (a patch's `readings`): the
 * specification an ambiguous phrase needed, kept out of the statement's text. The referee grades it
 * with the patch; once accepted it binds the F stages like every pin. Its id is `ass:pin-fix-<hash>`. */
export const PATCH_ADDED_BY = "V1-patch";
/** The id prefix of a reading stated by a repair. */
export const PATCH_PIN_PREFIX = "ass:pin-fix-";
/** The id of the reading `text` a repair of `node` states: by its meaning, so a re-typesetting keeps it. */
export function patchReadingId(node: string, text: string): string {
  return `${PATCH_PIN_PREFIX}${createHash("sha256").update(`${node}|${normalizeBasisText(text)}`).digest("hex").slice(0, 8)}`;
}

/** The tag in the id of a block a repair SPLITS OFF a result (a patch's `corollaries`): a result of
 * its own, of the parent's kind, that the paper does not print — `<thm|lem|prop>:cor-fix-<hash>`. The
 * tag, the field and `split_from` keep the word for both kinds of block (`splitKind`): the id keys the
 * node's grades, plan and Lean tags. */
export const SPLIT_COROLLARY_TAG = "cor-fix-";
/** The id of the corollary `statement` a repair of `parent` splits off: the parent's id prefix (its
 * kind) and the statement by its meaning, so a re-typesetting — and a re-run emitting it again — keeps
 * the id, and with it the node's grades, plan and receipts. */
export function splitCorollaryId(parent: string, statement: string): string {
  return `${parent.split(":")[0]}:${SPLIT_COROLLARY_TAG}${createHash("sha256").update(`${parent}|${normalizeBasisText(statement)}`).digest("hex").slice(0, 8)}`;
}
/** The statement of an UMBRELLA in the core (`CoreStatement.umbrella`; a patch's `umbrella`): a printed
 * result that mixes several conclusions, each under its own conditions, none its own main claim — every
 * conclusion is a proposition block and the result says that they hold. The text is FIXED (it is hashed
 * into every basis), so it never names the blocks: a reader is shown `umbrellaSentence`. */
export const UMBRELLA_STATEMENT = "The following propositions hold, each under the conditions stated in it.";
/** The proof of an umbrella in the core: it has none of its own. */
export const UMBRELLA_PROOF = "Each proposition is proved where it is stated.";
/** The blocks of an umbrella named together, from their display names in order ("Proposition 5.2.1",
 * …): "Propositions 5.2.1–5.2.6" (`dash`: the range mark of the medium); names that are not one
 * consecutive run are listed; null when a block has no such name (the blocks are not numbered there). Pure. */
export function umbrellaRange(names: readonly string[], dash = "–"): string | null {
  const parsed = names.map((n) => /^Proposition\s+(.*?)(\d+)$/u.exec(n.trim()));
  if (names.length === 0 || parsed.some((m) => !m)) return null;
  if (names.length === 1) return names[0]!.trim();
  const nums = parsed.map((m) => `${m![1]}${m![2]}`);
  const run = parsed.every((m, i) => m![1] === parsed[0]![1] && Number(m![2]) === Number(parsed[0]![2]) + i);
  return `Propositions ${run && names.length > 2 ? `${nums[0]}${dash}${nums[nums.length - 1]}` : `${nums.slice(0, -1).join(", ")} and ${nums[nums.length - 1]}`}`;
}
/** The umbrella sentence as a reader is shown it, generated from its blocks' names (`umbrellaRange`):
 * "Propositions 5.2.1–5.2.6 hold, each under the conditions stated in it."; `UMBRELLA_STATEMENT` when
 * the blocks have no numbers there. Pure. */
export function umbrellaSentence(names: readonly string[], dash = "–"): string {
  const range = umbrellaRange(names, dash);
  if (!range) return UMBRELLA_STATEMENT;
  return names.length === 1 ? `${range} holds under the conditions stated in it.` : `${range} hold, each under the conditions stated in it.`;
}
/** The blocks of each umbrella of a core, in core order, by the umbrella's id. */
export function umbrellaBlocks(core: { statements: ReadonlyArray<{ id: string; umbrella?: boolean; split_from?: string }> }): Map<string, string[]> {
  const out = new Map<string, string[]>(core.statements.filter((s) => s.umbrella).map((s) => [s.id, []]));
  for (const s of core.statements) if (s.split_from && out.has(s.split_from)) out.get(s.split_from)!.push(s.id);
  return out;
}
/** What a block a repair split off a result IS: a `corollary` of the corrected result, or a
 * `proposition` — a separate result the printed statement bundled in, resting on other results. */
export type SplitKind = "corollary" | "proposition";
/** A split-off block's kind, read from its PROOF alone (`follows` / `proof_tex`): a corollary exactly
 * when the proof cites the parent by its TeX label (`citedLabels`: `\ref` and its kin, comments
 * apart), a proposition otherwise — a citation in the block's statement decides nothing. A parent
 * without a label can be cited by nothing, so nothing tells the two apart: the block is then a
 * corollary (it keeps its dependency on the parent — an edge too many only re-grades, one too few
 * hides a use). A block of an UMBRELLA (`umbrella`) is a proposition whatever its proof says: the
 * umbrella rests on its blocks, never they on it. Pure; every name and every edge of a block comes from here. */
export function splitKind(proof: string | null | undefined, parentLabel: string | null | undefined, umbrella = false): SplitKind {
  if (umbrella) return "proposition";
  const label = parentLabel?.trim();
  return !label || citedLabels(proof ?? "").includes(label) ? "corollary" : "proposition";
}
/** The kind of each block of a core (`split_from` set), by its id (`splitKind` on its `proof_tex` and
 * its parent's `tex_locator.label`). */
export function splitKinds(core: { statements: ReadonlyArray<{ id: string; split_from?: string; umbrella?: boolean; proof_tex?: string | null; tex_locator?: { label?: string | null } | null }> }): Map<string, SplitKind> {
  const labelOf = new Map(core.statements.map((s) => [s.id, s.tex_locator?.label] as const));
  const umbrellas = new Set(core.statements.filter((s) => s.umbrella).map((s) => s.id));
  return new Map(core.statements.flatMap((s) => (s.split_from ? [[s.id, splitKind(s.proof_tex, labelOf.get(s.split_from), umbrellas.has(s.split_from))] as const] : [])));
}
/** A count of blocks in words, by kind: "2 corollaries", "1 corollary and 3 propositions". */
export function splitCount(kinds: readonly SplitKind[]): string {
  const c = kinds.filter((k) => k === "corollary").length, p = kinds.length - c;
  return [c > 0 ? `${c} corollar${c === 1 ? "y" : "ies"}` : "", p > 0 ? `${p} proposition${p === 1 ? "" : "s"}` : ""].filter(Boolean).join(" and ");
}
/** A reading appended to the core that the paper never prints: a referee pin / bookkeeping
 * condition, or an owner's reading. Wired in, never rendered in a hypothesis list. */
export function isReadingAddition(a: CoreAssumption): boolean {
  return a.bookkeeping?.added_by === REVIEW_ADDED_BY || a.bookkeeping?.added_by === OWNER_ADDED_BY || a.bookkeeping?.added_by === PATCH_ADDED_BY;
}
/** The marker that opens a patch's proof change inside a statement's `proof_tex`. */
export const PROOF_CHANGE_MARKER = "[Proof change (minimal patch):";

/**
 * A build that failed because of its INPUTS — a hand-edited `core.transcribed.json` that is not
 * a consistent graph, or a `patches.json` that no longer fits the transcription. The operator
 * fixes the file; the runner reports a checkpoint. (A broken invariant on a core built from
 * consistent inputs is a plain `Error`: a runner bug.)
 */
export class CoreGraphInputError extends Error {
  constructor(
    /** Which input file the operator must fix. */
    readonly file: "core.transcribed.json" | "patches.json",
    readonly problems: string[],
  ) {
    super(`${file} cannot be built into a core:\n${problems.map((p) => `  - ${p}`).join("\n")}`);
    this.name = "CoreGraphInputError";
  }
}

// ---------------------------------------------------------------------------------------------
// Edit language
// ---------------------------------------------------------------------------------------------

export type GraphEdit =
  /** A new assumption node. `used_by` is ignored: it is derived. */
  | { op: "add_assumption"; node: CoreAssumption }
  /** A new statement node (a corollary a repair splits off `node.split_from`), appended: no statement
   * of the paper changes place, so none changes its positional alias in the F stages. */
  | { op: "add_statement"; node: CoreStatement }
  /** Remove a statement, assumption or definition and every edge pointing at it. */
  | { op: "remove_node"; id: string; why: string }
  /** `statement.depends_on` gains `dep` (no-op when present). */
  | { op: "wire"; statement: string; dep: string }
  /** `statement.depends_on` loses `dep` (no-op when absent). */
  | { op: "unwire"; statement: string; dep: string }
  /** Replace a node's printed text: a statement's `statement`, an assumption's `condition`, a
   * definition's `construction`. A statement's printed hypothesis list is re-derived afterwards. */
  | { op: "set_statement"; id: string; statement: string }
  /** Append a proof change to a statement's `proof_tex`. */
  | { op: "append_proof"; id: string; text: string }
  /** Replace a statement's `proof_tex` (the printed proof with a repair's edits spliced in). */
  | { op: "set_proof"; id: string; text: string }
  /** Mark a statement an umbrella over the blocks split off it (`UMBRELLA_STATEMENT`). */
  | { op: "set_umbrella"; id: string }
  /** Correct a symbol's recorded `type` / `def` (the symbol referee's `fix`); an absent field is kept. */
  | { op: "set_symbol"; name: string; type?: string; space?: string; def?: string; scoped?: ScopedClause[] };

export interface ApplyOutcome {
  core: Core;
  /** Edits that could not be applied, with the reason; the core is as if they were absent. */
  rejected: Array<{ edit: GraphEdit; reason: string }>;
}

function nodeIds(core: Core): Set<string> {
  return new Set([...core.statements, ...core.assumptions, ...core.definitions].map((n) => n.id));
}

/**
 * Apply `edits` in order to a copy of `core`. Pure. Every edit is validated against the graph
 * as it stands when the edit is reached; an edit that does not fit is rejected and skipped.
 * Derived fields (`used_by`, the printed hypothesis list) are NOT touched here — call
 * `normalizeCore` afterwards (or use `buildCore`, which does).
 */
export function applyEdits(input: Core, edits: readonly GraphEdit[]): ApplyOutcome {
  const core = structuredClone(input) as Core;
  const rejected: ApplyOutcome["rejected"] = [];
  for (const edit of edits) {
    const ids = nodeIds(core);
    const statement = (id: string): CoreStatement | undefined => core.statements.find((s) => s.id === id);
    switch (edit.op) {
      case "add_assumption": {
        if (ids.has(edit.node.id)) {
          rejected.push({ edit, reason: `node "${edit.node.id}" already exists` });
          break;
        }
        const { used_by: _u, ...rest } = edit.node;
        core.assumptions.push(rest as CoreAssumption);
        break;
      }
      case "add_statement": {
        if (ids.has(edit.node.id)) rejected.push({ edit, reason: `node "${edit.node.id}" already exists` });
        else if (!statement(edit.node.split_from ?? "")) rejected.push({ edit, reason: `"${edit.node.split_from}" is not a statement of the core` });
        else core.statements.push(structuredClone(edit.node));
        break;
      }
      case "remove_node": {
        if (!ids.has(edit.id)) {
          rejected.push({ edit, reason: `node "${edit.id}" does not exist` });
          break;
        }
        core.statements = core.statements.filter((s) => s.id !== edit.id);
        core.assumptions = core.assumptions.filter((a) => a.id !== edit.id);
        core.definitions = core.definitions.filter((d) => d.id !== edit.id);
        for (const s of core.statements) s.depends_on = s.depends_on.filter((d) => d !== edit.id);
        break;
      }
      case "wire": {
        const s = statement(edit.statement);
        if (!s) {
          rejected.push({ edit, reason: `"${edit.statement}" is not a statement of the core` });
          break;
        }
        if (!ids.has(edit.dep)) {
          rejected.push({ edit, reason: `dependency "${edit.dep}" is not a node of the core` });
          break;
        }
        if (edit.dep === edit.statement) {
          rejected.push({ edit, reason: "a statement cannot depend on itself" });
          break;
        }
        if (!s.depends_on.includes(edit.dep)) s.depends_on = [...s.depends_on, edit.dep];
        break;
      }
      case "unwire": {
        const s = statement(edit.statement);
        if (!s) {
          rejected.push({ edit, reason: `"${edit.statement}" is not a statement of the core` });
          break;
        }
        s.depends_on = s.depends_on.filter((d) => d !== edit.dep);
        break;
      }
      case "set_statement": {
        const s = statement(edit.id);
        const a = core.assumptions.find((x) => x.id === edit.id);
        const d = core.definitions.find((x) => x.id === edit.id);
        if (s) s.statement = edit.statement;
        else if (a) a.condition = edit.statement;
        else if (d) d.construction = edit.statement;
        else rejected.push({ edit, reason: `"${edit.id}" is not a node of the core` });
        break;
      }
      case "set_proof": {
        const s = statement(edit.id);
        if (!s) {
          rejected.push({ edit, reason: `"${edit.id}" is not a statement of the core` });
          break;
        }
        s.proof_tex = edit.text;
        break;
      }
      case "set_umbrella": {
        const s = statement(edit.id);
        if (!s) rejected.push({ edit, reason: `"${edit.id}" is not a statement of the core` });
        else s.umbrella = true;
        break;
      }
      case "append_proof": {
        const s = statement(edit.id);
        if (!s) {
          rejected.push({ edit, reason: `"${edit.id}" is not a statement of the core` });
          break;
        }
        s.proof_tex = `${s.proof_tex ? `${s.proof_tex}\n\n` : ""}${edit.text}`;
        break;
      }
      case "set_symbol": {
        const sym = core.symbols.find((x) => x.name === edit.name);
        if (!sym) {
          rejected.push({ edit, reason: `"${edit.name}" is not a symbol of the table` });
          break;
        }
        if (edit.type !== undefined) sym.type = edit.type;
        if (edit.space !== undefined) sym.space = edit.space;
        if (edit.def !== undefined) sym.def = edit.def;
        if (edit.scoped !== undefined) sym.scoped = edit.scoped;
        break;
      }
    }
  }
  return { core, rejected };
}

// ---------------------------------------------------------------------------------------------
// Derived structure
// ---------------------------------------------------------------------------------------------

const HYPOTHESIS_LIST = /\s*\[Hypotheses:([^\]]*)\]\s*$/u;

/** A statement's text without its printed `[Hypotheses: …]` list. */
export function statementBody(text: string): string {
  return text.replace(HYPOTHESIS_LIST, "").trimEnd();
}

/** The ids a statement's printed `[Hypotheses: …]` list names, in order (empty when none). */
export function printedHypotheses(text: string): string[] {
  const m = HYPOTHESIS_LIST.exec(text);
  return m ? m[1].split(",").map((id) => id.trim()).filter(Boolean) : [];
}

/**
 * The printed hypothesis list of a statement, re-derived from its wiring: the ids the PRINTED
 * (transcribed) list carried that the statement still depends on, in their order — never a
 * dependency a repair superseded. Referee additions are wired but not printed. A statement whose printed
 * version had no list gets none (the list is V1's device for hypotheses stated outside the
 * environment; a statement V1 left bare stays bare).
 */
export function renderHypothesisList(body: string, printed: string, dependsOn: readonly string[]): string {
  // no printed list → none; a body carrying no list is returned byte-for-byte (whitespace kept)
  if (!HYPOTHESIS_LIST.test(printed)) return HYPOTHESIS_LIST.test(body) ? statementBody(body) : body;
  const clean = statementBody(body);
  const ids = printedHypotheses(printed).filter((id) => dependsOn.includes(id));
  return ids.length > 0 ? `${clean} [Hypotheses: ${ids.join(", ")}]` : clean;
}

/**
 * Derive everything that is a function of `depends_on`. Pure.
 *   • `assumption.used_by` = sorted statements depending on it (omitted when none);
 *   • a statement whose text or wiring differs from its transcribed version gets its printed
 *     `[Hypotheses: …]` list re-rendered (see `renderHypothesisList`); an unchanged statement
 *     keeps its bytes.
 * `transcribed` is the core as V1 copied it (the user's version); a statement absent from it
 * (none today) is rendered against its own text.
 */
export function normalizeCore(input: Core, transcribed: Core): Core {
  const core = structuredClone(input) as Core;
  const users = new Map<string, Set<string>>();
  for (const s of core.statements) for (const d of s.depends_on) (users.get(d) ?? users.set(d, new Set()).get(d)!).add(s.id);
  for (const a of core.assumptions) {
    const u = [...(users.get(a.id) ?? [])].sort();
    if (u.length === 0) delete a.used_by;
    else a.used_by = u;
  }
  // A split-off corollary reaches the users of its parent by the build, like a referee addition.
  const split = new Set(core.statements.filter((s) => s.split_from).map((s) => s.id));
  const isReview = (id: string): boolean => split.has(id) || core.assumptions.some((a) => a.id === id && isReadingAddition(a));
  const printedById = new Map(transcribed.statements.map((s) => [s.id, s] as const));
  for (const s of core.statements) {
    const printed = printedById.get(s.id);
    if (!printed) continue;
    // A referee addition (bk / pin) is wired but never printed, so it alone leaves the text alone.
    const wiring = s.depends_on.filter((d) => !isReview(d));
    const changed = s.statement !== printed.statement || wiring.join("\u0000") !== printed.depends_on.join("\u0000");
    if (changed) s.statement = renderHypothesisList(s.statement, printed.statement, s.depends_on);
  }
  return core;
}

// ---------------------------------------------------------------------------------------------
// The invariant
// ---------------------------------------------------------------------------------------------

/**
 * Every consistency condition the built core must satisfy. Empty = consistent. A non-empty
 * list is a RUNNER bug (the inputs were validated before compilation), never a finding about
 * the paper or the fixer.
 */
export function checkCoreInvariants(core: Core): string[] {
  const out: string[] = [];
  const all = [...core.statements, ...core.assumptions, ...core.definitions].map((n) => n.id);
  const ids = new Set(all);
  // 5. unique ids
  const seen = new Set<string>();
  for (const id of all) {
    if (seen.has(id)) out.push(`id "${id}" names more than one node`);
    seen.add(id);
  }
  // 1. no dangling edge
  for (const s of core.statements) {
    for (const d of s.depends_on) if (!ids.has(d)) out.push(`"${s.id}" depends on "${d}", which is not a node`);
    if (s.depends_on.includes(s.id)) out.push(`"${s.id}" depends on itself`);
  }
  // 2. used_by is the reverse of depends_on
  for (const a of core.assumptions) {
    const expected = core.statements.filter((s) => s.depends_on.includes(a.id)).map((s) => s.id).sort();
    const got = [...(a.used_by ?? [])].sort();
    if (expected.join("\u0000") !== got.join("\u0000")) {
      out.push(`"${a.id}".used_by is [${got.join(", ")}] but the statements depending on it are [${expected.join(", ")}]`);
    }
  }
  // 3. printed hypotheses ⊆ depends_on
  for (const s of core.statements) {
    for (const h of printedHypotheses(s.statement)) {
      if (!s.depends_on.includes(h)) out.push(`"${s.id}" prints hypothesis "${h}" but does not depend on it`);
    }
  }
  // 4. an umbrella rests on its blocks (at least two), and none of them on it
  const byId = new Map(core.statements.map((s) => [s.id, s] as const));
  for (const [id, bs] of umbrellaBlocks(core)) {
    if (bs.length < 2) out.push(`umbrella "${id}" has ${bs.length} block(s): it needs at least two`);
    for (const b of bs) {
      if (!byId.get(id)!.depends_on.includes(b)) out.push(`umbrella "${id}" does not depend on its block "${b}"`);
      if (statementClosure(core, [b]).has(id)) out.push(`block "${b}" rests on its umbrella "${id}" (a cycle)`);
    }
  }
  return out;
}

// ---------------------------------------------------------------------------------------------
// Compilation: patches
// ---------------------------------------------------------------------------------------------

/** The slice of the patch file `compilePatchEdits` reads (the zod type lives in `patches.ts`). */
export interface PatchFileLike {
  key_results: string[];
  patches: Array<{
    node: string;
    corrected_statement: string | null;
    proof_note: string;
    /** The repair as replacements of the paper's units (`ops.ts`); `corrected_statement` and, when an op
     * changes the proof, `proof_note` (the amended proof) are derived from them. */
    ops?: PatchOp[];
    /** DERIVED by the runner (`ops.ts` `supersededNodes`): the node's own hypotheses (assumptions)
     * whose printed text the replacement rewrites; the repaired node does not use them. */
    supersedes?: string[];
    /** The fixer's: hypotheses the node depends on that the corrected result no longer uses (it states
     * its own condition instead); unwired from it like superseded ones. A result named here that the
     * repair's text only cites (to compare, not to use) is not wired in. */
    drops?: string[];
    /** The fixer's: hypotheses the corrected result uses that it did not depend on; wired into it. */
    adds?: string[];
    /** The repairs this patch follows (`consequential.ts`). */
    consequence_of?: string[] | null;
    /** The fixer's: readings of the node's wording the repair states beside the statement; each
     * becomes an `ass:pin-fix-<hash>` wired like an owner reading. */
    readings?: string[];
    /** The fixer's: results the repair SPLITS OFF the node (a result) — each a statement node of its
     * own (`splitCorollaryId`) depending on `adds` and, a corollary (`splitKind`), on the node; proved by `follows`. */
    corollaries?: SplitCorollary[];
    /** The fixer's (or the orchestrator's, `--umbrella`): the node states nothing of its own — every
     * conclusion is a block of `corollaries` (all propositions) and the node is the UMBRELLA over
     * them: `UMBRELLA_STATEMENT`, depending on its blocks and on nothing else of the paper. */
    umbrella?: boolean;
  }>;
  /** `declined`: the owner declined the weakened repair suggested for it (`weakening.ts`). */
  unfixable: Array<{ node: string; reason: string; declined?: string }>;
  /** Readings the paper's owner adopted when withdrawing a finding (`owner_rulings.ts`): each
   * becomes an `ass:pin-owner-<n>` wired into the node (a statement) or every statement using it. */
  owner_readings?: OwnerReading[];
}

/** One corollary a repair splits off its node (`patches.json`, a patch's or a suggested repair's `corollaries`). */
export interface SplitCorollary {
  /** What the author would call it ("the Gaussian case"); shown in its heading. */
  title?: string;
  /** The corollary, complete and self-contained; it may cite its parent and other results by `\ref`. */
  statement: string;
  /** Its complete proof, from the results it cites — the corrected parent among them exactly when it
   * is a corollary of it (`splitKind`); the corrected paper prints it as the proof. */
  follows: string;
  /** The assumptions and definitions of the core its statement itself imposes or uses. */
  adds?: string[];
}

/** A patch that makes its node an umbrella: flagged so, with blocks to rest on. */
export function isUmbrellaPatch(p: { umbrella?: boolean | null; corollaries?: readonly unknown[] | null } | null | undefined): boolean {
  return p?.umbrella === true && (p.corollaries?.length ?? 0) > 0;
}

/** The id prefix of a side condition the paper's owner states (`--reject-finding "<node>: bookkeeping: …"`). */
export const OWNER_BK_PREFIX = "ass:bk-owner-";

/** One owner-adopted reading (`patches.json` `owner_readings`). */
export interface OwnerReading {
  /** `ass:pin-owner-<n>` (a reading), or `ass:bk-owner-<n>` for `kind: "bookkeeping"`. */
  id: string;
  /** `bookkeeping`: a side condition every reader takes for granted (an `ass:bk-owner-*`, listed with
   * the bookkeeping conditions; "Bookkeeping condition:" in the annotated paper); default: a reading. */
  kind?: "reading" | "bookkeeping";
  /** The node whose finding the owner withdrew. */
  node: string;
  /** The owner's reading / why the finding is wrong, verbatim. */
  reading: string;
  /** The findings the owner withdrew with this reading — the ONE record of the ruling: the ledger
   * stamp, the ruled-out list's owner entries and the withdrawal notes are derived from it
   * (`owner_rulings.ts` `syncOwnerRulings`). Absent on a further reading of a node already ruled on. */
  withdraws?: OwnerWithdrawal[];
}

/** One finding an owner reading withdrew (`OwnerReading.withdraws`). */
export interface OwnerWithdrawal {
  /** `ambiguity`: the finding withdrawn said the paper leaves the statement undetermined — no error
   * was claimed, so the withdrawal overrules no later error on the node. */
  axis: "correctness" | "clarify" | "ambiguity";
  /** The stage that raised it (`V1.5`, `F2.5`, …) and how it reached the owner. */
  stage: string;
  route: string;
  /** The finding as raised. */
  detail: string;
  witness?: string | null;
  at: string;
}

/** Per core: the symbols each node uses (memo — `nodeFingerprint` runs once per node of a pass). */
const USED_SYMBOLS = new WeakMap<Core, Map<string, Set<string>>>();

/**
 * The names of the symbol-table entries node `id` uses: listed in its `free_symbols`, or found as a
 * whole symbol in any of its text (statement / condition / construction, proof).
 */
export function symbolsUsedByNode(core: Core, id: string): Set<string> {
  let memo = USED_SYMBOLS.get(core);
  if (!memo) USED_SYMBOLS.set(core, (memo = new Map()));
  const hit = memo.get(id);
  if (hit) return hit;
  const n = [...core.statements, ...core.assumptions, ...core.definitions].find((x) => x.id === id) as Record<string, unknown> | undefined;
  const out = new Set<string>();
  if (n) {
    const free = new Set(((n.free_symbols as string[] | undefined) ?? []).map(normalizeSymbol));
    const text = ["statement", "condition", "construction", "proof_tex"].map((k) => (typeof n[k] === "string" ? (n[k] as string) : "")).join("\n");
    const canon = canonicalTokens(text);
    for (const x of core.symbols) if (free.has(normalizeSymbol(x.name)) || symbolOccurrences(text, symbolPattern(x.name), canon).length > 0) out.add(x.name);
  }
  memo.set(id, out);
  return out;
}

/**
 * The version of the verdict-basis scheme. A basis covers WHAT THE NODE'S REFEREE IS SHOWN (or told it
 * may read) — no less, or a carried verdict rests on text that moved; no more, or a change the referee
 * never saw re-grades it (`basisInputs`): the node's own record, WITHOUT its derived user-side fields
 * (`DERIVED_USER_FIELDS`: an assumption's `used_by` — who uses a node is recorded on the users); the
 * text of each node it uses DIRECTLY and, of a result it uses, the hypotheses and definitions that
 * result is stated under and its verdict as the shard shows it; the symbol entries its record and
 * those texts name. Never the proof of a result it uses, nor what that result rests on: a change deep
 * in the chain reaches a node through the verdicts between them, level by level.
 * Every symbol reading, symbol-table type / def and V1.5-appended condition (pinned reading, bookkeeping
 * condition) is read by its MEANING (`basis_text.ts` `normalizeBasisText`), so a re-typesetting of it
 * re-opens nothing; the symbol readings binding a node are hashed apart, with
 * their structured state (pinned / left open — with the line its shard prints —, redefined later);
 * a hypothesis's own readings, printed as binding on it, are its own extra (`ownReadingsExtra`). Of a symbol entry's scoped clauses a
 * basis reads only those applicable to the node (`applicableClauses`). A cache recorded under another
 * scheme is dropped (every node graded afresh) — but for scheme 4, carried over (`basisInputsV4`). A
 * basis never includes prompt text or the code version: editing a prompt never re-opens a verdict.
 */
export const BASIS_SCHEME = 5;

/** Fields of a node DERIVED from other nodes' wiring (the users' side, `normalizeCore`): never read
 * into a basis. */
export const DERIVED_USER_FIELDS = ["used_by"] as const;

/** A node as a basis reads it: without its derived user-side fields; a V1.5-appended condition (a
 * pinned reading, a bookkeeping condition) by its meaning — its condition and reason normalized
 * (`normalizeBasisText`). A statement's text never. */
function basisView(n: unknown): unknown {
  if (n == null) return null;
  if (typeof n !== "object") return n;
  const out = { ...(n as Record<string, unknown>) };
  for (const f of DERIVED_USER_FIELDS) delete out[f];
  if (isReadingAddition(out as unknown as CoreAssumption)) {
    if (typeof out.condition === "string") out.condition = normalizeBasisText(out.condition);
    const bk = out.bookkeeping as Record<string, unknown> | undefined;
    if (bk && typeof bk.reason === "string") out.bookkeeping = { ...bk, reason: normalizeBasisText(bk.reason) };
  }
  return out;
}

/** A symbol-table entry as a basis reads it: its type, def, space and signature by
 * their meaning (`normalizeBasisText`); its name and references verbatim; its scoped clauses apart
 * (`symbolEntryHash`). */
export function symbolEntryView(x: CoreSymbol): CoreSymbol {
  const { scoped: _s, ...out }: Record<string, unknown> = { ...x };
  for (const f of ["type", "def", "space", "sig"] as const) if (typeof out[f] === "string") out[f] = normalizeBasisText(out[f] as string);
  return out as CoreSymbol;
}

/** The hash of a symbol entry in the basis of a node: the entry (`symbolEntryView`) and each scoped
 * clause applicable to the node AS ITS SHARD PRINTS IT (`lines`: `scopedClauseText` of
 * `applicableClauses`, in order — the lead naming the results and the text, by their meaning) — so
 * adding, dropping or changing an applicable clause, or how its result is named, moves the basis and
 * any other clause does not. With none applicable: the hash of the entry alone, as before clauses
 * existed. */
function symbolEntryHash(x: CoreSymbol, lines: readonly string[]): string {
  const entry = JSON.stringify(symbolEntryView(x));
  return lines.length === 0 ? sha(entry) : sha(`${entry}\nscoped:\n${lines.map(normalizeBasisText).join("\n")}`);
}

/** A symbol reading binding a statement, as the symbol referee settled it (`stage_v1_5.ts`
 * `symbolBasisExtra`): the reading it pinned, or `open` (graded unresolvable), and whether the paper
 * later gives the symbol another meaning. */
export interface SymbolReadingBasis {
  symbol: string;
  state: "pinned" | "open";
  /** The pinned reading, verbatim (empty for `open`). */
  text: string;
  redefined: boolean;
}

/** What a basis reads beside the core, per node: a string is material read verbatim (the cited
 * source a cited leaf was checked against); `readings` are the symbol readings binding a statement,
 * read by their meaning. */
export type BasisExtraValue = string | { text?: string; readings?: readonly SymbolReadingBasis[] };
export type BasisExtra = ReadonlyMap<string, BasisExtraValue>;

/** Two extra maps merged (a node in both gets both: `a`'s text first). */
export function mergeBasisExtra(a: BasisExtra, b: BasisExtra): Map<string, BasisExtraValue> {
  const out = new Map<string, BasisExtraValue>(a);
  for (const [k, v] of b) {
    if (!out.has(k)) {
      out.set(k, v);
      continue;
    }
    const x = asExtraEntry(out.get(k)!);
    const y = asExtraEntry(v);
    const text = [x.text, y.text].filter((t): t is string => t !== undefined).join("\n");
    out.set(k, { ...(x.text !== undefined || y.text !== undefined ? { text } : {}), readings: [...(x.readings ?? []), ...(y.readings ?? [])] });
  }
  return out;
}

function asExtraEntry(v: BasisExtraValue): { text?: string; readings?: readonly SymbolReadingBasis[] } {
  return typeof v === "string" ? { text: v } : v;
}

/** What a basis is computed from, recorded with each verdict so a later scheme can be computed
 * without a snapshot of the core: hashes of the node, of what it is shown of the nodes it uses
 * (`closure`: its own verbatim extra and each direct dependency — under scheme 4, its whole
 * `depends_on` closure), of each symbol entry read (by name), of each symbol reading binding the node
 * or a node it uses (by symbol name), and of the verdict of each result it uses, as shown to it. */
export interface BasisInputs {
  scheme: number;
  node: string;
  closure: string;
  symbols: Record<string, string>;
  readings?: Record<string, string>;
  /** Per result the node uses directly: the hash of that result's verdict as the node's referee was
   * shown it (`basisInputs` `verdictOf`). Absent under scheme 4, and for a node using no graded result. */
  verdicts?: Record<string, string>;
  /** Material of the node alone, not of its users (the fixer's note on a repaired node). */
  own?: string;
}

const sha = (t: string): string => createHash("sha256").update(t).digest("hex");

/**
 * The scoped clauses of a symbol entry (`CoreSymbol.scoped`) APPLICABLE to node `id` — what a
 * consumer about that one node reads beside the entry's general `def` (the statement referee's
 * symbol rows, the node's verdict basis). A clause tagged with result T applies to
 *   - a statement X when T is X or in X's `depends_on` closure (the closure a basis reads: X is
 *     judged on what it rests on, read as those results read the symbol);
 *   - an assumption or definition N when N is in T's closure (only statements carry `depends_on`:
 *     a hypothesis is read through the results using it, as `symbolUsers` binds it) — as context:
 *     how T reads the symbol, never what N's own words are judged by (`symbolEntryShown`).
 * `ids` several nodes (a shard's symbol rows): the clauses applicable to any of them. Each applicable
 * clause is returned with `results` cut to the tagged results that make it apply (in the clause's
 * order): what the node's referee is shown and its basis hashes. A tag naming no statement of the
 * core applies to nothing. Pure.
 */
export function applicableClauses(core: Core, ids: string | Iterable<string>, clauses: readonly ScopedClause[] | undefined): ScopedClause[] {
  if (!clauses?.length) return [];
  const statements = new Set(core.statements.map((st) => st.id));
  const closures = new Map<string, Set<string>>();
  const closure = (x: string): Set<string> => closures.get(x) ?? closures.set(x, closureOf(core, x).seen).get(x)!;
  const nodes = typeof ids === "string" ? [ids] : [...ids];
  const applies = (t: string): boolean => statements.has(t) && nodes.some((id) => closure(id).has(t) || (!statements.has(id) && closure(t).has(id)));
  return clauses.flatMap((c) => {
    const results = [...new Set(c.results)].filter(applies);
    return results.length > 0 ? [{ results, text: c.text }] : [];
  });
}

/**
 * The settings of `core.sampling_model` that apply to a node of `ids`, or every setting when that
 * cannot be told. A setting's text names the results using it, by paper label (`tex_locator.label`)
 * or core id; a block split off a result is in its parent's settings, and an assumption or
 * definition — which no setting lists — in those of the result stating it and of every result
 * using it. A node of `ids` that no setting reaches this way leaves the question open. Pure.
 */
export function applicableSettings(core: Core, ids: Iterable<string>): Record<string, unknown> | undefined {
  const model = core.sampling_model;
  if (!model) return undefined;
  const byId = new Map([...core.statements, ...core.assumptions, ...core.definitions].map((n) => [n.id, n as { tex_locator?: { label?: string | null } | null }] as const));
  const statements = new Map(core.statements.map((st) => [st.id, st] as const));
  const texts = Object.entries(model).map(([k, v]) => [k, typeof v === "string" ? v : JSON.stringify(v)] as const);
  const names = (text: string, name: string): boolean => {
    for (let i = text.indexOf(name); i >= 0; i = text.indexOf(name, i + 1)) {
      if (!/[\w:-]/.test(text[i - 1] ?? " ") && !/[\w:-]/.test(text[i + name.length] ?? " ")) return true;
    }
    return false;
  };
  const withParent = (id: string): string[] => [id, ...(statements.get(id)?.split_from ? [statements.get(id)!.split_from!] : [])];
  const keep = new Set<string>();
  for (const id of ids) {
    const via = statements.has(id) ? withParent(id) : [id, ...core.statements.filter((st) => st.depends_on.includes(id)).flatMap((st) => withParent(st.id))];
    const labels = new Set(via.flatMap((v) => [v, byId.get(v)?.tex_locator?.label ?? v]));
    const hit = texts.filter(([, text]) => [...labels].some((l) => names(text, l))).map(([k]) => k);
    if (hit.length === 0) return model;
    for (const k of hit) keep.add(k);
  }
  return Object.fromEntries(Object.entries(model).filter(([k]) => keep.has(k)));
}

/** How a text names result `id` of the core: its environment word and `\ref{<label>}` (typeset to
 * the number the paper prints); a block a repair split off a result (it has no label) as the result
 * split from its parent; a published result a proof invokes (`cited_in`) by its citation and that proof's result; any other result without a label, or an id the core does not hold, by the
 * id. */
export function resultTexName(core: Core, id: string): string {
  const st = core.statements.find((x) => x.id === id);
  // A result a proof invokes by citation: by its citation, at the result whose proof uses it.
  if (st?.cited_in && st.cited_in !== id && st.source) return `\\cite[${st.source.locator}]{${st.source.cite}}, used in the proof of ${resultTexName(core, st.cited_in)}`;
  const label = st?.tex_locator?.label;
  if (label) return `${resultWord(st)}~\\ref{${label}}`;
  if (st?.split_from && st.split_from !== id) return `the result split from ${resultTexName(core, st.split_from)}`;
  return st ? `${resultWord(st)} ${id}` : id;
}

/** A scoped clause as it is read: "In <its results' names>: <text>" (`nameOf`: `resultTexName`, or
 * a consumer's own way to name a result to its reader). */
export function scopedClauseText(c: ScopedClause, nameOf: (id: string) => string): string {
  return `In ${[...new Set(c.results.map(nameOf))].join(", ")}: ${c.text}`;
}

/** A reading IN FULL, wherever one text shows a symbol's whole reading (the annotated paper, the
 * report): the general part, then every scoped clause led by its results' names. A result `nameOf`
 * cannot name (null: its id is no result of the paper any more — the symbol is graded afresh on the
 * next pass, `referee_symbols.ts` `staleTags`) is left out, and a clause naming none with it: a dead
 * id is never printed. A reading without clauses is its general part, unchanged. */
export function fullReadingText(reading: { reading: string; scoped?: readonly ScopedClause[] }, nameOf: (id: string) => string | null): string {
  const live = (reading.scoped ?? []).flatMap((c) => {
    const names = c.results.flatMap((id) => nameOf(id) ?? []);
    return names.length > 0 ? [`In ${[...new Set(names)].join(", ")}: ${c.text}`] : [];
  });
  return [reading.reading, ...live].join(" ");
}

/** A symbol entry as a prompt about some nodes shows it: the entry, and each `scoped` clause
 * applicable to a node of `ids` as that node's basis reads it (`scopedClauseText` of its
 * `applicableClauses`: shown = hashed) followed by the nodes it reaches — `binds` the results, is
 * `context for` the hypotheses and definitions (a label read off the node's kind: no basis input) —
 * one line per distinct rendering, so a shard of several nodes shows each of them exactly its own lines, labelled. `ids`
 * null (a prompt about the whole paper): every clause, with every result it names that the core
 * holds. An entry with nothing to show there has no `scoped`. */
export function symbolEntryShown(core: Core, x: CoreSymbol, ids: Iterable<string> | null): Record<string, unknown> {
  const { scoped, ...entry } = x;
  const name = (id: string): string => resultTexName(core, id);
  const nodes = ids === null ? null : [...ids];
  const statements = new Set(core.statements.map((st) => st.id));
  const lines = (scoped ?? []).flatMap((c) => {
    if (nodes === null) return liveClauses(core, [c]).map((l) => scopedClauseText(l, name));
    const on = new Map<string, { binds: string[]; context: string[] }>();
    for (const id of nodes) for (const a of applicableClauses(core, id, [c])) ((e) => (statements.has(id) ? e.binds : e.context).push(id))(((t) => on.get(t) ?? on.set(t, { binds: [], context: [] }).get(t)!)(scopedClauseText(a, name)));
    return [...on].map(([t, e]) => `${t} [${[e.binds.length > 0 ? `binds ${e.binds.join(", ")}` : "", e.context.length > 0 ? `context for ${e.context.join(", ")}` : ""].filter(Boolean).join("; ")}]`);
  });
  return lines.length > 0 ? { ...entry, scoped: lines } : entry;
}

/** `clauses` with each tag that is no statement of the core removed, and a clause left with none:
 * what the table hands on (`buildCore`) and a whole-paper prompt shows — never a dead id. */
function liveClauses(core: Core, clauses: readonly ScopedClause[]): ScopedClause[] {
  const statements = new Set(core.statements.map((st) => st.id));
  return clauses.flatMap((c) => ((results) => (results.length > 0 ? [{ results, text: c.text }] : []))([...new Set(c.results)].filter((r) => statements.has(r))));
}

function closureOf(core: Core, id: string): { byId: Map<string, { depends_on?: string[] }>; seen: Set<string> } {
  const byId = new Map<string, { depends_on?: string[] }>(
    [...core.statements, ...core.assumptions, ...core.definitions].map((n) => [n.id, n as { depends_on?: string[] }]),
  );
  const seen = new Set<string>();
  const queue = [id];
  while (queue.length > 0) {
    const x = queue.shift() as string;
    if (seen.has(x) || !byId.has(x)) continue;
    seen.add(x);
    queue.push(...(byId.get(x)!.depends_on ?? []));
  }
  return { byId, seen };
}

/** Per core: every node by id with its kind word, and the statement ids (memo — a basis reads them per node). */
const SHOWN_INDEX = new WeakMap<Core, { byId: Map<string, Record<string, unknown>>; kind: Map<string, string>; statements: Set<string> }>();
function shownIndex(core: Core): { byId: Map<string, Record<string, unknown>>; kind: Map<string, string>; statements: Set<string> } {
  let ix = SHOWN_INDEX.get(core);
  if (!ix) {
    const byId = new Map<string, Record<string, unknown>>();
    const kind = new Map<string, string>();
    for (const a of core.assumptions) (byId.set(a.id, a as unknown as Record<string, unknown>), kind.set(a.id, "assumption"));
    for (const d of core.definitions) (byId.set(d.id, d as unknown as Record<string, unknown>), kind.set(d.id, "definition"));
    // … a result by the word its prompts print for it (`resultWord`: its environment's, else its kind).
    for (const st of core.statements) (byId.set(st.id, st as unknown as Record<string, unknown>), kind.set(st.id, resultWord(st).toLowerCase()));
    SHOWN_INDEX.set(core, (ix = { byId, kind, statements: new Set(core.statements.map((st) => st.id)) }));
  }
  return ix;
}

/** Per core: the symbols each node's TEXT names (memo). */
const TEXT_SYMBOLS = new WeakMap<Core, Map<string, Set<string>>>();

/** The names of the symbol-table entries the text of node `id` names — its statement / condition /
 * construction, not its proof nor its `free_symbols` list (a result using the node is shown neither):
 * what a result USING the node reads of it. */
function symbolsNamedByText(core: Core, id: string): Set<string> {
  let memo = TEXT_SYMBOLS.get(core);
  if (!memo) TEXT_SYMBOLS.set(core, (memo = new Map()));
  const hit = memo.get(id);
  if (hit) return hit;
  const n = shownIndex(core).byId.get(id);
  const out = new Set<string>();
  if (n) {
    const text = usedText(n);
    const canon = canonicalTokens(text);
    for (const x of core.symbols) if (symbolOccurrences(text, symbolPattern(x.name), canon).length > 0) out.add(x.name);
  }
  memo.set(id, out);
  return out;
}

const usedText = (n: Record<string, unknown>): string => String(n.statement ?? n.condition ?? n.construction ?? "");

/** A node as a result USING it is shown it (the shard's "What they use", `compactCore`): its id, kind
 * word, paper label (what a `\ref` to it names — never its line numbers) and text, the text WHOLE (the
 * prompt cuts a long one and points to `discovery/core.json` for the rest, so the referee may read
 * all of it) and without its line breaks; a V1.5-appended condition by its meaning. */
/** The host of an inline cited leaf as it stands in the core: the result itself and the blocks a
 * repair split off it (`split_from`) — after a split, the hypotheses and the cited step may be a block's. */
export function hostParts(core: Core, host: string): string[] {
  return core.statements.filter((s) => s.id === host || s.split_from === host).map((s) => s.id);
}

function usedView(ix: ReturnType<typeof shownIndex>, id: string): string {
  const n = ix.byId.get(id)!;
  const text = isReadingAddition(n as unknown as CoreAssumption) ? normalizeBasisText(usedText(n)) : usedText(n).replace(/\s+/g, " ").trim();
  return JSON.stringify([id, ix.kind.get(id), (n.tex_locator as { label?: string | null } | undefined)?.label ?? null, text]);
}

/**
 * The inputs of the basis of a verdict on node `id` (scheme `BASIS_SCHEME`) — what its shard shows
 * the referee, or names as readable (`referee_shard_prompts.ts` `buildShardPrompt`, `shard.txt`):
 *   - the node as it stands in the core (its shard prints the record), without its derived user-side
 *     fields (`used_by`); its own `extra` (the cited source a cited leaf was checked against,
 *     verbatim) and `own` material (the repairs its shard shows it, `stage_v1_5.ts` `repairBasis`);
 *   - each node it uses DIRECTLY, as shown (`usedView`: id, kind, whole text); of a RESULT it uses,
 *     also the hypotheses and definitions that result is stated under (their ids and texts — to apply
 *     a result is to meet these) and its verdict as shown (`verdictOf`: a hash of the dependency line,
 *     or undefined when the node is shown none). Never that result's proof, nor the results it rests
 *     on: the node's referee takes it as graded, so a change below reaches the node only by changing
 *     the text or the verdict of what it uses — and then in the same pass (`stage_v1_5.ts`
 *     `partitionByBasis`);
 *   - the symbol-table entries its record names (`symbolsUsedByNode`) and those the texts of the nodes
 *     it uses name (`symbolsNamedByText`), closed under the entries' `refs`, by their meaning, each
 *     with the scoped clauses applicable to the node only (`applicableClauses`);
 *   - the symbol readings binding it or a node it uses (`extra`, by their meaning);
 *   - of an inline cited leaf (`cited_in`), its host as shown: text, what it is stated under, a
 *     repair's proof change.
 */
export function basisInputs(
  core: Core,
  id: string,
  extra: BasisExtra = new Map(),
  own?: string,
  verdictOf: (dep: string) => string | undefined = () => undefined,
): BasisInputs {
  const ix = shownIndex(core);
  const node = ix.byId.get(id);
  const depsOf = (k: string): string[] => [...new Set((ix.byId.get(k)?.depends_on as string[] | undefined) ?? [])].filter((d) => d !== k && ix.byId.has(d)).sort();
  const deps = depsOf(id);
  const table = new Map(core.symbols.map((x) => [x.name, x] as const));
  const used = new Set([...symbolsUsedByNode(core, id), ...deps.flatMap((d) => [...symbolsNamedByText(core, d)])]);
  const todo = [...used];
  while (todo.length > 0) {
    for (const r of table.get(todo.pop()!)?.refs ?? []) if (table.has(r) && !used.has(r)) (used.add(r), todo.push(r));
  }
  // Which symbol readings bind the node and each node it uses (wiring, in the part of that node); the
  // readings themselves hashed apart, by their meaning.
  const meaning = new Map<string, Set<string>>();
  const bound = (k: string): string => {
    const rs = extra.has(k) ? (asExtraEntry(extra.get(k)!).readings ?? []) : [];
    for (const r of rs) {
      const head = `${r.state}|${r.redefined ? "redefined" : "-"}|`;
      (meaning.get(r.symbol) ?? meaning.set(r.symbol, new Set()).get(r.symbol)!).add(head + normalizeBasisText(r.text));
    }
    const names = [...new Set(rs.map((r) => r.symbol))].sort();
    return names.length > 0 ? `\nreadings: ${JSON.stringify(names)}` : "";
  };
  const ownView = JSON.stringify(basisView(node));
  const text = extra.has(id) ? asExtraEntry(extra.get(id)!).text : undefined;
  const parts = [
    ownView + (text !== undefined ? `\n${text}` : "") + bound(id),
    ...deps.map((d) => usedView(ix, d) + (ix.statements.has(d) ? `\nunder: ${JSON.stringify(depsOf(d).filter((h) => !ix.statements.has(h)).map((h) => usedView(ix, h)))}` : "") + bound(d)),
  ];
  // An inline cited leaf (`cited_in`) is graded against its HOST as it stands — the host's text, what
  // it is stated under and a repair's change to its proof, as its shard shows them (`compactCore`),
  // and likewise each block a repair split off it (`hostParts`) — so a repair of the host re-opens it. Never the host's verdict: the host uses the leaf.
  for (const h of typeof node?.cited_in === "string" && node.cited_in !== id ? hostParts(core, node.cited_in) : []) {
    const proof = String(ix.byId.get(h)!.proof_tex ?? "");
    const at = proof.indexOf(PROOF_CHANGE_MARKER);
    parts.push(`host: ${usedView(ix, h)}\nunder: ${JSON.stringify(depsOf(h).filter((d) => !ix.statements.has(d)).map((d) => usedView(ix, d)))}${at >= 0 ? `\n${proof.slice(at)}` : ""}`);
  }
  const verdicts = Object.fromEntries(deps.filter((d) => ix.statements.has(d)).flatMap((d) => ((h) => (h !== undefined ? [[d, h] as const] : []))(verdictOf(d))));
  const hashSets = (m: Map<string, Set<string>>): Record<string, string> =>
    Object.fromEntries([...m.keys()].sort().map((k) => [k, sha([...m.get(k)!].sort().join("\n"))] as const));
  return {
    scheme: BASIS_SCHEME,
    ...(own !== undefined ? { own: sha(own) } : {}),
    node: sha(ownView),
    closure: sha(parts.join("\n")),
    symbols: Object.fromEntries(core.symbols.filter((x) => used.has(x.name)).map((x) => [x.name, symbolEntryHash(x, applicableClauses(core, id, x.scoped).map((c) => scopedClauseText(c, (r) => resultTexName(core, r))))] as const)),
    readings: hashSets(meaning),
    ...(Object.keys(verdicts).length > 0 ? { verdicts } : {}),
  };
}

/**
 * TRANSITION — the inputs of a scheme-4 basis, kept callable so a verdict recorded under scheme 4 is
 * carried over, not graded afresh (`stage_v1_5.ts` `partitionByBasis`): while its scheme-4 basis still
 * holds on the current core, nothing it rested on changed under that wider rule, and it is re-keyed
 * under `BASIS_SCHEME` without a call. Remove (with `basisInputsV4`'s callers) once every run on file
 * has passed one V1.5 pass under scheme 5.
 *
 * Scheme 4: the node as it stands in
 * the core, without its derived user-side fields (`used_by`); every node of its `depends_on` closure,
 * read the same way, with its `extra` material (the cited source a cited leaf was checked against,
 * verbatim; the symbol readings binding a statement, by their meaning); the symbol-table entries
 * those nodes use (`symbolsUsedByNode`, closed under the entries' `refs`), by their meaning — not the
 * whole table, so a fix to a symbol the node never uses keeps its verdict — each with the scoped
 * clauses applicable to the node only (`applicableClauses`).
 */
export function basisInputsV4(core: Core, id: string, extra: BasisExtra = new Map(), own?: string): BasisInputs {
  const { byId, seen } = closureOf(core, id);
  const table = new Map(core.symbols.map((x) => [x.name, x] as const));
  const used = new Set([...seen].flatMap((k) => [...symbolsUsedByNode(core, k)]));
  const todo = [...used];
  while (todo.length > 0) {
    for (const r of table.get(todo.pop()!)?.refs ?? []) if (table.has(r) && !used.has(r)) (used.add(r), todo.push(r));
  }
  const usedEntries = core.symbols.filter((x) => used.has(x.name));
  // The closure with its verbatim extra and which symbol readings bind each of its nodes (wiring);
  // the readings themselves hashed apart, by their meaning.
  const meaning = new Map<string, Set<string>>();
  const parts = [...seen].sort().map((k) => {
    const e = extra.has(k) ? asExtraEntry(extra.get(k)!) : {};
    const rs = e.readings ?? [];
    for (const r of rs) {
      const head = `${r.state}|${r.redefined ? "redefined" : "-"}|`;
      (meaning.get(r.symbol) ?? meaning.set(r.symbol, new Set()).get(r.symbol)!).add(head + normalizeBasisText(r.text));
    }
    const bound = [...new Set(rs.map((r) => r.symbol))].sort();
    return JSON.stringify(basisView(byId.get(k))) + (e.text !== undefined ? `\n${e.text}` : "") + (bound.length > 0 ? `\nreadings: ${JSON.stringify(bound)}` : "");
  });
  const hashSets = (m: Map<string, Set<string>>): Record<string, string> =>
    Object.fromEntries([...m.keys()].sort().map((k) => [k, sha([...m.get(k)!].sort().join("\n"))] as const));
  return {
    scheme: 4,
    ...(own !== undefined ? { own: sha(own) } : {}),
    node: sha(JSON.stringify(basisView(byId.get(id)))),
    closure: sha(parts.join("\n")),
    symbols: Object.fromEntries(usedEntries.map((x) => [x.name, symbolEntryHash(x, applicableClauses(core, id, x.scoped).map((c) => scopedClauseText(c, (r) => resultTexName(core, r))))] as const)),
    readings: hashSets(meaning),
  };
}

/** The basis a set of inputs gives: one hash of what the node is shown of itself and of what it uses
 * (`closure`), the symbol entries read, the symbol readings binding them, the node's own material and
 * the verdicts of the results it uses (the same formula for scheme-4 inputs, which have none). */
export function basisOf(inputs: BasisInputs): string {
  const kv = (m: Record<string, string>): string[] => Object.keys(m).sort().map((k) => `${k}=${m[k]}`);
  const verdicts = kv(inputs.verdicts ?? {});
  return sha(
    [inputs.closure, ...kv(inputs.symbols), "readings:", ...kv(inputs.readings ?? {}), ...(inputs.own !== undefined ? [`own: ${inputs.own}`] : []), ...(verdicts.length > 0 ? ["verdicts:", ...verdicts] : [])].join("\n"),
  );
}

/**
 * The BASIS of a V1.5 verdict on node `id` — what the verdict was given on, as one hash
 * (inputs: `basisInputs`), here without the verdicts of
 * the results it uses (the pass adds them: `partitionByBasis`). A verdict is CARRIED to a
 * later pass exactly when its basis is unchanged; a node whose text, wiring, hypotheses or symbols
 * moved, or that uses a result whose text or verdict moved, gets a fresh grade.
 */
export function nodeFingerprint(core: Core, id: string, extra: BasisExtra = new Map()): string {
  return basisOf(basisInputs(core, id, extra));
}

/** Why a node is graded afresh rather than carried (`regradeCause`), for the delta log. */
export type RegradeCause = "new" | "not clean before" | "no comparable record" | "content" | "note" | "dependency" | "dependency verdict" | "symbol meaning" | "cache withdrawn";

/**
 * Why node's verdict was not carried, from the inputs its last verdict was given on (`prev`, with
 * whether that verdict was clean) and its inputs now (of the same scheme): the first of its own
 * content, its fixer note, what it uses (a hypothesis, a definition, the statement of a result, or the
 * wiring moved), the verdict of a result it uses, the meaning of a symbol entry or reading it reads,
 * or — nothing moved — its cache entry was withdrawn. `null` prev: the node had no verdict.
 */
export function regradeCause(prev: { inputs: BasisInputs | undefined; clean: boolean } | null, cur: BasisInputs): RegradeCause {
  if (prev === null) return "new";
  if (!prev.clean) return "not clean before";
  const p = prev.inputs;
  if (!p || p.scheme !== cur.scheme) return "no comparable record";
  if (p.node !== cur.node) return "content";
  if (p.own !== cur.own) return "note";
  if (p.closure !== cur.closure) return "dependency";
  const same = (a: Record<string, string> | undefined, b: Record<string, string> | undefined): boolean => JSON.stringify(sortKeys(a ?? {})) === JSON.stringify(sortKeys(b ?? {}));
  if (!same(p.symbols, cur.symbols) || !same(p.readings, cur.readings)) return "symbol meaning";
  if (!same(p.verdicts, cur.verdicts)) return "dependency verdict";
  return "cache withdrawn";
}

function sortKeys(m: Record<string, string>): Array<[string, string]> {
  return Object.keys(m).sort().map((k) => [k, m[k]!]);
}

/** Statement ids reachable from `roots` through `depends_on`, roots included. */
export function statementClosure(core: Core, roots: readonly string[]): Set<string> {
  const byId = new Map(core.statements.map((s) => [s.id, s] as const));
  const seen = new Set<string>();
  const queue = [...roots];
  while (queue.length > 0) {
    const id = queue.shift() as string;
    if (seen.has(id) || !byId.has(id)) continue;
    seen.add(id);
    queue.push(...byId.get(id)!.depends_on);
  }
  return seen;
}

/** Statements left out of the Lean formalization: the unfixable ones and every non-key result
 * that rests on them (an unfixable non-statement node descopes the statements using it). A node
 * whose weakened repair the owner DECLINED descopes every result resting on it, key results
 * included: the owner chose to report it refuted rather than formalize less. */
export function descopedStatements(core: Core, file: PatchFileLike): Map<string, string> {
  const out = new Map<string, string>();
  const keys = new Set(file.key_results);
  const unfixable = new Set(file.unfixable.map((u) => u.node));
  // Nodes whose removal traces back to a declined repair: they take key results with them.
  const declined = new Set(file.unfixable.filter((u) => u.declined !== undefined).map((u) => u.node));
  for (const u of file.unfixable) {
    if (core.statements.some((s) => s.id === u.node)) out.set(u.node, `unfixable: ${u.reason}`);
  }
  // A result its repair no longer relies on (`drops`) takes nothing with it.
  const dropped = new Map(file.patches.map((p) => [p.node, new Set(p.drops ?? [])] as const));
  let grew = true;
  while (grew) {
    grew = false;
    for (const s of core.statements) {
      if (out.has(s.id)) continue;
      const deps = s.depends_on.filter((d) => !dropped.get(s.id)?.has(d));
      const hit = deps.find((d) => out.has(d) || unfixable.has(d));
      const viaDeclined = deps.find((d) => declined.has(d));
      if (keys.has(s.id) && !viaDeclined) continue;
      if (hit) {
        const why = viaDeclined ?? hit;
        out.set(s.id, declined.has(why) ? `descoped: rests on ${why}, whose weakened repair the owner declined` : `descoped: rests on ${hit}, which cannot be repaired`);
        if (declined.has(why)) declined.add(s.id);
        grew = true;
      }
    }
  }
  return out;
}

/** The labels a TeX text cites (`\ref`, `\eqref`, `\cref`, `\Cref`, `\autoref`, `\nameref`; a
 * comma list counts each; a comment, from an unescaped `%` to the line's end, cites nothing). Pure. */
export function citedLabels(tex: string): string[] {
  const out = new Set<string>();
  const live = tex.replace(/(^|[^\\])%.*$/gmu, "$1");
  for (const m of live.matchAll(/\\(?:ref|eqref|cref|Cref|autoref|nameref)\*?\{([^}]*)\}/g)) for (const l of m[1]!.split(",")) if (l.trim()) out.add(l.trim());
  return [...out];
}

/**
 * The edits a patch file stands for, against the TRANSCRIBED core: per repair, the node's corrected text
 * (a statement's, an assumption's, a definition's), the hypotheses and definitions its replacement
 * rewrites (`supersedes`) and those the repair declares it no longer uses (`drops`) unwired from it,
 * the proof change; for an assumption or definition with no
 * printed text of its own (its patch changes nothing), each result using it whose statement is
 * restated unwired from it (the restatement states its own version) — when its entry names the
 * results it follows (`consequence_of`), those only —, each result the repair's text
 * cites wired in, and such a node, or one a repair supersedes or drops, removed once no
 * result uses it (directly, or through a class definition's member properties); unfixable results and what
 * rests on them removed; owner readings added.
 */
export function compilePatchEdits(transcribed: Core, file: PatchFileLike): { edits: GraphEdit[]; descoped: Map<string, string> } {
  const edits: GraphEdit[] = [];
  const ids = nodeIds(transcribed);
  const statements = new Map(transcribed.statements.map((s) => [s.id, s] as const));
  const descoped = descopedStatements(transcribed, file);
  const unfixable = new Set(file.unfixable.map((u) => u.node));
  const gone = new Set<string>([...descoped.keys(), ...unfixable]);
  for (const id of gone) if (ids.has(id)) edits.push({ op: "remove_node", id, why: descoped.get(id) ?? "unfixable" });
  // A published result a proof invokes by citation (`cited_in`) is a passage of that proof: it leaves
  // with its host, unless another result that stays uses it.
  for (const s of transcribed.statements) {
    if (!s.cited_in || gone.has(s.id) || !gone.has(s.cited_in)) continue;
    if (transcribed.statements.some((u) => !gone.has(u.id) && u.id !== s.id && u.depends_on.includes(s.id))) continue;
    gone.add(s.id);
    edits.push({ op: "remove_node", id: s.id, why: `a step of the proof of ${s.cited_in}, which is no longer in the core` });
  }

  // Per repair: superseded dependencies, corrected text, proof change.
  const hypotheses = new Set([...transcribed.assumptions.map((a) => a.id), ...transcribed.definitions.map((d) => d.id)]);
  // A hypothesis repaired in its own printed text (its patch has ops) stays where the paper states it;
  // one without printed text of its own (its patch changes nothing) lives on in the restated results:
  // those its entry follows (`consequence_of`), or — the finding being its own — every restated one.
  const restatedAway = new Map(file.patches.filter((p) => hypotheses.has(p.node) && (p.ops?.length ?? 0) === 0).map((p) => [p.node, new Set(p.consequence_of ?? [])] as const));
  const unwired = new Map<string, Set<string>>();
  const unwire = (statement: string, dep: string): void => {
    edits.push({ op: "unwire", statement, dep });
    (unwired.get(statement) ?? unwired.set(statement, new Set()).get(statement)!).add(dep);
  };
  for (const p of file.patches) {
    if (!ids.has(p.node) || gone.has(p.node)) continue;
    const st = statements.get(p.node);
    if (st && isUmbrellaPatch(p)) {
      // An umbrella states nothing of its own: it uses no hypothesis and no result of the paper (its
      // blocks do, each its own), only its blocks (wired below).
      for (const d of st.depends_on) unwire(p.node, d);
      edits.push({ op: "set_statement", id: p.node, statement: UMBRELLA_STATEMENT }, { op: "set_proof", id: p.node, text: UMBRELLA_PROOF }, { op: "set_umbrella", id: p.node });
      continue;
    }
    for (const r of p.supersedes ?? []) if (st) unwire(p.node, r);
    for (const d of p.drops ?? []) if (st?.depends_on.includes(d)) unwire(p.node, d);
    // A restated result states its own version of a hypothesis that has no printed text of its own —
    // not one restated for another reason while the hypothesis's entry names the results it follows:
    // that result still uses the hypothesis as printed.
    if (st && p.corrected_statement !== null) for (const c of st.depends_on) if (((by) => by !== undefined && (by.size === 0 || by.has(p.node)))(restatedAway.get(c))) unwire(p.node, c);
    // What the repair declares it uses (`adds`) is wired last, so it stands whatever was unwired above.
    for (const a of p.adds ?? []) {
      if (!st || (st.depends_on.includes(a) && !unwired.get(p.node)?.has(a))) continue;
      edits.push({ op: "wire", statement: p.node, dep: a });
      unwired.get(p.node)?.delete(a);
    }
    if (p.corrected_statement !== null) edits.push({ op: "set_statement", id: p.node, statement: p.corrected_statement });
    if (!st) continue;
    if (revisesProof(p)) {
      // The printed proof, revised by the repair's ops (the derived `proof_note`): the F stages and the
      // confirming referee read it.
      edits.push({ op: "set_proof", id: p.node, text: `${PROOF_CHANGE_MARKER} the printed proof, revised step by step]\n${p.proof_note}` });
    } else {
      edits.push({ op: "append_proof", id: p.node, text: `${PROOF_CHANGE_MARKER} ${p.proof_note}]` });
    }
  }
  // A result the repair's own text cites (`\ref` and its kin) is one it uses: wired in, unless the label
  // names no single result or the edge would close a cycle.
  const byLabel = new Map<string, string[]>();
  for (const s of transcribed.statements) {
    const label = s.tex_locator?.label;
    if (label && !gone.has(s.id)) byLabel.set(label, [...(byLabel.get(label) ?? []), s.id]);
  }
  const uses = new Map(transcribed.statements.map((s) => [s.id, new Set(s.depends_on)] as const));
  const reaches = (from: string, to: string): boolean => {
    const seen = new Set<string>();
    const stack = [from];
    while (stack.length > 0) {
      const id = stack.pop()!;
      if (id === to) return true;
      if (seen.has(id)) continue;
      seen.add(id);
      stack.push(...(uses.get(id) ?? []));
    }
    return false;
  };
  for (const p of file.patches) {
    if (!statements.has(p.node) || gone.has(p.node) || isUmbrellaPatch(p)) continue;
    const written = [...(p.ops ?? []).map((o) => o.tex), ...(revisesProof(p) ? [] : [p.proof_note])].join("\n");
    for (const label of citedLabels(written)) {
      const hit = byLabel.get(label) ?? [];
      // A result the repair declares it does not use (`drops`: cited only to compare, say) stays unwired.
      if (hit.length !== 1 || hit[0] === p.node || uses.get(p.node)!.has(hit[0]) || reaches(hit[0], p.node) || p.drops?.includes(hit[0])) continue;
      edits.push({ op: "wire", statement: p.node, dep: hit[0] });
      uses.get(p.node)!.add(hit[0]);
    }
  }
  // A repair's split-off blocks (`corollaries`): one statement node each, of the parent's kind; it
  // depends on its `adds`, on the results its text cites, and on the parent only when it is a COROLLARY
  // of it (`splitKind`: its proof cites the parent) — a proposition block is a separate result the
  // printed statement bundled in, and a change of the parent leaves it alone. `split_from` is where it
  // came from and where it is shown, for both kinds. The printed result is the parent TOGETHER with
  // its blocks, so every result using the parent uses them too — unless a result a block cites rests
  // on that user (the edge would close a cycle).
  const split = new Set<string>();
  const splitOf = new Map<string, string>();
  for (const p of file.patches) {
    const st = statements.get(p.node);
    if (!st || gone.has(p.node)) continue;
    const users = transcribed.statements.filter((s) => s.id !== p.node && !gone.has(s.id) && uses.get(s.id)!.has(p.node) && !unwired.get(s.id)?.has(p.node)).map((s) => s.id);
    const umbrella = isUmbrellaPatch(p);
    // Blocks are told apart by their statement's meaning (`splitCorollaryId`): two that read the same
    // are one block, and an umbrella (hand-written, say) left with fewer than two is the file's fault.
    const blockIds = new Set((p.corollaries ?? []).map((c) => splitCorollaryId(p.node, c.statement)));
    if (umbrella && blockIds.size < 2) throw new CoreGraphInputError("patches.json", [`${p.node}: an umbrella needs at least two blocks that differ (${p.corollaries?.length ?? 0} given, ${blockIds.size} distinct by statement)`]);
    // The umbrella rests on its blocks alone from here on.
    if (umbrella) uses.set(p.node, new Set());
    for (const c of p.corollaries ?? []) {
      const id = splitCorollaryId(p.node, c.statement);
      if (split.has(id)) continue;
      split.add(id);
      splitOf.set(id, p.node);
      // A result resting on the umbrella is never a ground of one of its blocks: the edge would close a
      // cycle (the fixer is told so, `validatePatchFile`).
      const cited = citedLabels(`${c.statement}\n${c.follows}`).map((l) => byLabel.get(l) ?? []).filter((hit) => hit.length === 1 && hit[0] !== p.node && !(umbrella && reaches(hit[0]!, p.node))).map((hit) => hit[0]!);
      const deps = [...new Set([...(splitKind(c.follows, st.tex_locator?.label, umbrella) === "corollary" ? [p.node] : []), ...(c.adds ?? []).filter((a) => hypotheses.has(a) && !gone.has(a)), ...cited])];
      edits.push({ op: "add_statement", node: { id, kind: st.kind, statement: c.statement, depends_on: deps, status: "proved", proof_tex: c.follows, split_from: p.node } as CoreStatement });
      for (const u of users) if (!cited.some((r) => reaches(r, u))) edits.push({ op: "wire", statement: u, dep: id });
      if (umbrella) {
        edits.push({ op: "wire", statement: p.node, dep: id });
        uses.set(id, new Set(cited));
        uses.get(p.node)!.add(id);
      }
    }
  }
  // A reading of a result (the owner's, its repair's) binds the blocks split off it, of either kind:
  // a proposition block was stated inside the printed result, in the words the reading is pinned on.
  const corollariesOf = (node: string): string[] => [...split].filter((id) => splitOf.get(id) === node);
  const keptByCorollary = new Set(file.patches.filter((p) => statements.has(p.node) && !gone.has(p.node)).flatMap((p) => (p.corollaries ?? []).flatMap((c) => c.adds ?? [])));
  // A published result a proof invoked by citation (`cited_in`), dropped by that result's repair: its
  // text is a passage of the proof the repair replaces, so it leaves the core once no surviving result uses it
  // (before the hypotheses below: one only the leaf used leaves with it).
  for (const p of file.patches) {
    if (!ids.has(p.node) || gone.has(p.node)) continue;
    for (const id of p.drops ?? []) {
      if (gone.has(id) || statements.get(id)?.cited_in !== p.node) continue;
      if (transcribed.statements.some((s) => !gone.has(s.id) && s.depends_on.includes(id) && !unwired.get(s.id)?.has(id))) continue;
      edits.push({ op: "remove_node", id, why: `the repaired proof of ${p.node} no longer takes the step from the cited work` });
      // gone from here on: no reading below is wired into it
      gone.add(id);
    }
  }

  // A hypothesis a repair restates (one with no printed text of its own, or one a corrected statement
  // supersedes or drops) leaves the core once no surviving result uses it: graded alone it has nothing to say.
  const superseded = new Set(file.patches.filter((p) => ids.has(p.node) && !gone.has(p.node)).flatMap((p) => [...(p.supersedes ?? []), ...(p.drops ?? []), ...(isUmbrellaPatch(p) ? statements.get(p.node)?.depends_on ?? [] : [])]));
  for (const id of new Set([...restatedAway.keys(), ...superseded])) {
    if (gone.has(id) || !hypotheses.has(id)) continue;
    // Used directly, or as a member property of a class definition a result uses.
    const carved = new Set(transcribed.definitions.filter((d) => (d.by_member_properties ?? []).includes(id)).map((d) => d.id));
    const added = file.patches.some((p) => !gone.has(p.node) && (p.adds ?? []).includes(id));
    const used = carved.size > 0 || added || keptByCorollary.has(id) || transcribed.statements.some((s) => !gone.has(s.id) && s.depends_on.includes(id) && !unwired.get(s.id)?.has(id));
    if (!used) edits.push({ op: "remove_node", id, why: "restated into the results that use it" });
  }
  // Owner readings: one node each, wired into the node it settles (a statement) or every surviving
  // statement using it (an assumption / definition), like a referee pin.
  for (const r of file.owner_readings ?? []) {
    const into = (statements.has(r.node) ? [r.node, ...corollariesOf(r.node)] : transcribed.statements.filter((s) => s.depends_on.includes(r.node)).map((s) => s.id)).filter((w) => !gone.has(w));
    if (into.length === 0) continue;
    const reason = r.kind === "bookkeeping" ? `side condition of ${r.node} stated by the paper's owner` : `${PIN_REASON_PREFIX}${r.node}: adopted by the paper's owner`;
    edits.push({
      op: "add_assumption",
      node: { id: r.id, kind: "regularity", condition: r.reading, bookkeeping: { flag: true, added_by: OWNER_ADDED_BY, reason } } as CoreAssumption,
    });
    for (const w of into) edits.push({ op: "wire", statement: w, dep: r.id });
  }
  // A repair's readings: likewise, one node per reading.
  const stated = new Set<string>();
  for (const p of file.patches) {
    if (!ids.has(p.node) || gone.has(p.node)) continue;
    const into = (statements.has(p.node) ? [p.node, ...corollariesOf(p.node)] : transcribed.statements.filter((s) => s.depends_on.includes(p.node)).map((s) => s.id)).filter((w) => !gone.has(w));
    for (const reading of p.readings ?? []) {
      const id = patchReadingId(p.node, reading);
      if (into.length === 0 || stated.has(id)) continue;
      stated.add(id);
      edits.push({
        op: "add_assumption",
        node: { id, kind: "regularity", condition: reading, bookkeeping: { flag: true, added_by: PATCH_ADDED_BY, reason: `${PIN_REASON_PREFIX}${p.node}: stated by the repair` } } as CoreAssumption,
      });
      for (const w of into) edits.push({ op: "wire", statement: w, dep: id });
    }
  }
  return { edits, descoped };
}

// ---------------------------------------------------------------------------------------------
// Symbols: the symbol referee's fixes and the statements a symbol reading binds
// ---------------------------------------------------------------------------------------------

/** Hash of a symbol as recorded (name, type, def, refs), its type and def by their meaning
 * (`normalizeBasisText`): a symbol-table `fix` applies only to the entry it was graded on, and a
 * re-typesetting of that entry is the same entry. */
export function symbolSourceHash(sym: CoreSymbol): string {
  const def = sym.def === undefined ? null : normalizeBasisText(sym.def);
  return createHash("sha256").update(JSON.stringify({ name: sym.name, type: normalizeBasisText(sym.type), def, refs: sym.refs ?? [] })).digest("hex");
}

/** The slice of a symbol verdict the build reads. */
export type SymbolFixLike = Pick<V15SymbolVerdict, "name" | "meaning" | "fix" | "source"> & Partial<Pick<V15SymbolVerdict, "ambiguity" | "reading">>;

/** The `set_symbol` edits of the symbol referee's grades, for each verdict whose `source` is the
 * symbol as the core records it now (a re-transcribed symbol drops a stale grade): a `drift` fix
 * corrects `type` / `space` / `def`, and a `pinned` reading IS the symbol's settled meaning — its
 * general part the entry's `def`, its scoped clauses the entry's `scoped`. The table is what every
 * later stage reads; a reading never becomes a hypothesis. */
export function compileSymbolEdits(core: Core, verdicts: readonly SymbolFixLike[]): GraphEdit[] {
  const edits: GraphEdit[] = [];
  for (const v of verdicts) {
    const sym = core.symbols.find((x) => x.name === v.name);
    if (!sym || (v.source !== undefined && v.source !== symbolSourceHash(sym))) continue;
    const fix = v.meaning === "drift" ? v.fix : null;
    const type = fix?.type?.trim() || undefined;
    const space = fix?.space?.trim() || undefined;
    const reading = v.ambiguity === "pinned" ? v.reading?.reading.trim() || undefined : undefined;
    const def = reading ?? (fix?.def?.trim() || undefined);
    const scoped = reading !== undefined && v.reading?.scoped?.length ? v.reading.scoped.map((c) => ({ results: [...c.results], text: c.text.trim() })) : undefined;
    if (type === undefined && space === undefined && def === undefined) continue;
    edits.push({ op: "set_symbol", name: v.name, ...(type !== undefined ? { type } : {}), ...(space !== undefined ? { space } : {}), ...(def !== undefined ? { def } : {}), ...(scoped !== undefined ? { scoped } : {}) });
  }
  return edits;
}

/**
 * The statements a reading of symbol `name` binds: every statement that uses the symbol itself
 * (its `free_symbols`, or its text) or rests on a hypothesis or definition that does. Only
 * statements carry `depends_on`, so a hypothesis or definition using the symbol is bound through
 * the statements using it (`bindingReadings` shows the reading under it too). V1.5's own
 * additions (pins, bookkeeping conditions) are not users.
 */
export function symbolUsers(core: Core, name: string): string[] {
  const pat = symbolPattern(name);
  const norm = normalizeSymbol(name);
  const uses = (n: { free_symbols?: string[] }, text: string): boolean =>
    (n.free_symbols ?? []).some((f) => normalizeSymbol(f) === norm) || mentionsSymbol(text, pat);
  const carriers = new Set([
    ...core.assumptions.filter((a) => !isReadingAddition(a) && uses(a, a.condition)).map((a) => a.id),
    ...core.definitions.filter((d) => uses(d, d.construction ?? "")).map((d) => d.id),
  ]);
  return core.statements.filter((st) => uses(st, st.statement) || st.depends_on.some((d) => carriers.has(d))).map((st) => st.id);
}

/**
 * The results symbol `name` is USED in — the one notion of use of the symbol side: what a scoped
 * clause of its reading may be tagged with, the list its referee is shown, the statements its
 * reading is read from. A result uses the symbol when its record names it (`symbolsUsedByNode`: its
 * `free_symbols`, statement or proof — what its shard shows the symbol's row for) or a hypothesis or
 * definition it is stated under does (a clause reaches that node through the result,
 * `applicableClauses`). V1.5's own additions (pins, bookkeeping conditions) are not carriers.
 */
export function resultsUsingSymbol(core: Core, name: string): string[] {
  const carriers = new Set([...core.assumptions.filter((a) => !isReadingAddition(a)), ...core.definitions].filter((n) => symbolsUsedByNode(core, n.id).has(name)).map((n) => n.id));
  return core.statements.filter((st) => symbolsUsedByNode(core, st.id).has(name) || st.depends_on.some((d) => carriers.has(d))).map((st) => st.id);
}

/** How a symbol pin names what it pins: `pins reading of symbol <name>: <evidence>`. */
export const SYMBOL_PIN_OF = "symbol ";

// ---------------------------------------------------------------------------------------------
// Compilation: the referee's acceptance additions
// ---------------------------------------------------------------------------------------------

/**
 * One `ass:bk-<n>` per `bookkeeping` grade, wired into the statement that needs it; one
 * `ass:pin-<n>` per pinned reading, wired into the statement it disambiguates or — for a
 * definition / assumption node — into every statement that depends on it (an unused one keeps
 * its pin unwired). `free_symbols` is
 * deliberately OMITTED rather than `[]`: an absent list means "may use any symbol", while `[]`
 * would exempt a referee-authored condition from symbol invalidation. Only a `bookkeeping` grade
 * adds a condition (the contract check is the first lock; this is the second).
 *
 * Ids are STABLE across rebuilds when `ids` is given (`addedIdKey` → id, `discovery/added_ids.json`;
 * extended in place): an addition seen before keeps its id, a new one takes the next number never
 * used, and a retired number is never reused — so adding or dropping one condition renumbers no other
 * and a Lean tag never silently lands on another reading. Without `ids`, numbering is by order.
 */
export function compileReviewEdits(
  core: Core,
  review: V15Review,
  ids?: Record<string, string>,
): { edits: GraphEdit[]; added: Array<{ id: string; node: string }> } {
  const edits: GraphEdit[] = [];
  const added: Array<{ id: string; node: string }> = [];
  const taken = new Set(core.assumptions.map((a) => a.id));
  const reserved = new Set(Object.values(ids ?? {}));
  const fresh = (prefix: string, key: string): string => {
    const known = ids?.[key];
    if (known?.startsWith(prefix) && !taken.has(known)) {
      taken.add(known);
      return known;
    }
    let n = 0;
    let id: string;
    do {
      n += 1;
      id = `${prefix}${n}`;
    } while (taken.has(id) || reserved.has(id));
    taken.add(id);
    if (ids) ids[key] = id;
    return id;
  };
  // A symbol's pinned reading is its `def` in the table (`compileSymbolEdits`), never an assumption.
  for (const node of review.nodes) {
    const bk = node.bookkeeping_assumption;
    if (!bk || node.correctness !== "bookkeeping") continue;
    if (!core.statements.some((s) => s.id === node.id)) {
      throw new Error(`V1.5: bookkeeping assumption for "${node.id}", which is not a core statement — the contract check should have caught this.`);
    }
    const id = fresh("ass:bk-", addedIdKey("bk", node.id, bk.condition));
    edits.push({ op: "add_assumption", node: { id, kind: "regularity", condition: bk.condition, bookkeeping: { flag: true, added_by: REVIEW_ADDED_BY, reason: bk.reason } } as CoreAssumption });
    edits.push({ op: "wire", statement: node.id, dep: id });
    added.push({ id, node: node.id });
  }
  for (const node of review.nodes) {
    if (node.ambiguity !== "pinned" || !node.reading) continue;
    const reading = node.reading.reading;
    // A reading of an assumption's / definition's phrase noticed where a result uses it binds every
    // result using that node, as a pin graded on the node itself does.
    const of = node.reading.of;
    const site = of && of !== node.id && [...core.assumptions, ...core.definitions].some((n) => n.id === of) ? of : node.id;
    const targets = (
      core.statements.some((s) => s.id === site)
        ? [site]
        : core.statements.filter((s) => s.depends_on.includes(site)).map((s) => s.id)
    );
    const id = fresh("ass:pin-", addedIdKey("pin", site, reading));
    edits.push({
      op: "add_assumption",
      node: { id, kind: "regularity", condition: reading, bookkeeping: { flag: true, added_by: REVIEW_ADDED_BY, reason: `${PIN_REASON_PREFIX}${site}: ${node.reading.evidence}` } } as CoreAssumption,
    });
    // Keep a pin on an unused assumption / definition in the accepted core even though there is
    // no result to wire it into. F2 still realizes and F2.5 still reviews every such node; without
    // the assumption record their prompts lose the binding reading and reopen the settled ambiguity.
    for (const t of targets) edits.push({ op: "wire", statement: t, dep: id });
    added.push({ id, node: node.id });
  }
  return { edits, added };
}

/** The stable-id key of a referee addition: its kind, the node it settles, its text (spacing ignored). */
export function addedIdKey(kind: "bk" | "pin", node: string, text: string): string {
  return `${kind}|${node}|${text.replace(/\s+/g, " ").trim()}`;
}

/** How a pinned reading's `bookkeeping.reason` opens: `pins reading of <node>: <evidence>`. */
export const PIN_REASON_PREFIX = "pins reading of ";

/** The pinned readings (`ass:pin-n` by the referee, `ass:pin-owner-n` by the paper's owner) wired
 * into statement `id` of an accepted core, each with the node whose reading it pins. */
export function pinsOn(core: Core, id: string): Array<{ id: string; node: string; reading: string; by: "referee" | "owner" }> {
  const st = core.statements.find((s) => s.id === id);
  if (!st) return [];
  const out: Array<{ id: string; node: string; reading: string; by: "referee" | "owner" }> = [];
  for (const a of core.assumptions) {
    const reason = a.bookkeeping?.reason ?? "";
    if (!isReadingAddition(a) || !a.id.startsWith("ass:pin-") || !st.depends_on.includes(a.id)) continue;
    if (!reason.startsWith(PIN_REASON_PREFIX)) continue;
    const node = reason.slice(PIN_REASON_PREFIX.length).split(": ")[0]!.trim();
    out.push({ id: a.id, node, reading: a.condition, by: a.bookkeeping?.added_by === OWNER_ADDED_BY ? "owner" : "referee" });
  }
  return out;
}

/** The conditions statement `id` of an accepted core carries beyond the paper's text (`ass:bk-n` by
 * the referee, `ass:bk-owner-n` by the paper's owner): what the paper handed back must state there. */
export function conditionsOn(core: Core, id: string): Array<{ id: string; condition: string; by: "referee" | "owner" }> {
  const st = core.statements.find((s) => s.id === id);
  if (!st) return [];
  return core.assumptions
    .filter((a) => isReadingAddition(a) && a.id.startsWith("ass:bk-") && st.depends_on.includes(a.id))
    .map((a) => ({ id: a.id, condition: a.condition, by: a.bookkeeping?.added_by === OWNER_ADDED_BY ? "owner" as const : "referee" as const }));
}

/** A condition V1.5 appended to the paper on acceptance, as the F stages must read it. */
export interface BindingReading {
  /** The appended assumption (`ass:pin-n` / `ass:bk-n`). */
  id: string;
  /** `pin`: the reading of an ambiguous phrase of `of`; `bookkeeping`: a condition `of` needs. */
  kind: "pin" | "bookkeeping";
  of: string;
  text: string;
}

/**
 * The binding readings of core node `id` (user decision 2026-09-23): the conditions V1.5 appended
 * that settle how the node is to be read. For a statement: every pinned reading and bookkeeping
 * condition wired into it. For an assumption or definition: the pinned readings of that node, and
 * those wired into every statement using it (its reading is fixed where it is used; `ownOnly`
 * drops these). A condition V1.5 appended has none. Deduplicated, in core order.
 */
export function bindingReadings(core: Core, id: string, opts: { ownOnly?: boolean } = {}): BindingReading[] {
  if (core.assumptions.some((a) => a.id === id && isReadingAddition(a))) return [];
  const reviewAdded = core.assumptions.filter(isReadingAddition);
  const read = (a: CoreAssumption, owner: string): BindingReading | null => {
    const reason = a.bookkeeping?.reason ?? "";
    if (a.id.startsWith("ass:pin-") && reason.startsWith(PIN_REASON_PREFIX)) {
      return { id: a.id, kind: "pin", of: reason.slice(PIN_REASON_PREFIX.length).split(": ")[0]!.trim(), text: a.condition };
    }
    return a.id.startsWith("ass:bk-") ? { id: a.id, kind: "bookkeeping", of: owner, text: a.condition } : null;
  };
  const wiredInto = (stId: string): BindingReading[] => {
    const st = core.statements.find((s) => s.id === stId);
    if (!st) return [];
    return reviewAdded.filter((a) => st.depends_on.includes(a.id)).map((a) => read(a, stId)).filter((r): r is BindingReading => r !== null);
  };
  let out: BindingReading[];
  if (core.statements.some((s) => s.id === id)) {
    out = wiredInto(id);
  } else {
    const carved = new Set(core.definitions.filter((d) => (d.by_member_properties ?? []).includes(id)).map((d) => d.id));
    const users = core.statements.filter((s) => s.depends_on.some((d) => d === id || carved.has(d))).map((s) => s.id);
    const own = reviewAdded.map((a) => read(a, id)).filter((r): r is BindingReading => r !== null && r.kind === "pin" && r.of === id);
    out = opts.ownOnly ? own : [...own, ...users.flatMap(wiredInto)];
  }
  return out.filter((r, i) => out.findIndex((x) => x.id === r.id) === i);
}

/** One line for a prompt: `Pinned readings (binding): <id> (reading of <node>): <text>; …`, or "".
 * An owner's reading (`ass:pin-owner-*`) reads `(reading of <node>, adopted by the owner)`. */
export function renderBindingReadings(readings: readonly BindingReading[]): string {
  return readings.length === 0 ? "" : `Pinned readings (binding): ${readings.map(bindingReadingItem).join("; ")}`;
}

/** One binding reading as text: `<id> (reading of <node>): <text>`. */
export function bindingReadingItem(r: BindingReading): string {
  const by = r.id.startsWith(OWNER_PIN_PREFIX) ? ", adopted by the paper's owner" : r.id.startsWith(PATCH_PIN_PREFIX) ? ", stated by its repair" : "";
  return `${r.id} (${r.kind === "pin" ? `reading of ${r.of}${by}` : `condition of ${r.of}`}): ${r.text}`;
}

// ---------------------------------------------------------------------------------------------
// The build
// ---------------------------------------------------------------------------------------------

export interface BuildOutcome {
  core: Core;
  /** Statements removed as unfixable or resting on something unfixable, with the reason. */
  descoped: Map<string, string>;
  /** Referee additions (`bk` / `pin`), in order, with the node each serves. */
  added: Array<{ id: string; node: string }>;
}

/** The invariant on the TRANSCRIBED core alone (`used_by` derived first):
 * a hand-edited `core.transcribed.json` that fails this cannot be built on. */
export function transcribedCoreProblems(transcribed: Core): string[] {
  return checkCoreInvariants(normalizeCore(transcribed, transcribed));
}

/**
 * `core.json` as a pure function of its inputs: the transcribed core (the user's version), the
 * patch file (the fixer's repairs), the symbol referee's table fixes (`symbols`, `v1_5_symbols.json`)
 * and, on acceptance, the referee's review (its symbol pins included). Patches are compiled
 * and applied, the review is compiled AGAINST THE PATCHED core and applied, derived structure is
 * recomputed, and the invariant is checked.
 *
 * Failures are told apart: an inconsistent transcribed core, or a patch edit that does not fit
 * it, is a `CoreGraphInputError` (the operator hand-edits both files; the runner checkpoints on
 * it). A review edit that does not fit, or a broken invariant on a core built from consistent
 * inputs, is a plain `Error`: a runner bug, which must surface before a referee call.
 */
export function buildCore(
  transcribed: Core,
  overlays: { patches?: PatchFileLike | null; review?: V15Review | null; symbols?: readonly SymbolFixLike[] | null; addedIds?: Record<string, string> } = {},
): BuildOutcome {
  const transcribedBad = transcribedCoreProblems(transcribed);
  if (transcribedBad.length > 0) throw new CoreGraphInputError("core.transcribed.json", transcribedBad);
  let core = structuredClone(transcribed) as Core;
  // The symbol referee's table fixes (stale ones — graded on another version of the symbol — skipped).
  if (overlays.symbols?.length) core = applyEdits(core, compileSymbolEdits(core, overlays.symbols)).core;
  let descoped = new Map<string, string>();
  const bug = (what: string, lines: string[]): never => {
    throw new Error(`core graph: ${what} — this is a runner bug, not a finding about the paper:\n${lines.map((l) => `  - ${l}`).join("\n")}`);
  };
  if (overlays.patches) {
    const c = compilePatchEdits(transcribed, overlays.patches);
    descoped = c.descoped;
    const r = applyEdits(core, c.edits);
    if (r.rejected.length > 0) {
      throw new CoreGraphInputError("patches.json", r.rejected.map((x) => `${x.reason} (edit ${JSON.stringify(x.edit)})`));
    }
    core = r.core;
  }
  let added: BuildOutcome["added"] = [];
  if (overlays.review) {
    const c = compileReviewEdits(core, overlays.review, overlays.addedIds);
    added = c.added;
    const r = applyEdits(core, c.edits);
    if (r.rejected.length > 0) bug("a review edit did not fit the patched core", r.rejected.map((x) => `${JSON.stringify(x.edit)}: ${x.reason}`));
    core = r.core;
  }
  // A clause tagged with an id the built core does not hold (a block a repair re-keyed, a result left
  // out) is handed on to no stage; the symbol referee re-grades the symbol (`referee_symbols.ts` `staleTags`).
  for (const x of core.symbols) {
    if (!x.scoped) continue;
    const live = liveClauses(core, x.scoped);
    if (live.length > 0) x.scoped = live;
    else delete x.scoped;
  }
  core = normalizeCore(core, transcribed);
  const bad = checkCoreInvariants(core);
  if (bad.length > 0) bug("the built core breaks its invariant", bad);
  return { core, descoped, added };
}

// ---------------------------------------------------------------------------------------------
// Id remap (a node's content moved to other nodes)
// ---------------------------------------------------------------------------------------------

/** Everything keyed by node id that must follow a moved node. All fields optional; absent = untouched. */
export interface IdKeyedState {
  paper_errors?: Record<string, unknown>;
  /** Dropped for a moved node: its carrier is reviewed afresh. */
  confirmed?: Record<string, string>;
  findings?: Array<{ node: string }>;
  /** Dropped for a moved node: its drift was about the old node. */
  last_drift?: Record<string, string>;
  /** Revise rounds per drifting node: the carrier keeps the larger count, so a rename never resets the cap. */
  v1_5_rounds_by_node?: Record<string, number>;
  /** Rejected suggestions per node: moved like the revise rounds. */
  suggestion_rejections?: Record<string, number>;
  /** Records that name nodes: each name follows the moved node. */
  rejected_rewinds?: Array<{ node: string }>;
  fixer_rejections?: Array<{ node: string }>;
  split_requests?: string[];
  weakening_repair?: { items: Array<{ node: string }>; decisions?: Record<string, unknown> } | null;
  cross_stage_rewind?: { target?: string; nodes?: string[]; targets?: Array<{ node?: string; users?: string[] }> };
}

/** The repair fields of a patch or a suggested repair that hold node ids (`remapNodeIds`). */
interface RepairIdFields {
  drops?: string[];
  adds?: string[];
  supersedes?: string[];
  consequence_of?: string[] | null;
  corollaries?: Array<{ adds?: string[] }>;
}

/**
 * Statement X's content now stands on node `moves[X]` (a V1 restructuring removed or renamed X —
 * `orphan_records.ts`). Every name of X follows it: the patch, `unfixable` entry, owner reading,
 * error-ledger entry, finding, key-result mark and ruled-out / rejection / receipt entries on X (an
 * error-ledger entry the carrier already has is kept), and X among the ids a repair lists (its
 * hypotheses, the repairs it follows, its blocks' hypotheses); X's revise-round and
 * suggestion-rejection counts move to it (the larger count kept), and X's confirmation and
 * last-drift entry are dropped. Pure on the file; mutates `state` in place (it is `state.verify`).
 */
export function remapNodeIds<F extends PatchFileLike>(moves: Record<string, string>, file: F | null, state: IdKeyedState): F | null {
  const to = (id: string): string => moves[id] ?? id;
  const ids = (xs: readonly string[] | null | undefined): string[] | undefined => (xs ? [...new Set(xs.map(to))] : undefined);
  const repair = <R extends RepairIdFields>(r: R): R => ({
    ...r,
    ...(r.drops ? { drops: ids(r.drops) } : {}),
    ...(r.adds ? { adds: ids(r.adds) } : {}),
    ...(r.supersedes ? { supersedes: ids(r.supersedes) } : {}),
    ...(r.consequence_of ? { consequence_of: ids(r.consequence_of) } : {}),
    ...(r.corollaries ? { corollaries: r.corollaries.map((c) => ({ ...c, ...(c.adds ? { adds: ids(c.adds) } : {}) })) } : {}),
  });
  if (state.paper_errors) {
    const next: Record<string, unknown> = {};
    // Two entries meeting on one node: the carrier's wins — but a witnessed error always over an
    // ambiguity (`undetermined`), as in the ledger itself.
    const open = (e: unknown): boolean => (e as { undetermined?: boolean } | undefined)?.undetermined === true;
    for (const [id, e] of Object.entries(state.paper_errors)) {
      const k = to(id);
      if (!(k in next) || (open(next[k]) !== open(e) ? open(next[k]) : !moves[id])) next[k] = e;
    }
    state.paper_errors = next;
  }
  if (state.findings) state.findings = state.findings.map((f) => ({ ...f, node: to(f.node) }));
  if (state.rejected_rewinds) state.rejected_rewinds = state.rejected_rewinds.map((r) => ({ ...r, node: to(r.node) }));
  if (state.fixer_rejections) state.fixer_rejections = state.fixer_rejections.map((r) => ({ ...r, node: to(r.node) }));
  if (state.split_requests) state.split_requests = [...new Set(state.split_requests.map(to))];
  if (state.weakening_repair) {
    const w = state.weakening_repair;
    state.weakening_repair = {
      ...w,
      items: w.items.map((i) => ({ ...i, node: to(i.node) })),
      ...(w.decisions ? { decisions: Object.fromEntries(Object.entries(w.decisions).map(([n, d]) => [to(n), d])) } : {}),
    };
  }
  if (state.cross_stage_rewind) {
    const r = state.cross_stage_rewind;
    state.cross_stage_rewind = {
      ...r,
      ...(r.target ? { target: to(r.target) } : {}),
      ...(r.nodes ? { nodes: ids(r.nodes) } : {}),
      ...(r.targets ? { targets: r.targets.map((t) => ({ ...t, ...(t.node ? { node: to(t.node) } : {}), ...(t.users ? { users: ids(t.users) } : {}) })) } : {}),
    };
  }
  for (const old of Object.keys(moves)) {
    if (state.confirmed) delete state.confirmed[old];
    if (state.last_drift) delete state.last_drift[old];
    for (const counts of [state.v1_5_rounds_by_node, state.suggestion_rejections]) {
      if (!counts || !(old in counts)) continue;
      counts[moves[old]!] = Math.max(counts[moves[old]!] ?? 0, counts[old]!);
      delete counts[old];
    }
  }
  if (!file) return null;
  return {
    ...file,
    key_results: [...new Set(file.key_results.map(to))],
    patches: file.patches.map((p) => ({ ...repair(p), node: to(p.node) })),
    unfixable: file.unfixable.map((u) => {
      const sr = (u as { suggested_repair?: RepairIdFields | null }).suggested_repair;
      const follows = (u as { consequence_of?: string[] }).consequence_of;
      return { ...u, node: to(u.node), ...(sr ? { suggested_repair: repair(sr) } : {}), ...(follows ? { consequence_of: ids(follows) } : {}) };
    }),
    ...(file.owner_readings ? { owner_readings: file.owner_readings.map((r) => ({ ...r, node: to(r.node) })) } : {}),
  };
}
