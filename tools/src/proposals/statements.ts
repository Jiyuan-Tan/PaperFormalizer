// The toolkit's statement store, `<toolkit>/doc/statements.json`: every declaration round B has
// scanned in any paper, with a normalized statement and its hash, the filter's verdict, and — once
// known — the proposal it became and the owner's decision. It is the evidence base for
// CROSS-PAPER RECURRENCE, the primary reason to promote a lemma: when round B grounds a candidate,
// the store is searched for the same statement in other papers — an exact normalized-type hash is
// an identical statement, the same shape over each paper's own definitions a pattern match, and a
// lexical match over the statement text and docstring a similar one.
//
// A dry run keeps its own store under `runs/<slug>/proposals/dry_run/statements.json`; the
// toolkit's store is never written by a dry run.
//
// The toolkit's store is shared by every run, so each read-modify-write re-reads it under the
// promotion lock (`statementStoreLockPath`) and writes atomically: two runs finishing round B at
// once cannot clobber each other's entries.
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { mkdir, readdir, readFile, rm, writeFile } from "node:fs/promises";
import path from "node:path";
import { z } from "zod";
import { createRetrieval } from "../formalization/reuse_retrieval.js";
import { indexSourceFromPath } from "../library/sources.js";
import { withPromotionLock } from "../shared/build_mutex.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import type { CandidateScan, CandidatesFile } from "./candidate_scan.js";
import { proposalsDryRunDir, proposalsRunDir, type DecisionKind, type Proposal, type Recurrence } from "./schema.js";

export const statementEntrySchema = z.object({
  slug: z.string().min(1),
  name: z.string().min(1),
  module: z.string(),
  kind: z.string(),
  type_normalized: z.string(),
  type_sha256: z.string(),
  doc_first_paragraph: z.string(),
  /** `candidate`: proposable theorem; `moves_with`: movable only with a candidate; `rejected`. */
  verdict: z.enum(["candidate", "moves_with", "rejected"]),
  reasons: z.array(z.string()).default([]),
  proposal_id: z.string().nullable().default(null),
  decision: z.string().nullable().default(null),
  recorded_at: z.string(),
}).passthrough();
export type StatementEntry = z.infer<typeof statementEntrySchema>;

export const statementStoreSchema = z.object({
  version: z.literal(1),
  entries: z.array(statementEntrySchema).default([]),
});
export type StatementStore = z.infer<typeof statementStoreSchema>;

export function statementStorePath(cfg: ToolkitConfig, slug: string, dryRun: boolean): string {
  return dryRun ? path.join(proposalsDryRunDir(cfg, slug), "statements.json") : path.join(cfg.toolkitRoot, "doc", "statements.json");
}

/** The lock guarding a store's read-modify-write: the toolkit's promotion lock for the toolkit's
 *  store; a lock beside a dry run's private store (a dry run never touches the toolkit). */
export function statementStoreLockPath(cfg: ToolkitConfig, slug: string, dryRun: boolean): string {
  return dryRun ? `${statementStorePath(cfg, slug, true)}.lock` : cfg.lockPath;
}

export async function loadStatementStore(file: string): Promise<StatementStore> {
  if (!existsSync(file)) return { version: 1, entries: [] };
  const parsed = statementStoreSchema.safeParse(JSON.parse(await readFile(file, "utf8")));
  if (!parsed.success) throw new Error(`invalid statement store ${file}: ${parsed.error.issues.map((i) => `${i.path.join(".")}: ${i.message}`).join("; ")}`);
  return parsed.data;
}

/** Read the store, apply `fn`, write it back atomically — all under `lockPath` (default: a lock
 *  beside the file), so the snapshot `fn` edits is never stale. */
async function updateStatementStore<T>(file: string, lockPath: string | undefined, fn: (store: StatementStore) => { store: StatementStore; result: T }): Promise<T> {
  await mkdir(path.dirname(file), { recursive: true });
  const lock = lockPath ?? `${file}.lock`;
  await mkdir(path.dirname(lock), { recursive: true });
  return withPromotionLock(path.dirname(lock), async () => {
    const { store, result } = fn(await loadStatementStore(file));
    await writeJsonAtomic(file, store);
    return result;
  }, lock);
}

// ─── normalization ─────────────────────────────────────────────────────────

const IDENT_CHAR = /[\p{L}\p{N}_'!?✝]/u;
const IDENT = /^[\p{L}_][\p{L}\p{N}_'!?✝]*$/u;
const OPEN: Record<string, string> = { "(": ")", "{": "}", "[": "]", "⦃": "⦄" };
const BINDER_KW = /(?<![\p{L}\p{N}_'!?.])(?:∀|∃!|∃|fun|λ|Π)(?=[\s({\[⦃])/gu;

/** Names bound by the binder list starting at `i` (just after a binder keyword). */
function bindersAt(t: string, i: number): string[] {
  const names: string[] = [];
  let j = i;
  for (;;) {
    while (j < t.length && /\s/.test(t[j]!)) j += 1;
    const ch = t[j];
    if (ch !== undefined && OPEN[ch]) {
      let depth = 0;
      let k = j;
      for (; k < t.length; k += 1) {
        if (OPEN[t[k]!]) depth += 1;
        else if (Object.values(OPEN).includes(t[k]!)) { depth -= 1; if (depth === 0) break; }
      }
      const inner = t.slice(j + 1, k);
      // Names precede the group's first top-level `:` (a group without one binds all its tokens).
      let d = 0;
      let colon = -1;
      for (let q = 0; q < inner.length; q += 1) {
        if (OPEN[inner[q]!]) d += 1;
        else if (Object.values(OPEN).includes(inner[q]!)) d -= 1;
        else if (inner[q] === ":" && d === 0 && inner[q + 1] !== "=") { colon = q; break; }
      }
      names.push(...(colon >= 0 ? inner.slice(0, colon) : inner).trim().split(/\s+/));
      j = k + 1;
      continue;
    }
    if (ch !== undefined && IDENT_CHAR.test(ch)) {
      let k = j;
      while (k < t.length && IDENT_CHAR.test(t[k]!)) k += 1;
      names.push(t.slice(j, k));
      j = k;
      continue;
    }
    return names;
  }
}

/**
 * A pretty-printed Lean type in a form that compares across papers: whitespace collapsed,
 * universe parameters renamed (`Type u_1`, `Sort v`, `.{u}` → `?u`), and bound variables renamed
 * in order of binding (`∀ (n : ℕ), …` and `∀ (k : ℕ), …` normalize alike; hygienic `x✝` names too).
 * Textual, over the exe's pretty-printer output (which prints full names with no open namespaces).
 */
export function normalizeType(type: string): string {
  let t = type.replace(/\s+/g, " ").trim();
  t = t.replace(/\b(Type|Sort)\s+(?:[a-z](?:_\d+)?|u_\d+|\(max [^)]*\))/g, "$1 ?u").replace(/\.\{[^}]*\}/g, ".{?u}");
  const bound: string[] = [];
  for (const m of t.matchAll(BINDER_KW)) {
    for (const n of bindersAt(t, m.index! + m[0].length)) if (IDENT.test(n) && n !== "_" && !bound.includes(n)) bound.push(n);
  }
  bound.forEach((n, i) => {
    const esc = n.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    t = t.replace(new RegExp(`(?<![\\p{L}\\p{N}_'!?.✝])${esc}(?![\\p{L}\\p{N}_'!?✝])`, "gu"), `x${i + 1}`);
  });
  return t;
}

export function typeHash(normalized: string): string {
  return createHash("sha256").update(normalized, "utf8").digest("hex");
}

/**
 * The PATTERN of a normalized statement: every constant of a paper's own library (`<papersLib>.*`,
 * printed by full name) erased to `⋆`, so the same shape of hypotheses and conclusion over two
 * papers' local definitions compares alike. Null when too little remains to mean anything (fewer
 * than two named constants of the base libraries or the toolkit): such a shape matches too much.
 */
export function statementPattern(normalized: string, papersLib = "Papers"): string | null {
  const esc = papersLib.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const erased = normalized.replace(new RegExp(`(?<![\\p{L}\\p{N}_'!?.])${esc}\\.[\\p{L}\\p{N}_'!?.✝]+`, "gu"), "⋆");
  const named = new Set(erased.match(/[\p{L}_][\p{L}\p{N}_'!?]*(?:\.[\p{L}\p{N}_'!?]+)+/gu) ?? []);
  return named.size >= 2 ? erased : null;
}

function firstParagraph(doc: string | null): string {
  return (doc ?? "").split(/\n\s*\n/)[0]!.replace(/\s+/g, " ").trim();
}

// ─── recording ─────────────────────────────────────────────────────────────

/** Replace `slug`'s entries with one per scanned declaration (a re-scan supersedes the last). */
export async function recordScan(file: string, slug: string, scan: CandidateScan, filtered: Pick<CandidatesFile, "candidates" | "movable" | "rejected">, now: string, lockPath?: string): Promise<StatementEntry[]> {
  return updateStatementStore(file, lockPath, (store) => {
  const cands = new Set(filtered.candidates.map((c) => c.name));
  const movable = new Set(filtered.movable);
  const reasons = new Map(filtered.rejected.map((r) => [r.name, r.reasons] as const));
  const prior = new Map(store.entries.filter((e) => e.slug === slug).map((e) => [e.name, e] as const));
  const mine: StatementEntry[] = scan.declarations.map((d) => {
    const normalized = normalizeType(d.type);
    return {
      slug, name: d.name, module: d.module, kind: d.kind, type_normalized: normalized, type_sha256: typeHash(normalized),
      doc_first_paragraph: firstParagraph(d.doc),
      verdict: cands.has(d.name) ? "candidate" : movable.has(d.name) ? "moves_with" : "rejected",
      reasons: reasons.get(d.name) ?? [],
      proposal_id: prior.get(d.name)?.proposal_id ?? null,
      decision: prior.get(d.name)?.decision ?? null,
      recorded_at: now,
    };
  });
  return { store: { version: 1, entries: [...store.entries.filter((e) => e.slug !== slug), ...mine] }, result: mine };
  });
}

/** Record which declaration became which proposal (round B, proposed items only). */
export async function recordProposals(file: string, slug: string, proposals: readonly Proposal[], lockPath?: string): Promise<void> {
  const byRef = new Map(proposals.filter((p) => p.verdict === "propose").map((p) => [p.source.ref, p.id] as const));
  await updateStatementStore(file, lockPath, (store) => {
    for (const e of store.entries) if (e.slug === slug && byRef.has(e.name)) e.proposal_id = byRef.get(e.name)!;
    return { store, result: undefined };
  });
}

/** Record the owner's decisions against the proposals' declarations. */
export async function recordDecisions(file: string, slug: string, decisions: ReadonlyMap<string, DecisionKind>, lockPath?: string): Promise<void> {
  await updateStatementStore(file, lockPath, (store) => {
    for (const e of store.entries) if (e.slug === slug && e.proposal_id && decisions.has(e.proposal_id)) e.decision = decisions.get(e.proposal_id)!;
    return { store, result: undefined };
  });
}

// ─── recurrence ────────────────────────────────────────────────────────────

const SIMILAR_TOP_K = 3;

/**
 * Recurrence of `slug`'s declarations in OTHER papers of the store: an identical normalized
 * statement (hash match); the same PATTERN under each paper's own definitions (`statementPattern`:
 * bound variables renamed, paper constants erased); then up to three lexically similar ones (the
 * retrieval engine's concept search over a temporary index of the other papers' entries, statement
 * text + docstring). A pattern or similar match counts as recurrence only once the curator confirms
 * it in words (`recurrence_confirmed`). `workDir` holds the temporary index (content-named, so the
 * engine's cache stays correct).
 */
export async function findRecurrence(
  store: StatementStore,
  slug: string,
  targets: ReadonlyArray<{ name: string; type: string; doc: string | null }>,
  workDir: string,
  papersLib = "Papers",
): Promise<Map<string, Recurrence[]>> {
  const others = store.entries.filter((e) => e.slug !== slug);
  const out = new Map<string, Recurrence[]>(targets.map((t) => [t.name, []]));
  if (others.length === 0) return out;
  const key = (e: StatementEntry) => `${e.slug}::${e.name}`;
  const index = {
    commit: "statements", toolchain: "n/a", modules: {},
    entries: others.map((e) => ({
      name: key(e), kind: e.kind === "theorem" ? "theorem" : e.kind, module: e.module, file: "", line: 0,
      statement: e.type_normalized, doc: e.doc_first_paragraph || null, refs: [], proofRefs: [], axioms: [], usesSorry: false,
    })),
  };
  const text = JSON.stringify(index);
  const idxFile = path.join(workDir, `statements_index.${createHash("sha256").update(text).digest("hex").slice(0, 12)}.json`);
  await mkdir(workDir, { recursive: true });
  // one index at a time: the earlier runs' (other content, other names) are dropped
  for (const stale of (await readdir(workDir)).filter((f) => /^statements_index\.[0-9a-f]+\.json$/.test(f) && f !== path.basename(idxFile))) {
    await rm(path.join(workDir, stale), { force: true });
  }
  if (!existsSync(idxFile)) await writeFile(idxFile, text, "utf8");
  const retrieval = createRetrieval(indexSourceFromPath(idxFile, { library: "papers" }));
  const byKey = new Map(others.map((e) => [key(e), e] as const));
  const patternOf = new Map(others.map((e) => [e, statementPattern(e.type_normalized, papersLib)] as const));
  for (const t of targets) {
    const hash = typeHash(normalizeType(t.type));
    const identical = others.filter((e) => e.type_sha256 === hash);
    const rec: Recurrence[] = identical.map((e) => ({ slug: e.slug, name: e.name, kind: "identical" as const }));
    const pattern = statementPattern(normalizeType(t.type), papersLib);
    const samePattern = pattern === null ? [] : others.filter((e) => !identical.includes(e) && patternOf.get(e) === pattern);
    rec.push(...samePattern.map((e) => ({ slug: e.slug, name: e.name, kind: "pattern" as const })));
    const leaf = t.name.split(".").pop() ?? t.name;
    const hits = retrieval.search(
      { mode: "concept", title: `${leaf.replace(/[_.]/g, " ")} ${firstParagraph(t.doc)}`, bodyTerms: [normalizeType(t.type)] },
      { topK: SIMILAR_TOP_K + identical.length + samePattern.length },
    );
    for (const h of hits) {
      const e = byKey.get(h.name);
      if (!e || identical.includes(e) || samePattern.includes(e)) continue;
      if (rec.filter((r) => r.kind === "similar").length >= SIMILAR_TOP_K) break;
      rec.push({ slug: e.slug, name: e.name, kind: "similar", score: Math.round(h.score * 100) / 100 });
    }
    out.set(t.name, rec);
  }
  return out;
}

/** Where `findRecurrence`'s temporary index lives for a run. */
export function recurrenceWorkDir(cfg: ToolkitConfig, slug: string): string {
  return path.join(proposalsRunDir(cfg, slug), "tmp");
}
