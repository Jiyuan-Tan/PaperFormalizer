// The toolkit's statement store: every declaration round B has scanned in any paper, with a
// normalized statement and its hash, the filter's verdict, and — once known — the proposal it
// became and the owner's decision. It is the evidence base for CROSS-PAPER RECURRENCE, the primary
// reason to promote a lemma: when round B grounds a candidate, the store is searched for the same
// statement in other papers — an exact normalized-type hash is an identical statement, the same
// shape over each paper's own definitions a pattern match, and a lexical match over the statement
// text and docstring a similar one.
//
// One SHARD per paper since 2026-11-11: `<toolkit>/doc/statements/<slug>.json` (`{version: 1,
// entries}`, the paper's entries). A run reads and writes its own paper's shard alone, and a reader
// of every paper (recurrence) reads the shards one at a time — never the whole store at once. The
// store is still NAMED by its single-file path, `statementStorePath` (`doc/statements.json`), the
// shards living in the directory of that name without `.json` (`statementShardDir`). The single
// file it replaces had grown to 246 MB; every round B loaded and rewrote all of it, GBs of heap a
// process, and runners died of it. `paperformalizer statements split` splits that file once
// (`statements_split.ts`); from then on the shard directory is the store for this code. The single
// file is kept for processes on older code, which go on reading and writing it whole; this code
// never reads it beside shards, and the split, run again, merges what they wrote into the shards
// without losing a proposal or a decision (`--retire-monolith` retires it, later).
//
// A dry run keeps its own store under `runs/<slug>/proposals/dry_run/statements{.json,/}`; the
// toolkit's store is never written by a dry run.
//
// A read-modify-write holds the store's own lock (`statementStoreLockPath`:
// `<toolkit>/.toolkit-statements.lock`, never the promotion lock: a scan recorded waits behind no
// paper's moves and gates) and writes atomically (a new file renamed over the old). One lock for
// every shard: a write is one paper's shard, held for well under a second.
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { mkdir, readdir, readFile, rm } from "node:fs/promises";
import path from "node:path";
import { z } from "zod";
import { conceptScorer, prepareDecl, type IndexedDecl } from "../formalization/reuse_retrieval.js";
import { withStoreLock } from "../shared/build_mutex.js";
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

/** A shard (one paper's entries), and the single-file store before the split (every paper's). */
export const statementStoreSchema = z.object({
  version: z.literal(1),
  entries: z.array(statementEntrySchema).default([]),
});
export type StatementStore = z.infer<typeof statementStoreSchema>;

/** The store's name: its single-file path (the toolkit's `doc/statements.json`, or a dry run's
 *  own). The shards live in `statementShardDir` of it. */
export function statementStorePath(cfg: ToolkitConfig, slug: string, dryRun: boolean): string {
  return dryRun ? path.join(proposalsDryRunDir(cfg, slug), "statements.json") : path.join(cfg.toolkitRoot, "doc", "statements.json");
}

/** The directory of the store `file`'s shards: its path without `.json` (`doc/statements/`). */
export function statementShardDir(file: string): string {
  return file.replace(/\.json$/, "");
}

/** Paper `slug`'s shard in the store `file`. */
export function statementShardPath(file: string, slug: string): string {
  if (!slug || slug.startsWith(".") || /[/\\\0]/.test(slug)) throw new Error(`not a paper slug for a statement shard: ${JSON.stringify(slug)}`);
  return path.join(statementShardDir(file), `${slug}.json`);
}

// compat 2026-11-11: remove after ≤2 days (once every toolkit's store is split) — the single-file
// layout: a store whose single file exists and whose shard directory does not is not split yet, and
// is read and written as before (the whole file). Decided under the store's lock by a writer, so a
// split in between is seen.
/** Whether the store `file` is sharded (else it is the single file of before the split). */
export function statementStoreSharded(file: string): boolean {
  return existsSync(statementShardDir(file)) || !existsSync(file);
}

/** The toolkit store's own lock (gitignore it beside `.toolkit-promote.lock`). */
export const STATEMENT_STORE_LOCK_FILENAME = ".toolkit-statements.lock";

/** The lock guarding a read-modify-write: the toolkit store's own lock
 *  (`STATEMENT_STORE_LOCK_FILENAME`, never the promotion lock: a scan recorded waits behind no
 *  paper's moves); a lock beside a dry run's private store (a dry run never touches the toolkit). */
export function statementStoreLockPath(cfg: ToolkitConfig, slug: string, dryRun: boolean): string {
  return dryRun ? `${statementStorePath(cfg, slug, true)}.lock` : path.join(cfg.toolkitRoot, STATEMENT_STORE_LOCK_FILENAME);
}

function parseStatementStore(text: string, file: string): StatementStore {
  const parsed = statementStoreSchema.safeParse(JSON.parse(text));
  if (!parsed.success) throw new Error(`invalid statement store ${file}: ${parsed.error.issues.map((i) => `${i.path.join(".")}: ${i.message}`).join("; ")}`);
  return parsed.data;
}

/** Paper `slug`'s entries in the sharded store `file` (none when it has no shard). */
export async function loadShard(file: string, slug: string): Promise<StatementEntry[]> {
  const shard = statementShardPath(file, slug);
  return existsSync(shard) ? parseStatementStore(await readFile(shard, "utf8"), shard).entries : [];
}

/** The papers with a shard in the store `file`, by slug. */
export async function shardSlugs(file: string): Promise<string[]> {
  const names = await readdir(statementShardDir(file)).catch(() => [] as string[]);
  return names.filter((f) => f.endsWith(".json") && !f.startsWith(".")).map((f) => f.slice(0, -".json".length)).sort();
}

/** Every shard of the store `file`, one at a time (by slug): one paper's entries held at once. */
export async function* eachShard(file: string): AsyncGenerator<{ slug: string; entries: StatementEntry[] }> {
  for (const slug of await shardSlugs(file)) {
    const shard = statementShardPath(file, slug);
    const text = await readFile(shard, "utf8").catch(() => null); // removed meanwhile
    if (text !== null) yield { slug, entries: parseStatementStore(text, shard).entries };
  }
}

const readSingleFile = async (file: string): Promise<StatementStore> =>
  (existsSync(file) ? parseStatementStore(await readFile(file, "utf8"), file) : { version: 1, entries: [] });

/** The whole store `file`: every paper's entries at once (the single file, or every shard; never
 *  read by round B). */
export async function loadStatementStore(file: string): Promise<StatementStore> {
  if (!statementStoreSharded(file)) return readSingleFile(file); // compat 2026-11-11: remove after ≤2 days
  const entries: StatementEntry[] = [];
  for await (const s of eachShard(file)) entries.push(...s.entries);
  return { version: 1, entries };
}

async function withStore<T>(file: string, lockPath: string | undefined, action: () => Promise<T>): Promise<T> {
  await mkdir(path.dirname(file), { recursive: true });
  const lock = lockPath ?? `${file}.lock`;
  await mkdir(path.dirname(lock), { recursive: true });
  return withStoreLock(lock, action);
}

/** Read paper `slug`'s entries, apply `fn`, write them back atomically — its shard alone — under
 *  `lockPath` (default: a lock beside the store), so the entries `fn` edits are never stale. */
async function updatePaper<T>(file: string, slug: string, lockPath: string | undefined, fn: (entries: StatementEntry[]) => { entries: StatementEntry[]; result: T }): Promise<T> {
  return withStore(file, lockPath, async () => {
    if (!statementStoreSharded(file)) { // compat 2026-11-11: remove after ≤2 days — the single file, whole
      const store = await readSingleFile(file);
      const { entries, result } = fn(store.entries.filter((e) => e.slug === slug));
      await writeJsonAtomic(file, { version: 1, entries: [...store.entries.filter((e) => e.slug !== slug), ...entries] } satisfies StatementStore);
      return result;
    }
    const { entries, result } = fn(await loadShard(file, slug));
    await writeJsonAtomic(statementShardPath(file, slug), { version: 1, entries } satisfies StatementStore);
    return result;
  });
}

// compat 2026-11-11: remove after ≤2 days — the whole-store update of before the shards (nothing
// calls it now): every paper's entries loaded, `fn` applied, each paper's shard whose entries changed
// written back (a paper no entry names any more: its shard removed).
/** Read the whole store, apply `fn`, write it back atomically, under `lockPath` (default: a lock
 *  beside the store). `fn` must build its result from the store it is given alone. */
export async function updateStatementStore<T>(file: string, lockPath: string | undefined, fn: (store: StatementStore) => { store: StatementStore; result: T }): Promise<T> {
  return withStore(file, lockPath, async () => {
    if (!statementStoreSharded(file)) {
      const { store, result } = fn(await readSingleFile(file));
      await writeJsonAtomic(file, store);
      return result;
    }
    const before = new Map<string, string>();
    const all: StatementEntry[] = [];
    for await (const s of eachShard(file)) { before.set(s.slug, JSON.stringify(s.entries)); all.push(...s.entries); }
    const { store, result } = fn({ version: 1, entries: all });
    const after = new Map<string, StatementEntry[]>();
    for (const e of store.entries) after.set(e.slug, [...(after.get(e.slug) ?? []), e]);
    for (const [slug, entries] of after) {
      if (before.get(slug) !== JSON.stringify(entries)) await writeJsonAtomic(statementShardPath(file, slug), { version: 1, entries } satisfies StatementStore);
    }
    for (const slug of before.keys()) if (!after.has(slug)) await rm(statementShardPath(file, slug), { force: true });
    return result;
  });
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

/** Replace `slug`'s entries (its shard of the store `file`) with one per scanned declaration (a
 *  re-scan supersedes the last). */
export async function recordScan(file: string, slug: string, scan: CandidateScan, filtered: Pick<CandidatesFile, "candidates" | "movable" | "rejected">, now: string, lockPath?: string): Promise<StatementEntry[]> {
  return updatePaper(file, slug, lockPath, (entries) => {
    const cands = new Set(filtered.candidates.map((c) => c.name));
    const movable = new Set(filtered.movable);
    const reasons = new Map(filtered.rejected.map((r) => [r.name, r.reasons] as const));
    const prior = new Map(entries.filter((e) => e.slug === slug).map((e) => [e.name, e] as const));
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
    return { entries: mine, result: mine };
  });
}

/** Record which declaration became which proposal (round B, proposed items only). */
export async function recordProposals(file: string, slug: string, proposals: readonly Proposal[], lockPath?: string): Promise<void> {
  const byRef = new Map(proposals.filter((p) => p.verdict === "propose").map((p) => [p.source.ref, p.id] as const));
  await updatePaper(file, slug, lockPath, (entries) => {
    for (const e of entries) if (e.slug === slug && byRef.has(e.name)) e.proposal_id = byRef.get(e.name)!;
    return { entries, result: undefined };
  });
}

/** Record the owner's decisions against the proposals' declarations. */
export async function recordDecisions(file: string, slug: string, decisions: ReadonlyMap<string, DecisionKind>, lockPath?: string): Promise<void> {
  await updatePaper(file, slug, lockPath, (entries) => {
    for (const e of entries) if (e.slug === slug && e.proposal_id && decisions.has(e.proposal_id)) e.decision = decisions.get(e.proposal_id)!;
    return { entries, result: undefined };
  });
}

// ─── recurrence ────────────────────────────────────────────────────────────

const SIMILAR_TOP_K = 3;

/**
 * Recurrence of `slug`'s declarations in OTHER papers of the store: an identical normalized
 * statement (hash match); the same PATTERN under each paper's own definitions (`statementPattern`:
 * bound variables renamed, paper constants erased); then up to three lexically similar ones (the
 * retrieval engine's concept score of each other paper's entry, statement text + docstring, best
 * first). A pattern or similar match counts as recurrence only once the curator confirms it in words
 * (`recurrence_confirmed`).
 *
 * `store`: the store's path (`statementStorePath`), whose shards are read one at a time — memory
 * holds one paper's entries and the matches; matches are listed by paper (slug), each paper's in its
 * order — or, as before the shards, the store's entries in memory (listed in their order).
 * `workDir`: unused (it held a temporary index of every other paper's entries; kept for callers).
 */
export async function findRecurrence(
  store: Pick<StatementStore, "entries"> | string,
  slug: string,
  targets: ReadonlyArray<{ name: string; type: string; doc: string | null }>,
  _workDir?: string,
  papersLib = "Papers",
): Promise<Map<string, Recurrence[]>> {
  const queries = targets.map((t) => {
    const normalized = normalizeType(t.type);
    const leaf = t.name.split(".").pop() ?? t.name;
    return {
      name: t.name, hash: typeHash(normalized), pattern: statementPattern(normalized, papersLib),
      score: conceptScorer({ mode: "concept", title: `${leaf.replace(/[_.]/g, " ")} ${firstParagraph(t.doc)}`, bodyTerms: [normalized] }),
      identical: [] as Recurrence[], samePattern: [] as Recurrence[],
      // the best similar ones so far, best first (score, then name: the engine's order)
      similar: [] as Array<{ key: string; score: number; slug: string; name: string }>,
    };
  });
  const before = (a: { key: string; score: number }, b: { key: string; score: number }) => (a.score !== b.score ? a.score > b.score : a.key.localeCompare(b.key) < 0);
  const visit = (e: StatementEntry) => {
    if (e.slug === slug) return;
    const pattern = statementPattern(e.type_normalized, papersLib);
    const key = `${e.slug}::${e.name}`;
    let ix: IndexedDecl | null = null;
    for (const q of queries) {
      if (e.type_sha256 === q.hash) { q.identical.push({ slug: e.slug, name: e.name, kind: "identical" }); continue; }
      if (q.pattern !== null && pattern === q.pattern) { q.samePattern.push({ slug: e.slug, name: e.name, kind: "pattern" }); continue; }
      // as the engine indexes an entry (the name a key of slug and name: both are searched)
      ix ??= prepareDecl({
        name: key, kind: e.kind, module: e.module, file: "", line: 0, statement: e.type_normalized,
        doc: e.doc_first_paragraph || null, refs: [], proofRefs: [], axioms: [], usesSorry: false,
      }, "papers");
      const score = q.score(ix);
      if (score <= 0) continue;
      const hit = { key, score, slug: e.slug, name: e.name };
      if (q.similar.length === SIMILAR_TOP_K && !before(hit, q.similar[SIMILAR_TOP_K - 1]!)) continue;
      let at = q.similar.length;
      while (at > 0 && before(hit, q.similar[at - 1]!)) at -= 1;
      q.similar.splice(at, 0, hit);
      if (q.similar.length > SIMILAR_TOP_K) q.similar.pop();
    }
  };
  if (typeof store !== "string") for (const e of store.entries) visit(e);
  else if (!statementStoreSharded(store)) for (const e of (await readSingleFile(store)).entries) visit(e); // compat 2026-11-11: remove after ≤2 days
  else for await (const shard of eachShard(store)) if (shard.slug !== slug) for (const e of shard.entries) visit(e);
  return new Map(queries.map((q) => [q.name, [
    ...q.identical, ...q.samePattern,
    ...q.similar.map((h): Recurrence => ({ slug: h.slug, name: h.name, kind: "similar", score: Math.round(h.score * 100) / 100 })),
  ]] as const));
}

/** For each candidate: entries of other papers it recurs with that the owner deferred, read from
 *  the store `file` — of a sharded store, the shards of the papers it recurs in alone, one at a
 *  time (a deferred entry's key kept, nothing else). (`deferredMatches` in `round_b.ts`: the same
 *  over entries in memory.) */
export async function deferredMatchesIn(
  file: string,
  recurrence: ReadonlyMap<string, readonly Recurrence[] | undefined>,
): Promise<Map<string, Array<{ slug: string; proposal_id: string }>>> {
  const deferred = new Map<string, { slug: string; proposal_id: string }>();
  const keep = (e: StatementEntry) => { if (e.decision === "defer" && e.proposal_id) deferred.set(`${e.slug}::${e.name}`, { slug: e.slug, proposal_id: e.proposal_id }); };
  if (!statementStoreSharded(file)) (await readSingleFile(file)).entries.forEach(keep); // compat 2026-11-11: remove after ≤2 days
  else {
    const papers = new Set([...recurrence.values()].flatMap((recs) => (recs ?? []).map((r) => r.slug)));
    for (const s of [...papers].sort()) (await loadShard(file, s)).forEach(keep);
  }
  const out = new Map<string, Array<{ slug: string; proposal_id: string }>>();
  for (const [name, recs] of recurrence) {
    const hits = (recs ?? []).flatMap((r) => { const e = deferred.get(`${r.slug}::${r.name}`); return e ? [e] : []; });
    if (hits.length) out.set(name, hits);
  }
  return out;
}

/** Where `findRecurrence`'s temporary index lived for a run (no index is written now). */
export function recurrenceWorkDir(cfg: ToolkitConfig, slug: string): string {
  return path.join(proposalsRunDir(cfg, slug), "tmp");
}
