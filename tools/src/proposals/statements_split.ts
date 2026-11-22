// `paperformalizer statements split`: the single-file statement store (`doc/statements.json`, every
// paper's entries in one file) copied into the store's shards, `doc/statements/<slug>.json`, and —
// run again, daily while older processes may still write the single file — MERGED into them
// (`statements.ts`, header). The file is read as a stream, each entry written to its paper's staged
// copy as it comes: memory holds one entry, a small buffer per paper, then one paper at a time.
//
// Under the store's lock (an older process writing the single file takes it too). Every paper's
// staged copy is read back and checked against the file (count and digest, in order) before any
// shard is written. The single file is KEPT: processes on older code go on reading and writing it
// whole; only `--retire-monolith` renames it `statements.json.bak`, once none is left.
//
// The merge, per paper (`mergePaper`): its entries are those of its newer scan (`recorded_at`; a tie
// keeps the shard's, the newer code's); a proposal or decision is never lost — each entry takes
// `proposal_id` and `decision` from the shard when set there, else from the single file (same
// name). A shard whose merge changes nothing is not rewritten: the merge is idempotent.
import { createHash } from "node:crypto";
import { appendFileSync, createReadStream, existsSync } from "node:fs";
import { mkdir, readFile, rename, rm } from "node:fs/promises";
import path from "node:path";
import { withStoreLock } from "../shared/build_mutex.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import { loadShard, statementEntrySchema, statementShardDir, statementStoreLockPath, statementStorePath, type StatementEntry, type StatementStore } from "./statements.js";

export const STATEMENTS_USAGE =
  "Usage: paperformalizer statements split [--retire-monolith] [--toolkit <path>]\n" +
  "  copy the toolkit's single-file statement store doc/statements.json into one shard per paper, doc/statements/<slug>.json,\n" +
  "  or merge it into them again (safe daily: what older processes wrote to the file since; nothing is lost, an unchanged\n" +
  "  shard is not rewritten). The file stays for processes on older code; --retire-monolith renames it\n" +
  "  doc/statements.json.bak after the merge (once no such process is left).";

/** A string's next quote or backslash. */
const STRING_STOP = /["\\]/g;

/**
 * The entries of a store file `{version, entries: [...]}`, each parsed alone as the file is read;
 * returns the file without its entries (`{version, entries: []}`, parsed). A character scan that
 * tracks strings and nesting: an entry is the text of one top-level object of the `entries` array.
 */
export async function* streamStoreEntries(file: string): AsyncGenerator<unknown, unknown> {
  let skeleton = ""; // the file but the entries' text
  let depth = 0;
  let inStr = false;
  let esc = false;
  let entriesDepth = -1; // the depth inside the `entries` array while it is read, else -1
  let elem: string | null = null; // an entry's text read so far (carried across chunks)
  for await (const chunk of createReadStream(file, { encoding: "utf8", highWaterMark: 1 << 20 }) as AsyncIterable<string>) {
    let start = elem !== null ? 0 : -1;
    for (let i = 0; i < chunk.length; i += 1) {
      const c = chunk.charCodeAt(i);
      if (inStr) {
        if (esc) { esc = false; if (start < 0) skeleton += chunk[i]; continue; }
        // to the string's next quote or backslash at once (most of the file is string)
        STRING_STOP.lastIndex = i;
        const j = STRING_STOP.exec(chunk)?.index ?? chunk.length;
        if (start < 0) skeleton += chunk.slice(i, j + 1);
        if (j < chunk.length) { if (chunk.charCodeAt(j) === 0x5c) esc = true; else inStr = false; }
        i = j;
        continue;
      }
      if (c === 0x22) {
        inStr = true;
        if (start < 0) {
          if (entriesDepth >= 0) throw new Error(`${file}: an entry of \`entries\` is not an object`);
          skeleton += '"';
        }
        continue;
      }
      if (c === 0x7b || c === 0x5b) { // { [
        depth += 1;
        if (start >= 0) continue;
        if (entriesDepth >= 0) {
          if (c !== 0x7b) throw new Error(`${file}: an entry of \`entries\` is not an object`);
          start = i;
          elem = "";
          continue;
        }
        if (c === 0x5b && depth === 2 && /"entries"\s*:\s*$/.test(skeleton)) {
          skeleton += "[]";
          entriesDepth = depth;
          continue;
        }
        skeleton += chunk[i];
        continue;
      }
      if (c === 0x7d || c === 0x5d) { // } ]
        depth -= 1;
        if (start >= 0) {
          if (depth === entriesDepth) {
            const text = elem + chunk.slice(start, i + 1);
            elem = null;
            start = -1;
            yield JSON.parse(text);
          }
          continue;
        }
        if (entriesDepth >= 0 && depth === entriesDepth - 1) { entriesDepth = -1; continue; }
        skeleton += chunk[i];
        continue;
      }
      if (start >= 0) continue;
      if (entriesDepth >= 0) {
        if (c === 0x2c || c === 0x20 || c === 0x0a || c === 0x0d || c === 0x09) continue;
        throw new Error(`${file}: an entry of \`entries\` is not an object`);
      }
      skeleton += chunk[i];
    }
    if (start >= 0) elem += chunk.slice(start);
  }
  if (depth !== 0 || inStr || elem !== null) throw new Error(`${file}: the file ends inside a value (truncated?)`);
  return JSON.parse(skeleton);
}

/** An entry as `writeJsonAtomic` writes it inside a shard (`{version, entries}`, two-space indent). */
const shardEntryText = (e: unknown) => `    ${JSON.stringify(e, null, 2).replace(/\n/g, "\n    ")}`;
const SHARD_HEAD = '{\n  "version": 1,\n  "entries": [\n';
const SHARD_TAIL = "\n  ]\n}";
/** Flush a paper's buffered shard text at this size. */
const FLUSH_CHARS = 1 << 18;

interface PaperSplit { count: number; digest: ReturnType<typeof createHash>; buf: string }

export interface SplitResult { entries: number; papers: number; written: string[]; unchanged: string[]; backup: string | null }

const latestOf = (entries: readonly StatementEntry[]) => entries.reduce((m, e) => (e.recorded_at > m ? e.recorded_at : m), "");

/** Paper `slug`'s entries merged from its shard's (`shard`, null: none) and the single file's
 *  (`mono`): see the header. */
export function mergePaper(shard: readonly StatementEntry[] | null, mono: readonly StatementEntry[]): StatementEntry[] {
  if (shard === null) return [...mono];
  const shardNewer = latestOf(shard) >= latestOf(mono);
  const [base, other] = shardNewer ? [shard, mono] : [mono, shard];
  const otherByName = new Map(other.map((e) => [e.name, e] as const));
  const shardByName = new Map(shard.map((e) => [e.name, e] as const));
  const monoByName = new Map(mono.map((e) => [e.name, e] as const));
  return base.map((e) => {
    if (!otherByName.has(e.name)) return e;
    const s = shardByName.get(e.name);
    const m = monoByName.get(e.name);
    return { ...e, proposal_id: s?.proposal_id ?? m?.proposal_id ?? null, decision: s?.decision ?? m?.decision ?? null };
  });
}

/** Paper `slug`'s shard file in the directory `dir` (a slug that names no file is refused). */
const shardIn = (dir: string, slug: string) => {
  if (!slug || slug.startsWith(".") || /[/\\\0]/.test(slug)) throw new Error(`not a paper slug for a statement shard: ${JSON.stringify(slug)}`);
  return path.join(dir, `${slug}.json`);
};

const digestOf = (entries: readonly unknown[]) => {
  const h = createHash("sha256");
  for (const e of entries) h.update(`${JSON.stringify(e)}\n`);
  return h.digest("hex");
};

/**
 * Copy or merge the single-file store `legacyFile` (`statementStorePath`) into its shards
 * (`statementShardDir`; see the header), under `lockPath`; `retire`: then rename the file `.bak`.
 * Throws, writing no shard and keeping the file, when an entry is invalid or a staged copy does not
 * read back as the file's entries.
 */
export async function splitStatementStore(legacyFile: string, lockPath: string, log: (m: string) => void = () => {}, opts: { retire?: boolean } = {}): Promise<SplitResult> {
  const storeDir = statementShardDir(legacyFile);
  await mkdir(path.dirname(lockPath), { recursive: true });
  return withStoreLock(lockPath, async () => {
    if (!existsSync(legacyFile)) throw new Error(`no single-file statement store at ${legacyFile}: nothing to split`);
    const staging = `${storeDir}.split-tmp`;
    await rm(staging, { recursive: true, force: true });
    await mkdir(staging, { recursive: true });
    const papers = new Map<string, PaperSplit>();
    const flush = (slug: string, p: PaperSplit) => { if (p.buf) { appendFileSync(shardIn(staging, slug), p.buf); p.buf = ""; } };
    let total = 0;
    const entries = streamStoreEntries(legacyFile);
    let next = await entries.next();
    for (; !next.done; next = await entries.next()) {
      const raw = next.value;
      const ok = statementEntrySchema.safeParse(raw);
      if (!ok.success) throw new Error(`${legacyFile}: entry ${total + 1} is invalid: ${ok.error.issues.map((i) => `${i.path.join(".")}: ${i.message}`).join("; ")}`);
      const slug = ok.data.slug;
      shardIn(staging, slug); // a slug that names a file
      let p = papers.get(slug);
      if (!p) { p = { count: 0, digest: createHash("sha256"), buf: SHARD_HEAD }; papers.set(slug, p); }
      p.buf += `${p.count ? ",\n" : ""}${shardEntryText(raw)}`;
      p.count += 1;
      p.digest.update(`${JSON.stringify(raw)}\n`);
      total += 1;
      if (p.buf.length >= FLUSH_CHARS) flush(slug, p);
    }
    const top = next.value as { version?: unknown };
    if (top?.version !== 1) throw new Error(`${legacyFile}: version ${JSON.stringify(top?.version)}, not 1`);
    for (const [slug, p] of papers) { p.buf += SHARD_TAIL; flush(slug, p); }

    // every shard read back (one at a time): the file's entries, in order
    const want = new Map([...papers].map(([slug, p]) => [slug, { count: p.count, digest: p.digest.digest("hex") }] as const));
    let readBack = 0;
    for (const [slug, w] of want) {
      const file = shardIn(staging, slug);
      const shard = JSON.parse(await readFile(file, "utf8")) as { version?: unknown; entries?: unknown[] };
      const got = shard.entries ?? [];
      if (shard.version !== 1 || got.length !== w.count || digestOf(got) !== w.digest) {
        throw new Error(`${file}: does not read back as ${legacyFile}'s ${w.count} entries of ${slug} — nothing installed`);
      }
      readBack += got.length;
    }
    if (readBack !== total) throw new Error(`the shards hold ${readBack} entries, ${legacyFile} ${total} — nothing installed`);

    // merged: one paper at a time, a shard written only when its merge changes it
    const written: string[] = [];
    const unchanged: string[] = [];
    if (!existsSync(storeDir)) {
      // the first split: the staged copies are the shards, installed at once (the layout switches in one rename)
      await rename(staging, storeDir);
      written.push(...[...want.keys()].sort());
    }
    for (const slug of existsSync(staging) ? [...want.keys()].sort() : []) {
      const mono = (JSON.parse(await readFile(shardIn(staging, slug), "utf8")) as StatementStore).entries;
      const target = shardIn(storeDir, slug);
      const shard = existsSync(target) ? await loadShard(legacyFile, slug) : null;
      const merged = mergePaper(shard, mono);
      if (shard !== null && JSON.stringify(merged) === JSON.stringify(shard)) { unchanged.push(slug); continue; }
      await writeJsonAtomic(target, { version: 1, entries: merged } satisfies StatementStore);
      written.push(slug);
    }
    await rm(staging, { recursive: true, force: true });
    let backup: string | null = null;
    if (opts.retire) {
      backup = `${legacyFile}.bak`;
      if (existsSync(backup)) backup = `${legacyFile}.bak-${new Date().toISOString().replace(/[:.]/g, "-")}`;
      await rename(legacyFile, backup);
    }
    log(`statements: ${total} entries of ${want.size} paper(s) of ${legacyFile} merged into ${storeDir}/ (each read back and checked): ` +
      `${written.length} shard(s) written, ${unchanged.length} unchanged; ${backup ? `the file is now ${backup}` : "the file is kept (--retire-monolith renames it)"}`);
    return { entries: total, papers: want.size, written, unchanged, backup };
  });
}

export async function runStatementsCli(argv: string[], log: (m: string) => void = (m) => console.log(m)): Promise<void> {
  const i = argv.indexOf("--toolkit");
  const explicit = i >= 0 ? argv[i + 1] ?? null : null;
  const rest = i >= 0 ? [...argv.slice(0, i), ...argv.slice(i + 2)] : argv;
  const retire = rest.includes("--retire-monolith");
  const words = rest.filter((a) => a !== "--retire-monolith");
  if (words.length !== 1 || words[0] !== "split") throw new Error(STATEMENTS_USAGE);
  const { loadToolkitConfig } = await import("../toolkit/config.js");
  const cfg: ToolkitConfig = loadToolkitConfig({ explicit });
  await splitStatementStore(statementStorePath(cfg, "", false), statementStoreLockPath(cfg, "", false), log, { retire });
}
