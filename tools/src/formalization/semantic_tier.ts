import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { execFileSync } from "node:child_process";
import { pythonArgs } from "../shared/python.js";
import type { IndexSource } from "../library/sources.js";

// The semantic tier of ONE index source. Its embedding files sit next to the index and share
// its stem: `<dir>/library_index.json` → `<dir>/library_embeddings.{meta.json,f32}` (plus
// `library_embeddings.<view>.*` extra views); an index not named `*_index.json` uses
// `<stem>_embeddings.*`. Absent files ⇒ the tier is off for that source (no warning).

export interface SemHit { name: string; sim: number; }
export interface SemOpts { k: number; floor: number; exclude: Set<string>; graphProp?: number; }

/** Path prefix of a source's embedding files (see the file header). */
export function embeddingsPrefix(indexPath: string): string {
  const dir = path.dirname(indexPath);
  const stem = path.basename(indexPath).replace(/\.json$/i, "");
  return path.join(dir, stem.endsWith("_index") ? `${stem.slice(0, -"_index".length)}_embeddings` : `${stem}_embeddings`);
}

/** The library package root a source's relative model paths resolve against: the configured
 *  root, else the parent of a `doc/` directory holding the index, else the index directory. */
function sourceRoot(src: IndexSource): string {
  if (src.root) return src.root;
  const dir = path.dirname(src.indexPath);
  return path.basename(dir) === "doc" ? path.dirname(dir) : dir;
}

/** Cheap runtime staleness check (the authoritative content check belongs to the tool that
 *  built the embeddings). Catches added/removed decls and a new index commit. */
export function isEmbeddingsStale(
  meta: { names: string[]; index_commit?: string },
  index: { commit?: string; names: string[] },
): boolean {
  if (meta.index_commit !== index.commit) return true;
  if (meta.names.length !== index.names.length) return true;
  const m = new Set(meta.names);
  return !index.names.every((n) => m.has(n));
}

export class SemanticTier {
  constructor(
    private names: string[],
    private vecs: Float32Array, // row-major, normalized (the base "nl" view)
    private dim: number,
    // Additional row-aligned view matrices (e.g. statement / dependency-graph neighbourhood).
    // A decl's similarity is the MAX cosine over the base view and every extra view, so a
    // view can only ever raise a decl's score — never lower a hit the base view already found.
    private extraViews: Float32Array[] = [],
    // Undirected refs-graph neighbourhood as row indices per decl (Ch4 graph propagation).
    // Empty ⇒ propagation is a no-op regardless of `opts.graphProp`.
    private adjacency: number[][] = [],
  ) {}

  /** Max cosine of decl row `i` over the base view and every extra view (multi-view scoring). */
  private simOf(i: number, q: Float32Array): number {
    const off = i * this.dim;
    let best = 0;
    for (let d = 0; d < this.dim; d++) best += this.vecs[off + d] * q[d];
    for (const view of this.extraViews) {
      let dot = 0;
      for (let d = 0; d < this.dim; d++) dot += view[off + d] * q[d];
      if (dot > best) best = dot;
    }
    return best;
  }

  topK(q: Float32Array, opts: SemOpts): SemHit[] {
    const n = this.names.length;
    const raw = new Float32Array(n);
    for (let i = 0; i < n; i++) raw[i] = this.simOf(i, q);

    // Ch4 one-hop graph propagation: a word-poor target whose refs-graph neighbour matches the
    // query gets score'(d) = sim(d) + λ·max_{n∈adj(d)} sim(n). λ<1 keeps the boost below a direct
    // hit; it can lift a below-floor gap target over the floor via its neighbour. Uses RAW sims of
    // neighbours (pre-propagation) so it stays a single hop.
    const lam = opts.graphProp ?? 0;
    const eff = lam > 0 && this.adjacency.length === n ? new Float32Array(n) : raw;
    if (eff !== raw) {
      for (let i = 0; i < n; i++) {
        let bestNbr = 0;
        for (const j of this.adjacency[i]) if (raw[j] > bestNbr) bestNbr = raw[j];
        eff[i] = raw[i] + lam * bestNbr;
      }
    }

    const hits: SemHit[] = [];
    for (let i = 0; i < n; i++) {
      const name = this.names[i];
      if (opts.exclude.has(name)) continue;
      if (eff[i] >= opts.floor) hits.push({ name, sim: eff[i] });
    }
    hits.sort((a, b) => b.sim - a.sim || a.name.localeCompare(b.name));
    return hits.slice(0, opts.k);
  }
}

/** Load an extra embedding view (e.g. "nbr", "stmt"), reordered to match `primaryNames` so
 *  its rows align with the base view. Returns null (view simply skipped) when the sidecar is
 *  absent, wrong-dim, stale vs the index commit, or truncated — never throws. */
function loadAlignedView(
  prefix: string,
  view: string,
  primaryNames: string[],
  dim: number,
  indexCommit?: string,
): Float32Array | null {
  const metaPath = `${prefix}.${view}.meta.json`;
  const f32Path = `${prefix}.${view}.f32`;
  if (!fs.existsSync(metaPath) || !fs.existsSync(f32Path)) return null;
  try {
    const meta = JSON.parse(fs.readFileSync(metaPath, "utf8")) as { dim: number; names: string[]; index_commit?: string };
    if (meta.dim !== dim) return null;
    if (indexCommit && meta.index_commit !== indexCommit) {
      console.warn(`[semantic_tier] ${view} view stale vs index at ${prefix} — skipping`);
      return null;
    }
    const buf = fs.readFileSync(f32Path);
    if (buf.byteLength !== meta.names.length * dim * 4) return null;
    const raw = new Float32Array(buf.buffer, buf.byteOffset, buf.byteLength / 4);
    const rowOf = new Map<string, number>();
    meta.names.forEach((n, i) => rowOf.set(n, i));
    const aligned = new Float32Array(primaryNames.length * dim);
    for (let i = 0; i < primaryNames.length; i++) {
      const r = rowOf.get(primaryNames[i]);
      if (r !== undefined) aligned.set(raw.subarray(r * dim, (r + 1) * dim), i * dim);
    }
    return aligned;
  } catch {
    return null;
  }
}

/** Undirected refs-graph neighbourhood as row indices per decl, aligned to `names` row order.
 *  Neighbours = a decl's `refs` plus its reverse-refs (what uses it), capped like the nbr view
 *  so propagation cost stays bounded. Rows for names absent from the index get no neighbours. */
const MAX_ADJ = 16;
export function buildAdjacency(names: string[], entries: { name: string; refs?: string[] | null }[]): number[][] {
  const row = new Map<string, number>();
  names.forEach((n, i) => row.set(n, i));
  const adj: Set<number>[] = names.map(() => new Set<number>());
  for (const e of entries) {
    const ri = row.get(e.name);
    if (ri === undefined) continue;
    for (const r of e.refs ?? []) {
      const rj = row.get(r);
      if (rj === undefined || rj === ri) continue;
      adj[ri].add(rj); // ri references rj
      adj[rj].add(ri); // …so rj is used-by ri (reverse edge) — undirected neighbourhood
    }
  }
  return adj.map((s) => [...s].slice(0, MAX_ADJ));
}

/** The loaded tier per sidecar, keyed by the files' sizes and mtimes: `createRetrieval` is called
 *  per F1 pass and per CLI search, and the sidecar (names × dim floats) is read once per state
 *  of its files, not every time. A failed load is not cached. */
const tierCache = new Map<string, { key: string; tier: SemanticTier }>();

const fileStamp = (p: string): string => {
  try {
    const s = fs.statSync(p);
    return `${s.size}:${s.mtimeMs}`;
  } catch {
    return "-";
  }
};

/** Load a source's embedding sidecar. Returns null when absent (silently — the tier is
 *  optional), unreadable, stale vs the index, or truncated (with a warning). Never throws. */
export function loadSemanticTier(src: IndexSource): SemanticTier | null {
  const prefix = embeddingsPrefix(src.indexPath);
  const metaPath = `${prefix}.meta.json`;
  const f32Path = `${prefix}.f32`;
  if (!fs.existsSync(metaPath) || !fs.existsSync(f32Path)) return null;
  const key = [metaPath, f32Path, src.indexPath, `${prefix}.nbr.f32`].map(fileStamp).join("|");
  const cached = tierCache.get(prefix);
  if (cached && cached.key === key) return cached.tier;
  const tier = readSemanticTier(src, prefix, metaPath, f32Path);
  if (tier) tierCache.set(prefix, { key, tier });
  return tier;
}

function readSemanticTier(src: IndexSource, prefix: string, metaPath: string, f32Path: string): SemanticTier | null {
  let meta: { dim: number; names: string[]; index_commit?: string };
  let lib: { commit?: string; entries: { name: string; refs?: string[] | null }[] };
  try {
    meta = JSON.parse(fs.readFileSync(metaPath, "utf8"));
    lib = JSON.parse(fs.readFileSync(src.indexPath, "utf8"));
  } catch (e) {
    console.warn(`[semantic_tier] unreadable embeddings/index for ${src.indexPath} (${e instanceof Error ? e.message : String(e)}) — semantic tier off`);
    return null;
  }
  const idx = { commit: lib.commit, names: lib.entries.map((e) => e.name) };
  if (isEmbeddingsStale(meta, idx)) {
    console.warn(`[semantic_tier] embeddings stale vs ${src.indexPath} — semantic tier off for this source`);
    return null;
  }
  const buf = fs.readFileSync(f32Path);
  const expectedBytes = meta.names.length * meta.dim * 4;
  if (!Number.isInteger(meta.dim) || meta.dim <= 0 || buf.byteLength !== expectedBytes) {
    // why: stale/truncated sidecars otherwise produce undefined vector reads.
    console.warn(`[semantic_tier] embeddings shape mismatch: got ${buf.byteLength} bytes, expected ${expectedBytes} (${meta.names.length}×${meta.dim}×4) — disabling semantic tier`);
    return null;
  }
  const vecs = new Float32Array(buf.buffer, buf.byteOffset, buf.byteLength / 4);

  // The dependency-graph neighbourhood view, when its sidecar is present + fresh, scored by
  // max-sim (see SemanticTier) so it only ever helps. On the eval it beat nl-only across every
  // stratum (gap hit@3 +10%, recall@10 +13%); a statement-structure view diluted hit@3 (a NL
  // query vs raw Lean syntax is noisy in an un-fine-tuned encoder) and is not loaded.
  const extraViews: Float32Array[] = [];
  const nbr = loadAlignedView(prefix, "nbr", meta.names, meta.dim, lib.commit);
  if (nbr) extraViews.push(nbr);
  const adjacency = buildAdjacency(meta.names, lib.entries);
  return new SemanticTier(meta.names, vecs, meta.dim, extraViews, adjacency);
}

/**
 * Embed query texts at runtime with the encoder named in a source's embedding meta (via the
 * `scripts/embed_text.py` subprocess, `--model-path`), so a live query can be cosine-matched
 * against that source's decl vectors. A relative model path resolves against the library root.
 * Returns one normalized vector per input text (empty array for empty input).
 * NB: loads the model once per call (~30 s) — batch all queries into ONE call; do not call
 * per-item in a loop. Throws if python/model/meta are unavailable; callers should catch and
 * fall back to lexical-only.
 */
export function embedQueries(texts: string[], src: IndexSource): Float32Array[] {
  if (texts.length === 0) return [];
  const meta = JSON.parse(fs.readFileSync(`${embeddingsPrefix(src.indexPath)}.meta.json`, "utf8")) as { dim: number; model?: string };
  const dim = meta.dim;
  const script = path.resolve(import.meta.dirname, "..", "..", "scripts", "embed_text.py");
  const out = path.join(os.tmpdir(), `ceq_${process.pid}_${texts.length}.f32`);
  const modelArgs: string[] = [];
  if (meta.model) {
    const local = path.isAbsolute(meta.model) ? meta.model : path.join(sourceRoot(src), meta.model);
    modelArgs.push("--model-path", fs.existsSync(local) ? local : meta.model);
  }
  // `python3` is not a program name on Windows — resolve the interpreter (throws if none).
  const [bin, argv] = pythonArgs(script, ["--out", out, ...modelArgs]);
  // 180 s cap: a stuck model load must degrade to lexical, never stall the F1 pipeline.
  execFileSync(bin, argv, {
    input: texts.map((t) => t.replace(/\r?\n/g, " ")).join("\n"),
    timeout: 180_000,
    maxBuffer: 64 * 1024 * 1024,
  });
  const buf = fs.readFileSync(out);
  const all = new Float32Array(buf.buffer, buf.byteOffset, buf.byteLength / 4);
  fs.rmSync(out, { force: true });
  return texts.map((_, i) => all.subarray(i * dim, (i + 1) * dim));
}
