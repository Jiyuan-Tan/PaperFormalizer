/*!
 * Brief rendering over the reuse-retrieval engine (`reuse_retrieval.ts`).
 *
 * This file is downstream of the engine: it turns ranked candidates into the "library reuse
 * candidates" text block injected into the F1 plan brief (concept mode), one query per typed-core
 * node. Candidates are listed PER LIBRARY (one section per index source) so a large base library cannot crowd a small one out.
 */

import type { Core } from "../core/schema.js";
import type { IndexSource } from "../library/sources.js";
import { expandQuery } from "./aliases.js";
import { loadSemanticTier, embedQueries } from "./semantic_tier.js";
import { poolModules } from "./module_tier.js";
import {
  createRetrieval,
  symbolSet,
  backtickSpans,
  type Candidate,
  type F1Item,
  type Retrieval,
  type SemanticChannel,
} from "./reuse_retrieval.js";

// ─── scaffold-brief rendering (concept mode) ────────────────────────────────

export interface CandidateBlockOpts {
  topKPerItem?: number;
  totalCap?: number;
  /** Size cap on the rendered block (default `CANDIDATE_BLOCK_MAX_BYTES`): over it, the
   *  candidates per item go down one at a time, then the docstring lines go. The F1 block
   *  was 611 KB on a 1,080-entry core brief — 58% of a 1 MB prompt, at weak relevance. */
  maxBytes?: number;
  /** Blend each library's semantic tier into its concept search (confidence-aware fusion).
   *  The F1 plan-push turns this ON (stage1.ts); the human CLI leaves it opt-in. Query
   *  embedding goes through the warm daemon (~1 s; first call ~30 s cold-start), and needs
   *  the source's embeddings present. Degrades to lexical-only per library when they are
   *  missing/stale — never breaks the brief. */
  semantic?: boolean;
  /** Shell command prefix of the search CLI over the same sources, shown to the agent. */
  searchCommand?: string;
}

/** Min `typePattern` score for a supplementary candidate to be worth showing (≥2 shared
 * distinctive symbols). Below this the match is a single common symbol — noise. */
const SYMBOL_MIN_SCORE = 12;

/** The default size cap on a candidate block (see `CandidateBlockOpts.maxBytes`). */
export const CANDIDATE_BLOCK_MAX_BYTES = 160_000;

/**
 * Build the candidate block directly from a typed core (the F1 plan stage): one
 * retrieval query per core node (assumption / definition / statement), reusing the
 * shared ranking engine and output format. The S-block world
 * choice has no dedicated core node, so it is left to the agent's CLI / lean-lsp
 * search. Returns "" when the index is unavailable or the core has no nodes.
 */
export function coreReuseCandidateBlock(
  sources: readonly IndexSource[],
  core: Core,
  opts: CandidateBlockOpts = {},
): string {
  const r = createRetrieval(sources);
  if (r.libraries.length === 0) {
    console.error(`[reuse] no usable index among ${sources.length} source(s) — the core brief gets ZERO reuse candidates`);
    return "";
  }
  // The node-id slug carries the human concept words ("minimax-lower" → "minimax lower",
  // "clip-bias" → "clip bias"); it is a far stronger retrieval signal than the bare node
  // KIND ("theorem"/"assumption") or a symbol name ("M_n"). Prepend it to every query title
  // so both lexical and semantic ranking see the concept, not just the raw statement body.
  const slug = (id: string) => (id.split(":")[1] ?? "").replace(/-/g, " ").trim();
  const items: F1Item[] = [
    ...core.assumptions.map((a) => ({ kind: "A" as const, label: a.id, title: `${slug(a.id)} ${a.kind ?? "assumption"}`.trim(), body: a.condition })),
    ...core.definitions.map((d) => ({ kind: "P" as const, label: d.id, title: `${slug(d.id)} ${d.name}`.trim(), body: `${d.construction} ${(d.by_member_properties ?? []).join(" ")}`.trim() })),
    ...core.statements.map((s) => ({ kind: "L" as const, label: s.id, title: `${slug(s.id)} ${s.kind}`.trim(), body: s.statement })),
  ];
  if (items.length === 0) return "";
  return renderReuseCandidates(r, items, opts);
}

/**
 * Rank + format candidates for a list of typed-core items.
 */
function renderReuseCandidates(
  r: Retrieval,
  items: F1Item[],
  opts: CandidateBlockOpts,
): string {
  if (r.libraries.length === 0) return "";
  // Push is the baseline forcing-function; the agent can pull more via the CLI, so keep the
  // injected block lean — top 3 keyword candidates/item/library.
  const topKPerItem = opts.topKPerItem ?? 3;
  // `totalCap` is a SOFT total budget; the per-item budget is derived from it. The DEFAULT
  // scales with the node count so EVERY item gets its full `topKPerItem` regardless of core
  // size — a large core (30-51 nodes) must NOT starve to 1 candidate/node (a fixed `80`
  // collapsed perItem to 1 at ~50 nodes via `floor(80/items)`, hiding the correct candidate
  // that ranked #2-3). An explicit `opts.totalCap` still caps a pathological core.
  const totalCap = opts.totalCap ?? Math.max(80, topKPerItem * items.length);
  const perItemMax = Math.max(1, Math.min(topKPerItem, Math.floor(totalCap / Math.max(1, items.length))));
  // Optional semantic blend: per library, load the tier once and batch-embed every item's
  // query text in a SINGLE call (~1 s warm; ~30 s cold). Any failure (no embeddings, stale,
  // python missing) degrades that library to lexical-only — never breaks.
  const semVecs = new Map<string, { tier: SemanticChannel["tier"]; vecs: Float32Array[] }>();
  if (opts.semantic) {
    for (const lib of r.libraries) {
      try {
        const tier = loadSemanticTier(lib.source);
        if (tier) semVecs.set(lib.name, { tier, vecs: embedQueries(items.map((it) => `${it.title} ${it.body}`), lib.source) });
      } catch {
        /* lexical-only for this library */
      }
    }
  }
  // The block under its size cap: fewer candidates per item first (the lowest-ranked go), then
  // without the docstring lines. The lexical search is cheap to repeat; the embeddings are not
  // recomputed.
  const maxBytes = opts.maxBytes ?? CANDIDATE_BLOCK_MAX_BYTES;
  let block = "";
  for (let perItem = perItemMax; perItem >= 1; perItem--) {
    block = renderCandidateLines(r, items, opts, { perItem, docs: true, semVecs });
    if (Buffer.byteLength(block) <= maxBytes) return block;
  }
  return renderCandidateLines(r, items, opts, { perItem: 1, docs: false, semVecs });
}

function renderCandidateLines(
  r: Retrieval,
  items: F1Item[],
  opts: CandidateBlockOpts,
  shape: { perItem: number; docs: boolean; semVecs: Map<string, { tier: SemanticChannel["tier"]; vecs: Float32Array[] }> },
): string {
  const { perItem, semVecs } = shape;
  const multi = r.libraries.length > 1;
  const searchCli = opts.searchCommand
    ? `\`${opts.searchCommand} "<concept words>"\` (also \`--type "<sig pattern>"\`, \`--goal "<goal type>"\`)`
    : "the search CLI named in the brief";
  const lines: string[] = [
    "=== LIBRARY REUSE CANDIDATES (index-backed, per F1 plan node / item) ===",
    `Sources: ${r.libraries.map((l) => `${l.name} (${l.source.indexPath} @ ${l.library.commit})`).join("; ")}. ` +
      "The existing declarations most likely to fit each item — so you confront real " +
      "candidates instead of relying on a search you might not think to run.",
    "CONTRACT: decide EACH item below in its plan entry — `disposition:\"reuse\"` with " +
      "`reuse:\"<name>\"`, or `define-local` with why no candidate fits in one phrase of its `notes`. Prefer reuse " +
      "when a candidate fits the artifact's abstraction; verify the chosen decl's signature " +
      "with lean_hover_info before building on it. A `⚠usesSorry` candidate carries debt — " +
      "reuse only deliberately.",
    "Each item lists keyword candidates (`•`)" + (multi ? " per library (`[<library>]`)" : "") + "; a `↳ by type-signature` sub-list (when " +
      "present) matches the item's Lean/math symbols — use it for symbol-heavy items the " +
      "keyword pass missed, and confirm the shape fits. A `↳ relevant areas` line names the " +
      "module(s) whose contents are collectively closest to the item — read there (CLI / " +
      `lean_local_search) when no listed decl fits. Query the same indices yourself with ${searchCli}. ` +
      "This block and the CLI cover ONLY the sources above — a missing candidate is NOT " +
      "evidence a fact is absent, so before deciding that none fits (or planning to " +
      "build) on a plausibly-standard fact, search Mathlib (lean_leansearch / lean_loogle) as well.",
  ];
  const symbolTopK = Math.min(2, perItem);
  const render = (c: Candidate, bullet: string) => {
    const tags = [c.file, c.tier1 ? "tier-1" : "", c.usesSorry ? "⚠usesSorry" : ""]
      .filter(Boolean)
      .join(" · ");
    lines.push(`${bullet}${c.name} : ${c.statement.replace(/\s+/g, " ").slice(0, 200)}   [${tags}]`);
    if (shape.docs && c.docFirstPara) lines.push(`      ${c.docFirstPara.slice(0, 240)}`);
  };

  for (let itIdx = 0; itIdx < items.length; itIdx++) {
    const it = items[itIdx];
    lines.push("", `${it.label} — ${it.title}:`);
    let anyHit = false;
    for (const lib of r.libraries) {
      const sem = semVecs.get(lib.name);
      const channels = sem ? new Map([[lib.name, { tier: sem.tier, queryVec: sem.vecs[itIdx] }]]) : undefined;
      // One search per item and library over a POOL (top-50): the top `perItem` are the decl
      // candidates shown, and the whole pool is aggregated to modules (top-3 pooling) for the
      // "relevant areas" fallback.
      const pool = r.search(
        { mode: "concept", title: it.title, label: it.label, bodyTerms: [it.body] },
        { library: lib.name, topK: 50, semantic: channels ? { channels } : undefined },
      );
      const cands = pool.slice(0, perItem);
      const areas = poolModules(pool.map((c) => ({ module: c.module, name: c.name, score: c.score })), 2, 3);

      // Type-signature pass: for items whose discriminating content is Lean/math symbols
      // (inner products, projections, `Set.Icc`) rather than prose, concept-mode keyword
      // overlap finds little. Search the item's backtick symbols and surface fits that the
      // concept pass missed. Gated on ≥3 distinct symbols so word-rich items don't accrete
      // noise; a real match shares ≥2 distinctive symbols (scores ≥12).
      const seen = new Set(cands.map((c) => c.name));
      const symText = backtickSpans(`${it.title} ${it.body}`);
      const symCands =
        symbolSet(symText).size >= 3
          ? r
              .search({ mode: "typePattern", pattern: symText }, { library: lib.name, topK: perItem + symbolTopK })
              .filter((s) => !seen.has(s.name) && s.score >= SYMBOL_MIN_SCORE)
              .slice(0, symbolTopK)
          : [];
      if (cands.length === 0 && symCands.length === 0 && areas.length === 0) continue;
      anyHit = true;
      const ind = multi ? "  " : "";
      if (multi) lines.push(`  [${lib.name}]`);
      if (cands.length === 0 && symCands.length === 0) {
        lines.push(`${ind}  • (no single decl matched) relevant areas to read — search here with the CLI / lean_local_search:`);
        for (const a of areas) {
          const proto = a.prototypes.slice(0, 2).map((n) => n.split(".").slice(-1)[0]).join(", ");
          lines.push(`${ind}    ↳ ${a.module}${proto ? ` — e.g. ${proto}` : ""}`);
        }
        continue;
      }
      for (const c of cands) render(c, `${ind}  • `);
      if (symCands.length) {
        lines.push(`${ind}  ↳ by type-signature (vocabulary-independent — confirm the shape fits):`);
        for (const c of symCands) render(c, `${ind}    • `);
      }
      if (areas.length) {
        lines.push(`${ind}  ↳ relevant areas (read if none above fits): ${areas.map((a) => a.module).join(" · ")}`);
      }
    }
    if (!anyHit) {
      const exp = expandQuery(`${it.title} ${it.body}`, r.aliases);
      lines.push(exp.modules.length
        ? `  • (no indexed decl matched) likely module(s): ${exp.modules.join(", ")} — search here with lean_local_search.`
        : "  • (no indexed candidate matched — search the libraries directly.)");
    }
  }
  lines.push("=== END LIBRARY REUSE CANDIDATES ===");
  return lines.join("\n");
}
