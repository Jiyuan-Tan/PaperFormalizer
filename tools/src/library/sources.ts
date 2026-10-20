// Index sources: the per-declaration indices F-stage retrieval searches, derived from the
// toolkit config (`theoremchecker.json`) — never from a fixed repository layout.
//
// A source is one `library_index.json`-shaped file at ANY path, tagged with the library it
// indexes. Every base library with an `index` contributes one; the toolkit's own index
// (`doc/toolkit_index.json`) contributes one when it exists. Review sidecars (per-area
// `<Area>.json`, a tier-1 ranking signal only) and an alias lexicon are optional per source.
import { existsSync, statSync } from "node:fs";
import path from "node:path";
import { loadToolkitConfig, type ToolkitConfig } from "../toolkit/config.js";

export interface IndexSource {
  /** Library name every hit from this source is tagged with (a base library name from the
   *  config, or the toolkit library). Empty ⇒ derived from the index's module names. */
  library: string;
  /** Absolute path of the index file. */
  indexPath: string;
  /** Directory of per-area review sidecars (`<Area>.json`), when the library ships them. */
  reviewSidecars?: string;
  /** Alias lexicon file (`tools/data/aliases/*.json` shape), when configured. */
  aliasFile?: string;
  /** Library package root; relative model paths in embedding metadata resolve against it. */
  root?: string;
}

function isDir(p: string): boolean {
  try {
    return statSync(p).isDirectory();
  } catch {
    return false;
  }
}

/** A source for an index file at any path. Without an explicit `reviewSidecars`, a sibling
 *  `library_review/` directory (the layout `lake exe library_index` writes) is used when present. */
export function indexSourceFromPath(
  indexPath: string,
  opts: { library?: string; reviewSidecars?: string; aliasFile?: string; root?: string } = {},
): IndexSource {
  const abs = path.resolve(indexPath);
  const sibling = path.join(path.dirname(abs), "library_review");
  const reviewSidecars = opts.reviewSidecars ?? (isDir(sibling) ? sibling : undefined);
  return {
    library: opts.library ?? "",
    indexPath: abs,
    ...(reviewSidecars ? { reviewSidecars } : {}),
    ...(opts.aliasFile ? { aliasFile: path.resolve(opts.aliasFile) } : {}),
    ...(opts.root ? { root: path.resolve(opts.root) } : {}),
  };
}

/** Every index source a toolkit config names, in config order (base libraries first, then the
 *  toolkit). A configured index that does not exist on disk is skipped. `exists` is injectable. */
export function indexSourcesFromToolkit(
  cfg: ToolkitConfig,
  exists: (p: string) => boolean = existsSync,
): IndexSource[] {
  const out: IndexSource[] = [];
  for (const b of cfg.baseLibraries) {
    if (!b.index || !exists(b.index)) continue;
    out.push(indexSourceFromPath(b.index, {
      library: b.name,
      ...(b.reviewSidecars ? { reviewSidecars: b.reviewSidecars } : {}),
      ...(b.aliasFile ? { aliasFile: b.aliasFile } : {}),
      ...(b.path ? { root: b.path } : {}),
    }));
  }
  if (exists(cfg.indexPath)) {
    out.push(indexSourceFromPath(cfg.indexPath, { library: cfg.lib, root: cfg.toolkitRoot }));
  }
  return out;
}

/** The index sources for a pipeline context: `ctx.toolkit`, else the toolkit found from the
 *  repo root. Retrieval is best-effort, so an unresolvable toolkit yields `[]` with a warning. */
export function indexSourcesForContext(ctx: { repoRoot: string; toolkit?: ToolkitConfig }): IndexSource[] {
  let cfg: ToolkitConfig;
  try {
    cfg = ctx.toolkit ?? loadToolkitConfig({ cwd: ctx.repoRoot });
  } catch (e) {
    console.warn(`[retrieval] no toolkit config (${e instanceof Error ? e.message : String(e)}); library retrieval is disabled`);
    return [];
  }
  const sources = indexSourcesFromToolkit(cfg);
  if (sources.length === 0) {
    console.warn(`[retrieval] ${cfg.configPath} names no existing index; library retrieval is disabled`);
  }
  return sources;
}
