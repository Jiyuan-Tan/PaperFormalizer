// The declaration names the plan gate's reuse-existence check (P5) accepts: every name in the
// configured index sources (base-library indices and `doc/toolkit_index.json` when built) PLUS the
// toolkit's own declarations, which may not be indexed yet — the ledger (`doc/ledger.json`)
// records every admitted one, and the `Toolkit/**/*.lean` sources (study staging excluded, it is
// imported by nothing) are scanned for namespace-qualified declared names.
//
// P5 can only judge names an indexed source OWNS: the top-level module segments of every index
// source plus the toolkit and papers libraries. A name outside all of them (Mathlib, or any
// `transitive` base without an index) is reported as a note, never a violation.
import { existsSync, readFileSync, readdirSync, statSync } from "node:fs";
import path from "node:path";
import { createRetrieval } from "./reuse_retrieval.js";
import { indexSourcesForContext } from "../library/sources.js";
import { parseLedger } from "../toolkit/ledger.js";
import { declaredNames } from "../toolkit/lean_source.js";
import { loadToolkitConfig, type ToolkitConfig } from "../toolkit/config.js";

function leanFilesUnder(dir: string, skipDir: string): string[] {
  if (!existsSync(dir) || !statSync(dir).isDirectory()) return [];
  const out: string[] = [];
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    const abs = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      if (abs !== skipDir && entry.name !== ".lake") out.push(...leanFilesUnder(abs, skipDir));
    } else if (entry.isFile() && entry.name.endsWith(".lean")) out.push(abs);
  }
  return out;
}

/** Toolkit declaration names: the ledger's records ∪ names declared in `<lib>.lean` and
 *  `<lib>/**` (staging excluded). A malformed ledger is reported, not fatal: the scan still runs. */
export function toolkitDeclarationNames(cfg: ToolkitConfig): Set<string> {
  const names = new Set<string>();
  if (existsSync(cfg.ledgerPath)) {
    try {
      for (const d of parseLedger(readFileSync(cfg.ledgerPath, "utf8"), cfg.ledgerPath).declarations) names.add(d.name);
    } catch (e) {
      console.warn(`[known-decls] ${e instanceof Error ? e.message : String(e)}; toolkit names come from the Lean sources only`);
    }
  }
  const root = path.join(cfg.toolkitRoot, `${cfg.lib}.lean`);
  const files = [...(existsSync(root) ? [root] : []), ...leanFilesUnder(cfg.toolkitLibDir, cfg.stagingDir)];
  for (const f of files) {
    for (const d of declaredNames(readFileSync(f, "utf8"))) names.add(d.name);
  }
  return names;
}

/** The P5 inputs: the known names and the top-level prefixes whose names P5 may check. */
export interface KnownDecls {
  names: Set<string>;
  ownedPrefixes: string[];
}

/**
 * The P5 known-declaration set for a pipeline context, or undefined when no index source loads
 * (P5 is then skipped with a warning by the caller: without the base index the set would flag
 * every base-library reuse).
 */
export function knownDeclsForContext(ctx: { repoRoot: string; toolkit?: ToolkitConfig }): KnownDecls | undefined {
  let indexed: Set<string> | undefined;
  const owned = new Set<string>();
  try {
    const retrieval = createRetrieval(indexSourcesForContext(ctx));
    indexed = retrieval.knownDecls();
    for (const l of retrieval.libraries) {
      for (const e of l.library.entries) {
        const root = e.module.split(".")[0];
        if (root) owned.add(root);
      }
    }
  } catch {
    indexed = undefined;
  }
  if (!indexed) return undefined;
  let cfg: ToolkitConfig | null = ctx.toolkit ?? null;
  if (!cfg) {
    try {
      cfg = loadToolkitConfig({ cwd: ctx.repoRoot });
    } catch {
      cfg = null;
    }
  }
  if (cfg) {
    for (const n of toolkitDeclarationNames(cfg)) indexed.add(n);
    owned.add(cfg.lib);
    owned.add(cfg.papersLib);
  }
  return { names: indexed, ownedPrefixes: [...owned].sort() };
}
