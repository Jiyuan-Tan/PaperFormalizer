#!/usr/bin/env -S npx tsx
/**
 * Lint a TheoremChecker toolkit's layout (layering, module size, header contract, run tokens, and —
 * once the toolkit has `doc/taxonomy.json` — the topic tree).
 *
 *   npx tsx bin/lint_toolkit_layout.ts [--toolkit <root>] [--scope toolkit|all] [--json]
 *
 * The root resolves like every TheoremChecker command (`--toolkit`, `THEOREMCHECKER_TOOLKIT`, or the
 * nearest ancestor holding `theoremchecker.json`). `--scope toolkit` lints the toolkit library
 * only; `all` (default) adds the papers library. Study staging is never linted (it is
 * temporary), but importing it from anywhere else is an error.
 * Exit 1 on any finding.
 */
import { existsSync, readFileSync, readdirSync, statSync } from "node:fs";
import path from "node:path";
import process from "node:process";
import { fileURLToPath } from "node:url";
import { loadToolkitConfig, TOOLKIT_STAGING_SEGMENT, type ToolkitConfig } from "../src/toolkit/config.js";
import { formatLayoutFinding, lintToolkitLayout, type ToolkitModuleSource } from "../src/toolkit/layout_lint.js";
import { parseTaxonomy, taxonomyPath } from "../src/toolkit/taxonomy.js";
import { moduleNameFromPath } from "../src/toolkit/lean_source.js";
import { isPaperTmpPath } from "../src/paths.js";

function leanFilesUnder(dir: string, skip: (abs: string) => boolean): string[] {
  if (!existsSync(dir) || skip(dir)) return [];
  if (statSync(dir).isFile()) return dir.endsWith(".lean") ? [dir] : [];
  const out: string[] = [];
  for (const entry of readdirSync(dir, { withFileTypes: true })) {
    const abs = path.join(dir, entry.name);
    if (entry.isDirectory()) { if (entry.name !== ".lake") out.push(...leanFilesUnder(abs, skip)); }
    else if (entry.isFile() && entry.name.endsWith(".lean") && !skip(abs)) out.push(abs);
  }
  return out;
}

/** Load the modules to lint. Pure helper exported for tests. */
export function collectToolkitModules(cfg: ToolkitConfig, scope: "toolkit" | "all"): ToolkitModuleSource[] {
  // Study staging and each paper's disposable `tmp/` workspace (axiom probes, scratch files) are
  // not library modules.
  const skip = (abs: string) =>
    abs === cfg.stagingDir || abs.startsWith(`${cfg.stagingDir}${path.sep}`) ||
    isPaperTmpPath(path.relative(cfg.papersDir, abs));
  const files = [
    path.join(cfg.toolkitRoot, `${cfg.lib}.lean`),
    ...leanFilesUnder(cfg.toolkitLibDir, skip),
    ...(scope === "all"
      ? [path.join(cfg.toolkitRoot, `${cfg.papersLib}.lean`), ...leanFilesUnder(cfg.papersDir, skip)]
      : []),
  ].filter((f) => existsSync(f));
  return [...new Set(files)].sort().map((abs) => {
    const rel = path.relative(cfg.toolkitRoot, abs).split(path.sep).join("/");
    return { path: rel, module: moduleNameFromPath(rel), text: readFileSync(abs, "utf8") };
  });
}

function main(): void {
  const argv = process.argv.slice(2);
  const take = (name: string): string[] => {
    const vals: string[] = [];
    for (let i = argv.indexOf(name); i >= 0; i = argv.indexOf(name)) {
      const v = argv[i + 1];
      if (v === undefined || v.startsWith("--")) throw new Error(`${name} needs a value`);
      vals.push(v);
      argv.splice(i, 2);
    }
    return vals;
  };
  const json = argv.includes("--json");
  const explicit = take("--toolkit").at(-1);
  const scope = take("--scope").at(-1) ?? "all";
  const toolkit = explicit ?? argv.find((a) => !a.startsWith("--")) ?? null;
  if (scope !== "toolkit" && scope !== "all") throw new Error(`--scope must be toolkit|all (got ${scope})`);
  const cfg = loadToolkitConfig({ explicit: toolkit });
  const modules = collectToolkitModules(cfg, scope);
  // The topic rule applies once the toolkit has its own tree.
  const tax = existsSync(taxonomyPath(cfg)) ? parseTaxonomy(readFileSync(taxonomyPath(cfg), "utf8"), taxonomyPath(cfg)) : null;
  const findings = lintToolkitLayout(modules, {
    lib: cfg.lib, papersLib: cfg.papersLib, divisions: cfg.divisions, stagingSegment: TOOLKIT_STAGING_SEGMENT,
    ...(tax ? { topics: tax.topics.map((t) => t.path) } : {}),
  });
  if (json) console.log(JSON.stringify({ toolkit: cfg.toolkitRoot, modules: modules.length, findings }, null, 2));
  else {
    for (const f of findings) console.log(formatLayoutFinding(f));
    console.log(`[lint_toolkit_layout] ${cfg.toolkitRoot}: ${modules.length} module(s), ${findings.length} finding(s)`);
  }
  // Advisory findings (conventions `garden` repairs) are reported but never fail the lint.
  if (findings.some((f) => !f.advisory)) process.exitCode = 1;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {
    main();
  } catch (err) {
    console.error(`lint_toolkit_layout: ${err instanceof Error ? err.message : String(err)}`);
    process.exitCode = 1;
  }
}
