// Search instructions for agents working in a toolkit, rendered from `leansmith.json`, never
// hard-coded to one library: one command over every indexed source (the base libraries with an
// `index`, plus the toolkit's own index when built) through `npm run search -- --toolkit`, a
// named-tool or grep hint for every base without an index, and a grep hint for the toolkit
// while it has no index.
import { existsSync } from "node:fs";
import { loadToolkitConfig, leanSmithToolsDir, type ToolkitConfig } from "./config.js";

export interface SearchSource {
  name: string;
  /** Shell command prefix; append the query (`"<concepts>"`, `--type "<pat>"`, …). */
  command?: string;
  /** Plain-language instruction when no command applies. */
  hint?: string;
}

function shellQuote(s: string): string {
  return /^[A-Za-z0-9_./:@=+-]+$/.test(s) ? s : `'${s.replace(/'/g, `'\\''`)}'`;
}

/** The search CLI over every indexed source of the toolkit at `toolkitRoot`. */
export function toolkitSearchCommand(toolsDir: string, toolkitRoot: string): string {
  return `cd ${shellQuote(toolsDir)} && npm run search -- --toolkit ${shellQuote(toolkitRoot)}`;
}

/** Search sources for the base libraries and the toolkit. `exists` is injectable for tests. */
export function toolkitSearchSources(
  cfg: ToolkitConfig,
  toolsDir: string,
  exists: (p: string) => boolean = existsSync,
): SearchSource[] {
  const indexed: string[] = [];
  const out: SearchSource[] = [];
  for (const b of cfg.baseLibraries) {
    if (b.index && exists(b.index)) {
      indexed.push(b.name);
    } else if (b.search.length > 0) {
      out.push({ name: b.name, hint: `search with ${b.search.join(", ")} (lean-lsp tools)` });
    } else if (b.path) {
      out.push({ name: b.name, hint: `no index; grep its sources under ${b.path}` });
    }
  }
  if (exists(cfg.indexPath)) indexed.push(`${cfg.lib} (this toolkit)`);
  else out.push({ name: `${cfg.lib} (this toolkit)`, hint: `no toolkit index yet; grep the sources under ${cfg.toolkitLibDir}` });
  if (indexed.length > 0) {
    out.unshift({ name: indexed.join(", "), command: toolkitSearchCommand(toolsDir, cfg.toolkitRoot) });
  }
  return out;
}

/** Markdown bullet list of the sources, for a prompt. */
export function renderSearchBlock(sources: readonly SearchSource[]): string {
  const lines = sources.map((s) =>
    s.command
      ? `- ${s.name}: \`${s.command} "<concepts>"\` (declarations, tagged by library); add \`--scope module\` to find the topical home file, or use \`--type "<pattern>"\` / \`--goal "<goal>"\`.`
      : `- ${s.name}: ${s.hint}.`);
  return [
    ...lines,
    "- A miss in one source is not evidence of absence in another; check every source before minting.",
  ].join("\n");
}

/**
 * Where the sources of the base libraries and the toolkit are, one line for an agent that reads a
 * definition by name (a reviewer): a base library is outside the run's Lean directory. Empty when
 * no toolkit config resolves. A library with no source path of its own (Mathlib) is not listed.
 */
export function librarySourceRootsLine(ctx: { repoRoot: string; toolkit?: ToolkitConfig }): string {
  let cfg: ToolkitConfig | null = ctx.toolkit ?? null;
  if (!cfg) {
    try {
      cfg = loadToolkitConfig({ cwd: ctx.repoRoot });
    } catch {
      return "";
    }
  }
  const roots = [...cfg.baseLibraries.filter((b) => b.path).map((b) => `${b.name}: ${b.path}`), `${cfg.lib} (this toolkit): ${cfg.toolkitLibDir}`];
  return `- Library source roots, for a referenced definition the page does not unfold (Read/Grep its declaration by name before calling a target unadjudicable): ${roots.join("; ")}`;
}

/**
 * The `=== LIBRARY SEARCH ===` prompt block for an F-stage agent: where to look up existing
 * declarations for the run's toolkit (`ctx.toolkit`, else the toolkit found from the repo
 * root). Without a resolvable toolkit it says so, so the agent falls back to lean-lsp search.
 */
export function librarySearchPromptBlock(
  ctx: { repoRoot: string; toolkit?: ToolkitConfig },
  toolsDir: string = leanSmithToolsDir(),
): string {
  let cfg: ToolkitConfig | null = ctx.toolkit ?? null;
  if (!cfg) {
    try {
      cfg = loadToolkitConfig({ cwd: ctx.repoRoot });
    } catch {
      cfg = null;
    }
  }
  const body = cfg
    ? renderSearchBlock(toolkitSearchSources(cfg, toolsDir))
    : "- No toolkit config resolved: search with lean_local_search / lean_leansearch / lean_loogle only.";
  return [
    "=== LIBRARY SEARCH (base libraries + toolkit; search here before minting a declaration) ===",
    body,
    "- lean_leansearch / lean_loogle index Mathlib only; the command above indexes the listed libraries only.",
    "=== END LIBRARY SEARCH ===",
  ].join("\n");
}
