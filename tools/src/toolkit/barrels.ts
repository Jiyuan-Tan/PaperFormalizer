// Barrel maintenance for a toolkit: add one `public import` to a module-system barrel, keeping
// the import block sorted and the rest of the file byte-for-byte. Used by the study apply gate
// (division barrels) and by F5 (the root `<papers_lib>.lean` barrel of the paper output).
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import { writeTextAtomic } from "../shared/json_atomic.js";
import { maskLeanCommentsAndStrings } from "../shared/lean_mask.js";
import { isLeanModuleFile, LEAN_MODULE_LINE_RE, parseLeanImport } from "../shared/lean_syntax.js";
import type { ToolkitConfig } from "./config.js";

/** Add one barrel import in deterministic module-name order (idempotent; an import-shaped
 *  comment is not an import). The first import of an import-free module file goes right after
 *  `module`. */
export function insertImportSorted(rootFileText: string, importLine: string): string {
  const lines = rootFileText.split(/\r?\n/);
  const maskedLines = maskLeanCommentsAndStrings(rootFileText).split(/\r?\n/);
  const incoming = parseLeanImport(importLine);
  if (!incoming) throw new Error(`invalid Lean import line: ${importLine}`);
  const existing = lines
    .map((line, index) => ({ line, index, parsed: parseLeanImport(maskedLines[index] ?? "") }))
    .filter((row): row is { line: string; index: number; parsed: NonNullable<ReturnType<typeof parseLeanImport>> } => row.parsed != null);
  if (existing.some((row) => row.line === importLine)) return rootFileText;

  const imports = [
    ...existing.filter((row) => row.parsed.module !== incoming.module).map((row) => row.line),
    importLine,
  ].sort((a, b) => {
    const am = parseLeanImport(a)!.module;
    const bm = parseLeanImport(b)!.module;
    return am < bm ? -1 : am > bm ? 1 : a < b ? -1 : a > b ? 1 : 0;
  });
  if (existing.length > 0) {
    const firstImport = existing[0].index;
    const importIndexes = new Set(existing.map((row) => row.index));
    const rest = lines.filter((_, index) => !importIndexes.has(index));
    rest.splice(firstImport, 0, ...imports);
    return rest.join("\n");
  }

  const moduleLine = isLeanModuleFile(rootFileText)
    ? lines.findIndex((line) => LEAN_MODULE_LINE_RE.test(line))
    : -1;
  lines.splice(moduleLine + 1, 0, importLine);
  return lines.join("\n");
}

/** `<toolkit>/<papers_lib>.lean` — the root barrel of the per-paper output. */
export function papersBarrelPath(cfg: ToolkitConfig): string {
  return path.join(cfg.toolkitRoot, `${cfg.papersLib}.lean`);
}

function freshPapersBarrel(papersLib: string, importLine: string): string {
  return [
    "module",
    "",
    importLine,
    "",
    "/-!",
    `# ${papersLib}`,
    "",
    "Barrel of the per-paper Lean output. Each verified paper owns one module tree",
    `\`${papersLib}.<Slug>.*\`, written by PaperFormalizer's F stages; a paper joins this barrel when its`,
    "F5 completes.",
    "-/",
    "",
    "public section",
    "",
  ].join("\n");
}

/**
 * Ensure the root papers barrel imports the paper barrel `module` (`<papers_lib>.<Pascal>`):
 * insert `public import <module>` into its sorted import block (idempotent), creating the barrel
 * when absent. The module-system header is preserved; a barrel that is not a module-system file
 * is refused rather than rewritten.
 */
export async function ensurePapersBarrelImport(
  cfg: ToolkitConfig,
  module: string,
): Promise<{ path: string; changed: boolean }> {
  const parts = module.split(".");
  if (parts.length !== 2 || parts[0] !== cfg.papersLib || !/^[A-Za-z_][A-Za-z0-9_']*$/.test(parts[1])) {
    throw new Error(`not a paper barrel module of ${cfg.papersLib}: ${module}`);
  }
  const file = papersBarrelPath(cfg);
  const importLine = `public import ${module}`;
  if (!existsSync(file)) {
    await writeTextAtomic(file, freshPapersBarrel(cfg.papersLib, importLine));
    return { path: file, changed: true };
  }
  const text = await readFile(file, "utf8");
  if (!isLeanModuleFile(text)) {
    throw new Error(`${file} is not a module-system file (no \`module\` header); refusing to rewrite it`);
  }
  const next = insertImportSorted(text, importLine);
  if (next === text) return { path: file, changed: false };
  await writeTextAtomic(file, next);
  return { path: file, changed: true };
}

/**
 * Remove the root papers barrel's import of the paper barrel `module` (idempotent; a barrel that
 * does not exist or does not import it is left untouched). Used when a run re-extracts its core
 * (`--from-stage V1` / `V1.5`): the paper is no longer a completed F5 until it completes again,
 * when `ensurePapersBarrelImport` re-adds it.
 */
export async function removePapersBarrelImport(
  cfg: ToolkitConfig,
  module: string,
): Promise<{ path: string; changed: boolean }> {
  const file = papersBarrelPath(cfg);
  if (!existsSync(file)) return { path: file, changed: false };
  const text = await readFile(file, "utf8");
  const lines = text.split(/\r?\n/);
  const masked = maskLeanCommentsAndStrings(text).split(/\r?\n/);
  const keep = lines.filter((_, i) => parseLeanImport(masked[i] ?? "")?.module !== module);
  if (keep.length === lines.length) return { path: file, changed: false };
  await writeTextAtomic(file, keep.join("\n"));
  return { path: file, changed: true };
}
