// Papers may import each other: a paper's declarations another paper's Lean uses are reuse already
// shown. Round B flags them for the curator (`importedBy`); a move rewrites the references in those
// papers' files as in its own paper (`findImporters` → `planMove`), and its gate builds them.
import { execFile } from "node:child_process";
import { existsSync } from "node:fs";
import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import { PAPER_TMP_DIR } from "../paths.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { declaredNames } from "../toolkit/lean_source.js";
import { referencedNames } from "./move.js";

/** Other papers that may use a paper's declarations. */
export interface Importers {
  /** Their `.lean` files that name the paper's namespace or modules (absolute, sorted). */
  files: string[];
  /** Each such paper (`Papers.<Other>`): every declaration it declares itself (all its files) — at a
   *  use site in its files these shadow the moving paper's names (`rewriteReferences`' `shadow`). */
  declared: Map<string, Set<string>>;
}

export const NO_IMPORTERS: Importers = { files: [], declared: new Map() };

/** The paper (`Papers.<Other>`) a file of the papers' library belongs to. */
export function paperOfFile(cfg: Pick<ToolkitConfig, "toolkitRoot" | "papersLib">, file: string): string {
  const rel = path.relative(path.join(cfg.toolkitRoot, cfg.papersLib), file).split(path.sep);
  return `${cfg.papersLib}.${rel[0]!.replace(/\.lean$/, "")}`;
}

/**
 * The files of OTHER papers that can use `paperModule`'s (`Papers.<Pascal>`) declarations: one
 * whole-word `grep` for the paper's name over the papers' sources, every paper's `tmp/` scratch
 * left out. Using a declaration outside its own namespace takes writing that namespace somewhere in
 * the file (an `open`, a full name, a `namespace`), and Lean resolves it only when the paper is in the
 * file's import closure, direct or not — so no import line is required here; which names a hit
 * really uses, the move's name resolution decides. With each such paper's own declarations.
 */
export async function findImporters(cfg: Pick<ToolkitConfig, "toolkitRoot" | "papersLib">, paperModule: string): Promise<Importers> {
  const dir = path.join(cfg.toolkitRoot, cfg.papersLib);
  if (!existsSync(dir)) return NO_IMPORTERS;
  // grep: 0 = matches, 1 = none, anything else = it could not read the sources
  const stdout = await new Promise<string>((resolve, reject) => {
    execFile("grep", ["-rlFw", "--include=*.lean", `--exclude-dir=${PAPER_TMP_DIR}`, "-e", paperModule, dir], { encoding: "utf8", maxBuffer: 64 * 1024 * 1024 }, (err, so, se) => {
      if (!err || (err as { code?: unknown }).code === 1) resolve(err ? "" : so);
      else reject(new Error(`the papers' sources could not be searched for users of ${paperModule} (grep: ${se.trim() || err.message})`));
    });
  });
  const files = stdout.split("\n").filter(Boolean).filter((f) => paperOfFile(cfg, f) !== paperModule).sort();
  const declared = new Map<string, Set<string>>();
  for (const other of new Set(files.map((f) => paperOfFile(cfg, f)))) {
    const names = new Set<string>();
    const own = path.join(cfg.toolkitRoot, ...other.split("."));
    for (const f of [`${own}.lean`, ...(await leanFilesUnder(own))]) {
      if (!existsSync(f)) continue;
      for (const x of declaredNames(await readFile(f, "utf8"))) names.add(x.name);
    }
    declared.set(other, names);
  }
  return { files, declared };
}

async function leanFilesUnder(dir: string): Promise<string[]> {
  const out: string[] = [];
  for (const e of await readdir(dir, { withFileTypes: true }).catch(() => [])) {
    const abs = path.join(dir, e.name);
    if (e.isDirectory()) { if (e.name !== PAPER_TMP_DIR) out.push(...(await leanFilesUnder(abs))); }
    else if (e.isFile() && e.name.endsWith(".lean")) out.push(abs);
  }
  return out;
}

/**
 * For each of `names` (fully-qualified declarations of `paperModule`) that another paper's Lean
 * uses: those papers (`Papers.<Other>`), sorted. Read from `findImporters`' files with the move's
 * own name resolution (`referencedNames`, the paper's own declarations shadowing), so a name flagged
 * here is a name a move of it rewrites there.
 */
export async function importedBy(cfg: Pick<ToolkitConfig, "toolkitRoot" | "papersLib">, paperModule: string, names: readonly string[], imp?: Importers): Promise<Map<string, string[]>> {
  const out = new Map<string, Set<string>>();
  const wanted = new Set(names);
  if (wanted.size === 0) return new Map();
  const { files, declared } = imp ?? (await findImporters(cfg, paperModule));
  for (const f of files) {
    const other = paperOfFile(cfg, f);
    for (const n of referencedNames(await readFile(f, "utf8"), wanted, declared.get(other))) out.set(n, (out.get(n) ?? new Set()).add(other));
  }
  return new Map([...out].map(([n, s]) => [n, [...s].sort()] as const));
}
