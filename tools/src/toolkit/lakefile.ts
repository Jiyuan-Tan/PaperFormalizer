// The toolkit's Lake targets, read from its lakefile (never guessed). PaperFormalizer needs two
// executables and the two libraries in every toolkit:
//   `paper_index`    F5 docstring coverage (`lake exe paper_index -- --prefix … --out …`),
//   `toolkit_index`  indexes the toolkit library into `doc/toolkit_index.json`, the toolkit's
//                    retrieval source,
//   `<lib>` / `<papers_lib>`  the `lean_lib`s the toolkit config names.
// The `candidate_scan` exe (the template's `CandidateScan.lean`) is needed only by the promotion
// round after the report and by `toolkit-health`; they check for it when they start.
// `assertToolkitLakefile` runs at the start of every `verify` run and fails closed,
// naming the template (`templates/toolkit/` in this repository) the missing targets come from.
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import { paperFormalizerToolsDir, type ToolkitConfig } from "./config.js";

export const REQUIRED_TOOLKIT_EXES = ["paper_index", "toolkit_index"] as const;

export interface LakefileTargets {
  /** Absolute path of the lakefile read, or null when the toolkit has none. */
  file: string | null;
  libs: Set<string>;
  exes: Set<string>;
}

const stripQuotes = (s: string): string => s.replace(/^«|»$/g, "").replace(/^"|"$/g, "");

/** `lean_lib` / `lean_exe` names declared in a `lakefile.toml`: the `name` key of each
 *  `[[lean_lib]]` / `[[lean_exe]]` table (up to the next table header). Comments are ignored. */
export function parseLakefileToml(text: string): { libs: Set<string>; exes: Set<string> } {
  const libs = new Set<string>();
  const exes = new Set<string>();
  let section: "lib" | "exe" | null = null;
  for (const raw of text.split(/\r?\n/)) {
    const line = raw.replace(/(^|\s)#.*$/, "").trim();
    if (line === "") continue;
    const header = /^\[\[?\s*([A-Za-z_.]+)\s*\]\]?$/.exec(line);
    if (header) {
      section = header[1] === "lean_lib" && line.startsWith("[[") ? "lib"
        : header[1] === "lean_exe" && line.startsWith("[[") ? "exe"
        : null;
      continue;
    }
    const name = /^name\s*=\s*"([^"]+)"$/.exec(line);
    if (name && section) (section === "lib" ? libs : exes).add(name[1]);
  }
  return { libs, exes };
}

/** `lean_lib` / `lean_exe` names declared in a `lakefile.lean` (`lean_lib Foo`, `lean_exe «foo»`). */
export function parseLakefileLean(text: string): { libs: Set<string>; exes: Set<string> } {
  const code = text.replace(/--.*$/gm, "");
  const collect = (kw: string) =>
    new Set([...code.matchAll(new RegExp(`\\b${kw}\\s+(«[^»]+»|[A-Za-z_][A-Za-z0-9_']*)`, "g"))].map((m) => stripQuotes(m[1])));
  return { libs: collect("lean_lib"), exes: collect("lean_exe") };
}

/** The toolkit's declared Lake targets (`lakefile.toml` first, else `lakefile.lean`). */
export function readLakefileTargets(
  root: string,
  io: { exists: (p: string) => boolean; read: (p: string) => string } = {
    exists: existsSync, read: (p) => readFileSync(p, "utf8"),
  },
): LakefileTargets {
  const toml = path.join(root, "lakefile.toml");
  if (io.exists(toml)) return { file: toml, ...parseLakefileToml(io.read(toml)) };
  const lean = path.join(root, "lakefile.lean");
  if (io.exists(lean)) return { file: lean, ...parseLakefileLean(io.read(lean)) };
  return { file: null, libs: new Set(), exes: new Set() };
}

/** `templates/toolkit/` of this repository: the lakefile, exe roots and barrels a toolkit starts from. */
export function toolkitTemplateDir(): string {
  return path.resolve(paperFormalizerToolsDir(), "..", "templates", "toolkit");
}

/** The targets a toolkit lakefile lacks (empty when complete). */
export function missingToolkitTargets(cfg: Pick<ToolkitConfig, "lib" | "papersLib">, t: LakefileTargets): string[] {
  const missing: string[] = [];
  for (const lib of [cfg.lib, cfg.papersLib]) if (!t.libs.has(lib)) missing.push(`lean_lib ${lib}`);
  for (const exe of REQUIRED_TOOLKIT_EXES) if (!t.exes.has(exe)) missing.push(`lean_exe ${exe}`);
  return missing;
}

/**
 * Start-of-run check (`verify`): the toolkit lakefile must declare the toolkit and papers
 * libraries and the `paper_index` / `toolkit_index` executables. Throws, naming what is missing and
 * the template to copy it from; F5 would otherwise fail deep into a paid run.
 */
export function assertToolkitLakefile(
  cfg: Pick<ToolkitConfig, "lib" | "papersLib" | "toolkitRoot">,
  io?: Parameters<typeof readLakefileTargets>[1],
): void {
  const t = readLakefileTargets(cfg.toolkitRoot, io);
  const template = toolkitTemplateDir();
  if (!t.file) {
    throw new Error(
      `toolkit ${cfg.toolkitRoot} has no lakefile.toml or lakefile.lean. Start from the template ` +
        `${path.join(template, "lakefile.toml")} (with PaperIndex.lean and ToolkitIndex.lean).`,
    );
  }
  const missing = missingToolkitTargets(cfg, t);
  if (missing.length === 0) return;
  throw new Error(
    `toolkit lakefile ${t.file} is missing ${missing.join(", ")}. PaperFormalizer needs them (F5 runs ` +
      "`lake exe paper_index`; `lake exe toolkit_index` writes the toolkit's retrieval index). Copy the " +
      `\`[[lean_lib]]\` / \`[[lean_exe]]\` entries from ${path.join(template, "lakefile.toml")} and the exe roots ` +
      `${path.join(template, "PaperIndex.lean")} and ${path.join(template, "ToolkitIndex.lean")} into the toolkit root.`,
  );
}
