/**
 * What a build of one paper's modules (or a statement scan of them) reads, as a signature, and the
 * record of the last green build of them under it. A build is skipped, and a scan's output reused,
 * only when the signature now is the one recorded: every input provably unchanged since. Anything
 * the signature cannot vouch for makes it a `doubt:` value equal to nothing, so the build runs.
 */
import { execFile } from "node:child_process";
import { createHash, randomUUID } from "node:crypto";
import { existsSync, readFileSync } from "node:fs";
import { mkdir, open, readdir, readFile, rename, unlink, writeFile } from "node:fs/promises";
import path from "node:path";
import { PAPER_TMP_DIR } from "../paths.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { parseLakefileLean, parseLakefileToml } from "../toolkit/lakefile.js";
import { leanWorkspaceFor } from "./build_mutex.js";
import { maskLeanCommentsAndStrings } from "./lean_mask.js";

const doubt = (why: string) => `doubt:${why}:${randomUUID()}`;
export const isDoubt = (sig: string) => sig.startsWith("doubt:");

async function leanFilesUnder(dir: string, skip: string | null, out: string[]): Promise<void> {
  for (const e of await readdir(dir, { withFileTypes: true }).catch(() => [])) {
    const abs = path.join(dir, e.name);
    if (e.isDirectory()) { if (e.name !== skip && e.name !== ".lake") await leanFilesUnder(abs, null, out); }
    else if (e.name.endsWith(".lean")) out.push(abs);
  }
}

/** A path dependency of the toolkit: its directory, lakefile and libraries; `inherited` when the
 *  toolkit requires it only through another dependency. */
interface PathPackage { dir: string; lakefile: string; libs: string[]; inherited: boolean }

/** The toolkit's path dependencies (Causalean, StatLean, … — a git dependency is pinned by its
 *  revision in the manifest). Null when a package's libraries cannot be read off its lakefile. */
async function pathPackages(root: string): Promise<PathPackage[] | null> {
  const manifestFile = path.join(root, "lake-manifest.json");
  if (!existsSync(manifestFile)) return [];
  let packages: { type?: string; dir?: string; inherited?: boolean }[];
  try {
    packages = (JSON.parse(await readFile(manifestFile, "utf8")) as { packages?: typeof packages }).packages ?? [];
  } catch {
    return null;
  }
  const out: PathPackage[] = [];
  for (const p of packages) {
    if (p.type !== "path") continue;
    if (!p.dir) return null;
    const dir = path.resolve(root, p.dir);
    const toml = path.join(dir, "lakefile.toml");
    const lean = path.join(dir, "lakefile.lean");
    const file = existsSync(toml) ? toml : existsSync(lean) ? lean : null;
    if (!file) return null;
    const text = await readFile(file, "utf8");
    // a library elsewhere than `<dir>/<Name>.lean` and `<dir>/<Name>/`: not read here
    if (/\b(srcDir|roots|globs)\b/.test(text.replace(/--.*$|#.*$/gm, ""))) return null;
    out.push({ dir, lakefile: file, libs: [...(file === toml ? parseLakefileToml(text) : parseLakefileLean(text)).libs], inherited: p.inherited === true });
  }
  return out;
}

/** The Lean sources of the toolkit's path dependencies: each library's root file and directory,
 *  and the package's lakefile. Null when a package's libraries cannot be read off its lakefile. */
async function pathDependencySources(root: string): Promise<string[] | null> {
  const packages = await pathPackages(root);
  if (!packages) return null;
  const files: string[] = [];
  for (const p of packages) {
    files.push(p.lakefile);
    for (const lib of p.libs) {
      const base = path.join(p.dir, ...lib.split("."));
      files.push(`${base}.lean`);
      await leanFilesUnder(base, null, files);
    }
  }
  return files;
}

/** Why the paper's modules import something outside the signature (another paper, a module at the
 *  toolkit root), or null. A dependency's module (Mathlib, Causalean, …) is covered above. */
async function foreignImport(root: string, libName: string, paperDir: string, paperFiles: readonly string[]): Promise<string | null> {
  const paperModule = path.relative(root, paperDir).split(path.sep).join(".");
  for (const f of paperFiles) {
    const text = await readFile(f, "utf8").catch(() => null);
    if (text === null) return `${f} unreadable`;
    for (const m of text.matchAll(/^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?([^\s]+)/gm)) {
      const mod = m[1]!.replace(/[«»]/g, "");
      const first = mod.split(".")[0]!;
      // the paper's own `tmp/` scratch is outside the signature
      if (mod === `${paperModule}.${PAPER_TMP_DIR}` || mod.startsWith(`${paperModule}.${PAPER_TMP_DIR}.`)) return `${path.relative(root, f)} imports ${mod} (its tmp/ scratch)`;
      if (first === libName || mod === paperModule || mod.startsWith(`${paperModule}.`)) continue;
      if (existsSync(path.join(root, `${first}.lean`)) || existsSync(path.join(root, first))) return `${path.relative(root, f)} imports ${mod}`;
    }
  }
  return null;
}

/**
 * A cheap signature of the sources a build or a statement scan of the toolkit and one paper reads:
 * the path, size, mtime and inode of every `.lean` file under the toolkit's library, the paper's
 * directory (its `tmp/` scratch aside) and the libraries of the path dependencies, of the two
 * barrels, of the lakefiles, manifest and toolchain file, and the toolchain the environment picks
 * (`ELAN_TOOLCHAIN`). The same signature before a build or scan and later means it was of the
 * sources as they still stand. Every toolkit write is atomic (temp file + rename), so a rewrite
 * changes the inode whatever the mtime resolution of the filesystem. Nothing is read but metadata
 * and the paper's import lines (a thousand-module toolkit on NFS takes seconds, a scan's build
 * minutes). A paper importing another paper or a module at the toolkit root, or a path dependency
 * whose libraries cannot be read off its lakefile, gives a `doubt:` signature.
 */
export async function sourceSignature(cfg: Pick<ToolkitConfig, "toolkitRoot" | "toolkitLibDir">, paperDir: string): Promise<string> {
  const files: string[] = [];
  await leanFilesUnder(cfg.toolkitLibDir, null, files);
  const paperFiles: string[] = [];
  await leanFilesUnder(paperDir, PAPER_TMP_DIR, paperFiles);
  const foreign = await foreignImport(cfg.toolkitRoot, path.basename(cfg.toolkitLibDir), paperDir, paperFiles);
  if (foreign) return doubt(foreign);
  const deps = await pathDependencySources(cfg.toolkitRoot);
  if (!deps) return doubt("a path dependency's libraries are not read off its lakefile");
  files.push(...paperFiles, ...deps, `${cfg.toolkitLibDir}.lean`, `${paperDir}.lean`, ...projectFiles(cfg.toolkitRoot));
  return signatureOf(files);
}

const projectFiles = (root: string) => ["lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain"].map((f) => path.join(root, f));

/** The signature of `files`: the path, size, mtime and inode of each, and the toolchain (`head`:
 *  by default `ELAN_TOOLCHAIN`). */
export async function signatureOf(files: readonly string[], head = `ELAN_TOOLCHAIN=${process.env.ELAN_TOOLCHAIN ?? ""}`): Promise<string> {
  return hashStates(head, await fileStates(files));
}

function hashStates(head: string, states: ReadonlyMap<string, string>): string {
  const h = createHash("sha256");
  h.update(`${head}\n`);
  for (const [f, st] of states) h.update(`${f}\0${st}\n`);
  return h.digest("hex");
}

/** The size, mtime and inode of each of `files` (`absent` for one not there), sorted by path. */
async function fileStates(files: readonly string[]): Promise<Map<string, string>> {
  const sorted = [...new Set(files)].sort();
  const stats = new Array<string>(sorted.length);
  // Each file opened before its attributes are read: an NFS client revalidates a file it opens
  // (close-to-open), so another host's write is seen, not a cached size and mtime. 16 at a time:
  // about a second for the ~5k files of a toolkit with its path dependencies (stat alone: 0.3 s).
  let next = 0;
  await Promise.all(Array.from({ length: 16 }, async () => {
    for (let i = next++; i < sorted.length; i = next++) {
      const s = await open(sorted[i]!, "r").then(async (fh) => { try { return await fh.stat({ bigint: true }); } finally { await fh.close(); } }).catch(() => null);
      stats[i] = s ? `${s.size}:${s.mtimeNs}:${s.ino}` : "absent";
    }
  }));
  return new Map(sorted.map((f, i) => [f, stats[i]!]));
}

/** The signature for a paper's modules, from the toolkit's config (the library's directory); a
 *  `doubt:` one when the config cannot be read. */
export async function paperBuildSignature(toolkitRoot: string, leanDir: string): Promise<string> {
  try {
    const { toolkitConfigFromJson, toolkitConfigFileIn } = await import("../toolkit/config.js");
    const file = toolkitConfigFileIn(toolkitRoot);
    if (!file) return doubt("no toolkit config");
    const cfg = toolkitConfigFromJson(toolkitRoot, JSON.parse(await readFile(file, "utf8")));
    return await sourceSignature(cfg, leanDir);
  } catch (err) {
    return doubt(err instanceof Error ? err.message : String(err));
  }
}

// ─── the toolkit as shared builds read it (`build_mutex.ts`) ─────────────────────────────────────

/** Where a toolkit's libraries and run records live: from its config, else (a bare Lake project)
 *  `Toolkit`, `Papers` and `runs` at the root. */
export interface ToolkitLayout { root: string; lib: string; libDir: string; staging: string; papersLib: string; papersDir: string; runsDir: string }

export async function toolkitLayout(root: string): Promise<ToolkitLayout> {
  const { toolkitConfigFromJson, toolkitConfigFileIn, TOOLKIT_RUNS_DIRNAME } = await import("../toolkit/config.js");
  const file = toolkitConfigFileIn(root);
  if (!file) {
    return { root, lib: "Toolkit", libDir: path.join(root, "Toolkit"), staging: "Staging", papersLib: "Papers", papersDir: path.join(root, "Papers"), runsDir: path.join(root, TOOLKIT_RUNS_DIRNAME) };
  }
  const cfg = toolkitConfigFromJson(root, JSON.parse(await readFile(file, "utf8")));
  return { root: cfg.toolkitRoot, lib: cfg.lib, libDir: cfg.toolkitLibDir, staging: path.basename(cfg.stagingDir), papersLib: cfg.papersLib, papersDir: cfg.papersDir, runsDir: cfg.runsDir };
}

/** The toolchain a Lake command in `root` runs: its `lean-toolchain` and what `lean --version`
 *  says there (elan resolves `ELAN_TOOLCHAIN`, an override, the file), read once per process; null
 *  when `lean --version` fails — not kept: the next call asks again. */
const toolchains = new Map<string, string>();
/** When reading a root's toolchain last failed: retried only after `TOOLCHAIN_RETRY_MS` (a hanging
 *  `lean` is never waited on again and again, least of all under the Lake mutex). */
const toolchainFailedAt = new Map<string, number>();
export const TOOLCHAIN_RETRY = { ms: 5 * 60_000 };
export async function toolchainOf(root: string): Promise<string | null> {
  const known = toolchains.get(root);
  if (known) return known;
  const failed = toolchainFailedAt.get(root);
  if (failed !== undefined && Date.now() - failed < TOOLCHAIN_RETRY.ms) return null;
  const version = await new Promise<string | null>((resolve) => {
    execFile("lean", ["--version"], { cwd: root, timeout: 60_000 }, (err, stdout) => resolve(err ? null : stdout.trim()));
  });
  if (version === null) { toolchainFailedAt.set(root, Date.now()); return null; }
  toolchainFailedAt.delete(root);
  const file = await readFile(path.join(root, "lean-toolchain"), "utf8").catch(() => "(none)");
  const v = `lean-toolchain=${file.trim()}\nlean=${version}`;
  toolchains.set(root, v);
  return v;
}

/** The modules a Lean file imports, read as Lake reads them: its header (`module`, `prelude`, then
 *  `[public] [meta] import [all] M`, comments and strings aside), which ends at the first other
 *  token. An import further down is no import (Lean rejects the file). */
export function headerImports(text: string): string[] {
  const src = maskLeanCommentsAndStrings(text);
  const token = /\s*((?:[^\s«]|«[^»]*»)+)/y;
  const out: string[] = [];
  let named = false; // the next token (after an `all`) names a module
  for (let m = token.exec(src); m; m = token.exec(src)) {
    const t = m[1]!;
    if (named) {
      if (t !== "all") { out.push(t.replace(/^all(?=«)/, "").replace(/[«»]/g, "")); named = false; }
    } else if (t === "import") named = true;
    // `import«Papers».Bar`: the keyword runs into a quoted name
    else if (t.startsWith("import«")) out.push(t.slice("import".length).replace(/[«»]/g, ""));
    else if (!["module", "prelude", "public", "private", "meta"].includes(t)) break;
  }
  return out;
}

/**
 * The signature of what a build of the toolkit's library and its path dependencies' libraries
 * reads: as `sourceSignature`, over the library (its `Staging` aside: studies write it all the
 * time, and nothing the library builds imports it — `toolkitScope` makes sure), its barrel, the
 * path dependencies' libraries, the lakefiles, manifest and toolchain file, and the toolchain they
 * resolve to (`toolchainOf`: the same in a pipeline and in a worker whatever their environment).
 * A `doubt:` value when a path dependency's libraries cannot be read off its lakefile, or the
 * toolchain's version cannot be read.
 */
export async function toolkitSignature(t: ToolkitLayout): Promise<string> {
  const toolchain = await toolchainOf(t.root);
  if (toolchain === null) return doubt("`lean --version` could not be read");
  const sources = await toolkitSources(t);
  if (!sources) return doubt("a path dependency's libraries are not read off its lakefile");
  return hashStates(toolchain, sources);
}

/** The sources `toolkitSignature` is of, each with its size, mtime and inode; null when a path
 *  dependency's libraries cannot be read off its lakefile. */
export async function toolkitSources(t: ToolkitLayout): Promise<Map<string, string> | null> {
  const files: string[] = [];
  await leanFilesUnder(t.libDir, t.staging, files);
  const deps = await pathDependencySources(t.root);
  if (!deps) return null;
  files.push(...deps, `${t.libDir}.lean`, ...projectFiles(t.root));
  return fileStates(files);
}

/** The sources whose state differs between two `toolkitSources` (written, added or removed). */
export function changedSources(before: ReadonlyMap<string, string>, after: ReadonlyMap<string, string>): string[] {
  return [...new Set([...before.keys(), ...after.keys()])].filter((f) => before.get(f) !== after.get(f)).sort();
}

/** What `lake build <targets>` makes of the toolkit, read off the import lines. */
export interface ToolkitScope {
  /** The toolkit's library and its own path dependencies' libraries (Causalean, StatLean, …). */
  targets: string[];
  /** Every library whose modules the targets' build makes: those, and the libraries of the path
   *  dependencies they require in turn. A module of another library (Mathlib, Lean) comes built
   *  with its package (pinned by the manifest), and is never built by a toolkit build. */
  libs: string[];
  /** The modules of `libs` the build makes: the targets and everything they import, transitively. */
  modules: string[];
  /** The targets' root `.olean`s: a build output wiped since (`lake clean`) changes their signature. */
  outputs: string[];
}

const libOf = (libs: Iterable<string>, mod: string) => [...libs].find((l) => mod === l || mod.startsWith(`${l}.`));
/** A module at the toolkit root outside its libraries' sources (a paper, an index executable's). */
const atRoot = (root: string, mod: string) => { const first = mod.split(".")[0]!; return existsSync(path.join(root, `${first}.lean`)) || existsSync(path.join(root, first)); };
const inDir = (mod: string, prefix: string) => mod === prefix || mod.startsWith(`${prefix}.`);

/** The scope of a toolkit build, or why it cannot be vouched for by `toolkitSignature`: a module it
 *  reaches outside the signature (the library's `Staging`, a module at the toolkit root), or one
 *  whose source is not found. */
export async function toolkitScope(t: ToolkitLayout): Promise<ToolkitScope | { why: string }> {
  const packages = await pathPackages(t.root);
  if (!packages) return { why: "a path dependency's libraries are not read off its lakefile" };
  const dirOf = new Map<string, string>([[t.lib, t.root]]);
  for (const p of packages) for (const lib of p.libs) if (!dirOf.has(lib)) dirOf.set(lib, p.dir);
  const targets = [...new Set([t.lib, ...packages.filter((p) => !p.inherited).flatMap((p) => p.libs)])];
  const fileOf = (mod: string) => `${path.join(dirOf.get(libOf(dirOf.keys(), mod)!)!, ...mod.split("."))}.lean`;
  const seen = new Set<string>(targets);
  let frontier = [...targets];
  while (frontier.length > 0) {
    const texts = new Array<string | null>(frontier.length);
    let next = 0;
    await Promise.all(Array.from({ length: 16 }, async () => {
      for (let i = next++; i < frontier.length; i = next++) texts[i] = await readFile(fileOf(frontier[i]!), "utf8").catch(() => null);
    }));
    const found: string[] = [];
    for (const [i, mod] of frontier.entries()) {
      if (inDir(mod, `${t.lib}.${t.staging}`)) return { why: `the toolkit's build reaches ${mod}` };
      const text = texts[i];
      if (text == null) return { why: `${path.relative(t.root, fileOf(mod))} (of ${mod}) is not found` };
      for (const imp of headerImports(text)) {
        if (libOf(dirOf.keys(), imp)) { if (!seen.has(imp)) { seen.add(imp); found.push(imp); } }
        else if (atRoot(t.root, imp)) return { why: `${mod} imports ${imp}` };
      }
    }
    frontier = found;
  }
  const outputs = targets.map((lib) => `${path.join(dirOf.get(lib)!, ".lake", "build", "lib", "lean", ...lib.split("."))}.olean`);
  return { targets, libs: [...dirOf.keys()], modules: [...seen].sort(), outputs };
}

/** A read set larger than this is none (`readClosure`): its commit lands only on its base. */
export const READ_CLOSURE_MAX = 2000;

/**
 * The sources a build of `files` reads: they and, transitively, the source of each module they
 * import of the toolkit's library, of its path dependencies' libraries or at the toolkit root (a
 * paper's) — `toolkitScope`'s walk, started from `files` — and every path dependency's lakefile and
 * manifest (its `[leanOptions]` govern how its modules elaborate; 2026-11-11, audit). A module of
 * another package (Mathlib, Lean) is pinned by the manifest: not followed. Null when it cannot be vouched for: a source not
 * found (a paper not copied, a `tmp/` scratch), the library's staging tree, a path dependency's
 * libraries not read off its lakefile, more than `READ_CLOSURE_MAX` files. (2026-11-11: a paper-only
 * commit's read set, `commit.ts`.)
 */
export async function readClosure(t: ToolkitLayout, files: readonly string[]): Promise<string[] | null> {
  const packages = await pathPackages(t.root);
  if (!packages) return null;
  const dirOf = new Map<string, string>([[t.lib, t.root]]);
  for (const p of packages) for (const lib of p.libs) if (!dirOf.has(lib)) dirOf.set(lib, p.dir);
  const fileOf = (mod: string) => { const lib = libOf(dirOf.keys(), mod); return `${path.join(lib ? dirOf.get(lib)! : t.root, ...mod.split("."))}.lean`; };
  const seen = new Set(files.map((f) => path.resolve(f)));
  let frontier = [...seen];
  while (frontier.length > 0) {
    if (seen.size > READ_CLOSURE_MAX) return null;
    const texts = new Array<string | null>(frontier.length);
    let next = 0;
    await Promise.all(Array.from({ length: 16 }, async () => {
      for (let i = next++; i < frontier.length; i = next++) texts[i] = await readFile(frontier[i]!, "utf8").catch(() => null);
    }));
    const found: string[] = [];
    for (const text of texts) {
      if (text == null) return null;
      for (const imp of headerImports(text)) {
        if (inDir(imp, `${t.lib}.${t.staging}`)) return null;
        if (!libOf(dirOf.keys(), imp) && !atRoot(t.root, imp)) continue;
        const f = fileOf(imp);
        if (!seen.has(f)) { seen.add(f); found.push(f); }
      }
    }
    frontier = found;
  }
  for (const p of packages) for (const f of [p.lakefile, path.join(p.dir, "lake-manifest.json")]) if (existsSync(f)) seen.add(f);
  return seen.size > READ_CLOSURE_MAX ? null : [...seen].sort();
}

/** The states (size, mtime, inode) of the path dependencies' sources, lakefiles and manifests, seen
 *  from `root` (a workspace's are live links into the shared ones); null when a package's libraries
 *  cannot be read off its lakefile. Taken before a verdict and after it, the same: nothing of them
 *  changed meanwhile (2026-11-11: a commit's read set, `commit.ts`). */
export async function dependencyStates(root: string): Promise<Map<string, string> | null> {
  const packages = await pathPackages(root);
  const files = await pathDependencySources(root);
  if (!packages || !files) return null;
  return fileStates([...files, ...packages.map((p) => path.join(p.dir, "lake-manifest.json"))]);
}

/** The unit (`Papers.Foo`, or a study's `Toolkit.Staging.Foo`) a module of a paper's or a study's
 *  tree belongs to, or null. */
export function unitOf(t: ToolkitLayout, mod: string): string | null {
  const parts = mod.split(".");
  if (parts[0] === t.papersLib && parts.length >= 2) return parts.slice(0, 2).join(".");
  if (parts[0] === t.lib && parts[1] === t.staging && parts.length >= 3) return parts.slice(0, 3).join(".");
  return null;
}

/** The directory of a unit's modules (`unitOf`). */
const unitDir = (t: ToolkitLayout, unit: string) => {
  const parts = unit.split(".");
  return parts[0] === t.papersLib ? path.join(t.papersDir, parts[1]!) : path.join(t.libDir, t.staging, parts[2]!);
};

/** The units — papers (`Papers.Foo`) and studies' staging trees (`Toolkit.Staging.Foo`) — a build
 *  of `units`' modules, and of `files`, reads modules of: those and every paper a paper imports,
 *  transitively, through the import lines of each unit's `.lean` files (its `tmp/` scratch aside)
 *  and its barrel; and every other module they import. `why` names an import no shared build may
 *  make: another paper's scratch, the papers' barrel, a staging module of another study (or of
 *  any study, from a paper), a paper imported by a study. */
export async function paperImports(t: ToolkitLayout, units: readonly string[], files: readonly string[] = []): Promise<{ papers: string[]; imports: string[]; why: string | null }> {
  const done = new Set<string>();
  const imports = new Set<string>();
  let why: string | null = null;
  const queue = [...units];
  const visit = (text: string, from: string, own: string | null) => {
    for (const imp of headerImports(text)) {
      const unit = unitOf(t, imp);
      if (unit === null) {
        if (imp === t.papersLib || inDir(imp, `${t.lib}.${t.staging}`)) why ??= `${from} imports ${imp}`;
        else imports.add(imp);
        continue;
      }
      // a unit's `tmp/` scratch (its own included) is never read: its imports are unknown
      const depth = unit.split(".").length;
      if (imp.split(".")[depth] === PAPER_TMP_DIR) { why ??= `${from} imports ${imp}`; continue; }
      if (unit === own) continue;
      // another study's staging, or (from a study) a paper: not taken conservatively
      if (depth === 3 || (own !== null && own.split(".").length === 3)) { why ??= `${from} imports ${imp}`; continue; }
      queue.push(unit);
    }
  };
  for (const f of files) {
    const rel = path.relative(t.root, f);
    const own = rel.startsWith("..") ? null : unitOf(t, rel.replace(/\.lean$/, "").split(path.sep).join("."));
    visit(await readFile(f, "utf8").catch(() => ""), rel, own);
  }
  for (let u = queue.shift(); u !== undefined; u = queue.shift()) {
    if (done.has(u)) continue;
    done.add(u);
    const dir = unitDir(t, u);
    const sources: string[] = [];
    await leanFilesUnder(dir, PAPER_TMP_DIR, sources);
    sources.push(`${dir}.lean`);
    for (const f of sources) {
      const text = await readFile(f, "utf8").catch(() => null);
      if (text !== null) visit(text, path.relative(t.root, f), u);
    }
  }
  return { papers: [...done].sort(), imports: [...imports].sort(), why };
}

/** The first of `imports` a build would have to make that `scope` does not vouch for: a module of
 *  the scope's libraries outside its modules (a `Staging` module, one no target imports), or a
 *  module at the toolkit root; null when there is none. */
export function uncoveredImport(t: ToolkitLayout, scope: Pick<ToolkitScope, "libs" | "modules">, imports: Iterable<string>): string | null {
  const modules = new Set(scope.modules);
  for (const imp of imports) {
    if (libOf(scope.libs, imp) ? !modules.has(imp) : atRoot(t.root, imp)) return imp;
  }
  return null;
}

const recordDir = (root: string) => path.join(root, ".lake", "build", "paperformalizer");
const keyOf = (root: string, leanDir: string) => path.relative(root, leanDir).replace(/[^A-Za-z0-9_.-]+/g, "_");
const greenFile = (root: string, leanDir: string) => path.join(recordDir(root), `green_${keyOf(root, leanDir)}.json`);

async function writeJson(file: string, value: unknown): Promise<void> {
  await mkdir(path.dirname(file), { recursive: true });
  const tmp = `${file}.${process.pid}.${randomUUID()}.tmp`;
  await writeFile(tmp, `${JSON.stringify(value)}\n`);
  await rename(tmp, file);
}

/**
 * The signature a record is kept under: in a run's own workspace (`workspace.ts`) the sources'
 * signature with the generation the workspace is pinned to (`@gen<N>`) — what was built there was
 * built against that generation, not the shared toolkit. A shared-tree reader never takes a
 * workspace's record for its own, nor a workspace its record from before a re-pin.
 */
export function recordSig(sig: string): string {
  const ws = leanWorkspaceFor();
  if (!ws || isDoubt(sig)) return sig;
  let gen = "?";
  try { gen = String((JSON.parse(readFileSync(path.join(ws, ".pf-gen"), "utf8")) as { gen?: number }).gen ?? "?"); } catch { /* no pin */ }
  return `${sig}@gen${gen}`;
}

/** Whether `targets` (modules of the paper in `leanDir`) were all built green under `sig`. */
export async function greenBuildCurrent(root: string, leanDir: string, targets: readonly string[], sig: string): Promise<boolean> {
  if (isDoubt(sig) || targets.length === 0) return false;
  sig = recordSig(sig);
  const rec = await readFile(greenFile(root, leanDir), "utf8").then((t) => JSON.parse(t) as { sig?: string; targets?: string[] }).catch(() => null);
  if (!rec || rec.sig !== sig || !Array.isArray(rec.targets)) return false;
  const built = new Set(rec.targets);
  return targets.every((t) => built.has(t));
}

/** On record: `targets` built green from the sources `sig` was taken of before the build. */
export async function recordGreenBuild(root: string, leanDir: string, targets: readonly string[], sig: string): Promise<void> {
  if (isDoubt(sig)) return;
  await writeJson(greenFile(root, leanDir), { sig: recordSig(sig), targets: [...targets].sort(), at: new Date().toISOString() }).catch(() => {});
}

/** A scan's output `out`, with the signature of the sources it was taken from (`sig`): `null`
 *  forgets it (before a new scan overwrites `out`). */
export async function recordScan(out: string, value: { sig: string; modules: readonly string[] } | null): Promise<void> {
  if (value === null || isDoubt(value.sig)) { await unlink(`${out}.sig.json`).catch(() => {}); return; }
  await writeJson(`${out}.sig.json`, { sig: recordSig(value.sig), modules: [...value.modules] }).catch(() => {});
}

/** Whether the scan output `out` was taken of these modules from sources with signature `sig`. */
export async function scanCurrent(out: string, modules: readonly string[], sig: string): Promise<boolean> {
  if (isDoubt(sig) || !existsSync(out)) return false;
  const rec = await readFile(`${out}.sig.json`, "utf8").then((t) => JSON.parse(t) as { sig?: string; modules?: string[] }).catch(() => null);
  return rec?.sig === recordSig(sig) && JSON.stringify(rec.modules) === JSON.stringify([...modules]);
}
