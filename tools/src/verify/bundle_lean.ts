/**
 * The standalone Lake project of the V6 bundle (`bundle/lean/`): what a third person builds.
 *
 * The bundle may depend only on the public base libraries — Mathlib and the catalogued domain
 * libraries (`tools/data/libraries.json`) — each required in its PUBLIC form (git url + rev); a
 * catalogued library with no public form (a `path` under `third_party/`) is vendored into
 * `vendor/<name>/`. Everything of the owner's personal toolkit the paper uses is copied in.
 *
 * Pure helpers and two checks, all without `lake` or the network:
 *   - `checkSelfContained`: every import of every file resolves inside the bundle or to a required
 *     base library, no lakefile path leaves the bundle, nothing names the owner's machine;
 *   - `compareLocal`: the owner built against a LOCAL checkout of a base library; the files the
 *     paper reaches there are recorded by content hash, and compared with the public revision the
 *     bundle requires when that is at hand (in the local repository, or over the network on
 *     request). Read-only git on that checkout.
 */
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, readFileSync } from "node:fs";
import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import type { Catalog } from "../toolkit/init.js";

export const MATHLIB_GIT = "https://github.com/leanprover-community/mathlib4";
/** Module roots that come with the toolchain. */
const CORE_ROOTS = ["Init", "Std", "Lean", "Lake"] as const;
/** Module roots Mathlib brings in (itself and its own dependencies). */
const MATHLIB_ROOTS = ["Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible", "LeanSearchClient", "ImportGraph", "Cli"] as const;

/** A Lean file's header: whether it is a `module`, and the modules it imports. Only the header is
 * read (comments skipped, up to the first command), so an `import` inside a docstring is not one. */
export function leanHeader(text: string): { module: boolean; imports: string[] } {
  const imports: string[] = [];
  let module = false;
  let i = 0;
  const kw = /(module|prelude)(?=\s|$)/y;
  const imp = /(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)/y;
  for (;;) {
    while (i < text.length && /\s/u.test(text[i]!)) i += 1;
    if (text.startsWith("--", i)) {
      const e = text.indexOf("\n", i);
      i = e < 0 ? text.length : e + 1;
    } else if (text.startsWith("/-", i) && !text.startsWith("/--", i) && !text.startsWith("/-!", i)) {
      let depth = 1;
      i += 2;
      while (i < text.length && depth > 0) {
        if (text.startsWith("/-", i)) { depth += 1; i += 2; } else if (text.startsWith("-/", i)) { depth -= 1; i += 2; } else i += 1;
      }
    } else {
      kw.lastIndex = i;
      imp.lastIndex = i;
      const k = kw.exec(text);
      const m = k ? null : imp.exec(text);
      if (k) { module = module || k[1] === "module"; i = kw.lastIndex; } else if (m) { imports.push(m[1]!.replace(/[«»]/gu, "")); i = imp.lastIndex; } else break;
    }
  }
  return { module, imports };
}

export interface TomlTable {
  /** `""` for the keys before the first table header. */
  name: string;
  array: boolean;
  /** Its lines, comments stripped, header excluded. */
  lines: string[];
}

/** The tables of a `lakefile.toml`, in order (enough TOML for a lakefile: one key per line). */
export function tomlTables(text: string): TomlTable[] {
  const out: TomlTable[] = [{ name: "", array: false, lines: [] }];
  for (const raw of text.split(/\r?\n/u)) {
    const line = raw.replace(/(^|\s)#.*$/u, "").trimEnd();
    if (line.trim() === "") continue;
    const h = /^\s*(\[\[?)\s*([A-Za-z0-9_.]+)\s*\]\]?\s*$/u.exec(line);
    if (h) out.push({ name: h[2]!, array: h[1] === "[[", lines: [] });
    else out[out.length - 1]!.lines.push(line);
  }
  return out;
}

export const tomlString = (t: TomlTable, key: string): string | undefined => {
  for (const l of t.lines) {
    const m = new RegExp(`^\\s*${key}\\s*=\\s*"([^"]*)"\\s*$`, "u").exec(l);
    if (m) return m[1];
  }
  return undefined;
};

/** What the toolkit's lakefile requires, by package name. */
export interface ToolkitRequire { name: string; path?: string; git?: string; rev?: string }
export function toolkitRequires(lakefileToml: string | null): Map<string, ToolkitRequire> {
  const out = new Map<string, ToolkitRequire>();
  for (const t of lakefileToml ? tomlTables(lakefileToml) : []) {
    const name = t.name === "require" ? tomlString(t, "name") : undefined;
    if (!name) continue;
    const r: ToolkitRequire = { name };
    for (const k of ["path", "git", "rev"] as const) {
      const v = tomlString(t, k);
      if (v !== undefined) r[k] = v;
    }
    out.set(name, r);
  }
  return out;
}

/** One base library the bundle requires. */
export interface BundleRequire {
  name: string;
  /** Its root module. */
  lib: string;
  form: "git" | "vendored";
  git?: string;
  rev?: string;
  /** `vendor/<name>` (vendored). */
  path?: string;
  /** Vendored: the directory it is copied from. */
  source?: string;
  /** Git: the catalogue's pin, when `rev` is the toolkit's own (older or newer). */
  catalogRev?: string;
  /** Git: `rev` is the commit the toolkit built on, not the catalogue's. */
  fromToolkit?: true;
  /** Root modules it also brings in (libraries it provides). */
  provides: string[];
  summary: string;
}

/**
 * The base libraries the copied code needs, from the roots of its external imports: each catalogued
 * library whose root module is imported, in its public form — git url + rev, or vendored when the
 * catalogue gives only a path. A library another needed one provides is not required beside it;
 * one the toolkit does not require itself but gets through a library that provides it is required
 * through that library (what the owner built against). Mathlib is last, always. A library the
 * toolkit requires from the catalogue's repository is pinned where the toolkit built on it: the
 * commit its `lake-manifest.json` resolved (`manifest`, name → rev), else its lakefile's `rev` when
 * that is a commit (a branch moves), else the catalogue's; `catalogRev` keeps the catalogue's pin for
 * the reminder that a newer one exists. Pins are one set: when one comes from the toolkit, Mathlib
 * is the manifest's too (`fromToolkit` on the libraries so pinned) — the catalogue's Mathlib under an
 * older library is a pair nobody built.
 */
export function planRequires(a: { catalog: Catalog; roots: Iterable<string>; toolkit: Map<string, ToolkitRequire>; toolkitRoot: string; libraryRoot: string; manifest?: ReadonlyMap<string, string> }): BundleRequire[] {
  const c = a.catalog;
  const byLib = new Map(Object.entries(c.libraries).map(([name, l]) => [l.lib, name] as const));
  const needed = new Set<string>();
  for (const r of a.roots) {
    const name = byLib.get(r);
    if (!name) continue;
    const through = a.toolkit.has(name) ? undefined : Object.keys(c.libraries).find((p) => a.toolkit.has(p) && (c.libraries[p]!.provides ?? []).includes(name));
    needed.add(through ?? name);
  }
  const provided = new Set([...needed].flatMap((n) => c.libraries[n]!.provides ?? []));
  const out: BundleRequire[] = [...needed].filter((n) => !provided.has(n)).sort().map((name) => {
    const l = c.libraries[name]!;
    const provides = (l.provides ?? []).map((p) => c.libraries[p]?.lib ?? p);
    if ("git" in l.require) {
      const own = a.toolkit.get(name);
      const built = own?.git && sameRepo(own.git, l.require.git) ? [a.manifest?.get(name), own.rev].find((r) => r !== undefined && COMMIT.test(r)) : undefined;
      return { name, lib: l.lib, form: "git", git: l.require.git, rev: built ?? l.require.rev, catalogRev: l.require.rev, ...(built ? { fromToolkit: true as const } : {}), provides, summary: l.summary };
    }
    const own = a.toolkit.get(name)?.path;
    return { name, lib: l.lib, form: "vendored", path: `vendor/${name}`, source: own ? path.resolve(a.toolkitRoot, own) : path.join(a.libraryRoot, l.require.path), provides, summary: l.summary };
  });
  const ownMathlib = a.manifest?.get("mathlib");
  const mathlib = out.some((r) => r.fromToolkit) && ownMathlib && COMMIT.test(ownMathlib) ? ownMathlib : c.mathlib_rev;
  out.push({ name: "mathlib", lib: "Mathlib", form: "git", git: MATHLIB_GIT, rev: mathlib, provides: [], summary: "the Lean mathematical library" });
  return out;
}

/** A git commit (a pin that does not move), not a branch or tag. */
const COMMIT = /^[0-9a-f]{40}$/u;

/** Whether two git addresses name one repository (`.git` and a trailing slash aside). */
const sameRepo = (x: string, y: string): boolean => {
  const norm = (u: string) => u.trim().toLowerCase().replace(/\/+$/u, "").replace(/\.git$/u, "");
  return norm(x) === norm(y);
};

/** The module roots a required library answers for. */
export function allowedRoots(requires: readonly BundleRequire[]): Set<string> {
  return new Set<string>([...CORE_ROOTS, ...MATHLIB_ROOTS, ...requires.flatMap((r) => [r.lib, ...r.provides])]);
}

const DEFAULT_OPTIONS = ["pp.unicode.fun = true", "relaxedAutoImplicit = false", "weak.linter.mathlibStandardSet = true", "maxSynthPendingDepth = 3"];

/**
 * The bundle's `lakefile.toml`: the libraries of the copied code and the requires, nothing else —
 * no executable, no index. The Lean options and each library's table are the toolkit's own (read
 * from its `lakefile.toml`; the template's when it has none).
 */
export function renderLakefile(a: { name: string; libs: readonly string[]; requires: readonly BundleRequire[]; toolkitLakefile: string | null }): string {
  const tables = a.toolkitLakefile ? tomlTables(a.toolkitLakefile) : [];
  const options = tables.find((t) => t.name === "leanOptions")?.lines.map((l) => l.trim()) ?? DEFAULT_OPTIONS;
  const L = [
    `name = "${a.name}"`,
    `defaultTargets = [${a.libs.map((l) => `"${l}"`).join(", ")}]`,
    "",
    "# Generated by LeanSmith: a standalone project. It requires the public base libraries",
    "# only; everything else it uses is in this directory. Mathlib stays the last require.",
    "",
    "[leanOptions]",
    ...options,
    "",
  ];
  for (const r of a.requires) {
    L.push(`# ${r.summary}`, "[[require]]", `name = "${r.name}"`, ...(r.form === "git" ? [`git = "${r.git}"`, `rev = "${r.rev}"`] : [`path = "${r.path}"`]), "");
  }
  for (const lib of a.libs) {
    const own = tables.find((t) => t.name === "lean_lib" && tomlString(t, "name") === lib);
    L.push("[[lean_lib]]", ...(own ? own.lines.map((l) => l.trim()) : [`name = "${lib}"`]), "");
  }
  return L.join("\n");
}

/** A library's root module: imports `modules`, as a `module` when every one of them is. */
export function rootModule(modules: ReadonlyArray<{ name: string; module: boolean }>): string {
  const mod = modules.length > 0 && modules.every((m) => m.module);
  return `${mod ? "module\n\n" : ""}${modules.map((m) => `${mod ? "public " : ""}import ${m.name}`).join("\n")}\n`;
}

async function walkFiles(dir: string, rel = ""): Promise<string[]> {
  const out: string[] = [];
  for (const e of (await readdir(path.join(dir, rel), { withFileTypes: true })).sort((x, y) => x.name.localeCompare(y.name))) {
    const r = rel ? `${rel}/${e.name}` : e.name;
    if (e.isDirectory()) out.push(...(await walkFiles(dir, r)));
    else if (e.isFile()) out.push(r);
  }
  return out;
}

const modFile = (m: string): string => `${m.split(".").join("/")}.lean`;

/**
 * The self-containment check of a written `lean/`: what keeps a third person from building it
 * with nothing but this directory and the public libraries (empty when nothing does).
 */
export async function checkSelfContained(a: { leanDir: string; requires: readonly BundleRequire[]; forbidden: readonly string[] }): Promise<string[]> {
  const problems: string[] = [];
  const files = await walkFiles(a.leanDir);
  const bases = ["", ...a.requires.filter((r) => r.form === "vendored").map((r) => `${r.path}/`)];
  const have = new Set(files);
  const allowed = allowedRoots(a.requires.filter((r) => r.form === "git"));
  const forbidden = [...new Set(a.forbidden.filter((f) => f.length > 1))];
  const unresolved = new Map<string, string>();
  for (const f of files) {
    const text = await readFile(path.join(a.leanDir, f), "utf8");
    for (const s of forbidden) if (text.includes(s)) problems.push(`\`${f}\` names a path of the machine it was built on (\`${s}\`)`);
    const base = path.posix.basename(f);
    if (base === "lakefile.toml" || base === "lakefile.lean") {
      const code = text.split(/\r?\n/u).map((l) => l.replace(base.endsWith(".toml") ? /(^|\s)#.*$/u : /--.*$/u, "")).join("\n");
      for (const m of code.matchAll(/"([^"\n]*)"/gu)) {
        const v = m[1]!;
        if (v.startsWith("/") || v.startsWith("~") || /^[A-Za-z]:\\/u.test(v) || v.split("/").includes("..")) problems.push(`\`${f}\` refers to a path outside the bundle (\`${v}\`)`);
      }
    }
    if (!f.endsWith(".lean")) continue;
    for (const m of leanHeader(text).imports) {
      if (allowed.has(m.split(".")[0]!) || bases.some((b) => have.has(b + modFile(m)))) continue;
      if (!unresolved.has(m)) unresolved.set(m, f);
    }
  }
  for (const [m, f] of unresolved) problems.push(`\`${f}\` imports \`${m}\`, which is neither a file of the bundle nor a module of a library it requires`);
  for (const r of a.requires) {
    if (r.form === "vendored" && !files.some((f) => f.startsWith(`${r.path}/`) && /^(LICEN[CS]E|NOTICE|COPYING)/iu.test(f.slice(r.path!.length + 1)))) problems.push(`\`${r.path}\` (${r.name}) carries no licence or NOTICE file`);
  }
  return problems;
}

/** A base library as the owner built against it, beside the public revision the bundle requires. */
export interface LocalCompare {
  name: string;
  public_git: string;
  public_rev: string;
  /** HEAD of the local checkout, when it is one. The local repository may be another one than the
   * public (an internal repository, a restarted history): the hashes are never compared. */
  local_rev: string | null;
  /** Files reached that differ from the local HEAD (uncommitted or untracked). */
  uncommitted: number;
  /** Built against: each file of the library the paper reaches, with its git blob hash. */
  files: Record<string, string>;
  /** `same`: every file reached has the content it has at the public revision. `differs`: some do
   * not (blocking). `unverified`: not compared — the public revision is not at hand offline. */
  status: "same" | "differs" | "unverified";
  /** Files reached whose content is not the public revision's (first few). */
  changed: string[];
  detail: string;
}

export type Git = (dir: string, args: string[]) => { ok: boolean; out: string };
/** Read-only git (never takes the index lock, so `status`/`diff` write nothing in the checkout). */
export const readOnlyGit: Git = (dir, args) => {
  const r = spawnSync("git", ["-C", dir, ...args], { encoding: "utf8", maxBuffer: 256 * 1024 * 1024, env: { ...process.env, GIT_OPTIONAL_LOCKS: "0" } });
  return { ok: r.status === 0, out: (r.stdout ?? "").trim() };
};

/** The files of the package at `pkg` (and of the packages its lakefile requires by path) that the
 * modules `imports` reach, relative to `pkg`. */
export function reachedFiles(pkg: string, imports: Iterable<string>): string[] {
  const toml = path.join(pkg, "lakefile.toml");
  const dirs = [pkg, ...(existsSync(toml) ? [...toolkitRequires(readFileSync(toml, "utf8")).values()].flatMap((r) => (r.path ? [path.resolve(pkg, r.path)] : [])) : [])];
  const seen = new Set<string>();
  const out: string[] = [];
  const queue = [...imports];
  while (queue.length > 0) {
    const m = queue.pop()!;
    if (seen.has(m)) continue;
    seen.add(m);
    const file = dirs.map((d) => path.join(d, modFile(m))).find((f) => existsSync(f));
    if (!file) continue;
    out.push(path.relative(pkg, file).split(path.sep).join("/"));
    queue.push(...leanHeader(readFileSync(file, "utf8")).imports);
  }
  return out.sort();
}

/** The git blob hash of a file's content (what `git hash-object` prints). */
export function blobHash(content: Buffer): string {
  return createHash("sha1").update(`blob ${content.length}\0`).update(content).digest("hex");
}

/** The blob hash of each file at a revision of the public repository (at least those under the
 * directories of `paths`); `partial` when the listing is known to be incomplete. Null when it could
 * not be had. */
export type PublicTree = (git: string, rev: string, paths: readonly string[]) => Promise<{ files: Map<string, string>; partial: boolean } | null>;

type TreeJson = { tree?: Array<{ path: string; type: string; sha: string }>; truncated?: boolean };
/**
 * `PublicTree` over the GitHub API (no clone); other hosts: null. One recursive listing when the
 * repository is small enough; where GitHub truncates it, the subtrees leading to `paths` instead.
 */
export function githubTree(get: (url: string) => Promise<TreeJson | null> = githubJson): PublicTree {
  return async (git, rev, paths) => {
    const m = /^https:\/\/github\.com\/([^/]+)\/([^/]+?)(?:\.git)?\/?$/u.exec(git);
    if (!m) return null;
    const files = new Map<string, string>();
    let partial = false;
    const load = async (sha: string, prefix: string): Promise<boolean> => {
      const url = `https://api.github.com/repos/${m[1]}/${m[2]}/git/trees/${sha}`;
      const all = await get(`${url}?recursive=1`);
      if (!all) return false;
      if (!all.truncated) {
        for (const e of all.tree ?? []) if (e.type === "blob") files.set(prefix + e.path, e.sha);
        return true;
      }
      const one = await get(url);
      if (!one) return false;
      if (one.truncated) partial = true;
      for (const e of one.tree ?? []) {
        if (e.type === "blob") files.set(prefix + e.path, e.sha);
        else if (e.type === "tree" && paths.some((p) => p.startsWith(`${prefix}${e.path}/`)) && !(await load(e.sha, `${prefix}${e.path}/`))) return false;
      }
      return true;
    };
    return (await load(rev, "")) ? { files, partial } : null;
  };
}

async function githubJson(url: string): Promise<TreeJson | null> {
  try {
    const token = process.env.GITHUB_TOKEN;
    const res = await fetch(url, { headers: { accept: "application/vnd.github+json", "user-agent": "leansmith", ...(token ? { authorization: `Bearer ${token}` } : {}) } });
    return res.ok ? ((await res.json()) as TreeJson) : null;
  } catch {
    return null;
  }
}

const lsTree = (git: Git, dir: string, rev: string): Map<string, string> | null => {
  const r = git(dir, ["ls-tree", "-r", rev, "--", "."]);
  if (!r.ok) return null;
  return new Map(r.out.split("\n").flatMap((l) => { const m = /^\S+ blob (\S+)\t(.*)$/u.exec(l); return m ? [[m[2]!, m[1]!] as const] : []; }));
};

const short = (rev: string): string => rev.slice(0, 12);

/**
 * What the paper was built against in the local checkout `dir` of the library `r` — the files it
 * reaches there, by content hash, and the checkout's HEAD — and whether that content is the public
 * revision's. Commit hashes are not compared (the local repository need not be the public one).
 * Offline the content is compared only when the public revision is an object of the local
 * repository; `publicTree` (the network) compares it otherwise. Not compared is `unverified`.
 */
export async function compareLocal(r: BundleRequire, dir: string | null, imports: Iterable<string>, o: { git?: Git; publicTree?: PublicTree | undefined; verifyCommand?: string | undefined } = {}): Promise<LocalCompare> {
  const git = o.git ?? readOnlyGit;
  const base = { name: r.name, public_git: r.git!, public_rev: r.rev!, uncommitted: 0, changed: [] as string[] };
  const how = `${o.verifyCommand ? `\`${o.verifyCommand}\` compares them over the network; by hand: ` : ""}\`git hash-object <file>\` in the local checkout against the blob hashes of \`${r.git}\` at \`${r.rev}\``;
  if (!dir || !existsSync(dir)) return { ...base, local_rev: null, files: {}, status: "unverified", detail: `the local copy of ${r.name} this development was built against was not found, so what was built against is not recorded and was not compared with the public revision ${short(r.rev!)} this bundle requires` };
  const files: Record<string, string> = {};
  for (const f of reachedFiles(dir, imports)) files[f] = blobHash(readFileSync(path.join(dir, f)));
  const n = Object.keys(files).length;
  const head = git(dir, ["rev-parse", "HEAD"]);
  const local = head.ok ? head.out : null;
  const atHead = local ? lsTree(git, dir, "HEAD") : null;
  const uncommitted = atHead ? Object.entries(files).filter(([f, h]) => atHead.get(f) !== h).length : 0;
  const built = `built against a local copy of ${r.name}${local ? ` (its commit ${short(local)}${uncommitted > 0 ? `, with ${uncommitted} of the files reached changed since` : ""})` : ""}: ${n} file(s) of it are reached, recorded by content hash in \`built-against.json\``;
  const offline = git(dir, ["cat-file", "-e", `${r.rev}^{commit}`]).ok ? lsTree(git, dir, r.rev!) : null;
  const pub = offline ? { files: offline, partial: false } : o.publicTree ? await o.publicTree(r.git!, r.rev!, Object.keys(files)) : null;
  if (!pub) return { ...base, local_rev: local, uncommitted, files, status: "unverified", detail: `${built}. That they are the files of the public revision ${short(r.rev!)} this bundle requires was NOT verified${o.publicTree ? " (the public revision could not be read)" : " (not possible offline)"}: ${how}` };
  const changed = Object.entries(files).filter(([f, h]) => pub.files.get(f) !== h).map(([f]) => f);
  const missing = changed.filter((f) => !pub.files.has(f));
  if (changed.length > 0 && pub.partial && missing.length === changed.length) return { ...base, local_rev: local, uncommitted, files, status: "unverified", detail: `${built}. The listing of the public revision ${short(r.rev!)} was incomplete, so ${missing.length} file(s) were not compared: ${how}` };
  if (changed.length > 0) return { ...base, local_rev: local, uncommitted, files, status: "differs", changed: changed.slice(0, 20), detail: `${built}. ${changed.length} of them differ from the public revision ${short(r.rev!)} this bundle requires (${changed.slice(0, 5).join(", ")}${changed.length > 5 ? ", …" : ""}), so the build of this directory could differ from the one made here` };
  return { ...base, local_rev: local, uncommitted, files, status: "same", detail: `${built}. Each has the content it has at the public revision ${short(r.rev!)} this bundle requires (compared ${offline ? "in the local repository" : "over the network"})` };
}
