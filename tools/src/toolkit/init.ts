// `theoremchecker init <dir>`: create a personal toolkit — a copy of `templates/toolkit/`, the domain
// libraries the user picks from TheoremChecker's catalog (`tools/data/libraries.json`: one pinned
// Lean toolchain and Mathlib, and per library a source that builds against them), a git repository,
// and unless `--no-build` Mathlib's cache, each chosen library's own prebuilt cache, a build, and an
// index of each library that ships none.
import { spawnSync } from "node:child_process";
import { cpSync, existsSync, readFileSync, readdirSync, renameSync, writeFileSync } from "node:fs";
import path from "node:path";
import { createInterface } from "node:readline/promises";
import { z } from "zod";
import { TOOLKIT_CONFIG_FILE } from "./config.js";
import { toolkitTemplateDir } from "./lakefile.js";
import { bashBinary } from "../local_config.js";

const LibrarySchema = z.object({
  summary: z.string(),
  require: z.union([z.object({ git: z.string(), rev: z.string() }), z.object({ path: z.string() })]),
  /** The library's root module (what an index walks). */
  lib: z.string(),
  /** Libraries this one already brings in (its own dependencies): never required beside it. */
  provides: z.array(z.string()).optional(),
  /** Its declaration index, relative to the package root, when it ships one. */
  index: z.string().optional(),
  /** Retrieval synonyms and prompt notes, relative to the TheoremChecker repository. */
  alias_file: z.string().optional(),
  prompt_notes: z.string().optional(),
  /** The script (and its arguments), relative to the package root, that downloads the library's
   *  compiled files, when it publishes them: run before the first build, which then only replays. */
  fetch_cache: z.string().optional(),
  /** Set while a toolkit cannot use it (no source on the pinned Mathlib, or not yet a module library): why. */
  unavailable: z.string().optional(),
});

const CatalogSchema = z.object({
  lean_toolchain: z.string(),
  mathlib_rev: z.string(),
  domains: z.array(z.object({ id: z.string(), label: z.string(), libraries: z.array(z.string()) })),
  libraries: z.record(LibrarySchema),
});
export type Catalog = z.infer<typeof CatalogSchema>;
type Library = z.infer<typeof LibrarySchema>;

/** The TheoremChecker repository root (the template's grandparent). */
export function repoRoot(): string {
  return path.resolve(toolkitTemplateDir(), "..", "..");
}

export function loadCatalog(file = path.join(repoRoot(), "tools", "data", "libraries.json")): Catalog {
  const c = CatalogSchema.parse(JSON.parse(readFileSync(file, "utf8")));
  for (const d of c.domains) {
    for (const l of d.libraries) if (!c.libraries[l]) throw new Error(`library catalog: domain ${d.id} names unknown library ${l}`);
  }
  return c;
}

/** The libraries the domains call for, plus those `named` directly: each once, none another selected one already provides, and
 * none the catalog marks unavailable (returned in `skipped` with the reason). */
export function librariesFor(
  c: Catalog,
  domainIds: readonly string[],
  named: readonly string[] = [],
): { libs: string[]; skipped: Array<{ name: string; why: string }> } {
  const wanted: string[] = [];
  for (const id of domainIds) {
    const d = c.domains.find((x) => x.id === id);
    if (!d) throw new Error(`unknown domain "${id}" (one of: ${c.domains.map((x) => x.id).join(", ")})`);
    for (const l of d.libraries) if (!wanted.includes(l)) wanted.push(l);
  }
  for (const l of named) {
    if (!c.libraries[l]) throw new Error(`unknown library "${l}" (one of: ${Object.keys(c.libraries).join(", ")})`);
    if (!wanted.includes(l)) wanted.push(l);
  }
  const skipped = wanted.filter((l) => c.libraries[l]!.unavailable).map((name) => ({ name, why: c.libraries[name]!.unavailable! }));
  const available = wanted.filter((l) => !c.libraries[l]!.unavailable);
  const provided = new Set(available.flatMap((l) => c.libraries[l]!.provides ?? []));
  return { libs: available.filter((l) => !provided.has(l)), skipped };
}

const rel = (from: string, to: string): string => path.relative(from, to).split(path.sep).join("/") || ".";

/** Where a library's package sits, relative to the toolkit root. */
function packageRoot(name: string, lib: Library, toolkit: string): string {
  return "git" in lib.require ? `.lake/packages/${name}` : rel(toolkit, path.join(repoRoot(), lib.require.path));
}

/** The `[[require]]` blocks for the domain-libraries region of the toolkit lakefile. */
export function lakefileRequires(c: Catalog, libs: readonly string[], toolkit: string): string {
  return libs
    .map((name) => {
      const lib = c.libraries[name]!;
      const src = "git" in lib.require
        ? `git = "${lib.require.git}"\nrev = "${lib.require.rev}"`
        : `path = ${JSON.stringify(packageRoot(name, lib, toolkit))}`;
      return `# ${lib.summary}\n[[require]]\nname = "${name}"\n${src}\n`;
    })
    .join("\n");
}

/** The index a toolkit generates for a library that ships none (`init` writes it after the build). */
export const generatedIndex = (name: string): string => `doc/base_index/${name}.json`;

/** The `base` entries of `theoremchecker.json`: Mathlib, then each domain library. */
export function baseEntries(c: Catalog, libs: readonly string[], toolkit: string): Array<Record<string, unknown>> {
  return [
    { name: "Mathlib", kind: "transitive", search: ["loogle", "leansearch"], summary: "the Lean mathematical library" },
    ...libs.map((name) => {
      const lib = c.libraries[name]!;
      const root = packageRoot(name, lib, toolkit);
      return {
        name,
        kind: "path",
        path: root,
        summary: lib.summary,
        index: lib.index ? path.posix.join(root, lib.index) : generatedIndex(name),
        ...(lib.alias_file ? { alias_file: rel(toolkit, path.join(repoRoot(), lib.alias_file)) } : {}),
        ...(lib.prompt_notes ? { prompt_notes: rel(toolkit, path.join(repoRoot(), lib.prompt_notes)) } : {}),
      };
    }),
  ];
}

/** For each chosen library that publishes its compiled files: where to run its fetch script, and
 *  the script with its arguments. Pure. */
export function cacheFetches(c: Catalog, libs: readonly string[], toolkit: string): Array<{ name: string; cwd: string; argv: string[] }> {
  return libs.flatMap((name) => {
    const lib = c.libraries[name]!;
    return lib.fetch_cache ? [{ name, cwd: path.resolve(toolkit, packageRoot(name, lib, toolkit)), argv: lib.fetch_cache.split(/\s+/) }] : [];
  });
}

const BEGIN = "# BEGIN domain libraries\n";
const END = "# END domain libraries\n";

/** Render the template independently of the checkout's line endings. */
export function renderToolkitLakefile(template: string, c: Catalog, libs: readonly string[], toolkit: string): string {
  const lf = template.replace(/\r\n/g, "\n");
  const at = lf.indexOf(BEGIN);
  if (at < 0 || lf.indexOf(END, at) < 0) throw new Error(`template ${path.join(toolkit, "lakefile.toml")} lacks the domain-libraries markers`);
  const tail = lf.slice(lf.indexOf(END, at)).replace(/^rev = "[0-9a-f]{40}"$/m, () => `rev = "${c.mathlib_rev}"`);
  return lf.slice(0, at + BEGIN.length) + lakefileRequires(c, libs, toolkit) + tail;
}

export interface InitOptions {
  dir: string;
  domains: string[];
  /** Libraries chosen by name, beside the domains'. */
  libraries?: string[];
  owner: { name: string; email?: string };
  build: boolean;
  log?: (line: string) => void;
}

/** Create the toolkit at `dir` (absent or empty). Returns the libraries required and those skipped. */
export function initToolkit(o: InitOptions, c: Catalog = loadCatalog()): ReturnType<typeof librariesFor> {
  const log = o.log ?? ((l: string) => console.log(l));
  const dir = path.resolve(o.dir);
  if (existsSync(dir) && readdirSync(dir).length > 0) throw new Error(`${dir} exists and is not empty; init creates a new toolkit`);
  const sel = librariesFor(c, o.domains, o.libraries ?? []);
  for (const s of sel.skipped) log(`[init] ${s.name} skipped: ${s.why}`);

  cpSync(toolkitTemplateDir(), dir, { recursive: true });
  renameSync(path.join(dir, `${TOOLKIT_CONFIG_FILE}.example`), path.join(dir, TOOLKIT_CONFIG_FILE));
  writeFileSync(path.join(dir, "lean-toolchain"), `${c.lean_toolchain}\n`);
  const lakefile = path.join(dir, "lakefile.toml");
  writeFileSync(lakefile, renderToolkitLakefile(readFileSync(lakefile, "utf8"), c, sel.libs, dir));
  const cfgPath = path.join(dir, TOOLKIT_CONFIG_FILE);
  const cfg = JSON.parse(readFileSync(cfgPath, "utf8")) as Record<string, unknown>;
  cfg.owner = { name: o.owner.name, ...(o.owner.email ? { email: o.owner.email } : {}) };
  cfg.base = baseEntries(c, sel.libs, dir);
  cfg.lean = { toolchain: c.lean_toolchain };
  writeFileSync(cfgPath, `${JSON.stringify(cfg, null, 2)}\n`);
  log(`[init] toolkit at ${dir}: Mathlib ${c.mathlib_rev.slice(0, 7)}${sel.libs.length ? ` + ${sel.libs.join(", ")}` : ""}`);

  // The index executables record the toolkit's commit: it is a git repository from the start.
  const git = (...args: string[]) => spawnSync("git", args, { cwd: dir, encoding: "utf8" });
  if (git("init", "-q").status !== 0) throw new Error(`git init failed in ${dir}`);
  git("add", "-A");
  // (the owner given is the first commit's author, whatever this machine's git identity is)
  const as = ["-c", `user.name=${o.owner.name}`, ...(o.owner.email ? ["-c", `user.email=${o.owner.email}`] : [])];
  if (git(...as, "commit", "-q", "-m", "TheoremChecker toolkit").status !== 0) {
    log("[init] git commit failed (set git user.name / user.email, then commit the toolkit yourself)");
  }

  if (o.build) {
    const lake = (...args: string[]): void => {
      log(`[init] lake ${args.join(" ")}`);
      const r = spawnSync("lake", args, { cwd: dir, stdio: "inherit" });
      if (r.status !== 0) throw new Error(`lake ${args.join(" ")} failed in ${dir}; fix it and re-run the remaining steps by hand (README "Install")`);
    };
    lake("exe", "cache", "get");
    const fetched: string[] = [];
    // A library's own compiled files, when it publishes them (the dependencies are on disk now).
    // Without them Lake compiles the library from source: slower, never wrong — so a failed
    // download is said and passed over.
    for (const f of cacheFetches(c, sel.libs, dir)) {
      log(`[init] ${f.name}: fetching its prebuilt cache (bash ${f.argv.join(" ")})`);
      if (spawnSync(bashBinary(), f.argv, { cwd: f.cwd, stdio: "inherit" }).status !== 0) {
        log(`[init] ${f.name}: no prebuilt cache fetched — Lake will compile it from source (long). To try again: (cd ${f.cwd} && bash ${f.argv.join(" ")})`);
      } else fetched.push(f.name);
    }
    lake("build");
    // A fetched cache is checked now, while the user is installing: the library's build must only replay.
    for (const name of fetched) {
      const target = c.libraries[name]!.lib;
      log(`[init] lake build ${target} (checking the fetched cache)`);
      const r = spawnSync("lake", ["build", target], { cwd: dir, encoding: "utf8", maxBuffer: 1 << 30 });
      const count = (re: RegExp): number => (`${r.stdout}${r.stderr}`.match(re) ?? []).length;
      if (r.status !== 0) throw new Error(`lake build ${target} failed in ${dir}; fix it and re-run the remaining steps by hand (README "Install")`);
      log(`[init] ${name}: ${count(/^. \[\d+\/\d+\] Replayed /gm)} replayed, ${count(new RegExp(`^. \\[\\d+\\/\\d+\\] Built ${target}[. ]`, "gm"))} compiled`);
    }
    for (const name of sel.libs) {
      const lib = c.libraries[name]!;
      if (lib.index) { log(`[init] ${name}: ships its index`); continue; }
      lake("build", lib.lib);
      lake("exe", "toolkit_index", "--", "--lib", lib.lib, "--src-root", packageRoot(name, lib, dir), "--out", generatedIndex(name));
    }
  }
  return sel;
}

/** A domain's libraries as the user is shown them: one not yet available says so. */
const domainLibraries = (c: Catalog, libs: readonly string[]): string =>
  libs.map((l) => (c.libraries[l]!.unavailable ? `${l} (not yet available)` : l)).join(", ");

/** The domains and libraries on offer, for `--list` and for an agent asking the user. */
export function catalogListing(c: Catalog): string {
  return [
    `Domains (--domains), each installing the optional libraries listed:`,
    ...c.domains.map((d) => `  ${d.id.padEnd(13)} ${d.label}${d.libraries.length ? ` — ${domainLibraries(c, d.libraries)}` : ""}`),
    `Libraries (--libraries), all optional, all on Lean ${c.lean_toolchain.split(":")[1]} / Mathlib ${c.mathlib_rev.slice(0, 7)}:`,
    ...Object.entries(c.libraries).map(([n, l]) => `  ${n.padEnd(13)} ${l.summary}${l.unavailable ? ` [not yet available: ${l.unavailable}]` : ""}`),
  ].join("\n");
}

/** Ask for the domains on a terminal: numbered list, comma-separated answer. */
async function askDomains(c: Catalog): Promise<string[]> {
  const rl = createInterface({ input: process.stdin, output: process.stdout });
  try {
    console.log("Which domains will this toolkit mainly work on? (comma-separated numbers)");
    c.domains.forEach((d, i) => {
      const libs = domainLibraries(c, d.libraries);
      console.log(`  ${i + 1}. ${d.label}${libs ? ` — ${libs}` : ""}`);
    });
    const answer = await rl.question("> ");
    const picked = answer.split(",").map((s) => Number(s.trim())).filter((n) => Number.isInteger(n) && n >= 1 && n <= c.domains.length);
    if (picked.length === 0) throw new Error("no domain chosen");
    return [...new Set(picked.map((n) => c.domains[n - 1]!.id))];
  } finally {
    rl.close();
  }
}

export const INIT_USAGE =
  "Usage: theoremchecker init <dir> [--domains id,id] [--libraries name,name] [--owner \"Name\"] [--email e] [--no-build]\n" +
  "  creates a personal toolkit at <dir>: the template, the optional domain libraries (asked for on a terminal\n" +
  "  unless --domains / --libraries is given; --domains general = Mathlib only), a git repository; then Mathlib's\n" +
  "  cache, the chosen libraries' prebuilt caches, a build and the library indexes (skipped with --no-build). `--list` prints the domains and libraries.";

export async function runInitCli(args: string[]): Promise<void> {
  const value = (flag: string): string | undefined => {
    const i = args.indexOf(flag);
    return i >= 0 ? args[i + 1] : undefined;
  };
  const c = loadCatalog();
  if (args.includes("--list")) {
    console.log(catalogListing(c));
    return;
  }
  const flagged = new Set(["--domains", "--libraries", "--owner", "--email"].flatMap((f) => (args.includes(f) ? [args.indexOf(f) + 1] : [])));
  const dir = args.find((a, i) => !a.startsWith("--") && !flagged.has(i));
  if (!dir) throw new Error(INIT_USAGE);
  const list = (flag: string): string[] | null => value(flag)?.split(",").map((s) => s.trim()).filter(Boolean) ?? null;
  const libraries = list("--libraries") ?? [];
  const domains = list("--domains") ?? (args.includes("--libraries") ? [] : process.stdin.isTTY ? await askDomains(c) : null);
  if (!domains) {
    throw new Error(`no terminal to ask on: ask the user which optional libraries to install, then pass --domains and/or --libraries\n${catalogListing(c)}`);
  }
  const gitConfig = (key: string): string | undefined => spawnSync("git", ["config", key], { encoding: "utf8" }).stdout.trim() || undefined;
  const name = value("--owner") ?? gitConfig("user.name") ?? "Your Name";
  const email = value("--email") ?? gitConfig("user.email");
  const sel = initToolkit({ dir, domains, libraries, owner: { name, ...(email ? { email } : {}) }, build: !args.includes("--no-build") }, c);
  console.log(
    `[init] done. Use it with --toolkit ${path.resolve(dir)} (or THEOREMCHECKER_TOOLKIT), and push it to a private repository of your own.` +
      (sel.skipped.length ? ` Not installed: ${sel.skipped.map((s) => s.name).join(", ")}.` : ""),
  );
}
