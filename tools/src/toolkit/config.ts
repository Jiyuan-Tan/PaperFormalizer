// TheoremChecker toolkit configuration: the canonical loader.
//
// A toolkit is the owner's Lake project that TheoremChecker writes into. Its root holds
// `theoremchecker.json`, which names the toolkit library and its divisions, the papers library,
// and the read-only base libraries. Every path TheoremChecker needs inside a toolkit is derived
// here, so no caller hand-joins `runs/`, `doc/ledger.json`, or a lock file.
//
// Root resolution, in order: an explicit `--toolkit <path>`, the `THEOREMCHECKER_TOOLKIT` env
// var, then the nearest ancestor of the cwd that contains `theoremchecker.json`. Each source
// must name a directory that actually contains `theoremchecker.json`; there is no fallback to
// the cwd, because a wrong root would silently write run records into another tree.
import { existsSync, readFileSync, statSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { z } from "zod";
import { loadAliasFile } from "../formalization/aliases.js";

export const TOOLKIT_CONFIG_FILE = "theoremchecker.json";
export const TOOLKIT_ENV_VAR = "THEOREMCHECKER_TOOLKIT";
export const TOOLKIT_RUNS_DIRNAME = "runs";
export const TOOLKIT_STAGING_SEGMENT = "Staging";
/** Held across a whole toolkit promotion (move + build + lint + index), so two never interleave. */
export const TOOLKIT_LOCK_FILENAME = ".toolkit-promote.lock";

const leanIdent = z.string().regex(/^[A-Za-z_][A-Za-z0-9_']*$/, "must be a single Lean identifier");

const baseLibrarySchema = z.object({
  name: leanIdent,
  kind: z.enum(["path", "transitive"]),
  path: z.string().min(1).optional(),
  index: z.string().min(1).nullable().optional(),
  review_sidecars: z.string().min(1).nullable().optional(),
  alias_file: z.string().min(1).nullable().optional(),
  /** Markdown notes for this library (tactics, simp sets, conventions) appended to the F2
   *  scaffold and F4 filler prompts. Resolved like `alias_file`. */
  prompt_notes: z.string().min(1).nullable().optional(),
  search: z.array(z.string().min(1)).optional(),
  /** What the library covers, one line: shown to the F-stage agents beside its name. */
  summary: z.string().min(1).optional(),
}).superRefine((b, ctx) => {
  if (b.kind === "path" && !b.path) {
    ctx.addIssue({ code: z.ZodIssueCode.custom, path: ["path"], message: `base "${b.name}" has kind "path" but no path` });
  }
});

export const toolkitConfigFileSchema = z.object({
  version: z.literal(1),
  owner: z.object({ name: z.string().min(1), email: z.string().optional() }).passthrough(),
  toolkit: z.object({
    lib: leanIdent,
    papers_lib: leanIdent,
    divisions: z.array(leanIdent).min(1),
  }),
  base: z.array(baseLibrarySchema).default([]),
  lean: z.object({ toolchain: z.string().min(1) }).passthrough(),
  /** V1.5 referee options. `max_concurrent` caps its parallel referee
   *  calls (default 6); `shard_bytes` is a node shard's content budget (default 70000 bytes of
   *  statement + proof excerpts) and `shard_max_hypotheses` / `shard_max_lemmas` /
   *  `shard_max_theorems` its node-count ceilings per kind (defaults 10 / 6 / 3); `symbol_effort`
   *  is the codex reasoning effort of every symbol-referee call (default "medium"; statement
   *  shards and the global pass stay at "high"). */
  referee: z
    .object({
      max_concurrent: z.number().int().min(1).optional(),
      shard_bytes: z.number().int().min(1).optional(),
      shard_max_hypotheses: z.number().int().min(1).optional(),
      shard_max_lemmas: z.number().int().min(1).optional(),
      shard_max_theorems: z.number().int().min(1).optional(),
      symbol_effort: z.enum(["low", "medium", "high"]).optional(),
    })
    .optional(),
}).superRefine((c, ctx) => {
  const issue = (p: (string | number)[], message: string) =>
    ctx.addIssue({ code: z.ZodIssueCode.custom, path: p, message });
  if (c.toolkit.lib === c.toolkit.papers_lib) issue(["toolkit", "papers_lib"], "papers_lib must differ from lib");
  const seen = new Set<string>();
  c.toolkit.divisions.forEach((d, i) => {
    if (seen.has(d)) issue(["toolkit", "divisions", i], `duplicate division ${d}`);
    if (d === TOOLKIT_STAGING_SEGMENT) issue(["toolkit", "divisions", i], `"${d}" is reserved for study staging`);
    seen.add(d);
  });
  const names = new Set<string>();
  c.base.forEach((b, i) => {
    if (names.has(b.name)) issue(["base", i, "name"], `duplicate base library ${b.name}`);
    if (b.name === c.toolkit.lib || b.name === c.toolkit.papers_lib) {
      issue(["base", i, "name"], `base library ${b.name} collides with a toolkit library name`);
    }
    names.add(b.name);
  });
});

/** A base library with every path resolved to an absolute path (relative entries in
 *  `theoremchecker.json` are relative to the toolkit root). */
export interface BaseLibrary {
  name: string;
  kind: "path" | "transitive";
  /** Package root, for `kind: "path"`. */
  path?: string;
  /** Per-declaration index (`doc/library_index.json`-shaped), when the base ships one. */
  index?: string;
  reviewSidecars?: string;
  aliasFile?: string;
  /** Markdown notes appended to the F2 scaffold / F4 filler prompts (`## Notes for <name>`). */
  promptNotes?: string;
  /** Named search tools for this base (e.g. `loogle`, `leansearch`). */
  search: string[];
  /** What the library covers, one line. */
  summary?: string;
}

export type ToolkitRootSource = "arg" | "env" | "cwd";

export interface ToolkitConfig {
  /** Absolute toolkit root (the directory holding `theoremchecker.json`). */
  readonly toolkitRoot: string;
  readonly source: ToolkitRootSource;
  readonly configPath: string;
  /** The Lean/Lake project path TheoremChecker builds and serves lean-lsp from (= the root). */
  readonly leanProjectPath: string;
  readonly runsDir: string;
  /** Library name of the curated toolkit (e.g. `Toolkit`) and its source directory. */
  readonly lib: string;
  readonly toolkitLibDir: string;
  /** Study staging directory (`<lib>/Staging`), never imported by the toolkit barrel. */
  readonly stagingDir: string;
  /** Library name and source directory of the per-paper output. */
  readonly papersLib: string;
  readonly papersDir: string;
  /** Divisions, lowest layer first: a division may import only itself and earlier ones. */
  readonly divisions: readonly string[];
  readonly ledgerPath: string;
  readonly indexPath: string;
  readonly lockPath: string;
  readonly baseLibraries: readonly BaseLibrary[];
  readonly owner: { name: string; email?: string };
  readonly leanToolchain: string;
  /** `referee.max_concurrent` (default 6): the V1.5 referee's parallel calls; `referee.symbol_effort` (default "medium"): the codex
   *  reasoning effort of the symbol referee. */
  readonly referee?: RefereeOptions;
}

function abs(root: string, p: string | null | undefined): string | undefined {
  return p ? path.resolve(root, p) : undefined;
}

/** Defaults of the V1.5 referee's `theoremchecker.json` `referee` keys. */
export const DEFAULT_REFEREE_OPTIONS = Object.freeze({
  max_concurrent: 6,
  shard_bytes: 70_000,
  shard_max_hypotheses: 10,
  shard_max_lemmas: 6,
  shard_max_theorems: 3,
  symbol_effort: "medium" as SymbolEffort,
});

/** Codex reasoning effort of the V1.5 symbol referee (`referee.symbol_effort`). */
export type SymbolEffort = "low" | "medium" | "high";

/** `theoremchecker.json` `referee`, resolved (every key filled by `toolkitConfigFromJson`). */
export interface RefereeOptions {
  readonly max_concurrent?: number;
  readonly shard_bytes?: number;
  readonly shard_max_hypotheses?: number;
  readonly shard_max_lemmas?: number;
  readonly shard_max_theorems?: number;
  readonly symbol_effort?: SymbolEffort;
}

/** Build a config from an already-parsed `theoremchecker.json` value (no filesystem access). */
export function toolkitConfigFromJson(
  root: string,
  json: unknown,
  source: ToolkitRootSource = "arg",
  configFile: string = TOOLKIT_CONFIG_FILE,
): ToolkitConfig {
  const parsed = toolkitConfigFileSchema.safeParse(json);
  const rootAbs = path.resolve(root);
  const configPath = path.join(rootAbs, configFile);
  if (!parsed.success) {
    const detail = parsed.error.issues.map((i) => `${i.path.join(".") || "(root)"}: ${i.message}`).join("; ");
    throw new Error(`invalid ${configPath}: ${detail}`);
  }
  const c = parsed.data;
  const libDir = path.join(rootAbs, c.toolkit.lib);
  return Object.freeze({
    toolkitRoot: rootAbs,
    source,
    configPath,
    leanProjectPath: rootAbs,
    runsDir: path.join(rootAbs, TOOLKIT_RUNS_DIRNAME),
    lib: c.toolkit.lib,
    toolkitLibDir: libDir,
    stagingDir: path.join(libDir, TOOLKIT_STAGING_SEGMENT),
    papersLib: c.toolkit.papers_lib,
    papersDir: path.join(rootAbs, c.toolkit.papers_lib),
    divisions: Object.freeze([...c.toolkit.divisions]),
    ledgerPath: path.join(rootAbs, "doc", "ledger.json"),
    indexPath: path.join(rootAbs, "doc", "toolkit_index.json"),
    lockPath: path.join(rootAbs, TOOLKIT_LOCK_FILENAME),
    baseLibraries: Object.freeze(c.base.map((b): BaseLibrary => ({
      name: b.name,
      kind: b.kind,
      path: abs(rootAbs, b.path),
      index: abs(rootAbs, b.index),
      reviewSidecars: abs(rootAbs, b.review_sidecars),
      aliasFile: abs(rootAbs, b.alias_file),
      promptNotes: abs(rootAbs, b.prompt_notes),
      search: b.search ?? [],
      ...(b.summary ? { summary: b.summary } : {}),
    }))),
    owner: { name: c.owner.name, ...(c.owner.email ? { email: c.owner.email } : {}) },
    leanToolchain: c.lean.toolchain,
    referee: Object.freeze({ ...DEFAULT_REFEREE_OPTIONS, ...(c.referee ?? {}) }),
  });
}

const HOW_TO =
  `pass --toolkit <path>, set ${TOOLKIT_ENV_VAR}=<path>, or run from inside a toolkit ` +
  `(a directory tree whose root contains ${TOOLKIT_CONFIG_FILE})`;

function isFile(p: string): boolean {
  return existsSync(p) && statSync(p).isFile();
}

/** The toolkit config file in `dir` (`theoremchecker.json`), else null. */
export function toolkitConfigFileIn(dir: string): string | null {
  const p = path.join(dir, TOOLKIT_CONFIG_FILE);
  return isFile(p) ? p : null;
}

function hasConfig(dir: string): boolean {
  return toolkitConfigFileIn(dir) !== null;
}

export interface ResolveToolkitOptions {
  /** Value of an explicit `--toolkit <path>` argument. */
  explicit?: string | null;
  env?: NodeJS.ProcessEnv;
  cwd?: string;
}

/** Resolve the toolkit root (arg → env → cwd walk-up). Throws, naming all three ways, when
 *  no source yields a directory containing `theoremchecker.json`. */
export function resolveToolkitRoot(opts: ResolveToolkitOptions = {}): { root: string; source: ToolkitRootSource } {
  const cwd = path.resolve(opts.cwd ?? process.cwd());
  const explicit = opts.explicit?.trim();
  if (explicit) {
    const root = path.resolve(cwd, explicit);
    if (!hasConfig(root)) {
      throw new Error(`--toolkit ${explicit}: no ${TOOLKIT_CONFIG_FILE} in ${root}. To select a toolkit, ${HOW_TO}.`);
    }
    return { root, source: "arg" };
  }
  const fromEnv = (opts.env ?? process.env)[TOOLKIT_ENV_VAR]?.trim();
  if (fromEnv) {
    const root = path.resolve(cwd, fromEnv);
    if (!hasConfig(root)) {
      throw new Error(`${TOOLKIT_ENV_VAR}=${fromEnv}: no ${TOOLKIT_CONFIG_FILE} in ${root}. To select a toolkit, ${HOW_TO}.`);
    }
    return { root, source: "env" };
  }
  for (let cur = cwd; ; cur = path.dirname(cur)) {
    if (hasConfig(cur)) return { root: cur, source: "cwd" };
    if (path.dirname(cur) === cur) break;
  }
  throw new Error(`No TheoremChecker toolkit found from ${cwd}. To select a toolkit, ${HOW_TO}.`);
}

/**
 * Check every per-base data file the config names: an `alias_file` must be readable and parse as
 * an alias lexicon, a `prompt_notes` file must be readable. Throws naming the base library, the
 * file and the config, so a misconfigured toolkit fails at start-up, not mid-run.
 */
export function validateBaseLibraryFiles(cfg: ToolkitConfig): void {
  for (const b of cfg.baseLibraries) {
    if (b.aliasFile) {
      try {
        loadAliasFile(b.aliasFile);
      } catch (e) {
        throw new Error(`base library ${b.name}: alias_file: ${e instanceof Error ? e.message : String(e)}; fix or remove it in ${cfg.configPath}`);
      }
    }
    if (b.promptNotes) {
      try {
        readFileSync(b.promptNotes, "utf8");
      } catch (e) {
        throw new Error(
          `base library ${b.name}: prompt_notes ${b.promptNotes} is unreadable ` +
            `(${e instanceof Error ? e.message : String(e)}); fix or remove it in ${cfg.configPath}`,
        );
      }
    }
  }
}

/** Resolve the toolkit root and parse its `theoremchecker.json`; every configured alias / notes
 *  file is validated (`validateBaseLibraryFiles`). */
export function loadToolkitConfig(opts: ResolveToolkitOptions = {}): ToolkitConfig {
  const { root, source } = resolveToolkitRoot(opts);
  const configPath = toolkitConfigFileIn(root) ?? path.join(root, TOOLKIT_CONFIG_FILE);
  let json: unknown;
  try {
    json = JSON.parse(readFileSync(configPath, "utf8"));
  } catch (err) {
    throw new Error(`cannot parse ${configPath}: ${err instanceof Error ? err.message : String(err)}`);
  }
  const cfg = toolkitConfigFromJson(root, json, source, path.basename(configPath));
  validateBaseLibraryFiles(cfg);
  return cfg;
}

/** `<root>/<lib>/<division>.lean` — the division barrel. */
export function divisionBarrelPath(cfg: ToolkitConfig, division: string): string {
  return path.join(cfg.toolkitLibDir, `${division}.lean`);
}

/** The TheoremChecker `tools/` directory (holds the lint and search bins). */
export function theoremCheckerToolsDir(): string {
  return path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..");
}

/** The toolkit a pipeline context runs against. Every runner sets `ctx.toolkit`; a context
 *  without one is a wiring bug, so this throws instead of guessing a root. */
export function ctxToolkit(ctx: { toolkit?: ToolkitConfig; repoRoot: string }): ToolkitConfig {
  if (!ctx.toolkit) {
    throw new Error(`pipeline context for ${ctx.repoRoot} carries no toolkit config (ctx.toolkit); this is a runner wiring bug`);
  }
  return ctx.toolkit;
}
