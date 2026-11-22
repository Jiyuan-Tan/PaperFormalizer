/**
 * Per-run Lake workspaces (on for every run, below): a run builds its paper in a disposable
 * workspace of its own on the machine's local disk, so its builds never wait for the toolkit's
 * writers (promotions) and never stop them.
 *
 * GENERATIONS. Each time the toolkit is stamped clean (`build_mutex.stampToolkitClean`: the end of a
 * promotion's moves or a study's apply, and `toolkit-flux off`) a publisher of its own starts, which
 * once that exclusive hold is over takes a shared hold of no paper, checks the toolkit is still clean
 * and packs its pinned sources and their build outputs as one archive,
 * `<toolkit>/.lake/paperformalizer/gens/<N>.tar.zst`, and `gens/CURRENT.json` (renamed into place)
 * names it — only while the `gens/` directory exists (`paperformalizer toolkit-gen publish` makes it
 * and publishes the first). The newest 3 archives stay. What is pinned: every top-level `.lean` of
 * the toolkit but the papers' barrel, the library's directory but its staging tree, lakefile.toml,
 * lake-manifest.json, lean-toolchain (`scripts/lean_workspace.sh pack`).
 *
 * THE WORKSPACE `W` = `<local root>/ws/<slug>/<the toolkit's last path components>` (as many as its
 * lakefile's path dependencies climb: `../../AutoID/AutoID` needs two), where `<local root>` is the
 * machine's Lean cache (`.lake/packages/.pf-local-root`). In it:
 *   - the generation's pinned sources and build outputs, hard links into the machine's unpacked copy
 *     of the generation (`<local root>/gens/<N>/`, unpacked once per machine), but the files Lake
 *     writes in place (traces, hashes, …), which are copied (`lean_workspace.sh`, its header);
 *   - `.lake/build` otherwise its own (the paper's modules are built there), `.lake/config` a copy,
 *     `.lake/packages/*` the shared tree's links (the machine's package copies);
 *   - every other entry of the toolkit a symlink into the shared tree (Papers, runs, sources, the
 *     staging tree…): an edit or a move made through `W` lands in the shared tree, which stays the
 *     one source of truth; and the path dependencies' anchors (`ws/<slug>/AutoID`,
 *     `ws/<slug>/<repo>/third_party`) symlinks to the shared ones;
 *   - `.pf-toolkit` (the toolkit's root, and its real path: the lake shim maps paths by it) and,
 *     written last, `.pf-gen` (the generation pinned).
 *
 * WHO BUILDS WHERE. The run's lake commands — its workers', through the lake shim on their PATH,
 * and the pipeline's own, which `spawnWithInactivityTimeout` gives the shim (`build_mutex.leanWsChildEnv`) —
 * run in `W` (the shim maps the directory and the paths under the toolkit), with no shared-tree lock
 * (`withLakeBuildLock` runs its action at once for such a run) and under `W`'s own lock
 * (`W/.lake/build.lock`, `flock`) for a command that writes build output. The promotion lock's call
 * chain (a commit, the roll-forward of one), a promotion round's apply (`build_mutex.withSharedTree`) and any
 * chain inside a Lake hold stay in the shared tree, under its locks, as before: there the workspace
 * is cleared for every child. The language server is no exception: lean-lsp keeps the toolkit as its
 * project (it resolves symlinks, so every file of `W` would be outside `W`), and its `lake serve`
 * goes to `W` through the shim like any lake command.
 *
 * REFRESH. `ensureWorkspace` is idempotent; it re-pins `W` to the current generation, and only the
 * run's safe points call it: the run's start and each stage's (`refreshRunWorkspace`).
 *
 * ON FOR EVERY RUN, except a run that opts out (`runs/<slug>/no-workspace`): for it nothing here
 * runs. A run whose workspace cannot be made (no generation published, no lake shim, no local root)
 * builds in the shared tree and says so.
 *
 * RELEASE (2026-11-10: nothing removed them, several GB each). A run left for good
 * (`batch_orch.mjs`: settled) is marked (`runs/<slug>/logs/workspace_released.json`) and its
 * workspaces on that machine removed (`releaseWorkspaces`: `ws/<slug>`, `ws/<slug>.promo`,
 * `ws/study_<slug>__*.promo`; and its paper's `tmp/` in the shared tree, 2026-11-11); a machine's others go at the first `ensureWorkspace` of a process
 * there (`sweepWorkspaces`). Never while the run's runner or an apply of it lives or a journal is on
 * file (`releaseBusy`); each is renamed to `ws/.trash-*` first, then removed. A run that starts
 * again drops its marker. `gens/`, `pkgs/` and `toolchain/` are never touched. A study's promotion
 * workspace goes sooner, when its coordinate step ends for good (`releaseStudyPromo`, 2026-11-11).
 */
import { execFile, execFileSync, spawn } from "node:child_process";
import { closeSync, existsSync, openSync, readFileSync, realpathSync } from "node:fs";
import { copyFile, cp, lstat, mkdir, readdir, readFile, readlink, rename, rm, symlink, unlink } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { LEAN_WS_ENV } from "./build_mutex.js";
import { writeJsonAtomic, writeTextAtomic } from "./json_atomic.js";

/** A run's opt-out (`runs/<slug>/no-workspace`: it builds in the shared tree). */
export const WORKSPACE_OPT_OUT = "no-workspace";
/** A run's start waits this long at most for the generation of the toolkit as it stands (`lagWaitMs`),
 *  looking every `lagPollMs` (tests shorten it). */
export const WORKSPACE_TIMING = { lagWaitMs: 10 * 60_000, lagPollMs: 15_000 };
/** Archives of generations kept on the shared disk (a machine keeps as many unpacked). */
export const KEEP_GENERATIONS = 3;

const SCRIPT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..", "scripts", "lean_workspace.sh");

export const gensDir = (toolkitRoot: string) => path.join(toolkitRoot, ".lake", "paperformalizer", "gens");
const currentFile = (toolkitRoot: string) => path.join(gensDir(toolkitRoot), "CURRENT.json");
const archiveOf = (toolkitRoot: string, n: number) => path.join(gensDir(toolkitRoot), `${n}.tar.zst`);
/** What the commit that made generation `n` added (`commit.ts` step 9; 2026-11-11: kept for a later
 *  additive commit, read by nothing yet — a missing record means strict), pruned with its archive. */
export const addsRecordFile = (toolkitRoot: string, n: number) => path.join(gensDir(toolkitRoot), "adds", `${n}.json`);

/** A published generation (`gens/CURRENT.json`): its number and the toolkit signature it is of. */
export interface Generation { gen: number; sig: string; at: string }
/** A workspace's pin (`W/.pf-gen`). */
interface Pin extends Generation { toolkit: string; slug: string; local: string; pinned: string[] }

/** `scripts/lean_workspace.sh <args>` (pack, unpack, pin). */
export const leanWorkspaceSh = (args: string[], timeoutMs = 30 * 60_000) => new Promise<void>((resolve, reject) => {
  execFile("bash", [SCRIPT, ...args], { timeout: timeoutMs, maxBuffer: 16 << 20 }, (err, _out, stderr) => {
    if (err) reject(new Error(`lean_workspace.sh ${args[0]}: ${stderr.trim() || err.message}`));
    else resolve();
  });
});

const readJson = async <T>(file: string): Promise<T | null> => readFile(file, "utf8").then((t) => JSON.parse(t) as T, () => null);
const lexists = (p: string) => lstat(p).then(() => true, () => false);

export async function currentGeneration(toolkitRoot: string): Promise<Generation | null> {
  const g = await readJson<Generation>(currentFile(toolkitRoot));
  return g && Number.isInteger(g.gen) && g.gen > 0 && typeof g.sig === "string" ? g : null;
}

/** The generations whose archives are on the shared disk, newest first (the current one first). */
export async function publishedGenerations(toolkitRoot: string): Promise<number[]> {
  const cur = await currentGeneration(toolkitRoot);
  const numbers = (await readdir(gensDir(toolkitRoot)).catch(() => [] as string[])).map((n) => /^(\d+)\.tar\.zst$/.exec(n)?.[1]).filter((n): n is string => !!n).map(Number);
  return [...new Set([...(cur && numbers.includes(cur.gen) ? [cur.gen] : []), ...numbers.sort((a, b) => b - a)])];
}

/** The machine's local Lean root (`PAPERFORMALIZER_LEAN_LOCAL_ROOT`, else the toolkit's
 *  `.lake/packages/.pf-local-root`, written by `lean_local_cache.sh pack`). */
export function localLeanRoot(toolkitRoot: string): string {
  const env = process.env.PAPERFORMALIZER_LEAN_LOCAL_ROOT?.trim();
  if (env) return env;
  try {
    const r = readFileSync(path.join(toolkitRoot, ".lake", "packages", ".pf-local-root"), "utf8").trim();
    if (r) return r;
  } catch { /* below */ }
  // one machine: the toolkit's own disk (hard links need the generation and the workspaces on one disk)
  return path.join(toolkitRoot, ".lake", "paperformalizer", "local");
}

/** Why per-run workspaces cannot be made on this machine, or null: they need Linux or macOS (bash,
 *  hard links, the lake shim) and `flock`, `zstd` and `tar` on the PATH. On Windows they are off:
 *  a toolkit installed in WSL has them. */
export function workspacesUnsupported(): string | null {
  if (process.platform === "win32") return "this is Windows: per-run workspaces need Linux or macOS (on Windows, install in WSL)";
  if (process.env.PAPERFORMALIZER_LAKE_SHIM === "0") return "PAPERFORMALIZER_LAKE_SHIM is 0";
  if (process.env.PAPERFORMALIZER_WORKSPACES === "off") return "PAPERFORMALIZER_WORKSPACES is off";
  const dirs = (process.env.PATH ?? "").split(path.delimiter).filter(Boolean);
  const missing = ["flock", "zstd", "tar"].filter((c) => !dirs.some((d) => existsSync(path.join(d, c))));
  if (missing.length) return `${missing.join(", ")} not found on the PATH`;
  // `lean_workspace.sh` needs bash 4 or later and GNU cp and find (`cp -al`, `find -printf`): macOS has
  // neither by default (Homebrew's bash, coreutils and findutils, their gnubin first on the PATH)
  const gnu = gnuUserland();
  return gnu ? `${gnu} (on macOS: \`brew install bash coreutils findutils\`, their gnubin directories first on the PATH)` : null;
}
let gnuSeen: { path: string; why: string | null } | null = null;
function gnuUserland(): string | null {
  const PATH = process.env.PATH ?? "";
  if (gnuSeen?.path === PATH) return gnuSeen.why;
  const ok = (cmd: string) => { try { execFileSync("bash", ["-c", cmd], { stdio: "ignore", timeout: 10_000 }); return true; } catch { return false; } };
  const why = !ok("(( BASH_VERSINFO[0] >= 4 ))") ? "bash 4 or later is needed"
    : !ok("cp --version | grep -q GNU && find --version | grep -q GNU") ? "GNU cp and find are needed" : null;
  gnuSeen = { path: PATH, why };
  return why;
}

/** The toolkit's generations turned on where they are off (on by default): shared mode
 *  (`build_mutex`'s `lake-shared-mode`) and `gens/` made, the toolkit built clean under an exclusive
 *  hold and its first generation published — the current generation, or why there is none (the run
 *  then builds in the shared tree). Shared mode is turned on only while no other run of the toolkit
 *  is live: older code knows nothing of shared holds. */
export async function ensureGenerations(toolkitRoot: string, log: (line: string) => void = (l) => console.log(l)): Promise<Generation | { why: string }> {
  const root = path.resolve(toolkitRoot);
  // the machine and the switches first: an existing generation turns no switch back on
  const no = workspacesUnsupported();
  if (no) return { why: no };
  const have = await currentGeneration(root);
  if (have) return have;
  const { LAKE_LOCK_HELD_ENV, lakeLockChildEnv, lakeSharedModeFile, stampToolkitClean, withLakeBuildLock } = await import("./build_mutex.js");
  // an exclusive hold of its own: never from inside a hold this chain or a parent has
  if (Object.keys(lakeLockChildEnv()).length > 0 || process.env[LAKE_LOCK_HELD_ENV]) return { why: "no toolkit generation is published, and none is made from inside a Lake hold" };
  const modeFile = lakeSharedModeFile(path.join(root, ".lake-build.lock"));
  if (!existsSync(modeFile)) {
    const old = await liveOlderRuns(root);
    if (old.length) return { why: `shared builds are turned on only while no run of older code is live (${old.slice(0, 3).join(", ")}${old.length > 3 ? ", …" : ""})` };
    await mkdir(path.dirname(modeFile), { recursive: true });
    await writeTextAtomic(modeFile, "on by default\n");
    log("[workspace] shared builds turned on for this toolkit (.lake/paperformalizer/lake-shared-mode)");
  }
  await mkdir(gensDir(root), { recursive: true });
  const failed = await failedCleanBuild(root);
  if (failed) return { why: failed };
  log("[workspace] building the toolkit clean for its first generation");
  const clean = await withLakeBuildLock(root, () => stampToolkitClean(root, log), "the toolkit's first generation", log);
  if (!clean.clean) return { why: `the toolkit is not built clean (${clean.why})` };
  // the clean stamp started the publisher (`spawnPublisher`): wait for it, as long as it runs
  const { flockFree } = await import("./commit.js");
  const logFile = path.join(gensDir(root), "publish.log");
  const started = Date.now();
  for (const until = started + GENERATION_TIMING.publishWaitMs; Date.now() < until;) {
    const g = await currentGeneration(root);
    if (g) return g;
    if (Date.now() - started > GENERATION_TIMING.startMs && (await flockFree(publishLock(root)))) {
      const g2 = await currentGeneration(root);
      if (g2) return g2;
      const tail = (await readFile(logFile, "utf8").catch(() => "")).trim().split("\n").slice(-3).join(" | ");
      return { why: `the first generation's publisher ended without publishing (${logFile}${tail ? `: ${tail}` : ""})` };
    }
    await new Promise((r) => setTimeout(r, GENERATION_TIMING.pollMs));
  }
  return { why: `no generation published yet (see ${logFile})` };
}

/** A marker beside a run's heartbeat that its runner knows shared holds (`.run.active`'s owner token):
 *  written at the run's start, before its workspace (`enableRunWorkspace`). */
const KNOWS_SHARED = ".run.shared-holds";
export async function markKnowsShared(root: string, slug: string): Promise<void> {
  const { parseHeartbeat } = await import("./run_heartbeat.js");
  const logs = path.join(runDirOf(root, slug), "logs");
  const hb = parseHeartbeat(await readFile(path.join(logs, ".run.active"), "utf8").catch(() => ""), 0);
  if (hb?.ownerToken) await writeTextAtomic(path.join(logs, KNOWS_SHARED), `${hb.ownerToken}\n`).catch(() => {});
}
/** The toolkit's live runs whose runner never marked that it knows shared holds (older code). */
async function liveOlderRuns(root: string): Promise<string[]> {
  const { heartbeatLiveness, parseHeartbeat } = await import("./run_heartbeat.js");
  const out: string[] = [];
  for (const d of await readdir(path.join(root, "runs")).catch(() => [] as string[])) {
    const logs = path.join(root, "runs", d, "logs");
    if (!heartbeatLiveness(path.join(logs, ".run.active")).live) continue;
    const token = parseHeartbeat(await readFile(path.join(logs, ".run.active"), "utf8").catch(() => ""), 0)?.ownerToken;
    const marked = (await readFile(path.join(logs, KNOWS_SHARED), "utf8").catch(() => "")).trim();
    if (!token || marked !== token) out.push(d);
  }
  return out;
}
/** Why the toolkit's last clean build failed for its sources as they stand, or null (none, or other sources). */
async function failedCleanBuild(root: string): Promise<string | null> {
  const { lakeCleanStampFile } = await import("./build_mutex.js");
  const stamp = await readJson<{ sig?: string; ok?: boolean; why?: string }>(lakeCleanStampFile(path.join(root, ".lake-build.lock")));
  if (!stamp || stamp.ok !== false || typeof stamp.sig !== "string") return null;
  const { toolkitLayout, toolkitSignature } = await import("./build_inputs.js");
  const sig = await toolkitSignature(await toolkitLayout(root)).catch(() => null);
  return sig === stamp.sig ? `the toolkit's clean build failed for its sources as they stand (${(stamp.why ?? "").split("\n")[0]!.slice(0, 200)}): fix the toolkit; if the failure was not the toolkit's (a machine out of memory), remove ${lakeCleanStampFile(path.join(root, ".lake-build.lock"))} and the next run's start builds it again` : null;
}
/** How long `ensureGenerations` waits for the first generation's publisher at most, how often it looks,
 *  and how long the publisher has to take its lock before a free lock means it ended (tests shorten them). */
export const GENERATION_TIMING = { publishWaitMs: 30 * 60_000, pollMs: 2_000, startMs: 10_000 };

/**
 * Publish the toolkit as it stands — clean, of signature `sig` — as the next generation, when
 * generations are on (the `gens/` directory exists; else null) and the current one is not of `sig`
 * already. Called inside a hold that no toolkit writer runs beside (`toolkit-gen publish`'s shared
 * hold of no paper), by one publisher at a time (`gens/.publish.lock`).
 */
export async function publishGeneration(
  toolkitRoot: string, sig: string, log: (line: string) => void = (l) => console.warn(l),
  /** The archive of the toolkit as it stands, packed already (a commit's, `commit.ts`): moved into
   *  place instead of the toolkit packed. */
  packed?: string,
): Promise<Generation | null> {
  if (!existsSync(gensDir(toolkitRoot))) return null;
  const cur = await currentGeneration(toolkitRoot);
  if (cur?.sig === sig && existsSync(archiveOf(toolkitRoot, cur.gen))) return cur;
  const numbers = (await readdir(gensDir(toolkitRoot))).map((n) => /^(\d+)\.tar\.zst$/.exec(n)?.[1]).filter((n): n is string => !!n).map(Number);
  const gen = Math.max(cur?.gen ?? 0, ...numbers, 0) + 1;
  const { toolkitLayout } = await import("./build_inputs.js");
  const t = await toolkitLayout(toolkitRoot);
  const t0 = Date.now();
  if (!packed) await leanWorkspaceSh(["pack", toolkitRoot, archiveOf(toolkitRoot, gen), t.lib, t.papersLib, t.staging]);
  else {
    await rename(packed, archiveOf(toolkitRoot, gen)).catch(async (err: NodeJS.ErrnoException) => {
      if (err.code !== "EXDEV") throw err;
      await copyFile(packed, `${archiveOf(toolkitRoot, gen)}.tmp`);
      await rename(`${archiveOf(toolkitRoot, gen)}.tmp`, archiveOf(toolkitRoot, gen));
    });
  }
  const next: Generation = { gen, sig, at: new Date().toISOString() };
  await writeJsonAtomic(currentFile(toolkitRoot), next);
  for (const n of numbers.filter((n) => n <= gen - KEEP_GENERATIONS)) await unlink(archiveOf(toolkitRoot, n)).catch(() => {});
  for (const e of await readdir(path.join(gensDir(toolkitRoot), "adds")).catch(() => [] as string[])) {
    const n = Number(/^(\d+)\.json$/.exec(e)?.[1]);
    if (n <= gen - KEEP_GENERATIONS) await unlink(path.join(gensDir(toolkitRoot), "adds", e)).catch(() => {});
  }
  log(`[workspace] toolkit generation ${gen} published (${Math.round((Date.now() - t0) / 100) / 10} s)`);
  return next;
}

const TOOLS = path.resolve(path.dirname(SCRIPT), "..");
const publishLock = (toolkitRoot: string) => path.join(gensDir(toolkitRoot), ".publish.lock");
/** `paperformalizer toolkit-gen publish --locked` for `toolkitRoot`, under `flock -n` on the
 *  publishers' lock (one at a time; a second one does not start), with an environment that holds
 *  no Lake hold and no workspace. */
const publisherArgs = (toolkitRoot: string, sig: string | null) => ["-n", publishLock(toolkitRoot), process.execPath,
  "--import", path.join(TOOLS, "node_modules", "tsx", "dist", "loader.mjs"), path.join(TOOLS, "bin", "paperformalizer.ts"),
  "toolkit-gen", "publish", "--locked", "--toolkit", toolkitRoot, ...(sig ? ["--sig", sig] : [])];
const publisherEnv = () => {
  const env = { ...process.env };
  delete env.PAPERFORMALIZER_LAKE_LOCK_HELD;
  delete env[LEAN_WS_ENV];
  return env;
};

/** At a clean stamp, inside its exclusive hold: when generations are on, a publisher of its own
 *  started (detached; its log `gens/publish.log`) — it publishes once this hold is over, never in it. */
export function spawnPublisher(toolkitRoot: string, sig: string, log: (line: string) => void): void {
  if (!existsSync(gensDir(toolkitRoot))) return;
  const out = openSync(path.join(gensDir(toolkitRoot), "publish.log"), "a");
  try {
    const child = spawn("flock", publisherArgs(toolkitRoot, sig), { detached: true, stdio: ["ignore", out, out], env: publisherEnv() });
    child.on("error", (err) => log(`[workspace] the generation's publisher did not start (${err.message})`));
    child.unref();
    log(`[workspace] the toolkit's generation is published in the background (pid ${child.pid}, log ${path.join(gensDir(toolkitRoot), "publish.log")})`);
  } finally {
    closeSync(out);
  }
}

/** How many levels the toolkit's path dependencies climb (`path = "../../AutoID/AutoID"`: 2), and
 *  each one's anchor: the first entry outside the toolkit, relative to the toolkit. */
function pathDeps(toolkitRoot: string): { depth: number; anchors: string[] } {
  let text = "";
  try { text = readFileSync(path.join(toolkitRoot, "lakefile.toml"), "utf8"); } catch { /* none */ }
  let depth = 1;
  const anchors: string[] = [];
  for (const m of text.matchAll(/^\s*path\s*=\s*"([^"]+)"/gm)) {
    const parts = m[1]!.split("/").filter((p) => p && p !== ".");
    const ups = parts.findIndex((p) => p !== "..");
    if (ups <= 0) continue;
    depth = Math.max(depth, ups);
    anchors.push([...parts.slice(0, ups), parts[ups]!].join("/"));
  }
  return { depth, anchors };
}

/** The workspace of run `slug` on this machine. */
export function workspacePath(toolkitRoot: string, slug: string, localRoot = localLeanRoot(toolkitRoot)): string {
  if (!/^[A-Za-z0-9._-]+$/.test(slug)) throw new Error(`not a run slug: ${slug}`);
  const root = path.resolve(toolkitRoot);
  const tail = root.split(path.sep).filter(Boolean).slice(-pathDeps(root).depth);
  return path.join(localRoot, "ws", slug, ...tail);
}

const readPin = (ws: string) => readJson<Pin>(path.join(ws, ".pf-gen"));

/** The workspace's links into the shared tree (each made once; never replaced): every entry of the
 *  toolkit but `.lake` and the pinned ones, the packages, the path dependencies' anchors, the
 *  `.lake/config` copy and `.pf-toolkit`. */
async function linkShared(root: string, ws: string, pinned: readonly string[]): Promise<void> {
  await mkdir(path.join(ws, ".lake", "build"), { recursive: true });
  await mkdir(path.join(ws, ".lake", "packages"), { recursive: true });
  const roots = `${root}\n${realpathSync(root)}\n`;
  if ((await readFile(path.join(ws, ".pf-toolkit"), "utf8").catch(() => "")) !== roots) await writeTextAtomic(path.join(ws, ".pf-toolkit"), roots);
  for (const e of await readdir(root)) {
    if (e === ".lake" || pinned.includes(e) || (await lexists(path.join(ws, e)))) continue;
    await symlink(path.join(root, e), path.join(ws, e));
  }
  // the packages: the shared tree's links (the machine's copies), never its own `.pf-*` archives
  const pkgs = path.join(root, ".lake", "packages");
  for (const e of await readdir(pkgs).catch(() => [] as string[])) {
    if (e.startsWith(".") || (await lexists(path.join(ws, ".lake", "packages", e)))) continue;
    const st = await lstat(path.join(pkgs, e));
    await symlink(st.isSymbolicLink() ? await readlink(path.join(pkgs, e)) : path.join(pkgs, e), path.join(ws, ".lake", "packages", e));
  }
  if (!existsSync(path.join(ws, ".lake", "config")) && existsSync(path.join(root, ".lake", "config"))) {
    await cp(path.join(root, ".lake", "config"), path.join(ws, ".lake", "config"), { recursive: true, dereference: true });
  }
  for (const a of pathDeps(root).anchors) {
    const at = path.resolve(ws, a);
    if (await lexists(at)) continue;
    await mkdir(path.dirname(at), { recursive: true });
    await symlink(path.resolve(root, a), at);
  }
}

/**
 * The workspace of run `slug`, pinned to the toolkit's current generation (idempotent: a workspace
 * already on it only gains the links to entries new in the shared tree). Re-pins a workspace on an
 * older one — only at a safe point of the run (its caller's to choose). `.pf-gen` is written last.
 * `opts.gen`: pinned to that published generation instead (its archive on the shared disk; a
 * baseline's workspace, `garden_verify`).
 */
export async function ensureWorkspace(
  toolkitRoot: string,
  slug: string,
  opts: { localRoot?: string; log?: (line: string) => void; gen?: number } = {},
): Promise<{ path: string; gen: number; repinned: boolean; ms: number }> {
  const t0 = Date.now();
  const root = path.resolve(toolkitRoot);
  const latest = await currentGeneration(root);
  let cur = latest;
  if (opts.gen !== undefined && latest?.gen !== opts.gen) {
    if (!existsSync(archiveOf(root, opts.gen))) throw new Error(`toolkit generation ${opts.gen} is not on the shared disk (${archiveOf(root, opts.gen)})`);
    cur = { gen: opts.gen, sig: "(an older generation)", at: "" };
  }
  if (!cur) throw new Error(`no toolkit generation published (${currentFile(root)}): \`paperformalizer toolkit-gen publish\` publishes one`);
  const local = opts.localRoot ?? localLeanRoot(root);
  const ws = workspacePath(root, slug, local);
  // the run is live again (a resume, a revise, an apply): its release marker goes
  const owner = ownerOf(slug);
  if (owner && (await unlink(releasedMarker(root, owner)).then(() => true, () => false))) opts.log?.(`[workspace] ${owner}: live again — its release marker removed`);
  if (!WORKSPACE_SWEEP.done) {
    WORKSPACE_SWEEP.done = true;
    await sweepWorkspaces(root, local, slug, opts.log ?? (() => {})).catch((err) => opts.log?.(`[workspace] the sweep of ${path.join(local, "ws")} failed (${err instanceof Error ? err.message : String(err)})`));
  }
  const pin = await readPin(ws);
  if (pin?.gen === cur.gen) {
    await linkShared(root, ws, pin.pinned);
    return { path: ws, gen: cur.gen, repinned: false, ms: Date.now() - t0 };
  }
  const gen = path.join(local, "gens", String(cur.gen));
  await leanWorkspaceSh(["unpack", archiveOf(root, cur.gen), gen]);
  const { toolkitLayout } = await import("./build_inputs.js");
  const t = await toolkitLayout(root);
  const pinned = (await readdir(gen)).filter((e) => e !== ".lake" && !e.startsWith(".pf-"));
  await mkdir(ws, { recursive: true });
  await linkShared(root, ws, pinned);
  await leanWorkspaceSh(["pin", gen, ws, root, path.join(path.relative(root, t.libDir), t.staging)]);
  const next: Pin = { ...cur, toolkit: root, slug, local, pinned };
  await writeJsonAtomic(path.join(ws, ".pf-gen"), next);
  const ms = Date.now() - t0;
  opts.log?.(`[workspace] ${slug}: ${pin ? `re-pinned from generation ${pin.gen} to ${cur.gen}` : `created on generation ${cur.gen}`} (${ws}, ${Math.round(ms / 100) / 10} s)`);
  return { path: ws, gen: cur.gen, repinned: true, ms };
}

/**
 * At a run's start: unless the run has opted out (`runs/<slug>/no-workspace`), its workspace made
 * current and set for the process and every child (`PAPERFORMALIZER_LEAN_WS`). Otherwise nothing happens (null) — as when the workspace cannot be
 * made: the run builds in the shared tree (logged), never stopped for it. The published generation
 * may lag the shared toolkit (its publisher queues for a hold): that is fine for a run whose paper
 * needs nothing newer, but a run resumed after its own promotion imports what it moved. So the
 * start waits (`WORKSPACE_TIMING`) while the workspace lacks something of the run's own
 * (`ownLacks`), and past that the run builds in the shared tree. `lacks`: tests replace it.
 */
export async function enableRunWorkspace(
  toolkitRoot: string, slug: string, log: (line: string) => void = (l) => console.log(l),
  lacks?: (ws: string) => Promise<string[]>,
): Promise<string | null> {
  // this run's workspace or none: never one inherited from another run's process
  delete process.env[LEAN_WS_ENV];
  // (this runner knows shared holds: another run's start may turn them on beside it)
  await markKnowsShared(path.resolve(toolkitRoot), slug);
  const { verifyRunDir } = await import("../paths.js");
  if (existsSync(path.join(verifyRunDir(toolkitRoot, slug), WORKSPACE_OPT_OUT))) return null;
  const generation = await ensureGenerations(toolkitRoot, log).catch((err: unknown) => ({ why: err instanceof Error ? err.message : String(err) }));
  if ("why" in generation) {
    log(`[workspace] ${slug} builds in the shared tree: ${generation.why}`);
    return null;
  }
  const check = lacks ?? (await ownLacks(toolkitRoot, slug).catch(() => async () => ["(the run's needs could not be read)"]));
  let waited = false;
  for (const until = Date.now() + WORKSPACE_TIMING.lagWaitMs; ;) {
    let ws: string;
    let gen: number;
    try {
      const r = await ensureWorkspace(toolkitRoot, slug, { log });
      ws = r.path;
      gen = r.gen;
    } catch (err) {
      // a workspace already pinned keeps its generation (the pin's builds were busy, …); none: the shared tree
      ws = "";
      const pin = await (async () => { ws = workspacePath(toolkitRoot, slug); return readPin(ws); })().catch(() => null);
      if (!pin) {
        log(`[workspace] ${slug} builds in the shared tree: no workspace could be made (${err instanceof Error ? err.message : String(err)})`);
        return null;
      }
      gen = pin.gen;
      log(`[workspace] ${slug}: kept on generation ${pin.gen} (${err instanceof Error ? err.message : String(err)})`);
    }
    const missing = await check(ws).catch(() => ["(the workspace could not be checked)"]);
    if (missing.length === 0) {
      log(`[workspace] ${slug} builds in ${ws} (generation ${gen})`);
      process.env[LEAN_WS_ENV] = ws;
      return ws;
    }
    const what = `${missing.slice(0, 3).join(", ")}${missing.length > 3 ? ` and ${missing.length - 3} more` : ""}`;
    if (Date.now() >= until) {
      log(`[workspace] ${slug} builds in the shared tree: generation ${gen} still lacks this run's ${what} after ${Math.round(WORKSPACE_TIMING.lagWaitMs / 60_000)} min (its publish is behind)`);
      return null;
    }
    if (!waited) log(`[workspace] ${slug}: generation ${gen} lacks this run's ${what} (published before its promotion): waiting for the next`);
    waited = true;
    await new Promise((r) => setTimeout(r, WORKSPACE_TIMING.lagPollMs));
  }
}

/** What a run needs of the toolkit that a workspace may lack, read once from the shared tree: its
 *  declarations (the ledger's of origin `slug`, or used by it: `used_by`) where the shared Toolkit declares them now,
 *  and the Toolkit modules its paper imports that the shared tree has. The check of a workspace
 *  `ws` lists those it lacks (a declaration: its module there does not name it). */
async function ownLacks(toolkitRoot: string, slug: string): Promise<(ws: string) => Promise<string[]>> {
  const { toolkitLayout } = await import("./build_inputs.js");
  const t = await toolkitLayout(toolkitRoot);
  const text = (root: string, rel: string) => readFile(path.join(root, rel), "utf8").catch(() => null);
  // declared under its last component, or a dotted suffix of its name (`theorem Foo.bar` in a module)
  const esc = (x: string) => x.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const names = (src: string | null, name: string) => {
    if (!src) return false;
    const parts = name.split(".");
    return parts.slice(-4).some((_, i, tail) => new RegExp(`(^|[^\\w.'])${esc(tail.slice(i).join("."))}($|[^\\w'])`, "u").test(src));
  };
  const relOf = (mod: string) => `${path.join(...mod.split("."))}.lean`;
  // the run's own declarations, and those another run's move rewrote its paper to use (`used_by`)
  const decls: Array<{ name: string; rel: string }> = [];
  const ledger = JSON.parse((await text(toolkitRoot, path.join("doc", "ledger.json"))) ?? "{}") as { declarations?: Array<{ name?: string; module?: string; origin?: { slug?: string }; used_by?: string[] }> };
  for (const d of ledger.declarations ?? []) {
    if (!d.name || !d.module || (d.origin?.slug !== slug && !(d.used_by ?? []).includes(slug))) continue;
    const e = { name: d.name, rel: relOf(d.module) };
    if (names(await text(toolkitRoot, e.rel), e.name)) decls.push(e);
  }
  // (the ledger covers the run's own moves, a new module included; the paper's imports add what other
  // runs' moves rewrote it to import — best effort: a run state that cannot be read adds none)
  const mods = new Set<string>();
  const { loadState } = await import("../state.js");
  const sub = await loadState(toolkitRoot, slug).then((st) => st.lean_subdir, () => null);
  const paperDir = sub ? path.join(toolkitRoot, sub) : null;
  const importRe = new RegExp(`^\\s*(?:public\\s+)?(?:meta\\s+)?import\\s+(?:all\\s+)?(${t.lib}(?:\\.[\\w']+)*)`, "gmu");
  const walk = async (dir: string): Promise<void> => {
    for (const e of await readdir(dir, { withFileTypes: true }).catch(() => [])) {
      if (e.isDirectory() && e.name !== "tmp") await walk(path.join(dir, e.name));
      else if (e.isFile() && e.name.endsWith(".lean")) for (const m of (await readFile(path.join(dir, e.name), "utf8").catch(() => "")).matchAll(importRe)) mods.add(m[1]!);
    }
  };
  if (paperDir) await walk(paperDir);
  const imports = [...mods].filter((m) => existsSync(path.join(toolkitRoot, relOf(m))));
  return async (ws) => [
    ...imports.filter((m) => !existsSync(path.join(ws, relOf(m)))),
    ...(await Promise.all(decls.map(async (d) => (names(await text(ws, d.rel), d.name) ? null : d.name)))).filter((x): x is string => !!x),
  ];
}


/** A safe point of a run with a workspace (a stage's start): re-pinned to the current generation.
 *  A failure keeps the generation it has (logged). Nothing for a run without one. */
export async function refreshRunWorkspace(log: (line: string) => void = (l) => console.log(l)): Promise<void> {
  const ws = process.env[LEAN_WS_ENV];
  if (!ws) return;
  const pin = await readPin(ws);
  if (!pin) return log(`[workspace] ${ws} has no pin (.pf-gen): left as it is`);
  try {
    await ensureWorkspace(pin.toolkit, pin.slug, { localRoot: pin.local, log });
    // the current generation behind the clean toolkit: a stamping process that does not publish
    // (older code), or a publish still running — the workspace lags the shared tree meanwhile
    const { stampedClean } = await import("./build_mutex.js");
    const [cur, clean] = await Promise.all([currentGeneration(pin.toolkit), stampedClean(pin.toolkit)]);
    if (cur && "sig" in clean && clean.sig !== cur.sig) log(`[workspace] ${pin.slug}: generation ${cur.gen} is behind the toolkit's clean state (not published yet): the workspace lags the shared tree`);
  } catch (err) {
    log(`[workspace] ${pin.slug}: kept generation ${pin.gen} (${err instanceof Error ? err.message : String(err)})`);
  }
}

// ─── release (see the header) ────────────────────────────────────────────────────

/** A settled run's marker (`batch_orch.mjs` writes it, `{at, host, phase}`): its workspaces may go, on every machine. */
export const RELEASED_MARKER = "workspace_released.json";
/** (the toolkit's runs directory: `paths.runsRoot`) */
const runDirOf = (toolkitRoot: string, slug: string) => path.join(toolkitRoot, "runs", slug);
export const releasedMarker = (toolkitRoot: string, slug: string) => path.join(runDirOf(toolkitRoot, slug), "logs", RELEASED_MARKER);
/** The first `ensureWorkspace` of a process sweeps the machine's `ws/` (tests reset it). */
export const WORKSPACE_SWEEP = { done: false };
const TRASH = ".trash-";

/** The run a workspace directory is of: `<slug>`, `<slug>.promo`, `study_<slug>__<id>.promo`. */
export function ownerOf(name: string): string | null {
  if (name.startsWith(".") || !/^[A-Za-z0-9._-]+$/.test(name)) return null;
  if (!name.endsWith(".promo")) return name;
  const run = name.slice(0, -".promo".length);
  return /^study_(.+)__[^_].*$/.exec(run)?.[1] ?? run;
}

const finishedPhase = async (toolkitRoot: string, slug: string) =>
  ["done", "failed"].includes((await readJson<{ verify?: { phase?: string } }>(path.join(runDirOf(toolkitRoot, slug), "state.json")))?.verify?.phase ?? "");

/** Why run `slug`'s workspaces `names` (under `<local>/ws/`) are in use, or null: its runner or a study of it
 *  beats (`logs/.run.active`), an apply of it lives (`proposals/apply_*.pid`), a promotion workspace's own lock
 *  is held (`.pf-promo.flock`), a journal of its moves or its studies' is on file (in the run records, or a
 *  promotion workspace's own `.pf-promo/`), or the toolkit's commit journal names one of them. `at`: where a workspace is now (one moved into the trash), else `<local>/ws/<name>`. */
export async function releaseBusy(
  toolkitRoot: string, slug: string, local: string, names: readonly string[], at: ReadonlyMap<string, string> = new Map(),
  /** (2026-11-11) one study's promotion workspace at its step's end (`releaseStudyPromo`): that study's records
   *  alone, and its heartbeat held by this very process (the step ending) no use of it. */
  study?: string,
): Promise<string | null> {
  const { heartbeatLiveness } = await import("./run_heartbeat.js");
  const run = runDirOf(toolkitRoot, slug);
  const proposals = path.join(run, "proposals");
  if (!study) {
    const hb = heartbeatLiveness(path.join(run, "logs", ".run.active"));
    if (hb.live) return `its runner is live (${hb.elsewhere ? `on ${hb.elsewhere}` : `pid ${hb.pid}`})`;
    for (const f of (await readdir(proposals).catch(() => [] as string[])).filter((f) => /^apply_.*\.pid$/.test(f))) {
      const a = heartbeatLiveness(path.join(proposals, f));
      if (a.live) return `an apply is live (${f}: ${a.elsewhere ? `on ${a.elsewhere}` : `pid ${a.pid}`})`;
    }
  }
  const studies = study ? [study] : (await readdir(path.join(toolkitRoot, "runs")).catch(() => [] as string[])).filter((d) => ownerOf(`${d}.promo`) === slug && d.startsWith("study_"));
  // (a study run on its own: `paperformalizer study` takes the runner's heartbeat, 2026-11-10)
  for (const d of studies) {
    const s = heartbeatLiveness(path.join(toolkitRoot, "runs", d, "logs", ".run.active"));
    if (s.live && !(study && !s.elsewhere && s.pid === process.pid)) return `study ${d} is live (${s.elsewhere ? `on ${s.elsewhere}` : `pid ${s.pid}`})`;
  }
  const journals = [...(study ? [] : [path.join(proposals, "move_journal.json"), path.join(proposals, "move_batch_journal.json")]),
    ...studies.flatMap((d) => ["coordinate_journal.json", "coordinate_batch_journal.json"].map((j) => path.join(toolkitRoot, "runs", d, j)))];
  for (const j of journals) if (await lexists(j)) return `a journal is on file (${path.relative(toolkitRoot, j)})`;
  // a promotion workspace in use: its own lock held (`commit.withPromoWorkspace`; it moves with the directory)
  const { commitJournalFile, flockFree } = await import("./commit.js");
  for (const n of names.filter((n) => n.endsWith(".promo"))) {
    if (!(await flockFree(path.join(at.get(n) ?? path.join(local, "ws", n), ".pf-promo.flock")))) return `ws/${n} is in use (its .pf-promo.flock is held)`;
  }
  // a promotion's own journals (`local_moves.ts`, `local_coordinate.ts`): in its workspace, `<P>/.pf-promo/`
  for (const n of names.filter((n) => n.endsWith(".promo"))) {
    const priv = path.join(at.get(n) ?? path.join(local, "ws", n), path.relative(path.join(local, "ws", n), workspacePath(toolkitRoot, n, local)), ".pf-promo");
    const j = (await readdir(priv).catch(() => [] as string[])).find((f) => /journal.*\.json$/.test(f));
    if (j) return `a journal is on file (ws/${n}/…/.pf-promo/${j})`;
  }
  const cj = await readJson<{ id?: string; dir?: string }>(commitJournalFile(toolkitRoot));
  if (cj || (await lexists(commitJournalFile(toolkitRoot)))) {
    const ws = cj?.dir ? (await readJson<{ ws?: string }>(path.join(cj.dir, "manifest.json")))?.ws : undefined;
    if (!ws) return `a toolkit commit is on file (${commitJournalFile(toolkitRoot)}) whose workspace cannot be read`;
    const named = names.find((n) => { const rel = path.relative(path.join(local, "ws", n), path.resolve(ws)); return rel === "" || (!rel.startsWith("..") && !path.isAbsolute(rel)); });
    if (named) return `toolkit commit ${cj?.id ?? "?"} on file was prepared in ws/${named}`;
  }
  return null;
}

/** `<local>/ws/<name>` renamed to `<local>/ws/.trash-<name>-<pid>` (one rename: a workspace half removed is
 *  never seen as one); its new path, or null when it is gone already. */
async function toTrash(local: string, name: string): Promise<string | null> {
  const from = path.join(local, "ws", name);
  let to = path.join(local, "ws", `${TRASH}${name}-${process.pid}`);
  if (await lexists(to)) to = `${to}-${Date.now()}`;
  return rename(from, to).then(() => to, (err: NodeJS.ErrnoException) => { if (err.code === "ENOENT") return null; throw err; });
}

/** Each step of a release (tests replace it). */
export const RELEASE_STEP = { at: async (_step: "checked"): Promise<void> => {} };

/** Run `slug`'s workspaces `names`, in no use (`releaseBusy`), moved into the trash — and looked at again there: a
 *  runner or a journal that came between the look and the rename (2026-11-10) puts them back. The trash's paths, or why none. */
async function trashUnused(root: string, slug: string, local: string, names: readonly string[], study?: string): Promise<{ trashed: string[]; why?: string }> {
  const why = await releaseBusy(root, slug, local, names, new Map(), study);
  if (why) return { trashed: [], why };
  await RELEASE_STEP.at("checked");
  const moved = new Map<string, string>();
  for (const n of names) { const t = await toTrash(local, n); if (t) moved.set(n, t); }
  const again = await releaseBusy(root, slug, local, names, moved, study);
  if (!again) return { trashed: [...moved.values()] };
  // (one made anew meanwhile stays: its old copy is the next sweep's)
  for (const [n, t] of moved) await rename(t, path.join(local, "ws", n)).catch(() => {});
  return { trashed: [], why: `${again} — seen once renamed: put back` };
}

/** Run `slug`'s workspaces on this machine removed (`ws/<slug>`, `ws/<slug>.promo`, `ws/study_<slug>__*.promo`),
 *  unless they are in use (`releaseBusy`: kept, and said), and its paper's `tmp/` (`releasePaperTmp`). What was
 *  removed, or why nothing was. */
export async function releaseWorkspaces(
  toolkitRoot: string, slug: string, log: (line: string) => void = (l) => console.log(l), opts: { localRoot?: string } = {},
): Promise<{ removed: string[]; kept?: string; tmp?: string }> {
  const r = await releaseLocal(toolkitRoot, slug, log, opts);
  const tmp = await releasePaperTmp(path.resolve(toolkitRoot), slug, log).catch((err) => {
    log(`[workspace] ${slug}: its paper's tmp/ not removed (${err instanceof Error ? err.message : String(err)})`);
    return null;
  });
  return tmp ? { ...r, tmp } : r;
}

/** (2026-11-11) A released run's agents' scratch in the shared tree, `<its paper>/tmp` (`PAPER_TMP_DIR`: 17 GB
 *  and 235k files in 222 papers, one 3.3 GB), removed. No signature reads it (`toolkitSignature`: the library, its
 *  path dependencies, the project files) nor any generation (`lean_workspace.sh pack`: the library and the root's
 *  modules), and every build, scan and review of a paper leaves it out. Never while the run is in use
 *  (`releaseBusy`); renamed into the trash first. Its path, or null (none, or kept). */
async function releasePaperTmp(root: string, slug: string, log: (line: string) => void): Promise<string | null> {
  const { loadState } = await import("../state.js");
  const sub = await loadState(root, slug).then((st) => st.lean_subdir, () => null);
  if (!sub) return null;
  const { paperTmpDir } = await import("../paths.js");
  const tmp = paperTmpDir(root, sub);
  if (!(await lexists(tmp))) return null;
  const why = await releaseBusy(root, slug, "", []);
  if (why) {
    log(`[workspace] ${slug}: its paper's tmp/ kept — ${why}`);
    return null;
  }
  // (2026-11-11) renamed away first, as a workspace: a run restarted during a long removal makes a tmp/ of its own,
  // never removed with this one. Not beside it: every walk of a paper skips `tmp` alone, and would read a trash's
  // `.lean` files as the paper's — into the toolkit's own `.lake/paperformalizer/trash/` (one disk)
  const trash = path.join(root, ".lake", "paperformalizer", "trash", `${slug}-tmp-${process.pid}-${Date.now()}`);
  await mkdir(path.dirname(trash), { recursive: true });
  const gone = await rename(tmp, trash).then(() => trash, (err: NodeJS.ErrnoException) => {
    if (err.code === "ENOENT") return null;
    if (err.code === "EXDEV") return tmp; // (another disk: removed where it is)
    throw err;
  });
  if (!gone) return null;
  await rm(gone, { recursive: true, force: true }).catch((err) => log(`[workspace] ${gone} not removed (${err instanceof Error ? err.message : String(err)}): remove it by hand`));
  log(`[workspace] ${slug}: removed its paper's scratch ${path.relative(root, tmp)}`);
  return tmp;
}

async function releaseLocal(
  toolkitRoot: string, slug: string, log: (line: string) => void, opts: { localRoot?: string },
): Promise<{ removed: string[]; kept?: string }> {
  const root = path.resolve(toolkitRoot);
  let local: string;
  try { local = opts.localRoot ?? localLeanRoot(root); } catch (err) {
    log(`[workspace] ${slug}: nothing released (${err instanceof Error ? err.message : String(err)})`);
    return { removed: [], kept: "no local Lean root" };
  }
  const names = (await readdir(path.join(local, "ws")).catch(() => [] as string[])).filter((n) => ownerOf(n) === slug).sort();
  if (names.length === 0) {
    log(`[workspace] ${slug}: no workspace on this machine`);
    return { removed: [] };
  }
  const { trashed, why } = await trashUnused(root, slug, local, names);
  if (why) {
    log(`[workspace] ${slug}: workspaces kept — ${why}`);
    return { removed: [], kept: why };
  }
  for (const t of trashed) await rm(t, { recursive: true, force: true }).catch((err) => log(`[workspace] ${t} not removed (${err instanceof Error ? err.message : String(err)}): the next sweep removes it`));
  log(`[workspace] ${slug}: released ${names.map((n) => `ws/${n}`).join(", ")} (${local})`);
  return { removed: names };
}

/** (2026-11-11) Study `studyRun`'s promotion workspace on this machine (`ws/<studyRun>.promo`) removed once its
 *  coordinate step ended for good (committed, refused or halted: `substrate/pipeline.ts`) — it stayed until its
 *  paper's run was released (31 idle ones held 77 GB on one machine). A retry keeps it (the step goes on). The checks
 *  of `releaseWorkspaces` (its lock, its journals, a commit prepared in it, the study's heartbeat but this process's)
 *  and its trash rename; kept, and said, when in use. A later run of the study makes it anew. */
export async function releaseStudyPromo(
  toolkitRoot: string, studyRun: string, log: (line: string) => void = (l) => console.log(l), opts: { localRoot?: string } = {},
): Promise<{ removed: string[]; kept?: string }> {
  const root = path.resolve(toolkitRoot);
  const name = `${studyRun}.promo`;
  const owner = ownerOf(name);
  let local: string;
  try { local = opts.localRoot ?? localLeanRoot(root); } catch { return { removed: [] }; }
  if (!owner || !(await lexists(path.join(local, "ws", name)))) return { removed: [] };
  const { trashed, why } = await trashUnused(root, owner, local, [name], studyRun);
  if (why) {
    log(`[workspace] ${studyRun}: its promotion workspace kept — ${why}`);
    return { removed: [], kept: why };
  }
  for (const t of trashed) await rm(t, { recursive: true, force: true }).catch((err) => log(`[workspace] ${t} not removed (${err instanceof Error ? err.message : String(err)}): the next sweep removes it`));
  log(`[workspace] ${studyRun}: its step ended — released ws/${name} (${local})`);
  return { removed: [name] };
}

/** (2026-11-11) The operator's own workspaces, of no run (`ensureWorkspace(root, "library-check")` in the
 *  daily library check; the gardener's): not stray, never said. */
const OPS_WORKSPACES = new Set(["library-check", "_garden"]);

/** This machine's `ws/` swept: the workspaces of runs marked released and still finished, in no use (`releaseBusy`),
 *  removed, and `.trash-*` left behind; never `keep` (the one being ensured) and never a directory of no run
 *  (no `runs/<slug>/state.json`: only said). The removal runs detached (`rm -rf`); what was trashed is returned. */
export async function sweepWorkspaces(toolkitRoot: string, local: string, keep: string, log: (line: string) => void): Promise<string[]> {
  const root = path.resolve(toolkitRoot);
  const wsRoot = path.join(local, "ws");
  const trash: string[] = [];
  const byOwner = new Map<string, string[]>();
  const stray: string[] = [];
  for (const n of await readdir(wsRoot).catch(() => [] as string[])) {
    if (n.startsWith(TRASH)) { trash.push(path.join(wsRoot, n)); continue; }
    const owner = ownerOf(n);
    if (n === keep || !owner) continue;
    if (!(await lexists(path.join(runDirOf(root, owner), "state.json")))) { if (!OPS_WORKSPACES.has(owner)) stray.push(n); continue; }
    byOwner.set(owner, [...(byOwner.get(owner) ?? []), n]);
  }
  if (stray.length) log(`[workspace] no run state for ${stray.map((n) => `ws/${n}`).join(", ")} (${wsRoot}): left (remove by hand)`);
  const released: string[] = [];
  for (const [owner, names] of byOwner) {
    if (!(await lexists(releasedMarker(root, owner))) || !(await finishedPhase(root, owner))) continue;
    const r = await trashUnused(root, owner, local, names).catch((err) => ({ trashed: [], why: err instanceof Error ? err.message : String(err) }));
    if (r.why) { log(`[workspace] ${owner}: released, but its workspaces are kept — ${r.why}`); continue; }
    trash.push(...r.trashed);
    released.push(...names);
  }
  if (released.length) log(`[workspace] swept the workspaces of released runs: ${released.map((n) => `ws/${n}`).join(", ")}`);
  if (trash.length) {
    const c = spawn("rm", ["-rf", "--", ...trash], { detached: true, stdio: "ignore" });
    c.on("error", () => { /* the next sweep */ });
    c.unref();
  }
  return released;
}

export const TOOLKIT_GEN_USAGE =
  "Usage: paperformalizer toolkit-gen publish|status [--toolkit <path>]\n" +
  "       paperformalizer toolkit-gen ensure|release <slug> [--toolkit <path>]\n" +
  "  publish: turns generations on (the toolkit's .lake/paperformalizer/gens/) and publishes the toolkit, which must be\n" +
  "  stamped clean, as the next generation (every clean stamp publishes one from then on); status: the current one;\n" +
  "  ensure: run <slug>'s workspace on this machine, made or re-pinned to the current generation (prints its path);\n" +
  "  release: run <slug>'s workspaces on this machine removed (its own and its promotions'), and its paper's tmp/, unless in use";

/** `paperformalizer toolkit-gen …` (the generations behind the runs' workspaces). */
export async function runToolkitGenCli(argv: string[], log: (m: string) => void = (m) => console.log(m)): Promise<void> {
  const i = argv.indexOf("--toolkit");
  const explicit = i >= 0 ? argv[i + 1] ?? null : null;
  const rest = i >= 0 ? [...argv.slice(0, i), ...argv.slice(i + 2)] : argv;
  const [which, slug] = rest;
  const { loadToolkitConfig } = await import("../toolkit/config.js");
  const root = loadToolkitConfig({ explicit }).toolkitRoot;
  if (which === "status") {
    log(JSON.stringify({ gens: existsSync(gensDir(root)), current: await currentGeneration(root) }));
    return;
  }
  if (which === "ensure" && slug) {
    const r = await ensureWorkspace(root, slug, { log });
    log(r.path);
    return;
  }
  if (which === "release" && slug) {
    await releaseWorkspaces(root, slug, log);
    return;
  }
  if (which !== "publish") throw new Error(TOOLKIT_GEN_USAGE);
  await mkdir(gensDir(root), { recursive: true });
  if (!rest.includes("--locked")) {
    // by hand: the same publisher, under the publishers' lock, waited for
    const code = await new Promise<number>((resolve) => {
      const c = spawn("flock", publisherArgs(root, null), { stdio: "inherit", env: publisherEnv() });
      c.on("error", () => resolve(127));
      c.on("exit", (code) => resolve(code ?? 1));
    });
    if (code !== 0) throw new Error(`toolkit-gen publish exited ${code}${code === 1 ? " (another publish is running?)" : ""}`);
    return;
  }
  const j = rest.indexOf("--sig");
  const stamped = j >= 0 ? rest[j + 1] ?? null : null;
  const { stampedClean, withLakeBuildLock } = await import("./build_mutex.js");
  // Under a hold beside papers' builds, never beside a write of the toolkit: the clean toolkit as it
  // stands now — none when it moved on and is not clean (its next clean stamp publishes); again
  // while a newer clean stamp came meanwhile (its own publisher found this one running)
  for (let i = 0; i < 3; i++) {
    const g = await withLakeBuildLock(root, async () => {
      const c = await stampedClean(root);
      if ("why" in c) {
        log(`[workspace] the toolkit is not stamped clean as it stands (${c.why}): nothing published`);
        return null;
      }
      if (stamped && i === 0 && c.sig !== stamped) log("[workspace] the toolkit moved on since its stamp: its clean state as it stands is published");
      const cur = await currentGeneration(root);
      return cur?.sig === c.sig ? null : publishGeneration(root, c.sig, log);
    }, "toolkit-gen publish", log, undefined, { toolkitOnly: true });
    if (!g) break;
  }
  const cur = await currentGeneration(root);
  log(`current generation: ${cur?.gen ?? "none"}${cur ? ` (${cur.sig.slice(0, 12)}…)` : ""}`);
}
