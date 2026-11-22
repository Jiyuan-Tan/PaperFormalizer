/**
 * Promotions prepared locally, committed briefly: every round-B apply's moves and corollaries (`proposals/local_moves.ts`) and every
 * study's coordinate step (`substrate/local_coordinate.ts`); `paperformalizer toolkit-commit`
 * settles one by hand.
 *
 * PREPARE (no shared lock; `P`'s own, `withPromoWorkspace`, from the prepare to its last use). A
 * promotion works in a private workspace `P` of its own on local disk
 * (`prepareWorkspace`: `ensureWorkspace(toolkit, "<slug>.promo")`, pinned to the published
 * generation `N` and RESET to it — re-pinned even when already on `N`, then checked: every pinned
 * file is `N`'s — then DETACHED: `Papers/` holds copies of the papers it writes and nothing else, the
 * papers' barrel is a copy, `doc/` is copies (its largest stores left out, `DOC_COPY_MAX_BYTES`); no
 * lock file of the shared tree is linked: the code run in `P` takes `P`'s own. No path under `P`'s
 * `Papers/`, `doc/` or library leads into the shared tree, so no write there — in place or by
 * rename — can reach it (`runs/` is the shared one on purpose: a run's own records);
 * `prepareCommit` refuses a paper or doc file written that was not copied. Once its verdict is in, `prepareCommit` — holding `P`'s build lock from Lake's check to the
 * pack, so the generation is what Lake vouched for — writes the commit directory `C`
 * (`.lake/paperformalizer/commits/<id>/`), complete and self-contained:
 *   - `manifest.json` (written last): the base `{gen, sig}`, every source written or removed with
 *     its sha256 before and after, every build file that differs from generation `N` with its size
 *     and sha256, the ledger declarations (by default those `P`'s private ledger gained), one
 *     record per run, its read set `reads` (2026-11-11): the sha256 of every file its verdict read
 *     that it does not write (`readSetOf`; none when that cannot be vouched for) — only a PAPER-ONLY
 *     commit's is used (every source under `Papers/`, no build file, no declaration) — and the
 *     declarations it adds with their hashes (`adds`, when the caller knows them);
 *   - `src/` and `orig/`: the sources' new bytes and the bytes they had (`orig/`: a manual undo);
 *   - `delta.tar`: those build files (`.lake/build`, mtimes kept);
 *   - `gen.tar.zst`: generation `N+1`, `P` packed (`lean_workspace.sh pack`).
 *
 * COMMIT (`commitToolkit`), inside the promotion lock and an exclusive Lake hold, taken as old code
 * takes them (`withPromotionLock` then `withLakeBuildLock`; a commit bound to its base gives up its
 * place in the queue, `base-moved`, once `CURRENT` is not its base — never when the journal names it):
 *   1. a journal on file (`.lake/paperformalizer/commit.json`): that commit finished first, rolled
 *      forward (`recover`; it is this commit's own: landed); a commit's flux session no journal
 *      names (it died before its commit point: nothing written) closed; old prepared commits swept
 *      (never this one);
 *   2. the base checked: `CURRENT` is `N` — or, for a paper-only commit with `reads` (the off-switch
 *      `strict-base` not on file), any later generation `N+k` — the live `toolkitSignature` is
 *      `CURRENT.sig` (neither a `doubt:`), no flux session is open, every file to be written still has
 *      its `before` sha, and on `N+k` every file of `reads` its sha. Generation moved (a strict
 *      commit) or a file changed: `base-moved`; the tree not `CURRENT` but stamped clean: published,
 *      then a strict commit is `base-moved`, a paper-only one goes on; else `wait`;
 *   3. `C` checked complete: every new source's bytes and every build file (`delta.tar` unpacked
 *      beside the tree, each re-hashed), `orig/`, the archive — before anything is written;
 *   4. a flux session opened (`openFluxSession`, the commit's id): old code honours it — no shared
 *      hold begins, nothing is stamped clean, no generation published — until step 9 closes it;
 *   5. the journal written (the commit point), its base the generation committed onto, with the
 *      toolkit's sources' states (`toolkitSources`);
 *   6. the sources installed (temp file + rename);
 *   7. the build files renamed into place, mtimes kept: outputs, then `.hash` files, then `.trace`
 *      files last; re-hashed against the manifest;
 *   8. Lake judges: `lake build --no-build <targets>` in the shared tree exits 0, else (logged loudly)
 *      the real `lake build <targets>`; that failing STOPS THE LINE: the journal stays (marked
 *      `stopped`), the flux session stays, `CURRENT` stays `N`, every commit after returns `wait`
 *      until `toolkit-commit undo` or `toolkit-commit recover` (the owner's decision: no automatic
 *      undo). A build KILLED (its time cap) is no verdict: the journal stays unstopped (`wait`), and
 *      the next holder rolls forward;
 *   9. the ledger's declarations appended (under its own store lock; idempotent); the clean stamp for
 *      the new signature; the generation published (`C`'s archive renamed into `gens/`,
 *      `CURRENT.json` last — after a real build, or off its base, the shared tree packed instead: a
 *      paper-only commit's signature is `CURRENT`'s, so nothing is published), and its `adds` beside
 *      the new generation (`gens/adds/<gen>.json`); the flux session
 *      closed; each run's landed record (`runs/<slug>/proposals/landed/<id>.json`); the journal and
 *      `C` removed.
 *
 * ADDITIVE commits (2026-11-11, step 2; `additiveShape`): a toolkit commit whose toolkit sources are
 * new modules, but for the flat barrels (the modules the library's root imports: `Toolkit/Foundations.lean`,
 * `Toolkit/Tricks.lean`) and `doc/toolkit_index.json`, whose build files are those modules' or the
 * barrel chain's (a barrel, the root), that removes nothing and carries `reads` and `adds`, lands on a
 * later generation `N+k` without a rebase (the off-switch `strict-base` makes it strict too). At step
 * 2, before the commit point, each check failing is `base-moved`: its new files absent (their `before`
 * null), its `reads` unchanged (papers it rewrites keep their `before`), its barrels' and index's
 * changes nothing but additions (else strict), the names it adds absent from the live index and no
 * new `nameProblems` against what was added since `N`, every generation in `(N, N+k]` with an adds
 * record (`gens/adds/<gen>.json`; none — gardening, flux, the publisher, old code — strict) none of
 * whose names or statement hashes is one of its own, and Lean importing the merged barrels with its
 * new modules' outputs first on the path (`COMMIT_PRECHECK`: an import clash the index does not list,
 * such as an auto-named instance; nothing shared written). Then `C` is rebased onto `N+k`
 * (`rebaseCommit`): the barrels merged (`insertImportSorted` of its imports into the live bytes), the
 * index merged (the union), `src/`/`orig/` the merged and live bytes, the barrel chain's build files
 * dropped, the archive removed (never used), `manifest.json` rewritten (`base` `N+k`, `rebased`), the
 * prepared one kept as `manifest.prepared.json`. Its install then builds for real (`lake build` of
 * the targets: the barrels and the root rebuild, its modules' outputs installed), `--no-build` judges,
 * the shared tree is packed. The roll-forward, `undo` and `honourCommit` are unchanged: a rebased
 * manifest is an ordinary one, based on `N+k`.
 *
 * RECOVERY rolls forward, never back, and never over a moved base: every toolkit source whose state
 * changed since the commit point must be one of the commit's, with its `before` or `after` bytes —
 * anything else stops the line. Sources then go to their `after` bytes (a paper or doc file edited
 * meanwhile by its run is left and named in the landed record), the real `lake build` of the targets
 * runs (the half-installed delta is not trusted), the stamp, the shared tree packed
 * (`publishGeneration`), the flux session closed.
 *
 * Trust: `held: true` (a caller that holds both locks already) and `held: "promotion"` (it holds the
 * promotion lock: the commit takes the exclusive Lake hold itself) are the caller's word, not checked. A
 * commit's flux session is closed only by its commit (`clear`, `undo`, the roll-forward); an old
 * `toolkit-flux off` without `--id` can close it — operators always pass `--id`.
 *
 * Invariants: nothing is installed unless the live toolkit is exactly `CURRENT` and every file the
 * verdict read has the bytes it had on the generation the verdict was reached on (I1′, 2026-11-11:
 * was I1, "only on its base"); a commit that writes the toolkit read all of it (its barrel, the
 * duplicate and name checks, the lints, the index), so for it I1′ is I1 — generation equality. A
 * paper-only commit read its papers, their import closure and the pinned top-level files (`reads`);
 * a Lean build and the statement scan are a function of those, the toolchain and the manifest. The
 * stamp and `CURRENT` are written only after Lake itself found the shared tree up to date (I2);
 * `CURRENT` flips by one rename after its archive exists (I3); the shared tree is written only
 * inside the locks, after a verdict (I4).
 */
import { spawn, type ChildProcessWithoutNullStreams } from "node:child_process";
import { createHash, randomBytes } from "node:crypto";
import { createReadStream, existsSync, statSync } from "node:fs";
import { cp, lstat, mkdir, readdir, readFile, rename, rm, stat, unlink, writeFile } from "node:fs/promises";
import path from "node:path";
import { execFile } from "node:child_process";
import { fileURLToPath } from "node:url";
import { PAPER_TMP_DIR } from "../paths.js";
import type { LedgerDeclaration } from "../toolkit/ledger.js";
import {
  closeFluxSession, fluxSessionsOpen, LAKE_SHIM_DIR, LEAN_WS_ENV, LOCK_HOST, openFluxSession, recordToolkitClean, stampedClean, toolkitFluxWhy,
  withinCommit, withLakeBuildLock, withPromotionLock, withPromotionLockUntil, withSharedTree,
} from "./build_mutex.js";
import { changedSources, dependencyStates, headerImports, isDoubt, READ_CLOSURE_MAX, readClosure, toolkitLayout, toolkitScope, toolkitSignature, toolkitSources, type ToolkitLayout } from "./build_inputs.js";
import { recordCommitEvent } from "./lock_holds.js";
import { writeJsonAtomic, writeTextAtomic } from "./json_atomic.js";
import { isLeanModuleFile, parseLeanImport } from "./lean_syntax.js";
import { insertImportSorted } from "../toolkit/barrels.js";
import { addsRecordFile, currentGeneration, ensureGenerations, ensureWorkspace, gensDir, leanWorkspaceSh, localLeanRoot, publishGeneration, workspacePath } from "./workspace.js";

export const commitsDir = (root: string) => path.join(root, ".lake", "paperformalizer", "commits");
export const commitJournalFile = (root: string) => path.join(root, ".lake", "paperformalizer", "commit.json");
/** The off-switch (2026-11-11): while on file, every commit lands only on its base (I1), whatever
 *  its read set; read under the locks at each commit, so running processes follow it. */
export const strictBaseSwitch = (root: string) => path.join(root, ".lake", "paperformalizer", "strict-base");
/** (2026-11-11, step 2) The off-switch of additive landing alone: while on file, no toolkit commit
 *  lands on a later generation as an additive one (paper-only commits still may); read under the
 *  locks at each commit, and before queueing for them. */
export const noAdditiveSwitch = (root: string) => path.join(root, ".lake", "paperformalizer", "no-additive");
/** (2026-11-11, step 2) The caps on what an additive commit runs under the locks: its import
 *  pre-check (over it: base-moved, before the commit point) and its real build of the targets
 *  (over it: killed, no verdict — see `land`). */
export const ADDITIVE_LIMITS = { precheckMs: 5 * 60_000, buildMs: 10 * 60_000 };
/** (2026-11-11, step 2) `commitToolkit` takes `recheck` (run under the locks): read off the module by
 *  callers that may meet an older one (compat 2026-11-11). */
export const COMMIT_RECHECK_UNDER_LOCK = true;
/** A prepared commit not committed (nor named by the journal) is removed after this. */
export const COMMIT_ORPHAN_MS = 24 * 60 * 60_000;
/** A commit's id, which names its flux session too (`build_mutex.ts`'s session ids). */
const COMMIT_ID_RE = /^commit[0-9a-z]+-[0-9a-f]{6}$/;
/** What a commit's flux session says it is (`fluxSessionsOpen`). */
const FLUX_WHAT = "toolkit-commit";

/** A source written (`after`) or removed (`after: null`), or added (`before: null`); sha256 hex. */
export interface SourceChange { rel: string; before: string | null; after: string | null }
/** A build file of the delta, relative to `.lake/build`. */
export interface BuildFile { rel: string; size: number; sha: string }
/** One run's record of what landed (today's `BatchRecord`), written at step 9. */
export interface CommitRecord { slug: string; record: unknown }
export interface CommitManifest {
  id: string;
  created: string;
  /** The workspace it was prepared in (information only). */
  ws: string;
  base: { gen: number; sig: string };
  /** What Lake must find up to date in the shared tree: the library, its path dependencies' and the exes. */
  targets: string[];
  sources: SourceChange[];
  build: BuildFile[];
  removedBuild: string[];
  ledger: LedgerDeclaration[];
  records: CommitRecord[];
  /** The papers' barrel: imports the workspace added, inserted at the commit into its bytes then
   *  (`insertImportSorted`) — never compared and swapped: a paper registered meanwhile stands. */
  barrel?: { rel: string; imports: string[] };
  /** A paper-only commit's read set (`readSetOf`; 2026-11-11): what its verdict read and it does not
   *  write, relative to the toolkit, with its sha256 then. Absent: it lands only on its base. */
  reads?: ReadFile[];
  /** The declarations it adds, with their statement hashes (the toolkit graph's), when its caller
   *  knows them (2026-11-11: recorded at step 9 for a later additive commit; inert now). */
  adds?: CommitAdd[];
  /** (2026-11-11, step 2) Rebased under the locks onto a later generation as an additive commit
   *  (`rebaseCommit`): the generation it was prepared on, and when. Its install builds for real. */
  rebased?: { from: { gen: number; sig: string }; at: string };
}
export interface CommitAdd { name: string; hash: string }
/** A file a commit's verdict read (a path dependency's: `../…`) and its sha256 then. */
export interface ReadFile { rel: string; sha: string }
export interface CommitJournal {
  id: string; base: { gen: number; sig: string }; next: number; dir: string; at: string; host: string; pid: number;
  /** The toolkit's sources' states at the commit point (`toolkitSources`): a roll-forward installs
   *  nothing over a base that moved since. */
  states: Record<string, string>;
  /** The line stopped: Lake could not build the shared tree from the committed sources. */
  stopped?: { at: string; why: string };
}
export type CommitOutcome =
  | { kind: "landed"; gen: number; slow: boolean; left: string[]; ms: Record<string, number>; additive?: boolean }
  | { kind: "base-moved"; why: string }
  | { kind: "wait"; why: string };

/** The Lake runs of a commit (tests replace it): `lake <args>` in `cwd`, the real lake (never the
 *  workers' shim), never a run's workspace. `code` null: killed (a time cap), no verdict. */
export const COMMIT_LAKE = {
  run: async (cwd: string, args: string[], cap: { maxTotalMs?: number } = {}): Promise<{ code: number | null; out: string }> => {
    const { spawnWithInactivityTimeout } = await import("../workers/spawn.js");
    const env: NodeJS.ProcessEnv = { ...process.env, PATH: (process.env.PATH ?? "").split(path.delimiter).filter((d) => path.resolve(d) !== LAKE_SHIM_DIR).join(path.delimiter) };
    delete env[LEAN_WS_ENV];
    const max = cap.maxTotalMs ?? 90 * 60_000;
    const r = await withSharedTree(() => spawnWithInactivityTimeout("lake", args, { cwd, env, inactivityTimeoutMs: Math.min(30 * 60_000, max), maxTotalMs: max }));
    const killed = r.killedDueToInactivity || r.killedDueToTotalTimeout === true || r.killedDueToLiveness != null || r.exitCode === null;
    return { code: killed ? null : r.exitCode, out: `${r.stdout}\n${r.stderr}` };
  },
};

/** The environment of a commit's Lean child in the shared tree: the real lake (never the workers'
 *  shim), never a run's workspace. */
const sharedTreeEnv = (): NodeJS.ProcessEnv => {
  const env: NodeJS.ProcessEnv = { ...process.env, PATH: (process.env.PATH ?? "").split(path.delimiter).filter((d) => path.resolve(d) !== LAKE_SHIM_DIR).join(path.delimiter) };
  delete env[LEAN_WS_ENV];
  return env;
};

/**
 * A library directory `out` that is the shared tree's `shared` (its `.lake/build/lib/lean`) with the
 * commit's staged outputs `delta` (`C/delta/lib/lean`) laid over it: Lean finds a module under the
 * FIRST path entry holding its root (`Toolkit/`), so the new modules cannot go on a path entry of
 * their own. Only the directories on the way to a staged file are made; every other entry is a link
 * to the shared tree's (nothing of it is written).
 */
export async function overlayLib(shared: string, delta: string, out: string, opts: { skip?: (rel: string) => boolean } = {}, rel = ""): Promise<void> {
  await mkdir(path.join(out, rel), { recursive: true });
  // (a staged file `skip` names — a barrel chain's output, built for the prepared barrel — is left out: the shared one stands)
  const mine = new Map((await readdir(path.join(delta, rel), { withFileTypes: true }).catch(() => []))
    .filter((e) => e.isDirectory() || !opts.skip?.(path.join(rel, e.name))).map((e) => [e.name, e] as const));
  for (const name of await readdir(path.join(shared, rel)).catch(() => [] as string[])) {
    if (!mine.has(name)) await replaceWithLink(path.join(shared, rel, name), path.join(out, rel, name));
  }
  for (const [name, e] of mine) {
    if (e.isDirectory()) await overlayLib(shared, delta, out, opts, path.join(rel, name));
    else await replaceWithLink(path.join(delta, rel, name), path.join(out, rel, name));
  }
}
/** `at` made a symbolic link to `target` (whatever was there removed). */
const replaceWithLink = async (target: string, at: string) => {
  const { symlink } = await import("node:fs/promises");
  await rm(at, { recursive: true, force: true });
  await symlink(target, at);
};

/** (2026-11-11, step 2) An additive commit's import pre-check (tests replace it): Lean elaborates
 *  `text` — the library's root with the merged barrels' imports in place of theirs — on Lake's
 *  `LEAN_PATH` of the shared tree, its library's entry replaced by the commit's staged outputs laid
 *  over it (`overlayLib`, in `C/precheck/lib`). The file goes in `C/precheck/`; `lean` writes no
 *  output; nothing shared is written. `code` 0: the imports load together; else (null: killed) the
 *  commit is not landed off its base. */
export const COMMIT_PRECHECK = {
  run: async (root: string, C: string, text: string, chain: readonly string[] = []): Promise<{ code: number | null; out: string }> => {
    const { spawnWithInactivityTimeout } = await import("../workers/spawn.js");
    const dir = path.join(C, "precheck");
    const t0 = Date.now();
    // (the whole pre-check under one cap: `ADDITIVE_LIMITS.precheckMs`)
    const left = () => Math.max(1000, ADDITIVE_LIMITS.precheckMs - (Date.now() - t0));
    try {
      await rm(dir, { recursive: true, force: true });
      await mkdir(dir, { recursive: true });
      const file = path.join(dir, "Precheck.lean");
      await writeFile(file, text);
      const env = sharedTreeEnv();
      const killed = (r: { killedDueToInactivity: boolean; killedDueToTotalTimeout?: boolean; killedDueToLiveness?: unknown; exitCode: number | null }) =>
        r.killedDueToInactivity || r.killedDueToTotalTimeout === true || r.killedDueToLiveness != null || r.exitCode === null;
      const e = await withSharedTree(() => spawnWithInactivityTimeout("lake", ["env", "printenv", "LEAN_PATH", "LEAN_SYSROOT"], { cwd: root, env, inactivityTimeoutMs: left(), maxTotalMs: left() }));
      if (killed(e) || e.exitCode !== 0) return { code: killed(e) ? null : e.exitCode, out: `lake env: ${e.stdout}\n${e.stderr}` };
      const [leanPath = "", sysroot = ""] = e.stdout.trim().split("\n");
      const lib = path.join(root, ".lake", "build", "lib", "lean");
      const entries = leanPath.split(path.delimiter).filter(Boolean);
      const { realpath } = await import("node:fs/promises");
      const real = async (p: string) => realpath(p).catch(() => path.resolve(p));
      const libReal = await real(lib);
      const at = (await Promise.all(entries.map(real))).indexOf(libReal);
      if (at < 0) return { code: 1, out: `the shared tree's library (${lib}) is not on Lake's LEAN_PATH (${leanPath.slice(0, 300)})` };
      const overlay = path.join(dir, "lib");
      const stale = new Set(chain);
      await overlayLib(lib, path.join(C, "delta", "lib", "lean"), overlay, { skip: (rel) => stale.has(moduleOfBuild(path.join("lib", "lean", rel)) ?? "") });
      entries[at] = overlay;
      const lean = sysroot ? path.join(sysroot, "bin", "lean") : "lean";
      const r = await withSharedTree(() => spawnWithInactivityTimeout(lean, [file], {
        cwd: root, env: { ...env, LEAN_PATH: entries.join(path.delimiter) }, inactivityTimeoutMs: left(), maxTotalMs: left(),
      }));
      return { code: killed(r) ? null : r.exitCode, out: `${r.stdout}\n${r.stderr}` };
    } finally {
      await rm(dir, { recursive: true, force: true }).catch(() => {});
    }
  },
};

/** Called at each step of a commit past its commit point (`journaled`, `sources`, `build-half`,
 *  `build-files`, `stamped`, `published`; and `rebased`, an additive commit's rebase, before it): tests throw there, and a rehearsal kills the process at the
 *  step `PAPERFORMALIZER_COMMIT_KILL_AT` names, to see the roll-forward recover it. */
export const COMMIT_STEP = {
  at: async (step: string): Promise<void> => {
    if (process.env.PAPERFORMALIZER_COMMIT_KILL_AT === step) process.kill(process.pid, "SIGKILL");
  },
};

const tail = (out: string, n = 12) => out.trim().split("\n").filter((l) => !/^(⚠|✔|info:|warning:|\s)/.test(l)).slice(-n).join("\n");
const exec = (cmd: string, args: string[], cwd?: string) => new Promise<void>((resolve, reject) => {
  execFile(cmd, args, { cwd, maxBuffer: 64 << 20 }, (err, _o, stderr) => (err ? reject(new Error(`${cmd} ${args[0]}: ${stderr.trim() || err.message}`)) : resolve()));
});

/** The sha256 of a file, or null when it is not there. */
async function shaOf(file: string): Promise<string | null> {
  return new Promise((resolve, reject) => {
    const h = createHash("sha256");
    createReadStream(file).on("error", (err: NodeJS.ErrnoException) => (err.code === "ENOENT" ? resolve(null) : reject(err)))
      .on("data", (d) => h.update(d)).on("end", () => resolve(h.digest("hex")));
  });
}

/** The regular files under `dir`, relative to it (symlinks not followed, `skip` relative paths left out). */
async function filesUnder(dir: string, skip: (rel: string) => boolean = () => false, rel = ""): Promise<string[]> {
  const out: string[] = [];
  for (const e of await readdir(path.join(dir, rel), { withFileTypes: true }).catch(() => [])) {
    const r = rel ? path.join(rel, e.name) : e.name;
    if (skip(r)) continue;
    if (e.isDirectory()) out.push(...(await filesUnder(dir, skip, r)));
    else if (e.isFile()) out.push(r);
  }
  return out;
}

const readJson = async <T>(file: string): Promise<T | null> => readFile(file, "utf8").then((t) => JSON.parse(t) as T, () => null);

/** `fn` holding `file`'s `flock` (the lock `lean_workspace.sh pin` and the lake shim take for a
 *  workspace's build; a promotion workspace's own, `withPromoWorkspace`), by a `flock` child that
 *  keeps it until `fn` is done. Held by another process: waited for, `waitS` at most (logged at the
 *  start and every `FLOCK_LOG_EVERY_S`), then a clear error (`busy.fail` makes it) — `fn` never runs
 *  without it. (A holder that dies releases it: the wait never outlives a live holder by much.) */
async function withFlock<T>(file: string, fn: () => Promise<T>, waitS = 1800, busy: { what?: string; log?: (line: string) => void; fail?: (why: string) => Error } = {}): Promise<T> {
  await mkdir(path.dirname(file), { recursive: true });
  const what = busy.what ?? file;
  let child = await holdFlock(file, ["-n"]);
  const t0 = Date.now();
  for (let turn = 0; !child; turn++) {
    const waited = (Date.now() - t0) / 1000;
    if (waited >= waitS) {
      const why = `${what}: ${file} still held by another process after ${waitS} s — gave up, nothing done`;
      throw busy.fail ? busy.fail(why) : new Error(why);
    }
    busy.log?.(turn === 0
      ? `[workspace] ${what}: ${file} is held by another process — waiting for it (${waitS} s at most)`
      : `[workspace] ${what}: still waiting for ${file} (${Math.round(waited / 60)} min of ${Math.round(waitS / 60)})`);
    child = await holdFlock(file, ["-w", String(Math.max(1, Math.ceil(Math.min(FLOCK_LOG_EVERY_S, waitS - waited))))]);
  }
  try {
    return await fn();
  } finally {
    const c = child;
    c.stdin.end();
    await new Promise<void>((resolve) => { if (c.exitCode !== null) resolve(); else c.on("exit", () => resolve()); });
  }
}

/** Whether `file`'s `flock` is free now (`holdFlock -n`, let go at once); a missing file is free and never
 *  made (2026-11-10: a release of a promotion workspace, `workspace.releaseBusy`). */
export async function flockFree(file: string): Promise<boolean> {
  if (!existsSync(file)) return true;
  // (a probe that fails — the file gone between the check and the spawn, flock missing — counts as
  // held: a release then keeps the workspace, never deletes one unchecked; audit note 2026-11-10)
  const child = await holdFlock(file, ["-n"]).catch(() => null);
  if (!child) return false;
  child.stdin.end();
  await new Promise<void>((resolve) => { if (child.exitCode !== null) resolve(); else child.on("exit", () => resolve()); });
  return true;
}

/** How often a wait for a `flock` held elsewhere is logged (`withFlock`). */
const FLOCK_LOG_EVERY_S = 600;
/** `flock`'s exit code when the lock is held elsewhere (`-E`). */
const FLOCK_BUSY = 75;
/** A `flock` child holding `file` (`how`: `-n`, or `-w <s>`), or null: held by another process. */
function holdFlock(file: string, how: readonly string[]): Promise<ChildProcessWithoutNullStreams | null> {
  const child = spawn("flock", [...how, "-E", String(FLOCK_BUSY), file, "-c", "echo held; exec cat >/dev/null"], { stdio: ["pipe", "pipe", "pipe"] });
  return new Promise((resolve, reject) => {
    let err = "";
    child.stdout.on("data", (d: Buffer) => { if (d.toString().includes("held")) resolve(child); });
    child.stderr.on("data", (d: Buffer) => { err += d.toString(); });
    child.on("error", reject);
    child.on("exit", (code) => (code === FLOCK_BUSY ? resolve(null) : reject(new Error(`flock ${file} exited ${code}: ${err.trim()}`))));
  });
}

// ─── prepare ──────────────────────────────────────────────────────────────────────────────────────

/** A detached workspace's record (`P/.pf-detach.json`): the papers it writes and the sha256, at
 *  detach, of every file it copied that a commit may install (relative to the toolkit). */
interface Detached { papers: string[]; files: Record<string, string>; docs: Record<string, string> }
const DOC_PRIVATE = ["ledger.json", "toolkit_index.json"] as const;
/** Of the private doc copies, what a commit installs (the ledger gets declarations appended instead). */
const DOC_COMMITTED = ["toolkit_index.json"];
/** A lock file of the shared tree (`.lake-build.lock`, `.toolkit-promote.lock`, `.toolkit-ledger.lock`,
 *  their `.lock` directories, `.lake-build.flock`): never linked into a promotion's workspace, whose
 *  code takes its locks there (`withLakeBuildLock(<P>)`): those are the workspace's own. */
const LOCKISH = /\.(f?lock)(\.lock)?$/;

/** A promotion's private workspace `P` for run `slug` on this machine: pinned to the current
 *  generation (made, or re-pinned: its own paper build is kept), reset to it, checked, and detached
 *  (see the header): `papers` (`Foo` or `Papers.Foo`) are copied afresh from the shared tree.
 *  Only under `P`'s lock (`withPromoWorkspace`): a prepare resets `P`. */
export async function prepareWorkspace(
  toolkitRoot: string, slug: string, papers: readonly string[],
  opts: {
    localRoot?: string; log?: (line: string) => void;
    /** false: never seeded from the run's own workspace (`seedFromRun`). */
    seed?: boolean;
    /** How long the seed waits for the run's workspace's build lock (`SEED_LOCK_WAIT_S`). */
    seedWaitS?: number;
  } = {},
): Promise<{ path: string; gen: number; repinned: boolean; ms: number; seeded: string[] }> {
  const t0 = Date.now();
  const root = path.resolve(toolkitRoot);
  // (generations on by default: turned on here at a toolkit's first promotion, where they can be)
  const generation = await ensureGenerations(root, opts.log);
  if ("why" in generation) {
    throw new Error(`moving results into the shared library needs per-run Lean workspaces, and there are none here: ${generation.why}. ` +
      "The decisions are kept: apply again once workspaces are available (doc/USER_MANUAL.md, \"Lean workspaces\").");
  }
  const r = await ensureWorkspace(root, `${slug}.promo`, opts);
  const t = await toolkitLayout(root);
  const pin = (await readJson<{ gen: number; local: string; pinned: string[] }>(path.join(r.path, ".pf-gen")))!;
  const gen = path.join(pin.local ?? opts.localRoot ?? localLeanRoot(root), "gens", String(pin.gen));
  const stagingRel = path.join(path.relative(root, t.libDir), t.staging);
  // reset to the generation: what an earlier, abandoned preparation wrote is gone
  if (!r.repinned) {
    // (the generation's entries removed first: `pin` places each anew, never onto its own link)
    for (const e of pin.pinned) await rm(path.join(r.path, e), { recursive: true, force: true });
    for (const sub of [path.join("lib", "lean"), "ir", "bin"]) {
      for (const e of await readdir(path.join(gen, ".lake", "build", sub)).catch(() => [] as string[])) await rm(path.join(r.path, ".lake", "build", sub, e), { recursive: true, force: true });
    }
    await leanWorkspaceSh(["pin", gen, r.path, root, stagingRel]);
  }
  for (const e of await readdir(r.path)) {
    if (e.endsWith(".lean") && e !== `${t.papersLib}.lean` && !pin.pinned.includes(e) && !(await lstat(path.join(r.path, e))).isSymbolicLink()) await rm(path.join(r.path, e), { force: true });
  }
  const off = await notGeneration(r.path, gen, pin.pinned, stagingRel);
  if (off) throw new Error(`${r.path} is not generation ${pin.gen} after its reset (${off}); remove it and prepare again`);
  await copyConfigTools(root, r.path);
  // the papers written and every paper they import, transitively (their sources: their builds need them)
  const named = papers.map((p) => (p.startsWith(`${t.papersLib}.`) ? p : `${t.papersLib}.${p}`));
  const { paperImports } = await import("./build_inputs.js");
  const closure = named.length ? (await paperImports(t, named)).papers.filter((p) => p.startsWith(`${t.papersLib}.`)) : [];
  const copied = [...new Set([...named, ...closure])];
  await detach(t, r.path, copied.map((p) => p.slice(t.papersLib.length + 1)));
  const seeded = opts.seed === false || copied.length === 0 ? [] : await seedFromRun(root, slug, r.path, pin.gen, copied, opts).catch((err: unknown) => {
    opts.log?.(`[workspace] ${slug}.promo: not seeded from the run's workspace (${err instanceof Error ? err.message : String(err)})`);
    return [] as string[];
  });
  // (what P's own paper outputs were last prepared on: the next prepare's choice of a seed)
  await writeJsonAtomic(path.join(r.path, PAPERS_GEN_FILE), { gen: pin.gen });
  // (2026-11-11) the path dependencies, live links in P: their state before the verdict — its read
  // set is kept only when they are the same at `prepareCommit` (audit: a read set of the verdict's bytes)
  const deps = await dependencyStates(r.path);
  await writeJsonAtomic(path.join(r.path, DEPS_FILE), { states: deps ? Object.fromEntries(deps) : null });
  return { ...r, ms: Date.now() - t0, seeded };
}

/**
 * `fn` with run `slug`'s promotion workspace `P` prepared (`prepareWorkspace`), holding `P`'s own
 * lock (`<local>/ws/<slug>.promo/.pf-promo.flock`, `withFlock`, as the seed holds `W`'s) from the
 * prepare to `fn`'s end — the caller's last use of `P` (its commit prepared, its scan done). A prepare
 * resets `P`: another process (or call) of the same run on this machine waits for the holder,
 * `lockWaitS` at most (`PROMO_LOCK_WAIT_S`), then fails (`lockBusy` makes the error: under the
 * promotion lock, `HeldWait`) — it never resets `P` under the holder.
 */
export async function withPromoWorkspace<T>(
  toolkitRoot: string, slug: string, papers: readonly string[],
  opts: Parameters<typeof prepareWorkspace>[3] & { lockWaitS?: number; lockBusy?: (why: string) => Error },
  fn: (w: Awaited<ReturnType<typeof prepareWorkspace>>) => Promise<T>,
): Promise<T> {
  const root = path.resolve(toolkitRoot);
  const local = opts.localRoot ?? localLeanRoot(root);
  workspacePath(root, `${slug}.promo`, local); // (the slug checked: the lock's path is made of it)
  const file = path.join(local, "ws", `${slug}.promo`, ".pf-promo.flock");
  const { lockWaitS, lockBusy, ...prep } = opts;
  return withFlock(file, async () => fn(await prepareWorkspace(root, slug, papers, prep)), lockWaitS ?? PROMO_LOCK_WAIT_S, {
    what: `${slug}.promo (its promotion workspace, in use by another process)`, ...(opts.log ? { log: opts.log } : {}), ...(lockBusy ? { fail: lockBusy } : {}),
  });
}

/** How long a second user of a run's promotion workspace waits for the first (`withPromoWorkspace`;
 *  a holder may take long — an unseeded prepare and its gate, a coordinator agent — and its death
 *  releases the lock). Under the promotion lock: `SEED_LOCK_WAIT_HELD_S`, then `HeldWait`. */
export const PROMO_LOCK_WAIT_S = 4 * 3600;

/** How long a promotion waits for its run's workspace's build lock before it goes on unseeded
 *  (`seedWaitS` overrides it: an attempt under the promotion lock waits less). */
export const SEED_LOCK_WAIT_S = 120;
/** The same wait for an attempt prepared under the promotion lock and the exclusive Lake hold. */
export const SEED_LOCK_WAIT_HELD_S = 10;
/** `P/.pf-papers-gen.json`: the generation P's own paper outputs were last prepared on. */
const PAPERS_GEN_FILE = ".pf-papers-gen.json";
/** `P/.pf-deps.json`: the path dependencies' states when `P` was prepared, before its verdict. */
const DEPS_FILE = ".pf-deps.json";

/** Each paper's build outputs (relative to `.lake/build`) in workspace `ws`: its directories and the
 *  barrel's own files (`<P>.olean`, `<P>.trace`, …) in `lib/lean` and `ir`. */
async function paperOutputs(ws: string, paper: string): Promise<string[]> {
  const dir = path.join(...paper.split("."));
  const out: string[] = [];
  for (const sub of [path.join("lib", "lean"), "ir"]) {
    const base = path.join(sub, dir);
    if (existsSync(path.join(ws, ".lake", "build", base))) out.push(base);
    const entries = await readdir(path.join(ws, ".lake", "build", path.dirname(base))).catch(() => [] as string[]);
    out.push(...entries.filter((e) => e.startsWith(`${path.basename(base)}.`)).map((e) => path.join(path.dirname(base), e)));
  }
  return out;
}

/**
 * The papers' build outputs of the run's own workspace `W` (this machine's, `ensureWorkspace(<slug>)`)
 * placed in the promotion's workspace `P`, on every prepare (the first, each rebase, the attempt under
 * the lock). The newest source wins, never one ahead of `P`'s generation `gen`: `W`'s outputs when
 * `W` is pinned to a generation newer than the one `P`'s own outputs were last prepared on (`P` fresh:
 * any, up to `gen`) — so after each re-pin to the generation `W` is on; else `P`'s own are kept (its
 * pin only moved forward; on a tie too: `P`'s sources are the move's). A pin that moved back drops
 * `P`'s own. `W`'s papers are
 * taken only when Lake finds them up to date there (`lake build --no-build`, under `W`'s build lock,
 * held through the copy; each paper alone when not all are — a paper `W` never built is not seeded).
 * The compiler's outputs hard links (Lake unlinks one before it rewrites it), what Lake writes in
 * place copies (`lean_workspace.sh seed`). Nothing is trusted: Lake in `P` judges every module by its
 * trace against `P`'s sources and generation, and rebuilds what changed. Returns the papers seeded.
 */
async function seedFromRun(root: string, slug: string, P: string, gen: number, papers: readonly string[], opts: { localRoot?: string; log?: (line: string) => void; seedWaitS?: number }): Promise<string[]> {
  const { workspacePath } = await import("./workspace.js");
  const own = await readJson<{ gen: number }>(path.join(P, PAPERS_GEN_FILE));
  if (own && own.gen > gen) {
    // (the pin moved back: P's own outputs were made against a newer toolkit — dropped)
    for (const p of papers) for (const rel of await paperOutputs(P, p)) await rm(path.join(P, ".lake", "build", rel), { recursive: true, force: true });
    opts.log?.(`[workspace] ${slug}.promo: its pin moved back from generation ${own.gen} to ${gen} — its own paper outputs dropped`);
  }
  const ownGen = own && own.gen <= gen ? own.gen : null;
  const W = workspacePath(root, slug, opts.localRoot ?? localLeanRoot(root));
  const wpin = await readJson<{ gen: number }>(path.join(W, ".pf-gen"));
  if (!wpin) return [];
  if (wpin.gen > gen || (ownGen !== null && wpin.gen <= ownGen)) {
    opts.log?.(`[workspace] ${slug}.promo: not seeded (the run's workspace is on generation ${wpin.gen}, this one on ${gen}${ownGen !== null ? `, its own paper outputs prepared on ${ownGen}: kept` : ""})`);
    return [];
  }
  const t0 = Date.now();
  return withFlock(path.join(W, ".lake", "build.lock"), async () => {
    const built: string[] = [];
    for (const p of papers) if ((await paperOutputs(W, p)).length) built.push(p);
    let fresh: string[] = [];
    if (built.length && (await COMMIT_LAKE.run(W, ["build", "--no-build", ...built])).code === 0) fresh = built;
    else if (built.length > 1) for (const p of built) if ((await COMMIT_LAKE.run(W, ["build", "--no-build", p])).code === 0) fresh.push(p);
    if (!fresh.length) {
      opts.log?.(`[workspace] ${slug}.promo: not seeded (the papers are not up to date in the run's workspace)`);
      return [];
    }
    const all = (await Promise.all(fresh.map((p) => paperOutputs(W, p)))).flat();
    await leanWorkspaceSh(["seed", W, P, ...all]);
    opts.log?.(`[workspace] ${slug}.promo: seeded with ${fresh.join(", ")}'s build outputs from the run's workspace (generation ${wpin.gen}${wpin.gen !== gen ? `, this one on ${gen}: Lake rebuilds what changed` : ""}; ${Math.round((Date.now() - t0) / 100) / 10} s)`);
    return fresh;
  }, opts.seedWaitS ?? SEED_LOCK_WAIT_S);
}

/** The running checkout's `tools/` (this file's, two levels up). */
const RUNNING_TOOLS = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..");

/** The files the toolkit's config names under `../tools/` (a base library's alias lexicon, prompt
 *  notes: `"../tools/data/aliases/…"`), reachable from the workspace as from the toolkit: COPIES of
 *  the running checkout's — never a link, so nothing written there reaches a checkout, nor the shared
 *  toolkit's own `../tools`. Other paths outside the toolkit (a path dependency's index) are reached
 *  through the path dependencies' anchors (`ensureWorkspace`). */
async function copyConfigTools(root: string, ws: string): Promise<void> {
  const text = await readFile(path.join(root, "paperformalizer.json"), "utf8").catch(() => "");
  for (const m of text.matchAll(/"((?:\.\.\/)+tools\/[^"]+)"/g)) {
    const rest = m[1]!.split("/").filter((x) => x !== "..").slice(1).join("/");
    const from = path.join(RUNNING_TOOLS, rest);
    const at = path.resolve(ws, m[1]!);
    const parts = ws.split(path.sep);
    const promo = parts.slice(0, parts.findIndex((x) => x.endsWith(".promo")) + 1).join(path.sep);
    if (!promo || !at.startsWith(promo + path.sep) || !existsSync(from)) continue;
    await mkdir(path.dirname(at), { recursive: true });
    await cp(from, at, { recursive: true, force: true });
  }
}

/** Why the workspace's pinned entries are not the generation's (a file added, removed, or not its
 *  bytes), or null. */
async function notGeneration(ws: string, gen: string, pinned: readonly string[], stagingRel: string): Promise<string | null> {
  for (const e of pinned) {
    const st = await lstat(path.join(gen, e));
    const rels = st.isDirectory()
      ? [...new Set([...(await filesUnder(path.join(gen, e))), ...(await filesUnder(path.join(ws, e), (r) => path.join(e, r) === stagingRel))])].map((f) => path.join(e, f))
      : [e];
    for (const rel of rels) if (!(await sameFile(path.join(ws, rel), path.join(gen, rel)))) return `${rel} differs`;
  }
  return null;
}

/** A doc file at least this large is left out of a promotion's workspace (the toolkit graph, a
 *  single-file statement store not yet split: no gate reads or writes them; a promotion's own are
 *  written after its commit). */
export const DOC_COPY_MAX_BYTES = 64 << 20;
/** Left out of a promotion's workspace's `doc/` whatever their size: the statement store's shards
 *  (`doc/statements/`, every paper's: no gate reads or writes them, as when it was one large file). */
const DOC_LEFT_OUT = ["statements"];

/** `from` copied to `at` (a directory recursively), but for lock files, a paper's `tmp/` scratch
 *  (`paperTmp`), the entries of `from` named in `leftOut`, and files of `maxBytes` or more. */
async function copyIn(from: string, at: string, opts: { paperTmp?: boolean; maxBytes?: number; leftOut?: readonly string[] } = {}): Promise<void> {
  if (!existsSync(from)) return;
  await cp(from, at, {
    recursive: true,
    filter: (src) => {
      if (LOCKISH.test(path.basename(src))) return false;
      if (opts.paperTmp && src === path.join(from, PAPER_TMP_DIR)) return false;
      if (opts.leftOut?.some((e) => src === path.join(from, e))) return false;
      if (opts.maxBytes !== undefined) { try { const st = statSync(src); if (st.isFile() && st.size >= opts.maxBytes) return false; } catch { return false; } }
      return true;
    },
  });
}

async function detach(t: ToolkitLayout, ws: string, papers: readonly string[]): Promise<void> {
  const rel = (p: string) => path.relative(t.root, p);
  for (const e of await readdir(ws)) {
    if (LOCKISH.test(e) && (await lstat(path.join(ws, e))).isSymbolicLink()) await unlink(path.join(ws, e));
  }
  // Papers/: the papers written, copied — no other paper, and no link into the shared tree
  const papersWs = path.join(ws, rel(t.papersDir));
  await rm(papersWs, { recursive: true, force: true });
  await mkdir(papersWs, { recursive: true });
  for (const p of papers) {
    await copyIn(path.join(t.papersDir, p), path.join(papersWs, p), { paperTmp: true });
    await copyIn(path.join(t.papersDir, `${p}.lean`), path.join(papersWs, `${p}.lean`));
  }
  // the papers' barrel: a copy (a commit installs what the workspace made of it)
  const barrel = path.join(ws, `${t.papersLib}.lean`);
  await rm(barrel, { force: true });
  await copyIn(path.join(t.root, `${t.papersLib}.lean`), barrel);
  // doc/: copies, the largest stores left out
  await rm(path.join(ws, "doc"), { recursive: true, force: true });
  await copyIn(path.join(t.root, "doc"), path.join(ws, "doc"), { maxBytes: DOC_COPY_MAX_BYTES, leftOut: DOC_LEFT_OUT });
  const files: Record<string, string> = {};
  const tracked = [
    ...(await Promise.all(papers.map(async (p) => [
      ...(await filesUnder(path.join(papersWs, p))).map((f) => path.join(rel(t.papersDir), p, f)),
      path.join(rel(t.papersDir), `${p}.lean`)]))).flat(),
    `${t.papersLib}.lean`,
    ...DOC_COMMITTED.map((f) => path.join("doc", f)),
  ];
  const orig = path.join(ws, ".pf-detach", "orig");
  await rm(path.join(ws, ".pf-detach"), { recursive: true, force: true });
  await mkdir(orig, { recursive: true });
  for (const f of tracked) {
    const sha = await shaOf(path.join(ws, f));
    if (sha === null) continue;
    files[f] = sha;
    await mkdir(path.dirname(path.join(orig, f)), { recursive: true });
    await cp(path.join(ws, f), path.join(orig, f));
  }
  // every doc copy's bytes: a doc file changed in the workspace but the index is refused (`prepareCommit`)
  const docs: Record<string, string> = {};
  for (const f of await filesUnder(path.join(ws, "doc"))) docs[f] = (await shaOf(path.join(ws, "doc", f)))!;
  // the private ledger as copied: what it gains is the commit's declarations (`prepareCommit`)
  if (existsSync(path.join(ws, "doc", "ledger.json"))) await cp(path.join(ws, "doc", "ledger.json"), path.join(ws, ".pf-detach", "ledger.json"));
  await writeJsonAtomic(path.join(ws, ".pf-detach.json"), { papers: [...papers], files, docs } satisfies Detached);
}

/** The files written under `dir` of the workspace (a real file where the detach left a link), but
 *  for the copied top-level entries `own`. */
async function writtenIn(dir: string, own: ReadonlySet<string>, rel = ""): Promise<string[]> {
  const out: string[] = [];
  for (const e of await readdir(path.join(dir, rel), { withFileTypes: true }).catch(() => [])) {
    const r = rel ? path.join(rel, e.name) : e.name;
    if ((!rel && own.has(e.name)) || LOCKISH.test(e.name)) continue;
    if (e.isDirectory()) out.push(...(await writtenIn(dir, own, r)));
    else if (e.isFile()) out.push(r);
  }
  return out;
}

/** What a commit has Lake find up to date: the toolkit's build targets (its library and its path
 *  dependencies' libraries, as its clean stamp builds them) and its executables. */
async function commitTargets(t: ToolkitLayout): Promise<string[]> {
  const scope = await toolkitScope(t);
  const libs = "why" in scope ? [t.lib] : scope.targets;
  const { parseLakefileToml, parseLakefileLean } = await import("../toolkit/lakefile.js");
  const toml = await readFile(path.join(t.root, "lakefile.toml"), "utf8").catch(() => null);
  const exes = toml !== null ? parseLakefileToml(toml).exes : parseLakefileLean(await readFile(path.join(t.root, "lakefile.lean"), "utf8").catch(() => "")).exes;
  return [...new Set([...libs, ...[...exes].sort()])];
}

/** The build files a generation carries (`lean_workspace.sh pack`), relative to `.lake/build`:
 *  every output of a pinned root module, and `bin/` — the staging tree's left out, and every
 *  `.setup.json` (a compile's input Lake writes anew before each compile, read by nothing after:
 *  never carried, `lean_workspace.sh`'s header). */
async function generationBuildFiles(dir: string, roots: readonly string[], staging: string): Promise<string[]> {
  const build = path.join(dir, ".lake", "build");
  const skip = (r: string) => r.split(path.sep).includes(staging) || path.basename(r).startsWith(".nfs") || r.endsWith(".nobuild") || path.basename(r).startsWith(".pf-") || r.endsWith(".setup.json");
  const out: string[] = [];
  for (const sub of [path.join("lib", "lean"), "ir"]) {
    for (const e of await readdir(path.join(build, sub)).catch(() => [] as string[])) {
      if (!roots.some((m) => e === m || e.startsWith(`${m}.`))) continue;
      const st = await lstat(path.join(build, sub, e));
      if (st.isDirectory()) out.push(...(await filesUnder(path.join(build, sub, e), skip)).map((f) => path.join(sub, e, f)));
      else if (st.isFile() && !skip(e)) out.push(path.join(sub, e));
    }
  }
  out.push(...(await filesUnder(path.join(build, "bin"), skip)).map((f) => path.join("bin", f)));
  return out.sort();
}

/** Whether `a` (in the workspace) is the generation's file `b`: the same inode (a link Lake never
 *  replaced), or the same bytes. */
async function sameFile(a: string, b: string): Promise<boolean> {
  const [sa, sb] = await Promise.all([lstat(a).catch(() => null), lstat(b).catch(() => null)]);
  if (!sa || !sb) return !sa && !sb;
  if (sa.ino === sb.ino && sa.dev === sb.dev) return true;
  if (sa.isSymbolicLink() !== sb.isSymbolicLink() || sa.size !== sb.size) return false;
  return (await shaOf(a)) === (await shaOf(b));
}

/** The declarations the workspace's private ledger gained since its detach (by name, module and
 *  origin slug). */
async function ledgerGained(ws: string): Promise<LedgerDeclaration[]> {
  const { loadLedger } = await import("../toolkit/ledger.js");
  if (!existsSync(path.join(ws, ".pf-detach", "ledger.json"))) return [];
  const key = (d: LedgerDeclaration) => `${d.name}\0${d.module}\0${d.origin.slug}`;
  const was = new Set((await loadLedger(path.join(ws, ".pf-detach", "ledger.json"))).declarations.map(key));
  return (await loadLedger(path.join(ws, "doc", "ledger.json"))).declarations.filter((d) => !was.has(key(d)));
}

/**
 * The commit directory `C` of what the detached workspace `ws` changed against the generation it is
 * pinned to (see the header). `ws` must be built: `lake build --no-build <targets>` exits 0 there
 * (else this throws — the delta would be incomplete). `ledger`: by default what `ws`'s private
 * ledger gained. Returns `C`.
 */
export async function prepareCommit(
  toolkitRoot: string, ws: string,
  opts: { id?: string; ledger?: LedgerDeclaration[]; records?: CommitRecord[]; adds?: CommitAdd[]; log?: (line: string) => void } = {},
): Promise<string> {
  const root = path.resolve(toolkitRoot);
  const pin = await readJson<{ gen: number; sig: string; local: string; pinned: string[] }>(path.join(ws, ".pf-gen"));
  if (!pin) throw new Error(`${ws} is no workspace (no .pf-gen)`);
  const detached = await readJson<Detached>(path.join(ws, ".pf-detach.json"));
  if (!detached) throw new Error(`${ws} is not detached (prepareWorkspace)`);
  const id = opts.id ?? `commit${Date.now().toString(36)}-${randomBytes(3).toString("hex")}`;
  if (!COMMIT_ID_RE.test(id)) throw new Error(`not a commit id: ${id} (commit<base36>-<6 hex>)`);
  const gen = path.join(pin.local, "gens", String(pin.gen));
  const t = await toolkitLayout(root);
  const papersRel = path.relative(root, t.papersDir);
  // nothing written outside what was copied (a paper not named, a doc file but the index)
  const strays = [
    ...(await writtenIn(path.join(ws, papersRel), new Set(detached.papers.flatMap((p) => [p, `${p}.lean`])))).map((f) => path.join(papersRel, f)),
    ...(await Promise.all((await filesUnder(path.join(ws, "doc"), (r) => LOCKISH.test(path.basename(r))))
      .filter((f) => !(DOC_PRIVATE as readonly string[]).includes(f))
      .map(async (f) => ((await shaOf(path.join(ws, "doc", f))) === detached.docs?.[f] ? null : path.join("doc", f))))).filter((f): f is string => f !== null),
  ];
  if (strays.length) throw new Error(`${ws} wrote ${strays.slice(0, 5).join(", ")}${strays.length > 5 ? ` (and ${strays.length - 5} more)` : ""}, which it did not copy: prepare it with those papers named`);
  const targets = await commitTargets(t);
  const C = path.join(commitsDir(root), id);
  // P's build lock from Lake's verdict to the pack: the generation is what Lake vouched for
  await withFlock(path.join(ws, ".lake", "build.lock"), async () => {
    const built = await COMMIT_LAKE.run(ws, ["build", "--no-build", ...targets]);
    if (built.code !== 0) throw new Error(`${ws} is not built: \`lake build --no-build ${targets.join(" ")}\` exited ${built.code}\n${tail(built.out)}`);
    await rm(C, { recursive: true, force: true });
    await mkdir(C, { recursive: true });

    // the sources: the pinned trees against the generation, the copied papers and docs against detach
    const sources: SourceChange[] = [];
    const keep = async (rel: string, before: string | null, after: string | null, beforeFile: string | null) => {
      if (before === after) return;
      sources.push({ rel, before, after });
      if (after !== null) { await mkdir(path.dirname(path.join(C, "src", rel)), { recursive: true }); await cp(path.join(ws, rel), path.join(C, "src", rel)); }
      if (beforeFile) { await mkdir(path.dirname(path.join(C, "orig", rel)), { recursive: true }); await cp(beforeFile, path.join(C, "orig", rel)); }
    };
    const stagingRel = path.join(path.relative(root, t.libDir), t.staging);
    for (const e of pin.pinned) {
      const st = await lstat(path.join(gen, e));
      const rels = st.isDirectory()
        ? [...new Set([...(await filesUnder(path.join(gen, e))), ...(await filesUnder(path.join(ws, e), (r) => path.join(e, r) === stagingRel))])].map((f) => path.join(e, f))
        : [e];
      for (const rel of rels.sort()) {
        if (await sameFile(path.join(ws, rel), path.join(gen, rel))) continue;
        await keep(rel, await shaOf(path.join(gen, rel)), await shaOf(path.join(ws, rel)), existsSync(path.join(gen, rel)) ? path.join(gen, rel) : null);
      }
    }
    const barrelRel = `${t.papersLib}.lean`;
    const nowFiles = [
      ...(await Promise.all(detached.papers.map(async (p) => [
        ...(await filesUnder(path.join(ws, papersRel, p))).map((f) => path.join(papersRel, p, f)), path.join(papersRel, `${p}.lean`)]))).flat(),
      ...DOC_COMMITTED.map((f) => path.join("doc", f)),
    ];
    for (const rel of [...new Set([...Object.keys(detached.files), ...nowFiles])].sort()) {
      if (rel === barrelRel) continue;
      const before = detached.files[rel] ?? null;
      await keep(rel, before, await shaOf(path.join(ws, rel)), before === null ? null : path.join(ws, ".pf-detach", "orig", rel));
    }
    // the papers' barrel: the imports it gained (only those: nothing else of it is the commit's)
    const importsOf = (text: string) => new Set(text.split(/\r?\n/).filter((l) => parseLeanImport(l) !== null));
    const was = importsOf(await readFile(path.join(ws, ".pf-detach", "orig", barrelRel), "utf8").catch(() => ""));
    const added = [...importsOf(await readFile(path.join(ws, barrelRel), "utf8").catch(() => ""))].filter((l) => !was.has(l)).sort();

    // the build files that differ from the generation's
    const roots = pin.pinned.filter((e) => e.endsWith(".lean")).map((e) => e.slice(0, -".lean".length));
    const mine = await generationBuildFiles(ws, roots, t.staging);
    const theirs = await generationBuildFiles(gen, roots, t.staging);
    const build: BuildFile[] = [];
    for (const rel of mine) {
      const a = path.join(ws, ".lake", "build", rel);
      if (await sameFile(a, path.join(gen, ".lake", "build", rel))) continue;
      build.push({ rel, size: (await stat(a)).size, sha: (await shaOf(a))! });
    }
    const removedBuild = theirs.filter((r) => !mine.includes(r));
    await writeFile(path.join(C, "delta.list"), build.map((b) => `${b.rel}\0`).join(""));
    await exec("tar", ["-c", "-f", path.join(C, "delta.tar"), "-C", path.join(ws, ".lake", "build"), "--null", "--no-recursion", "-T", path.join(C, "delta.list")]);
    await leanWorkspaceSh(["pack", ws, path.join(C, "gen.tar.zst"), t.lib, t.papersLib, t.staging]);

    sources.sort((a, b) => (a.rel < b.rel ? -1 : a.rel > b.rel ? 1 : 0));
    const ledger = opts.ledger ?? (await ledgerGained(ws));
    // (2026-11-11) what its verdict read: a paper-only commit may land on a later generation by it (I1′)
    const paper = paperOnly(papersRel, { sources, build, removedBuild, ledger });
    // (the path dependencies changed since the prepare, during the verdict: no read set — strict)
    const depsThen = (await readJson<{ states: Record<string, string> | null }>(path.join(ws, DEPS_FILE)))?.states ?? null;
    const depsNow = await dependencyStates(ws);
    const depMoved = !depsThen || !depsNow ? "(not read)" : changedSources(new Map(Object.entries(depsThen)), depsNow)[0] ?? null;
    if (depMoved) opts.log?.(`[commit] ${id}: a path dependency changed during its verdict (${depMoved === "(not read)" ? depMoved : path.relative(ws, depMoved)}): no read set, it lands only on its base`);
    let reads = depMoved ? null : await readSetOf(ws, pin.pinned, gen, t, detached, sources);
    // (and once more after the read set is hashed: an edit in between leaves no read set — audit note 2026-11-11)
    if (reads) {
      const depsAfter = await dependencyStates(ws);
      if (!depsAfter || changedSources(new Map(Object.entries(depsThen!)), depsAfter).length) {
        opts.log?.(`[commit] ${id}: a path dependency changed while its read set was taken: no read set, it lands only on its base`);
        reads = null;
      }
    }
    const m: CommitManifest = {
      id, created: new Date().toISOString(), ws, base: { gen: pin.gen, sig: pin.sig }, targets, sources, build, removedBuild,
      ledger, records: opts.records ?? [],
      ...(added.length ? { barrel: { rel: barrelRel, imports: added } } : {}),
      ...(reads ? { reads } : {}),
      ...(opts.adds ? { adds: opts.adds } : {}),
    };
    await writeJsonAtomic(path.join(C, "manifest.json"), m);
    opts.log?.(`[commit] ${id} prepared on generation ${pin.gen}: ${sources.length} source(s), ${build.length} build file(s)${paper ? ", paper-only" : ""}${reads ? `, a read set of ${reads.length} file(s)` : ""} (${C})`);
  });
  return C;
}

/** Whether a commit writes papers alone (I1′): every source under `Papers/`, no build file, no
 *  declaration (2026-11-11). */
const paperOnly = (papersRel: string, m: Pick<CommitManifest, "sources" | "build" | "removedBuild" | "ledger">) =>
  m.sources.every((s) => s.rel.startsWith(`${papersRel}${path.sep}`)) && m.build.length === 0 && m.removedBuild.length === 0 && m.ledger.length === 0;

/**
 * A commit's read set (I1′; 2026-11-11), relative to the toolkit: every copied paper file it does not
 * write (its bytes at the detach); the sources of the import closure of the copied papers and of the
 * new modules it adds, as they stand in `ws` after the verdict (`readClosure`: through the library
 * and the path dependencies); the pinned top-level files but the library's barrel (lakefile,
 * manifest, toolchain, exe roots). Null when the closure cannot be vouched for, or is over
 * `READ_CLOSURE_MAX` files. (Only a paper-only commit's is used yet: `offBaseReads`.)
 */
async function readSetOf(ws: string, pinned: readonly string[], gen: string, t: ToolkitLayout, detached: Detached, sources: readonly SourceChange[]): Promise<ReadFile[] | null> {
  const papersRel = path.relative(t.root, t.papersDir);
  const files = new Map<string, string>();
  for (const [rel, sha] of Object.entries(detached.files)) if (rel.startsWith(`${papersRel}${path.sep}`)) files.set(rel, sha);
  const starts = (await Promise.all(detached.papers.map(async (p) => [
    ...(await filesUnder(path.join(ws, papersRel, p))).filter((f) => f.endsWith(".lean")).map((f) => path.join(ws, papersRel, p, f)),
    path.join(ws, papersRel, `${p}.lean`)]))).flat()
    .concat(sources.filter((s) => s.before === null && s.after !== null && s.rel.endsWith(".lean")).map((s) => path.join(ws, s.rel)))
    .filter((f) => existsSync(f));
  const closure = await readClosure(await toolkitLayout(ws), starts);
  if (!closure) return null;
  const pinnedFiles: string[] = [];
  for (const e of pinned) if (e !== `${t.lib}.lean` && (await lstat(path.join(gen, e)).catch(() => null))?.isFile()) pinnedFiles.push(path.join(ws, e));
  for (const f of [...closure, ...pinnedFiles]) {
    const rel = path.relative(ws, f);
    if (files.has(rel)) continue;
    const sha = await shaOf(f);
    if (sha === null) return null;
    files.set(rel, sha);
  }
  for (const s of sources) files.delete(s.rel);
  if (files.size > READ_CLOSURE_MAX) return null;
  return [...files.keys()].sort().map((rel) => ({ rel, sha: files.get(rel)! }));
}

/** The read set `m` may land off its base by (I1′), or null — it lands only on its base: it writes
 *  the toolkit or carries a declaration (`paperOnly`, checked again here), has no `reads`, or the
 *  off-switch `strict-base` is on file. */
function offBaseReads(root: string, t: ToolkitLayout, m: CommitManifest): ReadFile[] | null {
  if (!m.reads || existsSync(strictBaseSwitch(root))) return null;
  return paperOnly(path.relative(t.root, t.papersDir), m) ? m.reads : null;
}

// ─── additive commits (2026-11-11, step 2) ────────────────────────────────────────────────────────

/** The toolkit index a commit may extend off its base (by a union). */
const INDEX_REL = path.join("doc", "toolkit_index.json");
/** A toolkit source's module name (`Toolkit/Foundations/X.lean` → `Toolkit.Foundations.X`). */
const moduleOfSource = (t: ToolkitLayout, rel: string) => path.relative(path.dirname(t.libDir), path.join(t.root, rel)).replace(/\.lean$/, "").split(path.sep).join(".");
/** A source of module `mod`, relative to the toolkit. */
const sourceOfModule = (t: ToolkitLayout, mod: string) => path.relative(t.root, `${path.join(path.dirname(t.libDir), ...mod.split("."))}.lean`);
/** The module a build file of `.lake/build` belongs to (`lib/lean/A/B.olean.hash`, `ir/A/B.c` → `A.B`),
 *  or null (`bin/`, anything else). */
function moduleOfBuild(rel: string): string | null {
  const parts = rel.split(path.sep);
  const rest = parts[0] === "lib" && parts[1] === "lean" ? parts.slice(2) : parts[0] === "ir" ? parts.slice(1) : null;
  if (!rest || rest.length === 0) return null;
  const last = rest.pop()!;
  const dot = last.indexOf(".");
  return [...rest, dot < 0 ? last : last.slice(0, dot)].join(".");
}

/** What an additive commit extends: its new modules, the barrels (relative paths) and whether the index. */
export interface AdditiveShape { modules: string[]; barrels: string[]; index: boolean }

/**
 * Whether `m` (prepared in `C`) is shaped as an additive commit (see the header): its shape, or why it
 * is strict. Read from its manifest, its new modules' headers (none may import a barrel or the root)
 * and the live library root (whose imports are the barrels); the contents are checked under the locks
 * (`additiveMerge`). The off-switch `strict-base` makes every commit strict.
 */
export async function additiveShape(root: string, t: ToolkitLayout, C: string, m: CommitManifest): Promise<AdditiveShape | { strict: string }> {
  if (existsSync(strictBaseSwitch(root))) return { strict: "the off-switch strict-base is on file" };
  if (existsSync(noAdditiveSwitch(root))) return { strict: "the off-switch no-additive is on file" };
  if (!m.reads) return { strict: "it has no read set" };
  if (!m.adds?.length) return { strict: "it names no declaration it adds (no adds)" };
  if (m.removedBuild.length) return { strict: "it removes build files" };
  const papersRel = path.relative(t.root, t.papersDir);
  const libRel = path.relative(t.root, t.libDir);
  const rootText = await readFile(`${t.libDir}.lean`, "utf8").catch(() => null);
  if (rootText === null) return { strict: "the library's root cannot be read" };
  const barrelMods = new Set(headerImports(rootText).filter((x) => x.startsWith(`${t.lib}.`)));
  const barrelRels = new Set([...barrelMods].map((x) => sourceOfModule(t, x)));
  const modules: string[] = [];
  const barrels: string[] = [];
  let index = false;
  for (const s of m.sources) {
    if (s.rel.startsWith(`${papersRel}${path.sep}`)) continue;
    if (s.before !== null && s.after !== null && barrelRels.has(s.rel)) { barrels.push(s.rel); continue; }
    if (s.before !== null && s.after !== null && s.rel === INDEX_REL) { index = true; continue; }
    if (s.before === null && s.after !== null && s.rel.endsWith(".lean") && s.rel.startsWith(`${libRel}${path.sep}`) && !s.rel.startsWith(`${path.join(libRel, t.staging)}${path.sep}`)) {
      modules.push(moduleOfSource(t, s.rel));
      continue;
    }
    return { strict: `it ${s.before === null ? "adds" : s.after === null ? "removes" : "writes"} ${s.rel}, neither a new module nor a barrel nor the index` };
  }
  if (!modules.length) return { strict: "it adds no module" };
  const chain = new Set([...barrelMods, t.lib]);
  const mine = new Set(modules);
  for (const b of m.build) {
    const mod = moduleOfBuild(b.rel);
    if (mod === null || (!mine.has(mod) && !chain.has(mod))) return { strict: `its build file ${b.rel} is of neither a new module nor the barrel chain` };
  }
  for (const mod of modules) {
    const text = await readFile(path.join(C, "src", sourceOfModule(t, mod)), "utf8").catch(() => null);
    if (text === null) return { strict: `its new module ${mod} cannot be read in ${C}` };
    const imp = headerImports(text).find((x) => chain.has(x));
    if (imp) return { strict: `its new module ${mod} imports ${imp} (the barrel chain)` };
  }
  return { modules: modules.sort(), barrels: barrels.sort(), index };
}

/** A toolkit index (`toolkit_index`'s JSON): its entries sorted by name, as Lean sorts strings. */
interface ToolkitIndex { toolchain?: unknown; modules?: Record<string, unknown>; entries?: Array<{ name: string; kind?: string } & Record<string, unknown>>; [k: string]: unknown }
/** Lean's `String` order (`toolkit_index` sorts its entries so): by code point — UTF-8 bytes. */
const leanStringOrder = (a: string, b: string) => Buffer.compare(Buffer.from(a, "utf8"), Buffer.from(b, "utf8"));

/** What a commit's index (`src`) adds to the one it read (`orig`), or why it changed more. */
function indexAdditions(orig: ToolkitIndex, src: ToolkitIndex): { modules: Record<string, unknown>; entries: NonNullable<ToolkitIndex["entries"]> } | string {
  if (JSON.stringify(orig.toolchain) !== JSON.stringify(src.toolchain)) return "its index is of another toolchain";
  const om = orig.modules ?? {};
  const sm = src.modules ?? {};
  for (const k of Object.keys(om)) {
    if (!(k in sm)) return `its index drops the module ${k}`;
    if (JSON.stringify(om[k]) !== JSON.stringify(sm[k])) return `its index changes the module ${k}`;
  }
  const was = new Map((orig.entries ?? []).map((e) => [e.name, JSON.stringify(e)] as const));
  const entries: NonNullable<ToolkitIndex["entries"]> = [];
  const seen = new Set<string>();
  for (const e of src.entries ?? []) {
    seen.add(e.name);
    const w = was.get(e.name);
    if (w === undefined) entries.push(e);
    else if (w !== JSON.stringify(e)) return `its index changes the entry of ${e.name}`;
  }
  for (const k of was.keys()) if (!seen.has(k)) return `its index drops the entry of ${k}`;
  return { modules: Object.fromEntries(Object.entries(sm).filter(([k]) => !(k in om))), entries };
}

/** The bytes an additive commit writes, merged onto the live tree: per file, the live bytes and the merged. */
type Merged = Map<string, { live: string; merged: string }>;

/**
 * Checks 3–4 of an additive commit off its base (see the header), on the live tree under the locks, and
 * the merged barrels and index: `{ merged }`, or why it is not landed off its base — `moved` (a clash
 * with what landed since) or `strict` (its changes are not additions alone, or a generation since has
 * no adds record).
 */
async function additiveMerge(root: string, t: ToolkitLayout, C: string, m: CommitManifest, shape: AdditiveShape, cur: { gen: number }): Promise<{ merged: Merged } | { moved: string } | { strict: string }> {
  const merged: Merged = new Map();
  const added: string[] = [];
  // the barrels: imports added, nothing else; merged into the live bytes
  for (const rel of shape.barrels) {
    const orig = await readFile(path.join(C, "orig", rel), "utf8");
    const src = await readFile(path.join(C, "src", rel), "utf8");
    const imports = (text: string) => text.split(/\r?\n/).filter((l) => parseLeanImport(l) !== null);
    const was = new Set(imports(orig));
    const gained = imports(src).filter((l) => !was.has(l));
    if (gained.reduce((text, line) => insertImportSorted(text, line), orig) !== src) return { strict: `its change to ${rel} is not imports inserted, alone` };
    // (each import it inserts is of one of its own new modules)
    const own = new Set(shape.modules);
    const foreign = gained.find((l) => !own.has(parseLeanImport(l)!.module));
    if (foreign) return { strict: `${rel} gains ${foreign.trim()}, not one of its own new modules` };
    const live = await readFile(path.join(root, rel), "utf8");
    const liveImports = new Set(imports(live));
    const dup = gained.find((l) => liveImports.has(l));
    if (dup) return { moved: `${rel} imports ${dup.trim()} already` };
    merged.set(rel, { live, merged: gained.reduce((text, line) => insertImportSorted(text, line), live) });
  }
  // the index: entries and modules added, nothing else; merged by a union
  const liveIndexText = await readFile(path.join(root, INDEX_REL), "utf8").catch(() => null);
  const liveIndex = liveIndexText === null ? null : JSON.parse(liveIndexText) as ToolkitIndex;
  const liveNames = new Map((liveIndex?.entries ?? []).map((e) => [e.name, e.kind ?? ""] as const));
  let origIndex: ToolkitIndex | null = null;
  if (shape.index) {
    if (!liveIndex || liveIndexText === null) return { strict: `${INDEX_REL} cannot be read in the shared tree` };
    origIndex = JSON.parse(await readFile(path.join(C, "orig", INDEX_REL), "utf8")) as ToolkitIndex;
    const add = indexAdditions(origIndex, JSON.parse(await readFile(path.join(C, "src", INDEX_REL), "utf8")) as ToolkitIndex);
    if (typeof add === "string") return { strict: add };
    if (JSON.stringify(origIndex.toolchain) !== JSON.stringify(liveIndex.toolchain)) return { strict: "the live index is of another toolchain" };
    const clash = add.entries.find((e) => liveNames.has(e.name));
    if (clash) return { moved: `${clash.name}, which its index adds, is in the live index` };
    const modClash = Object.keys(add.modules).find((k) => k in (liveIndex.modules ?? {}));
    if (modClash) return { moved: `the module ${modClash}, which its index adds, is in the live index` };
    added.push(...add.entries.map((e) => e.name));
    const entries = [...(liveIndex.entries ?? []), ...add.entries].map((e) => [Buffer.from(e.name, "utf8"), e] as const).sort((a, b) => Buffer.compare(a[0], b[0])).map(([, e]) => e);
    const next: ToolkitIndex = { ...liveIndex, modules: { ...(liveIndex.modules ?? {}), ...add.modules }, entries };
    merged.set(INDEX_REL, { live: liveIndexText, merged: `${JSON.stringify(next, null, 1)}\n` });
  }
  // the names it adds: none in the live index, no naming problem the names added since its base make
  const names = new Set(m.adds!.map((a) => a.name));
  for (const n of names) if (liveNames.has(n)) return { moved: `${n}, which it adds, is declared in the toolkit already (the live index)` };
  if (origIndex) {
    const { nameProblems } = await import("../proposals/curator.js");
    const thenNames = new Map((origIndex.entries ?? []).map((e) => [e.name, e.kind ?? ""] as const));
    for (const n of names) {
      const then = new Set(nameProblems(n, thenNames));
      const now = nameProblems(n, liveNames).filter((p) => !then.has(p));
      if (now.length) return { moved: `${n}: ${now.join("; ")} (since generation ${m.base.gen})` };
    }
  }
  // every generation since its base: what it added, recorded — none of its names, none of its statements
  const hashes = new Map(m.adds!.map((a) => [a.hash, a.name] as const));
  for (let g = m.base.gen + 1; g <= cur.gen; g++) {
    const rec = await readJson<{ adds?: CommitAdd[] }>(addsRecordFile(root, g));
    if (!rec?.adds) return { strict: `generation ${g} has no record of what it added (a gardening, flux or publisher generation, or old code's)` };
    for (const a of rec.adds) {
      if (names.has(a.name)) return { moved: `${a.name}, which it adds, was added by generation ${g}` };
      const mine = hashes.get(a.hash);
      if (mine) return { moved: `${mine} states what ${a.name} states (statement hash), added by generation ${g}` };
    }
  }
  return { merged };
}

/** The import pre-check's file (`COMMIT_PRECHECK`): the live library root, each merged barrel's
 *  imports in place of its own import. */
async function precheckText(t: ToolkitLayout, merged: Merged): Promise<string> {
  const rootText = await readFile(`${t.libDir}.lean`, "utf8");
  const mod = isLeanModuleFile(rootText);
  const kw = mod ? "public import" : "import";
  const lines = mod ? ["module", ""] : [];
  for (const imp of headerImports(rootText)) {
    const b = merged.get(sourceOfModule(t, imp));
    if (b) for (const x of headerImports(b.merged)) lines.push(`${kw} ${x}`);
    else lines.push(`${kw} ${imp}`);
  }
  return `${lines.join("\n")}\n`;
}

/** An additive commit's `C` rebased onto `cur` (see the header): `src/` and `orig/` of the merged
 *  files their merged and live bytes, the barrel chain's build files dropped, the archive removed,
 *  `manifest.json` rewritten (the prepared one kept as `manifest.prepared.json`). Returns the new manifest. */
async function rebaseCommit(C: string, t: ToolkitLayout, m: CommitManifest, shape: AdditiveShape, merged: Merged, cur: { gen: number; sig: string }): Promise<CommitManifest> {
  const prepared = path.join(C, "manifest.prepared.json");
  if (!existsSync(prepared)) await cp(path.join(C, "manifest.json"), prepared);
  const sha = (text: string) => createHash("sha256").update(text, "utf8").digest("hex");
  const sources: SourceChange[] = [];
  for (const s of m.sources) {
    const f = merged.get(s.rel);
    if (!f) { sources.push(s); continue; }
    await writeTextAtomic(path.join(C, "orig", s.rel), f.live);
    await writeTextAtomic(path.join(C, "src", s.rel), f.merged);
    sources.push({ rel: s.rel, before: sha(f.live), after: sha(f.merged) });
  }
  const chain = new Set([...shape.barrels.map((rel) => moduleOfSource(t, rel)), ...[...(await readFile(`${t.libDir}.lean`, "utf8").then(headerImports, () => []))], t.lib]);
  const next: CommitManifest = {
    ...m, base: { gen: cur.gen, sig: cur.sig }, sources, build: m.build.filter((b) => !chain.has(moduleOfBuild(b.rel) ?? "")),
    rebased: { from: m.rebased?.from ?? m.base, at: new Date().toISOString() },
  };
  await rm(path.join(C, "gen.tar.zst"), { force: true });
  await writeJsonAtomic(path.join(C, "manifest.json"), next);
  return next;
}

// ─── commit ───────────────────────────────────────────────────────────────────────────────────────

const readManifest = (C: string) => readJson<CommitManifest>(path.join(C, "manifest.json"));
export const readCommitJournal = (root: string) => readJson<CommitJournal>(commitJournalFile(path.resolve(root)));

/** Inside the locks this module takes (`withPromotionLock`, then `withLakeBuildLock`, as old code). */
async function locked<T>(root: string, what: string, log: (line: string) => void, fn: () => Promise<T>): Promise<T> {
  return withPromotionLock(root, () => withinCommit(() => withLakeBuildLock(root, fn, what, log)), undefined, log);
}

/**
 * Commit the prepared commit `C` (its directory, or its id) to the shared toolkit (see the header):
 * `landed` (generation `N+1` published; a paper-only commit: `CURRENT`, maybe past `N`, unchanged),
 * `base-moved` (prepare again on the current generation) or `wait` (the tree is not `CURRENT`, a flux
 * session is open, the line is stopped, or a build was killed). Throws, writing nothing, when `C` is
 * not complete.
 */
export async function commitToolkit(
  toolkitRoot: string, commit: string,
  opts: {
    log?: (line: string) => void;
    // compat 2026-11-11: remove after the processes started before this merge have exited (≤2 days)
    // (a `local_moves` loaded before the merge passes its `settleBatches`: run as it was)
    settle?: () => Promise<void>;
    /** The caller holds both locks already (true), or the promotion lock alone ("promotion": a
     *  promotion that prepared under it, after rebases — the exclusive Lake hold is the commit's own,
     *  over its checks and install, as for any commit). */
    held?: boolean | "promotion";
    /** (2026-11-11, step 2) Run under the locks, before the base checks: a caller's last check on
     *  the shared tree (`local_moves.recheckPaperNames`); it throws to refuse the commit. */
    recheck?: () => Promise<void>;
  } = {},
): Promise<CommitOutcome> {
  const root = path.resolve(toolkitRoot);
  const log = opts.log ?? ((l: string) => console.warn(l));
  const C = commit.includes(path.sep) ? path.resolve(commit) : path.join(commitsDir(root), commit);
  const m0 = await readManifest(C);
  if (!m0) throw new Error(`${C} is no prepared commit (no manifest.json)`);
  const asked = Date.now();
  const what = `toolkit-commit ${m0.id}`;
  const body = async (): Promise<CommitOutcome> => {
    const ms: Record<string, number> = { waited: Date.now() - asked };
    let t0 = Date.now();
    const lap = (k: string) => { ms[k] = Date.now() - t0; t0 = Date.now(); };
    // 1. recover (this very commit, interrupted: landed now)
    const r = await recoverLocked(root, log);
    if (r?.id === m0.id) return r.outcome;
    if (r && r.outcome.kind !== "landed") return r.outcome;
    // compat 2026-11-11: remove after the processes started before this merge have exited (≤2 days)
    await opts.settle?.();
    await sweep(root, C);
    await opts.recheck?.();
    lap("recover");
    let m = await readManifest(C);
    if (!m) throw new Error(`${C} is no prepared commit (no manifest.json)`);
    const base0 = m.base;
    // 2. the base (I1′: `CURRENT` exactly; off its base, a paper-only commit's read set unchanged, or
    // an additive commit's checks: 2026-11-11, step 2)
    const t = await toolkitLayout(root);
    const reads = offBaseReads(root, t, m);
    let cur = await currentGeneration(root);
    if (!cur) return { kind: "wait", why: "no generation is published" };
    if (isDoubt(cur.sig)) return { kind: "wait", why: `the current generation's signature vouches for nothing (${cur.sig.slice(0, 40)}…)` };
    const onBase = (g: { gen: number; sig: string }) => g.gen === base0.gen && g.sig === base0.sig;
    // (an additive commit's shape is read only off its base: on it, it is any commit)
    let shape = !reads && !onBase(cur) ? await additiveShape(root, t, C, m) : null;
    const additive = () => (shape && !("strict" in shape) ? shape : null);
    if (!onBase(cur) && !reads && !additive()) return { kind: "base-moved", why: `the toolkit is generation ${cur.gen}, not ${base0.gen}${shape && "strict" in shape ? ` (strict: ${shape.strict})` : ""}` };
    const flux = await toolkitFluxWhy(root);
    if (flux) return { kind: "wait", why: flux };
    const live = await toolkitSignature(t);
    if (isDoubt(live)) return { kind: "wait", why: `the toolkit's signature cannot be read (${live.slice(0, 60)}…): never committed onto` };
    if (live !== cur.sig) {
      // The toolkit stamped clean as it stands (a flux session's hand edits, closed), its generation
      // not published yet: published here, by the shared tree packed — then a strict commit is
      // base-moved. Never when the stamp is missing or not of the tree as it stands (a hand edit).
      const clean = await stampedClean(root);
      if (!("sig" in clean) || clean.sig !== live) return { kind: "wait", why: `the toolkit as it stands is not generation ${cur.gen} (an unpublished change or a hand edit): never committed onto` };
      const g = await publishGeneration(root, live, log);
      log(`[commit] ${m.id}: the toolkit was stamped clean but not published — published as generation ${g?.gen ?? "?"} here`);
      // (2026-11-11) a paper-only commit goes on, onto it (its read set checked below); an additive
      // one too (that generation has no adds record: strict, below)
      if (!g) return { kind: "base-moved", why: `the toolkit as it stands was stamped clean and is published now as generation ?, not ${base0.gen}` };
      shape ??= reads ? null : await additiveShape(root, t, C, m);
      if (!reads && !additive()) return { kind: "base-moved", why: `the toolkit as it stands was stamped clean and is published now as generation ${g.gen}, not ${base0.gen}` };
      cur = g;
    }
    // (an additive commit off its base merges into its barrels and index: their `before` is not checked)
    const merging = !onBase(cur) && additive() ? new Set([...additive()!.barrels, ...(additive()!.index ? [INDEX_REL] : [])]) : new Set<string>();
    for (const s of m.sources) {
      if (merging.has(s.rel)) continue;
      if ((await shaOf(path.join(root, s.rel))) !== s.before) return { kind: "base-moved", why: `${s.rel} changed since it was read` };
    }
    // (2026-11-11) off its base: every file its verdict read as it was then (I1′)
    if (!onBase(cur)) {
      const rs = reads ?? (additive() ? m.reads! : null);
      if (!rs) return { kind: "base-moved", why: `the toolkit is generation ${cur.gen}, not ${base0.gen}` };
      for (const f of rs) {
        if ((await shaOf(path.join(root, f.rel))) === f.sha) continue;
        log(`[commit] ${m.id}: prepared on generation ${base0.gen}, ${f.rel} of its read set changed by generation ${cur.gen} — base-moved`);
        await recordCommitEvent(root, { event: "reads-miss", id: m.id, base: base0.gen, gen: cur.gen, file: f.rel });
        return { kind: "base-moved", why: `${f.rel}, which it read on generation ${base0.gen}, changed since (the toolkit is generation ${cur.gen})` };
      }
    }
    lap("check");
    // 3. C complete, before anything is written (an additive commit off its base: staged first —
    // its pre-check imports its outputs — then merged and rebased onto `CURRENT`)
    const incomplete = await stageCommit(C, m, onBase(cur));
    if (incomplete) throw new Error(`the prepared commit ${C} is not complete (${incomplete}); nothing was written — prepare it again`);
    lap("staged");
    const add = !onBase(cur) ? additive() : null;
    if (add) {
      const miss = async (why: string, kind: "moved" | "strict"): Promise<CommitOutcome> => {
        log(`[commit] ${m!.id}: prepared on generation ${base0.gen}, not landed as an additive commit on generation ${cur!.gen} (${kind === "strict" ? "strict: " : ""}${why}) — base-moved`);
        await recordCommitEvent(root, { event: "additive-miss", id: m!.id, base: base0.gen, gen: cur!.gen, why: `${kind}: ${why}`.slice(0, 500), ms: { ...ms } });
        return { kind: "base-moved", why: `${why} (the toolkit is generation ${cur!.gen}, not ${base0.gen})` };
      };
      // (a file of it that cannot be read or parsed: strict, never a throw under the locks)
      const r = await additiveMerge(root, t, C, m, add, cur).catch((err: unknown) => ({ strict: `its merge failed (${err instanceof Error ? err.message.split("\n")[0] : String(err)})` }));
      if ("moved" in r) return miss(r.moved, "moved");
      if ("strict" in r) return miss(r.strict, "strict");
      lap("merge");
      const chain = [...add.barrels.map((rel) => moduleOfSource(t, rel)), t.lib];
      const pre = await COMMIT_PRECHECK.run(root, C, await precheckText(t, r.merged), chain);
      lap("precheck");
      if (pre.code === null) return miss(`its import pre-check was killed (over ${Math.round(ADDITIVE_LIMITS.precheckMs / 1000)} s, or by a signal): ${tail(pre.out, 2).replace(/\s+/g, " ")}`, "strict");
      if (pre.code !== 0) return miss(`Lean does not import the merged barrels with its modules (exit ${pre.code}): ${tail(pre.out, 4).replace(/\s+/g, " ")}`, "moved");
      m = await rebaseCommit(C, t, m, add, r.merged, cur);
      lap("rebase");
      await COMMIT_STEP.at("rebased");
      log(`[commit] ${m.id}: prepared on generation ${base0.gen}, additive — rebased onto generation ${cur.gen} (${add.modules.length} new module(s); ${add.barrels.join(", ")}${add.index ? `, ${INDEX_REL}` : ""} merged)`);
    }
    // 4. flux, 5. the commit point
    await openFluxSession(root, m.id, `${FLUX_WHAT} ${m.id}`);
    const states = await toolkitSources(t);
    if (!states) throw new Error("the toolkit's sources cannot be listed (a path dependency's libraries)");
    // (its base: the generation it is committed onto — `m.base` unless off its base)
    const j: CommitJournal = { id: m.id, base: { gen: cur.gen, sig: cur.sig }, next: cur.gen + 1, dir: C, at: new Date().toISOString(), host: LOCK_HOST, pid: process.pid, states: Object.fromEntries(states) };
    await writeJsonAtomic(commitJournalFile(root), j);
    await COMMIT_STEP.at("journaled");
    return land(root, C, m, j, log, true, ms, lap);
  };
  if (opts.held === true) return body();
  if (opts.held === "promotion") return withinCommit(() => withLakeBuildLock(root, body, what, log));
  // (2026-11-11) a commit bound to its base never queues once `CURRENT` moved on: it could only be
  // base-moved under the lock (generations only grow; the check there stays the one that decides) —
  // never when the journal names it (its roll-forward is due)
  // (an additive commit is not bound: 2026-11-11, step 2)
  const t0 = await toolkitLayout(root);
  const paper = offBaseReads(root, t0, m0) !== null;
  const bound = !paper && "strict" in (await additiveShape(root, t0, C, m0));
  // (an additive one leaves the queue too, once it cannot land additive: an off-switch on file, or a
  // generation since its base without an adds record — read again at each look)
  const moved = async () => {
    if (paper || (await readCommitJournal(root))?.id === m0.id) return false;
    const cur = await currentGeneration(root);
    if (cur === null || isDoubt(cur.sig) || cur.gen === m0.base.gen) return false;
    if (bound || existsSync(strictBaseSwitch(root)) || existsSync(noAdditiveSwitch(root))) return true;
    for (let g = m0.base.gen + 1; g <= cur.gen; g++) if (!existsSync(addsRecordFile(root, g))) return true;
    return false;
  };
  const movedOn = async (): Promise<CommitOutcome> => ({ kind: "base-moved", why: `the toolkit is generation ${(await currentGeneration(root))?.gen ?? "?"}, not ${m0.base.gen} (seen before the promotion lock)` });
  if (await moved()) return movedOn();
  const r = await withPromotionLockUntil(root, () => withinCommit(() => withLakeBuildLock(root, body, what, log)), path.join(root, ".toolkit-promote.lock"), log, moved);
  return r ? r.value : movedOn();
}

/** Step 3: why `C` is not complete, or null — its new sources' bytes, `orig/`, the archive (`onBase`
 *  only: a commit landed off its base never publishes it, 2026-11-11; nor a rebased one), and every build file, unpacked
 *  from `delta.tar` beside the tree (`C/delta/`) and re-hashed. */
async function stageCommit(C: string, m: CommitManifest, onBase: boolean): Promise<string | null> {
  for (const s of m.sources) {
    if (s.after !== null && (await shaOf(path.join(C, "src", s.rel))) !== s.after) return `src/${s.rel}`;
    if (s.before !== null && (await shaOf(path.join(C, "orig", s.rel))) !== s.before) return `orig/${s.rel}`;
  }
  // (a rebased additive commit never has one: its install builds for real, then packs)
  if (onBase && !m.rebased && !existsSync(path.join(C, "gen.tar.zst"))) return "gen.tar.zst";
  const stage = path.join(C, "delta");
  await rm(stage, { recursive: true, force: true });
  await mkdir(stage, { recursive: true });
  try {
    await exec("tar", ["-x", "-f", path.join(C, "delta.tar"), "-C", stage]);
  } catch (err) {
    return `delta.tar (${err instanceof Error ? err.message : String(err)})`;
  }
  for (const f of m.build) if ((await shaOf(path.join(stage, f.rel))) !== f.sha) return `delta/${f.rel}`;
  return null;
}

/** Steps 6–9 (see the header): `fast`, the commit itself, else a roll-forward. */
async function land(
  root: string, C: string, m: CommitManifest, j: CommitJournal, log: (line: string) => void, fast: boolean,
  ms: Record<string, number> = {}, lap: (k: string) => void = () => {},
): Promise<CommitOutcome> {
  const t = await toolkitLayout(root);
  // a roll-forward: never over a base that moved since the commit point
  if (!fast) {
    const now = await toolkitSources(t);
    if (!now) return stopLine(root, j, "the toolkit's sources cannot be listed", log);
    const mine = new Map(m.sources.map((s) => [path.join(root, s.rel), s] as const));
    for (const f of changedSources(new Map(Object.entries(j.states ?? {})), now)) {
      const s = mine.get(f);
      const sha = await shaOf(f);
      if (!s || (sha !== s.before && sha !== s.after)) {
        return stopLine(root, j, `${path.relative(root, f)} changed since commit ${m.id}'s commit point${s ? " (neither the bytes it had nor the commit's)" : " (not a file of the commit)"}: never rolled forward over a moved base`, log);
      }
    }
  }
  // 6. sources
  const left: string[] = [];
  for (const s of m.sources) {
    const at = path.join(root, s.rel);
    const now = await shaOf(at);
    if (now === s.after) continue;
    // (a toolkit source neither was refused above; a paper or doc file its run edited meanwhile is left)
    if (!fast && now !== s.before) { left.push(s.rel); continue; }
    if (s.after === null) await unlink(at).catch(() => {});
    else await writeTextAtomic(at, await readFile(path.join(C, "src", s.rel), "utf8"));
  }
  if (m.barrel) {
    const at = path.join(root, m.barrel.rel);
    const now = await readFile(at, "utf8").catch(() => null);
    if (now !== null) {
      const next = m.barrel.imports.reduce((text, line) => insertImportSorted(text, line), now);
      if (next !== now) await writeTextAtomic(at, next);
    }
  }
  lap("sources");
  if (fast) await COMMIT_STEP.at("sources");
  // 7. build files: outputs, then hashes, then traces
  let slow = !fast;
  if (fast) {
    const bad = await installBuild(root, C, m);
    if (bad) { log(`[commit] ${m.id}: ${bad} — the real build decides`); slow = true; }
    lap("build-files");
    await COMMIT_STEP.at("build-files");
  }
  // 8. Lake judges (2026-11-11, step 2: a rebased additive commit — its barrels and the root not
  // built for the merged bytes — builds for real first, then Lake must find the tree up to date)
  const rebuilt = fast && !slow && m.rebased !== undefined;
  if (rebuilt) {
    // (capped: `ADDITIVE_LIMITS.buildMs`. Past its commit point a commit cannot be base-moved: killed,
    // it is no verdict — the journal stays unstopped and the next holder rolls it forward ONCE, with
    // the roll-forward's own real build (unchanged, uncapped by this), which keeps every module the
    // killed build finished; a roll-forward never takes this capped path: `fast` only)
    const r = await COMMIT_LAKE.run(root, ["build", ...m.targets], { maxTotalMs: ADDITIVE_LIMITS.buildMs });
    lap("lake-build");
    if (r.code === null) {
      log(`[commit] ${m.id}: \`lake build ${m.targets.join(" ")}\` was killed (its cap, ${Math.round(ADDITIVE_LIMITS.buildMs / 1000)} s, as an additive commit): no verdict — the journal stays, and the next holder rolls it forward`);
      await recordCommitEvent(root, { event: "additive-miss", id: m.id, base: m.rebased!.from.gen, gen: j.base.gen, why: "killed: its real build over the cap; rolled forward by the next holder", ms: { ...ms } });
      return { kind: "wait", why: `commit ${m.id}'s build in the shared tree was killed (its time cap); rolled forward by the next holder` };
    }
    if (r.code !== 0) return stopLine(root, j, `\`lake build ${m.targets.join(" ")}\` exited ${r.code} in the shared tree after commit ${m.id} (additive, rebased onto generation ${j.base.gen})\n${tail(r.out)}`, log);
  }
  if (!slow) {
    const r = await COMMIT_LAKE.run(root, ["build", "--no-build", ...m.targets]);
    lap("lake-check");
    if (r.code !== 0 && rebuilt) {
      // (built, yet not up to date: no verdict — the journal stays unstopped, the next holder rolls it forward)
      log(`[commit] ${m.id}: LAKE WOULD BUILD in the shared tree right after its real build (\`lake build --no-build\` exited ${r.code ?? "killed"}): no verdict — the journal stays, and the next holder rolls it forward\n${tail(r.out)}`);
      return { kind: "wait", why: `commit ${m.id}: Lake did not find the shared tree up to date after its real build; rolled forward by the next holder` };
    }
    if (r.code !== 0) {
      log(`[commit] ${m.id}: LAKE WOULD BUILD in the shared tree after the install (\`lake build --no-build\` exited ${r.code ?? "killed"}): building it for real (the slow path)\n${tail(r.out)}`);
      slow = true;
    }
  }
  if (slow) {
    const r = await COMMIT_LAKE.run(root, ["build", ...m.targets]);
    lap("lake-build");
    if (r.code === null) {
      log(`[commit] ${m.id}: \`lake build ${m.targets.join(" ")}\` was killed (its time cap): no verdict — the journal stays, and the next holder rolls it forward`);
      return { kind: "wait", why: `commit ${m.id}'s build in the shared tree was killed (its time cap); rolled forward by the next holder` };
    }
    if (r.code !== 0) return stopLine(root, j, `\`lake build ${m.targets.join(" ")}\` exited ${r.code} in the shared tree after commit ${m.id}\n${tail(r.out)}`, log);
  }
  // 9. the ledger, stamp, the generation (CURRENT last), flux closed, records
  if (m.ledger.length > 0) {
    const { appendLedgerDeclarations } = await import("../toolkit/ledger.js");
    await appendLedgerDeclarations(path.join(root, "doc", "ledger.json"), m.ledger);
  }
  const sig = await toolkitSignature(t);
  if (isDoubt(sig)) return stopLine(root, j, `the toolkit's signature cannot be read (${sig}) after commit ${m.id}`, log);
  const scope = await toolkitScope(t);
  if ("why" in scope) log(`[commit] ${m.id}: no clean stamp (${scope.why})`);
  else await recordToolkitClean(root, sig, scope);
  if (fast) await COMMIT_STEP.at("stamped");
  // (2026-11-11) off its base, never its archive: that is its base's next generation, not this one's
  const offBase = j.base.gen !== m.base.gen || j.base.sig !== m.base.sig;
  const g = await publishGeneration(root, sig, log, slow || offBase || m.rebased || !existsSync(path.join(C, "gen.tar.zst")) ? undefined : path.join(C, "gen.tar.zst"));
  // (2026-11-11) what it added, beside the generation it made (none: a later additive commit is strict)
  if (m.adds && g && g.gen > j.base.gen) {
    await writeJsonAtomic(addsRecordFile(root, g.gen), { gen: g.gen, id: m.id, base: j.base.gen, adds: m.adds })
      .catch((err: unknown) => log(`[commit] ${m.id}: its adds not recorded (${err instanceof Error ? err.message : String(err)}); nothing else depends on it yet`));
  }
  lap("publish");
  if (fast) await COMMIT_STEP.at("published");
  await closeFluxSession(root, m.id);
  for (const rec of m.records) {
    await writeJsonAtomic(path.join(t.runsDir, rec.slug, "proposals", "landed", `${m.id}.json`), { id: m.id, gen: g?.gen ?? null, left, record: rec.record });
  }
  await unlink(commitJournalFile(root)).catch(() => {});
  await rm(C, { recursive: true, force: true });
  if (offBase) await recordCommitEvent(root, { event: "off-base", id: m.id, base: m.base.gen, gen: g?.gen ?? j.base.gen });
  const additive = m.rebased !== undefined && fast;
  if (additive) await recordCommitEvent(root, { event: "additive", id: m.id, base: m.rebased!.from.gen, gen: g?.gen ?? j.next, ms: { ...ms } });
  log(`[commit] ${m.id} landed as generation ${g?.gen ?? "?"}${offBase ? ` (prepared on generation ${m.base.gen}: off its base, its read set unchanged)` : ""}${additive ? ` (additive: prepared on generation ${m.rebased!.from.gen}, merged onto ${j.base.gen}; built for real)` : ""}${slow ? " (built for real)" : ""}${left.length ? `; left as edited meanwhile: ${left.join(", ")}` : ""}${fast ? ` [${Object.entries(ms).map(([k, v]) => `${k} ${Math.round(v / 100) / 10} s`).join(", ")}]` : ""}`);
  return { kind: "landed", gen: g?.gen ?? j.next, slow, left, ms, ...(additive ? { additive: true } : {}) };
}

/** Step 7: each staged build file (`C/delta/`) renamed into place (outputs, then `.hash`, then
 *  `.trace` files), then re-hashed. Returns what went wrong, or null. */
async function installBuild(root: string, C: string, m: CommitManifest): Promise<string | null> {
  const stage = path.join(C, "delta");
  const rank = (rel: string) => (rel.endsWith(".trace") ? 2 : rel.endsWith(".hash") ? 1 : 0);
  const build = path.join(root, ".lake", "build");
  for (const rel of [...m.removedBuild].sort((a, b) => rank(b) - rank(a))) await unlink(path.join(build, rel)).catch(() => {});
  const ordered = [...m.build].sort((a, b) => rank(a.rel) - rank(b.rel));
  for (const [i, f] of ordered.entries()) {
    if (i === Math.floor(ordered.length / 2)) await COMMIT_STEP.at("build-half");
    await mkdir(path.dirname(path.join(build, f.rel)), { recursive: true });
    await rename(path.join(stage, f.rel), path.join(build, f.rel));
  }
  for (const f of m.build) if ((await shaOf(path.join(build, f.rel))) !== f.sha) return `${f.rel} is not the prepared file after its install`;
  return null;
}

async function stopLine(root: string, j: CommitJournal, why: string, log: (line: string) => void): Promise<CommitOutcome> {
  await writeJsonAtomic(commitJournalFile(root), { ...j, stopped: { at: new Date().toISOString(), why } } satisfies CommitJournal);
  log(`[commit] STOP THE LINE: ${why}\n` +
    `[commit] CURRENT stays generation ${j.base.gen}; the toolkit stays in flux (session ${j.id}); every commit waits. By hand: inspect the shared tree, then either\n` +
    `[commit]   fix it and \`paperformalizer toolkit-commit clear ${j.id}\` (Lake builds the tree as it stands; then it is stamped and published, the flux session closed, the journal removed), or\n` +
    `[commit]   \`paperformalizer toolkit-commit undo\` (the commit's files restored from ${path.join(j.dir, "orig")} first, then the same).\n` +
    `[commit] Never \`toolkit-flux off\` without \`--id\`: it may close this commit's session.`);
  return { kind: "wait", why: `the line is stopped: ${why}` };
}

/** Step 1, holding the locks: a commit's flux session no journal names closed (it died before its
 *  commit point: nothing was written); the journal's commit finished (rolled forward) — its id and
 *  outcome — or why every commit waits (the line stopped); null when nothing was on file. */
async function recoverLocked(root: string, log: (line: string) => void): Promise<{ id: string; outcome: CommitOutcome } | null> {
  const j = await readCommitJournal(root);
  for (const s of await fluxSessionsOpen(root)) {
    if (COMMIT_ID_RE.test(s.id) && s.id !== j?.id) {
      await closeFluxSession(root, s.id);
      log(`[commit] the flux session of commit ${s.id}, which ended before its commit point, closed (nothing was written)`);
    }
  }
  if (!j) return null;
  if (j.stopped) return { id: j.id, outcome: { kind: "wait", why: `the line is stopped since ${j.stopped.at} (commit ${j.id}): ${j.stopped.why.split("\n")[0]}` } };
  log(`[commit] commit ${j.id} was interrupted after its commit point: rolled forward`);
  const m = await readManifest(j.dir);
  if (!m) return { id: j.id, outcome: await stopLine(root, j, `commit ${j.id}'s manifest (${j.dir}) cannot be read`, log) };
  return { id: j.id, outcome: await land(root, j.dir, m, j, log, false) };
}

/** Prepared commits older than `COMMIT_ORPHAN_MS`: removed — never the journal's, nor `keep` (the
 *  one being committed). (2026-11-11) One the base moved past (`CURRENT` newer than its base) and
 *  bound to its base (no `offBaseReads`: step 2 can only say base-moved) loses its archive at once
 *  (`dropArchive`); one that may still land off its base never needs it, and keeps it. */
async function sweep(root: string, keep: string): Promise<void> {
  const j = await readCommitJournal(root);
  const cur = await currentGeneration(root);
  const t = await toolkitLayout(root);
  for (const e of await readdir(commitsDir(root)).catch(() => [] as string[])) {
    const dir = path.join(commitsDir(root), e);
    if ((j && path.resolve(j.dir) === dir) || dir === path.resolve(keep)) continue;
    const st = await stat(dir).catch(() => null);
    if (st && Date.now() - st.mtimeMs > COMMIT_ORPHAN_MS) await rm(dir, { recursive: true, force: true });
    else if (cur && existsSync(path.join(dir, "gen.tar.zst"))) {
      const m = await readManifest(dir);
      if (m && m.base.gen < cur.gen && !offBaseReads(root, t, m)) await dropArchive(root, dir);
    }
  }
}

/** (2026-11-11) A prepared commit that will never land (its base moved past it, or refused: `commitPrepared`):
 *  its archive (`gen.tar.zst`, half a GB on the shared disk) and its staged delta removed; its manifest, sources
 *  and `delta.tar` kept for the audit trail (the 24 h sweep removes it whole). Never the journal's commit. */
export async function dropArchive(root: string, C: string): Promise<void> {
  const j = await readCommitJournal(root);
  if (j && path.resolve(j.dir) === path.resolve(C)) return;
  await rm(path.join(C, "gen.tar.zst"), { force: true });
  await rm(path.join(C, "delta"), { recursive: true, force: true });
}

/** Whether a toolkit commit is on file (its journal) or one's flux session is open. */
export async function commitOnFile(toolkitRoot: string): Promise<boolean> {
  const root = path.resolve(toolkitRoot);
  return existsSync(commitJournalFile(root)) || (await fluxSessionsOpen(root)).some((s) => COMMIT_ID_RE.test(s.id));
}

/**
 * For every holder of the promotion lock besides a commit (a round-B apply or a study's coordinate
 * step before it prepares, the fallback of `withRebases`): a toolkit commit on file finished first — rolled forward
 * under an exclusive Lake hold — or, when it cannot be (the line stopped, a build killed), refused:
 * nothing builds, stamps or publishes over a commit. Nothing at all when none is on file.
 */
export async function honourCommit(toolkitRoot: string, log: (line: string) => void = (l) => console.warn(l)): Promise<void> {
  const root = path.resolve(toolkitRoot);
  if (!(await commitOnFile(root))) return;
  const r = await withinCommit(() => withLakeBuildLock(root, () => recoverLocked(root, log), "a toolkit commit on file, rolled forward first", log));
  if (r && r.outcome.kind !== "landed") {
    throw new Error(`a toolkit commit is on file and could not be finished (${r.outcome.why.split("\n")[0]}): no promotion goes on over it — \`paperformalizer toolkit-commit recover\`, \`clear <id>\` or \`undo\` settles it`);
  }
}

/** `toolkit-commit recover`: the journal's commit rolled forward under the locks — a stopped one
 *  too (its mark cleared: the owner fixed the cause). */
export async function recoverCommit(toolkitRoot: string, log: (line: string) => void = (l) => console.warn(l)): Promise<CommitOutcome | null> {
  const root = path.resolve(toolkitRoot);
  return locked(root, "toolkit-commit recover", log, async () => {
    const j = await readCommitJournal(root);
    if (j?.stopped) { const { stopped: _, ...rest } = j; await writeJsonAtomic(commitJournalFile(root), rest); }
    return (await recoverLocked(root, log))?.outcome ?? null;
  });
}

/** `toolkit-commit undo`: a stopped commit's sources restored from `orig/` (its added files
 *  removed) — refused when one is neither its own bytes nor the commit's — the toolkit built for
 *  real, stamped and published, the flux session closed, the journal removed. A failing build, or a
 *  signature that vouches for nothing, leaves the line stopped. */
export async function undoCommit(toolkitRoot: string, log: (line: string) => void = (l) => console.warn(l)): Promise<CommitOutcome> {
  const root = path.resolve(toolkitRoot);
  return locked(root, "toolkit-commit undo", log, async () => {
    const j = await readCommitJournal(root);
    if (!j) return { kind: "wait", why: "no commit is on file" };
    if (!j.stopped) return { kind: "wait", why: `commit ${j.id} is not stopped: \`toolkit-commit recover\` finishes it` };
    const m = await readManifest(j.dir);
    if (!m) return { kind: "wait", why: `commit ${j.id}'s manifest (${j.dir}) cannot be read` };
    for (const s of m.sources) {
      const sha = await shaOf(path.join(root, s.rel));
      if (sha !== s.before && sha !== s.after) return { kind: "wait", why: `${s.rel} is neither its bytes before commit ${m.id} nor the commit's: settle it by hand` };
    }
    for (const s of m.sources) {
      const at = path.join(root, s.rel);
      if (s.before === null) await unlink(at).catch(() => {});
      else if ((await shaOf(at)) !== s.before) await writeTextAtomic(at, await readFile(path.join(j.dir, "orig", s.rel), "utf8"));
    }
    if (m.barrel) {
      const at = path.join(root, m.barrel.rel);
      const now = await readFile(at, "utf8").catch(() => null);
      const drop = new Set(m.barrel.imports);
      if (now !== null) { const next = now.split("\n").filter((l) => !drop.has(l)).join("\n"); if (next !== now) await writeTextAtomic(at, next); }
    }
    const r = await COMMIT_LAKE.run(root, ["build", ...m.targets]);
    if (r.code !== 0) return stopLine(root, j, `undo of ${m.id}: \`lake build\` ${r.code === null ? "was killed" : `exited ${r.code}`}\n${tail(r.out)}`, log);
    const t = await toolkitLayout(root);
    const sig = await toolkitSignature(t);
    if (isDoubt(sig)) return stopLine(root, j, `undo of ${m.id}: the toolkit's signature cannot be read (${sig})`, log);
    const scope = await toolkitScope(t);
    if (!("why" in scope)) await recordToolkitClean(root, sig, scope);
    const g = await publishGeneration(root, sig, log);
    await closeFluxSession(root, m.id);
    await unlink(commitJournalFile(root)).catch(() => {});
    log(`[commit] ${m.id} undone; the toolkit is generation ${g?.gen ?? "?"}`);
    return { kind: "landed", gen: g?.gen ?? j.base.gen, slow: true, left: [], ms: {} };
  });
}

/** `toolkit-commit clear <id>`: a stopped commit settled by hand — the shared tree as it stands built
 *  for real (refused, the line still stopped, when it does not build or its signature vouches for
 *  nothing), stamped and published as the next generation, the commit's flux session closed, its
 *  journal and directory removed. Nothing restored, nothing recorded for the runs. */
export async function clearCommit(toolkitRoot: string, id: string, log: (line: string) => void = (l) => console.warn(l)): Promise<CommitOutcome> {
  const root = path.resolve(toolkitRoot);
  return locked(root, `toolkit-commit clear ${id}`, log, async () => {
    const j = await readCommitJournal(root);
    if (!j || j.id !== id) return { kind: "wait", why: `commit ${id} is not the one on file (${j?.id ?? "none"})` };
    if (!j.stopped) return { kind: "wait", why: `commit ${id} is not stopped: \`toolkit-commit recover\` finishes it` };
    const m = await readManifest(j.dir);
    const targets = m?.targets ?? await commitTargets(await toolkitLayout(root));
    const r = await COMMIT_LAKE.run(root, ["build", ...targets]);
    if (r.code !== 0) return stopLine(root, j, `clear of ${id}: \`lake build ${targets.join(" ")}\` ${r.code === null ? "was killed" : `exited ${r.code}`}\n${tail(r.out)}`, log);
    const t = await toolkitLayout(root);
    const sig = await toolkitSignature(t);
    if (isDoubt(sig)) return stopLine(root, j, `clear of ${id}: the toolkit's signature cannot be read (${sig})`, log);
    const scope = await toolkitScope(t);
    if (!("why" in scope)) await recordToolkitClean(root, sig, scope);
    // (as steps 9 of a commit: the declarations and the runs' records — the sources are installed)
    if (m?.ledger.length) {
      const { appendLedgerDeclarations } = await import("../toolkit/ledger.js");
      await appendLedgerDeclarations(path.join(root, "doc", "ledger.json"), m.ledger);
    }
    const g = await publishGeneration(root, sig, log);
    await closeFluxSession(root, id);
    for (const rec of m?.records ?? []) {
      await writeJsonAtomic(path.join(t.runsDir, rec.slug, "proposals", "landed", `${id}.json`), { id, gen: g?.gen ?? null, left: [], cleared: true, record: rec.record });
    }
    await unlink(commitJournalFile(root)).catch(() => {});
    await rm(j.dir, { recursive: true, force: true });
    log(`[commit] ${id} cleared by hand; the toolkit as it stands is generation ${g?.gen ?? "?"}`);
    return { kind: "landed", gen: g?.gen ?? j.base.gen, slow: true, left: [], ms: {} };
  });
}

export const TOOLKIT_COMMIT_USAGE =
  "Usage: paperformalizer toolkit-commit workspace <slug> [--papers A,B] [--toolkit <path>]\n" +
  "       paperformalizer toolkit-commit prepare <slug> [--toolkit <path>]\n" +
  "       paperformalizer toolkit-commit commit <id> [--toolkit <path>]\n" +
  "       paperformalizer toolkit-commit status|recover|undo [--toolkit <path>]\n" +
  "       paperformalizer toolkit-commit clear <id> [--toolkit <path>]\n" +
  "  workspace: <slug>'s private promotion workspace on this machine, pinned to the current generation and detached\n" +
  "  (the papers named are private copies), its path printed: edit and `lake build` there;\n" +
  "  prepare: its commit directory, once it is built (prints the id; the declarations its private ledger gained go with it);\n" +
  "  commit: install it in the shared toolkit as the next generation (landed, base-moved or wait); status: the journal and\n" +
  "  the prepared commits; recover: finish an interrupted or stopped commit; undo: restore a stopped commit's sources and rebuild;\n" +
  "  clear: a stopped commit settled by hand — the tree as it stands built, published, the commit's flux session closed";

/** `paperformalizer toolkit-commit …` (by hand; no pipeline caller yet). */
export async function runToolkitCommitCli(argv: string[], log: (m: string) => void = (m) => console.log(m)): Promise<void> {
  const opt = (name: string) => { const i = argv.indexOf(name); return i >= 0 ? argv[i + 1] ?? null : null; };
  const rest = argv.filter((a, i) => !a.startsWith("--") && !(i > 0 && argv[i - 1]!.startsWith("--")));
  const [which, arg] = rest;
  const { loadToolkitConfig } = await import("../toolkit/config.js");
  const root = loadToolkitConfig({ explicit: opt("--toolkit") }).toolkitRoot;
  const { workspacePath } = await import("./workspace.js");
  const print = (o: unknown) => log(typeof o === "string" ? o : JSON.stringify(o, null, 2));
  if (which === "workspace" && arg) {
    const papers = (opt("--papers") ?? "").split(",").filter(Boolean);
    print((await withPromoWorkspace(root, arg, papers, { log }, async (w) => w)).path);
  } else if (which === "prepare" && arg) {
    print(path.basename(await prepareCommit(root, workspacePath(root, `${arg}.promo`), { log })));
  } else if (which === "commit" && arg) {
    const r = await commitToolkit(root, arg, { log });
    print(r);
    if (r.kind !== "landed") process.exitCode = r.kind === "wait" ? 75 : 3;
  } else if (which === "status") {
    print({ journal: await readCommitJournal(root), current: await currentGeneration(root), gens: existsSync(gensDir(root)), prepared: await readdir(commitsDir(root)).catch(() => []) });
  } else if (which === "recover") {
    print((await recoverCommit(root, log)) ?? "no commit on file");
  } else if (which === "clear" && arg) {
    print(await clearCommit(root, arg, log));
  } else if (which === "undo") {
    print(await undoCommit(root, log));
  } else {
    throw new Error(TOOLKIT_COMMIT_USAGE);
  }
}
