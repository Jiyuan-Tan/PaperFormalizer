/**
 * The ChatGPT login under one CODEX_HOME, as the runner's parallel codex calls see it.
 *
 * The failure this guards against (two accounts lost their login): a fan-out starts N
 * `codex exec` processes under ONE login. When its access token needs refreshing, every process
 * refreshes at once with the same single-use refresh token; the first wins, the rest are refused
 * ("refresh token was already used"), and the login is revoked for all of them — a human must run
 * `codex login --device-auth` again. Four measures:
 *
 *   1. FATAL, NOT TRANSIENT: a dead login is classified (`fatalCodexAuthReason`) and thrown as a
 *      `CodexAuthError` naming the home and the remedy; the in-flight siblings are stopped, since
 *      each would fail the same way (retrying only burns time, or the next account).
 *   2. WARM FIRST: before calls start under a home with no recent success, ONE small probe call
 *      runs alone, so any refresh happens in one process (`ensureCodexAuthWarm`); concurrent
 *      callers in this process wait on that one probe.
 *   3. ACROSS PROCESSES: the probe holds a per-home file lock, so two runners sharing a home
 *      serialize their refresh; the second then sees the first's recorded success and skips.
 *   4. NEAR EXPIRY, ONE AT A TIME: a probe cannot refresh a token that is still valid, so a token
 *      expiring in the middle of a fan-out would still race. While the access token in `auth.json`
 *      has less than `CODEX_TOKEN_SERIALIZE_MS` left, calls under the home run one at a time (an
 *      in-process semaphore plus the same file lock) until `auth.json` carries a later expiry.
 *
 * The success record is a timestamp IN the file (NFS mtimes are unreliable), in the home itself.
 */
import { mkdir, readFile, rename, stat, writeFile } from "node:fs/promises";
import path from "node:path";
import lockfile from "proper-lockfile";

/** A success under a home within this window makes the warm probe unnecessary. Tokens live for
 * days, so a call that succeeded this recently proves the login is good for the next fan-out. */
export const CODEX_AUTH_FRESH_MS = 20 * 60_000;

/** The file (in the codex home) holding the time of the last successful call. */
export const CODEX_AUTH_OK_FILE = ".theoremchecker_auth_ok";
/** Held by the warm probe and by every call made one at a time near expiry. */
const WARM_LOCK_FILE = ".theoremchecker_warm.lock";

/** Below this much remaining life of the access token, codex calls under the home run one at a time. */
export const CODEX_TOKEN_SERIALIZE_MS = 2 * 60 * 60_000;

/** The login under a CODEX_HOME is dead: no retry can succeed. */
export class CodexAuthError extends Error {
  constructor(
    public readonly codexHome: string,
    public readonly reason: string,
  ) {
    super(
      `the codex login under CODEX_HOME=${codexHome} is no longer valid (${reason}). This is not a transient ` +
        `failure and was not retried; the other codex calls of this run were stopped. Remedy: run ` +
        `\`CODEX_HOME=${codexHome} codex login --device-auth\` and resume with --resume, or resume with ` +
        `another CODEX_HOME.`,
    );
    this.name = "CodexAuthError";
  }
}

/** Rethrow a dead-login error from a catch that otherwise degrades a failed call (it must halt). */
export function rethrowCodexAuthError(err: unknown): void {
  if (err instanceof CodexAuthError) throw err;
}

/**
 * The line of codex's output saying the login is dead, or null. Codex prints these when the
 * refresh token was reused/revoked/expired, and a 401 on the access token itself reads
 * "Incorrect API key provided: … You can find your API key at https://platform.openai.com/…".
 * Only the tail is read: the head of codex's stderr echoes the prompt.
 */
export function fatalCodexAuthReason(text: string): string | null {
  const tail = text.slice(-8_000);
  const re =
    /refresh token was already used|refresh token (?:was revoked|has expired)|log out and sign in again|could not be refreshed|platform\.openai\.com\/account\/api-keys|Incorrect API key provided/i;
  const line = tail.split(/\r?\n/).reverse().find((l) => re.test(l));
  if (!line) return null;
  const m = /Your (?:access token|authentication session)[^.]*\.(?: Please[^.]*\.)?/i.exec(line);
  return (m?.[0] ?? line).trim().slice(-300);
}

// ─── the success record ─────────────────────────────────────────────────────────

const lastOk = new Map<string, number>();

async function readLastOk(home: string): Promise<number> {
  const mem = lastOk.get(home) ?? 0;
  const raw = await readFile(path.join(home, CODEX_AUTH_OK_FILE), "utf8").catch(() => "");
  const disk = Date.parse(raw.trim());
  return Math.max(mem, Number.isFinite(disk) ? disk : 0);
}

/** Whether a call under `home` succeeded within `CODEX_AUTH_FRESH_MS`. */
export async function codexAuthFresh(home: string, now: number = Date.now()): Promise<boolean> {
  return now - (await readLastOk(home)) < CODEX_AUTH_FRESH_MS;
}

/** Record a successful call under `home` (throttled: the file is rewritten at most once a minute). */
export async function recordCodexAuthOk(home: string, now: number = Date.now()): Promise<void> {
  if (now - (lastOk.get(home) ?? 0) < 60_000) return;
  lastOk.set(home, now);
  try {
    const file = path.join(home, CODEX_AUTH_OK_FILE);
    const tmp = `${file}.${process.pid}.tmp`;
    await writeFile(tmp, `${new Date(now).toISOString()}\n`, "utf8");
    await rename(tmp, file);
  } catch {
    /* best-effort: the in-memory record still skips this process's next warm-up */
  }
}

// ─── the dead-login marker (this process) ───────────────────────────────────────

const dead = new Map<string, CodexAuthError>();

/** The dead-login error recorded for `home` in this process, if any. */
export function codexAuthDead(home: string): CodexAuthError | undefined {
  return dead.get(home);
}

/** Record `home`'s login as dead; returns the error to throw (the first one recorded). */
export function markCodexAuthDead(home: string, reason: string): { error: CodexAuthError; first: boolean } {
  const had = dead.get(home);
  if (had) return { error: had, first: false };
  const error = new CodexAuthError(home, reason);
  dead.set(home, error);
  return { error, first: true };
}

// ─── the warm-up ────────────────────────────────────────────────────────────────

/**
 * Take the `proper-lockfile` lock `lockName` in one codex home; returns its release. `waitMs`
 * bounds the wait behind another holder: it must exceed what the lock protects, or a process
 * queued behind a slow holder fails its stage.
 */
async function lockCodexHome(home: string, lockName: string, waitMs: number): Promise<() => Promise<void>> {
  await mkdir(home, { recursive: true });
  const lockTarget = path.join(home, lockName);
  if (!(await stat(lockTarget).then(() => true).catch(() => false))) {
    await writeFile(lockTarget, "{}\n", { encoding: "utf8", mode: 0o600 });
  }
  return await lockfile.lock(lockTarget, {
    stale: 10 * 60_000,
    retries: { retries: Math.ceil(waitMs / 10_000) + 10, factor: 1.5, minTimeout: 200, maxTimeout: 10_000 },
    realpath: false,
    // The default rethrows from a refresh timer (an uncaught exception killing the run); on an NFS
    // home a stalled mtime update is transient, so warn instead.
    onCompromised: (err: Error) => {
      console.warn(`[codex-auth] lock ${lockName} compromised (continuing): ${err.message}`);
    },
  });
}

/** `proper-lockfile` mutex over one codex home (`lockName` inside it); waits up to ~9 min (a cold
 * `codex login` or a warm probe takes a few minutes at most). */
export async function withCodexHomeLock<T>(home: string, lockName: string, action: () => Promise<T>): Promise<T> {
  const release = await lockCodexHome(home, lockName, 9 * 60_000);
  try {
    return await action();
  } finally {
    await release();
  }
}

/**
 * The warm probe under the cross-process lock: re-checks freshness inside the lock (the runner
 * queued ahead may just have warmed the home), else runs `probe` once and records its success.
 * A probe failing with a dead login throws `CodexAuthError`; any other failure is logged and the
 * calls go ahead (they then report their own error, as before).
 */
export async function warmCodexHomeUnderLock(
  home: string,
  probe: () => Promise<void>,
  log: (line: string) => void = (l) => console.warn(l),
): Promise<void> {
  // The same lock is held by calls made one at a time near expiry (each up to a long call), so the
  // probe may wait behind one: a long wait budget.
  const release = await lockCodexHome(home, WARM_LOCK_FILE, SERIAL_WAIT_MS);
  try {
    if (await codexAuthFresh(home)) return;
    const t0 = Date.now();
    try {
      await probe();
    } catch (err) {
      if (err instanceof CodexAuthError) throw err;
      log(`[codex-auth] warm-up call under CODEX_HOME=${home} failed (${err instanceof Error ? err.message.slice(0, 200) : String(err)}); continuing`);
      return;
    }
    await recordCodexAuthOk(home);
    log(`[codex-auth] warm-up call under CODEX_HOME=${home} succeeded in ${Math.round((Date.now() - t0) / 1000)}s`);
  } finally {
    await release();
  }
}

const warming = new Map<string, Promise<void>>();

/**
 * Make sure the login under `home` was used successfully within `CODEX_AUTH_FRESH_MS` before a
 * call starts: if not, ONE probe runs (single-flight in this process, file-locked across
 * processes) and every concurrent caller waits for it.
 */
export async function ensureCodexAuthWarm(
  home: string,
  probe: () => Promise<void>,
  log?: (line: string) => void,
): Promise<void> {
  const known = dead.get(home);
  if (known) throw known;
  if (await codexAuthFresh(home)) return;
  let p = warming.get(home);
  if (!p) {
    p = warmCodexHomeUnderLock(home, probe, log).finally(() => warming.delete(home));
    warming.set(home, p);
  }
  await p;
}

// ─── one at a time near expiry ──────────────────────────────────────────────────

/** How long a call queued behind calls made one at a time may wait for the file lock. */
const SERIAL_WAIT_MS = 6 * 60 * 60_000;

/**
 * Expiry (ms since the epoch) of the access token in `home`'s `auth.json`, read from the JWT's
 * `exp` claim; null when the file is unreadable or carries no expiry. Nothing else is kept.
 */
export async function codexTokenExp(home: string): Promise<number | null> {
  try {
    const auth = JSON.parse(await readFile(path.join(home, "auth.json"), "utf8")) as { tokens?: { access_token?: unknown } };
    const jwt = auth.tokens?.access_token;
    if (typeof jwt !== "string") return null;
    const payload = JSON.parse(Buffer.from(jwt.split(".")[1] ?? "", "base64url").toString("utf8")) as { exp?: unknown };
    return typeof payload.exp === "number" && Number.isFinite(payload.exp) ? payload.exp * 1000 : null;
  } catch {
    return null;
  }
}

const serialTail = new Map<string, Promise<void>>();
const serialOn = new Set<string>();

/** The in-process semaphore of 1 for `home`: resolves with its release once every earlier holder released. */
async function takeSerialTurn(home: string): Promise<() => void> {
  const prev = serialTail.get(home) ?? Promise.resolve();
  let release!: () => void;
  const mine = new Promise<void>((r) => (release = r));
  serialTail.set(home, prev.then(() => mine));
  await prev;
  return release;
}

const nearExpiry = (exp: number | null): exp is number => exp !== null && exp - Date.now() < CODEX_TOKEN_SERIALIZE_MS;

/**
 * The slot a codex call under `home` runs in; returns its release. While the access token has less
 * than `CODEX_TOKEN_SERIALIZE_MS` left (or has expired), the slot is exclusive — this process's
 * semaphore plus the home's file lock — so the refresh at expiry happens in one call only. Each
 * turn re-reads `auth.json`: once a call has refreshed it (a later expiry), calls run in parallel
 * again. One log line when calls start running one at a time, one when they stop.
 */
export async function acquireCodexCallSlot(
  home: string,
  log: (line: string) => void = (l) => console.warn(l),
): Promise<() => Promise<void>> {
  for (;;) {
    const exp = await codexTokenExp(home);
    if (!nearExpiry(exp)) {
      if (serialOn.delete(home)) {
        log(`[codex-auth] the access token under CODEX_HOME=${home} was refreshed${exp !== null ? ` (now expires ${new Date(exp).toISOString()})` : ""}: codex calls run in parallel again`);
      }
      return async () => {};
    }
    if (!serialOn.has(home)) {
      serialOn.add(home);
      log(`[codex-auth] the access token under CODEX_HOME=${home} expires ${new Date(exp).toISOString()} (under ${Math.round(CODEX_TOKEN_SERIALIZE_MS / 60_000)} min): codex calls run one at a time until it is refreshed`);
    }
    const releaseTurn = await takeSerialTurn(home);
    // The call ahead may have refreshed the token while this one waited.
    if (!nearExpiry(await codexTokenExp(home))) {
      releaseTurn();
      continue;
    }
    let releaseFile: () => Promise<void>;
    try {
      releaseFile = await lockCodexHome(home, WARM_LOCK_FILE, SERIAL_WAIT_MS);
    } catch (err) {
      releaseTurn();
      throw err;
    }
    return async () => {
      try {
        await releaseFile();
      } finally {
        releaseTurn();
      }
    };
  }
}

/** Test-only: forget the in-memory records. */
export function resetCodexAuthForTest(): void {
  lastOk.clear();
  dead.clear();
  warming.clear();
  serialTail.clear();
  serialOn.clear();
}
