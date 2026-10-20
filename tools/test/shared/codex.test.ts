import { spawn } from "node:child_process";
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it, vi } from "vitest";

// The codex child is replaced by a scripted fake: `script(input)` decides each call's outcome.
type Result = { stdout: string; stderr: string; exitCode: number | null; killedDueToInactivity: boolean };
const calls: Array<{ input: string; at: number }> = [];
let script: (input: string) => Promise<Result> = async () => ok("{}");
vi.mock("../../src/workers/spawn.js", () => ({
  spawnWithInactivityTimeout: async (_cmd: string, _args: string[], opts: { input?: string }) => {
    const input = opts.input ?? "";
    calls.push({ input, at: Date.now() });
    return await script(input);
  },
}));

import { CodexAuthError, CODEX_AUTH_OK_FILE, fatalCodexAuthReason, resetCodexAuthForTest, warmCodexHomeUnderLock } from "../../src/shared/codex_auth.js";
import { effectiveSandboxMode, isTransientCodexFailure, resolveCodexSandboxMode, runCodex, setCodexSpawnStaggerForTest,
  setCodexTransientBackoffForTest, CODEX_SPAWN_STAGGER_MS, CODEX_TRANSIENT_BACKOFF_MS } from "../../src/shared/codex.js";
import { liveChildren, registerChild, resetChildRegistryForTest } from "../../src/shared/child_registry.js";

function ok(stdout: string): Result {
  return { stdout, stderr: "", exitCode: 0, killedDueToInactivity: false };
}
const REUSED =
  "ERROR: Your access token could not be refreshed because your refresh token was already used. Please log out and sign in again.";
const API_KEY_HINT =
  "ERROR: unexpected status 401 Unauthorized: Incorrect API key provided: eyJhbGci***fvMA. You can find your API key at https://platform.openai.com/account/api-keys., url: https://chatgpt.com/backend-api/codex/responses";
const isProbe = (input: string): boolean => input.startsWith("Reply with the single word OK.");
const sleep = (ms: number) => new Promise((r) => setTimeout(r, ms));

describe("fatal login vs transient failure", () => {
  it("classifies a dead login as fatal, never transient", () => {
    for (const text of [
      REUSED,
      "Your access token could not be refreshed. Please log out and sign in again.",
      "Your access token could not be refreshed because your refresh token was revoked. Please log out and sign in again.",
      API_KEY_HINT,
    ]) {
      expect(fatalCodexAuthReason(text)).not.toBeNull();
      // codex's own reconnect lines around it must not make it look like a blip
      expect(isTransientCodexFailure(`stream disconnected before completion\n${text}`)).toBe(false);
    }
    expect(fatalCodexAuthReason(`codex exited 1. stderr-tail=${REUSED}`)).toBe(
      "Your access token could not be refreshed because your refresh token was already used. Please log out and sign in again.",
    );
  });
  it("leaves capacity / 5xx / 429 / dropped connections transient and a usage limit or schema error neither", () => {
    for (const text of ["ERROR: Selected model is at capacity.", "api_error_status: 503 upstream", "stream disconnected before completion", "read ECONNRESET", "ERROR: exceeded retry limit, last status: 429 Too Many Requests"]) {
      expect(fatalCodexAuthReason(text)).toBeNull();
      expect(isTransientCodexFailure(text)).toBe(true);
    }
    expect(fatalCodexAuthReason("You've hit your usage limit.")).toBeNull();
    expect(isTransientCodexFailure("You've hit your usage limit.")).toBe(false);
    expect(isTransientCodexFailure("429 Too Many Requests: You exceeded your current quota (insufficient_quota)")).toBe(false);
    expect(isTransientCodexFailure("codex exited 1. stderr-tail=schema violation")).toBe(false);
  });
});

describe("runCodex under a subscription login", () => {
  let home: string;
  const saved = { home: process.env.CODEX_HOME, mode: process.env.THEOREMCHECKER_OPENAI_AUTH };
  beforeEach(async () => {
    home = await mkdtemp(path.join(os.tmpdir(), "tc-codex-auth-"));
    process.env.CODEX_HOME = home;
    process.env.THEOREMCHECKER_OPENAI_AUTH = "subscription";
    calls.length = 0;
    resetCodexAuthForTest();
    resetChildRegistryForTest();
    setCodexSpawnStaggerForTest(0);
    vi.spyOn(console, "warn").mockImplementation(() => {});
  });
  afterEach(async () => {
    vi.restoreAllMocks();
    setCodexSpawnStaggerForTest(CODEX_SPAWN_STAGGER_MS);
    if (saved.home === undefined) delete process.env.CODEX_HOME;
    else process.env.CODEX_HOME = saved.home;
    if (saved.mode === undefined) delete process.env.THEOREMCHECKER_OPENAI_AUTH;
    else process.env.THEOREMCHECKER_OPENAI_AUTH = saved.mode;
    await rm(home, { recursive: true, force: true });
  });
  const fanOut = (n: number) => Promise.all(Array.from({ length: n }, (_, i) => runCodex({ prompt: `shard ${i}`, cwd: home, leanLsp: false })));

  it("an empty reply to a schema-constrained call is retried; without a schema it is returned as is (live: three runs lost theirs in one second)", async () => {
    await writeFile(path.join(home, CODEX_AUTH_OK_FILE), `${new Date().toISOString()}\n`);
    setCodexTransientBackoffForTest([5, 5]);
    try {
      let n = 0;
      script = async () => ((n += 1) === 1 ? ok("") : ok('{"a":1}'));
      const out = await runCodex({ prompt: "grade", cwd: home, leanLsp: false, outputSchema: { type: "object" } });
      expect(out.stdout.trim()).toBe('{"a":1}');
      expect(n).toBe(2);
      n = 0;
      script = async () => { n += 1; return ok(""); };
      expect((await runCodex({ prompt: "edit files", cwd: home, leanLsp: false })).stdout.trim()).toBe("");
      expect(n).toBe(1);
    } finally {
      setCodexTransientBackoffForTest(CODEX_TRANSIENT_BACKOFF_MS);
    }
  });

  it("runs ONE warm-up call before a fan-out, and none for the next fan-out", async () => {
    script = async (input) => {
      await sleep(isProbe(input) ? 100 : 20);
      return ok("{}");
    };
    await fanOut(5);
    expect(calls.filter((c) => isProbe(c.input))).toHaveLength(1);
    expect(isProbe(calls[0]!.input)).toBe(true);
    expect(calls).toHaveLength(6);
    calls.length = 0;
    resetCodexAuthForTest(); // a fresh process: the recorded success is read from the home
    await fanOut(3);
    expect(calls.filter((c) => isProbe(c.input))).toHaveLength(0);
  });

  it("a dead login is not retried, stops the in-flight siblings, and fails the queued calls at once", async () => {
    await writeFile(path.join(home, CODEX_AUTH_OK_FILE), `${new Date().toISOString()}\n`);
    const pids: number[] = [];
    script = async (input) => {
      if (input.startsWith("fail")) {
        await sleep(300);
        return { stdout: "", stderr: `stream disconnected before completion\n${REUSED}`, exitCode: 1, killedDueToInactivity: false };
      }
      // A sibling: a real detached process, registered as a codex child, that runs until stopped.
      const child = spawn("sleep", ["30"], { detached: true, stdio: "ignore" });
      pids.push(child.pid!);
      const unregister = registerChild(child.pid, { kind: "codex", groupLeader: true, cmd: "sleep 30" });
      await new Promise((r) => child.once("exit", r));
      unregister();
      return { stdout: "partial", stderr: "", exitCode: null, killedDueToInactivity: false };
    };
    const t0 = Date.now();
    const inflight = ["fail", "sib 1", "sib 2"].map((p) => runCodex({ prompt: p, cwd: home, leanLsp: false }));
    await sleep(50);
    const results = await Promise.allSettled([...inflight, (async () => { await sleep(600); return runCodex({ prompt: "sib queued", cwd: home, leanLsp: false }); })()]);
    expect(results.map((r) => r.status)).toEqual(["rejected", "rejected", "rejected", "rejected"]);
    for (const r of results) expect((r as PromiseRejectedResult).reason).toBeInstanceOf(CodexAuthError);
    expect(calls.filter((c) => c.input.startsWith("fail"))).toHaveLength(1); // no retry
    expect(calls.filter((c) => c.input.startsWith("sib queued"))).toHaveLength(0); // never spawned
    expect(Date.now() - t0).toBeLessThan(10_000);
    expect(liveChildren()).toHaveLength(0);
    for (const pid of pids) expect(() => process.kill(pid, 0)).toThrow();
  });
});

describe("the warm-up lock across runners", () => {
  let home: string;
  beforeEach(async () => {
    home = await mkdtemp(path.join(os.tmpdir(), "tc-codex-lock-"));
    resetCodexAuthForTest();
  });
  afterEach(async () => {
    await rm(home, { recursive: true, force: true });
  });

  it("serializes two warm-ups on one home; the second sees the first's success and skips", async () => {
    let active = 0;
    let peak = 0;
    let probes = 0;
    const probe = async () => {
      probes += 1;
      active += 1;
      peak = Math.max(peak, active);
      await sleep(300);
      active -= 1;
    };
    await Promise.all([warmCodexHomeUnderLock(home, probe, () => {}), warmCodexHomeUnderLock(home, probe, () => {})]);
    expect(probes).toBe(1);
    expect(peak).toBe(1);
  });
});

describe("one at a time near the access token's expiry", () => {
  let home: string;
  const saved = { home: process.env.CODEX_HOME, mode: process.env.THEOREMCHECKER_OPENAI_AUTH };
  const warn = vi.fn();
  /** A ChatGPT `auth.json` whose access token expires at `expMs` (a fake JWT; only `exp` matters). */
  const writeAuth = async (expMs: number) => {
    const b64 = (o: object) => Buffer.from(JSON.stringify(o)).toString("base64url");
    const jwt = `${b64({ alg: "none" })}.${b64({ exp: Math.floor(expMs / 1000), iat: Math.floor(Date.now() / 1000) })}.sig`;
    await writeFile(path.join(home, "auth.json"), JSON.stringify({ auth_mode: "chatgpt", tokens: { access_token: jwt, refresh_token: "r" }, last_refresh: new Date().toISOString() }));
  };
  // Each call's [start, end]; `onCall` runs inside the call (e.g. codex rewriting auth.json).
  let spans: Array<[number, number]> = [];
  let onCall: (i: number) => Promise<void> = async () => {};
  const peak = (xs: Array<[number, number]>) => Math.max(...xs.map(([a]) => xs.filter(([s, e]) => s <= a && a < e).length));
  beforeEach(async () => {
    home = await mkdtemp(path.join(os.tmpdir(), "tc-codex-exp-"));
    process.env.CODEX_HOME = home;
    process.env.THEOREMCHECKER_OPENAI_AUTH = "subscription";
    resetCodexAuthForTest();
    setCodexSpawnStaggerForTest(0);
    await writeFile(path.join(home, CODEX_AUTH_OK_FILE), `${new Date().toISOString()}\n`);
    spans = [];
    onCall = async () => {};
    warn.mockReset();
    vi.spyOn(console, "warn").mockImplementation(warn);
    script = async () => {
      const i = spans.length;
      const span: [number, number] = [Date.now(), Number.POSITIVE_INFINITY];
      spans.push(span);
      await onCall(i);
      await sleep(120);
      span[1] = Date.now();
      return ok("{}");
    };
  });
  afterEach(async () => {
    vi.restoreAllMocks();
    setCodexSpawnStaggerForTest(CODEX_SPAWN_STAGGER_MS);
    if (saved.home === undefined) delete process.env.CODEX_HOME;
    else process.env.CODEX_HOME = saved.home;
    if (saved.mode === undefined) delete process.env.THEOREMCHECKER_OPENAI_AUTH;
    else process.env.THEOREMCHECKER_OPENAI_AUTH = saved.mode;
    await rm(home, { recursive: true, force: true });
  });
  const fanOut = (n: number) => Promise.all(Array.from({ length: n }, (_, i) => runCodex({ prompt: `shard ${i}`, cwd: home, leanLsp: false })));
  const logged = (re: RegExp) => warn.mock.calls.filter((c) => re.test(String(c[0]))).length;

  it.each([
    ["within the window", 30 * 60_000],
    ["already expired", -60_000],
  ])("runs the calls one at a time when the token expires %s", async (_label, offset) => {
    await writeAuth(Date.now() + offset);
    await fanOut(4);
    expect(spans).toHaveLength(4);
    expect(peak(spans)).toBe(1);
    expect(logged(/run one at a time/)).toBe(1);
    expect(logged(/in parallel again/)).toBe(0);
  });

  it("goes parallel again once a call has rewritten auth.json with a later expiry", async () => {
    await writeAuth(Date.now() + 10 * 60_000);
    onCall = async (i) => {
      if (i === 0) await writeAuth(Date.now() + 10 * 24 * 3_600_000); // codex refreshed the token
    };
    await fanOut(5);
    const [first, ...rest] = spans;
    expect(rest.every(([s]) => s >= first![1])).toBe(true); // the refreshing call ran alone
    expect(peak(rest)).toBeGreaterThan(1); // the rest ran in parallel
    expect(logged(/run one at a time/)).toBe(1);
    expect(logged(/in parallel again/)).toBe(1);
  });
});

describe("resolveCodexSandboxMode", () => {
  it("keeps workspace-write as the portable default", () => {
    expect(resolveCodexSandboxMode({ env: {} })).toBe("workspace-write");
  });

  it("lets the environment override local configuration", () => {
    expect(
      resolveCodexSandboxMode({
        env: { THEOREMCHECKER_CODEX_SANDBOX: "workspace-write" },
        configured: "danger-full-access",
      }),
    ).toBe("workspace-write");
  });

  it("fails closed on an invalid override", () => {
    expect(() => resolveCodexSandboxMode({ env: { THEOREMCHECKER_CODEX_SANDBOX: "read-only" } })).toThrow(
      /must be workspace-write or danger-full-access/,
    );
  });
});

describe("effectiveSandboxMode (per-call narrowing)", () => {
  it("honours a narrowing under workspace-write, and never replaces a configured danger-full-access", () => {
    expect(effectiveSandboxMode(undefined, "workspace-write")).toBe("workspace-write");
    expect(effectiveSandboxMode("read-only", "workspace-write")).toBe("read-only");
    expect(effectiveSandboxMode("workspace-write", "workspace-write")).toBe("workspace-write");
    // danger-full-access in the config means Codex's sandbox cannot start on this host: every
    // call uses it, whatever the call asked for.
    expect(effectiveSandboxMode(undefined, "danger-full-access")).toBe("danger-full-access");
    expect(effectiveSandboxMode("read-only", "danger-full-access")).toBe("danger-full-access");
    expect(effectiveSandboxMode("workspace-write", "danger-full-access")).toBe("danger-full-access");
  });
});
