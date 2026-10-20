import { spawn } from "node:child_process";
import { createHash } from "node:crypto";
import { existsSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { startUiServer } from "../../src/ui/server.js";
import type { ToolkitConfig } from "../../src/toolkit/config.js";

const SCRIPTS = path.join(__dirname, "..", "..", "scripts");
const run1 = (root: string, slug: string, phase: string) => {
  const run = path.join(root, "runs", slug);
  mkdirSync(path.join(run, "logs"), { recursive: true });
  writeFileSync(path.join(run, "state.json"), JSON.stringify({ verify: { phase, source: { input: `/papers/${slug}`, main_file: "m.tex" } } }));
  return run;
};
const exited = (c: ReturnType<typeof spawn>) => {
  let out = "";
  c.stdout?.on("data", (d) => { out += d; });
  c.stderr?.on("data", (d) => { out += d; });
  return new Promise<{ code: number | null; out: string }>((resolve) => c.on("exit", (code) => resolve({ code, out })));
};

describe("batch jobs: what the owner starts on the page is started by the job attached to the run", () => {
  it("the page writes a start request (once) and starts nothing; the job's watch reports it", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-batch-ui-"));
    const run = run1(root, "b1", "v1_5");
    // the job's driver is the session: here, this test's process
    const watch = spawn(process.execPath, [path.join(SCRIPTS, "orch.mjs"), "watch", "b1", "--toolkit", root, "--starts", "--timeout", "20"], {
      env: { ...process.env, THEOREMCHECKER_ORCH_TICK_MS: "200", THEOREMCHECKER_ORCH_SESSION_PID: String(process.pid), THEOREMCHECKER_ORCH_AGENT: "batch job t" },
    });
    const done = exited(watch);
    for (let k = 0; k < 200 && !existsSync(path.join(run, "orch.json")); k++) await new Promise((r) => setTimeout(r, 50));
    const orch = JSON.parse(readFileSync(path.join(run, "orch.json"), "utf8")) as { starts?: boolean; agent?: string; pid?: number };
    expect(orch).toMatchObject({ starts: true, agent: "batch job t", pid: process.pid });
    const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs"), lib: "Toolkit", papersLib: "Papers", divisions: [], baseLibraries: [], owner: { name: "O" }, leanToolchain: "x" } as unknown as ToolkitConfig;
    const ui = await startUiServer(cfg, { port: 0 });
    try {
      const base = new URL(ui.url).origin;
      const Cookie = ((await fetch(ui.url, { redirect: "manual" })).headers.get("set-cookie") ?? "").split(";")[0]!;
      const act = () => fetch(`${base}/api/runs/b1/action`, { method: "POST", headers: { Cookie, "X-TC": "1" }, body: JSON.stringify({ action: { kind: "resume" } }) });
      const r = await act();
      expect(r.status).toBe(200);
      expect(await r.json()).toMatchObject({ queued: true });
      const req = JSON.parse(readFileSync(path.join(run, "start_request.json"), "utf8")) as { argv: string[]; kind: string };
      expect(req.kind).toBe("resume");
      expect(req.argv).toEqual(["verify", "/papers/b1", "--toolkit", root, "--slug", "b1", "--resume"]);
      // nothing was started here, and a second request waits for the first
      expect(existsSync(path.join(run, "logs", ".run.active"))).toBe(false);
      expect((await act()).status).toBe(409);
      const w = await done;
      expect(w.code).toBe(0);
      expect(w.out).toContain("the owner asked the page to start the run (resume): start `theoremchecker verify /papers/b1");
    } finally {
      watch.kill();
      await ui.close();
    }
  }, 30_000);
});

describe("batch_orch.mjs: a job takes runs from the shared queue, gives each event to the run's agent, and stops on a spent account", () => {
  const UUID = "11111111-2222-3333-4444-555555555555";
  /** A stand-in `codex` on PATH, speaking `--json`: it records each call's argv and prompt, then prints `out`
   *  (JSON events, one per line) and exits with `code`; `failFirst`: the first call exits 1 with nothing; `act`: a
   *  call whose prompt says `when` first runs `node <argv>` (the agent acting on the run). */
  const fakeCodex = (out: object[], code = 0, failFirst = false, act?: { when: string; argv: string[] }) => {
    const dir = mkdtempSync(path.join(tmpdir(), "tc-batch-codex-"));
    const lines = [{ type: "thread.started", thread_id: UUID }, ...out].map((e) => JSON.stringify(e)).join("\n");
    writeFileSync(path.join(dir, "codex.cjs"), `
const fs = require("node:fs"), path = require("node:path");
fs.appendFileSync(path.join(__dirname, "argv"), process.argv.slice(2).join(" ") + "\\n");
const input = fs.readFileSync(0, "utf8");
fs.appendFileSync(path.join(__dirname, "prompt"), input);
const act = ${JSON.stringify(act ?? null)};
if (act && input.includes(act.when)) require("node:child_process").execFileSync(process.execPath, act.argv, { stdio: "ignore" });
if (${failFirst} && !fs.existsSync(path.join(__dirname, "once"))) {
  fs.writeFileSync(path.join(__dirname, "once"), ""); process.exit(1);
}
console.log(${JSON.stringify(lines)});
process.exit(${code});
`);
    return dir;
  };
  const calls = (dir: string) => readFileSync(path.join(dir, "argv"), "utf8").trim().split("\n");
  // one run at work: a paper behind it in the queue is not taken (it would start a real run)
  const driver = (root: string, queue: string, codexDir: string, ...extra: string[]) =>
    exited(spawn(process.execPath, [path.join(SCRIPTS, "batch_orch.mjs"), "--toolkit", root, "--queue", queue, "--runs", "1", "--sandbox", "read-only", ...extra], {
      env: { ...process.env, THEOREMCHECKER_TEST_CODEX_MOCK: path.join(codexDir, "codex.cjs"), THEOREMCHECKER_ORCH_TICK_MS: "200" },
    }));

  it("takes a run off the queue and gives its agent the guide and the event; words in a transcript are not the account's", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-batch-"));
    run1(root, "d1", "done");
    const queue = path.join(root, "queue.txt");
    writeFileSync(queue, "# papers\nd1\n");
    const codex = fakeCodex([{ type: "item.completed", item: { type: "agent_message", text: "the paper's usage limit and rate limit are fine" } }]);
    const r = await driver(root, queue, codex);
    expect(r.code).toBe(0);
    expect(readFileSync(queue, "utf8")).toBe("# papers\n");
    const prompt = readFileSync(path.join(codex, "prompt"), "utf8");
    expect(prompt).toContain("orchestrating agent of the TheoremChecker run `d1`");
    expect(prompt).toContain(path.join(".claude", "skills", "theoremchecker", "SKILL.md"));
    expect(prompt).toContain("session start");
    // the resume it is told to start names the run's own source
    expect(prompt).toContain(`bin/theoremchecker.ts verify /papers/d1 --toolkit ${root} --slug d1 --resume`);
    expect(calls(codex)[0]).toMatch(/^exec --json -m gpt-6\.1-sol -c model_reasoning_effort="high" --sandbox read-only -C \S+ --skip-git-repo-check -o \S+ -$/);
  }, 60_000);

  it("with --batch, sees its runs through and ends, leaving the rest of the queue to the next job", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-batch-"));
    run1(root, "b1", "done");
    run1(root, "b2", "done");
    const queue = path.join(root, "queue.txt");
    writeFileSync(queue, "b1\nb2\n");
    const r = await driver(root, queue, fakeCodex([]), "--batch");
    expect(r.code).toBe(75);
    expect(readFileSync(queue, "utf8")).toBe("b2\n");
    expect(r.out).not.toContain("b2: followed");
  }, 60_000);

  it("gives a failed call's event once more, to a fresh conversation", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-batch-"));
    run1(root, "d2", "done");
    const queue = path.join(root, "queue.txt");
    writeFileSync(queue, "d2\n");
    const codex = fakeCodex([], 0, true);
    const r = await driver(root, queue, codex);
    expect(r.code).toBe(0);
    expect(calls(codex)).toHaveLength(2);
    expect(calls(codex)[1]).toMatch(/^exec --json -m /);
  }, 60_000);

  it("keeps following a finished run whose agent asks the owner something, until the owner's reply is acted on", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-batch-"));
    const run = run1(root, "f1", "done");
    writeFileSync(path.join(run, "orch_requests.json"), JSON.stringify([{ id: "q1", at: "2026-10-15T00:00:00Z", text: "which reading of (3.2) is meant?" }]));
    const queue = path.join(root, "queue.txt");
    writeFileSync(queue, "f1\n");
    // the agent, told of the owner's reply, settles the request as the skill says (`orch.mjs done`)
    const codex = fakeCodex([], 0, false, { when: "replies on the page (m1)", argv: [path.join(SCRIPTS, "orch.mjs"), "done", "f1", "--toolkit", root, "q1"] });
    let ended = false;
    const job = driver(root, queue, codex).then((r) => { ended = true; return r; });
    // the run is finished, but its agent's question is open: the job stays attached, waiting for the owner
    await new Promise((r) => setTimeout(r, 8_000));
    expect(ended).toBe(false);
    expect(existsSync(path.join(run, "orch.json"))).toBe(true);
    writeFileSync(path.join(run, "orch_messages.json"), JSON.stringify([{ id: "m1", from: "user", re: "q1", text: "the second", at: "2026-10-15T01:00:00Z" }]));
    const r = await job;
    expect(r.code).toBe(0);
    expect(readFileSync(path.join(codex, "prompt"), "utf8")).toContain("the owner replies on the page (m1) to your request q1");
    expect(existsSync(path.join(run, "orch_requests.json"))).toBe(false);
    expect(JSON.parse(readFileSync(path.join(run, "orch_messages.json"), "utf8"))[0].handled).toBe(true);
    expect(readFileSync(queue, "utf8").trim()).toBe("");
  }, 60_000);

  it("asks the agent, once, to clear a request of a finished run whose answers it acted on, and leaves the run when it does", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-batch-"));
    const run = run1(root, "a1", "done");
    writeFileSync(path.join(run, "orch_requests.json"), JSON.stringify([{ id: "q1", at: "2026-10-15T00:00:00Z", text: "which reading?" }]));
    writeFileSync(path.join(run, "orch_messages.json"), JSON.stringify([{ id: "m1", from: "user", re: "q1", text: "the second", at: "2026-10-15T01:00:00Z", handled: true }]));
    const queue = path.join(root, "queue.txt");
    writeFileSync(queue, "a1\n");
    const codex = fakeCodex([], 0, false, { when: "still open on the page", argv: [path.join(SCRIPTS, "orch.mjs"), "done", "a1", "--toolkit", root, "q1"] });
    const r = await driver(root, queue, codex);
    expect(r.out).toContain("a1: finished, its request(s) q1 answered but open");
    expect(readFileSync(path.join(codex, "prompt"), "utf8")).toContain("your request(s) q1 to the owner are still open");
    expect(existsSync(path.join(run, "orch_requests.json"))).toBe(false);
    expect(r.out).toContain("a1: finished, and nothing is left to act on — left");
    expect(r.code).toBe(0);
    expect(readFileSync(queue, "utf8").trim()).toBe("");
  }, 60_000);

  it("tells the agent of a job attached to a finished run its bundle's blocking items again, though they were told before", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-batch-"));
    const run = run1(root, "t1", "done");
    mkdirSync(path.join(run, "bundle"), { recursive: true });
    const bundle = JSON.stringify({ todo: { blocking: 2 } });
    writeFileSync(path.join(run, "bundle", "bundle.json"), bundle);
    // told to a session that is gone (the record names this very bundle)
    const sig = createHash("sha256").update(bundle).digest("hex");
    const told = path.join(run, "logs", "bundle_todo.told");
    writeFileSync(told, sig);
    const queue = path.join(root, "queue.txt");
    writeFileSync(queue, "t1\n");
    const codex = fakeCodex([]);
    const r = await driver(root, queue, codex);
    expect(r.code).toBe(0);
    expect(readFileSync(path.join(codex, "prompt"), "utf8")).toContain("the run's bundle has 2 blocking item(s)");
    // told once to this job's agent (its session start, then the report), and recorded as told again
    expect(calls(codex)).toHaveLength(2);
    expect(readFileSync(told, "utf8")).toBe(sig);
  }, 60_000);

  it("resumes the run's conversation at its next event, refuses a start request the page did not make, and hands the run on at the deadline", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-batch-"));
    const run = run1(root, "r1", "v1_5");
    writeFileSync(path.join(run, "start_request.json"), JSON.stringify({ kind: "resume", argv: ["verify", "/elsewhere", "--toolkit", root, "--slug", "r1", "--resume", "--from-stage", "V1"], command: "x" }));
    writeFileSync(path.join(run, "orch_messages.json"), JSON.stringify([{ id: "m1", from: "user", text: "please look", at: "2026-10-15T00:00:00Z" }]));
    const queue = path.join(root, "queue.txt");
    writeFileSync(queue, "r1\n");
    const codex = fakeCodex([]);
    const r = await driver(root, queue, codex, "--hours", "0.006", "--grace-min", "0");
    expect(r.code).toBe(75);
    expect(r.out).toContain("start request not taken");
    expect(existsSync(path.join(run, "start_request.json"))).toBe(false);
    const c = calls(codex);
    expect(c.length).toBeGreaterThanOrEqual(2);
    expect(c[1]).toContain(`exec resume --json --skip-git-repo-check -m gpt-6.1-sol -c model_reasoning_effort="high" -c sandbox_mode="read-only" -o`);
    expect(c[1]).toContain(UUID);
    expect(readFileSync(path.join(codex, "prompt"), "utf8")).toContain("the owner writes to you on the page (m1)");
    expect(readFileSync(queue, "utf8")).toBe("r1\n");
  }, 60_000);

  it("stops at a spent account: the run goes back to the queue, the reason is kept, and no successor is asked for", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-batch-"));
    run1(root, "s1", "v1_5");
    const queue = path.join(root, "queue.txt");
    writeFileSync(queue, "s1\nnext=/papers/next\n");
    const r = await driver(root, queue, fakeCodex([{ type: "turn.failed", error: { message: "You have hit your usage limit." } }], 1));
    expect(r.code).toBe(76);
    expect(r.out).toContain("STOP: the Codex account looks spent");
    // the unfinished run is back at the head; the paper not yet taken stays
    expect(readFileSync(queue, "utf8")).toBe("s1\nnext=/papers/next\n");
    expect(readFileSync(`${queue}.stopped`, "utf8")).toContain("usage limit");
    // detached as it ended: the page shows no job attached
    expect(existsSync(path.join(root, "runs", "s1", "orch.json"))).toBe(false);
  }, 60_000);
});
