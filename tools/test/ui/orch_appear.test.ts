import { spawn, type ChildProcess } from "node:child_process";
import { mkdirSync, mkdtempSync, writeFileSync } from "node:fs";
import { hostname, tmpdir } from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";

/** `orch.mjs watch` armed right after a launch: a run appears only once its runner has warmed up Lean. */
describe("orch.mjs watch: waiting for a run to appear", () => {
  const script = path.join(__dirname, "..", "..", "scripts", "orch.mjs");
  const env = { ...process.env, PAPERFORMALIZER_ORCH_APPEAR_MS: "300", PAPERFORMALIZER_ORCH_TICK_MS: "100" };
  const kids: ChildProcess[] = [];
  afterEach(() => { for (const k of kids.splice(0)) k.kill(); });
  const watch = (root: string, slug: string): Promise<{ code: number | null; err: string }> =>
    new Promise((resolve) => {
      const c = spawn(process.execPath, [script, "watch", slug, "--toolkit", root, "--timeout", "1"], { env });
      kids.push(c);
      let err = "";
      c.stderr.on("data", (d) => { err += d; });
      c.on("close", (code) => resolve({ code, err }));
    });

  it("with no runner of the run, gives up after the appear window (exit 66)", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-appear-"));
    const t0 = Date.now();
    const r = await watch(root, "ghost");
    expect(r.code).toBe(66);
    expect(r.err).toContain("no runner of it is live");
    expect(Date.now() - t0).toBeLessThan(5_000);
  }, 15_000);

  it("while its runner is live (still warming up Lean), waits past the window for state.json", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-appear-"));
    const run = path.join(root, "runs", "warm");
    mkdirSync(path.join(run, "logs"), { recursive: true });
    // a live process stands in for the runner: its heartbeat, written before state.json
    const runner = spawn(process.execPath, ["-e", "setTimeout(() => {}, 60000)"]);
    kids.push(runner);
    writeFileSync(path.join(run, "logs", ".run.active"), `${runner.pid} ${new Date().toISOString()} tok host=${hostname()} beat=15\n`);
    const done = watch(root, "warm");
    // seeded well after the 300 ms window
    await new Promise((r) => setTimeout(r, 1_500));
    writeFileSync(path.join(run, "state.json"), "{}");
    const r = await done;
    expect(r.code).not.toBe(66);
    expect(r.err).toContain("the runner is starting");
  }, 20_000);
});
