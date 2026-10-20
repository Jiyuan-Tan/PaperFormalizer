import { spawn } from "node:child_process";
import { mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";

describe("orch_watch_loop.mjs: one watch over several runs that re-arms itself", () => {
  const script = path.join(__dirname, "..", "..", "scripts", "orch_watch_loop.mjs");
  const env = { ...process.env, THEOREMCHECKER_ORCH_TICK_MS: "100", THEOREMCHECKER_ORCH_LOOP_PAUSE_MS: "300", THEOREMCHECKER_ORCH_APPEAR_MS: "300" };
  const until = async (f: () => boolean, what: string) => {
    for (let k = 0; k < 200 && !f(); k++) await new Promise((r) => setTimeout(r, 50));
    if (!f()) throw new Error(`never: ${what}`);
  };
  it("prints each new report once, prefixed with its run, and re-arms after it; a slug with no run is reported and left", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-orchloop-"));
    const run = path.join(root, "runs", "w1");
    mkdirSync(path.join(run, "logs"), { recursive: true });
    writeFileSync(path.join(run, "state.json"), "{}");
    const messages = path.join(run, "orch_messages.json");
    // a message not acted on: every arm returns with it at once
    writeFileSync(messages, JSON.stringify([{ id: "m1", from: "user", text: "first words", at: "x" }]));
    const c = spawn(process.execPath, [script, "--toolkit", root, "w1", "nope"], { env });
    let out = "";
    c.stdout.on("data", (d) => { out += d; });
    try {
      await until(() => out.includes("first words") && out.includes("[nope] not watched any more"), "the first report");
      expect(out).toMatch(/^\[w1\] \[orch\] w1: the owner writes to you on the page \(m1\): first words$/m);
      // several arms later, the standing report is still printed once
      await new Promise((r) => setTimeout(r, 1500));
      expect(out.split("first words").length - 1).toBe(1);
      // a new message changes the report: printed again, with both
      writeFileSync(messages, JSON.stringify([{ id: "m1", from: "user", text: "first words", at: "x" }, { id: "m2", from: "user", text: "second words", at: "y" }]));
      await until(() => out.includes("second words"), "the second report");
      expect(out).toContain("[w1] [orch] w1: the owner writes to you on the page (m2): second words");
      expect(out.split("[nope] not watched any more").length - 1).toBe(1);
      // an issue withdrawn and reported anew under the same id (or edited) is new: printed
      const issues = path.join(run, "owner_objections.json");
      writeFileSync(issues, JSON.stringify([{ id: "obj-1", node: "thm:a", kind: "finding", excerpt: "e", text: "FIRST issue", at: "t1" }]));
      await until(() => out.includes("FIRST issue"), "the first issue");
      writeFileSync(issues, JSON.stringify([{ id: "obj-1", node: "thm:b", kind: "finding", excerpt: "e", text: "SECOND issue", at: "t2" }]));
      await until(() => out.includes("SECOND issue"), "the issue reported anew under the same id");
      // words of the owner shaped like an id add nothing to what is known
      writeFileSync(issues, JSON.stringify([{ id: "obj-1", node: "thm:b", kind: "finding", excerpt: "e", text: "SECOND issue", at: "t2", handled: true }]));
      // stopped, it stops the watch it holds: none is left to take a report nobody prints
      // (both acted on, the next watch stays armed)
      writeFileSync(messages, JSON.stringify([{ id: "m1", from: "user", text: "first words", at: "x", handled: true }, { id: "m2", from: "user", text: "second words", at: "y", handled: true }]));
      const alive = (pid: number) => { try { process.kill(pid, 0); return true; } catch { return false; } };
      const watcher = () => { try { return JSON.parse(readFileSync(path.join(run, "orch.json"), "utf8")).watcher as number; } catch { return 0; } };
      await new Promise((r) => setTimeout(r, 1000));
      await until(() => watcher() > 0 && alive(watcher()), "a watch armed");
      const held = watcher();
      // still armed while the known messages stand (the page shows the watcher armed)
      expect(alive(held)).toBe(true);
      c.kill();
      await until(() => !alive(held), "the watch stopped with the loop");
    } finally { c.kill(); }
  }, 30_000);
  it("killed outright, the loop leaves no watch behind to take a report nobody prints", async () => {
    const root = mkdtempSync(path.join(tmpdir(), "tc-orchloop-"));
    const run = path.join(root, "runs", "w1");
    mkdirSync(path.join(run, "logs"), { recursive: true });
    writeFileSync(path.join(run, "state.json"), "{}");
    writeFileSync(path.join(run, "pipeline.jsonl"), JSON.stringify({ stage: "V1", status: "start", message: "a" }) + "\n");
    const c = spawn(process.execPath, [script, "--toolkit", root, "w1"], { env });
    const alive = (pid: number) => { try { process.kill(pid, 0); return true; } catch { return false; } };
    const orchJson = () => { try { return JSON.parse(readFileSync(path.join(run, "orch.json"), "utf8")) as { watcher?: number; seen?: string }; } catch { return {}; } };
    try {
      await until(() => !!orchJson().watcher && alive(orchJson().watcher!), "a watch armed");
      const held = orchJson().watcher!, seen = orchJson().seen;
      c.kill("SIGKILL");
      await until(() => !alive(held), "the orphaned watch ended");
      // the run moved meanwhile: nothing was handed over, so the next watch reports it
      writeFileSync(path.join(run, "pipeline.jsonl"), JSON.stringify({ stage: "V1", status: "checkpoint", message: "b" }) + "\n", { flag: "a" });
      await new Promise((r) => setTimeout(r, 400));
      expect(orchJson().seen).toBe(seen);
    } finally { c.kill("SIGKILL"); }
  }, 30_000);
});
