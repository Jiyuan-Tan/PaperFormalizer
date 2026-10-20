// `leansmith demo`: the recorded run of the demo paper played back on the real page, the stand-in
// agent taking what the owner sends as the cue for the next step.
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { afterAll, describe, expect, it } from "vitest";
import { DEMO_DATA_DIR, DemoDriver, loadDemoScript, TEMPLATE_TOOLKIT_DIR } from "../../src/demo/driver.js";
import { loadToolkitConfig } from "../../src/toolkit/config.js";
import { runDetail } from "../../src/ui/run_model.js";
import { startUiServer, type UiServer } from "../../src/ui/server.js";

function demoToolkit() {
  const root = mkdtempSync(path.join(tmpdir(), "tc-demo-"));
  const cfg = JSON.parse(readFileSync(path.join(TEMPLATE_TOOLKIT_DIR, "leansmith.json.example"), "utf8"));
  writeFileSync(path.join(root, "leansmith.json"), JSON.stringify(cfg));
  return root;
}
const until = async (cond: () => Promise<boolean>) => { for (let i = 0; i < 100 && !(await cond()); i++) await new Promise((r) => setTimeout(r, 30)); };

describe("the demo's recording", () => {
  it("every step's state is one the page reads, with the stand-in agent attached", async () => {
    const script = loadDemoScript();
    const root = demoToolkit();
    const driver = new DemoDriver(root, script, DEMO_DATA_DIR, 0);
    const cfg = loadToolkitConfig({ explicit: root });
    for (let n = 0; n < script.steps.length; n++) {
      driver.install(n);
      const d = await runDetail(cfg, script.slug);
      expect(d.summary.orch?.agent).toBe(script.agent);
      // the recording names this machine's paths through placeholders only
      expect(readFileSync(path.join(root, "runs", script.slug, "state.json"), "utf8")).not.toMatch(/@@(PAPER|TOOLKIT)@@/);
    }
    // a step that waits on the page names what it waits for
    expect(script.steps.filter((s) => s.advance && s.advance !== "next").every((s) => ["rule-repairs", "apply-promotion"].includes(s.advance!))).toBe(true);
  });
});

describe("the demo's page", () => {
  let ui: UiServer | undefined;
  afterAll(async () => { await ui?.close(); });
  it("moves on with the tour's Next and with what the owner sends, and answers a message", async () => {
    const script = loadDemoScript();
    const root = demoToolkit();
    const driver = new DemoDriver(root, script, DEMO_DATA_DIR, 0);
    driver.install(0);
    ui = await startUiServer(loadToolkitConfig({ explicit: root }), { port: 0, demo: driver });
    const base = new URL(ui.url).origin;
    const cookie = ((await fetch(ui.url, { redirect: "manual" })).headers.get("set-cookie") ?? "").split(";")[0]!;
    const get = async () => (await (await fetch(`${base}/api/demo`, { headers: { Cookie: cookie } })).json()) as { step: number; busy: boolean; expect: string | null };
    const post = (p: string, body: unknown = {}) => fetch(`${base}${p}`, { method: "POST", headers: { Cookie: cookie, "X-TC": "1", "Content-Type": "application/json" }, body: JSON.stringify(body) });
    expect(await get()).toMatchObject({ step: 0, busy: false });
    // to the first step that waits on the page, by Next
    const waits = script.steps.findIndex((s) => s.advance && s.advance !== "next");
    for (let n = 1; n <= waits; n++) { expect((await post("/api/demo/next")).status).toBe(200); await until(async () => (await get()).step === n && !(await get()).busy); }
    const at = await get();
    expect(at.expect).toBe(script.steps[waits]!.advance);
    // Next and a send that is not the step's are refused, and say what the step waits for
    expect((await post("/api/demo/next")).status).toBe(409);
    const wrong = at.expect === "rule-repairs" ? { kind: "apply-promotion", round: "B" } : { kind: "rule-repairs", accept: ["thm:x"] };
    const refused = await post(`/api/runs/${script.slug}/action`, { action: wrong });
    expect(refused.status).toBe(409);
    // the step's own: taken as the cue, nothing started
    const action = at.expect === "rule-repairs" ? { kind: "rule-repairs", accept: ["thm:amgm"] } : { kind: "apply-promotion", round: "B" };
    const sent = await post(`/api/runs/${script.slug}/action`, { action });
    expect(sent.status).toBe(200);
    expect(await sent.json()).toMatchObject({ demo: true });
    await until(async () => (await get()).step === waits + 1 && !(await get()).busy);
    expect((await get()).step).toBe(waits + 1);
    // a message is answered by the stand-in
    expect((await post(`/api/runs/${script.slug}/message`, { text: "Why accept this one?" })).status).toBe(200);
    const msgs = path.join(root, "runs", script.slug, "orch_messages.json");
    await until(async () => { try { return JSON.parse(readFileSync(msgs, "utf8")).some((m: { from: string }) => m.from === "agent"); } catch { return false; } });
    expect(JSON.parse(readFileSync(msgs, "utf8")).at(-1)).toMatchObject({ from: "agent", text: script.reply });
    // and the tour starts over
    expect(await (await post("/api/demo/restart")).json()).toMatchObject({ step: 0 });
  });
});
