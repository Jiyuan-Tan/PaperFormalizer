// Full auto (`verify --full-auto`): the owner's decisions — a repair that would weaken a main result,
// the promotion rounds — take the agent's recommendations, carried out by the recommendation that
// completes them (`orch.mjs recommend`) and listed for the owner's review.
import { spawnSync } from "node:child_process";
import { existsSync, mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { weakeningRepairGuidance } from "../../src/checkpoint_playbook.js";
import { parseChecklist, recommendationKeys, recommendedDecisions, setDecisions } from "../../src/proposals/checklist.js";
import { roundAStopMessage } from "../../src/proposals/round_a.js";
import type { ProposalBatch } from "../../src/proposals/schema.js";
import type { ToolkitConfig } from "../../src/toolkit/config.js";
import { runSummary } from "../../src/ui/run_model.js";
import { parseVerifyArgsForTest } from "../../src/verify/cli.js";

const script = path.join(__dirname, "..", "..", "scripts", "orch.mjs");

/** A run under a fresh toolkit, and a stand-in CLI that records the argv it was started with. */
function fixture(state: Record<string, unknown>) {
  const root = mkdtempSync(path.join(tmpdir(), "tc-full-auto-"));
  const run = path.join(root, "runs", "fa");
  mkdirSync(path.join(run, "proposals"), { recursive: true });
  writeFileSync(path.join(run, "state.json"), JSON.stringify(state));
  const started = path.join(root, "started.json");
  const cli = path.join(root, "cli.mjs");
  writeFileSync(cli, `import { writeFileSync } from "node:fs"; writeFileSync(${JSON.stringify(started)}, JSON.stringify(process.argv.slice(2)));\n`);
  const orch = (...args: string[]) => spawnSync(process.execPath, [script, args[0]!, "fa", "--toolkit", root, ...args.slice(1)], { encoding: "utf8", env: { ...process.env, THEOREMCHECKER_ORCH_CLI: cli } });
  const startedArgv = async (): Promise<string[] | null> => {
    for (let i = 0; i < 100 && !existsSync(started); i++) await new Promise((r) => setTimeout(r, 50));
    return existsSync(started) ? JSON.parse(readFileSync(started, "utf8")) : null;
  };
  return { root, run, orch, started, startedArgv };
}

describe("verify --full-auto", () => {
  it("is auto mode and is said at the halts it changes", () => {
    const p = parseVerifyArgsForTest(["paper.tex", "--full-auto"]);
    expect(p.fullAuto).toBe(true);
    expect(p.auto).toBe(true);
    expect(parseVerifyArgsForTest(["paper.tex", "--auto"]).fullAuto).toBe(false);
    expect(weakeningRepairGuidance(true, true)).toContain("FULL AUTO — the owner delegated this decision");
    expect(weakeningRepairGuidance(true)).toContain("this decision is still the user's");
    const rec = { status: "pending_user", checklist_path: "/c.md" } as Parameters<typeof roundAStopMessage>[2];
    expect(roundAStopMessage({ toolkitRoot: "/tk" } as ToolkitConfig, "s", rec, 2, false, true)).toContain("FULL AUTO, the owner delegated the round");
  });
});

describe("recommendedDecisions: the pending items take the agent's recommendations", () => {
  it("enters each recommendation written for the item as it stands, keeps the owner's own, names the rest", () => {
    const batch = { round: "B", proposals: [
      { id: "b-x", verdict: "propose", content: "x", target_module: "Toolkit/Foundations/A.lean", source: { kind: "paper_decl", is_paper_result: false }, new_topic: { path: "Foundations/New", scope: "s" } },
      { id: "b-y", verdict: "propose", content: "y", target_module: "Toolkit/Foundations/B.lean", source: { kind: "paper_decl", is_paper_result: false } },
      { id: "b-z", verdict: "propose", content: "z", target_module: "Toolkit/Foundations/C.lean", source: { kind: "paper_decl", is_paper_result: false } },
    ] } as unknown as ProposalBatch;
    const keys = recommendationKeys(batch);
    const md = ["## topic · Foundations/New", "```decision", "decision: pending", "```", "## b-x · X", "```decision", "decision: pending", "```", "## b-y · Y", "```decision", "decision: defer", "```", "## b-z · Z", "```decision", "decision: pending", "```", ""].join("\n");
    const recs = {
      "topic:Foundations/New": { kind: "accept", why: "nothing holds it", of: keys.get("topic:Foundations/New") },
      "b-x": { kind: "accept_with_edits", why: "a better home", of: keys.get("b-x") },
      "b-y": { kind: "accept", why: "the owner decided it already", of: keys.get("b-y") },
      "b-z": { kind: "accept", why: "on an earlier batch's entry", of: "0000000000000000" },
    };
    const { decisions, missing } = recommendedDecisions(batch, parseChecklist(md, batch), recs);
    expect(missing).toEqual(["b-z"]);
    expect(decisions).toEqual({
      "topic:Foundations/New": { kind: "accept", note: "as the agent recommended: nothing holds it" },
      "b-x": { kind: "accept_with_edits", edits: { target_module: "Toolkit/Foundations/A.lean" }, note: "as the agent recommended: a better home" },
    });
    // what it enters is what the apply reads
    expect(parseChecklist(setDecisions(md, decisions), batch)).toMatchObject({ "b-x": { kind: "accept_with_edits" }, "b-y": { kind: "defer" }, "b-z": { kind: "pending" } });
  });
});

describe("orch.mjs on a full-auto run", () => {
  const item = (node: string) => ({ node, printed: "p", proposed: `q ${node}`, given_up: "g", detail: "d", witness: null });
  const weak = (fullAuto: boolean) => ({ full_auto: fullAuto, stage_completed: "V1.5", verify: { phase: "v1_5", source: { input: "/papers/p.tex" }, weakening_repair: { status: "pending", items: [item("thm:a"), item("thm:b"), item("thm:c")] } } });

  it("the recommendation that completes the repairs resumes the run with them, listed for review", async () => {
    const f = fixture(weak(true));
    let r = f.orch("recommend", "repair", "thm:a", "accept", "the weaker rate is what is proved");
    expect(r.status).toBe(0);
    expect(r.stdout).toContain("1 of 3 repair(s) recommended");
    f.orch("recommend", "repair", "thm:b", "decline", "the bound is false");
    r = f.orch("recommend", "repair", "thm:c", "redo", "a better repair exists", "--guidance", "keep the rate, add $n>1$");
    expect(r.stdout).toContain("full auto: every item is recommended — started theoremchecker verify");
    expect(await f.startedArgv()).toEqual(["verify", "--toolkit", f.root, "--slug", "fa", "--resume", "--accept-repair", "thm:a", "--decline-repair", "thm:b: the bound is false", "--redo-repair", "thm:c: keep the rate, add $n>1$"]);
    const reviews = JSON.parse(readFileSync(path.join(f.run, "orch_decisions.json"), "utf8"));
    expect(reviews.map((d: { node: string }) => d.node)).toEqual(["thm:a", "thm:b", "thm:c"]);
    expect(reviews[2].text).toContain('Full auto: redo, with the guidance "keep the rate, add $n>1$"');
  });

  it("starts nothing on a run that is not in full auto", async () => {
    const f = fixture(weak(false));
    for (const n of ["thm:a", "thm:b", "thm:c"]) expect(f.orch("recommend", "repair", n, "accept", "fine").stdout).toBe("");
    await new Promise((r) => setTimeout(r, 300));
    expect(existsSync(f.started)).toBe(false);
    expect(existsSync(path.join(f.run, "orch_decisions.json"))).toBe(false);
  });

  it("the recommendation that completes a round applies it as recommended, one review entry", async () => {
    const f = fixture({ full_auto: true, verify: { phase: "proposals_A", source: { input: "/p" }, promotion_a: { status: "pending_user" } } });
    writeFileSync(path.join(f.run, "proposals", "A.json"), JSON.stringify({ round: "A", proposals: [{ id: "a-one", verdict: "propose", content: "c" }, { id: "a-two", verdict: "propose", content: "d" }, { id: "a-skip", verdict: "skip" }] }));
    expect(f.orch("recommend", "A", "a-one", "accept", "used twice").stdout).toContain("1 of 2 item(s) of round A recommended");
    expect(f.orch("recommend", "A", "a-two", "defer", "a one-line fact").stdout).toContain("started theoremchecker propose");
    expect(await f.startedArgv()).toEqual(["propose", "fa", "--round", "A", "--apply", "--recommended", "--toolkit", f.root]);
    const reviews = JSON.parse(readFileSync(path.join(f.run, "orch_decisions.json"), "utf8"));
    expect(reviews).toMatchObject([{ node: "round A" }]);
    expect(reviews[0].text).toContain("Full auto: promotion round A applied as recommended — accept: a-one; defer: a-two");
  });

  it("asks the owner only what they alone can give", () => {
    const f = fixture(weak(true));
    const r = f.orch("ask", "May thm:a assume $n>1$?");
    expect(r.status).toBe(65);
    expect(r.stderr).toContain("runs in full auto");
    expect(f.orch("ask", "--owner-only", "Please upload the cited preprint.").stdout.trim()).toBe("q1");
    expect(fixture(weak(false)).orch("ask", "May thm:a assume $n>1$?").status).toBe(0);
  });
});

describe("the page on a full-auto run", () => {
  it("leaves the owner's decisions with the attached agent", async () => {
    const f = fixture({ full_auto: true, stage_completed: "V1.5", verify: { phase: "v1_5", source: { input: "/p" }, weakening_repair: { status: "pending", items: [item("thm:a")] } } });
    // an agent attached: this test process stands for its session
    writeFileSync(path.join(f.run, "orch.json"), JSON.stringify({ agent: "Codex", pid: process.pid, attached_at: new Date().toISOString() }));
    const s = await runSummary({ toolkitRoot: f.root, runsDir: path.join(f.root, "runs") } as unknown as ToolkitConfig, "fa");
    expect(s.fullAuto).toBe(true);
    expect(s.status).toBe("agent");
    expect(s.headline).toContain("full auto: the agent decides each");
  });
  function item(node: string) { return { node, printed: "p", proposed: "q", given_up: "g", detail: "d", witness: null }; }
});
