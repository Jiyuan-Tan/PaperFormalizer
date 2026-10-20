// The orchestrator audits the first plan at F1.5; a re-plan of an approved plan continues into F2.
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { mkdtemp, mkdir, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { runStage1 } from "../../src/formalization/stage1.js";
import { haltUnactionableReview, notReviewed, runStage1_5, spendPlanReviewRound } from "../../src/formalization/stage1_5.js";
import { namedPlanEntries } from "../../src/formalization/revise_scope.js";
import { runReviewBoundary } from "../../src/shared/review_boundary.js";
import { checkpointGuidance } from "../../src/checkpoint_playbook.js";
import { formalizationDir, planCorePath, planPath, promptPath } from "../../src/paths.js";
import { createInitialState, stateSchema } from "../../src/state.js";
import type { PipelineContext } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import { tk } from "../toolkit/helpers.js";
import { PLAN_REVIEW_ROUNDS_MAX, planReviewRounds, resetFormalizationLoopCounters } from "../../src/formalization/loop_limits.js";
import type { ReviewResult } from "../../src/judgment.js";

describe("F1↔F1.5 correction budget (per formalization attempt)", () => {
  const bounce: ReviewResult = { status: "revise", classification: "reuse-fit", perItemFindings: [{ label: "lem:a", verdict: "FLAG", one_line: "x" }], verbatim_critique: "x" };
  const pass: ReviewResult = { status: "pass" };

  it("counts every bounce across entries, halts on the one past the budget, and starts over on a fresh plan", () => {
    const state = { flags: {} as Record<string, unknown> };
    expect(spendPlanReviewRound(state as never, pass)).toBe(pass);
    expect(planReviewRounds(state as never)).toBe(0);
    for (let i = 1; i <= PLAN_REVIEW_ROUNDS_MAX; i++) {
      expect((spendPlanReviewRound(state as never, bounce) as { halt_reason?: string }).halt_reason).toBeUndefined();
      expect(planReviewRounds(state as never)).toBe(i);
    }
    const halted = spendPlanReviewRound(state as never, bounce) as { halt_reason?: string };
    expect(halted.halt_reason).toContain(`all ${PLAN_REVIEW_ROUNDS_MAX} rounds`);
    expect(halted.halt_reason).toContain("lem:a");
    // The counter is a plain flag, so it is what state.json persists across a resume.
    expect(state.flags.plan_review_rounds).toBe(PLAN_REVIEW_ROUNDS_MAX + 1);
    resetFormalizationLoopCounters(state as never);
    expect(planReviewRounds(state as never)).toBe(0);
  });
});

describe("F1.5 without the intervention judge (2026-10-07)", () => {
  let repoRoot: string;
  const QID = "pid_f15";
  const ctx = (): PipelineContext => ({ repoRoot, toolkit: tk(repoRoot), qid: QID, dryRun: false, resume: false });
  const core = {
    qid: QID,
    symbols: [{ name: "Y", type: "outcome", space: "\\mathbb R", def: "the outcome", refs: [] }],
    assumptions: [{ id: "ass:a", kind: "assumption", condition: "$Y$ is bounded", free_symbols: ["Y"], novel: { flag: true, justification: "stated" }, used_by: ["thm:t"] }],
    definitions: [],
    statements: [{ id: "thm:t", kind: "theorem", statement: "$E[Y]$ exists", free_symbols: ["Y"], depends_on: ["ass:a"], proof_tex: "p", status: "to-prove" }],
    sampling_model: { iid: "units are iid" },
    target_estimand: "E[Y]",
    bibliography: [],
  };
  const GATE_CLEAN_PLAN = {
    qid: QID,
    lean_subdir: "Stat/Demo",
    env: [{ id: "S1", world: "local", binds_symbols: ["Y"], binds_sampling_model: true, disposition: "define-local", notes: "searched: none fits" }],
    nodes: {
      "ass:a": { lean_kind: "assumption", lean_name: "assA", disposition: "define-local", notes: "searched: none fits" },
      "thm:t": { lean_kind: "theorem", lean_name: "thmT", disposition: "define-local", hyps: ["ass:a"], notes: "searched: none fits" },
    },
  };
  const revise = (label: string, one_line = "wrong decl"): ReviewResult =>
    ({ status: "revise", classification: "reuse-fit", perItemFindings: [{ label, verdict: "FLAG-fit", one_line }], verbatim_critique: "re-plan it" });

  beforeEach(async () => {
    repoRoot = await mkdtemp(path.join(tmpdir(), "f15-"));
    for (const [name, body] of [["stage1_template.txt", "stub stage1_template"], ["stage1_head_revise.txt", "REVISION HEAD"]]) {
      const p = promptPath(repoRoot, name);
      await mkdir(path.dirname(p), { recursive: true });
      await writeFile(p, body, "utf8");
    }
    const corePath = path.join(formalizationDir(repoRoot, QID), "discovery", "core.json");
    await mkdir(path.dirname(corePath), { recursive: true });
    await writeFile(corePath, JSON.stringify(core), "utf8");
  });
  afterEach(async () => {
    await rm(repoRoot, { recursive: true, force: true });
  });

  it("a bounce re-runs F1 with the reviewer's findings as the correction and the flagged entries as seeds — F1 is the only model call — until the budget halts", async () => {
    const prompts: string[] = [];
    const deps = {
      // F1 writes a plan the gate bounces every time (no entry for either core node).
      runClaude: async (o: unknown) => {
        prompts.push((o as { prompt: string }).prompt);
        const p = planPath(repoRoot, QID);
        await mkdir(path.dirname(p), { recursive: true });
        await writeFile(p, JSON.stringify({ qid: QID, nodes: {} }), "utf8");
        return JSON.stringify({ status: "completed", artifacts: [] });
      },
      runCodex: async () => { throw new Error("no reviewer call: the gate bounces the plan first"); },
    } as unknown as StageDeps;
    const state = createInitialState(QID);
    state.stage_completed = "1";
    await mkdir(path.dirname(planPath(repoRoot, QID)), { recursive: true });
    await writeFile(planPath(repoRoot, QID), JSON.stringify({ qid: QID, nodes: {} }), "utf8");
    // the plan on disk was written against this core: the revise is scoped to what the findings name
    await writeFile(planCorePath(repoRoot, QID), JSON.stringify(core), "utf8");

    const result = await runStage1_5({ ctx: ctx(), state, deps });
    expect(prompts).toHaveLength(PLAN_REVIEW_ROUNDS_MAX);
    for (const prompt of prompts) {
      expect(prompt).toContain("=== CORRECTION");
      expect(prompt).toContain("- thm:t | FLAG-P1 | core node has no plan entry");
      expect(prompt).toContain("the 2 of 2 nodes this revise affects, in full");
      expect(prompt).not.toContain("INTERVENTION");
    }
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    expect(result.message).toContain("correction budget spent");
    expect(result.message).toContain("thm:t [FLAG-P1] core node has no plan entry");
    expect(result.message).toContain("The orchestrator rules");
    expect(state.flags.general_review_halt).toBe(result.message);

    // A resume after the budget is spent: the first bounce halts again, F1 is not run.
    state.flags.general_review_halt = null;
    const again = await runStage1_5({ ctx: ctx(), state, deps });
    expect(prompts).toHaveLength(PLAN_REVIEW_ROUNDS_MAX);
    expect(again.message).toContain(`all ${PLAN_REVIEW_ROUNDS_MAX} rounds`);

    // The orchestrator rules with a directive and re-enters F1: the budget starts over, so the
    // next bounce goes back to F1 instead of halting.
    state.flags.general_review_halt = null;
    state.flags.f1_revise_directive = "give thm:t an entry";
    await runStage1({ ctx: ctx(), state, deps });
    expect(planReviewRounds(state)).toBe(0);
    const fresh = await runStage1_5({ ctx: ctx(), state, deps });
    expect(prompts).toHaveLength(2 * PLAN_REVIEW_ROUNDS_MAX + 1);
    expect(fresh.message).toContain("correction budget spent");
  });

  it("a reject from the reviewer halts end to end: no F1 run, the findings and the orchestrator's duty in the message", async () => {
    let f1 = 0;
    const deps = {
      runClaude: async () => { f1 += 1; return JSON.stringify({ status: "completed", artifacts: [] }); },
      runCodex: async () => ({ stdout: JSON.stringify({ status: "reject", classification: "core-math", perItemFindings: [{ label: "thm:t", verdict: "FLAG-core", one_line: "false as stated" }], verbatim_critique: "the core is wrong" }), stderr: "" }),
    } as unknown as StageDeps;
    const reviewPrompt = promptPath(repoRoot, "stage1_5_reuse_soundness.txt");
    await mkdir(path.dirname(reviewPrompt), { recursive: true });
    await writeFile(reviewPrompt, "stub review", "utf8");
    const state = createInitialState(QID);
    state.stage_completed = "1";
    await mkdir(path.dirname(planPath(repoRoot, QID)), { recursive: true });
    await writeFile(planPath(repoRoot, QID), JSON.stringify(GATE_CLEAN_PLAN), "utf8");
    const result = await runStage1_5({ ctx: ctx(), state, deps });
    expect(f1).toBe(0);
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    expect(result.message).toContain("thm:t [FLAG-core] false as stated");
    expect(result.message).toContain("recorded by the orchestrator");
    expect(planReviewRounds(state)).toBe(0);
    expect(state.flags.general_review_halt).toBe(result.message);
  });

  it("a first plan still halts at CKPT 1 when the run's log holds V lines — a report written after a failed V1.5 is no approved plan", async () => {
    const deps = {
      runClaude: async () => { throw new Error("no F1 run: the plan passes"); },
      runCodex: async () => ({ stdout: JSON.stringify({ status: "pass" }), stderr: "" }),
    } as unknown as StageDeps;
    const reviewPrompt = promptPath(repoRoot, "stage1_5_reuse_soundness.txt");
    await mkdir(path.dirname(reviewPrompt), { recursive: true });
    await writeFile(reviewPrompt, "stub review", "utf8");
    const { pipelineLogPath } = await import("../../src/paths.js");
    await mkdir(path.dirname(pipelineLogPath(repoRoot, QID)), { recursive: true });
    await writeFile(pipelineLogPath(repoRoot, QID), ["V1", "V1.5", "V6"].map((stage) => JSON.stringify({ stage, status: stage === "V1.5" ? "refuted" : "completed" })).join("\n") + "\n", "utf8");
    const state = createInitialState(QID);
    state.stage_completed = "1";
    await mkdir(path.dirname(planPath(repoRoot, QID)), { recursive: true });
    await writeFile(planPath(repoRoot, QID), JSON.stringify(GATE_CLEAN_PLAN), "utf8");
    const result = await runStage1_5({ ctx: ctx(), state, deps });
    expect(result.status).toBe("checkpoint");
    expect(result.message).toContain("CONSOLIDATED CKPT 1");
  });

  it("a review F1 cannot act on halts as it is: a reject (rooted in the core), or one naming no plan entry", () => {
    const named = (texts: string[]): string[] => texts.filter((t) => t.includes("thm:t") || /\bS1\b/.test(t));
    const ok = revise("thm:t");
    expect(haltUnactionableReview(ok, named)).toBe(ok);
    const world = revise("S1");
    expect(haltUnactionableReview(world, named)).toBe(world);
    const gate = { ...revise("plan.json"), classification: "plan-gate" } as ReviewResult;
    expect(haltUnactionableReview(gate, named)).toBe(gate);
    const unread = haltUnactionableReview({ status: "reject", classification: "parse_failure", perItemFindings: [], verbatim_critique: "garbage" }, named) as { halt_reason?: string };
    expect(unread.halt_reason).toContain("could not be read");
    const unanchored = haltUnactionableReview(revise("the plan", "too shallow"), named) as { halt_reason?: string };
    expect(unanchored.halt_reason).toContain("names no plan entry");
    expect(unanchored.halt_reason).toContain("the plan [FLAG-fit] too shallow");
    const rooted = haltUnactionableReview({ status: "reject", classification: "core-math", perItemFindings: [{ label: "thm:t", verdict: "FLAG-core", one_line: "false as stated" }], verbatim_critique: "the core is wrong" }, named) as { halt_reason?: string };
    expect(rooted.halt_reason).toContain("reject/core-math");
    expect(rooted.halt_reason).toContain("thm:t [FLAG-core] false as stated");
  });

  it("a plan entry is a core node, an S-block or a citation of the plan", () => {
    const plan = { env: [{ id: "S1" }], citations: [{ id: "cite:bk2022" }] } as never;
    expect(namedPlanEntries(core as never, plan, ["S1 and S9", "cite:bk2022 is mis-stated; cite:other", "thm:t, thm:gone"])).toEqual(["thm:t", "S1", "cite:bk2022"]);
  });

  it("the boundary halts on a marked verdict without running the producer, and hands an unmarked bounce to it", async () => {
    const state = createInitialState(QID);
    let produced = 0;
    const run = (reviews: ReviewResult[]) => runReviewBoundary({
      ctx: ctx(), state, boundary: "stage_1.5_to_1", stage: "1.5", cap: 3,
      producer: async (prior) => {
        produced += 1;
        expect(prior).toBe(reviews[0]);
        return { stage: "1", status: "completed", message: "re-planned" };
      },
      reviewer: async (attempt) => reviews[attempt - 1]!,
    });
    const halted = await run([{ ...revise("x"), halt_reason: "cannot act" } as unknown as ReviewResult]);
    expect(halted).toMatchObject({ status: "checkpoint", advance: false });
    expect(halted.message).toContain("cannot act");
    expect(state.flags.general_review_halt).toContain("cannot act");
    expect(produced).toBe(0);
    expect(await run([revise("thm:t"), { status: "pass" }])).toMatchObject({ status: "completed" });
    expect(produced).toBe(1);
  });

  it("F1 blocked inside the loop: the halt carries the blocked-F1 reminder, and the resume plans again — with the review it was correcting — before any review", async () => {
    const calls: string[] = [];
    let reply = "blocked";
    const deps = {
      runClaude: async (o: unknown) => {
        calls.push(`F1${(o as { prompt: string }).prompt.includes("- thm:t | FLAG-P1") ? " with the review" : ""}`);
        if (reply === "blocked") return JSON.stringify({ status: "blocked", message: "the core's scope is undefined" });
        await writeFile(planPath(repoRoot, QID), JSON.stringify(GATE_CLEAN_PLAN), "utf8");
        return JSON.stringify({ status: "completed", artifacts: [] });
      },
      runCodex: async () => { calls.push("reviewer"); return JSON.stringify({ status: "pass", notes: "ok" }); },
    } as unknown as StageDeps;
    const state = createInitialState(QID);
    state.stage_completed = "1";
    await mkdir(path.dirname(planPath(repoRoot, QID)), { recursive: true });
    await writeFile(planPath(repoRoot, QID), JSON.stringify({ qid: QID, nodes: {} }), "utf8");
    await writeFile(planCorePath(repoRoot, QID), JSON.stringify(core), "utf8");

    const halted = await runStage1_5({ ctx: ctx(), state, deps });
    expect(halted).toMatchObject({ stage: "1", status: "checkpoint", advance: false });
    expect(state.flags.f1_blocked).toMatchObject({ message: expect.stringContaining("F1 blocked: the core's scope is undefined"), review: { status: "revise" } });
    for (const stage of ["1", "1.5"] as const) {
      const g = checkpointGuidance(stage, "checkpoint", state.flags, false, halted.message)!;
      expect(g).toContain("F1 BLOCKED");
      expect(g).toContain("A resume plans again before any review");
      expect(g).not.toContain("CONSOLIDATED CKPT 1");
    }
    // the resume: F1 first; blocked again, nothing is reviewed
    expect(calls).toEqual(["F1 with the review"]);
    expect((await runStage1_5({ ctx: ctx(), state, deps })).advance).toBe(false);
    expect(calls).toEqual(["F1 with the review", "F1 with the review"]);
    // … and once it plans, the review runs on the new plan and the record is cleared
    reply = "completed";
    const stub = path.join(repoRoot, "tools", "src", "formalization", "prompts", "F1.5", "stage1_5_reuse_soundness.txt");
    await mkdir(path.dirname(stub), { recursive: true });
    await writeFile(stub, "stub reviewer", "utf8");
    // … under the orchestrator's directive, with a fresh correction budget
    (state.flags as { plan_review_rounds?: number }).plan_review_rounds = PLAN_REVIEW_ROUNDS_MAX;
    state.flags.f1_revise_directive = "plan thm:t over the reals";
    await runStage1_5({ ctx: ctx(), state, deps }).catch(() => undefined); // (the stub reviewer's reply is not the point)
    expect(planReviewRounds(state)).toBeLessThan(PLAN_REVIEW_ROUNDS_MAX);
    expect(calls.slice(2, 4)).toEqual(["F1 with the review", "reviewer"]);
    expect(state.flags.f1_blocked ?? null).toBeNull();
  });

  it("no result of F1 through the F1.5 slot records F1.5 complete: a resume after a blocked F1 whose re-plan writes no usable plan does not advance", async () => {
    const state = createInitialState(QID);
    state.stage_completed = "1";
    state.flags.f1_blocked = { message: "F1 blocked: x" };
    await mkdir(path.dirname(planPath(repoRoot, QID)), { recursive: true });
    const deps = {
      // the re-plan answers `completed` and leaves a plan that is no plan
      runClaude: async () => { await writeFile(planPath(repoRoot, QID), JSON.stringify({ nodes: "not a plan" }), "utf8"); return JSON.stringify({ status: "completed", artifacts: [] }); },
      runCodex: async () => { throw new Error("no review of a plan that is none"); },
    } as unknown as StageDeps;
    const out = await runStage1_5({ ctx: ctx(), state, deps });
    expect(out).toMatchObject({ stage: "1", status: "checkpoint", advance: false });
    expect(notReviewed({ stage: "1", status: "checkpoint", message: "m" })).toMatchObject({ advance: false });
    expect(notReviewed({ stage: "1", status: "completed", message: "m" })).toMatchObject({ advance: false });
    expect(notReviewed({ stage: "1.5", status: "checkpoint", advance: true, message: "audit" })).toMatchObject({ advance: true });
  });

  it("a producer that halts without producing ends the loop with its own message; the earlier artifact is not reviewed again", async () => {
    const state = createInitialState(QID);
    let reviewed = 0;
    const out = await runReviewBoundary({
      ctx: ctx(), state, boundary: "stage_1.5_to_1", stage: "1.5", cap: 3,
      producer: async () => ({ stage: "1", status: "checkpoint", advance: false, message: "F1 blocked: the core's scope is undefined" }),
      reviewer: async () => { reviewed += 1; return revise("thm:t"); },
    });
    expect(out).toMatchObject({ stage: "1", status: "checkpoint", advance: false, message: "F1 blocked: the core's scope is undefined" });
    expect(reviewed).toBe(1);
  });

  it("a state file written with the judge's fields still loads", () => {
    const old = createInitialState(QID) as unknown as { flags: Record<string, unknown> };
    Object.assign(old.flags, { stage1_rewinds: 2, stage1_rewinds_cap_hit: "cap", scaffold_redirect_count: 1, scaffold_redirect_cap_hit: "cap", verify_no_d_rewind: "stage_0 rewind refused" });
    const loaded = stateSchema.parse(JSON.parse(JSON.stringify(old))) as unknown as { flags: Record<string, unknown> };
    expect(loaded.flags).toMatchObject({ stage1_rewinds: 2, scaffold_redirect_count: 1, verify_no_d_rewind: "stage_0 rewind refused" });
  });
});
