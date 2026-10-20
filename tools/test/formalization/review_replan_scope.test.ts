// F1.5 on a re-plan reviews what moved since the plan it passed, not the whole plan again.

import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { coreJsonPath } from "../../src/core/core_io.js";
import { reviewWithCodex } from "../../src/formalization/review_codex.js";
import { artifactPaths, type StageDeps } from "../../src/pipeline_support.js";
import { pipelineLogPath, planReviewedPath, promptPath } from "../../src/paths.js";
import { createInitialState } from "../../src/state.js";
import type { PipelineContext } from "../../src/types.js";
import { tk } from "../toolkit/helpers.js";

const QID = "replan_review";
let repoRoot = "";
const ctx = (): PipelineContext => ({ repoRoot, toolkit: tk(repoRoot), qid: QID, dryRun: false, resume: false });

const node = (lean_kind: string, lean_name: string, extra = {}) => ({ lean_kind, lean_name, disposition: "define-local", reuse: null, modules: [], ...extra });

function fixture() {
  const core = {
    qid: QID,
    symbols: [{ name: "x", type: "real" }, { name: "z", type: "real" }],
    assumptions: [
      { id: "ass:shared", condition: "x positive", free_symbols: ["x"], standard: { name: "positive", cite: "fixture" } },
      { id: "ass:unrelated", condition: "UNRELATED_CORE_SENTINEL", free_symbols: ["z"], standard: { name: "bounded", cite: "fixture" } },
    ],
    definitions: [],
    statements: [
      { id: "thm:target", kind: "theorem", statement: "target x", free_symbols: ["x"], depends_on: ["ass:shared"], status: "to-prove" },
      { id: "lem:unrelated", kind: "lemma", statement: "unrelated z", free_symbols: ["z"], depends_on: ["ass:unrelated"], status: "to-prove" },
    ],
    sampling_model: { observed: "x" },
    target_estimand: "x",
    bibliography: [],
  };
  const plan = {
    qid: QID,
    env: [{ id: "S1", world: "local", binds_symbols: ["x", "z"], binds_sampling_model: true, disposition: "define-local" }],
    nodes: {
      "ass:shared": node("assumption", "Shared", { notes: "trace: positivity -> not found" }),
      "ass:unrelated": node("assumption", "Unrelated", { notes: "UNRELATED_PLAN_SENTINEL" }),
      "thm:target": node("theorem", "target", { hyps: ["ass:shared"], notes: "TARGET_TRACE_V1" }),
      "lem:unrelated": node("lemma", "unrelated", { hyps: ["ass:unrelated"] }),
    },
    citations: [] as unknown[],
  };
  return { core, plan };
}

async function write(core: unknown, plan: unknown): Promise<void> {
  const paths = artifactPaths(ctx(), createInitialState(QID));
  await mkdir(path.dirname(coreJsonPath(ctx())), { recursive: true });
  await mkdir(path.dirname(paths.plan), { recursive: true });
  await writeFile(coreJsonPath(ctx()), JSON.stringify(core));
  await writeFile(paths.plan, JSON.stringify(plan));
}

async function review(replan: boolean, reply: Record<string, unknown> = { status: "pass", notes: "sound" }): Promise<string> {
  let prompt = "";
  const deps = { runCodex: async (o: { prompt: string }) => ((prompt = o.prompt), { stdout: JSON.stringify(reply), stderr: "" }) } as unknown as StageDeps;
  await reviewWithCodex({ ctx: ctx(), state: createInitialState(QID), deps }, "stage1_5_reuse_soundness.txt", "1.5", "Review the plan.", { replan });
  return prompt;
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "f15-replan-"));
  const p = promptPath(repoRoot, "stage1_5_reuse_soundness.txt");
  await mkdir(path.dirname(p), { recursive: true });
  await writeFile(p, "review instructions");
});
afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("F1.5 review of a re-plan", () => {
  it("a first review reads the whole plan and core, and a pass records them", async () => {
    const { core, plan } = fixture();
    await write(core, plan);
    const prompt = await review(false);
    expect(prompt).toContain("UNRELATED_PLAN_SENTINEL");
    expect(prompt).toContain("UNRELATED_CORE_SENTINEL");
    expect(prompt).not.toContain("REVIEW OF A RE-PLAN");
    const basis = JSON.parse(await readFile(planReviewedPath(repoRoot, QID), "utf8"));
    expect(basis.plan.nodes["thm:target"].notes).toBe("TARGET_TRACE_V1");
    expect(basis.core.statements[0].id).toBe("thm:target");
  });

  it("a re-plan review carries the changed entries with their notes and core records, a reference line for the rest, and the lookup paths", async () => {
    const { core, plan } = fixture();
    await write(core, plan);
    await review(false);
    (plan.nodes["thm:target"] as unknown as { notes: string }).notes = "TARGET_TRACE_V2";
    await write(core, plan);
    const prompt = await review(true, { status: "pass", notes: "sound. looked_up_beyond_scope: [ass:unrelated]" });
    expect(prompt).toContain("=== REVIEW OF A RE-PLAN (scoped) ===");
    expect(prompt).toContain("Changed since the pass: thm:target");
    expect(prompt).toContain("TARGET_TRACE_V2");
    expect(prompt).toContain('"statement":"target x"');
    expect(prompt).toContain("ass:shared | assumption | assumption Shared");
    expect(prompt).toContain("lem:unrelated | lemma | lemma unrelated");
    expect(prompt).not.toContain("UNRELATED_PLAN_SENTINEL");
    expect(prompt).not.toContain("UNRELATED_CORE_SENTINEL");
    expect(prompt).toContain(`typed core (READ-ONLY): ${coreJsonPath(ctx())}`);
    expect(prompt).toContain(`plan: ${artifactPaths(ctx(), createInitialState(QID)).plan}`);
    expect(prompt).toContain("looked_up_beyond_scope: [<ids>]");
    expect(await readFile(pipelineLogPath(repoRoot, QID), "utf8")).toContain("F1.5 re-plan review looked up 1 node(s) beyond the affected set");
    // the pass moves the record forward
    expect(JSON.parse(await readFile(planReviewedPath(repoRoot, QID), "utf8")).plan.nodes["thm:target"].notes).toBe("TARGET_TRACE_V2");
  });

  it("a core change the plan did not follow is reviewed too: the moved node and the statements citing it", async () => {
    const { core, plan } = fixture();
    await write(core, plan);
    await review(false);
    core.assumptions[1]!.condition = "z bounded by one";
    await write(core, plan);
    const prompt = await review(true);
    expect(prompt).toContain("Changed since the pass: ass:unrelated");
    expect(prompt).toContain('"lem:unrelated"');
    expect(prompt).not.toContain("TARGET_TRACE_V1");
  });

  it("without a record of the passed plan, after a revise verdict, or when a plan-level field moved, the whole plan is reviewed", async () => {
    const { core, plan } = fixture();
    await write(core, plan);
    expect(await review(true)).toContain("UNRELATED_PLAN_SENTINEL"); // no record yet (this pass writes it)
    plan.citations = [{ id: "cite:x", title: "t", authors: "a", year: 2020, locator: "Thm 1" }];
    await write(core, plan);
    const reply = { status: "revise", classification: "reuse-fit", perItemFindings: [], verbatim_critique: "re-plan" };
    expect(await review(true, reply)).toContain("UNRELATED_PLAN_SENTINEL"); // citations moved
    // a revise does not move the record
    expect(JSON.parse(await readFile(planReviewedPath(repoRoot, QID), "utf8")).plan.citations).toEqual([]);
    expect(existsSync(planReviewedPath(repoRoot, QID))).toBe(true);
  });
});
