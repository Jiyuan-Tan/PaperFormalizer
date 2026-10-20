/** F2 scaffold: the post-sync plan gate, revise-file preservation, and the fail-closed stops. */
import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { runStage2 } from "../../src/formalization/stage2.js";
import { blockingPostSyncPlanViolations, restoreDeletedReviseFiles } from "../../src/formalization/stage2.js";
import { canonicalLeanSubdir, formalizationDir, leanTheoremDir, planPath, promptPath } from "../../src/paths.js";
import { createInitialState } from "../../src/state.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import { tk } from "../toolkit/helpers.js";

let repoRoot: string;
const QID = "manski1990test";

function makeCtx(root: string): PipelineContext {
  return { repoRoot: root, toolkit: tk(root), qid: QID, dryRun: false, resume: false };
}

function makeState(): StateJson {
  const state = createInitialState(QID);
  state.stage_completed = "1.5";
  return state;
}

function depsReplying(responseJson: string): StageDeps {
  return {
    runClaude: async () => responseJson,
    runCodex: async () => ({ stdout: responseJson, stderr: "" }),
  };
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(tmpdir(), "stage2-"));
  const target = promptPath(repoRoot, "stage2_scaffold.txt");
  await mkdir(path.dirname(target), { recursive: true });
  await writeFile(target, "stub prompt");
  await writeFile(promptPath(repoRoot, "stage2_head_revise.txt"), "=== REVISE MODE ===");
  const coreDir = path.join(formalizationDir(repoRoot, QID), "discovery");
  await mkdir(coreDir, { recursive: true });
  await writeFile(
    path.join(coreDir, "core.json"),
    JSON.stringify({ qid: QID, symbols: [], assumptions: [], statements: [], target_estimand: "stub target estimand" }),
  );
  const plan = planPath(repoRoot, QID);
  await mkdir(path.dirname(plan), { recursive: true });
  await writeFile(plan, JSON.stringify({ qid: QID, nodes: {} }));
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("F2 scaffold", () => {
  it("post-sync plan gate blocks structural P2/P4 drift but leaves P5/P6 lookup drift advisory", () => {
    const violations = [
      { code: "P2", where: "def:class", message: "non-member" },
      { code: "P4", where: "thm:main", message: "uncovered assumption" },
      { code: "P5", where: "thm:main", message: "reuse lookup" },
      { code: "P6", where: "thm:main", message: "module lookup" },
    ] as const;
    expect(blockingPostSyncPlanViolations(violations as never).map((v) => v.code)).toEqual(["P2", "P4"]);
  });

  it("restores a pre-existing module deleted by a revise producer", async () => {
    const file = path.join(repoRoot, "Preserved.lean");
    await writeFile(file, "theorem preserved : True := by trivial\n");
    const snapshot = new Map([[file, await readFile(file, "utf8")]]);
    await rm(file);

    expect(await restoreDeletedReviseFiles(snapshot)).toEqual([file]);
    expect(await readFile(file, "utf8")).toBe("theorem preserved : True := by trivial\n");
  });

  it("fails closed when the run is missing its typed core", async () => {
    const ctx = { ...makeCtx(repoRoot), qid: "pid_missing_core_test" };
    await expect(runStage2({ ctx, state: makeState(), deps: depsReplying("{}") })).rejects.toThrow(
      /required typed core is unreadable/,
    );
  });

  it("hard-stops F2 when nested helpers contain duplicate canonical node anchors", async () => {
    const ctx = { ...makeCtx(repoRoot), resume: true };
    const state = makeState();
    state.stage_completed = "5";
    const nested = path.join(leanTheoremDir(repoRoot, canonicalLeanSubdir(QID)), "Helpers", "Duplicate.lean");
    await mkdir(path.dirname(nested), { recursive: true });
    await writeFile(
      nested,
      "-- @node: thm:duplicate\ntheorem primary : True := by trivial\n" +
        "-- @node: thm:duplicate\nlemma companion : True := by trivial\n",
    );
    const deps = depsReplying(JSON.stringify({ status: "completed", message: "scaffold done", artifacts: [nested] }));

    await expect(runStage2({ ctx, state, deps })).rejects.toThrow(/F2 duplicate @node gate failed[\s\S]*thm:duplicate/);
  });
});

describe("F2 scaffold redirect", () => {
  it("keeps the directive pending when a post-dispatch gate refuses the scaffold, so the resume re-applies it instead of the reviewer re-flagging", async () => {
    const ctx = { ...makeCtx(repoRoot), resume: true };
    const state = makeState();
    state.stage_completed = "5";
    state.flags.scaffold_redirect = "fix thm:orphan\n\nDeclarations to edit (one obj_id per line, verbatim):\n- thm:orphan";
    const lean = path.join(leanTheoremDir(repoRoot, canonicalLeanSubdir(QID)), "Orphan.lean");
    await mkdir(path.dirname(lean), { recursive: true });
    await writeFile(lean, "-- @node: thm:orphan\ntheorem orphan : True := by trivial\n");
    const deps = depsReplying(JSON.stringify({ status: "completed", message: "scaffold done", artifacts: [lean] }));
    await expect(runStage2({ ctx, state, deps })).rejects.toThrow(/F2 structural plan gate/);
    expect(state.flags.scaffold_redirect).toContain("thm:orphan");
  });
});

describe("F2 sends a plan the gate refuses on plan-only rules back to F1", () => {
  const CLASS = { lean_kind: "structure", lean_name: "Model", members: ["ass:a"], disposition: "define-local" };
  const planWith = (cls: object) => ({ qid: QID, nodes: { "ass:a": { lean_kind: "assumption", lean_name: "assA", disposition: "define-local" }, "def:model": cls } });
  /** A scaffolder that counts its calls and, like a sync-back, leaves `after` in plan.json. */
  const scaffolder = (calls: { n: number }, after?: object): StageDeps => {
    const reply = async () => {
      calls.n += 1;
      if (after) await writeFile(planPath(repoRoot, QID), JSON.stringify(after));
      return JSON.stringify({ status: "completed", message: "compiled sorry-only" });
    };
    return { runClaude: reply, runCodex: async () => ({ stdout: await reply(), stderr: "" }) };
  };

  beforeEach(async () => {
    await writeFile(
      path.join(formalizationDir(repoRoot, QID), "discovery", "core.json"),
      JSON.stringify({
        qid: QID,
        symbols: [],
        assumptions: [{ id: "ass:a", condition: "a holds", free_symbols: [], novel: { flag: true, justification: "stub" } }],
        definitions: [{ id: "def:model", name: "Model", construction: "the laws satisfying ass:a", by_member_properties: ["ass:a"] }],
        statements: [],
        target_estimand: "stub target estimand",
      }),
    );
  });

  it("before the scaffolder is called: no call is spent, the cursor is at F1 for the F1.5 pre-lint", async () => {
    await writeFile(planPath(repoRoot, QID), JSON.stringify(planWith({ lean_kind: "def", lean_name: "ModelClass", disposition: "define-local" })));
    const state = makeState();
    const calls = { n: 0 };
    const result = await runStage2({ ctx: makeCtx(repoRoot), state, deps: scaffolder(calls) });
    expect(result).toMatchObject({ stage: "2", status: "rewound", advance: false });
    expect(result.message).toMatch(/before the scaffolder ran[\s\S]*P3 @ def:model[\s\S]*P2 @ def:model: plan omits core member 'ass:a'/);
    expect(calls.n).toBe(0);
    expect(state.stage_completed).toBe("1");
  });

  it("after a sync-back that broke them: the same route instead of a halt, the redirect still pending", async () => {
    await writeFile(planPath(repoRoot, QID), JSON.stringify(planWith(CLASS)));
    const state = makeState();
    state.flags.scaffold_redirect = "make def:model a def\n\nDeclarations to edit (one obj_id per line, verbatim):\n- def:model";
    const calls = { n: 0 };
    const deps = scaffolder(calls, planWith({ lean_kind: "def", lean_name: "ModelClass", disposition: "define-local" }));
    const result = await runStage2({ ctx: makeCtx(repoRoot), state, deps });
    expect(result).toMatchObject({ status: "rewound", advance: false });
    expect(result.message).toMatch(/the scaffolder's sync-back left[\s\S]*P3 @ def:model/);
    expect(calls.n).toBe(1);
    expect(state.stage_completed).toBe("1");
    expect(state.flags.scaffold_redirect).toContain("def:model");
  });

  it("the same refusal again after F1 restored the plan: a halt naming the pending redirect, not another round", async () => {
    const state = makeState();
    state.flags.scaffold_redirect = "make def:model a def\n\nDeclarations to edit (one obj_id per line, verbatim):\n- def:model";
    const calls = { n: 0 };
    const deps = scaffolder(calls, planWith({ lean_kind: "def", lean_name: "ModelClass", disposition: "define-local" }));
    await writeFile(planPath(repoRoot, QID), JSON.stringify(planWith(CLASS)));
    expect(await runStage2({ ctx: makeCtx(repoRoot), state, deps })).toMatchObject({ status: "rewound" });
    await writeFile(planPath(repoRoot, QID), JSON.stringify(planWith(CLASS)));
    state.stage_completed = "1.5";
    await expect(runStage2({ ctx: makeCtx(repoRoot), state, deps })).rejects.toThrow(/same refusal[\s\S]*flags\.scaffold_redirect[\s\S]*P3 @ def:model/);
    expect(calls.n).toBe(2);
  });
});
