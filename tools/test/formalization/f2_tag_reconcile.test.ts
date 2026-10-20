import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { coreJsonPath } from "../../src/core/core_io.js";
import { CoreSchema, type Core } from "../../src/core/schema.js";
import {
  reconcileScaffoldTagsInMemory,
  tagReconciliationBlock,
} from "../../src/formalization/f2_tag_reconcile.js";
import { runPlanGate } from "../../src/formalization/plan/plan_gate.js";
import { PlanSchema, type Plan } from "../../src/formalization/plan/schema.js";
import { parseLeanNodeTags, runStage2 } from "../../src/formalization/stage2.js";
import { artifactPaths, type StageDeps } from "../../src/pipeline_support.js";
import { promptPath } from "../../src/paths.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import { tk } from "../toolkit/helpers.js";

const PIN1 = "The endpoint quantiles at zero and one are taken as one-sided limits.";
const BK1 = "Evaluate the conditional mean only when the event has positive probability.";

function pin(id: string, condition: string) {
  return { id, kind: "regularity", condition, bookkeeping: { flag: true, added_by: "V1.5", reason: "pins a reading" } };
}

function makeCore(): Core {
  return CoreSchema.parse({
    qid: "stat_tag_reconcile",
    symbols: [{ name: "x", type: "real" }],
    assumptions: [
      { id: "ass:pos", condition: "x positive", free_symbols: ["x"], standard: { name: "positive", cite: "fixture" } },
      pin("ass:pin-1", PIN1),
      pin("ass:bk-1", BK1),
    ],
    definitions: [],
    statements: [
      { id: "thm:main", kind: "theorem", statement: "main x", free_symbols: ["x"], depends_on: ["ass:pos", "ass:pin-1", "ass:bk-1"], status: "to-prove" },
    ],
    target_estimand: "x",
    bibliography: [],
  }) as Core;
}

function makePlan(names: { pin1?: string } = {}): Plan {
  const node = (lean_kind: string, lean_name: string, extra = {}) => ({
    lean_kind, lean_name, disposition: "define-local", reuse: null, modules: [], target_file: "Main.lean", ...extra,
  });
  return PlanSchema.parse({
    qid: "stat_tag_reconcile",
    env: [{ id: "S1", world: "local", binds_symbols: ["x"], binds_sampling_model: true, disposition: "define-local" }],
    nodes: {
      "ass:pos": node("assumption", "Pos"),
      "ass:pin-1": node("assumption", names.pin1 ?? "EndpointConvention"),
      "ass:bk-1": node("assumption", "CondMeanConvention"),
      "thm:main": node("theorem", "main", { hyps: ["ass:pos", "ass:pin-1", "ass:bk-1"] }),
    },
    citations: [],
  });
}

const HEAD = [
  "module",
  "",
  "public import Mathlib.Data.Real.Basic",
  "",
  "/-! Fixture. -/",
  "",
  "@[expose] public section",
  "",
  "namespace Fixture",
  "",
  "-- @env: S1",
  "structure World where",
  "  x : ℝ",
  "",
  "-- @node: ass:pos",
  "def Pos (W : World) : Prop := 0 < W.x",
  "",
];

const MAIN_PROOF = [
  "-- @node: thm:main",
  "theorem main (W : World) (h : Pos W) : 0 ≤ W.x := by",
  "  exact le_of_lt h",
  "",
  "end Fixture",
  "",
];

/** Stale `ass:pin-4` (docstring = a paraphrase that is not the current reading) with a
 *  carry-over comment; nothing references it. */
const STALE_UNREFERENCED = [
  "/-- Both processes use the limiting control CDF as bridge time. -/",
  "-- @node: ass:pin-4",
  "theorem OldPin (W : World) : W.x = W.x := by",
  "  sorry",
  "/-! PRIOR PROOF (carry-over: auto; signature-unchanged `OldPin`). Stage 3: replace the",
  "   `:= by sorry` above with this body, run `lean_diagnostic_messages`, patch failures only.",
  "   := by rfl",
  "-/",
  "",
];

function src(...blocks: string[][]) {
  return [{ file: "/x/Main.lean", text: [...HEAD, ...blocks.flat()].join("\n") }];
}

describe("F2 revise tag reconciliation", () => {
  it("removes an unreferenced stale pin declaration with its carry-over and lists untagged nodes as new", () => {
    const { result, changed } = reconcileScaffoldTagsInMemory({
      sources: src(STALE_UNREFERENCED, MAIN_PROOF), plan: makePlan(), core: makeCore(),
    });
    expect(result.removed).toEqual([{ id: "ass:pin-4", decl: "OldPin", file: "/x/Main.lean" }]);
    expect(result.retagged).toEqual([]);
    expect(result.newNodes.map((n) => n.id)).toEqual(["ass:bk-1", "ass:pin-1"]);
    const text = changed[0].text;
    expect(text).not.toContain("OldPin");
    expect(text).not.toContain("PRIOR PROOF");
    expect(text).not.toContain("bridge time");
    // unrelated declarations keep their tags and proofs byte-for-byte
    expect(text).toContain(MAIN_PROOF.slice(0, 3).join("\n"));
    expect(text).toContain("-- @node: ass:pos\ndef Pos (W : World) : Prop := 0 < W.x");
    expect(text).toContain("-- @env: S1\nstructure World where");
    const block = tagReconciliationBlock(result);
    expect(block).toContain("NEW NODES TO SCAFFOLD");
    expect(block).toContain("ass:bk-1: assumption CondMeanConvention in Main.lean");
    expect(block).toContain("Removed");
  });

  it("removes an indented stale declaration whole: its tag, header and body (never the tag alone)", () => {
    // Inside a namespace the scaffolder may indent; a stale pin there used to lose only its tag
    // (the header walk skipped indented lines), leaving an orphan declaration for P7.
    const indented = [
      "  /-- Both processes use the limiting control CDF as bridge time. -/",
      "  -- @node: ass:pin-4",
      "  theorem OldPin (W : World) : W.x = W.x := by",
      "    sorry",
      "",
      "  -- @node: thm:main",
      "  theorem main (W : World) (h : Pos W) : 0 ≤ W.x := by",
      "    exact le_of_lt h",
      "",
      "end Fixture",
      "",
    ];
    const { result, changed } = reconcileScaffoldTagsInMemory({ sources: src(indented), plan: makePlan(), core: makeCore() });
    expect(result.removed).toEqual([{ id: "ass:pin-4", decl: "OldPin", file: "/x/Main.lean" }]);
    const text = changed[0].text;
    expect(text).not.toContain("OldPin");
    expect(text).not.toContain("ass:pin-4");
    expect(text).toContain(indented.slice(5, 8).join("\n"));
  });

  it("never touches a plan-less non-positional tag (P7-exempt agent helpers)", () => {
    const helper = ["-- @node: lem:agent-helper", "theorem helperFact (W : World) : W.x = W.x := by", "  rfl", ""];
    const { result, changed } = reconcileScaffoldTagsInMemory({ sources: src(helper, MAIN_PROOF), plan: makePlan(), core: makeCore() });
    expect(result.removed).toEqual([]);
    expect(result.staleReferenced).toEqual([]);
    expect(changed).toEqual([]);
  });

  it("a repair's hashed ids go stale like positional ones: a corollary the repair no longer splits off and a reading it no longer states lose their declarations; one still referenced is kept and reported", () => {
    const cor = ["-- @node: thm:cor-fix-0a1b2c3d", "theorem gaussianCase (W : World) : W.x = W.x := by", "  rfl", ""];
    const reading = ["-- @node: ass:pin-fix-9f8e7d6c", "def OldReading (W : World) : Prop := W.x = W.x", ""];
    const { result, changed } = reconcileScaffoldTagsInMemory({ sources: src(cor, reading, MAIN_PROOF), plan: makePlan(), core: makeCore() });
    expect(result.removed.map((r) => [r.id, r.decl])).toEqual([["thm:cor-fix-0a1b2c3d", "gaussianCase"], ["ass:pin-fix-9f8e7d6c", "OldReading"]]);
    expect(changed[0].text).not.toContain("gaussianCase");
    expect(changed[0].text).not.toContain("OldReading");
    expect(changed[0].text).toContain(MAIN_PROOF.slice(0, 3).join("\n"));
    // still in the core → not stale
    const live = CoreSchema.parse({ ...makeCore(), statements: [...makeCore().statements, { id: "thm:cor-fix-0a1b2c3d", kind: "theorem", statement: "a case", depends_on: ["thm:main"], status: "proved", proof_tex: "by the theorem", split_from: "thm:main" }] }) as Core;
    expect(reconcileScaffoldTagsInMemory({ sources: src(cor, MAIN_PROOF), plan: makePlan(), core: live }).result.removed).toEqual([]);
    const user = ["-- @node: thm:main", "theorem main (W : World) (h : Pos W) : 0 ≤ W.x := by", "  have := gaussianCase W", "  exact le_of_lt h", "", "end Fixture", ""];
    const kept = reconcileScaffoldTagsInMemory({ sources: src(cor, user), plan: makePlan(), core: makeCore() }).result;
    expect(kept.removed).toEqual([]);
    expect(kept.staleReferenced).toEqual([{ id: "thm:cor-fix-0a1b2c3d", decl: "gaussianCase", file: "/x/Main.lean", referencedBy: ["thm:main"] }]);
  });

  it("retags (keeping the proof) when the previous core has the same reading text", () => {
    const { result, changed } = reconcileScaffoldTagsInMemory({
      sources: src(STALE_UNREFERENCED, MAIN_PROOF), plan: makePlan(), core: makeCore(),
      prevCore: { assumptions: [pin("ass:pin-4", `  ${PIN1.toUpperCase()} `)] as Core["assumptions"] },
    });
    expect(result.retagged).toEqual([
      { from: "ass:pin-4", to: "ass:pin-1", decl: "OldPin", file: "/x/Main.lean", basis: "prev-core-text" },
    ]);
    expect(result.removed).toEqual([]);
    expect(result.newNodes.map((n) => n.id)).toEqual(["ass:bk-1"]);
    expect(changed[0].text).toContain("-- @node: ass:pin-1\ntheorem OldPin (W : World) : W.x = W.x := by");
    expect(changed[0].text).toContain("   := by rfl");
  });

  it("keeps a stale declaration another declaration uses and names the user", () => {
    const stale = ["-- @node: ass:pin-4", "def OldPin (W : World) : Prop := W.x = W.x", ""];
    const user = [
      "-- @node: thm:main",
      "theorem main (W : World) (h : Pos W) (h2 : Fixture.OldPin W) : 0 ≤ W.x := by",
      "  exact le_of_lt h",
      "",
    ];
    const { result, changed } = reconcileScaffoldTagsInMemory({ sources: src(stale, user), plan: makePlan(), core: makeCore() });
    expect(result.staleReferenced).toEqual([
      { id: "ass:pin-4", decl: "OldPin", file: "/x/Main.lean", referencedBy: ["thm:main"] },
    ]);
    expect(changed).toEqual([]);
    expect(tagReconciliationBlock(result)).toContain("ass:pin-4: OldPin in Main.lean, used by thm:main");
    const gate = runPlanGate(makePlan(), makeCore(), {
      leanTags: { nodes: new Set(["ass:pos", "thm:main", "ass:pin-4"]), envs: new Set(["S1"]) },
      tagReconciliation: result,
    });
    expect(gate.violations.find((v) => v.where === "ass:pin-4")?.message).toContain("stale tag, referenced by thm:main");
    expect(gate.violations.find((v) => v.where === "ass:bk-1")?.message).toContain("listed it to the scaffolder as a new node");
  });
});

// End to end through runStage2: reconciliation runs before dispatch, the directive reaches the
// scaffolder, and once it adds the new nodes the post-F2 gate passes.
describe("F2 revise entry reconciles before the gate", () => {
  let repoRoot = "";
  beforeEach(async () => {
    repoRoot = await mkdtemp(path.join(os.tmpdir(), "f2-tag-reconcile-"));
    await mkdir(path.dirname(promptPath(repoRoot, "stage2_scaffold.txt")), { recursive: true });
    await writeFile(promptPath(repoRoot, "stage2_scaffold.txt"), "scaffold instructions");
    await writeFile(promptPath(repoRoot, "stage2_head_revise.txt"), "revise instructions");
  });
  afterEach(async () => {
    await rm(repoRoot, { recursive: true, force: true });
  });

  it("removes the stale pin, lists the new nodes, and the gate passes after the scaffolder adds them", async () => {
    const ctx: PipelineContext = { repoRoot, toolkit: tk(repoRoot), qid: "stat_tag_reconcile", dryRun: false, resume: true };
    const state = {
      stage_completed: "2", lean_subdir: "Papers/TagReconcile", design_decisions: {},
      added_assumptions: [], loop: "research", next_action: null, lineage: null, from_question_oq_id: null,
      method_id: null, closed_oq: null,
      flags: { rewound_from_stage4d: null, missing_architecture: false, scaffold_redirect: "Re-render after the V1.5 rewind." },
    } as unknown as StateJson;
    const paths = artifactPaths(ctx, state);
    await mkdir(path.dirname(coreJsonPath(ctx)), { recursive: true });
    await mkdir(path.dirname(paths.plan), { recursive: true });
    await mkdir(paths.leanDir, { recursive: true });
    await writeFile(coreJsonPath(ctx), JSON.stringify(makeCore()));
    await writeFile(paths.plan, JSON.stringify(makePlan()));
    const main = path.join(paths.leanDir, "Main.lean");
    await writeFile(main, [...HEAD, ...STALE_UNREFERENCED, ...MAIN_PROOF].join("\n"));

    let prompt = "";
    let onDiskAtDispatch = "";
    const deps = {
      runCodex: async (opts: { prompt: string }) => {
        prompt = opts.prompt;
        onDiskAtDispatch = await readFile(main, "utf8");
        const added = [
          "-- @node: ass:pin-1",
          "def EndpointConvention (W : World) : Prop := True",
          "",
          "-- @node: ass:bk-1",
          "def CondMeanConvention (W : World) : Prop := True",
          "",
        ];
        await writeFile(main, onDiskAtDispatch.replace("-- @node: thm:main", `${added.join("\n")}\n-- @node: thm:main`));
        return { stdout: JSON.stringify({ status: "completed", message: "ok", artifacts: [main] }), stderr: "" };
      },
      runClaude: async () => "",
    } as unknown as StageDeps;

    const res = await runStage2({ ctx, state, deps });
    expect(res.status).toBe("completed");
    expect(onDiskAtDispatch).not.toContain("ass:pin-4");
    expect(onDiskAtDispatch).toContain("  exact le_of_lt h");
    expect(prompt).toContain("=== F2 TAG RECONCILIATION");
    expect(prompt).toMatch(/NEW NODES TO SCAFFOLD[\s\S]*ass:bk-1: assumption CondMeanConvention/);
    expect(prompt).toContain("ass:pin-4: OldPin in Main.lean");
    const final = await readFile(main, "utf8");
    expect(final).toContain("theorem main (W : World) (h : Pos W) : 0 ≤ W.x := by\n  exact le_of_lt h");
    const gate = runPlanGate(makePlan(), makeCore(), { leanTags: await parseLeanNodeTags(paths.leanDir) });
    expect(gate.violations).toEqual([]);
  });
});
