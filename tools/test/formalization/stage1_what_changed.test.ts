// An F1 re-plan is told what moved in the core since the plan on disk was written: F1 records the
// core with every completed plan, and the next revise pass diffs against it.

import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { existsSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { planHygieneBlock, runStage1, stage1ReviseSeeds } from "../../src/formalization/stage1.js";
import { PLAN_NOTES_MAX } from "../../src/formalization/plan/schema.js";
import { coreDeltaLines, whatChangedBlock } from "../../src/formalization/core_delta.js";
import { formalizationDir, pipelineLogPath, planCorePath, planPath, promptPath } from "../../src/paths.js";
import { createInitialState } from "../../src/state.js";
import type { Core } from "../../src/core/schema.js";
import type { PipelineContext } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import { tk } from "../toolkit/helpers.js";

const QID = "pid_whatchanged";

function core(over: { statement?: string; assumptions?: Core["assumptions"]; setting?: string } = {}): Core {
  return {
    qid: QID,
    symbols: [{ name: "Y", type: "outcome", space: "\\mathbb R", def: "the outcome", refs: [] }],
    assumptions: over.assumptions ?? [
      { id: "ass:a", kind: "assumption", condition: "$Y$ is bounded", free_symbols: ["Y"], novel: { flag: true, justification: "stated" }, used_by: ["thm:t"] },
    ],
    definitions: [],
    statements: [
      { id: "thm:t", kind: "theorem", statement: over.statement ?? "$E[Y]$ exists", free_symbols: ["Y"], depends_on: ["ass:a"], proof_tex: "long proof", status: "to-prove" },
    ],
    sampling_model: { iid: over.setting ?? "units are iid" },
    target_estimand: "E[Y]",
    bibliography: [],
  } as unknown as Core;
}

describe("coreDeltaLines / whatChangedBlock", () => {
  it("lists every added, removed and changed node, symbol and setting, old → new, and nothing unchanged", () => {
    const next = core({
      statement: "$E[Y]$ exists and is finite",
      assumptions: [{ id: "ass:b", kind: "assumption", condition: "$Y\\ge 0$", free_symbols: ["Y"], tex_locator: "L9", used_by: ["thm:t"] } as never],
      setting: "units are exchangeable",
    });
    (next.statements[0] as unknown as Record<string, unknown>).proof_tex = "repaired proof";
    const lines = coreDeltaLines(core(), next).join("\n");
    expect(lines).toContain("- added assumption ass:b\n"); // named only: its record is among the affected nodes
    expect(lines).not.toContain("L9"); // locator fields are quiet
    expect(lines).toContain("- removed assumption ass:a");
    expect(lines).toContain('- changed statement thm:t:\n    statement: "$E[Y]$ exists" → "$E[Y]$ exists and is finite"');
    expect(lines).toContain("    proof_tex: changed");
    expect(lines).not.toContain("repaired proof");
    expect(lines).toContain('- changed sampling_model:\n    iid: "units are iid" → "units are exchangeable"');
    expect(lines).not.toContain("symbol Y");
  });

  it("is empty when nothing moved, and asks for a comparison when no prior core was recorded", () => {
    expect(whatChangedBlock(core(), core())).toBe("");
    expect(whatChangedBlock(null, core())).toContain("No record of the core");
  });
});

let repoRoot: string;
const ctx = (): PipelineContext => ({ repoRoot, toolkit: tk(repoRoot), qid: QID, dryRun: false, resume: false });
const corePath = (): string => path.join(formalizationDir(repoRoot, QID), "discovery", "core.json");

function deps(): { deps: StageDeps; prompt: () => string } {
  let prompt = "";
  return {
    deps: {
      runClaude: async (o: unknown) => {
        prompt = (o as { prompt: string }).prompt;
        const p = planPath(repoRoot, QID);
        await mkdir(path.dirname(p), { recursive: true });
        await writeFile(p, JSON.stringify({ qid: QID, nodes: {} }), "utf8");
        return JSON.stringify({ status: "completed", artifacts: [] });
      },
      runCodex: async () => { throw new Error("runCodex should not be called by Stage 1"); },
    },
    prompt: () => prompt,
  };
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(tmpdir(), "f1-what-changed-"));
  for (const [name, body] of [["stage1_template.txt", "stub stage1_template"], ["stage1_head_revise.txt", "REVISION HEAD"]]) {
    const p = promptPath(repoRoot, name);
    await mkdir(path.dirname(p), { recursive: true });
    await writeFile(p, body, "utf8");
  }
  await mkdir(path.dirname(corePath()), { recursive: true });
  await writeFile(corePath(), JSON.stringify(core()), "utf8");
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("F1 re-plan after the core moved", () => {
  it("records the core with the plan, then shows the next revise pass exactly what changed", async () => {
    const state = createInitialState(QID);
    state.stage_completed = "V1.5";
    await runStage1({ ctx: ctx(), state, deps: deps().deps });
    expect(existsSync(planCorePath(repoRoot, QID))).toBe(true);

    // A rewind through V1/V1.5 restated the theorem; a later stage had run (patch mode).
    await writeFile(pipelineLogPath(repoRoot, QID), JSON.stringify({ stage: "3", status: "completed" }) + "\n");
    await writeFile(corePath(), JSON.stringify(core({ statement: "$E[Y]$ exists and is finite" })), "utf8");
    const second = deps();
    await runStage1({ ctx: ctx(), state, deps: second.deps });
    const prompt = second.prompt();
    expect(prompt).not.toContain("REVISE REUSE SCOPE");
    expect(prompt).not.toContain("Patch the existing plan at");
    expect(prompt).toContain("=== WHAT CHANGED IN THE CORE SINCE THE PLAN WAS WRITTEN ===");
    expect(prompt).toContain('statement: "$E[Y]$ exists" → "$E[Y]$ exists and is finite"');
    expect(prompt.indexOf("WHAT CHANGED")).toBeLessThan(prompt.indexOf("REVISION HEAD"));
    // The patch shows in full only the node the delta affects, never the proof body; its
    // assumption did not move, so it gets a reference line, and the lookup paths are named.
    expect(prompt).toContain("the 1 of 2 nodes this revise affects, in full");
    expect(prompt).toContain('"id":"thm:t"');
    expect(prompt).not.toContain("$Y$ is bounded");
    expect(prompt).toContain("ass:a | assumption | no plan entry");
    expect(prompt).toContain(`typed core (READ-ONLY): ${corePath()}`);
    expect(prompt).toContain(`plan: ${planPath(repoRoot, QID)}`);
    expect(prompt).toContain("looked_up_beyond_scope");
    expect(prompt).not.toContain("long proof");
    // The completed re-plan records the new core: a further pass sees nothing moved.
    expect(JSON.parse(await readFile(planCorePath(repoRoot, QID), "utf8")).statements[0].statement).toBe("$E[Y]$ exists and is finite");
    const third = deps();
    await runStage1({ ctx: ctx(), state, deps: third.deps });
    expect(third.prompt()).not.toContain("WHAT CHANGED");
    expect(third.prompt()).toContain("names no core node");
    expect(third.prompt()).not.toContain("$E[Y]$ exists and is finite");
  });

  it("the plan's qid is the run's, written by the runner: no prompt asks the planner for it", async () => {
    const state = createInitialState(QID);
    state.stage_completed = "V1.5";
    const d = deps().deps;
    d.runClaude = async () => {
      await mkdir(path.dirname(planPath(repoRoot, QID)), { recursive: true });
      await writeFile(planPath(repoRoot, QID), JSON.stringify({ nodes: {} }), "utf8");
      return JSON.stringify({ status: "completed", artifacts: [] });
    };
    expect((await runStage1({ ctx: ctx(), state, deps: d })).status).toBe("completed");
    expect(JSON.parse(await readFile(planPath(repoRoot, QID), "utf8")).qid).toBe(QID);
  });

  it("a blocked reply on a re-plan halts with the blocker's message instead of sending the earlier plan to F1.5", async () => {
    const state = createInitialState(QID);
    state.stage_completed = "V1.5";
    expect((await runStage1({ ctx: ctx(), state, deps: deps().deps })).status).toBe("completed");
    for (const status of ["blocked", "blocked-infeasible"]) {
      const blocked = deps().deps;
      blocked.runClaude = async () => JSON.stringify({ status, message: "the core's scope is undefined", feasibility_notes: "thm:t needs machinery outside reach." });
      const result = await runStage1({ ctx: ctx(), state, deps: blocked });
      expect(result).toMatchObject({ status: "checkpoint", advance: false });
      expect(result.message).toContain(`F1 ${status}: the core's scope is undefined thm:t needs machinery outside reach.`);
      expect(result.message).toContain("The plan on disk is the earlier one");
    }
    // a reply that says completed over a file that is no plan is the same halt: F1 is not completed
    // (the cursor moved on, and the next resume reviewed that file), and its message names the exit
    const noPlan = deps().deps;
    noPlan.runClaude = async () => {
      await writeFile(planPath(repoRoot, QID), JSON.stringify({ nodes: "none" }), "utf8");
      return JSON.stringify({ status: "completed", message: "planned" });
    };
    const result = await runStage1({ ctx: ctx(), state, deps: noPlan });
    expect(result).toMatchObject({ status: "checkpoint", advance: false });
    expect(result.message).toMatch(/F1 wrote no usable plan \(.*plan\.json does not parse as a plan\): planned\. A resume plans again\./);
    expect(state.flags.f1_blocked).toMatchObject({ message: result.message });
  });

  it("a cold start gets the slim core (no proof bodies), and a correction naming a node restricts the patch to it and its closure", async () => {
    const state = createInitialState(QID);
    state.stage_completed = "V1.5";
    const first = deps();
    await runStage1({ ctx: ctx(), state, deps: first.deps });
    expect(first.prompt()).toContain("$E[Y]$ exists");
    expect(first.prompt()).not.toContain("long proof");
    expect(first.prompt()).not.toContain("nodes this revise affects");
    expect(first.prompt()).not.toContain("EVERY OTHER NODE");
    // the F1.5 correction names the assumption: the statement consuming it is affected too
    const second = deps();
    await runStage1({
      ctx: ctx(), state, deps: second.deps, attempt: 2,
      priorReview: { status: "revise", classification: "reuse-fit", perItemFindings: [{ label: "ass:a", verdict: "FLAG", one_line: "x" }], verbatim_critique: "re-plan ass:a" },
    });
    expect(second.prompt()).toContain("the 2 of 2 nodes this revise affects, in full");
  });

  it("a directive on a plan with no record of the core it was written against compares the plan with the whole core, and says so", async () => {
    const state = createInitialState(QID);
    state.stage_completed = "V1.5";
    await runStage1({ ctx: ctx(), state, deps: deps().deps });
    await rm(planCorePath(repoRoot, QID));
    state.flags.f1_revise_directive = "re-plan thm:t";
    const second = deps();
    await runStage1({ ctx: ctx(), state, deps: second.deps });
    // the directive names thm:t only; ass:a may have moved under its id, and is shown
    expect(second.prompt()).not.toContain("nodes this revise affects");
    expect(second.prompt()).toContain("$Y$ is bounded");
    expect(await readFile(pipelineLogPath(repoRoot, QID), "utf8")).toContain("WHOLE CONTEXT — F1 revise has no readable record of the core its plan was written against");
  });

  it("a plan that grew by accretion is listed for compaction in the same pass, by entry, without its core records", async () => {
    const state = createInitialState(QID);
    state.stage_completed = "V1.5";
    await runStage1({ ctx: ctx(), state, deps: deps().deps });
    await writeFile(pipelineLogPath(repoRoot, QID), JSON.stringify({ stage: "3", status: "completed" }) + "\n");
    const entry = { lean_kind: "theorem", lean_name: "T", disposition: "define-local", notes: "REVISION 3 (CURRENT) ".repeat(200), rev3: "old" };
    await writeFile(planPath(repoRoot, QID), JSON.stringify({ qid: QID, nodes: { "thm:t": entry } }), "utf8");
    const again = deps();
    await runStage1({ ctx: ctx(), state, deps: again.deps });
    const prompt = again.prompt();
    expect(prompt).toContain("=== PLAN HYGIENE");
    expect(prompt).toContain(`- thm:t: \`notes\` is ${entry.notes.length} characters (cap ${PLAN_NOTES_MAX})`);
    expect(prompt).toContain("`rev3`");
    expect(prompt).not.toContain("REVISION 3 (CURRENT) REVISION 3"); // the entry is read from the file, not pasted
    expect(prompt).toContain("names no core node");
    expect(planHygieneBlock({ qid: QID, nodes: { "thm:t": { lean_kind: "theorem", lean_name: "T", disposition: "define-local", notes: "short" } } })).toBe("");
  });
});

describe("stage1ReviseSeeds", () => {
  it("seeds the nodes a correction or directive names and the nodes that moved; a hygiene finding seeds nothing", () => {
    const cur = core();
    cur.statements.push({ id: "lem:far", kind: "lemma", statement: "s", free_symbols: ["Y"], depends_on: [], status: "to-prove" } as never);
    const prior = { status: "revise" as const, classification: "c", perItemFindings: [{ label: "S1", verdict: "FLAG", one_line: "the world of thm:t" }], verbatim_critique: "" };
    expect(stage1ReviseSeeds(cur, { planCore: null, prior, directive: null })).toEqual(["thm:t"]);
    expect(stage1ReviseSeeds(cur, { planCore: null, prior: null, directive: "fix ass:a and thm:gone" })).toEqual(["ass:a"]);
    expect(stage1ReviseSeeds(cur, { planCore: core(), prior: null, directive: null })).toEqual(["lem:far"]);
    const gate = { status: "revise" as const, classification: "plan-gate", perItemFindings: [{ label: "thm:t", verdict: "FLAG-P11", one_line: "`notes` is 9000 characters" }], verbatim_critique: "The plan failed the gate." };
    expect(stage1ReviseSeeds(cur, { planCore: null, prior: gate, directive: null })).toEqual([]);
  });
});
