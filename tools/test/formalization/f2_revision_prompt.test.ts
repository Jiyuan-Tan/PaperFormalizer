import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { coreJsonPath } from "../../src/core/core_io.js";
import { runStage2 } from "../../src/formalization/stage2.js";
import { F2_REVISION_NOTES_HEADER } from "../../src/formalization/f2_revision_context.js";
import { artifactPaths, type StageDeps } from "../../src/pipeline_support.js";
import { pipelineLogPath, promptPath, scaffoldBasisPath } from "../../src/paths.js";
import { formalizationCoreContextValue } from "../../src/formalization/core_context.js";
import { CoreSchema } from "../../src/core/schema.js";
import type { PipelineContext, StateJson } from "../../src/types.js";
import { tk } from "../toolkit/helpers.js";

let repoRoot = "";

function state(redirect: boolean, stage = "2"): StateJson {
  return {
    stage_completed: stage,
    lean_subdir: "CausalSmith/Stat/LocalContextTest",
    design_decisions: {},
    added_assumptions: [],
    loop: "research",
    next_action: null,
    lineage: null,
    from_question_oq_id: null,
    method_id: null,
    closed_oq: null,
    flags: {

      rewound_from_stage4d: null,

      missing_architecture: false,
      scaffold_redirect: redirect
        ? "Fix target.\n\nDeclarations to edit (one obj_id per line, verbatim):\n- thm:target"
        : null,
    },
  } as unknown as StateJson;
}

/** `replan`: no redirect; a later stage ran, and the core/plan moved since the scaffold was made
 *  (`basis`: whether F2 recorded what that scaffold realizes). */
async function arrange(redirect: boolean, replan?: { basis: boolean }) {
  const ctx: PipelineContext = {
    repoRoot,
    toolkit: tk(repoRoot),
    qid: "stat_local_context_test",
    dryRun: false,
    resume: redirect,
  };
  const runState = state(redirect, replan ? "3" : "2");
  const paths = artifactPaths(ctx, runState);
  const core = {
    qid: ctx.qid,
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
  const node = (lean_kind: string, lean_name: string, extra = {}) => ({
    lean_kind,
    lean_name,
    disposition: "define-local",
    reuse: null,
    modules: [],
    ...extra,
  });
  const plan = {
    qid: ctx.qid,
    env: [{ id: "S1", world: "local", binds_symbols: ["x", "z"], binds_sampling_model: true, disposition: "define-local" }],
    nodes: {
      "ass:shared": node("assumption", "Shared"),
      "ass:unrelated": node("assumption", "Unrelated", { notes: "UNRELATED_PLAN_SENTINEL" }),
      "thm:target": node("theorem", "target", { hyps: ["ass:shared"] }),
      "lem:unrelated": node("lemma", "unrelated", { hyps: ["ass:unrelated"] }),
    },
    citations: [],
  };
  await mkdir(path.dirname(coreJsonPath(ctx)), { recursive: true });
  await mkdir(path.dirname(paths.plan), { recursive: true });
  await mkdir(paths.leanDir, { recursive: true });
  if (redirect || replan?.basis) {
    await writeFile(scaffoldBasisPath(repoRoot, ctx.qid), JSON.stringify({ plan, core: formalizationCoreContextValue(CoreSchema.parse(core)) }));
  }
  if (replan) {
    // The re-plan: the target's statement moved, and a new lemma joined (no tag on disk yet).
    core.statements[0]!.statement = "target x, restated";
    core.statements.push({ id: "lem:new", kind: "lemma", statement: "new x", free_symbols: ["x"], depends_on: [], status: "to-prove" });
    (plan.nodes as Record<string, unknown>)["lem:new"] = node("lemma", "fresh");
  }
  await writeFile(coreJsonPath(ctx), JSON.stringify(core));
  await writeFile(paths.plan, JSON.stringify(plan));
  await writeFile(
    path.join(paths.leanDir, "Main.lean"),
    [
      "-- @env: S1",
      "-- @node: ass:shared",
      "-- @node: ass:unrelated",
      "-- @node: thm:target",
      "-- @node: lem:unrelated",
      "theorem target : True := by trivial",
      "",
    ].join("\n"),
  );
  return { ctx, runState };
}

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(os.tmpdir(), "f2-local-prompt-"));
  await mkdir(path.dirname(promptPath(repoRoot, "stage2_scaffold.txt")), { recursive: true });
  await writeFile(promptPath(repoRoot, "stage2_scaffold.txt"), "scaffold instructions");
  await writeFile(promptPath(repoRoot, "stage2_head_revise.txt"), "revise instructions");
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

/** Run F2 once with a scaffolder that stops after its prompt is captured. */
async function capture(ctx: PipelineContext, runState: StateJson, opts: { reply?: Record<string, unknown> } = {}): Promise<{ prompt: string }> {
  let prompt = "";
  const blocked = JSON.stringify({
    status: "blocked-missing-architecture",
    message: "stop after prompt capture",
    missing_items: [{ kind: "definition", name_suggestion: "Fixture", purpose: "test", why_substantial: "test" }],
    ...opts.reply,
  });
  const deps = {
    runCodex: async (o: { prompt: string }) => {
      prompt = o.prompt;
      return { stdout: blocked, stderr: "" };
    },
    runClaude: async () => blocked,
  } as unknown as StageDeps;
  await runStage2({ ctx, state: runState, deps });
  return { prompt };
}

describe("F2 revision prompt localization", () => {
  it("sends a local packet on a targeted redirect", async () => {
    const { ctx, runState } = await arrange(true);
    let prompt = "";
    const blocked = JSON.stringify({
      status: "blocked-missing-architecture",
      message: "stop after prompt capture",
      missing_items: [{ kind: "definition", name_suggestion: "Fixture", purpose: "test", why_substantial: "test" }],
    });
    const deps = {
      runCodex: async (opts: { prompt: string }) => {
        prompt = opts.prompt;
        return { stdout: blocked, stderr: "" };
      },
      runClaude: async () => blocked,
    } as unknown as StageDeps;
    await runStage2({ ctx, state: runState, deps });
    expect(prompt).toContain("LOCAL F2 REVISION CONTEXT");
    expect(prompt).not.toContain("tag EXACTLY ONE canonical primary declaration");
    expect(prompt).toContain("@realizes <core-symbol-name>(<short clause hint>)");
    expect(prompt).toContain('"thm:target"');
    // a prerequisite is no record: its text is given with the statement taking it, and it is named a
    // neighbour; every node — an unrelated one too — keeps its one line
    const core = JSON.parse(prompt.split("Typed core JSON (localized affected-region projection):\n")[1]!.split("\n")[0]!);
    expect(core.assumptions).toEqual([]);
    expect(core.hypothesis_texts).toEqual({ "ass:shared": "x positive" });
    expect(prompt).toContain("ass:shared | assumption | assumption Shared");
    expect(prompt).toContain("lem:unrelated | lemma | lemma unrelated");
    expect(prompt).toMatch(/=== NEIGHBOURS OF THE AFFECTED NODES \(1 of the 3 nodes not shown in full\) ===\n[^\n]*\nass:shared\n/);
    expect(prompt).not.toContain("UNRELATED_CORE_SENTINEL");
    expect(prompt).not.toContain("UNRELATED_PLAN_SENTINEL");
    expect(prompt).toContain(`typed core (READ-ONLY): ${coreJsonPath(ctx)}`);
    expect(prompt).toContain(`plan: ${artifactPaths(ctx, runState).plan}`);
    expect(prompt).toContain("looked_up_beyond_scope");
  });

  it("a re-scaffold after a re-plan carries what moved since the scaffold was made, and the node the scaffold lacks", async () => {
    const { ctx, runState } = await arrange(false, { basis: true });
    const { prompt } = await capture(ctx, runState);
    expect(prompt).toContain("LOCAL F2 REVISION CONTEXT");
    expect(prompt).toContain("target x, restated");
    expect(prompt).toContain('"lem:new"');
    expect(prompt).toContain("ass:shared | assumption | assumption Shared");
    expect(prompt).not.toContain("UNRELATED_CORE_SENTINEL");
    expect(prompt).not.toContain("UNRELATED_PLAN_SENTINEL");
  });

  it("a revise with no record of what its scaffold realizes, and nothing naming a target, keeps the whole plan and core", async () => {
    const { ctx, runState } = await arrange(false, { basis: false });
    const { prompt } = await capture(ctx, runState);
    expect(prompt).not.toContain("LOCAL F2 REVISION CONTEXT");
    expect(prompt).toContain("UNRELATED_CORE_SENTINEL");
    expect(prompt).toContain("UNRELATED_PLAN_SENTINEL");
  });

  it("a redirect on a scaffold with no readable record of what it realizes keeps the whole context, and says so", async () => {
    const { ctx, runState } = await arrange(true);
    // a text that moved under its id since the scaffold was made cannot be told from the targets
    await writeFile(scaffoldBasisPath(repoRoot, ctx.qid), "{ not json");
    const { prompt } = await capture(ctx, runState);
    expect(prompt).not.toContain("LOCAL F2 REVISION CONTEXT");
    expect(prompt).toContain("UNRELATED_CORE_SENTINEL");
    expect(await readFile(pipelineLogPath(repoRoot, ctx.qid), "utf8")).toContain("WHOLE CONTEXT — F2 revise has no readable record of the plan and core its scaffold was made from");
  });

  it("a plan that changed outside its entries since the scaffold (a citation) keeps the whole context: the entries do not say which declarations it reaches", async () => {
    const { ctx, runState } = await arrange(true);
    const planPath = artifactPaths(ctx, runState).plan;
    const plan = JSON.parse(await readFile(planPath, "utf8"));
    plan.citations = [{ id: "cite:bk2022", title: "T", authors: "A", year: 2022, locator: "Theorem 2 (restated)" }];
    await writeFile(planPath, JSON.stringify(plan));
    const { prompt } = await capture(ctx, runState);
    expect(prompt).not.toContain("LOCAL F2 REVISION CONTEXT");
    expect(prompt).toContain("UNRELATED_PLAN_SENTINEL");
    expect(await readFile(pipelineLogPath(repoRoot, ctx.qid), "utf8")).toContain("WHOLE CONTEXT — the plan changed outside its node and S-block entries");
  });

  it("an entry whose notes alone were rewritten since the scaffold is carried", async () => {
    const { ctx, runState } = await arrange(true);
    const planPath = artifactPaths(ctx, runState).plan;
    const plan = JSON.parse(await readFile(planPath, "utf8"));
    plan.nodes["lem:unrelated"].notes = "NOTES_ONLY_SENTINEL: state the bound per fold";
    await writeFile(planPath, JSON.stringify(plan));
    const { prompt } = await capture(ctx, runState);
    expect(prompt).toContain("NOTES_ONLY_SENTINEL");
    expect(await readFile(pipelineLogPath(repoRoot, ctx.qid), "utf8")).toContain("1 moved since the scaffold");
  });

  it("a loop reroute carries the flagged nodes alone, each with the reviewer's finding on its record", async () => {
    const { ctx, runState } = await arrange(true);
    runState.flags.scaffold_redirect = [
      "The premise drifts.",
      F2_REVISION_NOTES_HEADER,
      "• ass:shared: FINDING_SENTINEL — the Lean asks x ≥ 0",
      "",
      "Declarations to edit (one obj_id per line, verbatim):",
      "- ass:shared",
    ].join("\n");
    const { prompt } = await capture(ctx, runState);
    const core = JSON.parse(prompt.split("Typed core JSON (localized affected-region projection):\n")[1]!.split("\n")[0]!);
    expect(core.assumptions).toEqual([expect.objectContaining({ id: "ass:shared", reviewer_finding: "FINDING_SENTINEL — the Lean asks x ≥ 0" })]);
    // the user of the flagged premise is a neighbour line, not a record: its declaration takes the fix by name
    expect(core.statements).toEqual([]);
    expect(prompt).toMatch(/=== NEIGHBOURS OF THE AFFECTED NODES[^\n]*\n[^\n]*\nthm:target\n/);
    // the finding is printed once, on the record; the directive keeps its summary and its targets
    expect(prompt.split("FINDING_SENTINEL")).toHaveLength(2);
    expect(prompt).toContain("The premise drifts.");
    expect(prompt).toContain("on its record below (`reviewer_finding`)");
    const log = await readFile(pipelineLogPath(repoRoot, ctx.qid), "utf8");
    expect(log).toContain("F2 revise carries 1 node(s) in full (1 flagged or named, 0 moved since the scaffold, 0 without a declaration, 0 as context: named in their text or in a directive) with 1 neighbour(s)");
  });

  it("a node a redirect's text mentions beside its targets is carried as context, not as a target", async () => {
    const { ctx, runState } = await arrange(true);
    runState.flags.scaffold_redirect = "thm:target must restate what ass:unrelated says.\n\nDeclarations to edit (one obj_id per line, verbatim):\n- thm:target";
    const { prompt } = await capture(ctx, runState);
    expect(prompt).toContain("Carried beside them as CONTEXT (a target's text or a directive names them; change one only if the fix requires it): ass:unrelated");
    expect(prompt).toContain("UNRELATED_CORE_SENTINEL");
    expect(prompt).toContain("Requested/resolved targets: thm:target\n");
  });

  it("a flagged node whose record also moved since the scaffold carries what moves with it", async () => {
    const { ctx, runState } = await arrange(false, { basis: true });
    const corePath = coreJsonPath(ctx);
    const core = JSON.parse(await readFile(corePath, "utf8"));
    core.assumptions[0].condition = "x strictly positive";
    await writeFile(corePath, JSON.stringify(core));
    runState.flags.scaffold_redirect = "Fix it.\n\nDeclarations to edit (one obj_id per line, verbatim):\n- ass:shared";
    const { prompt } = await capture(ctx, runState);
    const shown = JSON.parse(prompt.split("Typed core JSON (localized affected-region projection):\n")[1]!.split("\n")[0]!);
    expect(shown.statements.map((s: { id: string }) => s.id)).toContain("thm:target");
  });

  it("a stray target is left out and logged; a revise none of whose targets resolves keeps the whole context and says so in the run's log", async () => {
    const { ctx, runState } = await arrange(true);
    runState.flags.scaffold_redirect = "Fix it.\n\nDeclarations to edit (one obj_id per line, verbatim):\n- thm:target\n- aux_helper";
    const scoped = await capture(ctx, runState);
    expect(scoped.prompt).toContain("LOCAL F2 REVISION CONTEXT");
    expect(scoped.prompt).toContain("Named, but no node of the core or S-block of the plan (find it in the Lean files): aux_helper");
    expect(scoped.prompt).not.toContain("UNRELATED_CORE_SENTINEL");
    expect(await readFile(pipelineLogPath(repoRoot, ctx.qid), "utf8")).toContain("left out: aux_helper");
    runState.flags.scaffold_redirect = "Fix it.\n\nDeclarations to edit (one obj_id per line, verbatim):\n- aux_helper";
    const { prompt } = await capture(ctx, runState);
    expect(prompt).toContain("UNRELATED_CORE_SENTINEL");
    expect(await readFile(pipelineLogPath(repoRoot, ctx.qid), "utf8")).toContain("WHOLE CONTEXT — F2 local context is unavailable for revision target(s) (aux_helper");
  });

  it("a carried consumer keeps the gate it threads when the gate itself is not carried", async () => {
    const { ctx, runState } = await arrange(true);
    const planPath = artifactPaths(ctx, runState).plan;
    const plan = JSON.parse(await readFile(planPath, "utf8"));
    // A gate the plan gate accepts: a result the paper cites, which the target uses.
    plan.nodes["lem:unrelated"] = { ...plan.nodes["lem:unrelated"], lean_kind: "assumption", lean_name: "UnrelatedGate", gate: true, gate_class: "cited", source: "cite:fixture", hyps: [] };
    plan.nodes["thm:target"].hyps = ["ass:shared", "lem:unrelated"];
    plan.citations = [{ id: "cite:fixture", title: "Fixture", authors: "A", year: 2020, locator: "Lemma 1" }];
    await writeFile(planPath, JSON.stringify(plan));
    const core = JSON.parse(await readFile(coreJsonPath(ctx), "utf8"));
    Object.assign(core.statements[1], { status: "cited", source: { cite: "F2020", locator: "Lemma 1" } });
    core.statements[0].depends_on.push("lem:unrelated");
    core.bibliography = [{ key: "F2020", citation: "A (2020)" }];
    await writeFile(coreJsonPath(ctx), JSON.stringify(core));
    await writeFile(scaffoldBasisPath(repoRoot, ctx.qid), JSON.stringify({ plan, core: formalizationCoreContextValue(CoreSchema.parse(core)) }));
    const { prompt } = await capture(ctx, runState);
    expect(prompt).toContain("LOCAL F2 REVISION CONTEXT");
    expect(prompt).toContain("• gate `UnrelatedGate` → hypothesis on: target");
    expect(prompt).not.toContain('"lem:unrelated":{');
  });

  it("two revise calls about different nodes open with the same text — the instructions with every realization rule, the line of every node", async () => {
    const real = (name: string) => readFile(path.join(process.cwd(), "src/formalization/prompts/F2", name), "utf8");
    const redirectOn = (id: string) => `Fix ${id}.\n\nDeclarations to edit (one obj_id per line, verbatim):\n- ${id}`;
    const prompts: string[] = [];
    for (const id of ["thm:target", "sym:z"]) {
      const { ctx, runState } = await arrange(true);
      await writeFile(promptPath(repoRoot, "stage2_scaffold.txt"), await real("stage2_scaffold.txt"));
      await writeFile(promptPath(repoRoot, "stage2_head_revise.txt"), await real("stage2_head_revise.txt"));
      runState.flags.scaffold_redirect = redirectOn(id);
      prompts.push((await capture(ctx, runState)).prompt);
    }
    const [a, b] = prompts as [string, string];
    const cut = a.indexOf("=== SCAFFOLD REDIRECT DIRECTIVE");
    expect(cut).toBeGreaterThan(0);
    expect(b.slice(0, cut)).toBe(a.slice(0, cut));
    // the shared opening holds the instructions, the policy, the revise rules, the brief, every node and the files
    for (const part of ["You are Stage 2: the LEAN SCAFFOLDER", "=== HARD RULES ===", "=== BOOKKEEPING PREMISE POLICY", "=== REVISE MODE", "=== THE PLAN AND THE CORE", "Lean target subdirectory:", "=== EVERY NODE (4; reference only) ===", "lem:unrelated | lemma | lemma unrelated", "  - Main.lean"]) {
      expect(a.slice(0, cut)).toContain(part);
    }
    expect(a.slice(0, cut)).not.toContain("{{");
    expect(a.slice(0, cut)).not.toContain("=== FILE LAYOUT + POST-PROOF LENGTH");
    // every rule, whatever the targets are: a flagged symbol alone carries no node, and a fix may edit a neighbour of another kind
    for (const rule of ["- `assumption` → ONE named `def <lean_name> : Prop := <the core condition>`", "- `gate:true` statement node →", "- definition, CLASS", "- definition, CONSTRUCTION", "- statement (`lean_kind:\"theorem\"|\"lemma\"`)", "- open-ended residual"]) {
      expect(a.slice(0, cut)).toContain(rule);
    }
  });

  it("a revise that must scaffold a node anew reads the instructions whole", async () => {
    const { ctx, runState } = await arrange(false, { basis: true });
    await writeFile(promptPath(repoRoot, "stage2_scaffold.txt"), await readFile(path.join(process.cwd(), "src/formalization/prompts/F2/stage2_scaffold.txt"), "utf8"));
    const { prompt } = await capture(ctx, runState);
    expect(prompt).toContain("LOCAL F2 REVISION CONTEXT");
    expect(prompt).toContain("=== FILE LAYOUT + POST-PROOF LENGTH (REQUIRED) ===");
    expect(prompt).toContain("=== MISSING-ARCHITECTURE CHECK (escalate before drafting) ===");
    expect(prompt).toContain("- `gate:true` statement node →");
  });

  it("keeps the complete plan/core on a cold scaffold", async () => {
    const { ctx, runState } = await arrange(false);
    let prompt = "";
    const blocked = JSON.stringify({
      status: "blocked-missing-architecture",
      message: "stop after prompt capture",
      missing_items: [{ kind: "definition", name_suggestion: "Fixture", purpose: "test", why_substantial: "test" }],
    });
    const deps = {
      runCodex: async (opts: { prompt: string }) => {
        prompt = opts.prompt;
        return { stdout: blocked, stderr: "" };
      },
      runClaude: async () => blocked,
    } as unknown as StageDeps;
    await runStage2({ ctx, state: runState, deps });
    expect(prompt).not.toContain("LOCAL F2 REVISION CONTEXT");
    expect(prompt).toContain("UNRELATED_CORE_SENTINEL");
    expect(prompt).toContain("UNRELATED_PLAN_SENTINEL");
  });

});
