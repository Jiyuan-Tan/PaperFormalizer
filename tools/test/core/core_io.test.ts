// A run's core.json is the runner's file and holds the paper's text verbatim: every reader takes it
// as written. A paper indented with tabs is the case that showed a reader repairing it (F1 refused
// the core V1.5 had accepted).

import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, mkdir, readFile, writeFile, rm } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { parseTypedCore, readFormalizationCore, readTypedCore } from "../../src/core/core_io.js";
import { readFormalizationCoreContext } from "../../src/formalization/core_context.js";
import { runStage1 } from "../../src/formalization/stage1.js";
import { planGatePrelint } from "../../src/formalization/stage1_5.js";
import { readRunCore } from "../../src/proposals/round_b.js";
import { formalizationDir, planCorePath, planPath, promptPath } from "../../src/paths.js";
import { createInitialState } from "../../src/state.js";
import type { Core } from "../../src/core/schema.js";
import type { PipelineContext } from "../../src/types.js";
import type { StageDeps } from "../../src/pipeline_support.js";
import { tk } from "../toolkit/helpers.js";

const QID = "pid_tabcore";
// A tab before a letter, a tab before a backslash, and a control space at a line end.
const STATEMENT = "Assume the above.\n\tLet\n\t\\begin{equation}\n\t\tE[Y] = 0 \\\n\t\\end{equation}";
const CONSTRUCTION = "\tthe mean\n\t\\[ \\theta = E[Y] \\]";

function core(): Core {
  return {
    qid: QID,
    symbols: [{ name: "Y", type: "outcome", space: "\\mathbb R", def: "the outcome", refs: [] }],
    assumptions: [
      { id: "ass:a", kind: "assumption", condition: "\t$Y$ is bounded", free_symbols: ["Y"], novel: { flag: true, justification: "stated" }, used_by: ["thm:t"] },
    ],
    definitions: [{ id: "def:d", kind: "definition", name: "theta", construction: CONSTRUCTION, free_symbols: ["Y"] }],
    statements: [
      { id: "thm:t", kind: "theorem", statement: STATEMENT, free_symbols: ["Y"], depends_on: ["ass:a"], proof_tex: "\tlong proof", status: "to-prove" },
    ],
    sampling_model: { iid: "units are iid" },
    target_estimand: "E[Y]",
    bibliography: [],
  } as unknown as Core;
}

let repoRoot: string;
const ctx = (): PipelineContext => ({ repoRoot, toolkit: tk(repoRoot), qid: QID, dryRun: false, resume: false });
const corePath = (): string => path.join(formalizationDir(repoRoot, QID), "discovery", "core.json");

beforeEach(async () => {
  repoRoot = await mkdtemp(path.join(tmpdir(), "tabcore-"));
  await mkdir(path.dirname(corePath()), { recursive: true });
  await writeFile(corePath(), JSON.stringify(core(), null, 2), "utf8");
});

afterEach(async () => {
  await rm(repoRoot, { recursive: true, force: true });
});

describe("a core whose text is indented with tabs", () => {
  it("is read unchanged, byte for byte, by every core reader", async () => {
    const parsed = parseTypedCore(await readFile(corePath(), "utf8"), "test");
    for (const read of [parsed, await readTypedCore(corePath()), await readFormalizationCore(corePath()), await readRunCore(tk(repoRoot), QID)]) {
      expect(read).toEqual(parsed);
      expect(read.statements[0]!.statement).toBe(STATEMENT);
      expect(read.definitions[0]!.construction).toBe(CONSTRUCTION);
      expect(read.assumptions[0]!.condition).toBe("\t$Y$ is bounded");
    }
    const context = JSON.parse(await readFormalizationCoreContext(corePath(), "test")) as Core;
    expect(context.statements[0]!.statement).toBe(STATEMENT);
    expect(context.definitions[0]!.construction).toBe(CONSTRUCTION);
  });

  it("still refuses any other control character, naming the field", () => {
    const bad = core();
    (bad.statements[0] as { statement: string }).statement = "$\u0008eta$";
    expect(() => parseTypedCore(JSON.stringify(bad), "test")).toThrow(/copied from the paper.s source[^]*statements\[0\]\.statement: U\+0008/);
  });

  it("is accepted by F1, which plans from the paper's text and records the core as written", async () => {
    for (const [name, body] of [["stage1_template.txt", "stub stage1_template"], ["stage1_head_revise.txt", "REVISION HEAD"]]) {
      const p = promptPath(repoRoot, name);
      await mkdir(path.dirname(p), { recursive: true });
      await writeFile(p, body, "utf8");
    }
    let prompt = "";
    const deps: StageDeps = {
      runClaude: async (o: unknown) => {
        prompt = (o as { prompt: string }).prompt;
        const p = planPath(repoRoot, QID);
        await mkdir(path.dirname(p), { recursive: true });
        await writeFile(p, JSON.stringify({ qid: QID, nodes: {} }), "utf8");
        return JSON.stringify({ status: "completed", artifacts: [] });
      },
      runCodex: async () => { throw new Error("runCodex should not be called by Stage 1"); },
    };
    const state = createInitialState(QID);
    state.stage_completed = "V1.5";
    expect((await runStage1({ ctx: ctx(), state, deps })).status).toBe("completed");
    expect(prompt).toContain(JSON.stringify(STATEMENT).slice(1, -1));
    expect(await readFile(planCorePath(repoRoot, QID), "utf8")).toBe(await readFile(corePath(), "utf8"));
  });

  it("is accepted by the F1.5 plan gate", async () => {
    const review = await planGatePrelint({ ctx: ctx(), state: createInitialState(QID) }, planPath(repoRoot, QID));
    // The core is read; what the gate then reports is the plan F1 has not written.
    expect(review).toMatchObject({ status: "revise", perItemFindings: [{ verdict: "FLAG-missing" }] });
  });
});
