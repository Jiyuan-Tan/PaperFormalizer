// V1 end to end, with a fake core-builder agent.
//
// The M1 fixture paper is copied into a temp run dir's `source/`; the fake `runCodex`
// writes a canned `core.json` built from the REAL parsed environments, so a passing round
// is one the structural gate and the transcription lint actually accept. No network, no
// model call.
import { existsSync } from "node:fs";
import { cp, mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { afterEach, describe, expect, it } from "vitest";
import type { runCodex } from "../../src/shared/codex.js";
import type { CodexRunInput } from "../../src/shared/codex.js";
import { createVerifyInitialState, loadState } from "../../src/state.js";
import type { StateJson } from "../../src/types.js";
import {
  computeScope,
  MAX_SEGMENT_ROUNDS,
  runStageV1,
  workerAccessFailure,
  V1_LINT_WARNINGS_FILE,
  V1_REFS_FILE,
  V1_SCOPE_FILE,
} from "../../src/verify/stage_v1.js";
import { readV1Warnings } from "../../src/verify/lint_warnings.js";
import { V1_SEGMENTS_FILE } from "../../src/verify/segments.js";
import { hashSourceTree } from "../../src/verify/source_bundle.js";
import { buildEnvsJson } from "../../src/verify/tex_envs.js";
import { VERIFY_FILES, type EnvsJson } from "../../src/verify/types.js";

const QID = "verify_sample_paper";
const FIXTURE = path.join(path.dirname(fileURLToPath(import.meta.url)), "fixtures", "paper");

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const dir of tmpDirs.splice(0)) await rm(dir, { recursive: true, force: true });
});

interface Run {
  repoRoot: string;
  runDir: string;
  state: StateJson;
  envs: EnvsJson;
}

async function prepareRun(targets: string[] | null, edit?: (sourceDir: string) => Promise<void>): Promise<Run> {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-v1-"));
  tmpDirs.push(repoRoot);
  const runDir = path.join(repoRoot, "run");
  for (const sub of ["discovery", "logs"]) await mkdir(path.join(runDir, sub), { recursive: true });
  await cp(FIXTURE, path.join(runDir, VERIFY_FILES.sourceDir), { recursive: true });
  await edit?.(path.join(runDir, VERIFY_FILES.sourceDir));
  const state = createVerifyInitialState(QID, {
    phase: "init",
    // the hash seeding records: V1 revises an existing transcription only while the tree hashes the same
    source: { input: "sample_paper.tex", main_file: "main.tex", sha256: await hashSourceTree(path.join(runDir, VERIFY_FILES.sourceDir)) },
    targets,
    core_sha256: null,
    v1_rounds: 0,
    v1_5_rounds: 0,
    findings: [],
    report_path: null,
  });
  const { envs } = await buildEnvsJson(path.join(runDir, VERIFY_FILES.sourceDir), "main.tex");
  return { repoRoot, runDir, state, envs };
}

/** Statement kind + node id the canned core uses for each theorem-like fixture env. */
const STATEMENT_NODES: Record<string, { id: string; kind: "theorem" | "lemma"; deps: string[] }> = {
  "thm:main": { id: "thm:main", kind: "theorem", deps: ["def:po", "ass:unconf"] },
  "lemma-1": { id: "lem:passing", kind: "lemma", deps: [] },
  "cor:rate": { id: "thm:rate", kind: "theorem", deps: ["thm:main"] },
};

/** A faithful transcription of the fixture paper, restricted to `scope`. `flavour`
 * `"violate"` paraphrases the headline statement, which is exactly a rule (a) violation;
 * `"warn"` hangs an assumption off the unlabeled lemma, whose environment references
 * nothing — a rule (g) WARNING, which must not block the round. */
function cannedCore(
  envs: EnvsJson,
  scope: readonly string[],
  flavour: "pass" | "violate" | "warn",
): unknown {
  const inScope = envs.envs.filter((e) => scope.includes(e.id));
  const ids = new Set(scope);
  const norm = (s: string) =>
    s.replace(/\\label\s*\{[^{}]*\}/g, " ").replace(/\s+/g, " ").trim();
  return {
    qid: QID,
    symbols: [{ name: "Y_i(a)", type: "potential outcome of unit i under treatment a", space: "$\\mathbb{R}$", def: "The outcome unit $i$ would have under treatment $a$." }],
    sampling_model: { main: "i.i.d. units; the treatment is random given the covariates." },
    assumptions: inScope
      .filter((e) => e.kind === "assumption")
      .map((e) => ({
        id: e.id,
        condition: norm(e.body),
        standard: { name: "Unconfoundedness", cite: "vdv1998" },
        tex_locator: e.lines,
      })),
    definitions: inScope
      .filter((e) => e.kind === "definition")
      .map((e) => ({
        id: e.id,
        name: e.title ?? e.id,
        construction: norm(e.body),
        tex_locator: e.lines,
      })),
    statements: inScope
      .filter((e) => STATEMENT_NODES[e.id] !== undefined)
      .map((e) => {
        const node = STATEMENT_NODES[e.id];
        const paraphrase = flavour === "violate" && e.id === "thm:main";
        const deps = node.deps.filter((d) => ids.has(d) || d === "thm:main");
        if (flavour === "warn" && e.id === "lemma-1") deps.push("ass:unconf");
        return {
          id: node.id,
          kind: node.kind,
          statement: paraphrase ? "The estimator is consistent." : e.body,
          status: "to-prove",
          depends_on: deps,
          free_symbols: e.id === "thm:main" ? ["Y_i(a)"] : [],
          tex_locator: e.lines,
          ...(e.proof !== null ? { proof_tex: e.proof } : {}),
        };
      }),
    target_estimand: "the average treatment effect of A on Y",
    bibliography: [],
  };
}

/** The same transcription as a REFERENCE core: no text, only where the text is. `"refs-bad"`
 * points one assumption at anchors that do not occur, which the runner must report by id. */
function cannedRefs(envs: EnvsJson, scope: readonly string[], bad: boolean): unknown {
  const inScope = envs.envs.filter((e) => scope.includes(e.id));
  const ids = new Set(scope);
  return {
    qid: QID,
    target_estimand: "the average treatment effect of A on Y",
    symbols: [{ name: "Y_i(a)", type: "potential outcome of unit i under treatment a", space: "$\\mathbb{R}$", def: "The outcome unit $i$ would have under treatment $a$." }],
    sampling_model: { main: "i.i.d. units; the treatment is random given the covariates." },
    assumptions: inScope
      .filter((e) => e.kind === "assumption")
      .map((e) => ({
        id: e.id,
        source: bad ? { env: e.id, slice: { from: "phrase that is nowhere", to: "nowhere either" } } : { env: e.id },
        standard: { name: "Unconfoundedness", cite: "vdv1998" },
      })),
    definitions: inScope
      .filter((e) => e.kind === "definition")
      .map((e) => ({ id: e.id, name: e.title ?? e.id, source: { env: e.id } })),
    statements: inScope
      .filter((e) => STATEMENT_NODES[e.id] !== undefined)
      .map((e) => {
        const node = STATEMENT_NODES[e.id];
        return {
          id: node.id,
          kind: node.kind,
          env: e.id,
          depends_on: node.deps.filter((d) => ids.has(d) || d === "thm:main"),
          free_symbols: e.id === "thm:main" ? ["Y_i(a)"] : [],
        };
      }),
  };
}

interface CodexSpy {
  calls: CodexRunInput[];
  segmentCalls: CodexRunInput[];
  runCodex: typeof runCodex;
}

/** Fake agent: consumes `plan` one entry per call, writing the canned core for a
 * `pass`/`violate` round and replying `failed` (writing nothing) for a `fail` round. */
function codexSpy(
  run: Run,
  scope: readonly string[],
  plan: Array<"pass" | "violate" | "warn" | "fail" | "refs" | "refs-bad">,
): CodexSpy {
  const calls: CodexRunInput[] = [];
  const segmentCalls: CodexRunInput[] = [];
  const corePath = path.join(run.runDir, VERIFY_FILES.coreJson);
  const refsPath = path.join(run.runDir, V1_REFS_FILE);
  const segPath = path.join(run.runDir, V1_SEGMENTS_FILE);
  const fake = async (input: CodexRunInput): Promise<{ stdout: string; stderr: string }> => {
    if (/^SEGMENTS_FILE: /m.test(input.prompt)) {
      // The segmenter: the fixture's orphan proof (`\cref{lem:orphan}`) is bound to lemma-1 by
      // the flat line numbers printed in the SOURCE block. Not a plan step.
      segmentCalls.push(input);
      const lines = input.prompt.split("\n");
      const num = (re: RegExp): number => Number(/^\s*(\d+)\|/.exec(lines.find((l) => re.test(l)) ?? "")?.[1] ?? 0);
      const from = num(/\\begin\{proof\}\[Proof of \\cref\{lem:orphan\}\]/);
      const to = lines.findIndex((l) => /^\s*\d+\| \\end\{proof\}/.test(l) && Number(/^\s*(\d+)\|/.exec(l)![1]) > from);
      const toNum = Number(/^\s*(\d+)\|/.exec(lines[to] ?? "")?.[1] ?? 0);
      if (from > 0 && toNum > from) {
        // the canned core is built from `run.envs`: give it the proof the runner will now carry
        const fromIdx = lines.findIndex((l) => new RegExp(`^\\s*${from}\\|`).test(l));
        const text = lines.slice(fromIdx + 1, to).map((l) => l.replace(/^\s*\d+\| /, "")).join("\n").trim();
        run.envs.envs.find((e) => e.id === "lemma-1")!.proof = text;
      }
      await writeFile(segPath, JSON.stringify({ results: [], bindings: from > 0 && toNum > from ? [{ result: "lemma-1", proof_lines: [from, toNum], note: "title label is a typo" }] : [] }), "utf8");
      return { stdout: '{"status":"completed","message":"bound one proof"}', stderr: "" };
    }
    calls.push(input);
    const step = plan[calls.length - 1] ?? plan[plan.length - 1];
    if (step === "fail") {
      return {
        stdout: JSON.stringify({
          status: "failed",
          message: "the scope holds no statement I can transcribe without inventing notation",
        }),
        stderr: "",
      };
    }
    if (step === "refs" || step === "refs-bad") {
      await writeFile(refsPath, JSON.stringify(cannedRefs(run.envs, scope, step === "refs-bad"), null, 2), "utf8");
      return { stdout: '{"status":"completed"}', stderr: "" };
    }
    await writeFile(corePath, JSON.stringify(cannedCore(run.envs, scope, step), null, 2), "utf8");
    return { stdout: '{"status":"completed"}', stderr: "" };
  };
  return { calls, segmentCalls, runCodex: fake as unknown as typeof runCodex };
}

function stageArgs(run: Run, deps: { runCodex: typeof runCodex }, dryRun = false) {
  return {
    repoRoot: run.repoRoot,
    qid: QID,
    runDir: run.runDir,
    state: run.state,
    deps,
    dryRun,
    log: () => {},
  };
}

const ALL_SCOPE = ["def:po", "ass:unconf", "thm:main", "lemma-1", "cor:rate"];

async function readJson(file: string): Promise<Record<string, unknown>> {
  return JSON.parse(await readFile(file, "utf8")) as Record<string, unknown>;
}

describe("computeScope", () => {
  it.each([
    { rule: "takes every core-bearing env when no target is given", targets: null, scope: ALL_SCOPE },
    { rule: "follows \\ref edges from the targets and drops the rest", targets: ["thm:main"], scope: ["def:po", "ass:unconf", "thm:main"] },
    { rule: "names the known handles when a target matches nothing", targets: ["thm:ghost"], error: /thm:ghost match no environment/ },
  ])("$rule", async ({ targets, scope, error }) => {
    const run = await prepareRun(targets);
    if (error) expect(() => computeScope(run.envs, targets)).toThrow(error);
    else expect(computeScope(run.envs, targets)).toEqual(scope);
  });
});

describe("a worker that could not reach the run's files: the machine's halt, not the paper's", () => {
  /** The segmenter (or, with `builder`, the core builder) writes nothing and says `said`. */
  const denied = (spy: CodexSpy, said: string, builder = false, status = builder ? "failed" : "completed") => {
    const seen = { segmenter: 0, builder: 0 };
    const fake = async (input: CodexRunInput): Promise<{ stdout: string; stderr: string }> => {
      const segmenter = /^SEGMENTS_FILE: /m.test(input.prompt);
      seen[segmenter ? "segmenter" : "builder"] += 1;
      if (segmenter === builder) return (spy.runCodex as unknown as typeof fake)(input);
      return { stdout: JSON.stringify({ status, message: said }), stderr: "" };
    };
    return { seen, runCodex: fake as unknown as typeof runCodex };
  };

  it.each([
    ["bwrap: Can't mkdir parents for /scr/x: Permission denied", true],
    ["I could not read the supplied source files, so nothing was written.", true],
    ["The sandbox blocked every command.", true],
    ["Unable to write the output file at discovery/segments.json", true],
    ["apply_patch failed: Read-only file system", true],
    ["the scope holds no statement I can transcribe without inventing notation", false],
    ["I could not read Theorem 3 as a closed statement.", false],
    ["bound one proof", false],
  ])("reads %j as an access failure: %s", (said, is) => {
    expect(workerAccessFailure(said)).toBe(is);
  });

  it("the segmenter writes no file and says it was denied: halted at once, no second round, no builder call", async () => {
    const run = await prepareRun(null);
    const d = denied(codexSpy(run, ALL_SCOPE, ["pass"]), "I cannot access the supplied source: bwrap: Permission denied");
    const result = await runStageV1(stageArgs(run, { runCodex: d.runCodex }));
    expect(result.status).toBe("checkpoint");
    expect(result.message).toMatch(/^ENVIRONMENT checkpoint: the segmenter \(a model worker\) could not read or write the run's files — it said: I cannot access the supplied source/);
    expect(result.message).toMatch(/This is the machine, not the paper: run `paperformalizer doctor`[\s\S]*Do not retry, and do not change the paper or --targets/);
    expect(result.message).not.toMatch(/could not transcribe|fix the source/);
    expect(d.seen).toEqual({ segmenter: 1, builder: 0 });
  });

  it("a segmenter that wrote no file for another reason is asked again, then set aside as before", async () => {
    const run = await prepareRun(null);
    const d = denied(codexSpy(run, ALL_SCOPE, ["pass"]), "nothing to bind");
    const result = await runStageV1(stageArgs(run, { runCodex: d.runCodex }));
    expect(result.status).not.toBe("checkpoint");
    expect(d.seen.segmenter).toBe(MAX_SEGMENT_ROUNDS);
  });

  it("the builder's refusal: an access refusal is the environment's, a scope refusal stays the paper's", async () => {
    for (const [said, environment] of [["Permission denied writing discovery/core_refs.json", true], ["the scope holds no statement I can transcribe", false]] as const) {
      const run = await prepareRun(null);
      const d = denied(codexSpy(run, ALL_SCOPE, ["pass"]), said, true);
      const result = await runStageV1(stageArgs(run, { runCodex: d.runCodex }));
      expect(result.status).toBe("checkpoint");
      expect(/^ENVIRONMENT checkpoint: the V1 builder/.test(result.message)).toBe(environment);
      expect(/V1 could not transcribe this paper[\s\S]*fix the source or --targets/.test(result.message)).toBe(!environment);
      expect(d.seen.builder).toBe(1);
    }
    // … also when it "completes" with nothing written
    const run = await prepareRun(null);
    const d = denied(codexSpy(run, ALL_SCOPE, ["pass"]), "Done, but the sandbox let me write no file.", true, "completed");
    expect((await runStageV1(stageArgs(run, { runCodex: d.runCodex }))).message).toMatch(/^ENVIRONMENT checkpoint: the V1 builder/);
    expect(d.seen.builder).toBe(1);
  });
});

describe("runStageV1", () => {
  it("cold run: writes every artifact, accepts the core, counts the nodes", async () => {
    const run = await prepareRun(null);
    const spy = codexSpy(run, ALL_SCOPE, ["pass"]);
    const result = await runStageV1(stageArgs(run, { runCodex: spy.runCodex }));

    expect(result.status).toBe("completed");
    expect(result.message).toContain("3 statements");
    expect(result.message).toContain("1 assumptions");
    expect(result.message).toContain("1 definitions");
    expect(result.message).toContain("0 cited leaves");
    expect(spy.calls).toHaveLength(1);
    expect(run.state.verify?.v1_rounds).toBe(1);
    // The SCOPE block carries each environment's sentences and its proof's locator, never the proof's
    // text (read in flat.tex); the bibliography is its keys.
    const prompt = spy.calls[0]!.prompt;
    const scope = prompt.slice(prompt.indexOf("=== SCOPE"), prompt.indexOf("=== CONTEXT"));
    expect(scope).toContain('"proofLines"');
    expect(scope).not.toContain('"proof":');
    const bib = prompt.slice(prompt.indexOf("=== BIBLIOGRAPHY"), prompt.indexOf("FULL PAPER:"));
    expect(bib).toContain("vdv1998");
    expect(bib).not.toContain('"text"');

    for (const rel of [
      VERIFY_FILES.envsJson,
      VERIFY_FILES.flatTex,
      VERIFY_FILES.flatLineMap,
      VERIFY_FILES.coreJson,
      V1_SCOPE_FILE,
      V1_LINT_WARNINGS_FILE,
    ]) {
      expect(existsSync(path.join(run.runDir, rel)), rel).toBe(true);
    }
    // The V1.5 contract: the file is ALWAYS written, empty when there is nothing to settle.
    expect(await readJson(path.join(run.runDir, V1_LINT_WARNINGS_FILE))).toMatchObject({
      warnings: [],
      // The fixture paper deliberately carries an orphan appendix proof; the parser reports it.
      parser_warnings: [expect.stringContaining("attached to no result"), expect.stringMatching(/^segment: proof at flat lines \d+–\d+ bound to lemma-1/)],
    });
    expect(await readJson(path.join(run.runDir, V1_SCOPE_FILE))).toMatchObject({
      targets: null,
      envs: ALL_SCOPE,
    });
    // The bibliography is the paper's, copied mechanically over whatever the agent wrote.
    const core = await readJson(path.join(run.runDir, VERIFY_FILES.coreJson));
    expect((core.bibliography as Array<{ key: string }>).map((b) => b.key).sort()).toEqual([
      "knight2006",
      "lehmann2005",
      "vdv1998",
    ]);
  });

  it("records what it wrote as the transcription; a hand edit of it since stops V1 before it is lost", async () => {
    const run = await prepareRun(null);
    const spy = codexSpy(run, ALL_SCOPE, ["pass"]);
    expect((await runStageV1(stageArgs(run, { runCodex: spy.runCodex }))).status).toBe("completed");
    expect(run.state.verify?.transcribed_written_sha256).toMatch(/^[0-9a-f]{64}$/u);
    const file = path.join(run.runDir, VERIFY_FILES.coreTranscribed);
    await writeFile(file, `${await readFile(file, "utf8")}\n`, "utf8");
    const again = await runStageV1(stageArgs(run, { runCodex: spy.runCodex }));
    expect(again).toMatchObject({ status: "checkpoint", message: expect.stringContaining(`make the fix in ${VERIFY_FILES.coreRefs}`) });
  });

  it("sends the violations back and accepts the corrected core", async () => {
    const run = await prepareRun(null);
    const spy = codexSpy(run, ALL_SCOPE, ["violate", "pass"]);
    const result = await runStageV1(stageArgs(run, { runCodex: spy.runCodex }));

    expect(result.status).toBe("completed");
    expect(spy.calls).toHaveLength(2);
    expect(spy.calls[0].prompt).not.toContain("=== VIOLATIONS");
    expect(spy.calls[1].prompt).toContain("=== VIOLATIONS (must fix, edit REFS_FILE in place) ===");
    expect(spy.calls[1].prompt).toContain("(a) thm:main");
    expect(run.state.verify?.v1_rounds).toBe(2);
  });

  it("checkpoints after three violating rounds, quoting the last violations", async () => {
    const run = await prepareRun(null);
    const spy = codexSpy(run, ALL_SCOPE, ["violate", "violate", "violate"]);
    const result = await runStageV1(stageArgs(run, { runCodex: spy.runCodex }));

    expect(result.status).toBe("checkpoint");
    expect(spy.calls).toHaveLength(3);
    expect(result.message).toContain("3 rounds");
    expect(result.message).toContain("(a) thm:main");
  });

  it("consumes the V1.5 revise directive and deletes it once a round passes", async () => {
    const run = await prepareRun(null);
    const directivePath = path.join(run.runDir, VERIFY_FILES.v1ReviseDirective);
    await writeFile(
      directivePath,
      JSON.stringify({
        round: 1,
        findings: [
          {
            id: "thm:main",
            axis: "faithfulness",
            detail: "the statement silently drops the unconfoundedness hypothesis",
          },
        ],
      }),
      "utf8",
    );
    run.state.verify!.last_drift = { "thm:main": "" };
    const spy = codexSpy(run, ALL_SCOPE, ["pass"]);
    const result = await runStageV1(stageArgs(run, { runCodex: spy.runCodex }));
    // A consumed revise directive keeps the drift record the next V1.5 pass compares against.
    expect(run.state.verify!.last_drift).toEqual({ "thm:main": "" });

    expect(result.status).toBe("completed");
    expect(spy.calls[0].prompt).toContain("REVISE DIRECTIVE (round 1)");
    expect(spy.calls[0].prompt).toContain("silently drops the unconfoundedness hypothesis");
    expect(spy.calls[0].prompt).toContain("EDIT IT IN PLACE");
    expect(existsSync(directivePath)).toBe(false);
  });

  it("restricts the run to the --targets closure", async () => {
    const run = await prepareRun(["thm:main"]);
    const scope = ["def:po", "ass:unconf", "thm:main"];
    const spy = codexSpy(run, scope, ["pass"]);
    const result = await runStageV1(stageArgs(run, { runCodex: spy.runCodex }));

    expect(result.status).toBe("completed");
    expect(result.message).toContain("1 statements");
    expect(await readJson(path.join(run.runDir, V1_SCOPE_FILE))).toMatchObject({
      targets: ["thm:main"],
      envs: scope,
      theorem_like: ["thm:main"],
    });
    // The out-of-scope corollary is not in the prompt's SCOPE block.
    expect(spy.calls[0].prompt).toContain("thm:main");
    expect(spy.calls[0].prompt.split("=== CONTEXT")[0]).not.toContain("cor:rate");
  });

  it("reference core: the runner copies every text field from the source and accepts the core", async () => {
    const run = await prepareRun(null);
    const spy = codexSpy(run, ALL_SCOPE, ["refs"]);
    const result = await runStageV1(stageArgs(run, { runCodex: spy.runCodex }));
    expect(result.status).toBe("completed");
    expect(spy.calls.length).toBe(1);
    expect(spy.calls[0]!.prompt).toContain(`REFS_FILE: ${path.join(run.runDir, V1_REFS_FILE)}`);
    const core = await readJson(path.join(run.runDir, VERIFY_FILES.coreJson));
    const statements = core.statements as Array<Record<string, unknown>>;
    const main = statements.find((s) => s.id === "thm:main")!;
    const env = run.envs.envs.find((e) => e.id === "thm:main")!;
    expect(main.statement).toBe(env.body.trim());
    expect(main.proof_tex).toBe(env.proof!.trim());
    expect(main.tex_locator).toEqual(env.lines);
    const ass = (core.assumptions as Array<Record<string, unknown>>)[0]!;
    expect(ass.condition).toBe(run.envs.envs.find((e) => e.id === "ass:unconf")!.body.trim());
  });

  it("reference core: an anchor that does not cut comes back as a violation naming the node, then the fix is accepted", async () => {
    const run = await prepareRun(null);
    const spy = codexSpy(run, ALL_SCOPE, ["refs-bad", "refs"]);
    const result = await runStageV1(stageArgs(run, { runCodex: spy.runCodex }));
    expect(result.status).toBe("completed");
    expect(spy.calls.length).toBe(2);
    expect(spy.calls[1]!.prompt).toMatch(/\(ref\) ass:unconf\.source: anchor `from` "phrase that is nowhere" does not occur/);
  });

  it("dry run: writes a gate-clean mechanical core without calling the agent", async () => {
    const run = await prepareRun(null);
    const forbidden = (async () => {
      throw new Error("the dry run must not call codex");
    }) as unknown as typeof runCodex;
    const result = await runStageV1(stageArgs(run, { runCodex: forbidden }, true));

    expect(result.status).toBe("completed");
    expect(result.message).toContain("dry run");
    expect(run.state.verify?.v1_rounds).toBe(1);
    const core = await readJson(path.join(run.runDir, VERIFY_FILES.coreJson));
    expect(core.target_estimand).toBe("dry-run");
    expect((core.statements as Array<{ id: string }>).map((s) => s.id)).toEqual([
      "thm:main",
      "lem:lemma-1",
      "thm:rate",
    ]);
    // The mechanical core must satisfy rule (g) itself: `\cref{def:po,ass:unconf}` in the
    // theorem body is a dependency edge, and `\ref{thm:main}` in the corollary is another.
    const deps = Object.fromEntries(
      (core.statements as Array<{ id: string; depends_on: string[] }>).map((s) => [
        s.id,
        s.depends_on,
      ]),
    );
    expect(deps["thm:main"]).toEqual(["def:po", "ass:unconf"]);
    expect(deps["thm:rate"]).toEqual(["thm:main"]);
    expect(deps["lem:lemma-1"]).toEqual([]);
    expect(await readJson(path.join(run.runDir, V1_LINT_WARNINGS_FILE))).toMatchObject({
      warnings: [],
      // The fixture paper deliberately carries an orphan appendix proof; the parser reports it.
      parser_warnings: [expect.stringContaining("attached to no result")],
    });
  });

  it("refuses a parse whose proof is not whole TeX at a checkpoint, before the core builder runs (dry run or not)", async () => {
    const run = await prepareRun(null);
    const appendix = path.join(run.runDir, VERIFY_FILES.sourceDir, "appendix.tex");
    // (the orphan proof goes, so that no parser gap calls the segmenter first)
    const tex = (await readFile(appendix, "utf8")).replace("apply dominated convergence.", () => "apply dominated convergence: $$ a = b.");
    await writeFile(appendix, tex.slice(0, tex.indexOf("\\begin{proof}[Proof of \\cref{lem:orphan}]")), "utf8");
    const forbidden = (async () => {
      throw new Error("an unbalanced parse must not reach the agent");
    }) as unknown as typeof runCodex;
    for (const dry of [true, false]) {
      const result = await runStageV1(stageArgs(run, { runCodex: forbidden }, dry));
      expect(result.status).toBe("checkpoint");
      expect(result.message).toMatch(/V1 refused the transcription: 1 parsed statement\/proof text\(s\) are not balanced TeX/);
      expect(result.message).toMatch(/thm:main proof \(appendix\.tex:3-5\): \$\$ not closed by \$\$/);
      expect(existsSync(path.join(run.runDir, VERIFY_FILES.coreJson))).toBe(false);
    }
  });

  it("records a lint warning without blocking the round", async () => {
    const run = await prepareRun(null);
    const spy = codexSpy(run, ALL_SCOPE, ["warn"]);
    const result = await runStageV1(stageArgs(run, { runCodex: spy.runCodex }));

    expect(result.status).toBe("completed");
    expect(spy.calls).toHaveLength(1);
    const { warnings } = (await readJson(path.join(run.runDir, V1_LINT_WARNINGS_FILE))) as {
      warnings: string[];
    };
    expect(warnings).toHaveLength(1);
    expect(warnings[0]).toContain("lem:passing: depends on ass:unconf");
    expect(warnings[0]).toContain("V1.5 must confirm the paper actually assumes it");
  });

  it("warns of a published result a proof invokes by citation, without blocking the round — also over the warnings of a run made before the check", async () => {
    const run = await prepareRun(null, async (sourceDir) => {
      const appendix = path.join(sourceDir, "appendix.tex");
      await writeFile(appendix, (await readFile(appendix, "utf8")).replace("apply dominated convergence.", () => "apply dominated convergence \\citep[Theorem 2.18]{vdv1998}."), "utf8");
    });
    const file = path.join(run.runDir, V1_LINT_WARNINGS_FILE);
    await writeFile(file, JSON.stringify({ warnings: ["lem:passing: depends on ass:unconf which the environment never references; V1.5 must confirm the paper actually assumes it"], parser_warnings: [] }), "utf8");
    expect((await readV1Warnings(run.runDir)).lint).toHaveLength(1);
    const spy = codexSpy(run, ALL_SCOPE, ["pass"]);
    const result = await runStageV1(stageArgs(run, { runCodex: spy.runCodex }));

    expect(result.status).toBe("completed");
    expect(spy.calls).toHaveLength(1);
    expect((await readV1Warnings(run.runDir)).lint).toEqual([
      expect.stringMatching(/^thm:main: the proof of thm:main invokes \[vdv1998, Theorem 2\.18\] \(thm:main\/proof\/1\/1\): a published result used inside the proof, with no cited node of its own/),
    ]);
  });
});


describe("authors' note macros and a run on file", () => {
  /** The fixture with a colour wrapper around a sentence of its introduction. */
  const wrapped = async (sourceDir: string): Promise<void> => {
    const main = path.join(sourceDir, "main.tex");
    await writeFile(main, (await readFile(main, "utf8")).replace("\\begin{document}", () => "\\newcommand{\\lp}[1]{{\\color{black} #1}}\n\\begin{document}\n\\lp{An edited sentence. And another.}"), "utf8");
  };
  const forbidden = (async () => {
    throw new Error("a dry run must not call codex");
  }) as unknown as typeof runCodex;
  const flatOf = (run: Run): Promise<string> => readFile(path.join(run.runDir, VERIFY_FILES.flatTex), "utf8");

  it("a cold extraction reads them away and records it; a revise of a run read as written leaves its flat text alone", async () => {
    // a run from before the reading existed: flattened as written, no table in envs.json
    const old = await prepareRun(null, wrapped);
    process.env.PAPERFORMALIZER_NOTE_MACROS = "off";
    try {
      expect((await runStageV1(stageArgs(old, { runCodex: forbidden }, true))).status).toBe("completed");
    } finally {
      delete process.env.PAPERFORMALIZER_NOTE_MACROS;
    }
    const before = await flatOf(old);
    expect(before).toContain("\\lp{An edited sentence. And another.}");
    expect((await readJson(path.join(old.runDir, VERIFY_FILES.envsJson))).note_macros).toBeUndefined();
    // resumed under the reading: the transcription on file is revised against the text it was cut from
    const logs: string[] = [];
    expect((await runStageV1({ ...stageArgs(old, { runCodex: forbidden }, true), log: (m: string) => logs.push(m) })).status).toBe("completed");
    expect(logs.join("\n")).toMatch(/entry: revise the existing transcription/);
    expect(await flatOf(old)).toBe(before);
    expect((await readJson(path.join(old.runDir, VERIFY_FILES.envsJson))).note_macros).toBeUndefined();

    // a new run of the same paper
    const fresh = await prepareRun(null, wrapped);
    const freshLogs: string[] = [];
    expect((await runStageV1({ ...stageArgs(fresh, { runCodex: forbidden }, true), log: (m: string) => freshLogs.push(m) })).status).toBe("completed");
    const flat = await flatOf(fresh);
    expect(flat).toContain("\nAn edited sentence. And another.\n");
    expect(flat.split("\n").length).toBe(before.split("\n").length);
    expect(freshLogs).toContain("parser: unwrapped the note macro \\lp (1 use(s)): its definition only colours or groups its argument");
    expect((await readJson(path.join(fresh.runDir, VERIFY_FILES.envsJson))).note_macros).toMatchObject({ macros: expect.arrayContaining([expect.objectContaining({ name: "lp", class: "keep" })]) });
    expect((await readJson(path.join(fresh.runDir, V1_LINT_WARNINGS_FILE))).parser_warnings).toEqual(expect.arrayContaining([expect.stringMatching(/^the paper was read with its authors' note macros read away — K \\lp \(1\)/)]));
    // and its own revise replays the reading it recorded
    expect((await runStageV1(stageArgs(fresh, { runCodex: forbidden }, true))).status).toBe("completed");
    expect(await flatOf(fresh)).toBe(flat);
  });
});

describe("inline citations are accounted for", () => {
  const cite = async (sourceDir: string): Promise<void> => {
    const appendix = path.join(sourceDir, "appendix.tex");
    await writeFile(appendix, (await readFile(appendix, "utf8")).replace("apply dominated convergence.", () => "apply dominated convergence \\citep[Theorem 2.18]{vdv1998}."), "utf8");
  };
  /** An agent writing the canned reference core, with `extra[k]` merged in on its k-th call. */
  const agent = (run: Run, extra: Array<Record<string, unknown>>) => {
    const prompts: string[] = [];
    const segmenter = codexSpy(run, ALL_SCOPE, ["refs"]).runCodex as unknown as (input: CodexRunInput) => Promise<{ stdout: string; stderr: string }>;
    const fake = async (input: CodexRunInput): Promise<{ stdout: string; stderr: string }> => {
      if (/^SEGMENTS_FILE: /m.test(input.prompt)) return segmenter(input);
      prompts.push(input.prompt);
      await writeFile(path.join(run.runDir, V1_REFS_FILE), JSON.stringify({ ...(cannedRefs(run.envs, ALL_SCOPE, false) as object), ...extra[Math.min(prompts.length, extra.length) - 1] }, null, 2), "utf8");
      return { stdout: '{"status":"completed"}', stderr: "" };
    };
    return { prompts, runCodex: fake as unknown as typeof runCodex };
  };
  const SITE = "thm:main | vdv1998 | Theorem 2.18";

  it("cold: the prompt lists the site, a round that ignores it is sent back, the registered leaf is accepted", async () => {
    const run = await prepareRun(null, cite);
    const spy = agent(run, [{}, { proof_citations: [{ id: "lem:vdv-2-18", site: SITE, units: ["thm:main/proof/1/1", "thm:main/proof/1/1"] }] }]);
    const result = await runStageV1(stageArgs(run, { runCodex: spy.runCodex }));
    expect(result.status, result.message).toBe("completed");
    expect(spy.prompts).toHaveLength(2);
    expect(spy.prompts[0]).toContain(`=== INLINE CITATIONS — account for each ===\n- site "${SITE}" — the proof of thm:main cites [vdv1998, Theorem 2.18]\n  > thm:main/proof/1/1: `);
    expect(spy.prompts[1]).toMatch(/=== VIOLATIONS[^\n]*\n- \(i\) thm:main: its proof cites \[vdv1998, Theorem 2\.18\] at thm:main\/proof\/1\/1 and the citation "thm:main \| vdv1998 \| Theorem 2\.18" is not accounted for/);
    const core = await readJson(path.join(run.runDir, VERIFY_FILES.coreJson));
    const statements = core.statements as Array<{ id: string; statement: string; status: string; cited_in?: string; depends_on: string[]; source?: { cite: string; locator: string } }>;
    expect(statements.find((s) => s.id === "lem:vdv-2-18")).toMatchObject({ status: "cited", cited_in: "thm:main", source: { cite: "vdv1998", locator: "Theorem 2.18" } });
    expect(statements.find((s) => s.id === "lem:vdv-2-18")!.statement).toContain("apply dominated convergence \\citep[Theorem 2.18]{vdv1998}.");
    expect(statements.find((s) => s.id === "thm:main")!.depends_on).toContain("lem:vdv-2-18");
    expect((await readV1Warnings(run.runDir)).lint.filter((l) => l.includes("vdv1998, Theorem 2.18"))).toEqual([]);
  });

  it("cold: a dismissal is accepted and reaches the referee as a warning", async () => {
    const run = await prepareRun(null, cite);
    const spy = agent(run, [{ dismissed_citations: [{ site: SITE, reason: "pointer", note: "a see-also" }] }]);
    expect((await runStageV1(stageArgs(run, { runCodex: spy.runCodex }))).status).toBe("completed");
    expect(spy.prompts).toHaveLength(1);
    expect((await readV1Warnings(run.runDir)).lint.filter((l) => l.includes("vdv1998, Theorem 2.18"))).toEqual([
      expect.stringMatching(/^thm:main: the proof of thm:main cites \[vdv1998, Theorem 2\.18\] \(thm:main\/proof\/1\/1\); the transcription reads the citation as a comparison or a pointer to the cited work and made no cited node for it \(a see-also\)\./),
    ]);
  });

  it("a reference core written before the accounting, re-entered at V1: a warning, no violation, no agent", async () => {
    const run = await prepareRun(null, cite);
    // the run as an earlier version left it: its reference core has neither key
    run.state.verify!.source.sha256 = await hashSourceTree(path.join(run.runDir, VERIFY_FILES.sourceDir));
    await writeFile(path.join(run.runDir, V1_REFS_FILE), JSON.stringify(cannedRefs(run.envs, ALL_SCOPE, false)), "utf8");
    const forbidden = (async () => {
      throw new Error("a re-entry must not call the agent");
    }) as unknown as typeof runCodex;
    const result = await runStageV1(stageArgs(run, { runCodex: forbidden }));
    expect(result.status, result.message).toBe("completed");
    expect((await readV1Warnings(run.runDir)).lint.filter((l) => l.includes("vdv1998, Theorem 2.18"))).toEqual([
      expect.stringMatching(/^thm:main: the proof of thm:main invokes \[vdv1998, Theorem 2\.18\] \(thm:main\/proof\/1\/1\): a published result used inside the proof, with no cited node of its own/),
    ]);
  });
  it("a cold run halted with its citations unaccounted still accounts on --resume: the state remembers, whatever the reference core holds", async () => {
    const run = await prepareRun(null, cite);
    const idle = agent(run, [{}]); // a reference core with neither key, every round
    expect((await runStageV1(stageArgs(run, { runCodex: idle.runCodex }))).status).toBe("checkpoint");
    expect(run.state.verify!.citation_accounting).toBe(true);
    // the resume enters as a revise of that reference core; an agent that drops the keys again is sent back too
    const spy = agent(run, [{}, { proof_citations: [{ id: "lem:vdv-2-18", site: SITE, units: ["thm:main/proof/1/1", "thm:main/proof/1/1"] }] }]);
    const result = await runStageV1(stageArgs(run, { runCodex: spy.runCodex }));
    expect(result.status, result.message).toBe("completed");
    expect(spy.prompts).toHaveLength(2);
    for (const p of spy.prompts) {
      expect(p).toContain("=== INLINE CITATIONS — account for each ===");
      expect(p).toMatch(/=== VIOLATIONS[^\n]*\n- \(i\) thm:main: its proof cites \[vdv1998, Theorem 2\.18\]/);
    }
  });

  it("a drift on a registered citation reaches V1 as what it is: dismiss the site or change its units, nothing to re-transcribe", async () => {
    const run = await prepareRun(null, cite);
    run.state.verify!.source.sha256 = await hashSourceTree(path.join(run.runDir, VERIFY_FILES.sourceDir));
    const registered = { proof_citations: [{ id: "lem:vdv-2-18", site: SITE, units: ["thm:main/proof/1/1", "thm:main/proof/1/1"] }] };
    await writeFile(path.join(run.runDir, V1_REFS_FILE), JSON.stringify({ ...(cannedRefs(run.envs, ALL_SCOPE, false) as object), ...registered }), "utf8");
    await writeFile(path.join(run.runDir, VERIFY_FILES.v1ReviseDirective), JSON.stringify({ round: 1, findings: [{ id: "lem:vdv-2-18", axis: "faithfulness", detail: "the proof derives the step itself", fix: null }] }), "utf8");
    const spy = agent(run, [{ dismissed_citations: [{ site: SITE, reason: "proved_here", note: "derived in the proof" }] }]);
    const result = await runStageV1(stageArgs(run, { runCodex: spy.runCodex }));
    expect(result.status, result.message).toBe("completed");
    expect(spy.prompts[0]).toContain(
      "lem:vdv-2-18: a `proof_citations` entry has no text to re-transcribe. A faithfulness finding on it is about your account of the citation: move its site to\n`dismissed_citations` when the proof does not rely on the cited result, or change `units` when they leave out the citation or the step it gives (at most 3 consecutive units).",
    );
    const core = await readJson(path.join(run.runDir, VERIFY_FILES.coreJson));
    expect((core.statements as Array<{ id: string }>).map((x) => x.id)).not.toContain("lem:vdv-2-18");
  });

  it("a provisional error on a registered citation, in a round another node's drift opened, is not presented as a finding about its account", async () => {
    const run = await prepareRun(null, cite);
    run.state.verify!.source.sha256 = await hashSourceTree(path.join(run.runDir, VERIFY_FILES.sourceDir));
    const registered = { proof_citations: [{ id: "lem:vdv-2-18", site: SITE, units: ["thm:main/proof/1/1", "thm:main/proof/1/1"] }] };
    await writeFile(path.join(run.runDir, V1_REFS_FILE), JSON.stringify({ ...(cannedRefs(run.envs, ALL_SCOPE, false) as object), ...registered }), "utf8");
    const findings = [
      { id: "cor:rate", axis: "faithfulness", detail: "the rate is misread", fix: null },
      { id: "lem:vdv-2-18", axis: "correctness (provisional)", detail: "the cited theorem needs a dominating function" },
    ];
    await writeFile(path.join(run.runDir, VERIFY_FILES.v1ReviseDirective), JSON.stringify({ round: 1, findings }), "utf8");
    const spy = agent(run, [registered]);
    const result = await runStageV1(stageArgs(run, { runCodex: spy.runCodex }));
    expect(result.status, result.message).toBe("completed");
    expect(spy.prompts[0]).toContain("=== REVISE DIRECTIVE");
    expect(spy.prompts[0]).not.toContain("has no text to re-transcribe");
  });

  it("a cold run records the accounting in the saved state before its first agent call", async () => {
    const run = await prepareRun(null, cite);
    const killed = (async (input: CodexRunInput) => {
      if (/^SEGMENTS_FILE: /m.test(input.prompt)) return (codexSpy(run, ALL_SCOPE, ["refs"]).runCodex as unknown as (i: CodexRunInput) => Promise<{ stdout: string; stderr: string }>)(input);
      expect((await loadState(run.repoRoot, QID)).verify!.citation_accounting).toBe(true);
      throw new Error("killed");
    }) as unknown as typeof runCodex;
    await runStageV1(stageArgs(run, { runCodex: killed })).catch(() => undefined);
    expect((await loadState(run.repoRoot, QID)).verify!.citation_accounting).toBe(true);
  });
});

describe("mechanical revise", () => {
  it("applies the referee's structured fix to the reference core and accepts without an agent round", async () => {
    const run = await prepareRun(null);
    const refsPath = path.join(run.runDir, V1_REFS_FILE);
    const refs = cannedRefs(run.envs, ALL_SCOPE, false) as { statements: Array<{ id: string; depends_on: string[]; hypotheses?: string[] }> };
    const main = refs.statements.find((s) => s.id === "thm:main")!;
    main.depends_on = main.depends_on.filter((d) => d !== "ass:unconf");
    main.hypotheses = (main.hypotheses ?? []).filter((d) => d !== "ass:unconf");
    await writeFile(refsPath, JSON.stringify(refs, null, 2), "utf8");
    await writeFile(
      path.join(run.runDir, VERIFY_FILES.v1ReviseDirective),
      JSON.stringify({ round: 1, findings: [{ id: "thm:main", axis: "faithfulness", detail: "drops the density bound", fix: { add_depends_on: ["ass:unconf"] } }] }),
      "utf8",
    );
    const spy = codexSpy(run, ALL_SCOPE, ["refs"]);
    const logs: string[] = [];
    const result = await runStageV1({ ...stageArgs(run, { runCodex: spy.runCodex }), log: (m: string) => logs.push(m) });
    expect(result.status).toBe("completed");
    expect(result.message, logs.join("\n")).toMatch(/revised mechanically/);
    expect(spy.calls).toHaveLength(0);
    const after = JSON.parse(await readFile(refsPath, "utf8")) as { statements: Array<{ id: string; depends_on: string[] }> };
    expect(after.statements.find((s) => s.id === "thm:main")!.depends_on).toContain("ass:unconf");
    const warnings = await readJson(path.join(run.runDir, "discovery/v1_lint_warnings.json"));
    expect(warnings.parser_warnings).toEqual(expect.arrayContaining([expect.stringMatching(/^referee fix applied — thm:main: depends_on \+ ass:unconf/)]));
  });
});

describe("mechanical revise — a fix with a part in words", () => {
  it("the structural part is applied by the runner and the setting still reaches the agent: the finding is not dropped with the fix", async () => {
    const run = await prepareRun(null);
    const refsPath = path.join(run.runDir, V1_REFS_FILE);
    const refs = cannedRefs(run.envs, ALL_SCOPE, false) as { statements: Array<{ id: string; depends_on: string[]; hypotheses?: string[] }> };
    const main = refs.statements.find((s) => s.id === "thm:main")!;
    main.depends_on = main.depends_on.filter((d) => d !== "ass:unconf");
    main.hypotheses = (main.hypotheses ?? []).filter((d) => d !== "ass:unconf");
    await writeFile(refsPath, JSON.stringify(refs, null, 2), "utf8");
    await writeFile(
      path.join(run.runDir, VERIFY_FILES.v1ReviseDirective),
      JSON.stringify({ round: 1, findings: [{ id: "thm:main", axis: "faithfulness", detail: "drops the density bound. The setting the core's sampling_model must state for it: the design is fixed", fix: { add_depends_on: ["ass:unconf"], setting: "the design is fixed" } }] }),
      "utf8",
    );
    const spy = codexSpy(run, ALL_SCOPE, ["refs"]);
    const logs: string[] = [];
    await runStageV1({ ...stageArgs(run, { runCodex: spy.runCodex }), log: (m: string) => logs.push(m) });
    expect(logs.join("\n")).toMatch(/1 fix\(es\) applied by the runner, 0 rejected, 1 finding\(s\) left for the agent/);
    expect(spy.calls.length).toBeGreaterThan(0);
    expect(spy.calls[0]!.prompt).toContain("the design is fixed");
  });
});

describe("mechanical revise — a fix that does not fit the paper", () => {
  it("is not applied: the finding reaches the agent as prose with why, and the agent is never charged a violation the runner made", async () => {
    const run = await prepareRun(null);
    const refsPath = path.join(run.runDir, V1_REFS_FILE);
    await writeFile(refsPath, JSON.stringify(cannedRefs(run.envs, ALL_SCOPE, false), null, 2), "utf8");
    const fix = { new_assumption: { id: "ass:order", env: "no-such-env", from: "Let the kernel", to: "have order two.", wire_into: ["thm:main"] } };
    await writeFile(
      path.join(run.runDir, VERIFY_FILES.v1ReviseDirective),
      JSON.stringify({ round: 1, findings: [{ id: "thm:main", axis: "faithfulness", detail: "misses the kernel-order premise", fix }] }),
      "utf8",
    );
    const spy = codexSpy(run, ALL_SCOPE, ["refs"]);
    const logs: string[] = [];
    const result = await runStageV1({ ...stageArgs(run, { runCodex: spy.runCodex }), log: (m: string) => logs.push(m) });
    expect(result.status, logs.join("\n")).toBe("completed");
    expect(logs.join("\n")).toMatch(/referee fix rejected — thm:main: the edit does not fit the paper/);
    expect(spy.calls).toHaveLength(1);
    expect(spy.calls[0]!.prompt).toContain("misses the kernel-order premise");
    expect(spy.calls[0]!.prompt).toContain("The referee's structural fix could not be applied");
    expect(logs.join("\n")).not.toMatch(/round 1: \d+ reference violation/);
  });
});

describe("mechanical revise — a fix the agent's round undoes", () => {
  it("goes back to the agent once, with its finding, when it no longer applies to the agent's transcription", async () => {
    const run = await prepareRun(null);
    const refsPath = path.join(run.runDir, V1_REFS_FILE);
    const refs = cannedRefs(run.envs, ALL_SCOPE, false) as { assumptions: Array<{ id: string; source: unknown }> };
    // a premise only this transcription carries: the referee's fix wires it in; the agent's round drops it
    refs.assumptions.push({ ...refs.assumptions[0]!, id: "ass:extra" });
    await writeFile(refsPath, JSON.stringify(refs, null, 2), "utf8");
    await writeFile(
      path.join(run.runDir, VERIFY_FILES.v1ReviseDirective),
      JSON.stringify({
        round: 1,
        findings: [
          { id: "thm:main", axis: "faithfulness", detail: "needs the extra premise", fix: { add_depends_on: ["ass:extra"] } },
          // a second finding on the node, with no fix: it still reaches the agent
          { id: "thm:main", axis: "faithfulness", detail: "a second drift for the agent" },
        ],
      }),
      "utf8",
    );
    const spy = codexSpy(run, ALL_SCOPE, ["refs", "refs"]);
    const logs: string[] = [];
    await runStageV1({ ...stageArgs(run, { runCodex: spy.runCodex }), log: (m: string) => logs.push(m) });
    expect(logs.join("\n")).toMatch(/referee fix not re-applied — thm:main/);
    expect(spy.calls.length, logs.join("\n")).toBeGreaterThanOrEqual(2);
    expect(spy.calls[1]!.prompt).toContain("no longer applies to your transcription");
    expect(spy.calls[1]!.prompt).toContain("needs the extra premise");
    expect(spy.calls[0]!.prompt).toContain("a second drift for the agent");
  });
});

describe("the order of the symbol table is the runner's", () => {
  const Y = { name: "Y_i(a)", type: "potential outcome of unit i under treatment a", space: "$\\mathbb{R}$", def: "The outcome unit $i$ would have under treatment $a$." };
  // a chain listed backwards (m before k) and two symbols described through each other (L, g)
  const TABLE = [
    { name: "m", type: "count", space: "$\\mathbb{N}$", def: "Twice $k$.", refs: ["k"] },
    { name: "L", type: "constant", space: "$(0,\\infty)$", def: "The Lipschitz constant of $g$.", refs: ["g"] },
    Y,
    { name: "g", type: "link", space: "$\\mathbb{R}\\to\\mathbb{R}$", def: "The $L$-Lipschitz link.", refs: ["L"] },
    { name: "k", type: "count", space: "$\\mathbb{N}$", def: "A block size." },
  ];
  const ORDERED = ["k", "m", "L", "g", "Y_i(a)"];
  const refsWith = (run: Run, symbols: unknown[]): string => JSON.stringify({ ...(cannedRefs(run.envs, ALL_SCOPE, false) as object), symbols }, null, 2);
  /** An agent that writes the reference core with each table of `tables`, one per round. */
  const agent = (run: Run, tables: unknown[][]): { prompts: string[]; runCodex: typeof runCodex } => {
    const prompts: string[] = [];
    const fake = async (input: CodexRunInput): Promise<{ stdout: string; stderr: string }> => {
      if (/^SEGMENTS_FILE: /m.test(input.prompt)) return codexSpy(run, ALL_SCOPE, ["refs"]).runCodex(input) as unknown as { stdout: string; stderr: string };
      prompts.push(input.prompt);
      await writeFile(path.join(run.runDir, V1_REFS_FILE), refsWith(run, tables[Math.min(prompts.length, tables.length) - 1]!), "utf8");
      return { stdout: '{"status":"completed"}', stderr: "" };
    };
    return { prompts, runCodex: fake as unknown as typeof runCodex };
  };
  const symbolNames = async (run: Run): Promise<string[]> => ((await readJson(path.join(run.runDir, VERIFY_FILES.coreJson))).symbols as Array<{ name: string }>).map((x) => x.name);

  it("a table out of order, with symbols naming each other, is accepted in one round: the core is ordered, the agent's file untouched", async () => {
    const run = await prepareRun(null);
    const a = agent(run, [TABLE]);
    const result = await runStageV1(stageArgs(run, { runCodex: a.runCodex }));
    expect(result.status, result.message).toBe("completed");
    expect(a.prompts.length).toBe(1);
    expect(await symbolNames(run)).toEqual(ORDERED);
    expect(await readFile(path.join(run.runDir, V1_REFS_FILE), "utf8")).toBe(refsWith(run, TABLE));
    expect(((await readJson(path.join(run.runDir, VERIFY_FILES.coreTranscribed))).symbols as Array<{ name: string }>).map((x) => x.name)).toEqual(ORDERED);
  });

  it("a hand-edited reference core re-entered at V1 is ordered the same way, with no agent; a table in order is left as it is", async () => {
    const run = await prepareRun(null);
    const inOrder = ORDERED.map((n) => TABLE.find((x) => x.name === n)!);
    expect((await runStageV1(stageArgs(run, { runCodex: agent(run, [inOrder]).runCodex }))).status).toBe("completed");
    const before = await readFile(path.join(run.runDir, VERIFY_FILES.coreJson), "utf8");
    expect(await symbolNames(run)).toEqual(ORDERED);
    const forbidden = (async () => {
      throw new Error("a revise re-entry must not call the agent");
    }) as unknown as typeof runCodex;
    await writeFile(path.join(run.runDir, V1_REFS_FILE), refsWith(run, TABLE), "utf8");
    const result = await runStageV1(stageArgs(run, { runCodex: forbidden }));
    expect(result.status, result.message).toBe("completed");
    expect(result.message).toMatch(/materialized from the existing transcription \(no agent\)/);
    expect(await readFile(path.join(run.runDir, VERIFY_FILES.coreJson), "utf8")).toBe(before); // same core, byte for byte
    expect(await readFile(path.join(run.runDir, V1_REFS_FILE), "utf8")).toBe(refsWith(run, TABLE));
  });

  it("a ref that names no symbol of the table still comes back as a violation", async () => {
    const run = await prepareRun(null);
    const a = agent(run, [[...TABLE.slice(0, 4), { ...TABLE[4]!, refs: ["ghost"] }], TABLE]);
    const result = await runStageV1(stageArgs(run, { runCodex: a.runCodex }));
    expect(result.status, result.message).toBe("completed");
    expect(a.prompts.length).toBe(2);
    expect(a.prompts[1]).toContain("(G1) symbol:k: refs names 'ghost', which is no symbol of the table");
    expect(a.prompts[1]).not.toContain("before it is defined");
  });
});

describe("re-entry: rewinds revise, they never rebuild", () => {
  const patchFile = {
    key_results: ["thm:main"],
    key_contribution: "identification of the effect",
    patches: [
      {
        node: "thm:main",
        corrected_statement: "Suppose the outcome is bounded. Then the effect is identified.",
        proof_note: "bound Y before integrating",
      },
    ],
    unfixable: [],
  };
  const forbidden = (async () => {
    throw new Error("a revise re-entry must not call the agent");
  }) as unknown as typeof runCodex;

  it("with the source unchanged and a reference core on disk: materializes core.json (refs + patches) with no agent call", async () => {
    const run = await prepareRun(null);
    const first = codexSpy(run, ALL_SCOPE, ["refs"]);
    expect((await runStageV1(stageArgs(run, { runCodex: first.runCodex }))).status).toBe("completed");
    await writeFile(path.join(run.runDir, VERIFY_FILES.patches), JSON.stringify(patchFile), "utf8");
    run.state.verify!.confirmed = { "thm:rate": "kept" };
    const logs: string[] = [];
    const result = await runStageV1({ ...stageArgs(run, { runCodex: forbidden }), log: (m: string) => logs.push(m) });
    expect(result.status, logs.join("\n")).toBe("completed");
    expect(result.message).toMatch(/materialized from the existing transcription \(no agent\)/);
    expect(logs.join("\n")).toMatch(/entry: revise the existing transcription — source unchanged/);
    const core = await readJson(path.join(run.runDir, VERIFY_FILES.coreJson));
    const main = (core.statements as Array<{ id: string; statement: string }>).find((s) => s.id === "thm:main")!;
    expect(main.statement).toContain("Suppose the outcome is bounded.");
    const transcribed = await readFile(path.join(run.runDir, VERIFY_FILES.coreTranscribed), "utf8");
    expect(transcribed).not.toContain("Suppose the outcome is bounded.");
    expect(run.state.verify!.confirmed).toEqual({ "thm:rate": "kept" }); // the cache survives a revise
  });

  it("when the source changed: a cold extraction, the old reference core set aside and the carried verdicts dropped", async () => {
    const run = await prepareRun(null);
    const first = codexSpy(run, ALL_SCOPE, ["refs"]);
    expect((await runStageV1(stageArgs(run, { runCodex: first.runCodex }))).status).toBe("completed");
    const before = run.state.verify!.source.sha256;
    run.state.verify!.confirmed = { "thm:rate": "stale" };
    // a revise directive pending from V1.5, and the drift it carries: neither reaches this extraction
    run.state.verify!.last_drift = { "thm:rate": "{}" };
    await writeFile(path.join(run.runDir, VERIFY_FILES.v1ReviseDirective), JSON.stringify({ mode: "transcribe", round: 1, findings: [] }), "utf8");
    const main = path.join(run.runDir, VERIFY_FILES.sourceDir, "main.tex");
    await writeFile(main, `${await readFile(main, "utf8")}\n% an edit\n`, "utf8");
    const second = codexSpy(run, ALL_SCOPE, ["refs"]);
    const logs: string[] = [];
    const result = await runStageV1({ ...stageArgs(run, { runCodex: second.runCodex }), log: (m: string) => logs.push(m) });
    expect(result.status).toBe("completed");
    expect(second.calls).toHaveLength(1);
    expect(logs.join("\n")).toMatch(/entry: cold extraction — the source changed/);
    expect(existsSync(path.join(run.runDir, `${V1_REFS_FILE}.prev`))).toBe(true);
    expect(run.state.verify!.source.sha256).not.toBe(before);
    expect(run.state.verify!.confirmed).toEqual({});
    expect(existsSync(path.join(run.runDir, VERIFY_FILES.v1ReviseDirective))).toBe(false);
    expect(run.state.verify!.last_drift).toBeUndefined();
  });

});
