/**
 * Degenerate witnesses (owner decision 2026-09-24): an `error` must say where its witness lives
 * (`witness_regime`, `witness_instance`). A witness that exists only in a case the paper's setting
 * implicitly excludes (`degenerate`) is no error of the paper: the runner records the exclusion as a
 * bookkeeping condition (`ass:bk-*`) on the statement — reported with the bookkeeping conditions,
 * never rendered in the annotated paper, never sent to the fixer.
 */
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState } from "../../src/state.js";
import type { StateJson } from "../../src/types.js";
import { planAnnotations } from "../../src/verify/annotated_paper.js";
import { buildCore } from "../../src/verify/core_graph.js";
import { SHARD_REPLY, GLOBAL_REPLY, settleDegenerateWitness } from "../../src/verify/referee_shards.js";
import { runStageV1_5 } from "../../src/verify/stage_v1_5.js";
import { VERIFY_FILES, type V15NodeVerdict, type VerifyStageArgs } from "../../src/verify/types.js";
import { symbolReply } from "./symbol_fake.js";

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

const FLAT = [
  "\\documentclass{article}",
  "\\begin{document}",
  "Let $m$ be a linear functional on $\\Gamma$, mean-square continuous with exponent $q$.",
  "",
  "\\begin{proposition}\\label{prop:rate}",
  "Under Assumption~\\ref{ass:ms}, the remainder is $O(\\bar{Q}^{1/2} r^{q/2})$.",
  "\\end{proposition}",
  "",
  "\\begin{assumption}\\label{ass:ms}",
  "$E[m(W,\\gamma)^2] \\leq \\bar{Q} \\|\\gamma\\|^{2q}$ for all $\\gamma \\in \\Gamma$.",
  "\\end{assumption}",
  "\\end{document}",
].join("\n");

function core(): Core {
  return {
    qid: "deg",
    symbols: [{ name: "m", type: "functional" }, { name: "q", type: "exponent" }],
    assumptions: [{ id: "ass:ms", kind: "regularity", condition: "$E[m(W,\\gamma)^2] \\leq \\bar{Q} \\|\\gamma\\|^{2q}$ for all $\\gamma \\in \\Gamma$.", free_symbols: ["m", "q"], novel: { flag: true, justification: "A1" }, tex_locator: { file: "main.tex", from: 9, to: 11, env: "assumption", label: "ass:ms" } }],
    definitions: [],
    statements: [{ id: "prop:rate", kind: "proposition", statement: "Under Assumption~\\ref{ass:ms}, the remainder is $O(\\bar{Q}^{1/2} r^{q/2})$.", depends_on: ["ass:ms"], free_symbols: ["q"], proof_tex: "", status: "to-prove", tex_locator: { file: "main.tex", from: 5, to: 7, env: "proposition", label: "prop:rate" } }],
    target_estimand: "t",
    bibliography: [],
  } as unknown as Core;
}

const EXCLUSION = "$m$ is not identically zero on $\\Gamma$ (so Assumption~\\ref{ass:ms} holds only with $q = 1$)";
const ok = (id: string): V15NodeVerdict => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "reproduced", witness: null, fix: null, bookkeeping_assumption: null, reading: null, minimality: false, weakens_contribution: false, witness_regime: null, witness_instance: null });
const refuted = (regime: "in_scope" | "degenerate" | null, over: Partial<V15NodeVerdict> = {}): V15NodeVerdict => ({
  ...ok("prop:rate"),
  correctness: "error",
  detail: "the rate fails for q = 1/2",
  witness: "Take $m \\equiv 0$ and $\\bar Q = 0$: the assumption holds with $q = 1/2$ and the bound is claimed at rate $r^{1/4}$.",
  witness_regime: regime,
  witness_instance: regime ? "m ≡ 0, Q̄ = 0, q = 1/2" : null,
  bookkeeping_assumption: regime === "degenerate" ? { condition: EXCLUSION, reason: "the witness needs m ≡ 0" } : null,
  ...over,
});

/** The ids a shard call grades (its NODES TO GRADE section). */
const shardIds = (prompt: string): string[] =>
  (prompt.match(/=== NODES TO GRADE[^\n]*===\n\n(?:[^\n-][^\n]*\n\n)?((?:- .*\n?)+)/)?.[1] ?? "").split("\n").filter(Boolean).map((l) => l.slice(2));

/** `replies[k]`: every node's grade the k-th time it is graded (a shard's retry is its second). The
 * sharded referee answers per shard; the global pass adds nothing. `calls`: the node-shard calls. */
async function run(replies: V15NodeVerdict[][]): Promise<{ state: StateJson; runDir: string; calls: CodexRunInput[]; logs: string[]; args: VerifyStageArgs }> {
  const root = await mkdtemp(path.join(os.tmpdir(), "verify-degenerate-"));
  tmpDirs.push(root);
  const runDir = path.join(root, "runs", "deg");
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  await writeFile(path.join(runDir, VERIFY_FILES.coreJson), JSON.stringify(core(), null, 2));
  await writeFile(path.join(runDir, VERIFY_FILES.coreTranscribed), JSON.stringify(core(), null, 2));
  await writeFile(path.join(runDir, VERIFY_FILES.flatTex), FLAT);
  const state = createVerifyInitialState("deg", { phase: "v1", source: { input: "p", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
  const calls: CodexRunInput[] = [];
  const logs: string[] = [];
  const seen = new Map<string, number>();
  const codex = (async (input: CodexRunInput) => {
    const sym = symbolReply(input);
    if (sym !== null) return { stdout: sym, stderr: "" };
    if (input.outputSchema === GLOBAL_REPLY) return { stdout: JSON.stringify({ verdict: "PASS", summary: "g", patch_review: null, rejection_verdicts: null, cross_node: [] }), stderr: "" };
    if (input.outputSchema !== SHARD_REPLY) throw new Error("unexpected call");
    calls.push(input);
    const nodes = shardIds(input.prompt).map((id) => {
      const k = (seen.get(id) ?? 0) + 1;
      seen.set(id, k);
      const v = replies[k - 1]?.find((n) => n.id === id);
      if (!v) throw new Error(`unexpected grading #${k} of ${id}`);
      return v;
    });
    return { stdout: JSON.stringify({ summary: "s", nodes }), stderr: "" };
  }) as typeof runCodex;
  const args: VerifyStageArgs = { repoRoot: root, qid: "deg", runDir, state, deps: { runCodex: codex }, dryRun: false, log: (m) => logs.push(m) };
  return { state, runDir, calls, logs, args };
}

describe("witness regime", () => {
  it("a degenerate witness becomes a bookkeeping exclusion on the statement: accepted, never an error, never the fixer's", async () => {
    const r = await run([[refuted("degenerate"), ok("ass:ms")]]);
    const res = await runStageV1_5(r.args);
    expect(res.status).toBe("completed");
    expect(r.calls).toHaveLength(2); // one shard per level (ass:ms, then prop:rate), no retry
    const accepted = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
    const bk = accepted.assumptions.find((a) => a.id === "ass:bk-1")!;
    expect(bk.condition).toBe(EXCLUSION);
    expect(bk.bookkeeping?.reason).toContain("m ≡ 0, Q̄ = 0, q = 1/2");
    expect(accepted.statements[0]!.depends_on).toContain("ass:bk-1");
    const review = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v15Review), "utf8"));
    const settled = review.nodes.find((n: V15NodeVerdict) => n.id === "prop:rate");
    expect(settled.correctness).toBe("bookkeeping");
    // The shard settles it (`settleDegenerateWitness`); the review says why.
    expect(settled.detail).toContain("[degenerate witness — recorded as a bookkeeping exclusion, not an error]");
    expect(r.state.verify!.paper_errors ?? {}).toEqual({});
    expect(r.state.verify!.findings.some((f) => f.kind === "refuted")).toBe(false);
  });

  it("an in-scope witness stays an error (a patch round)", async () => {
    const r = await run([[refuted("in_scope"), ok("ass:ms")]]);
    const res = await runStageV1_5(r.args);
    expect(res.status).toBe("patch");
    const directive = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(directive.mode).toBe("patch");
    expect(directive.findings.map((f: { id: string }) => f.id)).toEqual(["prop:rate"]);
  });

  it.each([
    ["an error with no witness_regime", () => [refuted(null), ok("ass:ms")], ["no witness_regime", "no witness_instance"]],
    ["a degenerate witness without the exclusion, or a regime on a non-error", () => [refuted("degenerate", { bookkeeping_assumption: null }), { ...ok("ass:ms"), witness_regime: "in_scope" }], ["degenerate witness but no bookkeeping_assumption", `node "ass:ms" carries a witness_regime`]],
  ] as Array<[string, () => V15NodeVerdict[], string[]]>)("%s breaks the contract (retried once, then set aside: a checkpoint)", async (_t, reply, problems) => {
    const r = await run([reply(), reply()]);
    const res = await runStageV1_5(r.args);
    expect(res.status).toBe("checkpoint");
    for (const p of problems) expect(res.message).toContain(p);
  });

  it("a bookkeeping condition is stated in the annotated paper by one note at its result (no red, no blue, no reading)", () => {
    const c = core();
    const built = buildCore(c, { review: { verdict: "PASS", summary: "", nodes: [settleDegenerateWitness(refuted("degenerate")), ok("ass:ms")] } }).core;
    expect(built.assumptions.some((a) => a.id === "ass:bk-1")).toBe(true);
    const env = (id: string, envName: string, from: number, to: number) => ({ id, kind: envName, envName, label: id, title: null, body: FLAT.split("\n").slice(from, to - 1).join("\n"), proof: null, proofLines: null, section: null, lines: { file: "main.tex", from, to }, refs: [] });
    const plan = planAnnotations({
      files: { "main.tex": FLAT },
      envs: { main_file: "main.tex", files: ["main.tex"], newtheorem: {}, envs: [env("prop:rate", "proposition", 5, 7), env("ass:ms", "assumption", 9, 11)], bibliography: [] } as never,
      flatText: FLAT,
      lineMap: FLAT.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 })),
      refs: null,
      transcribed: c,
      core: built,
      patches: null,
      paperErrors: {},
      findings: [],
      review: { verdict: "PASS", summary: "", nodes: [settleDegenerateWitness(refuted("degenerate")), ok("ass:ms")] },
    });
    const cond = built.assumptions.find((a) => a.id === "ass:bk-1")!.condition.replace(/\s+/gu, " ").trim();
    expect(Object.values(plan.edits).flat().map((e) => e.text)).toEqual([`\\vsCondition{${cond}}`]);
    expect(plan.records).toEqual([expect.objectContaining({ node: "prop:rate", kind: "condition added", located_by: "env-end", summary: expect.stringMatching(/^ass:bk-1: /u) })]);
  });

});
