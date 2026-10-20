/**
 * A finding on an inline cited leaf (`cited_in`) has no repair path of its own: the leaf's text is a
 * passage of its host's proof. The V1.5 runner hands an `error` graded on it to the fixer as the
 * HOST's (`stage_v1_5.ts` `errorsOnHosts`, read by `routeReview`); an `unclear` — the source shown
 * lacks the cited result — stops for the source, naming the result and its file.
 */
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState } from "../../src/state.js";
import { GLOBAL_REPLY, SHARD_REPLY } from "../../src/verify/referee_shards.js";
import { buildCore, basisInputs, basisOf } from "../../src/verify/core_graph.js";
import { rebuildPatchedCore } from "../../src/verify/patches.js";
import { compactCore } from "../../src/verify/referee_shard_prompts.js";
import { errorsOnHosts, inlineLeaves, keepEarlierConditions, partitionByBasis, priorConditionLines, routeReview, runStageV1_5 } from "../../src/verify/stage_v1_5.js";
import { VERIFY_FILES, type V15NodeVerdict, type V15Review, type VerifyStageArgs } from "../../src/verify/types.js";
import { symbolReply } from "./symbol_fake.js";

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

const PASSAGE = "By \\cite[Theorem 2]{k} we get $a \\le c$.";
const FLAT = [
  "\\documentclass{article}",
  "\\begin{document}",
  "\\begin{lemma}\\label{lem:a}",
  "The bound $a \\le b$ holds.",
  "\\end{lemma}",
  "\\begin{proof}",
  `We start from the definition. ${PASSAGE} Since $c \\le b$ the claim follows.`,
  "\\end{proof}",
  "\\begin{lemma}\\label{lem:b}",
  "The bound $d \\le e$ holds.",
  "\\end{lemma}",
  "\\end{document}",
].join("\n");
const LEAF = "lem:k-thm-2";

const OTHER = { id: "lem:b", kind: "lemma", statement: "The bound $d \\le e$ holds.", depends_on: [], free_symbols: [], proof_tex: "", status: "to-prove", tex_locator: { file: "main.tex", from: 9, to: 11, env: "lemma", label: "lem:b" } };

function core(other = false): Core {
  return {
    qid: "inl",
    symbols: [],
    assumptions: [],
    definitions: [],
    statements: [
      { id: "lem:a", kind: "lemma", statement: "The bound $a \\le b$ holds.", depends_on: [LEAF], free_symbols: [], proof_tex: "", status: "to-prove", tex_locator: { file: "main.tex", from: 3, to: 5, env: "lemma", label: "lem:a" } },
      { id: LEAF, kind: "lemma", statement: PASSAGE, depends_on: [], free_symbols: [], status: "cited", cited_in: "lem:a", source: { cite: "k", locator: "Theorem 2" }, tex_locator: { file: "main.tex", from: 6, to: 8, env: "proof", label: null } },
      ...(other ? [OTHER] : []),
    ],
    target_estimand: "t",
    bibliography: [{ key: "k", citation: "K (2020), A book" }],
  } as unknown as Core;
}

const ok = (id: string): V15NodeVerdict => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "reproduced", witness: null, fix: null, bookkeeping_assumption: null, reading: null, minimality: false, weakens_contribution: false, witness_regime: null, witness_instance: null });
const shardIds = (prompt: string): string[] =>
  (prompt.match(/=== NODES TO GRADE[^\n]*===\n\n(?:[^\n-][^\n]*\n\n)?((?:- .*\n?)+)/)?.[1] ?? "").split("\n").filter(Boolean).map((l) => l.slice(2));

async function run(grade: (id: string) => V15NodeVerdict, other = false, patches: unknown = null): Promise<{ runDir: string; args: VerifyStageArgs; graded: string[]; prompts: Map<string, string> }> {
  const root = await mkdtemp(path.join(os.tmpdir(), "verify-inline-host-"));
  tmpDirs.push(root);
  const runDir = path.join(root, "runs", "inl");
  await mkdir(path.join(runDir, "discovery", "cited_sources"), { recursive: true });
  await writeFile(path.join(runDir, VERIFY_FILES.coreJson), JSON.stringify(core(other), null, 2));
  await writeFile(path.join(runDir, VERIFY_FILES.coreTranscribed), JSON.stringify(core(other), null, 2));
  await writeFile(path.join(runDir, VERIFY_FILES.flatTex), FLAT);
  await writeFile(path.join(runDir, "discovery", "cited_sources", "k.txt"), "Theorem 2. If $a$ is bounded then $a \\le c$.");
  if (patches) {
    await writeFile(path.join(runDir, VERIFY_FILES.patches), JSON.stringify(patches, null, 2));
    await rebuildPatchedCore(runDir, { detectHandEdits: false });
  }
  const state = createVerifyInitialState("inl", { phase: "v1", source: { input: "p", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
  const graded: string[] = [];
  const prompts = new Map<string, string>();
  const codex = (async (input: CodexRunInput) => {
    const sym = symbolReply(input);
    if (sym !== null) return { stdout: sym, stderr: "" };
    if (input.outputSchema === GLOBAL_REPLY) return { stdout: JSON.stringify({ verdict: "PASS", summary: "g", patch_review: patches ? { key_results_ok: true, detail: "" } : null, rejection_verdicts: null, cross_node: [] }), stderr: "" };
    if (input.outputSchema !== SHARD_REPLY) throw new Error("unexpected call");
    const ids = shardIds(input.prompt);
    graded.push(...ids);
    for (const id of ids) prompts.set(id, input.prompt);
    return { stdout: JSON.stringify({ summary: "s", nodes: ids.map(grade) }), stderr: "" };
  }) as typeof runCodex;
  return { runDir, graded, prompts, args: { repoRoot: root, qid: "inl", runDir, state, deps: { runCodex: codex }, dryRun: false, log: () => {} } };
}

describe("a finding on an inline cited leaf", () => {
  it("an error on the leaf becomes a repair demand on its host: the fixer is never sent to a node with no text", async () => {
    const r = await run((id) => (id === LEAF ? { ...ok(id), correctness: "error", detail: "Theorem 2 needs $a$ bounded, which the proof never shows.", witness: "an unbounded $a$", witness_regime: "in_scope", witness_instance: "a unbounded" } : ok(id)));
    const res = await runStageV1_5(r.args);
    expect(res.status, res.message).toBe("patch");
    const directive = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v1ReviseDirective), "utf8")) as { mode: string; findings: Array<{ id: string; axis: string; detail: string; witness: string | null }> };
    expect(directive.mode).toBe("patch");
    expect(directive.findings.map((f) => [f.id, f.axis, f.witness])).toEqual([["lem:a", "correctness", "an unbounded $a$"]]);
    expect(directive.findings[0]!.detail).toContain(`the step its proof takes from [k, Theorem 2] (${LEAF}) does not hold as the proof uses it: Theorem 2 needs $a$ bounded, which the proof never shows.`);
    // the pause is recorded against the host, where the repair will be confirmed
    expect(r.args.state.verify!.level_pause?.errors.map((e) => e.id)).toEqual(["lem:a"]);
    // the leaf's call is told to report the failure on the leaf, and is shown the host it is checked against
    const asked = r.prompts.get(LEAF)!;
    expect(asked.replace(/\s+/g, " ")).toContain("grade THIS node `error`");
    expect(asked).toContain("The result whose proof invokes a cited result you grade (`cited_in`), as it stands now (with the blocks a repair split off it), and the hypotheses and definitions each is stated under:\n- lem:a (lemma, \\label{lem:a}): The bound $a \\le b$ holds.\n");
    // counted once, on the host: in the review on file and in the run's ledger
    const review = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v15Review), "utf8")) as { nodes: V15NodeVerdict[] };
    expect(review.nodes.filter((n) => n.correctness !== "ok").map((n) => n.id)).toEqual(["lem:a"]);
    expect(JSON.stringify(r.args.state.verify)).not.toContain(`"${LEAF}"`);
  });

  it("the leaf's report is what stands: a host graded clean by its own call keeps the finding while the leaf reports it, and loses it when the leaf no longer does", async () => {
    const failed = (id: string): V15NodeVerdict => ({ ...ok(id), correctness: "error", detail: "Theorem 2 needs $a$ bounded, which the proof never shows.", witness: "an unbounded $a$", witness_regime: "in_scope", witness_instance: "a unbounded" });
    let reports = true;
    const r = await run((id) => (id === LEAF && reports ? failed(id) : ok(id)));
    const errors = async (): Promise<string[]> => (JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v15Review), "utf8")) as { nodes: V15NodeVerdict[] }).nodes.filter((n) => n.correctness === "error").map((n) => n.id);
    // no pause: the leaf and its host are graded in one pass, by different calls — the host's is silent
    const whole = { ...r.args, refereeFixAsYouGo: false };
    expect((await runStageV1_5(whole)).status).toBe("patch");
    expect(r.graded).toEqual([LEAF, "lem:a"]);
    expect(await errors()).toEqual(["lem:a"]);
    // nothing repaired: both are asked again (neither verdict is carried), and the finding stands
    r.graded.length = 0;
    expect((await runStageV1_5(whole)).status).toBe("patch");
    expect(r.graded).toEqual([LEAF, "lem:a"]);
    expect(await errors()).toEqual(["lem:a"]);
    const directive = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v1ReviseDirective), "utf8")) as { findings: Array<{ id: string }> };
    expect(directive.findings.map((f) => f.id)).toEqual(["lem:a"]);
    // the leaf's grader no longer reports it: the finding is gone
    reports = false;
    r.graded.length = 0;
    const res = await runStageV1_5(whole);
    expect(res.status, res.message).toBe("completed");
    expect(r.graded).toEqual([LEAF, "lem:a"]);
    expect(await errors()).toEqual([]);
  });

  it("neither verdict of a moved error is carried by a pause that answers another node", () => {
    const k = core();
    const bases = partitionByBasis(k, {}, null).bases;
    const b = (id: string): string => bases.get(id)!;
    const failed: V15NodeVerdict = { ...ok(LEAF), correctness: "error", detail: "Theorem 2 needs $a$ bounded.", witness: "an unbounded $a$", witness_regime: "in_scope", basis: b(LEAF) };
    const graded = [failed, { ...ok("lem:a"), basis: b("lem:a") }];
    // the host was graded clean and cached; a pause carries every verdict it does not answer
    const carry = { [LEAF]: b(LEAF), "lem:a": b("lem:a") };
    const next = (nodes: V15NodeVerdict[]): string[] => partitionByBasis(k, { "lem:a": b("lem:a") }, { verdict: "FAIL", summary: "", nodes } as V15Review, new Map(), carry).toGrade;
    const moved = errorsOnHosts(graded, inlineLeaves(k));
    expect(moved.map((n) => [n.id, n.correctness, n.basis])).toEqual([[LEAF, "ok", undefined], ["lem:a", "error", undefined]]);
    expect(next(moved)).toEqual(["lem:a", LEAF]);
    // (with its basis kept, the pause would carry the leaf's `ok`: its grader would not be asked again)
    expect(next(moved.map((n) => ({ ...n, basis: b(n.id) })))).not.toContain(LEAF);
  });

  it("a repair of the host re-opens the leaf: its basis reads the host's text, what the host is stated under and a repair's proof change", () => {
    const k = core();
    const first = partitionByBasis(k, {}, null);
    const confirmed = Object.fromEntries(first.bases);
    const prior = { verdict: "PASS", summary: "", nodes: [...first.bases].map(([id, basis]) => ({ ...ok(id), basis, basis_scheme: 5, basis_inputs: first.inputs.get(id) })) } as V15Review;
    const again = (c: Core): string[] => partitionByBasis(c, confirmed, prior).toGrade;
    expect(again(k)).not.toContain(LEAF);
    const host = (over: Record<string, unknown>, assumptions: unknown[] = []): Core =>
      ({ ...k, assumptions, statements: k.statements.map((st) => (st.id === "lem:a" ? { ...st, ...over } : st)) }) as unknown as Core;
    // the repair restates the host, adds a hypothesis to it, or changes its proof
    expect(again(host({ statement: "If $a$ is bounded, the bound $a \\le b$ holds." }))).toContain(LEAF);
    expect(again(host({ depends_on: [LEAF, "ass:bounded"] }, [{ id: "ass:bounded", condition: "$a$ is bounded.", used_by: ["lem:a"] }]))).toContain(LEAF);
    expect(again(host({ proof_tex: "[Proof change (minimal patch): $a$ is bounded by construction.]" }))).toContain(LEAF);
    // a result that is not its host does not
    expect(again({ ...core(true), statements: [...k.statements, { ...OTHER, statement: "The bound $d \\le 2e$ holds." }] } as unknown as Core)).not.toContain(LEAF);
  });

  it("with a drift in the same pass, the leaf's error reaches V1 on its host: never as a finding about the account of the citation", async () => {
    const r = await run(
      (id) =>
        id === LEAF
          ? { ...ok(id), correctness: "error", detail: "Theorem 2 needs $a$ bounded, which the proof never shows.", witness: "an unbounded $a$", witness_regime: "in_scope", witness_instance: "a unbounded" }
          : id === "lem:b" ? { ...ok(id), faithfulness: "drift", detail: "the environment bounds $d$ by $2e$." } : ok(id),
      true,
    );
    const res = await runStageV1_5(r.args);
    expect(res.status, res.message).toBe("revise");
    const directive = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v1ReviseDirective), "utf8")) as { findings: Array<{ id: string; axis: string; detail: string }> };
    expect(directive.findings.map((f) => [f.id, f.axis]).sort()).toEqual([["lem:a", "correctness (provisional)"], ["lem:b", "faithfulness"]]);
    expect(directive.findings.find((f) => f.id === "lem:a")!.detail).toContain(`the step its proof takes from [k, Theorem 2] (${LEAF}) does not hold as the proof uses it`);
    // the review on file holds the verdicts as routed: the leaf clean, the error on its host
    const review = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v15Review), "utf8")) as { nodes: V15NodeVerdict[] };
    expect(review.nodes.filter((n) => n.correctness === "error").map((n) => n.id)).toEqual(["lem:a"]);
  });

  it("an unclear on the leaf — the source shown lacks the result — stops for the source, naming the result and its file", async () => {
    const r = await run((id) => (id === LEAF ? { ...ok(id), correctness: "unclear", detail: "Theorem 2 is not in the source shown." } : ok(id)));
    const res = await runStageV1_5(r.args);
    expect(res.status).toBe("checkpoint");
    expect(res.message).toBe(
      `the referee could not check 1 cited result(s) against the source shown: ${LEAF} ([k, Theorem 2] → discovery/cited_sources/k.txt) — Theorem 2 is not in the source shown.. ` +
        "Put the exact statement of each result named, copied from the cited work, in its file, then --from-stage V1.5.",
    );
  });
});

describe("a finding on an inline cited leaf: what the audit of the routing found", () => {
  const FAILED = { correctness: "error" as const, detail: "Theorem 2 needs $a$ bounded, which the proof never shows.", witness: "an unbounded $a$", witness_regime: "in_scope" as const, witness_instance: "a unbounded" };
  const PATCH = { node: "lem:a", corrected_statement: null, ops: [], drops: null, adds: null, readings: null, umbrella: null, proof_note: "", owner_explanation: "x", consequence_of: null, corollaries: null };
  const file = (over: Record<string, unknown>) => ({ key_results: ["lem:a"], key_contribution: "the bound", patches: [], unfixable: [], ...over });
  const BLOCK = { title: "bound", statement: "If $a$ is bounded, the bound $a \\le b$ holds.", follows: "By \\cite[Theorem 2]{k} we get $a\\le c$, and $c \\le b$.", adds: [] };

  it("a leaf leaves the core with its host; one whose host is gone is no inline leaf, and its error stays where it is", () => {
    const built = buildCore(core(true), { patches: file({ key_results: ["lem:b"], unfixable: [{ node: "lem:a", reason: "no repair keeps the claim" }] }) as never }).core;
    expect(built.statements.map((st) => st.id)).toEqual(["lem:b"]);
    // (a core on file from before: the host removed, the leaf left behind)
    const dangling = { ...core(), statements: core().statements.filter((st) => st.id === LEAF) } as Core;
    expect(inlineLeaves(dangling).size).toBe(0);
    expect(errorsOnHosts([{ ...ok(LEAF), ...FAILED }], inlineLeaves(dangling)).map((n) => [n.id, n.correctness])).toEqual([[LEAF, "error"]]);
  });

  it("a host a repair split, or made an umbrella: the leaf is shown, and keyed on, the blocks that carry the hypothesis now", () => {
    const shown = (c: Core): string => compactCore(c, new Set([LEAF]), new Map(), { idsOnly: true });
    for (const patch of [
      { ...PATCH, umbrella: true, corollaries: [BLOCK, { title: "eq", statement: "$x=y$.", follows: "Trivial.", adds: [] }] },
      { ...PATCH, corrected_statement: "$x=y$.", proof_note: "the bound is split off.", corollaries: [BLOCK] },
    ]) {
      const built = buildCore(core(), { patches: file({ patches: [patch] }) as never }).core;
      const block = built.statements.find((st) => st.split_from === "lem:a" && st.statement === BLOCK.statement)!;
      expect(shown(built)).toContain(`: ${BLOCK.statement}\n`);
      // … and a change of the block re-opens the leaf
      const moved = { ...built, statements: built.statements.map((st) => (st.id === block.id ? { ...st, statement: "If $a$ is bounded by $1$, the bound $a \\le b$ holds." } : st)) } as Core;
      expect(basisOf(basisInputs(moved, LEAF))).not.toBe(basisOf(basisInputs(built, LEAF)));
    }
  });

  it("the owner's withdrawal of the finding on the host holds when the leaf reports it again", async () => {
    const r = await run((id) => (id === LEAF ? { ...ok(id), ...FAILED } : ok(id)));
    r.args.state.verify!.rejected_rewinds = [{ node: "lem:a", axis: "correctness", stage: "V1.5", route: "owner", detail: "d", reason: "$a$ is bounded by the standing convention", by: "owner", at: new Date().toISOString() }] as never;
    const res = await runStageV1_5(r.args);
    expect(res.status, res.message).toBe("completed");
    expect(r.args.state.verify!.level_pause).toBeUndefined();
    // recorded once, on the host
    expect(r.args.state.verify!.findings.filter((f) => f.detail.includes("withdrew")).map((f) => [f.node, f.kind])).toEqual([["lem:a", "note"]]);
  });

  it("a ruling the owner recorded on the leaf itself holds too", async () => {
    const r = await run((id) => (id === LEAF ? { ...ok(id), ...FAILED } : ok(id)));
    r.args.state.verify!.rejected_rewinds = [{ node: LEAF, axis: "correctness", stage: "V1.5", route: "owner", detail: "d", reason: "$a$ is bounded by the standing convention", by: "owner", at: new Date().toISOString() }] as never;
    const res = await runStageV1_5(r.args);
    expect(res.status, res.message).toBe("completed");
    expect(r.args.state.verify!.level_pause).toBeUndefined();
  });

  it("a leaf that another result still uses stays when its host leaves", () => {
    const k = { ...core(true), statements: core(true).statements.map((st) => (st.id === "lem:b" ? { ...st, depends_on: [LEAF] } : st)) } as Core;
    const built = buildCore(k, { patches: file({ key_results: ["lem:b"], unfixable: [{ node: "lem:a", reason: "no repair keeps the claim" }] }) as never }).core;
    expect(built.statements.map((st) => [st.id, st.depends_on])).toEqual([[LEAF, []], ["lem:b", [LEAF]]]);
  });

  const review = async (runDir: string): Promise<V15Review> => JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.v15Review), "utf8")) as V15Review;

  it("a `bookkeeping` verdict on file for a leaf, from before the rule, is neither carried nor kept: the leaf is graded afresh", async () => {
    const r = await run(ok);
    expect((await runStageV1_5(r.args)).status).toBe("completed");
    // the review as an earlier version left it: the leaf `bookkeeping`, cached on its basis
    const old = await review(r.runDir);
    await writeFile(path.join(r.runDir, VERIFY_FILES.v15Review), JSON.stringify({ ...old, nodes: old.nodes.map((n) => (n.id === LEAF ? { ...n, correctness: "bookkeeping", bookkeeping_assumption: { condition: "$a$ is bounded.", reason: "Theorem 2 needs it" } } : n)) }));
    expect(r.args.state.verify!.confirmed![LEAF]).toBeDefined();
    r.args.state.verify!.core_sha256 = null;
    r.graded.length = 0;
    const res = await runStageV1_5(r.args);
    expect(res.status, res.message).toBe("completed");
    expect(r.graded).toContain(LEAF);
    expect(r.prompts.get(LEAF)).not.toContain("Theorem 2 needs it");
    expect((await review(r.runDir)).nodes.find((n) => n.id === LEAF)).toMatchObject({ correctness: "ok", bookkeeping_assumption: null });
  });

  it("the host's appended condition survives a leaf's error that pauses the grading below the host", async () => {
    const condition = { condition: "$b$ is finite.", reason: "the last step divides by it" };
    let phase = 0;
    const r = await run((id) => (phase === 0 && id === "lem:a" ? { ...ok(id), correctness: "bookkeeping", bookkeeping_assumption: condition } : phase === 1 && id === LEAF ? { ...ok(id), ...FAILED } : ok(id)));
    expect((await runStageV1_5(r.args)).status).toBe("completed");
    // the leaf is re-opened and now reports: the grading pauses before the host is reached
    const first = await review(r.runDir);
    await writeFile(path.join(r.runDir, VERIFY_FILES.v15Review), JSON.stringify({ ...first, nodes: first.nodes.map((n) => (n.id === LEAF ? { ...n, basis: undefined } : n)) }));
    delete r.args.state.verify!.confirmed![LEAF];
    r.args.state.verify!.core_sha256 = null;
    phase = 1;
    r.graded.length = 0;
    expect((await runStageV1_5(r.args)).status).toBe("patch");
    expect(r.graded).toEqual([LEAF]);
    expect((await review(r.runDir)).nodes.find((n) => n.id === "lem:a")).toMatchObject({ correctness: "error", bookkeeping_assumption: condition });
    // the leaf no longer reports; the host's call says plain `ok`: the condition is kept
    phase = 2;
    const res = await runStageV1_5(r.args);
    expect(res.status, res.message).toBe("completed");
    expect(r.prompts.get("lem:a")).toContain("the last step divides by it");
    expect((await review(r.runDir)).nodes.find((n) => n.id === "lem:a")).toMatchObject({ correctness: "bookkeeping", bookkeeping_assumption: condition });
  });

  it("a leaf's error merged into a host graded only non-minimal or weakening is a refuting error: the repair is not one to accept", () => {
    const inline = inlineLeaves(core());
    for (const flag of ["minimality", "weakens_contribution"] as const) {
      const moved = errorsOnHosts([{ ...ok(LEAF), ...FAILED }, { ...ok("lem:a"), correctness: "error", detail: "the repair asks too much.", witness: "a weaker condition", [flag]: true }], inline);
      expect(moved[1]).toMatchObject({ id: "lem:a", correctness: "error", minimality: false, weakens_contribution: false, witness: "an unbounded $a$", witness_regime: "in_scope", witness_instance: "a unbounded" });
      expect(moved[1]!.detail).toMatch(/^the step its proof takes from \[k, Theorem 2\].* Also: the repair asks too much\.$/);
      const r = routeReview({ verdict: "FAIL", summary: "", nodes: moved } as V15Review, file({ patches: [{ ...PATCH, corrected_statement: "x" }] }) as never, new Set(["lem:a", LEAF]));
      expect(r.refuted.map((n) => n.id)).toEqual(["lem:a"]);
    }
    // the host's own refuting error keeps its witness
    expect(errorsOnHosts([{ ...ok(LEAF), ...FAILED }, { ...ok("lem:a"), correctness: "error", detail: "a term is dropped.", witness: "w", witness_regime: "in_scope", witness_instance: "i" }], inline)[1]).toMatchObject({ witness: "w", witness_instance: "i" });
  });

  it("a condition appended to the host stays across the move", () => {
    const condition = { condition: "$b$ is finite.", reason: "the last step divides by it" };
    const moved = errorsOnHosts([{ ...ok(LEAF), ...FAILED }, { ...ok("lem:a"), correctness: "bookkeeping", bookkeeping_assumption: condition }], inlineLeaves(core()));
    const prior = { verdict: "FAIL", summary: "", nodes: moved } as V15Review;
    expect(priorConditionLines(prior, ["lem:a"]).map((x) => x.node)).toEqual(["lem:a"]);
    expect(keepEarlierConditions([ok("lem:a")], prior)[0]).toMatchObject({ correctness: "bookkeeping", bookkeeping_assumption: condition });
    // (an exclusion of a degenerate witness not yet settled was never appended)
    expect(priorConditionLines({ ...prior, nodes: [{ ...ok("lem:a"), correctness: "error", witness: "w", witness_regime: "degenerate", bookkeeping_assumption: condition }] }, ["lem:a"])).toEqual([]);
  });

  it("a hypothesis of the cited result is never a condition appended to the leaf: `bookkeeping` and a degenerate witness on it break the contract", async () => {
    const condition = { condition: "$a$ is bounded.", reason: "Theorem 2 needs it" };
    for (const grade of [{ correctness: "bookkeeping" as const, bookkeeping_assumption: condition }, { ...FAILED, witness_regime: "degenerate" as const, bookkeeping_assumption: condition }]) {
      const r = await run((id) => (id === LEAF ? { ...ok(id), ...grade } : ok(id)));
      const res = await runStageV1_5(r.args);
      expect(res.status).toBe("checkpoint");
      expect(res.message).toContain(`node "${LEAF}" is a published result a proof invokes by citation: a hypothesis of the cited result that its host's statement and hypotheses do not give is an "error"`);
      const k = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
      expect(k.assumptions).toEqual([]);
    }
  });

  it("the repair that adds the cited result's hypothesis to a main result is the owner's to accept: a suggestion with a receipt, never applied", async () => {
    const repaired = "If $a$ is bounded, the bound $a \\le b$ holds.";
    const patches = file({ patches: [{ ...PATCH, corrected_statement: repaired, proof_note: "Theorem 2 of the cited work needs $a$ bounded.", owner_explanation: "The cited theorem needs $a$ bounded." }] });
    // pass 1: the leaf reports the unmet hypothesis; the fixer is sent to the host
    let repairedNow = false;
    const r = await run((id) =>
      !repairedNow
        ? id === LEAF ? { ...ok(id), ...FAILED } : ok(id)
        : id === "lem:a" ? { ...ok(id), correctness: "error", weakens_contribution: true, detail: "the repair holds but proves the bound for bounded $a$ only.", witness: "an unbounded $a$" } : ok(id),
    );
    expect((await runStageV1_5(r.args)).status).toBe("patch");
    // the fixer adds the hypothesis to the host's statement; the referee finds it holds and weakens the claim
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(patches, null, 2));
    await rebuildPatchedCore(r.runDir, { detectHandEdits: false });
    repairedNow = true;
    r.graded.length = 0;
    const res = await runStageV1_5(r.args);
    // the leaf is asked again, against the repaired host
    expect(r.graded).toContain(LEAF);
    expect(r.prompts.get(LEAF)).toContain(`- lem:a (lemma, \\label{lem:a}): ${repaired}`);
    expect(res.status, res.message).toBe("narrowed");
    expect(res.message).toContain("0 intermediate result(s) narrowed, 1 suggestion(s) on a main theorem (lem:a)");
    expect(r.args.state.verify!.weakening_repair).toMatchObject({ status: "pending", items: [{ node: "lem:a", printed: "The bound $a \\le b$ holds.", proposed: repaired }] });
    // nothing is applied: the repair is a suggestion on file, and the result (with the step it cites)
    // is out of the core until the owner rules
    const onFile = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.patches), "utf8")) as { patches: unknown[]; unfixable: Array<{ node: string }> };
    expect([onFile.patches.length, onFile.unfixable.map((u) => u.node)]).toEqual([0, ["lem:a"]]);
    const k = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
    expect(k.statements).toEqual([]);
  });
});
