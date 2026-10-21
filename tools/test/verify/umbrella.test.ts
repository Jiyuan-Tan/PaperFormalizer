/**
 * The UMBRELLA form of a split repair (owner decision 2026-10-06): a printed result that mixes several
 * conclusions, each under different assumptions, none its own main claim. Every conclusion is a
 * proposition block and the result only says that they hold — a fixed sentence, depending on its
 * blocks, with NO Lean declaration: the F stages do not see it (`formalizationView`), and it is
 * established exactly when all its blocks are (derived in the report and on the page). The patch
 * schema and its checks, the build and its invariant, the referee's routing, the F-stage view at each
 * gate, the report / MATCH.md / page / corrected paper, the model-free conversion (`--umbrella`) and
 * the prompts' contract. No model call.
 */
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { readFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterAll, describe, expect, it } from "vitest";
import { formalizationView, parseTypedCore, umbrellaIds } from "../../src/core/core_io.js";
import { runStructuralGate } from "../../src/core/gate.js";
import type { Core } from "../../src/core/schema.js";
import { coreDeltaLines } from "../../src/formalization/core_delta.js";
import { reconcileScaffoldTagsInMemory } from "../../src/formalization/f2_tag_reconcile.js";
import { runPlanGate } from "../../src/formalization/plan/plan_gate.js";
import { PlanSchema, type Plan } from "../../src/formalization/plan/schema.js";
import { buildGraphFromCorePlan } from "../../src/graph/from_core.js";
import { createVerifyInitialState } from "../../src/state.js";
import { runDetail } from "../../src/ui/run_model.js";
import { renderPaper } from "../../src/ui/tex_html.js";
import { applyEdits as applyTexEdits, planAnnotations, type AnnotationInput } from "../../src/verify/annotated_paper.js";
import { renderMatch } from "../../src/verify/bundle_match.js";
import { parseVerifyArgsForTest } from "../../src/verify/cli.js";
import { correctedTex } from "../../src/verify/corrected_tex.js";
import { UMBRELLA_PROOF, UMBRELLA_STATEMENT, buildCore, checkCoreInvariants, nodeFingerprint, splitCorollaryId, splitKinds, umbrellaBlocks, umbrellaRange, umbrellaSentence, type PatchFileLike } from "../../src/verify/core_graph.js";
import { convertToUmbrella, movePlanEntries, parseUmbrella } from "../../src/verify/owner_rulings.js";
import { PROOF_UNCHANGED } from "../../src/verify/ops.js";
import { PATCH_REPLY_JSON_SCHEMA, PatchFileSchema, canonicalUmbrellas, findingPatch, materializeReply, umbrellaConversion, validatePatchFile, type PatchFile } from "../../src/verify/patches.js";
import { buildReport, deriveUmbrella, type ReportRow, type VerifyReportJson } from "../../src/verify/report.js";
import { formalStatus, renderPlainSections, resultNames, umbrellaWords } from "../../src/verify/report_plain.js";
import { restatementViolations, withdrawnRepairBlock } from "../../src/verify/stage_v1.js";
import { noteBasis, routeReview, splitObjection, splitRequests } from "../../src/verify/stage_v1_5.js";
import { VERIFY_FILES, type V15NodeVerdict, type V15Review } from "../../src/verify/types.js";
import { convertWeakeningPatches, withdrawnRepair } from "../../src/verify/weakening.js";

const PRINTED = "Under A the first bound holds; under B the second bound holds; and the third bound holds.";
const loc = (from: number, env: string, label: string) => ({ file: "main.tex", from, to: from + 2, env, label });
/** thm:main (a summary) rests on two lemmas and three conditions, one only it uses; thm:use uses it. */
function core(): Core {
  return {
    qid: "umbrella_paper",
    symbols: [],
    assumptions: [
      { id: "ass:a", condition: "condition A", novel: { flag: true, justification: "Assumption 1" } },
      { id: "ass:b", condition: "condition B", novel: { flag: true, justification: "Assumption 2" } },
      { id: "ass:only", condition: "a condition only the summary names", novel: { flag: true, justification: "Assumption 3" } },
    ],
    definitions: [],
    statements: [
      { id: "lem:one", kind: "lemma", statement: "the first bound", depends_on: ["ass:a"], status: "to-prove", tex_locator: loc(3, "lemma", "lem:one") },
      { id: "lem:two", kind: "lemma", statement: "the second bound", depends_on: ["ass:b"], status: "to-prove", tex_locator: loc(6, "lemma", "lem:two") },
      { id: "thm:main", kind: "theorem", statement: PRINTED, depends_on: ["ass:a", "ass:b", "ass:only", "lem:one", "lem:two"], status: "to-prove", tex_locator: loc(9, "theorem", "thm:main") },
      { id: "thm:use", kind: "theorem", statement: "the interval covers", depends_on: ["thm:main"], status: "to-prove", tex_locator: loc(12, "theorem", "thm:use") },
    ],
    target_estimand: "t",
    bibliography: [],
  } as unknown as Core;
}
const P1 = { title: "the first bound", statement: "Under condition A the first bound holds.", follows: "This is Lemma~\\ref{lem:one}.", adds: ["ass:a"] };
const P2 = { title: "the second bound", statement: "Under condition B the second bound holds.", follows: "This is Lemma~\\ref{lem:two}.", adds: ["ass:b"] };
const [ID1, ID2] = [P1, P2].map((p) => splitCorollaryId("thm:main", p.statement)) as [string, string];
const THIRD = "The third bound holds.";
const THIRD_PROOF = "Combine Lemma~\\ref{lem:one} with the triangle inequality.";
const file = (patch: Record<string, unknown>, over: Record<string, unknown> = {}): PatchFile => canonicalUmbrellas(PatchFileSchema.parse({ key_results: ["thm:main"], key_contribution: "the three bounds", patches: [patch], unfixable: [], ...over }));
const like = (f: PatchFile): PatchFileLike => f as unknown as PatchFileLike;
/** The fixer's umbrella: every conclusion a block, no ops. */
const umbrella = (over: Record<string, unknown> = {}) => ({ node: "thm:main", corrected_statement: null, ops: [], proof_note: "x", umbrella: true, corollaries: [P1, P2], ...over });
/** The existing split form: the statement keeps a fragment, the rest are proposition blocks. */
const split = (over: Record<string, unknown> = {}) => ({ node: "thm:main", corrected_statement: THIRD, ops: [{ op: "replace" as const, unit: "thm:main/1/1", tex: THIRD }], drops: ["ass:b", "ass:only"], proof_note: THIRD_PROOF, readings: ["a bound is uniform"], corollaries: [P1, P2], ...over });
const built = (f: PatchFile): Core => parseTypedCore(JSON.stringify(buildCore(core(), { patches: like(f) }).core), "built");
const st = (c: Core, id: string) => c.statements.find((s) => s.id === id)!;
const grade = (id: string, over: Partial<V15NodeVerdict> = {}): V15NodeVerdict => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "d", witness: null, bookkeeping_assumption: null, reading: null, ...over });

const tmp: string[] = [];
afterAll(() => {
  for (const d of tmp) rmSync(d, { recursive: true, force: true });
});

describe("the sentence is generated from the blocks' names, never stored with them", () => {
  it("a run of numbers is a range, two are joined, others listed; blocks without numbers get the fixed sentence", () => {
    const names = (n: number): string[] => Array.from({ length: n }, (_, i) => `Proposition 5.2.${i + 1}`);
    expect(umbrellaSentence(names(6))).toBe("Propositions 5.2.1–5.2.6 hold, each under the conditions stated in it.");
    expect(umbrellaSentence(names(6), "--")).toBe("Propositions 5.2.1--5.2.6 hold, each under the conditions stated in it.");
    expect(umbrellaSentence(names(2))).toBe("Propositions 5.2.1 and 5.2.2 hold, each under the conditions stated in it.");
    expect(umbrellaSentence(["Proposition B.8.1", "Proposition B.8.3", "Proposition B.8.4"])).toBe("Propositions B.8.1, B.8.3 and B.8.4 hold, each under the conditions stated in it.");
    expect(umbrellaSentence(names(1))).toBe("Proposition 5.2.1 holds under the conditions stated in it.");
    expect(umbrellaRange(names(3))).toBe("Propositions 5.2.1–5.2.3");
    for (const none of [[], ["Proposition 1 of Theorem (bounds)", "Proposition 2 of Theorem (bounds)"], ["Proposition 5.2.1", ""]]) {
      expect(umbrellaSentence(none)).toBe(UMBRELLA_STATEMENT);
      expect(umbrellaRange(none)).toBeNull();
    }
    // the core's text names no block: it is hashed
    expect(UMBRELLA_STATEMENT).not.toMatch(/\d/u);
  });
});

describe("the patch file: what an umbrella must satisfy", () => {
  type Schema = { properties: { patches: { items: { required: string[]; properties: Record<string, unknown> } }; unfixable: { items: { properties: { suggested_repair: { anyOf: Array<{ required?: string[]; properties?: Record<string, unknown> }> } } } } } };
  it("the reply schema carries `umbrella` (true or null) on a patch and on a suggested repair; null reads as absent", () => {
    const s = PATCH_REPLY_JSON_SCHEMA as unknown as Schema;
    expect(s.properties.patches.items.required).toContain("umbrella");
    expect(s.properties.patches.items.properties.umbrella).toEqual({ anyOf: [{ type: "boolean" }, { type: "null" }] });
    expect(s.properties.unfixable.items.properties.suggested_repair.anyOf[0]!.required).toContain("umbrella");
    const parsed = PatchFileSchema.parse({ patches: [{ ...split(), umbrella: null }, { ...split(), node: "thm:use", umbrella: false }] });
    expect(parsed.patches.map((p) => "umbrella" in p && p.umbrella !== undefined)).toEqual([false, false]);
  });

  it("the fixer writes no sentence: the reply's umbrella takes the pipeline's texts, a proof note of the fixer's included", () => {
    const { raw, violations } = materializeReply({ patches: [{ node: "thm:main", ops: [], proof_note: null, umbrella: true, corollaries: [P1, P2] }], unfixable: [{ node: "thm:use", suggested_repair: { ops: [], proof_note: "mine", umbrella: true, corollaries: [P1, P2] }, owner_explanation: { gives_up: "the third bound" } }] }, () => ({ units: [], passage: null }) as never, () => false);
    expect(violations).toEqual([]);
    const r = raw as { patches: Array<Record<string, unknown>>; unfixable: Array<{ suggested_repair: Record<string, unknown> }> };
    expect(r.patches[0]).toMatchObject({ corrected_statement: UMBRELLA_STATEMENT, proof_note: UMBRELLA_PROOF });
    expect(r.unfixable[0]!.suggested_repair).toMatchObject({ corrected_statement: UMBRELLA_STATEMENT, proof_note: UMBRELLA_PROOF, given_up: "the third bound" });
    // a stored file is read with them whatever it holds
    expect(file(umbrella({ corrected_statement: "anything", proof_note: "anything" })).patches[0]).toMatchObject({ corrected_statement: UMBRELLA_STATEMENT, proof_note: UMBRELLA_PROOF });
    // a flag without blocks is no umbrella: its texts stand (and the check below refuses it)
    expect(file(umbrella({ corrected_statement: "kept", corollaries: null })).patches[0]!.corrected_statement).toBe("kept");
    expect(findingPatch(file(umbrella()).patches[0]!, true)).toMatchObject({ umbrella: true, corollaries: [ID1, ID2] });
    expect(findingPatch(file(split()).patches[0]!, true).umbrella).toBeUndefined();
  });

  it("refused, each with a message the fixer can act on: fewer than two blocks, ops, hypotheses of its own, a block citing the umbrella or a result resting on it", () => {
    const bad = (patch: Record<string, unknown>): string[] => validatePatchFile(core(), file(patch), ["thm:main"]);
    expect(bad(umbrella())).toEqual([]);
    expect(bad(umbrella({ corollaries: [P1] })).join("\n")).toMatch(/is an umbrella \(`umbrella: true`\) but gives 1 block\(s\).*at least two/u);
    expect(bad(umbrella({ corollaries: null })).join("\n")).toMatch(/gives 0 block\(s\)/u);
    expect(bad(umbrella({ ops: [{ op: "replace", unit: "thm:main/1/1", tex: THIRD }] })).join("\n")).toMatch(/gives `ops`: an umbrella has no statement or proof of its own/u);
    expect(bad(umbrella({ adds: ["ass:a"] })).join("\n")).toMatch(/gives `drops` \/ `adds`: an umbrella uses no hypothesis itself/u);
    const citing = { ...P2, follows: "By Theorem~\\ref{thm:main} and Lemma~\\ref{lem:two}." };
    expect(bad(umbrella({ corollaries: [P1, citing] })).join("\n")).toMatch(/corollary 2 of the patch for "thm:main" cites "thm:main" \(\\ref\{thm:main\}\) in `follows`, but "thm:main" is an umbrella.*no block's proof may cite it/u);
    const circular = { ...P2, follows: "By Theorem~\\ref{thm:use}." };
    expect(bad(umbrella({ corollaries: [P1, circular] })).join("\n")).toMatch(/cites "thm:use" \(\\ref\{thm:use\}\), which rests on "thm:main" itself: under an umbrella that is circular/u);
    // the same proof is a legitimate corollary of a result that keeps a claim of its own
    expect(bad(split({ corollaries: [P1, citing] }))).toEqual([]);
  });

  it("an umbrella's sentence is not checked as a restatement of the printed statement; a weakening grade and a withdrawn repair keep the flag", () => {
    expect(restatementViolations(core(), file(umbrella()), null)).toEqual([]);
    const sug = convertWeakeningPatches(file(umbrella()), [{ id: "thm:main", detail: "the third bound is in no block" }]);
    expect(sug.unfixable[0]!.suggested_repair).toMatchObject({ umbrella: true, corrected_statement: UMBRELLA_STATEMENT, corollaries: [P1, P2] });
    expect(restatementViolations(core(), sug, null)).toEqual([]);
    expect(withdrawnRepair(sug, "thm:main")).toMatchObject({ umbrella: true });
    const shown = withdrawnRepairBlock([{ id: "thm:main", withdrawn_repair: withdrawnRepair(sug, "thm:main") }]);
    expect(shown).toContain("umbrella: true");
    expect(shown).not.toContain(UMBRELLA_STATEMENT);
    // applied, the suggestion builds the same umbrella
    expect(st(built(PatchFileSchema.parse({ ...sug, patches: [{ node: "thm:main", ...sug.unfixable[0]!.suggested_repair }], unfixable: [] })), "thm:main").umbrella).toBe(true);
  });
});

describe("the build: the result keeps its place and rests on its blocks", () => {
  it("id, kind, label and locator stay; the text is the fixed sentence; it depends on its blocks and nothing else of the paper; every block is a proposition; a condition only it named leaves the core", () => {
    const c = built(file(umbrella()));
    const u = st(c, "thm:main");
    expect(u).toMatchObject({ id: "thm:main", kind: "theorem", umbrella: true, statement: UMBRELLA_STATEMENT, proof_tex: UMBRELLA_PROOF, depends_on: [ID1, ID2], status: "to-prove", tex_locator: loc(9, "theorem", "thm:main") });
    expect(c.statements.map((s) => s.id)).toEqual(["lem:one", "lem:two", "thm:main", "thm:use", ID1, ID2]);
    expect(st(c, ID1)).toMatchObject({ split_from: "thm:main", depends_on: ["ass:a", "lem:one"], proof_tex: P1.follows, kind: "theorem" });
    expect(st(c, ID2).depends_on).toEqual(["ass:b", "lem:two"]);
    expect([...splitKinds(c).values()]).toEqual(["proposition", "proposition"]);
    expect(umbrellaBlocks(c)).toEqual(new Map([["thm:main", [ID1, ID2]]]));
    // what used the printed result uses it and its blocks
    expect(st(c, "thm:use").depends_on).toEqual(["thm:main", ID1, ID2]);
    expect(c.assumptions.map((a) => a.id)).toEqual(["ass:a", "ass:b"]);
    expect(checkCoreInvariants(c)).toEqual([]);
    expect(runStructuralGate(c, { allowBookkeeping: true, verbatim: true }).violations).toEqual([]);
  });

  it("a reading the repair states binds the umbrella and every block; a parent without a label still has proposition blocks (no edge back to it)", () => {
    const c = built(file(umbrella({ readings: ["a bound is uniform"] })));
    const pin = c.assumptions.find((a) => a.id.startsWith("ass:pin-fix-"))!;
    expect(pin.used_by).toEqual([ID1, ID2, "thm:main"].sort());
    const bare = core();
    delete (bare.statements[2] as { tex_locator?: unknown }).tex_locator;
    const d = buildCore(bare, { patches: like(file(umbrella())) }).core;
    expect([...splitKinds(d).values()]).toEqual(["proposition", "proposition"]);
    expect(st(d, ID1).depends_on).not.toContain("thm:main");
    expect(checkCoreInvariants(d)).toEqual([]);
  });

  it("a block that would rest on the umbrella never closes a cycle in the build, and the invariant names one in a core that has it", () => {
    const circular = { ...P2, follows: "By Theorem~\\ref{thm:use}." };
    const c = built(file(umbrella({ corollaries: [P1, circular] })));
    const id = splitCorollaryId("thm:main", circular.statement);
    expect(st(c, id).depends_on).toEqual(["ass:b"]);
    expect(checkCoreInvariants(c)).toEqual([]);
    const cyclic = structuredClone(built(file(umbrella())));
    st(cyclic, ID1).depends_on.push("thm:use");
    expect(checkCoreInvariants(cyclic).join("\n")).toContain(`block "${ID1}" rests on its umbrella "thm:main" (a cycle)`);
    const lone = structuredClone(built(file(umbrella())));
    lone.statements = lone.statements.filter((s) => s.id !== ID2).map((s) => ({ ...s, depends_on: s.depends_on.filter((d) => d !== ID2) }));
    expect(checkCoreInvariants(lone).join("\n")).toContain('umbrella "thm:main" has 1 block(s): it needs at least two');
  });

  it("the umbrella's verdict basis follows its blocks' statements and verdicts: a reworded block proof re-grades that block alone, a reworded block statement the umbrella too", () => {
    const a = built(file(umbrella()));
    const b = built(file(umbrella({ corollaries: [P1, { ...P2, follows: "This is Lemma~\\ref{lem:two}, applied once." }] })));
    expect(nodeFingerprint(a, ID2)).not.toBe(nodeFingerprint(b, ID2));
    expect(nodeFingerprint(a, "thm:main")).toBe(nodeFingerprint(b, "thm:main"));
    expect(nodeFingerprint(a, ID1)).toBe(nodeFingerprint(b, ID1));
    const c = built(file(umbrella({ corollaries: [P1, { ...P2, statement: `${P2.statement} Moreover the bound is sharp.` }] })));
    expect(nodeFingerprint(a, "thm:main")).not.toBe(nodeFingerprint(c, "thm:main"));
    // …and the parent's own grading material says it is an umbrella over these blocks
    expect(noteBasis(file(umbrella())).get("thm:main")).toMatch(/corollaries: .*\numbrella$/u);
    expect(noteBasis(file(split())).get("thm:main")).not.toContain("umbrella");
  });
});

describe("V1.5: the form of a repair, both ways, by the remark channel alone", () => {
  const results = new Set(["lem:one", "lem:two", "thm:main", "thm:use", ID1, ID2]);
  const review = (over: Partial<V15NodeVerdict>): V15Review => ({ verdict: "PASS", summary: "s", nodes: [grade("thm:main", over), grade(ID1), grade(ID2)], patch_review: { key_results_ok: true, detail: "" } });

  it("a remark on a confirmed umbrella is routed like one on a split parent: asked once, held while awaiting the owner, a note for the fixer", () => {
    const f = file(umbrella());
    const r = routeReview(review({ split: { why: "the third bound is the theorem's claim; the other two are its cases" } }), f, results);
    expect(r.splitRemarks.map((n) => n.id)).toEqual(["thm:main"]);
    expect(splitRequests(r, f, new Set()).ask.map((n) => n.id)).toEqual(["thm:main"]);
    expect(splitRequests(r, f, new Set(["thm:main"])).ask).toEqual([]);
    expect(splitRequests(r, f, new Set(), new Set(["thm:main"])).ask).toEqual([]);
    // an error on the umbrella is an error, not a remark
    expect(routeReview(review({ correctness: "error", split: { why: "x" } }), f, results).splitRemarks).toEqual([]);
  });

  it("the request says which way: restore the main claim of an umbrella; separate a statement — into an umbrella when nothing in it is its own main claim", () => {
    const n = grade("thm:main", { split: { why: "W." } });
    const restore = splitObjection(n, true);
    expect(restore).toMatchObject({ id: "thm:main", axis: "split", note: true, witness: null });
    expect(restore.detail).toContain("it states the result as an umbrella (`umbrella: true`) although the printed statement has a main claim of its own: W.");
    expect(restore.detail).toContain("`umbrella` null");
    expect(restore.detail).toContain("if nothing in the statement is its own main claim after all, return the entry as it is");
    const separate = splitObjection(n);
    expect(separate.detail).toContain("its corrected statement is several results");
    expect(separate.detail).toContain("make it an umbrella instead: every conclusion a block, `umbrella: true`, no ops");
  });
});

describe("the F stages: an umbrella is no formalization target", () => {
  const accepted = (): Core => built(file(umbrella()));
  const node = (lean_kind: string, lean_name: string, extra = {}) => ({ lean_kind, lean_name, disposition: "define-local", reuse: null, modules: [], target_file: "Main.lean", ...extra });
  const plan = (extra: Record<string, unknown> = {}): Plan =>
    PlanSchema.parse({
      qid: "umbrella_paper",
      env: [{ id: "S1", world: "local", binds_symbols: [], binds_sampling_model: true, disposition: "define-local" }],
      nodes: {
        "ass:a": node("assumption", "CondA"), "ass:b": node("assumption", "CondB"),
        "lem:one": node("lemma", "first_bound", { hyps: ["ass:a"] }), "lem:two": node("lemma", "second_bound", { hyps: ["ass:b"] }),
        "thm:use": node("theorem", "covers"),
        [ID1]: node("theorem", "first_bound_prop", { hyps: ["ass:a"] }), [ID2]: node("theorem", "second_bound_prop", { hyps: ["ass:b"] }),
        ...extra,
      },
      citations: [],
    });

  it("the view drops the umbrella and every edge to it, and is the same object for a core without one", () => {
    const c = accepted();
    const v = formalizationView(c);
    expect(umbrellaIds(c)).toEqual(["thm:main"]);
    expect(v.statements.map((s) => s.id)).toEqual(["lem:one", "lem:two", "thm:use", ID1, ID2]);
    expect(st(v, "thm:use").depends_on).toEqual([ID1, ID2]);
    expect(st(v, ID1)).toBe(st(c, ID1));
    expect(formalizationView(v)).toBe(v);
    const plain = core();
    expect(formalizationView(plain)).toBe(plain);
    expect(runStructuralGate(v, { allowBookkeeping: true, verbatim: true }).violations).toEqual([]);
  });

  it("F1 / F1.5 / F2 plan gate: no plan entry is asked for it, and one that names it is refused as naming no core node", () => {
    const v = formalizationView(accepted());
    const about = (p: Plan) => runPlanGate(p, v).violations.filter((x) => x.where.includes("thm:main") || x.message.includes("thm:main"));
    expect(about(plan())).toEqual([]);
    expect(runPlanGate(plan(), v).violations.filter((x) => x.code === "P1")).toEqual([]);
    const planned = about(plan({ "thm:main": node("theorem", "bounds") }));
    expect(planned.map((x) => x.code)).toContain("P1");
    // without the view the gate would demand a declaration it cannot have
    expect(runPlanGate(plan(), accepted()).violations.filter((x) => x.code === "P1").map((x) => x.where).join(" ")).toContain("thm:main");
  });

  it("F2 with tags: a scaffold without a tag for it passes P7, and a tag naming it is an orphan", () => {
    const v = formalizationView(accepted());
    const tags = (ids: string[]) => ({ nodes: new Set(ids), envs: new Set(["S1"]) });
    const all = ["ass:a", "ass:b", "lem:one", "lem:two", "thm:use", ID1, ID2];
    const p7 = (ids: string[]) => runPlanGate(plan(), v, { leanTags: tags(ids) as never }).violations.filter((x) => x.code === "P7");
    expect(p7(all)).toEqual([]);
    expect(p7([...all, "thm:main"]).map((x) => `${x.where} ${x.message}`).join("\n")).toContain("thm:main");
  });

  it("the graph: no node and no edge for it, and its alias slot is kept — no later result is renumbered", () => {
    const g = buildGraphFromCorePlan(accepted(), null);
    expect(g.nodes.some((n) => n.id === "thm:main")).toBe(false);
    expect(g.edges.some((e) => e.from === "thm:main" || e.to === "thm:main")).toBe(false);
    const alias = (graph: typeof g, id: string) => graph.nodes.find((n) => n.id === id)?.obj_id;
    const before = buildGraphFromCorePlan(built(file(split())), null);
    expect(alias(before, "thm:main")).toBe("T-3");
    for (const id of ["lem:one", "lem:two", "thm:use", ID1, ID2]) expect(alias(g, id)).toBe(alias(before, id));
    expect(alias(g, "thm:use")).toBe("T-4");
    // the same graph from the view alone would shift them: the builder takes the accepted core
    expect(alias(buildGraphFromCorePlan(formalizationView(accepted()), null), "thm:use")).toBe("T-3");
    // every theorem node left is one the proof loop can close
    expect(g.nodes.filter((n) => n.kind === "theorem").map((n) => n.id)).toEqual(["lem:one", "lem:two", "thm:use", ID1, ID2]);
  });

  it("F1's re-plan is told the result left the formalization: a removed statement in WHAT CHANGED", () => {
    const lines = coreDeltaLines(formalizationView(built(file(split()))), formalizationView(accepted())).join("\n");
    expect(lines).toContain("thm:main");
    expect(coreDeltaLines(formalizationView(accepted()), formalizationView(accepted()))).toEqual([]);
  });

  it("F2 tag reconciliation: a declaration still tagged with the umbrella's id is retagged to the block that takes its Lean name; with no taker it is removed, or reported when still used", () => {
    const v = formalizationView(accepted());
    const lean = (extra = "") => `-- @node: thm:main\ntheorem bounds : True := by\n  trivial\n\n-- @node: ${ID2}\ntheorem second_bound_prop : True := by\n  trivial\n${extra}`;
    const run = (p: Plan, text: string, retired = new Set(["thm:main"])) => reconcileScaffoldTagsInMemory({ sources: [{ file: "Main.lean", text }], plan: p, core: v, retired });
    // the conversion moved the plan entry: the block is planned under the old Lean name
    const taken = run(plan({ [ID1]: node("theorem", "bounds", { hyps: ["ass:a"] }) }), lean());
    expect(taken.result.retagged).toMatchObject([{ from: "thm:main", to: ID1, basis: "lean-name" }]);
    expect(taken.changed[0]!.text).toContain(`-- @node: ${ID1}\ntheorem bounds : True`);
    // no block takes the name: the stale declaration goes (unreferenced), and the block is new
    const dropped = run(plan(), lean());
    expect(dropped.result.removed.map((r) => r.id)).toEqual(["thm:main"]);
    expect(dropped.changed[0]!.text).not.toContain("theorem bounds");
    expect(dropped.result.newNodes.map((n) => n.id)).toContain(ID1);
    const used = run(plan(), lean("\ntheorem later : True := bounds\n"));
    expect(used.result.staleReferenced.map((r) => r.id)).toEqual(["thm:main"]);
    // an id that is not retired is none of the reconciliation's business (P7 reports it)
    expect(run(plan(), lean(), new Set()).result).toMatchObject({ retagged: [], removed: [], staleReferenced: [] });
  });
});

describe("the report: derived from the blocks, never better than the worst of them", () => {
  const row = (over: Partial<ReportRow>): ReportRow =>
    ({ env_id: "thm:main", label: null, kind: "theorem", title: null, locator: "main.tex:9-11", node_id: "thm:main", statement: PRINTED, appended_hypotheses: null, bucket: "verified", lean: null, crosswalk_verdict: null, bookkeeping: [], change: null, cited_hypotheses: [], assumed_substrate: [], added_premises: [], findings: [], axioms: null, v1_5: null, inherits_refutation_from: [], ...over }) as ReportRow;
  const block = (k: number, over: Partial<ReportRow> = {}): ReportRow => row({ node_id: `thm:cor-fix-${k}`, split_from: "thm:main", split_kind: "proposition", statement: `bound ${k}`, lean: { file: "Main.lean", decl: `P.b${k}`, line: k }, axioms: { axioms: ["propext"], clean: true }, ...over });
  const repaired = { node: "thm:main", stage: "V1.5", kind: "refuted", detail: "the second bound fails without B", witness: "w", at: "t", patch: { corrected_statement: UMBRELLA_STATEMENT, proof_note: UMBRELLA_PROOF, confirmed: true, umbrella: true } };
  const derive = (blocks: ReportRow[], over: Partial<ReportRow> = {}, earlyStop = false): ReportRow => {
    const u = row({ label: "thm:main", umbrella: true, bucket: "unresolved", ...over });
    deriveUmbrella(u, blocks, { earlyStop });
    return u;
  };

  it("verified exactly when every block is; conditional / bookkeeping / unresolved / not checked as its worst block; a refuted block or no block leaves it unresolved", () => {
    expect(derive([block(1), block(2)]).bucket).toBe("verified");
    expect(derive([block(1), block(2, { bucket: "verified_with_bookkeeping" })]).bucket).toBe("verified_with_bookkeeping");
    expect(derive([block(1, { bucket: "verified_with_bookkeeping" }), block(2, { bucket: "conditional" })]).bucket).toBe("conditional");
    expect(derive([block(1), block(2, { bucket: "unresolved" })]).bucket).toBe("unresolved");
    expect(derive([block(1), block(2, { bucket: "refuted" })]).bucket).toBe("unresolved");
    expect(derive([block(1, { bucket: "not_checked" }), block(2, { bucket: "not_checked" })], {}, true).bucket).toBe("not_checked");
    expect(derive([]).bucket).toBe("unresolved");
    expect(derive([block(1), block(2)], { findings: [{ node: "thm:main", stage: "F4", kind: "unresolved", detail: "d", witness: null, at: "t" }] as never }).bucket).toBe("unresolved");
  });

  it("a repaired umbrella is `repaired` only once every block is certified; an error with no confirmed repair stays refuted", () => {
    const f = [repaired] as never;
    expect(derive([block(1), block(2)], { findings: f }).bucket).toBe("repaired");
    expect(derive([block(1), block(2, { bucket: "conditional" })], { findings: f }).bucket).toBe("repaired");
    expect(derive([block(1), block(2, { bucket: "unresolved" })], { findings: f }).bucket).toBe("unresolved");
    expect(derive([block(1, { bucket: "not_checked" }), block(2, { bucket: "not_checked" })], { findings: f }, true).bucket).toBe("repaired");
    expect(derive([block(1), block(2)], { findings: [{ ...repaired, patch: { ...repaired.patch, confirmed: false } }] as never }).bucket).toBe("refuted");
  });

  it("its axioms are the union of its blocks', clean only when every block was audited clean", () => {
    expect(derive([block(1), block(2, { axioms: { axioms: ["Classical.choice", "propext"], clean: true } })]).axioms).toEqual({ axioms: ["Classical.choice", "propext"], clean: true });
    expect(derive([block(1), block(2, { axioms: { axioms: ["sorryAx"], clean: false } })]).axioms).toMatchObject({ axioms: ["propext", "sorryAx"], clean: false });
    expect(derive([block(1), block(2, { axioms: null })]).axioms).toBeNull();
  });

  const envs = { main_file: "main.tex", files: ["main.tex"], newtheorem: {}, bibliography: [], envs: core().statements.map((s) => ({ id: s.id, kind: s.kind, envName: s.kind, label: s.id, title: null, body: s.statement, proof: null, proofLines: null, section: null, lines: { file: "main.tex", from: s.tex_locator!.from, to: s.tex_locator!.to }, refs: [] })) };
  const report = (c: Core): VerifyReportJson => {
    const { json } = buildReport({
      qid: "umbrella_paper", envs: envs as never, scope: envs.envs.map((e) => e.id), core: c, transcribed: core(), review: null, findings: [repaired] as never,
      addedAssumptions: [], crosswalk: null, graph: null, lean: null, warnings: { lint: [], parser: [] }, flags: {}, stageCompleted: "V1.5", earlyStop: true, sourceSha256: "h",
      inputs: { v1_5_review: "x", crosswalk_full: "x", graph_json: "x", v1_scope: "x", lean_evidence: "x" },
    });
    json.names = resultNames(json.results, (l) => ({ "thm:main": "5.2", "thm:use": "5.3", "lem:one": "1", "lem:two": "2" })[l]);
    return json;
  };

  it("`buildReport`: the umbrella's row is at its environment, flagged, with no declaration, its blocks' rows after it; it lists no dropped condition", () => {
    const json = report(built(file(umbrella())));
    expect(json.results.map((r) => r.node_id)).toEqual(["lem:one", "lem:two", "thm:main", ID1, ID2, "thm:use"]);
    const u = json.results.find((r) => r.node_id === "thm:main")!;
    expect(u).toMatchObject({ umbrella: true, lean: null, label: "thm:main", bucket: "repaired", statement: PRINTED });
    expect(u.change).toMatchObject({ corrected: UMBRELLA_STATEMENT, dropped_dependencies: [], proof_change: null });
    expect(json.results.filter((r) => r.split_from === "thm:main").map((r) => r.split_kind)).toEqual(["proposition", "proposition"]);
    expect(json.results.find((r) => r.node_id === "lem:one")!.umbrella).toBeUndefined();
    expect(json.names).toMatchObject({ "thm:main": "Theorem 5.2", [ID1]: "Proposition 5.2.1", [ID2]: "Proposition 5.2.2" });
    expect(umbrellaWords(u, json.results, json.names!)).toEqual({ range: "Propositions 5.2.1 and 5.2.2", sentence: "Propositions 5.2.1 and 5.2.2 hold, each under the conditions stated in it." });
  });

  it("the plain report: \"Theorem 5.2 — established as Propositions …\", the sentence as its correction, each proposition with its own formal check, no proof of its own", () => {
    const text = renderPlainSections(report(built(file(umbrella())))).join("\n");
    expect(text).toContain("### Theorem 5.2 — established as Propositions 5.2.1 and 5.2.2");
    expect(text).toContain("- **Correction.** Propositions 5.2.1 and 5.2.2 hold, each under the conditions stated in it.");
    expect(text).toContain("the correction states every one as a proposition of its own (Propositions 5.2.1 and 5.2.2). The result is established exactly when all of them are.");
    expect(text).toContain(`  - **Proposition 5.2.1.** ${P1.statement} Formal check:`);
    expect(text).not.toContain(UMBRELLA_PROOF);
    expect(text).not.toContain(UMBRELLA_STATEMENT);
  });

  it("the words for what Lean establishes: through its propositions when all are proved, one of them open otherwise", () => {
    const u = derive([block(1), block(2)], { findings: [repaired] as never });
    expect(formalStatus(u, false)).toEqual({ status: "proved", words: "established through its propositions, each proved in Lean (it has no Lean declaration of its own)" });
    const open = derive([block(1), block(2, { bucket: "unresolved" })], { findings: [repaired] as never });
    expect(formalStatus(open, false)).toMatchObject({ status: "not certified", words: expect.stringContaining("the Lean formalization of one of its propositions did not close") });
  });

  it("MATCH.md lists it with its blocks: the sentence, no declaration of its own, the blocks' declarations and their axioms together", () => {
    const rows = [row({ label: "thm:main", umbrella: true, bucket: "unresolved", change: { printed: PRINTED, corrected: UMBRELLA_STATEMENT, referee_conditions: [], dropped_dependencies: [], proof_change: null, descoped: false } }), block(1), block(2)];
    deriveUmbrella(rows[0]!, rows.slice(1), { earlyStop: false });
    const json = { run: { qid: "umbrella_paper", early_stop: false }, results: rows, names: { "thm:main": "Theorem 5.2", "thm:cor-fix-1": "Proposition 5.2.1", "thm:cor-fix-2": "Proposition 5.2.2" } } as unknown as VerifyReportJson;
    const md = renderMatch({ report: json, links: [], tags: new Map(), core: built(file(umbrella())), leanDir: "lean/Papers/U" } as never);
    expect(md).toContain("## Theorem 5.2\n\n**Statement (corrected).** Propositions 5.2.1 and 5.2.2 hold, each under the conditions stated in it.");
    expect(md).toContain("set out after it: Proposition 5.2.1, Proposition 5.2.2. This result is established exactly when all of them are.");
    expect(md).toContain("**Lean.** no declaration of its own: established as Propositions 5.2.1 and 5.2.2 (`P.b1`, `P.b2`)");
    expect(md).toContain("**Status.** established through its propositions, each proved in Lean (it has no Lean declaration of its own). **Axioms (of its propositions together).**");
    expect(md).toContain("| Theorem 5.2 | `thm:main` | `thm:main` | `main.tex:9-11` | — (Propositions 5.2.1 and 5.2.2) |");
  });
});

describe("the page and the corrected paper", () => {
  const BLUE = `\\vsOriginal{${PRINTED}}\\vsCorrected{${UMBRELLA_STATEMENT}}`;
  const blocks = (n: number, macro = "vsSplitProposition"): string => Array.from({ length: n }, (_, k) => `\\${macro}{thm:cor-fix-${k + 1}}{Theorem~\\ref{thm:main}}{Bound ${k + 1}. \\vsLine\\textit{Proof.} By a lemma.}`).join("\n");
  const page = (body: string): string => renderPaper({ files: { "m.tex": `\\begin{document}\\begin{theorem}\\label{thm:main}${body}\\end{theorem}\n${blocks(3)}\n\\begin{theorem}\\label{thm:use}Z.\\end{theorem}\\end{document}` }, main: "m.tex", aux: String.raw`\newlabel{thm:main}{{5.2}{3}}\newlabel{thm:use}{{5.3}{3}}` }).html;

  it("the page: the printed statement red, then the sentence naming its propositions blue, then the proposition blocks", () => {
    const html = page(BLUE);
    const red = html.indexOf('class="rv del'), blue = html.indexOf("Propositions 5.2.1–5.2.3 hold, each under the conditions stated in it."), first = html.indexOf("Proposition 5.2.1.");
    expect(red).toBeGreaterThan(-1);
    expect(blue).toBeGreaterThan(red);
    expect(first).toBeGreaterThan(blue);
    expect(html).toMatch(/<div class="rv ins[^"]* umbrella"/u);
    expect(html).not.toContain(UMBRELLA_STATEMENT);
    expect(html).not.toContain("\u0001");
    // a corrected statement that is not the umbrella sentence is untouched
    expect(page("\\vsOriginal{X.}\\vsCorrected{The third bound holds.}")).not.toMatch(/class="rv ins[^"]* umbrella"/u);
  });

  it("the page's model: the umbrella with its blocks, no declaration, resting on them (the proof map draws it above), proved exactly when all of them are", async () => {
    const root = mkdtempSync(path.join(os.tmpdir(), "umbrella-ui-"));
    tmp.push(root);
    const dir = path.join(root, "runs", "u");
    mkdirSync(path.join(dir, "discovery"), { recursive: true });
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: { phase: "review" } }));
    writeFileSync(path.join(dir, "discovery", "core.json"), JSON.stringify(built(file(umbrella()))));
    const cfg = { toolkitRoot: root, runsDir: path.join(root, "runs") } as never;
    const by = new Map((await runDetail(cfg, "u")).results.map((r) => [r.id, r]));
    expect(by.get("thm:main")).toMatchObject({ umbrella: true, blocks: [ID1, ID2], deps: [ID1, ID2], lean: null, proved: false });
    expect(by.get(ID1)).toMatchObject({ splitFrom: "thm:main", splitKind: "proposition", deps: ["lem:one"] });
    expect(by.get("thm:use")!.umbrella).toBeUndefined();
    // with every proof closed in the run's graph (the scaffold stands: the proof loop is at work), the
    // umbrella — which has no node there — is proved
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "3", verify: { phase: "formalization" } }));
    const closed = ["lem:one", "lem:two", "thm:use", ID1, ID2].map((id) => ({ id, kind: "theorem", proof: { state: "complete" } }));
    writeFileSync(path.join(dir, "graph.json"), JSON.stringify({ nodes: closed, edges: [] }));
    expect(new Map((await runDetail(cfg, "u")).results.map((r) => [r.id, r.proved])).get("thm:main")).toBe(true);
    writeFileSync(path.join(dir, "graph.json"), JSON.stringify({ nodes: closed.map((n) => (n.id === ID2 ? { ...n, proof: { state: "sorry" } } : n)), edges: [] }));
    expect(new Map((await runDetail(cfg, "u")).results.map((r) => [r.id, r.proved])).get("thm:main")).toBe(false);
  });

  it("the page's script: an umbrella's drawer lists its propositions with their status and a jump to each, and no Lean rows", async () => {
    const js = await readFile(new URL("../../src/ui/static/app.js", import.meta.url), "utf8");
    expect(js).toContain("} else if (r.umbrella) {");
    expect(js).toContain("Established through its propositions: it has no Lean declaration of its own and holds exactly when all of them do");
    expect(js).toContain('data-umbgo="${esc(b.id)}"');
    expect(js).toContain('$$("#d-body [data-umbgo]").forEach((b) => b.addEventListener("click", () => { jumpTo(b.dataset.umbgo); openDrawer(b.dataset.umbgo); }));');
    expect(js).toContain('<h4>${r.umbrella ? "Its propositions" : "Lean"}</h4>');
  });

  const STMT = ["\\begin{theorem}\\label{thm:main}", PRINTED, "\\end{theorem}"];
  const doc = (...lines: string[]): string => ["\\documentclass{article}", "\\begin{document}", ...lines, "\\end{document}"].join("\n");
  const one = (): Core => ({ ...core(), statements: [{ ...core().statements[2]!, tex_locator: loc(3, "theorem", "thm:main") }] }) as Core;
  const input = (correctedView: boolean, corollaries: unknown[] = [P1, P2]): AnnotationInput => {
    const files = { "main.tex": doc(...STMT, "Text.") };
    return {
      files,
      envs: { main_file: "main.tex", files: ["main.tex"], newtheorem: {}, bibliography: [], envs: [{ id: "thm:main", kind: "theorem", envName: "theorem", label: "thm:main", title: null, body: PRINTED, proof: null, proofLines: null, section: null, lines: { file: "main.tex", from: 3, to: 5 }, refs: [] }] } as never,
      flatText: files["main.tex"], lineMap: files["main.tex"].split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 })), refs: null, transcribed: one(), core: one(),
      patches: { patches: [{ node: "thm:main", corrected_statement: UMBRELLA_STATEMENT, proof_note: UMBRELLA_PROOF, umbrella: true, corollaries }], unfixable: [] } as never,
      paperErrors: { "thm:main": { detail: "the second bound fails", witness: "w" } }, findings: [], review: null, correctedView,
    };
  };
  const annotated = (correctedView: boolean, corollaries?: unknown[]): string => {
    const i = input(correctedView, corollaries);
    const plan = planAnnotations(i);
    expect(plan.unlocated).toEqual([]);
    return applyTexEdits(i.files["main.tex"]!, plan.edits["main.tex"] ?? []);
  };

  it("the annotated paper: the whole printed statement red, the sentence blue, then every block under the proposition macro — a proof that names the result does not make it a corollary", () => {
    const naming = { ...P2, follows: "As in Theorem~\\ref{thm:main}, by Lemma~\\ref{lem:two}." };
    const tex = annotated(false, [P1, naming]);
    expect(tex).toContain(`\\vsOriginal{${PRINTED}}`);
    expect(tex).toContain(`\\vsCorrected{${UMBRELLA_STATEMENT}}`);
    expect(tex.match(/\\vsSplitProposition\{/gu)).toHaveLength(2);
    expect(tex).not.toContain("\\vsCorollary{");
    expect(tex.indexOf("\\vsSplitProposition{")).toBeGreaterThan(tex.indexOf("\\end{theorem}"));
    const html = renderPaper({ files: { "main.tex": tex }, main: "main.tex", aux: String.raw`\newlabel{thm:main}{{5.2}{3}}` }).html;
    expect(html).toContain("Propositions 5.2.1 and 5.2.2 hold, each under the conditions stated in it.");
  });

  it("the corrected paper prints the sentence in the result's environment and the blocks after it — by `\\ref` where the paper numbers its propositions, else \"The following propositions\"", () => {
    const tex = annotated(true);
    const numbered = correctedTex(tex, { proofEnv: true, propositionEnv: { name: "prop", numbered: true } }).tex;
    expect(numbered).toContain(`\\begin{theorem}\\label{thm:main}\nPropositions~\\ref{${ID1}} and~\\ref{${ID2}} hold, each under the conditions stated in it.\n\\end{theorem}`);
    expect(numbered).toContain(`\\begin{prop}[the first bound]\\label{${ID1}}\n${P1.statement}\n\\end{prop}`);
    expect(numbered.indexOf(`\\label{${ID1}}`)).toBeGreaterThan(numbered.indexOf("\\end{theorem}"));
    expect(numbered).not.toContain(PRINTED);
    const three = correctedTex(annotated(true, [P1, P2, { statement: "The third bound holds.", follows: THIRD_PROOF }]), { proofEnv: true, propositionEnv: { name: "prop", numbered: true } }).tex;
    expect(three).toContain(`Propositions~\\ref{${ID1}}--\\ref{${splitCorollaryId("thm:main", "The third bound holds.")}} hold, each under the conditions stated in it.`);
    for (const opts of [{ proofEnv: true }, { proofEnv: true, propositionEnv: { name: "prop", numbered: false } }]) {
      const plain = correctedTex(tex, opts).tex;
      expect(plain).toContain(`\\begin{theorem}\\label{thm:main}\n${UMBRELLA_STATEMENT}\n\\end{theorem}`);
      expect(plain).toContain(P1.statement);
    }
    expect(numbered).not.toMatch(/\\vs[A-Z]/u);
  });
});

describe("the conversion: a split repair becomes an umbrella without a fixer round", () => {
  it("pure: what the statement still states is one more proposition block — its corrected text, the proof the patch holds, the hypotheses the corrected node uses — after the blocks on file; the patch keeps its readings and loses its ops", () => {
    const before = file(split());
    const { file: after, block } = umbrellaConversion(core(), before, "thm:main", "the third bound");
    const p = after.patches[0]!;
    expect(block).toEqual({ title: "the third bound", statement: THIRD, follows: THIRD_PROOF, adds: ["ass:a"], id: splitCorollaryId("thm:main", THIRD) });
    expect(p).toMatchObject({ umbrella: true, ops: [], corrected_statement: UMBRELLA_STATEMENT, proof_note: UMBRELLA_PROOF, readings: ["a bound is uniform"] });
    expect(p.corollaries).toEqual([P1, P2, { title: "the third bound", statement: THIRD, follows: THIRD_PROOF, adds: ["ass:a"] }]);
    expect([p.drops, p.adds, p.supersedes]).toEqual([undefined, undefined, undefined]);
    expect(validatePatchFile(core(), after, ["thm:main"])).toEqual([]);
    expect(before.patches[0]!.umbrella).toBeUndefined();
  });

  it("the core it builds: the same blocks under the same ids, one more, the umbrella over all three; only the result's own verdict basis moves", () => {
    const before = file(split());
    const [a, b] = [built(before), built(umbrellaConversion(core(), before, "thm:main").file)];
    const id3 = splitCorollaryId("thm:main", THIRD);
    expect(st(b, "thm:main")).toMatchObject({ umbrella: true, statement: UMBRELLA_STATEMENT, depends_on: expect.arrayContaining([ID1, ID2, id3]) });
    expect(st(b, id3)).toMatchObject({ split_from: "thm:main", statement: THIRD, proof_tex: THIRD_PROOF });
    expect(st(b, id3).depends_on.filter((d) => !d.startsWith("ass:pin-fix-"))).toEqual(["ass:a", "lem:one"]);
    expect([...splitKinds(b).values()]).toEqual(["proposition", "proposition", "proposition"]);
    expect(checkCoreInvariants(b)).toEqual([]);
    const shared = [...a.statements, ...a.assumptions].map((n) => n.id).filter((id) => [...b.statements, ...b.assumptions].some((n) => n.id === id));
    expect(shared.filter((id) => nodeFingerprint(a, id) !== nodeFingerprint(b, id))).toEqual(["thm:main", "thm:use"]);
    // the reading stated by the repair binds the new block as it binds the others
    expect(b.assumptions.find((x) => x.id.startsWith("ass:pin-fix-"))!.used_by).toEqual([ID1, ID2, id3, "thm:main"].sort());
  });

  it("the proof of the new block: the amended or written proof of the patch; the printed proof when the patch left it as printed; none at all is refused", () => {
    const printed = core();
    (printed.statements[2] as { proof_tex?: string }).proof_tex = "By Lemma~\\ref{lem:two} and a union bound.";
    const asPrinted = split({ proof_note: PROOF_UNCHANGED });
    expect(umbrellaConversion(printed, file(asPrinted), "thm:main").block.follows).toBe("By Lemma~\\ref{lem:two} and a union bound.");
    expect(() => umbrellaConversion(core(), file(asPrinted), "thm:main")).toThrow(/neither the repair nor the paper holds a proof of what the statement still claims/u);
    // a statement the repair left as printed (blocks beside it): the printed text is the block, without its label or hypothesis list
    const labelled = core();
    (labelled.statements[2] as { statement: string }).statement = `\\label{thm:main}\n${PRINTED} [Hypotheses: ass:a, ass:b, ass:only]`;
    expect(umbrellaConversion(labelled, file(split({ corrected_statement: null, ops: [], drops: null })), "thm:main").block).toMatchObject({ statement: PRINTED, adds: ["ass:a", "ass:b", "ass:only"] });
  });

  it("refused with the reason: no repair, no blocks, an umbrella already, a block that is a corollary of the statement (it has a main claim), a proof citing the result", () => {
    expect(() => umbrellaConversion(core(), file(split()), "thm:use")).toThrow(/--umbrella thm:use: no applied repair of it/u);
    expect(() => umbrellaConversion(core(), file(split()), "ass:a")).toThrow(/not a result of the core/u);
    expect(() => umbrellaConversion(core(), file(split({ corollaries: null })), "thm:main")).toThrow(/its repair splits off no block.*only a repair that already splits is converted/u);
    expect(() => umbrellaConversion(core(), file(umbrella()), "thm:main")).toThrow(/it is an umbrella already/u);
    const cor = { ...P2, follows: "By Theorem~\\ref{thm:main}." };
    expect(() => umbrellaConversion(core(), file(split({ corollaries: [P1, cor] })), "thm:main")).toThrow(/block 2 is a corollary of the corrected statement.*the statement has a main claim of its own and the split form stands/u);
    expect(() => umbrellaConversion(core(), file(split({ proof_note: "By Theorem~\\ref{thm:main} itself." })), "thm:main")).toThrow(/cites the result itself/u);
  });

  it("`--umbrella <node>` / `\"<node>: <title>\"` parses, needs --resume and stands alone", () => {
    expect(parseUmbrella("thm:local")).toEqual({ node: "thm:local" });
    expect(parseUmbrella(" thm:local : Conditional-noise bounds ")).toEqual({ node: "thm:local", title: "Conditional-noise bounds" });
    expect(() => parseUmbrella("the local theorem")).toThrow(/give "<node>" or "<node>: <title>"/u);
    const base = ["paper.tex", "--toolkit", "/tk", "--slug", "s", "--resume"];
    expect(parseVerifyArgsForTest([...base, "--umbrella", "thm:local: Noise bounds", "--umbrella", "thm:b"]).umbrella).toEqual(["thm:local: Noise bounds", "thm:b"]);
    expect(parseVerifyArgsForTest(base).umbrella).toBeNull();
    expect(() => parseVerifyArgsForTest([...base.slice(0, -1), "--umbrella", "thm:local"])).toThrow(/--umbrella requires --resume/u);
    expect(() => parseVerifyArgsForTest([...base, "--umbrella"])).toThrow(/--umbrella requires "<node>" or "<node>: <title>"/u);
    expect(() => parseVerifyArgsForTest([...base, "--umbrella", "thm:local", "--add-condition", "thm:local: c"])).toThrow(/answer different halts/u);
  });

  async function run() {
    const root = mkdtempSync(path.join(os.tmpdir(), "umbrella-run-"));
    tmp.push(root);
    const runDir = path.join(root, "runs", "u");
    mkdirSync(path.join(runDir, "discovery"), { recursive: true });
    mkdirSync(path.join(runDir, "formalization"), { recursive: true });
    writeFileSync(path.join(runDir, VERIFY_FILES.coreTranscribed), JSON.stringify(core(), null, 2));
    writeFileSync(path.join(runDir, VERIFY_FILES.coreJson), JSON.stringify(built(file(split())), null, 2));
    writeFileSync(path.join(runDir, VERIFY_FILES.patches), JSON.stringify(file(split()), null, 2));
    const state = createVerifyInitialState("u", { phase: "formalization", source: { input: "paper.tex", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: "accepted", v1_rounds: 1, v1_5_rounds: 1, findings: [], report_path: null });
    state.stage_completed = "3";
    state.verify!.paper_errors = { "thm:main": { detail: "the second bound fails without B", witness: "w" } };
    return { runDir, state };
  }

  it("on a run: the patch file is rewritten, core.json rebuilt, the run sent back to V1.5 (the accepted-core hash dropped), and the plan entry of the result becomes the new block's with its Lean name", async () => {
    const { runDir, state } = await run();
    const planFile = path.join(runDir, "formalization", "plan.json");
    writeFileSync(planFile, JSON.stringify({ qid: "u", nodes: { "lem:one": { lean_name: "first_bound" }, "thm:main": { lean_kind: "theorem", lean_name: "third_bound", local_id: "thm:main" }, [ID1]: { lean_name: "first_bound_prop" } } }));
    const line = await convertToUmbrella(runDir, state, [{ node: "thm:main", title: "the third bound" }]);
    const id3 = splitCorollaryId("thm:main", THIRD);
    expect(line).toContain(`thm:main (its statement is now the block ${id3}, "the third bound"; 3 blocks)`);
    expect(line).toContain(`The plan entry of thm:main is now ${id3}'s (Lean name third_bound kept`);
    const onDisk = PatchFileSchema.parse(JSON.parse(readFileSync(path.join(runDir, VERIFY_FILES.patches), "utf8")));
    expect(onDisk.patches[0]).toMatchObject({ umbrella: true, ops: [], corrected_statement: UMBRELLA_STATEMENT });
    const c = JSON.parse(readFileSync(path.join(runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
    expect(st(c, "thm:main")).toMatchObject({ umbrella: true, statement: UMBRELLA_STATEMENT });
    expect(st(c, id3).statement).toBe(THIRD);
    expect(state).toMatchObject({ stage_completed: "V1", verify: { phase: "v1", core_sha256: null } });
    const plan = JSON.parse(readFileSync(planFile, "utf8")) as { nodes: Record<string, { lean_name: string; local_id?: string }> };
    expect(Object.keys(plan.nodes)).toEqual(["lem:one", id3, ID1]);
    expect(plan.nodes[id3]).toEqual({ lean_kind: "theorem", lean_name: "third_bound", local_id: id3 });
    // a second conversion is refused, and nothing is written
    await expect(convertToUmbrella(runDir, state, [{ node: "thm:main" }])).rejects.toThrow(/it is an umbrella already/u);
  });

  it("the plan is left alone when there is none, when it does not plan the result, or when it already plans the block", async () => {
    const { runDir } = await run();
    const planFile = path.join(runDir, "formalization", "plan.json");
    expect(await movePlanEntries(planFile, [{ from: "thm:main", to: "thm:cor-fix-x" }])).toEqual([]);
    writeFileSync(planFile, JSON.stringify({ nodes: { "thm:main": { lean_name: "a" }, "thm:cor-fix-x": { lean_name: "b" } } }));
    expect(await movePlanEntries(planFile, [{ from: "thm:main", to: "thm:cor-fix-x" }, { from: "thm:other", to: "thm:cor-fix-y" }])).toEqual([]);
    expect(JSON.parse(readFileSync(planFile, "utf8")).nodes["thm:main"]).toEqual({ lean_name: "a" });
  });

  it("refused before anything is written when the node has no blocks", async () => {
    const { runDir, state } = await run();
    writeFileSync(path.join(runDir, VERIFY_FILES.patches), JSON.stringify(file(split({ corollaries: null })), null, 2));
    const before = readFileSync(path.join(runDir, VERIFY_FILES.patches), "utf8");
    await expect(convertToUmbrella(runDir, state, [{ node: "thm:main" }])).rejects.toThrow(/its repair splits off no block/u);
    expect(readFileSync(path.join(runDir, VERIFY_FILES.patches), "utf8")).toBe(before);
    expect(state.stage_completed).toBe("3");
  });
});

describe("the prompts say when a result is an umbrella", () => {
  const read = (rel: string): Promise<string> => readFile(new URL(`../../src/${rel}`, import.meta.url), "utf8");
  const flat = (t: string): string => t.replace(/\s+/gu, " ");

  it("the fixer: one theorem or proposition mixing several conclusions under different assumptions with no main claim of its own; never when it has one, for a single claim, a \"moreover\" or length; it writes no sentence", async () => {
    const t = flat(await read("verify/prompts/V1/patch.txt"));
    expect(t).toContain("`umbrella`: null, unless the printed statement is ONE theorem or proposition mixing several conclusions, each holding under different assumptions, with nothing in it that is the statement's own main claim");
    expect(t).toContain("EVERY conclusion, or group of conclusions resting on the same conditions and results, is a block of `corollaries` (at least two), `ops` is empty");
    expect(t).toContain("You write no statement for the result");
    expect(t).toContain("it is established exactly when all of them are");
    expect(t).toContain("no `follows` cites the result itself, nor a result that rests on it");
    expect(t).toContain("A statement that has a main claim, with special cases or consequences beside it, is never an umbrella");
    expect(t).toContain("Never an umbrella for a single claim, for a further conclusion under the same assumptions, or for length.");
    expect(t).toContain("`suggested_repair` is `{ops, drops, adds, readings, conditions, corollaries, umbrella, proof_note}` or null");
    expect(t).toContain("A `split` finding on an umbrella says the printed statement has a main claim of its own");
  });

  it("the referee: an umbrella holds when each block does and they cover the printed statement; what no block keeps is given up; its own sentence is never graded; the form check runs both ways", async () => {
    const t = flat(await read("verify/prompts/V1.5/review.txt"));
    expect(t).toContain("UMBRELLAS. A patch with `umbrella: true` states its result as an umbrella");
    expect(t).toContain("The umbrella holds exactly when each of its blocks does and they together cover what the printed statement claims");
    expect(t).toContain("a conclusion in no block, or kept only under conditions excluding cases the paper meant, is given up (`weakens_contribution`, on the umbrella or on that block)");
    expect(t).toContain("Its own sentence and its proof are never an error, never unclear, never drift");
    expect(t).toContain("what it keeps is a mere fragment, one more conclusion among those already moved to blocks — say that it should be an umbrella");
    expect(t).toContain("on an umbrella whose printed statement plainly has a main claim of its own");
    expect(t).toContain("that the claim should be restored as the statement");
    expect(flat(await read("verify/v1_5_schema.ts"))).toContain("or that it should be an umbrella, or (on an umbrella) the main claim to restore as its statement");
  });

  it("the F stages reading core.json are told an umbrella is not formalized; no prompt names a paper", async () => {
    const line = "`umbrella: true`";
    const rule = "is not formalized — no plan entry, no declaration, no `@node` tag";
    for (const p of ["formalization/prompts/F2/stage2_scaffold.txt", "formalization/prompts/F4/proof_filler.txt", "formalization/prompts/F4/proof_reviewer.txt"]) { const t = flat(await read(p)); expect(t).toContain(line); expect(t).toContain(rule); }
    for (const p of ["verify/prompts/V1/patch.txt", "verify/prompts/V1.5/review.txt"]) expect(await read(p)).not.toMatch(/5\.2|thm:local|noise bound/iu);
  });
});
