import { fileURLToPath } from "node:url";
/**
 * SHOWN = HASHED. A verdict's basis (`core_graph.ts` `basisInputs`, with the repairs its shard shows
 * the node, `stage_v1_5.ts` `repairBasis`) must move whenever the shard PROMPT of the node moves. Each
 * case edits one thing of a run — a patch, the ledger, a node a result uses, a verdict — builds every
 * node's own shard prompt before and after (`buildShardPrompt`, the PATCHES section as the stage
 * renders it) and compares with the bases: no node whose prompt changed keeps its basis.
 */
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { basisInputs, basisOf, buildCore, splitCorollaryId, type PatchFileLike } from "../../src/verify/core_graph.js";
import { dependencyVerdicts } from "../../src/verify/referee_levels.js";
import { buildShardPrompt } from "../../src/verify/referee_shard_prompts.js";
import { paperIndex, setupExcerpt } from "../../src/verify/referee_slices.js";
import { patchesSection, repairBasis, shardPatchArgs, shownVerdictOf, type PatchInputs } from "../../src/verify/stage_v1_5.js";
import type { V15NodeVerdict } from "../../src/verify/types.js";

const DIR = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..", "src", "verify", "prompts", "V1.5");
const BASE = readFileSync(path.join(DIR, "review.txt"), "utf8");
const SHARD = readFileSync(path.join(DIR, "shard.txt"), "utf8");
const sha = (t: string): string => createHash("sha256").update(t).digest("hex");

/** thm:main (repaired, split into a corollary and a proposition block) rests on lem:rate; thm:use uses thm:main. */
function transcribed(): Core {
  return {
    qid: "shown",
    symbols: [{ name: "\\kappa", type: "constant" }, { name: "\\rho", type: "rate" }],
    assumptions: [{ id: "ass:gauss", condition: "the design is Gaussian", novel: { flag: true, justification: "Assumption 1" } }],
    definitions: [],
    statements: [
      { id: "lem:rate", kind: "lemma", statement: "the rate is $n^{-1/2}$ with constant $\\kappa$", depends_on: ["ass:gauss"], proof_tex: "A direct bound.", status: "to-prove", tex_locator: { file: "main.tex", from: 6, to: 8, env: "lemma", label: "lem:rate" } },
      { id: "thm:main", kind: "theorem", statement: "The estimator is normal; under a Gaussian design it is efficient; and the rate of Lemma~\\ref{lem:rate} is attained.", depends_on: ["lem:rate"], proof_tex: "By Lemma~\\ref{lem:rate}.", status: "to-prove", tex_locator: { file: "main.tex", from: 3, to: 5, env: "theorem", label: "thm:main" } },
      { id: "thm:use", kind: "theorem", statement: "the interval covers", depends_on: ["thm:main"], proof_tex: "By Theorem~\\ref{thm:main}.", status: "to-prove", tex_locator: { file: "main.tex", from: 9, to: 11, env: "theorem", label: "thm:use" } },
    ],
    target_estimand: "t",
    bibliography: [],
  } as unknown as Core;
}
const COR = { title: "the Gaussian case", statement: "If the design is Gaussian, the estimator is efficient.", follows: "Under a Gaussian design the limit variance of Theorem~\\ref{thm:main} is the information bound.", adds: ["ass:gauss"] };
const PROP = { title: "the rate", statement: "The estimator of Theorem~\\ref{thm:main} attains the rate $n^{-1/2}$.", follows: "This is Lemma~\\ref{lem:rate}." };
const COR_ID = splitCorollaryId("thm:main", COR.statement);
const PROP_ID = splitCorollaryId("thm:main", PROP.statement);

interface World {
  transcribed: Core;
  patches: PatchFileLike & { patches: Array<Record<string, unknown>> };
  ledger: Record<string, Record<string, unknown>>;
  verdicts: Record<string, Partial<V15NodeVerdict>>;
}
const world = (): World => ({
  transcribed: transcribed(),
  patches: {
    key_results: [],
    unfixable: [],
    patches: [{ node: "thm:main", corrected_statement: "The estimator is normal.", proof_note: "The central limit theorem.", given_up: "nothing", reason: "the printed claim bundles three", owner_explanation: "The theorem is split.", corollaries: [COR, PROP] }],
  } as never,
  ledger: { "thm:main": { detail: "the printed claim fails without a Gaussian design", witness: "a heavy-tailed design" } },
  verdicts: {},
});

/** Every node's own shard prompt and its basis, as a pass over `w` builds them. */
function snapshot(w: World): { ids: string[]; prompt: Map<string, string>; basis: Map<string, string> } {
  const core = buildCore(w.transcribed, { patches: w.patches }).core;
  const ids = [...core.statements, ...core.assumptions, ...core.definitions].map((n) => n.id);
  const px = paperIndex("", null, null);
  const args: PatchInputs = { patches: w.patches as never, paperErrors: w.ledger as never, printed: new Map(w.transcribed.statements.map((st) => [st.id, st.statement] as const)), hypotheses: new Map(w.transcribed.assumptions.map((a) => [a.id, a.condition] as const)) };
  const final = new Map(ids.map((id) => [id, { id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "reproduced", witness: null, bookkeeping_assumption: null, reading: null, ...w.verdicts[id] } as V15NodeVerdict] as const));
  const repairOf = (id: string) => (w.patches.patches.some((p) => p.node === id) ? { corrected: core.statements.find((st) => st.id === id)!.statement, printedError: (w.ledger[id]?.witness as string | undefined) ?? null } : null);
  const ctx = {
    core,
    px,
    setup: setupExcerpt(px),
    totalNodes: ids.length,
    scope: "scope",
    extraSections: (xs: readonly string[]) => patchesSection(args, xs, ...shardPatchArgs(core, px, xs)),
    dependencies: (id: string) => dependencyVerdicts(core, id, final, repairOf),
  };
  const own = repairBasis(args, core, px);
  const shown = shownVerdictOf(core, repairOf);
  const line = (d: string): string | undefined => (final.has(d) ? sha(shown(d, final.get(d)!)) : undefined);
  return {
    ids,
    // (Without the list of the OTHER nodes' ids: the vocabulary of a wiring fix, the same for every
    // shard and in no basis — a node that joins or leaves the paper does not re-open every verdict.)
    prompt: new Map(ids.map((id) => [id, buildShardPrompt(ctx as never, BASE, SHARD, [id]).replace(/^Every other node of the paper[^\n]*\n(?:[^\n]+\n)*/mu, "")] as const)),
    basis: new Map(ids.map((id) => [id, basisOf(basisInputs(core, id, new Map(), own.get(id), line))] as const)),
  };
}

/** After the edit `f`: the nodes whose prompt changed, and those among them whose basis did NOT (holes). */
function edit(f: (w: World) => void): { shown: string[]; holes: string[]; moved: string[] } {
  const [a, b] = [snapshot(world()), snapshot(((w) => (f(w), w))(world()))];
  const ids = a.ids.filter((id) => b.prompt.has(id));
  const shown = ids.filter((id) => a.prompt.get(id) !== b.prompt.get(id)).sort();
  return { shown, holes: shown.filter((id) => a.basis.get(id) === b.basis.get(id)), moved: ids.filter((id) => a.basis.get(id) !== b.basis.get(id)).sort() };
}
const patchOf = (w: World): Record<string, unknown> => w.patches.patches[0]!;
const st = (w: World, id: string): Core["statements"][number] => w.transcribed.statements.find((x) => x.id === id)!;

describe("shown = hashed: the repairs a shard shows", () => {
  it("the fixture: the parent's patch is shown to the parent and to each block split off it", () => {
    const s = snapshot(world());
    for (const id of ["thm:main", COR_ID, PROP_ID]) expect(s.prompt.get(id)).toContain("=== PATCHES");
    for (const id of ["thm:use", "lem:rate", "ass:gauss"]) expect(s.prompt.get(id)).not.toContain("=== PATCHES");
    // a block is shown the parent's proof note (its record does not carry it); the parent reads it in its record
    expect(s.prompt.get(COR_ID)).toContain('"proof_note":"The central limit theorem."');
  });

  it("a rewritten proof note of the parent's repair (its statement unchanged) moves the basis of every block shown it", () => {
    const r = edit((w) => (patchOf(w).proof_note = "The central limit theorem, applied along the folds."));
    expect(r.shown).toEqual([COR_ID, PROP_ID, "thm:main"].sort());
    expect(r.holes).toEqual([]);
  });

  it("each field of the repair shown and the ledger entry beside it: given up, reason, fixer note, the finding — no node shown the change keeps its basis", () => {
    const edits: Array<[string, (w: World) => void]> = [
      ["given_up", (w) => (patchOf(w).given_up = "the efficiency claim outside Gaussian designs")],
      ["reason", (w) => (patchOf(w).reason = "another reason")],
      ["owner_explanation", (w) => (patchOf(w).owner_explanation = "The theorem is split in three.")],
      ["ledger detail", (w) => (w.ledger["thm:main"]!.detail = "the printed claim fails at $n = 1$")],
      ["ledger entry added", (w) => (w.ledger["thm:main"] = { detail: "d", witness: "w", weakens_contribution: true, suggested_repair: "gives up: x" })],
      ["a sibling block's statement", (w) => ((patchOf(w).corollaries as Array<Record<string, unknown>>)[0] = { ...COR, title: "the Gaussian case, restated" })],
    ];
    for (const [what, f] of edits) {
      const r = edit(f);
      expect(r.shown.length, what).toBeGreaterThanOrEqual(3);
      expect(r.holes, what).toEqual([]);
      // … and nothing that is not shown the repair is re-opened by it
      expect(r.moved.filter((id) => !r.shown.includes(id)), what).toEqual([]);
    }
  });

  it("the owner's ruling recorded on the ledger entry is not shown, and re-opens nothing", () => {
    const r = edit((w) => Object.assign(w.ledger["thm:main"]!, { owner_decision: "accepted", decision_reason: "fine" }));
    expect(r).toEqual({ shown: [], holes: [], moved: [] });
  });
});

describe("shown = hashed: what a shard shows of the nodes its node uses", () => {
  it("a used result's label, kind word, text and verdict line are shown to its users and move their bases; its proof and its free-symbol list are not shown and move none", () => {
    const users = ["thm:main", PROP_ID].sort(); // the nodes using lem:rate directly
    const cases: Array<[string, (w: World) => void, boolean]> = [
      ["label", (w) => (st(w, "lem:rate").tex_locator = { ...st(w, "lem:rate").tex_locator!, label: "lem:relabelled" }), true],
      ["environment word", (w) => (st(w, "lem:rate").tex_locator = { ...st(w, "lem:rate").tex_locator!, env: "proposition" }), true],
      ["text", (w) => (st(w, "lem:rate").statement += " Moreover the bound is sharp."), true],
      ["verdict", (w) => (w.verdicts["lem:rate"] = { correctness: "unclear", detail: "the bound is not derived" }), true],
      ["a hypothesis it is stated under", (w) => (w.transcribed.assumptions[0]!.condition = "the design is Gaussian with unit variance"), false],
      ["proof", (w) => (st(w, "lem:rate").proof_tex = "Another bound."), false],
      ["free_symbols", (w) => (st(w, "lem:rate").free_symbols = ["\\rho"]), false],
      ["line numbers", (w) => (st(w, "lem:rate").tex_locator = { ...st(w, "lem:rate").tex_locator!, from: 60, to: 80 }), false],
    ];
    for (const [what, f, shownToUsers] of cases) {
      const r = edit(f);
      expect(r.holes, what).toEqual([]);
      const others = (xs: string[]): string[] => xs.filter((id) => id !== "lem:rate" && id !== "ass:gauss");
      if (shownToUsers) expect(others(r.shown).filter((id) => users.includes(id)), what).toEqual(users);
      // free_symbols, the proof and the line numbers of a used result reach no user's basis
      if (what === "proof" || what === "free_symbols" || what === "line numbers") expect(others(r.moved), what).toEqual([]);
    }
  });

  it("the label a `\\ref` resolves to is in the user's prompt beside the used node's text", () => {
    expect(snapshot(world()).prompt.get(PROP_ID)).toContain("- lem:rate (lemma, \\label{lem:rate}): the rate is");
  });
});
