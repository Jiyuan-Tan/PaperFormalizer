import { fileURLToPath } from "node:url";
/**
 * The sharded V1.5 referee (`referee_shards.ts`, `referee_slices.ts`). No network: `runCodex` is a fake
 * that answers by the reply schema it is handed (shard / global).
 */
import { readFileSync } from "node:fs";
import { mkdir, mkdtemp, readdir, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState } from "../../src/state.js";
import type { StateJson } from "../../src/types.js";
import {
  GLOBAL_REPLY,
  SHARD_REPLY,
  DEFAULT_SHARD_LIMITS,
  applyCrossNode,
  mergeFix,
  compactCore,
  UNRELATED_TEXT_MAX,
  dependencyLine,
  kindCeiling,
  groupShards,
  runShardedReferee,
  shardCapacities,
  type RefereeCall,
  type ShardedRefereeInput,
} from "../../src/verify/referee_shards.js";
import { dependencyVerdicts, refereeLevels, settleOnErroredDependencies } from "../../src/verify/referee_levels.js";
import { bibliographyEntries, citesIn, nodeExcerpts, paperIndex, referencedPassages, setupExcerpt, withoutBibliography } from "../../src/verify/referee_slices.js";
import { runStageV1_5 } from "../../src/verify/stage_v1_5.js";
import { runStageV1 } from "../../src/verify/stage_v1.js";
import { countRound } from "../../src/verify/caps.js";
import { PATCH_REPLY_JSON_SCHEMA, type PatchFile } from "../../src/verify/patches.js";
import { ruleOnReceipt } from "../../src/verify/weakening.js";
import { MAX_PATCH_ROUNDS_PER_LEVEL, VERIFY_FILES, type EnvsJson, type V15NodeVerdict, type V15Review, type VerifyStageArgs } from "../../src/verify/types.js";
import { withOwnerExplanations } from "./owner_explained.js";
import { symbolReply } from "./symbol_fake.js";

const TOOLS = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..");
const FLAT_FIXTURE = path.join(TOOLS, "test", "verify", "fixtures", "v1_5", "flat.tex");

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

/** The V1.5 fixture core (same paper as `fixtures/v1_5/flat.tex`): 6 nodes. */
function fixtureCore(): Core {
  return {
    qid: "toy",
    symbols: [{ name: "Y", type: "random variable", role: "outcome" }],
    assumptions: [
      { id: "ass:unconfoundedness", kind: "causal-structural", condition: "$Y(d) \\perp D \\mid X$ for $d \\in \\{0,1\\}$.", novel: { flag: true, justification: "Assumption 1" }, tex_locator: { file: "main.tex", from: 10, to: 12, env: "assumption", label: "ass:unconf" } },
      { id: "ass:overlap", kind: "support", condition: "$0 < e(X) < 1$ almost surely.", novel: { flag: true, justification: "Assumption 2" }, tex_locator: { file: "main.tex", from: 14, to: 16, env: "assumption", label: "ass:overlap" } },
    ],
    definitions: [{ id: "def:propensity", name: "propensity score", construction: "Let $Y$ be the outcome, $D \\in \\{0,1\\}$ the treatment and $X$ the covariates.", tex_locator: { file: "main.tex", from: 8, to: 8, env: "prose", label: null } }],
    statements: [
      { id: "lem:ipw-identity", kind: "lemma", statement: "Under Assumption \\ref{ass:overlap}, $E[DY/e(X)] = E[Y(1)]$.", depends_on: ["ass:overlap", "def:propensity"], proof_tex: "Condition on $X$ and apply the tower property.", status: "to-prove", tex_locator: { file: "main.tex", from: 18, to: 20, env: "lem", label: "lem:ipw" } },
      { id: "thm:ate-identification", kind: "theorem", statement: "Under Assumptions \\ref{ass:unconf} and \\ref{ass:overlap}, $\\tau = E[DY/e(X) - (1-D)Y/(1-e(X))]$.", depends_on: ["ass:unconfoundedness", "ass:overlap", "def:propensity", "lem:ipw-identity"], proof_tex: "Apply Lemma \\ref{lem:ipw} to each arm and subtract.", status: "to-prove", tex_locator: { file: "main.tex", from: 25, to: 27, env: "thm", label: "thm:ate" } },
      { id: "lem:delta-method", kind: "lemma", statement: "(van der Vaart, Theorem 3.1.) If $\\sqrt{n}(T_n - \\theta) \\rightsquigarrow T$ and $\\phi$ is differentiable at $\\theta$, then $\\sqrt{n}(\\phi(T_n) - \\phi(\\theta)) \\rightsquigarrow \\phi'_\\theta(T)$.", depends_on: [], status: "cited", source: { cite: "vandervaart1998", locator: "Theorem 3.1", verbatim_statement: "Delta method." }, tex_locator: { file: "main.tex", from: 32, to: 34, env: "lem", label: "lem:delta" } },
    ],
    target_estimand: "$\\tau = E[Y(1) - Y(0)]$",
    bibliography: [{ key: "vandervaart1998", citation: "van der Vaart (1998). Asymptotic Statistics." }],
  } as unknown as Core;
}
const FIXTURE_IDS = ["lem:ipw-identity", "thm:ate-identification", "lem:delta-method", "ass:unconfoundedness", "ass:overlap", "def:propensity"];
/** The fixture's dependency levels. */
const LEVEL: Record<string, number> = { "ass:unconfoundedness": 0, "ass:overlap": 0, "def:propensity": 0, "lem:ipw-identity": 1, "lem:delta-method": 1, "thm:ate-identification": 2 };

/** A synthetic core: `k` statements, statement i with `priv` private hypotheses, plus `shared`
 * hypotheses every statement uses. */
function syntheticCore(k: number, priv: number, shared = 0): Core {
  const assumptions: Array<Record<string, unknown>> = [];
  const statements: Array<Record<string, unknown>> = [];
  for (let j = 0; j < shared; j += 1) assumptions.push({ id: `ass:shared-${j}`, condition: `shared ${j}` });
  for (let i = 0; i < k; i += 1) {
    const hyps = Array.from({ length: priv }, (_, j) => `ass:s${i}-h${j}`);
    for (const h of hyps) assumptions.push({ id: h, condition: `condition ${h}` });
    statements.push({ id: `thm:s${i}`, kind: "theorem", statement: `statement ${i}`, depends_on: [...hyps, ...Array.from({ length: shared }, (_, j) => `ass:shared-${j}`)], status: "to-prove" });
  }
  return { qid: "syn", symbols: [], assumptions, definitions: [], statements, target_estimand: "t", bibliography: [] } as unknown as Core;
}
const allIds = (c: Core): string[] => [...c.statements, ...c.assumptions, ...c.definitions].map((n) => n.id);
/** The share of a shard's room its nodes take (each `1 / ceiling` of its kind). */
const roomUsed = (core: Core, s: readonly string[]): number => s.reduce((a, id) => a + 1 / kindCeiling(core, id, DEFAULT_SHARD_LIMITS), 0);

describe("shard grouping", () => {
  it("sizes 4–6 per shard; every node once; a statement travels with its own hypotheses when they fit", () => {
    for (let n = 8; n <= 60; n += 1) {
      const caps = shardCapacities(n, 6);
      expect(caps.reduce((a, b) => a + b, 0)).toBe(n);
      for (const c of caps) expect(c >= 4 && c <= 6).toBe(true);
    }
    expect(shardCapacities(7, 6)).toEqual([4, 3]);
    for (const [k, priv] of [[6, 2], [4, 5], [8, 2]] as const) {
      const core = syntheticCore(k, priv);
      const shards = groupShards(core, allIds(core));
      expect(shards.flat().sort()).toEqual(allIds(core).sort());
      for (let i = 0; i < k; i += 1) {
        const home = shards.find((s) => s.includes(`thm:s${i}`))!;
        for (let j = 0; j < priv; j += 1) expect(home).toContain(`ass:s${i}-h${j}`);
      }
      for (const s of shards) expect(roomUsed(core, s)).toBeLessThanOrEqual(1 + 1e-9);
    }
    // A unit too big for one shard (a theorem with 8 hypotheses: 1/3 + 8/10 of the room): split,
    // the statement first, with as many of its hypotheses as fit.
    const tight = syntheticCore(3, 8);
    const shards = groupShards(tight, allIds(tight));
    expect(shards.flat().sort()).toEqual(allIds(tight).sort());
    for (let i = 0; i < 3; i += 1) {
      // The statement keeps at least one of its hypotheses, and sits before them.
      const home = shards.find((s) => s.includes(`thm:s${i}`))!;
      const hyp = home.findIndex((x) => x.startsWith(`ass:s${i}-`));
      expect(hyp).toBeGreaterThan(home.indexOf(`thm:s${i}`));
    }
  });

});

describe("dependency order (levels)", () => {
  /** defs/assumptions, two leaf lemmas, a theorem using both, a corollary of the theorem. */
  function dagCore(): Core {
    return {
      qid: "dag",
      symbols: [],
      assumptions: [{ id: "ass:a", condition: "a" }, { id: "ass:b", condition: "b" }],
      definitions: [{ id: "def:d", name: "d", construction: "d" }],
      statements: [
        { id: "thm:main", kind: "theorem", statement: "main", depends_on: ["lem:one", "lem:two", "ass:a"], status: "to-prove" },
        { id: "lem:one", kind: "lemma", statement: "one", depends_on: ["ass:a", "def:d"], status: "to-prove" },
        { id: "lem:two", kind: "lemma", statement: "two", depends_on: ["ass:b"], status: "to-prove" },
        { id: "cor:c", kind: "corollary", statement: "c", depends_on: ["thm:main"], status: "to-prove" },
      ],
      target_estimand: "t",
      bibliography: [],
    } as unknown as Core;
  }

  it("definitions and assumptions at 0, leaf lemmas at 1, the theorem using them at 2, its corollary at 3; carried nodes count as graded; a cycle is one level", () => {
    const core = dagCore();
    expect(refereeLevels(core, allIds(core))).toEqual({ levels: [["ass:a", "ass:b", "def:d"], ["lem:one", "lem:two"], ["thm:main"], ["cor:c"]], cycles: [] });
    // A carried node counts as graded.
    expect(refereeLevels(core, ["thm:main", "cor:c", "lem:two"]).levels).toEqual([[], ["lem:two"], ["thm:main"], ["cor:c"]]);
    // A dependency cycle is one level; what rests on it comes after.
    core.statements.find((s) => s.id === "lem:one")!.depends_on.push("thm:main");
    const r = refereeLevels(core, allIds(core));
    expect(r.cycles).toEqual([["thm:main", "lem:one"]]);
    expect(r.levels).toEqual([["ass:a", "ass:b", "def:d"], ["lem:two"], ["thm:main", "lem:one"], ["cor:c"]]);
  });

  it("an errored dependency makes the user unclear; a confirmed repair or a repair-only error does not", () => {
    const core = dagCore();
    const v = (id: string, o: Partial<V15NodeVerdict> = {}): V15NodeVerdict => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "fine", witness: null, bookkeeping_assumption: null, reading: null, ...o });
    const final = new Map([["lem:one", v("lem:one", { correctness: "error", witness: "fails when $a=0$" })], ["lem:two", v("lem:two")]]);
    const deps = dependencyVerdicts(core, "thm:main", final);
    expect(deps.map((d) => d.id)).toEqual(["lem:one", "lem:two"]);
    expect(dependencyLine(deps[0]!)).toBe("lem:one (lemma): ERROR — fails when $a=0$; no confirmed repair");
    const s = settleOnErroredDependencies(v("thm:main", { correctness: "bookkeeping", bookkeeping_assumption: { condition: "c", reason: "r" } }), deps);
    expect(s.on).toEqual(["lem:one"]);
    expect(s.verdict).toMatchObject({ correctness: "unclear", bookkeeping_assumption: null });
    expect(s.verdict.detail).toMatch(/^depends on lem:one, graded error\. fine/);
    // Its own error stands.
    expect(settleOnErroredDependencies(v("thm:main", { correctness: "error", witness: "own" }), deps).verdict.correctness).toBe("error");
    // A repair on file the grade confirms (clean, or an error on minimality only): the corrected form is used.
    const repaired = new Map([["lem:one", v("lem:one", { correctness: "error", witness: "weaker suffices", minimality: true })]]);
    const rd = dependencyVerdicts(core, "thm:main", repaired, () => ({ corrected: "one, for $a>0$", printedError: "fails when $a=0$" }));
    expect(settleOnErroredDependencies(v("thm:main"), rd).verdict.correctness).toBe("ok");
    expect(dependencyLine(rd[0]!)).toContain("confirmed repair: use its corrected form, one, for $a>0$ (the printed statement was an error: fails when $a=0$)");
    // A repair the current grade refutes is not confirmed.
    const refuted = dependencyVerdicts(core, "thm:main", final, () => ({ corrected: "one'", printedError: null }));
    expect(settleOnErroredDependencies(v("thm:main"), refuted).on).toEqual(["lem:one"]);
  });
});

describe("paper excerpts from locators", () => {
  // flat.tex = main.tex with an \input{sec} folded in at flat line 3 (original sec.tex lines 1–4).
  const flat = [
    "\\documentclass{article}\\newcommand{\\E}{\\mathbb{E}}",
    "\\begin{document}",
    "\\section{Setup}\\label{sec:setup}",
    "Let $Y$ be the outcome and $X$ covariates.",
    "",
    "\\begin{lemma}\\label{lem:a}",
    "Suppose $X$ is bounded. Then $\\E[Y] < \\infty$, as in \\eqref{eq:key}.",
    "\\end{lemma}",
    "\\begin{proof}",
    "Bound $Y$ by \\eqref{eq:key}.",
    "\\end{proof}",
    "",
    "Remark text about the key display",
    "\\begin{equation}\\label{eq:key} |Y| \\le 1 \\end{equation}",
    "",
    "\\begin{theorem}\\label{thm:b}",
    "The result holds.",
    "\\end{theorem}",
    "\\subsection{Proof of Theorem \\ref{thm:b}}",
    "It follows from Lemma \\ref{lem:a}.",
    "\\section{End}",
    "\\end{document}",
  ].join("\n");
  const lineMap = { lineMap: flat.split("\n").map((_, i) => (i >= 5 && i <= 10 ? { file: "sec.tex", line: i - 4 } : { file: "main.tex", line: i + 1 })) };
  const envs: EnvsJson = {
    main_file: "main.tex",
    files: ["main.tex", "sec.tex"],
    newtheorem: { lemma: "lemma", theorem: "theorem" },
    bibliography: [],
    envs: [
      { id: "lem:a", kind: "lemma", envName: "lemma", label: "lem:a", title: null, body: "\\label{lem:a}\nSuppose $X$ is bounded. Then $\\E[Y] < \\infty$, as in \\eqref{eq:key}.", proof: "Bound $Y$ by \\eqref{eq:key}.", proofLines: { file: "sec.tex", from: 4, to: 6, env: "proof", label: null }, lines: { file: "sec.tex", from: 1, to: 3, env: "lemma", label: "lem:a" }, refs: ["eq:key"] },
      { id: "thm:b", kind: "theorem", envName: "theorem", label: "thm:b", title: null, body: "\\label{thm:b}\nThe result holds.", proof: null, proofLines: null, lines: { file: "main.tex", from: 16, to: 18, env: "theorem", label: "thm:b" }, refs: [] },
    ],
  };
  const core = {
    qid: "x",
    symbols: [],
    assumptions: [{ id: "ass:bounded", condition: "Suppose $X$ is bounded.", tex_locator: { file: "sec.tex", from: 1, to: 3, env: "lemma", label: "lem:a" } }],
    definitions: [],
    statements: [
      { id: "lem:a", kind: "lemma", statement: "\\label{lem:a}\nSuppose $X$ is bounded. Then $\\E[Y] < \\infty$, as in \\eqref{eq:key}. [Hypotheses: ass:bounded]", depends_on: ["ass:bounded"], proof_tex: "Bound $Y$ by \\eqref{eq:key}.", status: "to-prove", tex_locator: { file: "sec.tex", from: 1, to: 3, env: "lemma", label: "lem:a" } },
      { id: "thm:b", kind: "theorem", statement: "\\label{thm:b}\nThe result holds.", depends_on: ["lem:a"], status: "to-prove", tex_locator: { file: "main.tex", from: 16, to: 18, env: "theorem", label: "thm:b" } },
      { id: "lem:lost", kind: "lemma", statement: "A lemma the source does not contain anywhere at all.", depends_on: [], status: "to-prove" },
    ],
    target_estimand: "t",
    bibliography: [],
  } as unknown as Core;
  const px = paperIndex(flat, lineMap, envs);

  it("a statement is cut through the line map with its \\begin/\\end lines, its proof likewise; a premise to its own line; an absent node falls back to the core text", () => {
    const e = nodeExcerpts(px, core, "lem:a");
    expect(e.statement.range).toEqual([6, 8]);
    expect(e.statement.text.startsWith("\\begin{lemma}")).toBe(true);
    expect(e.statement.text.endsWith("\\end{lemma}")).toBe(true);
    expect(e.proof!.range).toEqual([9, 11]);
    expect(e.refs).toContain("eq:key");
    // A premise sliced out of a result is cut to its own line; an absent node falls back to the core text.
    expect(nodeExcerpts(px, core, "ass:bounded").statement.range).toEqual([7, 7]);
    const lost = nodeExcerpts(px, core, "lem:lost");
    expect(lost.statement.range).toBeNull();
    expect(lost.statement.text).toBe("A lemma the source does not contain anywhere at all.");
  });

  it("the setup runs to the first result, without the bibliography; referenced passages exclude core nodes and shown text; only cited entries are shown", () => {
    const s = setupExcerpt(px);
    expect(s.macros).toContain("\\newcommand{\\E}");
    expect(s.setup).toContain("Let $Y$ be the outcome");
    expect(s.setup).not.toContain("\\begin{lemma}");
    const refs = referencedPassages(px, core, [nodeExcerpts(px, core, "lem:a")]);
    expect(refs.passages.map((p) => p.label)).toEqual(["eq:key"]);
    expect(refs.passages[0]!.excerpt.text).toContain("Remark text about the key display");
    // The bibliography is dropped from the setup; only the entries a shard node cites are shown.
    expect(withoutBibliography(["a", "\\begin{thebibliography}{9}", "\\bibitem{k} K.", "\\end{thebibliography}", "\\bibliography{refs}", "b"])).toEqual(["a", "b"]);
    expect(citesIn("see \\citet[Thm 2]{bartlett2008, vdv} and \\cite{x}")).toEqual(["bartlett2008", "vdv", "x"]);
    const p2 = paperIndex(["\\begin{thebibliography}{9}", "\\bibitem[B(2008)]{bartlett2008} Bartlett,", "Fast rates.", "\\bibitem{other} O.", "\\end{thebibliography}"].join("\n"), null, null);
    expect(bibliographyEntries(p2, ["bartlett2008", "missing"])).toEqual([{ key: "bartlett2008", text: "\\bibitem[B(2008)]{bartlett2008} Bartlett, Fast rates." }]);
  });

  it("the compact core: a printed excerpt stands in for a node's text only when it IS that text", () => {
    const c = fixtureCore();
    const cond = c.assumptions.find((a) => a.id === "ass:overlap")!.condition;
    const ex = (text: string) => new Map([["ass:overlap", { id: "ass:overlap", statement: { where: "main.tex lines 14–14", text, range: [14, 14] as [number, number] }, proof: null }]]) as never;
    expect(compactCore(c, new Set(["ass:overlap"]), ex(cond))).toContain('"condition":"(as printed, below)"');
    // the printed line also carries the next sentence: the node's own text is shown
    const withNext = compactCore(c, new Set(["ass:overlap"]), ex(`${cond} The next condition bounds the`));
    expect(withNext).not.toContain("(as printed, below)");
    expect(withNext).toContain(JSON.stringify(cond).slice(1, -1));
  });

  it("the compact core: own nodes whole (no inline readings), what they use in full text, every other node clipped and unwired", () => {
    const big = { ...core, statements: [...core.statements, { id: "thm:far", kind: "theorem", statement: "x".repeat(2000), depends_on: [], proof_tex: "far proof", status: "to-prove" }] } as unknown as Core;
    const text = compactCore(big, new Set(["lem:a"]));
    expect(text).toContain("Bound $Y$ by");
    expect(text).not.toContain("far proof");
    expect(text).not.toContain("pinned_readings_binding");
    // Every other node: one line, id + the head of its text (the kind in the group header), no wiring.
    expect(text.split("\n")).toContain(`- thm:far: ${"x".repeat(UNRELATED_TEXT_MAX)} …`);
    expect(UNRELATED_TEXT_MAX).toBe(120);
    // A statement using the shard's node is context like any other: clipped, without its wiring.
    const b = text.split("\n").find((l) => l.startsWith("- thm:b:"))!;
    expect(b).not.toContain("depends_on");
    expect(text).not.toContain("bibliography");
    // A hypotheses-only shard lists the other nodes by id.
    expect(compactCore(big, new Set(["lem:a"]), new Map(), { idsOnly: true })).toMatch(/^result: .*thm:far/m);
  });

  it("the id list of a node shard names the paper's nodes, not the conditions V1.5 appended; a proof change is shown whole, apart from the capped proof", () => {
    const pin = { id: "ass:pin-1", condition: "$Y$ is bounded.", bookkeeping: { added_by: "V1.5", reason: "pins reading of lem:a: x" } };
    const change = `[Proof change (minimal patch): ${"step. ".repeat(4000)}end of the change]`;
    const c = { ...core, assumptions: [...core.assumptions, pin], statements: core.statements.map((st) => (st.id === "lem:a" ? { ...st, proof_tex: `The printed proof.\n${change}` } : st)) } as unknown as Core;
    const ids = compactCore(c, new Set(["lem:a"]), new Map(), { idsOnly: true });
    const list = ids.slice(ids.indexOf("Every other node"));
    expect(list).not.toContain("ass:pin-1");
    expect(compactCore(c, new Set(["lem:a"])).slice(compactCore(c, new Set(["lem:a"])).indexOf("Every other node"))).toContain("ass:pin-1");
    const own = JSON.parse(ids.split("\n").find((l) => l.startsWith('{"id":"lem:a"'))!) as { proof_tex: string; proof_change: string };
    expect(own.proof_change).toBe(change);
    expect(own.proof_tex).toBe("The printed proof.");
  });
});

describe("grading comparison and the global pass", () => {
  const v = (id: string, over: Partial<V15NodeVerdict> = {}): V15NodeVerdict => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "d", witness: null, bookkeeping_assumption: null, reading: null, ...over });

  it("a global fix is merged field by field: a shard's explicit nulls replace nothing, and a second value the runner cannot apply goes to the transcriber", () => {
    const empty = { add_depends_on: null, remove_depends_on: null, wire_into: null, unwire_from: null, extend_to: null, new_assumption: null, setting: null };
    const na = (id: string) => ({ id, env: null, from: "Assume", to: "holds.", wire_into: ["thm:x"] });
    // (a reply under the strict schema carries every key: the shard's are null where it had nothing to say)
    const merged = mergeFix({ ...empty, add_depends_on: ["ass:a"] }, { ...empty, new_assumption: na("ass:setup"), extend_to: "almost surely", setting: "the design is fixed" })!;
    expect(merged).toEqual({ ...empty, add_depends_on: ["ass:a"], new_assumption: na("ass:setup"), extend_to: "almost surely", setting: "the design is fixed" });
    // two different new assumptions, two settings: one is applied, the other is said in words — none dropped
    const both = mergeFix({ ...empty, new_assumption: na("ass:one"), setting: "s1" }, { ...empty, new_assumption: na("ass:two"), setting: "s2" })!;
    expect(both.new_assumption).toEqual(na("ass:one"));
    expect(both.setting).toBe("s1\ns2");
    expect(both.also).toMatch(/cannot merge with the first — make it yourself: new_assumption: \{"id":"ass:two"/);
    expect(mergeFix({ ...empty, extend_to: "x" }, { ...empty, extend_to: "x" })!.also).toBeUndefined();
    const out = applyCrossNode([v("thm:x", { fix: { ...empty, add_depends_on: ["ass:a"] } })], [{ id: "thm:x", kind: "wiring", detail: "a setup fact", fix: { ...empty, new_assumption: na("ass:setup") }, witness: null }]);
    expect(out[0]!.fix).toMatchObject({ add_depends_on: ["ass:a"], new_assumption: na("ass:setup") });
  });

  it("cross-node entries: wiring → drift with the fix merged; patch consistency only lowers a grade", () => {
    const out = applyCrossNode(
      [v("thm:x", { fix: { add_depends_on: ["ass:a"] } }), v("thm:p"), v("ass:patch-1", { correctness: "bookkeeping", bookkeeping_assumption: { condition: "c", reason: "r" } }), v("lem:y")],
      [
        { id: "thm:x", kind: "wiring", detail: "inherits ass:b", fix: { add_depends_on: ["ass:b"] }, witness: null },
        { id: "thm:p", kind: "patch_consistency", detail: "conflicts", fix: null, witness: "shown" },
        { id: "ass:patch-1", kind: "patch_consistency", detail: "unsure", fix: null, witness: null },
      ],
    );
    expect(out[0]).toMatchObject({ faithfulness: "drift", fix: { add_depends_on: ["ass:a", "ass:b"] } });
    expect(out[1]).toMatchObject({ correctness: "error", witness: "shown" });
    expect(out[2]).toMatchObject({ correctness: "unclear", bookkeeping_assumption: null });
    expect(out[3]).toEqual(v("lem:y"));
  });
});

// ---------------------------------------------------------------------------------------------
// Stage-level: the sharded path inside runStageV1_5
// ---------------------------------------------------------------------------------------------

/** `which`: "A" the first time a node is graded (grouping A runs first), "B" the second. */
type Grader = (id: string, which: "A" | "B") => Partial<V15NodeVerdict>;

/** A fake codex answering by reply schema: shards grade their NODES TO GRADE with `grade`, an
 * the global pass with `global`. `inFlight.max`: the most calls
 * running at once (each call yields for `delayMs`). */
function fakeCodex(
  calls: CodexRunInput[],
  opts: { grade?: Grader; global?: (prompt: string) => Record<string, unknown>; inFlight?: { now: number; max: number }; delayMs?: number } = {},
): typeof runCodex {
  const base = (id: string) => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "reproduced", witness: null, fix: null, bookkeeping_assumption: null, reading: null, minimality: false });
  const seen = new Map<string, number>();
  return (async (input: CodexRunInput) => {
    const sym = symbolReply(input);
    if (sym !== null) return { stdout: sym, stderr: "" };
    calls.push(input);
    if (opts.inFlight) {
      opts.inFlight.now += 1;
      opts.inFlight.max = Math.max(opts.inFlight.max, opts.inFlight.now);
      await new Promise((r) => setTimeout(r, opts.delayMs ?? 5));
      opts.inFlight.now -= 1;
    }
    const toGrade = (input.prompt.match(/=== NODES TO GRADE[^\n]*===\n\n(?:[^\n-][^\n]*\n\n)?((?:- .*\n?)+)/)?.[1] ?? "").split("\n").filter(Boolean).map((l) => l.slice(2));
    let reply: unknown;
    if (input.outputSchema === SHARD_REPLY) {
      const which = (id: string): "A" | "B" => {
        const n = (seen.get(id) ?? 0) + 1;
        seen.set(id, n);
        return n === 1 ? "A" : "B";
      };
      reply = { summary: "s", nodes: toGrade.map((id) => ({ ...base(id), ...(opts.grade?.(id, which(id)) ?? {}) })) };
    } else if (input.outputSchema === GLOBAL_REPLY) {
      reply = { verdict: "PASS", summary: "g", patch_review: null, rejection_verdicts: null, cross_node: [], ...(opts.global?.(input.prompt) ?? {}) };
    } else {
      throw new Error("the single referee was called on the sharded path");
    }
    return { stdout: JSON.stringify(withOwnerExplanations(reply)), stderr: "" };
  }) as typeof runCodex;
}

async function stageDir(): Promise<{ runDir: string; state: StateJson; args: (codex: typeof runCodex, dryRun?: boolean) => VerifyStageArgs }> {
  const root = await mkdtemp(path.join(os.tmpdir(), "verify-shards-"));
  tmpDirs.push(root);
  const runDir = path.join(root, "runs", "toy");
  await mkdir(path.join(runDir, "discovery", "cited_sources"), { recursive: true });
  await writeFile(path.join(runDir, VERIFY_FILES.coreJson), JSON.stringify(fixtureCore(), null, 2));
  await writeFile(path.join(runDir, VERIFY_FILES.coreTranscribed), JSON.stringify(fixtureCore(), null, 2));
  await writeFile(path.join(runDir, VERIFY_FILES.flatTex), await readFile(FLAT_FIXTURE, "utf8"));
  await writeFile(path.join(runDir, "discovery", "cited_sources", "vandervaart1998.txt"), "Theorem 3.1 (Delta method). If ... then ...");
  const state = createVerifyInitialState("toy", { phase: "v1", source: { input: "p", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
  return { runDir, state, args: (codex, dryRun = false) => ({ repoRoot: root, qid: "toy", runDir, state, deps: { runCodex: codex }, dryRun, log: () => {} }) };
}

async function review(runDir: string): Promise<V15Review> {
  return JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.v15Review), "utf8")) as V15Review;
}

describe("sharded V1.5 inside the stage", () => {
  it("one shard call per level + the global pass, each prompt persisted beside its reply; the review carries the per-node fields", async () => {
    const h = await stageDir();
    const calls: CodexRunInput[] = [];
    const res = await runStageV1_5(h.args(fakeCodex(calls)));
    expect(res.status).toBe("completed");
    // Three levels (hypotheses and the definition; the two leaf lemmas; the theorem), one shard each.
    expect(calls.map((c) => c.outputSchema)).toEqual([...Array(3).fill(SHARD_REPLY), GLOBAL_REPLY]);
    // Shards see excerpts, not the whole paper; the global pass sees the paper and the shard verdicts.
    expect(calls[0]!.prompt).toContain("=== PAPER EXCERPTS FOR THE NODES YOU GRADE");
    expect(calls[0]!.prompt).not.toContain("=== PAPER (flattened LaTeX) ===");
    expect(calls[3]!.prompt).toContain("=== PAPER (flattened LaTeX) ===");
    expect(calls[3]!.prompt).toContain("=== SHARD VERDICTS");
    expect(calls[3]!.prompt).not.toContain("=== NODES TO GRADE");
    const r = await review(h.runDir);
    expect(r.nodes.map((n) => n.id).sort()).toEqual([...FIXTURE_IDS].sort());
    for (const n of r.nodes) expect(n).toMatchObject({ graded: "fresh", shards: [`L${LEVEL[n.id]}-1`] });
    const m = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.v15RefereeMetrics), "utf8"));
    expect(m).toMatchObject({ cycles: [] });
    expect(m).not.toHaveProperty("mode");
    expect(m.total_bytes).toBe(calls.reduce((a, c) => a + Buffer.byteLength(c.prompt, "utf8"), 0));
    // Every live call persists its prompt under discovery/prompts, beside its reply in codex_raw/.
    const dir = path.join(h.runDir, VERIFY_FILES.v15Prompts);
    const files = await readdir(dir);
    const tags = files.map((f) => f.split("__")[0]!);
    expect(tags).toEqual(expect.arrayContaining(["v1_5_symbols_1", "v1_5_shard_L0-1", "v1_5_global"]));
    const saved = await Promise.all(files.map((f) => readFile(path.join(dir, f), "utf8")));
    for (const c of calls) expect(saved).toContain(c.prompt);
    const raw = (await readdir(path.join(h.runDir, "codex_raw"))).map((f) => f.split("__")[0]!);
    for (const t of tags) expect(raw).toContain(t);
    // One pipeline.jsonl line per referee pass, with the call count and prompt bytes of the log line.
    const pl = (await readFile(path.join(h.runDir, "pipeline.jsonl"), "utf8")).trim().split("\n").map((l) => JSON.parse(l) as { stage: string; status: string; message: string; duration_ms: number });
    expect(pl.map((e) => [e.stage, e.status])).toEqual([["V1.5", "symbol_pass"], ["V1.5", "referee_pass"]]);
    expect(pl[0]!.message).toMatch(/^symbol referee: .*; 1 call\(s\), \d+ prompt bytes$/);
    expect(pl[1]!.message).toMatch(/^sharded referee: .*; 4 call\(s\), \d+ prompt bytes$/);
  });

  it("levels: leaves first; a level-2 shard reads the level-1 verdicts; metrics per level", async () => {
    const h = await stageDir();
    const calls: CodexRunInput[] = [];
    const lines: string[] = [];
    await runStageV1_5({ ...h.args(fakeCodex(calls)), log: (m) => lines.push(m) });
    const graded = (c: CodexRunInput): string => c.prompt.match(/=== NODES TO GRADE[^\n]*===\n\n(?:[^\n-][^\n]*\n\n)?((?:- .*\n?)+)/)![1]!;
    expect(graded(calls[0]!)).not.toMatch(/lem:|thm:/);
    expect(graded(calls[1]!)).toMatch(/lem:ipw-identity/);
    expect(graded(calls[2]!).trim()).toBe("- thm:ate-identification");
    // The theorem's shard is shown the lemma's final verdict; the leaves have no such section.
    for (const c of calls.slice(2, 3)) {
      expect(c.prompt).toContain("=== DEPENDENCY VERDICTS (binding");
      expect(c.prompt).toContain("- lem:ipw-identity (lemma): ok — used by thm:ate-identification");
    }
    for (const c of calls.slice(0, 2)) expect(c.prompt).not.toContain("=== DEPENDENCY VERDICTS");
    const m = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.v15RefereeMetrics), "utf8"));
    expect(m.levels.map((l: { level: number; nodes: string[]; calls: number }) => [l.level, l.nodes.length, l.calls])).toEqual([[0, 3, 1], [1, 2, 1], [2, 1, 1]]);
    expect(m.levels.reduce((a: number, l: { bytes: number }) => a + l.bytes, 0)).toBe(m.shard_bytes);
    for (const l of m.levels) expect(l.wall_ms).toBeGreaterThanOrEqual(0);
    expect(lines.find((l) => l.startsWith("sharded referee:"))).toMatch(/^sharded referee: levels: L0 3 \(1 shard\(s\) 3 nodes, \d+ KB content\) · L1 2 \(1 shard\(s\) 2 nodes, \d+ KB content\) · L2 1 \(1 shard\(s\) 1 nodes, \d+ KB content\); 3 shard\(s\) \(3\+2\+1 nodes\)/);
  });

  it("delta: carried verdicts are never sharded; the global pass sees them as carried", async () => {
    const h = await stageDir();
    await runStageV1_5(h.args(fakeCodex([])));
    // Change one node's text in the transcription: only it (and what rests on it) is graded again.
    const tp = path.join(h.runDir, VERIFY_FILES.coreTranscribed);
    const core = JSON.parse(await readFile(tp, "utf8")) as Core;
    core.statements.find((s) => s.id === "lem:delta-method")!.statement += " (as quoted)";
    await writeFile(tp, JSON.stringify(core, null, 2));
    h.state.stage_completed = "V1";
    const calls: CodexRunInput[] = [];
    await runStageV1_5(h.args(fakeCodex(calls)));
    const shardCalls = calls.filter((c) => c.outputSchema === SHARD_REPLY);
    expect(shardCalls).toHaveLength(1);
    for (const c of shardCalls) {
      expect(c.prompt).toContain("=== NODES TO GRADE (1 of 6) ===\n\n- lem:delta-method");
    }
    // The global pass checks the node graded and its neighbours (none here); the transcription moved,
    // so it reads the whole paper.
    const glob = calls.find((c) => c.outputSchema === GLOBAL_REPLY)!;
    expect(glob.prompt).toContain("Not shown (unchanged since an earlier global pass checked them; their verdicts stand): ass:unconfoundedness, ass:overlap, def:propensity, lem:ipw-identity, thm:ate-identification");
    expect(glob.prompt).toContain("=== PAPER (flattened LaTeX) ===");
    const r = await review(h.runDir);
    expect(r.nodes.find((x) => x.id === "lem:delta-method")).toMatchObject({ graded: "fresh", shards: ["L1-1"] });
    expect(r.nodes.filter((x) => x.graded === "carried")).toHaveLength(5);
  });

  it("delta global pass: the node graded with its neighbours shown (as carried), the excerpts in place of the paper while the transcription is the one a global pass read whole", async () => {
    const h = await stageDir();
    await runStageV1_5(h.args(fakeCodex([])));
    const sha = (await review(h.runDir)).global_paper;
    expect(sha).toMatch(/^[0-9a-f]{64}$/);
    // Withdraw one cached verdict, the transcription untouched: only that node is graded again.
    delete h.state.verify!.confirmed!["lem:ipw-identity"];
    h.state.stage_completed = "V1";
    const calls: CodexRunInput[] = [];
    await runStageV1_5(h.args(fakeCodex(calls)));
    const glob = calls.find((c) => c.outputSchema === GLOBAL_REPLY)!;
    expect(glob.prompt).not.toContain("=== PAPER (flattened LaTeX) ===");
    expect(glob.prompt).toContain("=== PAPER EXCERPTS FOR THE NODES SHOWN");
    expect(glob.prompt).toContain("Not shown (unchanged since an earlier global pass checked them; their verdicts stand): ass:unconfoundedness, lem:delta-method");
    // A neighbour's verdict is shown, marked carried.
    expect(glob.prompt).toMatch(/\{"id":"thm:ate-identification"[^\n]*"graded":"carried"/);
    expect(glob.prompt).not.toMatch(/\{"id":"lem:delta-method"/);
    expect((await review(h.runDir)).global_paper).toBe(sha);
    // The node graded keeps its full material; a carried neighbour is its text, wiring and verdict
    // line — no other field of its record, no excerpt of its statement or proof.
    const coreSec = glob.prompt.slice(glob.prompt.indexOf("=== TYPED CORE"), glob.prompt.indexOf("=== SHARD VERDICTS"));
    const rec = (id: string): Record<string, unknown> => JSON.parse(coreSec.split("\n").find((l) => l.startsWith(`{"id":"${id}"`))!);
    // … with its paper label: what a `\\ref` in a node in full resolves to
    expect(Object.keys(rec("thm:ate-identification")).sort()).toEqual(["carried", "depends_on", "id", "kind", "label", "statement"]);
    expect(rec("thm:ate-identification").label).toBe("thm:ate");
    expect(coreSec).toContain("its whole record is in discovery/core.json (look it up by its id)");
    expect(rec("thm:ate-identification").depends_on).toContain("lem:ipw-identity");
    expect(rec("lem:ipw-identity")).toHaveProperty("status");
    expect(rec("lem:ipw-identity")).not.toHaveProperty("carried");
    expect(rec("ass:overlap")).toMatchObject({ carried: true, condition: expect.any(String) });
    for (const k of ["tex_locator", "free_symbols", "proof_change"]) expect(rec("ass:overlap")).not.toHaveProperty(k);
    const excerpts = glob.prompt.slice(glob.prompt.indexOf("=== PAPER EXCERPTS FOR THE NODES SHOWN IN FULL"));
    expect(excerpts).toContain("### lem:ipw-identity");
    expect(excerpts).not.toContain("### thm:ate-identification");
    expect(excerpts).not.toContain("### ass:overlap");
  });

  it("a carried verdict whose stored text does not compile is graded afresh at pass start, the compiler's line in its shard's prompt", async () => {
    const h = await stageDir();
    await runStageV1_5(h.args(fakeCodex([])));
    const r1 = await review(h.runDir);
    const id = "lem:delta-method";
    const curly = "Under the “smooth” map the limit holds";
    await writeFile(path.join(h.runDir, VERIFY_FILES.v15Review), JSON.stringify({ ...r1, nodes: r1.nodes.map((n) => (n.id === id ? { ...n, reading: { reading: curly, evidence: "x" } } : n)) }));
    h.state.stage_completed = "V1";
    const calls: CodexRunInput[] = [];
    const logs: string[] = [];
    expect((await runStageV1_5({ ...h.args(fakeCodex(calls)), log: (m: string) => logs.push(m) })).status).toBe("completed");
    const shards = calls.filter((c) => c.outputSchema === SHARD_REPLY);
    const shardNodes = shards.flatMap((c) => (c.prompt.match(/=== NODES TO GRADE[^\n]*===\n\n((?:- .*\n?)+)/)?.[1] ?? "").split("\n").filter(Boolean));
    expect(shardNodes).toEqual([`- ${id}`]);
    expect(shards[0]!.prompt).toContain("=== TEXTS ON FILE THAT DO NOT COMPILE");
    expect((await review(h.runDir)).nodes.find((x) => x.id === id)!.graded).toBe("fresh");
    expect(logs).toContain(`referee texts: 1 carried verdict(s) with a text that does not compile are graded afresh (${id})`);
    expect(logs.find((l) => l.startsWith("delta review: why re-graded"))).toContain("1 text does not compile");
  });

  it("one node never halts the pass: a grade that breaks the contract past its retry is set aside — its verdict on file kept unconfirmed, the rest recorded, graded afresh next pass", async () => {
    const h = await stageDir();
    expect((await runStageV1_5(h.args(fakeCodex([])))).status).toBe("completed");
    const X = "lem:ipw-identity";
    const before = (await review(h.runDir)).nodes.find((n) => n.id === X)!;
    const tp = path.join(h.runDir, VERIFY_FILES.coreTranscribed);
    const core = JSON.parse(await readFile(tp, "utf8")) as Core;
    core.statements.find((s) => s.id === X)!.statement += " (restated)";
    await writeFile(tp, JSON.stringify(core, null, 2));
    h.state.stage_completed = "V1";
    // Every grading of X (both groupings, first reply and retry) breaks the contract; the others comply.
    const logs: string[] = [];
    const res = await runStageV1_5({ ...h.args(fakeCodex([], { grade: (id) => (id === X ? { witness_regime: "in_scope" } : {}) })), log: (m: string) => logs.push(m) });
    expect(res.status).toBe("checkpoint");
    expect(res.message).toMatch(/^1 node\(s\) broke the output contract twice and were set aside \(lem:ipw-identity — referee shard_L\d-1: node "lem:ipw-identity" carries a witness_regime/);
    expect(logs.filter((l) => l.startsWith(`node ${X}: its grading broke the output contract twice — set aside (its verdict on file kept, not confirmed; graded afresh next pass)`))).toHaveLength(1);
    expect(logs.find((l) => l.startsWith("sharded referee:"))).toContain("1 node(s) set aside past the retry (lem:ipw-identity)");
    expect(logs.some((l) => l.startsWith("1 node(s) set aside this pass, graded afresh next pass: lem:ipw-identity — "))).toBe(true);
    const r = await review(h.runDir);
    const n = r.nodes.find((x) => x.id === X)!;
    expect(n).toMatchObject({ graded: "carried", correctness: before.correctness, detail: before.detail });
    expect(n.basis).toBeUndefined();
    expect(h.state.verify!.confirmed![X]).toBeUndefined();
    // The node above it was graded and recorded.
    expect(r.nodes.find((x) => x.id === "thm:ate-identification")!.graded).toBe("fresh");
    expect(h.state.verify!.confirmed!["thm:ate-identification"]).toBeDefined();
    // The next pass grades only the node set aside.
    const logs2: string[] = [];
    expect((await runStageV1_5({ ...h.args(fakeCodex([])), log: (m: string) => logs2.push(m) })).status).toBe("completed");
    expect(logs2.find((l) => l.startsWith("delta review:"))).toMatch(/^delta review: 1 of 6 node\(s\) to grade afresh \(lem:ipw-identity\)/);
  });

  it("a halt keeps what the pass graded: a pass that halts in L1 after L0 and two L1 shards finished resumes with those verdicts carried and grades only the rest", async () => {
    const h = await stageDir();
    const nodesOf = (prompt: string): string[] => (prompt.match(/=== NODES TO GRADE[^\n]*===\n\n(?:[^\n-][^\n]*\n\n)?((?:- .*\n?)+)/)?.[1] ?? "").split("\n").filter(Boolean).map((l) => l.slice(2));
    const good = fakeCodex([]);
    // One lemma per shard: L1 is two shards, one node each. The shard of lem:delta-method fails
    // (after the one of lem:ipw-identity has answered); the call error ends the pass.
    const failing = (async (input: CodexRunInput) => {
      if (input.outputSchema === SHARD_REPLY && nodesOf(input.prompt).includes("lem:delta-method")) {
        await new Promise((r) => setTimeout(r, 50));
        throw new Error("codex exited 1");
      }
      return good(input);
    }) as typeof runCodex;
    const logs: string[] = [];
    await expect(runStageV1_5({ ...h.args(failing), refereeShardLimits: { lemmas: 1 }, log: (m: string) => logs.push(m) })).rejects.toThrow("codex exited 1");
    const kept = ["ass:overlap", "ass:unconfoundedness", "def:propensity", "lem:ipw-identity"];
    expect(logs.filter((l) => /^shard L1-\d: /.test(l))).toHaveLength(2);
    expect(logs.some((l) => l.startsWith("halted at L1: 4 verdict(s) graded before the halt kept"))).toBe(true);
    const lp = h.state.verify!.level_pause!;
    expect(lp).toMatchObject({ level: "L1", via: "halt", errors: [] });
    expect(Object.keys(lp.carry).sort()).toEqual(kept);
    expect([...lp.graded!].sort()).toEqual(kept);
    const r1 = await review(h.runDir);
    expect(r1.nodes.filter((n) => n.graded === "fresh").map((n) => n.id).sort()).toEqual(kept);
    expect(r1.nodes.find((n) => n.id === "lem:ipw-identity")).toMatchObject({ basis: lp.carry["lem:ipw-identity"], shards: [expect.stringMatching(/^L1-\d/)] });
    // The resume carries them and grades only the rest.
    const calls: CodexRunInput[] = [];
    const logs2: string[] = [];
    expect((await runStageV1_5({ ...h.args(fakeCodex(calls)), refereeShardLimits: { lemmas: 1 }, log: (m: string) => logs2.push(m) })).status).toBe("completed");
    expect(logs2.find((l) => l.startsWith("delta review:"))).toMatch(/^delta review: 2 of 6 node\(s\) to grade afresh \((lem:delta-method, thm:ate-identification|thm:ate-identification, lem:delta-method)\), 4 verdict\(s\) carried/);
    expect([...new Set(calls.filter((c) => c.outputSchema === SHARD_REPLY).flatMap((c) => nodesOf(c.prompt)))].sort()).toEqual(["lem:delta-method", "thm:ate-identification"]);
    expect(logs2.some((l) => l.startsWith("level "))).toBe(true);
    expect(h.state.verify!.level_pause).toBeUndefined();
  });

  it("dry run: the whole sharded wiring with synthetic grades and no model call", async () => {
    const h = await stageDir();
    const calls: CodexRunInput[] = [];
    const res = await runStageV1_5(h.args(fakeCodex(calls), true));
    expect(res.status).toBe("completed");
    expect(calls).toHaveLength(0);
    const r = await review(h.runDir);
    for (const n of r.nodes) expect(n).toMatchObject({ shards: [`L${LEVEL[n.id]}-1`], correctness: "ok" });
    const m = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.v15RefereeMetrics), "utf8"));
    expect(m.calls.map((c: { kind: string }) => c.kind)).toEqual([...Array(3).fill("shard"), "global"]);
    expect(m.calls.map((c: { tag: string }) => c.tag)).toEqual(["shard_L0-1", "shard_L1-1", "shard_L2-1", "global"]);
    expect(h.state.verify!.dry_run).toBe(true);
  });
});

// ---------------------------------------------------------------------------------------------
// Fix as you go: a level with an error pauses the grading for the fixer
// ---------------------------------------------------------------------------------------------

/** The fixer's reply for the fixture: `lem:ipw-identity` corrected, with one patch hypothesis. */
function ipwPatch(): PatchFile {
  return {
    key_results: ["thm:ate-identification"],
    key_contribution: "identification of the ATE by inverse weighting",
    patches: [
      {
        node: "lem:ipw-identity",
        corrected_statement: "Under Assumption \\ref{ass:overlap} and $e(X) \\ge \\eta > 0$, $E[DY/e(X)] = E[Y(1)]$.",
        proof_note: "Bound DY/e(X) by |Y|/eta, then condition on X and apply the tower property.",
        owner_explanation: { claim: "Lemma 1 claims the weighting identity under overlap.", defects: [{ kind: "out_of_domain", step_unit: "lem:ipw/proof/1/1", uses: "integrability of the weight $1/e(X)$", assumed_on: "propensity scores bounded away from zero", applied_at: "every propensity score allowed by overlap", detail: null }], why: { objects: ["$e(X)=1/n$ on a set of probability $1/2$"], consequence: "$E\\{1/e(X)\\}=n/2+1\\to\\infty$" }, fix: "The fix bounds it away from zero.", gives_up: null },
      },
    ],
    unfixable: [],
  } as unknown as PatchFile;
}

/** The sharded fake plus the V1 fixer: a patch-mode call returns `fixer()` and is counted. */
function withFixer(codex: typeof runCodex, fixer: () => PatchFile, count: { fixer: number }): typeof runCodex {
  return (async (input: CodexRunInput) => {
    if (input.outputSchema === PATCH_REPLY_JSON_SCHEMA) {
      count.fixer += 1;
      return { stdout: JSON.stringify(fixer()), stderr: "" };
    }
    return codex(input);
  }) as typeof runCodex;
}

const shardTags = (calls: CodexRunInput[]): string[] =>
  calls.filter((c) => c.outputSchema === SHARD_REPLY).map((c) => c.prompt.match(/=== NODES TO GRADE[^\n]*===\n\n(?:[^\n-][^\n]*\n\n)?((?:- .*\n?)+)/)![1]!.trim());
const levelsOf = async (runDir: string): Promise<Array<[string, string[]]>> => {
  const m = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.v15RefereeMetrics), "utf8"));
  return m.levels.map((l: { level: number; delta?: boolean; nodes: string[] }) => [`${l.delta ? "fix-" : ""}L${l.level}`, l.nodes]);
};
const inScope = { correctness: "error" as const, witness: "fails when $e(X) \\to 0$", witness_regime: "in_scope" as const, witness_instance: "e(X) = 1/n on a sequence" };

describe("a malformed reply and a failing sibling (sharded referee)", () => {
  const BASE = readFileSync(path.join(TOOLS, "src", "verify", "prompts", "V1.5", "review.txt"), "utf8");
  const SHARD = readFileSync(path.join(TOOLS, "src", "verify", "prompts", "V1.5", "shard.txt"), "utf8");
  const ok = (id: string) => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "d", witness: null, fix: null, bookkeeping_assumption: null, reading: null, minimality: false, weakens_contribution: false, follows_repair: false });
  const reply = (c: RefereeCall): unknown => (c.kind === "shard" ? { summary: "s", nodes: c.nodes.map(ok) } : { verdict: "PASS", summary: "g", patch_review: null, rejection_verdicts: null, cross_node: [] });
  async function input(ask: ShardedRefereeInput["ask"], over: Partial<ShardedRefereeInput> = {}): Promise<ShardedRefereeInput> {
    const core = fixtureCore();
    const ids = [...core.assumptions, ...core.definitions, ...core.statements].map((n) => n.id);
    return {
      core,
      flatTex: await readFile(FLAT_FIXTURE, "utf8"),
      envs: null,
      lineMap: null,
      toGrade: ids,
      totalNodes: ids.length,
      scope: "scope",
      briefs: { base: BASE, shard: SHARD },
      extraSections: () => [],
      globalPrompt: () => "global",
      carried: [],
      isPatchPart: () => false,
      hasPatches: false,
      rejections: [],
      contract: () => [],
      ask,
      log: () => {},
      knownIds: new Set(ids),
      // One lemma per shard: level 1 is two shards.
      limits: { ...DEFAULT_SHARD_LIMITS, lemmas: 1 },
      ...over,
    };
  }

  it("a reply that fails the schema is retried once with the schema's complaint; twice, the shard's nodes are set aside and the pass goes on", async () => {
    const calls: RefereeCall[] = [];
    let bad = 1;
    const once: ShardedRefereeInput["ask"] = async (c) => {
      calls.push(c);
      if (c.tag === "shard_L1-1" && bad-- > 0) return { summary: "s", nodes: "not a list" };
      return reply(c);
    };
    const r = await runShardedReferee(await input(once));
    expect(r.ok).toBe(true);
    if (!r.ok) return;
    expect(calls.map((c) => c.tag)).toContain("shard_L1-1_retry");
    expect(calls.find((c) => c.tag === "shard_L1-1_retry")!.prompt).toContain("does not fit the output schema: nodes: ");
    expect(r.review.nodes).toHaveLength(6);
    expect(r.metrics.set_aside).toEqual([]);
    const always: ShardedRefereeInput["ask"] = async (c) => (c.tag.startsWith("shard_L1-1") ? { summary: "s", nodes: "not a list" } : reply(c));
    const logs: string[] = [];
    const r2 = await runShardedReferee(await input(always, { log: (m) => logs.push(m) }));
    expect(r2.ok).toBe(true);
    if (!r2.ok) return;
    expect(r2.metrics.set_aside).toHaveLength(1);
    expect(r2.metrics.set_aside![0]!.why).toContain("its reply did not parse twice");
    expect(r2.review.nodes).toHaveLength(5);
    expect(logs.some((l) => l.includes("set aside"))).toBe(true);
  });

  it("a shard whose call fails outright lets its siblings finish: the halt hands on their grades too", async () => {
    const wait = (ms: number) => new Promise((res) => setTimeout(res, ms));
    const flaky: ShardedRefereeInput["ask"] = async (c) => {
      if (c.tag === "shard_L1-1") {
        await wait(5);
        throw new Error("the model host went away");
      }
      if (c.tag === "shard_L1-2") await wait(60);
      return reply(c);
    };
    const halted: string[][] = [];
    const inp = await input(flaky, { onHalt: async (graded) => void halted.push(graded.map((v) => v.id).sort()), concurrency: 2 });
    await expect(runShardedReferee(inp)).rejects.toThrow("the model host went away");
    expect(halted).toHaveLength(1);
    // Level 0 whole, and the sibling shard of level 1 that finished after the failure.
    expect(halted[0]).toEqual(["ass:overlap", "ass:unconfoundedness", "def:propensity", expect.stringMatching(/^lem:/)]);
  });
});

describe("fix as you go (sharded referee)", () => {
  /** Pass 1 of the fixture with `lem:ipw-identity` (level 1) graded an error until it is patched. */
  async function pausedAtLevel1(o: { patchRounds?: number; patchLevels?: Record<string, number> } = {}) {
    const h = await stageDir();
    if (o.patchRounds !== undefined) h.state.verify!.patch_rounds = o.patchRounds;
    if (o.patchLevels) h.state.verify!.patch_rounds_by_level = o.patchLevels;
    const flags = { repaired: false, weakens: false };
    const count = { fixer: 0 };
    const calls: CodexRunInput[] = [];
    const lines: string[] = [];
    const grade: Grader = (id) => {
      if (id !== "lem:ipw-identity") return {};
      if (!flags.repaired) return inScope;
      return flags.weakens ? { correctness: "error", witness: "the repair needs eta > 0, which the paper does not assume", weakens_contribution: true } : {};
    };
    const codex = withFixer(
      fakeCodex(calls, { grade, global: () => ({ patch_review: { key_results_ok: true, detail: "the ATE theorem is the headline" } }) }),
      () => {
        flags.repaired = true;
        return ipwPatch();
      },
      count,
    );
    const args = (): VerifyStageArgs => ({ ...h.args(codex), log: (m: string) => lines.push(m) });
    const res = await runStageV1_5(args());
    return { h, flags, count, calls, lines, args, res };
  }

  /** What the pipeline does on a `patch`: spend the round, run V1 in patch mode. */
  async function fixerRound(t: Awaited<ReturnType<typeof pausedAtLevel1>>): Promise<void> {
    countRound(t.h.state.verify!, "error");
    expect((await runStageV1(t.args())).status).toBe("completed");
  }

  it("an error at level 1 pauses the grading: level 2 and the global pass wait; exactly that error goes to the fixer", async () => {
    const t = await pausedAtLevel1();
    expect(t.res.status).toBe("patch");
    expect(shardTags(t.calls)).toHaveLength(2); // L0, L1 — no L2, no global pass
    expect(t.calls.some((c) => c.outputSchema === GLOBAL_REPLY)).toBe(false);
    const directive = JSON.parse(await readFile(path.join(t.h.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(directive).toMatchObject({ mode: "patch", round: 1, findings: [{ id: "lem:ipw-identity", axis: "correctness" }] });
    expect(directive.findings).toHaveLength(1);
    const lp = t.h.state.verify!.level_pause!;
    expect(lp).toMatchObject({ level: "L1", via: "fixer", round: 1, errors: [{ id: "lem:ipw-identity", targets: ["lem:ipw-identity"] }] });
    expect(Object.keys(lp.carry).sort()).toEqual(["ass:overlap", "ass:unconfoundedness", "def:propensity", "lem:delta-method"]);
    const r = await review(t.h.runDir);
    expect(r.paused).toMatchObject({ level: "L1", ids: ["lem:ipw-identity"], ungraded: ["thm:ate-identification"] });
    expect(r.nodes.some((n) => n.id === "thm:ate-identification")).toBe(false);
    expect(t.lines.some((l) => l.startsWith("level L1: 1 error(s) → fixer round 1"))).toBe(true);
  });

  it("interleave: fixer called once, the delta confirms the repair first, then level 2 is graded under the corrected form; one global pass", async () => {
    const t = await pausedAtLevel1();
    await fixerRound(t);
    expect(t.count.fixer).toBe(1);
    const before = t.calls.length;
    const res = await runStageV1_5(t.args());
    expect(res.status).toBe("completed");
    const pass2 = t.calls.slice(before);
    // The delta (the repaired lemma), then the theorem; nothing below re-graded.
    expect(await levelsOf(t.h.runDir)).toEqual([["fix-L1", ["lem:ipw-identity"]], ["L1", ["thm:ate-identification"]]]);
    expect(pass2.map((c) => c.outputSchema)).toEqual([...Array(2).fill(SHARD_REPLY), GLOBAL_REPLY]);
    for (const c of pass2.filter((x) => x.outputSchema === SHARD_REPLY).slice(1)) {
      expect(c.prompt).toContain("- lem:ipw-identity (lemma): ok");
      expect(c.prompt).toContain("confirmed repair: use its corrected form");
      expect(c.prompt).not.toContain("no confirmed repair");
    }
    expect(t.lines).toContain("level L1: 1 error(s) → fixer round 1 → confirmed 1/1; continuing");
    // The delta shard that confirmed the repair graded the fixer's note; the ledger carries no note.
    const entry = t.h.state.verify!.paper_errors!["lem:ipw-identity"]!;
    for (const k of ["owner_explanation", "explanation_patch", "explanation_clarity"]) expect(entry).not.toHaveProperty(k);
    expect(t.h.state.verify!.level_pause).toBeUndefined();
    const r = await review(t.h.runDir);
    expect(r.paused).toBeUndefined();
    expect(r.nodes.find((n) => n.id === "thm:ate-identification")).toMatchObject({ correctness: "ok", graded: "fresh" });
    expect(r.nodes.filter((n) => n.graded === "carried").map((n) => n.id).sort()).toEqual(["ass:overlap", "ass:unconfoundedness", "def:propensity", "lem:delta-method"]);
    expect(t.h.state.verify!.patch_rounds).toBe(1);
  });

  it("a weakening halt inside a level (a main theorem): the confirming pass resumes the grading at that level and presents the receipt; the owner rules", async () => {
    const t = await pausedAtLevel1();
    await fixerRound(t);
    // the lemma is a key result here, so its weakening is the owner's call
    const pf = path.join(t.h.runDir, VERIFY_FILES.patches);
    const onDisk = JSON.parse(await readFile(pf, "utf8")) as PatchFile;
    await writeFile(pf, JSON.stringify({ ...onDisk, key_results: [...onDisk.key_results, "lem:ipw-identity"] }, null, 2));
    t.flags.weakens = true;
    let before = t.calls.length;
    // the patch becomes a suggestion; its receipt waits for the pass that grades it
    const narrowed = await runStageV1_5(t.args());
    expect(narrowed.status).toBe("narrowed");
    expect(t.calls.slice(before).some((c) => c.outputSchema === GLOBAL_REPLY)).toBe(false);
    expect(t.h.state.verify!.weakening_repair).toMatchObject({ status: "pending", unconfirmed: true });
    expect(t.h.state.verify!.level_pause).toMatchObject({ level: "fix-L1", via: "runner" });
    // the confirming pass grades the suggestion as a patch (its weakening accepted) and presents the receipt
    t.flags.weakens = false;
    before = t.calls.length;
    const halt = await runStageV1_5(t.args());
    expect(halt.status).toBe("checkpoint");
    expect(halt.message).toMatch(/weaken a main theorem/);
    expect(t.h.state.verify!.weakening_repair?.status).toBe("pending");
    expect(t.h.state.verify!.weakening_repair!.unconfirmed).toBeUndefined();
    // Resumed at the paused level: the suggestion (its hypothesis, graded clean before, is carried),
    // then the theorem; nothing below the pause is graded again.
    expect(await levelsOf(t.h.runDir)).toEqual([["fix-L1", ["lem:ipw-identity"]], ["L1", ["thm:ate-identification"]]]);
    expect(t.lines.some((l) => l.startsWith("level fix-L1: 1 error(s) → the runner's narrowing → confirmed 1/1; continuing"))).toBe(true);
    expect(t.calls.slice(before).some((c) => c.outputSchema === GLOBAL_REPLY)).toBe(true);
    await ruleOnReceipt(t.h.runDir, t.h.state, { accept: t.h.state.verify!.weakening_repair!.items.map((i) => i.node) });
    before = t.calls.length;
    expect((await runStageV1_5(t.args())).status).toBe("completed");
    // The accepted repair is the suggestion the confirming pass graded: every verdict is carried.
    expect(t.lines).toContain("delta review: 0 of 6 node(s) to grade afresh, 6 verdict(s) carried on an unchanged basis");
    expect(t.calls.length).toBe(before);
    expect(t.count.fixer).toBe(1);
  });

  it("a cap halt inside a level: the round is not opened, the pause is kept for --clear-patch-cap", async () => {
    // The level's 3 error rounds are spent; another level's round would still be open.
    const t = await pausedAtLevel1({ patchRounds: MAX_PATCH_ROUNDS_PER_LEVEL, patchLevels: { L1: MAX_PATCH_ROUNDS_PER_LEVEL } });
    expect(t.res.status).toBe("checkpoint");
    expect(t.res.message).toMatch(/at its cap: error round 4\/3 at level L1/);
    expect(t.h.state.verify!.cap_reached).toMatchObject({ counter: "patch_rounds", origin: "V1.5", level: "L1", nodes: ["lem:ipw-identity"], backstop_hit: false, findings: [{ id: "lem:ipw-identity" }] });
    expect(t.h.state.verify!.level_pause).toMatchObject({ level: "L1", via: "fixer" });
    expect(t.calls.some((c) => c.outputSchema === GLOBAL_REPLY)).toBe(false);
    expect(t.count.fixer).toBe(0);
  });

});
