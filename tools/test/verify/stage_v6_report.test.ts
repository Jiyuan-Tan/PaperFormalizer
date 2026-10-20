import { existsSync } from "node:fs";
import { copyFile, mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { afterEach, describe, expect, it } from "vitest";
import { parseTypedCore } from "../../src/core/core_io.js";
import type { Core } from "../../src/core/schema.js";
import type { FormalizationGraph, GraphNode } from "../../src/graph/types.js";
import { crosswalkFullJsonPath, verifyRunDir } from "../../src/paths.js";
import { createVerifyInitialState } from "../../src/state.js";
import type { CrosswalkEntry, CrosswalkVerdict, StateJson } from "../../src/types.js";
import { sha256File } from "../../src/verify/core_hash.js";
import { parseAxiomReport, type LeanEvidence } from "../../src/verify/lean_evidence.js";
import { buildReport, type ReportInput, type ReportInputStatus } from "../../src/verify/report.js";
import { makeStageV6 } from "../../src/verify/stage_v6_report.js";
import {
  VERIFY_FILES,
  type EnvsJson,
  type V15Review,
  type VerifyFinding,
} from "../../src/verify/types.js";

const FIXTURES = path.join(path.dirname(fileURLToPath(import.meta.url)), "fixtures", "v6");
const QID = "sample_paper";

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const dir of tmpDirs.splice(0)) await rm(dir, { recursive: true, force: true });
});

async function tmpRepo(): Promise<string> {
  const dir = await mkdtemp(path.join(os.tmpdir(), "verify-v6-"));
  tmpDirs.push(dir);
  return dir;
}

async function fixture<T>(name: string): Promise<T> {
  return JSON.parse(await readFile(path.join(FIXTURES, name), "utf8")) as T;
}

async function fixtureCore(): Promise<Core> {
  const file = path.join(FIXTURES, "core.json");
  return parseTypedCore(await readFile(file, "utf8"), `fixture ${file}`);
}

/** A green Lean audit of the three fixture declarations. */
function cleanLean(): LeanEvidence {
  return {
    build: { ok: true, log_tail: "Build completed successfully." },
    sorry_scan: [],
    axioms: {
      "Verify.t1_thm": { axioms: ["propext", "Classical.choice"], clean: true },
      "Verify.l1_lemma": { axioms: [], clean: true },
      "Verify.t2_thm": { axioms: ["propext"], clean: true },
    },
  };
}

const INPUTS: ReportInputStatus = {
  v1_5_review: "present (verdict PASS)",
  crosswalk_full: "present (3 object(s))",
  graph_json: "present (0 node(s))",
  v1_scope: "present (4 environment(s))",
  lean_evidence: "collected",
};

async function baseInput(over: Partial<ReportInput> = {}): Promise<ReportInput> {
  const envs = await fixture<EnvsJson>("envs.json");
  const scope = (await fixture<{ envs: string[] }>("v1_scope.json")).envs;
  return {
    qid: QID,
    envs,
    scope,
    core: await fixtureCore(),
    review: await fixture<V15Review>("v1_5_review.json"),
    findings: [],
    addedAssumptions: [],
    crosswalk: await fixture<CrosswalkEntry[]>("crosswalk_full.json"),
    graph: null,
    lean: cleanLean(),
    warnings: { lint: [], parser: [] },
    flags: {},
    stageCompleted: "5",
    earlyStop: false,
    sourceSha256: "deadbeef",
    inputs: INPUTS,
    ...over,
  };
}

function bucketsOf(json: { results: Array<{ node_id: string; bucket: string }> }): Record<string, string> {
  return Object.fromEntries(json.results.map((r) => [r.node_id, r.bucket]));
}

function finding(over: Partial<VerifyFinding> & Pick<VerifyFinding, "node" | "kind">): VerifyFinding {
  return {
    stage: "F3",
    detail: "detail",
    witness: null,
    at: "2026-09-16T00:00:00.000Z",
    ...over,
  };
}

/** A graph whose `thm:main` node still depends on an undischarged (non-cited) substrate gate. */
function graphWithAssumedGate(): FormalizationGraph {
  const node = (over: Partial<GraphNode> & Pick<GraphNode, "id" | "kind">): GraphNode => ({
    provenance: "from-note",
    nl: { statement: `NL for ${over.id}`, tex_anchor: "", frozen: false },
    lean: { decl_name: null, file: null },
    review: { status: "matched", passed_hash: null },
    proof: { state: "complete", sorry_count: 0 },
    ...over,
  });
  return {
    qid: QID,
    nodes: [
      node({ id: "thm:main", obj_id: "T-2", kind: "theorem", lean: { decl_name: "Verify.t2_thm", file: "Basic.lean" } }),
      node({
        id: "gate:dominated-convergence",
        kind: "gate",
        nl: { statement: "Dominated convergence for the weighted average.", tex_anchor: "", frozen: false },
        gate: { gate_class: "gated" },
      }),
      node({
        id: "gate:cited-moment",
        kind: "gate",
        nl: { statement: "The cited moment bound.", tex_anchor: "", frozen: false },
        gate: { gate_class: "cited", source: "cite:imbens2004" },
      }),
    ],
    edges: [
      { kind: "proof-uses", from: "thm:main", to: "gate:dominated-convergence", source: "declared" },
      { kind: "proof-uses", from: "thm:main", to: "gate:cited-moment", source: "declared" },
    ],
  };
}

describe("buildReport buckets", () => {
  it("a pinned symbol reading is listed in full: its general part, then each scoped clause led by its results' names", async () => {
    const base = await baseInput();
    const st = base.core.statements.find((x) => x.tex_locator?.label)!;
    const name = `${st.kind[0]!.toUpperCase()}${st.kind.slice(1)}~\\ref{${st.tex_locator!.label}}`;
    const symbols = [{ name: "W", meaning: "ok", fix: null, ambiguity: "pinned", reading: { reading: "$W$ is random.", evidence: "Section 2", scoped: [{ results: [st.id], text: "$W$ is bounded." }] }, redefined_at: null, detail: "" }];
    const { json, md } = buildReport({ ...base, review: { ...base.review!, symbols } as never });
    expect(json.symbol_readings).toEqual([{ symbol: "W", reading: `$W$ is random. In ${name}: $W$ is bounded.`, evidence: "Section 2" }]);
    expect(md).toContain("is bounded.");
  });

  it("a hypothesis the proof stage added to a result's Lean is always disclosed: a substrate-gate makes the result conditional, any other is an added condition", async () => {
    const g = graphWithAssumedGate();
    const added = (id: string, classification: string) => ({ ...g.nodes[0]!, id, obj_id: undefined, kind: "assumption", provenance: "agent-introduced", nl: { statement: `NL of ${id}`, tex_anchor: "", frozen: false }, lean: { decl_name: null, file: null }, assumption: { tier: 2, classification } });
    const graph = {
      ...g,
      nodes: [g.nodes[0]!, added("ass:filler:gate", "substrate-gate"), added("ass:filler:reg", "regularity-bookkeeping")],
      edges: [{ kind: "proof-uses", from: "thm:main", to: "ass:filler:gate", source: "declared" }, { kind: "proof-uses", from: "thm:main", to: "ass:filler:reg", source: "declared" }],
    } as never;
    const { json, md } = buildReport(await baseInput({ graph }));
    const main = json.results.find((r) => r.node_id === "thm:main")!;
    expect(main.bucket).toBe("conditional");
    expect(main.assumed_substrate).toEqual([{ id: "ass:filler:gate", description: "NL of ass:filler:gate" }]);
    expect(main.added_premises).toEqual([expect.objectContaining({ label: "ass:filler:reg", statement: "NL of ass:filler:reg", classification: "regularity-bookkeeping" })]);
    expect(md).toContain("ass:filler:reg");
    expect(md).toContain("NL of ass:filler:gate");
  });

  it("anchors a crosswalk row keyed by the graph's obj_id (no core label, no line range) through the graph (live Athey–Imbens, 2026-10-01)", async () => {
    const base = await baseInput();
    const rows = base.crosswalk!;
    const objOf = (i: number): string => `X-${i + 1}`;
    const crosswalk = rows.map((e, i) => ({ ...e, obj_id: objOf(i), tex: { ...e.tex, label: objOf(i), line_range: "" } }));
    // The core id each row resolves to in the baseline (by label or line range).
    const before = buildReport(base).json.results as Array<{ node_id: string; lean: { decl: string } | null }>;
    const coreOf = (decl: string): string => before.find((r) => r.lean?.decl === decl)!.node_id;
    const graph = { qid: "q", nodes: rows.map((e, i) => ({ id: coreOf(e.lean!.decl), obj_id: objOf(i) })), edges: [] } as never;
    expect(bucketsOf(buildReport({ ...base, crosswalk, graph }).json)).toEqual(bucketsOf(buildReport(base).json));
  });

  it("a cited result the run proved is no cited input of the results using it (live Ding: Hájek's CLT discharged from the toolkit)", async () => {
    const base = await baseInput();
    const proved = { id: "lem:cited", kind: "lemma", provenance: "from-note", nl: { statement: "s", tex_anchor: "", frozen: false }, lean: { decl_name: "V.cited", file: "Basic.lean" }, review: { status: "matched", passed_hash: null }, proof: { state: "complete", sorry_count: 0 } };
    const graph = { qid: "q", nodes: [...(base.graph?.nodes ?? []).filter((n) => n.id !== "lem:cited"), proved], edges: base.graph?.edges ?? [] } as never;
    const { json } = buildReport({ ...base, graph });
    const overlap = json.results.find((r) => r.node_id === "thm:overlap")!;
    expect(overlap.cited_hypotheses).toEqual([]);
    expect(bucketsOf(json)["thm:overlap"]).not.toBe("conditional");
  });

  it("a printed result the paper only cites, left cited, is conditional on its source — not unresolved, and the report is not incomplete (live Li–Ding: Fraser's lemma)", async () => {
    const base = await baseInput();
    const core = structuredClone(base.core);
    const aux = core.statements.find((s) => s.id === "lem:aux")!;
    Object.assign(aux, { status: "cited", source: { cite: "fraser1956", locator: "Theorem 2" } });
    const crosswalk = base.crosswalk!.filter((e) => e.tex?.label !== "lem:aux" && !String(e.obj_id ?? "").includes("aux"));
    const { json } = buildReport({ ...base, core, crosswalk });
    const row = json.results.find((r) => r.node_id === "lem:aux")!;
    expect(row.cited_hypotheses.map((c) => c.id)).toContain("lem:aux");
    expect(bucketsOf(json)["lem:aux"]).toBe("conditional");
    expect(json.verdict).not.toBe("incomplete");
  });

  it("separates conditional, bookkeeping and plain verified results", async () => {
    const { json, md } = buildReport(await baseInput());
    expect(bucketsOf(json)).toEqual({
      "thm:overlap": "conditional",
      "lem:aux": "verified_with_bookkeeping",
      "thm:main": "verified",
    });
    expect(json.verdict).toBe("no_error_found");
    expect(json.summary.verified).toBe(1);

    // The conditional row names the cited leaf it rests on; the bookkeeping row names `bk-1`.
    const overlap = json.results.find((r) => r.node_id === "thm:overlap");
    expect(overlap?.cited_hypotheses).toEqual([
      { id: "lem:cited", cite: "imbens2004", locator: "Theorem 3.1", source_check: null },
    ]);
    // a citation never checked against its source says so in the report
    expect(md).toContain("NOT checked against its source");
    expect(json.results.find((r) => r.node_id === "lem:aux")?.bookkeeping.map((b) => b.id)).toEqual([
      "ass:bk-1",
    ]);

    // Every result's source locator and Lean anchor are in the markdown.
    for (const r of json.results) {
      expect(md).toContain(r.locator);
      expect(md).toContain(`${r.lean?.file}:${r.lean?.line}`);
      expect(md).toContain(r.lean?.decl as string);
    }
    expect(md).toContain("NO ERROR FOUND");
    expect(md).toContain("## Conditions assumed");
  });

  it("a refuted finding flips its row and the header verdict", async () => {
    const { json, md } = buildReport(
      await baseInput({
        findings: [
          finding({ node: "thm:main", kind: "refuted", stage: "V1.5", witness: "take X = 0" }),
        ],
      }),
    );
    expect(bucketsOf(json)["thm:main"]).toBe("refuted");
    expect(json.verdict).toBe("errors_found");
    expect(md).toContain("ERRORS FOUND");
    expect(md).toContain("take X = 0");
  });

  /** The fixture with `thm:overlap` resting on `thm:main` (a corollary of it). */
  async function restingInput(over: Partial<ReportInput>): Promise<ReportInput> {
    const input = await baseInput({ earlyStop: true, ...over });
    return { ...input, core: { ...input.core, statements: input.core.statements.map((s) => (s.id === "thm:overlap" ? { ...s, depends_on: [...s.depends_on, "thm:main"] } : s)) } };
  }
  const plainOf = (md: string): string => md.split("# Technical appendix")[0]!;
  /** What V1.5 records for a statement the paper leaves undetermined and nobody repaired. */
  const open = (node: string, detail = "neither the estimator nor the mode of convergence is named"): VerifyFinding =>
    finding({ node, kind: "unresolved", undetermined: true, stage: "V1.5", detail: `${detail} — cannot be repaired: any repair weakens the contribution` });

  it("results the paper leaves undetermined are `not_determined`: counted apart, never worded as wrong, false or refuted", async () => {
    const { json, md } = buildReport(await restingInput({ findings: [open("thm:main"), open("lem:aux", "the sentence states no proposition"), open("thm:overlap", "no rate is named"), open("ass:overlap", "the symbol admits two readings")] }));
    expect(bucketsOf(json)).toMatchObject({ "thm:main": "not_determined", "lem:aux": "not_determined", "thm:overlap": "not_determined" });
    expect(json.summary).toMatchObject({ not_determined: 3, refuted: 0 });
    expect(json.verdict).toBe("not_determined");
    expect(json.results.find((r) => r.node_id === "thm:overlap")).toMatchObject({ inherits_refutation_from: [], rests_on_undetermined: ["thm:main"] });
    expect(md).toContain("**Verdict: NOT DETERMINED — RESULTS THAT COULD NOT BE CHECKED AS PRINTED**");
    expect(md).not.toContain("ERRORS FOUND");
    const plain = plainOf(md);
    expect(plain).toContain("None was found wrong as printed. 3 could not be checked as printed: they do not say enough to determine what is claimed (not shown false).");
    expect(plain).toContain("No error was found in the results examined.");
    const section = plain.split("## What could not be checked as printed")[1]!.split("\n## ")[0]!;
    expect(section.match(/^### .* — could not be checked as printed$/gmu)).toHaveLength(3);
    expect(section).toContain("- **What is not determined.** neither the estimator nor the mode of convergence is named");
    expect(section).toMatch(/- \*\*Rests on\.\*\* [^\n]*, which also could not be checked as printed\.\n/u);
    expect(section).toContain("- **Formal check.** not formalized: it could not be checked as printed and has no adopted reading or repair (this is not a claim that the result is wrong)");
    expect(section).toContain("### Conditions and definitions left undetermined");
    expect(plain.replace("None was found wrong as printed.", "").replace("## What was wrong and what was done", "").replaceAll("not a claim that the result is wrong", "")).not.toMatch(/wrong|false as printed|refuted|What is wrong|Counterexample/u);
    // the appendix names the finding for what it is, and lists no error
    expect(md).toContain("[not determined, V1.5]");
    expect(md).not.toContain("## Errors by root cause");
    expect(md).toContain("## Not determined");
    expect(md).toContain("| not_determined | 3 |");
  });

  it("a mixed run counts refuted and not-determined results apart; a refuted result reads as before", async () => {
    const refuted = (node: string): VerifyFinding => finding({ node, kind: "refuted", stage: "V1.5", detail: "the bound fails", witness: "take X = 0" });
    const mixed = buildReport(await restingInput({ findings: [open("thm:main"), refuted("thm:overlap"), refuted("lem:aux")] }));
    expect(bucketsOf(mixed.json)).toMatchObject({ "thm:main": "not_determined", "thm:overlap": "refuted", "lem:aux": "refuted" });
    expect(mixed.json.summary).toMatchObject({ not_determined: 1, refuted: 2 });
    expect(mixed.json.verdict).toBe("errors_found");
    expect(mixed.md).toContain("**Verdict: ERRORS FOUND**");
    const plain = plainOf(mixed.md);
    expect(plain).toContain("2 were found wrong as printed: 0 corrected, 2 not repaired. 1 could not be checked as printed: it does not say enough to determine what is claimed (not shown false).");
    // a refuted result resting on an undetermined one says what it rests on is: not determined
    const overlap = plain.split("## What was wrong and what was done")[1]!.split("\n### ").find((e) => e.includes("- **Rests on.**"))!;
    expect(overlap).toMatch(/- \*\*Rests on\.\*\* [^\n]*, which could not be checked as printed\.\n/u);
    expect(overlap).not.toContain("also found wrong");
    expect(overlap).toContain("- **Formal check.** not formalized: it is false as printed and has no adopted repair");
    // a confirmed error elsewhere does not turn the headline into ERRORS FOUND when what is left open is undetermined
    const patch = { corrected_statement: "the corrected bound", proof_note: "n", confirmed: true };
    expect(buildReport(await restingInput({ findings: [open("thm:main"), { ...refuted("lem:aux"), patch }] })).json.verdict).toBe("not_determined");

    // refuted only: every string as before
    const only = buildReport(await restingInput({ findings: [refuted("thm:main"), refuted("thm:overlap")] }));
    expect(only.json.summary).toMatchObject({ not_determined: 0, refuted: 2 });
    expect(only.json.results.find((r) => r.node_id === "thm:overlap")!.rests_on_undetermined).toBeUndefined();
    expect(only.md).toContain("**Verdict: ERRORS FOUND**");
    const p = plainOf(only.md);
    expect(p).toContain("2 were found wrong as printed: 0 corrected, 2 not repaired. The run stopped before the Lean formalization.");
    expect(p).toMatch(/- \*\*What is wrong\.\*\* the bound fails\n- \*\*Counterexample\.\*\* take X = 0\n- \*\*Rests on\.\*\* [^\n]*, also found wrong as printed\.\n- \*\*Correction\.\*\* None: no repair that keeps the point of the result was found\.\n- \*\*Formal check\.\*\* not formalized: it is false as printed and has no adopted repair[^\n]*\.\n/u);
    expect(p).not.toContain("could not be checked as printed");
    expect(only.md).toContain("[refuted, V1.5]");
    expect(only.md).not.toContain("## Not determined");
  });

  it("a statement made precise by a confirmed repair is no error: counted apart, never under ERRORS FOUND or 'wrong as printed'", async () => {
    const patch = { corrected_statement: "the estimator converges in probability", proof_note: "names the mode", confirmed: true };
    const precise = finding({ node: "thm:main", kind: "note", undetermined: true, stage: "V1.5", detail: "made precise — the printed statement did not determine the claim; the reading its repair states was confirmed: the mode of convergence is not named", patch });
    const { json, md } = buildReport(await baseInput({ findings: [precise] }));
    expect(bucketsOf(json)["thm:main"]).toBe("verified");
    expect(json.summary).toMatchObject({ repaired: 0, refuted: 0, not_determined: 0 });
    expect(json.verdict).toBe("no_error_found");
    const plain = plainOf(md);
    expect(plain).toContain("None was found wrong as printed. 1 was made precise: the printed statement did not determine what is claimed, and the reading adopted was confirmed (not an error).");
    const section = plain.split("## Statements made precise (not errors)")[1]!.split("\n## ")[0]!;
    expect(section).toContain("- **What was not determined.** the mode of convergence is not named");
    expect(section).toContain("- **As it reads now.** the estimator converges in probability");
    expect(md).not.toMatch(/ERRORS FOUND|Errors found — repaired|The result as printed is false/u);
    expect(plain).not.toContain("Restated to follow a correction above");
  });

  it("a refuted repair of an undetermined statement leaves it not determined; its witness is named as against the repair tried", async () => {
    const tried = finding({ node: "thm:main", kind: "unresolved", undetermined: true, stage: "V1.5", detail: "the repair tried for it was refuted: under the reading the repair states the rate fails", witness: "take X = 0" });
    const rejected = { ...open("thm:main"), patch: { corrected_statement: "the reading tried", proof_note: "n", confirmed: false } };
    const { json, md } = buildReport(await baseInput({ earlyStop: true, findings: [rejected, tried] }));
    expect(bucketsOf(json)["thm:main"]).toBe("not_determined");
    expect(json.verdict).toBe("not_determined");
    const plain = plainOf(md);
    expect(plain).toContain("None was found wrong as printed.");
    expect(plain).toContain("- **A repair was tried and rejected by the confirming check.** the reading tried");
    expect(plain).toContain("- **Why the repair tried was rejected.** the repair tried for it was refuted: under the reading the repair states the rate fails Counterexample to the reading tried (not to the printed statement): take X = 0");
    expect(plain).not.toContain("- **Counterexample.**");
    expect(md).toContain("witness against the repair tried: take X = 0");
  });

  it("a refutation repaired by a confirmed minimal patch is `repaired`, before Lean and once Lean certifies it; the header says so only with Lean", async () => {
    const patch = {
      corrected_statement: "the corrected rate",
      assumptions: [{ id: "ass:patch-two-sided", condition: "two-sided overlap" }],
      proof_note: "bound 1/p̂ by 1/η",
      confirmed: true,
    };
    const { json, md } = buildReport(
      await baseInput({ findings: [finding({ node: "thm:main", kind: "refuted", stage: "V1.5", witness: "p̂ → 0", patch })] }),
    );
    expect(bucketsOf(json)["thm:main"]).toBe("repaired");
    expect(json.verdict).toBe("repaired");
    expect(md).toContain("REPAIRED BY MINIMAL PATCHES");
    expect(md).toContain("### Errors found — repaired");
    expect(md).toContain("confirmed by an independent referee pass");
    expect(md).toContain("the corrected statement is proved in Lean");

    // before Lean, a confirmed repair is still `repaired` (never `refuted`): the witness is shown
    // under "errors found — repaired" with the corrected statement; the header stays incomplete
    const early = buildReport(
      await baseInput({ earlyStop: true, findings: [finding({ node: "thm:main", kind: "refuted", stage: "V1.5", witness: "p̂ → 0 on a design sequence", patch })] }),
    );
    expect(bucketsOf(early.json)["thm:main"]).toBe("repaired");
    expect(early.json.summary.refuted).toBe(0);
    expect(early.json.verdict).toBe("incomplete");
    const section = early.md.split("### Errors found — repaired")[1]!.split("\n## ")[0]!;
    expect(section).toContain("witness: p̂ → 0 on a design sequence");
    expect(section).toContain("corrected statement: the corrected rate");
    expect(section).toContain("not formalized yet (the run stopped before Lean)");
    // with Lean reached, a confirmed repair Lean did not certify is unresolved — never refuted
    const uncertified = buildReport(
      await baseInput({ lean: null, findings: [finding({ node: "thm:main", kind: "refuted", stage: "V1.5", witness: "w", patch })] }),
    );
    expect(bucketsOf(uncertified.json)["thm:main"]).toBe("unresolved");
    // an unconfirmed patch is an unrepaired error
    const unconfirmed = buildReport(
      await baseInput({ findings: [finding({ node: "thm:main", kind: "refuted", stage: "V1.5", witness: "w", patch: { ...patch, confirmed: false } })] }),
    );
    expect(bucketsOf(unconfirmed.json)["thm:main"]).toBe("refuted");
    expect(unconfirmed.json.verdict).toBe("errors_found");
    expect(unconfirmed.md).toContain("NOT confirmed");
  });

  it("a weakened repair the owner accepted is `repaired` with what it gives up; a declined one is refuted with the suggestion", async () => {
    const patch = {
      corrected_statement: "the limit is N(0, λ)",
      assumptions: [],
      proof_note: "the finite-population correction λ",
      confirmed: true,
      narrowed: "the N(0,1) limit holds only when λ = 1",
    };
    const accepted = buildReport(
      await baseInput({ earlyStop: true, findings: [finding({ node: "thm:main", kind: "refuted", stage: "V1.5", witness: "a permuted population", patch })] }),
    );
    expect(bucketsOf(accepted.json)["thm:main"]).toBe("repaired");
    const section = accepted.md.split("### Errors found — repaired")[1]!.split("\n## ")[0]!;
    expect(section).toContain("contribution narrowed: the N(0,1) limit holds only when λ = 1 (the owner accepted the weaker version)");

    const input = await baseInput({
      findings: [
        finding({
          node: "thm:main",
          kind: "refuted",
          stage: "V1.5",
          detail: "the N(0,1) limit is false — cannot be repaired without losing its point: any repair weakens the contribution: the limit becomes N(0, λ)",
          witness: "a permuted population",
          descoped: true,
          suggested_repair: "corrected statement: the limit is N(0, λ) · gives up: N(0,1) only when λ = 1",
          suggestion_declined: "the N(0,1) calibration is the point",
        }),
      ],
    });
    const main = input.core.statements.find((s) => s.id === "thm:main")!;
    const declined = buildReport({ ...input, core: { ...input.core, statements: input.core.statements.filter((s) => s.id !== "thm:main") }, descoped: [main] });
    expect(bucketsOf(declined.json)["thm:main"]).toBe("refuted");
    expect(declined.json.verdict).toBe("errors_found");
    const unfixable = declined.md.split("### Unfixable results (left out of Lean)")[1]!.split("\n## ")[0]!;
    expect(unfixable).toContain("witness: a permuted population");
    expect(unfixable).toContain("suggested repair (declined by the owner: the N(0,1) calibration is the point): corrected statement: the limit is N(0, λ)");
  });

  it("a descoped result keeps its row although the patched core no longer has it", async () => {
    const input = await baseInput({
      findings: [finding({ node: "thm:main", kind: "refuted", stage: "V1.5", detail: "cannot be repaired: x", witness: null, descoped: true })],
    });
    const main = input.core.statements.find((s) => s.id === "thm:main")!;
    const { json, md } = buildReport({ ...input, core: { ...input.core, statements: input.core.statements.filter((s) => s.id !== "thm:main") }, descoped: [main] });
    expect(bucketsOf(json)["thm:main"]).toBe("refuted");
    expect(md).toContain("### Unfixable results (left out of Lean)");
  });

  it.each<[string, () => unknown]>([
    [
      "a result with no Lean declaration",
      async () => {
        const crosswalk = (await fixture<CrosswalkEntry[]>("crosswalk_full.json")).filter(
          (e) => e.obj_id !== "T-2",
        );
        const { json } = buildReport(await baseInput({ crosswalk }));
        expect(bucketsOf(json)["thm:main"]).toBe("unresolved");
        expect(json.verdict).toBe("incomplete");
      },
    ],
    [
      "a declaration with dirty axioms, or a sorry in its file",
      async () => {
        const lean = cleanLean();
        lean.axioms["Verify.t2_thm"] = { axioms: ["propext", "Paper.magicAxiom"], clean: false };
        const { json } = buildReport(await baseInput({ lean }));
        expect(bucketsOf(json)["thm:main"]).toBe("unresolved");
        expect(json.verdict).toBe("incomplete");
        const sorried = cleanLean();
        sorried.sorry_scan = ["sorry in Papers/SamplePaper/Basic.lean"];
        const withSorry = buildReport(await baseInput({ lean: sorried }));
        // Every row is anchored in Basic.lean, so all three are unresolved.
        expect(new Set(withSorry.json.results.map((r) => r.bucket))).toEqual(new Set(["unresolved"]));
      },
    ],
    [
      "a drifted crosswalk verdict, however clean the Lean is",
      async () => {
        // Every value of CrosswalkVerdict other than `exact` / `equivalent`: the Lean declaration
        // states something the paper did not, so its (green, axiom-clean) proof certifies nothing.
        const failing: CrosswalkVerdict[] = [
          "stronger-in-Lean",
          "weaker-in-Lean",
          "missing-in-Lean",
          "extra-in-Lean",
          "encoding-drift",
          "drift",
          "unmatched",
        ];
        for (const verdict of failing) {
          const crosswalk = (await fixture<CrosswalkEntry[]>("crosswalk_full.json")).map((e) =>
            e.obj_id === "T-2" ? { ...e, verdict } : e,
          );
          const { json, md } = buildReport(await baseInput({ crosswalk }));
          expect(bucketsOf(json)["thm:main"], verdict).toBe("unresolved");
          expect(json.verdict).toBe("incomplete");
          // The row and the unresolved reason both name the verdict, so the reader sees WHY.
          expect(json.results.find((r) => r.node_id === "thm:main")?.crosswalk_verdict).toBe(verdict);
          expect(md).toContain(`does not state this result (crosswalk verdict \`${verdict}\`)`);
          // The other two rows are untouched.
          expect(bucketsOf(json)["lem:aux"]).toBe("verified_with_bookkeeping");
        }
      },
    ],
  ])("%s is unresolved and the run incomplete", async (_name, run) => {
    await run();
  });

  it("an assumed substrate gate makes the row conditional and is disclosed", async () => {
    const { json, md } = buildReport(await baseInput({ graph: graphWithAssumedGate() }));
    const main = json.results.find((r) => r.node_id === "thm:main");
    expect(main?.bucket).toBe("conditional");
    // The `cited` gate is NOT an assumed substrate gate — it is a literature leaf.
    expect(main?.assumed_substrate).toEqual([
      {
        id: "gate:dominated-convergence",
        description: "Dominated convergence for the weighted average.",
      },
    ]);
    expect(md).toContain("### Deferred substrate gates");
    expect(md).toContain("gate:dominated-convergence");
    expect(json.verdict).toBe("no_error_found");
  });
});

describe("parseAxiomReport", () => {
  it("reads both output forms, flags a missing declaration, and never matches a longer name sharing its suffix", () => {
    const out = [
      "'Verify.t1_thm' depends on axioms: [propext,",
      "Classical.choice, Quot.sound]",
      "'Verify.l1_lemma' does not depend on any axioms",
      "'Verify.t3_thm' depends on axioms: [propext, Paper.magicAxiom]",
    ].join("\n");
    const got = parseAxiomReport(out, [
      "Verify.t1_thm",
      "Verify.l1_lemma",
      "Verify.t3_thm",
      "Verify.missing",
    ]);
    expect(got["Verify.t1_thm"]).toEqual({
      axioms: ["propext", "Classical.choice", "Quot.sound"],
      clean: true,
    });
    expect(got["Verify.l1_lemma"]).toEqual({ axioms: [], clean: true });
    expect(got["Verify.t3_thm"].clean).toBe(false);
    expect(got["Verify.missing"].clean).toBe(false);
    expect(got["Verify.missing"].error).toContain("Verify.missing");
    const suffix = parseAxiomReport("'X.Verify.foo' depends on axioms: [propext]", ["Verify.foo"]);
    expect(suffix["Verify.foo"].error).toBeTruthy();
  });
});

describe("runStageV6", () => {
  async function seedRun(repoRoot: string, opts: { stageCompleted: string }): Promise<{
    state: StateJson;
    runDir: string;
  }> {
    const runDir = verifyRunDir(repoRoot, QID);
    await mkdir(path.join(runDir, "discovery"), { recursive: true });
    for (const f of ["envs.json", "core.json", "v1_scope.json", "v1_5_review.json"]) {
      await copyFile(path.join(FIXTURES, f), path.join(runDir, "discovery", f));
    }
    const cw = crosswalkFullJsonPath(repoRoot, QID);
    await mkdir(path.dirname(cw), { recursive: true });
    await copyFile(path.join(FIXTURES, "crosswalk_full.json"), cw);
    await writeFile(
      path.join(runDir, "graph.json"),
      JSON.stringify(graphWithAssumedGate(), null, 2),
      "utf8",
    );
    const state = createVerifyInitialState(QID, {
      phase: "v6",
      source: { input: "main.tex", main_file: "main.tex", sha256: "deadbeef" },
      targets: null,
      // As V1.5 stamps it: the hash of the core the F stages were then run over.
      core_sha256: await sha256File(path.join(runDir, "discovery", "core.json")),
      v1_rounds: 1,
      v1_5_rounds: 0,
      findings: [],
      report_path: null,
    });
    state.stage_completed = opts.stageCompleted as StateJson["stage_completed"];
    return { state, runDir };
  }

  it("writes report.json + report.md and stamps report_path", async () => {
    const repoRoot = await tmpRepo();
    const { state, runDir } = await seedRun(repoRoot, { stageCompleted: "5" });
    let sawArgs: { declNames: readonly string[] } | null = null;
    const stage = makeStageV6({
      collectLeanEvidence: async (a) => {
        sawArgs = { declNames: a.declNames };
        return cleanLean();
      },
    });

    const result = await stage({
      repoRoot,
      qid: QID,
      runDir,
      state,
      deps: { runCodex: (() => {
        throw new Error("V6 must never call a model");
      }) as never },
      dryRun: false,
      log: () => {},
    });

    expect(result.status).toBe("completed");
    expect(result.message).toContain("no_error_found");
    expect(existsSync(path.join(runDir, VERIFY_FILES.reportJson))).toBe(true);
    expect(state.verify?.report_path).toBe(path.join(runDir, VERIFY_FILES.reportMd));
    expect([...sawArgs!.declNames].sort()).toEqual([
      "Verify.l1_lemma",
      "Verify.t1_thm",
      "Verify.t2_thm",
    ]);

    const md = await readFile(path.join(runDir, VERIFY_FILES.reportMd), "utf8");
    expect(md).toContain("main.tex:30-36");
    expect(md).toContain("Basic.lean:70");
    // The seeded graph leaves one gate assumed, so the main theorem is conditional.
    const json = JSON.parse(
      await readFile(path.join(runDir, VERIFY_FILES.reportJson), "utf8"),
    ) as { results: Array<{ node_id: string; bucket: string }> };
    expect(bucketsOf(json)["thm:main"]).toBe("conditional");
    // The stage is a reporter: it must not touch the findings it reads.
    expect(state.verify?.findings).toEqual([]);
  });

  it("--dry-run skips the Lean audit but still writes the report", async () => {
    const repoRoot = await tmpRepo();
    const { state, runDir } = await seedRun(repoRoot, { stageCompleted: "5" });
    const stage = makeStageV6({
      collectLeanEvidence: async () => {
        throw new Error("dry run must not collect Lean evidence");
      },
    });
    const result = await stage({
      repoRoot,
      qid: QID,
      runDir,
      state,
      deps: { runCodex: (() => {
        throw new Error("V6 must never call a model");
      }) as never },
      dryRun: true,
      log: () => {},
    });
    expect(result.status).toBe("completed");
    const json = JSON.parse(
      await readFile(path.join(runDir, VERIFY_FILES.reportJson), "utf8"),
    ) as { lean_build: unknown; verdict: string };
    expect(json.lean_build).toBeNull();
    expect(json.verdict).toBe("incomplete");
  });

  it.each<[string, () => unknown]>([
    [
      "a core that changed after V1.5 accepted it",
      async () => {
        const repoRoot = await tmpRepo();
        const { state, runDir } = await seedRun(repoRoot, { stageCompleted: "5" });
        const corePath = path.join(runDir, "discovery", "core.json");
        const core = JSON.parse(await readFile(corePath, "utf8")) as Core;
        // The kind of edit `--from-stage V6` makes reachable: the statement now says something the
        // Lean proof was never about.
        core.statements.find((st) => st.id === "thm:main")!.statement = "Something else entirely.";
        await writeFile(corePath, JSON.stringify(core, null, 2), "utf8");
        const stage = makeStageV6({ collectLeanEvidence: async () => cleanLean() });
        await expect(
          stage({
            repoRoot,
            qid: QID,
            runDir,
            state,
            deps: { runCodex: (() => undefined) as never },
            dryRun: false,
            log: () => {},
          }),
        ).rejects.toThrow(/core\.json changed after V1\.5 accepted it/);
      },
    ],
    [
      "a changed core on an early stop, but only once V1.5 stamped a hash",
      async () => {
        const repoRoot = await tmpRepo();
        const { state, runDir } = await seedRun(repoRoot, { stageCompleted: "V1.5" });
        const corePath = path.join(runDir, "discovery", "core.json");
        await writeFile(corePath, `${await readFile(corePath, "utf8")}\n`, "utf8");
        const stage = makeStageV6({
          collectLeanEvidence: async () => {
            throw new Error("an early stop must not collect Lean evidence");
          },
        });
        const args = {
          repoRoot,
          qid: QID,
          runDir,
          state,
          deps: { runCodex: (() => undefined) as never },
          dryRun: false,
          log: () => {},
        };
        await expect(stage(args)).rejects.toThrow(/core\.json changed after V1\.5 accepted it/);
        // A run that stopped BEFORE V1.5 accepted anything has no hash to compare and still reports.
        state.verify!.core_sha256 = null;
        const result = await stage(args);
        expect(result.status).toBe("completed");
        // A completed F run whose core V1.5 never accepted is refused.
        state.stage_completed = "5" as StateJson["stage_completed"];
        await expect(stage(args)).rejects.toThrow(/no core was ever accepted by V1\.5/);
      },
    ],
    [
      "a completed F run with no crosswalk (an error, not a null)",
      async () => {
        const repoRoot = await tmpRepo();
        const { state, runDir } = await seedRun(repoRoot, { stageCompleted: "5" });
        await rm(crosswalkFullJsonPath(repoRoot, QID));
        const stage = makeStageV6({ collectLeanEvidence: async () => cleanLean() });
        await expect(
          stage({
            repoRoot,
            qid: QID,
            runDir,
            state,
            deps: { runCodex: (() => undefined) as never },
            dryRun: false,
            log: () => {},
          }),
        ).rejects.toThrow(/crosswalk_full\.json is missing/);
      },
    ],
  ])("refuses %s", async (_name, run) => {
    await run();
  });
});
