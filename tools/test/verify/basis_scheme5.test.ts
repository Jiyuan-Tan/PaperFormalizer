import { fileURLToPath } from "node:url";
/**
 * Basis scheme 5: a verdict is keyed on what its referee is shown — the node's own record, the text
 * of what it uses directly (of a result it uses: also the hypotheses and definitions that result is
 * stated under, and its verdict line), the symbol entries those name — and no longer on its whole
 * `depends_on` closure. A change deep in the chain reaches a node through the verdicts between them,
 * in the same pass (`partitionByBasis` `onGraded`, `referee_shards.ts`); a verdict recorded under
 * scheme 4 is carried over without a call while its scheme-4 basis holds.
 */
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState } from "../../src/state.js";
import type { StateJson } from "../../src/types.js";
import { BASIS_SCHEME, basisInputs, basisInputsV4, basisOf, nodeFingerprint, regradeCause } from "../../src/verify/core_graph.js";
import { refereeLevels } from "../../src/verify/referee_levels.js";
import { dependencyLine } from "../../src/verify/referee_shards.js";
import { partitionByBasis, regradeBreakdownLine, runStageV1_5, shownVerdictOf } from "../../src/verify/stage_v1_5.js";
import { VERIFY_FILES, type V15NodeVerdict, type V15Review, type VerifyStageArgs } from "../../src/verify/types.js";
import { isRefereeGlobal, isRefereeShard, shardIds } from "./referee_fake.js";
import { withOwnerExplanations } from "./owner_explained.js";
import { symbolReply } from "./symbol_fake.js";

const TOOLS = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..");
const FLAT_FIXTURE = path.join(TOOLS, "test", "verify", "fixtures", "v1_5", "flat.tex");

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

/** A chain: ass:overlap, def:propensity ← lem:deep ← lem:mid ← thm:top ← thm:roof. */
function chain(): Core {
  return {
    qid: "toy",
    symbols: [
      { name: "Y", type: "random variable", role: "outcome" },
      { name: "\\kappa", type: "constant", def: "$\\kappa$ is the rate constant." },
    ],
    assumptions: [
      { id: "ass:unconfoundedness", kind: "causal-structural", condition: "$Y(d) \\perp D \\mid X$ for $d \\in \\{0,1\\}$.", novel: { flag: true, justification: "Assumption 1" }, tex_locator: { file: "main.tex", from: 10, to: 12, env: "assumption", label: "ass:unconf" } },
      { id: "ass:overlap", kind: "support", condition: "$0 < e(X) < 1$ almost surely.", novel: { flag: true, justification: "Assumption 2" }, tex_locator: { file: "main.tex", from: 14, to: 16, env: "assumption", label: "ass:overlap" } },
    ],
    definitions: [{ id: "def:propensity", name: "propensity score", construction: "Let $Y$ be the outcome, $D \\in \\{0,1\\}$ the treatment and $X$ the covariates.", tex_locator: { file: "main.tex", from: 8, to: 8, env: "prose", label: null } }],
    statements: [
      { id: "lem:deep", kind: "lemma", statement: "Under Assumption \\ref{ass:overlap}, $E[DY/e(X)] = E[Y(1)]$.", depends_on: ["ass:overlap", "def:propensity"], proof_tex: "Condition on $X$ and apply the tower property.", status: "to-prove", tex_locator: { file: "main.tex", from: 18, to: 20, env: "lem", label: "lem:ipw" } },
      { id: "lem:mid", kind: "lemma", statement: "The two arms are identified with constant $\\kappa$.", depends_on: ["lem:deep"], proof_tex: "Apply Lemma \\ref{lem:ipw} to each arm.", status: "to-prove" },
      { id: "thm:top", kind: "theorem", statement: "Under Assumptions \\ref{ass:unconf} and \\ref{ass:overlap}, $\\tau = E[DY/e(X) - (1-D)Y/(1-e(X))]$.", depends_on: ["ass:unconfoundedness", "lem:mid"], proof_tex: "Subtract the two arms.", status: "to-prove", tex_locator: { file: "main.tex", from: 25, to: 27, env: "thm", label: "thm:ate" } },
      { id: "thm:roof", kind: "theorem", statement: "In particular $\\tau$ is identified.", depends_on: ["thm:top"], proof_tex: "Immediate.", status: "to-prove" },
    ],
    target_estimand: "$\\tau = E[Y(1) - Y(0)]$",
    bibliography: [],
  } as unknown as Core;
}
const IDS = ["lem:deep", "lem:mid", "thm:top", "thm:roof", "ass:unconfoundedness", "ass:overlap", "def:propensity"];
const withStatement = (c: Core, id: string, f: (st: Core["statements"][number]) => void): Core => {
  const out = structuredClone(c);
  f(out.statements.find((st) => st.id === id)!);
  return out;
};
const moved = (a: Core, b: Core): string[] => IDS.filter((id) => nodeFingerprint(a, id) !== nodeFingerprint(b, id));

describe("scheme 5: what a basis reads", () => {
  it("a proof-only edit of a deep lemma moves that lemma's basis and no user's", () => {
    expect(moved(chain(), withStatement(chain(), "lem:deep", (st) => (st.proof_tex = "Condition on $X$; then integrate.")))).toEqual(["lem:deep"]);
    // … nor does its locator, or any other field its users are not shown
    expect(moved(chain(), withStatement(chain(), "lem:deep", (st) => (st.tex_locator = { ...st.tex_locator!, from: 19 })))).toEqual(["lem:deep"]);
  });

  it("a changed statement of a dependency moves its direct users, not theirs; the text is read whole, past where the prompt cuts it", () => {
    expect(moved(chain(), withStatement(chain(), "lem:deep", (st) => (st.statement += " The identity is exact.")))).toEqual(["lem:deep", "lem:mid"]);
    const long = withStatement(chain(), "lem:deep", (st) => (st.statement = `${"x ".repeat(2000)}end A.`));
    const longer = withStatement(chain(), "lem:deep", (st) => (st.statement = `${"x ".repeat(2000)}end B.`));
    expect(moved(long, longer)).toEqual(["lem:deep", "lem:mid"]);
    // a re-wrapped line of it is the same text to its user
    expect(moved(chain(), withStatement(chain(), "lem:deep", (st) => (st.statement = st.statement.replace(", ", ",\n  "))))).toEqual(["lem:deep"]);
  });

  it("a hypothesis moves the results stated under it and the results using those — to apply a result is to meet its hypotheses — and no further", () => {
    const c = structuredClone(chain());
    c.assumptions.find((a) => a.id === "ass:overlap")!.condition = "$\\epsilon < e(X) < 1 - \\epsilon$ almost surely.";
    expect(moved(chain(), c)).toEqual(["lem:deep", "lem:mid", "ass:overlap"]);
    // a hypothesis wired into a result reaches the result (its record) and its direct users (what it is stated under)
    expect(moved(chain(), withStatement(chain(), "lem:deep", (st) => st.depends_on.push("ass:unconfoundedness")))).toEqual(["lem:deep", "lem:mid"]);
  });

  it("the order of a node's wiring list is its own record's (its shard prints it): the node alone; of a used result's hypotheses a user reads the set", () => {
    expect(moved(chain(), withStatement(chain(), "lem:deep", (st) => st.depends_on.reverse()))).toEqual(["lem:deep"]);
    expect(moved(chain(), withStatement(chain(), "thm:top", (st) => st.depends_on.reverse()))).toEqual(["thm:top"]);
  });

  it("a symbol entry is read by the nodes naming it and by the nodes using one of those — not through a proof, not further up", () => {
    const c = structuredClone(chain());
    c.symbols.find((x) => x.name === "\\kappa")!.def = "$\\kappa$ is the rate constant, at least one.";
    // lem:mid names \kappa in its statement: itself and thm:top (which is shown that statement)
    expect(moved(chain(), c)).toEqual(["lem:mid", "thm:top"]);
    // named only in a proof: the node alone
    const inProof = (x: Core): Core => withStatement(x, "lem:mid", (st) => ((st.statement = "The two arms are identified."), (st.proof_tex = "With the constant $\\kappa$.")));
    expect(moved(inProof(chain()), inProof(c))).toEqual(["lem:mid"]);
  });

  it("the verdict of a result a node uses is part of its basis, as the line its referee is shown; a node using nothing hashes as under scheme 4", () => {
    const c = chain();
    const a = basisInputs(c, "lem:mid", new Map(), undefined, () => "line A");
    const b = basisInputs(c, "lem:mid", new Map(), undefined, () => "line B");
    expect(a.scheme).toBe(BASIS_SCHEME);
    expect(a.verdicts).toEqual({ "lem:deep": "line A" });
    expect(basisOf(a)).not.toBe(basisOf(b));
    expect(regradeCause({ inputs: a, clean: true }, b)).toBe("dependency verdict");
    // only results have a verdict line: a hypothesis or definition used is shown by its text
    expect(basisInputs(c, "lem:deep", new Map(), undefined, () => "x").verdicts).toBeUndefined();
    for (const id of ["ass:overlap", "def:propensity"]) expect(nodeFingerprint(c, id)).toBe(basisOf(basisInputsV4(c, id)));
    expect(regradeCause({ inputs: basisInputs(c, "lem:mid"), clean: true }, basisInputs(withStatement(c, "lem:deep", (st) => (st.statement += " Exactly.")), "lem:mid"))).toBe("dependency");
  });
});

// ---------------------------------------------------------------------------------------------
// The partition and the chain
// ---------------------------------------------------------------------------------------------

const ok = (id: string, over: Partial<V15NodeVerdict> = {}): V15NodeVerdict => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "reproduced", witness: null, bookkeeping_assumption: null, reading: null, ...over }) as V15NodeVerdict;

/** The review and cache a scheme-5 pass over `c` leaves, every node graded as `verdicts` say (default ok). */
function passed(c: Core, verdicts: Record<string, Partial<V15NodeVerdict>> = {}): { prior: V15Review; confirmed: Record<string, string> } {
  const part = partitionByBasis(c, {}, null);
  const final = new Map(IDS.map((id) => [id, ok(id, verdicts[id])] as const));
  // leaves first, as the levels are graded
  for (const id of ["ass:unconfoundedness", "ass:overlap", "def:propensity", "lem:deep", "lem:mid", "thm:top", "thm:roof"]) part.onGraded(final, [id]);
  const nodes = IDS.map((id) => ({ ...final.get(id)!, basis: part.bases.get(id), basis_scheme: BASIS_SCHEME, basis_inputs: part.inputs.get(id), graded: "fresh" as const }));
  const clean = (n: V15NodeVerdict): boolean => n.faithfulness === "ok" && (n.correctness === "ok" || n.correctness === "bookkeeping");
  return { prior: { verdict: "PASS", summary: "s", nodes }, confirmed: Object.fromEntries(nodes.filter(clean).map((n) => [n.id, n.basis!])) };
}

describe("scheme 5: the partition and the chain", () => {
  it("an unchanged core carries everything; a deep proof edit grades that lemma only, and its users are re-opened exactly when its verdict then reads otherwise", () => {
    const { prior, confirmed } = passed(chain());
    expect(partitionByBasis(chain(), confirmed, prior).toGrade).toEqual([]);
    const edited = withStatement(chain(), "lem:deep", (st) => (st.proof_tex = "Condition on $X$; then integrate."));
    const part = partitionByBasis(edited, confirmed, prior);
    expect(part.toGrade).toEqual(["lem:deep"]);
    expect(part.why).toEqual({ causes: { content: 1 } });
    // graded ok again: the line its users were shown stands, nothing is re-opened
    const final = new Map(prior.nodes.map((n) => [n.id, n] as const));
    expect(part.onGraded(new Map([...final, ["lem:deep", ok("lem:deep", { detail: "reproduced, differently" })]]), ["lem:deep"])).toEqual([]);
    expect(part.carried.map((n) => n.id)).toContain("lem:mid");
    // graded unclear: its direct user is re-opened (not the users above — until that one's verdict moves too)
    const again = partitionByBasis(edited, confirmed, prior);
    const unclear = new Map([...final, ["lem:deep", ok("lem:deep", { correctness: "unclear", detail: "the tower step is not justified" })]]);
    expect(again.onGraded(unclear, ["lem:deep"])).toEqual(["lem:mid"]);
    expect(again.toGrade).toEqual(["lem:deep", "lem:mid"]);
    expect(again.carried.map((n) => n.id)).not.toContain("lem:mid");
    expect(regradeBreakdownLine(again.why)).toBe("delta review: why re-graded — 1 content changed, 0 dependency changed, 0 symbol meaning changed, 1 dependency verdict changed");
    // lem:mid graded ok under the new line: thm:top stays; graded bookkeeping: thm:top is re-opened in turn
    expect(again.onGraded(new Map([...unclear, ["lem:mid", ok("lem:mid")]]), ["lem:mid"])).toEqual([]);
    const third = partitionByBasis(edited, confirmed, prior);
    third.onGraded(unclear, ["lem:deep"]);
    expect(third.onGraded(new Map([...unclear, ["lem:mid", ok("lem:mid", { correctness: "bookkeeping", bookkeeping_assumption: { condition: "$\\kappa > 0$", reason: "used silently" } })]]), ["lem:mid"])).toEqual(["thm:top"]);
    // the basis a graded node is recorded on holds the lines it was shown
    const shown = shownVerdictOf(edited);
    expect(shown("lem:deep", unclear.get("lem:deep")!)).toBe(dependencyLine({ id: "lem:deep", kind: "lemma", verdict: unclear.get("lem:deep")!, repair: null }));
    expect(Object.keys(third.inputs.get("lem:mid")!.verdicts!)).toEqual(["lem:deep"]);
    expect(third.inputs.get("lem:mid")!.verdicts!["lem:deep"]).not.toBe(prior.nodes.find((n) => n.id === "lem:mid")!.basis_inputs!.verdicts!["lem:deep"]);
  });

  it("a carried verdict or an earlier pass's grade shows its users the same line: `graded` is not part of it", () => {
    const { prior, confirmed } = passed(chain());
    const carriedOnce = { ...prior, nodes: prior.nodes.map((n) => ({ ...n, graded: "carried" as const })) };
    expect(partitionByBasis(chain(), confirmed, carriedOnce).toGrade).toEqual([]);
  });

  it("a verdict altered after its users were graded (the global pass, a ruling): a result still to grade re-opens them only if its new verdict reads otherwise; one carried as altered re-opens them at once", () => {
    const { prior, confirmed } = passed(chain());
    // The global pass made lem:deep drift after lem:mid was graded under its `ok`: not clean, graded again.
    const drift = { ...prior, nodes: prior.nodes.map((n) => (n.id === "lem:deep" ? { ...n, faithfulness: "drift" as const, detail: "[global pass, wiring] a hypothesis is missing" } : n)) };
    const { "lem:deep": _d, ...rest } = confirmed;
    const part = partitionByBasis(chain(), rest, drift);
    expect(part.toGrade).toEqual(["lem:deep"]);
    expect(part.why).toEqual({ causes: { "not clean before": 1 } });
    const final = new Map(drift.nodes.map((n) => [n.id, n] as const));
    // back to the `ok` its user was shown: the user's verdict stands
    expect(part.onGraded(new Map([...final, ["lem:deep", ok("lem:deep")]]), ["lem:deep"])).toEqual([]);
    // still drifting: the user was graded under another line
    const still = partitionByBasis(chain(), rest, drift);
    expect(still.onGraded(final, ["lem:deep"])).toEqual(["lem:mid"]);
    // A ruling rewrote a verdict that stays clean and carried (an owner's withdrawal): its users are graded afresh.
    const ruled = { ...prior, nodes: prior.nodes.map((n) => (n.id === "lem:deep" ? { ...n, owner_overruled: true, owner_reason: "the paper grants it" } : n)) };
    const after = partitionByBasis(chain(), confirmed, ruled);
    expect(after.toGrade).toEqual(["lem:mid"]);
    expect(after.why).toEqual({ causes: { "dependency verdict": 1 } });
  });

  it("transition: a scheme-4 cache is carried over node by node — re-keyed with no node to grade while its scheme-4 basis holds; where it moved, graded afresh for the scheme-4 cause", () => {
    const c = chain();
    const v4 = (x: Core): { prior: V15Review; confirmed: Record<string, string> } => {
      const nodes = IDS.map((id) => ({ ...ok(id), basis: basisOf(basisInputsV4(x, id)), basis_scheme: 4, basis_inputs: basisInputsV4(x, id), graded: "carried" as const }));
      return { prior: { verdict: "PASS", summary: "s", nodes }, confirmed: Object.fromEntries(nodes.map((n) => [n.id, n.basis])) };
    };
    const old = v4(c);
    const part = partitionByBasis(c, old.confirmed, old.prior);
    expect(part.toGrade).toEqual([]);
    expect(part.carried.map((n) => [n.id, n.basis_scheme, n.basis])).toEqual(IDS.map((id) => [id, BASIS_SCHEME, part.bases.get(id)]));
    // the re-keyed bases are the ones a scheme-5 pass records: the next pass carries them as its own
    expect(Object.fromEntries(part.bases)).toEqual(passed(c).confirmed);
    // a result whose scheme-4 basis moved (a deep proof edit moved every closure above it) is graded afresh …
    const edited = withStatement(c, "lem:deep", (st) => (st.proof_tex = "Condition on $X$; then integrate."));
    const stale = partitionByBasis(edited, old.confirmed, old.prior);
    expect(stale.toGrade).toEqual(["lem:deep", "lem:mid", "thm:top", "thm:roof"]);
    expect(stale.why).toEqual({ causes: { content: 1, dependency: 3 } });
    expect(stale.carried.map((n) => n.id)).toEqual(["ass:unconfoundedness", "ass:overlap", "def:propensity"]);
    // … and a verdict not clean, or cached on another basis, is not carried over — nor is the verdict
    // of a result using it: scheme 4 kept no record of the line that verdict was given under, and the
    // result it uses is graded again
    const { "thm:top": _t, ...withdrawn } = old.confirmed;
    const w = partitionByBasis(c, withdrawn, old.prior);
    expect(w.toGrade).toEqual(["thm:top", "thm:roof"]);
    expect(w.why).toEqual({ causes: { "cache withdrawn": 1, "dependency verdict": 1 } });
    // a paused pass's verdicts (`carryAny`) are carried over the same way, whatever their grade — but
    // not a verdict resting on one that is not clean
    const unclear = { ...old.prior, nodes: old.prior.nodes.map((n) => (n.id === "thm:top" ? { ...n, correctness: "unclear" as const } : n)) };
    expect(partitionByBasis(c, withdrawn, unclear, new Map(), { "thm:top": old.confirmed["thm:top"]! }).toGrade).toEqual(["thm:roof"]);
  });

  it("transition: a used result whose line holds what the scheme-4 basis cannot prove the user was graded with — a condition or a pinned reading on the verdict only, the ledger's word on its repair — re-grades the user; one wired into the core re-keys it without a call", () => {
    const v4file = (c: Core, over: Partial<V15NodeVerdict>): { prior: V15Review; confirmed: Record<string, string> } => {
      const ids = [...c.statements, ...c.assumptions, ...c.definitions].map((n) => n.id);
      const nodes = ids.map((id) => ({ ...ok(id, id === "lem:deep" ? over : {}), basis: basisOf(basisInputsV4(c, id)), basis_scheme: 4, basis_inputs: basisInputsV4(c, id), graded: "carried" as const }));
      return { prior: { verdict: "PASS", summary: "s", nodes }, confirmed: Object.fromEntries(nodes.map((n) => [n.id, n.basis])) };
    };
    const afresh = (c: Core, over: Partial<V15NodeVerdict>, shown = shownVerdictOf(c), complete = false): string[] =>
      ((f) => partitionByBasis(c, f.confirmed, f.prior, new Map(), {}, new Map(), shown, { complete }).toGrade)(v4file(c, over));
    const bk = { correctness: "bookkeeping" as const, bookkeeping_assumption: { condition: "$e(X)$ is measurable.", reason: "used silently" } };
    const pin = { ambiguity: "pinned" as const, reading: { reading: "the expectation is conditional on $X$", evidence: "Section 2" } };
    const above = ["lem:mid", "thm:top", "thm:roof"];
    // (i) a condition, (ii) a reading: on the verdict only
    expect(afresh(chain(), bk)).toEqual(above);
    expect(afresh(chain(), pin)).toEqual(above);
    // (iii) the ledger's word on what the printed statement got wrong, in the line of a confirmed repair
    const repaired = (ledger: string | null) => shownVerdictOf(chain(), (id) => (id === "lem:deep" ? { corrected: "The corrected lemma.", printedError: ledger } : null));
    expect(afresh(chain(), {}, repaired("fails when $e(X) \\to 0$"))).toEqual(above);
    expect(afresh(chain(), {}, repaired(null))).toEqual([]);
    // wired into the core (a node of the user's scheme-4 closure), with the same meaning: carried over
    const wired = (a: Record<string, unknown>): Core => {
      const c = structuredClone(chain());
      c.assumptions.push(a as never);
      c.statements.find((st) => st.id === "lem:deep")!.depends_on.push(a.id as string);
      return c;
    };
    const bkNode = { id: "ass:bk-1", kind: "regularity", condition: "$e(X)$  is measurable", bookkeeping: { flag: true, added_by: "V1.5", reason: "used silently" } };
    const pinNode = { id: "ass:pin-1", kind: "regularity", condition: "the expectation is conditional on $X$.", bookkeeping: { flag: true, added_by: "V1.5", reason: "pins reading of lem:deep: Section 2" } };
    expect(afresh(wired(bkNode), bk)).toEqual([]);
    expect(afresh(wired(pinNode), pin)).toEqual([]);
    // … wired with another meaning, or a pin of another node: not proved
    expect(afresh(wired({ ...bkNode, condition: "$e(X)$ is bounded." }), bk)).toEqual(above);
    expect(afresh(wired({ ...pinNode, bookkeeping: { ...pinNode.bookkeeping, reason: "pins reading of ass:overlap: Section 2" } }), pin)).toEqual(above);
    // A review left by a COMPLETE pass is what its owner accepted: all three are re-keyed, no node graded …
    expect(afresh(chain(), bk, shownVerdictOf(chain()), true)).toEqual([]);
    expect(afresh(chain(), pin, shownVerdictOf(chain()), true)).toEqual([]);
    expect(afresh(chain(), {}, repaired("fails when $e(X) \\to 0$"), true)).toEqual([]);
    // … but for what is stale for sure, in both cases: a used result rewritten by a ruling, not clean, or with no cache entry
    const overruled = { owner_overruled: true, owner_reason: "the paper grants it" };
    expect(afresh(chain(), overruled)).toEqual(above);
    expect(afresh(chain(), overruled, shownVerdictOf(chain()), true)).toEqual(["lem:mid"]);
    expect(afresh(chain(), { correctness: "unclear" }, shownVerdictOf(chain()), true)).toEqual(["lem:deep", "lem:mid"]);
    const f = v4file(chain(), {});
    const { "lem:deep": _w, ...withdrawn } = f.confirmed;
    const part = partitionByBasis(chain(), withdrawn, f.prior, new Map(), {}, new Map(), shownVerdictOf(chain()), { complete: true });
    expect(part.toGrade).toEqual(["lem:deep", "lem:mid"]);
    // the results above wait on the one graded in this pass: re-opened if its line moves (the chain)
    const final = new Map(f.prior.nodes.map((n) => [n.id, n] as const));
    expect(part.onGraded(new Map([...final, ["lem:deep", ok("lem:deep")], ["lem:mid", ok("lem:mid", bk)]]), ["lem:mid"])).toEqual(["thm:top"]);
  });

  it("transition: a used result's verdict rewritten by a ruling since (clean, carried, its record unchanged) is no line its users were graded under — they are graded afresh, not re-keyed", () => {
    const c = chain();
    const nodes = IDS.map((id) => ({ ...ok(id, id === "lem:deep" ? { owner_overruled: true, owner_reason: "the paper grants it" } : {}), basis: basisOf(basisInputsV4(c, id)), basis_scheme: 4, basis_inputs: basisInputsV4(c, id), graded: "carried" as const }));
    const part = partitionByBasis(c, Object.fromEntries(nodes.map((n) => [n.id, n.basis])), { verdict: "PASS", summary: "s", nodes });
    // … and so are the results above: each uses one graded in this pass, whose line then is not on record
    expect(part.toGrade).toEqual(["lem:mid", "thm:top", "thm:roof"]);
    expect(part.why).toEqual({ causes: { "dependency verdict": 3 } });
    expect(part.carried.map((n) => n.id)).toEqual(["lem:deep", "ass:unconfoundedness", "ass:overlap", "def:propensity"]);
  });
});

// ---------------------------------------------------------------------------------------------
// Inside the stage: the chain in one pass, the carry-over on file
// ---------------------------------------------------------------------------------------------

type Grade = (id: string, pass: number) => Partial<V15NodeVerdict>;

function fakeCodex(calls: CodexRunInput[], pass: number, grade: Grade = () => ({})): typeof runCodex {
  const base = (id: string) => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "reproduced", witness: null, fix: null, bookkeeping_assumption: null, reading: null, minimality: false });
  return (async (input: CodexRunInput) => {
    const sym = symbolReply(input);
    if (sym !== null) return { stdout: sym, stderr: "" };
    calls.push(input);
    if (isRefereeShard(input)) return { stdout: JSON.stringify(withOwnerExplanations({ summary: "s", nodes: shardIds(input.prompt).map((id) => ({ ...base(id), ...grade(id, pass) })) })), stderr: "" };
    if (isRefereeGlobal(input)) return { stdout: JSON.stringify({ verdict: "PASS", summary: "g", patch_review: null, rejection_verdicts: null, cross_node: [] }), stderr: "" };
    throw new Error("unexpected call");
  }) as typeof runCodex;
}

async function stageDir(): Promise<{ runDir: string; state: StateJson; args: (codex: typeof runCodex, log?: (m: string) => void) => VerifyStageArgs }> {
  const root = await mkdtemp(path.join(os.tmpdir(), "verify-scheme5-"));
  tmpDirs.push(root);
  const runDir = path.join(root, "runs", "toy");
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  await writeFile(path.join(runDir, VERIFY_FILES.coreJson), JSON.stringify(chain(), null, 2));
  await writeFile(path.join(runDir, VERIFY_FILES.coreTranscribed), JSON.stringify(chain(), null, 2));
  await writeFile(path.join(runDir, VERIFY_FILES.flatTex), await readFile(FLAT_FIXTURE, "utf8"));
  const state = createVerifyInitialState("toy", { phase: "v1", source: { input: "p", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
  return { runDir, state, args: (codex, log = () => {}) => ({ repoRoot: root, qid: "toy", runDir, state, deps: { runCodex: codex }, dryRun: false, refereeFixAsYouGo: false, log }) };
}
/** … with fix as you go on (the default): an error with an in-scope witness pauses the grading. */
const pausing = (a: VerifyStageArgs): VerifyStageArgs => (({ refereeFixAsYouGo: _f, ...rest }) => rest)(a);
const IN_SCOPE = { correctness: "error" as const, detail: "the step fails", witness: "fails when $e(X) \\to 0$", witness_regime: "in_scope" as const, witness_instance: "$e(X) = 1/n$" };

const readReview = async (runDir: string): Promise<V15Review> => JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.v15Review), "utf8")) as V15Review;
const gradedIn = (calls: CodexRunInput[]): string[][] => calls.filter(isRefereeShard).map((c) => shardIds(c.prompt));

async function editTranscribed(runDir: string, id: string, f: (st: Core["statements"][number]) => void): Promise<void> {
  const tp = path.join(runDir, VERIFY_FILES.coreTranscribed);
  const core = JSON.parse(await readFile(tp, "utf8")) as Core;
  f(core.statements.find((st) => st.id === id)!);
  await writeFile(tp, JSON.stringify(core, null, 2));
}

describe("scheme 5 inside the stage", () => {
  it("a proof-only edit of a deep lemma grades the lemma alone; when its verdict then reads otherwise, its direct user is graded in the same pass, shown the new line", async () => {
    const h = await stageDir();
    expect((await runStageV1_5(h.args(fakeCodex([], 1)))).status).toBe("completed");
    await editTranscribed(h.runDir, "lem:deep", (st) => (st.proof_tex = "Condition on $X$; then integrate."));
    h.state.stage_completed = "V1";
    const second: CodexRunInput[] = [];
    await runStageV1_5(h.args(fakeCodex(second, 2)));
    expect(gradedIn(second)).toEqual([["lem:deep"]]);
    expect((await readReview(h.runDir)).nodes.filter((n) => n.graded === "fresh").map((n) => n.id)).toEqual(["lem:deep"]);
    // Edited again, and this time the referee cannot reproduce a step: lem:mid, carried, is re-opened.
    await editTranscribed(h.runDir, "lem:deep", (st) => (st.proof_tex = "Condition on $X$."));
    h.state.stage_completed = "V1";
    const third: CodexRunInput[] = [];
    const logs: string[] = [];
    await runStageV1_5(h.args(fakeCodex(third, 3, (id) => (id === "lem:deep" ? { correctness: "unclear", detail: "the tower step is not justified" } : {})), (m) => logs.push(m)));
    expect(gradedIn(third)).toEqual([["lem:deep"], ["lem:mid"]]);
    expect(logs).toContain("delta review: 1 carried verdict(s) re-opened — a result they use changed its verdict in this pass (lem:mid)");
    const mid = third.filter(isRefereeShard)[1]!.prompt;
    expect(mid).toContain("- lem:deep (lemma): unclear — a step was not reproduced (not an error): the tower step is not justified — used by lem:mid");
    const r = await readReview(h.runDir);
    expect(r.nodes.filter((n) => n.graded === "fresh").map((n) => [n.id, n.shards]).sort()).toEqual([["lem:deep", ["L1-1"]], ["lem:mid", ["L2-1"]]]);
    // thm:top and thm:roof were never re-opened: lem:mid's verdict reads as before
    expect(r.nodes.filter((n) => n.graded === "carried").map((n) => n.id).sort()).toEqual(["ass:overlap", "ass:unconfoundedness", "def:propensity", "thm:roof", "thm:top"]);
    // Nothing edited: lem:deep, not clean, is graded again — clean now, so lem:mid (graded under `unclear`) follows.
    h.state.stage_completed = "V1";
    const fourth: CodexRunInput[] = [];
    await runStageV1_5(h.args(fakeCodex(fourth, 4)));
    expect(gradedIn(fourth)).toEqual([["lem:deep"], ["lem:mid"]]);
    h.state.stage_completed = "V1";
    const fifth: CodexRunInput[] = [];
    await runStageV1_5(h.args(fakeCodex(fifth, 5)));
    expect(fifth).toEqual([]);
  });

  it("a result to grade that rests on another through a carried one waits for it: the carried verdict between them, re-opened, is graded first and its new line shown", async () => {
    // (levels) thm:top rests on lem:deep through lem:mid, carried: not the same level
    expect(refereeLevels(chain(), ["lem:deep", "thm:top"]).levels).toEqual([[], ["lem:deep"], ["thm:top"]]);
    expect(refereeLevels(chain(), ["lem:deep", "thm:roof", "ass:overlap"]).levels).toEqual([["ass:overlap"], ["lem:deep"], ["thm:roof"]]);
    const h = await stageDir();
    await runStageV1_5(h.args(fakeCodex([], 1)));
    await editTranscribed(h.runDir, "lem:deep", (st) => (st.proof_tex = "Condition on $X$."));
    await editTranscribed(h.runDir, "thm:top", (st) => (st.proof_tex = "Subtract the two arms, each identified."));
    h.state.stage_completed = "V1";
    const calls: CodexRunInput[] = [];
    const grade: Grade = (id) =>
      id === "lem:deep" ? { correctness: "unclear", detail: "the tower step is not justified" } : id === "lem:mid" ? { correctness: "bookkeeping", bookkeeping_assumption: { condition: "$e(X)$ is measurable.", reason: "used silently by the tower step" } } : {};
    await runStageV1_5(h.args(fakeCodex(calls, 2, grade)));
    expect(gradedIn(calls)).toEqual([["lem:deep"], ["lem:mid"], ["thm:top"]]);
    expect(calls.filter(isRefereeShard)[2]!.prompt).toContain("- lem:mid (lemma): bookkeeping — holds under the added condition $e(X)$ is measurable. — used by thm:top");
    // thm:top was graded under lem:mid's new line and its own verdict reads as before: thm:roof stands
    const r = await readReview(h.runDir);
    expect(r.nodes.find((n) => n.id === "thm:roof")!.graded).toBe("carried");
    expect(Object.keys(r.nodes.find((n) => n.id === "thm:top")!.basis_inputs!.verdicts!)).toEqual(["lem:mid"]);
  });

  it("a halt after the chain re-opened a verdict: that verdict is not kept — the next pass grades its node, and carries what was graded before the halt", async () => {
    const h = await stageDir();
    await runStageV1_5(h.args(fakeCodex([], 1)));
    await editTranscribed(h.runDir, "lem:deep", (st) => (st.proof_tex = "Condition on $X$."));
    h.state.stage_completed = "V1";
    // lem:deep's verdict now reads otherwise: lem:mid is re-opened — and its call fails.
    const failing: CodexRunInput[] = [];
    const inner = fakeCodex(failing, 2, (id) => (id === "lem:deep" ? { correctness: "unclear", detail: "the tower step is not justified" } : {}));
    const codex = (async (input: CodexRunInput) => {
      if (isRefereeShard(input) && shardIds(input.prompt).includes("lem:mid")) throw new Error("the referee call failed");
      return inner(input);
    }) as typeof runCodex;
    await expect(runStageV1_5(pausing(h.args(codex)))).rejects.toThrow("the referee call failed");
    const halted = await readReview(h.runDir);
    expect(halted.nodes.find((n) => n.id === "lem:deep")).toMatchObject({ correctness: "unclear", graded: "fresh" });
    // The verdict on file of lem:mid was given under `lem:deep: ok`: neither it nor its cache entry survives the halt.
    expect(halted.nodes.map((n) => n.id)).not.toContain("lem:mid");
    expect(h.state.verify!.confirmed).not.toHaveProperty("lem:mid");
    expect(h.state.verify!.level_pause?.carry).not.toHaveProperty("lem:mid");
    expect(h.state.verify!.level_pause?.carry).toHaveProperty("lem:deep");
    // The next pass: lem:deep's grade stands (kept from the halted pass), lem:mid is graded under it;
    // thm:top was given its verdict under `lem:mid: ok`, which lem:mid is graded again — it stands.
    h.state.stage_completed = "V1";
    const next: CodexRunInput[] = [];
    await runStageV1_5(pausing(h.args(fakeCodex(next, 3))));
    expect(gradedIn(next)).toEqual([["lem:mid"]]);
    expect(next.filter(isRefereeShard)[0]!.prompt).toContain("- lem:deep (lemma): unclear — a step was not reproduced (not an error): the tower step is not justified");
    expect((await readReview(h.runDir)).nodes.find((n) => n.id === "thm:top")!.graded).toBe("carried");
  });

  it("a pause after the chain re-opened verdicts (fix as you go): the error stops the grading there; a verdict re-opened and not reached is not kept, and the pass after grades its node under the line that then stands", async () => {
    const h = await stageDir();
    await runStageV1_5(h.args(fakeCodex([], 1)));
    await editTranscribed(h.runDir, "lem:deep", (st) => (st.proof_tex = "Condition on $X$."));
    h.state.stage_completed = "V1";
    const calls: CodexRunInput[] = [];
    const bk = { correctness: "bookkeeping" as const, bookkeeping_assumption: { condition: "$e(X)$ is measurable.", reason: "used silently" } };
    // lem:deep now holds under a condition: lem:mid is re-opened, and graded an error — which re-opens thm:top and pauses.
    const res = await runStageV1_5(pausing(h.args(fakeCodex(calls, 2, (id) => (id === "lem:deep" ? bk : id === "lem:mid" ? IN_SCOPE : {})))));
    expect(res.status).toBe("patch");
    expect(gradedIn(calls)).toEqual([["lem:deep"], ["lem:mid"]]);
    expect(calls.some(isRefereeGlobal)).toBe(false);
    const paused = await readReview(h.runDir);
    expect(h.state.verify!.level_pause).toMatchObject({ level: "L2", errors: [{ id: "lem:mid" }] });
    expect(paused.paused).toMatchObject({ level: "L2", ids: ["lem:mid"], ungraded: ["thm:top"] });
    expect(paused.nodes.find((n) => n.id === "lem:mid")).toMatchObject({ correctness: "error", graded: "fresh" });
    // thm:top's verdict was given under `lem:mid: ok`: it is on file no more, nor cached, nor held by the pause;
    // thm:roof's stands (thm:top's line has not moved — it has none until it is graded).
    expect(paused.nodes.map((n) => n.id)).not.toContain("thm:top");
    expect(h.state.verify!.confirmed).not.toHaveProperty("thm:top");
    expect(Object.keys(h.state.verify!.level_pause!.carry).sort()).toEqual(["ass:overlap", "ass:unconfoundedness", "def:propensity", "lem:deep", "thm:roof"]);
    // Resumed: lem:mid (the error, graded again — clean now) and thm:top under it; thm:roof only if thm:top's verdict moved.
    h.state.stage_completed = "V1";
    const again: CodexRunInput[] = [];
    await runStageV1_5(pausing(h.args(fakeCodex(again, 3, (id) => (id === "lem:deep" ? bk : {})))));
    expect(gradedIn(again)).toEqual([["lem:mid"], ["thm:top"]]);
    const after = await readReview(h.runDir);
    expect(after.nodes.find((n) => n.id === "thm:roof")!.graded).toBe("carried");
    expect(Object.keys(after.nodes.find((n) => n.id === "thm:top")!.basis_inputs!.verdicts!)).toEqual(["lem:mid"]);
  });

  it("transition, the pass pausing: on a scheme-4 file of a complete pass a result whose cache entry was withdrawn is graded — an error, which pauses; its user, forced with it and not reached, keeps no verdict; the results above stand on the line they were re-keyed on", async () => {
    const h = await stageDir();
    await runStageV1_5(h.args(fakeCodex([], 1)));
    const now = await readReview(h.runDir);
    const core = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
    const nodes = now.nodes.map((n) => ({ ...n, basis: basisOf(basisInputsV4(core, n.id)), basis_scheme: 4, basis_inputs: basisInputsV4(core, n.id) }));
    await writeFile(path.join(h.runDir, VERIFY_FILES.v15Review), JSON.stringify({ ...now, nodes }));
    h.state.verify!.confirmed = Object.fromEntries(nodes.filter((n) => n.id !== "lem:deep").map((n) => [n.id, n.basis]));
    h.state.verify!.confirmed_scheme = 4;
    h.state.stage_completed = "V1";
    // lem:deep's cache entry was withdrawn: it is graded — an error. Its direct user is forced with it.
    const calls: CodexRunInput[] = [];
    const logs: string[] = [];
    expect((await runStageV1_5(pausing(h.args(fakeCodex(calls, 2, (id) => (id === "lem:deep" ? IN_SCOPE : {})), (m) => logs.push(m))))).status).toBe("patch");
    expect(logs).toContain("delta review: why re-graded — 0 content changed, 0 dependency changed, 0 symbol meaning changed, 1 dependency verdict changed, 1 cache entry withdrawn");
    expect(gradedIn(calls)).toEqual([["lem:deep"]]);
    const paused = await readReview(h.runDir);
    expect(paused.nodes.map((n) => n.id).sort()).toEqual(["ass:overlap", "ass:unconfoundedness", "def:propensity", "lem:deep", "thm:roof", "thm:top"]);
    // The pass after (the referee now reproduces everything): lem:deep and lem:mid are graded — never
    // `lem:mid: ok` carried over the error; thm:top, re-keyed on `lem:mid: ok`, stands as lem:mid is graded `ok`.
    h.state.stage_completed = "V1";
    const next: CodexRunInput[] = [];
    await runStageV1_5(pausing(h.args(fakeCodex(next, 3))));
    expect(gradedIn(next).flat()).toEqual(["lem:deep", "lem:mid"]);
  });

  it("transition on file: which rule applies is read off the run — a review of a complete pass is carried over whole (a used result's verdict-only condition included); one a pause is recorded on, or a run holding a pause, by the strict rule", async () => {
    const run = async (mark: (h: Awaited<ReturnType<typeof stageDir>>, review: V15Review) => V15Review): Promise<string[]> => {
      const h = await stageDir();
      await runStageV1_5(h.args(fakeCodex([], 1)));
      const now = await readReview(h.runDir);
      const core = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
      const bk = { correctness: "bookkeeping" as const, bookkeeping_assumption: { condition: "$e(X)$ is measurable.", reason: "used silently" } };
      const nodes = now.nodes.map((n) => ({ ...n, ...(n.id === "lem:deep" ? bk : {}), basis: basisOf(basisInputsV4(core, n.id)), basis_scheme: 4, basis_inputs: basisInputsV4(core, n.id) }));
      h.state.verify!.confirmed = Object.fromEntries(nodes.map((n) => [n.id, n.basis]));
      h.state.verify!.confirmed_scheme = 4;
      await writeFile(path.join(h.runDir, VERIFY_FILES.v15Review), JSON.stringify(mark(h, { ...now, nodes })));
      h.state.stage_completed = "V1";
      const calls: CodexRunInput[] = [];
      await runStageV1_5(h.args(fakeCodex(calls, 2, (id) => (id === "lem:deep" ? bk : {}))));
      return gradedIn(calls).flat();
    };
    expect(await run((_h, r) => r)).toEqual([]);
    const above = ["lem:mid", "thm:top", "thm:roof"];
    expect(await run((_h, r) => ({ ...r, paused: { level: "L3", ids: [], ungraded: [] } }))).toEqual(above);
    expect(await run((h, r) => ((h.state.verify!.level_pause = { level: "the merged review", errors: [], via: "halt", round: 0, carry: {}, graded: [], at: "2026-10-07T00:00:00.000Z" }), r))).toEqual(above);
  });

  it("a changed statement of a dependency grades it and its direct users, not the results above", async () => {
    const h = await stageDir();
    await runStageV1_5(h.args(fakeCodex([], 1)));
    await editTranscribed(h.runDir, "lem:deep", (st) => (st.statement += " The identity is exact."));
    h.state.stage_completed = "V1";
    const calls: CodexRunInput[] = [];
    const logs: string[] = [];
    await runStageV1_5(h.args(fakeCodex(calls, 2), (m) => logs.push(m)));
    expect(gradedIn(calls)).toEqual([["lem:deep"], ["lem:mid"]]);
    expect(logs).toContain("delta review: why re-graded — 1 content changed, 1 dependency changed, 0 symbol meaning changed");
  });

  it("transition on file: a run whose review and cache were written under scheme 4 passes with no referee call, re-keyed to scheme 5", async () => {
    const h = await stageDir();
    await runStageV1_5(h.args(fakeCodex([], 1)));
    const now = await readReview(h.runDir);
    const scheme5 = { ...h.state.verify!.confirmed };
    // The run as the earlier code left it: every verdict and cache entry on its scheme-4 basis.
    const core = JSON.parse(await readFile(path.join(h.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
    const nodes = now.nodes.map((n) => ({ ...n, basis: basisOf(basisInputsV4(core, n.id)), basis_scheme: 4, basis_inputs: basisInputsV4(core, n.id) }));
    await writeFile(path.join(h.runDir, VERIFY_FILES.v15Review), JSON.stringify({ ...now, nodes }));
    h.state.verify!.confirmed = Object.fromEntries(nodes.map((n) => [n.id, n.basis]));
    h.state.verify!.confirmed_scheme = 4;
    expect(h.state.verify!.confirmed["thm:top"]).not.toBe(scheme5["thm:top"]);
    h.state.stage_completed = "V1";
    const calls: CodexRunInput[] = [];
    const logs: string[] = [];
    expect((await runStageV1_5(h.args(fakeCodex(calls, 2), (m) => logs.push(m)))).status).toBe("completed");
    expect(calls).toEqual([]);
    expect(logs).toContain(`verdict bases: the cache was recorded under basis scheme 4: each verdict whose scheme-4 basis still holds is carried over to scheme ${BASIS_SCHEME}, with no call`);
    expect(logs).toContain("delta review: 0 of 7 node(s) to grade afresh, 7 verdict(s) carried on an unchanged basis");
    expect(h.state.verify!.confirmed).toEqual(scheme5);
    expect(h.state.verify!.confirmed_scheme).toBe(BASIS_SCHEME);
    const after = await readReview(h.runDir);
    expect(after.nodes.map((n) => [n.id, n.basis_scheme, n.basis, n.graded]).sort()).toEqual(now.nodes.map((n) => [n.id, BASIS_SCHEME, n.basis, "carried"]).sort());
  });
});
