import { readFileSync } from "node:fs";
/**
 * The core graph: one edit language, derived wiring, one invariant. Unit cases for each
 * operation, then a seeded fuzz — random DAG cores × random patch files × random reviews —
 * asserting the invariant on every build. No network.
 */
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import {
  CoreGraphInputError,
  PIN_REASON_PREFIX,
  applyEdits,
  bindingReadings,
  conditionsOn,
  isReadingAddition,
  patchConditionId,
  patchReadingId,
  renderBindingReadings,
  buildCore,
  checkCoreInvariants,
  citedLabels,
  compilePatchEdits,
  normalizeCore,
  pinsOn,
  renderHypothesisList,
  type GraphEdit,
  type PatchFileLike,
} from "../../src/verify/core_graph.js";
import { PatchFileSchema } from "../../src/verify/patches.js";
import type { V15NodeVerdict, V15Review } from "../../src/verify/types.js";

function core(): Core {
  return {
    qid: "verify_toy_graph",
    symbols: [],
    assumptions: [
      { id: "ass:overlap", condition: "overlap", novel: { flag: true, justification: "A1" }, used_by: ["lem:rate"] },
      { id: "ass:iid", condition: "iid", novel: { flag: true, justification: "A2" } },
    ],
    definitions: [{ id: "def:est", name: "estimator", construction: "the IPW estimator" }],
    statements: [
      { id: "lem:rate", kind: "lemma", statement: "the rate holds [Hypotheses: ass:overlap]", depends_on: ["ass:overlap", "def:est"], status: "to-prove", proof_tex: "P1" },
      { id: "thm:main", kind: "theorem", statement: "normality", depends_on: ["lem:rate", "ass:iid"], status: "to-prove", proof_tex: "P2" },
      { id: "thm:side", kind: "theorem", statement: "variance", depends_on: ["lem:rate"], status: "to-prove" },
      { id: "prop:aside", kind: "proposition", statement: "an identity", depends_on: [], status: "to-prove" },
    ],
    target_estimand: "tau",
  } as unknown as Core;
}

function verdict(id: string, over: Partial<V15NodeVerdict> = {}): V15NodeVerdict {
  return { id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "", witness: null, bookkeeping_assumption: null, reading: null, ...over };
}

describe("applyEdits", () => {
  it("applies each operation and rejects what does not fit, leaving the input untouched", () => {
    const input = core();
    const edits: GraphEdit[] = [
      { op: "add_assumption", node: { id: "ass:bk-x", condition: "x", bookkeeping: { flag: true, added_by: "V1.5", reason: "r" }, used_by: ["ignored"] } as Core["assumptions"][number] },
      { op: "wire", statement: "thm:main", dep: "ass:bk-x" },
      { op: "wire", statement: "thm:main", dep: "ass:bk-x" }, // idempotent
      { op: "unwire", statement: "thm:main", dep: "ass:iid" },
      { op: "set_statement", id: "thm:main", statement: "corrected normality" },
      // set_statement sets an assumption's condition and a definition's construction too
      { op: "set_statement", id: "ass:overlap", statement: "strict overlap" },
      { op: "set_statement", id: "def:est", statement: "the Hajek estimator" },
      { op: "append_proof", id: "thm:main", text: "[change]" },
      { op: "append_proof", id: "thm:side", text: "[change]" }, // no prior proof
      { op: "remove_node", id: "prop:aside", why: "descoped" },
      // rejected:
      { op: "wire", statement: "ass:overlap", dep: "ass:iid" },
      { op: "wire", statement: "thm:main", dep: "ass:ghost" },
      { op: "wire", statement: "thm:main", dep: "thm:main" },
      { op: "remove_node", id: "nope", why: "" },
      { op: "add_assumption", node: { id: "ass:iid", condition: "dup" } as Core["assumptions"][number] },
      { op: "set_statement", id: "ass:nope", statement: "not a node" },
    ];
    const { core: out, rejected } = applyEdits(input, edits);
    expect(rejected).toHaveLength(6);
    const main = out.statements.find((s) => s.id === "thm:main")!;
    expect(main.depends_on).toEqual(["lem:rate", "ass:bk-x"]);
    expect(out.assumptions.find((a) => a.id === "ass:overlap")!.condition).toBe("strict overlap");
    expect(out.definitions.find((d) => d.id === "def:est")!.construction).toBe("the Hajek estimator");
    expect(main.statement).toBe("corrected normality");
    expect(main.proof_tex).toBe("P2\n\n[change]");
    expect(out.statements.find((s) => s.id === "thm:side")!.proof_tex).toBe("[change]");
    expect(out.statements.some((s) => s.id === "prop:aside")).toBe(false);
    expect(out.assumptions.find((a) => a.id === "ass:bk-x")!.used_by).toBeUndefined(); // derived later
    expect(input).toEqual(core());
  });
});

describe("normalizeCore", () => {
  it("derives used_by from depends_on and re-renders the printed hypothesis list only where something changed; a statement changed only by a referee wire (bk / pin) keeps its bytes", () => {
    const transcribed = core();
    const c = core();
    c.statements.find((s) => s.id === "lem:rate")!.depends_on = ["def:est"]; // a repair superseded ass:overlap
    c.statements.find((s) => s.id === "thm:main")!.depends_on.push("ass:bk-1");
    c.assumptions.push({ id: "ass:bk-1", condition: "finite variance", bookkeeping: { flag: true, added_by: "V1.5", reason: "r" } } as Core["assumptions"][number]);
    const out = normalizeCore(c, transcribed);
    expect(out.assumptions.find((a) => a.id === "ass:overlap")!.used_by).toBeUndefined();
    expect(out.assumptions.find((a) => a.id === "ass:iid")!.used_by).toEqual(["thm:main"]);
    expect(out.statements.find((s) => s.id === "lem:rate")!.statement).toBe("the rate holds");
    // a referee addition is wired but not printed; a statement with no printed list stays bare
    expect(out.statements.find((s) => s.id === "thm:main")!.statement).toBe("normality");
    expect(out.statements.find((s) => s.id === "thm:side")!.statement).toBe("variance");
    // changed only by a referee wire: the statement keeps its bytes
    const transcribed2 = core();
    const c2 = core();
    c2.statements.find((s) => s.id === "lem:rate")!.statement = "the rate holds   [Hypotheses:ass:overlap]"; // odd spacing, as a hand edit might leave
    transcribed2.statements.find((s) => s.id === "lem:rate")!.statement = "the rate holds   [Hypotheses:ass:overlap]";
    c2.statements.find((s) => s.id === "lem:rate")!.depends_on.push("ass:bk-1");
    c2.assumptions.push({ id: "ass:bk-1", condition: "c", bookkeeping: { flag: true, added_by: "V1.5", reason: "r" } } as Core["assumptions"][number]);
    expect(normalizeCore(c2, transcribed2).statements.find((s) => s.id === "lem:rate")!.statement).toBe("the rate holds   [Hypotheses:ass:overlap]");
  });

  it("renderHypothesisList keeps the printed order, drops removed ids, adds nothing, and never invents a list", () => {
    expect(renderHypothesisList("x [Hypotheses: ass:z]", "p [Hypotheses: ass:a, ass:b]", ["ass:b", "ass:a", "ass:q", "ass:bk-1"])).toBe("x [Hypotheses: ass:a, ass:b]");
    expect(renderHypothesisList("x", "p [Hypotheses: ass:a]", [])).toBe("x");
    expect(renderHypothesisList("x", "p", ["ass:q"])).toBe("x");
    // a statement printed without a list is returned byte-for-byte (a corrected text's trailing
    // newline survives); only a stray list on it is stripped
    expect(renderHypothesisList("x \n", "p", ["ass:q"])).toBe("x \n");
    expect(renderHypothesisList("x [Hypotheses: ass:q]", "p", [])).toBe("x");
  });
});

describe("checkCoreInvariants", () => {
  it("names every broken condition", () => {
    const c = core();
    c.statements[1].depends_on.push("ass:ghost");
    c.statements[2].statement = "variance [Hypotheses: ass:iid]";
    c.definitions.push({ id: "ass:iid", name: "dup", construction: "dup" } as Core["definitions"][number]);
    const bad = checkCoreInvariants(c);
    expect(bad.some((b) => b.includes('"thm:main" depends on "ass:ghost"'))).toBe(true);
    expect(bad.some((b) => b.includes('"ass:overlap".used_by'))).toBe(false); // consistent
    expect(bad.some((b) => b.includes('"ass:iid".used_by'))).toBe(true); // thm:main uses it, list absent
    expect(bad.some((b) => b.includes('"thm:side" prints hypothesis "ass:iid"'))).toBe(true);

    expect(bad.some((b) => b.includes('id "ass:iid" names more than one node'))).toBe(true);
    expect(checkCoreInvariants(normalizeCore(core(), core()))).toEqual([]);
  });
});

describe("buildCore", () => {
  const file = (over: Partial<PatchFileLike> = {}): PatchFileLike => ({
    key_results: ["thm:main"],
    patches: [
      {
        node: "lem:rate",
        corrected_statement: "the corrected rate holds under two-sided overlap",
        supersedes: ["ass:overlap"],
        proof_note: "bound both tails",
      },
    ],
    unfixable: [],
    ...over,
  });

  it("patches, unwires what a replacement supersedes, adds no node, derives wiring, and passes its own invariant", () => {
    const { core: out, descoped } = buildCore(core(), { patches: file() });
    expect(checkCoreInvariants(out)).toEqual([]);
    expect(descoped.size).toBe(0);
    const rate = out.statements.find((s) => s.id === "lem:rate")!;
    // the superseded hypothesis leaves the wiring and the printed list; the corrected text states it
    expect(rate.statement).toBe("the corrected rate holds under two-sided overlap");
    expect(rate.depends_on).toEqual(["def:est"]);
    expect(rate.proof_tex).toContain("[Proof change (minimal patch): bound both tails]");
    // no hypothesis node is added, and the users of lem:rate keep their own wiring
    expect(out.statements.find((s) => s.id === "thm:main")!.depends_on).toEqual(["lem:rate", "ass:iid"]);
    expect(out.statements.find((s) => s.id === "thm:side")!.depends_on).toEqual(["lem:rate"]);
    // ass:overlap lost its only user: the corrected statement states it, so it leaves the core (live CNS
    // 2026-09-27: graded alone, a superseded cross-reference premise drew a drift no model could fix)
    expect(out.assumptions.map((a) => a.id).sort()).toEqual(["ass:iid"]);
    // a repair of an assumption's or a definition's own text sets its condition / construction; its users keep it
    const own = buildCore(core(), {
      patches: file({
        patches: [
          { node: "ass:overlap", corrected_statement: "two-sided overlap", proof_note: "n" },
          { node: "def:est", corrected_statement: "the Hajek estimator", proof_note: "n" },
        ],
      }),
    }).core;
    expect(own.assumptions.find((a) => a.id === "ass:overlap")!.condition).toBe("two-sided overlap");
    expect(own.assumptions.find((a) => a.id === "ass:overlap")!.used_by).toEqual(["lem:rate"]);
    expect(own.definitions.find((d) => d.id === "def:est")!.construction).toBe("the Hajek estimator");
    expect(own.statements.find((s) => s.id === "lem:rate")!.statement).toBe("the rate holds [Hypotheses: ass:overlap]");
    expect(checkCoreInvariants(own)).toEqual([]);
  });

  it("compilePatchEdits: supersedes → unwire on a statement only; the corrected text of any node → set_statement", () => {
    const { edits } = compilePatchEdits(core(), {
      key_results: [],
      patches: [
        { node: "lem:rate", corrected_statement: "r", supersedes: ["ass:overlap", "def:est"], proof_note: "p" },
        { node: "ass:iid", corrected_statement: "iid within strata", supersedes: ["ass:overlap"], proof_note: "p" },
        { node: "thm:ghost", corrected_statement: "g", supersedes: ["ass:iid"], proof_note: "p" },
      ],
      unfixable: [],
    });
    expect(edits.filter((e) => e.op === "unwire")).toEqual([
      { op: "unwire", statement: "lem:rate", dep: "ass:overlap" },
      { op: "unwire", statement: "lem:rate", dep: "def:est" },
    ]);
    expect(edits.filter((e) => e.op === "set_statement").map((e) => (e as { id: string }).id)).toEqual(["lem:rate", "ass:iid"]);
    // a proof change only for a statement
    expect(edits.filter((e) => e.op === "append_proof" || e.op === "set_proof").map((e) => (e as { id: string }).id)).toEqual(["lem:rate"]);
  });

  it("compilePatchEdits: a restated result is unwired from the repaired assumption its consequence_of names, or from a hypothesis with no printed text of its own (a patch with no ops); an unrestated one keeps it", () => {
    const { edits } = compilePatchEdits(core(), {
      key_results: [],
      patches: [
        { node: "ass:overlap", corrected_statement: "two-sided overlap", proof_note: "n" },
        { node: "lem:rate", corrected_statement: "the rate holds under two-sided overlap", consequence_of: ["ass:overlap"], proof_note: "p" },
        { node: "ass:iid", corrected_statement: "iid within strata", proof_note: "n" },
        { node: "thm:main", corrected_statement: null, consequence_of: ["ass:iid"], proof_note: "p" },
      ],
      unfixable: [],
    });
    expect(edits.filter((e) => e.op === "unwire")).toEqual([{ op: "unwire", statement: "lem:rate", dep: "ass:overlap" }]);
    // a textless hypothesis patch: every restated user leaves it, with or without consequence_of
    const { edits: textless } = compilePatchEdits(core(), {
      key_results: [],
      patches: [
        { node: "ass:overlap", corrected_statement: null, ops: [], proof_note: "restated in lem:rate" },
        // lem:rate has a finding of its own: it restates the hypothesis in its own repair, no consequence_of
        { node: "lem:rate", corrected_statement: "the rate holds under two-sided overlap", proof_note: "p" },
      ],
      unfixable: [],
    });
    expect(textless.filter((e) => e.op === "unwire")).toEqual([{ op: "unwire", statement: "lem:rate", dep: "ass:overlap" }]);
    // … unless the restated result declares it still uses it (`adds`): that edge survives, and so does the hypothesis
    const kept = buildCore(core(), {
      patches: {
        key_results: [],
        patches: [
          { node: "ass:overlap", corrected_statement: null, ops: [], proof_note: "restated in lem:rate" },
          { node: "lem:rate", corrected_statement: "the rate holds under two-sided overlap", adds: ["ass:overlap"], proof_note: "p" },
        ],
        unfixable: [],
      },
    }).core;
    expect(kept.statements.find((s) => s.id === "lem:rate")!.depends_on).toContain("ass:overlap");
    expect(kept.assumptions.map((a) => a.id)).toContain("ass:overlap");
  });

  // Live extreme-effects (2026-10-08): the fixer filed a no-op entry on the printed algorithm as a
  // consequence of two corollaries; every result restated for whatever reason was unwired from it and
  // the algorithm left the core, though the lemmas about its other steps still used it.
  it("a hypothesis with no printed text whose entry names the results it follows is restated away from those only: a result restated for another reason keeps it, and it stays in the core", () => {
    const k = (): Core => {
      const c = core();
      c.definitions.push({ id: "def:proc", name: "procedure", construction: "split; fit; average; estimate the index" } as never);
      c.statements.push({ id: "lem:index", kind: "lemma", statement: "the index estimate is consistent", depends_on: ["def:proc"], status: "to-prove" } as never);
      for (const id of ["lem:rate", "thm:main", "thm:side"]) c.statements.find((x) => x.id === id)!.depends_on.push("def:proc");
      return c;
    };
    const patches = (consequence_of: string[] | null) =>
      file({
        patches: [
          { node: "def:proc", corrected_statement: null, ops: [], proof_note: "restated", consequence_of, ...(consequence_of ? { reason: "the theorem states its own index step" } : {}) },
          { node: "thm:main", corrected_statement: "normality, with the index of the lemma", proof_note: "p" },
          { node: "lem:index", corrected_statement: "the full-sample index estimate is consistent", drops: ["def:proc"], proof_note: "p" },
          { node: "lem:rate", corrected_statement: "the rate holds under a moment bound [Hypotheses: ass:overlap]", proof_note: "p" },
        ],
      });
    const uses = (c: Core): string[] => c.statements.filter((x) => x.depends_on.includes("def:proc")).map((x) => x.id);
    const named = buildCore(k(), { patches: patches(["thm:main"]) }).core;
    expect(uses(named)).toEqual(["lem:rate", "thm:side"]);
    expect(named.definitions.map((d) => d.id)).toContain("def:proc");
    expect(checkCoreInvariants(named)).toEqual([]);
    // the finding is the hypothesis's own (no `consequence_of`): every restated result leaves it, as before
    const own = buildCore(k(), { patches: patches(null) }).core;
    expect(uses(own)).toEqual(["thm:side"]);
    // … and it leaves the core once the results named were its only users left
    const last = k();
    for (const id of ["lem:rate", "thm:side"]) ((st) => (st.depends_on = st.depends_on.filter((d) => d !== "def:proc")))(last.statements.find((x) => x.id === id)!);
    expect(buildCore(last, { patches: patches(["thm:main"]) }).core.definitions.map((d) => d.id)).not.toContain("def:proc");
    // a restated user the entry cannot name (its own patch only follows the theorem's repair): it
    // leaves the hypothesis by its own `drops`, and without one stays wired to the printed text
    const follower = (drops?: string[]) =>
      file({
        patches: [
          { node: "def:proc", corrected_statement: null, ops: [], proof_note: "restated", consequence_of: ["thm:main"] },
          { node: "thm:main", corrected_statement: "normality, with the index of the lemma", proof_note: "p" },
          { node: "thm:side", corrected_statement: "variance, with the index of the lemma", consequence_of: ["thm:main"], proof_note: "p", ...(drops ? { drops } : {}) },
        ],
      });
    expect(uses(buildCore(k(), { patches: follower() }).core)).toEqual(["lem:rate", "thm:side", "lem:index"]);
    expect(uses(buildCore(k(), { patches: follower(["def:proc"]) }).core)).toEqual(["lem:rate", "lem:index"]);
    const brief = readFileSync(new URL("../../src/verify/prompts/V1/patch.txt", import.meta.url), "utf8").replace(/\s+/g, " ");
    expect(brief).toContain("one whose own patch only follows other repairs — that restates the node lists it in its `drops`");
    const referee = readFileSync(new URL("../../src/verify/prompts/V1.5/review.txt", import.meta.url), "utf8").replace(/\s+/g, " ");
    expect(referee).toContain("for the results that patch names in `consequence_of` (every restated result using it when it names none)");
    expect(referee).toContain("Another patched result still uses that hypothesis as printed and keeps the edge, which is no wrong wiring");
    expect(referee).not.toContain("(restated in each result using it)");
    expect(brief).toContain("a result that replaces one step of a definition and still uses the rest says so in its corrected statement, and the definition takes no entry");
  });

  it("citedLabels: \\ref and its kin, comma lists split", () => {
    expect(citedLabels("By Lemma~\\ref{lem::a} and \\cref{thm::b, eq:c}; see \\eqref*{eq:c}.")).toEqual(["lem::a", "thm::b", "eq:c"]);
    expect(citedLabels("By Lemma~\\ref{lem::a}. % see \\ref{lem::b}\nAt 50\\% of \\ref{lem::c}.")).toEqual(["lem::a", "lem::c"]);
  });

  it("compilePatchEdits: a result the repair's own text cites is wired in — not when the label names two results, the result itself, or would close a cycle", () => {
    const c = core();
    const loc = (label: string) => ({ file: "main.tex", from: 1, to: 2, env: "lemma", label });
    const byId = (id: string) => c.statements.find((s) => s.id === id)! as { tex_locator?: unknown };
    byId("lem:rate").tex_locator = loc("lemma:rate");
    byId("thm:side").tex_locator = loc("thm:side");
    byId("prop:aside").tex_locator = loc("prop:aside");
    byId("thm:main").tex_locator = loc("thm:split");
    const cites = (node: string, tex: string) => compilePatchEdits(c, { key_results: [], patches: [{ node, corrected_statement: null, ops: [{ op: "replace", unit: `${node}/proof/1/1`, tex }], proof_note: "amended" }], unfixable: [] }).edits.filter((e) => e.op === "wire");
    // thm:side's repaired proof now cites prop:aside: wired; lem:rate it already uses: nothing new.
    expect(cites("thm:side", "By Proposition~\\ref{prop:aside} and Lemma~\\ref{lemma:rate}, done.")).toEqual([{ op: "wire", statement: "thm:side", dep: "prop:aside" }]);
    // lem:rate citing thm:side would close a cycle (thm:side uses lem:rate); citing itself is no edge.
    expect(cites("lem:rate", "As in Theorem~\\ref{thm:side} and Lemma~\\ref{lemma:rate}.")).toEqual([]);
    // a result the repair declares it does not use (`drops`) is not wired, though its text cites it
    // (live cns: a bandwidth comparison with Corollary CI-local wired thm:local into it; the referee's
    // removal could not stick since every rebuild re-wired the citation)
    expect(compilePatchEdits(c, { key_results: [], patches: [{ node: "thm:side", corrected_statement: null, ops: [{ op: "replace", unit: "thm:side/proof/1/1", tex: "Compare Proposition~\\ref{prop:aside}." }], drops: ["prop:aside"], proof_note: "amended" }], unfixable: [] }).edits.filter((e) => e.op === "wire")).toEqual([]);
    // a label two results share (a passage split into clauses) is left to the referee
    byId("prop:aside").tex_locator = loc("thm:split");
    expect(cites("thm:side", "By \\ref{thm:split}.")).toEqual([]);
  });

  it("compilePatchEdits: a hypothesis a corrected statement supersedes, or a repaired assumption, leaves the core once no surviving result uses it; one still used stays", () => {
    const supersede = (c: Core) =>
      compilePatchEdits(c, { key_results: [], patches: [{ node: "lem:rate", corrected_statement: "the rate holds under two-sided overlap", supersedes: ["ass:overlap"], proof_note: "p" }], unfixable: [] }).edits.filter((e) => e.op === "remove_node");
    expect(supersede(core())).toEqual([{ op: "remove_node", id: "ass:overlap", why: "restated into the results that use it" }]);
    const shared = core();
    shared.statements.find((s) => s.id === "thm:side")!.depends_on.push("ass:overlap");
    expect(supersede(shared)).toEqual([]);
    expect(buildCore(core(), { patches: { key_results: [], patches: [{ node: "lem:rate", corrected_statement: "the rate holds under two-sided overlap", supersedes: ["ass:overlap"], proof_note: "p" }], unfixable: [] } }).core.assumptions.map((a) => a.id)).toEqual(["ass:iid"]);
    // a repaired assumption whose only user restates it (consequence_of) leaves the core too
    const patches: PatchFileLike = {
      key_results: ["thm:main"],
      patches: [
        { node: "ass:overlap", corrected_statement: "two-sided overlap", proof_note: "n" },
        { node: "lem:rate", corrected_statement: "the rate holds under two-sided overlap", consequence_of: ["ass:overlap"], proof_note: "p" },
        { node: "ass:iid", corrected_statement: "iid within strata", proof_note: "n" },
      ],
      unfixable: [],
    };
    expect(compilePatchEdits(core(), patches).edits.filter((e) => e.op === "remove_node")).toEqual([{ op: "remove_node", id: "ass:overlap", why: "restated into the results that use it" }]);
    const { core: out } = buildCore(core(), { patches });
    expect(out.assumptions.map((a) => a.id)).toEqual(["ass:iid"]);
    expect(out.assumptions[0]!.condition).toBe("iid within strata");
    expect(out.assumptions[0]!.used_by).toEqual(["thm:main"]);
    expect(out.statements.find((s) => s.id === "lem:rate")!.depends_on).toEqual(["def:est"]);
    expect(checkCoreInvariants(out)).toEqual([]);
  });

  it("descopes an unfixable side result with what rests on it, and removes an unfixable non-statement", () => {
    const c = core();
    c.statements.push({ id: "cor:x", kind: "theorem", statement: "cor", depends_on: ["thm:side"], status: "to-prove" } as Core["statements"][number]);
    const { core: out, descoped } = buildCore(c, { patches: file({ patches: [], unfixable: [{ node: "thm:side", reason: "no repair" }] }) });
    expect([...descoped.keys()].sort()).toEqual(["cor:x", "thm:side"]);
    expect(out.statements.map((s) => s.id).sort()).toEqual(["lem:rate", "prop:aside", "thm:main"]);
    expect(checkCoreInvariants(out)).toEqual([]);
    const { core: out2 } = buildCore(c, { patches: file({ patches: [], key_results: ["prop:aside"], unfixable: [{ node: "ass:overlap", reason: "false" }] }) });
    expect(out2.assumptions.some((a) => a.id === "ass:overlap")).toBe(false);
    expect(out2.statements.map((s) => s.id).sort()).toEqual(["prop:aside"]); // lem:rate used it; thm:* rest on lem:rate
    expect(checkCoreInvariants(out2)).toEqual([]);
  });

  it("applies the review's bookkeeping and pinned readings against the PATCHED core, numbering past taken ids; pinsOn reads them back with the node each pins", () => {
    const review: V15Review = {
      verdict: "PASS",
      summary: "",
      nodes: [
        verdict("thm:main", { correctness: "bookkeeping", bookkeeping_assumption: { condition: "finite variance", reason: "CLT" } }),
        verdict("def:est", { ambiguity: "pinned", reading: { reading: "the Horvitz–Thompson form", evidence: "eq. 3" } }),
        verdict("ass:iid", { ambiguity: "pinned", reading: { reading: "iid across units", evidence: "§2" } }),
        verdict("prop:aside", { ambiguity: "pinned", reading: { reading: "unused pin", evidence: "—" } }),
      ],
    };
    const c = core();
    c.assumptions.push({ id: "ass:bk-1", condition: "already there", novel: { flag: true, justification: "x" } } as Core["assumptions"][number]);
    const { core: out, added } = buildCore(c, { patches: file(), review });
    expect(checkCoreInvariants(out)).toEqual([]);
    expect(added.map((a) => a.id)).toEqual(["ass:bk-2", "ass:pin-1", "ass:pin-2", "ass:pin-3"]);
    expect(out.statements.find((s) => s.id === "thm:main")!.depends_on).toContain("ass:bk-2");
    // def:est is used by lem:rate only → its pin lands there; ass:iid → thm:main; prop:aside pins itself
    expect(out.assumptions.find((a) => a.id === "ass:pin-1")!.used_by).toEqual(["lem:rate"]);
    expect(out.assumptions.find((a) => a.id === "ass:pin-2")!.used_by).toEqual(["thm:main"]);
    expect(out.assumptions.find((a) => a.id === "ass:pin-3")!.used_by).toEqual(["prop:aside"]);
    // referee additions are wired, not printed
    expect(out.statements.find((s) => s.id === "lem:rate")!.statement).toBe("the corrected rate holds under two-sided overlap");
    // pinsOn reads back the pinned readings wired into a statement
    const pinReview: V15Review = { verdict: "PASS", summary: "", nodes: [verdict("def:est", { ambiguity: "pinned", reading: { reading: "the HT form", evidence: "eq. 3" } })] };
    const { core: pinned } = buildCore(core(), { review: pinReview });
    expect(pinsOn(pinned, "lem:rate")).toEqual([{ id: "ass:pin-1", node: "def:est", reading: "the HT form", by: "referee" }]);
    expect(pinsOn(pinned, "thm:main")).toEqual([]);
  });

  it("referee additions keep stable ids across passes: a new pin takes a fresh number, a dropped one retires its number (live cns: renumbering left a Lean tag on another reading)", () => {
    const pin = (id: string, reading: string) => verdict(id, { ambiguity: "pinned", reading: { reading, evidence: "e" } });
    const ids: Record<string, string> = {};
    const first = buildCore(core(), { review: { verdict: "PASS", summary: "", nodes: [pin("ass:iid", "iid across units"), pin("prop:aside", "an identity")] }, addedIds: ids });
    expect(first.added.map((a) => a.id)).toEqual(["ass:pin-1", "ass:pin-2"]);
    // A new pin graded BEFORE the others in review order, and the first pin dropped:
    const second = buildCore(core(), { review: { verdict: "PASS", summary: "", nodes: [pin("def:est", "the HT form"), pin("prop:aside", "an identity")] }, addedIds: ids });
    const byNode = Object.fromEntries(second.added.map((a) => [a.node, a.id]));
    expect(byNode["prop:aside"]).toBe("ass:pin-2"); // kept
    expect(byNode["def:est"]).toBe("ass:pin-3"); // fresh; ass:pin-1 stays retired for "iid across units"
    expect(second.core.assumptions.find((a) => a.id === "ass:pin-2")!.condition).toBe("an identity");
    // Without the map, numbering is by order (the old behaviour).
    expect(buildCore(core(), { review: { verdict: "PASS", summary: "", nodes: [pin("def:est", "the HT form"), pin("prop:aside", "an identity")] } }).added.map((a) => a.id)).toEqual(["ass:pin-1", "ass:pin-2"]);
  });

  it("a reading of an assumption's phrase noticed on a result (reading.of) binds every result using the assumption (live drdid: a sampling reading pinned on one result left the siblings asking)", () => {
    const c = core();
    c.statements.find((s) => s.id === "thm:side")!.depends_on.push("ass:iid");
    const review: V15Review = {
      verdict: "PASS",
      summary: "",
      nodes: [verdict("thm:main", { ambiguity: "pinned", reading: { reading: "each draw from the one population", evidence: "§2", of: "ass:iid" } })],
    };
    const { core: out } = buildCore(c, { review });
    const pin = out.assumptions.find((a) => a.id === "ass:pin-1")!;
    expect(pin.used_by).toEqual(["thm:main", "thm:side"]);
    expect(pinsOn(out, "thm:side")).toEqual([{ id: "ass:pin-1", node: "ass:iid", reading: "each draw from the one population", by: "referee" }]);
    // an `of` naming no assumption or definition keeps the pin on the graded node
    const stray: V15Review = { ...review, nodes: [verdict("thm:main", { ambiguity: "pinned", reading: { reading: "r", evidence: "e", of: "thm:side" } })] };
    expect(buildCore(c, { review: stray }).core.assumptions.find((a) => a.id === "ass:pin-1")!.used_by).toEqual(["thm:main"]);
  });

  it("a repair's readings are pinned beside the statement, wired into it, and bind like every pin", () => {
    const f = file();
    f.patches[0]!.readings = ["the rate is uniform over the class"];
    const { core: built } = buildCore(core(), { patches: f });
    const id = patchReadingId("lem:rate", "the rate is uniform over the class");
    expect(id).toMatch(/^ass:pin-fix-[0-9a-f]{8}$/);
    const pin = built.assumptions.find((x) => x.id === id)!;
    expect(pin.condition).toBe("the rate is uniform over the class");
    expect(isReadingAddition(pin)).toBe(true);
    const rate = built.statements.find((x) => x.id === "lem:rate")!;
    expect(rate.depends_on).toContain(id);
    expect(rate.statement).not.toContain("uniform over the class");
    expect(renderBindingReadings(bindingReadings(built, "lem:rate"))).toContain(`${id} (reading of lem:rate, stated by its repair): the rate is uniform over the class`);
    // the fixer's reply: null or blank readings read as absent, a list is kept
    const entry = (readings: unknown) => PatchFileSchema.parse({ patches: [{ node: "lem:rate", corrected_statement: null, proof_note: "p", readings }] }).patches[0]!.readings;
    expect(entry(null)).toBeUndefined();
    expect(entry(["  "])).toBeUndefined();
    expect(entry([" on all of R "])).toEqual(["on all of R"]);
    // the same reading re-typeset keeps its id; without readings nothing is added
    expect(patchReadingId("lem:rate", "the  rate is uniform over the class")).toBe(id);
    expect(buildCore(core(), { patches: file() }).core.assumptions.some((x) => x.id.startsWith("ass:pin-fix-"))).toBe(false);
  });

  it("a repair's side conditions are bookkeeping conditions beside the statement, never pins, never in its text", () => {
    const f = file();
    f.patches[0]!.conditions = ["the fitted nuisances are measurable with respect to the training split"];
    const { core: built } = buildCore(core(), { patches: f });
    const id = patchConditionId("lem:rate", "the fitted nuisances are measurable with respect to the training split");
    expect(id).toMatch(/^ass:bk-fix-[0-9a-f]{8}$/);
    const bk = built.assumptions.find((x) => x.id === id)!;
    expect(isReadingAddition(bk)).toBe(true);
    expect(bk.bookkeeping?.reason.startsWith(PIN_REASON_PREFIX)).toBe(false);
    const rate = built.statements.find((x) => x.id === "lem:rate")!;
    expect(rate.depends_on).toContain(id);
    expect(rate.statement).not.toContain("measurable");
    // the annotated paper's "Bookkeeping condition:" note, written by the fixer; not a pinned reading
    expect(conditionsOn(built, "lem:rate")).toEqual([{ id, condition: bk.condition, by: "repair" }]);
    expect(pinsOn(built, "lem:rate")).toEqual([]);
    expect(renderBindingReadings(bindingReadings(built, "lem:rate"))).toContain(`${id} (condition of lem:rate, stated by its repair): ${bk.condition}`);
    // the fixer's reply: null reads as absent
    expect(PatchFileSchema.parse({ patches: [{ node: "lem:rate", corrected_statement: null, proof_note: "p", conditions: null }] }).patches[0]!.conditions).toBeUndefined();
  });

  it("tells an operator's input mistake (CoreGraphInputError, names the file) from a runner bug (plain Error)", () => {
    // a stale patch file naming a node the re-transcription dropped: skipped, never a crash
    const stale = file({ patches: [{ ...file().patches[0], node: "thm:ghost" }] });
    expect(() => buildCore(core(), { patches: stale })).not.toThrow();
    // two repairs of the same assumption, one superseding it in its user: never a crash
    const twice = file({
      patches: [
        { node: "ass:overlap", corrected_statement: "c", proof_note: "n" },
        { node: "lem:rate", corrected_statement: null, supersedes: ["ass:overlap"], proof_note: "n" },
        { node: "ass:overlap", corrected_statement: "c again", proof_note: "again" },
      ],
    });
    expect(() => buildCore(core(), { patches: twice })).not.toThrow();
    // a hand-written umbrella whose two blocks read the same (one block by id) → the patch file's fault, never "a runner bug"
    const sameBlocks = file({ patches: [{ node: "thm:main", corrected_statement: null, ops: [], proof_note: "x", umbrella: true, corollaries: [{ statement: "The bound holds.", follows: "f" }, { statement: "The bound holds.", follows: "g" }] }] });
    let umbrellaErr: unknown;
    try {
      buildCore(core(), { patches: sameBlocks });
    } catch (e) {
      umbrellaErr = e;
    }
    expect(umbrellaErr).toBeInstanceOf(CoreGraphInputError);
    expect((umbrellaErr as CoreGraphInputError).file).toBe("patches.json");
    expect((umbrellaErr as CoreGraphInputError).problems.join(" ")).toMatch(/thm:main: an umbrella needs at least two blocks that differ \(2 given, 1 distinct/);
    // a hand-edited transcription with a dangling dependency → the operator's file, named
    const dangling = core();
    dangling.statements[0].depends_on.push("ass:ghost");
    let err: unknown;
    try {
      buildCore(dangling, { patches: file() });
    } catch (e) {
      err = e;
    }
    expect(err).toBeInstanceOf(CoreGraphInputError);
    expect((err as CoreGraphInputError).file).toBe("core.transcribed.json");
    expect((err as CoreGraphInputError).problems.join(" ")).toContain('"lem:rate" depends on "ass:ghost"');
    // a hand-edited transcription whose printed list names an id it does not depend on
    const listed = core();
    listed.statements[1].statement = "normality [Hypotheses: ass:overlap]";
    expect(() => buildCore(listed)).toThrow(CoreGraphInputError);
    // an owner reading colliding with a node of the transcription → the patch file, named
    const collide = file({ owner_readings: [{ id: "ass:iid", node: "lem:rate", reading: "r" }] });
    try {
      buildCore(core(), { patches: collide });
      err = null;
    } catch (e) {
      err = e;
    }
    expect((err as CoreGraphInputError).file).toBe("patches.json");
    // a review that names a non-statement for bookkeeping is the contract check's failure: a runner bug
    const review: V15Review = { verdict: "PASS", summary: "", nodes: [verdict("ass:iid", { correctness: "bookkeeping", bookkeeping_assumption: { condition: "c", reason: "r" } })] };
    expect(() => buildCore(core(), { review })).toThrow(/not a core statement/);
    expect(() => buildCore(core(), { review })).not.toThrow(CoreGraphInputError);
  });
});

// ---------------------------------------------------------------------------------------------
// Fuzz
// ---------------------------------------------------------------------------------------------

function rng(seed: number): () => number {
  let s = seed >>> 0;
  return () => {
    s = (s + 0x6d2b79f5) >>> 0;
    let t = s;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function randomCore(r: () => number): Core {
  const nA = 1 + Math.floor(r() * 4);
  const nD = Math.floor(r() * 3);
  const nS = 2 + Math.floor(r() * 6);
  const assumptions = Array.from({ length: nA }, (_, i) => ({ id: `ass:a${i}`, condition: `c${i}`, novel: { flag: true, justification: "j" } }));
  const definitions = Array.from({ length: nD }, (_, i) => ({ id: `def:d${i}`, name: `d${i}`, construction: `k${i}` }));
  const statements: Array<Record<string, unknown>> = [];
  for (let i = 0; i < nS; i += 1) {
    const deps = new Set<string>();
    for (const a of assumptions) if (r() < 0.4) deps.add(a.id);
    for (const d of definitions) if (r() < 0.3) deps.add(d.id);
    for (let j = 0; j < i; j += 1) if (r() < 0.35) deps.add(`lem:s${j}`); // a DAG: only earlier statements
    const printed = [...deps].filter((d) => d.startsWith("ass:") && r() < 0.6);
    statements.push({
      id: `lem:s${i}`,
      kind: "lemma",
      statement: `claim ${i}${printed.length > 0 ? ` [Hypotheses: ${printed.join(", ")}]` : ""}`,
      depends_on: [...deps],
      status: "to-prove",
      ...(r() < 0.7 ? { proof_tex: `proof ${i}` } : {}),
    });
  }
  return { qid: "verify_fuzz", symbols: [], assumptions, definitions, statements, target_estimand: "t" } as unknown as Core;
}

function randomPatchFile(r: () => number, c: Core): PatchFileLike {
  const sids = c.statements.map((s) => s.id);
  const nonS = [...c.assumptions.map((a) => a.id), ...c.definitions.map((d) => d.id)];
  const pick = <T>(xs: T[]): T => xs[Math.floor(r() * xs.length)]!;
  const key = [pick(sids)];
  const patched = new Set<string>();
  const patches: PatchFileLike["patches"] = [];
  const nP = Math.floor(r() * 4);
  for (let i = 0; i < nP; i += 1) {
    const node = r() < 0.8 ? pick(sids) : pick(nonS.length > 0 ? nonS : sids);
    if (patched.has(node)) continue;
    patched.add(node);
    const st = c.statements.find((s) => s.id === node);
    const supersedes = st ? st.depends_on.filter((d) => !d.startsWith("lem:") && r() < 0.3) : [];
    patches.push({
      node,
      corrected_statement: r() < 0.5 ? `corrected ${node}` : null,
      ...(supersedes.length > 0 ? { supersedes } : {}),
      proof_note: "note",
    });
  }
  const unfixable: PatchFileLike["unfixable"] = [];
  if (r() < 0.4) {
    const cand = [...sids, ...nonS].filter((id) => !patched.has(id) && !key.includes(id));
    if (cand.length > 0) unfixable.push({ node: pick(cand), reason: "cannot" });
  }
  return { key_results: key, patches, unfixable };
}

function randomReview(r: () => number, c: Core): V15Review {
  const nodes = [...c.statements, ...c.assumptions, ...c.definitions].map((n) => {
    const isS = n.id.startsWith("lem:");
    const over: Partial<V15NodeVerdict> = {};
    if (isS && r() < 0.25) {
      over.correctness = "bookkeeping";
      over.bookkeeping_assumption = { condition: "regular", reason: "step" };
    }
    if (r() < 0.2) {
      over.ambiguity = "pinned";
      over.reading = { reading: "read", evidence: "ev" };
    }
    return verdict(n.id, over);
  });
  return { verdict: "PASS", summary: "", nodes };
}

describe("fuzz: every build satisfies the invariant", () => {
  it("random cores × random patch files × random reviews", () => {
    const r = rng(20260923);
    for (let iter = 0; iter < 400; iter += 1) {
      const c = randomCore(r);
      const before = JSON.stringify(c);
      const pf = randomPatchFile(r, c);
      // the referee grades the PATCHED core (that is what V1.5 is handed), so the review names
      // its nodes, never a descoped one
      const review = randomReview(r, buildCore(c, { patches: pf }).core);
      let out: ReturnType<typeof buildCore>;
      try {
        out = buildCore(c, { patches: pf, review });
      } catch (err) {
        throw new Error(`iteration ${iter}: ${err instanceof Error ? err.message : String(err)}\ncore=${before}\npatches=${JSON.stringify(pf)}`);
      }
      const ctx = `iteration ${iter}`;
      expect(checkCoreInvariants(out.core), ctx).toEqual([]);
      expect(JSON.stringify(c), ctx).toBe(before); // the input is untouched
      // key results survive; descoped statements are gone; unfixable nodes are gone
      for (const k of pf.key_results) expect(out.core.statements.some((s) => s.id === k), ctx).toBe(true);
      for (const d of out.descoped.keys()) expect(out.core.statements.some((s) => s.id === d), ctx).toBe(false);
      for (const u of pf.unfixable) expect([...out.core.statements, ...out.core.assumptions, ...out.core.definitions].some((n) => n.id === u.node), ctx).toBe(false);
      // every surviving patched statement carries its corrected text and its proof change
      for (const p of pf.patches) {
        const a = out.core.assumptions.find((x) => x.id === p.node);
        const d = out.core.definitions.find((x) => x.id === p.node);
        if (p.corrected_statement && a) expect(a.condition, ctx).toBe(p.corrected_statement);
        if (p.corrected_statement && d) expect(d.construction, ctx).toBe(p.corrected_statement);
        const s = out.core.statements.find((x) => x.id === p.node);
        if (!s) continue;
        if (p.corrected_statement) expect(s.statement.startsWith(p.corrected_statement), ctx).toBe(true);
        expect(s.proof_tex ?? "", ctx).toContain(p.proof_note);
        for (const rm of p.supersedes ?? []) expect(s.depends_on, ctx).not.toContain(rm);
      }
      // a review addition is wired into the statement(s) it was compiled for; a pin on an
      // assumption / definition no statement uses stays in the core unwired
      for (const a of out.added) {
        const node = out.core.assumptions.find((x) => x.id === a.id)!;
        expect(node.bookkeeping?.added_by, ctx).toBe("V1.5");
        const reason = node.bookkeeping?.reason ?? "";
        const site = reason.startsWith(PIN_REASON_PREFIX) ? reason.slice(PIN_REASON_PREFIX.length).split(": ")[0]! : a.node;
        const users = out.core.statements.filter((s) => s.id === site || s.depends_on.includes(site));
        expect((node.used_by ?? []).length > 0, ctx).toBe(users.length > 0);
      }
      // compilation is deterministic
      const again = compilePatchEdits(c, pf);
      expect(JSON.stringify(again.edits), ctx).toBe(JSON.stringify(compilePatchEdits(c, pf).edits));
    }
  });
});

describe("remapNodeIds — two ledger entries meeting on one node", () => {
  it("a witnessed error wins over an ambiguity, whichever is the carrier's; otherwise the carrier's wins", async () => {
    const { remapNodeIds } = await import("../../src/verify/core_graph.js");
    const error = { detail: "false", witness: "w" };
    const open = { detail: "vague", witness: null, undetermined: true };
    for (const ledger of [{ X: error, Y: open }, { Y: open, X: error }]) {
      const state = { paper_errors: { ...ledger } };
      remapNodeIds({ X: "Y" }, null, state as never);
      expect(state.paper_errors).toEqual({ Y: error });
    }
    const carried = { paper_errors: { X: open, Y: error } };
    remapNodeIds({ X: "Y" }, null, carried as never);
    expect(carried.paper_errors).toEqual({ Y: error });
    const both = { paper_errors: { X: { detail: "moved", witness: "a" }, Y: { detail: "carrier", witness: "b" } } };
    remapNodeIds({ X: "Y" }, null, both as never);
    expect(both.paper_errors).toEqual({ Y: { detail: "carrier", witness: "b" } });
  });
});
