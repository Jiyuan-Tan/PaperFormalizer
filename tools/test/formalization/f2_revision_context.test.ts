import { describe, expect, it } from "vitest";
import { CoreSchema } from "../../src/core/schema.js";
import {
  buildF2RevisionContext,
  F2_REVISION_NOTES_HEADER,
  revisionNotesFromRedirect,
  scaffoldCoverageGaps,
  withReviewerFindings,
} from "../../src/formalization/f2_revision_context.js";
import { PlanSchema } from "../../src/formalization/plan/schema.js";

function fixture() {
  const core = CoreSchema.parse({
    qid: "local-context-test",
    symbols: [
      { name: "x", type: "real" },
      { name: "y", type: "real", refs: ["x"], ref: "def:derived" },
      { name: "z", type: "real" },
    ],
    assumptions: [
      {
        id: "ass:shared",
        condition: "x is positive",
        free_symbols: ["x"],
        standard: { name: "positivity", cite: "fixture" },
      },
      {
        id: "ass:unrelated",
        condition: "z is bounded",
        free_symbols: ["z"],
        standard: { name: "boundedness", cite: "fixture" },
      },
    ],
    definitions: [
      {
        id: "def:shared",
        name: "Shared",
        construction: "objects satisfying ass:shared",
        free_symbols: ["x"],
        by_member_properties: ["ass:shared"],
      },
      {
        id: "def:derived",
        name: "Derived",
        construction: "y computed from x",
        free_symbols: ["x", "y"],
        inputs: ["x"],
      },
    ],
    statements: [
      {
        id: "thm:target",
        kind: "theorem",
        statement: "target about x",
        free_symbols: ["x"],
        depends_on: ["def:shared"],
        route: "direct",
        status: "to-prove",
        proof_tex: "PROOF_SENTINEL",
        justification: "PROSE_SENTINEL",
      },
      {
        id: "lem:consumer",
        kind: "lemma",
        statement: "consumer of target",
        free_symbols: ["x"],
        depends_on: ["thm:target"],
        status: "to-prove",
      },
      {
        id: "lem:sibling",
        kind: "lemma",
        statement: "sibling using the same prerequisite",
        free_symbols: ["x"],
        depends_on: ["def:shared"],
        status: "to-prove",
      },
      {
        id: "lem:unrelated",
        kind: "lemma",
        statement: "unrelated z result",
        free_symbols: ["z"],
        depends_on: ["ass:unrelated"],
        status: "to-prove",
      },
    ],
    sampling_model: { observed: "x" },
    target_estimand: "x",
    bibliography: [],
  });
  const node = (lean_kind: string, lean_name: string, extra = {}) => ({
    lean_kind,
    lean_name,
    disposition: "define-local",
    reuse: null,
    modules: [],
    ...extra,
  });
  const plan = PlanSchema.parse({
    qid: core.qid,
    env: [
      { id: "S1", world: "x-world", binds_symbols: ["x"], binds_sampling_model: true, disposition: "define-local" },
      { id: "S2", world: "z-world", binds_symbols: ["z"], binds_sampling_model: false, disposition: "define-local" },
    ],
    nodes: {
      "ass:shared": node("assumption", "SharedAssumption"),
      "ass:unrelated": node("assumption", "UnrelatedAssumption"),
      "def:shared": node("structure", "Shared", { members: ["ass:shared"] }),
      "def:derived": node("def", "Derived"),
      "thm:target": node("theorem", "targetTheorem", { hyps: ["def:shared"] }),
      "lem:consumer": node("lemma", "consumerLemma", { hyps: ["thm:target"] }),
      "lem:sibling": node("lemma", "siblingLemma", { hyps: ["def:shared"] }),
      "lem:unrelated": node("lemma", "unrelatedLemma", { hyps: ["ass:unrelated"] }),
    },
    citations: [],
  });
  return { core, plan };
}

describe("F2 local revision context", () => {
  it("keeps the target and the consumers its change forces, a reference line for its prerequisites, and no sibling churn", () => {
    const { core, plan } = fixture();
    const packet = buildF2RevisionContext(core, plan, ["thm:target"]);
    expect(packet).not.toBeNull();
    const ids = Object.keys(packet!.plan.nodes as Record<string, unknown>);
    expect(ids).toEqual(["thm:target", "lem:consumer"]);
    expect(packet!.affected.sort()).toEqual(["lem:consumer", "thm:target"]);
    expect(packet!.index).toContain("def:shared | class | structure Shared");
    expect(packet!.index).toContain("ass:shared | assumption | assumption SharedAssumption");
    expect(packet!.index).toHaveLength(6);
    expect(ids).not.toContain("lem:sibling");
    expect(ids).not.toContain("lem:unrelated");
    expect(packet!.plan.env).toEqual([expect.objectContaining({ id: "S1" })]);
    expect(JSON.stringify(packet!.core)).not.toContain("PROOF_SENTINEL");
    expect(JSON.stringify(packet!.core)).not.toContain("PROSE_SENTINEL");
  });

  it("expands a shared symbol target to every declaration that uses that symbol", () => {
    const { core, plan } = fixture();
    const packet = buildF2RevisionContext(core, plan, ["sym:x"]);
    const ids = Object.keys(packet!.plan.nodes as Record<string, unknown>);
    expect(ids).toContain("lem:sibling");
    expect(ids).toContain("def:derived");
    expect(ids).not.toContain("lem:unrelated");
    expect(packet!.resolved_targets).toEqual(["sym:x"]);
    expect(packet!.core.symbols).toEqual(expect.arrayContaining([
      expect.objectContaining({ name: "x" }),
      expect.objectContaining({ name: "y" }),
    ]));
  });

  it("drops a target that names nothing, and keeps the whole context only when none resolves or the set is every node", () => {
    const { core, plan } = fixture();
    const packet = buildF2RevisionContext(core, plan, ["thm:target", "missing:node"]);
    expect(packet!.unresolved_targets).toEqual(["missing:node"]);
    expect(packet!.resolved_targets).toEqual(["thm:target"]);
    expect(buildF2RevisionContext(core, plan, ["missing:node"])).toBeNull();
    const all = [...core.assumptions, ...core.definitions, ...core.statements].map((n) => n.id);
    expect(buildF2RevisionContext(core, plan, all, { flagged: all })).toBeNull();
  });

  it("a flagged S-block is shown with the symbols it binds, their users unchanged; the other S-blocks are one line each", () => {
    const { core, plan } = fixture();
    const packet = buildF2RevisionContext(core, plan, ["thm:target", "S2"], { flagged: ["thm:target", "S2"] });
    expect(packet!.affected).toEqual(["thm:target"]);
    expect((packet!.plan.env as Array<{ id: string }>).map((e) => e.id)).toEqual(["S1", "S2"]);
    expect((packet!.core.symbols as Array<{ name: string }>).map((s) => s.name)).toEqual(["x", "z"]);
    const one = buildF2RevisionContext(core, plan, ["thm:target"], { flagged: ["thm:target"] });
    expect(one!.env_index).toEqual(["S2 | binds z | define-local"]);
    // a CHANGED S-block moves the users of what it binds
    expect(buildF2RevisionContext(core, plan, ["S2"])!.affected.sort()).toEqual(["ass:unrelated", "lem:unrelated"]);
  });

  it("a node without `free_symbols` uses the symbols its text writes — never the whole table", () => {
    const { core, plan } = fixture();
    // The users of a changed symbol are found by text where the list is absent: no whole-context fallback.
    delete core.statements[0].free_symbols;
    core.statements[0].statement = "target about $x$";
    const bySymbol = buildF2RevisionContext(core, plan, ["sym:x"]);
    expect(bySymbol).not.toBeNull();
    expect(bySymbol!.affected).toContain("thm:target");
    expect(bySymbol!.affected).not.toContain("lem:unrelated");
    // And the entries shown are those the affected nodes use.
    const packet = buildF2RevisionContext(core, plan, ["thm:target"], { flagged: ["thm:target"] });
    expect((packet!.core.symbols as Array<{ name: string }>).map((s) => s.name)).toEqual(["x"]);
    expect(packet!.omitted_counts.symbols).toBe(2);
  });

  it("a flagged target is carried alone — its users and prerequisites are neighbour lines", () => {
    const { core, plan } = fixture();
    const packet = buildF2RevisionContext(core, plan, ["ass:shared"], { flagged: ["ass:shared"] });
    expect(packet!.affected).toEqual(["ass:shared"]);
    expect(packet!.neighbours).toEqual(["def:shared"]);
    // a statement: what it rests on and what uses it, one hop
    const statement = buildF2RevisionContext(core, plan, ["thm:target"], { flagged: ["thm:target"] });
    expect(statement!.affected).toEqual(["thm:target"]);
    expect(statement!.neighbours.sort()).toEqual(["def:shared", "lem:consumer"]);
    // what the statement assumes is shown as text: the class it takes, and the class's member atom
    expect(statement!.core.hypothesis_texts).toEqual({ "def:shared": "Shared: objects satisfying ass:shared", "ass:shared": "x is positive" });
    expect(statement!.index).toHaveLength(7);
    // a flagged symbol: its entry and the definition it names, not its users
    const symbol = buildF2RevisionContext(core, plan, ["sym:y"], { flagged: ["sym:y"] });
    expect(symbol!.affected).toEqual(["def:derived"]);
    expect((symbol!.core.symbols as Array<{ name: string }>).map((s) => s.name).sort()).toEqual(["x", "y"]);
  });

  it("prints a reading several affected nodes share once, by id, and the settings that name an affected node", () => {
    const { core, plan } = fixture();
    const pinned = CoreSchema.parse({
      ...core,
      assumptions: [
        ...core.assumptions,
        { id: "ass:pin-1", condition: "SHARED_READING_SENTINEL", bookkeeping: { flag: true, added_by: "V1.5", reason: "pins reading of def:shared: the paper says so" } },
      ],
      statements: core.statements.map((s) => (s.id === "thm:target" || s.id === "lem:sibling" ? { ...s, depends_on: [...s.depends_on, "ass:pin-1"] } : s)),
      sampling_model: { population: "For thm:target the law is fixed.", sample: "For lem:unrelated the draws are iid.", SETTING_OF_NONE: "For lemma:other nothing is random." },
    });
    const packet = buildF2RevisionContext(pinned, plan, ["thm:target", "lem:sibling"], { flagged: ["thm:target", "lem:sibling"] });
    const text = JSON.stringify(packet!.core);
    expect(text.split("SHARED_READING_SENTINEL")).toHaveLength(2);
    expect(packet!.core.binding_readings).toEqual({ "ass:pin-1": "(reading of def:shared): SHARED_READING_SENTINEL" });
    for (const s of packet!.core.statements as Array<Record<string, unknown>>) expect(s.pinned_readings_binding).toEqual(["ass:pin-1"]);
    // lem:sibling is named by no setting: the settings cannot be cut, and all are shown
    expect(Object.keys(packet!.core.sampling_model as object)).toEqual(["population", "sample", "SETTING_OF_NONE"]);
    const one = buildF2RevisionContext(pinned, plan, ["thm:target"], { flagged: ["thm:target"] });
    expect(Object.keys(one!.core.sampling_model as object)).toEqual(["population"]);
    // an assumption is in the settings of the results using it
    const atom = buildF2RevisionContext(pinned, plan, ["ass:unrelated"], { flagged: ["ass:unrelated"] });
    expect(Object.keys(atom!.core.sampling_model as object)).toEqual(["sample"]);
  });

  it("a flagged condition that takes a lemma by reference is carried with that lemma, its hypotheses' texts and its readings", () => {
    const { core, plan } = fixture();
    const byRef = CoreSchema.parse({
      ...core,
      assumptions: [
        ...core.assumptions,
        { id: "ass:by-ref", condition: "The conditions of Lemma~\\ref{lemma:unrelated} hold.", free_symbols: [], standard: { name: "referenced", cite: "fixture" } },
        { id: "ass:pin-1", condition: "LIMITS_NOT_ENDPOINTS_SENTINEL", bookkeeping: { flag: true, added_by: "V1.5", reason: "pins reading of ass:unrelated: the paper says so" } },
      ],
      statements: core.statements.map((s) => (s.id === "lem:unrelated" ? { ...s, depends_on: [...s.depends_on, "ass:pin-1"], tex_locator: { file: "a.tex", from: 1, to: 2, env: "lemma", label: "lemma:unrelated" } } : s)),
    });
    const packet = buildF2RevisionContext(byRef, plan, ["ass:by-ref"], { flagged: ["ass:by-ref"] })!;
    expect(packet.affected).toEqual(["ass:by-ref"]);
    expect(packet.context).toEqual(["lem:unrelated"]);
    expect((packet.core.statements as Array<{ id: string }>).map((s) => s.id)).toEqual(["lem:unrelated"]);
    expect(Object.keys(packet.plan.nodes as object)).toContain("lem:unrelated");
    expect(packet.core.hypothesis_texts).toEqual({ "ass:unrelated": "z is bounded" });
    expect(packet.core.binding_readings).toEqual({ "ass:pin-1": "(reading of ass:unrelated): LIMITS_NOT_ENDPOINTS_SENTINEL" });
    expect(packet.index.some((l) => l.startsWith("lem:unrelated"))).toBe(false);
  });

  it("reads a redirect's per-target findings back, and puts each on the record of its node", () => {
    const redirect = [
      "The reviewer's summary.",
      F2_REVISION_NOTES_HEADER,
      "• thm:target: drops the premise",
      "  on a second line",
      "• ass:shared",
      "• sym:x: carries no tag",
      "",
      "Declarations to edit (one obj_id per line, verbatim):",
      "- thm:target",
      "- ass:shared",
    ].join("\n");
    const read = revisionNotesFromRedirect(redirect);
    expect(read.notes).toEqual({ "thm:target": "drops the premise\n  on a second line", "sym:x": "carries no tag" });
    expect(read.rest).toBe("The reviewer's summary.\nDeclarations to edit (one obj_id per line, verbatim):\n- thm:target\n- ass:shared");
    expect(revisionNotesFromRedirect("a hand-written directive")).toEqual({ notes: {}, rest: "a hand-written directive" });
    const { core, plan } = fixture();
    const packet = buildF2RevisionContext(core, plan, ["thm:target", "sym:x"], { flagged: ["thm:target", "sym:x"] })!;
    const found = withReviewerFindings(packet.core, read.notes);
    expect(found.attached.sort()).toEqual(["sym:x", "thm:target"]);
    expect(Object.entries((found.core.statements as Array<Record<string, unknown>>)[0]!).slice(0, 2)).toEqual([["id", "thm:target"], ["reviewer_finding", "drops the premise\n  on a second line"]]);
    expect((found.core.symbols as Array<Record<string, unknown>>).find((s) => s.name === "x")!.reviewer_finding).toBe("carries no tag");
  });

  it("a changed atom carries its class and the statements taking it; a symbol shown for context changes no node", () => {
    const { core, plan } = fixture();
    const packet = buildF2RevisionContext(core, plan, ["ass:shared"], { contextSymbols: ["z"] });
    expect(Object.keys(packet!.plan.nodes as Record<string, unknown>).sort()).toEqual(["ass:shared", "def:shared", "lem:consumer", "lem:sibling", "thm:target"]);
    expect((packet!.core.symbols as Array<{ name: string }>).map((s) => s.name)).toContain("z");
    expect(packet!.affected).not.toContain("lem:unrelated");
  });

  it("names every gap in a scaffold's coverage, so a revise can carry them as targets", () => {
    const { plan } = fixture();
    const tags = { nodes: new Set(Object.keys(plan.nodes)), envs: new Set(["S1"]) };
    tags.nodes.delete("lem:unrelated");
    expect(scaffoldCoverageGaps(plan, tags)).toEqual(["lem:unrelated", "S2"]);
  });

});

describe("F2 local revision context — plan notes", () => {
  it("keeps the carried plan records' `notes`: the statement shape and the encoding decisions F1 recorded for F2", () => {
    const { core, plan } = fixture();
    const noted = PlanSchema.parse({
      ...plan,
      env: plan.env.map((e) => ({ ...e, notes: "ENV_NOTE_SENTINEL" })),
      nodes: Object.fromEntries(Object.entries(plan.nodes).map(([id, n]) => [id, { ...n, notes: `NOTE_OF ${id}` }])),
    });
    const packet = buildF2RevisionContext(core, noted, ["thm:target"])!;
    const nodes = packet.plan.nodes as Record<string, { lean_name: string; notes?: string }>;
    expect(nodes["thm:target"].notes).toBe("NOTE_OF thm:target");
    expect(nodes["thm:target"].lean_name).toBe("targetTheorem");
    // only the carried records are shown, so only their notes travel
    const omitted = Object.keys(plan.nodes).filter((id) => !(id in nodes));
    for (const id of omitted) expect(JSON.stringify(packet.plan)).not.toContain(`NOTE_OF ${id}"`);
  });
});
