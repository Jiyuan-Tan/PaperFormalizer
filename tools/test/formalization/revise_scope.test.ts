// The affected set of a revise: the seeds and what must move with them — and what it leaves out.

import { describe, expect, it } from "vitest";
import { SCOPED_SYMBOLS_NOTE, formalizationCoreContextValue } from "../../src/formalization/core_context.js";
import type { Core } from "../../src/core/schema.js";
import type { Plan } from "../../src/formalization/plan/schema.js";
import {
  beyondScopeReported,
  coreChangeSeeds,
  namedNodeIds,
  nodeNeighbours,
  nodeReferenceIndex,
  planChangeSeeds,
  referencedNodeIds,
  reviseAffectedNodeIds,
  reviseLookupBlock,
} from "../../src/formalization/revise_scope.js";

const novel = { flag: true, justification: "stated" };

function core(): Core {
  return {
    qid: "q",
    symbols: [{ name: "Y", type: "outcome", def: "the outcome", ref: "def:est" }, { name: "h", type: "bandwidth", scoped: [{ results: ["lem:far"], text: "h is small" }] }],
    assumptions: [
      { id: "ass:a", condition: "a", free_symbols: [], novel },
      { id: "ass:member", condition: "m", free_symbols: [], novel },
      { id: "ass:alone", condition: "z", free_symbols: [], novel },
      { id: "ass:pin-1", condition: "the rate is uniform", free_symbols: [], bookkeeping: { flag: true, added_by: "V1.5", reason: "pins reading of def:est: the paper says so" } },
    ],
    definitions: [
      { id: "def:class", name: "C", construction: "c", by_member_properties: ["ass:member"] },
      { id: "def:est", name: "E", construction: "e", inputs: ["ass:a"] },
    ],
    statements: [
      { id: "thm:main", kind: "theorem", statement: "main", depends_on: ["ass:a", "def:class", "lem:gate"], status: "to-prove" },
      { id: "lem:uses-main", kind: "lemma", statement: "u", depends_on: ["thm:main"], status: "to-prove" },
      { id: "lem:gate", kind: "lemma", statement: "g", depends_on: [], status: "to-prove" },
      { id: "lem:pinned", kind: "lemma", statement: "p", depends_on: ["ass:pin-1"], status: "to-prove" },
      { id: "thm:b1", kind: "theorem", statement: "b1", depends_on: [], status: "to-prove", split_from: "thm:main" },
      { id: "thm:b2", kind: "theorem", statement: "b2", depends_on: [], status: "to-prove", split_from: "thm:main" },
      { id: "thm:c1", kind: "theorem", statement: "c1", depends_on: [], status: "to-prove", split_from: "thm:umbrella-gone" },
      { id: "thm:c2", kind: "theorem", statement: "c2", depends_on: [], status: "to-prove", split_from: "thm:umbrella-gone" },
      { id: "lem:far", kind: "lemma", statement: "f", depends_on: ["ass:alone"], status: "to-prove" },
    ],
    target_estimand: "t",
    bibliography: [],
  } as unknown as Core;
}

const entry = (lean_kind: string, lean_name: string, extra: Record<string, unknown> = {}) => ({ lean_kind, lean_name, disposition: "define-local", reuse: null, modules: [], ...extra });

function plan(): Plan {
  return {
    qid: "q",
    env: [],
    citations: [],
    nodes: {
      "ass:a": entry("assumption", "A"),
      "ass:member": entry("assumption", "M"),
      "def:class": entry("structure", "C", { members: ["ass:member"] }),
      "thm:main": entry("theorem", "main", { hyps: ["ass:a", "def:class", "lem:gate"], target_file: "TMain.lean" }),
      "lem:gate": entry("assumption", "Gate", { gate: true }),
      "lem:far": entry("lemma", "far", { hyps: ["ass:alone"] }),
    },
  } as unknown as Plan;
}

const affected = (seeds: string[], withPlan = true): string[] => [...reviseAffectedNodeIds(core(), withPlan ? plan() : null, seeds)].sort();

describe("reviseAffectedNodeIds", () => {
  it("a changed assumption reaches the statements and constructions citing it — not the lemmas using those", () => {
    expect(affected(["ass:a"])).toEqual(["ass:a", "def:est", "thm:b1", "thm:b2", "thm:main"]);
    expect(affected(["ass:a"])).not.toContain("lem:uses-main");
  });

  it("a changed member reaches its class, and through the class the statements taking it", () => {
    expect(affected(["ass:member"])).toEqual(["ass:member", "def:class", "thm:b1", "thm:b2", "thm:main"]);
  });

  it("a changed ordinary statement moves alone with its split blocks; a statement the plan threads as a hypothesis moves its consumers", () => {
    expect(affected(["lem:uses-main"])).toEqual(["lem:uses-main"]);
    expect(affected(["lem:gate"])).toEqual(["lem:gate", "thm:b1", "thm:b2", "thm:main"]);
    // without a plan the gate is an ordinary statement: an under-reach the lookup duty covers
    expect(affected(["lem:gate"], false)).toEqual(["lem:gate"]);
  });

  it("a changed pinned reading reaches the results it is wired into and the node it is a reading of — not that node's other users", () => {
    expect(affected(["ass:pin-1"])).toEqual(["ass:pin-1", "def:est", "lem:pinned"]);
  });

  it("a block moves with its parent and its sibling blocks, also when the parent is an umbrella the F stages do not see", () => {
    expect(affected(["thm:b1"])).toEqual(["thm:b1", "thm:b2", "thm:main"]);
    expect(affected(["thm:c1"])).toEqual(["thm:c1", "thm:c2"]);
    expect(affected(["thm:main"])).toEqual(["thm:b1", "thm:b2", "thm:main"]);
  });

  it("a flagged node is carried alone, with the subject of a flagged pinned reading — its users and sibling blocks stay out", () => {
    const flagged = (ids: string[], seeds: string[] = []): string[] => [...reviseAffectedNodeIds(core(), plan(), seeds, ids)].sort();
    expect(flagged(["ass:a"])).toEqual(["ass:a"]);
    expect(flagged(["thm:b1"])).toEqual(["thm:b1"]);
    expect(flagged(["ass:pin-1"])).toEqual(["ass:pin-1", "def:est"]);
    expect(flagged(["lem:far", "nope:x"], ["ass:member"])).toEqual(["ass:member", "def:class", "lem:far", "thm:b1", "thm:b2", "thm:main"]);
  });

  it("the neighbours of a set are what its nodes rest on and what uses them, one hop", () => {
    expect([...nodeNeighbours(core(), plan(), new Set(["thm:main"]))].sort()).toEqual(["ass:a", "def:class", "lem:gate", "lem:uses-main", "thm:b1", "thm:b2"]);
    expect([...nodeNeighbours(core(), plan(), new Set(["ass:member"]))]).toEqual(["def:class"]);
    expect(nodeNeighbours(core(), plan(), new Set()).size).toBe(0);
  });

  it("leaves an unrelated node out, drops an id that is no core node, and is empty for no seed", () => {
    expect(affected(["ass:a", "ass:member", "ass:pin-1", "thm:c1"])).not.toContain("lem:far");
    expect(affected(["ass:a"])).not.toContain("ass:alone");
    expect(affected(["thm:gone", "S1"])).toEqual([]);
    expect(affected([])).toEqual([]);
  });
});

describe("the seeds of a change", () => {
  it("the F stages are told how a symbol's scoped clauses read", () => {
    expect(SCOPED_SYMBOLS_NOTE).toContain("`scoped` entries `{results, text}`");
  });

  it("names the nodes a text cites, known ones only", () => {
    expect(namedNodeIds(core(), ["re-plan thm:main (and thm:unknown)", null, "see ass:a."])).toEqual(["thm:main", "ass:a"]);
  });

  it("a core change seeds every added or changed node (locators apart), a changed symbol's definition and the results of a new scoped clause", () => {
    const cur = core() as unknown as { symbols: Array<Record<string, unknown>>; assumptions: Array<Record<string, unknown>>; statements: Array<Record<string, unknown>> };
    cur.assumptions[2]!.tex_locator = "L12"; // quiet
    cur.assumptions[0]!.condition = "a, strictly";
    cur.statements.push({ id: "lem:new", kind: "lemma", statement: "n", depends_on: [], status: "to-prove" });
    cur.symbols[0]!.def = "the observed outcome";
    cur.symbols[1]!.scoped = [{ results: ["lem:far"], text: "h is small" }, { results: ["lem:pinned"], text: "h is fixed" }];
    const seeds = coreChangeSeeds(core(), cur);
    expect(seeds.nodes.sort()).toEqual(["ass:a", "def:est", "lem:new", "lem:pinned"]);
    expect(seeds.symbols).toEqual(["Y", "h"]);
    expect(coreChangeSeeds(core(), core())).toEqual({ nodes: [], symbols: [] });
    // a clause that is gone seeds its results too, and the F stages' core view carries the clauses
    expect(coreChangeSeeds(cur, { ...cur, symbols: cur.symbols.map((s, i) => (i === 1 ? { ...s, scoped: [{ results: ["lem:pinned"], text: "h is fixed" }] } : s)) }).nodes).toEqual(["lem:far"]);
    const view = formalizationCoreContextValue(cur as unknown as Core) as { symbols: Array<{ name: string; scoped?: unknown }> };
    expect(view.symbols.find((s) => s.name === "h")!.scoped).toEqual([{ results: ["lem:far"], text: "h is small" }, { results: ["lem:pinned"], text: "h is fixed" }]);
  });

  it("a plan change seeds the entries that differ — one whose `notes` alone were rewritten too", () => {
    const cur = plan() as unknown as { nodes: Record<string, Record<string, unknown>>; env: unknown[]; citations: unknown[] };
    cur.nodes["thm:main"]!.notes = "rewritten";
    cur.nodes["lem:far"]!.lean_name = "farther";
    cur.nodes["lem:new"] = entry("lemma", "fresh");
    cur.env = [{ id: "S1", world: "w" }];
    expect(planChangeSeeds(plan(), cur)).toEqual({ nodes: ["thm:main", "lem:far", "lem:new"], envs: ["S1"], other: false });
    const notesOnly = plan() as unknown as { nodes: Record<string, Record<string, unknown>> };
    notesOnly.nodes["thm:main"]!.notes = "the conclusion is stated per fold";
    expect(planChangeSeeds(plan(), notesOnly).nodes).toEqual(["thm:main"]);
    cur.citations = [{ id: "cite:x" }];
    expect(planChangeSeeds(plan(), cur).other).toBe(true);
  });
});

describe("what a scoped revise prompt says of the rest", () => {
  it("gives one reference line per node not shown, with its plan name, and marks an unplanned node", () => {
    const index = nodeReferenceIndex(core(), plan(), new Set(["ass:a", "thm:main"]));
    expect(index).toContain("def:class | class | structure C");
    expect(index).toContain("lem:far | lemma | lemma far");
    expect(index).toContain("ass:alone | assumption | no plan entry");
    expect(index.some((l) => l.startsWith("ass:a |") || l.startsWith("thm:main |"))).toBe(false);
    expect(index).toHaveLength(15 - 2);
    expect(nodeReferenceIndex(core(), plan(), new Set()).find((l) => l.startsWith("thm:main"))).toBe("thm:main | theorem | theorem main | TMain.lean");
  });

  it("names both files, the lookup by id, the duty to trace and to report", () => {
    const block = reviseLookupBlock({ index: ["x | assumption | assumption X"], shown: 3, total: 4, corePath: "/run/core.json", planPath: "/run/plan.json", replyField: "`looked_up_beyond_scope`" });
    expect(block).toContain("EVERY OTHER NODE (1 of 4");
    expect(block).toContain("typed core (READ-ONLY): /run/core.json");
    expect(block).toContain("plan: /run/plan.json");
    expect(block).toContain("never read either file whole");
    expect(block).toContain("UNDER-REACH");
    expect(block).toContain("list every node you had to look up in `looked_up_beyond_scope`");
  });

  it("a result the paper labels carries its label on its line, so a `\\ref` in a text can be resolved", () => {
    const labelled = core();
    (labelled.statements[8] as { tex_locator?: unknown }).tex_locator = { file: "a.tex", from: 1, to: 2, env: "lemma", label: "lemma:far" };
    expect(nodeReferenceIndex(labelled, plan(), new Set()).find((l) => l.startsWith("lem:far"))).toBe("lem:far | lemma | lemma far | \\ref{lemma:far}");
  });

  it("names the nodes a carried text cites by label or by id — a mention no graph edge records", () => {
    const c = core();
    (c.statements[8] as { tex_locator?: unknown }).tex_locator = { file: "a.tex", from: 1, to: 2, env: "lemma", label: "lemma:far" };
    (c.assumptions[2] as { tex_locator?: unknown }).tex_locator = { file: "a.tex", from: 5, to: 6, env: "assumption", label: "assumption:alone" };
    c.assumptions[0]!.condition = "The conditions of Lemma~\\ref{lemma:far} and Assumption~\\ref{assumption:alone} hold, see \\ref{eq:none}.";
    expect([...referencedNodeIds(c, new Set(["ass:a"]))].sort()).toEqual(["ass:alone", "lem:far"]);
    // by id, in the reason of an added condition; a node already in the set is not named again
    expect([...referencedNodeIds(c, new Set(["ass:pin-1"]))]).toEqual(["def:est"]);
    expect([...referencedNodeIds(c, new Set(["ass:pin-1", "def:est"]))]).toEqual([]);
    expect([...referencedNodeIds(c, new Set(["ass:member"]))]).toEqual([]);
  });

  it("a neighbours block names the ids to read first in the index of every node", () => {
    const block = reviseLookupBlock({ index: ["ass:a", "lem:far"], neighboursOnly: true, shown: 2, total: 12, corePath: "/c.json", planPath: "/p.json", replyField: "`x`" });
    expect(block).toContain("=== NEIGHBOURS OF THE AFFECTED NODES (2 of the 10 nodes not shown in full) ===");
    expect(block).toContain("\nass:a, lem:far\n");
    expect(block).toContain("`Lemma~\\ref{<label>}`");
    expect(block).toContain("typed core (READ-ONLY): /c.json");
    expect(block).not.toContain("EVERY OTHER NODE");
  });

  it("reads the report back from a reply, as a field or in a review's prose", () => {
    expect(beyondScopeReported('{"status":"completed","looked_up_beyond_scope":["lem:far","ass:alone"]}')).toEqual(["lem:far", "ass:alone"]);
    expect(beyondScopeReported('{"status":"pass","notes":"sound. looked_up_beyond_scope: [def:class]"}')).toEqual(["def:class"]);
    expect(beyondScopeReported('{"status":"completed","looked_up_beyond_scope":[]}')).toEqual([]);
    expect(beyondScopeReported('{"status":"completed"}')).toEqual([]);
  });
});
