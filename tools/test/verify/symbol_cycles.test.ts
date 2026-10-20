// A symbol table whose `refs` form a cycle (two symbols described through each other) is a table like
// any other for every reader of `refs`: each terminates, and what a verdict rests on is the same
// whatever order the table lists the symbols in.
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { orderSymbolsByRefs } from "../../src/core/symbol_order.js";
import { basisInputs, basisInputsV4, basisOf, symbolSourceHash } from "../../src/verify/core_graph.js";
import { symbolShownBasis, symbolsUsedBy } from "../../src/verify/referee_shard_prompts.js";
import { groupSymbolShards } from "../../src/verify/referee_symbols.js";

const SYMBOLS = [
  { name: "L", type: "constant", def: "The Lipschitz constant of $g$.", refs: ["g"] },
  { name: "g", type: "function", def: "The $L$-Lipschitz link.", refs: ["L"] },
  { name: "N", type: "count", def: "The number of observations $X_i$.", refs: ["X_i"] },
  { name: "i", type: "index", def: "An index in $1,\\dots,N$.", refs: ["N"] },
  { name: "X_i", type: "observation", def: "The observation of unit $i$.", refs: ["i"] },
  { name: "\\kappa", type: "constant", def: "A constant.", refs: [] },
] as Core["symbols"];

function core(symbols: Core["symbols"]): Core {
  return {
    qid: "cycles",
    symbols,
    assumptions: [{ id: "ass:lip", condition: "the link $g$ is Lipschitz", novel: { flag: true, justification: "Assumption 1" } }],
    definitions: [],
    statements: [
      { id: "lem:rate", kind: "lemma", statement: "the mean of the $X_i$ converges", depends_on: [], free_symbols: ["X_i"], status: "to-prove" },
      { id: "thm:main", kind: "theorem", statement: "the error is at most $L$", depends_on: ["ass:lip", "lem:rate"], free_symbols: ["L"], status: "to-prove" },
    ],
    target_estimand: "t",
    bibliography: [],
  } as unknown as Core;
}

const ORDERS: Array<Core["symbols"]> = [SYMBOLS, [...SYMBOLS].reverse(), orderSymbolsByRefs(SYMBOLS), [SYMBOLS[4]!, SYMBOLS[1]!, SYMBOLS[5]!, SYMBOLS[3]!, SYMBOLS[0]!, SYMBOLS[2]!]];

describe("a cycle of symbol refs", () => {
  it("symbolsUsedBy closes over the cycle once, the same in every table order", () => {
    for (const t of ORDERS) {
      expect([...symbolsUsedBy(core(t), ["thm:main"])].sort()).toEqual(["L", "g"]);
      expect([...symbolsUsedBy(core(t), ["lem:rate"])].sort()).toEqual(["N", "X_i", "i"]);
    }
  });

  it("a node's verdict basis (scheme 5 and scheme 4) does not depend on the order of the table", () => {
    for (const id of ["thm:main", "lem:rate", "ass:lip"]) {
      const bases = ORDERS.map((t) => basisOf(basisInputs(core(t), id)));
      expect(new Set(bases).size).toBe(1);
      expect(new Set(ORDERS.map((t) => basisOf(basisInputsV4(core(t), id)))).size).toBe(1);
    }
    expect(Object.keys(basisInputs(core(SYMBOLS), "thm:main").symbols).sort()).toEqual(["L", "N", "X_i", "g", "i"]);
  });

  it("a symbol's own hashes read its entry, not its place in the table", () => {
    for (const s of SYMBOLS) {
      expect(new Set(ORDERS.map((t) => symbolSourceHash(t.find((x) => x.name === s.name)!))).size).toBe(1);
      expect(new Set(ORDERS.map((t) => symbolShownBasis({ core: core(t), slices: new Map() }, s.name))).size).toBe(1);
    }
    expect(JSON.parse(symbolShownBasis({ core: core(SYMBOLS), slices: new Map() }, "L")).refs.map((r: { name: string }) => r.name)).toEqual(["g"]);
  });

  it("the symbol shards hold every symbol to grade exactly once", () => {
    for (const t of ORDERS) {
      for (const max of [2, 6]) {
        const shards = groupSymbolShards(t, t.map((x) => x.name), max);
        expect(shards.flat().sort()).toEqual(SYMBOLS.map((x) => x.name).sort());
      }
    }
  });
});
