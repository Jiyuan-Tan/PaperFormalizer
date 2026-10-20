// The order of the symbol table is the runner's: `orderSymbolsByRefs` puts each symbol after those
// its `refs` name, a cycle of `refs` is no defect (G1 accepts it), and every reader of `refs`
// terminates on one and reads the same whatever the order of the table.
import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { runStructuralGate } from "../../src/core/gate.js";
import type { Core } from "../../src/core/schema.js";
import { orderSymbolsByRefs, symbolRefsReach } from "../../src/core/symbol_order.js";

const sym = (name: string, refs: string[] = []) => ({ name, type: "t", refs });
const names = (xs: ReadonlyArray<{ name: string }>): string[] => xs.map((x) => x.name);

/** Symbols described through each other (a constant of a function and the function by its constant;
 * a count, its index and its observations), with one acyclic chain out of order around them. */
const CYCLIC = [sym("y", ["d"]), sym("L", ["g"]), sym("g", ["L"]), sym("N", ["X_i"]), sym("free"), sym("i", ["N"]), sym("X_i", ["i"]), sym("d"), sym("top", ["N", "y"])];

describe("orderSymbolsByRefs", () => {
  it("is the identity on a table already in order, and keeps the transcriber's order among independent symbols", () => {
    const sorted = [sym("b"), sym("a"), sym("c", ["a", "b"]), sym("z"), sym("d", ["c"])];
    expect(orderSymbolsByRefs(sorted)).toEqual(sorted);
    expect(names(orderSymbolsByRefs([sym("c", ["a"]), sym("z"), sym("a"), sym("b", ["c"])]))).toEqual(["a", "c", "z", "b"]);
  });

  it("orders a chain listed backwards", () => {
    expect(names(orderSymbolsByRefs([sym("c", ["b"]), sym("b", ["a"]), sym("a")]))).toEqual(["a", "b", "c"]);
  });

  it("keeps a cycle together in the transcriber's order, after what it refers to; a second pass moves nothing", () => {
    const once = orderSymbolsByRefs(CYCLIC);
    expect(names(once)).toEqual(["d", "y", "L", "g", "N", "i", "X_i", "free", "top"]);
    expect(orderSymbolsByRefs(once)).toEqual(once);
    expect([...once].sort((a, b) => a.name.localeCompare(b.name))).toEqual([...CYCLIC].sort((a, b) => a.name.localeCompare(b.name)));
  });

  it("a ref to the symbol itself or to no symbol of the table orders nothing", () => {
    const t = [sym("a", ["a", "ghost"]), sym("b", ["a"])];
    expect(orderSymbolsByRefs(t)).toEqual(t);
  });

  it("reach: a symbol reaches itself exactly on a cycle", () => {
    const reach = symbolRefsReach(CYCLIC);
    expect([...reach.get("N")!].sort()).toEqual(["N", "X_i", "i"]);
    expect([...reach.get("top")!].sort()).toEqual(["N", "X_i", "d", "i", "y"]);
    expect(reach.get("y")!.has("y")).toBe(false);
  });
});

describe("G1 on the symbol table", () => {
  const core = (symbols: unknown[]): Core => {
    const c = JSON.parse(readFileSync(new URL("../fixtures/stat_ate_overlap_decay_core.json", import.meta.url), "utf8")) as Core;
    c.symbols = [...c.symbols, ...(symbols as Core["symbols"])];
    return c;
  };
  const g1 = (symbols: unknown[]): string[] =>
    runStructuralGate(core(symbols), { requireDischarged: true }).violations.filter((v) => v.where.startsWith("symbol:")).map((v) => `${v.where}: ${v.message}`);

  it("accepts symbols that refer to each other in a cycle, in any order", () => {
    expect(g1(CYCLIC.filter((s) => ["L", "g", "N", "i", "X_i"].includes(s.name)))).toEqual([]);
    expect(g1(orderSymbolsByRefs(CYCLIC))).toEqual([]);
    expect(g1([sym("s", ["s"])])).toEqual([]);
  });

  it("still refuses a use before its definition that an order would satisfy — the order V1 gives the table", () => {
    expect(g1(CYCLIC)).toEqual(["symbol:y: references symbol 'd' before it is defined"]);
  });

  it("refuses a ref that names no symbol of the table", () => {
    expect(g1([sym("a"), sym("b", ["a", "ghost"])])).toEqual([
      "symbol:b: refs names 'ghost', which is no symbol of the table; `refs` lists symbol names only (add the symbol, or drop the name)",
    ]);
  });
});
