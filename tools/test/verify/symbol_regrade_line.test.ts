/**
 * The symbol pass says why each symbol it grades afresh was not carried: which parts of its basis
 * moved (`basis_parts`, recorded with every verdict), a symbol new to the table, a verdict graded
 * before parts were recorded. One line, counts per part, largest first.
 */
import { describe, expect, it } from "vitest";
import type { Core, CoreSymbol } from "../../src/core/schema.js";
import { symbolBasis, symbolBasisParts, symbolRegradeLine } from "../../src/verify/referee_symbols.js";
import { settingsNaming, symbolShownBasis, symbolShownParts } from "../../src/verify/referee_shard_prompts.js";

const sym = (over: Partial<CoreSymbol> = {}): CoreSymbol => ({ name: "k", type: "integer", space: "$\\mathbb{N}$", def: "the number of clusters", refs: [], ...over }) as CoreSymbol;
const shown = (over: Record<string, unknown> = {}) => ({ entry: { name: "k" }, refs: [], settings: { s: "iid" }, listing: ["thm:a"], redefinitions: [], uses: [["thm:a", "k clusters"]], ...over });

describe("symbolBasisParts", () => {
  it("one hash per part; a part that moves changes its hash alone", () => {
    const a = symbolBasisParts(sym(), "Let $k$ be the number of clusters.", [], shown());
    expect(Object.keys(a).sort()).toEqual(["corrected", "entry", "intro", "listing", "redefinitions", "refs", "settings", "source", "uses"]);
    const b = symbolBasisParts(sym(), "Let $k$ be the number of clusters.", [], shown({ settings: { s: "iid, n large" } }));
    expect(Object.entries(b).filter(([k, h]) => a[k] !== h).map(([k]) => k)).toEqual(["settings"]);
    // (the entry as shown is the caller's: here a fixed one, so only the source hash moves)
    const c = symbolBasisParts(sym({ def: "the number of centres" }), "Let $k$ be the number of clusters.", [], shown());
    expect(Object.entries(c).filter(([k, h]) => a[k] !== h).map(([k]) => k)).toEqual(["source"]);
  });

  it("the parts move exactly when the basis moves (a typesetting change of the entry moves neither)", () => {
    const intro = "Let $k$ be the number of clusters.";
    const base = symbolBasis(sym(), intro, [], JSON.stringify(shown()));
    const same = sym({ def: "the  number of clusters" });
    expect(symbolBasis(same, intro, [], JSON.stringify(shown({ entry: { name: "k" } })))).toBe(base);
    expect(symbolBasisParts(same, intro, [], shown())).toEqual(symbolBasisParts(sym(), intro, [], shown()));
  });
});

describe("symbolShownParts: the settings naming the symbol, the listing and the uses by their set", () => {
  const core = {
    symbols: [{ name: "k", type: "integer", space: "$\\mathbb{N}$", def: "the number of clusters", refs: [] }, { name: "n", type: "integer", space: "$\\mathbb{N}$", def: "the sample size", refs: [] }, { name: "\\mu", type: "measure", space: "", def: "the law", refs: [] }],
    sampling_model: {
      seeding: "the $k$ centers are drawn uniformly. Used by thm:a.",
      design: "the $n$ points are iid. Used by thm:b.",
      other: "the weights are fixed. Used by thm:c.",
      nested: { law: "the law $\\mu$ is fixed" },
    },
    statements: [
      { id: "thm:b", free_symbols: ["k", "n"], depends_on: [], statement: "$k$ and $n$" },
      { id: "thm:a", free_symbols: ["k"], depends_on: [], statement: "$k$" },
      { id: "thm:c", free_symbols: [], depends_on: [], statement: "nothing" },
    ],
    assumptions: [],
    definitions: [],
  } as unknown as Core;
  const slices = new Map();
  it("settingsNaming: the settings in which the symbol appears, those of a result using it, and a global one; not a setting of other results", () => {
    // k appears in `seeding`; `design` governs thm:b, which uses k; `other` governs thm:c only;
    // `nested` names no result: global, read by its strings
    expect(Object.keys(settingsNaming(core, "k"))).toEqual(["design", "nested", "seeding"]);
    expect(Object.keys(settingsNaming(core, "n"))).toEqual(["design", "nested"]);
    expect(Object.keys(settingsNaming(core, "\\mu"))).toEqual(["nested"]);
    const global = { ...core, sampling_model: { ...core.sampling_model, general: "every quantity is finite" } } as Core;
    expect(Object.keys(settingsNaming(global, "n"))).toEqual(["design", "general", "nested"]);
  });
  it("a reworded setting moves only the symbols it names; a reordered listing moves none; the legacy key moves on both", () => {
    const before = symbolShownParts({ core, slices } as never, "k");
    const reworded = { ...core, sampling_model: { ...core.sampling_model, other: "the weights are fixed and positive. Used by thm:c." } } as Core;
    expect(symbolShownParts({ core: reworded, slices } as never, "k")).toEqual(before);
    expect(symbolShownBasis({ core: reworded, slices } as never, "k", true)).not.toBe(symbolShownBasis({ core, slices } as never, "k", true));
    const reordered = { ...core, statements: [...core.statements].reverse() } as Core;
    expect(symbolShownParts({ core: reordered, slices } as never, "k")).toEqual(before);
    expect(before.listing).toEqual(["thm:a", "thm:b"]);
    expect(symbolShownBasis({ core: reordered, slices } as never, "k", true)).not.toBe(symbolShownBasis({ core, slices } as never, "k", true));
    const kReworded = { ...core, sampling_model: { ...core.sampling_model, seeding: "the $k$ centers are drawn at random. Used by thm:a." } } as Core;
    expect(symbolShownParts({ core: kReworded, slices } as never, "k")).not.toEqual(before);
    expect(symbolShownParts({ core: kReworded, slices } as never, "n")).toEqual(symbolShownParts({ core, slices } as never, "n"));
  });
});

describe("symbolRegradeLine", () => {
  const parts = { k: { source: "1", intro: "2", settings: "3" }, n: { source: "1", intro: "2", settings: "3" }, x: { source: "9", intro: "2", settings: "3" } };
  const prior = {
    k: { basis_parts: { source: "1", intro: "2", settings: "0" } },
    n: { basis_parts: { source: "1", intro: "0", settings: "0" } },
    x: {},
  };
  it("counts each moved part over the graded symbols, then the new and the unrecorded", () => {
    const line = symbolRegradeLine(["k", "n", "x", "y"], (name) => parts[name as keyof typeof parts], (name) => prior[name as keyof typeof prior]);
    expect(line).toBe("why re-graded — 2 settings, 1 intro, 1 new, 1 no parts on record");
  });
  it("nothing moved: says so", () => {
    expect(symbolRegradeLine(["k"], () => ({ a: "1" }), () => ({ basis_parts: { a: "1" } }))).toBe("why re-graded — nothing moved");
  });
});
