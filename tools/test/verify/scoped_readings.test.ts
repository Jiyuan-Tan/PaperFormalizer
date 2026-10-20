/**
 * A pinned symbol reading in two parts (`types.ts` `V15SymbolVerdict.reading`): the GENERAL part is the
 * symbol's `def`, each SCOPED clause holds in the results it is tagged with. A node reads the general
 * part and the clauses applicable to it (`core_graph.ts` `applicableClauses`) — in its referee's
 * prompt and in its verdict basis — so rewording one result's clause re-opens that result and what
 * rests on it, never an unrelated user of the symbol; a reading without clauses is the reading as it
 * was, basis for basis.
 */
import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { SymbolSchema, type Core } from "../../src/core/schema.js";
import { applicableClauses, basisInputs, basisInputsV4, basisOf, buildCore, compileSymbolEdits, fullReadingText, nodeFingerprint, regradeCause, resultTexName, resultsUsingSymbol, symbolEntryShown } from "../../src/verify/core_graph.js";
import { compactCore, globalCoreText, SymbolReplySchema } from "../../src/verify/referee_shard_prompts.js";
import { keptReading, staleTags, symbolContract, symbolRetryEcho } from "../../src/verify/referee_symbols.js";
import type { V15SymbolVerdict } from "../../src/verify/types.js";

/** lem:a (under ass:h) and thm:c (under ass:g) use W; thm:b rests on lem:a without naming W. */
function core(): Core {
  return {
    qid: "scoped",
    symbols: [
      { name: "W", type: "vector", def: "$W$ is the model vector.", refs: ["n"] },
      { name: "n", type: "sample size" },
    ],
    assumptions: [
      { id: "ass:h", kind: "regularity", condition: "$E|W| < \\infty$.", free_symbols: ["W"] },
      { id: "ass:g", kind: "regularity", condition: "$W$ is bounded.", free_symbols: ["W"] },
    ],
    definitions: [],
    statements: [
      { id: "lem:a", kind: "lemma", statement: "$W$ is tight.", depends_on: ["ass:h"], free_symbols: ["W"], status: "to-prove", tex_locator: { file: "m.tex", from: 1, to: 2, env: "lemma", label: "lem:tight" } },
      { id: "thm:b", kind: "theorem", statement: "The estimator is consistent.", depends_on: ["lem:a"], free_symbols: [], status: "to-prove", tex_locator: { file: "m.tex", from: 3, to: 4, env: "theorem", label: "thm:cons" } },
      { id: "thm:c", kind: "theorem", statement: "$W$ has a density.", depends_on: ["ass:g"], free_symbols: ["W"], status: "to-prove" },
    ],
    target_estimand: "x",
    bibliography: [],
  } as unknown as Core;
}
const IDS = ["lem:a", "thm:b", "thm:c", "ass:h", "ass:g"];
/** The scheme-4 bases of `core()` under the code before scoped clauses existed (commit 1faec84). */
const BEFORE: Record<string, string> = {
  "lem:a": "f04d60ad114330b556a045be76df336f357a3fc6014665d2f24437c287a00a53",
  "thm:b": "882be9be729d01d4126d5125dfff1f0c37ce86ee81f2571bf8349c8e391abeb2",
  "thm:c": "25e833758a6467c77cc99bea3575b02a381624cde1ecf702fa9d5930e3f5b14a",
  "ass:h": "abbcf121849c7759100b78df74575861693b2234de6e68e1dc844d9a253ebca4",
  "ass:g": "601a0842c53bc383ad4e782319f93a69b8563bf91702ccd2fc7e9b3590989b73",
};

const GENERAL = "$W$ is the random model vector.";
const pin = (scoped?: Array<{ results: string[]; text: string }>, reading = GENERAL): V15SymbolVerdict =>
  ({ name: "W", meaning: "ok", fix: null, ambiguity: "pinned", reading: { reading, evidence: "Section 2", ...(scoped ? { scoped } : {}) }, redefined_at: null, detail: "d" }) as V15SymbolVerdict;
const built = (v: V15SymbolVerdict): Core => buildCore(core(), { symbols: [v] }).core;
const bases = (c: Core): Record<string, string> => Object.fromEntries(IDS.map((id) => [id, nodeFingerprint(c, id)]));
/** … under scheme 4 (`basisInputsV4`, kept for the carry-over of verdicts recorded under it). */
const basesV4 = (c: Core): Record<string, string> => Object.fromEntries(IDS.map((id) => [id, basisOf(basisInputsV4(c, id))]));
const moved = (a: Core, b: Core): string[] => IDS.filter((id) => nodeFingerprint(a, id) !== nodeFingerprint(b, id));

describe("scoped symbol readings: the reply and its contract", () => {
  const users = (): ReadonlySet<string> => new Set(["lem:a", "thm:c"]);
  const check = (v: V15SymbolVerdict): string => symbolContract([v], new Set(["W"]), new Set(["W"]), users).join(" ");

  it("the reply schema takes a reading with scoped clauses and null (kept) texts; a reply without `scoped` is the earlier shape", () => {
    const entry = (reading: unknown) => ({ name: "W", keep: false, meaning: "ok", fix: null, ambiguity: "pinned", reading, redefined_at: null, detail: "d" });
    const r = SymbolReplySchema.parse({ summary: "s", symbols: [entry({ reading: null, evidence: "e", scoped: [{ results: ["lem:a"], text: null }] }), entry({ reading: "g", evidence: "e" })] });
    expect(r.symbols[0]!.reading).toEqual({ reading: null, evidence: "e", scoped: [{ results: ["lem:a"], text: null }] });
    expect(r.symbols[1]!.reading).toEqual({ reading: "g", evidence: "e" });
    expect(() => SymbolReplySchema.parse({ summary: "s", symbols: [entry({ reading: "g", evidence: "e", scoped: [{ results: "lem:a", text: "t" }] })] })).toThrow();
  });

  it("a clause is tagged with statements using the symbol, has a text, and no two clauses the same results; a reading has a general part", () => {
    expect(check(pin([{ results: ["lem:a"], text: "$W$ is localized." }]))).toBe("");
    expect(check(pin([{ results: ["lem:a", "thm:b"], text: "t" }]))).toContain("is tagged with thm:b, not the id of a result using the symbol");
    expect(check(pin([{ results: ["ass:h"], text: "t" }]))).toContain("is tagged with ass:h");
    expect(check(pin([{ results: [], text: "t" }]))).toContain("names no result");
    expect(check(pin([{ results: ["lem:a"], text: " " }]))).toContain("has no text");
    expect(check(pin([{ results: ["lem:a", "thm:c"], text: "t" }, { results: ["thm:c", "lem:a"], text: "u" }]))).toContain("repeats the results of another clause");
    expect(check(pin(undefined, ""))).toContain("has no general part");
    // TeX of a clause is checked like the general part's, and the retry echoes it
    const bad = pin([{ results: ["lem:a"], text: "$W$ in \\\\mathbb{R}" }]);
    const v = symbolContract([bad], new Set(["W"]), new Set(["W"]), users);
    expect(v.join(" ")).toContain("its reading's scoped clause [lem:a]");
    expect(symbolRetryEcho([bad], v)).toContain("scoped [lem:a]: $W$ in \\\\mathbb{R}");
  });

  it("keptReading: a null text is the piece on file, word for word; a clause is found by its results, in any order; nothing on file to keep comes out empty (refused)", () => {
    const on = { reading: GENERAL, evidence: "old", scoped: [{ results: ["thm:c", "lem:a"], text: "both" }, { results: ["lem:a"], text: "only a" }] };
    const k = keptReading({ reading: null, evidence: "new", scoped: [{ results: ["lem:a", "thm:c"], text: null }, { results: ["lem:a"], text: "only a, reworded" }] }, on);
    expect(k).toEqual({ reading: GENERAL, evidence: "new", scoped: [{ results: ["thm:c", "lem:a"], text: "both" }, { results: ["lem:a"], text: "only a, reworded" }] });
    const none = keptReading({ reading: null, evidence: "e", scoped: [{ results: ["thm:c", "thm:c"], text: null }] }, null);
    expect(none).toEqual({ reading: "", evidence: "e", scoped: [{ results: ["thm:c"], text: "" }] });
    expect(check({ ...pin(), reading: none })).toMatch(/has no general part.*has no text/su);
  });

  it("omission never deletes: a clause on file the reply does not mention stays, in place; only an explicit drop removes one; a new clause is added after", () => {
    const A = { results: ["lem:a"], text: "only a" };
    const C = { results: ["thm:c"], text: "only c" };
    const on = { reading: GENERAL, evidence: "old", scoped: [A, C] };
    // the reply lists only the clause it changed; lists none; has no `scoped` at all
    expect(keptReading({ reading: null, evidence: "e", scoped: [{ results: ["thm:c"], text: "c, reworded" }] }, on).scoped).toEqual([A, { results: ["thm:c"], text: "c, reworded" }]);
    expect(keptReading({ reading: "g2", evidence: "e", scoped: [] }, on)).toEqual({ reading: "g2", evidence: "e", scoped: [A, C] });
    expect(keptReading({ reading: null, evidence: "e" }, on).scoped).toEqual([A, C]);
    // an explicit drop, with its reason; a drop of a clause not on file drops nothing
    const gone: string[] = [];
    const d = keptReading({ reading: null, evidence: "e", scoped: [{ results: ["lem:a"], text: null, drop: "the lemma no longer localizes" }, { results: ["thm:b"], text: null, drop: "x" }, { results: ["lem:a", "thm:c"], text: "both" }] }, on, { dropped: (c, why) => gone.push(`${c.results.join(",")}: ${why}`) });
    expect(d.scoped).toEqual([C, { results: ["lem:a", "thm:c"], text: "both" }]);
    expect(gone).toEqual(["lem:a: the lemma no longer localizes"]);
    expect(keptReading({ reading: null, evidence: "e", scoped: [{ results: ["lem:a"], text: null, drop: "a" }, { results: ["thm:c"], text: null, drop: "c" }] }, on)).toEqual({ reading: GENERAL, evidence: "e" });
    // a clause on file with a dead tag, unmentioned: kept for its live results; with none left it stays as
    // it is — never removed silently — and the contract refuses it until the reply says where it goes
    const AC = { results: ["lem:a", "thm:c"], text: "both" };
    const stale = keptReading({ reading: null, evidence: "e" }, { ...on, scoped: [A, AC] }, { live: (id) => id !== "lem:a", dropped: () => gone.push("removed") });
    expect(stale.scoped).toEqual([A, { results: ["thm:c"], text: "both" }]);
    expect(gone).not.toContain("removed");
    expect(symbolContract([{ ...pin(), reading: stale }], new Set(["W"]), new Set(["W"]), () => new Set(["thm:c"])).join(" ")).toContain("scoped clause [lem:a] is tagged with lem:a, not the id of a result using the symbol");
    // a new clause overlapping a clause on file the reply does not list: both would bind the shared result — reported
    const why: string[] = [];
    keptReading({ reading: null, evidence: "e", scoped: [{ results: ["lem:a", "thm:b"], text: "restated" }] }, on, { problem: (w) => why.push(w) });
    expect(why).toEqual([expect.stringContaining("its new scoped clause [lem:a, thm:b] and the clause on file [lem:a], which the reply does not list, would both hold in lem:a")]);
    why.length = 0;
    keptReading({ reading: null, evidence: "e", scoped: [{ results: ["lem:a", "thm:b"], text: "restated" }, { results: ["lem:a"], text: null, drop: "restated wider" }] }, on, { problem: (w) => why.push(w) });
    keptReading({ reading: null, evidence: "e", scoped: [{ results: ["lem:a", "thm:b"], text: "restated" }, { results: ["lem:a"], text: null }] }, on, { problem: (w) => why.push(w) });
    expect(why).toEqual([]);
    expect(staleTags(on, new Set(["thm:c"]))).toEqual([{ clause: A, gone: ["lem:a"] }]);
    expect(staleTags(on, new Set(["thm:c", "lem:a"]))).toEqual([]);
  });
});

describe("scoped symbol readings: the core's table", () => {
  it("the general part is the entry's def, the clauses its `scoped`; a reading without clauses leaves no field; the entry survives the core schema", () => {
    const clause = { results: ["lem:a"], text: " $W$ is localized. " };
    expect(compileSymbolEdits(core(), [pin([clause])])).toEqual([{ op: "set_symbol", name: "W", def: GENERAL, scoped: [{ results: ["lem:a"], text: "$W$ is localized." }] }]);
    expect(compileSymbolEdits(core(), [pin()])).toEqual([{ op: "set_symbol", name: "W", def: GENERAL }]);
    expect(compileSymbolEdits(core(), [pin([])])).toEqual([{ op: "set_symbol", name: "W", def: GENERAL }]);
    // only a pinned reading's clauses reach the table
    expect(compileSymbolEdits(core(), [{ ...pin([clause]), ambiguity: "unresolvable" }])).toEqual([]);
    const c = built(pin([clause]));
    expect(c.symbols[0]).toMatchObject({ def: GENERAL, scoped: [{ results: ["lem:a"], text: "$W$ is localized." }] });
    expect(SymbolSchema.parse(JSON.parse(JSON.stringify(c.symbols[0]))).scoped).toEqual([{ results: ["lem:a"], text: "$W$ is localized." }]);
    expect("scoped" in built(pin()).symbols[0]!).toBe(false);
  });
});

describe("scoped symbol readings: the clauses applicable to a node", () => {
  const clauses = [
    { results: ["lem:a"], text: "A" },
    { results: ["thm:c", "lem:a"], text: "AC" },
    { results: ["thm:c"], text: "C" },
    { results: ["thm:gone"], text: "stale" },
  ];
  const of = (id: string | string[]): string[] => applicableClauses(core(), id, clauses).map((c) => `${c.text}<${c.results.join(",")}>`);

  it("a statement: the clauses tagged with it or with a result in its closure, cut to those results", () => {
    expect(of("lem:a")).toEqual(["A<lem:a>", "AC<lem:a>"]);
    expect(of("thm:b")).toEqual(["A<lem:a>", "AC<lem:a>"]);
    expect(of("thm:c")).toEqual(["AC<thm:c>", "C<thm:c>"]);
  });

  it("an assumption or definition: the clauses tagged with a result whose closure holds it; a tag that names no statement applies to nothing", () => {
    expect(of("ass:h")).toEqual(["A<lem:a>", "AC<lem:a>"]);
    expect(of("ass:g")).toEqual(["AC<thm:c>", "C<thm:c>"]);
    expect(of("thm:gone")).toEqual([]);
    expect(applicableClauses(core(), "lem:a", undefined)).toEqual([]);
  });

  it("several nodes (a shard): the clauses applicable to any of them", () => {
    expect(of(["thm:b", "ass:g"])).toEqual(["A<lem:a>", "AC<thm:c,lem:a>", "C<thm:c>"]);
  });
});

describe("the global pass's core: a carried neighbour", () => {
  it("keeps what places it in the paper and in a split: its label, `split_from`, `umbrella` — with its text and wiring, no other field", () => {
    const c = core();
    Object.assign(c.statements.find((st) => st.id === "thm:b")!, { split_from: "thm:c", umbrella: true, proof_tex: "p" });
    const line = globalCoreText(c, new Set(["lem:a", "thm:b"]), new Set(["lem:a"])).split("\n").find((l) => l.startsWith('{"id":"thm:b"'))!;
    expect(JSON.parse(line)).toEqual({ id: "thm:b", kind: "theorem", label: "thm:cons", statement: "The estimator is consistent.", depends_on: ["lem:a"], split_from: "thm:c", umbrella: true, carried: true });
  });
});

describe("scoped symbol readings: the verdict basis", () => {
  it("a table without scoped clauses hashes under scheme 4 exactly as before the split: every scheme-4 basis of the fixture is the one the earlier code gave; a node using nothing keeps it under scheme 5", () => {
    expect(basesV4(core())).toEqual(BEFORE);
    expect(basisInputsV4(core(), "lem:a").scheme).toBe(4);
    expect(basisInputs(core(), "lem:a").scheme).toBe(5);
    for (const id of ["ass:h", "ass:g"]) expect(bases(core())[id]).toBe(BEFORE[id]);
    // a clause applicable to no node of the core moves nothing either
    const stale = core();
    stale.symbols[0]!.scoped = [{ results: ["thm:gone"], text: "stale" }];
    expect(basesV4(stale)).toEqual(BEFORE);
    expect(bases(stale)).toEqual(bases(core()));
  });

  it("a clause tagged with result A is in the basis of A, of what rests on A and of A's hypotheses — not of an unrelated user of the symbol", () => {
    const plain = built(pin());
    const a1 = built(pin([{ results: ["lem:a"], text: "$W$ is localized at $0$." }]));
    const a2 = built(pin([{ results: ["lem:a"], text: "$W$ is localized at $1$." }]));
    expect(moved(plain, a1)).toEqual(["lem:a", "thm:b", "ass:h"]);
    expect(moved(a1, a2)).toEqual(["lem:a", "thm:b", "ass:h"]);
    expect(regradeCause({ inputs: basisInputs(a1, "thm:b"), clean: true }, basisInputs(a2, "thm:b"))).toBe("symbol meaning");
    // a re-typesetting of the clause moves nothing; nor does tagging it with one more, unrelated result… for A
    expect(moved(a1, built(pin([{ results: ["lem:a"], text: "$W$  is localized at $0$." }])))).toEqual([]);
    expect(moved(a1, built(pin([{ results: ["lem:a", "thm:c"], text: "$W$ is localized at $0$." }])))).toEqual(["thm:c", "ass:g"]);
    // dropping it re-opens the same nodes
    expect(moved(a1, plain)).toEqual(["lem:a", "thm:b", "ass:h"]);
  });

  it("the general part is in the basis of every user of the symbol", () => {
    const clause = [{ results: ["lem:a"], text: "$W$ is localized at $0$." }];
    expect(moved(built(pin(clause)), built(pin(clause, "$W$ is the fixed model vector.")))).toEqual(IDS);
  });
});

describe("scoped symbol readings: what a prompt and a reader are shown", () => {
  const c = built(pin([{ results: ["lem:a"], text: "$W$ is localized." }, { results: ["thm:c"], text: "$W$ has a density." }]));
  const W = c.symbols[0]!;

  it("a result is named by its environment word and \\ref; one without a label, or gone from the core, by its id", () => {
    expect(resultTexName(c, "lem:a")).toBe("Lemma~\\ref{lem:tight}");
    expect(resultTexName(c, "thm:c")).toBe("Theorem thm:c");
    expect(resultTexName(c, "thm:gone")).toBe("thm:gone");
  });

  it("a shard's symbol rows carry the clauses applicable to the nodes it grades, as 'In <result>: <text>' with the nodes each binds; the global pass every clause", () => {
    expect(symbolEntryShown(c, W, ["thm:b"])).toEqual({ name: "W", type: "vector", def: GENERAL, refs: ["n"], scoped: ["In Lemma~\\ref{lem:tight}: $W$ is localized. [binds thm:b]"] });
    const shard = compactCore(c, new Set(["lem:a"]));
    expect(shard).toContain(JSON.stringify("In Lemma~\\ref{lem:tight}: $W$ is localized. [binds lem:a]"));
    expect(shard).not.toContain("has a density. [");
    const other = compactCore(c, new Set(["thm:c"]));
    expect(other).toContain(JSON.stringify("In Theorem thm:c: $W$ has a density. [binds thm:c]"));
    expect(other).not.toContain("is localized");
    const all = globalCoreText(c);
    expect(all).toContain(JSON.stringify("In Lemma~\\ref{lem:tight}: $W$ is localized."));
    expect(all).toContain("has a density.");
    expect(globalCoreText(c, new Set(["thm:c", "ass:g"]))).not.toContain("is localized");
    // a table without clauses is shown as it was: the entry, no `scoped`
    expect(compactCore(built(pin()), new Set(["lem:a"]))).toContain(JSON.stringify({ name: "W", type: "vector", def: GENERAL, refs: ["n"] }));
  });

  // A clause reaches a hypothesis only through a result using it: it says how that result reads the
  // symbol, and the hypothesis is graded on its own words (live extreme-effects, 2026-10-08: a
  // repaired result's clause, labelled as binding the printed definition, was graded as its drift).
  it("a line binds the results it reaches and is context for the hypotheses and definitions; the label moves no basis", () => {
    expect(symbolEntryShown(c, W, ["ass:h"]).scoped).toEqual(["In Lemma~\\ref{lem:tight}: $W$ is localized. [context for ass:h]"]);
    expect(symbolEntryShown(c, W, ["lem:a", "ass:h", "thm:b"]).scoped).toEqual(["In Lemma~\\ref{lem:tight}: $W$ is localized. [binds lem:a, thm:b; context for ass:h]"]);
    // a global prompt over its budget shows each clause once, naming its results, without the shown nodes it binds or is context for
    const compact = globalCoreText(c, new Set(["lem:a", "ass:h", "thm:b"]), new Set(["lem:a", "ass:h", "thm:b"]), { compactSymbols: true });
    expect(compact).toContain(JSON.stringify("In Lemma~\\ref{lem:tight}: $W$ is localized."));
    expect(compact).not.toContain("context for");
    expect(compact).not.toContain("[binds");
    // the basis reads the clause as printed before its label (`scopedClauseText`), as it did
    const line = applicableClauses(c, "ass:h", W.scoped).map((cl) => `In ${cl.results.map((r) => resultTexName(c, r)).join(", ")}: ${cl.text}`);
    expect(line).toEqual(["In Lemma~\\ref{lem:tight}: $W$ is localized."]);
    // … to the hash: the basis of the hypothesis under the code before the label (commit 192cfd2)
    expect(nodeFingerprint(c, "ass:h")).toBe("43c44ca94381839737660558fe4338be9580fc9c32ee437d8af3a72133c120f9");
    const brief = (rel: string): string => readFileSync(new URL(`../../src/verify/prompts/V1.5/${rel}`, import.meta.url), "utf8").replace(/\s+/g, " ");
    expect(brief("shard.txt")).toContain("after `context for`, the hypotheses and definitions a result it names uses — how that result reads the symbol, never a ground for their grade");
    expect(brief("review.txt")).toContain("never a hypothesis or definition they use, which is faithful on its own printed words");
    expect(brief("review.txt")).not.toContain("a line binds the nodes it lists");
  });

  it("shown = hashed over a shard of several nodes: each node is bound by exactly the lines its basis reads, and rewording a clause changes the lines of the nodes whose basis moves, no other", () => {
    const shardOf = (k: Core): Map<string, string[]> => {
      const row = compactCore(k, new Set(IDS)).split("\n").find((l) => l.startsWith('{"name":"W"'))!;
      const lines = ((JSON.parse(row) as { scoped?: string[] }).scoped ?? []).map((l) => /^(.*) \[(.*)\]$/su.exec(l)!);
      return new Map(IDS.map((id) => [id, lines.filter((m) => m[2]!.replace(/binds |context for /gu, "").split(/[,;] /u).includes(id)).map((m) => m[1]!)] as const));
    };
    const two = (cText: string): Core => built(pin([{ results: ["lem:a", "thm:c"], text: "$W$ is centred." }, { results: ["thm:c"], text: cText }]));
    const k = two("$W$ has a density.");
    const own = (kk: Core, id: string): string[] => applicableClauses(kk, id, kk.symbols[0]!.scoped).map((cl) => `In ${cl.results.map((r) => resultTexName(kk, r)).join(", ")}: ${cl.text}`);
    for (const id of IDS) expect(shardOf(k).get(id)).toEqual(own(k, id));
    // the clause shared by lem:a and thm:c is printed once per reading of it, each labelled with its nodes
    expect(shardOf(k).get("lem:a")).toEqual(["In Lemma~\\ref{lem:tight}: $W$ is centred."]);
    expect(shardOf(k).get("thm:c")).toEqual(["In Theorem thm:c: $W$ is centred.", "In Theorem thm:c: $W$ has a density."]);
    const k2 = two("$W$ has a bounded density.");
    const changed = IDS.filter((id) => JSON.stringify(shardOf(k).get(id)) !== JSON.stringify(shardOf(k2).get(id)));
    expect(changed).toEqual(moved(k, k2));
    expect(changed).toEqual(["thm:c", "ass:g"]);
    // how a tagged result is named is printed, so it is hashed: a new label moves the nodes shown it
    const relabelled = structuredClone(k);
    relabelled.statements.find((st) => st.id === "lem:a")!.tex_locator!.label = "lem:tight2";
    expect(moved(k, relabelled).filter((id) => id !== "lem:a")).toEqual(["thm:b", "ass:h"]);
  });

  it("a tag that is no statement of the built core is handed on nowhere: not in the table, not in a full reading; a block a repair split off is named by its parent", () => {
    const dead = built(pin([{ results: ["thm:cor-fix-dead", "lem:a", "lem:a"], text: "A." }, { results: ["thm:cor-fix-dead"], text: "gone." }]));
    expect(dead.symbols[0]!.scoped).toEqual([{ results: ["lem:a"], text: "A." }]);
    expect("scoped" in built(pin([{ results: ["thm:cor-fix-dead"], text: "gone." }])).symbols[0]!).toBe(false);
    const name = (id: string): string | null => (c.statements.some((st) => st.id === id) ? resultTexName(c, id) : null);
    expect(fullReadingText(pin([{ results: ["thm:gone", "lem:a"], text: "A." }, { results: ["thm:gone"], text: "gone." }]).reading!, name)).toBe(`${GENERAL} In Lemma~\\ref{lem:tight}: A.`);
    const split = structuredClone(c);
    split.statements.push({ id: "lem:cor-fix-1", kind: "lemma", statement: "$W$ is tight on a ball.", depends_on: [], status: "proved", split_from: "lem:a" } as never);
    expect(resultTexName(split, "lem:cor-fix-1")).toBe("the result split from Lemma~\\ref{lem:tight}");
  });

  it("a result uses a symbol when its statement or proof names it, or a hypothesis it is stated under does — and may then be tagged", () => {
    const k = core();
    k.statements.push({ id: "lem:p", kind: "lemma", statement: "The remainder vanishes.", proof_tex: "Condition on $W$.", depends_on: [], free_symbols: [], status: "to-prove" } as never);
    k.statements.push({ id: "lem:h", kind: "lemma", statement: "The mean exists.", depends_on: ["ass:h"], free_symbols: [], status: "to-prove" } as never);
    expect(resultsUsingSymbol(k, "W")).toEqual(["lem:a", "thm:c", "lem:p", "lem:h"]);
    const users = (n: string): ReadonlySet<string> => new Set(resultsUsingSymbol(k, n));
    expect(symbolContract([pin([{ results: ["lem:p"], text: "In the proof $W$ is conditioned on." }])], new Set(["W"]), new Set(["W"]), users)).toEqual([]);
    expect(symbolContract([pin([{ results: ["thm:b"], text: "t" }])], new Set(["W"]), new Set(["W"]), users).join(" ")).toContain("is tagged with thm:b");
    // the proof-only user is shown the row with its clause, and its basis reads it
    const b = buildCore(k, { symbols: [pin([{ results: ["lem:p"], text: "In the proof $W$ is conditioned on." }])] }).core;
    expect(compactCore(b, new Set(["lem:p"]))).toContain("In Lemma lem:p: In the proof $W$ is conditioned on. [binds lem:p]");
    expect(nodeFingerprint(b, "lem:p")).not.toBe(nodeFingerprint(buildCore(k, { symbols: [pin()] }).core, "lem:p"));
  });

  it("a reading in full: the general part, then every clause led by its results' names; without clauses, the general part unchanged", () => {
    const name = (id: string): string => resultTexName(c, id);
    expect(fullReadingText(pin([{ results: ["lem:a", "thm:c"], text: "$W$ is localized." }, { results: ["thm:c"], text: "kept." }]).reading!, name)).toBe(
      `${GENERAL} In Lemma~\\ref{lem:tight}, Theorem thm:c: $W$ is localized. In Theorem thm:c: kept.`,
    );
    expect(fullReadingText(pin().reading!, name)).toBe(GENERAL);
  });
});
