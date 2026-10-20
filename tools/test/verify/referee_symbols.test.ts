import { fileURLToPath } from "node:url";
/**
 * The V1.5 symbol referee (`referee_symbols.ts`, `symbol_match.ts`, the symbol parts of
 * `referee_slices.ts`, `core_graph.ts`, `stage_v1_5.ts`, `annotated_paper.ts`). No network: the fake
 * codex answers by the reply schema it is handed.
 */
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState } from "../../src/state.js";
import type { StateJson } from "../../src/types.js";
import { createHash } from "node:crypto";
import { bindingReadings, buildCore, symbolSourceHash, symbolUsers } from "../../src/verify/core_graph.js";
import { paperIndex, sectionRange } from "../../src/verify/referee_slices.js";
import { SYMBOL_REPLY, symbolShownBasis } from "../../src/verify/referee_shard_prompts.js";
import { allSymbolSlices, correctedBasisText, correctedReading, correctedSources, correctionTouchesSymbol, groupSymbolShards, resultsNamedBy, runSymbolPass, unresolvedRefs, sentencesNaming, sentencesOf, symbolBasis, symbolContract, type SymbolPassInput } from "../../src/verify/referee_symbols.js";
import { priorPassComplete, runStageV1_5, symbolsReadingDemoted } from "../../src/verify/stage_v1_5.js";
import { mentionsSymbol, symbolAppears, symbolPattern } from "../../src/verify/symbol_match.js";
import { VERIFY_FILES, type V15SymbolVerdict, type VerifyStageArgs } from "../../src/verify/types.js";
import { isSymbolCall, okSymbol, symbolNames } from "./symbol_fake.js";


const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

const TOOLS = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..");
const BRIEF = (f: string): Promise<string> => readFile(path.join(TOOLS, "src", "verify", "prompts", "V1.5", f), "utf8");

// ---------------------------------------------------------------------------------------------
// A toy paper: Δ is a random remainder defined inside the theorem.
// ---------------------------------------------------------------------------------------------

const FLAT = [
  "\\documentclass{article}", // 1
  "\\newcommand{\\E}{\\mathbb{E}}", // 2
  "\\begin{document}", // 3
  "\\section{Setup}", // 4
  "Let $W$ denote the data; the sample is split into folds.", // 5
  "Write $\\hat\\gamma$ for the estimator trained on the other folds.", // 6
  "", // 7
  "\\begin{theorem}\\label{thm:main}", // 8
  "With probability $1-\\epsilon$, $|\\hat{\\theta}-\\theta_0| \\leq \\Delta$,", // 9
  "where $\\Delta = n^{-1/2} R(\\hat{\\gamma})$ and $\\Delta_h$ is unrelated.", // 10
  "\\end{theorem}", // 11
  "", // 12
  "\\begin{lemma}\\label{lem:aux}", // 13
  "Under Assumption~\\ref{ass:a}, $\\Delta \\geq 0$ and $\\bar{\\Delta} \\leq 1$.", // 14
  "\\end{lemma}", // 15
  "", // 16
  "\\begin{assumption}\\label{ass:a}", // 17
  "$E[\\Delta^2] < \\infty$.", // 18
  "\\end{assumption}", // 19
  "", // 20
  "\\begin{theorem}\\label{thm:other}", // 21
  "Under Assumption~\\ref{ass:a}, $\\hat{\\theta}$ is consistent.", // 22
  "\\end{theorem}", // 23
  "", // 24
  "\\section{Appendix}", // 25
  "In this section we redefine: let $\\Delta$ be the oracle remainder instead.", // 26
  "\\end{document}", // 27
].join("\n");

function toyCore(): Core {
  return {
    qid: "toy",
    symbols: [
      { name: "W", type: "data" },
      { name: "\\hat{\\gamma}", type: "estimator", refs: ["W"] },
      { name: "n", type: "sample size" },
      { name: "\\theta_0", type: "target" },
      { name: "\\hat{\\theta}", type: "estimator", refs: ["\\theta_0", "\\hat{\\gamma}"] },
      { name: "\\Delta", type: "bound", refs: ["\\hat{\\gamma}", "n"] },
    ],
    assumptions: [
      { id: "ass:a", kind: "regularity", condition: "$E[\\Delta^2] < \\infty$.", free_symbols: ["\\Delta"], novel: { flag: true, justification: "Assumption 1" }, tex_locator: { file: "main.tex", from: 17, to: 19, env: "assumption", label: "ass:a" } },
    ],
    definitions: [],
    statements: [
      { id: "thm:main", kind: "theorem", statement: "With probability $1-\\epsilon$, $|\\hat{\\theta}-\\theta_0| \\leq \\Delta$,\nwhere $\\Delta = n^{-1/2} R(\\hat{\\gamma})$ and $\\Delta_h$ is unrelated.", depends_on: [], free_symbols: ["\\hat{\\theta}", "\\theta_0", "\\Delta"], proof_tex: "", status: "to-prove", tex_locator: { file: "main.tex", from: 8, to: 11, env: "theorem", label: "thm:main" } },
      { id: "lem:aux", kind: "lemma", statement: "Under Assumption~\\ref{ass:a}, $\\Delta \\geq 0$ and $\\bar{\\Delta} \\leq 1$.", depends_on: [], free_symbols: [], proof_tex: "", status: "to-prove", tex_locator: { file: "main.tex", from: 13, to: 15, env: "lemma", label: "lem:aux" } },
      { id: "thm:other", kind: "theorem", statement: "Under Assumption~\\ref{ass:a}, $\\hat{\\theta}$ is consistent.", depends_on: ["ass:a"], free_symbols: ["\\hat{\\theta}"], proof_tex: "", status: "to-prove", tex_locator: { file: "main.tex", from: 21, to: 23, env: "theorem", label: "thm:other" } },
    ],
    target_estimand: "$\\theta_0$",
    bibliography: [],
  } as unknown as Core;
}

const DELTA_READING = "$\\Delta$ is random: a function of the folds $\\hat\\gamma$ is trained on; the probability in Theorem~\\ref{thm:main} is over those folds.";

function sym(name: string, over: Partial<V15SymbolVerdict> = {}): V15SymbolVerdict {
  return { ...(okSymbol(name) as unknown as V15SymbolVerdict), ...over };
}

// ---------------------------------------------------------------------------------------------
// Finding a symbol in TeX
// ---------------------------------------------------------------------------------------------

describe("symbol matching", () => {
  it("matches whole symbols only, across spellings", () => {
    const d = symbolPattern("\\Delta");
    expect(mentionsSymbol("$\\Delta = 1$", d)).toBe(true);
    expect(mentionsSymbol("$\\Delta^2$", d)).toBe(true);
    expect(mentionsSymbol("$\\Delta_h$", d)).toBe(false);
    expect(mentionsSymbol("$\\Delta'$", d)).toBe(false);
    expect(mentionsSymbol("$\\Delta_{1\\ell}^2$", d)).toBe(false);
    expect(mentionsSymbol("$\\bar{\\Delta}$", d)).toBe(false);
    expect(mentionsSymbol("$\\DeltaL$", d)).toBe(false);
    expect(mentionsSymbol("$\\|\\alpha^{\\min}_0\\|$", symbolPattern("\\alpha_0^{\\min}"))).toBe(true);
    expect(mentionsSymbol("$\\hat\\gamma_\\ell(W)$", symbolPattern("\\hat{\\gamma}_{\\ell}"))).toBe(true);
    expect(mentionsSymbol("$\\theta_0^h$", symbolPattern("\\theta_0"))).toBe(false);
    expect(mentionsSymbol("$\\bar{\\sigma}$", symbolPattern("\\sigma"))).toBe(false);
    expect(mentionsSymbol("We write $W$ for", symbolPattern("W"))).toBe(true);
    expect(mentionsSymbol("We write it", symbolPattern("W"))).toBe(false);
  });
});

// ---------------------------------------------------------------------------------------------
// Sharding and slices
// ---------------------------------------------------------------------------------------------

describe("symbol shards", () => {
  /** 49 symbols in 7 chains of 7: s<c>_<k> refers to s<c>_<k-1>. */
  const chains = Array.from({ length: 7 }, (_, c) => Array.from({ length: 7 }, (_, k) => ({ name: `s${c}_${k}`, type: "t", ...(k > 0 ? { refs: [`s${c}_${k - 1}`] } : {}) }))).flat();
  const names = chains.map((x) => x.name);

  it("~10 per shard, sizes as equal as possible, a symbol with what it refers to", () => {
    const a = groupSymbolShards(chains as never, names);
    expect(a.map((s) => s.length)).toEqual([10, 10, 10, 10, 9]);
    expect(a.flat().sort()).toEqual([...names].sort());
    // a chain of 7 travels whole whenever a shard still has room for it (five of the seven here)
    const whole = Array.from({ length: 7 }, (_, c) => a.some((s) => Array.from({ length: 7 }, (_, k) => `s${c}_${k}`).every((n) => s.includes(n))));
    expect(whole.filter(Boolean).length).toBeGreaterThanOrEqual(5);
  });
});

// ---------------------------------------------------------------------------------------------
// Grading comparison and contract
// ---------------------------------------------------------------------------------------------

describe("symbol contract", () => {
  it("contract: drift needs a fix, pinned a reading, a redefinition is not ok, coverage", () => {
    const known = new Set(["\\Delta", "n"]);
    expect(symbolContract([sym("\\Delta", { meaning: "drift" })], new Set(["\\Delta"]), known).join(" ")).toContain("no fix");
    expect(symbolContract([sym("\\Delta", { ambiguity: "pinned" })], new Set(["\\Delta"]), known).join(" ")).toContain("no reading");
    expect(symbolContract([sym("\\Delta", { redefined_at: "later" })], new Set(["\\Delta"]), known).join(" ")).toContain("redefined_at");
    expect(symbolContract([sym("\\Delta")], new Set(["\\Delta", "n"]), known).join(" ")).toContain("carry no verdict");
    expect(symbolContract([sym("\\Zeta")], new Set(), known).join(" ")).toContain("unknown name");
  });
});

// ---------------------------------------------------------------------------------------------
// The pass: delta cache
// ---------------------------------------------------------------------------------------------

type Grader = (name: string, call: number) => Partial<V15SymbolVerdict>;

function fakeAsk(calls: Array<{ kind: string; names: string[]; prompt: string }>, grade: Grader = () => ({})) {
  return async (c: { kind: string; nodes: string[]; prompt: string }): Promise<unknown> => {
    calls.push({ kind: c.kind, names: c.nodes, prompt: c.prompt });
    const k = calls.length;
    return { summary: "s", symbols: c.nodes.map((n) => ({ ...okSymbol(n), ...grade(n, k) })) };
  };
}

async function passInput(over: Partial<SymbolPassInput> = {}): Promise<SymbolPassInput> {
  return {
    core: toyCore(),
    px: paperIndex(FLAT, null, null),
    lineMap: null,
    prior: [],
    confirmed: {},
    briefs: { symbols: await BRIEF("symbols.txt") },
    scope: "scope",
    ask: fakeAsk([]),
    log: () => {},
    ...over,
  };
}

describe("the symbol pass", () => {
  it("delta: an unchanged table costs no call; a changed symbol is re-graded with the symbols shown its entry; a cleared cache re-grades all", async () => {
    const first = await runSymbolPass(await passInput());
    expect(first.ok).toBe(true);
    if (!first.ok) return;
    const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
    const again = await runSymbolPass(await passInput({ prior: first.symbols, confirmed: first.confirmed, ask: fakeAsk(calls) }));
    expect(calls).toHaveLength(0);
    expect(again.ok && again.symbols.every((v) => v.graded === "carried")).toBe(true);
    const moved = toyCore();
    moved.symbols.find((x) => x.name === "n")!.type = "number of observations";
    await runSymbolPass(await passInput({ core: moved, prior: first.symbols, confirmed: first.confirmed, ask: fakeAsk(calls) }));
    // (\Delta refers to n: its call prints n's entry — shown = hashed)
    expect([...new Set(calls.flatMap((c) => c.names))].sort()).toEqual(["\\Delta", "n"]);
    calls.length = 0;
    await runSymbolPass(await passInput({ prior: first.symbols, confirmed: {}, ask: fakeAsk(calls) }));
    expect(new Set(calls.flatMap((c) => c.names)).size).toBe(6);
  });

  it("a symbol re-graded because a text it is read from changed keeps its grade on file word for word (keep); keep false, or a changed entry, takes the new grade", async () => {
    const pinned = (reading: string): Partial<V15SymbolVerdict> => ({ ambiguity: "pinned", reading: { reading, evidence: "the paper" } });
    const first = await runSymbolPass(await passInput({ ask: fakeAsk([], (n) => (n === "\\Delta" ? pinned("$\\Delta$ is the remainder") : {})) }));
    if (!first.ok) throw new Error("pass failed");
    const main = toyCore().statements.find((s) => s.id === "thm:main")!.statement;
    const corrected = new Map([["thm:main", { printed: main, text: main.replace("With probability", "With probability at least") }]]);
    const again = async (keep: boolean, core = toyCore()) => {
      const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
      const res = await runSymbolPass(
        await passInput({ core, corrected, prior: first.symbols, confirmed: first.confirmed, ask: fakeAsk(calls, (n) => (n === "\\Delta" ? { ...pinned("$\\Delta$ denotes the remainder term"), keep } : {})) }),
      );
      if (!res.ok) throw new Error("pass failed");
      return { calls, delta: res.symbols.find((v) => v.name === "\\Delta")! };
    };
    const k = await again(true);
    expect(k.calls.flatMap((c) => c.names)).toContain("\\Delta");
    expect(k.calls[0]!.prompt).toContain("- \\Delta: meaning ok; ambiguity pinned");
    expect(k.calls[0]!.prompt).toContain("reading (general part): $\\Delta$ is the remainder");
    expect(k.delta).toMatchObject({ graded: "fresh", reading: { reading: "$\\Delta$ is the remainder" } });
    expect(k.delta).not.toHaveProperty("keep");
    expect((await again(false)).delta.reading?.reading).toBe("$\\Delta$ denotes the remainder term");
    // a changed entry is graded afresh: its grade on file is not offered, a keep is ignored
    const moved = toyCore();
    moved.symbols.find((x) => x.name === "\\Delta")!.type = "remainder term";
    const m = await again(true, moved);
    expect(m.calls[0]!.prompt).not.toContain("- \\Delta: meaning");
    expect(m.delta.reading?.reading).toBe("$\\Delta$ denotes the remainder term");
  });

  it("a re-graded reading keeps its pieces: the general part and the clauses answered null are the ones on file word for word, only the clause written is new; a clause tagged with a result not using the symbol is refused", async () => {
    const general = "$\\Delta$ is the random remainder.";
    const onFile = [{ results: ["thm:main"], text: "$\\Delta = n^{-1/2} R(\\hat{\\gamma})$." }, { results: ["lem:aux"], text: "$\\Delta \\geq 0$." }];
    const first = await runSymbolPass(await passInput({ ask: fakeAsk([], (n) => (n === "\\Delta" ? { ambiguity: "pinned", reading: { reading: general, evidence: "the paper", scoped: onFile } } : {})) }));
    if (!first.ok) throw new Error("pass failed");
    expect(first.symbols.find((v) => v.name === "\\Delta")!.reading).toEqual({ reading: general, evidence: "the paper", scoped: onFile });
    const main = toyCore().statements.find((s) => s.id === "thm:main")!.statement;
    const corrected = new Map([["thm:main", { printed: main, text: main.replace("With probability", "With probability at least") }]]);
    const regrade = async (reading: unknown) => {
      const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
      const logs: string[] = [];
      const res = await runSymbolPass(
        await passInput({ corrected, prior: first.symbols, confirmed: first.confirmed, log: (m) => logs.push(m), ask: fakeAsk(calls, (n) => (n === "\\Delta" ? ({ keep: false, ambiguity: "pinned", reading } as never) : {})) }),
      );
      if (!res.ok) throw new Error("pass failed");
      return { calls, logs, delta: res.symbols.find((v) => v.name === "\\Delta")!, metrics: res.metrics };
    };
    const k = await regrade({ reading: null, evidence: "the corrected theorem", scoped: [{ results: ["thm:main"], text: "$\\Delta$ is as corrected." }, { results: ["lem:aux"], text: null }] });
    // the prompt gives each result's id and shows the pieces on file
    expect(k.calls[0]!.prompt).toContain("Theorem~\\ref{thm:main} [thm:main] as corrected by a confirmed repair");
    expect(k.calls[0]!.prompt).toContain(`  reading (general part): ${general}\n  scoped [thm:main]: ${onFile[0]!.text}\n  scoped [lem:aux]: ${onFile[1]!.text}\n  evidence: the paper`);
    expect(k.calls).toHaveLength(1);
    expect(k.delta.reading).toEqual({ reading: general, evidence: "the corrected theorem", scoped: [{ results: ["thm:main"], text: "$\\Delta$ is as corrected." }, onFile[1]] });
    // refused: a tag that is no result using the symbol; a kept clause with nothing on file — retried, then set aside (the grade on file stands)
    for (const [scoped, why] of [[[{ results: ["ass:a"], text: "t" }], "is tagged with ass:a"], [[{ results: ["thm:other"], text: null }], "has no text"]] as const) {
      const bad = await regrade({ reading: null, evidence: "e", scoped });
      expect(bad.calls).toHaveLength(2);
      expect(bad.calls[1]!.prompt).toContain(why);
      expect(bad.metrics.set_aside?.map((x) => x.name)).toEqual(["\\Delta"]);
      expect(bad.delta.reading).toEqual({ reading: general, evidence: "the paper", scoped: onFile });
    }
  });

  it("a re-grade that mentions only the clause it changes keeps the others on file; an explicit drop removes one (logged with its reason)", async () => {
    const general = "$\\Delta$ is the random remainder.";
    const onFile = [{ results: ["thm:main"], text: "$\\Delta = n^{-1/2} R(\\hat{\\gamma})$." }, { results: ["lem:aux"], text: "$\\Delta \\geq 0$." }];
    const first = await runSymbolPass(await passInput({ ask: fakeAsk([], (n) => (n === "\\Delta" ? { ambiguity: "pinned", reading: { reading: general, evidence: "the paper", scoped: onFile } } : {})) }));
    if (!first.ok) throw new Error("pass failed");
    const main = toyCore().statements.find((s) => s.id === "thm:main")!.statement;
    const corrected = new Map([["thm:main", { printed: main, text: main.replace("With probability", "With probability at least") }]]);
    const regrade = async (scoped: unknown) => {
      const logs: string[] = [];
      const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
      const res = await runSymbolPass(await passInput({ corrected, prior: first.symbols, confirmed: first.confirmed, log: (m) => logs.push(m), ask: fakeAsk(calls, (n) => (n === "\\Delta" ? ({ keep: false, ambiguity: "pinned", reading: { reading: null, evidence: "e", scoped } } as never) : {})) }));
      if (!res.ok) throw new Error("pass failed");
      return { logs, calls, reading: res.symbols.find((v) => v.name === "\\Delta")!.reading! };
    };
    const one = await regrade([{ results: ["thm:main"], text: "$\\Delta$ is as corrected.", drop: null }]);
    expect(one.calls[0]!.prompt).toContain("every scoped clause on file stays as it is unless your reply lists it");
    expect(one.reading.scoped).toEqual([{ results: ["thm:main"], text: "$\\Delta$ is as corrected." }, onFile[1]]);
    expect((await regrade([])).reading.scoped).toEqual(onFile);
    const dropped = await regrade([{ results: ["lem:aux"], text: null, drop: "the lemma no longer bounds it" }]);
    expect(dropped.reading.scoped).toEqual([onFile[0]]);
    expect(dropped.logs.join("\n")).toContain("the scoped clause [lem:aux] on file is dropped — the lemma no longer bounds it");
  });

  it("a verdict on file with a clause tagged with a result that is gone is not carried: the symbol is graded afresh, shown the dead id and the blocks now split from the same result (a re-keyed block)", async () => {
    const block = (id: string, text: string) => ({ id, kind: "theorem", statement: text, depends_on: [], free_symbols: ["\\Delta"], proof_tex: "", status: "proved", split_from: "thm:main" });
    const withBlock = (id: string, text: string): Core => ({ ...toyCore(), statements: [...toyCore().statements, block(id, text) as never] });
    const general = "$\\Delta$ is the random remainder.";
    const tagged = (id: string) => [{ results: ["thm:main"], text: "$\\Delta$ is as printed." }, { results: [id], text: "$\\Delta$ is deterministic." }];
    const before = withBlock("thm:cor-fix-aaaa1111", "On the event $E$, $\\Delta \\leq 1$.");
    const first = await runSymbolPass(await passInput({ core: before, ask: fakeAsk([], (n) => (n === "\\Delta" ? { ambiguity: "pinned", reading: { reading: general, evidence: "the paper", scoped: tagged("thm:cor-fix-aaaa1111") } } : {})) }));
    if (!first.ok) throw new Error("pass failed");
    const on = first.symbols.find((v) => v.name === "\\Delta")!;
    expect(on.split_tags).toEqual({ "thm:cor-fix-aaaa1111": "thm:main" });
    // unchanged: carried, no call
    const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
    await runSymbolPass(await passInput({ core: before, prior: first.symbols, confirmed: first.confirmed, ask: fakeAsk(calls) }));
    expect(calls).toHaveLength(0);
    // the fixer rewords the block: a new id; the symbol's own basis does not move, the tag is dead
    const after = withBlock("thm:cor-fix-bbbb2222", "On the event $E$, $\\Delta \\leq 2$.");
    const logs: string[] = [];
    const run = async (scoped: unknown, keep = false) =>
      runSymbolPass(await passInput({ core: after, prior: first.symbols, confirmed: first.confirmed, log: (m) => logs.push(m), ask: fakeAsk(calls, (n) => (n === "\\Delta" ? ({ keep, ambiguity: "pinned", reading: { reading: null, evidence: "e", scoped } } as never) : {})) }));
    const retag = { results: ["thm:cor-fix-bbbb2222"], text: "$\\Delta$ is deterministic.", drop: null };
    const res = await run([retag, { results: ["thm:cor-fix-aaaa1111"], text: null, drop: "the block was stated again" }]);
    if (!res.ok) throw new Error("pass failed");
    expect(calls.map((c) => c.names)).toEqual([["\\Delta"]]);
    expect(calls[0]!.prompt).toContain("CLAUSES ON FILE TAGGED WITH A RESULT THAT IS GONE");
    expect(calls[0]!.prompt).toContain('the clause on file scoped [thm:cor-fix-aaaa1111] is tagged with thm:cor-fix-aaaa1111, no longer a result using the symbol — now split from the same result (Theorem~\\ref{thm:main}): thm:cor-fix-bbbb2222.');
    expect(calls[0]!.prompt).toContain("the result split from Theorem~\\ref{thm:main} (a repair states it apart; the paper does not print it) [thm:cor-fix-bbbb2222] as a confirmed repair states it");
    const now = res.symbols.find((v) => v.name === "\\Delta")!;
    // the dead clause is dropped as the reply says, the live one kept word for word, the new one in
    expect(now.reading!.scoped).toEqual([tagged("x")[0], { results: ["thm:cor-fix-bbbb2222"], text: "$\\Delta$ is deterministic." }]);
    expect(now.split_tags).toEqual({ "thm:cor-fix-bbbb2222": "thm:main" });
    expect(logs.join("\n")).toContain("verdict(s) with a scoped clause tagged with a result that is gone are graded afresh: \\Delta");
    // a reply that ignores the dead clause is refused — never a silent removal — and so is one that restates
    // a clause on file under other results without replacing or dropping it
    calls.length = 0;
    const ignored = await run([retag]);
    expect(ignored.ok && ignored.metrics.set_aside?.map((x) => x.name)).toEqual(["\\Delta"]);
    expect(calls[1]!.prompt).toContain("scoped clause [thm:cor-fix-aaaa1111] is tagged with thm:cor-fix-aaaa1111, not the id of a result using the symbol");
    calls.length = 0;
    await run([{ results: ["thm:main", "lem:aux"], text: "$\\Delta$ is as printed.", drop: null }, { results: ["thm:cor-fix-aaaa1111"], text: null, drop: "gone" }]);
    expect(calls[1]!.prompt).toContain("its new scoped clause [thm:main, lem:aux] and the clause on file [thm:main], which the reply does not list, would both hold in thm:main");
    // `keep: true` cannot keep a dead tag: refused, retried, then set aside
    calls.length = 0;
    const kept = await run([], true);
    expect(kept.ok && kept.metrics.set_aside?.map((x) => x.name)).toEqual(["\\Delta"]);
    expect(calls[1]!.prompt).toContain("is tagged with thm:cor-fix-aaaa1111, not the id of a result using the symbol");
  });

  it("a reading on file that does not compile drops its cached verdict: the symbol is graded afresh, alone", async () => {
    const tex = { runDir: await mkdtemp(path.join(os.tmpdir(), "sym-stale-")) };
    tmpDirs.push(tex.runDir);
    const first = await runSymbolPass(await passInput());
    expect(first.ok).toBe(true);
    if (!first.ok) return;
    const curly = "$\\Delta$ is the “oracle” remainder";
    const prior = first.symbols.map((v) => (v.name === "\\Delta" ? { ...v, ambiguity: "pinned" as const, reading: { reading: curly, evidence: "x" } } : v));
    const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
    const logs: string[] = [];
    const res = await runSymbolPass(await passInput({ prior, confirmed: first.confirmed, ask: fakeAsk(calls), tex, log: (m) => logs.push(m) }));
    if (!res.ok) throw new Error("pass failed");
    expect(calls.map((c) => c.kind)).toEqual(["symbol_shard"]);
    expect(calls[0]!.names).toEqual(["\\Delta"]);
    expect(res.symbols.find((v) => v.name === "\\Delta")).toMatchObject({ graded: "fresh", ambiguity: "ok", reading: null });
    expect(logs.some((l) => l.startsWith("symbol delta: 1 verdict(s) whose texts do not compile are graded afresh: \\Delta"))).toBe(true);
  });

  // The retry shows the model the text it rejected, verbatim, with the exact problem (CNS resume
  // 2026-09-26: the retry never showed the reading); past the retry a symbol is set aside and the
  // pass goes on — with no verdict on file it is left ungraded, else the verdict on file is kept.
  it("a symbol breaking the contract twice is set aside; the retry echoes the rejected reading; the others stand", async () => {
    const logs: string[] = [];
    const res = await runSymbolPass(await passInput({ ask: fakeAsk([], (n) => (n === "n" ? { meaning: "drift" } : {})), log: (m) => logs.push(m) }));
    expect(res.ok).toBe(true);
    if (!res.ok) return;
    expect(res.symbols.map((v) => v.name)).not.toContain("n"); // no verdict on file: left ungraded
    expect(res.symbols).toHaveLength(5);
    expect(res.confirmed.n).toBeUndefined(); // graded afresh next pass
    expect(res.metrics.set_aside?.map((x) => x.name)).toEqual(["n"]);
    expect(logs.some((l) => l.startsWith("symbol n: its new grading broke the contract twice — set aside (no verdict on file"))).toBe(true);

    const bad = "the drift term $\\\\Delta_n$ of the estimator"; // a doubled backslash: exact
    const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
    logs.length = 0;
    const pin = (n: string): Partial<V15SymbolVerdict> => (n === "\\Delta" ? { ambiguity: "pinned", reading: { reading: bad, evidence: "x" }, detail: "d" } : {});
    const first = await runSymbolPass(await passInput());
    if (!first.ok) throw new Error("pass failed");
    const prior = first.symbols.map((v) => (v.name === "\\Delta" ? { ...v, detail: "the verdict on file" } : v));
    const res2 = await runSymbolPass(await passInput({ prior, ask: fakeAsk(calls, pin), log: (m) => logs.push(m) }));
    expect(calls).toHaveLength(2);
    const retry = calls[1]!.prompt;
    expect(retry).toContain('symbol "\\Delta", your previous text, verbatim:');
    expect(retry).toContain(`  reading: ${bad}`);
    expect(retry).toContain("doubled backslash");
    expect(res2.ok).toBe(true);
    if (!res2.ok) return;
    const d = res2.symbols.find((v) => v.name === "\\Delta")!;
    expect(d).toMatchObject({ detail: "the verdict on file", graded: "carried" });
    expect(res2.confirmed["\\Delta"]).toBeUndefined();
    expect(Object.keys(res2.confirmed)).toHaveLength(5);
    expect(logs.some((l) => l.startsWith("symbol \\Delta: its new grading broke the contract twice — set aside (its verdict on file kept"))).toBe(true);
  });
});

describe("the symbol pass: what moves a symbol's basis (the re-grade cascade)", () => {
  it("a corrected result using the symbol re-grades it only when the correction changed a sentence the symbol is in; the introducing result always", () => {
    const c = toyCore();
    const px = paperIndex(FLAT, null, null);
    const slices = allSymbolSlices(px, c);
    const other = c.statements.find((s) => s.id === "thm:other")!.statement;
    const main = c.statements.find((s) => s.id === "thm:main")!.statement;
    // thm:other uses \hat{\theta}; a sentence added elsewhere in it leaves the symbol's reading alone.
    const elsewhere = new Map([["thm:other", { printed: other, text: `${other} Moreover, $W$ is bounded.` }]]);
    expect(correctionTouchesSymbol("\\hat{\\theta}", elsewhere.get("thm:other")!)).toBe(false);
    expect(correctedSources(px, c, slices.get("\\hat{\\theta}"), elsewhere)).toEqual([]);
    // … but the sentence it is in reworded re-grades it.
    const touched = new Map([["thm:other", { printed: other, text: other.replace("is consistent", "is consistent at rate $n^{-1/2}$") }]]);
    expect(correctionTouchesSymbol("\\hat{\\theta}", touched.get("thm:other")!)).toBe(true);
    expect(correctedSources(px, c, slices.get("\\hat{\\theta}"), touched)).toEqual(["thm:other"]);
    // \Delta is introduced inside thm:main: any correction of thm:main is in its basis.
    const intro = new Map([["thm:main", { printed: main, text: main.replace("With probability", "With probability at least") }]]);
    expect(correctedSources(px, c, slices.get("\\Delta"), intro)).toEqual(["thm:main"]);
  });

  it("of a corrected statement a symbol reads the sentences naming it: an edit to another sentence re-grades it not, an edit to one of its own does; the prompt shows exactly those sentences", async () => {
    const main = toyCore().statements.find((s) => s.id === "thm:main")!.statement;
    const v1 = { printed: main, text: main.replace("With probability", "With probability at least") + " Moreover, $W$ is bounded." };
    // \Delta is introduced in thm:main, so the corrected theorem is one of its sources whatever changed.
    // The core graded is the patched one: thm:main's statement is its corrected text.
    const coreWith = (text: string): Core => {
      const c = toyCore();
      c.statements.find((st) => st.id === "thm:main")!.statement = text;
      return c;
    };
    const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
    const first = await runSymbolPass(await passInput({ core: coreWith(v1.text), corrected: new Map([["thm:main", v1]]), ask: fakeAsk(calls) }));
    if (!first.ok) throw new Error("pass failed");
    const shown = calls.find((c) => c.names.includes("\\Delta"))!.prompt;
    const named = correctedReading("\\Delta", v1);
    expect(named.whole).toBe(false);
    expect(named.sentences.length).toBeGreaterThan(0);
    expect(named.sentences.every((x) => x.includes("\\Delta"))).toBe(true);
    expect(shown).toContain(`Its sentences that name this symbol now read:\n\n${named.sentences.map((x) => `- ${x}`).join("\n")}`);
    // … and no other sentence of the corrected statement, under that symbol.
    const block = shown.slice(shown.indexOf("### \\Delta\n")).split(/\n\n(?=### |=== )/)[0]!;
    expect(block).toContain("Corrected by a repair: thm:main");
    expect(block).not.toContain("Moreover, $W$ is bounded.");
    const regraded = async (text: string): Promise<string[]> => {
      const again: Array<{ kind: string; names: string[]; prompt: string }> = [];
      const res = await runSymbolPass(await passInput({ core: coreWith(text), corrected: new Map([["thm:main", { printed: main, text }]]), prior: first.symbols, confirmed: first.confirmed, ask: fakeAsk(again) }));
      if (!res.ok) throw new Error("pass failed");
      return [...new Set(again.flatMap((c) => c.names))].sort();
    };
    // The sentence about W reworded: W is re-graded, \Delta (named in other sentences only) is not.
    expect(await regraded(v1.text.replace("$W$ is bounded", "$W$ is bounded by one"))).toEqual(["W"]);
    // A sentence naming \Delta reworded: \Delta is re-graded.
    expect(await regraded(v1.text.replace("$\\Delta_h$ is unrelated", "$\\Delta_h$ is unrelated to $\\Delta$"))).toContain("\\Delta");
    expect(await regraded(v1.text)).toEqual([]);
  });

  it("a symbol the matcher finds in neither text reads the corrected statement whole; one the correction removed reads that it is gone", () => {
    const c = { printed: "The bound holds for $x$.", text: "The bound holds for $x$ and $y$." };
    expect(correctedReading("\\zeta", c)).toEqual({ sentences: [c.text], whole: true });
    expect(correctedBasisText("thm:a", correctedReading("\\zeta", c))).toBe(`thm:a\n${c.text}`);
    expect(correctedReading("x", { printed: c.printed, text: "The bound holds." })).toEqual({ sentences: [], whole: false });
    expect(correctedBasisText("thm:a", correctedReading("x", c))).toBe("thm:a\nTheboundholdsfor$x$and$y$.");
  });

  it("shown = hashed: the entry's other fields, an entry it refers to and the settings re-grade a symbol; a key from before they were hashed is re-keyed from a complete pass only", async () => {
    const first = await runSymbolPass(await passInput());
    if (!first.ok) throw new Error("pass failed");
    const regraded = async (core: Core, over: Partial<Parameters<typeof passInput>[0] & object> = {}) => {
      const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
      const res = await runSymbolPass(await passInput({ core, prior: first.symbols, confirmed: first.confirmed, ask: fakeAsk(calls), ...over }));
      return { res, names: [...new Set(calls.flatMap((c) => c.names))].sort(), prompt: calls.map((c) => c.prompt).join("\n") };
    };
    // a field of the entry the earlier key did not read: the symbol's call prints it
    for (const [field, value] of [["space", "\\mathbb{R}^d"], ["sig", "W \\to \\mathbb{R}"], ["role", "nuisance"]] as const) {
      const core = toyCore();
      (core.symbols.find((x) => x.name === "W") as unknown as Record<string, string>)[field] = value;
      const r = await regraded(core);
      // W, and \hat{\gamma}, which refers to it and is shown its entry
      expect(r.names).toEqual(["W", "\\hat{\\gamma}"]);
      expect(r.prompt).toContain(JSON.stringify(value).slice(1, -1));
    }
    // the settings are printed in every symbol call, but a symbol's key reads the settings it can rest
    // on (`settingsNaming`): one naming no result is global and re-grades every symbol; one of a
    // result re-grades the symbols that result uses, and the symbols it names
    const settings = toyCore();
    settings.sampling_model = { ...(settings.sampling_model ?? {}), design: "the sample is drawn without replacement" } as never;
    const all = await regraded(settings);
    expect(all.names).toHaveLength(first.symbols.length);
    expect(all.prompt).toContain("the sample is drawn without replacement");
    settings.sampling_model = { ...(toyCore().sampling_model ?? {}), design: "the sample is drawn without replacement. Used by lem:aux." } as never;
    expect((await regraded(settings)).names).toEqual(["\\Delta"]);
    settings.sampling_model = { ...(toyCore().sampling_model ?? {}), design: "the sample of $W$ is drawn without replacement. Used by lem:aux." } as never;
    expect((await regraded(settings)).names).toEqual(["W", "\\Delta"]);
    // the transition: a verdict keyed before any of this was hashed
    const px = paperIndex(FLAT, null, null);
    const slices = allSymbolSlices(px, toyCore());
    const now = first.confirmed;
    const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
    const prompts = await runSymbolPass(await passInput({ ask: fakeAsk(calls) }));
    if (!prompts.ok) throw new Error("pass failed");
    const describes = (name: string): string => calls.map((c) => c.prompt).join("\n").split("\n").find((l) => l.startsWith(`- ${name}: `))!;
    const unshown = Object.fromEntries(toyCore().symbols.map((x) => [x.name, symbolBasis(x, slices.get(x.name)?.intro, [`describes\n${describes(x.name)}`])]));
    expect(unshown.W).not.toBe(now.W);
    // … a verdict keyed with every setting (to 2026-10-13): carried, of a complete pass, and re-keyed
    const legacyKeys = Object.fromEntries(toyCore().symbols.map((x) => [x.name, symbolBasis(x, slices.get(x.name)?.intro, [`describes\n${describes(x.name)}`], symbolShownBasis({ core: toyCore(), slices }, x.name, true))]));
    expect(legacyKeys.W).not.toBe(now.W);
    const legacyCarry = await regraded(toyCore(), { prior: first.symbols.map((v) => ({ ...v, basis: legacyKeys[v.name]! })), confirmed: legacyKeys, priorComplete: true });
    expect(legacyCarry.names).toEqual([]);
    expect(legacyCarry.res.ok && legacyCarry.res.confirmed).toEqual(now);
    // (… of a paused pass too: that key hashes a superset of the one above)
    expect((await regraded(toyCore(), { prior: first.symbols.map((v) => ({ ...v, basis: legacyKeys[v.name]! })), confirmed: legacyKeys })).names).toEqual([]);
    const prior = first.symbols.map((v) => ({ ...v, basis: unshown[v.name]! }));
    const complete = await regraded(toyCore(), { prior, confirmed: unshown, priorComplete: true });
    expect(complete.names).toEqual([]);
    expect(complete.res.ok && complete.res.confirmed).toEqual(now);
    // … of a paused or halted pass, graded afresh: nothing says what it was shown stood still
    expect((await regraded(toyCore(), { prior, confirmed: unshown })).names).toHaveLength(first.symbols.length);
    // … and never when what the earlier key did read has moved
    const moved = toyCore();
    moved.symbols.find((x) => x.name === "W")!.type = "another type";
    // (\hat{\gamma}'s earlier key never read W's entry: of a complete pass it is carried as it stands)
    expect((await regraded(moved, { prior, confirmed: unshown, priorComplete: true })).names).toEqual(["W"]);
  });

  it("transition: a verdict recorded on the earlier basis (the corrected statement whole) is carried while that basis holds and re-keyed, with no call; one whose earlier basis moved is graded afresh", async () => {
    const main = toyCore().statements.find((s) => s.id === "thm:main")!.statement;
    const v1 = { printed: main, text: main.replace("With probability", "With probability at least") + " Moreover, $W$ is bounded." };
    const corrected = new Map([["thm:main", v1]]);
    const now = await runSymbolPass(await passInput({ corrected }));
    if (!now.ok) throw new Error("pass failed");
    // The run as the earlier code left it: every symbol keyed on its sources' whole corrected text.
    const px = paperIndex(FLAT, null, null);
    const slices = allSymbolSlices(px, toyCore());
    const earlier = (name: string): string =>
      symbolBasis(toyCore().symbols.find((x) => x.name === name)!, slices.get(name)?.intro, correctedSources(px, toyCore(), slices.get(name), corrected).map((id) => `${id}\n${corrected.get(id)!.text}`));
    const confirmed = Object.fromEntries(now.symbols.map((v) => [v.name, earlier(v.name)]));
    const prior = now.symbols.map((v) => ({ ...v, basis: confirmed[v.name]! }));
    expect(confirmed["\\Delta"]).not.toBe(now.confirmed["\\Delta"]);
    const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
    // (of a complete pass; a paused or halted one grades every verdict on an earlier basis afresh)
    const paused: Array<{ kind: string; names: string[]; prompt: string }> = [];
    await runSymbolPass(await passInput({ corrected, prior, confirmed, ask: fakeAsk(paused) }));
    expect(new Set(paused.flatMap((c) => c.names)).size).toBe(now.symbols.length);
    const next = await runSymbolPass(await passInput({ corrected, prior, confirmed, priorComplete: true, ask: fakeAsk(calls) }));
    if (!next.ok) throw new Error("pass failed");
    expect(calls).toHaveLength(0);
    expect(next.symbols.every((v) => v.graded === "carried")).toBe(true);
    expect(next.confirmed).toEqual(now.confirmed);
    expect(next.symbols.map((v) => v.basis)).toEqual(now.symbols.map((v) => v.basis));
    // The statement changed since the earlier basis was recorded (a sentence naming \Delta): afresh.
    const moved = new Map([["thm:main", { printed: main, text: v1.text.replace("$\\Delta_h$ is unrelated", "$\\Delta_h$ is unrelated to $\\Delta$") }]]);
    await runSymbolPass(await passInput({ corrected: moved, prior, confirmed, ask: fakeAsk(calls) }));
    expect(calls.flatMap((c) => c.names)).toContain("\\Delta");
  });

  it("a reading that names a result is read from that result whole: a sentence of it not naming the symbol re-grades the symbol; a reading that does not name it is not re-graded; the transition keys carry", async () => {
    const other = toyCore().statements.find((s) => s.id === "thm:other")!.statement;
    // thm:other is corrected in a sentence naming \hat{\theta} (so it is a source of that symbol), plus one naming nothing.
    const v1 = { printed: other, text: other.replace("is consistent", "is consistent at rate $n^{-1/2}$") + " The sample is i.i.d." };
    const coreWith = (text: string): Core => {
      const c = toyCore();
      c.statements.find((st) => st.id === "thm:other")!.statement = text;
      return c;
    };
    const about = { ambiguity: "pinned" as const, reading: { reading: "$\\hat{\\theta}$ is the estimator.", evidence: "Theorem~\\ref{thm:other} states i.i.d. sampling." } };
    const plain = { ambiguity: "pinned" as const, reading: { reading: "$n$ is the number of observations.", evidence: "the setup" } };
    const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
    const first = await runSymbolPass(await passInput({ core: coreWith(v1.text), corrected: new Map([["thm:other", v1]]), ask: fakeAsk(calls, (n) => (n === "\\hat{\\theta}" ? about : n === "n" ? plain : {})) }));
    if (!first.ok) throw new Error("pass failed");
    expect(resultsNamedBy(about.reading, toyCore().statements)).toEqual(new Set(["thm:other"]));
    expect(resultsNamedBy({ reading: "As in lem:aux.", evidence: "", scoped: [{ results: ["thm:main"], text: "t" }] }, toyCore().statements)).toEqual(new Set(["thm:main", "lem:aux"]));
    const regraded = async (text: string, prior = first.symbols, confirmed = first.confirmed): Promise<{ names: string[]; prompt: string }> => {
      const again: Array<{ kind: string; names: string[]; prompt: string }> = [];
      const res = await runSymbolPass(await passInput({ core: coreWith(text), corrected: new Map([["thm:other", { printed: other, text }]]), prior, confirmed, ask: fakeAsk(again, (n) => (n === "\\hat{\\theta}" ? about : n === "n" ? plain : {})) }));
      if (!res.ok) throw new Error("pass failed");
      return { names: [...new Set(again.flatMap((c) => c.names))].sort(), prompt: again.map((c) => c.prompt).join("\n") };
    };
    expect((await regraded(v1.text)).names).toEqual([]);
    // The sentence naming no symbol changes: the symbol whose reading names thm:other is re-graded,
    // shown the statement whole; n (named in another sentence, its reading about no result) is not.
    // (\Delta reaches thm:other through a hypothesis only: it cannot be placed there, so any change counts.)
    const iid = v1.text.replace("The sample is i.i.d.", "The sample is independent, not identically distributed.");
    const r = await regraded(iid);
    expect(r.names).toEqual(["\\Delta", "\\hat{\\theta}"]);
    expect(correctedReading("n", { printed: other, text: iid })).toEqual(correctedReading("n", v1));
    expect(r.prompt).toContain(`Corrected by a repair: thm:other, a statement this symbol is read from — the corrected statement replaces the printed one, so the reading is the one it uses. It now reads:\n\n${iid}`);
    // The transition: verdicts keyed as the earlier code keyed them (whole sources; then the sentences
    // naming the whole symbol) are carried on unchanged files with no call, and re-keyed.
    const px = paperIndex(FLAT, null, null);
    const slices = allSymbolSlices(px, coreWith(v1.text));
    const corrected = new Map([["thm:other", v1]]);
    const sym = (name: string) => toyCore().symbols.find((x) => x.name === name)!;
    for (const key of [
      (name: string) => symbolBasis(sym(name), slices.get(name)?.intro, correctedSources(px, coreWith(v1.text), slices.get(name), corrected, new Set(), true).map((id) => `${id}\n${v1.text}`)),
      (name: string) => symbolBasis(sym(name), slices.get(name)?.intro, correctedSources(px, coreWith(v1.text), slices.get(name), corrected, new Set(), true).map((id) => correctedBasisText(id, correctedReading(name, v1, false, true)))),
    ]) {
      const confirmed = Object.fromEntries(first.symbols.map((v) => [v.name, key(v.name)]));
      const prior = first.symbols.map((v) => ({ ...v, basis: confirmed[v.name]! }));
      expect(confirmed["\\hat{\\theta}"]).not.toBe(first.confirmed["\\hat{\\theta}"]);
      const again: Array<{ kind: string; names: string[]; prompt: string }> = [];
      const res = await runSymbolPass(await passInput({ core: coreWith(v1.text), corrected, prior, confirmed, ask: fakeAsk(again, (n) => (n === "\\hat{\\theta}" ? about : {})) }));
      // … but of a pass on file that was not complete (a pause, a halt) every verdict on an earlier
      // key is graded afresh, once: no earlier key covers all its referee was shown
      expect(new Set(again.flatMap((c) => c.names)).size).toBe(first.symbols.length);
      // a COMPLETE pass is carried over as it stands: no call at all, every verdict re-keyed
      const whole: Array<{ kind: string; names: string[]; prompt: string }> = [];
      const done = await runSymbolPass(await passInput({ core: coreWith(v1.text), corrected, prior, confirmed, priorComplete: true, ask: fakeAsk(whole) }));
      expect(whole).toHaveLength(0);
      expect(done.ok && done.confirmed).toEqual(first.confirmed);
      expect(priorPassComplete({ paused: null }, {})).toBe(true);
      expect(priorPassComplete(null, {})).toBe(true);
      expect(priorPassComplete({ paused: { level: "L1", ids: [], ungraded: [] } }, {})).toBe(false);
      expect(priorPassComplete({ paused: null }, { level_pause: {} })).toBe(false);
      expect(res.ok && res.confirmed).toEqual(first.confirmed);
      if (!res.ok) throw new Error("pass failed");
      expect((await regraded(v1.text, res.symbols, res.confirmed)).names).toEqual([]);
    }
    // a cache recorded before the introducing passage was read by its words (2026-10-06): its key is the passage verbatim
    const noRepair = await runSymbolPass(await passInput());
    if (!noRepair.ok) throw new Error("pass failed");
    const s0 = allSymbolSlices(px, toyCore());
    const rawKey = (name: string) => createHash("sha256").update(`${symbolSourceHash(sym(name))}\n${s0.get(name)?.intro?.text ?? ""}`).digest("hex");
    const confirmed = Object.fromEntries(noRepair.symbols.map((v) => [v.name, rawKey(v.name)]));
    const old: Array<{ kind: string; names: string[]; prompt: string }> = [];
    const carried = await runSymbolPass(await passInput({ prior: noRepair.symbols.map((v) => ({ ...v, basis: confirmed[v.name]! })), confirmed, priorComplete: true, ask: fakeAsk(old) }));
    expect(old).toHaveLength(0);
    expect(carried.ok && carried.confirmed).toEqual(noRepair.confirmed);
    // … and, earlier still, with every corrected statement using the symbol whole (also one whose correction named it nowhere)
    const elsewhere = new Map([["thm:other", { printed: other, text: `${other} The sample is i.i.d.` }]]);
    const now = await runSymbolPass(await passInput({ core: coreWith(elsewhere.get("thm:other")!.text), corrected: elsewhere }));
    if (!now.ok) throw new Error("pass failed");
    const s1 = allSymbolSlices(px, coreWith(elsewhere.get("thm:other")!.text));
    const oldest = (name: string) => createHash("sha256").update(`${symbolSourceHash(sym(name))}\n${s1.get(name)?.intro?.text ?? ""}${symbolUsers(toyCore(), name).includes("thm:other") ? `\nthm:other\n${elsewhere.get("thm:other")!.text}` : ""}`).digest("hex");
    const keys = Object.fromEntries(now.symbols.map((v) => [v.name, oldest(v.name)]));
    expect(correctedSources(px, coreWith(elsewhere.get("thm:other")!.text), s1.get("\\hat{\\theta}"), elsewhere, new Set(), true)).toEqual([]);
    const oldestCalls: Array<{ kind: string; names: string[]; prompt: string }> = [];
    await runSymbolPass(await passInput({ core: coreWith(elsewhere.get("thm:other")!.text), corrected: elsewhere, prior: now.symbols.map((v) => ({ ...v, basis: keys[v.name]! })), confirmed: keys, priorComplete: true, ask: fakeAsk(oldestCalls) }));
    expect(oldestCalls).toHaveLength(0);
  });

  it("a reading names a result by its \\ref, its id, a clause's tag or the \\ref of the section that prints it; a named result names the blocks split from it; a \\ref the paper holds nowhere is unresolved", () => {
    const flat = ["\\section{Setup}\\label{sec:setup}", "Text.", "\\section{Main results}\\label{sec:main}", "\\begin{theorem}\\label{thm:main}", "A.", "\\end{theorem}", "\\subsection{More}", "\\begin{lemma}\\label{lem:aux}", "B.", "\\end{lemma}", "\\section{Appendix}\\label{sec:app}", "\\begin{theorem}\\label{thm:other}", "C.", "\\end{theorem}"].join("\n");
    const px = paperIndex(flat, null, null);
    const statements = [...toyCore().statements, { id: "thm:cor-fix-1", split_from: "thm:other" }, { id: "thm:cor-fix-2", split_from: "lem:aux" }] as Array<{ id: string; split_from?: string; tex_locator?: { label?: string | null } | null }>;
    const r = (reading: string, evidence = "") => ({ reading, evidence });
    expect(sectionRange(px, "sec:main")).toEqual([3, 10]);
    expect(sectionRange(px, "thm:main")).toBeNull();
    expect([...resultsNamedBy(r("As in the results of Section~\\ref{sec:main}."), statements, px)].sort()).toEqual(["lem:aux", "thm:cor-fix-2", "thm:main"]);
    expect([...resultsNamedBy(r("As in the results of Section~\\ref{sec:main}."), statements)]).toEqual([]);
    expect([...resultsNamedBy(r("x", "the result split from Theorem~\\ref{thm:other}"), statements, px)].sort()).toEqual(["thm:cor-fix-1", "thm:other"]);
    expect(unresolvedRefs(r("See Section~\\ref{sec:gone} and Section~\\ref{sec:app}."), statements, px)).toEqual(["sec:gone"]);
    expect(unresolvedRefs(r("See Theorem~\\ref{thm:main}."), statements, px)).toEqual([]);
  });

  it("a weakened repair demoted to a suggestion withdraws the symbols that read it: one named in a sentence it changed, and one whose reading names the result", () => {
    const main = toyCore().statements.find((s) => s.id === "thm:main")!.statement;
    const core = toyCore();
    core.statements.find((s) => s.id === "thm:main")!.free_symbols!.push("W");
    const corrected = new Map([["thm:main", { printed: main, text: `${main} Moreover, $W$ is bounded.` }]]);
    const verdict = (name: string, reading: string) => sym(name, { ambiguity: "pinned", reading: { reading, evidence: "the paper" } });
    const verdicts = [verdict("n", "$n$ is the sample size, as Theorem~\\ref{thm:main} uses it."), verdict("\\theta_0", "$\\theta_0$ is the target.")];
    // W: a sentence naming it changed; n: its reading names the demoted theorem; \theta_0: neither
    expect(symbolsReadingDemoted(core, new Set(["thm:main"]), corrected, verdicts)).toEqual(["W", "n"]);
    expect(symbolsReadingDemoted(core, new Set(["thm:other"]), corrected, verdicts)).toEqual([]);
  });

  it("a sentence holding the symbol decorated or inside a compound names it; a lead-in travels with the display it introduces", () => {
    const h = symbolPattern("h");
    const M = symbolPattern("\\bar{M}");
    expect(symbolAppears("the bound $m_h \\leq 1$", h)).toBe(true);
    expect(mentionsSymbol("the bound $m_h \\leq 1$", h)).toBe(false);
    expect(symbolAppears("$\\ell_{h}$ which holds", h)).toBe(true);
    expect(symbolAppears("which holds then", h)).toBe(false);
    expect(symbolAppears("$\\bar M_h \\geq 0$", M)).toBe(true);
    expect(symbolAppears("$M_h \\geq 0$", M)).toBe(false);
    const text = "Fix $\\epsilon$. For every bandwidth $h$:\n\\[ |\\hat\\theta - \\theta_0| \\leq \\Delta. \\]\nThen $\\ell_h \\to 0$; the rest is standard.";
    expect(sentencesOf(text)).toEqual(["Fix $\\epsilon$.", "For every bandwidth $h$: \\[ |\\hat\\theta - \\theta_0| \\leq \\Delta.", "\\]\nThen $\\ell_h \\to 0$;", "the rest is standard."]);
    // \Delta is read with the quantifier that introduces its display; h also from the sentence that only decorates it
    expect(sentencesNaming(text, symbolPattern("\\Delta"))).toEqual(["For every bandwidth $h$: \\[ |\\hat\\theta - \\theta_0| \\leq \\Delta."]);
    expect(sentencesNaming(text, h)).toEqual(["For every bandwidth $h$: \\[ |\\hat\\theta - \\theta_0| \\leq \\Delta.", "\\]\nThen $\\ell_h \\to 0$;"]);
    expect(sentencesOf("We have;\n\\[ x \\]\nand so on.")).toEqual(["We have; \\[ x \\]\nand so on."]);
    // a correction of the decorated sentence touches the symbol
    expect(correctionTouchesSymbol("h", { printed: "Then $\\ell_h \\to 0$.", text: "Then $\\ell_h \\to 1$." })).toBe(true);
    expect(correctionTouchesSymbol("h", { printed: "Then $\\ell_h \\to 0$.", text: "Then $\\ell_h \\to 1$." }, true)).toBe(true); // legacy: unplaceable, any change counts
    expect(correctedReading("h", { printed: "Then $\\ell_h \\to 0$. Also $x$.", text: "Then $\\ell_h \\to 1$. Also $y$." })).toEqual({ sentences: ["Then $\\ell_h \\to 1$."], whole: false });
  });

  it("shown = hashed: what a symbol's prompt shows of its corrected sources and of the results it is used in is what its basis reads — a new pending suggestion, a block a repair states apart or its text re-grade the symbol", async () => {
    const main = toyCore().statements.find((s) => s.id === "thm:main")!.statement;
    const v1 = { printed: main, text: main.replace("With probability", "With probability at least") + " Moreover, $W$ is bounded." };
    const block = (text: string) => ({ id: "thm:cor-fix-aaaa1111", kind: "theorem", statement: text, depends_on: [], free_symbols: ["\\Delta"], proof_tex: "", status: "proved", split_from: "thm:main" });
    const coreWith = (blockText: string | null): Core => {
      const c = toyCore();
      c.statements.find((st) => st.id === "thm:main")!.statement = v1.text;
      if (blockText !== null) c.statements.push(block(blockText) as never);
      return c;
    };
    const corrected = new Map([["thm:main", v1]]);
    const run = async (over: Partial<SymbolPassInput>, prior?: Extract<Awaited<ReturnType<typeof runSymbolPass>>, { ok: true }>) => {
      const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
      const res = await runSymbolPass(await passInput({ core: coreWith(null), corrected, ...(prior ? { prior: prior.symbols, confirmed: prior.confirmed } : {}), ...over, ask: fakeAsk(calls) }));
      if (!res.ok) throw new Error("pass failed");
      return { res, calls, names: [...new Set(calls.flatMap((c) => c.names))].sort() };
    };
    const first = await run({});
    // every piece a basis hashes is in the prompt that graded the symbol: the sentences read of each source, and its line
    const px = paperIndex(FLAT, null, null);
    const slices = allSymbolSlices(px, coreWith(null));
    const squeeze = (t: string): string => t.replace(/\s+/g, "");
    for (const x of coreWith(null).symbols) {
      const prompt = first.calls.find((c) => c.names.includes(x.name))!.prompt;
      const line = prompt.split("\n").find((l) => l.startsWith(`- ${x.name}: `) && l.includes("["))!;
      const reads = correctedSources(px, coreWith(null), slices.get(x.name), corrected).map((id) => ({ id, ...correctedReading(x.name, corrected.get(id)!) }));
      for (const r of reads) for (const s of r.sentences) expect(squeeze(prompt)).toContain(squeeze(s));
      expect(first.res.confirmed[x.name]).toBe(symbolBasis(x, slices.get(x.name)?.intro, [...reads.map((r) => correctedBasisText(r.id, r)), `describes\n${line}`], symbolShownBasis({ core: coreWith(null), slices }, x.name)));
    }
    expect((await run({}, first.res)).names).toEqual([]);
    // a suggestion now pends on thm:other: the symbols it uses are shown it "AS PRINTED" — re-graded
    const st = toyCore().statements.find((s) => s.id === "thm:other")!;
    expect((await run({ pending: [{ node: "thm:other", label: "thm:other", kind: "Theorem", statement: st }] }, first.res)).names).toEqual(["\\Delta", "\\hat{\\theta}"]);
    // a repair states a block apart: the symbols it uses are re-graded, shown its text; then on any change of it
    const b1 = await run({ core: coreWith("On the event $E$, $\\Delta \\leq 1$.") }, first.res);
    expect(b1.names).toEqual(["\\Delta"]);
    expect(b1.calls[0]!.prompt).toContain("Corrected by a repair: thm:cor-fix-aaaa1111");
    expect(b1.calls[0]!.prompt).toContain("- On the event $E$, $\\Delta \\leq 1$.");
    expect((await run({ core: coreWith("On the event $E$, $\\Delta \\leq 1$.") }, b1.res)).names).toEqual([]);
    expect((await run({ core: coreWith("On the event $E$, $\\Delta \\leq 2$.") }, b1.res)).names).toEqual(["\\Delta"]);
  });

  it("the basis reads the introducing passage's words: the clipping marker's line numbers and whitespace move nothing", () => {
    const x = toyCore().symbols[0]!;
    const a = symbolBasis(x, { text: "Let $W$ denote the data;\nthe sample is split.\n[… the paragraph runs over flat.tex lines 3–9 …]" });
    const b = symbolBasis(x, { text: "Let $W$ denote the data;  the sample is split.\n[… the paragraph runs over flat.tex lines 5–11 …]" });
    expect(a).toBe(b);
    expect(symbolBasis(x, { text: "Let $W$ denote the sample." })).not.toBe(a);
    expect(symbolBasis(x, "Let $W$ denote the data; the sample is split.")).toBe(a);
  });

  it("an unresolvable verdict on file is carried word for word while its basis stands; once it moved the symbol is graded afresh, the old grade not offered under GRADES ON FILE", async () => {
    const first = await runSymbolPass(await passInput());
    if (!first.ok) throw new Error("pass failed");
    const prior = first.symbols.map((v) => (v.name === "\\Delta" ? { ...v, ambiguity: "unresolvable" as const, reading: null, detail: "two readings" } : v));
    const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
    const same = await runSymbolPass(await passInput({ prior, confirmed: first.confirmed, ask: fakeAsk(calls) }));
    if (!same.ok) throw new Error("pass failed");
    // (its line is in the basis of every node listing the symbol: re-asking would reword it and re-grade them each pass)
    expect(calls).toHaveLength(0);
    expect(same.symbols.find((v) => v.name === "\\Delta")).toMatchObject({ graded: "carried", ambiguity: "unresolvable", detail: "two readings" });
    const moved = toyCore();
    moved.symbols.find((x) => x.name === "\\Delta")!.type = "another bound";
    const res = await runSymbolPass(await passInput({ core: moved, prior, confirmed: first.confirmed, ask: fakeAsk(calls) }));
    if (!res.ok) throw new Error("pass failed");
    expect(calls.flatMap((c) => c.names)).toEqual(["\\Delta"]);
    expect(calls[0]!.prompt).not.toContain("GRADES ON FILE");
    expect(res.symbols.find((v) => v.name === "\\Delta")).toMatchObject({ graded: "fresh", ambiguity: "ok" });
  });

  it("the symbol prompt carries symbols.txt's own conventions list, not the referee brief's statement-level checklist", async () => {
    const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
    await runSymbolPass(await passInput({ ask: fakeAsk(calls) }));
    expect(calls[0]!.prompt).not.toContain("CONVENTIONS CHECKLIST");
    expect(calls[0]!.prompt).not.toContain("CONVENTIONS TO SETTLE.");
    expect(calls[0]!.prompt).toContain("AMBIGUITY — the conventions that live at symbol level");
  });

  it("a reply that fails the schema is a contract violation: retried once with the schema's complaint; twice, every symbol of the call is set aside and the pass goes on", async () => {
    const calls: Array<{ kind: string; names: string[]; prompt: string }> = [];
    const logs: string[] = [];
    let n = 0;
    const flaky = async (c: { kind: string; nodes: string[]; prompt: string }): Promise<unknown> => {
      calls.push({ kind: c.kind, names: c.nodes, prompt: c.prompt });
      n += 1;
      return n === 1 ? { summary: "s", symbols: "not a list" } : { summary: "s", symbols: c.nodes.map((x) => okSymbol(x)) };
    };
    const res = await runSymbolPass(await passInput({ ask: flaky, log: (m) => logs.push(m) }));
    expect(res.ok).toBe(true);
    if (!res.ok) return;
    expect(calls).toHaveLength(2);
    expect(calls[1]!.prompt).toContain("=== CONTRACT VIOLATIONS IN YOUR PREVIOUS REPLY ===");
    expect(calls[1]!.prompt).toContain("does not fit the output schema: symbols: ");
    expect(res.symbols).toHaveLength(6);
    expect(res.metrics.calls.map((c) => c.tag)).toEqual(["symbols_1", "symbols_1_retry"]);
    const always = async (): Promise<unknown> => ({ summary: "s", symbols: "not a list" });
    const res2 = await runSymbolPass(await passInput({ ask: always, log: (m) => logs.push(m) }));
    expect(res2.ok).toBe(true);
    if (!res2.ok) return;
    expect(res2.symbols).toHaveLength(0);
    expect(res2.metrics.set_aside?.map((x) => x.name).sort()).toEqual(toyCore().symbols.map((x) => x.name).sort());
    expect(logs.some((l) => l.includes("its reply did not parse twice"))).toBe(true);
  });
});

// ---------------------------------------------------------------------------------------------
// The core graph: fixes and pins
// ---------------------------------------------------------------------------------------------

describe("symbol fixes and pins in the core", () => {
  const core = toyCore();

  it("a pinned symbol reading is the symbol's def in the table, never an assumption (2026-09-30)", () => {
    expect(symbolUsers(core, "\\Delta").sort()).toEqual(["lem:aux", "thm:main", "thm:other"]);
    const pin = sym("\\Delta", { ambiguity: "pinned", reading: { reading: DELTA_READING, evidence: "Theorem 1" } });
    const { core: built, added } = buildCore(core, { symbols: [pin], review: { verdict: "PASS", summary: "", nodes: [], symbols: [pin] } });
    expect(added).toEqual([]);
    expect(built.assumptions.some((x) => x.id.startsWith("ass:pin-"))).toBe(false);
    expect(built.symbols.find((x) => x.name === "\\Delta")!.def).toBe(DELTA_READING);
    expect(bindingReadings(built, "ass:a").map((r) => r.of)).not.toContain("symbol \\Delta");
  });

  it("a drift fix corrects type, space and def; a pinned reading wins the def", () => {
    const v = sym("\\Delta", { meaning: "drift", fix: { type: "random remainder", space: "$\\mathbb{R}$", def: "the remainder" }, ambiguity: "pinned", reading: { reading: DELTA_READING, evidence: "Theorem 1" } });
    const s = buildCore(core, { symbols: [v] }).core.symbols.find((x) => x.name === "\\Delta")!;
    expect(s).toMatchObject({ type: "random remainder", space: "$\\mathbb{R}$", def: DELTA_READING });
  });
});

// ---------------------------------------------------------------------------------------------
// The stage
// ---------------------------------------------------------------------------------------------

type NodeFake = { symbolGrade?: (name: string, call: number) => Record<string, unknown> };

function stageCodex(calls: CodexRunInput[], opts: NodeFake = {}): typeof runCodex {
  const ok = (id: string) => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "reproduced", witness: null, fix: null, bookkeeping_assumption: null, reading: null, minimality: false, weakens_contribution: false, owner_explanation: null });
  return (async (input: CodexRunInput) => {
    calls.push(input);
    let reply: unknown;
    if (isSymbolCall(input)) {
      const names = symbolNames(input.prompt);
      const g = (n: string) => ({ ...okSymbol(n), ...(opts.symbolGrade?.(n, calls.length) ?? {}) });
      reply = { summary: "s", symbols: names.map(g) };
    } else if ((input.outputSchema as { required?: string[] }).required?.includes("cross_node")) {
      reply = { verdict: "PASS", summary: "g", patch_review: null, rejection_verdicts: null, cross_node: [] };
    } else {
      const ids = (input.prompt.match(/=== NODES TO GRADE[^\n]*===\n\n(?:[^\n-][^\n]*\n\n)?((?:- .*\n?)+)/)?.[1] ?? "").split("\n").filter(Boolean).map((l) => l.slice(2));
      reply = { summary: "s", nodes: ids.map(ok) };
    }
    return { stdout: JSON.stringify(reply), stderr: "" };
  }) as typeof runCodex;
}

async function stageRun(): Promise<{ runDir: string; state: StateJson; logs: string[]; args: (codex: typeof runCodex, o?: { dryRun?: boolean; symbolEffort?: "low" | "medium" | "high" }) => VerifyStageArgs }> {
  const root = await mkdtemp(path.join(os.tmpdir(), "verify-symbols-"));
  tmpDirs.push(root);
  const runDir = path.join(root, "runs", "toy");
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  await writeFile(path.join(runDir, VERIFY_FILES.coreJson), JSON.stringify(toyCore(), null, 2));
  await writeFile(path.join(runDir, VERIFY_FILES.coreTranscribed), JSON.stringify(toyCore(), null, 2));
  await writeFile(path.join(runDir, VERIFY_FILES.flatTex), FLAT);
  const state = createVerifyInitialState("toy", { phase: "v1", source: { input: "p", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
  const logs: string[] = [];
  return {
    runDir,
    state,
    logs,
    args: (codex, o = {}) => ({ repoRoot: root, qid: "toy", runDir, state, deps: { runCodex: codex }, dryRun: !!o.dryRun, ...(o.symbolEffort ? { refereeSymbolEffort: o.symbolEffort } : {}), log: (m: string) => logs.push(m) }),
  };
}

const deltaGrade = (n: string): Record<string, unknown> =>
  n === "\\Delta"
    ? { meaning: "drift", fix: { type: "random remainder of the fitted nuisances", def: "$n^{-1/2} R(\\hat{\\gamma})$" }, ambiguity: "pinned", reading: { reading: DELTA_READING, evidence: "Theorem 1 defines it from the fitted nuisances" } }
    : {};

describe("V1.5 with the symbol referee", () => {
  it("the symbol shard runs first; the fix reaches the table and the statement shards, the pin every user and every statement shard using it; metrics", async () => {
    const r = await stageRun();
    const calls: CodexRunInput[] = [];
    const res = await runStageV1_5(r.args(stageCodex(calls, { symbolGrade: deltaGrade })));
    expect(res.status).toBe("completed");
    expect(calls.filter(isSymbolCall)).toHaveLength(1);
    expect(isSymbolCall(calls[0]!)).toBe(true);
    expect(calls[0]!.outputSchema).toBe(SYMBOL_REPLY);
    expect(symbolNames(calls[0]!.prompt)).toHaveLength(6);
    const statementCalls = calls.slice(1).filter((c) => c.prompt.includes("=== NODES TO GRADE"));
    expect(statementCalls.length).toBeGreaterThan(0);
    for (const c of statementCalls) expect(c.prompt).toContain("random remainder of the fitted nuisances"); // the corrected table
    const core = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
    expect(core.symbols.find((x) => x.name === "\\Delta")!.type).toBe("random remainder of the fitted nuisances");
    expect(core.assumptions.some((a) => a.id.startsWith("ass:pin-"))).toBe(false);
    expect(core.symbols.find((x) => x.name === "\\Delta")!.def).toBe(DELTA_READING); // the reading is the table's def
    const review = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v15Review), "utf8"));
    expect(review.symbols).toHaveLength(6);
    const metrics = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v15RefereeMetrics), "utf8"));
    expect(metrics.symbols).toMatchObject({ symbols: 6, graded: 6, carried: 0 });
    expect(r.logs.some((l) => l.startsWith("symbol referee: 6 of 6 graded"))).toBe(true);
    expect(r.state.verify!.findings.some((f) => f.node === "symbol \\Delta" && f.detail.startsWith("symbol table corrected"))).toBe(true);

    // every statement shard grading thm:main sees Δ's reading in the symbol table it reads
    const shardPrompts = statementCalls.filter((c) => c.prompt.includes("- thm:main"));
    expect(shardPrompts.length).toBeGreaterThan(0);
    for (const p of shardPrompts) expect(p.prompt).toContain(JSON.stringify(DELTA_READING).slice(1, 40));

    // A second pass: nothing moved, no call at all (symbols and nodes carried).
    const calls2: CodexRunInput[] = [];
    const again = await runStageV1_5(r.args(stageCodex(calls2, { symbolGrade: deltaGrade })));
    expect(again.status).toBe("completed");
    expect(calls2).toHaveLength(0);
  });
});
