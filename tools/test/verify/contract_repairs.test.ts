/**
 * The content contract of what the author reads (independent reader's findings on the live CNS and
 * DFM PDFs, 2026-09-25), each defect caught by a check and sent back to its producer:
 *   C4 a proof-only repair gives nothing up;
 *   C5 a symbol read from a statement a repair corrects is re-graded against the corrected text;
 *   C6 TeX of corrected statements, added hypotheses, proof edits and notes, referee readings.
 * Fixtures quote the live runs verbatim (`fixtures/contract_c1_c7.json`). No model call.
 */
import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { givesUpProblems, texMathProblems, type OwnerExplanation } from "../../src/verify/owner_text.js";
import { PatchFileSchema } from "../../src/verify/patches.js";
import { symbolUsers } from "../../src/verify/core_graph.js";
import { paperIndex } from "../../src/verify/referee_slices.js";
import { runSymbolPass, type SymbolPassInput } from "../../src/verify/referee_symbols.js";
import { repairTextProblems } from "../../src/verify/restatement.js";
import { repairTextViolations } from "../../src/verify/stage_v1.js";

const HERE = path.dirname(fileURLToPath(import.meta.url));
const PROMPTS = path.join(HERE, "..", "..", "src", "verify", "prompts");
const LIVE = JSON.parse(readFileSync(path.join(HERE, "fixtures", "contract_c1_c7.json"), "utf8"));

describe("C4: a proof-only repair gives nothing up", () => {
  it("the live Proposition D.6 note gives up the bound its proof-only repair establishes: refused at every producer", () => {
    const repair = LIVE.cns_prop_delta_patch;
    expect(repair.corrected_statement).toBeNull();
    const D6 = LIVE.cns_d6_note as OwnerExplanation;
    expect(givesUpProblems(D6, repair)).toEqual([expect.stringContaining("the repair changes the proof alone")]);
    // the fixer's reply
    const file = PatchFileSchema.parse({ key_results: [], key_contribution: "c", patches: [{ ...repair, remove_depends_on: [], owner_explanation: D6 }], unfixable: [] });
    const core = { statements: [{ id: "prop:delta", statement: "s", proof_tex: "p" }], assumptions: [], definitions: [] } as unknown as Core;
    expect(repairTextViolations(core, file, null).join(" ")).toContain('the patch for "prop:delta": its owner_explanation gives something up');
    // a repair that restates the result (e.g. with an added hypothesis) may give something up
    expect(givesUpProblems(D6, { corrected_statement: "If $r<1$, the bound holds." })).toEqual([]);
  });
});

describe("C5: a symbol read from a corrected statement is re-graded", () => {
  const FLAT = (LIVE.dfm_sks.flat_1240_1270 as string[]).join("\n");
  const lines = FLAT.split("\n");
  const from = lines.findIndex((l) => l.startsWith("\\begin{thm}")) + 1;
  const to = lines.findIndex((l) => l.startsWith("\\end{thm}")) + 1;
  const core = (): Core =>
    ({
      qid: "dfm",
      symbols: LIVE.dfm_symbols,
      assumptions: [],
      definitions: [],
      statements: [{ id: "thm:sks-nuisance", kind: "theorem", statement: LIVE.dfm_sks.printed, depends_on: [], free_symbols: LIVE.dfm_sks.free_symbols, proof_tex: "", status: "to-prove", tex_locator: { file: "main.tex", from, to, env: "thm", label: "thm::sks-nuisance" } }],
      target_estimand: "$\\tau$",
      bibliography: [],
    }) as unknown as Core;
  const okSym = (name: string) => ({ name, meaning: "ok", fix: null, ambiguity: "ok", reading: null, redefined_at: null, detail: "d" });
  const ask = (calls: Array<{ names: string[]; prompt: string }>) => async (c: { kind: string; nodes: string[]; prompt: string }): Promise<unknown> => {
    calls.push({ names: c.nodes, prompt: c.prompt });
    return { summary: "s", symbols: c.nodes.map(okSym) };
  };
  const input = async (over: Partial<SymbolPassInput>): Promise<SymbolPassInput> => ({
    core: core(),
    px: paperIndex(FLAT, null, null),
    lineMap: null,
    prior: [],
    confirmed: {},
    briefs: { symbols: readFileSync(path.join(PROMPTS, "V1.5", "symbols.txt"), "utf8") },
    scope: "scope",
    ask: ask([]),
    log: () => {},
    ...over,
  });

  it("correcting Theorem 4 (the live DFM repair: BB{F_0(y)}) re-grades every symbol it uses (BB, ξ, x, τ), shown the corrected text", async () => {
    const first = await runSymbolPass(await input({}));
    expect(first.ok).toBe(true);
    if (!first.ok) return;
    const calls: Array<{ names: string[]; prompt: string }> = [];
    // unchanged: nothing re-graded
    await runSymbolPass(await input({ prior: first.symbols, confirmed: first.confirmed, ask: ask(calls) }));
    expect(calls).toHaveLength(0);
    const corrected = new Map([["thm:sks-nuisance", { printed: LIVE.dfm_sks.printed, text: LIVE.dfm_sks.corrected }]]);
    const again = await runSymbolPass(await input({ prior: first.symbols, confirmed: first.confirmed, ask: ask(calls), corrected }));
    expect(again.ok).toBe(true);
    const graded = new Set(calls.flatMap((c) => c.names));
    for (const s of ["BB(\\cdot)", "\\xi(\\cdot)", "x", "\\tau"]) expect(graded.has(s)).toBe(true);
    // user finding 2026-09-26: every statement USING a symbol is a source of its reading, not only the
    // ones that introduce it
    expect(core().symbols.filter((x) => symbolUsers(core(), x.name).includes("thm:sks-nuisance")).every((x) => graded.has(x.name))).toBe(true);
    expect(calls[0]!.prompt).toContain("Corrected by a repair: thm:sks-nuisance, a statement this symbol is read from");
    expect(calls[0]!.prompt).toContain("SBB(y)\\equiv BB\\{F_0(y)\\}+\\xi(y)");
    // the corrected text on file again: carried
    const calls2: Array<{ names: string[]; prompt: string }> = [];
    if (!again.ok) return;
    await runSymbolPass(await input({ prior: again.symbols, confirmed: again.confirmed, ask: ask(calls2), corrected }));
    expect(calls2).toHaveLength(0);
  });

  it("an unresolvable symbol is carried, with its line, on an unchanged basis like a settled one: nothing it was shown moved", async () => {
    const first = await runSymbolPass(await input({}));
    expect(first.ok).toBe(true);
    if (!first.ok) return;
    const open = first.symbols[0]!.name;
    const prior = first.symbols.map((v) => (v.name === open ? { ...v, ambiguity: "unresolvable" as const, detail: "two readings" } : v));
    const calls: Array<{ names: string[]; prompt: string }> = [];
    const next = await runSymbolPass(await input({ prior, confirmed: first.confirmed, ask: ask(calls) }));
    expect(calls.flatMap((c) => c.names)).toEqual([]);
    expect(next.ok && next.symbols.find((v) => v.name === open)).toMatchObject({ ambiguity: "unresolvable", detail: "two readings", graded: "carried" });
  });
});

describe("C6: the TeX of every repair text and of the referee's readings", () => {
  it("the live DFM proof edit with an over-escaped \\\\mu is a fixer violation; the live CNS amended proof with a stray $$ is named, the printed statement's own multi-line inline math is not", () => {
    const u = LIVE.dfm_var_kurt_suggestion;
    expect(u.suggested_repair.proof_edits[0].replacement).toContain("\\widehat{\\\\mu}_t");
    // (its note, written before notes were fields, is not what this test checks)
    const file = PatchFileSchema.parse({ key_results: [], key_contribution: "c", patches: [], unfixable: [{ ...u, owner_explanation: LIVE.cns_d6_note }] });
    const core = { statements: [{ id: "thm:var-kurt", statement: "s", proof_tex: "p" }], assumptions: [], definitions: [] } as unknown as Core;
    // Its sentence-anchored edit is not part of the ops format: the amended proof it derived is checked.
    expect(repairTextViolations(core, file, null).join(" ")).toContain('the suggested repair for "thm:var-kurt": writes a TeX command with a doubled backslash in `proof_note` ("\\\\mu")');
    expect(repairTextProblems({ ops: [{ op: "replace", unit: "lemma:global/proof/1/1", tex: "x" }], proof_note: LIVE.cns_lem_global_proof_note }, null, { printed: "", proof: "", labelOf: () => null }).join(" ")).toContain('leaves "$$" unclosed in `amended proof');
    const { printed, corrected } = LIVE.cns_local_clause;
    expect(texMathProblems(corrected, "corrected_statement")).toEqual([expect.stringContaining("line break inside $…$")]);
    expect(texMathProblems(corrected, "corrected_statement", { reference: printed })).toEqual([]);
    // a break that ate "\n" of a command still counts
    expect(texMathProblems("$a \neq b$", "c", { reference: printed }).join(" ")).toContain("line break inside $…$");
  });
});
