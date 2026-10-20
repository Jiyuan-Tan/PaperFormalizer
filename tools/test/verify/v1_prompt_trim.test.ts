/**
 * The V1 prompts' size discipline (`stage_v1.ts`): the fixer's core excerpt carries the fields it
 * reads, a previous reply is shown by the entries the violations name (whole only when nothing is
 * named and it is short), and the segmenter's source elides the proofs already attached.
 */
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { FlatTex } from "../../src/verify/tex_envs.js";
import { PREVIOUS_REPLY_WHOLE_MAX, coreExcerpt, numberedFlatWithout, previousReplyExcerpt } from "../../src/verify/stage_v1.js";

const core = (): Core =>
  ({
    qid: "q",
    target_estimand: "t",
    symbols: [{ name: "\\theta", type: "target" }, { name: "n", type: "sample size" }],
    assumptions: [{ id: "ass:a", kind: "regularity", condition: "$n \\ge 2$.", free_symbols: ["n"], novel: { flag: true, justification: "j" }, tex_locator: { file: "main.tex", from: 1, to: 2, env: "assumption", label: "a" }, used_by: ["lem:l"] }],
    definitions: [],
    statements: [
      { id: "lem:l", kind: "lemma", statement: "$\\theta \\le 1$.", depends_on: ["ass:a"], free_symbols: ["\\theta"], proof_tex: "the printed proof", status: "cited", source: { cite: "k", locator: "Thm 1", verbatim_statement: "v" }, tex_locator: { file: "main.tex", from: 3, to: 4, env: "lemma", label: "l" }, env: "lemma-1" },
      { id: "thm:t", kind: "theorem", statement: "Under the lemma, $\\theta = 0$.", depends_on: ["lem:l"], free_symbols: ["\\theta"], proof_tex: "p", status: "to-prove", tex_locator: { file: "main.tex", from: 5, to: 6, env: "theorem", label: "t" } },
    ],
    bibliography: [],
  }) as unknown as Core;

describe("the fixer's core excerpt", () => {
  it("each closure node with the fields the fixer reads: text, wiring, a cited source; no locator, symbol list, proof or provenance", () => {
    const lines = coreExcerpt(core(), ["lem:l"]).split("\n");
    const lem = JSON.parse(lines.find((l) => l.startsWith('{"id":"lem:l"'))!) as Record<string, unknown>;
    expect(lem).toEqual({ id: "lem:l", kind: "lemma", statement: "$\\theta \\le 1$.", depends_on: ["ass:a"], status: "cited", source: { cite: "k", locator: "Thm 1", verbatim_statement: "v" } });
    const ass = JSON.parse(lines.find((l) => l.startsWith('{"id":"ass:a"'))!) as Record<string, unknown>;
    expect(ass).toEqual({ id: "ass:a", kind: "regularity", condition: "$n \\ge 2$." });
    // The symbols those nodes use, and the results using them in one line.
    expect(lines).toContain('{"name":"\\\\theta","type":"target"}');
    expect(lines).toContain('{"name":"n","type":"sample size"}');
    expect(lines.some((l) => l.startsWith('{"id":"thm:t","depends_on":["lem:l"],"statement":'))).toBe(true);
  });
});

describe("the fixer's previous reply", () => {
  const reply = (big = false) => ({
    key_results: ["lem:a"],
    key_contribution: "c",
    patches: [
      { node: "lem:a", corrected_statement: "a" },
      { node: "lem:b", corrected_statement: big ? "b".repeat(PREVIOUS_REPLY_WHOLE_MAX) : "b" },
    ],
    unfixable: [],
    rejected: [],
  });

  it("the entries the violations name, with the key fields — also when another violation names no entry", () => {
    const shown = previousReplyExcerpt(reply(), ['the patch for "lem:a" has no note', "(reply) something general"]) as { patches: Array<{ node: string }>; key_results: string[] };
    expect(shown.patches.map((p) => p.node)).toEqual(["lem:a"]);
    expect(shown.key_results).toEqual(["lem:a"]);
  });

  it("whole only when no violation names an entry and the reply is short; a long one is shown by its key fields alone", () => {
    const short = reply();
    expect(previousReplyExcerpt(short, ["(reply) something general"])).toBe(short);
    const r = reply(true);
    expect(previousReplyExcerpt(r, ["(reply) something general"])).toEqual({ key_results: ["lem:a"], key_contribution: "c", patches: [], unfixable: [], rejected: [] });
  });

  it("a reply that did not parse is shown as text, cut at the cap", () => {
    const raw = `{"patches": [${"x".repeat(3 * PREVIOUS_REPLY_WHOLE_MAX)}`;
    const shown = previousReplyExcerpt(raw, ["(reply) the patch file did not parse"]) as string;
    expect(shown.length).toBeLessThan(raw.length);
    expect(shown).toMatch(/\[… \d+ bytes omitted: the reply did not parse; answer afresh …\]$/);
    expect(previousReplyExcerpt("short", ["(reply) did not parse"])).toBe("short");
  });
});

describe("the segmenter's source", () => {
  it("the proofs already attached are elided, one marker each, the numbering unchanged", () => {
    const flat = { text: ["a", "b", "proof 1", "proof 2", "c", "proof 3", "d"].join("\n"), lineMap: [], files: [], bibFiles: [] } as unknown as FlatTex;
    const out = numberedFlatWithout(flat, [
      { range: [3, 4], what: "the proof of thm:x, already attached" },
      { range: [6, 6], what: "the proof of lem:y, already attached" },
    ]);
    expect(out.split("\n")).toEqual([
      "    1| a",
      "    2| b",
      "     | [lines 3–4: the proof of thm:x, already attached; read them in discovery/flat.tex]",
      "    5| c",
      "     | [lines 6–6: the proof of lem:y, already attached; read them in discovery/flat.tex]",
      "    7| d",
    ]);
    expect(numberedFlatWithout(flat, [])).toContain("    3| proof 1");
  });
});
