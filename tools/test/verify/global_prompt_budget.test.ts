import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { PatchFile } from "../../src/verify/patches.js";
import { globalCoreText, verdictLine } from "../../src/verify/referee_shard_prompts.js";
import { GLOBAL_BY_FILE, globalPromptText, patchesShown } from "../../src/verify/stage_v1_5.js";
import type { V15NodeVerdict } from "../../src/verify/types.js";

const core = {
  qid: "g",
  symbols: [{ name: "W", type: "vector", def: "$W$ is the model vector." }],
  assumptions: [{ id: "ass:h", kind: "regularity", condition: "$W$ is bounded." }],
  definitions: [],
  statements: [{ id: "lem:a", kind: "lemma", statement: "$W$ converges in probability.", depends_on: ["ass:h"], status: "to-prove" }],
  target_estimand: "t",
} as unknown as Core;
const PRINTED = "$W$ converges almost surely.";
const patches = { key_results: ["lem:a"], key_contribution: "c", patches: [{ node: "lem:a", corrected_statement: "$W$ converges in probability.", proof_note: "p" }], unfixable: [] } as unknown as PatchFile;
const inputs = (flatTex: string) =>
  ({ base: "BRIEF", flatTex, targets: null, lintWarnings: { lint: [], parser: [] }, patches, printed: new Map([["lem:a", PRINTED]]) }) as unknown as Parameters<typeof globalPromptText>[0];
const verdicts = "=== SHARD VERDICTS ===\n{}";
const ids = new Set(["lem:a", "ass:h"]);

describe("the global pass's prompt within its budget", () => {
  it("pastes everything when it fits; past the budget, in turn: the repairs without their printed text, then the paper by file", () => {
    const paper = `\\begin{document}${"x".repeat(5000)}\\end{document}`;
    const all = globalPromptText(inputs(paper), core, verdicts, ids);
    expect(all).toContain(paper);
    expect(all).toContain(JSON.stringify(PRINTED));
    expect(all).toContain('"$W$ converges in probability."');
    const noPrinted = globalPromptText(inputs(paper), core, verdicts, ids, null, all.length - 1);
    expect(noPrinted).not.toContain(JSON.stringify(PRINTED));
    expect(noPrinted).toContain(paper);
    const noPaper = globalPromptText(inputs(paper), core, verdicts, ids, null, noPrinted.length - 1);
    expect(noPaper).not.toContain(paper);
    expect(noPaper).toContain(GLOBAL_BY_FILE.paper);
    expect(noPaper).toContain('"$W$ converges in probability."');
    // the core itself is always pasted (a pass confirming suggestions grades a core built in memory)
    const tight = globalPromptText(inputs(paper), core, verdicts, ids, null, 10);
    expect(tight).toContain(GLOBAL_BY_FILE.paper);
    expect(tight).toContain('"$W$ converges in probability."');
  });

  it("the symbol table takes the shorter of its two forms", () => {
    const scoped = { ...core, symbols: [{ name: "W", type: "vector", def: "$W$ is the model vector.", scoped: [{ results: ["lem:a"], text: "$W$ is localized." }, { results: ["lem:b"], text: "$W$ is a ".concat("long clause about another result. ".repeat(40)) }] }] } as unknown as Core;
    const shown = new Set(["lem:a", "ass:h"]);
    const perNode = globalCoreText(scoped, shown, shown), compact = globalCoreText(scoped, shown, shown, { compactSymbols: true });
    const prompt = globalPromptText(inputs("p"), scoped, verdicts, ids, { ids: shown, full: shown, paper: null });
    expect(prompt).toContain(perNode.length <= compact.length ? perNode : compact);
  });

  it("a shard's repairs still leave out the printed text only of the nodes it shows beside them", () => {
    const shown = (printedShown: (id: string) => boolean, global: boolean, sel?: string[]) => JSON.stringify(patchesShown(inputs("") as never, sel, printedShown, global));
    expect(shown(() => true, false, ["lem:a"])).not.toContain(PRINTED);
    expect(shown(() => false, false, ["lem:a"])).toContain(PRINTED);
    expect(shown(() => false, true)).toContain(PRINTED);
  });

  it("a verdict clean on every axis is shown by its grades; a flagged one keeps its reasons", () => {
    const v = (over: Record<string, unknown>) => ({ id: "lem:a", faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "the proof checks", graded: "fresh", ...over }) as unknown as V15NodeVerdict;
    expect(JSON.parse(verdictLine(v({})))).not.toHaveProperty("detail");
    expect(JSON.parse(verdictLine(v({})))).toMatchObject({ id: "lem:a", correctness: "ok" });
    expect(JSON.parse(verdictLine(v({ correctness: "error", detail: "the bound fails", witness: "n = 1" })))).toMatchObject({ detail: "the bound fails", witness: "n = 1" });
    expect(JSON.parse(verdictLine(v({ ambiguity: "pinned" })))).toHaveProperty("detail");
    expect(JSON.parse(verdictLine(v({ correctness: "bookkeeping" })))).toHaveProperty("detail");
  });
});
