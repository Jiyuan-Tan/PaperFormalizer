// Drift on a hypothesis or definition whose record is the transcribed one, with no edit named, over a
// symbol clause that reaches it through a result using it: the transcriber writes neither the symbol
// table nor a repair, so no revise round is started (live extreme-effects, 2026-10-08: a printed
// algorithm graded drift against a repaired result's reading of its estimator; the round returned
// the same core and the run halted on "drift repeated").
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { readingDrift } from "../../src/verify/stage_v1_5.js";
import type { V15NodeVerdict } from "../../src/verify/types.js";

const transcribed = (): Core =>
  ({
    qid: "reading-drift",
    symbols: [{ name: "W", type: "statistic", def: "$W$ is the statistic of the procedure." }],
    assumptions: [{ id: "ass:h", kind: "regularity", condition: "The sample is i.i.d." }],
    definitions: [
      { id: "def:proc", name: "Procedure", construction: "Compute $W$ on the retained half.", free_symbols: ["W"] },
      { id: "def:other", name: "Other", construction: "A set is retained when it is large." },
    ],
    statements: [{ id: "lem:a", kind: "lemma", statement: "$W$ is consistent.", depends_on: ["def:proc", "def:other", "ass:h"], free_symbols: ["W"], status: "to-prove" }],
    target_estimand: "x",
    bibliography: [],
  }) as unknown as Core;
/** The graded core: the table carries a clause of the result using the definition. */
const graded = (): Core => {
  const c = structuredClone(transcribed());
  c.symbols[0]!.scoped = [{ results: ["lem:a"], text: "$W$ is computed on the whole sample." }];
  (c.assumptions[0] as { used_by?: string[] }).used_by = ["lem:a"];
  return c;
};
const drift = (id: string, fix: V15NodeVerdict["fix"] = null): V15NodeVerdict =>
  ({ id, faithfulness: "drift", ambiguity: "ok", correctness: "ok", detail: "d", witness: null, fix, bookkeeping_assumption: null, reading: null }) as V15NodeVerdict;
const paper = (n: V15NodeVerdict): boolean => n.faithfulness === "drift";

describe("drift no transcription round can remove", () => {
  it("is drift without an edit on a transcribed hypothesis or definition that a result's symbol clause reaches", () => {
    expect(readingDrift([drift("def:proc")], paper, graded(), transcribed())).toEqual(["def:proc"]);
  });
  it("is not ordinary drift: an edit named, a setting asked, a result, a node no clause reaches, a table without clauses, a record a repair wrote", () => {
    const fix = { add_depends_on: null, remove_depends_on: null, wire_into: ["lem:a"], unwire_from: null, extend_to: null, new_assumption: null } as never;
    expect(readingDrift([drift("def:proc", fix)], paper, graded(), transcribed())).toEqual([]);
    expect(readingDrift([drift("def:proc", { setting: "The sample is random." } as never)], paper, graded(), transcribed())).toEqual([]);
    expect(readingDrift([drift("lem:a"), drift("def:other"), drift("ass:h")], paper, graded(), transcribed())).toEqual([]);
    expect(readingDrift([drift("def:proc")], paper, transcribed(), transcribed())).toEqual([]);
    const repaired = graded();
    (repaired.definitions[0] as { construction: string }).construction = "Compute $W$ on the whole sample.";
    expect(readingDrift([drift("def:proc")], paper, repaired, transcribed())).toEqual([]);
    expect(readingDrift([drift("def:proc")], () => false, graded(), transcribed())).toEqual([]);
  });
});
