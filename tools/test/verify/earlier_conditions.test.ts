import { readFileSync } from "node:fs";
import { join } from "node:path";
import { describe, expect, it } from "vitest";
import { keepEarlierConditions, priorConditionLines } from "../../src/verify/stage_v1_5.js";
import type { V15NodeVerdict, V15Review } from "../../src/verify/types.js";

const v = (id: string, over: Partial<V15NodeVerdict> = {}): V15NodeVerdict =>
  ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "d", witness: null, bookkeeping_assumption: null, reading: null, ...over }) as V15NodeVerdict;
const bk = { condition: "the scores are square integrable", reason: "the Taylor step" };
const prior: V15Review = { verdict: "PASS", summary: "", nodes: [v("lem:a", { correctness: "bookkeeping", bookkeeping_assumption: bk }), v("lem:b")] };

describe("V1.5: a condition appended on an earlier pass", () => {
  it("is kept when a fresh clean grade neither restates nor drops it (live yang: an AIPW regularity condition vanished on a re-grade)", () => {
    const [a] = keepEarlierConditions([v("lem:a")], prior);
    expect(a).toMatchObject({ correctness: "bookkeeping", bookkeeping_assumption: bk });
    expect(a!.detail).toMatch(/^\[condition kept from an earlier pass\]/);
  });

  it("is replaced when restated, gone when dropped on purpose, and untouched on an error grade", () => {
    const restated = { condition: "the scores are in L2 near the limit", reason: "r" };
    expect(keepEarlierConditions([v("lem:a", { correctness: "bookkeeping", bookkeeping_assumption: restated })], prior)[0]!.bookkeeping_assumption).toEqual(restated);
    expect(keepEarlierConditions([v("lem:a", { bookkeeping_dropped: true })], prior)[0]).toMatchObject({ correctness: "ok", bookkeeping_assumption: null });
    expect(keepEarlierConditions([v("lem:a", { correctness: "error", witness: "w" })], prior)[0]).toMatchObject({ correctness: "error" });
    expect(keepEarlierConditions([v("lem:b")], prior)[0]).toMatchObject({ correctness: "ok" });
  });

  it("is shown to the shard grading the node", () => {
    expect(priorConditionLines(prior, ["lem:a", "lem:b"])).toEqual([{ node: "lem:a", line: "lem:a: the scores are square integrable (the Taylor step)" }]);
  });
});

describe("V1.5 global pass prompt", () => {
  it("asks that what a result's proof takes from the setup or another result's hypotheses reach that result", () => {
    const g = readFileSync(join(process.cwd(), "src/verify/prompts/V1.5/global.txt"), "utf8").replace(/\r\n/g, "\n");
    expect(g).toContain("Read each result's PROOF too");
    expect(g).toContain("a setup fact that is no node yet → `new_assumption`, wired into every result whose proof\n   uses it");
  });
});
