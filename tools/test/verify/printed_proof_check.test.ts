/**
 * After reproducing the load-bearing steps, the referee checks the proof AS PRINTED (e.g. the minor arcs were reproduced on R/Z while the proof printed them as
 * intervals in [0,1], missing the arc at 1; the reproduction matched the formulas, so nothing was
 * reported). Step 4 of "Reproduce it" says so; the brief a shard reads carries it.
 */
import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import { shardBriefOf } from "../../src/verify/referee_shard_prompts.js";

const BRIEF = readFileSync(path.join(path.dirname(fileURLToPath(import.meta.url)), "..", "..", "src", "verify", "prompts", "V1.5", "review.txt"), "utf8");
const STEP4 =
  "4. Then check the proof as printed: its setup (the sets, ranges, domains and properties it introduces) and each step. Where the printed version is not what you used, redo the step under the printed version. Report a step only if it is wrong as printed, with its witness, graded as in step 3 (a typo goes in `typos`).";
const flat = (t: string): string => t.replace(/\s+/gu, " ");

describe("reproduce, then check the proof as printed", () => {
  it("step 4 follows step 3 of the method", () => {
    const text = flat(BRIEF);
    expect(text).toContain(STEP4);
    expect(text.indexOf("3. Diff your term list")).toBeLessThan(text.indexOf(STEP4));
    expect(text.indexOf(STEP4)).toBeLessThan(text.indexOf("CITED STANDARD RESULTS."));
  });

  it("a shard grading a statement reads it", () => {
    expect(flat(shardBriefOf(BRIEF, { statements: true, patches: false, cited: false }))).toContain(STEP4);
  });
});
