/**
 * Defects of the CNS resume of 2026-09-26 (`logs/live_resume_ops2.log`), on its live I/O
 * (`fixtures/cns_resume_ops2.json`, read-only copies of the run files named in its `_source`):
 *
 * 3. prop:delta stayed unclear: every rewrite quoting the right-hand side of a display row
 *    ("&= L^{1/2}…") was refused as beginning mid-sentence — since notes are fields (2026-09-26) a
 *    defect names its step's unit and the quote is that unit, whole (`stepQuote`).
 */
import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import { noteProblems, stepQuote, type OwnerExplanation } from "../../src/verify/owner_text.js";
import type { V15SymbolVerdict } from "../../src/verify/types.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const live = JSON.parse(readFileSync(path.join(here, "fixtures/cns_resume_ops2.json"), "utf8")) as {
  symbols_B1: V15SymbolVerdict[];
  symbols_B1_retry: V15SymbolVerdict[];
  prop_delta_note: OwnerExplanation;
  flat_prop_delta: string;
};

describe("3. a display row is never quoted alone: the step is its unit, quoted whole", () => {
  it("the live prop:delta note as fields passes the contract; its quote is the whole display", () => {
    const n = live.prop_delta_note;
    expect(noteProblems(n, { paper: live.flat_prop_delta })).toEqual([]);
    const unit = /By Proposition~\\ref\{prop:Taylor\}, write[\s\S]*?\\end\{align\*\}/u.exec(live.flat_prop_delta)![0];
    const q = stepQuote(unit);
    // both rows, inline, no alignment mark: never a row's right-hand side alone
    expect(q).not.toContain("&");
    expect(q).toContain("\\frac{n^{1/2}}{n_{\\ell}^{1/2}}");
    expect(q).toContain("L^{1/2}\\frac{1}{L} \\sum_{\\ell=1}^L \\sum_{j=1}^3 \\Delta_{j\\ell}");
  });
});
