import { describe, expect, it } from "vitest";
import { undefinedCitations } from "../../src/verify/annotated_compile.js";
import { baselineCitations, citationItems, isBlockingTodo } from "../../src/verify/bundle.js";

describe("undefined citations of the corrected paper", () => {
  it("reads the keys a LaTeX log reports undefined, once each, across a wrapped line", () => {
    const log = "LaTeX Warning: Citation `smith2020' on page 3 undefined on input line 12.\nLaTeX Warning: Citation `doe\n1999' on page 4 undefined\nLaTeX Warning: Citation `smith2020' on page 9 undefined";
    expect(undefinedCitations(log)).toEqual(["smith2020", "doe1999"]);
  });

  it("is the source's only when the unmodified source's compile leaves the same key undefined", () => {
    // a key the correction added (the source never cites it) is blocking; one the original also leaves undefined is not
    const items = citationItems(["madeup2026", "ghost"], new Set(["ghost"]), "main.tex", null);
    expect(items.map((i) => [i.group, isBlockingTodo(i), i.text])).toEqual([
      ["references-original", false, "1 citation(s) (ghost) undefined: the original source leaves them undefined too"],
      ["references", true, "1 citation(s) (madeup2026) undefined in the corrected paper, which the original source resolves or does not cite"],
    ]);
    // no baseline to compare with: blocking, said so
    expect(citationItems(["ghost"], null, "main.tex", "bibtex: not on PATH").map((i) => [i.group, i.text])).toEqual([
      ["references", "1 citation(s) (ghost) undefined in the corrected paper (the original source could not be compiled to compare) (bibtex: not on PATH)"],
    ]);
  });
  it("takes no baseline from a compile that timed out (its log names every key undefined)", () => {
    expect(baselineCitations({ status: "failed", reason: "timed out after 240 s", undefined_citations: ["realkey"] })).toBeNull();
    expect(baselineCitations({ status: "skipped", reason: "no pdflatex" })).toBeNull();
    expect([...baselineCitations({ status: "failed", reason: "pdflatex: Undefined control sequence", undefined_citations: ["k"] })!]).toEqual(["k"]);
  });
});
