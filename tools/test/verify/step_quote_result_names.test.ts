/**
 * Contract items from the independent reading of the DFM annotated paper (2026-09-25), on the live
 * texts: a quoted step is the printed unit itself (`stepQuote`, whole by construction); a reading
 * describes the paper, not a pending repair (`correctedStatements`). Fixture: `fixtures/dfm_step_quote_result_names.json`
 * (read-only copies of the live run files named in its `_source`).
 */
import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import { noteProse, quoted, stepQuote, type OwnerExplanation } from "../../src/verify/owner_text.js";
import { correctedStatements } from "../../src/verify/stage_v1_5.js";

const here = path.dirname(fileURLToPath(import.meta.url));
const live = JSON.parse(readFileSync(path.join(here, "fixtures/dfm_step_quote_result_names.json"), "utf8")) as {
  dfm_flat: string;
  dfm_sks_note: OwnerExplanation;
  dfm_readings: Record<string, string>;
  cns_preamble: string;
  sks_printed: string;
  sks_corrected: string;
  var_kurt_printed: string;
  var_kurt_suggested: string;
};
const flat = live.dfm_flat;
/** The live DFM Theorem 4 note as fields (its step: the proof unit the old quote was cut from). */
const SKS: OwnerExplanation = {
  claim: "Under the constant-shift null, $\\sqrt{N}t_{SKS}$ has the displayed limit formed from independent $SBB_1$ and $SBB_0$ processes.",
  defects: [{ kind: "out_of_domain", step_unit: "thm::sks-nuisance/proof/1/5", uses: "independence of $SBB_1$ and $SBB_0$", assumed_on: "the two realizations in the theorem statement", applied_at: "the treatment and control sums formed under one matched-pair assignment", detail: null }],
  why: { objects: ["$N=2m$ with one treated subject per pair", "$\\tau=0$"], consequence: "the actual limit is $2^{-1/2}$ times the displayed nondegenerate supremum" },
  fix: "State a sampling and assignment hypothesis that gives the treatment and control sums the required independent joint process limit.",
  gives_up: null,
};

describe("a quoted step is the printed unit, whole by construction", () => {
  it("the live DFM quote (cut mid-sentence and on a lead-in before) is the unit's text; its claim closes it", () => {
    const unit = /Since both[\s\S]*?SBB_0\(y\)\.\s*\$\$/u.exec(flat)![0];
    const w = noteProse(SKS, (id) => (id === "thm::sks-nuisance/proof/1/5" ? unit : null)).what_is_wrong[0]!;
    // a quote keeps its marks; a display ending it is a quoted formula that holds the closing mark
    expect(w).toMatch(/^``\\dots we have \\vsDisplay\{\\sqrt\{N\}/u);
    expect(w).toContain("SBB_0(y).\\mbox{''}} This step uses independence of $SBB_1$ and $SBB_0$, which the paper assumes only for the two realizations in the theorem statement");
    // a row break `\\[2pt]` is no display
    expect(quoted(String.raw`a $\begin{cases} x \\[2pt] y\end{cases}$ so \[z\]`)).toBe("``" + String.raw`a $\begin{cases} x \\[2pt] y\end{cases}$ so \vsDisplay{z\mbox{''}}`);
    // a layout box the sentence cut opens (and closes after the quote) is dropped: left open it swallowed the page
    expect(quoted(String.raw`\begin{minipage}{0.47\textwidth} \[a = b\] \end{minipage} \hfill \begin{minipage}[t]{0.47\textwidth} \[c = d\]`)).toBe("\\vsDisplay{\\mbox{``}a = b} \\vsDisplay{c = d\\mbox{''}}");
    expect(stepQuote("The final conclusion follows from the symmetry of the shifted Brownian Bridge.")).toBe("The final conclusion follows from the symmetry of the shifted Brownian Bridge.");
  });
});

describe("a reading describes the paper as printed or as a confirmed repair changed it", () => {
  it("a symbol read from a statement whose only change is a pending suggestion is graded against the printed text", () => {
    const transcribed = { statements: [{ id: "thm:sks-nuisance", statement: live.sks_printed }, { id: "thm:var-kurt", statement: live.var_kurt_printed }] };
    const file = { patches: [{ node: "thm:sks-nuisance", corrected_statement: live.sks_corrected }], unfixable: [{ node: "thm:var-kurt", suggested_repair: { corrected_statement: live.var_kurt_suggested } }] };
    expect([...correctedStatements(transcribed, file).keys()]).toEqual(["thm:sks-nuisance"]);
    // a repair's readings are part of what a symbol is read from, with or without a changed statement
    const withReadings = correctedStatements(
      { statements: [{ id: "thm:a", statement: "printed a" }, { id: "thm:b", statement: "printed b" }] },
      { patches: [{ node: "thm:a", corrected_statement: "corrected a", readings: ["$m$ is the pointwise formula"] }, { node: "thm:b", corrected_statement: null, readings: ["$h$ is deterministic"] }] },
    );
    expect(withReadings.get("thm:a")!.text).toBe("corrected a\n\nReadings of this statement, stated by its repair (binding):\n- $m$ is the pointwise formula");
    expect(withReadings.get("thm:b")!.text).toBe("printed b\n\nReadings of this statement, stated by its repair (binding):\n- $h$ is deterministic");
  });
});
