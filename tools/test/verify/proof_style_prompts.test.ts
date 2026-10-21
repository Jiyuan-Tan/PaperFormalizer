import { readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";

/** The prompts' text with its line breaks and indentation read as single spaces. */
const prompt = (stage: string, file: string): string =>
  readFileSync(path.join(__dirname, "..", "..", "src", "verify", "prompts", stage, file), "utf8").replace(/\s+/gu, " ");

describe("a repaired proof keeps the paper's level of detail: the fixer is told it, the referee grades it", () => {
  const fixer = prompt("V1", "patch.txt");
  const referee = prompt("V1.5", "review.txt");

  it("the fixer keeps what the paper prints, adds only in details, and writes unprinted proofs complete without them", () => {
    expect(fixer).toContain("the corrected paper prints it WITHOUT its details");
    expect(fixer).toContain("keeping every display, intermediate step and cited result the paper prints there");
    expect(fixer).toContain("Never condense, summarize or paraphrase printed mathematics, nor move it into a detail");
    expect(fixer).toContain("your proof text without its details is never less complete than the printed proof it revises");
    expect(fixer).toContain("a proof the paper does not print (`proof_note`, a block's `follows`) is, without its details, a complete proof at the paper's level");
    // the level of detail is defined for a proof the paper does not print too
    expect(fixer).toContain("for a proof the paper does not print, that of its own proofs of results of the same kind");
  });

  it("the referee grades lost printed mathematics as an error of the repair, never as minimality", () => {
    expect(referee).toContain("The corrected paper prints the proof change WITHOUT its details");
    expect(referee).toContain("is an `error` of the repair, the witness naming the printed passage to keep — not a `minimality` grade");
    expect(referee).toContain("(and only such a grade, except that a change losing what the paper prints is the plain `error` under PATCHES)");
    expect(referee).toContain("`follows` read without its details is judged as above");
    // judging a repair's form is not judging the paper's style
    expect(referee).toContain("presentation or style of the paper as printed (a repair's form is judged under PATCHES)");
  });

  it("no older sentence pushes the other way", () => {
    // a taken-for-granted regularity condition goes beside the statement, not into it
    expect(fixer).not.toContain("write down a condition every reader takes for granted,");
    expect(fixer).toContain("goes in `conditions`, never into the statement");
    // a wrong step is corrected in place, not replaced wholesale
    expect(fixer).not.toContain("the note says is wrong is replaced,");
    expect(fixer).toContain("the wrong part changed, the rest of what it prints kept");
  });
});
