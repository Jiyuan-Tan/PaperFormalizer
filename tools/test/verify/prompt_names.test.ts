// A prompt names a section, a field or a rule as the builder that emits it does.
import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { correctionBlock } from "../../src/pipeline_support.js";
import { corollaryReason } from "../../src/proposals/build.js";
import { NOTE_FIELDS_TEXT } from "../../src/verify/owner_text.js";
import { GLOBAL_OUTPUT_BLOCK } from "../../src/verify/referee_shard_prompts.js";
import { NODE_FIELDS_TEXT, SYMBOL_FIELDS_TEXT } from "../../src/verify/v1_5_schema.js";

const read = (rel: string): string => readFileSync(new URL(`../../src/${rel}`, import.meta.url), "utf8");

describe("prompt names", () => {
  it("a symbol's reading names an unlabelled result by its id, in the brief and in the field list alike", () => {
    for (const text of [SYMBOL_FIELDS_TEXT, read("verify/prompts/V1.5/symbols.txt")]) {
      expect(text.replace(/\s+/g, " ")).toMatch(/by its id as listed under THE TEXT EACH READING DESCRIBES/);
      expect(text).not.toContain("an unlabelled one by its printed heading");
    }
  });

  it("the referee's fields name the sections and lines its prompt shows", () => {
    expect(read("verify/stage_v1_5.ts")).toContain('"CONDITIONS APPENDED EARLIER (keep unless no longer needed)"');
    expect(NODE_FIELDS_TEXT).toContain("CONDITIONS APPENDED EARLIER");
    expect(NODE_FIELDS_TEXT).not.toContain("CONDITION APPENDED EARLIER");
    // a shard is shown a note as the author reads it ("Gives up: …"), never its `gives_up` field
    expect(read("verify/prompts/V1.5/review.txt")).not.toContain("gives_up");
    // the global pass is shown no brief text on the shape of a drift fix
    expect(GLOBAL_OUTPUT_BLOCK).not.toContain("the brief gives for a drift fix");
  });

  it("the fixer's note fields name its units section, and a correction does not contradict the revise head", () => {
    expect(read("verify/stage_v1.ts")).toContain("=== PAPER UNITS (");
    expect(NOTE_FIELDS_TEXT).toContain("as PAPER UNITS shows it");
    const block = correctionBlock({ status: "revise", classification: "c", perItemFindings: [], verbatim_critique: "x" }, 2);
    expect(block).not.toContain("Address ONLY");
    expect(block).toContain("what each entails for the entries that depend on it");
  });

  it("no prompt asks for a record or a field nothing reads", () => {
    for (const f of ["formalization/reuse_render.ts", "pipeline_support.ts"]) expect(read(f)).not.toMatch(/bypass-justified|no-candidate-fits|Assumption table artifact/);
    expect(read("formalization/prompts/F4/proof_filler.txt")).not.toContain("worked_on");
    expect(read("formalization/prompts/F5/stage5_docstrings.txt")).not.toContain("reply with DONE");
    expect(read("formalization/prompts/F1/stage1_template.txt")).not.toMatch(/openendedquestion|D0 must/);
    expect(SYMBOL_FIELDS_TEXT).toContain("{type, space, def}");
    expect(NODE_FIELDS_TEXT).not.toContain("`ambiguous`");
    expect(GLOBAL_OUTPUT_BLOCK).not.toMatch(/as the brief says\.\n  cross_node|the brief's rule gives/);
    expect(read("verify/prompts/V1.5/global.txt")).not.toContain("`rejection_verdicts` as the brief says");
  });

  it("the reason an agent gives for keeping the paper's proof reaches the log", () => {
    expect(corollaryReason("…\nCOROLLARY: not possible — the general result needs a bounded kernel\n")).toBe("the general result needs a bounded kernel");
    expect(corollaryReason("COROLLARY: done")).toBe("");
    expect(corollaryReason("`COROLLARY: not possible — it needs a bounded kernel`")).toBe("it needs a bounded kernel");
  });

  it("the plan prompts prescribe no plan the plan gate refuses: a gate or a deferral only on a statement the core marks cited", () => {
    const f15 = read("formalization/prompts/F1.5/stage1_5_reuse_soundness.txt");
    expect(f15).not.toMatch(/bounded-build|research-scale-external|Reclassify the irreducible core to `lean_kind:"assumption"`/);
    expect(f15).toContain("Never ask for a gate, a deferral or `lean_kind:\"assumption\"` on a paper-owned statement");
    const f1 = read("formalization/prompts/F1/stage1_template.txt");
    expect(f1).not.toContain("non-cited or cited");
    expect(f1).toContain("the gate (P8) refuses `gate:true` on any other statement, and `defer_tier:true` on a `define-local` node that is not such a gate");
    expect(read("formalization/prompts/F2/stage2_scaffold.txt")).not.toContain('`gate_class:"gated"` (or absent)');
  });

  it("a substrate-gate hypothesis is debt the report discloses, in the prompts as in the runner (it passes review)", () => {
    expect(read("formalization/prompts/F4/proof_reviewer.txt")).not.toMatch(/BLOCKS until built|assumption `derived`\/`substrate-gate`/);
    expect(read("formalization/prompts/F4/proof_filler.txt")).not.toContain("never stays in a delivered result");
  });
});
