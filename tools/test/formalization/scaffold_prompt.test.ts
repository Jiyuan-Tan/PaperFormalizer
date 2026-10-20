import { readFileSync } from "node:fs";
import { join } from "node:path";
import { describe, expect, it } from "vitest";
import { scaffoldInstructions } from "../../src/formalization/stage2.js";

// Match readPrompt's canonical text, independent of the checkout's line endings.
const prompt = readFileSync(join(process.cwd(), "src/formalization/prompts/F2/stage2_scaffold.txt"), "utf8").replace(/\r\n/g, "\n");

describe("F2 scaffold prompt", () => {
  it("forbids library-forced instances and junk values at excluded points (live lmz, yang: StandardBorelSpace for MAR, 1/(0:ℝ) for a dimension — each capped the proof loop)", () => {
    expect(prompt).toContain("LIBRARY-FORCED INSTANCE");
    expect(prompt).toContain("conditional independence as the a.e.\n  factorization of conditional expectations of indicators");
    expect(prompt).toContain("TOTALIZED OPERATIONS");
  });

  it("prefers a statement shaped as the paper states it, as a preference only (the owner: a long Lean statement is hard to compare with the paper)", () => {
    expect(prompt).toContain("shape a statement you write or change as the paper states it: one named hypothesis\n  per condition the paper states");
    expect(prompt).toContain("preference, never at the price of a weaker, stronger or harder-to-prove statement");
  });

  it("an object defined up to null sets is one measurable version (live cns: per-property ∃-versions with a sorry'd common choice; a smooth version without Measurable made lem:rp unprovable)", () => {
    expect(prompt).toContain("ONE MEASURABLE VERSION");
    expect(prompt).toContain("never\n  a separate `∃ version` per property, never a chosen version without measurability");
  });

  it("a helper F2 writes gets no @node tag (live yang: F2 tagged its own helper and the P7 gate stopped the run)", () => {
    expect(prompt).toContain("A helper you write gets NO `@node` tag (only plan nodes are tagged)");
  });

  // What a scaffolder must hold to on EVERY call, first scaffold or revise: one sentence per rule.
  const FAITHFULNESS_RULES = [
    "Do NOT make a node vacuous in Lean:",
    "- OVER-GENERALIZATION: replacing a constructed core object",
    "- ASSUMING THE CONCLUSION: `lemma foo (h : P) : P`.",
    "- DERIVABLE INTERMEDIATE AS PREMISE:",
    "- UNIVERSAL-CONSTANT QUANTIFIER ORDER:",
    "- DROPPED CONSTRAINT IN HELPERS:",
    "- WEAKENED EXISTENTIAL / DROPPED CONCLUSION:",
    "- LIBRARY-FORCED INSTANCE:",
    "- TOTALIZED OPERATIONS:",
    "- ONE MEASURABLE VERSION:",
    "- NEVER stub a load-bearing hypothesis as `(_h : True)`",
    "- HYPOTHESIS-COMPLETENESS:",
    "- BOOKKEEPING PREMISES ARE NOT \"ASSUMING THE CONCLUSION\"",
    "- MINIMAX / CONVERSE RISK ENCODING",
    "- DISTRIBUTION-CLASS AUXILIARY PINNING:",
    "- UNIFORM-CONSTANT MEMBERSHIP ON A CONVERSE:",
    "never replace a working proof\n  with `sorry` when its signature is unchanged",
    "- Statements, assumptions, and definitions match the CORE node verbatim: no silent strengthening,\n  weakening, extra assumptions, or vacuous restatements.",
    "- Encoding fidelity (literal-unfold rule):",
    "- Definitions carry full bodies; only lemmas/theorems carry `:= by sorry`.",
    "- No new typeclasses or library-scale structures.",
    "- Write only under the Lean target subdirectory, plus plan.json (sync-back).",
    "{{HEADER_CONTRACT}}",
    "tag EXACTLY ONE primary\ndeclaration and leave the companions untagged",
    "every adjustment is written\nBACK into plan.json",
    "=== OUTPUT JSON (return ONLY this object — no prose, no fences) ===",
    "{\"status\":\"completed\",\"message\":\"compiled sorry-only\"}",
    "\"status\":\"blocked-missing-architecture\"",
    "{\"status\":\"blocked\",\"message\":\"<file:line: error message and what was tried>\"}",
  ];
  const KIND_RULES: Record<string, string> = {
    assumption: "An `ass:` node is ALWAYS a threaded\n  hypothesis",
    gate: "the declaration must remain **exactly equivalent to the frozen core statement**",
    class: "fields are the member atoms",
    construction: "a `def` / `noncomputable def` realizing the core\n  `construction`",
    statement: "with hypotheses exactly the plan's `hyps`",
    open: "by the frozen-node TWO-CASE rule",
  };

  it("a first scaffold reads the template whole: the first-scaffold blocks in place, no revise text, no marker", () => {
    const whole = scaffoldInstructions(prompt, false);
    expect(whole).toBe(prompt.replace(/\{\{REVISE\}\}\n[\s\S]*?\{\{\/REVISE\}\}\n/g, "").replace(/\{\{\/?FIRST\}\}\n/g, ""));
    expect(whole).not.toMatch(/\{\{\/?(FIRST|REVISE)/);
    for (const rule of [...FAITHFULNESS_RULES, ...Object.values(KIND_RULES)]) expect(whole).toContain(rule);
    for (const first of ["=== MISSING-ARCHITECTURE CHECK (escalate before drafting) ===", "MANDATORY PARENT-ABSTRACTION CHECK", "=== FILE LAYOUT + POST-PROOF LENGTH (REQUIRED) ===", "target ≤600 lines per file", "one `T<local_id>.lean` per theorem"]) {
      expect(whole).toContain(first);
    }
  });

  it("a revise drops what only a first scaffold plans, and keeps every faithfulness rule, the rule of every kind, and how to mint a helper", () => {
    const slim = scaffoldInstructions(prompt, true);
    expect(slim).not.toMatch(/\{\{\/?(FIRST|REVISE)/);
    for (const rule of [...FAITHFULNESS_RULES, ...Object.values(KIND_RULES)]) expect(slim).toContain(rule);
    for (const first of ["MANDATORY PARENT-ABSTRACTION CHECK", "=== FILE LAYOUT + POST-PROOF LENGTH (REQUIRED) ===", "target ≤600 lines per file", "one `T<local_id>.lean` per theorem"]) {
      expect(slim).not.toContain(first);
    }
    // what stands in their place: when to escalate, with the three checks; where a declaration or a helper goes
    expect(slim).toContain("Return `blocked-missing-architecture` ONLY when the fix needs a\nSUBSTANTIAL new architectural piece");
    expect(slim).toContain("`why_substantial`\nMUST cite the result of each of the three checks.");
    expect(slim).toContain("Keep every declaration in the file it is in.");
    expect(slim).toContain("a helper gets NO `@node` tag");
    expect(slim).toContain("`<target>/Helpers/<Topic>.lean` under the thin imports-only\n`Helpers.lean` barrel");
    expect(slim).toContain("- Verify each file you wrote compiles standalone");
    expect(slim).toContain("only `declaration uses 'sorry'` warnings acceptable");
    expect(slim.length).toBeLessThan(scaffoldInstructions(prompt, false).length);
  });

  it("sync-back keeps the kind and members the core fixes, also under a redirect (live tbs: a reviewer's finding had the scaffolder re-plan a class as a `def`; the plan gate refused the scaffold three times)", () => {
    expect(prompt).toContain("Sync-back never changes what the core fixes — a class stays a `structure`\nwith its `members`");
    expect(prompt).toContain("Meet a redirect or `reviewer_finding` that asks for another shape INSIDE the planned kind");
    expect(scaffoldInstructions(prompt, true)).toContain("Sync-back never changes what the core fixes");
  });
});
