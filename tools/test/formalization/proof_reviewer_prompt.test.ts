import { readFileSync } from "node:fs";
import { join } from "node:path";
import { describe, expect, it } from "vitest";

const prompt = readFileSync(join(process.cwd(), "src/formalization/prompts/F4/proof_reviewer.txt"), "utf8").replace(/\r\n/g, "\n");

describe("proof reviewer prompt", () => {
  it("states the null-set convention, so 'which version / pointwise or a.e.' is no statement finding (live drdid, yang: one question halted the runs again and again)", () => {
    expect(prompt).toContain("OBJECTS DEFINED UP TO NULL SETS");
    expect(prompt).toContain('never escalate "which version / pointwise or a.e." as `statement-wrong`');
    expect(prompt).toContain("Four recurring shapes are NOT ambiguous");
  });

  it("a detail a referee-written reading or condition leaves open is no paper finding (live yang, cns, drdid: envelope order, measurability, support)", () => {
    expect(prompt).toContain("A pinned reading or appended condition is the referee's wording, not the\npaper's");
    expect(prompt).toContain("means\nwhat the result's proof uses it for");
    // live cns: two reviewers read one pin oppositely (each called the other's Lean a mismatch) and
    // thm:local spent its three strikes — an open formal reading is reported, never silently chosen
    expect(prompt).toContain("the Lean is NOT drift: do\nnot pick the other reading and call it a mismatch");
    expect(prompt).toContain("so the owner\npins one");
  });

  it("names the frozen core node as the spec and carries no CausalSmith-only routes or targets", () => {
    expect(prompt).toContain("THE SPEC OF RECORD is the user's paper as its referee accepted it");
    expect(prompt).not.toMatch(/note-wrong|UNDELIVERED DELIVERY-ROLE|Routes BACK TO\s+D0|D0-AUTHORED|from-note|lemmav|T-n\/P-n\/L-n/);
  });
});

describe("proof reviewer prompt — the page is the spec excerpt", () => {
  it("grades from the page and opens the typed core only when the page does not settle a question (live cns: told merely where the core lives, 103 of 107 sessions read core.json whole)", () => {
    expect(prompt).toContain("Everything you grade is on\nthis page");
    expect(prompt).not.toMatch(/read\s+access to the Lean and the typed core/);
    expect(prompt).toContain("the typed core behind it is opened when the page does not settle a\nquestion");
  });
  it("a proved result that says more than the paper is matched; a hypothesis or definition stays under equivalence", () => {
    expect(prompt).toContain("EXCEPTION — A PROVED RESULT THAT SAYS MORE");
    expect(prompt).toMatch(/never a\s+hypothesis, a definition, or a carrier other results assume/);
    expect(prompt).toContain("THE BAR IS LOGICAL EQUIVALENCE");
  });
  it("states general rules, never a paper's own symbols", () => {
    expect(prompt).not.toMatch(/Y\(0\),Y\(1\)|WellFormedLaw|BoundedOutcome|Observation\.A|propensity/);
  });
});
