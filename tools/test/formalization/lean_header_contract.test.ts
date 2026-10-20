import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import { LEAN_HEADER_CONTRACT } from "../../src/formalization/lean_header_contract.js";

describe("Lean header prompt contract", () => {
  // (the digests that pinned these prompts byte for byte proved the constant's extraction changed
  // nothing; the prompts have been edited since, and what must hold is that each carries the one contract)
  it.each(["F1/stage1_template.txt", "F2/stage2_scaffold.txt", "F4/proof_filler.txt"])("%s takes the one header contract, by its placeholder alone", (file) => {
    const template = readFileSync(new URL(`../../src/formalization/prompts/${file}`, import.meta.url), "utf8");
    expect(template).toContain("{{HEADER_CONTRACT}}");
    expect(template).not.toContain(LEAN_HEADER_CONTRACT.slice(0, 60));
    expect(template.replaceAll("{{HEADER_CONTRACT}}", () => LEAN_HEADER_CONTRACT)).toContain(LEAN_HEADER_CONTRACT);
  });

  it("keeps the docstring pass limited to docstrings", () => {
    const template = readFileSync(new URL("../../src/formalization/prompts/F5/stage5_docstrings.txt", import.meta.url), "utf8");
    expect(template).not.toContain("HEADER_CONTRACT");
    expect(template).not.toContain("HEADER CONTRACT");
    expect(template).toContain("Do not change any statement, proof, name, attribute, or non-docstring text.");
  });
});
