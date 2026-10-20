import { readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { docstringContract } from "../../src/shared/docstring_contract.js";
import { buildCoordinatorPrompt, buildReviewerPrompt, buildScaffolderPrompt, type ToolkitPromptContext } from "../../src/substrate/prompts.js";
import { readProposalPrompt } from "../../src/proposals/curator.js";

const toolkit: ToolkitPromptContext = {
  toolkitRoot: "/tk", lib: "Toolkit", papersLib: "Papers", divisions: ["Foundations", "Tricks"],
  baseNames: "Mathlib", searchBlock: "(search)",
};
const base = { toolkit, requirement: "R", leanDir: "/tk/Toolkit/Staging/s", modulePrefix: "Toolkit.Staging.s" };

describe("docstring contract: one text in every Lean-writing prompt", () => {
  const contract = docstringContract();
  it("states the crosslink rule, the placeholder ban and the no-script rule", () => {
    expect(contract).toContain("[phrase](hyp:name)");
    expect(contract).toContain("[phrase](goal)");
    expect(contract).toContain("the stated condition");
    expect(contract).toContain("never generate docstrings with a script");
  });
  it("reaches the study builder, coordinator and reviewer", () => {
    const scaffolder = buildScaffolderPrompt({ ...base, slug: "s", planMarkdown: null, lastReport: null, lastReview: null, buildRounds: 0, buildCap: 3 });
    const coordinator = buildCoordinatorPrompt({ ...base, slug: "s", leanFiles: [], stagingDir: "/st", lastFailureLog: null, topicTree: "" });
    const reviewer = buildReviewerPrompt(base);
    for (const p of [scaffolder, coordinator, reviewer]) {
      expect(p).toContain(contract);
      expect(p).not.toContain("{{DOCSTRING_CONTRACT}}");
    }
    expect(reviewer).toContain("documented");
  });
  it("reaches the promotion curator and the F5 docstring prompt", async () => {
    const curator = await readProposalPrompt("curator.txt");
    expect(curator).toContain(contract);
    // F5's prompt is read from disk at dispatch, also by runners started on older code, so it
    // carries the contract verbatim rather than a placeholder only new code fills.
    const f5 = readFileSync(path.resolve(__dirname, "../../src/formalization/prompts/F5/stage5_docstrings.txt"), "utf8");
    expect(f5).toContain(contract);
    expect(f5).not.toContain("{{DOCSTRING_CONTRACT}}");
  });
});
