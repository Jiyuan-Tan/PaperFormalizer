// Per-base-library prompt notes: `prompt_notes` in paperformalizer.json → `## Notes for <name>` in the
// F2 scaffold and F4 filler prompts; a library without notes contributes nothing.
import { mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { runFiller } from "../../src/formalization/proof_filler.js";
import { createEmptyGraph } from "../../src/graph/store.js";
import { toolkitConfigFromJson, type ToolkitConfig } from "../../src/toolkit/config.js";
import { baseLibraryNotesBlock } from "../../src/toolkit/prompt_notes.js";
import { TOOLKIT_JSON, tk } from "./helpers.js";

function withNotes(root: string, notes: string | null): ToolkitConfig {
  return toolkitConfigFromJson(root, {
    ...TOOLKIT_JSON,
    base: TOOLKIT_JSON.base.map((b) => (b.name === "Base" ? { ...b, prompt_notes: notes } : b)),
  });
}

describe("baseLibraryNotesBlock", () => {
  let root: string;
  beforeEach(async () => { root = await mkdtemp(path.join(os.tmpdir(), "prompt-notes-")); });
  afterEach(async () => { await rm(root, { recursive: true, force: true }); });

  async function fillerPrompt(toolkit: ToolkitConfig): Promise<string> {
    let rendered = "";
    await runFiller({
      ctx: { repoRoot: root, qid: "q", toolkit },
      graph: createEmptyGraph("q"),
      leanDir: path.join(root, "Papers", "Q"),
      promptPath: path.resolve(import.meta.dirname, "..", "..", "src", "formalization", "prompts", "F4", "proof_filler.txt"),
      deps: {
        runCodex: async (input) => {
          rendered = input.prompt;
          return { stdout: JSON.stringify({ summary: "no work" }), stderr: "" };
        },
      },
    });
    return rendered;
  }

  it("resolves prompt_notes against the toolkit root, renders one section per library, and reaches the F4 filler prompt", async () => {
    await writeFile(path.join(root, "base_notes.md"), "Use `base_simps`.\n", "utf8");
    const cfg = withNotes(root, "base_notes.md");
    expect(cfg.baseLibraries.find((b) => b.name === "Base")?.promptNotes).toBe(path.join(root, "base_notes.md"));
    expect(baseLibraryNotesBlock({ repoRoot: root, toolkit: cfg })).toBe("## Notes for Base\n\nUse `base_simps`.");
    expect(await fillerPrompt(cfg)).toContain("## Notes for Base\n\nUse `base_simps`.");
  });

  it("renders nothing when no base library has notes", async () => {
    expect(baseLibraryNotesBlock({ repoRoot: root, toolkit: tk(root) })).toBe("");
    expect(baseLibraryNotesBlock({ repoRoot: root, toolkit: withNotes(root, null) })).toBe("");
    expect(await fillerPrompt(tk(root))).not.toContain("## Notes for");
  });

  it("fails closed on a configured but unreadable notes file", () => {
    expect(() => baseLibraryNotesBlock({ repoRoot: root, toolkit: withNotes(root, "missing.md") }))
      .toThrow(/prompt_notes of base library Base is unreadable at .*missing\.md/);
  });
});
