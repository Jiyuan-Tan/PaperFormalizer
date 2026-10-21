/** The reviewer's pointer to library sources (live wss: a Causalean definition "not located", the target called unadjudicable). */
import { describe, expect, it } from "vitest";
import { librarySourceRootsLine } from "../../src/toolkit/search.js";
import type { ToolkitConfig } from "../../src/toolkit/config.js";

describe("librarySourceRootsLine", () => {
  it("names the source root of every base library that has one and of the toolkit; a library with no path is left out", () => {
    const toolkit = {
      lib: "Toolkit",
      toolkitLibDir: "/tk/Toolkit",
      baseLibraries: [{ name: "Mathlib", search: ["loogle"] }, { name: "Causalean", path: "/src/Causalean", search: [] }],
    } as unknown as ToolkitConfig;
    const line = librarySourceRootsLine({ repoRoot: "/tk", toolkit });
    expect(line).toContain("Causalean: /src/Causalean; Toolkit (this toolkit): /tk/Toolkit");
    expect(line).not.toContain("Mathlib");
  });
  it("is empty when no toolkit resolves", () => {
    const saved = process.env.PAPERFORMALIZER_TOOLKIT;
    delete process.env.PAPERFORMALIZER_TOOLKIT;
    try {
      expect(librarySourceRootsLine({ repoRoot: "/nonexistent-toolkit-root" })).toBe("");
    } finally {
      if (saved !== undefined) process.env.PAPERFORMALIZER_TOOLKIT = saved;
    }
  });
});
