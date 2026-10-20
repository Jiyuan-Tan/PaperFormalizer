import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { toolkitTemplateDir } from "../../src/toolkit/lakefile.js";

// The toolkit template ships its own copy of Causalean's index extractor (`LibraryIndexCore.lean`)
// so a toolkit needs no Causalean. This keeps the copy from drifting: wherever a Causalean
// checkout is named (`CAUSALEAN_ROOT`), the copy below its header comment must equal the upstream
// file, its opening sentence apart (the copy names no other project). Port an upstream change by
// copying it.
const upstream = path.join(process.env.CAUSALEAN_ROOT ?? "/nonexistent", "LibraryIndexCore.lean");
/** The module docstring's first sentence, which the copy words for itself. */
const sansOpening = (lean: string): string => lean.replace(/\r\n/g, "\n").replace(/(\/-! # Library-index extractor core\n\n)[\s\S]*?(?=\(statement,)/, "$1");

describe("LeanSmithIndexCore.lean", () => {
  it.skipIf(!existsSync(upstream))("equals Causalean's LibraryIndexCore.lean below its header", () => {
    const copy = readFileSync(path.join(toolkitTemplateDir(), "LeanSmithIndexCore.lean"), "utf8").replace(/\r\n/g, "\n");
    const body = copy.slice(copy.indexOf("-/\n\n") + 4);
    expect(sansOpening(body)).toBe(sansOpening(readFileSync(upstream, "utf8")));
  });

  it("is imported by both index executables, never Causalean's module", () => {
    for (const exe of ["PaperIndex.lean", "ToolkitIndex.lean"]) {
      const src = readFileSync(path.join(toolkitTemplateDir(), exe), "utf8").replace(/\r\n/g, "\n");
      expect(src.startsWith("import LeanSmithIndexCore\n")).toBe(true);
    }
  });
});
