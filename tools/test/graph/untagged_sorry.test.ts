import { describe, it, expect, afterAll } from "vitest";
import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { untaggedSorryDecls } from "../../src/graph/extractor.js";
import { createEmptyGraph } from "../../src/graph/store.js";
import { renderFillerContext } from "../../src/formalization/proof_filler.js";

// A tagged result assembled from untagged branch theorems reads `complete` in the graph while the
// branches still hold `sorry`; the filler's open work must list them (yang: six such branches).
const dir = mkdtempSync(join(tmpdir(), "untagged-sorry-"));
afterAll(() => rmSync(dir, { recursive: true, force: true }));
mkdirSync(join(dir, "tmp"));
writeFileSync(join(dir, "TBoot.lean"), [
  "theorem boot_ral : True := by",
  "  sorry",
  "",
  "/-- uses `sorry` only in prose -/",
  "theorem boot_clean : True := trivial -- sorry in a comment",
  "",
  "-- @node: thm:boot",
  "/-- Full statement. -/",
  "theorem boot : True := by",
  "  sorry",
  "",
  "-- @node: own_helper",
  "lemma own_helper : True := by sorry",
  "lemma boot_matching : True := by sorry",
].join("\n"));
writeFileSync(join(dir, "tmp", "Scratch.lean"), "theorem scratch : True := by sorry\n");

describe("untaggedSorryDecls", () => {
  it("lists exactly the untagged declarations whose own text holds a sorry", async () => {
    const found = await untaggedSorryDecls(dir);
    expect(found.map((d) => [d.declName, d.line])).toEqual([["boot_ral", 1], ["boot_matching", 14]]);
    expect(found[0].file).toBe("TBoot.lean");
  });

  it("renders them in the filler's open work", async () => {
    const ctx = renderFillerContext(createEmptyGraph("q"), await untaggedSorryDecls(dir));
    expect(ctx).toContain("UNTAGGED DECLARATIONS STILL HOLDING `sorry`");
    expect(ctx).toContain("- boot_ral (TBoot.lean:1)");
    expect(ctx).not.toContain("scratch");
    expect(renderFillerContext(createEmptyGraph("q"))).not.toContain("UNTAGGED");
  });
});
