import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, mkdir, writeFile, readFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { writeRunBarrel } from "../../src/formalization/proof_review_loop.js";
import { lintModuleHeader } from "../../src/toolkit/layout_lint.js";

// An in-progress run's Lean modules are NOT reachable from the toolkit's root barrels, so the
// DEFAULT lake target skips them: a plain `lake build` reports green while the run's oleans
// stay STALE, and a `#print axioms` against those lies. A per-run sibling barrel makes the whole run
// buildable/verifiable as ONE target — without wiring in-progress runs into the root barrel, which
// would make one broken run break everyone's default build.
let root: string;
beforeEach(async () => { root = await mkdtemp(path.join(tmpdir(), "barrel-")); });
afterEach(async () => { await rm(root, { recursive: true, force: true }); });

describe("writeRunBarrel: per-run aggregator so the run is one buildable target", () => {
  it("emits a deterministic module barrel with public imports, never importing itself", async () => {
    const leanDir = path.join(root, "CausalSmith", "ExactID", "EID_Foo_Research");
    await mkdir(path.join(leanDir, "Helpers"), { recursive: true });
    await writeFile(path.join(leanDir, "TApolar.lean"), "-- x\n", "utf8");
    await writeFile(path.join(leanDir, "Helpers", "ApolarQD.lean"), "-- x\n", "utf8");

    const out = await writeRunBarrel(root, leanDir);
    const src = await readFile(out!, "utf8");
    expect(src).toMatch(/^module\npublic import /);
    expect(src).not.toMatch(/Copyright/); // no owner hard-coded into generated files
    expect(src).toContain("public import CausalSmith.ExactID.EID_Foo_Research.TApolar");
    expect(src).toContain("public import CausalSmith.ExactID.EID_Foo_Research.Helpers.ApolarQD");
    expect(src).not.toMatch(/^import CausalSmith\./m);
    expect(src).not.toContain("import CausalSmith.ExactID.EID_Foo_Research\n"); // never imports itself
    expect(src.indexOf("module\n")).toBeLessThan(src.indexOf("public import "));
    expect(src.indexOf("public import ")).toBeLessThan(src.indexOf("/-!"));
    // The toolkit header contract: one blanket `public section` after the overview.
    expect(src).toMatch(/-\/\n\npublic section\n$/);
    expect(lintModuleHeader("Barrel.lean", src)).toEqual([]);
    // deterministic: sorted, so re-running produces no spurious diff
    expect(src).toBe(await readFile((await writeRunBarrel(root, leanDir))!, "utf8"));
  });

  it("returns null when there is nothing to aggregate", async () => {
    const empty = path.join(root, "CausalSmith", "ExactID", "Empty_Research");
    await mkdir(empty, { recursive: true });
    expect(await writeRunBarrel(root, empty)).toBeNull();
  });
});
