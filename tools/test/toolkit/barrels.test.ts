// The root papers barrel: F5 adds `public import <papers_lib>.<Pascal>` to `<toolkit>/<papers_lib>.lean`.
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { ensurePapersBarrelImport, papersBarrelPath, removePapersBarrelImport } from "../../src/toolkit/barrels.js";
import { lintModuleHeader } from "../../src/toolkit/layout_lint.js";
import { BARREL, tk } from "./helpers.js";

describe("ensurePapersBarrelImport", () => {
  let root: string;
  beforeEach(async () => { root = await mkdtemp(path.join(os.tmpdir(), "papers-barrel-")); });
  afterEach(async () => { await rm(root, { recursive: true, force: true }); });

  it("insert → remove → insert round-trips byte-for-byte (a V1 re-extraction, then F5 again)", async () => {
    const cfg = tk(root);
    const before = BARREL("Papers");
    await writeFile(papersBarrelPath(cfg), before, "utf8");
    await ensurePapersBarrelImport(cfg, "Papers.LeeBounds");
    const inserted = await readFile(papersBarrelPath(cfg), "utf8");
    expect(await removePapersBarrelImport(cfg, "Papers.LeeBounds")).toEqual({ path: papersBarrelPath(cfg), changed: true });
    expect(await readFile(papersBarrelPath(cfg), "utf8")).toBe(before);
    expect((await removePapersBarrelImport(cfg, "Papers.LeeBounds")).changed).toBe(false);
    await ensurePapersBarrelImport(cfg, "Papers.LeeBounds");
    expect(await readFile(papersBarrelPath(cfg), "utf8")).toBe(inserted);
    // Only the named paper leaves; a comment mentioning it is not an import.
    await ensurePapersBarrelImport(cfg, "Papers.Alpha");
    await writeFile(papersBarrelPath(cfg), `${await readFile(papersBarrelPath(cfg), "utf8")}-- public import Papers.LeeBounds\n`, "utf8");
    await removePapersBarrelImport(cfg, "Papers.LeeBounds");
    const after = await readFile(papersBarrelPath(cfg), "utf8");
    expect(after.split("\n").filter((l) => l.startsWith("public import"))).toEqual(["public import Papers.Alpha"]);
    expect(after).toContain("-- public import Papers.LeeBounds");
    expect(lintModuleHeader("Papers.lean", after)).toEqual([]);
    // No barrel: nothing to do.
    const other = tk(await mkdtemp(path.join(os.tmpdir(), "papers-barrel-none-")));
    expect((await removePapersBarrelImport(other, "Papers.X")).changed).toBe(false);
  });

  it("keeps the import block sorted and is idempotent", async () => {
    const cfg = tk(root);
    await writeFile(papersBarrelPath(cfg), BARREL("Papers", ["Papers.Alpha", "Papers.Zeta"]), "utf8");
    await ensurePapersBarrelImport(cfg, "Papers.Mid");
    const once = await readFile(papersBarrelPath(cfg), "utf8");
    expect(once.split("\n").filter((l) => l.startsWith("public import"))).toEqual([
      "public import Papers.Alpha", "public import Papers.Mid", "public import Papers.Zeta",
    ]);
    expect(lintModuleHeader("Papers.lean", once)).toEqual([]);
    expect((await ensurePapersBarrelImport(cfg, "Papers.Mid")).changed).toBe(false);
    expect(await readFile(papersBarrelPath(cfg), "utf8")).toBe(once);
  });

  it("refuses a non-module barrel and a module outside the papers library", async () => {
    const cfg = tk(root);
    await writeFile(papersBarrelPath(cfg), "import Papers.Old\n", "utf8");
    await expect(ensurePapersBarrelImport(cfg, "Papers.New")).rejects.toThrow(/not a module-system file/);
    expect(await readFile(papersBarrelPath(cfg), "utf8")).toBe("import Papers.Old\n");
    await expect(ensurePapersBarrelImport(cfg, "Toolkit.Tricks")).rejects.toThrow(/not a paper barrel module/);
    await expect(ensurePapersBarrelImport(cfg, "Papers.A.B")).rejects.toThrow(/not a paper barrel module/);
  });
});
