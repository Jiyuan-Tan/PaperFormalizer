import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdtemp, rm, writeFile, readFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { seedAnnotations } from "../../src/graph/annotate.js";

let dir: string;
beforeEach(async () => { dir = await mkdtemp(path.join(tmpdir(), "annot-")); });
afterEach(async () => { await rm(dir, { recursive: true, force: true }); });

const LEAN = `import Mathlib

/-- The overlap + bounded-outcome assumption bundle. -/
structure a3Bundle where
  e_bdd : True
  y_bdd : True

/-- The main rate theorem. -/
theorem t1_thm : True := by trivial

theorem t2_thm : True := by trivial
`;

describe("seedAnnotations", () => {
  it("inserts -- @node: above each obj_id-bearing decl (incl. assumption bundles)", async () => {
    await writeFile(path.join(dir, "T1.lean"), LEAN, "utf8");
    const count = await seedAnnotations(dir);
    expect(count).toBe(3);
    const out = await readFile(path.join(dir, "T1.lean"), "utf8");
    expect(out).toContain("-- @node: a3\nstructure a3Bundle"); // between docstring and header
    expect(out).toContain("-- @node: t1\ntheorem t1_thm");
    expect(out).toContain("-- @node: t2\ntheorem t2_thm");
    // idempotent: a second run inserts nothing
    expect(await seedAnnotations(dir)).toBe(0);
  });

  it.each([
    ["above a declaration docstring", "-- @node: thm:headline\n/-- The headline theorem. -/\ntheorem headline : True := by trivial\n"],
    ["across a multiline docstring and attribute", "-- @node: thm:headline\n/-- The headline\ntheorem. -/\n@[simp]\ntheorem headline : True := by trivial\n"],
  ])("does not duplicate an existing anchor %s", async (_label, body) => {
    const source = `import Mathlib\n\n${body}`;
    await writeFile(path.join(dir, "T1.lean"), source, "utf8");
    const count = await seedAnnotations(dir);
    expect(count).toBe(0);
    const out = await readFile(path.join(dir, "T1.lean"), "utf8");
    expect(out).toBe(source);
  });
});
