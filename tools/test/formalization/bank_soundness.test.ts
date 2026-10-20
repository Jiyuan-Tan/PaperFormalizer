import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { bankSoundnessIssues } from "../../src/formalization/bank_soundness.js";

let root = "";
let leanDir = "";

beforeEach(async () => {
  root = await mkdtemp(join(tmpdir(), "bank-soundness-"));
  leanDir = join(root, "CausalSmith", "Stat", "Demo");
  await mkdir(leanDir, { recursive: true });
});
afterEach(async () => {
  await rm(root, { recursive: true, force: true });
});

const clean = "import Mathlib.Tactic\n\nnamespace Demo\n\ntheorem ok : True := by trivial\n\nend Demo\n";

describe("bankSoundnessIssues", () => {
  it("passes a clean artifact", async () => {
    await writeFile(join(leanDir, "T.lean"), clean);
    expect(await bankSoundnessIssues(leanDir, root)).toEqual([]);
  });

  it.each(["axiom foo : True", "opaque bar : Nat", "theorem t : True := by admit", "theorem t : True := by exact sorryAx True true"])(
    "reports the cheat token in %j",
    async (line) => {
      await writeFile(join(leanDir, "T.lean"), `namespace D\n${line}\nend D\n`);
      expect(await bankSoundnessIssues(leanDir, root)).not.toEqual([]);
    },
  );

  // The paper's disposable agent workspace (`<leanDir>/tmp`) is excluded from the bank
  // inventory: agents are TOLD to leave sorry-laden Lean probes there, and a scratch file
  // must not spuriously block banking of an otherwise clean artifact.
  it("ignores scratch files under the paper tmp/ workspace", async () => {
    await writeFile(join(leanDir, "T.lean"), clean);
    const scratch = join(leanDir, "tmp");
    await mkdir(scratch, { recursive: true });
    await writeFile(join(scratch, "Main.lean"), "theorem probe : True := by sorry\n");
    expect(await bankSoundnessIssues(leanDir, root)).toEqual([]);
  });

  // The gate follows imports, so debt cannot be laundered by moving it one module out of the
  // artifact directory.
  it.each([
    ["a module-style public import", {
      "CausalSmith/Mathlib/PublicHelper.lean": "module\n\n/-! Public helper fixture. -/\n\n@[expose] public section\nnamespace H\ntheorem hiddenDebt : True := by sorry\nend H\n",
    }, "module\npublic import CausalSmith.Mathlib.PublicHelper\n\n/-! Artifact fixture. -/\n\n@[expose] public section\ntheorem cleanSurface : True := by trivial\n",
    /Mathlib\/PublicHelper\.lean/],
    ["guillemet components containing spaces", {
      "CausalSmith/Sub Dir/Helper.lean": "theorem debt2 : True := by sorry\n",
    }, "import CausalSmith.«Sub Dir».Helper\ntheorem ok : True := trivial\n",
    /Sub Dir\/Helper\.lean/],
    ["a transitive import to a Unicode module name", {
      "CausalSmith/Shared/ΔHelper.lean": "theorem debt : True := by sorry\n",
      "CausalSmith/Substrate/X.lean": "public import CausalSmith.Shared.ΔHelper\ntheorem x : True := by trivial\n",
    }, "public import CausalSmith.Substrate.X\ntheorem clean : True := by trivial\n",
    /Shared\/ΔHelper\.lean/],
  ])("reports debt reached through %s", async (_label, files, main, where) => {
    for (const [rel, text] of Object.entries(files as Record<string, string>)) {
      await mkdir(join(root, rel, ".."), { recursive: true });
      await writeFile(join(root, rel), text);
    }
    await writeFile(join(leanDir, "T.lean"), main as string);
    const issues = await bankSoundnessIssues(leanDir, root);
    expect(issues.some((i) => (where as RegExp).test(i) && /sorry/.test(i))).toBe(true);
  });
});

it("follows imports into any library of the Lake project, never into dependencies", async () => {
  const { mkdtempSync, mkdirSync, writeFileSync } = await import("node:fs");
  const { tmpdir } = await import("node:os");
  const { join } = await import("node:path");
  const root = mkdtempSync(join(tmpdir(), "bank-project-libs-"));
  const run = join(root, "Papers", "Foo");
  mkdirSync(run, { recursive: true });
  mkdirSync(join(root, "Toolkit", "Tricks"), { recursive: true });
  writeFileSync(
    join(run, "Main.lean"),
    "public import Toolkit.Tricks.Bound\npublic import Causalean.Stat.Basic\npublic import Mathlib.Tactic\ntheorem ok : True := trivial\n",
  );
  writeFileSync(join(root, "Toolkit", "Tricks", "Bound.lean"), "theorem debt : True := by sorry\n");
  const issues = await bankSoundnessIssues(run, root);
  expect(issues.some((i) => /Toolkit\/Tricks\/Bound\.lean/.test(i) && /sorry/.test(i))).toBe(true);
  // a dependency is not part of the project: no "unreadable file" for Causalean / Mathlib
  expect(issues.some((i) => /Causalean|Mathlib/.test(i))).toBe(false);
});

describe("bankSoundnessIssues: one report per token, strings masked", () => {
  it("reports a sorry once with its line, and not one inside a string literal or a comment", async () => {
    await writeFile(join(leanDir, "T.lean"), [
      "namespace D",
      '/-- a docstring saying sorry -/',
      'def msg : String := "no sorry here, no axiom either"',
      "theorem t : True := by",
      "  sorry -- real",
      "end D",
      "",
    ].join("\n"));
    expect(await bankSoundnessIssues(leanDir, root)).toEqual(["sorry in CausalSmith/Stat/Demo/T.lean:5"]);
  });
});
