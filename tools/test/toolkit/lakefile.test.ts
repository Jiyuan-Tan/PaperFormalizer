import { readFileSync } from "node:fs";
import path from "node:path";
import { describe, expect, it } from "vitest";
import {
  assertToolkitLakefile, parseLakefileLean, parseLakefileToml, readLakefileTargets, toolkitTemplateDir,
} from "../../src/toolkit/lakefile.js";
import { tk } from "./helpers.js";

const ROOT = path.resolve("/tk");
const LIBS_ONLY = 'name = "t"\n\n[[require]]\nname = "Causalean"\npath = "../AutoID"\n\n[[lean_lib]]\nname = "Toolkit"\n\n[[lean_lib]]\nname = "Papers"\n';
const io = (files: Record<string, string>) => ({
  exists: (p: string) => p in files,
  read: (p: string) => { if (!(p in files)) throw new Error(`ENOENT ${p}`); return files[p]; },
});

describe("toolkit lakefile targets", () => {
  it("parses the shipped template: both libs, the index extractor and the three exes", () => {
    const text = readFileSync(path.join(toolkitTemplateDir(), "lakefile.toml"), "utf8");
    const t = parseLakefileToml(text);
    expect([...t.libs].sort()).toEqual(["Papers", "TheoremCheckerIndexCore", "Toolkit"]);
    expect([...t.exes].sort()).toEqual(["candidate_scan", "paper_index", "toolkit_index"]);
    // A `[[require]]` (mathlib; the optional Causalean, commented out) is not a lib.
    expect(t.libs.has("mathlib")).toBe(false);
    expect(t.libs.has("Causalean")).toBe(false);
    expect(() => assertToolkitLakefile(tk(ROOT), io({ [path.join(ROOT, "lakefile.toml")]: text }))).not.toThrow();
  });

  it("fails closed on missing exes, a missing lib, and no lakefile at all", () => {
    const files = { [path.join(ROOT, "lakefile.toml")]: LIBS_ONLY };
    expect(() => assertToolkitLakefile(tk(ROOT), io(files))).toThrow(
      /missing lean_exe paper_index, lean_exe toolkit_index[\s\S]*templates[\\/]toolkit[\\/]lakefile\.toml/,
    );
    const noPapers = 'name = "t"\n[[lean_lib]]\nname = "Toolkit"\n[[lean_exe]]\nname = "paper_index"\n[[lean_exe]]\nname = "toolkit_index"\n';
    expect(() => assertToolkitLakefile(tk(ROOT), io({ [path.join(ROOT, "lakefile.toml")]: noPapers }))).toThrow(/missing lean_lib Papers/);
    expect(() => assertToolkitLakefile(tk(ROOT), io({}))).toThrow(/has no lakefile\.toml or lakefile\.lean/);
  });

  it("reads lakefile.lean targets, ignoring comments", () => {
    const lean = 'import Lake\nopen Lake DSL\npackage t\nlean_lib Toolkit\nlean_lib «Papers»\n-- lean_exe toolkit_index\nlean_exe paper_index where\n  root := `PaperIndex\n';
    const t = parseLakefileLean(lean);
    expect([...t.libs].sort()).toEqual(["Papers", "Toolkit"]);
    expect([...t.exes]).toEqual(["paper_index"]);
    const r = readLakefileTargets(ROOT, io({ [path.join(ROOT, "lakefile.lean")]: lean }));
    expect(r.file).toBe(path.join(ROOT, "lakefile.lean"));
  });
});
