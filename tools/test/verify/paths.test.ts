import path from "node:path";
import { describe, expect, it } from "vitest";
import {
  artifactPath,
  canonicalLeanSubdir,
  formalizationDir,
  isPaperLeanSubdir,
  leanModulePrefix,
  slugToPascal,
  verifyRunDir,
} from "../../src/paths.js";

const ROOT = path.join(path.sep, "home", "me", "my-toolkit");
const QID = "my_paper";

describe("run paths (wave 3a: runs/<slug> under the toolkit)", () => {
  it("puts a run under <toolkit>/runs/<slug>/", () => {
    const expected = path.join(ROOT, "runs", QID);
    expect(verifyRunDir(ROOT, QID)).toBe(expected);
    expect(formalizationDir(ROOT, QID)).toBe(expected);
    expect(artifactPath(ROOT, QID, "discovery", "core.json")).toBe(path.join(expected, "discovery", "core.json"));
    expect(artifactPath(ROOT, QID, "root", "state.json")).toBe(path.join(expected, "state.json"));
  });

  it("refuses a run id that would escape runs/", () => {
    for (const bad of ["", ".", "..", "a/b", "a\\b", "../x", "/abs"]) {
      expect(() => formalizationDir(ROOT, bad)).toThrow(/Invalid qid slug/);
    }
  });

  it("puts the Lean under <papers_lib>/<Pascal> with module prefix and barrel", () => {
    expect(slugToPascal("my_paper")).toBe("MyPaper");
    expect(slugToPascal("lee_bounds_2009")).toBe("LeeBounds2009");
    expect(slugToPascal("2026_note")).toBe("Paper2026Note");
    expect(canonicalLeanSubdir(QID)).toBe("Papers/MyPaper");
    expect(canonicalLeanSubdir(QID, "Output")).toBe("Output/MyPaper");
    expect(leanModulePrefix("Papers/MyPaper")).toBe("Papers.MyPaper");
    expect(isPaperLeanSubdir(QID, "Papers/MyPaper")).toBe(true);
    expect(isPaperLeanSubdir(QID, "Papers/MyPaper_Verify")).toBe(false);
    expect(isPaperLeanSubdir(QID, "CausalSmith/Verify/MyPaper")).toBe(false);
  });
});
