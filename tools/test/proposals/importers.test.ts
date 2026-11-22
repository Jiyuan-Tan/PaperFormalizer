// Papers that import another paper: which files, and which of its declarations they use.
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { findImporters, importedBy } from "../../src/proposals/importers.js";
import { referencedNames, rewriteReferences } from "../../src/proposals/move.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

async function papers(files: Record<string, string>) {
  const root = await mkdtemp(path.join(os.tmpdir(), "importers-"));
  tmp.push(root);
  for (const [rel, text] of Object.entries(files)) {
    await mkdir(path.dirname(path.join(root, rel)), { recursive: true });
    await writeFile(path.join(root, rel), text);
  }
  return { toolkitRoot: root, papersLib: "Papers" };
}

describe("the papers that use a paper's declarations", () => {
  it("lists the files of other papers that name the paper — never its own, a tmp/ scratch file, or a paper whose name only starts the same", async () => {
    const cfg = await papers({
      "Papers/Frz.lean": "import Papers.Frz.Main\n",
      "Papers/Frz/Main.lean": "namespace Papers.Frz\ntheorem bm_incr : True := trivial\ntheorem bm_var : True := trivial\nend Papers.Frz\n",
      "Papers/Emp/Use.lean": "module\npublic import Papers.Frz.Main\nopen Papers.Frz\ntheorem x : True := bm_incr\n",
      "Papers/Emp/Plain.lean": "-- see Papers.Frz.Main\ntheorem y : True := trivial\n",
      "Papers/Emp/tmp/Scratch.lean": "import Papers.Frz.Main\ntheorem z : True := Papers.Frz.bm_var\n",
      "Papers/Kit/All.lean": "import Papers.Frz\ntheorem w : True := Papers.Frz.bm_var\n",
      "Papers/FrzOther/A.lean": "import Papers.FrzOther.B\n",
    });
    const imp = await findImporters(cfg, "Papers.Frz");
    // Plain.lean names the paper in a comment only: listed, and the name resolution finds no use in it
    expect(imp.files.map((f) => path.relative(cfg.toolkitRoot, f))).toEqual(["Papers/Emp/Plain.lean", "Papers/Emp/Use.lean", "Papers/Kit/All.lean"]);
    expect(imp.declared.get("Papers.Emp")).toEqual(new Set(["x", "y"]));
    expect(await importedBy(cfg, "Papers.Frz", ["Papers.Frz.bm_incr", "Papers.Frz.bm_var", "Papers.Frz.unused"]))
      .toEqual(new Map([["Papers.Frz.bm_incr", ["Papers.Emp"]], ["Papers.Frz.bm_var", ["Papers.Kit"]]]));
    expect(await importedBy({ ...cfg, toolkitRoot: path.join(cfg.toolkitRoot, "nowhere") }, "Papers.Frz", ["Papers.Frz.bm_var"])).toEqual(new Map());
  });

  it("resolves names as the move's rewrite does: namespaces, opens, a trailing field; comments and other namespaces do not count", () => {
    const names = new Set(["Papers.Frz.Bm", "Papers.Frz.bm_incr", "Papers.Frz.Sub.helper"]);
    expect(referencedNames("open Papers.Frz\n-- Papers.Frz.Sub.helper\ndef f (b : Bm) := b.drift\ntheorem t := Sub.helper\n", names))
      .toEqual(new Set(["Papers.Frz.Bm", "Papers.Frz.Sub.helper"]));
    expect(referencedNames("namespace Papers.Frz\ntheorem t := bm_incr\nend Papers.Frz\ntheorem u := Other.bm_incr\n", names)).toEqual(new Set(["Papers.Frz.bm_incr"]));
    expect(referencedNames("theorem u := bm_incr\n", names)).toEqual(new Set());
  });
});

describe("the audit's cases", () => {
  it("a file that reaches the paper through its own paper's modules (a transitive import) is found", async () => {
    const cfg = await papers({
      "Papers/Frz/Main.lean": "module\nnamespace Papers.Frz\ntheorem bm_incr : True := trivial\nend Papers.Frz\n",
      "Papers/Emp/A.lean": "module\npublic import Papers.Frz.Main\n",
      "Papers/Emp/B.lean": "module\npublic import Papers.Emp.A\nopen Papers.Frz\ntheorem x : True := bm_incr\n",
    });
    expect((await findImporters(cfg, "Papers.Frz")).files.map((f) => path.relative(cfg.toolkitRoot, f))).toEqual(["Papers/Emp/A.lean", "Papers/Emp/B.lean"]);
    expect(await importedBy(cfg, "Papers.Frz", ["Papers.Frz.bm_incr"])).toEqual(new Map([["Papers.Frz.bm_incr", ["Papers.Emp"]]]));
  });

  it("a name the other paper declares itself shadows the moving paper's: its header and its uses stay", async () => {
    const text = "namespace Papers.Emp\nopen Papers.Frz\ndef clipTime := 1\ntheorem t : clipTime = 1 := rfl\ntheorem u : pathNorm = 2 := rfl\nend Papers.Emp\n";
    const shadow = new Set(["Papers.Emp.clipTime", "Papers.Emp.t", "Papers.Emp.u"]);
    const renames = new Map([["Papers.Frz.clipTime", "Toolkit.X.clipTime"], ["Papers.Frz.pathNorm", "Toolkit.X.pathNorm"]]);
    expect(referencedNames(text, new Set(renames.keys()), shadow)).toEqual(new Set(["Papers.Frz.pathNorm"]));
    const r = rewriteReferences(text, renames, { shadow });
    expect(r.text).toContain("def clipTime := 1\ntheorem t : clipTime = 1 := rfl");
    expect(r.text).toContain("theorem u : Toolkit.X.pathNorm = 2 := rfl");
    // the shadowing paper is read whole: a name declared in another of its files shadows too
    const cfg = await papers({
      "Papers/Frz/Main.lean": "namespace Papers.Frz\ndef clipTime := 1\nend Papers.Frz\n",
      "Papers/Emp/Defs.lean": "namespace Papers.Emp\ndef clipTime := 3\nend Papers.Emp\n",
      "Papers/Emp/Use.lean": "import Papers.Frz.Main\nimport Papers.Emp.Defs\nnamespace Papers.Emp\nopen Papers.Frz\ntheorem t : clipTime = 3 := rfl\nend Papers.Emp\n",
    });
    expect(await importedBy(cfg, "Papers.Frz", ["Papers.Frz.clipTime"])).toEqual(new Map());
  });
});
