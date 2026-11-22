import { mkdtemp, mkdir, writeFile, rm } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { listStudyModuleFiles } from "../../src/substrate/pipeline.js";

describe("a study's module files", () => {
  let dir = "";
  afterEach(async () => { if (dir) await rm(dir, { recursive: true, force: true }); });
  it("leave out directories whose name starts with '.' (a probe's .scratch/), at any depth", async () => {
    dir = await mkdtemp(path.join(os.tmpdir(), "staging-files-"));
    for (const d of [".scratch", "Sub", "Sub/.probe"]) await mkdir(path.join(dir, d), { recursive: true });
    for (const f of ["Main.lean", ".scratch/Axioms.lean", "Sub/Part.lean", "Sub/.probe/X.lean", "notes.md"]) await writeFile(path.join(dir, f), "");
    expect((await listStudyModuleFiles(dir)).map((f) => path.relative(dir, f))).toEqual(["Main.lean", "Sub/Part.lean"]);
  });
});
