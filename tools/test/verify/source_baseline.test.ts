import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { COMPILE_RECIPE, sourceBaseline } from "../../src/verify/annotated_compile.js";

const dirs: string[] = [];
afterEach(async () => {
  for (const d of dirs.splice(0)) await rm(d, { recursive: true, force: true });
});

describe("the source's compile baseline", () => {
  it("is kept under the compile's recipe: a record of an older recipe is compiled again", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "baseline-"));
    dirs.push(root);
    const sourceDir = path.join(root, "source");
    await (await import("node:fs/promises")).mkdir(sourceDir);
    await writeFile(path.join(sourceDir, "main.tex"), "\\documentclass{article}\\begin{document}x\\end{document}\n", "utf8");
    const cacheFile = path.join(root, "logs", "source_compile.json");
    let calls = 0;
    const compile = async () => { calls += 1; return { status: "passed" as const, tool: "pdflatex", pdf: "main.pdf", log_tail: "", reason: "" }; };
    const first = await sourceBaseline({ sourceDir, cacheFile, mainFile: "main.tex", compile });
    expect(first.recipe).toBe(COMPILE_RECIPE);
    expect(first.undefined_citations).toEqual([]);
    await sourceBaseline({ sourceDir, cacheFile, mainFile: "main.tex", compile });
    expect(calls).toBe(1); // kept
    const rec = JSON.parse(await readFile(cacheFile, "utf8")) as Record<string, unknown>;
    delete rec.recipe; // a record written before the bibliography was built
    await writeFile(cacheFile, JSON.stringify(rec), "utf8");
    await sourceBaseline({ sourceDir, cacheFile, mainFile: "main.tex", compile });
    expect(calls).toBe(2);
  });
});
