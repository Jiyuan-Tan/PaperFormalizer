import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { afterEach, describe, expect, it } from "vitest";
import { attributeErrors, compileGuarded, paperSideFailure, sourceFailureNote, treeSha, type CompileTex } from "../../src/verify/annotated_compile.js";
import { lintAnnotated, lintAnnotatedTex } from "../../src/verify/render_check.js";

const dump = readFileSync(path.join(path.dirname(fileURLToPath(import.meta.url)), "fixtures/overfull_box_bang.log"), "latin1");

const dirs: string[] = [];
afterEach(() => {
  for (const d of dirs.splice(0)) rmSync(d, { recursive: true, force: true });
});

function run(status: "passed" | "failed", logTail = dump.split("\n").slice(-40).join("\n"), paperSide = false): string {
  const dir = mkdtempSync(path.join(tmpdir(), "render-check-"));
  dirs.push(dir);
  mkdirSync(path.join(dir, "annotated"));
  mkdirSync(path.join(dir, "logs"));
  writeFileSync(path.join(dir, "annotated/main.tex"), "\\documentclass{article}\\begin{document}x\\end{document}\n");
  writeFileSync(path.join(dir, "annotated/main.log"), dump);
  writeFileSync(path.join(dir, "logs/annotated_compile.json"), JSON.stringify({ status, reason: status === "failed" ? "pdflatex exited with 1" : "", log_tail: logTail, paper_side: paperSide }));
  return dir;
}

describe("lintAnnotated — the compile's exit status decides", () => {
  it("a passed compile is clean even when its log holds a line starting with '! '", async () => {
    expect(await lintAnnotated(run("passed"))).toEqual([]);
  });
  it("a passed record from another compile does not stand for this log", async () => {
    expect((await lintAnnotated(run("passed", "an earlier log"))).map((d) => d.block)).toContain("pdflatex (main.log)");
  });
  it("a failed compile reports the log's error lines", async () => {
    expect((await lintAnnotated(run("failed"))).map((d) => d.block)).toContain("pdflatex (main.log)");
  });
  it("a failed compile located in the paper's own TeX is not the renderer's", async () => {
    expect(await lintAnnotated(run("failed", undefined, true))).toEqual([]);
  });
  it("a paper-side record stands for a rendered tree whose compile the guard skipped", async () => {
    const dir = run("failed", "no log", true);
    rmSync(path.join(dir, "annotated/main.log"));
    const rec = path.join(dir, "logs/annotated_compile.json");
    const sha = await treeSha(path.join(dir, "annotated"), { renderedOnly: true });
    writeFileSync(rec, JSON.stringify({ ...JSON.parse(readFileSync(rec, "utf8")), tree_sha256: sha }));
    writeFileSync(path.join(dir, "annotated/ANNOTATIONS.md"), "# index\n");
    expect(await lintAnnotated(dir)).toEqual([]);
    // what an earlier compile left behind (endnotes, hyperref) is not the rendered tree
    writeFileSync(path.join(dir, "annotated/main.ent"), "notes\n");
    writeFileSync(path.join(dir, "annotated/main.out"), "bookmarks\n");
    expect(await lintAnnotated(dir)).toEqual([]);
    writeFileSync(path.join(dir, "annotated/main.tex"), "changed\n");
    expect((await lintAnnotated(dir)).map((d) => d.block)).toContain("pdflatex");
  });
  it("a paper-side record from another compile does not stand for this log", async () => {
    expect((await lintAnnotated(run("failed", "an earlier log", true))).map((d) => d.block)).toContain("pdflatex (main.log)");
  });
  it("a missing \\input of the paper is paper-side though the macro block follows it", () => {
    const tex = ["\\documentclass{article}", "\\input{tcilatex}", "% PaperFormalizer annotation macros", "\\newcommand{\\vsNote}[1]{#1}", "\\begin{document}"].join("\n");
    const log = "! LaTeX Error: File `tcilatex.tex' not found.\n./main.tex:2: Emergency stop.\n";
    expect(paperSideFailure(log, { "main.tex": tex })).toBe(true);
    // an error just after our block is still ours
    expect(paperSideFailure("./main.tex:5: Undefined control sequence.\n", { "main.tex": tex })).toBe(false);
  });
});

describe("a compile error the paper's unmodified source has too", () => {
  const already = (n: number): string => `./main.tex:${n}: LaTeX Error: Command \\theHalgorithm already defined.`;
  const undefinedAt = (n: number): string => `./main.tex:${n}: Undefined control sequence.`;

  it("attributeErrors: the same error on a shifted line is the source's; one the source lacks is not", () => {
    expect(attributeErrors([already(90)], [already(88)])).toEqual({ source: [already(90)], own: [] });
    expect(attributeErrors([undefinedAt(120)], [already(88)])).toEqual({ source: [], own: [undefinedAt(120)] });
    expect(attributeErrors([already(90), undefinedAt(120)], [already(88)])).toEqual({ source: [already(90)], own: [undefinedAt(120)] });
    // one more occurrence than the source has: which is new cannot be told
    expect(attributeErrors([undefinedAt(12), undefinedAt(40)], [undefinedAt(10)])).toEqual({ source: [], own: [undefinedAt(12), undefinedAt(40)] });
    expect(attributeErrors([already(90)], [])).toEqual({ source: [], own: [already(90)] });
  });

  /** A run whose source redefines a command the installation's packages define, annotated with `extra`. */
  function seeded(extra = ""): { runDir: string; args: { recFile: string; dir: string; mainFile: string; sourceDir: string; log: (m: string) => void }; logs: string[] } {
    const runDir = mkdtempSync(path.join(tmpdir(), "render-base-"));
    dirs.push(runDir);
    for (const d of ["source", "annotated", "logs"]) mkdirSync(path.join(runDir, d));
    const source = "\\documentclass{article}\n\\newcommand{\\theHalgorithm}{x}\n\\begin{document}\nText.\n\\end{document}\n";
    writeFileSync(path.join(runDir, "source/main.tex"), source);
    writeFileSync(path.join(runDir, "annotated/main.tex"), source.replace("\\newcommand", "\\usepackage{xcolor}% added by PaperFormalizer\n\\newcommand").replace("Text.", `Text.${extra}`));
    const logs: string[] = [];
    return { runDir, logs, args: { recFile: path.join(runDir, "logs/annotated_compile.json"), dir: path.join(runDir, "annotated"), mainFile: "main.tex", sourceDir: path.join(runDir, "source"), log: (m) => logs.push(m) } };
  }
  /** pdflatex, faked: an error at every `\theHalgorithm` definition (unless `sound`) and every `\vsBroken`. */
  const fake = (calls: string[], sound = false): CompileTex => async ({ dir, mainFile }) => {
    calls.push(dir);
    const errors = readFileSync(path.join(dir, mainFile), "utf8").split("\n").flatMap((l, i) => [
      ...(l.includes("\\theHalgorithm") && !sound ? [already(i + 1)] : []),
      ...(l.includes("\\vsBroken") ? [undefinedAt(i + 1)] : []),
    ]);
    writeFileSync(path.join(dir, "main.log"), `This is pdfTeX\n${errors.join("\n")}\n`);
    return errors.length > 0
      ? { status: "failed", tool: "pdflatex", pdf: null, log_tail: `This is pdfTeX\n${errors.join("\n")}\n`, reason: "pdflatex exited with 1" }
      : { status: "passed", tool: "pdflatex", pdf: "main.pdf", log_tail: "This is pdfTeX\n\n", reason: "" };
  };

  it("both fail the same way: no render defect, a note; the source is compiled once, in a scratch copy", async () => {
    const { runDir, args, logs } = seeded();
    const calls: string[] = [];
    const r = await compileGuarded({ ...args, compile: fake(calls) });
    expect(r.source_failure).toEqual({ error: "main.tex:2: LaTeX Error: Command \\theHalgorithm already defined.", lines: [already(3)], only: true });
    expect(sourceFailureNote(r, "annotated")).toBe("the paper's own source does not compile here (pdflatex: main.tex:2: LaTeX Error: Command \\theHalgorithm already defined.); the annotated PDF could not be built — the annotated TeX and the page are unaffected");
    expect(logs.join("\n")).toContain("the paper's own source does not compile here");
    expect(await lintAnnotated(runDir)).toEqual([]);
    expect(readFileSync(path.join(runDir, "source/main.tex"), "utf8")).not.toContain("PaperFormalizer");
    expect(calls).toHaveLength(2);
    expect(calls[1]).not.toContain(runDir);
    expect(existsSync(calls[1]!)).toBe(false);
    // another annotated tree of the same source: the source is not compiled again
    writeFileSync(path.join(runDir, "annotated/main.tex"), `${readFileSync(path.join(runDir, "annotated/main.tex"), "utf8")}% again\n`);
    await compileGuarded({ ...args, compile: fake(calls) });
    expect(calls).toHaveLength(3);
    expect(await lintAnnotated(runDir)).toEqual([]);
  });

  it("an error only the annotated copy has stays a render defect; the source's own beside it does not", async () => {
    const { runDir, args } = seeded("\\vsBroken");
    const r = await compileGuarded({ ...args, compile: fake([]) });
    expect(r.source_failure).toMatchObject({ lines: [already(3)], only: false });
    expect(sourceFailureNote(r, "annotated")).toBeNull();
    expect(await lintAnnotated(runDir)).toEqual([{ node: null, block: "pdflatex (main.log)", reason: undefinedAt(5) }]);
  });

  it("the source compiles and the annotated copy does not: a render defect, as without a baseline", async () => {
    const { runDir, args } = seeded("\\vsBroken");
    const r = await compileGuarded({ ...args, compile: fake([], true) });
    expect(r.source_failure).toBeUndefined();
    expect(await lintAnnotated(runDir)).toEqual([{ node: null, block: "pdflatex (main.log)", reason: undefinedAt(5) }]);
  });
});

// The finding: a step quoting the paper's comment line `%was (\delta^{+})$.` was counted an odd number of $.
describe("the odd-$ scan of a block", () => {
  it("does not count a $ inside a % comment", () => {
    const block = "\\vsStep{set $x''=y$\n%was (\\delta^{+})$.\nIn both cases $a=b$.}";
    expect(lintAnnotatedTex("m.tex", block)).toEqual([]);
    expect(lintAnnotatedTex("m.tex", "\\vsStep{an $x}")).toHaveLength(1);
  });
});
