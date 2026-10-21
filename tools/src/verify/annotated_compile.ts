/**
 * Compiling the annotated paper (`annotated_paper.ts`): pdflatex / latexmk, and the cost guard —
 * a tree whose byte-identical copy last failed on the paper's own TeX is not compiled again — and
 * the baseline: a failure the paper's UNMODIFIED source has too (an old paper on a new TeX
 * installation) is the source's, not the annotation's (`sourceBaseline`, `attributeErrors`).
 */
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { cp, mkdir, mkdtemp, readdir, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { execFileTracked } from "../shared/child_registry.js";
import { findExecutable } from "../shared/program.js";

export interface CompileResult {
  status: "passed" | "failed" | "skipped";
  tool: string | null;
  /** Relative to the annotated dir, when a PDF was written. */
  pdf: string | null;
  log_tail: string;
  reason: string;
  /** A failed compile whose errors the paper's unmodified source has too (`compileGuarded`): the
   * source's first error, the error lines of this compile's log that are the source's, and whether
   * they are all of them (`only`: nothing the annotation added fails). */
  source_failure?: { error: string; lines: string[]; only: boolean };
}
export type CompileTex = (args: { dir: string; mainFile: string; timeoutMs: number }) => Promise<CompileResult>;

// `max_print_line`: an error line is not wrapped, so it reads the same wherever its line number falls.
const exec = (cmd: string, args: string[], opts: { cwd?: string; timeout?: number; maxBuffer?: number }) =>
  execFileTracked("latex", cmd, args, { ...opts, env: { ...process.env, max_print_line: "10000" } });

const onPath = (name: string): string | null => findExecutable(name, { nativeOnly: true });

/** pdflatex twice (else latexmk), `-interaction=nonstopmode` (no `-halt-on-error`: the log holds
 * every error up to a fatal one), within `timeoutMs` overall. A paper that ships no `.bbl` gets its
 * bibliography built after the first pass, as LaTeX's own order has it: bibtex when the `.aux` names
 * a `\bibdata`, biber when biblatex wrote a `.bcf`; then pdflatex twice more. A bibliography tool
 * that fails is noted in `reason`, not a failure of the compile (latexmk does all this itself). */
export const compileTex: CompileTex = async ({ dir, mainFile, timeoutMs }) => {
  const pdflatex = onPath("pdflatex");
  const latexmk = onPath("latexmk");
  if (!pdflatex && !latexmk) return { status: "skipped", tool: null, pdf: null, log_tail: "", reason: "no pdflatex or latexmk on PATH" };
  const base = mainFile.replace(/\.tex$/i, "");
  const pdf = `${base}.pdf`;
  const at = (ext: string) => path.join(dir, `${base}${ext}`);
  const shipsBbl = existsSync(at(".bbl"));
  const started = Date.now();
  const tool = pdflatex ? "pdflatex" : "latexmk";
  const pass = ["-interaction=nonstopmode", "-file-line-error", mainFile];
  let failure: string | null = null;
  let note = "";
  // the time of one more pass is given when the bibliography is built (two passes follow it, not one)
  let budget = timeoutMs;
  const left = () => budget - (Date.now() - started);
  const run = async (cmd: string, args: string[]): Promise<boolean> => {
    if (left() <= 0) {
      failure = `timed out after ${Math.round(budget / 1000)} s`;
      return false;
    }
    try {
      await exec(cmd, args, { cwd: dir, timeout: left(), maxBuffer: 64 * 1024 * 1024 });
    } catch (err) {
      const e = err as { killed?: boolean; code?: number | string };
      failure = e.killed ? `timed out after ${Math.round(budget / 1000)} s` : `${path.basename(cmd)} exited with ${String(e.code ?? "an error")}`;
      if (e.killed) return false;
    }
    return true;
  };
  if (!pdflatex) await run(latexmk!, ["-pdf", "-interaction=nonstopmode", mainFile]);
  else if (await run(pdflatex, pass)) {
    const aux = existsSync(at(".aux")) ? await readFile(at(".aux"), "latin1") : "";
    const bib = shipsBbl ? null : existsSync(at(".bcf")) ? "biber" : /\\bibdata\{/u.test(aux) ? "bibtex" : null;
    const bibTool = bib ? onPath(bib) : null;
    if (bib && !bibTool) note = `the bibliography was not built: no ${bib} on PATH`;
    if (bibTool) {
      budget += Date.now() - started;
      const before = failure;
      if (!(await run(bibTool, [base]))) note = `${bib} ${failure}`; // out of time: the failure stands
      else {
        if (failure !== before) note = `${bib} reported errors (see ${path.basename(base)}.blg); the bibliography may be incomplete`;
        failure = before;
      }
    }
    // the compile is the last pass: an error of an earlier one that a later pass no longer has (a
    // shipped .bbl read before the .aux exists, a reference not yet resolved) was transient
    for (const _ of bibTool ? [0, 1] : [0]) {
      if ((failure as string | null)?.startsWith("timed out")) break;
      failure = null;
      if (!(await run(pdflatex, pass))) break;
    }
  }
  const logFile = path.join(dir, path.dirname(mainFile), `${path.basename(base)}.log`);
  const logTail = existsSync(logFile) ? (await readFile(logFile, "latin1")).split("\n").slice(-40).join("\n") : "";
  const hasPdf = existsSync(path.join(dir, pdf));
  if (!failure && hasPdf) return { status: "passed", tool, pdf, log_tail: logTail, reason: note };
  return { status: "failed", tool, pdf: hasPdf ? pdf : null, log_tail: logTail, reason: [failure ?? "no PDF was written", note].filter(Boolean).join("; ") };
};

/** `runs/<slug>/<this>`: the last compile of the annotated tree (outside `annotated/`, which is
 * rebuilt each time). The cost guard reads it. */
export const ANNOTATED_COMPILE_RECORD = "logs/annotated_compile.json";

interface CompileRecord {
  tree_sha256: string;
  status: CompileResult["status"];
  tool: string | null;
  reason: string;
  /** The failure lies in the paper's own TeX (not in anything the annotation inserted). */
  paper_side: boolean;
  source_failure?: CompileResult["source_failure"];
  log_tail: string;
  at: string;
}

/** Files a compile (or the index written after it) adds to the rendered tree. */
const COMPILE_OUTPUT = /(?:^ANNOTATIONS\.md|\.(?:log|aux|pdf|out|toc|lof|lot|loa|blg|fls|fdb_latexmk|synctex\.gz|nav|snm|vrb|bcf|run\.xml|ent|idx|ind|ilg|brf|spl))$/i;

/** sha256 over every file of the tree (path and bytes), in path order. `renderedOnly`: leave out
 * what a compile and the index add, so a tree read after them hashes as it did before the compile. */
export async function treeSha(dir: string, opts: { renderedOnly?: boolean } = {}): Promise<string> {
  const h = createHash("sha256");
  const walk = async (d: string, rel: string): Promise<void> => {
    const entries = (await readdir(d, { withFileTypes: true })).sort((a, b) => a.name.localeCompare(b.name));
    for (const e of entries) {
      if (e.isDirectory()) await walk(path.join(d, e.name), `${rel}${e.name}/`);
      else if (e.isFile()) {
        if (opts.renderedOnly && COMPILE_OUTPUT.test(`${rel}${e.name}`)) continue;
        h.update(`${rel}${e.name}\0`);
        h.update(await readFile(path.join(d, e.name)));
        h.update("\0");
      }
    }
  };
  await walk(dir, "");
  return h.digest("hex");
}

/**
 * Did a failed compile fail on the paper's own TeX? Yes when the log names at least one error
 * (`file:line:`, from `-file-line-error`) and none is ours: none mentions xcolor or a `\vs` macro,
 * and none lies on or up to two lines after anything the annotation inserted (a `\vs` macro or a
 * line marked PaperFormalizer) — TeX reports an error at or after the line causing it, so a block
 * inserted just after the paper's failing line is not the cause. A timeout or an error the log does
 * not locate is not paper-side.
 */
export function paperSideFailure(logText: string, files: Record<string, string>): boolean {
  const errors = [...logText.matchAll(/^(?:\.\/)?([^\s:][^:\n]*\.(?:tex|sty|cls|bbl|bib)):(\d+): (.*)$/gm)];
  if (errors.length === 0) return false;
  for (const m of errors) {
    const [, file, lineNo, msg] = m;
    if (/xcolor|\\vs[A-Z]|PaperFormalizer/.test(msg!)) return false;
    const text = files[file!.replace(/^\.\//, "")];
    if (text === undefined) continue; // a package or class file of the paper
    const lines = text.split("\n");
    const at = Number(lineNo) - 1;
    const window = lines.slice(Math.max(0, at - 2), at + 1).join("\n");
    if (/\\vs[A-Z]|PaperFormalizer/.test(window)) return false;
  }
  return true;
}

/** pdflatex errors in a log (`-file-line-error` lines, and `! ` lines). Pure. */
export function latexLogErrors(log: string): string[] {
  const out: string[] = [];
  for (const line of log.split("\n")) {
    if (/^(?:\.\/)?[^\s:][^:\n]*\.(?:tex|sty|cls|bbl):\d+: /u.test(line) || /^! /u.test(line)) out.push(line.trim());
  }
  return [...new Set(out)];
}

/** An error line without its line number (`./f.tex:90: msg` → `f.tex: msg`): what the annotation
 * inserts shifts the lines of the paper's own errors. Pure. */
export const errorKey = (line: string): string => line.trim().replace(/^(?:\.\/)?([^\s:][^:\n]*\.(?:tex|sty|cls|bbl)):\d+: /u, "$1: ");

/**
 * The errors of a compile (`latexLogErrors`) set against those of the unmodified source: `source`
 * the ones the source has too (same file and message, at whatever line), `own` the rest. An error
 * occurring more often than in the source is `own` at every occurrence (which one is new cannot be
 * told). Pure.
 */
export function attributeErrors(errors: readonly string[], baseline: readonly string[]): { source: string[]; own: string[] } {
  const count = (ls: readonly string[]): Map<string, number> => {
    const n = new Map<string, number>();
    for (const l of ls) n.set(errorKey(l), (n.get(errorKey(l)) ?? 0) + 1);
    return n;
  };
  const [here, base] = [count(errors), count(baseline)];
  const source: string[] = [];
  const own: string[] = [];
  for (const l of errors) (here.get(errorKey(l))! <= (base.get(errorKey(l)) ?? 0) ? source : own).push(l);
  return { source, own };
}

/** Beside a compile record: the compile of the paper's unmodified source (`sourceBaseline`). */
export const SOURCE_COMPILE_RECORD = "source_compile.json";

/** The compile's recipe: a source baseline kept under another (2: the bibliography is built between
 * the passes; 3: the record names the citations it leaves undefined) is compiled again. */
export const COMPILE_RECIPE = 3;

/** The citation keys a LaTeX log reports undefined. Pure. */
export const undefinedCitations = (log: string): string[] => [...new Set([...log.replace(/\n/gu, "").matchAll(/Citation `([^']*)' on page/gu)].map((m) => m[1]!))];

interface SourceRecord {
  source_sha256: string;
  main: string;
  recipe?: number;
  status: CompileResult["status"];
  tool: string | null;
  reason: string;
  /** `latexLogErrors` of its log, when it failed. */
  errors: string[];
  /** The citations its compile leaves undefined (`undefinedCitations`). */
  undefined_citations?: string[];
  at: string;
}

/**
 * Compile the paper's unmodified source, in a scratch copy, with the compiler the annotated tree is
 * compiled with. Done once per source: the result is kept in `cacheFile` under the source tree's
 * hash (a timeout, or no compiler, is not kept).
 */
export async function sourceBaseline(a: { sourceDir: string; cacheFile: string; mainFile: string; compile: CompileTex }): Promise<SourceRecord> {
  const sha = await treeSha(a.sourceDir);
  try {
    const prior = existsSync(a.cacheFile) ? (JSON.parse(await readFile(a.cacheFile, "utf8")) as SourceRecord) : null;
    if (prior && prior.source_sha256 === sha && prior.main === a.mainFile && prior.recipe === COMPILE_RECIPE) return prior;
  } catch {
    // an unreadable record: compile again
  }
  const scratch = await mkdtemp(path.join(os.tmpdir(), "tc-source-"));
  try {
    await cp(a.sourceDir, scratch, { recursive: true, dereference: true });
    const r = await a.compile({ dir: scratch, mainFile: a.mainFile, timeoutMs: 120_000 });
    const logFile = path.join(scratch, a.mainFile.replace(/\.tex$/i, ".log"));
    const logText = existsSync(logFile) ? await readFile(logFile, "latin1") : r.log_tail;
    const errors = r.status === "failed" ? latexLogErrors(logText) : [];
    const rec: SourceRecord = { source_sha256: sha, main: a.mainFile, recipe: COMPILE_RECIPE, status: r.status, tool: r.tool, reason: r.reason, errors, undefined_citations: undefinedCitations(logText), at: new Date().toISOString() };
    if (r.status !== "skipped" && !/timed out/.test(r.reason)) {
      await mkdir(path.dirname(a.cacheFile), { recursive: true });
      await writeFile(a.cacheFile, `${JSON.stringify(rec, null, 2)}\n`, "utf8");
    }
    return rec;
  } finally {
    await rm(scratch, { recursive: true, force: true });
  }
}

/** What a compile failure of the source's own says to the reader (null: none, or errors beyond the
 * source's remain). `what`: the paper compiled — "annotated", "corrected". Pure. */
export function sourceFailureNote(c: CompileResult, what: string): string | null {
  return c.status !== "passed" && c.source_failure?.only
    ? `the paper's own source does not compile here (${c.tool}: ${c.source_failure.error}); the ${what} PDF ${c.pdf ? "was written past the errors and may be incomplete" : "could not be built"} — the ${what} TeX and the page are unaffected`
    : null;
}

/**
 * Compile the annotated tree, unless the previous compile of the very same tree failed on the
 * paper's own TeX (it would fail again: the cost guard). Every compile run is recorded in
 * `ANNOTATED_COMPILE_RECORD`. `sourceDir`: the unmodified source the tree was written from — a failed
 * compile is set against its own (`sourceBaseline`): the errors both have are the source's
 * (`source_failure`), and a failure with no other error is paper-side. A source that compiles, or
 * shares no error with the tree, changes nothing.
 */
export async function compileGuarded(a: { recFile: string; dir: string; mainFile: string; compile: CompileTex; sourceDir?: string; log: (m: string) => void }): Promise<CompileResult> {
  const recFile = a.recFile;
  // (what an earlier compile left in the tree is not the tree: the record is read against a tree
  // hashed the same way after this compile, `lintAnnotated`)
  const sha = await treeSha(a.dir, { renderedOnly: true });
  let prior: CompileRecord | null = null;
  try {
    prior = existsSync(recFile) ? (JSON.parse(await readFile(recFile, "utf8")) as CompileRecord) : null;
  } catch {
    prior = null;
  }
  if (prior && prior.tree_sha256 === sha && prior.status === "failed" && prior.paper_side) {
    a.log("annotated paper: compile skipped — the previous compile of this same annotated TeX failed on the paper's own TeX");
    return {
      status: "skipped",
      tool: prior.tool,
      pdf: null,
      log_tail: prior.log_tail,
      reason: `the previous compile of this same annotated TeX (${prior.at}) failed on the paper's own TeX (${prior.reason}); not re-run`,
      ...(prior.source_failure ? { source_failure: prior.source_failure } : {}),
    };
  }
  let result = await a.compile({ dir: a.dir, mainFile: a.mainFile, timeoutMs: 120_000 });
  let paperSide = false;
  if (result.status === "failed" && !/timed out/.test(result.reason)) {
    const logFile = path.join(a.dir, a.mainFile.replace(/\.tex$/i, ".log"));
    const logText = existsSync(logFile) ? await readFile(logFile, "latin1") : result.log_tail;
    const files: Record<string, string> = {};
    for (const m of logText.matchAll(/^(?:\.\/)?([^\s:][^:\n]*\.tex):\d+: /gm)) {
      const f = m[1]!.replace(/^\.\//, "");
      if (files[f] === undefined && existsSync(path.join(a.dir, f))) files[f] = await readFile(path.join(a.dir, f), "latin1");
    }
    paperSide = paperSideFailure(logText, files);
    if (a.sourceDir && existsSync(a.sourceDir)) {
      // a baseline that cannot be had (the copy, the compiler) leaves the failure as it stands
      const base = await sourceBaseline({ sourceDir: a.sourceDir, cacheFile: path.join(path.dirname(recFile), SOURCE_COMPILE_RECORD), mainFile: a.mainFile, compile: a.compile }).catch(() => null);
      const split = attributeErrors(latexLogErrors(logText), base?.errors ?? []);
      if (base && split.source.length > 0) {
        paperSide = split.own.length === 0;
        result = { ...result, source_failure: { error: base.errors[0]!.replace(/^\.\//u, ""), lines: split.source, only: paperSide } };
        a.log(`annotated paper: the paper's own source does not compile here (${base.tool}: ${result.source_failure!.error}): ${split.source.length} error(s) of this compile are the source's${paperSide ? ", and there is no other" : `; ${split.own.length} are not`}`);
      }
    }
  }
  if (result.status !== "skipped") {
    const rec: CompileRecord = { tree_sha256: sha, status: result.status, tool: result.tool, reason: result.reason, paper_side: paperSide, ...(result.source_failure ? { source_failure: result.source_failure } : {}), log_tail: result.log_tail, at: new Date().toISOString() };
    await mkdir(path.dirname(recFile), { recursive: true });
    await writeFile(recFile, `${JSON.stringify(rec, null, 2)}\n`, "utf8");
  }
  return result;
}
