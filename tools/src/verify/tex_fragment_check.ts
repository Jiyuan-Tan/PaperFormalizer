/**
 * Compile-at-source (design 2026-09-25, "verify at the source, never repair downstream"): every TeX
 * fragment a model writes for the annotated paper — an explanation field, a reading, a condition, a
 * corrected statement, a proof step — is checked by COMPILING it, alone, against the paper's own
 * preamble. A fragment that does not compile is the model's to fix: the producer sends the compiler's
 * first error back through its existing feedback loop (`texFieldViolations`), and the renderer, which
 * never repairs, prints a fragment that still fails verbatim and reports it at the render checkpoint
 * (`render_check.ts`).
 *
 * `checkTexFragment` builds a scratch document from the paper's main file up to `\begin{document}`,
 * the annotation macros (`VS_PREAMBLE_BLOCK`, via `injectPreamble` — exactly as the annotated paper
 * gets them), and the fragment as the annotated paper prints it (`printedFragment`: laid out, its displays fitted,
 * in check mode — a display of the model's that would print below 5/6 of its size is an error) set as it is set in the paper: a statement or hypothesis inside the
 * paper's `theorem` environment (a plain paragraph when the paper defines none) in its blue block, a
 * proof step inside `proof` in its block, a note in `\vsNote{…}`. It runs `pdflatex -halt-on-error`
 * in a scratch directory under the run's `logs/`, the paper's `source/` on `TEXINPUTS`. A character
 * outside printable ASCII fails before any compile (`nonAsciiProblem`: the reply is plain ASCII, every
 * symbol a TeX command), and so do unbalanced braces (`braceProblem`: a stray `}` a later `{` rebalances
 * compiles and prints the wrong text). Verdicts are cached by sha256(preamble + macros + kind + printed fragment) in
 * `discovery/tex_check_cache.json`; calls run at most `MAX_PARALLEL` compiles at once, so a caller may
 * fan out freely. Skipped (ok, logged once) when pdflatex is not on PATH, when the paper's main file
 * is not on file, or when the paper's preamble does not compile on its own — the render checkpoint
 * (the whole annotated paper's compile) still guards then.
 */
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { mkdir, readFile, rm, writeFile } from "node:fs/promises";
import path from "node:path";
import { execFileTracked } from "../shared/child_registry.js";
import { findExecutable } from "../shared/program.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import { VS_PREAMBLE_BLOCK, braceProblem, documentClassOf, injectPreamble, loadsXcolor, nonAsciiProblem, preambleOf, printedFragment } from "./annotate_tex.js";
import { isProofOp, opTex, type PatchOp } from "./ops.js";
import { envImbalance, envTags } from "./tex_balance.js";
import { isControlLine } from "./units.js";
import { isStructuredExplanation, noteFields, type OwnerExplanationField } from "./owner_text.js";
import type { PatchFile } from "./patches.js";
import { readGroup } from "./tex_envs.js";
import { VERIFY_FILES } from "./types.js";

/** Where a fragment is set in the paper (what it is wrapped in for the check). */
export type TexFragmentKind = "statement" | "hypothesis" | "step" | "note";

export interface TexCheckContext {
  runDir: string;
  /** The paper's main file under `source/` (default: `discovery/envs.json`'s `main_file`). */
  mainFile?: string | null;
  log?: (m: string) => void;
}

export type TexCheckResult = { ok: true; skipped?: string } | { ok: false; error: string; rule?: number };

/** What every violation says after the compiler's line. */
export const TEX_FRAGMENT_RULE = "the fragment must compile as LaTeX against the paper's preamble";
/** The rule a cached FAILURE was judged by: a failure recorded under an earlier rule is judged again
 * (2: a clean pdflatex exit passes whatever its log shows; 3: an error line the log wrapped is read
 * whole). Passes stand across rules. */
const FAILURE_RULE = 3;
/** `runs/<slug>/<this>`: the verdict cache. */
export const TEX_CHECK_CACHE = "discovery/tex_check_cache.json";
/** Compiles at once, over every caller of this process. */
const MAX_PARALLEL = 6;
const TIMEOUT_MS = 30_000;
/** pdflatex's log line width: a longer line continues on the next. */
const MAX_PRINT_LINE = 79;

/** Paper text read as UTF-8 when it is valid UTF-8, else as Latin-1 (with the encoding to write it back). */
export async function readPaperText(file: string): Promise<{ text: string; enc: BufferEncoding }> {
  const buf = await readFile(file);
  const utf = buf.toString("utf8");
  return Buffer.from(utf, "utf8").equals(buf) ? { text: utf, enc: "utf8" } : { text: buf.toString("latin1"), enc: "latin1" };
}

const onPath = (name: string): string | null => findExecutable(name, { nativeOnly: true });

/** The fragment as the annotated paper prints it (`printedFragment`) and sets it, in the scratch
 * document's body. */
function wrapped(raw: string, kind: TexFragmentKind | "baseline"): string {
  const fragment = kind === "baseline" ? raw : printedFragment(raw, kind);
  switch (kind) {
    case "statement":
      return `\\begin{vsCheckStatement}\\vsCorrected{${fragment}}\n\\end{vsCheckStatement}`;
    case "hypothesis":
      return `\\begin{vsCheckStatement}\\vsCorrected{${fragment}}\n\\end{vsCheckStatement}`;
    case "step":
      return `\\begin{vsCheckProof}\\vsCorrectedStep{${fragment}}\n\\end{vsCheckProof}`;
    case "note":
      return `\\vsNote{${fragment}}`;
    case "baseline":
      return "\\vsNote{x}";
  }
}

/** The paper's `theorem` / `proof` environments when it defines them, else a plain paragraph; the
 * annotation macros in check mode. */
const ENV_SHIMS = [
  "\\vsChecktrue",
  "\\makeatletter",
  "\\@ifundefined{theorem}{\\newenvironment{vsCheckStatement}{\\par}{\\par}}{\\newenvironment{vsCheckStatement}{\\begin{theorem}}{\\end{theorem}}}",
  "\\@ifundefined{proof}{\\newenvironment{vsCheckProof}{\\par}{\\par}}{\\newenvironment{vsCheckProof}{\\begin{proof}}{\\end{proof}}}",
  "\\makeatother",
].join("\n");

/** The scratch document for one fragment. Pure. */
export function scratchDocument(preamble: string, xcolorLoaded: boolean, fragment: string, kind: TexFragmentKind | "baseline"): string {
  const doc = `${preamble.trimEnd()}\n\\begin{document}\n${ENV_SHIMS}\n${wrapped(fragment, kind)}\n\\vsCheckEnd\n\\end{document}\n`;
  return injectPreamble(doc, xcolorLoaded).tex;
}

/** A compile's verdict from its exit and log: an error only when pdflatex failed (-halt-on-error
 * exits non-zero on the first one). A clean exit is a pass whatever the log shows — an overfull box's
 * dump can wrap onto a line starting with "! " (live CNS 2026-09-28). Pure. */
export function compileOutcome(failed: boolean, log: string): { ok: true } | { ok: false; error: string; cacheable: boolean } {
  if (!failed) return { ok: true };
  const error = firstLatexError(log);
  return error ? { ok: false, error, cacheable: true } : { ok: false, error: "pdflatex failed without an error line in its log", cacheable: false };
}

/** The first error of a pdflatex log (`-file-line-error` or `! ` line, rejoined where the log wrapped
 * it at `max_print_line`) with the source text it stopped at, or null. Pure. */
export function firstLatexError(log: string): string | null {
  const lines = log.split("\n");
  const at = lines.findIndex((l) => /^(?:\.\/)?[^\s:][^:\n]*\.tex:\d+: /u.test(l) || /^! /u.test(l));
  if (at < 0) return null;
  let line = lines[at]!;
  for (let k = at + 1; lines[k - 1]!.length === MAX_PRINT_LINE && k < lines.length; k++) line += lines[k]!;
  const err = line.replace(/^(?:\.\/)?[^\s:][^:\n]*\.tex:\d+: /u, "").replace(/^! /u, "").trim();
  const ctx = lines.slice(at + 1, at + 15).find((l) => /^l\.\d+ /u.test(l));
  const where = ctx ? ctx.replace(/^l\.\d+\s?/u, "").trim() : "";
  return where ? `${err} (at: ${where.length > 80 ? `…${where.slice(-79)}` : where})` : err;
}

interface Paper {
  preamble: string;
  /** The preamble without the paper's body definitions (`bodyDefinitions`), when it has any. */
  plain?: string;
  xcolor: boolean;
  enc: BufferEncoding;
  src: string;
}

async function mainFileOf(ctx: TexCheckContext): Promise<string | null> {
  if (ctx.mainFile) return ctx.mainFile;
  const envs = path.join(ctx.runDir, VERIFY_FILES.envsJson);
  if (!existsSync(envs)) return null;
  try {
    return (JSON.parse(await readFile(envs, "utf8")) as { main_file?: string }).main_file ?? null;
  } catch {
    return null;
  }
}

/** The preamble without an `\input` / `\include` of a file the bundle does not ship (a converter's
 * macro file such as `tcilatex`): the flattener skips it too, and left in, the preamble cannot compile
 * and no fragment is checked. Pure but for the existence checks. */
export function withoutMissingInputs(preamble: string, dir: string): string {
  return preamble.replace(/\\(?:input|include)\s*\{([^{}]+)\}/gu, (all, name: string) =>
    [name, `${name}.tex`].some((f) => existsSync(path.join(dir, f.trim()))) ? all : "",
  );
}

/** The macros the paper defines in its BODY rather than its preamble (`\\newcommand`, `\\renewcommand`,
 * `\\providecommand`, `\\DeclareMathOperator`, `\\def` and its `\\gdef`/`\\edef`/`\\xdef` forms), each with
 * its arguments, in the order of the text and each name once (the first: a name a paper defines again in
 * another group would clash at the top level), inside `\\makeatletter … \\makeatother` (an `@` name).
 * A definition inside one already taken is part of it, and a `\\def\\csname …` (built by `\\expandafter`) is
 * not read. `flat` is the flattened paper (comments and literal blocks blanked). Pure. */
export function bodyDefinitions(flat: string): string {
  const out = bodyDefinitionList(flat).map((d) => d.text);
  return out.length ? ["\\makeatletter", ...out, "\\makeatother"].join("\n") : "";
}

/** `bodyDefinitions`, one entry per name: the name (`\\name`) and its definition as written. Pure. */
export function bodyDefinitionList(flat: string): Array<{ name: string; text: string }> {
  const at = flat.indexOf("\\begin{document}");
  const body = at < 0 ? "" : flat.slice(at);
  const out: Array<{ name: string; text: string }> = [];
  const names = new Set<string>();
  const re = /\\(?:(?:new|renew|provide)command\*?|DeclareMathOperator\*?|[gex]?def)(?![A-Za-z@])/gu;
  for (let m = re.exec(body); m; m = re.exec(body)) {
    let i = m.index + m[0].length;
    let name: string | null = null;
    if (/def$/u.test(m[0])) {
      // \def\name<parameter text>{body}
      const r = /^\s*(\\[A-Za-z@]+)[^{]*/u.exec(body.slice(i));
      if (!r || r[1] === "\\csname") continue;
      name = r[1]!;
      i += r[0].length;
    } else {
      // the name, braced or bare
      const g = readGroup(body, i, "{");
      if (g) { name = g.value.trim(); i = g.end; }
      else {
        const r = /^\s*(\\[A-Za-z@]+)/u.exec(body.slice(i));
        if (!r) continue;
        name = r[1]!;
        i += r[0].length;
      }
      for (let k = 0; k < 2; k += 1) { const o = readGroup(body, i, "["); if (!o) break; i = o.end; }
    }
    const b = readGroup(body, i, "{");
    if (!b) continue;
    // the scan resumes after this definition: one inside its body belongs to it
    re.lastIndex = b.end;
    if (names.has(name)) continue;
    names.add(name);
    out.push({ name, text: body.slice(m.index, b.end) });
  }
  return out;
}

/** A note set where the paper has not yet defined a body macro it uses (a reading placed at a symbol's
 * first use, the macro defined sections later) does not compile. Prefix the note with the definitions
 * of the body macros it uses (and those they use), as `\\providecommand` inside a brace group: local to
 * the note, a no-op where the macro already exists, and the paper's own definition later is untouched.
 * Only the `\\newcommand` family is carried: a `\\def` cannot be made conditional the same way (and a `\\gdef`
 * would leave the group), `\\DeclareMathOperator` is preamble-only, and `@` names have catcodes fixed in an
 * argument — those are left out. Pure. */
export function withLocalBodyDefinitions(text: string, defs: ReadonlyArray<{ name: string; text: string }>): string {
  const byName = new Map(defs.filter((d) => !d.name.includes("@") && /^\\(?:new|renew|provide)command/u.test(d.text)).map((d) => [d.name, d.text] as const));
  const uses = (s: string): string[] => [...s.matchAll(/\\[A-Za-z]+(?![A-Za-z])/gu)].map((m) => m[0]).filter((n) => byName.has(n));
  const need = new Set<string>();
  const queue = uses(text);
  while (queue.length) { const n = queue.shift()!; if (need.has(n)) continue; need.add(n); queue.push(...uses(byName.get(n)!)); }
  if (!need.size) return text;
  const local = [...byName.entries()].filter(([n]) => need.has(n)).map(([, t]) => t.replace(/^\\(?:new|renew)command/u, "\\providecommand"));
  return `{${local.join("")}${text}}`;
}

async function paperOf(ctx: TexCheckContext): Promise<Paper | null> {
  const main = await mainFileOf(ctx);
  const src = path.join(ctx.runDir, VERIFY_FILES.sourceDir);
  const file = main ? path.join(src, main) : null;
  if (!file || !existsSync(file)) return null;
  const { text, enc } = await readPaperText(file);
  // the paper's own macros defined in its body follow the preamble: a fragment may use them
  const flatFile = path.join(ctx.runDir, VERIFY_FILES.flatTex);
  const defs = existsSync(flatFile) ? bodyDefinitions(await readFile(flatFile, "utf8")) : "";
  const plain = withoutMissingInputs(preambleOf(text.replace(/\r\n?/gu, "\n")), path.dirname(file));
  const preamble = defs ? `${plain}\n${defs}\n` : plain;
  const cls = documentClassOf(preamble);
  const clsFile = cls ? path.join(src, `${cls}.cls`) : null;
  const clsText = clsFile && existsSync(clsFile) ? await readFile(clsFile, "latin1") : null;
  return { preamble, ...(defs ? { plain } : {}), xcolor: loadsXcolor(preamble, clsText, cls), enc, src: path.dirname(file) };
}

// --- the cache, one per run, shared by every caller of this process --------------------------

interface Cache {
  file: string;
  map: Map<string, TexCheckResult>;
  /** Compiles running, by key: a second caller of the same fragment waits for the first. */
  inflight: Map<string, Promise<TexCheckResult>>;
  writing: Promise<void> | null;
  dirty: boolean;
}
const caches = new Map<string, Promise<Cache>>();

function cacheOf(runDir: string): Promise<Cache> {
  const file = path.join(runDir, TEX_CHECK_CACHE);
  let c = caches.get(file);
  if (!c) {
    c = (async () => {
      const map = new Map<string, TexCheckResult>();
      if (existsSync(file)) {
        try {
          for (const [k, v] of Object.entries(JSON.parse(await readFile(file, "utf8")) as Record<string, TexCheckResult>)) {
            if (v.ok || v.rule === FAILURE_RULE) map.set(k, v);
          }
        } catch {
          // an unreadable cache is rebuilt
        }
      }
      return { file, map, inflight: new Map(), writing: null, dirty: false };
    })();
    caches.set(file, c);
  }
  return c;
}

/** Write the cache (writes coalesce; resolves when what was set before the call is on disk). */
function persist(c: Cache): Promise<void> {
  c.dirty = true;
  if (!c.writing) {
    c.writing = (async () => {
      try {
        while (c.dirty) {
          c.dirty = false;
          await writeJsonAtomic(c.file, Object.fromEntries(c.map));
        }
      } finally {
        c.writing = null;
      }
    })();
  }
  return c.writing;
}

// --- the compile ---------------------------------------------------------------------------

let running = 0;
const queue: Array<() => void> = [];
async function slot<T>(f: () => Promise<T>): Promise<T> {
  if (running >= MAX_PARALLEL) await new Promise<void>((r) => queue.push(r));
  running += 1;
  try {
    return await f();
  } finally {
    running -= 1;
    queue.shift()?.();
  }
}

const said = new Set<string>();
function logOnce(ctx: TexCheckContext, msg: string): void {
  const k = `${ctx.runDir}\u0000${msg}`;
  if (said.has(k)) return;
  said.add(k);
  ctx.log?.(`tex check: ${msg}`);
}

async function compile(ctx: TexCheckContext, paper: Paper, pdflatex: string, key: string, doc: string): Promise<{ ok: true } | { ok: false; error: string; cacheable: boolean }> {
  const dir = path.join(ctx.runDir, "logs", "tex_check", `${key.slice(0, 16)}-${process.pid}`);
  await mkdir(dir, { recursive: true });
  try {
    await writeFile(path.join(dir, "frag.tex"), doc, paper.enc);
    let failed: { killed?: boolean } | null = null;
    try {
      await execFileTracked("latex", pdflatex, ["-interaction=nonstopmode", "-halt-on-error", "-file-line-error", "-no-shell-escape", "frag.tex"], {
        cwd: dir,
        timeout: TIMEOUT_MS,
        maxBuffer: 16 * 1024 * 1024,
        env: { ...process.env, TEXINPUTS: `${paper.src}${path.delimiter}` },
      });
    } catch (err) {
      failed = err as { killed?: boolean };
    }
    const logFile = path.join(dir, "frag.log");
    const log = existsSync(logFile) ? await readFile(logFile, "latin1") : "";
    if (failed?.killed) return { ok: false, error: `the compile timed out after ${TIMEOUT_MS / 1000} s`, cacheable: false };
    return compileOutcome(!!failed, log);
  } finally {
    await rm(dir, { recursive: true, force: true });
  }
}

/** A verdict's key: the scratch document's inputs, the fragment in its printed form. */
const keyOf = (paper: Paper, kind: TexFragmentKind | "baseline", fragment: string): string =>
  createHash("sha256").update(`${paper.preamble}\u0000${VS_PREAMBLE_BLOCK}\u0000${ENV_SHIMS}\u0000${kind}\u0000${kind === "baseline" ? fragment : printedFragment(fragment, kind)}`).digest("hex");

/** Compile `kind` of `fragment` (cached; see the module doc). */
async function verdict(ctx: TexCheckContext, paper: Paper, fragment: string, kind: TexFragmentKind | "baseline"): Promise<TexCheckResult> {
  const c = await cacheOf(ctx.runDir);
  const key = keyOf(paper, kind, fragment);
  const hit = c.map.get(key) ?? c.inflight.get(key);
  if (hit) return hit instanceof Promise ? hit : hit.ok ? hit : { ok: false, error: hit.error };
  const pdflatex = onPath("pdflatex");
  if (!pdflatex) {
    logOnce(ctx, "skipped — pdflatex is not on PATH (the annotated paper's compile still guards)");
    return { ok: true, skipped: "pdflatex is not on PATH" };
  }
  const run = (async (): Promise<TexCheckResult> => {
    const r = await slot(() => compile(ctx, paper, pdflatex, key, scratchDocument(paper.preamble, paper.xcolor, fragment, kind)));
    if (!r.ok && !r.cacheable) return { ok: false, error: r.error };
    const out: TexCheckResult = r.ok ? { ok: true } : { ok: false, error: r.error };
    c.map.set(key, r.ok ? out : { ok: false, error: r.error, rule: FAILURE_RULE });
    await persist(c);
    return out;
  })();
  c.inflight.set(key, run);
  try {
    return await run;
  } finally {
    c.inflight.delete(key);
  }
}

/**
 * Does `fragment` compile, set as `kind`, against the paper's preamble? `{ ok: false, error }` names
 * its non-ASCII characters, its unbalanced braces, or the compiler's first error line with the text
 * it stopped at.
 */
export async function checkTexFragment(fragment: string, kind: TexFragmentKind, ctx: TexCheckContext): Promise<TexCheckResult> {
  const pre = nonAsciiProblem(fragment) ?? braceProblem(fragment);
  if (pre) return { ok: false, error: pre };
  const paper = await paperOf(ctx);
  if (!paper) {
    logOnce(ctx, "skipped — the paper's main file is not on file under source/");
    return { ok: true, skipped: "the paper's main file is not on file" };
  }
  let base = await verdict(ctx, paper, "", "baseline");
  // the paper's body definitions are a help, never a reason to check nothing: without them when they break it
  if (!base.ok && paper.plain !== undefined) {
    const plain = { ...paper, preamble: paper.plain, plain: undefined };
    const again = await verdict(ctx, plain, "", "baseline");
    if (again.ok) {
      logOnce(ctx, `the paper's body definitions do not compile in its preamble (${base.error}); checked without them`);
      return verdict(ctx, plain, fragment, kind);
    }
    base = again;
  }
  if (!base.ok) {
    logOnce(ctx, `skipped — the paper's preamble does not compile on its own (${base.error})`);
    return { ok: true, skipped: "the paper's preamble does not compile on its own" };
  }
  return verdict(ctx, paper, fragment, kind);
}

/** One text a producer wrote: where it sits (for the message), its text, how it is set; `problem`: a
 * violation found without compiling (the field is then not compiled). */
export interface TexField {
  where: string;
  text: string | null | undefined;
  kind: TexFragmentKind;
  problem?: string;
}

/**
 * The violations of the fields that do not compile, checked in parallel: `<where> does not compile:
 * <compiler line> — the fragment must compile as LaTeX against the paper's preamble.` No context →
 * nothing is checked (a caller without a run).
 */
export async function texFieldViolations(fields: readonly TexField[], ctx: TexCheckContext | null | undefined): Promise<string[]> {
  if (!ctx) return [];
  const todo = fields.filter((f): f is TexField & { text: string } => !f.problem && typeof f.text === "string" && f.text.trim() !== "");
  const res = await Promise.all(todo.map((f) => checkTexFragment(f.text, f.kind, ctx)));
  const flatFile = path.join(ctx.runDir, VERIFY_FILES.flatTex);
  const unknown = existsSync(flatFile) ? unknownRefs(await readFile(flatFile, "utf8"), todo.map((f) => f.text)) : () => [];
  return [
    ...fields.flatMap((f) => (f.problem ? [`${f.where} ${f.problem}`] : [])),
    ...todo.flatMap((f) => unknown(f.text).map((l) => `${f.where} references \\ref{${l}}, a label the paper does not define (the page and the annotated paper print ??) — name the result by its printed number ("Lemma 4.2") or use the label the paper's own \\label gives it.`)),
    ...todo.flatMap((f, i) => {
      const r = res[i]!;
      return r.ok ? [] : [`${f.where} does not compile: ${r.error}${mathModeHint(r.error, f.text)} — ${TEX_FRAGMENT_RULE}.`];
    }),
  ];
}

/** The labels a text's `\\ref`-like commands name that neither the paper (`flat`: its `\\label`s, also through a
 * macro wrapping `\\label{#1}`, and any label it refers to itself) nor any of `texts` (a label a repair adds) defines. Returns a lookup per text. Pure. */
export function unknownRefs(flat: string, texts: readonly string[]): (text: string) => string[] {
  const key = (l: string): string => l.trim().replace(/\s+/gu, " ");
  const wrappers = [...flat.matchAll(/\\(?:re)?newcommand\*?\s*\{?\s*\\([A-Za-z]+)\s*\}?\s*\[1\]\s*\{[^{}]*\\label\s*\{#1\}/gu)].map((m) => m[1]!);
  const labelRe = new RegExp(String.raw`\\(?:label${wrappers.map((w) => `|${w}`).join("")})\s*(?:\[[^\]]*\])?\s*\{([^}]*)\}`, "gu");
  const refsOf = (t: string): string[] => [...t.matchAll(/\\(?:eq|c|C|auto)?ref\*?\{([^}]*)\}/gu)].flatMap((m) => m[1]!.split(",").map(key));
  // a label the paper itself refers to counts as defined (one set by a private package's macro, `\\numb{…}`)
  const labels = new Set([...[flat, ...texts].flatMap((t) => [...t.matchAll(labelRe)].map((m) => key(m[1]!))), ...refsOf(flat)]);
  return (text) => refsOf(text).filter((l) => l !== "" && !labels.has(l));
}

/** For "Missing $ inserted": the `_` / `^` the text has outside math, which is what pdflatex reports that
 * way. Math (`$…$`, `$$…$$`, `\[…\]`, `\(…\)`, math environments, `\ensuremath`), `\verb`, comments and
 * the arguments of `\ref`-like, `\label`, `\cite`, `\url`, `\input` commands are skipped: `_` is legal
 * there. The snippet quotes the text itself. Empty when there is none. Pure. */
export function mathModeHint(error: string, text: string): string {
  if (!/Missing \$ inserted/u.test(error)) return "";
  const blank = (m: string): string => m.replace(/[^\n]/gu, " ");
  const skipped = [
    /(?<!\\)%.*$/gmu,
    /\\verb\*?(.)[\s\S]*?\1/gu,
    /\\begin\{(equation|align|gather|multline|eqnarray|math|displaymath|flalign|alignat)(\*?)\}[\s\S]*?\\end\{\1\2\}/gu,
    /\\(?:[a-zA-Z]*ref|label|cite[a-z]*|url|input|include|ensuremath)\*?(?:\[[^\]]*\])*\{[^}]*\}/gu,
    /(?<!\\)\$\$[\s\S]*?(?<!\\)\$\$|(?<!\\)\$(?:\\.|[^$\\])*\$|\\\[[\s\S]*?\\\]|\\\([\s\S]*?\\\)/gu,
  ].reduce((t, re) => t.replace(re, blank), text);
  const hit = /(?:^|[^\\])([_^])/u.exec(skipped);
  if (!hit) return "";
  const at = hit.index + hit[0].length - 1;
  return ` (a \`${hit[1]}\` outside math, at …${text.slice(Math.max(0, at - 20), at + 10)}…: put it inside $…$, or write the name in words)`;
}

/** The TeX fields of a note for the author (`noteFields`, or legacy prose), each a note; `where`
 * prefixes the field's path in the message. */
export function explanationTexFields(oe: OwnerExplanationField | null | undefined, where: string): TexField[] {
  if (!oe) return [];
  if (typeof oe === "string") return [{ where, text: oe, kind: "note" }];
  return isStructuredExplanation(oe) ? noteFields(oe).map(([k, text]) => ({ where: `${where} \`${k}\``, text, kind: "note" as const })) : [];
}

/** A unit-sized replacement compiled as it sits in the paper: a unit (or a run of units) the paper
 * itself cuts across an environment (a nested lemma inside a proof opens in one unit and closes in a
 * later one) leaves the same environments open in its replacement, and those are closed (or opened)
 * around it for the check (`envImbalance`) — never in the printed text. `printed`: the text the
 * replacement takes the place of. Only an imbalance equal to the printed text's (its unmatched tags, in
 * order) is balanced; any other stays for the compiler to report. Pure. */
export function balancedLikeUnit(tex: string, printed: string | null | undefined): string {
  if (!printed) return tex;
  const a = envImbalance(tex);
  if ((a.close.length === 0 && a.open.length === 0) || !sameList(unmatched(tex), unmatched(printed))) return tex;
  return `${[...a.close].reverse().map((e) => `\\begin{${e}}`).join("")}${tex}${[...a.open].reverse().map((e) => `\\end{${e}}`).join("")}`;
}

const sameList = (x: readonly string[], y: readonly string[]): boolean => x.length === y.length && x.every((e, i) => e === y[i]);
/** A text's unmatched environment tags, in order (`\\end{X}`, `\\begin{Y}`). */
const unmatched = (tex: string): string[] => envTags(tex).filter((t) => !t.matched).map((t) => `\\${t.begin ? "begin" : "end"}{${t.env}}`);

/** Why a replacement of a text the paper cuts across environments does not take its place (`printed`
 * leaves environments open or closes some it does not open, and `tex` does not do the same, in the same
 * order: the paper's text around it holds their other ends); null when it does, or `printed` crosses
 * none. Pure. */
export function envKeepProblem(tex: string, printed: string | null | undefined): string | null {
  if (!printed) return null;
  const a = unmatched(tex);
  const b = unmatched(printed);
  if (b.length === 0 || sameList(a, b)) return null;
  return `does not keep the environments of the printed text it replaces: that text closes or opens without its other end ${b.join(" ")}, the replacement ${a.join(" ") || "none"} — a replacement keeps those unmatched \\begin / \\end markers, in the same order (the paper's text around it holds their other ends), and changes the text between them.`;
}

/**
 * The TeX the V1 fixer writes in a patch file, each set as the paper sets it: each op's TeX in its unit's
 * context (a statement op `statement`, a proof op `step`; balanced like the text it replaces, `printed`
 * of the op: `balancedLikeUnit`, a violation when it does not keep that text's crossing environments:
 * `envKeepProblem`) and the corrected statement it derives
 * (`statement`), a proof note the fixer wrote whole (not an amended printed proof: the paper's own
 * text), a consequential `reason` and an unfixable `reason` (`note`), and the
 * explanation's fields — for patches and suggested repairs alike. The fixer's wiring passes them to
 * `texFieldViolations`. Pure.
 */
export function patchFileTexFields(file: Pick<PatchFile, "patches" | "unfixable">, printed: (op: PatchOp) => string | null = () => null): TexField[] {
  type Body = { corrected_statement?: string | null; ops?: PatchOp[]; proof_note?: string | null; corollaries?: ReadonlyArray<{ statement: string; follows: string }> | null };
  // Each op's TeX in its unit's context: a proof step, or a statement's text.
  const kindOf = (op: PatchOp): TexFragmentKind => (isProofOp(op) ? "step" : "statement");
  // A corrected algorithm is the paper's own float around its ops, each compiled on its own (a control
  // line: its condition).
  const algorithm = (t: string | null | undefined): boolean => /\\begin\s*\{algorithmic\}/u.test(t ?? "");
  const stepTex = (tex: string): string => (isControlLine(tex) ? (/^\s*\\[A-Za-z]+\s*\{([\s\S]*)\}\s*$/u.exec(tex)?.[1] ?? "") : tex);
  const body = (b: Body, where: string): TexField[] => [
    ...(algorithm(b.corrected_statement) ? [] : [{ where: `${where}: its corrected statement (derived from its ops)`, text: b.corrected_statement, kind: "statement" as const }]),
    ...(b.ops ?? []).map((op, k): TexField => {
      const field = { where: `${where}: ops[${k}] (${op.op})`, kind: kindOf(op) };
      if (algorithm(b.corrected_statement)) return { ...field, text: stepTex(opTex(op)) };
      const problem = envKeepProblem(opTex(op), printed(op));
      return { ...field, text: balancedLikeUnit(opTex(op), printed(op)), ...(problem ? { problem } : {}) };
    }),
    // A proof note the fixer wrote whole (the paper prints no proof); an amended printed proof is the
    // paper's own text around the proof ops, each already compiled as a step.
    ...((b.ops ?? []).some(isProofOp) ? [] : [{ where: `${where}: its proof_note`, text: b.proof_note, kind: "note" as const }]),
    // Each corollary it splits off: a statement of its own, and its proof.
    ...(b.corollaries ?? []).flatMap((c, k) => [
      { where: `${where}: corollaries[${k}].statement`, text: c.statement, kind: "statement" as const },
      { where: `${where}: corollaries[${k}].follows`, text: c.follows, kind: "note" as const },
    ]),
  ];
  return [
    ...file.patches.flatMap((p) => [
      ...body(p, `the patch for "${p.node}"`),
      { where: `the patch for "${p.node}": its reason`, text: (p as { reason?: string | null }).reason, kind: "note" as const },
      ...explanationTexFields(p.owner_explanation, `the owner_explanation for "${p.node}"`),
    ]),
    ...file.unfixable.flatMap((u) => [
      { where: `the unfixable entry for "${u.node}": its reason`, text: u.reason, kind: "note" as const },
      ...explanationTexFields(u.owner_explanation, `the owner_explanation for "${u.node}"`),
      ...(u.suggested_repair ? body(u.suggested_repair, `the suggested repair for "${u.node}"`) : []),
    ]),
  ];
}

/** Every fragment's verdict key (`texVerdicts`). */
export const texVerdictKey = (kind: TexFragmentKind, text: string): string => `${kind}\u0000${text}`;

/**
 * The failing fragments among `fragments`, by `texVerdictKey`: the compiler's line for each. The
 * annotated paper's render check (`annotated_paper.ts` `writeAnnotatedPaper`).
 */
export async function texVerdicts(fragments: ReadonlyArray<{ kind: TexFragmentKind; text: string }>, ctx: TexCheckContext): Promise<Map<string, string>> {
  const out = new Map<string, string>();
  const res = await Promise.all(fragments.map((f) => checkTexFragment(f.text, f.kind, ctx)));
  fragments.forEach((f, i) => {
    const r = res[i]!;
    if (!r.ok) out.set(texVerdictKey(f.kind, f.text), r.error);
  });
  return out;
}
