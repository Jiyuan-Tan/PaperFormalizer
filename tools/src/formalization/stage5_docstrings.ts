// F5 docstring-coverage step. Coverage is authored HERE — the guaranteed-final
// Lean-edit point of the run.

import { createHash } from "node:crypto";
import { mkdir, readdir, readFile, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import path from "node:path";
import { MODEL_PLAN } from "../constants.js";
import type { PipelineContext, StateJson } from "../types.js";
import { artifactPaths, readPrompt, type StageDeps } from "../pipeline_support.js";
import { isPaperTmpPath } from "../paths.js";
import { dispatchAgent } from "../framework/agent_dispatch.js";
import { CodexRunError } from "../shared/codex.js";
import { crosslinkNames, linksGoal, parseNlCrosslinks, sourceBinders } from "../shared/nl_crosslinks.js";
import { spawnWithInactivityTimeout } from "../workers/spawn.js";
import { withLakeBuildLock } from "../shared/build_mutex.js";
import { mapLimit } from "./reviewer_verdicts.js";
import { fillTemplate } from "../shared/template.js";

const LAKE_TIMEOUT_MS = 1800_000;
/** Docstring passes per F5 entry: the pass, then one retry on the declarations it left defective. */
const MAX_DOCSTRING_PASSES = 2;

/**
 * The checkpoint-sized summary of a failed lake invocation: its `error` lines (lake writes
 * Lean's per-file diagnostics to STDOUT and only `build failed` to stderr, so both streams
 * are scanned), never the command line — a `lake -d <root> build <4 module names>` prefix
 * alone exceeds any sane cap and hid every diagnostic behind it (2026-09-11).
 */
export function lakeFailureSummary(
  r: { stdout: string; stderr: string; exitCode: number | null; killedDueToInactivity?: boolean; killedDueToTotalTimeout?: boolean },
  logPath: string,
): string {
  const errs = `${r.stdout}\n${r.stderr}`
    .split("\n")
    .filter((l) => /error/i.test(l))
    .slice(0, 25)
    .join("\n")
    .trim();
  const killed = r.killedDueToInactivity ? " (killed: no output for 30 min)" : r.killedDueToTotalTimeout ? " (killed: 30 min wall-clock)" : "";
  return `${errs || `lake exited ${r.exitCode}`}${killed}\n(full lake output: ${logPath})`;
}

/**
 * A failed lake invocation. `leanError` tells a Lean diagnostic (an `error:` line: the sources
 * do not elaborate — after a docstring pass, the pass's defect) from a lake that did not finish
 * (stopped by its timeout) or failed without one (a toolchain or lake problem): the second never
 * condemns the docstrings it was validating.
 */
export class LakeFailure extends Error {
  constructor(message: string, readonly leanError: boolean) {
    super(message);
  }
}

/** Whether a failed lake run reports a Lean diagnostic rather than a stopped or broken lake. Pure. */
export function lakeReportsLeanError(r: { stdout: string; stderr: string; killedDueToInactivity?: boolean; killedDueToTotalTimeout?: boolean }): boolean {
  if (r.killedDueToInactivity || r.killedDueToTotalTimeout) return false;
  return /^[^\n]*:\d+:\d+: error/m.test(`${r.stdout}\n${r.stderr}`) || /\berror: /.test(r.stdout);
}

export interface UndocumentedDecl {
  name: string;
  file: string;
  line: number;
  kind: string;
  /** Set when the decl IS documented but its NL↔Lean crosslink annotations are
   * missing or defective (see crosslinkDefect) — the docstring pass must fix
   * the annotation, not write a docstring from scratch. */
  problem?: string;
}

/** A linked phrase that would fit any declaration: it covers a binder without translating it. */
const PLACEHOLDER_PHRASE = /^(?:the |an? )?(?:stated|supplied)\b|^the (?:first|second|third) condition$/i;

/** The placeholder phrases among `firstPara`'s crosslinks (lower-cased, deduplicated). */
export function placeholderPhrases(firstPara: string): string[] {
  const out = parseNlCrosslinks(firstPara)
    .filter((g) => g.links && PLACEHOLDER_PHRASE.test(g.text.trim()))
    .map((g) => g.text.trim().toLowerCase());
  return [...new Set(out)];
}

/**
 * NL↔Lean crosslink requirement (hard F5 gate, docstring contract). A theorem's first
 * paragraph links every hypothesis-classified binder via `[phrase](hyp:name)` and the
 * conclusion via `[phrase](goal)`, every referenced name existing in the signature
 * (hypothesis-free theorems still link the conclusion). A definition links every explicit
 * parameter and the object (`(goal)`); names are not checked against the signature there,
 * since a section `variable` it uses is linked by name too. For both, no linked phrase may be
 * a placeholder ("the stated condition", "the supplied x"): such a phrase covers a binder
 * without translating it. Returns a short problem description, or null.
 */
export function crosslinkDefect(e: { kind?: unknown; doc?: unknown; source?: unknown }): string | null {
  if ((e.kind !== "theorem" && e.kind !== "def") || typeof e.doc !== "string" || !e.doc.trim()) return null;
  // Whitespace-collapsed: a crosslink marker wrapped
  // across a source line must parse the same here as on the rendered page.
  const firstPara = e.doc.trim().split(/\n\s*\n/)[0].replace(/\s+/g, " ");
  const placeholders = placeholderPhrases(firstPara);
  if (placeholders.length > 0) {
    return `placeholder phrases that translate nothing: ${placeholders.map((p) => `"${p}"`).join(", ")} — say what each hypothesis or object is`;
  }
  const names = crosslinkNames(firstPara);
  const hasGoal = linksGoal(firstPara);
  const binders = typeof e.source === "string" ? sourceBinders(e.source) : null;
  if (!binders) return null; // unstructurable signature: the site renders flat, nothing to link
  const linked = new Set(names);
  if (e.kind === "def") {
    const params = binders.filter((b) => b.isExplicit && !b.names.some((n) => linked.has(n)));
    if (params.length > 0) return `parameters with no [phrase](hyp:…) crosslink: ${params.map((b) => b.names.join(" ")).join(", ")}`;
    if (!hasGoal) return "the object defined has no [phrase](goal) crosslink";
    return null;
  }
  const hyps = binders.filter((b) => b.isHyp);
  const declared = new Set(binders.flatMap((b) => b.names));
  const unknown = names.filter((n) => !declared.has(n));
  if (unknown.length > 0) return `crosslink names not in signature: ${unknown.join(", ")}`;
  const uncovered = hyps.filter((b) => !b.names.some((n) => linked.has(n)));
  if (uncovered.length > 0) {
    return `hypotheses with no [phrase](hyp:…) crosslink: ${uncovered.map((b) => b.names.join(" ")).join(", ")}`;
  }
  if (!hasGoal) return "conclusion has no [phrase](goal) crosslink";
  return null;
}

/** Dotted module names for every .lean source in the run dir (find-derived, sorted; the
 * disposable `tmp/` agent workspace is excluded — it is not part of the published run). */
/** Two docstrings in a row (only whitespace between) do not parse: the docstring pass wrote a new
 * one above a declaration's existing one instead of replacing it. Keep one — the one carrying the
 * NL↔Lean crosslinks (`](hyp:…)` / `](goal)`) the page needs, else the one nearest the declaration.
 * Pure. */
export function collapseAdjacentDocstrings(src: string): { text: string; collapsed: number } {
  // Two docstrings with only whitespace and line comments (`-- @node: …` tags) between them.
  const pair = /(\/--(?:(?!-\/)[\s\S])*?-\/)((?:\s*--[^\n]*)*\s*)(\/--(?:(?!-\/)[\s\S])*?-\/)/;
  const linked = (d: string): boolean => /\]\((?:hyp:[^)]*|goal|step:\d+)\)/.test(d);
  let text = src;
  let collapsed = 0;
  for (let m = pair.exec(text); m; m = pair.exec(text)) {
    // The comments between stay where they are; one docstring goes.
    const [first, between, second] = [m[1]!, m[2]!, m[3]!];
    const kept = linked(first) && !linked(second) ? `${first}${between.replace(/^\s*\n/, "\n")}` : `${between.replace(/^\s*\n/, "")}${second}`;
    text = text.slice(0, m.index) + kept + text.slice(m.index + m[0].length);
    collapsed += 1;
  }
  return { text, collapsed };
}

/** A docstring the model left open runs into the tag line or the declaration below it and comments
 * out the rest of the file. It is open exactly when Lean's nesting comment scanner (each `/-`
 * opens, each `-/` closes) never returns to depth 0 after it: a text line that merely starts with a
 * keyword ("class in every bin …") is prose, a nested `/- … -/` in the text is allowed. Close it at
 * the end of its last text line before the next command or comment. Pure. */
export function closeUnterminatedDocstrings(src: string): { text: string; closed: number } {
  const lines = src.split("\n");
  const head = /^[ \t]*(?:--[ \t]*@(?:node|env|realizes)\b|@\[|(?:(?:private|protected|noncomputable|public|unsafe|partial|nonrec|scoped|local)[ \t]+)*(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|example|axiom|opaque|variable|open|namespace|section|end|attribute|set_option|notation|infix[lr]?|macro|macro_rules|syntax|universe|omit|include|export|mutual)\b)/;
  const runsOn = (i: number, from: number): boolean => {
    let depth = 1;
    for (let j = i, k = from; j < lines.length; j++, k = 0) {
      const line = lines[j]!;
      while (k < line.length - 1) {
        const two = line.slice(k, k + 2);
        if (two === "/-") { depth += 1; k += 2; }
        else if (two === "-/") { depth -= 1; k += 2; if (depth === 0) return false; }
        else k += 1;
      }
    }
    return true;
  };
  let closed = 0;
  for (let i = 0; i < lines.length; i++) {
    const at = lines[i]!.indexOf("/--");
    if (at < 0 || !runsOn(i, at + 3)) continue;
    for (let j = i + 1; j < lines.length; j++) {
      if (!head.test(lines[j]!) && !lines[j]!.includes("/-")) continue;
      let last = j - 1;
      while (last > i && lines[last]!.trim() === "") last--;
      lines[last] = `${lines[last]!.replace(/[ \t]+$/, "")} -/`;
      closed += 1;
      break;
    }
  }
  return { text: lines.join("\n"), closed };
}

/** The docstring-style linter (an error in the toolkit's build) wants a docstring to end with one
 * space or one newline before `-/`: a model writes "text.-/", "text.  -/" or "text.\n -/". Rewrite
 * each ending to the single form it is nearest to. Pure. */
export function normalizeDocstringEndings(src: string): { text: string; fixed: number } {
  let fixed = 0;
  const text = src.replace(/\/--((?:(?!-\/)[\s\S])*?)-\//g, (whole, body: string) => {
    const trimmed = body.replace(/[ \t\n]+$/, "");
    const end = /\n[ \t]*$/.test(body) ? "\n" : " ";
    const out = `/--${trimmed}${end}-/`;
    if (out !== whole) fixed += 1;
    return out;
  });
  return { text, fixed };
}

/** A docstring written above a scoping prefix (`omit … in`, `open … in`, `set_option … in`,
 * `include … in`) does not parse: Lean wants it on the declaration, after the prefix. Move it there;
 * comments between stay above the prefix. Pure. */
export function docstringAfterScopePrefix(src: string): { text: string; moved: number } {
  const stranded = /(\/--(?:(?!-\/)[\s\S])*?-\/)((?:[ \t]*\n|[ \t]*--[^\n]*\n)*)((?:[ \t]*(?:omit|open|set_option|include)\b[^\n]*\bin[ \t]*\n(?:[ \t]*--[^\n]*\n)*)+)/g;
  let moved = 0;
  const text = src.replace(stranded, (_m, doc: string, between: string, prefix: string) => {
    moved += 1;
    return `${between.replace(/^[ \t]*\n/, "")}${prefix}${doc}\n`;
  });
  return { text, moved };
}

/** A docstring and the first line of what it documents (blank lines and `--` comments between are
 * skipped). */
const DOCSTRING_WITH_HEAD = /\/--((?:(?!-\/)[\s\S])*?)-\/((?:[ \t]*\n|[ \t]*--[^\n]*\n)*)([^\n]+)/g;
const TAG_LINE = /^[ \t]*@(?:realizes|node|env)\b.*$/gm;

/**
 * The docstring pass rewrites docstrings; the `@realizes` / `@node` / `@env` tag lines that live in
 * them are the run's bookkeeping, never the model's to retype. Put back, at the end of the docstring
 * above the same declaration line, every tag line `before` had there and `after` lost. Pure.
 */
export function restoreDocstringTags(before: string, after: string): { text: string; restored: number } {
  const tagsByHead = new Map<string, string[][]>();
  for (const m of before.matchAll(DOCSTRING_WITH_HEAD)) {
    const head = m[3]!.trim();
    const tags = (m[1]!.match(TAG_LINE) ?? []).map((t) => t.trim());
    tagsByHead.set(head, [...(tagsByHead.get(head) ?? []), tags]);
  }
  const seen = new Map<string, number>();
  let restored = 0;
  const text = after.replace(DOCSTRING_WITH_HEAD, (whole, body: string, between: string, headLine: string) => {
    const head = headLine.trim();
    const k = seen.get(head) ?? 0;
    seen.set(head, k + 1);
    const had = tagsByHead.get(head)?.[k] ?? [];
    const has = new Set((body.match(TAG_LINE) ?? []).map((t) => t.trim()));
    const lost = had.filter((t) => !has.has(t));
    if (lost.length === 0) return whole;
    restored += lost.length;
    return `/--${body.trimEnd()}\n${lost.join("\n")} -/${between}${headLine}`;
  });
  return { text, restored };
}

export function moduleNamesFor(leanSubdir: string, relFiles: string[]): string[] {
  const prefix = leanSubdir.replace(/\//g, ".");
  return relFiles
    .filter((f) => f.endsWith(".lean") && !isPaperTmpPath(f))
    .map((f) => `${prefix}.${f.replace(/\.lean$/, "").replace(/[\\/]+/g, ".")}`)
    .sort();
}

/** The prompt's per-file declaration list (file heading, then `  L<line> <kind> <name>` rows). */
export function declListFor(undoc: UndocumentedDecl[]): string {
  const byFile = new Map<string, UndocumentedDecl[]>();
  for (const e of undoc) byFile.set(e.file, [...(byFile.get(e.file) ?? []), e]);
  return [...byFile.entries()]
    .map(([f, es]) =>
      [f, ...es.slice().sort((a, b) => a.line - b.line).map((e) =>
        `  L${e.line} ${e.kind} ${e.name}${e.problem ? ` — FIX CROSSLINKS: ${e.problem}` : ""}`)].join("\n"),
    )
    .join("\n\n");
}

/** Declarations per docstring call: few enough that each one is read and translated, not scripted
 *  (one call over a whole paper's 288 declarations wrote them with a name→phrase table, 2026-10-02). */
const DOCSTRING_BATCH = 40;
/** Docstring calls running at once (each on its own files). */
const DOCSTRING_CONCURRENCY = 4;

/**
 * The docstring calls of one pass, as lanes: a lane's calls run in sequence, lanes run side by
 * side, and no two lanes touch the same file. Whole files are packed into calls of at most
 * `size` declarations; a file holding more is split across consecutive calls of its own lane.
 * Pure.
 */
export function docstringLanes(undoc: UndocumentedDecl[], size = DOCSTRING_BATCH): UndocumentedDecl[][][] {
  const byFile = new Map<string, UndocumentedDecl[]>();
  for (const e of undoc) byFile.set(e.file, [...(byFile.get(e.file) ?? []), e]);
  const lanes: UndocumentedDecl[][][] = [];
  let packed: UndocumentedDecl[] = [];
  for (const file of [...byFile.keys()].sort()) {
    const es = byFile.get(file)!.slice().sort((a, b) => a.line - b.line);
    if (es.length > size) {
      const calls: UndocumentedDecl[][] = [];
      for (let k = 0; k < es.length; k += size) calls.push(es.slice(k, k + size));
      lanes.push(calls);
      continue;
    }
    if (packed.length + es.length > size) {
      lanes.push([packed]);
      packed = [];
    }
    packed.push(...es);
  }
  if (packed.length) lanes.push([packed]);
  return lanes;
}

/** Bump when crosslinkDefect or the contract changes what passes: a fingerprint taken under an
 *  older gate must not let unchanged sources skip the new one. */
const DOCSTRING_GATE_VERSION = 2;

/**
 * Fingerprint of a docstring check: the gate version and every module's source text (module name
 * + file bytes; an absent file counts as empty). Docstrings and signatures live in the source, so
 * equal fingerprints mean the check would find what it found last time. Pure.
 */
export function docstringFingerprint(sources: ReadonlyArray<{ module: string; text: string }>): string {
  const h = createHash("sha256").update(`gate-${DOCSTRING_GATE_VERSION}\n`);
  for (const s of [...sources].sort((a, b) => a.module.localeCompare(b.module))) h.update(`${s.module}\n${s.text.length}\n${s.text}`);
  return h.digest("hex");
}

/** What `documentModules` documents, and where it keeps its records. */
export interface DocstringTarget {
  ctx: PipelineContext;
  deps: StageDeps;
  /** Dotted module names to cover (all under `prefix`). */
  modules: string[];
  /** Declaration-name prefix the index walks (`Papers.X` for a paper, the toolkit lib name). */
  prefix: string;
  /** Holds docstring_coverage.json, docstring_lake.log and docstring_rejected/. */
  outDir: string;
  /** Who runs the pass: the log tag and the block reason's opening ("F5", "toolkit"). */
  label: string;
  /** Modules the caller built green in this entry, with the tree unchanged since: the pre-pass
   *  build covers only the others (F5 builds them for the statement fingerprints just before). */
  builtModules?: readonly string[];
}

/** One docstring call. A call the worker watchdog killed (hung, no output) leaves its declarations
 * undocumented, and the coverage after the pass lists them for the next one: throwing would fail the
 * stage while the other lanes kept writing — a dead run that still looked busy. Any other failure
 * stops the pass. Returns whether the call ran to its end. */
export async function unlessKilled(label: string, call: () => Promise<unknown>): Promise<boolean> {
  try {
    await call();
    return true;
  } catch (err) {
    if (!(err instanceof CodexRunError && err.message.startsWith("codex killed:"))) throw err;
    console.warn(`[${label}] ${err.message.slice(0, 120)} — its declarations are left to the next pass`);
    return false;
  }
}

/**
 * Bring every declaration of `modules` to the docstring contract: documented, with NL↔Lean
 * crosslinks (see crosslinkDefect). Returns null when that holds; otherwise a block reason.
 * Codex documents the gaps in batched calls (docstring edits only); the rebuild validates the
 * edits (restored byte-for-byte on a build failure) and a re-extraction confirms coverage.
 */
export async function documentModules(t: DocstringTarget): Promise<string | null> {
  if (t.modules.length === 0) return null;
  await mkdir(t.outDir, { recursive: true });
  // Incremental: a check that came back clean records the sources' fingerprint; while no module
  // source changes (and the gate does not), the build + index are skipped.
  const cleanFile = path.join(t.outDir, "docstring_clean.json");
  const fingerprint = async () => docstringFingerprint(await Promise.all(t.modules.map(async (module) => {
    const f = path.join(t.ctx.repoRoot, `${module.split(".").join("/")}.lean`);
    return { module, text: existsSync(f) ? await readFile(f, "utf8") : "" };
  })));
  const recordClean = async () => writeFile(cleanFile, JSON.stringify({ fingerprint: await fingerprint(), modules: t.modules.length }) + "\n", "utf8");
  try {
    const last = JSON.parse(await readFile(cleanFile, "utf8")) as { fingerprint?: unknown };
    if (last.fingerprint === await fingerprint()) {
      console.log(`[${t.label}] docstring coverage: no module source changed since the last clean check — skipped`);
      return null;
    }
  } catch {
    // no record (or unreadable): check from scratch
  }
  const indexOut = path.join(t.outDir, "docstring_coverage.json");
  const lakeLog = path.join(t.outDir, "docstring_lake.log");
  const root = t.ctx.repoRoot;
  // Full stdout+stderr of every lake call lands in `lakeLog` (overwritten per call); a failure
  // throws only the diagnostic lines, so the checkpoint message carries the Lean error itself.
  const lake = (lakeArgs: string[]) =>
    withLakeBuildLock(root, async () => {
      const r = await spawnWithInactivityTimeout("lake", ["-d", root, ...lakeArgs], {
        cwd: root,
        env: process.env,
        inactivityTimeoutMs: LAKE_TIMEOUT_MS,
        maxTotalMs: LAKE_TIMEOUT_MS,
      });
      await writeFile(lakeLog, `$ lake ${lakeArgs.join(" ")}\n${r.stdout}\n${r.stderr}`, "utf8");
      if (r.exitCode !== 0) throw new LakeFailure(lakeFailureSummary(r, lakeLog), lakeReportsLeanError(r));
    });
  // Build first: paper_index reads OLEANS and silently emits an empty index over stale ones.
  const extractUndocumented = async (modulesToBuild: readonly string[]): Promise<UndocumentedDecl[]> => {
    if (modulesToBuild.length > 0) await lake(["build", ...modulesToBuild]);
    await lake(["exe", "paper_index", "--",
      "--prefix", t.prefix, "--src-root", root, "--modules", t.modules.join(","), "--out", indexOut]);
    const idx = JSON.parse(await readFile(indexOut, "utf8")) as {
      entries?: { name?: unknown; file?: unknown; line?: unknown; kind?: unknown; doc?: unknown; source?: unknown }[];
    };
    if (!Array.isArray(idx.entries)) throw new Error(`docstring extraction produced no entries array (${indexOut})`);
    return idx.entries.flatMap((e) => {
      if (typeof e.name !== "string" || typeof e.file !== "string") return [];
      const base = { name: e.name, file: e.file, line: typeof e.line === "number" ? e.line : 0,
        kind: typeof e.kind === "string" ? e.kind : "decl" };
      if (!e.doc) return [base];
      // Documented, but its NL↔Lean crosslink annotations are missing
      // or defective — same hard gate, fixed by the same docstring pass.
      const problem = crosslinkDefect(e);
      return problem ? [{ ...base, problem }] : [];
    });
  };

  let undoc: UndocumentedDecl[];
  try {
    const built = new Set(t.builtModules ?? []);
    undoc = await extractUndocumented(t.modules.filter((m) => !built.has(m)));
  } catch (err) {
    return (
      `${t.label} docstring coverage could not be computed:\n${err instanceof Error ? err.message : String(err)}\n` +
      `Resolve the build/extraction error then resume; the docstring gate cannot be skipped.`
    );
  }
  if (undoc.length === 0) {
    await recordClean();
    return null;
  }
  const template = await readPrompt(t.ctx, "stage5_docstrings.txt");

  // One pass and, when it leaves defects (a crosslink naming no binder), a second on exactly those.
  for (let pass = 1; ; pass += 1) {
    // Snapshot the exact bytes of every target file BEFORE the codex pass, so a build-failure
    // rollback restores only this pass's docstring edits. NEVER `git checkout` here: it reverts
    // to HEAD and destroys unrelated uncommitted work this pass did not author.
    const snapshot = new Map<string, string>();
    for (const f of new Set(undoc.map((e) => e.file))) {
      snapshot.set(f, await readFile(path.join(root, f), "utf8"));
    }
    const lanes = docstringLanes(undoc);
    const calls = lanes.reduce((n, l) => n + l.length, 0);
    console.log(`[${t.label}] docstring pass ${pass}: ${undoc.length} declaration(s) in ${calls} call(s)`);
    let k = 0;
    // after a killed call the pass dispatches nothing new: a hang that hits every call (a tool that
    // never comes up) would otherwise cost every call its full watchdog time; the residual pass retries
    let killed = false;
    await mapLimit(lanes, DOCSTRING_CONCURRENCY, async (lane) => {
      for (const batch of lane) {
        if (killed) return;
        k += 1;
        const label = `${t.label} docstrings ${k}/${calls}`;
        if (!(await unlessKilled(label, () => dispatchAgent({
          ctx: t.ctx,
          deps: t.deps,
          stage: "5",
          label,
          prompt: fillTemplate(template, { package_root: root, decl_list: declListFor(batch) }),
          promptSources: ["stage5_docstrings.txt"],
          model: MODEL_PLAN.stage5.model,
          reasoningEffort: MODEL_PLAN.stage5.effort,
        })))) killed = true;
      }
    });
    for (const f of snapshot.keys()) {
      const abs = path.join(root, f);
      const { text: whole, closed } = closeUnterminatedDocstrings(await readFile(abs, "utf8"));
      const { text: single, collapsed } = collapseAdjacentDocstrings(whole);
      const { text: placed, moved } = docstringAfterScopePrefix(single);
      const { text: tagged, restored } = restoreDocstringTags(snapshot.get(f)!, placed);
      const { text, fixed } = normalizeDocstringEndings(tagged);
      if (closed > 0 || collapsed > 0 || moved > 0 || restored > 0 || fixed > 0) await writeFile(abs, text, "utf8");
      if (closed > 0) console.warn(`[${t.label}] ${f}: ${closed} docstring(s) left open were closed`);
      if (moved > 0) console.warn(`[${t.label}] ${f}: ${moved} docstring(s) written above an \`… in\` prefix were moved onto the declaration`);
      if (collapsed > 0) console.warn(`[${t.label}] ${f}: ${collapsed} declaration(s) carried two docstrings — kept the crosslinked one`);
      if (restored > 0) console.warn(`[${t.label}] ${f}: ${restored} tag line(s) the docstring pass dropped were put back`);
    }
    let residual: UndocumentedDecl[];
    try {
      residual = await extractUndocumented(t.modules);
    } catch (err) {
      if (err instanceof LakeFailure && !err.leanError) {
        // Lake did not finish or broke on its own: the docstrings are not the defect and stay
        // on disk (no clean record is written, so the resume re-checks them).
        return (
          `${t.label} docstring pass could not be validated — lake did not finish (the edits are kept):\n${err.message}\n` +
          `Resume to validate them again; fix the build or toolchain first if the failure is not transient.`
        );
      }
      // Keep the rejected edit (the only evidence of what the model wrote) before restoring.
      const rejectedDir = path.join(t.outDir, "docstring_rejected");
      for (const [f, content] of snapshot) {
        const abs = path.join(root, f);
        try {
          const keep = path.join(rejectedDir, f);
          await mkdir(path.dirname(keep), { recursive: true });
          await writeFile(keep, await readFile(abs, "utf8"), "utf8");
        } catch (keepErr) {
          // Evidence is best-effort; the restore below must run regardless.
          console.warn(`[${t.label}] could not keep rejected ${f}: ${keepErr instanceof Error ? keepErr.message : String(keepErr)}`);
        }
        await writeFile(abs, content, "utf8");
      }
      return (
        `${t.label} docstring pass broke the build; its edits were restored byte-for-byte ` +
        `(rejected versions kept under ${rejectedDir}):\n${err instanceof Error ? err.message : String(err)}\n` +
        `Document the declarations by hand (first paragraph = NL translation) then resume.`
      );
    }
    if (residual.length > 0) {
      if (pass < MAX_DOCSTRING_PASSES) {
        console.warn(`[${t.label}] docstring pass ${pass}: ${residual.length} declaration(s) still undocumented or crosslink-defective — one more pass on those`);
        undoc = residual;
        continue;
      }
      return (
        `${t.label} docstring coverage: ${residual.length} declaration(s) still undocumented or crosslink-defective after the docstring pass — ` +
        residual.slice(0, 12).map((e) => `${e.file}:${e.line} ${e.name}${e.problem ? ` (${e.problem})` : ""}`).join(", ") +
        (residual.length > 12 ? ` (+${residual.length - 12} more)` : "") +
        `. Fix them (the docstring contract: first paragraph = the NL translation, with ` +
        `[phrase](hyp:name)/[phrase](goal) crosslinks covering every hypothesis and the conclusion) then resume.`
      );
    }
    await recordClean();
    return null;
  }
}

/**
 * Ensure every declaration in the run's Lean modules carries a contract docstring (see
 * documentModules). Returns `null` when coverage holds; otherwise a block reason for the F5
 * caller (same contract as the crosswalk emit). Runs BEFORE the crosswalk emit: docstring
 * insertion shifts line numbers, and the banked crosswalk must record the post-docstring lines.
 */
export async function ensureDocstringCoverage(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  /** See `DocstringTarget.builtModules`. */
  builtModules?: readonly string[];
}): Promise<string | null> {
  const paths = artifactPaths(args.ctx, args.state);
  const relFiles = (await readdir(paths.leanDir, { recursive: true }).catch((err: NodeJS.ErrnoException) => {
    if (err.code === "ENOENT") return [] as string[]; // no Lean dir — nothing to document
    throw err; // any other readdir failure must not silently pass the gate
  })).map(String);
  const prefix = args.state.lean_subdir.replace(/\//g, ".");
  // Include the root umbrella module (`<leanDir>.lean`, a sibling of the dir): it is
  // import-only by convention, but a declaration landing there must still be covered.
  const rootModule = existsSync(`${paths.leanDir}.lean`) ? [prefix] : [];
  const modules = [...rootModule, ...moduleNamesFor(args.state.lean_subdir, relFiles)];
  return documentModules({
    ctx: args.ctx, deps: args.deps, modules, prefix,
    outDir: paths.formalizationDir, label: "F5", builtModules: args.builtModules,
  });
}
