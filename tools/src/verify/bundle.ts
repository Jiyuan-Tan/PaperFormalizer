/**
 * V6 corrected-paper bundle — `runs/<slug>/bundle/`, a self-contained directory to submit from.
 *
 *   corrected_paper/ the author's source tree with the corrections written in (`corrected_tex.ts`; a
 *               block a repair split off a result is a corollary or a proposition of the paper after it): their
 *               class, preamble, bibliography, figures and layout, plain TeX with no macro, colour or
 *               word of the review; a condition
 *               added to a result is the last paragraph of its statement; compiled with the annotated paper's compiler. `TODO.md` lists, each
 *               with file:line, what still keeps it from being ready to submit.
 *   lean/       a standalone Lake project to send to a third person: the paper's Lean
 *               (`Papers/<Name>` without `tmp/`), the toolkit modules it imports, a generated lakefile
 *               requiring the public base libraries only, the pin, `Check.lean` and a README
 *               (`bundle_lean.ts`; checked self-contained, and against the local base checkouts).
 *   page/       `page.json`: the paper's page as the local UI draws it, for a reader with the bundle
 *               alone (`ui/page_snapshot.ts`).
 *   MATCH.md    each result beside its Lean declaration (`bundle_match.ts`).
 *   REPORT.md   the report (the stage copies it in once rendered).
 *   f4_seal.json the two reviewers' F4 receipts under one code (`f4_seal.ts`), and
 *   f4_reviews.log what they answered at each F4 pass, as the run logged it.
 *   bundle.json what was written and what the checks found.
 *
 * Deterministic and model-free; no `lake`. The corrected TeX is derived from the SAME plan as the
 * annotated paper (`planAnnotations`, corrected view), so the two never disagree on what a repair
 * replaces. The mechanical part of "the corrected paper reads as a complete paper" is checked here:
 * it compiles, every reference resolves, every passage that refers to a corrected result is listed,
 * every result with no repair and every correction that found no place is listed. Whether the
 * abstract, introduction and discussion still say what the corrected results say is NOT checked —
 * that needs a reader — and `TODO.md` says so.
 */
import { existsSync, realpathSync } from "node:fs";
import { cp, mkdir, readdir, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { applyEdits, compileGuarded, compileTex, planAnnotations, readSourceTex, sourceFailureNote, type AnnotationInput, type CompileResult, type CompileTex } from "./annotated_paper.js";
import { SOURCE_COMPILE_RECORD, sourceBaseline, undefinedCitations } from "./annotated_compile.js";
import { blankTexComments } from "../shared/tex_text.js";
import { documentClassOf, preambleOf } from "./annotate_tex.js";
import { AUTHOR_NOTES_FILE, SOURCE_FILLER, unwrapSource, withoutFillerLines } from "./note_macros.js";
import { loadCatalog, repoRoot, type Catalog } from "../toolkit/init.js";
import { checkSelfContained, compareLocal, leanHeader, planRequires, renderLakefile, rootModule, toolkitRequires, type Git, type LocalCompare, type PublicTree } from "./bundle_lean.js";
import { currentStatements, nodeTags, renderMatch, type NlLinksResult, type NodeTag } from "./bundle_match.js";
import { PAGE_FILE, pageSnapshot } from "../ui/page_snapshot.js";
import { TIKZ_DIR } from "../ui/tikz.js";
import { blankPaths, checkF4Seal, F4_REVIEWS_FILE, F4_SEAL_FILE, f4Reviews, REVIEWER_CALLS_LOG, sha256, withBundle, type F4Seal } from "./f4_seal.js";
import { auxLabels, correctedTex, envSpanOfLabel, labelsDefined, refsIn, type CorrectedItem } from "./corrected_tex.js";
import { splitCount, splitKind } from "./core_graph.js";
import { resultNames } from "./report_plain.js";
import type { ReportBundle, ReportRow, VerifyReportJson } from "./report.js";
import { BUILTIN_ENVS, blankInactiveToggles, parseTheoremCounters, readToggles, stripIffalse } from "./tex_envs.js";
import { texVerdicts } from "./tex_fragment_check.js";

export const BUNDLE_DIR = "bundle";
/** The corrected paper's folder in the bundle (`bundle.json` `paper.dir`). */
export const PAPER_DIR = "corrected_paper";
/** `runs/<slug>/<this>`: the last compile of the corrected paper (the compile guard reads it). */
export const BUNDLE_COMPILE_RECORD = "logs/bundle_compile.json";

/** What the seal names of a bundle: the files under these folders. */
const SEALED = new RegExp(`^(?:lean|${PAPER_DIR}|page)/`, "u");

/** One thing between the corrected paper and a submission. */
export interface TodoItem {
  group: TodoGroup;
  file: string | null;
  line: number | null;
  text: string;
}
export type TodoGroup = "lean-contained" | "lean-public" | "compile" | "compile-original" | "not-established" | "unplaced" | "references" | "proofs" | "proof-added" | "numbering" | "references-original" | "kept";
const GROUPS: ReadonlyArray<{ id: TodoGroup; blocking: boolean; title: string; lead: string }> = [
  { id: "compile", blocking: true, title: "The paper does not compile", lead: "Errors of the compile of the corrected source." },
  { id: "compile-original", blocking: true, title: "The original source does not compile on this installation", lead: "Not caused by a correction: the paper's unmodified source fails with the same errors under the TeX installed here, so the corrected paper was not compiled cleanly here either. Before submitting from this directory, compile it with the TeX distribution the paper was written for, or fix these." },
  { id: "not-established", blocking: true, title: "Results that are not established", lead: "Printed as in the original, although the review refuted them or could not check them as printed and no correction was adopted, or they were left out of the corrected paper's formal development. Remove, restate or qualify each before submitting." },
  { id: "unplaced", blocking: true, title: "Corrections not written into the paper", lead: "The correction exists (see the report) but its place in the source was not found, or its text does not typeset. Apply each by hand." },
  { id: "references", blocking: true, title: "Unresolved references", lead: "References and citations the compiled paper does not resolve." },
  { id: "proofs", blocking: true, title: "Two proofs of one result", lead: "The corrected proof was written after the printed proof it replaces, which could not be replaced in place. Remove the superseded one." },
  { id: "lean-contained", blocking: true, title: "The Lean directory is not self-contained", lead: "`lean/` is meant to be sent to a third person, who builds it with the public libraries alone. Each item keeps them from doing so." },
  { id: "lean-public", blocking: false, title: "The Lean directory may not build as it was built here (to check)", lead: "`lean/` requires each base library at its public revision; the development was built against a local copy whose content differs from it. A reader's build may differ: build `lean/` from scratch to see, or publish the library and check the paper again." },
  { id: "proof-added", blocking: false, title: "Proofs added", lead: "A corrected proof with no printed proof found to replace." },
  { id: "numbering", blocking: false, title: "Numbers and labels", lead: "A correction replaced text that carried numbered displays, or added a numbered result." },
  { id: "references-original", blocking: false, title: "References unresolved in the original source too", lead: "Not caused by a correction." },
  { id: "kept", blocking: false, title: "Kept as printed, no longer used", lead: "Printed conditions and definitions the corrected results no longer rely on (they state what they use themselves). Keep, reword or delete." },
];

/** Whether a TODO item keeps the paper from being submitted (its group is a blocking one). Pure. */
export const isBlockingTodo = (i: Pick<TodoItem, "group">): boolean => GROUPS.find((g) => g.id === i.group)?.blocking ?? true;

export interface BundleArgs {
  runDir: string;
  toolkitRoot: string;
  slug: string;
  /** Where the bundle is written (default `<runDir>/bundle`). */
  outDir?: string;
  mainFile: string;
  /** `Papers/<Name>`, or null when the run has no Lean (it stopped before the formalization). */
  leanSubdir: string | null;
  /** The annotated paper's records, as V6 reads them (nothing pending). */
  input: Omit<AnnotationInput, "files" | "pending" | "correctedView" | "texVerdicts">;
  report: VerifyReportJson;
  /** Declarations of the paper a promotion round moved into the toolkit. */
  promoted?: readonly string[];
  /** The run's F4 seal (`f4_seal.ts`); absent when the run has no Lean. The reviews it travels with
   * are read from the run's reviewer log here. */
  seal?: F4Seal;
  compile?: CompileTex;
  /** The compile record's path (default under the run's `logs/`). */
  compileRecord?: string;
  /** Compile-check the run's fragments as the annotated paper does (cached in the run); `false`
   * writes nothing into the run. */
  checkFragments?: boolean;
  /** The base-library catalogue (default `tools/data/libraries.json`) and the directory its `path`
   * requires are relative to (default this repository). */
  catalog?: Catalog;
  libraryRoot?: string;
  /** Read-only git on a base library's local checkout. */
  git?: Git;
  /** The public revision of a base library, to compare the local content with (the network: only
   * on request — `report --verify-public`). */
  publicTree?: PublicTree;
  log?: (msg: string) => void;
}

export interface BundleResult {
  dir: string;
  bundle: ReportBundle;
  names: Record<string, string>;
  todo: TodoItem[];
}

/** The regular files under `dir`, by path from it. A link is refused: the bundle holds regular
 *  files only (copies are dereferenced), so one met here would be a file the seal cannot name. */
async function walk(dir: string, skip: (rel: string, isDir: boolean) => boolean, rel = ""): Promise<string[]> {
  const out: string[] = [];
  for (const e of (await readdir(path.join(dir, rel), { withFileTypes: true })).sort((a, b) => a.name.localeCompare(b.name))) {
    const r = rel ? `${rel}/${e.name}` : e.name;
    if (e.isSymbolicLink()) throw new Error(`${path.join(dir, r)} is a link: the bundle holds regular files only`);
    if (skip(r, e.isDirectory())) continue;
    if (e.isDirectory()) out.push(...(await walk(dir, skip, r)));
    else if (e.isFile()) out.push(r);
  }
  return out;
}

/** The paths that name the machine a bundle is written on: `dirs`, this repository, the home and
 *  temp directories, each as given and as resolved. */
function machinePaths(dirs: readonly string[]): string[] {
  const real = (p: string): string => { try { return realpathSync(p); } catch { return p; } };
  return [...dirs, repoRoot(), os.homedir(), os.tmpdir()].flatMap((p) => [path.resolve(p), real(p)]);
}

/** Where `text` names the machine's user `who` as part of a path — `/home/<who>`, `C:\\Users\\<who>` (in
 *  JSON, its backslashes doubled), `~<who>`: the name right after a path separator or `~` and right
 *  before another or the end of the path. The name as a word of prose ("the root-n rate" on a
 *  machine whose user is `root`) is not a path. Null when it is named in none, or is too short to tell. Pure. */
export function userPathIn(text: string, who: string): string | null {
  if (who.length <= 2) return null;
  const name = who.replace(/[.*+?^${}()|[\]\\]/gu, "\\$&");
  return new RegExp(`(?:[\\\\/]|~)${name}(?=[\\\\/"'\\s:]|$)`, "iu").exec(text)?.[0] ?? null;
}

/** The compile log's located errors (`-file-line-error`), first few. */
function logErrors(log: string): Array<{ file: string; line: number; msg: string }> {
  return [...log.matchAll(/^(?:\.\/)?([^\s:][^:\n]*\.(?:tex|sty|cls|bbl)):(\d+): (.*)$/gmu)].slice(0, 12).map((m) => ({ file: m[1]!, line: Number(m[2]), msg: m[3]!.trim() }));
}

/** The TODO list as markdown. Pure. */
export function renderTodo(slug: string, items: readonly TodoItem[], note: string | null): string {
  const L = [`# Before submitting — ${slug}`, ""];
  const blocking = items.filter((i) => GROUPS.find((g) => g.id === i.group)!.blocking).length;
  L.push(
    items.length === 0
      ? "The mechanical checks leave nothing open: the corrected paper compiles, every reference resolves, every correction is written in, and no passage outside a corrected result refers to one."
      : `${items.length} item(s), ${blocking} of them blocking. Lines are those of the corrected source in this directory.`,
    "",
  );
  if (note) L.push(note, "");
  for (const g of GROUPS) {
    const mine = items.filter((i) => i.group === g.id);
    if (mine.length === 0) continue;
    L.push(`## ${g.title}${g.blocking ? "" : " (to check)"}`, "", g.lead, "");
    for (const i of mine) L.push(`- ${i.file ? `\`${i.file}${i.line ? `:${i.line}` : ""}\` — ` : ""}${i.text.replace(/\s+/gu, " ").trim()}`);
    L.push("");
  }
  return `${L.join("\n")}\n`;
}

/** The TODO items of the citations the corrected paper's compile left undefined: one the unmodified
 * source's compile (`original`: its baseline, compiled the same way; null when it could not be had)
 * leaves undefined too is the source's (not blocking); any other is blocking. Pure. */
export function citationItems(cites: readonly string[], original: ReadonlySet<string> | null, mainFile: string, reason: string | null | undefined): TodoItem[] {
  const list = (xs: string[]): string => `${xs.length} citation(s) (${xs.slice(0, 8).join(", ")}${xs.length > 8 ? ", …" : ""})`;
  const own = original ? cites.filter((c) => original.has(c)) : [];
  const ours = cites.filter((c) => !own.includes(c));
  return [
    ...(own.length > 0 ? [{ group: "references-original" as const, file: mainFile, line: null, text: `${list(own)} undefined: the original source leaves them undefined too` }] : []),
    ...(ours.length > 0 ? [{ group: "references" as const, file: mainFile, line: null, text: `${list(ours)} undefined in the corrected paper${original ? ", which the original source resolves or does not cite" : " (the original source could not be compiled to compare)"}${reason ? ` (${reason})` : ""}` }] : []),
  ];
}

/** The corrected paper: `corrected_paper/` written, compiled and checked. */

/** The keys the unmodified source's compile leaves undefined, to compare with the corrected paper's;
 * null when there is no complete baseline (not compiled, or timed out: a log cut short names every
 * key undefined). Pure. */
export function baselineCitations(base: { status: string; reason?: string | null; undefined_citations?: string[] } | null): Set<string> | null {
  return base && base.status !== "skipped" && !/timed out/u.test(base.reason ?? "") ? new Set(base.undefined_citations ?? []) : null;
}
async function writePaper(a: BundleArgs, dir: string, log: (m: string) => void): Promise<{ compile: CompileResult; pages: number | null; todo: TodoItem[]; names: Record<string, string>; unwrapped: string[] }> {
  const src = path.join(a.runDir, "source");
  const paper = path.join(dir, PAPER_DIR);
  // a link in the source (a shared bibliography, a figure) becomes the file itself: the seal hashes it
  await cp(src, paper, { recursive: true, dereference: true });
  const { files: source, enc } = await readSourceTex(src, a.mainFile, a.input.envs);
  // The run read the paper with its authors' note macros read away: a correction replaces text it was
  // shown, so a file that held such a macro is written as it was read (a wrapper is never left half).
  const notes = a.input.envs.note_macros ?? null;
  const files = notes ? Object.fromEntries(Object.entries(source).map(([f, t]) => [f, unwrapSource(t, notes, "remove", SOURCE_FILLER)])) : source;
  const unwrapped = Object.keys(files).filter((f) => files[f] !== source[f]).sort();
  let plan = planAnnotations({ ...a.input, files, pending: null, correctedView: true });
  if (a.checkFragments !== false) {
    const failing = await texVerdicts(plan.fragments, { runDir: a.runDir, mainFile: a.mainFile, log });
    if (failing.size > 0) plan = planAnnotations({ ...a.input, files, pending: null, correctedView: true, texVerdicts: failing });
  }
  // what the paper loads, declares and uses: a commented-out `\usepackage` or `\begin{proof}` is none
  const all = blankTexComments(Object.values(files).join("\n"));
  const pre = blankTexComments(preambleOf(files[a.mainFile] ?? ""));
  const cls = documentClassOf(files[a.mainFile] ?? "") ?? "";
  const loads = (re: RegExp): boolean => re.test(pre);
  // The paper's corollary environment, and its proposition environment (a block a repair split off is
  // one or the other): one it declares, else a standard name its class defines (it is used).
  const counters = parseTheoremCounters(all);
  const envOfKind = (want: string): { name: string; numbered: boolean } | null => {
    const n = Object.entries(a.input.envs.newtheorem).find(([n, kind]) => kind === want && !n.endsWith("*") && (n in counters.display || (n in BUILTIN_ENVS && all.includes(`\\begin{${n}}`))))?.[0];
    return n ? { name: n, numbered: n in counters.counterOf || !(n in counters.display) } : null;
  };
  const opts = {
    proofEnv: /\\begin\s*\{proof\}/u.test(all) || loads(/\{[^}]*\bamsthm\b[^}]*\}/u),
    corollaryEnv: envOfKind("corollary"),
    propositionEnv: envOfKind("proposition"),
    plain: {
      eqref: !loads(/\{[^}]*\b(?:amsmath|mathtools)\b[^}]*\}/u) && !/^ams/u.test(cls) && !/\\eqref\b/u.test(all),
      cref: !loads(/\{[^}]*\bcleveref\b[^}]*\}/u),
      autoref: !loads(/\{[^}]*\bhyperref\b[^}]*\}/u),
      natbib: !loads(/\{[^}]*\bnatbib\b[^}]*\}/u) && !/\\cite[tp]\b/u.test(all),
    },
  };
  const todo: TodoItem[] = [];
  const corrected: Record<string, string> = {};
  const raw: Array<CorrectedItem & { file: string }> = [];
  /** Where each corollary a repair split off is written. */
  const corollaryAt = new Map<string, { file: string; from: number; to: number }>();
  for (const f of Object.keys(files).sort()) {
    const r = correctedTex(applyEdits(files[f]!, plan.edits[f] ?? []), opts);
    // a line the reading emptied is not kept in the paper the author goes on editing
    if (notes && r.tex.includes(SOURCE_FILLER)) {
      const fillers = r.tex.split("\n").flatMap((l, i) => (l === SOURCE_FILLER ? [i + 1] : []));
      const moved = (line: number): number => line - fillers.filter((k) => k < line).length;
      for (const i of r.items) i.line = moved(i.line);
      for (const c of r.corollaries) [c.from, c.to] = [moved(c.from), moved(c.to)];
      r.tex = withoutFillerLines(r.tex);
    }
    corrected[f] = r.tex;
    raw.push(...r.items.map((i) => ({ ...i, file: f })));
    for (const c of r.corollaries) corollaryAt.set(c.node, { file: f, from: c.from, to: c.to });
    if (r.tex !== source[f]) await writeFile(path.join(paper, f), r.tex, enc[f] ?? "utf8");
  }

  // --- compile, with the annotated paper's compiler and guard; its by-products do not stay.
  const before = new Set(await walk(paper, () => false));
  const compile = await compileGuarded({ recFile: a.compileRecord ?? path.join(a.runDir, BUNDLE_COMPILE_RECORD), dir: paper, mainFile: a.mainFile, compile: a.compile ?? compileTex, sourceDir: src, log: (m) => log(m.replace(/^annotated paper/u, "corrected paper")) });
  const base = a.mainFile.replace(/\.tex$/iu, "");
  const read = async (ext: string): Promise<string> => (existsSync(path.join(paper, `${base}.${ext}`)) ? readFile(path.join(paper, `${base}.${ext}`), "latin1") : "");
  // The guard skips a tree whose identical copy just failed on the paper's own TeX: still a failure.
  const failed = compile.status === "failed" || (compile.status === "skipped" && compile.tool !== null);
  const logText = (await read("log")) || compile.log_tail;
  // A compile that stopped early leaves no usable `.aux`: the labels the source defines stand in.
  const aux = compile.status === "passed" ? auxLabels(await read("aux")) : null;
  for (const f of await walk(paper, () => false)) if (!before.has(f) && f !== compile.pdf) await rm(path.join(paper, f), { force: true });
  const flatLog = logText.replace(/\n/gu, "");
  const pages = compile.pdf ? Number(/Output written on .*?\((\d+) pages?/u.exec(flatLog)?.[1] ?? NaN) || null : null;

  const envName = new Map(a.input.envs.envs.map((e) => [e.id, e.envName]));
  const names = resultNames(a.report.results, (l) => aux?.get(l), (r) => {
    const n = envName.get(r.env_id);
    return n !== undefined && !(n in counters.counterOf) && (n in counters.display || n.endsWith("*"));
  });
  const nameOf = (id: string | null): string => (id && names[id]) || "a condition or definition of the paper";
  const where = (r: ReportRow): { file: string; line: number | null } => {
    const c = corollaryAt.get(r.node_id);
    if (c) return { file: c.file, line: c.from };
    for (const [f, t] of Object.entries(corrected)) {
      const s = r.label ? envSpanOfLabel(t, r.label) : null;
      if (s) return { file: f, line: s.from };
    }
    return { file: /^(.*):\d+-\d+$/u.exec(r.locator)?.[1] ?? a.mainFile, line: null };
  };

  // The errors the unmodified source has too (`compileGuarded`) are not a correction's: their own group.
  const ofSource = compile.source_failure;
  const sourceLines = new Set((ofSource?.lines ?? []).map((l) => l.replace(/^\.\//u, "")));
  const first = !failed ? undefined : ofSource?.only ? `the original source itself does not compile on this installation (${compile.tool}: ${ofSource.error})` : /^! (?:LaTeX Error: )?(.*)$/mu.exec(logText)?.[1]?.trim();
  if (failed && ofSource) {
    const theirs = logErrors(logText).filter((e) => sourceLines.has(`${e.file}:${e.line}: ${e.msg}`) && !/Emergency stop|Fatal error/u.test(e.msg));
    const missing = /File `([^']*)' not found/u.exec(ofSource.error)?.[1];
    if (missing) todo.push({ group: "compile-original", file: a.mainFile, line: null, text: `the source needs \`${missing}\`, which is not among the paper's files: add it` });
    else if (theirs.length === 0) todo.push({ group: "compile-original", file: a.mainFile, line: null, text: `${compile.tool}: ${ofSource.error}` });
    for (const e of theirs) todo.push({ group: "compile-original", file: e.file, line: e.line, text: `${compile.tool}: ${e.msg}` });
  }
  if (failed && !ofSource?.only) {
    const errs = logErrors(logText).filter((e) => !sourceLines.has(`${e.file}:${e.line}: ${e.msg}`));
    const missing = /File `([^']*)' not found/u.exec(first ?? "")?.[1];
    todo.push({ group: "compile", file: errs[0]?.file ?? a.mainFile, line: errs[0]?.line ?? null, text: missing ? `the source needs \`${missing}\`, which is not among the paper's files (the original source does not compile without it either): add it` : `${compile.tool} failed: ${first ?? compile.reason}` });
    for (const e of errs.slice(1).filter((x) => !/Emergency stop|Fatal error/u.test(x.msg))) todo.push({ group: "compile", file: e.file, line: e.line, text: e.msg });
  }
  // --- what the corrected text itself could not settle.
  const group: Record<CorrectedItem["kind"], TodoGroup> = { "not-repaired": "not-established", unplaced: "unplaced", superseded: "kept", "no-longer-used": "kept", "second-proof": "proofs", "proof-added": "proof-added", "label-lost": "numbering", numbering: "numbering" };
  const flaggedOpen = new Set<string>();
  // A suggested repair that was not adopted may split the result: its blocks are not the paper's.
  const proposed = (node: string | null): string => {
    const sr = a.input.patches?.unfixable?.find((u) => u.node === node)?.suggested_repair;
    const cors = sr?.corollaries ?? [];
    const label = a.report.results.find((r) => r.node_id === node)?.label;
    return cors.length > 0 ? `; the suggested repair, which was not adopted, would state it with ${splitCount(cors.map((c) => splitKind(c.follows, label, !!(sr as { umbrella?: boolean }).umbrella)))}: ${cors.length === 1 ? "it is" : "they are"} not written into the paper` : "";
  };
  for (const i of raw) {
    if (i.kind === "superseded") continue; // the restated statement carries it: nothing to do
    if (i.kind === "not-repaired" && i.node) flaggedOpen.add(i.node);
    todo.push({ group: group[i.kind], file: i.file, line: i.line, text: `${nameOf(i.node)}: ${i.detail}${i.kind === "not-repaired" ? proposed(i.node) : ""}` });
  }
  for (const r of a.report.results) {
    if (flaggedOpen.has(r.node_id) || !(r.bucket === "refuted" || r.bucket === "not_determined" || r.change?.descoped)) continue;
    const shown = r.split_from ? "it is written into the paper as its repair states it" : "it is printed as in the original";
    todo.push({ group: "not-established", ...where(r), text: `${names[r.node_id]}: ${r.change?.descoped ? `left out of the corrected paper's formal development (it has no repair, or rests on a result that has none); ${shown}` : r.bucket === "not_determined" ? `this result could not be checked as printed (the paper does not determine what is claimed) and no reading or repair was adopted; ${shown}` : `the review refuted this result and no repair was adopted; ${shown}`}${proposed(r.node_id)}` });
  }
  for (const u of plan.unlocated.filter((x) => x.placed === null && x.kind !== "clarification (reading)")) {
    const what = u.kind === "corrected proof" ? "its corrected proof" : u.kind === "no longer used" ? "the passage no corrected result uses" : u.kind === "error (not repaired)" ? "the refuted passage" : u.kind === "not determined" ? "the passage that could not be checked" : u.kind === "condition added" ? "the place of a condition added to it" : "its correction";
    todo.push({ group: u.kind === "no longer used" ? "kept" : u.kind === "error (not repaired)" || u.kind === "not determined" ? "not-established" : "unplaced", file: null, line: null, text: `${nameOf(u.node)}: ${what} was not found in the source (${u.reason})` });
  }
  for (const d of plan.defects) todo.push({ group: "unplaced", file: null, line: null, text: `${nameOf(d.node)}: a text of the correction does not typeset (${d.block}): ${d.reason}` });

  // --- references: every one resolves (the compiled `.aux`, else the labels the source defines).
  // A `%` comment and an `\iffalse … \fi` block are not typeset: their references and labels are not
  // the paper's (comments first, so a commented `%\iffalse` or `% \fi` toggles nothing).
  // So is the branch of an etoolbox `\iftoggle` the paper's toggles do not select — after `\iffalse`, as TeX:
  // a dead block's text never reaches the toggle reader.
  const stripped = (f: string, t: string): string => {
    const live = blankTexComments(t);
    try { return stripIffalse(live, f); } catch (e) { log(`corrected paper: ${(e as Error).message}; its \\iffalse blocks are read as text`); return live; }
  };
  const toggles = readToggles(Object.entries(corrected).map(([f, t]) => stripped(f, t)).join("\n"));
  const skipIffalse = (f: string, t: string): string => blankInactiveToggles(stripped(f, t), toggles);
  const defined = aux ?? new Set(Object.entries(corrected).flatMap(([f, t]) => labelsDefined(skipIffalse(f, t))));
  const original = new Set(Object.entries(files).flatMap(([f, t]) => labelsDefined(skipIffalse(f, t))));
  for (const [f, t] of Object.entries(corrected)) {
    for (const r of refsIn(skipIffalse(f, t))) {
      if (defined.has(r.label)) continue;
      todo.push({ group: original.has(r.label) ? "references" : "references-original", file: f, line: r.line, text: `\`\\${r.command}{${r.label}}\` does not resolve${original.has(r.label) ? ": the label was in text a correction replaced" : ""}` });
    }
  }
  // A citation the unmodified source's compile leaves undefined too is the source's; any other is ours.
  const cites = undefinedCitations(flatLog);
  if (cites.length > 0) {
    const base = await sourceBaseline({ sourceDir: src, cacheFile: path.join(path.dirname(a.compileRecord ?? path.join(a.runDir, BUNDLE_COMPILE_RECORD)), SOURCE_COMPILE_RECORD), mainFile: a.mainFile, compile: a.compile ?? compileTex }).catch(() => null);
    todo.push(...citationItems(cites, baselineCitations(base), a.mainFile, compile.reason));
  }

  return { compile: failed ? { ...compile, status: "failed", reason: first ?? compile.reason } : compile, pages, todo, names, unwrapped };
}

/** What `lean/` holds and what its checks found. */
interface LeanBundle extends NonNullable<ReportBundle["lean"]> {
  tags: Map<string, NodeTag>;
  /** The paths that name the machine the bundle is written on. */
  machine: string[];
  rel: string;
  todo: TodoItem[];
}

/**
 * `lean/`: a standalone Lake project — the paper's modules, the toolkit modules they import (and
 * theirs), a generated lakefile requiring the public base libraries only (a library with no public
 * form vendored), the pinned toolchain, `Check.lean` and a README. No `lake-manifest.json`: the
 * toolkit's names the owner's local checkouts, and a correct one for the generated requires needs
 * the network (Lake resolves it on the first build; every require is pinned to a full revision).
 */
async function writeLean(a: BundleArgs, dir: string, names: Record<string, string>): Promise<LeanBundle | null> {
  if (!a.leanSubdir) return null;
  const from = path.join(a.toolkitRoot, ...a.leanSubdir.split("/"));
  if (!existsSync(from)) return null;
  const lean = path.join(dir, "lean");
  const rel = a.leanSubdir;
  const files = (await walk(from, (r, isDir) => (isDir ? path.basename(r) === "tmp" || path.basename(r).startsWith(".") : !r.endsWith(".lean"))));
  const tags = new Map<string, NodeTag>();
  /** Every module written, with its header. */
  const written = new Map<string, { module: boolean; imports: string[] }>();
  const put = async (srcFile: string, relFile: string): Promise<string> => {
    const text = await readFile(srcFile, "utf8");
    await mkdir(path.dirname(path.join(lean, relFile)), { recursive: true });
    await writeFile(path.join(lean, relFile), text, "utf8");
    written.set(relFile.replace(/\.lean$/u, "").split("/").join("."), leanHeader(text));
    return text;
  };
  for (const f of files) {
    const text = await put(path.join(from, f), `${rel}/${f}`);
    for (const [id, t] of nodeTags(f, text)) if (!tags.has(id)) tags.set(id, t);
  }
  let count = files.length;
  const barrel = rel.split("/").join(".");
  if (existsSync(`${from}.lean`)) { await put(`${from}.lean`, `${rel}.lean`); count += 1; }
  // The toolkit modules it imports, and theirs: copied (they are the user's own, and few).
  const lib = rel.split("/")[0]!;
  const toolkit: string[] = [];
  const done = new Set<string>();
  for (let grew = true; grew; ) {
    grew = false;
    for (const m of [...new Set([...written.values()].flatMap((h) => h.imports))].sort()) {
      const root = m.split(".")[0]!;
      if (done.has(m) || root === lib || !existsSync(path.join(a.toolkitRoot, `${root}.lean`)) || !existsSync(path.join(a.toolkitRoot, root))) continue;
      done.add(m);
      const file = `${m.split(".").join("/")}.lean`;
      if (!existsSync(path.join(a.toolkitRoot, file))) continue;
      await put(path.join(a.toolkitRoot, file), file);
      toolkit.push(m);
      grew = true;
    }
  }
  toolkit.sort();
  // A root module per library, so `lake build` builds all of it: the paper's barrel (what the run
  // built) or, without one, each of its files; every toolkit module copied.
  const roots = (ms: string[]): Array<{ name: string; module: boolean }> => ms.map((name) => ({ name, module: written.get(name)!.module }));
  const paperModules = [...written.keys()].filter((m) => m.startsWith(`${barrel}.`)).sort();
  const libs = [...new Set([lib, ...toolkit.map((m) => m.split(".")[0]!)])];
  for (const l of libs) {
    if (written.has(l)) continue;
    const text = rootModule(roots(l === lib ? (written.has(barrel) ? [barrel] : paperModules) : toolkit.filter((m) => m.split(".")[0] === l)));
    await writeFile(path.join(lean, `${l}.lean`), text, "utf8");
    written.set(l, leanHeader(text));
  }
  const built = new Set<string>();
  for (const queue = [...libs]; queue.length > 0; ) {
    const m = queue.pop()!;
    if (built.has(m) || !written.has(m)) continue;
    built.add(m);
    queue.push(...written.get(m)!.imports);
  }
  const unbuilt = paperModules.filter((m) => !built.has(m));

  // The base libraries: what the copied code imports from outside, in its public form.
  const catalog = a.catalog ?? loadCatalog();
  const lakefileToml = existsSync(path.join(a.toolkitRoot, "lakefile.toml")) ? await readFile(path.join(a.toolkitRoot, "lakefile.toml"), "utf8") : null;
  const own = toolkitRequires(lakefileToml);
  const external = new Map<string, Set<string>>();
  for (const h of written.values()) {
    for (const m of h.imports) {
      const root = m.split(".")[0]!;
      if (!written.has(m)) external.set(root, (external.get(root) ?? new Set()).add(m));
    }
  }
  let manifest: Array<{ name: string; rev?: string }> = [];
  try {
    manifest = (JSON.parse(await readFile(path.join(a.toolkitRoot, "lake-manifest.json"), "utf8")) as { packages?: Array<{ name: string; rev?: string }> }).packages ?? [];
  } catch {
    manifest = [];
  }
  const requires = planRequires({ catalog, roots: external.keys(), toolkit: own, toolkitRoot: a.toolkitRoot, libraryRoot: a.libraryRoot ?? repoRoot(), manifest: new Map(manifest.flatMap((p) => (p.rev ? [[p.name, p.rev] as const] : []))) });
  const todo: TodoItem[] = [];
  for (const r of requires.filter((x) => x.form === "vendored")) {
    if (existsSync(r.source!)) await cp(r.source!, path.join(lean, r.path!), { recursive: true, dereference: true, filter: (s) => ![".lake", ".git"].includes(path.basename(s)) });
    else todo.push({ group: "lean-contained", file: null, line: null, text: `${r.name} has no public source in the catalogue and its directory was not found to copy into \`lean/${r.path}\`` });
  }
  await writeFile(path.join(lean, "lakefile.toml"), renderLakefile({ name: a.slug.replace(/[^A-Za-z0-9]+/gu, "-"), libs, requires, toolkitLakefile: lakefileToml }), "utf8");
  // the toolchain goes with the pins: the toolkit's own when a library is pinned where it built on it
  const toolchain = existsSync(path.join(a.toolkitRoot, "lean-toolchain")) ? (await readFile(path.join(a.toolkitRoot, "lean-toolchain"), "utf8")).trim() || null : null;
  const pinnedToolchain = requires.some((r) => r.fromToolkit) && toolchain ? toolchain : catalog.lean_toolchain;
  await writeFile(path.join(lean, "lean-toolchain"), `${pinnedToolchain}\n`, "utf8");
  const decls = a.report.results.flatMap((r) => (r.lean?.decl ? [{ name: names[r.node_id] ?? r.node_id, decl: r.lean.decl, at: `${rel}/${r.lean.file}${r.lean.line ? `:${r.lean.line}` : ""}`, axioms: r.axioms }] : []));
  const checked = [...new Set(decls.map((d) => d.decl))];
  if (checked.length > 0) {
    await writeFile(path.join(lean, "Check.lean"), `import ${lib}\n\n-- The paper's results: each must list no axiom beyond propext, Classical.choice and Quot.sound.\n${checked.map((d) => `#print axioms ${d}`).join("\n")}\n`, "utf8");
  }

  // What was built here against what the third person will fetch.
  const warnings: string[] = [];
  const base: LocalCompare[] = [];
  const localDirs: string[] = [];
  for (const r of requires.filter((x) => x.form === "git" && x.name !== "mathlib")) {
    const t = own.get(r.name);
    const local = t?.path ? path.resolve(a.toolkitRoot, t.path) : path.join(a.toolkitRoot, ".lake", "packages", r.name);
    if (t?.path) localDirs.push(local);
    const reach = [...external].flatMap(([root, ms]) => (root === r.lib || r.provides.includes(root) ? [...ms] : []));
    base.push(await compareLocal(r, local, reach, { git: a.git, publicTree: a.publicTree, verifyCommand: `paperformalizer report ${a.slug} --verify-public` }));
  }
  if (toolchain !== pinnedToolchain) warnings.push(`built with ${toolchain ? `the toolchain \`${toolchain}\`` : "an unrecorded toolchain"}, which differs from the pinned \`${pinnedToolchain}\` this bundle requires`);
  const mathlib = manifest.find((p) => p.name === "mathlib")?.rev ?? null;
  const pinnedMathlib = requires.find((r) => r.name === "mathlib")!.rev!;
  if (mathlib !== pinnedMathlib) warnings.push(`built against Mathlib at ${mathlib ? mathlib.slice(0, 12) : "a revision the toolkit's manifest does not record"}, which differs from the public rev ${pinnedMathlib.slice(0, 12)} this bundle requires`);
  warnings.push(...base.filter((b) => b.status === "differs").map((b) => b.detail));
  if (base.length > 0) await writeFile(path.join(lean, "built-against.json"), `${JSON.stringify(base.map(({ detail: _d, changed: _c, ...b }) => b), null, 2)}\n`, "utf8");
  for (const w of warnings) todo.push({ group: "lean-public", file: null, line: null, text: w });

  const module = rel.split("/").join(".");
  const git = requires.filter((r) => r.form === "git");
  const vendored = requires.filter((r) => r.form === "vendored");
  const R = [`# Lean formalization — ${a.slug}`, ""];
  R.push(`A standalone Lake project: \`${rel}/\` is the Lean development of the corrected paper (${count} file(s)). It depends on the public libraries listed below and on nothing else; what it uses of the author's own library is copied here.`, "");
  R.push("## Build", "", `Lean toolchain: \`${pinnedToolchain}\` (\`lean-toolchain\`; \`elan\` installs it). From this directory:`, "", "```", "lake exe cache get   # fetches the libraries and Mathlib's compiled files", "lake build", ...(checked.length > 0 ? ["lake env lean Check.lean   # the axioms of each result"] : []), "```", "");
  R.push(`\`lake build\` builds ${libs.map((l) => `\`${l}\``).join(" and ")} (\`${module}\` is the paper). There is no \`lake-manifest.json\`: Lake writes it on the first command, from the revisions the lakefile pins.`, "");
  if (unbuilt.length > 0) R.push(`${unbuilt.length} file(s) of \`${rel}/\` are not imported by the paper's root module and are not built: ${unbuilt.map((m) => `\`${m}\``).join(", ")}.`, "");
  R.push("## Libraries it requires", "");
  for (const r of git) R.push(`- \`${r.name}\` (${r.summary}): \`${r.git}\` at \`${r.rev}\`${r.provides.length > 0 ? `; it brings in ${r.provides.map((p) => `\`${p}\``).join(", ")}` : ""}`);
  for (const r of vendored) R.push(`- \`${r.name}\` (${r.summary}): no public repository carries the adapted copy this was built with, so it is included in \`${r.path}/\` with its licence${existsSync(path.join(lean, r.path!, "UPSTREAM.md")) ? ` (\`${r.path}/UPSTREAM.md\`: where it comes from)` : ""}`);
  R.push("");
  // a reminder, never a refusal: the paper was checked on the version it pins
  for (const r of git.filter((x) => x.catalogRev && x.catalogRev !== x.rev)) R.push(`Built on \`${r.name}\` at \`${r.rev!.slice(0, 12)}\`; PaperFormalizer now pins \`${r.catalogRev!.slice(0, 12)}\`. To build on that version, set \`rev = "${r.catalogRev}"\` for \`${r.name}\` in the toolkit's \`lakefile.toml\`, run \`lake update ${r.name}\` and check the paper again.`, "");
  if (warnings.length > 0) R.push("**Warning — this may not be what was built:**", "", ...warnings.map((w) => `- ${w}`), "");
  for (const b of base.filter((x) => x.status !== "differs")) R.push(`${b.status === "same" ? "Verified" : "Note"}: ${b.detail}.`, "");
  R.push("## The paper's results", "");
  if (decls.length === 0) R.push("No result of the report has a Lean declaration.", "");
  else R.push(...decls.map((d) => `- ${d.name}: \`${d.decl}\` (\`${d.at}\`)`), "", "`MATCH.md`, one directory up, sets each statement beside its declaration.", "");
  R.push("## Checking the axioms", "", `${checked.length > 0 ? "`Check.lean` prints the axioms of each result above (`lake env lean Check.lean`, after the build)" : "`#print axioms <declaration>` (through `lake env lean`) prints the axioms of a result"}: none may appear beyond \`propext\`, \`Classical.choice\` and \`Quot.sound\`. The source must contain no \`sorry\`, \`admit\` or \`axiom\`.`, "");
  R.push("## What is in this directory", "");
  R.push(toolkit.length > 0 ? `From the author's own library, copied here (${toolkit.length} module(s)): ${toolkit.map((m) => `\`${m}\``).join(", ")}.` : "Nothing from the author's own library.", "");
  if (external.size > 0) R.push(`Imported from the required libraries: ${[...external].sort(([x], [y]) => x.localeCompare(y)).map(([r, ms]) => `\`${r}\` (${ms.size} module(s))`).join(", ")}.`, "");
  if ((a.promoted ?? []).length > 0) {
    R.push("## Moved into the author's library", "", "Results first proved for this paper and since moved into the library, where the paper now uses them:", "", ...a.promoted!.map((d) => `- \`${d}\``), "");
  }
  R.push("## Self-containment", "");
  const readme = (problems: string[]): string => `${[...R, problems.length === 0 ? "Checked when this directory was written: every import of every file resolves to a file here or to a module of a required library, no path in a lakefile leaves this directory, and nothing names the machine it was built on." : `NOT self-contained — the check made when this directory was written found:\n\n${problems.map((p) => `- ${p}`).join("\n")}`, ""].join("\n")}\n`;
  await writeFile(path.join(lean, "README.md"), readme([]), "utf8");
  const machine = machinePaths([a.toolkitRoot, ...(a.libraryRoot ? [a.libraryRoot] : []), ...localDirs]);
  const problems = await checkSelfContained({ leanDir: lean, requires, forbidden: machine });
  if (problems.length > 0) await writeFile(path.join(lean, "README.md"), readme(problems), "utf8");
  for (const p of problems) todo.push({ group: "lean-contained", file: null, line: null, text: p });
  return {
    files: count, toolkit_modules: toolkit, tags, machine, rel, todo,
    requires: requires.map((r) => ({ name: r.name, form: r.form, ...(r.form === "git" ? { git: r.git!, rev: r.rev!, ...(r.catalogRev && r.catalogRev !== r.rev ? { catalog_rev: r.catalogRev } : {}) } : { path: r.path! }) })),
    toolchain: pinnedToolchain, manifest: false, check: checked.length > 0 ? "Check.lean" : null,
    self_contained: { ok: problems.length === 0, problems }, base, warnings,
    notes: base.filter((b) => b.status === "unverified").map((b) => b.detail),
  };
}

/**
 * Write the bundle (see the module doc). The directory is rebuilt from scratch, so the same records
 * give the same tree.
 */
export async function writeBundle(a: BundleArgs): Promise<BundleResult> {
  const log = a.log ?? (() => {});
  const dir = a.outDir ?? path.join(a.runDir, BUNDLE_DIR);
  await rm(dir, { recursive: true, force: true });
  await mkdir(dir, { recursive: true });
  const paper = await writePaper(a, dir, log);
  const lean = await writeLean(a, dir, paper.names);
  if (lean) paper.todo.push(...lean.todo);
  const report: VerifyReportJson = { ...a.report, names: paper.names };
  const linksFile = path.join(a.runDir, "nl_links.json");
  let links: NlLinksResult[] | null = null;
  try {
    links = existsSync(linksFile) ? ((JSON.parse(await readFile(linksFile, "utf8")) as { results?: NlLinksResult[] }).results ?? null) : null;
  } catch {
    links = null;
  }
  await writeFile(path.join(dir, "MATCH.md"), renderMatch({ report, links, tags: lean?.tags ?? new Map(), core: a.input.core, leanDir: `lean/${lean?.rel ?? a.leanSubdir ?? ""}`, current: lean ? await currentStatements(report, path.join(dir, "lean"), path.join(dir, "lean", lean.rel)) : undefined }), "utf8");
  const blocking = paper.todo.filter((i) => GROUPS.find((g) => g.id === i.group)!.blocking).length;
  const ownSource = sourceFailureNote(paper.compile, "corrected") !== null;
  const note = paper.compile.status === "passed" ? null : `The paper ${ownSource ? "did not compile (nor does its original source on this installation)" : paper.compile.status === "failed" ? "did not compile" : `was not compiled (${paper.compile.reason})`}: references were checked against the labels the source defines, and results are named by their place in the source.`;
  const unwrapNote = paper.unwrapped.length > 0 ? `The paper was read with its authors' note macros read away (colour wrappers around edited passages dropped, hidden text and authors' comments removed); these files are written as they were read, the macros' definitions kept: ${paper.unwrapped.map((f) => `\`${f}\``).join(", ")}. Every removed comment and hidden passage is listed, whole, in the run's \`${AUTHOR_NOTES_FILE}\` — check that none of it is the paper's.` : null;
  await writeFile(path.join(dir, PAPER_DIR, "TODO.md"), renderTodo(a.slug, paper.todo, [note, unwrapNote].filter((x) => x !== null).join("\n\n") || null), "utf8");
  // The paper's page as the local UI draws it, with no path of this machine. Never fails the bundle.
  let page: string | null = null;
  try {
    if (path.resolve(a.runDir) !== path.resolve(a.toolkitRoot, "runs", a.slug)) throw new Error("the run is not in the toolkit's runs/");
    const snap = await pageSnapshot({ toolkitRoot: a.toolkitRoot, slug: a.slug, report, paperDir: PAPER_DIR, pdf: paper.compile.pdf, leanDir: lean ? `lean/${lean.rel}` : null });
    await mkdir(path.dirname(path.join(dir, PAGE_FILE)), { recursive: true });
    const text = blankPaths(JSON.stringify(snap), lean?.machine ?? machinePaths([a.toolkitRoot]));
    // The page is published: a home directory or this machine's user left in it (a path outside the
    // roots blanked above, quoted in a model's note) keeps it out of the bundle.
    const who = os.userInfo().username;
    const left = (userPathIn(text, who) ? `the user of this machine (\`${who}\`) in a path` : null) ?? /\/(?:home|Users)\/[A-Za-z0-9._-]+/.exec(text)?.[0] ?? null;
    if (left) throw new Error(`it names ${left}`);
    await writeFile(path.join(dir, PAGE_FILE), `${text}\n`, "utf8");
    page = PAGE_FILE;
    // the TikZ pictures the page draws, typeset by the local UI into the run's logs: the bundle carries
    // them where the page names them, so a reader with the bundle sees them too
    for (const f of new Set([...text.matchAll(new RegExp(`${PAPER_DIR}/_tikz/([0-9a-f]+\\.pdf)`, "gu"))].map((m) => m[1]!))) {
      const from = path.join(a.runDir, TIKZ_DIR, f);
      if (!existsSync(from)) { log(`bundle: the TikZ picture ${f} the page names is not in ${TIKZ_DIR}`); continue; }
      await mkdir(path.join(dir, PAPER_DIR, "_tikz"), { recursive: true });
      await cp(from, path.join(dir, PAPER_DIR, "_tikz", f));
    }
  } catch (err) {
    await rm(path.dirname(path.join(dir, PAGE_FILE)), { recursive: true, force: true });
    log(`bundle: page snapshot not written (${err instanceof Error ? err.message : String(err)})`);
  }
  // What the two reviewers answered at F4, as the run logged it, with no path of this machine.
  const calls = a.seal ? await readFile(path.join(a.runDir, REVIEWER_CALLS_LOG), "utf8").catch(() => "") : "";
  const reviews = f4Reviews(calls, lean?.machine ?? machinePaths([a.toolkitRoot]));
  // The seal names every file of lean/, corrected_paper/ and page/ as written, the compiled paper apart: it is not
  // the same from one compile to the next (what else a compile leaves, `writePaper` has removed).
  const sealed = new Map<string, string>();
  if (a.seal) {
    const output = (rel: string): boolean => paper.compile.pdf !== null && rel === `${PAPER_DIR}/${paper.compile.pdf}`;
    for (const rel of await walk(dir, (r, isDir) => (isDir ? !SEALED.test(`${r}/`) : !SEALED.test(r) || output(r)))) sealed.set(rel, sha256(await readFile(path.join(dir, rel))));
  }
  const beside = { reviews: reviews || null, files: sealed };
  const seal = a.seal ? withBundle(a.seal, beside) : undefined;
  const user = os.userInfo().username;
  const sealProblems = seal ? [...checkF4Seal(seal, beside), ...(user.length > 2 && reviews.includes(user) ? [`${F4_REVIEWS_FILE} names the user of the machine it was written on (\`${user}\`)`] : [])] : [];
  const bundle: ReportBundle = {
    dir: BUNDLE_DIR,
    paper: { dir: PAPER_DIR, main: a.mainFile, pdf: paper.compile.pdf, pages: paper.pages, compile: { status: paper.compile.status, tool: paper.compile.tool, reason: paper.compile.reason } },
    todo: { total: paper.todo.length, blocking },
    lean: lean ? (({ tags: _t, machine: _m, rel: _r, todo: _d, ...rest }) => rest)(lean) : null,
    page,
    ...(seal ? { f4_seal: { code: seal.code, problems: sealProblems, reviews: reviews ? F4_REVIEWS_FILE : null } } : {}),
  };
  if (seal) await writeFile(path.join(dir, F4_SEAL_FILE), `${JSON.stringify(seal, null, 2)}\n`, "utf8");
  if (seal && reviews) await writeFile(path.join(dir, F4_REVIEWS_FILE), reviews, "utf8");
  const R = [`# Corrected paper — ${a.slug}`, ""];
  R.push(
    blocking === 0 && paper.compile.status === "passed"
      ? `Ready to submit as far as the mechanical checks go${paper.todo.length > 0 ? `; ${paper.todo.length} item(s) to check are listed in \`${PAPER_DIR}/TODO.md\`` : ""}.`
      : `NOT ready to submit: ${blocking} blocking item(s)${paper.compile.status === "passed" ? "" : `, and the paper ${ownSource ? "does not compile on this installation (nor does its original source)" : paper.compile.status === "failed" ? "does not compile" : "was not compiled"}`} — see \`${PAPER_DIR}/TODO.md\`.`,
    "",
    `- \`${PAPER_DIR}/\` — the paper as it reads after the corrections: the author's own source (class, preamble, bibliography, figures, file layout), with each corrected statement, proof step and proof written in place of the printed one. Main file \`${PAPER_DIR}/${a.mainFile}\`${paper.compile.pdf ? `; compiled: \`${PAPER_DIR}/${paper.compile.pdf}\`${paper.pages ? ` (${paper.pages} pages)` : ""}` : ""}. A reading the statements rely on appears as a remark of the paper at the statement it concerns.`,
    `- \`${PAPER_DIR}/TODO.md\` — what remains before submitting, each item with its file and line.`,
    "- `REPORT.md` — what was wrong, what was done about it, and what was proved in Lean.",
    "- `MATCH.md` — each result beside its Lean declaration, phrase by phrase.",
    ...(page ? [`- \`${page}\` — the paper's page as PaperFormalizer's reader draws it (the statements as corrected, the notes, each result's verdict and its Lean), as data.`] : []),
    ...(lean ? [`- \`lean/\` — the Lean code, a standalone project to send to whoever checks it (\`lean/README.md\`: how to build it); ${lean.self_contained.ok ? "self-contained" : "NOT self-contained"}${lean.warnings.length > 0 ? `, ${lean.warnings.length} warning(s) on the base libraries it was built against` : ""}.`] : []),
    ...(bundle.f4_seal ? [`- \`${F4_SEAL_FILE}\` — the two reviewers' verdicts on each Lean statement, under the code \`${bundle.f4_seal.code}\`${bundle.f4_seal.problems.length > 0 ? ` (NOT a finished review: ${bundle.f4_seal.problems.length} problem(s), see \`bundle.json\`)` : ""}, with the hash of every file of \`lean/\`, \`${PAPER_DIR}/\` and \`page/\`${seal?.arxiv ? ` and the paper's arXiv identifier as declared (${seal.arxiv})` : ""}; \`paperformalizer seal\` checks it. The files at this directory's root (\`REPORT.md\`, \`MATCH.md\`, \`bundle.json\`, this file) are outside the seal.${bundle.f4_seal.reviews ? ` \`${F4_REVIEWS_FILE}\` — what the two reviewers answered at each review pass of the run, earlier passes included.` : ""}`] : []),
    "",
    "What is checked is the paper's results: each corrected statement and proof, and every result that depends on one. The prose around them is the authors', as printed.",
    "",
  );
  await writeFile(path.join(dir, "README.md"), R.join("\n"), "utf8");
  await writeFile(path.join(dir, "bundle.json"), `${JSON.stringify({ slug: a.slug, ...bundle, names: paper.names, todo_items: paper.todo }, null, 2)}\n`, "utf8");
  for (const r of lean?.requires ?? []) if (r.catalog_rev && r.rev) log(`bundle: built on ${r.name} at ${r.rev.slice(0, 12)}; PaperFormalizer now pins ${r.catalog_rev.slice(0, 12)} — the Lean README says how to move to it`);
  log(`bundle: ${dir} — corrected paper compile ${paper.compile.status}${paper.pages ? ` (${paper.pages} pages)` : ""}, ${paper.todo.length} TODO item(s) (${blocking} blocking)${lean ? `, ${lean.files} Lean file(s), ${lean.self_contained.ok ? "self-contained" : `NOT self-contained (${lean.self_contained.problems.length} problem(s))`}${lean.warnings.length > 0 ? `, ${lean.warnings.length} warning(s) on the base libraries` : ""}` : ""}`);
  return { dir, bundle, names: paper.names, todo: paper.todo };
}
