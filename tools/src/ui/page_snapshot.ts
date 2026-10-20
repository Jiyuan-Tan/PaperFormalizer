// A run's paper as its page draws it (the server's `paper` view), and the page of a finished run as
// one file: the bundle's `page/page.json` (`verify/bundle.ts`), for a reader that has the bundle and
// not the run. The snapshot is what the server answers for the page (`runDetail`, the paper, the
// rendered TeX) less what only a run at work has; it is model-free and the same for the same records.
import { existsSync, readdirSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import type { ToolkitConfig } from "../toolkit/config.js";
import { splitKinds } from "../verify/core_graph.js";
import { unwrapSource, type NoteMacroTable } from "../verify/note_macros.js";
import { readJsonCached } from "./fscache.js";
import { coreWhere, ownerReadingsByComment, runDetail, type CoreFile, type OwnerReadingEntry, type ResultView, type RunDetail, type RunReport, type TokenTotals } from "./run_model.js";
import { paperRenderer, tikzPictures, tikzSetup, type MathFailure, type RenderedPaper } from "./tex_html.js";
import { TIKZ_DIR, tikzFailure, tikzPdf } from "./tikz.js";

/** The agent's replacements for formulas neither renderer reads (source → TeX), per run. */
export const MATH_OVERRIDES_FILE = "ui_math_overrides.json";
/** Files a paper page may load from the paper's directory (figures, the typeset PDF). */
export const ASSET_EXT = new Set([".png", ".jpg", ".jpeg", ".gif", ".svg", ".webp", ".pdf", ".eps", ".ps"]);
/** Keys of a run's detail whose strings are TeX the page shows (rendered under the paper's macros). */
const TEX_KEYS = new Set(["detail", "reason", "given_up", "witness", "reading", "condition", "text", "guidance", "why"]);

/** The TeX strings of a run's detail (`TEX_KEYS`), each once, in the order met. Pure. */
export function texStrings(detail: unknown): string[] {
  const out = new Set<string>();
  const walk = (v: unknown, key: string) => {
    if (typeof v === "string") { if (TEX_KEYS.has(key) && v) out.add(v); }
    else if (Array.isArray(v)) for (const x of v) walk(x, key);
    else if (v && typeof v === "object") for (const [k, x] of Object.entries(v)) walk(x, k);
  };
  walk(detail, "");
  return [...out];
}

/** The paper as the page draws it. `from`: the directory of the run it is read from; `pdf`: its
 *  typeset PDF under `assetBase`, when there is one. */
/** What the page could not draw of the paper, formulas apart (`ui_math_failures.json`): commands and
 *  environments it does not know (their text is shown, their meaning lost), figure files not found,
 *  drawings left out, and why the paper's TikZ pictures were not typeset. Each list empty when none. */
export interface RenderProblems { unknownCommands: Record<string, number>; unknownEnvironments: Record<string, number>; missingFigures: string[]; omittedDrawings: number; tikz: string | null; unresolvedRefs: string[]; unnamedResults: string[] }
export type PaperView = RenderedPaper & { ownerReadings: Record<string, OwnerReadingEntry[]>; anchorHeadings: Record<string, string>; from: "annotated" | "source"; pdf: string | null; renderProblems: RenderProblems };
export type Fragment = (tex: string) => { html: string; failures: MathFailure[] };

/**
 * The paper of the run at `dir` (its annotated copy, else its source): the files it is drawn from
 * (`inputs`, under `base`) and `render`, which draws it with its figures addressed under
 * `assetBase` and gives the renderer of the run's other TeX. Null when the run has no paper.
 */
export async function runPaper(dir: string, assetBase: string): Promise<{ base: string; inputs: string[]; render: () => Promise<{ view: PaperView; fragment: Fragment }> } | null> {
  const annotated = path.join(dir, "annotated");
  const useAnnotated = existsSync(annotated) && readdirSync(annotated).some((f) => f.endsWith(".tex"));
  const base = useAnnotated ? annotated : path.join(dir, "source");
  const state = await readJsonCached<{ verify?: { source?: { main_file?: string } } }>(path.join(dir, "state.json"));
  const envs = await readJsonCached<{ main_file?: string; newtheorem?: Record<string, string>; note_macros?: NoteMacroTable }>(path.join(dir, "discovery", "envs.json"));
  const main = state?.verify?.source?.main_file ?? envs?.main_file ?? (existsSync(base) ? readdirSync(base).find((f) => f.endsWith(".tex")) : undefined);
  if (!main || !existsSync(path.join(base, main))) return null;
  const files = listTex(base);
  const aux = path.join(base, main.replace(/\.tex$/, ".aux"));
  const bbl = path.join(base, main.replace(/\.tex$/, ".bbl"));
  const pdf = path.join(base, main.replace(/\.tex$/, ".pdf"));
  const coreFiles = ["core.json", "core.transcribed.json"].map((f) => path.join(dir, "discovery", f));
  const overridesFile = path.join(dir, MATH_OVERRIDES_FILE);
  const patchesFile = path.join(dir, "discovery", "patches.json");
  const render = async () => {
    const texts: Record<string, string> = {};
    // the paper as the run read it: its authors' note macros read away (`note_macros.ts`)
    const asRead = (tex: string): string => unwrapSource(tex, envs?.note_macros, "remove");
    for (const f of files) texts[f] = asRead(await readFile(path.join(base, f), "utf8"));
    // results with no environment of their own (stated in prose): anchor them at their first line,
    // named as that line names them ("\textbf{Theorem 1.}" → Theorem 1); a result an environment
    // holds is anchored too, and the page prefers the environment
    const source = path.join(dir, "source");
    // (each source file read and its note macros read away once per render, not once per statement it holds)
    const sourceTexts = new Map<string, Promise<string | null>>();
    const sourceText = (file: string): Promise<string | null> => {
      let t = sourceTexts.get(file);
      if (!t) {
        const src = path.join(source, file);
        t = existsSync(src) ? readFile(src, "utf8").then((x) => asRead(x.replace(/\r\n?/g, "\n"))) : Promise.resolve(null);
        sourceTexts.set(file, t);
      }
      return t;
    };
    const sourceLines = new Map<string, string[]>();
    const anchors: Array<{ node: string; file: string; line: string; at?: number; after?: true; nth?: [number, number] }> = [];
    const anchorHeadings: Record<string, string> = {};
    for (const cf of coreFiles) {
      const core = await readJsonCached<{ statements?: Array<{ id: string; cited_in?: string | null; tex_locator?: { file?: string; from?: number; env?: string; label?: string | null } }> }>(cf);
      for (const st of core?.statements ?? []) {
        const loc = st.tex_locator;
        if (!loc?.file || !loc.from || anchors.some((a) => a.node === st.id)) continue;
        const src = (await sourceText(loc.file)) ?? "";
        if (!sourceLines.has(loc.file)) sourceLines.set(loc.file, src.split("\n"));
        const lines = sourceLines.get(loc.file)!;
        const line = lines[loc.from - 1] ?? "";
        if (line.trim().length < 8) continue;
        // which occurrence of that line it is in the source (k of n): the rendered copy may have shifted its lines
        const needle = line.trim(), lineStart = lines.slice(0, loc.from - 1).join("\n").length + (loc.from > 1 ? 1 : 0);
        const hits: number[] = [];
        for (let i = src.indexOf(needle); i >= 0; i = src.indexOf(needle, i + 1)) hits.push(i);
        const k = hits.findIndex((i) => i >= lineStart);
        // a citation invoked inside a proof is located at that proof: its label stands after the proof's
        // opening, inside it — before it, the proof would read as the cited result's own
        anchors.push({ node: st.id, file: loc.file, line, at: loc.from, ...(k >= 0 ? { nth: [k, hits.length] as [number, number] } : {}), ...(st.cited_in ? { after: true as const } : {}) });
        const named = /\b(Theorem|Lemma|Proposition|Corollary|Definition|Assumption|Result|Claim|Condition|Property|Criterion)\s+([A-Z]?\d+(?:\.\d+)*[a-z]?)/.exec(line);
        if (named) anchorHeadings[st.id] = `${named[1]} ${named[2]}`;
      }
    }
    // an assumption or definition no labelled environment holds: anchored where its own text
    // begins, when the source first has that text inside the passage the core locates it in
    const coreFile = await readJsonCached<CoreFile>(coreFiles[0]!);
    const where = coreWhere(coreFile);
    for (const p of where.passages) {
      const src = await sourceText(p.file);
      const at = src ? src.indexOf(p.text) : -1;
      const ln = at < 0 ? 0 : src!.slice(0, at).split("\n").length;
      if (ln >= p.from && ln <= p.to) anchors.push({ node: p.node, file: p.file, line: p.text });
    }
    const mathOverrides = await readJsonCached<Record<string, string>>(overridesFile);
    const pictures = tikzPictures(texts, main);
    const setup = tikzSetup(texts, main);
    const tikzFile = tikzPdf(dir, base, texts[main] ?? "", pictures, setup);
    const { paper: r, fragment } = paperRenderer({
      files: texts, main, aux: existsSync(aux) ? await readFile(aux, "utf8") : null, bbl: existsSync(bbl) ? await readFile(bbl, "utf8") : null,
      theoremKinds: envs?.newtheorem ?? null, assets: listAssets(base), assetBase, tikz: tikzFile ? { url: `${assetBase}/_tikz/${tikzFile}`, pictures } : null, anchors, readings: where.readings, mathOverrides,
      splitKinds: Object.fromEntries(splitKinds({ statements: coreFile?.statements ?? [] })),
    });
    // the readings entered for the owner, each under the note that states it (the page edits them)
    const ownerReadings = ownerReadingsByComment(r.readings, r.comments, (await readJsonCached<{ owner_readings?: Parameters<typeof ownerReadingsByComment>[2] }>(patchesFile))?.owner_readings);
    // a result anchored just before an environment the paper leaves unlabelled (`\begin{corollary}` with
    // no \label) takes that environment's heading, "Corollary 3", as the page numbers it
    const labelled = new Set(r.envs.map((e) => e.label).filter(Boolean));
    const ownLabel = new Map((coreFile?.statements ?? []).map((st) => [st.id, st] as const));
    for (const [node, aid] of Object.entries(r.anchors)) {
      const st = ownLabel.get(node);
      // a result its own environment's label names, or a citation (named by its citation), takes no other heading
      if (anchorHeadings[node] || st?.cited_in || (st?.tex_locator?.label && labelled.has(st.tex_locator.label))) continue;
      const at = r.html.indexOf(`id="${aid}"`);
      const next = at < 0 ? null : /^[^>]*><\/span>(?:\s|<span class="res-anchor"[^>]*><\/span>|<\/div>|<div class="p">)*<div class="formal[^"]*" id="([^"]*)"/.exec(r.html.slice(at));
      const env = next ? r.envs.find((e) => e.anchor === next[1]) : undefined;
      if (env && !env.label) anchorHeadings[node] = env.heading;
    }
    for (const st of coreFile?.statements ?? []) {
      if (r.anchors[st.id] && !anchorHeadings[st.id] && !st.cited_in && !(st.tex_locator?.label && labelled.has(st.tex_locator.label)) && st.source?.cite) {
        anchorHeadings[st.id] = `[${st.source.cite}${st.source.locator ? `, ${st.source.locator}` : ""}]`;
      }
    }
    // a result the page names by no environment (drawn by its kind on the proof map, "Thm ?" or "Thm (theorem 4)"):
    // its anchor found no environment of its own — often one placed at the wrong line
    const unnamedResults = (coreFile?.statements ?? [])
      .filter((st) => !st.cited_in && !st.split_from && !(st.tex_locator?.label && labelled.has(st.tex_locator.label)) && !anchorHeadings[st.id])
      .map((st) => st.id);
    const h = r.health;
    const unknown = Object.entries(h.unknownCommands);
    const renderProblems: RenderProblems = {
      unknownCommands: Object.fromEntries(unknown.filter(([k]) => !k.startsWith("env:"))),
      unknownEnvironments: Object.fromEntries(unknown.filter(([k]) => k.startsWith("env:")).map(([k, n]) => [k.slice(4), n])),
      missingFigures: h.missingFigures, omittedDrawings: h.omitted,
      tikz: tikzFile ? null : tikzFailure(dir, base, texts[main] ?? "", pictures, setup), unresolvedRefs: h.unresolvedRefs, unnamedResults,
    };
    const view: PaperView = { ...r, ownerReadings, anchorHeadings, from: useAnnotated ? "annotated" : "source", pdf: existsSync(pdf) ? `${assetBase}/${main.replace(/\.tex$/, ".pdf").split("/").map(encodeURIComponent).join("/")}` : null, renderProblems };
    return { view, fragment };
  };
  return { base, inputs: [...files.map((f) => path.join(base, f)), aux, bbl, pdf, path.join(dir, "discovery", "envs.json"), ...coreFiles, overridesFile, patchesFile, path.join(dir, TIKZ_DIR)], render };
}

/** Figure and PDF files under `dir` (relative, `/`-separated; three levels deep). */
function listAssets(dir: string): string[] {
  const out: string[] = [];
  const walk = (d: string, rel: string, depth: number) => {
    for (const e of readdirSync(d, { withFileTypes: true })) {
      const r = rel ? `${rel}/${e.name}` : e.name;
      if (e.isDirectory()) { if (!e.name.startsWith(".") && depth < 3) walk(path.join(d, e.name), r, depth + 1); }
      else if (ASSET_EXT.has(path.extname(e.name).toLowerCase())) out.push(r);
    }
  };
  if (existsSync(dir)) walk(dir, "", 0);
  return out.sort();
}

function listTex(dir: string): string[] {
  const out: string[] = [];
  const walk = (d: string, rel: string) => {
    for (const e of readdirSync(d, { withFileTypes: true })) {
      const r = rel ? `${rel}/${e.name}` : e.name;
      if (e.isDirectory()) { if (!e.name.startsWith(".") && rel.split("/").length < 3) walk(path.join(d, e.name), r); }
      else if (e.name.endsWith(".tex")) out.push(r);
    }
  };
  if (existsSync(dir)) walk(dir, "");
  return out.sort();
}

export const PAGE_SCHEMA = 1;
/** The snapshot's place in a bundle. */
export const PAGE_FILE = "page/page.json";

/**
 * The page of a finished run, read-only (`page/page.json` of its bundle). Nothing of a run at work
 * is in it: no stage, halt, pending decision, recommendation, promotion round, owner report, agent
 * session or token count, and no path of the machine (`RunDetail.source.input`).
 */
export interface PageSnapshot {
  schema: typeof PAGE_SCHEMA;
  slug: string;
  title: string;
  authors: string;
  /** The report's verdict and its count of results per bucket (`RunSummary`). */
  verdict: string | null;
  buckets: Record<string, number> | null;
  /** The model calls and tokens the run's ledger counted (token_usage.jsonl), when it has one. */
  tokens: TokenTotals | null;
  /** The paper's main TeX file. */
  main: string | null;
  /** The paper's Lean in the bundle, which each result's `lean.file` is under; null without Lean. */
  leanDir: string | null;
  /** Each result with all its drawer shows (`RunDetail.results`). */
  results: Array<Omit<ResultView, "needs">>;
  leanDefs: RunDetail["leanDefs"];
  places: RunDetail["places"];
  /** The paper as drawn (`PaperView`). Its figures and `pdf` are paths from the bundle, into the
   *  corrected paper; `pages` is empty — the page numbers on file are the annotated PDF's. */
  paper: Omit<PaperView, "from" | "health"> | null;
  /** The TeX strings of `results` rendered under the paper's macros: string → HTML. */
  texHtml: Record<string, string>;
}

/**
 * The snapshot of run `slug` of the toolkit at `toolkitRoot`, under `report` (V6's, which it holds
 * before it is on file). `paperDir`: the corrected paper's folder in the bundle, where the figures
 * are; `pdf`: its compiled PDF there, when it compiled; `leanDir`: the paper's Lean in the bundle.
 */
export async function pageSnapshot(a: { toolkitRoot: string; slug: string; report: RunReport & { verdict?: string; summary?: Record<string, number> }; paperDir: string; pdf: string | null; leanDir: string | null }): Promise<PageSnapshot> {
  const cfg = { toolkitRoot: a.toolkitRoot } as ToolkitConfig;
  const d = await runDetail(cfg, a.slug, { lean: true, report: a.report });
  // (a finding's text opens with the stage that raised it: the run's own bookkeeping, not the page's)
  const results = d.results.map(({ needs: _n, ...r }) => (r.paperError ? { ...r, paperError: { ...r.paperError, detail: r.paperError.detail.replace(/^\[F[\d.]+ reviewer\]\s*/, "") } } : r));
  const drawn = await (await runPaper(path.join(a.toolkitRoot, "runs", a.slug), a.paperDir))?.render();
  const texHtml: Record<string, string> = {};
  if (drawn) for (const t of texStrings(results)) texHtml[t] = drawn.fragment(t).html;
  // Left out of the page: where it was drawn from, the render diagnostics, and the annotation macros
  // (`\vs…`: the annotated paper's own, already expanded in the HTML).
  const paper = drawn
    ? (({ from: _f, health: _h, macros, ...v }) => ({ ...v, macros: Object.fromEntries(Object.entries(macros ?? {}).filter(([k]) => !k.startsWith("\\vs"))), pages: {}, pdf: a.pdf ? `${a.paperDir}/${a.pdf}` : null }))(drawn.view)
    : null;
  return {
    schema: PAGE_SCHEMA, slug: a.slug, title: d.summary.title, authors: d.summary.authors,
    verdict: a.report.verdict ?? null,
    buckets: a.report.summary ? Object.fromEntries(Object.entries(a.report.summary).filter(([, v]) => typeof v === "number" && v > 0)) : null,
    tokens: d.summary.tokens,
    main: d.source.main, leanDir: a.leanDir, results, leanDefs: d.leanDefs, places: d.places, paper, texHtml,
  };
}
