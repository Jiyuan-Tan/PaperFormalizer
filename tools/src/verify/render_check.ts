/**
 * The render check (user decision 2026-09-25: "rendering fallbacks are a checkpoint, never silent";
 * design 2026-09-25: the ONE place a fragment the renderer cannot set is reported).
 *
 * A block of the annotated paper that could not be set as TeX — a model-written fragment with a
 * non-ASCII character or failing its compile against the paper's preamble (`tex_fragment_check.ts`),
 * printed verbatim (`\texttt{\textbackslash…}`) and named; a proof-step fragment escaped; a character
 * printed as its code point (`[U+…]`) — or a pdflatex error is a defect: the paper's owner would read
 * raw TeX. It is never waived. Nothing is repaired. A pdflatex failure the compile guard located in
 * the paper's own TeX (`paper_side`) is the paper's and not reported; nor is an error the paper's
 * unmodified source has too (`source_failure`: the compile says so in a note).
 *
 * Two classes (user rule 2026-09-25, "fix the order and the classification"): a MODEL-TEXT defect is
 * a model-written fragment failing `checkTexFragment` — the planner records it with its `fragment`
 * (kind, text, the compiler's line and its PRODUCER: the symbol referee, the V1.5 referee, the fixer,
 * or a text no model of the run re-writes) and the verify runner routes it back to
 * that producer (`fragment_routing.ts`); a RENDERER defect is everything else (a proof-step fragment
 * escaped, escaped TeX or a code point the renderer itself printed, an odd `$`, a pdflatex error) and
 * is fixed in the renderer (`splitRenderDefects`).
 *
 * ONE implementation, two callers: `lintAnnotated` reads a run's rendered tree — the defects the
 * renderer recorded (`logs/annotated_render.json`, written by `annotate_run.ts` after each render),
 * the last compile (`logs/annotated_compile.json`), the pdflatex log's errors, and a scan of every
 * `\vs…` block in `annotated/*.tex` for escaped TeX (`\textbackslash`, `\^{}`), code points
 * (`[U+XXXX]`) and an odd number of `$` — and is what both `theoremchecker lint-annotated` and the
 * pipeline's checkpoints (after every annotated-paper render) block on. The scan skips `\texttt{…}`:
 * the renderer's only typewriter text is the verbatim print of a failing model fragment, which the
 * record already reports with its producer.
 */
import { existsSync } from "node:fs";
import { readdir, readFile } from "node:fs/promises";
import path from "node:path";
import { latexLogErrors, treeSha, type CompileResult } from "./annotated_compile.js";
import type { TexFragmentKind } from "./tex_fragment_check.js";

/** Who wrote a model fragment of the annotated paper, i.e. who is asked to write it again:
 * `symbol` the symbol referee (a reading, a table fix), `referee` the V1.5 referee (an explanation, a
 * reading, a finding's text), `fixer` the V1 fixer (a repair's texts and notes); `other` a text no model of the run
 * writes again (the owner's words, the transcription's symbol name, an F-stage reviewer's reason). */
export type FragmentProducer = "symbol" | "referee" | "fixer" | "other";

/** A model-written fragment that failed the compile check, as the planner recorded it. `ref`: what the
 * producer keys it by (the symbol's name, the clarity key of the note; else the node). */
export interface FailedFragment {
  kind: TexFragmentKind;
  text: string;
  producer: FragmentProducer;
  error: string;
  ref?: string;
}

/** One block that could not be set as TeX. `node`: the result it annotates (null when the scan of
 * the written file cannot tell); `block`: what kind of block (its label, or `file:line`); `reason`;
 * `fragment`: set on a model-text defect (a model-written fragment failing its compile check). */
export interface RenderDefect {
  node: string | null;
  block: string;
  reason: string;
  fragment?: FailedFragment;
}

/** `runs/<slug>/<this>`: the defects the last render recorded (read by `lintAnnotated`). */
export const ANNOTATED_RENDER_RECORD = "logs/annotated_render.json";
const COMPILE_RECORD = "logs/annotated_compile.json";

/** The blocking summary of a render's defects (null: nothing blocks), one line each. Pure. */
export function renderBlock(defects: readonly RenderDefect[] | null | undefined): string | null {
  if (!defects || defects.length === 0) return null;
  const lines = defects.map((d) => `    ${d.node ?? "(file)"} — ${d.block}: ${d.reason.replace(/\s+/g, " ").trim()}`);
  return `${defects.length} block(s) could not be set as TeX —\n${lines.join("\n")}`;
}

/** A render's defects in the two classes: model-text (`fragment` set; routed to the producer) and
 * renderer (everything else; the renderer is fixed). Pure. */
export function splitRenderDefects(defects: readonly RenderDefect[] | null | undefined): { renderer: RenderDefect[]; fragments: Array<RenderDefect & { fragment: FailedFragment }> } {
  const renderer: RenderDefect[] = [];
  const fragments: Array<RenderDefect & { fragment: FailedFragment }> = [];
  for (const d of defects ?? []) {
    if (d.fragment) fragments.push(d as RenderDefect & { fragment: FailedFragment });
    else renderer.push(d);
  }
  return { renderer, fragments };
}

/** The contract checkpoint's summary: the model fragments that still do not compile, by producer
 * (null: nothing). Pure. */
export function contractBlock(fragments: ReadonlyArray<RenderDefect & { fragment: FailedFragment }>): string | null {
  if (fragments.length === 0) return null;
  const by = new Map<FragmentProducer, string[]>();
  for (const d of fragments) {
    const shown = d.fragment.text.replace(/\s+/g, " ").trim();
    (by.get(d.fragment.producer) ?? by.set(d.fragment.producer, []).get(d.fragment.producer)!).push(
      `    ${d.node ?? "(file)"} — ${d.block}: ${d.fragment.error.replace(/\s+/g, " ").trim()} — the fragment: ${shown.length > 120 ? `${shown.slice(0, 119)}…` : shown}`,
    );
  }
  const parts = [...by].map(([p, ls]) => `  ${PRODUCER_LABEL[p]} (${ls.length}):\n${ls.join("\n")}`);
  return `${fragments.length} model-written fragment(s) still do not compile against the paper's preamble —\n${parts.join("\n")}`;
}

/** How a producer is named to the orchestrator. */
export const PRODUCER_LABEL: Record<FragmentProducer, string> = {
  symbol: "the symbol referee",
  referee: "the V1.5 referee",
  fixer: "the fixer",
  other: "no model of the run re-writes these (the owner's words, the transcription, an F-stage reviewer)",
};

/** `\vsCorrectedStep` → "Corrected step". */
const macroLabel = (name: string): string => name.replace(/^vs/, "").replace(/([a-z])([A-Z])/g, "$1 $2").replace(/^./, (c) => c.toUpperCase()).replace(/ ([A-Z])/g, (_m, c: string) => ` ${c.toLowerCase()}`);

/** The brace-balanced argument starting at `text[at] === "{"`: its end (exclusive), or -1. */
function groupEnd(text: string, at: number): number {
  let depth = 0;
  for (let i = at; i < text.length; i += 1) {
    const c = text[i]!;
    if (c === "\\") {
      i += 1;
      continue;
    }
    if (c === "%") {
      const nl = text.indexOf("\n", i);
      if (nl < 0) return -1;
      i = nl;
      continue;
    }
    if (c === "{") depth += 1;
    else if (c === "}") {
      depth -= 1;
      if (depth === 0) return i + 1;
    }
  }
  return -1;
}

/** Unescaped `$` in a TeX text (a `$$` counts twice); a `%` comment, to its line end, is not text. */
function dollars(tex: string): number {
  let n = 0;
  for (let i = 0; i < tex.length; i += 1) {
    if (tex[i] === "\\") i += 1;
    else if (tex[i] === "%") { const nl = tex.indexOf("\n", i); i = nl < 0 ? tex.length : nl; }
    else if (tex[i] === "$") n += 1;
  }
  return n;
}

const ESCAPED = [
  { re: /\\textbackslash\b/u, what: "escaped TeX (\\textbackslash)" },
  { re: /\\\^\{\}/u, what: "escaped TeX (\\^{})" },
  { re: /\[U\+[0-9A-F]{4,6}\]/u, what: "a character printed as its code point" },
];

/** `text` with every `\texttt{…}` group blanked: the renderer's verbatim print of a model fragment
 * that failed its check (`verbatimLike`), reported from the render record. */
function withoutVerbatim(text: string): string {
  let out = "";
  let i = 0;
  for (let at = text.indexOf("\\texttt{", i); at >= 0; at = text.indexOf("\\texttt{", i)) {
    const end = groupEnd(text, at + "\\texttt".length);
    if (end < 0) break;
    out += `${text.slice(i, at)}\\texttt{}`;
    i = end;
  }
  return out + text.slice(i);
}

/** The defects in one annotated `.tex` file: every top-level `\vs…{…}` block scanned. Pure. */
export function lintAnnotatedTex(file: string, text: string): RenderDefect[] {
  const out: RenderDefect[] = [];
  const lineOf = (i: number): number => text.slice(0, i).split("\n").length;
  const re = /\\(vs[A-Z][A-Za-z]*)\s*(?=\{)/g;
  for (let m = re.exec(text); m; m = re.exec(text)) {
    let at = m.index + m[0].length;
    const args: string[] = [];
    while (text[at] === "{") {
      const end = groupEnd(text, at);
      if (end < 0) break;
      args.push(text.slice(at + 1, end - 1));
      at = end;
    }
    if (args.length === 0 || args.some((a) => a.includes("#1"))) continue; // a macro definition
    // A failing model fragment printed verbatim is reported from the render record, with its producer.
    const body = withoutVerbatim(args.join("\n"));
    const where = `${macroLabel(m[1]!)} at ${file}:${lineOf(m.index)}`;
    for (const e of ESCAPED) {
      const hit = e.re.exec(body);
      if (hit) out.push({ node: null, block: where, reason: `${e.what}: …${body.slice(Math.max(0, hit.index - 40), hit.index + 40).replace(/\s+/g, " ")}…` });
    }
    for (const a of args.map(withoutVerbatim)) if (dollars(a) % 2 === 1) out.push({ node: null, block: where, reason: `an odd number of $ in the block: …${a.slice(0, 80).replace(/\s+/g, " ")}…` });
    re.lastIndex = at; // nested \vs macros are inside this block's scan
  }
  return out;
}

async function texFiles(dir: string, rel = ""): Promise<string[]> {
  const out: string[] = [];
  for (const e of await readdir(path.join(dir, rel), { withFileTypes: true })) {
    const r = rel ? `${rel}/${e.name}` : e.name;
    if (e.isDirectory()) out.push(...(await texFiles(dir, r)));
    else if (e.isFile() && /\.tex$/i.test(e.name)) out.push(r);
  }
  return out.sort();
}

/**
 * Everything in the run's rendered annotated paper that could not be set as TeX (see the module
 * doc). An absent `annotated/` is itself reported (nothing was rendered to check). `compileRecord`: the
 * compile guard's record when kept elsewhere (`annotate --compile-record`).
 */
export async function lintAnnotated(runDir: string, opts: { compileRecord?: string } = {}): Promise<RenderDefect[]> {
  const dir = path.join(runDir, "annotated");
  if (!existsSync(dir)) return [{ node: null, block: "annotated paper", reason: "annotated/ does not exist — nothing was rendered" }];
  const out: RenderDefect[] = [];
  const rec = path.join(runDir, ANNOTATED_RENDER_RECORD);
  if (existsSync(rec)) {
    try {
      out.push(...((JSON.parse(await readFile(rec, "utf8")) as { defects?: RenderDefect[] }).defects ?? []));
    } catch {
      out.push({ node: null, block: ANNOTATED_RENDER_RECORD, reason: "unreadable" });
    }
  }
  for (const f of await texFiles(dir)) out.push(...lintAnnotatedTex(f, await readFile(path.join(dir, f), "utf8")));
  // pdflatex's exit status decides: a passed compile's log can still hold a line starting with "! " (an
  // overfull-box dump wrapped onto a new line), so the log is scanned only when the compile did not pass.
  const compileRec = opts.compileRecord ?? path.join(runDir, COMPILE_RECORD);
  let compile: { status?: string; reason?: string; log_tail?: string; paper_side?: boolean; tree_sha256?: string; source_failure?: CompileResult["source_failure"] } | null = null;
  if (existsSync(compileRec)) {
    try {
      compile = JSON.parse(await readFile(compileRec, "utf8")) as { status?: string; reason?: string };
    } catch {
      // an unreadable record adds nothing: the log scan stands
    }
  }
  // a "passed" record stands for this tree only when its log tail is a current log's tail
  const logs = new Map<string, string>();
  for (const f of (await readdir(dir)).filter((n) => /\.log$/i.test(n)).sort()) logs.set(f, await readFile(path.join(dir, f), "latin1"));
  const tail = (log: string): string => log.split("\n").slice(-40).join("\n");
  if (compile?.status === "passed" && [...logs.values()].some((l) => tail(l) === compile.log_tail)) return out;
  // A failure the compile guard located entirely in the paper's own TeX (`paperSideFailure`: every
  // located error away from anything the annotation inserted — e.g. a copied .bbl in a legacy
  // encoding) is the paper's, not the renderer's: the unannotated source fails the same way.
  // The record stands for this tree when its log is the current log, or — the guard skipped the
  // compile, so no log was written — when the rendered tree is the one it compiled.
  if (
    compile?.status === "failed" &&
    compile.paper_side === true &&
    ([...logs.values()].some((l) => tail(l) === compile.log_tail) ||
      (logs.size === 0 && compile.tree_sha256 === (await treeSha(dir, { renderedOnly: true }))))
  )
    return out;
  // The errors the unmodified source has too are the paper's; the others stay the renderer's.
  const sources = new Set([...logs.values()].some((l) => tail(l) === compile?.log_tail) ? (compile?.source_failure?.lines ?? []) : []);
  let logErrors = 0;
  for (const [f, log] of logs) {
    for (const line of latexLogErrors(log).filter((l) => !sources.has(l))) {
      logErrors += 1;
      out.push({ node: null, block: `pdflatex (${f})`, reason: line });
    }
  }
  if (compile?.status === "failed" && logErrors === 0) out.push({ node: null, block: "pdflatex", reason: `the compile failed: ${compile.reason || "no reason recorded"}` });
  return out;
}
