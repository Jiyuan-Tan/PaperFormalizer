/**
 * The annotated paper for the run's CURRENT state (user rule: the owner reviews the annotated paper,
 * never a JSON receipt or a digest).
 *
 * Written, with the same machinery as V6 (`annotated_paper.ts`), at the end of every V1.5 pass
 * (accepted, a revise or patch hand-off, a refutation) and at every halt that asks the owner to
 * decide: a weakened repair (`state.verify.weakening_repair` pending), a proposed F-stage rewind
 * (`state.verify.cross_stage_rewind` pending and presented), a patch cap (`state.verify.cap_reached`).
 * The pending items are rendered at their passages under "… (awaiting your decision)" labels; what
 * the run has confirmed renders exactly as at V6. The tree is rebuilt from scratch each time, so a
 * re-run of the same halt gives the same tree, and V6 — which passes nothing pending — leaves no
 * stale "awaiting" block. Never throws: a failure is logged and named in place of the paper.
 */
import { existsSync } from "node:fs";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { parseTypedCore } from "../core/core_io.js";
import type { Core } from "../core/schema.js";
import type { StateJson } from "../types.js";
import {
  ANNOTATED_DIR,
  ANNOTATIONS_MD,
  sourceFailureNote,
  writeAnnotatedPaper,
  type AnnotatedPaperResult,
  type AnnotationInput,
  type CompileTex,
  type LoosePatchFile,
  type PendingDecisions,
} from "./annotated_paper.js";
import { RefCoreSchema, type RefCore } from "./ref_core.js";
import { ANNOTATED_RENDER_RECORD, lintAnnotated, renderBlock, splitRenderDefects, type RenderDefect } from "./render_check.js";
import { readPatchFile } from "./patches.js";
import { MAX_SUGGESTION_REJECTIONS, VERIFY_FILES, type EnvsJson, type V15Review, type VerifyState } from "./types.js";
import { PROPOSED_UNCHANGED } from "./weakening.js";

/** `discovery/core_refs.json`, as V1 writes it. */
export const CORE_REFS_FILE = "discovery/core_refs.json";

/** The run records the annotation reads besides the cores: reference core, patches, flat text. */
export async function readAnnotationRecords(
  runDir: string,
  log: (msg: string) => void,
): Promise<{ refs: RefCore | null; patches: LoosePatchFile | null; flatText: string; lineMap: Array<{ file: string; line: number }> }> {
  const read = async (rel: string): Promise<string | null> => {
    const p = path.join(runDir, rel);
    return existsSync(p) ? readFile(p, "utf8") : null;
  };
  const refsText = await read(CORE_REFS_FILE);
  let refs: RefCore | null = null;
  if (refsText !== null) {
    const parsed = RefCoreSchema.safeParse(JSON.parse(refsText));
    if (parsed.success) refs = parsed.data;
    else log(`annotated paper: ${CORE_REFS_FILE} does not parse; locating by the core's text instead`);
  }
  const lineMapText = await read(VERIFY_FILES.flatLineMap);
  // Every repair's texts as its ops derive under the current rules (`readPatchFile`).
  const patches = (await readPatchFile(runDir)) as LoosePatchFile | null;
  return {
    refs,
    patches,
    flatText: (await read(VERIFY_FILES.flatTex)) ?? "",
    lineMap: lineMapText ? ((JSON.parse(lineMapText) as { lineMap: Array<{ file: string; line: number }> }).lineMap ?? []) : [],
  };
}

/** The records the annotation reads: the run's (`readAnnotationRecords`), the V1.5 review as written. */
export type AnnotationRecords = Awaited<ReturnType<typeof readAnnotationRecords>>;

/**
 * The annotation's input from the run's records — the ONE builder of it, shared by the halts
 * (`annotateRun`) and V6 (`stage_v6_report.ts`), so the two never disagree on what is shown: a
 * symbol reading only while its verdict is confirmed (`verify.confirmed_symbols`; a dropped
 * confirmation — a demoted repair it was read against, a text breaking the contract — is graded
 * afresh first), and the suggestions the referee rejected, whose review verdict may be about the
 * suggestion rather than the paper. Pure.
 */
export function annotationInput(a: {
  envs: EnvsJson;
  verify: VerifyState;
  core: Core;
  transcribed: Core | null;
  /** `v1_5_review.json` as written (null: none). */
  review: V15Review | null;
  records: AnnotationRecords;
}): Omit<AnnotationInput, "files" | "pending" | "correctedView" | "texVerdicts"> {
  const confirmed = a.verify.confirmed_symbols;
  return {
    envs: a.envs,
    flatText: a.records.flatText,
    lineMap: a.records.lineMap,
    refs: a.records.refs,
    transcribed: a.transcribed ?? a.core,
    core: a.core,
    patches: a.records.patches,
    paperErrors: a.verify.paper_errors ?? {},
    suggestionRejected: new Set(Object.keys(a.verify.suggestion_rejections ?? {})),
    findings: a.verify.findings,
    review: a.review && confirmed ? { ...a.review, symbols: (a.review.symbols ?? []).filter((v) => v.name in confirmed) } : a.review,
  };
}

/** What `state.verify` holds pending for the owner, in the shape the planner renders; null when nothing. */
export function pendingDecisions(verify: VerifyState, patches: LoosePatchFile | null): PendingDecisions | null {
  const weakening: PendingDecisions["weakening"] =
    verify.weakening_repair?.status === "pending"
      ? verify.weakening_repair.items.map((i) => {
          const entry = patches?.unfixable?.find((u) => u.node === i.node && u.suggested_repair);
          const sr = entry?.suggested_repair ?? null;
          return {
            node: i.node,
            corrected_statement: sr ? sr.corrected_statement : i.proposed === PROPOSED_UNCHANGED ? null : i.proposed,
            given_up: i.given_up,
            ...(i.given_up_by ? { given_up_by: i.given_up_by } : {}),
            detail: i.detail,
            witness: i.witness,
            owner_explanation: i.owner_explanation ?? entry?.owner_explanation ?? null,
            ...(sr?.ops?.length ? { ops: sr.ops } : {}),
            ...(sr?.corollaries?.length ? { corollaries: sr.corollaries } : {}),
            ...(i.guidance ? { guidance: i.guidance } : {}),
          };
        })
      : [];
  const rec = verify.cross_stage_rewind;
  let rewind: PendingDecisions["rewind"] = null;
  if (rec?.status === "pending" && rec.presented) {
    // A batch keeps its resolved targets; a one-finding receipt names its statements in `nodes`.
    const routed = (rec.targets ?? []).filter((t) => t.status === "routed" && t.node);
    const targets = routed.length > 0
      ? routed.map((t) => ({ node: t.node!, axis: t.axis, ...(t.kind ? { kind: t.kind } : {}), reason: t.reason }))
      : (rec.nodes ?? []).map((node) => ({ node, axis: rec.axis ?? "correctness", ...(rec.kind ? { kind: rec.kind } : {}), reason: rec.detail }));
    if (targets.length > 0) rewind = { stage: rec.stage, targets };
  }
  const c = verify.cap_reached ?? null;
  // A suggestion limit alone: its note sits on the suggestion nodes, counting their rejections.
  const onlySug = c?.suggestions_only ? new Set(c.suggestions ?? []) : null;
  const cap: PendingDecisions["cap"] = c
    ? {
        counter: c.counter,
        rounds: onlySug ? MAX_SUGGESTION_REJECTIONS + 1 : c.rounds,
        cap: c.cap,
        origin: c.origin,
        findings: onlySug ? c.findings.filter((f) => onlySug.has(f.id)) : c.findings,
        summary:
          `the round would carry ${c.findings.length} finding(s) (${c.findings.map((f) => f.id).join(", ") || "none"}); ` +
          (c.proposed.length
            ? `the fixer's patch file proposes ${c.proposed.map((p) => `${p.node}${p.corrected_statement ? " (statement corrected)" : ""}`).join("; ")}`
            : "the fixer's patch file proposes no patch yet"),
      }
    : null;
  const confirming = weakening.length > 0 && verify.weakening_repair?.unconfirmed === true;
  return weakening.length > 0 || rewind || cap ? { weakening, ...(confirming ? { confirming } : {}), rewind, cap } : null;
}

export interface AnnotatedOutcome {
  /** Absolute path of the PDF, or of the annotated main TeX when there is no PDF; null when not written. */
  path: string | null;
  /** One line naming it (logs, halt messages). */
  line: string;
  result: AnnotatedPaperResult | null;
  error: string | null;
  /** The render check (`render_check.ts` `lintAnnotated`) of the paper just written: every block that
   * could not be set as TeX and every pdflatex error. Non-empty blocks the run (`renderBlock`). Absent:
   * nothing was written. */
  render?: RenderDefect[];
}

export type AnnotateRun = (args: {
  runDir: string;
  qid: string;
  state: StateJson;
  /** What the tree is written for, for the log: `V1.5` (end of a pass) or `halt`. */
  when: string;
  compile?: CompileTex;
  /** The compile record's path (default under the run's `logs/`). */
  compileRecord?: string;
  log: (msg: string) => void;
}) => Promise<AnnotatedOutcome>;

/** Write `annotated/` for the run as it stands (see the module doc). */
export const annotateRun: AnnotateRun = async ({ runDir, qid, state, when, compile, compileRecord, log }) => {
  try {
    const verify = state.verify!;
    const envsFile = path.join(runDir, VERIFY_FILES.envsJson);
    const coreFile = path.join(runDir, VERIFY_FILES.coreJson);
    if (!existsSync(envsFile)) throw new Error(`${VERIFY_FILES.envsJson} is missing`);
    const envs = JSON.parse(await readFile(envsFile, "utf8")) as EnvsJson;
    const transcribedFile = path.join(runDir, VERIFY_FILES.coreTranscribed);
    const transcribed = existsSync(transcribedFile)
      ? parseTypedCore(await readFile(transcribedFile, "utf8"), `verify core ${transcribedFile}`)
      : null;
    const core = existsSync(coreFile) ? parseTypedCore(await readFile(coreFile, "utf8"), `verify core ${coreFile}`) : transcribed;
    if (!core) throw new Error(`${VERIFY_FILES.coreJson} is missing`);
    const reviewFile = path.join(runDir, VERIFY_FILES.v15Review);
    const review = existsSync(reviewFile) ? (JSON.parse(await readFile(reviewFile, "utf8")) as V15Review) : null;
    const rec = await readAnnotationRecords(runDir, log);
    const main = verify.source.main_file || envs.main_file;
    const input = { ...annotationInput({ envs, verify, core, transcribed, review, records: rec }), pending: pendingDecisions(verify, rec.patches) };
    const r = await writeAnnotatedPaper({ runDir, slug: qid, mainFile: main, input, compile, ...(compileRecord ? { compileRecord } : {}), log });
    // The render check: every block that could not be set as TeX, and every pdflatex error.
    await mkdir(path.join(runDir, "logs"), { recursive: true });
    await writeFile(path.join(runDir, ANNOTATED_RENDER_RECORD), `${JSON.stringify({ at: new Date().toISOString(), when, defects: r.defects }, null, 2)}\n`, "utf8");
    const render = await lintAnnotated(runDir, compileRecord ? { compileRecord } : {});
    const dir = path.join(runDir, ANNOTATED_DIR);
    const pdf = r.compile.pdf && (r.compile.status === "passed" || r.compile.status === "failed") ? path.join(dir, r.compile.pdf) : null;
    const tex = path.join(dir, r.main);
    const awaiting = new Set(r.records.filter((a) => a.kind === "awaiting decision").map((a) => a.node)).size;
    const counts = `${r.records.length} annotation(s)${awaiting ? `, ${awaiting} awaiting your decision` : ""}, ${r.unlocated.length} unlocated; index ${path.join(dir, ANNOTATIONS_MD)}`;
    const note = sourceFailureNote(r.compile, "annotated");
    const line =
      r.compile.status === "passed" && pdf
        ? `${pdf} (${counts})`
        : note
          ? `${tex} (note: ${note}${pdf ? `; that PDF: ${pdf}` : ""}; ${counts})`
        : `${tex} (${r.compile.status === "failed" ? `compiling it failed: ${r.compile.reason}${pdf ? `; a partial PDF: ${pdf}` : ""}` : `not compiled: ${r.compile.reason}`}; ${counts})`;
    log(`annotated paper (${when}): ${line}`);
    // The renderer's own defects, then the model-written fragments that do not compile (the verify runner
    // routes these to their producers; `render_check.ts` `splitRenderDefects`).
    const split = splitRenderDefects(render);
    const block = renderBlock(split.renderer);
    if (block) log(`annotated paper (${when}): render check: ${block}`);
    if (split.fragments.length > 0) log(`annotated paper (${when}): render check: ${split.fragments.length} model-written fragment(s) fail the compile check (printed verbatim; a too-wide display shrunk): ${split.fragments.map((d) => `${d.node ?? "(file)"} (${d.block})`).join(", ")}`);
    return { path: r.compile.status === "passed" && pdf ? pdf : tex, line, result: r, error: null, render };
  } catch (err) {
    const msg = err instanceof Error ? err.message : String(err);
    log(`annotated paper (${when}): not written (${msg})`);
    return { path: null, line: `not written (${msg})`, result: null, error: msg };
  }
};

/** A halt message with the annotated paper named before the flag instructions. */
export function withAnnotatedPaper(message: string, a: AnnotatedOutcome): string {
  const line = `  Review the annotated paper: ${a.line}\n`;
  const at = message.indexOf("  Continue with one of:");
  return at >= 0 ? `${message.slice(0, at)}${line}${message.slice(at)}` : `${message}\n${line.trimEnd()}`;
}
