/**
 * V6 — per-result correctness report.
 *
 * Deterministic and model-free: the stage only LOADS what earlier stages produced, runs the
 * mechanical Lean audit (full barrel build + soundness scan + `#print axioms`), and hands both
 * to the pure assembler in `report.ts`. It runs after F5 (`stage_completed === "5"`) or directly
 * after a V1.5 refutation, in which case there is no F output at all (`earlyStop`) and every
 * un-refuted result is reported as `not_checked` rather than as anything verified.
 *
 * It re-hashes `discovery/core.json` first and refuses a core that is not the one V1.5 accepted:
 * every verdict below is about THAT core, so a core edited after the proofs were written would
 * be reported as verified on the strength of a proof of a different statement.
 *
 * The stage NEVER mutates `state.verify.findings` — the findings are the record the report reads,
 * and a reporter that could edit them could edit away the refutation it is supposed to publish.
 */
import { rethrowCodexAuthError } from "../shared/codex_auth.js";
import { existsSync } from "node:fs";
import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { parseTypedCore } from "../core/core_io.js";
import { graphPath, loadGraph } from "../graph/store.js";
import type { FormalizationGraph } from "../graph/types.js";
import { crosswalkFullJsonPath, leanTheoremDir } from "../paths.js";
import { STAGE_ORDER } from "../constants.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import type { CrosswalkEntry } from "../types.js";
import { sha256File } from "./core_hash.js";
import { collectLeanEvidence as realCollectLeanEvidence, type CollectLeanEvidence } from "./lean_evidence.js";
import { readV1Warnings, V1_LINT_WARNINGS_FILE } from "./lint_warnings.js";
import { ANNOTATED_DIR, ANNOTATIONS_MD, sourceFailureNote, writeAnnotatedPaper, type AnnotationInput, type CompileTex } from "./annotated_paper.js";
import { annotationInput, readAnnotationRecords } from "./annotate_run.js";
import { resultNames } from "./report_plain.js";
import { loadUnits } from "./units.js";
import { isStructuredExplanation, noteProse, type NoteProse, type OwnerExplanation } from "./owner_text.js";
import { buildReport, renderReport, REPORT_BUCKETS, type ReportCitedLean, type ReportInputStatus, type VerifyReportJson } from "./report.js";
import { readPatchFile } from "./patches.js";
import { parseFileDecls } from "../formalization/lean_rows.js";
import { leanNameLeaf } from "../presentation/lean_decl_name.js";
import { extractFullDeclSource } from "../presentation/lean_extract.js";
import type { Core } from "../core/schema.js";
import { BUNDLE_DIR, writeBundle } from "./bundle.js";
import { buildF4Seal } from "./f4_seal.js";
import type { PublicTree } from "./bundle_lean.js";
import { isCoreBearingEnv } from "./transcription_lint.js";
import {
  VERIFY_FILES,
  type EnvsJson,
  type V15Review,
  type VerifyStage,
  type VerifyStageArgs,
  type VerifyStageResult,
} from "./types.js";

/** `discovery/v1_scope.json`, as V1 writes it (`stage_v1.ts` `V1_SCOPE_FILE`; the path is in
 * `VERIFY_FILES` so the report stage does not pull in the V1 agent machinery). */
const V1_SCOPE_FILE = VERIFY_FILES.v1Scope;

/** The report counts as a full run only when F5 completed (cursor at "5", or "V6" on a re-run). */
const FINAL_F_STAGE_INDEX = STAGE_ORDER.indexOf("5");

async function readJsonFile(file: string): Promise<unknown> {
  return JSON.parse(await readFile(file, "utf8")) as unknown;
}

export interface StageV6Deps {
  collectLeanEvidence?: CollectLeanEvidence;
  /** The annotated paper's compile step (tests mock it; default: pdflatex / latexmk on PATH). */
  compileTex?: CompileTex;
  /** Write the report and the bundle HERE and leave the run as it is (no annotated paper, no cache,
   * no state): `paperformalizer report --out`. Default: the run directory. */
  outDir?: string;
  /** Compare the bundle's base libraries with their public revisions (`report --verify-public`). */
  publicTree?: PublicTree;
}

/**
 * The Lean declaration of each cited gate of the graph, by core node id: its name, file and line
 * under `leanDir` and its source text — what Lean assumes for the citation, which the report prints
 * (`ReportCitedHypothesis.lean`). A file or declaration not found leaves line and text null.
 */
export async function citedGateDeclarations(core: Pick<Core, "statements">, graph: FormalizationGraph, leanDir: string): Promise<Record<string, ReportCitedLean>> {
  const out: Record<string, ReportCitedLean> = {};
  for (const s of core.statements) {
    // (an assumed gate only: a cited result Lean proves from the libraries is no assumption)
    const node = s.status === "cited" ? graph.nodes.find((n) => n.id === s.id) : undefined;
    const lean = node?.kind === "gate" && node.gate?.gate_class === "cited" ? node.lean : undefined;
    if (!lean?.decl_name || !lean.file) continue;
    const decl = lean.decl_name;
    const text = await readFile(path.join(leanDir, lean.file), "utf8").catch(() => null);
    const named = text ? parseFileDecls(text).decls.filter((d) => leanNameLeaf(d.name) === leanNameLeaf(decl)) : [];
    const full = (d: (typeof named)[number]): string => (d.ns ? `${d.ns}.${d.name}` : d.name);
    const at = named.find((d) => decl === full(d) || decl.endsWith(`.${full(d)}`)) ?? named[0];
    let statement: string | null = null;
    try {
      statement = text && at ? extractFullDeclSource(text, at.name, at.line).trim() : null;
    } catch {
      statement = null;
    }
    out[s.id] = { decl, file: lean.file, line: at?.line ?? null, statement };
  }
  return out;
}

/**
 * Build the V6 stage. `deps.collectLeanEvidence` is injectable so tests never spawn lake.
 */
export function makeStageV6(deps: StageV6Deps = {}): VerifyStage {
  const collect = deps.collectLeanEvidence ?? realCollectLeanEvidence;

  return async (args: VerifyStageArgs): Promise<VerifyStageResult> => {
    const { repoRoot, qid, runDir, state, dryRun, log } = args;
    const verify = state.verify;
    if (!verify) {
      throw new Error("V6: state.verify is missing — it was not seeded by `paperformalizer verify`.");
    }
    const earlyStop = STAGE_ORDER.indexOf(state.stage_completed) < FINAL_F_STAGE_INDEX;

    // --- required inputs. A missing one is a broken run, not a reportable state.
    const envsFile = path.join(runDir, VERIFY_FILES.envsJson);
    if (!existsSync(envsFile)) {
      throw new Error(`V6: ${VERIFY_FILES.envsJson} is missing at ${envsFile} — re-run V1.`);
    }
    const envs = (await readJsonFile(envsFile)) as EnvsJson;
    const coreFile = path.join(runDir, VERIFY_FILES.coreJson);
    if (!existsSync(coreFile)) {
      throw new Error(`V6: ${VERIFY_FILES.coreJson} is missing at ${coreFile} — re-run V1.`);
    }
    // IDENTITY GATE. Every row of this report says something about the core on disk, but what
    // the Lean was proved from is the core V1.5 ACCEPTED (`state.verify.core_sha256`, the same
    // hash the F-stage entry gate enforces). A core edited or re-extracted after F5 — which
    // `--from-stage V6` makes a one-command path — would otherwise be reported as verified on
    // the strength of a proof of something else. So re-hash it and refuse a mismatch.
    const coreSha = await sha256File(coreFile);
    const coreChanged =
      "core.json changed after V1.5 accepted it; re-review with --from-stage V1.5 and re-run " +
      `the F stages (accepted ${verify.core_sha256}, on disk ${coreSha}).`;
    if (!earlyStop) {
      if (!verify.core_sha256) {
        throw new Error(
          "V6: the run reports a completed F5 but no core was ever accepted by V1.5 " +
            "(state.verify.core_sha256 is unset) — re-review with --from-stage V1.5.",
        );
      }
      if (coreSha !== verify.core_sha256) throw new Error(`V6: ${coreChanged}`);
    } else if (verify.core_sha256 && coreSha !== verify.core_sha256) {
      // An early stop has no Lean to misreport, but the review it DOES publish was written
      // about the accepted core, so the same mismatch invalidates it.
      throw new Error(`V6: ${coreChanged}`);
    }
    const core = parseTypedCore(await readFile(coreFile, "utf8"), `verify core ${coreFile}`);
    // The user's version: the report diffs the corrected core against it, and statements a
    // minimal patch descoped (gone from core.json) still get a row from it.
    const transcribedFile = path.join(runDir, VERIFY_FILES.coreTranscribed);
    // The "as printed" side is part of what was reviewed: an edit after acceptance is refused like
    // an edited core.
    if (verify.transcribed_sha256 && (!existsSync(transcribedFile) || (await sha256File(transcribedFile)) !== verify.transcribed_sha256)) {
      throw new Error(
        `V6: ${VERIFY_FILES.coreTranscribed} changed or disappeared after V1.5 accepted the core; re-review with --from-stage V1.5.`,
      );
    }
    const transcribed = existsSync(transcribedFile)
      ? parseTypedCore(await readFile(transcribedFile, "utf8"), `verify core ${transcribedFile}`)
      : null;
    const descoped = (transcribed?.statements ?? []).filter((s) => !core.statements.some((c) => c.id === s.id));

    const inputs: ReportInputStatus = {
      v1_5_review: "absent",
      crosswalk_full: "absent",
      graph_json: "absent",
      v1_scope: "absent",
      lean_evidence: "absent",
    };

    // --- scope: what V1 asked the core to cover, else every core-bearing environment.
    const scopeFile = path.join(runDir, V1_SCOPE_FILE);
    let scope: string[];
    if (existsSync(scopeFile)) {
      const raw = (await readJsonFile(scopeFile)) as { envs?: unknown };
      if (!Array.isArray(raw.envs) || raw.envs.some((e) => typeof e !== "string")) {
        throw new Error(`V6: ${V1_SCOPE_FILE} has no string \`envs\` array (${scopeFile}).`);
      }
      scope = raw.envs as string[];
      inputs.v1_scope = `present (${scope.length} environment(s))`;
    } else {
      scope = envs.envs.filter(isCoreBearingEnv).map((e) => e.id);
      inputs.v1_scope = "absent: falling back to every core-bearing environment in envs.json";
    }

    // --- V1's non-blocking warnings (lint + parser). Absent file = V1 had none.
    const warnings = await readV1Warnings(runDir);
    log(
      `${warnings.lint.length} lint warning(s) and ${warnings.parser.length} parser warning(s) ` +
        `from ${V1_LINT_WARNINGS_FILE}`,
    );

    // --- V1.5 review: absent on a run whose review never ran.
    const reviewFile = path.join(runDir, VERIFY_FILES.v15Review);
    let review: V15Review | null = null;
    if (existsSync(reviewFile)) {
      review = (await readJsonFile(reviewFile)) as V15Review;
      inputs.v1_5_review = `present (verdict ${review.verdict})`;
    } else {
      inputs.v1_5_review = "absent: V1.5 wrote no review for this core";
    }

    // --- crosswalk + graph: the Lean-side anchors. On a completed F run they are the
    // deliverable, so their absence is an ERROR, not a null.
    const crosswalkFile = crosswalkFullJsonPath(repoRoot, qid);
    let crosswalk: CrosswalkEntry[] | null = null;
    if (existsSync(crosswalkFile)) {
      crosswalk = (await readJsonFile(crosswalkFile)) as CrosswalkEntry[];
      inputs.crosswalk_full = `present (${crosswalk.length} object(s))`;
    } else if (!earlyStop && !dryRun) {
      throw new Error(
        `V6: crosswalk_full.json is missing at ${crosswalkFile} although the run completed F5. ` +
          "Without it no paper result can be tied to a Lean declaration — re-run F5 (--from-stage F5).",
      );
    } else {
      // A dry run's F handler writes no artifacts; the report then marks every result unresolved.
      inputs.crosswalk_full = dryRun
        ? "absent: dry run (the F stages wrote nothing)"
        : "absent: the run stopped before the Lean formalization";
    }

    const gp = graphPath(runDir);
    let graph: FormalizationGraph | null = null;
    if (existsSync(gp)) {
      graph = await loadGraph(gp);
      inputs.graph_json = `present (${graph.nodes.length} node(s))`;
    } else if (!earlyStop && !dryRun) {
      throw new Error(
        `V6: graph.json is missing at ${gp} although the run completed F5. Without it the report ` +
          "cannot say which substrate gates a result still assumes — re-run F5 (--from-stage F5).",
      );
    } else {
      inputs.graph_json = dryRun
        ? "absent: dry run (the F stages wrote nothing)"
        : "absent: the run stopped before the Lean formalization";
    }

    // --- Lean evidence: a full barrel build, the soundness scan, and `#print axioms`.
    let lean = null;
    if (earlyStop) {
      inputs.lean_evidence = "not collected: the run stopped before the Lean formalization";
    } else if (dryRun) {
      inputs.lean_evidence = "not collected: --dry-run";
    } else {
      const declNames = (crosswalk ?? [])
        .map((e) => e.lean?.decl)
        .filter((d): d is string => typeof d === "string" && d.length > 0);
      const leanDir = leanTheoremDir(repoRoot, state.lean_subdir);
      log(`building the run barrel and auditing ${declNames.length} declaration(s) under ${leanDir}`);
      lean = await collect({ repoRoot, leanDir, declNames, exec: undefined });
      inputs.lean_evidence =
        `collected (build ${lean.build.ok ? "ok" : "FAILED"}, ` +
        `${lean.sorry_scan.length} scan issue(s), ${Object.keys(lean.axioms).length} declaration(s))`;
    }

    // The author-facing explanation of each error: the structured one on file (no model call here).
    const explanations = await reportExplanations(runDir, { transcribed: transcribed ?? core, review, verify, log });
    const { json } = buildReport({
      qid,
      explanations,
      patches: await readPatchFile(runDir),
      withdrawn: (verify.rejected_rewinds ?? [])
        .filter((r) => r.by === "owner")
        .map((r) => ({ node: r.node, stage: r.stage, finding: r.detail, reason: r.reason, pin: r.pin ?? null })),
      envs,
      scope,
      core,
      review,
      findings: verify.findings,
      addedAssumptions: state.added_assumptions ?? [],
      crosswalk,
      graph,
      lean,
      ...(graph && !earlyStop ? { citedLean: await citedGateDeclarations(core, graph, leanTheoremDir(repoRoot, state.lean_subdir)) } : {}),
      warnings,
      descoped,
      transcribed,
      flags: {
        verify_no_d_rewind: state.flags.verify_no_d_rewind,
      },
      stageCompleted: state.stage_completed,
      earlyStop,
      sourceSha256: verify.source.sha256,
      inputs,
    });

    const out = deps.outDir ?? runDir;
    const jsonPath = path.join(out, VERIFY_FILES.reportJson);
    const mdPath = path.join(out, VERIFY_FILES.reportMd);
    const main = verify.source.main_file || envs.main_file;
    const rec = await readAnnotationRecords(runDir, log);
    const annotation = annotationInput({ envs, verify, core, transcribed, review, records: rec });
    // The annotated paper and the bundle never fail the stage: the report is the deliverable of record.
    if (!deps.outDir) json.annotated = await annotatePaper({ runDir, qid, main, input: annotation, compile: deps.compileTex, log });
    else {
      const prior = existsSync(path.join(runDir, VERIFY_FILES.reportJson)) ? ((await readJsonFile(path.join(runDir, VERIFY_FILES.reportJson))) as VerifyReportJson).annotated : undefined;
      if (prior) json.annotated = prior;
    }
    const bundleDir = path.join(out, BUNDLE_DIR);
    try {
      const b = await writeBundle({
        runDir,
        toolkitRoot: repoRoot,
        slug: qid,
        outDir: bundleDir,
        mainFile: main,
        leanSubdir: earlyStop || dryRun ? null : state.lean_subdir,
        input: annotation,
        report: json,
        promoted: verify.promotion?.promoted ?? [],
        ...(graph && !earlyStop && !dryRun ? { seal: buildF4Seal({ slug: qid, paperSha256: verify.source.sha256, arxiv: verify.source.arxiv ?? null, graph, delivery: state.delivery_review_receipts, cited: state.cited_review_receipts }) } : {}),
        compile: deps.compileTex,
        ...(deps.publicTree ? { publicTree: deps.publicTree } : {}),
        ...(deps.outDir ? { compileRecord: path.join(out, "bundle_compile.json"), checkFragments: false } : {}),
        log,
      });
      json.names = b.names;
      json.bundle = b.bundle;
      if (graph && !earlyStop && !dryRun && !deps.outDir && b.bundle.todo.blocking === 0) log(`Share your checked work to help other people: press Share on the paper's page, or run \`paperformalizer share ${qid}\`.`);
    } catch (err) {
      rethrowCodexAuthError(err);
      const msg = err instanceof Error ? err.message : String(err);
      log(`bundle: not written (${msg})`);
      // Without the compiled paper's numbering the results still get their titles and labels:
      // the plain report must never call every result "a condition or definition".
      const starred = new Set(envs.envs.filter((e) => e.envName.endsWith("*")).map((e) => e.id));
      json.names = resultNames(json.results, () => undefined, (r) => starred.has(r.env_id));
      json.bundle = { dir: BUNDLE_DIR, error: msg, paper: { main, pdf: null, pages: null, compile: { status: "skipped", tool: null, reason: msg } }, todo: { total: 0, blocking: 0 }, lean: null };
    }
    const report = renderReport(json);
    await writeJsonAtomic(jsonPath, json);
    await writeFile(mdPath, report, "utf8");
    if (existsSync(bundleDir)) await writeFile(path.join(bundleDir, "REPORT.md"), report, "utf8");
    if (!deps.outDir) verify.report_path = mdPath;

    const counts = REPORT_BUCKETS.filter((b) => json.summary[b] > 0)
      .map((b) => `${b} ${json.summary[b]}`)
      .join(", ");
    return {
      status: "completed",
      message:
        `${json.verdict} over ${json.results.length} result(s)` +
        (counts ? ` (${counts})` : "") +
        `; report at ${mdPath}`,
    };
  };
}

export const runStageV6: VerifyStage = makeStageV6();

/**
 * Write `annotated/` (see `annotated_paper.ts`): what the report says of it (`annotated` in
 * `report.json`, a section of `report.md`). Any failure is logged and recorded, never thrown.
 */
async function annotatePaper(a: {
  runDir: string;
  qid: string;
  main: string;
  input: Omit<AnnotationInput, "files">;
  compile: CompileTex | undefined;
  log: (msg: string) => void;
}): Promise<Record<string, unknown>> {
  try {
    // Nothing is pending at V6 (`pending` absent), and the tree is rebuilt from scratch: no
    // "awaiting your decision" block of an earlier halt survives into the final paper.
    const r = await writeAnnotatedPaper({ runDir: a.runDir, slug: a.qid, mainFile: a.main, input: a.input, compile: a.compile, log: a.log });
    const tex = `${ANNOTATED_DIR}/${r.main}`;
    const pdf = r.compile.status === "passed" && r.compile.pdf ? `${ANNOTATED_DIR}/${r.compile.pdf}` : null;
    const note = sourceFailureNote(r.compile, "annotated");
    return { tex, pdf, index: `${ANNOTATED_DIR}/${ANNOTATIONS_MD}`, annotations: r.records.length, unlocated: r.unlocated.length, compile: { status: r.compile.status, tool: r.compile.tool, reason: r.compile.reason, ...(note ? { note } : {}) } };
  } catch (err) {
    rethrowCodexAuthError(err);
    const msg = err instanceof Error ? err.message : String(err);
    a.log(`annotated paper: not written (${msg})`);
    return { error: msg };
  }
}

/** Each repair's note for the report, as the author reads it (`noteProse`): the fixer's, on the patch
 * or the unfixable entry. */
async function reportExplanations(
  runDir: string,
  a: { transcribed: import("../core/schema.js").Core; review: V15Review | null; verify: NonNullable<import("../types.js").StateJson["verify"]>; log: (m: string) => void },
): Promise<Record<string, NoteProse>> {
  const rec = await readAnnotationRecords(runDir, a.log);
  const out: Record<string, OwnerExplanation> = {};
  for (const x of [...(rec.patches?.unfixable ?? []), ...(rec.patches?.patches ?? [])]) {
    if (isStructuredExplanation(x.owner_explanation)) out[x.node] = x.owner_explanation;
  }
  const units = await loadUnits(runDir, { write: false });
  return Object.fromEntries(Object.entries(out).map(([id, e]) => [id, noteProse(e, units?.textById)]));
}
