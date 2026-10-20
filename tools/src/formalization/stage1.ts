// Formalization Stage 1 (F1) — the FORMALIZATION PLANNER.
//
// The typed core V1.5 accepted (`discovery/core.json`) is the machine-readable structural source
// of truth (symbols, atomic assumptions, class/construction definitions, statements,
// dep-DAG). F1 does not re-extract structure from the prose .tex: it authors the
// per-node formalization PLAN (`formalization/plan.json`) that maps every core node +
// ambient world to a Lean object, maximizing reuse of the base libraries and the toolkit.
// F2 then implements that plan.

import { LEAN_HEADER_CONTRACT } from "./lean_header_contract.js";
import { existsSync } from "node:fs";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import path from "node:path";
import { MODEL_PLAN } from "../constants.js";
import type { ReviewResult } from "../judgment.js";
import type { PipelineContext, StageResult, StateJson } from "../types.js";
import {
  artifactPaths,
  baseBrief,
  correctionBlock,
  parseStageOutput,
  readPrompt,
  readRequired,
  type StageDeps,
} from "../pipeline_support.js";
import { writeLeanLspMcpConfig } from "../workers/claude.js";
import { dispatchClaudeAgent } from "../framework/agent_dispatch.js";
import { buildGraphFromCorePlan } from "../graph/from_core.js";
import { renderBridgeNote } from "../graph/render_note.js";
import { graphPath, loadGraph, saveGraph } from "../graph/store.js";
import { mergeStage1RevisionGraph } from "../graph/revise_merge.js";
import { type Core } from "../core/schema.js";
import { coreJsonPath, formalizationView, parseTypedCore } from "../core/core_io.js";
import { BINDING_READINGS_NOTE, plannerCoreContextValue, restrictCoreContextValue } from "./core_context.js";
import { bindingReadings } from "../verify/core_graph.js";
import { logPlanGateNotes, planHygieneViolations } from "../formalization/plan/plan_gate.js";
import { planGateOnDisk } from "../formalization/plan/gate_run.js";
import { PlanSchema, type Plan } from "../formalization/plan/schema.js";
import { coreReuseCandidateBlock } from "../formalization/reuse_render.js";
import { indexSourcesForContext } from "../library/sources.js";
import { librarySearchPromptBlock, toolkitSearchCommand } from "../toolkit/search.js";
import { theoremCheckerToolsDir } from "../toolkit/config.js";
import { laterStageEverRan } from "../shared/resume_mode.js";
import { parseJsonWithEscapeRepair, parseJsonWithEscapeRepairStatus } from "../shared/codex_json.js";
import { planCorePath } from "../paths.js";
import { whatChangedBlock } from "./core_delta.js";
import { BEYOND_SCOPE_KEY, coreChangeSeeds, namedNodeIds, nodeReferenceIndex, reviseAffectedNodeIds, reviseLookupBlock } from "./revise_scope.js";
import { appendPipelineLog } from "../log.js";
import { resetFormalizationLoopCounters } from "./loop_limits.js";

/** The core the plan on disk was written from, or null when none was recorded (or it is unreadable). */
async function readPlanCore(p: string): Promise<Core | null> {
  if (!existsSync(p)) return null;
  try {
    return formalizationView(parseTypedCore(await readFile(p, "utf8"), `F1: ${p}`));
  } catch {
    return null;
  }
}

/** Copy the verified cited source-of-record (V1.5's) into the F1 plan in place. */
export function copyVerifiedCitedSourcesToPlan(planObj: unknown, core: Core): number {
  if (!planObj || typeof planObj !== "object") return 0;
  const pj = planObj as {
    nodes?: Record<string, { source?: string }>;
    citations?: Array<Record<string, unknown> & { id?: string }>;
  };
  let copied = 0;
  for (const s of core.statements.filter((x) => x.status === "cited")) {
    const citeId = pj.nodes?.[s.id]?.source;
    const citation = citeId && pj.citations?.find((c) => c.id === citeId);
    if (!citation || !s.source) continue;
    citation.locator = s.source.locator;
    // An inline citation (`cited_in`) has no statement of record here: its text is the paper's
    // passage, and the Lean review reads the cited work's file of the run (`citedSourceOfRecord`).
    const verbatim = s.cited_in ? undefined : (s.source.verbatim_statement ?? s.proof_tex?.trim() ?? undefined);
    if (verbatim) citation.verbatim_statement = verbatim;
    else if (s.cited_in) delete citation.verbatim_statement;
    if (s.source.arxiv) citation.arxiv = s.source.arxiv;
    if (s.source.doi) citation.doi = s.source.doi;
    if (s.source.url) citation.url = s.source.url;
    if (s.source.attestation) citation.attestation = s.source.attestation;
    copied++;
  }
  return copied;
}

/** The plan on disk as a revise reads it: what the schema parses, or null (absent, unparseable). */
async function readPlanOnDisk(p: string): Promise<{ raw: unknown; plan: Plan | null } | null> {
  if (!existsSync(p)) return null;
  try {
    const raw = parseJsonWithEscapeRepair(await readFile(p, "utf8"));
    const parsed = PlanSchema.safeParse(raw);
    return { raw, plan: parsed.success ? (parsed.data as Plan) : null };
  } catch {
    return null;
  }
}

/**
 * The seeds of an F1 revise (`reviseAffectedNodeIds` closes them): the nodes the correction or
 * the directive names and the nodes that moved since the plan was written. A hygiene finding
 * (P11) names a plan entry whose core node did not move, so it seeds nothing. Pure; exported for tests.
 */
export function stage1ReviseSeeds(
  core: Core,
  args: { planCore: Core | null; prior: ReviewResult | null; directive: string | null },
): string[] {
  const texts: Array<string | undefined> = [args.directive ?? undefined];
  if (args.prior && (args.prior.status === "revise" || args.prior.status === "reject")) {
    for (const f of args.prior.perItemFindings) if (f.verdict !== "FLAG-P11") texts.push(f.label, f.one_line);
    texts.push(args.prior.verbatim_critique);
  }
  return [...new Set([...namedNodeIds(core, texts), ...(args.planCore ? coreChangeSeeds(args.planCore, core).nodes : [])])];
}

/** The PLAN HYGIENE block of a revise: every P11 violation of the plan on disk, so a plan that
 *  grew by accretion is compacted in the same pass that patches it. Empty when there is none. Pure. */
export function planHygieneBlock(planRaw: unknown): string {
  const violations = planHygieneViolations(planRaw);
  if (violations.length === 0) return "";
  return [
    "=== PLAN HYGIENE (the gate's P11 — fix ALL of it in this pass) ===",
    "The plan on disk records history. It holds the CURRENT plan only: for every entry below, REWRITE its",
    "`notes` to the current plan of that entry within the cap and DELETE the keys listed (fold into `notes`",
    "what one of them says of the current plan; drop what it says of an earlier one). Change nothing else of",
    "these entries. Read each from plan.json by its id.",
    ...violations.map((v) => `- ${v.where}: ${v.message}`),
    "=== END PLAN HYGIENE ===",
    "",
  ].join("\n");
}

/** Locate the first bracket mismatch in a JSON text, ignoring brackets inside strings:
 * "opened `{` at line 128, closed by `]` at line 327". Null when the brackets balance (the
 * error is elsewhere — a bad escape, a stray comma). Exported for tests. */
export function describeJsonSyntaxError(text: string): string | null {
  const stack: Array<{ ch: string; line: number }> = [];
  let inString = false;
  let escaped = false;
  let line = 1;
  for (const ch of text) {
    if (ch === "\n") line += 1;
    if (inString) {
      if (escaped) escaped = false;
      else if (ch === "\\") escaped = true;
      else if (ch === '"') inString = false;
      continue;
    }
    if (ch === '"') inString = true;
    else if (ch === "{" || ch === "[") stack.push({ ch, line });
    else if (ch === "}" || ch === "]") {
      const open = stack.pop();
      if (!open) return `stray \`${ch}\` at line ${line}`;
      if ((open.ch === "{") !== (ch === "}")) {
        return `opened \`${open.ch}\` at line ${open.line}, closed by \`${ch}\` at line ${line}`;
      }
    }
  }
  if (stack.length > 0) return `unclosed \`${stack[stack.length - 1]!.ch}\` opened at line ${stack[stack.length - 1]!.line}`;
  return null;
}

export async function runStage1(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  priorReview?: ReviewResult | null;
  attempt?: number;
  /** Set on the ONE bounded re-dispatch after the planner wrote a plan.json that is not
   *  valid JSON: the parser's message plus a bracket diagnosis, for an in-place fix. */
  planSyntaxError?: string;
}): Promise<StageResult> {
  const paths = artifactPaths(args.ctx, args.state);
  const corePath = coreJsonPath(args.ctx);
  // The typed core is the structural input and is REQUIRED: V1.5 accepts it before any F
  // stage runs, so absence is a fault (a plan authored from prose alone silently loses the
  // structural ground truth).
  const coreText = await readRequired(corePath, "F1 planning");
  let core: Core;
  /** The core as accepted, umbrellas included: the graph builder keeps their alias slots. */
  let acceptedCore: Core;
  try {
    acceptedCore = parseTypedCore(coreText, `F1 planning: core.json at ${corePath}`);
    core = formalizationView(acceptedCore);
  } catch (err) {
    throw new Error(
      `F1 planning: core.json at ${corePath} failed to parse/validate: ${err instanceof Error ? err.message : String(err)} (a core from before the typed core? rebuild it with --from-stage V1)`,
    );
  }
  // Readings V1.5 pinned (and conditions it appended) follow their node's text in the prompt.
  const hasBinding = [...core.statements, ...core.assumptions, ...core.definitions].some((n) => bindingReadings(core, n.id).length > 0);

  // REVISE MODE (token-saver, drift-guard). F1 re-runs on two paths: the F1.5
  // boundary loop (carries `priorReview`) and a re-plan under a directive (no
  // priorReview: the runner or the orchestrator parked it on
  // `flags.f1_revise_directive`). In either case the prior plan is on disk and only
  // the flagged nodes need to change — point the worker at it and Edit in place.
  const f1Directive = args.state.flags.f1_revise_directive ?? null;
  // A re-plan entered under a directive is a ruling on the plan (the orchestrator's after a halt,
  // or the runner's): the F1↔F1.5 correction budget starts over. Not on a retry inside the
  // boundary loop, where an unconsumed directive is still on file.
  if (f1Directive && !args.priorReview) resetFormalizationLoopCounters(args.state);
  const hasLaterStageHistory = await laterStageEverRan(args.ctx, args.state, "1");
  const isRevise =
    args.priorReview?.status === "revise" ||
    !!f1Directive ||
    hasLaterStageHistory;
  const patching = isRevise && existsSync(paths.plan);
  let reviseBlock = "";
  /** The nodes a patch is about (`reviseAffectedNodeIds`), shown in full. */
  let affected = new Set<string>();
  /** A patch with no record of what moved and nothing naming it compares the plan with the whole core. */
  let wholeCore = !patching;
  let planOnDisk: Plan | null = null;
  if (patching) {
    // What moved since the plan was written. Without a record of that core, what moved under an
    // unchanged id cannot be told — the names in a correction or a directive are not the whole
    // change — so the plan is compared with the whole core.
    const planCore = await readPlanCore(planCorePath(args.ctx.repoRoot, args.ctx.qid));
    const named = args.priorReview?.status === "revise" || !!f1Directive;
    const onDisk = await readPlanOnDisk(paths.plan);
    planOnDisk = onDisk?.plan ?? null;
    wholeCore = !planCore;
    if (!planCore) {
      const why = `F1 revise has no readable record of the core its plan was written against (${planCorePath(args.ctx.repoRoot, args.ctx.qid)}): what moved since cannot be told; the plan is compared with the whole core.`;
      console.warn(`[theoremchecker] ${why}`);
      await appendPipelineLog(args.ctx, { stage: "1", status: "revise-scope", duration_ms: 0, message: `WHOLE CONTEXT — ${why}` });
    }
    affected = reviseAffectedNodeIds(core, planOnDisk, stage1ReviseSeeds(core, { planCore, prior: args.priorReview ?? null, directive: f1Directive }));
    // The gate's hygiene violations go into THIS pass (a correction from the gate already lists them).
    const hygieneBlock = (args.priorReview as { classification?: string } | null | undefined)?.classification === "plan-gate" ? "" : planHygieneBlock(onDisk?.raw);
    reviseBlock = [
      planCore || !named ? whatChangedBlock(planCore, core) : "",
      hygieneBlock,
      await readPrompt(args.ctx, "stage1_head_revise.txt"),
      "",
      f1Directive
        ? `DIRECTIVE (from the runner or the orchestrator — fix the plan as it says):\n${f1Directive}\n`
        : "",
      `Prior plan to patch (read the entries you edit, then Edit in place): ${paths.plan}`,
      "",
    ].filter(Boolean).join("\n");
  }

  const reuseBlock = patching
    ? ""
    : coreReuseCandidateBlock(indexSourcesForContext(args.ctx), core, {
        searchCommand: args.ctx.toolkit
          ? toolkitSearchCommand(theoremCheckerToolsDir(), args.ctx.toolkit.toolkitRoot)
          : undefined,
        // Semantic blend: pure-lexical ranking surfaced surface-token matches over
        // concept-correct declarations. Degrades to lexical-only if embeddings are stale.
        semantic: true,
      });

  // The core as the planner reads it: the slim view (no proof bodies or positioning prose) with
  // the cited bibliography entries. A patch gets the affected nodes in full, a reference line for
  // every other node, and the lookup duty (`revise_scope.ts`); the rest is on disk.
  const coreView = plannerCoreContextValue(core);
  const nodeCount = core.assumptions.length + core.definitions.length + core.statements.length;
  const coreBlock = wholeCore
    ? `Typed core JSON (the structural source of truth — map EVERY node; do NOT re-derive structure from prose; proof bodies and positioning prose omitted, the full file is at ${corePath})${hasBinding ? `. ${BINDING_READINGS_NOTE}` : ""}:\n${JSON.stringify(coreView)}`
    : [
        affected.size > 0
          ? `Typed core — the ${affected.size} of ${nodeCount} nodes this revise affects, in full (symbols and settings are in the core file)${hasBinding ? `. ${BINDING_READINGS_NOTE}` : ""}:\n${JSON.stringify(restrictCoreContextValue(coreView, affected))}`
          : "Typed core — the change above names no core node, so none is shown in full.",
        "",
        reviseLookupBlock({
          index: nodeReferenceIndex(core, planOnDisk, affected),
          shown: affected.size,
          total: nodeCount,
          corePath,
          planPath: paths.plan,
          replyField: `\`${BEYOND_SCOPE_KEY}\``,
        }),
      ].join("\n");

  const syntaxFixBlock = args.planSyntaxError
    ? [
        "=== PLAN FILE IS NOT VALID JSON — FIX IT IN PLACE ===",
        `Your previous plan at ${paths.plan} does not parse: ${args.planSyntaxError}`,
        "Repair the file with a minimal Edit (do not regenerate it), then validate before returning:",
        "  node -e 'JSON.parse(require(\"fs\").readFileSync(process.argv[1],\"utf8\"))' <plan path>",
        "",
      ].join("\n")
    : "";

  const prompt = [
    syntaxFixBlock,
    correctionBlock(args.priorReview ?? null, args.attempt ?? 1),
    reviseBlock,
    (await readPrompt(args.ctx, "stage1_template.txt")).replaceAll(
      "{{HEADER_CONTRACT}}",
      () => LEAN_HEADER_CONTRACT,
    ),
    "",
    baseBrief(args.ctx, args.state),
    "",
    coreBlock,
    "",
    librarySearchPromptBlock(args.ctx),
    "",
    reuseBlock,
    "",
    patching
      ? ""
      : `Write the formalization plan JSON to ${paths.plan}.`,
    "Return only the JSON object specified in the prompt's `=== OUTPUT JSON ===` block.",
  ].join("\n");

  const out = await dispatchClaudeAgent({
    ctx: args.ctx,
    deps: args.deps,
    stage: "1",
    label: "F1 plan author",
    promptSources: ["stage1_template.txt", ...(isRevise ? ["stage1_head_revise.txt"] : []), corePath],
    input: {
      prompt,
      model: MODEL_PLAN.stage1.model,
      cwd: args.ctx.repoRoot,
      mcpConfigPath: writeLeanLspMcpConfig(args.ctx.repoRoot),
      allowedTools: [
        "Read", "Write", "Edit", "Grep", "Glob",
        // Substrate survey for the per-node reuse decisions.
        "mcp__lean-lsp__lean_leansearch",
        "mcp__lean-lsp__lean_loogle",
        "mcp__lean-lsp__lean_local_search",
        "mcp__lean-lsp__lean_hover_info",
        "mcp__lean-lsp__lean_file_outline",
      ],
    },
  });
  const parsed = parseStageOutput(out);
  if (parsed.status === "parse_failed") {
    // AUDIT-A: fail closed on unparseable stage output; why: F1 must not advance on garbage.
    throw new Error("Stage 1: F1 worker output did not parse (parse_failed) - refusing to advance on unparseable output");
  }
  const p = parsed as Record<string, unknown>;
  // The mechanical affected set under-reached: say where, so the rule can be widened.
  const beyond = Array.isArray(p[BEYOND_SCOPE_KEY]) ? (p[BEYOND_SCOPE_KEY] as unknown[]).map(String) : [];
  if (beyond.length > 0) {
    await appendPipelineLog(args.ctx, {
      stage: "1",
      status: "revise-scope",
      duration_ms: 0,
      message: `F1 revise looked up ${beyond.length} node(s) beyond the affected set (${affected.size}): ${beyond.join(", ")}`,
    });
    console.warn(`[theoremchecker] F1 revise looked up ${beyond.length} node(s) beyond the affected set: ${beyond.join(", ")}`);
  }

  // A blocked reply wrote no plan. On a re-plan the earlier plan is still on disk: advancing
  // would have F1.5 review that stale plan, and the blocker's message would be lost. F1 is not
  // completed (`advance: false`) and the block is on record (`flags.f1_blocked`): the
  // orchestrator rules, and a resume plans again before any review (`runStage1_5`).
  if (parsed.status?.startsWith("blocked")) {
    const notes = typeof p.feasibility_notes === "string" && p.feasibility_notes.trim() ? ` ${p.feasibility_notes.trim()}` : "";
    const message = `F1 ${parsed.status}: ${parsed.message ?? "the planner gave no reason"}${notes}${existsSync(paths.plan) ? " The plan on disk is the earlier one and was not reviewed again." : ""}`;
    args.state.flags.f1_blocked = { message, ...(args.priorReview ? { review: args.priorReview } : {}) };
    return { stage: "1", status: "checkpoint", advance: false, message };
  }
  args.state.flags.f1_blocked = null;

  // Read the just-written plan (if any) and run the deterministic gate as a
  // best-effort self-check — log violations. The F1.5 boundary enforces them as a
  // pre-review lint with producer retry (Phase 3); F1 never blocks on the gate.
  let planObj: unknown = null;
  if (existsSync(paths.plan)) {
    try {
      const parsedPlanText = parseJsonWithEscapeRepairStatus(await readFile(paths.plan, "utf8"));
      planObj = parsedPlanText.value;
      // PERSIST the repair. Repairing only in memory leaves an unparseable durable store
      // behind a gate that now passes, so every later reader must repeat the repair —
      // and F2's plan-derived directive builders do a bare `JSON.parse` and fail OPEN,
      // silently dropping the UNDELIVERED and gated-hyps blocks from the producer prompt.
      // Canonicalizing here keeps `plan.json` parseable for readers that do not repair.
      if (parsedPlanText.repaired) {
        await writeFile(paths.plan, JSON.stringify(planObj, null, 2), "utf8");
        console.warn(`[theoremchecker] F1 repaired invalid string escapes in ${paths.plan} and rewrote it canonically.`);
      }
    } catch (err) {
      const reason = err instanceof Error ? err.message : String(err);
      console.warn(`[theoremchecker] F1 wrote an unparseable plan at ${paths.plan}: ${reason}`);
      // A syntax slip is something the planner can fix in seconds; halting the run for it
      // is not. ONE bounded re-dispatch with the parser's message and a bracket diagnosis.
      if (!args.planSyntaxError) {
        const diagnosis = describeJsonSyntaxError(await readFile(paths.plan, "utf8"));
        console.warn(`[theoremchecker] F1: re-dispatching once to repair the plan file (${diagnosis ?? "no bracket diagnosis"})`);
        return runStage1({
          ...args,
          attempt: (args.attempt ?? 1) + 1,
          planSyntaxError: `${reason}${diagnosis ? `; ${diagnosis}` : ""}`,
        });
      }
    }
  }
  // V1.5 has already source-matched every status:"cited" node. F1 must COPY
  // that verified source of record, not ask the planner to reconstruct theorem
  // text from prose. Apply it deterministically through the cited node's cite:
  // alias. Legacy cores may store the attested transcription in proof_tex.
  // The plan's `qid` is the run's: the schema requires it and no prompt asks the planner for it.
  if (planObj && typeof planObj === "object" && !Array.isArray(planObj) && (planObj as { qid?: unknown }).qid !== args.ctx.qid) {
    planObj = { ...(planObj as object), qid: args.ctx.qid };
    await writeFile(paths.plan, JSON.stringify(planObj, null, 2), "utf8");
  }
  if (planObj && typeof planObj === "object") {
    const copied = copyVerifiedCitedSourcesToPlan(planObj, core);
    if (copied > 0) {
      await writeFile(paths.plan, JSON.stringify(planObj, null, 2), "utf8");
      console.warn(`[theoremchecker] F1 copied ${copied} verified cited source-of-record entr${copied === 1 ? "y" : "ies"} into the plan.`);
    }
  }
  let planGateOk = true;
  const parsedPlan = planObj ? PlanSchema.safeParse(planObj) : null;
  if (planObj) {
    // The same gate run F1.5's prelint applies next (`planGateOnDisk` memoizes it, so the
    // boundary does not run it a second time on an unchanged plan and core).
    const gate = planGateOnDisk(args.ctx, { planObj, coreText, core });
    logPlanGateNotes(gate.notes);
    planGateOk = gate.ok;
    if (!gate.ok) {
      console.warn(
        `[theoremchecker] F1 plan_gate: ${gate.violations.length} violation(s)\n  ` +
          gate.violations.slice(0, 12).map((v) => `${v.code} @ ${v.where}: ${v.message}`).join("\n  "),
      );
    }
  }
  // Judge cleanliness by the gate F1.5's prelint applies (with knownDecls) — a knownDecls-less
  // run here would clear the retry directives on a plan the boundary is about to bounce for
  // reuse-existence violations.
  const planGateClean =
    parsed.status === "completed" &&
    !!parsedPlan?.success &&
    planGateOk;
  // The core this plan was written from: the next re-plan's WHAT CHANGED block diffs against it.
  // Only a completed pass records it — a blocked one left the plan on disk for the older core.
  if (parsed.status === "completed" && parsedPlan?.success) {
    await writeFile(planCorePath(args.ctx.repoRoot, args.ctx.qid), coreText, "utf8");
  }
  if (planGateClean && f1Directive) {
    // why: keep the retry directive until F1 completed with a parsed, gate-clean plan.
    args.state.flags.f1_revise_directive = null;
  }

  // Emit the formalization graph from core + plan (the graph is the interchange the
  // F3/F4 proof loop refreshes off — without it the loop has no graph to refresh).
  // On revise, merge the structural delta into the existing graph. Later F stages
  // own its Lean links, proof state, review receipts, extracted edges, and auxiliary
  // nodes; rebuilding from an empty graph here would silently destroy all of them.
  // Best-effort: never blocks the stage. A failed revise merge leaves the existing
  // artifacts untouched rather than falling back to a destructive fresh write.
  try {
    // A malformed/partial revise must not replace valid downstream artifacts
    // with the builder's plan=null fallback.
    if (!parsedPlan?.success) throw new Error("plan is not schema-valid; preserving existing graph/note");
    const gp = graphPath(paths.formalizationDir);
    const rebuilt = buildGraphFromCorePlan(acceptedCore, parsedPlan.data);
    const g = isRevise && existsSync(gp)
      ? mergeStage1RevisionGraph(await loadGraph(gp), rebuilt)
      : rebuilt;
    await saveGraph(gp, g);
    // Bridge .md: the human record + report input + F5 premise-check
    // source, rendered deterministically from the graph (parseNoteBlocks-compatible).
    // The bridge is a canonical core+plan projection. Auxiliary proof-engineering
    // nodes belong in graph.json but must not leak into the paper-facing note.
    await mkdir(path.dirname(paths.md), { recursive: true });
    await writeFile(paths.md, renderBridgeNote(rebuilt), "utf8");
  } catch (err) {
    console.warn(`[graph] F1 core+plan emission skipped: ${err instanceof Error ? err.message : String(err)}`);
  }

  // The plan-audit checkpoint (CKPT 1) moved DOWNSTREAM to F1.5: when F1 produced
  // a usable plan it advances STRAIGHT into the F1.5 reuse-soundness review, so
  // F1 + F1.5 halt together at ONE consolidated CKPT 1 (fewer recall events for
  // the orchestrator). F1 still halts on its own when no usable plan was
  // parsed — there is nothing for F1.5 to review. It is the blocked halt's record and exit
  // (`flags.f1_blocked`, F1 not completed): a resume plans again before any review.
  if (!parsedPlan?.success) {
    const message = `F1 wrote no usable plan (${existsSync(paths.plan) ? `${paths.plan} does not parse as a plan` : "no plan file"})${parsed.message ? `: ${parsed.message}` : ""}. A resume plans again.`;
    args.state.flags.f1_blocked = { message, ...(args.priorReview ? { review: args.priorReview } : {}) };
    return { stage: "1", status: "checkpoint", advance: false, message };
  }
  return {
    stage: "1",
    status: "completed",
    message: parsed.message ?? "F1 plan authored; advancing to F1.5 reuse-soundness review (consolidated CKPT 1).",
  };
}
