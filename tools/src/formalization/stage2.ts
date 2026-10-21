// Formalization Stage 2.

import { LEAN_HEADER_CONTRACT } from "./lean_header_contract.js";
import { knownDeclsForContext } from "./known_decls.js";
import path from "node:path";
import { existsSync } from "node:fs";
import { mkdir, readFile, writeFile } from "node:fs/promises";
import { MODEL_PLAN } from "../constants.js";
import type { PipelineContext, StageResult, StateJson } from "../types.js";
import {
  artifactPaths,
  baseBrief,
  bookkeepingPolicyBlock,
  parseStageOutput,
  readIfExists,
  readPrompt,
  listLeanFiles,
  type StageDeps,
} from "../pipeline_support.js";
import { librarySearchPromptBlock } from "../toolkit/search.js";
import { baseLibraryNotesBlock } from "../toolkit/prompt_notes.js";
import { BINDING_READINGS_NOTE, SCOPED_SYMBOLS_NOTE, SHARED_READINGS_NOTE, formalizationCoreContextValue, readFormalizationCoreContext } from "./core_context.js";
import { BEYOND_SCOPE_KEY, beyondScopeReported, coreChangeSeeds, namedNodeIds, nodeReferenceIndex, planChangeSeeds, readReviseBasis, reviseLookupBlock, writeReviseBasis } from "./revise_scope.js";
import { appendPipelineLog } from "../log.js";
import { scaffoldBasisPath } from "../paths.js";
import { coreJsonPath, formalizationView, readFormalizationCore, readTypedCore, umbrellaIds } from "../core/core_io.js";
import type { Core } from "../core/schema.js";
import { logPlanGateNotes, runPlanGate, type PlanGateViolation } from "./plan/plan_gate.js";
import { PlanSchema, type Plan } from "./plan/schema.js";
import {
  buildF2RevisionContext,
  scaffoldCoverageGaps,
  revisionNotesFromRedirect,
  revisionTargetsFromRedirect,
  withReviewerFindings,
  type F2RevisionContext,
} from "./f2_revision_context.js";
import { PROOF_SCAFFOLD_MAX } from "./loop_limits.js";
import {
  describeTagReconciliation,
  reconcileScaffoldTags,
  reconciliationIsEmpty,
  tagReconciliationBlock,
  type TagReconciliation,
} from "./f2_tag_reconcile.js";
import { WORKER_BUILD_INACTIVITY_MS, dispatchAgent } from "../framework/agent_dispatch.js";
import {
  snapshotPriorProofs,
  injectCarryoverComments,
  restoreCarryoverProofs,
} from "./proof_carryover.js";
import {
  recordMissingArchitecture,
  missingArchitectureLedgerPath,
} from "../shared/missing_architecture_ledger.js";
import { seedAnnotations } from "../graph/annotate.js";
import { extractFromLean, parseAnnotatedDecls } from "../graph/extractor.js";
import { graphPath, loadGraph, saveGraph } from "../graph/store.js";
import { validate } from "../graph/validator.js";
import type { FormalizationGraph, Finding } from "../graph/types.js";
import { markUnreviewed } from "../graph/mutate.js";
import { objIdToNodeId } from "../graph/from_note.js";
import {
  findStatementSemanticDefs,
  parseLeanDecls,
  type StatementSemanticDef,
} from "./crosswalk.js";
import { laterStageEverRan } from "../shared/resume_mode.js";
import { parseJsonWithEscapeRepair } from "../shared/codex_json.js";
import { buildRunModules } from "./proof_review_loop.js";

/** Headline nodes whose statement meaning changed through an untagged inline
 * definition/structure during an F2 revise pass.  The headline's own Lean
 * signature hash can remain byte-identical while the body of (for example) its
 * output structure changes, so hash-only graph refresh would otherwise carry a
 * stale `matched` F2.5 verdict. */
export function hiddenDefinitionChangeTargets(
  before: StatementSemanticDef[],
  after: StatementSemanticDef[],
): string[] {
  const oldByName = new Map(before.map((d) => [d.name, d] as const));
  const newByName = new Map(after.map((d) => [d.name, d] as const));
  const names = new Set([...oldByName.keys(), ...newByName.keys()]);
  const targets = new Set<string>();
  for (const name of names) {
    const old = oldByName.get(name);
    const cur = newByName.get(name);
    if (old?.contentHash === cur?.contentHash) continue;
    for (const id of [...(old?.reachedFrom ?? []), ...(cur?.reachedFrom ?? [])]) {
      targets.add(objIdToNodeId(id));
    }
  }
  return [...targets].sort();
}

/** Canonicalize citation provenance after an F2 producer syncs implementation
 * details back into plan.json. A cited statement remains source-reviewed until
 * gate.ts stamps a lemma/theorem discharge. Its carrier may be either the
 * traditional Prop assumption or a non-Prop metadata def; F2 may change that
 * implementation detail, but may not erase/reclassify discovery provenance.
 *
 * Agent JSON commonly spells absent optional keys as null. Delete those keys
 * before schema validation, then restore the authoritative cited classification
 * on an undischargeable carrier. Proved lemma/theorem shapes are deliberately
 * untouched so P9 still rejects an unstamped self-discharge. */
export function canonicalizeCitedPlanAfterF2(
  planInput: unknown,
  core: Core,
): { plan: unknown; changed: boolean } {
  if (!planInput || typeof planInput !== "object" || Array.isArray(planInput)) {
    return { plan: planInput, changed: false };
  }
  const plan = planInput as Record<string, unknown>;
  if (!plan.nodes || typeof plan.nodes !== "object" || Array.isArray(plan.nodes)) {
    return { plan: planInput, changed: false };
  }
  const nodes = plan.nodes as Record<string, unknown>;
  let changed = false;
  for (const rawNode of Object.values(nodes)) {
    if (!rawNode || typeof rawNode !== "object" || Array.isArray(rawNode)) continue;
    const node = rawNode as Record<string, unknown>;
    if (node.gate === null) {
      delete node.gate;
      changed = true;
    }
    if (node.gate_class === null) {
      delete node.gate_class;
      changed = true;
    }
  }
  // A core assumption is realized as a `def <name> : Prop` (lean_kind `assumption`); a sync-back that
  // names that Lean keyword (`def`) is the same plan, not a kind change the gate should refuse.
  for (const assumption of core.assumptions) {
    const rawNode = nodes[assumption.id];
    if (!rawNode || typeof rawNode !== "object" || Array.isArray(rawNode)) continue;
    const node = rawNode as Record<string, unknown>;
    if (node.lean_kind === "def") {
      node.lean_kind = "assumption";
      changed = true;
    }
  }
  for (const statement of core.statements) {
    if (statement.status !== "cited") continue;
    const rawNode = nodes[statement.id];
    if (!rawNode || typeof rawNode !== "object" || Array.isArray(rawNode)) continue;
    const node = rawNode as Record<string, unknown>;
    if (node.citation_discharged === true) continue;
    const expectedKind = (statement.source?.carrier ?? "logical-claim") === "bibliographic-metadata"
      ? "def"
      : "assumption";
    if (node.lean_kind !== expectedKind) continue;
    if (node.gate !== true) {
      node.gate = true;
      changed = true;
    }
    if (node.gate_class !== "cited") {
      node.gate_class = "cited";
      changed = true;
    }
  }
  return { plan, changed };
}

/** Restore pre-existing Lean files that a revise producer deleted. F2 revise is
 * patch-in-place: removing an entire prior module is never an acceptable implicit
 * side effect. The caller fails closed after restoration so the deletion cannot
 * be mistaken for a successful incremental scaffold. */
export async function restoreDeletedReviseFiles(
  snapshot: Map<string, string>,
): Promise<string[]> {
  const restored: string[] = [];
  for (const [file, source] of snapshot) {
    if (existsSync(file)) continue;
    await mkdir(path.dirname(file), { recursive: true });
    await writeFile(file, source, "utf8");
    restored.push(file);
  }
  return restored.sort();
}

/** Parse `-- @node: <id>` and `-- @env: <id>` tag comments from every .lean file in
 *  a directory, so the plan gate can verify the emitted Lean covers the plan (P7). */
export async function parseLeanNodeTags(
  leanDir: string,
): Promise<{ nodes: Set<string>; envs: Set<string> }> {
  const nodes = new Set<string>();
  const envs = new Set<string>();
  if (!existsSync(leanDir)) return { nodes, envs };
  let files: string[];
  try {
    files = await listLeanFiles(leanDir);
  } catch {
    return { nodes, envs };
  }
  for (const f of files) {
    let text: string;
    try {
      text = await readFile(f, "utf8");
    } catch {
      continue;
    }
    // Ownership/environment anchors are top-level metadata and therefore must
    // start in column zero. This excludes both prose mentions and an indented
    // duplicate accidentally emitted inside a declaration body.
    for (const m of text.matchAll(/^--\s*@node:\s*([A-Za-z0-9:._-]+)\s*$/gm)) nodes.add(m[1]);
    for (const m of text.matchAll(/^--\s*@env:\s*([A-Za-z0-9:._-]+)\s*$/gm)) envs.add(m[1]);
  }
  return { nodes, envs };
}

export interface DuplicateLeanNodeAnchor {
  id: string;
  locations: string[];
}

/** Return repeated canonical node anchors across the entire run tree.  A Set-based
 * coverage gate cannot detect these, and the graph extractor intentionally rejects
 * them only after extraction, so F2 checks multiplicity directly before advancing. */
export async function findDuplicateLeanNodeAnchors(
  leanDir: string,
): Promise<DuplicateLeanNodeAnchor[]> {
  if (!existsSync(leanDir)) return [];
  const byId = new Map<string, string[]>();
  for (const file of await listLeanFiles(leanDir)) {
    const text = await readFile(file, "utf8").catch(() => "");
    for (const [index, line] of text.split(/\r?\n/).entries()) {
      const match = /^--\s*@node:\s*([A-Za-z0-9:._-]+)\s*$/.exec(line);
      if (!match) continue;
      const locations = byId.get(match[1]) ?? [];
      locations.push(`${file}:${index + 1}`);
      byId.set(match[1], locations);
    }
  }
  return [...byId.entries()]
    .filter(([, locations]) => locations.length > 1)
    .map(([id, locations]) => ({ id, locations }))
    .sort((a, b) => a.id.localeCompare(b.id));
}

/**
 * Parse `plan.json` for a producer-prompt directive builder.
 *
 * A plan that EXISTS but will not parse is a FAULT, not an absence. Returning an empty
 * directive here silently deletes a load-bearing block from the F2 prompt — the
 * UNDELIVERED list, or the gated-hyps instruction — and the run then fails downstream
 * looking exactly like a model that ignored its instructions, with nothing in the
 * transcript saying the instruction was never sent. Escape repair is applied first so an
 * agent-written plan carrying a raw `\(x\)` parses rather than tripping this.
 */
type PlanShape = ReturnType<typeof PlanSchema.parse>;

function parsePlanForDirective(planText: string, directive: string): PlanShape | null {
  if (!planText.trim()) return null;
  let raw: unknown;
  try {
    raw = parseJsonWithEscapeRepair(planText);
  } catch (err) {
    throw new Error(
      `F2 ${directive}: plan.json is present but unparseable (${err instanceof Error ? err.message : String(err)}). ` +
        "Refusing to build the producer prompt with this directive silently omitted — re-emit a well-formed plan.",
    );
  }
  const parsed = PlanSchema.safeParse(raw);
  if (!parsed.success) {
    console.warn(`[paperformalizer] F2 ${directive}: plan.json is not schema-valid; directive omitted from the producer prompt.`);
    return null;
  }
  return parsed.data;
}

/** Durable F2 instruction for disclosed non-delivery. These nodes remain in the
 * core/plan/graph, but must have no Lean declaration or @node anchor. */
export function undeliveredBlockFromPlan(planText: string): string {
  const plan = parsePlanForDirective(planText, "undelivered-objects block");
  if (!plan) return "";
  {
    const rows = Object.entries(plan.nodes)
      .filter(([, n]) => n.delivery_status === "undelivered")
      .map(([id, n]) => `  • ${id} (${n.delivery_role ?? "cited"}): ${n.delivery_reason ?? "reason missing"}`);
    if (rows.length === 0) return "";
    return [
      "=== UNDELIVERED OBJECTS — RETAIN IN PLAN, OMIT FROM LEAN ===",
      "The plan gate has classified the following objects as disclosed undelivered remarks.",
      "For each one, remove any existing Lean declaration and its `-- @node:` tag. Do not replace",
      "it with a Prop definition, axiom, gate, weakened theorem, or `sorry`. Preserve every unrelated",
      "declaration and proof body. The typed statement remains in core/plan/graph for presentation.",
      ...rows,
      "=== END UNDELIVERED OBJECTS ===",
      "",
    ].join("\n");
  }
}

/** Scaffold-side dual of the F2.5/F4 logical-gate review exemption: build a directive telling the producer
 *  to emit each registered `gate_class:"gated"` node and each cited logical assumption as an EXPLICIT `_of_gate`
 *  HYPOTHESIS on every consumer that threads it in `hyps` — NOT an in-proof `have … := by sorry`.
 *  Without this the producer treats a note-DERIVED gate as an in-proof obligation (the general bias),
 *  re-emits a `sorry`, and the filler escalates `build-substrate` on debt we chose to assume. Reading
 *  it from the plan (not a hand-set free-text directive) is what lets `bin/gate.ts` register a durable
 *  gate that survives every re-scaffold with no hand-editing. Empty when there are no gated nodes. */
function gatedHypsBlockFromPlan(planText: string): string {
  const parsedPlan = parsePlanForDirective(planText, "gated-hypothesis directive");
  if (!parsedPlan) return "";
  const plan = parsedPlan as { nodes?: Record<string, { gate?: boolean; gate_class?: string; lean_kind?: string; lean_name?: string; hyps?: string[] }> };
  const nodes = plan.nodes ?? {};
  const gated: { leanName: string; consumers: string[] }[] = [];
  for (const [id, n] of Object.entries(nodes)) {
    if (!n.gate || (n.gate_class === "cited" && n.lean_kind !== "assumption")) continue;
    const consumers = Object.entries(nodes)
      .filter(([, c]) => Array.isArray(c.hyps) && c.hyps.includes(id))
      .map(([cid, c]) => c.lean_name || cid);
    gated.push({ leanName: n.lean_name || id, consumers });
  }
  if (!gated.length) return "";
  return [
    "=== GATED SUBSTRATE-GATES — EMIT AS HYPOTHESES (registered via bin/gate.ts) ===",
    "",
    'The plan registers the DISCLOSED logical gate(s) below (`gate:true`, either build-gated or a cited Prop assumption). Each is',
    "an ASSUMED input this paper does NOT prove here (the run's report discloses every build-gated fact and",
    "cited logical claim). For EACH gate, emit it as an EXPLICIT `_of_gate`-style HYPOTHESIS on the signature",
    "of every listed consumer, and pass it through. This OVERRIDES the general 'derive a note-fact in-proof'",
    "guidance for THESE nodes specifically: do NOT inline them as an in-proof `have … := by sorry`, and do",
    "NOT drop them. A gate held as a signature hypothesis makes the consumer a sorry-free CONDITIONAL (the",
    "goal); an in-proof `sorry` makes it an un-closable obligation (not the goal). These are the ONLY",
    "hypotheses you may add that the note does not itself list — every other added premise is still drift.",
    "",
    ...gated.map((g) => `  • gate \`${g.leanName}\` → hypothesis on: ${g.consumers.join(", ") || "(no consumers threaded in plan hyps)"}`),
    "",
    "=== END GATED SUBSTRATE-GATES ===",
    "",
  ].join("\n");
}

/** Best-effort F2 graph link: seed `-- @node:` annotations from the obj_id
 *  convention, extract the Lean side into the graph (links, proof state,
 *  statement-uses edges), persist, and return advisory validation findings.
 *  Never throws, never blocks the scaffold. */
export async function linkGraphFromStage2(a: {
  qid: string;
  formalizationDir: string;
  leanDir: string;
  /** From-note rows whose cached review must be invalidated because an inline,
   * meaning-bearing dependency changed while their own signature stayed fixed. */
  invalidateReviewNodeIds?: string[];
}): Promise<{ graph: FormalizationGraph | null; findings: Finding[] }> {
  try {
    const p = graphPath(a.formalizationDir);
    if (!existsSync(p)) return { graph: null, findings: [] };
    await seedAnnotations(a.leanDir);
    const g = await loadGraph(p);
    const extracted = await extractFromLean(g, a.leanDir);
    let graph = extracted.graph;
    for (const id of a.invalidateReviewNodeIds ?? []) {
      const node = graph.nodes.find((n) => n.id === id);
      if (node?.provenance === "from-note") graph = markUnreviewed(graph, id);
    }
    await saveGraph(p, graph);
    return { graph, findings: validate(graph).findings };
  } catch {
    return { graph: null, findings: [] };
  }
}

/**
 * F2 may leave reuse lookup (P5) and module-resolution (P6) drift to the later typed phases.
 * Every other plan-gate code is structural/semantic and must refuse the scaffold.
 */
export function blockingPostSyncPlanViolations(violations: PlanGateViolation[]): PlanGateViolation[] {
  return violations.filter((violation) => violation.code !== "P5" && violation.code !== "P6");
}

/**
 * The plan goes back to F1: the gate refuses it on rules that read the plan and the core alone
 * (no Lean), so no scaffold can pass on it. The cursor is reset to F1 and F1.5's pre-lint hands
 * F1 the violations as its correction, within the F1↔F1.5 budget. `when` says whether a scaffold
 * call was spent: none before the scaffolder ran; after it, its sync-back wrote the refused plan.
 * The same refusal twice running is not F1's to cure (F1 restored the plan and it was broken the
 * same way again, e.g. by a standing redirect): it halts for the orchestrator instead of looping.
 */
function planBackToF1(state: StateJson, violations: PlanGateViolation[], when: string): StageResult {
  const listed = violations.map((v) => `${v.code} @ ${v.where}: ${v.message}`).join("\n  ");
  const signature = violations.map((v) => `${v.code} @ ${v.where}`).sort().join("|");
  if (state.flags.plan_rewind_violations === signature) {
    throw new Error(
      `F2 structural plan gate refused the plan ${when} — the same refusal as the last one F1 corrected, so re-planning does not cure it` +
        (state.flags.scaffold_redirect ? " (a scaffold redirect is pending: flags.scaffold_redirect may ask for what the gate refuses)" : "") +
        `:\n  ${listed}`,
    );
  }
  state.flags.plan_rewind_violations = signature;
  state.stage_completed = "1";
  const message = `F2 structural plan gate refused the plan ${when} — back to F1 through the F1.5 pre-lint:\n  ${listed}`;
  console.warn(`[paperformalizer] ${message}`);
  return { stage: "2", status: "rewound", advance: false, message };
}

/** How the scaffolder reads the plan it is given, and tags what it writes. */
const PLAN_CONTRACT_NOTE =
  "plan.json — the contract you implement). For the SETUP/ENVIRONMENT symbols: tag EVERY Lean location that helps realize a core symbol's space with \"@realizes <core-symbol-name>(<short clause hint>)\" — using the EXACT core symbol name as the JSON spells it (case-sensitive; never the Lean field name). Put the tag at the most SPECIFIC location: for a structure FIELD, an INLINE trailing comment on that field line ('<field> : <carrier> -- @realizes <symbol>(carrier <type>; range via <predicate>)'), NOT lumped on the structure docstring; for a MULTI-clause predicate (a Prop def of the form A and B and …), an INLINE comment on the SPECIFIC conjunct line that pins each symbol ('-- @realizes <symbol>(<the clause>)' on that conjunct's line); a SINGLE-clause predicate may use its docstring. A symbol's space is normally carried by the CONJUNCTION of its carrier-type field PLUS the predicate(s) that pin its range, so the SAME symbol gets tagged on several locations (the field line AND each constraining predicate); the reviewer grades that whole cluster together. Tag EVERY core symbol in the JSON — not only setup-world ones — so the symbol→Lean crosswalk is COMPLETE: a primitive on its carrier field + constraining predicate; a quantity the paper DEFINES by a formula on the `def` that computes it; a symbol introduced only inside a theorem statement (e.g. an existential multiplier) on the clause that pins its range. Never tag a decl that merely USES a symbol without introducing it";

/**
 * `stage2_scaffold.txt` as one call reads it. The template marks what only a scaffold made from
 * nothing needs (`{{FIRST}}`: planning the files, the escalation procedure) and what a revise
 * reads in its place (`{{REVISE}}`). Whole: the `FIRST` blocks. `slim` (a revise of a scaffold
 * that covers the plan): the `REVISE` blocks. Every other line is in both. Pure.
 */
export function scaffoldInstructions(template: string, slim: boolean): string {
  const text: string[] = [];
  let block: string | null = null;
  for (const line of template.split("\n")) {
    const open = /^\{\{(FIRST|REVISE)\}\}$/.exec(line);
    if (open) block = open[1]!;
    else if (/^\{\{\/(FIRST|REVISE)\}\}$/.test(line)) block = null;
    else if (!block || (block === "REVISE") === slim) text.push(line);
  }
  return text.join("\n");
}

export async function runStage2(args: {
  ctx: PipelineContext;
  state: StateJson;
  deps: StageDeps;
  /** Exact proof-review targets. Absent/unknown targets deliberately retain full context. */
  revisionTargets?: string[];
}): Promise<StageResult> {
  const paths = artifactPaths(args.ctx, args.state);
  // The core⊕plan structural gate only runs POST-dispatch: an absent plan.json beside a
  // surviving core.json (rewind/manual surgery) sailed through `readIfExists`'s "" and
  // burned a full high-effort scaffold call before that gate threw (audit, 2026-08-26).
  // Refuse the known-broken input before paying.
  if (existsSync(coreJsonPath(args.ctx)) && !existsSync(paths.plan)) {
    throw new Error("F2: core.json exists but plan.json is missing — restore the F1 plan (or rewind F1) before scaffolding");
  }
  const planText = await readIfExists(paths.plan);
  // The same for a plan the gate refuses on the plan and the core alone (the sync-back of a
  // refused pass, a hand edit): it is F1's to fix, and is sent back before a scaffold call is paid for.
  if (existsSync(coreJsonPath(args.ctx)) && planText.trim()) {
    const refused = blockingPostSyncPlanViolations(
      runPlanGate(parseJsonWithEscapeRepair(planText), await readFormalizationCore(coreJsonPath(args.ctx))).violations,
    );
    if (refused.length > 0) return planBackToF1(args.state, refused, "before the scaffolder ran");
  }
  const redirectBlockOf = (directive: string | null | undefined): string =>
    directive
      ? [
          "=== SCAFFOLD REDIRECT DIRECTIVE (from the proof-review loop or the orchestrator) ===",
          "",
          "Apply this directive verbatim as a top-priority constraint on top of the typed core + plan contract.",
          "Do NOT interpret it loosely; do NOT negotiate it.",
          "When the directive says the Lean OMITS / drops / weakens a hypothesis, condition, or clause",
          "that the note (spec) STATES, the faithful fix is to ADD that condition to the STATEMENT",
          "signature of the named target(s) — changing the signature here is EXPECTED and REQUIRED, not",
          "something to avoid. Resolving such a drift by editing only docstrings/comments to 'acknowledge'",
          "or 'note' the gap is FORBIDDEN: it leaves the statement unfaithful and the drift just re-flags.",
          "What you must NOT do is INVENT a hypothesis the spec does not state in order to make a target",
          "vacuously pass (gerrymandering) — only add conditions the note/spec actually states.",
          "",
          directive,
          "",
          // The proof loop's reroute budget is the one budget a redirect spends (a redirect set by
          // hand before any loop entry has no counters yet and names no attempt).
          args.state.flags.proof_loop_counters
            ? `Proof-loop scaffold attempt: ${args.state.flags.proof_loop_counters.scaffold_rounds} of ${PROOF_SCAFFOLD_MAX} max.`
            : "",
          "",
          "=== END SCAFFOLD REDIRECT DIRECTIVE ===",
          "",
        ].join("\n")
      : "";
  // REVISE / PATCH-IN-PLACE MODE (token-saver, drift-guard, proof-preserver). When
  // a prior scaffold is ALREADY on disk — an in-loop F2.5 revise OR a Stage-3
  // scaffold_redirect rewind — only the flagged/directed declarations (plus their
  // consistency ripples) need to change. Regenerating every file from the full contract is
  // slow, burns tokens, drifts on declarations that already passed, AND DISCARDS any
  // real proof bodies Stage 3 already filled (and the carry-over comments that
  // preserve them). So we hand the producer the on-disk files and tell it to Edit in
  // place. A scaffold_redirect's directive is normally localized (it names specific
  // decls); editing in place keeps every other decl — and its proof — intact.
  // A `--from-stage F2` re-entry after any later stage ran is also a revise,
  // even when it carries only a persistent f2_scaffold_directive: treating it
  // as attempt 1 would replace every working proof with `sorry`.
  // (Not used on a true attempt 1, where there is no prior scaffold to patch.)
  let reviseBlock = "";
  let reviseFilesBlock = "";
  const hasLaterStageHistory = await laterStageEverRan(args.ctx, args.state, "2");
  const patchInPlace = !!args.state.flags.scaffold_redirect || hasLaterStageHistory;
  let existingScaffoldFiles: string[] = [];
  if (patchInPlace && existsSync(paths.leanDir)) {
    existingScaffoldFiles = (await listLeanFiles(paths.leanDir)).sort();
    if (existingScaffoldFiles.length > 0) {
      reviseBlock = `${(await readPrompt(args.ctx, "stage2_head_revise.txt")).trimEnd()}\n`;
      reviseFilesBlock = [
        `On-disk files to patch, under ${paths.leanDir} (Read first, then Edit):`,
        ...existingScaffoldFiles.map((f) => `  - ${path.relative(paths.leanDir, f)}`),
        "",
      ].join("\n");
    }
  }
  // Positional pin/bookkeeping ids are renumbered by every V1.5 pass, so a carried scaffold can
  // tag ids the plan no longer has and miss ids it now delivers. Reconcile the tags against the
  // current plan BEFORE the scaffolder runs (retag / remove stale, list new) and tell it what is left.
  let tagReconciliation: TagReconciliation | null = null;
  if (existingScaffoldFiles.length > 0 && existsSync(coreJsonPath(args.ctx))) {
    const parsedPlan = PlanSchema.safeParse(planText.trim() ? parseJsonWithEscapeRepair(planText) : null);
    if (parsedPlan.success) {
      const acceptedCore = await readTypedCore(coreJsonPath(args.ctx));
      tagReconciliation = await reconcileScaffoldTags({
        leanDir: paths.leanDir,
        plan: parsedPlan.data as Plan,
        core: formalizationView(acceptedCore),
        retired: new Set(umbrellaIds(acceptedCore)),
        prevPlanPath: `${paths.plan}.prev`,
        prevCorePath: `${coreJsonPath(args.ctx)}.prev`,
      });
      if (!reconciliationIsEmpty(tagReconciliation)) {
        console.warn(`[paperformalizer] F2 revise tag reconciliation: ${describeTagReconciliation(tagReconciliation)}`);
      }
    }
  }
  const tagReconciliationDirective = tagReconciliation ? tagReconciliationBlock(tagReconciliation) : "";
  // PERSISTENT orchestrator scaffold directive (analogue of F3's `f3_filler_directive`):
  // read on EVERY scaffold/revise pass, uncapped and never self-cleared, until the
  // orchestrator clears it in `state.json`. A faithfulness/statement-shape steer.
  const persistentDirectiveBlock =
    args.state.flags.f2_scaffold_directive
      ? [
          "=== PERSISTENT ORCHESTRATOR SCAFFOLD DIRECTIVE (applies to EVERY scaffold pass) ===",
          "",
          "A top-priority, PERSISTENT faithfulness constraint from the orchestrator. Apply it verbatim,",
          "on top of the typed core + plan contract, on THIS and every subsequent scaffold/revise pass (it is NOT one-shot",
          "and NOT capped). It steers statement SHAPE / faithfulness only: NEVER invent a hypothesis the",
          "spec does not state and NEVER weaken a statement; the F2.5 review + anti-laundering gates still",
          "apply. When it says the Lean over-assumes a fact the note DERIVES (e.g. a continuity/boundedness",
          "property, an algebraic identity), the fix is to DROP that premise and derive it in-proof",
          "(`have h : … := by sorry`), not to keep it as a hypothesis.",
          "",
          args.state.flags.f2_scaffold_directive,
          "",
          "=== END PERSISTENT ORCHESTRATOR SCAFFOLD DIRECTIVE ===",
          "",
        ].join("\n")
      : "";
  const scaffoldCorePath = coreJsonPath(args.ctx);
  // What this revise is about. FLAGGED nodes: a redirect names its targets ("Declarations to edit":
  // the nodes the review flagged in this round), and it, a correction or a persistent directive
  // names nodes in its text — their records stand, their Lean is to change, so each is carried alone. CHANGED
  // nodes: the plan entries and core records that moved since the scaffold on disk was made
  // (`scaffoldBasisPath`), with what must move with them. The reconciliation's leftovers and every
  // gap in the scaffold's coverage join the changed ones, so a node the scaffold lacks is always
  // among the targets. No source of targets ⇒ the whole plan and core.
  const explicitTargets = args.revisionTargets?.length
    ? args.revisionTargets
    : revisionTargetsFromRedirect(args.state.flags.scaffold_redirect);
  let revisionContext: F2RevisionContext | null = null;
  let revisionTargets: string[] = [];
  /** One line for every node of the core (`nodeReferenceIndex`): where a scoped revise finds any of them. */
  let everyNode: string[] = [];
  /** The scaffold on disk has no readable record of the plan and core it realizes. */
  let noBasis = false;
  /** The plan changed outside its node and S-block entries since the scaffold was made (`planChangeSeeds` `other`). */
  let planWide = false;
  /** Targets the scaffold has no declaration for yet: the revise mints one, as a first scaffold does. */
  let unscaffolded: string[] = [];
  const redirect = revisionNotesFromRedirect(args.state.flags.scaffold_redirect);
  let shownRedirect = args.state.flags.scaffold_redirect;
  if (patchInPlace && existingScaffoldFiles.length > 0 && existsSync(scaffoldCorePath)) {
    try {
      const parsedPlan = PlanSchema.safeParse(parseJsonWithEscapeRepair(planText));
      if (parsedPlan.success) {
        const planNow = parsedPlan.data as Plan;
        const core = await readFormalizationCore(scaffoldCorePath);
        const basis = await readReviseBasis(scaffoldBasisPath(args.ctx.repoRoot, args.ctx.qid));
        // Without the record, what moved under an unchanged id since the scaffold was made cannot
        // be told: nothing may be scoped to the targets a redirect names, and the whole context goes.
        noBasis = !basis;
        const moved = basis ? coreChangeSeeds(basis.core, formalizationCoreContextValue(core)) : { nodes: [], symbols: [] };
        const replanned = basis ? planChangeSeeds(basis.plan, parseJsonWithEscapeRepair(planText)) : { nodes: [], envs: [], other: false };
        // The targets a redirect lists are to be edited; a node a
        // directive's text mentions beside them is context — unless the text is all there is.
        const pointed = explicitTargets;
        const mentioned = namedNodeIds(core, [args.state.flags.f2_scaffold_directive, args.state.flags.scaffold_redirect]);
        const flagged = pointed.length > 0 ? pointed : mentioned;
        const changed = [...new Set([...moved.nodes, ...replanned.nodes, ...replanned.envs])];
        // A plan field outside the entries moved (a citation, the feasibility, a top-level
        // field): which entries it reaches cannot be told from the entries, so the whole context goes.
        planWide = replanned.other;
        if (basis && !planWide && flagged.length + changed.length > 0) {
          unscaffolded = [...new Set([
            ...(tagReconciliation ? tagReconciliation.newNodes.map((n) => n.id) : []),
            ...scaffoldCoverageGaps(planNow, await parseLeanNodeTags(paths.leanDir)),
          ])];
          changed.push(...(tagReconciliation ? tagReconciliation.staleReferenced.flatMap((x) => x.referencedBy) : []), ...unscaffolded);
          revisionTargets = [...new Set([...flagged, ...changed])];
          // A flagged node whose record also moved is a changed one.
          revisionContext = buildF2RevisionContext(core, planNow, revisionTargets, { contextSymbols: moved.symbols, flagged: flagged.filter((t) => !changed.includes(t)), contextNodes: mentioned });
          if (revisionContext?.unresolved_targets.length) {
            console.warn(`[paperformalizer] F2 revise: target(s) that name no core node, symbol or S-block are left out of the local context: ${revisionContext.unresolved_targets.join(", ")}`);
          }
          if (revisionContext) {
            // Each finding goes on the record of its node; the directive keeps them only when one has no record here.
            const found = withReviewerFindings(revisionContext.core, redirect.notes);
            revisionContext.core = found.core;
            if (found.attached.length > 0 && found.attached.length === Object.keys(redirect.notes).length) {
              shownRedirect = `${redirect.rest.trimEnd()}\n\nThe reviewer's finding on each target is on its record below (\`reviewer_finding\`): apply EACH precisely — do NOT re-emit the shape it rejects.`;
            }
            everyNode = nodeReferenceIndex(core, planNow, new Set());
            await appendPipelineLog(args.ctx, {
              stage: "2",
              status: "revise-scope",
              duration_ms: 0,
              message: `F2 revise carries ${revisionContext.affected.length + revisionContext.context.length} node(s) in full (${flagged.length} flagged or named, ${changed.length - unscaffolded.length} moved since the scaffold, ${unscaffolded.length} without a declaration, ${revisionContext.context.length} as context: named in their text or in a directive) with ${revisionContext.neighbours.length} neighbour(s)${revisionContext.unresolved_targets.length > 0 ? `; target(s) naming nothing of the core or plan, left out: ${revisionContext.unresolved_targets.join(", ")}` : ""}`,
            });
          }
        }
      }
    } catch (err) {
      console.warn(
        `[paperformalizer] F2 local revision context unavailable; retaining full context: ${err instanceof Error ? err.message : String(err)}`,
      );
    }
    if (!revisionContext) {
      const why = noBasis
        ? `F2 revise has no readable record of the plan and core its scaffold was made from (${scaffoldBasisPath(args.ctx.repoRoot, args.ctx.qid)}): what moved since cannot be told; retaining full plan/core context.`
        : planWide
        ? "the plan changed outside its node and S-block entries since the scaffold was made (a citation, the feasibility or a top-level field): which declarations that reaches cannot be told from the entries; retaining full plan/core context."
        : revisionTargets.length > 0
        ? `F2 local context is unavailable for revision target(s) (${revisionTargets.join(", ")}) (no target names a core node, symbol or S-block, or the change reaches every node); retaining full plan/core context.`
          : "F2 revise names no target and nothing moved since its scaffold was made; retaining full plan/core context.";
      console.warn(`[paperformalizer] ${why}`);
      await appendPipelineLog(args.ctx, { stage: "2", status: "revise-scope", duration_ms: 0, message: `WHOLE CONTEXT — ${why}` });
    }
  }
  const promptPlanText = revisionContext ? JSON.stringify(revisionContext.plan) : planText;
  // Both directives read the WHOLE plan: a carried consumer may thread a gate the packet omits.
  const gatedHypsBlock = gatedHypsBlockFromPlan(planText);
  const undeliveredBlock = undeliveredBlockFromPlan(planText);
  const scaffoldCoreContext = revisionContext
    ? JSON.stringify(revisionContext.core)
    : await readFormalizationCoreContext(scaffoldCorePath, "F2 scaffold");
  const revisionScopeBlock = revisionContext
    ? [
        "=== LOCAL F2 REVISION CONTEXT ===",
        "The plan and typed core below carry IN FULL only the nodes this revise affects: the edit targets and",
        "what must move with a changed record. Every other node is settled, on disk, and has its line in EVERY NODE.",
        `Requested/resolved targets: ${revisionContext.resolved_targets.join(", ")}`,
        ...(revisionContext.context.length > 0
          ? [`Carried beside them as CONTEXT (a target's text or a directive names them; change one only if the fix requires it): ${revisionContext.context.join(", ")}`]
          : []),
        ...(revisionContext.unresolved_targets.length > 0
          ? [`Named, but no node of the core or S-block of the plan (find it in the Lean files): ${revisionContext.unresolved_targets.join(", ")}`]
          : []),
        `Omitted record counts: ${JSON.stringify(revisionContext.omitted_counts)}`,
        "Do not infer that an omitted object is absent from the project. If the implementation must deviate,",
        "sync back only the affected plan entries under the existing F2 contract.",
        "=== END LOCAL F2 REVISION CONTEXT ===",
        "",
      ].join("\n")
    : "";
  const revisionLookupBlock = revisionContext
    ? [
        ...(revisionContext.env_index.length > 0
          ? [
              "=== EVERY OTHER S-BLOCK (reference only) ===",
              "Unchanged, and not shown in full: `<id> | binds <symbols> | <reuse>`.",
              ...revisionContext.env_index,
              "=== END EVERY OTHER S-BLOCK ===",
              "",
            ]
          : []),
        reviseLookupBlock({
          index: revisionContext.neighbours,
          neighboursOnly: true,
          shown: revisionContext.affected.length + revisionContext.context.length,
          total: everyNode.length,
          corePath: scaffoldCorePath,
          planPath: paths.plan,
          replyField: `a \`${BEYOND_SCOPE_KEY}\` array of your output JSON`,
        }),
      ].join("\n")
    : "";
  const redirectBlock = redirectBlockOf(revisionContext ? shownRedirect : args.state.flags.scaffold_redirect);
  const template = (await readPrompt(args.ctx, "stage2_scaffold.txt")).replaceAll(
    "{{HEADER_CONTRACT}}",
    () => LEAN_HEADER_CONTRACT,
  );
  // A revise that mints no declaration reads the slim instructions; one that must scaffold a node
  // anew, or that could not be scoped, reads them whole — as a first scaffold does.
  const instructions = scaffoldInstructions(template, reviseBlock !== "" && !!revisionContext && unscaffolded.length === 0);
  // F2 implements the plan F1 already authored: per-node reuse / define-local
  // decisions, the env world, the node→Lean mapping. The reuse SEARCH happened at
  // F1; F2 does not re-run retrieval. The typed core is the ground truth for the
  // node statements/conditions the plan maps.
  const prompt = (reviseBlock
    ? [
        // A revise opens with what every revise of this run is told, in the same words — a
        // provider's prompt cache covers it — and ends with what this call is about.
        instructions,
        "",
        bookkeepingPolicyBlock(),
        "",
        reviseBlock,
        "=== THE PLAN AND THE CORE (the two JSON blocks that end this prompt) ===",
        `Formalization plan (${PLAN_CONTRACT_NOTE}.`,
        `Typed core JSON: structural ground truth for each node's statement / condition; proof/publication prose omitted. ${revisionContext ? SHARED_READINGS_NOTE : BINDING_READINGS_NOTE} ${SCOPED_SYMBOLS_NOTE}`,
        "=== END THE PLAN AND THE CORE ===",
        "",
        librarySearchPromptBlock(args.ctx),
        "",
        baseLibraryNotesBlock(args.ctx),
        "",
        baseBrief(args.ctx, args.state),
        "",
        ...(everyNode.length > 0
          ? [
              `=== EVERY NODE (${everyNode.length}; reference only) ===`,
              "One line per node of the typed core: `<id> | <what it is> | <lean_kind> <lean_name> | <target_file> | \\ref{<paper label>}`.",
              ...everyNode,
              "=== END EVERY NODE ===",
              "",
            ]
          : []),
        reviseFilesBlock,
        ...[
          undeliveredBlock,
          gatedHypsBlock,
          persistentDirectiveBlock,
          redirectBlock,
          tagReconciliationDirective,
          revisionScopeBlock,
        ].filter(Boolean),
        `Formalization plan${revisionContext ? " (localized affected-region projection)" : ""}:\n${promptPlanText}`,
        "",
        `Typed core JSON${revisionContext ? " (localized affected-region projection)" : ""}:\n${scaffoldCoreContext}`,
        "",
        revisionLookupBlock,
        "Return JSON. If blocked-missing-architecture, include missing_items exactly.",
      ]
    : [
        persistentDirectiveBlock,
        undeliveredBlock,
        gatedHypsBlock,
        redirectBlock,
        revisionScopeBlock,
        tagReconciliationDirective,
        reviseBlock,
        instructions,
        "",
        bookkeepingPolicyBlock(),
        "",
        baseBrief(args.ctx, args.state),
        "",
        librarySearchPromptBlock(args.ctx),
        "",
        baseLibraryNotesBlock(args.ctx),
        "",
        `Formalization plan (${PLAN_CONTRACT_NOTE}:\n${promptPlanText}`,
        "",
        `Typed core JSON (structural ground truth for each node's statement / condition; proof/publication prose omitted). ${BINDING_READINGS_NOTE} ${SCOPED_SYMBOLS_NOTE}\n${scaffoldCoreContext}`,
        "",
        revisionLookupBlock,
        "Return JSON. If blocked-missing-architecture, include missing_items exactly.",
      ]
  ).join("\n");
  // Rewind proof-preservation: snapshot the real proof bodies currently on disk
  // BEFORE the producer overwrites them, so we can re-attach those that survive a
  // signature match (see injectCarryoverComments after the producer runs). Empty
  // on a first scaffold or a sorry-only prior (nothing to preserve).
  const priorProofs = await snapshotPriorProofs(paths.leanDir);
  // P7 needs the actual pre-worker declaration image. The graph's passed_hash is a
  // review receipt, not a durable source snapshot (and can predate extractor fixes),
  // so it cannot distinguish an exact preserved helper from an F2 rewrite reliably.
  const preF2AnnotatedDecls = existsSync(paths.leanDir)
    ? await parseAnnotatedDecls(paths.leanDir)
    : [];
  // Snapshot the graph before granting the worker production-write access as well.
  // Reloading it only after dispatch would let a worker-created node certify its own tag.
  let preF2Graph: FormalizationGraph | undefined;
  try {
    preF2Graph = await loadGraph(graphPath(paths.formalizationDir));
  } catch {
    preF2Graph = undefined;
  }
  const priorReviseFiles = new Map<string, string>();
  if (patchInPlace && existsSync(paths.leanDir)) {
    for (const file of await listLeanFiles(paths.leanDir)) {
      priorReviseFiles.set(file, await readFile(file, "utf8"));
    }
  }
  // Snapshot the typed-theorem → meaning-bearing inline-def closure before the
  // producer edits.  This is deliberately separate from proof carry-over: a
  // theorem can keep the same signature/proof while an output structure or
  // predicate it names changes semantics and therefore requires delta review.
  let priorSemanticDefs: StatementSemanticDef[] = [];
  if (patchInPlace && existsSync(paths.leanDir)) {
    try {
      priorSemanticDefs = await findStatementSemanticDefs(paths.leanDir);
    } catch (err) {
      console.warn(
        `[paperformalizer] Stage 2 hidden-definition snapshot failed (continuing): ${err instanceof Error ? err.message : String(err)}`,
      );
    }
  }

  const plan = MODEL_PLAN.stage2;
  const stage2PromptSources = [
    "stage2_scaffold.txt",
    ...(reviseBlock ? ["stage2_head_revise.txt"] : []),
    paths.plan,
    ...(args.state.flags.scaffold_redirect ? ["flags.scaffold_redirect"] : []),
    ...(args.state.flags.f2_scaffold_directive ? ["flags.f2_scaffold_directive"] : []),
  ];
  // codex writes the .lean files directly (workspace-write) and gets lean-lsp
  // for the substrate survey, like F3. NOTE the failure-path cost: parseStageOutput
  // falls back to `parse_failed` on a non-JSON tail (NOT "completed" — a prior version
  // of this comment claimed otherwise and cost a debugging cycle), and stage2 grades
  // parse_failed as blocked — so a truncated/killed stdout envelope over a perfectly
  // good on-disk scaffold re-scaffolds cold on resume. Known accepted cost; grading
  // parse_failed by inspecting the on-disk artifacts instead is a deliberate design
  // decision left open (audit, 2026-08-26).
  const res = await dispatchAgent({
    ctx: args.ctx,
    deps: args.deps,
    stage: "2",
    label: "F2 scaffolder (codex)",
    prompt,
    promptSources: stage2PromptSources,
    model: plan.model,
    reasoningEffort: (plan.effort ?? "high") as "minimal" | "low" | "medium" | "high" | "xhigh",
    // The scaffolder builds inside its shell like the filler (`WORKER_BUILD_INACTIVITY_MS`).
    inactivityTimeoutMs: WORKER_BUILD_INACTIVITY_MS,
    leanLsp: true,
    // A redirect is invoked from the combined F2.5 loop, whose default cwd is
    // paper-local tmp/. F2 edits production Lean, so keep Codex rooted at the
    // explicit package cwd instead of trapping it in the scratch sandbox.
    productionWrite: true,
  });
  const out = res.stdout;
  const restoredDeletedFiles = await restoreDeletedReviseFiles(priorReviseFiles);
  if (restoredDeletedFiles.length > 0) {
    throw new Error(
      "F2 revise preservation gate restored file(s) deleted by the producer; refusing the non-incremental scaffold:\n  " +
        restoredDeletedFiles.join("\n  "),
    );
  }
  const parsed = parseStageOutput(out);
  // The mechanical affected set under-reached: say where, so the rule can be widened.
  const beyond = revisionContext ? beyondScopeReported(out) : [];
  if (beyond.length > 0) {
    await appendPipelineLog(args.ctx, {
      stage: "2",
      status: "revise-scope",
      duration_ms: 0,
      message: `F2 revise looked up ${beyond.length} node(s) beyond the affected set (${revisionContext!.affected.length}): ${beyond.join(", ")}`,
    });
    console.warn(`[paperformalizer] F2 revise looked up ${beyond.length} node(s) beyond the affected set: ${beyond.join(", ")}`);
  }
  if (parsed.status === "blocked-missing-architecture") {
    args.state.flags.missing_architecture = true;
    args.state.flags.missing_architecture_items = parsed.missing_items ?? [];
    // Mirror into the permanent ledger so the gap survives outside this run's state.
    try {
      const items = parsed.missing_items ?? [];
      if (items.length > 0) {
        recordMissingArchitecture(missingArchitectureLedgerPath(args.ctx.repoRoot, args.ctx.qid), {
          qid: args.ctx.qid,
          source: "F2 missing-architecture",
          date: new Date().toISOString().slice(0, 10),
          items: items.map((m) => ({
            kind: m.kind,
            description: [
              `${m.name_suggestion} — ${m.purpose}`,
              m.suggested_location ? `[loc: ${m.suggested_location}]` : "",
            ].filter(Boolean).join(" "),
            effort: undefined,
          })),
        });
      }
    } catch (err) {
      console.warn(`[paperformalizer] missing-architecture ledger write failed: ${err instanceof Error ? err.message : String(err)}`);
    }
    return {
      stage: "2",
      status: "blocked",
      advance: false,
      message: parsed.message ?? "MISSING ARCHITECTURE BLOCKED",
    };
  }
  if (parsed.status !== "completed") {
    // why: F2 must not run the completed state mutation path unless the worker completed.
    return {
      stage: "2",
      status: "blocked",
      advance: false,
      message: parsed.message ?? "F2 did not complete",
    };
  }

  // Rewind proof-preservation: re-attach prior proofs for new `sorry` decls whose
  // signature is unchanged. In revise mode, reactivate them immediately so F2
  // cannot return with a working proof downgraded to `sorry`; cold mode retains
  // the historical inert-comment handoff to F2.5/F3. No-op unless real prior
  // proofs existed. Best-effort: a preservation failure must not hide the
  // producer result, but it is surfaced loudly.
  if (priorProofs.size > 0) {
    try {
      const carried = await injectCarryoverComments(paths.leanDir, priorProofs);
      if (carried.count > 0) {
        if (patchInPlace) {
          const restored = await restoreCarryoverProofs(paths.leanDir);
          console.warn(
            `[paperformalizer] Stage 2 revise proof preservation: restored ${restored.count} active prior proof(s) ` +
              `for signature-unchanged decl(s) (${restored.names.join(", ")}); only changed/new obligations may remain sorry.`,
          );
        } else {
          console.warn(
            `[paperformalizer] Stage 2 proof carry-over: re-attached ${carried.count} prior proof(s) as Stage-3 anchors ` +
              `for signature-unchanged decl(s) (${carried.names.join(", ")}) — rewind did not discard them.`,
          );
        }
      }
    } catch (err) {
      console.warn(
        `[paperformalizer] Stage 2 proof carry-over failed (continuing): ${err instanceof Error ? err.message : String(err)}`,
      );
    }
  }

  const duplicateNodeAnchors = await findDuplicateLeanNodeAnchors(paths.leanDir);
  if (duplicateNodeAnchors.length > 0) {
    throw new Error(
      "F2 duplicate @node gate failed; every graph node must have exactly one canonical primary declaration:\n" +
        duplicateNodeAnchors
          .map((d) => `  ${d.id}: ${d.locations.join(", ")}`)
          .join("\n"),
    );
  }

  // Sync-back check. The worker may have updated plan.json on
  // deviation (a planned reuse that did not type-fit; an atom better as a named def);
  // re-run the plan gate against the typed core, now also checking the emitted Lean's
  // @node/@env tags cover the plan one-to-one (P7). Every structural violation blocks the
  // scaffold EXCEPT P5 (reuse existence) and P6 (module resolution) — reuse lookup and
  // module resolution are settled in the later typed phases, so they stay advisory here.
  // An F run has both inputs (the pipeline refuses F entry without the core; F2 refuses a
  // core without its plan above), so a missing one here is a fault, never a legacy case.
  {
    const corePath = coreJsonPath(args.ctx);
    try {
      if (!existsSync(corePath) || !existsSync(paths.plan)) {
        throw new Error(
          `F2 structural plan gate inputs incomplete (core=${existsSync(corePath)}, plan=${existsSync(paths.plan)})`,
        );
      }
      {
        const core = await readFormalizationCore(corePath);
        const rawPlanObj = parseJsonWithEscapeRepair(await readFile(paths.plan, "utf8"));
        const canonicalPlan = canonicalizeCitedPlanAfterF2(rawPlanObj, core);
        const planObj = canonicalPlan.plan;
        if (canonicalPlan.changed) {
          await writeFile(paths.plan, JSON.stringify(planObj, null, 2) + "\n", "utf8");
          console.warn(
            "[paperformalizer] F2 post-sync canonicalized optional gate keys and restored cited provenance from the typed core.",
          );
        }
        const leanTags = await parseLeanNodeTags(paths.leanDir);
        const leanDeclNames = new Set((await parseLeanDecls(paths.leanDir, { includeLemmas: true })).map((decl) => decl.name));
        const annotatedDecls = await parseAnnotatedDecls(paths.leanDir);
        // `preF2Graph` and `preF2AnnotatedDecls` were snapshotted before dispatch.
        // A run's first F2 pass has neither, so the exemption simply stays off then.
        // Index sources ∪ the toolkit ledger ∪ declarations scanned from the toolkit sources.
        const knownDecls = knownDeclsForContext(args.ctx);
        if (!knownDecls) {
          console.warn(
            "[paperformalizer] no library index loaded — the P5 reuse-existence check is SKIPPED this pass; hallucinated reuse decls will surface only at compile.",
          );
        }
        const gate = runPlanGate(planObj, core, {
          knownDecls: knownDecls?.names,
          ownedDeclPrefixes: knownDecls?.ownedPrefixes,
          leanTags,
          leanDeclNames,
          preF2Graph,
          annotatedDecls,
          proofsNotDue: true,
          preF2AnnotatedDecls,
          tagReconciliation: tagReconciliation ?? undefined,
        });
        logPlanGateNotes(gate.notes);
        // The plan passed these rules before the scaffolder ran: its sync-back broke them.
        const planOnly = gate.ok ? [] : blockingPostSyncPlanViolations(runPlanGate(planObj, core).violations);
        if (planOnly.length > 0) return planBackToF1(args.state, planOnly, "the scaffolder's sync-back left");
        args.state.flags.plan_rewind_violations = null;
        if (!gate.ok) {
          const blockingViolations = blockingPostSyncPlanViolations(gate.violations);
          if (blockingViolations.length > 0) {
            const reconciled = tagReconciliation && !reconciliationIsEmpty(tagReconciliation)
              && blockingViolations.some((v) => v.code === "P7")
              ? `\n  (pre-scaffold tag reconciliation: ${describeTagReconciliation(tagReconciliation)})`
              : "";
            throw new Error(
              `F2 structural plan gate refused the scaffold:\n  ` +
                blockingViolations.map((v) => `${v.code} @ ${v.where}: ${v.message}`).join("\n  ") +
                reconciled,
            );
          }
          console.warn(
            `[paperformalizer] F2 post-sync plan_gate: ${gate.violations.length} violation(s)\n  ` +
              gate.violations.slice(0, 12).map((v) => `${v.code} @ ${v.where}: ${v.message}`).join("\n  "),
          );
        }
      }
    } catch (err) {
      if (err instanceof Error && err.message.startsWith("F2 structural plan gate refused")) throw err;
      // Reaching here means a real execution failure (or a missing input) — fail closed.
      throw new Error(
        `F2 structural plan gate failed to execute: ${err instanceof Error ? err.message : String(err)}`,
      );
    }
  }
  // Graph link (best-effort, advisory): seed `-- @node:` annotations + extract the
  // Lean side into the formalization graph.
  let hiddenChangedTargets: string[] = [];
  if (patchInPlace) {
    try {
      hiddenChangedTargets = hiddenDefinitionChangeTargets(
        priorSemanticDefs,
        await findStatementSemanticDefs(paths.leanDir),
      );
      if (hiddenChangedTargets.length > 0) {
        console.warn(
          `[paperformalizer] Stage 2 revise semantic invalidation: reset cached F2.5 review for ` +
            `${hiddenChangedTargets.join(", ")} (meaning-bearing inline dependency changed).`,
        );
      }
    } catch (err) {
      console.warn(
        `[paperformalizer] Stage 2 hidden-definition comparison failed (continuing): ${err instanceof Error ? err.message : String(err)}`,
      );
    }
  }
  const invalidateReviewNodeIds = [...new Set(hiddenChangedTargets)].sort();
  const graphLink = await linkGraphFromStage2({
    qid: args.ctx.qid,
    formalizationDir: paths.formalizationDir,
    leanDir: paths.leanDir,
    invalidateReviewNodeIds,
  });
  if (graphLink.graph) {
    const errs = graphLink.findings.filter((f) => f.severity === "error").length;
    console.warn(`[graph] F2 linked ${graphLink.graph.nodes.length} nodes; ${errs} advisory invariant error(s)`);
  }
  // Do not trust the producer's `compiled sorry-only` self-report.  A revised
  // helper can be outside the producer's narrow target even though it is in the
  // run import closure; advancing to F2.5 with a red tree then lets a stale
  // review cache hide the failure.  Production runs have a lakefile at the repo
  // root; isolated unit-test fixtures do not and deliberately skip this gate.
  if (existsSync(path.join(args.ctx.repoRoot, "lakefile.toml"))) {
    const build = await buildRunModules(args.ctx.repoRoot, paths.leanDir);
    if (!build.ok) {
      throw new Error(`F2 run compile gate failed; refusing to advance to F2.5:\n${build.errors}`);
    }
    console.warn("[paperformalizer] F2 run compile gate passed");
  }
  // The redirect is honoured only now, once the plan gate and the compile gate have passed:
  // cleared before them, a gate failure left no pending directive for the resume to re-apply,
  // the reviewer re-flagged the same drift and the node took a strike for an edit never retried.
  args.state.flags.scaffold_redirect = null;
  // F2 rewrites statements (a changed one loses its proof): the proof loop's progress measure starts
  // over from the tree this pass leaves, whichever route ran it.
  if (args.state.flags.proof_loop_counters) args.state.flags.proof_loop_counters.progress_best = undefined;
  // The plan and core this scaffold realizes: the next re-scaffold covers what moved since.
  try {
    await writeReviseBasis(scaffoldBasisPath(args.ctx.repoRoot, args.ctx.qid), {
      plan: parseJsonWithEscapeRepair(await readFile(paths.plan, "utf8")),
      core: formalizationCoreContextValue(await readFormalizationCore(scaffoldCorePath)),
    });
  } catch (err) {
    console.warn(`[paperformalizer] F2 scaffold basis not recorded (the next revise keeps full context): ${err instanceof Error ? err.message : String(err)}`);
  }
  return {
    stage: "2",
    status: "completed",
    message: parsed.message ?? "Stage 2 Lean scaffold completed",
  };
}
