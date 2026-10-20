import { LEAN_HEADER_CONTRACT } from "./lean_header_contract.js";
import { readFile } from "node:fs/promises";
import { MODELS } from "../models.js";
import { existsSync } from "node:fs";
import { addAssumption, addEdge, markUnreviewed } from "../graph/mutate.js";
import { nodeIdToObjId, objIdToNodeId } from "../graph/from_note.js";
import { reviewerObjId } from "../graph/skeleton.js";
import { untaggedSorryDecls } from "../graph/extractor.js";
import { isUndeliveredNode, type AssumptionClass, type FormalizationGraph } from "../graph/types.js";
import type { CodexRunInput } from "../shared/codex.js";
import type { ToolkitConfig } from "../toolkit/config.js";
import { parseJsonWithEscapeRepair } from "../shared/codex_json.js";
import { promptPath } from "../paths.js";
import { WORKER_BUILD_INACTIVITY_MS, dispatchAgent } from "../framework/agent_dispatch.js";
import { librarySearchPromptBlock } from "../toolkit/search.js";
import { baseLibraryNotesBlock } from "../toolkit/prompt_notes.js";
import { readFormalizationCore } from "../core/core_io.js";
import { balancedJsonObjects } from "./reviewer_verdicts.js";

/** The proof-filler agent's escalation when it hits a wall it cannot resolve.
 *  `unparsable-output` is synthesized by the DISPATCHER (not the model) when the filler's
 *  stdout carries no parseable FillerOutput — a mechanical fault that must surface as a
 *  resumable checkpoint, not crash the run (the loop has no stage-level catch). */
export interface FillerEscalation {
  kind: "statement-wrong" | "needs-substrate" | "ambiguous-spec" | "unparsable-output";
  reason: string;
  node?: string;
}

interface FillerAddedAssumption {
  id: string;
  statement: string;
  classification: string; // faithful[-refinement] | regularity[-bookkeeping] | substrate-gate
  attached_to: string; // obj_id of the node whose proof needs it
  anchor?: string;
}

interface FillerOutput {
  added_assumptions?: FillerAddedAssumption[];
  escalate?: FillerEscalation | null;
  summary?: string;
}

export interface FillerResult {
  graph: FormalizationGraph;
  escalate: FillerEscalation | null;
  summary: string;
}

/**
 * `content-gate` is the LAUNDERING tag: an added premise standing in for a result the note DERIVES.
 * It must never be recorded as `substrate-gate` (accepted, dischargeable debt) — that silently turns
 * a reject into a bankable disclosure. Callers escalate instead of persisting it.
 */
export function isContentGateTag(tag: string): boolean {
  return tag.trim().toLowerCase().startsWith("content");
}

/**
 * Map the filler's `classification` tag to an {@link AssumptionClass}.
 *
 * Precondition: `!isContentGateTag(tag)` — a content-gate has no honest {@link AssumptionClass}, so
 * it is filtered out upstream and escalated rather than mapped.
 *
 * An unrecognized tag falls back to `substrate-gate`, the CONSERVATIVE choice: a substrate-gate is
 * owed a build, and the report gives the result as conditional on it. Silently downgrading an unknown tag
 * to `regularity-bookkeeping` would be the unsafe direction.
 */
export function toAssumptionClass(tag: string): AssumptionClass {
  const t = tag.trim().toLowerCase();
  if (t.startsWith("faithful")) return "faithful-refinement";
  if (t.startsWith("regularity")) return "regularity-bookkeeping";
  return "substrate-gate";
}

const isFillerShape = (o: unknown): o is FillerOutput => {
  if (!o || typeof o !== "object" || Array.isArray(o)) return false;
  const r = o as Record<string, unknown>;
  // why: copied examples/prose objects are unsafe unless they have the filler result shape.
  if (!("added_assumptions" in r) && !("escalate" in r) && !("summary" in r)) return false;
  if ("added_assumptions" in r && r.added_assumptions != null && !Array.isArray(r.added_assumptions)) return false;
  if ("summary" in r && r.summary != null && typeof r.summary !== "string") return false;
  return true;
};

/** Tolerant JSON parse: balanced, string-aware extraction from fenced/prose-wrapped output. */
function parseFillerOutput(stdout: string): FillerOutput {
  for (const cand of balancedJsonObjects(stdout)) {
    try {
      // Escape-repair parse, NOT bare JSON.parse: a filler note carrying LaTeX
      // (`\(`, `\mathcal`) is invalid JSON, and discarding the reply lost its
      // disclosed `added_assumptions` — including substrate-gate disclosures —
      // while the Lean edits stayed on disk.
      const o = parseJsonWithEscapeRepair(cand);
      if (isFillerShape(o)) return o;
    } catch {
      // try the next balanced object
    }
  }
  throw new Error("filler: no parseable FillerOutput JSON object in output");
}

/** The reply contract the filler is dispatched under (`CodexRunInput.outputSchema`, strict
 *  mode): the prompt's OUTPUT JSON, with optional fields nullable. */
const str = { type: "string" } as const;
const nullable = (schema: Record<string, unknown>) => ({ anyOf: [{ type: "null" }, schema] });
export const FILLER_OUTPUT_SCHEMA: Record<string, unknown> = {
  type: "object",
  additionalProperties: false,
  required: ["added_assumptions", "escalate", "summary"],
  properties: {
    added_assumptions: {
      type: "array",
      items: {
        type: "object", additionalProperties: false,
        // (the three classes the prompt offers; the graph records every filler premise at tier 2)
        required: ["id", "statement", "classification", "attached_to", "anchor"],
        properties: {
          id: str, statement: str,
          classification: { enum: ["faithful-refinement", "regularity-bookkeeping", "substrate-gate"] },
          attached_to: str, anchor: nullable(str),
        },
      },
    },
    escalate: nullable({
      type: "object", additionalProperties: false, required: ["kind", "reason", "node"],
      properties: { kind: { enum: ["statement-wrong", "needs-substrate", "ambiguous-spec"] }, reason: str, node: nullable(str) },
    }),
    summary: str,
  },
};

/** A schema-constrained reply parsed strictly, else the prose-tolerant extractor, logged. */
function parseFillerReply(stdout: string): FillerOutput {
  try {
    const o = parseJsonWithEscapeRepair(stdout.trim());
    if (isFillerShape(o)) return o;
  } catch {
    /* fall through to the tolerant extractor */
  }
  console.warn("[f3] filler: schema-constrained reply needed the heuristic parser");
  return parseFillerOutput(stdout);
}

/** Open nodes the filler is pointed at this round, leaf-first (a node none of whose own
 *  theorem/lemma dependencies is still open comes first, so its users unblock), then graph order. */
const FOCUS_PER_ROUND = 3;
const ONE_LINE = 240;
const oneLine = (s: string): string => {
  const t = s.replace(/\s+/g, " ").trim();
  return t.length > ONE_LINE ? t.slice(0, ONE_LINE) + "…" : t;
};

/**
 * A compact context string for the filler: the open nodes (with their frozen statements to
 * PRESERVE) and the environment. The FOCUS nodes of this round carry their full statement and,
 * when the typed core has one, their proof roadmap (`proof_tex`, by node id); every other open
 * node is one line. The prompt used to list every open node's full LaTeX statement and every
 * setup block in full, round after round — tens of KB the filler never acted on.
 */
export function renderFillerContext(
  graph: FormalizationGraph,
  untagged: { file: string; line: number; declName: string }[] = [],
  proofTexById: ReadonlyMap<string, string> = new Map(),
): string {
  const open = graph.nodes.filter(
    (n) => (n.kind === "theorem" || n.kind === "lemma") && !isUndeliveredNode(n) && n.proof.state !== "complete",
  );
  const openIds = new Set(open.map((n) => n.id));
  const usesOf = (id: string) => [...new Set(graph.edges
    .filter((e) => (e.kind === "statement-uses" || e.kind === "proof-uses") && e.from === id)
    .map((e) => e.to))];
  const openDeps = (id: string) => usesOf(id).filter((d) => openIds.has(d)).length;
  const ranked = open.map((n, i) => ({ n, i, deps: openDeps(n.id) })).sort((a, b) => a.deps - b.deps || a.i - b.i).map((x) => x.n);
  const focus = ranked.slice(0, FOCUS_PER_ROUND);
  const rest = ranked.slice(FOCUS_PER_ROUND);
  const head = (n: FormalizationGraph["nodes"][number]) =>
    `- ${n.id} (${n.kind}, ${n.lean.decl_name ?? "(unlinked)"}, ${n.proof.state})${n.provenance === "from-note" ? " [FROZEN STATEMENT — do not weaken]" : ""}`;
  const lines: string[] = ["OPEN WORK — FOCUS THIS ROUND (leaf-first; full statement, and the proof roadmap of the spec of record where it has one):"];
  for (const n of focus) {
    const uses = usesOf(n.id);
    lines.push(`${head(n)}: ${n.nl.statement}${uses.length ? `  uses: ${uses.join(", ")}` : ""}`);
    const roadmap = proofTexById.get(n.id) ?? (n.obj_id ? proofTexById.get(n.obj_id) : undefined);
    if (roadmap?.trim()) lines.push(`  PROOF ROADMAP (proof_tex): ${roadmap.trim()}`);
  }
  if (rest.length) {
    lines.push("", "OTHER OPEN WORK (by id; take one up only when every focus node is blocked — its statement is its Lean declaration):");
    for (const n of rest) lines.push(head(n));
  }
  if (untagged.length) {
    lines.push("", "UNTAGGED DECLARATIONS STILL HOLDING `sorry` (open work too: a result built on one is not proved until it is closed; the run cannot finish while any remains):");
    for (const d of untagged) lines.push(`- ${d.declName} (${d.file}:${d.line})`);
  }
  const setups = graph.nodes.filter((n) => n.kind === "setup");
  if (setups.length) {
    lines.push("", "ENVIRONMENT (one line each; the Lean `@env` declaration is the full world):");
    for (const s of setups) lines.push(`- ${s.id}: ${oneLine(s.nl.statement)}${s.setup?.required_modules.length ? `  (modules: ${s.setup.required_modules.join(", ")})` : ""}`);
  }
  return lines.join("\n");
}

/** `proof_tex` of every core statement, by id (empty when the core cannot be read: the
 *  roadmap is context, never a gate). */
async function proofRoadmaps(corePath: string | undefined): Promise<Map<string, string>> {
  const out = new Map<string, string>();
  if (!corePath) return out;
  try {
    for (const s of (await readFormalizationCore(corePath)).statements) {
      if (typeof s.proof_tex === "string" && s.proof_tex.trim()) out.set(s.id, s.proof_tex);
    }
  } catch {
    /* no readable core: focus nodes carry their statement only */
  }
  return out;
}

/**
 * One proof-filler session: dispatch the Codex filler over the graph, then record
 * any assumptions it added (writing them into Lean is the filler's job) onto the
 * graph — minting an `agent-introduced` assumption node + a `proof-uses` edge to the
 * node it serves, and flipping that parent to `unreviewed` so the reviewer re-checks
 * it on the dirty frontier. Returns the updated graph + any escalation.
 *
 * Missing-primitive policy (NOT "always escalate"): if the filler CAN build the
 * needed helper here — a project-specific lemma in the paper's Lean subtree, or by
 * composing existing base-library / toolkit / Mathlib lemmas — it BUILDS it inline as an
 * `agent-introduced` node and the reviewer judges it next iteration (the normal path). It
 * leaves `sorry -- BLOCKER: needs-substrate(<primitive>)` and escalates `needs-substrate`
 * ONLY for substrate it cannot build here: library-scale / toolkit-bound (outside its edit
 * scope) or genuinely open math, where the orchestrator builds it as a named toolkit lemma
 * and independently verifies it 0-sorry/axiom-clean before dependents lean on it
 * (invariant #10). It must SEARCH + try composing first.
 * In all cases it MUST NOT assume the crux (no crux as a hypothesis, no vacuous stub).
 */
export async function runFiller(args: {
  ctx: { repoRoot: string; qid: string; toolkit?: ToolkitConfig };
  deps: { runCodex: (o: CodexRunInput) => Promise<{ stdout: string; stderr: string }> };
  graph: FormalizationGraph;
  leanDir: string;
  corePath?: string;
  promptPath?: string;
  /** Load-bearing orchestrator PROOF hint (lemma names / tactic strategy / Mathlib API),
   *  injected verbatim near the top of the prompt. A proof hint ONLY — must not be read as
   *  license to weaken a statement, add an unsanctioned hypothesis, or axiomatize a goal. */
  directive?: string | null;
  /** Informational memory of earlier filler sessions this run (their one-line summaries); rendered
   *  as context, deliberately OUTSIDE the orchestrator-directive fence so it carries no authority. */
  priorSessions?: string | null;
}): Promise<FillerResult> {
  // Resolve via the shared promptPath helper, never a hardcoded tools-relative prefix (which
  // double-nests and leaves basePrompt empty).
  const promptFile = args.promptPath ?? promptPath(args.ctx.repoRoot, "proof_filler.txt");
  // Fail CLOSED, like the reviewer. The base prompt carries the no-axiom, disclosure and
  // frozen-statement contract; degrading it to "" would still dispatch a write-capable agent,
  // just one that was never told the rules.
  if (!existsSync(promptFile)) throw new Error(`proof-filler prompt missing: ${promptFile}`);
  const basePrompt = (await readFile(promptFile, "utf8")).replaceAll(
    "{{HEADER_CONTRACT}}",
    () => LEAN_HEADER_CONTRACT,
  );
  if (!basePrompt.trim()) throw new Error(`proof-filler prompt is empty: ${promptFile}`);
  const directiveBlock =
    args.directive && args.directive.trim().length > 0
      ? [
          "=== ORCHESTRATOR PROOF DIRECTIVE (load-bearing — apply as a top-priority PROOF hint) ===",
          args.directive.trim(),
          "This is a PROOF hint only (lemma names / tactic strategy / Mathlib API). It does NOT",
          "authorize weakening a frozen statement, adding an unsanctioned hypothesis, or axiomatizing",
          "a goal — those are still rejected downstream. Prove the stated goals as written.",
          "=== END ORCHESTRATOR PROOF DIRECTIVE ===",
          "",
        ].join("\n")
      : "";
  const priorSessionsBlock =
    args.priorSessions && args.priorSessions.trim().length > 0 ? args.priorSessions.trim() + "\n" : "";
  // The first line names the LOGICAL stage (the loop runs every fill in the F2.5 slot): the
  // transcript and token ledgers key on it. The statements and the proof roadmaps of this
  // round's focus nodes are ON THE PAGE (from the typed core, by node id); the core itself is
  // not pointed at — a filler told where it lives read it whole, every round.
  const prompt = [
    "=== F3 PROOF FILL ===",
    basePrompt,
    "",
    directiveBlock,
    priorSessionsBlock,
    renderFillerContext(args.graph, await untaggedSorryDecls(args.leanDir), await proofRoadmaps(args.corePath)),
    "",
    librarySearchPromptBlock(args.ctx),
    "",
    baseLibraryNotesBlock(args.ctx),
    "",
    "SOURCES — the statements and proof roadmaps you need are on this page; do not read the typed core",
    "or the plan. Open a Lean file to edit it, to read the declaration you are proving, or to unfold a",
    "definition it uses; search the libraries by concept before building anything.",
    `Lean source tree: ${args.leanDir}`,
    "Return ONLY the JSON object specified in the prompt.",
  ].filter(Boolean).join("\n");

  const out = await dispatchAgent({
    ctx: args.ctx,
    deps: args.deps,
    stage: "3",
    label: "F3 proof filler",
    prompt,
    promptSources: [promptFile, ...(args.corePath ? [args.corePath] : []), args.leanDir],
    model: MODELS.codexKernel,
    reasoningEffort: "medium",
    // The filler builds the paper's modules inside its own shell (`WORKER_BUILD_INACTIVITY_MS`).
    inactivityTimeoutMs: WORKER_BUILD_INACTIVITY_MS,
    // F3 writes proof bodies in the run's paper modules; scratch probes
    // still belong in tmp/, as stated in the prompt, but the workspace-write
    // root itself must be the package so those edits are permitted.
    productionWrite: true,
    // The reply is one JSON object of the prompt's OUTPUT shape by construction.
    outputSchema: FILLER_OUTPUT_SCHEMA,
  });
  // Mirror the reviewer's parse boundary (runUnit → `unparsable-output`): a throw here would
  // unwind through the proof-review loop — which has no stage-level catch — and abort the whole
  // run on one flaky model reply. Escalate as a structured, resumable outcome instead; the raw
  // stdout is already preserved in the agent logs by the dispatch wrapper.
  let parsed: FillerOutput;
  try {
    parsed = parseFillerReply(out.stdout);
  } catch (err) {
    return {
      graph: args.graph,
      escalate: {
        kind: "unparsable-output",
        reason:
          `filler output failed to parse (${err instanceof Error ? err.message : String(err)}); ` +
          `any Lean edits it made are on disk and will be re-reviewed on resume — raw output is in the agent logs`,
      },
      summary: "",
    };
  }

  let graph = args.graph;

  // A `content-gate` tag is the filler admitting it assumed the crux. Escalate as a STRUCTURED
  // result (`statement-wrong` → `fix-source`, a human decides) rather than throwing: the loop has no
  // stage-level catch, so a throw would unwind past `saveState`, leave `stage_completed` unadvanced,
  // and make `--resume` re-enter the same filler — a crash loop on a deterministic content-gate.
  // Nothing is persisted: the offending premise is never added to the graph.
  const contentGates = (parsed.added_assumptions ?? []).filter((a) => isContentGateTag(a.classification));
  if (contentGates.length > 0) {
    return {
      graph: args.graph,
      escalate: {
        kind: "statement-wrong",
        reason:
          `filler classified ${contentGates.length} added premise(s) as content-gate (laundering the ` +
          `crux — a result the note DERIVES, assumed instead of proven): ` +
          contentGates.map((a) => `${a.id} on ${a.attached_to}`).join("; "),
        node: contentGates[0].attached_to,
      },
      summary: parsed.summary ?? "",
    };
  }

  for (const a of parsed.added_assumptions ?? []) {
    // why: core-built graph ids can be semantic (`thm:*`) while the filler prompt names the paper obj_id
    // alias (`T-1`). Resolve in PRIORITY ORDER — an exact node-id match must win over an earlier node
    // whose obj_id (or derived alias) happens to match, else the hypothesis attaches to the wrong node.
    const attached =
      graph.nodes.find((n) => n.id === a.attached_to) ??
      graph.nodes.find((n) => n.obj_id === a.attached_to) ??
      graph.nodes.find((n) => nodeIdToObjId(n.id) === a.attached_to);
    const parentId = attached?.id ?? objIdToNodeId(a.attached_to);
    if (!graph.nodes.some((n) => n.id === parentId)) {
      // Unknown parent: the hypothesis is already in the LEAN (writing it is the filler's job),
      // but its graph node — including a substrate-gate disclosure — cannot be recorded. Never
      // drop that silently (the "graded N, applied M" class): surface it loudly for the
      // orchestrator; the parent's changed signature still lands on the dirty review frontier.
      console.warn(
        `[f3] filler added assumption '${a.id}' (${a.classification}) attached to unknown node ` +
          `'${a.attached_to}' — NOT recorded on the graph; verify the disclosure is not lost.`,
      );
      continue;
    }
    // Filler ids often use the legacy short form (`a1`).  That spelling has a display alias
    // (`A-1`) which may already belong to a frozen from-note assumption whose semantic graph id is
    // different (`ass:overlap`).  Allocate over the COMPLETE reviewer-identity namespace, not only
    // exact graph ids.  Reuse is allowed only when the existing node is the same disclosed premise
    // already attached to the same parent; otherwise choose an injective parent-scoped semantic id
    // and collision-check that generated id too.  This prevents both alias theft and silent premise/
    // edge loss when two fillers independently choose the same short id.
    const owners = (candidate: string) => {
      const candidateIdentities = new Set([candidate, nodeIdToObjId(candidate)]);
      return graph.nodes.filter((n) =>
        [n.id, n.obj_id, nodeIdToObjId(n.id), reviewerObjId(n)]
          .some((identity) => identity != null && candidateIdentities.has(identity)));
    };
    const samePremise = (node: FormalizationGraph["nodes"][number]) =>
      node.kind === "assumption" &&
      node.nl.statement === a.statement &&
      node.nl.tex_anchor === (a.anchor ?? "") &&
      node.assumption?.tier === 2 &&
      // (not its class: the reviewer's class replaces the filler's on the node, and the premise
      // stated again under the filler's own class is the same hypothesis of the same proof)
      graph.edges.some((e) => e.kind === "proof-uses" && e.from === parentId && e.to === node.id);
    const choose = (candidate: string): string | null => {
      const found = owners(candidate);
      if (found.length === 0) return candidate;
      if (found.length === 1 && samePremise(found[0])) return found[0].id;
      return null;
    };
    // Never let a model-chosen raw id enter the reviewer namespace.  The graph can gain hidden AUX
    // nodes during the post-fill refresh and synthetic `sym:*` rows come from the typed core rather
    // than today's graph, so a pre-refresh blacklist can never be complete.  A semantic `ass:filler:`
    // id is stable across resumes and cannot acquire legacy/AUX/symbol projection semantics later.
    const encodedParent = `${parentId.length}:${parentId}`;
    const encodedRequested = `${a.id.length}:${a.id}`;
    const base = `ass:filler:${encodedParent}:${encodedRequested}`;
    let assumptionId = choose(base);
    for (let suffix = 1; assumptionId == null; suffix += 1) assumptionId = choose(`${base}:${suffix}`);
    if (!graph.nodes.some((n) => n.id === assumptionId)) {
      graph = addAssumption(graph, {
        node: parentId,
        id: assumptionId,
        statement: a.statement,
        tier: 2,
        classification: toAssumptionClass(a.classification),
        anchor: a.anchor ?? "",
        provenance: "agent-introduced",
      });
    } else {
      // Semantic reuse still must carry the dependency requested in THIS filler output.
      graph = addEdge(graph, { kind: "proof-uses", from: parentId, to: assumptionId, source: "declared" });
    }
    graph = markUnreviewed(graph, parentId); // the parent gained a hypothesis → re-review
  }

  return { graph, escalate: parsed.escalate ?? null, summary: parsed.summary ?? "" };
}
