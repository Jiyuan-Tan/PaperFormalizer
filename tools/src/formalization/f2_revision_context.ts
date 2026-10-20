import type { Core } from "../core/schema.js";
import { objIdToNodeId } from "../graph/from_note.js";
import { applicableSettings, symbolEntryShown, symbolsUsedByNode } from "../verify/core_graph.js";
import type { Plan } from "./plan/schema.js";
import { formalizationCoreContextValue, shareBindingReadings } from "./core_context.js";
import { nodeNeighbours, nodeReferenceIndex, referencedNodeIds, reviseAffectedNodeIds } from "./revise_scope.js";

export const F2_REVISION_TARGETS_HEADER =
  "Declarations to edit (one obj_id per line, verbatim):";

/** Recover only the exact target block written by the proof-review dispatcher. */
export function revisionTargetsFromRedirect(redirect: string | null | undefined): string[] {
  if (!redirect) return [];
  const lines = redirect.split(/\r?\n/);
  const start = lines.lastIndexOf(F2_REVISION_TARGETS_HEADER);
  if (start < 0) return [];
  const targets: string[] = [];
  for (const line of lines.slice(start + 1)) {
    if (!line.startsWith("- ")) break;
    const target = line.slice(2).trim();
    if (target) targets.push(target);
  }
  return [...new Set(targets)];
}

/** Opens the per-target findings of a redirect the proof loop writes: one `• <obj_id>: <finding>` each. */
export const F2_REVISION_NOTES_HEADER =
  "Reviewer's specific per-target diagnosis (apply EACH precisely — do NOT re-emit the same shape the reviewer just rejected):";

/**
 * A redirect's per-target findings, by target, and the redirect without them (`rest`) — a revise
 * shows each finding on the record of its node. A redirect without the block is `rest` whole.
 */
export function revisionNotesFromRedirect(redirect: string | null | undefined): { notes: Record<string, string>; rest: string } {
  const lines = (redirect ?? "").split(/\r?\n/);
  const start = lines.lastIndexOf(F2_REVISION_NOTES_HEADER);
  if (start < 0) return { notes: {}, rest: redirect ?? "" };
  const targets = lines.lastIndexOf(F2_REVISION_TARGETS_HEADER);
  const end = targets > start ? targets : lines.length;
  const notes: Record<string, string> = {};
  let current: string | null = null;
  for (const line of lines.slice(start + 1, end)) {
    const item = /^• (.+?)(?:: (.*))?$/.exec(line);
    if (item) {
      current = item[1]!;
      if (item[2] !== undefined) notes[current] = item[2];
    } else if (current && current in notes) notes[current] += `\n${line}`;
  }
  for (const id of Object.keys(notes)) notes[id] = notes[id]!.trim();
  return { notes, rest: [...lines.slice(0, start), ...lines.slice(end)].join("\n") };
}

/**
 * A packet's core with each finding on the record it is about, as `reviewer_finding` right after
 * the record's id (a node by its id, a symbol as `sym:<name>`), and the targets so served.
 */
export function withReviewerFindings(core: Record<string, unknown>, notes: Record<string, string>): { core: Record<string, unknown>; attached: string[] } {
  const attached: string[] = [];
  const put = (list: unknown, target: (record: Record<string, unknown>) => string): unknown =>
    Array.isArray(list)
      ? (list as Array<Record<string, unknown>>).map((record) => {
          const note = notes[target(record)];
          if (note === undefined) return record;
          attached.push(target(record));
          const [[key, value], ...rest] = Object.entries(record) as [[string, unknown], ...Array<[string, unknown]>];
          return { [key]: value, reviewer_finding: note, ...Object.fromEntries(rest) };
        })
      : list;
  const out = {
    ...core,
    symbols: put(core.symbols, (s) => `sym:${String(s.name)}`),
    assumptions: put(core.assumptions, (n) => String(n.id)),
    definitions: put(core.definitions, (n) => String(n.id)),
    statements: put(core.statements, (n) => String(n.id)),
  };
  return { core: out, attached };
}

export interface F2RevisionContext {
  requested_targets: string[];
  resolved_targets: string[];
  /** Requested targets that name no core node, symbol or S-block: dropped from the packet. */
  unresolved_targets: string[];
  /** One line per S-block of the plan not carried (`envReferenceIndex`). */
  env_index: string[];
  plan: Record<string, unknown>;
  core: Record<string, unknown>;
  /** The affected nodes: the targets and what must move with a changed record. */
  affected: string[];
  /** Nodes carried in full beside them, as context: what an affected node's text names (`referencedNodeIds`). */
  context: string[];
  /** One reference line per core node not carried (`nodeReferenceIndex`). */
  index: string[];
  /** The nodes one hop from the carried ones (`nodeNeighbours`). */
  neighbours: string[];
  omitted_counts: {
    plan_nodes: number;
    env_entries: number;
    symbols: number;
    assumptions: number;
    definitions: number;
    statements: number;
    citations: number;
  };
}

/** Where a scaffold on disk does not cover the plan: delivered nodes without an `@node` tag,
 *  undelivered nodes that still have one, S-blocks without an `@env` tag. A revise that names
 *  them among its targets may be localized; one that does not would leave them unscaffolded. */
export function scaffoldCoverageGaps(
  plan: Plan,
  tags: { nodes: Set<string>; envs: Set<string> },
): string[] {
  return [
    ...Object.entries(plan.nodes)
      .filter(([id, node]) => (node.delivery_status !== "undelivered") !== tags.nodes.has(id))
      .map(([id]) => id),
    ...plan.env.filter((env) => !tags.envs.has(env.id)).map((env) => env.id),
  ];
}

type CoreNode = Core["assumptions"][number] | Core["definitions"][number] | Core["statements"][number];

function envTarget(target: string, envIds: Set<string>): string | null {
  if (envIds.has(target)) return target;
  const compact = target.replace(/-/g, "").toUpperCase();
  return envIds.has(compact) ? compact : null;
}

/**
 * The packet of a scoped revise (F2's re-scaffold, F1.5's review of a re-plan): the plan entries
 * and core records of the AFFECTED nodes (`reviseAffectedNodeIds` over the requested targets),
 * the symbol entries they use (`symbolsUsedByNode`, each with the scoped clauses applicable to
 * them), the S-blocks binding those, the settings that apply to them (`applicableSettings`), their
 * binding readings once (`shareBindingReadings`), and a reference line for every other node.
 * `flagged` are the targets whose record did not change (a reviewer's flag, a name in a
 * directive): shown without what moves with a changed record. A carried entry keeps its
 * `notes` (the statement shape and the encoding decisions on record).
 * Beside the affected nodes the packet carries, as CONTEXT, the nodes their text names
 * (`referencedNodeIds`) and `contextNodes` (nodes a directive mentions without asking to edit
 * them): records and plan entries in full, and nothing followed from them.
 * `contextSymbols` / `contextEnvs` are symbols and S-blocks to show without treating their users
 * as changed (a symbol whose wording moved, an S-block whose entry was edited). A target that
 * names nothing of the core or the plan is dropped (`unresolved_targets`): one stray id must not
 * cost the scoping. Null — the caller keeps the whole plan and core — when no target resolves or
 * the set reaches every node.
 */
export function buildF2RevisionContext(
  core: Core,
  plan: Plan,
  requestedTargets: string[],
  opts: { contextSymbols?: readonly string[]; contextEnvs?: readonly string[]; flagged?: readonly string[]; contextNodes?: readonly string[] } = {},
): F2RevisionContext | null {
  const requested = [...new Set(requestedTargets.map((t) => t.trim()).filter(Boolean))];
  if (requested.length === 0 && !opts.contextEnvs?.length) return null;
  const flagged = new Set((opts.flagged ?? []).map((t) => t.trim()));

  const assumptions = new Map(core.assumptions.map((node) => [node.id, node] as const));
  const definitions = new Map(core.definitions.map((node) => [node.id, node] as const));
  const statements = new Map(core.statements.map((node) => [node.id, node] as const));
  const coreNodes = new Map<string, CoreNode>([
    ...assumptions,
    ...definitions,
    ...statements,
  ]);
  const envIds = new Set(plan.env.map((entry) => entry.id));
  const symbols = new Map(core.symbols.map((symbol) => [symbol.name, symbol] as const));
  const leanNameToId = new Map(
    Object.entries(plan.nodes).map(([id, entry]) => [entry.lean_name, id] as const),
  );

  const changedNodes = new Set<string>();
  const flaggedNodes = new Set<string>();
  const changedSymbols = new Set<string>();
  const selectedEnvs = new Set<string>();
  const flaggedEnvs = new Set<string>();
  const selectedSymbols = new Set<string>();
  const resolvedTargets: string[] = [];
  const unresolved: string[] = [];
  for (const target of requested) {
    if (target.startsWith("sym:") && symbols.has(target.slice(4))) {
      // A flagged symbol is one whose realization the reviewer could not find or accept: its
      // entry and the definition it names are the context; its users did not change.
      const symbol = symbols.get(target.slice(4))!;
      if (!flagged.has(target)) changedSymbols.add(symbol.name);
      else {
        selectedSymbols.add(symbol.name);
        if (symbol.ref && coreNodes.has(symbol.ref)) flaggedNodes.add(symbol.ref);
      }
      resolvedTargets.push(target);
      continue;
    }
    const env = envTarget(target, envIds);
    if (env) {
      // A flagged S-block is shown with the symbols it binds; a changed one moves their users.
      if (flagged.has(target)) flaggedEnvs.add(env);
      else selectedEnvs.add(env);
      resolvedTargets.push(env);
      continue;
    }
    const normalized = objIdToNodeId(target);
    const nodeId = coreNodes.has(target)
      ? target
      : coreNodes.has(normalized)
        ? normalized
        : leanNameToId.get(target);
    if (!nodeId || !coreNodes.has(nodeId)) {
      unresolved.push(target);
      continue;
    }
    (flagged.has(target) ? flaggedNodes : changedNodes).add(nodeId);
    resolvedTargets.push(nodeId);
  }
  if (resolvedTargets.length === 0 && !opts.contextEnvs?.length) return null;

  // A shared symbol/environment change starts at every declaration that realizes
  // or directly uses it; those declarations are the actual forced edit frontier.
  for (const env of plan.env) {
    if (selectedEnvs.has(env.id)) {
      for (const symbol of env.binds_symbols) changedSymbols.add(symbol);
    }
  }
  // If x changes, every symbol whose definition references x changes as well.
  let grew = true;
  while (grew) {
    grew = false;
    for (const symbol of core.symbols) {
      if (changedSymbols.has(symbol.name)) continue;
      if ((symbol.refs ?? []).some((ref) => changedSymbols.has(ref))) {
        changedSymbols.add(symbol.name);
        grew = true;
      }
    }
  }
  if (changedSymbols.size > 0) {
    // A node uses a symbol it lists in `free_symbols` or writes in its text (`symbolsUsedByNode`:
    // a node without the list is read by its text, never taken to use every symbol).
    for (const id of coreNodes.keys()) {
      for (const symbol of symbolsUsedByNode(core, id)) if (changedSymbols.has(symbol)) changedNodes.add(id);
    }
    for (const name of changedSymbols) {
      const ref = symbols.get(name)?.ref;
      if (ref && coreNodes.has(ref)) changedNodes.add(ref);
    }
  }

  // What must move with the changed nodes (the one rule of `revise_scope.ts`); a prerequisite
  // that does not move is a reference line, not a record.
  const affectedNodes = reviseAffectedNodeIds(core, plan, changedNodes, flaggedNodes);
  if (affectedNodes.size >= coreNodes.size) return null;
  // A result an affected node's text names (a condition that is "the conditions of Lemma X") is
  // read with it: carried in full, as context — with its hypotheses' texts and readings, below.
  const contextNodes = referencedNodeIds(core, affectedNodes);
  for (const id of opts.contextNodes ?? []) if (coreNodes.has(id) && !affectedNodes.has(id)) contextNodes.add(id);
  const selectedNodes = new Set([...affectedNodes, ...contextNodes]);

  // The symbols the affected nodes use, and the S-blocks binding one of them — the world an edit
  // must typecheck in. Nodes that use no bound symbol get the blocks of the sampling model.
  for (const symbol of changedSymbols) selectedSymbols.add(symbol);
  // (Of the affected nodes: a context node is read, not edited — its symbols are in the core file.)
  for (const id of affectedNodes) for (const symbol of symbolsUsedByNode(core, id)) selectedSymbols.add(symbol);
  for (const env of plan.env) {
    if (env.binds_symbols.some((symbol) => selectedSymbols.has(symbol))) selectedEnvs.add(env.id);
  }
  if (selectedEnvs.size === 0 && selectedNodes.size > 0) {
    for (const env of plan.env) if (env.binds_sampling_model) selectedEnvs.add(env.id);
  }
  for (const symbol of opts.contextSymbols ?? []) if (symbols.has(symbol)) selectedSymbols.add(symbol);
  for (const env of opts.contextEnvs ?? []) if (envIds.has(env)) selectedEnvs.add(env);
  for (const env of plan.env) {
    if (!flaggedEnvs.has(env.id)) continue;
    selectedEnvs.add(env.id);
    for (const symbol of env.binds_symbols) if (symbols.has(symbol)) selectedSymbols.add(symbol);
  }
  // Symbol definitions may reference other symbols; retain that small closure.
  grew = true;
  while (grew) {
    grew = false;
    for (const symbol of core.symbols) {
      if (!selectedSymbols.has(symbol.name)) continue;
      for (const ref of symbol.refs ?? []) {
        if (symbols.has(ref) && !selectedSymbols.has(ref)) {
          selectedSymbols.add(ref);
          grew = true;
        }
      }
    }
  }

  // A carried plan record keeps its `notes`: there F1 states the statement shape F2 realizes and
  // the encoding decisions earlier redirects settled — a scaffolder that does not see them can
  // undo one while fixing something else. They are the current plan only, capped by the plan gate
  // (P11), and only the carried records are shown.
  const withoutNotes = <T extends { notes?: string }>(entry: T): T => entry;
  const selectedPlanNodes = Object.fromEntries(
    Object.entries(plan.nodes).filter(([id]) => selectedNodes.has(id)).map(([id, entry]) => [id, withoutNotes(entry)]),
  );
  const citedIds = new Set(
    Object.values(selectedPlanNodes).map((entry) => entry.source).filter((id): id is string => !!id),
  );
  const coreView = formalizationCoreContextValue(core);
  const selected = (list: unknown): Array<Record<string, unknown>> =>
    (list as Array<Record<string, unknown>>).filter((node) => selectedNodes.has(String(node.id)));
  const shared = shareBindingReadings([...selected(coreView.assumptions), ...selected(coreView.definitions), ...selected(coreView.statements)]);
  const records = (ids: ReadonlyMap<string, unknown>): Array<Record<string, unknown>> => shared.nodes.filter((node) => ids.has(String(node.id)));
  const settings = applicableSettings(core, affectedNodes);
  // The text of each hypothesis a carried statement takes (and of the members of a class it takes,
  // or that is carried) when the hypothesis is neither carried nor among the readings: a reader
  // of the statement needs what it assumes, not the id.
  const hypothesisTexts: Record<string, string> = {};
  const say = (id: string): void => {
    if (selectedNodes.has(id) || id in shared.readings) return;
    const atom = assumptions.get(id);
    const def = definitions.get(id);
    if (atom) hypothesisTexts[id] = atom.condition;
    else if (def) hypothesisTexts[id] = [def.name, def.construction].filter(Boolean).join(": ");
    for (const member of def?.by_member_properties ?? []) if (member !== id && !(member in hypothesisTexts)) say(member);
  };
  for (const id of selectedNodes) {
    for (const dep of [...(statements.get(id)?.depends_on ?? []), ...(definitions.get(id)?.by_member_properties ?? [])]) say(dep);
  }
  const selectedCore: Record<string, unknown> = {
    qid: core.qid,
    ...(core.cluster ? { cluster: core.cluster } : {}),
    symbols: core.symbols.filter((symbol) => selectedSymbols.has(symbol.name)).map((symbol) => symbolEntryShown(core, symbol, affectedNodes)),
    assumptions: records(assumptions),
    definitions: records(definitions),
    statements: records(statements),
    ...(Object.keys(shared.readings).length > 0 ? { binding_readings: shared.readings } : {}),
    ...(Object.keys(hypothesisTexts).length > 0 ? { hypothesis_texts: hypothesisTexts } : {}),
    ...(settings ? { sampling_model: settings } : {}),
    ...(core.estimand_functional ? { estimand_functional: core.estimand_functional } : {}),
    target_estimand: core.target_estimand,
  };
  const selectedPlan: Record<string, unknown> = {
    qid: plan.qid,
    ...(plan.cluster ? { cluster: plan.cluster } : {}),
    ...(plan.lean_subdir ? { lean_subdir: plan.lean_subdir } : {}),
    env: plan.env.filter((entry) => selectedEnvs.has(entry.id)).map(withoutNotes),
    nodes: selectedPlanNodes,
    citations: plan.citations.filter((citation) => citedIds.has(citation.id)),
    ...(plan.feasibility ? { feasibility: plan.feasibility } : {}),
  };

  const neighbours = nodeNeighbours(core, plan, selectedNodes);
  return {
    requested_targets: requested,
    resolved_targets: [...new Set(resolvedTargets)],
    unresolved_targets: unresolved,
    env_index: envReferenceIndex(plan, selectedEnvs),
    plan: selectedPlan,
    core: selectedCore,
    affected: [...affectedNodes],
    context: [...contextNodes],
    index: nodeReferenceIndex(core, plan, selectedNodes),
    neighbours: [...coreNodes.keys()].filter((id) => neighbours.has(id)),
    omitted_counts: {
      plan_nodes: Object.keys(plan.nodes).length - Object.keys(selectedPlanNodes).length,
      env_entries: plan.env.length - selectedEnvs.size,
      symbols: core.symbols.length - selectedSymbols.size,
      assumptions: core.assumptions.length - records(assumptions).length,
      definitions: core.definitions.length - records(definitions).length,
      statements: core.statements.length - records(statements).length,
      citations: plan.citations.length - (selectedPlan.citations as unknown[]).length,
    },
  };
}

/** One line per S-block a revise does not carry: `<id> | binds <symbols> | <reuse>` (its `world`
 *  is in the plan file). */
export function envReferenceIndex(plan: Plan, shown: ReadonlySet<string>): string[] {
  return plan.env
    .filter((entry) => !shown.has(entry.id))
    .map((entry) => [entry.id, `binds ${entry.binds_symbols.join(", ") || "no symbol"}`, entry.reuse ?? entry.disposition].join(" | "));
}
