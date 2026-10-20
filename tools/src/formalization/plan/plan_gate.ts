// The F1 plan gate.
//
// Mechanical, no LLM. Runs on the plan right after F1 (self-check), as F1.5's
// pre-review lint, and at F2 before the scaffold call and after its sync-back.
// Enforces the one-to-one invariant —
// every core node maps to exactly one Lean object, no orphan Lean — plus kind/
// member/hyp consistency. A whole class of plan defects never reaches the
// reuse-soundness reviewer.
import type { Core } from "../../core/schema.js";
import { coreNodeIds } from "../../core/schema.js";
import { buildDagFromCore } from "../../core/dag.js";
import type { ExtractedDecl } from "../../graph/extractor.js";
import type { FormalizationGraph } from "../../graph/types.js";
import { EnvEntrySchema, LEGACY_PLAN_KEYS, NodeEntrySchema, PLAN_NOTES_MAX, PlanSchema, deriveFeasibility, type Plan } from "./schema.js";
import type { TagReconciliation } from "../f2_tag_reconcile.js";

export type PlanGateCode =
  | "schema"
  | "P1" // coverage
  | "P2" // member consistency
  | "P3" // kind consistency
  | "P4" // hyp closure
  | "P5" // reuse existence
  | "P6" // module resolution
  | "P7" // orphan Lean (emitted-tag correspondence)
  | "P8" // derived-feasibility consistency
  | "P9" // cited mapping (the core's status:"cited" ↔ gate_class:"cited"; source resolution)
  | "P10" // undelivered guard (secondary theorem or cited node only; never load-bearing)
  | "P11"; // hygiene: no key outside the schema, no `notes` past the cap (F1/F1.5 only)

export interface PlanGateViolation {
  code: PlanGateCode;
  where: string;
  message: string;
}

export interface PlanGateResult {
  ok: boolean;
  violations: PlanGateViolation[];
  /** Non-blocking observations (a reuse name in an unindexed library, which P5 cannot check). */
  notes: PlanGateViolation[];
}

export interface PlanGateOptions {
  /** Library-index decl names; when present, enables P5 (reuse existence). */
  knownDecls?: Set<string>;
  /** Top-level name prefixes an indexed source owns (`Causalean`, the toolkit and papers libs).
   *  When present, P5 checks only names under one of them; any other name (Mathlib and other
   *  unindexed libraries) becomes a note. Absent ⇒ every reuse name is checked. */
  ownedDeclPrefixes?: readonly string[];
  /** Importable module paths; when present, P6 requires membership (else format-only). */
  knownModules?: Set<string>;
  /** Tags parsed from emitted Lean (`-- @node` / `-- @env`); enables P7. F2 only. */
  leanTags?: { nodes: Set<string>; envs: Set<string> };
  /** All emitted Lean declaration names. Catches stale untagged declarations for an
   * undelivered plan node, which tag-only P7 cannot see. */
  leanDeclNames?: Set<string>;
  /** Formalization graph captured before F2. Enables the P7 exemption for agent-introduced
   * helpers already on the graph, which intentionally have no plan node. */
  preF2Graph?: FormalizationGraph;
  /** Declarations extracted from the emitted Lean. Required with `preF2Graph` to
   * verify that an exempt helper is still linked to the same declaration. */
  annotatedDecls?: ExtractedDecl[];
  /** The scaffold pass (F2): proofs are not due yet, so a discharged citation's declaration may
   *  still carry `sorry` — its name, kind and uniqueness are checked; the delivery audit checks the proof. */
  proofsNotDue?: boolean;
  /** Declarations snapshotted from disk immediately before the F2 worker ran. A
   * plan-less helper is preserved only when its emitted declaration is byte-for-byte
   * identical at the extractor level; graph review hashes can be stale across parser
   * upgrades and therefore are not an adequate pre-image. */
  preF2AnnotatedDecls?: ExtractedDecl[];
  /** What the F2 revise tag reconciliation did before the scaffolder ran; P7 messages cite it. */
  tagReconciliation?: TagReconciliation;
  /** Final delivery audit only: permit a non-cited secondary omission after that
   * caller has required and will validate dual-model evidence receipts. */
  allowReviewedSecondaryUndelivered?: boolean;
  /** Enforce P11 (`planHygieneViolations`). On where F1 can act on it — its self-check and F1.5's
   *  pre-lint; F2's post-sync gate and the delivery audit leave an over-long plan to the next F1 pass. */
  hygiene?: boolean;
}

/**
 * P11 — the plan holds the CURRENT plan and nothing else. One violation per offender (the plan
 * root, an S-block, a node entry), naming every key the schema does not define and a `notes`
 * past `PLAN_NOTES_MAX`. The schema strips unknown keys on parse, so no stage reads them — but
 * the plan is pasted into prompts as written, and a plan whose every revise appended a note and
 * archived what it replaced grew past what one call can hold. Reads the plan as written. Pure.
 */
export function planHygieneViolations(planInput: unknown): PlanGateViolation[] {
  const out: PlanGateViolation[] = [];
  const rec = (x: unknown): Record<string, unknown> | null => (x && typeof x === "object" && !Array.isArray(x) ? (x as Record<string, unknown>) : null);
  const plan = rec(planInput);
  if (!plan) return out;
  const check = (where: string, entry: Record<string, unknown>, defined: readonly string[], notes: boolean): void => {
    const extra = Object.keys(entry).filter((k) => !defined.includes(k));
    const length = notes && typeof entry.notes === "string" ? entry.notes.length : 0;
    const parts = [
      length > PLAN_NOTES_MAX
        ? `\`notes\` is ${length} characters (cap ${PLAN_NOTES_MAX}): REWRITE it to state the current plan of this entry only — no history of earlier revisions or attempts, nothing marked superseded`
        : "",
      extra.length > 0
        ? `key(s) the plan schema does not define: ${extra.map((k) => `\`${k}\``).join(", ")} — DELETE them (what one says of the current plan goes into \`notes\`, within the cap)`
        : "",
    ].filter(Boolean);
    if (parts.length > 0) out.push({ code: "P11", where, message: parts.join("; ") });
  };
  check("<root>", plan, [...Object.keys(PlanSchema.shape), ...LEGACY_PLAN_KEYS.root], false);
  for (const e of Array.isArray(plan.env) ? plan.env : []) {
    const entry = rec(e);
    if (entry) check(typeof entry.id === "string" ? entry.id : "env", entry, Object.keys(EnvEntrySchema.shape), true);
  }
  for (const [id, n] of Object.entries(rec(plan.nodes) ?? {})) {
    const entry = rec(n);
    if (entry) check(id, entry, [...Object.keys(NodeEntrySchema.shape), ...LEGACY_PLAN_KEYS.node], true);
  }
  return out;
}

/** Log the gate's non-blocking notes (one line each); silent when there are none. */
export function logPlanGateNotes(notes: readonly PlanGateViolation[]): void {
  if (notes.length === 0) return;
  console.warn(`[theoremchecker] plan_gate notes:\n  ${notes.map((n) => `${n.code} @ ${n.where}: ${n.message}`).join("\n  ")}`);
}

const MODULE_RE = /^[A-Z][A-Za-z0-9_]*(\.[A-Za-z0-9_]+)*$/;

function isDirectCanonicalMetadataPayload(decl: ExtractedDecl | undefined): boolean {
  if (!decl?.sourceText) return false;
  const cut = decl.sourceText.indexOf(":=");
  if (cut < 0) return false;
  // The extractor bounds declarations at the next declaration/tag. For the final
  // declaration in a namespace, that can leave the namespace-closing `end ...`
  // attached to sourceText even though it is not part of the definition body.
  const body = decl.sourceText.slice(cut + 2).trim()
    .replace(/\n\s*end(?:\s+[A-Za-z0-9_.]+)?\s*$/, "")
    .trim();
  const leanString = `"(?:\\\\.|[^"\\\\])*"`;
  const items = `(?:${leanString}(?:\\s*,\\s*${leanString})*\\s*,?)?`;
  if (/\b_root_\.String\b/.test(decl.statement) && !/\b_root_\.(?:List|Array)\b/.test(decl.statement)) {
    return new RegExp(`^${leanString}$`, "s").test(body);
  }
  if (/\b_root_\.List\s+_root_\.String\b/.test(decl.statement)) {
    return new RegExp(`^\\[\\s*${items}\\s*\\]$`, "s").test(body);
  }
  if (/\b_root_\.Array\s+_root_\.String\b/.test(decl.statement)) {
    return new RegExp(`^#\\[\\s*${items}\\s*\\]$`, "s").test(body);
  }
  return false;
}

/** A statement's `depends_on` with those of every result it uses, transitively. */
function inheritedDeps(core: Core, id: string): Set<string> {
  const byId = new Map(core.statements.map((st) => [st.id, st] as const));
  const out = new Set<string>();
  const stack = [...(byId.get(id)?.depends_on ?? [])];
  while (stack.length > 0) {
    const d = stack.pop()!;
    if (out.has(d)) continue;
    out.add(d);
    stack.push(...(byId.get(d)?.depends_on ?? []));
  }
  return out;
}

export function runPlanGate(planInput: unknown, core: Core, opts: PlanGateOptions = {}): PlanGateResult {
  const violations: PlanGateViolation[] = [];

  const parsed = PlanSchema.safeParse(planInput);
  if (!parsed.success) {
    for (const issue of parsed.error.issues) {
      violations.push({ code: "schema", where: issue.path.join(".") || "<root>", message: issue.message });
    }
    return { ok: false, violations, notes: [] };
  }
  const plan: Plan = parsed.data;
  if (opts.hygiene) violations.push(...planHygieneViolations(planInput));
  const dag = buildDagFromCore(core);
  const nodeIds = coreNodeIds(core);
  const symbolNames = new Set(core.symbols.map((s) => s.name));
  const classIds = new Set([...dag.kindOf].filter(([, k]) => k === "definition-class").map(([id]) => id));
  const assumptionIds = new Set([...dag.kindOf].filter(([, k]) => k === "assumption").map(([id]) => id));
  const gateIds = new Set(Object.entries(plan.nodes).filter(([, n]) => n.gate).map(([id]) => id));

  // P1: coverage. nodes keys == core node ids; symbols all bound by some S-block.
  const planNodeKeys = new Set(Object.keys(plan.nodes));
  for (const id of nodeIds) {
    if (!planNodeKeys.has(id)) violations.push({ code: "P1", where: id, message: `core node has no plan entry` });
  }
  for (const id of planNodeKeys) {
    if (!nodeIds.has(id)) violations.push({ code: "P1", where: id, message: `plan node is not a core node id` });
  }
  const boundSymbols = new Set<string>();
  for (const e of plan.env) {
    for (const s of e.binds_symbols) {
      boundSymbols.add(s);
      if (!symbolNames.has(s)) violations.push({ code: "P1", where: e.id, message: `binds unknown symbol '${s}'` });
    }
  }
  for (const s of symbolNames) {
    if (!boundSymbols.has(s)) violations.push({ code: "P1", where: `symbol:${s}`, message: `symbol bound by no S-block` });
  }

  // P3: kind consistency (per node id whose plan entry exists).
  for (const [id, node] of Object.entries(plan.nodes)) {
    const kind = dag.kindOf.get(id);
    if (kind === undefined) continue; // already flagged by P1
    const coreStmt = kind === "statement" ? core.statements.find((s) => s.id === id) : undefined;
    const want =
      // A core assumption is normally `assumption`, but may be DISCHARGED to a proved
      // `lemma`/`theorem` (substrate-fact discharge) — allow all three for assumptions.
      kind === "assumption" ? ["assumption", "lemma", "theorem"]
      : kind === "definition-class" ? ["structure"]
      : kind === "definition-construction" ? ["def"]
      : coreStmt && node.gate
        ? node.gate_class === "cited"
          ? (coreStmt.source?.carrier ?? "logical-claim") === "bibliographic-metadata" ? ["def"] : ["assumption"]
          : ["assumption"]
      : coreStmt?.kind === "openendedquestion" ? ["def"] // solved OEQs are represented by thm: nodes in the core; only unresolved OEQs can reach F1.
      : ["theorem", "lemma"]; // statement
    if (!want.includes(node.lean_kind)) {
      violations.push({ code: "P3", where: id, message: `lean_kind '${node.lean_kind}' invalid for core ${kind} (expected ${want.join("|")})` });
    }
  }

  // P2: member consistency. A class node's `members` must equal the core's
  // by_member_properties for that class; every member is an assumption id.
  for (const classId of classIds) {
    const node = plan.nodes[classId];
    if (!node) continue;
    const coreMembers = new Set(dag.classMembers.get(classId) ?? []);
    const planMembers = new Set(node.members ?? []);
    for (const m of coreMembers) {
      if (!planMembers.has(m)) violations.push({ code: "P2", where: classId, message: `plan omits core member '${m}'` });
    }
    for (const m of planMembers) {
      if (!coreMembers.has(m)) violations.push({ code: "P2", where: classId, message: `plan lists non-member '${m}'` });
      else if (!assumptionIds.has(m)) violations.push({ code: "P2", where: classId, message: `member '${m}' is not an assumption` });
    }
  }

  // P4: declared-hyp consistency. Only theorem/lemma consumers may carry hyps at all.
  // Each declared top-level hyp must be an assumption, class, or logical gate in
  // depends_on — its own, or inherited from a result it uses ("under the conditions of
  // Lemma X": the Lean must assume X's hypotheses to apply X; whether the paper grants
  // them is F2.5's call, below). Do not infer the converse from the dependency DAG: a core assumption
  // may occur under a quantified implication in the theorem conclusion, so requiring
  // every assumption dependency here as a top-level hyp changes a faithful statement.
  // F2.5 compares the emitted Lean statement with the frozen note and remains the
  // authoritative completeness check.
  for (const [id, candidate] of Object.entries(plan.nodes)) {
    if ((candidate.hyps?.length ?? 0) === 0) continue;
    if (candidate.lean_kind !== "theorem" && candidate.lean_kind !== "lemma") {
      violations.push({ code: "P4", where: id, message: `lean_kind '${candidate.lean_kind}' cannot carry hyps` });
    } else if (!core.statements.some((statement) => statement.id === id)) {
      violations.push({ code: "P4", where: id, message: `only a core statement mapped to theorem/lemma may carry hyps` });
    }
  }
  for (const s of core.statements) {
    const node = plan.nodes[s.id];
    if (!node) continue;
    const logicalCitedDeps = s.depends_on.filter((dep) => {
      const cited = core.statements.find((candidate) => candidate.id === dep && candidate.status === "cited");
      return !!cited && (cited.source?.carrier ?? "logical-claim") === "logical-claim";
    });
    if (node.lean_kind !== "theorem" && node.lean_kind !== "lemma") {
      for (const dep of logicalCitedDeps) {
        violations.push({ code: "P4", where: s.id, message: `logical cited dep '${dep}' requires a theorem/lemma consumer with an explicit hyp` });
      }
      continue;
    }
    const hyps = new Set(node.hyps ?? []);
    const depSet = inheritedDeps(core, s.id);
    for (const h of hyps) {
      if (!depSet.has(h)) violations.push({ code: "P4", where: s.id, message: `hyp '${h}' is not in depends_on` });
      else if (!assumptionIds.has(h) && !classIds.has(h) && !gateIds.has(h)) {
        violations.push({ code: "P4", where: s.id, message: `hyp '${h}' is neither an assumption nor a class (cannot be a hypothesis)` });
      } else if (gateIds.has(h)) {
        const citedGate = core.statements.find((candidate) => candidate.id === h && candidate.status === "cited");
        if (citedGate && (citedGate.source?.carrier ?? "logical-claim") === "bibliographic-metadata") {
          violations.push({ code: "P4", where: s.id, message: `bibliographic metadata '${h}' cannot be a logical hyp` });
        }
      }
    }
    // A logical cited statement is a borrowed proposition and must surface explicitly
    // in every direct consumer. Bibliographic metadata is deliberately non-logical and
    // is never a theorem hypothesis even when the core uses it for comparative framing.
    for (const dep of logicalCitedDeps) {
      const citedPlanNode = plan.nodes[dep];
      if (citedPlanNode?.citation_discharged === true &&
          (citedPlanNode.lean_kind === "lemma" || citedPlanNode.lean_kind === "theorem")) continue;
      if (!hyps.has(dep)) {
        violations.push({ code: "P4", where: s.id, message: `logical cited dep '${dep}' must be an explicit hyp` });
      }
    }
  }

  // P5: reuse existence (optional — needs the library index). Only a name some indexed source
  // owns can be checked; one outside every owned prefix is in an unindexed library (a note).
  const notes: PlanGateViolation[] = [];
  if (opts.knownDecls) {
    const owned = opts.ownedDeclPrefixes;
    const checkReuse = (where: string, decl: string | null | undefined) => {
      if (!decl || opts.knownDecls!.has(decl)) return;
      if (owned && !owned.some((p) => decl === p || decl.startsWith(`${p}.`))) {
        notes.push({ code: "P5", where, message: `reuse decl '${decl}' is in an unindexed library, not checked` });
      } else {
        violations.push({ code: "P5", where, message: `reuse decl '${decl}' not found in library index` });
      }
    };
    for (const e of plan.env) checkReuse(e.id, e.disposition === "reuse" ? e.reuse : null);
    for (const [id, n] of Object.entries(plan.nodes)) checkReuse(id, n.disposition === "reuse" ? n.reuse : null);
  }

  // P6: module resolution. Format always; membership when knownModules supplied.
  const checkModules = (where: string, mods: string[]) => {
    for (const m of mods) {
      if (!MODULE_RE.test(m)) violations.push({ code: "P6", where, message: `module '${m}' is not a valid module path` });
      else if (opts.knownModules && !opts.knownModules.has(m)) violations.push({ code: "P6", where, message: `module '${m}' does not resolve` });
    }
  };
  for (const e of plan.env) checkModules(e.id, e.modules);
  for (const [id, n] of Object.entries(plan.nodes)) checkModules(id, n.modules);

  // P7: orphan Lean — emitted tags correspond exactly to plan keys (F2 only).
  if (opts.leanTags) {
    const envIds = new Set(plan.env.map((e) => e.id));
    const preF2Nodes = new Map(opts.preF2Graph?.nodes.map((node) => [node.id, node]) ?? []);
    const extractedByNode = new Map<string, ExtractedDecl[]>();
    for (const decl of opts.annotatedDecls ?? []) {
      const decls = extractedByNode.get(decl.nodeId) ?? [];
      decls.push(decl);
      extractedByNode.set(decl.nodeId, decls);
    }
    // A helper the agents introduced before this F2 pass (a graph node with no plan entry) keeps its
    // tag on exactly one declaration, finished or not and whatever F2 revised in it: it is no orphan,
    // and the reviewer judges it as a node. A tag naming no known node stays an orphan.
    const isPreF2Helper = (id: string): boolean => {
      const node = preF2Nodes.get(id);
      return (node?.kind === "lemma" || node?.kind === "definition") &&
        node.provenance === "agent-introduced" &&
        (extractedByNode.get(id) ?? []).length === 1;
    };
    // An agent helper's tag is its declaration's own name (no `:` — core ids always carry one), so it
    // is recognised from the Lean alone: a re-plan rebuilds the graph from the core and drops helpers.
    const isSelfNamedHelper = (id: string): boolean => {
      const decls = extractedByNode.get(id) ?? [];
      return !id.includes(":") && decls.length === 1 && decls[0]!.declName.split(".").pop() === id;
    };
    // Say what the pre-scaffold reconciliation did with this id, so the failure is actionable.
    const rec = opts.tagReconciliation;
    const orphanContext = (t: string): string => {
      const kept = rec?.staleReferenced.find((x) => x.id === t);
      if (kept) return ` — stale tag, referenced by ${kept.referencedBy.join(", ")}; reconciliation kept ${kept.decl} for the scaffolder, which did not resolve it`;
      const moved = rec?.retagged.find((x) => x.from === t);
      if (moved) return ` — reconciliation retagged it to ${moved.to}, but the scaffolder re-emitted the old tag`;
      if (rec?.removed.some((x) => x.id === t)) return ` — reconciliation removed it, but the scaffolder re-emitted it`;
      return "";
    };
    const missingContext = (id: string): string => {
      if (rec?.newNodes.some((x) => x.id === id)) return ` — reconciliation listed it to the scaffolder as a new node to scaffold; none was emitted`;
      const moved = rec?.retagged.find((x) => x.to === id);
      if (moved) return ` — reconciliation retagged ${moved.from} (${moved.decl}) to it, but the tag is gone`;
      return "";
    };
    for (const t of opts.leanTags.nodes) {
      if (!planNodeKeys.has(t) && !isPreF2Helper(t) && !isSelfNamedHelper(t)) {
        violations.push({ code: "P7", where: t, message: `emitted Lean tags '@node ${t}' but no plan entry or pre-F2 agent-introduced helper${orphanContext(t)}` });
      }
    }
    for (const id of planNodeKeys) {
      const undelivered = plan.nodes[id]?.delivery_status === "undelivered";
      if (undelivered && opts.leanTags.nodes.has(id)) {
        violations.push({ code: "P7", where: id, message: `undelivered node must not emit an '@node' Lean declaration` });
      } else if (!undelivered && !opts.leanTags.nodes.has(id)) {
        violations.push({ code: "P7", where: id, message: `delivered plan node has no emitted '@node' tag${missingContext(id)}` });
      }
    }
    if (opts.leanDeclNames) {
      const names = new Set<string>();
      for (const name of opts.leanDeclNames) {
        names.add(name);
        names.add(name.split(".").at(-1) ?? name);
      }
      for (const id of planNodeKeys) {
        const node = plan.nodes[id];
        if (node.delivery_status !== "undelivered") continue;
        const shortName = node.lean_name.split(".").at(-1) ?? node.lean_name;
        if (names.has(node.lean_name) || names.has(shortName)) {
          violations.push({ code: "P7", where: id, message: `undelivered node still has Lean declaration '${node.lean_name}' (tagged or untagged)` });
        }
      }
    }
    for (const t of opts.leanTags.envs) {
      if (!envIds.has(t)) violations.push({ code: "P7", where: t, message: `emitted Lean tags '@env ${t}' but no S-block` });
    }
    for (const id of envIds) {
      if (!opts.leanTags.envs.has(id)) violations.push({ code: "P7", where: id, message: `planned S-block has no emitted '@env' tag` });
    }
  }

  // P8: stored feasibility must match the derived value.
  if (plan.feasibility && plan.feasibility !== deriveFeasibility(plan)) {
    violations.push({ code: "P8", where: "<root>", message: `feasibility '${plan.feasibility}' disagrees with derived '${deriveFeasibility(plan)}'` });
  }
  // Paper-owned work cannot leave F1 as an assumed or omitted proof obligation.
  // Only an explicit external gate may use the substrate-build checkpoint; all
  // other delivered define-local nodes must proceed to F2–F4, however difficult.
  for (const [id, node] of Object.entries(plan.nodes)) {
    if (
      node.disposition === "define-local" &&
      node.defer_tier &&
      !node.gate
    ) {
      violations.push({
        code: "P8",
        where: id,
        message: "paper-owned proved/to-prove statement or support node cannot be defer_tier without an external gate; keep it in the F2–F4 proof scope",
      });
    }
  }
  for (const statement of core.statements) {
    const node = plan.nodes[statement.id];
    if (node?.gate && statement.status !== "cited") {
      violations.push({
        code: "P8",
        where: statement.id,
        message: `paper-owned core statement with status '${statement.status}' cannot be converted into a planner-authored external gate`,
      });
    }
  }
  for (const [id, node] of Object.entries(plan.nodes)) {
    if (node.gate && !core.statements.some((statement) => statement.id === id)) {
      violations.push({
        code: "P8",
        where: id,
        message: "gate:true is legal only for a core statement with frozen external provenance",
      });
    }
  }

  // P9: cited mapping. A `status:"cited"` statement of the core starts BORROWED (the paper
  // does not prove it). A mathematical cited claim is represented by a `gate_class:"cited"`
  // Prop assumption; a bibliographic scope/provenance record uses a source-reviewed non-Prop `def`
  // rather than a logical premise.
  // The supported discharge path may later replace that gate with an exact proved
  // lemma/theorem while retaining `source` as provenance. Do not force such a proved node
  // back into an assumption: gate.ts --discharge deliberately removes the gate keys and
  // reopens every consumer for F2.5/F4 review. Conversely, a non-gate `assumption` is not a
  // discharge and remains forbidden. The discharged shape carries `citation_discharged:true`:
  // F1 may plan a cited result that way from the start (it is then scaffolded, proved and
  // matched against its source like any discharged citation), and bin/gate.ts --discharge and
  // a round-A plan rewrite (plan/discharge.ts) stamp it later. It is always `define-local`: a
  // `reuse` emits nothing locally for F2.5 to match against the source. Every node `source`
  // must resolve to citations[].
  const citationIds = new Set(plan.citations.map((c) => c.id));
  for (const s of core.statements) {
    const node = plan.nodes[s.id];
    if (!node) continue; // P1 already flagged
    if (s.status === "cited") {
      const frozenCarrier = s.source?.carrier ?? "logical-claim";
      const expectedDeferredKind = frozenCarrier === "bibliographic-metadata" ? "def" : "assumption";
      const deferredCitation =
        node.gate && node.gate_class === "cited" && node.lean_kind === expectedDeferredKind;
      const provedCitation =
        frozenCarrier === "logical-claim" &&
        !node.gate && node.gate_class === undefined && node.citation_discharged === true &&
        node.disposition !== "reuse" &&
        (node.lean_kind === "lemma" || node.lean_kind === "theorem");
      if (!deferredCitation && !provedCitation) {
        violations.push({
          code: "P9",
          where: s.id,
          message:
            `core status:"cited" with source.carrier=${frozenCarrier} must map to a gate_class:"cited" ` +
            `${expectedDeferredKind} or to its ` +
            `proved form: a lemma/theorem with gate:false, no gate_class, citation_discharged:true and its source kept ` +
            `(got lean_kind=${node.lean_kind}, gate=${!!node.gate}, gate_class=${node.gate_class ?? "none"}, ` +
            `citation_discharged=${node.citation_discharged === true}) — re-laundering a citation`,
        });
      }
      if (provedCitation && opts.annotatedDecls) {
        const decls = opts.annotatedDecls.filter((decl) => decl.nodeId === s.id);
        const expectedName = node.lean_name.split(".").at(-1) ?? node.lean_name;
        const exact = decls.length === 1 ? decls[0] : undefined;
        const exactName = exact && (node.lean_name.includes(".")
          ? exact.declName === node.lean_name
          : (exact.declName.split(".").at(-1) ?? exact.declName) === expectedName);
        const exactKind = exact && exact.declKind === node.lean_kind;
        if (!exact || !exactName || !exactKind || (exact.hasSorry && !opts.proofsNotDue)) {
          violations.push({
            code: "P9",
            where: s.id,
            message:
              `discharged citation must map to exactly one sorry-free emitted ${node.lean_kind} ` +
              `'${node.lean_name}' (found ${decls.length}${exact ? `; decl=${exact.declName}, kind=${exact.declKind}, sorry=${exact.hasSorry}` : ""})`,
          });
        }
      }
      // (an undelivered cited gate has no declaration by design: P7 forbids its tag, P10 guards the mark)
      if (deferredCitation && opts.annotatedDecls && node.disposition !== "reuse" && node.delivery_status !== "undelivered") {
        const decls = opts.annotatedDecls.filter((decl) => decl.nodeId === s.id);
        const expectedName = node.lean_name.split(".").at(-1) ?? node.lean_name;
        const exact = decls.length === 1 ? decls[0] : undefined;
        const exactName = exact && (node.lean_name.includes(".")
          ? exact.declName === node.lean_name
          : (exact.declName.split(".").at(-1) ?? exact.declName) === expectedName);
        const exactDef = exact?.declKind === "def";
        // Carrier checks are deliberately syntactic and closed-world. In particular, "anything
        // other than the token Prop" is not a metadata type: `Sort 0` and aliases can elaborate
        // to Prop. Metadata therefore uses only the canonical text payloads supported by F2.
        // `Sort 0` is Lean's unshadowable proposition universe syntax. A bare `Prop`
        // identifier can be shadowed by a namespace-local alias and is therefore rejected.
        const isSyntacticProp = !!exact && /:\s*\(*\s*Sort\s+0\s*\)*\s*(?:--[^\n]*)?$/.test(exact.statement.trim());
        const isCanonicalMetadata = !!exact &&
          /:\s*\(*\s*(?:_root_\.String|_root_\.List\s+_root_\.String|_root_\.Array\s+_root_\.String)\s*\)*\s*(?:--[^\n]*)?$/.test(exact.statement.trim());
        const exactCarrier = frozenCarrier === "logical-claim"
          ? isSyntacticProp
          : isCanonicalMetadata && isDirectCanonicalMetadataPayload(exact);
        if (!exact || !exactName || !exactDef || !exactCarrier || exact.hasSorry) {
          violations.push({
            code: "P9",
            where: s.id,
            message:
              `deferred cited ${frozenCarrier} carrier must match one sorry-free emitted def named '${expectedName}' ` +
              `with ${frozenCarrier === "logical-claim" ? "the unshadowable proposition carrier Sort 0" : "a direct literal root-qualified _root_.String/_root_.List _root_.String/_root_.Array _root_.String metadata"} payload ` +
              `(found ${decls.length === 0 ? "none" : decls.map((decl) => `${decl.declKind} ${decl.declName}: ${decl.statement}`).join("; ")})`,
          });
        }
      }
      if (!node.source) {
        violations.push({ code: "P9", where: s.id, message: `cited node must set 'source' to a cite: id` });
      }
    } else if (node.gate_class === "cited") {
      violations.push({ code: "P9", where: s.id, message: `plan marks gate_class:"cited" but core status is '${s.status}' — F1 must not invent a citation` });
    }
  }
  for (const [id, n] of Object.entries(plan.nodes)) {
    if (n.source && !citationIds.has(n.source)) {
      violations.push({ code: "P9", where: id, message: `node 'source' '${n.source}' does not resolve to a citations[] entry` });
    }
  }

  // P10: `undelivered` is a narrow, disclosed presentation status — never a way
  // to hide a headline or a proof dependency. At F1 it is legal only for a cited
  // node: the planner cannot independently certify its own theorem as secondary
  // before the downstream role audit. It must be a leaf with
  // respect to every delivered statement, because a delivered result cannot rely
  // on an object that has no Lean declaration.
  const undeliveredIds = new Set(
    Object.entries(plan.nodes)
      .filter(([, n]) => n.delivery_status === "undelivered")
      .map(([id]) => id),
  );
  for (const id of undeliveredIds) {
    const node = plan.nodes[id];
    const stmt = core.statements.find((s) => s.id === id);
    const cited = !!stmt && stmt.status === "cited" && node.gate && node.gate_class === "cited";
    const reviewedSecondary =
      opts.allowReviewedSecondaryUndelivered === true &&
      stmt?.kind === "theorem" &&
      node.lean_kind === "theorem" &&
      node.delivery_role === "secondary";
    if (!cited && !reviewedSecondary) {
      violations.push({
        code: "P10",
        where: id,
        message:
          `F1 may mark only a cited node undelivered; paper-owned secondary classification requires downstream independent review ` +
          `(got kind=${stmt?.kind ?? "non-statement"}, role=${node.delivery_role ?? "none"}, cited=${cited})`,
      });
    }
    if (!node.delivery_reason) {
      violations.push({ code: "P10", where: id, message: `undelivered node must disclose a nonempty delivery_reason` });
    }
  }
  const statementById = new Map(core.statements.map((s) => [s.id, s] as const));
  for (const s of core.statements) {
    if (undeliveredIds.has(s.id)) continue;
    const seen = new Set<string>();
    const stack = [...s.depends_on];
    while (stack.length > 0) {
      const dep = stack.pop()!;
      if (seen.has(dep)) continue;
      seen.add(dep);
      if (undeliveredIds.has(dep)) {
        violations.push({
          code: "P10",
          where: s.id,
          message: `delivered statement transitively depends on undelivered node '${dep}'`,
        });
        break;
      }
      stack.push(...(statementById.get(dep)?.depends_on ?? []));
    }
  }

  return { ok: violations.length === 0, violations, notes };
}
