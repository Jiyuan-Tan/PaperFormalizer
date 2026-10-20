// F4 convergence receipts: what a dual-model verdict certifies, and when a later F4 round may
// reuse it instead of re-reviewing.
//
// Why: F4 used to re-review the FULL frozen surface with both peers on every entry — and an
// escalation-fix-resume cycle re-enters F4 several times per run, so each headline theorem was
// re-judged 5–10× at byte-identical text. Measured over five runs, a re-read of an unchanged,
// already dual-passed target flipped to a finding <2% of the time, while a SINGLE peer missed a
// third of all findings. So the safety lives in the second model, not in the repetition: keep the
// dual review, cache its result — but bind the cached verdict to everything that could change
// what the reviewer saw, and require BOTH peers at the same evidence before skipping.
//
// Evidence for a node target = reviewer rubric + the node's NL + its typed-core entry + its Lean
// anchor + the CLOSURE FINGERPRINT of the declaration the anchor names + the gated substrate
// hypotheses shown to the reviewer. The fingerprint is what Lean elaborated
// (`statement_fingerprints.ts`): the declaration's statement and that of every declaration of the
// toolkit package it reaches — agent-introduced and untagged helpers included, which the graph's
// `statement-uses` edges deliberately stop short of — so nothing of the source TEXT is hashed. An
// `open`, a notation, a `variable`, an instance or an option changes a receipt only through the
// term it makes Lean elaborate; a proof, a comment, a docstring (F5 writes them after F4) or an
// import never does. What binds a declaration to a target stays in the key by itself: the node's
// anchor (`@node`), a symbol's member list (`@realizes`). The rubric slot is the hand-bumped
// REVIEW_STANDARD token, NOT a hash of the prompt text or of the reviewer's source: a wording
// clarification or a refactor must not re-open every receipt. Bump it only when the review
// standard tightens.
//
// A target whose declaration has no fingerprint (the scan could not run, or reports no such
// declaration) has NO evidence: it is reviewed and never current. The one anchor expected outside
// the scan is a `library` node's, on a pinned library's declaration: it is keyed by name.
//
// Not cached here: undelivered (delivery-role) targets and `cited` gates — they already carry
// their own hash-bound per-peer receipts in state.json (`delivery_audit.ts`) and are re-reviewed
// every round; and symbol clusters with no `@realizes` member (the tag-reroute machinery owns them).

import { readFile } from "node:fs/promises";
import path from "node:path";
import type { Core } from "../core/schema.js";
import { statementHash } from "../graph/hash.js";
import { convergenceTargets } from "../graph/review_scope.js";
import {
  CONVERGENCE_PEERS,
  isUndeliveredNode,
  ConvergenceLedgerSchema,
  type ConvergenceLedger,
  type ConvergenceReceipt,
  type FormalizationGraph,
  type GraphNode,
} from "../graph/types.js";
import { buildSymbolClusters, type SymbolClusterMember } from "./crosswalk_semantics.js";
import { symbolInScope, verdictClass } from "./reviewer_verdicts.js";
import { fingerprintRows, fingerprintsInFile, resolveFingerprints, type DeclFingerprint, type StatementFingerprints } from "./statement_fingerprints.js";

// ---------------------------------------------------------------------------
// Evidence hashes
// ---------------------------------------------------------------------------

/** The reviewer standard a convergence receipt is issued under — an opaque version token, hashed
 *  into every node/symbol evidence hash. It replaced a hash of the reviewer prompt text and the
 *  reviewer's own source, which re-opened every verdict on a wording tweak or a refactor.
 *  Initial value is the hash the receipts carried on 2026-09-12 so existing receipts stay valid;
 *  bump to any new literal only when the review standard tightens (a receipt issued under the old
 *  standard would be wrong); prompt wording and code changes never bump it. */
export const REVIEW_STANDARD = "16865e36da9271bbf0e9906def5868e43c1ec0d8";

export function coreEntry(core: Core | null, nodeId: string): unknown {
  if (!core) return null;
  return (
    core.statements.find((s) => s.id === nodeId) ??
    core.definitions.find((d) => d.id === nodeId) ??
    core.assumptions.find((a) => a.id === nodeId) ??
    null
  );
}

/** The registered `gated` substrate hypotheses the reviewer is told to exempt for `nodeId`. */
export function gatedDeps(graph: FormalizationGraph, nodeId: string): [string, string | null, string][] {
  const byId = new Map(graph.nodes.map((n) => [n.id, n] as const));
  const out: [string, string | null, string][] = [];
  for (const e of graph.edges) {
    if (e.from !== nodeId || (e.kind !== "proof-uses" && e.kind !== "statement-uses")) continue;
    const g = byId.get(e.to);
    if (!g || g.kind !== "gate" || g.gate?.gate_class !== "gated") continue;
    out.push([g.id, g.lean.decl_name, g.nl.statement.trim()]);
  }
  return out.sort();
}

/** The fingerprints a node's evidence rests on: those of its anchor's declaration; none for a node
 *  with no anchor or a `library` node anchored outside the scan; null when the anchor's declaration
 *  has no fingerprint. */
function nodeFingerprints(fp: StatementFingerprints | null, n: GraphNode): DeclFingerprint[] | null {
  if (!fp) return null;
  if (!n.lean.decl_name) return [];
  const found = resolveFingerprints(fp, n.lean.decl_name, n.lean.file);
  return found.length > 0 || n.provenance === "library" ? found : null;
}

/** A node target's evidence hash; null when it has none (see the header) — the target is then
 *  reviewed, and no receipt can be current for it. */
export function nodeConvergenceEvidence(args: {
  graph: FormalizationGraph;
  fingerprints: StatementFingerprints | null;
  core: Core | null;
  rubricHash: string;
  nodeId: string;
}): string | null {
  const n = args.graph.nodes.find((x) => x.id === args.nodeId);
  if (!n) throw new Error(`convergence evidence: node ${JSON.stringify(args.nodeId)} is not in the graph`);
  const decls = nodeFingerprints(args.fingerprints, n);
  if (!decls) return null;
  return statementHash(JSON.stringify({
    rubric: args.rubricHash,
    id: n.id,
    kind: n.kind,
    provenance: n.provenance,
    nl: n.nl.statement.trim(),
    core: coreEntry(args.core, n.id),
    lean: n.lean,
    decls: fingerprintRows(decls),
    gated: gatedDeps(args.graph, n.id),
  }));
}

// ---------------------------------------------------------------------------
// Symbol-cluster rows (the `sym:<symbol>` review surface)
// ---------------------------------------------------------------------------

export interface SymbolReviewRow {
  id: string;
  /** The prompt row shown to the reviewer. */
  row: string;
  /** Hash of `evidenceRow` — the delta-mode `symbolReview` staleness key. */
  hash: string;
  /** Stable semantic row used by convergence receipts. The human-facing row includes optional
   *  hints and source line labels, both of which F5 documentation may change without changing
   *  the realization carrier. */
  evidenceRow: string;
  empty: boolean;
  members: SymbolClusterMember[];
}

/** Build the complete synthetic symbol-review surface once (reviewer + F5 audit share it). */
export async function buildSymbolReviewRows(
  leanDir: string,
  symbols: { name?: string; space?: string; type?: string; role?: string }[],
): Promise<SymbolReviewRow[]> {
  const syms = symbols
    .filter(symbolInScope)
    .map((s) => ({ name: s.name as string, space: (s.space || s.type) as string }));
  if (!syms.length) return [];
  const clusters = await buildSymbolClusters(leanDir, syms);
  return clusters.map((c) => {
    const head = `- sym:${c.symbol} : ${c.space ?? "(no space)"}`;
    const row = !c.members.length
      ? `${head}\n    realized_by: (UNTAGGED — no \`@realizes ${c.symbol}\` tag found. There is NO member to verify against, so the ONLY valid verdict is \`untagged\`: NEVER \`matched\`/\`equivalent\` (that is "verified against nothing", even for a computed quantity — def-by-construction needs a TAGGED def member) and NEVER \`drift\` (a missing tag is a tagging gap, not a mismatch). In your \`note\`, you MUST NAME the specific Lean decl that realizes this symbol — SEARCH the Lean dir (Grep/lean-lsp) for the \`def\` that computes it, the structure field that carries it, or the theorem/def binder/parameter that introduces it, and state the file + decl name. The scaffolder tags EXACTLY what you name, so a vague note ("tag the decls realizing X") is unactionable.)`
      : `${head}\n    realized_by (judge the CONJUNCTION of these):\n${c.members
          .map((m) => `      • ${m.decl} (${m.declKind}) in ${m.file}${m.hint ? `  — ${m.hint}` : ""}`)
          .join("\n")}`;
    // A declaration tagged twice for the symbol (its docstring and a trailing comment both carry
    // `@realizes`) is one member: the realization is the declarations, not how often they say so.
    const memberRows = c.members.map((m) => JSON.stringify({
      decl: m.declKind === "variable" ? "variable" : m.decl,
      declKind: m.declKind,
      file: m.file,
      codeAnchor: m.codeAnchor ?? null,
    }));
    const evidenceRow = JSON.stringify({
      symbol: c.symbol,
      space: c.space ?? null,
      members: memberRows.filter((r, i) => memberRows.indexOf(r) === i).map((r) => JSON.parse(r) as unknown),
    });
    return {
      id: `sym:${c.symbol}`,
      row,
      hash: statementHash(evidenceRow),
      evidenceRow,
      empty: !c.members.length,
      members: c.members,
    };
  });
}

/** A tagged symbol cluster's evidence hash; null when a member has no fingerprint. A standalone
 *  `variable` carrier is no declaration: it is read through every declaration of its file, whose
 *  statements are where its binder lands. */
export function symbolConvergenceEvidence(args: {
  fingerprints: StatementFingerprints | null;
  rubricHash: string;
  row: SymbolReviewRow;
}): string | null {
  const fp = args.fingerprints;
  if (!fp) return null;
  const decls: DeclFingerprint[] = [];
  for (const m of args.row.members) {
    const found = m.declKind === "variable" ? fingerprintsInFile(fp, m.file) : resolveFingerprints(fp, m.decl, m.file);
    if (found.length === 0) return null;
    decls.push(...found);
  }
  return statementHash(JSON.stringify({
    rubric: args.rubricHash,
    id: args.row.id,
    row: args.row.evidenceRow,
    decls: fingerprintRows(decls),
  }));
}

/** The delta-tier pass predicate for a stored symbol verdict (`untagged` clears the delta gate's
 *  "is there work?" check but is NOT a faithfulness pass). */
export const symbolVerdictPasses = (v: string): boolean => verdictClass(v) === "pass" && !/untagged/i.test(v);

// ---------------------------------------------------------------------------
// Receipts
// ---------------------------------------------------------------------------

/** Where a convergence pass keeps the dual receipts it has issued so far (`runs/<slug>/`): a pass
 *  that dies part-way (a worker timeout, a kill) leaves them for the next pass to reuse. */
export function partialReceiptsPath(runDir: string): string {
  return path.join(runDir, "convergence_partial.json");
}

/** The entries of `ledger` both peers passed (`matched`, on the same evidence): the only ones a
 *  later pass may reuse. Pure. */
export function dualMatchedReceipts(ledger: ConvergenceLedger): ConvergenceLedger {
  return Object.fromEntries(Object.entries(ledger).filter(([, r]) =>
    r.codex?.verdict === "matched" && r.claude?.verdict === "matched" && r.codex.evidence_hash === r.claude.evidence_hash));
}

/** The dual receipts an unfinished pass left behind; `{}` when there is no readable file. Each is
 *  bound to its evidence hash, so one issued on an older statement is simply never current. */
export async function loadPartialReceipts(runDir: string): Promise<ConvergenceLedger> {
  try {
    return dualMatchedReceipts(ConvergenceLedgerSchema.parse(JSON.parse(await readFile(partialReceiptsPath(runDir), "utf8"))));
  } catch {
    return {};
  }
}

/** True iff BOTH peers hold a `matched` receipt for `id` at exactly `evidenceHash`; never for a
 *  target with no evidence (null). */
export function dualClearedAt(ledger: ConvergenceLedger | undefined, id: string, evidenceHash: string | null): boolean {
  const entry = ledger?.[id];
  if (!entry || evidenceHash === null) return false;
  return CONVERGENCE_PEERS.every((peer) => {
    const r: ConvergenceReceipt | undefined = entry[peer];
    return r !== undefined && r.verdict === "matched" && r.evidence_hash === evidenceHash;
  });
}

/** The F4 node targets this ledger governs: the full convergence surface minus the targets that
 *  carry their own state.json receipts (undelivered nodes, `cited` gates). */
export function ledgerNodeTargets(graph: FormalizationGraph): string[] {
  const t = convergenceTargets(graph);
  const byId = new Map(graph.nodes.map((n) => [n.id, n] as const));
  const cited = (id: string): boolean => {
    const n = byId.get(id);
    return !!n && n.kind === "gate" && n.gate?.gate_class === "cited";
  };
  return [...t.statementTargets, ...t.definitionTargets, ...t.lemmaTargets, ...t.assumptionTargets].filter((id) => !cited(id));
}

export interface ConvergenceAuditFinding {
  code: "convergence-review";
  node_id?: string;
  message: string;
}

interface CurrentTree { graph: FormalizationGraph; leanDir: string; core: Core | null; fingerprints: StatementFingerprints | null }

/** Every governed target's current evidence hash (nodes and tagged symbol clusters); null for a
 *  target with none. */
export async function currentEvidence(args: CurrentTree): Promise<Map<string, string | null>> {
  const rubricHash = REVIEW_STANDARD;
  const out = new Map<string, string | null>();
  for (const id of ledgerNodeTargets(args.graph)) out.set(id, nodeConvergenceEvidence({ graph: args.graph, fingerprints: args.fingerprints, core: args.core, rubricHash, nodeId: id }));
  for (const row of await buildSymbolReviewRows(args.leanDir, args.core?.symbols ?? [])) {
    if (!row.empty) out.set(row.id, symbolConvergenceEvidence({ fingerprints: args.fingerprints, rubricHash, row }));
  }
  return out;
}

/** The targets both peers have passed on the Lean as it stands. */
export async function clearedTargets(args: CurrentTree): Promise<string[]> {
  const evidence = await currentEvidence(args);
  return [...evidence].filter(([id, h]) => dualClearedAt(args.graph.convergenceReview, id, h)).map(([id]) => id);
}

/**
 * Move the receipts of `ids` to the evidence of the Lean as it stands. Only for a change Lean has
 * certified leaves every statement as it was (a promotion's statement-invariance gate): the
 * reviewers' verdicts on those statements then hold under the names and anchors the change left. A
 * target no longer governed, or with no evidence now, keeps its entry untouched.
 */
export async function restampCleared(args: CurrentTree & { ids: readonly string[] }): Promise<{ graph: FormalizationGraph; restamped: string[] }> {
  // only a receipt both peers issued on the same evidence is a pass to carry
  const passed = dualMatchedReceipts(args.graph.convergenceReview ?? {});
  args = { ...args, ids: args.ids.filter((id) => id in passed) };
  const evidence = await currentEvidence(args);
  const ledger: ConvergenceLedger = { ...(args.graph.convergenceReview ?? {}) };
  const restamped: string[] = [];
  for (const id of args.ids) {
    const h = evidence.get(id);
    const entry = ledger[id];
    if (!h || !entry?.codex || !entry.claude) continue;
    if (entry.codex.evidence_hash === h && entry.claude.evidence_hash === h) continue;
    ledger[id] = { codex: { ...entry.codex, evidence_hash: h }, claude: { ...entry.claude, evidence_hash: h } };
    restamped.push(id);
  }
  return { graph: { ...args.graph, convergenceReview: ledger }, restamped };
}

/**
 * Re-verify the F4 ledger against the CURRENT tree: every governed node target must be delta-
 * `matched` and dual-receipted at its current evidence, and every tagged symbol cluster must be
 * delta-passed at its current row and dual-receipted at its current evidence. Run at F5,
 * so a skipped F4 target is never banked on a receipt the tree has outgrown.
 * `fingerprints` takes those of the tree as built now (`takeStatementFingerprints`; called only
 * when there is a target to verify); without them no receipt can be verified, and every governed
 * target is a finding.
 */
export async function auditConvergenceReview(args: {
  graph: FormalizationGraph;
  leanDir: string;
  core: Core;
  fingerprints: () => Promise<StatementFingerprints | null>;
}): Promise<ConvergenceAuditFinding[]> {
  const findings: ConvergenceAuditFinding[] = [];
  const nodeTargets = ledgerNodeTargets(args.graph);
  const rows = await buildSymbolReviewRows(args.leanDir, args.core.symbols ?? []);
  const taggedRows = rows.filter((row) => !row.empty);
  if (nodeTargets.length === 0 && taggedRows.length === 0) return findings;
  const rubricHash = REVIEW_STANDARD;
  const fingerprints = await args.fingerprints();
  const ledger = args.graph.convergenceReview;
  const byId = new Map(args.graph.nodes.map((n) => [n.id, n] as const));
  for (const id of nodeTargets) {
    const n = byId.get(id) as GraphNode;
    if (isUndeliveredNode(n)) continue;
    if (n.review.status !== "matched") {
      findings.push({ code: "convergence-review", node_id: id, message: `review status is ${n.review.status}, not matched` });
      continue;
    }
    const evidence = nodeConvergenceEvidence({ graph: args.graph, fingerprints, core: args.core, rubricHash, nodeId: id });
    if (!dualClearedAt(ledger, id, evidence)) {
      findings.push({ code: "convergence-review", node_id: id, message: describeMissing(ledger, id, evidence, fingerprints, n.lean.decl_name) });
    }
  }
  for (const row of taggedRows) {
    const prior = args.graph.symbolReview?.[row.id];
    if (!prior || prior.hash !== row.hash || !symbolVerdictPasses(prior.verdict)) {
      findings.push({ code: "convergence-review", node_id: row.id, message: `symbol cluster is not delta-cleared at its current realization` });
      continue;
    }
    const evidence = symbolConvergenceEvidence({ fingerprints, rubricHash, row });
    if (!dualClearedAt(ledger, row.id, evidence)) {
      findings.push({ code: "convergence-review", node_id: row.id, message: describeMissing(ledger, row.id, evidence, fingerprints, row.members.map((m) => m.decl).join(", ")) });
    }
  }
  return findings;
}

function describeMissing(ledger: ConvergenceLedger | undefined, id: string, evidence: string | null, fingerprints: StatementFingerprints | null, decls: string | null): string {
  const rerun = "re-run F4 (`--resume --from-stage F2.5`)";
  // The receipts may well be current: they could not be checked. A resume re-takes the fingerprints.
  if (!fingerprints) return "no statement fingerprints for the built tree (the build or candidate_scan did not finish; see the [f4] log line) — fix that if it is not transient, then resume (F4 is not re-run)";
  if (evidence === null) return `Lean elaborated no declaration its anchor names (${decls ?? "no anchor"}): the receipt cannot be bound — repair the anchor, then ${rerun}`;
  const entry = ledger?.[id];
  const parts = CONVERGENCE_PEERS.map((peer) => {
    const r = entry?.[peer];
    if (!r) return `${peer}: no F4 receipt`;
    if (r.verdict !== "matched") return `${peer}: ${r.verdict}${r.note ? ` (${r.note})` : ""}`;
    if (r.evidence_hash !== evidence) return `${peer}: receipt is stale for the current statement/dependency/rubric evidence`;
    return `${peer}: ok`;
  });
  return `${parts.join("; ")} — ${rerun}`;
}
