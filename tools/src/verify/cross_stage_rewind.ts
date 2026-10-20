/**
 * F-stage rewinds into V1 patch mode — "rewinds revise, they never rebuild" (user decision
 * 2026-09-23) — PROPOSED by the runner, APPROVED by the orchestrator (user decision 2026-09-23).
 *
 * The paper's mathematics is the user's and is never re-derived, so an F-stage reviewer that finds
 * the paper lacks a hypothesis or is wrong as stated is answered by
 * the minimal-patch loop V1.5 already drives: the finding
 * becomes a PATCH DIRECTIVE on the statement it names — the same `v1_revise_directive.json`
 * (`mode: "patch"`) a V1.5 `error` writes — the run re-enters V1 in patch mode, the fixer extends
 * `patches.json`, V1 rebuilds `core.json` mechanically, V1.5 re-grades only what changed, and F1
 * re-plans. A `correctness` rewind spends an error round (charged to `global`, `MAX_PATCH_ROUNDS_PER_LEVEL`), a `clarify` rewind a
 * refinement round (`MAX_REFINEMENT_ROUNDS`); a round due at its cap halts (`caps.ts`).
 *
 * The F2.5–F4 proof-review escalations leave such a receipt (an F1.5 one, route `stage_0` /
 * `stage_neg1`, is on file only in runs from before 2026-10-07): those that assert a defect in a PAPER statement
 * (`proofReviewRewindAxis`): `fix-source` with kind `statement-wrong`, and `unclear` when the
 * statement's wording is what is unclear (the filler's `ambiguous-spec`, or a reviewer's
 * `unadjudicable` that says the statement admits several readings). A finding that names a Lean
 * declaration rather than a statement of the core, a witnessed refutation of an agent-added helper
 * (`redo-math`) and every workflow route keep halting as before. The fixer's axis is
 * `correctness` for a wrong claim and `clarify` for an ambiguity — a clarification writes the
 * intended reading INTO the statement, folding any reading the referee had pinned on it
 * (`FoldedReading`), and is recorded in the ledger as a clarification, not an error.
 *
 * A finding may name an ASSUMPTION or DEFINITION of the core rather than a statement: the
 * directive then carries one finding on that node, naming the statements that use it, and the
 * fixer repairs it by replacing its own printed text, or — stated only in running prose —
 * restates each result using it (`hypothesisRepairLine`). Only a name that is no node of the core
 * (a Lean declaration) is refused.
 *
 * One receipt carries EVERY paper-statement finding of one review pass (`targets`; the F2.5
 * delta reviewers run per node in parallel, so a pass can find several): they are presented
 * together, approved or rejected together, and spend ONE round — an error round when any target
 * is a `correctness` finding, else a refinement round. The fixer gets one directive listing them
 * all, and V1.5's delta then re-grades their union.
 *
 * The receipt (`state.verify.cross_stage_rewind`, recorded `pending` by the F runner) is never
 * acted on silently. The runner PRESENTS it (`presentPendingRewind`: the finding, the statement,
 * the axis and the two ways forward) and halts, in every mode (auto mode too: the orchestrator
 * skill judges). A plain `--resume` approves it (`applyPendingRewind`: the directive is written and
 * the receipt marked `applied`, so a resume never applies it twice); `--resume --reject-rewind
 * "<reason>"` rejects it (`rejectPendingRewind`: the receipt, the ruled-out list and a note on the
 * statement record why, and the F stages continue from where they halted). The same finding again
 * on the same node (the same axis) is then a note, not a halt. A receipt naming no node of the
 * core is `refused` at once (nothing to route; the run halts as before).
 */
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import type { Core } from "../core/schema.js";
import { parseTypedCore } from "../core/core_io.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import { resetForNewCore } from "../formalization/loop_limits.js";
import type { StateJson } from "../types.js";
import { atCap, capRecord, countRound, errorScope, nextRound, roundsUsed } from "./caps.js";
import { bindingReadings, pinsOn, renderBindingReadings } from "./core_graph.js";

/** A referee-pinned reading a clarification writes into its statement: the node whose reading was
 * pinned, and the reading. */
type FoldedReading = { node: string; reading: string };
import { recordVerifyFinding } from "./findings.js";
import { readPatchFile } from "./patches.js";
import { VERIFY_FILES, type CrossStageRewind, type PatchRoundKind, type RejectedRewind, type RewindTarget, type VerifyState } from "./types.js";

/** Wording by which a reviewer says a statement admits more than one reading. */
const AMBIGUITY_TEXT =
  /\bambigu|\breadings?\b|\binterpretations?\b|under-?specif|\bunspecified\b|\bspecify\b|admits (?:both|two|more than one)|permits both/i;

/**
 * Does an F2.5–F4 proof-review escalation assert a defect in a PAPER statement, and on which
 * fixer axis? `fix-source` with kind `statement-wrong` (the reviewer's or the filler's): `clarify`
 * when the reason says the statement admits several readings, else `correctness`; with kind
 * `claim-false` (the frozen claim refuted by a witness): `correctness`. `unclear`: only
 * when the unclarity is the statement's — the filler's `ambiguous-spec`, or a reviewer's
 * `unadjudicable` whose reason says the statement admits several readings (a reviewer that could
 * not judge for want of Lean evidence, or a mechanical fault, places no fault on the paper).
 * `null`: not a paper-statement route — the run halts as before. Whether the node it names is a
 * node of the core is checked when the receipt is presented.
 */
export function proofReviewRewindAxis(e: { route: string; reason: string; kind?: string }): "correctness" | "clarify" | null {
  const kind = e.kind ?? /^\[([a-z0-9-]+)\]/.exec(e.reason)?.[1];
  const text = e.reason.replace(/^\[[a-z0-9-]+\]\s*/, "");
  if (e.route === "fix-source" && kind === "statement-wrong") return AMBIGUITY_TEXT.test(text) ? "clarify" : "correctness";
  if (e.route === "fix-source" && kind === "claim-false") return "correctness";
  if (e.route === "unclear" && (kind === "ambiguous-spec" || (kind === "unadjudicable" && AMBIGUITY_TEXT.test(text)))) return "clarify";
  return null;
}

type Flag = NonNullable<StateJson["flags"]["proof_review_escalation_pending"]>;

/**
 * The receipt for a proof-review escalation (`state.flags.proof_review_escalation_pending`), when
 * it asserts a defect in a paper statement; `null` otherwise. Its `targets` are every
 * paper-statement finding of the pass (`flag.batch`, else the flag itself). The F runner records
 * it at the escalation (`dispatcher.ts`); the verify runner derives it again at formalization
 * entry for a flag left without one (an older run, or a crash between the two writes).
 */
export function proofReviewRewind(flag: Flag): CrossStageRewind | null {
  const targets: RewindTarget[] = [];
  for (const e of flag.batch?.length ? flag.batch : [flag]) {
    const axis = proofReviewRewindAxis(e);
    if (!axis || (e.route !== "fix-source" && e.route !== "unclear")) continue;
    if (targets.some((t) => t.obj_id === e.obj_id && t.reason === e.reason)) continue;
    targets.push({ ...(e.obj_id ? { obj_id: e.obj_id } : {}), ...(e.kind ? { kind: e.kind } : {}), route: e.route, axis, reason: e.reason });
  }
  const first = targets[0];
  if (!first) return null;
  return {
    ...pendingRewind(`F${flag.phase ?? "2.5"}`, first.route!, targets.map((t) => t.reason).join("\n")),
    axis: batchAxis(targets),
    ...(first.kind ? { kind: first.kind } : {}),
    ...(first.obj_id ? { target: first.obj_id } : {}),
    targets,
  };
}

/**
 * Record the receipt for a pending proof-review escalation that has none yet. `false` when there
 * is nothing to record: no escalation, not a paper-statement route, or this escalation already
 * has its receipt (pending, applied or refused — a refused one is never retried by a resume).
 */
export function recordProofReviewRewind(state: StateJson): boolean {
  const flag = state.flags.proof_review_escalation_pending;
  if (!flag || !state.verify) return false;
  const rec = proofReviewRewind(flag);
  if (!rec) return false;
  const prev = state.verify.cross_stage_rewind;
  // One receipt per escalation. A REJECTED one is the exception: the same escalation raised again
  // after the rejection gets a fresh receipt, which the runner then turns into a note (a repeat).
  if (prev && prev.route === rec.route && prev.detail === rec.detail && prev.status !== "rejected") return false;
  state.verify.cross_stage_rewind = rec;
  return true;
}

/** A receipt's findings: `targets`, or the one finding a receipt without them stands for. */
export function receiptTargets(rec: CrossStageRewind): RewindTarget[] {
  if (rec.targets) return rec.targets;
  return [{
    ...(rec.target ? { obj_id: rec.target } : {}),
    ...(rec.kind ? { kind: rec.kind } : {}),
    route: rec.route,
    axis: rec.axis ?? "correctness",
    reason: rec.detail,
  }];
}

/** A batch spends an error round when any finding is a wrong claim, else a refinement round. */
function batchAxis(targets: readonly RewindTarget[]): "correctness" | "clarify" {
  return targets.some((t) => t.axis === "correctness") ? "correctness" : "clarify";
}

/**
 * The core statement an F-stage finding is about: the first statement id the text names (a
 * reviewer's `thm::x` typo is read as `thm:x`), else the first `T-k` / `L-k` graph alias that maps
 * to a statement. One statement only — the fixer must patch or declare unfixable every node a
 * directive names, so a statement merely mentioned in passing must never be put in front of it.
 */
export function rewindTarget(core: Core, text: string, objIds: ReadonlyMap<string, string> = new Map()): string | null {
  const statements = new Set(core.statements.map((s) => s.id));
  // Any `<prefix>:<name>` the text names is tried against the core's own statement ids, so every
  // statement kind the schema admits (`oeq:`, `conj:`, …) is found and nothing else is.
  for (const m of text.matchAll(/\b([a-z]+)::?([a-z0-9]+(?:-[a-z0-9]+)*)/g)) {
    const id = `${m[1]}:${m[2]}`;
    if (statements.has(id)) return id;
  }
  for (const m of text.matchAll(/\b[TL]-\d+\b/g)) {
    const id = objIds.get(m[0]);
    if (id && statements.has(id)) return id;
  }
  return null;
}

/** `obj_id` (`T-3`) → core id (`thm:x`) from the run's formalization graph, when there is one. */
async function graphAliases(runDir: string): Promise<Map<string, string>> {
  const out = new Map<string, string>();
  for (const p of [path.join(runDir, "graph.json"), path.join(runDir, "formalization", "graph.json")]) {
    if (!existsSync(p)) continue;
    try {
      const g = JSON.parse(await readFile(p, "utf8")) as { nodes?: Array<{ id?: string; obj_id?: string }> };
      for (const n of g.nodes ?? []) if (n.id && n.obj_id) out.set(n.obj_id, n.id);
    } catch {
      // an unreadable graph only loses the alias fallback
    }
    break;
  }
  return out;
}

/** The fixer's axis of a receipt (of its round, for a batch). */
export function rewindAxis(rec: CrossStageRewind): "correctness" | "clarify" {
  return rec.targets ? batchAxis(rec.targets) : (rec.axis ?? "correctness");
}

/**
 * The statements that use assumption or definition `id`: those whose `depends_on` names it, or
 * names a class definition it carves (`by_member_properties`). In core order.
 */
export function hypothesisUsers(core: Core, id: string): string[] {
  const carved = new Set(core.definitions.filter((d) => (d.by_member_properties ?? []).includes(id)).map((d) => d.id));
  return core.statements.filter((s) => s.depends_on.some((d) => d === id || carved.has(d))).map((s) => s.id);
}

/** How the fixer repairs a finding on the paper's assumption or definition `id` (null: `id` is not
 * one, or no statement uses it) — the ONE wording V1.5 and an F-stage rewind give. */
export function hypothesisRepairLine(core: Core, id: string): string | null {
  const what = core.assumptions.some((a) => a.id === id) ? "hypothesis" : core.definitions.some((d) => d.id === id) ? "definition" : null;
  const users = what ? hypothesisUsers(core, id) : [];
  if (!what || users.length === 0) return null;
  return (
    `This ${what} of the paper is used by ${users.join(", ")}. Repair it by replacing its own printed text; ` +
    "when the paper states it in running prose or inside a result's statement (no units of its own), restate each result using it instead " +
    "(in that result's own repair when it has a finding, else a patch with `consequence_of`) and give this node a patch with no ops " +
    "(`gives_up` null: what a restatement gives up is stated on the result)."
  );
}

/** One finding resolved against the core: the node it is about and the statements to patch. */
export function resolveTarget(core: Core, t: RewindTarget, aliases: ReadonlyMap<string, string> = new Map()): RewindTarget {
  const { node: _n, node_kind: _k, users: _u, why: _w, ...base } = t;
  const status = t.status === "repeat" ? "repeat" : undefined;
  if (t.obj_id) {
    const id = aliases.get(t.obj_id) ?? t.obj_id;
    if (core.statements.some((s) => s.id === id)) return { ...base, node: id, node_kind: "statement", users: [id], status: status ?? "routed" };
    // A condition the referee added (a bookkeeping condition, a pinned reading) is no text of the
    // paper and no node the fixer can patch: a finding on it is a finding on the results carrying
    // it, each restated with the condition settled.
    const added = core.assumptions.find((a) => a.id === id && a.bookkeeping);
    if (added) {
      const users = hypothesisUsers(core, id);
      if (users.length > 0) return { ...base, node: users[0], node_kind: "statement", users, status: status ?? "routed" };
    }
    const nodeKind = core.assumptions.some((a) => a.id === id) ? "assumption" : core.definitions.some((d) => d.id === id) ? "definition" : null;
    if (nodeKind) {
      const users = hypothesisUsers(core, id);
      return users.length > 0
        ? { ...base, node: id, node_kind: nodeKind, users, status: status ?? "routed" }
        : { ...base, node: id, node_kind: nodeKind, status: "refused", why: `the finding names ${t.obj_id}, a${nodeKind === "assumption" ? "n assumption" : " definition"} no statement of the core uses` };
    }
    // A Lean declaration, or any name that is no node of the core: nothing the fixer can patch.
    return { ...base, status: "refused", why: `the finding names ${t.obj_id}, which is not a node of the core (a Lean-side finding, or no statement the fixer could patch)` };
  }
  const node = rewindTarget(core, t.reason, aliases);
  return node
    ? { ...base, node, node_kind: "statement", users: [node], status: status ?? "routed" }
    : { ...base, status: "refused", why: "the finding names no statement of the core the fixer could patch" };
}

/** Every finding of a receipt resolved against the run's core, or why none can be. */
export async function resolveRewindTargets(runDir: string, rec: CrossStageRewind): Promise<{ targets: RewindTarget[]; core: Core } | { why: string }> {
  const corePath = path.join(runDir, VERIFY_FILES.coreJson);
  if (!existsSync(corePath)) return { why: `${VERIFY_FILES.coreJson} is missing` };
  const core = parseTypedCore(await readFile(corePath, "utf8"), `verify core ${corePath}`);
  const aliases = await graphAliases(runDir);
  return { targets: receiptTargets(rec).map((t) => resolveTarget(core, t, aliases)), core };
}

function refusedWhy(targets: readonly RewindTarget[]): string {
  if (targets.length === 0) return "the receipt lists no finding";
  return targets.map((t) => t.why ?? `${t.node ?? t.obj_id ?? "?"} is a repeat of a ruled-out finding`).join("; ");
}

/** The statements a set of resolved findings sends to the fixer, deduplicated, in order. */
function routedStatements(targets: readonly RewindTarget[]): string[] {
  return [...new Set(targets.filter((t) => t.status === "routed").flatMap((t) => t.users ?? []))];
}

/** How a resolved finding reads in a message: `statement thm:x` / `hypothesis ass:y (used by …)`. */
function describeTarget(t: RewindTarget): string {
  if (t.node_kind === "statement") return `statement ${t.node}`;
  const what = t.node_kind === "definition" ? "definition" : "hypothesis";
  return `${what} ${t.node} (used by ${(t.users ?? []).join(", ")})`;
}

/** The words of a finding: its `[tag]` prefixes, TeX commands and punctuation dropped, lower-cased. */
function findingWords(text: string): Set<string> {
  const plain = text.replace(/^\s*(\[[^\]]*\]\s*)+/, "").replace(/\\[A-Za-z]+/g, " ").toLowerCase();
  return new Set(plain.match(/[\p{L}\p{N}_]+/gu) ?? []);
}

/** How much two findings' word sets share (Jaccard) for a new one to count as the ruled-out one
 * raised again. A near-verbatim re-raise (an escalation re-recorded on resume, a reworded tag)
 * passes; a different complaint on the same node and axis does not. */
export const REPEAT_OVERLAP = 0.8;

/** Whether finding `a` is finding `b` raised again (`REPEAT_OVERLAP`). */
export function sameFinding(a: string, b: string): boolean {
  const x = findingWords(a);
  const y = findingWords(b);
  if (x.size === 0 || y.size === 0) return x.size === y.size;
  let shared = 0;
  for (const w of x) if (y.has(w)) shared += 1;
  return shared / (x.size + y.size - shared) >= REPEAT_OVERLAP;
}

/** The ruled-out finding a new one on `node` repeats: the same node and axis, and — on the
 * correctness axis — the same finding by content (`sameFinding`), so a different claimed error on a
 * node that once had one ruled out goes to the orchestrator like any other. On the clarify axis the
 * node and axis suffice: the ruling already says how the statement is meant, the reviewer is shown
 * it, and a reworded "which reading?" on the same statement is the same question (word overlap
 * misses a rewording; the repeat is still recorded as a note, never dropped). */
export function rejectedMatch(verify: VerifyState, node: string, axis: RejectedRewind["axis"], detail: string): RejectedRewind | undefined {
  return (verify.rejected_rewinds ?? []).find(
    (r) => r.node === node && r.axis === axis && (axis === "clarify" || sameFinding(r.detail, detail)),
  );
}

/** The nodes whose rulings bind a reviewer's target: the target, what it uses, and — for a
 * hypothesis, definition or pinned reading — the results using it: a finding on a condition is
 * routed to (and ruled on) the results carrying it (`resolveTarget`), so that is where its ruling is. */
export function ruledOutScope(statements: readonly { id: string; depends_on?: readonly string[] }[], id: string): string[] {
  const own = statements.find((st) => st.id === id)?.depends_on ?? [];
  const users = statements.filter((st) => st.depends_on?.includes(id)).map((st) => st.id);
  return [...new Set([id, ...own, ...users])];
}

/** For a reviewer's target: the findings already ruled out on `nodes` (the target and the hypotheses
 * and definitions it uses), with the ruling — or "". A reviewer that is not shown a ruling raises the
 * same point again in other words, which no word-overlap match catches. */
export function renderRuledOut(rejected: readonly RejectedRewind[] | undefined, nodes: readonly string[]): string {
  const on = (rejected ?? []).filter((r) => nodes.includes(r.node));
  if (on.length === 0) return "";
  return [
    "Already ruled out (binding — checked against the paper; do not raise it again, and judge the Lean under the ruling):",
    ...on.map((r) => `  • ${r.node}: ${r.detail.replace(/\s+/g, " ").trim()} — RULING (${r.by}): ${r.reason.replace(/\s+/g, " ").trim()}`),
  ].join("\n");
}

export type PresentOutcome =
  | { kind: "refused"; message: string }
  | { kind: "repeat"; node: string; message: string }
  | { kind: "present"; node: string; nodes: string[]; message: string };

/** Demote the `unresolved` F finding a receipt target recorded to a note on `node`. */
function demoteFinding(state: StateJson, stage: string, reason: string, node: string, note: string): boolean {
  let demoted = false;
  for (const f of state.verify!.findings) {
    if (f.stage === stage && f.kind === "unresolved" && f.detail === reason) {
      f.kind = "note";
      f.node = node;
      f.detail = note;
      demoted = true;
    }
  }
  return demoted;
}

/**
 * First sight of a `pending` receipt. Every finding is resolved against the core. `refused` when
 * none names a node of the core (the run halts as before, with the findings in the report);
 * `repeat` when every routable finding repeats one ruled out before (recorded as notes; the F
 * stages continue); otherwise the receipt is marked `presented` — its refused and repeated
 * findings left out and listed — and the message is what the orchestrator must rule on. The
 * caller persists the state and halts on `present` / `refused`.
 */
export async function presentPendingRewind(args: { runDir: string; state: StateJson; input: string }): Promise<PresentOutcome> {
  const verify = args.state.verify!;
  const rec = verify.cross_stage_rewind!;
  const resolved = await resolveRewindTargets(args.runDir, rec);
  if ("why" in resolved) {
    verify.cross_stage_rewind = { ...rec, status: "refused", why: resolved.why };
    return { kind: "refused", message: `${rec.stage} ${rec.route} finding not routed to V1 patch mode: ${resolved.why}` };
  }
  const targets = resolved.targets;
  if (!targets.some((t) => t.status === "routed")) {
    const why = refusedWhy(targets);
    verify.cross_stage_rewind = { ...rec, targets: rec.targets ? targets : undefined, status: "refused", why };
    return { kind: "refused", message: `${rec.stage} ${rec.route} finding not routed to V1 patch mode: ${why}` };
  }
  // A finding ruled out before (same node, same axis, same finding by content) is a note, not a question.
  const repeats: string[] = [];
  for (const t of targets) {
    if (t.status !== "routed") continue;
    const prior = rejectedMatch(verify, t.node!, t.axis, t.reason);
    if (!prior) continue;
    const reason = `repeats the ${prior.stage} finding on ${t.node} ruled out by the ${prior.by} (${prior.at}): ${prior.reason}`;
    t.status = "repeat";
    t.why = reason;
    const note = `${t.reason}\n(a repeat of a ruled-out finding on ${t.node}: ${reason})`;
    if (!demoteFinding(args.state, rec.stage, t.reason, t.node!, note)) {
      recordVerifyFinding(args.state, { node: t.node!, stage: rec.stage, kind: "note", detail: note, witness: null });
    }
    repeats.push(`${rec.stage} ${t.route ?? rec.route} finding on ${t.node} (${t.axis}) ${reason}`);
  }
  const routed = targets.filter((t) => t.status === "routed");
  if (routed.length === 0) {
    const first = targets.find((t) => t.status === "repeat")!;
    verify.cross_stage_rewind = { ...rec, targets: rec.targets ? targets : undefined, status: "rejected", rejected_reason: first.why, nodes: [first.node!] };
    liftHaltFlags(args.state, rec);
    return { kind: "repeat", node: first.node!, message: `${repeats.join("\n")} — recorded as a note; the F stages continue.` };
  }
  const nodes = routedStatements(targets);
  const axis = batchAxis(routed);
  verify.cross_stage_rewind = { ...rec, ...(rec.targets ? { targets } : {}), axis: rec.targets ? axis : rec.axis, presented: true, nodes };
  const kind: PatchRoundKind = axis === "clarify" ? "refinement" : "error";
  const scope = kind === "error" ? errorScope(verify, resolved.core, null) : null;
  const repairOf = (t: RewindTarget): string =>
    t.node_kind !== "statement"
      ? `the fixer ${t.axis === "clarify" ? "clarifies" : "corrects"} ${t.node} where it is used (a replacement hypothesis wired into ${(t.users ?? []).join(", ")}, or a corrected statement)`
      : t.axis === "clarify"
        ? "the fixer writes the intended reading into the statement (any reading the referee pinned on it is folded into the text)"
        : "the fixer writes the smallest repair of the statement (a corrected statement or the weakest missing hypothesis)";
  // A clarification on a node that has pinned readings: show them, since a pinned reading binds and
  // a finding it settles is a Lean-side fix, not a defect of the paper.
  const pinnedNote = (t: RewindTarget): string => {
    if (t.axis !== "clarify" || !t.node) return "";
    const pinned = renderBindingReadings(bindingReadings(resolved.core, t.node));
    return pinned ? `\n     ${pinned} — reject the finding if one of them settles it` : "";
  };
  const line = (t: RewindTarget): string =>
    `route ${t.route ?? rec.route}${t.kind ? ` [${t.kind}]` : ""}, ${describeTarget(t)}, axis ${t.axis}`;
  const one = routed.length === 1 ? routed[0]! : null;
  const findingsBlock = one
    ? `  stage ${rec.stage}, ${line(one)}\n  finding: ${one.reason.replace(/\s+/g, " ")}${pinnedNote(one).replace(/\n     /, "\n  ")}\n  proposed repair: ${repairOf(one)}; it would be ${nextRound(verify, kind, scope)}.\n`
    : `  stage ${rec.stage}: ${routed.length} findings of one review pass, ruled on together — one ${nextRound(verify, kind, scope)}, one directive:\n` +
      routed.map((t, i) => `  ${i + 1}. ${line(t)}\n     finding: ${t.reason.replace(/\s+/g, " ")}${pinnedNote(t)}\n     proposed repair: ${repairOf(t)}`).join("\n") + "\n";
  const left = targets.filter((t) => t.status !== "routed");
  const leftBlock = left.length
    ? `  left out of the batch (${left.length}):\n${left.map((t) => `    - ${t.node ?? t.obj_id ?? "?"}: ${t.why}`).join("\n")}\n`
    : "";
  const message =
    `F-STAGE REWIND PROPOSED — the orchestrator decides (in every mode, auto mode included).\n` +
    findingsBlock +
    leftBlock +
    `  Continue with one of:\n` +
    `    leansmith verify ${args.input} --resume                              (approve${one ? "" : " all"}: V1 patch mode on ${nodes.join(", ")}, then V1.5, then F1 re-plans)\n` +
    `    leansmith verify ${args.input} --resume --reject-rewind "<reason>"   (reject${one ? "" : " all"}: the paper is right as stated — say where it grants this; the F stages continue)\n` +
    `    leansmith verify ${args.input} --resume --reject-finding "<reading>" (the finding${one ? "" : "s"} misread${one ? "s" : ""} the paper: withdrawn, the statement stands under the reading you give, pinned into the core and binding for the formalization; V1.5 re-grades, F1 re-plans)\n` +
    (one ? "" : `  To approve only some findings, delete the others from state.verify.cross_stage_rewind.targets, then --resume.\n`) +
    `  (with the --toolkit / --slug / --dry-run the run was started with)`;
  return { kind: "present", node: nodes[0]!, nodes, message };
}

/** Lift the flags that halted the F runner on a receipt, so it continues from where it stopped. */
export function liftHaltFlags(state: StateJson, rec: CrossStageRewind): void {
  if (rec.route === "fix-source" || rec.route === "unclear") state.flags.proof_review_escalation_pending = null;
  state.flags.verify_no_d_rewind = null;
}

/**
 * Rule out a pending receipt: the orchestrator's `--reject-rewind` (one decision for the whole
 * batch). The receipt says `rejected` and why; each finding joins the ruled-out list under the
 * node it names; each F-stage finding becomes a note on its node; the flags that halted the F
 * runner are lifted, so it continues from where it stopped (F2.5 re-enters the proof-review loop
 * with its budgets as they were; F1.5 reviews again). `fallbackNode` names a finding the receipt
 * never resolved (no core at presentation).
 */
export function rejectPendingRewind(state: StateJson, reason: string, fallbackNode = "run", by: "orchestrator" | "owner" = "orchestrator"): void {
  const verify = state.verify!;
  const rec = verify.cross_stage_rewind!;
  const at = new Date().toISOString();
  const targets = receiptTargets(rec).filter((t) => t.status !== "refused" && t.status !== "repeat");
  const legacyNode = rec.nodes?.[0] ?? rec.target ?? fallbackNode;
  const nodeOf = (t: RewindTarget): string => t.node ?? (rec.targets ? (t.obj_id ?? fallbackNode) : legacyNode);
  verify.cross_stage_rewind = { ...rec, status: "rejected", rejected_reason: reason, nodes: rec.nodes ?? [legacyNode] };
  for (const t of targets) {
    const node = nodeOf(t);
    verify.rejected_rewinds = [
      ...(verify.rejected_rewinds ?? []),
      { node, axis: t.axis, stage: rec.stage, route: t.route ?? rec.route, detail: t.reason, reason, by, at },
    ];
    const note = `${t.reason}\n(${by === "owner" ? "finding withdrawn by the paper's owner" : "rewind rejected by the orchestrator"} on ${node}: ${reason})`;
    if (!demoteFinding(state, rec.stage, t.reason, node, note)) {
      recordVerifyFinding(state, { node, stage: rec.stage, kind: "note", detail: note, witness: null });
    }
  }
  liftHaltFlags(state, rec);
}

export type RewindOutcome =
  | { applied: true; node: string; nodes: string[]; round: number; message: string }
  | { applied: false; capped?: boolean; message: string };

type DirectiveFinding = {
  id: string;
  axis: "correctness" | "clarify";
  detail: string;
  witness: string | null;
  from_stage: string;
  folds?: FoldedReading[];
};

/**
 * The directive findings for the routed findings of a receipt: one per node. A statement finding
 * goes to its statement (a clarification carrying the readings the referee pinned on it); an
 * assumption or definition finding goes to that node, naming the statements using it
 * (`hypothesisRepairLine`). Two findings on one node merge into one entry (the fixer answers each
 * node once).
 */
export function directiveFindings(core: Core, stage: string, targets: readonly RewindTarget[]): DirectiveFinding[] {
  const byId = new Map<string, DirectiveFinding>();
  for (const t of targets) {
    if (t.status !== "routed") continue;
    const tag = `[${stage} reviewer]`;
    for (const u of t.node_kind === "statement" ? (t.users ?? []) : [t.node!]) {
      let f: DirectiveFinding;
      if (t.node_kind === "statement") {
        // A clarification folds the readings the referee pinned on the statement: they go to the
        // fixer to be written into the statement text, and the patch then carries them.
        const folds: FoldedReading[] = t.axis === "clarify" ? pinsOn(core, u).map((p) => ({ node: p.node, reading: p.reading })) : [];
        f = {
          id: u,
          axis: t.axis,
          detail:
            `${tag} ${t.reason}` +
            (folds.length > 0
              ? `\nReading(s) the referee pinned for this statement, to be written into it: ${folds.map((x) => `${x.reading} (the reading of ${x.node})`).join("; ")}`
              : ""),
          witness: t.axis === "clarify" ? null : t.reason,
          from_stage: stage,
          ...(folds.length > 0 ? { folds } : {}),
        };
      } else {
        f = {
          id: u,
          axis: t.axis,
          detail: `${tag} ${t.reason}\n${hypothesisRepairLine(core, u) ?? ""}`.trim(),
          witness: t.axis === "clarify" ? null : t.reason,
          from_stage: stage,
        };
      }
      const prev = byId.get(u);
      if (!prev) {
        byId.set(u, f);
        continue;
      }
      byId.set(u, {
        ...prev,
        axis: prev.axis === "correctness" || f.axis === "correctness" ? "correctness" : "clarify",
        detail: `${prev.detail}\n${f.detail}`,
        witness: [prev.witness, f.witness].filter(Boolean).join("\n") || null,
        ...(prev.folds || f.folds ? { folds: [...(prev.folds ?? []), ...(f.folds ?? [])] } : {}),
      });
    }
  }
  return [...byId.values()];
}

/**
 * Apply an APPROVED `pending` receipt — every finding it still lists, as one round. Applied: the
 * patch directive is written (merged into a pending one, deduplicated, so a crash between the
 * write and the state save re-applies nothing new), ONE round of the batch's kind is counted,
 * the cursor goes back to V1 (the transcription stands; V1.5 must accept the patched core
 * afresh), the refused-rewind flag is lifted and each routed F-stage finding becomes a note (the
 * ledger entry patch mode records carries the error from here on). Capped: the round's counter is
 * at its cap — `state.verify.cap_reached` is recorded and the receipt stays pending
 * (`--clear-patch-cap` then routes it). Refused: no finding names a node of the core; the receipt
 * says why and the run halts where the F runner stopped. The caller persists the state.
 */
export async function applyPendingRewind(args: { runDir: string; state: StateJson }): Promise<RewindOutcome> {
  const { runDir, state } = args;
  const verify = state.verify!;
  const rec = verify.cross_stage_rewind;
  if (!rec || rec.status !== "pending") return { applied: false, message: "no pending F-stage rewind" };
  const resolved = await resolveRewindTargets(runDir, rec);
  if ("why" in resolved) {
    verify.cross_stage_rewind = { ...rec, status: "refused", why: resolved.why };
    return { applied: false, message: `${rec.stage} ${rec.route} finding not routed to V1 patch mode: ${resolved.why}` };
  }
  const { core, targets } = resolved;
  const routed = targets.filter((t) => t.status === "routed");
  if (routed.length === 0) {
    const why = refusedWhy(targets);
    verify.cross_stage_rewind = { ...rec, ...(rec.targets ? { targets } : {}), status: "refused", why };
    return { applied: false, message: `${rec.stage} ${rec.route} finding not routed to V1 patch mode: ${why}` };
  }
  const nodes = routedStatements(targets);
  const axis = rec.targets ? batchAxis(routed) : rewindAxis(rec);
  const kind: PatchRoundKind = axis === "clarify" ? "refinement" : "error";
  const findingsNow = directiveFindings(core, rec.stage, routed);
  const scope = kind === "error" ? errorScope(verify, core, null) : null;
  if (atCap(verify, kind, scope)) {
    verify.cap_reached = capRecord(verify, kind, "F-rewind", findingsNow.map((f) => ({ id: f.id, axis: f.axis, detail: f.detail, witness: f.witness })), await readPatchFile(runDir), scope);
    return { applied: false, capped: true, message: `${rec.stage} ${rec.route} finding(s) on ${nodes.join(", ")}: a ${kind} round is due but the cap is reached` };
  }

  const moved = countRound(verify, kind, scope);
  const round = roundsUsed(verify, kind);
  const directivePath = path.join(runDir, VERIFY_FILES.v1ReviseDirective);
  let findings: DirectiveFinding[] = findingsNow;
  if (existsSync(directivePath)) {
    try {
      const prior = JSON.parse(await readFile(directivePath, "utf8")) as { mode?: string; findings?: DirectiveFinding[] };
      if (prior?.mode === "patch" && Array.isArray(prior.findings)) {
        findings = [...prior.findings, ...findingsNow.filter((f) => !prior.findings!.some((p) => p.id === f.id && p.detail === f.detail))];
      }
    } catch {
      // an unreadable directive is replaced
    }
  }
  await writeJsonAtomic(directivePath, { mode: "patch", round, findings });

  verify.phase = "init";
  verify.core_sha256 = null;
  state.stage_completed = "V1";
  verify.cross_stage_rewind = { ...rec, ...(rec.targets ? { targets } : {}), status: "applied", nodes, round };
  state.flags.verify_no_d_rewind = null;
  if (rec.route === "fix-source" || rec.route === "unclear") {
    // The escalation is answered by the rewind; the next formalization attempt (a new plan and
    // scaffold of the revised core) starts with fresh loop budgets. Bounded: every rewind spends a
    // capped round. The filler's dead-end memory is not a budget and is kept.
    resetForNewCore(state);
  }
  for (const t of routed) {
    for (const f of verify.findings) {
      if (f.stage === rec.stage && f.kind === "unresolved" && f.detail === t.reason) {
        f.kind = "note";
        f.detail = `${t.reason}\n(routed to V1 patch mode on ${(t.users ?? []).join(", ")}, ${moved})`;
      }
    }
  }
  const folded = findings.filter((f) => findingsNow.includes(f)).reduce((n, f) => n + (f.folds?.length ?? 0), 0);
  const what = routed.length === 1 ? "finding" : `${routed.length} findings (${routed.map((t) => t.node_kind === "statement" ? t.node : `${t.node} → ${(t.users ?? []).join(", ")}`).join("; ")})`;
  return {
    applied: true,
    node: nodes[0]!,
    nodes,
    round,
    message:
      `${rec.stage} ${rec.route} ${what} routed to V1 patch mode on ${nodes.join(", ")}, axis ${axis}` +
      (folded > 0 ? `, folding ${folded} pinned reading(s)` : "") +
      ` — ${moved}`,
  };
}

/** The receipt the F runner records (`dispatcher.ts`), in one place. */
export function pendingRewind(stage: string, route: CrossStageRewind["route"], detail: string): CrossStageRewind {
  return { intent: "incremental_repair", status: "pending", stage, route, detail, at: new Date().toISOString() };
}
