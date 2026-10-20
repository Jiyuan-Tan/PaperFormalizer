/**
 * The paper's owner WITHDRAWS a finding (`--resume --reject-finding "<reading>"`, user decision
 * 2026-09-24). The owner is the expert on the paper: a finding the owner shows to be a misreading
 * (say, a probability the paper states conditionally on the training sample, read unconditionally)
 * is not an error of the paper, whatever the referee graded.
 *
 * It is the third answer at the two halts that ask about a finding — a weakened repair
 * (`state.verify.weakening_repair`) and a proposed F-stage rewind (`state.verify.cross_stage_rewind`)
 * — and, like the other answers there, covers the whole batch (the owner deletes items from the
 * receipt first to split it). For every node of the batch:
 *
 *   • the printed statement stands: a pending suggestion is dropped from `patches.json`;
 *   • the owner's reading becomes a pinned reading `ass:pin-owner-<n>` (`patches.json`
 *     `owner_readings`, compiled by `core_graph.ts`) wired into the node — binding for the F stages
 *     like every pin (`bindingReadings`), rendered in the annotated paper as "Clarification
 *     (author):". That entry, with the findings it `withdraws`, is the ruling's ONE record; the next
 *     two are derived from it (`syncOwnerRulings`, at every `verify` invocation and every ruling);
 *   • the ledger entry says `owner_decision: "finding rejected"` (with the reason, `owner_overruled`)
 *     and is no error of the paper any more (`openErrorIds`);
 *   • the finding joins the ruled-out list (`rejected_rewinds`, `by: "owner"`): the same finding on
 *     the same node and axis is a note from now on, never a halt — at an F-stage presentation as for
 *     every ruled-out finding (`rejectedMatch`: by content for an error, by node and axis for a clarification), and in V1.5, where
 *     `governByOwnerRulings` overrules a re-raised error (`ok`, `owner_overruled`, the reason);
 *   • the report lists it under "Findings withdrawn by the owner", never as refuted or repaired.
 *
 * Then V1.5 grades what changed (the node now carries the pin) and F1 plans the core with it.
 */
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import { resetForNewCore } from "../formalization/loop_limits.js";
import type { StateJson } from "../types.js";
import { OWNER_BK_PREFIX, OWNER_PIN_PREFIX, type OwnerReading, type OwnerWithdrawal } from "./core_graph.js";
import { receiptTargets, rejectPendingRewind, rewindAxis } from "./cross_stage_rewind.js";
import { nonAsciiProblem } from "./annotate_tex.js";
import { recordVerifyFinding } from "./findings.js";
import { isPendingSuggestion, isWithdrawn, openErrorIds, readPatchFile, readTranscribedCore, rebuildPatchedCore, umbrellaConversion, validatePatchFile, type PatchFile } from "./patches.js";
import { recordDecisions, undecidedItems } from "./weakening.js";
import { VERIFY_FILES, type PaperError, type RejectedRewind, type V15NodeVerdict, type V15Review, type VerifyState } from "./types.js";

/** The phrase every note recording an owner's withdrawal carries (`stampWithdrawal`, `rejectPendingRewind`). */
const OWNER_WITHDRAWAL_NOTE = "finding withdrawn by the paper's owner";

/**
 * ONE record per owner ruling: the `patches.json` `owner_readings` entry, its `withdraws` listing
 * the findings it withdrew. Everything else that says "the owner withdrew this" is derived from it
 * here — the ledger stamp (`owner_decision: "finding rejected"`), the ruled-out list's owner
 * entries (`rejected_rewinds`, `by: "owner"`) and the withdrawal notes — so a ruling is added or
 * revoked in one place: delete its `owner_readings` entry and the next `verify` invocation reopens
 * the ledger entry, drops the ruled-out entry and the note (V1.5 then re-grades the node, which lost
 * its pin). With no patch file there is no record to sync from: nothing changes.
 * Mutates `state`; returns the readings and what changed, for the log.
 */
export function syncOwnerRulings(state: StateJson, readings: readonly OwnerReading[] | undefined): { readings: OwnerReading[]; changes: string[] } {
  const verify = state.verify!;
  const changes: string[] = [];
  const out = [...(readings ?? [])];

  // The ruled-out list: every non-owner entry as it is, the owner's exactly as the record says.
  const owner: RejectedRewind[] = out.flatMap((r) =>
    (r.withdraws ?? []).map((w) => ({ node: r.node, axis: w.axis, stage: w.stage, route: w.route, detail: w.detail, reason: r.reading, by: "owner" as const, pin: r.id, at: w.at })),
  );
  const had = (verify.rejected_rewinds ?? []).filter((r) => r.by === "owner");
  const key = (x: RejectedRewind): string => JSON.stringify([x.node, x.axis, x.pin ?? null, x.detail]);
  const now = new Set(owner.map(key));
  const hadKeys = new Set(had.map(key));
  for (const x of had) if (!now.has(key(x))) changes.push(`ruled-out list: the owner's entry on ${x.node} (${x.axis}${x.pin ? `, ${x.pin}` : ""}) dropped — no owner reading records it`);
  for (const x of owner) if (!hadKeys.has(key(x))) changes.push(`ruled-out list: the owner's withdrawal on ${x.node} (${x.axis}, ${x.pin}) recorded`);
  const others = (verify.rejected_rewinds ?? []).filter((r) => r.by !== "owner");
  if (others.length + owner.length > 0) verify.rejected_rewinds = [...others, ...owner];
  else delete verify.rejected_rewinds;

  // The ledger: a node ruled on is stamped (the first withdrawing reading's text the reason); a
  // stamp no reading records is lifted — the finding is open again.
  const ruling = new Map<string, { r: OwnerReading; w: OwnerWithdrawal }>();
  for (const r of out) for (const w of r.withdraws ?? []) if (!ruling.has(r.node)) ruling.set(r.node, { r, w });
  const ledger: Record<string, PaperError> = { ...(verify.paper_errors ?? {}) };
  for (const [node, { r, w }] of ruling) {
    const e = ledger[node] ?? { detail: w.detail, witness: w.witness ?? null, ...(w.axis === "clarify" ? { kind: "clarification" as const } : {}), ...(w.axis === "ambiguity" ? { undetermined: true } : {}) };
    // A withdrawn AMBIGUITY withdraws no error: a witnessed error found on the node since stands.
    if (w.axis === "ambiguity" && !e.undetermined) continue;
    if (isWithdrawn(e) && e.decision_reason === r.reading && e.owner_overruled) continue;
    ledger[node] = { ...e, owner_decision: "finding rejected", decision_reason: r.reading, owner_overruled: true };
    if (!isWithdrawn(e)) changes.push(`ledger: ${node} marked withdrawn by the owner (${r.id})`);
  }
  for (const [id, e] of Object.entries(ledger)) {
    if (!isWithdrawn(e) || ruling.has(id)) continue;
    const { owner_decision: _d, decision_reason: _r, owner_overruled: _o, ...open } = e;
    ledger[id] = open;
    changes.push(`ledger: ${id} reopened — no owner reading withdraws its finding`);
  }
  if (verify.paper_errors || Object.keys(ledger).length > 0) verify.paper_errors = ledger;

  // The withdrawal notes of a node no reading rules on go with the ruling.
  const kept = verify.findings.filter((f) => !(f.kind === "note" && f.detail.includes(OWNER_WITHDRAWAL_NOTE) && !ruling.has(f.node)));
  if (kept.length !== verify.findings.length) changes.push(`findings: ${verify.findings.length - kept.length} withdrawal note(s) dropped — no owner reading records them`);
  verify.findings = kept;
  return { readings: out, changes };
}

/** `syncOwnerRulings` against the run's `patches.json` as stored (read only); no patch file,
 * nothing to sync. Returns the log lines. */
export async function syncOwnerRulingsOnDisk(runDir: string, state: StateJson): Promise<string[]> {
  const p = path.join(runDir, VERIFY_FILES.patches);
  if (!existsSync(p) || !state.verify) return [];
  let raw: { owner_readings?: OwnerReading[] };
  try {
    raw = JSON.parse(await readFile(p, "utf8"));
  } catch {
    return []; // an unreadable patch file is reported by the stage that reads it
  }
  return syncOwnerRulings(state, raw.owner_readings).changes;
}

/** The owner's ruling on a V1.5 node, if the owner withdrew a finding on it on that axis. */
export function ownerRuling(verify: VerifyState, node: string, axis: "correctness" | "clarify" = "correctness"): RejectedRewind | undefined {
  return (verify.rejected_rewinds ?? []).find((r) => r.by === "owner" && r.node === node && r.axis === axis);
}

/** A verdict with its error overruled by the owner: `ok`, the reason recorded, the detail kept. */
export function overruleVerdict(n: V15NodeVerdict, reason: string): V15NodeVerdict {
  const { weakens_contribution: _w, minimality: _m, ...rest } = n;
  return { ...rest, correctness: "ok", witness: null, owner_overruled: true, owner_reason: reason, detail: `[withdrawn by the owner: ${reason}] ${n.detail}` };
}

/**
 * A V1.5 pass re-raising a finding the owner withdrew: an `error` (a weakening grade included) on
 * a node the owner ruled on (same node, correctness axis) is overruled and recorded as a note —
 * never an objection, never a halt. Returns the governed nodes and the ids overruled.
 */
export function governByOwnerRulings(state: StateJson, nodes: V15NodeVerdict[], on: (id: string) => string = (id) => id): { nodes: V15NodeVerdict[]; overruled: string[] } {
  const verify = state.verify!;
  const overruled: string[] = [];
  const out = nodes.map((n) => {
    if (n.correctness !== "error") return n;
    // (`on`: the node the finding stands on, when it is graded on another — `stage_v1_5.ts` `findingNode`;
    // a ruling recorded on the node graded holds too)
    const r = ownerRuling(verify, on(n.id)) ?? ownerRuling(verify, n.id);
    if (!r) return n;
    overruled.push(n.id);
    recordVerifyFinding(state, {
      node: on(n.id),
      stage: "V1.5",
      kind: "note",
      detail: `the referee raised again a finding the paper's owner withdrew (${r.reason}); overruled. The referee's finding: ${n.detail}`,
      witness: null,
    });
    return overruleVerdict(n, r.reason);
  });
  return { nodes: out, overruled };
}

/** Fresh owner ids, one per node, numbered after every owner entry of the same kind on file:
 * `ass:pin-owner-<n>` for a reading, `ass:bk-owner-<n>` for a side condition (`kind: "bookkeeping"`). */
export function ownerReadingsFor(file: PatchFile | null, nodes: readonly string[], reading: string, kind: OwnerFindingKind = "reading"): OwnerReading[] {
  assertOwnerTex(reading);
  const prefix = kind === "bookkeeping" ? OWNER_BK_PREFIX : OWNER_PIN_PREFIX;
  const taken = (file?.owner_readings ?? []).filter((r) => r.id.startsWith(prefix)).map((r) => Number(r.id.slice(prefix.length))).filter(Number.isFinite);
  let n = taken.length > 0 ? Math.max(...taken) : 0;
  return nodes.map((node) => ({ id: `${prefix}${(n += 1)}`, node, reading, ...(kind === "bookkeeping" ? { kind } : {}) }));
}

/** An owner reading or condition is written into the corrected paper as TeX, and the reviewed core
 * holds it as written: one that is not plain-ASCII TeX is refused here, before it is recorded (a later
 * rewording changes the reviewed core). */
export function assertOwnerTex(text: string): void {
  const bad = nonAsciiProblem(text);
  if (bad) throw new Error(`the owner reading or condition must be written in TeX: ${bad}. Write it again in TeX (e.g. $\\gamma\\in\\Gamma$, not γ ∈ Γ).`);
}

export type OwnerFindingKind = "reading" | "bookkeeping";

/** The owner's answer text: `bookkeeping: <condition>` states a side condition, anything else a reading. */
export function ownerAnswerKind(text: string): { kind: OwnerFindingKind; text: string } {
  const m = /^\s*bookkeeping\s*:\s*([\s\S]+)$/i.exec(text);
  return m ? { kind: "bookkeeping", text: m[1]!.trim() } : { kind: "reading", text: text.trim() };
}

/** The node ids of the transcribed core (what a `--reject-finding "<node>: …"` may name); empty when
 * the run has no core yet. */
export async function transcribedNodeIds(runDir: string): Promise<Set<string>> {
  const p = path.join(runDir, VERIFY_FILES.coreTranscribed);
  if (!existsSync(p)) return new Set();
  try {
    const c = JSON.parse(await readFile(p, "utf8")) as { statements?: Array<{ id: string }>; assumptions?: Array<{ id: string }>; definitions?: Array<{ id: string }> };
    return new Set([...(c.statements ?? []), ...(c.assumptions ?? []), ...(c.definitions ?? [])].map((n) => n.id));
  } catch {
    return new Set();
  }
}

/** One `--reject-finding` value: `<node>: <reading>`, `<node>: bookkeeping: <condition>` (a node of
 * the core named first), or the batch form (no node: the pending receipt's items). */
export function parseRejectFinding(value: string, ids: ReadonlySet<string>): { node: string | null; kind: OwnerFindingKind; text: string } {
  const m = /^\s*([A-Za-z]+:[A-Za-z0-9._-]+)\s*:\s*([\s\S]+)$/.exec(value);
  if (m && ids.has(m[1]!)) return { node: m[1]!, ...ownerAnswerKind(m[2]!) };
  return { node: null, ...ownerAnswerKind(value) };
}

/** A withdrawal as the owner reading records it (`OwnerReading.withdraws`). */
/** The axis a withdrawal of the ledger entry `e` is recorded on. */
function withdrawnAxis(e: PaperError | undefined): OwnerWithdrawal["axis"] {
  return e?.kind === "clarification" ? "clarify" : e?.undetermined ? "ambiguity" : "correctness";
}

function withdrawal(it: { axis: OwnerWithdrawal["axis"]; stage: string; route: string; detail: string; witness?: string | null }, at: string): OwnerWithdrawal {
  return { axis: it.axis, stage: it.stage, route: it.route, detail: it.detail, ...(it.witness ? { witness: it.witness } : {}), at };
}

/** The review and the findings stamped for a withdrawn finding. (The ledger stamp and the
 * ruled-out entry are derived from the owner reading, `syncOwnerRulings`.) */
async function stampWithdrawal(
  runDir: string,
  state: StateJson,
  items: ReadonlyArray<{ node: string; stage: string; detail: string; pin: string }>,
  reason: string,
  alreadyNoted: boolean,
): Promise<void> {
  const verify = state.verify!;
  for (const it of items) {
    // Never refuted, never repaired: what the run had recorded against the node is withdrawn with it.
    verify.findings = verify.findings.filter((f) => !(f.node === it.node && (f.kind === "refuted" || f.kind === "unresolved" || f.undetermined) && f.stage === it.stage));
    // (At a rewind halt `rejectPendingRewind` already turned the finding into this note.)
    if (!alreadyNoted) recordVerifyFinding(state, {
      node: it.node,
      stage: it.stage,
      kind: "note",
      detail: `${OWNER_WITHDRAWAL_NOTE}: ${reason} (${it.pin.startsWith(OWNER_BK_PREFIX) ? "side condition recorded as" : "reading pinned as"} ${it.pin}). The withdrawn finding: ${it.detail}`,
      witness: null,
    });
  }
  // The referee's verdict on the node is overruled on file too, so every view of the run agrees.
  const reviewPath = path.join(runDir, VERIFY_FILES.v15Review);
  if (existsSync(reviewPath)) {
    try {
      const review = JSON.parse(await readFile(reviewPath, "utf8")) as V15Review;
      const ids = new Set(items.map((i) => i.node));
      if (Array.isArray(review.nodes) && review.nodes.some((n) => ids.has(n.id) && n.correctness === "error")) {
        review.nodes = review.nodes.map((n) => (ids.has(n.id) && n.correctness === "error" ? overruleVerdict(n, reason) : n));
        await writeJsonAtomic(reviewPath, review);
      }
    } catch {
      // an unreadable review is re-written by the next pass
    }
  }
}

/** Refuse, before anything is changed, a patch file with the owner's readings that does not fit the
 * transcribed core (the withdrawn nodes need no patch). */
async function checkFits(runDir: string, verify: VerifyState, file: PatchFile, withdrawn: readonly string[]): Promise<void> {
  const transcribed = await readTranscribedCore(runDir);
  const bad = validatePatchFile(transcribed, file, openErrorIds(verify.paper_errors).filter((id) => !withdrawn.includes(id)));
  if (bad.length > 0) throw new Error(`the patch file with the owner's reading does not fit the transcribed core: ${bad.join(" ")} Fix ${VERIFY_FILES.patches}, then answer again.`);
}

/** Write the patch file with the owner's readings (the ruling's one record), derive the ledger
 * stamps and ruled-out entries from it, rebuild `core.json`, send the run to V1.5. */
async function persistAndRewind(runDir: string, state: StateJson, file: PatchFile): Promise<void> {
  const verify = state.verify!;
  const { readings } = syncOwnerRulings(state, file.owner_readings);
  await writeJsonAtomic(path.join(runDir, VERIFY_FILES.patches), { ...file, owner_readings: readings });
  await rebuildPatchedCore(runDir, { detectHandEdits: false });
  verify.core_sha256 = null;
  verify.phase = "v1";
  state.stage_completed = "V1";
}

const emptyPatchFile = (): PatchFile => ({ key_results: [], key_contribution: "", patches: [], unfixable: [] });

/** `--reject-finding` at a weakened-repair halt: every item still pending, or only `only` (a
 * node-scoped answer, `"<node>: <reading>"` naming an item of the receipt). Returns the log line. */
export async function rejectWeakeningFinding(runDir: string, state: StateJson, reason: string, only?: readonly string[], opts: { check?: boolean } = {}): Promise<string> {
  const verify = state.verify!;
  const rec = verify.weakening_repair;
  if (!rec || rec.status !== "pending") throw new Error("no weakened repair is pending (state.verify.weakening_repair).");
  const file = await readPatchFile(runDir);
  if (!file) throw new Error(`${VERIFY_FILES.patches} is missing: the suggested repairs live there.`);
  const listed = new Set(undecidedItems(rec).map((i) => i.node).filter((n) => !only || only.includes(n)));
  for (const n of only ?? []) if (!listed.has(n)) throw new Error(`${n} is not a pending item of the receipt.`);
  const nodes = file.unfixable.filter((u) => isPendingSuggestion(u) && listed.has(u.node)).map((u) => u.node);
  if (nodes.length === 0) throw new Error(`none of the receipt's items (${[...listed].join(", ")}) is a pending suggestion in ${VERIFY_FILES.patches}.`);
  const answer = ownerAnswerKind(reason);
  const item = new Map(rec.items.map((i) => [i.node, i] as const));
  const at = new Date().toISOString();
  const readings = ownerReadingsFor(file, nodes, answer.text, answer.kind).map((r) => ({
    ...r,
    withdraws: [withdrawal({
      axis: withdrawnAxis(verify.paper_errors?.[r.node]),
      stage: "V1.5",
      route: "weakening halt",
      detail: verify.paper_errors?.[r.node]?.detail ?? item.get(r.node)?.detail ?? "",
      witness: verify.paper_errors?.[r.node]?.witness ?? item.get(r.node)?.witness ?? null,
    }, at)],
  }));
  const next: PatchFile = {
    ...file,
    unfixable: file.unfixable.filter((u) => !nodes.includes(u.node)),
    owner_readings: [...(file.owner_readings ?? []), ...readings],
  };
  await checkFits(runDir, verify, next, nodes);
  if (opts.check) return ""; // (every refusal is above: a resume with several answers checks each before it applies one)
  await stampWithdrawal(runDir, state, readings.map((r) => ({ node: r.node, stage: "V1.5", detail: r.withdraws[0]!.detail, pin: r.id })), reason, false);
  await persistAndRewind(runDir, state, next);
  verify.weakening_repair = { ...rec, reason };
  recordDecisions(verify, nodes, "finding rejected");
  return (
    `--reject-finding: the owner withdraws the finding on ${nodes.join(", ")} (${reason}); the printed statement stands, ` +
    `the reading is pinned as ${readings.map((r) => r.id).join(", ")} and binds the formalization; a fresh V1.5 pass grades what changed.`
  );
}

/** `--reject-finding` at a proposed F-stage rewind: `--reject-rewind`, by the owner, with the reading
 * pinned into every node of the batch (then V1.5 on the delta, F1 re-plans). Returns the log line. */
export async function rejectRewindFinding(runDir: string, state: StateJson, reason: string): Promise<string> {
  const verify = state.verify!;
  const rec = verify.cross_stage_rewind;
  if (!rec || rec.status !== "pending" || !rec.presented) throw new Error("no F-stage rewind is presented (state.verify.cross_stage_rewind pending and presented).");
  // The findings to withdraw, each on its node: a batch's resolved targets; a one-finding receipt
  // (an F1.5 D-rewind, or one recorded before batching) on the statements it named.
  const resolved = receiptTargets(rec).filter((t) => t.status !== "refused" && t.status !== "repeat" && t.node);
  const items = resolved.length > 0
    ? resolved.map((t) => ({ node: t.node!, axis: t.axis, route: t.route ?? rec.route, detail: t.reason }))
    : (rec.targets ? [] : (rec.nodes ?? [])).map((node) => ({ node, axis: rewindAxis(rec), route: rec.route, detail: rec.detail }));
  if (items.length === 0) throw new Error("the presented rewind names no node of the core to pin a reading on; answer with --reject-rewind instead.");
  const file = (await readPatchFile(runDir)) ?? emptyPatchFile();
  const nodes = [...new Set(items.map((t) => t.node))];
  const answer = ownerAnswerKind(reason);
  // Every withdrawn finding is recorded on its own node's reading (a one-finding receipt names only
  // its first statement); the ruled-out entries are derived from them (`syncOwnerRulings`).
  const at = new Date().toISOString();
  const readings = ownerReadingsFor(file, nodes, answer.text, answer.kind).map((r) => ({
    ...r,
    withdraws: items.filter((it) => it.node === r.node).map((it) => withdrawal({ ...it, stage: rec.stage }, at)),
  }));
  const pinOf = new Map(readings.map((r) => [r.node, r.id] as const));
  const next: PatchFile = { ...file, owner_readings: [...(file.owner_readings ?? []), ...readings] };
  await checkFits(runDir, verify, next, nodes);
  rejectPendingRewind(state, reason, nodes[0], "owner");
  await stampWithdrawal(runDir, state, items.map((t) => ({ node: t.node, stage: rec.stage, detail: t.detail, pin: pinOf.get(t.node)! })), reason, true);
  await persistAndRewind(runDir, state, next);
  // The next formalization attempt plans the core with the pin: fresh loop budgets, as after an
  // approved rewind.
  resetForNewCore(state);
  return (
    `--reject-finding: the owner withdraws the ${rec.stage} finding${nodes.length > 1 ? "s" : ""} on ${nodes.join(", ")} (${reason}); ` +
    `the reading is pinned as ${readings.map((r) => r.id).join(", ")} and binds the formalization; the same finding on the same node is a note from now on. ` +
    "V1.5 grades what changed, then F1 plans the core with the pin."
  );
}

/**
 * `--add-condition "<node>: <condition>"` (repeatable), at any halt: the orchestrator states a condition
 * the paper takes for granted that the core does not carry on `node` (a setup fact the referee pinned on a
 * sibling only, the well-definedness a lemma presupposes). It becomes an owner side condition
 * (`ass:bk-owner-<n>`, wired into the node — or into every result using it, for an assumption) and
 * WITHDRAWS NOTHING: a finding, an applied repair and every ruling on the node stand. V1.5 grades the
 * node with it. Returns the log line.
 */
export async function addOwnerConditions(runDir: string, state: StateJson, items: ReadonlyArray<{ node: string; text: string }>): Promise<string> {
  const verify = state.verify!;
  const file = (await readPatchFile(runDir)) ?? emptyPatchFile();
  const readings: OwnerReading[] = [];
  for (const it of items) {
    if (!it.text.trim()) throw new Error(`--add-condition "${it.node}: …" needs the condition.`);
    const [r] = ownerReadingsFor({ ...file, owner_readings: [...(file.owner_readings ?? []), ...readings] }, [it.node], it.text, "bookkeeping");
    readings.push({ ...r!, withdraws: [] });
  }
  const next: PatchFile = { ...file, owner_readings: [...(file.owner_readings ?? []), ...readings] };
  await checkFits(runDir, verify, next, items.map((it) => it.node));
  await persistAndRewind(runDir, state, next);
  return `--add-condition: ${readings.map((r) => `${r.node} → ${r.id}`).join(", ")} (owner side condition${readings.length > 1 ? "s" : ""}; nothing withdrawn, any repair kept); a fresh V1.5 pass grades what changed.`;
}

/** One `--umbrella` value: `<node>`, or `<node>: <title>` (the new block's title). */
export function parseUmbrella(value: string): { node: string; title?: string } {
  const m = /^\s*([A-Za-z]+:[A-Za-z0-9._-]+)\s*(?::\s*([\s\S]*))?$/.exec(value);
  if (!m) throw new Error(`--umbrella "${value}": give "<node>" or "<node>: <title>", the node a result whose repair splits off blocks.`);
  return { node: m[1]!, ...(m[2]?.trim() ? { title: m[2].trim() } : {}) };
}

/**
 * `--umbrella <node>` / `--umbrella "<node>: <title>"` (repeatable), at any halt: the orchestrator
 * turns a split repair into the UMBRELLA form without a fixer round (`patches.ts`
 * `umbrellaConversion`) — what the corrected statement still states becomes one more proposition block
 * (titled `title`) and the result an umbrella over all its blocks, established exactly when they are.
 * Nothing is withdrawn and nothing the repair claims changes: the same conclusions, under the same
 * conditions, in one more block. Then `core.json` is rebuilt, V1.5 grades what changed (the new block,
 * the umbrella, what uses them) and F1 re-plans: the umbrella takes no Lean declaration, and the one
 * the result had is the new block's (`plan` rename by the planner; its `@node` tag follows the plan).
 * Returns the log line.
 */
export async function convertToUmbrella(runDir: string, state: StateJson, items: ReadonlyArray<{ node: string; title?: string }>): Promise<string> {
  const verify = state.verify!;
  let file = await readPatchFile(runDir);
  if (!file) throw new Error(`--umbrella: ${VERIFY_FILES.patches} is missing — there is no repair to convert.`);
  const transcribed = await readTranscribedCore(runDir);
  const done: string[] = [];
  const moved: Array<{ from: string; to: string }> = [];
  for (const it of items) {
    if (items.filter((x) => x.node === it.node).length > 1) throw new Error(`--umbrella names ${it.node} twice.`);
    const c = umbrellaConversion(transcribed, file, it.node, it.title);
    file = c.file;
    moved.push({ from: it.node, to: c.block.id });
    done.push(`${it.node} (its statement is now the block ${c.block.id}${it.title ? `, "${it.title}"` : ""}; ${file.patches.find((p) => p.node === it.node)!.corollaries!.length} blocks)`);
  }
  await checkFits(runDir, verify, file, []);
  const due = verify.phase === "init";
  await persistAndRewind(runDir, state, file);
  if (due) verify.phase = "init";
  const planned = await movePlanEntries(path.join(runDir, "formalization", "plan.json"), moved);
  return (
    `--umbrella: ${done.join("; ")} — the result is an umbrella over its blocks, established exactly when all of them are; a fresh V1.5 pass grades what changed, then F1 re-plans (the umbrella takes no Lean declaration).` +
    (planned.length > 0 ? ` The plan entry of ${planned.map((m) => `${m.from} is now ${m.to}'s (Lean name ${m.lean_name} kept: F2 retags its declaration by that name)`).join("; ")}.` : "")
  );
}

/**
 * The plan entry of each result turned into an umbrella becomes its new block's: the Lean declaration
 * that stated what the result still stated states that block — same Lean name, so F2's tag
 * reconciliation retags it (`f2_tag_reconcile.ts`, basis `lean-name`) instead of scaffolding it anew.
 * Best effort: no plan yet, an unreadable one, or one that already plans the block is left alone (F1
 * then plans the block itself). Returns the entries moved.
 */
export async function movePlanEntries(planFile: string, moves: ReadonlyArray<{ from: string; to: string }>): Promise<Array<{ from: string; to: string; lean_name: string }>> {
  if (!existsSync(planFile)) return [];
  let plan: { nodes?: Record<string, { lean_name?: string; local_id?: string }> } & Record<string, unknown>;
  try {
    plan = JSON.parse(await readFile(planFile, "utf8"));
  } catch {
    return [];
  }
  if (!plan.nodes || typeof plan.nodes !== "object") return [];
  const out: Array<{ from: string; to: string; lean_name: string }> = [];
  for (const m of moves) {
    const entry = plan.nodes[m.from];
    if (!entry || plan.nodes[m.to]) continue;
    // In place, so the plan's node order — and every positional alias read off it — stays.
    plan.nodes = Object.fromEntries(Object.entries(plan.nodes).map(([k, v]) => (k === m.from ? [m.to, { ...v, ...(v.local_id === m.from ? { local_id: m.to } : {}) }] : [k, v])));
    out.push({ ...m, lean_name: String(entry.lean_name ?? "") });
  }
  if (out.length > 0) await writeJsonAtomic(planFile, plan);
  return out;
}

/** One `--edit-reading` value: `<id>: <new text>`, the id an owner reading's (`ass:pin-owner-<n>` /
 * `ass:bk-owner-<n>`). */
export function parseEditReading(value: string): { id: string; text: string } {
  const m = /^\s*(ass:(?:pin|bk)-owner-[0-9]+)\s*:\s*([\s\S]+)$/.exec(value);
  if (!m || !m[2]!.trim()) throw new Error(`--edit-reading "${value}": give "<id>: <new text>", the id an owner reading's (ass:pin-owner-<n> or ass:bk-owner-<n>).`);
  return { id: m[1]!, text: m[2]!.trim() };
}

/**
 * `--edit-reading "<id>: <new text>"` / `--remove-reading <id>` (repeatable), at any halt: the owner
 * revises a ruling on record. An edit rewrites the reading's text and keeps its id, node, kind and
 * the findings it withdrew (their ledger reason follows the text, `syncOwnerRulings`). A removal
 * deletes the entry, as revoking it by hand does: the ledger stamp, the ruled-out entry and the
 * withdrawal note it stood for go with it; a finding it had withdrawn that no repair on file
 * addresses leaves the ledger, so the node goes back to the referee as printed and an error that
 * still holds is raised again. Then `core.json` is rebuilt and V1.5 grades what changed (a patch
 * round still due runs first). Returns the log line.
 */
export async function reviseOwnerReadings(runDir: string, state: StateJson, edits: ReadonlyArray<{ id: string; text: string }>, removals: readonly string[]): Promise<string> {
  const verify = state.verify!;
  const file = await readPatchFile(runDir);
  const onFile = file?.owner_readings ?? [];
  const named = [...edits.map((e) => e.id), ...removals];
  for (const id of named) {
    if (!onFile.some((r) => r.id === id)) throw new Error(`${id} is not an owner reading of ${VERIFY_FILES.patches} (on file: ${onFile.map((r) => r.id).join(", ") || "none"}).`);
    if (named.filter((x) => x === id).length > 1) throw new Error(`${id} is named twice; give one --edit-reading or --remove-reading per reading.`);
  }
  for (const e of edits) assertOwnerTex(e.text);
  const text = new Map(edits.map((e) => [e.id, e.text] as const));
  const kept = onFile.filter((r) => !removals.includes(r.id)).map((r) => (text.has(r.id) ? { ...r, reading: text.get(r.id)! } : r));
  const next: PatchFile = { ...file!, owner_readings: kept };
  await checkFits(runDir, verify, next, []);
  const ruled = new Set(kept.filter((r) => (r.withdraws ?? []).length > 0).map((r) => r.node));
  const addressed = new Set([...next.patches, ...next.unfixable].map((x) => x.node));
  const regraded = [...new Set(onFile.filter((r) => removals.includes(r.id) && (r.withdraws ?? []).length > 0 && !ruled.has(r.node) && !addressed.has(r.node)).map((r) => r.node))];
  if (verify.paper_errors) for (const node of regraded) delete verify.paper_errors[node];
  // A patch round still due runs first; the V1.5 pass after it grades the changed reading with it.
  const due = verify.phase === "init";
  await persistAndRewind(runDir, state, next);
  if (due) verify.phase = "init";
  return (
    [
      edits.length > 0 ? `--edit-reading: ${edits.map((e) => e.id).join(", ")} reworded (id, node and the findings withdrawn kept)` : "",
      removals.length > 0 ? `--remove-reading: ${removals.join(", ")} removed${regraded.length > 0 ? ` (the finding on ${regraded.join(", ")} is no longer withdrawn: the referee grades the statement as printed)` : ""}` : "",
    ].filter(Boolean).join("; ") + "; a fresh V1.5 pass grades what changed."
  );
}

/**
 * `--reject-finding "<node>: <reading>"` / `"<node>: bookkeeping: <condition>"` (repeatable), at ANY
 * halt (owner decision 2026-09-24): the owner downgrades a finding the run already acted on — an
 * APPLIED repair (a patch, or an unfixable entry that is not a pending suggestion), or an open
 * finding not repaired yet. Per node: the patch (its corrected text, proof note)
 * or the unfixable entry leaves `patches.json`, so the printed statement stands; the owner's text
 * becomes an `ass:pin-owner-<n>` (a reading — "Clarification (author):" in the annotated paper) or an
 * `ass:bk-owner-<n>` (a side condition every reader takes for granted — "Bookkeeping condition:"),
 * wired into the node; the ledger entry is marked `owner_decision: "finding rejected"`, the finding
 * ruled out (a re-raise is overruled), every refutation recorded against the node withdrawn. Then
 * V1.5 re-reviews what changed. A node that is an item of the pending receipt is answered with the
 * batch form. (A side condition that withdraws nothing is `--add-condition`, `addOwnerConditions`.)
 * Returns the log line.
 */
export async function rejectAppliedFindings(runDir: string, state: StateJson, items: ReadonlyArray<{ node: string; kind: OwnerFindingKind; text: string }>): Promise<string> {
  const verify = state.verify!;
  const file = (await readPatchFile(runDir)) ?? emptyPatchFile();
  const receipt = new Set<string>([
    ...(verify.weakening_repair?.status === "pending" ? verify.weakening_repair.items.map((i) => i.node) : []),
    ...(verify.cross_stage_rewind?.status === "pending" ? [...receiptTargets(verify.cross_stage_rewind).map((t) => t.node ?? ""), ...(verify.cross_stage_rewind.nodes ?? [])] : []),
  ]);
  const seen = new Set<string>();
  for (const it of items) {
    if (seen.has(it.node)) throw new Error(`--reject-finding names ${it.node} twice; give one answer per node.`);
    seen.add(it.node);
    if (!it.text) throw new Error(`--reject-finding "${it.node}: …" needs the reading (or "bookkeeping: <condition>").`);
    if (receipt.has(it.node)) throw new Error(`${it.node} is an item of the pending receipt: answer the receipt — --reject-finding "<reading>" with no node (at a proposed rewind, or a cap its round ran into), or the receipt's own flags.`);
    const e = verify.paper_errors?.[it.node];
    if (isWithdrawn(e)) continue; // a further reading of a node already ruled on
    const applied = file.patches.some((p) => p.node === it.node) || file.unfixable.some((u) => u.node === it.node && !isPendingSuggestion(u));
    if (file.unfixable.some((u) => u.node === it.node && isPendingSuggestion(u))) throw new Error(`${it.node} carries a suggested repair awaiting the owner: answer it with the batch form --reject-finding "<reading>".`);
    if (!applied && !e) throw new Error(`${it.node} carries no finding and no repair to withdraw (to add a condition the paper takes for granted, use --add-condition "${it.node}: <condition>").`);
  }
  const nodes = items.map((it) => it.node);
  // A node already ruled on takes a further reading and withdraws nothing more.
  const further = new Set(nodes.filter((n) => isWithdrawn(verify.paper_errors?.[n])));
  const at = new Date().toISOString();
  const readings = items.map((it) => {
    const [r] = ownerReadingsFor({ ...file, owner_readings: [...(file.owner_readings ?? [])] }, [it.node], it.text, it.kind);
    const e = verify.paper_errors?.[it.node];
    const detail = e?.detail ?? file.patches.find((p) => p.node === it.node)?.proof_note ?? "";
    const reading: OwnerReading = {
      ...r!,
      withdraws: further.has(it.node) ? [] : [withdrawal({ axis: withdrawnAxis(e), stage: "V1.5", route: "applied repair", detail, witness: e?.witness ?? null }, at)],
    };
    file.owner_readings = [...(file.owner_readings ?? []), reading];
    return reading;
  });
  // The repair the withdrawn finding produced leaves the file; a further reading withdraws nothing,
  // so a repair on its node (a consequential one, say) stands.
  const stripped = nodes.filter((n) => !further.has(n));
  const next: PatchFile = {
    ...file,
    patches: file.patches.filter((p) => !stripped.includes(p.node)),
    unfixable: file.unfixable.filter((u) => !stripped.includes(u.node)),
  };
  await checkFits(runDir, verify, next, nodes);
  for (const [k, it] of items.entries()) {
    if (further.has(it.node)) continue;
    await stampWithdrawal(runDir, state, [{ node: it.node, stage: "V1.5", detail: readings[k]!.withdraws![0]!.detail, pin: readings[k]!.id }], it.text, false);
    // Never refuted, never repaired, whichever stage recorded it.
    verify.findings = verify.findings.filter((f) => !(f.node === it.node && (f.kind === "refuted" || f.kind === "unresolved" || f.undetermined)));
  }
  await persistAndRewind(runDir, state, next);
  return (
    `--reject-finding: the owner withdraws the finding${nodes.length > 1 ? "s" : ""} on ${nodes.join(", ")}; the printed statement${nodes.length > 1 ? "s stand" : " stands"} (any repair removed), ` +
    readings.map((r) => `${r.node} → ${r.id} (${r.kind === "bookkeeping" ? "side condition" : "reading"}${further.has(r.node) ? ", a further reading of a finding already withdrawn" : ""})`).join(", ") +
    "; a fresh V1.5 pass grades what changed."
  );
}
