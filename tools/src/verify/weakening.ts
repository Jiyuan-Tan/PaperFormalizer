/**
 * Repairs never weaken the contribution (user decision 2026-09-23; owner scope 2026-09-24).
 *
 * The fixer repairs a result only without weakening what the paper claims: it makes an intended
 * reading explicit, adds a condition a competent reader treats as implicit, or tightens a
 * hypothesis to the paper's actual setting, null or framework — the conclusion unchanged. When no
 * such repair exists, it answers the node `unfixable` with a `suggested_repair`: the STRONGEST
 * version still true (a patch body plus one line on what it gives up). A referee that finds a
 * confirmed repair weakens the claim grades it `weakens_contribution`, and that patch becomes such
 * a suggestion — never another fixer attempt.
 *
 * A repair may SPLIT a result into a general statement and corollaries (`patches.ts` `corollaries`).
 * What it gives up is judged on the statement TOGETHER with its corollaries against the printed
 * claim: a conclusion moved to a corollary is kept, one in no block is given up. The split travels
 * with the repair through every step here — a weakening grade on a corollary is a grade on its
 * parent's repair (`patches.ts` `onSplitParent`), the suggestion and the owner's receipt carry the
 * corollaries, and the owner rules on the parent.
 *
 * The owner decides only for MAIN THEOREMS (`mainTheoremIds`: the core's `theorem` / `corollary`
 * statements and the fixer's `key_results`). A suggestion on any other node — a lemma, a
 * proposition, a definition, an assumption, a clause of a non-theorem — is an INTERMEDIATE result:
 * the runner applies it at once as a patch (`narrowIntermediates`, `narrowed_by: "runner"`), the
 * next V1.5 pass confirms it like any repair, and the report shows it `repaired` with
 * "narrowed: …". When a narrowed lemma leaves a main theorem unprovable at full strength, that
 * theorem's halt is where the owner decides.
 *
 * A pending suggestion on a main theorem halts the run for the paper's OWNER, in every mode
 * (auto mode included), with one receipt for the batch (`state.verify.weakening_repair`):
 *
 *   --resume --accept-repair             the suggestions become patches (`accepted_weakening`), a
 *                                        V1.5 pass confirms them, the report shows each result
 *                                        `repaired` with "contribution narrowed: …"
 *   --resume --decline-repair "<reason>" each result stays `refuted` (paper claim, witness, the
 *                                        declined suggestion) and is descoped from Lean with what
 *                                        rests on it, key results included; the run goes on
 *   --resume --reject-finding "<reading>" the finding is WITHDRAWN (a referee misreading): the
 *                                        printed statement stands, the owner's reading is pinned
 *                                        into the node, the referee's error on it is overruled
 *                                        and may not be raised again (`owner_rulings.ts`)
 *
 *   --resume --redo-repair "<node>: <guidance>"  the suggestion is discarded; the fixer repairs the
 *                                        node again under the owner's guidance (binding), V1.5
 *                                        confirms it (`ruleOnReceipt`)
 *
 * Answers may name nodes (`--accept-repair thm:a`, `--decline-repair "thm:b: <reason>"`,
 * `--reject-finding "thm:c: <reading>"`, `--redo-repair "thm:d: …"`) to rule item by item in one
 * resume, one bare answer covering the items no other names (`decisions`, `closeReceipt`); items no
 * answer names stay pending suggestions and are presented again at the next halt.
 */
import { ownerWordsTex } from "./owner_text.js";
import { createHash } from "node:crypto";
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import type { Core } from "../core/schema.js";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import type { StateJson } from "../types.js";
import {
  WEAKENS_REASON_PREFIX,
  applySuggestions,
  type Patch,
  isPendingSuggestion,
  openErrorIds,
  readPatchFile,
  readTranscribedCore,
  rebuildPatchedCore,
  repairBody,
  suggestionText,
  validatePatchFile,
  type PatchFile,
  type RepairBody,
} from "./patches.js";
import { VERIFY_FILES, type PaperError, type WeakeningDecision, type WeakeningItem, type WeakeningRepair } from "./types.js";
import { roundsUsed } from "./caps.js";
import { TEX_FRAGMENT_RULE, mathModeHint } from "./tex_fragment_check.js";

/** `WeakeningItem.proposed` when the suggestion changes no statement text (its proof only). */
export const PROPOSED_UNCHANGED = "the statement as printed";

/** The detail prefix a weakening grade carries. */
export const WEAKENS_DETAIL_PREFIX = "weakens the contribution:";

const clip = (s: string, n = 320): string => {
  const t = s.replace(/\s+/g, " ").trim();
  return t.length > n ? `${t.slice(0, n)}…` : t;
};

/** A detail with the weakening prefix, exactly once. */
export function weakeningDetail(detail: string): string {
  const d = detail.trim();
  return d.toLowerCase().startsWith(WEAKENS_DETAIL_PREFIX) ? d : `${WEAKENS_DETAIL_PREFIX} ${d}`;
}

/** Whether a text grades a REPAIR (a weakening grade, or the reason of the suggestion made of it):
 * it says what the repair gives up, not what is wrong with the printed statement. */
export function gradesRepair(text: string): boolean {
  const t = text.trim().toLowerCase();
  return t.startsWith(WEAKENS_DETAIL_PREFIX) || t.startsWith(WEAKENS_REASON_PREFIX);
}

function withoutPrefix(detail: string): string {
  const d = detail.trim();
  return d.toLowerCase().startsWith(WEAKENS_DETAIL_PREFIX) ? d.slice(WEAKENS_DETAIL_PREFIX.length).trim() : d;
}

/** What a repair's note says it gives up (`gives_up`), trimmed; empty when it says nothing. */
function noteGivesUp(p: { owner_explanation?: unknown }): string {
  const e = p.owner_explanation;
  return e && typeof e === "object" && typeof (e as { gives_up?: unknown }).gives_up === "string" ? (e as { gives_up: string }).gives_up.trim() : "";
}

/**
 * The patches the referee graded `weakens_contribution` become suggestions: each patch body moves,
 * unchanged, into an `unfixable` entry's `suggested_repair`. What it gives up is the note's own
 * `gives_up` field when it has one, else the referee's detail. A consequential patch has no finding
 * of its own: the entry keeps the results it follows, the only record of why the printed statement
 * no longer stands. Pure.
 */
export function convertWeakeningPatches(file: PatchFile, findings: ReadonlyArray<{ id: string; detail: string }>): PatchFile {
  const referee = new Map(findings.map((f) => [f.id, withoutPrefix(f.detail)] as const));
  const moved = file.patches.filter((p) => referee.has(p.node));
  const byNode = new Map(moved.map((p) => [p.node, noteGivesUp(p) || referee.get(p.node)!] as const));
  return {
    ...file,
    patches: file.patches.filter((p) => !referee.has(p.node)),
    unfixable: [
      ...file.unfixable.filter((u) => !referee.has(u.node)),
      ...moved.map((p) => ({
        node: p.node,
        reason: `${WEAKENS_REASON_PREFIX} ${referee.get(p.node)}`,
        suggested_repair: {
          ...repairBody(p),
          given_up: byNode.get(p.node)!,
          ...(noteGivesUp(p) ? {} : { given_up_by: "referee" as const }),
        },
        suggested_by: "referee" as const,
        ...(p.owner_explanation ? { owner_explanation: p.owner_explanation } : {}),
        ...(p.consequence_of?.length ? { consequence_of: p.consequence_of, ...(p.reason ? { consequence_reason: p.reason } : {}) } : {}),
      })),
    ],
  };
}

/**
 * What an earlier file settled that a fixer reply may not undo: an unfixable entry carrying a
 * suggestion (pending, or declined by the owner) stands as it was, and a patch the owner accepted
 * as a weakening keeps that mark while the fixer returns it unchanged. New suggestions are stamped
 * as the fixer's.
 */
export function pinOwnerEntries(file: PatchFile, prior: PatchFile | null, restated: ReadonlySet<string> = new Set()): PatchFile {
  const pinned = (prior?.unfixable ?? []).filter((u) => u.suggested_repair);
  // The owner's readings are the owner's: a fixer reply never carries them, and never drops them.
  const ownerReadings = prior?.owner_readings ?? [];
  const pinnedIds = new Set(pinned.map((u) => u.node));
  const accepted = new Map((prior?.patches ?? []).filter((p) => p.accepted_weakening).map((p) => [p.node, p] as const));
  // A runner narrowing sent back only to be restated (`restated`) keeps its mark under a new
  // wording; an owner-accepted one is the repair the owner accepted — its ops, hypotheses, readings
  // and blocks, not its statement text alone — so a reply that changes any of it goes to the owner
  // again. (`supersedes` and a proof revision follow the ops; a free proof note is not the repair.)
  const key = (p: PatchFile["patches"][number]): string => {
    const { proof_note: _p, supersedes: _s, ...repair } = repairBody(p);
    return JSON.stringify(repair);
  };
  const same = (a: PatchFile["patches"][number], b: PatchFile["patches"][number]): boolean =>
    key(a) === key(b) || (restated.has(b.node) && a.narrowed_by === "runner");
  const { owner_readings: _o, ...reply } = file;
  return {
    ...reply,
    ...(ownerReadings.length > 0 ? { owner_readings: ownerReadings } : {}),
    patches: file.patches
      .filter((p) => !pinnedIds.has(p.node))
      .map((p) => {
        const a = accepted.get(p.node);
        if (!a || !same(a, p)) return p;
        // What a runner narrowing gives up is the fixer's current note, which a revision may complete;
        // an owner-accepted one keeps the text the owner accepted.
        const own = a.narrowed_by === "runner" ? noteGivesUp(p) : "";
        return {
          ...p,
          accepted_weakening: true,
          given_up: own || a.given_up,
          ...(!own && a.given_up_by ? { given_up_by: a.given_up_by } : {}),
          ...(a.narrowed_by ? { narrowed_by: a.narrowed_by } : {}),
        };
      }),
    unfixable: [
      ...file.unfixable
        .filter((u) => !pinnedIds.has(u.node))
        .map((u) => (u.suggested_repair && !u.suggested_by ? { ...u, suggested_by: "fixer" as const } : u)),
      ...pinned,
    ],
  };
}

function printedClaim(core: Core, id: string): string {
  const st = core.statements.find((s) => s.id === id);
  if (st) return st.statement;
  const a = core.assumptions.find((x) => x.id === id);
  if (a) return a.condition;
  const d = core.definitions.find((x) => x.id === id) as { statement?: string; definition?: string } | undefined;
  return d?.statement ?? d?.definition ?? "(not in the transcribed core)";
}

/** The MAIN THEOREMS, the only results whose weakening the owner decides: the core's `theorem` /
 * `corollary` statements (the paper's stated theorems; a corollary is transcribed as a theorem) and
 * the fixer's `key_results`. Every other node is an intermediate result. */
export function mainTheoremIds(core: Core, file: { key_results: readonly string[] } | null): Set<string> {
  return new Set([
    ...core.statements.filter((s) => /^(theorem|corollary)$/u.test(String(s.kind))).map((s) => s.id),
    ...(file?.key_results ?? []),
  ]);
}

/** One intermediate result narrowed by the runner: its node and what the narrowing gives up. */
export interface Narrowing {
  node: string;
  given_up: string;
}

/** The file with the pending suggestions of `nodes` applied as patches the RUNNER narrowed
 * (`accepted_weakening`, `narrowed_by: "runner"`). Pure. */
function narrowNodes(file: PatchFile, nodes: ReadonlySet<string>): { file: PatchFile; narrowed: Narrowing[] } {
  const picked = file.unfixable.filter((u) => nodes.has(u.node) && isPendingSuggestion(u));
  if (picked.length === 0) return { file, narrowed: [] };
  const ids = new Set(picked.map((u) => u.node));
  const applied = applySuggestions(file, ids);
  return {
    file: { ...applied, patches: applied.patches.map((p): Patch => (ids.has(p.node) ? { ...p, narrowed_by: "runner" } : p)) },
    narrowed: picked.map((u) => ({ node: u.node, given_up: u.suggested_repair!.given_up ?? "" })),
  };
}

/** Every pending suggestion on an INTERMEDIATE result (not a main theorem) applied as a patch the
 * runner narrowed. Pure. */
export function narrowIntermediates(core: Core, file: PatchFile): { file: PatchFile; narrowed: Narrowing[] } {
  const mains = mainTheoremIds(core, file);
  return narrowNodes(file, new Set(file.unfixable.filter((u) => isPendingSuggestion(u) && !mains.has(u.node)).map((u) => u.node)));
}

/** The ledger entries of the narrowed nodes stamped (`weakens_contribution`, `auto_narrowed`), and
 * one log line per node. */
function stampNarrowings(state: StateJson, file: PatchFile, narrowed: readonly Narrowing[], log: (m: string) => void): void {
  if (narrowed.length === 0) return;
  const verify = state.verify!;
  const ledger = { ...(verify.paper_errors ?? {}) };
  for (const n of narrowed) {
    const e = ledger[n.node] ?? { detail: "every repair weakens the claim", witness: null };
    const p = file.patches.find((x) => x.node === n.node);
    ledger[n.node] = {
      ...e,
      weakens_contribution: true,
      auto_narrowed: true,
      ...(p ? { suggested_repair: suggestionText({ ...p, given_up: n.given_up }) } : {}),
    };
    log(`${n.node} is an intermediate result: its strongest true version is applied automatically (narrowed: ${clip(n.given_up, 200)})`);
  }
  verify.paper_errors = ledger;
}

/**
 * The owner-scope rule applied to a patch file's pending suggestions: those on intermediate results
 * are applied as patches (ledger stamped, one log line each), and the receipt records the rest —
 * main theorems only — or is null when none is left. The caller writes `file`.
 */
export function settleSuggestions(
  state: StateJson,
  transcribed: Core,
  file: PatchFile,
  log: (m: string) => void,
): { file: PatchFile; narrowed: Narrowing[]; receipt: WeakeningRepair | null } {
  const { file: next, narrowed } = narrowIntermediates(transcribed, file);
  stampNarrowings(state, next, narrowed, log);
  return { file: next, narrowed, receipt: recordWeakeningReceipt(state, transcribed, next) };
}

/** What is wrong with the printed statement of a suggestion made of a consequential patch: the
 * corrected results it rests on, and the fixer's sentence on what it now uses. */
function followsRepairs(u: PatchFile["unfixable"][number]): string | undefined {
  if (!u.consequence_of?.length) return undefined;
  return `As printed, this result rests on ${u.consequence_of.join(", ")}, corrected by a repair, and no longer follows.${u.consequence_reason ? ` Changed to follow that repair: ${u.consequence_reason}` : ""}`;
}

/** The receipt for every pending suggestion of `file`, and the ledger updated with them. */
export function recordWeakeningReceipt(state: StateJson, transcribed: Core, file: PatchFile): WeakeningRepair | null {
  const verify = state.verify!;
  const pending = file.unfixable.filter(isPendingSuggestion);
  if (pending.length === 0) return null;
  const ledger = { ...(verify.paper_errors ?? {}) };
  const items: WeakeningItem[] = pending.map((u) => {
    const s = u.suggested_repair!;
    const e = ledger[u.node];
    // The finding on the PRINTED statement: the ledger's error, else the repairs the result was
    // changed to follow, else the fixer's reason — never a grade of the repair (that is `given_up`),
    // which is all the ledger holds of a node no finding named. Empty when none is on record.
    const wrong = [e?.detail, followsRepairs(u), u.reason].find((t) => t && !gradesRepair(t)) ?? "";
    ledger[u.node] = { ...(e ?? { detail: u.reason, witness: null }), weakens_contribution: true, suggested_repair: suggestionText(s) };
    return {
      node: u.node,
      printed: printedClaim(transcribed, u.node),
      proposed: s.corrected_statement ?? PROPOSED_UNCHANGED,
      // The proposal is the statement TOGETHER with the corollaries it splits off.
      ...(s.corollaries?.length ? { corollaries: s.corollaries.map((c) => ({ ...(c.title ? { title: c.title } : {}), statement: c.statement })) } : {}),
      given_up: s.given_up ?? "",
      ...(s.given_up_by ? { given_up_by: s.given_up_by } : {}),
      detail: wrong,
      witness: e && wrong === e.detail ? e.witness : null,
      source: u.suggested_by ?? "fixer",
      ...(u.owner_explanation ? { owner_explanation: u.owner_explanation } : {}),
      ...(e?.owner_decision === "redo" && e.guidance ? { guidance: e.guidance } : {}),
    };
  });
  verify.paper_errors = ledger;
  // Written again by a later round of the same receipt: it stays unpresented until a pass confirms,
  // and the owner's rulings so far on items still listed stand.
  const prior = verify.weakening_repair?.status === "pending" ? verify.weakening_repair : null;
  const unconfirmed = prior?.unconfirmed === true;
  const decisions = Object.fromEntries(Object.entries(prior?.decisions ?? {}).filter(([node]) => items.some((i) => i.node === node)));
  verify.weakening_repair = { status: "pending", items, ...(Object.keys(decisions).length > 0 ? { decisions } : {}), ...(unconfirmed ? { unconfirmed } : {}), at: new Date().toISOString() };
  return verify.weakening_repair;
}

/** The halt message (main theorems only — intermediate results are narrowed automatically): each suggestion compactly, and the owner's three answers. */
/** How results left without their weakened repair are reported: refuted when a witness stands against
 * the printed statement, not determined when the paper leaves it open (`PaperError.undetermined`). */
function unrepairedWord(nodes: readonly string[], ledger: Record<string, PaperError> | undefined): string {
  const open = nodes.filter((n) => ledger?.[n]?.undetermined === true).length;
  return open === 0 ? "refuted" : open === nodes.length ? "not determined" : "refuted, or not determined where the paper leaves the statement open";
}

export function weakeningMessage(rec: WeakeningRepair, slug: string, ledger?: Record<string, PaperError> | undefined): string {
  const items = rec.items
    .map((i) =>
      [
        `    - ${i.node} (${i.source === "referee" ? "the referee found the repair weakens the claim" : "the fixer found no repair that keeps it"})`,
        `        printed:  ${clip(i.printed)}`,
        `        proposed: ${clip(i.proposed)}`,
        ...(i.corollaries ?? []).map((c, k) => `        with corollary ${k + 1}${c.title ? ` (${c.title})` : ""}: ${clip(c.statement)}`),
        ...(i.given_up.trim() ? [`        gives up: ${clip(i.given_up)}`] : []),
        ...(i.witness ? [`        witness:  ${clip(i.witness)}`] : []),
        ...(i.guidance ? [`        your earlier guidance (--redo-repair): ${clip(i.guidance, 600)}`] : []),
      ].join("\n"),
    )
    .join("\n");
  return (
    `WEAKENED REPAIR: no repair keeps ${rec.items.length} main theorem(s) at full strength; the strongest true version is suggested. ` +
    "The run halts for the paper's owner (in every mode, auto mode included).\n" +
    `${items}\n  Continue with one of:\n` +
    `    leansmith verify ${slug} --resume --accept-repair              (apply them; a V1.5 pass confirms them; reported repaired, contribution narrowed)\n` +
    `    leansmith verify ${slug} --resume --decline-repair "<reason>"  (report them ${unrepairedWord(rec.items.map((i) => i.node), ledger)}; they and what rests on them leave Lean; the run goes on)\n` +
    `    leansmith verify ${slug} --resume --reject-finding "<reading>" (the finding is wrong: the printed statement stands under your reading, which binds the formalization)\n` +
    `    leansmith verify ${slug} --resume --redo-repair "<node>: <guidance>" (discard the suggestion; the fixer repairs that result again along your guidance, and a V1.5 pass confirms it)\n` +
    "  A bare answer covers the batch. To rule item by item in one resume, name nodes: --accept-repair <node>[,<node>], --decline-repair \"<node>[,<node>]: <reason>\", " +
    "--reject-finding \"<node>: <reading>\", --redo-repair \"<node>: <guidance>\" (--reject-finding and --redo-repair repeatable; --accept-repair and --decline-repair once each, several nodes separated by commas); a bare answer alongside them covers the items not named, and items no answer names are presented again.\n" +
    "  (with the --toolkit / --slug / --dry-run the run was started with)"
  );
}

/** `--decline-repair "<node>[,<node>]: <reason>"`: the node-scoped form (else the value is a bare
 * reason). The colon is read as every other node-scoped answer reads it, with or without a space. */
export const DECLINE_NODES = /^\s*([A-Za-z]+:[A-Za-z0-9._-]+(?:\s*,\s*[A-Za-z]+:[A-Za-z0-9._-]+)*)\s*:\s*(\S[\s\S]*)$/;

/** The answers to a halt an invocation may carry (`leansmith verify … --resume <answer>`): the
 * parser and the runner share this shape and the one rule on how they combine (`haltAnswerConflict`). */
export interface HaltAnswers {
  rejectRewind?: string | null;
  clearPatchCap?: boolean;
  acceptCap?: boolean;
  acceptRepair?: boolean | readonly string[];
  declineRepair?: string | null;
  rejectFinding?: string | readonly string[] | null;
  redoRepair?: readonly string[] | null;
  addCondition?: readonly string[] | null;
  editReading?: readonly string[] | null;
  removeReading?: readonly string[] | null;
  umbrella?: readonly string[] | null;
}

/** The answer flags `a` gives, by name, in a fixed order; empty when it answers nothing. */
export function haltAnswerFlags(a: HaltAnswers): string[] {
  const some = (v: readonly string[] | null | undefined): boolean => (v?.length ?? 0) > 0;
  return [
    a.rejectRewind != null && "--reject-rewind",
    a.clearPatchCap && "--clear-patch-cap",
    a.acceptCap && "--accept-cap",
    (a.acceptRepair === true || (Array.isArray(a.acceptRepair) && a.acceptRepair.length > 0)) && "--accept-repair",
    a.declineRepair != null && "--decline-repair",
    a.rejectFinding != null && (typeof a.rejectFinding === "string" || a.rejectFinding.length > 0) && "--reject-finding",
    some(a.redoRepair) && "--redo-repair",
    some(a.addCondition) && "--add-condition",
    some(a.editReading) && "--edit-reading",
    some(a.removeReading) && "--remove-reading",
    some(a.umbrella) && "--umbrella",
  ].filter(Boolean) as string[];
}

/** Why the answers of `a` cannot be given together, or null. The answers to a weakened-repair receipt
 * combine (node-scoped, item by item), at most one of them bare (covering the items no other names);
 * so do the two revisions of an owner reading; any other answer stands alone. */
export function haltAnswerConflict(a: HaltAnswers): string | null {
  const answers = haltAnswerFlags(a);
  if (answers.length <= 1) return null;
  const receipt = new Set(["--accept-repair", "--decline-repair", "--reject-finding", "--redo-repair"]);
  const revisions = new Set(["--edit-reading", "--remove-reading"]);
  if (!answers.every((x) => receipt.has(x)) && !answers.every((x) => revisions.has(x))) return `${answers.join(" and ")} answer different halts; give one.`;
  const bare = [a.acceptRepair === true && "--accept-repair", a.declineRepair != null && !DECLINE_NODES.test(a.declineRepair) && "--decline-repair"].filter(Boolean);
  if (bare.length > 1) return `${bare.join(" and ")} both answer the whole receipt; give one, or name nodes (--accept-repair <node>, --decline-repair "<node>: <reason>").`;
  return null;
}

/** The receipt's items the owner has not ruled on yet. */
export function undecidedItems(rec: WeakeningRepair): WeakeningItem[] {
  return rec.items.filter((i) => !rec.decisions?.[i.node]);
}

/** Record the owner's ruling on `nodes`; the receipt closes once every item is ruled on (status: the
 * one ruling, or `ruled` when they differ). */
export function recordDecisions(verify: NonNullable<StateJson["verify"]>, nodes: Iterable<string>, decision: WeakeningDecision): void {
  const rec = verify.weakening_repair;
  if (!rec) return;
  const decisions = { ...(rec.decisions ?? {}) };
  for (const n of nodes) decisions[n] = decision;
  verify.weakening_repair = { ...rec, decisions };
  if (undecidedItems(verify.weakening_repair).length === 0) closeReceipt(verify);
}

/** Close the receipt after a resume's answers: the items ruled on keep their rulings; any item no
 * answer named stays a pending suggestion in the patch file and is presented again at the next halt. */
export function closeReceipt(verify: NonNullable<StateJson["verify"]>): void {
  const rec = verify.weakening_repair;
  if (!rec || rec.status !== "pending") return;
  const ruled = rec.items.filter((i) => rec.decisions?.[i.node]);
  if (ruled.length === 0) return;
  const kinds = [...new Set(ruled.map((i) => rec.decisions![i.node]!))];
  verify.weakening_repair = { ...rec, items: ruled, status: kinds.length === 1 ? kinds[0]! : "ruled" };
}

/** The owner's node-scoped rulings on a pending receipt (`--accept-repair`, `--decline-repair`,
 * `--redo-repair`; withdrawals go through `owner_rulings.ts`). */
export interface ReceiptRulings {
  accept?: readonly string[];
  decline?: ReadonlyArray<{ node: string; reason: string }>;
  redo?: ReadonlyArray<{ node: string; guidance: string }>;
}

/**
 * The owner's answers on items of a pending receipt, in one patch-file write: an accepted suggestion
 * becomes a patch (`accepted_weakening`), a declined one is marked declined, and a REDONE one is
 * discarded — the fixer answers that node again in V1 patch mode, the owner's guidance binding (the
 * directive's `owner_guidance`, rendered as the OWNER GUIDANCE block with the node's SERVES block);
 * its error stays open, stamped `owner_decision: "redo"` with the guidance. The ledger is stamped,
 * `core.json` rebuilt, and the run goes to V1 patch mode (a redo) or a fresh V1.5 pass. Returns the
 * log lines.
 */
export async function ruleOnReceipt(runDir: string, state: StateJson, r: ReceiptRulings, opts: { check?: boolean } = {}): Promise<string[]> {
  const verify = state.verify!;
  const rec = verify.weakening_repair;
  if (!rec || rec.status !== "pending") throw new Error("no weakened repair is pending (state.verify.weakening_repair).");
  const file = await readPatchFile(runDir);
  if (!file) throw new Error(`${VERIFY_FILES.patches} is missing: the suggested repairs live there.`);
  const open = new Set(undecidedItems(rec).map((i) => i.node).filter((n) => file.unfixable.some((u) => u.node === n && isPendingSuggestion(u))));
  const accept = new Set(r.accept ?? []);
  const decline = new Map((r.decline ?? []).map((d) => [d.node, ownerWordsTex(d.reason.trim())] as const));
  const redo = new Map((r.redo ?? []).map((d) => [d.node, ownerWordsTex(d.guidance.trim())] as const));
  const named = [...accept, ...decline.keys(), ...redo.keys()];
  if (named.length === 0) throw new Error("no ruling given.");
  const seen = new Set<string>();
  for (const n of named) {
    if (seen.has(n)) throw new Error(`${n} is named by two answers; give one answer per result.`);
    seen.add(n);
    if (!open.has(n)) throw new Error(`${n} is not a pending item of the receipt (pending: ${[...open].join(", ") || "none"}).`);
  }
  for (const [n, why] of decline) if (!why) throw new Error(`--decline-repair on ${n} needs a reason: say why the weakened version is not worth formalizing.`);
  for (const [n, g] of redo) if (!g) throw new Error(`--redo-repair "${n}: <guidance>" needs the guidance: say how the fixer should repair it.`);
  const next: PatchFile = {
    ...applySuggestions(file, accept),
  };
  next.unfixable = next.unfixable
    .filter((u) => !redo.has(u.node))
    .map((u) => (decline.has(u.node) ? { ...u, declined: decline.get(u.node)! } : u));
  // The consequential patches held for these suggestions (`set_aside`): applied with an accepted one
  // (every repair it follows is now a patch), dropped with a declined or redone one.
  const ruled = (p: Patch): boolean => (p.consequence_of ?? []).some((o) => decline.has(o) || redo.has(o));
  const applied = (next.set_aside ?? []).filter((p) => !ruled(p) && (p.consequence_of ?? []).every((o) => next.patches.some((x) => x.node === o)));
  const stillHeld = (next.set_aside ?? []).filter((p) => !ruled(p) && !applied.includes(p));
  next.patches = [...next.patches, ...applied];
  if (stillHeld.length > 0) next.set_aside = stillHeld;
  else delete next.set_aside;
  const transcribed = await readTranscribedCore(runDir);
  const bad = validatePatchFile(transcribed, next, openErrorIds(verify.paper_errors).filter((id) => !redo.has(id)));
  if (bad.length > 0) throw new Error(`the answered patch file does not fit the transcribed core: ${bad.join(" ")} Fix ${VERIFY_FILES.patches}, then answer again.`);
  if (opts.check) return []; // (every refusal is above)
  await writeJsonAtomic(path.join(runDir, VERIFY_FILES.patches), next);
  await rebuildPatchedCore(runDir, { detectHandEdits: false });
  const ledger = { ...(verify.paper_errors ?? {}) };
  const item = new Map(rec.items.map((i) => [i.node, i] as const));
  const entry = (id: string) => ledger[id] ?? { detail: item.get(id)?.detail || "every repair weakens the contribution", witness: item.get(id)?.witness ?? null };
  for (const id of accept) ledger[id] = { ...entry(id), weakens_contribution: true, owner_decision: "accepted" };
  for (const [id, reason] of decline) ledger[id] = { ...entry(id), weakens_contribution: true, owner_decision: "declined", decision_reason: reason };
  for (const [id, guidance] of redo) {
    // The suggestion is discarded: the node is an open error again, to be repaired under the guidance.
    const { weakens_contribution: _w, suggested_repair: _s, decision_reason: _d, ...e } = entry(id);
    ledger[id] = { ...e, owner_decision: "redo", guidance };
  }
  verify.paper_errors = ledger;
  const lines: string[] = [];
  if (accept.size > 0) lines.push(`--accept-repair: the owner accepts the weakened repair of ${[...accept].join(", ")}; applied as patches${applied.length > 0 ? ` with the consequential patch(es) held for it (${applied.map((p) => p.node).join(", ")})` : ""}, a fresh V1.5 pass confirms them.`);
  if (decline.size > 0) lines.push(`--decline-repair: the owner declines the weakened repair of ${[...decline.keys()].join(", ")} (${[...new Set(decline.values())].join("; ")}); reported ${unrepairedWord([...decline.keys()], ledger)} and left out of Lean with what rests on them — the run goes on.`);
  if (redo.size > 0) {
    await writeJsonAtomic(path.join(runDir, VERIFY_FILES.v1ReviseDirective), {
      mode: "patch",
      round: Math.max(1, roundsUsed(verify, "error")),
      findings: [...redo].map(([id, guidance]) => {
        const e = ledger[id]!;
        return { id, axis: "correctness", detail: e.detail, witness: e.witness, owner_guidance: guidance };
      }),
    });
    lines.push(`--redo-repair: the owner discards the suggested repair of ${[...redo.keys()].join(", ")}; the fixer repairs ${redo.size > 1 ? "them" : "it"} again under the owner's guidance (V1 patch mode), then a V1.5 pass confirms the result.`);
  }
  recordDecisions(verify, accept, "accepted");
  recordDecisions(verify, decline.keys(), "declined");
  recordDecisions(verify, redo.keys(), "redo");
  verify.core_sha256 = null;
  verify.phase = redo.size > 0 ? "init" : "v1";
  state.stage_completed = "V1";
  return lines;
}

/** A suggested repair as it stood when sent back to the fixer (the directive finding's `withdrawn_repair`):
 * the fixer's new entry replaces it whole — its ops apply to the printed text — so it is shown what to keep.
 * The repair's body without its proof note (the fixer writes that afresh). */
export type WithdrawnRepair = Omit<RepairBody, "proof_note">;

/** The suggested repair of `node` on `file`, as a `WithdrawnRepair`; undefined when it has none. Pure. */
export function withdrawnRepair(file: PatchFile, node: string): WithdrawnRepair | undefined {
  const sr = file.unfixable.find((u) => u.node === node)?.suggested_repair;
  if (!sr) return undefined;
  const { proof_note: _p, ...body } = repairBody(sr);
  return body;
}

/** Suggested repairs sent back to the fixer before the owner rules: they leave the patch file (the
 * node's error stays in the ledger, without its weakening mark) and the receipt; `core.json` is
 * rebuilt. */
export async function withdrawSuggestions(runDir: string, state: StateJson, file: PatchFile, nodes: readonly string[]): Promise<void> {
  const verify = state.verify!;
  const out = new Set(nodes);
  const transcribed = await readTranscribedCore(runDir);
  const next: PatchFile = { ...file, unfixable: file.unfixable.filter((u) => !out.has(u.node)) };
  const bad = validatePatchFile(transcribed, next, openErrorIds(verify.paper_errors).filter((id) => !out.has(id)));
  if (bad.length > 0) throw new Error(`sending the suggested repair of ${nodes.join(", ")} back: the patch file does not fit the transcribed core: ${bad.join(" ")} Fix ${VERIFY_FILES.patches}, then --resume.`);
  await writeJsonAtomic(path.join(runDir, VERIFY_FILES.patches), next);
  await rebuildPatchedCore(runDir, { detectHandEdits: false });
  const ledger = { ...(verify.paper_errors ?? {}) };
  const item = new Map((verify.weakening_repair?.items ?? []).map((i) => [i.node, i] as const));
  for (const id of out) {
    const { weakens_contribution: _w, suggested_repair: _s, ...e } = ledger[id] ?? { detail: item.get(id)?.detail || "every repair weakens the contribution", witness: item.get(id)?.witness ?? null };
    ledger[id] = e;
  }
  verify.paper_errors = ledger;
  const rec = verify.weakening_repair;
  if (rec?.status === "pending") {
    const items = rec.items.filter((i) => !out.has(i.node));
    verify.weakening_repair = items.length > 0 ? { ...rec, items } : null;
  }
}

/**
 * The repairs whose texts the annotated paper printed verbatim because they do not compile against the
 * paper's preamble (`compile`, by node: the render's routing, `fragment_routing.ts`) go back to the fixer
 * in ONE scoped round (the directive names only them; every other entry is carried), each with the
 * compiler's line. A patch stays applied until the fixer's answer replaces it; its V1.5 confirmation is
 * dropped, so the next pass grades it afresh. A pending suggestion is discarded — the node is an open
 * error again — and a pending receipt is withdrawn whole. A patch directive already on file takes the
 * findings in, so it stays one round. Each text is sent back once (`restatement_rounds`). Returns the
 * log lines; none when nothing was sent.
 */
export async function restateAllPatches(runDir: string, state: StateJson, compile: ReadonlyMap<string, ReadonlyArray<{ where: string; text: string; error: string }>>): Promise<string[]> {
  const verify = state.verify!;
  const file = await readPatchFile(runDir);
  if (!file) return [];
  const directivePath = path.join(runDir, VERIFY_FILES.v1ReviseDirective);
  const pendingDirective = existsSync(directivePath) ? (JSON.parse(await readFile(directivePath, "utf8")) as { mode?: string; round?: number; findings?: Array<Record<string, unknown> & { id: string }> }) : null;
  // A revise (re-transcription) directive re-reads the paper: its patches are judged after it.
  if (pendingDirective && pendingDirective.mode !== "patch") return [];
  const entries = [...file.patches.map((p) => ({ node: p.node, what: "patch" as const })), ...file.unfixable.filter(isPendingSuggestion).map((u) => ({ node: u.node, what: "suggestion" as const }))];
  const done = new Set(verify.restatement_rounds ?? []);
  const back: Array<{ node: string; what: "patch" | "suggestion"; problems: string[]; key: string }> = [];
  for (const e of entries) {
    const failing = compile.get(e.node) ?? [];
    const key = createHash("sha256").update(JSON.stringify([e.node, "compile", failing.map((f) => f.text)])).digest("hex").slice(0, 16);
    if (failing.length > 0 && !done.has(key)) back.push({ node: e.node, what: e.what, problems: failing.map((f) => `${f.where} does not compile: ${f.error}${mathModeHint(f.error, f.text)} — ${TEX_FRAGMENT_RULE}.`), key });
  }
  if (back.length === 0) return [];
  const withdrawn = verify.weakening_repair?.status === "pending";
  const suggestions = back.filter((b) => b.what === "suggestion").map((b) => b.node);
  const was = new Map(suggestions.map((n) => [n, withdrawnRepair(file, n)] as const));
  if (suggestions.length > 0) await withdrawSuggestions(runDir, state, file, suggestions);
  const ledger = verify.paper_errors ?? {};
  const findings = back.map((b) => {
    const e = ledger[b.node];
    return b.what === "suggestion"
      ? { id: b.node, axis: "correctness", detail: e!.detail, witness: e!.witness, restatement: b.problems, ...(was.get(b.node) ? { withdrawn_repair: was.get(b.node) } : {}) }
      : { id: b.node, axis: "restatement", detail: e?.detail ?? "a text of the repair does not compile", witness: e?.witness ?? null, restatement: b.problems };
  });
  const merged = [...(pendingDirective?.findings ?? [])];
  for (const f of findings) {
    const at = merged.findIndex((x) => x.id === f.id);
    if (at >= 0) merged[at] = { ...merged[at]!, restatement: f.restatement, ...("withdrawn_repair" in f && f.withdrawn_repair ? { withdrawn_repair: f.withdrawn_repair } : {}) };
    else merged.push(f);
  }
  await writeJsonAtomic(directivePath, { ...(pendingDirective ?? {}), mode: "patch", round: pendingDirective?.round ?? Math.max(1, roundsUsed(verify, "error")), findings: merged });
  for (const b of back) {
    if (verify.confirmed) delete verify.confirmed[b.node];
    if (verify.level_pause?.carry) delete verify.level_pause.carry[b.node];
  }
  verify.restatement_rounds = [...done, ...back.map((b) => b.key)];
  if (withdrawn) verify.weakening_repair = null;
  verify.core_sha256 = null;
  verify.phase = "init";
  state.stage_completed = "V1";
  return [
    `render check: ${back.length} repair(s) with a text that does not compile — one scoped fixer round answers ${back.map((b) => b.node).join(", ")}${pendingDirective ? " (joined to the patch round already on file)" : ""}${withdrawn ? "; the pending receipt is withdrawn and presented again after the round" : ""}.`,
    ...back.map((b) => `render check: ${b.what === "suggestion" ? `the suggested repair of ${b.node}` : `the patch on ${b.node}`}: ${b.problems.join("; ")}`),
  ];
}

