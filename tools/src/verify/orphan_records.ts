/**
 * No record left on a node a V1 restructuring removed.
 *
 * A V1 revise round may remove or rename a statement node — a runner-applied referee fix, or the
 * agent's own edit (live CNS 2026-09-26: the agent deleted `lem:cont-elasticity` / `lem:cont-deriv`,
 * whose repairs then named no node, and V1.5 checkpointed on the patch file). Whatever the round
 * did, each removed node's records — its patch or `unfixable` entry, its error-ledger entry, its
 * findings, a key-result mark — move to the node that now prints the same content, through the one
 * id remap (`remapNodeIds`). The carrier is found from the texts alone: the new
 * node printing the removed node's statement exactly; else the one node whose statement contains
 * it; else, among several, the one under the same hypotheses. A removed node with no carrier (no
 * node, or several indistinguishable ones, or one that carries a repair of its own) never halts the
 * run: its records leave the patch file and the ledger — kept, with the reason, in
 * `discovery/orphaned_records.json` — and the nodes that print its text lose their confirmation, so
 * the next V1.5 pass grades them afresh and an error it re-finds goes to the fixer's scoped round.
 * A removed node's confirmation or last-drift entry alone is dropped (the carrier is new).
 */
import { existsSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import { writeJsonAtomic } from "../shared/json_atomic.js";
import { remapNodeIds, statementBody, type IdKeyedState, type PatchFileLike } from "./core_graph.js";
import { VERIFY_FILES } from "./types.js";

export const ORPHANED_RECORDS_FILE = "discovery/orphaned_records.json";

/** The parts of a core the carrier search reads. */
export interface OrphanCoreLike {
  statements: ReadonlyArray<{ id: string; statement: string; depends_on?: readonly string[] }>;
  assumptions: ReadonlyArray<{ id: string }>;
  definitions: ReadonlyArray<{ id: string }>;
}

export interface OrphanPlan {
  /** removed id → the node that now carries its content */
  carriers: Record<string, string>;
  /** removed ids whose records have no carrier, with the reason and the nodes printing its text */
  unresolved: Array<{ id: string; reason: string; candidates: string[] }>;
  /** removed ids whose only records are a confirmation / last-drift entry: dropped */
  stale: string[];
}

export interface OrphanedRecord {
  at: string;
  node: string;
  reason: string;
  candidates: string[];
  patch: unknown;
  unfixable: unknown;
  paper_error: unknown;
}

const norm = (t: string): string => t.replace(/\s+/gu, " ").trim();

/** Ids that carry a record which must follow the content (a repair, a ledger entry, a finding, a key-result mark). */
function substantiveIds(file: PatchFileLike | null, verify: IdKeyedState): Set<string> {
  return new Set([
    ...(file?.patches ?? []).map((p) => p.node),
    ...(file?.unfixable ?? []).map((u) => u.node),
    ...(file?.key_results ?? []),
    ...Object.keys(verify.paper_errors ?? {}),
    ...(verify.findings ?? []).map((f) => f.node),
  ]);
}

/** Which removed nodes carry records, and where each record goes. Pure. */
export function planOrphans(before: OrphanCoreLike, after: OrphanCoreLike, file: PatchFileLike | null, verify: IdKeyedState): OrphanPlan {
  // removed = a node of the previous transcription the new one lacks (ids a patch or a review adds
  // are in neither and are never touched here)
  const ids = (core: OrphanCoreLike): Set<string> => new Set([...core.statements, ...core.assumptions, ...core.definitions].map((n) => n.id));
  const kept = ids(after);
  const removed = new Set([...ids(before)].filter((id) => !kept.has(id)));
  const substantive = substantiveIds(file, verify);
  const bookkeeping = new Set([...Object.keys(verify.confirmed ?? {}), ...Object.keys(verify.last_drift ?? {})]);
  const hypsOf = (core: OrphanCoreLike, deps: readonly string[] | undefined): string => {
    const ass = new Set(core.assumptions.map((a) => a.id));
    return [...new Set((deps ?? []).filter((d) => ass.has(d)))].sort().join(",");
  };
  const plan: OrphanPlan = { carriers: {}, unresolved: [], stale: [] };
  for (const id of [...bookkeeping].filter((x) => removed.has(x) && !substantive.has(x))) plan.stale.push(id);
  for (const id of [...substantive].filter((x) => removed.has(x))) {
    const old = before.statements.find((s) => s.id === id);
    if (!old) {
      plan.unresolved.push({ id, reason: "it is not a statement node, so no printed statement locates its carrier", candidates: [] });
      continue;
    }
    const body = norm(statementBody(old.statement));
    const exact = after.statements.filter((s) => norm(s.statement) === norm(old.statement));
    const containing = after.statements.filter((s) => body.length > 0 && norm(statementBody(s.statement)).includes(body));
    const sameHyps = containing.filter((s) => hypsOf(after, s.depends_on) === hypsOf(before, old.depends_on));
    const pick = exact.length === 1 ? exact : containing.length === 1 ? containing : sameHyps.length === 1 ? sameHyps : [];
    if (pick.length === 1) {
      plan.carriers[id] = pick[0]!.id;
      continue;
    }
    plan.unresolved.push({
      id,
      reason:
        containing.length === 0
          ? "no node of the new transcription prints its statement"
          : `${containing.length} nodes print its statement (${containing.map((s) => s.id).join(", ")}) and ${sameHyps.length === 0 ? "none" : "several"} under its hypotheses`,
      candidates: containing.map((s) => s.id),
    });
  }
  // A carrier takes one removed node's repair / ledger entry, and only when it has none of its own.
  const heavy = (id: string): boolean =>
    (file?.patches ?? []).some((p) => p.node === id) || (file?.unfixable ?? []).some((u) => u.node === id) || Object.hasOwn(verify.paper_errors ?? {}, id);
  const byCarrier = new Map<string, string[]>();
  for (const [id, c] of Object.entries(plan.carriers)) if (heavy(id)) byCarrier.set(c, [...(byCarrier.get(c) ?? []), id]);
  for (const [c, ids] of byCarrier) {
    if (ids.length === 1 && !heavy(c)) continue;
    for (const id of ids) {
      delete plan.carriers[id];
      plan.unresolved.push({
        id,
        reason: ids.length > 1 ? `${c} would receive the repairs of ${ids.join(" and ")}` : `${c}, which prints its statement, already carries a repair or error of its own`,
        candidates: [c],
      });
    }
  }
  return plan;
}

/** Apply a plan: remap to carriers, set the unresolved aside. Pure on the file; mutates `verify`. */
export function applyOrphanPlan<F extends PatchFileLike>(plan: OrphanPlan, fileIn: F | null, verify: IdKeyedState): { file: F | null; setAside: OrphanedRecord[] } {
  let file = Object.keys(plan.carriers).length > 0 ? remapNodeIds(plan.carriers, fileIn, verify) : fileIn;
  // a carrier's statement now takes a repair it was not graded with: graded afresh
  for (const c of Object.values(plan.carriers)) {
    if (verify.confirmed) delete verify.confirmed[c];
    if (verify.last_drift) delete verify.last_drift[c];
  }
  const at = new Date().toISOString();
  const setAside: OrphanedRecord[] = [];
  for (const u of plan.unresolved) {
    setAside.push({
      at,
      node: u.id,
      reason: u.reason,
      candidates: u.candidates,
      patch: file?.patches.find((p) => p.node === u.id) ?? null,
      unfixable: file?.unfixable.find((x) => x.node === u.id) ?? null,
      paper_error: verify.paper_errors?.[u.id] ?? null,
    });
    const to = (ids: string[]): string[] => [...new Set(ids.flatMap((x) => (x === u.id ? u.candidates : [x])))];
    if (file) {
      file = {
        ...file,
        key_results: u.candidates.length > 0 ? to(file.key_results) : file.key_results,
        patches: file.patches.filter((p) => p.node !== u.id),
        unfixable: file.unfixable.filter((x) => x.node !== u.id),
      };
    }
    if (verify.paper_errors) delete verify.paper_errors[u.id];
    if (verify.findings) verify.findings = verify.findings.filter((f) => f.node !== u.id);
    for (const c of [u.id, ...u.candidates]) {
      if (verify.confirmed) delete verify.confirmed[c];
      if (verify.last_drift) delete verify.last_drift[c];
    }
  }
  for (const id of plan.stale) {
    if (verify.confirmed) delete verify.confirmed[id];
    if (verify.last_drift) delete verify.last_drift[id];
  }
  return { file, setAside };
}

/** One line per move, for the log. */
export function orphanPlanLines(plan: OrphanPlan): string[] {
  return [
    ...Object.entries(plan.carriers).map(([id, c]) => `${id} was removed by this round — its repair, ledger entry and findings now on ${c}, which prints the same statement`),
    ...plan.unresolved.map(
      (u) =>
        `${u.id} was removed by this round and its records have no carrier (${u.reason}) — set aside in ${ORPHANED_RECORDS_FILE}` +
        (u.candidates.length ? `; ${u.candidates.join(", ")} will be graded afresh, and an error found there goes to the fixer` : ""),
    ),
  ];
}

/**
 * At a V1 revise acceptance, before the transcription snapshot: carry every record on a node the
 * round removed (the previous `core.transcribed.json` → `after`). Writes the patch file and the
 * set-aside file when they change; mutates `verify`. Returns the log lines.
 */
export async function carryOrphanedRecords(runDir: string, after: OrphanCoreLike, verify: IdKeyedState, fileIn: PatchFileLike | null): Promise<string[]> {
  const beforePath = path.join(runDir, VERIFY_FILES.coreTranscribed);
  if (!existsSync(beforePath)) return [];
  const before = JSON.parse(await readFile(beforePath, "utf8")) as OrphanCoreLike;
  const plan = planOrphans(before, after, fileIn, verify);
  if (Object.keys(plan.carriers).length + plan.unresolved.length + plan.stale.length === 0) return [];
  const { file, setAside } = applyOrphanPlan(plan, fileIn, verify);
  if (file && JSON.stringify(file) !== JSON.stringify(fileIn)) await writeJsonAtomic(path.join(runDir, VERIFY_FILES.patches), file);
  if (setAside.length > 0) {
    const p = path.join(runDir, ORPHANED_RECORDS_FILE);
    const prior = existsSync(p) ? (JSON.parse(await readFile(p, "utf8")) as OrphanedRecord[]) : [];
    await writeJsonAtomic(p, [...prior, ...setAside]);
  }
  return orphanPlanLines(plan);
}
