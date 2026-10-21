/**
 * The two patch-loop counters and the halt at their caps (user decisions 2026-09-23, 2026-09-26).
 *
 * `patch_rounds` counts ERROR rounds (a defect of a paper claim), `refinement_rounds` counts
 * REFINEMENT rounds (an F-stage clarify rewind, a minimality-only round). Error rounds are capped
 * PER DEPENDENCY LEVEL (`patch_rounds_by_level`, `MAX_PATCH_ROUNDS_PER_LEVEL` each): fix as you go
 * spends a round on every defective level, so a large paper is not stopped for being large. A
 * round is charged to the level of the whole core (`referee_levels.ts` over every node, so the key
 * is stable across passes — a pause's own tag is relative to what that pass still grades) of the
 * nodes that stopped the grading; the final
 * global pass and an F-stage rewind charge `global`. `patch_rounds` stays the whole-run total,
 * capped by the BACKSTOP 3 × the core's level count (at least `MIN_PATCH_BACKSTOP`).
 * A round due while a cap is reached never fails the run: the runner records
 * `state.verify.cap_reached` — the counter, the rounds spent, the level and its nodes, the findings
 * the round would carry and what the fixer's patch file proposes — and halts for the orchestrator
 * in every mode, auto mode included. `--resume --clear-patch-cap` grants one more window (the
 * level's counter resets; at the backstop the total resets), `--resume --accept-cap` ends the
 * loop: at a V1.5 refinement cap the correct-but-non-minimal repair is accepted and F1 formalizes
 * it; otherwise V6 reports the state as it stands. Both are refused unless the run halted at a cap.
 */
import type { Core } from "../core/schema.js";
import type { PatchFile } from "./patches.js";
import { refereeLevels } from "./referee_levels.js";
import {
  MAX_PATCH_ROUNDS_PER_LEVEL,
  MAX_REFINEMENT_ROUNDS,
  MIN_PATCH_BACKSTOP,
  type CapReached,
  type PatchRoundKind,
  type RoundScope,
  type VerifyState,
} from "./types.js";

/** The key of error rounds not charged to a dependency level. */
export const GLOBAL_LEVEL = "global";

export function roundCounter(kind: PatchRoundKind): CapReached["counter"] {
  return kind === "refinement" ? "refinement_rounds" : "patch_rounds";
}

/** The dependency levels of the whole core (every definition, assumption and statement). */
function coreLevels(core: Core): string[][] {
  const ids = [...core.definitions, ...core.assumptions, ...core.statements].map((n) => n.id);
  return refereeLevels(core, ids).levels;
}

/** The whole-run backstop on error rounds: 3 × the core's (non-empty) level count, at least 6. */
export function patchBackstop(core: Core): number {
  return Math.max(MIN_PATCH_BACKSTOP, MAX_PATCH_ROUNDS_PER_LEVEL * coreLevels(core).filter((l) => l.length > 0).length);
}

/** The lowest level of the whole core holding one of `ids` (`L<k>`), or `global` (none of them is a node). */
export function levelOf(core: Core, ids: readonly string[]): string {
  const want = new Set(ids);
  const k = coreLevels(core).findIndex((l) => l.some((id) => want.has(id)));
  return k < 0 ? GLOBAL_LEVEL : `L${k}`;
}

/** State from before the per-level caps (a flat `patch_rounds`, no map): the rounds spent count on
 * the level paused now (`level_pause`, its nodes' owners), else on `global`. */
export function migratePatchRounds(verify: VerifyState, core: Core | null): void {
  if (verify.patch_rounds_by_level) return;
  const n = verify.patch_rounds ?? 0;
  const lp = verify.level_pause;
  const key = lp && core ? levelOf(core, lp.errors.flatMap((e) => e.targets)) : GLOBAL_LEVEL;
  verify.patch_rounds_by_level = n > 0 ? { [key]: n } : {};
}

/** Where an error round is charged: `owners` = the owners of the nodes that stopped the grading at a
 * level, `null` for a round not due at a level (the global pass, an F-stage rewind). */
export function errorScope(verify: VerifyState, core: Core, owners: readonly string[] | null): RoundScope {
  migratePatchRounds(verify, core);
  const nodes = [...new Set(owners ?? [])];
  return { level: nodes.length > 0 ? levelOf(core, nodes) : GLOBAL_LEVEL, nodes, backstop: patchBackstop(core) };
}

/** Rounds of `kind` spent over the whole run (for an error round: the backstop counter). */
export function roundsUsed(verify: VerifyState, kind: PatchRoundKind): number {
  return verify[roundCounter(kind)] ?? 0;
}

function levelRounds(verify: VerifyState, level: string): number {
  return verify.patch_rounds_by_level?.[level] ?? 0;
}

function needScope(kind: PatchRoundKind, scope: RoundScope | null | undefined): RoundScope | null {
  if (kind === "error" && !scope) throw new Error("an error round needs its scope (caps.ts errorScope)");
  return kind === "error" ? scope! : null;
}

/** The label of round `k` of `kind` (`error round k/3 at level Lx (total t/backstop)`). */
function label(verify: VerifyState, kind: PatchRoundKind, scope: RoundScope | null, ahead: number): string {
  if (!scope) return `${kind} round ${roundsUsed(verify, kind) + ahead}/${MAX_REFINEMENT_ROUNDS} (${roundCounter(kind)})`;
  return `error round ${levelRounds(verify, scope.level) + ahead}/${MAX_PATCH_ROUNDS_PER_LEVEL} at level ${scope.level} (total ${roundsUsed(verify, "error") + ahead}/${scope.backstop})`;
}

/** The label of the round about to be spent (nothing is counted). */
export function nextRound(verify: VerifyState, kind: PatchRoundKind, scope?: RoundScope | null): string {
  return label(verify, kind, needScope(kind, scope), 1);
}

/** Spend one round of `kind` (an error round: on its level and on the total); returns its label.
 * An error round handed on without a scope (a stage result predating it) is charged to `global`. */
export function countRound(verify: VerifyState, kind: PatchRoundKind, scope?: RoundScope | null): string {
  const s = kind === "error" ? (scope ?? { level: GLOBAL_LEVEL, nodes: [], backstop: MIN_PATCH_BACKSTOP }) : null;
  if (s) migratePatchRounds(verify, null);
  const counter = roundCounter(kind);
  verify[counter] = (verify[counter] ?? 0) + 1;
  if (s) verify.patch_rounds_by_level = { ...(verify.patch_rounds_by_level ?? {}), [s.level]: levelRounds(verify, s.level) + 1 };
  return label(verify, kind, s, 0);
}

/** A round of `kind` is due but a cap is reached: the level's (3) or the whole-run backstop. */
export function atCap(verify: VerifyState, kind: PatchRoundKind, scope?: RoundScope | null): boolean {
  const s = needScope(kind, scope);
  if (!s) return roundsUsed(verify, kind) >= MAX_REFINEMENT_ROUNDS;
  return levelRounds(verify, s.level) >= MAX_PATCH_ROUNDS_PER_LEVEL || roundsUsed(verify, kind) >= s.backstop;
}

/** The scope of the round an error cap receipt holds back (a receipt from before 2026-09-26: `global`). */
export function capScope(cap: CapReached): RoundScope | null {
  if (cap.counter === "refinement_rounds") return null;
  return { level: cap.level ?? GLOBAL_LEVEL, nodes: cap.nodes ?? [], backstop: cap.backstop ?? cap.cap };
}

/** `--clear-patch-cap`: one more window — the capped level's counter resets (at the backstop, the
 * whole-run total; on a receipt from before the per-level caps, both). A cleared cap opens the round
 * it held back: a level cleared while the total also stands at the backstop resets the total too.
 * Returns the log line. */
export function clearCap(verify: VerifyState, cap: CapReached): string {
  if (cap.suggestions?.length) {
    const counts = { ...(verify.suggestion_rejections ?? {}) };
    for (const id of cap.suggestions) delete counts[id];
    verify.suggestion_rejections = counts;
    const line = `suggestion rejections reset for ${cap.suggestions.join(", ")}; the fixer answers again.`;
    if (cap.suggestions_only) return line;
    return `${line} ${clearCap(verify, { ...cap, suggestions: undefined })}`;
  }
  if (cap.counter === "refinement_rounds") {
    verify.refinement_rounds = 0;
    return `refinement_rounds reset (was ${cap.rounds}/${cap.cap}); one more window of ${cap.cap} round(s).`;
  }
  if (cap.level === undefined) {
    verify.patch_rounds = 0;
    verify.patch_rounds_by_level = {};
    return `patch_rounds reset (was ${cap.rounds}/${cap.cap}); a fresh window.`;
  }
  if (cap.backstop_hit) {
    verify.patch_rounds = 0;
    return `whole-run backstop reset (was ${cap.rounds}/${cap.cap}); one more whole-run window.`;
  }
  verify.patch_rounds_by_level = { ...(verify.patch_rounds_by_level ?? {}), [cap.level]: 0 };
  const total = verify.patch_rounds ?? 0;
  const atBackstop = cap.backstop !== undefined && total >= cap.backstop;
  if (atBackstop) verify.patch_rounds = 0;
  return `level ${cap.level} reset (was ${cap.rounds}/${cap.cap}); one more window of ${cap.cap} round(s) at that level${atBackstop ? ` (the whole-run total, at its backstop ${total}/${cap.backstop}, resets too)` : ""}.`;
}

/** The halt record for a round of `kind` due at its cap. */
export function capRecord(
  verify: VerifyState,
  kind: PatchRoundKind,
  origin: CapReached["origin"],
  findings: CapReached["findings"],
  patches: PatchFile | null,
  scope?: RoundScope | null,
): CapReached {
  const s = needScope(kind, scope);
  const levelHit = s ? levelRounds(verify, s.level) >= MAX_PATCH_ROUNDS_PER_LEVEL : false;
  return {
    counter: roundCounter(kind),
    rounds: !s ? roundsUsed(verify, kind) : levelHit ? levelRounds(verify, s.level) : roundsUsed(verify, kind),
    cap: !s ? MAX_REFINEMENT_ROUNDS : levelHit ? MAX_PATCH_ROUNDS_PER_LEVEL : s.backstop,
    ...(s ? { level: s.level, nodes: s.nodes, backstop: s.backstop, backstop_hit: !levelHit } : {}),
    origin,
    findings,
    proposed: (patches?.patches ?? []).map((p) => ({
      node: p.node,
      corrected_statement: p.corrected_statement,
    })),
    at: new Date().toISOString(),
  };
}

/** The halt message: what was spent, what the next round would carry, and the two ways forward. */
export function capMessage(cap: CapReached, slug: string, at: { rewind?: boolean } = {}): string {
  // What says "the finding misreads the paper" here: at a cap the approved round of a proposed
  // rewind ran into, the rewind's own answers (its nodes are items of that receipt); else per node.
  const misreads = at.rewind
    ? `    paperformalizer verify ${slug} --resume --reject-rewind "<where the paper grants it>"  (the finding is ruled out: no round is due, the F stages continue)\n` +
      `    paperformalizer verify ${slug} --resume --reject-finding "<reading>"  (the finding misreads the paper: withdrawn, the statement stands under the reading; no round is due)\n`
    : null;
  const findings = cap.findings.map((f) => `    - ${f.id} [${f.axis}] ${f.detail.replace(/\s+/g, " ").slice(0, 400)}`).join("\n");
  const proposed = cap.proposed.length
    ? cap.proposed.map((p) => `    - ${p.node}${p.corrected_statement ? " (statement corrected)" : ""}`).join("\n")
    : "    (no patch yet)";
  const rejected = cap.suggestions?.length ? `the referee rejected the suggested weakening of ${cap.suggestions.join(", ")} past its limit` : "";
  if (cap.suggestions_only) {
    const findings = cap.findings.map((f) => `    - ${f.id} [${f.axis}] ${f.detail.replace(/\s+/g, " ").slice(0, 400)}`).join("\n");
    return (
      `SUGGESTION LIMIT: ${rejected} (due at ${cap.origin}). The run halts for the orchestrator (in every mode, auto mode included).\n` +
      `  The round would carry:\n${findings || "    (none)"}\n  Continue with one of:\n` +
      `    paperformalizer verify ${slug} --resume --clear-patch-cap   (the fixer answers these nodes again)\n` +
      `    paperformalizer verify ${slug} --resume --accept-cap        (end the loop; V6 reports)\n` +
      `    paperformalizer verify ${slug} --resume --reject-finding "<node>: <reading>"  (the finding misreads the paper: it is withdrawn on that result, which stands under the reading; repeatable)\n` +
      `  (with the --toolkit / --slug / --dry-run the run was started with)`
    );
  }
  const which = cap.level === undefined
      ? `${cap.counter} is at its cap`
      : cap.backstop_hit
        ? `the whole-run backstop is reached (level ${cap.level}${cap.nodes?.length ? `: ${cap.nodes.join(", ")}` : ""})`
        : `level ${cap.level}${cap.nodes?.length ? ` (${cap.nodes.join(", ")})` : ""} is at its cap`;
  const window = cap.level === undefined
      ? `one more window of ${cap.cap} round(s); the counter resets`
      : cap.backstop_hit
        ? "one more whole-run window; the total resets"
        : `one more window of ${cap.cap} round(s) at level ${cap.level}; that level's counter resets`;
  return (
    `PATCH CAP: a ${cap.counter === "refinement_rounds" ? "refinement" : "patch"} round is due but ${which}${rejected ? `, and ${rejected}` : ""} ` +
    `(${cap.rounds}/${cap.cap}; due at ${cap.origin}). The run halts for the orchestrator (in every mode, auto mode included).\n` +
    `  The round would carry:\n${findings || "    (none)"}\n  The fixer's patch file proposes:\n${proposed}\n` +
    `  Continue with one of:\n` +
    `    paperformalizer verify ${slug} --resume --clear-patch-cap   (${window})\n` +
    `    paperformalizer verify ${slug} --resume --accept-cap        (end the loop: a refinement cap keeps the repair and goes to F1; otherwise V6 reports)\n` +
    (misreads ?? `    paperformalizer verify ${slug} --resume --reject-finding "<node>: <reading>"  (the finding misreads the paper: it is withdrawn on that result, its applied repair included; repeatable)\n`) +
    `  (with the --toolkit / --slug / --dry-run the run was started with)`
  );
}
