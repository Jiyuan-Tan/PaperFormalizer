/**
 * `state.verify.findings` — the durable channel the V6 report reads.
 *
 * A run formalizes a USER'S paper: its mathematics is never re-derived.
 * The F stages RECORD what the reviewer found here and halt at an operator
 * checkpoint; V6 turns these entries into the per-result buckets (`refuted` / `unresolved` /
 * `note`).
 *
 * Recording is idempotent: the same `(node, stage, kind, detail)` observation made again by a
 * `--resume` that re-enters the same stage does not duplicate the report row. Findings are
 * otherwise append-only, with ONE exception: `clearFormalizationUnresolved` (below) retracts the
 * F-stage `unresolved` entries once the proof loop actually closes.
 */
import type { StateJson } from "../types.js";
import type { PaperError, VerifyFinding } from "./types.js";

/**
 * How an entry of the paper-error ledger left WITHOUT a confirmed repair is recorded. `refuted` is a
 * witness against the printed statement; a clarification that was not written, and a statement the
 * paper leaves undetermined (an unresolvable ambiguity: nothing was shown false), are `unresolved`.
 */
export function openFindingKind(e: Pick<PaperError, "kind" | "undetermined"> | undefined): Pick<VerifyFinding, "kind" | "undetermined"> {
  if (e?.kind === "clarification") return { kind: "unresolved" };
  return e?.undetermined ? { kind: "unresolved", undetermined: true } : { kind: "refuted" };
}

/**
 * Append `f` to `state.verify.findings` with the current timestamp, unless an entry with the
 * same `(node, stage, kind, detail)` is already there. Throws when `state.verify` is missing:
 * the run was not seeded by the verify runner, and silently dropping the finding would hide it
 * from the report.
 */
export function recordVerifyFinding(state: StateJson, f: Omit<VerifyFinding, "at">): void {
  const verify = state.verify;
  if (!verify) {
    throw new Error("state.verify is missing; the run was not seeded by the verify runner");
  }
  if (!Array.isArray(verify.findings)) verify.findings = [];
  const duplicate = verify.findings.some(
    (prior) =>
      prior.node === f.node && prior.stage === f.stage && prior.kind === f.kind && prior.detail === f.detail,
  );
  if (duplicate) return;
  verify.findings.push({ ...f, at: new Date().toISOString() });
}

/**
 * Drop every `unresolved` finding an F stage recorded. Called when the proof-review loop
 * COMPLETES: the loop completes only with every node closed, so an earlier escalation
 * (a transient F2.5 `unclear`, a `fix-source` the operator then fixed) no longer describes
 * the run, and leaving it in would pin the result to `unresolved` in the report forever.
 *
 * Deliberately narrow: `refuted` (a positive witness of an error — a fact about the paper that
 * closing the loop does not undo) and `note` (disclosure) survive, and so does anything V1.5
 * recorded, whose `stage` is not an `F` stage.
 */
export function clearFormalizationUnresolved(state: StateJson): number {
  const verify = state.verify;
  if (!verify || !Array.isArray(verify.findings)) return 0;
  const before = verify.findings.length;
  let demoted = 0;
  verify.findings = verify.findings.flatMap((f) => {
    if (!(f.kind === "unresolved" && f.stage.startsWith("F"))) return [f];
    // A WITNESSED unresolved finding (e.g. contradictory hypotheses, under which the Lean
    // theorem closes vacuously) is a fact about the paper that closing the loop does not
    // undo: keep it as a disclosure `note` instead of erasing it.
    if (f.witness !== null && f.witness !== undefined) {
      demoted += 1;
      return [{ ...f, kind: "note" as const }];
    }
    return [];
  });
  return before - verify.findings.length + demoted;
}

