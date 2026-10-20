import { describe, it, expect } from "vitest";
import {
  gradeReviewerOutput,
  mergeOutputs,
  normalizeReviewerObjId,
  resolveVerdictIds,
} from "../../src/formalization/proof_reviewer.js";

// A node legitimately has TWO names: its graph `id` (`lem:admissible-swaps-preserve-direction`)
// and its `obj_id` (`L-1`). `nodeIdToObjId` only rewrites short ids like `l1`→`L-1`, so a
// descriptive id passes through unchanged into `expectedObjIds` — while the reviewer may answer
// under EITHER name. Keying `seen` on the returned name and checking it against the expected name
// therefore DROPS a real `matched` and synthesizes `drift / "missing reviewer verdict"` over it.
// That is a coin-flip blocker: the same review passes or fails on which alias the model happened
// to use.
const CANON = "lem:admissible-swaps-preserve-direction";
const ALIASES = new Map<string, string>([
  [CANON, CANON],
  ["L-1", CANON],
]);

describe("reviewer verdict grading resolves node id ↔ obj_id aliases", () => {
  it.each([
    // a `matched` under the obj_id alias is NOT dropped and NOT overwritten by a synthetic drift
    { label: "a `matched` under the obj_id alias passes once", verdicts: [{ obj_id: "L-1", verdict: "matched", note: "faithful" }], blocking: [], verdict: "equivalent" },
    // the fix must not launder a failure
    { label: "a `drift` under the alias still blocks", verdicts: [{ obj_id: "L-1", verdict: "drift", note: "statement weakened" }], blocking: [CANON], verdict: "drift" },
    // silence must never read as a pass
    { label: "a reviewer DROPOUT blocks as a missing verdict", verdicts: [], blocking: [CANON], verdict: "drift" },
  ])("$label", ({ verdicts, blocking, verdict }) => {
    const out = { status: "ok", statement_verdicts: verdicts, assumption_verdicts: [], substrate_gates: [], escalate: null };
    const graded = gradeReviewerOutput(out as never, [CANON], ALIASES);
    expect(graded.blocking).toEqual(blocking);
    expect(graded.rows).toHaveLength(1);
    expect(graded.rows[0]).toMatchObject({ obj_id: CANON, verdict });
    if (verdicts.length === 0) expect(graded.rows[0].note).toBe("missing reviewer verdict");
  });

  it("deduplicates conflicting aliases negative-first", () => {
    const out = {
      status: "flagged",
      statement_verdicts: [
        { obj_id: CANON, verdict: "matched", note: "peer A" },
        { obj_id: "L-1", verdict: "drift", note: "peer B" },
      ],
      assumption_verdicts: [], substrate_gates: [], escalate: null,
    };
    const graded = gradeReviewerOutput(out as never, [CANON], ALIASES);
    expect(graded.rows).toHaveLength(1);
    expect(graded.blocking).toEqual([CANON]);
    expect(graded.rows[0].verdict).toBe("drift");
  });
});

describe("reviewer object-id normalization preserves TeX symbol ids", () => {
  const HEAVY_LIGHT = "sym:\\(\\widehat{\\mathcal H}_n,\\widehat{\\mathcal L}_n\\)";
  const RISK = "sym:\\(\\mathsf R_{n,d,\\epsilon}\\)";

  it.each([
    {
      label: "a keyed-object id with spaces and commas",
      expected: HEAVY_LIGHT,
      out: { status: "ok", statement_verdicts: { [HEAVY_LIGHT]: { verdict: "untagged", note: "tag heavyCells" } }, assumption_verdicts: {}, substrate_gates: [], escalate: null },
      blocking: [] as string[],
    },
    {
      label: "a bare-string verdict",
      expected: RISK,
      out: { status: "ok", statement_verdicts: [`${RISK}: matched — exact risk definition`], assumption_verdicts: [], substrate_gates: [], escalate: null },
      blocking: [] as string[],
    },
    {
      label: "a truncated pseudo-id, which is never forwarded to F2",
      expected: HEAVY_LIGHT,
      out: {
        status: "flagged",
        statement_verdicts: [{ obj_id: "sym:\\(\\widehat{\\mathcal", verdict: "drift", note: "missing" }],
        assumption_verdicts: [], substrate_gates: [],
        escalate: { kind: "scaffold-mismatch", obj_id: "sym:\\(\\widehat{\\mathcal", reason: "missing" },
      },
      blocking: [HEAVY_LIGHT],
    },
  ])("grades $label under the full expected TeX id", ({ expected, out, blocking }) => {
    expect(normalizeReviewerObjId(expected)).toBe(expected);
    expect(normalizeReviewerObjId(`${expected} realized by heavyCells`, [expected])).toBe(expected);
    const graded = gradeReviewerOutput(out as never, [expected]);
    expect(graded.blocking).toEqual(blocking);
    expect(graded.rows.map((row) => row.obj_id)).toEqual([expected]);
    expect(graded.escalate?.obj_id).toBeUndefined();
  });
});

// REGRESSION (2026-07-21 audit): `mergeOutputs` is a plain reducer with NO expected-id list, so a
// prose-STRING verdict ("def:rate-bound: matched — …" — a documented live model-output shape) that
// reaches it unresolved is shredded to `{verdict: <whole string>}` with no obj_id, irreversibly.
// `resolveVerdictIds` must run at the PARSE boundary, before any merge. Typed-core ids
// (`def:`/`thm:`) and `sym:` ids are the affected classes.
describe("prose-string verdicts survive the merge boundary (resolveVerdictIds)", () => {
  it.each([
    ["def:rate-bound", "def:rate-bound: matched — the Lean def is faithful"],
    ["sym:e_P", "sym:e_P: matched — cluster pins (0,1)"],
  ])("a %s prose verdict keeps its obj_id through mergeOutputs + grading", (id, verdict) => {
    const resolved = resolveVerdictIds({ status: "ok", statement_verdicts: [verdict] } as never, [id]);
    const merged = mergeOutputs(resolved, { status: "ok" } as never);
    const graded = gradeReviewerOutput(merged, [id]);
    expect(graded.blocking).toEqual([]);
    expect(graded.rows[0]).toMatchObject({ obj_id: id, verdict: "equivalent" });
  });
});
