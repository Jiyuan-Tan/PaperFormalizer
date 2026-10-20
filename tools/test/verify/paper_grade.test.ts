import { describe, expect, it } from "vitest";
import { paperGrade, renderGrade, type ReportRow } from "../../src/verify/report.js";
import type { V15Review, VerifyFinding } from "../../src/verify/types.js";

const row = (o: Partial<ReportRow>): ReportRow =>
  ({ node_id: "n", bucket: "verified", change: null, findings: [], bookkeeping: [], inherits_refutation_from: [], ...o }) as ReportRow;
const refuted = (node: string, confirmed: boolean): VerifyFinding =>
  ({ kind: "refuted", node, detail: "x", ...(confirmed ? { patch: { confirmed: true } } : {}) }) as unknown as VerifyFinding;
const mains = new Set(["thm:main"]);

describe("the paper's grade", () => {
  it("error-free when nothing was found", () => {
    expect(paperGrade([row({ node_id: "thm:main" }), row({ node_id: "lem:a" })], [], null, mains, null).grade).toBe("error_free");
  });

  it("minor: an error repaired without weakening, a lemma narrowed, a pinned reading, a bookkeeping condition", () => {
    const g = paperGrade(
      [
        row({ node_id: "thm:main", findings: [refuted("thm:main", true)], bucket: "repaired" }),
        row({ node_id: "lem:b", bookkeeping: [{ id: "ass:bk-1", condition: "c", reason: "r" }] }),
      ],
      [],
      { nodes: [{ id: "lem:c", ambiguity: "pinned" }] } as unknown as V15Review,
      mains,
      { key_results: [], patches: [{ node: "lem:a", accepted_weakening: true, given_up: "the case p = 1" }] },
    );
    expect(g.grade).toBe("minor");
    expect(g.minor.map((x) => `${x.node}: ${x.what}`)).toEqual([
      "lem:a: weakened: the case p = 1",
      "thm:main: error repaired",
      "lem:b: condition added (bookkeeping or a pinned reading)",
      "lem:c: ambiguous; a reading was pinned",
    ]);
  });

  it("major: a main result weakened, left refuted, or resting on a refuted result; a refuted side result alone is minor", () => {
    const weakened = paperGrade([row({ node_id: "thm:main" })], [], null, mains, { key_results: [], patches: [{ node: "thm:main", accepted_weakening: true, given_up: "the rate" }] });
    expect(weakened).toMatchObject({ grade: "major", major: [{ node: "thm:main", what: "weakened: the rate" }] });
    // weakened only in constants or corner cases, the referee finding the contribution kept: minor
    const kept = paperGrade([row({ node_id: "thm:main" })], [], { nodes: [], patch_review: { key_results_ok: true, detail: "kept" } } as unknown as V15Review, mains, { key_results: [], patches: [{ node: "thm:main", accepted_weakening: true, given_up: "a constant for small alpha" }] });
    expect(kept).toMatchObject({ grade: "minor", major: [], minor: [{ node: "thm:main", what: "weakened: a constant for small alpha (the referee found the key results and the contribution kept)" }] });
    const lost = paperGrade([row({ node_id: "thm:main" })], [], { nodes: [], patch_review: { key_results_ok: false, detail: "lost" } } as unknown as V15Review, mains, { key_results: [], patches: [{ node: "thm:main", accepted_weakening: true, given_up: "the rate" }] });
    expect(lost.grade).toBe("major");
    expect(paperGrade([row({ node_id: "thm:main", bucket: "refuted", findings: [refuted("thm:main", false)] })], [], null, mains, null).grade).toBe("major");
    // a main result with no finding of its own, resting on a lemma still false
    const rests = (id: string) => (id === "thm:main" ? ["thm:main", "lem:z"] : [id]);
    const onFalse = paperGrade([row({ node_id: "lem:z", bucket: "refuted", findings: [refuted("lem:z", false)] }), row({ node_id: "thm:main" })], [], null, mains, null, rests);
    expect(onFalse.major).toEqual([{ node: "thm:main", what: "rests on a result false as printed (lem:z)" }]);
    // ... but a repaired main result over a repaired lemma is minor: the error spread and both were repaired
    const both = paperGrade(
      [row({ node_id: "lem:z", bucket: "repaired", findings: [refuted("lem:z", true)], inherits_refutation_from: [] }), row({ node_id: "thm:main", bucket: "repaired", findings: [refuted("thm:main", true)], inherits_refutation_from: ["lem:z"] })],
      [], null, mains, null, rests,
    );
    expect(both.grade).toBe("minor");
    // a block split off a main result counts as main
    expect(paperGrade([row({ node_id: "thm:main-fix-1", split_from: "thm:main", bucket: "refuted", findings: [refuted("thm:main-fix-1", false)] })], [], null, mains, null).grade).toBe("major");
    const side = paperGrade([row({ node_id: "lem:z", bucket: "refuted", findings: [refuted("lem:z", false)] }), row({ node_id: "thm:main" })], [], null, mains, null);
    expect(side).toMatchObject({ grade: "minor", minor: [{ node: "lem:z", what: "false as printed, no repair holds" }] });
    // a key result the fixer names counts as main, whatever its kind
    expect(paperGrade([row({ node_id: "lem:key", bucket: "refuted", findings: [refuted("lem:key", false)] })], [], null, new Set(["lem:key"]), null).grade).toBe("major");
    // a refutation the run could not place on a result: major unrepaired, minor repaired
    expect(paperGrade([], [refuted("run", false)], null, mains, null).grade).toBe("major");
    expect(paperGrade([], [refuted("def:x", true)], null, mains, null)).toMatchObject({ grade: "minor", minor: [{ node: "def:x", what: "error repaired" }] });
    // an ambiguity the owner settled is minor
    expect(paperGrade([], [], null, mains, { key_results: [], patches: [], owner_readings: [{ node: "def:y" }] })).toMatchObject({ grade: "minor", minor: [{ node: "def:y", what: "ambiguous; the owner settled a reading" }] });
  });

  it("is printed under the verdict, each reason by the result's name", () => {
    const md = renderGrade({
      paper_grade: { grade: "major", major: [{ node: "thm:main", what: "weakened: the rate" }], minor: [{ node: "lem:a", what: "error repaired" }, { node: "lem:a", what: "condition added (bookkeeping or a pinned reading)" }] },
      names: { "thm:main": "Theorem 2" },
    }).join("\n");
    expect(md).toContain("**Paper: MAJOR ERRORS — a main result or the contribution is affected**");
    expect(md).toContain("- Theorem 2: weakened: the rate");
    expect(md).toContain("- `lem:a`: error repaired; condition added (bookkeeping or a pinned reading)");
  });
});
