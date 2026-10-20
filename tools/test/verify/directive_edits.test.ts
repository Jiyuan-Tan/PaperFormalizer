import { describe, expect, it } from "vitest";
import { DriftFixSchema, applyDriftFixes, assertFixKeepsRefCoreValid, hasDriftFix, newRefCoreViolations, refCoreViolations } from "../../src/verify/directive_edits.js";

const refs = () => ({
  qid: "verify_t",
  statements: [
    { id: "thm:a", kind: "theorem", env: "thm:a", depends_on: ["ass:x", "lem:b"], hypotheses: ["ass:x"] },
    { id: "lem:b", kind: "lemma", env: "lem:b", depends_on: [] },
    { id: "thm:c", kind: "theorem", env: "thm:c", depends_on: ["thm:a"] },
  ],
  assumptions: [
    { id: "ass:x", source: { env: "ass:x" } },
    { id: "ass:y", source: { env: "ass:y" } },
    { id: "ass:z", source: { prose: true, slice: { from: "Let", to: "hold." } } },
  ],
  definitions: [{ id: "def:d", name: "d", source: { prose: true, slice: { from: "Define", to: "fold." } } }],
});

describe("the strict reply schema and the zod schema agree on an empty string", () => {
  it("an empty prose edit is no edit (the wire types it string | null and cannot say non-empty)", () => {
    expect(DriftFixSchema.parse({ extend_to: "", setting: "  " })).toMatchObject({ extend_to: null, setting: null });
    expect(DriftFixSchema.parse({ extend_to: "hold.", setting: null })).toMatchObject({ extend_to: "hold.", setting: null });
    expect(hasDriftFix(DriftFixSchema.parse({ extend_to: "", setting: "" }))).toBe(false);
  });
  it("a TeX field zod refuses empty is refused empty on the wire too", async () => {
    const { TEX_STRING_NONEMPTY, TEX_STRING } = await import("../../src/verify/owner_text.js");
    const re = new RegExp(TEX_STRING_NONEMPTY.pattern as string);
    expect(re.test("")).toBe(false);
    expect(re.test("$n > 1$")).toBe(true);
    expect(new RegExp(TEX_STRING.pattern as string).test("")).toBe(true);
    const { NodeVerdictSchema } = await import("../../src/verify/v1_5_schema.js");
    const base = { id: "thm:a", faithfulness: "ok", ambiguity: "ok", correctness: "bookkeeping", detail: "", witness: null, reading: null };
    expect(NodeVerdictSchema.safeParse({ ...base, bookkeeping_assumption: { condition: "", reason: "r" } }).success).toBe(false);
  });
});

describe("applyDriftFixes", () => {
  it("adds and removes dependencies, keeping hypotheses in step", () => {
    const out = applyDriftFixes(refs(), [{ id: "thm:a", fix: DriftFixSchema.parse({ add_depends_on: ["ass:y", "def:d"], remove_depends_on: ["ass:x"] }) }]);
    expect(out.applied).toEqual(["thm:a"]);
    const a = out.refs.statements.find((s) => s.id === "thm:a")!;
    expect(a.depends_on).toEqual(["lem:b", "ass:y", "def:d"]);
    expect(a.hypotheses).toEqual(["ass:y"]);
  });

  it("extends a slice, adds a stated premise and wires it, and rejects unknown targets", () => {
    const out = applyDriftFixes(refs(), [
      { id: "def:d", fix: DriftFixSchema.parse({ extend_to: "of the $k$-th fold." }) },
      { id: "thm:c", fix: DriftFixSchema.parse({ new_assumption: { id: "ass:iid", env: null, from: "Let the sample be", to: "i.i.d.", wire_into: ["thm:c", "lem:b"] } }) },
      { id: "thm:a", fix: DriftFixSchema.parse({ add_depends_on: ["ass:nope"] }) },
      { id: "ass:x", fix: DriftFixSchema.parse({ extend_to: "anything" }) },
    ]);
    expect(out.applied).toEqual(["def:d", "thm:c"]);
    expect(out.rejected.map((r) => r.id)).toEqual(["thm:a", "ass:x"]);
    expect(out.rejected[1]!.reason).toMatch(/no anchor slice to extend/);
    expect(out.refs.definitions[0]!.source!.slice!.to).toBe("of the $k$-th fold.");
    expect(out.refs.assumptions.map((a) => a.id)).toContain("ass:iid");
    expect(out.refs.statements.find((s) => s.id === "lem:b")!.hypotheses).toEqual(["ass:iid"]);
  });

  it("a fix with every field null carries no edit (the finding goes to the agent)", () => {
    const none = DriftFixSchema.parse({ add_depends_on: null, extend_to: null });
    expect(hasDriftFix(none)).toBe(false);
    const out = applyDriftFixes(refs(), [{ id: "thm:a", fix: none }]);
    expect(out.rejected[0]!.reason).toMatch(/carries no edit/);
    expect(out.refs).toEqual(refs());
  });
});

describe("applyDriftFixes — a new premise's environment", () => {
  it("named by the id of the node it holds, it is that node's environment", () => {
    const r = refs();
    r.statements[1]!.env = "lemma:b";
    const out = applyDriftFixes(r, [{ id: "lem:b", fix: DriftFixSchema.parse({ new_assumption: { id: "ass:order", env: "lem:b", from: "Let", to: "kernel.", wire_into: ["lem:b"] } }) }]);
    expect(out.applied).toEqual(["lem:b"]);
    expect(out.refs.assumptions.find((a) => a.id === "ass:order")!.source).toEqual({ env: "lemma:b", slice: { from: "Let", to: "kernel." } });
  });
});

describe("applyDriftFixes — a dependency fix on an assumption", () => {
  it("lands on each statement using it (only a statement has dependencies); on an unused one it is rejected", () => {
    const out = applyDriftFixes(refs(), [
      { id: "ass:x", fix: DriftFixSchema.parse({ add_depends_on: ["ass:y"] }) },
      { id: "ass:z", fix: DriftFixSchema.parse({ add_depends_on: ["ass:y"] }) },
    ]);
    expect(out.applied).toEqual(["ass:x"]);
    const a = out.refs.statements.find((s) => s.id === "thm:a")!;
    expect(a.depends_on).toContain("ass:y");
    expect(a.hypotheses).toContain("ass:y");
    expect(out.rejected).toEqual([{ id: "ass:z", reason: expect.stringMatching(/no statement uses it/) }]);
    // a fix on a hypothesis naming a RESULT is ambiguous in direction: the transcriber's
    const named = applyDriftFixes(refs(), [{ id: "ass:x", fix: DriftFixSchema.parse({ add_depends_on: ["lem:b"] }) }]);
    expect(named.rejected).toEqual([{ id: "ass:x", reason: expect.stringMatching(/names results \(lem:b\)/) }]);
  });

  it("adds no printed hypothesis where the node is not one, removes nothing, and notes a fix every user already satisfies", () => {
    const r = refs();
    r.statements[2]!.depends_on.push("ass:y"); // thm:c uses ass:y, not as a printed hypothesis
    const out = applyDriftFixes(r, [
      { id: "ass:y", fix: DriftFixSchema.parse({ add_depends_on: ["ass:x"] }) },
      { id: "ass:x", fix: DriftFixSchema.parse({ remove_depends_on: ["lem:b"] }) },
    ]);
    const c = out.refs.statements.find((s) => s.id === "thm:c")!;
    expect(c.depends_on).toContain("ass:x");
    expect(c.hypotheses ?? []).not.toContain("ass:x");
    expect(out.rejected).toEqual([{ id: "ass:x", reason: expect.stringMatching(/no dependencies to remove/) }]);
    // thm:a, the one statement using ass:x, already depends on ass:y: no edit, so the finding goes on to the agent with why
    const r2 = refs();
    r2.statements[0]!.depends_on.push("ass:y");
    const again = applyDriftFixes(r2, [{ id: "ass:x", fix: DriftFixSchema.parse({ add_depends_on: ["ass:y"] }) }]);
    expect(again.applied).toEqual([]);
    expect(again.rejected).toEqual([{ id: "ass:x", reason: expect.stringMatching(/every statement using ass:x \(thm:a\) already depends on ass:y — nothing to add/) }]);
    // re-applied after an agent round, the same fix already in place is kept, not failed
    expect(applyDriftFixes(r2, [{ id: "ass:x", fix: DriftFixSchema.parse({ add_depends_on: ["ass:y"] }) }], { reapply: true }).applied).toEqual(["ass:x"]);
  });
});

describe("applyDriftFixes — the results using an assumption or definition", () => {
  it("wires it into the named results and out of others; on a statement, or naming no statement, it is rejected", () => {
    const out = applyDriftFixes(refs(), [
      { id: "ass:x", fix: DriftFixSchema.parse({ wire_into: ["lem:b"], unwire_from: ["thm:a"] }) },
      { id: "def:d", fix: DriftFixSchema.parse({ wire_into: ["thm:c"] }) },
      { id: "thm:a", fix: DriftFixSchema.parse({ wire_into: ["thm:c"] }) },
      { id: "ass:y", fix: DriftFixSchema.parse({ unwire_from: ["ass:z"] }) },
    ]);
    expect(out.applied).toEqual(["ass:x", "def:d"]);
    expect(out.rejected.map((r) => r.id)).toEqual(["thm:a", "ass:y"]);
    const st = (id: string) => out.refs.statements.find((s) => s.id === id)!;
    expect(st("lem:b")).toMatchObject({ depends_on: ["ass:x"], hypotheses: ["ass:x"] });
    expect(st("thm:a")).toMatchObject({ depends_on: ["lem:b"], hypotheses: [] });
    expect(st("thm:c").depends_on).toEqual(["thm:a", "def:d"]);
    expect(st("thm:c").hypotheses ?? []).toEqual([]);
  });
});

describe("applyDriftFixes — reapply", () => {
  it("re-applying fixes the agent dropped is idempotent: nodes already present are accepted, missing wiring is restored", () => {
    const fixes = [{ id: "thm:c", fix: DriftFixSchema.parse({ new_assumption: { id: "ass:iid", env: null, from: "Let", to: "i.i.d.", wire_into: ["thm:c"] } }) }];
    const first = applyDriftFixes(refs(), fixes);
    expect(first.applied).toEqual(["thm:c"]);
    // the agent kept the node but dropped the wiring
    const dropped = structuredClone(first.refs);
    dropped.statements.find((s) => s.id === "thm:c")!.depends_on = ["thm:a"];
    const again = applyDriftFixes(dropped, fixes, { reapply: true });
    expect(again.applied).toEqual(["thm:c"]);
    expect(again.refs.statements.find((s) => s.id === "thm:c")!.depends_on).toEqual(["thm:a", "ass:iid"]);
    expect(again.refs.assumptions.filter((a) => a.id === "ass:iid")).toHaveLength(1);
    // the same new_assumption re-issued by the referee in a later directive is applied, not rejected
    const reissued = applyDriftFixes(dropped, [fixes[0]!]);
    expect(reissued.applied).toEqual(["thm:c"]);
  });
});

describe("the reference-core invariant at the fix site", () => {
  it("refuses an edit that leaves dangling wiring; a violation already on file is not the fix's", () => {
    const dangling = refs();
    dangling.statements[2]!.depends_on = ["thm:a", "lem:ghost"];
    expect(() => assertFixKeepsRefCoreValid(refs(), dangling, "V1 revise round 3")).toThrow(
      /V1 revise round 3: a runner-applied referee fix would write an invalid reference core — not written:[\s\S]*thm:c: depends_on names no node: lem:ghost/,
    );
    expect(newRefCoreViolations(refs(), dangling)).toEqual(["thm:c: depends_on names no node: lem:ghost"]);
    const dup = refs();
    dup.statements.push({ ...dup.statements[1]! });
    expect(refCoreViolations(dup)).toContain("duplicate node id lem:b (2 records)");
    const out = applyDriftFixes(dup, [{ id: "thm:a", fix: DriftFixSchema.parse({ add_depends_on: ["ass:y"] }) }]);
    expect(out.applied).toEqual(["thm:a"]);
    expect(() => assertFixKeepsRefCoreValid(dup, out.refs, "x")).not.toThrow();
  });
});
