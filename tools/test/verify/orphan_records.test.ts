// No record is left on a node a V1 restructuring removed (live CNS run, 2026-09-26: the agent
// deleted the patched `lem:cont-elasticity` / `-deriv`, whose statements `lem:cont-alt3` / `-alt4`
// print, and V1.5 checkpointed on the orphaned patches). The records follow the node now printing
// the same statement.
import { readFile } from "node:fs/promises";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import type { PatchFileLike } from "../../src/verify/core_graph.js";
import { applyOrphanPlan, planOrphans, type OrphanCoreLike } from "../../src/verify/orphan_records.js";

const FIX = path.join(path.dirname(fileURLToPath(import.meta.url)), "fixtures", "orphan_records_cns");
const load = async <T>(f: string): Promise<T> => JSON.parse(await readFile(path.join(FIX, f), "utf8")) as T;
type Verify = { paper_errors: Record<string, unknown>; confirmed: Record<string, string>; findings: Array<{ node: string }>; v1_5_rounds_by_node?: Record<string, number> };

describe("no record left on a node a V1 restructuring removed", () => {
  it("live CNS: the patches, ledger entries of lem:cont-elasticity / -deriv move to lem:cont-alt3 / -alt4, which print the same statements", async () => {
    const before = await load<OrphanCoreLike>("transcribed.before.json");
    const after = await load<OrphanCoreLike>("transcribed.after.json");
    const rec = await load<{ patches: PatchFileLike; verify: Verify }>("records.halted.json");
    rec.verify.v1_5_rounds_by_node = { "lem:cont-elasticity": 2, "lem:cont-alt3": 1 };
    const plan = planOrphans(before, after, rec.patches, rec.verify);
    expect(plan.carriers).toEqual({ "lem:cont-elasticity": "lem:cont-alt3", "lem:cont-deriv": "lem:cont-alt4" });
    expect(plan.unresolved).toEqual([]);
    expect(plan.stale).toEqual(["lem:cont-rdd"]);
    const { file, setAside } = applyOrphanPlan(plan, rec.patches, rec.verify);
    expect(setAside).toEqual([]);
    expect(file!.patches.map((p) => p.node)).toEqual(["lem:cont-alt3", "lem:cont-alt4"]);
    expect(file!.patches[0]!.corrected_statement).toBe(rec.patches.patches[0]!.corrected_statement);
    expect(Object.keys(rec.verify.paper_errors).sort()).toEqual(["lem:cont-alt3", "lem:cont-alt4"]);
    expect(rec.verify.confirmed).toEqual({});
    // the revise cap follows the moved node: a rename does not reset it
    expect(rec.verify.v1_5_rounds_by_node).toEqual({ "lem:cont-alt3": 2 });
  });

  it("with no single carrier the records are set aside with the reason and the candidates graded afresh — never a halt", async () => {
    const before = await load<OrphanCoreLike>("transcribed.before.json");
    const after = await load<OrphanCoreLike>("transcribed.after.json");
    const rec = await load<{ patches: PatchFileLike; verify: Verify }>("records.halted.json");
    // lem:cont-alt3 already carries a repair of its own
    rec.patches.patches.push({ ...rec.patches.patches[0]!, node: "lem:cont-alt3" });
    rec.verify.confirmed["lem:cont-alt3"] = "sha";
    const plan = planOrphans(before, after, rec.patches, rec.verify);
    expect(plan.carriers).toEqual({ "lem:cont-deriv": "lem:cont-alt4" });
    expect(plan.unresolved).toEqual([{ id: "lem:cont-elasticity", reason: expect.stringMatching(/already carries a repair/), candidates: ["lem:cont-alt3"] }]);
    const { file, setAside } = applyOrphanPlan(plan, rec.patches, rec.verify);
    expect(file!.patches.map((p) => p.node)).toEqual(["lem:cont-alt4", "lem:cont-alt3"]);
    expect(setAside.map((s) => s.node)).toEqual(["lem:cont-elasticity"]);
    expect(setAside[0]!.patch).toMatchObject({ node: "lem:cont-elasticity" });
    expect(rec.verify.paper_errors).not.toHaveProperty("lem:cont-elasticity");
    expect(rec.verify.confirmed).not.toHaveProperty("lem:cont-alt3");
  });
});

describe("every name of a moved node follows it", () => {
  it("an owner reading on the node, the ids a repair lists (hypotheses, consequence_of, a block's adds), a suggestion's, and the receipts naming it", () => {
    const plan = { carriers: { "lem:old": "lem:new" }, unresolved: [], stale: [] };
    const file = {
      key_results: ["lem:old"],
      patches: [
        { node: "lem:old", corrected_statement: "c", proof_note: "p", adds: ["ass:a"], drops: ["lem:old"], corollaries: [{ statement: "s", follows: "f", adds: ["ass:a"] }] },
        { node: "thm:use", corrected_statement: "c", proof_note: "p", consequence_of: ["lem:old"], drops: ["lem:old"], supersedes: ["lem:old"] },
      ],
      unfixable: [{ node: "thm:side", reason: "r", suggested_repair: { corrected_statement: "c", proof_note: "p", adds: ["lem:old"], corollaries: [{ statement: "s", follows: "f", adds: ["lem:old"] }] } }],
      owner_readings: [{ id: "ass:pin-owner-1", node: "lem:old", reading: "r" }],
    } as unknown as PatchFileLike;
    const verify = {
      paper_errors: {},
      confirmed: {},
      findings: [],
      rejected_rewinds: [{ node: "lem:old", axis: "correctness", stage: "F2.5", route: "fix-source", detail: "d", reason: "r", by: "orchestrator", at: "t" }],
      fixer_rejections: [{ node: "lem:old" }],
      split_requests: ["lem:old", "lem:new"],
      weakening_repair: { status: "pending", items: [{ node: "lem:old" }], decisions: { "lem:old": "accepted" }, at: "t" },
      cross_stage_rewind: { status: "pending", target: "lem:old", nodes: ["lem:old"], targets: [{ node: "lem:old", users: ["lem:old", "thm:use"] }], at: "t" },
    };
    const { file: out } = applyOrphanPlan(plan, file, verify as never);
    expect(out!.patches[0]).toMatchObject({ node: "lem:new", adds: ["ass:a"], drops: ["lem:new"], corollaries: [{ adds: ["ass:a"] }] });
    expect(out!.patches[1]).toMatchObject({ node: "thm:use", consequence_of: ["lem:new"], drops: ["lem:new"], supersedes: ["lem:new"] });
    expect(out!.unfixable[0]).toMatchObject({ node: "thm:side", suggested_repair: { adds: ["lem:new"], corollaries: [{ adds: ["lem:new"] }] } });
    expect(out!.owner_readings).toEqual([{ id: "ass:pin-owner-1", node: "lem:new", reading: "r" }]);
    expect(verify.rejected_rewinds[0]!.node).toBe("lem:new");
    expect(verify.fixer_rejections[0]!.node).toBe("lem:new");
    expect(verify.split_requests).toEqual(["lem:new"]);
    expect(verify.weakening_repair).toMatchObject({ items: [{ node: "lem:new" }], decisions: { "lem:new": "accepted" } });
    expect(verify.cross_stage_rewind).toMatchObject({ target: "lem:new", nodes: ["lem:new"], targets: [{ node: "lem:new", users: ["lem:new", "thm:use"] }] });
  });
});

describe("an error set aside by a re-transcription reaches the referee", () => {
  it("each node now printing the text is shown the error to check again; a node not graded is not", async () => {
    const { mkdtemp, mkdir, writeFile, rm } = await import("node:fs/promises");
    const os = await import("node:os");
    const { priorErrorLines } = await import("../../src/verify/stage_v1_5.js");
    const { ORPHANED_RECORDS_FILE } = await import("../../src/verify/orphan_records.js");
    const dir = await mkdtemp(path.join(os.tmpdir(), "prior-errors-"));
    await mkdir(path.join(dir, "discovery"), { recursive: true });
    const record = { at: "t", node: "lem:a-alt2", reason: "several carriers", candidates: ["lem:a"], patch: null, unfixable: null, paper_error: { detail: "the rate fails for $q=1/2$", witness: "$q=1/2$" } };
    await writeFile(path.join(dir, ORPHANED_RECORDS_FILE), JSON.stringify([record]));
    expect(await priorErrorLines(dir, ["lem:a"])).toEqual([{ node: "lem:a", line: "lem:a: found on lem:a-alt2 (an earlier transcription of this result): the rate fails for $q=1/2$ Witness: $q=1/2$" }]);
    expect(await priorErrorLines(dir, ["thm:b"])).toEqual([]);
    await rm(dir, { recursive: true, force: true });
  });
});
