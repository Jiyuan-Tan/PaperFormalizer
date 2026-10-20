// Round B end to end in a dry run: one entry per main result (its helper folded in), the checklist
// read as a textbook entry with the Lean details below, decisions round-tripping through
// `propose --apply`, and a finished run entering the round on `--resume`.
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { CandidateScan, ScanDecl } from "../../src/proposals/candidate_scan.js";
import { pendingMoveSnapshot } from "../../src/proposals/apply_b.js";
import { runProposeCli } from "../../src/proposals/cli.js";
import { archiveEarlierRound, gardenListOrNull, runRoundB } from "../../src/proposals/round_b.js";
import { batchPath, checklistPath, proposalBatchSchema, proposalLedgerPath } from "../../src/proposals/schema.js";
import { createVerifyInitialState, loadState, saveState } from "../../src/state.js";
import { writeSkeleton } from "../toolkit/helpers.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});
const quiet = () => undefined;
const noCodex = (async () => { throw new Error("no model call in tests"); }) as never;
const QID = "paper_x";

async function setup() {
  const root = await mkdtemp(path.join(os.tmpdir(), "roundb-"));
  tmp.push(root);
  const cfg = await writeSkeleton(root);
  await mkdir(path.join(root, "runs", QID, "discovery"), { recursive: true });
  const st = createVerifyInitialState(QID, {
    phase: "proposals_B", source: { input: "/p.tex", main_file: "main.tex", sha256: "x" }, targets: null, core_sha256: null,
    v1_rounds: 0, v1_5_rounds: 0, findings: [], report_path: null, dry_run: true,
  }, cfg.papersLib);
  await saveState(root, QID, st);
  return { cfg, prefix: st.lean_subdir.split("/").join(".") };
}

function decl(name: string, over: Partial<ScanDecl> = {}): ScanDecl {
  return {
    name, kind: "theorem", module: `${name.split(".").slice(0, 2).join(".")}.Main`, file: "Main.lean", line: 1, end_line: 2,
    is_private: false, type: "∀ (n : ℕ), n + n = 2 * n", doc: null, axioms: ["propext"], has_sorry: false,
    type_constants: [], body_constants: [], ...over,
  };
}

describe("the gardening list is a by-product of round B", () => {
  it("a gardener that fails costs the list, not the round", async () => {
    const logged: string[] = [];
    expect(await gardenListOrNull(async () => ({ path: "/tk/doc/proposals/garden.md" }), (m) => logged.push(m))).toBe("/tk/doc/proposals/garden.md");
    expect(await gardenListOrNull(async () => null, (m) => logged.push(m))).toBeNull();
    expect(await gardenListOrNull(async () => { throw new Error("gardener broke the output contract twice"); }, (m) => logged.push(m))).toBeNull();
    expect(logged).toEqual(["gardening list: not written — gardener broke the output contract twice"]);
  });
});

describe("round B", () => {
  it("proposes one entry per main result — the helper moves with it — written as a textbook entry", async () => {
    const { cfg, prefix } = await setup();
    const helper = decl(`${prefix}.sum_helper`);
    const main = decl(`${prefix}.double_is_mul`, { body_constants: [{ name: helper.name, class: "paper", module: helper.module }] });
    const scan: CandidateScan = { schema: 1, paper: prefix, toolkit_prefix: "Toolkit", papers_prefix: "Papers", modules: [], declarations: [helper, main] };
    const rec = await runRoundB({ toolkit: cfg, qid: QID, dryRun: true, runCodex: noCodex, log: quiet, scan: async () => scan, graph: async () => null });
    expect(rec.status).toBe("pending_user");
    const batch = proposalBatchSchema.parse(JSON.parse(await readFile(batchPath(cfg, QID), "utf8")));
    const entry = batch.proposals.find((p) => p.source.ref === main.name)!;
    const folded = batch.proposals.find((p) => p.source.ref === helper.name)!;
    expect(entry).toMatchObject({ verdict: "propose", moves_with: [helper.name] });
    expect(folded).toMatchObject({ verdict: "skip", part_of: entry.id });

    const text = await readFile(checklistPath(cfg, QID, true), "utf8");
    expect(text).toContain(`## ${entry.id} · ${entry.title}`);
    expect(text.indexOf("**Reference.**")).toBeLessThan(text.indexOf("<details><summary>Lean details</summary>"));
    expect(text).toMatch(/\*\*In your other papers\.\*\* first time/);
    expect(text).toContain(`Moves with it (the helper lemmas proving it and the definitions it needs): \`${helper.name}\``);
    expect(text).not.toContain(`## ${folded.id} ·`);

    // The owner's decision comes back through `propose --apply` (dry run: recorded, nothing moved).
    await writeFile(checklistPath(cfg, QID, true), text.replace("decision: pending", "decision: accept\nnote: standard identity"));
    const state = await loadState(cfg.toolkitRoot, QID);
    state.verify!.promotion = rec;
    await saveState(cfg.toolkitRoot, QID, state);
    const resumed: string[][] = [];
    await runProposeCli([QID, "--apply", "--dry-run", "--toolkit", cfg.toolkitRoot], { log: quiet, resumeVerify: async (a) => { resumed.push(a); } });
    const ledger = JSON.parse(await readFile(proposalLedgerPath(cfg, QID, true), "utf8")) as { decisions: Array<{ proposal_id: string; decision: { kind: string; note?: string } }> };
    expect(ledger.decisions.map((d) => [d.proposal_id, d.decision.kind])).toEqual([[entry.id, "accept"]]);
    expect((await loadState(cfg.toolkitRoot, QID)).verify!.promotion).toMatchObject({ status: "applied" });
    expect(resumed[0]).toContain("--resume");
    // applying it again is refused — and is no failed apply of the round: no failure is left for the page
    const live = await loadState(cfg.toolkitRoot, QID);
    delete live.verify!.dry_run;
    await saveState(cfg.toolkitRoot, QID, live);
    await expect(runProposeCli([QID, "--apply", "--round", "B", "--toolkit", cfg.toolkitRoot], { log: quiet })).rejects.toThrow(/already applied/);
    expect(existsSync(path.join(cfg.runsDir, QID, "proposals", "apply_failed.json"))).toBe(false);
  });

  it("a batch written for a round applied before a rewind sets that round's files aside, and keeps only its own recommendations", async () => {
    const { cfg } = await setup();
    const dir = path.join(cfg.runsDir, QID, "proposals");
    await mkdir(dir, { recursive: true });
    const old = ["B.json", "B.decisions.json", "B.moves.json", "move_b-old.log", "statements_before_b-old.json", "statements_after_b-old.json"];
    for (const f of old) await writeFile(path.join(dir, f), "{}");
    await writeFile(path.join(dir, "A.decisions.json"), "{}");
    // a move the toolkit is half-way through: its record, journal, snapshot and log are not this round's to archive
    const kept = ["move_pending.json", "move_journal.json", "move_b-kept.log", "statements_before_b-kept.json"];
    await writeFile(path.join(dir, "move_pending.json"), JSON.stringify({ proposal_id: "b-kept", statements_before: path.join(dir, "statements_before_b-kept.json") }));
    for (const f of kept.slice(1)) await writeFile(path.join(dir, f), JSON.stringify({ declarations: [{ name: "Papers.X.t", stmt_hash: "h" }] }));
    const batch = { slug: QID, round: "B" as const, created: "2026-10-07T12:00:00.000Z", proposals: [{ id: "b-new", content: "c" }, { id: "b-same", content: "restated" }] } as never;
    const { recommendationKeys } = await import("../../src/proposals/checklist.js");
    const of = recommendationKeys(batch).get("b-new");
    // b-same: an entry of the same id whose statement the new batch states differently — not its recommendation
    await writeFile(path.join(dir, "B.recommendations.json"), JSON.stringify({ "b-old": { kind: "accept", why: "w" }, "b-new": { kind: "defer", why: "v", of }, "b-same": { kind: "accept", why: "u", of: "0000000000000000" } }));
    const moved = await archiveEarlierRound(cfg, QID, batch);
    const to = path.join(dir, "voided", "2026-10-07T12-00-00-000Z");
    expect(moved).toEqual([...[...old].sort(), "B.recommendations.json (2 entries)"]);
    for (const f of old) {
      expect(existsSync(path.join(dir, f))).toBe(false);
      expect(existsSync(path.join(to, f))).toBe(true);
    }
    expect(JSON.parse(await readFile(path.join(dir, "B.recommendations.json"), "utf8"))).toEqual({ "b-new": { kind: "defer", why: "v", of } });
    expect(JSON.parse(await readFile(path.join(to, "B.recommendations.json"), "utf8"))).toEqual({ "b-old": { kind: "accept", why: "w" }, "b-same": { kind: "accept", why: "u", of: "0000000000000000" } });
    // the other round's files and a move still half-way stay
    expect(existsSync(path.join(dir, "A.decisions.json"))).toBe(true);
    for (const f of kept) expect(existsSync(path.join(dir, f))).toBe(true);
    // … and the pending move finds its snapshot; one whose snapshot is gone is refused, not gated without it
    const pend = JSON.parse(await readFile(path.join(dir, "move_pending.json"), "utf8"));
    const where = { pendingFile: path.join(dir, "move_pending.json"), journal: path.join(dir, "move_journal.json"), voided: path.join(dir, "voided") };
    expect(pendingMoveSnapshot(pend, where)).toBeInstanceOf(Map);
    expect(pendingMoveSnapshot({ ...pend, statements_before: null }, where)).toBeNull();
    await rm(path.join(dir, "statements_before_b-kept.json"));
    expect(() => pendingMoveSnapshot(pend, where)).toThrow(/statement snapshot taken before it is missing[\s\S]*cannot check that no statement changed/);
    await writeFile(path.join(dir, "statements_before_b-kept.json"), "{}");
    expect(() => pendingMoveSnapshot(pend, where)).toThrow(/holds no statement hashes/);
    expect(await archiveEarlierRound(cfg, QID, batch)).toEqual([]);
  });

  it("an apply refused before anything is read leaves no apply pid, and leaves why for the page and the watcher", async () => {
    const { cfg } = await setup();
    const dir = path.join(cfg.runsDir, QID, "proposals");
    await mkdir(dir, { recursive: true });
    await writeFile(path.join(dir, "apply_B.pid"), "12345\n"); // as the page writes it when it launches the apply
    // (a live apply on a dry-run state: refused at the first check)
    await expect(runProposeCli([QID, "--apply", "--round", "B", "--toolkit", cfg.toolkitRoot], { log: quiet, now: () => new Date("2026-10-07T12:00:00Z") })).rejects.toThrow(/dry/i);
    expect(existsSync(path.join(dir, "apply_B.pid"))).toBe(false);
    const failed = JSON.parse(await readFile(path.join(dir, "apply_failed.json"), "utf8"));
    expect(failed).toMatchObject({ round: "B", at: "2026-10-07T12:00:00.000Z", message: expect.stringMatching(/dry/i) });
  });
});
