// What keeps promotion structured: the topic tree (curator contract, lint, owner-decided new topics),
// the Foundations/Tricks signal, hypotheses a proof never uses, recurrence by pattern, the compact
// curator input, and `--reopen-deferred`.
import { mkdir, mkdtemp, readdir, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { CandidateScan, ScanDecl } from "../../src/proposals/candidate_scan.js";
import { roundBDecisionProblems } from "../../src/proposals/apply_b.js";
import { newTopics, parseChecklist, renderChecklist, topicKey } from "../../src/proposals/checklist.js";
import { runProposeCli } from "../../src/proposals/cli.js";
import { curatorViolations, promptCandidates, type CuratorItem, type GroundedCandidate } from "../../src/proposals/curator.js";
import { divisionSignal, roundBCandidates, runRoundB } from "../../src/proposals/round_b.js";
import { batchPath, proposalBatchSchema, proposalLedgerPath, type Proposal, type ProposalBatch } from "../../src/proposals/schema.js";
import { findRecurrence, normalizeType, statementPattern } from "../../src/proposals/statements.js";
import { createVerifyInitialState, loadState, saveState } from "../../src/state.js";
import { lintTopic } from "../../src/toolkit/layout_lint.js";
import { effectiveTaxonomy, newTopicProblem, topicOfModulePath } from "../../src/toolkit/taxonomy.js";
import { tk, writeSkeleton } from "../toolkit/helpers.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});
const quiet = () => undefined;
const cfg = tk("/tk");

function decl(name: string, over: Partial<ScanDecl> = {}): ScanDecl {
  return {
    name, kind: "theorem", module: `${name.split(".").slice(0, 2).join(".")}.Main`, file: "Main.lean", line: 1, end_line: 2,
    is_private: false, type: "∀ (n : ℕ), n + n = 2 * n", doc: null, axioms: ["propext"], has_sorry: false,
    type_constants: [], body_constants: [], ...over,
  };
}

function item(over: Partial<CuratorItem> = {}): CuratorItem {
  return {
    candidate_id: "Papers.X.foo", verdict: "propose", title: "Foo", reference: "Book, Thm 1", content: "For every n, n + n = 2n.", relation_to_paper: "",
    division: "Foundations", division_reason: "a standard identity in Mathlib's vocabulary", qualifies_by: "standard",
    target_module: "Toolkit/Foundations/Algebra/Doubling.lean", new_module_overview: "Doubling.", new_topic: null,
    proposed_name: "Nat.double_eq_two_mul'", nearest_existing: [{ name: "two_mul", library: "Mathlib", why_not_same: "the other direction" }],
    reuse_evidence: "standard", path: "move", recurrence_confirmed: [], ...over,
  };
}

describe("the topic tree", () => {
  it("places every toolkit module under a topic; a new topic is the owner's item, never silent", async () => {
    const tax = await effectiveTaxonomy({ toolkitRoot: "/nonexistent" });
    const topics = tax.topics.map((t) => t.path);
    expect(topics).toEqual(expect.arrayContaining(["Probability", "Probability/Conditioning", "Design"]));
    expect(topicOfModulePath("Toolkit/Foundations/Probability/Conditioning.lean", cfg)).toBe("Probability");
    expect(lintTopic("Toolkit/Foundations/Probability/Conditioning.lean", { ...cfg, topics })).toEqual([]);
    expect(lintTopic("Toolkit/Foundations/Astrology/Stars.lean", { ...cfg, topics })[0]!.message).toMatch(/not a topic of doc\/taxonomy\.json/);
    expect(newTopicProblem("Probability/Martingales", tax)).toBeNull();
    expect(newTopicProblem("Astrology/Stars", tax)).toMatch(/not a topic/);

    const cand = [{ candidate_id: "Papers.X.foo", source: { kind: "paper_decl" as const, ref: "Papers.X.foo" }, kind: "theorem", statement: "s", context: {} }];
    expect(curatorViolations([item()], cand, cfg, undefined, tax)).toEqual([]);
    expect(curatorViolations([item({ target_module: "Toolkit/Foundations/Probability/Martingales/Doob.lean" })], cand, cfg, undefined, tax).join(" "))
      .toMatch(/not a topic of the tree/);
    expect(curatorViolations([item({ target_module: "Toolkit/Foundations/Probability/Martingales/Doob.lean", new_topic: { path: "Probability/Martingales", scope: "martingales" } })], cand, cfg, undefined, tax)).toEqual([]);
    expect(curatorViolations([item({ division_reason: "" })], cand, cfg, undefined, tax).join(" ")).toMatch(/division_reason is empty/);
  });

  it("asks the owner for each new topic as its own checklist item and refuses to apply while it is pending", () => {
    const p: Proposal = {
      id: "b-doob", round: "B", source: { kind: "paper_decl", ref: "Papers.X.doob" }, verdict: "propose", title: "Doob's inequality",
      reference: "Williams, Probability with Martingales, 14.11", content: "For a submartingale …", division: "Foundations",
      target_module: "Toolkit/Foundations/Probability/Martingales/Doob.lean", new_module_overview: "Martingale inequalities.",
      proposed_name: "MeasureTheory.Submartingale.doob", nearest_existing: [{ name: "x", library: "Mathlib", why_not_same: "y" }],
      reuse_evidence: "named result", division_reason: "a named textbook result in Mathlib's vocabulary", division_signal: "Foundations",
      new_topic: { path: "Probability/Martingales", scope: "martingales and their inequalities" },
    };
    const batch: ProposalBatch = { slug: "s", round: "B", created: "t", proposals: [p] };
    const text = renderChecklist(batch, { toolkitRoot: "/tk" });
    expect(text).toContain("**Goes to.** Foundations › Probability › Martingales (a new topic, decided below) — a named textbook result in Mathlib's vocabulary");
    expect(text).toContain("## topic · Probability/Martingales");
    expect(newTopics(batch).map((t) => t.path)).toEqual(["Probability/Martingales"]);
    const decided = parseChecklist(text.replace(/decision: pending/g, "decision: accept"), batch);
    expect(decided[topicKey("Probability/Martingales")]).toEqual({ kind: "accept" });
    expect(() => parseChecklist(text.replace(/decision: pending/, "decision: defer"), batch)).toThrow(/accepted or declined/);
    // the topic's decision block is checked like an entry's: one cut before its closing fence is refused
    expect(() => parseChecklist(text.slice(0, text.indexOf("decision: pending") + "decision: pending".length), batch)).toThrow(/Probability\/Martingales: unterminated ```decision block/);
  });

  it("presents a paper result on the general-form path in words, and lets the owner place it but not change what it proves", () => {
    const p: Proposal = {
      id: "b-pair", round: "B", source: { kind: "paper_decl", ref: "Papers.X.pair", is_paper_result: true, paper_env: "L-1" }, verdict: "propose",
      title: "Pairwise assignment probabilities", reference: "Cochran, ch. 2", content: "For any finite set of groups …",
      relation_to_paper: "The paper proves the case of adoption dates.", division: "Foundations",
      target_module: "Toolkit/Foundations/Probability/FixedCount.lean", new_module_overview: "Fixed counts.", proposed_name: "fixedCount_pair",
      nearest_existing: [{ name: "x", library: "Causalean", why_not_same: "y" }], reuse_evidence: "standard", path: "generalize",
      paper_shaped: ["`Date` is the paper's aux_Date", "`Pin3` is the paper's reading pin ass:pin-3"],
      checker: { agrees: false, content_matches: true, duplicate_of: null, note: "belongs under Design" },
    };
    const batch: ProposalBatch = { slug: "s", round: "B", created: "t", proposals: [p] };
    const text = renderChecklist(batch, { toolkitRoot: "/tk" });
    const visible = text.slice(0, text.indexOf("<details>"));
    expect(visible).toContain("its general form would be built in your toolkit and the paper's result re-proved from it");
    expect(visible).not.toContain("moves verbatim");
    expect(visible).toContain("own setting — objects defined for this paper and a reading of its wording the referee pinned — so it cannot move as is");
    expect(visible).not.toContain("aux_Date");
    expect(text.slice(text.indexOf("<details>"))).toContain("What ties it to the paper: `Date` is the paper's aux_Date");
    expect(visible).toContain("**In the paper.** The paper proves the case of adoption dates.");
    expect(visible).toContain("the disagreement is about its wording or placement");
    expect(visible).not.toMatch(/does not (match|hold)/);
    const edits = (block: string) => text.replace("decision: pending", block);
    expect(parseChecklist(edits("decision: accept_with_edits\nedits:\ntarget_module: Toolkit/Foundations/Design/FixedCount.lean"), batch)["b-pair"])
      .toEqual({ kind: "accept_with_edits", edits: { target_module: "Toolkit/Foundations/Design/FixedCount.lean" } });
    expect(() => parseChecklist(edits("decision: accept_with_edits\nedits:\ncontent: something else"), batch)).toThrow(/not content/);
    expect(roundBDecisionProblems([p], { "b-pair": { kind: "accept_with_edits", edits: { target_module: "Toolkit/Foundations/Design/FixedCount.lean" } } })).toEqual([]);
    expect(roundBDecisionProblems([p], { "b-pair": { kind: "accept_with_edits", edits: { content: "x" } } }).join(" ")).toMatch(/not content/);
  });
});

describe("candidates", () => {
  it("reads the division signal off what a statement leans on, and sends a result with unused hypotheses to its general form", () => {
    expect(divisionSignal(decl("Papers.X.a", { type_constants: [{ name: "Finset.sum", class: "base", module: "Mathlib.Algebra.BigOperators.Basic" }] }))).toBe("Foundations");
    expect(divisionSignal(decl("Papers.X.b", { body_constants: [{ name: "Causalean.FiniteDesign.E", class: "base", module: "Causalean.Stat.FiniteDesign" }] }))).toBe("Tricks");
    const main = decl("Papers.X.main", { body_constants: [{ name: "Papers.X.help", class: "paper", module: "Papers.X.Main" }] });
    const help = decl("Papers.X.help");
    const file = {
      schema: 1 as const, slug: "x", paper: "Papers.X", scan_path: "", synthetic: false, movable: [], rejected: [],
      candidates: [main, help].map((d) => ({ name: d.name, kind: d.kind, module: d.module, file: d.file, line: 1, end_line: 2, type: d.type, doc: "A doc.", moves_with: d === main ? [help.name] : [], used_by: [], paper_objects: {} })),
    };
    const cands = roundBCandidates(file, new Map(), { declarations: [main, help] }, { unused: new Map([["main", ["hJunk"]]]) });
    const m = cands.find((c) => c.candidate_id === main.name)!;
    expect(m).toMatchObject({ division_signal: "Foundations", dropped_hypotheses: ["hJunk"] });
    expect(m.context.hypotheses_the_proof_never_uses).toEqual(["hJunk"]);
    // The helper is compact in the curator's input; nothing is sent twice.
    const shown = promptCandidates(cands.map((c) => ({ ...c, search_hits: [{ name: "n", library: "L", module: "M", statement: "s".repeat(500), doc: "d" }] })) as GroundedCandidate[]) as Array<Record<string, unknown>>;
    const h = shown.find((c) => c.candidate_id === help.name)!;
    expect(h).toMatchObject({ helper_of: [main.name] });
    expect(h.search_hits).toBeUndefined();
    const mm = shown.find((c) => c.candidate_id === main.name)!;
    expect(mm.dropped_hypotheses).toBeUndefined();
    expect((mm.search_hits as Array<{ statement: string; doc?: string }>)[0]).toEqual({ name: "n", library: "L", statement: "s".repeat(120) });
  });

  it("finds the same pattern over two papers' own definitions — evidence the curator must confirm", async () => {
    const a = "∀ (D : Papers.A.Design) (i j : Fin N), Causalean.FiniteDesign.E D (Papers.A.ind i) = Finset.card (Papers.A.grp D) / ↑N";
    const b = "∀ (W : Papers.B.Plan) (u v : Fin N), Causalean.FiniteDesign.E W (Papers.B.onehot u) = Finset.card (Papers.B.cohort W) / ↑N";
    expect(statementPattern(normalizeType(a))).not.toBeNull();
    expect(statementPattern(normalizeType(a))).toBe(statementPattern(normalizeType(b)));
    expect(statementPattern(normalizeType("∀ (x : Papers.A.T), Papers.A.p x"))).toBeNull();
    const work = await mkdtemp(path.join(os.tmpdir(), "pattern-"));
    tmp.push(work);
    const store = { version: 1 as const, entries: [{
      slug: "paper_b", name: "Papers.B.onehot_mean", module: "Papers.B.Main", kind: "theorem", type_normalized: normalizeType(b),
      type_sha256: "x", doc_first_paragraph: "", verdict: "candidate" as const, reasons: [], proposal_id: "b-onehot-mean", decision: "defer", recorded_at: "t",
    }] };
    const rec = await findRecurrence(store, "paper_a", [{ name: "Papers.A.ind_mean", type: a, doc: null }], work);
    expect(rec.get("Papers.A.ind_mean")?.map((r) => [r.slug, r.name, r.kind])).toEqual([["paper_b", "Papers.B.onehot_mean", "pattern"]]);
    // one temporary index at a time: a later call over other entries drops the earlier one
    await findRecurrence({ ...store, entries: [{ ...store.entries[0]!, name: "Papers.B.other_mean" }] }, "paper_a", [{ name: "Papers.A.ind_mean", type: a, doc: null }], work);
    expect((await readdir(work)).filter((f) => f.startsWith("statements_index."))).toHaveLength(1);
  });
});

describe("propose --reopen-deferred", () => {
  it("re-proposes only the entries the owner deferred, as a new checklist", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "reopen-"));
    tmp.push(root);
    const tcfg = await writeSkeleton(root);
    const qid = "paper_x";
    await mkdir(path.join(root, "runs", qid, "discovery"), { recursive: true });
    const st = createVerifyInitialState(qid, {
      phase: "done", source: { input: "/p.tex", main_file: "main.tex", sha256: "x" }, targets: null, core_sha256: null,
      v1_rounds: 0, v1_5_rounds: 0, findings: [], report_path: null, dry_run: true,
    }, tcfg.papersLib);
    const prefix = st.lean_subdir.split("/").join(".");
    const kept = decl(`${prefix}.kept_result`);
    const deferred = decl(`${prefix}.deferred_result`, { type: "∀ (m : ℕ), m * 1 = m" });
    const scan: CandidateScan = { schema: 1, paper: prefix, toolkit_prefix: "Toolkit", papers_prefix: "Papers", modules: [], declarations: [kept, deferred] };
    await saveState(root, qid, st);
    const rec = await runRoundB({ toolkit: tcfg, qid, dryRun: true, runCodex: (async () => { throw new Error("no model"); }) as never, log: quiet, scan: async () => scan, graph: async () => null });
    st.verify!.promotion = { ...rec, status: "applied" };
    await saveState(root, qid, st);
    const first = proposalBatchSchema.parse(JSON.parse(await readFile(batchPath(tcfg, qid), "utf8")));
    const ledger = { version: 1, declarations: [], decisions: first.proposals.map((p) => ({
      kind: "proposal_decision", slug: qid, round: "B", proposal_id: p.id, decision: { kind: p.source.ref === deferred.name ? "defer" : "accept" },
      proposal: p, decided_at: "t", batch_created: first.created, promoted: [], dry_run: true,
    })) };
    await mkdir(path.dirname(proposalLedgerPath(tcfg, qid, true)), { recursive: true });
    await writeFile(proposalLedgerPath(tcfg, qid, true), JSON.stringify(ledger));
    // refused on a run re-entered and not finished: its phase is the re-formalization's (the reopen flipped it to
    // round B, and the next resume left the proof loop it was halted in)
    st.verify!.phase = "formalization";
    await saveState(root, qid, st);
    await expect(runProposeCli([qid, "--reopen-deferred", "--dry-run", "--toolkit", root], { log: quiet, reopen: { scan: async () => scan, graph: async () => null } })).rejects.toThrow(/the run is not finished \(phase formalization\)/);
    expect((await loadState(root, qid)).verify).toMatchObject({ phase: "formalization", promotion: { status: "applied" } });
    st.verify!.phase = "done";
    await saveState(root, qid, st);
    await runProposeCli([qid, "--reopen-deferred", "--dry-run", "--toolkit", root], { log: quiet, reopen: { scan: async () => scan, graph: async () => null } });
    const again = proposalBatchSchema.parse(JSON.parse(await readFile(batchPath(tcfg, qid), "utf8")));
    expect(again.proposals.map((p) => p.source.ref)).toEqual([deferred.name]);
    // the round waits in the phase the page and the runner read it from (it stayed done: the page drew nothing)
    expect((await loadState(root, qid)).verify).toMatchObject({ phase: "proposals_B", promotion: { status: "pending_user" } });
  });
});
