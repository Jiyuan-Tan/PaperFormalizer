// Round A (cited results after F1) and the rules the promotion rounds share since the study
// pipeline builds entries: the dry-run round end to end, the generalize path of a paper-shaped
// result, the naming check, the corollary re-proof's guard, and a moved module's minimal header.
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { reproveAsCorollary } from "../../src/proposals/build.js";
import { paperShapedReasons } from "../../src/proposals/candidate_scan.js";
import { parseChecklist, renderChecklist } from "../../src/proposals/checklist.js";
import { runProposeCli } from "../../src/proposals/cli.js";
import { nameProblems } from "../../src/proposals/curator.js";
import { neededContext, planMove, type MovePlanInput } from "../../src/proposals/move.js";
import { runRoundA } from "../../src/proposals/round_a.js";
import { batchPath, checklistPath, entersBy, proposalBatchSchema, proposalLedgerPath, type Proposal } from "../../src/proposals/schema.js";
import { createVerifyInitialState, loadState, saveState } from "../../src/state.js";
import { loadLedger } from "../../src/toolkit/ledger.js";
import { writeSkeleton } from "../toolkit/helpers.js";
import { PAPER_MAIN } from "./helpers.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});
const quiet = () => undefined;
const noCodex = (async () => { throw new Error("no model call in tests"); }) as never;
const QID = "paper_a";

const CORE = {
  qid: QID, cluster: "stat",
  symbols: [{ name: "Y", type: "outcome", space: "ℝ", def: "the outcome" }],
  assumptions: [{ id: "ass:reg", condition: "Y bounded", free_symbols: ["Y"], novel: { flag: true, justification: "regularity" } }],
  definitions: [],
  statements: [
    { id: "thm:main", kind: "theorem", statement: "rate holds", depends_on: ["ass:reg", "lem:borrowed-upper"], status: "to-prove", proof_tex: "By the upper bound." },
    { id: "lem:borrowed-upper", kind: "lemma", statement: "A published upper bound.", depends_on: [], status: "cited", source: { cite: "BK2022", locator: "Theorem 3" } },
  ],
  target_estimand: "theta",
  bibliography: [{ key: "BK2022", citation: "Bonvini, Kennedy (2022)" }],
};

describe("round A", () => {
  it("proposes the cited results only, with the cited text; the owner's decisions build them through the study pipeline", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "rounda-"));
    tmp.push(root);
    const cfg = await writeSkeleton(root);
    const runDir = path.join(root, "runs", QID);
    await mkdir(path.join(runDir, "discovery", "cited_sources"), { recursive: true });
    await writeFile(path.join(runDir, "discovery", "core.json"), JSON.stringify(CORE));
    await writeFile(path.join(runDir, "discovery", "cited_sources", "BK2022.txt"), "Theorem 3. The upper bound holds for every bounded Y.");
    const st = createVerifyInitialState(QID, {
      phase: "proposals_A", source: { input: "/p.tex", main_file: "main.tex", sha256: "x" }, targets: null, core_sha256: null,
      v1_rounds: 0, v1_5_rounds: 0, findings: [], report_path: null, dry_run: true,
    }, cfg.papersLib);
    const rec = await runRoundA({ toolkit: cfg, qid: QID, dryRun: true, runCodex: noCodex, log: quiet });
    st.verify!.promotion_a = rec;
    await saveState(root, QID, st);

    const batch = proposalBatchSchema.parse(JSON.parse(await readFile(batchPath(cfg, QID, "A"), "utf8")));
    expect(batch.round).toBe("A");
    expect(batch.proposals.map((p) => [p.id, p.source.ref, p.path])).toEqual([["a-lem-borrowed-upper", "lem:borrowed-upper", "generalize"]]);
    expect(batch.proposals[0]!.source_text).toContain("The upper bound holds");
    const text = await readFile(checklistPath(cfg, QID, true, "A"), "utf8");
    expect(text).toContain("cited result(s) it does not prove");
    expect(text).toContain("It is built in your toolkit from scratch");
    expect(text).toContain("--round A --apply");
    expect(() => parseChecklist(text.replace("decision: pending", "decision: generalize_first"), batch)).toThrow(/always built in general form/);

    // Accept it; `propose --round A --apply` builds it through the (fake) study and resumes the run.
    await writeFile(checklistPath(cfg, QID, true, "A"), text.replace("decision: pending", "decision: accept"));
    const studies: string[] = [];
    const resumed: string[][] = [];
    await runProposeCli([QID, "--round", "A", "--apply", "--toolkit", root, "--dry-run"], {
      log: quiet,
      resumeVerify: async (argv) => { resumed.push(argv); },
      applyA: { runStudy: async (o) => { studies.push(o.slug); return { phase: "done" } as never; } },
    });
    expect(studies).toEqual([`${QID}__a-lem-borrowed-upper`]);
    expect(await readFile(path.join(root, "runs", `study_${QID}__a-lem-borrowed-upper`, "requirement.md"), "utf8")).toContain("The upper bound holds");
    expect((await loadState(root, QID)).verify!.promotion_a!.status).toBe("applied");
    expect(resumed).toHaveLength(1);
    const ledger = await loadLedger(proposalLedgerPath(cfg, QID, true));
    expect(ledger.decisions).toContainEqual(expect.objectContaining({ round: "A", proposal_id: "a-lem-borrowed-upper", decision: { kind: "accept" } }));
  });
});

const entry = (over: Partial<Proposal>): Proposal => ({
  id: "b-x", round: "B", source: { kind: "paper_decl", ref: "Papers.P.x" }, verdict: "propose",
  title: "A result", reference: "new", content: "For all n, …", division: "Tricks", target_module: "Toolkit/Tricks/A/B.lean",
  new_module_overview: "x", proposed_name: "foo", nearest_existing: [{ name: "n", library: "Mathlib", why_not_same: "w" }],
  reuse_evidence: "r", ...over,
});

describe("round B: a result stated over the paper's own setting", () => {
  it("is paper-shaped, enters by the generalize path, and the checklist says so in words", () => {
    const scan = { declarations: [
      { name: "Papers.P.Date", kind: "def" }, { name: "Papers.P.pin", kind: "def" }, { name: "Papers.P.helper", kind: "theorem" },
    ] } as never;
    const shaped = paperShapedReasons({ moves_with: ["Papers.P.Date", "Papers.P.pin", "Papers.P.helper"], paper_objects: { "Papers.P.pin": "ass:pin-3", "Papers.P.helper": "lem:aux" } }, scan);
    expect(shaped).toEqual(["`Date` is a definition made for this paper", "`pin` is the paper's reading pin ass:pin-3"]);
    expect(paperShapedReasons({ moves_with: ["Papers.P.helper"], paper_objects: {} }, scan)).toEqual([]);

    const moving = entry({ path: "move" });
    const general = entry({ path: "generalize", paper_shaped: shaped });
    expect(entersBy(moving, { kind: "accept" })).toBe("move");
    expect(entersBy(moving, { kind: "generalize_first" })).toBe("generalize");
    expect(entersBy(general, { kind: "accept" })).toBe("generalize");
    const text = renderChecklist({ slug: "p", round: "B", created: "t", proposals: [general] }, { toolkitRoot: "/tk" });
    expect(text).toContain("Built in general form — the statement above — in your toolkit; the paper's result stays in the paper as a corollary of it.");
    expect(text).toContain("`Date` is a definition made for this paper");
  });
});

describe("toolkit names", () => {
  it("refuses a taken name and a type head outside the type's namespace", () => {
    const table = new Map([["MeasureTheory.Integrable", "def"], ["Nat.succ_le", "theorem"]]);
    expect(nameProblems("Nat.succ_le", table)).toEqual(["`Nat.succ_le` is already declared in a base library or the toolkit"]);
    expect(nameProblems("Integrable.foo", table)[0]).toMatch(/name it `MeasureTheory\.Integrable\.foo`/);
    expect(nameProblems("MeasureTheory.Integrable.foo", table)).toEqual([]);
  });
});

describe("re-proving the paper's result as a corollary", () => {
  it("keeps the edit only when the statement is unchanged and the module builds; otherwise restores the file", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "corollary-"));
    tmp.push(root);
    const cfg = await writeSkeleton(root);
    const file = path.join(root, "Papers", "P", "Main.lean");
    await mkdir(path.dirname(file), { recursive: true });
    const before = "namespace Papers.P\n\ntheorem r (n : Nat) : n + 0 = n := by\n  simp\n\nend Papers.P\n";
    await writeFile(file, before);
    const edit = (to: string) => (async () => { await writeFile(file, to); return { stdout: "COROLLARY: done" }; }) as never;
    const general = { name: "Toolkit.Tricks.A.add_zero'", module: "Toolkit.Tricks.A.B" };
    const args = { toolkit: cfg, qid: "p", proposalId: "b-r", decl: "Papers.P.r", file, general, log: quiet };

    const changed = await reproveAsCorollary({ ...args, deps: { runCodex: edit(before.replace("n + 0 = n", "n = n")), build: async () => ({ ok: true, log: "" }) } });
    expect(changed).toEqual({ ok: false, why: "the statement changed" });
    expect(await readFile(file, "utf8")).toBe(before);

    const reproved = before.replace("  simp", `  exact ${general.name} n`);
    const broken = await reproveAsCorollary({ ...args, deps: { runCodex: edit(reproved), build: async () => ({ ok: false, log: "error: unknown identifier" }) } });
    expect(broken.ok).toBe(false);
    expect(await readFile(file, "utf8")).toBe(before);

    expect(await reproveAsCorollary({ ...args, deps: { runCodex: edit(reproved), build: async () => ({ ok: true, log: "" }) } })).toEqual({ ok: true, why: "" });
    expect(await readFile(file, "utf8")).toBe(reproved);
  });
});

describe("a moved module's header", () => {
  it("imports what the moved declarations use and keeps only the context they need", () => {
    const ctx = ["open Nat Finset", "set_option linter.unusedVariables false", "set_option maxHeartbeats 400000", "variable {Ω : Type*} (k : ℕ)", "open scoped BigOperators"];
    // `Nat.succ_le` written `succ_le` needs `open Nat`; nothing needs `Finset`; Ω is bound by the lemma itself.
    expect(neededContext(ctx, ["theorem t {Ω : Type*} (x : Ω) : succ_le k = k := rfl"], "Papers", [{ name: "Nat.succ_le" }]))
      .toEqual(["open Nat", "set_option maxHeartbeats 400000", "variable (k : ℕ)", "open scoped BigOperators"]);

    const main = path.join("/tk", "Papers", "Fix", "Main.lean");
    const input: MovePlanInput = {
      cfg: { lib: "Toolkit", papersLib: "Papers", toolkitRoot: "/tk" },
      paperFiles: new Map([[main, PAPER_MAIN]]),
      decls: [
        { from: "Papers.Fix.twice", to: "Toolkit.Tricks.Arith.twice", kind: "def" },
        { from: "Papers.Fix.twice_eq_two_mul", to: "Toolkit.Tricks.Arith.twice_eq_two_mul'", kind: "theorem" },
      ],
      mainFrom: "Papers.Fix.twice_eq_two_mul", docstringOverride: null, fallbackDocstring: null,
      target: { rel: "Toolkit/Tricks/Arith/Doubling.lean", module: "Toolkit.Tricks.Arith.Doubling", division: "Tricks", overview: "Doubling.", existingText: null },
      alreadyMoved: new Map(), toolkitModulesUsed: [], readModule: () => null,
      usedConstants: [{ name: "HAdd.hAdd", module: "Init.Prelude" }, { name: "Mathlib.Tactic.Ring.add_pf", module: "Mathlib.Tactic.Ring.Basic" }],
    };
    const minimal = planMove(input);
    expect(minimal.importsAdded).toEqual(["Mathlib.Tactic.Ring.Basic"]);
    expect(minimal.block).not.toContain("open Nat");
    // The fallback: the source file's imports and its opens.
    const source = planMove({ ...input, importMode: "source" });
    expect(source.importsAdded).toEqual(["Mathlib.Tactic.Ring"]);
    expect(source.block).toContain("open Nat");
  });
});
