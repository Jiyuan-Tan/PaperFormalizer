// F5's Lean Proof in English: which account each helper is proved in (inside a result, or shared),
// what an English entry may and may not say, the review of it against the Lean (an entry with a defect
// revised, up to three times), and the comparator's verdicts — end to end with the model stubbed.
import { copyFile, mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it, vi } from "vitest";
import {
  auxClosure, batchByChars, checkComparisons, checkEntries, checkReviews, citedShared, docAbove, dominators, emitLeanProofEnglish, entryProblems, fileDecls,
  LEAN_PROOF_ENGLISH_ARTIFACT, leanNameSet, planTasks, proseOnly, reviewBlock, statementOf, translatorBlocks, usedDefs, type LeanProofEnglish, type Task,
} from "../../src/formalization/lean_proof_english.js";
import { artifactPaths, type StageDeps } from "../../src/pipeline_support.js";
import { createEmptyGraph, graphPath, saveGraph } from "../../src/graph/store.js";
import { addNode, setLean } from "../../src/graph/mutate.js";
import { createVerifyInitialState } from "../../src/state.js";
import type { PipelineContext } from "../../src/types.js";
import { leanProofView } from "../../src/ui/run_model.js";

const PROMPTS = path.join(__dirname, "..", "..", "src", "formalization", "prompts", "F5");

const LEAN = [
  "namespace Papers.UserPaper", "",
  "/-- The square of a number. -/",
  "def sq (x : ℕ) : ℕ := x * x", "",
  "/-- The square of a positive number is positive. -/",
  "lemma sq_pos_aux (x : ℕ) (hx : 0 < x) : 0 < sq x := by",
  "  unfold sq",
  "  positivity", "",
  "lemma shared_step (x : ℕ) : sq x = x ^ 2 := by",
  "  unfold sq; ring", "",
  "theorem main_result (x : ℕ) (hx : 0 < x) : 0 < x ^ 2 := by",
  "  rw [← shared_step]",
  "  exact sq_pos_aux x hx", "",
  "theorem second_result (x : ℕ) : sq x = x * x := by",
  "  rw [shared_step]; ring", "",
  "end Papers.UserPaper", "",
].join("\n");

const decls = fileDecls("Parts.lean", LEAN);
const nodeOfDecl = new Map([["Papers.UserPaper.main_result", "thm:main"], ["Papers.UserPaper.second_result", "thm:second"]]);
const results = [{ id: "thm:main", decl: "Papers.UserPaper.main_result", statement: "$0 < x^2$", deps: ["ass:pos"] }, { id: "thm:second", decl: "Papers.UserPaper.second_result", statement: "$x^2 = x x$" }];
const lineOf = (needle: string) => LEAN.split("\n").findIndex((l) => l.includes(needle)) + 1;

describe("the run's Lean", () => {
  it("reads the docstring right above each declaration, not the file's first one", () => {
    expect(docAbove("/-- First doc. -/\ndef a := 1\n/-- Second doc. -/\ndef b := 2", 4)).toBe("Second doc.");
    expect(docAbove("/-- First doc. -/\ndef a := 1\ndef b := 2", 3)).toBe("");
    expect(decls.find((d) => d.leaf === "sq_pos_aux")!.doc).toBe("The square of a positive number is positive.");
    expect(decls.find((d) => d.leaf === "shared_step")!.doc).toBe("");
  });
});

describe("the Lean in the prompts", () => {
  it("states a declaration up to its top-level `:=` or its first pattern-match line", () => {
    const st = (source: string) => statementOf({ source } as Parameters<typeof statementOf>[0]);
    expect(st("lemma a (n : ℕ := 0) (h : n = 0) : n + 0 = n := by\n  simp")).toBe("lemma a (n : ℕ := 0) (h : n = 0) : n + 0 = n");
    expect(st("/-- uses := in prose -/\ntheorem b : True := trivial")).toBe("/-- uses := in prose -/\ntheorem b : True");
    expect(st("theorem c : ∀ n : ℕ, |(n : ℤ)| ≥ 0\n  | 0 => by simp\n  | n + 1 => by positivity")).toBe("theorem c : ∀ n : ℕ, |(n : ℤ)| ≥ 0");
    expect(st("axiom d : False")).toBe("axiom d : False");
  });
  it("shows each task's declaration and helpers with their line numbers, the definitions they use once, and a cited shared lemma's statement", () => {
    const plan = planTasks(decls, nodeOfDecl, results);
    const main = plan.results[0]!;
    const byLeaf = new Map(decls.map((d) => [d.leaf, [d]] as const));
    const defs = usedDefs([main.decl, ...main.inline], byLeaf);
    expect(defs.map((d) => d.leaf)).toEqual(["sq"]);
    expect(usedDefs([main.decl, ...main.inline], byLeaf, 0)).toEqual([]);
    const { context, tasks } = translatorBlocks([main], plan, new Map(), (f) => `Lean/${f}`, defs);
    expect(tasks).toContain(`${lineOf("theorem main_result")}| theorem main_result`);
    expect(tasks).toContain(`${lineOf("lemma sq_pos_aux")}| lemma sq_pos_aux`);
    expect(context).toContain(`${lineOf("def sq")}| def sq`);
    expect(context).toContain("lemma shared_step (x : ℕ) : sq x = x ^ 2");
    expect(context).not.toContain("unfold sq; ring");
    const review = reviewBlock([main], new Map([["thm:main", { id: "thm:main", statement: null, proof: "We show it." }]]), (f) => `Lean/${f}`);
    expect(review).toContain(`${lineOf("  exact sq_pos_aux")}|   exact sq_pos_aux x hx`);
  });
});

describe("planTasks", () => {
  it("proves a helper only one result uses inside that result's account, shares one two results use, and writes no definition", () => {
    const plan = planTasks(decls, nodeOfDecl, results);
    expect(plan.results.map((t) => [t.id, t.inline.map((d) => d.leaf)])).toEqual([["thm:main", ["sq_pos_aux"]], ["thm:second", []]]);
    expect(plan.shared.map((t) => [t.id, t.decl.leaf, t.inline.length])).toEqual([["A1", "shared_step", 0]]);
    // a result may cite its paper dependencies (a cited result among them) and the shared lemmas its Lean uses
    expect(plan.uses.get("thm:main")).toEqual({ refs: ["ass:pos"], aux: ["A1"] });
    expect(plan.uses.get("thm:second")).toEqual({ refs: [], aux: ["A1"] });
    // one call per account
    expect(plan.calls.map((c) => c.map((t) => t.id))).toEqual([["thm:main"], ["thm:second"], ["A1"]]);
  });

  it("a helper reached only through a shared lemma is proved inside the shared lemma", () => {
    const lean = ["namespace P", "", "lemma base_fact : True := trivial", "",
      "lemma mid_step : True := by", "  exact base_fact", "",
      "theorem first_thm : True := by", "  exact mid_step", "",
      "theorem second_thm : True := by", "  exact mid_step", "", "end P", ""].join("\n");
    const ds = fileDecls("N.lean", lean);
    const plan = planTasks(ds, new Map([["P.first_thm", "thm:a"], ["P.second_thm", "thm:b"]]), [{ id: "thm:a", decl: "P.first_thm", statement: "" }, { id: "thm:b", decl: "P.second_thm", statement: "" }]);
    expect(plan.shared.map((t) => [t.id, t.decl.leaf, t.inline.map((d) => d.leaf)])).toEqual([["A1", "mid_step", ["base_fact"]]]);
    expect(plan.results.every((t) => t.inline.length === 0)).toBe(true);
  });

  it("two paper results formalized by one declaration share one account, written once", () => {
    const plan = planTasks(decls, new Map([...nodeOfDecl, ["Papers.UserPaper.main_result", "thm:main"]]), [results[0]!, { id: "cor:main", decl: "Papers.UserPaper.main_result", statement: "$x^2>0$" }]);
    expect(plan.results.map((t) => t.id)).toEqual(["thm:main", "cor:main"]);
    expect(plan.aliases.get("cor:main")).toBe("thm:main");
    // shared_step is used by this declaration alone here: proved inside the one account
    expect(plan.calls.map((c) => c.map((t) => t.id))).toEqual([["thm:main"]]);
    expect(plan.results[1]!.inline.map((d) => d.leaf)).toEqual(["shared_step", "sq_pos_aux"]);
  });

  it("an account too long for one call gives its largest part its own account, cited from it", () => {
    const body = (n: number) => Array.from({ length: Math.round((n * 2) / 3) }, () => "  have : True := trivial"); // sizes for a 4000-line cap
    const lean = ["namespace P", "",
      "lemma part_a : True := by", ...body(2500), "  trivial", "",
      "lemma part_b2 : True := by", ...body(2000), "  trivial", "",
      "lemma part_b : True := by", "  exact part_b2", ...body(2500), "",
      "lemma part_c : True := by", ...body(500), "  trivial", "",
      "theorem big_thm : True := by", "  exact part_a", "  exact part_b", "  exact part_c", "", "end P", ""].join("\n");
    const plan = planTasks(fileDecls("B.lean", lean), new Map([["P.big_thm", "thm:big"]]), [{ id: "thm:big", decl: "P.big_thm", statement: "" }]);
    // part_b with part_b2 (≈4,500 lines) is split off; the rest (≈3,000) fits
    expect(plan.shared.map((t) => [t.id, t.decl.leaf, t.inline.map((d) => d.leaf)])).toEqual([["A1", "part_b", ["part_b2"]]]);
    expect(plan.results[0]!.inline.map((d) => d.leaf)).toEqual(["part_a", "part_c"]);
    expect(plan.uses.get("thm:big")!.aux).toEqual(["A1"]);
    // a result whose Lean is a short wrapper of one long lemma keeps the argument: the part split off
    // is the long lemma's largest part, not the long lemma
    const wrapped = lean.replace("theorem big_thm : True := by", "lemma core_step : True := by").replace("end P", "theorem wrap_thm : True := by\n  exact core_step\n\nend P");
    const p2 = planTasks(fileDecls("B.lean", wrapped), new Map([["P.wrap_thm", "thm:wrap"]]), [{ id: "thm:wrap", decl: "P.wrap_thm", statement: "" }]);
    expect(p2.shared.map((t) => t.decl.leaf)).toEqual(["part_b"]);
    expect(p2.results[0]!.inline.map((d) => d.leaf)).toEqual(["core_step", "part_a", "part_c"]);
  });

  it("a helper a split-off part and its account both use is an account of its own, cited by both", () => {
    const body = (n: number) => Array.from({ length: Math.round((n * 2) / 3) }, () => "  have : True := trivial"); // sizes for a 4000-line cap
    const lean = ["namespace P", "", "lemma basic_fact : True := trivial", "",
      "lemma part_r : True := by", "  exact basic_fact", ...body(5000), "",
      "lemma part_q : True := by", "  exact basic_fact", ...body(2000), "",
      "theorem big_thm : True := by", "  exact part_r", "  exact part_q", "", "end P", ""].join("\n");
    const plan = planTasks(fileDecls("R.lean", lean), new Map([["P.big_thm", "thm:big"]]), [{ id: "thm:big", decl: "P.big_thm", statement: "" }]);
    expect(plan.shared.map((t) => t.decl.leaf).sort()).toEqual(["basic_fact", "part_r"]);
    const id = (leaf: string) => plan.shared.find((t) => t.decl.leaf === leaf)!.id;
    expect(plan.uses.get(id("part_r"))!.aux).toEqual([id("basic_fact")]);
    expect(plan.uses.get("thm:big")!.aux.sort()).toEqual([id("basic_fact"), id("part_r")].sort());
    // both are parts of the result: its English must cite them
    expect(plan.parts.get("thm:big")!.sort()).toEqual([id("basic_fact"), id("part_r")].sort());
    const t = plan.results[0]!;
    const e = { id: t.id, statement: null, proof: `[It holds](lean:${t.decl.line}-${t.decl.end}) and [so does this](lean:${t.inline[0]!.line}).` };
    expect(entryProblems(e, t, new Set(plan.uses.get(t.id)!.aux), new Set(), (x) => x, plan.parts.get(t.id)).join(" ")).toContain("is never cited");
  });

  it("a lemma only the parts split off use is not required in the account they came from", () => {
    const body = (n: number) => Array.from({ length: Math.round((n * 2) / 3) }, () => "  have : True := trivial"); // sizes for a 4000-line cap
    const lean = ["namespace P", "", "lemma basic_fact : True := trivial", "",
      "lemma part_1 : True := by", "  exact basic_fact", ...body(3000), "",
      "lemma part_2 : True := by", "  exact basic_fact", ...body(3000), "",
      "lemma part_3 : True := by", ...body(3000), "  trivial", "",
      "theorem big_thm : True := by", "  exact part_1", "  exact part_2", "  exact part_3", "", "end P", ""].join("\n");
    const plan = planTasks(fileDecls("Q.lean", lean), new Map([["P.big_thm", "thm:big"]]), [{ id: "thm:big", decl: "P.big_thm", statement: "" }]);
    const id = (leaf: string) => plan.shared.find((t) => t.decl.leaf === leaf)?.id;
    expect(id("basic_fact")).toBeDefined();
    expect(plan.parts.get("thm:big")!.sort()).toEqual([id("part_1"), id("part_2")].sort());
    // and it may cite every part it must cite
    for (const x of plan.parts.get("thm:big")!) expect(plan.uses.get("thm:big")!.aux).toContain(x);
  });

  it("an account whose own declaration is too long for one call is not split", () => {
    const lean = ["namespace P", "", ...Array.from({ length: 50 }, (_, i) => [`lemma small_${i} : True := trivial`, ""]).flat(),
      "theorem huge_thm : True := by", ...Array.from({ length: 50 }, (_, i) => `  exact small_${i}`), ...Array.from({ length: 6100 }, () => "  have : True := trivial"), "", "end P", ""].join("\n");
    const plan = planTasks(fileDecls("H.lean", lean), new Map([["P.huge_thm", "thm:huge"]]), [{ id: "thm:huge", decl: "P.huge_thm", statement: "" }]);
    expect(plan.shared).toHaveLength(0);
    expect(plan.results[0]!.inline).toHaveLength(50);
  });

  it("one call per result; small shared lemmas packed together", () => {
    const n = 30;
    const lean = ["namespace P", "", ...Array.from({ length: n }, (_, i) => [`lemma tiny_${i} : True := trivial`, ""]).flat(),
      "theorem one_thm : True := by", ...Array.from({ length: n }, (_, i) => `  exact tiny_${i}`), "",
      "theorem two_thm : True := by", ...Array.from({ length: n }, (_, i) => `  exact tiny_${i}`), "", "end P", ""].join("\n");
    const plan = planTasks(fileDecls("T.lean", lean), new Map([["P.one_thm", "thm:a"], ["P.two_thm", "thm:b"]]), [{ id: "thm:a", decl: "P.one_thm", statement: "" }, { id: "thm:b", decl: "P.two_thm", statement: "" }]);
    expect(plan.shared).toHaveLength(n);
    expect(plan.calls.map((c) => c.length)).toEqual([1, 1, 25, 5]);
  });

  it("a cited shared lemma with no entry is still cited (so the account cannot be confirmed without it)", () => {
    expect(citedShared("by ⟦A2⟧ and ⟦thm:x⟧", new Map())).toEqual(["A2"]);
  });

  it("dominators: a vertex reached by two branches is dominated by the root, one below it by that vertex", () => {
    // 0 → 1, 2; 1 → 3; 2 → 3; 3 → 4
    expect([...dominators([[1, 2], [3], [3], [4], []])]).toEqual([0, 0, 0, 0, 3]);
    // an unreached vertex has none
    expect(dominators([[1], [], []])[2]).toBe(-1);
  });
});

describe("what an English entry may say", () => {
  const rel = (f: string) => f;
  const main: Task = { id: "thm:main", role: "result", decl: decls.find((d) => d.leaf === "main_result")!, inline: [decls.find((d) => d.leaf === "sq_pos_aux")!] };
  const aux = main.inline[0]!;
  const names = leanNameSet(decls);
  const cite = new Set(["A1"]);
  const ok = { id: "thm:main", statement: null, proof: String.raw`Since $x^2 = x\cdot x$ by ⟦A1⟧, [the claim follows](lean:${main.decl.line + 1}-${main.decl.end}) from [the positivity of $\mathrm{sq}(x)$ for $x>0$](lean:Parts.lean:${aux.line}-${aux.end}).` };

  it("accepts a self-contained proof with anchors on its declarations and references it may make", () => {
    expect(entryProblems(ok, main, cite, names, rel)).toEqual([]);
    // "positivity" is English too
    expect(entryProblems({ ...ok, proof: `${ok.proof} This holds by positivity of the square.` }, main, cite, names, rel)).toEqual([]);
  });

  it("refuses Lean in the prose, a reference it may not make, an anchor on no declaration of the account or one that does not parse, a helper left out, and a proof with no anchor", () => {
    const p = entryProblems({ ...ok, proof: "By `shared_step` and simp, ⟦A9⟧ gives it [here](lean:1-2)." }, main, cite, names, rel).join(" | ");
    expect(p).toContain("backticks");
    expect(p).toContain(`"simp" is Lean`);
    expect(p).toContain("⟦A9⟧ is no id");
    expect(p).toContain("is on no declaration of this account");
    expect(entryProblems({ ...ok, proof: "Clear." }, main, cite, names, rel).join(" ")).toContain("no anchor on its own declaration");
    // a helper whose lines no anchor reaches is not proved in it
    expect(entryProblems({ ...ok, proof: `[It holds](lean:${main.decl.line}).` }, main, cite, names, rel).join(" ")).toContain("the helper `Papers.UserPaper.sq_pos_aux`");
    // an anchor in another file than the helper's
    expect(entryProblems({ ...ok, proof: `${ok.proof} [x](lean:Other.lean:${aux.line})` }, main, cite, names, rel).join(" ")).toContain("is on no declaration");
    expect(entryProblems({ ...ok, proof: `${ok.proof} [for $t$ in (0,1/2]](lean:${main.decl.line})` }, main, cite, names, rel).join(" ")).toContain("does not parse");
    // an unclosed bracket before many displays fails fast (no exponential backtracking)
    const t0 = Date.now();
    entryProblems({ ...ok, proof: `${ok.proof} see [Smith ${"$$a$$ ".repeat(40)}` }, main, cite, names, rel);
    expect(Date.now() - t0).toBeLessThan(500);
    // TeX display math inside a phrase, with brackets in it
    expect(entryProblems({ ...ok, proof: `${ok.proof} [the derivative is\n\\[\nDf(x)[h]=h,\n\\]\nas claimed](lean:${main.decl.line})` }, main, cite, names, rel)).toEqual([]);
    // an interval in math is ignored, inline or displayed
    expect(entryProblems({ ...ok, proof: `${ok.proof} [for $t\\in(0,1/2]$ and $$s\\in[0,1)$$](lean:${main.decl.line})` }, main, cite, names, rel)).toEqual([]);
    expect(entryProblems({ ...ok, proof: `${ok.proof} By sq_pos_aux [it holds](lean:${main.decl.line}).` }, main, cite, names, rel).join(" ")).toContain('"sq_pos_aux" is a Lean declaration name');
    expect(proseOnly(String.raw`see $\mathrm{sq\_pos}$ and \[a=b\]`)).not.toContain("sq");
  });

  it("asks a failing entry again and, the second time, keeps what is sound, an anchor on no declaration left as its phrase", () => {
    const bad = { entries: [{ id: "thm:main", statement: null, proof: "By simp, [it holds](lean:1-2)." }] };
    expect(checkEntries([main], bad, () => cite, names, rel).ok.size).toBe(0);
    expect(checkEntries([main], bad, () => cite, names, rel, true).ok.get("thm:main")?.proof).toBe("By simp, it holds.");
  });

  it("an account takes the shared lemmas its proof cites, and theirs, in order", () => {
    const aux = new Map([["A1", { id: "A1", statement: "uses ⟦A2⟧", proof: null }], ["A2", { id: "A2", statement: "x", proof: null }], ["A3", { id: "A3", statement: "y", proof: null }]]);
    expect(auxClosure("by ⟦A3⟧ and ⟦A1⟧", aux)).toEqual(["A3", "A1", "A2"]);
  });
});

describe("the review and the comparator's replies", () => {
  it("a review says unfaithful only with an issue; an unknown id is ignored", () => {
    const r = checkReviews(["A1", "A2"], { reviews: [{ id: "A1", faithful: false, issues: ["the sign: Lean proves x - y"] }, { id: "A2", faithful: false, issues: [] }, { id: "Z", faithful: true, issues: [] }] });
    expect(r.get("A1")).toEqual({ faithful: false, issues: ["the sign: Lean proves x - y"], readability: [] });
    expect(r.get("A2")?.faithful).toBe(true);
    expect(r.has("Z")).toBe(false);
    // a readability note never makes a faithful entry unfaithful
    expect(checkReviews(["A1"], { reviews: [{ id: "A1", faithful: true, issues: [], readability: ["$c$ is used before it is defined"] }] }).get("A1")).toEqual({ faithful: true, issues: [], readability: ["$c$ is used before it is defined"] });
  });

  it("an error is a departure (one that leaves the step out is an unclear step) and needs a snippet and its suggestion; an ambiguity is a note, a difference a route", () => {
    const it0 = { id: "thm:main", ref: { id: "thm:main", kind: "theorem", label: null, statement: "" }, printed: "p", corrected: null, recorded: [], cited: [], account: "a" };
    const d = (kind: string, printed: string, suggestion: string, missing = false) => ({ printed, lean: "L", kind, missing, suggestion, reason: "r" });
    const c = checkComparisons([it0], { results: [{ id: "thm:main", summary: "s", differences: [d("error", "", "x"), d("difference", "q", "")] }] });
    expect(c.ok.get("thm:main")?.verdict).toBe("other-route");
    expect(c.problems[0]).toContain("dropped");
    const e = checkComparisons([it0], { results: [{ id: "thm:main", summary: "s", differences: [d("error", "so $H=0$", "so $H=\\ker d=0$"), d("error", "Hence $z$.", "Hence $z$, since $d$ is injective.", true), d("ambiguity", "for each $x$ there is $R$", "there is $R$ such that for each $x$")] }] }).ok.get("thm:main")!;
    expect(e.verdict).toBe("departs");
    expect(e.departures.map((x) => x.kind)).toEqual(["printed-wrong"]);
    expect(e.unclear.map((x) => x.printed)).toEqual(["for each $x$ there is $R$", "Hence $z$."]);
    // an omission alone, given as an error, is an unclear step: no departure, the verdict unchanged
    const o = checkComparisons([it0], { results: [{ id: "thm:main", summary: "s", differences: [d("error", "Hence $z$.", "Hence $z$, since $d$ is injective.", true)] }] });
    expect(o.problems).toEqual([]);
    expect(o.ok.get("thm:main")).toMatchObject({ verdict: "follows", departures: [], unclear: [{ printed: "Hence $z$.", lean: "L", suggestion: "Hence $z$, since $d$ is injective." }] });
    // an ambiguity alone never changes the verdict; a reply without differences reads no answer
    expect(checkComparisons([it0], { results: [{ id: "thm:main", summary: "s", differences: [d("ambiguity", "a", "b")] }] }).ok.get("thm:main")?.verdict).toBe("follows");
    expect(checkComparisons([it0], { results: [{ id: "thm:main", summary: "s" }] }).problems[0]).toContain("no answer");
    expect(batchByChars([{ printed: "aa", account: "b" }, { printed: "cccc", account: "" }], 4)).toHaveLength(2);
  });
});

async function seed() {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "lean-proof-english-"));
  const qid = "user_paper";
  const ctx = { repoRoot, qid, resume: true, dryRun: false } as PipelineContext;
  const state = createVerifyInitialState(qid, {
    phase: "formalization", source: { input: "paper.tex", main_file: "paper.tex", sha256: "0".repeat(64) },
    targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 1, findings: [], report_path: null,
  });
  state.lean_subdir = "Papers/UserPaper";
  const paths = artifactPaths(ctx, state);
  await mkdir(paths.leanDir, { recursive: true });
  await mkdir(path.join(paths.formalizationDir, "discovery"), { recursive: true });
  const prompts = path.join(repoRoot, "tools", "src", "formalization", "prompts", "F5");
  await mkdir(prompts, { recursive: true });
  for (const f of ["stage5_proof_english.txt", "stage5_proof_english_review.txt", "stage5_proof_compare.txt"]) await copyFile(path.join(PROMPTS, f), path.join(prompts, f));
  await writeFile(path.join(paths.leanDir, "Parts.lean"), LEAN);
  let g = createEmptyGraph(qid);
  for (const [id, decl, statement] of [["thm:main", "main_result", "If $x>0$ then $x^2>0$."], ["thm:second", "second_result", "$\\mathrm{sq}(x)=x x$."]] as const) {
    g = addNode(g, { id, kind: "theorem", provenance: "from-note", nl_statement: statement, tex_anchor: "" });
    g = setLean(g, id, `Papers.UserPaper.${decl}`, "Parts.lean");
  }
  await saveGraph(graphPath(paths.formalizationDir), g);
  const core = {
    qid, cluster: "stat", symbols: [], assumptions: [], definitions: [], target_estimand: "", bibliography: [],
    statements: [
      { id: "thm:main", kind: "theorem", statement: "If $x>0$ then $x^2>0$.", depends_on: ["lem:cited"], status: "to-prove", proof_tex: "We have $x^2 = x + x$, which is positive." },
      { id: "thm:second", kind: "theorem", statement: "$\\mathrm{sq}(x)=x x$.", depends_on: [], status: "to-prove" },
      { id: "lem:cited", kind: "lemma", statement: "Products of positives are positive.", depends_on: [], status: "cited", source: { cite: "Smith 2010", locator: "Thm 3" } },
    ],
  };
  await writeFile(path.join(paths.formalizationDir, "discovery", "core.json"), JSON.stringify(core));
  return { ctx, state, paths };
}

/** A stub of the three calls. `reviewSecond`: whether the review of a rewrite answers; `stubborn`: thm:main
 *  stays unfaithful; `regress`: A1's revision is found unfaithful; `dropFirstReview`: the first review call fails. */
function stub(calls: string[], opts: { reviewSecond: boolean; stubborn?: boolean; regress?: boolean; dropFirstReview?: boolean }) {
  const reviewed = new Set<string>();
  let dropped = false;
  const entry = (id: string, rewrite: boolean) => {
    if (id === "thm:main") return { id, statement: null, proof: `By ⟦A1⟧ and ⟦lem:cited⟧, $x^2$ is the square of $x$, [positive](lean:${lineOf("exact sq_pos_aux")}) since [${rewrite ? "for $x>0$" : "for $x\\ge 0$"} a product of positives is positive](lean:${lineOf("  positivity")}).` };
    if (id === "thm:second") return { id, statement: null, proof: `[Rewrite with ⟦A1⟧](lean:${lineOf("rw [shared_step]")}).` };
    return { id, statement: "For every $x$, $\\mathrm{sq}(x) = x^2$.", proof: `[Unfold and expand](lean:${lineOf("unfold sq; ring")}).` };
  };
  return { runCodex: async ({ prompt }: { prompt: string }) => {
    const ids = [...prompt.matchAll(/^### ⟦([^⟧]+)⟧/gm)].map((m) => m[1]!);
    if (prompt.includes("You are auditing the Lean Proof in English")) {
      if (opts.dropFirstReview && !dropped) { dropped = true; calls.push("review dropped"); return { stdout: "{}", stderr: "" }; }
      // the first review of an account finds its defect (thm:main: the hypothesis; A1: a reader's note); a rewrite's is clean
      const rewrite = ids.some((id) => reviewed.has(id));
      ids.forEach((id) => reviewed.add(id));
      calls.push(rewrite ? "review rewrite" : "review");
      if (rewrite && !opts.reviewSecond) return { stdout: "{}", stderr: "" };
      return { stdout: JSON.stringify({ reviews: ids.map((id) => ((!rewrite || opts.stubborn) && id === "thm:main" ? { id, faithful: false, issues: ["the hypothesis: Lean assumes x > 0"], readability: [] } : !rewrite && id === "A1" ? { id, faithful: true, issues: [], readability: ["sq is not defined where it is used"] } : rewrite && opts.regress && id === "A1" ? { id, faithful: false, issues: ["the revision drops x"], readability: [] } : { id, faithful: true, issues: [], readability: [] })) }), stderr: "" };
    }
    if (prompt.includes("You are checking a paper's printed proofs")) {
      calls.push("compare");
      return { stdout: JSON.stringify({ results: [{ id: "thm:main", summary: "Lean squares, the paper doubles.", differences: [{ printed: "$x^2 = x + x$", lean: "$x^2 = x\\cdot x$", kind: "error", missing: false, suggestion: "$x^2 = x \\cdot x$", reason: "Lean writes the square as a product." }] }] }), stderr: "" };
    }
    const rewrite = prompt.includes("A review of your earlier text against the Lean found");
    // a rewrite is a revision: it is shown its earlier text
    if (rewrite && ids.includes("thm:main") && !prompt.includes("YOUR EARLIER TEXT:") ) throw new Error("the rewrite is not shown its earlier text");
    calls.push(rewrite ? "rewrite" : "english");
    // the translator is never shown a printed proof, and is told the cited result it may cite and the helper it proves inside
    if (prompt.includes("x + x")) throw new Error("the translator was shown a printed proof");
    if (ids.includes("thm:main") && !prompt.includes("⟦lem:cited⟧ lemma — cited from Smith 2010, Thm 3")) throw new Error("the cited result is not offered");
    if (ids.includes("thm:main") && !prompt.includes("Lean `Papers.UserPaper.sq_pos_aux` (lemma)")) throw new Error("the helper is not listed");
    return { stdout: JSON.stringify({ entries: ids.map((id) => entry(id, rewrite)) }), stderr: "" };
  } } as unknown as StageDeps;
}

describe("emitLeanProofEnglish", () => {
  it("writes, reviews (an account with a defect revised), compares, and stores what the page draws", async () => {
    const { ctx, state, paths } = await seed();
    const calls: string[] = [];
    vi.spyOn(console, "log").mockImplementation(() => {});
    const summary = await emitLeanProofEnglish({ ctx, state, deps: stub(calls, { reviewSecond: true }) });
    const n = (k: string) => calls.filter((c) => c === k).length;
    // three accounts (two results, one shared lemma); thm:main (unfaithful) and A1 (a readability note) written again
    expect([n("english"), n("review"), n("rewrite"), n("review rewrite"), n("compare")]).toEqual([3, 3, 2, 2, 1]);
    expect(summary).toContain("2/2 result(s) written in English (1 helper(s) proved inside them, 1/1 shared lemma(s); 3 call(s))");
    expect(summary).toContain("none found unfaithful");
    expect(summary).toContain("departs 1");
    const stored = JSON.parse(await readFile(path.join(paths.formalizationDir, LEAN_PROOF_ENGLISH_ARTIFACT), "utf8")) as LeanProofEnglish;
    const main = stored.results.find((r) => r.id === "thm:main")!;
    expect(main.proof).toContain("x>0");
    expect(main.review).toEqual({ faithful: true, issues: [], readability: [], rewritten: true });
    expect(main.inline?.map((d) => d.decl)).toEqual(["Papers.UserPaper.sq_pos_aux"]);
    expect(main.aux).toEqual(["A1"]);
    // no verify run here: nothing to correct, the departure reported unplaced
    expect(main.comparison?.verdict).toBe("departs");
    expect(main.comparison?.departures.map((d) => [d.kind, d.placed])).toEqual([["printed-wrong", false]]);
    expect(stored.refs["lem:cited"]).toEqual({ kind: "lemma", label: null });
    expect(stored.results.find((r) => r.id === "thm:second")!.no_printed_proof).toBe(true);
    // a readability note alone sends a faithful account back once too
    expect(stored.auxiliary.map((a) => [a.id, a.review?.rewritten])).toEqual([["A1", true]]);
    const view = leanProofView(stored, "thm:main")!;
    expect(view.aux.map((a) => a.id)).toEqual(["A1"]);
    expect(view.proof.lean.source).toContain("theorem main_result");
    expect(view.proof.lean.inline?.[0]?.source).toContain("lemma sq_pos_aux");
  });

  it("an account with a defect left is revised up to three times, then shown with its last review", async () => {
    const { ctx, state, paths } = await seed();
    const calls: string[] = [];
    vi.spyOn(console, "log").mockImplementation(() => {});
    await emitLeanProofEnglish({ ctx, state, deps: stub(calls, { reviewSecond: true, stubborn: true }) });
    const n = (k: string) => calls.filter((c) => c === k).length;
    // thm:main three revisions (each reviewed); A1 one, its reader's note gone after it
    expect([n("rewrite"), n("review rewrite")]).toEqual([4, 4]);
    const stored = JSON.parse(await readFile(path.join(paths.formalizationDir, LEAN_PROOF_ENGLISH_ARTIFACT), "utf8")) as LeanProofEnglish;
    expect(stored.results.find((r) => r.id === "thm:main")!.review).toMatchObject({ faithful: false, rewritten: true });
    expect(stored.auxiliary[0]!.review).toMatchObject({ faithful: true, rewritten: true });
  });

  it("a rewrite whose review does not answer is shown as not reviewed, not under the first review's issues", async () => {
    const { ctx, state, paths } = await seed();
    vi.spyOn(console, "log").mockImplementation(() => {});
    const summary = await emitLeanProofEnglish({ ctx, state, deps: stub([], { reviewSecond: false }) });
    // thm:main (unfaithful) written again; A1's revision (for a readability note) unreviewed, so its faithful text stands
    expect(summary).toContain("1 not reviewed");
    // an account not confirmed faithful is not compared
    expect(summary).toContain("compared 0 (1 not compared: English not confirmed faithful)");
    const stored = JSON.parse(await readFile(path.join(paths.formalizationDir, LEAN_PROOF_ENGLISH_ARTIFACT), "utf8")) as LeanProofEnglish;
    expect(stored.results.find((r) => r.id === "thm:main")!.review).toBeNull();
    expect(stored.auxiliary[0]!.review).toEqual({ faithful: true, issues: [], readability: ["sq is not defined where it is used"] });
  });

  it("a revision for the reader found unfaithful gives way to the faithful text it revised, revised no more", async () => {
    const { ctx, state, paths } = await seed();
    const calls: string[] = [];
    vi.spyOn(console, "log").mockImplementation(() => {});
    await emitLeanProofEnglish({ ctx, state, deps: stub(calls, { reviewSecond: true, regress: true }) });
    const stored = JSON.parse(await readFile(path.join(paths.formalizationDir, LEAN_PROOF_ENGLISH_ARTIFACT), "utf8")) as LeanProofEnglish;
    const a1 = stored.auxiliary[0]!;
    expect(a1.review).toEqual({ faithful: true, issues: [], readability: ["sq is not defined where it is used"] });
    expect(a1.statement).toBe("For every $x$, $\\mathrm{sq}(x) = x^2$.");
    expect(stored.problems.some((p) => p.includes("the revision of A1 was not confirmed faithful; the earlier faithful text stands"))).toBe(true);
    // thm:main and A1 revised once each; nothing after
    expect(calls.filter((c) => c === "rewrite")).toHaveLength(2);
    expect(stored.results.find((r) => r.id === "thm:main")!.comparison?.verdict).toBe("departs");
  });

  it("a review call that fails is asked once more", async () => {
    const { ctx, state, paths } = await seed();
    const calls: string[] = [];
    vi.spyOn(console, "log").mockImplementation(() => {});
    const summary = await emitLeanProofEnglish({ ctx, state, deps: stub(calls, { reviewSecond: true, dropFirstReview: true }) });
    expect(calls).toContain("review dropped");
    expect(summary).not.toContain("not reviewed");
    const stored = JSON.parse(await readFile(path.join(paths.formalizationDir, LEAN_PROOF_ENGLISH_ARTIFACT), "utf8")) as LeanProofEnglish;
    expect(stored.problems.filter((p) => p.includes("no review of"))).toEqual([]);
    expect([...stored.results, ...stored.auxiliary].every((p) => p.review)).toBe(true);
  });

  it("only: a name of no result with a Lean proof leaves the artifact as it is", async () => {
    const { ctx, state, paths } = await seed();
    vi.spyOn(console, "log").mockImplementation(() => {});
    await emitLeanProofEnglish({ ctx, state, deps: stub([], { reviewSecond: true }) });
    const file = path.join(paths.formalizationDir, LEAN_PROOF_ENGLISH_ARTIFACT);
    const before = await readFile(file, "utf8");
    await expect(emitLeanProofEnglish({ ctx, state, deps: stub([], { reviewSecond: true }), only: new Set(["thm:mian"]) })).rejects.toThrow("thm:mian: no paper result with a Lean proof");
    expect(await readFile(file, "utf8")).toBe(before);
  });

  it("a step that fails writes the artifact with the problem, never a throw; a run with no result replaces an earlier artifact", async () => {
    const { ctx, state, paths } = await seed();
    vi.spyOn(console, "log").mockImplementation(() => {});
    await writeFile(path.join(paths.formalizationDir, "discovery", "patches.json"), "{ not json");
    const summary = await emitLeanProofEnglish({ ctx, state, deps: stub([], { reviewSecond: true }) });
    expect(summary).toContain("problem(s)");
    const stored = JSON.parse(await readFile(path.join(paths.formalizationDir, LEAN_PROOF_ENGLISH_ARTIFACT), "utf8")) as LeanProofEnglish;
    expect(stored.problems.some((p) => p.startsWith("compare:"))).toBe(true);
    expect(stored.results.find((r) => r.id === "thm:main")!.proof).toBeTruthy();
    // no result left: the file says so
    await saveGraph(graphPath(paths.formalizationDir), createEmptyGraph("user_paper"));
    expect(await emitLeanProofEnglish({ ctx, state, deps: stub([], { reviewSecond: true }) })).toContain("no paper result");
    expect((JSON.parse(await readFile(path.join(paths.formalizationDir, LEAN_PROOF_ENGLISH_ARTIFACT), "utf8")) as LeanProofEnglish).results).toEqual([]);
  });
});
