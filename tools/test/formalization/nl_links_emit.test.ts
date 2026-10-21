// F5's link step end to end, the model stubbed: what it asks (the rows of a theorem stated through
// `type_of% @name` included), how it survives a bad reply, and what it writes — per result the
// links, the key of the statement they were cut from and what was measured; for the run a summary
// with its warnings. The page then puts those links on the very rows that were asked.
import { createHash } from "node:crypto";
import { copyFile, mkdir, mkdtemp, readFile, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it, vi } from "vitest";
import { collectItems, emitNlLinks, leanStatementView, NL_LINKS_ARTIFACT, declSource, viewRows, type StoredResult } from "../../src/formalization/nl_links.js";
import { propDeclView } from "../../src/formalization/lean_rows.js";
import { artifactPaths, type StageDeps } from "../../src/pipeline_support.js";
import { createEmptyGraph, graphPath, loadGraph, saveGraph } from "../../src/graph/store.js";
import { addNode, setLean } from "../../src/graph/mutate.js";
import { createVerifyInitialState } from "../../src/state.js";
import type { PipelineContext } from "../../src/types.js";
import { applyLinks, eachRow, leanDefs, type PageView } from "../../src/ui/lean_view.js";

const PROMPTS = path.join(__dirname, "..", "..", "src", "formalization", "prompts", "F5");

async function seed() {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "nl-links-emit-"));
  const qid = "user_paper";
  const ctx = { repoRoot, qid, resume: true, dryRun: false } as PipelineContext;
  const state = createVerifyInitialState(qid, {
    phase: "formalization", source: { input: "paper.tex", main_file: "paper.tex", sha256: "0".repeat(64) },
    targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 1, findings: [], report_path: null,
  });
  state.lean_subdir = "Papers/UserPaper";
  const paths = artifactPaths(ctx, state);
  await mkdir(paths.leanDir, { recursive: true });
  await mkdir(paths.formalizationDir, { recursive: true });
  const prompts = path.join(repoRoot, "tools", "src", "formalization", "prompts", "F5");
  await mkdir(prompts, { recursive: true });
  for (const f of ["stage5_nl_links.txt", "stage5_nl_links_verify.txt"]) await copyFile(path.join(PROMPTS, f), path.join(prompts, f));
  await writeFile(path.join(paths.leanDir, "Parts.lean"), [
    "namespace Papers.UserPaper", "",
    "theorem ral_part {n : ℕ} (hn : 0 < n) : A n ∧ (∀ m, m < n → B m) := by", "  sorry", "",
    "theorem boot : (type_of% @ral_part) ∧ C := by", "  sorry", "",
    "theorem plain (x : ℕ) (hx : 0 < x) : D x := by", "  sorry", "",
    "end Papers.UserPaper", "",
  ].join("\n"));
  let g = createEmptyGraph(qid);
  const node = (id: string, decl: string, statement: string) => {
    g = addNode(g, { id, kind: "theorem", provenance: "from-note", nl_statement: statement, tex_anchor: "" });
    g = setLean(g, id, `Papers.UserPaper.${decl}`, "Parts.lean");
  };
  node("thm:boot", "boot", String.raw`Suppose $n>0$. Then $A_n$ holds, $B_m$ holds for $m<n$, and $C$ holds.`);
  node("thm:plain", "plain", String.raw`If $x>0$ then $D_x$.`);
  await saveGraph(graphPath(paths.formalizationDir), g);
  return { repoRoot, ctx, state, paths };
}

/** The rows a prompt asks, by result. */
const asked = (prompt: string): Map<string, string[]> => {
  const out = new Map<string, string[]>();
  for (const block of prompt.split(/^## /m).slice(1)) {
    const id = block.split(" ")[0]!;
    out.set(id, [...block.split("Lean rows:\n")[1]!.split("\n\n")[0]!.matchAll(/^  (\S+): /gm)].map((m) => m[1]!));
  }
  return out;
};

describe("emitNlLinks", () => {
  // The finding this guards: a re-link asked every result of every paper again from nothing — both
  // calls — though neither its statement, its Lean nor the prompts had changed.
  it("links again only what changed: the same basis keeps the links without a call, a changed prompt revises them by the audit alone, --fresh starts over", async () => {
    const { repoRoot, ctx, state, paths } = await seed();
    const prompts: string[] = [];
    const deps = { runCodex: async ({ prompt }: { prompt: string }) => {
      prompts.push(prompt);
      const rows = asked(prompt);
      const results = [...rows].map(([obj_id, ids]) => ({ obj_id, uncovered: [], rows: ids.map((row, k) => (row === "r2" && obj_id === "thm:boot" ? { row, segments: [], unstated: true } : { row, segments: [obj_id === "thm:boot" ? `s${(k % 2) + 1}` : "s1"], unstated: false })) }));
      return { stdout: JSON.stringify({ results, changes: [] }), stderr: "" };
    } } as unknown as StageDeps;
    const log = vi.spyOn(console, "log").mockImplementation(() => {});
    const file = path.join(paths.formalizationDir, NL_LINKS_ARTIFACT);
    await emitNlLinks({ ctx, state, deps });
    expect(prompts).toHaveLength(2);
    const first = await readFile(file, "utf8");
    expect(JSON.parse(first).results.every((r: { basis?: string }) => /^[0-9a-f]{16}$/.test(r.basis ?? ""))).toBe(true);

    // nothing changed: no call, the file as it was
    expect(await emitNlLinks({ ctx, state, deps })).toContain("(2 kept as linked)");
    expect(prompts).toHaveLength(2);
    expect(JSON.parse(await readFile(file, "utf8")).results).toEqual(JSON.parse(first).results);

    // a prompt changed: the links on file go to the audit as its proposal, no assign call
    const verify = path.join(repoRoot, "tools", "src", "formalization", "prompts", "F5", "stage5_nl_links_verify.txt");
    await writeFile(verify, (await readFile(verify, "utf8")) + "\n");
    expect(await emitNlLinks({ ctx, state, deps })).toContain("(2 revised from the links on file)");
    expect(prompts).toHaveLength(3);
    expect(prompts[2]).toContain("Proposed assignment:");

    // one result's statement changed: it alone is linked from nothing, the other kept
    const g = await loadGraph(graphPath(paths.formalizationDir));
    g.nodes.find((n) => n.id === "thm:plain")!.nl!.statement = String.raw`If $x>0$ then $D_x$ holds.`;
    await saveGraph(graphPath(paths.formalizationDir), g);
    expect(await emitNlLinks({ ctx, state, deps })).toContain("(1 kept as linked)");
    expect(prompts).toHaveLength(5);
    expect([...asked(prompts[3]!).keys()]).toEqual(["thm:plain"]);
    expect(prompts[3]).not.toContain("Proposed assignment:");

    // an audit call that fails settles nothing: the links are stored without a basis and revised next time
    const failing = { runCodex: async (a: { prompt: string }) => { if (a.prompt.includes("Proposed assignment:")) { prompts.push(a.prompt); throw new Error("timeout"); } return (deps as unknown as { runCodex: (x: { prompt: string }) => Promise<unknown> }).runCodex(a); } } as unknown as StageDeps;
    await emitNlLinks({ ctx, state, deps: failing, fresh: true });
    expect(prompts).toHaveLength(7);
    expect(JSON.parse(await readFile(file, "utf8")).results.map((r: { basis?: string }) => r.basis)).toEqual([undefined, undefined]);
    expect(await emitNlLinks({ ctx, state, deps })).toContain("(2 revised from the links on file)");
    expect(prompts).toHaveLength(8);
    expect(JSON.parse(await readFile(file, "utf8")).results.every((r: { basis?: string }) => !!r.basis)).toBe(true);

    await emitNlLinks({ ctx, state, deps, fresh: true });
    expect(prompts).toHaveLength(10);
    expect([...asked(prompts[8]!).keys()].sort()).toEqual(["thm:boot", "thm:plain"]);
    log.mockRestore();
  });
  it("asks the rows of the named theorem, writes links under the statement's key with what was measured — and the page puts them on those rows", async () => {
    const { repoRoot, ctx, state, paths } = await seed();
    const prompts: string[] = [];
    const deps = { runCodex: async ({ prompt }: { prompt: string }) => {
      prompts.push(prompt);
      const rows = asked(prompt);
      const results = [...rows].map(([obj_id, ids]) => ({ obj_id, uncovered: [], rows: ids.map((row, k) => (row === "r2" && obj_id === "thm:boot" ? { row, segments: [], unstated: true } : { row, segments: [obj_id === "thm:boot" ? `s${(k % 2) + 1}` : "s1"], unstated: false })) }));
      return { stdout: JSON.stringify({ results, changes: [] }), stderr: "" };
    } } as unknown as StageDeps;
    const log = vi.spyOn(console, "log").mockImplementation(() => {});
    const summary = await emitNlLinks({ ctx, state, deps });
    const lines = log.mock.calls.map((c) => String(c[0]));
    log.mockRestore();

    // one assign call and one verify call; the theorem stated through `type_of%` is asked row by row
    expect(prompts).toHaveLength(2);
    expect(asked(prompts[0]!).get("thm:boot")).toEqual(["r1/r1", "r1/r2", "r1/r3", "r1/r4", "r1/r5", "r1/r6", "r2"]);
    expect(prompts[0]).toContain("  r1/r5: m < n");
    expect(prompts[0]).not.toContain("type_of%");
    expect(prompts[1]).toContain("Proposed assignment:");

    const nl = JSON.parse(await readFile(path.join(paths.formalizationDir, NL_LINKS_ARTIFACT), "utf8"));
    // no version tag: each result's `key` says which statement its links are for
    expect(Object.keys(nl).sort()).toEqual(["changes", "problems", "results", "summary", "unlinked"]);
    expect(nl.unlinked).toEqual([]);
    const boot = nl.results.find((r: { node: string }) => r.node === "thm:boot");
    expect(boot.key).toMatch(/^[0-9a-f]{40}$/);
    expect(boot.metrics).toEqual({ asked: 7, linked: 6, unstated: 1, unanswered: 0, unique: 0, max_segments: 1, shared: 0 });
    expect(nl.summary).toMatchObject({ results: 2, of: 2, rows: { asked: 10, linked: 9, unstated: 1, unanswered: 0, shared: 0 } });
    // few rows with a list of their own: the run is told
    expect(nl.summary.warnings).toEqual([expect.stringMatching(/^only \d+% of the linked rows have a segment list of their own$/)]);
    expect(summary).toMatch(/^2\/2 result\(s\) linked row by row; rows asked 10, linked 9, unstated 1; lists of their own \d+%; WARNING: only/);
    expect(lines).toContainEqual(expect.stringMatching(/^\[paperformalizer\] F5 nl-links thm:boot: rows asked 7, linked 6, unstated 1, unanswered 0; lists of their own 0%, most segments on a row 1$/));

    // the page: the same rows, each with the link F5 gave it
    const source = declSource(await readFile(path.join(paths.leanDir, "Parts.lean"), "utf8"), "Papers.UserPaper.boot")!;
    const view = leanStatementView(source) as PageView;
    await leanDefs(repoRoot, paths.leanDir).annotate(view, "Parts.lean", "Papers.UserPaper.boot");
    expect(applyLinks(view, boot.rows, boot.key)).toBe(true);
    const got: string[] = [];
    eachRow(view, (row, content) => got.push(`${row.id} ${content} | ${row.xl ?? (row.unstated ? "unstated" : "")}${row.coarse ? " ~" : ""}`));
    expect(got).toEqual(["r1/r1 {n : ℕ} | s1", "r1/r2 (hn : 0 < n) | s2", "r1/r3 A n | s1", "r1/r4 ∀ m | s2", "r1/r5 m < n | s1", "r1/r6 B m | s2", "r2 C | unstated"]);
    // the named theorem edited since: the links are another statement's
    await writeFile(path.join(paths.leanDir, "Parts.lean"), (await readFile(path.join(paths.leanDir, "Parts.lean"), "utf8")).replace("A n ∧", "A (n + 1) ∧"));
    const edited = leanStatementView(source) as PageView;
    await leanDefs(repoRoot, paths.leanDir).annotate(edited, "Parts.lean", "Papers.UserPaper.boot");
    expect(applyLinks(edited, boot.rows, boot.key)).toBe(false);
  });

  it("a result answered with a blanket list is asked again alone; rows still under one are stored as such and the run warned", async () => {
    const { ctx, state, paths } = await seed();
    const labels: string[] = [];
    const deps = { runCodex: async ({ prompt }: { prompt: string }) => {
      const rows = asked(prompt);
      labels.push(`${prompt.startsWith("You are auditing") ? "verify" : prompt.includes("not accepted") ? "again" : "assign"} ${[...rows.keys()].join("+")}`);
      // thm:boot: every row the same three segments, whatever is asked; thm:plain: one row unanswered at first
      const results = [...rows].map(([obj_id, ids]) => ({ obj_id, uncovered: [], rows: (obj_id === "thm:plain" && !prompt.includes("not accepted") ? ids.slice(1) : ids).map((row) => ({ row, segments: obj_id === "thm:boot" ? ["s1", "s2", "s3"] : ["s1"], unstated: false })) }));
      return { stdout: JSON.stringify({ results, changes: [] }), stderr: "" };
    } } as unknown as StageDeps;
    const log = vi.spyOn(console, "log").mockImplementation(() => {});
    const summary = await emitNlLinks({ ctx, state, deps });
    log.mockRestore();
    expect(labels).toEqual(["assign thm:boot+thm:plain", "again thm:boot", "again thm:plain", "verify thm:boot+thm:plain"]);
    const nl = JSON.parse(await readFile(path.join(paths.formalizationDir, NL_LINKS_ARTIFACT), "utf8"));
    const boot = nl.results.find((r: { node: string }) => r.node === "thm:boot");
    expect(boot.rows.every((r: { coarse?: boolean }) => r.coarse === true)).toBe(true);
    expect(boot.metrics).toMatchObject({ shared: 7, unique: 0, max_segments: 3 });
    expect(nl.results.find((r: { node: string }) => r.node === "thm:plain").rows.every((r: { coarse?: boolean }) => r.coarse === undefined)).toBe(true);
    expect(nl.summary.warnings[0]).toBe("7 row(s) under a list shared by more rows than their result allows (thm:boot)");
    expect(nl.problems.map((p: string) => p.replace(/rows r1\/r1.*?carry/g, "rows … carry").replace(/: give each[^()]*?(?= \(|\)|$)/g, ""))).toEqual([
      "thm:boot: rows … carry one identical list of segments (asked again: answered; rows … carry one identical list of segments)",
      "thm:plain: rows not answered: r1 (asked again: answered)",
      "verify thm:boot: rows … carry one identical list of segments (assignment kept)",
      "verify thm:plain: rows not answered: r1 (assignment kept)",
    ]);
    expect(summary).toContain("WARNING: 7 row(s) under a list shared by more rows than their result allows (thm:boot)");
  });

  // The finding this guards: `replaceAll("{{items}}", block)` read `$$`, `$'`, `$&` in the paper's
  // TeX as replacement patterns — `$$ a = b $$` was sent as `$ a = b $`, and a `$'` spliced the
  // rest of the template (the proposed assignment) into a segment.
  it("sends the paper's text verbatim: `$$`, `$'` and `$&` reach the model as written", async () => {
    const { ctx, state, paths } = await seed();
    let g = createEmptyGraph("user_paper");
    g = addNode(g, { id: "thm:plain", kind: "theorem", provenance: "from-note", nl_statement: String.raw`If $x>0$ then $$ D_x = x $$ holds under $\beta$'s law, at cost 5\$& more.`, tex_anchor: "" });
    g = setLean(g, "thm:plain", "Papers.UserPaper.plain", "Parts.lean");
    await saveGraph(graphPath(paths.formalizationDir), g);
    const prompts: string[] = [];
    const deps = { runCodex: async ({ prompt }: { prompt: string }) => {
      prompts.push(prompt);
      const results = [...asked(prompt)].map(([obj_id, ids]) => ({ obj_id, uncovered: [], rows: ids.map((row, k) => ({ row, segments: [`s${(k % 2) + 1}`], unstated: false })) }));
      return { stdout: JSON.stringify({ results, changes: [] }), stderr: "" };
    } } as unknown as StageDeps;
    const log = vi.spyOn(console, "log").mockImplementation(() => {});
    await emitNlLinks({ ctx, state, deps });
    log.mockRestore();
    const nl = JSON.parse(await readFile(path.join(paths.formalizationDir, NL_LINKS_ARTIFACT), "utf8"));
    const lines = nl.results[0].segments.map((s: { id: string; text: string }) => `  ${s.id}: ${s.text.replace(/\s+/g, " ").trim()}`);
    expect(lines.join("\n")).toContain("$$ D_x = x $$");
    for (const p of prompts) for (const line of lines) expect(p).toContain(line);
    // the verify prompt holds the proposed assignment once, after its own heading
    expect(prompts[1]!.split("Proposed assignment:")).toHaveLength(2);
  });

  // The finding this guards: one thrown model call lost the links of the whole run (no file written).
  it("a call that throws is a call with no answer: its results are asked again alone, the rest kept, the file always written", async () => {
    const { ctx, state, paths } = await seed();
    const labels: string[] = [];
    const deps = { runCodex: async ({ prompt }: { prompt: string }) => {
      const rows = asked(prompt);
      const kind = prompt.startsWith("You are auditing") ? "verify" : prompt.includes("not accepted") ? "again" : "assign";
      labels.push(`${kind} ${[...rows.keys()].join("+")}`);
      if (kind === "assign" || (kind === "again" && rows.has("thm:plain"))) throw new Error("codex exec timed out after 1800s");
      const results = [...rows].map(([obj_id, ids]) => ({ obj_id, uncovered: [], rows: ids.map((row, k) => ({ row, segments: [`s${(k % 2) + 1}`], unstated: false })) }));
      return { stdout: JSON.stringify({ results, changes: [] }), stderr: "" };
    } } as unknown as StageDeps;
    const log = vi.spyOn(console, "log").mockImplementation(() => {});
    const summary = await emitNlLinks({ ctx, state, deps });
    log.mockRestore();
    expect(labels).toEqual(["assign thm:boot+thm:plain", "again thm:boot", "again thm:plain", "verify thm:boot"]);
    const nl = JSON.parse(await readFile(path.join(paths.formalizationDir, NL_LINKS_ARTIFACT), "utf8"));
    const plain = nl.results.find((r: { node: string }) => r.node === "thm:plain");
    // the result no call answered is stored with its rows, none linked, and named in the warnings
    expect(plain).toMatchObject({ unanswered: true, metrics: { asked: 3, linked: 0, unanswered: 3 } });
    expect(nl.results.find((r: { node: string }) => r.node === "thm:boot").metrics.linked).toBe(7);
    expect(nl.unlinked).toEqual(["thm:plain"]);
    expect(nl.problems.filter((p: string) => p.includes("the call failed (codex exec timed out after 1800s)"))).toHaveLength(2);
    expect(summary).toMatch(/^1\/2 result\(s\) linked row by row.*WARNING: not linked: thm:plain/);
  });

  // The finding this guards: names bound by a section's `variable` (`(ν : Measure Ω)
  // [IsProbabilityMeasure ν]`) were in no row: a real hypothesis invisible to F5 and the reviewer.
  it("asks the section variables the statement takes as rows of their own, and the page draws those rows", async () => {
    const { repoRoot, ctx, state, paths } = await seed();
    await writeFile(path.join(paths.leanDir, "Parts.lean"), [
      "namespace Papers.UserPaper", "",
      "variable {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] (unused : ℕ)", "",
      "section", "variable (hν : Good ν)", "",
      "theorem plain (x : ℕ) (hx : 0 < x) : D x ν := by", "  sorry", "",
      "end", "",
      "theorem boot : C := by", "  sorry", "",
      "end Papers.UserPaper", "",
    ].join("\n"));
    const prompts: string[] = [];
    const deps = { runCodex: async ({ prompt }: { prompt: string }) => {
      prompts.push(prompt);
      const results = [...asked(prompt)].map(([obj_id, ids]) => ({ obj_id, uncovered: [], rows: ids.map((row, k) => ({ row, segments: [`s${(k % 2) + 1}`], unstated: false })) }));
      return { stdout: JSON.stringify({ results, changes: [] }), stderr: "" };
    } } as unknown as StageDeps;
    const log = vi.spyOn(console, "log").mockImplementation(() => {});
    await emitNlLinks({ ctx, state, deps });
    log.mockRestore();
    // `hν` is not mentioned: not taken; `unused` neither; the instance on ν is
    // (instance binders are Lean-only: not asked)
    expect(asked(prompts[0]!).get("thm:plain")).toEqual(["v1", "v3", "r1", "r2", "r3"]);
    expect(prompts[0]).toContain("  v1: Ω : Type*");
    expect(prompts[0]).toContain("  v3: ν : Measure Ω");
    const nl = JSON.parse(await readFile(path.join(paths.formalizationDir, NL_LINKS_ARTIFACT), "utf8"));
    const plain = nl.results.find((r: { node: string }) => r.node === "thm:plain");
    expect(plain.rows.filter((r: { section?: boolean }) => r.section).map((r: { id: string }) => r.id)).toEqual(["v1", "v2", "v3", "v4"]);
    // the page: the same rows, the section's first, each with its link
    const source = declSource(await readFile(path.join(paths.leanDir, "Parts.lean"), "utf8"), "Papers.UserPaper.plain")!;
    const view = leanStatementView(source) as PageView;
    await leanDefs(repoRoot, paths.leanDir).annotate(view, "Parts.lean", "Papers.UserPaper.plain");
    expect(applyLinks(view, plain.rows, plain.key)).toBe(true);
    const got: string[] = [];
    eachRow(view, (row, content) => got.push(`${row.id}${(row as { section?: boolean }).section ? " §" : ""} ${content}`));
    expect(got).toEqual(["v1 § {Ω : Type*}", "v2 § [MeasurableSpace Ω]", "v3 § (ν : Measure Ω)", "v4 § [IsProbabilityMeasure ν]", "r1 (x : ℕ)", "r2 (hx : 0 < x)", "r3 D x ν"]);
  });

  it("re-links only the results asked (`only`), keeping what is stored for the others", async () => {
    const { ctx, state, paths } = await seed();
    let round = 0;
    const deps = { runCodex: async ({ prompt }: { prompt: string }) => {
      const results = [...asked(prompt)].map(([obj_id, ids]) => ({ obj_id, uncovered: [], rows: ids.map((row, k) => ({ row, segments: [round === 0 ? "s1" : `s${(k % 2) + 1}`], unstated: false })) }));
      return { stdout: JSON.stringify({ results, changes: [] }), stderr: "" };
    } } as unknown as StageDeps;
    const log = vi.spyOn(console, "log").mockImplementation(() => {});
    await emitNlLinks({ ctx, state, deps });
    const first = JSON.parse(await readFile(path.join(paths.formalizationDir, NL_LINKS_ARTIFACT), "utf8"));
    round = 1;
    const summary = await emitNlLinks({ ctx, state, deps, only: new Set(["thm:plain"]) });
    log.mockRestore();
    const second = JSON.parse(await readFile(path.join(paths.formalizationDir, NL_LINKS_ARTIFACT), "utf8"));
    const by = (nl: { results: Array<{ node: string }> }, id: string) => nl.results.find((r) => r.node === id);
    expect(by(second, "thm:boot")).toEqual(by(first, "thm:boot"));
    expect(by(second, "thm:plain")).not.toEqual(by(first, "thm:plain"));
    expect(second.summary).toMatchObject({ results: 2, of: 2 });
    expect(summary).toMatch(/^2\/2 result\(s\) linked/);
  });

  // The finding this guards: only results were linked — an assumption's or a definition's drawer
  // showed its Lean with no word of the paper on it.
  it("links an assumption's and a definition's Prop-valued declaration under prompts of their own; a data-valued definition is no item and no warning; the results' links stand", async () => {
    const { repoRoot, ctx, state, paths } = await seed();
    const prompts: string[] = [];
    const deps = { runCodex: async ({ prompt }: { prompt: string }) => {
      prompts.push(prompt);
      const results = [...asked(prompt)].map(([obj_id, ids]) => ({ obj_id, uncovered: [], rows: ids.map((row, k) => (k === 0 ? { row, segments: [], unstated: true } : { row, segments: [obj_id === "thm:boot" ? `s${(k % 2) + 1}` : "s1"], unstated: false })) }));
      return { stdout: JSON.stringify({ results, changes: [] }), stderr: "" };
    } } as unknown as StageDeps;
    const log = vi.spyOn(console, "log").mockImplementation(() => {});
    const file = path.join(paths.formalizationDir, NL_LINKS_ARTIFACT);
    await emitNlLinks({ ctx, state, deps });
    const before = JSON.parse(await readFile(file, "utf8")).results as StoredResult[];
    // a result's basis is its key, its segments and the two prompts as they stand
    const tpl = { assign: (await readFile(path.join(PROMPTS, "stage5_nl_links.txt"), "utf8")).replace(/\r\n/g, "\n"), verify: (await readFile(path.join(PROMPTS, "stage5_nl_links_verify.txt"), "utf8")).replace(/\r\n/g, "\n") };
    const results = (await collectItems(ctx, state)).items;
    expect(before.map((r) => r.basis)).toEqual(results.map((it) => createHash("sha256").update(JSON.stringify([it.key, it.segments.map((x) => x.text), tpl.assign, tpl.verify])).digest("hex").slice(0, 16)));

    await copyFile(path.join(PROMPTS, "stage5_nl_links_declared.txt"), path.join(repoRoot, "tools", "src", "formalization", "prompts", "F5", "stage5_nl_links_declared.txt"));
    await writeFile(path.join(paths.leanDir, "Defs.lean"), [
      "namespace Papers.UserPaper", "",
      "-- @node: ass:mixing", "def Mixing (τ : ℕ) : Prop :=", "  0 < τ ∧ ∀ n, n < τ → A n", "",
      "structure Regular (n : ℕ) : Prop where", "  pos : 0 < n", "  small : n < 10", "",
      "noncomputable def rate (n : ℕ) : ℝ := 1", "",
      "end Papers.UserPaper", "",
    ].join("\n"));
    let g = await loadGraph(graphPath(paths.formalizationDir));
    for (const [id, kind, decl, statement] of [
      ["ass:mixing", "assumption", "Mixing", String.raw`The chain mixes in time $\tau>0$.`],
      ["def:regular", "definition", "Regular", String.raw`We call $n$ regular when $0<n<10$.`],
      ["def:rate", "definition", "rate", String.raw`The rate of $n$ is $1$.`],
    ] as const) {
      g = addNode(g, { id, kind, provenance: "from-note", nl_statement: statement, tex_anchor: "" });
      g = setLean(g, id, `Papers.UserPaper.${decl}`, "Defs.lean");
    }
    await saveGraph(graphPath(paths.formalizationDir), g);

    const { items, skipped } = await collectItems(ctx, state);
    expect(skipped).toEqual([]);
    expect(items.map((it) => [it.node, Boolean(it.declared)])).toEqual([["thm:boot", false], ["thm:plain", false], ["ass:mixing", true], ["def:regular", true]]);
    // the rows are the page's: the declaration's view, row for row, under its key
    const view = propDeclView((await readFile(path.join(paths.leanDir, "Defs.lean"), "utf8")).split("-- @node: ass:mixing\n")[1]!.split("\n\n")[0]!)!.view!;
    expect(items[2]).toMatchObject({ key: view.key, rows: viewRows(view) });
    expect(items[2]!.rows.map((r) => `${r.id} ${r.kind} ${r.names ? `${r.names} : ` : ""}${r.lean}`)).toEqual(["r1 binder τ : ℕ", "r2 conclusion Mixing τ : Prop", "r3 conclusion 0 < τ", "r4 premise ∀ n", "r5 premise n < τ", "r6 conclusion A n"]);
    expect(items[3]!.rows.map((r) => r.lean)).toEqual(["ℕ", "pos : 0 < n", "small : n < 10"]);

    // the results are kept without a call; the two declarations are asked together, the note before them
    prompts.length = 0;
    const summary = await emitNlLinks({ ctx, state, deps });
    expect(summary).toContain("(2 kept as linked)");
    expect(prompts).toHaveLength(2);
    for (const p of prompts) {
      expect([...asked(p).keys()]).toEqual(["ass:mixing", "def:regular"]);
      expect(p.indexOf("assumptions and definitions, not results")).toBeGreaterThan(0);
      expect(p.indexOf("assumptions and definitions, not results")).toBeLessThan(p.indexOf("## ass:mixing"));
    }
    const nl = JSON.parse(await readFile(file, "utf8"));
    expect(nl.unlinked).toEqual([]);
    expect(nl.summary.warnings.join(" ")).not.toMatch(/not linked|def:rate/);
    expect(nl.results.slice(0, 2)).toEqual(before);
    const mixing = nl.results.find((r: StoredResult) => r.node === "ass:mixing") as StoredResult;
    expect(mixing).toMatchObject({ key: view.key, decl: "Papers.UserPaper.Mixing", basis: expect.stringMatching(/^[0-9a-f]{16}$/) });
    expect(mixing.rows.map((r) => r.unstated || r.segments.join(" "))).toEqual([true, "s1", "s1", "s1", "s1", "s1"]);
    // their basis holds the note: kept at the next link, and one of them linked alone by `only`
    expect(await emitNlLinks({ ctx, state, deps })).toContain("(4 kept as linked)");
    expect(prompts).toHaveLength(2);
    await emitNlLinks({ ctx, state, deps, only: new Set(["def:regular"]) });
    expect(prompts).toHaveLength(4);
    expect([...asked(prompts[2]!).keys()]).toEqual(["def:regular"]);
    expect(JSON.parse(await readFile(file, "utf8")).results.map((r: StoredResult) => r.node).sort()).toEqual(["ass:mixing", "def:regular", "thm:boot", "thm:plain"]);
    log.mockRestore();
  });
});
