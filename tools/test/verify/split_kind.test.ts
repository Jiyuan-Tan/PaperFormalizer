/**
 * A block a repair splits off a result is one of two things, and its PROOF says which
 * (`core_graph.ts` `splitKind`): a corollary of the corrected result — its proof cites the result — or
 * a proposition, a separate claim the printed statement bundled in, resting on other results. The
 * kind is derived, never stored: the helper, the compiled dependency edge, the names a reader sees
 * (page, proof map, report, MATCH.md, corrected paper), what is shown of a core built before the
 * kinds were told apart, and the prompts' contract. No model call.
 */
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { readFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterAll, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { runDetail } from "../../src/ui/run_model.js";
import { renderPaper } from "../../src/ui/tex_html.js";
import { applyEdits as applyTexEdits, planAnnotations, type AnnotationInput } from "../../src/verify/annotated_paper.js";
import { VS_PREAMBLE_BLOCK, SPLIT_MACROS, splitMacroKind } from "../../src/verify/annotate_tex.js";
import { correctedTex } from "../../src/verify/corrected_tex.js";
import { buildCore, checkCoreInvariants, nodeFingerprint, splitCorollaryId, splitCount, splitKind, splitKinds, type PatchFileLike } from "../../src/verify/core_graph.js";
import { buildReport, type ReportRow } from "../../src/verify/report.js";
import { resultNames } from "../../src/verify/report_plain.js";
import { splitObjection } from "../../src/verify/stage_v1_5.js";

const BODY = "The estimator is normal; under a Gaussian design it is efficient; and the rate of Lemma~\\ref{lem:rate} is attained.";
/** thm:main (labelled) rests on lem:rate (labelled); thm:use uses thm:main. */
function core(): Core {
  return {
    qid: "kind_paper",
    symbols: [],
    assumptions: [{ id: "ass:gauss", condition: "the design is Gaussian", novel: { flag: true, justification: "Assumption 1" } }],
    definitions: [],
    statements: [
      { id: "lem:rate", kind: "lemma", statement: "the rate is $n^{-1/2}$", depends_on: [], status: "to-prove", tex_locator: { file: "main.tex", from: 6, to: 8, env: "lemma", label: "lem:rate" } },
      { id: "thm:main", kind: "theorem", statement: BODY, depends_on: [], status: "to-prove", tex_locator: { file: "main.tex", from: 3, to: 5, env: "theorem", label: "thm:main" } },
      { id: "thm:use", kind: "theorem", statement: "the interval covers", depends_on: ["thm:main"], status: "to-prove", tex_locator: { file: "main.tex", from: 9, to: 11, env: "theorem", label: "thm:use" } },
    ],
    target_estimand: "t",
    bibliography: [],
  } as unknown as Core;
}
/** A consequence of the corrected theorem: its proof cites it. */
const COR = { title: "the Gaussian case", statement: "If the design is Gaussian, the estimator is efficient.", follows: "Under a Gaussian design the limit variance of Theorem~\\ref{thm:main} is the information bound.", adds: ["ass:gauss"] };
/** A separate claim the printed theorem bundled in: its proof rests on the lemma alone (its STATEMENT names the theorem). */
const PROP = { title: "the rate", statement: "The estimator of Theorem~\\ref{thm:main} attains the rate $n^{-1/2}$.", follows: "This is Lemma~\\ref{lem:rate}." };
const COR_ID = splitCorollaryId("thm:main", COR.statement);
const PROP_ID = splitCorollaryId("thm:main", PROP.statement);
const patch = (corollaries: unknown[]) => ({ node: "thm:main", corrected_statement: "The estimator is normal.", proof_note: "The central limit theorem.", readings: ["normal means asymptotically normal"], corollaries });
const patches = (corollaries: unknown[] = [COR, PROP]): PatchFileLike => ({ key_results: [], patches: [patch(corollaries)], unfixable: [] }) as unknown as PatchFileLike;
/** The built core as it was before the kinds were told apart: every block wired to its parent. */
const oldEdge = (c: Core): Core => ({ ...c, statements: c.statements.map((s) => (s.split_from && !s.depends_on.includes(s.split_from) ? { ...s, depends_on: [s.split_from, ...s.depends_on] } : s)) }) as Core;

const tmp: string[] = [];
afterAll(() => {
  for (const d of tmp) rmSync(d, { recursive: true, force: true });
});

describe("the kind of a split-off block is read from its proof", () => {
  it("a corollary cites its parent's label in the proof (`\\ref` and its kin, a comma list); a proposition does not", () => {
    expect(splitKind("By Theorem~\\ref{thm:main}.", "thm:main")).toBe("corollary");
    expect(splitKind("By \\cref{lem:rate,thm:main} and \\eqref{eq:1}.", "thm:main")).toBe("corollary");
    expect(splitKind("By \\Cref{thm:main}.", "thm:main")).toBe("corollary");
    expect(splitKind("By Lemma~\\ref{lem:rate}.", "thm:main")).toBe("proposition");
    expect(splitKind("By \\ref{thm:main2}.", "thm:main")).toBe("proposition");
    expect(splitKind("", "thm:main")).toBe("proposition");
    expect(splitKind(null, "thm:main")).toBe("proposition");
  });

  it("a citation in a comment cites nothing, and the statement decides nothing: the proof does", () => {
    expect(splitKind("By Lemma~\\ref{lem:rate}. % not Theorem~\\ref{thm:main}", "thm:main")).toBe("proposition");
    expect(splitKind("A rate of 5\\% holds by \\ref{thm:main}.", "thm:main")).toBe("corollary");
    const c = buildCore(core(), { patches: patches() }).core;
    // PROP's statement names the theorem, its proof does not
    expect(splitKinds(c)).toEqual(new Map([[COR_ID, "corollary"], [PROP_ID, "proposition"]]));
  });

  it("a parent without a label can be cited by nothing: its blocks are corollaries (the edge is kept)", () => {
    expect(splitKind("By Lemma~\\ref{lem:rate}.", undefined)).toBe("corollary");
    expect(splitKind("By Lemma~\\ref{lem:rate}.", null)).toBe("corollary");
    expect(splitKind("By Lemma~\\ref{lem:rate}.", " ")).toBe("corollary");
    const bare = core();
    delete (bare.statements[1] as { tex_locator?: unknown }).tex_locator;
    const c = buildCore(bare, { patches: patches([PROP]) }).core;
    expect(c.statements.find((s) => s.id === PROP_ID)!.depends_on).toContain("thm:main");
    expect(splitKinds(c).get(PROP_ID)).toBe("corollary");
  });

  it("counts in words, by kind", () => {
    expect(splitCount(["corollary"])).toBe("1 corollary");
    expect(splitCount(["proposition", "proposition"])).toBe("2 propositions");
    expect(splitCount(["corollary", "proposition", "corollary"])).toBe("2 corollaries and 1 proposition");
  });
});

describe("the build: only a corollary depends on its parent", () => {
  const c = buildCore(core(), { patches: patches() }).core;
  const st = (id: string) => c.statements.find((s) => s.id === id)!;

  it("a corollary block is wired to the parent; a proposition block to the results its proof cites, not to the parent — ids, provenance and the parent's readings are those of any block", () => {
    expect(st(COR_ID).depends_on.slice(0, 2)).toEqual(["thm:main", "ass:gauss"]);
    expect(st(PROP_ID).depends_on).not.toContain("thm:main");
    expect(st(PROP_ID).depends_on).toContain("lem:rate");
    // the id is the statement's, whatever the kind
    expect([COR_ID, PROP_ID].every((id) => /^thm:cor-fix-[0-9a-f]{8}$/u.test(id))).toBe(true);
    expect([st(COR_ID).split_from, st(PROP_ID).split_from]).toEqual(["thm:main", "thm:main"]);
    // a reading of the parent binds both: a proposition block was stated inside the printed parent
    const pin = c.assumptions.find((a) => a.id.startsWith("ass:pin-fix-"))!;
    expect(pin.used_by).toEqual(expect.arrayContaining(["thm:main", COR_ID, PROP_ID]));
    // the printed result is the parent together with its blocks: what used it uses them all
    expect(st("thm:use").depends_on).toEqual(["thm:main", COR_ID, PROP_ID]);
    expect(checkCoreInvariants(c)).toEqual([]);
  });

  it("against a core that still has the old edge, the change is an ordinary wiring change: the proposition block's basis moves, the corollary's and the parent's do not, nor that of a result using the block", () => {
    const old = oldEdge(c);
    expect(old.statements.find((s) => s.id === PROP_ID)!.depends_on[0]).toBe("thm:main");
    expect(old.statements.map((s) => s.id)).toEqual(c.statements.map((s) => s.id));
    expect(nodeFingerprint(old, PROP_ID)).not.toBe(nodeFingerprint(c, PROP_ID));
    expect(nodeFingerprint(old, COR_ID)).toBe(nodeFingerprint(c, COR_ID));
    expect(nodeFingerprint(old, "thm:main")).toBe(nodeFingerprint(c, "thm:main"));
    expect(nodeFingerprint(old, "lem:rate")).toBe(nodeFingerprint(c, "lem:rate"));
    // what uses the block reads its text, the hypotheses it is stated under and its verdict — not the
    // results it rests on: it is re-opened only if the block's verdict moves
    expect(nodeFingerprint(old, "thm:use")).toBe(nodeFingerprint(c, "thm:use"));
  });
});

describe("what is shown of a built core", () => {
  const old = buildCore(core(), { patches: patches() }).core;

  it("the page's model: `splitKind` on each block, and the proof map's dependencies as built", async () => {
    const root = mkdtempSync(path.join(os.tmpdir(), "split-kind-ui-"));
    tmp.push(root);
    const dir = path.join(root, "runs", "k");
    mkdirSync(path.join(dir, "discovery"), { recursive: true });
    writeFileSync(path.join(dir, "state.json"), JSON.stringify({ stage_completed: "V1.5", verify: { phase: "review" } }));
    writeFileSync(path.join(dir, "discovery", "core.json"), JSON.stringify(old));
    const d = await runDetail({ toolkitRoot: root, runsDir: path.join(root, "runs") } as never, "k");
    const by = new Map(d.results.map((r) => [r.id, r]));
    expect([by.get(COR_ID)!.splitKind, by.get(PROP_ID)!.splitKind, by.get("thm:main")!.splitKind]).toEqual(["corollary", "proposition", undefined]);
    expect(by.get(COR_ID)!.deps).toContain("thm:main");
    expect(by.get(PROP_ID)!.deps).toEqual(["lem:rate"]);
    expect(by.get(PROP_ID)!.splitFrom).toBe("thm:main");
  });

  it("the report: each block's row says its kind and is named by it, and a proposition block does not rest on its parent", () => {
    const envs = { main_file: "main.tex", files: ["main.tex"], newtheorem: {}, bibliography: [], envs: old.statements.filter((s) => !s.split_from).map((s) => ({ id: s.id, kind: s.kind, envName: s.kind, label: s.id, title: null, body: s.statement, proof: null, proofLines: null, lines: { file: "main.tex", from: s.tex_locator!.from, to: s.tex_locator!.to }, refs: [] })) };
    // the parent is refuted: only what rests on it inherits that
    const refuted = [{ node: "thm:main", stage: "V1.5", kind: "refuted", detail: "d", witness: "w", at: "t" }, { node: COR_ID, stage: "V1.5", kind: "refuted", detail: "d", witness: "w", at: "t" }, { node: PROP_ID, stage: "V1.5", kind: "refuted", detail: "d", witness: "w", at: "t" }];
    const { json } = buildReport({
      qid: "kind_paper", envs: envs as never, scope: envs.envs.map((e) => e.id), core: old, transcribed: core(), review: null, findings: refuted as never,
      addedAssumptions: [], crosswalk: null, graph: null, lean: null, warnings: { lint: [], parser: [] }, flags: {}, stageCompleted: "V1.5", earlyStop: true, sourceSha256: "h",
      inputs: { v1_5_review: "x", crosswalk_full: "x", graph_json: "x", v1_scope: "x", lean_evidence: "x" },
    });
    const row = (id: string): ReportRow => json.results.find((r) => r.node_id === id)!;
    expect([row(COR_ID).split_kind, row(PROP_ID).split_kind, row("thm:main").split_kind]).toEqual(["corollary", "proposition", undefined]);
    expect(row(COR_ID).title).toMatch(/^Corollary of .* \(split off by its repair\)$/u);
    expect(row(PROP_ID).title).toMatch(/^Proposition stated in .* \(split off by its repair\)$/u);
    expect(row(COR_ID).inherits_refutation_from).toContain("thm:main");
    expect(row(PROP_ID).inherits_refutation_from).not.toContain("thm:main");
    expect(resultNames(json.results, () => undefined)).toMatchObject({ [COR_ID]: expect.stringMatching(/^Corollary 1 of /u), [PROP_ID]: expect.stringMatching(/^Proposition 2 of /u) });
  });
});

describe("naming: by kind, one running number per result", () => {
  const row = (over: Partial<ReportRow>): ReportRow => ({ env_id: "thm:main", label: null, kind: "theorem", title: null, locator: "main.tex:3-5", node_id: "thm:main", ...over }) as ReportRow;

  it("`resultNames`: \"Proposition 5.2.1\", \"Corollary 5.2.2\"; a row without a kind (an older report) is a corollary", () => {
    const rows = [
      row({ label: "thm:main" }),
      row({ node_id: "thm:cor-fix-1", split_from: "thm:main", split_kind: "proposition" }),
      row({ node_id: "thm:cor-fix-2", split_from: "thm:main", split_kind: "corollary" }),
      row({ node_id: "thm:cor-fix-3", split_from: "thm:main" }),
    ];
    expect(resultNames(rows, () => "5.2")).toEqual({ "thm:main": "Theorem 5.2", "thm:cor-fix-1": "Proposition 5.2.1", "thm:cor-fix-2": "Corollary 5.2.2", "thm:cor-fix-3": "Corollary 5.2.3" });
    expect(resultNames(rows, () => undefined)).toMatchObject({ "thm:cor-fix-1": "Proposition 1 of Theorem labelled `thm:main`", "thm:cor-fix-2": "Corollary 2 of Theorem labelled `thm:main`" });
  });

  const head = (html: string): string[][] => [...html.matchAll(/<div class="(rv ins cor[^"]*)"[^>]*data-res="([^"]*)"[^>]*><span class="res-anchor"[^>]*><\/span><span class="env">(.*?)<\/span> <span class="rv-tag">(.*?)<\/span>/gu)].map((m) => [m[1]!, m[2]!, m[3]!, m[4]!]);
  const page = (blocks: string, splitKinds?: Record<string, "corollary" | "proposition">): string =>
    renderPaper({ files: { "m.tex": `\\begin{document}\\begin{theorem}\\label{thm:main}X.\\vsCorrected{Y.}\\end{theorem}\n${blocks}\\end{document}` }, main: "m.tex", aux: String.raw`\newlabel{thm:main}{{5.2}{3}}`, splitKinds }).html;

  it("the page: a proposition block is headed \"Proposition 5.2.k\" with its own tag, a corollary block \"Corollary 5.2.k\", numbered together in order", () => {
    const html = page(
      String.raw`\vsSplitProposition{thm:cor-fix-1}{Theorem~\ref{thm:main}}{P. \vsLine\textit{Proof.} By the lemma.}` + "\n" +
        String.raw`\vsCorollary{thm:cor-fix-2}{Theorem~\ref{thm:main}}{Q. \vsLine\textit{Proof.} By Theorem~\ref{thm:main}.}` + "\n" +
        String.raw`\vsProposedSplitProposition{thm:cor-fix-3}{Theorem~\ref{thm:main}}{R.}`,
    );
    expect(head(html)).toEqual([
      ["rv ins cor formal k-proposition", "thm:cor-fix-1", "Proposition 5.2.1.", "Stated apart by the repair"],
      ["rv ins cor formal k-corollary", "thm:cor-fix-2", "Corollary 5.2.2.", "Added by the repair"],
      ["rv ins cor pending formal k-proposition", "thm:cor-fix-3", "Proposition 5.2.3.", "Proposed — awaiting a ruling"],
    ]);
    // its proof is under the page's proof heading, like a corollary's
    expect(html).toMatch(/k-proposition"[^>]*>.*?<div class="proof"><span class="env">Proof\.<\/span> By the lemma\./su);
  });

  it("an annotated paper written with the corollary macros alone still renders — and is headed by the core's kinds when the page has them", () => {
    const old = String.raw`\vsCorollary{thm:cor-fix-1}{Theorem~\ref{thm:main}}{P.}` + "\n" + String.raw`\vsCorollary{thm:cor-fix-2}{Theorem~\ref{thm:main}}{Q.}`;
    expect(head(page(old)).map((b) => [b[0], b[2]])).toEqual([["rv ins cor formal k-corollary", "Corollary 5.2.1."], ["rv ins cor formal k-corollary", "Corollary 5.2.2."]]);
    expect(head(page(old, { "thm:cor-fix-1": "proposition", "thm:cor-fix-2": "corollary" })).map((b) => [b[0], b[2]])).toEqual([["rv ins cor formal k-proposition", "Proposition 5.2.1."], ["rv ins cor formal k-corollary", "Corollary 5.2.2."]]);
  });

  it("the page's script names a block by `splitKind` (drawer title, proof-map label)", async () => {
    const js = await readFile(path.join(import.meta.dirname, "..", "..", "src", "ui", "static", "app.js"), "utf8");
    expect(js).toContain(`const word = r.splitKind === "proposition" ? "Proposition" : "Corollary";`);
    expect(js).toContain("return num ? `${word} ${num}.${k}` : `${word} ${k} of ${of || \"the result above\"}`;");
  });
});

describe("the annotated and the corrected paper", () => {
  const STMT = ["\\begin{theorem}\\label{thm:main}", BODY, "\\end{theorem}"];
  const PROOF = ["\\begin{proof}[Proof of Theorem~\\ref{thm:main}]", "By the central limit theorem.", "\\end{proof}"];
  const one = (): Core => ({ ...core(), statements: [core().statements[1]!] }) as Core;
  const doc = (...lines: string[]): string => ["\\documentclass{article}", "\\begin{document}", ...lines, "\\end{document}"].join("\n");
  const input = (files: Record<string, string>, proofLines: { file: string; from: number; to: number } | null, correctedView: boolean): AnnotationInput => ({
    files,
    envs: { main_file: "main.tex", files: Object.keys(files), newtheorem: {}, bibliography: [], envs: [{ id: "thm:main", kind: "theorem", envName: "theorem", label: "thm:main", title: null, body: BODY, proof: proofLines ? "By the central limit theorem." : null, proofLines, section: null, lines: { file: "main.tex", from: 3, to: 5 }, refs: [] }] } as never,
    flatText: Object.values(files).join("\n"), lineMap: Object.entries(files).flatMap(([file, t]) => t.split("\n").map((_, i) => ({ file, line: i + 1 }))), refs: null, transcribed: one(), core: one(),
    patches: { patches: [{ node: "thm:main", corrected_statement: "The estimator is normal.", proof_note: "The proof as printed proves the repaired statement; no step changes.", corollaries: [PROP, COR] }], unfixable: [] } as never,
    paperErrors: { "thm:main": { detail: "efficiency fails", witness: "w" } }, findings: [], review: null, correctedView,
  });
  const APPENDIX = { "main.tex": doc(...STMT, "Text.", "\\input{appendix}"), "appendix.tex": ["\\section{Proofs}", ...PROOF, "More."].join("\n") };
  const AT = { file: "appendix.tex", from: 2, to: 4 };
  const corrected = (opts: Parameters<typeof correctedTex>[1]): Record<string, string> => {
    const plan = planAnnotations(input(APPENDIX, AT, true));
    expect(plan.unlocated).toEqual([]);
    return Object.fromEntries(Object.entries(APPENDIX).map(([f, t]) => [f, correctedTex(applyTexEdits(t, plan.edits[f] ?? []), opts).tex]));
  };

  it("the macros: a proposition block has its own, with the corollary macros' arguments, defined in the preamble with its label", () => {
    expect(SPLIT_MACROS.proposition).toEqual({ block: "vsSplitProposition", proposed: "vsProposedSplitProposition", proof: "vsSplitPropositionProof" });
    expect(["vsCorollary", "vsProposedCorollary", "vsCorollaryProof", "vsSplitProposition", "vsProposedSplitProposition", "vsSplitPropositionProof", "vsCorrected"].map(splitMacroKind)).toEqual(["corollary", "corollary", "corollary", "proposition", "proposition", "proposition", null]);
    const pre = VS_PREAMBLE_BLOCK;
    expect(pre).toContain("\\newcommand{\\vsSplitProposition}[3]{\\vsBlock{vsBlue}{}{Proposition stated in #2:}{#3}}");
    expect(pre).toContain("\\newcommand{\\vsProposedSplitProposition}[3]{\\vsBlock{vsBlue}{}{Proposed proposition stated in #2 (awaiting your decision):}{#3}}");
    expect(pre).toContain("\\newcommand{\\vsCorollary}[3]{\\vsBlock{vsBlue}{}{Corollary of #2:}{#3}}");
  });

  it("the annotated paper writes each block under the macro of its kind, in the fixer's order", () => {
    const files = { "main.tex": doc(...STMT, "Text.") };
    const tex = applyTexEdits(files["main.tex"], planAnnotations(input(files, null, false)).edits["main.tex"] ?? []);
    const p = tex.indexOf(`\\vsSplitProposition{${PROP_ID}}{Theorem~\\ref{thm:main}}{\\textbf{the rate.} ${PROP.statement} \\vsLine\\textit{Proof.} ${PROP.follows}}`);
    const c = tex.indexOf(`\\vsCorollary{${COR_ID}}{Theorem~\\ref{thm:main}}{\\textbf{the Gaussian case.} ${COR.statement} \\vsLine\\textit{Proof.} ${COR.follows}}`);
    expect(p).toBeGreaterThan(tex.indexOf("\\end{theorem}"));
    expect(c).toBeGreaterThan(p);
    // and it renders: one running number across both kinds
    const html = renderPaper({ files: { "main.tex": tex }, main: "main.tex", aux: String.raw`\newlabel{thm:main}{{5.2}{3}}` }).html;
    expect(html).toMatch(/<span class="env">Proposition 5\.2\.1\.<\/span>[\s\S]*<span class="env">Corollary 5\.2\.2\.<\/span>/u);
  });

  it("the corrected paper: a proposition block is a \"Proposition\" paragraph, its remote proof \"Proof of the proposition\"; a corollary block as before", () => {
    const out = corrected({ proofEnv: true });
    expect(out["main.tex"]).toContain(`\\noindent\\textit{Proposition (the rate).} ${PROP.statement}\n\n\\noindent\\textit{Corollary (the Gaussian case).} ${COR.statement}`);
    expect(out["appendix.tex"]).toContain(`\\begin{proof}[Proof of the proposition (the rate)]\n${PROP.follows}\n\\end{proof}\n\n\\begin{proof}[Proof of the corollary (the Gaussian case)]\n${COR.follows}\n\\end{proof}`);
    expect(Object.values(out).join("\n")).not.toMatch(/\\vs[A-Z]/u);
  });

  it("the corrected paper uses the paper's own proposition environment when it has one, labelled and named by its number", () => {
    const out = corrected({ proofEnv: true, corollaryEnv: { name: "cor", numbered: true }, propositionEnv: { name: "prop", numbered: true } });
    expect(out["main.tex"]).toContain(`\\begin{prop}[the rate]\\label{${PROP_ID}}\n${PROP.statement}\n\\end{prop}\n\n\\begin{cor}[the Gaussian case]\\label{${COR_ID}}\n${COR.statement}\n\\end{cor}`);
    expect(out["appendix.tex"]).toContain(`\\begin{proof}[Proof of Proposition~\\ref{${PROP_ID}}]`);
    expect(out["appendix.tex"]).toContain(`\\begin{proof}[Proof of Corollary~\\ref{${COR_ID}}]`);
    // a corollary environment alone: the proposition block stays a paragraph
    const half = corrected({ proofEnv: true, corollaryEnv: { name: "cor", numbered: true } });
    expect(half["main.tex"]).toContain(`\\noindent\\textit{Proposition (the rate).} ${PROP.statement}`);
    expect(half["appendix.tex"]).toContain("\\begin{proof}[Proof of the proposition (the rate)]");
  });

  it("a proposition block awaiting the owner is not the paper's", () => {
    const r = correctedTex(`\\end{theorem}\n\\vsAt{${PROP_ID}}{awaiting decision}\\vsProposedSplitProposition{${PROP_ID}}{}{P holds.}\nNext.`, { proofEnv: true });
    expect(r.tex).not.toContain("P holds.");
  });
});

describe("the prompts say when to separate and how a block is labelled", () => {
  const read = async (...p: string[]): Promise<string> => (await readFile(path.join(import.meta.dirname, "..", "..", "src", "verify", "prompts", ...p), "utf8")).replace(/\s+/gu, " ");

  it("the fixer: two cases, grouped by shared conditions; the label is read from the proof's citation of the corrected statement", async () => {
    const p = await read("V1", "patch.txt");
    expect(p).toContain("(1) a general statement mixed with special cases that hold under their own conditions");
    expect(p).toContain("(2) several conclusions bundled in one statement that do not rest on the same conditions or the same results");
    expect(p).toContain("a summary collecting results proved separately, each under its own hypotheses, each by a different lemma");
    expect(p).toContain("group by shared conditions: never one block per formula when several follow from the same lemma under the same hypotheses");
    // what the parent keeps is left open beyond "what is not moved"
    expect(p).toContain("the ops leave the node what is not moved to a block (it may become short)");
    expect(p).toContain("A block is shown as a COROLLARY when it is a consequence of the corrected statement, and as a PROPOSITION when it is a separate claim the printed statement bundled in.");
    expect(p).toContain("You do not write the label: the pipeline reads it from `follows`.");
    expect(p).toContain("So `follows` cites the corrected statement exactly when it uses it: never as decoration, never omitted when used.");
    // the reasons never to split stand
    expect(p).toContain("Never split a statement that is one claim, a further conclusion under the same hypotheses (\"moreover …\" stays in the statement), or to shorten");
    expect(p).toContain("correct the citation in `follows` and change nothing else");
  });

  it("the referee: a block's proof is graded as written and need not go through the parent; the citation must be honest, by the lightest channel; the form request covers bundled conclusions", async () => {
    const p = await read("V1.5", "review.txt");
    expect(p).toContain("The proof need not go through the parent: never require it to.");
    expect(p).toContain("a proof that cites the parent must really use it, and one that uses the parent must cite it");
    expect(p).toContain("a mismatch is a defect of that proof's text, never of the paper");
    expect(p).toContain("grade the block `error` with `minimality: true`, the witness naming the citation to remove or to add");
    expect(p).toContain("(it is not wired to the parent, and that missing edge is no drift)");
    expect(p).toContain("(2) it still bundles conclusions that do not rest on the same conditions or the same results");
    expect(p).toContain("is then a block of its own — say so in `split.why`, naming the blocks");
    expect(p).toContain("This is a remark on form, never a grade: the node stays `ok`.");
    expect(p).toContain("Never a reason to split: a further conclusion under the same hypotheses (\"moreover …\"), a statement that is one claim, mere length.");
  });

  it("the runner's form request to the fixer names both cases and stays a note", () => {
    const o = splitObjection({ id: "thm:main", split: { why: "W." } } as never);
    expect(o).toMatchObject({ axis: "split", note: true, witness: null });
    expect(o.detail).toContain("a general claim with special cases, or conclusions resting on different conditions or results): W.");
    expect(o.detail).toContain("one block per case, or per group of conclusions resting on the same conditions and results (`corollaries`), nothing dropped");
  });
});
