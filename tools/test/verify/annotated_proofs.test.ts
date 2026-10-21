/**
 * Proof corrections in the annotated paper (user rule 2026-09-24: every change to the paper is
 * visible; proofs are revised, not rewritten): proof ops in the paper's proof itself — the printed
 * units red ("Original:"), their replacement blue right after ("Corrected:" / "Corrected
 * (for the proposed statement):"), adjacent replaced units one block — an added step is a replacement of the step it follows — also when the proof sits in
 * another file under a "Proof of Theorem" heading; a proof note after the proof it amends
 * ("Corrected proof (confirmed):"), a proof-only repair made visible; a proof
 * that cannot be located → the block at the end of the statement's section; a pending suggestion's
 * proof ("Proof of the proposed statement:").
 */
import { execFileSync } from "node:child_process";
import { existsSync } from "node:fs";
import { findExecutable } from "../../src/shared/program.js";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { injectPreamble } from "../../src/verify/annotate_tex.js";
import { applyEdits, planAnnotations, type AnnotationInput } from "../../src/verify/annotated_paper.js";
import { correctedTex } from "../../src/verify/corrected_tex.js";
import { FURTHER_PROOF_SEPARATOR } from "../../src/verify/tex_envs.js";

const FLAT = [
  "\\documentclass{article}", // 1
  "\\begin{document}", // 2
  "\\begin{theorem}\\label{thm:a}", // 3
  "The estimator is consistent.", // 4
  "\\end{theorem}", // 5
  "\\begin{proof}", // 6
  "First, $E[X_n] \\to \\mu$ by the law of large numbers.", // 7
  "Then $\\hat\\theta - \\theta = O_p(n^{-1/2})$ follows.", // 8
  "\\end{proof}", // 9
  "", // 10
  "\\begin{lemma}\\label{lem:b}", // 11
  "The bound holds.", // 12
  "\\end{lemma}", // 13
  "\\end{document}", // 14
].join("\n");

function core(): Core {
  return {
    qid: "pf",
    symbols: [],
    assumptions: [],
    definitions: [],
    statements: [
      { id: "thm:a", kind: "theorem", statement: "The estimator is consistent.", depends_on: [], status: "to-prove", tex_locator: { file: "main.tex", from: 3, to: 5, env: "theorem", label: "thm:a" } },
      { id: "lem:b", kind: "lemma", statement: "The bound holds.", depends_on: [], status: "to-prove", tex_locator: { file: "main.tex", from: 11, to: 13, env: "lemma", label: "lem:b" } },
    ],
    target_estimand: "t",
    bibliography: [],
  } as unknown as Core;
}

const PROOF_NOTE = "The second step is replaced: by the bias bound, $\\hat\\theta - \\theta = O_p(n^{-1/3})$, which gives consistency.";

function input(over: Partial<AnnotationInput> = {}): AnnotationInput {
  const env = (id: string, envName: string, from: number, to: number, body: string, proof: { text: string; from: number; to: number } | null) => ({
    id, kind: envName, envName, label: id, title: null, body, proof: proof?.text ?? null, proofLines: proof ? { file: "main.tex", from: proof.from, to: proof.to } : null, section: null, lines: { file: "main.tex", from, to }, refs: [],
  });
  return {
    files: { "main.tex": FLAT },
    envs: {
      main_file: "main.tex",
      files: ["main.tex"],
      newtheorem: {},
      envs: [
        env("thm:a", "theorem", 3, 5, "The estimator is consistent.", { text: "First, $E[X_n] \\to \\mu$ by the law of large numbers.\nThen $\\hat\\theta - \\theta = O_p(n^{-1/2})$ follows.", from: 6, to: 9 }),
        env("lem:b", "lemma", 11, 13, "The bound holds.", null),
      ],
      bibliography: [],
    } as never,
    flatText: FLAT,
    lineMap: FLAT.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 })),
    refs: null,
    transcribed: core(),
    core: core(),
    patches: { patches: [{ node: "thm:a", corrected_statement: null, proof_note: PROOF_NOTE }], unfixable: [] },
    paperErrors: { "thm:a": { detail: "the second step is false", witness: "The display $\\hat\\theta - \\theta = O_p(n^{-1/2})$ fails: the bias is of order n^{-1/3}." } },
    findings: [],
    review: null,
    ...over,
  };
}

const annotated = (inp: AnnotationInput): string => applyEdits(FLAT, planAnnotations(inp).edits["main.tex"] ?? []);

describe("proof corrections in the annotated paper", () => {
  it("an applied patch's proof note follows the proof; no step is marked without an op on it; a proof-only repair says the statement stands", () => {
    const out = annotated(input());
    expect(out).toContain(`\\end{proof}\n\\vsProof{The statement stands; the proof is completed as follows. ${PROOF_NOTE}}\n`);
    expect(out).not.toContain("\\vsStep{");
    const plan = planAnnotations(input());
    expect(plan.records.filter((r) => r.kind === "corrected proof").map((r) => r.located_by)).toEqual(["after-proof"]);
    // pure: planning twice gives the same edits
    expect(JSON.stringify(planAnnotations(input()).edits)).toBe(JSON.stringify(plan.edits));
  });

  it("a result the paper prints no proof of, resting on a lemma whose proof is corrected: the block says so and names the lemma and where", () => {
    const inp = input({
      patches: {
        patches: [
          { node: "lem:b", corrected_statement: null, proof_note: "Bound it by $2C$." },
          { node: "thm:a", corrected_statement: null, proof_note: "Combine the lemmas." },
        ],
        unfixable: [],
      },
      paperErrors: {},
    });
    // thm:a uses lem:b
    for (const c of [inp.transcribed, inp.core]) c.statements[0]!.depends_on = ["lem:b"];
    const thm = (inp.envs as unknown as { envs: Array<{ proof: string | null; proofLines: unknown; section: string | null }> }).envs[0]!;
    thm.proof = null;
    thm.proofLines = null;
    (inp.envs as unknown as { envs: Array<{ section: string | null }> }).envs[1]!.section = "Local rates";
    const out = annotated(inp);
    // (2026-09-25) right after the result, no heading; every lemma it uses; where their corrections are
    // marked by the paper's own numbering (here no heading: the lemma's page), never a file name
    expect(out).toContain("\\end{theorem}\n\\vsProof{This result prints no proof; it follows from Lemma~\\ref{lem:b} (its corrected proof is marked on page~\\pageref{lem:b}). \\vsLine The statement stands; the proof is completed as follows. Combine the lemmas.}\n");
    expect(out).not.toMatch(/\\texttt\{main\.tex\}|\\textbf\{Theorem~\\ref\{thm:a\}\.\}/u);
    // the lemma itself rests on nothing corrected: the old wording, right after it (2026-09-26)
    expect(out).toContain("\\end{lemma}\n\\vsProof{\\textit{(the paper's proof could not be located; the corrected proof is given here)} \\vsLine The statement stands; the proof is completed as follows. Bound it by $2C$.}");
    const plan = planAnnotations(inp);
    expect(plan.records.filter((r) => r.kind === "corrected proof").map((r) => [r.node, r.located_by])).toEqual(expect.arrayContaining([["thm:a", "after-env (no printed proof)"], ["lem:b", "after-env (no proof located)"]]));
  });
});

describe("the corrected view of a proof block after the printed proof", () => {
  const PRINTED = "First, $E[X_n] \\to \\mu$ by the law of large numbers.\nThen $\\hat\\theta - \\theta = O_p(n^{-1/2})$ follows.";
  /** The whole amended proof of steps that could not be marked (`materializeRepair`). */
  const AMENDED = "First, $E[X_n] \\to \\mu$ by the law of large numbers. By the bias bound, $\\hat\\theta - \\theta = O_p(n^{-1/3})$ follows.";
  const UMBRELLA = "Each proposition is proved where it is stated.";
  const located = (patch: Record<string, unknown> = {}, proof = PRINTED): AnnotationInput => {
    const inp = input({ patches: { patches: [{ node: "thm:a", corrected_statement: null, proof_note: PROOF_NOTE, ...patch } as never], unfixable: [] } });
    const thm = (inp.envs as unknown as { envs: Array<{ proof: string | null; proofLines: Record<string, unknown> }> }).envs[0]!;
    thm.proofLines = { ...thm.proofLines, env: "proof" };
    thm.proof = proof;
    return inp;
  };
  /** Steps whose op does not resolve: the fallback block. */
  const unplaced = (): AnnotationInput => located({ proof_note: AMENDED, ops: [{ op: "replace", unit: "thm:a/proof/1/9", tex: "x" }] });
  /** An umbrella whose printed proof does not align: its note in a block after the proof. */
  const umbrella = (): AnnotationInput => located({ proof_note: UMBRELLA, umbrella: true, ops: [] }, "A proof that is not the printed one.");
  const view = (inp: AnnotationInput): string => applyEdits(FLAT, planAnnotations({ ...inp, correctedView: true }).edits["main.tex"] ?? []);
  it("a whole proof — the amended proof of unplaced steps — replaces the printed proof environment V1 located, exactly; the annotated paper keeps both", () => {
    const tagged = view(unplaced());
    expect(tagged).toContain("\\end{theorem}\n\\vsAt{thm:a}{printed proof}\\vsPrintedProof{begin}\\begin{proof}\nFirst,");
    expect(tagged).toContain("follows.\n\\end{proof}\\vsAt{thm:a}{printed proof}\\vsPrintedProof{end}\n\\vsAt{thm:a}{corrected proof; steps unplaced}\\vsProof{");
    const r = correctedTex(tagged, { proofEnv: true });
    expect(r.tex).toContain(`\\end{theorem}\n\n\\begin{proof}\n${AMENDED}\n\\end{proof}\n`);
    expect(r.tex.split("\\begin{proof}").length).toBe(2);
    expect(r.tex.indexOf(AMENDED)).toBeLessThan(r.tex.indexOf("\\begin{lemma}"));
    expect(r.tex).not.toContain("O_p(n^{-1/2})");
    expect(r.items).toEqual([]);
    const out = annotated(unplaced());
    expect(out).toContain("O_p(n^{-1/2})");
    expect(out).toContain("\\end{proof}\n\\vsProof{\\textit{(the corrected steps could not be marked");
    expect(out).not.toContain("vsPrintedProof");
  });
  it("an umbrella's note whose printed proof did not align replaces it likewise", () => {
    const r = correctedTex(view(umbrella()), { proofEnv: true });
    expect(r.tex).toContain(`\\end{theorem}\n\n\\begin{proof}\n${UMBRELLA}\n\\end{proof}\n`);
    expect(r.tex).not.toContain("law of large numbers");
    expect(r.items).toEqual([]);
  });
  it("a note beside a printed proof that is neither may be partial: nothing is marked, both proofs stay, listed as blocking", () => {
    const tagged = view(located());
    expect(tagged).not.toContain("vsPrintedProof");
    const r = correctedTex(tagged, { proofEnv: true });
    expect(r.tex).toContain("law of large numbers");
    expect(r.tex).toContain(`\\begin{proof}\n${PROOF_NOTE}\n\\end{proof}`);
    expect(r.items.map((i) => i.kind)).toEqual(["second-proof"]);
  });
  it("does not mark a proof the paper prints in several places, nor one read from plain lines", () => {
    expect(view(located({ proof_note: AMENDED, ops: [{ op: "replace", unit: "thm:a/proof/1/9", tex: "x" }] }, `A.${FURTHER_PROOF_SEPARATOR}B.`))).not.toContain("vsPrintedProof");
    const seg = unplaced();
    (seg.envs as unknown as { envs: Array<{ proofLines: Record<string, unknown> }> }).envs[0]!.proofLines.env = "segment-proof";
    expect(view(seg)).not.toContain("vsPrintedProof");
    expect(correctedTex(view(seg), { proofEnv: true }).items.map((i) => i.kind)).toEqual(["second-proof"]);
  });
});

describe("an umbrella's proof", () => {
  const NOTE = "Each proposition is proved where it is stated.";
  it("replaces the printed proof whole (its blocks carry the proofs): the printed proof red, the note blue in its place, no block after it", () => {
    const out = annotated(input({ patches: { patches: [{ node: "thm:a", corrected_statement: null, proof_note: NOTE, umbrella: true, ops: [] } as never], unfixable: [] } }));
    expect(out).toContain(`\\begin{proof}\n\\vsStep{First, $E[X_n] \\to \\mu$ by the law of large numbers.\nThen $\\hat\\theta - \\theta = O_p(n^{-1/2})$ follows.} \\vsCorrectedStep{${NOTE}}`);
    expect(out).not.toContain("\\vsProof{");
    const plan = planAnnotations(input({ patches: { patches: [{ node: "thm:a", corrected_statement: null, proof_note: NOTE, umbrella: true, ops: [] } as never], unfixable: [] } }));
    expect(plan.records.filter((r) => r.kind === "corrected proof").map((r) => r.located_by)).not.toContain("after-proof");
  });
  it("a repair that is not an umbrella keeps its note after the printed proof", () => {
    const out = annotated(input({ patches: { patches: [{ node: "thm:a", corrected_statement: null, proof_note: NOTE, ops: [] } as never], unfixable: [] } }));
    expect(out).toContain(`\\end{proof}\n\\vsProof{The statement stands; the proof is completed as follows. ${NOTE}}\n`);
    expect(out).not.toContain("\\vsStep{");
  });
});

describe("proof edits: the printed proof revised in place", () => {
  /** The proof's second unit, "Then … follows.", replaced. */
  const EDIT = { op: "replace", unit: "thm:a/proof/1/2", tex: "By the bias bound $|E\\hat\\theta - \\theta| \\le C h^2$ with $h = n^{-1/6}$, $\\hat\\theta - \\theta = O_p(n^{-1/3})$." };

  it("a step whose words stand as printed and only gains a detail is not marked: its detail is a side note after it; a revised step keeps its detail in its block", () => {
    const kept = { op: "replace", unit: "thm:a/proof/1/1", tex: "First, $E[X_n] \\to \\mu$ by the law of large numbers.\\vsDetail{The $X_n$ are i.i.d.\\ with finite mean.}" };
    const revised = { ...EDIT, tex: `${EDIT.tex}\\vsDetail{Here $C$ bounds the second derivative.}` };
    const out = annotated(input({ patches: { patches: [{ node: "thm:a", corrected_statement: null, proof_note: "derived", ops: [kept, revised] as never }], unfixable: [] } }));
    expect(out).toContain("First, $E[X_n] \\to \\mu$ by the law of large numbers. \\vsDetail{The $X_n$ are i.i.d.\\ with finite mean.}");
    expect(out).not.toContain("\\vsStep{First");
    expect(out).toContain(`\\vsStep{Then $\\hat\\theta - \\theta = O_p(n^{-1/2})$ follows.} \\vsCorrectedStep{${revised.tex}}`);
  });

  it("each run of replaced steps red with its replacement blue right after (adjacent steps one block), no note on the proof", () => {
    const out = annotated(input({
      patches: { patches: [{ node: "thm:a", corrected_statement: null, proof_note: "derived", ops: [EDIT, { op: "replace", unit: "thm:a/proof/1/1", tex: "First, $E[X_n] \\to \\mu$ by the law of large numbers. The variance is $O(1/n)$." }] as never }], unfixable: [] },
    }));
    // adjacent replaced steps are one red block and one blue block (user decision 2026-09-29)
    expect(out).toContain(`\\vsStep{First, $E[X_n] \\to \\mu$ by the law of large numbers.\nThen $\\hat\\theta - \\theta = O_p(n^{-1/2})$ follows.} \\vsCorrectedStep{First, $E[X_n] \\to \\mu$ by the law of large numbers. The variance is $O(1/n)$.\n${EDIT.tex}}`);
    expect(out).not.toContain("vsAddedStep");
    expect(out).not.toContain("\\vsProof{");
    const proof = out.slice(out.indexOf("\\begin{proof}"), out.indexOf("\\end{proof}"));
    expect(proof).not.toContain("\\vsNote{");
  });

  it("a pending proposal's gives-up text that fails goes back to whoever wrote it: the referee's when marked so, else the fixer's", () => {
    const producer = (by?: "referee") => {
      const plan = planAnnotations(input({
        patches: { patches: [], unfixable: [{ node: "thm:a", reason: "any repair weakens the contribution", suggested_repair: { corrected_statement: "The estimator is consistent at a slower rate.", proof_note: "derived", ops: [EDIT] as never, given_up: "the rate μ" } }] },
        pending: { weakening: [{ node: "thm:a", corrected_statement: "The estimator is consistent at a slower rate.", given_up: "the rate μ", ...(by ? { given_up_by: by } : {}), detail: "the second step is false", witness: "w" }], rewind: null, cap: null },
      }));
      return plan.defects.filter((d) => d.fragment?.text.includes("μ")).map((d) => d.fragment!.producer);
    };
    expect(producer("referee")).toEqual(expect.arrayContaining(["referee"]));
    expect(producer("referee")).not.toContain("fixer");
    expect(producer()).toEqual(expect.arrayContaining(["fixer"]));
  });

  it("ops the annotator cannot place fall back to one block after the printed proof, saying so", () => {
    const bad = { ...EDIT, unit: "thm:a/proof/1/9" };
    const out = annotated(input({ patches: { patches: [{ node: "thm:a", corrected_statement: null, proof_note: "the corrected proof, in full", ops: [bad] as never }], unfixable: [] } }));
    expect(out).toContain("\\end{proof}\n\\vsProof{\\textit{(the corrected steps could not be marked in the printed proof; the corrected proof is given here)} \\vsLine");
    expect(out).not.toContain("\\vsCorrectedStep");
  });
});

describe("a repair of a definition printed in running text", () => {
  it("is placed on its own passage, never widened to the document around it", () => {
    const flat = ["\\documentclass{article}", "\\begin{document}", "Intro.", "We write $\\psi_0(W)$ for the oracle score.", "More text.", "\\end{document}"].join("\n");
    const defs = [{ id: "def:score", term: "oracle score", construction: "We write $\\psi_0(W)$ for the oracle score.", depends_on: [] }];
    const c = { ...core(), statements: [], definitions: defs } as unknown as Core;
    const base = input();
    const plan = planAnnotations({
      ...base,
      files: { "main.tex": flat },
      flatText: flat,
      lineMap: flat.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 })),
      envs: { ...(base.envs as object), envs: [] } as never,
      refs: { assumptions: [], statements: [], definitions: [{ id: "def:score", source: { prose: true, slice: { from: "We write", to: "oracle score." } } }] } as never,
      transcribed: c,
      core: c,
      patches: { patches: [{ node: "def:score", corrected_statement: "We write $\\psi_0(Y,W)$ for the oracle score.", proof_note: "p" }], unfixable: [] },
      paperErrors: { "def:score": { detail: "the score takes the outcome too", witness: null } },
    });
    expect(plan.unlocated).toEqual([]);
    expect(plan.records.filter((r) => r.node === "def:score").map((r) => r.located_by)).toEqual(["slice"]);
    const out = applyEdits(flat, plan.edits["main.tex"] ?? []);
    expect(out.indexOf("\\vsOriginal{")).toBeGreaterThan(out.indexOf("Intro."));
    expect(out).toContain("\\begin{document}\nIntro.\n");
  });
});

describe("a proof op on a unit the paper cuts across environments (a lemma nested in the proof)", () => {
  const NESTED = [
    "\\documentclass{article}", // 1
    "\\usepackage{amsthm}", // 2
    "\\newtheorem{theorem}{Theorem}", // 3
    "\\newtheorem{lemma}{Lemma}", // 4
    "\\begin{document}", // 5
    "\\begin{theorem}\\label{thm:a}", // 6
    "The estimator is consistent.", // 7
    "\\end{theorem}", // 8
    "\\begin{proof}", // 9
    "We first need a bound.", // 10
    "\\begin{lemma}\\label{lem:in}", // 11
    "The event $E$ has probability at least $1/2$.", // 12
    "\\end{lemma}", // 13
    "\\begin{proof}", // 14
    "The event $E$ holds when $X \\le 1$. Hence it has probability $1/2$.", // 15
    "\\end{proof}", // 16
    "The theorem follows from Lemma~\\ref{lem:in}.", // 17
    "\\end{proof}", // 18
    "\\end{document}", // 19
  ].join("\n");
  const PROOF = NESTED.split("\n").slice(9, 17).join("\n");
  const nested = (ops: unknown[], over: Partial<AnnotationInput> = {}): AnnotationInput => {
    const base = input();
    const thm = { ...(base.envs as unknown as { envs: Array<Record<string, unknown>> }).envs[0]!, lines: { file: "main.tex", from: 6, to: 8 }, proof: PROOF, proofLines: { file: "main.tex", from: 9, to: 18, env: "proof" } };
    const st = core().statements[0]!;
    const c = { ...core(), statements: [{ ...st, tex_locator: { ...st.tex_locator, from: 6, to: 8 } }] } as Core;
    return {
      ...base,
      files: { "main.tex": NESTED },
      flatText: NESTED,
      lineMap: NESTED.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 })),
      envs: { ...(base.envs as object), newtheorem: { theorem: "theorem", lemma: "lemma" }, envs: [thm] } as never,
      transcribed: c,
      core: c,
      patches: { patches: [{ node: "thm:a", corrected_statement: null, proof_note: "derived", ops: ops as never }], unfixable: [] },
      paperErrors: { "thm:a": { detail: "the bound on the event is not shown", witness: null } },
      ...over,
    };
  };
  /** Unit 3: "\end{lemma} \begin{proof} The event … X \le 1$." — it closes the lemma and opens its proof. */
  const STEP = "\\end{lemma}\n\\begin{proof}\nThe event $E$ holds when $X \\le 1$, by Markov's inequality.";
  const out = (inp: AnnotationInput): string => applyEdits(NESTED, planAnnotations(inp).edits["main.tex"] ?? []);

  it("the render check compiles the step balanced like the unit; the paper prints it as written", () => {
    const plan = planAnnotations(nested([{ op: "replace", unit: "thm:a/proof/1/3", tex: STEP }]));
    expect(plan.fragments).toContainEqual({ kind: "step", text: `\\begin{lemma}${STEP}\\end{proof}` });
    expect(plan.fragments.some((f) => f.text === STEP)).toBe(false);
    expect(plan.defects).toEqual([]);
    // a verdict on the balanced text is the step's
    const failed = planAnnotations({ ...nested([{ op: "replace", unit: "thm:a/proof/1/3", tex: STEP }]), texVerdicts: new Map([[`step\u0000\\begin{lemma}${STEP}\\end{proof}`, "Undefined control sequence."]]) });
    expect(failed.defects.map((d) => d.fragment?.text)).toEqual([STEP]);
  });

  it("only the text between the environment markers is marked; the markers stand once, as printed", () => {
    const text = out(nested([{ op: "replace", unit: "thm:a/proof/1/3", tex: STEP }]));
    expect(text).toContain("\\end{lemma}\n\\begin{proof}\n\\vsStep{The event $E$ holds when $X \\le 1$.} \\vsCorrectedStep{The event $E$ holds when $X \\le 1$, by Markov's inequality.} Hence");
    expect(text.match(/\\begin\{proof\}/gu)).toHaveLength(2);
    expect(text.match(/\\end\{lemma\}/gu)).toHaveLength(1);
  });

  it("a range op over the lemma and its proof's first sentence: each segment paired with its own, one left as printed not marked", () => {
    const tex = "\\begin{lemma}\\label{lem:in}\nThe event $E$ has probability at least $1/4$.\n\\end{lemma}\n\\begin{proof}\nThe event $E$ holds when $X \\le 1$.";
    const text = out(nested([{ op: "replace", unit: "thm:a/proof/1/2", to: "thm:a/proof/1/3", tex }]));
    expect(text).toContain("\\begin{lemma}\\label{lem:in}\n\\vsStep{The event $E$ has probability at least $1/2$.} \\vsCorrectedStep{The event $E$ has probability at least $1/4$.}\n\\end{lemma}\n\\begin{proof}\nThe event $E$ holds when $X \\le 1$. Hence");
    // the corrected view replaces the printed segment by its correction
    const view = applyEdits(NESTED, planAnnotations({ ...nested([{ op: "replace", unit: "thm:a/proof/1/2", to: "thm:a/proof/1/3", tex }]), correctedView: true }).edits["main.tex"] ?? []);
    const corrected = correctedTex(view, { proofEnv: true }).tex;
    expect(corrected).toContain("\\begin{lemma}\\label{lem:in}\nThe event $E$ has probability at least $1/4$.\n\\end{lemma}");
    expect(corrected).toContain("at least $1/4$.");
    expect(corrected).not.toContain("at least $1/2$.");
  });

  it("the corrected view carries each label once: one the correction moves inside its segment, to another segment, or keeps in the fallback", () => {
    const labelCount = (tex: string): number => {
      const view = applyEdits(NESTED, planAnnotations({ ...nested([{ op: "replace", unit: "thm:a/proof/1/2", to: "thm:a/proof/1/3", tex }]), correctedView: true }).edits["main.tex"] ?? []);
      return correctedTex(view, { proofEnv: true }).tex.match(/\\label\{lem:in\}/gu)?.length ?? 0;
    };
    const proofHead = "\\end{lemma}\n\\begin{proof}\nThe event $E$ holds when $X \\le 1$.";
    expect(labelCount(`\\begin{lemma}\nThe event $E$\\label{lem:in} has probability at least $1/4$.\n${proofHead}`)).toBe(1);
    expect(labelCount(`\\begin{lemma}\nThe event $E$ has probability at least $1/4$.\n\\end{lemma}\n\\begin{proof}\\label{lem:in}\nThe event $E$ holds when $X \\le 1$, surely.`)).toBe(1);
    // the inner proof's \begin dropped: the fallback, the correction (balanced) after the last segment
    expect(labelCount("\\begin{lemma}\\label{lem:in}\nThe event $E$ has probability at least $1/4$.\n\\end{lemma}\nThe event $E$ holds when $X \\le 1$.")).toBe(1);
  });

  it("markers the correction does not keep: the printed segments red, the correction after the last one (verbatim when it crosses environments itself)", () => {
    const tex = "The event $E$ holds when $X \\le 1$, by Markov's inequality.\n\\begin{proof}";
    const text = out(nested([{ op: "replace", unit: "thm:a/proof/1/3", tex }]));
    expect(text).toContain("\\end{lemma}\n\\begin{proof}\n\\vsStep{The event $E$ holds when $X \\le 1$.} \\vsCorrectedStep{\\texttt{The event");
  });

  const hasPdflatex = findExecutable("pdflatex", { nativeOnly: true }) !== null;
  it.skipIf(!hasPdflatex)("the annotated paper compiles with pdflatex", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "nested-proof-"));
    try {
      const range = "\\begin{lemma}\\label{lem:in}\nThe event $E$ has probability at least $1/4$.\n\\end{lemma}\n\\begin{proof}\nThe event $E$ holds when $X \\le 1$.";
      const cases = [
        ["single", [{ op: "replace", unit: "thm:a/proof/1/3", tex: STEP }]],
        ["range", [{ op: "replace", unit: "thm:a/proof/1/2", to: "thm:a/proof/1/3", tex: range }]],
        ["fallback", [{ op: "replace", unit: "thm:a/proof/1/3", tex: "The event $E$ holds when $X \\le 1$.\n\\begin{proof}" }]],
      ] as const;
      for (const [name, ops] of cases) {
        const out = path.join(dir, name);
        await mkdir(out, { recursive: true });
        await writeFile(path.join(out, "main.tex"), injectPreamble(applyEdits(NESTED, planAnnotations(nested([...ops])).edits["main.tex"] ?? []), false).tex, "utf8");
        let log = "";
        try {
          log = execFileSync("pdflatex", ["-interaction=nonstopmode", "-halt-on-error", "main.tex"], { cwd: out, encoding: "utf8" });
        } catch (e) {
          log = String((e as { stdout?: string }).stdout ?? e);
        }
        expect(log.split("\n").filter((l) => l.startsWith("!"))).toEqual([]);
        expect(existsSync(path.join(out, "main.pdf"))).toBe(true);
      }
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  }, 120_000);
});

describe("a statement whose units the paper cuts across an environment (a minipage in its body)", () => {
  const MINI = [
    "\\documentclass{article}", // 1
    "\\usepackage{amsthm}", // 2
    "\\newtheorem{theorem}{Theorem}", // 3
    "\\begin{document}", // 4
    "\\begin{theorem}\\label{thm:m}", // 5
    "Let $x$ be given.", // 6
    "\\begin{minipage}{3cm}", // 7
    "Then $x \\le 1$. Hence $x \\le 2$.", // 8
    "\\end{minipage}", // 9
    "Assume $x \\ge 0$.", // 10
    "\\end{theorem}", // 11
    "\\end{document}", // 12
  ].join("\n");
  const BODY = MINI.split("\n").slice(5, 10).join("\n");
  const loc = { file: "main.tex", from: 5, to: 11 };
  const mini = (over: { statement?: Record<string, unknown>; assumptions?: unknown[]; patches?: unknown[]; paperErrors?: Record<string, unknown>; findings?: unknown[] }): AnnotationInput => {
    const base = input();
    const c = {
      ...core(),
      assumptions: over.assumptions ?? [],
      statements: [{ id: "thm:m", kind: "theorem", statement: BODY, depends_on: [], status: "to-prove", tex_locator: { ...loc, env: "theorem", label: "thm:m" }, ...over.statement }],
    } as unknown as Core;
    return {
      ...base,
      files: { "main.tex": MINI },
      flatText: MINI,
      lineMap: MINI.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 })),
      envs: { ...(base.envs as object), newtheorem: { theorem: "theorem" }, envs: [{ id: "thm:m", kind: "theorem", envName: "theorem", label: "thm:m", title: null, body: BODY, proof: null, proofLines: null, section: null, lines: loc, refs: [] }] } as never,
      transcribed: c,
      core: c,
      patches: { patches: (over.patches ?? []) as never, unfixable: [] },
      paperErrors: (over.paperErrors ?? { "thm:m": { detail: "the bound is too strong", witness: null } }) as never,
      findings: (over.findings ?? []) as never,
    };
  };
  const out = (inp: AnnotationInput): string => applyEdits(MINI, planAnnotations(inp).edits["main.tex"] ?? []);
  const STATEMENT_OP = { node: "thm:m", corrected_statement: null, proof_note: "p", ops: [{ op: "replace", unit: "thm:m/1/2", tex: "\\begin{minipage}{3cm}\nThen $x \\le 3$." }] };
  /** Unit 4 ("\end{minipage} Assume …") a hypothesis: the asserting units 1–3 leave the minipage open. */
  const HYP = { id: "asm:h", condition: "\\end{minipage}\nAssume $x \\ge 0$.", depends_on: [], tex_locator: { ...loc, env: "theorem" } };
  const UNREPAIRED = { statement: { depends_on: ["asm:h"] }, assumptions: [HYP], findings: [{ node: "thm:m", stage: "V1.5", kind: "refuted", detail: "the bound is too strong", witness: null, at: "2026-10-14T00:00:00.000Z" }] };
  /** A hypothesis printed on unit 2 repaired with a text crossing the minipage, over the statement's own mark. */
  const CLASH = {
    assumptions: [{ id: "asm:c", condition: "\\begin{minipage}{3cm}\nThen $x \\le 1$.", depends_on: [], tex_locator: { ...loc, env: "theorem" } }],
    patches: [{ ...STATEMENT_OP, ops: [{ op: "replace", unit: "thm:m/1/2", to: "thm:m/1/3", tex: "\\begin{minipage}{3cm}\nThen $x \\le 3$. Hence $x \\le 4$." }] }, { node: "asm:c", corrected_statement: "\\begin{minipage}{3cm}\nThen $x \\le 5$.", proof_note: "p" }],
    paperErrors: { "thm:m": { detail: "the bound is too strong", witness: null }, "asm:c": { detail: "the bound is too strong", witness: null } },
  };

  it("a statement op: the minipage's \\begin (with its argument) stands as printed, the sentence after it marked", () => {
    expect(out(mini({ patches: [STATEMENT_OP] }))).toContain("\\begin{minipage}{3cm}\n\\vsOriginal{Then $x \\le 1$.} \\vsCorrected{Then $x \\le 3$.} Hence");
  });

  it("an unrepaired error: its red run cut at the marker, nothing blue", () => {
    const text = out(mini(UNREPAIRED));
    expect(text).toContain("\\vsOriginal{Let $x$ be given.}\n\\begin{minipage}{3cm}\n\\vsOriginal{Then $x \\le 1$. Hence $x \\le 2$.}");
    expect(text).not.toContain("\\vsCorrected{");
  });

  it("a correction crossing environments placed after another node's mark (an overlap) is printed verbatim", () => {
    const text = out(mini(CLASH));
    expect(planAnnotations(mini(CLASH)).records.find((r) => r.node === "asm:c")?.extended).toContain("overlaps the span of thm:m; placed after it");
    expect(text).toContain("\\vsCorrected{\\texttt{\\textbackslash{}begin\\{minipage\\}\\{3cm\\} Then \\$x \\textbackslash{}le 5\\$.}}");
    expect(text.match(/\\begin\{minipage\}/gu)).toHaveLength(1);
  });

  const hasPdflatex = findExecutable("pdflatex", { nativeOnly: true }) !== null;
  it.skipIf(!hasPdflatex)("each compiles with pdflatex", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "minipage-"));
    try {
      for (const [name, inp] of [["statement", mini({ patches: [STATEMENT_OP] })], ["red", mini(UNREPAIRED)], ["clash", mini(CLASH)]] as const) {
        const build = path.join(dir, name);
        await mkdir(build, { recursive: true });
        await writeFile(path.join(build, "main.tex"), injectPreamble(out(inp), false).tex, "utf8");
        let log = "";
        try {
          log = execFileSync("pdflatex", ["-interaction=nonstopmode", "-halt-on-error", "main.tex"], { cwd: build, encoding: "utf8" });
        } catch (e) {
          log = String((e as { stdout?: string }).stdout ?? e);
        }
        expect(log.split("\n").filter((l) => l.startsWith("!"))).toEqual([]);
      }
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  }, 120_000);
});
