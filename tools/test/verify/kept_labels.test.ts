import { describe, expect, it } from "vitest";
import { applyEdits, planAnnotations } from "../../src/verify/annotated_paper.js";
import { correctedTex } from "../../src/verify/corrected_tex.js";
import { PaperUnits } from "../../src/verify/units.js";

// A label the replaced text carries, in the corrected paper: kept on a display that stays numbered,
// and never by itself the difference that makes a sentence a correction.
function paper(lines: string[], env: { from: number; to: number; body: [number, number] }) {
  const flat = lines.join("\n");
  const body = lines.slice(env.body[0], env.body[1]).join("\n");
  const core = { qid: "x", symbols: [], assumptions: [], definitions: [], statements: [{ id: "thm:a", kind: "theorem", statement: "s", depends_on: [], status: "to-prove", tex_locator: { file: "main.tex", from: env.from, to: env.to, env: "theorem", label: "thm:a" } }], target_estimand: "t", bibliography: [] };
  const envs = { main_file: "main.tex", files: ["main.tex"], newtheorem: { theorem: "theorem", corollary: "corollary" }, envs: [{ id: "thm:a", kind: "theorem", envName: "theorem", label: "thm:a", title: null, body, proof: null, proofLines: null, section: null, lines: { file: "main.tex", from: env.from, to: env.to }, refs: [] }], bibliography: [] };
  const units = PaperUnits.parse(flat, envs as never);
  const base = { files: { "main.tex": flat }, envs, flatText: flat, lineMap: lines.map((_, i) => ({ file: "main.tex", line: i + 1 })), refs: null, transcribed: core, core, paperErrors: { "thm:a": { detail: "d", witness: "w" } }, findings: [], review: null };
  const write = (patch: object, correctedView: boolean): string => applyEdits(flat, planAnnotations({ ...base, patches: { patches: [patch], unfixable: [] }, correctedView } as never).edits["main.tex"] ?? []);
  return { units: units.unitsOf("thm:a"), write };
}

describe("a label the replaced text carries", () => {
  it("stays on its numbered display when the repair splits the result (the statement is written whole)", () => {
    const p = paper([
      "\\documentclass{article}", "\\begin{document}",
      "\\begin{theorem}\\label{thm:a}",
      "The estimator is consistent, and",
      "\\begin{equation}\\label{eq:main}",
      "T_n \\to N(0,1).",
      "\\end{equation}",
      "If moreover $X$ is bounded then $T_n$ is bounded.",
      "\\end{theorem}",
      "By \\eqref{eq:main} we are done.",
      "\\end{document}",
    ], { from: 3, to: 9, body: [3, 8] });
    const corrected = "The estimator is strongly consistent, and\n\\begin{equation}\\label{eq:main}\nT_n \\to N(0,1).\n\\end{equation}";
    const patch = { node: "thm:a", corrected_statement: corrected, proof_note: "p", ops: [], corollaries: [{ title: null, statement: "If $X$ is bounded then $T_n$ is bounded.", follows: "By \\ref{thm:a}, done.", adds: null }] };
    const out = correctedTex(p.write(patch, true), { proofEnv: true, corollaryEnv: { name: "corollary", numbered: true } });
    expect(out.tex).toContain("\\begin{equation}\\label{eq:main}");
    expect(out.tex).not.toContain("equation*");
    expect(out.items.filter((i) => /eq:main/u.test(JSON.stringify(i)))).toEqual([]);
  });

  it("dropped by an op is no change: the sentence stays as printed, its label with it", () => {
    const p = paper([
      "\\documentclass{article}", "\\begin{document}",
      "\\begin{theorem}\\label{thm:a}",
      "Suppose $X$ is bounded, a condition we call (B)\\label{cond:b}.",
      "Then the estimator is consistent.",
      "\\end{theorem}",
      "By \\ref{cond:b} we are done.",
      "\\end{document}",
    ], { from: 3, to: 6, body: [3, 5] });
    const ops = [
      { op: "replace", unit: p.units[1]!.id, tex: "Then the estimator is strongly consistent." },
      { op: "replace", unit: p.units[0]!.id, tex: "Suppose $X$ is bounded, a condition we call (B)." },
    ];
    const patch = { node: "thm:a", corrected_statement: null, proof_note: "unchanged", ops };
    const annotated = p.write(patch, false);
    expect(annotated).toContain("Suppose $X$ is bounded, a condition we call (B)\\label{cond:b}.");
    expect(annotated.match(/\\vsOriginal\{/gu)?.length).toBe(1);
    expect(correctedTex(p.write(patch, true), { proofEnv: true }).tex).toContain("(B)\\label{cond:b}.\nThen the estimator is strongly consistent.");
  });
});
