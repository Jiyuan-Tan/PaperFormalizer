import { describe, expect, it } from "vitest";
import {
  DEFECT_KINDS,
  KIND_FIELDS,
  OWNER_EXPLANATION_JSON,
  explanationParts,
  isOwnerFacing,
  nodeIdMentions,
  noteProblems,
  NOTE_FIELDS_TEXT,
  FIXER_INSTRUCTIONS,
  withoutFixerInstructions,
  noteProse,
  ownerExplanation,
  ownerFacing,
  paperLabels,
  renderExplanation,
  resultWord,
  stepQuote,
  balancedBraces,
  type Defect,
  type OwnerExplanation,
} from "../../src/verify/owner_text.js";
import { ownerExplanationViolations } from "../../src/verify/stage_v1.js";
import { PatchFileSchema } from "../../src/verify/patches.js";
import { fitDisplays } from "../../src/verify/annotate_tex.js";

/** An out_of_domain defect (fields overridable). */
const defect = (over: Partial<Defect> = {}): Defect => ({ kind: "out_of_domain", step_unit: "thm:a/proof/1/1", uses: "$E(U \\mid W) = 0$", assumed_on: "the regression nuisance", applied_at: "a projection nuisance", detail: null, ...over });
/** A note meeting the contract (fields overridable). */
const note = (over: Partial<OwnerExplanation> = {}): OwnerExplanation => ({
  claim: "It claims the variance bound.",
  defects: [defect()],
  why: { objects: ["$X$ uniform on $[0,1]$", "$f(x) = x^{-1/2}$"], consequence: "$E\\{f(X)^2\\} = \\infty$, while the statement bounds it by $4$" },
  fix: "The bound is weakened to what survives.",
  gives_up: "the lower bound",
  ...over,
});
const UNITS: Record<string, string> = {
  "thm:a/proof/1/1": "We have $E(U \\mid W) = 0$ for every nuisance.",
  "thm:a/1/1": "Then $\\sigma^2 \\leq 4$.",
};
const quoteOf = (id: string): string | null => UNITS[id] ?? null;

describe("ownerFacing — the backstop filter for text the paper's author reads", () => {
  it("drops every sentence naming a node id or a pipeline word, keeps the rest", () => {
    const text =
      "The missing direct edge to ass:berry-iid-moments is harmless: lem:berry is invoked with the i.i.d. oracle summands. " +
      "The paper's proof treats the training-dependent Δ as a fixed threshold. The random bound is false.";
    expect(ownerFacing(text)).toBe("The paper's proof treats the training-dependent Δ as a fixed threshold. The random bound is false.");
    for (const id of ["thm:main", "lem:x", "prop:y", "def:z", "cor:w", "ass:a"]) expect(isOwnerFacing(`See ${id} for this.`)).toBe(false);
    for (const w of ["dependency edge", "wired", "wiring", "depends_on", "core.json", "core_json", "core node", "node_id", "transcription", "transcribed", "pipeline", "referee", "fixer", "scaffold"]) {
      expect(isOwnerFacing(`The ${w} matters here.`)).toBe(false);
    }
    // a graph's edges and nodes, or a game's core, are the paper's mathematics
    for (const s of ["Let $G$ have vertex set $[4]$, edge set $E$, and weight $1$ on every edge.", "Each node is sampled independently.", "The allocation lies in the core of the game.", "Add the missing edge $uv$, a direct edge from $u$ to $v$.", "Every node has a unique node ID.", "$H$ is a core graph."]) {
      expect(isOwnerFacing(s)).toBe(true);
    }
    expect(isOwnerFacing("The variance bound ignores the cross term.")).toBe(true);
    expect(isOwnerFacing("The scorecard is fine.")).toBe(true); // a word that merely contains one is kept
  });
});

describe("the note is fields (design 2026-09-25, P3): one schema for every producer", () => {
  it("the reply schema: claim, defects (kind, step_unit and the TeX fields, all required, nullable), why {objects, consequence}, fix, gives_up", () => {
    const j = OWNER_EXPLANATION_JSON as { required: string[]; properties: Record<string, { items?: { required: string[]; properties: { kind: { enum: string[] } } }; required?: string[] }> };
    expect(j.required).toEqual(["claim", "defects", "why", "fix", "gives_up"]);
    expect(j.properties.defects!.items!.required).toEqual(["kind", "step_unit", "uses", "assumed_on", "applied_at", "detail"]);
    expect(j.properties.defects!.items!.properties.kind.enum).toEqual([...DEFECT_KINDS]);
    expect(j.properties.why!.required).toEqual(["objects", "consequence"]);
    expect(KIND_FIELDS.out_of_domain).toEqual(["uses", "assumed_on", "applied_at"]);
    for (const k of DEFECT_KINDS.filter((k) => k !== "out_of_domain")) expect(KIND_FIELDS[k]).toEqual(["detail"]);
    expect(noteProblems(note())).toEqual([]);
  });

  it.each([
    ["an out_of_domain defect without applied_at", defect({ applied_at: null }), "has no `defects[0].applied_at` — a out_of_domain defect gives uses, assumed_on, applied_at"],
    ["an out_of_domain defect carrying detail", defect({ detail: "extra" }), "gives `defects[0].detail`, which a out_of_domain defect does not carry"],
    ["another kind without its detail", { kind: "missing_hypothesis", step_unit: "thm:a/proof/1/1", uses: null, assumed_on: null, applied_at: null, detail: " " } as Defect, "has no `defects[0].detail`"],
  ] as Array<[string, Defect, string]>)("each kind requires its fields and carries no other: %s", (_t, d, problem) => {
    expect(noteProblems(note({ defects: [d] }))).toEqual([expect.stringContaining(problem)]);
  });

  it("exact checks on the fields: the step a unit of the node, objects and a consequence present, node ids and TeX per field; content is the judges' call", () => {
    const units = new Set(["thm:a/proof/1/1", "thm:a/1/1"]);
    expect(noteProblems(note(), { units })).toEqual([]);
    expect(noteProblems(note({ defects: [defect({ step_unit: "thm:b/proof/1/1" })] }), { units })).toEqual([expect.stringContaining('`defects[0].step_unit` ("thm:b/proof/1/1") is not a unit of this result')]);
    expect(noteProblems(note({ why: { objects: [], consequence: "c" } }))).toEqual([expect.stringContaining("has no `why.objects`")]);
    expect(noteProblems(note({ why: { objects: ["$n = 1$"], consequence: " " } }))).toEqual([expect.stringContaining("has an empty `why.consequence`")]);
    expect(noteProblems(note({ why: { objects: ["in half the pairs both outcomes equal one standard Normal draw"], consequence: "c" } }))).toEqual([]);
    expect(noteProblems(note({ gives_up: null }))).toEqual([]);
    // a note with no defect: wording the paper leaves open is one (a fixer repairing an ambiguity read none)
    expect(noteProblems(note({ defects: [] }))).toEqual([expect.stringMatching(/has no `defects`.*a phrase that admits more than one reading is one \(kind other/)]);
    expect(NOTE_FIELDS_TEXT).toContain("a phrase of the statement that admits more than one reading (the readings a finding names) is one, kind other");
    expect(noteProblems(note({ claim: "See thm:local-clause." }))).toEqual([expect.stringContaining("names node ids in `claim`")]);
    expect(noteProblems(note({ defects: [defect({ uses: "E(U | W) = 0 with σ" })] }))[0]).toContain("`defects[0].uses`");
  });

  it("free prose and the form before fields are refused", () => {
    expect(noteProblems("It claims X. It fails.")).toEqual([expect.stringContaining("is free prose")]);
    expect(noteProblems({ claim: "c", what_is_wrong: "Step: x. It uses: y which the paper assumes only on: z. But the step applies it at: w.", why: "w", fix: "f", gives_up: null })[0]).toContain("is not the object {claim, defects, why, fix, gives_up}");
  });
});

describe("the prose is generated from the fields, in one place (noteProse)", () => {
  it("per kind: the step quoted from its unit, then one plain sentence", () => {
    const q = "``We have $E(U \\mid W) = 0$ for every nuisance.''";
    expect(noteProse(note(), quoteOf).what_is_wrong).toEqual([`${q} This step uses $E(U \\mid W) = 0$, which the paper assumes only for the regression nuisance, but applies it to a projection nuisance.`]);
    const d = (kind: Defect["kind"], detail: string, step_unit = "thm:a/proof/1/1"): string => noteProse(note({ defects: [{ kind, step_unit, uses: null, assumed_on: null, applied_at: null, detail }] }), quoteOf).what_is_wrong[0]!;
    // Every kind but out_of_domain prints its detail as the complete sentence it is (no frame).
    expect(d("undefined_case", "The step divides by $\\hat\\sigma_0$, which is zero with positive probability.")).toBe(`${q} The step divides by $\\hat\\sigma_0$, which is zero with positive probability.`);
    expect(d("missing_hypothesis", "the step needs $E(U \\mid W) = 0$, which the statement does not assume")).toBe(`${q} The step needs $E(U \\mid W) = 0$, which the statement does not assume.`);
    expect(d("dropped_case", "The statement omits the case $n = 1$.", "thm:a/1/1")).toBe("``Then $\\sigma^2 \\leq 4$.'' The statement omits the case $n = 1$.");
    expect(d("other", "the two displays use one symbol for two quantities.")).toBe(`${q} The two displays use one symbol for two quantities.`);
    // An unknown unit is not quoted.
    expect(d("undefined_case", "The quotient is undefined at $n = 0$.", "thm:a/proof/9/9")).toBe("The quotient is undefined at $n = 0$.");
  });

  it("each step is quoted once: a later defect in it names the earlier one; a slot's leading article continues the sentence", () => {
    const q = "``We have $E(U \\mid W) = 0$ for every nuisance.''";
    const at = (kind: Defect["kind"], detail: string | null, uses: string | null = null) => ({ kind, step_unit: "thm:a/proof/1/1", uses, assumed_on: uses ? "the regression nuisance" : null, applied_at: uses ? "a projection nuisance" : null, detail });
    const w = noteProse(note({ defects: [at("undefined_case", "The quotient is undefined at $n = 0$."), at("other", "The display drops a factor."), at("out_of_domain", null, "The order bounds")] }), quoteOf).what_is_wrong;
    expect(w).toEqual([
      `${q} The quotient is undefined at $n = 0$.`,
      "In the step quoted in (a): The display drops a factor.",
      "The step quoted in (a) uses the order bounds, which the paper assumes only for the regression nuisance, but applies it to a projection nuisance.",
    ]);
  });

  it("the author's view filters the fields, never the paper's quote", () => {
    const graph: Record<string, string> = { "thm:a/proof/1/1": "The edge from $D$ to $Y$ is in the core graph." };
    const parts = explanationParts(note(), { quoteOf: (id) => graph[id] ?? null });
    expect(parts.find((p) => p.label === "What is wrong")!.text).toContain("``The edge from $D$ to $Y$ is in the core graph.''");
    // a field naming a node id drops (the backstop), and with it the sentence that needs it: the
    // counterexample alone is left under "What is wrong"
    const dropped = explanationParts(note({ defects: [defect({ uses: "thm:x-clause" })] })).find((p) => p.label === "What is wrong")!;
    expect(dropped.items).toEqual([expect.stringMatching(/^Counterexample: /u)]);
    expect(renderExplanation(note(), { quoteOf })).toContain("What is wrong: ``We have");
    expect(ownerExplanation({ owner_explanation: note(), detail: "d", witness: null })).toContain("What is wrong: This step uses");
  });

  it("a counterexample graph given by its vertices and edges reaches the note (live CKL thm:gw, 2026-10-14: dropped, the referee asked three rounds for the graphs)", () => {
    const graph = "Let $G$ have vertex set $[4]$, edge set $E=\\{\\{i,j\\}:1\\leq i<j\\leq4\\}$, and weight $w_e=1$ on every edge";
    expect(renderExplanation(note({ why: { objects: [graph], consequence: "column rounding returns the all-positive cut with probability $1/8$" } }))).toContain(graph);
  });
});

describe("stepQuote: the unit's printed text, whole by construction", () => {
  it("a group the paper opens in this step and closes in a later one is closed; a } closing an earlier step's group is dropped", () => {
    // yang_ding_combine Thm for mat/proof/1/1: `\textcolor{black}{` over the whole proof
    expect(stepQuote("\\textcolor{black}{First, we express $n^{1/2}(\\hat\\tau-\\tau)$ as")).toBe("\\textcolor{black}{First, we express $n^{1/2}(\\hat\\tau-\\tau)$ as}");
    expect(stepQuote("which ends the proof.}")).toBe("which ends the proof.");
    expect(balancedBraces("a \\{ b \\} {c}")).toBe("a \\{ b \\} {c}");
    // a unit ending in a control space: its space is trimmed, the lone `\` must not escape the closing }
    expect(stepQuote("{\\bf the estimator is robust\\ \n")).toBe("{\\bf the estimator is robust}");
    expect(balancedBraces("a line break \\\\")).toBe("a line break \\\\");
  });
  it("a display stays displayed as \\[…\\]; labels and tags go; a long unit is cut to its last clauses at a clause start outside mathematics, marked \\dots", () => {
    expect(stepQuote("we have\n$$\na = b \\label{eq:x}\n$$")).toBe("we have \\[ a = b \\]");
    // several rows stay rows (a core-LaTeX array), never one line past the margin
    expect(stepQuote("Hence \\begin{align*} a &= b \\\\ &\\leq c. \\end{align*}")).toBe("Hence \\[\\begin{array}{@{}c@{}}\\displaystyle a = b \\\\ \\displaystyle \\leq c.\\end{array}\\]");
    expect(stepQuote("So \\[ x \\tag{3} \\]")).toBe("So \\[ x \\]");
    // a long unit: cut at a clause start outside mathematics; none before the formula's end → the last clause, whole
    const head = `Since ${"$a_1 + a_2$ and ".repeat(12)}the rest hold, we have $x = y$.`;
    expect(stepQuote(head)).toBe("\\dots we have $x = y$.");
    // never at a comma inside a brace group: the cut left `Theorem 2.1}}` with braces that close nothing
    const cited = `${"Using the bound above and the assumption, ".repeat(8)}by {\\citetext{\\citealp{k}, Theorem 2.1}}, we have $x = y$.`;
    const balanced = (q: string) => (q.match(/\{/g) ?? []).length === (q.match(/\}/g) ?? []).length;
    expect(stepQuote(cited).endsWith("we have $x = y$.")).toBe(true);
    expect(balanced(stepQuote(cited))).toBe(true);
    expect(balanced(stepQuote(`${"word ".repeat(80)}{\\citetext{\\citealp{k}, Theorem 2.1}} holds`))).toBe(true);
    expect(stepQuote(`${"word ".repeat(80)}{\\citetext{\\citealp{k}, Theorem 2.1}} holds`)).not.toMatch(/^\\dots Theorem/);
    const math = `We have $${"a + ".repeat(80)}b, c$, and so on.`;
    // no clause start outside mathematics before the formula's end: the last clause, whole
    expect(stepQuote(math)).toBe("\\dots and so on.");
    expect(stepQuote(`$${"a, ".repeat(100)}b$`)).toBe(`$${"a, ".repeat(100)}b$`);
  });
});

describe("the nine note-shape false positives of 2026-09-25/26 are gone (fields, not templates)", () => {
  const DISPLAY_UNITS = new Set(["thm:a/proof/1/3"]);
  it.each([
    ['"applies it to" / "applies them": no wording is parsed — the sentence is generated', note({ defects: [defect({ uses: "Lemmas~\\ref{a} and~\\ref{b}", applied_at: "the joint contrast of complementary arms" })] }), undefined],
    ["a quote at an aligned row: the quote is the whole unit, never checked against boundaries", note({ defects: [defect({ step_unit: "thm:a/proof/1/3" })] }), DISPLAY_UNITS],
    ['"= 1/4 \\ne 0": a consequence is never parsed by keywords', note({ why: { objects: ["$D, Z \\in \\{-1, 1\\}$"], consequence: "$E[m(W,\\gamma)] = 1/4 \\ne 0$" } }), undefined],
  ] as Array<[string, OwnerExplanation, Set<string> | undefined]>)("%s", (_t, n, units) => {
    expect(noteProblems(n, units ? { units } : undefined)).toEqual([]);
  });
});

describe("the fixer's owner_explanation", () => {
  const file = (over: object) => PatchFileSchema.parse({ key_results: ["thm:a"], key_contribution: "c", patches: [], unfixable: [], ...over });
  const patch = (owner_explanation?: unknown) => ({ node: "thm:a", corrected_statement: null, add_assumptions: [], remove_depends_on: [], proof_note: "p", ...(owner_explanation === undefined ? {} : { owner_explanation }) });

  it("is the note on every patch and unfixable entry the fixer writes; its steps among the node's units", () => {
    expect(ownerExplanationViolations(file({ patches: [patch()] }), null)).toEqual([expect.stringContaining("has no `owner_explanation`")]);
    expect(ownerExplanationViolations(file({ patches: [patch("It claims X. It fails.")] }), null)).toEqual([expect.stringContaining("is free prose")]);
    expect(ownerExplanationViolations(file({ patches: [patch(note({ claim: "It claims X; see lem:b." }))] }), null)).toEqual([expect.stringContaining("names node ids in `claim`")]);
    expect(ownerExplanationViolations(file({ patches: [patch(note({ gives_up: "" }))] }), null)).toEqual([expect.stringContaining("empty `gives_up`")]);
    expect(ownerExplanationViolations(file({ patches: [patch(note())] }), null)).toEqual([]);
    expect(ownerExplanationViolations(file({ patches: [patch(note())] }), null, undefined, undefined, () => new Set(["thm:a/1/1"]))).toEqual([expect.stringContaining("is not a unit of this result")]);
    expect(ownerExplanationViolations(file({ unfixable: [{ node: "thm:a", reason: "r", suggested_repair: null }] }), null)).toEqual([expect.stringContaining("unfixable entry")]);
  });
});

describe("the node-id rule: the paper's own references are no node-id mention", () => {
  const labels = paperLabels("\\begin{theorem}\\label{thm:local} A. \\end{theorem}\n\\begin{corollary}\\label{cor:CI} B.\\end{corollary}\n\\label{cor:CI_local} \\label{thm:var}");

  it.each([
    ["never counts the argument of a reference macro", "See \\eqref{eq:a}, \\cref{lem:rp-alt1}, \\Cref{thm:x,thm:y}, \\autoref{prop:z}, \\cite[Thm.~2]{lem:q}, \\hyperref[thm:w]{here}.", false, []],
    ["counts a bare pipeline-minted id, matched whole", "The clause thm:local-local-clause fails.", true, ["thm:local-local-clause"]],
    ["lets a bare label of the paper through when the labels are known; no prefix matching", "Corollary cor:CI_local asserts coverage.", true, []],
  ] as Array<[string, string, boolean, string[]]>)("%s", (_t, text, withLabels, ids) => {
    expect(nodeIdMentions(text, withLabels ? labels : undefined)).toEqual(ids);
  });
});

describe("a result is named by the word its printed environment stands for", () => {
  it("a corollary the core records as a theorem is a Corollary; a short environment name is its word; else the kind", () => {
    expect(resultWord({ kind: "theorem", tex_locator: { env: "corollary" } })).toBe("Corollary");
    expect(resultWord({ kind: "theorem", tex_locator: { env: "thm" } })).toBe("Theorem");
    expect(resultWord({ tex_locator: { env: "algorithm" } })).toBe("Algorithm");
    expect(resultWord({ tex_locator: { env: "algorithmic" } })).toBe("Algorithm");
    expect(resultWord({ kind: "proposition", tex_locator: { env: "prop*" } })).toBe("Proposition");
    expect(resultWord({ kind: "lemma", tex_locator: { env: "mystery" } })).toBe("Lemma");
    expect(resultWord({ kind: "theorem", tex_locator: { env: "main" } }, { main: "theorem" })).toBe("Theorem");
    // an environment the map knows only as "other" falls back to the recorded kind
    expect(resultWord({ kind: "proposition", tex_locator: { env: "conj" } }, { conj: "other" })).toBe("Proposition");
  });
});

describe("fitDisplays: each display of a text we write fitted to the line", () => {
  it("fits $$ and \\[ displays found by the TeX parser; leaves \\\\[2pt], adjacent inline math and \\eqno displays", () => {
    expect(fitDisplays("We have $$ a = b $$ as claimed.")).toBe("We have \\vsFit{a = b} as claimed.");
    expect(fitDisplays("Then \\[ x \\to y \\] holds.")).toBe("Then \\vsFit{x \\to y} holds.");
    expect(fitDisplays("\\begin{align*} a &= b \\\\[2pt] c &= d \\end{align*}")).toBe("\\begin{align*} a &= b \\\\[2pt] c &= d \\end{align*}");
    expect(fitDisplays("For $i$$j$ we have $$ a=b $$ done")).toBe("For $i$$j$ we have \\vsFit{a=b} done");
    expect(fitDisplays("$$ a=b \\eqno(3.1) $$")).toBe("$$ a=b \\eqno(3.1) $$");
    // a display touching a comment is left as printed
    expect(fitDisplays("% old \\[ x\nThen \\[ y \\] z")).toBe("% old \\[ x\nThen \\[ y \\] z");
  });
});

describe("the runner's instructions to the fixer stay out of what the author reads", () => {
  it("are removed from a finding's detail an author-facing note quotes", () => {
    const d = `the repair is confirmed, but its note for the paper's author is unclear: it never defines $G'$. ${FIXER_INSTRUCTIONS.noteRewrite}\nThe error of the paper this node still answers: the bound fails.`;
    const out = withoutFixerInstructions(d);
    expect(out).not.toContain("owner_explanation");
    expect(out).toContain("it never defines $G'$.");
    // the label before the paper's error goes, the error stays (with "node" in it the whole sentence was dropped)
    expect(out).not.toContain("this node still answers");
    expect(out).toContain("the bound fails.");
    expect(withoutFixerInstructions(`no longer follows: x. ${FIXER_INSTRUCTIONS.consequence}`)).toBe("no longer follows: x.");
  });
});

