// The rules of the V1 transcription lint, one violation at a time.
//
// The fixture is a miniature paper: two theorems (one proved in an appendix), a lemma with
// no proof, an assumption environment stating two conditions, a definition, and an
// `algorithmv` estimator environment. `passingCore()` is a faithful transcription of it;
// each test perturbs exactly one thing and asserts the rule letter that must fire.
import { describe, expect, it } from "vitest";
import { CoreSchema, type Core } from "../../src/core/schema.js";
import { invokesRef, lintTranscription } from "../../src/verify/transcription_lint.js";
import type { EnvsJson, TexEnv } from "../../src/verify/types.js";

function loc(file: string, from: number, to: number, env: string, label: string | null): TexEnv["lines"] {
  return { file, from, to, env, label };
}

const DEF_BODY = "\\label{def:kernel}\nThe kernel \\(K\\) is the map \\(x \\mapsto k(x)\\).";
const ASS_BODY =
  "\\label{ass:overlap}\nOverlap holds: \\(e(X) \\in (0,1)\\) almost surely. The density of \\(X\\) is bounded.";
const ALG_BODY = "\\label{alg:est}\nCompute \\(\\hat\\tau = n^{-1}\\sum_i \\psi_i\\).";
const THM_MAIN_BODY = "\\label{thm:main}\nUnder \\cref{ass:overlap}, \\(\\hat\\tau\\) is consistent.";
const THM_MAIN_PROOF = "Apply the law of large numbers to \\(\\psi_i\\).";
const THM_RATE_BODY = "\\label{thm:rate}\nThe estimator converges at rate \\(n^{-1/2}\\).";
const THM_RATE_PROOF = "A central limit theorem for \\(\\psi_i\\).";
const LEM_BODY = "\\label{lem:bound}\nThe influence function is bounded.";

const ENVS: EnvsJson = {
  main_file: "main.tex",
  files: ["main.tex", "appendix.tex"],
  newtheorem: {
    thm: "theorem",
    lem: "lemma",
    assump: "assumption",
    defn: "definition",
    algorithmv: "other",
  },
  bibliography: [{ key: "vdv1998", text: "van der Vaart, A. W. (1998). Asymptotic Statistics." }],
  envs: [
    {
      id: "def:kernel",
      kind: "definition",
      envName: "defn",
      label: "def:kernel",
      title: "Kernel",
      body: DEF_BODY,
      proof: null,
      proofLines: null,
      lines: loc("main.tex", 10, 13, "defn", "def:kernel"),
      refs: [],
    },
    {
      id: "ass:overlap",
      kind: "assumption",
      envName: "assump",
      label: "ass:overlap",
      title: "Overlap",
      body: ASS_BODY,
      proof: null,
      proofLines: null,
      lines: loc("main.tex", 15, 19, "assump", "ass:overlap"),
      refs: [],
    },
    {
      id: "alg:est",
      kind: "other",
      envName: "algorithmv",
      label: "alg:est",
      title: "The estimator",
      body: ALG_BODY,
      proof: null,
      proofLines: null,
      lines: loc("main.tex", 21, 25, "algorithmv", "alg:est"),
      refs: [],
    },
    {
      id: "thm:main",
      kind: "theorem",
      envName: "thm",
      label: "thm:main",
      title: null,
      body: THM_MAIN_BODY,
      proof: THM_MAIN_PROOF,
      proofLines: loc("appendix.tex", 3, 6, "proof", null),
      lines: loc("main.tex", 30, 34, "thm", "thm:main"),
      refs: ["ass:overlap"],
    },
    {
      id: "thm:rate",
      kind: "theorem",
      envName: "thm",
      label: "thm:rate",
      title: null,
      body: THM_RATE_BODY,
      proof: THM_RATE_PROOF,
      proofLines: loc("main.tex", 42, 44, "proof", null),
      lines: loc("main.tex", 37, 40, "thm", "thm:rate"),
      refs: [],
    },
    {
      id: "lem:bound",
      kind: "lemma",
      envName: "lem",
      label: "lem:bound",
      title: null,
      body: LEM_BODY,
      proof: null,
      proofLines: null,
      lines: loc("main.tex", 46, 49, "lem", "lem:bound"),
      refs: [],
    },
  ],
};

const SCOPE = ENVS.envs.map((e) => e.id);

/** `ENVS` with ONE environment's body replaced — for the rules that are about the source
 * text rather than about the core (a negated condition, an either/or, an empty body). */
function envsWithBody(id: string, body: string): EnvsJson {
  const copy = structuredClone(ENVS) as EnvsJson;
  const env = copy.envs.find((e) => e.id === id);
  if (!env) throw new Error(`fixture has no env ${id}`);
  env.body = body;
  return copy;
}

/** A faithful transcription of `ENVS`: the lint must pass on it unchanged. */
function passingCore(): Core {
  return {
    qid: "verify_lint_fixture",
    symbols: [],
    sampling_model: { main: "i.i.d. units (X, A, Y); the treatment A is random given X." },
    assumptions: [
      {
        id: "ass:overlap",
        condition: "Overlap holds: \\(e(X) \\in (0,1)\\) almost surely.",
        novel: { flag: true, justification: "the paper's own condition" },
        tex_locator: ENVS.envs[1].lines,
      },
      {
        id: "ass:density",
        condition: "The density of \\(X\\) is bounded.",
        novel: { flag: true, justification: "the paper's own condition" },
        tex_locator: ENVS.envs[1].lines,
      },
    ],
    definitions: [
      {
        id: "def:kernel",
        name: "Kernel",
        construction: "the map \\(x \\mapsto k(x)\\)",
        tex_locator: ENVS.envs[0].lines,
      },
      {
        id: "def:estimator",
        name: "The estimator",
        construction: "\\(\\hat\\tau = n^{-1}\\sum_i \\psi_i\\)",
        tex_locator: ENVS.envs[2].lines,
      },
    ],
    statements: [
      {
        id: "thm:main",
        kind: "theorem",
        statement: THM_MAIN_BODY,
        status: "to-prove",
        proof_tex: THM_MAIN_PROOF,
        // \cref{ass:overlap} is a `\ref` edge, so BOTH conditions transcribed from that
        // environment are dependencies (rule (g), forward direction).
        depends_on: ["ass:overlap", "ass:density"],
        tex_locator: ENVS.envs[3].lines,
      },
      {
        id: "thm:rate",
        kind: "theorem",
        statement: THM_RATE_BODY,
        status: "to-prove",
        proof_tex: THM_RATE_PROOF,
        depends_on: [],
        tex_locator: ENVS.envs[4].lines,
      },
      {
        id: "lem:bound",
        kind: "lemma",
        statement: LEM_BODY,
        status: "to-prove",
        depends_on: [],
        tex_locator: ENVS.envs[5].lines,
      },
    ],
    target_estimand: "the average treatment effect",
    bibliography: ENVS.bibliography.map((b) => ({ key: b.key, citation: b.text })),
  } as Core;
}

/** The blocking half of the lint, in phase `v1` unless a test says otherwise. */
function lint(
  core: Core,
  envs: EnvsJson = ENVS,
  scope: readonly string[] = SCOPE,
  phase: "v1" | "v1_5" = "v1",
  flatText?: string,
): string[] {
  return lintTranscription(core, envs, scope, { phase, flatText }).violations;
}

/** Rule letters present in a violation list, so an assertion names the rule, not a string. */
function letters(violations: string[]): string[] {
  return violations.map((v) => v.slice(0, v.indexOf(")") + 1));
}

describe("lintTranscription", () => {
  it("passes a faithful transcription, which is also a schema-valid core", () => {
    const core = passingCore();
    expect(() => CoreSchema.parse(core)).not.toThrow();
    expect(lintTranscription(core, ENVS, SCOPE, { phase: "v1" })).toEqual({
      violations: [],
      warnings: [],
    });
  });

  it("(s) every symbol has a space and a def, and the core a sampling model — the shape the F stages read (2026-09-30)", () => {
    const core = passingCore();
    core.symbols = [{ name: "e(x)", type: "propensity score", space: "$(0,1)$" }] as Core["symbols"];
    delete (core as { sampling_model?: unknown }).sampling_model;
    expect(lint(core)).toEqual(["(s) symbol e(x): no def", "(s) sampling_model: missing — one entry per setting the paper works in"]);
  });

  it("(s) a def that writes the symbol's own name does not thereby name the symbols inside it (live Yang–Ding: Y(a) and Y)", () => {
    const core = passingCore();
    core.symbols = [
      { name: "a", type: "treatment level", space: "$\\{0,1\\}$", def: "A treatment level." },
      { name: "Y(a)", type: "potential outcome", space: "$\\mathbb{R}$", def: "For each level $a$, $Y(a)$ is the outcome had the subject been given treatment $a$.", refs: ["a"] },
      { name: "Y", type: "observed outcome", space: "$\\mathbb{R}$", def: "$Y=Y(1)$ for the treated.", refs: [] },
    ] as Core["symbols"];
    expect(lint(core).filter((v) => v.startsWith("(s) symbol Y(a)"))).toEqual([]);
  });

  it("(s) a symbol's def names other symbols only through refs, its mathematics read (not its words)", () => {
    const core = passingCore();
    core.symbols = [
      { name: "a", type: "treatment level", space: "$\\{0,1\\}$", def: "A treatment level." },
      { name: "X", type: "covariates", space: "$\\mathbb{R}^d$", def: "The covariate vector." },
      { name: "e(x)", type: "propensity score", space: "$(0,1)$", def: "$e(x) = P(A = 1 \\mid X = x)$ for a unit with covariates $X$." },
    ] as Core["symbols"];
    expect(lint(core)).toEqual(["(s) symbol e(x): its def names X — list it in refs"]);
    core.symbols[2]!.refs = ["X"];
    expect(lint(core)).toEqual([]);
    // two symbols described through each other list each other, in whatever order: no (s) violation
    core.symbols = [
      { name: "L", type: "constant", space: "$(0,\\infty)$", def: "The Lipschitz constant of $g$.", refs: ["g"] },
      { name: "g", type: "link", space: "$\\mathbb{R}\\to\\mathbb{R}$", def: "The $L$-Lipschitz link.", refs: ["L"] },
    ] as Core["symbols"];
    expect(lint(core)).toEqual([]);
    core.symbols[1]!.refs = [];
    expect(lint(core)).toEqual(["(s) symbol g: its def names L — list it in refs"]);
  });

  it("allows an appended hypothesis list after the verbatim body", () => {
    const core = passingCore();
    core.statements[0].statement = `${THM_MAIN_BODY} [Hypotheses: ass:overlap, ass:density]`;
    expect(lint(core)).toEqual([]);
  });

  describe("(a) theorem-like environments", () => {
    // Each row is one part of a statement node the rule checks; each mutation inside a
    // row is a separate core, linted alone.
    it.each([
      {
        part: "the statement text (verbatim body, grammar-checked suffix)",
        cases: [
          { mutate: (c: Core) => { c.statements[0].statement = "The estimator is consistent under overlap."; }, expected: ["thm:main", "verbatim"] },
          { mutate: (c: Core) => { c.statements[0].statement = `${THM_MAIN_BODY} and \\(\\hat\\tau\\) is NOT asymptotically normal.`; }, expected: ["hypothesis", "asymptotically normal"] },
        ],
      },
      {
        part: "the proof body (rewritten, or written where the paper gives none)",
        cases: [
          { mutate: (c: Core) => { c.statements[0].proof_tex = "Apply the LLN."; }, expected: ["(a) thm:main"] },
          { mutate: (c: Core) => { c.statements[2].proof_tex = "Immediate from the triangle inequality."; }, expected: ["lem:bound", "NO proof"] },
        ],
      },
      {
        part: "the hypothesis list (a core node, and in depends_on)",
        cases: [
          {
            mutate: (c: Core) => {
              c.statements[0].statement = `${THM_MAIN_BODY} [Hypotheses: ass:ghost]`;
              c.statements[0].depends_on = [...c.statements[0].depends_on, "ass:ghost"];
            },
            expected: ["ass:ghost", "not an `ass:`/`def:` node"],
          },
          { mutate: (c: Core) => { c.statements[0].statement = `${THM_MAIN_BODY} [Hypotheses: ass:overlap, def:kernel]`; }, expected: ["def:kernel", "depends_on"] },
        ],
      },
    ])("rejects a faulty $part", ({ cases }) => {
      for (const { mutate, expected } of cases) {
        const core = passingCore();
        mutate(core);
        const violations = lint(core);
        expect(letters(violations)).toContain("(a)");
        for (const s of expected) expect(violations.join("\n")).toContain(s);
      }
    });
  });

  describe("(b) assumption environments", () => {
    it("rejects a condition that is not a verbatim slice of its environment", () => {
      const core = passingCore();
      core.assumptions[1].condition = "The density of \\(X\\) is bounded away from zero.";
      const violations = lint(core);
      expect(letters(violations)).toContain("(b)");
      expect(violations.join("\n")).toContain("ass:density");
    });

    // A verbatim slice that leaves the governing word behind.
    it.each([
      {
        governing: "'do not'",
        body: "\\label{ass:overlap}\nWe do not require that the density of \\(X\\) is bounded.",
        condition: "the density of \\(X\\) is bounded.",
      },
      {
        governing: "'either'",
        body: "\\label{ass:overlap}\nEither the density of \\(X\\) is bounded or the kernel \\(K\\) is Lipschitz.",
        condition: "the kernel \\(K\\) is Lipschitz.",
      },
    ])("rejects a slice that drops the governing $governing", ({ governing, body, condition }) => {
      const envs = envsWithBody("ass:overlap", body);
      const core = passingCore();
      core.assumptions = [
        {
          id: "ass:density",
          condition,
          novel: { flag: true, justification: "sliced out of its governing sentence" },
          tex_locator: ENVS.envs[1].lines,
        },
      ];
      core.statements[0].depends_on = ["ass:density"];
      const violations = lint(core, envs);
      expect(letters(violations)).toContain("(b)");
      expect(violations.join("\n")).toContain("ass:density");
      expect(violations.join("\n")).toContain(governing);
    });

    it("ignores a governing word inside a bracketed title that closes before the slice", () => {
      const envs = envsWithBody(
        "ass:overlap",
        "\\label{ass:overlap} {\\sc (No Testable Restrictions)} Suppose all units are exchangeable.",
      );
      const core = passingCore();
      core.assumptions = [
        {
          id: "ass:density",
          condition: "Suppose all units are exchangeable.",
          novel: { flag: true, justification: "after the title" },
          tex_locator: ENVS.envs[1].lines,
        },
      ];
      core.statements[0].depends_on = ["ass:density"];
      const result = lintTranscription(core, envs, SCOPE, { phase: "v1" });
      expect(result.violations.filter((v) => v.includes("governing"))).toEqual([]);
    });

    it("ignores a governing word that sits in a different clause of the sentence", () => {
      const envs = structuredClone(ENVS);
      envs.envs[1].body =
        "\\label{ass:overlap} The density \\(f\\) is continuous or piecewise continuous, and " +
        "\\(\\sigma^2 < \\infty\\). There is no interference between units: \\(Y_i(d) = Y_i(d_i)\\) for every \\(i\\).";
      const core = passingCore();
      core.assumptions = [
        {
          id: "ass:overlap",
          condition: "\\(\\sigma^2 < \\infty\\).",
          novel: { flag: true, justification: "own conjunct" },
          tex_locator: envs.envs[1].lines,
        },
        {
          id: "ass:density",
          condition: "\\(Y_i(d) = Y_i(d_i)\\) for every \\(i\\).",
          novel: { flag: true, justification: "after the colon" },
          tex_locator: envs.envs[1].lines,
        },
      ];
      core.statements[0].depends_on = ["ass:overlap", "ass:density"];
      const result = lintTranscription(core, envs, SCOPE, { phase: "v1" });
      expect(result.violations.filter((v) => v.includes("governing"))).toEqual([]);
    });
  });

  describe("(g) a result about an algorithm", () => {
    const aboutAlgorithm = () => {
      const envs = structuredClone(ENVS);
      const body = "\\label{thm:rate}\nThe output of Algorithm~\\ref{alg:est} converges at rate \\(n^{-1/2}\\).";
      envs.envs[4] = { ...envs.envs[4]!, body, refs: ["alg:est"] };
      const core = passingCore();
      core.statements[1] = { ...core.statements[1]!, statement: body };
      return { envs, core };
    };
    it("is pointed out to the referee when it does not depend on the algorithm's definition (a mention is the referee's call)", () => {
      const { envs, core } = aboutAlgorithm();
      const r = lintTranscription(core, envs, SCOPE, { phase: "v1" });
      expect(r.violations.filter((v) => v.includes("thm:rate"))).toEqual([]);
      expect(r.warnings.join("\n")).toMatch(/thm:rate: .*alg:est.*def:estimator/);
    });
    it("passes once it does", () => {
      const { envs, core } = aboutAlgorithm();
      core.statements[1]!.depends_on = ["def:estimator"];
      expect(lintTranscription(core, envs, SCOPE, { phase: "v1" }).warnings.filter((w) => w.startsWith("thm:rate") && w.includes("alg:est"))).toEqual([]);
    });
  });

  describe("(c) definition and algorithm environments", () => {
    it("rejects an algorithm environment with no definition node", () => {
      const core = passingCore();
      core.definitions = core.definitions.slice(0, 1);
      const violations = lint(core);
      expect(letters(violations)).toContain("(c)");
      expect(violations.join("\n")).toContain("alg:est");
    });
  });

  describe("(d) locators", () => {
    it.each([
      {
        fault: "no locator",
        mutate: (c: Core) => { delete c.definitions[0].tex_locator; },
        // the node named in the violation
        expected: ["(d)"], names: "def:kernel",
      },
      {
        fault: "a locator matching no environment (the lemma env then has no node: (a) fires too)",
        mutate: (c: Core) => { c.statements[2].tex_locator = loc("main.tex", 900, 901, "lem", "lem:bound"); },
        expected: ["(d)", "(a)"], names: "lem:bound",
      },
    ])("rejects a node with $fault", ({ mutate, expected, names }) => {
      const core = passingCore();
      mutate(core);
      const violations = lint(core);
      for (const l of expected) expect(letters(violations)).toContain(l);
      expect(violations.join("\n")).toContain(names);
    });
  });

  describe("(p) prose nodes", () => {
    const PROSE = { file: "flat.tex", from: 0, to: 0, env: "prose", label: null };
    const FLAT = "Throughout, let $\\gamma_0(w)=E(Y\\mid W=w)$ denote the regression.\n" + THM_MAIN_BODY;
    it("accepts a def/ass node sliced verbatim from the running text; rejects prose the paper does not write, a prose statement, and a missing flat text", () => {
      const good = passingCore();
      good.definitions.push({
        id: "def:gamma0",
        name: "regression function",
        construction: "let $\\gamma_0(w)=E(Y\\mid W=w)$ denote the regression",
        free_symbols: [],
        inputs: [],
        tex_locator: PROSE,
      });
      expect(lint(good, ENVS, SCOPE, "v1", FLAT)).toEqual([]);

      const core = passingCore();
      core.definitions.push({
        id: "def:gamma0",
        name: "regression function",
        construction: "the regression function is $E(Y\\mid W)$",
        free_symbols: [],
        inputs: [],
        tex_locator: PROSE,
      });
      expect(lint(core, ENVS, SCOPE, "v1", FLAT).join("\n")).toContain("(p) def:gamma0");
      expect(lint(core).join("\n")).toContain("supplied no flattened text");
      const bad = passingCore();
      bad.statements[0].tex_locator = PROSE;
      expect(lint(bad, ENVS, SCOPE, "v1", FLAT).join("\n")).toContain("(p) thm:main");
    });
  });

  describe("(e) cited leaves", () => {
    it("accepts a proof-less lemma env restated from the literature, and a cited node located where this paper invokes it (exempt from the text rules)", () => {
      const leaf = passingCore();
      leaf.statements[2].status = "cited";
      leaf.statements[2].source = { cite: "vdv1998", locator: "Lemma 2.1" };
      delete leaf.statements[2].proof_tex;
      expect(lint(leaf)).toEqual([]);

      const imported = passingCore();
      imported.statements.push({
        id: "thm:imported",
        kind: "theorem",
        statement: "Every uniformly integrable sequence converges in \\(L^1\\).",
        status: "cited",
        source: { cite: "vdv1998", locator: "Theorem 2.20" },
        depends_on: [],
        // Where THIS paper invokes it: inside the proof of thm:main.
        tex_locator: ENVS.envs[3].proofLines ?? undefined,
      });
      expect(lint(imported)).toEqual([]);
    });

    const IMPORTED = {
      id: "thm:imported",
      kind: "theorem",
      statement: "Every uniformly integrable sequence converges in \\(L^1\\).",
      status: "cited",
      depends_on: [] as string[],
    } as const;
    it.each([
      {
        fault: "at an environment the paper proves",
        mutate: (c: Core) => {
          c.statements[0].status = "cited";
          c.statements[0].source = { cite: "vdv1998", locator: "Theorem 1" };
        },
        rule: "(a)", expected: "PROVES this environment",
      },
      {
        fault: "naming no environment invoking it",
        mutate: (c: Core) => {
          c.statements.push({ ...IMPORTED, source: { cite: "vdv1998", locator: "Theorem 2.20" } } as Core["statements"][number]);
        },
        rule: "(d)", expected: "invokes it",
      },
      {
        fault: "with no source",
        mutate: (c: Core) => {
          c.statements.push({ ...IMPORTED, tex_locator: ENVS.envs[3].proofLines ?? undefined } as Core["statements"][number]);
        },
        rule: "(e)", expected: "thm:imported",
      },
    ])("rejects a cited node $fault", ({ mutate, rule, expected }) => {
      const core = passingCore();
      mutate(core);
      const violations = lint(core);
      expect(letters(violations)).toContain(rule);
      expect(violations.join("\n")).toContain(expected);
    });
  });

  describe("(f) scope", () => {
    it("rejects a node transcribed from an environment outside the scope, and reports a scope id that names no environment", () => {
      const narrowed = SCOPE.filter((id) => id !== "def:kernel");
      const violations = lint(passingCore(), ENVS, narrowed);
      expect(letters(violations)).toContain("(f)");
      expect(violations.join("\n")).toContain("def:kernel");
      expect(lint(passingCore(), ENVS, [...SCOPE, "thm:ghost"]).join("\n")).toContain("(scope) thm:ghost");
    });
  });

  describe("(r) pointers", () => {
    it("a \\ref to a label inside an environment's body (an \\item label) is not an unresolved pointer", () => {
      const core = passingCore();
      const envs = structuredClone(ENVS) as typeof ENVS;
      const ass = envs.envs.find((e) => e.id === "ass:overlap")!;
      ass.body = `${ass.body}\n\\begin{enumerate}\\item (Overlap) $p(x) \\ge p_{\\min}$. \\label{overlap-item}\\end{enumerate}`;
      const main = envs.envs.find((e) => e.id === "thm:main")!;
      main.body = "\\label{thm:main}\nUnder \\cref{ass:overlap} and \\ref{overlap-item}, \\(\\hat\\tau\\) is consistent.";
      core.statements[0].statement = core.statements[0].statement.replace(/^[\s\S]*?(?=\s*\[Hypotheses:|$)/, main.body.replace(/\\label\s*\{[^{}]*\}\s*/, ""));
      const result = lintTranscription(core, envs, SCOPE, { phase: "v1" });
      expect(result.violations.filter((v) => /\(r\)/.test(v))).toEqual([]);
    });
  });

  describe("(a) one printed result, one node", () => {
    it("rejects a second statement node at the environment, whatever its hypotheses", () => {
      const core = passingCore();
      const alt = structuredClone(core.statements[0]);
      alt.id = "thm:main-alt";
      alt.depends_on = ["ass:overlap"];
      core.statements.push(alt);
      const r = lintTranscription(core, ENVS, SCOPE, { phase: "v1" });
      expect(r.violations).toEqual([expect.stringMatching(/^\(a\) thm:main: found 2 statement nodes at one environment \(thm:main, thm:main-alt\)/)]);
    });
  });

  describe("(g) dependency edges", () => {
    it("reports an unreferenced assumption dependency as a WARNING, not a violation", () => {
      const core = passingCore();
      core.statements[1].depends_on = ["ass:overlap"]; // thm:rate's env \refs nothing
      const result = lintTranscription(core, ENVS, SCOPE, { phase: "v1" });
      expect(result.violations).toEqual([]);
      expect(result.warnings).toEqual([
        "thm:rate: depends on ass:overlap which the environment never references; " +
          "V1.5 must confirm the paper actually assumes it",
      ]);
    });
  });

  // `added_by:"V1.5"` is a string the V1 agent can type; the PHASE decides.
  describe("(h) bookkeeping assumptions", () => {
    it("refuses a bookkeeping assumption in phase v1, accepts it in phase v1_5 exempt from the text and locator rules", () => {
      const core = passingCore();
      core.assumptions.push({
        id: "ass:measurable",
        condition: "\\(\\psi\\) is measurable",
        bookkeeping: { flag: true, added_by: "V1.5", reason: "the proof integrates \\(\\psi\\)" },
      });
      const violations = lint(core);
      expect(letters(violations)).toContain("(h)");
      expect(violations.join("\n")).toContain("ass:measurable");
      expect(violations.join("\n")).toContain("only V1.5 may add bookkeeping assumptions");
      expect(lint(core, ENVS, SCOPE, "v1_5")).toEqual([]);
    });
  });
});

describe("invokesRef", () => {
  it("reads invocation from the words around the reference", () => {
    expect(invokesRef("Under Assumptions \\ref{ass:a} and \\ref{ass:b}, the estimator is consistent.", "ass:b")).toBe(true);
    expect(invokesRef("Suppose that Assumptions~\\ref{ass:a}--\\ref{ass:c} hold. Then…", "ass:c")).toBe(true);
    expect(invokesRef("Assume \\cref{ass:a} holds.", "ass:a")).toBe(true);
    expect(invokesRef("Unlike \\ref{ass:a}, we do not require symmetry. Then the bound holds.", "ass:a")).toBe(false);
    expect(invokesRef("See also \\ref{ass:a} for a discussion.", "ass:a")).toBe(false);
  });
});
