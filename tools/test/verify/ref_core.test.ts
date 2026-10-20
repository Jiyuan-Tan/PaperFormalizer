import { describe, expect, it } from "vitest";
import { RefCoreSchema, cutSlice, materializeRefCore } from "../../src/verify/ref_core.js";
import type { EnvsJson, TexEnv } from "../../src/verify/types.js";

const env = (partial: Partial<TexEnv> & Pick<TexEnv, "id" | "kind" | "body">): TexEnv => ({
  envName: partial.kind,
  label: partial.id,
  title: null,
  proof: null,
  proofLines: null,
  lines: { file: "main.tex", from: 1, to: 3, env: partial.kind, label: partial.id },
  refs: [],
  ...partial,
});

const ENVS: EnvsJson = {
  main: "main.tex",
  files: ["main.tex"],
  envs: [
    env({
      id: "ass:reg",
      kind: "assumption",
      body: "\\label{ass:reg}\n(i) $X$ has a density bounded away from zero. (ii) The map $\\gamma \\mapsto m(w,\\gamma)$ is\tlinear.",
    }),
    env({
      id: "thm:main",
      kind: "theorem",
      body: "\\label{thm:main}\nSuppose $\\|\\hat\\gamma - \\gamma_0\\| \\to 0$. Then $\\hat\\tau$ is consistent. Moreover, if (i) holds, $\\hat\\tau$ is efficient.",
      proof: "By Assumption~\\ref{ass:reg} and $r^2\\\n&& x$, done.",
      proofLines: { file: "main.tex", from: 10, to: 12, env: "proof", label: null },
    }),
  ],
  bibliography: [],
  warnings: [],
} as unknown as EnvsJson;

const FLAT = "Let $\\gamma_0(w) = E(Y \\mid W = w)$ denote the regression. We write $n_\\ell = n/L$ throughout.";

describe("cutSlice", () => {
  it("ends a slice typed up to a display's last formula at the display's closer", () => {
    const text = "Let the estimator be\n\\[\nB=\\sum_j c_j,\n\\]\nWe show that it holds.";
    expect(cutSlice(text, { from: "Let the estimator", to: "c_j,$" }, "x")).toEqual({ text: "Let the estimator be\n\\[\nB=\\sum_j c_j,\n\\]" });
    // a cut followed by more text before the closer is left as typed (rule (m) reports it)
    expect(cutSlice("see \\[ a=b, c=d \\]", { from: "see", to: "a=b," }, "x")).toEqual({ text: "see \\[ a=b," });
  });
  it("cuts between two anchors, whitespace-loosely, and reports non-unique or missing anchors", () => {
    const text = "alpha beta   gamma delta gamma epsilon";
    expect(cutSlice(text, { from: "beta gamma", to: "delta" }, "x")).toEqual({ text: "beta   gamma delta" });
    // `gamma` occurs twice; the pair with `delta` cuts shortest from the first one
    expect(cutSlice(text, { from: "gamma", to: "delta" }, "x")).toEqual({ text: "gamma delta" });
    // two equally short fits are ambiguous
    expect(cutSlice("a x b. a x b.", { from: "a x", to: "b." }, "x")).toMatchObject({ error: expect.stringMatching(/fit 2 places equally well/) });
    expect(cutSlice(text, { from: "zeta", to: "delta" }, "x")).toMatchObject({ error: expect.stringMatching(/does not occur/) });
    // a near miss names the words that do occur and shows the source there
    expect(cutSlice(text, { from: "and beta gamma", to: "delta" }, "x")).toMatchObject({
      error: expect.stringMatching(/does not occur.*The words "beta gamma" do occur; the source there reads: …alpha beta gamma delta/),
    });
    // a missing `$` in the anchor still lands; the slice is cut from the real text
    expect(cutSlice("Let $\\mathcal{S}_{2}$ is selected at random.", { from: "$\\mathcal{S}_{2} is selected", to: "random." }, "x")).toEqual({ text: "$\\mathcal{S}_{2}$ is selected at random." });
    // `to` is the first occurrence after `from`, so a later repeat does not extend the slice
    expect(cutSlice(text, { from: "alpha", to: "gamma" }, "x")).toEqual({ text: "alpha beta   gamma" });
  });
});

describe("materializeRefCore", () => {
  const ref = RefCoreSchema.parse({
    qid: "verify_t",
    target_estimand: "$\\tau$",
    symbols: [{ name: "\\hat\\tau", type: "estimator" }],
    assumptions: [
      { id: "ass:density", source: { env: "ass:reg", slice: { from: "$X$ has a density", to: "away from zero." } }, novel: { flag: true, justification: "own" } },
      { id: "ass:linear", source: { env: "ass:reg", slice: { from: "The map", to: "linear." } }, novel: { flag: true, justification: "own" } },
      { id: "ass:consistent-first-stage", source: { env: "thm:main", slice: { from: "Suppose $\\|\\hat\\gamma", to: "\\to 0$." } }, novel: { flag: true, justification: "inline" } },
      { id: "ass:fold-size", source: { prose: true, slice: { from: "We write $n_\\ell", to: "throughout." } }, novel: { flag: true, justification: "prose" } },
    ],
    definitions: [
      { id: "def:gamma0", name: "regression function", source: { prose: true, slice: { from: "Let $\\gamma_0(w)", to: "regression." } } },
    ],
    statements: [
      {
        id: "thm:main",
        kind: "theorem",
        env: "thm:main",
        depends_on: ["ass:consistent-first-stage", "ass:density", "ass:linear", "def:gamma0"],
        hypotheses: ["ass:density", "ass:linear"],
      },
    ],
  });

  it("copies every text field verbatim from the source, tabs and control spaces included", () => {
    const { core, violations } = materializeRefCore(ref, ENVS, FLAT);
    expect(violations).toEqual([]);
    const byId = (id: string) => core.assumptions.find((a) => a.id === id)!;
    expect(byId("ass:density").condition).toBe("$X$ has a density bounded away from zero.");
    expect(byId("ass:linear").condition).toBe("The map $\\gamma \\mapsto m(w,\\gamma)$ is\tlinear.");
    expect(byId("ass:linear").tex_locator).toEqual({ file: "main.tex", from: 1, to: 3, env: "assumption", label: "ass:reg" });
    expect(byId("ass:consistent-first-stage").condition).toBe("Suppose $\\|\\hat\\gamma - \\gamma_0\\| \\to 0$.");
    expect(byId("ass:consistent-first-stage").tex_locator?.label).toBe("thm:main");
    expect(byId("ass:fold-size").condition).toBe("We write $n_\\ell = n/L$ throughout.");
    expect(byId("ass:fold-size").tex_locator).toEqual({ file: "flat.tex", from: 0, to: 0, env: "prose", label: null });
    expect(core.definitions[0]!.construction).toBe("Let $\\gamma_0(w) = E(Y \\mid W = w)$ denote the regression.");
    const main = core.statements.find((s) => s.id === "thm:main")!;
    expect(main.statement).toBe(`${ENVS.envs[1]!.body.trim()} [Hypotheses: ass:density, ass:linear]`);
    expect(main.proof_tex).toBe("By Assumption~\\ref{ass:reg} and $r^2\\\n&& x$, done.");
    expect(core.bibliography).toEqual([]);
  });

  it("cuts by numbered sentences, and numbers them as the SCOPE block shows", async () => {
    const { numberedSentences } = await import("../../src/verify/ref_core.js");
    const body = ENVS.envs[1]!.body;
    expect(numberedSentences(body)).toEqual([
      "(1) \\label{thm:main} Suppose $\\|\\hat\\gamma - \\gamma_0\\| \\to 0$.",
      "(2) Then $\\hat\\tau$ is consistent.",
      "(3) Moreover, if (i) holds, $\\hat\\tau$ is efficient.",
    ]);
    const r = RefCoreSchema.parse({
      ...ref,
      assumptions: [{ id: "ass:s", source: { env: "thm:main", sentences: [1, 1] }, novel: { flag: true, justification: "j" } }],
      statements: [],
    });
    const { core, violations } = materializeRefCore(r, ENVS, FLAT);
    expect(violations).toEqual([]);
    expect(core.assumptions[0]!.condition).toBe("\\label{thm:main}\nSuppose $\\|\\hat\\gamma - \\gamma_0\\| \\to 0$.");
    const bad = RefCoreSchema.parse({ ...r, assumptions: [{ id: "ass:s", source: { env: "thm:main", sentences: [3, 9] }, novel: { flag: true, justification: "j" } }] });
    expect(materializeRefCore(bad, ENVS, FLAT).violations).toEqual([expect.stringMatching(/sentences \[3, 9\] out of range .* has 3 sentence/)]);
  });

  it("reports structural mistakes as (ref) violations without throwing, and refuses the reserved id families the referee and the fixer mint (bk, pin, patch)", () => {
    const bad = RefCoreSchema.parse({
      ...ref,
      assumptions: [{ id: "ass:x", source: { env: "nope" }, novel: { flag: true, justification: "j" } }],
      statements: [
        { id: "thm:c", kind: "theorem", env: "thm:main", status: "cited", depends_on: [] },
        { id: "thm:h", kind: "theorem", env: "thm:main", depends_on: [], hypotheses: ["ass:x"] },
      ],
    });
    const { violations } = materializeRefCore(bad, ENVS, FLAT);
    expect(violations).toHaveLength(3);
    expect(violations).toEqual(
      expect.arrayContaining([
        expect.stringMatching(/\(ref\) ass:x\.source: source env "nope" is not an id/),
        expect.stringMatching(/\(ref\) thm:h\.hypotheses: ass:x listed but not in depends_on/),
        expect.stringMatching(/\(ref\) thm:c: status "cited" needs `source`/),
      ]),
    );
    const reserved = RefCoreSchema.parse({
      ...ref,
      assumptions: ["ass:bk-1", "ass:pin-2", "ass:patch-two-sided", "ass:pinned"].map((id) => ({
        id,
        source: { env: "ass:reg", sentences: [1, 1] },
        novel: { flag: true, justification: "j" },
      })),
      statements: [],
    });
    const r = materializeRefCore(reserved, ENVS, FLAT);
    expect(r.violations).toHaveLength(3);
    for (const id of ["ass:bk-1", "ass:pin-2", "ass:patch-two-sided"]) {
      expect(r.violations).toContainEqual(expect.stringMatching(new RegExp(`\\(ref\\) ${id.replace(/[-]/g, "\\-")}: ids .* are reserved`)));
    }
    expect(r.core.assumptions.map((a) => a.id)).toEqual(["ass:pinned"]); // a prefix that merely resembles one is fine
  });
});
