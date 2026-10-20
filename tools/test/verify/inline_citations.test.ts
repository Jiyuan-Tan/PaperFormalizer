// The published results a proof invokes by citation (`inline_citations.ts`): which citations are
// sites, and the V1 lint warning for each one no `cited` node registers.
//
// The fixtures: a verbatim excerpt of a paper that surfaced the gap (run tbs_extreme_effects, the
// maintainer's own paper), where such a result was the last open proof of the Lean stage, and a
// synthetic paper laid out like the other one that did (ustat_synthetic). The expected sites below
// were read off their TeX.
import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { inlineCitationSites, inlineCitationWarnings, locatorsIn } from "../../src/verify/inline_citations.js";
import { PaperUnits } from "../../src/verify/units.js";
import type { EnvKind, EnvsJson, TexEnv } from "../../src/verify/types.js";

const FIXTURES = path.join(path.dirname(fileURLToPath(import.meta.url)), "fixtures", "inline_citations");

function env(id: string, kind: EnvKind, body: string, proof: string | null, n: number): TexEnv {
  return {
    id,
    kind,
    envName: kind,
    label: id,
    title: null,
    body,
    proof,
    proofLines: proof === null ? null : { file: "appendix.tex", from: 100 * n, to: 100 * n + 50, env: "proof", label: null },
    lines: { file: "main.tex", from: 10 * n, to: 10 * n + 5, env: kind, label: id },
    refs: [],
  };
}
const envsOf = (list: TexEnv[]): EnvsJson => ({ main_file: "main.tex", files: ["main.tex"], newtheorem: {}, envs: list, bibliography: [] });
const ids = (e: EnvsJson): string[] => e.envs.map((x) => x.id);

/** A fixture file as `envs.json`: a `%%% <id> <kind> <body|proof> …` line opens a text, every other
 * `%%` line (the header, the marks of a cut) is dropped. */
function fixture(name: string): EnvsJson {
  const parts = new Map<string, { kind: EnvKind; body: string[]; proof: string[] | null }>();
  let into: string[] | null = null;
  for (const line of readFileSync(path.join(FIXTURES, name), "utf8").split("\n")) {
    const head = /^%%% (\S+) (\S+) (body|proof)\b/.exec(line);
    if (head) {
      const e = parts.get(head[1]!) ?? { kind: head[2] as EnvKind, body: [], proof: null };
      parts.set(head[1]!, e);
      into = head[3] === "body" ? e.body : (e.proof = []);
    } else if (!line.startsWith("%%")) into?.push(line);
  }
  return envsOf([...parts].map(([id, e], k) => env(id, e.kind, e.body.join("\n").trim(), e.proof ? e.proof.join("\n").trim() : null, k + 1)));
}

const found = (e: EnvsJson, scope: readonly string[] = ids(e)): string[] => inlineCitationSites(e, scope).map((s) => `${s.env} | ${s.key} | ${s.locator}`);
const one = (proof: string, body = "The bound holds."): EnvsJson => envsOf([env("lem:a", "lemma", body, proof, 1)]);

describe("inlineCitationSites on the papers that surfaced the gap", () => {
  it("tbs_extreme_effects: the four results the proofs invoke, and none of the citations without a locator", () => {
    const e = fixture("tbs_extreme_effects.tex");
    expect(found(e)).toEqual([
      "prop:id | bingham1989regular | Theorem 1.56",
      "lemma:mu_rate | nguyen2014tail | Theorem 2.1",
      "lemma:eta_rate | zhang2023wasserstein | Proposition 3.1",
      "lemma:eta_ipw | su2023estimated | Theorem 1",
    ]);
    // The proofs cite these too, naming no result: "in {\citep{boucheron2015tail}}", "By
    // {\citep{boucheron2015tail}}, with probability …", "by standard DML theory {\citep{foster2023orthogonal}}".
    const proofs = e.envs.map((x) => x.proof ?? "").join("\n");
    expect(proofs.match(/boucheron2015tail/g)).toHaveLength(3);
    expect(proofs).toContain("foster2023orthogonal");
    const sites = inlineCitationSites(e, ids(e));
    expect(sites.find((s) => s.key === "zhang2023wasserstein")!.text).toContain("where we use {\\citetext{\\citealp{zhang2023wasserstein}, Proposition 3.1}} in the last inequality");
    // The proof of lemma:eta_ipw is whole in the fixture: the unit is the one the run's own cut gives.
    expect(sites.find((s) => s.key === "su2023estimated")!.unit).toBe("lemma:eta_ipw/proof/2/2");
  });

  it("ustat_synthetic: Theorem 3.27, Theorems 11.2 and 12.3 — not the symmetrization citation, not the cited lemma's own title", () => {
    const e = fixture("ustat_synthetic.tex");
    expect(found(e)).toEqual([
      "thm:excess_risk | wainwright2019high | Theorem 3.27",
      "thm:smooth_clt | van2000asymptotic | Theorem 11.2",
      "thm:smooth_clt | van2000asymptotic | Theorem 12.3",
      // "an analogous argument to the one used in the proof of Theorem 12.3 in \citet{…}", further down
      "thm:smooth_clt | van2000asymptotic | Theorem 12.3",
    ]);
    expect(e.envs.find((x) => x.id === "thm:excess_risk")!.proof).toContain("standard symmetrization argument \\citep{wainwright2019high}");
    // A STATEMENT that cites with a locator (`\begin{lemma}[Theorem A.4 in \citet{bartlett2005local}]`).
    expect(e.envs.find((x) => x.id === "lem:emp-pop-rad")!.body).toContain("Theorem A.4 in \\citet{bartlett2005local}");
  });

  it("names the proof unit that holds the citation, in the cut of units.ts", () => {
    for (const name of ["tbs_extreme_effects.tex", "ustat_synthetic.tex"]) {
      const e = fixture(name);
      // A flat text holding every body and proof once, as `parseUnits` reads them.
      const flat = e.envs.flatMap((x) => [x.body, ...(x.proof ? [x.proof] : [])]).join("\n\n\n");
      const units = PaperUnits.parse(flat, e);
      const sites = inlineCitationSites(e, ids(e));
      expect(sites.length).toBeGreaterThan(0);
      for (const s of sites) {
        const u = units.unitById(s.unit);
        expect(u, s.unit).toBeDefined();
        for (const k of s.keys) expect(units.textOf(u!)).toContain(`{${k}}`);
      }
    }
  });
});

describe("locatorsIn reads a named locator back (a leaf's locator, a repair's citation)", () => {
  it("named alone, and numbered over named", () => {
    expect(locatorsIn("Freedman's inequality")).toEqual(["Freedman's inequality"]);
    expect(locatorsIn("Freedman's inequality and Theorem 1.6")).toEqual(["Theorem 1.6"]);
    expect(locatorsIn("Lemma A.1")).toEqual(["Lemma A.1"]);
  });
});

describe("inlineCitationSites, form by form", () => {
  it.each([
    { form: "optional argument", proof: "By \\citep[Theorem 2.1]{k}, the bound holds.", sites: ["k | Theorem 2.1"] },
    { form: "abbreviation with a tie", proof: "See \\cite[Prop.~3]{k}.", sites: ["k | Proposition 3"] },
    { form: "two locators in one argument", proof: "This is \\citet[Thm.~6.5, Cor.~6.7]{k}.", sites: ["k | Theorem 6.5", "k | Corollary 6.7"] },
    // live cns: `\\cite[Lemma B2]{newey1994kernel}` was missed
    { form: "appendix number with no dot", proof: "By \\cite[Lemma B2]{k} and \\citet[Theorem S3]{j} the bound holds.", sites: ["k | Lemma B2", "j | Theorem S3"] },
    { form: "a roman section number", proof: "By \\cite[Theorem VIII.1]{k}, a quantized network exists.", sites: ["k | Theorem VIII.1"] },
    { form: "pre-note and post-note", proof: "Apply \\citep[see][Lemma A.4]{k} to $f$.", sites: ["k | Lemma A.4"] },
    { form: "locator after the citation", proof: "By \\citet{k}, Theorem 2, the claim follows.", sites: ["k | Theorem 2"] },
    { form: "locator before the citation", proof: "By lemma 11.2 of \\citet{k} the claim follows.", sites: ["k | Lemma 11.2"] },
    { form: "author and year commands", proof: "By \\citeauthor{k} (\\citeyear{k}), Corollary 4, we are done.", sites: ["k | Corollary 4"] },
    { form: "several keys: one site naming them", proof: "By \\citep[Theorem 2]{a, b} the claim follows.", sites: ["a, b | Theorem 2"] },
    { form: "a locator between two citations goes to the nearer", proof: "Use \\citet{a}, Theorem 2 and \\citet{b}, Lemma 3 in turn.", sites: ["a | Theorem 2", "b | Lemma 3"] },
    { form: "an escaped percent is not a comment", proof: "On 50\\% of the sample, \\cite[Theorem 1]{k} applies.", sites: ["k | Theorem 1"] },
    // a named result is a locator: "Freedman's inequality \\cite{Fre75} (see, also, \\cite[Lemma A.1]{CeLuSt06})"
    { form: "a named result before its citation", proof: "Freedman's inequality \\cite{f} (see, also, \\cite[Lemma A.1]{c}) implies that the bound holds.", sites: ["f | Freedman's inequality", "c | Lemma A.1"] },
    { form: "a hyphenated named result", proof: "By Azuma-Hoeffding's inequality \\citep{k} the sum concentrates.", sites: ["k | Azuma-Hoeffding's inequality"] },
    { form: "a named result in an optional argument stays with its citation", proof: "By \\cite[Freedman's inequality]{a} and \\cite{b} the claim follows.", sites: ["a | Freedman's inequality"] },
    { form: "a numbered locator wins over a named one", proof: "Freedman's inequality \\cite{k}, Theorem 1.6, gives the bound.", sites: ["k | Theorem 1.6"] },
    { form: "no brace in a named locator", proof: "By \\emph{Hoeffding}'s inequality \\cite{k} the sum concentrates.", sites: [] },
    { form: "a named result after a sentence end is not one", proof: "We use Bernstein's inequality. Then \\citet{k} gives more.", sites: [] },
    { form: "no locator", proof: "By standard theory \\citep{k}, the bound holds; see also \\citet[Chapter 3]{k} and \\cite[p.~12]{k}.", sites: [] },
    { form: "the paper's own result", proof: "By Lemma~\\ref{lem:b} and \\citet{k} the claim follows.", sites: [] },
    { form: "locator in another sentence", proof: "This proves Theorem 2. Then \\citet{k} show more.", sites: [] },
    { form: "locator beyond the window", proof: "Theorem 2 is what one obtains, after a long and careful computation, from the work of \\citet{k}.", sites: [] },
    { form: "citation in a comment", proof: "The bound holds. % see \\citet[Cor.~3.7]{k}\n% and Theorem 2 of \\cite{k}\nHence the claim.", sites: [] },
  ])("$form", ({ proof, sites }) => {
    expect(found(one(proof)).map((s) => s.replace(/^lem:a \| /, ""))).toEqual(sites);
  });

  it("reads proofs only, of the in-scope theorem-like environments", () => {
    const cite = "By \\cite[Theorem 1]{k}, the bound holds.";
    // in a statement
    expect(found(one("A direct computation.", cite))).toEqual([]);
    expect(found(envsOf([env("lem:a", "lemma", cite, null, 1)]))).toEqual([]);
    // out of scope; a remark's proof
    const e = envsOf([env("lem:a", "lemma", "The bound holds.", cite, 1), env("rem:b", "remark", "A remark.", cite, 2)]);
    expect(found(e, ["rem:b"])).toEqual([]);
    expect(found(e)).toEqual(["lem:a | k | Theorem 1"]);
  });
});

describe("inlineCitationWarnings", () => {
  const e = fixture("tbs_extreme_effects.tex");
  const host = e.envs.find((x) => x.id === "lemma:eta_rate")!;
  const statement = (id: string, at: TexEnv["lines"], depends_on: string[] = []) => ({ id, kind: "lemma", statement: "…", status: "to-prove", depends_on, free_symbols: [], tex_locator: at });
  const leaf = (id: string, cite: string, at: TexEnv["lines"]) => ({ ...statement(id, at), status: "cited", source: { cite, locator: "Proposition 3.1" } });
  const core = (...statements: unknown[]): Core => ({ statements }) as unknown as Core;
  const about = (c: Core): string[] => inlineCitationWarnings(c, e, ids(e)).filter((w) => w.includes("zhang2023wasserstein"));

  it("one line per unregistered result, opening with the host's node", () => {
    const lines = inlineCitationWarnings(core(statement("lem:eta-rate", host.lines)), e, ids(e));
    expect(lines).toHaveLength(4);
    expect(about(core(statement("lem:eta-rate", host.lines)))).toEqual([
      expect.stringMatching(
        /^lem:eta-rate: the proof of lemma:eta_rate invokes \[zhang2023wasserstein, Proposition 3\.1\] \(lemma:eta_rate\/proof\/\d+\/\d+\): a published result used inside the proof, with no cited node of its own\. Not a defect of the node or of its wiring: grade the step as any use of a published result\. paper: "/,
      ),
    ]);
    // no statement node at the environment: the line opens with the environment
    expect(about(core())[0]).toMatch(/^lemma:eta_rate: the proof of lemma:eta_rate invokes/);
  });

  it("is silent when a cited node of that key sits at the host or is one of its dependencies", () => {
    const elsewhere = e.envs.find((x) => x.id === "prop:id")!.lines;
    expect(about(core(statement("lem:eta-rate", host.lines), leaf("lem:zhang", "zhang2023wasserstein", host.proofLines!)))).toEqual([]);
    expect(about(core(statement("lem:eta-rate", host.lines), leaf("lem:zhang", "zhang2023wasserstein", host.lines)))).toEqual([]);
    expect(about(core(statement("lem:eta-rate", host.lines, ["lem:zhang"]), leaf("lem:zhang", "zhang2023wasserstein", elsewhere)))).toEqual([]);
    // another work's leaf at the host; the right work's leaf somewhere the host does not depend on
    expect(about(core(statement("lem:eta-rate", host.lines), leaf("lem:other", "su2023estimated", host.proofLines!)))).toHaveLength(1);
    expect(about(core(statement("lem:eta-rate", host.lines), leaf("lem:zhang", "zhang2023wasserstein", elsewhere)))).toHaveLength(1);
  });

  it("a result invoked at two places of one proof is one line naming both units", () => {
    const ustat = fixture("ustat_synthetic.tex");
    const lines = inlineCitationWarnings(core(), ustat, ids(ustat));
    expect(lines).toHaveLength(3);
    expect(lines[2]).toMatch(/invokes \[van2000asymptotic, Theorem 12\.3\] \(thm:smooth_clt\/proof\/\d+\/\d+, thm:smooth_clt\/proof\/\d+\/\d+\)/);
  });
});
