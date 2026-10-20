import { beforeEach, describe, expect, it } from "vitest";
import { mkdtempSync, mkdirSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import {
  clearRetrievalCache,
  createRetrieval,
  expandQuery,
} from "../src/formalization/reuse_retrieval.js";
import { loadAliasFile } from "../src/formalization/aliases.js";
import { indexSourceFromPath, indexSourcesFromToolkit, type IndexSource } from "../src/library/sources.js";
import { toolkitConfigFromJson } from "../src/toolkit/config.js";
import { TOOLKIT_JSON } from "./toolkit/helpers.js";

/** The alias lexicon shipped for Causalean (data, not code). */
const ALIASES = resolve(import.meta.dirname, "..", "data", "aliases", "causalean.json");
const LEX = loadAliasFile(ALIASES);

/** The fixture root's index as a retrieval source, with the Causalean alias lexicon. */
function src(root: string): IndexSource {
  return indexSourceFromPath(join(root, "doc", "library_index.json"), { library: "Causalean", aliasFile: ALIASES });
}

/** A second library whose index sits at an arbitrary path (not `<root>/doc/library_index.json`). */
function toolkitSource(): IndexSource {
  const dir = mkdtempSync(join(tmpdir(), "toolkit-idx-"));
  const indexPath = join(dir, "decls.json");
  const entry = (name: string, doc: string) => ({
    name, kind: "theorem", module: "Toolkit.Tricks.Overlap", file: "Toolkit/Tricks/Overlap.lean", line: 1,
    statement: "trimmed s ≤ c", doc, refs: [], axioms: [], usesSorry: false,
  });
  writeFileSync(indexPath, JSON.stringify({
    commit: "cafef00d", toolchain: "t",
    entries: [entry("Toolkit.Tricks.overlap_trim_bound", "Overlap trimming bound for the propensity score.")],
  }));
  return indexSourceFromPath(indexPath);
}

/** A fixture Causalean root with a hand-built index covering the cases we care about. */
function fixtureRoot(): string {
  const root = mkdtempSync(join(tmpdir(), "reuse-"));
  mkdirSync(join(root, "doc", "library_review"), { recursive: true });
  const entries = [
    {
      name: "Causalean.PO.ID.ConditionalExchangeability",
      kind: "def",
      module: "Causalean.PO.ID.Basic",
      file: "Causalean/PO/ID/Basic.lean",
      line: 10,
      statement: "(s : POSystem) → Prop",
      doc: "Conditional exchangeability of the potential outcomes given covariates.\n\nMeasure-theoretic note.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      // same concept, but sorried — must rank below the clean one on equal overlap
      name: "Causalean.PO.ID.ConditionalExchangeabilityWeak",
      kind: "def",
      module: "Causalean.PO.ID.Basic",
      file: "Causalean/PO/ID/Basic.lean",
      line: 40,
      statement: "(s : POSystem) → Prop",
      doc: "Conditional exchangeability of the potential outcomes given covariates.\n\nWeak variant.",
      refs: [],
      axioms: [],
      usesSorry: true,
    },
    {
      name: "Causalean.PO.ID.Overlap",
      kind: "def",
      module: "Causalean.PO.ID.Basic",
      file: "Causalean/PO/ID/Basic.lean",
      line: 70,
      statement: "(s : POSystem) → Prop",
      doc: "Overlap (positivity): the propensity score is bounded away from 0 and 1.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      name: "Causalean.PO.ID.Exact.ate_backdoor",
      kind: "theorem",
      module: "Causalean.PO.ID.Exact.Backdoor",
      file: "Causalean/PO/ID/Exact/Backdoor.lean",
      line: 100,
      statement: "ate s = ∫ x, condExp s x ∂μ",
      doc: "The ATE equals the backdoor adjustment integral.",
      refs: [],
      proofRefs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      // noise: name shares the connective word "conditional" with the ignorability
      // alias phrase, but is unrelated. Must NOT surface for "ignorability".
      name: "Causalean.PO.ID.Exact.IV.conditionalMarginResponse",
      kind: "def",
      module: "Causalean.PO.ID.Exact.IV",
      file: "Causalean/PO/ID/Exact/IV.lean",
      line: 3,
      statement: "(s : POSystem) → ℝ",
      doc: "Variable-intensity IV margin response.",
      refs: [],
      proofRefs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      // an auto-generated instance — must be penalized below a real def on equal match.
      name: "Causalean.PO.ID.instOverlapWitness",
      kind: "instance",
      module: "Causalean.PO.ID.Basic",
      file: "Causalean/PO/ID/Basic.lean",
      line: 90,
      statement: "(s : POSystem) → Prop",
      doc: "Overlap positivity instance.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      // qualified identifier in the statement — exercises symbolSet dot-splitting.
      name: "Causalean.PO.indep_lemma",
      kind: "theorem",
      module: "Causalean.PO.Indep",
      file: "Causalean/PO/Indep.lean",
      line: 1,
      statement: "ProbabilityTheory.CondIndepFun m h Y A",
      doc: "Conditional independence of Y and A.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      name: "Causalean.Stat.Minimax.foo_rate",
      kind: "theorem",
      module: "Causalean.Stat.Minimax.Rate",
      file: "Causalean/Stat/Minimax/Rate.lean",
      line: 5,
      statement: "minimaxRate s = c",
      doc: "A minimax rate result.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      // generic-token-heavy name: "treatment"+"effect" must NOT outrank a single
      // specific "quantile" hit (the fractional name-weighting guard).
      name: "Causalean.Panel.EventStudy.TreatmentEffectFixed",
      kind: "def",
      module: "Causalean.Panel.EventStudy",
      file: "Causalean/Panel/EventStudy.lean",
      line: 1,
      statement: "(s : Panel) → ℝ",
      doc: "Fixed treatment effect of an event-study panel.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      name: "Causalean.Stat.Quantile.quantile_le_iff",
      kind: "theorem",
      module: "Causalean.Stat.Quantile",
      file: "Causalean/Stat/Quantile.lean",
      line: 1,
      statement: "quantile p ≤ x ↔ p ≤ cdf x",
      doc: "Characterization of the quantile by the cdf.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
    {
      // Matchable only by symbol shape (math operators ⨆ ∈ ⊥), which word-tokenization
      // strips — so the type-signature pass surfaces it where concept mode cannot. Its
      // name/doc/word-tokens are deliberately disjoint from the probe item's prose.
      name: "Causalean.Geo.bigsup_perp",
      kind: "theorem",
      module: "Causalean.Geo.Lattice",
      file: "Causalean/Geo/Lattice.lean",
      line: 1,
      statement: "⨆ i ∈ s, f i ⊥ g",
      doc: "Indexed supremum orthogonality witness.",
      refs: [],
      axioms: [],
      usesSorry: false,
    },
  ];
  writeFileSync(
    join(root, "doc", "library_index.json"),
    JSON.stringify({ commit: "deadbeef", toolchain: "t", entries }),
  );
  writeFileSync(
    join(root, "doc", "library_review", "PO.json"),
    JSON.stringify({ headline_theorems: [], reviews: [], flags: [] }),
  );
  return root;
}

beforeEach(() => clearRetrievalCache());

describe("alias expansion", () => {
  it("expands ignorability to the exchangeability family + PO/ID module", () => {
    const e = expandQuery("ignorability of potential outcomes", LEX);
    expect(e.terms).toContain("exchangeability");
    expect(e.terms).toContain("unconfoundedness");
    expect(e.modules).toContain("Causalean/PO/ID/");
  });

  it("a malformed or unreadable alias file is an error, not a silent loss of the lexicon", () => {
    const dir = mkdtempSync(join(tmpdir(), "alias-"));
    const bad = join(dir, "bad.json");
    writeFileSync(bad, JSON.stringify({ version: 2, entries: "nope" }));
    expect(() => loadAliasFile(bad)).toThrow(/invalid alias file .*bad\.json/);
    expect(() => loadAliasFile(join(dir, "missing.json"))).toThrow(/cannot read alias file .*missing\.json/);
  });
});

describe("search modes", () => {
  it("concept mode bridges a synonym via the alias and ranks a clean decl above a usesSorry one", () => {
    const r = createRetrieval(src(fixtureRoot()));
    const ign = r.search({ mode: "concept", title: "ignorability" });
    expect(ign[0].name).toBe("Causalean.PO.ID.ConditionalExchangeability");
    expect(ign[0].matchedVia).toBe("alias");
    expect(ign.find((h) => h.name.endsWith("conditionalMarginResponse"))).toBeUndefined();
    const hits = r.search({ mode: "concept", title: "conditional exchangeability" });
    const clean = hits.findIndex((h) => h.name.endsWith("ConditionalExchangeability"));
    const weak = hits.findIndex((h) => h.name.endsWith("ConditionalExchangeabilityWeak"));
    expect(clean).toBeGreaterThanOrEqual(0);
    expect(weak).toBeGreaterThan(clean);
  });

  it("typePattern and goal modes match by symbol shape, independent of vocabulary", () => {
    const r = createRetrieval(src(fixtureRoot()));
    expect(r.search({ mode: "typePattern", pattern: "∫ condExp _" })[0].name).toBe("Causalean.PO.ID.Exact.ate_backdoor");
    expect(r.search({ mode: "typePattern", pattern: "→ ∀ ≤ ∈" })).toEqual([]);
    const goal = r.search({ mode: "goal", goalType: "ate s = ∫ x, condExp s x ∂μ" }, { topK: 3 });
    expect(goal.map((h) => h.name)).toEqual(["Causalean.PO.ID.Exact.ate_backdoor"]);
  });
});

describe("multi-index retrieval", () => {
  it("searches every source and tags each hit with its library", () => {
    const r = createRetrieval([src(fixtureRoot()), toolkitSource()]);
    expect(r.libraries.map((l) => l.name)).toEqual(["Causalean", "Toolkit"]); // name derived from modules
    const hits = r.search({ mode: "concept", title: "overlap positivity" }, { topK: 10 });
    expect(hits.find((h) => h.name === "Causalean.PO.ID.Overlap")?.library).toBe("Causalean");
    expect(hits.find((h) => h.name === "Toolkit.Tricks.overlap_trim_bound")?.library).toBe("Toolkit");
    // lexical scores share one scale, so the merged list is score-ordered
    for (let i = 1; i < hits.length; i++) expect(hits[i - 1].score).toBeGreaterThanOrEqual(hits[i].score);
  });

  it("derives the sources from the toolkit config (relative paths resolved; missing index skipped)", () => {
    const root = mkdtempSync(join(tmpdir(), "tk-"));
    const cfg = toolkitConfigFromJson(join(root, "tk"), TOOLKIT_JSON);
    const baseIndex = join(root, "base", "doc", "library_index.json");
    const INDEX = JSON.stringify({
      commit: "x", toolchain: "y", modules: {},
      entries: [{ name: "Foo.bar", kind: "theorem", statement: "True", file: "Foo/Bar.lean", module: "Foo.Bar", line: 1, doc: "", refs: [], usesSorry: false, axioms: [] }],
    });
    expect(indexSourcesFromToolkit(cfg)).toEqual([]); // nothing on disk yet
    mkdirSync(join(root, "base", "doc"), { recursive: true });
    writeFileSync(baseIndex, INDEX);
    mkdirSync(join(root, "tk", "doc"), { recursive: true });
    writeFileSync(cfg.indexPath, INDEX);
    const sources = indexSourcesFromToolkit(cfg);
    expect(sources.map((s) => [s.library, s.indexPath])).toEqual([["Base", baseIndex], ["Toolkit", cfg.indexPath]]);
    expect(sources[0].root).toBe(join(root, "base"));
  });
});
