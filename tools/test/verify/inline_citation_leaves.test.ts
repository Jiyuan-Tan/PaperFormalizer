// A published result a PROOF invokes by citation, made a cited leaf of that proof's result
// (`ref_core.ts` `proof_citations`, `inline_citations.ts` `lintInlineCitations`), and every stage
// that then meets a statement sitting at a proof's locator.
//
// The fixtures are the excerpts of the two papers that surfaced the gap. They are cut, so their unit
// ids are not the runs' own: on the runs, Zhang's Proposition 3.1 is lemma:eta_rate/proof/10/2 …
// 11/1 and Wainwright's Theorem 3.27 is thm:excess_risk/proof/13/2 — the same sentences as below.
import { readFileSync } from "node:fs";
import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { afterEach, describe, expect, it } from "vitest";
import { runStructuralGate } from "../../src/core/gate.js";
import { parseTypedCore } from "../../src/core/core_io.js";
import type { Core } from "../../src/core/schema.js";
import { runPlanGate } from "../../src/formalization/plan/plan_gate.js";
import { copyVerifiedCitedSourcesToPlan } from "../../src/formalization/stage1.js";
import { roundACandidates } from "../../src/proposals/round_a.js";
import { applyDriftFixes } from "../../src/verify/directive_edits.js";
import { errorsOnHosts, inlineLeaves, routeReview } from "../../src/verify/stage_v1_5.js";
import type { V15NodeVerdict, V15Review } from "../../src/verify/types.js";
import { tk } from "../toolkit/helpers.js";
import { coreWhere } from "../../src/ui/run_model.js";
import { applyEdits, planAnnotations } from "../../src/verify/annotated_paper.js";
import { citedSourceOfRecord, excerptAround, resolveCitedSources } from "../../src/verify/cited_sources.js";
import { resultTexName } from "../../src/verify/core_graph.js";
import { applyPatchFile, validatePatchFile, type PatchFile } from "../../src/verify/patches.js";
import { citationSites, inlineCitationsBlock, joinLocators, lintInlineCitations, locatorsIn, repairCitationWarnings } from "../../src/verify/inline_citations.js";
import { RefCoreSchema, accountsForCitations, materializeRefCore } from "../../src/verify/ref_core.js";
import { nodeExcerpts, paperIndex } from "../../src/verify/referee_slices.js";
import { buildReport, type ReportInput } from "../../src/verify/report.js";
import { renderMatch } from "../../src/verify/bundle_match.js";
import { citedGateDeclarations } from "../../src/verify/stage_v6_report.js";
import { addNode, setLean } from "../../src/graph/mutate.js";
import { createEmptyGraph } from "../../src/graph/store.js";
import { lintTranscription } from "../../src/verify/transcription_lint.js";
import type { EnvKind, EnvsJson, TexEnv } from "../../src/verify/types.js";
import { regionUnits } from "../../src/verify/units.js";

const FIXTURES = path.join(path.dirname(fileURLToPath(import.meta.url)), "fixtures", "inline_citations");
const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

/** A fixture file as `envs.json` (see `inline_citations.test.ts`). */
function fixture(name: string, keys: string[]): EnvsJson {
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
  const envs = [...parts].map(([id, e], k): TexEnv => {
    const proof = e.proof ? e.proof.join("\n").trim() : null;
    const n = k + 1;
    return {
      id,
      kind: e.kind,
      envName: e.kind,
      label: id,
      title: null,
      body: e.body.join("\n").trim(),
      proof,
      proofLines: proof === null ? null : { file: "appendix.tex", from: 100 * n, to: 100 * n + 50, env: "proof", label: null },
      lines: { file: "main.tex", from: 10 * n, to: 10 * n + 5, env: e.kind, label: id },
      refs: [],
    };
  });
  return { main_file: "main.tex", files: ["main.tex"], newtheorem: {}, envs, bibliography: keys.map((key) => ({ key, text: key })) };
}

const nodeId = (e: TexEnv): string => `${e.kind === "proposition" ? "prop" : e.kind === "lemma" ? "lem" : "thm"}:${e.id.replace(/^.*:/, "").replace(/_/g, "-")}`;
const scopeOf = (e: EnvsJson): string[] => e.envs.map((x) => x.id);

/** The reference core of a fixture: one statement per environment, plus `extra`. */
function refs(e: EnvsJson, extra: Record<string, unknown>): unknown {
  return {
    qid: "q",
    target_estimand: "the target",
    sampling_model: { main: "i.i.d. data." },
    // lem:emp-pop-rad is the lemma the paper restates from the literature (no proof)
    statements: e.envs.map((x) => ({ id: nodeId(x), kind: x.kind === "lemma" ? "lemma" : x.kind === "proposition" ? "proposition" : "theorem", env: x.id, ...(x.proof === null ? { status: "cited", source: { cite: "bartlett2005local", locator: "Theorem A.4", verbatim_statement: "…" } } : {}) })),
    ...extra,
  };
}

/** The reference core materialized and checked as a V1 round checks it. */
function round(e: EnvsJson, extra: Record<string, unknown>): { core: Core; violations: string[]; warnings: string[] } {
  const ref = RefCoreSchema.parse(refs(e, extra));
  const m = materializeRefCore(ref, e, "");
  m.core.bibliography = e.bibliography.map((b) => ({ key: b.key, citation: b.text }));
  const gate = runStructuralGate(m.core, { allowBookkeeping: true, verbatim: true }).violations.map((v) => `(${v.code}) ${v.where}: ${v.message}`);
  // the fixtures are cut: a `\ref` to a part left out is not this test's
  const lint = lintTranscription(m.core, e, scopeOf(e), { phase: "v1", flatText: "" }).violations.filter((v) => !v.startsWith("(r)") && !v.startsWith("(s)"));
  const inline = lintInlineCitations(m.core, e, scopeOf(e), ref.dismissed_citations ?? []);
  return { core: m.core, violations: [...m.violations, ...gate, ...lint, ...inline.violations], warnings: inline.warnings };
}

const TBS_KEYS = ["bingham1989regular", "nguyen2014tail", "zhang2023wasserstein", "su2023estimated"];
const USTAT_KEYS = ["wainwright2019high", "van2000asymptotic", "bartlett2005local"];
const tbs = fixture("tbs_extreme_effects.tex", TBS_KEYS);
const ustat = fixture("ustat_synthetic.tex", USTAT_KEYS);
const site = (e: EnvsJson, key: string, locator?: string) => citationSites(e, scopeOf(e)).find((s) => s.key === key && (!locator || s.locator === locator))!;
const before = (unit: string, e: EnvsJson): string => {
  const env = e.envs.find((x) => unit.startsWith(`${x.id}/proof/`))!;
  const ids = regionUnits(env.proof!).map((u) => `${env.id}/proof/${u.p}/${u.u}`);
  return ids[ids.indexOf(unit) - 1]!;
};
const dismissAll = (e: EnvsJson, but: string[]): unknown[] => citationSites(e, scopeOf(e)).filter((s) => !but.includes(s.id)).map((s) => ({ site: s.id, reason: "pointer", note: "" }));

// tbs: "Therefore, we have [the bound] where we use [Zhang, Proposition 3.1] in the last inequality …"
const zhang = site(tbs, "zhang2023wasserstein");
const ZHANG = { id: "lem:zhang-prop-3-1", site: zhang.id, units: [before(zhang.units[0]!, tbs), zhang.units[0]!] };
// ustat: "Hence a standard concentration inequality (Theorem 3.27 \citet{wainwright2019high}) … gives: [the bound]"
const wain = site(ustat, "wainwright2019high");
const WAIN = { id: "lem:wainwright-thm-3-27", site: wain.id, units: [wain.units[0]!, wain.units[0]!] };

describe("an inline citation registered in the reference core", () => {
  it("tbs, Zhang's Proposition 3.1: the node is the proof's own passage, cited, wired to its host", () => {
    const r = round(tbs, { proof_citations: [ZHANG], dismissed_citations: dismissAll(tbs, [zhang.id]) });
    expect(r.violations).toEqual([]);
    const node = r.core.statements.find((s) => s.id === ZHANG.id)!;
    const host = tbs.envs.find((x) => x.id === "lemma:eta_rate")!;
    expect(node).toMatchObject({ kind: "lemma", status: "cited", cited_in: "lem:eta-rate", tex_locator: host.proofLines, source: { cite: "zhang2023wasserstein", locator: "Proposition 3.1" } });
    expect(node.statement).toMatch(/^Therefore, we have\s+\\begin\{align\}/);
    expect(node.statement).toMatch(/where we use \{\\citetext\{\\citealp\{zhang2023wasserstein\},\s+Proposition 3\.1\}\}\s+in the last inequality[\s\S]*\$\.$/);
    expect(host.proof).toContain(node.statement);
    // the passage is the paper's text, never the cited work's statement of record
    expect(node.source!.verbatim_statement).toBeUndefined();
    expect(node.proof_tex).toBeUndefined();
    expect(r.core.statements.find((s) => s.id === "lem:eta-rate")!.depends_on).toEqual([ZHANG.id]);
    expect(resultTexName(r.core, ZHANG.id)).toBe("\\cite[Proposition 3.1]{zhang2023wasserstein}, used in the proof of Lemma~\\ref{lemma:eta_rate}");
  });

  it("ustat, Wainwright's Theorem 3.27: one unit; the lemma the paper restates stays an ordinary cited leaf", () => {
    const r = round(ustat, { proof_citations: [WAIN], dismissed_citations: dismissAll(ustat, [wain.id]) });
    expect(r.violations).toEqual([]);
    const node = r.core.statements.find((s) => s.id === WAIN.id)!;
    expect(node.statement).toMatch(/^Hence a standard concentration inequality \(Theorem 3\.27 \\citet\{wainwright2019high\}\)/);
    expect(node).toMatchObject({ cited_in: "thm:excess-risk", source: { cite: "wainwright2019high", locator: "Theorem 3.27" } });
    expect(r.core.statements.find((s) => s.id === "thm:excess-risk")!.depends_on).toContain(WAIN.id);
    expect(r.core.statements.find((s) => s.id === "lem:emp-pop-rad")!.cited_in).toBeUndefined();
  });

  it("a dismissal accounts for a site and is a warning naming the host, the citation and the reading", () => {
    const clt = site(ustat, "van2000asymptotic", "Theorem 11.2");
    const r = round(ustat, {
      proof_citations: [WAIN, { id: "lem:vdv-12-3", site: site(ustat, "van2000asymptotic", "Theorem 12.3").id, units: [clt.units[0], clt.units[0]] }],
      dismissed_citations: [{ site: clt.id, reason: "method", note: "the projection argument is redone" }],
    });
    expect(r.violations).toEqual([]);
    expect(r.warnings).toEqual([
      // (the proof cites Theorem 12.3 once more, further down: outside the registered passage)
      expect.stringMatching(/^thm:smooth-clt: the proof of thm:smooth_clt cites \[van2000asymptotic, Theorem 12\.3\] also at thm:smooth_clt\/proof\/\d+\/\d+, outside the passage lem:vdv-12-3 registers/),
      expect.stringMatching(
        /^thm:smooth-clt: the proof of thm:smooth_clt cites \[van2000asymptotic, Theorem 11\.2\] \(thm:smooth_clt\/proof\/\d+\/\d+\); the transcription reads the citation as a method or argument borrowed from the cited work, not its result and made no cited node for it \(the projection argument is redone\)\. paper: "/,
      ),
    ]);
  });

  it("the prompt block lists each site once, the unit holding the citation marked between its neighbours", () => {
    const block = inlineCitationsBlock(ustat, scopeOf(ustat));
    expect(block.filter((l) => l.startsWith("- site "))).toEqual([
      '- site "thm:excess_risk | wainwright2019high | Theorem 3.27" — the proof of thm:excess_risk cites [wainwright2019high, Theorem 3.27]',
      '- site "thm:smooth_clt | van2000asymptotic | Theorem 11.2" — the proof of thm:smooth_clt cites [van2000asymptotic, Theorem 11.2]',
      '- site "thm:smooth_clt | van2000asymptotic | Theorem 12.3" — the proof of thm:smooth_clt cites [van2000asymptotic, Theorem 12.3]',
    ]);
    expect(block.filter((l) => l.startsWith("  > "))[0]).toMatch(new RegExp(`^  > ${wain.units[0]}: Hence a standard concentration inequality`));
    expect(inlineCitationsBlock(ustat, [])).toEqual([]);
  });
});

describe("the accounting is checked (rule i)", () => {
  const all = dismissAll(tbs, [zhang.id]);
  const violationsOf = (extra: Record<string, unknown>): string[] => round(tbs, extra).violations;

  it("an unaccounted site blocks", () => {
    expect(violationsOf({ proof_citations: [ZHANG], dismissed_citations: [] })).toEqual([
      expect.stringMatching(/^\(i\) prop:id: its proof cites \[bingham1989regular, Theorem 1\.56\] at prop:id\/proof\/\d+\/\d+ and the citation "prop:id \| bingham1989regular \| Theorem 1\.56" is not accounted for/),
      expect.stringMatching(/^\(i\) lemma:mu_rate: /),
      expect.stringMatching(/^\(i\) lemma:eta_ipw: /),
    ]);
  });

  it("a site accounted for twice blocks, and a dismissal of no site", () => {
    expect(violationsOf({ proof_citations: [ZHANG], dismissed_citations: [...all, { site: zhang.id, reason: "pointer", note: "" }] })).toEqual([
      expect.stringMatching(/^\(i\) lemma:eta_rate: the citation "lemma:eta_rate \| zhang2023wasserstein \| Proposition 3\.1" is accounted for 2 times \(lem:zhang-prop-3-1, a dismissal \(pointer\)\)/),
    ]);
    expect(violationsOf({ proof_citations: [ZHANG], dismissed_citations: [...all, { site: "lemma:eta_rate | nobody | Theorem 9", reason: "pointer", note: "" }] })).toEqual([
      expect.stringMatching(/^\(i\) dismissed_citations: "lemma:eta_rate \| nobody \| Theorem 9" is not a site of INLINE CITATIONS/),
    ]);
  });

  it("more than 3 units blocks: a citation cannot take the argument around it", () => {
    const first = before(before(ZHANG.units[0]!, tbs), tbs);
    expect(violationsOf({ proof_citations: [{ ...ZHANG, units: [first, ZHANG.units[1]] }], dismissed_citations: all })).toEqual([
      expect.stringMatching(/^\(i\) lem:zhang-prop-3-1: it takes 4 units \(lemma:eta_rate\/proof\/\d+\/\d+ … lemma:eta_rate\/proof\/\d+\/\d+\); an inline citation takes at most 3/),
    ]);
  });

  it("units out of order, of another proof, or that do not hold the citation block", () => {
    const zhangOpen = expect.stringMatching(/^\(i\) lemma:eta_rate: its proof cites \[zhang2023wasserstein/);
    expect(violationsOf({ proof_citations: [{ ...ZHANG, units: [ZHANG.units[1], ZHANG.units[0]] }], dismissed_citations: all })).toEqual([
      expect.stringMatching(/^\(ref\) lem:zhang-prop-3-1: units \[.*\] are not a first and a last unit of the proof of lemma:eta_rate, in order/),
      zhangOpen,
    ]);
    const other = site(tbs, "su2023estimated").units[0]!;
    expect(violationsOf({ proof_citations: [{ ...ZHANG, units: [other, other] }], dismissed_citations: all })).toEqual([expect.stringMatching(/^\(ref\) lem:zhang-prop-3-1: units \[lemma:eta_ipw\/proof/), zhangOpen]);
    const away = before(ZHANG.units[0]!, tbs);
    expect(violationsOf({ proof_citations: [{ ...ZHANG, units: [away, away] }], dismissed_citations: all })).toEqual([
      expect.stringMatching(/^\(i\) lem:zhang-prop-3-1: its units \(.*\) do not hold the citation, which is at lemma:eta_rate\/proof\/\d+\/\d+$/),
    ]);
  });

  it("a node whose text is not the host proof's own words blocks (a hand-edited core)", () => {
    const r = round(tbs, { proof_citations: [ZHANG], dismissed_citations: all });
    const edited = structuredClone(r.core);
    edited.statements.find((s) => s.id === ZHANG.id)!.statement = "The Wasserstein distance is at most $t^{-1}$.";
    expect(lintInlineCitations(edited, tbs, scopeOf(tbs), []).violations[0]).toMatch(/^\(i\) lem:zhang-prop-3-1: its text is not a passage of that proof \(lemma:eta_rate\)/);
    const unwired = structuredClone(r.core);
    unwired.statements.find((s) => s.id === "lem:eta-rate")!.depends_on = [];
    expect(lintInlineCitations(unwired, tbs, scopeOf(tbs), []).violations[0]).toBe("(i) lem:zhang-prop-3-1: lem:eta-rate must depend on it");
  });

  it("a command citing several works needs `cite`, one of them", () => {
    const e: EnvsJson = { ...tbs, envs: [{ ...tbs.envs[0]!, proof: "The bound holds. By \\citep[Theorem 2]{a, b} the claim follows. This ends the proof." }], bibliography: [{ key: "a", text: "a" }, { key: "b", text: "b" }] };
    const s = citationSites(e, scopeOf(e))[0]!;
    const entry = { id: "lem:ab", site: s.id, units: [s.units[0], s.units[0]] };
    expect(round(e, { proof_citations: [entry] }).violations[0]).toMatch(/^\(ref\) lem:ab: the citation names a, b — set `cite`/);
    const r = round(e, { proof_citations: [{ ...entry, cite: "b" }] });
    expect(r.violations).toEqual([]);
    expect(r.core.statements.find((x) => x.id === "lem:ab")).toMatchObject({ statement: "By \\citep[Theorem 2]{a, b} the claim follows.", source: { cite: "b", locator: "Theorem 2" } });
  });

  it("a reference core written before the accounting has neither key; one that accounts has either", () => {
    expect(accountsForCitations(RefCoreSchema.parse(refs(tbs, {})))).toBe(false);
    expect(accountsForCitations(RefCoreSchema.parse(refs(tbs, { dismissed_citations: [] })))).toBe(true);
    // and it materializes as before: no inline node, no edge
    const legacy = materializeRefCore(RefCoreSchema.parse(refs(tbs, {})), tbs, "");
    expect(legacy.violations).toEqual([]);
    expect(legacy.core.statements.every((s) => s.cited_in === undefined && s.depends_on.length === 0)).toBe(true);
  });
});

describe("a core with an inline cited leaf, downstream", () => {
  const { core } = round(ustat, { proof_citations: [WAIN], dismissed_citations: dismissAll(ustat, [wain.id]) });

  it("loads as a typed core, and a core without the field loads as before", () => {
    const again = parseTypedCore(JSON.stringify({ ...core, symbols: [] }), "test");
    expect(again.statements.find((s) => s.id === WAIN.id)!.cited_in).toBe("thm:excess-risk");
    const legacy = { ...core, symbols: [], statements: core.statements.filter((s) => s.id !== WAIN.id).map((s) => ({ ...s, depends_on: s.depends_on.filter((d) => d !== WAIN.id) })) };
    expect(parseTypedCore(JSON.stringify(legacy), "test").statements.map((s) => s.id)).toEqual(legacy.statements.map((s) => s.id));
  });

  it("V1.5 asks for its source; one supplied file per work serves every result cited from it", async () => {
    const runDir = await mkdtemp(path.join(os.tmpdir(), "inline-cite-"));
    tmpDirs.push(runDir);
    const dir = path.join(runDir, "discovery", "cited_sources");
    await mkdir(dir, { recursive: true });
    const only = { ...core, statements: core.statements.filter((s) => s.id !== "lem:emp-pop-rad") } as Core;
    const first = await resolveCitedSources({ runDir, core: only, envs: ustat });
    expect(first.missing.map((m) => [m.nodeId, m.key, m.locator, m.file])).toEqual([[WAIN.id, "wainwright2019high", "Theorem 3.27", "discovery/cited_sources/wainwright2019high.txt"]]);
    await writeFile(path.join(dir, "wainwright2019high.txt"), "Theorem 3.27. Let F be a b-uniformly bounded class …", "utf8");
    expect((await resolveCitedSources({ runDir, core: only, envs: ustat })).sources.map((s) => [s.nodeId, s.mode])).toEqual([[WAIN.id, "supplied"]]);
    // a second result of the same book is shown the same file: whether the file holds it is the
    // referee's to say (no text match decides it)
    const second = { ...core.statements.find((s) => s.id === WAIN.id)!, id: "lem:wainwright-thm-4-10", source: { cite: "wainwright2019high", locator: "Theorem 4.10" } };
    const both = await resolveCitedSources({ runDir, core: { ...only, statements: [...only.statements, second] } as Core, envs: ustat });
    expect(both.sources.map((s) => [s.nodeId, s.mode])).toEqual([[WAIN.id, "supplied"], ["lem:wainwright-thm-4-10", "supplied"]]);
    expect(both.missing).toEqual([]);
  });

  it("the referee is shown its passage as the statement and the host's proof as context, never as its proof", () => {
    const flat = ustat.envs.flatMap((x) => [x.body, ...(x.proof ? [x.proof] : [])]).join("\n\n\n");
    const ex = nodeExcerpts(paperIndex(flat, null, ustat), core, WAIN.id);
    expect(ex.statement.text).toContain("Hence a standard concentration inequality (Theorem 3.27 \\citet{wainwright2019high})");
    expect(ex.proof).toBeNull();
    expect(ex.context!.of).toBe("thm:excess-risk");
    expect(ex.context!.excerpt.text).toContain("standard symmetrization argument \\citep{wainwright2019high}");
    expect(nodeExcerpts(paperIndex(flat, null, ustat), core, "thm:excess-risk").context).toBeUndefined();
  });

  it("the plan gate takes it as a cited gate of its host and refuses a plan that drops it from the host's hyps", () => {
    const small = {
      qid: "q",
      cluster: "stat",
      symbols: [],
      assumptions: [],
      definitions: [],
      statements: core.statements.filter((s) => s.id === WAIN.id || s.id === "thm:excess-risk").map((s) => ({ ...s, depends_on: s.depends_on.filter((d) => d === WAIN.id) })),
      target_estimand: "t",
      bibliography: core.bibliography,
    } as unknown as Core;
    const plan = (hyps: string[]) => ({
      qid: "q",
      cluster: "stat",
      lean_subdir: "Stat/Shap",
      env: [{ id: "S1", world: "po-system", binds_symbols: [], binds_sampling_model: true, disposition: "reuse", reuse: "Causalean.PO.System.POStructure", modules: ["Causalean.PO.System"] }],
      nodes: {
        [WAIN.id]: { lean_kind: "assumption", lean_name: "wainwrightConcentration", disposition: "define-local", gate: true, gate_class: "cited", source: "cite:wainwright" },
        "thm:excess-risk": { lean_kind: "theorem", lean_name: "excessRisk", target_file: "Basic.lean", hyps, disposition: "define-local" },
      },
      citations: [{ id: "cite:wainwright", title: "High-dimensional statistics", authors: "Wainwright", year: 2019, locator: "Theorem 3.27" }],
      feasibility: "formalizable-now",
    });
    expect(runPlanGate(plan([WAIN.id]), small).violations).toEqual([]);
    expect(runPlanGate(plan([]), small).violations).toEqual([expect.objectContaining({ code: "P4", where: "thm:excess-risk", message: `logical cited dep '${WAIN.id}' must be an explicit hyp` })]);
  });

  it("the report lists it among the cited results its host rests on, and the host as conditional", () => {
    const input: ReportInput = {
      qid: "q",
      envs: ustat,
      scope: scopeOf(ustat),
      core,
      review: null,
      findings: [{ stage: "V1.5", node: WAIN.id, kind: "note", detail: "cited source checked: source supplied by the user at discovery/cited_sources/wainwright2019high.txt", witness: null, at: "2026-10-09T00:00:00.000Z" }],
      addedAssumptions: [],
      crosswalk: null,
      graph: null,
      lean: null,
      warnings: { lint: [], parser: [] },
      flags: {},
      stageCompleted: "V1.5",
      earlyStop: true,
      sourceSha256: "s",
      inputs: { v1_5_review: "absent", crosswalk_full: "absent", graph_json: "absent", v1_scope: "present", lean_evidence: "absent" },
    };
    const { json, md } = buildReport(input);
    // no row of its own (it is no environment of the paper); its host carries it
    expect(json.results.map((r) => r.node_id)).toEqual(["thm:excess-risk", "lem:emp-pop-rad", "thm:smooth-clt"]);
    const host = json.results.find((r) => r.node_id === "thm:excess-risk")!;
    expect(host.cited_hypotheses.map((c) => [c.id, c.cite, c.locator])).toEqual([[WAIN.id, "wainwright2019high", "Theorem 3.27"]]);
    expect(md).toContain("wainwright2019high");
    expect(md).toContain("Theorem 3.27");
    // what the leaf is: the passage of the host's proof, in the report's record and its text
    const passage = core.statements.find((x) => x.id === WAIN.id)!.statement;
    expect(host.cited_hypotheses[0]).toMatchObject({ cited_in: "thm:excess-risk", passage });
    expect(host.cited_hypotheses[0]!.lean).toBeUndefined();
    expect(md).toContain(`\`${WAIN.id}\` (wainwright2019high, Theorem 3.27), invoked in the proof of \`thm:excess-risk\`:\n\nThe passage of the proof:\n\n> ${passage.split("\n")[0]}`);
  });

  it("the report discloses what Lean assumes for a cited result: the gate's declaration and its statement, beside the passage", async () => {
    const dir = await mkdtemp(path.join(os.tmpdir(), "inline-cited-lean-"));
    tmpDirs.push(dir);
    const DECL = ["/-- Wainwright, Theorem 3.27, as the proof uses it. -/", "def WainwrightLocalization (b : ℝ) : Prop :=", "  ∀ δ > 0, δ ≤ b → True"].join("\n");
    await mkdir(path.join(dir, "Helpers"), { recursive: true });
    await writeFile(path.join(dir, "Helpers", "CitedGates.lean"), ["import Mathlib", "", "namespace Papers.Shap", "", DECL, "", "theorem other : True := trivial", "", "end Papers.Shap", ""].join("\n"));
    let g = createEmptyGraph("q");
    g = addNode(g, { id: WAIN.id, kind: "gate", provenance: "from-note", nl_statement: "p", tex_anchor: "" });
    g = setLean(g, WAIN.id, "Papers.Shap.WainwrightLocalization", "Helpers/CitedGates.lean");
    g.nodes[0]!.gate = { gate_class: "cited", source: "cite:wainwright2019high" };
    const citedLean = await citedGateDeclarations(core, g, dir);
    const lean = { decl: "Papers.Shap.WainwrightLocalization", file: "Helpers/CitedGates.lean", line: 6, statement: DECL.split("\n").slice(1).join("\n") };
    expect(citedLean).toEqual({ [WAIN.id]: lean });
    // a declaration that is not in the file is said so, never guessed
    expect(await citedGateDeclarations(core, setLean(g, WAIN.id, "Papers.Shap.Missing", "Helpers/CitedGates.lean"), dir)).toEqual({ [WAIN.id]: { decl: "Papers.Shap.Missing", file: "Helpers/CitedGates.lean", line: null, statement: null } });
    const { json, md } = buildReport({
      qid: "q", envs: ustat, scope: scopeOf(ustat), core, review: null, findings: [], addedAssumptions: [], crosswalk: [], graph: g, lean: null, citedLean, warnings: { lint: [], parser: [] }, flags: {},
      stageCompleted: "F5", earlyStop: false, sourceSha256: "s", inputs: { v1_5_review: "absent", crosswalk_full: "absent", graph_json: "present", v1_scope: "present", lean_evidence: "absent" },
    });
    const c = json.results.find((r) => r.node_id === "thm:excess-risk")!.cited_hypotheses[0]!;
    const passage = core.statements.find((x) => x.id === WAIN.id)!.statement;
    expect(c).toMatchObject({ id: WAIN.id, lean, cited_in: "thm:excess-risk", passage });
    const shown = (indent: string, at: string): string =>
      [`What Lean assumes for it: \`Papers.Shap.WainwrightLocalization\` (\`${at}\`)`, "", "```lean", ...lean.statement.split("\n"), "```", "", "The passage of the proof:", "", ...passage.split("\n").map((l) => `> ${l}`)].map((l) => (l ? indent + l : l)).join("\n");
    // the technical list, then the plain-language one
    expect(md).toContain(`\`${WAIN.id}\` (wainwright2019high, Theorem 3.27), invoked in the proof of \`thm:excess-risk\`:\n\n${shown("", "Helpers/CitedGates.lean:6")}`);
    expect(md).toContain(`- wainwright2019high, Theorem 3.27 — not checked against its source\n\n${shown("  ", "Helpers/CitedGates.lean:6")}`);
    // MATCH.md: beside the result whose proof invokes it, and nowhere else
    const match = renderMatch({ report: json, links: null, tags: new Map(), core, leanDir: "lean/Papers/Shap" });
    expect(match.split(`**Taken from the literature: wainwright2019high, Theorem 3.27.**\n\n${shown("", "lean/Papers/Shap/Helpers/CitedGates.lean:6")}`)).toHaveLength(2);
  });

  it("the page shows it at its host, and the annotated paper puts its note at the citing passage of the proof", () => {
    const w = coreWhere({ statements: [{ id: "thm:excess-risk", kind: "theorem", tex_locator: { label: "thm:excess_risk" } }, { id: WAIN.id, kind: "lemma", cited_in: "thm:excess-risk" }] } as never);
    expect(w.places).toEqual({ "thm:excess-risk": { anchor: "lbl-thm-excess-risk" }, [WAIN.id]: { anchor: "lbl-thm-excess-risk" } });

    const body = "The bound $a \\le b$ holds.";
    const proof = "We start from the definition. By \\citep[Theorem 2]{k} we get $a \\le c$. Since $c \\le b$ the claim follows.";
    const TEX = ["\\documentclass{article}", "\\begin{document}", "\\begin{lemma}\\label{lem:a}", body, "\\end{lemma}", "\\begin{proof}", proof, "\\end{proof}", "\\end{document}"].join("\n");
    const env: TexEnv = { id: "lem:a", kind: "lemma", envName: "lemma", label: "lem:a", title: null, body, proof, lines: { file: "main.tex", from: 3, to: 5, env: "lemma", label: "lem:a" }, proofLines: { file: "main.tex", from: 6, to: 8, env: "proof", label: null }, refs: [] };
    const envs: EnvsJson = { main_file: "main.tex", files: ["main.tex"], newtheorem: {}, envs: [env], bibliography: [{ key: "k", text: "k" }] };
    const s = citationSites(envs, ["lem:a"])[0]!;
    const ref = RefCoreSchema.parse({ qid: "q", target_estimand: "t", statements: [{ id: "lem:a", kind: "lemma", env: "lem:a" }], proof_citations: [{ id: "lem:k-thm-2", site: s.id, units: [s.units[0], s.units[0]] }] });
    const transcribed = materializeRefCore(ref, envs, TEX).core;
    expect(lintInlineCitations(transcribed, envs, ["lem:a"], []).violations).toEqual([]);
    const plan = planAnnotations({
      files: { "main.tex": TEX },
      envs,
      flatText: TEX,
      lineMap: TEX.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 })),
      refs: ref,
      transcribed,
      core: transcribed,
      patches: null,
      paperErrors: {},
      findings: [],
      review: null,
      // a decision pending on the leaf (the path that places a note on a node as it stands)
      pending: { weakening: [], rewind: null, cap: { counter: "patch_rounds", rounds: 2, cap: 2, origin: "V1.5", summary: "", findings: [{ id: "lem:k-thm-2", axis: "correctness", detail: "The cited theorem needs a bounded class.", witness: null }] } },
    });
    expect(plan.unlocated).toEqual([]);
    expect(plan.records.map((r) => [r.node, r.file, r.line])).toEqual([["lem:k-thm-2", "main.tex", 7]]);
    const out = applyEdits(TEX, plan.edits["main.tex"] ?? []);
    expect(out.indexOf("The cited theorem needs a bounded class.")).toBeGreaterThan(out.indexOf("By \\citep[Theorem 2]{k} we get"));
    expect(out.indexOf("The cited theorem needs a bounded class.")).toBeLessThan(out.indexOf("the claim follows."));
  });

  // live lms: a leaf repaired on its host (a note only) and a condition on a leaf were "not found" — blocking TODO items
  it("a leaf repaired on its host with no text of its own is not unplaced, and a condition on a leaf goes after its host", () => {
    const body = "The bound $a \\le b$ holds.";
    const proof = "We start from the definition. By \\citep[Theorem 2]{k} we get $a \\le c$. Since $c \\le b$ the claim follows.";
    const TEX = ["\\documentclass{article}", "\\begin{document}", "\\begin{lemma}\\label{lem:a}", body, "\\end{lemma}", "\\begin{proof}", proof, "\\end{proof}", "\\end{document}"].join("\n");
    const env: TexEnv = { id: "lem:a", kind: "lemma", envName: "lemma", label: "lem:a", title: null, body, proof, lines: { file: "main.tex", from: 3, to: 5, env: "lemma", label: "lem:a" }, proofLines: { file: "main.tex", from: 6, to: 8, env: "proof", label: null }, refs: [] };
    const envs: EnvsJson = { main_file: "main.tex", files: ["main.tex"], newtheorem: {}, envs: [env], bibliography: [{ key: "k", text: "k" }] };
    const s = citationSites(envs, ["lem:a"])[0]!;
    const ref = RefCoreSchema.parse({ qid: "q", target_estimand: "t", statements: [{ id: "lem:a", kind: "lemma", env: "lem:a" }], proof_citations: [{ id: "lem:k-thm-2", site: s.id, units: [s.units[0], s.units[0]] }] });
    const transcribed = materializeRefCore(ref, envs, TEX).core;
    const base = { files: { "main.tex": TEX }, envs, flatText: TEX, lineMap: TEX.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 })), refs: ref, transcribed, paperErrors: {}, findings: [], review: null, pending: null };
    const leaf = { node: "lem:k-thm-2", corrected_statement: null, ops: [], proof_note: "This cited passage is repaired on Lemma~\\ref{lem:a}." };
    const host = { node: "lem:a", corrected_statement: null, ops: [], drops: ["lem:k-thm-2"], proof_note: "The step is now proved directly." };
    const file = (ps: object[]) => ({ key_results: ["lem:a"], key_contribution: "k", unfixable: [], patches: ps }) as never;
    expect(planAnnotations({ ...base, core: transcribed, patches: file([leaf, host]) } as never).unlocated.filter((u) => u.node === "lem:k-thm-2")).toEqual([]);
    // a note-only leaf whose host carries no repair is still reported: nothing else shows it
    expect(planAnnotations({ ...base, core: transcribed, patches: file([leaf]) } as never).unlocated.map((u) => u.node)).toContain("lem:k-thm-2");
    const cond = { id: "ass:bk-owner-1", kind: "regularity", condition: "Here the cited theorem is read on the whole space.", bookkeeping: { flag: true, added_by: "owner", reason: "r" } };
    const core = { ...transcribed, assumptions: [...transcribed.assumptions, cond], statements: transcribed.statements.map((x) => (x.id === "lem:k-thm-2" ? { ...x, depends_on: [...x.depends_on, cond.id] } : x)) } as Core;
    const plan = planAnnotations({ ...base, core, patches: null } as never);
    expect(plan.unlocated).toEqual([]);
    const out = applyEdits(TEX, plan.edits["main.tex"] ?? []);
    expect(out.indexOf("read on the whole space")).toBeGreaterThan(out.indexOf("\\end{lemma}"));
    // … named as the cited result's condition, never read as a hypothesis of the host
    expect(out).toMatch(/For a result cited in the proof of Lemma~\\ref\{lem:a\}: Here the cited theorem/u);
    expect(plan.records.find((r) => r.kind === "condition added")).toMatchObject({ node: "lem:k-thm-2", located_by: "after-env" });
  });

  // live wss: "with no cited node of its own" was said of the lemma the paper states as that cited result
  it("a repair that cites the result an ordinary cited leaf already is — the node itself or a dependency — is not listed", () => {
    const stated = { id: "lem:stated", status: "cited", depends_on: [], source: { cite: "bartlett2005local", locator: "Lemma A.4" } };
    const host = { id: "thm:h", status: "to-prove", depends_on: ["lem:stated"] };
    const c = { statements: [stated, host] } as never;
    const tex = "By \\citet[Lemma A.4]{bartlett2005local} the bound holds.";
    expect(repairCitationWarnings(c, [{ node: "lem:stated", ops: [{ tex }] }, { node: "thm:h", ops: [{ tex }] }], () => true)).toEqual([]);
    expect(repairCitationWarnings(c, [{ node: "thm:h", ops: [{ tex: "By \\citet[Lemma A.5]{bartlett2005local} the bound holds." }] }], () => true)).toHaveLength(1);
  });

  it("a repair whose proof cites a located result no inline leaf of that host registers is listed for the referee", () => {
    const lines = repairCitationWarnings(
      core,
      [
        { node: "thm:excess-risk", ops: [{ tex: "By \\citet[Theorem 3.27]{wainwright2019high} and \\cite[Lemma 2]{other2020}, the bound holds." }], proof_note: "By \\cite[Theorem 9]{note2021}." },
        { node: "thm:smooth-clt", ops: [], proof_note: "As in \\citep{van2000asymptotic}; see \\citep[Theorem 12.3]{van2000asymptotic}." },
      ],
      (p) => (p.ops ?? []).length > 0,
    );
    expect(lines).toEqual([
      "thm:excess-risk: the repair of thm:excess-risk cites [other2020, Lemma 2] in the proof it writes: a published result used inside the repaired proof, with no cited node of its own. Not a defect of the node or of its wiring: grade the step as any use of a published result.",
      expect.stringMatching(/^thm:smooth-clt: the repair of thm:smooth-clt cites \[van2000asymptotic, Theorem 12\.3\]/),
    ]);
  });

  it("a repair that reroutes the host's proof drops the leaf: accepted on a proof-only patch, and the rebuilt core has neither the edge nor the node", () => {
    const patch = (drops: string[]) => ({ node: "thm:excess-risk", corrected_statement: null, ops: [], drops, proof_note: "By \\citet[Theorem 3.27]{wainwright2019high} applied to the truncated class, the bound holds." });
    const file = (drops: string[]): PatchFile => ({ key_results: ["thm:excess-risk"], key_contribution: "the excess-risk bound", patches: [patch(drops)], unfixable: [] }) as PatchFile;
    expect(core.statements.find((s) => s.id === "thm:excess-risk")!.depends_on).toContain(WAIN.id);
    expect(validatePatchFile(core, file([WAIN.id]), ["thm:excess-risk"])).toEqual([]);
    // any other dependency still needs a corrected statement to be dropped
    const other = core.statements.find((s) => s.id === "thm:excess-risk")!.depends_on.find((d) => d !== WAIN.id)!;
    expect(validatePatchFile(core, file([WAIN.id, other]), ["thm:excess-risk"])).toEqual(['the patch for "thm:excess-risk" drops dependencies but leaves the statement as printed: a result drops one only in its corrected statement.']);
    // … and so does the leaf of another result's proof
    const foreign = { ...core, statements: core.statements.map((s) => (s.id === WAIN.id ? { ...s, cited_in: "thm:smooth-clt" } : s)) } as Core;
    expect(validatePatchFile(foreign, file([WAIN.id]), ["thm:excess-risk"])).toHaveLength(1);
    const rebuilt = applyPatchFile(core, file([WAIN.id])).core;
    expect(rebuilt.statements.map((s) => s.id)).not.toContain(WAIN.id);
    expect(rebuilt.statements.find((s) => s.id === "thm:excess-risk")!.depends_on).not.toContain(WAIN.id);
    expect(rebuilt.statements).toHaveLength(core.statements.length - 1);
    // a reading a repair states on a hypothesis the dropped leaf used is wired into the results that stay,
    // never into the leaf (the build refused the file: "… is not a statement of the core")
    const hyp = "ass:leaf-class-bounded";
    const withHyp = {
      ...core,
      assumptions: [...core.assumptions, { id: hyp, kind: "regularity", condition: "the class is bounded" }],
      statements: core.statements.map((s) => (s.id === WAIN.id || s.id === "thm:excess-risk" ? { ...s, depends_on: [...s.depends_on, hyp] } : s)),
    } as Core;
    const read = { ...file([WAIN.id]), patches: [patch([WAIN.id]), { node: hyp, corrected_statement: null, ops: [], readings: ["the reading the repair states"], proof_note: "p" }] } as PatchFile;
    const built = applyPatchFile(withHyp, read).core;
    expect(built.statements.map((s) => s.id)).not.toContain(WAIN.id);
    const reading = built.assumptions.find((a) => a.condition === "the reading the repair states")!;
    expect(built.statements.filter((s) => s.depends_on.includes(reading.id)).map((s) => s.id)).toEqual(["thm:excess-risk"]);
    // a hypothesis only the leaf and its host used, both dropping it, leaves the core with the leaf
    const only = "def:leaf-only-metric";
    const withOnly = {
      ...core,
      definitions: [...core.definitions, { id: only, name: "metric", construction: "the metric of the leaf" }],
      statements: core.statements.map((s) => (s.id === WAIN.id || s.id === "thm:excess-risk" ? { ...s, depends_on: [...s.depends_on, only] } : s)),
    } as Core;
    const both = { ...file([WAIN.id]), patches: [{ ...patch([WAIN.id, only]), corrected_statement: "the bound holds for the truncated class" }] } as PatchFile;
    expect(applyPatchFile(withOnly, both).core.definitions.map((d) => d.id)).not.toContain(only);
    // while another result still uses the leaf, it stays
    const shared = { ...core, statements: core.statements.map((s) => (s.id === "thm:smooth-clt" ? { ...s, depends_on: [...s.depends_on, WAIN.id] } : s)) } as Core;
    expect(applyPatchFile(shared, file([WAIN.id])).core.statements.map((s) => s.id)).toContain(WAIN.id);
    // the citation the repair writes is then a published result with no node of its own: said to the referee
    const warned = [expect.stringMatching(/^thm:excess-risk: the repair of thm:excess-risk cites \[wainwright2019high, Theorem 3\.27\] in the proof it writes/)];
    expect(repairCitationWarnings(core, [patch([])], () => false)).toEqual([]);
    expect(repairCitationWarnings(core, [patch([WAIN.id])], () => false)).toEqual(warned);
    expect(repairCitationWarnings(rebuilt, [patch([WAIN.id])], () => false)).toEqual(warned);
  });
});

describe("the window of a long cited source", () => {
  const pad = (n: number): string => "Some theorems of the preface are recalled here. ".repeat(Math.ceil(n / 48)).slice(0, n);
  it("sits at the result's number, not at the first occurrence of the locator's word", () => {
    const numbered = `${pad(30000)}\\textbf{Thm 3.27.} Let F be b-uniformly bounded.${pad(30000)}`;
    expect(excerptAround(numbered, "Theorem 3.27", 12000, true)).toContain("Let F be b-uniformly bounded.");
    // each result of a joined locator is tried
    const joined = `${pad(30000)}Theorem 12.3. A U-statistic is asymptotically normal.${pad(30000)}`;
    expect(excerptAround(joined, "Theorems 11.2 and 12.3", 12000, true)).toContain("A U-statistic is asymptotically normal.");
    // a number is matched whole, and the word is the fallback
    const inside = `${pad(30000)}see (13.27) and 3.270${pad(30000)}Result 3.27 holds.${pad(30000)}`;
    expect(excerptAround(inside, "Theorem 3.27", 12000, true)).toContain("Result 3.27 holds.");
    const plain = "Some results of the preface are recalled here. ".repeat(700);
    expect(excerptAround(`${plain}The Theorem. X.${plain}`, "Theorem 2", 12000, true)).toContain("The Theorem. X.");
    // an ordinary cited leaf keeps the window it always had (it is part of its verdict's basis)
    expect(excerptAround(numbered, "Theorem 3.27", 12000)).not.toContain("Let F be b-uniformly bounded.");
  });
});

describe("what the audit of the registration found", () => {
  const vdv = (l: string) => site(ustat, "van2000asymptotic", l);
  const flatProof = (proof: string, extra: Partial<TexEnv> = {}): TexEnv => ({ id: "thm:y", kind: "theorem", envName: "theorem", label: "thm:y", title: null, body: "The claim holds.", proof, proofLines: { file: "main.tex", from: 30, to: 40, env: "proof", label: null }, lines: { file: "main.tex", from: 20, to: 25, env: "theorem", label: "thm:y" }, refs: [], ...extra });

  it("a paper with no parsed bibliography: its sites are warnings, never accountable — block, lint and materializer alike", () => {
    const bare: EnvsJson = { ...tbs, bibliography: [] };
    expect(inlineCitationsBlock(bare, scopeOf(bare))).toEqual([]);
    const r = round(bare, { proof_citations: [], dismissed_citations: [] });
    expect(r.violations).toEqual([]);
    expect(r.warnings).toHaveLength(citationSites(bare, scopeOf(bare)).length);
    expect(r.warnings.find((w) => w.includes("zhang2023wasserstein"))).toMatch(
      /^lem:eta-rate: the proof of lemma:eta_rate invokes \[zhang2023wasserstein, Proposition 3\.1\] \(.*\): a published result used inside the proof, with no cited node of its own \(zhang2023wasserstein is not in the parsed bibliography, so none can be made\)\. Not a defect/,
    );
    expect(round(bare, { proof_citations: [ZHANG] }).violations[0]).toBe(`(ref) lem:zhang-prop-3-1: site "${zhang.id}" is not a site of INLINE CITATIONS`);
    // one work of the bibliography among several others: only its sites are accountable
    const one: EnvsJson = { ...tbs, bibliography: [{ key: "zhang2023wasserstein", text: "z" }] };
    expect(inlineCitationsBlock(one, scopeOf(one)).filter((l) => l.startsWith("- site "))).toEqual([expect.stringContaining(zhang.id)]);
    expect(round(one, { proof_citations: [ZHANG] }).violations).toEqual([]);
  });

  it("several results cited in one sentence are ONE entry (`sites`) and one leaf naming them all", () => {
    const entry = { id: "lem:vdv-11-2-12-3", sites: [vdv("Theorem 11.2").id, vdv("Theorem 12.3").id], units: [vdv("Theorem 11.2").units[0], vdv("Theorem 11.2").units[0]] };
    const r = round(ustat, { proof_citations: [WAIN, entry] });
    expect(r.violations).toEqual([]);
    const leaves = r.core.statements.filter((x) => x.cited_in === "thm:smooth-clt");
    expect(leaves.map((x) => [x.id, x.source!.cite, x.source!.locator])).toEqual([["lem:vdv-11-2-12-3", "van2000asymptotic", "Theorems 11.2 and 12.3"]]);
    expect(leaves[0]!.statement).toContain("Theorems 11.2 and 12.3 from \\citet{van2000asymptotic} imply");
    // each of its sites is accounted for once: a dismissal of one of them is a second account
    expect(round(ustat, { proof_citations: [WAIN, entry], dismissed_citations: [{ site: vdv("Theorem 12.3").id, reason: "method", note: "" }] }).violations).toEqual([
      expect.stringMatching(/^\(i\) thm:smooth_clt: the citation "thm:smooth_clt \| van2000asymptotic \| Theorem 12\.3" is accounted for 2 times \(lem:vdv-11-2-12-3, a dismissal \(method\)\)/),
    ]);
    expect(RefCoreSchema.safeParse(refs(ustat, { proof_citations: [{ ...entry, site: wain.id }] })).success).toBe(false);
    expect(round(ustat, { proof_citations: [{ ...entry, sites: [wain.id, vdv("Theorem 11.2").id] }] }).violations[0]).toMatch(/^\(ref\) lem:vdv-11-2-12-3: sites .* are not the results of one citation/);
    expect([joinLocators(["Theorem 1", "Theorem 2", "Theorem 3"]), joinLocators(["Theorem 6.5", "Corollary 6.7"]), joinLocators(["Lemma A.4"])]).toEqual(["Theorems 1, 2 and 3", "Theorem 6.5 and Corollary 6.7", "Lemma A.4"]);
    expect(locatorsIn(joinLocators(["Theorem 1", "Theorem 2", "Corollary 6.7"]))).toEqual(["Theorem 1", "Theorem 2", "Corollary 6.7"]);
  });

  it("a restated cited leaf covers an inline citation of the SAME result only", () => {
    const stated: TexEnv = { ...flatProof(""), id: "lem:x", kind: "lemma", envName: "lemma", label: "lem:x", proof: null, proofLines: null, lines: { file: "main.tex", from: 5, to: 9, env: "lemma", label: "lem:x" } };
    const envsOf = (locator: string): EnvsJson => ({ ...ustat, envs: [stated, flatProof(`We bound the term. By \\cite[${locator}]{bartlett2005local} the claim follows.`)] });
    const violationsOf = (e: EnvsJson): string[] => {
      const ref = refs(e, { dismissed_citations: [] }) as { statements: Array<{ id: string; depends_on?: string[] }> };
      ref.statements.find((x) => x.id === "thm:y")!.depends_on = ["lem:x"]; // the leaf restates Theorem A.4
      const core = materializeRefCore(RefCoreSchema.parse(ref), e, "").core;
      return lintInlineCitations(core, e, scopeOf(e), []).violations;
    };
    expect(violationsOf(envsOf("Theorem A.4"))).toEqual([]);
    expect(violationsOf(envsOf("Theorem 5"))).toEqual([expect.stringMatching(/^\(i\) thm:y: its proof cites \[bartlett2005local, Theorem 5\] .* is not accounted for/)]);
  });

  it("one result cited at two distant places of a proof: one leaf, and a warning naming the place it does not hold", () => {
    const e: EnvsJson = { ...ustat, envs: [flatProof("By \\cite[Theorem 2]{wainwright2019high} we get $a \\le c$. Since $c \\le d$ we get $a \\le d$. Next $d \\le e$ holds. Then $e \\le f$ holds. Again by \\cite[Theorem 2]{wainwright2019high} we get $f \\le g$.")] };
    const s = citationSites(e, scopeOf(e))[0]!;
    expect(s.units).toHaveLength(2);
    const ref = RefCoreSchema.parse({ qid: "q", target_estimand: "t", statements: [{ id: "thm:y", kind: "theorem", env: "thm:y" }], proof_citations: [{ id: "lem:w", site: s.id, units: [s.units[0], s.units[0]] }] });
    const m = materializeRefCore(ref, e, "");
    expect(m.violations).toEqual([]);
    expect(lintInlineCitations(m.core, e, scopeOf(e), [])).toEqual({
      violations: [],
      warnings: [
        `thm:y: the proof of thm:y cites [wainwright2019high, Theorem 2] also at ${s.units[1]}, outside the passage lem:w registers (${s.units[0]} … ${s.units[0]}): ` +
          "a published result used there with no cited node covering that use. Not a defect of the node or of its wiring: grade the step as any use of a published result.",
      ],
    });
  });

  it("a citation in the proof of a result that is itself a cited leaf is a warning, not accountable", () => {
    const e: EnvsJson = { ...ustat, envs: [flatProof("By \\cite[Theorem 2]{wainwright2019high} the claim follows.")] };
    const s = citationSites(e, scopeOf(e))[0]!;
    const cited = { qid: "q", target_estimand: "t", statements: [{ id: "thm:y", kind: "theorem", env: "thm:y", status: "cited", source: { cite: "bartlett2005local", locator: "Theorem 1", verbatim_statement: "…" } }] };
    const check = (extra: Record<string, unknown>) => {
      const ref = RefCoreSchema.parse({ ...cited, ...extra });
      const m = materializeRefCore(ref, e, "");
      return { ref: m.violations, ...lintInlineCitations(m.core, e, scopeOf(e), ref.dismissed_citations ?? []) };
    };
    expect(check({ dismissed_citations: [] })).toEqual({ ref: [], violations: [], warnings: [expect.stringMatching(/^thm:y: the proof of thm:y invokes \[wainwright2019high, Theorem 2\] .* with no cited node of its own \(thm:y is itself a cited result\)/)] });
    expect(check({ dismissed_citations: [{ site: s.id, reason: "pointer", note: "" }] }).violations).toEqual([]);
    expect(check({ proof_citations: [{ id: "lem:w", site: s.id, units: [s.units[0], s.units[0]] }] }).ref).toEqual(["(ref) lem:w: thm:y is a cited result of this core: a citation in its proof needs no entry — remove this one"]);
  });

  const { core } = round(ustat, { proof_citations: [WAIN], dismissed_citations: dismissAll(ustat, [wain.id]) });
  const verdict = (id: string, over: Partial<V15NodeVerdict> = {}): V15NodeVerdict => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "reproduced", witness: null, fix: null, bookkeeping_assumption: null, reading: null, ...over });
  const failed = verdict(WAIN.id, { correctness: "error", detail: "the class is not uniformly bounded", witness: "an unbounded class", witness_regime: "in_scope" });

  it("an error graded on the leaf is routed as its host's, whether or not the host was graded; an unclear stays", () => {
    const inline = inlineLeaves(core);
    expect([...inline]).toEqual([[WAIN.id, { host: "thm:excess-risk", cite: "wainwright2019high", locator: "Theorem 3.27" }]]);
    const results = new Set(core.statements.map((s) => s.id));
    const route = (nodes: V15NodeVerdict[]) => routeReview({ verdict: "FAIL", summary: "", nodes: errorsOnHosts(nodes, inline) } as V15Review, null, results);
    // the grading paused at the leaf's level: the host has no verdict yet
    const paused = route([failed]);
    expect(paused.refuted.map((n) => [n.id, n.witness])).toEqual([["thm:excess-risk", "an unbounded class"]]);
    expect(paused.refuted[0]!.detail).toBe(`the step its proof takes from [wainwright2019high, Theorem 3.27] (${WAIN.id}) does not hold as the proof uses it: the class is not uniformly bounded`);
    // the verdict made for the host takes the error alone, nothing else the leaf's verdict carries
    expect(errorsOnHosts([{ ...failed, basis: "b", graded: "fresh", minimality: true, weakens_contribution: true, split: { why: "x" }, follows_repair_of: ["lem:x"] } as V15NodeVerdict], inline)[1]).toEqual({
      id: "thm:excess-risk", fix: null, faithfulness: "ok", ambiguity: "ok", reading: null, bookkeeping_assumption: null, correctness: "error", witness: "an unbounded class", witness_regime: "in_scope",
      detail: `the step its proof takes from [wainwright2019high, Theorem 3.27] (${WAIN.id}) does not hold as the proof uses it: the class is not uniformly bounded`,
    });
    // the host was graded clean, or with an error of its own
    expect(route([failed, verdict("thm:excess-risk")]).refuted.map((n) => n.id)).toEqual(["thm:excess-risk"]);
    const own = errorsOnHosts([failed, verdict("thm:excess-risk", { correctness: "error", detail: "a term is dropped.", witness: "w" })], inline);
    expect(own.map((n) => [n.id, n.correctness])).toEqual([[WAIN.id, "ok"], ["thm:excess-risk", "error"]]);
    expect(own[1]!.detail).toMatch(/^a term is dropped\. Also: the step its proof takes from \[wainwright2019high, Theorem 3\.27\]/);
    // the source shown lacks the result: the leaf's own, and the run asks for the source
    expect(route([verdict(WAIN.id, { correctness: "unclear", detail: "Theorem 3.27 is not in the source shown" })]).unchecked.map((n) => n.id)).toEqual([WAIN.id]);
    // a core with no inline leaf: nothing moves
    expect(errorsOnHosts([failed], new Map())).toEqual([failed]);
    expect(routeReview({ verdict: "FAIL", summary: "", nodes: [failed] } as V15Review, null, results).refuted.map((n) => n.id)).toEqual([WAIN.id]);
  });

  it("a referee fix dropping the host's edge to the leaf is refused with what to do, not applied and undone", () => {
    const ref = refs(ustat, { proof_citations: [WAIN], dismissed_citations: dismissAll(ustat, [wain.id]) }) as Parameters<typeof applyDriftFixes>[0];
    const out = applyDriftFixes({ ...ref, assumptions: [], definitions: [] }, [{ id: "thm:excess-risk", fix: { remove_depends_on: [WAIN.id] } }]);
    expect(out.applied).toEqual([]);
    expect(out.rejected).toEqual([{ id: "thm:excess-risk", reason: `${WAIN.id} is a \`proof_citations\` entry, whose edge is not an edit: when the proof does not rely on the cited result, move its site to \`dismissed_citations\`` }]);
  });

  it("the Lean stages read the cited work's file of the run as the statement of record, never the passage", async () => {
    const runDir = await mkdtemp(path.join(os.tmpdir(), "inline-cite-f-"));
    tmpDirs.push(runDir);
    const plan = { nodes: { [WAIN.id]: { source: "cite:w" } }, citations: [{ id: "cite:w", locator: "?", verbatim_statement: "Hence a standard concentration inequality …" }] };
    expect(copyVerifiedCitedSourcesToPlan(plan, core)).toBe(1);
    expect(plan.citations[0]).toEqual({ id: "cite:w", locator: "Theorem 3.27" });
    const dir = path.join(runDir, "discovery", "cited_sources");
    await mkdir(dir, { recursive: true });
    // no file, or the work declared unavailable: never "attested"
    await writeFile(path.join(dir, "wainwright2019high.unavailable"), "the library copy is on loan", "utf8");
    expect(await citedSourceOfRecord(runDir, "wainwright2019high", "Theorem 3.27")).toEqual({ text: "", mode: "unverifiable", detail: "no source of wainwright2019high at discovery/cited_sources/wainwright2019high.txt" });
    await writeFile(path.join(dir, "wainwright2019high.arxiv.tex"), "\\begin{theorem} Let F be b-uniformly bounded … \\end{theorem}", "utf8");
    expect(await citedSourceOfRecord(runDir, "wainwright2019high", "Theorem 3.27")).toMatchObject({ mode: "fetched", text: expect.stringContaining("b-uniformly bounded") });
    await writeFile(path.join(dir, "wainwright2019high.txt"), "Theorem 3.27. Let F be a b-uniformly bounded class …", "utf8");
    expect(await citedSourceOfRecord(runDir, "wainwright2019high", "Theorem 3.27")).toEqual({ text: "Theorem 3.27. Let F be a b-uniformly bounded class …", mode: "attested", detail: "source supplied at discovery/cited_sources/wainwright2019high.txt @ Theorem 3.27" });
  });

  it("round A lists a result several proofs invoke once", async () => {
    const leaf = core.statements.find((s) => s.id === WAIN.id)!;
    const twice = { ...core, statements: [...core.statements, { ...leaf, id: "lem:wainwright-again", cited_in: "thm:smooth-clt" }] } as Core;
    const root = await mkdtemp(path.join(os.tmpdir(), "inline-cite-a-"));
    tmpDirs.push(root);
    expect((await roundACandidates(tk(root), "q", twice, null)).map((c) => c.candidate_id)).toEqual(["lem:emp-pop-rad", WAIN.id]);
  });

  it("the prompts state the one rule: the node stands only for what the cited result gives", () => {
    const prompt = (rel: string): string => readFileSync(path.join(path.dirname(fileURLToPath(import.meta.url)), "..", "..", "src", rel), "utf8").replace(/\s+/g, " ");
    const v1 = prompt("verify/prompts/V1/extract_core.txt");
    expect(v1).toContain("A unit that also holds deductions of the proof's own is taken whole — that cannot be avoided, and the node still stands only for what the cited result gives.");
    expect(v1).toContain("give `sites`, the list of their ids, in place of `site`: one entry, one node.");
    const referee = prompt("verify/prompts/V1.5/review.txt");
    expect(referee).toContain("The node stands ONLY for what the passage attributes to the cited result: the assertion the citation is attached to");
    expect(referee).toContain("For such a node the following REPLACES the checks of CITED STANDARD RESULTS");
    // a failure is reported where its grader is — the leaf — and the runner moves it (`errorsOnHosts`):
    // the host may be graded by another call, which was never asked about it
    expect(referee).toContain("A failure of either is an error of the HOST's proof, and this node is where you report it: grade THIS node `error`, the witness the hypothesis the host's proof does not establish or the assertion the cited result does not give, `witness_regime` `in_scope`, `witness_instance` the host's setting in which the hypothesis fails or is not established.");
    // … an error, whatever the general rule lets a referee supply; the contract refuses the other grades (`inline_citation_host.test.ts`)
    expect(referee).toContain("A hypothesis of the cited result that the host's statement and hypotheses do not give is an error here, not a line to supply: `bookkeeping` and a `degenerate` witness are never grades of such a node.");
    expect(referee).toContain("never leave it to the host's grader, and never in the `detail` of an `ok`. With no such failure the node is `ok`, with two exceptions.");
    expect(referee).not.toContain("never on this node");
    expect(referee).toContain("`unclear`, only when the source shown under CITED SOURCES does not contain the result the passage names");
    // the node is a leaf (the core refuses a cited node that depends on a result): the paper's own results the
    // host combines with the citation are wired on the host, and their absence here is not drift
    expect(referee).toContain("such a node is a leaf, wired only to the assumptions and definitions its passage uses. A lemma, proposition or theorem of the paper that the host's proof combines with the citation is a dependency of the HOST, graded on the host — its absence from this node is never drift.");
    // … and the global pass, which owns wiring across nodes and is not shown that section, is told the same
    expect(prompt("verify/prompts/V1.5/global.txt")).toContain("A `cited` node is a leaf, wired only to assumptions and definitions: a result of the paper used with it is a dependency of the result that cites it.");
    // the passage's extent is the runner's cut (the referee sees no unit boundary): only a passage
    // without the citation or its assertion is drift
    expect(referee).toContain("or the passage leaves out the citation or the assertion it gives. The passage's extent is otherwise not yours to grade: it is the runner's cut of the proof into pieces, of which V1 takes at most three whole ones, so it may begin or end in the middle of a sentence and may hold more of the host's argument than the citation — never drift.");
    expect(referee).not.toContain("name the units it should take");
    // a wrong dismissal is V1's misreading, routed to V1 — never a finding against the paper
    expect(referee).toContain("A citation read as a mention on which the proof in fact relies is V1's misreading, never a defect of the paper: `drift` on the result being proved, the detail naming the citation to register.");
    expect(referee).toContain("Only a step asserted by analogy with a cited argument that the proof does not carry out is unproved: a correctness finding on that result.");
    // a citation with no node of its own keeps the allowance of any use of a published result (the
    // runner's warning line says so), and the use-or-mention check is asked only of the inline ones
    expect(referee).toContain("The same allowance covers a published result a proof invokes that has no cited node of its own (a named classical theorem; a numbered result that V1 LINT WARNINGS lists as having none).");
    expect(referee).toContain("For each inline citation registered as such a node or listed under V1 LINT WARNINGS as read otherwise (a pointer, a borrowed method, a result proved here, a definition), judge whether the proof USES the cited result or only mentions it.");
    expect(referee).not.toContain("For EVERY citation");
    expect(prompt("verify/prompts/V1/patch.txt")).toContain("A cited result with `cited_in` has no text of its own — it is a passage of the proof of the result named there: a finding about it is repaired on that result, never by ops on it; when the corrected proof no longer takes that step from the cited work, list the node in `drops`.");
    expect(prompt("formalization/prompts/F1/stage1_template.txt")).toContain("its proposition is ONLY what the passage attributes to the cited result — the assertion the citation is attached to — stated in the host's context");
    expect(prompt("formalization/prompts/F4/proof_reviewer.txt")).toContain("the declaration states ONLY what the passage attributes to the cited result, in that result's context; the rest of the passage is that result's to prove and must not be assumed here");
  });
});

// live jpw_always_valid_inference: the proof's text sits in an author's note macro, `\lp{Lemma 3 of
// \cite{PS1975} provides … (three paragraphs) … }` — every passage of at most three units is cut
// inside that group, the registered leaf failed the whole-fragment rule, and V1 could not converge
describe("a citation no well-formed passage can register", () => {
  const env = (proof: string): TexEnv => ({ id: "lem:h", kind: "lemma", envName: "lemma", label: "lem:h", title: null, body: "The bound holds.", proof, proofLines: { file: "main.tex", from: 5, to: 30, env: "proof", label: null }, lines: { file: "main.tex", from: 1, to: 4, env: "lemma", label: "lem:h" }, refs: [] }) as TexEnv;
  const envs = (proof: string): EnvsJson => ({ main_file: "main.tex", files: ["main.tex"], newtheorem: [], envs: [env(proof)], bibliography: [{ key: "k", text: "K (2000) A paper." }] }) as unknown as EnvsJson;
  const filler = Array.from({ length: 6 }, (_, i) => `Sentence number ${i} of the note goes on.`).join(" ");
  it("is a warning that says why, never an entry the lint demands", () => {
    const wrapped = envs(`\\lp{Lemma 3 of \\cite{k} gives the bound. ${filler}\n\n${filler}\n\n${filler}}`);
    expect(citationSites(wrapped, ["lem:h"])).toHaveLength(1);
    expect(inlineCitationsBlock(wrapped, ["lem:h"])).toEqual([]);
    const r = lintInlineCitations({ statements: [] } as never, wrapped, ["lem:h"], []);
    expect(r.violations).toEqual([]);
    expect(r.warnings.join("\n")).toMatch(/no passage of at most 3 units holding it is a whole TeX fragment/);
  });
  it("leaves a citation in plain proof text accountable", () => {
    const plain = envs(`Lemma 3 of \\cite{k} gives the bound. ${filler}`);
    expect(inlineCitationsBlock(plain, ["lem:h"]).length).toBeGreaterThan(0);
    expect(lintInlineCitations({ statements: [] } as never, plain, ["lem:h"], []).violations).toHaveLength(1);
  });
});
