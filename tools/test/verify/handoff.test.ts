/**
 * Stage hand-offs, replayed on REAL runs. Each case takes what one stage persisted on a finished
 * run and feeds it to the next stage's own reader or gate, asserting that the reader accepts it
 * and reproduces what the runner persisted downstream. A stub only emits what we thought to
 * write; the boundary bugs (a plan shape the round-A reader refused, a gate demanding proofs at
 * scaffold time, a proved citation reported as an unproved input) only showed on real papers.
 *
 * Fixtures (`fixtures/handoff/<slug>/`) are byte-for-byte copies of the run's files, gzipped,
 * under their run-relative paths, from runs of the maintainer's own papers: `tbs_extreme_effects`
 * (V1.5 → core, F1 → round A and plan gate, rulings; the run as committed to its toolkit after F1),
 * `tbs_neural_causal_pi` (F1 → round A and plan gate, F5 → V6, rulings), `tbs_prte_optimal_transport`
 * (F1 → round A and plan gate, rulings). Each test unpacks a run into a temporary toolkit and calls the
 * production readers on it. A deliberate rule change that alters what a stage derives shows up
 * here: re-copy the fixtures from a run made under the new rule, never edit them by hand.
 */
import { createHash } from "node:crypto";
import { readdirSync } from "node:fs";
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { gunzipSync } from "node:zlib";
import { afterEach, describe, expect, it } from "vitest";
import { readTypedCore } from "../../src/core/core_io.js";
import { coreNodeIds, type Core } from "../../src/core/schema.js";
import { runPlanGate } from "../../src/formalization/plan/plan_gate.js";
import { PlanSchema } from "../../src/formalization/plan/schema.js";
import { canonicalizeCitedPlanAfterF2 } from "../../src/formalization/stage2.js";
import { planSchemaViolations, roundACandidates } from "../../src/proposals/round_a.js";
import { readRunCore } from "../../src/proposals/round_b.js";
import type { StateJson } from "../../src/types.js";
import { REVIEW_ADDED_BY, buildCore } from "../../src/verify/core_graph.js";
import { proofReviewRewindAxis, rejectedMatch, renderRuledOut } from "../../src/verify/cross_stage_rewind.js";
import type { LeanEvidence } from "../../src/verify/lean_evidence.js";
import { readPatchFile, readTranscribedCore } from "../../src/verify/patches.js";
import type { VerifyReportJson } from "../../src/verify/report.js";
import { makeStageV6 } from "../../src/verify/stage_v6_report.js";
import { VERIFY_FILES, type V15Review } from "../../src/verify/types.js";
import { tk } from "../toolkit/helpers.js";

const FIXTURES = path.join(path.dirname(fileURLToPath(import.meta.url)), "fixtures", "handoff");

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const dir of tmpDirs.splice(0)) await rm(dir, { recursive: true, force: true });
});

/** Every fixture file of `slug`, run-relative, without the `.gz`. */
function fixtureFiles(slug: string, dir = ""): string[] {
  return readdirSync(path.join(FIXTURES, slug, dir), { withFileTypes: true }).flatMap((e) =>
    e.isDirectory() ? fixtureFiles(slug, path.join(dir, e.name)) : [path.join(dir, e.name.replace(/\.gz$/, ""))],
  );
}

/** Unpack run `slug` into a fresh toolkit root: `<root>/runs/<slug>/…` as the run left it. */
async function unpackRun(slug: string): Promise<{ root: string; runDir: string }> {
  const root = await mkdtemp(path.join(os.tmpdir(), "handoff-"));
  tmpDirs.push(root);
  const runDir = path.join(root, "runs", slug);
  for (const f of fixtureFiles(slug)) {
    await mkdir(path.dirname(path.join(runDir, f)), { recursive: true });
    await writeFile(path.join(runDir, f), gunzipSync(await readFile(path.join(FIXTURES, slug, `${f}.gz`))));
  }
  return { root, runDir };
}

async function readJson<T>(file: string): Promise<T> {
  return JSON.parse(await readFile(file, "utf8")) as T;
}

/** A core without V1.5's acceptance additions (`added_by: "V1.5"` conditions and pins, the edges
 * to them, and the derived `used_by`). */
function withoutReviewAdditions(core: Core): Core {
  const added = new Set(core.assumptions.filter((a) => a.bookkeeping?.added_by === REVIEW_ADDED_BY).map((a) => a.id));
  return {
    ...core,
    assumptions: core.assumptions.filter((a) => !added.has(a.id)).map(({ used_by: _u, ...a }) => a as Core["assumptions"][number]),
    statements: core.statements.map((st) => ({ ...st, depends_on: st.depends_on.filter((d) => !added.has(d)) })),
  };
}

describe("V1/V1.5 → core.json: the pure rebuild reproduces the accepted core", () => {
  // What the runner adds on top of transcription + patches is V1.5's acceptance (`acceptCore`):
  // the referee's bookkeeping conditions and pinned readings, and the symbol table fixes, all from
  // the review on file. Nothing else: the build is byte-identical to the file the run accepted.
  it.each(["tbs_extreme_effects"])("%s", async (slug) => {
    const { runDir } = await unpackRun(slug);
    const transcribed = await readTranscribedCore(runDir);
    // The runner's reader: every repair's texts re-derived from its ops under the current rules.
    const patches = await readPatchFile(runDir);
    const review = await readJson<V15Review>(path.join(runDir, VERIFY_FILES.v15Review));
    const onDisk = await readFile(path.join(runDir, VERIFY_FILES.coreJson), "utf8");
    const state = await readJson<StateJson>(path.join(runDir, "state.json"));

    const addedIds = await readJson<Record<string, string>>(path.join(runDir, VERIFY_FILES.addedIds));
    const built = buildCore(transcribed, { patches, review, symbols: review.symbols ?? null, addedIds });
    const text = JSON.stringify(built.core, null, 2);
    expect(JSON.parse(text)).toEqual(JSON.parse(onDisk));
    expect(text).toBe(onDisk);
    expect(createHash("sha256").update(text).digest("hex")).toBe(state.verify!.core_sha256);

    // The review's additions are exactly the V1.5-tagged records on file; without them, the
    // build is what V1 leaves as core.json before the referee (`rebuildPatchedCore`).
    const accepted = JSON.parse(onDisk) as Core;
    expect(built.added.map((a) => a.id).sort()).toEqual(
      accepted.assumptions.filter((a) => a.bookkeeping?.added_by === REVIEW_ADDED_BY).map((a) => a.id).sort(),
    );
    const beforeReferee = buildCore(transcribed, { patches, symbols: review.symbols ?? null }).core;
    expect(withoutReviewAdditions(beforeReferee)).toEqual(withoutReviewAdditions(accepted));
  });
});

describe("F1 plan → round A and the plan gate", () => {
  it.each(["tbs_extreme_effects", "tbs_neural_causal_pi", "tbs_prte_optimal_transport"])("%s", async (slug) => {
    const { root, runDir } = await unpackRun(slug);
    expect(await planSchemaViolations(root, slug)).toBeNull();

    const raw = await readJson<unknown>(path.join(runDir, "formalization", "plan.json"));
    const core = await readTypedCore(path.join(runDir, VERIFY_FILES.coreJson));
    // F2 writes the plan in canonical form: its post-sync canonicalization has nothing to change.
    expect(canonicalizeCitedPlanAfterF2(structuredClone(raw), core).changed).toBe(false);
    // F1's self-check and F1.5 (no library index here: P5 is off), then F2 at scaffold time.
    // F2's Lean-side checks (P7 tags, a discharged citation's declaration) read the emitted Lean,
    // which the run directory does not hold: not covered here.
    for (const opts of [{}, { proofsNotDue: true }]) {
      const gate = runPlanGate(raw, core, opts);
      expect(gate.violations).toEqual([]);
      expect(gate.ok).toBe(true);
    }

    // Round A's reader on the same plan: the cited results it proposed on the run.
    const cfg = tk(root);
    const candidates = await roundACandidates(cfg, slug, await readRunCore(cfg, slug), PlanSchema.parse(raw));
    const batch = await readJson<{ proposals: Array<{ source: { ref: string } }> }>(path.join(runDir, "proposals", "A.json"));
    expect(candidates.map((c) => c.candidate_id).sort()).toEqual(batch.proposals.map((p) => p.source.ref).sort());
  });
});

describe("F5 → V6: the report stage on the run's inputs reproduces report.json", () => {
  // The Lean audit (full barrel build, `#print axioms`) needs lake; the run stored its result in
  // report.json (`lean_build`, `sorry_scan`, each row's `axioms`), which stands in for it. Left out
  // of the comparison: `inputs.lean_evidence` (it counts every audited declaration, the stored
  // copy has the reported rows' only), `annotated` (the TeX compile and the source tree are not
  // in the fixture), `toolkit` (round B adds it after V6), and `bundle` / `names` (the corrected-paper
  // bundle, written after V6 by `report`).
  it("tbs_neural_causal_pi: the cited gates named from the graph, a result resting on one conditional", async () => {
    const slug = "tbs_neural_causal_pi";
    const { root, runDir } = await unpackRun(slug);
    const stored = await readJson<VerifyReportJson & Record<string, unknown>>(path.join(runDir, VERIFY_FILES.reportJson));
    const axioms: LeanEvidence["axioms"] = {};
    for (const r of stored.results) if (r.lean && r.axioms) axioms[r.lean.decl] = r.axioms;
    // The stage writes the report afresh: the stored one must not be what is read back.
    await rm(path.join(runDir, VERIFY_FILES.reportJson));
    const state = await readJson<StateJson>(path.join(runDir, "state.json"));
    const stage = makeStageV6({
      collectLeanEvidence: async () => ({ build: stored.lean_build!, sorry_scan: stored.sorry_scan!, axioms }),
      compileTex: async () => ({ status: "skipped", tool: null, pdf: null, log_tail: "", reason: "test" }),
    });
    const result = await stage({
      repoRoot: root,
      qid: slug,
      runDir,
      state,
      deps: { runCodex: (() => {
        throw new Error("V6 must never call a model");
      }) as never },
      dryRun: false,
      log: () => {},
    });
    expect(result.status).toBe("completed");

    const built = await readJson<VerifyReportJson & Record<string, unknown>>(path.join(runDir, VERIFY_FILES.reportJson));
    // (The report now says what Lean assumes for a cited result: added to the stored rows, checked below.)
    const rowView = (r: VerifyReportJson["results"][number]) => ({ bucket: r.bucket, cited: r.cited_hypotheses.map(({ lean: _l, ...c }) => c), gates: r.assumed_substrate });
    const rows = (j: VerifyReportJson) => Object.fromEntries(j.results.map((r) => [r.node_id, rowView(r)]));
    // The classification first, for a readable diff; then everything.
    expect(rows(built)).toEqual(rows(stored));
    expect(built.summary).toEqual(stored.summary);
    expect(built.verdict).toBe(stored.verdict);
    // The cited results the run left as source-reviewed gates: none is a row of its own, each is
    // named by its declaration from the graph (with its Lean text), and a result resting on an
    // undischarged one is conditional.
    const gates = new Map(built.results.flatMap((r) => r.cited_hypotheses.map((c) => [c.id, c.lean?.decl] as const)));
    expect([...gates.keys()].sort()).toEqual([
      "lem:consistency-fournier-theorem-2", "lem:deep-nn-yarotsky-theorem-2", "lem:sup-wasserstein-anthony-theorem-17-1",
      "lem:sup-wasserstein-anthony-theorems", "lem:wide-nn-perekrestenko-theorem-viii-1", "lem:wide-nn-yarotsky-theorem-2",
    ]);
    expect(gates.get("lem:wide-nn-yarotsky-theorem-2")).toBe("Papers.TbsNeuralCausalPi.YarotskyCoordinateApprox");
    for (const id of gates.keys()) expect(built.results.some((r) => r.node_id === id)).toBe(false);
    expect(built.results.filter((r) => r.bucket === "conditional").map((r) => r.node_id)).toEqual(["thm:cor-fix-3c402872"]);

    // The paper's grade: key results hold only weakened, but the referee found the key results and
    // the contribution kept — minor
    expect(built.paper_grade?.grade).toBe("minor");
    expect(built.paper_grade?.major).toEqual([]);
    expect(built.paper_grade?.minor.some((x) => x.node === "prop:counterexample-foral" && x.what.startsWith("weakened"))).toBe(true);
    const strip = ({ annotated: _a, toolkit: _t, bundle: _b, names: _n, inputs, ...rest }: VerifyReportJson & Record<string, unknown>) => ({
      ...rest,
      results: rest.results.map((r) => ({ ...r, cited_hypotheses: r.cited_hypotheses.map(({ lean: _l, ...c }) => c) })),
      inputs: { ...inputs, lean_evidence: undefined },
    });
    expect(strip(built)).toEqual(strip(stored));
  });
});

describe("rulings in state.json → the repeat check and the reviewer's ruled-out block", () => {
  it.each(["tbs_extreme_effects", "tbs_neural_causal_pi", "tbs_prte_optimal_transport"])("%s", async (slug) => {
    const { runDir } = await unpackRun(slug);
    const verify = (await readJson<StateJson>(path.join(runDir, "state.json"))).verify!;
    const core = await readTypedCore(path.join(runDir, VERIFY_FILES.coreJson));
    const rulings = verify.rejected_rewinds ?? [];
    expect(rulings.length).toBeGreaterThan(0);
    const flat = (t: string): string => t.replace(/\s+/g, " ").trim();
    for (const r of rulings) {
      // The axis on file is the one the escalation's text gives, when it gives one (the receipt and
      // its replay agree); an orchestrator's ruling on a finding with no rewind axis records its own.
      const derived = r.route === "fix-source" || r.route === "unclear" ? proofReviewRewindAxis({ route: r.route, reason: r.detail }) : null;
      if (derived) expect(derived).toBe(r.axis);
      // The same finding raised again is a repeat of a ruling on its node and axis.
      const again = rejectedMatch(verify, r.node, r.axis, r.detail);
      expect(again && { node: again.node, axis: again.axis }).toEqual({ node: r.node, axis: r.axis });
      // A ruling on a node the core no longer has (a pin a later pass dropped, a filler-scoped
      // hypothesis) is shown to no reviewer of the core's nodes.
      if (!coreNodeIds(core).has(r.node)) {
        expect(renderRuledOut([r], [...coreNodeIds(core)])).toBe("");
        continue;
      }
      // Every reviewer target that is the node or uses it is shown the ruling (the proof reviewer's
      // node list: the target and its `depends_on`).
      const targets = [[r.node], ...core.statements.filter((s) => s.depends_on.includes(r.node)).map((s) => [s.id, ...s.depends_on])];
      for (const nodes of targets) {
        expect(renderRuledOut(rulings, nodes)).toContain(`• ${r.node}: ${flat(r.detail)} — RULING (${r.by}): ${flat(r.reason)}`);
      }
    }
  });
});
