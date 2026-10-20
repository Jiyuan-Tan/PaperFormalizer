import { fileURLToPath } from "node:url";
/**
 * A fresh re-entry (`--from-stage V1|V1.5`, `--fresh-review`) voids the pending owner receipts: a
 * weakened-repair receipt (and its pending suggestions in `patches.json`), a proposed F-stage
 * rewind, a patch cap. They are set aside, never presented again; owner decisions stay binding.
 * No model call: the V1.5 pass is the real dry run (sharded through the toolkit config) or a stub.
 */
import { existsSync } from "node:fs";
import { mkdir, mkdtemp, readFile, readdir, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it, vi } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { recordProofReviewOutcome } from "../../src/formalization/dispatcher.js";
import { verifyRunDir } from "../../src/paths.js";
import type { runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState, loadState, saveState } from "../../src/state.js";
import type { StateJson } from "../../src/types.js";
import { PatchFileSchema, type PatchFile } from "../../src/verify/patches.js";
import { runVerifyPipeline, type RunFormalization } from "../../src/verify/pipeline.js";
import { VERIFY_FILES, type VerifyPhase, type VerifyStage } from "../../src/verify/types.js";
import { recordWeakeningReceipt } from "../../src/verify/weakening.js";
import { tk } from "../toolkit/helpers.js";

const QID = "reentry_paper";
const TOOLS = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..", "..");
const FLAT_FIXTURE = path.join(TOOLS, "test", "verify", "fixtures", "v1_5", "flat.tex");

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

/** The V1.5 fixture core (`fixtures/v1_5/flat.tex`), as in `referee_shards.test.ts`. */
function core(): Core {
  return {
    qid: QID,
    symbols: [{ name: "Y", type: "random variable", role: "outcome" }],
    assumptions: [
      { id: "ass:unconfoundedness", kind: "causal-structural", condition: "$Y(d) \\perp D \\mid X$ for $d \\in \\{0,1\\}$.", novel: { flag: true, justification: "Assumption 1" }, tex_locator: { file: "main.tex", from: 10, to: 12, env: "assumption", label: "ass:unconf" } },
      { id: "ass:overlap", kind: "support", condition: "$0 < e(X) < 1$ almost surely.", novel: { flag: true, justification: "Assumption 2" }, tex_locator: { file: "main.tex", from: 14, to: 16, env: "assumption", label: "ass:overlap" } },
    ],
    definitions: [{ id: "def:propensity", name: "propensity score", construction: "Let $Y$ be the outcome, $D \\in \\{0,1\\}$ the treatment and $X$ the covariates.", tex_locator: { file: "main.tex", from: 8, to: 8, env: "prose", label: null } }],
    statements: [
      { id: "lem:ipw-identity", kind: "lemma", statement: "Under Assumption \\ref{ass:overlap}, $E[DY/e(X)] = E[Y(1)]$.", depends_on: ["ass:overlap", "def:propensity"], proof_tex: "Condition on $X$ and apply the tower property.", status: "to-prove", tex_locator: { file: "main.tex", from: 18, to: 20, env: "lem", label: "lem:ipw" } },
      { id: "thm:ate-identification", kind: "theorem", statement: "Under Assumptions \\ref{ass:unconf} and \\ref{ass:overlap}, $\\tau = E[DY/e(X) - (1-D)Y/(1-e(X))]$.", depends_on: ["ass:unconfoundedness", "ass:overlap", "def:propensity", "lem:ipw-identity"], proof_tex: "Apply Lemma \\ref{lem:ipw} to each arm and subtract.", status: "to-prove", tex_locator: { file: "main.tex", from: 25, to: 27, env: "thm", label: "thm:ate" } },
      { id: "lem:delta-method", kind: "lemma", statement: "(van der Vaart, Theorem 3.1.) If $\\sqrt{n}(T_n - \\theta) \\rightsquigarrow T$ and $\\phi$ is differentiable at $\\theta$, then $\\sqrt{n}(\\phi(T_n) - \\phi(\\theta)) \\rightsquigarrow \\phi'_\\theta(T)$.", depends_on: [], status: "cited", source: { cite: "vandervaart1998", locator: "Theorem 3.1", verbatim_statement: "Delta method." }, tex_locator: { file: "main.tex", from: 32, to: 34, env: "lem", label: "lem:delta" } },
    ],
    target_estimand: "$\\tau = E[Y(1) - Y(0)]$",
    bibliography: [{ key: "vandervaart1998", citation: "van der Vaart (1998). Asymptotic Statistics." }],
  } as unknown as Core;
}

const SUGGESTION = (text: string) => ({
  corrected_statement: text,
  add_assumptions: [],
  remove_depends_on: [],
  proof_note: "the bound is taken on the trimmed sample; every other step is unchanged.",
  given_up: "the untrimmed identity",
});

/** The patch file the single-referee pass left: a PENDING suggestion on lem:ipw-identity, a
 * suggestion the owner DECLINED on lem:delta-method, and an owner reading pinned on the theorem. */
function patchFile(): PatchFile {
  return PatchFileSchema.parse({
    key_results: ["thm:ate-identification"],
    key_contribution: "identification of the ATE by inverse propensity weighting",
    patches: [],
    unfixable: [
      { node: "lem:ipw-identity", reason: "any repair weakens the contribution: overlap is one-sided", suggested_repair: SUGGESTION("On the trimmed sample, $E[DY/e(X)] = E[Y(1)]$."), suggested_by: "fixer", owner_explanation: "x" },
      { node: "lem:delta-method", reason: "any repair weakens the contribution: d", suggested_repair: SUGGESTION("A weaker delta method."), suggested_by: "fixer", declined: "not the paper's point" },
    ],
    owner_readings: [{ id: "ass:pin-owner-1", node: "thm:ate-identification", reading: "τ is the population average treatment effect", withdraws: [{ axis: "correctness", stage: "V1.5", route: "weakening", detail: "d", at: "t" }] }],
  });
}

const noCodex = (async () => {
  throw new Error("no model call in these tests");
}) as unknown as typeof runCodex;

async function seed(opts: { phase: VerifyPhase; stage: StateJson["stage_completed"]; mutate?: (s: StateJson, runDir: string) => Promise<void> | void }) {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "verify-reentry-"));
  tmpDirs.push(repoRoot);
  const runDir = verifyRunDir(repoRoot, QID);
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  await mkdir(path.join(runDir, VERIFY_FILES.sourceDir), { recursive: true });
  for (const f of [VERIFY_FILES.coreJson, VERIFY_FILES.coreTranscribed]) await writeFile(path.join(runDir, f), JSON.stringify(core(), null, 2), "utf8");
  await writeFile(path.join(runDir, VERIFY_FILES.flatTex), await readFile(FLAT_FIXTURE, "utf8"), "utf8");
  const state = createVerifyInitialState(QID, {
    phase: opts.phase,
    source: { input: "/papers/reentry_paper.tex", main_file: "main.tex", sha256: "h" },
    targets: null,
    core_sha256: null,
    v1_rounds: 1,
    v1_5_rounds: 0,
    findings: [],
    report_path: null,
    dry_run: true,
  });
  state.stage_completed = opts.stage;
  await opts.mutate?.(state, runDir);
  await saveState(repoRoot, QID, state);
  return { repoRoot, runDir };
}

/** Seeds the weakening halt of the live CNS run in miniature: receipt pending, suggestion in the file. */
async function seedWeakening(s: StateJson, runDir: string): Promise<void> {
  const f = patchFile();
  await writeFile(path.join(runDir, VERIFY_FILES.patches), JSON.stringify(f, null, 2), "utf8");
  s.verify!.paper_errors = {
    "lem:ipw-identity": { detail: "1/e(X) is unbounded", witness: "e(X) → 0" },
    "lem:delta-method": { detail: "d", witness: null, weakens_contribution: true, owner_decision: "declined", decision_reason: "not the paper's point" },
    "thm:ate-identification": { detail: "d", witness: null, owner_decision: "finding rejected", decision_reason: "τ is the population average treatment effect", owner_overruled: true },
  };
  s.verify!.rejected_rewinds = [{ node: "thm:ate-identification", axis: "correctness", stage: "V1.5", route: "weakening", detail: "d", reason: "τ is the population average treatment effect", by: "owner", pin: "ass:pin-owner-1", at: "t" }];
  expect(recordWeakeningReceipt(s, core(), f)?.items.map((i) => i.node)).toEqual(["lem:ipw-identity"]);
  s.verify!.confirmed = { "ass:overlap": "stale-basis" };
}

function args(repoRoot: string, extra: Record<string, unknown> = {}) {
  const formal: Array<string | undefined> = [];
  const runFormalization: RunFormalization = async ({ toolkit, qid, startStage }) => {
    formal.push(startStage);
    const s = await loadState(toolkit.toolkitRoot, qid);
    s.stage_completed = "5";
    await saveState(toolkit.toolkitRoot, qid, s);
    return s;
  };
  return {
    formal,
    args: {
      toolkit: tk(repoRoot),
      qid: QID,
      input: "/papers/reentry_paper.tex",
      mainHint: null,
      targets: null,
      resume: false,
      fromStage: null as string | null,
      auto: true,
      dryRun: true,
      deps: {
        runCodex: noCodex,
        annotate: async ({ runDir }: { runDir: string }) => ({ path: path.join(runDir, "annotated", "main.pdf"), line: "annotated/main.pdf", result: null, error: null }),
      },
      runFormalization,
      runPromotion: async () => ({ status: "empty" as const, batch_path: null, checklist_path: null, promoted: [] }),
      ...extra,
    },
  };
}

async function logged(fn: () => Promise<unknown>): Promise<string[]> {
  const spy = vi.spyOn(console, "log").mockImplementation(() => {});
  try {
    await fn();
    return spy.mock.calls.map((c) => String(c[0]));
  } finally {
    spy.mockRestore();
  }
}

describe("a fresh re-entry voids pending owner receipts", () => {
  it("a pending weakened repair: voided (receipt + suggestion), the (sharded) referee runs, owner decisions survive", async () => {
    const { repoRoot, runDir } = await seed({ phase: "v1", stage: "V1.5", mutate: seedWeakening });
    const base = args(repoRoot);
    const toolkit = base.args.toolkit;
    const lines = await logged(() => runVerifyPipeline({ ...base.args, toolkit, resume: true, fromStage: "V1.5", freshReview: true, stopAfter: "V1.5" } as never));
    const text = lines.join("\n");
    expect(text).toContain("voided pending weakening_repair receipt (1 item: lem:ipw-identity) — the review is redone");
    expect(text).toContain("1 ledger entry dropped");
    expect(text).not.toContain("WEAKENED REPAIR:");
    // The referee ran (dry: synthetic shard grades), sharded.
    expect(text).toMatch(/V1\.5: sharded referee: levels: L0 \d+ .*; \d+ shard\(s\) \(/);
    const metrics = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.v15RefereeMetrics), "utf8"));
    expect(metrics.shards.length).toBeGreaterThan(0);
    const after = (await loadState(repoRoot, QID)).verify!;
    expect(after.weakening_repair).toBeNull();
    expect(after.phase).toBe("v1_5");
    expect(after.voided_receipts).toEqual([expect.objectContaining({ kind: "weakening_repair", nodes: ["lem:ipw-identity"], items: 1, ledger_dropped: ["lem:ipw-identity"], reason: "--from-stage V1.5 --fresh-review" })]);
    // The voided node goes back to the referee as printed; the owner's decisions stay binding.
    expect(Object.keys(after.paper_errors ?? {}).sort()).toEqual(["lem:delta-method", "thm:ate-identification"]);
    expect(after.paper_errors!["thm:ate-identification"]!.owner_decision).toBe("finding rejected");
    expect(after.paper_errors!["lem:delta-method"]!.owner_decision).toBe("declined");
    expect(after.rejected_rewinds).toHaveLength(1);
    const saved = PatchFileSchema.parse(JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.patches), "utf8")));
    expect(saved.unfixable.map((u) => [u.node, u.declined])).toEqual([["lem:delta-method", "not the paper's point"]]);
    // A reading recorded before `withdraws` existed takes its withdrawal from the ruled-out entry once.
    expect(saved.owner_readings).toEqual(patchFile().owner_readings);
    const accepted = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.coreJson), "utf8")) as Core;
    expect(accepted.assumptions.map((a) => a.id)).toContain("ass:pin-owner-1");
    // Set aside as history: the receipt, the suggestion, the dropped ledger entry, the patch file as it stood.
    const [stamp] = await readdir(path.join(runDir, "proposals", "voided"));
    const dir = path.join(runDir, "proposals", "voided", stamp!);
    const archived = JSON.parse(await readFile(path.join(dir, "weakening_repair.json"), "utf8"));
    expect(archived.receipt.items.map((i: { node: string }) => i.node)).toEqual(["lem:ipw-identity"]);
    expect(archived.suggestions.map((u: { node: string }) => u.node)).toEqual(["lem:ipw-identity"]);
    expect(Object.keys(archived.ledger_entries)).toEqual(["lem:ipw-identity"]);
    expect(PatchFileSchema.parse(JSON.parse(await readFile(path.join(dir, "patches.json"), "utf8"))).unfixable).toHaveLength(2);
    // A second re-entry has nothing pending: nothing is voided again.
    const again = await logged(() => runVerifyPipeline({ ...base.args, toolkit, resume: true, fromStage: "V1.5", stopAfter: "V1.5" } as never));
    expect(again.join("\n")).not.toContain("voided pending");
    expect((await loadState(repoRoot, QID)).verify!.voided_receipts).toHaveLength(1);
  });

  it("the re-review halts again only on suggestions it derives itself", async () => {
    const { repoRoot, runDir } = await seed({ phase: "v1", stage: "V1.5", mutate: seedWeakening });
    const v1_5: VerifyStage = async ({ state }) => {
      const onDisk = PatchFileSchema.parse(JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.patches), "utf8")));
      expect(onDisk.unfixable.map((u) => u.node)).toEqual(["lem:delta-method"]); // the old suggestion is gone
      const next = { ...onDisk, unfixable: [...onDisk.unfixable, { node: "thm:ate-identification", reason: "any repair weakens the contribution: new", suggested_repair: SUGGESTION("A weaker ATE formula."), suggested_by: "referee" as const }] };
      await writeFile(path.join(runDir, VERIFY_FILES.patches), JSON.stringify(next), "utf8");
      state.verify!.paper_errors = { ...state.verify!.paper_errors, "thm:ate-identification": { detail: "new", witness: "w" } };
      recordWeakeningReceipt(state, core(), next);
      return { status: "checkpoint", message: "a new suggestion" };
    };
    const base = args(repoRoot, { stages: { v1_5 } });
    const lines = await logged(() => runVerifyPipeline({ ...base.args, resume: true, fromStage: "V1.5", freshReview: true } as never));
    const halt = lines.find((l) => l.includes("WEAKENED REPAIR:")) ?? "";
    expect(halt).toContain("thm:ate-identification");
    expect(halt).not.toContain("lem:ipw-identity");
    expect((await loadState(repoRoot, QID)).verify!.weakening_repair?.items.map((i) => i.node)).toEqual(["thm:ate-identification"]);
  });

  it("a presented F-stage rewind: voided, its halting flag lifted, never presented again; F restarts at F1", async () => {
    const reason = "[statement-wrong] thm:ate-identification needs bounded outcomes, which the paper does not grant.";
    const { repoRoot } = await seed({
      phase: "formalization",
      stage: "2",
      mutate: (s) => {
        recordProofReviewOutcome(s, { status: "escalate", phase: "2.5", route: "fix-source", reason, kind: "statement-wrong", obj_id: "thm:ate-identification" } as never);
        s.verify!.cross_stage_rewind = { ...s.verify!.cross_stage_rewind!, presented: true };
        s.verify!.rejected_rewinds = [{ node: "lem:ipw-identity", axis: "correctness", stage: "F1.5", route: "stage_0", detail: "d", reason: "owner reading", by: "owner", pin: "ass:pin-owner-1", at: "t" }];
      },
    });
    const v1_5: VerifyStage = async ({ state }) => {
      state.stage_completed = "V1.5";
      return { status: "completed", message: "ok" };
    };
    const base = args(repoRoot, { stages: { v1_5, v6: (async () => ({ status: "completed", message: "report" })) as VerifyStage } });
    const lines = await logged(() => runVerifyPipeline({ ...base.args, resume: true, fromStage: "V1.5" } as never));
    const text = lines.join("\n");
    expect(text).toContain("voided pending cross_stage_rewind receipt (1 item: thm:ate-identification) — the review is redone");
    expect(text).not.toMatch(/PROPOSED|approves the/);
    expect(base.formal).toEqual(["1"]);
    const after = await loadState(repoRoot, QID);
    expect(after.verify!.cross_stage_rewind).toBeUndefined();
    expect(after.flags.proof_review_escalation_pending).toBeNull();
    expect(after.verify!.rejected_rewinds).toHaveLength(1); // the owner's ruling stays binding
    expect(after.verify!.voided_receipts?.map((v) => v.kind)).toEqual(["cross_stage_rewind"]);
    expect(after.verify!.phase).toBe("done");
  });

  it("a patch cap: voided with the directive it held back; V1 re-enters without it", async () => {
    const { repoRoot, runDir } = await seed({
      phase: "v1",
      stage: "V1",
      mutate: async (s, runDir) => {
        s.verify!.patch_rounds = 3;
        s.verify!.cap_reached = { counter: "patch_rounds", rounds: 3, cap: 3, origin: "V1.5", findings: [{ id: "lem:ipw-identity", axis: "correctness", detail: "1/e(X) is unbounded", witness: "w" }], proposed: [], at: "t" };
        await writeFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), JSON.stringify({ mode: "patch", round: 4, findings: [{ id: "lem:ipw-identity", axis: "correctness", detail: "d", witness: "w" }] }), "utf8");
      },
    });
    const seen: boolean[] = [];
    const v1: VerifyStage = async () => {
      seen.push(existsSync(path.join(runDir, VERIFY_FILES.v1ReviseDirective)));
      return { status: "completed", message: "revised" };
    };
    const v1_5: VerifyStage = async ({ state }) => {
      state.stage_completed = "V1.5";
      return { status: "completed", message: "ok" };
    };
    const base = args(repoRoot, { stages: { v1, v1_5 } });
    const lines = await logged(() => runVerifyPipeline({ ...base.args, resume: true, fromStage: "V1", stopAfter: "V1.5" } as never));
    const text = lines.join("\n");
    expect(text).toContain("voided pending cap_reached receipt (1 item: lem:ipw-identity) — the review is redone");
    expect(text).not.toContain("PATCH CAP:");
    expect(seen).toEqual([false]);
    const after = (await loadState(repoRoot, QID)).verify!;
    expect(after.cap_reached).toBeNull();
    expect(after.patch_rounds).toBe(0);
    const [stamp] = await readdir(path.join(runDir, "proposals", "voided"));
    const dir = path.join(runDir, "proposals", "voided", stamp!);
    expect(existsSync(path.join(dir, "cap_reached.json"))).toBe(true);
    expect(JSON.parse(await readFile(path.join(dir, "v1_revise_directive.json"), "utf8")).round).toBe(4);
  });
});
