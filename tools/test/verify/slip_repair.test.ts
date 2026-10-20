/**
 * The first repair in the order (owner decision 2026-09-24): a slip in what a statement displays is corrected to
 * the form the paper's own proof establishes, with no hypothesis; a patch that adds a hypothesis where
 * such a correction suffices is not minimal. Fixture modelled on CNS `prop:delta2` (read-only there):
 * Δ′ collected t₄ + t₅ + t₆ as {Q̄+(ᾱ′)²}ℛ^q, putting the exponent q on the (ᾱ′)² term whose bound t₅
 * has exponent 1; the fixer restated it with the hypothesis "q = 1" where the bracket
 * Q̄ℛ^q + (ᾱ′)²ℛ is the smaller repair.
 */
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState } from "../../src/state.js";
import { PatchFileSchema, type PatchFile } from "../../src/verify/patches.js";
import { runStageV1_5 } from "../../src/verify/stage_v1_5.js";
import { VERIFY_FILES, type V15NodeVerdict } from "../../src/verify/types.js";
import { withOwnerExplanations, writeToyPaper } from "./owner_explained.js";
import { isRefereeCall, isRefereeGlobal, isRefereeShard, shardIds, shardedRefereeReply, type WholeCoreReply } from "./referee_fake.js";
import { symbolReply } from "./symbol_fake.js";

const tmpDirs: string[] = [];
afterEach(async () => {
  for (const d of tmpDirs.splice(0)) await rm(d, { recursive: true, force: true });
});

const PRINTED = "With probability $1-\\epsilon'$, $\\Delta' = 4(\\hat\\theta-\\theta_0)^2 + \\frac{24L}{\\epsilon'}[\\{\\bar Q+(\\bar\\alpha')^2\\}\\mathcal R(\\hat\\gamma_\\ell)^q + \\bar\\sigma^2\\mathcal R(\\hat\\alpha_\\ell)]$ bounds the second moment.";
const SLIP_WITNESS = "$t_5 \\le (\\bar\\alpha')^2\\mathcal R(\\hat\\gamma_\\ell)$ with exponent 1, so the collected bracket should read $\\bar Q\\mathcal R^q + (\\bar\\alpha')^2\\mathcal R$; for $q < 1$ and $\\mathcal R < 1$, $(\\bar\\alpha')^2\\mathcal R^q > (\\bar\\alpha')^2\\mathcal R$ is not what $t_5$ gives, but the printed $\\Delta'$ then is still an upper bound only when $\\mathcal R \\le 1$ -- the proof's own form is the bracket with exponent 1 on the $(\\bar\\alpha')^2$ term.";

function core(): Core {
  return {
    qid: "slip",
    symbols: [{ name: "q", type: "exponent" }],
    assumptions: [{ id: "ass:ms", kind: "regularity", condition: "$E[m(W,\\gamma)^2] \\leq \\bar Q \\|\\gamma\\|^{2q}$", novel: { flag: true, justification: "A1" } }],
    definitions: [],
    statements: [
      { id: "prop:delta2", kind: "proposition", statement: PRINTED, depends_on: ["ass:ms"], proof_tex: "Collect $t_4 + t_5 + t_6$.", status: "to-prove" },
      { id: "thm:var", kind: "theorem", statement: "the variance estimator is consistent", depends_on: ["prop:delta2"], status: "to-prove" },
    ],
    target_estimand: "t",
    bibliography: [],
  } as unknown as Core;
}

function file(over: Partial<PatchFile> = {}): PatchFile {
  return PatchFileSchema.parse({ key_results: ["thm:var"], key_contribution: "consistency of the variance estimator", patches: [], unfixable: [], ...over });
}

/** The hypothesis-based repair: the statement restated with "q = 1" (a repair adds a hypothesis by restating). */
const Q_ONE_PATCH = {
  node: "prop:delta2",
  corrected_statement: `Suppose $q = 1$. ${PRINTED}`,
  proof_note: "with q = 1 the two exponents agree.",
};

async function setup() {
  const root = await mkdtemp(path.join(os.tmpdir(), "verify-slip-"));
  tmpDirs.push(root);
  const runDir = path.join(root, "runs", "slip");
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  for (const f of [VERIFY_FILES.coreJson, VERIFY_FILES.coreTranscribed]) await writeFile(path.join(runDir, f), JSON.stringify(core(), null, 2));
  await writeFile(path.join(runDir, VERIFY_FILES.flatTex), `\\begin{document}\n${PRINTED}\n\\end{document}\n`);
  await writeToyPaper(runDir, core());
  const state = createVerifyInitialState("slip", { phase: "init", source: { input: "p", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
  state.verify!.paper_errors = { "prop:delta2": { detail: "the exponent q sits on the (ᾱ′)² term", witness: SLIP_WITNESS } };
  const calls: CodexRunInput[] = [];
  // replies[k]: the k-th fixer call's reply, or the k-th referee pass's (every shard and its global call).
  let next = 0;
  const codex = (replies: unknown[]) =>
    (async (input: CodexRunInput) => {
      const sym = symbolReply(input);
      if (sym !== null) return { stdout: sym, stderr: "" };
      const reply = replies[next];
      calls.push(input);
      if (reply === undefined) throw new Error(`unexpected call #${calls.length}`);
      if (isRefereeCall(input)) {
        if (isRefereeGlobal(input)) next += 1;
        return { stdout: shardedRefereeReply(input, reply as WholeCoreReply)!, stderr: "" };
      }
      next += 1;
      return { stdout: JSON.stringify(withOwnerExplanations(reply)), stderr: "" };
    }) as typeof runCodex;
  const args = (replies: unknown[]) => ({ repoRoot: root, qid: "slip", runDir, state, deps: { runCodex: codex(replies) }, dryRun: false, log: () => {} });
  return { runDir, state, calls, args };
}

const ok = (id: string): V15NodeVerdict => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "reproduced", witness: null, bookkeeping_assumption: null, reading: null });

describe("the smallest repair: a formula slip is corrected, no hypothesis added", () => {
  it("the referee grades a hypothesis-based repair non-minimal with the slip correction as the weaker repair: a refinement round", async () => {
    const r = await setup();
    r.state.verify!.phase = "v1";
    await writeFile(path.join(r.runDir, VERIFY_FILES.patches), JSON.stringify(file({ patches: [Q_ONE_PATCH] })));
    const reply = {
      verdict: "REVISE",
      summary: "the q = 1 hypothesis is correct but not minimal",
      nodes: [
        ok("ass:ms"),
        { ...ok("prop:delta2"), correctness: "error", minimality: true, detail: "correct but not minimal: a slip correction suffices", witness: "correct the bracket to $\\bar Q\\mathcal R^q + (\\bar\\alpha')^2\\mathcal R$ (the form $t_5$ gives), no hypothesis" },
        ok("thm:var"),
      ],
      patch_review: { key_results_ok: true, detail: "thm:var is the headline" },
      rejection_verdicts: null,
    };
    const res = await runStageV1_5(r.args([reply]));
    expect(res.status).toBe("patch");
    expect(res.round_kind).toBe("refinement");
    // The shard grading the patched node carries the minimality rule.
    const shard = r.calls.find((c) => isRefereeShard(c) && shardIds(c.prompt).includes("prop:delta2"))!;
    expect(shard.prompt).toContain("uses a later step where an earlier one suffices");
    const directive = JSON.parse(await readFile(path.join(r.runDir, VERIFY_FILES.v1ReviseDirective), "utf8"));
    expect(JSON.stringify(directive.findings)).toContain("$\\\\bar Q\\\\mathcal R^q");
  });
});
