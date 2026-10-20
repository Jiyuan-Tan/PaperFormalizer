/**
 * A runner exception while V1 patch mode validates the fixer's reply is the runner's bug: it is
 * never sent back to the fixer as a violation and never spends a fixer round. The run checkpoints
 * at once with the reply saved; the next entry on the same directive validates that saved reply
 * before any new fixer call. Fake codex; no network.
 */
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { existsSync } from "node:fs";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it, vi } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState } from "../../src/state.js";
import { runStageV1 } from "../../src/verify/stage_v1.js";
import { VERIFY_FILES } from "../../src/verify/types.js";
import { withOwnerExplanations, writeToyPaper } from "./owner_explained.js";

const crash = vi.hoisted(() => ({ on: false }));
vi.mock("../../src/verify/patches.js", async (importOriginal) => {
  const real = await importOriginal<typeof import("../../src/verify/patches.js")>();
  return {
    ...real,
    materializeReply: (...a: Parameters<typeof real.materializeReply>) => {
      if (crash.on) throw new TypeError("Cannot read properties of undefined (reading 'end')");
      return real.materializeReply(...a);
    },
  };
});

const tmp: string[] = [];
afterEach(async () => {
  crash.on = false;
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

const PROOF = "By Assumption 1, $E[U_2 \\mid W] = 0$. Hence the cross term vanishes. The bound follows.";
const core = (): Core =>
  ({
    qid: "pe",
    symbols: [],
    assumptions: [],
    definitions: [],
    statements: [{ id: "lem:global", kind: "lemma", statement: "$\\tilde c \\bar M \\le \\sigma$.", depends_on: [], status: "to-prove", proof_tex: PROOF }],
    target_estimand: "t",
  }) as unknown as Core;

async function fixture() {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "v1-runner-error-"));
  tmp.push(repoRoot);
  const runDir = path.join(repoRoot, "runs", "pe");
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  for (const f of [VERIFY_FILES.coreJson, VERIFY_FILES.coreTranscribed]) await writeFile(path.join(runDir, f), JSON.stringify(core(), null, 2));
  await writeToyPaper(runDir, core());
  const finding = { id: "lem:global", axis: "correctness", detail: "the cross term is dropped", witness: "a projection model" };
  await writeFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), JSON.stringify({ mode: "patch", round: 1, findings: [finding] }));
  const state = createVerifyInitialState("pe", { phase: "init", source: { input: "p.tex", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 0, findings: [], report_path: null });
  state.verify!.paper_errors = { "lem:global": { detail: finding.detail, witness: finding.witness } };
  const reply = { key_results: ["lem:global"], key_contribution: "c", patches: [{ node: "lem:global", corrected_statement: "$[\\tilde c \\bar M - \\bar c]_+ \\le \\sigma$.", add_assumptions: [], remove_depends_on: [], proof_edits: [], insert_after: [], proof_note: null }], unfixable: [], rejected: [] };
  const calls: CodexRunInput[] = [];
  const codex = (async (input: CodexRunInput) => {
    calls.push(input);
    return { stdout: JSON.stringify(withOwnerExplanations(reply)), stderr: "" };
  }) as typeof runCodex;
  return { repoRoot, runDir, state, calls, codex };
}

describe("V1 patch mode: a runner exception is not the fixer's violation", () => {
  it("checkpoints at once with the reply saved and the stack logged, spends no further round, keeps the directive; the next entry validates the saved reply without a fixer call", async () => {
    const { repoRoot, runDir, state, calls, codex } = await fixture();
    const lines: string[] = [];
    crash.on = true;
    const res = await runStageV1({ repoRoot, qid: "pe", runDir, state, deps: { runCodex: codex }, dryRun: false, log: (m: string) => lines.push(m) });
    expect(res.status).toBe("checkpoint");
    expect(res.message).toContain("runner error");
    expect(res.message).not.toContain("did not parse");
    expect(calls).toHaveLength(1); // no second fixer round was spent on the runner's bug
    const log = lines.join("\n");
    expect(log).toContain("runner error");
    expect(log).toContain("TypeError: Cannot read properties of undefined (reading 'end')");
    expect(log).toMatch(/\n\s+at /); // the stack
    expect(log).not.toContain("violation");
    expect(existsSync(path.join(runDir, VERIFY_FILES.v1ReviseDirective))).toBe(true);
    const pending = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.v1PendingReply), "utf8")) as { stdout: string };
    expect(JSON.parse(pending.stdout).patches[0].node).toBe("lem:global");

    crash.on = false;
    const lines2: string[] = [];
    const res2 = await runStageV1({ repoRoot, qid: "pe", runDir, state, deps: { runCodex: codex }, dryRun: false, log: (m: string) => lines2.push(m) });
    if (res2.status !== "completed") console.log(res2.message, lines2.join("\n"));
    expect(res2.status).toBe("completed");
    expect(calls).toHaveLength(1); // the saved reply was replayed, no new fixer call
    expect(lines2.join("\n")).toContain("validating the saved reply");
    expect(existsSync(path.join(runDir, VERIFY_FILES.v1PendingReply))).toBe(false);
    expect(existsSync(path.join(runDir, VERIFY_FILES.patches))).toBe(true);
  });

  it("a saved reply with violations: round 1 revises it — the prompt shows it, and a reply of the named entries alone is merged with it", async () => {
    const { repoRoot, runDir, state, calls } = await fixture();
    const full = withOwnerExplanations({ key_results: ["lem:global"], key_contribution: "c", patches: [{ node: "lem:global", corrected_statement: "$[\\tilde c \\bar M - \\bar c]_+ \\le \\sigma$.", add_assumptions: [], remove_depends_on: [], proof_edits: [], insert_after: [], proof_note: null }], unfixable: [], rejected: [] }) as { patches: Array<Record<string, unknown>> };
    const { owner_explanation: _oe, ...bare } = full.patches[0]!;
    // The saved reply lacks the note; the fixer answers with that patch alone.
    const saved = { ...full, patches: [bare] };
    const partial = { patches: [full.patches[0]] };
    const codex = (async (input: CodexRunInput) => {
      calls.push(input);
      return { stdout: JSON.stringify(partial), stderr: "" };
    }) as typeof runCodex;
    // A crashing first entry saves the violating reply as the pending one.
    crash.on = true;
    await runStageV1({ repoRoot, qid: "pe", runDir, state, deps: { runCodex: (async () => ({ stdout: JSON.stringify(saved), stderr: "" })) as typeof runCodex }, dryRun: false, log: () => {} });
    crash.on = false;
    const lines: string[] = [];
    const res = await runStageV1({ repoRoot, qid: "pe", runDir, state, deps: { runCodex: codex }, dryRun: false, log: (m: string) => lines.push(m) });
    if (res.status !== "completed") console.log(res.message, lines.join("\n"));
    expect(res.status).toBe("completed");
    expect(calls).toHaveLength(1);
    expect(calls[0]!.prompt).toContain("=== YOUR PREVIOUS REPLY");
  });

  it("a runner error in a round that revises a reply saves the reply merged with the one it revised: the replay keeps every entry", async () => {
    const { repoRoot, runDir, state } = await fixture();
    const full = withOwnerExplanations({ key_results: ["lem:global"], key_contribution: "c", patches: [{ node: "lem:global", corrected_statement: "$[\\tilde c \\bar M - \\bar c]_+ \\le \\sigma$.", add_assumptions: [], remove_depends_on: [], proof_edits: [], insert_after: [], proof_note: null }], unfixable: [], rejected: [] }) as { patches: Array<Record<string, unknown>> };
    const { owner_explanation: _oe, ...bare } = full.patches[0]!;
    let n = 0;
    // round 1: a reply lacking the note (a violation); round 2: the named entry alone — and the runner crashes on it
    const codex = (async () => {
      n++;
      if (n === 2) crash.on = true;
      return { stdout: JSON.stringify(n === 1 ? { ...full, patches: [bare] } : { patches: [full.patches[0]] }), stderr: "" };
    }) as typeof runCodex;
    const res = await runStageV1({ repoRoot, qid: "pe", runDir, state, deps: { runCodex: codex }, dryRun: false, log: () => {} });
    expect(res.message).toContain("runner error");
    expect(n).toBe(2);
    const saved = JSON.parse(JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.v1PendingReply), "utf8")).stdout) as { key_results?: string[]; patches: Array<Record<string, unknown>> };
    expect(saved.key_results).toEqual(["lem:global"]);
    expect(saved.patches[0]!.owner_explanation).toBeTruthy();
  });
});
