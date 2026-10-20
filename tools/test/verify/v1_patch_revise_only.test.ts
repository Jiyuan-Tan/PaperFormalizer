/**
 * V1 patch mode, round 2: the prompt shows the entries of the fixer's own round-1 reply the violations
 * name (not the on-disk patches.json), the fixer returns those, the runner keeps the rest; a reply that
 * changes an entry no violation names is a drift violation. Fake codex; no network.
 */
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState } from "../../src/state.js";
import { replyDriftViolations, runStageV1 } from "../../src/verify/stage_v1.js";
import { VERIFY_FILES } from "../../src/verify/types.js";
import { cannedExplanation } from "./owner_explained.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

const RULE = "=== YOUR PREVIOUS REPLY (the entries the violations below name, with key_results and key_contribution: revise them and return them; the runner keeps every other entry of that reply as it was) ===";
const PRIOR_MARK = "prior on-disk proof note";

const core = (): Core =>
  ({
    qid: "pe",
    symbols: [],
    assumptions: [],
    definitions: [],
    statements: [
      { id: "lem:a", kind: "lemma", statement: "$a \\le 1$.", depends_on: [], status: "to-prove" },
      { id: "lem:b", kind: "lemma", statement: "$b \\le 1$.", depends_on: [], status: "to-prove" },
    ],
    target_estimand: "t",
  }) as unknown as Core;

const patch = (node: string, statement: string, explained = true) => ({
  node,
  corrected_statement: statement,
  add_assumptions: [],
  remove_depends_on: [],
  proof_edits: [],
  insert_after: [],
  // No node id in the text: a proof note of a result the paper prints no proof of reaches the author.
  proof_note: `The bound on ${node.replace(":", " ")} follows.`,
  owner_explanation: explained ? cannedExplanation(node) : { ...cannedExplanation(node), why: { objects: [], consequence: "  " } },
});
const file = (a: object, b: object) => ({ key_results: ["lem:a"], key_contribution: "c", patches: [a, b], unfixable: [], rejected: [] });

async function fixture(replies: object[]) {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "v1-revise-only-"));
  tmp.push(repoRoot);
  const runDir = path.join(repoRoot, "runs", "pe");
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  for (const f of [VERIFY_FILES.coreJson, VERIFY_FILES.coreTranscribed]) await writeFile(path.join(runDir, f), JSON.stringify(core(), null, 2));
  await writeFile(path.join(runDir, VERIFY_FILES.flatTex), "\\begin{lemma}x\\end{lemma}\n");
  // An on-disk patch file from an earlier V1 run: shown in round 1 only.
  const { rejected: _r, ...onDisk } = file({ ...patch("lem:a", "$a \\le 2$."), proof_note: PRIOR_MARK }, patch("lem:b", "$b \\le 2$."));
  await writeFile(path.join(runDir, VERIFY_FILES.patches), JSON.stringify(onDisk));
  const findings = ["lem:a", "lem:b"].map((id) => ({ id, axis: "correctness", detail: `the bound on ${id} is wrong`, witness: "w" }));
  await writeFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), JSON.stringify({ mode: "patch", round: 2, findings }));
  const state = createVerifyInitialState("pe", { phase: "init", source: { input: "p.tex", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 1, findings: [], report_path: null });
  state.verify!.paper_errors = Object.fromEntries(findings.map((f) => [f.id, { detail: f.detail, witness: f.witness }]));
  const calls: CodexRunInput[] = [];
  const codex = (async (input: CodexRunInput) => {
    calls.push(input);
    return { stdout: JSON.stringify(replies[calls.length - 1]), stderr: "" };
  }) as typeof runCodex;
  return { repoRoot, runDir, state, calls, codex };
}

const round1 = file(patch("lem:a", "$a \\le 3$.", false), patch("lem:b", "$b \\le 3$."));

describe("V1 patch mode: round 2 revises only what the violations name", () => {
  it("round 1 shows the on-disk file; round 2 shows the round-1 reply and the rule; a compliant reply passes", async () => {
    const round2 = file(patch("lem:a", "$a \\le 3$."), { ...patch("lem:b", "$b \\le 3$."), proof_note: "The  bound on lem b\n follows." }); // whitespace only
    const { repoRoot, runDir, state, calls, codex } = await fixture([round1, round2]);
    const res = await runStageV1({ repoRoot, qid: "pe", runDir, state, deps: { runCodex: codex }, dryRun: false, log: () => {} });
    expect(res.status).toBe("completed");
    expect(calls).toHaveLength(2);
    const [p1, p2] = calls.map((c) => c.prompt);
    expect(p1).toContain("=== PATCHES FILE (your previous patch");
    expect(p1).toContain(PRIOR_MARK);
    expect(p1).not.toContain("=== YOUR PREVIOUS REPLY");
    expect(p2).toContain(RULE);
    // only the entry the violations name (lem:a's explanation), with the key results
    const shown = p2.slice(p2.indexOf(RULE), p2.indexOf("=== VIOLATIONS"));
    expect(shown).toContain('"node": "lem:a"');
    expect(shown).not.toContain('"node": "lem:b"');
    expect(shown).toContain('"key_results"');
    expect(p2).not.toContain("=== PATCHES FILE");
    expect(p2).not.toContain(PRIOR_MARK);
    expect(p2).toMatch(/VIOLATIONS IN YOUR PREVIOUS REPLY[\s\S]*"lem:a"/);
    // One pipeline.jsonl line per fixer round: the call, its prompt bytes, what it was asked.
    const pl = (await readFile(path.join(runDir, "pipeline.jsonl"), "utf8")).trim().split("\n").map((l) => JSON.parse(l) as { stage: string; status: string; message: string });
    expect(pl.map((e) => [e.stage, e.status])).toEqual([["V1", "fixer_round"], ["V1", "fixer_round"]]);
    expect(pl[0]!.message).toMatch(/^fixer round 1\/\d+ \(patch round 2\): 1 call, \d+ prompt bytes, 2 node\(s\) demanded, 0 carried$/);
    expect(pl[1]!.message).toMatch(/\d+ violation\(s\) answered$/);
  });

  it("a round-2 reply returning only the named entry: the runner keeps the other as the round-1 reply had it", async () => {
    const round2 = { key_results: ["lem:a"], key_contribution: "c", patches: [patch("lem:a", "$a \\le 3$.")], unfixable: [], rejected: [] };
    const { repoRoot, runDir, state, calls, codex } = await fixture([round1, round2]);
    const res = await runStageV1({ repoRoot, qid: "pe", runDir, state, deps: { runCodex: codex }, dryRun: false, log: () => {} });
    expect(res.status).toBe("completed");
    expect(calls).toHaveLength(2);
    const { readFile } = await import("node:fs/promises");
    const saved = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.patches), "utf8")) as { patches: Array<{ node: string; proof_note: string }> };
    expect(saved.patches.map((p) => p.node).sort()).toEqual(["lem:a", "lem:b"]);
    expect(saved.patches.find((p) => p.node === "lem:b")!.proof_note).toBe("The bound on lem b follows.");
  });

  it("a round-2 reply that alters an entry no violation names is a drift violation naming it", async () => {
    const round2 = file(patch("lem:a", "$a \\le 3$."), patch("lem:b", "$b \\le 4$."));
    const { repoRoot, runDir, state, calls, codex } = await fixture([round1, round2]);
    const lines: string[] = [];
    const res = await runStageV1({ repoRoot, qid: "pe", runDir, state, deps: { runCodex: codex }, dryRun: false, log: (m) => lines.push(m) });
    expect(calls).toHaveLength(2);
    expect(res.status).toBe("checkpoint");
    expect(res.message).toContain('(drift) patches "lem:b" changed');
    expect(res.message).not.toContain('"lem:a" changed');
    // replyDriftViolations: the named entry may change; changed, dropped and added un-named entries are flagged
    const prev = file(patch("lem:a", "x"), patch("lem:b", "y"));
    const v = ['the `owner_explanation` for "lem:a" is free prose'];
    expect(replyDriftViolations(prev, v, file(patch("lem:a", "z"), patch("lem:b", "y")))).toEqual([]);
    expect(replyDriftViolations(prev, v, { ...prev, patches: [patch("lem:a", "x")] })).toEqual([expect.stringContaining('patches "lem:b" was dropped')]);
    expect(replyDriftViolations(prev, v, { ...prev, patches: [...prev.patches, patch("lem:c", "w")] })).toEqual([expect.stringContaining('patches "lem:c" is new')]);
    expect(replyDriftViolations(prev, v, { ...prev, key_contribution: "d" })).toEqual([expect.stringContaining("key_contribution changed")]);
    // a violation naming no entry, or an unparsed previous reply, opens the whole file
    const other = file(patch("lem:a", "z"), patch("lem:b", "q"));
    expect(replyDriftViolations(prev, [...v, "(gate G1) somewhere: broken"], other)).toEqual([]);
    expect(replyDriftViolations("not json", v, other)).toEqual([]);
  });
});
