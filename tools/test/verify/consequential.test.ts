/**
 * Consequential edits (user decision 2026-09-25, `consequential.ts`): a patch on a node with no
 * finding follows another repair — `consequence_of` + a one-sentence `reason`, never a defect note —
 * and a patch on a finding node never declares one (the runner's check both ways, and a fake-codex
 * patch round); the annotated paper renders such a patch's steps red/blue with one line naming the
 * repair it follows, no Claim / What is wrong / Why.
 */
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import type { CodexRunInput, runCodex } from "../../src/shared/codex.js";
import { createVerifyInitialState } from "../../src/state.js";
import { applyEdits, planAnnotations, type AnnotationInput } from "../../src/verify/annotated_paper.js";
import { consequenceViolations, findingNodes, setAsideSuggestionConsequences } from "../../src/verify/consequential.js";
import { PatchFileSchema, type PatchFile } from "../../src/verify/patches.js";
import { runStageV1 } from "../../src/verify/stage_v1.js";
import { ruleOnReceipt } from "../../src/verify/weakening.js";
import { VERIFY_FILES } from "../../src/verify/types.js";
import { cannedExplanation, writeToyPaper } from "./owner_explained.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

const PROOF_B = "First, $\\omega_h \\geq \\tilde f/2$ by the density bound.\nThen $b \\le 2/\\tilde f$ follows.";
/** The last step of lem:b's printed proof (its unit `lem:b/proof/1/2`), replaced. */
const OP_B = { op: "replace", unit: "lem:b/proof/1/2", to: null, tex: "By the normalizer bound $c_\\omega>0$, $b \\le 1/c_\\omega$." };

const core = (): Core =>
  ({
    qid: "cq",
    symbols: [],
    assumptions: [],
    definitions: [],
    statements: [
      { id: "lem:a", kind: "lemma", statement: "$a \\le 1$.", depends_on: [], status: "to-prove", proof_tex: "Since $a \\le 1/2$, the claim holds." },
      { id: "lem:b", kind: "lemma", statement: "$b \\lesssim h^{-1}$.", depends_on: [], status: "to-prove", proof_tex: PROOF_B },
    ],
    target_estimand: "t",
  }) as unknown as Core;

/** lem:a's repair: its statement restated with the normalizer hypothesis (a replacement of its one unit). */
const OP_A = { op: "replace", unit: "lem:a/1/1", to: null, tex: "Suppose $\\inf_{h}|\\omega_h|>0$. Then $a \\le 1$." };
const owner = { node: "lem:a", corrected_statement: null, ops: [OP_A], proof_note: "Divide by the normalizer bound.", owner_explanation: cannedExplanation("lem:a"), consequence_of: null, reason: null };
const conseq = (over: Record<string, unknown> = {}) => ({
  node: "lem:b",
  corrected_statement: null,
  ops: [OP_B],
  proof_note: null,
  owner_explanation: null,
  consequence_of: ["lem:a"],
  reason: "The last step now divides by the normalizer lower bound the repair of Lemma~\\ref{lem:a} adds.",
  ...over,
});
// As the runner parses a reply: after `materializeReply` has filled each `proof_note`.
const parse = (patches: object[]): PatchFile =>
  PatchFileSchema.parse({ key_results: ["lem:a"], key_contribution: "c", patches: patches.map((p) => ({ ...p, proof_note: (p as { proof_note?: string | null }).proof_note ?? "derived" })), unfixable: [] });
const check = (f: PatchFile, finding: string[]): string[] =>
  consequenceViolations(f, (n) => finding.includes(n), { statements: new Set(["lem:a", "lem:b"]), printsProof: () => true });

describe("the fixer contract: consequence_of both ways", () => {
  it.each([
    ["a patch on a node with no finding declaring consequence_of passes", conseq(), ["lem:a"], []],
    ["a patch on a node with no finding and no consequence_of is refused", conseq({ consequence_of: null, reason: null }), ["lem:a"], ['the patch for "lem:b": this node has no finding — give consequence_of and a one-sentence reason, not a defect note']],
    ["consequence_of on a node with a finding of its own is refused", conseq(), ["lem:a", "lem:b"], ['the patch for "lem:b" declares `consequence_of`, but "lem:b" has a finding of its own']],
  ] as Array<[string, object, string[], string[]]>)("%s", (_title, b, finding, violations) => {
    expect(check(parse([owner, b]), finding)).toEqual(violations.map((v) => expect.stringContaining(v)));
  });

  it("a patch following only a suggested repair the owner has not ruled on is set aside, not refused; one following an applied repair too stays", () => {
    const afterSuggestion = conseq({ node: "def:v", ops: [{ ...OP_B, unit: "def:v/1/1" }], consequence_of: ["thm:main"], reason: "The estimator now carries the scaling the suggested statement needs." });
    const both = conseq({ node: "lem:c", consequence_of: ["lem:a", "thm:main"] });
    const file = parse([owner, conseq(), afterSuggestion, both]);
    const out = setAsideSuggestionConsequences(file, new Set(["thm:main"]));
    expect(out.setAside).toEqual([{ node: "def:v", follows: ["thm:main"] }]);
    expect(out.file.patches.map((p) => p.node)).toEqual(["lem:a", "lem:b", "lem:c"]);
    // nothing to set aside: the file is returned as it is
    expect(setAsideSuggestionConsequences(file, new Set())).toEqual({ file, setAside: [] });
    // the suggestion's node patched as well (the owner accepted it): the patch follows a repair, nothing is set aside
    const accepted = parse([owner, conseq(), afterSuggestion, { ...owner, node: "thm:main", ops: [] }]);
    expect(setAsideSuggestionConsequences(accepted, new Set(["thm:main"])).setAside).toEqual([]);
    // a patch following a set-aside patch goes with it
    const chain = parse([owner, conseq(), afterSuggestion, conseq({ node: "lem:c", consequence_of: ["def:v"], reason: "The step now uses the rescaled estimator." })]);
    const out2 = setAsideSuggestionConsequences(chain, new Set(["thm:main"]));
    expect(out2.setAside).toEqual([{ node: "def:v", follows: ["thm:main"] }, { node: "lem:c", follows: ["def:v"] }]);
    expect(out2.file.patches.map((p) => p.node)).toEqual(["lem:a", "lem:b"]);
  });

  it("a definition whose formula a repair needs changed follows it, with its own units or none", () => {
    const def = (ops: object[]) => conseq({ node: "def:v", ops: ops.length ? [{ ...OP_B, unit: "def:v/1/1" }] : [] });
    const v = (ops: object[]) => consequenceViolations(parse([owner, def(ops)]), (n) => n === "lem:a", { statements: new Set(["lem:a"]), printsProof: () => true });
    expect(v([OP_B])).toEqual([]);
    expect(v([])).toEqual([]);
  });

  it("a consequence naming another consequence is told the repairs that chain starts from", () => {
    const c = conseq({ node: "lem:c", consequence_of: ["lem:b"], reason: "The step now follows the restated Lemma~\\ref{lem:b}." });
    const v = consequenceViolations(parse([owner, conseq(), c]), (n) => n === "lem:a", { statements: new Set(["lem:a", "lem:b", "lem:c"]), printsProof: () => true });
    expect(v).toContainEqual(expect.stringContaining('names "lem:b" in `consequence_of`, whose own patch only follows other repairs: replace "lem:b" by "lem:a"'));
    // its repairs already named (live CNS thm:dml): remove it
    const both = consequenceViolations(parse([owner, conseq(), { ...c, consequence_of: ["lem:a", "lem:b"] }]), (n) => n === "lem:a", { statements: new Set(["lem:a", "lem:b", "lem:c"]), printsProof: () => true });
    expect(both).toContainEqual(expect.stringContaining('("lem:a"), already named: remove "lem:b" from `consequence_of`'));
  });

  it("findingNodes: the directive's nodes (not a `consequence` finding), the ledger's, earlier finding-answering patches; not a rejected consequential edit", () => {
    const prior = parse([owner, conseq(), { ...conseq({ node: "lem:c", consequence_of: null, reason: null }) }]);
    const s = findingNodes({ findings: [{ id: "lem:b", axis: "patch rejected" }, { id: "lem:d", axis: "clarify" }, { id: "run", axis: "key_results" }], ledger: { "lem:e": { detail: "x", witness: null } }, prior });
    expect([...s].sort()).toEqual(["lem:a", "lem:c", "lem:d", "lem:e"]);
    expect(findingNodes({ findings: [{ id: "lem:b", axis: "correctness" }], ledger: {}, prior }).has("lem:b")).toBe(true);
    expect([...findingNodes({ findings: [{ id: "lem:a", axis: "correctness" }, { id: "lem:b", axis: "consequence" }], ledger: {}, prior: null })]).toEqual(["lem:a"]);
  });
});

async function fixture(replies: object[]) {
  const repoRoot = await mkdtemp(path.join(os.tmpdir(), "v1-consequential-"));
  tmp.push(repoRoot);
  const runDir = path.join(repoRoot, "runs", "cq");
  await mkdir(path.join(runDir, "discovery"), { recursive: true });
  for (const f of [VERIFY_FILES.coreJson, VERIFY_FILES.coreTranscribed]) await writeFile(path.join(runDir, f), JSON.stringify(core(), null, 2));
  await writeToyPaper(runDir, core());
  const findings = [{ id: "lem:a", axis: "correctness", detail: "the bound on lem:a is wrong", witness: "w" }];
  await writeFile(path.join(runDir, VERIFY_FILES.v1ReviseDirective), JSON.stringify({ mode: "patch", round: 1, findings }));
  const state = createVerifyInitialState("cq", { phase: "init", source: { input: "p.tex", main_file: "main.tex", sha256: "h" }, targets: null, core_sha256: null, v1_rounds: 1, v1_5_rounds: 1, findings: [], report_path: null });
  const calls: CodexRunInput[] = [];
  const codex = (async (input: CodexRunInput) => {
    calls.push(input);
    return { stdout: JSON.stringify(replies[calls.length - 1]), stderr: "" };
  }) as typeof runCodex;
  return { repoRoot, runDir, state, calls, codex };
}

describe("V1 patch round: the runner enforces the contract", () => {
  const file = (b: object) => ({ key_results: ["lem:a"], key_contribution: "c", patches: [owner, b], unfixable: [], rejected: [] });

  it("a sibling patched with a defect note is sent back; declared consequential it is accepted and persisted", async () => {
    const round1 = file(conseq({ consequence_of: null, reason: null, owner_explanation: cannedExplanation("lem:b", OP_B.unit) }));
    const round2 = file(conseq());
    const { repoRoot, runDir, state, calls, codex } = await fixture([round1, round2]);
    const res = await runStageV1({ repoRoot, qid: "cq", runDir, state, deps: { runCodex: codex }, dryRun: false, log: () => {} });
    expect(res.status).toBe("completed");
    expect(calls).toHaveLength(2);
    expect(calls[1]!.prompt).toMatch(/VIOLATIONS IN YOUR PREVIOUS REPLY[\s\S]*"lem:b": this node has no finding — give consequence_of and a one-sentence reason, not a defect note/);
    const onDisk = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.patches), "utf8")) as PatchFile;
    const b = onDisk.patches.find((p) => p.node === "lem:b")!;
    expect(b.consequence_of).toEqual(["lem:a"]);
    expect(b.reason).toContain("normalizer lower bound");
    expect(b.owner_explanation).toBeUndefined();
  });
});

describe("V1 patch round: a consequential patch following a SUGGESTED repair", () => {
  const sug = { corrected_statement: "$a \\le 2$.", ops: [{ op: "replace", unit: "lem:a/1/1", to: null, tex: "$a \\le 2$." }], proof_note: "the bound is doubled; every other step is unchanged.", given_up: "the constant 1" };
  const unfix = { node: "lem:a", reason: "only the doubled bound holds", suggested_repair: sug, owner_explanation: { ...cannedExplanation("lem:a"), gives_up: sug.given_up } };
  const reply = (key_results: string[]) => ({ key_results, key_contribution: "c", patches: [conseq()], unfixable: [unfix], rejected: [] });
  const run = async (replies: object[]) => {
    const f = await fixture(replies);
    const logs: string[] = [];
    const res = await runStageV1({ repoRoot: f.repoRoot, qid: "cq", runDir: f.runDir, state: f.state, deps: { runCodex: f.codex }, dryRun: false, log: (m) => logs.push(m) });
    const onDisk = JSON.parse(await readFile(path.join(f.runDir, VERIFY_FILES.patches), "utf8")) as PatchFile;
    return { ...f, res, logs, onDisk };
  };

  it("of an intermediate result: the suggestion is the repair the runner applies in the same call, so the patch follows a repair and stands", async () => {
    const { res, calls, onDisk, logs } = await run([reply(["lem:b"])]);
    expect(res.status).toBe("completed");
    expect(calls).toHaveLength(1);
    expect(onDisk.patches.map((p) => p.node).sort()).toEqual(["lem:a", "lem:b"]);
    expect(onDisk.patches.find((p) => p.node === "lem:a")!.accepted_weakening).toBe(true);
    expect(onDisk.patches.find((p) => p.node === "lem:b")!.consequence_of).toEqual(["lem:a"]);
    expect(logs.join("\n")).not.toContain("set aside");
  });

  it("of a main theorem (a key result): the owner rules first — the patch is held in the file, no violation, the halt presents the suggestion; it is applied with the accepted suggestion", async () => {
    const { res, calls, onDisk, logs, runDir, state } = await run([reply(["lem:a"])]);
    expect(res.status).toBe("checkpoint");
    expect(res.message).toContain("await the owner");
    expect(calls).toHaveLength(1);
    expect(onDisk.patches).toEqual([]);
    expect(onDisk.unfixable.map((u) => u.node)).toEqual(["lem:a"]);
    expect(onDisk.set_aside!.map((p) => [p.node, p.consequence_of])).toEqual([["lem:b", ["lem:a"]]]);
    expect(logs.join("\n")).toContain('1 consequential patch(es) set aside, each following only a suggested repair of a main theorem the owner has not ruled on — lem:b (after lem:a)');
    // the owner accepts: the suggestion and the patch held for it are applied together
    const lines = await ruleOnReceipt(runDir, state, { accept: ["lem:a"] });
    expect(lines[0]).toContain("with the consequential patch(es) held for it (lem:b)");
    const after = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.patches), "utf8")) as PatchFile;
    expect(after.patches.map((p) => p.node).sort()).toEqual(["lem:a", "lem:b"]);
    expect(after.patches.find((p) => p.node === "lem:a")!.accepted_weakening).toBe(true);
    expect(after.set_aside).toBeUndefined();
  });

  it("of a main theorem the owner declines: the patch held for it is dropped", async () => {
    const { runDir, state } = await run([reply(["lem:a"])]);
    await ruleOnReceipt(runDir, state, { decline: [{ node: "lem:a", reason: "the doubled bound is not worth formalizing" }] });
    const after = JSON.parse(await readFile(path.join(runDir, VERIFY_FILES.patches), "utf8")) as PatchFile;
    expect(after.patches).toEqual([]);
    expect(after.set_aside).toBeUndefined();
    expect(after.unfixable[0]!.declined).toBeTruthy();
  });
});

// --- rendering --------------------------------------------------------------------------------

const FLAT = [
  "\\documentclass{article}", // 1
  "\\begin{document}", // 2
  "\\begin{lemma}\\label{lem:a}", // 3
  "$a \\le 1$.", // 4
  "\\end{lemma}", // 5
  "\\begin{lemma}\\label{lem:b}", // 6
  "$b \\lesssim h^{-1}$.", // 7
  "\\end{lemma}", // 8
  "\\begin{proof}", // 9
  "First, $\\omega_h \\geq \\tilde f/2$ by the density bound.", // 10
  "Then $b \\le 2/\\tilde f$ follows.", // 11
  "\\end{proof}", // 12
  "\\end{document}", // 13
].join("\n");

function input(patches: object[]): AnnotationInput {
  const c = core();
  const loc = (id: string, from: number, to: number) => ({ file: "main.tex", from, to, env: "lemma", label: id });
  const cc = { ...c, statements: [{ ...c.statements[0]!, tex_locator: loc("lem:a", 3, 5) }, { ...c.statements[1]!, tex_locator: loc("lem:b", 6, 8) }] } as Core;
  const env = (id: string, from: number, to: number, body: string, proof: { text: string; from: number; to: number } | null) => ({
    id, kind: "lemma", envName: "lemma", label: id, title: null, body, proof: proof?.text ?? null, proofLines: proof ? { file: "main.tex", from: proof.from, to: proof.to } : null, section: null, lines: { file: "main.tex", from, to }, refs: [],
  });
  return {
    files: { "main.tex": FLAT },
    envs: { main_file: "main.tex", files: ["main.tex"], newtheorem: {}, bibliography: [], envs: [env("lem:a", 3, 5, "$a \\le 1$.", null), env("lem:b", 6, 8, "$b \\lesssim h^{-1}$.", { text: PROOF_B, from: 9, to: 12 })] } as never,
    flatText: FLAT,
    lineMap: FLAT.split("\n").map((_, i) => ({ file: "main.tex", line: i + 1 })),
    refs: null,
    transcribed: cc,
    core: cc,
    patches: { patches: patches as never, unfixable: [] },
    paperErrors: { "lem:a": { detail: "the bound on lem:a is wrong", witness: "w" } },
    findings: [],
    review: null,
  };
}

describe("the annotated paper: a consequential edit", () => {
  const b = { ...conseq(), proof_note: "derived" };

  it("its step red/blue as for any repair, one line naming the repair it follows, no defect block", () => {
    const plan = planAnnotations(input([owner, b]));
    const out = applyEdits(FLAT, plan.edits["main.tex"] ?? []);
    expect(out).toContain(`\\vsStep{Then $b \\le 2/\\tilde f$ follows.} \\vsCorrectedStep{${OP_B.tex}}`);
    const note = out.slice(out.indexOf("\\begin{lemma}\\label{lem:b}"), out.indexOf("\\begin{proof}"));
    expect(note).toContain("\\vsLine Changed to follow the repair of Lemma~\\ref{lem:a}: the last step now divides by the normalizer lower bound the repair of Lemma~\\ref{lem:a} adds.");
    expect(note).not.toMatch(/Claim:|What is wrong|Why:|Counterexample:/u);
    // No statement op of its own: its printed statement is left as printed (no insertion marks).
    expect(note).toContain("$b \\lesssim h^{-1}$. \\vsNote{");
    expect(note).not.toContain("\\vsAdded");
    expect(plan.records.find((r) => r.node === "lem:b" && r.located_by !== "proof edit")?.kind).toBe("corrected proof");
  });
});
