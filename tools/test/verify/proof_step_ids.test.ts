/**
 * Proof steps name no pipeline id (user rule 2026-09-25: "Apply ass:patch-local-normalizer …" reached
 * the author in a blue step): the runner sends back a proof op or (unprinted-proof) proof note naming a node id (paper
 * labels and `\ref` arguments exempt).
 */
import { describe, expect, it } from "vitest";
import { PatchFileSchema, type PatchFile } from "../../src/verify/patches.js";
import { proofStepIdViolations } from "../../src/verify/stage_v1.js";

/** An op replacing the printed step "Then it follows." (the proof's second unit). */
const OP = (tex: string) => ({ op: "replace" as const, unit: "lem:b/proof/1/2", tex });
const file = (patches: object[], unfixable: object[] = []): PatchFile =>
  PatchFileSchema.parse({ key_results: ["lem:a"], key_contribution: "c", patches: patches.map((p) => ({ corrected_statement: null, proof_note: "derived", ...p })), unfixable });

describe("the runner: proofStepIdViolations", () => {
  const prints = (n: string): boolean => n !== "lem:np";
  it.each([
    ["flags a node id in any replacement step, naming the node", [OP("Apply ass:bounded to both."), { op: "replace" as const, unit: "lem:b/proof/1/1", tex: "First step. By lem:a, done." }], undefined, ['a proof step of the patch for "lem:b" names ass:bounded, lem:a']],
    ["exempts the paper's own labels and reference-macro arguments", [OP("By Lemma~\\ref{lem:zz} and lem:a, done.")], new Set(["lem:a"]), []],
  ] as Array<[string, object[], Set<string> | undefined, string[]]>)("%s", (_t, ops, labels, violations) => {
    expect(proofStepIdViolations(file([{ node: "lem:b", ops }]), prints, labels)).toEqual(violations.map((v) => expect.stringContaining(v)));
  });

  it("checks a proof note only where the paper prints no proof; checks a suggested repair too", () => {
    expect(proofStepIdViolations(file([{ node: "lem:b", proof_note: "Uses ass:patch-x." }]), prints)).toEqual([]);
    expect(proofStepIdViolations(file([{ node: "lem:np", proof_note: "Uses ass:patch-x." }]), prints)).toEqual([expect.stringContaining('"lem:np" names ass:patch-x')]);
    const sug = { node: "lem:b", reason: "r", suggested_repair: { corrected_statement: null, proof_note: "d", ops: [OP("Use ass:patch-y.")], given_up: "g" } };
    expect(proofStepIdViolations(file([], [sug]), prints)).toEqual([expect.stringContaining('a proof step of the suggested repair for "lem:b" names ass:patch-y')]);
  });
});
