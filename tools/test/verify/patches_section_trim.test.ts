/**
 * The PATCHES section of a shard or global prompt (`stage_v1_5.ts` `patchesSection`) carries
 * only what the call needs: no `printed` statement for a node whose excerpt as printed the prompt
 * already shows, `repairs` the ledger entry as it is (the fixer's note is the patch's own), and only the
 * `unfixable` entries of the nodes graded. What the core carries travels once: no `ops`, no
 * `corrected_statement`, no corollary `follows`; the global pass sees no `proof_note` or `repairs`.
 */
import { describe, expect, it } from "vitest";
import { patchesSection } from "../../src/verify/stage_v1_5.js";

const patch = (node: string) => ({
  node,
  ops: [{ op: "replace", unit: "u1", to: null, tex: `${node} corrected` }],
  corrected_statement: `${node} corrected`,
  proof_note: "note",
  corollaries: [{ title: "block", statement: `${node} block`, follows: "the block's proof", adds: null }],
  owner_explanation: `the patch's own explanation of ${node}`,
});
const args = {
  patches: {
    patches: [patch("thm:a"), patch("lem:b")],
    unfixable: [{ node: "thm:a", reason: "x" }, { node: "thm:z", reason: "y" }],
    key_results: ["thm:a"],
    key_contribution: "k",
  },
  printed: new Map([
    ["thm:a", "thm:a as printed"],
    ["lem:b", "lem:b as printed"],
  ]),
  paperErrors: {
    "thm:a": { kind: "error", detail: "d", witness: "w" },
  },
} as never;
const json = (sec: string[]): Record<string, unknown> => JSON.parse(sec[0]!.slice(sec[0]!.indexOf("\n{") + 1).trim());

describe("patchesSection trims what a shard or the global pass already has", () => {
  it("a shard: printed dropped where the excerpt is shown, repairs the ledger entry, unfixable of its ids", () => {
    const out = json(patchesSection(args, ["thm:a", "lem:b"], (id) => id === "thm:a"));
    const [a, b] = out.patches as Array<Record<string, unknown>>;
    expect(a).not.toHaveProperty("printed");
    expect(a!.owner_explanation).toBe("the patch's own explanation of thm:a");
    expect(a!.repairs).toEqual({ kind: "error", detail: "d", witness: "w" });
    // lem:b's excerpt is not in the prompt: printed stays.
    expect(b!.printed).toBe("lem:b as printed");
    expect(out.unfixable).toEqual([{ node: "thm:a", reason: "x" }]);
    expect(out).not.toHaveProperty("key_results");
    // The corrected statement and the ops are the node's record in the core; a corollary's proof its node's proof_tex.
    expect(a).not.toHaveProperty("ops");
    expect(a).not.toHaveProperty("corrected_statement");
    expect(a!.proof_note).toBe("note");
    expect((a!.corollaries as Array<Record<string, unknown>>)[0]).toMatchObject({ statement: "thm:a block", title: "block" });
    expect((a!.corollaries as Array<Record<string, unknown>>)[0]).not.toHaveProperty("follows");
  });

  it("the global pass: the key results, printed texts, drops and adds; no ops, corrected statement, proof note or ledger entry", () => {
    const out = json(patchesSection(args, undefined, () => false, true));
    expect(out.key_results).toEqual(["thm:a"]);
    const [a] = out.patches as Array<Record<string, unknown>>;
    expect(a!.printed).toBe("thm:a as printed");
    for (const k of ["ops", "corrected_statement", "proof_note", "repairs", "owner_explanation"]) expect(a).not.toHaveProperty(k);
    expect((a!.corollaries as Array<Record<string, unknown>>)[0]).not.toHaveProperty("follows");
  });

  it("a shard grading a hypothesis sees the repairs that restate it (supersedes or drops)", () => {
    const base = args as unknown as { patches: Record<string, unknown> };
    const restating = { ...base, patches: { ...base.patches, patches: [{ ...patch("lem:b"), supersedes: ["ass:c"] }, { ...patch("thm:a"), drops: ["ass:d"] }] } } as never;
    const nodes = (ids: string[]): unknown[] => (json(patchesSection(restating, ids)).patches as Array<{ node: string }>).map((p) => p.node);
    expect(nodes(["ass:c"])).toEqual(["lem:b"]);
    expect((json(patchesSection(restating, ["ass:c"])).patches as Array<{ supersedes?: string[] }>)[0]!.supersedes).toEqual(["ass:c"]);
    expect(nodes(["ass:d"])).toEqual(["thm:a"]);
    expect(patchesSection(restating, ["ass:e"])).toEqual([]);
  });

  it("a shard grading only what a repair restates or drops is told so and no more; one grading the repaired node or a corollary of it sees the repair", () => {
    const base = args as unknown as { patches: Record<string, unknown> };
    const restating = { ...base, patches: { ...base.patches, patches: [{ ...patch("lem:b"), supersedes: ["ass:c", "ass:x"] }, { ...patch("thm:a"), drops: ["ass:d"] }] } } as never;
    const of = (ids: string[]): Array<Record<string, unknown>> => json(patchesSection(restating, ids)).patches as Array<Record<string, unknown>>;
    expect(of(["ass:c"])).toEqual([{ node: "lem:b", supersedes: ["ass:c"] }]);
    expect(of(["ass:d"])).toEqual([{ node: "thm:a", drops: ["ass:d"] }]);
    // The repaired node graded with the hypothesis: the repair whole.
    expect(of(["ass:c", "lem:b"])[0]).toMatchObject({ node: "lem:b", proof_note: "note", supersedes: ["ass:c", "ass:x"] });
    // A corollary the repair splits off is graded with the repair that wrote it.
    const cor = ((of(["lem:b"])[0]!.corollaries as Array<{ id: string }>)[0]!).id;
    expect(of([cor])[0]).toMatchObject({ node: "lem:b", proof_note: "note" });
    // The global pass is not a shard: unchanged.
    expect((json(patchesSection(restating, ["ass:c"], () => false, true)).patches as Array<Record<string, unknown>>)[0]).toHaveProperty("printed");
  });

  it("a proof note the node's record already shows as its proof change is not sent again", () => {
    const change = (id: string): string | null => (id === "thm:a" ? "[Proof change (minimal patch): note]" : id === "lem:b" ? "[Proof change (minimal patch): another text]" : null);
    const [a, b] = json(patchesSection(args, ["thm:a", "lem:b"], () => false, false, change)).patches as Array<Record<string, unknown>>;
    expect(a).not.toHaveProperty("proof_note");
    // A record that does not hold the note word for word: the note stays.
    expect(b!.proof_note).toBe("note");
  });

  it("a delta global pass lists the patches touching the nodes it shows in full whole, and the repair of every other key result or carried neighbour shown by one line", () => {
    const withWeakening = { ...(args as unknown as Record<string, unknown>), patches: { ...(args as unknown as { patches: Record<string, unknown> }).patches, patches: [{ ...patch("thm:a"), accepted_weakening: true, given_up: "the rate" }, patch("lem:b"), { ...patch("lem:c"), corrected_statement: null }] } } as never;
    const out = json(patchesSection(withWeakening, ["lem:b"], () => false, true, () => null, ["lem:c"]));
    const [a, b, c] = out.patches as Array<Record<string, unknown>>;
    expect(out.key_results).toEqual(["thm:a"]);
    // the key result, not in full: what the key-result judgement reads of its repair
    expect(a).toEqual({ node: "thm:a", carried: true, changes_printed_statement: true, accepted_weakening: true, given_up: "the rate", corollaries: [expect.stringMatching(/^thm:cor-fix-/)] });
    expect(b).toMatchObject({ node: "lem:b", printed: "lem:b as printed" });
    expect(b).not.toHaveProperty("carried");
    // a carried neighbour shown, no key result
    expect(c).toMatchObject({ node: "lem:c", carried: true, changes_printed_statement: false });
    // a repair of a node neither shown nor a key result has its line too
    expect((json(patchesSection(withWeakening, ["lem:b"], () => false, true)).patches as Array<{ node: string }>).map((p) => p.node)).toEqual(["thm:a", "lem:b", "lem:c"]);
    const lossy = { ...(args as unknown as Record<string, unknown>), patches: { ...(args as unknown as { patches: Record<string, unknown> }).patches, patches: [patch("thm:a"), { ...patch("lem:c"), given_up: "the uniform rate" }, { ...patch("lem:d"), accepted_weakening: true }, patch("lem:e")] } } as never;
    const lines = json(patchesSection(lossy, [], () => false, true)).patches as Array<Record<string, unknown>>;
    // every repair of the file, wherever its node is: an accepted loss is read with the contribution
    expect(lines.map((p) => p.node)).toEqual(["thm:a", "lem:c", "lem:d", "lem:e"]);
    expect(lines.every((p) => p.carried === true)).toBe(true);
    expect(lines[1]).toMatchObject({ carried: true, given_up: "the uniform rate" });
    expect(lines[2]).toMatchObject({ carried: true, accepted_weakening: true });
  });

  it("a global focus touching no patched node still gets the PATCHES section: the key results, the contribution, and each key result's repair by its line — what `patch_review` is owed on", () => {
    for (const focus of [[], ["ass:e"]]) {
      const sec = patchesSection(args, focus, () => false, true);
      expect(sec).toHaveLength(1);
      const out = json(sec);
      expect(out).toMatchObject({ key_results: ["thm:a"], key_contribution: "k" });
      const line = (node: string) => ({ node, carried: true, changes_printed_statement: true, corollaries: [expect.stringMatching(/-fix-/)] });
      expect(out.patches).toEqual([line("thm:a"), line("lem:b")]);
      expect(sec[0]).toContain("one line marked `carried: true`");
    }
    // a shard touching no patch has no section, as before
    expect(patchesSection(args, ["ass:e"])).toEqual([]);
  });

  it("a node graded in one shard with the node whose repair restates it is shown that repair whole; its own material is the line — whose content the body shown holds", () => {
    const base = args as unknown as { patches: Record<string, unknown> };
    const restating = { ...base, patches: { ...base.patches, patches: [{ ...patch("lem:b"), supersedes: ["ass:c"] }] } } as never;
    const together = (json(patchesSection(restating, ["lem:b", "ass:c"])).patches as Array<Record<string, unknown>>)[0]!;
    const alone = (json(patchesSection(restating, ["ass:c"])).patches as Array<Record<string, unknown>>)[0]!;
    expect(alone).toEqual({ node: "lem:b", supersedes: ["ass:c"] });
    // every part of the line (which repair, which list names the node) is in the body its shard-mate's shard shows
    expect(together).toMatchObject(alone);
    expect(together).toHaveProperty("proof_note");
  });

  it("an excerpt not located (the prompt shows the patched text): printed stays", () => {
    const out = json(patchesSection(args, ["thm:a"], () => false));
    expect((out.patches as Array<Record<string, unknown>>)[0]!.printed).toBe("thm:a as printed");
  });
});
