// shown = hashed, for what a shard prints under PINNED READINGS beyond the wiring: a hypothesis's own
// readings, and the symbols left open that its nodes — or the nodes they use — name anywhere in
// their record. And the transition of the verdicts keyed before either was read into a basis.
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { basisInputs, basisInputsV4, basisOf, buildCore, mergeBasisExtra, type BasisExtra } from "../../src/verify/core_graph.js";
import { readingsSection } from "../../src/verify/referee_shard_prompts.js";
import { ownReadingsExtra, partitionByBasis, symbolBasisExtra } from "../../src/verify/stage_v1_5.js";
import type { V15NodeVerdict, V15Review, V15SymbolVerdict } from "../../src/verify/types.js";

const pin = (text: string) => ({ id: "ass:pin-owner-1", kind: "regularity", condition: text, bookkeeping: { flag: true, added_by: "owner", reason: "pins reading of ass:scale: the owner's reading" } });

function core(over: { pin?: string } = {}): Core {
  return {
    qid: "shown",
    symbols: [{ name: "\\sigma", type: "scale" }, { name: "\\theta", type: "parameter" }, { name: "K", type: "kernel" }],
    assumptions: [{ id: "ass:scale", condition: "$\\sigma > 0$.", free_symbols: ["\\sigma"] }, ...(over.pin ? [pin(over.pin)] : [])],
    definitions: [],
    statements: [
      // K is named in the proof of thm:b only: its statement does not name it
      { id: "thm:b", kind: "theorem", statement: "The limit is normal.", proof_tex: "Use the kernel $K$.", depends_on: ["ass:scale", ...(over.pin ? ["ass:pin-owner-1"] : [])], status: "to-prove" },
      { id: "lem:a", kind: "lemma", statement: "$\\hat\\theta \\to \\theta$.", depends_on: [], status: "to-prove" },
    ],
    target_estimand: "x",
    bibliography: [],
  } as unknown as Core;
}

const sym = (name: string, over: Partial<V15SymbolVerdict> = {}): V15SymbolVerdict =>
  ({ name, meaning: "ok", fix: null, ambiguity: "ok", reading: null, redefined_at: null, detail: "d", ...over }) as V15SymbolVerdict;
const open = (name: string, detail: string): V15SymbolVerdict => sym(name, { ambiguity: "unresolvable", detail });
const clean = (id: string): V15NodeVerdict => ({ id, faithfulness: "ok", ambiguity: "ok", correctness: "ok", detail: "", witness: null }) as V15NodeVerdict;

/** A pass over `c` with these symbol verdicts: the graded core, its extras, and the bases it keys. */
function pass(c: Core, symbols: V15SymbolVerdict[], earlier = false) {
  const graded = buildCore(c, { symbols }).core;
  const now: BasisExtra = mergeBasisExtra(ownReadingsExtra(graded), symbolBasisExtra(graded, symbols));
  const before: BasisExtra = symbolBasisExtra(graded, symbols, { earlier: true });
  const ids = [...graded.statements, ...graded.assumptions].map((n) => n.id);
  const bases = Object.fromEntries(ids.map((id) => [id, basisOf(basisInputs(graded, id, earlier ? before : now))]));
  const review = { nodes: ids.map((id) => ({ ...clean(id), basis: bases[id], basis_scheme: 5 })) } as unknown as V15Review;
  return { graded, now, before, bases, review };
}

describe("shown = hashed: PINNED READINGS beyond the wiring", () => {
  it("a hypothesis's own reading is printed as binding on it, and moves its basis when reworded or removed", () => {
    const withPin = pass(core({ pin: "the scale is the conditional one" }), []);
    expect(readingsSection(withPin.graded, undefined, ["ass:scale"]).join("\n")).toContain("the scale is the conditional one — binds ass:scale");
    const reworded = pass(core({ pin: "the scale is the unconditional one" }), []);
    const removed = pass(core(), []);
    expect(reworded.bases["ass:scale"]).not.toBe(withPin.bases["ass:scale"]);
    expect(removed.bases["ass:scale"]).not.toBe(withPin.bases["ass:scale"]);
    // a re-typesetting of the reading is the same reading; a hypothesis with no reading keeps its key
    expect(pass(core({ pin: "the scale is the  conditional one" }), []).bases["ass:scale"]).toBe(withPin.bases["ass:scale"]);
    expect(removed.bases["ass:scale"]).toBe(basisOf(basisInputs(removed.graded, "ass:scale", removed.before)));
    // the edit re-grades the hypothesis itself, not only the statements the reading is wired into
    const part = partitionByBasis(reworded.graded, withPin.bases, withPin.review, reworded.now);
    expect(part.toGrade).toContain("ass:scale");
  });

  it("a symbol left open is in the basis of every node whose shard lists it — a node that names it in its proof alone, with the line printed", () => {
    const was = pass(core(), [sym("K")]);
    const left = pass(core(), [open("K", "a kernel or a constant: the paper does not say")]);
    expect(readingsSection(left.graded, { binding: left.graded, unresolved: [open("K", "a kernel or a constant: the paper does not say")] }, ["thm:b"]).join("\n")).toContain("- K: a kernel or a constant: the paper does not say");
    expect(left.bases["thm:b"]).not.toBe(was.bases["thm:b"]);
    expect(left.bases["lem:a"]).toBe(was.bases["lem:a"]);
    // … which the earlier extra (the statement's text, or a hypothesis's) did not reach
    expect(basisOf(basisInputs(left.graded, "thm:b", left.before))).toBe(basisOf(basisInputs(was.graded, "thm:b", was.before)));
    // the line is read too
    expect(pass(core(), [open("K", "another line")]).bases["thm:b"]).not.toBe(left.bases["thm:b"]);
    // a node using a node that names it is shown it as well
    const sigma = pass(core(), [open("\\sigma", "which scale")]);
    expect(sigma.bases["thm:b"]).not.toBe(was.bases["thm:b"]);
    expect(sigma.bases["ass:scale"]).not.toBe(was.bases["ass:scale"]);
  });

  it("the transition: a verdict keyed before these were read is re-keyed without a call from a complete pass, graded afresh from a paused one, and never carried once its earlier basis moved", () => {
    const symbols = [open("K", "a kernel or a constant")];
    const c = core({ pin: "the scale is the conditional one" });
    const old = pass(c, symbols, true);
    const cur = pass(c, symbols);
    expect(old.bases["thm:b"]).not.toBe(cur.bases["thm:b"]);
    expect(old.bases["ass:scale"]).not.toBe(cur.bases["ass:scale"]);
    const complete = partitionByBasis(cur.graded, old.bases, old.review, cur.now, {}, new Map(), undefined, { complete: true, earlierExtra: cur.before });
    expect(complete.toGrade).toEqual([]);
    expect(Object.fromEntries(complete.bases)).toEqual(cur.bases);
    const paused = partitionByBasis(cur.graded, old.bases, old.review, cur.now, {}, new Map(), undefined, { complete: false, earlierExtra: cur.before });
    expect(paused.toGrade.sort()).toEqual(["ass:scale", "thm:b"]);
    expect(paused.carried.map((n) => n.id).sort()).toEqual(["ass:pin-owner-1", "lem:a"]);
    // the statement changed since: its earlier basis does not hold either
    const moved = core({ pin: "the scale is the conditional one" });
    moved.statements[1]!.statement = "$\\hat\\theta \\to \\theta$ in probability.";
    const after = pass(moved, symbols);
    expect(partitionByBasis(after.graded, old.bases, old.review, after.now, {}, new Map(), undefined, { complete: true, earlierExtra: after.before }).toGrade).toEqual(["lem:a"]);
  });

  it("a scheme-4 cache (every run on file) was keyed with the earlier extra: its transition reads that one, so a complete pass is still carried whole", () => {
    const symbols = [open("K", "a kernel or a constant"), open("\\sigma", "which scale")];
    const cur = pass(core(), symbols);
    const ids = Object.keys(cur.bases);
    const v4 = Object.fromEntries(ids.map((id) => [id, basisOf(basisInputsV4(cur.graded, id, cur.before))]));
    const review = { nodes: ids.map((id) => ({ ...clean(id), basis: v4[id], basis_scheme: 4 })) } as unknown as V15Review;
    const part = partitionByBasis(cur.graded, v4, review, cur.now, {}, new Map(), undefined, { complete: true, earlierExtra: cur.before });
    expect(part.toGrade).toEqual([]);
    expect(Object.fromEntries(part.bases)).toEqual(cur.bases);
    // … of a paused or halted pass, only the verdicts whose key the new extra leaves as it was: the
    // nodes shown an open symbol (their key never read its line) are graded afresh
    const paused = partitionByBasis(cur.graded, v4, review, cur.now, {}, new Map(), undefined, { complete: false, earlierExtra: cur.before });
    expect(paused.toGrade.sort()).toEqual(["ass:scale", "thm:b"]);
    expect(paused.carried.map((n) => n.id)).toEqual(["lem:a"]);
    // (read with the new extra, the same keys would not hold)
    expect(basisOf(basisInputsV4(cur.graded, "thm:b", cur.now))).not.toBe(v4["thm:b"]);
  });
});
