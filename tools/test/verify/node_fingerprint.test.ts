/**
 * The basis of a V1.5 verdict (`core_graph.ts` `nodeFingerprint`) moves with what the node rests
 * on — including the symbol-table entries its closure uses — and with nothing else: a symbol-table
 * fix re-opens only the verdicts of the nodes using that symbol, and a pinned symbol reading only
 * those of the statements it binds.
 */
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { buildCore, nodeFingerprint, normalizeCore } from "../../src/verify/core_graph.js";

function core(symbols: Array<Record<string, unknown>> = []): Core {
  return {
    qid: "fp",
    symbols: [
      { name: "\\theta", type: "parameter", def: "the target" },
      { name: "\\sigma", type: "scale" },
      { name: "\\psi", type: "score", refs: ["\\gamma"] },
      { name: "\\gamma", type: "nuisance" },
      { name: "K", type: "kernel" },
      ...symbols,
    ],
    assumptions: [{ id: "ass:scale", condition: "$\\sigma > 0$.", free_symbols: ["\\sigma"] }],
    definitions: [],
    statements: [
      { id: "lem:a", kind: "lemma", statement: "$\\hat\\theta \\to \\theta$.", depends_on: [], status: "to-prove" },
      { id: "thm:b", kind: "theorem", statement: "The limit is normal.", depends_on: ["ass:scale"], status: "to-prove" },
      { id: "thm:c", kind: "theorem", statement: "$E\\psi = 0$.", depends_on: [], status: "to-prove", free_symbols: ["\\psi"] },
    ],
    target_estimand: "x",
    bibliography: [],
  } as unknown as Core;
}

const fix = (c: Core, name: string, over: Record<string, unknown>): Core => ({ ...c, symbols: c.symbols.map((x) => (x.name === name ? { ...x, ...over } : x)) }) as Core;

describe("nodeFingerprint and the symbol table", () => {
  it("a fix to a used symbol re-opens exactly its users — directly, through a hypothesis, or through refs", () => {
    const c = core();
    const theta = fix(c, "\\theta", { def: "the population functional" });
    expect(nodeFingerprint(theta, "lem:a")).not.toBe(nodeFingerprint(c, "lem:a"));
    expect(nodeFingerprint(theta, "thm:b")).toBe(nodeFingerprint(c, "thm:b"));
    const sigma = fix(c, "\\sigma", { type: "random scale" });
    expect(nodeFingerprint(sigma, "thm:b")).not.toBe(nodeFingerprint(c, "thm:b")); // via ass:scale
    expect(nodeFingerprint(sigma, "lem:a")).toBe(nodeFingerprint(c, "lem:a"));
    const gamma = fix(c, "\\gamma", { def: "E[Y | X]" });
    expect(nodeFingerprint(gamma, "thm:c")).not.toBe(nodeFingerprint(c, "thm:c")); // \psi refers to \gamma
    expect(nodeFingerprint(gamma, "lem:a")).toBe(nodeFingerprint(c, "lem:a"));
  });

  it("a pinned symbol reading (the symbol's def) moves only the statements using the symbol", () => {
    const c = core();
    const pin = { name: "\\sigma", meaning: "ok", fix: null, ambiguity: "pinned", reading: { reading: "$\\sigma$ is fixed.", evidence: "Section 2" }, redefined_at: null, detail: "d" };
    const graded = buildCore(c, { symbols: [pin] as never }).core;
    expect(nodeFingerprint(graded, "thm:b")).not.toBe(nodeFingerprint(c, "thm:b")); // through its hypothesis
    expect(nodeFingerprint(graded, "lem:a")).toBe(nodeFingerprint(c, "lem:a"));
    expect(nodeFingerprint(graded, "thm:c")).toBe(nodeFingerprint(c, "thm:c"));
  });
});

describe("the verdict cache under the current scheme", () => {
  it("a basis takes no prompt and no code version: the same core gives the same basis", () => {
    expect(nodeFingerprint.length).toBeLessThanOrEqual(3); // (core, id, extra) — nothing else
    expect(nodeFingerprint(core(), "thm:c")).toBe(nodeFingerprint(core(), "thm:c"));
  });
});

/** `lem:a` becomes a second user of `ass:scale` (its own wiring; `used_by` re-derived). */
function rewire(c: Core): Core {
  const next = { ...c, statements: c.statements.map((st) => (st.id === "lem:a" ? { ...st, depends_on: [...st.depends_on, "ass:scale"] } : st)) } as Core;
  return normalizeCore(next, next);
}

describe("a basis reads no derived user-side field", () => {
  it("changing a user's wiring does not move the used node's basis, nor that of its other users", () => {
    const before = normalizeCore(core(), core());
    const after = rewire(before);
    expect(after.assumptions[0]!.used_by).toEqual(["lem:a", "thm:b"]);
    expect(before.assumptions[0]!.used_by).toEqual(["thm:b"]);
    expect(nodeFingerprint(after, "ass:scale")).toBe(nodeFingerprint(before, "ass:scale"));
    expect(nodeFingerprint(after, "thm:b")).toBe(nodeFingerprint(before, "thm:b"));
    expect(nodeFingerprint(after, "lem:a")).not.toBe(nodeFingerprint(before, "lem:a"));
  });
});
