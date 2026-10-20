import { describe, expect, it } from "vitest";
import { readFileSync } from "node:fs";
import { readFile } from "node:fs/promises";
import path from "node:path";
import { runStructuralGate, type GateViolation } from "../../src/core/gate.js";
import { CoreSchema, type Core } from "../../src/core/schema.js";

function clone(): Core {
  const raw = readFileSync(new URL("../fixtures/stat_ate_overlap_decay_core.json", import.meta.url), "utf8");
  return JSON.parse(raw) as Core;
}

function codes(vs: GateViolation[]): string[] {
  return vs.map((v) => v.code);
}

describe("structural gate", () => {
  it("the hand-authored golden core passes every gate", () => {
    const res = runStructuralGate(clone(), { requireDischarged: true });
    expect(res.violations).toEqual([]);
    expect(res.ok).toBe(true);
  });

  it.each([
    ["G1", (core: Core) => { core.assumptions.find((x) => x.id === "ass:tail")!.free_symbols!.push("undeclared_symbol"); }],
    ["G4", (core: Core) => { core.statements.find((s) => s.id === "thm:lower")!.depends_on.push("thm:does-not-exist"); }],
    ["schema", (core: Core) => { delete (core.assumptions.find((x) => x.id === "ass:tail") as { standard?: unknown }).standard; }],
  ] as const)("rejects a %s breakage", (code, breakIt) => {
    const core = clone();
    breakIt(core);
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(res.ok).toBe(false);
    expect(codes(res.violations)).toContain(code);
  });

  it("G1: a comma-grouped free-symbol entry gets an atomic-splitting diagnostic", () => {
    const core = clone();
    const declared = core.symbols.slice(0, 2).map((s) => s.name);
    core.assumptions.find((x) => x.id === "ass:tail")!.free_symbols = [declared.join(",")];
    const res = runStructuralGate(core, { requireDischarged: true });
    expect(res.ok).toBe(false);
    expect(res.violations.find((v) => v.code === "G1")?.message).toMatch(
      /exactly one declared symbol \(split comma-separated groups\)/,
    );
  });

  it("G2: a `verbatim` several-sentence condition is a referee note, never a violation", () => {
    const core = clone();
    core.assumptions.find((x) => x.id === "ass:smoothness")!.condition = "One of two alternatives holds. (1) $a = 1$. (2) $b = 2$.";
    const res = runStructuralGate(core, { requireDischarged: true, verbatim: true });
    expect(codes(res.violations)).not.toContain("G2");
    expect(res.notes?.map((n) => n.code)).toContain("G2");
    expect(codes(runStructuralGate(core, { requireDischarged: true }).violations)).toContain("G2");
  });

  it("G2: a verbatim quote of a displayed equation is not an omnibus condition", async () => {
    const fixture = JSON.parse(await readFile(path.join(__dirname, "..", "verify", "fixtures", "v6", "core.json"), "utf8"));
    fixture.assumptions.push({
      id: "ass:ral-form",
      condition: "Suppose the estimator admits the linear form \\begin{equation} \\hat\\tau - \\tau = n^{-1}\\sum_i \\psi_i + o_p(n^{-1/2}). \\label{eq:RAL1} \\end{equation} Here $\\psi$ has mean zero.",
      novel: { flag: true, justification: "paper" },
      tex_locator: { file: "flat.tex", from: 0, to: 0, env: "prose", label: null },
    });
    const core = CoreSchema.parse(fixture);
    const strict = runStructuralGate(core, { allowBookkeeping: true });
    const verbatim = runStructuralGate(core, { allowBookkeeping: true, verbatim: true });
    expect(strict.violations.some((v) => v.code === "G2" && v.where === "ass:ral-form")).toBe(true);
    expect(verbatim.violations.some((v) => v.code === "G2" && v.where === "ass:ral-form")).toBe(false);
  });
});

describe("G4 dependency cycles", () => {
  it("reports every cycle in one pass, at the statement whose dependency closes it", () => {
    const core = clone();
    // two disjoint cycles: lecam ↔ bernoulli, and smoothness-l2 → clipped-bias → smoothness-l2
    core.statements.find((s) => s.id === "lem:lecam-two-point")!.depends_on.push("lem:bernoulli-kl");
    core.statements.find((s) => s.id === "lem:bernoulli-kl")!.depends_on.push("lem:lecam-two-point");
    core.statements.find((s) => s.id === "lem:smoothness-l2")!.depends_on.push("lem:clipped-bias");
    const g4 = runStructuralGate(core, { requireDischarged: true }).violations.filter((v) => v.code === "G4");
    // one violation per cycle, at whichever member's edge the search closes it on
    expect(g4).toHaveLength(2);
    expect(g4.some((v) => ["lem:lecam-two-point", "lem:bernoulli-kl"].includes(v.where))).toBe(true);
    expect(g4.some((v) => ["lem:smoothness-l2", "lem:clipped-bias"].includes(v.where))).toBe(true);
    expect(g4.every((v) => /dependency cycle/.test(v.message))).toBe(true);
  });
});
