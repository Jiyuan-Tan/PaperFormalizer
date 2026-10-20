/**
 * Ops rules (design 2026-09-26): a repair is a replacement of printed units — of a result's statement or
 * proof, or of an assumption's or a definition's own printed text; the runner derives which of the
 * node's own hypotheses and definitions a replacement rewrites (`supersededNodes`) and the build unwires
 * them; an op's TeX never creates an equation number or label. Live fixture: the run of the maintainer's
 * own paper on extreme treatment effects (`handoff/tbs_extreme_effects`; Theorem thm:rate, whose first
 * sentence carries its assumption $\alpha < \beta$).
 */
import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { gunzipSync } from "node:zlib";
import { describe, expect, it } from "vitest";
import type { Core } from "../../src/core/schema.js";
import { buildCore } from "../../src/verify/core_graph.js";
import { PatchOpSchema, materializeRepair, nodePassage, unnumberedTex, type PassageSources, type PatchOp } from "../../src/verify/ops.js";
import { rederiveOn, type PatchFile } from "../../src/verify/patches.js";
import { RefCoreSchema } from "../../src/verify/ref_core.js";
import type { EnvsJson } from "../../src/verify/types.js";
import { PaperUnits, type UnitsFile } from "../../src/verify/units.js";

const DIR = path.join(path.dirname(fileURLToPath(import.meta.url)), "fixtures", "handoff", "tbs_extreme_effects", "discovery");
const gz = (f: string): string => gunzipSync(readFileSync(path.join(DIR, `${f}.gz`))).toString("utf8");
const ops = (x: unknown[]): PatchOp[] => x.map((o) => PatchOpSchema.parse(o));

function paper(): { src: PassageSources; core: Core } {
  const core = JSON.parse(gz("core.transcribed.json")) as Core;
  const envs = JSON.parse(gz("envs.json")) as EnvsJson;
  const src: PassageSources = { units: new PaperUnits(gz("flat.tex"), JSON.parse(gz("units.json")) as UnitsFile), refs: RefCoreSchema.parse(JSON.parse(gz("core_refs.json"))), statements: core.statements, envs };
  return { src, core };
}

describe("a replacement of an assumption's own printed text", () => {
  /** The sources with Theorem thm:rate printing no result: its environment is then the
   * assumption $\alpha < \beta$'s own (as an `assumption` environment is). */
  const ownEnv = (src: PassageSources): PassageSources => ({
    ...src,
    statements: src.statements.filter((s) => s.id !== "thm:rate"),
    refs: src.refs ? { ...src.refs, statements: src.refs.statements.filter((s) => s.id !== "thm:rate") } : null,
  });

  it("in its own environment: resolves on the units its reference-core source covers, and derives its corrected condition", () => {
    const src = ownEnv(paper().src);
    const passage = nodePassage(src, "ass:rate-alpha-less-beta");
    expect(passage).toMatchObject({ env: "thm:rate" });
    expect(passage!.units.map((u) => u.id)).toEqual(["thm:rate/1/1"]);
    const scope = { units: src.units, passage };
    const m = materializeRepair(ops([{ op: "replace", unit: "thm:rate/1/1", tex: "Assume that $\\alpha \\le \\beta$." }]), scope, "w");
    expect(m.problems).toEqual([]);
    expect(m.corrected_statement).toBe("Assume that $\\alpha \\le \\beta$.");
    expect(m.proof).toBeNull();
    // a unit outside its own text (the theorem's nuisance-rate hypothesis) is not its to replace
    const out = materializeRepair(ops([{ op: "replace", unit: "thm:rate/1/2", tex: "x" }]), scope, "w");
    expect(out.problems.join(" ")).toContain("is not a unit of this node's printed text");
  });
});

describe("supersedes: the hypotheses a replacement rewrites leave the node's wiring (definitions stay)", () => {
  // Theorem thm:rate's first sentence: the assumptions it cites, then its own condition $\alpha < \beta$.
  const cites = String.raw`Suppose that Assumption \ref{assump:exo}, \ref{assump:overlap}, \ref{assump:iid}, \ref{assump:f_homo}, \ref{assump:mvary} hold, `;
  const where = String.raw`where $\alpha$ and $\beta$ are defined in \cref{assump:f_homo} and \cref{assump:mvary} respectively.`;
  const rate = (tex: string): PatchFile =>
    ({
      key_results: ["thm:rate"],
      patches: [{ node: "thm:rate", corrected_statement: null, ops: ops([{ op: "replace", unit: "thm:rate/1/1", tex }]), proof_note: "The proof as printed proves the repaired statement; no step changes." }],
      unfixable: [],
    }) as unknown as PatchFile;

  it("the derived supersedes reaches the patch file, and the build unwires them from the node only", () => {
    const { src, core } = paper();
    const r = rederiveOn(rate(cites + String.raw`$\alpha \le \beta$, ` + where), src);
    expect(r.changed).toEqual([{ node: "thm:rate", applied: true, fields: ["corrected_statement", "supersedes"] }]);
    const p = r.file.patches[0]!;
    expect(p.supersedes).toEqual(["ass:rate-alpha-less-beta"]);
    expect(p.corrected_statement!.startsWith(cites + String.raw`$\alpha \le \beta$`)).toBe(true);
    const built = buildCore(core, { patches: r.file }).core;
    const printed = core.statements.find((s) => s.id === "thm:rate")!;
    const repaired = built.statements.find((s) => s.id === "thm:rate")!;
    // the cited assumptions stay wired: their text is their own environment's, not this unit's
    expect(repaired.depends_on).toEqual(printed.depends_on.filter((d) => d !== "ass:rate-alpha-less-beta"));
    expect(repaired.statement.startsWith(cites + String.raw`$\alpha \le \beta$`)).toBe(true);
    // the superseded assumption stays in the core while another result uses it; no node is added
    expect(built.statements.find((s) => s.id === "thm:cor-rate")!.depends_on).toContain("ass:rate-alpha-less-beta");
    expect(built.assumptions.map((a) => a.id).sort()).toEqual(core.assumptions.map((a) => a.id).sort());
    // re-deriving again is a no-op
    expect(rederiveOn(r.file, src).changed).toEqual([]);
  });
  it("a hypothesis the replacement keeps word for word stays wired", () => {
    const { src } = paper();
    const at = (cond: string): string[] | undefined => rederiveOn(rate(cites + cond + where), src).file.patches[0]!.supersedes;
    expect(at(String.raw`$\alpha < \beta$, `)).toBeUndefined();
    // the kept condition may be followed by another clause; a qualifier appended to it rewrites it
    expect(at(String.raw`$\alpha < \beta$, and let $n\to\infty$, `)).toBeUndefined();
    expect(at(String.raw`$\alpha < \beta$ for $t = 1$, `)).toEqual(["ass:rate-alpha-less-beta"]);
    expect(at(String.raw`$\alpha < \beta$ and $t = 1$, `)).toEqual(["ass:rate-alpha-less-beta"]);
  });
});

describe("an op's TeX never creates an equation number or label", () => {
  it("numbered displays become starred, labels dropped, unless the replaced unit carried the label", () => {
    expect(unnumberedTex("so \\begin{equation}\\label{A2} x=1 \\end{equation} and \\begin{align} y \\end{align}")).toBe("so \\begin{equation*} x=1 \\end{equation*} and \\begin{align*} y \\end{align*}");
    expect(unnumberedTex("\\begin{equation} x \\label{eq:k} \\end{equation}", new Set(["eq:k"]))).toBe("\\begin{equation} x \\label{eq:k} \\end{equation}");
  });
});

