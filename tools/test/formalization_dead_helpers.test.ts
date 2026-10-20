import { mkdir, mkdtemp, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { describe, expect, it } from "vitest";
import { sweepDeadHelpers } from "../src/formalization/dead_helpers.js";

/** F4 dead-helper sweep: flags public decls nothing consumes; spares graph-node realizations,
 *  attributed/instance decls, `-- keep:` justified helpers, tmp/ probes, and commented mentions. */
describe("sweepDeadHelpers", () => {
  it("flags the dead helper and spares consumed, exempt, attributed, and kept decls", async () => {
    const dir = await mkdtemp(path.join(tmpdir(), "dead-helpers-"));
    try {
      await mkdir(path.join(dir, "Helpers"));
      await mkdir(path.join(dir, "tmp"));
      await writeFile(
        path.join(dir, "Helpers", "Envelope.lean"),
        `/-- An abandoned-route helper: nothing references it. -/
lemma coeff_envelope : True := by trivial

lemma consumed_bound : True := by trivial

-- keep: substrate for the follow-on one-arm run (2026-08-25)
lemma kept_substrate : True := by trivial

@[simp] lemma simp_fact : True := by trivial

instance : Inhabited Unit := ⟨()⟩

private lemma local_step : True := by trivial
`,
      );
      await writeFile(
        path.join(dir, "Main.lean"),
        `-- coeff_envelope is only mentioned in this comment, which is not a use.
theorem headline : True := by
  have h := consumed_bound
  trivial
`,
      );
      await writeFile(
        path.join(dir, "tmp", "Probe.lean"),
        "lemma disposable_probe : True := by trivial\n",
      );

      const dead = await sweepDeadHelpers(
        dir,
        new Set(["CausalSmith.Stat.X_Research.headline"]), // graph node ⇒ headline exempt by short name
      );
      expect(dead).toEqual([
        { decl: "coeff_envelope", file: "Helpers/Envelope.lean", line: 2 },
      ]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("spares a decl that realizes a symbol (its @realizes tag anywhere in its own text), and only that decl (live Athey–Imbens, 2026-10-01)", async () => {
    const dir = await mkdtemp(path.join(tmpdir(), "dead-helpers-"));
    try {
      await writeFile(
        path.join(dir, "Basic.lean"),
        `/-- Every randomization variance is nonnegative. -/
lemma variance_nonneg : True := by -- @realizes V(nonnegative scalar variance)
  trivial

noncomputable def S2cross : Nat :=
  0
  -- @realizes S^2_{aa'}(unsquared printed cross quantity)

lemma truly_dead : True := by trivial
`,
      );
      expect(await sweepDeadHelpers(dir, new Set())).toEqual([{ decl: "truly_dead", file: "Basic.lean", line: 9 }]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("spares a decl whose own docstring carries @realizes (the crosswalk reads it there), and not the next decl (live cns: two Δ-nonnegativity realizers pruned)", async () => {
    const dir = await mkdtemp(path.join(tmpdir(), "dead-helpers-doc-"));
    try {
      await writeFile(
        path.join(dir, "Delta.lean"),
        `/-- @realizes \\Delta(formula is nonnegative on its standing domain) -/
lemma delta_nonneg : True := by trivial

lemma truly_dead : True := by trivial
`,
      );
      expect(await sweepDeadHelpers(dir, new Set())).toEqual([{ decl: "truly_dead", file: "Delta.lean", line: 4 }]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it("binds a keep marker to exactly the NEXT decl, across a long docstring, leaking to none after", async () => {
    // Audited 2026-08-25: a fixed 3-line lookback let one marker exempt up to three following
    // decls, and failed to exempt a decl behind its own multi-line docstring. Adjacency binding
    // fixes both directions.
    const dir = await mkdtemp(path.join(tmpdir(), "dead-helpers-keep-"));
    try {
      await writeFile(
        path.join(dir, "Keeps.lean"),
        `-- keep: reused by the sibling run
/-- A docstring
spanning three
whole lines. -/
lemma kept_but_documented : True := by trivial

lemma dead_two : True := by trivial
lemma dead_three : True := by trivial
`,
      );
      const dead = await sweepDeadHelpers(dir, new Set());
      expect(dead.map((d) => d.decl).sort()).toEqual(["dead_three", "dead_two"]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });

  it.each([
    ["@[expose] public section"],
    ["@[expose] public noncomputable section"],
  ])("flags a bare helper published by `%s`", async (header) => {
    const dir = await mkdtemp(path.join(tmpdir(), "dead-helpers-module-"));
    try {
      await writeFile(path.join(dir, "Helpers.lean"), [
        "module",
        header,
        "lemma dead_module_helper : True := by trivial",
        "lemma second_module_helper : True := by trivial",
        "theorem module_headline : True := by trivial",
      ].join("\n"));
      const dead = await sweepDeadHelpers(dir, new Set(["module_headline", "second_module_helper"]));
      expect(dead).toEqual([{ decl: "dead_module_helper", file: "Helpers.lean", line: 3 }]);
    } finally {
      await rm(dir, { recursive: true, force: true });
    }
  });
});
