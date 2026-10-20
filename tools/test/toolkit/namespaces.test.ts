// The toolkit's naming and import conventions, and the study apply that enforces them.
import { mkdir, mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, describe, expect, it } from "vitest";
import { applyEdits, type Proposal } from "../../src/proposals/schema.js";
import { applyManifest, realApplyDeps } from "../../src/substrate/coordinate.js";
import { declarationSpans } from "../../src/toolkit/lean_source.js";
import { inNamespace, renamespace, topicNamespaceOfPath, trimmedImportSets, withImportBlock } from "../../src/toolkit/namespaces.js";
import { rewriteReferences } from "../../src/proposals/move.js";
import { leanModule, writeSkeleton } from "./helpers.js";

const tmp: string[] = [];
afterEach(async () => {
  for (const d of tmp.splice(0)) await rm(d, { recursive: true, force: true });
});

describe("toolkit conventions", () => {
  it("a declaration's name lives in its module's topic namespace; an accepted proposal's name is put there", () => {
    const ns = topicNamespaceOfPath("Toolkit/Foundations/Probability/Independence/Exchangeability.lean");
    expect(ns).toBe("Toolkit.Foundations.Probability.Independence");
    expect(inNamespace("IndepFun.cond_preimage", ns)).toBe("Toolkit.Foundations.Probability.Independence.cond_preimage");
    expect(inNamespace("Toolkit.Foundations.Probability.Independence.x", ns)).toBe("Toolkit.Foundations.Probability.Independence.x");
    const p = { proposed_name: "cond_preimage", target_module: "Toolkit/Foundations/Probability/Conditioning.lean" } as Proposal;
    expect(applyEdits(p, { kind: "accept" }).proposed_name).toBe("Toolkit.Foundations.Probability.cond_preimage");
  });

  it("trims an import block to the modules used (with the common tactics as the fallback for Mathlib.Tactic)", () => {
    const text = leanModule({ imports: ["Mathlib.Tactic", "Mathlib.Data.Real.Basic"], body: "theorem t : True := trivial" });
    const sets = trimmedImportSets(text, ["Mathlib.Order.Basic"]);
    expect(sets).toEqual([["Mathlib.Order.Basic"], ["Mathlib.Order.Basic", "Mathlib.Tactic.Common"]]);
    const out = withImportBlock(text, sets[0]!);
    expect(out).toContain("module\n\npublic import Mathlib.Order.Basic\n\n/-!");
  });

  it("moving declarations into their topic namespace keeps `omit … in`, never doubles a name, and follows them elsewhere", () => {
    // A module one namespace too high, using a sibling namespace by short names (the shape of the
    // first live gardening run's Exchangeability module).
    const mod = "Toolkit.Foundations.Probability.Independence.Exchangeability";
    const text = [
      "namespace Toolkit.Foundations.Probability",
      "open Toolkit.Foundations.Design",
      "variable {U : Type*} [DecidableEq U] [Fintype U]",
      "",
      "def Exch (n : Nat) : Prop := counts n = n",
      "",
      "omit [DecidableEq U]",
      "  [Fintype U] in",
      "/-- Only the counts. -/",
      "theorem exch_iff (n : Nat) : Exch n ↔ counts n = n := Iff.rfl",
      "",
      "end Toolkit.Foundations.Probability",
    ].join("\n");
    const spans = declarationSpans(text);
    expect(text.slice(spans[1]!.from, spans[1]!.to)).toMatch(/^omit \[DecidableEq U\]\n  \[Fintype U\] in\n\/-- Only the counts/);
    const r = renamespace(text, mod, () => true);
    const renames = r.renames;
    expect([...renames.values()]).toEqual(["Toolkit.Foundations.Probability.Independence.Exch", "Toolkit.Foundations.Probability.Independence.exch_iff"]);
    // The study apply rewrites every file it writes, the moved module included.
    const own = rewriteReferences(r.text, renames).text;
    expect(own).toContain("omit [DecidableEq U]\n  [Fintype U] in\n/-- Only the counts. -/\ntheorem exch_iff (n : Nat) : Exch n ↔ counts n = n");
    expect(own).not.toMatch(/theorem Toolkit\.|def Toolkit\./);
    expect(declarationSpans(own).map((s) => s.name)).toEqual(["Toolkit.Foundations.Probability.Independence.Exch", "Toolkit.Foundations.Probability.Independence.exch_iff"]);
    // Elsewhere: the renamed declarations follow, an unrenamed one of the old namespace stays.
    const paper = "theorem t : Toolkit.Foundations.Probability.Exch 0 := Toolkit.Foundations.Probability.cond_preimage";
    expect(rewriteReferences(paper, renames).text).toBe("theorem t : Toolkit.Foundations.Probability.Independence.Exch 0 := Toolkit.Foundations.Probability.cond_preimage");
  });

  it("a doc comment with a blank line inside belongs to its declaration's span", () => {
    const text = "/-- First.\n\nSecond. -/\ntheorem a : True := trivial\n";
    expect(declarationSpans(text)[0]!.from).toBe(0);
  });

  it("a study's new module declares in its topic namespace and imports only what it uses (kept when it builds)", async () => {
    const root = await mkdtemp(path.join(os.tmpdir(), "conv-"));
    tmp.push(root);
    const cfg = await writeSkeleton(root);
    await writeFile(path.join(root, "lakefile.toml"), 'name = "t"\n\n[[lean_lib]]\nname = "Toolkit"\n\n[[lean_exe]]\nname = "candidate_scan"\nroot = "CandidateScan"\n');
    const staging = path.join(root, "staging");
    await mkdir(staging, { recursive: true });
    const body = "namespace IndepFun\n\n/-- Independence survives conditioning. -/\ntheorem cond_preimage : True := trivial\n\nend IndepFun";
    await writeFile(path.join(staging, "c.lean"), leanModule({ imports: ["Mathlib.Tactic"], doc: "Conditioning", body }));
    const module = "Toolkit.Foundations.Probability.Conditioning";
    const runs: string[] = [];
    const run = async (cmd: string) => {
      runs.push(cmd);
      const out = /--out '?([^'\s]+)'?/.exec(cmd)?.[1];
      if (out) {
        await mkdir(path.dirname(out), { recursive: true });
        await writeFile(out, JSON.stringify({ declarations: [{ module, type_constants: [{ module: "Mathlib.Probability.Independence.Basic" }], body_constants: [{ module: "Init.Core" }] }] }));
      }
      const probe = /lake env lean '?([^'\s]+)'?/.exec(cmd)?.[1];
      if (probe) {
        const names = [...(await readFile(probe, "utf8")).matchAll(/#print axioms (\S+)/g)].map((m) => m[1]);
        return { code: 0, log: names.map((n) => `'${n}' depends on axioms: [propext]`).join("\n") };
      }
      return { code: 0, log: "ok" };
    };
    const r = await applyManifest({
      toolkit: cfg, toolsDir: "/tools", stagingDir: staging, leanFiles: [], slug: "s", modulePrefix: "Toolkit.Staging.S", indexStep: null,
      manifest: { ops: [{ kind: "create_file", target: "Toolkit/Foundations/Probability/Conditioning.lean", from: "c.lean", newModule: module }], notes: "" },
    }, { ...realApplyDeps, run });
    expect(r.ok).toBe(true);
    const text = await readFile(path.join(root, "Toolkit/Foundations/Probability/Conditioning.lean"), "utf8");
    expect(text).toContain("namespace Toolkit.Foundations.Probability\n");
    expect(text).not.toContain("namespace IndepFun");
    expect(text).toContain("public import Mathlib.Probability.Independence.Basic\n");
    expect(text).not.toContain("Mathlib.Tactic");
    expect(r.log).toContain("header trimmed to 1 import(s)");
    const ledger = JSON.parse(await readFile(cfg.ledgerPath, "utf8")) as { declarations: Array<{ name: string }> };
    expect(ledger.declarations.map((d) => d.name)).toEqual(["Toolkit.Foundations.Probability.cond_preimage"]);
  });
});
