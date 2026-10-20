import { describe, expect, it } from "vitest";
import { leanNameLeaf, leanSourceDeclarations } from "../src/presentation/lean_decl_name.js";

describe("leanNameLeaf", () => {
  it("splits a qualified name only at dots outside quotes", () => {
    expect(leanNameLeaf("Outer.«inner.with.dot»")).toBe("«inner.with.dot»");
  });
});

describe("anonymous instances carry Lean's auto-generated name", () => {
  it("names an instance from the constants of its result type, skipping binder variables", () => {
    const src = [
      "namespace M",
      "instance {n : ℕ} {G : Causalean.DAG (Fin n)} : TopologicalSpace (Mechanism n G) :=",
      "  TopologicalSpace.induced mechanismC2Coordinates inferInstance",
      "instance : Fintype (Fin n × Bool) := inferInstance",
      "noncomputable instance named : Inhabited ℝ := ⟨0⟩",
      "end M",
    ].join("\n");
    expect(leanSourceDeclarations(src).map((d) => [d.name, d.line, d.kind])).toEqual([
      ["instTopologicalSpaceMechanism", 2, "instance"],
      ["instFintypeProdFinBool", 4, "instance"],
      ["named", 5, "instance"],
    ]);
  });
});
