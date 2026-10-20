module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.FiniteCarrier

@[expose] public section

/-!
# A constitutive bundle for a Donsker process

Two complementary predicates describe the book's notion of a `P`-Donsker
class: the operational Theorem-18.14 characterization
`IsPDonsker`, and the literal path-space convergence statement
`IsPDonskerWithBridge`. Theorem 19.23 needs both facets at once.

Reference: van der Vaart, *Asymptotic Statistics*, §19.2, p.269.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Constitutive Donsker process data.** This is one book-level Donsker
assumption represented by the two complementary predicates above. Edge
behavior: no nonemptiness or envelope assumption is
added; those remain requirements of particular construction theorems. -/
structure PDonskerProcessData (F : Set (Ω → ℝ)) (P : Measure Ω) : Prop where
  /-- Constitutive (vdV §19.2 p.269): the index class consists of measurable
  functions. -/
  measurable : ∀ f ∈ F, Measurable f
  /-- Constitutive (vdV §19.2 p.269 and Theorem 18.14): the operational
  finite-dimensional-CLT and asymptotic-equicontinuity facet. -/
  operational : IsPDonsker F P
  /-- Constitutive (vdV §19.2 p.269): the literal outer weak convergence of
  the full empirical-process path to a tight `P`-Brownian bridge. -/
  literal : IsPDonskerWithBridge F P

namespace PDonskerProcessData

/-- Every member of a constitutively bundled Donsker class lies in `L²(P)`.
This is derived from the operational marginal CLT and is not an additional
regularity hypothesis. -/
theorem memLp {F : Set (Ω → ℝ)} {P : Measure Ω}
    (h : PDonskerProcessData F P) {f : Ω → ℝ} (hf : f ∈ F) :
    MemLp f 2 P := by
  exact h.operational.marginalCLT.memLp f hf

end PDonskerProcessData

end AsymptoticStatistics.EmpiricalProcess
