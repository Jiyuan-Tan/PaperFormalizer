module
public import StatLean.AsymptoticStatistics.Core.NondominatedTangent
public import StatLean.AsymptoticStatistics.Core.PathwiseVec

@[expose] public section

/-! # Selected-path differentiability on nondominated tangent cones -/

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace AsymptoticStatistics.Core.NondominatedPathwise

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.NondominatedTangent

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (C : NondominatedTangentCone P)

/-- Scalar pathwise differentiability along each independently selected
one-sided QMD path.  The derivative lives on the closed linear span, while
the quotient is required only for carrier paths.

Constitutive (vdV §25.3 p.363): derivative plus right difference quotients;
regularity and the eventual derivative identity are not fields. -/
structure NondominatedPathwiseDifferentiableAt
    (ψ : Measure Ω → ℝ) where
  /-- Constitutive (vdV §25.3 p.363): continuous linear derivative on the
  closed tangent span. -/
  derivative : tangentSpace C →L[ℝ] ℝ
  /-- Constitutive (vdV §25.3 p.363): right quotient on every selected
  carrier path. -/
  derivative_spec : ∀ g : {g : ↥(L2ZeroMean P) // g ∈ C.carrier},
    Tendsto (fun t : ℝ => (ψ ((C.selectedPath g).curve t) - ψ P) / t)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (derivative ⟨g, selected_mem_tangentSpace C g⟩))

/-- Vector pathwise differentiability on the same selected paths.

Constitutive (vdV §25.3 p.363): vector derivative and selected right
quotients.  The definition includes `d=0` without special casing. -/
structure NondominatedPathwiseDifferentiableAtVec
    {d : ℕ} (ψ : Measure Ω → EuclideanSpace ℝ (Fin d)) where
  /-- Constitutive (vdV §25.3 p.363): vector continuous linear derivative. -/
  derivative : tangentSpace C →L[ℝ] EuclideanSpace ℝ (Fin d)
  /-- Constitutive (vdV §25.3 p.363): vector right quotient on every selected
  carrier path. -/
  derivative_spec : ∀ g : {g : ↥(L2ZeroMean P) // g ∈ C.carrier},
    Tendsto (fun t : ℝ =>
      t⁻¹ • (ψ ((C.selectedPath g).curve t) - ψ P))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (derivative ⟨g, selected_mem_tangentSpace C g⟩))

end AsymptoticStatistics.Core.NondominatedPathwise
