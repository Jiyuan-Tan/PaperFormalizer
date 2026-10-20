module
public import StatLean.AsymptoticStatistics.Core.NondominatedQMDPath
public import StatLean.AsymptoticStatistics.Core.TangentAbstract

@[expose] public section

/-! # Nondominated one-sided tangent cones -/

open MeasureTheory
open scoped InnerProductSpace

namespace AsymptoticStatistics.Core.NondominatedTangent

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.NondominatedQMDPath

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- A genuine one-sided tangent cone with an independently selected
nondominated QMD realization of every carrier score.

Constitutive (vdV §25.3 pp.362--363): the carrier is nonempty and closed
under nonnegative scaling; each member is a score realized by a one-sided
QMD path. Addition and negation are intentionally absent. The zero cone and
moving-atom paths show that these conditions are non-vacuous and do not imply
common domination. -/
structure NondominatedTangentCone
    (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- Constitutive (vdV §25.3 p.362): the admissible score set. -/
  carrier : Set ↥(L2ZeroMean P)
  /-- Constitutive (vdV §25.3 p.363): a tangent cone contains at least one
  score; zero is subsequently derived. -/
  carrier_nonempty : carrier.Nonempty
  /-- Constitutive (vdV §25.3 p.363): closure under nonnegative scaling. -/
  nonneg_smul_mem : ∀ {a : ℝ}, 0 ≤ a → ∀ {g}, g ∈ carrier → a • g ∈ carrier
  /-- Constitutive (vdV §25.3 pp.362--363): an independently chosen realizing
  one-sided QMD submodel for each carrier score. -/
  selectedPath : {g : ↥(L2ZeroMean P) // g ∈ carrier} → NondominatedQMDPath P
  /-- Constitutive (vdV §25.3 p.362): the realizing path has the requested
  score, rather than merely some score in the carrier. -/
  selectedPath_score : ∀ g, (selectedPath g).score = (g : ↥(L2ZeroMean P))

/-- Zero belongs to every nonempty nonnegative cone: select any carrier point
and scale it by zero. -/
theorem zero_mem (C : NondominatedTangentCone P) :
    (0 : ↥(L2ZeroMean P)) ∈ C.carrier := by
  obtain ⟨g, hg⟩ := C.carrier_nonempty
  simpa using C.nonneg_smul_mem (a := 0) le_rfl hg

/-- Closed linear span of the nondominated tangent cone.  Edge behavior:
for the zero cone this is bottom. -/
noncomputable def tangentSpace
    (C : NondominatedTangentCone P) : Submodule ℝ ↥(L2ZeroMean P) :=
  (Submodule.span ℝ C.carrier).topologicalClosure

/-- Each selected carrier score belongs to the derived tangent space, by
inclusion in the span and then its closure. -/
theorem selected_mem_tangentSpace
    (C : NondominatedTangentCone P)
    (g : {g : ↥(L2ZeroMean P) // g ∈ C.carrier}) :
    (g : ↥(L2ZeroMean P)) ∈ tangentSpace C := by
  exact (Submodule.span ℝ C.carrier).le_topologicalClosure
    (Submodule.subset_span g.property)

end AsymptoticStatistics.Core.NondominatedTangent
