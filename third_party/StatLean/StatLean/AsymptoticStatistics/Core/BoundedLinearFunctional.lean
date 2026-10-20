module
public import StatLean.AsymptoticStatistics.Core.LinearFunctional
public import Mathlib.Probability.StrongLaw

@[expose] public section

/-!
# Globally bounded extensions of linear mean functionals

This file provides the theorem-agnostic bounded-extension layer used when a
statistical functional is identified only on a model class but pathwise
differentiability quantifies over unrestricted QMD paths.  The extension is made
globally bounded before applying the mass-method theorem from
`Core/LinearFunctional`.

The radius is `C + 1`, rather than `C`, because Mathlib's `truncation f A` uses
the half-open interval `(-A, A]`.  Since `C < C + 1`, this radius preserves every
value satisfying the closed bound `|f| ≤ C`, while Mathlib's global estimate
bounds the clipped function by `|C + 1|`.  Edge behavior: for negative `C` the
same literal radius `C + 1` is used.
-/

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
open AsymptoticStatistics.Core
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise

namespace AsymptoticStatistics.Core.MassMethod

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- A globally bounded extension of `a`, obtained by Mathlib truncation at
radius `C + 1`.

This agrees with `a` wherever `|a| ≤ C` and is globally bounded by
`|C + 1|`.  Edge behavior for `C < 0`: the literal radius `C + 1` is retained. -/
noncomputable def clippedFunction (a : Ω → ℝ) (C : ℝ) : Ω → ℝ :=
  truncation a (C + 1)

/-- The mean functional of the globally clipped extension.

Edge behavior for `C < 0` is inherited from `clippedFunction`. -/
noncomputable def clippedMeanFunctional (a : Ω → ℝ) (C : ℝ) : Measure Ω → ℝ :=
  meanFunctional (clippedFunction a C)

/-- Measurability of the globally clipped extension. -/
theorem measurable_clippedFunction {a : Ω → ℝ} {C : ℝ}
    (ha : Measurable a) : Measurable (clippedFunction a C) := by
  unfold clippedFunction truncation
  exact (measurable_id.indicator measurableSet_Ioc).comp ha

omit [MeasurableSpace Ω] in
/-- The clipped extension is globally bounded by `|C + 1|`. -/
theorem abs_clippedFunction_le {a : Ω → ℝ} {C : ℝ}
    (ω : Ω) : |clippedFunction a C ω| ≤ |C + 1| := by
  unfold clippedFunction
  exact abs_truncation_le_bound a (C + 1) ω

omit [MeasurableSpace Ω] in
/-- Clipping preserves every point satisfying `|a| ≤ C`. -/
theorem clippedFunction_eq_self_of_abs_le {a : Ω → ℝ} {C : ℝ}
    {ω : Ω} (hω : |a ω| ≤ C) :
    clippedFunction a C ω = a ω := by
  unfold clippedFunction
  have hC_lt : C < C + 1 := by linarith
  exact truncation_eq_self (lt_of_le_of_lt hω hC_lt)

/-- A measurable function bounded by `C` almost everywhere is in `L²(P)`.
This transport lemma is useful when the model law sees only the region on
which the unclipped and clipped integrands agree. -/
theorem memLp_two_of_ae_bounded {a : Ω → ℝ} {C : ℝ}
    (ha : Measurable a) (ha_bdd : ∀ᵐ ω ∂P, |a ω| ≤ C) : MemLp a 2 P := by
  refine MemLp.of_bound ha.aestronglyMeasurable C ?_
  filter_upwards [ha_bdd] with ω hω
  simpa only [Real.norm_eq_abs] using hω

/-- The clipped mean functional has the mass-method TV-Fréchet expansion. -/
theorem clippedMeanFunctional_isTVFrechetExpansion {a : Ω → ℝ} {C : ℝ}
    (ha : Measurable a) :
    IsTVFrechetExpansion P (clippedMeanFunctional a C) (clippedFunction a C) := by
  exact meanFunctional_isTVFrechetExpansion (measurable_clippedFunction ha)
    ⟨|C + 1|, fun ω ↦ abs_clippedFunction_le ω⟩

/-- The clipped mean functional is pathwise differentiable over any supplied
tangent submodule, with derivative represented by the centered clipped
integrand. -/
noncomputable def clippedMeanFunctional_pathwise {a : Ω → ℝ} (C : ℝ)
    (ha : Measurable a)
    (T : Submodule ℝ ↥(L2ZeroMean P)) :
    PathwiseDifferentiableAt P T (clippedMeanFunctional a C) := by
  let hf : MemLp (clippedFunction a C) 2 P :=
    memLp_two_of_bounded (measurable_clippedFunction ha)
      ⟨|C + 1|, fun ω ↦ abs_clippedFunction_le ω⟩
  let hfull := pathwiseDifferentiableAt_of_TVFrechet hf
    (clippedMeanFunctional_isTVFrechetExpansion ha)
  exact
    { derivative :=
        (innerSL ℝ ((centeredCandidate (P := P) (clippedFunction a C) hf).toL2ZeroMean)).comp
          (Submodule.subtypeL T)
      derivative_spec := fun γ _ ↦ hfull.derivative_spec γ Submodule.mem_top }

omit [IsProbabilityMeasure P] in
/-- Under a `P`-a.e. closed bound, the clipped extension and the raw mean
functional agree at `P`. -/
theorem clippedMeanFunctional_eq_meanFunctional {a : Ω → ℝ} {C : ℝ}
    (ha_bdd : ∀ᵐ ω ∂P, |a ω| ≤ C) :
    clippedMeanFunctional a C P = meanFunctional a P := by
  unfold clippedMeanFunctional meanFunctional
  apply integral_congr_ae
  filter_upwards [ha_bdd] with ω hω
  exact clippedFunction_eq_self_of_abs_le hω

/-- Under a `P`-a.e. closed bound, the centered candidate of the clipped
extension agrees `P`-a.e. with the raw centered integrand, relating the
globally controlled derivative to the in-model influence-function calculation. -/
theorem centeredCandidate_clipped_ae_eq_raw_centered {a : Ω → ℝ} {C : ℝ}
    (ha : Measurable a) (ha_bdd : ∀ᵐ ω ∂P, |a ω| ≤ C) :
    (((centeredCandidate (P := P) (clippedFunction a C)
        (memLp_two_of_bounded (measurable_clippedFunction ha)
          ⟨|C + 1|, fun ω ↦ abs_clippedFunction_le ω⟩)).toL2ZeroMean :
          Lp ℝ 2 P) : Ω → ℝ)
      =ᵐ[P] fun ω ↦ a ω - meanFunctional a P := by
  have hcoe := AsymptoticStatistics.Core.CandidateIF.coeFn_toL2ZeroMean
    (centeredCandidate (P := P) (clippedFunction a C)
      (memLp_two_of_bounded (measurable_clippedFunction ha)
        ⟨|C + 1|, fun ω ↦ abs_clippedFunction_le ω⟩))
  filter_upwards [hcoe, ha_bdd] with ω hcoeω hω
  rw [hcoeω]
  change clippedFunction a C ω - clippedMeanFunctional a C P =
    a ω - meanFunctional a P
  rw [clippedFunction_eq_self_of_abs_le hω,
    clippedMeanFunctional_eq_meanFunctional ha_bdd]

end AsymptoticStatistics.Core.MassMethod
