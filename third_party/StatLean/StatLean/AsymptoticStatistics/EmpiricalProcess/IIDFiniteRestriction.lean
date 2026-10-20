module
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-!
# Finite restrictions of iid samples

This module identifies the product law of the first `n` coordinates of an
infinite iid sample.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory

/-- The pushforward law of the first `n` coordinates of an iid sample with
common law `P` is the `n`-fold product measure `Pⁿ`.

The iid sequence `X` may be realized on any probability space `Ξ`; its finite
restriction has the canonical product law on `Fin n → Ω`. -/
theorem iidFiniteRestriction_map_eq_pi
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) (n : ℕ) :
    μ.map (fun ξ : Ξ => fun i : Fin n => X i.val ξ) =
      Measure.pi (fun _ : Fin n => P) := by
  have h_indep : ProbabilityTheory.iIndepFun (fun i : Fin n => X i.val) μ :=
    hX_indep.precomp Fin.val_injective
  have h_coord : ∀ i : Fin n, μ.map (X i.val) = P := by
    intro i
    rw [(hX_id i.val).map_eq]
    exact hX_law
  have h_aem : ∀ i : Fin n, AEMeasurable (fun ξ : Ξ => X i.val ξ) μ :=
    fun i => (hX_meas i.val).aemeasurable
  rw [(ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map h_aem).mp h_indep]
  congr 1
  funext i
  exact h_coord i

end AsymptoticStatistics.EmpiricalProcess
