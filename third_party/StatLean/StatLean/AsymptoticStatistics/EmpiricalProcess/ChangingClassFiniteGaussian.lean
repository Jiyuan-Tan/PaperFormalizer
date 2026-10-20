module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ChangingClassCore

@[expose] public section

/-!
# Finite Gaussian projection laws for changing classes

This file constructs the finite-partition Gaussian approximants used in the
finite-dimensional-to-outer weak convergence step for van der Vaart Theorem
19.28.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open Filter MeasureTheory ProbabilityTheory

/-- The Gaussian finite-partition approximation on `LinfT T`.

Constitutive (vdV Theorem 18.14, as used in Theorem 19.28): this is the
finite-dimensional centered Gaussian law reconstructed as a path constant on
each cell. Edge behavior: if the finite covariance cut is not positive
semidefinite, Mathlib's `multivariateGaussian` is the Dirac mass at zero, so
this definition remains a probability measure without an extra hypothesis.
-/
noncomputable def finiteGaussianProjectionLaw {T : Type*}
    (C : T → T → ℝ) (a : FiniteApproximation T) : Measure (LinfT T) :=
  (multivariateGaussian 0 (finiteCovariance C a.rep)).map (finiteReconstruction a)

instance instIsProbabilityMeasureFiniteGaussianProjectionLaw {T : Type*}
    (C : T → T → ℝ) (a : FiniteApproximation T) :
    IsProbabilityMeasure (finiteGaussianProjectionLaw C a) := by
  unfold finiteGaussianProjectionLaw
  exact Measure.isProbabilityMeasure_map
    (finiteReconstruction a).continuous.measurable.aemeasurable

/-- A finite-partition Gaussian approximation is tight, with no countability
assumption on the target index type. Tightness is transported from the
finite-dimensional Euclidean Gaussian law through continuous reconstruction.
-/
theorem finiteGaussianProjectionLaw_isTightMeasureSet {T : Type*}
    (C : T → T → ℝ) (a : FiniteApproximation T) :
    IsTightMeasureSet
      ({finiteGaussianProjectionLaw C a} : Set (Measure (LinfT T))) := by
  have hsrc : IsTightMeasureSet
      ({multivariateGaussian 0 (finiteCovariance C a.rep)} :
        Set (Measure (EuclideanSpace ℝ (Fin a.k)))) :=
    isTightMeasureSet_singleton
  have himg := hsrc.map (finiteReconstruction a).continuous
  simpa [finiteGaussianProjectionLaw] using himg

/-- Finite-partition projections converge in distribution to their
reconstructed Gaussian laws.

This is the continuous mapping theorem applied to finite-dimensional
convergence, followed by identification of the limiting pushforward law.
-/
theorem finiteProjection_tendstoInDistribution
    {Ξ T : Type*} [MeasurableSpace Ξ]
    (μ : ℕ → Measure Ξ) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ℕ → Ξ → LinfT T) (C : T → T → ℝ)
    (hfdd : FDDConverges μ X C) (a : FiniteApproximation T) :
    TendstoInDistribution (fun n ξ => a.project (X n ξ)) atTop id μ
      (finiteGaussianProjectionLaw C a) := by
  have hcoord := hfdd a.rep
  have hmap := hcoord.continuous_comp (finiteReconstruction a).continuous
  refine
    { forall_aemeasurable := fun n => ?_
      aemeasurable_limit := measurable_id.aemeasurable
      tendsto := ?_ }
  · simpa [FiniteApproximation.project, Function.comp_def] using
      (finiteReconstruction a).continuous.measurable.comp_aemeasurable
        (hcoord.forall_aemeasurable n)
  · convert! hmap.tendsto using 1 with n
    congr 1
    apply Subtype.ext
    simp [finiteGaussianProjectionLaw]

end AsymptoticStatistics.EmpiricalProcess
