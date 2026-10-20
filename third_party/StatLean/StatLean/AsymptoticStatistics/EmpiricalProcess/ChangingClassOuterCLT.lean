module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ChangingClassFiniteGaussian
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterMapping

@[expose] public section

/-!
# Identification of changing-class outer weak limits

This file identifies every finite-coordinate law of an outer weak limit from
the ordinary finite-dimensional convergence supplied by `FDDConverges`.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open Filter MeasureTheory ProbabilityTheory

/-- For an almost-everywhere measurable sequence, outer weak convergence is
equivalent to ordinary weak convergence of its pushforward laws. The result
follows by choosing measurable versions and using invariance of both outer
expectation and `Measure.map` under a.e. equality.
-/
private theorem weakConvergesOuter_iff_of_forall_aemeasurable
    {Ω D : Type*} [MeasurableSpace Ω] [MeasurableSpace D]
    [PseudoMetricSpace D] [OpensMeasurableSpace D]
    {μ : ℕ → Measure Ω} {Y : ℕ → Ω → D} {ν : Measure D}
    [∀ n, IsProbabilityMeasure (μ n)]
    (hY : ∀ n, AEMeasurable (Y n) (μ n)) :
    WeakConvergesOuter μ Y ν ↔
      WeakConverges (fun n => (μ n).map (Y n)) ν := by
  let Ym : ℕ → Ω → D := fun n => (hY n).mk (Y n)
  have hYm_meas : ∀ n, Measurable (Ym n) := fun n => (hY n).measurable_mk
  have hreadout : ∀ (f : BoundedContinuousFunction D ℝ) n,
      outerExpectation (μ n)
          (fun ω => ENNReal.ofReal (f (Y n ω) + ‖f‖)) =
        outerExpectation (μ n)
          (fun ω => ENNReal.ofReal (f (Ym n ω) + ‖f‖)) := by
    intro f n
    exact outerExpectation_congr_ae
      ((hY n).ae_eq_mk.fun_comp fun y => ENNReal.ofReal (f y + ‖f‖))
  have hmap : ∀ n, (μ n).map (Y n) = (μ n).map (Ym n) := fun n =>
    Measure.map_congr (hY n).ae_eq_mk
  rw [show WeakConvergesOuter μ Y ν ↔ WeakConvergesOuter μ Ym ν by
    constructor <;> intro h f
    · simpa only [hreadout] using h f
    · simpa only [hreadout] using h f]
  rw [weakConvergesOuter_of_measurable hYm_meas]
  constructor <;> intro h f
  · simpa only [hmap] using h f
  · simpa only [hmap] using h f

/-- The finite-coordinate law of any outer weak limit is the Gaussian law
specified by the finite-dimensional convergence hypothesis. -/
theorem finiteProjectionLaw_eq_of_fdd_weakConvergesOuter
    {Ξ T : Type*} [MeasurableSpace Ξ]
    (μ : ℕ → Measure Ξ) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ℕ → Ξ → LinfT T) (C : T → T → ℝ)
    (ν : Measure (LinfT T)) [IsProbabilityMeasure ν]
    (hfdd : FDDConverges μ X C) (hweak : WeakConvergesOuter μ X ν)
    {k : ℕ} (t : Fin k → T) :
    ν.map (finiteCoordinateProjection t) =
      multivariateGaussian 0 (finiteCovariance C t) := by
  let p := finiteCoordinateProjection t
  let Y : ℕ → Ξ → EuclideanSpace ℝ (Fin k) := fun n ξ => p (X n ξ)
  have htid : TendstoInDistribution Y atTop id μ
      (multivariateGaussian 0 (finiteCovariance C t)) := by
    simpa [Y, p] using hfdd t
  have houter : WeakConvergesOuter μ Y (ν.map p) := by
    simpa [Y, Function.comp_def] using hweak.continuous_comp p.continuous
  have houterWeak : WeakConverges (fun n => (μ n).map (Y n)) (ν.map p) :=
    (weakConvergesOuter_iff_of_forall_aemeasurable
      htid.forall_aemeasurable).mp houter
  have htidWeak : WeakConverges (fun n => (μ n).map (Y n))
      (multivariateGaussian 0 (finiteCovariance C t)) := by
    intro f
    have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      htid.tendsto) f
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using h
  letI : IsFiniteMeasure (ν.map p) := Measure.isFiniteMeasure_map ν p
  exact WeakConverges.unique houterWeak htidWeak

/-- Probability, singleton tightness, outer weak convergence, and FDD
convergence identify a centered tight Gaussian limit law. -/
theorem tightCenteredGaussianLaw_of_fdd_weakConvergesOuter
    {Ξ T : Type*} [MeasurableSpace Ξ]
    (μ : ℕ → Measure Ξ) [∀ n, IsProbabilityMeasure (μ n)]
    (X : ℕ → Ξ → LinfT T) (C : T → T → ℝ)
    (ν : Measure (LinfT T))
    (hfdd : FDDConverges μ X C)
    (hνprob : IsProbabilityMeasure ν)
    (hνtight : IsTightMeasureSet ({ν} : Set (Measure (LinfT T))))
    (hweak : WeakConvergesOuter μ X ν) :
    TightCenteredGaussianLaw C ν := by
  letI : IsProbabilityMeasure ν := hνprob
  exact
    { prob := hνprob
      tight := hνtight
      finiteLaw := fun t =>
        finiteProjectionLaw_eq_of_fdd_weakConvergesOuter μ X C ν hfdd hweak t }

end AsymptoticStatistics.EmpiricalProcess
