module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalDistribution
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterFiniteProduct

@[expose] public section

/-!
# Kolmogorov–Smirnov and Cramér–von Mises functionals

The continuous-mapping part of van der Vaart Corollary 19.21 (book
pp.277–278).  Both statistics are obtained jointly from the genuine
`LinfF halfLineIndicatorClass` empirical-process limit.

The Cramér–von Mises functional is defined by upper integration.  A general
`LinfF` path need not be measurable as a function of its threshold, so a
Bochner integral would have the wrong `integral_undef = 0` fallback.  Ordinary
integration is recovered only for the measurable empirical paths below.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

/-- Kolmogorov–Smirnov functional `z ↦ ‖z‖∞` (vdV 19.21, p.277).

Edge behavior: the zero path, including the empirical path at `n = 0`, maps
to zero. -/
noncomputable def ksFunctional
    (z : LinfF halfLineIndicatorClass) : ℝ :=
  ‖z‖

/-- Cramér–von Mises functional `z ↦ ∫* z(t)² dP(t)` (vdV 19.21,
p.277), encoded by outer expectation and then converted to its finite real
value.

Edge behavior: this is defined for every bounded path, including paths whose
threshold parametrization is nonmeasurable.  It never uses the Bochner
integral's nonmeasurable-function fallback. -/
noncomputable def cvmFunctional (P : Measure ℝ) [IsProbabilityMeasure P]
    (z : LinfF halfLineIndicatorClass) : ℝ :=
  (outerExpectation P fun t =>
    ENNReal.ofReal ((z (halfLineIndex t)) ^ 2)).toReal

/-- Joint KS/CvM readout used for the single continuous-mapping step.

Edge behavior: both coordinates vanish on the zero path. -/
noncomputable def gofFunctional (P : Measure ℝ) [IsProbabilityMeasure P]
    (z : LinfF halfLineIndicatorClass) : ℝ × ℝ :=
  (ksFunctional z, cvmFunctional P z)

/-- The KS functional is continuous for the uniform norm. -/
theorem continuous_ksFunctional : Continuous ksFunctional := by
  exact continuous_norm

private theorem cvmOuter_ne_top (P : Measure ℝ) [IsProbabilityMeasure P]
    (z : LinfF halfLineIndicatorClass) :
    outerExpectation P (fun t =>
      ENNReal.ofReal ((z (halfLineIndex t)) ^ 2)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
  calc
    outerExpectation P (fun t => ENNReal.ofReal ((z (halfLineIndex t)) ^ 2))
        ≤ outerExpectation P (fun _ => ENNReal.ofReal (‖z‖ ^ 2)) := by
          apply outerExpectation_mono
          intro t
          apply ENNReal.ofReal_le_ofReal
          have hz : |z (halfLineIndex t)| ≤ ‖z‖ := by
            simpa [Real.norm_eq_abs] using
              lp.norm_apply_le_norm ENNReal.top_ne_zero z (halfLineIndex t)
          simpa [sq_abs] using
            (sq_le_sq₀ (abs_nonneg (z (halfLineIndex t))) (norm_nonneg z)).2 hz
    _ = ENNReal.ofReal (‖z‖ ^ 2) := by
      rw [outerExpectation_const]
      simp

private theorem square_eval_le_add
    (z w : LinfF halfLineIndicatorClass) (t : ℝ) :
    (z (halfLineIndex t)) ^ 2 ≤ (w (halfLineIndex t)) ^ 2 +
      ‖z - w‖ * (‖z‖ + ‖w‖) := by
  let x := z (halfLineIndex t)
  let y := w (halfLineIndex t)
  have hxy : |x - y| ≤ ‖z - w‖ := by
    simpa only [x, y, Real.norm_eq_abs, lp.coeFn_sub] using!
      lp.norm_apply_le_norm ENNReal.top_ne_zero (z - w) (halfLineIndex t)
  have hx : |x| ≤ ‖z‖ := by
    simpa only [x, Real.norm_eq_abs] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero z (halfLineIndex t)
  have hy : |y| ≤ ‖w‖ := by
    simpa only [y, Real.norm_eq_abs] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero w (halfLineIndex t)
  calc
    x ^ 2 ≤ y ^ 2 + |x ^ 2 - y ^ 2| := by
      linarith [le_abs_self (x ^ 2 - y ^ 2)]
    _ = y ^ 2 + |x - y| * |x + y| := by
      congr 1
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ y ^ 2 + |x - y| * (|x| + |y|) := by
      gcongr
      exact abs_add_le x y
    _ ≤ y ^ 2 + ‖z - w‖ * (‖z‖ + ‖w‖) := by
      gcongr

private theorem cvmFunctional_le_add (P : Measure ℝ) [IsProbabilityMeasure P]
    (z w : LinfF halfLineIndicatorClass) :
    cvmFunctional P z ≤ cvmFunctional P w + ‖z - w‖ * (‖z‖ + ‖w‖) := by
  let C := ‖z - w‖ * (‖z‖ + ‖w‖)
  have hC : 0 ≤ C := mul_nonneg (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have houter :
      outerExpectation P (fun t => ENNReal.ofReal ((z (halfLineIndex t)) ^ 2)) ≤
        outerExpectation P (fun t => ENNReal.ofReal ((w (halfLineIndex t)) ^ 2)) +
          ENNReal.ofReal C := by
    calc
      outerExpectation P (fun t => ENNReal.ofReal ((z (halfLineIndex t)) ^ 2))
          ≤ outerExpectation P (fun t =>
              ENNReal.ofReal ((w (halfLineIndex t)) ^ 2) + ENNReal.ofReal C) := by
            apply outerExpectation_mono
            intro t
            change ENNReal.ofReal ((z (halfLineIndex t)) ^ 2) ≤
              ENNReal.ofReal ((w (halfLineIndex t)) ^ 2) + ENNReal.ofReal C
            rw [← ENNReal.ofReal_add (sq_nonneg _) hC]
            exact ENNReal.ofReal_le_ofReal (square_eval_le_add z w t)
      _ = outerExpectation P (fun t =>
            ENNReal.ofReal ((w (halfLineIndex t)) ^ 2)) + ENNReal.ofReal C := by
          rw [outerExpectation_add_const _ _ ENNReal.ofReal_ne_top]
          simp
  have hright :
      outerExpectation P (fun t => ENNReal.ofReal ((w (halfLineIndex t)) ^ 2)) +
        ENNReal.ofReal C ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨cvmOuter_ne_top P w, ENNReal.ofReal_ne_top⟩
  have hreal := ENNReal.toReal_mono hright houter
  rw [ENNReal.toReal_add (cvmOuter_ne_top P w) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hC] at hreal
  simpa only [cvmFunctional, C] using hreal

private theorem dist_cvmFunctional_le (P : Measure ℝ) [IsProbabilityMeasure P]
    (z w : LinfF halfLineIndicatorClass) :
    dist (cvmFunctional P z) (cvmFunctional P w) ≤
      ‖z - w‖ * (‖z‖ + ‖w‖) := by
  rw [Real.dist_eq, abs_le]
  constructor
  · have h := cvmFunctional_le_add P w z
    rw [norm_sub_rev, add_comm] at h
    linarith
  · have h := cvmFunctional_le_add P z w
    linarith

/-- The upper-integral CvM functional is continuous for the uniform norm. -/
theorem continuous_cvmFunctional (P : Measure ℝ) [IsProbabilityMeasure P] :
    Continuous (cvmFunctional P) := by
  rw [continuous_iff_continuousAt]
  intro z
  rw [Metric.continuousAt_iff]
  intro ε hε
  let B := 2 * ‖z‖ + 1
  have hB : 0 < B := by positivity
  refine ⟨min 1 (ε / B), lt_min (by norm_num) (div_pos hε hB), ?_⟩
  intro w hw
  have hw_one : dist w z < 1 := hw.trans_le (min_le_left _ _)
  have hw_div : dist w z < ε / B := hw.trans_le (min_le_right _ _)
  have hw_norm : ‖w‖ + ‖z‖ ≤ B := by
    have htriangle := norm_le_norm_add_norm_sub z w
    rw [norm_sub_rev, ← dist_eq_norm] at htriangle
    dsimp only [B]
    linarith
  calc
    dist (cvmFunctional P w) (cvmFunctional P z)
        ≤ ‖w - z‖ * (‖w‖ + ‖z‖) := dist_cvmFunctional_le P w z
    _ = dist w z * (‖w‖ + ‖z‖) := by rw [dist_eq_norm]
    _ ≤ dist w z * B := mul_le_mul_of_nonneg_left hw_norm dist_nonneg
    _ < (ε / B) * B := mul_lt_mul_of_pos_right hw_div hB
    _ = ε := div_mul_cancel₀ ε (ne_of_gt hB)

/-- The joint KS/CvM readout is continuous. -/
theorem continuous_gofFunctional (P : Measure ℝ) [IsProbabilityMeasure P] :
    Continuous (gofFunctional P) := by
  exact continuous_ksFunctional.prodMk (continuous_cvmFunctional P)

/-- Canonical half-line empirical-process path.

Edge behavior: at `n = 0`, the empirical average and the `sqrt n` scale make
this the zero path. -/
noncomputable def empiricalHalfLinePath (P : Measure ℝ) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → ℝ) : LinfF halfLineIndicatorClass := by
  have henv : ∃ G, IsEnvelope halfLineIndicatorClass G ∧ Integrable G P := by
    refine ⟨fun _ => (1 : ℝ), ?_, integrable_const 1⟩
    rintro f ⟨t, rfl⟩ x
    by_cases hxt : x ≤ t <;> simp [halfLineIndicator, hxt]
  exact empiricalProcessLinf X (memℓp_empiricalProcess henv X)

/-- Scaled Kolmogorov–Smirnov statistic as a functional of the empirical
half-line path.

Edge behavior: it is zero for `n = 0`. -/
noncomputable def kolmogorovSmirnovStatistic
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → ℝ) : ℝ :=
  ksFunctional (empiricalHalfLinePath P n X)

/-- Scaled Cramér–von Mises statistic as a functional of the empirical
half-line path.

Edge behavior: it is zero for `n = 0`. -/
noncomputable def cramerVonMisesStatistic
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → ℝ) : ℝ :=
  cvmFunctional P (empiricalHalfLinePath P n X)

private theorem empiricalHalfLinePath_apply
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → ℝ) (t : ℝ) :
    empiricalHalfLinePath P n X (halfLineIndex t) =
      Real.sqrt n * (empiricalCDF n X t - cdf P t) := by
  simpa only [empiricalHalfLinePath, empiricalProcessLinf] using!
    empiricalProcess_halfLine_eq P n X t

/-- Empirical-path identity for the scaled KS statistic. -/
theorem kolmogorovSmirnovStatistic_eq_iSup
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → ℝ) :
    kolmogorovSmirnovStatistic P n X =
      ⨆ t : ℝ, |Real.sqrt n * (empiricalCDF n X t - cdf P t)| := by
  unfold kolmogorovSmirnovStatistic ksFunctional
  rw [lp.norm_eq_ciSup]
  exact (halfLineIndexEquiv.iSup_congr fun t => by
    change |empiricalHalfLinePath P n X (halfLineIndex t)| =
      |Real.sqrt n * (empiricalCDF n X t - cdf P t)|
    exact congrArg abs (empiricalHalfLinePath_apply P n X t)).symm

private theorem measurable_empiricalCDF (n : ℕ) (X : Fin n → ℝ) :
    Measurable (empiricalCDF n X) := by
  unfold empiricalCDF empiricalAvg
  apply measurable_const.mul
  refine Finset.measurable_sum Finset.univ fun i _ => ?_
  apply Monotone.measurable
  intro s t hst
  by_cases hxs : X i ≤ s
  · simp [halfLineIndicator, hxs, hxs.trans hst]
  · by_cases hxt : X i ≤ t
    · simp [halfLineIndicator, hxs, hxt]
    · simp [halfLineIndicator, hxs, hxt]

/-- On an empirical path the upper-integral CvM definition reduces to the
ordinary Bochner integral of the measurable squared empirical-CDF path. -/
theorem cramerVonMisesStatistic_eq_integral
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → ℝ) :
    cramerVonMisesStatistic P n X =
      ∫ t, (Real.sqrt n * (empiricalCDF n X t - cdf P t)) ^ 2 ∂P := by
  let g : ℝ → ℝ := fun t => Real.sqrt n * (empiricalCDF n X t - cdf P t)
  have hg : Measurable g :=
    measurable_const.mul ((measurable_empiricalCDF n X).sub (monotone_cdf P).measurable)
  have hg_sq : Measurable fun t => g t ^ 2 := hg.pow_const 2
  have hof : Measurable fun t => ENNReal.ofReal (g t ^ 2) :=
    ENNReal.measurable_ofReal.comp hg_sq
  unfold cramerVonMisesStatistic cvmFunctional
  simp_rw [empiricalHalfLinePath_apply]
  change (outerExpectation P fun t => ENNReal.ofReal (g t ^ 2)).toReal =
    ∫ t, g t ^ 2 ∂P
  rw [outerExpectation_eq_lintegral hof]
  exact (integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun t => sq_nonneg (g t))
    hg_sq.aestronglyMeasurable).symm

/-- The joint statistic is exactly the joint functional of the empirical
half-line path. -/
theorem gofFunctional_empiricalHalfLinePath
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → ℝ) :
    gofFunctional P (empiricalHalfLinePath P n X) =
      (kolmogorovSmirnovStatistic P n X, cramerVonMisesStatistic P n X) := by
  rfl

/-- **Corollary 19.21, joint outer weak-convergence form.**
For iid observations with arbitrary real distribution `P`, the pair of scaled
KS and CvM statistics converges jointly to the corresponding continuous
functionals of a tight `P`-Brownian bridge.

This conclusion is obtained from the full `LinfF` process theorem, not from
pointwise convergence. -/
theorem goodnessOfFit_joint_weakConvergesOuter
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ξ → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ ν : Measure (LinfF halfLineIndicatorClass),
      IsPBrownianBridge halfLineIndicatorClass P ν ∧
      WeakConvergesOuter (fun _ => μ)
        (fun n ξ =>
          (kolmogorovSmirnovStatistic P n (fun i : Fin n => X i.val ξ),
            cramerVonMisesStatistic P n (fun i : Fin n => X i.val ξ)))
        (ν.map (gofFunctional P)) := by
  obtain ⟨ν, hν, hall⟩ := halfLine_isPDonskerWithBridge P
  refine ⟨ν, hν, ?_⟩
  obtain ⟨hmem, hweak⟩ := hall μ X hX_meas hX_indep hX_ident hX_law
  have hmapped := hweak.map (gofFunctional P) (continuous_gofFunctional P)
    (continuous_gofFunctional P).aemeasurable
  have hproc :
      (fun n ξ => gofFunctional P
        (empiricalProcessLinf (fun i : Fin n => X i.val ξ) (hmem n ξ))) =
      (fun n ξ =>
        (kolmogorovSmirnovStatistic P n (fun i : Fin n => X i.val ξ),
          cramerVonMisesStatistic P n (fun i : Fin n => X i.val ξ))) := by
    funext n ξ
    rw [← gofFunctional_empiricalHalfLinePath]
    congr 1
  rw [← hproc]
  exact hmapped

/-- Marginal outer weak convergence of the scaled KS statistic in Corollary
19.21, for an arbitrary real probability law. -/
theorem kolmogorovSmirnov_weakConvergesOuter
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ξ → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ ν : Measure (LinfF halfLineIndicatorClass),
      IsPBrownianBridge halfLineIndicatorClass P ν ∧
      WeakConvergesOuter (fun _ => μ)
        (fun n ξ => kolmogorovSmirnovStatistic P n (fun i : Fin n => X i.val ξ))
        (ν.map ksFunctional) := by
  obtain ⟨ν, hν, hjoint⟩ := goodnessOfFit_joint_weakConvergesOuter
    μ P X hX_meas hX_indep hX_ident hX_law
  refine ⟨ν, hν, ?_⟩
  have hmapped := hjoint.map (fun p : ℝ × ℝ => p.1) continuous_fst
    continuous_fst.aemeasurable
  have hlaw : (ν.map (gofFunctional P)).map (fun p : ℝ × ℝ => p.1) =
      ν.map ksFunctional := by
    rw [Measure.map_map measurable_fst (continuous_gofFunctional P).measurable]
    congr 1
  rw [hlaw] at hmapped
  simpa using hmapped

/-- Marginal outer weak convergence of the scaled CvM statistic in Corollary
19.21, for an arbitrary real probability law. -/
theorem cramerVonMises_weakConvergesOuter
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (X : ℕ → Ξ → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P) :
    ∃ ν : Measure (LinfF halfLineIndicatorClass),
      IsPBrownianBridge halfLineIndicatorClass P ν ∧
      WeakConvergesOuter (fun _ => μ)
        (fun n ξ => cramerVonMisesStatistic P n (fun i : Fin n => X i.val ξ))
        (ν.map (cvmFunctional P)) := by
  obtain ⟨ν, hν, hjoint⟩ := goodnessOfFit_joint_weakConvergesOuter
    μ P X hX_meas hX_indep hX_ident hX_law
  refine ⟨ν, hν, ?_⟩
  have hmapped := hjoint.map (fun p : ℝ × ℝ => p.2) continuous_snd
    continuous_snd.aemeasurable
  have hlaw : (ν.map (gofFunctional P)).map (fun p : ℝ × ℝ => p.2) =
      ν.map (cvmFunctional P) := by
    rw [Measure.map_map measurable_snd (continuous_gofFunctional P).measurable]
    congr 1
  rw [hlaw] at hmapped
  simpa using hmapped

end AsymptoticStatistics.EmpiricalProcess
