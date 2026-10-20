module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.GlivenkoCantelli
public import StatLean.AsymptoticStatistics.EmpiricalProcess.HalfLineBracketing
public import StatLean.AsymptoticStatistics.EmpiricalProcess.AbstractDonsker.FiniteCarrier

@[expose] public section

/-!
# Empirical distribution process

The empirical CDF and the structural statements of van der Vaart Theorems 19.1
and 19.3 (book pp.265–266). The Donsker conclusion is genuine outer weak
convergence in `LinfF halfLineIndicatorClass` to a tight Brownian-bridge law.

The threshold parametrization is uniformly norm-isometric to bounded real
paths indexed by `ℝ`. We do not introduce or claim convergence in a separate
cadlag/Skorohod space, and pointwise convergence is not used as a substitute
for the `ℓ∞` process statement.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Empirical distribution function `Fₙ(t) = n⁻¹ Σᵢ 1{Xᵢ ≤ t}`.

Edge behavior: for the empty sample (`n = 0`) the empirical average convention
gives the zero function. The book invokes this definition only for `n ≥ 1`. -/
noncomputable def empiricalCDF (n : ℕ) (X : Fin n → ℝ) (t : ℝ) : ℝ :=
  empiricalAvg (halfLineIndicator t) n X

/-- The empirical CDF is the normalized count of observations in `(-∞,t]`. -/
lemma empiricalCDF_eq_count (n : ℕ) (X : Fin n → ℝ) (t : ℝ) :
    empiricalCDF n X t =
      (n : ℝ)⁻¹ * ((Finset.univ.filter fun i => X i ≤ t).card : ℝ) := by
  unfold empiricalCDF empiricalAvg
  congr 1
  simp [halfLineIndicator, Set.indicator_apply, Finset.sum_boole]

/-- Half-line coordinate of the empirical process is the classical centred
empirical distribution process `√n (Fₙ(t) - F(t))`. -/
lemma empiricalProcess_halfLine_eq (P : Measure ℝ) [IsProbabilityMeasure P]
    (n : ℕ) (X : Fin n → ℝ) (t : ℝ) :
    empiricalProcess P n X (halfLineIndicator t) =
      Real.sqrt n * (empiricalCDF n X t - cdf P t) := by
  rw [empiricalProcess, empiricalCDF, integral_halfLineIndicator]

/-- Bounded real paths indexed by thresholds, with the uniform norm. -/
abbrev HalfLineLinf : Type := lp (fun _ : ℝ => ℝ) ∞

/-- Uniform-norm reindexing of `ℓ∞(halfLineIndicatorClass)` by thresholds.

Edge behavior: this is a pure reindexing through `halfLineIndexEquiv`; it adds
no cadlag or endpoint regularity to the path space. -/
noncomputable def halfLineLinfEquiv :
    LinfF halfLineIndicatorClass ≃ₗᵢ[ℝ] HalfLineLinf where
  toFun z := ⟨fun t ↦ z (halfLineIndex t), by
    apply memℓp_infty
    refine ⟨‖z‖, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero z (halfLineIndex t)⟩
  invFun y := ⟨fun f ↦ y (halfLineIndexEquiv.symm f), by
    apply memℓp_infty
    refine ⟨‖y‖, ?_⟩
    rintro _ ⟨f, rfl⟩
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero y (halfLineIndexEquiv.symm f)⟩
  left_inv z := by
    ext f
    exact congrArg z (halfLineIndexEquiv.apply_symm_apply f)
  right_inv y := by
    ext t
    exact congrArg y (halfLineIndexEquiv.symm_apply_apply t)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' z := by
    simp only [lp.norm_eq_ciSup]
    exact halfLineIndexEquiv.iSup_congr (fun _ ↦ rfl)

/-- Every threshold evaluation is continuous in the `ℓ∞` uniform norm. -/
theorem continuous_halfLine_evaluation (t : ℝ) :
    Continuous (fun z : LinfF halfLineIndicatorClass => z (halfLineIndex t)) :=
  continuous_linfF_eval (halfLineIndex t)

/-- **Theorem 19.1 (Glivenko–Cantelli for empirical distribution functions).**
For every real probability law, the closed half-line indicator class is
`P`-Glivenko–Cantelli. No continuity or nonatomicity assumption is present. -/
theorem halfLine_isPGlivenkoCantelli
    -- USER-INPUT: an arbitrary probability law on `ℝ`; vdV Theorem 19.1.
    (P : Measure ℝ) [IsProbabilityMeasure P] :
    IsPGlivenkoCantelli halfLineIndicatorClass P := by
  apply isPGlivenkoCantelli_of_finite_bracketing_L1 halfLineIndicatorClass P
  · rintro f ⟨t, rfl⟩
    exact (halfLineIndicator_memLp P t 1).integrable (by norm_num)
  · exact fun ε hε ↦ halfLine_hasFiniteBracketingCover_L1 P hε

/-- **Theorem 19.3 (Donsker for empirical distribution functions).**
The full half-line empirical process converges weakly, in the uniform-norm
carrier `ℓ∞(halfLineIndicatorClass)`, to a tight `P`-Brownian bridge.

This invokes the carrier-agnostic finite-bracketing-entropy theorem. It does
not assert that the Gaussian carrier is finite-dimensional. -/
theorem halfLine_isPDonskerWithBridge
    -- USER-INPUT: an arbitrary probability law on `ℝ`; vdV Theorem 19.3.
    (P : Measure ℝ) [IsProbabilityMeasure P] :
    IsPDonskerWithBridge halfLineIndicatorClass P := by
  obtain ⟨_, _, _, hbridge⟩ := donskerWithBridge_of_finite_bracketing_entropy
    (F := halfLineIndicatorClass) (P := P)
    (by rintro f ⟨t, rfl⟩; exact measurable_halfLineIndicator t)
    (halfLine_bracketingEntropyIntegral_lt_top P)
  exact hbridge

/-- Brownian-bridge covariance for half-line coordinates:
`F(min s t) - F(s)F(t)`, valid for arbitrary atoms. -/
theorem halfLine_bridge_covariance
    (P : Measure ℝ) [IsProbabilityMeasure P]
    {ν : Measure (LinfF halfLineIndicatorClass)}
    (hν : IsPBrownianBridge halfLineIndicatorClass P ν) (s t : ℝ) :
    ∫ z, z (halfLineIndex s) * z (halfLineIndex t) ∂ν =
      cdf P (min s t) - cdf P s * cdf P t := by
  rw [hν.cov (halfLineIndex s) (halfLineIndex t)]
  simp only [halfLineIndex]
  rw [integral_halfLineIndicator_mul, integral_halfLineIndicator,
    integral_halfLineIndicator]

end AsymptoticStatistics.EmpiricalProcess
