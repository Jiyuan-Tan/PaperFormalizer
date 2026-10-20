module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringBook
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringOuterMaximal

@[expose] public section

/-!
# Anchored book-uniform covering maximal inequality

This file converts the finite-discrete uniform entropy bound to the
book all-probability entropy integral for classes containing the zero function.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- A corrected anchored consequence of the uniform-covering maximal route,
not a literal formalization of vdV Lemma 19.38.  The additional assumption
`0 ∈ F` absorbs the regularized entropy head term, while `hDense` is the
concrete sufficient admissibility condition used for suitable measurability. -/
theorem outer_empiricalProcessSup_le_bookUniformEntropy_of_zero_mem
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i,
      ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (F : Set (Ω → ℝ))
    (hzero : (fun _ : Ω => 0) ∈ F)
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ) (hΦ : IsEnvelope F Φ)
    (hΦ_meas : Measurable Φ) (n : ℕ) :
    MeasureTheory.outerExpectation μ
        (fun ξ => supNormOver F
          (empiricalProcess P n
            (fun i : Fin n => X i.val ξ))) ≤
      156 * bookUniformCoveringEntropyIntegral 1 F Φ *
        eLpNorm Φ 2 P := by
  let Y : Ξ → (Fin n → Ω) := fun ξ i => X i.val ξ
  let D : Ξ → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal (empiricalL2Seminorm n (Y ξ) Φ)
  let J₁ : ℝ≥0∞ := bookUniformCoveringEntropyIntegral 1 F Φ
  have hY_meas : Measurable Y :=
    measurable_pi_lambda _ fun i => hX_meas i.val
  have hD_meas : Measurable D :=
    ((measurable_empiricalL2Seminorm Φ hΦ_meas n).comp hY_meas).ennreal_ofReal
  have hJ_le : ∀ ξ,
      uniformCoveringEntropyIntegral
          (empiricalRelativeRadiusReal F Φ n (Y ξ)) F Φ ≤
        3 * J₁ := by
    intro ξ
    calc
      uniformCoveringEntropyIntegral
          (empiricalRelativeRadiusReal F Φ n (Y ξ)) F Φ ≤
          3 * bookUniformCoveringEntropyIntegral
            (empiricalRelativeRadiusReal F Φ n (Y ξ)) F Φ :=
        empiricalUniformEntropyIntegral_le_three_mul_book
          F hzero hF_meas Φ hΦ_meas n (Y ξ)
      _ ≤ 3 * J₁ := mul_le_mul_right
        (bookUniformCoveringEntropyIntegral_mono_delta F Φ
          (empiricalRelativeRadiusReal_le_one_of_isEnvelope
            F Φ n (Y ξ) hΦ)) 3
  calc
    MeasureTheory.outerExpectation μ
        (fun ξ => supNormOver F
          (empiricalProcess P n (fun i : Fin n => X i.val ξ))) ≤
        52 * ∫⁻ ξ, D ξ *
          uniformCoveringEntropyIntegral
            (empiricalRelativeRadiusReal F Φ n (Y ξ)) F Φ ∂μ := by
      simpa only [Y, D] using
        outer_empiricalProcessSup_le_expected_empiricalUniformEntropy
          P μ X hX_meas hX_iindep hX_idem hX_law F hDense hF_meas Φ hΦ n
    _ ≤ 52 * ∫⁻ ξ, D ξ * (3 * J₁) ∂μ :=
      mul_le_mul_right (lintegral_mono fun ξ =>
        mul_le_mul_right (hJ_le ξ) (D ξ)) 52
    _ = 156 * J₁ * ∫⁻ ξ, D ξ ∂μ := by
      rw [lintegral_mul_const (3 * J₁) hD_meas]
      ring
    _ ≤ 156 * J₁ * eLpNorm Φ 2 P :=
      mul_le_mul_right
        (lintegral_iid_empiricalL2Seminorm_le_eLpNorm
          P μ X hX_meas hX_iindep hX_idem hX_law Φ hΦ_meas n)
        (156 * J₁)

/-- A corrected anchored random-radius consequence of the uniform-covering
maximal route, not a literal formalization of vdV Lemma 19.38.  The assumption
`0 ∈ F` absorbs the regularized entropy head term pointwise in the sample. -/
theorem outer_empiricalProcessSup_le_expected_bookUniformEntropy_of_zero_mem
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (F : Set (Ω → ℝ))
    (hzero : (fun _ : Ω => 0) ∈ F)
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ)
    (hΦ : IsEnvelope F Φ)
    (hΦ_meas : Measurable Φ)
    (n : ℕ) :
    MeasureTheory.outerExpectation μ
        (fun ξ => supNormOver F
          (empiricalProcess P n (fun i : Fin n => X i.val ξ))) ≤
      156 * ∫⁻ ξ,
        ENNReal.ofReal
            (empiricalL2Seminorm n (fun i : Fin n => X i.val ξ) Φ) *
          bookUniformCoveringEntropyIntegral
            (empiricalRelativeRadiusReal F Φ n
              (fun i : Fin n => X i.val ξ)) F Φ ∂μ := by
  let Y : Ξ → (Fin n → Ω) := fun ξ i => X i.val ξ
  let D : Ξ → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal (empiricalL2Seminorm n (Y ξ) Φ)
  let J : Ξ → ℝ≥0∞ := fun ξ =>
    bookUniformCoveringEntropyIntegral
      (empiricalRelativeRadiusReal F Φ n (Y ξ)) F Φ
  have hJ_le : ∀ ξ,
      uniformCoveringEntropyIntegral
          (empiricalRelativeRadiusReal F Φ n (Y ξ)) F Φ ≤
        3 * J ξ := fun ξ =>
    empiricalUniformEntropyIntegral_le_three_mul_book
      F hzero hF_meas Φ hΦ_meas n (Y ξ)
  calc
    MeasureTheory.outerExpectation μ
        (fun ξ => supNormOver F
          (empiricalProcess P n (fun i : Fin n => X i.val ξ))) ≤
        52 * ∫⁻ ξ, D ξ *
          uniformCoveringEntropyIntegral
            (empiricalRelativeRadiusReal F Φ n (Y ξ)) F Φ ∂μ := by
      simpa only [Y, D] using
        outer_empiricalProcessSup_le_expected_empiricalUniformEntropy
          P μ X hX_meas hX_iindep hX_idem hX_law F hDense hF_meas Φ hΦ n
    _ ≤ 52 * ∫⁻ ξ, D ξ * (3 * J ξ) ∂μ :=
      mul_le_mul_right (lintegral_mono fun ξ =>
        mul_le_mul_right (hJ_le ξ) (D ξ)) 52
    _ = 156 * ∫⁻ ξ, D ξ * J ξ ∂μ := by
      have hreorder : (∫⁻ ξ, D ξ * (3 * J ξ) ∂μ) =
          ∫⁻ ξ, 3 * (D ξ * J ξ) ∂μ := by
        apply lintegral_congr
        intro ξ
        ac_rfl
      rw [hreorder, lintegral_const_mul' 3 (fun ξ => D ξ * J ξ) (by norm_num)]
      ring

end AsymptoticStatistics.EmpiricalProcess
