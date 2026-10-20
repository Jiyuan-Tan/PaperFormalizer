module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringRademacherFiniteChaining
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringSymmetrization
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.MeanInequalities

@[expose] public section

/-!
# Expected empirical envelope seminorm

This file bounds the expected realized empirical `L²` seminorm by the
population `L²` seminorm, first under the canonical product law and then for
an abstract iid sample. It is the analytic normalization step in the
finite-discrete outer maximal inequality.
-/

namespace AsymptoticStatistics.EmpiricalProcess
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The expected realized empirical `L²` seminorm is at most the population
`L²` seminorm. The statement is total when the population seminorm is
infinite, and the empty sample has value zero. -/
theorem lintegral_empiricalL2Seminorm_le_eLpNorm
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ) (n : ℕ) :
    (∫⁻ x : Fin n → Ω, ENNReal.ofReal (empiricalL2Seminorm n x Φ)
      ∂Measure.pi (fun _ : Fin n => P)) ≤ eLpNorm Φ 2 P := by
  cases n with
  | zero => simp
  | succ k =>
      let ν : Measure (Fin (k + 1) → Ω) :=
        Measure.pi (fun _ : Fin (k + 1) => P)
      let g : (Fin (k + 1) → Ω) → ℝ := fun x =>
        empiricalL2Seminorm (k + 1) x Φ
      have hg_meas : Measurable g :=
        measurable_empiricalL2Seminorm Φ hΦ_meas (k + 1)
      have hL2 : eLpNorm g 2 ν = eLpNorm Φ 2 P := by
        rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
              (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num),
          eLpNorm_eq_lintegral_rpow_enorm_toReal
              (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)]
        simp only [ENNReal.toReal_ofNat]
        congr 1
        calc
          (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂ν) =
              ∫⁻ x, ENNReal.ofReal ((k + 1 : ℝ)⁻¹) *
                ∑ i : Fin (k + 1), ENNReal.ofReal (|Φ (x i)| ^ 2) ∂ν := by
            apply lintegral_congr
            intro x
            have havg : 0 ≤ empiricalAvg (fun y => |Φ y| ^ 2) (k + 1) x := by
              unfold empiricalAvg
              positivity
            rw [show g x = Real.sqrt
                (empiricalAvg (fun y => |Φ y| ^ 2) (k + 1) x) by
                  rfl,
              Real.enorm_eq_ofReal_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
            calc
              ENNReal.ofReal
                    (Real.sqrt (empiricalAvg (fun y => |Φ y| ^ 2) (k + 1) x)) ^
                    (2 : ℝ) =
                  ENNReal.ofReal
                    (Real.sqrt (empiricalAvg (fun y => |Φ y| ^ 2) (k + 1) x)) ^
                    (2 : ℕ) := ENNReal.rpow_natCast _ 2
              _ = ENNReal.ofReal
                    ((Real.sqrt
                      (empiricalAvg (fun y => |Φ y| ^ 2) (k + 1) x)) ^ 2) :=
                (ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2).symm
              _ = ENNReal.ofReal
                    (empiricalAvg (fun y => |Φ y| ^ 2) (k + 1) x) := by
                rw [Real.sq_sqrt havg]
              _ = ENNReal.ofReal ((k + 1 : ℝ)⁻¹) *
                    ∑ i : Fin (k + 1), ENNReal.ofReal (|Φ (x i)| ^ 2) := by
                rw [empiricalAvg]
                rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by norm_num]
                rw [ENNReal.ofReal_mul (inv_nonneg.mpr (by positivity)),
                  ENNReal.ofReal_sum_of_nonneg]
                exact fun i hi => by positivity
          _ = ENNReal.ofReal ((k + 1 : ℝ)⁻¹) *
              ∑ i : Fin (k + 1),
                ∫⁻ x, ENNReal.ofReal (|Φ (x i)| ^ 2) ∂ν := by
            rw [lintegral_const_mul]
            · rw [lintegral_finset_sum]
              intro i hi
              exact ((hΦ_meas.comp (measurable_pi_apply i)).abs.pow_const 2).ennreal_ofReal
            · exact Finset.measurable_sum Finset.univ fun i _ =>
                ((hΦ_meas.comp (measurable_pi_apply i)).abs.pow_const 2).ennreal_ofReal
          _ = ENNReal.ofReal ((k + 1 : ℝ)⁻¹) *
              ∑ i : Fin (k + 1),
                ∫⁻ y, ENNReal.ofReal (|Φ y| ^ 2) ∂P := by
            congr 2 with i
            exact (measurePreserving_eval
              (fun _ : Fin (k + 1) => P) i).lintegral_comp
                (hΦ_meas.abs.pow_const 2).ennreal_ofReal
          _ = ∫⁻ y, ENNReal.ofReal (|Φ y| ^ 2) ∂P := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
              ENNReal.ofReal_inv_of_pos (by positivity)]
            simp only [nsmul_eq_mul]
            rw [show ENNReal.ofReal ((k : ℝ) + 1) = (k : ℝ≥0∞) + 1 by
              rw [ENNReal.ofReal_add (by positivity) (by positivity)]
              simp]
            rw [show ((k + 1 : ℕ) : ℝ≥0∞) = (k : ℝ≥0∞) + 1 by norm_num]
            rw [← mul_assoc]
            rw [ENNReal.inv_mul_cancel]
            · simp
            · positivity
            · finiteness
          _ = ∫⁻ y, ‖Φ y‖ₑ ^ (2 : ℝ) ∂P := by
            apply lintegral_congr
            intro y
            rw [Real.enorm_eq_ofReal_abs,
              ENNReal.ofReal_pow (abs_nonneg _) 2]
            exact (ENNReal.rpow_natCast _ 2).symm
      calc
        (∫⁻ x, ENNReal.ofReal (empiricalL2Seminorm (k + 1) x Φ) ∂ν) =
            eLpNorm g 1 ν := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          apply lintegral_congr
          intro x
          rw [Real.enorm_eq_ofReal_abs,
            abs_of_nonneg (empiricalL2Seminorm_nonneg (k + 1) x Φ)]
        _ ≤ eLpNorm g 2 ν :=
          eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hg_meas.aestronglyMeasurable
        _ = eLpNorm Φ 2 P := hL2

/-- The expected empirical `L²` seminorm bound transported to an abstract iid
sample with common law `P`. -/
theorem lintegral_iid_empiricalL2Seminorm_le_eLpNorm
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (Φ : Ω → ℝ) (hΦ_meas : Measurable Φ) (n : ℕ) :
    (∫⁻ ξ, ENNReal.ofReal (empiricalL2Seminorm n
      (fun i : Fin n => X i.val ξ) Φ) ∂μ) ≤ eLpNorm Φ 2 P := by
  let Y : Ξ → (Fin n → Ω) := fun ξ i => X i.val ξ
  let rms : (Fin n → Ω) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (empiricalL2Seminorm n x Φ)
  have hY_meas : Measurable Y :=
    measurable_pi_lambda _ fun i => hX_meas i.val
  have hY_map : μ.map Y = Measure.pi (fun _ : Fin n => P) :=
    AsymptoticStatistics.map_fin_restrict_eq_pi_of_iid
      P μ X hX_meas hX_iindep hX_idem hX_law n
  have hrms_meas : Measurable rms :=
    (measurable_empiricalL2Seminorm Φ hΦ_meas n).ennreal_ofReal
  change (∫⁻ ξ, rms (Y ξ) ∂μ) ≤ eLpNorm Φ 2 P
  calc
    (∫⁻ ξ, rms (Y ξ) ∂μ) =
        ∫⁻ x, rms x ∂Measure.pi (fun _ : Fin n => P) := by
      rw [← hY_map, lintegral_map hrms_meas hY_meas]
    _ ≤ eLpNorm Φ 2 P :=
      lintegral_empiricalL2Seminorm_le_eLpNorm P Φ hΦ_meas n

/-- The finite-discrete empirical entropy integrand is bounded by
its unit-endpoint entropy integral times the population `L²` seminorm. -/
theorem lintegral_iid_empiricalUniformEntropy_le
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (hΦ : IsEnvelope F Φ)
    (hΦ_meas : Measurable Φ) (n : ℕ) :
    (∫⁻ ξ, ENNReal.ofReal (empiricalL2Seminorm n
        (fun i : Fin n => X i.val ξ) Φ) *
      uniformCoveringEntropyIntegral
        (empiricalRelativeRadiusReal F Φ n
          (fun i : Fin n => X i.val ξ)) F Φ ∂μ) ≤
      uniformCoveringEntropyIntegral 1 F Φ * eLpNorm Φ 2 P := by
  let Y : Ξ → (Fin n → Ω) := fun ξ i => X i.val ξ
  let D : Ξ → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal (empiricalL2Seminorm n (Y ξ) Φ)
  let J : Ξ → ℝ≥0∞ := fun ξ =>
    uniformCoveringEntropyIntegral
      (empiricalRelativeRadiusReal F Φ n (Y ξ)) F Φ
  let J1 : ℝ≥0∞ := uniformCoveringEntropyIntegral 1 F Φ
  have hY_meas : Measurable Y :=
    measurable_pi_lambda _ fun i => hX_meas i.val
  have hD_meas : Measurable D :=
    ((measurable_empiricalL2Seminorm Φ hΦ_meas n).comp hY_meas).ennreal_ofReal
  have hJ_le : ∀ ξ, J ξ ≤ J1 := fun ξ =>
    uniformCoveringEntropyIntegral_mono_delta F Φ
      (empiricalRelativeRadiusReal_le_one_of_isEnvelope F Φ n (Y ξ) hΦ)
  change (∫⁻ ξ, D ξ * J ξ ∂μ) ≤ J1 * eLpNorm Φ 2 P
  calc
    (∫⁻ ξ, D ξ * J ξ ∂μ) ≤ ∫⁻ ξ, D ξ * J1 ∂μ :=
      lintegral_mono fun ξ => mul_le_mul_right (hJ_le ξ) (D ξ)
    _ = (∫⁻ ξ, D ξ ∂μ) * J1 := lintegral_mul_const J1 hD_meas
    _ = J1 * (∫⁻ ξ, D ξ ∂μ) := mul_comm _ _
    _ ≤ J1 * eLpNorm Φ 2 P := mul_le_mul_right
      (lintegral_iid_empiricalL2Seminorm_le_eLpNorm
        P μ X hX_meas hX_iindep hX_idem hX_law Φ hΦ_meas n) J1

/-- The outer empirical-process supremum is bounded by the expected realized
finite-discrete entropy integral, with the explicit chaining constant `52`. -/
theorem outer_empiricalProcessSup_le_expected_empiricalUniformEntropy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (F : Set (Ω → ℝ)) (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ) (hΦ : IsEnvelope F Φ) (n : ℕ) :
    MeasureTheory.outerExpectation μ (fun ξ => supNormOver F
      (empiricalProcess P n (fun i : Fin n => X i.val ξ))) ≤
      52 * ∫⁻ ξ, ENNReal.ofReal (empiricalL2Seminorm n
        (fun i : Fin n => X i.val ξ) Φ) *
      uniformCoveringEntropyIntegral
        (empiricalRelativeRadiusReal F Φ n
          (fun i : Fin n => X i.val ξ)) F Φ ∂μ := by
  let D : Ξ → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal (empiricalL2Seminorm n
      (fun i : Fin n => X i.val ξ) Φ)
  let J : Ξ → ℝ≥0∞ := fun ξ =>
    uniformCoveringEntropyIntegral
      (empiricalRelativeRadiusReal F Φ n
        (fun i : Fin n => X i.val ξ)) F Φ
  have hpoint : ∀ ξ, conditionalRademacherSup F n
      (fun i : Fin n => X i.val ξ) ≤ 26 * (D ξ * J ξ) := by
    intro ξ
    simpa only [D, J, mul_assoc] using
      conditionalRademacherSup_le_uniformCoveringEntropyIntegral
        F Φ n (fun i : Fin n => X i.val ξ) hΦ
  calc
    MeasureTheory.outerExpectation μ (fun ξ => supNormOver F
        (empiricalProcess P n (fun i : Fin n => X i.val ξ))) ≤
        2 * ∫⁻ ξ, conditionalRademacherSup F n
          (fun i : Fin n => X i.val ξ) ∂μ :=
      outer_symmetrization_empiricalProcess P μ X hX_meas hX_iindep
        hX_idem hX_law F hDense hF_meas n
    _ ≤ 2 * ∫⁻ ξ, 26 * (D ξ * J ξ) ∂μ :=
      mul_le_mul_right (lintegral_mono hpoint) 2
    _ = 2 * (26 * ∫⁻ ξ, D ξ * J ξ ∂μ) := by
      rw [lintegral_const_mul' 26 (fun ξ => D ξ * J ξ) (by norm_num)]
    _ = 52 * ∫⁻ ξ, D ξ * J ξ ∂μ := by ring

/-- The unit-endpoint version of the finite-discrete uniform-covering
outer maximal inequality. -/
theorem outer_empiricalProcessSup_le_uniformCoveringEntropyIntegral
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (F : Set (Ω → ℝ)) (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ) (hΦ : IsEnvelope F Φ)
    (hΦ_meas : Measurable Φ) (n : ℕ) :
    MeasureTheory.outerExpectation μ (fun ξ => supNormOver F
      (empiricalProcess P n (fun i : Fin n => X i.val ξ))) ≤
      52 * uniformCoveringEntropyIntegral 1 F Φ * eLpNorm Φ 2 P := by
  calc
    MeasureTheory.outerExpectation μ (fun ξ => supNormOver F
        (empiricalProcess P n (fun i : Fin n => X i.val ξ))) ≤
        52 * ∫⁻ ξ, ENNReal.ofReal (empiricalL2Seminorm n
          (fun i : Fin n => X i.val ξ) Φ) *
        uniformCoveringEntropyIntegral
          (empiricalRelativeRadiusReal F Φ n
            (fun i : Fin n => X i.val ξ)) F Φ ∂μ :=
      outer_empiricalProcessSup_le_expected_empiricalUniformEntropy
        P μ X hX_meas hX_iindep hX_idem hX_law F hDense hF_meas Φ hΦ n
    _ ≤ 52 * (uniformCoveringEntropyIntegral 1 F Φ * eLpNorm Φ 2 P) :=
      mul_le_mul_right (lintegral_iid_empiricalUniformEntropy_le
        P μ X hX_meas hX_iindep hX_idem hX_law F Φ hΦ hΦ_meas n) 52
    _ = 52 * uniformCoveringEntropyIntegral 1 F Φ * eLpNorm Φ 2 P := by
      rw [mul_assoc]

end AsymptoticStatistics.EmpiricalProcess
