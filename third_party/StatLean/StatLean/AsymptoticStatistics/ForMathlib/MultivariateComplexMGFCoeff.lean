module
public import Mathlib.Probability.Moments.ComplexMGF
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.FormalMultilinearSeries
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-!
Multivariate complex-MGF — power-series coefficients and convergence.

Closes `multivariate_complexMGF_analytic` in
`AsymptoticStatistics.ForMathlib.MultivariateComplexMGF` by exhibiting
an explicit `FormalMultilinearSeries` for
`F(z) = ∫ Complex.exp(∑ zᵢ Xᵢ(ω)) ∂μ(ω)`
and verifying `HasFPowerSeriesOnBall F p 0 ⊤`, which gives
`AnalyticOnNhd ℂ F univ` via `HasFPowerSeriesOnBall.analyticOnNhd` +
`Metric.eball_top`.

## Construction

`p_n : (Fin m → ℂ)[×n]→L[ℂ] ℂ` is built as a finite sum over multi-indices
`ι : Fin n → Fin m` of monomial CMMs scaled by scalar moment integrals
`mgfMomentCoeff X ι := ∫ ∏ⱼ X(ω) (ι j) ∂μ`. The exponential `1/n!` factor
is bundled into `mgfCoeffCMM`. This avoids any Bochner integration of
CMM-valued functions.
-/

open MeasureTheory Complex Set Filter Topology Finset
open scoped ENNReal NNReal BigOperators

namespace AsymptoticStatistics.ForMathlib.MultivariateComplexMGFCoeff

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ### Auxiliary integrability lemmas -/

omit [IsProbabilityMeasure μ] in
/-- *Polycube domination.* If `Real.exp(∑ᵢ tᵢ Xᵢ)` is integrable for every
real direction `t`, then `Real.exp(s · ∑ᵢ |Xᵢ|)` is integrable for every
`s : ℝ`. The proof bounds `s · ∑ |X| ≤ ∑ ((±|s|) · X)` over signs ε. -/
lemma integrable_exp_smul_sum_abs
    {m : ℕ} (X : Ω → Fin m → ℝ) (hX : Measurable X)
    (h_mgf : ∀ t : Fin m → ℝ,
      Integrable (fun ω => Real.exp (∑ i, t i * X ω i)) μ)
    (s : ℝ) :
    Integrable (fun ω => Real.exp (s * ∑ i, |X ω i|)) μ := by
  classical
  have hbound : ∀ ω,
      Real.exp (s * ∑ i, |X ω i|) ≤
        ∑ ε : Fin m → Bool,
          Real.exp (∑ i, (if ε i then |s| else -|s|) * X ω i) := by
    intro ω
    set ε₀ : Fin m → Bool := fun i => decide (0 ≤ s * X ω i)
    have h_eq_pt : ∀ i,
        s * |X ω i| = (if ε₀ i then |s| else -|s|) * X ω i := by
      intro i
      have hε₀_iff : ε₀ i = true ↔ 0 ≤ s * X ω i := by simp [ε₀]
      by_cases hs : 0 ≤ s
      · rcases le_or_gt 0 (X ω i) with hx | hx
        · have : ε₀ i = true := by rw [hε₀_iff]; positivity
          rw [this]
          simp [abs_of_nonneg hx, abs_of_nonneg hs]
        · rcases lt_or_eq_of_le hs with hs_pos | hs_zero
          · have : ε₀ i = false := by
              rw [show ε₀ i = false ↔ ¬ (0 ≤ s * X ω i) from
                  by simp [ε₀]]
              push Not
              exact mul_neg_of_pos_of_neg hs_pos hx
            rw [this]
            simp only [Bool.false_eq_true, if_false]
            rw [abs_of_neg hx, abs_of_pos hs_pos]; ring
          · simp [← hs_zero]
      · push Not at hs
        rcases le_or_gt 0 (X ω i) with hx | hx
        · rcases eq_or_lt_of_le hx with hx_zero | hx_pos
          · simp [← hx_zero]
          · have : ε₀ i = false := by
              rw [show ε₀ i = false ↔ ¬ (0 ≤ s * X ω i) from by simp [ε₀]]
              push Not
              exact mul_neg_of_neg_of_pos hs hx_pos
            rw [this]
            simp only [Bool.false_eq_true, if_false]
            rw [abs_of_nonneg hx, abs_of_neg hs]; ring
        · have : ε₀ i = true := by
            rw [hε₀_iff]
            exact (mul_pos_of_neg_of_neg hs hx).le
          rw [this]
          simp only [if_true]
          rw [abs_of_neg hx, abs_of_neg hs]; ring
    have h_sum_eq :
        s * (∑ i, |X ω i|) = ∑ i, (if ε₀ i then |s| else -|s|) * X ω i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => h_eq_pt i)
    rw [h_sum_eq]
    refine Finset.single_le_sum (f := fun ε : Fin m → Bool =>
      Real.exp (∑ i, (if ε i then |s| else -|s|) * X ω i))
      (fun ε _ => (Real.exp_pos _).le) (Finset.mem_univ ε₀)
  have h_each : ∀ ε : Fin m → Bool,
      Integrable (fun ω => Real.exp (∑ i, (if ε i then |s| else -|s|) * X ω i)) μ :=
    fun ε => h_mgf (fun i => if ε i then |s| else -|s|)
  have h_sum_int :
      Integrable (fun ω => ∑ ε : Fin m → Bool,
        Real.exp (∑ i, (if ε i then |s| else -|s|) * X ω i)) μ :=
    integrable_finset_sum _ (fun ε _ => h_each ε)
  have h_meas : AEStronglyMeasurable
      (fun ω => Real.exp (s * ∑ i, |X ω i|)) μ := by
    have h_sum_meas : AEStronglyMeasurable (fun ω : Ω => ∑ i, |X ω i|) μ := by
      have h_each_aem : ∀ i : Fin m,
          AEStronglyMeasurable (fun ω => |X ω i|) μ := fun i =>
        continuous_abs.comp_aestronglyMeasurable
          ((measurable_pi_apply i).comp hX).aestronglyMeasurable
      have hfun : (fun ω => ∑ i, |X ω i|) = ∑ i : Fin m, fun ω => |X ω i| := by
        funext ω; simp [Finset.sum_apply]
      rw [hfun]
      exact Finset.aestronglyMeasurable_sum _ (fun i _ => h_each_aem i)
    exact Real.continuous_exp.comp_aestronglyMeasurable
      ((continuous_const.mul continuous_id).comp_aestronglyMeasurable h_sum_meas)
  refine Integrable.mono' h_sum_int h_meas
    (Filter.Eventually.of_forall (fun ω => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  exact hbound ω

/-- Power-bound integrability: `(∑ᵢ |X i|)^n` is `μ`-integrable for all
`n : ℕ` whenever `Real.exp(∑ tᵢ Xᵢ)` is integrable for every `t`. -/
lemma integrable_pow_sum_abs
    {m : ℕ} (X : Ω → Fin m → ℝ) (hX : Measurable X)
    (h_mgf : ∀ t : Fin m → ℝ,
      Integrable (fun ω => Real.exp (∑ i, t i * X ω i)) μ) (n : ℕ) :
    Integrable (fun ω => (∑ i, |X ω i|) ^ n) μ := by
  classical
  have h_bound : ∀ ω : Ω, 0 ≤ ∑ i, |X ω i| := fun ω =>
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have h_pow_le : ∀ ω, (∑ i, |X ω i|) ^ n ≤
      (n : ℝ) ^ n * Real.exp (∑ i, |X ω i|) ∨ n = 0 := by
    intro ω
    by_cases hn : n = 0
    · right; exact hn
    · left
      have h := ProbabilityTheory.rpow_abs_le_mul_exp_abs (∑ i, |X ω i|)
        (p := (n : ℝ)) (t := 1) (by exact_mod_cast Nat.zero_le n) one_ne_zero
      simp only [abs_one, div_one, abs_of_nonneg (h_bound ω), one_mul] at h
      have h_nat : (∑ i, |X ω i|) ^ n = (∑ i, |X ω i|) ^ ((n : ℝ) : ℝ) := by
        rw [← Real.rpow_natCast]
      have h_n_nat : ((n : ℝ) : ℝ) ^ ((n : ℝ) : ℝ) = ((n : ℝ) ^ n : ℝ) := by
        rw [← Real.rpow_natCast]
      calc (∑ i, |X ω i|) ^ n
          = (∑ i, |X ω i|) ^ ((n : ℝ) : ℝ) := h_nat
        _ ≤ (n : ℝ) ^ ((n : ℝ) : ℝ) * Real.exp (∑ i, |X ω i|) := h
        _ = (n : ℝ) ^ n * Real.exp (∑ i, |X ω i|) := by rw [h_n_nat]
  have h_sum_meas : AEStronglyMeasurable (fun ω : Ω => ∑ i, |X ω i|) μ := by
    have h_each : ∀ i : Fin m,
        AEStronglyMeasurable (fun ω => |X ω i|) μ := fun i =>
      continuous_abs.comp_aestronglyMeasurable
        ((measurable_pi_apply i).comp hX).aestronglyMeasurable
    have hfun :
        (fun ω => ∑ i, |X ω i|) = ∑ i : Fin m, fun ω => |X ω i| := by
      funext ω; simp [Finset.sum_apply]
    rw [hfun]
    exact Finset.aestronglyMeasurable_sum _ (fun i _ => h_each i)
  have h_pow_meas : AEStronglyMeasurable
      (fun ω => (∑ i, |X ω i|) ^ n) μ := h_sum_meas.pow n
  by_cases hn : n = 0
  · subst hn
    simpa using (integrable_const (1 : ℝ))
  · have h_int_exp := integrable_exp_smul_sum_abs X hX h_mgf 1
    have h_const_mul :
        Integrable (fun ω => (n : ℝ) ^ n * Real.exp (∑ i, |X ω i|)) μ := by
      refine (h_int_exp.const_mul ((n : ℝ) ^ n)).congr
        (Filter.Eventually.of_forall (fun ω => ?_))
      simp [one_mul]
    refine Integrable.mono' h_const_mul h_pow_meas ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (h_bound ω) n)]
    rcases h_pow_le ω with h | h
    · exact h
    · exact absurd h hn

/-- Integrability of monomial product `∏_j X(ω)(ι j)`. -/
lemma integrable_prod_X
    {m : ℕ} (X : Ω → Fin m → ℝ) (hX : Measurable X)
    (h_mgf : ∀ t : Fin m → ℝ,
      Integrable (fun ω => Real.exp (∑ i, t i * X ω i)) μ)
    {n : ℕ} (ι : Fin n → Fin m) :
    Integrable (fun ω => ∏ j : Fin n, X ω (ι j)) μ := by
  classical
  have h_meas : AEStronglyMeasurable (fun ω => ∏ j : Fin n, X ω (ι j)) μ := by
    have h_each : ∀ j : Fin n,
        AEStronglyMeasurable (fun ω => X ω (ι j)) μ := fun j =>
      ((measurable_pi_apply (ι j)).comp hX).aestronglyMeasurable
    have hfun :
        (fun ω => ∏ j : Fin n, X ω (ι j)) = ∏ j : Fin n, fun ω => X ω (ι j) := by
      funext ω; simp [Finset.prod_apply]
    rw [hfun]
    exact Finset.aestronglyMeasurable_prod _ (fun j _ => h_each j)
  have h_int_pow := integrable_pow_sum_abs X hX h_mgf n
  refine h_int_pow.mono h_meas ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  rw [Real.norm_eq_abs]
  calc |∏ j : Fin n, X ω (ι j)|
      = ∏ j : Fin n, |X ω (ι j)| := by rw [Finset.abs_prod]
    _ ≤ ∏ j : Fin n, ∑ i, |X ω i| := by
        refine Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => ?_)
        exact Finset.single_le_sum (f := fun i => |X ω i|)
          (fun i _ => abs_nonneg _) (Finset.mem_univ (ι j))
    _ = (∑ i, |X ω i|) ^ n := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = ‖(∑ i, |X ω i|) ^ n‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        exact pow_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) _

/-! ### Moment coefficient and elementary multilinear maps -/

/-- Scalar moment coefficient `∫ ∏ⱼ X(ω) (ι j) ∂μ(ω)`. -/
noncomputable def mgfMomentCoeff {m : ℕ} (X : Ω → Fin m → ℝ) (μ : Measure Ω)
    {n : ℕ} (ι : Fin n → Fin m) : ℂ :=
  ((∫ ω, ∏ j : Fin n, X ω (ι j) ∂μ : ℝ) : ℂ)

/-- Bound on the magnitude of `mgfMomentCoeff`. -/
lemma norm_mgfMomentCoeff_le {m : ℕ} (X : Ω → Fin m → ℝ) (hX : Measurable X)
    (h_mgf : ∀ t : Fin m → ℝ,
      Integrable (fun ω => Real.exp (∑ i, t i * X ω i)) μ) {n : ℕ}
    (ι : Fin n → Fin m) :
    ‖mgfMomentCoeff X μ ι‖ ≤ ∫ ω, (∑ i, |X ω i|) ^ n ∂μ := by
  classical
  rw [mgfMomentCoeff, Complex.norm_real, Real.norm_eq_abs]
  refine (abs_integral_le_integral_abs).trans ?_
  have h_int_pow := integrable_pow_sum_abs X hX h_mgf n
  refine integral_mono ?_ h_int_pow ?_
  · exact (integrable_prod_X X hX h_mgf ι).abs
  · intro ω
    simp only [Finset.abs_prod]
    calc (∏ j, |X ω (ι j)|)
        ≤ ∏ j : Fin n, ∑ i, |X ω i| := by
          refine Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => ?_)
          exact Finset.single_le_sum (f := fun i => |X ω i|)
            (fun i _ => abs_nonneg _) (Finset.mem_univ (ι j))
      _ = (∑ i, |X ω i|) ^ n := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Elementary multilinear monomial `v ↦ ∏ⱼ v j (ι j)`. -/
noncomputable def mgfMonomialCMM {m n : ℕ} (ι : Fin n → Fin m) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin m → ℂ) ℂ :=
  ContinuousMultilinearMap.compContinuousLinearMap
    (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ)
    (fun j => ContinuousLinearMap.proj (ι j))

@[simp]
lemma mgfMonomialCMM_apply {m n : ℕ} (ι : Fin n → Fin m) (v : Fin n → Fin m → ℂ) :
    mgfMonomialCMM ι v = ∏ j : Fin n, v j (ι j) := by
  simp [mgfMonomialCMM, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

/-! ### `n`-th coefficient as a CMM -/

/-- *`n`-th coefficient.*
`p_n(v) := (1/n!) · ∑_ι (mgfMomentCoeff X ι) · ∏ⱼ v j (ι j)`. -/
noncomputable def mgfCoeffCMM {m : ℕ} (X : Ω → Fin m → ℝ) (μ : Measure Ω) (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin m → ℂ) ℂ :=
  (n.factorial : ℂ)⁻¹ • ∑ ι : Fin n → Fin m,
    (mgfMomentCoeff X μ ι) • mgfMonomialCMM ι

lemma mgfCoeffCMM_apply {m : ℕ} (X : Ω → Fin m → ℝ) (μ : Measure Ω) (n : ℕ)
    (v : Fin n → Fin m → ℂ) :
    mgfCoeffCMM X μ n v =
      (n.factorial : ℂ)⁻¹ * ∑ ι : Fin n → Fin m,
        mgfMomentCoeff X μ ι * ∏ j : Fin n, v j (ι j) := by
  simp only [mgfCoeffCMM, ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.sum_apply, mgfMonomialCMM_apply, smul_eq_mul]

/-! ### Diagonal evaluation -/

private lemma sum_prod_eq_pow {m n : ℕ} (y : Fin m → ℂ) (x : Fin m → ℝ) :
    ∑ ι : Fin n → Fin m,
        ∏ j : Fin n, y (ι j) * (x (ι j) : ℂ)
      = (∑ i, y i * (x i : ℂ)) ^ n := by
  classical
  rw [show ((∑ i, y i * (x i : ℂ)) ^ n : ℂ) = ∏ _j : Fin n, ∑ i, y i * (x i : ℂ) by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
  rw [Fintype.prod_sum]

/-- `mgfCoeffCMM n` evaluated on the diagonal `(y, ..., y)`. -/
lemma mgfCoeffCMM_diag {m : ℕ} (X : Ω → Fin m → ℝ) (hX : Measurable X)
    (h_mgf : ∀ t : Fin m → ℝ,
      Integrable (fun ω => Real.exp (∑ i, t i * X ω i)) μ)
    (n : ℕ) (y : Fin m → ℂ) :
    mgfCoeffCMM X μ n (fun _ => y) =
      (n.factorial : ℂ)⁻¹ * ∫ ω, (∑ i, y i * (X ω i : ℂ)) ^ n ∂μ := by
  classical
  rw [mgfCoeffCMM_apply]
  congr 1
  have h_int_each : ∀ ι : Fin n → Fin m,
      Integrable (fun ω => (∏ j : Fin n, y (ι j) * (X ω (ι j) : ℂ))) μ := by
    intro ι
    have h_meas : AEStronglyMeasurable
        (fun ω => ∏ j : Fin n, y (ι j) * (X ω (ι j) : ℂ)) μ := by
      have h_each : ∀ j : Fin n,
          AEStronglyMeasurable (fun ω => y (ι j) * (X ω (ι j) : ℂ)) μ := fun j =>
        (continuous_const.mul Complex.continuous_ofReal).comp_aestronglyMeasurable
          ((measurable_pi_apply (ι j)).comp hX).aestronglyMeasurable
      have hfun :
          (fun ω => ∏ j : Fin n, y (ι j) * (X ω (ι j) : ℂ))
            = ∏ j : Fin n, fun ω => y (ι j) * (X ω (ι j) : ℂ) := by
        funext ω; simp [Finset.prod_apply]
      rw [hfun]
      exact Finset.aestronglyMeasurable_prod _ (fun j _ => h_each j)
    have h_bound : ∀ ω,
        ‖∏ j : Fin n, y (ι j) * (X ω (ι j) : ℂ)‖
          ≤ (∏ j, ‖y (ι j)‖) * (∑ i, |X ω i|) ^ n := by
      intro ω
      rw [norm_prod]
      have h1 : ∀ j, ‖y (ι j) * (X ω (ι j) : ℂ)‖ = ‖y (ι j)‖ * |X ω (ι j)| := by
        intro j; rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simp_rw [h1]
      rw [Finset.prod_mul_distrib]
      gcongr ?_ * ?_
      calc (∏ j : Fin n, |X ω (ι j)|)
          ≤ ∏ j : Fin n, ∑ i, |X ω i| := by
            refine Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => ?_)
            exact Finset.single_le_sum (f := fun i => |X ω i|)
              (fun i _ => abs_nonneg _) (Finset.mem_univ (ι j))
        _ = (∑ i, |X ω i|) ^ n := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    refine Integrable.mono'
      ((integrable_pow_sum_abs X hX h_mgf n).const_mul (∏ j, ‖y (ι j)‖))
      h_meas (Filter.Eventually.of_forall (fun ω => h_bound ω))
  have h_each_eq : ∀ ι : Fin n → Fin m,
      mgfMomentCoeff X μ ι * ∏ j, y (ι j) =
      ∫ ω, ∏ j : Fin n, y (ι j) * (X ω (ι j) : ℂ) ∂μ := by
    intro ι
    rw [mgfMomentCoeff]
    rw [show ((∫ ω, ∏ j : Fin n, X ω (ι j) ∂μ : ℝ) : ℂ)
          = ∫ ω, ((∏ j : Fin n, X ω (ι j) : ℝ) : ℂ) ∂μ from
        (integral_ofReal (μ := μ) (f := fun ω => ∏ j : Fin n, X ω (ι j))).symm]
    rw [show (∫ ω, ((∏ j : Fin n, X ω (ι j) : ℝ) : ℂ) ∂μ) * (∏ j, y (ι j))
          = ∫ ω, ((∏ j : Fin n, X ω (ι j) : ℝ) : ℂ) * (∏ j, y (ι j)) ∂μ from
      (integral_mul_const (∏ j, y (ι j))
        (fun ω => ((∏ j : Fin n, X ω (ι j) : ℝ) : ℂ))).symm]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    push_cast
    rw [Finset.prod_mul_distrib (s := (Finset.univ : Finset (Fin n)))
      (f := fun j => y (ι j)) (g := fun j => (X ω (ι j) : ℂ))]
    ring
  rw [show ∑ ι : Fin n → Fin m, mgfMomentCoeff X μ ι * ∏ j, y (ι j)
        = ∑ ι : Fin n → Fin m,
            ∫ ω, ∏ j : Fin n, y (ι j) * (X ω (ι j) : ℂ) ∂μ from
      Finset.sum_congr rfl (fun ι _ => h_each_eq ι)]
  rw [← integral_finset_sum _ (fun ι _ => h_int_each ι)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
  exact sum_prod_eq_pow y (X ω)

/-! ### Formal multilinear series -/

/-- The formal multilinear series for the multivariate complex MGF. -/
noncomputable def mgfFormalSeries {m : ℕ} (X : Ω → Fin m → ℝ) (μ : Measure Ω) :
    FormalMultilinearSeries ℂ (Fin m → ℂ) ℂ :=
  fun n => mgfCoeffCMM X μ n

/-! ### Pointwise sum -/

/-- *Pointwise sum at `y`.* The series of `mgfCoeffCMM n (fun _ => y)`
sums to `F(y) := ∫ Complex.exp(∑ yᵢ Xᵢ) ∂μ`. -/
lemma hasSum_mgfFormalSeries_diag {m : ℕ} (X : Ω → Fin m → ℝ) (hX : Measurable X)
    (h_mgf : ∀ t : Fin m → ℝ,
      Integrable (fun ω => Real.exp (∑ i, t i * X ω i)) μ)
    (y : Fin m → ℂ) :
    HasSum (fun n : ℕ => mgfCoeffCMM X μ n (fun _ => y))
      (∫ ω, Complex.exp (∑ i, y i * (X ω i : ℂ)) ∂μ) := by
  classical
  -- Setup: v(ω) := ∑ y_i · (X i ω : ℂ); u(ω) := ∑ ‖y_i‖ · |X i ω|.
  set v : Ω → ℂ := fun ω => ∑ i, y i * (X ω i : ℂ) with hv
  set u : Ω → ℝ := fun ω => ∑ i, ‖y i‖ * |X ω i| with hu
  have hv_le_u : ∀ ω, ‖v ω‖ ≤ u ω := by
    intro ω
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hu_nn : ∀ ω, 0 ≤ u ω := fun ω =>
    Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (abs_nonneg _))
  have hu_meas : AEStronglyMeasurable u μ := by
    have h_each_aem : ∀ i : Fin m,
        AEStronglyMeasurable (fun ω => ‖y i‖ * |X ω i|) μ := fun i =>
      (continuous_const.mul continuous_abs).comp_aestronglyMeasurable
        ((measurable_pi_apply i).comp hX).aestronglyMeasurable
    have hfun : u = ∑ i : Fin m, fun ω => ‖y i‖ * |X ω i| := by
      funext ω; simp [hu, Finset.sum_apply]
    rw [hfun]
    exact Finset.aestronglyMeasurable_sum _ (fun i _ => h_each_aem i)
  have hu_int : Integrable (fun ω => Real.exp (u ω)) μ := by
    have hM_max : ∀ i, ‖y i‖ ≤ ∑ j, ‖y j‖ :=
      fun i => Finset.single_le_sum (f := fun j => ‖y j‖)
        (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    have hu_bound : ∀ ω, u ω ≤ (∑ i, ‖y i‖) * ∑ i, |X ω i| := by
      intro ω
      simp only [hu]
      calc ∑ i, ‖y i‖ * |X ω i|
          ≤ ∑ i, (∑ j, ‖y j‖) * |X ω i| := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            gcongr
            exact hM_max i
        _ = (∑ j, ‖y j‖) * ∑ i, |X ω i| := by rw [← Finset.mul_sum]
    refine Integrable.mono' (integrable_exp_smul_sum_abs X hX h_mgf (∑ i, ‖y i‖))
      (Real.continuous_exp.comp_aestronglyMeasurable hu_meas)
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (hu_bound ω)
  have hv_meas : AEStronglyMeasurable v μ := by
    have h_each : ∀ i : Fin m,
        AEStronglyMeasurable (fun ω => y i * (X ω i : ℂ)) μ := fun i =>
      (continuous_const.mul Complex.continuous_ofReal).comp_aestronglyMeasurable
        ((measurable_pi_apply i).comp hX).aestronglyMeasurable
    have hfun : v = ∑ i : Fin m, fun ω => y i * (X ω i : ℂ) := by
      funext ω; simp [hv, Finset.sum_apply]
    rw [hfun]
    exact Finset.aestronglyMeasurable_sum _ (fun i _ => h_each i)
  -- Partial sums s_N(ω) := ∑_{n<N} v(ω)^n / n!.
  set s : ℕ → Ω → ℂ := fun N ω => ∑ n ∈ Finset.range N, v ω ^ n / (n.factorial : ℂ)
    with hs_def
  have h_pt_taylor : ∀ ω,
      HasSum (fun n : ℕ => v ω ^ n / (n.factorial : ℂ)) (Complex.exp (v ω)) := by
    intro ω
    have h := NormedSpace.expSeries_div_hasSum_exp (v ω)
    have heq : Complex.exp (v ω) = NormedSpace.exp (v ω) := by
      rw [Complex.exp_eq_exp_ℂ]
    rw [heq]
    exact h
  have h_pt : ∀ ω, Tendsto (fun N => s N ω) atTop (𝓝 (Complex.exp (v ω))) :=
    fun ω => (h_pt_taylor ω).tendsto_sum_nat
  have h_sN_bd : ∀ N ω, ‖s N ω‖ ≤ Real.exp (u ω) := by
    intro N ω
    refine (norm_sum_le _ _).trans ?_
    have h_each : ∀ n ∈ Finset.range N,
        ‖v ω ^ n / (n.factorial : ℂ)‖ ≤ u ω ^ n / (n.factorial : ℝ) := by
      intro n _
      rw [norm_div, norm_pow, Complex.norm_natCast]
      have hfact_pos : (0 : ℝ) < (n.factorial : ℝ) :=
        by exact_mod_cast Nat.factorial_pos n
      gcongr
      exact hv_le_u ω
    refine (Finset.sum_le_sum h_each).trans ?_
    by_cases hN : N = 0
    · subst hN; simpa using (Real.exp_pos _).le
    · exact Real.sum_le_exp_of_nonneg (hu_nn ω) N
  have h_s_int : ∀ N, Integrable (s N) μ := by
    intro N
    have h_meas_sN : AEStronglyMeasurable (s N) μ := by
      have h_each : ∀ n : ℕ,
          AEStronglyMeasurable (fun ω => v ω ^ n / (n.factorial : ℂ)) μ := by
        intro n
        have h_inv : AEStronglyMeasurable
            (fun ω => v ω ^ n * (n.factorial : ℂ)⁻¹) μ :=
          (hv_meas.pow n).mul aestronglyMeasurable_const
        refine h_inv.congr ?_
        exact Filter.Eventually.of_forall (fun ω => by
          show (fun ω => v ω ^ n * (n.factorial : ℂ)⁻¹) ω
            = (fun ω => v ω ^ n / (n.factorial : ℂ)) ω
          simp [div_eq_mul_inv])
      have hfun : s N =
          ∑ n ∈ Finset.range N, fun ω => v ω ^ n / (n.factorial : ℂ) := by
        funext ω; simp [hs_def, Finset.sum_apply]
      rw [hfun]
      exact Finset.aestronglyMeasurable_sum _ (fun n _ => h_each n)
    refine Integrable.mono' hu_int h_meas_sN
      (Filter.Eventually.of_forall (fun ω => h_sN_bd N ω))
  -- DCT: ∫ s_N → ∫ exp(v).
  have h_lim_sN_int : Tendsto (fun N => ∫ ω, s N ω ∂μ) atTop
      (𝓝 (∫ ω, Complex.exp (v ω) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence
      (bound := fun ω => Real.exp (u ω))
      (fun N => (h_s_int N).aestronglyMeasurable) hu_int
      (fun N => Filter.Eventually.of_forall (fun ω => h_sN_bd N ω))
      (Filter.Eventually.of_forall h_pt)
  -- v^n is integrable: ‖v‖^n ≤ ((∑ ‖y‖)^n) · (∑ |X|)^n which is integrable.
  have hyn := (∑ i, ‖y i‖ : ℝ)
  have h_v_pow_int : ∀ n, Integrable (fun ω => v ω ^ n) μ := by
    intro n
    refine Integrable.mono'
      ((integrable_pow_sum_abs X hX h_mgf n).const_mul ((∑ i, ‖y i‖) ^ n))
      (hv_meas.pow n)
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [norm_pow]
    have h_le_u : ‖v ω‖ ≤ u ω := hv_le_u ω
    have hM_max : ∀ i, ‖y i‖ ≤ ∑ j, ‖y j‖ :=
      fun i => Finset.single_le_sum (f := fun j => ‖y j‖)
        (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    have hu_bound : u ω ≤ (∑ i, ‖y i‖) * ∑ i, |X ω i| := by
      simp only [hu]
      calc ∑ i, ‖y i‖ * |X ω i|
          ≤ ∑ i, (∑ j, ‖y j‖) * |X ω i| := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            gcongr
            exact hM_max i
        _ = (∑ j, ‖y j‖) * ∑ i, |X ω i| := by rw [← Finset.mul_sum]
    have h_v_bd : ‖v ω‖ ≤ (∑ i, ‖y i‖) * ∑ i, |X ω i| := h_le_u.trans hu_bound
    have h_pow_bd : ‖v ω‖ ^ n ≤ ((∑ i, ‖y i‖) * ∑ i, |X ω i|) ^ n :=
      pow_le_pow_left₀ (norm_nonneg _) h_v_bd n
    refine h_pow_bd.trans ?_
    rw [mul_pow]
  -- Identify ∫ s_N with the partial sum ∑_{n<N} mgfCoeffCMM n (fun _ => y).
  have h_partial_eq : ∀ N,
      ∫ ω, s N ω ∂μ =
        ∑ n ∈ Finset.range N, mgfCoeffCMM X μ n (fun _ => y) := by
    intro N
    rw [hs_def]
    -- ∫ ∑_{n<N} v^n / n! = ∑_{n<N} ∫ v^n / n!.
    rw [integral_finset_sum _ (fun n _ => Integrable.div_const (h_v_pow_int n) _)]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [mgfCoeffCMM_diag X hX h_mgf n y]
    -- ∫ v^n / n! = (∫ v^n) / n! = (n!)⁻¹ · ∫ v^n.
    rw [show ∫ ω, v ω ^ n / (n.factorial : ℂ) ∂μ
          = (∫ ω, v ω ^ n ∂μ) / (n.factorial : ℂ) from
        MeasureTheory.integral_div (n.factorial : ℂ) (fun ω => v ω ^ n)]
    rw [div_eq_mul_inv, mul_comm]
  -- Combine: partial sums tend to F(y).
  have h_partial_tendsto : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, mgfCoeffCMM X μ n (fun _ => y))
      atTop (𝓝 (∫ ω, Complex.exp (v ω) ∂μ)) :=
    h_lim_sN_int.congr h_partial_eq
  -- Norm summability: bound ‖mgfCoeffCMM n (fun _ => y)‖ ≤ M^n / n! · ∫ (∑|X|)^n
  -- where M = ∑ ‖y_i‖. Use the fact that ∑ ‖y‖^n · (∫ (∑|X|)^n) / n! ≤ ∫ exp(M ∑|X|),
  -- which is integrable.
  -- Actually we use a Cauchy-test bound directly via integral tsum.
  -- ‖mgfCoeffCMM n‖ = ‖(1/n!) ∫ v^n‖ ≤ (1/n!) ∫ ‖v^n‖ ≤ (1/n!) ∫ u^n.
  -- ∑_n (∫ u^n)/n! ≤ ∫ exp(u) < ∞ (by lintegral_tsum / monotone convergence).
  -- That gives Summable (fun n => (∫ u^n)/n!).
  -- Then `Summable.of_nonneg_of_le` finishes the norm summability.
  have h_u_pow_int : ∀ n, Integrable (fun ω => u ω ^ n) μ := by
    intro n
    refine Integrable.mono'
      ((integrable_pow_sum_abs X hX h_mgf n).const_mul ((∑ i, ‖y i‖) ^ n))
      (hu_meas.pow n) (Filter.Eventually.of_forall (fun ω => ?_))
    have hM_max : ∀ i, ‖y i‖ ≤ ∑ j, ‖y j‖ :=
      fun i => Finset.single_le_sum (f := fun j => ‖y j‖)
        (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    have hu_bound : u ω ≤ (∑ i, ‖y i‖) * ∑ i, |X ω i| := by
      simp only [hu]
      calc ∑ i, ‖y i‖ * |X ω i|
          ≤ ∑ i, (∑ j, ‖y j‖) * |X ω i| := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            gcongr
            exact hM_max i
        _ = (∑ j, ‖y j‖) * ∑ i, |X ω i| := by rw [← Finset.mul_sum]
    have h_pow_bd : u ω ^ n ≤ ((∑ i, ‖y i‖) * ∑ i, |X ω i|) ^ n :=
      pow_le_pow_left₀ (hu_nn ω) hu_bound n
    rw [show ‖u ω ^ n‖ = u ω ^ n from by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hu_nn ω) n)]]
    refine h_pow_bd.trans ?_
    rw [mul_pow]
  have h_norm_bd : ∀ n, ‖mgfCoeffCMM X μ n (fun _ => y)‖ ≤
      (∫ ω, u ω ^ n ∂μ) / (n.factorial : ℝ) := by
    intro n
    rw [mgfCoeffCMM_diag X hX h_mgf n y]
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    -- Goal: (n.factorial)⁻¹ * ‖∫ ω, v^n ∂μ‖ ≤ (∫ u^n) / n!.
    have h_int_v_bd :
        ‖∫ ω, (∑ i, y i * (X ω i : ℂ)) ^ n ∂μ‖ ≤ ∫ ω, u ω ^ n ∂μ := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine integral_mono ?_ (h_u_pow_int n) (fun ω => ?_)
      · exact (h_v_pow_int n).norm
      · rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hv_le_u ω) n
    have hfact_pos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    rw [div_eq_mul_inv, mul_comm]
    refine mul_le_mul_of_nonneg_right h_int_v_bd ?_
    exact inv_nonneg.mpr hfact_pos.le
  -- Summable (fun n => (∫ u^n) / n!): use that ∑ (∫ u^n)/n! ≤ ∫ exp(u).
  -- Since u^n / n! ≥ 0 and ∑ u^n / n! = exp(u), monotone-convergence-style sum gives it.
  -- Use: HasSum_of_lt_top of nonneg + bounded partial sums.
  have h_summable_int_pow : Summable (fun n => (∫ ω, u ω ^ n ∂μ) / (n.factorial : ℝ)) := by
    -- Bound partial sums: ∑_{n<N} (∫ u^n)/n! = ∫ ∑_{n<N} u^n/n! ≤ ∫ exp(u).
    -- Use Summable.of_partial_bounded.
    refine summable_of_sum_range_le (f := fun n => (∫ ω, u ω ^ n ∂μ) / (n.factorial : ℝ))
      (c := ∫ ω, Real.exp (u ω) ∂μ)
      (fun n => ?_) (fun N => ?_)
    · refine div_nonneg ?_ (by exact_mod_cast Nat.zero_le _)
      exact integral_nonneg (fun ω => pow_nonneg (hu_nn ω) n)
    · -- ∑_{n<N} (∫ u^n)/n! = ∫ ∑_{n<N} u^n/n! ≤ ∫ exp(u).
      have h_sum_swap :
          ∑ n ∈ Finset.range N, (∫ ω, u ω ^ n ∂μ) / (n.factorial : ℝ)
            = ∫ ω, ∑ n ∈ Finset.range N, u ω ^ n / (n.factorial : ℝ) ∂μ := by
        rw [integral_finset_sum _ (fun n _ => Integrable.div_const (h_u_pow_int n) _)]
        refine Finset.sum_congr rfl (fun n _ => ?_)
        exact (MeasureTheory.integral_div (n.factorial : ℝ) (fun ω => u ω ^ n)).symm
      rw [h_sum_swap]
      refine integral_mono ?_ hu_int (fun ω => ?_)
      · refine integrable_finset_sum _ (fun n _ => Integrable.div_const (h_u_pow_int n) _)
      · by_cases hN : N = 0
        · subst hN; simp; exact (Real.exp_pos _).le
        · exact Real.sum_le_exp_of_nonneg (hu_nn ω) N
  have h_norm_summable : Summable (fun n => ‖mgfCoeffCMM X μ n (fun _ => y)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) h_norm_bd h_summable_int_pow
  -- Conclude.
  exact (hasSum_iff_tendsto_nat_of_summable_norm h_norm_summable).mpr h_partial_tendsto

/-! ### Radius bound -/

/-- *Norm bound on `p_n`.* `‖mgfCoeffCMM n‖ ≤ (∫ (∑|X|)^n dμ) / n!`. -/
lemma norm_mgfCoeffCMM_le {m : ℕ} (X : Ω → Fin m → ℝ) (hX : Measurable X)
    (h_mgf : ∀ t : Fin m → ℝ,
      Integrable (fun ω => Real.exp (∑ i, t i * X ω i)) μ) (n : ℕ) :
    ‖mgfCoeffCMM X μ n‖ ≤ (∫ ω, (∑ i, |X ω i|) ^ n ∂μ) / (n.factorial : ℝ) := by
  classical
  refine ContinuousMultilinearMap.opNorm_le_bound ?_ (fun v => ?_)
  · refine div_nonneg ?_ (by exact_mod_cast Nat.zero_le _)
    exact integral_nonneg (fun ω => pow_nonneg
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) n)
  · rw [mgfCoeffCMM_apply, norm_mul, norm_inv, Complex.norm_natCast]
    -- Goal: (n!)⁻¹ · ‖∑_ι coeff_ι · ∏_j v_j(ι j)‖ ≤ (∫.../n!) · ∏‖v_j‖.
    -- Step 1: ∑_ι |coeff_ι| ≤ ∫ (∑|X|)^n.
    have h_coeff_bd :
        ∑ ι : Fin n → Fin m, ‖mgfMomentCoeff X μ ι‖ ≤
          ∫ ω, (∑ i, |X ω i|) ^ n ∂μ := by
      have h_int_sum : Integrable
          (fun ω => ∑ ι : Fin n → Fin m, ∏ j : Fin n, |X ω (ι j)|) μ := by
        refine integrable_finset_sum _ (fun ι _ => ?_)
        -- |∏ X(ι j)| = ∏ |X(ι j)| ≤ (∑|X|)^n integrable.
        refine Integrable.mono' (integrable_pow_sum_abs X hX h_mgf n)
          ?_ (Filter.Eventually.of_forall (fun ω => ?_))
        · -- AEStronglyMeasurable of ∏ |X(ι j)|.
          have h_each : ∀ j : Fin n,
              AEStronglyMeasurable (fun ω => |X ω (ι j)|) μ := fun j =>
            continuous_abs.comp_aestronglyMeasurable
              ((measurable_pi_apply (ι j)).comp hX).aestronglyMeasurable
          have hfun :
              (fun ω => ∏ j : Fin n, |X ω (ι j)|)
                = ∏ j : Fin n, fun ω => |X ω (ι j)| := by
            funext ω; simp [Finset.prod_apply]
          rw [hfun]
          exact Finset.aestronglyMeasurable_prod _ (fun j _ => h_each j)
        · rw [Real.norm_eq_abs, abs_of_nonneg
            (Finset.prod_nonneg (fun _ _ => abs_nonneg _))]
          calc (∏ j : Fin n, |X ω (ι j)|)
              ≤ ∏ j : Fin n, ∑ i, |X ω i| := by
                refine Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => ?_)
                exact Finset.single_le_sum (f := fun i => |X ω i|)
                  (fun i _ => abs_nonneg _) (Finset.mem_univ (ι j))
            _ = (∑ i, |X ω i|) ^ n := by
                rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      calc (∑ ι : Fin n → Fin m, ‖mgfMomentCoeff X μ ι‖)
          ≤ ∑ ι : Fin n → Fin m, ∫ ω, ∏ j, |X ω (ι j)| ∂μ := by
            refine Finset.sum_le_sum (fun ι _ => ?_)
            rw [mgfMomentCoeff, Complex.norm_real, Real.norm_eq_abs]
            refine (abs_integral_le_integral_abs).trans ?_
            refine integral_mono (integrable_prod_X X hX h_mgf ι).abs ?_ (fun ω => ?_)
            · -- AEStronglyMeasurable of ∏ |X(ι j)|.
              refine Integrable.mono' (integrable_pow_sum_abs X hX h_mgf n) ?_
                (Filter.Eventually.of_forall (fun ω => ?_))
              · have h_each : ∀ j : Fin n,
                    AEStronglyMeasurable (fun ω => |X ω (ι j)|) μ := fun j =>
                  continuous_abs.comp_aestronglyMeasurable
                    ((measurable_pi_apply (ι j)).comp hX).aestronglyMeasurable
                have hfun :
                    (fun ω => ∏ j : Fin n, |X ω (ι j)|)
                      = ∏ j : Fin n, fun ω => |X ω (ι j)| := by
                  funext ω; simp [Finset.prod_apply]
                rw [hfun]
                exact Finset.aestronglyMeasurable_prod _ (fun j _ => h_each j)
              · rw [Real.norm_eq_abs, abs_of_nonneg
                  (Finset.prod_nonneg (fun _ _ => abs_nonneg _))]
                calc (∏ j : Fin n, |X ω (ι j)|)
                    ≤ ∏ j : Fin n, ∑ i, |X ω i| := by
                      refine Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => ?_)
                      exact Finset.single_le_sum (f := fun i => |X ω i|)
                        (fun i _ => abs_nonneg _) (Finset.mem_univ (ι j))
                  _ = (∑ i, |X ω i|) ^ n := by
                      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
            · rw [Finset.abs_prod]
        _ = ∫ ω, ∑ ι : Fin n → Fin m, ∏ j, |X ω (ι j)| ∂μ := by
            rw [integral_finset_sum _ (fun ι _ => ?_)]
            · refine Integrable.mono' (integrable_pow_sum_abs X hX h_mgf n) ?_
                (Filter.Eventually.of_forall (fun ω => ?_))
              · have h_each : ∀ j : Fin n,
                    AEStronglyMeasurable (fun ω => |X ω (ι j)|) μ := fun j =>
                  continuous_abs.comp_aestronglyMeasurable
                    ((measurable_pi_apply (ι j)).comp hX).aestronglyMeasurable
                have hfun :
                    (fun ω => ∏ j : Fin n, |X ω (ι j)|)
                      = ∏ j : Fin n, fun ω => |X ω (ι j)| := by
                  funext ω; simp [Finset.prod_apply]
                rw [hfun]
                exact Finset.aestronglyMeasurable_prod _ (fun j _ => h_each j)
              · rw [Real.norm_eq_abs, abs_of_nonneg
                  (Finset.prod_nonneg (fun _ _ => abs_nonneg _))]
                calc (∏ j : Fin n, |X ω (ι j)|)
                    ≤ ∏ j : Fin n, ∑ i, |X ω i| := by
                      refine Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => ?_)
                      exact Finset.single_le_sum (f := fun i => |X ω i|)
                        (fun i _ => abs_nonneg _) (Finset.mem_univ (ι j))
                  _ = (∑ i, |X ω i|) ^ n := by
                      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        _ = ∫ ω, (∑ i, |X ω i|) ^ n ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
            -- ∑_ι ∏_j |X(ι j)| = (∑_i |X i|)^n.
            change (∑ ι : Fin n → Fin m, ∏ j, |X ω (ι j)| : ℝ) = (∑ i, |X ω i|) ^ n
            rw [show ((∑ i, |X ω i|) ^ n : ℝ)
                  = ∏ _j : Fin n, ∑ i, |X ω i| from by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
            rw [Fintype.prod_sum]
    -- Step 2: combine.
    have h_sum_le :
        ‖∑ ι : Fin n → Fin m, mgfMomentCoeff X μ ι * ∏ j, v j (ι j)‖ ≤
          (∫ ω, (∑ i, |X ω i|) ^ n ∂μ) * ∏ j, ‖v j‖ := by
      refine (norm_sum_le _ _).trans ?_
      have h_each : ∀ ι ∈ (Finset.univ : Finset (Fin n → Fin m)),
          ‖mgfMomentCoeff X μ ι * ∏ j, v j (ι j)‖ ≤
            ‖mgfMomentCoeff X μ ι‖ * ∏ j, ‖v j‖ := by
        intro ι _
        rw [norm_mul, norm_prod]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        refine Finset.prod_le_prod (fun (j : Fin n) _ => norm_nonneg ((v j) (ι j)))
          (fun (j : Fin n) _ => ?_)
        exact norm_le_pi_norm (v j) (ι j)
      calc (∑ ι : Fin n → Fin m,
              ‖mgfMomentCoeff X μ ι * ∏ j, v j (ι j)‖)
          ≤ ∑ ι : Fin n → Fin m, ‖mgfMomentCoeff X μ ι‖ * ∏ j, ‖v j‖ :=
            Finset.sum_le_sum h_each
        _ = (∑ ι, ‖mgfMomentCoeff X μ ι‖) * ∏ j, ‖v j‖ := by
            rw [← Finset.sum_mul]
        _ ≤ (∫ ω, (∑ i, |X ω i|) ^ n ∂μ) * ∏ j, ‖v j‖ := by
            gcongr
    -- Combine.
    have hfact_pos : (0 : ℝ) < (n.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos n
    have hfact_inv_nn : (0 : ℝ) ≤ ((n.factorial : ℝ))⁻¹ :=
      inv_nonneg.mpr hfact_pos.le
    -- Already rewrote `‖(n!)⁻¹‖ = (n!)⁻¹` in the original `norm_inv` step.
    -- Goal: (n!)⁻¹ * ‖∑‖ ≤ (∫ ...)/n! · ∏‖v‖.
    rw [div_eq_mul_inv, mul_comm (∫ _, _ ∂_) _, mul_assoc]
    -- Now: (n!)⁻¹ * ‖∑‖ ≤ (n!)⁻¹ * ((∫) * ∏‖v‖).
    refine mul_le_mul_of_nonneg_left ?_ hfact_inv_nn
    exact h_sum_le

/-- *Radius is `⊤`.* The formal multilinear series has infinite radius. -/
lemma mgfFormalSeries_radius_top {m : ℕ} (X : Ω → Fin m → ℝ) (hX : Measurable X)
    (h_mgf : ∀ t : Fin m → ℝ,
      Integrable (fun ω => Real.exp (∑ i, t i * X ω i)) μ) :
    (mgfFormalSeries X μ).radius = ⊤ := by
  classical
  refine FormalMultilinearSeries.radius_eq_top_of_summable_norm _ ?_
  intro r
  -- Show Summable (fun n => ‖p_n‖ * r^n).
  -- Bound: ‖p_n‖ * r^n ≤ r^n · (∫ (∑|X|)^n) / n!.
  -- Then ∑_n r^n · (∫ (∑|X|)^n) / n! = ∫ ∑_n (r ∑|X|)^n / n! = ∫ exp(r ∑|X|) < ∞.
  have h_bd : ∀ n,
      ‖(mgfFormalSeries X μ) n‖ * (r : ℝ) ^ n ≤
        (∫ ω, (∑ i, |X ω i|) ^ n ∂μ) / (n.factorial : ℝ) * (r : ℝ) ^ n := by
    intro n
    refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (NNReal.coe_nonneg _) n)
    exact norm_mgfCoeffCMM_le X hX h_mgf n
  -- ∑_n ((∫ (∑|X|)^n) / n!) * r^n is summable. Use: this = ∑_n (r^n · ∫ (∑|X|)^n)/n!
  -- = ∫ ∑_n (r ∑|X|)^n / n! = ∫ exp(r ∑|X|) < ∞.
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (by positivity)) h_bd ?_
  -- Now Summable (fun n => (∫ (∑|X|)^n) / n! * r^n).
  -- Equivalent: ∫ (r ∑|X|)^n / n!.
  have h_int_pow_r_sum : ∀ n, Integrable (fun ω => ((r : ℝ) * ∑ i, |X ω i|) ^ n) μ := by
    intro n
    rw [show (fun ω : Ω => ((r : ℝ) * ∑ i, |X ω i|) ^ n)
          = (fun ω => ((r : ℝ) ^ n) * ((∑ i, |X ω i|) ^ n)) by
        funext ω; rw [mul_pow]]
    exact (integrable_pow_sum_abs X hX h_mgf n).const_mul _
  refine summable_of_sum_range_le
    (f := fun n => (∫ ω, (∑ i, |X ω i|) ^ n ∂μ) / (n.factorial : ℝ) * (r : ℝ) ^ n)
    (c := ∫ ω, Real.exp ((r : ℝ) * ∑ i, |X ω i|) ∂μ)
    (fun n => ?_) (fun N => ?_)
  · refine mul_nonneg ?_ (by positivity)
    refine div_nonneg ?_ (by exact_mod_cast Nat.zero_le _)
    exact integral_nonneg (fun ω => pow_nonneg
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) n)
  · -- ∑_{n<N} (∫ (∑|X|)^n / n! * r^n) ≤ ∫ exp(r ∑|X|).
    have h_swap :
        ∑ n ∈ Finset.range N,
            (∫ ω, (∑ i, |X ω i|) ^ n ∂μ) / (n.factorial : ℝ) * (r : ℝ) ^ n
          = ∫ ω, ∑ n ∈ Finset.range N,
              ((r : ℝ) * ∑ i, |X ω i|) ^ n / (n.factorial : ℝ) ∂μ := by
      rw [integral_finset_sum _ (fun n _ => Integrable.div_const (h_int_pow_r_sum n) _)]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      -- Goal: (∫ (∑|X|)^n) / n! * r^n = ∫ (r ∑|X|)^n / n!.
      -- RHS: pull out 1/n! via integral_div, expand (r*x)^n, pull out r^n.
      have h1 :
          (∫ a, ((r : ℝ) * ∑ i, |X a i|) ^ n / (n.factorial : ℝ) ∂μ)
            = (∫ a, ((r : ℝ) * ∑ i, |X a i|) ^ n ∂μ) / (n.factorial : ℝ) :=
        MeasureTheory.integral_div (n.factorial : ℝ)
          (fun a => ((r : ℝ) * ∑ i, |X a i|) ^ n)
      have h2 :
          (∫ a, ((r : ℝ) * ∑ i, |X a i|) ^ n ∂μ)
            = (r : ℝ) ^ n * ∫ a, (∑ i, |X a i|) ^ n ∂μ := by
        rw [show (fun a : Ω => ((r : ℝ) * ∑ i, |X a i|) ^ n)
              = (fun a => (r : ℝ) ^ n * (∑ i, |X a i|) ^ n) by
            funext a; rw [mul_pow]]
        exact integral_const_mul ((r : ℝ) ^ n) (fun a => (∑ i, |X a i|) ^ n)
      rw [h1, h2]
      ring
    rw [h_swap]
    refine integral_mono ?_ ?_ (fun ω => ?_)
    · refine integrable_finset_sum _ (fun n _ => ?_)
      exact Integrable.div_const (h_int_pow_r_sum n) _
    · -- exp(r · ∑|X|) integrable.
      have := integrable_exp_smul_sum_abs X hX h_mgf (r : ℝ)
      exact this
    · -- partial sum ≤ exp.
      by_cases hN : N = 0
      · subst hN
        simp; exact (Real.exp_pos _).le
      · refine Real.sum_le_exp_of_nonneg ?_ N
        positivity

/-! ### HasFPowerSeriesOnBall -/

/-- *HasFPowerSeriesOnBall.* The formal multilinear series represents
the multivariate complex MGF on the ball of radius `⊤` (i.e. all of
`ℂᵐ`). -/
lemma mgf_hasFPowerSeriesOnBall {m : ℕ} (X : Ω → Fin m → ℝ) (hX : Measurable X)
    (h_mgf : ∀ t : Fin m → ℝ,
      Integrable (fun ω => Real.exp (∑ i, t i * X ω i)) μ) :
    HasFPowerSeriesOnBall
      (fun z : Fin m → ℂ =>
        ∫ ω, Complex.exp (∑ i, z i * (X ω i : ℂ)) ∂μ)
      (mgfFormalSeries X μ) 0 ⊤ where
  r_le := by
    rw [mgfFormalSeries_radius_top X hX h_mgf]
  r_pos := by simp
  hasSum := by
    intro y _hy
    have h := hasSum_mgfFormalSeries_diag X hX h_mgf y
    -- F(0 + y) = F(y).
    convert! h using 2
    rw [zero_add]

/-! ### AnalyticOnNhd via the power series -/

/-- *Multivariate complex-MGF analyticity* — the headline result, derived
from `mgf_hasFPowerSeriesOnBall` + `HasFPowerSeriesOnBall.analyticOnNhd`. -/
theorem analyticOnNhd_mgf {m : ℕ} (X : Ω → Fin m → ℝ) (hX : Measurable X)
    (h_mgf : ∀ t : Fin m → ℝ,
      Integrable (fun ω => Real.exp (∑ i, t i * X ω i)) μ) :
    AnalyticOnNhd ℂ
      (fun z : Fin m → ℂ =>
        ∫ ω, Complex.exp (∑ i, z i * (X ω i : ℂ)) ∂μ)
      Set.univ := by
  have h := (mgf_hasFPowerSeriesOnBall X hX h_mgf).analyticOnNhd
  rw [Metric.eball_top] at h
  exact h

end AsymptoticStatistics.ForMathlib.MultivariateComplexMGFCoeff
