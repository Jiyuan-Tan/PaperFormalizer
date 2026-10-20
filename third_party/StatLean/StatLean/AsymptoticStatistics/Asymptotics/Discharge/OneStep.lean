module
public import StatLean.AsymptoticStatistics.Asymptotics.OneStep
public import Mathlib.Algebra.Order.Chebyshev
public import StatLean.AsymptoticStatistics.ForMathlib.IIdJointLaw
public import StatLean.AsymptoticStatistics.ForMathlib.IidWLLN
public import Mathlib.Probability.StrongLaw
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# One-step estimator: Taylor-based discharge layer

Establishes asymptotic linearity of the one-step estimator from **Taylor-in-θ
regularity** of the score estimator at the preliminary, plus the Bartlett
identity, the plug-in info-estimator formula, and the √n-rate of the
preliminary. Per vdV's remark: under stronger regularity conditions, the
Pfanzagl second-order display can also be proved by a Taylor expansion of
`ℓ̃_{θ,η}` in θ; this file implements that route.

The strong-regularity conditions are bundled in `OneStepTaylorHyp`. From them,
`OneStepTaylorHyp.pfanzagl_display` and `OneStepTaylorHyp.info_consistency` are
derived, and `oneStep_asympLinear_of_taylor` proves the main asymptotic-linearity
statement by decomposing the residual into three error terms each tending to 0 in
Pⁿ-probability.

Reference: vdV §25.8 thm:25.57 + Taylor strong-regularity remark.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace ENNReal Function

namespace AsymptoticStatistics.Asymptotics.Discharge.OneStep

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.Asymptotics.OneStep

variable {Ω : Type*} [MeasurableSpace Ω]

/-- *Strong-regularity hypothesis bundle for the one-step estimator discharge.*

Exposes the **Taylor-in-θ regularity** as the load-bearing condition. Per vdV:
under stronger regularity conditions, the Pfanzagl second-order display can also
be proved by a Taylor expansion of `ℓ̃_{θ,η}` in θ. This structure encodes that
route.

**Parameters** (in addition to the standard ones for the estimator setup):
- `score_l_dot : Lp ℝ 2 P` — the L²(P) derivative `ℓ̇` of `θ → ℓ̃_{θ,η}` at θ₀.

**Fields**:
1. `hI_pos`: `Ĩ > 0` (efficient information positive).
2. `score_l_dot_bartlett`: `E_P[ℓ̇] = -Ĩ` (Bartlett identity for the efficient score).
3. `info_plug_in_def`: `Î_n = (1/n) Σᵢ (ℓ̂_n)²` (plug-in 2nd-moment estimator formula).
4. `score_l2_taylor`: `Σᵢ r_n(Xᵢ)² →_P 0` where `r_n` is the empirical Taylor remainder.
5. `preliminary_sqrt_n_rate`: `√n·(θ̃_n − θ₀) = O_P(1)`.

Both `pfanzagl_display` and `info_consistency` are derived theorems on this
structure: `OneStepTaylorHyp.pfanzagl_display` and `OneStepTaylorHyp.info_consistency`.

Reference: vdV §25.8 thm:25.57 + Taylor strong-regularity remark. -/
structure OneStepTaylorHyp
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (v : Θ)
    (preliminary : ∀ n, (Fin n → Ω) → ℝ)
    (score_estimate_seq : ℕ → Ω → ℝ → ℝ)
    (info_estimate_seq : ∀ n, (Fin n → Ω) → ℝ)
    (score_l_dot : Lp ℝ 2 P)
    (θ₀ : ℝ) : Prop where
  /-- vdV §25.4: efficient information is positive. -/
  hI_pos : 0 < efficientInformation S_θ T_nuis v
  /-- vdV §25.4 (Bartlett identity for the efficient score):
  `E_P[ℓ̇] = -Ĩ`. Derived in vdV by differentiating `E_{P_{θ,η}}[ℓ̃_{θ,η}] = 0`
  in θ; we take it as a primitive condition on `score_l_dot`. -/
  score_l_dot_bartlett :
    ∫ ω, (score_l_dot : Ω → ℝ) ω ∂P = -efficientInformation S_θ T_nuis v
  /-- vdV §25.8 (one-step construction / proof of thm:25.57): the information estimator equals
  the empirical 2nd moment of the score estimator at the preliminary. -/
  info_plug_in_def : ∀ n (X : Fin n → Ω),
    info_estimate_seq n X
      = (n : ℝ)⁻¹ * ∑ i : Fin n, (score_estimate_seq n (X i) (preliminary n X)) ^ 2
  /-- vdV §25.8 (strong regularity, Taylor remark):
  empirical L²-Taylor remainder vanishes faster than 1/n. Specifically:
  `Σᵢ r_n(Xᵢ)² →_P 0` where
  `r_n(X) := score_estimate_seq n (X) (θ̃_n) − ℓ̃(X) − (θ̃_n − θ₀)·ℓ̇(X)`.
  Equivalent to `(1/n) Σᵢ r_n²(Xᵢ) = oP(1/n)`. By Cauchy-Schwarz this implies
  `√n · (1/n) Σᵢ r_n(Xᵢ) →_P 0`, the Taylor-form Pfanzagl remainder. -/
  score_l2_taylor : ∀ ε > 0, Tendsto
    (fun n : ℕ =>
      let scoreEff : Ω → ℝ :=
        ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ ∑ i : Fin n,
            (score_estimate_seq n (X i) (preliminary n X)
              - scoreEff (X i)
              - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)) ^ 2})
    atTop (nhds 0)
  /-- vdV §25.8: preliminary achieves the √n-rate: O_P(1).
  For every ε > 0 there is a uniform bound M such that
  `Pⁿ(|√n·(θ̃_n − θ₀)| ≥ M) ≤ ε` for all n. -/
  preliminary_sqrt_n_rate : ∀ ε > 0, ∃ M : ℝ, ∀ n : ℕ,
    (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω |
        M ≤ abs (Real.sqrt n * (preliminary n X - θ₀))}
    ≤ ENNReal.ofReal ε

/-- **L²-norm-square ↔ integral identity for the efficient score.**

`∫ scoreEff² dP = Ĩ` where `Ĩ := ‖efficientScore‖²` (definitional). -/
private lemma eff_score_sq_integral
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ} :
    ∫ ω, (((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) :
              Ω → ℝ) ω ^ 2 ∂P
    = efficientInformation S_θ T_nuis v := by
  unfold efficientInformation
  set f : Lp ℝ 2 P :=
    ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) with hf_def
  change ∫ ω, (f : Ω → ℝ) ω ^ 2 ∂P = ‖efficientScore S_θ T_nuis v‖ ^ 2
  have h_norm_eq : (‖efficientScore S_θ T_nuis v‖ : ℝ) ^ 2 = ‖f‖ ^ 2 := rfl
  rw [h_norm_eq, ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  change ((f : Ω → ℝ) ω) ^ 2 = ⟪(f : Ω → ℝ) ω, (f : Ω → ℝ) ω⟫_ℝ
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- **Normalized efficient-score sum is bounded in probability** (O_P(1)).

For all ε > 0, ∃ M such that for all n,
  `Pⁿ(|(1/√n)·Σᵢ ℓ̃(Xᵢ)| ≥ M) ≤ ε`.

**Proof.** Chebyshev with the variance identity
`Var^Pⁿ[(1/√n)·Σ ℓ̃(X_i)] = (1/n)·n·Var^P[ℓ̃] = Ĩ` (using `variance_sum_pi`
+ mean-zero property of `L2ZeroMean P` + `eff_score_sq_integral`).
Take `M = √(Ĩ/ε + 1)`. -/
private lemma score_sum_bddAbove_in_prob
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    (hI_pos : 0 < efficientInformation S_θ T_nuis v) :
    let scoreEff : Ω → ℝ :=
      ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
    ∀ ε > 0, ∃ M : ℝ, ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          M ≤ abs ((Real.sqrt n)⁻¹ * (∑ i : Fin n, scoreEff (X i)))}
      ≤ ENNReal.ofReal ε := by
  intro scoreEff ε hε
  set scoreLp : Lp ℝ 2 P := ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
    with hSLp
  set Ĩ := efficientInformation S_θ T_nuis v with hĨ
  have hĨ_nn : 0 ≤ Ĩ := hI_pos.le
  have hScoreEff_memLp : MemLp scoreEff 2 P := Lp.memLp scoreLp
  -- Mean-zero of scoreEff under P (since scoreLp ∈ L2ZeroMean P).
  have h_mean : ∫ ω, scoreEff ω ∂P = 0 := by
    have h_in_ker : scoreLp ∈ LinearMap.ker (integralL2 P).toLinearMap :=
      (efficientScore S_θ T_nuis v).2
    rw [LinearMap.mem_ker] at h_in_ker
    have h_bridge : integralL2 P scoreLp = ∫ ω, scoreEff ω ∂P := by
      change ⟪oneL2 P, scoreLp⟫_ℝ = _
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      have h_one_ae : ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] fun _ => (1 : ℝ) :=
        MemLp.coeFn_toLp (memLp_const (1 : ℝ))
      filter_upwards [h_one_ae] with a ha
      have hcomm : ⟪((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a, (scoreLp : Ω → ℝ) a⟫_ℝ
                  = (scoreLp : Ω → ℝ) a * ((oneL2 P : Lp ℝ 2 P) : Ω → ℝ) a := rfl
      rw [hcomm, ha]; ring
    rw [← h_bridge]; exact h_in_ker
  have h_sq : ∫ ω, scoreEff ω ^ 2 ∂P = Ĩ := eff_score_sq_integral
  have h_var_P : variance scoreEff P = Ĩ := by
    rw [variance_eq_integral hScoreEff_memLp.aestronglyMeasurable.aemeasurable]
    simp_rw [h_mean, sub_zero]
    exact h_sq
  refine ⟨Real.sqrt (Ĩ / ε + 1), fun n => ?_⟩
  have hM_pos : 0 < Real.sqrt (Ĩ / ε + 1) :=
    Real.sqrt_pos.mpr (by positivity)
  have hM_sq : Real.sqrt (Ĩ / ε + 1) ^ 2 = Ĩ / ε + 1 :=
    Real.sq_sqrt (by positivity)
  haveI hPn_prob : IsProbabilityMeasure (Measure.pi (fun _ : Fin n => P)) := inferInstance
  have h_each_memLp : ∀ i : Fin n,
      MemLp (fun ω : Fin n → Ω => scoreEff (ω i)) 2 (Measure.pi (fun _ : Fin n => P)) := by
    intro i
    have h_mp := MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => P) i
    exact hScoreEff_memLp.comp_measurePreserving h_mp
  have h_var_sum :
      variance (∑ i : Fin n, fun ω : Fin n → Ω => scoreEff (ω i))
        (Measure.pi (fun _ : Fin n => P)) = (n : ℝ) * Ĩ := by
    rw [variance_sum_pi (fun _ : Fin n => hScoreEff_memLp)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, h_var_P, nsmul_eq_mul]
  set S : (Fin n → Ω) → ℝ := fun ω => ∑ i : Fin n, scoreEff (ω i) with hS_def
  have h_S_eq : (∑ i : Fin n, fun ω : Fin n → Ω => scoreEff (ω i)) = S := by
    funext ω
    simp [hS_def, Finset.sum_apply]
  have h_var_S : variance S (Measure.pi (fun _ : Fin n => P)) = (n : ℝ) * Ĩ :=
    h_S_eq ▸ h_var_sum
  have h_each_int : ∀ i : Fin n,
      Integrable (fun ω : Fin n → Ω => scoreEff (ω i))
        (Measure.pi (fun _ : Fin n => P)) :=
    fun i => (h_each_memLp i).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_each_mean : ∀ i : Fin n,
      ∫ ω, scoreEff (ω i) ∂(Measure.pi (fun _ : Fin n => P)) = 0 := by
    intro i
    have h_mp := MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => P) i
    have h_aem : AEMeasurable (fun ω : Fin n → Ω => ω i)
        (Measure.pi (fun _ : Fin n => P)) := (measurable_pi_apply i).aemeasurable
    have h_aesm : AEStronglyMeasurable scoreEff
        ((Measure.pi (fun _ : Fin n => P)).map (fun ω : Fin n → Ω => ω i)) := by
      rw [show (fun ω : Fin n → Ω => ω i) = Function.eval i from rfl, h_mp.map_eq]
      exact hScoreEff_memLp.aestronglyMeasurable
    calc ∫ ω, scoreEff (ω i) ∂(Measure.pi (fun _ : Fin n => P))
        = ∫ ω, scoreEff ((fun ω : Fin n → Ω => ω i) ω) ∂(Measure.pi (fun _ : Fin n => P)) :=
          rfl
      _ = ∫ x, scoreEff x ∂((Measure.pi (fun _ : Fin n => P)).map
              (fun ω : Fin n → Ω => ω i)) := (integral_map h_aem h_aesm).symm
      _ = ∫ x, scoreEff x ∂P := by
            rw [show (fun ω : Fin n → Ω => ω i) = Function.eval i from rfl, h_mp.map_eq]
      _ = 0 := h_mean
  have h_S_mean : ∫ ω, S ω ∂(Measure.pi (fun _ : Fin n => P)) = 0 := by
    rw [hS_def]
    rw [integral_finset_sum _ (fun i _ => h_each_int i)]
    simp [h_each_mean]
  have h_S_memLp : MemLp S 2 (Measure.pi (fun _ : Fin n => P)) := by
    change MemLp (fun ω : Fin n → Ω => ∑ i : Fin n, scoreEff (ω i))
        2 (Measure.pi (fun _ : Fin n => P))
    exact memLp_finset_sum Finset.univ (fun i _ => h_each_memLp i)
  by_cases hn : n = 0
  · subst hn
    refine le_trans (le_of_eq ?_) (zero_le)
    convert measure_empty (μ := Measure.pi (fun _ : Fin 0 => P))
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    have h_sum_zero : ∑ i : Fin 0, scoreEff (X i) = 0 := by
      apply Finset.sum_of_isEmpty
    rw [h_sum_zero, mul_zero, abs_zero]
    exact hM_pos
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have h_sqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  set c : ℝ := (Real.sqrt n)⁻¹ with hc_def
  set X : (Fin n → Ω) → ℝ := fun ω => c * S ω with hX_def
  have h_X_mean : ∫ ω, X ω ∂(Measure.pi (fun _ : Fin n => P)) = 0 := by
    simp [hX_def, integral_const_mul, h_S_mean]
  have h_X_var : variance X (Measure.pi (fun _ : Fin n => P)) = Ĩ := by
    rw [hX_def, variance_const_mul, h_var_S]
    have hc_sq : c ^ 2 = (n : ℝ)⁻¹ := by
      rw [hc_def, inv_pow, Real.sq_sqrt hn_pos.le]
    rw [hc_sq]; field_simp
  have h_X_memLp : MemLp X 2 (Measure.pi (fun _ : Fin n => P)) := by
    rw [hX_def]
    exact h_S_memLp.const_mul c
  have h_cheb := meas_ge_le_variance_div_sq h_X_memLp hM_pos
  rw [h_X_mean] at h_cheb
  simp only [sub_zero] at h_cheb
  rw [h_X_var, hM_sq] at h_cheb
  refine h_cheb.trans ?_
  apply ENNReal.ofReal_le_ofReal
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < Ĩ / ε + 1)]
  have key : ε * (Ĩ / ε + 1) = Ĩ + ε := by
    field_simp
  linarith [hε.le]

/-- **Info convergence implies `(1 − Î_n⁻¹·Ĩ) →_P 0`.**

Given `Î_n →_P Ĩ` (h_info) and `Ĩ > 0` (hI_pos), for every δ > 0,
`Pⁿ({X | δ ≤ |1 − (Î_n X)⁻¹ · Ĩ|}) → 0`.

Proof: algebraic inclusion
`{δ ≤ |1 − Î⁻¹Ĩ|} ⊆ {Ĩ/2 ≤ |Î − Ĩ|} ∪ {δ·Ĩ/2 ≤ |Î − Ĩ|}`,
then squeeze both terms to 0 via h_info. -/
private lemma info_mul_inv_oP
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {info_estimate_seq : ∀ n, (Fin n → Ω) → ℝ}
    (hI_pos : 0 < efficientInformation S_θ T_nuis v)
    (h_info : ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | ε ≤ abs (info_estimate_seq n X - efficientInformation S_θ T_nuis v)})
      atTop (nhds 0)) :
    ∀ δ > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          δ ≤ abs (1 - (info_estimate_seq n X)⁻¹ * efficientInformation S_θ T_nuis v)})
      atTop (nhds 0) := by
  set Ĩ := efficientInformation S_θ T_nuis v
  intro δ hδ
  -- Key algebraic fact: {|1 − Î⁻¹Ĩ| ≥ δ} ⊆ {|Î − Ĩ| ≥ Ĩ/2} ∪ {|Î − Ĩ| ≥ δ·Ĩ/2}
  have h_alg : ∀ n (X : Fin n → Ω),
      δ ≤ abs (1 - (info_estimate_seq n X)⁻¹ * Ĩ) →
      Ĩ / 2 ≤ abs (info_estimate_seq n X - Ĩ) ∨
      δ * Ĩ / 2 ≤ abs (info_estimate_seq n X - Ĩ) := by
    intro n X hX
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    -- From h1: Î > Ĩ/2 (since |Î − Ĩ| < Ĩ/2 → Î > Ĩ − Ĩ/2 = Ĩ/2)
    have hÎ_lower : Ĩ / 2 < info_estimate_seq n X := by
      linarith [neg_abs_le (info_estimate_seq n X - Ĩ), hI_pos]
    have hÎ_pos : 0 < info_estimate_seq n X := lt_trans (by positivity) hÎ_lower
    -- |1 − Î⁻¹Ĩ| = |Î − Ĩ| / Î
    have h_eq : 1 - (info_estimate_seq n X)⁻¹ * Ĩ
        = (info_estimate_seq n X - Ĩ) / info_estimate_seq n X := by
      field_simp
    rw [h_eq, abs_div, abs_of_pos hÎ_pos] at hX
    -- hX : δ ≤ |Î − Ĩ| / Î; contradicts |Î − Ĩ| / Î < δ
    -- From hX, multiplying by Î > 0: δ·Î ≤ |Î − Ĩ|
    have h_prod : δ * info_estimate_seq n X ≤ abs (info_estimate_seq n X - Ĩ) := by
      have hmul := mul_le_mul_of_nonneg_right hX hÎ_pos.le
      have hcancel : abs (info_estimate_seq n X - Ĩ) / info_estimate_seq n X
          * info_estimate_seq n X = abs (info_estimate_seq n X - Ĩ) := by
        field_simp
      linarith [hcancel ▸ hmul]
    -- But |Î − Ĩ| < δ·Ĩ/2 ≤ δ·Î (from h2 + hÎ_lower)
    have h_num : abs (info_estimate_seq n X - Ĩ) < δ * info_estimate_seq n X :=
      calc abs (info_estimate_seq n X - Ĩ) < δ * Ĩ / 2 := h2
        _ ≤ δ * info_estimate_seq n X := by nlinarith [hδ.le, hÎ_lower.le]
    linarith
  -- Measure bound via union bound
  have h_meas : ∀ n,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | δ ≤ abs (1 - (info_estimate_seq n X)⁻¹ * Ĩ)}
      ≤ (Measure.pi (fun _ : Fin n => P)) {X | Ĩ / 2 ≤ abs (info_estimate_seq n X - Ĩ)} +
        (Measure.pi (fun _ : Fin n => P)) {X | δ * Ĩ / 2 ≤ abs (info_estimate_seq n X - Ĩ)} := by
    intro n
    apply (measure_mono _).trans (measure_union_le _ _)
    intro X hX
    simp only [Set.mem_union, Set.mem_setOf_eq]
    exact h_alg n X hX
  -- Both bounds → 0 by h_info; squeeze
  have h1 := h_info (Ĩ / 2) (by positivity)
  have h2 := h_info (δ * Ĩ / 2) (by positivity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
  · simpa using h1.add h2
  · exact Filter.Eventually.of_forall fun _ => zero_le
  · exact Filter.Eventually.of_forall fun n => h_meas n

/-- **Info convergence implies `(Î_n⁻¹ − Ĩ⁻¹) →_P 0`.**

Given `Î_n →_P Ĩ` and `Ĩ > 0`, for every δ > 0,
`Pⁿ({X | δ ≤ |Î_n(X)⁻¹ − Ĩ⁻¹|}) → 0`.

Proof: algebraic inclusion
`{δ ≤ |Î⁻¹ − Ĩ⁻¹|} ⊆ {Ĩ/2 ≤ |Î − Ĩ|} ∪ {δ·Ĩ²/4 ≤ |Î − Ĩ|}`. -/
private lemma info_inv_diff_oP
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {info_estimate_seq : ∀ n, (Fin n → Ω) → ℝ}
    (hI_pos : 0 < efficientInformation S_θ T_nuis v)
    (h_info : ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | ε ≤ abs (info_estimate_seq n X - efficientInformation S_θ T_nuis v)})
      atTop (nhds 0)) :
    ∀ δ > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          δ ≤ abs ((info_estimate_seq n X)⁻¹ - (efficientInformation S_θ T_nuis v)⁻¹)})
      atTop (nhds 0) := by
  set Ĩ := efficientInformation S_θ T_nuis v
  intro δ hδ
  -- Key: {|Î⁻¹ − Ĩ⁻¹| ≥ δ} ⊆ {|Î − Ĩ| ≥ Ĩ/2} ∪ {|Î − Ĩ| ≥ δ·Ĩ²/4}
  have h_alg : ∀ n (X : Fin n → Ω),
      δ ≤ abs ((info_estimate_seq n X)⁻¹ - Ĩ⁻¹) →
      Ĩ / 2 ≤ abs (info_estimate_seq n X - Ĩ) ∨
      δ * Ĩ ^ 2 / 4 ≤ abs (info_estimate_seq n X - Ĩ) := by
    intro n X hX
    by_contra hc
    push Not at hc
    obtain ⟨h1, h2⟩ := hc
    have hÎ_lower : Ĩ / 2 < info_estimate_seq n X := by
      linarith [neg_abs_le (info_estimate_seq n X - Ĩ), hI_pos]
    have hÎ_pos : 0 < info_estimate_seq n X := lt_trans (by positivity) hÎ_lower
    -- |Î⁻¹ − Ĩ⁻¹| = |Î − Ĩ| / (Î·Ĩ)
    have h_eq : (info_estimate_seq n X)⁻¹ - Ĩ⁻¹
        = (Ĩ - info_estimate_seq n X) / (info_estimate_seq n X * Ĩ) := by
      field_simp
    rw [h_eq, abs_div, abs_of_pos (mul_pos hÎ_pos hI_pos)] at hX
    have hprod_lower : Ĩ ^ 2 / 4 < info_estimate_seq n X * Ĩ := by
      nlinarith [hÎ_lower, hI_pos]
    -- From hX (multiplied by Î·Ĩ > 0): δ·(Î·Ĩ) ≤ |Ĩ − Î|
    have h_prod : δ * (info_estimate_seq n X * Ĩ)
        ≤ abs (Ĩ - info_estimate_seq n X) := by
      have hmul := mul_le_mul_of_nonneg_right hX (mul_pos hÎ_pos hI_pos).le
      have hcancel : abs (Ĩ - info_estimate_seq n X) / (info_estimate_seq n X * Ĩ)
          * (info_estimate_seq n X * Ĩ) = abs (Ĩ - info_estimate_seq n X) := by
        field_simp
      linarith [hcancel ▸ hmul]
    -- But |Ĩ − Î| = |Î − Ĩ| < δ·Ĩ²/4 < δ·(Î·Ĩ) (from h2 + hprod_lower)
    have h_num : abs (Ĩ - info_estimate_seq n X) < δ * (info_estimate_seq n X * Ĩ) :=
      calc abs (Ĩ - info_estimate_seq n X)
          = abs (info_estimate_seq n X - Ĩ) := abs_sub_comm _ _
        _ < δ * Ĩ ^ 2 / 4 := h2
        _ < δ * (info_estimate_seq n X * Ĩ) := by nlinarith [hδ.le, hprod_lower]
    linarith
  have h_meas : ∀ n,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | δ ≤ abs ((info_estimate_seq n X)⁻¹ - Ĩ⁻¹)}
      ≤ (Measure.pi (fun _ : Fin n => P)) {X | Ĩ / 2 ≤ abs (info_estimate_seq n X - Ĩ)} +
        (Measure.pi (fun _ : Fin n => P)) {X | δ * Ĩ ^ 2 / 4 ≤ abs (info_estimate_seq n X - Ĩ)} :=
            by
    intro n
    apply (measure_mono _).trans (measure_union_le _ _)
    intro X hX
    simp only [Set.mem_union, Set.mem_setOf_eq]
    exact h_alg n X hX
  have h1 := h_info (Ĩ / 2) (by positivity)
  have h2 := h_info (δ * Ĩ ^ 2 / 4) (by positivity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
  · simpa using h1.add h2
  · exact Filter.Eventually.of_forall fun _ => zero_le
  · exact Filter.Eventually.of_forall fun n => h_meas n

/-- **Error A → 0 in Pⁿ-probability.**
`(Î_n⁻¹ − Ĩ⁻¹) · (1/√n) · Σᵢ ℓ̃(Xᵢ)`. -/
private lemma error_A_tendsto_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {info_estimate_seq : ∀ n, (Fin n → Ω) → ℝ}
    (hI_pos : 0 < efficientInformation S_θ T_nuis v)
    (h_info : ∀ ε > 0, Tendsto
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω |
            ε ≤ abs (info_estimate_seq n X - efficientInformation S_θ T_nuis v)})
      atTop (nhds 0)) :
    let scoreEff : Ω → ℝ :=
      ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
    ∀ ε > 0, Tendsto
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω |
            ε ≤ abs ((info_estimate_seq n X)⁻¹ - (efficientInformation S_θ T_nuis v)⁻¹)
                * abs ((Real.sqrt n)⁻¹ * ∑ i : Fin n, scoreEff (X i))})
      atTop (nhds 0) := by
  set Ĩ := efficientInformation S_θ T_nuis v
  -- Introduce scoreEff from the let-binding, then ε hε from the ∀
  intro scoreEff ε hε
  -- For any η > 0, eventually the measure ≤ ENNReal.ofReal η
  have key : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ abs ((info_estimate_seq n X)⁻¹ - Ĩ⁻¹)
              * abs ((Real.sqrt n)⁻¹ * ∑ i : Fin n, scoreEff (X i))}
      ≤ ENNReal.ofReal η := by
    intro η hη
    -- OP(1): score sum bounded via score_sum_bddAbove_in_prob
    obtain ⟨M_raw, hM_score⟩ := score_sum_bddAbove_in_prob hI_pos (η / 2) (by linarith)
    set M := max M_raw 1
    have hM_pos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hM_score' : ∀ n,
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | M ≤ abs ((Real.sqrt n)⁻¹ * ∑ i : Fin n, scoreEff (X i))}
        ≤ ENNReal.ofReal (η / 2) := by
      intro n
      apply (measure_mono _).trans (hM_score n)
      intro X hX; exact (le_max_left M_raw 1).trans hX
    -- oP(1): info_inv_diff_oP with δ = ε/M
    have h_inv_tendsto := info_inv_diff_oP hI_pos h_info (ε / M) (div_pos hε hM_pos)
    rw [ENNReal.tendsto_nhds_zero] at h_inv_tendsto
    have h_inv_le := h_inv_tendsto (ENNReal.ofReal (η / 2)) (by positivity)
    -- Set inclusion: {|B||S| ≥ ε} ⊆ {|S| ≥ M} ∪ {|B| ≥ ε/M}
    have h_incl : ∀ n,
        {X : Fin n → Ω |
          ε ≤ abs ((info_estimate_seq n X)⁻¹ - Ĩ⁻¹)
              * abs ((Real.sqrt n)⁻¹ * ∑ i : Fin n, scoreEff (X i))}
        ⊆ {X | M ≤ abs ((Real.sqrt n)⁻¹ * ∑ i : Fin n, scoreEff (X i))} ∪
          {X | ε / M ≤ abs ((info_estimate_seq n X)⁻¹ - Ĩ⁻¹)} := by
      intro n X hX
      simp only [Set.mem_union, Set.mem_setOf_eq]
      by_contra hc
      push Not at hc
      obtain ⟨h1, h2⟩ := hc
      have hAB : abs ((info_estimate_seq n X)⁻¹ - Ĩ⁻¹)
          * abs ((Real.sqrt n)⁻¹ * ∑ i : Fin n, scoreEff (X i)) < ε := by
        have hle : abs ((info_estimate_seq n X)⁻¹ - Ĩ⁻¹)
            * abs ((Real.sqrt n)⁻¹ * ∑ i : Fin n, scoreEff (X i))
            ≤ (ε / M) * abs ((Real.sqrt n)⁻¹ * ∑ i : Fin n, scoreEff (X i)) :=
          mul_le_mul_of_nonneg_right h2.le (abs_nonneg _)
        have hlt : (ε / M) * abs ((Real.sqrt n)⁻¹ * ∑ i : Fin n, scoreEff (X i)) < ε := by
          have h1' : (ε / M) * abs ((Real.sqrt n)⁻¹ * ∑ i : Fin n, scoreEff (X i))
              < (ε / M) * M := mul_lt_mul_of_pos_left h1 (div_pos hε hM_pos)
          have h2' : (ε / M) * M = ε := by field_simp
          linarith [h1', h2']
        linarith
      exact absurd hX (not_le.mpr hAB)
    -- Assemble
    filter_upwards [h_inv_le] with n hn
    have h1eq : ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
    exact le_trans
      (le_trans (measure_mono (h_incl n))
        (measure_union_le
          {X : Fin n → Ω | M ≤ abs ((Real.sqrt n)⁻¹ * ∑ i : Fin n, scoreEff (X i))}
          {X : Fin n → Ω | ε / M ≤ abs ((info_estimate_seq n X)⁻¹ - Ĩ⁻¹)}))
      (le_trans (add_le_add (hM_score' n) hn) h1eq.le)
  -- Conclude Tendsto from key via ENNReal.tendsto_nhds_zero
  rw [ENNReal.tendsto_nhds_zero]
  intro c hc
  by_cases hc_inf : c = ⊤
  · exact Filter.Eventually.of_forall fun _ => hc_inf ▸ le_top
  · have hc_real_pos : 0 < ENNReal.toReal c :=
      ENNReal.toReal_pos hc.ne' hc_inf
    filter_upwards [key (ENNReal.toReal c) hc_real_pos] with n hn
    exact hn.trans (ENNReal.ofReal_toReal hc_inf).le

/-- **Error B → 0 in Pⁿ-probability.**
`Î_n⁻¹ · √n · Pfanz_n`. -/
private lemma error_B_tendsto_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {preliminary : ∀ n, (Fin n → Ω) → ℝ}
    {score_estimate_seq : ℕ → Ω → ℝ → ℝ}
    {info_estimate_seq : ∀ n, (Fin n → Ω) → ℝ}
    {θ₀ : ℝ}
    (hI_pos : 0 < efficientInformation S_θ T_nuis v)
    (h_pfanz : ∀ ε > 0, Tendsto
      (fun n : ℕ =>
        let scoreEff : Ω → ℝ :=
          ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω |
            ε ≤ Real.sqrt n * abs
              ((n : ℝ)⁻¹ * (∑ i : Fin n, score_estimate_seq n (X i) (preliminary n X))
                - (n : ℝ)⁻¹ * (∑ i : Fin n, scoreEff (X i))
                + efficientInformation S_θ T_nuis v * (preliminary n X - θ₀))})
      atTop (nhds 0))
    (h_info : ∀ ε > 0, Tendsto
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω |
            ε ≤ abs (info_estimate_seq n X - efficientInformation S_θ T_nuis v)})
      atTop (nhds 0)) :
    let scoreEff : Ω → ℝ :=
      ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
    ∀ ε > 0, Tendsto
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω |
            ε ≤ abs (info_estimate_seq n X)⁻¹
              * (Real.sqrt n * abs
                  ((n : ℝ)⁻¹ * (∑ i : Fin n, score_estimate_seq n (X i) (preliminary n X))
                    - (n : ℝ)⁻¹ * (∑ i : Fin n, scoreEff (X i))
                    + efficientInformation S_θ T_nuis v * (preliminary n X - θ₀)))})
      atTop (nhds 0) := by
  set Ĩ := efficientInformation S_θ T_nuis v
  intro scoreEff ε hε
  set B := 1 + |Ĩ⁻¹| with hB_def
  have hB_pos : 0 < B := by
    have : 0 ≤ |Ĩ⁻¹| := abs_nonneg _
    linarith
  have key : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ abs (info_estimate_seq n X)⁻¹
            * (Real.sqrt n * abs
                ((n : ℝ)⁻¹ *
                  (∑ i : Fin n, score_estimate_seq n (X i) (preliminary n X))
                  - (n : ℝ)⁻¹ * (∑ i : Fin n, scoreEff (X i))
                  + Ĩ * (preliminary n X - θ₀)))}
      ≤ ENNReal.ofReal η := by
    intro η hη
    have h_inv_tendsto := info_inv_diff_oP hI_pos h_info 1 one_pos
    rw [ENNReal.tendsto_nhds_zero] at h_inv_tendsto
    have h_inv_le := h_inv_tendsto (ENNReal.ofReal (η / 2)) (by positivity)
    have h_pfanz_inst := h_pfanz (ε / B) (div_pos hε hB_pos)
    rw [ENNReal.tendsto_nhds_zero] at h_pfanz_inst
    have h_pfanz_le := h_pfanz_inst (ENNReal.ofReal (η / 2)) (by positivity)
    have h_incl : ∀ n : ℕ,
        {X : Fin n → Ω |
          ε ≤ abs (info_estimate_seq n X)⁻¹
            * (Real.sqrt n * abs
                ((n : ℝ)⁻¹ *
                  (∑ i : Fin n, score_estimate_seq n (X i) (preliminary n X))
                  - (n : ℝ)⁻¹ * (∑ i : Fin n, scoreEff (X i))
                  + Ĩ * (preliminary n X - θ₀)))}
        ⊆ {X : Fin n → Ω |
            1 ≤ abs ((info_estimate_seq n X)⁻¹ - Ĩ⁻¹)} ∪
          {X : Fin n → Ω |
            ε / B ≤ Real.sqrt n * abs
              ((n : ℝ)⁻¹ *
                (∑ i : Fin n, score_estimate_seq n (X i) (preliminary n X))
                - (n : ℝ)⁻¹ * (∑ i : Fin n, scoreEff (X i))
                + Ĩ * (preliminary n X - θ₀))} := by
      intro n X hX
      simp only [Set.mem_union, Set.mem_setOf_eq] at hX ⊢
      by_contra hc
      push Not at hc
      obtain ⟨h1, h2⟩ := hc
      have h_inv_lt_B : abs ((info_estimate_seq n X)⁻¹) < B := by
        have h_split : (info_estimate_seq n X)⁻¹
            = ((info_estimate_seq n X)⁻¹ - Ĩ⁻¹) + Ĩ⁻¹ := by ring
        calc abs ((info_estimate_seq n X)⁻¹)
            = abs (((info_estimate_seq n X)⁻¹ - Ĩ⁻¹) + Ĩ⁻¹) := by rw [← h_split]
          _ ≤ abs ((info_estimate_seq n X)⁻¹ - Ĩ⁻¹) + abs Ĩ⁻¹ := abs_add_le _ _
          _ < 1 + abs Ĩ⁻¹ := by linarith
          _ = B := by rw [hB_def]
      set Pfanz_val : ℝ :=
          (n : ℝ)⁻¹ *
            (∑ i : Fin n, score_estimate_seq n (X i) (preliminary n X))
            - (n : ℝ)⁻¹ * (∑ i : Fin n, scoreEff (X i))
            + Ĩ * (preliminary n X - θ₀)
      have h_pfanz_nn : 0 ≤ Real.sqrt n * abs Pfanz_val :=
        mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
      have h_AB_lt :
          abs ((info_estimate_seq n X)⁻¹)
            * (Real.sqrt n * abs Pfanz_val) < ε := by
        calc abs ((info_estimate_seq n X)⁻¹)
              * (Real.sqrt n * abs Pfanz_val)
            ≤ B * (Real.sqrt n * abs Pfanz_val) :=
              mul_le_mul_of_nonneg_right h_inv_lt_B.le h_pfanz_nn
          _ < B * (ε / B) := mul_lt_mul_of_pos_left h2 hB_pos
          _ = ε := by field_simp
      linarith
    filter_upwards [h_inv_le, h_pfanz_le] with n h1n h2n
    have h_sum : ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2)
        = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
    exact le_trans
      (le_trans (measure_mono (h_incl n)) (measure_union_le _ _))
      (le_trans (add_le_add h1n h2n) h_sum.le)
  rw [ENNReal.tendsto_nhds_zero]
  intro c hc
  by_cases hc_inf : c = ⊤
  · exact Filter.Eventually.of_forall fun _ => hc_inf ▸ le_top
  have hc_real_pos : 0 < ENNReal.toReal c := ENNReal.toReal_pos hc.ne' hc_inf
  filter_upwards [key (ENNReal.toReal c) hc_real_pos] with n hn
  exact hn.trans (ENNReal.ofReal_toReal hc_inf).le

/-- **Error C → 0 in Pⁿ-probability.**
`√n·(θ̃_n − θ₀) · (1 − Î_n⁻¹·Ĩ)`. -/
private lemma error_C_tendsto_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {preliminary : ∀ n, (Fin n → Ω) → ℝ}
    {info_estimate_seq : ∀ n, (Fin n → Ω) → ℝ}
    {θ₀ : ℝ}
    (hI_pos : 0 < efficientInformation S_θ T_nuis v)
    (h_info : ∀ ε > 0, Tendsto
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω |
            ε ≤ abs (info_estimate_seq n X - efficientInformation S_θ T_nuis v)})
      atTop (nhds 0))
    (h_rate : ∀ ε > 0, ∃ M : ℝ, ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          M ≤ abs (Real.sqrt n * (preliminary n X - θ₀))}
      ≤ ENNReal.ofReal ε) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω |
            ε ≤ abs (Real.sqrt n * (preliminary n X - θ₀))
              * abs (1 - (info_estimate_seq n X)⁻¹ * efficientInformation S_θ T_nuis v)})
      atTop (nhds 0) := by
  set Ĩ := efficientInformation S_θ T_nuis v
  intro ε hε
  -- For any η > 0, eventually measure ≤ ENNReal.ofReal η
  have key : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ abs (Real.sqrt n * (preliminary n X - θ₀))
            * abs (1 - (info_estimate_seq n X)⁻¹ * Ĩ)}
      ≤ ENNReal.ofReal η := by
    intro η hη
    -- OP(1): preliminary rate. Get M from h_rate.
    obtain ⟨M_raw, hM_bound⟩ := h_rate (η / 2) (by linarith)
    set M := max M_raw 1
    have hM_pos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hM_bound' : ∀ n,
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | M ≤ abs (Real.sqrt n * (preliminary n X - θ₀))}
        ≤ ENNReal.ofReal (η / 2) := by
      intro n
      apply (measure_mono _).trans (hM_bound n)
      intro X hX; exact (le_max_left M_raw 1).trans hX
    -- oP(1): (1 − Î⁻¹Ĩ) → 0 via info_mul_inv_oP
    have h_B_tendsto := info_mul_inv_oP hI_pos h_info (ε / M) (div_pos hε hM_pos)
    rw [ENNReal.tendsto_nhds_zero] at h_B_tendsto
    have h_B_le := h_B_tendsto (ENNReal.ofReal (η / 2)) (by positivity)
    -- Set inclusion: {|A||B| ≥ ε} ⊆ {|A| ≥ M} ∪ {|B| ≥ ε/M}
    have h_incl : ∀ n,
        {X : Fin n → Ω |
          ε ≤ abs (Real.sqrt n * (preliminary n X - θ₀))
            * abs (1 - (info_estimate_seq n X)⁻¹ * Ĩ)}
        ⊆ {X | M ≤ abs (Real.sqrt n * (preliminary n X - θ₀))} ∪
          {X | ε / M ≤ abs (1 - (info_estimate_seq n X)⁻¹ * Ĩ)} := by
      intro n X hX
      simp only [Set.mem_union, Set.mem_setOf_eq]
      by_contra hc
      push Not at hc
      obtain ⟨h1, h2⟩ := hc
      have hAB : abs (Real.sqrt n * (preliminary n X - θ₀))
          * abs (1 - (info_estimate_seq n X)⁻¹ * Ĩ) < ε := by
        have hle : abs (Real.sqrt n * (preliminary n X - θ₀))
            * abs (1 - (info_estimate_seq n X)⁻¹ * Ĩ)
            ≤ abs (Real.sqrt n * (preliminary n X - θ₀)) * (ε / M) :=
          mul_le_mul_of_nonneg_left h2.le (abs_nonneg _)
        have hlt : abs (Real.sqrt n * (preliminary n X - θ₀)) * (ε / M) < ε := by
          have h1' : abs (Real.sqrt n * (preliminary n X - θ₀)) * (ε / M)
              < M * (ε / M) := mul_lt_mul_of_pos_right h1 (div_pos hε hM_pos)
          have h2' : M * (ε / M) = ε := by field_simp
          linarith [h1', h2']
        linarith [hle, hlt]
      exact absurd hX (not_le.mpr hAB)
    -- Assemble: bound by two terms, both ≤ ofReal (η/2)
    filter_upwards [h_B_le] with n hn
    have h2eq : ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
    exact le_trans
      (le_trans (measure_mono (h_incl n))
        (measure_union_le
          {X : Fin n → Ω | M ≤ abs (Real.sqrt n * (preliminary n X - θ₀))}
          {X : Fin n → Ω | ε / M ≤ abs (1 - (info_estimate_seq n X)⁻¹ * Ĩ)}))
      (le_trans (add_le_add (hM_bound' n) hn) h2eq.le)
  -- Conclude Tendsto from key via ENNReal.tendsto_nhds_zero
  rw [ENNReal.tendsto_nhds_zero]
  intro c hc
  by_cases hc_inf : c = ⊤
  · exact Filter.Eventually.of_forall fun _ => hc_inf ▸ le_top
  · have hc_real_pos : 0 < ENNReal.toReal c :=
      ENNReal.toReal_pos hc.ne' hc_inf
    filter_upwards [key (ENNReal.toReal c) hc_real_pos] with n hn
    exact hn.trans (ENNReal.ofReal_toReal hc_inf).le

/-! ## Helper lemmas for derivation theorems

LLN bridges and Cauchy-Schwarz utilities used in the proofs of
`OneStepTaylorHyp.pfanzagl_display`, `OneStepTaylorHyp.info_consistency`,
and `oneStep_asympLinear_of_taylor`. -/

/-- **Cauchy-Schwarz: `√n · |empirical mean| ≤ √(empirical 2nd moment · n)`.**

For `aᵢ : Fin n → ℝ`:
`(√n · (1/n) · Σᵢ aᵢ)² ≤ Σᵢ aᵢ²`

Equivalently: `√n · |(1/n) · Σᵢ aᵢ| ≤ √(Σᵢ aᵢ²)`.

Pure algebra via `Finset.sq_sum_le_card_mul_sum_sq` (Cauchy-Schwarz for
finite sums with constant weights). -/
private lemma sqrt_n_avg_sq_le_sum_sq
    {n : ℕ} (a : Fin n → ℝ) :
    (Real.sqrt n * ((n : ℝ)⁻¹ * ∑ i : Fin n, a i)) ^ 2 ≤ ∑ i : Fin n, (a i) ^ 2 := by
  by_cases hn : n = 0
  · subst hn; simp
  have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  -- Cauchy-Schwarz for finite sums with constant weights
  have hCS : (∑ i : Fin n, a i) ^ 2 ≤ (Finset.univ : Finset (Fin n)).card *
      ∑ i : Fin n, (a i) ^ 2 := sq_sum_le_card_mul_sum_sq
  rw [Finset.card_fin] at hCS
  -- LHS: (√n · (1/n) · Σa)² = (1/n) · (Σa)²
  have h_expand : (Real.sqrt n * ((n : ℝ)⁻¹ * ∑ i : Fin n, a i)) ^ 2
      = (n : ℝ)⁻¹ * (∑ i : Fin n, a i) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hn_pos.le, mul_pow]
    field_simp
  rw [h_expand]
  -- Goal: (1/n) · (Σa)² ≤ Σa². From hCS and dividing by n > 0.
  have h_n_inv_nn : 0 ≤ (n : ℝ)⁻¹ := by positivity
  calc (n : ℝ)⁻¹ * (∑ i : Fin n, a i) ^ 2
      ≤ (n : ℝ)⁻¹ * ((n : ℝ) * ∑ i : Fin n, (a i) ^ 2) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hCS) h_n_inv_nn
    _ = ∑ i : Fin n, (a i) ^ 2 := by
        rw [← mul_assoc, inv_mul_cancel₀ hn_ne, one_mul]

/-- **`(1/n) · Σ ℓ̇ + Ĩ →_P 0`.**

Application of `iid_lln_in_prob_l1` to `score_l_dot ∈ L²(P) ⊂ L¹(P)`,
combined with `score_l_dot_bartlett` (`E_P[ℓ̇] = -Ĩ`).

Specifically: `(1/n)·Σ ℓ̇(Xᵢ) - ∫ℓ̇ ∂P →_P 0` gives `(1/n)·Σ ℓ̇(Xᵢ) →_P -Ĩ`,
and equivalently `(1/n)·Σ ℓ̇(Xᵢ) + Ĩ →_P 0`. -/
private lemma score_l_dot_avg_plus_info_oP
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {score_l_dot : Lp ℝ 2 P}
    (h_bartlett :
      ∫ ω, (score_l_dot : Ω → ℝ) ω ∂P = -efficientInformation S_θ T_nuis v) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ abs ((n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i))
                   + efficientInformation S_θ T_nuis v)})
      atTop (nhds 0) := by
  -- Apply iid_lln_in_prob_l1 with f = score_l_dot ∈ L¹.
  -- Bridge: |(1/n)Σℓ̇ + Ĩ| = |(1/n)Σℓ̇ - (-Ĩ)| = |(1/n)Σℓ̇ - ∫ℓ̇ ∂P| (h_bartlett).
  have hf_int : Integrable (fun ω => (score_l_dot : Ω → ℝ) ω) P :=
    (Lp.memLp score_l_dot).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h_lln := iid_lln_in_prob_l1 (fun ω => (score_l_dot : Ω → ℝ) ω) hf_int
  intro ε hε
  -- Rewrite the goal sets to match h_lln's form
  have h_set_eq : ∀ n : ℕ,
      {X : Fin n → Ω |
        ε ≤ abs ((n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i))
                 + efficientInformation S_θ T_nuis v)}
      = {X : Fin n → Ω |
          ε ≤ abs ((n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i))
                   - ∫ ω, (score_l_dot : Ω → ℝ) ω ∂P)} := by
    intro n
    ext X
    simp only [Set.mem_setOf_eq]
    rw [h_bartlett]
    constructor
    · intro h; convert h using 2; ring
    · intro h; convert h using 2; ring
  simp_rw [h_set_eq]
  exact h_lln ε hε

/-- **iid LLN for `ℓ̇²`.** `(1/n) Σᵢ ℓ̇(Xᵢ)² →_P ∫ ℓ̇² ∂P`.

Direct application of `iid_lln_in_prob_l1` to `f = ℓ̇²` which is in L¹(P)
since `ℓ̇ ∈ L²(P)` (`MemLp.integrable_sq`). -/
private lemma score_l_dot_sq_avg_lln
    {P : Measure Ω} [IsProbabilityMeasure P]
    {score_l_dot : Lp ℝ 2 P} :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ abs ((n : ℝ)⁻¹ * (∑ i : Fin n, ((score_l_dot : Ω → ℝ) (X i)) ^ 2)
                   - ∫ ω, ((score_l_dot : Ω → ℝ) ω) ^ 2 ∂P)})
      atTop (nhds 0) := by
  have h_int : Integrable (fun ω => ((score_l_dot : Ω → ℝ) ω) ^ 2) P :=
    (Lp.memLp score_l_dot).integrable_sq
  exact iid_lln_in_prob_l1 (fun ω => ((score_l_dot : Ω → ℝ) ω) ^ 2) h_int

/-- **iid LLN for `ℓ̃²`.** `(1/n) Σᵢ ℓ̃(Xᵢ)² →_P ∫ ℓ̃² ∂P`.

Direct application of `iid_lln_in_prob_l1` to `f = ℓ̃²` which is in L¹(P)
since `ℓ̃ ∈ L²(P)` (`MemLp.integrable_sq`). The limit `∫ ℓ̃² ∂P` equals the
efficient information `Ĩ` (separate identity, used at the application site). -/
private lemma ell_tilde_sq_avg_lln
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ} :
    let scoreEff : Ω → ℝ :=
      ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ abs ((n : ℝ)⁻¹ * (∑ i : Fin n, scoreEff (X i) ^ 2)
                   - ∫ ω, scoreEff ω ^ 2 ∂P)})
      atTop (nhds 0) := by
  intro scoreEff
  have h_int : Integrable (fun ω => scoreEff ω ^ 2) P :=
    (Lp.memLp _).integrable_sq
  exact iid_lln_in_prob_l1 (fun ω => scoreEff ω ^ 2) h_int

/-- **iid LLN for `ℓ̃·ℓ̇`.** `(1/n) Σᵢ (ℓ̃·ℓ̇)(Xᵢ) →_P ∫ ℓ̃·ℓ̇ ∂P`.

Direct application of `iid_lln_in_prob_l1` to `f = ℓ̃·ℓ̇` which is in L¹(P)
by Cauchy-Schwarz from `ℓ̃, ℓ̇ ∈ L²(P)` (`MemLp.integrable_mul`). -/
private lemma ell_tilde_score_l_dot_avg_lln
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {score_l_dot : Lp ℝ 2 P} :
    let scoreEff : Ω → ℝ :=
      ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ abs ((n : ℝ)⁻¹ *
              (∑ i : Fin n, scoreEff (X i) * (score_l_dot : Ω → ℝ) (X i))
                   - ∫ ω, scoreEff ω * (score_l_dot : Ω → ℝ) ω ∂P)})
      atTop (nhds 0) := by
  intro scoreEff
  have h_int : Integrable (fun ω => scoreEff ω * (score_l_dot : Ω → ℝ) ω) P :=
    MemLp.integrable_mul (Lp.memLp _) (Lp.memLp _)
  exact iid_lln_in_prob_l1 (fun ω => scoreEff ω * (score_l_dot : Ω → ℝ) ω) h_int

/-- **Empirical Taylor remainder controls `√n·|empirical mean|`.**

Given `score_l2_taylor` (`Σᵢ rᵢ² →_P 0`) and the algebraic bound
`(√n · (1/n) · Σᵢ rᵢ)² ≤ Σᵢ rᵢ²` (sqrt_n_avg_sq_le_sum_sq), deduce
`√n · (1/n) · Σᵢ rᵢ →_P 0`. -/
private lemma taylor_remainder_root_n_oP
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {preliminary : ∀ n, (Fin n → Ω) → ℝ}
    {score_estimate_seq : ℕ → Ω → ℝ → ℝ}
    {score_l_dot : Lp ℝ 2 P}
    {θ₀ : ℝ}
    (h_taylor : ∀ ε > 0, Tendsto
      (fun n : ℕ =>
        let scoreEff : Ω → ℝ :=
          ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω |
            ε ≤ ∑ i : Fin n,
              (score_estimate_seq n (X i) (preliminary n X)
                - scoreEff (X i)
                - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)) ^ 2})
      atTop (nhds 0)) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ =>
        let scoreEff : Ω → ℝ :=
          ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω |
            ε ≤ Real.sqrt n * abs ((n : ℝ)⁻¹ * ∑ i : Fin n,
              (score_estimate_seq n (X i) (preliminary n X)
                - scoreEff (X i)
                - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)))})
      atTop (nhds 0) := by
  intro ε hε
  -- Apply h_taylor at threshold ε² and use sqrt_n_avg_sq_le_sum_sq.
  have h_sq := h_taylor (ε ^ 2) (by positivity)
  -- Set inclusion: {ε ≤ √n·|(1/n)Σ r|} ⊆ {ε² ≤ Σ r²}
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sq
    (Filter.Eventually.of_forall fun _ => zero_le)
  refine Filter.Eventually.of_forall fun n => measure_mono ?_
  intro X hX
  simp only [Set.mem_setOf_eq] at hX ⊢
  -- Want: ε² ≤ Σ rᵢ², given ε ≤ √n · |(1/n)Σ rᵢ|
  -- Use Cauchy-Schwarz: (√n · (1/n)Σ rᵢ)² ≤ Σ rᵢ²
  have h_cs := sqrt_n_avg_sq_le_sum_sq (fun i =>
    score_estimate_seq n (X i) (preliminary n X)
      - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
      - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i))
  -- Square hX: ε² ≤ (√n · |(1/n)Σ r|)² = (√n · (1/n)Σ r)² (sq_abs)
  have h_sq_bd : ε ^ 2 ≤ (Real.sqrt n * abs ((n : ℝ)⁻¹ * ∑ i : Fin n,
      (score_estimate_seq n (X i) (preliminary n X)
        - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
        - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)))) ^ 2 := by
    have h_pos : 0 ≤ Real.sqrt n * abs ((n : ℝ)⁻¹ * ∑ i : Fin n,
        (score_estimate_seq n (X i) (preliminary n X)
          - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
          - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i))) := by
      positivity
    nlinarith [hX, h_pos]
  -- (√n · |(1/n)Σ r|)² = (√n · (1/n)Σ r)² ≤ Σ r²
  have h_abs_eq : (Real.sqrt n * abs ((n : ℝ)⁻¹ * ∑ i : Fin n,
      (score_estimate_seq n (X i) (preliminary n X)
        - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
        - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)))) ^ 2
      = (Real.sqrt n * ((n : ℝ)⁻¹ * ∑ i : Fin n,
        (score_estimate_seq n (X i) (preliminary n X)
          - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
          - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)))) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
  linarith [h_cs, h_abs_eq ▸ h_sq_bd]

/-- **Empirical Cauchy-Schwarz for averages.** `(avg(a·b))² ≤ avg(a²)·avg(b²)`.

Direct from `Finset.sum_mul_sq_le_sq_mul_sq` (`(Σaᵢbᵢ)² ≤ (Σaᵢ²)(Σbᵢ²)`)
multiplied by `(1/n)²`. -/
private lemma avg_prod_sq_le
    {n : ℕ} (a b : Fin n → ℝ) :
    ((n : ℝ)⁻¹ * (∑ i : Fin n, a i * b i)) ^ 2 ≤
      ((n : ℝ)⁻¹ * (∑ i : Fin n, (a i) ^ 2)) *
        ((n : ℝ)⁻¹ * (∑ i : Fin n, (b i) ^ 2)) := by
  have h_cs : (∑ i : Fin n, a i * b i) ^ 2 ≤
      (∑ i : Fin n, (a i) ^ 2) * (∑ i : Fin n, (b i) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have h_n_inv_sq_nn : (0 : ℝ) ≤ ((n : ℝ)⁻¹) ^ 2 := sq_nonneg _
  calc ((n : ℝ)⁻¹ * (∑ i : Fin n, a i * b i)) ^ 2
      = ((n : ℝ)⁻¹) ^ 2 * (∑ i : Fin n, a i * b i) ^ 2 := by ring
    _ ≤ ((n : ℝ)⁻¹) ^ 2 *
        ((∑ i : Fin n, (a i) ^ 2) * (∑ i : Fin n, (b i) ^ 2)) :=
        mul_le_mul_of_nonneg_left h_cs h_n_inv_sq_nn
    _ = ((n : ℝ)⁻¹ * (∑ i : Fin n, (a i) ^ 2)) *
        ((n : ℝ)⁻¹ * (∑ i : Fin n, (b i) ^ 2)) := by ring

/-- **`(prel-θ₀) →_P 0`** (preliminary consistency in probability).

Direct from `preliminary_sqrt_n_rate` (`√n·(prel-θ₀) = OP(1)`): for any ε > 0,
choose M = M(η) from h_rate. For n large enough that M/√n < ε, the set
`{|prel-θ₀| ≥ ε}` is contained in `{√n·|prel-θ₀| ≥ M}`, whose measure is
bounded by η. Hence `(prel-θ₀) →_P 0`. -/
private lemma preliminary_diff_oP
    {P : Measure Ω} [IsProbabilityMeasure P]
    {preliminary : ∀ n, (Fin n → Ω) → ℝ}
    {θ₀ : ℝ}
    (h_rate : ∀ ε > 0, ∃ M : ℝ, ∀ n : ℕ,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | M ≤ abs (Real.sqrt n * (preliminary n X - θ₀))}
      ≤ ENNReal.ofReal ε) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | ε ≤ abs (preliminary n X - θ₀)})
      atTop (nhds 0) := by
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro c hc
  by_cases hc_inf : c = ⊤
  · exact Filter.Eventually.of_forall fun _ => hc_inf ▸ le_top
  have hc_real_pos : 0 < ENNReal.toReal c :=
    ENNReal.toReal_pos hc.ne' hc_inf
  obtain ⟨M_raw, hM_bound⟩ := h_rate (ENNReal.toReal c) hc_real_pos
  set M := max M_raw 1
  have hM_pos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hM_bound' : ∀ n,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | M ≤ abs (Real.sqrt n * (preliminary n X - θ₀))}
      ≤ ENNReal.ofReal (ENNReal.toReal c) := by
    intro n
    apply (measure_mono _).trans (hM_bound n)
    intro X hX; exact (le_max_left M_raw 1).trans hX
  filter_upwards [eventually_gt_atTop (⌈(M / ε) ^ 2⌉₊)] with n hn
  have h_n_real : (M / ε) ^ 2 < (n : ℝ) := by
    have hn_real : ((⌈(M / ε) ^ 2⌉₊ : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact lt_of_le_of_lt (Nat.le_ceil _) hn_real
  have h_M_lt_sqrt : M / ε < Real.sqrt n := by
    rw [show M/ε = Real.sqrt ((M/ε)^2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) h_n_real
  have h_M_lt : M < Real.sqrt n * ε := by
    have h1 : M / ε * ε < Real.sqrt n * ε :=
      mul_lt_mul_of_pos_right h_M_lt_sqrt hε
    rwa [div_mul_cancel₀ M (ne_of_gt hε)] at h1
  have h_incl : {X : Fin n → Ω | ε ≤ abs (preliminary n X - θ₀)}
      ⊆ {X : Fin n → Ω | M ≤ abs (Real.sqrt n * (preliminary n X - θ₀))} := by
    intro X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h_le : Real.sqrt n * ε ≤ Real.sqrt n * abs (preliminary n X - θ₀) :=
      mul_le_mul_of_nonneg_left hX (Real.sqrt_nonneg _)
    linarith
  exact (measure_mono h_incl).trans
    ((hM_bound' n).trans (ENNReal.ofReal_toReal hc_inf).le)

/-! ## Derivation theorems on `OneStepTaylorHyp`

`pfanzagl_display` and `info_consistency` are derived from the Taylor
regularity conditions, plus iid LLN applied to `ℓ̃`, `ℓ̇` and their products. -/

/-- **Pfanzagl 2nd-order display, derived from Taylor regularity.**

From `OneStepTaylorHyp`, derive
`(1/n)·Σᵢ ℓ̂_n(Xᵢ, θ̃_n) − (1/n)·Σᵢ ℓ̃(Xᵢ) + Ĩ·(θ̃_n − θ₀) = oP(1/√n)`.

**Proof sketch**:
1. Decompose: `Σᵢ score_estimate(Xᵢ, θ̃_n) = Σᵢ ℓ̃(Xᵢ) + (θ̃_n − θ₀)·Σᵢ ℓ̇(Xᵢ) + Σᵢ r_n(Xᵢ)`
2. Multiply by 1/n, subtract `(1/n) Σ ℓ̃`, add `Ĩ·(θ̃_n − θ₀)`:
   `LHS = (θ̃_n − θ₀)·((1/n) Σ ℓ̇ + Ĩ) + (1/n) Σ r_n`
3. `(1/n) Σ ℓ̇ + Ĩ →_P 0` by iid LLN + `score_l_dot_bartlett` (`E[ℓ̇] = -Ĩ`).
   Combined with `√n(θ̃_n − θ₀) = OP(1)`, the first term is oP(1/√n).
4. `(1/n) Σ r_n` is oP(1/√n) by Cauchy-Schwarz: `|(1/n) Σ r_n|² ≤ (1/n) Σ r²`,
   so `√n · |(1/n) Σ r_n| ≤ √(Σ r_n²) →_P 0` from `score_l2_taylor`.

Reference: vdV §25.8 (Taylor strong-regularity remark). -/
theorem OneStepTaylorHyp.pfanzagl_display
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {preliminary : ∀ n, (Fin n → Ω) → ℝ}
    {score_estimate_seq : ℕ → Ω → ℝ → ℝ}
    {info_estimate_seq : ∀ n, (Fin n → Ω) → ℝ}
    {score_l_dot : Lp ℝ 2 P}
    {θ₀ : ℝ}
    (hpf : OneStepTaylorHyp P Θ S_θ T_nuis v preliminary score_estimate_seq
              info_estimate_seq score_l_dot θ₀) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ =>
        let scoreEff : Ω → ℝ :=
          ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω |
            ε ≤ Real.sqrt n * abs
              ((n : ℝ)⁻¹ * (∑ i : Fin n, score_estimate_seq n (X i) (preliminary n X))
                - (n : ℝ)⁻¹ * (∑ i : Fin n, scoreEff (X i))
                + efficientInformation S_θ T_nuis v * (preliminary n X - θ₀))})
      atTop (nhds 0) := by
  intro ε hε
  set Ĩ := efficientInformation S_θ T_nuis v with hĨ_def
  -- Algebraic identity: Pfanz_n = (prel-θ₀)·[avg(ℓ̇) + Ĩ] + avg(r_n)
  -- Finset.sum_sub_distrib (twice) + Finset.mul_sum (factor (prel-θ₀)) + ring.
  have h_alg : ∀ n (X : Fin n → Ω),
      let scoreEff : Ω → ℝ :=
        ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
      (n : ℝ)⁻¹ * (∑ i : Fin n, score_estimate_seq n (X i) (preliminary n X))
        - (n : ℝ)⁻¹ * (∑ i : Fin n, scoreEff (X i))
        + Ĩ * (preliminary n X - θ₀)
      = (preliminary n X - θ₀) *
          ((n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i)) + Ĩ)
        + (n : ℝ)⁻¹ * (∑ i : Fin n,
            (score_estimate_seq n (X i) (preliminary n X)
              - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
              - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i))) := by
    intro n X _scoreEff
    have h_sum :
        ∑ i : Fin n,
          (score_estimate_seq n (X i) (preliminary n X)
            - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
            - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i))
        = (∑ i : Fin n, score_estimate_seq n (X i) (preliminary n X))
          - (∑ i : Fin n,
              ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i))
          - (preliminary n X - θ₀) *
              (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [h_sum]
    ring
  -- Apply helpers
  have h_l_dot := score_l_dot_avg_plus_info_oP (score_l_dot := score_l_dot)
                    hpf.score_l_dot_bartlett
  have h_rem := taylor_remainder_root_n_oP (score_l_dot := score_l_dot)
                  (preliminary := preliminary) (score_estimate_seq := score_estimate_seq)
                  (θ₀ := θ₀) hpf.score_l2_taylor
  -- Key: ∀ η > 0, eventually P^n ≤ ofReal η
  have key : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ Real.sqrt n * abs
            ((n : ℝ)⁻¹ * (∑ i : Fin n, score_estimate_seq n (X i) (preliminary n X))
              - (n : ℝ)⁻¹ * (∑ i : Fin n,
                  ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i))
              + Ĩ * (preliminary n X - θ₀))}
      ≤ ENNReal.ofReal η := by
    intro η hη
    -- Choose M from preliminary_sqrt_n_rate(η/3)
    obtain ⟨M_raw, hM_bound⟩ := hpf.preliminary_sqrt_n_rate (η / 3) (by linarith)
    set M := max M_raw 1
    have hM_pos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hM_bound' : ∀ n,
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | M ≤ abs (Real.sqrt n * (preliminary n X - θ₀))}
        ≤ ENNReal.ofReal (η / 3) := by
      intro n
      apply (measure_mono _).trans (hM_bound n)
      intro X hX; exact (le_max_left M_raw 1).trans hX
    -- Apply h_l_dot and h_rem at appropriate thresholds
    have h_l_dot_inst := h_l_dot (ε / (2 * M)) (by positivity)
    rw [ENNReal.tendsto_nhds_zero] at h_l_dot_inst
    have h_l_dot_le := h_l_dot_inst (ENNReal.ofReal (η / 3)) (by positivity)
    have h_rem_inst := h_rem (ε / 2) (by linarith)
    rw [ENNReal.tendsto_nhds_zero] at h_rem_inst
    have h_rem_le := h_rem_inst (ENNReal.ofReal (η / 3)) (by positivity)
    -- 3-term union bound (set inclusion + measure_mono + measure_union_le twice)
    filter_upwards [h_l_dot_le, h_rem_le] with n hn1 hn2
    -- Set inclusion via the algebraic identity h_alg.
    have h_incl : {X : Fin n → Ω |
          ε ≤ Real.sqrt n * abs
            ((n : ℝ)⁻¹ * (∑ i : Fin n, score_estimate_seq n (X i) (preliminary n X))
              - (n : ℝ)⁻¹ * (∑ i : Fin n,
                  ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i))
              + Ĩ * (preliminary n X - θ₀))}
        ⊆ {X : Fin n → Ω | M ≤ abs (Real.sqrt n * (preliminary n X - θ₀))} ∪
          ({X : Fin n → Ω |
              ε / (2 * M) ≤ abs ((n : ℝ)⁻¹ *
                (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i)) + Ĩ)} ∪
            {X : Fin n → Ω |
              ε / 2 ≤ Real.sqrt n * abs ((n : ℝ)⁻¹ *
                (∑ i : Fin n, (score_estimate_seq n (X i) (preliminary n X)
                  - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
                  - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i))))}) := by
      intro X hX
      simp only [Set.mem_union, Set.mem_setOf_eq] at hX ⊢
      by_contra hc
      push Not at hc
      obtain ⟨h1, h2, h3⟩ := hc
      -- h1: |√n·(prel-θ₀)| < M
      -- h2: |avg(ℓ̇) + Ĩ| < ε/(2M)
      -- h3: √n · |avg(r_n)| < ε/2
      -- Apply h_alg to rewrite Pfanz_n in hX
      rw [h_alg n X] at hX
      -- hX : ε ≤ √n · |(prel-θ₀)·(avg(ℓ̇)+Ĩ) + avg(r_n)|
      set A : ℝ := (preliminary n X - θ₀) *
        ((n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i)) + Ĩ) with hA_def
      set B : ℝ := (n : ℝ)⁻¹ * (∑ i : Fin n,
        (score_estimate_seq n (X i) (preliminary n X)
          - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
          - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i))) with hB_def
      have h_sqrt_nn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
      -- Triangle: √n·|A+B| ≤ √n·|A| + √n·|B|
      have h_tri : Real.sqrt n * abs (A + B)
          ≤ Real.sqrt n * abs A + Real.sqrt n * abs B := by
        have := abs_add_le A B
        nlinarith [Real.sqrt_nonneg n]
      -- |A| = |prel-θ₀| · |avg(ℓ̇)+Ĩ|
      -- √n·|A| = (√n·|prel-θ₀|)·|avg(ℓ̇)+Ĩ| = |√n·(prel-θ₀)|·|avg(ℓ̇)+Ĩ|
      have h_termA : Real.sqrt n * abs A < ε / 2 := by
        rw [hA_def, abs_mul, ← mul_assoc,
            show Real.sqrt n * abs (preliminary n X - θ₀)
              = abs (Real.sqrt n * (preliminary n X - θ₀)) by
              rw [abs_mul, abs_of_nonneg h_sqrt_nn]]
        calc abs (Real.sqrt n * (preliminary n X - θ₀)) *
            abs ((n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i)) + Ĩ)
            ≤ abs (Real.sqrt n * (preliminary n X - θ₀)) * (ε / (2 * M)) :=
              mul_le_mul_of_nonneg_left h2.le (abs_nonneg _)
          _ < M * (ε / (2 * M)) :=
              mul_lt_mul_of_pos_right h1 (by positivity)
          _ = ε / 2 := by field_simp
      -- √n·|B| < ε/2 from h3
      have h_termB : Real.sqrt n * abs B < ε / 2 := h3
      linarith
    -- Apply union bound: 3 terms each ≤ ofReal (η/3), sum ≤ ofReal η
    refine (measure_mono h_incl).trans ?_
    refine (measure_union_le _ _).trans ?_
    refine le_trans (add_le_add (hM_bound' n) (measure_union_le _ _)) ?_
    rw [show ENNReal.ofReal η =
          ENNReal.ofReal (η/3) + ENNReal.ofReal (η/3) + ENNReal.ofReal (η/3) by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith),
            ← ENNReal.ofReal_add (by linarith) (by linarith)]
        congr 1; ring]
    rw [add_assoc]
    exact add_le_add le_rfl (add_le_add hn1 hn2)
  -- Conclude Tendsto via ENNReal.tendsto_nhds_zero
  rw [ENNReal.tendsto_nhds_zero]
  intro c hc
  by_cases hc_inf : c = ⊤
  · exact Filter.Eventually.of_forall fun _ => hc_inf ▸ le_top
  have hc_real_pos : 0 < ENNReal.toReal c :=
    ENNReal.toReal_pos hc.ne' hc_inf
  filter_upwards [key (ENNReal.toReal c) hc_real_pos] with n hn
  exact hn.trans (ENNReal.ofReal_toReal hc_inf).le

/-- **Information estimator consistency, derived from Taylor regularity + plug-in.**

From `OneStepTaylorHyp` (which encodes `Î_n = (1/n) Σ (ℓ̂_n)²`), derive
`Î_n →_P Ĩ`.

**Proof sketch**:
Substitute Taylor `ℓ̂_n(X, θ̃_n) = ℓ̃(X) + (θ̃_n − θ₀)·ℓ̇(X) + r_n(X)`:
```
Î_n = (1/n) Σ (ℓ̃ + (θ̃_n − θ₀)·ℓ̇ + r_n)²
    = P_n(ℓ̃²) + 2(θ̃_n − θ₀)·P_n(ℓ̃·ℓ̇) + (θ̃_n − θ₀)²·P_n(ℓ̇²)
      + 2·P_n(ℓ̃·r_n) + 2(θ̃_n − θ₀)·P_n(ℓ̇·r_n) + P_n(r_n²)
```

Each term:
- `P_n(ℓ̃²) →_P E_P[ℓ̃²] = Ĩ` (iid LLN; ℓ̃ ∈ L²(P) so ℓ̃² ∈ L¹).
- Other terms involve a factor `→_P 0` (preliminary consistency, Taylor remainder
  via Cauchy-Schwarz, etc.).

Sum →_P Ĩ. -/
theorem OneStepTaylorHyp.info_consistency
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {preliminary : ∀ n, (Fin n → Ω) → ℝ}
    {score_estimate_seq : ℕ → Ω → ℝ → ℝ}
    {info_estimate_seq : ∀ n, (Fin n → Ω) → ℝ}
    {score_l_dot : Lp ℝ 2 P}
    {θ₀ : ℝ}
    (hpf : OneStepTaylorHyp P Θ S_θ T_nuis v preliminary score_estimate_seq
              info_estimate_seq score_l_dot θ₀) :
    ∀ ε > 0, Tendsto
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω |
            ε ≤ abs (info_estimate_seq n X - efficientInformation S_θ T_nuis v)})
      atTop (nhds 0) := by
  intro ε hε
  set Ĩ := efficientInformation S_θ T_nuis v
  -- Expanding the plug-in square and distributing the finite sums gives the
  -- identity `Î_n - Ĩ = T1 + 2·T2 + T3 + 2·T4 + 2·T5 + T6` below.
  have h_info_alg : ∀ n (X : Fin n → Ω),
      let scoreEff : Ω → ℝ :=
        ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
      let ldot : Ω → ℝ := (score_l_dot : Ω → ℝ)
      let prel_dev : ℝ := preliminary n X - θ₀
      info_estimate_seq n X - Ĩ
      = ((n : ℝ)⁻¹ * (∑ i : Fin n, (scoreEff (X i)) ^ 2) - Ĩ)
        + 2 * (prel_dev * ((n : ℝ)⁻¹ *
            (∑ i : Fin n, scoreEff (X i) * ldot (X i))))
        + (prel_dev ^ 2 * ((n : ℝ)⁻¹ * (∑ i : Fin n, (ldot (X i)) ^ 2)))
        + 2 * ((n : ℝ)⁻¹ * (∑ i : Fin n, scoreEff (X i) *
            (score_estimate_seq n (X i) (preliminary n X)
              - scoreEff (X i) - prel_dev * ldot (X i))))
        + 2 * (prel_dev * ((n : ℝ)⁻¹ * (∑ i : Fin n, ldot (X i) *
            (score_estimate_seq n (X i) (preliminary n X)
              - scoreEff (X i) - prel_dev * ldot (X i)))))
        + ((n : ℝ)⁻¹ * (∑ i : Fin n,
            (score_estimate_seq n (X i) (preliminary n X)
              - scoreEff (X i) - prel_dev * ldot (X i)) ^ 2)) := by
    intro n X _scoreEff _ldot _prel_dev
    -- Use h_plug: info_estimate_seq = avg(score_est²)
    rw [hpf.info_plug_in_def n X]
    -- Pointwise expansion: score_est² = scoreEff² + 2·prel·sE·ld + prel²·ld² + 2·sE·r + 2·prel·ld·r
    -- + r²
    have h_pt : ∀ i : Fin n,
        (score_estimate_seq n (X i) (preliminary n X)) ^ 2
        = (((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)) ^ 2
          + 2 * ((preliminary n X - θ₀) *
              ((((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)) *
                  (score_l_dot : Ω → ℝ) (X i)))
          + (preliminary n X - θ₀) ^ 2 *
              ((score_l_dot : Ω → ℝ) (X i)) ^ 2
          + 2 * (((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i) *
              (score_estimate_seq n (X i) (preliminary n X)
                - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
                - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)))
          + 2 * ((preliminary n X - θ₀) *
              ((score_l_dot : Ω → ℝ) (X i) *
                (score_estimate_seq n (X i) (preliminary n X)
                  - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
                  - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i))))
          + (score_estimate_seq n (X i) (preliminary n X)
              - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
              - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)) ^ 2 := by
      intro i; ring
    rw [Finset.sum_congr rfl (fun i _ => h_pt i)]
    -- Distribute the sum + factor out constants
    simp_rw [Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum]
    ring
  -- 6 per-term oP claims:
  -- T1 = avg(ℓ̃²) - Ĩ →_P 0 (LLN + ∫ℓ̃² = Ĩ identity)
  -- T2 = (prel-θ₀)·avg(ℓ̃·ℓ̇) →_P 0 (oP × OP)
  -- T3 = (prel-θ₀)²·avg(ℓ̇²) →_P 0 (oP² × OP)
  -- T4 = avg(ℓ̃·r_n) →_P 0 (Cauchy-Schwarz × score_l2_taylor)
  -- T5 = (prel-θ₀)·avg(ℓ̇·r_n) →_P 0 (oP × Cauchy-Schwarz)
  -- T6 = avg(r_n²) →_P 0 (from score_l2_taylor / n)

  -- T6: avg(r_n²) →_P 0 from score_l2_taylor.
  -- Set inclusion: {(1/n)·Σ r² ≥ ε} ⊆ {Σ r² ≥ ε} (since (1/n) ≤ 1 for n ≥ 1 and Σ r² ≥ 0).
  have h_T6_oP : ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ (n : ℝ)⁻¹ * (∑ i : Fin n,
            (score_estimate_seq n (X i) (preliminary n X)
              - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
              - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)) ^ 2)})
      atTop (nhds 0) := by
    intro ε' hε'
    have h_taylor := hpf.score_l2_taylor ε' hε'
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_taylor
      (Filter.Eventually.of_forall fun _ => zero_le)
    refine Filter.Eventually.of_forall fun n => measure_mono ?_
    intro X hX
    simp only [Set.mem_setOf_eq] at hX ⊢
    by_cases hn : n = 0
    · subst hn; simp only [Fin.sum_univ_zero, mul_zero] at hX; linarith
    have hn_ge : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have h_inv_le : (n : ℝ)⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; exact hn_ge
    have h_sum_nn : 0 ≤ ∑ i : Fin n,
        (score_estimate_seq n (X i) (preliminary n X)
          - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
          - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    calc ε' ≤ (n : ℝ)⁻¹ * _ := hX
      _ ≤ 1 * _ := mul_le_mul_of_nonneg_right h_inv_le h_sum_nn
      _ = _ := one_mul _
  -- Each Tᵢ →_P 0 in P^n-probability. Statements parameterized by ε > 0.
  have h_T1_oP : ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ abs ((n : ℝ)⁻¹ * (∑ i : Fin n,
              (((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
                (X i)) ^ 2) - Ĩ)})
      atTop (nhds 0) := by
    intro ε' hε'
    have h_lln := ell_tilde_sq_avg_lln (S_θ := S_θ) (T_nuis := T_nuis) (v := v)
                    ε' hε'
    have h_int := eff_score_sq_integral (S_θ := S_θ) (T_nuis := T_nuis) (v := v)
    have h_set_eq : ∀ n : ℕ,
        {X : Fin n → Ω |
          ε' ≤ abs ((n : ℝ)⁻¹ * (∑ i : Fin n,
              (((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
                (X i)) ^ 2) - Ĩ)}
        = {X : Fin n → Ω |
          ε' ≤ abs ((n : ℝ)⁻¹ * (∑ i : Fin n,
              (((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
                (X i)) ^ 2)
            - ∫ ω, (((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) :
                Lp ℝ 2 P) : Ω → ℝ) ω ^ 2 ∂P)} := by
      intro n; ext X; simp only [Set.mem_setOf_eq]; rw [h_int]
    simp_rw [h_set_eq]
    exact h_lln
  have h_T2_oP : ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ abs ((preliminary n X - θ₀) *
            ((n : ℝ)⁻¹ * (∑ i : Fin n,
              ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i) *
                (score_l_dot : Ω → ℝ) (X i))))})
      atTop (nhds 0) := by
    intro ε' hε'
    set Cint := ∫ ω,
      (((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) ω *
        (score_l_dot : Ω → ℝ) ω ∂P with hCint_def
    set B := |Cint| + 1 with hB_def
    have hB_pos : 0 < B := by
      have : 0 ≤ |Cint| := abs_nonneg _
      linarith
    rw [ENNReal.tendsto_nhds_zero]
    intro c hc
    by_cases hc_inf : c = ⊤
    · exact Filter.Eventually.of_forall fun _ => hc_inf ▸ le_top
    have hc_real_pos : 0 < ENNReal.toReal c := ENNReal.toReal_pos hc.ne' hc_inf
    have h_pre := preliminary_diff_oP hpf.preliminary_sqrt_n_rate (ε' / B)
                    (by positivity)
    rw [ENNReal.tendsto_nhds_zero] at h_pre
    have h_pre_le := h_pre (ENNReal.ofReal (ENNReal.toReal c / 2))
                            (by positivity)
    have h_lln := ell_tilde_score_l_dot_avg_lln
                    (S_θ := S_θ) (T_nuis := T_nuis) (v := v)
                    (score_l_dot := score_l_dot) 1 (by norm_num)
    rw [ENNReal.tendsto_nhds_zero] at h_lln
    have h_lln_le := h_lln (ENNReal.ofReal (ENNReal.toReal c / 2))
                            (by positivity)
    filter_upwards [h_pre_le, h_lln_le] with n h_pre_n h_lln_n
    have h_incl : {X : Fin n → Ω |
          ε' ≤ abs ((preliminary n X - θ₀) *
            ((n : ℝ)⁻¹ * (∑ i : Fin n,
              ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i) *
                (score_l_dot : Ω → ℝ) (X i))))}
        ⊆ {X : Fin n → Ω | ε' / B ≤ abs (preliminary n X - θ₀)} ∪
          {X : Fin n → Ω | 1 ≤ abs ((n : ℝ)⁻¹ * (∑ i : Fin n,
            ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i) *
              (score_l_dot : Ω → ℝ) (X i)) - Cint)} := by
      intro X hX
      simp only [Set.mem_union, Set.mem_setOf_eq] at hX ⊢
      by_contra hc'
      push Not at hc'
      obtain ⟨h1, h2⟩ := hc'
      set avg : ℝ := (n : ℝ)⁻¹ * (∑ i : Fin n,
        ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i) *
          (score_l_dot : Ω → ℝ) (X i)) with havg_def
      have h_avg_lt : abs avg < B := by
        have h_tri : abs avg ≤ abs (avg - Cint) + abs Cint := by
          have h_split : avg = (avg - Cint) + Cint := by ring
          calc abs avg = abs ((avg - Cint) + Cint) := by rw [← h_split]
            _ ≤ abs (avg - Cint) + abs Cint := abs_add_le _ _
        linarith
      have h_T2_lt : abs ((preliminary n X - θ₀) * avg) < ε' := by
        rw [abs_mul]
        calc abs (preliminary n X - θ₀) * abs avg
            ≤ (ε' / B) * abs avg :=
              mul_le_mul_of_nonneg_right h1.le (abs_nonneg _)
          _ < (ε' / B) * B := mul_lt_mul_of_pos_left h_avg_lt (by positivity)
          _ = ε' := by field_simp
      linarith
    refine (measure_mono h_incl).trans ?_
    refine (measure_union_le _ _).trans ?_
    have h_sum : ENNReal.ofReal (ENNReal.toReal c / 2) +
                  ENNReal.ofReal (ENNReal.toReal c / 2)
        = ENNReal.ofReal (ENNReal.toReal c) := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
    exact (add_le_add h_pre_n h_lln_n).trans
      (h_sum.le.trans (ENNReal.ofReal_toReal hc_inf).le)
  have h_T3_oP : ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ (preliminary n X - θ₀) ^ 2 *
            ((n : ℝ)⁻¹ * (∑ i : Fin n, ((score_l_dot : Ω → ℝ) (X i)) ^ 2))})
      atTop (nhds 0) := by
    intro ε' hε'
    set Cint := ∫ ω, ((score_l_dot : Ω → ℝ) ω) ^ 2 ∂P with hCint_def
    set C := |Cint| + 1 with hC_def
    have hC_pos : 0 < C := by
      have : 0 ≤ |Cint| := abs_nonneg _
      linarith
    rw [ENNReal.tendsto_nhds_zero]
    intro c hc
    by_cases hc_inf : c = ⊤
    · exact Filter.Eventually.of_forall fun _ => hc_inf ▸ le_top
    have hc_real_pos : 0 < ENNReal.toReal c := ENNReal.toReal_pos hc.ne' hc_inf
    obtain ⟨M_raw, hM_bound⟩ := hpf.preliminary_sqrt_n_rate
      (ENNReal.toReal c / 2) (by linarith)
    set M := max M_raw 1
    have hM_pos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hM_bound' : ∀ n,
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | M ≤ abs (Real.sqrt n * (preliminary n X - θ₀))}
        ≤ ENNReal.ofReal (ENNReal.toReal c / 2) := by
      intro n
      apply (measure_mono _).trans (hM_bound n)
      intro X hX; exact (le_max_left M_raw 1).trans hX
    have h_lln := score_l_dot_sq_avg_lln
                    (score_l_dot := score_l_dot) 1 (by norm_num)
    rw [ENNReal.tendsto_nhds_zero] at h_lln
    have h_lln_le := h_lln (ENNReal.ofReal (ENNReal.toReal c / 2))
                            (by positivity)
    filter_upwards [eventually_gt_atTop ⌈M ^ 2 * C / ε'⌉₊, h_lln_le]
      with n hn h_lln_n
    have h_n_real : M ^ 2 * C / ε' < (n : ℝ) := by
      have : ((⌈M ^ 2 * C / ε'⌉₊ : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact lt_of_le_of_lt (Nat.le_ceil _) this
    have hn_pos : 0 < n := by
      have hMC_pos : (0 : ℝ) < M ^ 2 * C / ε' := by positivity
      have : (0 : ℝ) < (n : ℝ) := lt_trans hMC_pos h_n_real
      exact_mod_cast this
    have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have h_M_sq_C_le : M ^ 2 * C ≤ (n : ℝ) * ε' := by
      rw [div_lt_iff₀ hε'] at h_n_real
      exact le_of_lt h_n_real
    have h_incl : {X : Fin n → Ω |
          ε' ≤ (preliminary n X - θ₀) ^ 2 *
            ((n : ℝ)⁻¹ * (∑ i : Fin n, ((score_l_dot : Ω → ℝ) (X i)) ^ 2))}
        ⊆ {X : Fin n → Ω | M ≤ abs (Real.sqrt n * (preliminary n X - θ₀))} ∪
          {X : Fin n → Ω | 1 ≤ abs ((n : ℝ)⁻¹ *
            (∑ i : Fin n, ((score_l_dot : Ω → ℝ) (X i)) ^ 2) - Cint)} := by
      intro X hX
      simp only [Set.mem_union, Set.mem_setOf_eq] at hX ⊢
      by_contra hc'
      push Not at hc'
      obtain ⟨h1, h2⟩ := hc'
      have h_pre_sq : (preliminary n X - θ₀) ^ 2 ≤ M ^ 2 / n := by
        have h_sq_lt : (Real.sqrt n * (preliminary n X - θ₀)) ^ 2 < M ^ 2 := by
          nlinarith [h1, sq_abs (Real.sqrt n * (preliminary n X - θ₀)),
            abs_nonneg (Real.sqrt n * (preliminary n X - θ₀)), hM_pos]
        have h_eq : (Real.sqrt n * (preliminary n X - θ₀)) ^ 2
            = (n : ℝ) * (preliminary n X - θ₀) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hn_real_pos.le]
        rw [h_eq] at h_sq_lt
        rw [le_div_iff₀ hn_real_pos]
        linarith
      have h_avg_nn : 0 ≤ (n : ℝ)⁻¹ *
          (∑ i : Fin n, ((score_l_dot : Ω → ℝ) (X i)) ^ 2) := by
        apply mul_nonneg (by positivity)
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have h_avg_lt_C : (n : ℝ)⁻¹ *
          (∑ i : Fin n, ((score_l_dot : Ω → ℝ) (X i)) ^ 2) < C := by
        have h_diff_lt : (n : ℝ)⁻¹ *
            (∑ i : Fin n, ((score_l_dot : Ω → ℝ) (X i)) ^ 2) - Cint < 1 :=
          (abs_lt.mp h2).2
        have h_Cint_le_abs : Cint ≤ |Cint| := le_abs_self Cint
        linarith
      have h_A_pos : (0 : ℝ) < M ^ 2 / n := div_pos (by positivity) hn_real_pos
      have h_T3_lt : (preliminary n X - θ₀) ^ 2 *
          ((n : ℝ)⁻¹ *
            (∑ i : Fin n, ((score_l_dot : Ω → ℝ) (X i)) ^ 2)) < M ^ 2 / n * C := by
        calc (preliminary n X - θ₀) ^ 2 *
            ((n : ℝ)⁻¹ *
              (∑ i : Fin n, ((score_l_dot : Ω → ℝ) (X i)) ^ 2))
            ≤ M ^ 2 / n *
              ((n : ℝ)⁻¹ *
                (∑ i : Fin n, ((score_l_dot : Ω → ℝ) (X i)) ^ 2)) :=
              mul_le_mul_of_nonneg_right h_pre_sq h_avg_nn
          _ < M ^ 2 / n * C := mul_lt_mul_of_pos_left h_avg_lt_C h_A_pos
      have h_div_le : M ^ 2 / n * C ≤ ε' := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hn_real_pos]
        linarith
      linarith
    refine (measure_mono h_incl).trans ?_
    refine (measure_union_le _ _).trans ?_
    have h_sum : ENNReal.ofReal (ENNReal.toReal c / 2) +
                  ENNReal.ofReal (ENNReal.toReal c / 2)
        = ENNReal.ofReal (ENNReal.toReal c) := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
    exact (add_le_add (hM_bound' n) h_lln_n).trans
      (h_sum.le.trans (ENNReal.ofReal_toReal hc_inf).le)
  have h_T4_oP : ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ abs ((n : ℝ)⁻¹ * (∑ i : Fin n,
            ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i) *
              (score_estimate_seq n (X i) (preliminary n X)
                - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
                - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i))))})
      atTop (nhds 0) := by
    intro ε' hε'
    set Cint_s := ∫ ω,
      (((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) :
        Ω → ℝ) ω ^ 2 ∂P with hCints_def
    set B := |Cint_s| + 1 with hB_def
    have hB_pos : 0 < B := by
      have : 0 ≤ |Cint_s| := abs_nonneg _
      linarith
    rw [ENNReal.tendsto_nhds_zero]
    intro c hc
    by_cases hc_inf : c = ⊤
    · exact Filter.Eventually.of_forall fun _ => hc_inf ▸ le_top
    have hc_real_pos : 0 < ENNReal.toReal c := ENNReal.toReal_pos hc.ne' hc_inf
    have h_lln := ell_tilde_sq_avg_lln (S_θ := S_θ) (T_nuis := T_nuis) (v := v)
                    1 (by norm_num)
    rw [ENNReal.tendsto_nhds_zero] at h_lln
    have h_lln_le := h_lln (ENNReal.ofReal (ENNReal.toReal c / 2))
                            (by positivity)
    have h_taylor := hpf.score_l2_taylor (ε' ^ 2 / B) (by positivity)
    rw [ENNReal.tendsto_nhds_zero] at h_taylor
    have h_taylor_le := h_taylor (ENNReal.ofReal (ENNReal.toReal c / 2))
                                  (by positivity)
    filter_upwards [h_lln_le, h_taylor_le, eventually_ge_atTop 1]
      with n h_lln_n h_taylor_n hn_ge
    have h_n_inv_le_one : (n : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]; right
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
      linarith
    have h_incl : {X : Fin n → Ω |
          ε' ≤ abs ((n : ℝ)⁻¹ * (∑ i : Fin n,
            ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i) *
              (score_estimate_seq n (X i) (preliminary n X)
                - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
                  (X i)
                - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i))))}
        ⊆ {X : Fin n → Ω | 1 ≤ abs ((n : ℝ)⁻¹ * (∑ i : Fin n,
            (((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
              (X i)) ^ 2) - Cint_s)} ∪
          {X : Fin n → Ω |
            ε' ^ 2 / B ≤ ∑ i : Fin n,
              (score_estimate_seq n (X i) (preliminary n X)
                - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
                  (X i)
                - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)) ^ 2} := by
      intro X hX
      simp only [Set.mem_union, Set.mem_setOf_eq] at hX ⊢
      by_contra hc'
      push Not at hc'
      obtain ⟨h1, h2⟩ := hc'
      set scoreEff_term : Fin n → ℝ := fun i =>
        ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
      set rterm : Fin n → ℝ := fun i =>
        score_estimate_seq n (X i) (preliminary n X)
          - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
          - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)
      set avg_s_sq : ℝ := (n : ℝ)⁻¹ * (∑ i : Fin n, (scoreEff_term i) ^ 2)
      set avg_r_sq : ℝ := (n : ℝ)⁻¹ * (∑ i : Fin n, (rterm i) ^ 2)
      set avg_prod : ℝ :=
        (n : ℝ)⁻¹ * (∑ i : Fin n, scoreEff_term i * rterm i)
      have h_sum_r_nn : 0 ≤ ∑ i : Fin n, (rterm i) ^ 2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have h_avg_r_sq_nn : 0 ≤ avg_r_sq := mul_nonneg (by positivity) h_sum_r_nn
      have h_avg_s_sq_nn : 0 ≤ avg_s_sq :=
        mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      have h_avg_s_sq_lt_B : avg_s_sq < B := by
        have h_diff_lt : avg_s_sq - Cint_s < 1 := (abs_lt.mp h1).2
        have h_Cint_le_abs : Cint_s ≤ |Cint_s| := le_abs_self Cint_s
        linarith
      have h_avg_r_sq_lt : avg_r_sq < ε' ^ 2 / B := by
        calc avg_r_sq = (n : ℝ)⁻¹ * (∑ i : Fin n, (rterm i) ^ 2) := rfl
          _ ≤ 1 * (∑ i : Fin n, (rterm i) ^ 2) :=
              mul_le_mul_of_nonneg_right h_n_inv_le_one h_sum_r_nn
          _ = ∑ i : Fin n, (rterm i) ^ 2 := one_mul _
          _ < ε' ^ 2 / B := h2
      have h_cs : avg_prod ^ 2 ≤ avg_s_sq * avg_r_sq :=
        avg_prod_sq_le scoreEff_term rterm
      have h_prod_bd : avg_s_sq * avg_r_sq < ε' ^ 2 := by
        calc avg_s_sq * avg_r_sq
            ≤ avg_s_sq * (ε' ^ 2 / B) :=
              mul_le_mul_of_nonneg_left h_avg_r_sq_lt.le h_avg_s_sq_nn
          _ < B * (ε' ^ 2 / B) :=
              mul_lt_mul_of_pos_right h_avg_s_sq_lt_B (by positivity)
          _ = ε' ^ 2 := by field_simp
      have h_avg_prod_sq_lt : avg_prod ^ 2 < ε' ^ 2 := lt_of_le_of_lt h_cs h_prod_bd
      have h_avg_prod_lt : abs avg_prod < ε' := by
        nlinarith [sq_abs avg_prod, abs_nonneg avg_prod, hε']
      linarith
    refine (measure_mono h_incl).trans ?_
    refine (measure_union_le _ _).trans ?_
    have h_sum : ENNReal.ofReal (ENNReal.toReal c / 2) +
                  ENNReal.ofReal (ENNReal.toReal c / 2)
        = ENNReal.ofReal (ENNReal.toReal c) := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
    exact (add_le_add h_lln_n h_taylor_n).trans
      (h_sum.le.trans (ENNReal.ofReal_toReal hc_inf).le)
  have h_T5_oP : ∀ ε > 0, Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ abs ((preliminary n X - θ₀) *
            ((n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i) *
              (score_estimate_seq n (X i) (preliminary n X)
                - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
                - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)))))})
      atTop (nhds 0) := by
    intro ε' hε'
    set Cint_l := ∫ ω, ((score_l_dot : Ω → ℝ) ω) ^ 2 ∂P with hCintl_def
    set D := |Cint_l| + 1 with hD_def
    have hD_pos : 0 < D := by
      have : 0 ≤ |Cint_l| := abs_nonneg _
      linarith
    rw [ENNReal.tendsto_nhds_zero]
    intro c hc
    by_cases hc_inf : c = ⊤
    · exact Filter.Eventually.of_forall fun _ => hc_inf ▸ le_top
    have hc_real_pos : 0 < ENNReal.toReal c := ENNReal.toReal_pos hc.ne' hc_inf
    have h_pre := preliminary_diff_oP hpf.preliminary_sqrt_n_rate 1 (by norm_num)
    rw [ENNReal.tendsto_nhds_zero] at h_pre
    have h_pre_le := h_pre (ENNReal.ofReal (ENNReal.toReal c / 3))
                            (by positivity)
    have h_lln := score_l_dot_sq_avg_lln
                    (score_l_dot := score_l_dot) 1 (by norm_num)
    rw [ENNReal.tendsto_nhds_zero] at h_lln
    have h_lln_le := h_lln (ENNReal.ofReal (ENNReal.toReal c / 3))
                            (by positivity)
    have h_taylor := hpf.score_l2_taylor (ε' ^ 2 / D) (by positivity)
    rw [ENNReal.tendsto_nhds_zero] at h_taylor
    have h_taylor_le := h_taylor (ENNReal.ofReal (ENNReal.toReal c / 3))
                                  (by positivity)
    filter_upwards [h_pre_le, h_lln_le, h_taylor_le, eventually_ge_atTop 1]
      with n h_pre_n h_lln_n h_taylor_n hn_ge
    have hn_real_pos : (0 : ℝ) < (n : ℝ) := by
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
      linarith
    have h_n_inv_le_one : (n : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]; right
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge
      linarith
    have h_incl : {X : Fin n → Ω |
          ε' ≤ abs ((preliminary n X - θ₀) *
            ((n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i) *
              (score_estimate_seq n (X i) (preliminary n X)
                - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
                  (X i)
                - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)))))}
        ⊆ {X : Fin n → Ω | 1 ≤ abs (preliminary n X - θ₀)} ∪
          ({X : Fin n → Ω | 1 ≤ abs ((n : ℝ)⁻¹ *
            (∑ i : Fin n, ((score_l_dot : Ω → ℝ) (X i)) ^ 2) - Cint_l)} ∪
          {X : Fin n → Ω |
            ε' ^ 2 / D ≤ ∑ i : Fin n,
              (score_estimate_seq n (X i) (preliminary n X)
                - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
                  (X i)
                - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)) ^ 2}) := by
      intro X hX
      simp only [Set.mem_union, Set.mem_setOf_eq] at hX ⊢
      by_contra hc'
      push Not at hc'
      obtain ⟨h1, h2, h3⟩ := hc'
      set rterm : Fin n → ℝ := fun i =>
        score_estimate_seq n (X i) (preliminary n X)
          - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
          - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i) with hrterm_def
      set lterm : Fin n → ℝ := fun i => (score_l_dot : Ω → ℝ) (X i) with hlterm_def
      set avg_l_sq : ℝ := (n : ℝ)⁻¹ * (∑ i : Fin n, (lterm i) ^ 2)
      set avg_r_sq : ℝ := (n : ℝ)⁻¹ * (∑ i : Fin n, (rterm i) ^ 2)
      set avg_prod : ℝ := (n : ℝ)⁻¹ * (∑ i : Fin n, lterm i * rterm i)
      have h_sum_r_nn : 0 ≤ ∑ i : Fin n, (rterm i) ^ 2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have h_avg_r_sq_nn : 0 ≤ avg_r_sq := mul_nonneg (by positivity) h_sum_r_nn
      have h_avg_l_sq_nn : 0 ≤ avg_l_sq :=
        mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      have h_avg_l_sq_lt_D : avg_l_sq < D := by
        have h_diff_lt : avg_l_sq - Cint_l < 1 := (abs_lt.mp h2).2
        have h_Cint_le_abs : Cint_l ≤ |Cint_l| := le_abs_self Cint_l
        linarith
      have h_avg_r_sq_lt : avg_r_sq < ε' ^ 2 / D := by
        calc avg_r_sq = (n : ℝ)⁻¹ * (∑ i : Fin n, (rterm i) ^ 2) := rfl
          _ ≤ 1 * (∑ i : Fin n, (rterm i) ^ 2) :=
              mul_le_mul_of_nonneg_right h_n_inv_le_one h_sum_r_nn
          _ = ∑ i : Fin n, (rterm i) ^ 2 := one_mul _
          _ < ε' ^ 2 / D := h3
      have h_cs : avg_prod ^ 2 ≤ avg_l_sq * avg_r_sq := avg_prod_sq_le lterm rterm
      have h_prod_bd : avg_l_sq * avg_r_sq < ε' ^ 2 := by
        calc avg_l_sq * avg_r_sq
            ≤ D * avg_r_sq :=
              mul_le_mul_of_nonneg_right h_avg_l_sq_lt_D.le h_avg_r_sq_nn
          _ < D * (ε' ^ 2 / D) := mul_lt_mul_of_pos_left h_avg_r_sq_lt hD_pos
          _ = ε' ^ 2 := by field_simp
      have h_avg_prod_sq_lt : avg_prod ^ 2 < ε' ^ 2 := lt_of_le_of_lt h_cs h_prod_bd
      have h_avg_prod_lt : abs avg_prod < ε' := by
        nlinarith [sq_abs avg_prod, abs_nonneg avg_prod, hε']
      have h_T5_lt : abs ((preliminary n X - θ₀) * avg_prod) < ε' := by
        rw [abs_mul]
        calc abs (preliminary n X - θ₀) * abs avg_prod
            ≤ abs (preliminary n X - θ₀) * ε' :=
              mul_le_mul_of_nonneg_left h_avg_prod_lt.le (abs_nonneg _)
          _ < 1 * ε' := mul_lt_mul_of_pos_right h1 hε'
          _ = ε' := one_mul _
      linarith
    refine (measure_mono h_incl).trans ?_
    refine (measure_union_le _ _).trans ?_
    refine le_trans (add_le_add h_pre_n (measure_union_le _ _)) ?_
    have h_sum : ENNReal.ofReal (ENNReal.toReal c / 3) +
                  (ENNReal.ofReal (ENNReal.toReal c / 3) +
                  ENNReal.ofReal (ENNReal.toReal c / 3))
        = ENNReal.ofReal (ENNReal.toReal c) := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith),
          ← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1; ring
    exact (add_le_add le_rfl (add_le_add h_lln_n h_taylor_n)).trans
      (h_sum.le.trans (ENNReal.ofReal_toReal hc_inf).le)
  -- 6-term union bound assembly. For any η > 0, eventually P^n ≤ ofReal η.
  have key : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ abs (info_estimate_seq n X - Ĩ)}
      ≤ ENNReal.ofReal η := by
    intro η hη
    -- Apply each Tᵢ_oP at threshold ε/6 (with weights), giving bound ofReal (η/6).
    have hε6 : 0 < ε / 6 := by linarith
    have hε12 : 0 < ε / 12 := by linarith
    have h_T1_inst := h_T1_oP (ε / 6) hε6
    have h_T2_inst := h_T2_oP (ε / 12) hε12
    have h_T3_inst := h_T3_oP (ε / 6) hε6
    have h_T4_inst := h_T4_oP (ε / 12) hε12
    have h_T5_inst := h_T5_oP (ε / 12) hε12
    have h_T6_inst := h_T6_oP (ε / 6) hε6
    rw [ENNReal.tendsto_nhds_zero] at h_T1_inst h_T2_inst h_T3_inst h_T4_inst h_T5_inst h_T6_inst
    have h_T1_le := h_T1_inst (ENNReal.ofReal (η / 6)) (by positivity)
    have h_T2_le := h_T2_inst (ENNReal.ofReal (η / 6)) (by positivity)
    have h_T3_le := h_T3_inst (ENNReal.ofReal (η / 6)) (by positivity)
    have h_T4_le := h_T4_inst (ENNReal.ofReal (η / 6)) (by positivity)
    have h_T5_le := h_T5_inst (ENNReal.ofReal (η / 6)) (by positivity)
    have h_T6_le := h_T6_inst (ENNReal.ofReal (η / 6)) (by positivity)
    filter_upwards [h_T1_le, h_T2_le, h_T3_le, h_T4_le, h_T5_le, h_T6_le]
      with n h1 h2 h3 h4 h5 h6
    -- 6-term set inclusion via h_info_alg + iterated triangle inequality.
    have h_incl : {X : Fin n → Ω | ε ≤ abs (info_estimate_seq n X - Ĩ)}
        ⊆ {X : Fin n → Ω |
            ε / 6 ≤ abs ((n : ℝ)⁻¹ * (∑ i : Fin n,
              (((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
                (X i)) ^ 2) - Ĩ)} ∪
          ({X : Fin n → Ω |
              ε / 12 ≤ abs ((preliminary n X - θ₀) *
                ((n : ℝ)⁻¹ * (∑ i : Fin n,
                  ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
                    (X i) *
                    (score_l_dot : Ω → ℝ) (X i))))} ∪
          ({X : Fin n → Ω |
              ε / 6 ≤ (preliminary n X - θ₀) ^ 2 *
                ((n : ℝ)⁻¹ * (∑ i : Fin n,
                  ((score_l_dot : Ω → ℝ) (X i)) ^ 2))} ∪
          ({X : Fin n → Ω |
              ε / 12 ≤ abs ((n : ℝ)⁻¹ * (∑ i : Fin n,
                ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
                  (X i) *
                  (score_estimate_seq n (X i) (preliminary n X)
                    - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
                      (X i)
                    - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i))))} ∪
          ({X : Fin n → Ω |
              ε / 12 ≤ abs ((preliminary n X - θ₀) *
                ((n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i) *
                  (score_estimate_seq n (X i) (preliminary n X)
                    - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
                      (X i)
                    - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)))))} ∪
          {X : Fin n → Ω |
              ε / 6 ≤ (n : ℝ)⁻¹ * (∑ i : Fin n,
                (score_estimate_seq n (X i) (preliminary n X)
                  - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
                    (X i)
                  - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)) ^ 2)})))) := by
      intro X hX
      simp only [Set.mem_union, Set.mem_setOf_eq] at hX ⊢
      by_contra hc
      push Not at hc
      obtain ⟨hT1, hT2, hT3, hT4, hT5, hT6⟩ := hc
      set t1 : ℝ := (n : ℝ)⁻¹ * (∑ i : Fin n,
        (((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P)
          (X i)) ^ 2) - Ĩ
      set t2 : ℝ := (preliminary n X - θ₀) *
        ((n : ℝ)⁻¹ * (∑ i : Fin n,
          ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i) *
            (score_l_dot : Ω → ℝ) (X i)))
      set t3 : ℝ := (preliminary n X - θ₀) ^ 2 *
        ((n : ℝ)⁻¹ * (∑ i : Fin n, ((score_l_dot : Ω → ℝ) (X i)) ^ 2))
      set t4 : ℝ := (n : ℝ)⁻¹ * (∑ i : Fin n,
        ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i) *
          (score_estimate_seq n (X i) (preliminary n X)
            - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
            - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)))
      set t5 : ℝ := (preliminary n X - θ₀) *
        ((n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i) *
          (score_estimate_seq n (X i) (preliminary n X)
            - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
            - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i))))
      set t6 : ℝ := (n : ℝ)⁻¹ * (∑ i : Fin n,
        (score_estimate_seq n (X i) (preliminary n X)
          - ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) (X i)
          - (preliminary n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)) ^ 2)
      have h_t3_nn : 0 ≤ t3 :=
        mul_nonneg (sq_nonneg _)
          (mul_nonneg (by positivity)
            (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
      have h_t6_nn : 0 ≤ t6 :=
        mul_nonneg (by positivity)
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      have h_alg : info_estimate_seq n X - Ĩ
          = t1 + 2 * t2 + t3 + 2 * t4 + 2 * t5 + t6 := h_info_alg n X
      rw [h_alg] at hX
      have h_abs_2t2 : abs (2 * t2) = 2 * abs t2 := by rw [abs_mul]; simp
      have h_abs_2t4 : abs (2 * t4) = 2 * abs t4 := by rw [abs_mul]; simp
      have h_abs_2t5 : abs (2 * t5) = 2 * abs t5 := by rw [abs_mul]; simp
      have h_abs_t3 : abs t3 = t3 := abs_of_nonneg h_t3_nn
      have h_abs_t6 : abs t6 = t6 := abs_of_nonneg h_t6_nn
      have h_total : abs (t1 + 2 * t2 + t3 + 2 * t4 + 2 * t5 + t6)
          ≤ abs t1 + 2 * abs t2 + t3 + 2 * abs t4 + 2 * abs t5 + t6 := by
        have e1 : t1 + 2 * t2 + t3 + 2 * t4 + 2 * t5 + t6
            = (t1 + 2 * t2 + t3 + 2 * t4 + 2 * t5) + t6 := by ring
        have e2 : t1 + 2 * t2 + t3 + 2 * t4 + 2 * t5
            = (t1 + 2 * t2 + t3 + 2 * t4) + 2 * t5 := by ring
        have e3 : t1 + 2 * t2 + t3 + 2 * t4
            = (t1 + 2 * t2 + t3) + 2 * t4 := by ring
        have e4 : t1 + 2 * t2 + t3 = (t1 + 2 * t2) + t3 := by ring
        rw [e1]
        have b1 : abs ((t1 + 2 * t2 + t3 + 2 * t4 + 2 * t5) + t6)
            ≤ abs (t1 + 2 * t2 + t3 + 2 * t4 + 2 * t5) + abs t6 := abs_add_le _ _
        rw [e2] at b1
        have b2 : abs ((t1 + 2 * t2 + t3 + 2 * t4) + 2 * t5)
            ≤ abs (t1 + 2 * t2 + t3 + 2 * t4) + abs (2 * t5) := abs_add_le _ _
        rw [e3] at b2
        have b3 : abs ((t1 + 2 * t2 + t3) + 2 * t4)
            ≤ abs (t1 + 2 * t2 + t3) + abs (2 * t4) := abs_add_le _ _
        rw [e4] at b3
        have b4 : abs ((t1 + 2 * t2) + t3)
            ≤ abs (t1 + 2 * t2) + abs t3 := abs_add_le _ _
        have b5 : abs (t1 + 2 * t2) ≤ abs t1 + abs (2 * t2) := abs_add_le _ _
        simp only [h_abs_2t2, h_abs_2t4, h_abs_2t5, h_abs_t3, h_abs_t6]
          at b1 b2 b3 b4 b5
        linarith
      linarith
    refine (measure_mono h_incl).trans ?_
    refine le_trans (measure_union_le _ _) ?_
    refine le_trans (add_le_add le_rfl (measure_union_le _ _)) ?_
    refine le_trans (add_le_add le_rfl
      (add_le_add le_rfl (measure_union_le _ _))) ?_
    refine le_trans (add_le_add le_rfl (add_le_add le_rfl
      (add_le_add le_rfl (measure_union_le _ _)))) ?_
    refine le_trans (add_le_add le_rfl (add_le_add le_rfl
      (add_le_add le_rfl (add_le_add le_rfl (measure_union_le _ _))))) ?_
    refine le_trans
      (add_le_add h1 (add_le_add h2 (add_le_add h3
        (add_le_add h4 (add_le_add h5 h6))))) ?_
    have hη6_nn : (0 : ℝ) ≤ η / 6 := by linarith
    have h_eq : ENNReal.ofReal (η / 6) +
                  (ENNReal.ofReal (η / 6) +
                  (ENNReal.ofReal (η / 6) +
                  (ENNReal.ofReal (η / 6) +
                  (ENNReal.ofReal (η / 6) +
                  ENNReal.ofReal (η / 6)))))
        = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add hη6_nn hη6_nn,
          ← ENNReal.ofReal_add hη6_nn (by positivity),
          ← ENNReal.ofReal_add hη6_nn (by positivity),
          ← ENNReal.ofReal_add hη6_nn (by positivity),
          ← ENNReal.ofReal_add hη6_nn (by positivity)]
      congr 1; ring
    exact h_eq.le
  -- Conclude via ENNReal.tendsto_nhds_zero
  rw [ENNReal.tendsto_nhds_zero]
  intro c hc
  by_cases hc_inf : c = ⊤
  · exact Filter.Eventually.of_forall fun _ => hc_inf ▸ le_top
  have hc_real_pos : 0 < ENNReal.toReal c :=
    ENNReal.toReal_pos hc.ne' hc_inf
  filter_upwards [key (ENNReal.toReal c) hc_real_pos] with n hn
  exact hn.trans (ENNReal.ofReal_toReal hc_inf).le

/-- **Pⁿ-a.e. equality of sum over coordinates of `(c • f)` and `c · f`.**

Bridge lemma for `Lp.coeFn_smul` lifted to the i-th coordinate of the
product measure `Pⁿ`. For each i, evaluating along the i-th projection
sends Pⁿ-a.e. to P-a.e., so finitely intersecting over `i : Fin n` gives
the Pⁿ-a.e. statement on the full sum, via
`MeasureTheory.Measure.MeasurePreserving` of the i-th evaluation map. -/
private lemma sum_smul_lp_ae_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    (c : ℝ) (f : Lp ℝ 2 P) (n : ℕ) :
    (fun X : Fin n → Ω => ∑ i : Fin n, (((c • f) : Lp ℝ 2 P) : Ω → ℝ) (X i))
      =ᵐ[Measure.pi (fun _ : Fin n => P)]
    (fun X => c * ∑ i : Fin n, (f : Ω → ℝ) (X i)) := by
  have h_pt : ∀ᵐ ω ∂P,
      (((c • f) : Lp ℝ 2 P) : Ω → ℝ) ω = c * (f : Ω → ℝ) ω := by
    filter_upwards [Lp.coeFn_smul c f] with ω hω
    simpa [Pi.smul_apply, smul_eq_mul] using hω
  have h_each : ∀ i : Fin n,
      ∀ᵐ X ∂(Measure.pi (fun _ : Fin n => P)),
        (((c • f) : Lp ℝ 2 P) : Ω → ℝ) (X i) = c * (f : Ω → ℝ) (X i) := by
    intro i
    exact (MeasureTheory.measurePreserving_eval
            (μ := fun _ : Fin n => P) i).quasiMeasurePreserving.ae h_pt
  have h_all : ∀ᵐ X ∂(Measure.pi (fun _ : Fin n => P)),
      ∀ i ∈ (Finset.univ : Finset (Fin n)),
        (((c • f) : Lp ℝ 2 P) : Ω → ℝ) (X i) = c * (f : Ω → ℝ) (X i) := by
    rw [Filter.eventually_all_finset]
    intro i _
    exact h_each i
  filter_upwards [h_all] with X hX
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i hi => hX i hi)

/-- **vdV thm:25.57 — Taylor-based discharge.**

Given `OneStepTaylorHyp` (Taylor-regularity primitive conditions) and the
one-step formula `estimator_def`, the one-step estimator is asymptotically
linear at `P` with influence function `(1/Ĩ) • ℓ̃` and centering `θ₀`.

**Proof.** Substitute `estimator_def` into the AL residual, decompose as
`error_A + error_B + error_C` (using the Pfanzagl display `√n·Pfanz_n →_P 0`
and info consistency `Î_n →_P Ĩ` derived from `OneStepTaylorHyp`), use the
union bound `Pⁿ(|res| ≥ ε) ≤ Pⁿ(|A| ≥ ε/3) + Pⁿ(|B| ≥ ε/3) + Pⁿ(|C| ≥ ε/3)`,
apply the three sub-lemmas, and squeeze. The bridge between the AL goal set
(which uses `((c • φ : ↥M) : Lp)` smul-then-coerce) and the pointwise
residual sets (which use scalar multiplication directly) is via `Lp.coeFn_smul`,
lifted to the product measure `Pⁿ` per coordinate by `sum_smul_lp_ae_eq`.

Reference: vdV §25.8, thm:25.57 + Taylor remark. -/
theorem oneStep_asympLinear_of_taylor
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {preliminary : ∀ n, (Fin n → Ω) → ℝ}
    {score_estimate_seq : ℕ → Ω → ℝ → ℝ}
    {info_estimate_seq : ∀ n, (Fin n → Ω) → ℝ}
    {score_l_dot : Lp ℝ 2 P}
    {θ₀ : ℝ}
    (hpf : OneStepTaylorHyp P Θ S_θ T_nuis v preliminary score_estimate_seq
              info_estimate_seq score_l_dot θ₀)
    (estimator : ∀ n, (Fin n → Ω) → ℝ)
    (estimator_def : ∀ n (X : Fin n → Ω),
        estimator n X
          = preliminary n X
            + (info_estimate_seq n X)⁻¹
                * ((n : ℝ)⁻¹ * ∑ i : Fin n,
                    score_estimate_seq n (X i) (preliminary n X))) :
    AsymptoticallyLinearAt estimator P
      ((1 / efficientInformation S_θ T_nuis v) • efficientScore S_θ T_nuis v)
      θ₀ := by
  set Ĩ := efficientInformation S_θ T_nuis v with hĨ_def
  -- Derived theorems on `hpf` ready for the three error lemmas.
  have h_pfanz := hpf.pfanzagl_display
  have h_info := hpf.info_consistency
  -- Unfold AL definition: for each ε > 0, show Pⁿ({|residual| ≥ ε}) → 0.
  intro ε hε
  -- Apply error_A, error_B, error_C at threshold ε/3.
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  have h_A := error_A_tendsto_zero (info_estimate_seq := info_estimate_seq)
                hpf.hI_pos h_info (ε / 3) hε3
  have h_B := error_B_tendsto_zero (preliminary := preliminary)
                (score_estimate_seq := score_estimate_seq)
                (info_estimate_seq := info_estimate_seq) (θ₀ := θ₀)
                hpf.hI_pos h_pfanz h_info (ε / 3) hε3
  have h_C := error_C_tendsto_zero (preliminary := preliminary)
                (info_estimate_seq := info_estimate_seq) (θ₀ := θ₀)
                hpf.hI_pos h_info hpf.preliminary_sqrt_n_rate (ε / 3) hε3
  -- Squeeze: bound the AL probability by sum of three error probabilities,
  -- each → 0.
  rw [ENNReal.tendsto_nhds_zero] at h_A h_B h_C
  rw [ENNReal.tendsto_nhds_zero]
  intro c hc
  by_cases hc_inf : c = ⊤
  · exact Filter.Eventually.of_forall fun _ => hc_inf ▸ le_top
  have hc_real_pos : (0 : ℝ) < ENNReal.toReal c :=
    ENNReal.toReal_pos hc.ne' hc_inf
  -- Apply each error lemma at threshold ENNReal.ofReal (ENNReal.toReal c / 3)
  have h_A_le := h_A (ENNReal.ofReal (ENNReal.toReal c / 3)) (by positivity)
  have h_B_le := h_B (ENNReal.ofReal (ENNReal.toReal c / 3)) (by positivity)
  have h_C_le := h_C (ENNReal.ofReal (ENNReal.toReal c / 3)) (by positivity)
  filter_upwards [h_A_le, h_B_le, h_C_le] with n h_A_n h_B_n h_C_n
  -- The AL goal set `S_AL` equals (a.e.) the pointwise residual set `S_pt`.
  -- We work via `measure_congr` after establishing a.e.-set equality.
  set scoreEff : Ω → ℝ := fun ω =>
    (((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) ω
    with hscoreEff_def
  -- Define the AL residual
  set res_AL : (Fin n → Ω) → ℝ := fun X =>
    Real.sqrt n * (estimator n X - θ₀)
      - (Real.sqrt n)⁻¹ * (∑ i : Fin n,
          ((((1 / Ĩ) • efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) :
            Lp ℝ 2 P) : Ω → ℝ) (X i))
    with hres_AL_def
  -- Define the pointwise residual (after Lp.coeFn_smul a.e. simplification)
  set res_pt : (Fin n → Ω) → ℝ := fun X =>
    Real.sqrt n * (estimator n X - θ₀)
      - Ĩ⁻¹ * ((Real.sqrt n)⁻¹ * (∑ i : Fin n, scoreEff (X i)))
    with hres_pt_def
  -- Step 1: Show {|res_AL| ≥ ε} =ᵃᵉ {|res_pt| ≥ ε} via Lp.coeFn_smul.
  have h_ae_eq : (fun X => res_AL X) =ᵐ[Measure.pi (fun _ : Fin n => P)]
                  (fun X => res_pt X) := by
    -- The smul-Lp coercion equals scalar multiplication a.e. via sum_smul_lp_ae_eq.
    have h_sum_eq := sum_smul_lp_ae_eq (1 / Ĩ)
                    ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) n
    -- The submodule smul coerces definitionally to Lp smul:
    -- `(((1/Ĩ) • efficientScore : ↥M) : Lp) = (1/Ĩ) • ((efficientScore : ↥M) : Lp)` (rfl)
    filter_upwards [h_sum_eq] with X hX
    simp only [hres_AL_def, hres_pt_def]
    -- Rewrite the AL sum using h_sum_eq, then recover res_pt's form.
    have h_target :
        (∑ i : Fin n, ((((1 / Ĩ) • efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) :
            Lp ℝ 2 P) : Ω → ℝ) (X i))
        = (1 / Ĩ) * ∑ i : Fin n, scoreEff (X i) := hX
    rw [h_target]
    -- (√n)⁻¹ · ((1/Ĩ) · Σ scoreEff) = Ĩ⁻¹ · ((√n)⁻¹ · Σ scoreEff)
    rw [one_div]; ring
  -- Step 2: Use measure_congr on the level sets.
  have h_set_ae_eq :
      {X : Fin n → Ω | ε ≤ |res_AL X|} =ᵐ[Measure.pi (fun _ : Fin n => P)]
      {X : Fin n → Ω | ε ≤ |res_pt X|} := by
    filter_upwards [h_ae_eq] with X hX
    change (ε ≤ |res_AL X|) = (ε ≤ |res_pt X|)
    rw [hX]
  have h_meas_eq :
      (Measure.pi (fun _ : Fin n => P)) {X : Fin n → Ω | ε ≤ |res_AL X|}
      = (Measure.pi (fun _ : Fin n => P)) {X : Fin n → Ω | ε ≤ |res_pt X|} :=
    measure_congr h_set_ae_eq
  -- Step 3: Algebraic decomposition
  --   res_pt X = error_A_val + error_B_val + error_C_val
  -- where (substituting estimator_def):
  --   res_pt = √n·(prel - θ₀) + Î⁻¹·(1/√n)·Σ score_est - Ĩ⁻¹·(1/√n)·Σ scoreEff
  --   Pfanz_val := (1/n)·Σ score_est - (1/n)·Σ scoreEff + Ĩ·(prel - θ₀)
  --   error_A_val := (Î⁻¹ - Ĩ⁻¹) · (1/√n)·Σ scoreEff
  --   error_B_val := Î⁻¹ · √n · Pfanz_val
  --   error_C_val := √n·(prel - θ₀) · (1 - Î⁻¹·Ĩ)
  have h_alg : ∀ X : Fin n → Ω, res_pt X
      = ((info_estimate_seq n X)⁻¹ - Ĩ⁻¹) *
          ((Real.sqrt n)⁻¹ * (∑ i : Fin n, scoreEff (X i)))
        + (info_estimate_seq n X)⁻¹ *
            (Real.sqrt n *
              ((n : ℝ)⁻¹ * (∑ i : Fin n,
                score_estimate_seq n (X i) (preliminary n X))
                - (n : ℝ)⁻¹ * (∑ i : Fin n, scoreEff (X i))
                + Ĩ * (preliminary n X - θ₀)))
        + Real.sqrt n * (preliminary n X - θ₀) *
            (1 - (info_estimate_seq n X)⁻¹ * Ĩ) := by
    intro X
    simp only [hres_pt_def]
    rw [estimator_def n X]
    by_cases hn : n = 0
    · subst hn; simp
    have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
    have hsq_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
    have hsq_ne : Real.sqrt n ≠ 0 := ne_of_gt hsq_pos
    -- Key identity: √n · n⁻¹ = (√n)⁻¹.
    have h_sqrt_inv : Real.sqrt n * (n : ℝ)⁻¹ = (Real.sqrt n)⁻¹ := by
      have h_sqrt_sq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
        Real.mul_self_sqrt hn_pos.le
      rw [show ((n : ℝ)⁻¹) = (Real.sqrt n * Real.sqrt n)⁻¹ by rw [h_sqrt_sq],
          mul_inv, ← mul_assoc, mul_inv_cancel₀ hsq_ne, one_mul]
    -- Distribute and use h_sqrt_inv to clear the only nonlinear term.
    set s : ℝ := Real.sqrt n with hs_def
    set Î : ℝ := info_estimate_seq n X with hÎ_def
    set p : ℝ := preliminary n X with hp_def
    set σe : ℝ := ∑ i : Fin n, score_estimate_seq n (X i) p with hσe_def
    set σs : ℝ := ∑ i : Fin n, scoreEff (X i) with hσs_def
    -- LHS = s · ((p + Î⁻¹ · ((n)⁻¹ · σe)) - θ₀) - Ĩ⁻¹ · (s⁻¹ · σs)
    --     = s · (p - θ₀) + s · Î⁻¹ · (n)⁻¹ · σe - Ĩ⁻¹ · s⁻¹ · σs
    --     = s · (p - θ₀) + Î⁻¹ · s⁻¹ · σe - Ĩ⁻¹ · s⁻¹ · σs   (h_sqrt_inv)
    change s * (p + Î⁻¹ * ((n : ℝ)⁻¹ * σe) - θ₀)
          - Ĩ⁻¹ * (s⁻¹ * σs)
        = (Î⁻¹ - Ĩ⁻¹) * (s⁻¹ * σs)
          + Î⁻¹ * (s * ((n : ℝ)⁻¹ * σe - (n : ℝ)⁻¹ * σs + Ĩ * (p - θ₀)))
          + s * (p - θ₀) * (1 - Î⁻¹ * Ĩ)
    have h_step2 : s * ((n : ℝ)⁻¹ * σs) = s⁻¹ * σs := by
      rw [← mul_assoc, h_sqrt_inv]
    -- Only h_step2 is needed: σe terms cancel by ring; σs terms collapse via
    -- s · (n)⁻¹ · σs = s⁻¹ · σs (h_step2), giving the Î⁻¹ coefficient.
    linear_combination Î⁻¹ * h_step2
  -- Step 4: Set inclusion via h_alg + triangle inequality
  have h_incl :
      {X : Fin n → Ω | ε ≤ |res_pt X|} ⊆
        {X : Fin n → Ω | ε / 3 ≤
          |((info_estimate_seq n X)⁻¹ - Ĩ⁻¹)| *
            |((Real.sqrt n)⁻¹ * ∑ i : Fin n, scoreEff (X i))|} ∪
        ({X : Fin n → Ω | ε / 3 ≤ |(info_estimate_seq n X)⁻¹|
          * (Real.sqrt n * |((n : ℝ)⁻¹ *
              (∑ i : Fin n, score_estimate_seq n (X i) (preliminary n X))
              - (n : ℝ)⁻¹ * (∑ i : Fin n, scoreEff (X i))
              + Ĩ * (preliminary n X - θ₀))|)} ∪
         {X : Fin n → Ω | ε / 3 ≤
          |(Real.sqrt n * (preliminary n X - θ₀))|
            * |1 - (info_estimate_seq n X)⁻¹ * Ĩ|}) := by
    intro X hX
    simp only [Set.mem_union, Set.mem_setOf_eq] at hX ⊢
    by_contra hc'
    push Not at hc'
    obtain ⟨hA, hB, hC⟩ := hc'
    rw [h_alg X] at hX
    -- Define abbreviations and abs bounds for each error term.
    have h_absA : |((info_estimate_seq n X)⁻¹ - Ĩ⁻¹) *
        ((Real.sqrt n)⁻¹ * (∑ i : Fin n, scoreEff (X i)))| < ε / 3 := by
      rw [abs_mul]; exact hA
    have h_absB : |(info_estimate_seq n X)⁻¹ *
        (Real.sqrt n *
          ((n : ℝ)⁻¹ * (∑ i : Fin n,
            score_estimate_seq n (X i) (preliminary n X))
            - (n : ℝ)⁻¹ * (∑ i : Fin n, scoreEff (X i))
            + Ĩ * (preliminary n X - θ₀)))| < ε / 3 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact hB
    have h_absC : |Real.sqrt n * (preliminary n X - θ₀) *
        (1 - (info_estimate_seq n X)⁻¹ * Ĩ)| < ε / 3 := by
      rw [abs_mul]; exact hC
    -- Triangle inequality on the three-term sum
    set A : ℝ := ((info_estimate_seq n X)⁻¹ - Ĩ⁻¹) *
        ((Real.sqrt n)⁻¹ * (∑ i : Fin n, scoreEff (X i))) with hA_def
    set Bv : ℝ := (info_estimate_seq n X)⁻¹ *
        (Real.sqrt n *
          ((n : ℝ)⁻¹ * (∑ i : Fin n,
            score_estimate_seq n (X i) (preliminary n X))
            - (n : ℝ)⁻¹ * (∑ i : Fin n, scoreEff (X i))
            + Ĩ * (preliminary n X - θ₀))) with hBv_def
    set Cv : ℝ := Real.sqrt n * (preliminary n X - θ₀) *
        (1 - (info_estimate_seq n X)⁻¹ * Ĩ) with hCv_def
    have h_sum : |A + Bv + Cv| ≤ |A| + |Bv| + |Cv| := by
      have h1 := abs_add_le (A + Bv) Cv
      have h2 := abs_add_le A Bv
      linarith
    linarith
  -- Step 5: Apply union bound + measure_mono.
  -- h_incl: {ε ≤ |res_pt|} ⊆ SA ∪ (SB ∪ SC)
  -- After measure_mono: μ(SA ∪ (SB ∪ SC))
  -- measure_union_le: ≤ μ SA + μ(SB ∪ SC)
  -- add_le_add le_rfl (measure_union_le _ _): ≤ μ SA + (μ SB + μ SC)
  rw [h_meas_eq]
  refine le_trans (measure_mono h_incl) ?_
  refine le_trans (measure_union_le _ _) ?_
  refine le_trans (add_le_add le_rfl (measure_union_le _ _)) ?_
  -- Now: μ SA + (μ SB + μ SC) ≤ ofReal/3 + (ofReal/3 + ofReal/3)
  refine le_trans (add_le_add h_A_n (add_le_add h_B_n h_C_n)) ?_
  -- Sum: 3 · ofReal (toReal c / 3) ≤ ofReal (toReal c) ≤ c
  have h_sum3 : ENNReal.ofReal (ENNReal.toReal c / 3) +
                  (ENNReal.ofReal (ENNReal.toReal c / 3) +
                   ENNReal.ofReal (ENNReal.toReal c / 3))
      = ENNReal.ofReal (ENNReal.toReal c) := by
    rw [← ENNReal.ofReal_add (by linarith) (by linarith),
        ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1; ring
  exact h_sum3.le.trans (ENNReal.ofReal_toReal hc_inf).le

/-- **Adapter: `OneStepTaylorHyp` → `asympLinear_25_57` field.**

Fills `OneStepAssumptions.asympLinear_25_57` from primitive Taylor-regularity
conditions. -/
theorem OneStepTaylorHyp.toAsymptoticallyLinear
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {preliminary : ∀ n, (Fin n → Ω) → ℝ}
    {score_estimate_seq : ℕ → Ω → ℝ → ℝ}
    {info_estimate_seq : ∀ n, (Fin n → Ω) → ℝ}
    {score_l_dot : Lp ℝ 2 P}
    {θ₀ : ℝ}
    (h : OneStepTaylorHyp P Θ S_θ T_nuis v preliminary score_estimate_seq
            info_estimate_seq score_l_dot θ₀)
    (estimator : ∀ n, (Fin n → Ω) → ℝ)
    (estimator_def : ∀ n (X : Fin n → Ω),
        estimator n X
          = preliminary n X
            + (info_estimate_seq n X)⁻¹
                * ((n : ℝ)⁻¹ * ∑ i : Fin n,
                    score_estimate_seq n (X i) (preliminary n X))) :
    AsymptoticallyLinearAt estimator P
      ((1 / efficientInformation S_θ T_nuis v) • efficientScore S_θ T_nuis v)
      θ₀ :=
  oneStep_asympLinear_of_taylor h estimator estimator_def

end AsymptoticStatistics.Asymptotics.Discharge.OneStep
