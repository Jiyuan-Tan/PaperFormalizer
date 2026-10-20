module
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimator

@[expose] public section

/-!
# Z-estimator bias-residual expansion (explicit bias)

The explicit-bias variant of the Z-estimator bias-residual expansion, with a
residual term matching vdV's `√n · P_{θ̂_n,η} ℓ̃_{θ̂_n,η̂_n}`.

This differs from the bias=0 specialization (`ZEstimatorBiasResidual`) by
dropping the estimating-equation rate `score_eq` and reinstating it with a
bias residual `bias : ∀ n, (Fin n → Ω) → ℝ`, the Lean analog of vdV's
`√n · P_{θ̂_n,η} ℓ̃_{θ̂_n,η̂_n}` (modulo the truth-P vs P_{θ̂_n,η} measure shift,
discussed in the main theorem's docstring).

The bias version replaces `ZEstimatorTaylorCore`'s equation
`score_eq : √n 𝕡_n ℓ̃ →_P 0` with
`score_eq_with_bias : √n 𝕡_n ℓ̃ − bias →_P 0`, allowing a nonzero bias term in
the asymptotic-linear expansion. Root-`n` consistency is an independent
hypothesis of this version and is supplied directly by the caller.

Headline declaration: `zEstimator_biasResidual_asympLinear_of_taylor_explicit`.

Reference: vdV §25.8, Theorem 25.59.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal Function

namespace AsymptoticStatistics.Asymptotics.Discharge.ZEstimator

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.Asymptotics.ZEstimator

variable {Ω : Type} [MeasurableSpace Ω]

/-- *vdV §25.8, Theorem 25.59 explicit-bias hypothesis bundle (Taylor route).*

Extends `ZEstimatorTaylorCoreBase` (the no-bias-and-no-score_eq core) with three
new fields encoding the bias-residual setup of Theorem 25.59:
- `bias : ∀ n, (Fin n → Ω) → ℝ`: the bias residual that the concrete model
  identifies, the Lean analog of `√n · P_{θ̂_n,η} ℓ̃_{θ̂_n,η̂_n}`.
- `score_eq_with_bias`: the bias-shifted estimating-equation
  `√n · 𝕡_n ℓ̃_{θ̂_n,η̂_n} − bias_n →_P 0` under `Pⁿ`. Replaces `score_eq` from
  the bias=0 bundle (which forced `bias = o_P(1)`).
- `sqrt_n_consistency`: `√n · (θ̂_n − θ₀) = O_P(1)`, supplied directly as
  an independent hypothesis of the explicit-bias interface.

Reference: vdV §25.8, Theorem 25.59. -/
structure ZEstimatorBiasResidualExplicitTaylorHyp
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (v : Θ)
    (estimator : ∀ n, (Fin n → Ω) → ℝ)
    (score_func_seq : ∀ n, (Fin n → Ω) → (Ω → ℝ))
    (score_truth : Ω → ℝ)
    (donsker_class : Set (Ω → ℝ))
    (score_l_dot : Lp ℝ 2 P)
    (θ₀ : ℝ)
    (bias : ∀ n, (Fin n → Ω) → ℝ) : Prop
    extends ZEstimatorTaylorCoreBase P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀ where
  /-- vdV §25.8, Theorem 25.59 (estimating-equation residual):
  `√n · 𝕡_n ℓ̃_{θ̂_n,η̂_n} − bias_n →_P 0` under `Pⁿ`. Replaces the
  `score_eq` field of `ZEstimatorTaylorCore` (which would force the
  bias to be o_P(1)). Concrete consumers identify `bias_n` as
  the model-specific bias term and verify this residual condition. -/
  score_eq_with_bias : ∀ ε > 0, Tendsto
    (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω |
        ε ≤ |(Real.sqrt n)⁻¹ *
              (∑ i : Fin n, score_func_seq n X (X i))
              - bias n X|})
    atTop (𝓝 0)
  /-- vdV §25.8, Theorem 25.59 (prerequisite): the rescaled
  estimator error `√n · (estimator − θ₀)` is bounded in `Pⁿ`-probability
  uniformly in `n` (i.e., `Δ_n = O_P(1)`). Required for the Taylor
  expansion's cross term `Δ_n · D_n` to vanish via `O_P × o_P → o_P`.

  In the bias=0 specialization this was bootstrapped from `score_eq` + Steps
  3, 4 (via `step5_sqrt_n_consistency`); without `score_eq`, the bootstrap
  fails, so it is supplied directly here. -/
  sqrt_n_consistency : ∀ ε > 0, ∃ M : ℝ, ∀ n : ℕ,
    (Measure.pi (fun _ : Fin n => P))
      {X : Fin n → Ω | M ≤ |Real.sqrt n * (estimator n X - θ₀)|}
    ≤ ENNReal.ofReal ε

namespace ZEstimatorBiasResidualExplicitTaylorHyp

variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
variable {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
variable [T_nuis.HasOrthogonalProjection] {v : Θ}
variable {estimator : ∀ n, (Fin n → Ω) → ℝ}
variable {score_func_seq : ∀ n, (Fin n → Ω) → (Ω → ℝ)}
variable {score_truth : Ω → ℝ}
variable {donsker_class : Set (Ω → ℝ)}
variable {score_l_dot : Lp ℝ 2 P}
variable {θ₀ : ℝ}
variable {bias : ∀ n, (Fin n → Ω) → ℝ}

/-- *vdV §25.8, Theorem 25.59 — Z-estimator bias-residual expansion (explicit bias).*

From the bundle `ZEstimatorBiasResidualExplicitTaylorHyp`, the Z-estimator
satisfies the bias-residual asymptotic-linear expansion
$$\sqrt n\,(\hat\theta_n - \theta_0) = \tilde I^{-1}\cdot\frac{1}{\sqrt n}
   \sum_{i=1}^n\tilde\ell(X_i) - \tilde I^{-1}\cdot\mathrm{bias}_n + o_P(1),$$
i.e. `AsymptoticallyLinearWithBiasAt` with bias parameter
`-(1/Ĩ) * bias_n`.

**Relationship to vdV's stated form.** vdV Theorem 25.59 writes the
expansion as
$$\sqrt n\,(\hat\theta_n - \theta) = (1/\sqrt n)\sum \tilde I^{-1}\tilde\ell(X_i)
   + \sqrt n\,P_{\hat\theta_n,\eta}\,\tilde\ell_{\hat\theta_n,\hat\eta_n} + o_P(1).$$
The Lean bias `bias_n` is the analog of vdV's
`√n · P_{θ̂_n,η} ℓ̃`: concrete consumers supply it as their
model-specific bias term. The factor `-(1/Ĩ)` in our AL-with-bias
parameter comes from solving the Taylor-route identity
`Ĩ · Δ_n = S_n − bias_n + o_P(1)` for `Δ_n`. vdV's notation absorbs the
`-Ĩ⁻¹` sign + factor into the bias term via the chain rule on
`∂_θ P_θ ℓ̃|_{θ_0}`; both formulations describe the same residual
algebraically.

**Caveat (truth-P vs P_{θ̂_n,η}).** vdV's bias integrates `ℓ̃_{θ̂_n,η̂_n}`
against the law `P_{θ̂_n, η}` at the estimator's `θ̂_n` (with truth's η).
Our Lean encoding parameterizes the bias as an opaque
`bias : ∀ n, (Fin n → Ω) → ℝ` — the consumer is free to identify it
with `√n · ∫ score_func_seq n X dP` (truth-P integral) or any other
specific form. Under DQM in θ, the two differ by a correction
`∼ Δ_n · ∂_θ P_θ ℓ̃|_{θ_0}` of order `O_P(1)`. The Taylor route's
algebra accommodates either via the `score_eq_with_bias` field, which
imposes the consumer's chosen `bias` definition on the estimating
equation residual.

**Proof outline.** Mirrors Step 6 of the bias=0 discharge, with the
following modifications:
1. The Taylor identity `LHS_n = S_n + Δ_n · (D_n − Ĩ) + R_n` holds
   pointwise (same as before).
2. Rearrange: `Ĩ · Δ_n = S_n + R_n + Δ_n · D_n - LHS_n`, so
   `Ĩ · Δ_n - S_n + bias_n = R_n + Δ_n · D_n - (LHS_n - bias_n)`.
3. By `score_eq_with_bias`: `LHS_n - bias_n →_P 0`.
4. By Step 3 (`Core`-Base): `R_n →_P 0`.
5. By Step 4 (`Core`-Base): `D_n →_P 0`.
6. By `sqrt_n_consistency`: `Δ_n = O_P(1)`, so `Δ_n · D_n →_P 0`.
7. Combine: `Ĩ · Δ_n - S_n + bias_n →_P 0`, i.e.,
   `Δ_n - (1/Ĩ) S_n + (1/Ĩ) bias_n →_P 0`, which is precisely the
   AL-with-bias form with bias parameter `-(1/Ĩ) * bias_n`.

Reference: vdV §25.8, Theorem 25.59. -/
theorem zEstimator_biasResidual_asympLinear_of_taylor_explicit
    (h : ZEstimatorBiasResidualExplicitTaylorHyp P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀ bias) :
    AsymptoticallyLinearWithBiasAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) θ₀
      (fun n X => -(1 / efficientInformation S_θ T_nuis v) * bias n X) := by
  intro ε hε
  set Ĩ : ℝ := efficientInformation S_θ T_nuis v with hĨ_def
  have hĨ_pos : 0 < Ĩ := h.hI_pos
  have hĨ_ne : Ĩ ≠ 0 := ne_of_gt hĨ_pos
  -- Inner key: for any real η > 0, eventually the residual measure ≤ ENNReal.ofReal η.
  have key : ∀ η : ℝ, 0 < η → ∀ᶠ n in atTop,
      (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ |Real.sqrt n * (estimator n X - θ₀)
                - (1 / Ĩ) * ((Real.sqrt n)⁻¹
                  * (∑ i : Fin n, score_truth (X i)))
                - (-(1 / Ĩ) * bias n X)|}
      ≤ ENNReal.ofReal η := by
    intro η hη
    have hη4 : 0 < η / 4 := by linarith
    have hη4_nn : (0 : ℝ) ≤ η / 4 := by linarith
    -- O_P(1) bound on √n(estimator − θ₀) from `sqrt_n_consistency`.
    obtain ⟨M_raw, hM_raw⟩ := h.sqrt_n_consistency (η / 4) hη4
    set M : ℝ := max M_raw 1 with hM_def
    have hM_pos : (0 : ℝ) < M := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hM_ne : M ≠ 0 := ne_of_gt hM_pos
    have hM_bound : ∀ n,
        (Measure.pi (fun _ : Fin n => P))
          {X : Fin n → Ω | M ≤ |Real.sqrt n * (estimator n X - θ₀)|}
        ≤ ENNReal.ofReal (η / 4) := by
      intro n
      refine le_trans (measure_mono ?_) (hM_raw n)
      intro X hX; exact (le_max_left M_raw 1).trans hX
    -- Thresholds for the o_P(1) ingredients.
    have h_τD_pos : (0 : ℝ) < ε * Ĩ / (3 * M) := by positivity
    have h_τR_pos : (0 : ℝ) < ε * Ĩ / 3 := by positivity
    have h_step4_inst := step4_score_dot_lln
      h.toZEstimatorTaylorCoreBase (ε * Ĩ / (3 * M)) h_τD_pos
    have h_step3_inst := step3_taylor_remainder_oP
      h.toZEstimatorTaylorCoreBase (ε * Ĩ / 3) h_τR_pos
    have h_se_inst := h.score_eq_with_bias (ε * Ĩ / 3) h_τR_pos
    rw [ENNReal.tendsto_nhds_zero] at h_step4_inst h_step3_inst h_se_inst
    have h_step4_le := h_step4_inst (ENNReal.ofReal (η / 4)) (by positivity)
    have h_step3_le := h_step3_inst (ENNReal.ofReal (η / 4)) (by positivity)
    have h_se_le := h_se_inst (ENNReal.ofReal (η / 4)) (by positivity)
    -- Combine the three eventually-bounds into a single eventually.
    filter_upwards [h_step4_le, h_step3_le, h_se_le] with n h4 h3 hse
    -- Set inclusion: residual ≥ ε ⇒ at least one of four sets is hit.
    have h_incl :
        {X : Fin n → Ω |
          ε ≤ |Real.sqrt n * (estimator n X - θ₀)
                - (1 / Ĩ) * ((Real.sqrt n)⁻¹
                  * (∑ i : Fin n, score_truth (X i)))
                - (-(1 / Ĩ) * bias n X)|}
        ⊆ ({X : Fin n → Ω |
              M ≤ |Real.sqrt n * (estimator n X - θ₀)|} ∪
            {X : Fin n → Ω |
              ε * Ĩ / (3 * M) ≤ |(n : ℝ)⁻¹ *
                (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i)) + Ĩ|})
          ∪ ({X : Fin n → Ω |
                ε * Ĩ / 3 ≤ |(Real.sqrt n)⁻¹ *
                  (∑ i : Fin n,
                    (score_func_seq n X (X i)
                      - score_truth (X i)
                      - (estimator n X - θ₀)
                        * (score_l_dot : Ω → ℝ) (X i)))|} ∪
              {X : Fin n → Ω |
                ε * Ĩ / 3 ≤ |(Real.sqrt n)⁻¹ *
                  (∑ i : Fin n, score_func_seq n X (X i))
                  - bias n X|}) := by
      intro X hX
      simp only [Set.mem_setOf_eq, Set.mem_union] at hX ⊢
      by_contra hc
      push Not at hc
      obtain ⟨⟨hcΔ, hcD⟩, hcR, hcLHSb⟩ := hc
      -- Abbreviations matching Step 6's identity (with bias).
      set LHS_n : ℝ :=
        (Real.sqrt n)⁻¹ * (∑ i : Fin n, score_func_seq n X (X i)) with hLHS_def
      set S_n : ℝ :=
        (Real.sqrt n)⁻¹ * (∑ i : Fin n, score_truth (X i)) with hS_def
      set R_n : ℝ :=
        (Real.sqrt n)⁻¹ *
          (∑ i : Fin n,
            (score_func_seq n X (X i)
              - score_truth (X i)
              - (estimator n X - θ₀)
                * (score_l_dot : Ω → ℝ) (X i))) with hR_def
      set D_n : ℝ :=
        (n : ℝ)⁻¹ * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i)) + Ĩ with hD_def
      set Δ_n : ℝ := Real.sqrt n * (estimator n X - θ₀) with hΔ_def
      set b_n : ℝ := bias n X with hb_def
      -- n = 0 special case: Δ_0 = S_0 = 0, so |residual| = |bias_0|.
      -- `hcLHSb : |LHS_0 - bias_0| < ε·Ĩ/3`, which with LHS_0 = 0 gives
      -- `|bias_0| < ε·Ĩ/3`. Then |residual| = |(1/Ĩ) bias_0| < ε/3 < ε.
      by_cases hn0 : n = 0
      · subst hn0
        have h_Δ_zero : Δ_n = 0 := by
          simp only [hΔ_def, Nat.cast_zero, Real.sqrt_zero, zero_mul]
        have h_S_zero : S_n = 0 := by
          simp only [hS_def, Nat.cast_zero, Real.sqrt_zero, inv_zero,
            zero_mul]
        have h_LHS_zero : LHS_n = 0 := by
          simp only [hLHS_def, Nat.cast_zero, Real.sqrt_zero, inv_zero,
            zero_mul]
        -- hcLHSb after substitution: |0 - b_n| < ε·Ĩ/3, so |b_n| < ε·Ĩ/3.
        have hb_lt : |b_n| < ε * Ĩ / 3 := by
          have := hcLHSb
          simp only [hLHS_def, hb_def] at this
          rw [show (Real.sqrt (0 : ℕ))⁻¹ *
              (∑ i : Fin 0, score_func_seq 0 X (X i))
              = 0 by simp] at this
          rwa [zero_sub, abs_neg] at this
        have h_abs_neg_inv : |-(1 / Ĩ)| = 1 / Ĩ := by
          rw [abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / Ĩ)]
        rw [h_Δ_zero, h_S_zero, mul_zero, sub_zero, zero_sub, abs_neg,
          abs_mul, h_abs_neg_inv] at hX
        have h_div_lt : (1 / Ĩ) * |b_n| < (1 / Ĩ) * (ε * Ĩ / 3) :=
          mul_lt_mul_of_pos_left hb_lt (by positivity)
        have h_simp : (1 / Ĩ) * (ε * Ĩ / 3) = ε / 3 := by field_simp
        rw [h_simp] at h_div_lt
        linarith
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hnR_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
      have h_sqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR_pos
      have h_sqrt_ne : Real.sqrt n ≠ 0 := ne_of_gt h_sqrt_pos
      have hnR_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR_pos
      -- Algebraic identity LHS_n = S_n + Δ_n · (D_n − Ĩ) + R_n (same as Step 6).
      have h_sum_split : ∀ i : Fin n,
          score_func_seq n X (X i)
            = score_truth (X i)
              + (estimator n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)
              + (score_func_seq n X (X i)
                  - score_truth (X i)
                  - (estimator n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)) := by
        intro i; ring
      have h_sum_eq :
          (∑ i : Fin n, score_func_seq n X (X i))
            = (∑ i : Fin n, score_truth (X i))
              + (estimator n X - θ₀)
                  * (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i))
              + (∑ i : Fin n,
                  (score_func_seq n X (X i)
                    - score_truth (X i)
                    - (estimator n X - θ₀)
                      * (score_l_dot : Ω → ℝ) (X i))) := by
        rw [Finset.mul_sum]
        rw [show (∑ i : Fin n, score_func_seq n X (X i))
            = (∑ i : Fin n,
                (score_truth (X i)
                  + (estimator n X - θ₀) * (score_l_dot : Ω → ℝ) (X i)
                  + (score_func_seq n X (X i)
                      - score_truth (X i)
                      - (estimator n X - θ₀)
                        * (score_l_dot : Ω → ℝ) (X i))))
            from Finset.sum_congr rfl (fun i _ => h_sum_split i)]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have h_identity : LHS_n = S_n + Δ_n * (D_n - Ĩ) + R_n := by
        simp only [hLHS_def, hS_def, hR_def, hD_def, hΔ_def]
        rw [h_sum_eq]
        have h_sqrt_sq : Real.sqrt n * Real.sqrt n = (n : ℝ) :=
          Real.mul_self_sqrt hnR_pos.le
        have h_inv_eq : (Real.sqrt (n : ℝ))⁻¹ = Real.sqrt n * ((n : ℝ)⁻¹) := by
          calc (Real.sqrt (n : ℝ))⁻¹
              = (Real.sqrt n)⁻¹ * 1 := by rw [mul_one]
            _ = (Real.sqrt n)⁻¹ * (Real.sqrt n * Real.sqrt n * (n : ℝ)⁻¹) := by
                rw [h_sqrt_sq, mul_inv_cancel₀ hnR_ne]
            _ = ((Real.sqrt n)⁻¹ * Real.sqrt n) * (Real.sqrt n * (n : ℝ)⁻¹) := by ring
            _ = 1 * (Real.sqrt n * (n : ℝ)⁻¹) := by
                rw [inv_mul_cancel₀ h_sqrt_ne]
            _ = Real.sqrt n * ((n : ℝ)⁻¹) := by rw [one_mul]
        rw [h_inv_eq]
        ring
      -- Target identity: Δ_n − (1/Ĩ)·S_n + (1/Ĩ)·b_n
      --   = (1/Ĩ) · (R_n − (LHS_n − b_n) + Δ_n · D_n)
      have h_target_eq : Δ_n - (1 / Ĩ) * S_n - (-(1 / Ĩ) * b_n)
          = (1 / Ĩ) * (R_n - (LHS_n - b_n) + Δ_n * D_n) := by
        have h := h_identity
        field_simp
        linarith
      -- Strict bounds from the by_contra/push Not.
      have hcD' : |D_n| < ε * Ĩ / (3 * M) := hcD
      have hcR' : |R_n| < ε * Ĩ / 3 := hcR
      have hcLHSb' : |LHS_n - b_n| < ε * Ĩ / 3 := by
        have := hcLHSb
        simp only [hLHS_def, hb_def] at this
        exact this
      have hcΔ' : |Δ_n| < M := hcΔ
      -- Triangle inequality on the rearranged residual.
      have h1Ĩ_nn : 0 ≤ 1 / Ĩ := by positivity
      have h_neg_LHSb : |-(LHS_n - b_n)| = |LHS_n - b_n| := abs_neg _
      have h_split_ΔD : |Δ_n * D_n| = |Δ_n| * |D_n| := abs_mul _ _
      have h_tri : |Δ_n - (1 / Ĩ) * S_n - (-(1 / Ĩ) * b_n)|
          ≤ (1 / Ĩ) * (|R_n| + |LHS_n - b_n| + |Δ_n| * |D_n|) := by
        rw [h_target_eq, abs_mul, abs_of_nonneg h1Ĩ_nn]
        refine mul_le_mul_of_nonneg_left ?_ h1Ĩ_nn
        calc |R_n - (LHS_n - b_n) + Δ_n * D_n|
            = |R_n + (-(LHS_n - b_n)) + Δ_n * D_n| := by ring_nf
          _ ≤ |R_n + (-(LHS_n - b_n))| + |Δ_n * D_n| := abs_add_le _ _
          _ ≤ (|R_n| + |-(LHS_n - b_n)|) + |Δ_n * D_n| := by
              linarith [abs_add_le R_n (-(LHS_n - b_n))]
          _ = |R_n| + |LHS_n - b_n| + |Δ_n| * |D_n| := by
              rw [h_neg_LHSb, h_split_ΔD]
      -- Bound the cross term: |Δ_n| · |D_n| < M · (ε·Ĩ/(3M)) = ε·Ĩ/3.
      have h_prod_lt : |Δ_n| * |D_n| < ε * Ĩ / 3 := by
        have h_step1 : |Δ_n| * |D_n| ≤ M * |D_n| :=
          mul_le_mul_of_nonneg_right hcΔ'.le (abs_nonneg _)
        have h_step2 : M * |D_n| < M * (ε * Ĩ / (3 * M)) :=
          mul_lt_mul_of_pos_left hcD' hM_pos
        have h_step3' : M * (ε * Ĩ / (3 * M)) = ε * Ĩ / 3 := by
          field_simp
        linarith
      -- Sum: < ε·Ĩ.
      have h_sum_lt : |R_n| + |LHS_n - b_n| + |Δ_n| * |D_n| < ε * Ĩ := by linarith
      -- Final residual bound: |Δ_n − S_n/Ĩ − (-bias_n/Ĩ)| < ε.
      have h_target_lt :
          |Δ_n - (1 / Ĩ) * S_n - (-(1 / Ĩ) * b_n)| < ε := by
        calc |Δ_n - (1 / Ĩ) * S_n - (-(1 / Ĩ) * b_n)|
            ≤ (1 / Ĩ) * (|R_n| + |LHS_n - b_n| + |Δ_n| * |D_n|) := h_tri
          _ < (1 / Ĩ) * (ε * Ĩ) :=
              mul_lt_mul_of_pos_left h_sum_lt (by positivity)
          _ = ε := by field_simp
      exact absurd hX (not_le.mpr h_target_lt)
    -- Apply the union bound to the inclusion.
    have h_meas_bd :
        (Measure.pi (fun _ : Fin n => P))
            {X : Fin n → Ω |
              ε ≤ |Real.sqrt n * (estimator n X - θ₀)
                    - (1 / Ĩ) * ((Real.sqrt n)⁻¹
                      * (∑ i : Fin n, score_truth (X i)))
                    - (-(1 / Ĩ) * bias n X)|}
        ≤ ((Measure.pi (fun _ : Fin n => P))
              {X : Fin n → Ω | M ≤ |Real.sqrt n * (estimator n X - θ₀)|}
            + (Measure.pi (fun _ : Fin n => P))
              {X : Fin n → Ω |
                ε * Ĩ / (3 * M) ≤ |(n : ℝ)⁻¹ *
                  (∑ i : Fin n, (score_l_dot : Ω → ℝ) (X i)) + Ĩ|})
          + ((Measure.pi (fun _ : Fin n => P))
              {X : Fin n → Ω |
                ε * Ĩ / 3 ≤ |(Real.sqrt n)⁻¹ *
                  (∑ i : Fin n,
                    (score_func_seq n X (X i)
                      - score_truth (X i)
                      - (estimator n X - θ₀)
                        * (score_l_dot : Ω → ℝ) (X i)))|}
            + (Measure.pi (fun _ : Fin n => P))
              {X : Fin n → Ω |
                ε * Ĩ / 3 ≤ |(Real.sqrt n)⁻¹ * (∑ i : Fin n,
                  score_func_seq n X (X i)) - bias n X|}) := by
      refine le_trans (measure_mono h_incl) ?_
      refine le_trans (measure_union_le _ _) ?_
      exact add_le_add (measure_union_le _ _) (measure_union_le _ _)
    have h_M_le : (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω | M ≤ |Real.sqrt n * (estimator n X - θ₀)|}
        ≤ ENNReal.ofReal (η / 4) := hM_bound n
    have h_sum_eps : ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4)
                      + (ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4))
                    = ENNReal.ofReal η := by
      have h1 : ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4)
                  = ENNReal.ofReal (η / 4 + η / 4) :=
        (ENNReal.ofReal_add hη4_nn hη4_nn).symm
      rw [h1]
      rw [(ENNReal.ofReal_add (by linarith : (0:ℝ) ≤ η/4 + η/4)
            (by linarith : (0:ℝ) ≤ η/4 + η/4)).symm]
      congr 1; ring
    refine le_trans h_meas_bd ?_
    refine le_trans (add_le_add (add_le_add h_M_le h4) (add_le_add h3 hse)) ?_
    exact h_sum_eps.le
  -- Conclude the Tendsto from the real-`η` key, casing on c = ⊤.
  have hTrTendsto : Tendsto
      (fun n : ℕ => (Measure.pi (fun _ : Fin n => P))
        {X : Fin n → Ω |
          ε ≤ |Real.sqrt n * (estimator n X - θ₀)
                - (1 / Ĩ) * ((Real.sqrt n)⁻¹
                  * (∑ i : Fin n, score_truth (X i)))
                - (-(1 / Ĩ) * bias n X)|})
      atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro c hc
    by_cases hc_inf : c = ⊤
    · exact Filter.Eventually.of_forall fun _ => hc_inf ▸ le_top
    · have hc_real_pos : 0 < ENNReal.toReal c :=
        ENNReal.toReal_pos hc.ne' hc_inf
      filter_upwards [key (ENNReal.toReal c) hc_real_pos] with n hn
      exact hn.trans (ENNReal.ofReal_toReal hc_inf).le
  -- Bridge to AL-with-bias form's set via Lp/smul shuffle on Pⁿ-a.e. equality.
  -- Pattern matches `zEstimator_asympLinear_of_taylor`'s main-thm assembly.
  set effScoreLp : Lp ℝ 2 P :=
    ((efficientScore S_θ T_nuis v : ↥(L2ZeroMean P)) : Lp ℝ 2 P) with h_eff_def
  have h_eq_P :
      (fun ω => ((((1 / Ĩ) • effScoreLp) : Lp ℝ 2 P) : Ω → ℝ) ω)
        =ᵐ[P] fun ω => (1 / Ĩ) * score_truth ω := by
    have h_truth_aeEq : (effScoreLp : Ω → ℝ) =ᵐ[P] score_truth := h.truth_aeEq
    filter_upwards [Lp.coeFn_smul ((1 / Ĩ) : ℝ) effScoreLp, h_truth_aeEq]
      with ω h_smul h_truth
    rw [h_smul]
    change (1 / Ĩ) * _ = _
    rw [h_truth]
  refine hTrTendsto.congr (fun n => ?_)
  refine MeasureTheory.measure_congr ?_
  have h_eq_Pi : ∀ (i : Fin n),
      (fun X : Fin n → Ω =>
          ((((1 / Ĩ) • effScoreLp) : Lp ℝ 2 P) : Ω → ℝ) (X i))
        =ᵐ[Measure.pi (fun _ : Fin n => P)]
          fun X => (1 / Ĩ) * score_truth (X i) := by
    intro i
    have h_mp :
        MeasureTheory.MeasurePreserving (Function.eval i)
          (Measure.pi (fun _ : Fin n => P)) P :=
      MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => P) i
    exact h_eq_P.comp_tendsto h_mp.quasiMeasurePreserving.tendsto_ae
  have h_eq_sum : ∀ᵐ X ∂(Measure.pi (fun _ : Fin n => P)),
      ∀ (i : Fin n),
        ((((1 / Ĩ) • effScoreLp) : Lp ℝ 2 P) : Ω → ℝ) (X i)
        = (1 / Ĩ) * score_truth (X i) := by
    rw [ae_all_iff]
    exact h_eq_Pi
  filter_upwards [h_eq_sum] with X h_X
  have h_sum_eq :
      (∑ i : Fin n,
          ((((1 / efficientInformation S_θ T_nuis v) • efficientScore S_θ T_nuis v
              : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) (X i))
        = (1 / Ĩ) * (∑ i : Fin n, score_truth (X i)) := by
    change (∑ i : Fin n, ((((1 / Ĩ) • effScoreLp) : Lp ℝ 2 P) : Ω → ℝ) (X i)) = _
    rw [Finset.sum_congr rfl (fun i _ => h_X i), ← Finset.mul_sum]
  have h_inner_eq :
      Real.sqrt ↑n * (estimator n X - θ₀)
          - 1 / efficientInformation S_θ T_nuis v
            * ((Real.sqrt ↑n)⁻¹ * (∑ i : Fin n, score_truth (X i)))
          - (-(1 / Ĩ) * bias n X)
        = Real.sqrt ↑n * (estimator n X - θ₀)
          - (Real.sqrt ↑n)⁻¹
            * (∑ i : Fin n,
                ((((1 / efficientInformation S_θ T_nuis v) • efficientScore S_θ T_nuis v
                    : ↥(L2ZeroMean P)) : Lp ℝ 2 P) : Ω → ℝ) (X i))
          - (-(1 / efficientInformation S_θ T_nuis v) * bias n X) := by
    rw [h_sum_eq, show (1 : ℝ) / efficientInformation S_θ T_nuis v = 1 / Ĩ from rfl]
    ring
  exact congrArg (fun x : ℝ => ε ≤ |x|) h_inner_eq

/-- **Explicit-bias Taylor assumptions as a bias-residual bundle.**

Constructs `EfficientScoreEqBiasResidualAssumptions` from
`ZEstimatorBiasResidualExplicitTaylorHyp` and the EIF-construction inputs `h_mem` and
`h_dψ`, with residual
`(fun n X => -(1 / efficientInformation S_θ T_nuis v) * bias n X)`. Positivity of the
efficient information is inherited from `h.hI_pos`, and `asympLinear_25_59` is supplied
by `zEstimator_biasResidual_asympLinear_of_taylor_explicit`.

Reference: vdV §25.8, Theorem 25.59. -/
def toEfficientScoreEqBiasResidualAssumptions_explicit
    {T : Submodule ℝ ↥(L2ZeroMean P)} {dψ : T →L[ℝ] ℝ}
    (h : ZEstimatorBiasResidualExplicitTaylorHyp P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀ bias)
    (h_mem :
      (1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v ∈ T)
    (h_dψ : ∀ g : T,
      dψ g
        = (1 / efficientInformation S_θ T_nuis v)
            * ⟪efficientScore S_θ T_nuis v, (g : ↥(L2ZeroMean P))⟫_ℝ) :
    EfficientScoreEqBiasResidualAssumptions P Θ S_θ T_nuis v T dψ
      estimator
      (fun n X => -(1 / efficientInformation S_θ T_nuis v) * bias n X) θ₀ where
  h_mem := h_mem
  h_dψ := h_dψ
  hI_pos := h.hI_pos
  asympLinear_25_59 :=
    zEstimator_biasResidual_asympLinear_of_taylor_explicit h

end ZEstimatorBiasResidualExplicitTaylorHyp

end AsymptoticStatistics.Asymptotics.Discharge.ZEstimator
