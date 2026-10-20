module
public import StatLean.AsymptoticStatistics.MEstimator.ArgmaxLocalization
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ZEstimatorNormality
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LinearizationEquicontinuity

@[expose] public section

/-!
# M-estimator asymptotic normality (vdV Theorem 5.23)

Assembly layer (T8). An M-estimator `θ̂ₙ` is a near-maximizer of the empirical
criterion `θ ↦ ℙₙm_θ`; vdV 5.23 gives, under a Lipschitz condition on `θ ↦ m_θ`, a
second-order Taylor expansion of the population criterion `θ ↦ Pm_θ` at a maximum `θ₀`
with nonsingular symmetric negative-definite `V`, and `θ̂ₙ →ₚ θ₀`,

    √n(θ̂ₙ − θ₀) = −V⁻¹ 𝔾ₙṁ_{θ₀} + o_P(1),   hence
    √n(θ̂ₙ − θ₀) ⇝ N(0, V⁻¹ P[ṁ_{θ₀}ṁ_{θ₀}ᵀ] V⁻¹).

The distinctive step versus the Z-estimator (vdV 5.21) is the argmax complete-the-
square localization `argmax_localization` (`MEstimator/ArgmaxLocalization.lean`); the
CLT / covariance / normality glue is shared with T6
(`EmpiricalProcess/ZEstimatorNormality.lean`): we reuse `empiricalProcessVec`,
`psiCov`, `empiricalProcessVec_weakConverges` with `ψ := fun _ => mdot` (`ṁ_{θ₀}` is
`θ`-independent for the CLT of the score at `θ₀`).

## Main results

* `mEstimator_quadratic_expansion` combines the empirical increment split,
  the population Taylor expansion, and stochastic equicontinuity.
* `mEstimator_linear_representation` derives the linear expansion through
  `argmax_localization`.
* `mEstimator_normality_of_expansion` combines the linear expansion with the CLT.
* `m_estimator_normality` is stated in `MEstimator/AsymptoticNormality.lean` to avoid
  an import cycle with the rate theorem.
-/

namespace AsymptoticStatistics.MEstimator

open MeasureTheory Filter ProbabilityTheory EmpiricalProcess
open scoped ENNReal Topology RealInnerProductSpace Matrix ProbabilityTheory

/-! ### B1 — empirical-process quadratic expansion -/

/-- **B1 sub-lemma (a): empirical increment split.**

`n·ℙₙf = n·Pf + √n·𝔾ₙf`, i.e. the empirical average scaled by `n` splits into the
`n`-scaled population integral plus the `√n`-scaled empirical process. Immediate from
`empiricalProcess P n Xs f = √n·(ℙₙf − Pf)` and `√n·√n = n`. This is the algebraic
skeleton of `mEstimator_quadratic_expansion`. -/
theorem empiricalIncrement_split {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (n : ℕ) (Xs : Fin n → Ω) (f : Ω → ℝ) :
    (n : ℝ) * empiricalAvg f n Xs
      = (n : ℝ) * (∫ x, f x ∂P) + Real.sqrt n * empiricalProcess P n Xs f := by
  unfold empiricalProcess
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg n)
  rw [← mul_assoc, hsq]
  ring

/-- **B1 sub-lemma (b): population Taylor at the local scale.**

For a bounded-in-probability random direction `hₙ`, the `n`-scaled population increment
along `θ = θ₀ + hₙ/√n` collapses to the leading quadratic:

    n·P(m_{θ₀+hₙ/√n} − m_{θ₀}) − ½⟪hₙ, V hₙ⟫ →ₚ 0.

Book route (vdV 5.23 proof step 1): the second-order population Taylor expansion
`P(m_θ − m_{θ₀}) = ½⟪θ−θ₀, V(θ−θ₀)⟫ + o(‖θ−θ₀‖²)` (`hTaylor`, on the difference
integral `∫(m_θ − m_{θ₀})`) evaluated at `θ−θ₀ = hₙ/√n` gives
`n·[½·(1/n)⟪hₙ,Vhₙ⟫] = ½⟪hₙ,Vhₙ⟫` for the quadratic part (exact
cancellation via `√n·√n = n`), and the
remainder `n·o(‖hₙ/√n‖²) = o_P(1)·‖hₙ‖²` vanishes in probability because `hₙ = O_P(1)`
and `‖hₙ/√n‖ = ‖hₙ‖/√n →ₚ 0`.

The ε-δ argument extracts `‖θ−θ₀‖ < ρ' ⟹ |remainder| ≤ ε'‖θ−θ₀‖²` from `hTaylor`
(`Asymptotics.isLittleO_iff` + `Metric.eventually_nhds_iff`); choosing `ε' = δ/(M+1)²` at the
`O_P(1)` threshold `M` and `N` with `M < ρ'√n` (via `√n → ∞`) contains the exceedance event
`{δ ≤ ‖·‖}` inside `{M < ‖hₙ‖}`, whose mass is `≤ η/4 < η`. -/
theorem populationTaylor_at_localScale
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (V : Matrix (Fin d) (Fin d) ℝ)
    (hTaylor : Asymptotics.IsLittleO (𝓝 θ₀)
      (fun θ => (∫ x, (m θ x - m θ₀ x) ∂P)
        - (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (θ - θ₀)⟫)
      (fun θ => ‖θ - θ₀‖ ^ 2))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (hₙ : ℕ → Ξ → EuclideanSpace ℝ (Fin d))
    (hₙ_meas : ∀ n, Measurable (hₙ n))
    (hₙ_bdd : IsBoundedInProb (fun _ : ℕ => μ) hₙ) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      (n : ℝ) * (∫ x, (m (θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ) x - m θ₀ x) ∂P)
        - (1 / 2) * ⟪hₙ n ξ, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (hₙ n ξ)⟫) := by
  set Vc := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V with hVcdef
  intro δ hδ
  rw [Metric.tendsto_atTop]
  intro η hη
  -- `O_P(1)` threshold for `hₙ` at level `η/4`.
  obtain ⟨M, hM⟩ := hₙ_bdd (η / 4) (by positivity)
  have hMp0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  have hMp1 : (0 : ℝ) < max M 0 + 1 := by positivity
  -- `ε'` for the localized Taylor remainder bound; `√(δ/ε') = max M 0 + 1 > max M 0`.
  have hε'pos : (0 : ℝ) < δ / (max M 0 + 1) ^ 2 := by positivity
  have hLO := (Asymptotics.isLittleO_iff.mp hTaylor) hε'pos
  rw [Metric.eventually_nhds_iff] at hLO
  obtain ⟨ρ', hρ', hb⟩ := hLO
  -- Pick `N` with `max M 0 < ρ'·√n` and `1 ≤ n` (uses `√n → ∞`).
  have hsqrt_tendsto : Tendsto (fun n : ℕ => ρ' * Real.sqrt n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hρ'
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hev : ∀ᶠ n : ℕ in atTop, max M 0 < ρ' * Real.sqrt n ∧ 1 ≤ n :=
    (hsqrt_tendsto.eventually_gt_atTop (max M 0)).and (eventually_ge_atTop 1)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨hNn, hn1⟩ := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  -- The exceedance set sits inside `{max M 0-tail of hₙ}`; the mass is `≤ η/4 < η`.
  refine lt_of_le_of_lt (le_trans (measureReal_mono ?_) (hM n)) (by linarith)
  intro ξ hξ
  simp only [Set.mem_setOf_eq] at hξ ⊢
  by_contra hcon
  push_neg at hcon
  -- `hcon : ‖hₙ n ξ‖ ≤ M`.
  set θ := θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ with hθdef
  have hnn : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn1)
  have hsqrtpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
  have hsqrtne : Real.sqrt n ≠ 0 := ne_of_gt hsqrtpos
  have hθsubeq : θ - θ₀ = (Real.sqrt n)⁻¹ • hₙ n ξ := by rw [hθdef, add_sub_cancel_left]
  -- `Z n ξ = n · R θ` where `R θ` is the Taylor remainder (quadratic cancels).
  have hquad : (n : ℝ) * ((1 / 2) * ⟪θ - θ₀, Vc (θ - θ₀)⟫)
      = (1 / 2) * ⟪hₙ n ξ, Vc (hₙ n ξ)⟫ := by
    rw [hθsubeq, map_smul, real_inner_smul_left, real_inner_smul_right,
      show (Real.sqrt n)⁻¹ * ((Real.sqrt n)⁻¹ * ⟪hₙ n ξ, Vc (hₙ n ξ)⟫)
          = ((Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹) * ⟪hₙ n ξ, Vc (hₙ n ξ)⟫ from by ring,
      ← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg n),
      show (n : ℝ) * ((1 / 2) * ((n : ℝ)⁻¹ * ⟪hₙ n ξ, Vc (hₙ n ξ)⟫))
          = ((n : ℝ) * (n : ℝ)⁻¹) * ((1 / 2) * ⟪hₙ n ξ, Vc (hₙ n ξ)⟫) from by ring,
      mul_inv_cancel₀ hnn, one_mul]
  have hZeq : (n : ℝ) * (∫ x, (m θ x - m θ₀ x) ∂P)
        - (1 / 2) * ⟪hₙ n ξ, Vc (hₙ n ξ)⟫
      = (n : ℝ) * ((∫ x, (m θ x - m θ₀ x) ∂P)
          - (1 / 2) * ⟪θ - θ₀, Vc (θ - θ₀)⟫) := by
    linear_combination hquad
  -- `‖θ - θ₀‖ = ‖hₙ‖/√n < ρ'`, so the localized bound applies.
  have hnorm_eq : ‖θ - θ₀‖ = (Real.sqrt n)⁻¹ * ‖hₙ n ξ‖ := by
    rw [hθsubeq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.sqrt n)⁻¹)]
  have hθlt : ‖θ - θ₀‖ < ρ' := by
    rw [hnorm_eq]
    have hhlt : ‖hₙ n ξ‖ < ρ' * Real.sqrt n :=
      lt_of_le_of_lt (le_trans hcon (le_max_left M 0)) hNn
    calc (Real.sqrt n)⁻¹ * ‖hₙ n ξ‖
        < (Real.sqrt n)⁻¹ * (ρ' * Real.sqrt n) :=
          mul_lt_mul_of_pos_left hhlt (by positivity)
      _ = ρ' := by rw [mul_comm ρ', ← mul_assoc, inv_mul_cancel₀ hsqrtne, one_mul]
  have hRle : |(∫ x, (m θ x - m θ₀ x) ∂P) - (1 / 2) * ⟪θ - θ₀, Vc (θ - θ₀)⟫|
      ≤ (δ / (max M 0 + 1) ^ 2) * ‖θ - θ₀‖ ^ 2 := by
    have hbb := @hb θ (by rw [dist_eq_norm]; exact hθlt)
    simp only [Real.norm_eq_abs] at hbb
    rwa [abs_of_nonneg (sq_nonneg ‖θ - θ₀‖)] at hbb
  have hZval : ‖(n : ℝ) * (∫ x, (m θ x - m θ₀ x) ∂P)
        - (1 / 2) * ⟪hₙ n ξ, Vc (hₙ n ξ)⟫‖
      = (n : ℝ) * |(∫ x, (m θ x - m θ₀ x) ∂P)
          - (1 / 2) * ⟪θ - θ₀, Vc (θ - θ₀)⟫| := by
    rw [hZeq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  have hθsq : ‖θ - θ₀‖ ^ 2 = (n : ℝ)⁻¹ * ‖hₙ n ξ‖ ^ 2 := by
    rw [hnorm_eq, mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  -- `‖Z‖ ≤ ε'·‖hₙ‖²`.
  have key1 : ‖(n : ℝ) * (∫ x, (m θ x - m θ₀ x) ∂P)
        - (1 / 2) * ⟪hₙ n ξ, Vc (hₙ n ξ)⟫‖
      ≤ (δ / (max M 0 + 1) ^ 2) * ‖hₙ n ξ‖ ^ 2 := by
    rw [hZval]
    have h1 := mul_le_mul_of_nonneg_left hRle (Nat.cast_nonneg n)
    rw [hθsq] at h1
    refine le_trans h1 (le_of_eq ?_)
    rw [show (n : ℝ) * ((δ / (max M 0 + 1) ^ 2) * ((n : ℝ)⁻¹ * ‖hₙ n ξ‖ ^ 2))
          = ((n : ℝ) * (n : ℝ)⁻¹) * ((δ / (max M 0 + 1) ^ 2) * ‖hₙ n ξ‖ ^ 2) from by ring,
      mul_inv_cancel₀ hnn, one_mul]
  -- `ε'·‖hₙ‖² < δ`.
  have hh2 : ‖hₙ n ξ‖ ^ 2 ≤ (max M 0) ^ 2 := by
    have hle : ‖hₙ n ξ‖ ≤ max M 0 := le_trans hcon (le_max_left M 0)
    nlinarith [norm_nonneg (hₙ n ξ), hMp0, hle]
  have key2 : (δ / (max M 0 + 1) ^ 2) * ‖hₙ n ξ‖ ^ 2 < δ := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left hh2 (le_of_lt hε'pos)) ?_
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity : (0 : ℝ) < (max M 0 + 1) ^ 2)]
    nlinarith [hMp0, hδ]
  linarith [hξ, key1, key2]

/-- **B1: M-estimator quadratic expansion** (vdV 5.23 proof steps 1+3, book p.53–54).

For a bounded-in-probability random direction `hₙ`, the empirical criterion increment
along the local reparametrization `θ = θ₀ + hₙ/√n` expands as

    n·ℙₙ(m_{θ₀+hₙ/√n} − m_{θ₀}) = ½⟪hₙ, V hₙ⟫ + ⟪hₙ, 𝔾ₙṁ_{θ₀}⟫ + o_P(1).

Assembly of the three pieces:
* (a) `empiricalIncrement_split`: `n·ℙₙ(incr) = n·P(incr) + √n·𝔾ₙ(incr)`;
* (b) `populationTaylor_at_localScale`: `n·P(incr) − ½⟪hₙ,Vhₙ⟫ →ₚ 0` (population Taylor);
* (c) `mEstimator_linearization_equicontinuity` (C3, vdV Lem 19.31):
  `𝔾ₙ(√n·incr) − ⟪hₙ, 𝔾ₙṁ⟫ →ₚ 0`, with `𝔾ₙ(√n·incr) = √n·𝔾ₙ(incr)`
  (`empiricalProcess_smul`).

`o_P`-additivity (`TendstoInProbZero.add`) then closes it. The proof uses the proved
theorems `populationTaylor_at_localScale` and
`mEstimator_linearization_equicontinuity`. Its two applications are
`hₙ = √n(θ̂−θ₀)` and `hₙ = −V⁻¹𝔾ₙṁ`. -/
theorem mEstimator_quadratic_expansion
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (mdot : Fin d → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (V : Matrix (Fin d) (Fin d) ℝ)
    (hm_meas : ∀ θ, Measurable (m θ)) (hmdot_meas : ∀ i, Measurable (mdot i))
    (hmdot_L2 : ∀ i, MemLp (mdot i) 2 P)
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P) (hmenv_meas : Measurable menv)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    (hderiv : ∀ᵐ ω ∂P, HasFDerivAt (fun θ => m θ ω)
      (innerSL ℝ (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)) θ₀)
    (hTaylor : Asymptotics.IsLittleO (𝓝 θ₀)
      (fun θ => (∫ x, (m θ x - m θ₀ x) ∂P)
        - (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (θ - θ₀)⟫)
      (fun θ => ‖θ - θ₀‖ ^ 2))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (hₙ : ℕ → Ξ → EuclideanSpace ℝ (Fin d))
    (hₙ_meas : ∀ n, Measurable (hₙ n))
    (hₙ_bdd : IsBoundedInProb (fun _ : ℕ => μ) hₙ) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      (n : ℝ) * empiricalAvg
          (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ) ω - m θ₀ ω) n (fun i : Fin n => X i.val ξ)
        - ((1 / 2) * ⟪hₙ n ξ, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (hₙ n ξ)⟫
            + ⟪hₙ n ξ, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                (fun i : Fin n => X i.val ξ)⟫)) := by
  -- (b) population Taylor half.
  have hb := populationTaylor_at_localScale P m θ₀ V hTaylor μ hₙ hₙ_meas hₙ_bdd
  -- (c) empirical-process equicontinuity half (vdV Lem 19.31).
  have hc := mEstimator_linearization_equicontinuity P m mdot θ₀ hm_meas hmdot_meas hmdot_L2
    menv hmenv ρ hρ hLip hderiv μ X hX_meas hX_indep hX_id hX_law hmenv_meas hₙ hₙ_meas hₙ_bdd
  -- (a) split + `empiricalProcess_smul`: the goal function equals (b) + (c) pointwise.
  have hfun : (fun (n : ℕ) (ξ : Ξ) =>
        (n : ℝ) * empiricalAvg
            (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ) ω - m θ₀ ω) n (fun i : Fin n => X i.val ξ)
          - ((1 / 2) * ⟪hₙ n ξ, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (hₙ n ξ)⟫
              + ⟪hₙ n ξ, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                  (fun i : Fin n => X i.val ξ)⟫))
      = (fun (n : ℕ) (ξ : Ξ) =>
          ((n : ℝ) * (∫ x, (m (θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ) x - m θ₀ x) ∂P)
              - (1 / 2) * ⟪hₙ n ξ, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (hₙ n ξ)⟫)
            + (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ) ω - m θ₀ ω))
                - ⟪hₙ n ξ, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                    (fun i : Fin n => X i.val ξ)⟫)) := by
    funext n ξ
    rw [empiricalIncrement_split P n (fun i : Fin n => X i.val ξ)
        (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ) ω - m θ₀ ω),
      empiricalProcess_smul P n (fun i : Fin n => X i.val ξ) (Real.sqrt n)
        (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ) ω - m θ₀ ω)]
    ring
  rw [hfun]
  exact TendstoInProbZero.add hb hc

/-- **B1 fixed-direction `L²` adapter** for the probability-differentiability route.

This has the same data and conclusion as `mEstimator_quadratic_expansion`, but replaces
the pointwise-a.e. Fréchet derivative by exactly the fixed-direction `distL2` convergence
consumed by `mEstimator_linearization_equicontinuity_of_distL2`.  It is the B1 interface
used by the vdV 5.39 assembly; no derivative-compatibility equality is introduced. -/
theorem mEstimator_quadratic_expansion_of_distL2
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ) (mdot : Fin d → (Ω → ℝ))
    (θ₀ : EuclideanSpace ℝ (Fin d)) (V : Matrix (Fin d) (Fin d) ℝ)
    -- Measurable criterion sections, as in vdV 5.23/5.39.
    (hm_meas : ∀ θ, Measurable (m θ))
    -- Measurable score coordinates for the empirical-process term.
    (hmdot_meas : ∀ i, Measurable (mdot i))
    -- Coordinatewise score `L²`, which follows from the 5.39 assumptions.
    (hmdot_L2 : ∀ i, MemLp (mdot i) 2 P)
    (menv : Ω → ℝ)
    -- vdV's common local Lipschitz envelope belongs to `L²(P)`.
    (hmenv : MemLp menv 2 P)
    -- Measurability of the empirical-process envelope.
    (hmenv_meas : Measurable menv)
    (ρ : ℝ)
    -- Positive radius of the local Lipschitz neighborhood.
    (hρ : 0 < ρ)
    -- vdV's local Lipschitz domination.
    (hLip : ∀ θ₁ ∈ Metric.closedBall θ₀ ρ, ∀ θ₂ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
              |m θ₁ ω - m θ₂ ω| ≤ menv ω * ‖θ₁ - θ₂‖)
    -- Fixed-direction `L²` linearization, derived from
    -- differentiability in probability plus the common envelope in the 5.39 route.
    (hd : ∀ h : EuclideanSpace ℝ (Fin d), Tendsto (fun n : ℕ => distL2 P
      (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
      (fun ω => ⟪h, psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
      atTop (𝓝 0))
    -- Second-order population Taylor expansion at `θ₀`.
    (hTaylor : Asymptotics.IsLittleO (𝓝 θ₀)
      (fun θ => (∫ x, (m θ x - m θ₀ x) ∂P)
        - (1 / 2) * ⟪θ - θ₀, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (θ - θ₀)⟫)
      (fun θ => ‖θ - θ₀‖ ^ 2))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    -- Measurable sample-map encoding of the iid experiment.
    (hX_meas : ∀ i, Measurable (X i))
    -- Independence component of the iid sample encoding.
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    -- Identical-distribution component of the iid sample encoding.
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    -- Identifies the common sample law with `P`.
    (hX_law : μ.map (X 0) = P)
    (hₙ : ℕ → Ξ → EuclideanSpace ℝ (Fin d))
    -- Measurability of the random local direction.
    (hₙ_meas : ∀ n, Measurable (hₙ n))
    -- The local direction is bounded in probability.
    (hₙ_bdd : IsBoundedInProb (fun _ : ℕ => μ) hₙ) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      (n : ℝ) * empiricalAvg
          (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ) ω - m θ₀ ω) n
            (fun i : Fin n => X i.val ξ)
        - ((1 / 2) * ⟪hₙ n ξ, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (hₙ n ξ)⟫
            + ⟪hₙ n ξ, empiricalProcessVec P (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                (fun i : Fin n => X i.val ξ)⟫)) := by
  have hb := populationTaylor_at_localScale P m θ₀ V hTaylor μ hₙ hₙ_meas hₙ_bdd
  have hc := mEstimator_linearization_equicontinuity_of_distL2 P m mdot θ₀ hm_meas
    hmdot_meas hmdot_L2 menv hmenv ρ hρ hLip hd μ X hX_meas hX_indep hX_id hX_law
    hmenv_meas hₙ hₙ_meas hₙ_bdd
  have hfun : (fun (n : ℕ) (ξ : Ξ) =>
        (n : ℝ) * empiricalAvg
            (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ) ω - m θ₀ ω) n
              (fun i : Fin n => X i.val ξ)
          - ((1 / 2) * ⟪hₙ n ξ, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (hₙ n ξ)⟫
              + ⟪hₙ n ξ, empiricalProcessVec P
                  (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                  (fun i : Fin n => X i.val ξ)⟫))
      = (fun (n : ℕ) (ξ : Ξ) =>
          ((n : ℝ) * (∫ x, (m (θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ) x - m θ₀ x) ∂P)
              - (1 / 2) * ⟪hₙ n ξ, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V (hₙ n ξ)⟫)
            + (empiricalProcess P n (fun i : Fin n => X i.val ξ)
                  (fun ω => Real.sqrt n * (m (θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ) ω - m θ₀ ω))
                - ⟪hₙ n ξ, empiricalProcessVec P
                    (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ n
                    (fun i : Fin n => X i.val ξ)⟫)) := by
    funext n ξ
    rw [empiricalIncrement_split P n (fun i : Fin n => X i.val ξ)
        (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ) ω - m θ₀ ω),
      empiricalProcess_smul P n (fun i : Fin n => X i.val ξ) (Real.sqrt n)
        (fun ω => m (θ₀ + (Real.sqrt n)⁻¹ • hₙ n ξ) ω - m θ₀ ω)]
    ring
  rw [hfun]
  exact TendstoInProbZero.add hb hc

/-! ### B2 — linear representation (Level A) via the argmax core. -/

/-- **B2: linear representation of the M-estimator.**

Under the two quadratic expansions (`hExpA` at `hₙ = √n(θ̂−θ₀)`, `hExpB` at the
comparison point) and near-maximization (`hNearMax`), with `V` symmetric, nonsingular,
uniformly negative definite,

    √n(θ̂ₙ − θ₀) + V⁻¹ 𝔾ₙṁ_{θ₀} →ₚ 0.

Direct application of `argmax_localization` to the concrete objects
`h := √n(θ̂−θ₀)` and `G := empiricalProcessVec P (fun _=>mdot) θ₀`. Same conclusion
TYPE as T6 `zEstimator_linear_representation`. -/
theorem mEstimator_linear_representation
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (mdot : Fin d → (Ω → ℝ)) (θ₀ : EuclideanSpace ℝ (Fin d))
    (V : Matrix (Fin d) (Fin d) ℝ)
    (hVunit : IsUnit V.det) (hVsymm : V.IsHermitian)
    {c : ℝ} (hc : 0 < c)
    (hVneg : ∀ x : EuclideanSpace ℝ (Fin d),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ ≤ - c * ‖x‖ ^ 2)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω)
    (A B : ℕ → Ξ → ℝ)
    (hExpA : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => A n ξ
      - ((1 / 2) * ⟪Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀),
            Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V
              (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))⟫
          + ⟪Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀),
              empiricalProcessVec P (fun _ => mdot) θ₀ n
                (fun i : Fin n => X i.val ξ)⟫)))
    (hExpB : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => B n ξ
      - (- (1 / 2) * ⟪empiricalProcessVec P (fun _ => mdot) θ₀ n
              (fun i : Fin n => X i.val ξ),
            Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
              (empiricalProcessVec P (fun _ => mdot) θ₀ n
                (fun i : Fin n => X i.val ξ))⟫)))
    (hNearMax : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => max 0 (B n ξ - A n ξ))) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
        + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
            (empiricalProcessVec P (fun _ => mdot) θ₀ n
              (fun i : Fin n => X i.val ξ))) :=
  argmax_localization (P := fun _ : ℕ => μ) V hVunit hVsymm hc hVneg
    (fun n ξ => Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
    (fun n ξ => empiricalProcessVec P (fun _ => mdot) θ₀ n
      (fun i : Fin n => X i.val ξ))
    A B hExpA hExpB hNearMax

/-! ### B3 — asymptotic normality from a quadratic expansion -/

/-- **B3: asymptotic normality from an assumed quadratic expansion and near-maximization.**

This declaration certifies the Gaussian limit given the quadratic expansion and
near-maximization as hypotheses over free
`A, B : ℕ → Ξ → ℝ`; the criterion `m` and the Lipschitz condition do not appear, and
`hExpA`/`hExpB` are facts vdV *derives* (Lem 19.31 + Taylor), here assumed. It is the
CLT⇒normality implication used by the vdV 5.23 theorem, whose hypotheses concern the
actual criterion, Lipschitz envelope, Taylor expansion, near-maximality, and consistency.

Given the assumed expansion at the two local directions (`hExpA`/`hExpB`), near-max
(`hNearMax`), symmetric nonsingular negative-definite `V`, `P‖ṁ_{θ₀}‖² < ∞`
(`hψ_L2`), and first-order condition `Pṁ_{θ₀} = 0` (`hPmdot_zero`, itself derivable):

    √n(θ̂ₙ − θ₀) ⇝ N(0, V⁻¹ P[ṁ_{θ₀}ṁ_{θ₀}ᵀ] (V⁻¹)ᵀ)   (conclusion IS vdV-exact).

Assembly: `mEstimator_linear_representation` (B2, via the argmax core) gives
`√n(θ̂−θ₀) = −V⁻¹𝔾ₙṁ + o_P(1)`; `empiricalProcessVec_weakConverges`
gives `𝔾ₙṁ ⇝ N(0, psiCov)`; CMT by `−V⁻¹` (`multivariateGaussian_map_toEuclideanCLM`,
`(−A)Σ(−A)ᵀ = AΣAᵀ`) plus the random-shift Slutsky
`WeakConverges.slutsky_of_tendstoInMeasure_dist` transport the limit. This glue is
the same linear-representation-to-Gaussian-limit argument used by
`zEstimator_asymptotic_normality`. -/
theorem mEstimator_normality_of_expansion
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (mdot : Fin d → (Ω → ℝ)) (θ₀ : EuclideanSpace ℝ (Fin d))
    (V : Matrix (Fin d) (Fin d) ℝ)
    (hVunit : IsUnit V.det) (hVsymm : V.IsHermitian)
    {c : ℝ} (hc : 0 < c)
    (hVneg : ∀ x : EuclideanSpace ℝ (Fin d),
      ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V x⟫ ≤ - c * ‖x‖ ^ 2)
    (hmdot_meas : ∀ i, Measurable (mdot i))
    (hψ_L2 : MemLp (psiVec (fun _ => mdot) θ₀) 2 P)
    (hPmdot_zero : ∀ i, ∫ x, mdot i x ∂P = 0)
    (θ_hat : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : ProbabilityTheory.iIndepFun X μ)
    (hX_id : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (A B : ℕ → Ξ → ℝ)
    (hExpA : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => A n ξ
      - ((1 / 2) * ⟪Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀),
            Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V
              (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))⟫
          + ⟪Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀),
              empiricalProcessVec P (fun _ => mdot) θ₀ n
                (fun i : Fin n => X i.val ξ)⟫)))
    (hExpB : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => B n ξ
      - (- (1 / 2) * ⟪empiricalProcessVec P (fun _ => mdot) θ₀ n
              (fun i : Fin n => X i.val ξ),
            Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
              (empiricalProcessVec P (fun _ => mdot) θ₀ n
                (fun i : Fin n => X i.val ξ))⟫)))
    (hNearMax : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => max 0 (B n ξ - A n ξ)))
    (hθhat_meas : ∀ n, Measurable
      (fun ξ : Ξ => θ_hat n (fun i : Fin n => X i.val ξ))) :
    WeakConverges
      (fun n => μ.map (fun ξ =>
        Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)))
      (multivariateGaussian 0 (V⁻¹ * psiCov P (fun _ => mdot) θ₀ * (V⁻¹)ᵀ)) := by
  classical
  -- B2: linear representation  √n(θ̂-θ₀) + V⁻¹ 𝔾ₙṁ →ₚ 0.
  have hlin := mEstimator_linear_representation P mdot θ₀ V hVunit hVsymm hc hVneg
    θ_hat μ X A B hExpA hExpB hNearMax
  -- CLT: 𝔾ₙṁ ⇝ N(0, psiCov).
  have hCLT := empiricalProcessVec_weakConverges P (fun _ => mdot) θ₀ μ X hX_meas
    hX_indep hX_id hX_law hmdot_meas hψ_L2 hPmdot_zero
  have hPSD := psiCov_posSemidef P (fun _ => mdot) θ₀ hψ_L2
  -- Measurability of the vector empirical process `𝔾ₙṁ`.
  have hG_meas : ∀ n, Measurable (fun ξ : Ξ =>
      empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)) := by
    intro n
    have hcoord : ∀ h : Fin d, Measurable
        (fun ξ : Ξ => empiricalProcess P n (fun i : Fin n => X i.val ξ) (mdot h)) := by
      intro h
      simp only [empiricalProcess, empiricalAvg]
      refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
      exact Finset.measurable_sum _ (fun i _ => (hmdot_meas h).comp (hX_meas i.val))
    exact (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp (measurable_pi_iff.mpr hcoord)
  -- Push the CLT through the continuous linear map `-V⁻¹`.
  have hmap := WeakConverges.map hCLT
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)).continuous
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)).continuous.measurable
  rw [multivariateGaussian_map_toEuclideanCLM (-V⁻¹) 0 hPSD] at hmap
  -- Identify the limit `N(0, V⁻¹ psiCov (V⁻¹)ᵀ)` and the mapped statistic.
  have hcov : (-V⁻¹) * psiCov P (fun _ => mdot) θ₀ * (-V⁻¹)ᴴ
      = V⁻¹ * psiCov P (fun _ => mdot) θ₀ * (V⁻¹)ᵀ := by
    have hHT : (V⁻¹)ᴴ = (V⁻¹)ᵀ := by
      ext i j; rw [Matrix.conjTranspose_apply, Matrix.transpose_apply, star_trivial]
    rw [Matrix.conjTranspose_neg, hHT]
    simp only [neg_mul, mul_neg]
    exact neg_neg _
  rw [hcov, map_zero] at hmap
  have hmap' : WeakConverges (fun n => μ.map (fun ξ : Ξ =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)
        (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ))))
      (multivariateGaussian 0 (V⁻¹ * psiCov P (fun _ => mdot) θ₀ * (V⁻¹)ᵀ)) := by
    have hfun : (fun n => μ.map (fun ξ : Ξ =>
          Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)
            (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ))))
        = (fun n => (μ.map (fun ξ : Ξ =>
            empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ))).map
              (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹))) := by
      funext n
      exact (Measure.map_map
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)).continuous.measurable
        (hG_meas n)).symm
    rw [hfun]; exact hmap
  -- Slutsky: transport the limit along the `o_P(1)` difference.
  refine WeakConverges.slutsky_of_tendstoInMeasure_dist
    (X := fun n ξ => Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)
      (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))
    (Y := fun n ξ => Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))
    (fun n => ((Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)).continuous.measurable.comp
      (hG_meas n)).aemeasurable)
    (fun n => (((hθhat_meas n).sub measurable_const).const_smul (Real.sqrt n)).aemeasurable)
    hmap' ?_
  intro ε hε
  have hset : ∀ n, {ξ : Ξ | ε ≤ dist
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) (-V⁻¹)
          (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))
        (Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀))}
      = {ξ : Ξ | ε ≤ ‖Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
              (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ))‖} := by
    intro n
    ext ξ
    simp only [Set.mem_setOf_eq, dist_eq_norm, map_neg, ContinuousLinearMap.neg_apply]
    rw [show -Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
          (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ))
        - Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
      = -(Real.sqrt n • (θ_hat n (fun i : Fin n => X i.val ξ) - θ₀)
          + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) V⁻¹
              (empiricalProcessVec P (fun _ => mdot) θ₀ n (fun i : Fin n => X i.val ξ)))
        from by abel, norm_neg]
  simp only [hset]
  exact hlin ε hε

/-! ### Headline — vdV Theorem 5.23.

The book-faithful headline `m_estimator_normality` (which reduces to
`mEstimator_normality_of_expansion` above) has **moved** to
`StatLean/AsymptoticStatistics/MEstimator/AsymptoticNormality.lean`. It must consume both
`Rate.mEstimator_sqrtn_rate` (§D) and `LinearizationEquicontinuity` (§C); since
`MEstimator/Rate.lean` imports *this* file, the headline cannot live here without an
import cycle. The new file imports `Rate` + `LinearizationEquicontinuity` + this file
and hosts the reduction. -/

end AsymptoticStatistics.MEstimator
