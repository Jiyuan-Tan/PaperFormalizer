module
public import StatLean.AsymptoticStatistics.ParametricFamily.Defs
public import StatLean.AsymptoticStatistics.DQM.Defs
public import StatLean.AsymptoticStatistics.ForMathlib.L2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# Consequences of Differentiability in Quadratic Mean (DQM)

Analytical lemmas that follow from the bare DQM assumption
(`AsymptoticStatistics.DifferentiableQuadraticMean`), independent of any specific
theorem. They discharge the auxiliary hypotheses appearing in Theorem 7.2.

Headline declarations: `dqm_residual_eventually_memLp` (the rescaled DQM residual is
in `L²(μ)` near `0`), `dqm_score_memLp_two` (the score `⟨u, ℓ⟩·√p_{θ₀}` is in `L²(μ)`,
essentially Theorem 7.2 (ii)), `dqm_fisher_integrable` (integrability of `⟨u, ℓ⟩² · p_{θ₀}`),
`dqm_sqrt_density_l2_convergence`, `dqm_fisher_cont`, and the asymptotic singular-mass
controls `dqm_perturbation_deficit_mass_tendsto` / `dqm_perturbation_excess_mass_tendsto`.
-/

open MeasureTheory Asymptotics Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace AsymptoticStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]

/-- **DQM ⇒ rescaled residual eventually in L²(μ).**

For every direction `u : Θ`, the function

  `q_t(x) := t⁻¹ · (√p_{θ₀+t·u}(x) − √p_{θ₀}(x))
            − (1/2) · ⟨u, ℓ x⟩ · √p_{θ₀}(x)`

belongs to `L²(μ)` for every `t` in some punctured neighbourhood of `0`.

This theorem supplies the `h_fminus_memLp` input used by
`LANExpansion.score_mean_zero` and `LANExpansion.LAN_expansion_score_fisher_part`.

**Proof.** From `hDQM.mem`, the unrescaled DQM residual
`r(h) := √p_{θ₀+h} − √p_{θ₀} − (1/2)⟨h, ℓ⟩·√p_{θ₀}`
is in `L²(μ)` for every `h` in some neighbourhood of `0 ∈ Θ`.  Composing with
the continuous map `t ↦ t • u : ℝ → Θ`, we get `MemLp (r(t·u)) 2 μ` eventually
as `t → 0` (in the punctured filter).  For `t ≠ 0`, the pointwise identity
`r(t·u)(x) = t · q_t(x)` (using `⟨t·u, ℓ x⟩ = t·⟨u, ℓ x⟩` and `t·t⁻¹ = 1`)
gives `q_t = t⁻¹ · r(t·u)`, which is in `L²(μ)` by `MemLp.const_mul`. -/
lemma dqm_residual_eventually_memLp
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ) (u : Θ) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      MemLp (fun x =>
        t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
          - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ := by
  -- Step 1: continuous specialisation `t ↦ t • u : ℝ → Θ`.
  have h_smul_tendsto :
      Filter.Tendsto (fun t : ℝ => t • u) (𝓝 (0 : ℝ)) (𝓝 (0 : Θ)) := by
    have h_cont : Continuous (fun t : ℝ => t • u) := continuous_id.smul continuous_const
    simpa using h_cont.tendsto (0 : ℝ)
  have h_smul_ne :
      Filter.Tendsto (fun t : ℝ => t • u) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : Θ)) :=
    h_smul_tendsto.mono_left nhdsWithin_le_nhds
  -- Step 2: pull back `hDQM.mem` along `t ↦ t • u`.
  have h_residual_eventually :
      ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        MemLp (fun x => M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x
                        - (1/2 : ℝ) * ⟪t • u, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ := by
    exact h_smul_ne.eventually hDQM.mem
  -- Step 3: combine with `t ≠ 0`; pointwise rewrite to `t⁻¹ · r(t·u) = q_t`.
  filter_upwards [h_residual_eventually, self_mem_nhdsWithin]
    with t h_residual_t ht_mem
  have ht_ne : t ≠ 0 := by simpa [Set.mem_compl_iff] using ht_mem
  have ht_inv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht_ne
  -- Pointwise identity: `q_t(x) = t⁻¹ · r(t·u)(x)`.
  have h_pt : ∀ x,
      t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
        - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x
      = t⁻¹ *
        (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x
          - (1/2 : ℝ) * ⟪t • u, ℓ x⟫ * M.sqrtDensity θ₀ x) := by
    intro x
    have h_inner : (⟪t • u, ℓ x⟫ : ℝ) = t * ⟪u, ℓ x⟫ :=
      real_inner_smul_left u (ℓ x) t
    have h_t_inv_t : t⁻¹ * t = 1 := inv_mul_cancel₀ ht_ne
    rw [h_inner]
    -- Algebraic: t⁻¹·(A − tB) = t⁻¹·A − t⁻¹·t·B = t⁻¹·A − B.
    field_simp
  -- Step 4: rewrite the goal to `MemLp (t⁻¹ · r(t·u)) 2 μ` and apply
  --         `MemLp.const_mul` to `h_residual_t`.
  have h_funext :
      (fun x =>
        t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
          - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x)
      = (fun x =>
        t⁻¹ *
          (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x
            - (1/2 : ℝ) * ⟪t • u, ℓ x⟫ * M.sqrtDensity θ₀ x)) := by
    funext x; exact h_pt x
  rw [h_funext]
  exact h_residual_t.const_mul (t⁻¹)

/-- **DQM ⇒ score is in L²(μ).**

For every direction `u : Θ`, the function `x ↦ ⟨u, ℓ x⟩ · √p_{θ₀}(x)` is in
`L²(μ)`. This is the L² content behind the existence of the Fisher information
in direction `u` and is essentially conclusion (ii) of Theorem 7.2.

**Proof.** Pick any `t ≠ 0` in the eventually-set produced by
`dqm_residual_eventually_memLp`. Then
  `q_t = t⁻¹·(√p_{θ₀+t·u} − √p_{θ₀}) − (1/2)·⟨u, ℓ⟩·√p_{θ₀} ∈ L²(μ)`.
Both `√p_{θ₀+t·u}` and `√p_{θ₀}` are in `L²(μ)` (via `sqrtDensity_memLp_two`
applied to the integrable densities), so their (scaled) difference
`t⁻¹·(√p_{θ₀+t·u} − √p_{θ₀})` is in `L²(μ)`.
Subtracting `q_t` recovers `(1/2)·⟨u, ℓ⟩·√p_{θ₀}`, and scaling by `2` gives
`⟨u, ℓ⟩·√p_{θ₀}`. -/
lemma dqm_score_memLp_two
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ)
    (hint : Integrable (M.density θ₀) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ) (u : Θ)
    (hint_perturb : ∀ t : ℝ, Integrable (M.density (θ₀ + t • u)) μ) :
    MemLp (fun x => ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ := by
  -- Step 1: extract a witness `t ≠ 0` such that `MemLp q_t 2 μ`.
  have h_q := dqm_residual_eventually_memLp M μ θ₀ ℓ hDQM u
  have h_q' :
      ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        (MemLp (fun x =>
            t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
              - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ) ∧ t ≠ 0 := by
    filter_upwards [h_q, self_mem_nhdsWithin] with t hq ht_mem
    exact ⟨hq, ht_mem⟩
  obtain ⟨t, ht_qt, ht_ne⟩ := h_q'.exists
  -- Step 2: square roots of both densities are in L²(μ).
  have h_sqrt_θ : MemLp (M.sqrtDensity θ₀) 2 μ :=
    M.sqrtDensity_memLp_two μ θ₀ hint
  have h_sqrt_θtu : MemLp (M.sqrtDensity (θ₀ + t • u)) 2 μ :=
    M.sqrtDensity_memLp_two μ (θ₀ + t • u) (hint_perturb t)
  -- Step 3: their difference, scaled by `t⁻¹`, is in L²(μ).
  have h_diff_memLp :
      MemLp (fun x => M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x) 2 μ :=
    h_sqrt_θtu.sub h_sqrt_θ
  have h_scaled_diff_memLp :
      MemLp (fun x =>
        t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)) 2 μ :=
    h_diff_memLp.const_mul (t⁻¹)
  -- Step 4: `(1/2)·⟨u, ℓ⟩·√p_{θ₀} = scaled_diff − q_t` (pointwise),
  --         hence in L²(μ) by closure under subtraction.
  have h_half_score :
      MemLp (fun x => (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ := by
    have h_funext :
        (fun x => (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) =
        (fun x =>
          (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)) -
          (t⁻¹ * (M.sqrtDensity (θ₀ + t • u) x - M.sqrtDensity θ₀ x)
            - (1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x)) := by
      funext x; ring
    rw [h_funext]
    exact h_scaled_diff_memLp.sub ht_qt
  -- Step 5: scale by 2 to drop the `(1/2)` factor.
  have h_funext :
      (fun x => ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) =
      (fun x => 2 * ((1/2 : ℝ) * ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x)) := by
    funext x; ring
  rw [h_funext]
  exact h_half_score.const_mul (2 : ℝ)

/-- **DQM rate, sequence form.**

Specialise the `IsLittleO` rate of DQM along the sequence `htil_n := h_n / √n`,
which → `0` in `Θ` whenever `h_n → h` (bounded). The conclusion is the
sequence form of vdV's "DQM along the curve `θ₀ + h_n / √n`":

  `∫ (√n · (√p_{θ₀ + h_n/√n} − √p_{θ₀}) − ½⟨h_n, ℓ⟩ · √p_{θ₀})² dμ → 0`.

Pure DQM analysis — no Fisher continuity assumption needed (the score appears
with `h_n`, not the limit `h`). The "swap to `h`" step lives in
`dqm_sqrt_density_l2_convergence`. -/
lemma dqm_residual_rate_along
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    {h : Θ} {h_n : ℕ → Θ} (hconv : Tendsto h_n atTop (𝓝 h)) :
    Tendsto
      (fun n : ℕ =>
        ∫ x,
          (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                          - M.sqrtDensity θ₀ x)
           - (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  -- Abbreviation: `htil_n := (1/√n) • h_n`.
  set htil : ℕ → Θ := fun n => (Real.sqrt n)⁻¹ • h_n n with hhtil_def
  -- `htil_n → 0`.
  have hhtil_tendsto : Tendsto htil atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h_norm_h_n : Tendsto (fun n : ℕ => ‖h_n n‖) atTop (𝓝 ‖h‖) := hconv.norm
    have h_inv_sqrt : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop := by
        have h2 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
        exact Real.tendsto_sqrt_atTop.comp h2
      simpa using! h1.inv_tendsto_atTop
    have h_prod := h_inv_sqrt.mul h_norm_h_n
    simp only [zero_mul] at h_prod
    refine h_prod.congr' ?_
    refine Filter.Eventually.of_forall fun n => ?_
    change (Real.sqrt n)⁻¹ * ‖h_n n‖ = ‖htil n‖
    rw [hhtil_def, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  -- ‖h_n‖ ≤ M_bd uniformly (from `hconv.norm`).
  have h_bound : ∃ M_bd : ℝ, ∀ n, ‖h_n n‖ ≤ M_bd := by
    obtain ⟨M_bd, _, hM⟩ := hconv.norm.bddAbove_range.exists_ge 0
    exact ⟨M_bd, fun n => hM ‖h_n n‖ ⟨n, rfl⟩⟩
  obtain ⟨M_bd, hM_bd⟩ := h_bound
  -- DQM along the sequence htil_n → 0.
  have h_along : (fun n : ℕ =>
        ∫ x, (M.sqrtDensity (θ₀ + htil n) x - M.sqrtDensity θ₀ x
              - (1 / 2 : ℝ) * ⟪htil n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
      =o[atTop] (fun n : ℕ => ‖htil n‖ ^ 2) :=
    hDQM.isLittleO.comp_tendsto hhtil_tendsto
  -- Convert to ε-δ form.
  rw [Metric.tendsto_atTop]
  intro ε hε
  set c : ℝ := ε / (M_bd ^ 2 + 1) with hc_def
  have hc_pos : 0 < c := div_pos hε (by positivity)
  have hc_bd : ∀ n, c * ‖h_n n‖ ^ 2 < ε := by
    intro n
    have h_denom : 0 < M_bd ^ 2 + 1 := by positivity
    have h_norm_sq : ‖h_n n‖ ^ 2 ≤ M_bd ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hM_bd n) 2
    rw [hc_def, div_mul_eq_mul_div, div_lt_iff₀ h_denom]
    nlinarith [hε, h_norm_sq, sq_nonneg M_bd]
  have h_bd := (Asymptotics.isLittleO_iff.mp h_along) hc_pos
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp h_bd
  refine ⟨max N 1, fun n hn => ?_⟩
  have hN_le : N ≤ n := le_trans (le_max_left _ _) hn
  have hn_one_le : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn_nat_pos : 0 < n := hn_one_le
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_nat_pos
  have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hsqrt_ne : Real.sqrt n ≠ 0 := ne_of_gt hsqrt_pos
  have h_bd_n := hN n hN_le
  -- Pointwise: `(target_n)² = (√n)² · r(htil_n)²`.
  have h_pt : ∀ x,
      (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                      - M.sqrtDensity θ₀ x)
       - (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
      = (Real.sqrt n) ^ 2 *
        (M.sqrtDensity (θ₀ + htil n) x - M.sqrtDensity θ₀ x
          - (1 / 2 : ℝ) * ⟪htil n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 := by
    intro x
    have h_inner : (⟪htil n, ℓ x⟫ : ℝ) = (Real.sqrt n)⁻¹ * (⟪h_n n, ℓ x⟫ : ℝ) := by
      rw [hhtil_def]; exact real_inner_smul_left (h_n n) (ℓ x) _
    rw [hhtil_def, h_inner]
    have h_factor :
        M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x - M.sqrtDensity θ₀ x
          - (1 / 2 : ℝ) * ((Real.sqrt n)⁻¹ * ⟪h_n n, ℓ x⟫) * M.sqrtDensity θ₀ x
        = (Real.sqrt n)⁻¹ *
          (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                          - M.sqrtDensity θ₀ x)
           - (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫ * M.sqrtDensity θ₀ x) := by
      have h_t_inv_t : (Real.sqrt n)⁻¹ * Real.sqrt n = 1 :=
        inv_mul_cancel₀ hsqrt_ne
      have hcancel :
          (Real.sqrt n)⁻¹ * (Real.sqrt n *
              (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                - M.sqrtDensity θ₀ x))
          = M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
            - M.sqrtDensity θ₀ x := by
        rw [← mul_assoc, h_t_inv_t, one_mul]
      linarith [hcancel]
    rw [h_factor]
    field_simp
  have h_int_eq :
      ∫ x,
        (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                        - M.sqrtDensity θ₀ x)
         - (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
      = (Real.sqrt n) ^ 2 *
        ∫ x,
          (M.sqrtDensity (θ₀ + htil n) x - M.sqrtDensity θ₀ x
            - (1 / 2 : ℝ) * ⟪htil n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ := by
    simp_rw [h_pt]
    rw [MeasureTheory.integral_const_mul]
  have h_norm_htil_sq : ‖htil n‖ ^ 2 = (Real.sqrt n)⁻¹ ^ 2 * ‖h_n n‖ ^ 2 := by
    rw [hhtil_def, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have h_int_nn :
      0 ≤ ∫ x,
          (M.sqrtDensity (θ₀ + htil n) x - M.sqrtDensity θ₀ x
            - (1 / 2 : ℝ) * ⟪htil n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
  have h_bound_t : ∫ x,
          (M.sqrtDensity (θ₀ + htil n) x - M.sqrtDensity θ₀ x
            - (1 / 2 : ℝ) * ⟪htil n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ ≤
        c * ((Real.sqrt n)⁻¹ ^ 2 * ‖h_n n‖ ^ 2) := by
    have := h_bd_n
    rw [Real.norm_eq_abs, abs_of_nonneg h_int_nn,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at this
    rw [h_norm_htil_sq] at this
    exact this
  have h_target_bd :
      (Real.sqrt n) ^ 2 *
        ∫ x,
          (M.sqrtDensity (θ₀ + htil n) x - M.sqrtDensity θ₀ x
            - (1 / 2 : ℝ) * ⟪htil n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ ≤
        (Real.sqrt n) ^ 2 * (c * ((Real.sqrt n)⁻¹ ^ 2 * ‖h_n n‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left h_bound_t (sq_nonneg _)
  have h_simp :
      (Real.sqrt n) ^ 2 * (c * ((Real.sqrt n)⁻¹ ^ 2 * ‖h_n n‖ ^ 2)) =
        c * ‖h_n n‖ ^ 2 := by
    field_simp
  rw [h_int_eq, Real.dist_eq, sub_zero]
  have h_target_nn : 0 ≤ (Real.sqrt n) ^ 2 *
        ∫ x,
          (M.sqrtDensity (θ₀ + htil n) x - M.sqrtDensity θ₀ x
            - (1 / 2 : ℝ) * ⟪htil n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ :=
    mul_nonneg (sq_nonneg _) h_int_nn
  rw [abs_of_nonneg h_target_nn]
  rw [h_simp] at h_target_bd
  exact lt_of_le_of_lt h_target_bd (hc_bd n)

/-- **DQM ⇒ joint L² convergence of rescaled square-root density.**

Given `h_n → h` in `Θ`,
  `√n · (√p_{θ₀ + h_n/√n} − √p_{θ₀}) → ½⟨h, ℓ⟩ · √p_{θ₀}`  in `L²(μ)`.

Central analytical input to Theorem 7.2 Steps 2 and 3.

Combines `dqm_residual_rate_along` (which gives the same convergence with
`⟨h_n, ℓ⟩` in place of `⟨h, ℓ⟩`) with the Fisher-continuity-at-`0` hypothesis
`h_fisher_cont` (automatic in finite-dim from `dqm_fisher_integrable`).

**Proof.** Pointwise `(X + Y)² ≤ 2X² + 2Y²` where
`X := √n(√p_n − √p) − ½⟨h_n, ℓ⟩√p` and `Y := ½⟨h_n − h, ℓ⟩√p`. Both
`∫X² → 0` (from `dqm_residual_rate_along`) and `∫Y² → 0` (from Fisher
continuity at `0` applied to `h_n − h → 0`). Squeeze. -/
lemma dqm_sqrt_density_l2_convergence
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ)
    (hint : Integrable (M.density θ₀) μ)
    (hint_perturb : ∀ t : ℝ, ∀ u : Θ, Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (h_fisher_cont :
      Tendsto (fun v : Θ => ∫ x, ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ)
        (𝓝 0) (𝓝 0))
    {h : Θ} {h_n : ℕ → Θ} (hconv : Tendsto h_n atTop (𝓝 h)) :
    Tendsto
      (fun n : ℕ =>
        ∫ x,
          (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                          - M.sqrtDensity θ₀ x)
           - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  -- The two pieces.
  have h_first : Tendsto (fun n : ℕ =>
        ∫ x,
          (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                          - M.sqrtDensity θ₀ x)
           - (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
        atTop (𝓝 0) :=
    dqm_residual_rate_along M μ θ₀ ℓ hDQM hconv
  -- The Fisher-continuity piece, in the form `∫ ((1/2)⟨h_n − h, ℓ⟩√p)² → 0`.
  have h_second : Tendsto (fun n : ℕ =>
        ∫ x, ((1 / 2 : ℝ) * ⟪h_n n - h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
        atTop (𝓝 0) := by
    have hconv_diff : Tendsto (fun n : ℕ => h_n n - h) atTop (𝓝 0) := by
      have := hconv.sub (tendsto_const_nhds (x := h))
      simpa using this
    -- Pointwise rewrite: ((1/2)⟨v, ℓ⟩√p)² = (1/4)⟨v, ℓ⟩²·p.
    have h_inner_int_eq : ∀ v : Θ,
        ∫ x, ((1 / 2 : ℝ) * ⟪v, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
          = (1 / 4 : ℝ) * ∫ x, ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ := by
      intro v
      have hpt : ∀ x,
          ((1 / 2 : ℝ) * ⟪v, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 =
            (1 / 4 : ℝ) * (⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x) := by
        intro x
        have hsq : (M.sqrtDensity θ₀ x) ^ 2 = M.density θ₀ x :=
          M.sqrtDensity_sq θ₀ x
        have heq : ((1 / 2 : ℝ) * ⟪v, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
              = (1 / 4 : ℝ) * (⟪v, ℓ x⟫ ^ 2 * (M.sqrtDensity θ₀ x) ^ 2) := by ring
        rw [heq, hsq]
      simp_rw [hpt]
      rw [MeasureTheory.integral_const_mul]
    have h_fisher_along :
        Tendsto (fun n : ℕ => ∫ x, ⟪h_n n - h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ)
          atTop (𝓝 0) :=
      h_fisher_cont.comp hconv_diff
    have h_quarter := h_fisher_along.const_mul (1 / 4 : ℝ)
    simp only [mul_zero] at h_quarter
    refine h_quarter.congr fun n => ?_
    rw [h_inner_int_eq (h_n n - h)]
  -- Eventually-integrability of X² (the `dqm_residual_rate_along` integrand).
  -- From `hDQM.mem` composed with `htil_n → 0`: `r(htil_n) ∈ L²(μ)` eventually.
  set htil : ℕ → Θ := fun n => (Real.sqrt n)⁻¹ • h_n n with hhtil_def
  have hhtil_tendsto : Tendsto htil atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h_inv_sqrt : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      simpa using! h1.inv_tendsto_atTop
    have h_prod := h_inv_sqrt.mul hconv.norm
    simp only [zero_mul] at h_prod
    refine h_prod.congr' (Filter.Eventually.of_forall fun n => ?_)
    change (Real.sqrt n)⁻¹ * ‖h_n n‖ = ‖htil n‖
    rw [hhtil_def, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  have hX_memLp_eventually : ∀ᶠ (n : ℕ) in atTop,
      MemLp (fun x => Real.sqrt n *
                (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                  - M.sqrtDensity θ₀ x)
              - (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ := by
    have h_mem_along := hhtil_tendsto.eventually hDQM.mem
    -- h_mem_along : ∀ᶠ n, MemLp (r(htil n)) 2 μ, where
    -- r(htil n)(x) = √p_{θ₀ + htil n}(x) − √p_{θ₀}(x) − (1/2)⟨htil n, ℓ x⟩ √p_{θ₀}(x)
    --             = √p_n(x) − √p_{θ₀}(x) − (1/2·1/√n)⟨h_n, ℓ x⟩ √p_{θ₀}(x).
    -- Then √n · r(htil n)(x) = √n(√p_n − √p) − (1/2)⟨h_n, ℓ⟩√p = X_n(x),
    -- so X_n = (√n)·r(htil n) ∈ L²(μ) (constant scaling) when r(htil n) ∈ L²(μ).
    filter_upwards [h_mem_along, Filter.eventually_ge_atTop 1] with n h_mem_n hn_pos
    have hn_nat_pos : 0 < n := hn_pos
    have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_nat_pos
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos_real
    have hsqrt_ne : Real.sqrt n ≠ 0 := ne_of_gt hsqrt_pos
    -- Pointwise: X_n(x) = √n · r(htil n)(x).
    have h_eq : (fun x => Real.sqrt n *
                  (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                    - M.sqrtDensity θ₀ x)
                - (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫ * M.sqrtDensity θ₀ x)
              = (fun x => Real.sqrt n *
                  (M.sqrtDensity (θ₀ + htil n) x - M.sqrtDensity θ₀ x
                    - (1 / 2 : ℝ) * ⟪htil n, ℓ x⟫ * M.sqrtDensity θ₀ x)) := by
      funext x
      have h_inner : (⟪htil n, ℓ x⟫ : ℝ) = (Real.sqrt n)⁻¹ * (⟪h_n n, ℓ x⟫ : ℝ) := by
        rw [hhtil_def]; exact real_inner_smul_left (h_n n) (ℓ x) _
      rw [hhtil_def, h_inner]
      have h_t_inv_t : (Real.sqrt n)⁻¹ * Real.sqrt n = 1 :=
        inv_mul_cancel₀ hsqrt_ne
      have hcancel :
          Real.sqrt n * ((Real.sqrt n)⁻¹ * (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫
                          * M.sqrtDensity θ₀ x)
          = (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫ * M.sqrtDensity θ₀ x := by
        rw [show Real.sqrt n * ((Real.sqrt n)⁻¹ * (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫
                                  * M.sqrtDensity θ₀ x)
              = Real.sqrt n * (Real.sqrt n)⁻¹ * (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫
                  * M.sqrtDensity θ₀ x from by ring,
            mul_inv_cancel₀ hsqrt_ne, one_mul]
      ring_nf
      ring_nf at hcancel
      linarith [hcancel]
    rw [h_eq]
    exact h_mem_n.const_mul (Real.sqrt n)
  -- Y_n is in L²(μ) for every n (from dqm_score_memLp_two on direction h_n n - h).
  have hY_memLp : ∀ n,
      MemLp (fun x => (1 / 2 : ℝ) * ⟪h_n n - h, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ := by
    intro n
    have h_score_memLp :
        MemLp (fun x => ⟪h_n n - h, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ :=
      dqm_score_memLp_two M μ θ₀ ℓ hint hDQM (h_n n - h)
        (fun t => hint_perturb t (h_n n - h))
    -- Multiply by 1/2 (constant).
    have h_eq : (fun x => (1 / 2 : ℝ) * ⟪h_n n - h, ℓ x⟫ * M.sqrtDensity θ₀ x)
              = (fun x => (1 / 2 : ℝ) * (⟪h_n n - h, ℓ x⟫ * M.sqrtDensity θ₀ x)) := by
      funext x; ring
    rw [h_eq]
    exact h_score_memLp.const_mul (1 / 2 : ℝ)
  -- Squeeze.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (b := atTop)
    (g := fun (_ : ℕ) => (0 : ℝ))
    (h := fun (n : ℕ) =>
      2 * ∫ x,
            (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                            - M.sqrtDensity θ₀ x)
             - (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ +
      2 * ∫ x,
            ((1 / 2 : ℝ) * ⟪h_n n - h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
    tendsto_const_nhds
    ?_
    (Filter.Eventually.of_forall fun (_ : ℕ) =>
      MeasureTheory.integral_nonneg (fun _ => sq_nonneg _))
    ?_
  · -- Upper bound → 0.
    have h1 := h_first.const_mul (2 : ℝ)
    have h2 := h_second.const_mul (2 : ℝ)
    simp only [mul_zero] at h1 h2
    have := h1.add h2
    simpa using this
  · -- Pointwise + integration upper bound (eventually for `n ≥ 1`).
    filter_upwards [hX_memLp_eventually] with n hX_memLp_n
    -- Pointwise (X + Y)² ≤ 2X² + 2Y².
    have h_pt : ∀ x,
        (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                        - M.sqrtDensity θ₀ x)
         - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ≤
          2 * (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                              - M.sqrtDensity θ₀ x)
               - (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 +
          2 * ((1 / 2 : ℝ) * ⟪h_n n - h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 := by
      intro x
      have h_inner_split :
          (⟪h, ℓ x⟫ : ℝ) = (⟪h_n n, ℓ x⟫ : ℝ) - (⟪h_n n - h, ℓ x⟫ : ℝ) := by
        have h_lin : (⟪h_n n - h, ℓ x⟫ : ℝ) = (⟪h_n n, ℓ x⟫ : ℝ) - (⟪h, ℓ x⟫ : ℝ) :=
          inner_sub_left (h_n n) h (ℓ x)
        linarith [h_lin]
      have h_eq :
          Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                         - M.sqrtDensity θ₀ x)
            - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x
          = (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                            - M.sqrtDensity θ₀ x)
             - (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫ * M.sqrtDensity θ₀ x) +
            ((1 / 2 : ℝ) * ⟪h_n n - h, ℓ x⟫ * M.sqrtDensity θ₀ x) := by
        rw [h_inner_split]; ring
      rw [h_eq]
      exact L2Utils.sq_add_le_two_mul_sq _ _
    -- Integrability of RHS.
    have hX_sq_int := hX_memLp_n.integrable_sq
    have hY_sq_int := (hY_memLp n).integrable_sq
    have h_rhs_int : Integrable (fun x =>
        2 * (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                            - M.sqrtDensity θ₀ x)
             - (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 +
        2 * ((1 / 2 : ℝ) * ⟪h_n n - h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2) μ :=
      (hX_sq_int.const_mul 2).add (hY_sq_int.const_mul 2)
    -- Integrate.
    have h_integrate :
        ∫ x, (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                              - M.sqrtDensity θ₀ x)
              - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ ≤
        ∫ x,
          (2 * (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                                - M.sqrtDensity θ₀ x)
                - (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 +
           2 * ((1 / 2 : ℝ) * ⟪h_n n - h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2) ∂μ :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        h_rhs_int
        (Filter.Eventually.of_forall h_pt)
    -- Split RHS via `integral_add` and `integral_const_mul`.
    have h_split :
        ∫ x,
          (2 * (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                                - M.sqrtDensity θ₀ x)
                - (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 +
           2 * ((1 / 2 : ℝ) * ⟪h_n n - h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2) ∂μ =
        2 * ∫ x,
              (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h_n n) x
                              - M.sqrtDensity θ₀ x)
               - (1 / 2 : ℝ) * ⟪h_n n, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ +
        2 * ∫ x,
              ((1 / 2 : ℝ) * ⟪h_n n - h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ := by
      rw [MeasureTheory.integral_add (hX_sq_int.const_mul 2) (hY_sq_int.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    linarith [h_integrate, h_split.symm ▸ h_integrate]

/-- **DQM ⇒ Fisher information is finite.**

Concrete restatement of `dqm_score_memLp_two` as the integrability of
`x ↦ ⟨u, ℓ x⟩² · p_{θ₀}(x)`.  This is exactly the form of `h_Fisher` in
`LANExpansion.score_mean_zero` and `LANExpansion.LAN_expansion_score_fisher_part`, so it discharges
that hypothesis and simultaneously closes Theorem 7.2 (ii) for direction `u`. -/
lemma dqm_fisher_integrable
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧)
    (θ₀ : Θ) (ℓ : 𝓧 → Θ)
    (hint : Integrable (M.density θ₀) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ) (u : Θ)
    (hint_perturb : ∀ t : ℝ, Integrable (M.density (θ₀ + t • u)) μ) :
    Integrable (fun x => ⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x) μ := by
  have h_score_memLp :
      MemLp (fun x => ⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ :=
    dqm_score_memLp_two M μ θ₀ ℓ hint hDQM u hint_perturb
  have h_int_sq :
      Integrable (fun x => (⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2) μ :=
    h_score_memLp.integrable_sq
  -- Pointwise: `(⟨u,ℓ⟩·√p_θ)² = ⟨u,ℓ⟩² · p_θ` since `(√p_θ)² = p_θ`.
  have h_pt : ∀ x,
      (⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 = ⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x := by
    intro x
    have hsq : (M.sqrtDensity θ₀ x) ^ 2 = M.density θ₀ x := M.sqrtDensity_sq θ₀ x
    rw [mul_pow, hsq]
  have h_funext :
      (fun x => ⟪u, ℓ x⟫ ^ 2 * M.density θ₀ x) =
      (fun x => (⟪u, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2) := by
    funext x; rw [h_pt]
  rw [h_funext]
  exact h_int_sq

/-- **Norm-squared score is integrable against the density** (finite-dim).

Decomposes `‖ℓ x‖²` as `∑ i (ℓ x).ofLp i ^ 2 = ∑ i ⟪e_i, ℓ x⟫²` using the
standard orthonormal basis of `EuclideanSpace ℝ (Fin k)`, then applies
`dqm_fisher_integrable` per coordinate and sums. -/
lemma dqm_norm_sq_score_integrable
    {k : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    (hint : Integrable (M.density θ₀) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (hint_perturb : ∀ t : ℝ, ∀ u : EuclideanSpace ℝ (Fin k),
      Integrable (M.density (θ₀ + t • u)) μ) :
    Integrable (fun x => ‖ℓ x‖ ^ 2 * M.density θ₀ x) μ := by
  classical
  -- Rewrite `‖ℓ x‖² = ∑ i, ⟪e_i, ℓ x⟫²` via the standard basis `e_i := single i 1`.
  have h_sum_ofLp_sq : ∀ y : EuclideanSpace ℝ (Fin k),
      ‖y‖ ^ 2 = ∑ i, (y.ofLp i) ^ 2 := by
    intro y
    rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    exact Finset.sum_congr rfl (fun i _ => by rw [Real.norm_eq_abs, sq_abs])
  have h_ofLp_eq_inner : ∀ (y : EuclideanSpace ℝ (Fin k)) (i : Fin k),
      (y.ofLp i : ℝ)
        = ⟪(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin k)), y⟫ := by
    intro y i
    have h := EuclideanSpace.inner_single_left (𝕜 := ℝ) i (1 : ℝ) y
    rw [map_one, one_mul] at h
    exact h.symm
  have h_fun_eq : (fun x => ‖ℓ x‖ ^ 2 * M.density θ₀ x)
      = fun x => ∑ i : Fin k,
        ⟪(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin k)), ℓ x⟫ ^ 2
          * M.density θ₀ x := by
    funext x
    rw [h_sum_ofLp_sq, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [h_ofLp_eq_inner]
  rw [h_fun_eq]
  refine integrable_finset_sum _ (fun i _ => ?_)
  exact dqm_fisher_integrable M μ θ₀ ℓ hint hDQM
    (EuclideanSpace.single i (1 : ℝ)) (fun t => hint_perturb t _)

/-- **DQM ⇒ Fisher quadratic form is continuous at 0** (finite-dim).

The map `v ↦ ∫ ⟨v, ℓ x⟩² p_{θ₀}(x) dμ(x)` tends to `0` as `v → 0`. This
discharges the `h_fisher_cont` auxiliary hypothesis of
`LANExpansion.LAN_expansion_iii` / `Ch7.AsymptoticRepresentation.LAN_representation`.

Proof: Cauchy-Schwarz gives the pointwise bound
`⟪v, ℓ x⟫² * p(x) ≤ ‖v‖² * ‖ℓ x‖² * p(x)`, and
`dqm_norm_sq_score_integrable` provides `∫ ‖ℓ‖² p dμ < ∞`. Hence
`∫ ⟪v, ℓ⟫² p dμ ≤ ‖v‖² · C` for a constant `C`, and `‖v‖² → 0` as `v → 0`. -/
lemma dqm_fisher_cont
    {k : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    (hint : Integrable (M.density θ₀) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (hint_perturb : ∀ t : ℝ, ∀ u : EuclideanSpace ℝ (Fin k),
      Integrable (M.density (θ₀ + t • u)) μ) :
    Tendsto
      (fun v : EuclideanSpace ℝ (Fin k) =>
        ∫ x, ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ)
      (𝓝 0) (𝓝 0) := by
  classical
  -- `C := ∫ ‖ℓ‖² p_θ₀ dμ < ∞` (finite by `dqm_norm_sq_score_integrable`).
  set C : ℝ := ∫ x, ‖ℓ x‖ ^ 2 * M.density θ₀ x ∂μ with hC_def
  have hC_int := dqm_norm_sq_score_integrable M μ θ₀ ℓ hint hDQM hint_perturb
  have hp_nn : ∀ x, 0 ≤ M.density θ₀ x := M.density_nonneg θ₀
  -- Pointwise Cauchy-Schwarz bound (after multiplying by `p(x) ≥ 0`).
  have h_bound : ∀ v : EuclideanSpace ℝ (Fin k), ∀ x,
      ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x ≤ ‖v‖ ^ 2 * (‖ℓ x‖ ^ 2 * M.density θ₀ x) := by
    intro v x
    have h_cs : ⟪v, ℓ x⟫ ^ 2 ≤ ‖v‖ ^ 2 * ‖ℓ x‖ ^ 2 := by
      have h := real_inner_mul_inner_self_le v (ℓ x)
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, ← sq] at h
      linarith
    calc ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x
        ≤ (‖v‖ ^ 2 * ‖ℓ x‖ ^ 2) * M.density θ₀ x :=
          mul_le_mul_of_nonneg_right h_cs (hp_nn x)
      _ = ‖v‖ ^ 2 * (‖ℓ x‖ ^ 2 * M.density θ₀ x) := by ring
  -- Nonnegativity of the integrand.
  have h_nn : ∀ v x, 0 ≤ ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x := fun v x =>
    mul_nonneg (sq_nonneg _) (hp_nn x)
  -- Integrated bound: `∫ ⟪v, ℓ⟫² p dμ ≤ ‖v‖² · C`. Integrability of the LHS
  -- comes from `dqm_fisher_integrable` (per-direction).
  have h_int_bound : ∀ v : EuclideanSpace ℝ (Fin k),
      ∫ x, ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ ≤ ‖v‖ ^ 2 * C := by
    intro v
    have h_int_v : Integrable (fun x => ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x) μ :=
      dqm_fisher_integrable M μ θ₀ ℓ hint hDQM v (fun t => hint_perturb t v)
    calc ∫ x, ⟪v, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ
        ≤ ∫ x, ‖v‖ ^ 2 * (‖ℓ x‖ ^ 2 * M.density θ₀ x) ∂μ :=
          MeasureTheory.integral_mono_ae h_int_v (hC_int.const_mul _)
            (Filter.Eventually.of_forall (h_bound v))
      _ = ‖v‖ ^ 2 * C := by rw [MeasureTheory.integral_const_mul]
  -- `v → 0` ⇒ `‖v‖² · C → 0`.
  have h_upper : Tendsto
      (fun v : EuclideanSpace ℝ (Fin k) => ‖v‖ ^ 2 * C) (𝓝 0) (𝓝 0) := by
    have h_norm_sq_zero : Tendsto
        (fun v : EuclideanSpace ℝ (Fin k) => ‖v‖ ^ 2) (𝓝 0) (𝓝 0) := by
      have := ((continuous_norm (E := EuclideanSpace ℝ (Fin k))).pow 2).tendsto
        (0 : EuclideanSpace ℝ (Fin k))
      simpa [norm_zero] using! this
    have := h_norm_sq_zero.mul_const C
    simpa [zero_mul] using this
  -- Squeeze: `0 ≤ ∫ ⟪v, ℓ⟫² p ≤ ‖v‖² · C` and `‖v‖² C → 0`, `0 → 0`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) h_upper
    (Filter.Eventually.of_forall (fun v =>
      MeasureTheory.integral_nonneg (fun x => h_nn v x)))
    (Filter.Eventually.of_forall h_int_bound)

/-! ## DQM ⇒ asymptotic singular-mass control (vdV §7.3)

The two lemmas below replace the *exact* finite-`n` change-of-measure identity (which forced
absolute continuity and hence a common-support hypothesis) by a DQM-derived **asymptotic** bound:
each per-factor singular set carries `o(1/n)` probability mass. DQM does *not* imply common
support; this is asymptotic singular-mass control, not a derivation of common support from DQM.

The "probability mass" here is the density integral `∫_A p dμ` over the singular set `A`, NOT the
bare `μ`-volume `μ A` (DQM controls density integrals, not the dominating-measure volume; a
`μ`-volume statement would be FALSE on infinite-`μ` / small-density regions). -/

/-- **Deficit side — `n · P_{θ_n}({p₀ = 0}) = o(1)`** (the genuine `Q ⊥ P` side).

Under DQM at `θ₀`, for a fixed direction `h`, the rescaled probability mass that the *perturbed*
density `p_{θ₀ + h/√n}` places on the set where the *base* density `p_{θ₀}` vanishes tends
to `0`:
`n · ∫_{x : p_{θ₀}(x) = 0} p_{θ₀+h/√n}(x) dμ → 0`.

vdV §7.3 (contiguity footing): DQM-derived asymptotic singular-mass control replacing the exact
change-of-measure identity.

**Proof.** Bound a restricted piece of the single `dqm_sqrt_density_l2_convergence` residual
`Rₙ = ∫(√n(√p_n − √p₀) − ½⟨h,ℓ⟩√p₀)² dμ → 0`. On `{p_{θ₀} = 0}` the base root `√p₀ = 0`,
so the residual integrand restricted there collapses to `(√n·√p_n)² = n·p_n`:
`n ∫_{p₀=0} p_n dμ = ∫_{p₀=0} gₙ dμ ≤ Rₙ → 0`.
Direct, no Cauchy–Schwarz. Reuse: `dqm_sqrt_density_l2_convergence`, `dqm_fisher_cont`
(to feed `h_fisher_cont`), `M.sqrtDensity_sq`. -/
lemma dqm_perturbation_deficit_mass_tendsto
    {k : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    (hint : Integrable (M.density θ₀) μ)
    (hint_perturb : ∀ t : ℝ, ∀ u : EuclideanSpace ℝ (Fin k),
      Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (h : EuclideanSpace ℝ (Fin k)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) * ∫ x in {x | M.density θ₀ x = 0},
          M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ)
      atTop (𝓝 0) := by
  -- `Rₙ → 0` from the L² convergence along the constant sequence `h_n ≡ h`.
  have h_fisher_cont := dqm_fisher_cont M μ θ₀ ℓ hint hDQM hint_perturb
  have hR : Tendsto
      (fun n : ℕ =>
        ∫ x,
          (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x
                          - M.sqrtDensity θ₀ x)
           - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
      atTop (𝓝 0) := by
    have := dqm_sqrt_density_l2_convergence M μ θ₀ ℓ hint
      (fun t u => hint_perturb t u) hDQM h_fisher_cont
      (h := h) (h_n := fun _ => h) tendsto_const_nhds
    simpa using this
  -- Eventual L²-membership of the residual integrand `Xₙ`, hence integrability of `gₙ = Xₙ²`.
  have hX_memLp_eventually : ∀ᶠ (n : ℕ) in atTop,
      MemLp (fun x => Real.sqrt n *
                (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)
              - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ := by
    have h_inv_sqrt : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      simpa using! h1.inv_tendsto_atTop
    have hhtil_tendsto : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ • h) atTop (𝓝 0) := by
      have := h_inv_sqrt.smul_const h
      simpa using this
    have h_mem_along := hhtil_tendsto.eventually hDQM.mem
    filter_upwards [h_mem_along, Filter.eventually_ge_atTop 1] with n h_mem_n hn_pos
    have hn_nat_pos : 0 < n := hn_pos
    have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_nat_pos
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos_real
    have hsqrt_ne : Real.sqrt n ≠ 0 := ne_of_gt hsqrt_pos
    have h_eq : (fun x => Real.sqrt n *
                  (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)
                - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x)
              = (fun x => Real.sqrt n *
                  (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x
                    - (1 / 2 : ℝ) * ⟪(Real.sqrt n)⁻¹ • h, ℓ x⟫ * M.sqrtDensity θ₀ x)) := by
      funext x
      have h_inner : (⟪(Real.sqrt n)⁻¹ • h, ℓ x⟫ : ℝ)
          = (Real.sqrt n)⁻¹ * (⟪h, ℓ x⟫ : ℝ) :=
        real_inner_smul_left h (ℓ x) _
      rw [h_inner]
      have h_t_inv_t : Real.sqrt n * (Real.sqrt n)⁻¹ = 1 := mul_inv_cancel₀ hsqrt_ne
      field_simp
    rw [h_eq]
    exact h_mem_n.const_mul (Real.sqrt n)
  -- Squeeze `0 ≤ (n)·∫_{p₀=0} p_n = ∫_{p₀=0} gₙ ≤ Rₙ → 0`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (b := atTop)
    (g := fun (_ : ℕ) => (0 : ℝ))
    (h := fun (n : ℕ) =>
      ∫ x,
        (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)
         - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
    tendsto_const_nhds hR ?_ ?_
  · -- Lower bound: `0 ≤ (n)·∫_{p₀=0} p_n`.
    refine Filter.Eventually.of_forall fun n => ?_
    apply mul_nonneg (Nat.cast_nonneg n)
    exact MeasureTheory.setIntegral_nonneg
      (measurableSet_eq_fun (M.density_meas θ₀) measurable_const)
      (fun x _ => M.density_nonneg _ x)
  · -- Upper bound: `(n)·∫_{p₀=0} p_n = ∫_{p₀=0} gₙ ≤ Rₙ`, eventually for `n ≥ 1`.
    filter_upwards [hX_memLp_eventually, Filter.eventually_ge_atTop 1]
      with n hX_memLp_n hn_pos
    have hn_nat_pos : 0 < n := hn_pos
    have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_nat_pos
    -- On `{p₀ = 0}`, `√p₀ = 0`, so `gₙ = (√n·√p_n)² = n·p_n`.
    have hset : MeasurableSet {x | M.density θ₀ x = 0} :=
      measurableSet_eq_fun (M.density_meas θ₀) measurable_const
    -- `gₙ` is integrable (`Xₙ ∈ L²`).
    have hg_int := hX_memLp_n.integrable_sq
    -- `(n)·∫_{p₀=0} p_n = ∫_{p₀=0} gₙ`.
    have h_restr_eq :
        (n : ℝ) * ∫ x in {x | M.density θ₀ x = 0},
            M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x ∂μ
          = ∫ x in {x | M.density θ₀ x = 0},
            (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x
                            - M.sqrtDensity θ₀ x)
             - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun hset (fun x hx => ?_)
      have hx0 : M.density θ₀ x = 0 := hx
      have hsqrt0 : M.sqrtDensity θ₀ x = 0 := by
        unfold ParametricFamily.sqrtDensity; rw [hx0, Real.sqrt_zero]
      have hpsq : M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x ^ 2
          = M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x := M.sqrtDensity_sq _ x
      rw [hsqrt0]
      have hnsq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hn_pos_real)
      have hpt : (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - 0)
                - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * 0) ^ 2
            = (Real.sqrt n) ^ 2 * M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x ^ 2 := by
        ring
      rw [hpt, hnsq, hpsq]
    rw [h_restr_eq]
    -- `∫_{p₀=0} gₙ ≤ ∫ gₙ = Rₙ`.
    exact MeasureTheory.setIntegral_le_integral hg_int
      (Filter.Eventually.of_forall (fun _ => sq_nonneg _))

/-- **Excess side — `n · P_{θ₀}({p_n = 0}) = o(1)`** (the `exp∘log` encoding-junk side).

Under DQM at `θ₀`, for a fixed direction `h`, the rescaled probability mass that the *base*
density `p_{θ₀}` places on the set where the *perturbed* density `p_{θ₀ + h/√n}` vanishes tends
to `0`:
`n · ∫_{x : p_{θ₀+h/√n}(x) = 0} p_{θ₀}(x) dμ → 0`.

vdV §7.3 (contiguity footing): DQM-derived asymptotic singular-mass control replacing the exact
change-of-measure identity.

This side exists **only** because the conclusion's `exp∘log` encoding deposits junk mass `1` on
`{p₀ > 0, p_n = 0}`; the honest Radon–Nikodym ratio drops it, leaving only the deficit side.

**Proof (absolute-continuity).** On `{p_{θ₀+h/√n} = 0}` the perturbed root
`√p_n = 0`, so `√n·(√p_n − √p₀) = −√n·√p₀` and `n·mₙ = ∫_{p_n=0} (√n(√p_n−√p₀))² dμ` with
`mₙ = ∫_{p_n=0} p₀ dμ`. Decompose `√n(√p_n−√p₀) = Xₙ + ½⟨h,ℓ⟩√p₀` (`Xₙ` the
`dqm_sqrt_density_l2_convergence` residual integrand) and bound by `(a+b)² ≤ 2a²+2b²`:
`n·mₙ ≤ 2∫_{p_n=0} Xₙ² + ½∫_{p_n=0} ⟨h,ℓ⟩²p₀ ≤ 2Rₙ + ½Bₙ`, where `Bₙ = ∫_{p_n=0} ⟨h,ℓ⟩²p₀ dμ`.
With `Bₙ ≤ I = ∫ ⟨h,ℓ⟩²p₀` (a fixed finite constant by `dqm_fisher_integrable`), `n·mₙ` is
bounded, so `mₙ → 0`; then `Bₙ → 0` by absolute continuity of the integral against
`P₀ = μ.withDensity p₀` (the singular-set mass `P₀({p_n=0}) = mₙ → 0`), and finally
`n·mₙ ≤ 2Rₙ + ½Bₙ → 0`. Reuse: `dqm_sqrt_density_l2_convergence`, `dqm_fisher_integrable`,
`dqm_fisher_cont`, `L2Utils.sq_add_le_two_mul_sq`, `Integrable.tendsto_setIntegral_nhds_zero`. -/
lemma dqm_perturbation_excess_mass_tendsto
    {k : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    (hint : Integrable (M.density θ₀) μ)
    (hint_perturb : ∀ t : ℝ, ∀ u : EuclideanSpace ℝ (Fin k),
      Integrable (M.density (θ₀ + t • u)) μ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (h : EuclideanSpace ℝ (Fin k)) :
    Tendsto
      (fun n : ℕ =>
        (n : ℝ) * ∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0},
          M.density θ₀ x ∂μ)
      atTop (𝓝 0) := by
  -- `Rₙ → 0` from the L² convergence along the constant sequence `h_n ≡ h`.
  have h_fisher_cont := dqm_fisher_cont M μ θ₀ ℓ hint hDQM hint_perturb
  have hR : Tendsto
      (fun n : ℕ =>
        ∫ x,
          (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x
                          - M.sqrtDensity θ₀ x)
           - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
      atTop (𝓝 0) := by
    have := dqm_sqrt_density_l2_convergence M μ θ₀ ℓ hint
      (fun t u => hint_perturb t u) hDQM h_fisher_cont
      (h := h) (h_n := fun _ => h) tendsto_const_nhds
    simpa using this
  -- `G := ⟨h,ℓ⟩²·p₀ ∈ L¹(μ)`; `I := ∫ G dμ` and `Bₙ := ∫_{p_n=0} G dμ ≤ I`.
  have hG_int : Integrable (fun x => ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x) μ :=
    dqm_fisher_integrable M μ θ₀ ℓ hint hDQM h (fun t => hint_perturb t h)
  -- `½·G = (½⟨h,ℓ⟩√p₀)²·2`; the score-square integrand `(½⟨h,ℓ⟩√p₀)² ∈ L¹`.
  have hYsq_int : Integrable
      (fun x => ((1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2) μ := by
    have h_eq : (fun x => ((1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2)
        = (fun x => (1 / 4 : ℝ) * (⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x)) := by
      funext x
      have hsq : (M.sqrtDensity θ₀ x) ^ 2 = M.density θ₀ x := M.sqrtDensity_sq θ₀ x
      have : ((1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
          = (1 / 4 : ℝ) * (⟪h, ℓ x⟫ ^ 2 * (M.sqrtDensity θ₀ x) ^ 2) := by ring
      rw [this, hsq]
    rw [h_eq]
    exact hG_int.const_mul (1 / 4 : ℝ)
  -- Eventual L²-membership of the residual integrand `Xₙ` (same as the deficit side).
  have hX_memLp_eventually : ∀ᶠ (n : ℕ) in atTop,
      MemLp (fun x => Real.sqrt n *
                (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)
              - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ := by
    have h_inv_sqrt : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      simpa using! h1.inv_tendsto_atTop
    have hhtil_tendsto : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ • h) atTop (𝓝 0) := by
      have := h_inv_sqrt.smul_const h
      simpa using this
    have h_mem_along := hhtil_tendsto.eventually hDQM.mem
    filter_upwards [h_mem_along, Filter.eventually_ge_atTop 1] with n h_mem_n hn_pos
    have hn_nat_pos : 0 < n := hn_pos
    have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_nat_pos
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos_real
    have hsqrt_ne : Real.sqrt n ≠ 0 := ne_of_gt hsqrt_pos
    have h_eq : (fun x => Real.sqrt n *
                  (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)
                - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x)
              = (fun x => Real.sqrt n *
                  (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x
                    - (1 / 2 : ℝ) * ⟪(Real.sqrt n)⁻¹ • h, ℓ x⟫ * M.sqrtDensity θ₀ x)) := by
      funext x
      have h_inner : (⟪(Real.sqrt n)⁻¹ • h, ℓ x⟫ : ℝ)
          = (Real.sqrt n)⁻¹ * (⟪h, ℓ x⟫ : ℝ) :=
        real_inner_smul_left h (ℓ x) _
      rw [h_inner]
      have h_t_inv_t : Real.sqrt n * (Real.sqrt n)⁻¹ = 1 := mul_inv_cancel₀ hsqrt_ne
      field_simp
    rw [h_eq]
    exact h_mem_n.const_mul (Real.sqrt n)
  -- `P₀ := μ.withDensity (ENNReal.ofReal ∘ p₀)`, a finite measure.
  set ρ : 𝓧 → ℝ≥0∞ := fun x => ENNReal.ofReal (M.density θ₀ x) with hρ_def
  have hρ_meas : Measurable ρ := (M.density_meas θ₀).ennreal_ofReal
  have hρ_lt_top : ∀ᵐ x ∂μ, ρ x < ∞ :=
    Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)
  have hρ_toReal : ∀ x, (ρ x).toReal = M.density θ₀ x := fun x => by
    rw [hρ_def]; exact ENNReal.toReal_ofReal (M.density_nonneg θ₀ x)
  set P₀ : Measure 𝓧 := μ.withDensity ρ with hP₀_def
  have hP₀_finite : IsFiniteMeasure P₀ := by
    refine ⟨?_⟩
    rw [hP₀_def, withDensity_apply ρ MeasurableSet.univ, Measure.restrict_univ]
    have : (∫⁻ x, ρ x ∂μ) = ENNReal.ofReal (∫ x, M.density θ₀ x ∂μ) := by
      rw [hρ_def, ← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (M.density_nonneg θ₀))]
    rw [this]; exact ENNReal.ofReal_lt_top
  -- `⟨h,ℓ⟩² ∈ L¹(P₀)`.
  have hsq_int_P₀ : Integrable (fun x => ⟪h, ℓ x⟫ ^ 2) P₀ := by
    rw [hP₀_def, integrable_withDensity_iff hρ_meas hρ_lt_top]
    refine hG_int.congr ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    simp only [hρ_toReal]
  -- Measurable singular sets.
  have hset : ∀ n : ℕ, MeasurableSet {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0} :=
    fun n => measurableSet_eq_fun (M.density_meas _) measurable_const
  -- Key identity: on `{p_n=0}`, `∫_{p_n=0} G dμ = ∫_{p_n=0} ⟨h,ℓ⟩² dP₀`.
  have hB_bridge : ∀ n : ℕ,
      ∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0}, ⟪h, ℓ x⟫ ^ 2 ∂P₀
        = ∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0},
            ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ := by
    intro n
    rw [hP₀_def,
      setIntegral_withDensity_eq_setIntegral_toReal_smul hρ_meas
        (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) _ (hset n)]
    refine MeasureTheory.setIntegral_congr_fun (hset n) (fun x _ => ?_)
    rw [hρ_toReal, smul_eq_mul, mul_comm]
  -- `mₙ := ∫_{p_n=0} p₀ dμ`.  `P₀({p_n=0}) = ENNReal.ofReal mₙ`.
  have hm_nonneg : ∀ n : ℕ,
      0 ≤ ∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0}, M.density θ₀ x ∂μ :=
    fun n => MeasureTheory.setIntegral_nonneg (hset n) (fun x _ => M.density_nonneg _ x)
  have hP₀_apply : ∀ n : ℕ,
      P₀ {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0}
        = ENNReal.ofReal
            (∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0}, M.density θ₀ x ∂μ) := by
    intro n
    rw [hP₀_def, withDensity_apply ρ (hset n), hρ_def,
      ← ofReal_integral_eq_lintegral_ofReal (hint.restrict)
        (ae_restrict_of_ae (Filter.Eventually.of_forall (M.density_nonneg θ₀)))]
  -- `n·mₙ ≤ 2·Rₙ + ½·Bₙ`  (`Bₙ = ∫_{p_n=0} G dμ`), eventually for `n ≥ 1`.
  have h_key : ∀ᶠ (n : ℕ) in atTop,
      (n : ℝ) * ∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0}, M.density θ₀ x ∂μ
        ≤ 2 * ∫ x,
            (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)
             - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
          + (1 / 2 : ℝ) * ∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0},
              ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ := by
    filter_upwards [hX_memLp_eventually, Filter.eventually_ge_atTop 1]
      with n hX_memLp_n hn_pos
    have hn_nat_pos : 0 < n := hn_pos
    have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_nat_pos
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos_real
    have hnsq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hn_pos_real)
    set s : Set 𝓧 := {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0} with hs_def
    -- `n·mₙ = ∫_s (√n(√p_n − √p₀))² dμ`.
    have h_nm_eq :
        (n : ℝ) * ∫ x in s, M.density θ₀ x ∂μ
          = ∫ x in s,
              (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x
                              - M.sqrtDensity θ₀ x)) ^ 2 ∂μ := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun (hset n) (fun x hx => ?_)
      have hx0 : M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0 := hx
      have hsqrtn0 : M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0 := by
        unfold ParametricFamily.sqrtDensity; rw [hx0, Real.sqrt_zero]
      have hp₀sq : M.sqrtDensity θ₀ x ^ 2 = M.density θ₀ x := M.sqrtDensity_sq θ₀ x
      rw [hsqrtn0]
      have : (Real.sqrt n * (0 - M.sqrtDensity θ₀ x)) ^ 2
          = (Real.sqrt n) ^ 2 * M.sqrtDensity θ₀ x ^ 2 := by ring
      rw [this, hnsq, hp₀sq]
    -- pointwise `(√n(√p_n−√p₀))² = (Xₙ + ½⟨h,ℓ⟩√p₀)² ≤ 2Xₙ² + 2(½⟨h,ℓ⟩√p₀)²`.
    have h_pt : ∀ x,
        (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)) ^ 2
          ≤ 2 * (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)
                  - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
            + 2 * ((1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 := by
      intro x
      set a : ℝ := Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x
                    - M.sqrtDensity θ₀ x)
                  - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x with ha_def
      set b : ℝ := (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x with hb_def
      have hsum : Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x
                    - M.sqrtDensity θ₀ x) = a + b := by rw [ha_def, hb_def]; ring
      rw [hsum]
      exact L2Utils.sq_add_le_two_mul_sq a b
    -- integrate the pointwise bound over `s`.
    have hX_sq_int := hX_memLp_n.integrable_sq
    -- `√n(√p_n−√p₀) ∈ L²`, hence its square is integrable.
    have hZ_memLp : MemLp (fun x => Real.sqrt n *
          (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)) 2 μ := by
      have h_sqrt_n := M.sqrtDensity_memLp_two μ (θ₀ + (Real.sqrt n)⁻¹ • h) (hint_perturb _ h)
      have h_sqrt_0 := M.sqrtDensity_memLp_two μ θ₀ hint
      exact (h_sqrt_n.sub h_sqrt_0).const_mul (Real.sqrt n)
    have hZ_sq_int := hZ_memLp.integrable_sq
    have h_rhs_int : Integrable (fun x =>
        2 * (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)
              - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
        + 2 * ((1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2) μ :=
      (hX_sq_int.const_mul 2).add (hYsq_int.const_mul 2)
    have h_int_mono :
        ∫ x in s,
            (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x
                            - M.sqrtDensity θ₀ x)) ^ 2 ∂μ
          ≤ ∫ x in s,
              (2 * (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x
                                    - M.sqrtDensity θ₀ x)
                    - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
               + 2 * ((1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2) ∂μ :=
      MeasureTheory.setIntegral_mono_on
        hZ_sq_int.integrableOn h_rhs_int.integrableOn (hset n)
        (fun x _ => by
          have := h_pt x; simpa using this)
    -- split the RHS integral and bound each piece by its full integral.
    have h_split :
        ∫ x in s,
            (2 * (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x
                                  - M.sqrtDensity θ₀ x)
                  - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
             + 2 * ((1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2) ∂μ
          = 2 * ∫ x in s,
              (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x
                              - M.sqrtDensity θ₀ x)
               - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
            + 2 * ∫ x in s,
              ((1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ := by
      rw [MeasureTheory.integral_add ((hX_sq_int.const_mul 2).integrableOn)
            ((hYsq_int.const_mul 2).integrableOn),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    -- `∫_s Xₙ² ≤ Rₙ`.
    have hX_le : ∫ x in s,
          (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)
           - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
        ≤ ∫ x,
          (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)
           - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ :=
      MeasureTheory.setIntegral_le_integral hX_sq_int
        (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    -- `∫_s (½⟨h,ℓ⟩√p₀)² = ¼·∫_s G dμ`.
    have hY_eq : ∫ x in s, ((1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
        = (1 / 4 : ℝ) * ∫ x in s, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ := by
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun (hset n) (fun x _ => ?_)
      have hsq : (M.sqrtDensity θ₀ x) ^ 2 = M.density θ₀ x := M.sqrtDensity_sq θ₀ x
      have : ((1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2
          = (1 / 4 : ℝ) * (⟪h, ℓ x⟫ ^ 2 * (M.sqrtDensity θ₀ x) ^ 2) := by ring
      rw [this, hsq]
    rw [h_nm_eq]
    calc
      ∫ x in s,
          (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x
                          - M.sqrtDensity θ₀ x)) ^ 2 ∂μ
        ≤ 2 * ∫ x in s,
              (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x
                              - M.sqrtDensity θ₀ x)
               - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
            + 2 * ∫ x in s,
              ((1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ := by
              rw [← h_split]; exact h_int_mono
      _ ≤ 2 * ∫ x,
              (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x
                              - M.sqrtDensity θ₀ x)
               - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
            + (1 / 2 : ℝ) * ∫ x in s, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ := by
              rw [hY_eq]
              have hrw : (2 : ℝ) * ((1 / 4 : ℝ) * ∫ x in s, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ)
                  = (1 / 2 : ℝ) * ∫ x in s, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ := by ring
              rw [hrw]
              have := hX_le
              linarith
  -- `Bₙ → 0`: absolute continuity of the integral against `P₀`.
  have hP₀_set_tendsto : Tendsto
      (fun n : ℕ => P₀ {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0}) atTop (𝓝 0) := by
    -- first `mₙ → 0` from `n·mₙ ≤ 2Rₙ + ½·I` (bounded), `Bₙ ≤ I`.
    have hI_nonneg : 0 ≤ ∫ x, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ :=
      MeasureTheory.integral_nonneg
        (fun x => mul_nonneg (sq_nonneg _) (M.density_nonneg _ x))
    -- `n·mₙ ≤ 2Rₙ + ½·I`, eventually.
    have h_nm_bound : ∀ᶠ (n : ℕ) in atTop,
        (n : ℝ) * ∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0}, M.density θ₀ x ∂μ
          ≤ 2 * ∫ x,
              (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)
               - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
            + (1 / 2 : ℝ) * ∫ x, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ := by
      filter_upwards [h_key] with n hkey
      have hG_le : ∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0},
            ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ
          ≤ ∫ x, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ :=
        MeasureTheory.setIntegral_le_integral hG_int
          (Filter.Eventually.of_forall
            (fun x => mul_nonneg (sq_nonneg _) (M.density_nonneg _ x)))
      linarith [hkey, hG_le]
    -- RHS of `h_nm_bound` is bounded (`Rₙ → 0`), so `n·mₙ` is `O(1)`; hence `mₙ → 0`.
    have h_rhs_tendsto : Tendsto
        (fun n : ℕ =>
          2 * ∫ x,
              (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)
               - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
            + (1 / 2 : ℝ) * ∫ x, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ)
        atTop (𝓝 ((1 / 2 : ℝ) * ∫ x, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ)) := by
      have h2R := hR.const_mul (2 : ℝ)
      simp only [mul_zero] at h2R
      have := h2R.add (tendsto_const_nhds
        (x := (1 / 2 : ℝ) * ∫ x, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ))
      simpa using this
    -- bound `n·mₙ ≤ C` eventually, so `mₙ ≤ C/n → 0`.  `C := L + 1` (the RHS limit).
    set C : ℝ := ((1 / 2 : ℝ) * ∫ x, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ) + 1 with hC_def
    have h_rhs_le_C : ∀ᶠ (n : ℕ) in atTop,
        2 * ∫ x,
            (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)
             - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
          + (1 / 2 : ℝ) * ∫ x, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ ≤ C := by
      have := h_rhs_tendsto
      rw [Metric.tendsto_atTop] at this
      obtain ⟨N, hN⟩ := this 1 (by norm_num)
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have := hN n hn
      rw [Real.dist_eq, abs_lt] at this
      rw [hC_def]; linarith [this.2]
    -- Extract a uniform upper bound on `n·mₙ`.
    have h_nm_le_C : ∀ᶠ (n : ℕ) in atTop,
        (n : ℝ) * ∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0}, M.density θ₀ x ∂μ
          ≤ C := by
      filter_upwards [h_nm_bound, h_rhs_le_C] with n hn hnC
      exact hn.trans hnC
    -- `mₙ → 0`.
    have hg0 : Tendsto (fun n : ℕ => max C 0 * (n : ℝ)⁻¹) atTop (𝓝 0) := by
      have h_inv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      have := h_inv.const_mul (max C 0)
      simpa using this
    have hm_tendsto : Tendsto
        (fun n : ℕ =>
          ∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0}, M.density θ₀ x ∂μ)
        atTop (𝓝 0) := by
      refine squeeze_zero' (Filter.Eventually.of_forall hm_nonneg) ?_ hg0
      -- `mₙ ≤ (max C 0)/n`.
      filter_upwards [h_nm_le_C, Filter.eventually_ge_atTop 1] with n hnC hn_pos
      have hn_pos_real : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (hn_pos : 1 ≤ n)
      have hnm_le : (n : ℝ) * ∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0},
            M.density θ₀ x ∂μ ≤ max C 0 := hnC.trans (le_max_left _ _)
      have hkey : (∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0}, M.density θ₀ x ∂μ)
          ≤ max C 0 / (n : ℝ) := by
        rw [le_div_iff₀ hn_pos_real]; linarith [hnm_le]
      rw [div_eq_mul_inv] at hkey
      exact hkey
    -- `P₀({p_n=0}) = ENNReal.ofReal mₙ → ENNReal.ofReal 0 = 0`.
    have hcomp := (ENNReal.continuous_ofReal.tendsto 0).comp hm_tendsto
    simp only [ENNReal.ofReal_zero] at hcomp
    refine hcomp.congr (fun n => ?_)
    rw [Function.comp_apply, hP₀_apply n]
  -- AC: `∫_{p_n=0} ⟨h,ℓ⟩² dP₀ → 0`.
  have hB_tendsto : Tendsto
      (fun n : ℕ =>
        ∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0}, ⟪h, ℓ x⟫ ^ 2 ∂P₀)
      atTop (𝓝 0) :=
    hsq_int_P₀.tendsto_setIntegral_nhds_zero hP₀_set_tendsto
  -- Hence `∫_{p_n=0} G dμ → 0` via the bridge.
  have hBμ_tendsto : Tendsto
      (fun n : ℕ =>
        ∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0},
          ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ)
      atTop (𝓝 0) := by
    refine hB_tendsto.congr (fun n => ?_)
    exact hB_bridge n
  -- Squeeze `0 ≤ n·mₙ ≤ 2Rₙ + ½·Bₙ → 0`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (b := atTop)
    (g := fun (_ : ℕ) => (0 : ℝ))
    (h := fun (n : ℕ) =>
      2 * ∫ x,
          (Real.sqrt n * (M.sqrtDensity (θ₀ + (Real.sqrt n)⁻¹ • h) x - M.sqrtDensity θ₀ x)
           - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
        + (1 / 2 : ℝ) * ∫ x in {x | M.density (θ₀ + (Real.sqrt n)⁻¹ • h) x = 0},
            ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ)
    tendsto_const_nhds ?_
    (Filter.Eventually.of_forall fun n =>
      mul_nonneg (Nat.cast_nonneg n) (hm_nonneg n))
    h_key
  · -- Upper envelope → 0.
    have h2R := hR.const_mul (2 : ℝ)
    simp only [mul_zero] at h2R
    have hhalfB := hBμ_tendsto.const_mul (1 / 2 : ℝ)
    simp only [mul_zero] at hhalfB
    have := h2R.add hhalfB
    simpa using this

end AsymptoticStatistics
