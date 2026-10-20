module
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import StatLean.AsymptoticStatistics.ForMathlib.Slutsky

@[expose] public section

/-!
# Slutsky–Fréchet shift bridge for `WeakConverges`

Given a sequence of probability measures `P k` on spaces `Ω k`, a statistic
`T k : Ω k → E`, and a real-valued scaling sequence `sqn k → ∞`, suppose the
"unshifted" pushforward
`(P k).map (fun ω => sqn k • (T k ω - ψ θ₀))`
weakly converges to a limit `ν`. If additionally `ψ : F → E` is Fréchet-
differentiable at `θ₀` with derivative `ψDot`, then the "shifted" pushforward
`(P k).map (fun ω => sqn k • (T k ω - ψ (θ₀ + (sqn k)⁻¹ • h)))`
weakly converges to the translated law `ν.map (· - ψDot h)`.

The mathematics is two-piece:

1. **Fréchet shift** — `sqn k • (ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀) → ψDot h`
   pointwise (deterministically), via `HasFDerivAt.isLittleO` composed along
   `k ↦ θ₀ + (sqn k)⁻¹ • h`.
2. **Slutsky** — the two random variables
   `X k ω := sqn k • (T k ω - ψ θ₀) - ψDot h` and
   `Y k ω := sqn k • (T k ω - ψ (θ₀ + (sqn k)⁻¹ • h))`
   differ by the deterministic null sequence in (1), so
   `WeakConverges.slutsky_of_tendstoInMeasure_dist` bridges from the law of
   `X` (≡ unshifted pushforward translated by `· - ψDot h`) to the law of `Y`
   (the shifted pushforward).

The theorem packages the Fréchet-shift form of Slutsky's theorem independently
of any particular consumer.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AsymptoticStatistics

/-- **Slutsky shift bridge from a pre-supplied null sequence.**

The Slutsky tail of `WeakConverges.slutsky_frechet_shift`, taking the
deterministic null sequence
`h_frechet_shift : sqn k • (ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀) - ψDot h →_k 0`
as a hypothesis rather than deriving it from a `HasFDerivAt`. This is the
per-direction interface: any `ψDot h` limit of the rescaled functional shift
(Fréchet, Gateaux, or otherwise) feeds Slutsky here, with no Fréchet
requirement and no continuity. `slutsky_frechet_shift` is the `HasFDerivAt`
wrapper of this lemma. -/
theorem WeakConverges.slutsky_shift_of_tendsto
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    {T : ∀ k, Ω k → E} (hT_meas : ∀ k, Measurable (T k))
    {ψ : F → E} {ψDot : F →L[ℝ] E} {θ₀ : F}
    {sqn : ℕ → ℝ} {h : F}
    (h_frechet_shift : Tendsto (fun k : ℕ =>
        sqn k • (ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀) - ψDot h) atTop (𝓝 0))
    {ν : Measure E} [IsProbabilityMeasure ν]
    (h_wc_unshifted : WeakConverges
      (fun k : ℕ => (P k).map (fun ω => sqn k • (T k ω - ψ θ₀))) ν) :
    WeakConverges
      (fun k : ℕ => (P k).map
        (fun ω => sqn k • (T k ω - ψ (θ₀ + (sqn k)⁻¹ • h))))
      (ν.map (fun y : E => y - ψDot h)) := by
  classical
  -- Step 1: push the unshifted weak conv through `y ↦ y - ψDot h` (continuous
  -- mapping theorem), yielding the "X-side" of Slutsky: laws of
  -- `sqn k • (T k ω - ψ θ₀) - ψDot h` converging to `ν.map (· - ψDot h)`.
  have hSub_cont : Continuous (fun y : E => y - ψDot h) := by fun_prop
  have hSub_meas : Measurable (fun y : E => y - ψDot h) := hSub_cont.measurable
  have h_T_meas_inner : ∀ k,
      Measurable (fun ω : Ω k => sqn k • (T k ω - ψ θ₀)) := fun k => by
    have := hT_meas k
    fun_prop
  have h_wc_shifted_X : WeakConverges
      (fun k : ℕ => (P k).map
        (fun ω => sqn k • (T k ω - ψ θ₀) - ψDot h))
      (ν.map (fun y : E => y - ψDot h)) := by
    have h_map := h_wc_unshifted.map hSub_cont hSub_meas
    have h_rewrite : ∀ k,
        ((P k).map (fun ω => sqn k • (T k ω - ψ θ₀))).map
            (fun y : E => y - ψDot h)
        = (P k).map (fun ω => sqn k • (T k ω - ψ θ₀) - ψDot h) := by
      intro k
      rw [Measure.map_map hSub_meas (h_T_meas_inner k)]
      rfl
    intro f
    have hf := h_map f
    have h_funext : (fun k : ℕ => ∫ x, f x
          ∂(((P k).map (fun ω => sqn k • (T k ω - ψ θ₀))).map
            (fun y : E => y - ψDot h)))
        = (fun k : ℕ => ∫ x, f x ∂((P k).map
            (fun ω => sqn k • (T k ω - ψ θ₀) - ψDot h))) :=
      funext fun k => by rw [h_rewrite k]
    rw [h_funext] at hf
    exact hf
  -- Step 2: Slutsky bridge. `X` and `Y` differ by the deterministic null
  -- sequence `sqn k • (ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀) - ψDot h → 0`.
  have hX_meas : ∀ k, AEMeasurable
      (fun ω => sqn k • (T k ω - ψ θ₀) - ψDot h) (P k) := by
    intro k
    have h1 : Measurable (T k) := hT_meas k
    fun_prop
  have hY_meas : ∀ k, AEMeasurable
      (fun ω => sqn k • (T k ω - ψ (θ₀ + (sqn k)⁻¹ • h))) (P k) := by
    intro k
    have h1 : Measurable (T k) := hT_meas k
    fun_prop
  have h_dist_eq : ∀ k ω,
      dist (sqn k • (T k ω - ψ θ₀) - ψDot h)
        (sqn k • (T k ω - ψ (θ₀ + (sqn k)⁻¹ • h)))
        = ‖sqn k • (ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀) - ψDot h‖ := by
    intro k ω
    rw [dist_eq_norm]
    congr 1
    simp only [smul_sub]
    abel
  have hDist : ∀ ε > 0,
      Tendsto (fun k => (P k).real
        {ω | ε ≤ dist (sqn k • (T k ω - ψ θ₀) - ψDot h)
          (sqn k • (T k ω - ψ (θ₀ + (sqn k)⁻¹ • h)))})
        atTop (𝓝 0) := by
    intro ε hε
    have h_norm_small : ∀ᶠ k in atTop,
        ‖sqn k • (ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀) - ψDot h‖ < ε := by
      have := h_frechet_shift.eventually (Metric.ball_mem_nhds (0 : E) hε)
      filter_upwards [this] with k hk
      simpa [Metric.mem_ball, dist_zero_right] using hk
    have h_set_empty : ∀ᶠ k in atTop,
        {ω | ε ≤ dist (sqn k • (T k ω - ψ θ₀) - ψDot h)
          (sqn k • (T k ω - ψ (θ₀ + (sqn k)⁻¹ • h)))}
          = (∅ : Set (Ω k)) := by
      filter_upwards [h_norm_small] with k hk
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      calc dist (sqn k • (T k ω - ψ θ₀) - ψDot h)
            (sqn k • (T k ω - ψ (θ₀ + (sqn k)⁻¹ • h)))
          = ‖sqn k • (ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀) - ψDot h‖ :=
            h_dist_eq k ω
        _ < ε := hk
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [h_set_empty] with k hk
    rw [hk]
    simp
  haveI : IsProbabilityMeasure (ν.map (fun y : E => y - ψDot h)) :=
    Measure.isProbabilityMeasure_map hSub_meas.aemeasurable
  exact WeakConverges.slutsky_of_tendstoInMeasure_dist
    (P := P)
    (X := fun k ω => sqn k • (T k ω - ψ θ₀) - ψDot h)
    (Y := fun k ω => sqn k • (T k ω - ψ (θ₀ + (sqn k)⁻¹ • h)))
    (ν := ν.map (fun y : E => y - ψDot h))
    hX_meas hY_meas h_wc_shifted_X hDist

/-- **Slutsky–Fréchet shift bridge.**

Given a statistic `T k : Ω k → E` whose unshifted, `sqn k`-scaled pushforward
under `P k` weakly converges to `ν`, and a functional `ψ : F → E` Fréchet-
differentiable at `θ₀` with derivative `ψDot`, the shifted pushforward
(centered at `ψ (θ₀ + (sqn k)⁻¹ • h)` rather than `ψ θ₀`) weakly converges to
the translated law `ν.map (· - ψDot h)`.

The bridge is Slutsky's theorem applied to the deterministic null sequence
`sqn k • (ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀) - ψDot h →_k 0` coming from
`hψ_diff`. Thin `HasFDerivAt` wrapper of
`WeakConverges.slutsky_shift_of_tendsto`: it derives the null sequence from
`hψ_diff` and forwards to the per-direction sibling. -/
theorem WeakConverges.slutsky_frechet_shift
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {P : ∀ k, Measure (Ω k)} [∀ k, IsProbabilityMeasure (P k)]
    {T : ∀ k, Ω k → E} (hT_meas : ∀ k, Measurable (T k))
    {ψ : F → E} {ψDot : F →L[ℝ] E} {θ₀ : F} (hψ_diff : HasFDerivAt ψ ψDot θ₀)
    {sqn : ℕ → ℝ} (h_sqn_atTop : Tendsto sqn atTop atTop)
    {h : F}
    {ν : Measure E} [IsProbabilityMeasure ν]
    (h_wc_unshifted : WeakConverges
      (fun k : ℕ => (P k).map (fun ω => sqn k • (T k ω - ψ θ₀))) ν) :
    WeakConverges
      (fun k : ℕ => (P k).map
        (fun ω => sqn k • (T k ω - ψ (θ₀ + (sqn k)⁻¹ • h))))
      (ν.map (fun y : E => y - ψDot h)) := by
  classical
  -- The Fréchet-perturbation sequence `(sqn k)⁻¹ • h` tends to `0`.
  have h_sqn_pos_event : ∀ᶠ k in atTop, 0 < sqn k :=
    h_sqn_atTop.eventually (eventually_gt_atTop 0)
  have h_sqn_inv_to_zero : Tendsto (fun k : ℕ => (sqn k)⁻¹) atTop (𝓝 0) :=
    h_sqn_atTop.inv_tendsto_atTop
  have h_pt_to_θ₀ : Tendsto (fun k : ℕ => θ₀ + (sqn k)⁻¹ • h) atTop (𝓝 θ₀) := by
    have hh : Tendsto (fun k : ℕ => (sqn k)⁻¹ • h) atTop (𝓝 0) := by
      simpa using h_sqn_inv_to_zero.smul_const h
    simpa using tendsto_const_nhds.add hh
  -- Fréchet `=o[𝓝 θ₀]` form composed along `k ↦ θ₀ + h/sqn k`.
  have h_little_o := hψ_diff.isLittleO
  have h_little_o_comp : (fun k : ℕ =>
        ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀ - ψDot ((sqn k)⁻¹ • h))
        =o[atTop] (fun k : ℕ => (sqn k)⁻¹ • h) := by
    have h_comp := h_little_o.comp_tendsto h_pt_to_θ₀
    have h_lhs_eq : (fun x' => ψ x' - ψ θ₀ - ψDot (x' - θ₀)) ∘
        (fun k : ℕ => θ₀ + (sqn k)⁻¹ • h)
        = (fun k : ℕ =>
          ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀ - ψDot ((sqn k)⁻¹ • h)) := by
      funext k
      simp [add_sub_cancel_left]
    have h_rhs_eq : (fun x' => x' - θ₀) ∘
        (fun k : ℕ => θ₀ + (sqn k)⁻¹ • h)
        = (fun k : ℕ => (sqn k)⁻¹ • h) := by
      funext k
      simp [add_sub_cancel_left]
    rw [h_lhs_eq, h_rhs_eq] at h_comp
    exact h_comp
  -- The Fréchet shift `sqn k • (ψ (θ₀ + h/sqn k) - ψ θ₀) → ψDot h` is the
  -- deterministic null sequence we feed the per-direction sibling.
  have h_frechet_shift : Tendsto (fun k : ℕ =>
      sqn k • (ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀) - ψDot h)
    atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    set c : ℝ := ε / (‖h‖ + 1) with hc_def
    have hc_pos : 0 < c := by
      have : 0 < ‖h‖ + 1 := by positivity
      positivity
    have hc_bound : c * ‖h‖ < ε := by
      have hh1 : 0 < ‖h‖ + 1 := by positivity
      have := mul_lt_mul_of_pos_left
        (show ‖h‖ < ‖h‖ + 1 by linarith [norm_nonneg h]) hc_pos
      calc c * ‖h‖
          < c * (‖h‖ + 1) := this
        _ = ε := by rw [hc_def, div_mul_cancel₀ _ hh1.ne']
    have h_eventually : ∀ᶠ k in atTop,
        ‖ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀ - ψDot ((sqn k)⁻¹ • h)‖
          ≤ c * ‖(sqn k)⁻¹ • h‖ := by
      have := h_little_o_comp.def hc_pos
      simpa using this
    filter_upwards [h_eventually, h_sqn_pos_event] with k h_bound h_sqn_pos
    have h_ψDot_smul : ψDot ((sqn k)⁻¹ • h) = (sqn k)⁻¹ • ψDot h := by
      simp
    have h_norm_smul : ‖(sqn k)⁻¹ • h‖ = (sqn k)⁻¹ * ‖h‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h_sqn_pos)]
    have h_smul_factor :
        sqn k • (ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀) - ψDot h
          = sqn k •
            (ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀ - (sqn k)⁻¹ • ψDot h) := by
      rw [smul_sub (sqn k) (ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀)
        ((sqn k)⁻¹ • ψDot h), smul_inv_smul₀ h_sqn_pos.ne']
    have h_dist_eq :
        dist (sqn k • (ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀) - ψDot h) 0
          = sqn k * ‖ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀
              - ψDot ((sqn k)⁻¹ • h)‖ := by
      rw [dist_zero_right, h_smul_factor, norm_smul, Real.norm_eq_abs,
        abs_of_pos h_sqn_pos, h_ψDot_smul]
    rw [h_dist_eq]
    calc sqn k * ‖ψ (θ₀ + (sqn k)⁻¹ • h) - ψ θ₀
              - ψDot ((sqn k)⁻¹ • h)‖
        ≤ sqn k * (c * ‖(sqn k)⁻¹ • h‖) :=
          mul_le_mul_of_nonneg_left h_bound h_sqn_pos.le
      _ = sqn k * (c * ((sqn k)⁻¹ * ‖h‖)) := by rw [h_norm_smul]
      _ = (sqn k * (sqn k)⁻¹) * (c * ‖h‖) := by ring
      _ = 1 * (c * ‖h‖) := by rw [mul_inv_cancel₀ h_sqn_pos.ne']
      _ = c * ‖h‖ := one_mul _
      _ < ε := hc_bound
  exact WeakConverges.slutsky_shift_of_tendsto hT_meas h_frechet_shift
    h_wc_unshifted

end AsymptoticStatistics
