module
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorNarrow
public import StatLean.AsymptoticStatistics.ForMathlib.HellingerIntegralBound
public import StatLean.AsymptoticStatistics.ForMathlib.Slutsky

@[expose] public section

/-!
# Reverse direction of the narrow/broad regularity equivalence

The non-trivial direction of `IsRegularEstimator_narrow ⟺ IsRegularEstimator`:

  `IsRegularEstimator_narrow P T_set ψ hψ hEIF T_n L`
   ⟹ `IsRegularEstimator P T_set ψ hψ hEIF T_n L` (restricted to natural QMDPaths)

Under a dominator-scope restriction (both the chosen family and the arbitrary
realising `QMDPath` `γ` have `dominating := P`), narrow regularity implies broad
regularity. Reference: vdV §25.3.2 (paragraph preceding Theorem 25.20) — Hájek-style
regularity at a chosen submodel transfers to any same-score submodel.

Headline declarations: `isRegularEstimator_of_narrow_explicit` and its packaged
wrapper `isRegularEstimator_of_narrow`.

## Proof structure

Let `γ` (arbitrary) and `γ₀ := chosenFamily g hg` both have score `g` and
dominator `P`. Goal: weak convergence of the `γ`-perturbed rescaled estimator
to `L`. Per test function `f ∈ BCF`:

* (A) `|∫ (f ∘ Fγ) d((γ.curve(t_n))^n) - ∫ (f ∘ Fγ) d((γ₀.curve(t_n))^n)| → 0`
  by `hellinger_locality_for_qmdpath_same_score` + the wrapper
  `ForMathlib.HellingerIntegralBound.integral_test_diff_tendsto_zero`.
* (B) `|∫ (f ∘ Fγ) d((γ₀.curve(t_n))^n) - ∫ (f ∘ Fγ₀) d((γ₀.curve(t_n))^n)| → 0`
  via ψ-shift Slutsky (deterministic shift → 0 by `hψ.derivative_spec`).
* (C) `∫ (f ∘ Fγ₀) d((γ₀.curve(t_n))^n) → ∫ f dL` from `h_chosen_regular`.

Triangle inequality assembles (A) + (B) + (C).
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal MeasureTheory

namespace AsymptoticStatistics.LowerBounds.RegularEstimator

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Reverse direction of the narrow/broad equivalence (explicit chosen-family form).**

Under a dominator-scope restriction (both the chosen family and the arbitrary
realising `QMDPath` have `dominating := P`), narrow regularity implies broad
regularity.

### Hypotheses

* `chosenFamily g hg`: a `QMDPath P` realising score `g` for each
  `g ∈ tangentSpace T_set`.
* `h_chosen_dom`: every chosen-family entry has `dominating := P`.
* `h_chosen_score`: scores match.
* `h_chosen_regular`: the weak convergence holds along the chosen family.
* `hT_meas`: the estimator sequence is measurable.

### Conclusion

For every realising `γ : QMDPath P` with `dominating := P`, the rescaled
estimator computed along `γ` and recentered at the perturbed truth converges
weakly to `L`.

Reference: vdV §25.3.2 (paragraph preceding Theorem 25.20) — Hájek-style
regularity at a chosen submodel transfers to any same-score submodel because
Hellinger LAN-locality implies TV-zero between the corresponding product
measures, and TV-zero implies bounded-functional-integral equality (and hence
weak-limit equality). -/
theorem isRegularEstimator_of_narrow_explicit
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T_set : TangentSpec P}
    {ψ : Measure Ω → ℝ}
    {IF_eff : ↥(L2ZeroMean P)}
    {hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ}
    {_hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff}
    {T_n : ∀ n, (Fin n → Ω) → ℝ}
    {L : Measure ℝ} [IsProbabilityMeasure L]
    (chosenFamily : ∀ (g : ↥(L2ZeroMean P)),
        (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier → QMDPath P)
    (h_chosen_dom : ∀ (g : ↥(L2ZeroMean P))
        (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier),
        (chosenFamily g hg).dominating = P)
    (h_chosen_score : ∀ (g : ↥(L2ZeroMean P))
        (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier),
        (chosenFamily g hg).score = g)
    (h_chosen_regular : ∀ (g : ↥(L2ZeroMean P))
        (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier),
        WeakConverges
          (fun n : ℕ =>
            (MeasureTheory.Measure.pi
                (fun _ : Fin n => (chosenFamily g hg).curve ((Real.sqrt n)⁻¹))).map
              (fun X : Fin n → Ω =>
                Real.sqrt n *
                  (T_n n X - ψ ((chosenFamily g hg).curve ((Real.sqrt n)⁻¹)))))
          L)
    (hT_meas : ∀ n, Measurable (T_n n))
    (g : ↥(L2ZeroMean P))
    (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier)
    (γ : QMDPath P)
    (hscore : γ.score = g)
    (h_dom_γ : γ.dominating = P) :
    WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi
            (fun _ : Fin n => γ.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n * (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹)))))
      L := by
  classical
  have hg_cl : (g : ↥(L2ZeroMean P)) ∈ tangentSpace T_set :=
    span_carrier_le_tangentSpace _ hg
  set γ₀ : QMDPath P := chosenFamily g hg with hγ₀_def
  have h_γ₀_dom : γ₀.dominating = P := h_chosen_dom g hg
  have h_γ₀_score : γ₀.score = g := h_chosen_score g hg
  have h_dom_eq : γ.dominating = γ₀.dominating := h_dom_γ.trans h_γ₀_dom.symm
  have h_score_eq : γ.score = γ₀.score := hscore.trans h_γ₀_score.symm
  set t : ℕ → ℝ := fun n => (Real.sqrt n)⁻¹ with ht_def
  set Pn : ∀ n : ℕ, Measure (Fin n → Ω) :=
    fun n => MeasureTheory.Measure.pi (fun _ : Fin n => γ.curve (t n)) with hPn_def
  set Pn₀ : ∀ n : ℕ, Measure (Fin n → Ω) :=
    fun n => MeasureTheory.Measure.pi (fun _ : Fin n => γ₀.curve (t n)) with hPn₀_def
  haveI hPn_prob : ∀ n, IsProbabilityMeasure (Pn n) := by
    intro n
    haveI : ∀ _ : Fin n, IsProbabilityMeasure (γ.curve (t n)) := fun _ =>
      γ.curve_isProbability _
    rw [hPn_def]; infer_instance
  haveI hPn₀_prob : ∀ n, IsProbabilityMeasure (Pn₀ n) := by
    intro n
    haveI : ∀ _ : Fin n, IsProbabilityMeasure (γ₀.curve (t n)) := fun _ =>
      γ₀.curve_isProbability _
    rw [hPn₀_def]; infer_instance
  set Fγ : ∀ n, (Fin n → Ω) → ℝ :=
    fun n X => Real.sqrt n * (T_n n X - ψ (γ.curve (t n))) with hFγ_def
  set Fγ₀ : ∀ n, (Fin n → Ω) → ℝ :=
    fun n X => Real.sqrt n * (T_n n X - ψ (γ₀.curve (t n))) with hFγ₀_def
  have hFγ_meas : ∀ n, Measurable (Fγ n) := fun n =>
    (Measurable.const_mul ((hT_meas n).sub measurable_const) _)
  have hFγ₀_meas : ∀ n, Measurable (Fγ₀ n) := fun n =>
    (Measurable.const_mul ((hT_meas n).sub measurable_const) _)
  -- Step (C): weak conv along γ₀ (chosen family).
  have h_C : WeakConverges (fun n => (Pn₀ n).map (Fγ₀ n)) L := by
    have := h_chosen_regular g hg
    simpa [hPn₀_def, hFγ₀_def, ht_def, hγ₀_def] using this
  -- Step (B): ψ-shift via PathwiseDifferentiableAt — same score ⟹ same derivative.
  have h_inv_to_zero : Tendsto t atTop (𝓝 0) := by
    have h_sqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa [ht_def] using! h_sqrt.inv_tendsto_atTop
  have h_inv_ne : ∀ᶠ n : ℕ in atTop, t n ≠ 0 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hpos : (0 : ℝ) < Real.sqrt n :=
      Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le one_pos hn))
    exact inv_ne_zero hpos.ne'
  have h_inv_punctured : Tendsto t atTop (nhdsWithin 0 {0}ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h_inv_to_zero, h_inv_ne.mono fun n hn => hn⟩
  have h_γ_score_in : (γ.score : ↥(L2ZeroMean P)) ∈ tangentSpace T_set := by
    rw [hscore]; exact hg_cl
  have h_γ₀_score_in : (γ₀.score : ↥(L2ZeroMean P)) ∈ tangentSpace T_set := by
    rw [h_γ₀_score]; exact hg_cl
  have h_diff_γ : Tendsto (fun s : ℝ => (ψ (γ.curve s) - ψ P) / s)
      (nhdsWithin 0 {0}ᶜ)
      (𝓝 (hψ.derivative ⟨(γ.score : ↥(L2ZeroMean P)), h_γ_score_in⟩)) :=
    hψ.derivative_spec γ h_γ_score_in
  have h_diff_γ₀ : Tendsto (fun s : ℝ => (ψ (γ₀.curve s) - ψ P) / s)
      (nhdsWithin 0 {0}ᶜ)
      (𝓝 (hψ.derivative ⟨(γ₀.score : ↥(L2ZeroMean P)), h_γ₀_score_in⟩)) :=
    hψ.derivative_spec γ₀ h_γ₀_score_in
  have h_deriv_eq :
      hψ.derivative ⟨(γ.score : ↥(L2ZeroMean P)), h_γ_score_in⟩
        = hψ.derivative ⟨(γ₀.score : ↥(L2ZeroMean P)), h_γ₀_score_in⟩ := by
    congr 1
    apply Subtype.ext
    simp [hscore, h_γ₀_score]
  have h_psi_diff_zero :
      Tendsto (fun s : ℝ =>
          (ψ (γ.curve s) - ψ P) / s - (ψ (γ₀.curve s) - ψ P) / s)
        (nhdsWithin 0 {0}ᶜ) (𝓝 0) := by
    have h_sub := h_diff_γ.sub h_diff_γ₀
    rw [h_deriv_eq] at h_sub
    simpa using h_sub
  -- The shift `√n · (ψ(γ.curve(t_n)) - ψ(γ₀.curve(t_n))) → 0`.
  have h_shift_to_zero' :
      Tendsto (fun n : ℕ => Real.sqrt n *
          (ψ (γ.curve (t n)) - ψ (γ₀.curve (t n))))
        atTop (𝓝 0) := by
    -- Step: rewrite (ψ_γ - ψ_P)/s - (ψ_γ₀ - ψ_P)/s = (ψ_γ - ψ_γ₀)/s, then compose
    -- with t n → 0 punctured, and rewrite /t n = √n · ...
    have h_psi_diff_zero' :
        Tendsto (fun s : ℝ => (ψ (γ.curve s) - ψ (γ₀.curve s)) / s)
          (nhdsWithin 0 {0}ᶜ) (𝓝 0) := by
      apply h_psi_diff_zero.congr'
      have h_self_ne : {x : ℝ | x ≠ 0} ∈ nhdsWithin (0 : ℝ) {0}ᶜ :=
        self_mem_nhdsWithin
      filter_upwards [h_self_ne] with s hs
      have hs_ne : s ≠ 0 := hs
      -- Goal after `congr'`: show old form = new form on filter.
      change (ψ (γ.curve s) - ψ P) / s - (ψ (γ₀.curve s) - ψ P) / s
           = (ψ (γ.curve s) - ψ (γ₀.curve s)) / s
      field_simp
      ring
    have h_shift_to_zero :
        Tendsto (fun n : ℕ => (ψ (γ.curve (t n)) - ψ (γ₀.curve (t n))) / t n)
          atTop (𝓝 0) :=
      h_psi_diff_zero'.comp h_inv_punctured
    apply h_shift_to_zero.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hpos : (0 : ℝ) < Real.sqrt n :=
      Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le one_pos hn))
    have h_t_eq : t n = (Real.sqrt n)⁻¹ := rfl
    rw [h_t_eq]
    field_simp
  -- Pointwise distance dist(Fγ₀ n X, Fγ n X) is constant in X, equal to
  -- |√n (ψ(γ.curve(t_n)) - ψ(γ₀.curve(t_n)))| (which → 0).
  have h_dist_const : ∀ n (X : Fin n → Ω),
      dist (Fγ₀ n X) (Fγ n X)
        = |Real.sqrt n * (ψ (γ.curve (t n)) - ψ (γ₀.curve (t n)))| := by
    intro n X
    rw [Real.dist_eq]
    have h_diff_eq : Fγ₀ n X - Fγ n X
        = Real.sqrt n * (ψ (γ.curve (t n)) - ψ (γ₀.curve (t n))) := by
      simp only [hFγ_def, hFγ₀_def]
      ring
    rw [h_diff_eq]
  have h_dist_to_zero : ∀ ε > 0,
      Tendsto (fun n : ℕ =>
          (Pn₀ n).real {ω : Fin n → Ω | ε ≤ dist (Fγ₀ n ω) (Fγ n ω)})
        atTop (𝓝 0) := by
    intro ε hε
    have h_close : Tendsto (fun n : ℕ =>
        |Real.sqrt n * (ψ (γ.curve (t n)) - ψ (γ₀.curve (t n)))|) atTop (𝓝 0) := by
      have h := (continuous_abs.tendsto _).comp h_shift_to_zero'
      simp only [Function.comp_def] at h
      simpa [abs_zero] using h
    have hev : ∀ᶠ n : ℕ in atTop,
        |Real.sqrt n * (ψ (γ.curve (t n)) - ψ (γ₀.curve (t n)))| < ε := by
      have := (Metric.tendsto_nhds.mp h_close) ε hε
      filter_upwards [this] with n hn
      rwa [Real.dist_eq, sub_zero, abs_abs] at hn
    have h_eventually_empty :
        ∀ᶠ n : ℕ in atTop,
          {ω : Fin n → Ω | ε ≤ dist (Fγ₀ n ω) (Fγ n ω)} = (∅ : Set _) := by
      filter_upwards [hev] with n hn
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      rw [h_dist_const]
      exact hn
    have h_real_zero :
        ∀ᶠ n : ℕ in atTop,
          (Pn₀ n).real {ω : Fin n → Ω | ε ≤ dist (Fγ₀ n ω) (Fγ n ω)} = 0 := by
      filter_upwards [h_eventually_empty] with n hn
      rw [hn]; simp
    exact (tendsto_congr' h_real_zero).mpr tendsto_const_nhds
  -- Step (B): Slutsky-by-distance, common Pn₀ base.
  have h_B : WeakConverges (fun n => (Pn₀ n).map (Fγ n)) L :=
    AsymptoticStatistics.WeakConverges.slutsky_of_tendstoInMeasure_dist
      (X := Fγ₀) (Y := Fγ)
      (hX_meas := fun n => (hFγ₀_meas n).aemeasurable)
      (hY_meas := fun n => (hFγ_meas n).aemeasurable)
      (hX := h_C)
      (hDist := h_dist_to_zero)
  -- Step (A): Hellinger-LAN locality + integral-bound wrapper.
  have h_hellinger :
      Tendsto
        (fun n : ℕ =>
          (eLpNorm
            (fun X : Fin n → Ω =>
              Real.sqrt
                (∏ j, (γ.curve (t n)).rnDeriv γ.dominating (X j)).toReal
              - Real.sqrt
                (∏ j, (γ₀.curve (t n)).rnDeriv γ₀.dominating (X j)).toReal)
            2 (Measure.pi (fun _ : Fin n => γ.dominating))).toReal)
        atTop (𝓝 (0 : ℝ)) :=
    hellinger_locality_for_qmdpath_same_score P γ γ₀ h_dom_eq h_score_eq
  -- Recast h_hellinger to dominator `P` on both sides.
  have h_hellinger_P :
      Tendsto
        (fun n : ℕ =>
          (eLpNorm
            (fun X : Fin n → Ω =>
              Real.sqrt (∏ j, (γ.curve (t n)).rnDeriv P (X j)).toReal
              - Real.sqrt (∏ j, (γ₀.curve (t n)).rnDeriv P (X j)).toReal)
            2 (Measure.pi (fun _ : Fin n => P))).toReal)
        atTop (𝓝 (0 : ℝ)) := by
    have h_eq : (fun n : ℕ =>
          (eLpNorm
            (fun X : Fin n → Ω =>
              Real.sqrt
                (∏ j, (γ.curve (t n)).rnDeriv γ.dominating (X j)).toReal
              - Real.sqrt
                (∏ j, (γ₀.curve (t n)).rnDeriv γ₀.dominating (X j)).toReal)
            2 (Measure.pi (fun _ : Fin n => γ.dominating))).toReal)
        = (fun n : ℕ =>
          (eLpNorm
            (fun X : Fin n → Ω =>
              Real.sqrt (∏ j, (γ.curve (t n)).rnDeriv P (X j)).toReal
              - Real.sqrt (∏ j, (γ₀.curve (t n)).rnDeriv P (X j)).toReal)
            2 (Measure.pi (fun _ : Fin n => P))).toReal) := by
      funext n; rw [h_dom_γ, h_γ₀_dom]
    rw [← h_eq]; exact h_hellinger
  -- Apply `integral_test_diff_tendsto_zero`.
  have h_γ_dom_P : ∀ n, γ.curve (t n) ≪ P := fun n => by
    have := γ.curve_absContinuous (t n); rwa [h_dom_γ] at this
  have h_γ₀_dom_P : ∀ n, γ₀.curve (t n) ≪ P := fun n => by
    have := γ₀.curve_absContinuous (t n); rwa [h_γ₀_dom] at this
  haveI : ∀ n, IsProbabilityMeasure (γ.curve (t n)) := fun n => γ.curve_isProbability _
  haveI : ∀ n, IsProbabilityMeasure (γ₀.curve (t n)) := fun n => γ₀.curve_isProbability _
  intro f
  have h_push_eq_γ : ∀ n,
      ∫ y, f y ∂((Pn n).map (Fγ n)) = ∫ X, f (Fγ n X) ∂(Pn n) := fun n =>
    integral_map (hFγ_meas n).aemeasurable f.continuous.aestronglyMeasurable
  have h_push_eq_γ₀ : ∀ n,
      ∫ y, f y ∂((Pn₀ n).map (Fγ n)) = ∫ X, f (Fγ n X) ∂(Pn₀ n) := fun n =>
    integral_map (hFγ_meas n).aemeasurable f.continuous.aestronglyMeasurable
  have h_diff_to_zero :
      Tendsto (fun n => |∫ X, f (Fγ n X) ∂(Pn n) - ∫ X, f (Fγ n X) ∂(Pn₀ n)|)
        atTop (𝓝 0) := by
    have :=
      AsymptoticStatistics.ForMathlib.HellingerIntegralBound.integral_test_diff_tendsto_zero
        (ξ := P)
        (μ := fun n => γ.curve (t n)) (ν := fun n => γ₀.curve (t n))
        h_γ_dom_P h_γ₀_dom_P
        (F := Fγ) (fun n => hFγ_meas n) f h_hellinger_P
    simpa [hPn_def, hPn₀_def] using this
  -- Combine (B) + (A) via triangle inequality.
  have h_B_int : Tendsto (fun n => ∫ y, f y ∂((Pn₀ n).map (Fγ n))) atTop
      (𝓝 (∫ y, f y ∂L)) := h_B f
  have h_eq_γ : (fun n => ∫ y, f y ∂((Pn n).map (Fγ n)))
      = fun n => ∫ X, f (Fγ n X) ∂(Pn n) := by funext n; exact h_push_eq_γ n
  have h_eq_γ₀ : (fun n => ∫ y, f y ∂((Pn₀ n).map (Fγ n)))
      = fun n => ∫ X, f (Fγ n X) ∂(Pn₀ n) := by funext n; exact h_push_eq_γ₀ n
  rw [h_eq_γ]
  rw [h_eq_γ₀] at h_B_int
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε₂ : 0 < ε / 2 := by positivity
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp h_diff_to_zero) (ε / 2) hε₂
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp h_B_int) (ε / 2) hε₂
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  have hA := hN₁ n hn₁
  have hC := hN₂ n hn₂
  rw [Real.dist_eq, sub_zero, abs_abs] at hA
  rw [Real.dist_eq] at hC
  rw [Real.dist_eq]
  have h_triangle : |∫ X, f (Fγ n X) ∂(Pn n) - ∫ y, f y ∂L|
      ≤ |∫ X, f (Fγ n X) ∂(Pn n) - ∫ X, f (Fγ n X) ∂(Pn₀ n)|
          + |∫ X, f (Fγ n X) ∂(Pn₀ n) - ∫ y, f y ∂L| := by
    have h_split : ∫ X, f (Fγ n X) ∂(Pn n) - ∫ y, f y ∂L
        = (∫ X, f (Fγ n X) ∂(Pn n) - ∫ X, f (Fγ n X) ∂(Pn₀ n))
            + (∫ X, f (Fγ n X) ∂(Pn₀ n) - ∫ y, f y ∂L) := by ring
    rw [h_split]
    exact abs_add_le _ _
  linarith [h_triangle]

/-- **Reverse direction (packaged form).**

Wrapper that takes `h_narrow : IsRegularEstimator_narrow ...` and produces broad
regularity, under the dominator-scope restriction. -/
theorem isRegularEstimator_of_narrow
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T_set : TangentSpec P}
    {ψ : Measure Ω → ℝ}
    {IF_eff : ↥(L2ZeroMean P)}
    {hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ}
    {hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff}
    {T_n : ∀ n, (Fin n → Ω) → ℝ}
    {L : Measure ℝ} [IsProbabilityMeasure L]
    (h_narrow : IsRegularEstimator_narrow P T_set ψ hψ hEIF T_n L)
    (h_chosen_dom : ∀ (g : ↥(L2ZeroMean P))
        (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier),
        ((Classical.choose h_narrow) g hg).dominating = P)
    (hT_meas : ∀ n, Measurable (T_n n))
    (g : ↥(L2ZeroMean P))
    (hg : (g : ↥(L2ZeroMean P)) ∈ Submodule.span ℝ T_set.carrier)
    (γ : QMDPath P)
    (hscore : γ.score = g)
    (h_dom_γ : γ.dominating = P) :
    WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi
            (fun _ : Fin n => γ.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω =>
            Real.sqrt n * (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹)))))
      L := by
  obtain ⟨h_score, h_regular⟩ := Classical.choose_spec h_narrow
  exact isRegularEstimator_of_narrow_explicit
    (IF_eff := IF_eff) (hψ := hψ) (_hEIF := hEIF)
    (chosenFamily := Classical.choose h_narrow)
    h_chosen_dom h_score h_regular hT_meas g hg γ hscore h_dom_γ

end AsymptoticStatistics.LowerBounds.RegularEstimator
