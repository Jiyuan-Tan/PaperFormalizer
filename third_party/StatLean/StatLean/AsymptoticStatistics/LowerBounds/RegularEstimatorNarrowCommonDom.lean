module
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorNarrow

@[expose] public section

/-!
# Common-dominator generalization of QMDPath Hellinger locality

The reverse direction `IsRegularEstimator_narrow ⟹ IsRegularEstimator` in
`RegularEstimatorNarrowReverse` is, as originally proved, restricted to realising
paths with `dominating = P`, because `hellinger_locality_for_qmdpath_same_score`
carries an **equal-dominator** hypothesis `γ₁.dominating = γ₂.dominating`.

This file removes that restriction. Two `QMDPath`s `γ₁, γ₂` at the same `P` pass
through the *same* `P` at `t = 0`, with `P ≪ γᵢ.dominating`; picking any common
dominator `ξ` (e.g. `γ₁.dominating + γ₂.dominating`), the per-sample squared
Hellinger residual is **dominator-invariant** in `L²`-norm:

```
‖√(dμ/dξ) − √(dP/dξ) − (t/2)·g·√(dP/dξ)‖_{L²(ξ)} = ‖ same w.r.t. ν ‖_{L²(ν)}
```

for `μ ≪ ν ≪ ξ`, because the `ξ`-residual factors as `√(dν/dξ)·(ν-residual)`
and the weighting `√(dν/dξ)` is exactly the change-of-variables Jacobian
(`∫ f·(dν/dξ) dξ = ∫ f dν`). The linear terms cancel as before because both
expansions are anchored at the **common** `√(dP/dξ)`.

Headline declarations:

* `eLpNorm_sqrt_rnDeriv_mul_eq` — the weighted-`L²` change-of-dominator identity.
* `hellinger_locality_for_qmdpath_same_score_common_dom` — the locality lemma with
  the equal-dominator hypothesis replaced by a common dominator `ξ`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal MeasureTheory

namespace AsymptoticStatistics.LowerBounds.RegularEstimator

open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Change of dominator for a weighted `L²` seminorm.**

For `ν ≪ ξ` (both σ-finite) and any measurable `h : Ω → ℝ`,

```
‖ √(dν/dξ) · h ‖_{L²(ξ)} = ‖ h ‖_{L²(ν)} .
```

This is the `L²`-form of the change-of-variables `∫ f · (dν/dξ) dξ = ∫ f dν`
(`lintegral_rnDeriv_mul`): the weighting `√(dν/dξ)` squares to the
Radon–Nikodym derivative `dν/dξ`, which converts the `ξ`-integral of `‖h‖²` into
the `ν`-integral. -/
lemma eLpNorm_sqrt_rnDeriv_mul_eq
    {ν ξ : Measure Ω} [SigmaFinite ν] [SigmaFinite ξ]
    (hνξ : ν ≪ ξ) {h : Ω → ℝ} (hh : Measurable h) :
    eLpNorm (fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal * h ω) 2 ξ
      = eLpNorm h 2 ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  congr 1
  -- Reduce to the lintegral equality (then apply `lintegral_rnDeriv_mul`).
  -- a.e.-ξ rewrite of the LHS integrand to `(ν.rnDeriv ξ ω) * ‖h ω‖ₑ ^ 2`.
  have h_ae : (fun ω => ‖Real.sqrt (ν.rnDeriv ξ ω).toReal * h ω‖ₑ ^ (2 : ℝ))
      =ᵐ[ξ] (fun ω => ν.rnDeriv ξ ω * ‖h ω‖ₑ ^ (2 : ℝ)) := by
    filter_upwards [Measure.rnDeriv_lt_top ν ξ] with ω hω_lt
    have hω_ne : ν.rnDeriv ξ ω ≠ ⊤ := hω_lt.ne
    have hr_nn : (0 : ℝ) ≤ (ν.rnDeriv ξ ω).toReal := ENNReal.toReal_nonneg
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    -- ‖√(dν/dξ).toReal‖ₑ ^ 2 = ν.rnDeriv ξ ω.
    rw [Real.enorm_of_nonneg (Real.sqrt_nonneg _),
      ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_two, Real.sq_sqrt hr_nn, ENNReal.ofReal_toReal hω_ne]
  rw [lintegral_congr_ae h_ae]
  -- ∫⁻ (ν.rnDeriv ξ ω) * ‖h ω‖ₑ ^ 2 ∂ξ = ∫⁻ ‖h ω‖ₑ ^ 2 ∂ν.
  exact lintegral_rnDeriv_mul hνξ
    ((hh.enorm.pow_const (2 : ℝ)).aemeasurable)

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Change of dominator for a QMD residual `L²`-norm.**

The `L²(ξ)`-norm of the QMD residual of a path `γ` computed against a common
dominator `ξ ≫ γ.dominating` equals its `L²(γ.dominating)`-norm against the path's
own dominator. Via the chain rule `(γ.curve s).rnDeriv ξ =ᵐ[ξ] (γ.curve s).rnDeriv ν
· ν.rnDeriv ξ`, the `ξ`-residual factors as `√(dν/dξ) · (ν-residual)`, and the
weighting `√(dν/dξ)` is exactly absorbed by `eLpNorm_sqrt_rnDeriv_mul_eq`. -/
lemma eLpNorm_qmd_residual_change_dom
    (γ : QMDPath P) (ξ : Measure Ω) [SigmaFinite ξ]
    (hγξ : γ.dominating ≪ ξ) (t : ℝ) :
    eLpNorm (fun ω =>
        Real.sqrt ((γ.curve t).rnDeriv ξ ω).toReal
        - Real.sqrt ((γ.curve 0).rnDeriv ξ ω).toReal
        - (t / 2) * (γ.score : Ω → ℝ) ω
            * Real.sqrt ((γ.curve 0).rnDeriv ξ ω).toReal) 2 ξ
      = eLpNorm (fun ω =>
        Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
        - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
        - (t / 2) * (γ.score : Ω → ℝ) ω
            * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal) 2 γ.dominating := by
  haveI := γ.curve_isProbability t
  haveI := γ.curve_isProbability 0
  set ν : Measure Ω := γ.dominating with hν_def
  -- Score is measurable (its Lp representative is strongly measurable).
  have h_score_meas : Measurable (γ.score : Ω → ℝ) :=
    (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P)).measurable
  -- The ν-residual is measurable.
  have h_res_meas : Measurable (fun ω =>
      Real.sqrt ((γ.curve t).rnDeriv ν ω).toReal
      - Real.sqrt ((γ.curve 0).rnDeriv ν ω).toReal
      - (t / 2) * (γ.score : Ω → ℝ) ω
          * Real.sqrt ((γ.curve 0).rnDeriv ν ω).toReal) := by
    have m_t := (Measure.measurable_rnDeriv (γ.curve t) ν).ennreal_toReal.sqrt
    have m_0 := (Measure.measurable_rnDeriv (γ.curve 0) ν).ennreal_toReal.sqrt
    exact (m_t.sub m_0).sub ((measurable_const.mul h_score_meas).mul m_0)
  -- Pointwise factorization a.e.-ξ: ξ-residual = √(dν/dξ) · ν-residual.
  have h_fac : (fun ω =>
        Real.sqrt ((γ.curve t).rnDeriv ξ ω).toReal
        - Real.sqrt ((γ.curve 0).rnDeriv ξ ω).toReal
        - (t / 2) * (γ.score : Ω → ℝ) ω
            * Real.sqrt ((γ.curve 0).rnDeriv ξ ω).toReal)
      =ᵐ[ξ] (fun ω =>
        Real.sqrt (ν.rnDeriv ξ ω).toReal *
          (Real.sqrt ((γ.curve t).rnDeriv ν ω).toReal
           - Real.sqrt ((γ.curve 0).rnDeriv ν ω).toReal
           - (t / 2) * (γ.score : Ω → ℝ) ω
               * Real.sqrt ((γ.curve 0).rnDeriv ν ω).toReal)) := by
    have hct : (γ.curve t).rnDeriv ν * ν.rnDeriv ξ =ᵐ[ξ] (γ.curve t).rnDeriv ξ :=
      Measure.rnDeriv_mul_rnDeriv (γ.curve_absContinuous t)
    have hc0 : (γ.curve 0).rnDeriv ν * ν.rnDeriv ξ =ᵐ[ξ] (γ.curve 0).rnDeriv ξ :=
      Measure.rnDeriv_mul_rnDeriv (γ.curve_absContinuous 0)
    filter_upwards [hct, hc0] with ω hωt hω0
    have st : Real.sqrt ((γ.curve t).rnDeriv ξ ω).toReal
        = Real.sqrt ((γ.curve t).rnDeriv ν ω).toReal * Real.sqrt (ν.rnDeriv ξ ω).toReal := by
      rw [← hωt, Pi.mul_apply, ENNReal.toReal_mul, Real.sqrt_mul ENNReal.toReal_nonneg]
    have s0 : Real.sqrt ((γ.curve 0).rnDeriv ξ ω).toReal
        = Real.sqrt ((γ.curve 0).rnDeriv ν ω).toReal * Real.sqrt (ν.rnDeriv ξ ω).toReal := by
      rw [← hω0, Pi.mul_apply, ENNReal.toReal_mul, Real.sqrt_mul ENNReal.toReal_nonneg]
    rw [st, s0]; ring
  rw [eLpNorm_congr_ae h_fac]
  exact eLpNorm_sqrt_rnDeriv_mul_eq hγξ h_res_meas

/-- Measurability of the QMD residual computed against any σ-finite dominator. -/
private lemma qmd_residual_measurable
    (γ : QMDPath P) (ζ : Measure Ω) (t : ℝ) :
    Measurable (fun ω =>
      Real.sqrt ((γ.curve t).rnDeriv ζ ω).toReal
      - Real.sqrt ((γ.curve 0).rnDeriv ζ ω).toReal
      - (t / 2) * (γ.score : Ω → ℝ) ω
          * Real.sqrt ((γ.curve 0).rnDeriv ζ ω).toReal) := by
  have h_score_meas : Measurable (γ.score : Ω → ℝ) :=
    (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P)).measurable
  have m_t := (Measure.measurable_rnDeriv (γ.curve t) ζ).ennreal_toReal.sqrt
  have m_0 := (Measure.measurable_rnDeriv (γ.curve 0) ζ).ennreal_toReal.sqrt
  exact (m_t.sub m_0).sub ((measurable_const.mul h_score_meas).mul m_0)

/-- **Single-path QMD residual is `o(t)` against a common dominator (ℝ-form).**

The `L²(ξ)`-norm of the QMD residual of `γ`, divided by `|t|`, tends to `0` as
`t → 0`, for any σ-finite `ξ ≫ γ.dominating`. This is the change-of-dominator
transfer (`eLpNorm_qmd_residual_change_dom`) of the path's own
`o(t)` quadratic-mean residual (`QMDPath.qmd_limit`), converted from the
`ℝ≥0∞`-quotient form to the `ℝ`-ratio form via eventual `L²`-finiteness
(`QMDPath.residual_memLp_eventually`). -/
lemma qmd_residual_eLpNorm_toReal_div_isLittleO
    (γ : QMDPath P) (ξ : Measure Ω) [SigmaFinite ξ] (hγξ : γ.dominating ≪ ξ) :
    Tendsto (fun t : ℝ =>
        (eLpNorm (fun ω : Ω =>
          Real.sqrt ((γ.curve t).rnDeriv ξ ω).toReal
          - Real.sqrt ((γ.curve 0).rnDeriv ξ ω).toReal
          - (t / 2) * (γ.score : Ω → ℝ) ω
              * Real.sqrt ((γ.curve 0).rnDeriv ξ ω).toReal) 2 ξ).toReal / |t|)
      (𝓝[≠] 0) (𝓝 0) := by
  -- Transfer the integrand to `γ.dominating` via the change-of-dominator identity.
  have h_eq : (fun t : ℝ =>
      (eLpNorm (fun ω : Ω =>
        Real.sqrt ((γ.curve t).rnDeriv ξ ω).toReal
        - Real.sqrt ((γ.curve 0).rnDeriv ξ ω).toReal
        - (t / 2) * (γ.score : Ω → ℝ) ω
            * Real.sqrt ((γ.curve 0).rnDeriv ξ ω).toReal) 2 ξ).toReal / |t|)
      = (fun t : ℝ =>
      (eLpNorm (fun ω : Ω =>
        Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
        - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
        - (t / 2) * (γ.score : Ω → ℝ) ω
            * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal) 2 γ.dominating).toReal
        / |t|) := by
    funext t; rw [eLpNorm_qmd_residual_change_dom γ ξ hγξ t]
  rw [h_eq]
  -- Convert the `ℝ≥0∞`-quotient `qmd_limit` to the `ℝ`-ratio form.
  have h_cont : ContinuousAt ENNReal.toReal (0 : ℝ≥0∞) :=
    ENNReal.continuousAt_toReal (by norm_num)
  have h_toReal :
      Tendsto (fun t : ℝ =>
          (eLpNorm (fun ω : Ω =>
            Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal
            - Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal
            - (t / 2) * (γ.score : Ω → ℝ) ω
                * Real.sqrt ((γ.curve 0).rnDeriv γ.dominating ω).toReal) 2 γ.dominating
            / ENNReal.ofReal |t|).toReal)
        (𝓝[≠] 0) (𝓝 (0 : ℝ)) :=
    h_cont.tendsto.comp γ.qmd_limit
  have h_self_ne : {x : ℝ | x ≠ 0} ∈ 𝓝[≠] (0 : ℝ) := self_mem_nhdsWithin
  refine h_toReal.congr' ?_
  filter_upwards [h_self_ne, γ.residual_memLp_eventually] with t ht_ne ht_mem
  have habs : 0 < |t| := abs_pos.mpr ht_ne
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal habs.le]

/-- **Common-dominator per-sample Hellinger little-o.**

For two `QMDPath`s `γ₁, γ₂` at the same `P` with the same score, sharing a common
σ-finite dominator `ξ` (`γᵢ.dominating ≪ ξ`), the per-sample `L²(ξ)` Hellinger
distance is `o(t)`. The equal-dominator hypothesis of
`hellinger_per_sample_residual_isLittleO` is dropped: both QMD expansions are
anchored at the *common* reference `√(dP/dξ)` (since `γᵢ.curve 0 = P`), so the
linear terms cancel and the difference is the difference of the two `ξ`-residuals,
each `o(t)` by `qmd_residual_eLpNorm_toReal_div_isLittleO`. -/
lemma hellinger_per_sample_residual_isLittleO_common_dom
    (γ₁ γ₂ : QMDPath P) (ξ : Measure Ω) [SigmaFinite ξ]
    (h₁ : γ₁.dominating ≪ ξ) (h₂ : γ₂.dominating ≪ ξ)
    (h_score : γ₁.score = γ₂.score) :
    Tendsto
      (fun t : ℝ =>
        (eLpNorm
          (fun ω : Ω =>
            Real.sqrt ((γ₁.curve t).rnDeriv ξ ω).toReal
            - Real.sqrt ((γ₂.curve t).rnDeriv ξ ω).toReal)
          2 ξ).toReal / |t|)
      (𝓝[≠] 0) (𝓝 0) := by
  -- Score functions agree pointwise.
  have h_score_fn : ((γ₁.score : Ω → ℝ)) = ((γ₂.score : Ω → ℝ)) := by rw [h_score]
  -- `ξ`-residuals of the two paths.
  set R₁ : ℝ → Ω → ℝ := fun t ω =>
    Real.sqrt ((γ₁.curve t).rnDeriv ξ ω).toReal
      - Real.sqrt ((γ₁.curve 0).rnDeriv ξ ω).toReal
      - (t / 2) * (γ₁.score : Ω → ℝ) ω
          * Real.sqrt ((γ₁.curve 0).rnDeriv ξ ω).toReal with hR₁_def
  set R₂ : ℝ → Ω → ℝ := fun t ω =>
    Real.sqrt ((γ₂.curve t).rnDeriv ξ ω).toReal
      - Real.sqrt ((γ₂.curve 0).rnDeriv ξ ω).toReal
      - (t / 2) * (γ₂.score : Ω → ℝ) ω
          * Real.sqrt ((γ₂.curve 0).rnDeriv ξ ω).toReal with hR₂_def
  set H : ℝ → Ω → ℝ := fun t ω =>
    Real.sqrt ((γ₁.curve t).rnDeriv ξ ω).toReal
      - Real.sqrt ((γ₂.curve t).rnDeriv ξ ω).toReal with hH_def
  -- Pointwise cancellation: `H = R₁ - R₂` (both anchored at `√(dP/dξ)`).
  have h_H_eq_sub : ∀ t, H t = R₁ t - R₂ t := by
    intro t; funext ω
    have hc1 : γ₁.curve 0 = P := γ₁.curve_at_zero
    have hc2 : γ₂.curve 0 = P := γ₂.curve_at_zero
    simp only [hH_def, hR₁_def, hR₂_def, Pi.sub_apply]
    rw [hc1, hc2, h_score_fn]; ring
  -- Each `ξ`-residual ratio tends to `0`.
  have hr₁ := qmd_residual_eLpNorm_toReal_div_isLittleO γ₁ ξ h₁
  have hr₂ := qmd_residual_eLpNorm_toReal_div_isLittleO γ₂ ξ h₂
  have h_sum : Tendsto (fun t : ℝ =>
      (eLpNorm (R₁ t) 2 ξ).toReal / |t| + (eLpNorm (R₂ t) 2 ξ).toReal / |t|)
      (𝓝[≠] 0) (𝓝 0) := by
    simpa using hr₁.add hr₂
  -- Eventual `L²(ξ)`-finiteness of both residuals (via the change-of-dominator).
  have h_mem₁ : ∀ᶠ t : ℝ in 𝓝[≠] 0, eLpNorm (R₁ t) 2 ξ ≠ ⊤ := by
    filter_upwards [γ₁.residual_memLp_eventually] with t ht
    rw [hR₁_def, eLpNorm_qmd_residual_change_dom γ₁ ξ h₁ t]; exact ht.2.ne
  have h_mem₂ : ∀ᶠ t : ℝ in 𝓝[≠] 0, eLpNorm (R₂ t) 2 ξ ≠ ⊤ := by
    filter_upwards [γ₂.residual_memLp_eventually] with t ht
    rw [hR₂_def, eLpNorm_qmd_residual_change_dom γ₂ ξ h₂ t]; exact ht.2.ne
  -- Squeeze `0 ≤ (eLpNorm H).toReal/|t| ≤ (eLpNorm R₁).toReal/|t| + (eLpNorm R₂).toReal/|t|`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum
    (Filter.Eventually.of_forall (fun t => by positivity)) ?_
  filter_upwards [h_mem₁, h_mem₂] with t ht₁ ht₂
  have h_aes₁ : AEStronglyMeasurable (R₁ t) ξ :=
    (qmd_residual_measurable γ₁ ξ t).aestronglyMeasurable
  have h_aes₂ : AEStronglyMeasurable (R₂ t) ξ :=
    (qmd_residual_measurable γ₂ ξ t).aestronglyMeasurable
  have h_tri : eLpNorm (H t) 2 ξ ≤ eLpNorm (R₁ t) 2 ξ + eLpNorm (R₂ t) 2 ξ := by
    rw [h_H_eq_sub t]
    exact eLpNorm_sub_le h_aes₁ h_aes₂ (by norm_num)
  have h_toReal_le : (eLpNorm (H t) 2 ξ).toReal
      ≤ (eLpNorm (R₁ t) 2 ξ).toReal + (eLpNorm (R₂ t) 2 ξ).toReal := by
    calc (eLpNorm (H t) 2 ξ).toReal
        ≤ (eLpNorm (R₁ t) 2 ξ + eLpNorm (R₂ t) 2 ξ).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ht₁, ht₂⟩) h_tri
      _ = (eLpNorm (R₁ t) 2 ξ).toReal + (eLpNorm (R₂ t) 2 ξ).toReal :=
          ENNReal.toReal_add ht₁ ht₂
  rw [← add_div]
  gcongr

/-- **Common-dominator LAN-locality for same-score `QMDPath`s.**

The equal-dominator generalization of `hellinger_locality_for_qmdpath_same_score`:
two `QMDPath`s `γ₁, γ₂` at the same `P` with the same score, sharing *any* common
σ-finite dominator `ξ`, have their `n`-fold product-Hellinger `L²(ξ)`-norm tending
to `0` at scale `t = 1/√n`. Composes the common-dominator per-sample little-o
(`hellinger_per_sample_residual_isLittleO_common_dom`) with the (already
ξ-generic) tensorization bound
`hellinger_product_eLpNorm_le_sqrt_n_per_sample`. -/
theorem hellinger_locality_for_qmdpath_same_score_common_dom
    (γ₁ γ₂ : QMDPath P) (ξ : Measure Ω) [SigmaFinite ξ]
    (h₁ : γ₁.dominating ≪ ξ) (h₂ : γ₂.dominating ≪ ξ)
    (h_score : γ₁.score = γ₂.score) :
    Tendsto
      (fun n : ℕ =>
        (eLpNorm
          (fun X : Fin n → Ω =>
            Real.sqrt (∏ j, (γ₁.curve ((Real.sqrt n)⁻¹)).rnDeriv ξ (X j)).toReal
            - Real.sqrt (∏ j, (γ₂.curve ((Real.sqrt n)⁻¹)).rnDeriv ξ (X j)).toReal)
          2 (Measure.pi (fun _ : Fin n => ξ))).toReal)
      atTop (𝓝 (0 : ℝ)) := by
  set t : ℕ → ℝ := fun n => (Real.sqrt n)⁻¹ with ht_def
  set Tgt : ℕ → ℝ := fun n =>
    (eLpNorm
      (fun X : Fin n → Ω =>
        Real.sqrt (∏ j, (γ₁.curve (t n)).rnDeriv ξ (X j)).toReal
        - Real.sqrt (∏ j, (γ₂.curve (t n)).rnDeriv ξ (X j)).toReal)
      2 (Measure.pi (fun _ : Fin n => ξ))).toReal with hTgt_def
  set PerSample : ℕ → ℝ := fun n =>
    (eLpNorm
      (fun ω : Ω =>
        Real.sqrt ((γ₁.curve (t n)).rnDeriv ξ ω).toReal
        - Real.sqrt ((γ₂.curve (t n)).rnDeriv ξ ω).toReal)
      2 ξ).toReal with hPerSample_def
  -- t n > 0 for n ≥ 1.
  have h_t_pos : ∀ n : ℕ, 1 ≤ n → 0 < t n := by
    intro n hn
    have hpos : 0 < (n : ℝ) := lt_of_lt_of_le one_pos (by exact_mod_cast hn)
    exact inv_pos.mpr (Real.sqrt_pos.mpr hpos)
  have h_Tgt_nn : ∀ n : ℕ, 0 ≤ Tgt n := fun n => ENNReal.toReal_nonneg
  -- Tensorisation bound (ξ-generic).
  have h_bound : ∀ n : ℕ, Tgt n ≤ Real.sqrt n * PerSample n := by
    intro n
    haveI := γ₁.curve_isProbability (t n)
    haveI := γ₂.curve_isProbability (t n)
    have hac₁ : γ₁.curve (t n) ≪ ξ := (γ₁.curve_absContinuous (t n)).trans h₁
    have hac₂ : γ₂.curve (t n) ≪ ξ := (γ₂.curve_absContinuous (t n)).trans h₂
    exact hellinger_product_eLpNorm_le_sqrt_n_per_sample (ξ := ξ)
      (μ := γ₁.curve (t n)) (ν := γ₂.curve (t n)) hac₁ hac₂ n
  -- t n → 0 within the punctured neighbourhood.
  have h_t_to_zero : Tendsto t atTop (𝓝[≠] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h_sqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
        Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
      simpa [ht_def] using! h_sqrt.inv_tendsto_atTop
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      exact (h_t_pos n hn).ne'
  -- PerSample n / |t n| → 0 (common-dominator per-sample little-o composed with t n → 0).
  have h_per_div : Tendsto (fun n : ℕ => PerSample n / |t n|) atTop (𝓝 (0 : ℝ)) := by
    have h_sub := hellinger_per_sample_residual_isLittleO_common_dom γ₁ γ₂ ξ h₁ h₂ h_score
    have h_comp := h_sub.comp h_t_to_zero
    convert! h_comp using 1
  -- For n ≥ 1, √n · PerSample n = PerSample n / |t n|.
  have h_id : ∀ n : ℕ, 1 ≤ n → Real.sqrt n * PerSample n = PerSample n / |t n| := by
    intro n hn
    have hpos := h_t_pos n hn
    rw [abs_of_pos hpos, ht_def]
    have hsq_pos : 0 < Real.sqrt n :=
      Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le one_pos hn))
    field_simp
  have h_sqrt_per :
      Tendsto (fun n : ℕ => Real.sqrt n * PerSample n) atTop (𝓝 (0 : ℝ)) := by
    apply h_per_div.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact (h_id n hn).symm
  -- Squeeze.
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sqrt_per
    (Filter.Eventually.of_forall h_Tgt_nn)
    (Filter.Eventually.of_forall h_bound)

end AsymptoticStatistics.LowerBounds.RegularEstimator
