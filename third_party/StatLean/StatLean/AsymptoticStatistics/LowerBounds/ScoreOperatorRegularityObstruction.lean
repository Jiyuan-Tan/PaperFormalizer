module
public import StatLean.AsymptoticStatistics.Core.EfficiencyOperational
public import StatLean.AsymptoticStatistics.Efficiency.HajekLeCamConvolution
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorNarrowReverseUncond
public import StatLean.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.Abstract1DLAN
public import StatLean.AsymptoticStatistics.Operators.ScoreOperator
public import Mathlib.MeasureTheory.Group.Convolution

@[expose] public section

/-!
# Regularity obstruction outside the adjoint score range

Probability and functional-analytic ingredients for van der Vaart
Theorem 25.32. Raw regularity is kept independent of differentiability,
influence functions, and Gaussian conclusions.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace AsymptoticStatistics.LowerBounds.ScoreOperatorRegularityObstruction

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Operators.ScoreOperator

/-- Reparameterize a dominated QMD path by the scalar map `t ↦ a t`, so that
its score is multiplied by `a`. -/
noncomputable def reparamQMDPath
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (a : ℝ) (gamma : QMDPath P) : QMDPath P where
  curve t := gamma.curve (a * t)
  curve_at_zero := by simp [gamma.curve_at_zero]
  curve_isProbability t := gamma.curve_isProbability (a * t)
  dominating := gamma.dominating
  curve_absContinuous t := gamma.curve_absContinuous (a * t)
  dominating_sigmaFinite := gamma.dominating_sigmaFinite
  score := a • gamma.score
  qmd_limit := by
    by_cases ha : a = 0
    · subst a
      simp
    · have hmap : Tendsto (fun t : ℝ => a * t) (𝓝[≠] 0) (𝓝[≠] 0) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · simpa using!
            (((continuous_const : Continuous (fun _ : ℝ => a)).mul continuous_id).tendsto 0
              |>.mono_left inf_le_left)
        · filter_upwards [self_mem_nhdsWithin] with t ht
          exact mul_ne_zero ha ht
      have hcomp := gamma.qmd_limit.comp hmap
      have hmul0 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal |a|) hcomp
        (Or.inr ENNReal.ofReal_ne_top)
      have hmul :
          Tendsto
            (fun t : ℝ => ENNReal.ofReal |a| *
              (eLpNorm (fun omega : Ω =>
                Real.sqrt ((gamma.curve (a * t)).rnDeriv gamma.dominating omega).toReal
                  - Real.sqrt ((gamma.curve 0).rnDeriv gamma.dominating omega).toReal
                  - ((a * t) / 2) * (gamma.score : Ω → ℝ) omega *
                    Real.sqrt ((gamma.curve 0).rnDeriv gamma.dominating omega).toReal)
                2 gamma.dominating / ENNReal.ofReal |a * t|))
            (𝓝[≠] 0) (𝓝 0) := by
        simpa only [Function.comp_apply, mul_zero] using hmul0
      apply hmul.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ha_ofReal : ENNReal.ofReal |a| ≠ 0 :=
        ENNReal.ofReal_ne_zero_iff.mpr (abs_pos.mpr ha)
      have ha_top : ENNReal.ofReal |a| ≠ ⊤ := ENNReal.ofReal_ne_top
      have hPdom : P ≪ gamma.dominating := by
        simpa [gamma.curve_at_zero] using gamma.curve_absContinuous 0
      have hscoreP :
          (fun omega : Ω =>
              (((a • gamma.score : ↥(L2ZeroMean P)) : Ω → ℝ) omega)) =ᵐ[P]
            fun omega => a * (gamma.score : Ω → ℝ) omega := by
        simpa only [Pi.smul_apply, smul_eq_mul] using!
          (Lp.coeFn_smul a (gamma.score : Lp ℝ 2 P))
      have hscoreDensity : ∀ᵐ omega ∂gamma.dominating,
          P.rnDeriv gamma.dominating omega ≠ 0 →
            (((a • gamma.score : ↥(L2ZeroMean P)) : Ω → ℝ) omega) =
              a * (gamma.score : Ω → ℝ) omega := by
        apply (ae_withDensity_iff (Measure.measurable_rnDeriv P gamma.dominating)).1
        rw [Measure.withDensity_rnDeriv_eq P gamma.dominating hPdom]
        exact hscoreP
      have hres :
          eLpNorm (fun omega : Ω =>
            Real.sqrt ((gamma.curve (a * t)).rnDeriv gamma.dominating omega).toReal
              - Real.sqrt ((gamma.curve (a * 0)).rnDeriv gamma.dominating omega).toReal
              - (t / 2) * (((a • gamma.score : ↥(L2ZeroMean P)) : Ω → ℝ) omega) *
                Real.sqrt ((gamma.curve (a * 0)).rnDeriv gamma.dominating omega).toReal)
            2 gamma.dominating =
          eLpNorm (fun omega : Ω =>
            Real.sqrt ((gamma.curve (a * t)).rnDeriv gamma.dominating omega).toReal
              - Real.sqrt ((gamma.curve 0).rnDeriv gamma.dominating omega).toReal
              - ((a * t) / 2) * (gamma.score : Ω → ℝ) omega *
                Real.sqrt ((gamma.curve 0).rnDeriv gamma.dominating omega).toReal)
            2 gamma.dominating := by
        apply eLpNorm_congr_ae
        filter_upwards [hscoreDensity] with omega hscore
        simp only [mul_zero]
        by_cases hd : P.rnDeriv gamma.dominating omega = 0
        · simp [gamma.curve_at_zero, hd]
        · rw [hscore hd]
          ring
      rw [hres, abs_mul, ENNReal.ofReal_mul (abs_nonneg a)]
      rw [← mul_div_assoc]
      exact ENNReal.mul_div_mul_left _ _ ha_ofReal ha_top

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- Selected path/derivative data used by the score-operator obstruction.

Constitutive (vdV §25.5, Theorem 25.32): every parameter direction `b`
has a selected QMD path whose score is `A b`, and whose parameter quotient
is the Riesz derivative `inner chiTilde b`.

For example, in a one-dimensional Gaussian location model one may take
`H=ℝ`, `A` to be the location-score isometry, `chiTilde=1`, and the standard
location paths. -/
structure ScorePathDerivativeData
    (A : ScoreOperator H P) (chiTilde : H)
    (ψ : Measure Ω → ℝ) where
  /-- Constitutive (vdV §25.5): selected QMD path in direction `b`. -/
  selectedPath : H → AsymptoticStatistics.Core.QMDPath.QMDPath P
  /-- Constitutive (vdV §25.5): its score is the score-operator image. -/
  score_eq : ∀ b : H, (selectedPath b).score = A.toCLM b
  /-- Constitutive (vdV §25.5): quotient derivative is the Riesz pairing. -/
  derivative_quotient : ∀ b : H,
    Tendsto (fun t : ℝ => (ψ ((selectedPath b).curve t) - ψ P) / t)
      (𝓝[≠] 0) (𝓝 ⟪chiTilde, b⟫_ℝ)

/-- Raw regularity: measurable estimators have one common local weak limit
along all selected paths.  There is no hpd/eif/normality field.

Constitutive (vdV §25.5, Theorem 25.32): regularity is precisely invariance
of the centered local limit law over `b`.

For the Gaussian location sample mean, the common limit is `N(0,1)` along
every local location path. -/
structure RawRegularity
    (A : ScoreOperator H P) (chiTilde : H)
    (ψ : Measure Ω → ℝ)
    (paths : ScorePathDerivativeData A chiTilde ψ)
    (T_n : ∀ n, (Fin n → Ω) → ℝ) where
  /-- Standard measurable-estimator side condition. -/
  estimator_meas : ∀ n, Measurable (T_n n)
  /-- The common local limit law. -/
  limitLaw : Measure ℝ
  /-- The common limit is a probability measure. -/
  limit_isProbability : IsProbabilityMeasure limitLaw
  /-- Common weak convergence after centering at the perturbed truth. -/
  weak_limit : ∀ b : H,
    AsymptoticStatistics.WeakConverges
      (fun n : ℕ =>
        (Measure.pi
          (fun _ : Fin n => (paths.selectedPath b).curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω => Real.sqrt n *
            (T_n n X - ψ ((paths.selectedPath b).curve ((Real.sqrt n)⁻¹)))))
      limitLaw

/-- A same-score QMD path may replace another path in a regular local limit,
provided the two centering functionals have the same directional derivative.
The comparison is through the sum of their (path-local) dominators. -/
private theorem weakConverges_sameScore_commonDom
    (ψ : Measure Ω → ℝ)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hT_meas : ∀ n, Measurable (T_n n))
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (γ γ₀ : QMDPath P)
    (h_score_eq : γ.score = γ₀.score)
    (d : ℝ)
    (h_diff_γ : Tendsto (fun s : ℝ => (ψ (γ.curve s) - ψ P) / s)
      (𝓝[≠] 0) (𝓝 d))
    (h_diff_γ₀ : Tendsto (fun s : ℝ => (ψ (γ₀.curve s) - ψ P) / s)
      (𝓝[≠] 0) (𝓝 d))
    (h_chosen : AsymptoticStatistics.WeakConverges
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => γ₀.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω => Real.sqrt n *
            (T_n n X - ψ (γ₀.curve ((Real.sqrt n)⁻¹))))) L) :
    AsymptoticStatistics.WeakConverges
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => γ.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω => Real.sqrt n *
            (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹))))) L := by
  classical
  set t : ℕ → ℝ := fun n => (Real.sqrt n)⁻¹ with ht_def
  set Pn : ∀ n : ℕ, Measure (Fin n → Ω) :=
    fun n => Measure.pi (fun _ : Fin n => γ.curve (t n)) with hPn_def
  set Pn₀ : ∀ n : ℕ, Measure (Fin n → Ω) :=
    fun n => Measure.pi (fun _ : Fin n => γ₀.curve (t n)) with hPn₀_def
  haveI hPn_prob : ∀ n, IsProbabilityMeasure (Pn n) := by
    intro n
    haveI : ∀ _ : Fin n, IsProbabilityMeasure (γ.curve (t n)) := fun _ =>
      γ.curve_isProbability _
    rw [hPn_def]
    infer_instance
  haveI hPn₀_prob : ∀ n, IsProbabilityMeasure (Pn₀ n) := by
    intro n
    haveI : ∀ _ : Fin n, IsProbabilityMeasure (γ₀.curve (t n)) := fun _ =>
      γ₀.curve_isProbability _
    rw [hPn₀_def]
    infer_instance
  set Fγ : ∀ n, (Fin n → Ω) → ℝ :=
    fun n X => Real.sqrt n * (T_n n X - ψ (γ.curve (t n))) with hFγ_def
  set Fγ₀ : ∀ n, (Fin n → Ω) → ℝ :=
    fun n X => Real.sqrt n * (T_n n X - ψ (γ₀.curve (t n))) with hFγ₀_def
  have hFγ_meas : ∀ n, Measurable (Fγ n) := fun n =>
    Measurable.const_mul ((hT_meas n).sub measurable_const) _
  have hFγ₀_meas : ∀ n, Measurable (Fγ₀ n) := fun n =>
    Measurable.const_mul ((hT_meas n).sub measurable_const) _
  have h_C : AsymptoticStatistics.WeakConverges
      (fun n => (Pn₀ n).map (Fγ₀ n)) L := by
    simpa [hPn₀_def, hFγ₀_def, ht_def] using h_chosen
  have h_inv_to_zero : Tendsto t atTop (𝓝 0) := by
    have h_sqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa [ht_def] using! h_sqrt.inv_tendsto_atTop
  have h_inv_ne : ∀ᶠ n : ℕ in atTop, t n ≠ 0 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hpos : (0 : ℝ) < Real.sqrt n :=
      Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le one_pos hn))
    exact inv_ne_zero hpos.ne'
  have h_inv_punctured : Tendsto t atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h_inv_to_zero, h_inv_ne.mono fun _ hn => hn⟩
  have h_psi_diff_zero :
      Tendsto (fun s : ℝ =>
          (ψ (γ.curve s) - ψ P) / s - (ψ (γ₀.curve s) - ψ P) / s)
        (𝓝[≠] 0) (𝓝 0) := by
    simpa using h_diff_γ.sub h_diff_γ₀
  have h_shift_to_zero' :
      Tendsto (fun n : ℕ => Real.sqrt n *
          (ψ (γ.curve (t n)) - ψ (γ₀.curve (t n))))
        atTop (𝓝 0) := by
    have h_psi_diff_zero' :
        Tendsto (fun s : ℝ => (ψ (γ.curve s) - ψ (γ₀.curve s)) / s)
          (𝓝[≠] 0) (𝓝 0) := by
      apply h_psi_diff_zero.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      field_simp
      ring
    have h_shift_to_zero :
        Tendsto (fun n : ℕ =>
          (ψ (γ.curve (t n)) - ψ (γ₀.curve (t n))) / t n)
          atTop (𝓝 0) := h_psi_diff_zero'.comp h_inv_punctured
    apply h_shift_to_zero.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hpos : (0 : ℝ) < Real.sqrt n :=
      Real.sqrt_pos.mpr (by exact_mod_cast (lt_of_lt_of_le one_pos hn))
    rw [show t n = (Real.sqrt n)⁻¹ by rfl]
    field_simp
  have h_dist_const : ∀ n (X : Fin n → Ω),
      dist (Fγ₀ n X) (Fγ n X) =
        |Real.sqrt n * (ψ (γ.curve (t n)) - ψ (γ₀.curve (t n)))| := by
    intro n X
    rw [Real.dist_eq]
    congr 1
    simp only [hFγ_def, hFγ₀_def]
    ring
  have h_dist_to_zero : ∀ ε > 0,
      Tendsto (fun n : ℕ =>
          (Pn₀ n).real {ω : Fin n → Ω | ε ≤ dist (Fγ₀ n ω) (Fγ n ω)})
        atTop (𝓝 0) := by
    intro ε hε
    have h_close : Tendsto (fun n : ℕ =>
        |Real.sqrt n * (ψ (γ.curve (t n)) - ψ (γ₀.curve (t n)))|)
        atTop (𝓝 0) := by
      have h := (continuous_abs.tendsto _).comp h_shift_to_zero'
      simpa only [Function.comp_apply, abs_zero] using! h
    have hev : ∀ᶠ n : ℕ in atTop,
        |Real.sqrt n * (ψ (γ.curve (t n)) - ψ (γ₀.curve (t n)))| < ε := by
      have h := (Metric.tendsto_nhds.mp h_close) ε hε
      filter_upwards [h] with n hn
      rwa [Real.dist_eq, sub_zero, abs_abs] at hn
    have h_eventually_empty : ∀ᶠ n : ℕ in atTop,
        {ω : Fin n → Ω | ε ≤ dist (Fγ₀ n ω) (Fγ n ω)} = (∅ : Set _) := by
      filter_upwards [hev] with n hn
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
      rw [h_dist_const]
      exact hn
    have h_real_zero : ∀ᶠ n : ℕ in atTop,
        (Pn₀ n).real {ω : Fin n → Ω | ε ≤ dist (Fγ₀ n ω) (Fγ n ω)} = 0 := by
      filter_upwards [h_eventually_empty] with n hn
      rw [hn]
      simp
    exact (tendsto_congr' h_real_zero).mpr tendsto_const_nhds
  have h_B : AsymptoticStatistics.WeakConverges
      (fun n => (Pn₀ n).map (Fγ n)) L :=
    AsymptoticStatistics.WeakConverges.slutsky_of_tendstoInMeasure_dist
      (X := Fγ₀) (Y := Fγ)
      (hX_meas := fun n => (hFγ₀_meas n).aemeasurable)
      (hY_meas := fun n => (hFγ_meas n).aemeasurable)
      (hX := h_C) (hDist := h_dist_to_zero)
  set ξ : Measure Ω := γ.dominating + γ₀.dominating with hξ_def
  haveI hξ_sf : SigmaFinite ξ := by rw [hξ_def]; infer_instance
  have h_γ_ξ : γ.dominating ≪ ξ :=
    Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have h_γ₀_ξ : γ₀.dominating ≪ ξ :=
    Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  have h_hellinger :
      Tendsto
        (fun n : ℕ =>
          (eLpNorm
            (fun X : Fin n → Ω =>
              Real.sqrt (∏ j, (γ.curve (t n)).rnDeriv ξ (X j)).toReal
              - Real.sqrt (∏ j, (γ₀.curve (t n)).rnDeriv ξ (X j)).toReal)
            2 (Measure.pi (fun _ : Fin n => ξ))).toReal)
        atTop (𝓝 (0 : ℝ)) :=
    RegularEstimator.hellinger_locality_for_qmdpath_same_score_common_dom
      γ γ₀ ξ h_γ_ξ h_γ₀_ξ h_score_eq
  have h_γ_dom_ξ : ∀ n, γ.curve (t n) ≪ ξ := fun n =>
    (γ.curve_absContinuous (t n)).trans h_γ_ξ
  have h_γ₀_dom_ξ : ∀ n, γ₀.curve (t n) ≪ ξ := fun n =>
    (γ₀.curve_absContinuous (t n)).trans h_γ₀_ξ
  haveI : ∀ n, IsProbabilityMeasure (γ.curve (t n)) := fun n =>
    γ.curve_isProbability _
  haveI : ∀ n, IsProbabilityMeasure (γ₀.curve (t n)) := fun n =>
    γ₀.curve_isProbability _
  intro f
  have h_push_eq_γ : ∀ n,
      ∫ y, f y ∂((Pn n).map (Fγ n)) = ∫ X, f (Fγ n X) ∂(Pn n) := fun n =>
    integral_map (hFγ_meas n).aemeasurable f.continuous.aestronglyMeasurable
  have h_push_eq_γ₀ : ∀ n,
      ∫ y, f y ∂((Pn₀ n).map (Fγ n)) = ∫ X, f (Fγ n X) ∂(Pn₀ n) := fun n =>
    integral_map (hFγ_meas n).aemeasurable f.continuous.aestronglyMeasurable
  have h_diff_to_zero :
      Tendsto (fun n =>
        |∫ X, f (Fγ n X) ∂(Pn n) - ∫ X, f (Fγ n X) ∂(Pn₀ n)|)
        atTop (𝓝 0) := by
    have h :=
      AsymptoticStatistics.ForMathlib.HellingerIntegralBound.integral_test_diff_tendsto_zero
        (ξ := ξ) (μ := fun n => γ.curve (t n)) (ν := fun n => γ₀.curve (t n))
        h_γ_dom_ξ h_γ₀_dom_ξ (F := Fγ) (fun n => hFγ_meas n) f h_hellinger
    simpa [hPn_def, hPn₀_def] using h
  have h_B_int : Tendsto (fun n => ∫ y, f y ∂((Pn₀ n).map (Fγ n))) atTop
      (𝓝 (∫ y, f y ∂L)) := h_B f
  have h_eq_γ : (fun n => ∫ y, f y ∂((Pn n).map (Fγ n))) =
      fun n => ∫ X, f (Fγ n X) ∂(Pn n) := by
    funext n
    exact h_push_eq_γ n
  have h_eq_γ₀ : (fun n => ∫ y, f y ∂((Pn₀ n).map (Fγ n))) =
      fun n => ∫ X, f (Fγ n X) ∂(Pn₀ n) := by
    funext n
    exact h_push_eq_γ₀ n
  rw [h_eq_γ]
  rw [h_eq_γ₀] at h_B_int
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε₂ : 0 < ε / 2 := by positivity
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp h_diff_to_zero) (ε / 2) hε₂
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp h_B_int) (ε / 2) hε₂
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hA := hN₁ n (le_of_max_le_left hn)
  have hC := hN₂ n (le_of_max_le_right hn)
  rw [Real.dist_eq, sub_zero, abs_abs] at hA
  rw [Real.dist_eq] at hC ⊢
  have h_triangle : |∫ X, f (Fγ n X) ∂(Pn n) - ∫ y, f y ∂L| ≤
      |∫ X, f (Fγ n X) ∂(Pn n) - ∫ X, f (Fγ n X) ∂(Pn₀ n)| +
        |∫ X, f (Fγ n X) ∂(Pn₀ n) - ∫ y, f y ∂L| := by
    calc
      _ = |(∫ X, f (Fγ n X) ∂(Pn n) - ∫ X, f (Fγ n X) ∂(Pn₀ n)) +
          (∫ X, f (Fγ n X) ∂(Pn₀ n) - ∫ y, f y ∂L)| := by
        congr 1
        ring
      _ ≤ _ := abs_add_le _ _
  linarith

private theorem continuous_single_zero :
    Continuous (EuclideanSpace.single (0 : Fin 1) :
      ℝ → EuclideanSpace ℝ (Fin 1)) := by
  have hfun :
      (EuclideanSpace.single (0 : Fin 1) : ℝ → EuclideanSpace ℝ (Fin 1)) =
        fun r : ℝ => (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ : Fin 1 => r) := by
    funext r
    ext i
    fin_cases i
    rw [PiLp.single_apply]
    simp
  rw [hfun]
  refine (PiLp.continuous_toLp 2 (β := fun _ : Fin 1 => ℝ)).comp ?_
  exact continuous_pi fun _ => continuous_id

private theorem qmdPath_withDensity_eq_curve (γ : QMDPath P) (t : ℝ) :
    γ.dominating.withDensity (fun x => ENNReal.ofReal
      ((γ.curve t).rnDeriv γ.dominating x).toReal) = γ.curve t := by
  letI : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
  rw [show γ.dominating.withDensity (fun x => ENNReal.ofReal
      ((γ.curve t).rnDeriv γ.dominating x).toReal) =
      γ.dominating.withDensity ((γ.curve t).rnDeriv γ.dominating) by
    apply withDensity_congr_ae
    filter_upwards [Measure.rnDeriv_lt_top (γ.curve t) γ.dominating] with x hx
    exact ENNReal.ofReal_toReal hx.ne]
  exact Measure.withDensity_rnDeriv_eq _ _ (γ.curve_absContinuous t)

private theorem qmdPath_isPDFOf (γ : QMDPath P) :
    AsymptoticStatistics.IsPDFOf
      (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.to1DParametricFamily γ)
      γ.dominating where
  density_integral_eq_one θ := by
    haveI : IsProbabilityMeasure (γ.curve (θ 0)) := γ.curve_isProbability _
    have h := Measure.integral_toReal_rnDeriv (γ.curve_absContinuous (θ 0))
    change ∫ x, ((γ.curve (θ 0)).rnDeriv γ.dominating x).toReal ∂γ.dominating = 1
    rw [h]
    simp [Measure.real]
  density_integrable θ := by
    letI : IsProbabilityMeasure (γ.curve (θ 0)) := γ.curve_isProbability _
    exact Measure.integrable_toReal_rnDeriv

private theorem reparam_derivative_quotient
    (chiTilde : H) (ψ : Measure Ω → ℝ)
    (paths : ScorePathDerivativeData A chiTilde ψ)
    (b : H) (a : ℝ) :
    Tendsto (fun t : ℝ =>
      (ψ ((reparamQMDPath (P := P) a (paths.selectedPath b)).curve t) - ψ P) / t)
      (𝓝[≠] 0) (𝓝 (a * ⟪chiTilde, b⟫_ℝ)) := by
  by_cases ha : a = 0
  · subst a
    simp [reparamQMDPath, (paths.selectedPath b).curve_at_zero]
  · have hmap : Tendsto (fun t : ℝ => a * t) (𝓝[≠] 0) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · simpa using!
          (((continuous_const : Continuous (fun _ : ℝ => a)).mul continuous_id).tendsto 0
            |>.mono_left inf_le_left)
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_ne_zero ha ht
    have h := (paths.derivative_quotient b).comp hmap
    have ha_mul : Tendsto (fun t : ℝ => a *
        ((ψ ((paths.selectedPath b).curve (a * t)) - ψ P) / (a * t)))
        (𝓝[≠] 0) (𝓝 (a * ⟪chiTilde, b⟫_ℝ)) := by
      simpa only [Function.comp_apply] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => a) (𝓝[≠] 0) (𝓝 a)).mul h)
    apply ha_mul.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [reparamQMDPath]
    field_simp

private theorem fisher_info_fin1_eq_score_norm_sq (γ : QMDPath P) :
    AsymptoticStatistics.fisherInformation
      (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.to1DParametricFamily γ)
      γ.dominating 0
      (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.score1D γ)
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
      (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) =
        ‖(γ.score : Lp ℝ 2 P)‖ ^ 2 := by
  classical
  set h' : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1 with hh'
  have hinner : ∀ x : Ω,
      (⟪h', AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.score1D γ x⟫_ℝ : ℝ) =
        ((γ.score : Lp ℝ 2 P) : Ω → ℝ) x := by
    intro x
    rw [PiLp.inner_apply, Fin.sum_univ_one]
    simp only [hh', Fin.isValue, PiLp.single_eq_same,
      T6_FinDimLAN.QMDPath.score1D]
    change ((γ.score : Lp ℝ 2 P) : Ω → ℝ) x * 1 = _
    ring
  unfold AsymptoticStatistics.fisherInformation
  have hpw : ∀ x : Ω,
      (⟪h', AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.score1D γ x⟫_ℝ *
          ⟪h', AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.score1D γ x⟫_ℝ) *
          (T6_FinDimLAN.QMDPath.to1DParametricFamily γ).density 0 x =
        (P.rnDeriv γ.dominating x).toReal *
          (((γ.score : Lp ℝ 2 P) : Ω → ℝ) x) ^ 2 := by
    intro x
    rw [hinner x]
    change _ * _ * ((γ.curve 0).rnDeriv γ.dominating x).toReal = _
    rw [γ.curve_at_zero]
    ring
  rw [integral_congr_ae (ae_of_all _ hpw)]
  have hPdom : P ≪ γ.dominating := by
    simpa [γ.curve_at_zero] using γ.curve_absContinuous 0
  rw [MeasureTheory.integral_toReal_rnDeriv_mul hPdom]
  have hself :
      (⟪(γ.score : Lp ℝ 2 P), (γ.score : Lp ℝ 2 P)⟫_ℝ : ℝ) =
        ‖(γ.score : Lp ℝ 2 P)‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [MeasureTheory.L2.inner_def] at hself
  have hsq :
      (fun x => (⟪((γ.score : Lp ℝ 2 P) : Ω → ℝ) x,
        ((γ.score : Lp ℝ 2 P) : Ω → ℝ) x⟫_ℝ : ℝ)) =ᵐ[P]
      fun x => (((γ.score : Lp ℝ 2 P) : Ω → ℝ) x) ^ 2 := by
    filter_upwards with x
    rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [integral_congr_ae hsq] at hself
  exact hself

/-- One-dimensional convolution consequence in every score-normalized
direction.

Proof idea: 1D LAN for the selected path, Le Cam's third lemma, and the
regular shift identity.

The Gaussian location sample mean is an example with zero residual
convolution factor. -/
theorem rawRegularity_oneDim_convolution
    (A : ScoreOperator H P) (chiTilde : H)
    (ψ : Measure Ω → ℝ)
    (paths : ScorePathDerivativeData A chiTilde ψ)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hraw : RawRegularity A chiTilde ψ paths T_n)
    (b : H) (_hb : ‖A.toCLM b‖ = 1) :
    ∃ M : Measure ℝ, IsProbabilityMeasure M ∧
      hraw.limitLaw =
        gaussianReal 0 ⟨⟪chiTilde, b⟫_ℝ ^ 2, sq_nonneg _⟩ ∗ M := by
  classical
  let γ : QMDPath P := paths.selectedPath b
  let M := AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.to1DParametricFamily γ
  let d : ℝ := ⟪chiTilde, b⟫_ℝ
  let ψ₁ : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1) := fun θ =>
    EuclideanSpace.single 0 (ψ (γ.curve (θ 0)))
  let T₁ : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin 1) := fun n X =>
    EuclideanSpace.single 0 (T_n n X)
  let pr0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ :=
    innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  have hpr0 : ∀ y : EuclideanSpace ℝ (Fin 1), pr0 y = y.ofLp 0 := by
    intro y
    change (innerSL ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) y : ℝ) = _
    rw [innerSL_apply_apply, PiLp.inner_apply, Fin.sum_univ_one]
    simp only [Fin.isValue, PiLp.single_eq_same]
    change y.ofLp 0 * 1 = y.ofLp 0
    ring
  let singleLM : ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin 1) :=
    { toFun := EuclideanSpace.single 0
      map_add' := by
        intro x y
        ext i
        fin_cases i
        simp
      map_smul' := by
        intro c x
        ext i
        fin_cases i
        simp }
  let singleCLM : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    LinearMap.toContinuousLinearMap singleLM
  have hsingleCLM : ∀ r : ℝ, singleCLM r = EuclideanSpace.single 0 r := fun _ => rfl
  have hγ_deriv : HasDerivAt (fun t : ℝ => ψ (γ.curve t)) d 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    apply (paths.derivative_quotient b).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [zero_add, γ]
    rw [(paths.selectedPath b).curve_at_zero]
    change (ψ ((paths.selectedPath b).curve t) - ψ P) / t =
      t⁻¹ * (ψ ((paths.selectedPath b).curve t) - ψ P)
    rw [div_eq_mul_inv]
    ring
  let ψDot : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    singleCLM.comp ((ContinuousLinearMap.toSpanSingleton ℝ d).comp pr0)
  have hψ_diff : HasFDerivAt ψ₁ ψDot 0 := by
    have hγ_at_pr0 : HasFDerivAt (fun t : ℝ => ψ (γ.curve t))
        (ContinuousLinearMap.toSpanSingleton ℝ d) (pr0 0) := by
      simpa using hγ_deriv.hasFDerivAt
    have hcomp := singleCLM.hasFDerivAt.comp 0
      (hγ_at_pr0.comp 0 pr0.hasFDerivAt)
    convert! hcomp using 1
    · funext θ
      change EuclideanSpace.single 0 (ψ (γ.curve (θ.ofLp 0))) =
        singleCLM (ψ (γ.curve (pr0 θ)))
      rw [hsingleCLM, hpr0]
  have hT₁_meas : ∀ n, Measurable (T₁ n) := by
    intro n
    exact continuous_single_zero.measurable.comp (hraw.estimator_meas n)
  have hψ₁_meas_single := continuous_single_zero.measurable
  letI : IsProbabilityMeasure hraw.limitLaw := hraw.limit_isProbability
  let hReg : AsymptoticStatistics.ParametricFamily.RegularEstimatorSequence
      M γ.dominating 0 ψ₁ T₁ := by
    refine
      { limitDist := hraw.limitLaw.map (EuclideanSpace.single 0 :
          ℝ → EuclideanSpace ℝ (Fin 1))
        isProb := Measure.isProbabilityMeasure_map
          continuous_single_zero.measurable.aemeasurable
        tendsto := ?_ }
    intro h
    let a : ℝ := h.ofLp 0
    let γa : QMDPath P := reparamQMDPath (P := P) a γ
    let γ₀ : QMDPath P := paths.selectedPath (a • b)
    have hscore : γa.score = γ₀.score := by
      change a • γ.score = (paths.selectedPath (a • b)).score
      rw [show γ.score = A.toCLM b by exact paths.score_eq b]
      rw [paths.score_eq, map_smul]
    have hdiffa : Tendsto (fun t : ℝ => (ψ (γa.curve t) - ψ P) / t)
        (𝓝[≠] 0) (𝓝 (a * d)) := by
      simpa [γa, γ, d] using
        (reparam_derivative_quotient (A := A) chiTilde ψ paths b a)
    have hdiff₀ : Tendsto (fun t : ℝ => (ψ (γ₀.curve t) - ψ P) / t)
        (𝓝[≠] 0) (𝓝 (a * d)) := by
      have hh := paths.derivative_quotient (a • b)
      simpa [γ₀, d, inner_smul_right] using hh
    have hscalar := weakConverges_sameScore_commonDom ψ T_n hraw.estimator_meas
      hraw.limitLaw γa γ₀ hscore (a * d) hdiffa hdiff₀ (hraw.weak_limit (a • b))
    have hpushed := hscalar.map continuous_single_zero continuous_single_zero.measurable
    intro f
    have htest := hpushed f
    have hmeasScalar : ∀ n, Measurable (fun X : Fin n → Ω =>
        Real.sqrt n * (T_n n X - ψ (γa.curve ((Real.sqrt n)⁻¹)))) := fun n =>
      Measurable.const_mul ((hraw.estimator_meas n).sub measurable_const) _
    have hmeasure : ∀ n : ℕ,
        ((Measure.pi (fun _ : Fin n => γa.curve ((Real.sqrt n)⁻¹))).map
          (fun X : Fin n → Ω => Real.sqrt n *
            (T_n n X - ψ (γa.curve ((Real.sqrt n)⁻¹))))).map
            (EuclideanSpace.single (0 : Fin 1)) =
        (AsymptoticStatistics.AsymptoticRepresentation.productMeasure M γ.dominating
          ((0 : EuclideanSpace ℝ (Fin 1)) + (Real.sqrt n)⁻¹ • h) n).map
          (fun X => Real.sqrt n •
            (T₁ n X - ψ₁ ((0 : EuclideanSpace ℝ (Fin 1)) +
              (Real.sqrt n)⁻¹ • h))) := by
      intro n
      rw [Measure.map_map continuous_single_zero.measurable (hmeasScalar n)]
      have hbase :
          AsymptoticStatistics.AsymptoticRepresentation.productMeasure M γ.dominating
            ((0 : EuclideanSpace ℝ (Fin 1)) + (Real.sqrt n)⁻¹ • h) n =
          Measure.pi (fun _ : Fin n => γa.curve ((Real.sqrt n)⁻¹)) := by
        unfold AsymptoticStatistics.AsymptoticRepresentation.productMeasure
        congr 1
        funext i
        change γ.dominating.withDensity (fun x => ENNReal.ofReal
          ((γ.curve (((0 : EuclideanSpace ℝ (Fin 1)) +
            (Real.sqrt n)⁻¹ • h).ofLp 0)).rnDeriv γ.dominating x).toReal) =
          γa.curve ((Real.sqrt n)⁻¹)
        rw [qmdPath_withDensity_eq_curve]
        change γ.curve (((0 : EuclideanSpace ℝ (Fin 1)) +
          (Real.sqrt n)⁻¹ • h).ofLp 0) = γ.curve (a * (Real.sqrt n)⁻¹)
        congr 1
        change ((0 : EuclideanSpace ℝ (Fin 1)) + (Real.sqrt n)⁻¹ • h).ofLp 0 =
          a * (Real.sqrt n)⁻¹
        simp only [zero_add]
        change (Real.sqrt n)⁻¹ * h.ofLp 0 = a * (Real.sqrt n)⁻¹
        rw [show h.ofLp 0 = a by rfl]
        ring
      rw [hbase]
      congr 1
      funext X
      ext i
      fin_cases i
      rw [show γa.curve ((Real.sqrt n)⁻¹) =
          γ.curve ((Real.sqrt n)⁻¹ * h.ofLp 0) by
        change γ.curve (a * (Real.sqrt n)⁻¹) = _
        congr 1
        rw [show h.ofLp 0 = a by rfl]
        ring]
      simp [T₁, ψ₁]
    simpa only [hmeasure] using htest
  have hscore_meas : Measurable
      (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.score1D γ) := by
    exact continuous_single_zero.measurable.comp
      (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P)).measurable
  have hscore_norm : ‖(γ.score : Lp ℝ 2 P)‖ = 1 := by
    change ‖γ.score‖ = 1
    rw [show γ.score = A.toCLM b by exact paths.score_eq b]
    exact _hb
  have hJ_fisher : ∀ u v : EuclideanSpace ℝ (Fin 1),
      AsymptoticStatistics.fisherInformation M γ.dominating 0
        (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.score1D γ) u v =
      ⟪u, (WithLp.equiv 2 _).symm
        ((1 : Matrix (Fin 1) (Fin 1) ℝ).mulVec ((WithLp.equiv 2 _) v))⟫_ℝ := by
    intro u v
    let e : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
    have hu : u = u.ofLp 0 • e := by
      ext i
      fin_cases i
      simp [e]
    have hv : v = v.ofLp 0 • e := by
      ext i
      fin_cases i
      simp [e]
    have hunit := fisher_info_fin1_eq_score_norm_sq γ
    rw [hscore_norm, one_pow] at hunit
    rw [hu, hv]
    have hscale :
        AsymptoticStatistics.fisherInformation M γ.dominating 0
          (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.score1D γ)
          (u.ofLp 0 • e) (v.ofLp 0 • e) =
        (u.ofLp 0 * v.ofLp 0) *
          AsymptoticStatistics.fisherInformation M γ.dominating 0
            (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.score1D γ) e e := by
      unfold AsymptoticStatistics.fisherInformation
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [inner_smul_left, inner_smul_left]
      change (u.ofLp 0 * ⟪e,
          AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.score1D γ x⟫_ℝ) *
          (v.ofLp 0 * ⟪e,
            AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.score1D γ x⟫_ℝ) *
          M.density 0 x =
        (u.ofLp 0 * v.ofLp 0) *
          ((⟪e, AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.score1D γ x⟫_ℝ *
            ⟪e, AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.score1D γ x⟫_ℝ) *
            M.density 0 x)
      ring
    rw [hscale, hunit]
    simp only [Fin.isValue, mul_one, WithLp.equiv_apply, WithLp.ofLp_smul,
      PiLp.ofLp_single, Matrix.one_mulVec, WithLp.equiv_symm_apply,
      WithLp.toLp_smul, PiLp.toLp_single, PiLp.inner_apply,
      Finset.univ_unique, Fin.default_eq_zero, PiLp.smul_apply,
      PiLp.single_apply, smul_eq_mul, mul_ite, mul_zero,
      Finset.sum_singleton, reduceIte, e]
    change u.ofLp 0 * v.ofLp 0 = v.ofLp 0 * u.ofLp 0
    ring
  let D : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => d
  have hψDot_mat : ∀ h : EuclideanSpace ℝ (Fin 1),
      ψDot h = (WithLp.equiv 2 _).symm (D.mulVec ((WithLp.equiv 2 _) h)) := by
    intro h
    ext i
    fin_cases i
    simp [ψDot, D, singleCLM, singleLM, hpr0, Matrix.mulVec, dotProduct, d]
    ring
  obtain ⟨Mθ, hMθ, hconv⟩ :=
    AsymptoticStatistics.HajekLeCamConvolution.hajek_le_cam_convolution_theorem
      M γ.dominating 0
      (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.score1D γ)
      hscore_meas
      (AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDPath.dqm γ)
      (1 : Matrix (Fin 1) (Fin 1) ℝ) Matrix.PosDef.one hJ_fisher
      ψ₁ ψDot hψ_diff D hψDot_mat T₁ hT₁_meas hReg (qmdPath_isPDFOf γ)
  haveI : IsProbabilityMeasure Mθ := hMθ
  let C : Matrix (Fin 1) (Fin 1) ℝ := D *
    (1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ * D.transpose
  have hCentry : C 0 0 = d ^ 2 := by
    simp only [C, inv_one, Matrix.mul_one, Matrix.mul_apply, Matrix.transpose_apply,
      Finset.univ_unique, Finset.sum_singleton]
    simp [D, sq]
  have hCpsd : C.PosSemidef := by
    have h := Matrix.PosSemidef.mul_mul_conjTranspose_same
      ((Matrix.PosDef.one : Matrix.PosDef (1 : Matrix (Fin 1) (Fin 1) ℝ)).inv.posSemidef) D
    have htrans : D.conjTranspose = D.transpose := by
      ext i j
      simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    simpa [C, htrans] using h
  have hmapL :
      (hraw.limitLaw.map (EuclideanSpace.single (0 : Fin 1) :
        ℝ → EuclideanSpace ℝ (Fin 1))).map pr0 = hraw.limitLaw := by
    rw [Measure.map_map pr0.continuous.measurable continuous_single_zero.measurable]
    have hid : (pr0 ∘ EuclideanSpace.single (0 : Fin 1) : ℝ → ℝ) = id := by
      funext r
      change pr0 (EuclideanSpace.single (0 : Fin 1) r) = r
      rw [hpr0]
      simp
    rw [hid, Measure.map_id]
  have hgauss :
      (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) C).map pr0 =
        gaussianReal 0 ⟨d ^ 2, sq_nonneg d⟩ := by
    have hfun : (pr0 : EuclideanSpace ℝ (Fin 1) → ℝ) =
        fun y => ⟪EuclideanSpace.single (0 : Fin 1) (1 : ℝ), y⟫_ℝ := rfl
    rw [hfun, ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal _ hCpsd]
    congr 1
    apply Subtype.ext
    simp only [Fin.isValue, PiLp.ofLp_single, Matrix.mulVec_single,
      MulOpposite.op_one, one_smul, single_dotProduct, Matrix.col_apply,
      one_mul, NNReal.val_eq_coe, Real.coe_toNNReal']
    rw [hCentry, max_eq_left (sq_nonneg d)]
  refine ⟨Mθ.map pr0, Measure.isProbabilityMeasure_map
    pr0.continuous.measurable.aemeasurable, ?_⟩
  have hlimit : hReg.limitDist = hraw.limitLaw.map (EuclideanSpace.single 0 :
      ℝ → EuclideanSpace ℝ (Fin 1)) := rfl
  rw [hlimit] at hconv
  have happly := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 1)) => μ.map pr0) hconv
  change (hraw.limitLaw.map (EuclideanSpace.single 0 :
      ℝ → EuclideanSpace ℝ (Fin 1))).map pr0 =
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) C ∗ Mθ).map pr0 at happly
  rw [hmapL] at happly
  rw [MeasureTheory.Measure.map_conv_continuousLinearMap pr0] at happly
  change hraw.limitLaw =
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1)) C).map pr0 ∗
      Mθ.map pr0 at happly
  rw [hgauss] at happly
  simpa [d] using happly

/-- A probability characteristic function is nonzero in a neighborhood of
the origin.

Proof idea: continuity of `charFun` and `charFun μ 0 = 1`. -/
theorem charFun_nonzero_near_zero
    (L : Measure ℝ) [IsProbabilityMeasure L] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ → charFun L t ≠ 0 := by
  have hzero : charFun L 0 = (1 : ℂ) := by
    rw [charFun_zero]
    simp [Measure.real, isProbabilityMeasure_iff.mp (inferInstance :
      IsProbabilityMeasure L)]
  have hball : Metric.ball (1 : ℂ) 1 ∈ 𝓝 (charFun L 0) := by
    rw [hzero]
    exact Metric.ball_mem_nhds _ zero_lt_one
  have hev := MeasureTheory.continuous_charFun.continuousAt hball
  change {t : ℝ | charFun L t ∈ Metric.ball (1 : ℂ) 1} ∈ 𝓝 0 at hev
  rw [Metric.mem_nhds_iff] at hev
  obtain ⟨δ, hδ, hsub⟩ := hev
  refine ⟨δ, hδ, fun t ht hvanish => ?_⟩
  have htball : t ∈ Metric.ball (0 : ℝ) δ := by
    simpa [Real.dist_eq] using ht
  have hcf := hsub htball
  change charFun L t ∈ Metric.ball (1 : ℂ) 1 at hcf
  rw [hvanish] at hcf
  have hlt : (1 : ℝ) < 1 := by
    simpa only [Metric.mem_ball, dist_zero_left, norm_one] using hcf
  exact (lt_irrefl 1 hlt)

/-- Raw regularity forces the derivative to vanish on the kernel of the
score operator.  This makes the range functional well-defined. -/
theorem rawRegularity_kernel_derivative_zero
    (A : ScoreOperator H P) (chiTilde : H) (ψ : Measure Ω → ℝ)
    (paths : ScorePathDerivativeData A chiTilde ψ)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (_hraw : RawRegularity A chiTilde ψ paths T_n) :
    ∀ b : H, A.toCLM b = 0 → ⟪chiTilde, b⟫_ℝ = 0 := by
  classical
  intro b hb
  let γ : QMDPath P := paths.selectedPath b
  let γ₀ : QMDPath P := paths.selectedPath 0
  let d : ℝ := ⟪chiTilde, b⟫_ℝ
  have hscore : γ₀.score = γ.score := by
    rw [show γ₀.score = A.toCLM 0 by exact paths.score_eq 0,
      show γ.score = A.toCLM b by exact paths.score_eq b, map_zero, hb]
  let S_n : ∀ n, (Fin n → Ω) → ℝ := fun n X =>
    T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹))
  have hSmeas : ∀ n, Measurable (S_n n) := fun n =>
    (_hraw.estimator_meas n).sub measurable_const
  let zeroψ : Measure Ω → ℝ := fun _ => 0
  letI : IsProbabilityMeasure _hraw.limitLaw := _hraw.limit_isProbability
  have hsource : AsymptoticStatistics.WeakConverges
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => γ.curve ((Real.sqrt n)⁻¹))).map
          (fun X => Real.sqrt n * (S_n n X - zeroψ (γ.curve ((Real.sqrt n)⁻¹)))))
      _hraw.limitLaw := by
    simpa [S_n, zeroψ] using _hraw.weak_limit b
  have hzeroDiff : ∀ η : QMDPath P,
      Tendsto (fun t : ℝ => (zeroψ (η.curve t) - zeroψ P) / t)
        (𝓝[≠] 0) (𝓝 0) := by
    intro η
    simp [zeroψ]
  have htransfer := weakConverges_sameScore_commonDom zeroψ S_n hSmeas
    _hraw.limitLaw γ₀ γ hscore 0 (hzeroDiff γ₀) (hzeroDiff γ) hsource
  have htarget : AsymptoticStatistics.WeakConverges
      (fun n : ℕ =>
        (Measure.pi (fun _ : Fin n => γ₀.curve ((Real.sqrt n)⁻¹))).map
          (fun X => Real.sqrt n *
            (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹))))) _hraw.limitLaw := by
    simpa [S_n, zeroψ] using htransfer
  have hraw₀ := _hraw.weak_limit 0
  let s : ℕ → ℝ := fun n => Real.sqrt n *
    (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ (γ₀.curve ((Real.sqrt n)⁻¹)))
  have hs : Tendsto s atTop (𝓝 d) := by
    have hdiffγ := paths.derivative_quotient b
    have hdiffγ₀ := paths.derivative_quotient 0
    have hdiff : Tendsto (fun t : ℝ =>
        (ψ (γ.curve t) - ψ (γ₀.curve t)) / t) (𝓝[≠] 0) (𝓝 d) := by
      have hsub := hdiffγ.sub hdiffγ₀
      have hz : ⟪chiTilde, (0 : H)⟫_ℝ = 0 := inner_zero_right _
      have hsub' : Tendsto (fun t : ℝ =>
          (ψ (γ.curve t) - ψ P) / t - (ψ (γ₀.curve t) - ψ P) / t)
          (𝓝[≠] 0) (𝓝 d) := by
        simpa [γ, γ₀, d, hz] using hsub
      apply hsub'.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      field_simp
      ring
    have ht0 : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
      simpa using! (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
    have htne : ∀ᶠ n : ℕ in atTop, (Real.sqrt n)⁻¹ ≠ 0 := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      exact inv_ne_zero (Real.sqrt_pos.mpr (by exact_mod_cast
        (lt_of_lt_of_le one_pos hn))).ne'
    have htp : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨ht0, htne.mono fun _ hn => hn⟩
    have hc := hdiff.comp htp
    apply hc.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    change (ψ (γ.curve ((Real.sqrt n)⁻¹)) - ψ (γ₀.curve ((Real.sqrt n)⁻¹))) /
        (Real.sqrt n)⁻¹ = s n
    simp only [s]
    field_simp
  let μn : ℕ → Measure ℝ := fun n =>
    (Measure.pi (fun _ : Fin n => γ₀.curve ((Real.sqrt n)⁻¹))).map
      (fun X => Real.sqrt n * (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹))))
  let νn : ℕ → Measure ℝ := fun n =>
    (Measure.pi (fun _ : Fin n => γ₀.curve ((Real.sqrt n)⁻¹))).map
      (fun X => Real.sqrt n * (T_n n X - ψ (γ₀.curve ((Real.sqrt n)⁻¹))))
  have hFmeas : ∀ n, Measurable (fun X : Fin n → Ω => Real.sqrt n *
      (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹)))) := fun n =>
    Measurable.const_mul ((_hraw.estimator_meas n).sub measurable_const) _
  haveI hμprob : ∀ n, IsProbabilityMeasure (μn n) := by
    intro n
    haveI : ∀ _ : Fin n, IsProbabilityMeasure (γ₀.curve ((Real.sqrt n)⁻¹)) :=
      fun _ => γ₀.curve_isProbability _
    exact Measure.isProbabilityMeasure_map (hFmeas n).aemeasurable
  have hνmeas : ∀ n, Measurable (fun X : Fin n → Ω => Real.sqrt n *
      (T_n n X - ψ (γ₀.curve ((Real.sqrt n)⁻¹)))) := fun n =>
    Measurable.const_mul ((_hraw.estimator_meas n).sub measurable_const) _
  haveI hνprob : ∀ n, IsProbabilityMeasure (νn n) := by
    intro n
    haveI : ∀ _ : Fin n, IsProbabilityMeasure (γ₀.curve ((Real.sqrt n)⁻¹)) :=
      fun _ => γ₀.curve_isProbability _
    exact Measure.isProbabilityMeasure_map (hνmeas n).aemeasurable
  let μp : ℕ → ProbabilityMeasure ℝ := fun n => ⟨μn n, hμprob n⟩
  let νp : ℕ → ProbabilityMeasure ℝ := fun n => ⟨νn n, hνprob n⟩
  let Lp : ProbabilityMeasure ℝ := ⟨_hraw.limitLaw, _hraw.limit_isProbability⟩
  have hμweak : AsymptoticStatistics.WeakConverges μn _hraw.limitLaw := by
    simpa [μn] using htarget
  have hνweak : AsymptoticStatistics.WeakConverges νn _hraw.limitLaw := by
    simpa [νn, γ₀] using hraw₀
  have hμt : Tendsto μp atTop (𝓝 Lp) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    exact hμweak
  have hνt : Tendsto νp atTop (𝓝 Lp) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    exact hνweak
  have hmap : ∀ n, νn n = (μn n).map (fun x => x + s n) := by
    intro n
    rw [Measure.map_map (by fun_prop) (hFmeas n)]
    change (Measure.pi (fun _ : Fin n => γ₀.curve ((Real.sqrt n)⁻¹))).map
        (fun X => Real.sqrt n * (T_n n X - ψ (γ₀.curve ((Real.sqrt n)⁻¹)))) =
      (Measure.pi (fun _ : Fin n => γ₀.curve ((Real.sqrt n)⁻¹))).map
        ((fun x => x + s n) ∘ fun X =>
          Real.sqrt n * (T_n n X - ψ (γ.curve ((Real.sqrt n)⁻¹))))
    congr 1
    funext X
    simp only [Function.comp_apply, s]
    ring
  have hid : ∀ t : ℝ, charFun _hraw.limitLaw t =
      charFun _hraw.limitLaw t * Complex.exp ((d * t : ℝ) * Complex.I) := by
    intro t
    have hμcf := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hμt) t
    have hνcf := (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hνt) t
    have hexp : Tendsto (fun n => Complex.exp ((s n * t : ℝ) * Complex.I)) atTop
        (𝓝 (Complex.exp ((d * t : ℝ) * Complex.I))) := by
      exact Tendsto.comp Complex.continuous_exp.continuousAt
        (((hs.mul_const t).ofReal).mul_const Complex.I)
    have hprod := hμcf.mul hexp
    have hrel : (fun n => charFun (νp n) t) =
        fun n => charFun (μp n) t * Complex.exp ((s n * t : ℝ) * Complex.I) := by
      funext n
      change charFun (νn n) t = _
      rw [hmap n, charFun_map_add_const]
      congr 2
      change (((t * s n : ℝ) : ℂ) * Complex.I) =
        (((s n * t : ℝ) : ℂ) * Complex.I)
      congr 1
      push_cast
      ring
    rw [hrel] at hνcf
    exact tendsto_nhds_unique hνcf hprod
  obtain ⟨δ, hδ, hnonzero⟩ := charFun_nonzero_near_zero _hraw.limitLaw
  have hexpOne : (fun t : ℝ => Complex.exp ((d * t : ℝ) * Complex.I)) =ᶠ[𝓝 0]
      fun _ => (1 : ℂ) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
    have habs : |t| < δ := by simpa [Real.dist_eq] using ht
    have hcf := hid t
    have hn := hnonzero t habs
    apply mul_left_cancel₀ hn
    simpa using hcf.symm
  have hsin : (fun t : ℝ => Real.sin (d * t)) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [hexpOne] with t ht
    have him := congrArg Complex.im ht
    have him' : (Complex.exp (((d * t : ℝ) : ℂ) * Complex.I)).im = 0 := by
      convert him using 1
      simp
    simpa only [Complex.exp_ofReal_mul_I_im] using him'
  have hsinDeriv : HasDerivAt (fun t : ℝ => Real.sin (d * t)) d 0 := by
    simpa using! (Real.hasDerivAt_sin (d * 0)).comp 0
      (hasDerivAt_const_mul (x := (0 : ℝ)) d)
  have hsinDerivZero : HasDerivAt (fun t : ℝ => Real.sin (d * t)) 0 0 :=
    (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))).congr_of_eventuallyEq hsin
  exact hsinDeriv.unique hsinDerivZero

/-- The one-dimensional convolution identities force a uniform bound on
the derivative over score-normalized directions.

Proof idea: evaluate characteristic functions at a fixed nonzero point
where the common limit charFun is nonzero; the Gaussian factor then bounds
`abs (inner chiTilde b)` uniformly. -/
theorem rawRegularity_uniform_derivative_bound
    (A : ScoreOperator H P) (chiTilde : H)
    (ψ : Measure Ω → ℝ)
    (paths : ScorePathDerivativeData A chiTilde ψ)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hraw : RawRegularity A chiTilde ψ paths T_n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ b : H, |⟪chiTilde, b⟫_ℝ| ≤ C * ‖A.toCLM b‖ := by
  letI : IsProbabilityMeasure hraw.limitLaw := hraw.limit_isProbability
  obtain ⟨δ, hδ, hnonzero⟩ := charFun_nonzero_near_zero hraw.limitLaw
  let t : ℝ := δ / 2
  have ht : 0 < t := by simp [t, hδ]
  have htδ : |t| < δ := by rw [abs_of_pos ht]; simp [t, hδ]
  let q : ℝ := ‖charFun hraw.limitLaw t‖
  have hq : 0 < q := norm_pos_iff.mpr (hnonzero t htδ)
  have hq_one : q ≤ 1 := norm_charFun_le_one t
  have hlog : 0 ≤ -Real.log q := by
    have := Real.log_nonpos hq.le hq_one
    linarith
  let K : ℝ := (-2 * Real.log q) / t ^ 2
  have hK : 0 ≤ K := by
    dsimp [K]
    exact div_nonneg (by linarith) (sq_nonneg _)
  let C : ℝ := Real.sqrt K
  have hnormed : ∀ c : H, ‖A.toCLM c‖ = 1 → |⟪chiTilde, c⟫_ℝ| ≤ C := by
    intro c hc
    obtain ⟨N, hNprob, hconv⟩ :=
      rawRegularity_oneDim_convolution A chiTilde ψ paths T_n hraw c hc
    letI : IsProbabilityMeasure N := hNprob
    have hv : 0 ≤ ⟪chiTilde, c⟫_ℝ ^ 2 := sq_nonneg _
    let v : NNReal := ⟨(⟪chiTilde, c⟫_ℝ) ^ 2, hv⟩
    have hcf := congrArg (fun μ : Measure ℝ => charFun μ t) hconv
    change charFun hraw.limitLaw t =
      charFun (gaussianReal 0 v ∗ N) t at hcf
    rw [charFun_conv, charFun_gaussianReal] at hcf
    have hcfNorm := congrArg (fun z : ℂ => ‖z‖) hcf
    have hgauss :
        ‖Complex.exp (((t : ℂ) * (0 : ℂ) * Complex.I) -
          (v : ℂ) *
            (t : ℂ) ^ 2 / 2)‖ =
          Real.exp (-(⟪chiTilde, c⟫_ℝ ^ 2 * t ^ 2 / 2)) := by
      rw [Complex.norm_exp]
      congr 1
      norm_num [v, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, pow_two]
      exact Or.inl rfl
    have hqle : q ≤ Real.exp (-(⟪chiTilde, c⟫_ℝ ^ 2 * t ^ 2 / 2)) := by
      change ‖charFun hraw.limitLaw t‖ ≤ _
      rw [show ‖charFun hraw.limitLaw t‖ =
          ‖Complex.exp (((t : ℂ) * (0 : ℂ) * Complex.I) -
            (v : ℂ) *
              (t : ℂ) ^ 2 / 2) * charFun N t‖ by exact hcfNorm,
        norm_mul, hgauss]
      exact mul_le_of_le_one_right (Real.exp_nonneg _)
        (norm_charFun_le_one t)
    have hlogle : Real.log q ≤ -(⟪chiTilde, c⟫_ℝ ^ 2 * t ^ 2 / 2) :=
      (Real.log_le_iff_le_exp hq).mpr hqle
    have hsq : ⟪chiTilde, c⟫_ℝ ^ 2 ≤ K := by
      have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
      dsimp [K]
      apply (le_div_iff₀ ht2).mpr
      nlinarith
    exact (Real.abs_le_sqrt hsq).trans_eq rfl
  refine ⟨C, Real.sqrt_nonneg _, fun b => ?_⟩
  by_cases hbzero : ‖A.toCLM b‖ = 0
  · have hAb : A.toCLM b = 0 := norm_eq_zero.mp hbzero
    rw [rawRegularity_kernel_derivative_zero A chiTilde ψ paths T_n hraw b hAb,
      abs_zero, hbzero, mul_zero]
  · have hbpos : 0 < ‖A.toCLM b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hbzero)
    let c : H := ‖A.toCLM b‖⁻¹ • b
    have hc : ‖A.toCLM c‖ = 1 := by
      rw [show A.toCLM c = ‖A.toCLM b‖⁻¹ • A.toCLM b by
        simp [c], norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hbpos,
        inv_mul_cancel₀ hbzero]
    have hcbd := hnormed c hc
    have hinner : ⟪chiTilde, c⟫_ℝ = ‖A.toCLM b‖⁻¹ * ⟪chiTilde, b⟫_ℝ := by
      simp [c, inner_smul_right]
    rw [hinner, abs_mul, abs_inv, abs_of_pos hbpos] at hcbd
    have hC : 0 ≤ C := Real.sqrt_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hcbd hbpos.le
    field_simp at hmul
    simpa [mul_comm] using hmul

/-- A uniformly bounded range functional is continuous on the actual score
range and hence gives `DifferentiableRelScoreRange`.

The value on `A b` is well defined by the bound, which also gives continuity
and hence a continuous linear map. -/
theorem differentiableRelScoreRange_of_uniform_bound
    (A : ScoreOperator H P) (chiTilde : H)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ b : H, |⟪chiTilde, b⟫_ℝ| ≤ C * ‖A.toCLM b‖) :
    DifferentiableRelScoreRange A chiTilde := by
  classical
  obtain ⟨C, hC, hbound⟩ := hbound
  let repr : A.toCLM.range → H := fun y => Classical.choose y.property
  have hrepr (y : A.toCLM.range) : A.toCLM (repr y) = y :=
    Classical.choose_spec y.property
  have hker (z : H) (hz : A.toCLM z = 0) : ⟪chiTilde, z⟫_ℝ = 0 := by
    have hzbound := hbound z
    rw [hz, norm_zero, mul_zero] at hzbound
    exact abs_eq_zero.mp (le_antisymm hzbound (abs_nonneg _))
  let L : A.toCLM.range →ₗ[ℝ] ℝ :=
    { toFun := fun y => ⟪chiTilde, repr y⟫_ℝ
      map_add' := by
        intro x y
        have hd : A.toCLM (repr (x + y) - (repr x + repr y)) = 0 := by
          rw [map_sub, map_add, hrepr, hrepr, hrepr]
          simp
        exact sub_eq_zero.mp (by
          simpa [inner_sub_right, inner_add_right] using
            hker (repr (x + y) - (repr x + repr y)) hd)
      map_smul' := by
        intro r y
        have hd : A.toCLM (repr (r • y) - r • repr y) = 0 := by
          rw [map_sub, map_smul, hrepr, hrepr]
          simp
        exact sub_eq_zero.mp (by
          simpa [inner_sub_right, inner_smul_right] using
            hker (repr (r • y) - r • repr y) hd) }
  have hLbound (y : A.toCLM.range) : ‖L y‖ ≤ C * ‖y‖ := by
    rw [Real.norm_eq_abs]
    change |⟪chiTilde, repr y⟫_ℝ| ≤ C * ‖y‖
    simpa [hrepr y] using hbound (repr y)
  refine ⟨L.mkContinuous C hLbound, fun b => ?_⟩
  let y : A.toCLM.range := ⟨A.toCLM b, ⟨b, rfl⟩⟩
  have hd : A.toCLM (repr y - b) = 0 := by
    rw [map_sub, hrepr]
    simp [y]
  have hsame := hker (repr y - b) hd
  change L y = ⟪chiTilde, b⟫_ℝ
  change ⟪chiTilde, repr y⟫_ℝ = ⟪chiTilde, b⟫_ℝ
  exact sub_eq_zero.mp (by simpa [inner_sub_right] using hsame)

/-- Raw regularity implies differentiability relative to the actual score
range.  This is the probability-to-functional-analysis bridge of 25.32. -/
theorem differentiableRelScoreRange_of_rawRegularity
    (A : ScoreOperator H P) (chiTilde : H)
    (ψ : Measure Ω → ℝ)
    (paths : ScorePathDerivativeData A chiTilde ψ)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (hraw : RawRegularity A chiTilde ψ paths T_n) :
    DifferentiableRelScoreRange A chiTilde := by
  exact differentiableRelScoreRange_of_uniform_bound A chiTilde
    (rawRegularity_uniform_derivative_bound A chiTilde ψ paths T_n hraw)

/-- vdV Theorem 25.32: if `chiTilde` is not in the actual range of the
adjoint score operator, no raw-regular estimator sequence exists.

Proof idea: the preceding bridge gives differentiability on `range A`;
`mem_range_adjoint_of_differentiable_unrestricted` then contradicts the
stated range obstruction.  No closed-range assumption is present.

For a finite-dimensional identity score operator, every `chiTilde` is in the
adjoint range and the Gaussian sample mean is raw regular. The negative premise is
therefore correctly false in that model. -/
theorem no_rawRegularity_of_not_mem_range_adjoint
    (A : ScoreOperator H P)
    -- LEAN-ONLY: an explicit adjoint representative and its defining identity.
    (Astar : ↥(L2ZeroMean P) →L[ℝ] H)
    (h_adj : ∀ (b : H) (y : ↥(L2ZeroMean P)),
      ⟪Astar y, b⟫_ℝ = ⟪y, A.toCLM b⟫_ℝ)
    (chiTilde : H)
    -- USER-INPUT: the parameter derivative is outside the adjoint range;
    -- vdV Theorem 25.32.
    (h_not_mem : chiTilde ∉ (Astar.range : Submodule ℝ H))
    (ψ : Measure Ω → ℝ)
    -- USER-INPUT: the score-direction family realizes the derivative represented by `chiTilde`.
    (paths : ScorePathDerivativeData A chiTilde ψ)
    (T_n : ∀ n, (Fin n → Ω) → ℝ) :
    RawRegularity A chiTilde ψ paths T_n → False := by
  intro hraw
  exact h_not_mem (mem_range_adjoint_of_differentiable_unrestricted
    A Astar h_adj chiTilde
    (differentiableRelScoreRange_of_rawRegularity
      A chiTilde ψ paths T_n hraw))

end AsymptoticStatistics.LowerBounds.ScoreOperatorRegularityObstruction
