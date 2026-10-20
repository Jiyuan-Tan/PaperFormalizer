module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.ForMathlib.Probability.IsonormalProcess

@[expose] public section

/-!
# Gaussian laws under L² closure and measure-preserving transport

Reusable closure and transport lemmas for Gaussian random elements.
-/

namespace ProbabilityTheory

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

/-! A local closure brick: a centred Gaussian sequence converging in `L²`
has a centred Gaussian limit.  This is the scalar ingredient needed because
the regression part of an influence function generally lies only in the
closed, rather than algebraic, span of the bridge coordinates. -/

/-- A centered scalar Gaussian law is closed under convergence in `L²(μ)`.
This supplies Gaussianity for limits obtained from a closed Hilbert span. -/
theorem hasGaussianLaw_of_centered_tendsto_L2
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (Y : ℕ → Lp ℝ 2 μ) (Z : Lp ℝ 2 μ)
    (hY_gauss : ∀ n, HasGaussianLaw (Y n : S → ℝ) μ)
    (hY_mean : ∀ n, ∫ x, (Y n : S → ℝ) x ∂μ = 0)
    (hYZ : Tendsto Y atTop (nhds Z)) :
    HasGaussianLaw (Z : S → ℝ) μ := by
  classical
  have hmeas : TendstoInMeasure μ (fun n => (Y n : S → ℝ)) atTop (Z : S → ℝ) :=
    tendstoInMeasure_of_tendsto_Lp hYZ
  have hZmeas : AEMeasurable (Z : S → ℝ) μ := (Lp.aestronglyMeasurable Z).aemeasurable
  have hcf : ∀ (W : S → ℝ) (t : ℝ), AEMeasurable W μ →
      charFun (μ.map W) t = ∫ x, Complex.exp (↑(t * W x) * Complex.I) ∂μ := by
    intro W t hW
    rw [charFun_apply, integral_map hW (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [] with x
    norm_cast
  suffices hChar : ∀ t : ℝ, charFun (μ.map (Z : S → ℝ)) t =
      Complex.exp (((-(‖Z‖ ^ 2 * t ^ 2) / 2 : ℝ) : ℂ)) by
    refine ⟨isGaussian_iff_gaussian_charFun.mpr
      ⟨0, ‖Z‖ ^ 2 • ContinuousLinearMap.mul ℝ ℝ,
        ⟨⟨fun x y => ?_⟩, ⟨fun x => ?_⟩⟩, ?_⟩⟩
    · simp only [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.mul_apply', smul_eq_mul]
      ring
    · simp only [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.mul_apply', smul_eq_mul]
      exact mul_nonneg (sq_nonneg _) (mul_self_nonneg x)
    · intro t
      rw [hChar t]
      congr 1
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply', smul_eq_mul,
        inner_zero_right]
      push_cast
      ring
  intro t
  have hA : Tendsto (fun n => charFun (μ.map (Y n : S → ℝ)) t) atTop
      (nhds (charFun (μ.map (Z : S → ℝ)) t)) := by
    have hgcont : Continuous (fun z : ℝ => Complex.exp (↑(t * z) * Complex.I)) := by
      fun_prop
    have hgb : ∀ z : ℝ, ‖Complex.exp (↑(t * z) * Complex.I)‖ ≤ 1 := by
      intro z
      rw [Complex.norm_exp]
      simp [mul_comm, Complex.I_re, Complex.I_im]
    have hconv := IsonormalProcess.tendsto_integral_comp_of_tendstoInMeasure
      (fun n => (hY_gauss n).aemeasurable) hmeas hgcont hgb
    simpa only [hcf _ t (hY_gauss _).aemeasurable, hcf _ t hZmeas] using hconv
  have hform : ∀ n, charFun (μ.map (Y n : S → ℝ)) t =
      Complex.exp ((↑(-(t ^ 2 * ‖Y n‖ ^ 2) / 2 : ℝ) : ℂ)) := by
    intro n
    rw [(hY_gauss n).charFun_map_eq t]
    have hinner : (fun x => (⟪t, (Y n : S → ℝ) x⟫_ℝ : ℝ)) =
        fun x => t * (Y n : S → ℝ) x := by
      funext x
      change (Y n : S → ℝ) x * t = t * (Y n : S → ℝ) x
      ring
    rw [hinner, integral_const_mul, hY_mean n, mul_zero,
      variance_const_mul]
    have hvar : Var[(Y n : S → ℝ); μ] = ‖Y n‖ ^ 2 := by
      rw [variance_of_integral_eq_zero
        (Lp.aestronglyMeasurable (Y n)).aemeasurable (hY_mean n),
        ← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    rw [hvar]
    push_cast
    ring_nf
  refine tendsto_nhds_unique hA ?_
  rw [Filter.tendsto_congr hform]
  refine (Complex.continuous_exp.tendsto _).comp
    ((Complex.continuous_ofReal.tendsto _).comp ?_)
  have hnorm := (hYZ.norm.pow 2)
  convert (Filter.Tendsto.div_const
      (Filter.Tendsto.neg ((tendsto_const_nhds (x := t ^ 2)).mul hnorm)) 2) using 1
  all_goals ring_nf

/-- A measurable Banach-valued random element is Gaussian when every continuous
linear functional applied to it has a scalar Gaussian law. -/
theorem hasGaussianLaw_of_forall_dual
    {S E : Type*} [MeasurableSpace S] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure S) (X : S → E)
    (hX : Measurable X)
    (hdual : ∀ L : StrongDual ℝ E, HasGaussianLaw (L ∘ X) μ) :
    HasGaussianLaw X μ := by
  refine ⟨⟨fun L => ?_⟩⟩
  have hL := (hdual L).isGaussian_map.map_eq_gaussianReal
    (ContinuousLinearMap.id ℝ ℝ)
  rw [Measure.map_map L.continuous.measurable hX]
  have hid : ⇑(ContinuousLinearMap.id ℝ ℝ) = id := rfl
  rw [hid, Measure.map_id] at hL
  have hmean : (∫ x : E, L x ∂(μ.map X)) =
      ∫ x : ℝ, id x ∂(μ.map (⇑L ∘ X)) := by
    rw [integral_map hX.aemeasurable (by fun_prop),
      integral_map (hdual L).aemeasurable (by fun_prop)]
    rfl
  have hvar : Var[⇑L; μ.map X] = Var[id; μ.map (⇑L ∘ X)] := by
    rw [variance_map L.continuous.aemeasurable hX.aemeasurable,
      variance_map measurable_id.aemeasurable (hdual L).aemeasurable]
    rfl
  rw [hmean, hvar]
  exact hL

/-- Pulling a Gaussian random element back along a measure-preserving map
preserves its Gaussian law. -/
theorem hasGaussianLaw_comp_measurePreserving
    {S A E : Type*} {mS : MeasurableSpace S} {mA : MeasurableSpace A}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    {μ : Measure S} {ρ : Measure A} {T : S → A} {X : A → E}
    (hX : HasGaussianLaw X ρ) (hT : MeasurePreserving T μ ρ) :
    HasGaussianLaw (X ∘ T) μ := by
  refine ⟨?_⟩
  have hXmap : AEMeasurable X (μ.map T) := by
    rw [hT.map_eq]
    exact hX.aemeasurable
  rw [← AEMeasurable.map_map_of_aemeasurable
      hXmap hT.measurable.aemeasurable, hT.map_eq]
  exact hX.isGaussian_map


end ProbabilityTheory
