module
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros

@[expose] public section

/-!
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junwei Lu, Claude Opus 4.7
-/

/-!
# Bivariate MGF uniqueness on `ℝ × ℝ`

This file ships a single theorem `bivariate_mgf_uniqueness`: two probability
measures `μ ν : Measure (ℝ × ℝ)` agreeing on the bivariate generating
identity
```
∫ exp(I · u · t + s · z) dμ = ∫ exp(I · u · t + s · z) dν   ∀ (u, s : ℝ)
```
are equal, provided their snd-marginals are the *same* `gaussianReal 0 σ²`
distribution (so that `exp(s · z)` is integrable for every real `s` against
both, enabling the analytic continuation in `s`).

## Strategy

For each fixed real `u`, define
```
F_u^μ(s) := ∫ p, exp(I·u·p.1 + s·p.2) dμ            s : ℂ
F_u^ν(s) := ∫ p, exp(I·u·p.1 + s·p.2) dν
```
Both are entire functions of `s : ℂ` because the Gaussian-tail snd-marginal
makes `s ↦ ∫ exp(s · p.2) dμ` analytic on ℂ; the bounded `exp(I·u·p.1)` factor
contributes an envelope of unit modulus and does not affect the dominator.

By hypothesis `F_u^μ = F_u^ν` on the real axis. The identity theorem
(Mathlib's `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`) extends the
equality to all of ℂ. Evaluating at `s = -I · v` for arbitrary `v : ℝ`
yields, for all real `(u, v)`,
```
∫ exp(I · u · p.1 - I · v · p.2) dμ = ∫ exp(I · u · p.1 - I · v · p.2) dν
```
which is the bivariate characteristic function identity. Pushing forward via
the measurable equivalence `MeasurableEquiv.toLp 2 (ℝ × ℝ)` and applying
`Measure.ext_of_charFun` on `WithLp 2 (ℝ × ℝ)` (a complete inner product
space) closes.

This is the generic two-measure form of the analytic MGF-to-characteristic-function
factorisation used by `JointMGFAnalyticClosure.joint_mgf_to_charFn_factorisation`.

## Public API

* `bivariate_mgf_uniqueness` — the headline.
-/

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped ENNReal NNReal InnerProductSpace

namespace AsymptoticStatistics.ForMathlib.BivariateMGFUniqueness

/-- Helper lemma: for any probability measure `μ` on `ℝ × ℝ` whose snd-marginal
is `gaussianReal 0 σ²`, and any real `t`, `exp (t * p.2)` is `μ`-integrable. -/
private lemma integrable_exp_snd
    {μ : Measure (ℝ × ℝ)} (σ_sq : ℝ≥0)
    (h_snd : μ.map Prod.snd = ProbabilityTheory.gaussianReal 0 σ_sq)
    (t : ℝ) :
    Integrable (fun p : ℝ × ℝ => Real.exp (t * p.2)) μ := by
  have h_g : Integrable (fun x : ℝ => Real.exp (t * x))
      (ProbabilityTheory.gaussianReal 0 σ_sq) :=
    ProbabilityTheory.integrable_exp_mul_gaussianReal t
  have h_g' : Integrable (fun x : ℝ => Real.exp (t * x)) (μ.map Prod.snd) := by
    rw [h_snd]; exact h_g
  have h_meas_snd : AEMeasurable (fun p : ℝ × ℝ => p.2) μ :=
    measurable_snd.aemeasurable
  exact h_g'.comp_aemeasurable h_meas_snd

/-- Helper lemma: for any probability measure `μ` on `ℝ × ℝ` whose snd-marginal
is `gaussianReal 0 σ²`, the parametric `s ↦ ∫ exp(I·u·p.1 + s·p.2) dμ` is
*entire* on ℂ. -/
private lemma F_u_analytic
    {μ : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ] (σ_sq : ℝ≥0)
    (h_snd : μ.map Prod.snd = ProbabilityTheory.gaussianReal 0 σ_sq)
    (u : ℝ) :
    AnalyticOnNhd ℂ
      (fun s' : ℂ =>
        ∫ p : ℝ × ℝ,
          Complex.exp (Complex.I * (u : ℂ) * (p.1 : ℂ) + s' * (p.2 : ℂ)) ∂μ)
      Set.univ := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
  intro s₀ _hs₀
  set F_param : ℂ → (ℝ × ℝ) → ℂ := fun s' p =>
    Complex.exp (Complex.I * (u : ℂ) * (p.1 : ℂ) + s' * (p.2 : ℂ)) with hF_param_def
  set F'_param : ℂ → (ℝ × ℝ) → ℂ := fun s' p =>
    (p.2 : ℂ) * Complex.exp (Complex.I * (u : ℂ) * (p.1 : ℂ) +
                              s' * (p.2 : ℂ)) with hF'_param_def
  set bound : (ℝ × ℝ) → ℝ := fun p =>
    |p.2| * Real.exp (s₀.re * p.2 + (1 / 2) * |p.2|) with hbound_def
  have h_int_pos : Integrable
      (fun p : ℝ × ℝ => Real.exp ((s₀.re + 1) * p.2)) μ :=
    integrable_exp_snd σ_sq h_snd _
  have h_int_neg : Integrable
      (fun p : ℝ × ℝ => Real.exp ((s₀.re - 1) * p.2)) μ :=
    integrable_exp_snd σ_sq h_snd _
  have h_bound_int : Integrable bound μ := by
    have h := ProbabilityTheory.integrable_pow_abs_mul_exp_add_of_integrable_exp_mul
      (X := fun p : ℝ × ℝ => p.2) (μ := μ) (v := s₀.re) (t := 1) (x := 1/2)
      h_int_pos h_int_neg (by norm_num) (by simp; norm_num) 1
    simpa [bound, pow_one] using h
  have h_diff_pointwise : ∀ p : ℝ × ℝ, ∀ s' : ℂ,
      HasDerivAt (fun s' : ℂ => F_param s' p) (F'_param s' p) s' := by
    intro p s'
    simp only [hF_param_def, hF'_param_def]
    have h_lin : HasDerivAt
        (fun s' : ℂ => Complex.I * (u : ℂ) * (p.1 : ℂ) + s' * (p.2 : ℂ))
        ((p.2 : ℂ)) s' := by
      have h1 : HasDerivAt (fun s' : ℂ => s' * (p.2 : ℂ)) (p.2 : ℂ) s' := by
        simpa using (hasDerivAt_id s').mul_const (p.2 : ℂ)
      have h2 : HasDerivAt
          (fun s' : ℂ => Complex.I * (u : ℂ) * (p.1 : ℂ) + s' * (p.2 : ℂ))
          (0 + (p.2 : ℂ)) s' :=
        (hasDerivAt_const s' (Complex.I * (u : ℂ) * (p.1 : ℂ))).add h1
      simpa using h2
    have h_exp_deriv := h_lin.cexp
    convert! h_exp_deriv using 1
    ring
  have h_bound_pointwise : ∀ p : ℝ × ℝ, ∀ s' ∈ Metric.ball s₀ (1/2 : ℝ),
      ‖F'_param s' p‖ ≤ bound p := by
    intro p s' hs'
    simp only [hF'_param_def, hbound_def]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    gcongr
    have h_re : (Complex.I * (u : ℂ) * (p.1 : ℂ) + s' * (p.2 : ℂ)).re
        = s'.re * p.2 := by
      simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
    rw [h_re]
    have hs'_eq : s'.re = s₀.re + (s'.re - s₀.re) := by ring
    rw [hs'_eq, add_mul]
    gcongr _ + ?_
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    gcongr
    have h_re_diff : s'.re - s₀.re = (s' - s₀).re := by simp [Complex.sub_re]
    rw [h_re_diff]
    refine (Complex.abs_re_le_norm _).trans ?_
    simp only [Metric.mem_ball, dist_eq_norm] at hs'
    exact hs'.le
  have h_meas_param : ∀ s : ℂ, AEStronglyMeasurable (F_param s) μ := by
    intro s
    simp only [hF_param_def]
    fun_prop
  have h_meas'_param : AEStronglyMeasurable (F'_param s₀) μ := by
    simp only [hF'_param_def]
    fun_prop
  have h_int_F_s₀ : Integrable (F_param s₀) μ := by
    rw [← integrable_norm_iff (h_meas_param s₀)]
    have h_norm_eq : ∀ p : ℝ × ℝ,
        ‖F_param s₀ p‖ = Real.exp (s₀.re * p.2) := by
      intro p
      simp only [hF_param_def, Complex.norm_exp]
      congr 1
      simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.ofReal_re, Complex.ofReal_im]
    simp_rw [h_norm_eq]
    exact integrable_exp_snd σ_sq h_snd _
  have h_deriv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (𝕜 := ℂ) (E := ℂ) (s := Metric.ball s₀ (1/2 : ℝ))
    (x₀ := s₀) (F := F_param) (F' := F'_param) (bound := bound)
    (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1/2))
    (Filter.Eventually.of_forall (fun s => h_meas_param s))
    h_int_F_s₀
    h_meas'_param
    (Filter.Eventually.of_forall (fun p s' hs' => h_bound_pointwise p s' hs'))
    h_bound_int
    (Filter.Eventually.of_forall (fun p s' _ => h_diff_pointwise p s'))).2
  exact h_deriv.differentiableAt.differentiableWithinAt

/-- Identity theorem on the real axis: any two entire `f g : ℂ → ℂ` agreeing on
all real values are equal. -/
private lemma eq_of_real_eq_of_analytic {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (hg : AnalyticOnNhd ℂ g Set.univ)
    (h_real : ∀ s' : ℝ, f (s' : ℂ) = g (s' : ℂ)) :
    ∀ s' : ℂ, f s' = g s' := by
  have h_freq_eq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z := by
    have h_seq_punctured :
        Filter.Tendsto (fun n : ℕ => ((1 / (n + 1 : ℝ) : ℝ) : ℂ))
          Filter.atTop (𝓝[≠] (0 : ℂ)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have h_real_t :
            Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ) : ℝ))
              Filter.atTop (𝓝 (0 : ℝ)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        exact_mod_cast (Complex.continuous_ofReal.tendsto _).comp h_real_t
      · refine Filter.Eventually.of_forall (fun n => ?_)
        have h_pos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by
          positivity
        intro h_mem
        rw [Set.mem_singleton_iff] at h_mem
        have h_real_zero : (1 / ((n : ℝ) + 1) : ℝ) = 0 := by
          exact_mod_cast h_mem
        linarith
    exact h_seq_punctured.frequently
      (Filter.Frequently.of_forall (fun n => h_real _))
  intro s'
  exact hf.eqOn_of_preconnected_of_frequently_eq hg
    isPreconnected_univ (Set.mem_univ (0 : ℂ)) h_freq_eq (Set.mem_univ s')

/-- Inner product on `WithLp 2 (ℝ × ℝ)` reduces, after `toLp`, to a pointwise
sum of products of components. The orientation matches Mathlib's
`RCLike.inner_apply` convention `⟪a, b⟫_ℝ = b * a` on real scalars. -/
private lemma inner_toLp_prod (p : ℝ × ℝ) (v : WithLp 2 (ℝ × ℝ)) :
    (⟪(WithLp.toLp 2 p : WithLp 2 (ℝ × ℝ)), v⟫_ℝ : ℝ)
      = (WithLp.ofLp v).1 * p.1 + (WithLp.ofLp v).2 * p.2 := by
  rw [WithLp.prod_inner_apply]
  -- After unfolding, we have `⟪p.1, (ofLp v).1⟫_ℝ + ⟪p.2, (ofLp v).2⟫_ℝ`
  -- on real scalars, both equal to `(ofLp v).i * p.i` by RCLike's
  -- defeq to `b * a`.
  have h1 : (⟪((WithLp.ofLp (WithLp.toLp 2 p : WithLp 2 (ℝ × ℝ))).1 : ℝ),
                  (WithLp.ofLp v).1⟫_ℝ : ℝ)
      = (WithLp.ofLp v).1 * p.1 := by
    change inner ℝ p.1 (WithLp.ofLp v).1 = (WithLp.ofLp v).1 * p.1
    simp [inner, RCLike.re, mul_comm]
  have h2 : (⟪((WithLp.ofLp (WithLp.toLp 2 p : WithLp 2 (ℝ × ℝ))).2 : ℝ),
                  (WithLp.ofLp v).2⟫_ℝ : ℝ)
      = (WithLp.ofLp v).2 * p.2 := by
    change inner ℝ p.2 (WithLp.ofLp v).2 = (WithLp.ofLp v).2 * p.2
    simp [inner, RCLike.re, mul_comm]
  rw [h1, h2]

/-- *Bivariate MGF uniqueness* on `ℝ × ℝ`.

If two probability measures `μ ν : Measure (ℝ × ℝ)` have the same Gaussian
snd-marginal `gaussianReal 0 σ²` and agree on the bivariate generating
identity for all real `(u, s)`, then `μ = ν`.

The Gaussian-tail snd-marginal is what allows the parametric integral
`s ↦ ∫ exp(I·u·t + s·z) dμ` to be entire on ℂ. The identity theorem then
extends the real-axis equality to all complex `s`, and evaluating at
`s = -I·v` yields the bivariate characteristic function identity, which
`Measure.ext_of_charFun` (on `WithLp 2 (ℝ × ℝ)`) converts back to measure
equality. -/
theorem bivariate_mgf_uniqueness
    {μ ν : Measure (ℝ × ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (σ_sq : ℝ≥0)
    (h_snd_μ : μ.map Prod.snd = ProbabilityTheory.gaussianReal 0 σ_sq)
    (h_snd_ν : ν.map Prod.snd = ProbabilityTheory.gaussianReal 0 σ_sq)
    (h_int :
      ∀ (u s : ℝ),
        (∫ p : ℝ × ℝ,
            Complex.exp (Complex.I * (u : ℂ) * (p.1 : ℂ) +
                         (s : ℂ) * (p.2 : ℂ)) ∂μ)
          = ∫ p : ℝ × ℝ,
              Complex.exp (Complex.I * (u : ℂ) * (p.1 : ℂ) +
                           (s : ℂ) * (p.2 : ℂ)) ∂ν) :
    μ = ν := by
  -- Step 1: lift μ, ν via `WithLp.toLp 2`.
  set μ_L : Measure (WithLp 2 (ℝ × ℝ)) :=
    μ.map (WithLp.toLp 2 (V := ℝ × ℝ)) with hμL_def
  set ν_L : Measure (WithLp 2 (ℝ × ℝ)) :=
    ν.map (WithLp.toLp 2 (V := ℝ × ℝ)) with hνL_def
  have h_meas_toLp : Measurable (WithLp.toLp 2 (V := ℝ × ℝ)) :=
    WithLp.measurable_toLp _ _
  haveI : IsProbabilityMeasure μ_L :=
    Measure.isProbabilityMeasure_map h_meas_toLp.aemeasurable
  haveI : IsProbabilityMeasure ν_L :=
    Measure.isProbabilityMeasure_map h_meas_toLp.aemeasurable
  -- Step 2: extend the real-axis identity to all complex `s` per fixed real `u`.
  have h_F_eq_C : ∀ (u : ℝ) (s : ℂ),
      (∫ p : ℝ × ℝ,
          Complex.exp (Complex.I * (u : ℂ) * (p.1 : ℂ) + s * (p.2 : ℂ)) ∂μ)
        = ∫ p : ℝ × ℝ,
            Complex.exp (Complex.I * (u : ℂ) * (p.1 : ℂ) + s * (p.2 : ℂ)) ∂ν := by
    intro u s
    refine eq_of_real_eq_of_analytic
      (F_u_analytic σ_sq h_snd_μ u) (F_u_analytic σ_sq h_snd_ν u) ?_ s
    intro s'
    exact h_int u s'
  -- Step 3: evaluate at s = I · v for arbitrary real v.
  have h_im_eq : ∀ (u v : ℝ),
      (∫ p : ℝ × ℝ,
          Complex.exp (Complex.I * (u : ℂ) * (p.1 : ℂ) +
                       (Complex.I * (v : ℂ)) * (p.2 : ℂ)) ∂μ)
        = ∫ p : ℝ × ℝ,
            Complex.exp (Complex.I * (u : ℂ) * (p.1 : ℂ) +
                         (Complex.I * (v : ℂ)) * (p.2 : ℂ)) ∂ν := by
    intro u v
    exact h_F_eq_C u (Complex.I * (v : ℂ))
  -- Step 4: rewrite the imaginary-evaluated integrand into the
  -- canonical char-fn shape `exp((u·p.1 + v·p.2) · I)`.
  have h_charFn_eq_raw : ∀ (u v : ℝ),
      (∫ p : ℝ × ℝ,
          Complex.exp (((u : ℂ) * (p.1 : ℂ) + (v : ℂ) * (p.2 : ℂ)) *
                        Complex.I) ∂μ)
        = ∫ p : ℝ × ℝ,
            Complex.exp (((u : ℂ) * (p.1 : ℂ) + (v : ℂ) * (p.2 : ℂ)) *
                          Complex.I) ∂ν := by
    intro u v
    have h_pointwise : ∀ p : ℝ × ℝ,
        Complex.exp (Complex.I * (u : ℂ) * (p.1 : ℂ) +
                     (Complex.I * (v : ℂ)) * (p.2 : ℂ))
          = Complex.exp (((u : ℂ) * (p.1 : ℂ) + (v : ℂ) * (p.2 : ℂ)) *
                          Complex.I) := by
      intro p
      congr 1
      ring
    have h_lhs_rewrite :
        (∫ p : ℝ × ℝ,
            Complex.exp (Complex.I * (u : ℂ) * (p.1 : ℂ) +
                         (Complex.I * (v : ℂ)) * (p.2 : ℂ)) ∂μ)
          = ∫ p : ℝ × ℝ,
              Complex.exp (((u : ℂ) * (p.1 : ℂ) + (v : ℂ) * (p.2 : ℂ)) *
                            Complex.I) ∂μ := by
      refine integral_congr_ae (.of_forall fun p => ?_)
      exact h_pointwise p
    have h_rhs_rewrite :
        (∫ p : ℝ × ℝ,
            Complex.exp (Complex.I * (u : ℂ) * (p.1 : ℂ) +
                         (Complex.I * (v : ℂ)) * (p.2 : ℂ)) ∂ν)
          = ∫ p : ℝ × ℝ,
              Complex.exp (((u : ℂ) * (p.1 : ℂ) + (v : ℂ) * (p.2 : ℂ)) *
                            Complex.I) ∂ν := by
      refine integral_congr_ae (.of_forall fun p => ?_)
      exact h_pointwise p
    have h_im_uv := h_im_eq u v
    rw [h_lhs_rewrite, h_rhs_rewrite] at h_im_uv
    exact h_im_uv
  -- Step 5: bridge to charFun on `WithLp 2 (ℝ × ℝ)`.
  have h_charFn_μL_eq_νL : ∀ (t : WithLp 2 (ℝ × ℝ)),
      MeasureTheory.charFun μ_L t = MeasureTheory.charFun ν_L t := by
    intro t
    set u : ℝ := (WithLp.ofLp t).1 with hu_def
    set v : ℝ := (WithLp.ofLp t).2 with hv_def
    -- Push the integral to μ via `integral_map`.
    have h_integrand_meas_μL : AEStronglyMeasurable
        (fun x : WithLp 2 (ℝ × ℝ) => Complex.exp (⟪x, t⟫_ℝ * Complex.I)) μ_L := by
      refine Continuous.aestronglyMeasurable ?_
      fun_prop
    have h_integrand_meas_νL : AEStronglyMeasurable
        (fun x : WithLp 2 (ℝ × ℝ) => Complex.exp (⟪x, t⟫_ℝ * Complex.I)) ν_L := by
      refine Continuous.aestronglyMeasurable ?_
      fun_prop
    -- charFun μ_L t.
    rw [MeasureTheory.charFun_apply, MeasureTheory.charFun_apply, hμL_def, hνL_def,
        integral_map h_meas_toLp.aemeasurable h_integrand_meas_μL,
        integral_map h_meas_toLp.aemeasurable h_integrand_meas_νL]
    -- Replace each pushed integrand with the canonical form.
    have h_inner_pointwise : ∀ p : ℝ × ℝ,
        Complex.exp ((⟪(WithLp.toLp 2 p : WithLp 2 (ℝ × ℝ)), t⟫_ℝ : ℝ) *
                      Complex.I)
          = Complex.exp (((u : ℂ) * (p.1 : ℂ) + (v : ℂ) * (p.2 : ℂ)) *
                          Complex.I) := by
      intro p
      have h_inner := inner_toLp_prod p t
      -- h_inner : ⟪toLp p, t⟫_ℝ = (ofLp t).1 * p.1 + (ofLp t).2 * p.2
      -- The integrand becomes exp((u * p.1 + v * p.2) * I).
      congr 1
      rw [show (⟪(WithLp.toLp 2 p : WithLp 2 (ℝ × ℝ)), t⟫_ℝ : ℂ)
            = ((WithLp.ofLp t).1 * p.1 + (WithLp.ofLp t).2 * p.2 : ℝ) from by
          exact_mod_cast h_inner]
      push_cast
      ring
    have h_lhs_rewrite :
        (∫ p : ℝ × ℝ,
            Complex.exp ((⟪(WithLp.toLp 2 p : WithLp 2 (ℝ × ℝ)), t⟫_ℝ : ℝ) *
                          Complex.I) ∂μ)
          = ∫ p : ℝ × ℝ,
              Complex.exp (((u : ℂ) * (p.1 : ℂ) + (v : ℂ) * (p.2 : ℂ)) *
                            Complex.I) ∂μ := by
      refine integral_congr_ae (.of_forall fun p => ?_)
      exact h_inner_pointwise p
    have h_rhs_rewrite :
        (∫ p : ℝ × ℝ,
            Complex.exp ((⟪(WithLp.toLp 2 p : WithLp 2 (ℝ × ℝ)), t⟫_ℝ : ℝ) *
                          Complex.I) ∂ν)
          = ∫ p : ℝ × ℝ,
              Complex.exp (((u : ℂ) * (p.1 : ℂ) + (v : ℂ) * (p.2 : ℂ)) *
                            Complex.I) ∂ν := by
      refine integral_congr_ae (.of_forall fun p => ?_)
      exact h_inner_pointwise p
    rw [h_lhs_rewrite, h_rhs_rewrite]
    exact h_charFn_eq_raw u v
  -- Step 6: apply ext_of_charFun on WithLp 2 (ℝ × ℝ).
  have h_μL_eq_νL : μ_L = ν_L :=
    Measure.ext_of_charFun (funext h_charFn_μL_eq_νL)
  -- Step 7: pull back via `MeasurableEquiv.toLp 2`.
  have h_pull : ∀ ρ : Measure (ℝ × ℝ),
      ρ = (ρ.map (WithLp.toLp 2 (V := ℝ × ℝ))).map (WithLp.ofLp) := by
    intro ρ
    rw [Measure.map_map (WithLp.measurable_ofLp _ _) h_meas_toLp]
    have h_id : (fun x : ℝ × ℝ => WithLp.ofLp (WithLp.toLp 2 x)) = id := by
      funext x; rfl
    rw [Function.comp_def, h_id, Measure.map_id]
  rw [h_pull μ, h_pull ν]
  congr 1

end AsymptoticStatistics.ForMathlib.BivariateMGFUniqueness
