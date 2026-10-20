module
public import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity
public import StatLean.AsymptoticStatistics.ForMathlib.RnDerivSqrt
public import StatLean.AsymptoticStatistics.ForMathlib.L2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# Product-Hellinger inequality for iid products

For two probability measures dominated by a common σ-finite measure with densities
`p, q : Ω → ℝ≥0∞` (typed via `ENNReal` to match `Measure.rnDeriv`), the squared
Hellinger residual

```
‖√p.toReal - √q.toReal‖²_{L²(μ)}
```

and its `n`-fold-product counterpart

```
‖√(∏ⱼ pⱼ).toReal - √(∏ⱼ qⱼ).toReal‖²_{L²(μ^n)}
```

are related by

```
‖√∏p.toReal - √∏q.toReal‖²_{L²(μ^n)} ≤ n · ‖√p.toReal - √q.toReal‖²_{L²(μ)}
```

This is the central tensorisation step for the LAN-locality argument of same-score
`QMDPath`s (see `LowerBounds/RegularEstimatorNarrow.lean`,
`hellinger_locality_for_qmdpath_same_score`).

## Mathematical content

Define the *Hellinger affinity* `A := ∫ √(p · q).toReal dμ`. Then for probability
densities `p, q`:

1. `‖√p.toReal - √q.toReal‖²_{L²(μ)} = ∫ p.toReal + ∫ q.toReal - 2A = 2 - 2A`.
2. The affinity multiplies under iid products:
   `A(μ^n, ν^n, μ_dom^n) = A(μ, ν, μ_dom)^n` (via `lintegral_fintype_prod_eq_prod`
   applied to `∏ⱼ √(pⱼ qⱼ)`).
3. Bernoulli inequality `1 - A^n ≤ n · (1 - A)` for `0 ≤ A ≤ 1` (Cauchy-Schwarz).
4. Combining gives the squared `L²`-form, and `√n` after square-rooting.

The analytic core is product-affinity multiplicativity, expressed below in
`lintegral` and Bochner-integral forms. Together with the one-sample Hellinger
identity and Bernoulli's inequality, it yields the squared residual bound and
the headline square-root estimate
`hellinger_product_eLpNorm_le_sqrt_n_per_sample`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AsymptoticStatistics.ForMathlib.HellingerProduct

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Pointwise / numerical lemma: Bernoulli `1 - x^n ≤ n(1-x)` for `x ∈ [0,1]`. -/

/-- Bernoulli-style inequality: `1 - x^n ≤ n(1-x)` for `x ∈ [0,1]`.

Proof: induction on `n`. The step uses
`1 - x^{n+1} = (1 - x^n) + x^n · (1 - x) ≤ n(1-x) + 1·(1-x) = (n+1)(1-x)`. -/
lemma one_sub_pow_le_nsmul_one_sub
    {x : ℝ} (hx_nn : 0 ≤ x) (hx_le : x ≤ 1) (n : ℕ) :
    1 - x ^ n ≤ n * (1 - x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hx_n_nn : 0 ≤ x ^ n := pow_nonneg hx_nn n
      have hx_n_le : x ^ n ≤ 1 := pow_le_one₀ hx_nn hx_le
      have h_id : 1 - x ^ (n + 1) = (1 - x ^ n) + x ^ n * (1 - x) := by ring
      have h_term2 : x ^ n * (1 - x) ≤ 1 * (1 - x) :=
        mul_le_mul_of_nonneg_right hx_n_le (by linarith)
      have h_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [h_id, h_cast]
      have h_rhs : ((n : ℝ) + 1) * (1 - x) = (n : ℝ) * (1 - x) + 1 * (1 - x) := by
        ring
      rw [h_rhs]
      linarith

/-! ## Product affinity multiplicativity (toReal form).

For iid product measures with densities `p, q : Ω → ℝ≥0∞`, the Hellinger affinity
factors as a power:

```
∫ Real.sqrt ((∏ⱼ p(X j)).toReal * (∏ⱼ q(X j)).toReal) d(μ^n)
  = (∫ Real.sqrt (p ω . toReal * q ω . toReal) dμ) ^ n
```

(when both `p, q` are finite-valued so `.toReal` commutes with products).

The cleanest framing uses `ℝ≥0∞`-valued integrals of `√(p · q)` via
`ENNReal.toReal` and a finiteness side-condition. We state the unwrapped form
on the `lintegral` side (with the ENNReal product) and a `.toReal` wrapper. -/

omit [MeasurableSpace Ω] in
/-- Product affinity factorisation: `∏ⱼ (p(X j) * q(X j)) = (∏ⱼ p(X j)) * (∏ⱼ q(X j))`
pointwise. This is `Finset.prod_mul_distrib` packaged for the affinity. -/
lemma prod_mul_prod_eq
    {n : ℕ} (p q : Ω → ℝ≥0∞) (X : Fin n → Ω) :
    (∏ j, p (X j)) * (∏ j, q (X j)) = ∏ j, p (X j) * q (X j) := by
  rw [← Finset.prod_mul_distrib]

/-- For iid product measures, the lintegral of `∏ⱼ f(X j)` factors as `(∫ f dμ)^n`,
when `f` is the same function at each coordinate.

This is `lintegral_fin_nat_prod_eq_prod` specialised to the iid case. -/
lemma lintegral_prod_iid_eq_pow
    {n : ℕ} (μ : Measure Ω) [SigmaFinite μ]
    (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ X : Fin n → Ω, ∏ _j : Fin n, f (X _j)
        ∂Measure.pi (fun _ : Fin n => μ)
      = (∫⁻ ω, f ω ∂μ) ^ n := by
  have h_fact := MeasureTheory.lintegral_fin_nat_prod_eq_prod
    (μ := fun _ : Fin n => μ)
    (f := fun _ : Fin n => f) (fun _ => hf)
  rw [h_fact, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## Affinity-route bricks for the iid product Hellinger inequality

We establish the tensorisation inequality
`(eLpNorm (√(∏p) − √(∏q)) 2 (ξ^n)).toReal ≤ √n · (eLpNorm (√p − √q) 2 ξ).toReal`
via the **Hellinger affinity** `A := ∫ √p · √q dξ ∈ [0, 1]`, with the canonical
chain
  per-sample residual sq = `2 − 2A`,
  product residual sq    = `2 − 2 Aⁿ`,
  Bernoulli `1 − Aⁿ ≤ n(1 − A)`,
take sqrt.
All bricks live as named lemmas; final assembly = the headline theorem at the end.
-/

open AsymptoticStatistics.ForMathlib.RnDerivSqrt

omit [MeasurableSpace Ω] in
/-- Pointwise rewrite `(∏ⱼ √pⱼ.toReal) = √((∏ⱼ pⱼ).toReal)`. -/
lemma prod_sqrt_eq_sqrt_prod_toReal {n : ℕ} (p : Ω → ℝ≥0∞) (X : Fin n → Ω) :
    ∏ j, Real.sqrt ((p (X j)).toReal)
      = Real.sqrt ((∏ j, p (X j)).toReal) := by
  rw [ENNReal.toReal_prod]
  exact (Real.sqrt_prod _ (fun _ _ => ENNReal.toReal_nonneg)).symm

/-- `A := ∫ √p · √q dξ ≥ 0`. -/
lemma integral_sqrt_mul_sqrt_nonneg (μ ν ξ : Measure Ω) :
    0 ≤ ∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal
          * Real.sqrt (ν.rnDeriv ξ ω).toReal ∂ξ :=
  integral_nonneg (fun _ =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- `A ≤ 1`. By Cauchy-Schwarz `|∫ √p · √q|² ≤ (∫ p)(∫ q) = 1`. -/
lemma integral_sqrt_mul_sqrt_le_one
    {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    ∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal
          * Real.sqrt (ν.rnDeriv ξ ω).toReal ∂ξ ≤ 1 := by
  have hf_mem : MemLp (fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal) 2 ξ :=
    memLp_sqrt_rnDeriv hμ
  have hg_mem : MemLp (fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal) 2 ξ :=
    memLp_sqrt_rnDeriv hν
  have hf_sq_int :
      ∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal ^ 2 ∂ξ = 1 := by
    have := integral_sqrt_rnDeriv_sq (ν := μ) (μ := ξ) hμ
    simpa using this
  have hg_sq_int :
      ∫ ω, Real.sqrt (ν.rnDeriv ξ ω).toReal ^ 2 ∂ξ = 1 := by
    have := integral_sqrt_rnDeriv_sq (ν := ν) (μ := ξ) hν
    simpa using this
  have h_cs : |∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal
                    * Real.sqrt (ν.rnDeriv ξ ω).toReal ∂ξ|
              ≤ Real.sqrt (∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal ^ 2 ∂ξ)
                  * Real.sqrt (∫ ω, Real.sqrt (ν.rnDeriv ξ ω).toReal ^ 2 ∂ξ) :=
    AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq ξ hf_mem hg_mem
  rw [hf_sq_int, hg_sq_int] at h_cs
  simp only [Real.sqrt_one, mul_one] at h_cs
  exact le_of_abs_le h_cs

/-- `∫ (∏ⱼ pⱼ(Xⱼ)).toReal d(ξ^n) = 1` for prob μ ≪ ξ. -/
lemma integral_prod_rnDeriv_toReal_eq_one
    {n : ℕ} {μ ξ : Measure Ω} [SigmaFinite ξ] [IsProbabilityMeasure μ]
    (hμ : μ ≪ ξ) :
    ∫ X : Fin n → Ω, (∏ j, (μ.rnDeriv ξ (X j)).toReal)
        ∂(Measure.pi (fun _ : Fin n => ξ)) = 1 := by
  have h_prod_nn : ∀ X : Fin n → Ω, 0 ≤ ∏ j, (μ.rnDeriv ξ (X j)).toReal :=
    fun X => Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have h_meas_p : Measurable (fun ω => (μ.rnDeriv ξ ω).toReal) :=
    (Measure.measurable_rnDeriv μ ξ).ennreal_toReal
  have h_prod_meas : Measurable
      (fun X : Fin n → Ω => ∏ j, (μ.rnDeriv ξ (X j)).toReal) :=
    Finset.measurable_prod _ (fun j _ => h_meas_p.comp (measurable_pi_apply j))
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall h_prod_nn) h_prod_meas.aestronglyMeasurable]
  have h_ofReal_prod : ∀ X : Fin n → Ω,
      ENNReal.ofReal (∏ j, (μ.rnDeriv ξ (X j)).toReal)
        = ∏ j, ENNReal.ofReal ((μ.rnDeriv ξ (X j)).toReal) :=
    fun _ => ENNReal.ofReal_prod_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  rw [show (fun X : Fin n → Ω => ENNReal.ofReal (∏ j, (μ.rnDeriv ξ (X j)).toReal))
        = (fun X : Fin n → Ω => ∏ j, ENNReal.ofReal ((μ.rnDeriv ξ (X j)).toReal))
        from funext h_ofReal_prod]
  rw [lintegral_prod_iid_eq_pow (μ := ξ) (n := n)
      (f := fun ω => ENNReal.ofReal ((μ.rnDeriv ξ ω).toReal))
      (ENNReal.measurable_ofReal.comp h_meas_p)]
  have h_ae_finite : ∀ᵐ ω ∂ξ, μ.rnDeriv ξ ω ≠ ⊤ :=
    (Measure.rnDeriv_lt_top μ ξ).mono (fun _ => ne_of_lt)
  have h_ofReal_toReal : ∀ᵐ ω ∂ξ,
      ENNReal.ofReal ((μ.rnDeriv ξ ω).toReal) = μ.rnDeriv ξ ω :=
    h_ae_finite.mono (fun _ h => ENNReal.ofReal_toReal h)
  rw [lintegral_congr_ae h_ofReal_toReal]
  rw [MeasureTheory.Measure.lintegral_rnDeriv hμ]
  simp [measure_univ]

/-- Integrability of `(∏ⱼ pⱼ(Xⱼ)).toReal` under `ξ^n`. -/
lemma integrable_prod_rnDeriv_toReal
    {n : ℕ} {μ ξ : Measure Ω} [SigmaFinite ξ] [IsProbabilityMeasure μ]
    (hμ : μ ≪ ξ) :
    Integrable (fun X : Fin n → Ω => ∏ j, (μ.rnDeriv ξ (X j)).toReal)
      (Measure.pi (fun _ : Fin n => ξ)) := by
  have h_prod_nn : ∀ X : Fin n → Ω, 0 ≤ ∏ j, (μ.rnDeriv ξ (X j)).toReal :=
    fun _ => Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
  have h_meas_p : Measurable (fun ω => (μ.rnDeriv ξ ω).toReal) :=
    (Measure.measurable_rnDeriv μ ξ).ennreal_toReal
  have h_prod_meas : Measurable
      (fun X : Fin n → Ω => ∏ j, (μ.rnDeriv ξ (X j)).toReal) :=
    Finset.measurable_prod _ (fun j _ => h_meas_p.comp (measurable_pi_apply j))
  refine ⟨h_prod_meas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp_rw [Real.norm_of_nonneg (h_prod_nn _)]
  have h_eq : ∫⁻ X : Fin n → Ω,
      ENNReal.ofReal (∏ j, (μ.rnDeriv ξ (X j)).toReal)
        ∂(Measure.pi (fun _ : Fin n => ξ)) = 1 := by
    have h_ofReal_prod : ∀ X : Fin n → Ω,
        ENNReal.ofReal (∏ j, (μ.rnDeriv ξ (X j)).toReal)
          = ∏ j, ENNReal.ofReal ((μ.rnDeriv ξ (X j)).toReal) :=
      fun _ => ENNReal.ofReal_prod_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)
    rw [show (fun X : Fin n → Ω => ENNReal.ofReal (∏ j, (μ.rnDeriv ξ (X j)).toReal))
          = (fun X : Fin n → Ω => ∏ j, ENNReal.ofReal ((μ.rnDeriv ξ (X j)).toReal))
          from funext h_ofReal_prod]
    rw [lintegral_prod_iid_eq_pow (μ := ξ) (n := n)
        (f := fun ω => ENNReal.ofReal ((μ.rnDeriv ξ ω).toReal))
        (ENNReal.measurable_ofReal.comp h_meas_p)]
    have h_ae_finite : ∀ᵐ ω ∂ξ, μ.rnDeriv ξ ω ≠ ⊤ :=
      (Measure.rnDeriv_lt_top μ ξ).mono (fun _ => ne_of_lt)
    have h_ofReal_toReal : ∀ᵐ ω ∂ξ,
        ENNReal.ofReal ((μ.rnDeriv ξ ω).toReal) = μ.rnDeriv ξ ω :=
      h_ae_finite.mono (fun _ h => ENNReal.ofReal_toReal h)
    rw [lintegral_congr_ae h_ofReal_toReal]
    rw [MeasureTheory.Measure.lintegral_rnDeriv hμ]
    simp [measure_univ]
  rw [h_eq]; exact ENNReal.one_lt_top

/-- *Product affinity multiplicativity (Bochner form)*:
  `∫ (∏ⱼ √p(Xⱼ)) · (∏ⱼ √q(Xⱼ)) d(ξ^n) = (∫ √p · √q dξ)^n`. -/
lemma integral_prod_sqrt_mul_prod_sqrt_eq_pow
    {n : ℕ} {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∫ X : Fin n → Ω,
        (∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
          * (∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal)
        ∂(Measure.pi (fun _ : Fin n => ξ))
      = (∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal
              * Real.sqrt (ν.rnDeriv ξ ω).toReal ∂ξ) ^ n := by
  set h : Ω → ℝ := fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
                          * Real.sqrt (ν.rnDeriv ξ ω).toReal with hdef
  have hh_nn : ∀ ω, 0 ≤ h ω := fun _ =>
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_meas : Measurable h :=
    (((Measure.measurable_rnDeriv μ ξ).ennreal_toReal).sqrt).mul
      (((Measure.measurable_rnDeriv ν ξ).ennreal_toReal).sqrt)
  have h_distr : ∀ X : Fin n → Ω,
      (∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
        * (∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal)
      = ∏ j, h (X j) := by
    intro X; rw [← Finset.prod_mul_distrib]
  rw [integral_congr_ae (Filter.Eventually.of_forall h_distr)]
  have h_prod_nn : ∀ X : Fin n → Ω, 0 ≤ ∏ j, h (X j) :=
    fun _ => Finset.prod_nonneg (fun _ _ => hh_nn _)
  have h_prod_meas : Measurable (fun X : Fin n → Ω => ∏ j, h (X j)) :=
    Finset.measurable_prod _ (fun j _ => h_meas.comp (measurable_pi_apply j))
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall h_prod_nn) h_prod_meas.aestronglyMeasurable]
  have h_ofReal_prod : ∀ X : Fin n → Ω,
      ENNReal.ofReal (∏ j, h (X j)) = ∏ j, ENNReal.ofReal (h (X j)) :=
    fun _ => ENNReal.ofReal_prod_of_nonneg (fun _ _ => hh_nn _)
  rw [show (fun X : Fin n → Ω => ENNReal.ofReal (∏ j, h (X j)))
        = (fun X : Fin n → Ω => ∏ j, ENNReal.ofReal (h (X j))) from
        funext h_ofReal_prod]
  rw [lintegral_prod_iid_eq_pow (μ := ξ) (n := n)
      (f := fun ω => ENNReal.ofReal (h ω))
      (ENNReal.measurable_ofReal.comp h_meas)]
  rw [ENNReal.toReal_pow]
  congr 1
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall hh_nn) h_meas.aestronglyMeasurable]

/-- *Per-sample residual square identity (Bochner)*:
  `∫ (√p − √q)² dξ = 2 − 2A`. -/
lemma integral_per_sample_residual_sq_eq
    {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    ∫ ω, (Real.sqrt (μ.rnDeriv ξ ω).toReal
            - Real.sqrt (ν.rnDeriv ξ ω).toReal) ^ 2 ∂ξ
      = 2 - 2 * ∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal
                      * Real.sqrt (ν.rnDeriv ξ ω).toReal ∂ξ := by
  have hf_mem : MemLp (fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal) 2 ξ :=
    memLp_sqrt_rnDeriv hμ
  have hg_mem : MemLp (fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal) 2 ξ :=
    memLp_sqrt_rnDeriv hν
  have hf_sq : Integrable
      (fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal ^ 2) ξ :=
    hf_mem.integrable_sq
  have hg_sq : Integrable
      (fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal ^ 2) ξ :=
    hg_mem.integrable_sq
  have h_fg : Integrable
      (fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
                * Real.sqrt (ν.rnDeriv ξ ω).toReal) ξ :=
    hf_mem.integrable_mul hg_mem
  have h_a := integral_sqrt_rnDeriv_sq (ν := μ) (μ := ξ) hμ
  have h_b := integral_sqrt_rnDeriv_sq (ν := ν) (μ := ξ) hν
  simp only [measure_univ, ENNReal.toReal_one] at h_a h_b
  -- Use `set` aliases to keep integrand parses clean.
  set fF : Ω → ℝ := fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal ^ 2 with hfF_def
  set gG : Ω → ℝ := fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal ^ 2 with hgG_def
  set H : Ω → ℝ := fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
                            * Real.sqrt (ν.rnDeriv ξ ω).toReal with hH_def
  have hF_int : Integrable fF ξ := hf_sq
  have hG_int : Integrable gG ξ := hg_sq
  have hH_int : Integrable H ξ := h_fg
  have hF_val : ∫ ω, fF ω ∂ξ = 1 := h_a
  have hG_val : ∫ ω, gG ω ∂ξ = 1 := h_b
  have h_pt : ∀ ω, (Real.sqrt (μ.rnDeriv ξ ω).toReal
                      - Real.sqrt (ν.rnDeriv ξ ω).toReal) ^ 2
                = fF ω + gG ω - 2 * H ω := by
    intro ω; simp only [hfF_def, hgG_def, hH_def]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h_pt)]
  rw [integral_sub (hF_int.fun_add hG_int) (hH_int.const_mul 2)]
  rw [integral_add hF_int hG_int, integral_const_mul, hF_val, hG_val]
  ring

/-- *Product residual square identity*:
  `∫ (F − G)² d(ξ^n) = 2 − 2 Aⁿ`. -/
lemma integral_product_residual_sq_eq
    {n : ℕ} {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    ∫ X : Fin n → Ω,
        ((∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
          - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal) ^ 2
        ∂(Measure.pi (fun _ : Fin n => ξ))
      = 2 - 2 * (∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal
                      * Real.sqrt (ν.rnDeriv ξ ω).toReal ∂ξ) ^ n := by
  set f : Ω → ℝ := fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
  set g : Ω → ℝ := fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal
  have hf_meas : Measurable f :=
    ((Measure.measurable_rnDeriv μ ξ).ennreal_toReal).sqrt
  have hg_meas : Measurable g :=
    ((Measure.measurable_rnDeriv ν ξ).ennreal_toReal).sqrt
  have hf_nn : ∀ ω, 0 ≤ f ω := fun _ => Real.sqrt_nonneg _
  have hg_nn : ∀ ω, 0 ≤ g ω := fun _ => Real.sqrt_nonneg _
  -- F² = ∏ p.toReal, G² = ∏ q.toReal pointwise.
  have hF_sq_pt : ∀ X : Fin n → Ω,
      (∏ j, f (X j)) ^ 2 = ∏ j, (μ.rnDeriv ξ (X j)).toReal := by
    intro X
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun _ _ => ?_)
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hG_sq_pt : ∀ X : Fin n → Ω,
      (∏ j, g (X j)) ^ 2 = ∏ j, (ν.rnDeriv ξ (X j)).toReal := by
    intro X
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun _ _ => ?_)
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hF_sq_int : Integrable (fun X : Fin n → Ω => (∏ j, f (X j)) ^ 2)
      (Measure.pi (fun _ : Fin n => ξ)) :=
    (integrable_prod_rnDeriv_toReal hμ).congr
      (Filter.Eventually.of_forall (fun X => (hF_sq_pt X).symm))
  have hG_sq_int : Integrable (fun X : Fin n → Ω => (∏ j, g (X j)) ^ 2)
      (Measure.pi (fun _ : Fin n => ξ)) :=
    (integrable_prod_rnDeriv_toReal hν).congr
      (Filter.Eventually.of_forall (fun X => (hG_sq_pt X).symm))
  have hF_sq_val : ∫ X, (∏ j, f (X j)) ^ 2
      ∂(Measure.pi (fun _ : Fin n => ξ)) = 1 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hF_sq_pt)]
    exact integral_prod_rnDeriv_toReal_eq_one (μ := μ) (ξ := ξ) (n := n) hμ
  have hG_sq_val : ∫ X, (∏ j, g (X j)) ^ 2
      ∂(Measure.pi (fun _ : Fin n => ξ)) = 1 := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hG_sq_pt)]
    exact integral_prod_rnDeriv_toReal_eq_one (μ := ν) (ξ := ξ) (n := n) hν
  -- FG integrability via |FG| ≤ (F² + G²)/2.
  have hF_meas : Measurable (fun X : Fin n → Ω => ∏ j, f (X j)) :=
    Finset.measurable_prod _ (fun j _ => hf_meas.comp (measurable_pi_apply j))
  have hG_meas : Measurable (fun X : Fin n → Ω => ∏ j, g (X j)) :=
    Finset.measurable_prod _ (fun j _ => hg_meas.comp (measurable_pi_apply j))
  have hFG_int : Integrable (fun X : Fin n → Ω => (∏ j, f (X j)) * ∏ j, g (X j))
      (Measure.pi (fun _ : Fin n => ξ)) := by
    refine Integrable.mono ((hF_sq_int.add hG_sq_int).div_const 2)
      (hF_meas.mul hG_meas).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun X => ?_))
    have h1 : 0 ≤ ∏ j, f (X j) := Finset.prod_nonneg (fun _ _ => hf_nn _)
    have h2 : 0 ≤ ∏ j, g (X j) := Finset.prod_nonneg (fun _ _ => hg_nn _)
    have hbd : (∏ j, f (X j)) * ∏ j, g (X j)
              ≤ ((∏ j, f (X j)) ^ 2 + (∏ j, g (X j)) ^ 2) / 2 := by
      nlinarith [sq_nonneg ((∏ j, f (X j)) - ∏ j, g (X j))]
    have hr_nn : 0 ≤ ((∏ j, f (X j)) ^ 2 + (∏ j, g (X j)) ^ 2) / 2 := by
      have : 0 ≤ (∏ j, f (X j)) ^ 2 + (∏ j, g (X j)) ^ 2 :=
        add_nonneg (sq_nonneg _) (sq_nonneg _)
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h1 h2)]
    change (∏ j, f (X j)) * ∏ j, g (X j)
         ≤ ‖(fun X : Fin n → Ω =>
              ((∏ j, f (X j)) ^ 2 + (∏ j, g (X j)) ^ 2) / 2) X‖
    rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]
    exact hbd
  have hFG_val :
      ∫ X, (∏ j, f (X j)) * (∏ j, g (X j))
        ∂(Measure.pi (fun _ : Fin n => ξ))
      = (∫ ω, f ω * g ω ∂ξ) ^ n :=
    integral_prod_sqrt_mul_prod_sqrt_eq_pow (μ := μ) (ν := ν) (ξ := ξ)
  -- Assemble: ∫ ((F − G)²) = 2 − 2 (∫ FG)^n.
  -- Strategy: expand (F − G)² = F² + G² − 2 FG pointwise, then integrate by linearity.
  -- We use `integral_finset_sum` to handle the sum cleanly (treating it as a 3-term sum).
  set F : (Fin n → Ω) → ℝ := fun X => (∏ j, f (X j)) ^ 2 with hF_def
  set G : (Fin n → Ω) → ℝ := fun X => (∏ j, g (X j)) ^ 2 with hG_def
  set H : (Fin n → Ω) → ℝ := fun X => (∏ j, f (X j)) * ∏ j, g (X j) with hH_def
  have hF_int : Integrable F (Measure.pi (fun _ : Fin n => ξ)) := hF_sq_int
  have hG_int : Integrable G (Measure.pi (fun _ : Fin n => ξ)) := hG_sq_int
  have hH_int : Integrable H (Measure.pi (fun _ : Fin n => ξ)) := hFG_int
  have hF_val : ∫ X, F X ∂(Measure.pi (fun _ : Fin n => ξ)) = 1 := hF_sq_val
  have hG_val : ∫ X, G X ∂(Measure.pi (fun _ : Fin n => ξ)) = 1 := hG_sq_val
  have hH_val : ∫ X, H X ∂(Measure.pi (fun _ : Fin n => ξ)) = (∫ ω, f ω * g ω ∂ξ) ^ n :=
    hFG_val
  have h_pt : ∀ X : Fin n → Ω,
      ((∏ j, f (X j)) - ∏ j, g (X j)) ^ 2 = F X + G X - 2 * H X := by
    intro X; simp only [hF_def, hG_def, hH_def]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h_pt)]
  rw [integral_sub (hF_int.fun_add hG_int) (hH_int.const_mul 2)]
  rw [integral_add hF_int hG_int]
  rw [integral_const_mul]
  rw [hF_val, hG_val, hH_val]
  ring

/-- *Squared tensorisation inequality*:
  `∫ (F − G)² d(ξ^n) ≤ n · ∫ (f − g)² dξ`. -/
lemma hellinger_product_residual_sq_le_n_per_sample
    {n : ℕ} {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    ∫ X : Fin n → Ω,
        ((∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
          - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal) ^ 2
        ∂(Measure.pi (fun _ : Fin n => ξ))
      ≤ n * ∫ ω, (Real.sqrt (μ.rnDeriv ξ ω).toReal
                  - Real.sqrt (ν.rnDeriv ξ ω).toReal) ^ 2 ∂ξ := by
  set A : ℝ := ∫ ω, Real.sqrt (μ.rnDeriv ξ ω).toReal
                * Real.sqrt (ν.rnDeriv ξ ω).toReal ∂ξ
  have hA_nn : 0 ≤ A := integral_sqrt_mul_sqrt_nonneg μ ν ξ
  have hA_le_one : A ≤ 1 := integral_sqrt_mul_sqrt_le_one hμ hν
  rw [integral_product_residual_sq_eq (μ := μ) (ν := ν) (ξ := ξ) (n := n) hμ hν]
  rw [integral_per_sample_residual_sq_eq (μ := μ) (ν := ν) (ξ := ξ) hμ hν]
  have h_bern := one_sub_pow_le_nsmul_one_sub hA_nn hA_le_one n
  linarith

/-- *Tensorisation inequality (Bochner sqrt form)*:
  `√(∫ (F − G)² d(ξ^n)) ≤ √n · √(∫ (f − g)² dξ)`. -/
lemma hellinger_product_sqrt_residual_le_sqrt_n_per_sample
    {n : ℕ} {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    Real.sqrt (∫ X : Fin n → Ω,
        ((∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
          - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal) ^ 2
        ∂(Measure.pi (fun _ : Fin n => ξ)))
      ≤ Real.sqrt n * Real.sqrt (∫ ω,
            (Real.sqrt (μ.rnDeriv ξ ω).toReal
              - Real.sqrt (ν.rnDeriv ξ ω).toReal) ^ 2 ∂ξ) := by
  have h_sq := hellinger_product_residual_sq_le_n_per_sample
    (μ := μ) (ν := ν) (ξ := ξ) (n := n) hμ hν
  have h_n_nn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  calc Real.sqrt _
      ≤ Real.sqrt _ := Real.sqrt_le_sqrt h_sq
    _ = Real.sqrt n * Real.sqrt _ := Real.sqrt_mul h_n_nn _

/-- Per-sample sqrt-residual `√p − √q ∈ L²(ξ)`. -/
lemma hellinger_per_sample_residual_memLp_two
    {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    MemLp (fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
            - Real.sqrt (ν.rnDeriv ξ ω).toReal) 2 ξ :=
  (memLp_sqrt_rnDeriv hμ).sub (memLp_sqrt_rnDeriv hν)

/-- Product sqrt-residual (per-coord product form) is in `L²(ξ^n)`. -/
lemma hellinger_product_residual_memLp_two_perCoord
    {n : ℕ} {μ ν ξ : Measure Ω} [SigmaFinite ξ]
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) :
    MemLp (fun X : Fin n → Ω =>
            (∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
            - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal)
      2 (Measure.pi (fun _ : Fin n => ξ)) := by
  set f : Ω → ℝ := fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
  set g : Ω → ℝ := fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal
  have hf_meas : Measurable f :=
    ((Measure.measurable_rnDeriv μ ξ).ennreal_toReal).sqrt
  have hg_meas : Measurable g :=
    ((Measure.measurable_rnDeriv ν ξ).ennreal_toReal).sqrt
  have hF_meas : Measurable (fun X : Fin n → Ω => ∏ j, f (X j)) :=
    Finset.measurable_prod _ (fun j _ => hf_meas.comp (measurable_pi_apply j))
  have hG_meas : Measurable (fun X : Fin n → Ω => ∏ j, g (X j)) :=
    Finset.measurable_prod _ (fun j _ => hg_meas.comp (measurable_pi_apply j))
  have h_diff_meas := hF_meas.fun_sub hG_meas
  rw [memLp_two_iff_integrable_sq h_diff_meas.aestronglyMeasurable]
  -- Bound (F − G)² ≤ 2(F² + G²) pointwise; both F², G² integrable.
  have hF_sq_pt : ∀ X : Fin n → Ω,
      (∏ j, f (X j)) ^ 2 = ∏ j, (μ.rnDeriv ξ (X j)).toReal := by
    intro X
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun _ _ => ?_)
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hG_sq_pt : ∀ X : Fin n → Ω,
      (∏ j, g (X j)) ^ 2 = ∏ j, (ν.rnDeriv ξ (X j)).toReal := by
    intro X
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl (fun _ _ => ?_)
    exact Real.sq_sqrt ENNReal.toReal_nonneg
  have hF_sq_int : Integrable (fun X : Fin n → Ω => (∏ j, f (X j)) ^ 2)
      (Measure.pi (fun _ : Fin n => ξ)) :=
    (integrable_prod_rnDeriv_toReal hμ).congr
      (Filter.Eventually.of_forall (fun X => (hF_sq_pt X).symm))
  have hG_sq_int : Integrable (fun X : Fin n → Ω => (∏ j, g (X j)) ^ 2)
      (Measure.pi (fun _ : Fin n => ξ)) :=
    (integrable_prod_rnDeriv_toReal hν).congr
      (Filter.Eventually.of_forall (fun X => (hG_sq_pt X).symm))
  refine Integrable.mono ((hF_sq_int.add hG_sq_int).const_mul 2)
    (h_diff_meas.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun X => ?_))
  -- Pointwise bound (F − G)² ≤ 2 (F² + G²).
  have h_bd : ((∏ j, f (X j)) - ∏ j, g (X j)) ^ 2
              ≤ 2 * ((∏ j, f (X j)) ^ 2 + (∏ j, g (X j)) ^ 2) := by
    nlinarith [sq_nonneg ((∏ j, f (X j)) + ∏ j, g (X j)),
               sq_nonneg ((∏ j, f (X j)) - ∏ j, g (X j))]
  have hr_nn : 0 ≤ 2 * ((∏ j, f (X j)) ^ 2 + (∏ j, g (X j)) ^ 2) := by
    have : 0 ≤ (∏ j, f (X j)) ^ 2 + (∏ j, g (X j)) ^ 2 :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ((∏ j, f (X j)) - ∏ j, g (X j)) ^ 2
       ≤ ‖(2 * ((fun X : Fin n → Ω => (∏ j, f (X j)) ^ 2)
              + fun X : Fin n → Ω => (∏ j, g (X j)) ^ 2) X)‖
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]
  exact h_bd

/-- **Headline tensorisation inequality** (eLpNorm form):
`(eLpNorm (√(∏p) − √(∏q)) 2 (ξ^n)).toReal ≤ √n · (eLpNorm (√p − √q) 2 ξ).toReal`. -/
theorem hellinger_product_eLpNorm_le_sqrt_n_per_sample
    {ξ : Measure Ω} [SigmaFinite ξ]
    {μ ν : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) (n : ℕ) :
    (eLpNorm
      (fun X : Fin n → Ω =>
        Real.sqrt (∏ j, μ.rnDeriv ξ (X j)).toReal
        - Real.sqrt (∏ j, ν.rnDeriv ξ (X j)).toReal)
      2 (Measure.pi (fun _ : Fin n => ξ))).toReal
      ≤ Real.sqrt n *
          (eLpNorm
            (fun ω : Ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
              - Real.sqrt (ν.rnDeriv ξ ω).toReal)
            2 ξ).toReal := by
  -- Rewrite the headline `√(∏p) − √(∏q)` form to per-coord `(∏ √p) − (∏ √q)` form.
  have h_prod_repl : ∀ X : Fin n → Ω,
      Real.sqrt (∏ j, μ.rnDeriv ξ (X j)).toReal
          - Real.sqrt (∏ j, ν.rnDeriv ξ (X j)).toReal
        = (∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
          - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal := by
    intro X
    rw [prod_sqrt_eq_sqrt_prod_toReal, prod_sqrt_eq_sqrt_prod_toReal]
  have h_eLp_eq :
      eLpNorm (fun X : Fin n → Ω =>
        Real.sqrt (∏ j, μ.rnDeriv ξ (X j)).toReal
        - Real.sqrt (∏ j, ν.rnDeriv ξ (X j)).toReal)
        2 (Measure.pi (fun _ : Fin n => ξ))
      = eLpNorm (fun X : Fin n → Ω =>
        (∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
        - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal)
        2 (Measure.pi (fun _ : Fin n => ξ)) := by
    congr 1; funext X; exact h_prod_repl X
  rw [h_eLp_eq]
  -- Convert eLpNorm to ∫·² via MemLp.eLpNorm_eq_integral_rpow_norm.
  have hPer_mem := hellinger_per_sample_residual_memLp_two (μ := μ) (ν := ν)
    (ξ := ξ) hμ hν
  have hProd_mem := hellinger_product_residual_memLp_two_perCoord (μ := μ) (ν := ν)
    (ξ := ξ) (n := n) hμ hν
  have h_per_form := hPer_mem.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have h_prod_form := hProd_mem.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  rw [h_prod_form, h_per_form]
  have h_two : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h_two]
  -- toReal of ENNReal.ofReal of nonneg = identity.
  set Iper : ℝ := ∫ ω, ‖Real.sqrt (μ.rnDeriv ξ ω).toReal
                  - Real.sqrt (ν.rnDeriv ξ ω).toReal‖ ^ (2 : ℝ) ∂ξ with hIperDef
  set Iprod : ℝ := ∫ X : Fin n → Ω,
                ‖(∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
                  - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal‖ ^ (2 : ℝ)
                ∂(Measure.pi (fun _ : Fin n => ξ)) with hIprodDef
  have hIper_nn : 0 ≤ Iper :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hIprod_nn : 0 ≤ Iprod :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hIper_nn _),
      ENNReal.toReal_ofReal (Real.rpow_nonneg hIprod_nn _)]
  -- Rewrite ‖·‖^(2:ℝ) as (·)^(2:ℕ) using Real.rpow_natCast + Real.norm_eq_abs + sq_abs.
  have h_per_norm_eq_sq : ∀ ω,
      ‖Real.sqrt (μ.rnDeriv ξ ω).toReal - Real.sqrt (ν.rnDeriv ξ ω).toReal‖ ^ (2 : ℝ)
        = (Real.sqrt (μ.rnDeriv ξ ω).toReal - Real.sqrt (ν.rnDeriv ξ ω).toReal) ^ 2 := by
    intro ω
    rw [show ((2 : ℝ) = ((2 : ℕ) : ℝ)) from by norm_num,
        Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  have h_prod_norm_eq_sq : ∀ X : Fin n → Ω,
      ‖(∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
          - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal‖ ^ (2 : ℝ)
        = ((∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
          - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal) ^ 2 := by
    intro X
    rw [show ((2 : ℝ) = ((2 : ℕ) : ℝ)) from by norm_num,
        Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
  have h_Iper_eq :
      Iper = ∫ ω, (Real.sqrt (μ.rnDeriv ξ ω).toReal
                    - Real.sqrt (ν.rnDeriv ξ ω).toReal) ^ 2 ∂ξ := by
    simp_rw [hIperDef, h_per_norm_eq_sq]
  have h_Iprod_eq :
      Iprod = ∫ X : Fin n → Ω,
                ((∏ j, Real.sqrt (μ.rnDeriv ξ (X j)).toReal)
                  - ∏ j, Real.sqrt (ν.rnDeriv ξ (X j)).toReal) ^ 2
                ∂(Measure.pi (fun _ : Fin n => ξ)) := by
    simp_rw [hIprodDef, h_prod_norm_eq_sq]
  -- Identify rpow (2⁻¹) with Real.sqrt for nonneg.
  have h_rpow_half : ∀ x : ℝ, 0 ≤ x → x ^ (2 : ℝ)⁻¹ = Real.sqrt x := by
    intro x _
    rw [show ((2 : ℝ)⁻¹) = (1 / 2 : ℝ) from by norm_num]
    rw [← Real.sqrt_eq_rpow]
  rw [h_rpow_half _ hIper_nn, h_rpow_half _ hIprod_nn]
  rw [h_Iper_eq, h_Iprod_eq]
  exact hellinger_product_sqrt_residual_le_sqrt_n_per_sample
    (μ := μ) (ν := ν) (ξ := ξ) (n := n) hμ hν

end AsymptoticStatistics.ForMathlib.HellingerProduct
