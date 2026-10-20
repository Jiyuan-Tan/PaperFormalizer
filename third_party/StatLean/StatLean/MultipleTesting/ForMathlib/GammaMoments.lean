module
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-!
# Moment generating function, mean, variance of the Gamma distribution — ForMathlib brick

Closed forms for `Gamma(a, r)` (Mathlib's `gammaMeasure a r`: shape `a`, rate `r`, density
`r^a/Γ(a) · x^{a-1} e^{-rx}` on `x ≥ 0`), the inputs to identifying the chi-squared law
`χ²ₖ := Gamma(k/2, 1/2)`:

* `mgf_gammaMeasure` — `E[e^{tX}] = (r/(r−t))^a` for `t < r` (the brick the χ²-law identification
  uses: at rate `r = 1/2` this is `(1−2t)^{−a}`, matching the squared-Gaussian MGF);
* `integral_id_gammaMeasure` — `E[X] = a/r`;
* `variance_gammaMeasure` — `Var[X] = E[(X − a/r)²] = a/r²`.

Theorem-agnostic. Consumed by `ForMathlib/ChiSquared.lean` (the χ²ₖ definition and the
sum-of-squares law) in the chi-squared test development (Candès, Lecture 2, §2.3).

Reference: Candès, Lecture 2, §2.3, STAT 300C Notes.
-/

open MeasureTheory ProbabilityTheory Real Set

namespace StatLean.MultipleTesting

/-- The Gamma pdf as an `ℝ≥0∞`-valued function is measurable
(`gammaPDF = ofReal ∘ gammaPDFReal`). -/
private lemma measurable_gammaPDF (a r : ℝ) : Measurable (gammaPDF a r) :=
  (measurable_gammaPDFReal a r).ennreal_ofReal

/-- **Reduce a `gammaMeasure` integral to a Lebesgue integral over `Ioi 0`.** Since the density
vanishes for `x < 0`, `∫ g ∂Gamma(a,r) = ∫_{x>0} gammaPDFReal a r x · g x`. -/
private lemma integral_gammaMeasure_eq_setIntegral {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (g : ℝ → ℝ) :
    ∫ x, g x ∂(gammaMeasure a r) = ∫ x in Ioi (0 : ℝ), gammaPDFReal a r x * g x := by
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul (measurable_gammaPDF a r)
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have h1 : ∀ x : ℝ, (gammaPDF a r x).toReal • g x = gammaPDFReal a r x * g x := fun x => by
    rw [show gammaPDF a r x = ENNReal.ofReal (gammaPDFReal a r x) from rfl,
        ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x), smul_eq_mul]
  simp_rw [h1]
  refine (setIntegral_eq_integral_of_ae_compl_eq_zero ?_).symm
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (t := {(0 : ℝ)}) ?_ Real.volume_singleton
  intro x hx
  simp only [mem_setOf_eq, Classical.not_imp, mem_Ioi, not_lt] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rcases lt_or_eq_of_le hx1 with h | h
  · exact absurd (by rw [gammaPDFReal, if_neg (not_le.mpr h), zero_mul]) hx2
  · exact h

/-- **Raw moment of `Gamma(a, r)`**: `E[Xⁿ] = Γ(a+n) / (Γ(a)·rⁿ)` (`0 < a`, `0 < r`). -/
private lemma integral_pow_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    ∫ x, x ^ n ∂(gammaMeasure a r) = Real.Gamma (a + n) / (Real.Gamma a * r ^ n) := by
  have hEqOn : EqOn (fun x => gammaPDFReal a r x * x ^ n)
      (fun x => r ^ a / Real.Gamma a * (x ^ (a + (n : ℝ) - 1) * Real.exp (-(r * x))))
      (Ioi (0 : ℝ)) := by
    intro x hx
    rw [mem_Ioi] at hx
    simp only
    rw [gammaPDFReal, if_pos hx.le, ← Real.rpow_natCast x n,
        show a + (n : ℝ) - 1 = (a - 1) + (n : ℝ) by ring, Real.rpow_add hx (a - 1) (n : ℝ)]
    ring
  rw [integral_gammaMeasure_eq_setIntegral ha hr, setIntegral_congr_fun measurableSet_Ioi hEqOn,
      integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (show (0 : ℝ) < a + (n : ℝ) by positivity) hr,
      Real.rpow_add (by positivity : (0 : ℝ) < 1 / r) a (n : ℝ), Real.rpow_natCast (1 / r) n,
      div_pow, one_pow]
  rw [show r ^ a / Real.Gamma a * ((1 / r) ^ a * (1 / r ^ n) * Real.Gamma (a + (n : ℝ)))
        = (r ^ a * (1 / r) ^ a) * (Real.Gamma (a + (n : ℝ)) / (Real.Gamma a * r ^ n)) from by ring,
      show r ^ a * (1 / r) ^ a = 1 from by
        rw [← Real.mul_rpow hr.le (by positivity), mul_one_div, div_self hr.ne', Real.one_rpow],
      one_mul]

/-- Integrability of `Xⁿ` under `Gamma(a, r)` (`0 < a`, `0 < r`). -/
private lemma integrable_pow_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    Integrable (fun x => x ^ n) (gammaMeasure a r) := by
  rw [gammaMeasure, integrable_withDensity_iff (measurable_gammaPDF a r)
        (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  have hcongr : (fun x => x ^ n * (gammaPDF a r x).toReal)
      = fun x => x ^ n * gammaPDFReal a r x := by
    funext x
    rw [show gammaPDF a r x = ENNReal.ofReal (gammaPDFReal a r x) from rfl,
        ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr x)]
  rw [hcongr]
  -- integrability over `Ioi 0`, by comparison with `x^(a+n-1) e^{-rx}`
  have hmodel : IntegrableOn (fun x => x ^ (a + (n : ℝ) - 1) * Real.exp (-(r * x)))
      (Ioi (0 : ℝ)) volume := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a + (n : ℝ) - 1) (b := r)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith) one_pos hr
    refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
    rw [mem_Ioi] at hx
    beta_reduce; rw [Real.rpow_one, neg_mul]
  have hIoi : IntegrableOn (fun x => x ^ n * gammaPDFReal a r x) (Ioi (0 : ℝ)) volume := by
    refine IntegrableOn.congr_fun (hmodel.const_mul (r ^ a / Real.Gamma a))
      (fun x hx => ?_) measurableSet_Ioi
    rw [mem_Ioi] at hx
    rw [gammaPDFReal, if_pos hx.le, ← Real.rpow_natCast x n,
        show a + (n : ℝ) - 1 = (a - 1) + (n : ℝ) by ring, Real.rpow_add hx (a - 1) (n : ℝ)]
    ring
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  refine ⟨?_, hIoi⟩
  refine integrableOn_zero.congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic, MeasureTheory.ae_iff]
  refine measure_mono_null (t := {(0 : ℝ)}) ?_ Real.volume_singleton
  intro x hx
  simp only [mem_setOf_eq, Classical.not_imp, mem_Iic] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rcases lt_or_eq_of_le hx1 with h | h
  · exact absurd (show x ^ n * gammaPDFReal a r x = 0 by
      rw [gammaPDFReal, if_neg (not_le.mpr h), mul_zero]).symm hx2
  · exact h

/-- **MGF of `Gamma(a, r)`**: `E[e^{tX}] = (r/(r−t))^a` for `t < r` (`0 < a`, `0 < r`). At rate
`r = 1/2` this is `(1−2t)^{−a}`, the form the χ²-law identification matches against. -/
theorem mgf_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) {t : ℝ} (ht : t < r) :
    ∫ x, Real.exp (t * x) ∂(gammaMeasure a r) = (r / (r - t)) ^ a := by
  have hEqOn : EqOn (fun x => gammaPDFReal a r x * Real.exp (t * x))
      (fun x => r ^ a / Real.Gamma a * (x ^ (a - 1) * Real.exp (-((r - t) * x))))
      (Ioi (0 : ℝ)) := by
    intro x hx
    rw [mem_Ioi] at hx
    simp only
    rw [gammaPDFReal, if_pos hx.le, mul_assoc, ← Real.exp_add,
        show -(r * x) + t * x = -((r - t) * x) by ring]
    ring
  rw [integral_gammaMeasure_eq_setIntegral ha hr, setIntegral_congr_fun measurableSet_Ioi hEqOn,
      integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi ha (by linarith : (0 : ℝ) < r - t)]
  rw [show r ^ a / Real.Gamma a * ((1 / (r - t)) ^ a * Real.Gamma a)
        = r ^ a * (1 / (r - t)) ^ a from by
      rw [mul_comm ((1 / (r - t)) ^ a) (Real.Gamma a), ← mul_assoc,
          div_mul_cancel₀ _ (Real.Gamma_pos_of_pos ha).ne'],
    ← Real.mul_rpow hr.le (div_nonneg zero_le_one (by linarith : (0 : ℝ) ≤ r - t)), mul_one_div]

/-- **Mean of `Gamma(a, r)`**: `E[X] = a/r` (`0 < a`, `0 < r`). -/
theorem integral_id_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ x, x ∂(gammaMeasure a r) = a / r := by
  have h := integral_pow_gammaMeasure ha hr 1
  simp only [pow_one, Nat.cast_one] at h
  rw [h, Real.Gamma_add_one ha.ne']
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  field_simp

/-- **Variance of `Gamma(a, r)`**: `E[(X − a/r)²] = a/r²` (`0 < a`, `0 < r`). -/
theorem variance_gammaMeasure {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ x, (x - a / r) ^ 2 ∂(gammaMeasure a r) = a / r ^ 2 := by
  haveI := isProbabilityMeasure_gammaMeasure ha hr
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hint1 : Integrable (fun x : ℝ => x) (gammaMeasure a r) := by
    have := integrable_pow_gammaMeasure ha hr 1
    simpa only [pow_one] using this
  have hint2 : Integrable (fun x : ℝ => x ^ 2) (gammaMeasure a r) :=
    integrable_pow_gammaMeasure ha hr 2
  have hexp : ∀ x : ℝ, (x - a / r) ^ 2 = x ^ 2 - 2 * (a / r) * x + (a / r) ^ 2 :=
    fun x => by ring
  have hf : Integrable (fun x : ℝ => x ^ 2 - 2 * (a / r) * x) (gammaMeasure a r) :=
    hint2.sub (hint1.const_mul (2 * (a / r)))
  simp_rw [hexp]
  rw [integral_add hf (integrable_const _),
      integral_sub hint2 (hint1.const_mul (2 * (a / r))), integral_const_mul,
      integral_id_gammaMeasure ha hr, integral_const]
  have hX2 := integral_pow_gammaMeasure ha hr 2
  simp only [Nat.cast_ofNat] at hX2
  rw [hX2]
  have hG2 : Real.Gamma (a + 2) = (a + 1) * (a * Real.Gamma a) := by
    rw [show a + 2 = (a + 1) + 1 by ring, Real.Gamma_add_one (by positivity),
        Real.Gamma_add_one ha.ne']
  rw [hG2, probReal_univ, smul_eq_mul, one_mul]
  field_simp
  ring

end StatLean.MultipleTesting
