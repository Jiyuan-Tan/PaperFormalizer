module
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

/-!
# Esseen's smoothing inequality and the univariate Berry–Esseen theorem

Mathlib (v4.29.1) contains neither Esseen's smoothing inequality nor the Berry–Esseen
theorem. This file builds them from scratch, following Feller, *An Introduction to
Probability Theory and Its Applications*, Vol. II, 2nd ed., Wiley, 1971, §XVI.3.

## Main results

* `norm_cexp_sub_taylor_le`, `norm_cexp_sub_taylor3_le`, `norm_prod_sub_prod_le`,
  `norm_pow_sub_pow_sub_lin_le` — elementary complex-analytic estimates (the first and third
  restated here from `LindebergCLT.lean`, where they are `private`).
* `norm_charFun_sub_quadratic_le` — the characteristic function of a centered law is within
  `ρ|u|³/6` of its quadratic Taylor polynomial `1 − v u²/2`.
* `norm_charFun_sub_cubic_le` — the next order: within `(∫x⁴)|u|⁴/24` of
  `1 − v u²/2 − i m₃ u³/6`, retaining the third cumulant.
* `norm_charFun_le_exp_neg_sq` — the quadratic Gaussian majorant `‖charFun μ s‖ ≤ e^{−v s²/4}`
  on the window `v s² ≤ 2`, `ρ|s| ≤ 3v/2`.
* `norm_charFun_pow_sub_gaussian_le` — `‖(charFun μ w)ⁿ − exp(−n v w²/2)‖ ≤ n(ρ|w|³/6 +
  (v w²/2)²/2)`, the full characteristic-function content of Berry–Esseen (steps (i)–(iii)).
* `norm_charFun_pow_sub_edgeworth_le` — the **damped one-term Edgeworth expansion** of
  `(charFun μ)ⁿ`, the sharpening of the previous item that both retains the `n^{−1/2}` term and
  keeps a Gaussian envelope in the argument.
* `norm_charFun_iidSum_sub_gaussian_le` — the Berry–Esseen bound applied to the standardized
  i.i.d. sum `(√n)⁻¹ ∑ₖ Xₖ` via Mathlib's `charFun_inv_sqrt_mul_sum`.
* `fejerKernel`, `fejerKernel_nonneg`, `fejerKernel_even` — a partial foundation for Esseen's
  smoothing inequality.

## Status

The **characteristic-function half of Berry–Esseen is complete and axiom-clean**
(`norm_charFun_iidSum_sub_gaussian_le` and its inputs).

**Target 1, Esseen's smoothing inequality, is no longer open, and the verdict this file used
to record is dead.** All three ingredients listed below are now built in
`StatLean.HypothesisTesting.ForMathlib.EsseenSmoothing`:

* the sinc integral `∫(sin x/x)² dx = π` (`integral_sin_div_sq`) and hence the Fejér
  normalisation `∫ K_T = 1` (`integral_fejerKernel`);
* the Fejér/triangle Fourier pair, in the form `𝓕 Λ = (sin πξ/πξ)²` (`fourier_tentC`) and its
  dual `𝓕 ((sin πξ/πξ)²) = Λ` (`fourier_sqSincC`);
* the CDF-level smoothing inequality itself, `abs_measure_Iic_sub_le_charFun`. Crucially this
  is obtained **without** the Lévy/Esseen inversion formula for distribution functions that
  this file previously named as the binding obstruction: the argument runs on test functions
  (ramps and trapezoids) rather than on `F − G` directly, so the non-`L¹`-ness of `F − G` never
  arises.

What is genuinely missing for a *Kolmogorov-distance* Berry–Esseen theorem is therefore only
the assembly — choosing the flank width `δ` and integrating
`norm_charFun_pow_sub_gaussian_le` against the Esseen weight
`min(1/(π|ξ|), 1/(δπ²ξ²))`. Note that the undamped right-hand side of that bound is *not*
enough for the assembly to produce a rate; the damped
`norm_charFun_pow_sub_edgeworth_le` below is what the weighted integral needs, and its Gaussian
factor `e^{−v s²/4}` is supplied by `norm_charFun_le_exp_neg_sq`.

## Formalization notes

The two elementary estimates `norm_cexp_sub_taylor_le` (uniform third-order Taylor bound
for `exp (I y)`) and `norm_prod_sub_prod_le` (telescoping product bound) are needed both
here and in `LindebergCLT.lean`, where they are `private`. Rather than edit that file we
restate and reprove them verbatim, as the task requires.

**Reference.** W. Feller, *An Introduction to Probability Theory and Its Applications*,
Vol. II, 2nd ed., Wiley, 1971, §XVI.3 (smoothing) and §XVI.5 (Berry–Esseen).
-/

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology ENNReal NNReal Real

namespace StatLean.HypothesisTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### Elementary complex-analytic estimates (restated from `LindebergCLT`) -/

open Complex in
/-- **Uniform third-order remainder bound for `e^{iy}`.** The pointwise estimate driving
Lindeberg's swapping argument:
`‖exp (I y) − (1 + I y − y²/2)‖ ≤ min (|y|³/6) (y²)`.
Both bounds are elementary: the cubic half comes from integrating the exponential's remainder
three times, the quadratic half from `‖exp (I y) − 1 − I y‖ ≤ y²/2` and the triangle
inequality. Mathlib only provides the non-uniform `taylor_charFun_two`, so this is proved from
scratch here. -/
private lemma norm_cexp_sub_taylor_le (y : ℝ) :
    ‖Complex.exp (I * y) - (1 + I * y - (y : ℂ) ^ 2 / 2)‖ ≤ min (|y| ^ 3 / 6) (y ^ 2) := by
  -- Derivative of `u ↦ exp (I u)` (as a function of a real variable).
  have he : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w))
      (Complex.exp (I * ↑u) * I) u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using (h1.cexp).comp_ofReal
  -- `|exp (I u)| = 1`.
  have hnorme : ∀ u : ℝ, ‖Complex.exp (I * ↑u)‖ = 1 := by
    intro u; rw [Complex.norm_exp]; simp
  -- Derivative of `u ↦ I u`.
  have hIu : ∀ u : ℝ, HasDerivAt (fun w : ℝ => I * ↑w) I u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using h1.comp_ofReal
  -- Continuity of the three integrands.
  have hcontI : Continuous (fun u : ℝ => Complex.exp (I * ↑u) * I) := by fun_prop
  have hcont1 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1) * I) := by fun_prop
  have hcont2 : Continuous (fun u : ℝ => (Complex.exp (I * ↑u) - 1 - I * ↑u) * I) := by fun_prop
  -- Level 0: `‖exp (I z) − 1‖ ≤ z` for `z ≥ 0`.
  have hL0 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1‖ ≤ z := by
    intro z hz
    have hInt : (∫ u in (0:ℝ)..z, Complex.exp (I * ↑u) * I) = Complex.exp (I * ↑z) - 1 := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => he u)
        (hcontI.intervalIntegrable 0 z)]
      simp
    rw [← hInt]
    have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := z)
      (C := 1) (f := fun u => Complex.exp (I * ↑u) * I)
      (fun u _ => by rw [norm_mul, Complex.norm_I, mul_one]; exact le_of_eq (hnorme u))
    calc ‖∫ u in (0:ℝ)..z, Complex.exp (I * ↑u) * I‖ ≤ 1 * |z - 0| := hbnd
      _ = z := by rw [sub_zero, abs_of_nonneg hz, one_mul]
  -- Derivative of `A₁ w = exp (I w) − 1 − I w`.
  have hd1 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w)
      ((Complex.exp (I * ↑u) - 1) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1) * I = Complex.exp (I * ↑u) * I - 0 - I := by ring
    rw [heq]
    exact ((he u).sub (hasDerivAt_const u (1 : ℂ))).sub (hIu u)
  -- Level 1: `‖exp (I z) − 1 − I z‖ ≤ z²/2` for `z ≥ 0`.
  have hL1 : ∀ z : ℝ, 0 ≤ z → ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ z ^ 2 / 2 := by
    intro z hz
    have hInt : (∫ u in (0:ℝ)..z, (Complex.exp (I * ↑u) - 1) * I)
        = Complex.exp (I * ↑z) - 1 - I * ↑z := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd1 u)
        (hcont1.intervalIntegrable 0 z)]
      simp
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z‖ ≤ ∫ u in (0:ℝ)..z, u := by
      rw [← hInt]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        (continuous_id.intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL0 u hu.1.le
    rw [integral_id] at hb
    simpa using hb
  -- Derivative of `w ↦ w²/2` (written `w * w / 2`).
  have hsq : ∀ u : ℝ, HasDerivAt (fun w : ℝ => (↑w * ↑w / 2 : ℂ)) (↑u : ℂ) u := by
    intro u
    have hof : HasDerivAt (fun w : ℝ => (↑w : ℂ)) 1 u := by
      simpa using (hasDerivAt_id (↑u : ℂ)).comp_ofReal
    have heq : (↑u : ℂ) = (1 * ↑u + ↑u * 1) / 2 := by ring
    rw [heq]
    exact (hof.mul hof).div_const 2
  -- Derivative of `A₂ w = exp (I w) − 1 − I w + w²/2`.
  have hd2 : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w + ↑w * ↑w / 2)
      ((Complex.exp (I * ↑u) - 1 - I * ↑u) * I) u := by
    intro u
    have heq : (Complex.exp (I * ↑u) - 1 - I * ↑u) * I
        = (Complex.exp (I * ↑u) - 1) * I + ↑u := by
      have hI2 : (I : ℂ) * I = -1 := Complex.I_mul_I
      linear_combination (-(↑u : ℂ)) * hI2
    rw [heq]
    exact (hd1 u).add (hsq u)
  -- `A₂ z` as an integral of `A₁ · I`.
  have hA2z : ∀ z : ℝ, (∫ u in (0:ℝ)..z, (Complex.exp (I * ↑u) - 1 - I * ↑u) * I)
      = Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2 := by
    intro z
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd2 u)
      (hcont2.intervalIntegrable 0 z)]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    ring
  -- The `y ≥ 0` case of the goal (with `|y| = y`).
  have key : ∀ z : ℝ, 0 ≤ z →
      ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖ ≤ min (z ^ 3 / 6) (z ^ 2) := by
    intro z hz
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2‖
        ≤ ∫ u in (0:ℝ)..z, u ^ 2 / 2 := by
      rw [← hA2z z]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        ((by fun_prop : Continuous (fun u : ℝ => u ^ 2 / 2)).intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact hL1 u hu.1.le
    have hintval : (∫ u in (0:ℝ)..z, u ^ 2 / 2) = z ^ 3 / 6 := by
      rw [intervalIntegral.integral_div, integral_pow]; push_cast; ring
    refine le_min (hb.trans (le_of_eq hintval)) ?_
    have h1 := hL1 z hz
    have hcast : (↑z * ↑z / 2 : ℂ) = ((z * z / 2 : ℝ) : ℂ) := by push_cast; ring
    have hz2 : ‖(↑z * ↑z / 2 : ℂ)‖ = z ^ 2 / 2 := by
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]; ring
    have hsplit : Complex.exp (I * ↑z) - 1 - I * ↑z + ↑z * ↑z / 2
        = (Complex.exp (I * ↑z) - 1 - I * ↑z) + ↑z * ↑z / 2 := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [hz2]; linarith
  -- Reduce the goal to `A₂`.
  have hEq : Complex.exp (I * ↑y) - (1 + I * ↑y - (↑y : ℂ) ^ 2 / 2)
      = Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2 := by ring
  rw [hEq]
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]; exact key y hy
  · -- Reflect to `−y ≥ 0` via conjugation.
    have hz : (0:ℝ) ≤ -y := by linarith
    have hexp : (starRingEnd ℂ) (Complex.exp (I * ↑y)) = Complex.exp (I * ↑(-y)) := by
      rw [← Complex.exp_conj]; congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]; ring
    have hconj : (starRingEnd ℂ) (Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2)
        = Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2 := by
      simp only [map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I,
        Complex.conj_ofReal, hexp, Complex.ofReal_neg]
      ring
    have hnn : ‖Complex.exp (I * ↑y) - 1 - I * ↑y + ↑y * ↑y / 2‖
        = ‖Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + ↑(-y) * ↑(-y) / 2‖ := by
      rw [← hconj, Complex.norm_conj]
    rw [hnn, abs_of_neg hy, show (y : ℝ) ^ 2 = (-y) ^ 2 from by ring]
    exact key (-y) hz

open Complex in
/-- **The cubic remainder bound for `e^{iy}`, in public form.**
`‖exp (I y) − (1 + I y − y²/2)‖ ≤ |y|³/6`.

This is the `min`-free half of the private `norm_cexp_sub_taylor_le`, exported because the
*studentized* Edgeworth chain of `Bootstrap/Edgeworth.lean` expands `E[e^{iθHₙ}]` for the
delta-method surrogate `Hₙ` and needs the **cubic** — not the quadratic — remainder in order to
reach an `O(n⁻¹)` accuracy: the leading correction of the surrogate is itself of size `n^{-1/2}`,
so a quadratic remainder would only be `O(n⁻¹)` and would swamp the second-order term. -/
lemma norm_cexp_sub_quadratic_le (y : ℝ) :
    ‖Complex.exp (I * y) - (1 + I * y - (y : ℂ) ^ 2 / 2)‖ ≤ |y| ^ 3 / 6 :=
  (norm_cexp_sub_taylor_le y).trans (min_le_left _ _)

open Complex in
/-- **Second-order remainder bound for `e^{iy}`**, in the shape the *studentized* expansion
consumes: `‖exp (I y) − 1 − I y‖ ≤ 3 y² / 2`.

A corollary of `norm_cexp_sub_taylor_le` and the triangle inequality against the quadratic
monomial. The constant is not the sharp one (`1/2`) and does not need to be: in
`ForMathlib/BivariateEdgeworth.lean` it multiplies a remainder that is already `O(n^{-1/2})`
after the `n`-fold factorisation, so only its finiteness matters. -/
lemma norm_cexp_sub_one_sub_mul_I_le (y : ℝ) :
    ‖Complex.exp (I * y) - 1 - I * y‖ ≤ 3 * y ^ 2 / 2 := by
  have h : ‖Complex.exp (I * y) - (1 + I * y - (y : ℂ) ^ 2 / 2)‖ ≤ y ^ 2 :=
    (norm_cexp_sub_taylor_le y).trans (min_le_right _ _)
  have he : Complex.exp (I * y) - 1 - I * y
      = Complex.exp (I * y) - (1 + I * y - (y : ℂ) ^ 2 / 2) - (y : ℂ) ^ 2 / 2 := by ring
  have h2 : ‖((y : ℂ) ^ 2 / 2)‖ = y ^ 2 / 2 := by
    rw [norm_div, ← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg y)]
    norm_num
  calc ‖Complex.exp (I * y) - 1 - I * y‖
      ≤ ‖Complex.exp (I * y) - (1 + I * y - (y : ℂ) ^ 2 / 2)‖ + ‖((y : ℂ) ^ 2 / 2)‖ := by
        rw [he]; exact norm_sub_le _ _
    _ ≤ 3 * y ^ 2 / 2 := by rw [h2]; linarith

open Complex in
/-- **Uniform fourth-order remainder bound for `e^{iy}`.** The next order of
`norm_cexp_sub_taylor_le`:
`‖exp (I y) − (1 + I y − y²/2 − I y³/6)‖ ≤ min (|y|⁴/24) (|y|³/3)`.
The quartic half is obtained by integrating the cubic bound of `norm_cexp_sub_taylor_le` once
more; the cubic half is the triangle inequality against the extra monomial `I y³/6`. This is
the pointwise input of the *one-term Edgeworth* expansion, where the third cumulant has to be
retained rather than absorbed into the remainder. -/
private lemma norm_cexp_sub_taylor3_le (y : ℝ) :
    ‖Complex.exp (I * y) - (1 + I * y - (y : ℂ) ^ 2 / 2 - I * (y : ℂ) ^ 3 / 6)‖
      ≤ min (|y| ^ 4 / 24) (|y| ^ 3 / 3) := by
  -- The third-order remainder, in the "`A₂`" shape that integrates to the fourth-order one.
  have hA2 : ∀ u : ℝ, ‖Complex.exp (I * ↑u) - 1 - I * ↑u + (↑u : ℂ) ^ 2 / 2‖ ≤ |u| ^ 3 / 6 := by
    intro u
    have heq : Complex.exp (I * ↑u) - 1 - I * ↑u + (↑u : ℂ) ^ 2 / 2
        = Complex.exp (I * ↑u) - (1 + I * ↑u - (↑u : ℂ) ^ 2 / 2) := by ring
    rw [heq]
    exact (norm_cexp_sub_taylor_le u).trans (min_le_left _ _)
  -- Derivative of `u ↦ exp (I u)` (as a function of a real variable).
  have he : ∀ u : ℝ, HasDerivAt (fun w : ℝ => Complex.exp (I * ↑w))
      (Complex.exp (I * ↑u) * I) u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using (h1.cexp).comp_ofReal
  have hIu : ∀ u : ℝ, HasDerivAt (fun w : ℝ => I * ↑w) I u := by
    intro u
    have h1 : HasDerivAt (fun w : ℂ => I * w) I (↑u : ℂ) := by
      simpa using (hasDerivAt_id (↑u : ℂ)).const_mul I
    simpa using h1.comp_ofReal
  have hof : ∀ u : ℝ, HasDerivAt (fun w : ℝ => (↑w : ℂ)) 1 u := by
    intro u
    simpa using (hasDerivAt_id (↑u : ℂ)).comp_ofReal
  -- `A₃ w = exp (I w) − 1 − I w + w²/2 + I w³/6` has derivative `A₂ w · I`.
  have hd3 : ∀ u : ℝ, HasDerivAt
      (fun w : ℝ => Complex.exp (I * ↑w) - 1 - I * ↑w + (↑w : ℂ) ^ 2 / 2 + I * (↑w : ℂ) ^ 3 / 6)
      ((Complex.exp (I * ↑u) - 1 - I * ↑u + (↑u : ℂ) ^ 2 / 2) * I) u := by
    intro u
    have h1 : HasDerivAt (fun w : ℝ => (↑w : ℂ) ^ 2 / 2) (↑u : ℂ) u := by
      have h := ((hof u).pow 2).div_const 2
      simpa using h
    have h2 : HasDerivAt (fun w : ℝ => I * (↑w : ℂ) ^ 3 / 6) (I * (↑u : ℂ) ^ 2 / 2) u := by
      have h := (((hof u).pow 3).const_mul I).div_const 6
      convert! h using 1
      push_cast
      ring
    have hbase := ((he u).sub (hasDerivAt_const u (1 : ℂ))).sub (hIu u)
    have h := (hbase.add h1).add h2
    convert! h using 1
    have hI2 : (I : ℂ) * I = -1 := Complex.I_mul_I
    linear_combination (-(↑u : ℂ)) * hI2
  have hcont3 : Continuous
      (fun u : ℝ => (Complex.exp (I * ↑u) - 1 - I * ↑u + (↑u : ℂ) ^ 2 / 2) * I) := by fun_prop
  have hA3z : ∀ z : ℝ,
      (∫ u in (0 : ℝ)..z, (Complex.exp (I * ↑u) - 1 - I * ↑u + (↑u : ℂ) ^ 2 / 2) * I)
      = Complex.exp (I * ↑z) - 1 - I * ↑z + (↑z : ℂ) ^ 2 / 2 + I * (↑z : ℂ) ^ 3 / 6 := by
    intro z
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd3 u)
      (hcont3.intervalIntegrable 0 z)]
    simp
  -- The `z ≥ 0` case of the quartic bound.
  have key : ∀ z : ℝ, 0 ≤ z →
      ‖Complex.exp (I * ↑z) - 1 - I * ↑z + (↑z : ℂ) ^ 2 / 2 + I * (↑z : ℂ) ^ 3 / 6‖
        ≤ z ^ 4 / 24 := by
    intro z hz
    have hb : ‖Complex.exp (I * ↑z) - 1 - I * ↑z + (↑z : ℂ) ^ 2 / 2 + I * (↑z : ℂ) ^ 3 / 6‖
        ≤ ∫ u in (0 : ℝ)..z, u ^ 3 / 6 := by
      rw [← hA3z z]
      refine intervalIntegral.norm_integral_le_of_norm_le hz (ae_of_all _ fun u hu => ?_)
        ((by fun_prop : Continuous (fun u : ℝ => u ^ 3 / 6)).intervalIntegrable 0 z)
      rw [norm_mul, Complex.norm_I, mul_one]
      exact (hA2 u).trans_eq (by rw [abs_of_nonneg hu.1.le])
    have hintval : (∫ u in (0 : ℝ)..z, u ^ 3 / 6) = z ^ 4 / 24 := by
      rw [intervalIntegral.integral_div, integral_pow]; push_cast; ring
    exact hb.trans_eq hintval
  have hEq : Complex.exp (I * ↑y) - (1 + I * ↑y - (↑y : ℂ) ^ 2 / 2 - I * (↑y : ℂ) ^ 3 / 6)
      = Complex.exp (I * ↑y) - 1 - I * ↑y + (↑y : ℂ) ^ 2 / 2 + I * (↑y : ℂ) ^ 3 / 6 := by ring
  rw [hEq]
  refine le_min ?_ ?_
  · -- Quartic half: reflect to `−y ≥ 0` when `y < 0`.
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy]; exact key y hy
    · have hz : (0 : ℝ) ≤ -y := by linarith
      have hexp : (starRingEnd ℂ) (Complex.exp (I * ↑y)) = Complex.exp (I * ↑(-y)) := by
        rw [← Complex.exp_conj]; congr 1
        simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]; ring
      have hconj : (starRingEnd ℂ)
            (Complex.exp (I * ↑y) - 1 - I * ↑y + (↑y : ℂ) ^ 2 / 2 + I * (↑y : ℂ) ^ 3 / 6)
          = Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + (↑(-y) : ℂ) ^ 2 / 2
              + I * (↑(-y) : ℂ) ^ 3 / 6 := by
        simp only [map_add, map_sub, map_mul, map_div₀, map_one, map_pow, map_ofNat,
          Complex.conj_I, Complex.conj_ofReal, hexp, Complex.ofReal_neg]
        ring
      have hnn : ‖Complex.exp (I * ↑y) - 1 - I * ↑y + (↑y : ℂ) ^ 2 / 2 + I * (↑y : ℂ) ^ 3 / 6‖
          = ‖Complex.exp (I * ↑(-y)) - 1 - I * ↑(-y) + (↑(-y) : ℂ) ^ 2 / 2
              + I * (↑(-y) : ℂ) ^ 3 / 6‖ := by
        rw [← hconj, Complex.norm_conj]
      rw [hnn, abs_of_neg hy]
      exact key (-y) hz
  · -- Cubic half: triangle inequality against the extra monomial.
    have hmon : ‖I * (↑y : ℂ) ^ 3 / 6‖ = |y| ^ 3 / 6 := by
      rw [norm_div, norm_mul, Complex.norm_I, one_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs]
      norm_num
    have hsplit : Complex.exp (I * ↑y) - 1 - I * ↑y + (↑y : ℂ) ^ 2 / 2 + I * (↑y : ℂ) ^ 3 / 6
        = (Complex.exp (I * ↑y) - 1 - I * ↑y + (↑y : ℂ) ^ 2 / 2) + I * (↑y : ℂ) ^ 3 / 6 := by
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [hmon]
    linarith [hA2 y]

/-- **Telescoping product bound** (restated from `LindebergCLT`). -/
private lemma norm_prod_sub_prod_le {ι : Type*} {𝕜 : Type*} [RCLike 𝕜] (s : Finset ι)
    (f g : ι → 𝕜) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1) (hg : ∀ i ∈ s, ‖g i‖ ≤ 1) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hf' := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hg' := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a s)
    have key : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
        = f a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
    rw [key]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have hpg : ‖∏ i ∈ s, g i‖ ≤ 1 := by
      rw [norm_prod]; exact Finset.prod_le_one (fun i _ => norm_nonneg _) hg'
    have h1 : ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖f i - g i‖ :=
      calc ‖f a‖ * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖
            ≤ 1 * ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ :=
              mul_le_mul_of_nonneg_right hfa (norm_nonneg _)
        _ = ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ := one_mul _
        _ ≤ ∑ i ∈ s, ‖f i - g i‖ := ih hf' hg'
    have h2 : ‖f a - g a‖ * ‖∏ i ∈ s, g i‖ ≤ ‖f a - g a‖ :=
      calc ‖f a - g a‖ * ‖∏ i ∈ s, g i‖
            ≤ ‖f a - g a‖ * 1 := mul_le_mul_of_nonneg_left hpg (norm_nonneg _)
        _ = ‖f a - g a‖ := mul_one _
    linarith

/-- **Second-order telescoping bound.** The first-order telescoping estimate
`norm_prod_sub_prod_le` loses the whole `n^{-1/2}` term of an Edgeworth expansion; what is
needed instead is the *quadratic* remainder after subtracting the linear term:
`‖aⁿ − bⁿ − n bⁿ⁻¹ (a − b)‖ ≤ n(n−1)/2 · Mⁿ⁻² ‖a − b‖²` whenever `‖a‖, ‖b‖ ≤ M`.

Written with `n = m + 2` so that the two decremented exponents are literal. The induction step
is the identity `Δₙ₊₁ = a Δₙ + n bⁿ⁻¹ (a − b)²`, which turns the claim into the arithmetic
identity `n(n−1)/2 + n = n(n+1)/2`. Because `M` is carried along, the bound **retains the
damping** `Mⁿ⁻²` — this is exactly what the undamped `norm_charFun_pow_sub_gaussian_le` throws
away, and what makes the Edgeworth remainder integrable against the Esseen weight. -/
private lemma norm_pow_sub_pow_sub_lin_le {a b : ℂ} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M)
    (m : ℕ) :
    ‖a ^ (m + 2) - b ^ (m + 2) - ((m : ℂ) + 2) * b ^ (m + 1) * (a - b)‖
      ≤ ((m : ℝ) + 2) * ((m : ℝ) + 1) / 2 * M ^ m * ‖a - b‖ ^ 2 := by
  have hM : 0 ≤ M := (norm_nonneg a).trans ha
  have hbpow : ∀ j : ℕ, ‖b‖ ^ j ≤ M ^ j := fun j => pow_le_pow_left₀ (norm_nonneg b) hb j
  induction m with
  | zero =>
    have heq : a ^ (0 + 2) - b ^ (0 + 2) - (((0 : ℕ) : ℂ) + 2) * b ^ (0 + 1) * (a - b)
        = (a - b) ^ 2 := by push_cast; ring
    rw [heq, norm_pow]
    norm_num
  | succ k ih =>
    have hkey : a ^ (k + 1 + 2) - b ^ (k + 1 + 2)
          - (((k + 1 : ℕ) : ℂ) + 2) * b ^ (k + 1 + 1) * (a - b)
        = a * (a ^ (k + 2) - b ^ (k + 2) - ((k : ℂ) + 2) * b ^ (k + 1) * (a - b))
          + ((k : ℂ) + 2) * b ^ (k + 1) * (a - b) ^ 2 := by push_cast; ring
    have hnc : ‖((k : ℂ) + 2)‖ = (k : ℝ) + 2 := by
      have hc : ((k : ℂ) + 2) = (((k : ℝ) + 2 : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have t1 : ‖a * (a ^ (k + 2) - b ^ (k + 2) - ((k : ℂ) + 2) * b ^ (k + 1) * (a - b))‖
        ≤ M * (((k : ℝ) + 2) * ((k : ℝ) + 1) / 2 * M ^ k * ‖a - b‖ ^ 2) := by
      rw [norm_mul]
      exact mul_le_mul ha ih (norm_nonneg _) hM
    have t2 : ‖((k : ℂ) + 2) * b ^ (k + 1) * (a - b) ^ 2‖
        ≤ ((k : ℝ) + 2) * M ^ (k + 1) * ‖a - b‖ ^ 2 := by
      rw [norm_mul, norm_mul, hnc, norm_pow, norm_pow]
      have h1 : ((k : ℝ) + 2) * ‖b‖ ^ (k + 1) ≤ ((k : ℝ) + 2) * M ^ (k + 1) :=
        mul_le_mul_of_nonneg_left (hbpow (k + 1)) (by positivity)
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have hMk : M * M ^ k = M ^ (k + 1) := by rw [pow_succ]; ring
    calc ‖a ^ (k + 1 + 2) - b ^ (k + 1 + 2)
            - (((k + 1 : ℕ) : ℂ) + 2) * b ^ (k + 1 + 1) * (a - b)‖
        = ‖a * (a ^ (k + 2) - b ^ (k + 2) - ((k : ℂ) + 2) * b ^ (k + 1) * (a - b))
            + ((k : ℂ) + 2) * b ^ (k + 1) * (a - b) ^ 2‖ := by rw [hkey]
      _ ≤ ‖a * (a ^ (k + 2) - b ^ (k + 2) - ((k : ℂ) + 2) * b ^ (k + 1) * (a - b))‖
            + ‖((k : ℂ) + 2) * b ^ (k + 1) * (a - b) ^ 2‖ := norm_add_le _ _
      _ ≤ M * (((k : ℝ) + 2) * ((k : ℝ) + 1) / 2 * M ^ k * ‖a - b‖ ^ 2)
            + ((k : ℝ) + 2) * M ^ (k + 1) * ‖a - b‖ ^ 2 := add_le_add t1 t2
      _ = (((k : ℝ) + 1) + 2) * (((k : ℝ) + 1) + 1) / 2 * M ^ (k + 1) * ‖a - b‖ ^ 2 := by
          rw [← hMk]; ring
      _ = ((↑(k + 1) : ℝ) + 2) * ((↑(k + 1) : ℝ) + 1) / 2 * M ^ (k + 1) * ‖a - b‖ ^ 2 := by
          push_cast; ring

/-! ### Characteristic-function Gaussian approximation

The analytic heart of Berry–Esseen: the characteristic function of a centered
square-integrable law with finite third moment is close to its second-order Taylor
polynomial `1 - v u²/2`, uniformly, with error `ρ|u|³/6`. This is `norm_cexp_sub_taylor_le`
integrated against the law, and needs no Fourier theory. -/

/-- **Second-order approximation of a characteristic function.** For a probability measure
`μ` on `ℝ` with mean `0`, second moment `v`, and finite third absolute moment `ρ = ∫|x|³`,
the characteristic function satisfies
`‖charFun μ u − (1 − v u²/2)‖ ≤ ρ |u|³ / 6` for all `u`. -/
theorem norm_charFun_sub_quadratic_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ} (hint1 : Integrable (fun x => x) μ)
    (hint2 : Integrable (fun x => x ^ 2) μ) (hint3 : Integrable (fun x => |x| ^ 3) μ)
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = v) (u : ℝ) :
    ‖charFun μ u - (1 - (v : ℂ) * (u : ℂ) ^ 2 / 2)‖ ≤ (∫ x, |x| ^ 3 ∂μ) * |u| ^ 3 / 6 := by
  -- The complex exponential integrand of `charFun`.
  have hExpInt : Integrable (fun x : ℝ => Complex.exp (↑u * ↑x * I)) μ := by
    refine (integrable_const (1 : ℝ)).mono'
      ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    have hre : ((u : ℂ) * (x : ℂ) * I).re = 0 := by simp
    rw [Complex.norm_exp, hre, Real.exp_zero]
  -- The quadratic Taylor integrand.
  set p : ℝ → ℂ := fun x => 1 + ↑u * ↑x * I - (↑u * ↑x) ^ 2 / 2 with hp
  have hxC : Integrable (fun x : ℝ => (x : ℂ)) μ := hint1.ofReal
  have hx2C : Integrable (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ)) μ := hint2.ofReal
  have t2 : Integrable (fun x : ℝ => (↑u * ↑x * I : ℂ)) μ := by
    have := (hxC.const_mul (↑u * I : ℂ))
    refine this.congr (ae_of_all _ fun x => ?_); ring
  have t3 : Integrable (fun x : ℝ => ((↑u * ↑x) ^ 2 / 2 : ℂ)) μ := by
    have := (hx2C.const_mul (↑u ^ 2 / 2 : ℂ))
    refine this.congr (ae_of_all _ fun x => ?_); push_cast; ring
  have hPolyInt : Integrable p μ := by
    simp only [hp]; exact ((integrable_const (1 : ℂ)).add t2).sub t3
  -- Compute `∫ p = 1 - v u²/2`.
  have e1 : ∫ _x : ℝ, (1 : ℂ) ∂μ = 1 := by simp
  have e2 : ∫ x : ℝ, (↑u * ↑x * I : ℂ) ∂μ = 0 := by
    have hc : ∫ x : ℝ, (↑u * ↑x * I : ℂ) ∂μ = ∫ x : ℝ, ((↑u * I) • (↑x : ℂ)) ∂μ := by
      apply integral_congr_ae; filter_upwards with x; rw [smul_eq_mul]; ring
    rw [hc, integral_smul, integral_complex_ofReal, hmean]; simp
  have e3 : ∫ x : ℝ, ((↑u * ↑x) ^ 2 / 2 : ℂ) ∂μ = (v : ℂ) * (u : ℂ) ^ 2 / 2 := by
    have hc : ∫ x : ℝ, ((↑u * ↑x) ^ 2 / 2 : ℂ) ∂μ
        = ∫ x : ℝ, (((↑u : ℂ) ^ 2 / 2) • ((x ^ 2 : ℝ) : ℂ)) ∂μ := by
      apply integral_congr_ae; filter_upwards with x; rw [smul_eq_mul]; push_cast; ring
    rw [hc, integral_smul, integral_complex_ofReal, hvar, smul_eq_mul]; ring
  have hsum : Integrable (fun x : ℝ => (1 + ↑u * ↑x * I : ℂ)) μ :=
    ((integrable_const (1 : ℂ)).add t2).congr (ae_of_all _ fun x => rfl)
  have hIntP : ∫ x, p x ∂μ = 1 - (v : ℂ) * (u : ℂ) ^ 2 / 2 := by
    calc ∫ x, p x ∂μ
        = ∫ x, ((1 + ↑u * ↑x * I : ℂ) - (↑u * ↑x) ^ 2 / 2) ∂μ := by simp only [hp]
      _ = (∫ x, (1 + ↑u * ↑x * I : ℂ) ∂μ) - ∫ x, ((↑u * ↑x) ^ 2 / 2 : ℂ) ∂μ :=
            integral_sub hsum t3
      _ = ((∫ _x : ℝ, (1 : ℂ) ∂μ) + ∫ x, (↑u * ↑x * I : ℂ) ∂μ)
            - ∫ x, ((↑u * ↑x) ^ 2 / 2 : ℂ) ∂μ := by
            rw [integral_add (integrable_const 1) t2]
      _ = 1 - (v : ℂ) * (u : ℂ) ^ 2 / 2 := by rw [e1, e2, e3]; ring
  -- Pointwise Taylor bound.
  have hpt : ∀ x : ℝ, ‖Complex.exp (↑u * ↑x * I) - p x‖ ≤ |u| ^ 3 * |x| ^ 3 / 6 := by
    intro x
    have h := norm_cexp_sub_taylor_le (u * x)
    have harg : (↑u * ↑x * I : ℂ) = I * ↑(u * x) := by push_cast; ring
    have hsq : ((↑u * ↑x : ℂ)) ^ 2 = (↑(u * x) : ℂ) ^ 2 := by push_cast; ring
    rw [hp]; simp only []
    rw [harg, hsq]
    calc ‖Complex.exp (I * ↑(u * x)) - (1 + I * ↑(u * x) - (↑(u * x) : ℂ) ^ 2 / 2)‖
        ≤ min (|u * x| ^ 3 / 6) ((u * x) ^ 2) := h
      _ ≤ |u * x| ^ 3 / 6 := min_le_left _ _
      _ = |u| ^ 3 * |x| ^ 3 / 6 := by rw [abs_mul, mul_pow]
  -- Assemble.
  rw [charFun_apply_real, ← hIntP, ← integral_sub hExpInt hPolyInt]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hbound : Integrable (fun x : ℝ => |u| ^ 3 * |x| ^ 3 / 6) μ := by
    have := (hint3.const_mul (|u| ^ 3)).div_const 6
    exact this
  calc ∫ x, ‖Complex.exp (↑u * ↑x * I) - p x‖ ∂μ
      ≤ ∫ x, |u| ^ 3 * |x| ^ 3 / 6 ∂μ :=
        integral_mono ((hExpInt.sub hPolyInt).norm) hbound hpt
    _ = (∫ x, |x| ^ 3 ∂μ) * |u| ^ 3 / 6 := by
        rw [integral_div, integral_const_mul]; ring

/-- **Third-order approximation of a characteristic function.** For a probability measure `μ`
on `ℝ` with mean `0`, second moment `v`, third moment `m₃` and finite fourth moment,
`‖charFun μ u − (1 − v u²/2 − i m₃ u³/6)‖ ≤ (∫ x⁴) |u|⁴ / 24` for all `u`.

This is the expansion the *one-term Edgeworth* correction is read off from: unlike
`norm_charFun_sub_quadratic_le`, the cubic term (the third cumulant, since the mean vanishes)
is **retained** rather than absorbed into the remainder, and the remainder drops to order
`u⁴`. -/
theorem norm_charFun_sub_cubic_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v m₃ : ℝ} (hint1 : Integrable (fun x => x) μ)
    (hint2 : Integrable (fun x => x ^ 2) μ) (hint3 : Integrable (fun x => x ^ 3) μ)
    (hint4 : Integrable (fun x => x ^ 4) μ)
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = v) (hthird : ∫ x, x ^ 3 ∂μ = m₃) (u : ℝ) :
    ‖charFun μ u - (1 - (v : ℂ) * (u : ℂ) ^ 2 / 2 - I * (m₃ : ℂ) * (u : ℂ) ^ 3 / 6)‖
      ≤ (∫ x, x ^ 4 ∂μ) * |u| ^ 4 / 24 := by
  -- The complex exponential integrand of `charFun`.
  have hExpInt : Integrable (fun x : ℝ => Complex.exp (↑u * ↑x * I)) μ := by
    refine (integrable_const (1 : ℝ)).mono'
      ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    have hre : ((u : ℂ) * (x : ℂ) * I).re = 0 := by simp
    rw [Complex.norm_exp, hre, Real.exp_zero]
  -- The cubic Taylor integrand.
  set p : ℝ → ℂ := fun x => 1 + ↑u * ↑x * I - (↑u * ↑x) ^ 2 / 2 - I * (↑u * ↑x) ^ 3 / 6 with hp
  have hxC : Integrable (fun x : ℝ => (x : ℂ)) μ := hint1.ofReal
  have hx2C : Integrable (fun x : ℝ => ((x ^ 2 : ℝ) : ℂ)) μ := hint2.ofReal
  have hx3C : Integrable (fun x : ℝ => ((x ^ 3 : ℝ) : ℂ)) μ := hint3.ofReal
  have t2 : Integrable (fun x : ℝ => (↑u * ↑x * I : ℂ)) μ := by
    have := (hxC.const_mul (↑u * I : ℂ))
    refine this.congr (ae_of_all _ fun x => ?_); ring
  have t3 : Integrable (fun x : ℝ => ((↑u * ↑x) ^ 2 / 2 : ℂ)) μ := by
    have := (hx2C.const_mul (↑u ^ 2 / 2 : ℂ))
    refine this.congr (ae_of_all _ fun x => ?_); push_cast; ring
  have t4 : Integrable (fun x : ℝ => (I * (↑u * ↑x) ^ 3 / 6 : ℂ)) μ := by
    have := (hx3C.const_mul (I * ↑u ^ 3 / 6 : ℂ))
    refine this.congr (ae_of_all _ fun x => ?_); push_cast; ring
  have hPolyInt : Integrable p μ := by
    simp only [hp]; exact (((integrable_const (1 : ℂ)).add t2).sub t3).sub t4
  -- Compute `∫ p = 1 − v u²/2 − i m₃ u³/6`.
  have e1 : ∫ _x : ℝ, (1 : ℂ) ∂μ = 1 := by simp
  have e2 : ∫ x : ℝ, (↑u * ↑x * I : ℂ) ∂μ = 0 := by
    have hc : ∫ x : ℝ, (↑u * ↑x * I : ℂ) ∂μ = ∫ x : ℝ, ((↑u * I) • (↑x : ℂ)) ∂μ := by
      apply integral_congr_ae; filter_upwards with x; rw [smul_eq_mul]; ring
    rw [hc, integral_smul, integral_complex_ofReal, hmean]; simp
  have e3 : ∫ x : ℝ, ((↑u * ↑x) ^ 2 / 2 : ℂ) ∂μ = (v : ℂ) * (u : ℂ) ^ 2 / 2 := by
    have hc : ∫ x : ℝ, ((↑u * ↑x) ^ 2 / 2 : ℂ) ∂μ
        = ∫ x : ℝ, (((↑u : ℂ) ^ 2 / 2) • ((x ^ 2 : ℝ) : ℂ)) ∂μ := by
      apply integral_congr_ae; filter_upwards with x; rw [smul_eq_mul]; push_cast; ring
    rw [hc, integral_smul, integral_complex_ofReal, hvar, smul_eq_mul]; ring
  have e4 : ∫ x : ℝ, (I * (↑u * ↑x) ^ 3 / 6 : ℂ) ∂μ = I * (m₃ : ℂ) * (u : ℂ) ^ 3 / 6 := by
    have hc : ∫ x : ℝ, (I * (↑u * ↑x) ^ 3 / 6 : ℂ) ∂μ
        = ∫ x : ℝ, ((I * (↑u : ℂ) ^ 3 / 6) • ((x ^ 3 : ℝ) : ℂ)) ∂μ := by
      apply integral_congr_ae; filter_upwards with x; rw [smul_eq_mul]; push_cast; ring
    rw [hc, integral_smul, integral_complex_ofReal, hthird, smul_eq_mul]; ring
  have hsum : Integrable (fun x : ℝ => (1 + ↑u * ↑x * I : ℂ)) μ :=
    ((integrable_const (1 : ℂ)).add t2).congr (ae_of_all _ fun x => rfl)
  have hsum2 : Integrable (fun x : ℝ => (1 + ↑u * ↑x * I - (↑u * ↑x) ^ 2 / 2 : ℂ)) μ :=
    hsum.sub t3
  have hIntP : ∫ x, p x ∂μ
      = 1 - (v : ℂ) * (u : ℂ) ^ 2 / 2 - I * (m₃ : ℂ) * (u : ℂ) ^ 3 / 6 := by
    calc ∫ x, p x ∂μ
        = ∫ x, ((1 + ↑u * ↑x * I - (↑u * ↑x) ^ 2 / 2 : ℂ) - I * (↑u * ↑x) ^ 3 / 6) ∂μ := by
          simp only [hp]
      _ = (∫ x, (1 + ↑u * ↑x * I - (↑u * ↑x) ^ 2 / 2 : ℂ) ∂μ)
            - ∫ x, (I * (↑u * ↑x) ^ 3 / 6 : ℂ) ∂μ := integral_sub hsum2 t4
      _ = ((∫ x, (1 + ↑u * ↑x * I : ℂ) ∂μ) - ∫ x, ((↑u * ↑x) ^ 2 / 2 : ℂ) ∂μ)
            - ∫ x, (I * (↑u * ↑x) ^ 3 / 6 : ℂ) ∂μ := by rw [integral_sub hsum t3]
      _ = (((∫ _x : ℝ, (1 : ℂ) ∂μ) + ∫ x, (↑u * ↑x * I : ℂ) ∂μ)
            - ∫ x, ((↑u * ↑x) ^ 2 / 2 : ℂ) ∂μ) - ∫ x, (I * (↑u * ↑x) ^ 3 / 6 : ℂ) ∂μ := by
          rw [integral_add (integrable_const 1) t2]
      _ = 1 - (v : ℂ) * (u : ℂ) ^ 2 / 2 - I * (m₃ : ℂ) * (u : ℂ) ^ 3 / 6 := by
          rw [e1, e2, e3, e4]; ring
  -- Pointwise Taylor bound.
  have hpt : ∀ x : ℝ, ‖Complex.exp (↑u * ↑x * I) - p x‖ ≤ |u| ^ 4 * x ^ 4 / 24 := by
    intro x
    have h := norm_cexp_sub_taylor3_le (u * x)
    have harg : (↑u * ↑x * I : ℂ) = I * ↑(u * x) := by push_cast; ring
    have hsq : ((↑u * ↑x : ℂ)) ^ 2 = (↑(u * x) : ℂ) ^ 2 := by push_cast; ring
    have hcb : ((↑u * ↑x : ℂ)) ^ 3 = (↑(u * x) : ℂ) ^ 3 := by push_cast; ring
    rw [hp]; simp only []
    rw [harg, hsq, hcb]
    calc ‖Complex.exp (I * ↑(u * x))
            - (1 + I * ↑(u * x) - (↑(u * x) : ℂ) ^ 2 / 2 - I * (↑(u * x) : ℂ) ^ 3 / 6)‖
        ≤ min (|u * x| ^ 4 / 24) (|u * x| ^ 3 / 3) := h
      _ ≤ |u * x| ^ 4 / 24 := min_le_left _ _
      _ = |u| ^ 4 * x ^ 4 / 24 := by
          have hx : |x| ^ 4 = x ^ 4 := by
            rw [pow_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
          rw [abs_mul, mul_pow, hx]
  -- Assemble.
  rw [charFun_apply_real, ← hIntP, ← integral_sub hExpInt hPolyInt]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hbound : Integrable (fun x : ℝ => |u| ^ 4 * x ^ 4 / 24) μ :=
    (hint4.const_mul (|u| ^ 4)).div_const 24
  calc ∫ x, ‖Complex.exp (↑u * ↑x * I) - p x‖ ∂μ
      ≤ ∫ x, |u| ^ 4 * x ^ 4 / 24 ∂μ :=
        integral_mono ((hExpInt.sub hPolyInt).norm) hbound hpt
    _ = (∫ x, x ^ 4 ∂μ) * |u| ^ 4 / 24 := by
        rw [integral_div, integral_const_mul]; ring

/-- **Gaussian majorant for a characteristic function on a window around the origin.**

On the window `v s² ≤ 2` and `ρ |s| ≤ 3v/2` (`ρ = ∫|x|³`), a centred law satisfies
`‖charFun μ s‖ ≤ exp(−v s²/4)`.

This is the second ingredient the Edgeworth remainder needs. Raised to the `n`-th power it
supplies the factor `e^{−t²/4}` that damps the remainder in the Esseen integral; without it the
`n`-fold power bound of `norm_charFun_pow_sub_gaussian_le` is uniform in `t` and the whole rate
is lost. The proof is `‖φ(s)‖ ≤ |1 − v s²/2| + ρ|s|³/6 ≤ 1 − v s²/2 + v s²/4 ≤ e^{−v s²/4}`,
the middle step using `ρ|s|³ = (ρ|s|) s² ≤ (3v/2) s²`. -/
theorem norm_charFun_le_exp_neg_sq (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ} (hint1 : Integrable (fun x => x) μ)
    (hint2 : Integrable (fun x => x ^ 2) μ) (hint3 : Integrable (fun x => |x| ^ 3) μ)
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = v) {s : ℝ}
    (hs2 : v * s ^ 2 ≤ 2) (hs3 : (∫ x, |x| ^ 3 ∂μ) * |s| ≤ 3 * v / 2) :
    ‖charFun μ s‖ ≤ Real.exp (-(v * s ^ 2 / 4)) := by
  have h := norm_charFun_sub_quadratic_le μ hint1 hint2 hint3 hmean hvar s
  have hq : ‖(1 - (v : ℂ) * (s : ℂ) ^ 2 / 2)‖ = 1 - v * s ^ 2 / 2 := by
    have hcast : (1 - (v : ℂ) * (s : ℂ) ^ 2 / 2) = ((1 - v * s ^ 2 / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have htail : (∫ x, |x| ^ 3 ∂μ) * |s| ^ 3 / 6 ≤ v * s ^ 2 / 4 := by
    have habs : |s| ^ 3 = s ^ 2 * |s| := by rw [pow_succ, sq_abs]
    have hmul := mul_le_mul_of_nonneg_right hs3 (sq_nonneg s)
    rw [habs]
    linarith [hmul]
  have hsplit : charFun μ s
      = (charFun μ s - (1 - (v : ℂ) * (s : ℂ) ^ 2 / 2)) + (1 - (v : ℂ) * (s : ℂ) ^ 2 / 2) := by
    ring
  calc ‖charFun μ s‖
      = ‖(charFun μ s - (1 - (v : ℂ) * (s : ℂ) ^ 2 / 2)) + (1 - (v : ℂ) * (s : ℂ) ^ 2 / 2)‖ := by
        rw [← hsplit]
    _ ≤ ‖charFun μ s - (1 - (v : ℂ) * (s : ℂ) ^ 2 / 2)‖ + ‖(1 - (v : ℂ) * (s : ℂ) ^ 2 / 2)‖ :=
        norm_add_le _ _
    _ ≤ (∫ x, |x| ^ 3 ∂μ) * |s| ^ 3 / 6 + (1 - v * s ^ 2 / 2) := by rw [hq]; linarith
    _ ≤ 1 - v * s ^ 2 / 4 := by linarith
    _ ≤ Real.exp (-(v * s ^ 2 / 4)) := by linarith [Real.add_one_le_exp (-(v * s ^ 2 / 4))]

/-- **Quadratic upper bound for `e^{-z}`.** For `z ≥ 0`, `e^{-z} ≤ 1 - z + z²/2`. Combined
with `1 - z ≤ e^{-z}` (`Real.add_one_le_exp`) this pins `|e^{-z} - (1 - z)| ≤ z²/2`. -/
private lemma exp_neg_le_quadratic {z : ℝ} (hz : 0 ≤ z) :
    Real.exp (-z) ≤ 1 - z + z ^ 2 / 2 := by
  set f : ℝ → ℝ := fun t => 1 - t + t ^ 2 / 2 - Real.exp (-t) with hf
  have hderiv : ∀ x, HasDerivAt f (-1 + x + Real.exp (-x)) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => 1 - t + t ^ 2 / 2) (0 - 1 + 2 * x ^ 1 / 2) x :=
      ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add ((hasDerivAt_pow 2 x).div_const 2)
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
      simpa using! (Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)
    have := h1.sub h2
    convert! this using 1; ring
  have hdiff : Differentiable ℝ f := fun x => (hderiv x).differentiableAt
  have hmono : Monotone f := monotone_of_deriv_nonneg hdiff fun x => by
    rw [(hderiv x).deriv]; linarith [Real.add_one_le_exp (-x)]
  have h0 : f 0 = 0 := by simp [hf]
  have hle := hmono hz
  rw [h0] at hle
  simp only [hf] at hle
  linarith

/-! ### Gaussian approximation of `charFun^n`

The characteristic function of an `n`-fold sum (which is `(charFun μ)^n` for a convolution)
compared to the Gaussian `exp(-n v w²/2)`. This packages steps (i)–(iii) of the classical
Berry–Esseen argument at the level of characteristic functions, with no Fourier theory. -/

/-- **Gaussian approximation of the `n`-th power of a characteristic function.** For a
centered law with second moment `v ≥ 0` and finite third moment,
`‖(charFun μ w)ⁿ − exp(−n v w²/2)‖ ≤ n·(ρ|w|³/6 + (v w²/2)²/2)`. Telescoping
(`norm_prod_sub_prod_le`) reduces to the single-factor bound
`‖charFun μ w − exp(−v w²/2)‖`, itself split into the Taylor error
(`norm_charFun_sub_quadratic_le`) and `‖(1 − z) − e^{−z}‖ ≤ z²/2`. -/
theorem norm_charFun_pow_sub_gaussian_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ} (hv : 0 ≤ v) (hint1 : Integrable (fun x => x) μ)
    (hint2 : Integrable (fun x => x ^ 2) μ) (hint3 : Integrable (fun x => |x| ^ 3) μ)
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = v) (w : ℝ) (n : ℕ) :
    ‖(charFun μ w) ^ n - Complex.exp (-(n : ℂ) * v * w ^ 2 / 2)‖
      ≤ n * ((∫ x, |x| ^ 3 ∂μ) * |w| ^ 3 / 6 + (v * w ^ 2 / 2) ^ 2 / 2) := by
  set z : ℝ := v * w ^ 2 / 2 with hz_def
  have hznn : 0 ≤ z := by rw [hz_def]; positivity
  have hzc : (z : ℂ) = (v : ℂ) * (w : ℂ) ^ 2 / 2 := by rw [hz_def]; push_cast; ring
  -- Rewrite the Gaussian as `(exp(-z))ⁿ`.
  have hgauss : Complex.exp (-(n : ℂ) * v * w ^ 2 / 2) = (Complex.exp (-(z : ℂ))) ^ n := by
    rw [← Complex.exp_nat_mul]; congr 1; rw [hzc]; ring
  rw [hgauss]
  -- Both bases have norm ≤ 1.
  have hbase1 : ‖charFun μ w‖ ≤ 1 := norm_charFun_le_one w
  have hbase2 : ‖Complex.exp (-(z : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    have : (-(z : ℂ)).re = -z := by simp
    rw [this]; exact Real.exp_le_one_iff.mpr (by linarith)
  -- Telescoping product bound.
  have htel : ‖(charFun μ w) ^ n - (Complex.exp (-(z : ℂ))) ^ n‖
      ≤ (n : ℝ) * ‖charFun μ w - Complex.exp (-(z : ℂ))‖ := by
    have hp := norm_prod_sub_prod_le (Finset.range n) (fun _ => charFun μ w)
      (fun _ => Complex.exp (-(z : ℂ))) (fun i _ => hbase1) (fun i _ => hbase2)
    simpa [Finset.prod_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hp
  -- Single-factor bound.
  have hfac : ‖charFun μ w - Complex.exp (-(z : ℂ))‖
      ≤ (∫ x, |x| ^ 3 ∂μ) * |w| ^ 3 / 6 + z ^ 2 / 2 := by
    have h1 := norm_charFun_sub_quadratic_le μ hint1 hint2 hint3 hmean hvar w
    rw [← hzc] at h1
    -- `‖(1 - z) - exp(-z)‖ ≤ z²/2`.
    have hexpR : Complex.exp (-(z : ℂ)) = ((Real.exp (-z) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]; push_cast; ring_nf
    have h2 : ‖(1 - (z : ℂ)) - Complex.exp (-(z : ℂ))‖ ≤ z ^ 2 / 2 := by
      rw [hexpR]
      have hcast : (1 - (z : ℂ)) - ((Real.exp (-z) : ℝ) : ℂ)
          = ((1 - z - Real.exp (-z) : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_le]
      constructor
      · linarith [exp_neg_le_quadratic hznn]
      · linarith [Real.add_one_le_exp (-z), sq_nonneg z]
    calc ‖charFun μ w - Complex.exp (-(z : ℂ))‖
        = ‖(charFun μ w - (1 - (z : ℂ))) + ((1 - (z : ℂ)) - Complex.exp (-(z : ℂ)))‖ := by
          ring_nf
      _ ≤ ‖charFun μ w - (1 - (z : ℂ))‖ + ‖(1 - (z : ℂ)) - Complex.exp (-(z : ℂ))‖ :=
          norm_add_le _ _
      _ ≤ (∫ x, |x| ^ 3 ∂μ) * |w| ^ 3 / 6 + z ^ 2 / 2 := add_le_add h1 h2
  calc ‖(charFun μ w) ^ n - (Complex.exp (-(z : ℂ))) ^ n‖
      ≤ (n : ℝ) * ‖charFun μ w - Complex.exp (-(z : ℂ))‖ := htel
    _ ≤ (n : ℝ) * ((∫ x, |x| ^ 3 ∂μ) * |w| ^ 3 / 6 + z ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = n * ((∫ x, |x| ^ 3 ∂μ) * |w| ^ 3 / 6 + (v * w ^ 2 / 2) ^ 2 / 2) := by rw [hz_def]

/-! ### The damped Edgeworth expansion of `(charFun μ)ⁿ`

`norm_charFun_pow_sub_gaussian_le` compares `φⁿ` with the Gaussian characteristic function and
loses everything at order `n^{-1/2}`; its right-hand side also carries **no decay in the
argument**, so integrating it against the Esseen weight produces a constant rather than a rate.
Both defects are repaired here:

* the cubic term of `charFun` (`norm_charFun_sub_cubic_le`) is retained, giving the Edgeworth
  correction `1 + n c` with `c = −i m₃ s³/6`;
* the comparison is run at the second order of telescoping
  (`norm_pow_sub_pow_sub_lin_le`), whose bound keeps the damping factor `Mⁿ⁻²`, and `M` is
  taken to be the Gaussian majorant `e^{−v s²/4}` of `norm_charFun_le_exp_neg_sq`.

The result is `norm_charFun_pow_sub_edgeworth_le`, whose right-hand side is `e^{−(n−2)v s²/4}`
times a polynomial in `s`; in the standardized scaling `s = t/(σ√n)` this is
`e^{−t²/4}·O((t⁴ + t⁵ + t⁶)/n)`, which *is* integrable against the Esseen weight and gives the
`n⁻¹` rate. -/

/-- **The algebraic core of the damped expansion.** Purely a statement about complex numbers:
if `‖a‖ ≤ E`, `gc` is a nonnegative real in `[0, E]`, and `E ≤ 1`, then

`‖aⁿ − gcⁿ (1 + n c)‖ ≤ Eⁿ⁻² (n(n−1)/2 · D² + n (w + e₀))`

whenever `D` bounds `‖a − gc‖`, `e₀` bounds `‖a − gc − c‖` and `w` bounds `‖(1 − gc) c‖`.
The decomposition is `aⁿ − gcⁿ(1 + n c) = Δₙ + n gcⁿ⁻¹ ((1 − gc) c + (a − gc − c))` with
`Δₙ = aⁿ − gcⁿ − n gcⁿ⁻¹ (a − gc)`. -/
private lemma norm_pow_sub_edgeworth_le {a gc c : ℂ} {E D e₀ w gr : ℝ} (m : ℕ)
    (hgc : gc = (gr : ℂ)) (hgr0 : 0 ≤ gr) (hgrE : gr ≤ E) (haE : ‖a‖ ≤ E)
    (hE0 : 0 ≤ E) (hE1 : E ≤ 1)
    (hd : ‖a - gc‖ ≤ D) (he : ‖a - gc - c‖ ≤ e₀) (hcg : ‖(1 - gc) * c‖ ≤ w) :
    ‖a ^ (m + 2) - gc ^ (m + 2) * (1 + ((m : ℂ) + 2) * c)‖
      ≤ E ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1) / 2 * D ^ 2 + ((m : ℝ) + 2) * (w + e₀)) := by
  have hgcE : ‖gc‖ ≤ E := by
    rw [hgc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgr0]; exact hgrE
  have hnc : ‖((m : ℂ) + 2)‖ = (m : ℝ) + 2 := by
    have hc : ((m : ℂ) + 2) = (((m : ℝ) + 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hkey : a ^ (m + 2) - gc ^ (m + 2) * (1 + ((m : ℂ) + 2) * c)
      = (a ^ (m + 2) - gc ^ (m + 2) - ((m : ℂ) + 2) * gc ^ (m + 1) * (a - gc))
        + ((m : ℂ) + 2) * gc ^ (m + 1) * ((1 - gc) * c + (a - gc - c)) := by ring
  -- The quadratic telescoping remainder.
  have h1 : ‖a ^ (m + 2) - gc ^ (m + 2) - ((m : ℂ) + 2) * gc ^ (m + 1) * (a - gc)‖
      ≤ ((m : ℝ) + 2) * ((m : ℝ) + 1) / 2 * E ^ m * D ^ 2 := by
    refine (norm_pow_sub_pow_sub_lin_le haE hgcE m).trans ?_
    have hsq : ‖a - gc‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  -- The damped prefactor.
  have h2 : ‖((m : ℂ) + 2) * gc ^ (m + 1)‖ ≤ ((m : ℝ) + 2) * E ^ m := by
    rw [norm_mul, hnc, norm_pow]
    have hgm : ‖gc‖ ^ (m + 1) ≤ E ^ m :=
      (pow_le_pow_left₀ (norm_nonneg _) hgcE _).trans
        (pow_le_pow_of_le_one hE0 hE1 (Nat.le_succ m))
    exact mul_le_mul_of_nonneg_left hgm (by positivity)
  have h3 : ‖(1 - gc) * c + (a - gc - c)‖ ≤ w + e₀ :=
    (norm_add_le _ _).trans (add_le_add hcg he)
  calc ‖a ^ (m + 2) - gc ^ (m + 2) * (1 + ((m : ℂ) + 2) * c)‖
      = ‖(a ^ (m + 2) - gc ^ (m + 2) - ((m : ℂ) + 2) * gc ^ (m + 1) * (a - gc))
          + ((m : ℂ) + 2) * gc ^ (m + 1) * ((1 - gc) * c + (a - gc - c))‖ := by rw [hkey]
    _ ≤ ‖a ^ (m + 2) - gc ^ (m + 2) - ((m : ℂ) + 2) * gc ^ (m + 1) * (a - gc)‖
          + ‖((m : ℂ) + 2) * gc ^ (m + 1) * ((1 - gc) * c + (a - gc - c))‖ := norm_add_le _ _
    _ ≤ ((m : ℝ) + 2) * ((m : ℝ) + 1) / 2 * E ^ m * D ^ 2
          + ((m : ℝ) + 2) * E ^ m * (w + e₀) := by
        refine add_le_add h1 ?_
        rw [norm_mul]
        exact mul_le_mul h2 h3 (norm_nonneg _) (by positivity)
    _ = E ^ m * (((m : ℝ) + 2) * ((m : ℝ) + 1) / 2 * D ^ 2 + ((m : ℝ) + 2) * (w + e₀)) := by
        ring

/-- **Damped one-term Edgeworth expansion of `(charFun μ)ⁿ`.**

For a centred law with second moment `v`, third moment `m₃` and finite fourth moment, and for
`s` in the window `v s² ≤ 2`, `ρ|s| ≤ 3v/2` (`ρ = ∫|x|³`),

`‖φ(s)ⁿ − e^{−n v s²/2} (1 − n i m₃ s³/6)‖`
`  ≤ e^{−(n−2) v s²/4} · ( n(n−1)/2 · (ρ|s|³/6 + (v s²/2)²/2)²`
`      + n · ( (v s²/2)(|m₃||s|³/6) + (β|s|⁴/24 + (v s²/2)²/2) ) )`,

with `β = ∫ x⁴`, written with `n = m + 2`.

The Gaussian factor `e^{−n v s²/2}` times the *linear* correction `1 − n i m₃ s³/6` is exactly
the Edgeworth approximant: in the standardized scaling `s = t/(σ√n)`, `v = σ²`, the Gaussian
factor is `e^{−t²/2}` and the correction is `1 + (γ/6)(it)³ n^{−1/2}` with `γ = m₃/σ³` the
skewness.

**This is the estimate recorded as missing in `Bootstrap/Edgeworth.lean` (G2).** The two new
ingredients over `norm_charFun_pow_sub_gaussian_le` are `norm_charFun_sub_cubic_le`
(fourth-order Taylor expansion of `φ`, retaining the third cumulant) and
`norm_charFun_le_exp_neg_sq` (the quadratic majorant `|φ(s)| ≤ e^{−v s²/4}`), combined through
the damping-preserving telescoping bound `norm_pow_sub_pow_sub_lin_le`. -/
theorem norm_charFun_pow_sub_edgeworth_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v m₃ : ℝ} (hint1 : Integrable (fun x => x) μ)
    (hint2 : Integrable (fun x => x ^ 2) μ) (hint3 : Integrable (fun x => |x| ^ 3) μ)
    (hint4 : Integrable (fun x => x ^ 4) μ)
    (hmean : ∫ x, x ∂μ = 0) (hvar : ∫ x, x ^ 2 ∂μ = v) (hthird : ∫ x, x ^ 3 ∂μ = m₃)
    {s : ℝ} (hs2 : v * s ^ 2 ≤ 2) (hs3 : (∫ x, |x| ^ 3 ∂μ) * |s| ≤ 3 * v / 2) (m : ℕ) :
    ‖charFun μ s ^ (m + 2)
        - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ) ^ (m + 2)
            * (1 - ((m : ℂ) + 2) * I * (m₃ : ℂ) * (s : ℂ) ^ 3 / 6)‖
      ≤ Real.exp (-(v * s ^ 2 / 4)) ^ m *
          (((m : ℝ) + 2) * ((m : ℝ) + 1) / 2
              * ((∫ x, |x| ^ 3 ∂μ) * |s| ^ 3 / 6 + (v * s ^ 2 / 2) ^ 2 / 2) ^ 2
            + ((m : ℝ) + 2) * ((v * s ^ 2 / 2) * (|m₃| * |s| ^ 3 / 6)
              + ((∫ x, x ^ 4 ∂μ) * |s| ^ 4 / 24 + (v * s ^ 2 / 2) ^ 2 / 2))) := by
  have hvnn : 0 ≤ v := by rw [← hvar]; exact integral_nonneg fun x => sq_nonneg x
  have hznn : (0 : ℝ) ≤ v * s ^ 2 / 2 := by positivity
  have hint3' : Integrable (fun x : ℝ => x ^ 3) μ :=
    hint3.mono' (by fun_prop) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_pow])
  -- The gap between the quadratic polynomial and the Gaussian.
  have hgap : ‖(1 - (v : ℂ) * (s : ℂ) ^ 2 / 2)
      - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ)‖ ≤ (v * s ^ 2 / 2) ^ 2 / 2 := by
    have hc : (1 - (v : ℂ) * (s : ℂ) ^ 2 / 2) - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ)
        = ((1 - v * s ^ 2 / 2 - Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ) := by push_cast; ring
    rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_le]
    refine ⟨by linarith [exp_neg_le_quadratic hznn], ?_⟩
    linarith [Real.add_one_le_exp (-(v * s ^ 2 / 2)), sq_nonneg (v * s ^ 2 / 2)]
  -- (e) the single-factor Gaussian gap.
  have hd : ‖charFun μ s - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ)‖
      ≤ (∫ x, |x| ^ 3 ∂μ) * |s| ^ 3 / 6 + (v * s ^ 2 / 2) ^ 2 / 2 := by
    have hsp : charFun μ s - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ)
        = (charFun μ s - (1 - (v : ℂ) * (s : ℂ) ^ 2 / 2))
          + ((1 - (v : ℂ) * (s : ℂ) ^ 2 / 2) - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ)) := by
      ring
    rw [hsp]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_charFun_sub_quadratic_le μ hint1 hint2 hint3 hmean hvar s) hgap)
  -- (f) the cubic gap: what is left after subtracting the Edgeworth correction.
  have he : ‖charFun μ s - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ)
      - (-(I * (m₃ : ℂ) * (s : ℂ) ^ 3 / 6))‖
      ≤ (∫ x, x ^ 4 ∂μ) * |s| ^ 4 / 24 + (v * s ^ 2 / 2) ^ 2 / 2 := by
    have hsp : charFun μ s - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ)
          - (-(I * (m₃ : ℂ) * (s : ℂ) ^ 3 / 6))
        = (charFun μ s - (1 - (v : ℂ) * (s : ℂ) ^ 2 / 2 - I * (m₃ : ℂ) * (s : ℂ) ^ 3 / 6))
          + ((1 - (v : ℂ) * (s : ℂ) ^ 2 / 2) - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ)) := by
      ring
    rw [hsp]
    exact (norm_add_le _ _).trans
      (add_le_add
        (norm_charFun_sub_cubic_le μ hint1 hint2 hint3' hint4 hmean hvar hthird s) hgap)
  -- (g) the `(1 − g) c` term.
  have hexp1 : Real.exp (-(v * s ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hcg : ‖(1 - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ)) * (-(I * (m₃ : ℂ) * (s : ℂ) ^ 3 / 6))‖
      ≤ (v * s ^ 2 / 2) * (|m₃| * |s| ^ 3 / 6) := by
    have hA : ‖(1 - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ))‖ ≤ v * s ^ 2 / 2 := by
      have hc : (1 - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ))
          = ((1 - Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith [Real.add_one_le_exp (-(v * s ^ 2 / 2))]
    have hB : ‖(-(I * (m₃ : ℂ) * (s : ℂ) ^ 3 / 6))‖ = |m₃| * |s| ^ 3 / 6 := by
      have hc : (-(I * (m₃ : ℂ) * (s : ℂ) ^ 3 / 6)) = ((m₃ * s ^ 3 / 6 : ℝ) : ℂ) * (-I) := by
        push_cast; ring
      rw [hc, norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_div, abs_mul, abs_pow]
      norm_num
    rw [norm_mul, hB]
    exact mul_le_mul_of_nonneg_right hA (by positivity)
  -- Assemble via the algebraic core.
  have hgoal : charFun μ s ^ (m + 2)
        - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ) ^ (m + 2)
            * (1 - ((m : ℂ) + 2) * I * (m₃ : ℂ) * (s : ℂ) ^ 3 / 6)
      = charFun μ s ^ (m + 2)
        - ((Real.exp (-(v * s ^ 2 / 2)) : ℝ) : ℂ) ^ (m + 2)
            * (1 + ((m : ℂ) + 2) * (-(I * (m₃ : ℂ) * (s : ℂ) ^ 3 / 6))) := by ring
  rw [hgoal]
  exact norm_pow_sub_edgeworth_le m rfl (Real.exp_pos _).le
    (Real.exp_le_exp.2 (by linarith [sq_nonneg s, mul_nonneg hvnn (sq_nonneg s)]))
    (norm_charFun_le_exp_neg_sq μ hint1 hint2 hint3 hmean hvar hs2 hs3)
    (Real.exp_pos _).le (Real.exp_le_one_iff.2 (by linarith [mul_nonneg hvnn (sq_nonneg s)]))
    hd he hcg

/-- **Berry–Esseen rate for the characteristic function of a standardized i.i.d. sum.**
Combining `norm_charFun_pow_sub_gaussian_le` with Mathlib's factorization
`charFun_inv_sqrt_mul_sum`, the characteristic function of `(√n)⁻¹ ∑ₖ Xₖ` is within an
explicit `O(1/√n)` distance (the right-hand side, with `w = (√n)⁻¹ t`) of the Gaussian
characteristic function. This is the *entire* characteristic-function half of Berry–Esseen;
converting it into a bound on cumulative distribution functions is Esseen's smoothing
inequality (Target 1), which is blocked at this Mathlib pin — see the module docstring. -/
theorem norm_charFun_iidSum_sub_gaussian_le {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    {v : ℝ} (hv : 0 ≤ v)
    (hint1 : Integrable (fun x => x) (P.map (X 0)))
    (hint2 : Integrable (fun x => x ^ 2) (P.map (X 0)))
    (hint3 : Integrable (fun x => |x| ^ 3) (P.map (X 0)))
    (hmean : ∫ x, x ∂(P.map (X 0)) = 0) (hvar : ∫ x, x ^ 2 ∂(P.map (X 0)) = v)
    (t : ℝ) (n : ℕ) :
    ‖charFun (P.map (fun ω => (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω)) t
        - Complex.exp (-(n : ℂ) * v * (((√n)⁻¹ * t : ℝ) : ℂ) ^ 2 / 2)‖
      ≤ n * ((∫ x, |x| ^ 3 ∂(P.map (X 0))) * |(√n)⁻¹ * t| ^ 3 / 6
        + (v * ((√n)⁻¹ * t) ^ 2 / 2) ^ 2 / 2) := by
  haveI : IsProbabilityMeasure (P.map (X 0)) :=
    Measure.isProbabilityMeasure_map (hident 0).aemeasurable_fst
  rw [charFun_inv_sqrt_mul_sum hindep hident]
  exact norm_charFun_pow_sub_gaussian_le (P.map (X 0)) hv hint1 hint2 hint3 hmean hvar _ n

/-! ### Gaussian Fourier moments and the Hermite identity

The Edgeworth approximant is not a probability law but the signed measure with density
`y ↦ σ⁻¹φ(y/σ)(1 + (γ/6)(y³/σ³ − 3y/σ) n^{-1/2})`, and feeding it into a smoothing inequality
requires its Fourier transform. After the substitutions `y = σu`, `θ = σt` that reduces to the
three Gaussian moment transforms below, of which the third — the **Hermite identity**

`∫ e^{iθu} (u³ − 3u) e^{−u²/2} du = (iθ)³ √(2π) e^{−θ²/2}` —

is the one that matches the cubic Edgeworth correction `1 − n i m₃ s³/6` of
`norm_charFun_pow_sub_edgeworth_le`.

Rather than integrating by parts twice (which needs two improper boundary evaluations), each
identity is obtained from a **single explicit antiderivative**: for a quadratic `P`,

`d/du [P(u) e^{iθu − u²/2}] = (P'(u) + (iθ − u) P(u)) e^{iθu − u²/2}`,

so choosing `P` to make the bracket the desired polynomial minus a multiple of `1` turns the
identity into "the integral of a derivative of an integrable function with integrable derivative
vanishes" (`integral_eq_zero_of_hasDerivAt_of_integrable`). Concretely
`P(u) = −u − iθ` produces the `u²` identity and `P(u) = −u² − iθu + (θ² + 1)` the Hermite one.
The base value `∫ e^{iθu − u²/2} du = √(2π) e^{−θ²/2}` is Mathlib's `integral_cexp_quadratic`. -/

/-- The modulated Gaussian `u ↦ e^{iθu − u²/2}`. -/
private noncomputable def cexpGauss (θ u : ℝ) : ℂ :=
  Complex.exp ((θ : ℂ) * (u : ℂ) * I - (u : ℂ) ^ 2 / 2)

private lemma continuous_cexpGauss (θ : ℝ) : Continuous (cexpGauss θ) := by
  unfold cexpGauss; fun_prop

private lemma norm_cexpGauss (θ u : ℝ) : ‖cexpGauss θ u‖ = Real.exp (-(u ^ 2 / 2)) := by
  have h : ((θ : ℂ) * (u : ℂ) * I - (u : ℂ) ^ 2 / 2)
      = ((-(u ^ 2 / 2) : ℝ) : ℂ) + ((θ * u : ℝ) : ℂ) * I := by push_cast; ring
  rw [cexpGauss, h, Complex.norm_exp, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
    Complex.ofReal_im, neg_zero, add_zero]

private lemma hasDerivAt_cexpGauss (θ u : ℝ) :
    HasDerivAt (cexpGauss θ) (cexpGauss θ u * ((θ : ℂ) * I - (u : ℂ))) u := by
  have hbu : HasDerivAt (fun w : ℝ => (w : ℂ)) 1 u := by
    simpa using! Complex.ofRealCLM.hasDerivAt (x := u)
  have hg : HasDerivAt (fun w : ℝ => (θ : ℂ) * (w : ℂ) * I - (w : ℂ) ^ 2 / 2)
      ((θ : ℂ) * I - (u : ℂ)) u := by
    have h1 : HasDerivAt (fun w : ℝ => (θ : ℂ) * (w : ℂ) * I) ((θ : ℂ) * I) u := by
      simpa using (hbu.const_mul ((θ : ℂ))).mul_const I
    have h2 : HasDerivAt (fun w : ℝ => (w : ℂ) ^ 2 / 2) ((u : ℂ)) u := by
      have := (hbu.pow 2).div_const 2
      convert! this using 1
      ring
    exact h1.sub h2
  unfold cexpGauss
  exact hg.cexp

/-- `|u|^k ≤ (4^k k!) e^{u²/4}`, the crude majorant behind Gaussian integrability. -/
private lemma abs_pow_le_exp (k : ℕ) (u : ℝ) :
    |u| ^ k ≤ 4 ^ k * (Nat.factorial k : ℝ) * Real.exp (u ^ 2 / 4) := by
  have hfac : (1 : ℝ) ≤ (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
  have h4 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
  have hpos : (0 : ℝ) < 4 ^ k * (Nat.factorial k : ℝ) := by positivity
  have hC : (1 : ℝ) ≤ 4 ^ k * (Nat.factorial k : ℝ) := by nlinarith
  have hexp : (1 : ℝ) ≤ Real.exp (u ^ 2 / 4) := by
    linarith [Real.add_one_le_exp (u ^ 2 / 4), sq_nonneg u]
  rcases le_or_gt |u| 1 with h | h
  · calc |u| ^ k ≤ 1 ^ k := pow_le_pow_left₀ (abs_nonneg u) h k
      _ = 1 := one_pow k
      _ ≤ 4 ^ k * (Nat.factorial k : ℝ) * Real.exp (u ^ 2 / 4) := by nlinarith
  · have hkey : (u ^ 2 / 4) ^ k / (Nat.factorial k : ℝ) ≤ Real.exp (u ^ 2 / 4) :=
      Real.pow_div_factorial_le_exp (u ^ 2 / 4) (by positivity) k
    have hu2 : (u ^ 2 / 4) ^ k = |u| ^ (2 * k) / 4 ^ k := by
      rw [div_pow, ← sq_abs u, ← pow_mul]
    have hle : |u| ^ k ≤ |u| ^ (2 * k) := pow_le_pow_right₀ h.le (by omega)
    rw [hu2, div_div, div_le_iff₀ hpos] at hkey
    calc |u| ^ k ≤ |u| ^ (2 * k) := hle
      _ ≤ Real.exp (u ^ 2 / 4) * (4 ^ k * (Nat.factorial k : ℝ)) := hkey
      _ = 4 ^ k * (Nat.factorial k : ℝ) * Real.exp (u ^ 2 / 4) := by ring

private lemma integrable_abs_pow_mul_gauss (k : ℕ) :
    Integrable (fun u : ℝ => |u| ^ k * Real.exp (-(u ^ 2 / 2))) := by
  have hbase : Integrable (fun u : ℝ => Real.exp (-(1 / 4 : ℝ) * u ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num)
  refine Integrable.mono' (g := fun u : ℝ =>
      4 ^ k * (Nat.factorial k : ℝ) * Real.exp (-(1 / 4 : ℝ) * u ^ 2))
    (hbase.const_mul _) (by fun_prop) (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hmul := mul_le_mul_of_nonneg_right (abs_pow_le_exp k u)
    (Real.exp_pos (-(u ^ 2 / 2))).le
  refine hmul.trans_eq ?_
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

private lemma integrable_pow_mul_cexpGauss (θ : ℝ) (k : ℕ) :
    Integrable (fun u : ℝ => (u : ℂ) ^ k * cexpGauss θ u) := by
  have hcont : Continuous fun u : ℝ => (u : ℂ) ^ k * cexpGauss θ u :=
    (Complex.continuous_ofReal.pow k).mul (continuous_cexpGauss θ)
  refine Integrable.mono' (integrable_abs_pow_mul_gauss k) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, norm_cexpGauss]

private lemma integrable_cubic_cexpGauss (θ : ℝ) (α β γ δ : ℂ) :
    Integrable (fun u : ℝ =>
      (α * (u : ℂ) ^ 3 + β * (u : ℂ) ^ 2 + γ * (u : ℂ) + δ) * cexpGauss θ u) := by
  have i0 : Integrable (fun u : ℝ => δ * ((u : ℂ) ^ 0 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 0).const_mul δ
  have i1 : Integrable (fun u : ℝ => γ * ((u : ℂ) ^ 1 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 1).const_mul γ
  have i2 : Integrable (fun u : ℝ => β * ((u : ℂ) ^ 2 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 2).const_mul β
  have i3 : Integrable (fun u : ℝ => α * ((u : ℂ) ^ 3 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 3).const_mul α
  exact (i3.fun_add (i2.fun_add (i1.fun_add i0))).congr
    (Filter.Eventually.of_forall fun u => by ring)

private lemma integral_cubic_cexpGauss (θ : ℝ) (α β γ δ : ℂ) :
    (∫ u : ℝ, (α * (u : ℂ) ^ 3 + β * (u : ℂ) ^ 2 + γ * (u : ℂ) + δ) * cexpGauss θ u)
      = α * (∫ u : ℝ, (u : ℂ) ^ 3 * cexpGauss θ u) + β * (∫ u : ℝ, (u : ℂ) ^ 2 * cexpGauss θ u)
        + γ * (∫ u : ℝ, (u : ℂ) ^ 1 * cexpGauss θ u)
        + δ * (∫ u : ℝ, (u : ℂ) ^ 0 * cexpGauss θ u) := by
  have i0 : Integrable (fun u : ℝ => δ * ((u : ℂ) ^ 0 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 0).const_mul δ
  have i1 : Integrable (fun u : ℝ => γ * ((u : ℂ) ^ 1 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 1).const_mul γ
  have i2 : Integrable (fun u : ℝ => β * ((u : ℂ) ^ 2 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 2).const_mul β
  have i3 : Integrable (fun u : ℝ => α * ((u : ℂ) ^ 3 * cexpGauss θ u)) :=
    (integrable_pow_mul_cexpGauss θ 3).const_mul α
  have key : ∀ u : ℝ, (α * (u : ℂ) ^ 3 + β * (u : ℂ) ^ 2 + γ * (u : ℂ) + δ) * cexpGauss θ u
      = α * ((u : ℂ) ^ 3 * cexpGauss θ u) + (β * ((u : ℂ) ^ 2 * cexpGauss θ u)
        + (γ * ((u : ℂ) ^ 1 * cexpGauss θ u) + δ * ((u : ℂ) ^ 0 * cexpGauss θ u))) :=
    fun u => by ring
  have s3 : (∫ u : ℝ, (γ * ((u : ℂ) ^ 1 * cexpGauss θ u) + δ * ((u : ℂ) ^ 0 * cexpGauss θ u)))
      = (∫ u : ℝ, γ * ((u : ℂ) ^ 1 * cexpGauss θ u)) + ∫ u : ℝ, δ * ((u : ℂ) ^ 0 * cexpGauss θ u) :=
    integral_add i1 i0
  have s2 : (∫ u : ℝ, (β * ((u : ℂ) ^ 2 * cexpGauss θ u)
        + (γ * ((u : ℂ) ^ 1 * cexpGauss θ u) + δ * ((u : ℂ) ^ 0 * cexpGauss θ u))))
      = (∫ u : ℝ, β * ((u : ℂ) ^ 2 * cexpGauss θ u))
        + ∫ u : ℝ, (γ * ((u : ℂ) ^ 1 * cexpGauss θ u) + δ * ((u : ℂ) ^ 0 * cexpGauss θ u)) :=
    integral_add i2 (i1.fun_add i0)
  have s1 : (∫ u : ℝ, (α * ((u : ℂ) ^ 3 * cexpGauss θ u) + (β * ((u : ℂ) ^ 2 * cexpGauss θ u)
        + (γ * ((u : ℂ) ^ 1 * cexpGauss θ u) + δ * ((u : ℂ) ^ 0 * cexpGauss θ u)))))
      = (∫ u : ℝ, α * ((u : ℂ) ^ 3 * cexpGauss θ u))
        + ∫ u : ℝ, (β * ((u : ℂ) ^ 2 * cexpGauss θ u)
          + (γ * ((u : ℂ) ^ 1 * cexpGauss θ u) + δ * ((u : ℂ) ^ 0 * cexpGauss θ u))) :=
    integral_add i3 (i2.fun_add (i1.fun_add i0))
  have m3 : (∫ u : ℝ, α * ((u : ℂ) ^ 3 * cexpGauss θ u))
      = α * ∫ u : ℝ, (u : ℂ) ^ 3 * cexpGauss θ u :=
    MeasureTheory.integral_const_mul α _
  have m2 : (∫ u : ℝ, β * ((u : ℂ) ^ 2 * cexpGauss θ u))
      = β * ∫ u : ℝ, (u : ℂ) ^ 2 * cexpGauss θ u :=
    MeasureTheory.integral_const_mul β _
  have m1 : (∫ u : ℝ, γ * ((u : ℂ) ^ 1 * cexpGauss θ u))
      = γ * ∫ u : ℝ, (u : ℂ) ^ 1 * cexpGauss θ u :=
    MeasureTheory.integral_const_mul γ _
  have m0 : (∫ u : ℝ, δ * ((u : ℂ) ^ 0 * cexpGauss θ u))
      = δ * ∫ u : ℝ, (u : ℂ) ^ 0 * cexpGauss θ u :=
    MeasureTheory.integral_const_mul δ _
  rw [integral_congr_ae (Filter.Eventually.of_forall key), s1, s2, s3, m3, m2, m1, m0]
  ring

/-- The integral of the exact derivative `d/du[(a u² + b u + c) e^{iθu − u²/2}]` vanishes. -/
private lemma integral_poly_cexpGauss_deriv_eq_zero (θ : ℝ) (a b c : ℂ) :
    (∫ u : ℝ, ((2 * a * (u : ℂ) + b)
        + (a * (u : ℂ) ^ 2 + b * (u : ℂ) + c) * ((θ : ℂ) * I - (u : ℂ))) * cexpGauss θ u) = 0 := by
  have hderiv : ∀ u : ℝ,
      HasDerivAt (fun w : ℝ => (a * (w : ℂ) ^ 2 + b * (w : ℂ) + c) * cexpGauss θ w)
      (((2 * a * (u : ℂ) + b)
        + (a * (u : ℂ) ^ 2 + b * (u : ℂ) + c) * ((θ : ℂ) * I - (u : ℂ))) * cexpGauss θ u) u := by
    intro u
    have hbu : HasDerivAt (fun w : ℝ => (w : ℂ)) 1 u := by
      simpa using! Complex.ofRealCLM.hasDerivAt (x := u)
    have hp : HasDerivAt (fun w : ℝ => a * (w : ℂ) ^ 2 + b * (w : ℂ) + c)
        (2 * a * (u : ℂ) + b) u := by
      have h1 : HasDerivAt (fun w : ℝ => a * (w : ℂ) ^ 2) (a * (2 * (u : ℂ))) u := by
        have := (hbu.pow 2).const_mul a
        convert! this using 1
        ring
      have h2 : HasDerivAt (fun w : ℝ => b * (w : ℂ)) b u := by
        simpa using hbu.const_mul b
      have := (h1.add h2).add_const c
      convert! this using 1
      ring
    have := hp.mul (hasDerivAt_cexpGauss θ u)
    convert! this using 1
    ring
  have hInt : Integrable (fun w : ℝ => (a * (w : ℂ) ^ 2 + b * (w : ℂ) + c) * cexpGauss θ w) :=
    (integrable_cubic_cexpGauss θ 0 a b c).congr
      (Filter.Eventually.of_forall fun u => by ring)
  have hInt' : Integrable (fun u : ℝ => ((2 * a * (u : ℂ) + b)
      + (a * (u : ℂ) ^ 2 + b * (u : ℂ) + c) * ((θ : ℂ) * I - (u : ℂ))) * cexpGauss θ u) :=
    (integrable_cubic_cexpGauss θ (-a) (a * ((θ : ℂ) * I) - b)
      (2 * a + b * ((θ : ℂ) * I) - c) (b + c * ((θ : ℂ) * I))).congr
      (Filter.Eventually.of_forall fun u => by ring)
  exact integral_eq_zero_of_hasDerivAt_of_integrable hderiv hInt' hInt

/-- The linear relation between the first four Gaussian-transform moments produced by the
antiderivative `(a u² + b u + c) e^{iθu − u²/2}`. -/
private lemma poly_cexpGauss_relation (θ : ℝ) (a b c : ℂ) :
    (-a) * (∫ u : ℝ, (u : ℂ) ^ 3 * cexpGauss θ u)
        + (a * ((θ : ℂ) * I) - b) * (∫ u : ℝ, (u : ℂ) ^ 2 * cexpGauss θ u)
      + (2 * a + b * ((θ : ℂ) * I) - c) * (∫ u : ℝ, (u : ℂ) ^ 1 * cexpGauss θ u)
      + (b + c * ((θ : ℂ) * I)) * (∫ u : ℝ, (u : ℂ) ^ 0 * cexpGauss θ u) = 0 := by
  rw [← integral_cubic_cexpGauss θ (-a) (a * ((θ : ℂ) * I) - b) (2 * a + b * ((θ : ℂ) * I) - c)
      (b + c * ((θ : ℂ) * I)), ← integral_poly_cexpGauss_deriv_eq_zero θ a b c]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)

private lemma cexpGauss_eq (θ u : ℝ) :
    cexpGauss θ u = Complex.exp ((θ : ℂ) * (u : ℂ) * I) * Complex.exp (-(u : ℂ) ^ 2 / 2) := by
  rw [cexpGauss, ← Complex.exp_add]
  congr 1
  ring

private lemma integral_cexpGauss (θ : ℝ) :
    (∫ u : ℝ, (u : ℂ) ^ 0 * cexpGauss θ u)
      = ((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2) := by
  have hq := integral_cexp_quadratic (b := -(1 / 2 : ℂ)) (by norm_num) ((θ : ℂ) * I) 0
  have hlhs : (∫ x : ℝ, Complex.exp (-(1 / 2 : ℂ) * (x : ℂ) ^ 2 + (θ : ℂ) * I * (x : ℂ) + 0))
      = ∫ u : ℝ, (u : ℂ) ^ 0 * cexpGauss θ u := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [pow_zero, one_mul, cexpGauss]
    congr 1
    ring
  have hcpow : ((π : ℂ) / -(-(1 / 2 : ℂ))) ^ (1 / 2 : ℂ) = ((Real.sqrt (2 * π) : ℝ) : ℂ) := by
    have h2 : ((π : ℂ) / -(-(1 / 2 : ℂ))) = ((2 * π : ℝ) : ℂ) := by push_cast; ring
    rw [h2, Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity : (0 : ℝ) ≤ 2 * π)]
    norm_num
  have hexp : Complex.exp ((0 : ℂ) - ((θ : ℂ) * I) ^ 2 / (4 * -(1 / 2 : ℂ)))
      = Complex.exp (-(θ : ℂ) ^ 2 / 2) := by
    congr 1
    rw [mul_pow, Complex.I_sq]
    ring
  rw [← hlhs, hq, hcpow, hexp]

private lemma integral_pow1_cexpGauss (θ : ℝ) :
    (∫ u : ℝ, (u : ℂ) ^ 1 * cexpGauss θ u)
      = ((θ : ℂ) * I) * (((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2)) := by
  have h := poly_cexpGauss_relation θ 0 0 1
  rw [integral_cexpGauss θ] at h
  linear_combination -h

private lemma integral_pow2_cexpGauss (θ : ℝ) :
    (∫ u : ℝ, (u : ℂ) ^ 2 * cexpGauss θ u)
      = (1 - (θ : ℂ) ^ 2)
          * (((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2)) := by
  have h := poly_cexpGauss_relation θ 0 1 0
  rw [integral_cexpGauss θ, integral_pow1_cexpGauss θ] at h
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  linear_combination -h + ((θ : ℂ) ^ 2 * (((Real.sqrt (2 * π) : ℝ) : ℂ)
    * Complex.exp (-(θ : ℂ) ^ 2 / 2))) * hI

private lemma integral_pow3_cexpGauss (θ : ℝ) :
    (∫ u : ℝ, (u : ℂ) ^ 3 * cexpGauss θ u)
      = ((θ : ℂ) * I) * ((1 - (θ : ℂ) ^ 2)
          * (((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2)))
        + 2 * (((θ : ℂ) * I)
          * (((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2))) := by
  have h := poly_cexpGauss_relation θ 1 0 0
  rw [integral_pow1_cexpGauss θ, integral_pow2_cexpGauss θ] at h
  linear_combination -h

/-! ### The Gaussian Fourier moments -/

/-- `∫ e^{iθu} e^{−u²/2} du = √(2π) e^{−θ²/2}`. -/
theorem integral_cexp_mul_gaussian (θ : ℝ) :
    (∫ u : ℝ, Complex.exp ((θ : ℂ) * (u : ℂ) * I) * Complex.exp (-(u : ℂ) ^ 2 / 2))
      = ((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2) := by
  rw [← integral_cexpGauss θ]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun u => by simp only [cexpGauss_eq, pow_zero, one_mul])

/-- `∫ u² e^{iθu} e^{−u²/2} du = (1 − θ²) √(2π) e^{−θ²/2}`. -/
theorem integral_sq_mul_cexp_mul_gaussian (θ : ℝ) :
    (∫ u : ℝ, (u : ℂ) ^ 2
        * (Complex.exp ((θ : ℂ) * (u : ℂ) * I) * Complex.exp (-(u : ℂ) ^ 2 / 2)))
      = (1 - (θ : ℂ) ^ 2) * (((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2)) := by
  rw [← integral_pow2_cexpGauss θ]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => by simp only [cexpGauss_eq])

/-- **The first Hermite Fourier identity.** `∫ u e^{iθu} e^{−u²/2} du = (iθ) √(2π) e^{−θ²/2}`.

The `He₁` companion of `integral_hermite3_mul_cexp_mul_gaussian`. A one-term Edgeworth
correction whose Hermite content is not `He₃` alone — the *studentized* correction
`3t − 2t³ = −2He₃(t) − 3He₁(t)` is the case in point — needs this moment as well as the cubic
one. -/
theorem integral_linear_mul_cexp_mul_gaussian (θ : ℝ) :
    (∫ u : ℝ, (u : ℂ)
        * (Complex.exp ((θ : ℂ) * (u : ℂ) * I) * Complex.exp (-(u : ℂ) ^ 2 / 2)))
      = ((θ : ℂ) * I)
          * (((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2)) := by
  rw [← integral_pow1_cexpGauss θ]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun u => by simp only [cexpGauss_eq, pow_one])

/-- **A monomial is dominated by a Gaussian of half the rate.** `|u|ᵏ ≤ 4ᵏ k! e^{u²/4}`, with
an explicit constant. This is the elementary envelope behind every Gaussian moment bound used
by the Edgeworth assembly: multiplied by `e^{−u²/2}` it gives `|u|ᵏ e^{−u²/2} ≤ 4ᵏ k!`, a
*uniform* bound on the polynomial-times-Gaussian densities. -/
theorem abs_pow_le_const_mul_exp_sq_div_four (k : ℕ) (u : ℝ) :
    |u| ^ k ≤ 4 ^ k * (Nat.factorial k : ℝ) * Real.exp (u ^ 2 / 4) :=
  abs_pow_le_exp k u

/-- **Polynomial multiples of the Gaussian kernel are integrable.** -/
theorem integrable_abs_pow_mul_exp_neg_half_sq (k : ℕ) :
    Integrable (fun u : ℝ => |u| ^ k * Real.exp (-(u ^ 2 / 2))) :=
  integrable_abs_pow_mul_gauss k

/-- **Cubic multiples of the modulated Gaussian are integrable.** The companion of
`integral_cexp_mul_gaussian` and `integral_hermite3_mul_cexp_mul_gaussian`: it is what lets an
Edgeworth density be integrated against `e^{iθu}` term by term. -/
theorem integrable_cubic_mul_cexp_mul_gaussian (θ : ℝ) (a b c d : ℂ) :
    Integrable (fun u : ℝ => (a * (u : ℂ) ^ 3 + b * (u : ℂ) ^ 2 + c * (u : ℂ) + d)
      * (Complex.exp ((θ : ℂ) * (u : ℂ) * I) * Complex.exp (-(u : ℂ) ^ 2 / 2))) := by
  refine (integrable_cubic_cexpGauss θ a b c d).congr
    (Filter.Eventually.of_forall fun u => ?_)
  simp only [cexpGauss_eq]

/-- **The Hermite Fourier identity.**
`∫ e^{iθu} (u³ − 3u) e^{−u²/2} du = (iθ)³ √(2π) e^{−θ²/2}`. -/
theorem integral_hermite3_mul_cexp_mul_gaussian (θ : ℝ) :
    (∫ u : ℝ, ((u : ℂ) ^ 3 - 3 * (u : ℂ))
        * (Complex.exp ((θ : ℂ) * (u : ℂ) * I) * Complex.exp (-(u : ℂ) ^ 2 / 2)))
      = ((θ : ℂ) * I) ^ 3
          * (((Real.sqrt (2 * π) : ℝ) : ℂ) * Complex.exp (-(θ : ℂ) ^ 2 / 2)) := by
  have hsplit : (∫ u : ℝ, ((u : ℂ) ^ 3 - 3 * (u : ℂ)) * cexpGauss θ u)
      = (∫ u : ℝ, (u : ℂ) ^ 3 * cexpGauss θ u) - 3 * ∫ u : ℝ, (u : ℂ) ^ 1 * cexpGauss θ u := by
    have := integral_cubic_cexpGauss θ 1 0 (-3) 0
    rw [show (∫ u : ℝ,
          ((1 : ℂ) * (u : ℂ) ^ 3 + 0 * (u : ℂ) ^ 2 + (-3) * (u : ℂ) + 0) * cexpGauss θ u)
        = ∫ u : ℝ, ((u : ℂ) ^ 3 - 3 * (u : ℂ)) * cexpGauss θ u from
      integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)] at this
    rw [this]
    ring
  have hgoal : (∫ u : ℝ, ((u : ℂ) ^ 3 - 3 * (u : ℂ))
      * (Complex.exp ((θ : ℂ) * (u : ℂ) * I) * Complex.exp (-(u : ℂ) ^ 2 / 2)))
      = ∫ u : ℝ, ((u : ℂ) ^ 3 - 3 * (u : ℂ)) * cexpGauss θ u :=
    integral_congr_ae (Filter.Eventually.of_forall fun u => by simp only [cexpGauss_eq])
  rw [hgoal, hsplit, integral_pow3_cexpGauss θ, integral_pow1_cexpGauss θ]
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  linear_combination (-(θ : ℂ) ^ 3 * I * (((Real.sqrt (2 * π) : ℝ) : ℂ)
    * Complex.exp (-(θ : ℂ) ^ 2 / 2))) * hI

/-! ### The Fejér kernel — partial foundation for Esseen's smoothing inequality

Target 1 (Esseen's smoothing inequality) is proved classically by convolving `F − G` with
the **Fejér kernel** `K_T`, whose Fourier transform is the triangle function supported in
`[−T, T]` — the compact support is what truncates the inversion integral. Three ingredients
are needed:

1. the normalization `∫ K_T = 1`, which reduces to the sinc integral
   `∫ (sin x / x)² dx = π`;
2. the Fejér kernel and its Fourier transform (the triangle function);
3. a Lévy/Esseen inversion formula relating `∫_{−T}^{T} (F̂ − Ĝ)/t dt` to the *smoothed*
   distribution-function difference `(F − G) ∗ K_T`.

Items 1 and 2 were originally recorded here as absent from Mathlib v4.29.1 and hence as hard
obstructions. They are **no longer obstructions**: both are proved in
`StatLean.HypothesisTesting.ForMathlib.EsseenSmoothing` (`integral_sin_div_sq`,
`integral_fejerKernel`, `fourier_tentC`, `fourier_sqSincC`), by Fourier inversion applied to
the triangle function rather than by contour integration. Item 3 — the CDF-level (Stieltjes)
inversion formula — is the one that remains. This section keeps only the Fejér-kernel
definition and the facts that need no Fourier theory (nonnegativity, evenness); the
normalisation now lives with the sinc integral it depends on. -/

/-- The **Fejér kernel** `K_T(x) = (T / 2π) · (sin(Tx/2) / (Tx/2))²`. Its total integral is
`1` and its Fourier transform is the triangle function on `[−T, T]`; both facts rest on the
sinc integral, which is proved in `ForMathlib.EsseenSmoothing` (see `integral_fejerKernel`
there for the normalisation). -/
noncomputable def fejerKernel (T x : ℝ) : ℝ :=
  (T / (2 * π)) * (Real.sin (T * x / 2) / (T * x / 2)) ^ 2

/-- The Fejér kernel is nonnegative for `T ≥ 0`. -/
lemma fejerKernel_nonneg {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : 0 ≤ fejerKernel T x :=
  mul_nonneg (div_nonneg hT (by positivity)) (sq_nonneg _)

/-- The Fejér kernel is even. -/
lemma fejerKernel_even (T x : ℝ) : fejerKernel T (-x) = fejerKernel T x := by
  unfold fejerKernel
  rw [show T * (-x) / 2 = -(T * x / 2) by ring, Real.sin_neg, neg_div_neg_eq]

end StatLean.HypothesisTesting
