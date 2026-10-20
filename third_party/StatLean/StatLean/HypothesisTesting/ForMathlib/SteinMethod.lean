module
public import StatLean.HypothesisTesting.ForMathlib.EsseenSmoothing
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.CDF
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

/-!
# Stein's method for exchangeable pairs on a finite space

Stein's method replaces the characteristic function by a differential characterisation of the
standard normal law: a real random variable `Z` is `N(0,1)` if and only if
`𝔼[f'(Z) − Z f(Z)] = 0` for every bounded smooth `f`. Given a test function `h`, the **Stein
equation**
$$ f'(w) - w\,f(w) \;=\; h(w) - \mathbb E\,h(Z) $$
has the explicit solution
$$ f_h(w) \;=\; e^{w^2/2}\int_{-\infty}^{w} \bigl(h(x) - \mathbb E\,h(Z)\bigr)\,e^{-x^2/2}\,dx ,$$
so that bounding `|𝔼 h(W) − 𝔼 h(Z)|` for *some* random variable `W` becomes the problem of
bounding `𝔼[f_h'(W) − W f_h(W)]`, which needs no independence at all — only a way of
integrating `W f(W)` by parts. The **exchangeable-pair** device supplies that: if `(W, W')` is
an exchangeable pair with the linearity condition `𝔼[W' − W \mid W] = -\lambda W`, then for
every antisymmetric `F` one has `𝔼 F(W, W') = 0`, and choosing
`F(w, w') = (w' - w)\,(f(w') + f(w))` gives the exact identity
$$ 2\lambda\,\mathbb E\,[W f(W)] \;=\; \mathbb E\bigl[(W' - W)(f(W') - f(W))\bigr] . $$
A first-order Taylor expansion of `f(W') - f(W)` then produces the classical three-term bound.

## Main results

* `steinSolution` — the explicit solution of the Stein equation for the standard normal law,
  and `hasDerivAt_steinSolution` / `steinSolution_sub_mul` — the fact that it *is* a solution.
* `abs_steinSolution_le`, `abs_deriv_steinSolution_le`, `lipschitz_deriv_steinSolution` —
  the classical bounds on the solution and its derivative for a Lipschitz test function `h`
  (`‖f_h‖ ≤ L`, `‖f_h'‖ ≤ 2L` and `f_h'` `5L`-Lipschitz), together with the sharper
  `abs_deriv_steinSolution_mul_one_add_sq_le`, `|f_h'(w)|(1 + w²) ≤ L(2|w| + 1)`, which is
  the form the third bound consumes.
* `mul_div_le_integral_Ioi_exp_neg_sq_half` — **Mills' lower bound** for the unnormalised
  Gaussian tail, and the exact one-sided moments `integral_Ioi_id_mul_exp_neg_sq_half`,
  `integral_Iic_id_mul_exp_neg_sq_half`, `integral_abs_mul_exp_neg_sq_half`,
  `integral_exp_neg_sq_half`; these are the only analytic inputs to the three bounds.
* `integral_centred_mul_exp_neg_sq_half` — the centring identity
  `∫ (h − 𝔼h(Z))e^{-x²/2} = 0`, which is what makes the *tail* representation of `f_h`
  available, and `abs_sub_stdGaussianExpect_le` — `|h(w) − 𝔼h(Z)| ≤ L(|w| + 1)`.
* `sum_eq_zero_of_exchangeable` — the antisymmetry identity for an exchangeable pair.
* `sum_stein_pair` — the exact integration-by-parts identity
  `2λ|K| ∑_ω W(ω) f(W(ω)) = ∑_ω ∑_k (W'(ω,k) − W(ω))(f(W'(ω,k)) − f(W(ω)))`.
* `abs_sub_sub_mul_deriv_le` — Taylor's theorem with a Lipschitz derivative, sharp constant.
* `abs_avg_sub_le` — **the abstract exchangeable-pair theorem**: the three-term bound on
  `|𝔼 h(W) − 𝔼 h(Z)|` in terms of the conditional-variance defect and the third absolute
  moment of the increment.
* `lipschitzWith_cdf_gaussianReal` — the standard normal c.d.f. is 1-Lipschitz (Mathlib has
  no continuity lemma for `cdf`), and `abs_ramp_sub_ramp_le` — the ramp of
  `ForMathlib/EsseenSmoothing` is `δ⁻¹`-Lipschitz.
* `tendsto_of_squeeze_continuousAt` — the de-smoothing step: a quantity squeezed between the
  values of a *continuous* limit c.d.f. at `t ± ε`, up to `o(1)`, converges to it at `t`.

## Design notes

* *Everything is a finite sum.* The exchangeable pair is carried by a **finite** index type
  `Ω` (the configuration) together with a **finite** auxiliary randomisation `K` (which of the
  possible swaps is performed): `W : Ω → ℝ` and `W' : Ω → K → ℝ`. Conditioning on the
  configuration is then literally averaging over `K`, so no conditional-expectation machinery
  is needed and the "conditional variance" `V ω = |K|⁻¹ ∑ₖ (W' ω k − W ω)²` is a *definition*
  rather than a hypothesis. This is exactly the shape in which the combinatorial CLT arrives
  (`ForMathlib/CombinatorialCLT`): `Ω = Equiv.Perm (Fin N)` and `K` indexes the pairs
  (sampled position, unsampled position).
* *Unnormalised Gaussian kernel.* The solution is written with `e^{-x²/2}` and not with the
  density `φ(x) = (2π)^{-1/2}e^{-x²/2}`; the two differ by the factor `√(2π)` that the
  classical normalisation of `f_h` carries anyway, so the classical constants
  (`‖f_h‖ ≤ ‖h'‖`, `‖f_h'‖ ≤ √(2/π)‖h'‖`, `f_h'` is `2‖h'‖`-Lipschitz) apply verbatim.
* *Provable constants.* Where a constant below differs from the textbook one the deviation is
  documented at the statement. The limit theorems downstream are insensitive to constants.
  Two deviations occur: `‖f_h'‖ ≤ 2L` instead of the sharp `√(2/π)L`, and `f_h'` is proved
  `5L`-Lipschitz instead of `2L`-Lipschitz. Both are consequences of working with a merely
  Lipschitz `h` (so `f_h''` need not exist) and of the crude — but elementary — Mills bound
  `∫_w^∞ e^{-x²/2}dx ≥ w(1 + w²)^{-1}e^{-w²/2}`.

**Reference.** C. Stein, *Approximate Computation of Expectations*, IMS Lecture Notes 7, 1986,
Chapter III; L.H.Y. Chen, L. Goldstein and Q.-M. Shao, *Normal Approximation by Stein's
Method*, Springer, 2011, Lemma 2.4 (bounds on the solution) and Theorem 4.9 (the
exchangeable-pair bound). See also E.L. Lehmann and J.P. Romano, *Testing Statistical
Hypotheses*, 4th ed., 2022, §12.2 for the application to sampling without replacement.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

/-! ### The Stein equation and its solution -/

/-- The expectation of a test function under the standard normal law. -/
noncomputable def stdGaussianExpect (h : ℝ → ℝ) : ℝ := ∫ x, h x ∂(gaussianReal 0 1)

/-- The **solution of the Stein equation** for the standard normal law and the test function
`h`:
$$ f_h(w) = e^{w^2/2}\int_{-\infty}^w \bigl(h(x) - \mathbb E h(Z)\bigr) e^{-x^2/2}\,dx . $$
The unnormalised kernel `e^{-x²/2}` (rather than the density) is deliberate: it absorbs the
`√(2π)` that the classical normalisation of `f_h` carries, so that `f_h' - w f_h = h - 𝔼h(Z)`
on the nose. -/
noncomputable def steinSolution (h : ℝ → ℝ) (w : ℝ) : ℝ :=
  Real.exp (w ^ 2 / 2) * ∫ x in Iic w, (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2)

/-- The Gaussian kernel `e^{-x²/2}` is integrable on the line. -/
theorem integrable_exp_neg_sq_half :
    Integrable (fun x : ℝ => Real.exp (-x ^ 2 / 2)) := by
  have h := integrable_exp_neg_mul_sq (b := (1 : ℝ) / 2) (by norm_num)
  refine h.congr ?_
  filter_upwards with x
  congr 1
  ring

/-- A bounded measurable function times the Gaussian kernel is integrable. -/
theorem integrable_mul_exp_neg_sq_half {g : ℝ → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) :
    Integrable (fun x : ℝ => g x * Real.exp (-x ^ 2 / 2)) := by
  refine (integrable_exp_neg_sq_half.const_mul C).mono'
    (hg.aestronglyMeasurable.mul (by fun_prop)) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hC x) (Real.exp_pos _).le

/-- The centred test function times the Gaussian kernel is integrable. -/
theorem integrable_centred_mul_exp_neg_sq_half {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) :
    Integrable fun x : ℝ => (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2) := by
  refine integrable_mul_exp_neg_sq_half (hh.sub continuous_const)
    (C := C + |stdGaussianExpect h|) fun x => ?_
  have a1 := le_abs_self (h x)
  have a2 := neg_abs_le (h x)
  have b1 := le_abs_self (stdGaussianExpect h)
  have b2 := neg_abs_le (stdGaussianExpect h)
  have a3 := hC x
  rw [abs_le]
  constructor <;> linarith

/-- **The tail integral of the centred test function differentiates by the fundamental theorem
of calculus**: `G(w) = ∫_{-∞}^w (h − 𝔼h(Z))e^{-x²/2}` has derivative
`(h(w) − 𝔼h(Z))e^{-w²/2}`. -/
theorem hasDerivAt_gaussTail {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) (w : ℝ) :
    HasDerivAt
      (fun u : ℝ => ∫ x in Iic u, (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2))
      ((h w - stdGaussianExpect h) * Real.exp (-w ^ 2 / 2)) w := by
  have hFc : Continuous fun x : ℝ => (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2) :=
    (hh.sub continuous_const).mul (by fun_prop)
  have hFint := integrable_centred_mul_exp_neg_sq_half hh hC
  have hIic : ∀ u : ℝ,
      (∫ x in Iic u, (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2))
        = (∫ x in Iic (0 : ℝ), (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2))
          + ∫ x in (0 : ℝ)..u, (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2) := by
    intro u
    have hsub := intervalIntegral.integral_Iic_sub_Iic (a := (0 : ℝ)) (b := u)
      hFint.integrableOn hFint.integrableOn
    linarith
  have hkey : HasDerivAt
      (fun u : ℝ => ∫ x in (0 : ℝ)..u, (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2))
      ((h w - stdGaussianExpect h) * Real.exp (-w ^ 2 / 2)) w :=
    intervalIntegral.integral_hasDerivAt_right hFint.intervalIntegrable
      (hFc.stronglyMeasurableAtFilter _ _) hFc.continuousAt
  refine (hkey.const_add
    (∫ x in Iic (0 : ℝ),
      (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2))).congr_of_eventuallyEq ?_
  filter_upwards with u using hIic u

/-- **The Stein solution is differentiable, with the derivative dictated by the Stein
equation.** Writing `f = e^{w²/2} G` with `G(w) = ∫_{-∞}^w g e^{-x²/2}` and `g = h - 𝔼h(Z)`,
the fundamental theorem of calculus gives `G' (w) = g(w) e^{-w²/2}`, and the product rule
cancels the two exponentials. -/
theorem hasDerivAt_steinSolution {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) (w : ℝ) :
    HasDerivAt (steinSolution h)
      (w * steinSolution h w + (h w - stdGaussianExpect h)) w := by
  have hderiv0 := hasDerivAt_gaussTail hh hC w
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (u ^ 2 / 2)) (w * Real.exp (w ^ 2 / 2)) w := by
    have hq : HasDerivAt (fun u : ℝ => u ^ 2 / 2) w w := by
      have h0 := (hasDerivAt_pow 2 w).div_const 2
      convert! h0 using 1
      push_cast
      ring
    have he := hq.exp
    rw [mul_comm] at he
    exact he
  have hmul := hexp.mul hderiv0
  have hee : Real.exp (w ^ 2 / 2) * Real.exp (-w ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]
    rw [show w ^ 2 / 2 + -w ^ 2 / 2 = 0 by ring, Real.exp_zero]
  have hfun : steinSolution h = fun u : ℝ => Real.exp (u ^ 2 / 2) *
      ∫ x in Iic u, (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2) := rfl
  rw [hfun]
  convert! hmul using 1
  linear_combination (stdGaussianExpect h - h w) * hee

/-- **The Stein equation.** The derivative of the Stein solution minus `w` times the solution
recovers the centred test function. -/
theorem steinSolution_sub_mul {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) (w : ℝ) :
    deriv (steinSolution h) w - w * steinSolution h w = h w - stdGaussianExpect h := by
  rw [(hasDerivAt_steinSolution hh hC w).deriv]; ring

/-! ### The Gaussian kernel: mass, tail moments and Mills' bound

Everything the three bounds of the next section need about the unnormalised kernel
`e^{-x²/2}` is collected here: its total mass `√(2π)`, the exact one-sided first moments
`∫_w^∞ x e^{-x²/2}dx = e^{-w²/2}` and `∫_{-∞}^w x e^{-x²/2}dx = -e^{-w²/2}`, the first
absolute moment `∫_ℝ |x| e^{-x²/2}dx = 2`, and **Mills' lower bound**
`∫_w^∞ e^{-x²/2}dx ≥ w(1+w²)^{-1} e^{-w²/2}` for `w > 0`. Each is a single application of
the fundamental theorem of calculus on a half-line: the first three use the antiderivative
`-e^{-x²/2}` of `x e^{-x²/2}`, and Mills' bound the antiderivative `-x^{-1}e^{-x²/2}` of
`(1 + x^{-2})e^{-x²/2}` together with the crude comparison `x^{-2} ≤ w^{-2}` on `(w, ∞)`. -/

/-- The Gaussian kernel differentiates to `-x e^{-x²/2}`. -/
theorem hasDerivAt_exp_neg_sq_half (x : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-u ^ 2 / 2)) (-x * Real.exp (-x ^ 2 / 2)) x := by
  have hq : HasDerivAt (fun u : ℝ => -u ^ 2 / 2) (-x) x := by
    have h0 := ((hasDerivAt_pow 2 x).neg).div_const 2
    convert! h0 using 1
    push_cast
    ring
  have h1 := hq.exp
  convert h1 using 1
  ring

/-- The Gaussian kernel vanishes at `+∞`. -/
theorem tendsto_exp_neg_sq_half_atTop :
    Tendsto (fun u : ℝ => Real.exp (-u ^ 2 / 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun u : ℝ => u ^ 2 / 2) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun u : ℝ => (Real.exp (u ^ 2 / 2))⁻¹) atTop (𝓝 0) :=
    (Real.tendsto_exp_atTop.comp h1).inv_tendsto_atTop
  refine h2.congr fun u => ?_
  rw [← Real.exp_neg, neg_div]

/-- The Gaussian kernel vanishes at `-∞`. -/
theorem tendsto_exp_neg_sq_half_atBot :
    Tendsto (fun u : ℝ => Real.exp (-u ^ 2 / 2)) atBot (𝓝 0) := by
  have h1 := tendsto_exp_neg_sq_half_atTop.comp tendsto_neg_atBot_atTop
  refine h1.congr fun u => ?_
  simp

/-- `x e^{-x²/2}` is integrable on the line. -/
theorem integrable_id_mul_exp_neg_sq_half :
    Integrable (fun x : ℝ => x * Real.exp (-x ^ 2 / 2)) := by
  have h := integrable_mul_exp_neg_mul_sq (b := (1 : ℝ) / 2) (by norm_num)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  have hx : -(1 / 2 : ℝ) * x ^ 2 = -x ^ 2 / 2 := by ring
  simp only [hx]

/-- The total mass of the unnormalised Gaussian kernel. -/
theorem integral_exp_neg_sq_half :
    ∫ x : ℝ, Real.exp (-x ^ 2 / 2) = Real.sqrt (2 * Real.pi) := by
  have h := integral_gaussian (1 / 2 : ℝ)
  rw [show Real.pi / (1 / 2 : ℝ) = 2 * Real.pi by ring] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hx : -x ^ 2 / 2 = -(1 / 2 : ℝ) * x ^ 2 := by ring
  simp only [hx]

/-- **The one-sided first moment on a right half-line.** -/
theorem integral_Ioi_id_mul_exp_neg_sq_half (w : ℝ) :
    ∫ x in Ioi w, x * Real.exp (-x ^ 2 / 2) = Real.exp (-w ^ 2 / 2) := by
  have hlim : Tendsto (fun u : ℝ => -Real.exp (-u ^ 2 / 2)) atTop (𝓝 0) := by
    simpa using tendsto_exp_neg_sq_half_atTop.neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun u : ℝ => -Real.exp (-u ^ 2 / 2))
    (f' := fun u : ℝ => u * Real.exp (-u ^ 2 / 2)) (a := w)
    (fun x _ => by simpa using! (hasDerivAt_exp_neg_sq_half x).neg)
    integrable_id_mul_exp_neg_sq_half.integrableOn hlim
  simpa using h

/-- **The one-sided first moment on a left half-line.** -/
theorem integral_Iic_id_mul_exp_neg_sq_half (w : ℝ) :
    ∫ x in Iic w, x * Real.exp (-x ^ 2 / 2) = -Real.exp (-w ^ 2 / 2) := by
  have hlim : Tendsto (fun u : ℝ => -Real.exp (-u ^ 2 / 2)) atBot (𝓝 0) := by
    simpa using tendsto_exp_neg_sq_half_atBot.neg
  have h := integral_Iic_of_hasDerivAt_of_tendsto'
    (f := fun u : ℝ => -Real.exp (-u ^ 2 / 2))
    (f' := fun u : ℝ => u * Real.exp (-u ^ 2 / 2)) (a := w)
    (fun x _ => by simpa using! (hasDerivAt_exp_neg_sq_half x).neg)
    integrable_id_mul_exp_neg_sq_half.integrableOn hlim
  simpa using h

/-- The first absolute moment of the Gaussian kernel. -/
theorem integral_abs_mul_exp_neg_sq_half : ∫ x : ℝ, |x| * Real.exp (-x ^ 2 / 2) = 2 := by
  have h := integral_comp_abs (f := fun y : ℝ => y * Real.exp (-y ^ 2 / 2))
  simp only [sq_abs] at h
  rw [h, integral_Ioi_id_mul_exp_neg_sq_half]
  norm_num

/-- The Gaussian tail is invariant under reflection. -/
theorem integral_Iic_exp_neg_sq_half (w : ℝ) :
    ∫ x in Iic w, Real.exp (-x ^ 2 / 2) = ∫ x in Ioi (-w), Real.exp (-x ^ 2 / 2) := by
  have h := integral_comp_neg_Iic (c := w) (f := fun y : ℝ => Real.exp (-y ^ 2 / 2))
  simpa using h

/-- `-x^{-1}e^{-x²/2}` is an antiderivative of `(1 + x^{-2})e^{-x²/2}` away from the origin. -/
private lemma hasDerivAt_mills {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun u : ℝ => -(Real.exp (-u ^ 2 / 2) / u))
      (Real.exp (-x ^ 2 / 2) * (1 + (x ^ 2)⁻¹)) x := by
  have hd := ((hasDerivAt_exp_neg_sq_half x).div (hasDerivAt_id' x) hx).neg
  convert! hd using 1
  field_simp
  ring

/-- The Mills integrand is integrable away from the origin. -/
private lemma integrableOn_mills {w : ℝ} (hw : 0 < w) :
    IntegrableOn (fun x : ℝ => Real.exp (-x ^ 2 / 2) * (1 + (x ^ 2)⁻¹)) (Ioi w) := by
  have hmaj : Integrable (fun x : ℝ => (1 + (w ^ 2)⁻¹) * Real.exp (-x ^ 2 / 2)) :=
    integrable_exp_neg_sq_half.const_mul _
  refine Integrable.mono' hmaj.integrableOn
    ((by fun_prop : Measurable fun x : ℝ =>
      Real.exp (-x ^ 2 / 2) * (1 + (x ^ 2)⁻¹)).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => ?_)
  have hxw : w < x := hx
  have hx0 : 0 < x := hw.trans hxw
  have hsq : w ^ 2 ≤ x ^ 2 := by nlinarith
  have hinv : (x ^ 2)⁻¹ ≤ (w ^ 2)⁻¹ := by gcongr
  have hE := (Real.exp_pos (-x ^ 2 / 2)).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hinv hE]

/-- **Mills' lower bound** for the unnormalised Gaussian tail: for `w > 0`,
`∫_w^∞ e^{-x²/2}dx ≥ w(1+w²)^{-1}e^{-w²/2}`. -/
theorem mul_div_le_integral_Ioi_exp_neg_sq_half {w : ℝ} (hw : 0 < w) :
    Real.exp (-w ^ 2 / 2) * (w / (1 + w ^ 2)) ≤ ∫ x in Ioi w, Real.exp (-x ^ 2 / 2) := by
  have hw0 : w ≠ 0 := ne_of_gt hw
  have hMint : IntegrableOn (fun x : ℝ => Real.exp (-x ^ 2 / 2)) (Ioi w) :=
    integrable_exp_neg_sq_half.integrableOn
  have hJint : IntegrableOn (fun x : ℝ => Real.exp (-x ^ 2 / 2) * (x ^ 2)⁻¹) (Ioi w) := by
    have hsum := integrableOn_mills hw
    have hfun : (fun x : ℝ => Real.exp (-x ^ 2 / 2) * (x ^ 2)⁻¹)
        = fun x : ℝ => Real.exp (-x ^ 2 / 2) * (1 + (x ^ 2)⁻¹) - Real.exp (-x ^ 2 / 2) := by
      funext x; ring
    rw [hfun]
    exact hsum.sub hMint
  have hlim : Tendsto (fun u : ℝ => -(Real.exp (-u ^ 2 / 2) / u)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => Real.exp (-u ^ 2 / 2) * u⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_exp_neg_sq_half_atTop.mul tendsto_inv_atTop_zero
    have h2 : Tendsto (fun u : ℝ => -(Real.exp (-u ^ 2 / 2) * u⁻¹)) atTop (𝓝 0) := by
      simpa using h1.neg
    refine h2.congr fun u => ?_
    rw [div_eq_mul_inv (Real.exp (-u ^ 2 / 2)) u]
  have hftc : ∫ x in Ioi w, Real.exp (-x ^ 2 / 2) * (1 + (x ^ 2)⁻¹)
      = Real.exp (-w ^ 2 / 2) / w := by
    have h := integral_Ioi_of_hasDerivAt_of_tendsto'
      (f := fun u : ℝ => -(Real.exp (-u ^ 2 / 2) / u))
      (f' := fun u : ℝ => Real.exp (-u ^ 2 / 2) * (1 + (u ^ 2)⁻¹)) (a := w)
      (fun x hx => hasDerivAt_mills (ne_of_gt (hw.trans_le hx)))
      (integrableOn_mills hw) hlim
    simpa using h
  have hsplit : ∫ x in Ioi w, Real.exp (-x ^ 2 / 2) * (1 + (x ^ 2)⁻¹)
      = (∫ x in Ioi w, Real.exp (-x ^ 2 / 2))
        + ∫ x in Ioi w, Real.exp (-x ^ 2 / 2) * (x ^ 2)⁻¹ := by
    rw [← integral_add hMint hJint]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    ring
  have hJle : (∫ x in Ioi w, Real.exp (-x ^ 2 / 2) * (x ^ 2)⁻¹)
      ≤ (w ^ 2)⁻¹ * ∫ x in Ioi w, Real.exp (-x ^ 2 / 2) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hJint (hMint.const_mul _) measurableSet_Ioi fun x hx => ?_
    have hxw : w < x := hx
    have hx0 : 0 < x := hw.trans hxw
    have hsq : w ^ 2 ≤ x ^ 2 := by nlinarith
    have hinv : (x ^ 2)⁻¹ ≤ (w ^ 2)⁻¹ := by gcongr
    nlinarith [mul_le_mul_of_nonneg_left hinv (Real.exp_pos (-x ^ 2 / 2)).le]
  set M : ℝ := ∫ x in Ioi w, Real.exp (-x ^ 2 / 2) with hMdef
  have hkey : Real.exp (-w ^ 2 / 2) / w ≤ M + (w ^ 2)⁻¹ * M := by
    rw [← hftc, hsplit]; linarith
  have hpos : (0 : ℝ) < 1 + w ^ 2 := by positivity
  rw [← mul_div_assoc, div_le_iff₀ hpos]
  have h2 : Real.exp (-w ^ 2 / 2) ≤ (M + (w ^ 2)⁻¹ * M) * w := (div_le_iff₀ hw).1 hkey
  have h3 : (M + (w ^ 2)⁻¹ * M) * w * w = M * (1 + w ^ 2) := by field_simp; ring
  have h4 := mul_le_mul_of_nonneg_right h2 hw.le
  rw [h3] at h4
  exact h4

/-- **The normalised one-sided first absolute moment about `w ≥ 0`**, on the right half-line:
`e^{w²/2}∫_w^∞ (x−w)e^{-x²/2}dx ≤ (1+w²)^{-1}`. This is the only consequence of Mills'
bound that the derivative estimate uses. -/
private lemma exp_mul_integral_Ioi_sub_le {w : ℝ} (hw : 0 ≤ w) :
    Real.exp (w ^ 2 / 2) * (∫ x in Ioi w, (x - w) * Real.exp (-x ^ 2 / 2)) * (1 + w ^ 2)
      ≤ 1 := by
  have hI : (∫ x in Ioi w, (x - w) * Real.exp (-x ^ 2 / 2))
      = Real.exp (-w ^ 2 / 2) - w * ∫ x in Ioi w, Real.exp (-x ^ 2 / 2) := by
    have h1 : IntegrableOn (fun x : ℝ => x * Real.exp (-x ^ 2 / 2)) (Ioi w) :=
      integrable_id_mul_exp_neg_sq_half.integrableOn
    have h2 : IntegrableOn (fun x : ℝ => w * Real.exp (-x ^ 2 / 2)) (Ioi w) :=
      (integrable_exp_neg_sq_half.const_mul w).integrableOn
    rw [show (fun x : ℝ => (x - w) * Real.exp (-x ^ 2 / 2))
        = fun x : ℝ => x * Real.exp (-x ^ 2 / 2) - w * Real.exp (-x ^ 2 / 2) from by
      funext x; ring, integral_sub h1 h2, integral_Ioi_id_mul_exp_neg_sq_half,
      integral_const_mul]
  rw [hI]
  have hexp : Real.exp (w ^ 2 / 2) * Real.exp (-w ^ 2 / 2) = 1 := by
    rw [← Real.exp_add, show w ^ 2 / 2 + -w ^ 2 / 2 = 0 by ring, Real.exp_zero]
  rcases eq_or_lt_of_le hw with hw0 | hw0
  · rw [← hw0]
    norm_num
  · set M : ℝ := ∫ x in Ioi w, Real.exp (-x ^ 2 / 2) with hMdef
    have hE : (0 : ℝ) < Real.exp (w ^ 2 / 2) := Real.exp_pos _
    have hpos : (0 : ℝ) < 1 + w ^ 2 := by positivity
    have hmills := mul_div_le_integral_Ioi_exp_neg_sq_half hw0
    rw [← hMdef] at hmills
    have heq : w * Real.exp (w ^ 2 / 2) * (Real.exp (-w ^ 2 / 2) * (w / (1 + w ^ 2)))
        = w ^ 2 / (1 + w ^ 2) := by
      rw [show w * Real.exp (w ^ 2 / 2) * (Real.exp (-w ^ 2 / 2) * (w / (1 + w ^ 2)))
          = Real.exp (w ^ 2 / 2) * Real.exp (-w ^ 2 / 2) * (w * w / (1 + w ^ 2)) by ring,
        hexp, one_mul]
      ring
    have hkey : w ^ 2 / (1 + w ^ 2) ≤ w * Real.exp (w ^ 2 / 2) * M := by
      rw [← heq]
      exact mul_le_mul_of_nonneg_left hmills (mul_pos hw0 hE).le
    have hid : w ^ 2 / (1 + w ^ 2) = 1 - 1 / (1 + w ^ 2) := by field_simp; ring
    rw [hid] at hkey
    have hfin : Real.exp (w ^ 2 / 2) * (Real.exp (-w ^ 2 / 2) - w * M)
        = 1 - w * Real.exp (w ^ 2 / 2) * M := by
      rw [show Real.exp (w ^ 2 / 2) * (Real.exp (-w ^ 2 / 2) - w * M)
          = Real.exp (w ^ 2 / 2) * Real.exp (-w ^ 2 / 2) - w * Real.exp (w ^ 2 / 2) * M by ring,
        hexp]
    rw [hfin]
    calc (1 - w * Real.exp (w ^ 2 / 2) * M) * (1 + w ^ 2)
        ≤ (1 / (1 + w ^ 2)) * (1 + w ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ hpos.le
          linarith
      _ = 1 := by field_simp

/-- The left-half-line twin of `exp_mul_integral_Ioi_sub_le`, obtained by reflection. -/
private lemma exp_mul_integral_Iic_sub_le {w : ℝ} (hw : w ≤ 0) :
    Real.exp (w ^ 2 / 2) * (∫ x in Iic w, (w - x) * Real.exp (-x ^ 2 / 2)) * (1 + w ^ 2)
      ≤ 1 := by
  have hrefl : (∫ x in Iic w, (w - x) * Real.exp (-x ^ 2 / 2))
      = ∫ x in Ioi (-w), (x - -w) * Real.exp (-x ^ 2 / 2) := by
    have h := integral_comp_neg_Iic (c := w)
      (f := fun y : ℝ => (y - -w) * Real.exp (-y ^ 2 / 2))
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Iic fun x _ => ?_
    rw [neg_sq]
    ring
  rw [hrefl, show w ^ 2 = (-w) ^ 2 from (neg_sq w).symm]
  exact exp_mul_integral_Ioi_sub_le (by linarith)

/-! ### The centred test function

Two elementary facts about `g = h − 𝔼h(Z)`: it integrates to zero against the kernel — this
is what makes the *tail* representation `f_h(w) = -e^{w²/2}∫_w^∞ g e^{-x²/2}` available — and
it grows at most linearly, `|g(w)| ≤ L(|w| + 1)`, which is what makes the tail representation
useful. -/

/-- A function with a Lipschitz bound is continuous. -/
theorem continuous_of_lipschitz_bound {h : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|) : Continuous h :=
  (LipschitzWith.of_dist_le_mul (K := L.toNNReal) fun x y => by
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL]
    exact hlip x y).continuous

/-- **The Gaussian expectation against the unnormalised kernel.** -/
theorem integral_mul_exp_neg_sq_half_eq {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) :
    ∫ x : ℝ, h x * Real.exp (-x ^ 2 / 2) = Real.sqrt (2 * Real.pi) * stdGaussianExpect h := by
  have hs : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hpdf : ∀ x : ℝ, gaussianPDFReal 0 1 x
      = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
    intro x
    rw [gaussianPDFReal]
    norm_num
  have hEq : stdGaussianExpect h
      = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x : ℝ, h x * Real.exp (-x ^ 2 / 2) := by
    rw [stdGaussianExpect, integral_gaussianReal_eq_integral_smul one_ne_zero,
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hpdf x, smul_eq_mul]
    ring
  rw [hEq, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

/-- **The centred test function integrates to zero against the Gaussian kernel.** -/
theorem integral_centred_mul_exp_neg_sq_half {h : ℝ → ℝ} (hh : Continuous h) {C : ℝ}
    (hC : ∀ x, |h x| ≤ C) :
    ∫ x : ℝ, (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2) = 0 := by
  have h1 : Integrable fun x : ℝ => h x * Real.exp (-x ^ 2 / 2) :=
    integrable_mul_exp_neg_sq_half hh hC
  have h2 : Integrable fun x : ℝ => stdGaussianExpect h * Real.exp (-x ^ 2 / 2) :=
    integrable_exp_neg_sq_half.const_mul _
  rw [show (fun x : ℝ => (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2))
      = fun x : ℝ => h x * Real.exp (-x ^ 2 / 2)
        - stdGaussianExpect h * Real.exp (-x ^ 2 / 2) from by funext x; ring,
    integral_sub h1 h2, integral_mul_exp_neg_sq_half_eq hh hC, integral_const_mul,
    integral_exp_neg_sq_half]
  ring

/-- **The centred test function grows at most linearly:** `|h(w) − 𝔼h(Z)| ≤ L(|w| + 1)`. The
sharp constant is `𝔼|Z| = √(2/π) < 1` in place of the `1`, which is where the crude bound
`2 ≤ √(2π)` is spent. -/
theorem abs_sub_stdGaussianExpect_le {h : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|) {C : ℝ} (hC : ∀ x, |h x| ≤ C) (w : ℝ) :
    |h w - stdGaussianExpect h| ≤ L * (|w| + 1) := by
  have hh : Continuous h := continuous_of_lipschitz_bound hL hlip
  have hs : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have habs : Integrable fun y : ℝ => |y| * Real.exp (-y ^ 2 / 2) := by
    refine integrable_id_mul_exp_neg_sq_half.abs.congr
      (Filter.Eventually.of_forall fun y => ?_)
    simp only [abs_mul, abs_of_pos (Real.exp_pos (-y ^ 2 / 2))]
  -- the centred value as an average of increments
  have hrep : h w - stdGaussianExpect h
      = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ y : ℝ, (h w - h y) * Real.exp (-y ^ 2 / 2) := by
    have h1 : Integrable fun y : ℝ => h w * Real.exp (-y ^ 2 / 2) :=
      integrable_exp_neg_sq_half.const_mul _
    have h2 : Integrable fun y : ℝ => h y * Real.exp (-y ^ 2 / 2) :=
      integrable_mul_exp_neg_sq_half hh hC
    rw [show (fun y : ℝ => (h w - h y) * Real.exp (-y ^ 2 / 2))
        = fun y : ℝ => h w * Real.exp (-y ^ 2 / 2) - h y * Real.exp (-y ^ 2 / 2) from by
      funext y; ring, integral_sub h1 h2, integral_const_mul, integral_exp_neg_sq_half,
      integral_mul_exp_neg_sq_half_eq hh hC]
    field_simp
  -- the increments are dominated by `L(|w| + |y|)`
  have hmaj : Integrable fun y : ℝ => L * ((|w| + |y|) * Real.exp (-y ^ 2 / 2)) := by
    refine (Integrable.const_mul ?_ L)
    refine ((integrable_exp_neg_sq_half.const_mul |w|).add habs).congr
      (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply]
    ring
  have hbound : |∫ y : ℝ, (h w - h y) * Real.exp (-y ^ 2 / 2)|
      ≤ L * (|w| * Real.sqrt (2 * Real.pi) + 2) := by
    have hstep : ∫ y : ℝ, L * ((|w| + |y|) * Real.exp (-y ^ 2 / 2))
        = L * (|w| * Real.sqrt (2 * Real.pi) + 2) := by
      rw [integral_const_mul, show (fun y : ℝ => (|w| + |y|) * Real.exp (-y ^ 2 / 2))
          = fun y : ℝ => |w| * Real.exp (-y ^ 2 / 2) + |y| * Real.exp (-y ^ 2 / 2) from by
        funext y; ring, integral_add (integrable_exp_neg_sq_half.const_mul _) habs,
        integral_const_mul, integral_exp_neg_sq_half, integral_abs_mul_exp_neg_sq_half]
    rw [← hstep]
    refine (abs_integral_le_integral_abs).trans (integral_mono ?_ hmaj fun y => ?_)
    · have hA : Integrable fun y : ℝ => h w * Real.exp (-y ^ 2 / 2) :=
        integrable_exp_neg_sq_half.const_mul _
      have hB : Integrable fun y : ℝ => h y * Real.exp (-y ^ 2 / 2) :=
        integrable_mul_exp_neg_sq_half hh hC
      refine (hA.sub hB).abs.congr (Filter.Eventually.of_forall fun y => ?_)
      have hy : h w * Real.exp (-y ^ 2 / 2) - h y * Real.exp (-y ^ 2 / 2)
          = (h w - h y) * Real.exp (-y ^ 2 / 2) := by ring
      simp only [Pi.sub_apply, hy]
    · simp only [abs_mul, abs_of_pos (Real.exp_pos (-y ^ 2 / 2))]
      have h1 : |h w - h y| ≤ L * |w - y| := hlip w y
      have h2 : |w - y| ≤ |w| + |y| := by
        have hh2 := abs_add_le w (-y)
        rw [← sub_eq_add_neg, abs_neg] at hh2
        exact hh2
      have h3 : (0 : ℝ) < Real.exp (-y ^ 2 / 2) := Real.exp_pos _
      nlinarith [mul_le_mul_of_nonneg_right
        (h1.trans (mul_le_mul_of_nonneg_left h2 hL)) h3.le]
  have h2s : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    have h4 : (4 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have := Real.sqrt_le_sqrt h4
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at this
  rw [hrep, abs_mul, abs_of_nonneg (inv_nonneg.2 hs.le)]
  have hfin : (Real.sqrt (2 * Real.pi))⁻¹ * (L * (|w| * Real.sqrt (2 * Real.pi) + 2))
      ≤ L * (|w| + 1) := by
    rw [inv_mul_eq_div, div_le_iff₀ hs]
    nlinarith [mul_nonneg hL (sub_nonneg.2 h2s), abs_nonneg w]
  exact le_trans (mul_le_mul_of_nonneg_left hbound (inv_nonneg.2 hs.le)) hfin

/-! ### Bounds on the Stein solution for a Lipschitz test function

For an `L`-Lipschitz `h` the classical bounds are `‖f_h‖ ≤ L`, `‖f_h'‖ ≤ √(2/π)·L ≤ L` and
`f_h'` is `2L`-Lipschitz (Chen–Goldstein–Shao, Lemma 2.4; the first is sharp, as `h = id`
gives `f_h ≡ -1`). They are recorded here in the weakest form the exchangeable-pair theorem
needs, namely with the *provable* constants `L`, `2L`, `5L` stated. -/

/-- **The unimodality engine.** A differentiable `ψ` whose derivative is `-e^{-v²/2}` times a
*monotone* function increases and then decreases; if in addition `ψ` vanishes in the limit
along `±n`, then `ψ ≥ 0` everywhere. -/
private lemma nonneg_of_deriv_neg_mul_monotone {ψ ψ' q : ℝ → ℝ}
    (hψ : ∀ v, HasDerivAt ψ (ψ' v) v)
    (hsign : ∀ v, ψ' v = -(Real.exp (-v ^ 2 / 2) * q v))
    (hmono : Monotone q)
    (hbot : Tendsto (fun n : ℕ => ψ (-(n : ℝ))) atTop (𝓝 0))
    (htop : Tendsto (fun n : ℕ => ψ (n : ℝ)) atTop (𝓝 0)) (w : ℝ) :
    0 ≤ ψ w := by
  have hdiff : Differentiable ℝ ψ := fun v => (hψ v).differentiableAt
  have hderiv : ∀ v, deriv ψ v = ψ' v := fun v => (hψ v).deriv
  rcases le_or_gt (q w) 0 with hq | hq
  · have hmonoOn : MonotoneOn ψ (Iic w) := by
      refine monotoneOn_of_deriv_nonneg (convex_Iic w) hdiff.continuous.continuousOn
        hdiff.differentiableOn fun v hv => ?_
      rw [interior_Iic] at hv
      have hqv : q v ≤ 0 := le_trans (hmono (le_of_lt hv)) hq
      rw [hderiv v, hsign v]
      nlinarith [Real.exp_pos (-v ^ 2 / 2)]
    refine le_of_tendsto hbot ?_
    filter_upwards [eventually_ge_atTop ⌈|w|⌉₊] with n hn
    have hnw : -(n : ℝ) ≤ w := by
      have h1 : (⌈|w|⌉₊ : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
      have h2 : |w| ≤ (⌈|w|⌉₊ : ℝ) := Nat.le_ceil _
      have h3 := neg_abs_le w
      linarith
    exact hmonoOn (mem_Iic.2 hnw) (mem_Iic.2 le_rfl) hnw
  · have hantiOn : AntitoneOn ψ (Ici w) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ici w) hdiff.continuous.continuousOn
        hdiff.differentiableOn fun v hv => ?_
      rw [interior_Ici] at hv
      have hqv : 0 < q v := lt_of_lt_of_le hq (hmono (le_of_lt hv))
      rw [hderiv v, hsign v]
      nlinarith [Real.exp_pos (-v ^ 2 / 2)]
    refine le_of_tendsto htop ?_
    filter_upwards [eventually_ge_atTop ⌈w⌉₊] with n hn
    have hnw : w ≤ (n : ℝ) := by
      have h1 : (⌈w⌉₊ : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
      have h2 : w ≤ (⌈w⌉₊ : ℝ) := Nat.le_ceil _
      linarith
    exact hantiOn (mem_Ici.2 le_rfl) (mem_Ici.2 hnw) hnw

/-- **The tail integral of the centred test function is `L e^{-w²/2}` in absolute value.**
This is the sup-norm bound in the form in which it is proved: `u(w) = ∫_{-∞}^w (h − 𝔼h)e^{-x²/2}`
satisfies `u(±∞) = 0`, and `L e^{-w²/2} ∓ u` has derivative `-e^{-w²/2}(Lw ± (h − 𝔼h))` whose
second factor is *monotone*, so both are unimodal with vanishing limits, hence nonnegative. -/
theorem abs_gaussTail_le {h : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|) {C : ℝ} (hC : ∀ x, |h x| ≤ C) (w : ℝ) :
    |∫ x in Iic w, (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2)|
      ≤ L * Real.exp (-w ^ 2 / 2) := by
  have hh : Continuous h := continuous_of_lipschitz_bound hL hlip
  have hFint := integrable_centred_mul_exp_neg_sq_half hh hC
  have hzero := integral_centred_mul_exp_neg_sq_half hh hC
  -- the two limits of the tail integral along the integers
  have hlimTop : Tendsto
      (fun n : ℕ => ∫ x in Iic (n : ℝ), (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2))
      atTop (𝓝 0) := by
    have hmono : Monotone fun n : ℕ => Iic (n : ℝ) := fun i j hij =>
      Iic_subset_Iic.2 (Nat.cast_le.2 hij)
    have huniv : (⋃ n : ℕ, Iic (n : ℝ)) = univ :=
      eq_univ_of_forall fun x => mem_iUnion.2 ⟨⌈x⌉₊, Nat.le_ceil x⟩
    have hres := tendsto_setIntegral_of_monotone (f := fun x : ℝ =>
      (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2))
      (fun _ => measurableSet_Iic) hmono (by rw [huniv]; exact hFint.integrableOn)
    rwa [huniv, Measure.restrict_univ, hzero] at hres
  have hlimBot : Tendsto
      (fun n : ℕ => ∫ x in Iic (-(n : ℝ)), (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2))
      atTop (𝓝 0) := by
    have hanti : Antitone fun n : ℕ => Iic (-(n : ℝ)) := fun i j hij =>
      Iic_subset_Iic.2 (neg_le_neg (Nat.cast_le.2 hij))
    have hinter : (⋂ n : ℕ, Iic (-(n : ℝ))) = (∅ : Set ℝ) := by
      ext x
      simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-x)
      exact ⟨n, by linarith⟩
    have hres := tendsto_setIntegral_of_antitone (f := fun x : ℝ =>
      (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2))
      (fun _ => measurableSet_Iic) hanti ⟨0, hFint.integrableOn⟩
    rw [hinter] at hres
    simpa using hres
  have hEnat : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) ^ 2 / 2)) atTop (𝓝 0) :=
    tendsto_exp_neg_sq_half_atTop.comp tendsto_natCast_atTop_atTop
  have hEnat' : Tendsto (fun n : ℕ => Real.exp (-(-(n : ℝ)) ^ 2 / 2)) atTop (𝓝 0) := by
    refine hEnat.congr fun n => ?_
    rw [neg_sq]
  rw [abs_le]
  constructor
  · -- `L e^{-w²/2} + u(w) ≥ 0`
    have hpsi := nonneg_of_deriv_neg_mul_monotone
      (ψ := fun s : ℝ => L * Real.exp (-s ^ 2 / 2)
        + ∫ x in Iic s, (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2))
      (ψ' := fun s : ℝ =>
        -(Real.exp (-s ^ 2 / 2) * (L * s - (h s - stdGaussianExpect h))))
      (q := fun s : ℝ => L * s - (h s - stdGaussianExpect h))
      (fun v => by
        have h1 := ((hasDerivAt_exp_neg_sq_half v).const_mul L).add
          (hasDerivAt_gaussTail hh hC v)
        convert! h1 using 1
        ring)
      (fun _ => rfl)
      (fun s t hst => by
        have := hlip t s
        rw [abs_le] at this
        have habs : |t - s| = t - s := abs_of_nonneg (by linarith)
        rw [habs] at this
        simp only
        linarith [this.1])
      (by simpa using (hEnat'.const_mul L).add hlimBot)
      (by simpa using (hEnat.const_mul L).add hlimTop) w
    linarith
  · -- `L e^{-w²/2} - u(w) ≥ 0`
    have hpsi := nonneg_of_deriv_neg_mul_monotone
      (ψ := fun s : ℝ => L * Real.exp (-s ^ 2 / 2)
        - ∫ x in Iic s, (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2))
      (ψ' := fun s : ℝ =>
        -(Real.exp (-s ^ 2 / 2) * (L * s + (h s - stdGaussianExpect h))))
      (q := fun s : ℝ => L * s + (h s - stdGaussianExpect h))
      (fun v => by
        have h1 := ((hasDerivAt_exp_neg_sq_half v).const_mul L).sub
          (hasDerivAt_gaussTail hh hC v)
        convert! h1 using 1
        ring)
      (fun _ => rfl)
      (fun s t hst => by
        have := hlip t s
        rw [abs_le] at this
        have habs : |t - s| = t - s := abs_of_nonneg (by linarith)
        rw [habs] at this
        simp only
        linarith [this.2])
      (by simpa using (hEnat'.const_mul L).sub hlimBot)
      (by simpa using (hEnat.const_mul L).sub hlimTop) w
    linarith

/-- **Sup-norm bound on the Stein solution.** For an `L`-Lipschitz test function `h`,
`|f_h(w)| ≤ L` for every `w`; the constant is sharp (take `h = id`, for which `f_h ≡ -1`). -/
theorem abs_steinSolution_le {h : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|) {C : ℝ} (hC : ∀ x, |h x| ≤ C) (w : ℝ) :
    |steinSolution h w| ≤ L := by
  have hdef : steinSolution h w = Real.exp (w ^ 2 / 2) *
      ∫ x in Iic w, (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2) := rfl
  have hee : Real.exp (w ^ 2 / 2) * Real.exp (-w ^ 2 / 2) = 1 := by
    rw [← Real.exp_add, show w ^ 2 / 2 + -w ^ 2 / 2 = 0 by ring, Real.exp_zero]
  rw [hdef, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (w ^ 2 / 2)
        * |∫ x in Iic w, (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2)|
      ≤ Real.exp (w ^ 2 / 2) * (L * Real.exp (-w ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left (abs_gaussTail_le hL hlip hC w) (Real.exp_pos _).le
    _ = L := by
        rw [show Real.exp (w ^ 2 / 2) * (L * Real.exp (-w ^ 2 / 2))
          = L * (Real.exp (w ^ 2 / 2) * Real.exp (-w ^ 2 / 2)) by ring, hee, mul_one]

/-- `|a − b| ≤ |a| + |b|`. -/
private lemma abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have hab := abs_add_le a (-b)
  rwa [← sub_eq_add_neg, abs_neg] at hab

/-- **The core of the derivative bound**, stated for an already-centred `g` (which is all the
Stein solution ever sees). The point is the *pointwise-in-`w`* estimate

`|f'(w)| (1 + w²) ≤ L (2|w| + 1)`,

which is strictly stronger than `|f'(w)| ≤ 2L` and is what the Lipschitz bound on `f'`
consumes. The proof rewrites `f'(w) = w f(w) + g(w)` as a *single* integral over the half-line
on the far side of `w`, using `∫ g e^{-x²/2} = 0` to move the tail and
`∫_w^∞ x e^{-x²/2}dx = e^{-w²/2}` to absorb `g(w)`:

`f'(w) = e^{w²/2} ∫_w^∞ (g(w) x − w g(x)) e^{-x²/2} dx` for `w ≥ 0`,

and the integrand is bounded by `(|g(w)| + |w| L)|x − w|` because
`g(w)x − w g(x) = g(w)(x − w) − w(g(x) − g(w))`. The resulting one-sided first absolute
moment is exactly `exp_mul_integral_Ioi_sub_le`. -/
private lemma abs_deriv_steinSolution_mul_le {g : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |g x - g y| ≤ L * |x - y|)
    (hgint : Integrable fun x : ℝ => g x * Real.exp (-x ^ 2 / 2))
    (hgzero : ∫ x : ℝ, g x * Real.exp (-x ^ 2 / 2) = 0)
    (hgw : ∀ v, |g v| ≤ L * (|v| + 1)) (w : ℝ) :
    |w * (Real.exp (w ^ 2 / 2) * ∫ x in Iic w, g x * Real.exp (-x ^ 2 / 2)) + g w|
      * (1 + w ^ 2) ≤ L * (2 * |w| + 1) := by
  have hee : Real.exp (w ^ 2 / 2) * Real.exp (-w ^ 2 / 2) = 1 := by
    rw [← Real.exp_add, show w ^ 2 / 2 + -w ^ 2 / 2 = 0 by ring, Real.exp_zero]
  have hS : (0 : ℝ) < 1 + w ^ 2 := by positivity
  have hKn : (0 : ℝ) ≤ |g w| + |w| * L :=
    add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hL)
  have hK : |g w| + |w| * L ≤ L * (2 * |w| + 1) := by
    have := hgw w
    nlinarith [abs_nonneg w]
  have hA : ∀ S : Set ℝ, IntegrableOn (fun x : ℝ => g w * (x * Real.exp (-x ^ 2 / 2))) S :=
    fun S => (integrable_id_mul_exp_neg_sq_half.const_mul _).integrableOn
  have hB : ∀ S : Set ℝ, IntegrableOn (fun x : ℝ => w * (g x * Real.exp (-x ^ 2 / 2))) S :=
    fun S => (hgint.const_mul _).integrableOn
  have hPint : ∀ S : Set ℝ,
      IntegrableOn (fun x : ℝ => (g w * x - w * g x) * Real.exp (-x ^ 2 / 2)) S := by
    intro S
    refine ((hA S).sub (hB S)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hQint : ∀ (v : ℝ) (S : Set ℝ),
      IntegrableOn (fun x : ℝ => (x - v) * Real.exp (-x ^ 2 / 2)) S := by
    intro v S
    have h1 : Integrable fun x : ℝ => x * Real.exp (-x ^ 2 / 2) :=
      integrable_id_mul_exp_neg_sq_half
    have h2 : Integrable fun x : ℝ => v * Real.exp (-x ^ 2 / 2) :=
      integrable_exp_neg_sq_half.const_mul _
    refine (h1.sub h2).integrableOn.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  rcases le_or_gt 0 w with hw | hw
  · -- the right half-line
    have htail : (∫ x in Iic w, g x * Real.exp (-x ^ 2 / 2))
        = -∫ x in Ioi w, g x * Real.exp (-x ^ 2 / 2) := by
      have hsum := intervalIntegral.integral_Iic_add_Ioi (b := w)
        (f := fun x : ℝ => g x * Real.exp (-x ^ 2 / 2))
        hgint.integrableOn hgint.integrableOn
      rw [hgzero] at hsum
      linarith
    have hlin : (∫ x in Ioi w, (g w * x - w * g x) * Real.exp (-x ^ 2 / 2))
        = g w * (∫ x in Ioi w, x * Real.exp (-x ^ 2 / 2))
          - w * ∫ x in Ioi w, g x * Real.exp (-x ^ 2 / 2) := by
      rw [show (fun x : ℝ => (g w * x - w * g x) * Real.exp (-x ^ 2 / 2))
          = fun x : ℝ => g w * (x * Real.exp (-x ^ 2 / 2))
            - w * (g x * Real.exp (-x ^ 2 / 2)) from by funext x; ring,
        integral_sub (hA (Ioi w)) (hB (Ioi w)), integral_const_mul, integral_const_mul]
    have hrep : w * (Real.exp (w ^ 2 / 2) * ∫ x in Iic w, g x * Real.exp (-x ^ 2 / 2)) + g w
        = Real.exp (w ^ 2 / 2)
          * ∫ x in Ioi w, (g w * x - w * g x) * Real.exp (-x ^ 2 / 2) := by
      rw [hlin, integral_Ioi_id_mul_exp_neg_sq_half, htail]
      linear_combination (-(g w)) * hee
    have hbnd : |∫ x in Ioi w, (g w * x - w * g x) * Real.exp (-x ^ 2 / 2)|
        ≤ (|g w| + |w| * L) * ∫ x in Ioi w, (x - w) * Real.exp (-x ^ 2 / 2) := by
      rw [← integral_const_mul]
      refine abs_integral_le_integral_abs.trans ?_
      refine setIntegral_mono_on (hPint (Ioi w)).abs
        ((hQint w (Ioi w)).const_mul _) measurableSet_Ioi fun x hx => ?_
      have hxw : w < x := hx
      have hE : (0 : ℝ) < Real.exp (-x ^ 2 / 2) := Real.exp_pos _
      have h1 : |g x - g w| ≤ L * (x - w) := by
        have hl := hlip x w
        rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - w)] at hl
      have h2 : |g w * x - w * g x| ≤ (|g w| + |w| * L) * (x - w) := by
        rw [show g w * x - w * g x = g w * (x - w) - w * (g x - g w) by ring]
        refine (abs_sub_le_add _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - w)]
        nlinarith [abs_nonneg w, h1]
      simp only [abs_mul, abs_of_pos hE]
      nlinarith [mul_le_mul_of_nonneg_right h2 hE.le]
    have hrho := exp_mul_integral_Ioi_sub_le hw
    rw [hrep, abs_mul, abs_of_pos (Real.exp_pos (w ^ 2 / 2))]
    calc Real.exp (w ^ 2 / 2)
          * |∫ x in Ioi w, (g w * x - w * g x) * Real.exp (-x ^ 2 / 2)| * (1 + w ^ 2)
        ≤ Real.exp (w ^ 2 / 2)
            * ((|g w| + |w| * L) * ∫ x in Ioi w, (x - w) * Real.exp (-x ^ 2 / 2))
            * (1 + w ^ 2) := by
          have hm := mul_le_mul_of_nonneg_left hbnd (Real.exp_pos (w ^ 2 / 2)).le
          nlinarith [hS.le]
      _ = (|g w| + |w| * L)
            * (Real.exp (w ^ 2 / 2) * (∫ x in Ioi w, (x - w) * Real.exp (-x ^ 2 / 2))
              * (1 + w ^ 2)) := by ring
      _ ≤ (|g w| + |w| * L) * 1 := mul_le_mul_of_nonneg_left hrho hKn
      _ = |g w| + |w| * L := mul_one _
      _ ≤ L * (2 * |w| + 1) := hK
  · -- the left half-line
    have hlin : (∫ x in Iic w, (g w * x - w * g x) * Real.exp (-x ^ 2 / 2))
        = g w * (∫ x in Iic w, x * Real.exp (-x ^ 2 / 2))
          - w * ∫ x in Iic w, g x * Real.exp (-x ^ 2 / 2) := by
      rw [show (fun x : ℝ => (g w * x - w * g x) * Real.exp (-x ^ 2 / 2))
          = fun x : ℝ => g w * (x * Real.exp (-x ^ 2 / 2))
            - w * (g x * Real.exp (-x ^ 2 / 2)) from by funext x; ring,
        integral_sub (hA (Iic w)) (hB (Iic w)), integral_const_mul, integral_const_mul]
    have hrep : w * (Real.exp (w ^ 2 / 2) * ∫ x in Iic w, g x * Real.exp (-x ^ 2 / 2)) + g w
        = -(Real.exp (w ^ 2 / 2)
          * ∫ x in Iic w, (g w * x - w * g x) * Real.exp (-x ^ 2 / 2)) := by
      rw [hlin, integral_Iic_id_mul_exp_neg_sq_half]
      linear_combination (-(g w)) * hee
    have hQ' : IntegrableOn (fun x : ℝ => (w - x) * Real.exp (-x ^ 2 / 2)) (Iic w) := by
      refine ((hQint w (Iic w)).neg).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.neg_apply]
      ring
    have hbnd : |∫ x in Iic w, (g w * x - w * g x) * Real.exp (-x ^ 2 / 2)|
        ≤ (|g w| + |w| * L) * ∫ x in Iic w, (w - x) * Real.exp (-x ^ 2 / 2) := by
      rw [← integral_const_mul]
      refine abs_integral_le_integral_abs.trans ?_
      refine setIntegral_mono_on (hPint (Iic w)).abs
        (hQ'.const_mul _) measurableSet_Iic fun x hx => ?_
      have hxw : x ≤ w := hx
      have hE : (0 : ℝ) < Real.exp (-x ^ 2 / 2) := Real.exp_pos _
      have h1 : |g x - g w| ≤ L * (w - x) := by
        have hl := hlip x w
        rwa [abs_of_nonpos (by linarith : x - w ≤ 0), neg_sub] at hl
      have h2 : |g w * x - w * g x| ≤ (|g w| + |w| * L) * (w - x) := by
        rw [show g w * x - w * g x = g w * (x - w) - w * (g x - g w) by ring]
        refine (abs_sub_le_add _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonpos (by linarith : x - w ≤ 0), neg_sub]
        nlinarith [abs_nonneg w, h1]
      simp only [abs_mul, abs_of_pos hE]
      nlinarith [mul_le_mul_of_nonneg_right h2 hE.le]
    have hrho := exp_mul_integral_Iic_sub_le hw.le
    rw [hrep, abs_neg, abs_mul, abs_of_pos (Real.exp_pos (w ^ 2 / 2))]
    calc Real.exp (w ^ 2 / 2)
          * |∫ x in Iic w, (g w * x - w * g x) * Real.exp (-x ^ 2 / 2)| * (1 + w ^ 2)
        ≤ Real.exp (w ^ 2 / 2)
            * ((|g w| + |w| * L) * ∫ x in Iic w, (w - x) * Real.exp (-x ^ 2 / 2))
            * (1 + w ^ 2) := by
          have hm := mul_le_mul_of_nonneg_left hbnd (Real.exp_pos (w ^ 2 / 2)).le
          nlinarith [hS.le]
      _ = (|g w| + |w| * L)
            * (Real.exp (w ^ 2 / 2) * (∫ x in Iic w, (w - x) * Real.exp (-x ^ 2 / 2))
              * (1 + w ^ 2)) := by ring
      _ ≤ (|g w| + |w| * L) * 1 := mul_le_mul_of_nonneg_left hrho hKn
      _ = |g w| + |w| * L := mul_one _
      _ ≤ L * (2 * |w| + 1) := hK

/-- **The sharp form of the derivative bound**: `|f_h'(w)| (1 + w²) ≤ L(2|w| + 1)`. It contains
both `abs_deriv_steinSolution_le` (`(2|w|+1) ≤ 2(1+w²)`) and the estimate
`|w||f_h'(w)| ≤ 3L` that the Lipschitz bound needs. -/
theorem abs_deriv_steinSolution_mul_one_add_sq_le {h : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|) {C : ℝ} (hC : ∀ x, |h x| ≤ C) (w : ℝ) :
    |deriv (steinSolution h) w| * (1 + w ^ 2) ≤ L * (2 * |w| + 1) := by
  have hh : Continuous h := continuous_of_lipschitz_bound hL hlip
  have hderiv : deriv (steinSolution h) w
      = w * (Real.exp (w ^ 2 / 2)
          * ∫ x in Iic w, (h x - stdGaussianExpect h) * Real.exp (-x ^ 2 / 2))
        + (h w - stdGaussianExpect h) := (hasDerivAt_steinSolution hh hC w).deriv
  rw [hderiv]
  exact abs_deriv_steinSolution_mul_le (g := fun x => h x - stdGaussianExpect h) hL
    (fun x y => by simpa using hlip x y)
    (integrable_centred_mul_exp_neg_sq_half hh hC)
    (integral_centred_mul_exp_neg_sq_half hh hC)
    (fun v => abs_sub_stdGaussianExpect_le hL hlip hC v) w

/-- **Sup-norm bound on the derivative of the Stein solution.** For an `L`-Lipschitz test
function, `|f_h'(w)| ≤ 2L`. (The sharp constant is `√(2/π) < 1`; `2` is what the elementary
route yields — see `abs_deriv_steinSolution_mul_one_add_sq_le` — and it suffices
downstream.) -/
theorem abs_deriv_steinSolution_le {h : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|) {C : ℝ} (hC : ∀ x, |h x| ≤ C) (w : ℝ) :
    |deriv (steinSolution h) w| ≤ 2 * L := by
  have hsharp := abs_deriv_steinSolution_mul_one_add_sq_le hL hlip hC w
  have hS : (0 : ℝ) < 1 + w ^ 2 := by positivity
  have hsq : |w| ^ 2 = w ^ 2 := sq_abs w
  rw [← sub_nonneg]
  have hkey : (2 * L - |deriv (steinSolution h) w|) * (1 + w ^ 2)
      ≥ L * (2 * |w| ^ 2 - 2 * |w| + 1) := by nlinarith [abs_nonneg w]
  nlinarith [abs_nonneg w, abs_nonneg (deriv (steinSolution h) w),
    mul_nonneg hL (by nlinarith [sq_nonneg (2 * |w| - 1)] :
      (0 : ℝ) ≤ 2 * |w| ^ 2 - 2 * |w| + 1)]

/-- A function with a bounded derivative is Lipschitz, in the elementary form used below:
`M·u ∓ F(u)` are both monotone. -/
private lemma abs_sub_le_of_abs_deriv_le {F F' : ℝ → ℝ} (hF : ∀ u, HasDerivAt F (F' u) u)
    {M : ℝ} (hM : ∀ u, |F' u| ≤ M) (x y : ℝ) : |F x - F y| ≤ M * |x - y| := by
  have hg1 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => M * v - F v) (M - F' u) u := by
    intro u
    have hu := ((hasDerivAt_id' u).const_mul M).sub (hF u)
    convert! hu using 1
    ring
  have hg2 : ∀ u : ℝ, HasDerivAt (fun v : ℝ => M * v + F v) (M + F' u) u := by
    intro u
    have hu := ((hasDerivAt_id' u).const_mul M).add (hF u)
    convert! hu using 1
    ring
  have hmono1 : Monotone fun v : ℝ => M * v - F v :=
    monotone_of_deriv_nonneg (fun u => (hg1 u).differentiableAt) fun u => by
      rw [(hg1 u).deriv]; linarith [(le_abs_self (F' u)).trans (hM u)]
  have hmono2 : Monotone fun v : ℝ => M * v + F v :=
    monotone_of_deriv_nonneg (fun u => (hg2 u).differentiableAt) fun u => by
      rw [(hg2 u).deriv]; linarith [neg_abs_le (F' u), hM u]
  rcases le_total x y with hxy | hxy
  · have h1 : M * x - F x ≤ M * y - F y := hmono1 hxy
    have h2 : M * x + F x ≤ M * y + F y := hmono2 hxy
    have hd : |x - y| = y - x := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [hd, abs_le]
    constructor <;> nlinarith
  · have h1 : M * y - F y ≤ M * x - F x := hmono1 hxy
    have h2 : M * y + F y ≤ M * x + F x := hmono2 hxy
    have hd : |x - y| = x - y := abs_of_nonneg (by linarith)
    rw [hd, abs_le]
    constructor <;> nlinarith

/-- **Lipschitz bound on the derivative of the Stein solution**, i.e. the `‖f_h''‖ ≤ 2L` of
the classical statement, in the form actually used by the Taylor step.

CONSTANT. The statement is proved with `5L` in place of the textbook `2L`; the deviation is
deliberate. Since `h` is only *Lipschitz*, `f_h''` need not exist, so the bound is proved for
the increment directly, via `f_h'(u) = u f_h(u) + g(u)`: the map `u ↦ u f_h(u)` is
differentiable with derivative `f_h(u) + u f_h'(u)`, bounded by `L + 3L = 4L` by
`abs_steinSolution_le` and `abs_deriv_steinSolution_mul_one_add_sq_le` (which gives
`|u||f_h'(u)| ≤ 3L`, since `|u|(2|u| + 1) ≤ 3(1 + u²)`), and `g` is `L`-Lipschitz; total
`5L`. Tracking the sharp `sup_u |u|(2|u| + 1)/(1 + u²) ≈ 2.118` would give `≈ 4.12L`, and the
textbook `2L` needs the sharp `‖f_h'‖ ≤ √(2/π)` together with a genuine second derivative.
Only `abs_sub_sub_mul_deriv_le` consumes this bound, and only through the constant `B₂`, so
any finite constant `c·L` suffices downstream. -/
theorem lipschitz_deriv_steinSolution {h : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ x y, |h x - h y| ≤ L * |x - y|) {C : ℝ} (hC : ∀ x, |h x| ≤ C) (x y : ℝ) :
    |deriv (steinSolution h) x - deriv (steinSolution h) y| ≤ 5 * L * |x - y| := by
  have hh : Continuous h := continuous_of_lipschitz_bound hL hlip
  have hPhi : ∀ u : ℝ, HasDerivAt (fun v : ℝ => v * steinSolution h v)
      (steinSolution h u + u * deriv (steinSolution h) u) u := by
    intro u
    have hd := hasDerivAt_steinSolution hh hC u
    have hmul := (hasDerivAt_id' u).mul hd
    rw [hd.deriv]
    convert! hmul using 1
    ring
  have hbound : ∀ u : ℝ, |steinSolution h u + u * deriv (steinSolution h) u| ≤ 4 * L := by
    intro u
    have h1 := abs_steinSolution_le hL hlip hC u
    have h2 := abs_deriv_steinSolution_mul_one_add_sq_le hL hlip hC u
    have hS : (0 : ℝ) < 1 + u ^ 2 := by positivity
    have hu := abs_nonneg u
    have hsq : |u| ^ 2 = u ^ 2 := sq_abs u
    have h3 : |u| * |deriv (steinSolution h) u| ≤ 3 * L := by
      have hm := mul_le_mul_of_nonneg_left h2 hu
      have hpos : (0 : ℝ) ≤ 3 + u ^ 2 - |u| := by nlinarith [sq_nonneg (|u| - 1)]
      have hstep : |u| * |deriv (steinSolution h) u| * (1 + u ^ 2) ≤ 3 * L * (1 + u ^ 2) := by
        nlinarith [mul_nonneg hL hpos]
      exact le_of_mul_le_mul_right hstep hS
    calc |steinSolution h u + u * deriv (steinSolution h) u|
        ≤ |steinSolution h u| + |u * deriv (steinSolution h) u| := abs_add_le _ _
      _ = |steinSolution h u| + |u| * |deriv (steinSolution h) u| := by rw [abs_mul]
      _ ≤ L + 3 * L := add_le_add h1 h3
      _ = 4 * L := by ring
  have hPhiLip := abs_sub_le_of_abs_deriv_le hPhi hbound x y
  have hdx : deriv (steinSolution h) x
      = x * steinSolution h x + (h x - stdGaussianExpect h) :=
    (hasDerivAt_steinSolution hh hC x).deriv
  have hdy : deriv (steinSolution h) y
      = y * steinSolution h y + (h y - stdGaussianExpect h) :=
    (hasDerivAt_steinSolution hh hC y).deriv
  rw [hdx, hdy]
  calc |x * steinSolution h x + (h x - stdGaussianExpect h)
        - (y * steinSolution h y + (h y - stdGaussianExpect h))|
      ≤ |x * steinSolution h x - y * steinSolution h y| + |h x - h y| := by
        rw [show x * steinSolution h x + (h x - stdGaussianExpect h)
            - (y * steinSolution h y + (h y - stdGaussianExpect h))
            = x * steinSolution h x - y * steinSolution h y + (h x - h y) by ring]
        exact abs_add_le _ _
    _ ≤ 4 * L * |x - y| + L * |x - y| := add_le_add hPhiLip (hlip x y)
    _ = 5 * L * |x - y| := by ring

/-! ### A second-order Taylor bound from a Lipschitz derivative -/

/-- One half of Taylor's theorem with a Lipschitz derivative: the auxiliary function
`u ↦ f u - f x - (u - x) f' x - M (u - x)²/2` has a derivative of the sign that makes it
decrease away from `x` in both directions, hence stays below its value `0` at `x`. -/
private lemma sub_sub_mul_deriv_le {f f' : ℝ → ℝ} (hf : ∀ u, HasDerivAt f (f' u) u) {M : ℝ}
    (hlip : ∀ u v, |f' u - f' v| ≤ M * |u - v|) (x y : ℝ) :
    f y - f x - (y - x) * f' x ≤ M * (y - x) ^ 2 / 2 := by
  set F : ℝ → ℝ := fun u => f u - f x - (u - x) * f' x - M * (u - x) ^ 2 / 2 with hFdef
  have hFd : ∀ u, HasDerivAt F (f' u - f' x - M * (u - x)) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ => f v - f x) (f' u) u := (hf u).sub_const _
    have h2 : HasDerivAt (fun v : ℝ => (v - x) * f' x) (f' x) u := by
      simpa using ((hasDerivAt_id u).sub_const x).mul_const (f' x)
    have h3 : HasDerivAt (fun v : ℝ => M * (v - x) ^ 2 / 2) (M * (u - x)) u := by
      have hp : HasDerivAt (fun v : ℝ => (v - x) ^ 2) (2 * (u - x)) u := by
        simpa using! ((hasDerivAt_id u).sub_const x).pow 2
      have := (hp.const_mul M).div_const 2
      convert! this using 1
      ring
    simpa using! (h1.sub h2).sub h3
  have hFdiff : Differentiable ℝ F := fun u => (hFd u).differentiableAt
  have hderiv : ∀ u, deriv F u = f' u - f' x - M * (u - x) := fun u => (hFd u).deriv
  have hFx : F x = 0 := by simp [hFdef]
  have hFy : F y ≤ 0 := by
    rcases le_total x y with hxy | hxy
    · have hanti : AntitoneOn F (Ici x) := by
        refine antitoneOn_of_deriv_nonpos (convex_Ici x) hFdiff.continuous.continuousOn
          hFdiff.differentiableOn fun u hu => ?_
        rw [interior_Ici] at hu
        have hux : (0 : ℝ) ≤ u - x := by simp only [mem_Ioi] at hu; linarith
        have hb := hlip u x
        rw [abs_of_nonneg hux] at hb
        have := (le_abs_self (f' u - f' x)).trans hb
        rw [hderiv u]; linarith
      have := hanti self_mem_Ici (mem_Ici.2 hxy) hxy
      linarith [hFx]
    · have hmono : MonotoneOn F (Iic x) := by
        refine monotoneOn_of_deriv_nonneg (convex_Iic x) hFdiff.continuous.continuousOn
          hFdiff.differentiableOn fun u hu => ?_
        rw [interior_Iic] at hu
        have hux : (0 : ℝ) ≤ x - u := by simp only [mem_Iio] at hu; linarith
        have hb := hlip x u
        rw [abs_of_nonneg hux] at hb
        have := (le_abs_self (f' x - f' u)).trans hb
        rw [hderiv u]; linarith
      have := hmono (mem_Iic.2 hxy) self_mem_Iic hxy
      linarith [hFx]
  simp only [hFdef] at hFy
  linarith

/-- **Taylor's theorem with a Lipschitz derivative.** If `f` is differentiable with derivative
`f'` and `f'` is `M`-Lipschitz, then `|f y - f x - (y - x) f' x| ≤ M (y - x)² / 2`. -/
theorem abs_sub_sub_mul_deriv_le {f f' : ℝ → ℝ} (hf : ∀ u, HasDerivAt f (f' u) u) {M : ℝ}
    (hM : 0 ≤ M) (hlip : ∀ u v, |f' u - f' v| ≤ M * |u - v|) (x y : ℝ) :
    |f y - f x - (y - x) * f' x| ≤ M * (y - x) ^ 2 / 2 := by
  have hup := sub_sub_mul_deriv_le hf hlip x y
  have hdn := sub_sub_mul_deriv_le (f := fun u => -f u) (f' := fun u => -f' u)
    (fun u => (hf u).neg)
    (fun u v => by rw [show -f' u - -f' v = -(f' u - f' v) by ring, abs_neg]; exact hlip u v) x y
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-! ### Exchangeable pairs on a finite space

The pair is carried by a finite configuration type `Ω` and a finite auxiliary randomisation
`K`: the first coordinate of the pair is `W ω`, the second is `W' ω k`. Averaging over `K`
alone is conditioning on the configuration. -/

section ExchangeablePair

variable {Ω K : Type*} [Fintype Ω] [Fintype K]

/-- The conditional second moment of the increment, given the configuration: the average of
`(W' ω k - W ω)²` over the auxiliary randomisation only. -/
noncomputable def condSqIncrement (W : Ω → ℝ) (W' : Ω → K → ℝ) (ω : Ω) : ℝ :=
  (Fintype.card K : ℝ)⁻¹ * ∑ k, (W' ω k - W ω) ^ 2

/-- **Antisymmetry kills the average.** If the pair `(W, W')` is exchangeable then the total
sum of any *antisymmetric* function of the pair vanishes. -/
theorem sum_eq_zero_of_exchangeable {W : Ω → ℝ} {W' : Ω → K → ℝ}
    (hexch : ∀ F : ℝ → ℝ → ℝ,
      ∑ ω, ∑ k, F (W ω) (W' ω k) = ∑ ω, ∑ k, F (W' ω k) (W ω))
    (F : ℝ → ℝ → ℝ) (hF : ∀ x y, F y x = -F x y) :
    ∑ ω, ∑ k, F (W ω) (W' ω k) = 0 := by
  have h := hexch F
  have h2 : ∑ ω, ∑ k, F (W' ω k) (W ω) = -∑ ω, ∑ k, F (W ω) (W' ω k) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => hF (W ω) (W' ω k)
  rw [h2] at h
  linarith

/-- **The exchangeable-pair integration-by-parts identity.** For an exchangeable pair
satisfying the linearity condition `∑ₖ (W' ω k − W ω) = -λ |K| W ω`, and *any* function `f`,
$$ 2\lambda |K| \sum_\omega W(\omega) f(W(\omega))
   \;=\; \sum_\omega \sum_k \bigl(W'(\omega,k) - W(\omega)\bigr)
          \bigl(f(W'(\omega,k)) - f(W(\omega))\bigr). $$
This is the exact substitute for integration by parts against the Gaussian density; no
smoothness of `f` is used. -/
theorem sum_stein_pair {W : Ω → ℝ} {W' : Ω → K → ℝ} {lam : ℝ}
    (hexch : ∀ F : ℝ → ℝ → ℝ,
      ∑ ω, ∑ k, F (W ω) (W' ω k) = ∑ ω, ∑ k, F (W' ω k) (W ω))
    (hlin : ∀ ω, ∑ k, (W' ω k - W ω) = -lam * (Fintype.card K : ℝ) * W ω) (f : ℝ → ℝ) :
    2 * lam * (Fintype.card K : ℝ) * ∑ ω, W ω * f (W ω)
      = ∑ ω, ∑ k, (W' ω k - W ω) * (f (W' ω k) - f (W ω)) := by
  -- the antisymmetric choice `F x y = (y - x)(f y + f x)` has vanishing total sum
  have hanti : ∑ ω, ∑ k, (W' ω k - W ω) * (f (W' ω k) + f (W ω)) = 0 :=
    sum_eq_zero_of_exchangeable hexch (fun x y => (y - x) * (f y + f x)) fun x y => by ring
  -- split `f(W') + f(W) = (f(W') - f(W)) + 2 f(W)` and use the linearity condition
  have hsplit : ∀ ω, ∑ k, (W' ω k - W ω) * (f (W' ω k) + f (W ω))
      = (∑ k, (W' ω k - W ω) * (f (W' ω k) - f (W ω)))
        + 2 * f (W ω) * ∑ k, (W' ω k - W ω) := by
    intro ω
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have key : ∑ ω, ((∑ k, (W' ω k - W ω) * (f (W' ω k) - f (W ω)))
      + 2 * f (W ω) * (-lam * (Fintype.card K : ℝ) * W ω)) = 0 := by
    rw [← hanti]
    exact Finset.sum_congr rfl fun ω _ => by rw [hsplit ω, hlin ω]
  rw [Finset.sum_add_distrib] at key
  have h2 : ∑ ω, 2 * f (W ω) * (-lam * (Fintype.card K : ℝ) * W ω)
      = -(2 * lam * (Fintype.card K : ℝ) * ∑ ω, W ω * f (W ω)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun ω _ => by ring
  rw [h2] at key
  linarith

/-- **The abstract exchangeable-pair bound.** Let `(W, W')` be an exchangeable pair on the
finite space `Ω × K` with `𝔼[W' − W ∣ Ω] = -λ W`, and let `f` solve the Stein equation for the
test function `h`, with `|f'| ≤ B₁` and `f'` `B₂`-Lipschitz. Then
$$ \bigl|\mathbb E h(W) - \mathbb E h(Z)\bigr|
   \;\le\; B_1\,\mathbb E\Bigl|1 - \tfrac1{2\lambda}\,\mathbb E[(W'-W)^2 \mid \Omega]\Bigr|
     \;+\; \frac{B_2}{4\lambda}\,\mathbb E\,|W' - W|^3 . $$
The first term is the *variance-regression defect* and the second is the *third-moment*
term; both are pure finite sums here. -/
theorem abs_avg_sub_le [Nonempty Ω] [Nonempty K] {W : Ω → ℝ} {W' : Ω → K → ℝ} {lam : ℝ}
    (hlam : 0 < lam)
    (hexch : ∀ F : ℝ → ℝ → ℝ,
      ∑ ω, ∑ k, F (W ω) (W' ω k) = ∑ ω, ∑ k, F (W' ω k) (W ω))
    (hlin : ∀ ω, ∑ k, (W' ω k - W ω) = -lam * (Fintype.card K : ℝ) * W ω)
    {h f f' : ℝ → ℝ} {c B₁ B₂ : ℝ} (hB₂ : 0 ≤ B₂)
    (hf : ∀ u, HasDerivAt f (f' u) u)
    (hstein : ∀ u, f' u - u * f u = h u - c)
    (hfb : ∀ u, |f' u| ≤ B₁)
    (hflip : ∀ u v, |f' u - f' v| ≤ B₂ * |u - v|) :
    |(Fintype.card Ω : ℝ)⁻¹ * ∑ ω, h (W ω) - c|
      ≤ B₁ * ((Fintype.card Ω : ℝ)⁻¹ *
            ∑ ω, |1 - (2 * lam)⁻¹ * condSqIncrement W W' ω|)
        + (4 * lam)⁻¹ * B₂ * ((Fintype.card Ω : ℝ)⁻¹ * (Fintype.card K : ℝ)⁻¹ *
            ∑ ω, ∑ k, |W' ω k - W ω| ^ 3) := by
  classical
  have hn0 : (0 : ℝ) < (Fintype.card Ω : ℝ) := by exact_mod_cast Fintype.card_pos
  have hk0 : (0 : ℝ) < (Fintype.card K : ℝ) := by exact_mod_cast Fintype.card_pos
  -- the Taylor remainder of `f` along the increment
  set R : Ω → K → ℝ :=
    fun ω k => f (W' ω k) - f (W ω) - (W' ω k - W ω) * f' (W ω) with hRdef
  have hRb : ∀ ω k, |R ω k| ≤ B₂ * (W' ω k - W ω) ^ 2 / 2 := fun ω k =>
    abs_sub_sub_mul_deriv_le hf hB₂ hflip (W ω) (W' ω k)
  -- expand the exchangeable-pair identity to first order
  have hper : ∀ ω, ∑ k, (W' ω k - W ω) * (f (W' ω k) - f (W ω))
      = f' (W ω) * (∑ k, (W' ω k - W ω) ^ 2) + ∑ k, (W' ω k - W ω) * R ω k := by
    intro ω
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hRdef]
    ring
  have hsum : ∑ ω, ∑ k, (W' ω k - W ω) * (f (W' ω k) - f (W ω))
      = (∑ ω, f' (W ω) * (∑ k, (W' ω k - W ω) ^ 2))
        + ∑ ω, ∑ k, (W' ω k - W ω) * R ω k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ω _ => hper ω
  have hpair := (sum_stein_pair hexch hlin f).trans hsum
  set n : ℝ := (Fintype.card Ω : ℝ) with hndef
  set κ : ℝ := (Fintype.card K : ℝ) with hκdef
  have hpos : (0 : ℝ) < 2 * lam * κ := mul_pos (mul_pos (by norm_num) hlam) hk0
  -- solve for the Stein expectation
  have e2 : ∑ ω, W ω * f (W ω)
      = (2 * lam * κ)⁻¹ * ((∑ ω, f' (W ω) * (∑ k, (W' ω k - W ω) ^ 2))
          + ∑ ω, ∑ k, (W' ω k - W ω) * R ω k) := by
    have hc : (2 * lam * κ)⁻¹ * (2 * lam * κ * ∑ ω, W ω * f (W ω))
        = (2 * lam * κ)⁻¹ * ((∑ ω, f' (W ω) * (∑ k, (W' ω k - W ω) ^ 2))
            + ∑ ω, ∑ k, (W' ω k - W ω) * R ω k) := by rw [hpair]
    rwa [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul] at hc
  have e3 : ∑ ω, f' (W ω) * (1 - (2 * lam)⁻¹ * condSqIncrement W W' ω)
      = (∑ ω, f' (W ω))
        - (2 * lam * κ)⁻¹ * ∑ ω, f' (W ω) * (∑ k, (W' ω k - W ω) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [condSqIncrement]
    field_simp
    ring
  have e1 : ∑ ω, (h (W ω) - c) = (∑ ω, f' (W ω)) - ∑ ω, W ω * f (W ω) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ω _ => (hstein (W ω)).symm
  have hmain : ∑ ω, (h (W ω) - c)
      = (∑ ω, f' (W ω) * (1 - (2 * lam)⁻¹ * condSqIncrement W W' ω))
        - (2 * lam * κ)⁻¹ * ∑ ω, ∑ k, (W' ω k - W ω) * R ω k := by
    rw [e1, e2, e3]; ring
  -- the two error terms
  have hA : |∑ ω, f' (W ω) * (1 - (2 * lam)⁻¹ * condSqIncrement W W' ω)|
      ≤ B₁ * ∑ ω, |1 - (2 * lam)⁻¹ * condSqIncrement W W' ω| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ω _ => ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hfb (W ω)) (abs_nonneg _)
  have hT : |∑ ω, ∑ k, (W' ω k - W ω) * R ω k|
      ≤ B₂ / 2 * ∑ ω, ∑ k, |W' ω k - W ω| ^ 3 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ω _ => ?_
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [abs_mul]
    have hsq : (W' ω k - W ω) ^ 2 = |W' ω k - W ω| ^ 2 := (sq_abs _).symm
    have hb := hRb ω k
    rw [hsq] at hb
    calc |W' ω k - W ω| * |R ω k|
        ≤ |W' ω k - W ω| * (B₂ * |W' ω k - W ω| ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = B₂ / 2 * |W' ω k - W ω| ^ 3 := by ring
  -- assemble
  have hEq : n⁻¹ * (∑ ω, h (W ω)) - c = n⁻¹ * ∑ ω, (h (W ω) - c) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hndef]
    field_simp
  rw [hEq, hmain, abs_mul, abs_of_nonneg (inv_nonneg.2 hn0.le)]
  set A : ℝ := ∑ ω, f' (W ω) * (1 - (2 * lam)⁻¹ * condSqIncrement W W' ω) with hAdef
  set T : ℝ := ∑ ω, ∑ k, (W' ω k - W ω) * R ω k with hTdef
  set P : ℝ := ∑ ω, |1 - (2 * lam)⁻¹ * condSqIncrement W W' ω| with hPdef
  set Q : ℝ := ∑ ω, ∑ k, |W' ω k - W ω| ^ 3 with hQdef
  have htri : |A - (2 * lam * κ)⁻¹ * T| ≤ |A| + (2 * lam * κ)⁻¹ * |T| := by
    have h1 := abs_sub_le A 0 ((2 * lam * κ)⁻¹ * T)
    rwa [sub_zero, zero_sub, abs_neg, abs_mul,
      abs_of_nonneg (inv_nonneg.2 hpos.le)] at h1
  have hTb : (2 * lam * κ)⁻¹ * |T| ≤ (2 * lam * κ)⁻¹ * (B₂ / 2 * Q) :=
    mul_le_mul_of_nonneg_left hT (inv_nonneg.2 hpos.le)
  have hfin : n⁻¹ * (B₁ * P + (2 * lam * κ)⁻¹ * (B₂ / 2 * Q))
      = B₁ * (n⁻¹ * P) + (4 * lam)⁻¹ * B₂ * (n⁻¹ * κ⁻¹ * Q) := by
    field_simp
    ring
  calc n⁻¹ * |A - (2 * lam * κ)⁻¹ * T|
      ≤ n⁻¹ * (B₁ * P + (2 * lam * κ)⁻¹ * (B₂ / 2 * Q)) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hn0.le)
        linarith
    _ = _ := hfin

end ExchangeablePair

/-! ### De-smoothing: from Lipschitz test functions to the c.d.f.

The output of Stein's method is a bound on `|𝔼 h(W) − 𝔼 h(Z)|` for *Lipschitz* `h`; the
statement wanted downstream is convergence of `P(W ≤ t)` to `Φ(t)`. Since `Φ` is continuous,
sandwiching the indicator of `Iic t` between the ramps of `ForMathlib/EsseenSmoothing` at
scale `ε` and letting `ε → 0` suffices — no rate is lost that matters. -/

/-- The standard normal density is bounded by `1` (crudely: by `(2π)^{-1/2} < 1`). -/
theorem gaussianPDFReal_std_le_one (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 := by
  have hπ : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)) := by
    have h2 : (1 : ℝ) ≤ 2 * Real.pi * ((1 : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_one, mul_one]
      linarith [Real.pi_gt_three]
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt h2
  have hexp : Real.exp (-(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff, NNReal.coe_one, mul_one,
      show -(x - 0) ^ 2 / 2 = -((x - 0) ^ 2 / 2) by ring, neg_nonpos]
    positivity
  have hinv : (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by linarith : (0 : ℝ) < Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))]
    exact hπ
  rw [gaussianPDFReal]
  calc (Real.sqrt (2 * Real.pi * ((1 : ℝ≥0) : ℝ)))⁻¹ *
        Real.exp (-(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))
      ≤ 1 * 1 := mul_le_mul hinv hexp (Real.exp_pos _).le zero_le_one
    _ = 1 := one_mul 1

/-- **The standard normal c.d.f. is 1-Lipschitz.** In particular it is continuous, which is
all the de-smoothing step needs (a sharper constant `(2π)^{-1/2}` is available but not
useful here). -/
theorem lipschitzWith_cdf_gaussianReal :
    LipschitzWith 1 (cdf (gaussianReal 0 1)) := by
  have hmono : Monotone (cdf (gaussianReal 0 1)) := (cdf (gaussianReal 0 1)).mono
  have hstep : ∀ a b : ℝ, a ≤ b →
      cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a ≤ b - a := by
    intro a b hab
    have hIoc : gaussianReal 0 1 (Ioc a b) ≤ ENNReal.ofReal (b - a) := by
      rw [gaussianReal_apply 0 one_ne_zero]
      calc ∫⁻ x in Ioc a b, gaussianPDF 0 1 x ≤ ∫⁻ _ in Ioc a b, 1 := by
            refine lintegral_mono fun x => ?_
            rw [gaussianPDF, ← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_std_le_one x)
        _ = volume (Ioc a b) := by rw [lintegral_one, Measure.restrict_apply_univ]
        _ = ENNReal.ofReal (b - a) := Real.volume_Ioc
    have hsplit : gaussianReal 0 1 (Iic b) = gaussianReal 0 1 (Iic a)
        + gaussianReal 0 1 (Ioc a b) := by
      rw [← measure_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc,
        Set.Iic_union_Ioc_eq_Iic hab]
    have hfin : gaussianReal 0 1 (Iic a) ≠ ⊤ := measure_ne_top _ _
    rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def, hsplit,
      ENNReal.toReal_add hfin (measure_ne_top _ _), add_sub_cancel_left]
    calc (gaussianReal 0 1 (Ioc a b)).toReal ≤ (ENNReal.ofReal (b - a)).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hIoc
      _ = b - a := ENNReal.toReal_ofReal (by linarith)
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
  rcases le_total x y with hxy | hxy
  · have h1 := hstep x y hxy
    have h2 := hmono hxy
    rw [abs_of_nonpos (by linarith : x - y ≤ 0)]
    constructor <;> linarith
  · have h1 := hstep y x hxy
    have h2 := hmono hxy
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y)]
    constructor <;> linarith

/-- The ramp of width `δ` is `δ⁻¹`-Lipschitz. -/
theorem abs_ramp_sub_ramp_le {u δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    |ramp u δ x - ramp u δ y| ≤ δ⁻¹ * |x - y| := by
  have key : ∀ a b : ℝ, |min 1 (max 0 a) - min 1 (max 0 b)| ≤ |a - b| := by
    intro a b
    refine (abs_min_sub_min_le_max 1 (max 0 a) 1 (max 0 b)).trans ?_
    rw [sub_self, abs_zero]
    refine max_le (abs_nonneg _) ?_
    have h := abs_max_sub_max_le_abs a b 0
    rwa [max_comm a 0, max_comm b 0] at h
  have h := key ((u + δ - x) / δ) ((u + δ - y) / δ)
  have heq : (u + δ - x) / δ - (u + δ - y) / δ = (y - x) / δ := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hδ, abs_sub_comm y x] at h
  rw [show δ⁻¹ * |x - y| = |x - y| / δ from (div_eq_inv_mul _ _).symm]
  simpa only [ramp] using h

/-- **The squeeze against a continuous limit c.d.f.** If, for every `ε > 0`, the quantity
`G i` eventually lies between `Φ(t - ε) - ε` and `Φ(t + ε) + ε`, and `Φ` is continuous at `t`,
then `G i → Φ t`. This is the only form of de-smoothing the combinatorial CLT needs, the limit
c.d.f. being continuous everywhere. -/
theorem tendsto_of_squeeze_continuousAt {ι : Type*} {l : Filter ι} {G : ι → ℝ} {Φ : ℝ → ℝ}
    {t : ℝ} (hΦ : ContinuousAt Φ t)
    (hb : ∀ ε > (0 : ℝ), ∀ᶠ i in l, Φ (t - ε) - ε ≤ G i ∧ G i ≤ Φ (t + ε) + ε) :
    Tendsto G l (𝓝 (Φ t)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ, hδΦ⟩ := Metric.tendsto_nhds_nhds.1 hΦ (η / 2) (by linarith)
  set ε : ℝ := min (δ / 2) (η / 4) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hεη : ε ≤ η / 4 := min_le_right _ _
  have hd1 : dist (Φ (t - ε)) (Φ t) < η / 2 := by
    refine hδΦ ?_
    rw [Real.dist_eq, show t - ε - t = -ε by ring, abs_neg, abs_of_pos hε0]
    linarith
  have hd2 : dist (Φ (t + ε)) (Φ t) < η / 2 := by
    refine hδΦ ?_
    rw [Real.dist_eq, show t + ε - t = ε by ring, abs_of_pos hε0]
    linarith
  rw [Real.dist_eq, abs_lt] at hd1 hd2
  filter_upwards [hb ε hε0] with i hi
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith [hi.1, hd1.1], by linarith [hi.2, hd2.2]⟩

end StatLean.HypothesisTesting
