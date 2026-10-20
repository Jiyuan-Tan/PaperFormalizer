module
public import StatLean.HypothesisTesting.ForMathlib.BerryEsseen
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Foundations for Esseen's smoothing inequality: the sinc integral and the Fejér pair

Esseen's smoothing inequality — the analytic bridge from a characteristic-function estimate to
a Kolmogorov-distance estimate — is classically proved by convolving the distribution-function
difference with the **Fejér kernel**, whose Fourier transform is compactly supported. Two
quantitative facts underlie that route: the normalisation `∫ K_T = 1`, which reduces to the
**sinc integral** `∫_ℝ (sin x / x)² dx = π`, and the **Fejér/triangle Fourier pair**, whose
compact support is what truncates the inversion integral.

Neither the sinc integral nor the Dirichlet integral `∫ sin x/x = π/2` is in Mathlib v4.29.1,
and `ForMathlib/BerryEsseen.lean` originally recorded both facts as hard obstructions. They are
**not** obstructions: this file proves them, by Fourier inversion applied to the triangle
function rather than by contour integration.

## Contents

* `tent` — the triangle function `Λ(x) = max 0 (1 − |x|)`, and its elementary properties;
* `fourier_tentC` — `𝓕 Λ (ξ) = (sin(πξ)/(πξ))²` for `ξ ≠ 0`, computed from an explicit complex
  antiderivative on each of the two linear pieces of `Λ`;
* `integrable_sin_div_sq` — `(sin x/x)²` is integrable, via `sin²x ≤ min(1, x²)` and hence
  `(sin x/x)² ≤ 2/(1 + x²)`;
* `integral_sin_div_sq` — `∫ (sin x/x)² dx = π`, obtained by evaluating Fourier inversion for
  `Λ` at the origin: `∫ 𝓕 Λ = 𝓕⁻ (𝓕 Λ) 0 = Λ 0 = 1`;
* `integral_fejerKernel` — `∫ K_T = 1` for `T > 0`, the Fejér normalisation;
* `fourier_sqSincC` — `𝓕 ((sin(πξ)/(πξ))²) = Λ`, the dual half of the Fejér/triangle pair: the
  transform is **compactly supported**, in `[-1, 1]`;
* `integral_fourier_measure` — Parseval against a finite measure,
  `∫ 𝓕 g dP = ∫ φ_P(−2πξ) g(ξ) dξ`;
* `norm_integral_fourier_sub_le` — the resulting **smoothing inequality in test-function form**:
  `‖∫ 𝓕 g dP − ∫ 𝓕 g dQ‖ ≤ ∫ ‖φ_P − φ_Q‖ ‖g‖`, which for `g` supported in `[−T/2π, T/2π]`
  uses the characteristic functions only on the window `|t| ≤ T`;
* `ramp`, `abs_measure_Iic_sub_le_of_integral_ramp` — **de-smoothing**: a family of continuous
  test functions squeezing the half-line indicator, giving
  `sup|F_P − F_Q| ≤ (ramp discrepancy) + A δ` for an `A`-Lipschitz `F_Q`;
* `trapezoid`, `abs_integral_ramp_sub_le_of_trapezoid` — the reduction of the ramp discrepancy
  to **compactly supported** test functions, using that `P − Q` has total mass zero;
* `exists_fourier_trapezoid` — every trapezoid is `𝓕 g` for an integrable `g` with
  `‖g ξ‖ ≤ min(1/(π|ξ|), 1/(δπ²ξ²))`, the envelope being *independent of the plateau*;
* `abs_measure_Iic_sub_le_charFun` — **Esseen's smoothing inequality at the level of
  distribution functions**.
* `densityCDF`, `charFunDensity`, `abs_measure_Iic_sub_densityCDF_le_charFun` — the same
  inequality with the comparison probability law replaced by a **signed** `L¹` density, which
  is what an Edgeworth approximant is.
* `setIntegral_esseenWeight_tail_le`, `setIntegral_mul_esseenWeight_tail_le`,
  `exists_pow_mul_geometric_le` — the tail of the Esseen weight off a neighbourhood of the
  origin, and the geometric-beats-polynomial bookkeeping that the Cramér tail consumes.

## The Stieltjes inversion is not needed

Earlier notes in this repository recorded the **CDF-level (Stieltjes) Lévy/Esseen inversion** —
the identity expressing `(F − G) ∗ K_T` as a Fourier integral of `(F̂ − Ĝ)/t` — as the single
remaining obstruction to a Kolmogorov-distance bound, on the ground that Mathlib's inversion
theorem is for `L¹` functions while `F − G` is not `L¹`. **That verdict is overturned here.**
The `1/t` weight of Lévy's formula is recovered without any Stieltjes-level inversion, by
running Esseen's argument entirely on test functions:

* the half-line indicator is squeezed between two **ramps**, at a cost `A δ` — this needs only
  monotonicity of `F_P` and Lipschitz continuity of `F_Q` (`ramp`);
* a ramp is not `L¹`, but the difference of two ramps is compactly supported, and since `P − Q`
  has total mass zero the ramp discrepancy is the limit of **trapezoid** discrepancies
  (`abs_integral_ramp_sub_le_of_trapezoid`) — this is where the `1/t` singularity is absorbed;
* a trapezoid is a difference of two **co-centred dilated tents**
  (`trapezoid_eq_tent_combination`), so `fourier_sqSincC` transforms it explicitly, and the
  cancellation `sin²(πw₁ξ) − sin²(πw₂ξ) = sin(π(w₁+w₂)ξ) sin(πδξ)` produces exactly the
  `1/(π|ξ|)` weight, uniformly in the plateau length (`exists_fourier_trapezoid`).

What remains between this file and a Kolmogorov-distance Berry–Esseen or Edgeworth bound is no
longer a Fourier-inversion gap but a **characteristic-function** gap: `BerryEsseen.lean`'s
`norm_charFun_pow_sub_gaussian_le` bounds `‖(φ_F)ⁿ − e^{−nvw²/2}‖` by `n(ρ|w|³/6 + …)` with **no
Gaussian damping factor**, and an undamped bound is not integrable against the `1/|ξ|` weight at
the rate needed. The missing estimate is the damped one,
`‖φ_F(t/(σ√n))ⁿ − e^{−t²/2}‖ ≤ C|t|³ e^{−t²/4}/√n` on `|t| ≤ c√n`. See the status note on
`edgeworth_mean_uniform` in `Bootstrap/Edgeworth.lean`.
-/

open MeasureTheory intervalIntegral
open scoped FourierTransform Real Topology

namespace StatLean.HypothesisTesting

/-! ## The tent function -/

/-- The **tent (triangle) function** `Λ(x) = max 0 (1 − |x|)`, supported on `[-1, 1]`. -/
noncomputable def tent (x : ℝ) : ℝ := max 0 (1 - |x|)

lemma tent_nonneg (x : ℝ) : 0 ≤ tent x := le_max_left _ _

lemma tent_zero : tent 0 = 1 := by simp [tent]

lemma tent_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : tent x = 0 := by
  simp [tent, sub_nonpos.2 hx]

lemma tent_of_mem_Icc_zero_one {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : tent x = 1 - x := by
  have h : |x| = x := abs_of_nonneg hx.1
  simp only [tent, h]
  exact max_eq_right (by linarith [hx.2])

lemma tent_of_mem_Icc_neg_one_zero {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 0) :
    tent x = 1 + x := by
  have h : |x| = -x := abs_of_nonpos hx.2
  simp only [tent, h, sub_neg_eq_add]
  exact max_eq_right (by linarith [hx.1])

lemma continuous_tent : Continuous tent := by
  unfold tent; fun_prop

/-- `Λ` vanishes off `[-1, 1]`. -/
lemma tent_eq_zero_of_notMem {x : ℝ} (hx : x ∉ Set.Icc (-1 : ℝ) 1) : tent x = 0 := by
  refine tent_of_one_le_abs ?_
  rcases not_and_or.1 (fun h => hx ⟨h.1, h.2⟩) with h | h
  · rw [abs_of_nonpos (by linarith [not_le.1 h])]; linarith [not_le.1 h]
  · rw [abs_of_nonneg (by linarith [not_le.1 h])]; linarith [not_le.1 h]

/-! ## An explicit antiderivative for `(c + v) e^{a v}` -/

/-- The interval integral of `(c + v) e^{a v}` in the real variable `v`, computed from the
explicit antiderivative `((c + v)/a − 1/a²) e^{a v}`. -/
private lemma integral_linear_mul_cexp {a : ℂ} (ha : a ≠ 0) (c : ℂ) (p q : ℝ) :
    (∫ v in p..q, (c + (v : ℂ)) * Complex.exp (a * v)) =
      ((c + (q : ℂ)) / a - 1 / a ^ 2) * Complex.exp (a * q) -
        ((c + (p : ℂ)) / a - 1 / a ^ 2) * Complex.exp (a * p) := by
  have hderiv : ∀ v : ℝ, HasDerivAt
      (fun w : ℝ => ((c + (w : ℂ)) / a - 1 / a ^ 2) * Complex.exp (a * w))
      ((c + (v : ℂ)) * Complex.exp (a * v)) v := by
    intro v
    have hb : HasDerivAt (fun w : ℝ => (w : ℂ)) 1 v := by
      simpa using! Complex.ofRealCLM.hasDerivAt (x := v)
    have h1 : HasDerivAt (fun w : ℝ => (c + (w : ℂ)) / a - 1 / a ^ 2) (1 / a) v := by
      simpa using ((hb.const_add c).div_const a).sub_const (1 / a ^ 2)
    have h2 : HasDerivAt (fun w : ℝ => Complex.exp (a * w))
        (Complex.exp (a * v) * a) v := by
      simpa using ((hb.const_mul a).cexp)
    have := h1.mul h2
    convert! this using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun v : ℝ => (c + (v : ℂ)) * Complex.exp (a * v))
      MeasureTheory.volume p q := by
    apply Continuous.intervalIntegrable
    fun_prop
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint

/-! ## The Fourier transform of the tent function -/

/-- The complexification of the tent function. -/
noncomputable def tentC (x : ℝ) : ℂ := (tent x : ℂ)

private lemma continuous_tentC : Continuous tentC :=
  Complex.continuous_ofReal.comp continuous_tent

/-- **The Fourier transform of the triangle function is the squared sinc.**

With Mathlib's `e^{-2πi x ξ}` normalisation, `𝓕 Λ (ξ) = (sin(πξ)/(πξ))²` for `ξ ≠ 0`
(at `ξ = 0` the right-hand side is the junk value `0`, while `𝓕 Λ (0) = ∫ Λ = 1`). -/
theorem fourier_tentC {ξ : ℝ} (hξ : ξ ≠ 0) :
    𝓕 tentC ξ = ((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  obtain ⟨a, ha_def⟩ : ∃ a : ℂ, a = -2 * (π : ℂ) * (ξ : ℂ) * Complex.I := ⟨_, rfl⟩
  have ha : a ≠ 0 := by
    rw [ha_def]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) ?_) Complex.I_ne_zero
    · exact_mod_cast hπ
    · exact_mod_cast hξ
  -- Step 1: rewrite the Fourier integral in the form `∫ Λ(v) e^{a v}`.
  have hstep1 : 𝓕 tentC ξ = ∫ v : ℝ, tentC v * Complex.exp (a * v) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have hexp : ((-2 * π * v * ξ : ℝ) : ℂ) * Complex.I = a * (v : ℂ) := by
      rw [ha_def]; push_cast; ring
    dsimp only
    rw [smul_eq_mul, mul_comm, hexp]
  -- Step 2: the integrand is supported in `[-1, 1]`.
  have hsupp : ∀ v : ℝ, v ∉ Set.Icc (-1 : ℝ) 1 → tentC v * Complex.exp (a * v) = 0 := by
    intro v hv
    simp [tentC, tent_eq_zero_of_notMem hv]
  have hcont : Continuous fun v : ℝ => tentC v * Complex.exp (a * v) := by
    exact continuous_tentC.mul (by fun_prop)
  have hstep2 : (∫ v : ℝ, tentC v * Complex.exp (a * v))
      = ∫ v in (-1 : ℝ)..1, tentC v * Complex.exp (a * v) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp,
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  -- Step 3: split at the origin and evaluate each linear piece.
  have hsplit : (∫ v in (-1 : ℝ)..1, tentC v * Complex.exp (a * v))
      = (∫ v in (-1 : ℝ)..0, tentC v * Complex.exp (a * v)) +
        ∫ v in (0 : ℝ)..1, tentC v * Complex.exp (a * v) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)).symm
  have hleft : (∫ v in (-1 : ℝ)..0, tentC v * Complex.exp (a * v))
      = ∫ v in (-1 : ℝ)..0, ((1 : ℂ) + (v : ℂ)) * Complex.exp (a * v) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hv
    simp [tentC, tent_of_mem_Icc_neg_one_zero hv]
  have hright : (∫ v in (0 : ℝ)..1, tentC v * Complex.exp (a * v))
      = ∫ v in (0 : ℝ)..1, -((((-1 : ℂ)) + (v : ℂ)) * Complex.exp (a * v)) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    rw [tentC, tent_of_mem_Icc_zero_one hv]
    push_cast
    ring
  rw [hstep1, hstep2, hsplit, hleft, hright, intervalIntegral.integral_neg,
    integral_linear_mul_cexp ha, integral_linear_mul_cexp ha]
  -- Step 4: the closed-form algebra.
  have he0 : Complex.exp (a * ((0 : ℝ) : ℂ)) = 1 := by
    norm_num
  have he1 : Complex.exp (a * ((1 : ℝ) : ℂ)) = Complex.exp a := by
    norm_num
  have hem1 : Complex.exp (a * ((-1 : ℝ) : ℂ)) = Complex.exp (-a) := by
    norm_num
  have hcos : Complex.exp a + Complex.exp (-a) = 2 * Complex.cos (2 * (π : ℂ) * (ξ : ℂ)) := by
    have h1 : a = (-(2 * (π : ℂ) * (ξ : ℂ))) * Complex.I := by rw [ha_def]; ring
    rw [h1, show -(-(2 * (π : ℂ) * (ξ : ℂ)) * Complex.I)
        = (2 * (π : ℂ) * (ξ : ℂ)) * Complex.I by ring,
      Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  have ha2 : a ^ 2 = -(4 * (π : ℂ) ^ 2 * (ξ : ℂ) ^ 2) := by
    rw [ha_def]
    rw [mul_pow, mul_pow, mul_pow, Complex.I_sq]
    ring
  have hsin : 2 - 2 * Complex.cos (2 * (π : ℂ) * (ξ : ℂ))
      = 4 * Complex.sin ((π : ℂ) * (ξ : ℂ)) ^ 2 := by
    have : (2 : ℂ) * (π : ℂ) * (ξ : ℂ) = 2 * ((π : ℂ) * (ξ : ℂ)) := by ring
    rw [this, Complex.cos_two_mul', Complex.cos_sq']
    ring
  have hπξ : ((π : ℂ) * (ξ : ℂ)) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast hπ
    · exact_mod_cast hξ
  have hsum : Complex.exp a + Complex.exp (-a) - 2
      = -(4 * Complex.sin ((π : ℂ) * (ξ : ℂ)) ^ 2) := by
    rw [hcos]
    linear_combination -hsin
  have hfinal : (Complex.exp a + Complex.exp (-a) - 2) / a ^ 2
      = ((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) := by
    rw [hsum, ha2]
    push_cast
    field_simp
  rw [he0, he1, hem1, ← hfinal]
  field_simp
  push_cast
  ring

/-! ## Integrability and the value of the sinc integral -/

/-- The elementary bound `(sin x / x)² ≤ 2/(1 + x²)`, from `sin²x ≤ min (1, x²)`. -/
private lemma sq_sin_div_le (x : ℝ) : (Real.sin x / x) ^ 2 ≤ 2 * (1 + x ^ 2)⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · norm_num
  have hx2 : (0 : ℝ) < x ^ 2 := by positivity
  have hpos : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have h1 : Real.sin x ^ 2 ≤ 1 := Real.sin_sq_le_one x
  have h2 : Real.sin x ^ 2 ≤ x ^ 2 := Real.sin_sq_le_sq
  rw [div_pow, ← div_eq_mul_inv, div_le_div_iff₀ hx2 hpos]
  rcases le_or_gt (x ^ 2) 1 with h | h
  · nlinarith [sq_nonneg (Real.sin x)]
  · nlinarith [sq_nonneg (Real.sin x)]

/-- **The squared sinc function is integrable on the line.** -/
theorem integrable_sin_div_sq : Integrable (fun x : ℝ => (Real.sin x / x) ^ 2) := by
  refine Integrable.mono' (g := fun x : ℝ => 2 * (1 + x ^ 2)⁻¹)
    (integrable_inv_one_add_sq.const_mul 2)
    ((Real.continuous_sin.measurable.div measurable_id).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_sin_div_le x

/-- **The sinc integral.** `∫_ℝ (sin x / x)² dx = π`.

The proof evaluates the Fourier inversion formula for the triangle function `Λ` at the
origin: `𝓕 Λ` is the squared sinc `(sin(πξ)/(πξ))²` (`fourier_tentC`), which is integrable,
so `∫ 𝓕 Λ = 𝓕⁻ (𝓕 Λ) 0 = Λ 0 = 1`; rescaling by `π` gives the stated value. -/
theorem integral_sin_div_sq : ∫ x : ℝ, (Real.sin x / x) ^ 2 = π := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  -- the `π`-rescaled squared sinc is integrable, and equals `𝓕 Λ` off the origin
  have hscaled : Integrable (fun ξ : ℝ => (Real.sin (π * ξ) / (π * ξ)) ^ 2) :=
    MeasureTheory.Integrable.comp_mul_left' integrable_sin_div_sq hπ
  have hae : 𝓕 tentC =ᵐ[volume] fun ξ : ℝ => (((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) : ℂ) := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with ξ hξ
    exact fourier_tentC (by simpa using hξ)
  have hFint : Integrable (𝓕 tentC) := hscaled.ofReal.congr hae.symm
  -- Fourier inversion at the origin
  have hcs : HasCompactSupport tentC :=
    HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun x hx => by
      simp [tentC, tent_eq_zero_of_notMem hx]
  have htent : Integrable tentC := continuous_tentC.integrable_of_hasCompactSupport hcs
  have hinv : 𝓕⁻ (𝓕 tentC) (0 : ℝ) = tentC 0 :=
    htent.fourierInv_fourier_eq hFint continuous_tentC.continuousAt
  have h0 : 𝓕⁻ (𝓕 tentC) (0 : ℝ) = ∫ ξ : ℝ, 𝓕 tentC ξ := by
    rw [Real.fourierInv_eq]
    simp
  -- hence the rescaled integral is `1`
  have hone : (∫ ξ : ℝ, (Real.sin (π * ξ) / (π * ξ)) ^ 2) = 1 := by
    have h : (∫ ξ : ℝ, (((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) : ℂ)) = 1 := by
      rw [← integral_congr_ae hae, ← h0, hinv, tentC, tent_zero]
      norm_num
    exact_mod_cast h
  -- undo the rescaling
  have hchange := MeasureTheory.Measure.integral_comp_mul_left
    (fun u : ℝ => (Real.sin u / u) ^ 2) π
  rw [hone, smul_eq_mul, abs_of_pos (inv_pos.2 Real.pi_pos)] at hchange
  have h2 := congrArg (fun z : ℝ => π * z) hchange.symm
  simp only [← mul_assoc, mul_inv_cancel₀ hπ, one_mul, mul_one] at h2
  exact h2

/-! ## The Fejér kernel: total mass and Fourier transform -/

/-- **The Fejér kernel is a probability density**: `∫ K_T = 1` for `T > 0`. This is the
normalisation that Esseen's smoothing argument consumes, and it is exactly the sinc integral
after the substitution `u = T x / 2`. -/
theorem integral_fejerKernel {T : ℝ} (hT : 0 < T) : ∫ x : ℝ, fejerKernel T x = 1 := by
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have h : ∀ x : ℝ,
      fejerKernel T x = (T / (2 * π)) * (Real.sin (T / 2 * x) / (T / 2 * x)) ^ 2 := by
    intro x
    unfold fejerKernel
    rw [show T * x / 2 = T / 2 * x from by ring]
  have hg : (∫ x : ℝ, (Real.sin (T / 2 * x) / (T / 2 * x)) ^ 2)
      = |(T / 2)⁻¹| • ∫ y : ℝ, (Real.sin y / y) ^ 2 :=
    MeasureTheory.Measure.integral_comp_mul_left (fun u : ℝ => (Real.sin u / u) ^ 2) (T / 2)
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul, hg, integral_sin_div_sq, smul_eq_mul,
    abs_of_pos (inv_pos.2 (by linarith : (0 : ℝ) < T / 2))]
  field_simp

/-- The tent function is even. -/
lemma tent_neg (x : ℝ) : tent (-x) = tent x := by simp [tent]

/-- The complexified squared sinc `ξ ↦ (sin(πξ)/(πξ))²`, i.e. `𝓕 Λ` up to the null set `{0}`. -/
noncomputable def sqSincC (ξ : ℝ) : ℂ := (((Real.sin (π * ξ) / (π * ξ)) ^ 2 : ℝ) : ℂ)

private lemma fourier_tentC_ae : 𝓕 tentC =ᵐ[volume] sqSincC := by
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with ξ hξ
  exact fourier_tentC (by simpa using hξ)

private lemma integrable_sqSincC : Integrable sqSincC :=
  (MeasureTheory.Integrable.comp_mul_left' integrable_sin_div_sq Real.pi_ne_zero).ofReal

/-- **The Fourier transform of the squared sinc is the triangle function.**

This is the second half of the classical Fejér/triangle Fourier pair, and it is the fact that
makes Esseen's smoothing work: the transform is **compactly supported**, in `[-1, 1]`. It is
obtained from `fourier_tentC` by Fourier inversion together with the evenness of `Λ`. -/
theorem fourier_sqSincC : 𝓕 sqSincC = tentC := by
  have hcs : HasCompactSupport tentC :=
    HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) fun x hx => by
      simp [tentC, tent_eq_zero_of_notMem hx]
  have htent : Integrable tentC := continuous_tentC.integrable_of_hasCompactSupport hcs
  have hFint : Integrable (𝓕 tentC) := integrable_sqSincC.congr fourier_tentC_ae.symm
  have hinv : 𝓕⁻ (𝓕 tentC) = tentC :=
    continuous_tentC.fourierInv_fourier_eq htent hFint
  funext x
  have h1 : 𝓕 sqSincC x = 𝓕 (𝓕 tentC) x :=
    (Real.fourier_congr_ae fourier_tentC_ae x).symm
  have h2 : 𝓕 (𝓕 tentC) x = 𝓕⁻ (𝓕 tentC) (-x) := by
    rw [Real.fourierInv_eq_fourier_neg, neg_neg]
  rw [h1, h2, hinv]
  simp [tentC, tent_neg]

/-! ## The dilated, translated tent as a Fourier transform -/

/-- The `L¹` function whose Fourier transform is the dilated and translated tent
`y ↦ Λ((y − m)/w)`: a modulated dilation of the squared sinc. -/
private noncomputable def gTent (w m : ℝ) (ξ : ℝ) : ℂ :=
  (w : ℂ) * (Complex.exp (((2 * π * m * ξ : ℝ) : ℂ) * Complex.I) * sqSincC (w * ξ))

private lemma integrable_gTent {w : ℝ} (hw : w ≠ 0) (m : ℝ) : Integrable (gTent w m) := by
  have hbase : Integrable (fun ξ : ℝ => sqSincC (w * ξ)) :=
    MeasureTheory.Integrable.comp_mul_left' integrable_sqSincC hw
  have hmod : Integrable
      (fun ξ : ℝ => Complex.exp (((2 * π * m * ξ : ℝ) : ℂ) * Complex.I) * sqSincC (w * ξ)) := by
    refine hbase.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun ξ => ?_)
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    · rw [Complex.norm_exp_ofReal_mul_I]
  exact hmod.const_mul _

/-- **Fourier transform of a modulated dilation of the squared sinc.**

`𝓕 (ξ ↦ w e^{2πi m ξ} (sin(πwξ)/(πwξ))²) (y) = Λ((y − m)/w)` for `w > 0`: dilation and
translation of the Fejér/triangle pair `fourier_sqSincC`. -/
private lemma fourier_gTent {w : ℝ} (hw : 0 < w) (m y : ℝ) :
    𝓕 (gTent w m) y = tentC ((y - m) / w) := by
  have hw' : (w : ℝ) ≠ 0 := ne_of_gt hw
  set z : ℝ := (y - m) / w with hz
  set G : ℝ → ℂ := fun η : ℝ => Complex.exp (((-2 * π * η * z : ℝ) : ℂ) * Complex.I) * sqSincC η
    with hG
  have hkey : ∀ ξ : ℝ,
      Complex.exp (((-2 * π * ξ * y : ℝ) : ℂ) * Complex.I) • gTent w m ξ = (w : ℂ) * G (w * ξ) := by
    intro ξ
    have hzw : w * z = y - m := by rw [hz]; field_simp
    have hreal : (-2 * π * (w * ξ) * z : ℝ) = (-2 * π * ξ * y : ℝ) + (2 * π * m * ξ : ℝ) := by
      rw [show (-2 * π * (w * ξ) * z : ℝ) = -2 * π * ξ * (w * z) from by ring, hzw]
      ring
    simp only [hG, smul_eq_mul, gTent]
    rw [hreal]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  calc (∫ ξ : ℝ, Complex.exp (((-2 * π * ξ * y : ℝ) : ℂ) * Complex.I) • gTent w m ξ)
      = ∫ ξ : ℝ, (w : ℂ) * G (w * ξ) := integral_congr_ae (Filter.Eventually.of_forall hkey)
    _ = (w : ℂ) * ∫ ξ : ℝ, G (w * ξ) := MeasureTheory.integral_const_mul _ _
    _ = (w : ℂ) * (|w⁻¹| • ∫ η : ℝ, G η) := by
          congr 1
          exact MeasureTheory.Measure.integral_comp_mul_left G w
    _ = ∫ η : ℝ, G η := by
          rw [abs_of_pos (inv_pos.2 hw), Complex.real_smul, ← mul_assoc]
          push_cast
          rw [mul_inv_cancel₀ (by exact_mod_cast hw' : (w : ℂ) ≠ 0), one_mul]
    _ = tentC z := by
          rw [← fourier_sqSincC]
          rw [Real.fourier_real_eq_integral_exp_smul]
          exact integral_congr_ae (Filter.Eventually.of_forall fun η => rfl)

/-! ## The trapezoid as a difference of two dilated tents -/

/-- Rescaling a clipped ramp: for `δ > 0`, `min 1 (max 0 (X/δ)) = δ⁻¹ · min δ (max 0 X)`. -/
private lemma min_one_max_zero_div {δ : ℝ} (hδ : 0 < δ) (X : ℝ) :
    min 1 (max 0 (X / δ)) = (1 / δ) * min δ (max 0 X) := by
  have hpos : (0 : ℝ) ≤ 1 / δ := by positivity
  rw [mul_min_of_nonneg _ _ hpos, mul_max_of_nonneg _ _ hpos]
  simp [div_eq_mul_inv, mul_comm, mul_inv_cancel₀ (ne_of_gt hδ)]

/-- The piecewise-linear core identity behind `trapezoid_eq_tent_combination`, with the
translation `s = y − m` already carried out and the flank width `δ` scaled away. -/
private lemma trapezoid_core (w δ s : ℝ) (hw : 0 ≤ w) (hδ : 0 < δ) :
    min δ (max 0 (w + δ - s)) - min δ (max 0 (-w - s))
      = max 0 (w + δ - |s|) - max 0 (w - |s|) := by
  rcases abs_cases s with ⟨hs, _⟩ | ⟨hs, _⟩ <;> rw [hs] <;>
    simp only [max_def, min_def] <;> split_ifs <;> linarith

/-- A nonnegative multiple of a dilated tent, in clipped form:
`(w/δ) · Λ(t/w) = δ⁻¹ · max 0 (w − |t|)`, valid also at the degenerate width `w = 0`. -/
private lemma smul_tent_eq_max {w δ : ℝ} (hw : 0 ≤ w) (hδ : 0 < δ) (t : ℝ) :
    (w / δ) * tent (t / w) = (1 / δ) * max 0 (w - |t|) := by
  rcases hw.lt_or_eq with hw' | hw'
  · have hne : w ≠ 0 := ne_of_gt hw'
    have habs : |t / w| = |t| / w := by rw [abs_div, abs_of_pos hw']
    have hstep : tent (t / w) = max 0 ((w - |t|) / w) := by
      rw [tent, habs]
      congr 1
      field_simp
    rw [hstep, mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ w / δ),
      mul_max_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / δ)]
    congr 1
    · ring
    · field_simp
  · subst hw'
    simp [max_eq_left (by simpa using abs_nonneg t : (0 : ℝ) - |t| ≤ 0)]

private lemma integrable_gTent' {w : ℝ} (hw : 0 ≤ w) (m : ℝ) : Integrable (gTent w m) := by
  rcases hw.lt_or_eq with h | h
  · exact integrable_gTent (ne_of_gt h) m
  · have hz : gTent w m = fun _ : ℝ => (0 : ℂ) := by funext ξ; simp [gTent, ← h]
    rw [hz]
    exact integrable_zero _ _ _

/-- The scaled tent transform, including the degenerate width `w = 0` (where both sides
vanish). -/
private lemma smul_fourier_gTent {w : ℝ} (hw : 0 ≤ w) (δ m y : ℝ) :
    ((w / δ : ℝ) : ℂ) * 𝓕 (gTent w m) y = (((w / δ) * tent ((y - m) / w) : ℝ) : ℂ) := by
  rcases hw.lt_or_eq with h | h
  · rw [fourier_gTent h m y]
    simp [tentC]
  · have hz : gTent w m = fun _ : ℝ => (0 : ℂ) := by funext ξ; simp [gTent, ← h]
    rw [hz, ← h]
    simp [Real.fourier_real_eq_integral_exp_smul]

/-! ## The smoothing (Parseval) identity against a finite measure -/

/-- **Parseval's identity against a finite measure.** For every integrable `g : ℝ → ℂ`,

`∫ 𝓕 g dP = ∫ charFun P (−2πξ) · g(ξ) dξ`.

This is the analytic core of the smoothing step: it converts an integral of a *smooth test
function* against `P` into an integral of the *characteristic function* of `P` against the
transform. Applied to `P − Q` with a `g` whose transform is compactly supported — such as the
triangle function of `fourier_sqSincC`, rescaled — it bounds a smoothed functional of the
difference using only the characteristic functions on a compact frequency window, which is
exactly what Esseen's argument needs. -/
theorem integral_fourier_measure {P : Measure ℝ} [IsFiniteMeasure P] {g : ℝ → ℂ}
    (hg : Integrable g) :
    ∫ x : ℝ, 𝓕 g x ∂P = ∫ ξ : ℝ, charFun P (-(2 * π * ξ)) * g ξ := by
  have hL : Continuous fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2 := continuous_inner
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp only [LinearMap.flip_apply, innerₗ_apply_apply]
    exact real_inner_comm x y
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := P) (ν := (volume : Measure ℝ)) (L := innerₗ ℝ)
    (f := fun _ : ℝ => (1 : ℂ)) (g := g)
    Real.continuous_fourierChar hL (integrable_const 1) hg
  rw [hflip] at key
  have hchar : ∀ ξ : ℝ,
      VectorFourier.fourierIntegral Real.fourierChar P (innerₗ ℝ) (fun _ : ℝ => (1 : ℂ)) ξ
        = charFun P (-(2 * π * ξ)) := by
    intro ξ
    rw [Real.vector_fourierIntegral_eq_integral_exp_smul, charFun_apply_real]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have hin : ((innerₗ ℝ) v) ξ = v * ξ := by
      simp only [innerₗ_apply_apply]
      change ξ * v = v * ξ
      ring
    dsimp only
    rw [hin, smul_eq_mul, mul_one]
    congr 1
    push_cast
    ring
  have hfour : ∀ x : ℝ,
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) g x = 𝓕 g x :=
    fun _ => rfl
  simp only [hchar, hfour, smul_eq_mul, one_mul] at key
  exact key.symm

/-- **Smoothed comparison of two laws through their characteristic functions.**

`‖∫ 𝓕 g dP − ∫ 𝓕 g dQ‖ ≤ ∫ ‖φ_P(−2πξ) − φ_Q(−2πξ)‖ ‖g ξ‖ dξ`.

If `g` vanishes off `[−T/2π, T/2π]` the right-hand side sees the characteristic functions only
on the window `|t| ≤ T`: this is Esseen's smoothing inequality in its test-function form, the
step that converts a characteristic-function estimate on a compact window into an estimate for
a smoothed functional of `P − Q`. -/
theorem norm_integral_fourier_sub_le {P Q : Measure ℝ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {g : ℝ → ℂ} (hg : Integrable g) :
    ‖(∫ x : ℝ, 𝓕 g x ∂P) - ∫ x : ℝ, 𝓕 g x ∂Q‖
      ≤ ∫ ξ : ℝ, ‖charFun P (-(2 * π * ξ)) - charFun Q (-(2 * π * ξ))‖ * ‖g ξ‖ := by
  have hsm : Measurable fun ξ : ℝ => -(2 * π * ξ) := by fun_prop
  have hP : Integrable (fun ξ : ℝ => charFun P (-(2 * π * ξ)) * g ξ) :=
    hg.bdd_mul (measurable_charFun.comp hsm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => norm_charFun_le_one _)
  have hQ : Integrable (fun ξ : ℝ => charFun Q (-(2 * π * ξ)) * g ξ) :=
    hg.bdd_mul (measurable_charFun.comp hsm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => norm_charFun_le_one _)
  rw [integral_fourier_measure hg, integral_fourier_measure hg, ← integral_sub hP hQ]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans_eq
    (integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_))
  dsimp only
  rw [← sub_mul, norm_mul]

/-! ## De-smoothing: from test functions back to distribution functions

The smoothing inequality above compares two laws through a *test function*. To turn such a
comparison into a bound on the Kolmogorov distance one needs the converse step: a family of
test functions that squeezes the indicator of a half-line tightly enough that the resulting
loss is controlled by the modulus of continuity of the comparison law. The **ramp** below is
that family, and `abs_measure_Iic_sub_le_of_integral_ramp` is the de-smoothing step in its
sharp form: the Kolmogorov distance is bounded by the ramp-test discrepancy plus `A δ`, where
`A` is a Lipschitz constant for the comparison distribution function and `δ` is the ramp
width.

This replaces the classical Fejér-convolution de-smoothing lemma and is strictly more
elementary: no convolution of distribution functions, and no Fejér tail estimate, is needed.
-/

/-- The **ramp** (continuous smoothed indicator) `R_{u,δ}`: it equals `1` on `(-∞, u]`, falls
linearly to `0` across `[u, u + δ]`, and vanishes on `[u + δ, ∞)`. -/
noncomputable def ramp (u δ y : ℝ) : ℝ := min 1 (max 0 ((u + δ - y) / δ))

lemma ramp_nonneg (u δ y : ℝ) : 0 ≤ ramp u δ y :=
  le_min zero_le_one (le_max_left _ _)

lemma ramp_le_one (u δ y : ℝ) : ramp u δ y ≤ 1 := min_le_left _ _

lemma continuous_ramp (u δ : ℝ) : Continuous (ramp u δ) := by
  unfold ramp; fun_prop

/-- The ramp is `1` to the left of its shoulder. -/
lemma ramp_eq_one_of_le {u δ y : ℝ} (hδ : 0 < δ) (hy : y ≤ u) : ramp u δ y = 1 := by
  have h : (1 : ℝ) ≤ (u + δ - y) / δ := (one_le_div hδ).2 (by linarith)
  exact min_eq_left (le_max_of_le_right h)

/-- The ramp vanishes to the right of its foot. -/
lemma ramp_eq_zero_of_le {u δ y : ℝ} (hδ : 0 < δ) (hy : u + δ ≤ y) : ramp u δ y = 0 := by
  have h : (u + δ - y) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  simp [ramp, max_eq_left h]

/-- The ramp is monotone in its shoulder position. -/
lemma ramp_mono_shoulder {v u δ : ℝ} (h : v ≤ u) (hδ : 0 < δ) (y : ℝ) :
    ramp v δ y ≤ ramp u δ y := by
  refine min_le_min le_rfl (max_le_max le_rfl ?_)
  have hinv : (0 : ℝ) ≤ δ⁻¹ := (inv_pos.2 hδ).le
  have hmul : (v + δ - y) * δ⁻¹ ≤ (u + δ - y) * δ⁻¹ :=
    mul_le_mul_of_nonneg_right (by linarith) hinv
  simpa [div_eq_mul_inv] using hmul

lemma integrable_ramp (P : Measure ℝ) [IsFiniteMeasure P] (u δ : ℝ) :
    Integrable (ramp u δ) P :=
  (integrable_const (1 : ℝ)).mono' (continuous_ramp u δ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ramp_nonneg u δ y)]; exact ramp_le_one u δ y)

/-- The half-line indicator is dominated by the ramp sitting on it. -/
lemma measure_Iic_le_integral_ramp (P : Measure ℝ) [IsFiniteMeasure P] {δ : ℝ} (hδ : 0 < δ)
    (u : ℝ) : (P (Set.Iic u)).toReal ≤ ∫ y, ramp u δ y ∂P := by
  have hbase : (∫ y, (Set.Iic u).indicator (fun _ => (1 : ℝ)) y ∂P) = (P (Set.Iic u)).toReal := by
    rw [MeasureTheory.integral_indicator_const _ measurableSet_Iic]
    simp [measureReal_def]
  rw [← hbase]
  refine integral_mono ((integrable_const (1 : ℝ)).indicator measurableSet_Iic)
    (integrable_ramp P u δ) fun y => ?_
  · by_cases hy : y ∈ Set.Iic u
    · rw [Set.indicator_of_mem hy, ramp_eq_one_of_le hδ hy]
    · rw [Set.indicator_of_notMem hy]; exact ramp_nonneg u δ y

/-- The ramp is dominated by the indicator of the half-line ending at its foot. -/
lemma integral_ramp_le_measure_Iic (P : Measure ℝ) [IsFiniteMeasure P] {δ : ℝ} (hδ : 0 < δ)
    (u : ℝ) : (∫ y, ramp u δ y ∂P) ≤ (P (Set.Iic (u + δ))).toReal := by
  have hbase : (∫ y, (Set.Iic (u + δ)).indicator (fun _ => (1 : ℝ)) y ∂P)
      = (P (Set.Iic (u + δ))).toReal := by
    rw [MeasureTheory.integral_indicator_const _ measurableSet_Iic]
    simp [measureReal_def]
  rw [← hbase]
  refine integral_mono (integrable_ramp P u δ)
    ((integrable_const (1 : ℝ)).indicator measurableSet_Iic) fun y => ?_
  · by_cases hy : y ∈ Set.Iic (u + δ)
    · rw [Set.indicator_of_mem hy]; exact ramp_le_one u δ y
    · rw [Set.indicator_of_notMem hy,
        ramp_eq_zero_of_le hδ (le_of_not_ge (by simpa using hy))]

/-- **De-smoothing: the Kolmogorov distance is controlled by the ramp discrepancy.**

If every ramp of width `δ` separates the two laws by at most `E`, and the distribution function
of the comparison law `Q` has Lipschitz constant `A`, then the two distribution functions differ
by at most `E + A δ` at *every* point.

This is the converse half of Esseen's argument — the step that recovers a statement about
distribution functions from a statement about smooth test functions. Combined with
`norm_integral_fourier_sub_le` it reduces a Kolmogorov-distance bound to the single remaining
task of exhibiting each ramp as a Fourier transform of an integrable function. -/
theorem abs_measure_Iic_sub_le_of_integral_ramp {P Q : Measure ℝ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {δ E A : ℝ} (hδ : 0 < δ)
    -- the comparison distribution function is `A`-Lipschitz
    (hQ : ∀ a b : ℝ, a ≤ b →
      (Q (Set.Iic b)).toReal - (Q (Set.Iic a)).toReal ≤ A * (b - a))
    -- every ramp of width `δ` separates the two laws by at most `E`
    (hE : ∀ u : ℝ, |(∫ y, ramp u δ y ∂P) - ∫ y, ramp u δ y ∂Q| ≤ E) (x : ℝ) :
    |(P (Set.Iic x)).toReal - (Q (Set.Iic x)).toReal| ≤ E + A * δ := by
  refine abs_le.2 ⟨?_, ?_⟩
  · -- lower bound: use the ramp whose *foot* sits at `x`
    have h1 : (∫ y, ramp (x - δ) δ y ∂P) ≤ (P (Set.Iic x)).toReal := by
      have := integral_ramp_le_measure_Iic P hδ (x - δ)
      simpa using this
    have h2 : (Q (Set.Iic (x - δ))).toReal ≤ ∫ y, ramp (x - δ) δ y ∂Q :=
      measure_Iic_le_integral_ramp Q hδ (x - δ)
    have h3 := hQ (x - δ) x (by linarith)
    have h4 := abs_le.1 (hE (x - δ))
    simp only [sub_sub_cancel] at h3
    linarith [h4.1, h4.2]
  · -- upper bound: use the ramp whose *shoulder* sits at `x`
    have h1 : (P (Set.Iic x)).toReal ≤ ∫ y, ramp x δ y ∂P :=
      measure_Iic_le_integral_ramp P hδ x
    have h2 : (∫ y, ramp x δ y ∂Q) ≤ (Q (Set.Iic (x + δ))).toReal :=
      integral_ramp_le_measure_Iic Q hδ x
    have h3 := hQ x (x + δ) (by linarith)
    have h4 := abs_le.1 (hE x)
    simp only [add_sub_cancel_left] at h3
    linarith [h4.1, h4.2]

/-! ## From ramps to compactly supported test functions

A ramp is not integrable — it tends to `1` at `-∞` — so it is not in the image of the Fourier
transform of an `L¹` function, and `norm_integral_fourier_sub_le` cannot be applied to it
directly. This is the analytic shadow of the `1/t` singularity in Lévy's inversion formula.
The difference of two ramps *is* compactly supported, however, and since `P − Q` has total mass
zero the ramp discrepancy is the limit of trapezoid discrepancies as the lower shoulder recedes
to `-∞`. The results below make that reduction precise, so that the Kolmogorov distance is
bounded by the discrepancy over the compactly supported, continuous, piecewise-linear
**trapezoids** alone. -/

/-- The distribution function of a probability measure vanishes at `-∞`. -/
lemma tendsto_measure_Iic_atBot (P : Measure ℝ) [IsProbabilityMeasure P] :
    Filter.Tendsto (fun x : ℝ => (P (Set.Iic x)).toReal) Filter.atBot (𝓝 0) := by
  refine (ProbabilityTheory.tendsto_cdf_atBot P).congr fun x => ?_
  rw [ProbabilityTheory.cdf_eq_real]
  rfl

/-- The ramp integral vanishes as the ramp recedes to `-∞`. -/
lemma tendsto_integral_ramp_atBot (P : Measure ℝ) [IsProbabilityMeasure P] {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun v : ℝ => ∫ y, ramp v δ y ∂P) Filter.atBot (𝓝 0) := by
  refine squeeze_zero (fun v => integral_nonneg fun y => ramp_nonneg v δ y)
    (fun v => integral_ramp_le_measure_Iic P hδ v) ?_
  exact (tendsto_measure_Iic_atBot P).comp
    (Filter.tendsto_atBot_add_const_right _ δ Filter.tendsto_id)

/-- The **trapezoid** test function `R_{u,δ} − R_{v,δ}`: continuous, supported in
`[v, u + δ]`, equal to `1` on `[v + δ, u]`, with the two flanks of slope `±1/δ`. -/
noncomputable def trapezoid (v u δ y : ℝ) : ℝ := ramp u δ y - ramp v δ y

lemma trapezoid_nonneg {v u δ : ℝ} (hvu : v ≤ u) (hδ : 0 < δ) (y : ℝ) :
    0 ≤ trapezoid v u δ y :=
  sub_nonneg.2 (ramp_mono_shoulder hvu hδ y)

lemma trapezoid_le_one {v u δ : ℝ} (hvu : v ≤ u) (hδ : 0 < δ) (y : ℝ) :
    trapezoid v u δ y ≤ 1 :=
  sub_le_self _ (ramp_nonneg v δ y) |>.trans (ramp_le_one u δ y)

lemma continuous_trapezoid (v u δ : ℝ) : Continuous (trapezoid v u δ) :=
  (continuous_ramp u δ).sub (continuous_ramp v δ)

/-- The trapezoid is supported in `[v, u + δ]`. -/
lemma trapezoid_eq_zero_of_notMem {v u δ : ℝ} (hδ : 0 < δ) (hvu : v ≤ u) {y : ℝ}
    (hy : y ∉ Set.Icc v (u + δ)) : trapezoid v u δ y = 0 := by
  rcases not_and_or.1 (fun h => hy ⟨h.1, h.2⟩) with h | h
  · have hy' : y < v := not_le.1 h
    rw [trapezoid, ramp_eq_one_of_le hδ (by linarith), ramp_eq_one_of_le hδ hy'.le, sub_self]
  · have hy' : u + δ < y := not_le.1 h
    rw [trapezoid, ramp_eq_zero_of_le hδ hy'.le, ramp_eq_zero_of_le hδ (by linarith), sub_self]

lemma hasCompactSupport_trapezoid {v u δ : ℝ} (hδ : 0 < δ) (hvu : v ≤ u) :
    HasCompactSupport (trapezoid v u δ) :=
  HasCompactSupport.intro (isCompact_Icc (a := v) (b := u + δ))
    fun _ hy => trapezoid_eq_zero_of_notMem hδ hvu hy

/-- **The ramp discrepancy is the limit of trapezoid discrepancies.**

Because `P` and `Q` are probability measures, the mass that the ramp carries off to `-∞`
cancels in the difference, so a uniform bound over trapezoids transfers to the ramp. -/
theorem abs_integral_ramp_sub_le_of_trapezoid {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {u δ E : ℝ} (hδ : 0 < δ)
    (hE : ∀ v : ℝ, v + δ ≤ u →
      |(∫ y, trapezoid v u δ y ∂P) - ∫ y, trapezoid v u δ y ∂Q| ≤ E) :
    |(∫ y, ramp u δ y ∂P) - ∫ y, ramp u δ y ∂Q| ≤ E := by
  have hsplit : ∀ v : ℝ,
      (∫ y, trapezoid v u δ y ∂P) - ∫ y, trapezoid v u δ y ∂Q
        = ((∫ y, ramp u δ y ∂P) - ∫ y, ramp u δ y ∂Q)
          - ((∫ y, ramp v δ y ∂P) - ∫ y, ramp v δ y ∂Q) := by
    intro v
    simp only [trapezoid]
    rw [integral_sub (integrable_ramp P u δ) (integrable_ramp P v δ),
      integral_sub (integrable_ramp Q u δ) (integrable_ramp Q v δ)]
    ring
  have hlim : Filter.Tendsto (fun v : ℝ =>
      |(∫ y, trapezoid v u δ y ∂P) - ∫ y, trapezoid v u δ y ∂Q|) Filter.atBot
      (𝓝 |(∫ y, ramp u δ y ∂P) - ∫ y, ramp u δ y ∂Q|) := by
    simp_rw [hsplit]
    have hmain : Filter.Tendsto (fun v : ℝ =>
        ((∫ y, ramp u δ y ∂P) - ∫ y, ramp u δ y ∂Q)
          - ((∫ y, ramp v δ y ∂P) - ∫ y, ramp v δ y ∂Q)) Filter.atBot
        (𝓝 (((∫ y, ramp u δ y ∂P) - ∫ y, ramp u δ y ∂Q) - (0 - 0))) :=
      tendsto_const_nhds.sub
        ((tendsto_integral_ramp_atBot P hδ).sub (tendsto_integral_ramp_atBot Q hδ))
    simpa using hmain.abs
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_le_atBot (u - δ)] with v hv using hE v (by linarith)

/-- **De-smoothing in trapezoid form: the Kolmogorov distance from compactly supported tests.**

If the two laws are separated by at most `E` on every trapezoid of flank width `δ`, and the
distribution function of `Q` is `A`-Lipschitz, then the two distribution functions differ by at
most `E + A δ` everywhere.

Every hypothesis here is about *continuous, compactly supported* test functions, so this is the
form that `norm_integral_fourier_sub_le` can consume: what remains, to obtain a Kolmogorov
Berry–Esseen or Edgeworth bound, is to exhibit each trapezoid as `𝓕 g` for an integrable `g`
and to estimate `∫ ‖φ_P − φ_Q‖ ‖g‖`. -/
theorem abs_measure_Iic_sub_le_of_trapezoid {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {δ E A : ℝ} (hδ : 0 < δ)
    (hQ : ∀ a b : ℝ, a ≤ b →
      (Q (Set.Iic b)).toReal - (Q (Set.Iic a)).toReal ≤ A * (b - a))
    (hE : ∀ v u : ℝ, v + δ ≤ u →
      |(∫ y, trapezoid v u δ y ∂P) - ∫ y, trapezoid v u δ y ∂Q| ≤ E) (x : ℝ) :
    |(P (Set.Iic x)).toReal - (Q (Set.Iic x)).toReal| ≤ E + A * δ :=
  abs_measure_Iic_sub_le_of_integral_ramp hδ hQ
    (fun u => abs_integral_ramp_sub_le_of_trapezoid hδ fun v hv => hE v u hv) x

/-- **The trapezoid is a difference of two dilated tents.**

With `m = (v + u + δ)/2` the centre, `w₁ = (u − v + δ)/2` the outer half-width and
`w₂ = (u − v − δ)/2` the inner half-width, the trapezoid `R_{u,δ} − R_{v,δ}` equals
`(w₁/δ) Λ((· − m)/w₁) − (w₂/δ) Λ((· − m)/w₂)`. Both tents are centred at `m`, so the Fourier
transforms of the two pieces differ only by a dilation — this is what makes the modulus of the
transform of the trapezoid computable in closed form. -/
private lemma trapezoid_eq_tent_combination {v u δ : ℝ} (hδ : 0 < δ) (hvu : v + δ ≤ u) (y : ℝ) :
    trapezoid v u δ y
      = ((u - v + δ) / 2 / δ) * tent ((y - (v + u + δ) / 2) / ((u - v + δ) / 2))
        - ((u - v - δ) / 2 / δ) * tent ((y - (v + u + δ) / 2) / ((u - v - δ) / 2)) := by
  have hw2 : (0 : ℝ) ≤ (u - v - δ) / 2 := by linarith
  have hw1 : (u - v + δ) / 2 = (u - v - δ) / 2 + δ := by ring
  have hs1 : u + δ - y = (u - v - δ) / 2 + δ - (y - (v + u + δ) / 2) := by ring
  have hs2 : v + δ - y = -((u - v - δ) / 2) - (y - (v + u + δ) / 2) := by ring
  rw [trapezoid, ramp, ramp, hs1, hs2, min_one_max_zero_div hδ, min_one_max_zero_div hδ,
    ← mul_sub, trapezoid_core _ _ _ hw2 hδ, hw1,
    smul_tent_eq_max hw2 hδ, smul_tent_eq_max (by linarith : (0:ℝ) ≤ (u - v - δ) / 2 + δ) hδ]
  ring

/-! ## The trapezoid as a Fourier transform, with the classical `1/|ξ|` envelope -/

/-- **Every trapezoid is the Fourier transform of an integrable function obeying the classical
`1/(π|ξ|)` envelope.**

This is the Fourier half of Esseen's argument for the test functions produced by
`abs_measure_Iic_sub_le_of_trapezoid`. Writing the trapezoid as a difference of two co-centred
dilated tents (`trapezoid_eq_tent_combination`) and transforming each piece
(`fourier_gTent`) gives

`g ξ = e^{2πi m ξ} (sin²(π w₁ ξ) − sin²(π w₂ ξ)) / (δ π² ξ²)`,

whose modulus is `|sin(π(w₁ + w₂)ξ) sin(πδξ)| / (δ π² ξ²) ≤ 1/(π|ξ|)`. The envelope is
**independent of `v` and `u`** — the cancellation between the two tents is exactly what removes
the length of the plateau from the bound. It is the `1/|t|` weight of Lévy's inversion formula,
obtained here without any Stieltjes-level inversion theorem. -/
theorem exists_fourier_trapezoid {v u δ : ℝ} (hδ : 0 < δ) (hvu : v + δ ≤ u) :
    ∃ g : ℝ → ℂ, Integrable g ∧
      (∀ y : ℝ, 𝓕 g y = ((trapezoid v u δ y : ℝ) : ℂ)) ∧
      (∀ ξ : ℝ, ‖g ξ‖ ≤ min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2))) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  set w₁ : ℝ := (u - v + δ) / 2 with hw₁
  set w₂ : ℝ := (u - v - δ) / 2 with hw₂
  set m : ℝ := (v + u + δ) / 2 with hm
  have hw₂0 : 0 ≤ w₂ := by rw [hw₂]; linarith
  have hw₁0 : 0 < w₁ := by rw [hw₁]; linarith
  have hdiff : w₁ - w₂ = δ := by rw [hw₁, hw₂]; ring
  refine ⟨fun ξ => ((w₁ / δ : ℝ) : ℂ) * gTent w₁ m ξ - ((w₂ / δ : ℝ) : ℂ) * gTent w₂ m ξ,
    ((integrable_gTent (ne_of_gt hw₁0) m).const_mul _).sub
      ((integrable_gTent' hw₂0 m).const_mul _), fun y => ?_, fun ξ => ?_⟩
  · -- the Fourier transform is the trapezoid
    have hI : ∀ w : ℝ, 0 ≤ w → Integrable (fun ξ : ℝ =>
        Complex.exp (((-2 * π * ξ * y : ℝ) : ℂ) * Complex.I) * gTent w m ξ) := by
      intro w hw
      refine (integrable_gTent' hw m).bdd_mul (c := 1) ?_
        (Filter.Eventually.of_forall fun ξ => ?_)
      · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
      · rw [Complex.norm_exp_ofReal_mul_I]
    have hsplit : 𝓕 (fun ξ : ℝ => ((w₁ / δ : ℝ) : ℂ) * gTent w₁ m ξ
          - ((w₂ / δ : ℝ) : ℂ) * gTent w₂ m ξ) y
        = ((w₁ / δ : ℝ) : ℂ) * 𝓕 (gTent w₁ m) y - ((w₂ / δ : ℝ) : ℂ) * 𝓕 (gTent w₂ m) y := by
      have expand : ∀ ξ : ℝ, Complex.exp (((-2 * π * ξ * y : ℝ) : ℂ) * Complex.I)
            * (((w₁ / δ : ℝ) : ℂ) * gTent w₁ m ξ - ((w₂ / δ : ℝ) : ℂ) * gTent w₂ m ξ)
          = ((w₁ / δ : ℝ) : ℂ)
              * (Complex.exp (((-2 * π * ξ * y : ℝ) : ℂ) * Complex.I) * gTent w₁ m ξ)
            - ((w₂ / δ : ℝ) : ℂ)
              * (Complex.exp (((-2 * π * ξ * y : ℝ) : ℂ) * Complex.I) * gTent w₂ m ξ) :=
        fun ξ => by ring
      simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
      have hc : ∀ (c : ℂ) (f : ℝ → ℂ), (∫ a : ℝ, c * f a) = c * ∫ a : ℝ, f a := by
        intro c f
        simpa using MeasureTheory.integral_smul c f
      rw [integral_congr_ae (Filter.Eventually.of_forall expand),
        MeasureTheory.integral_sub ((hI w₁ hw₁0.le).const_mul _) ((hI w₂ hw₂0).const_mul _),
        hc, hc]
    rw [hsplit, smul_fourier_gTent hw₁0.le δ m y, smul_fourier_gTent hw₂0 δ m y,
      trapezoid_eq_tent_combination hδ hvu y, ← hw₁, ← hw₂, ← hm]
    push_cast
    ring
  · -- the envelope
    dsimp only
    rcases eq_or_ne ξ 0 with rfl | hξ
    · simp [gTent, sqSincC]
    have hξa : (0 : ℝ) < |ξ| := abs_pos.2 hξ
    have hval : ∀ w : ℝ,
        (w / δ) * (w * ((Real.sin (π * (w * ξ)) / (π * (w * ξ))) ^ 2))
          = Real.sin (π * (w * ξ)) ^ 2 / (δ * π ^ 2 * ξ ^ 2) := by
      intro w
      rcases eq_or_ne w 0 with rfl | hw
      · simp
      · field_simp
        try ring
    set A : ℝ := Real.sin (π * (w₁ * ξ)) ^ 2 / (δ * π ^ 2 * ξ ^ 2) with hAdef
    set B : ℝ := Real.sin (π * (w₂ * ξ)) ^ 2 / (δ * π ^ 2 * ξ ^ 2) with hBdef
    have hg : ((w₁ / δ : ℝ) : ℂ) * gTent w₁ m ξ - ((w₂ / δ : ℝ) : ℂ) * gTent w₂ m ξ
        = Complex.exp (((2 * π * m * ξ : ℝ) : ℂ) * Complex.I) * ((A - B : ℝ) : ℂ) := by
      have e : ∀ w : ℝ, ((w / δ : ℝ) : ℂ) * gTent w m ξ
          = Complex.exp (((2 * π * m * ξ : ℝ) : ℂ) * Complex.I)
              * (((Real.sin (π * (w * ξ)) ^ 2 / (δ * π ^ 2 * ξ ^ 2) : ℝ)) : ℂ) := by
        intro w
        simp only [gTent, sqSincC]
        rw [← hval w]
        push_cast
        ring
      rw [e w₁, e w₂, hAdef, hBdef]
      push_cast
      ring
    rw [hg, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    -- the sine-difference identity and the two elementary bounds
    have hAB : A - B
        = (Real.sin (π * (w₁ * ξ)) ^ 2 - Real.sin (π * (w₂ * ξ)) ^ 2) / (δ * π ^ 2 * ξ ^ 2) := by
      rw [hAdef, hBdef]; ring
    have hsin : Real.sin (π * (w₁ * ξ)) ^ 2 - Real.sin (π * (w₂ * ξ)) ^ 2
        = Real.sin (π * (w₁ * ξ) + π * (w₂ * ξ)) * Real.sin (π * δ * ξ) := by
      have harg : π * (w₁ * ξ) - π * (w₂ * ξ) = π * δ * ξ := by
        rw [← hdiff]; ring
      rw [← harg, Real.sin_add, Real.sin_sub]
      nlinarith [Real.sin_sq_add_cos_sq (π * (w₁ * ξ)), Real.sin_sq_add_cos_sq (π * (w₂ * ξ))]
    have h1 : |Real.sin (π * (w₁ * ξ) + π * (w₂ * ξ))| ≤ 1 := Real.abs_sin_le_one _
    have h2 : |Real.sin (π * δ * ξ)| ≤ π * δ * |ξ| := by
      refine Real.abs_sin_le_abs.trans_eq ?_
      rw [abs_mul, abs_mul, abs_of_pos hπ, abs_of_pos hδ]
    have hprod : |Real.sin (π * (w₁ * ξ) + π * (w₂ * ξ))| * |Real.sin (π * δ * ξ)|
        ≤ π * δ * |ξ| :=
      (mul_le_mul h1 h2 (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    refine le_min ?_ ?_
    · rw [hAB, hsin, abs_div, abs_of_pos (by positivity : (0 : ℝ) < δ * π ^ 2 * ξ ^ 2), abs_mul,
        show ξ ^ 2 = |ξ| ^ 2 from (sq_abs ξ).symm,
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hprod, hξa, hδ, hπ, abs_nonneg (Real.sin (π * δ * ξ))]
    · have hb : |Real.sin (π * (w₁ * ξ)) ^ 2 - Real.sin (π * (w₂ * ξ)) ^ 2| ≤ 1 := by
        rw [abs_le]
        constructor <;>
          nlinarith [Real.sin_sq_le_one (π * (w₁ * ξ)), Real.sin_sq_le_one (π * (w₂ * ξ)),
            sq_nonneg (Real.sin (π * (w₁ * ξ))), sq_nonneg (Real.sin (π * (w₂ * ξ)))]
      rw [hAB, abs_div, abs_of_pos (by positivity : (0 : ℝ) < δ * π ^ 2 * ξ ^ 2),
        div_le_div_iff₀ (by positivity) (by positivity)]
      simpa using mul_le_mul_of_nonneg_right hb
        (by positivity : (0 : ℝ) ≤ δ * π ^ 2 * ξ ^ 2)

/-! ## Esseen's smoothing inequality at the level of distribution functions -/

/-- **Esseen's smoothing inequality, at the level of distribution functions.**

For probability laws `P` and `Q` on the line whose distribution functions are compared, with
`Q` having an `A`-Lipschitz distribution function, and for every flank width `δ > 0`,

`|F_P(x) − F_Q(x)| ≤ ∫ ‖φ_P(−2πξ) − φ_Q(−2πξ)‖ · min(1/(π|ξ|), 1/(δπ²ξ²)) dξ + A δ`

uniformly in `x`. Substituting `t = −2πξ` turns the integral into
`(1/π) ∫ ‖φ_P(t) − φ_Q(t)‖ min(1/|t|, 2/(πδt²)) dt`, which is the classical Esseen bound
`(1/π) ∫ |φ_P − φ_Q|/|t| dt` together with the extra quadratic decay supplied by the flank.

The route is the one assembled in this file and uses **no Stieltjes-level Lévy inversion**:
ramps de-smooth the half-line indicator (`abs_measure_Iic_sub_le_of_integral_ramp`), the mass
that a ramp carries to `−∞` cancels in the difference of two probability laws
(`abs_integral_ramp_sub_le_of_trapezoid`), and the resulting compactly supported trapezoid is a
Fourier transform of an integrable function with the classical `1/|ξ|` envelope
(`exists_fourier_trapezoid`), so `norm_integral_fourier_sub_le` applies to it directly. -/
theorem abs_measure_Iic_sub_le_charFun {P Q : Measure ℝ} [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] {δ A : ℝ} (hδ : 0 < δ)
    -- the comparison distribution function is `A`-Lipschitz
    (hQ : ∀ a b : ℝ, a ≤ b →
      (Q (Set.Iic b)).toReal - (Q (Set.Iic a)).toReal ≤ A * (b - a))
    -- the weighted characteristic-function difference is integrable
    (hint : Integrable (fun ξ : ℝ =>
      ‖charFun P (-(2 * π * ξ)) - charFun Q (-(2 * π * ξ))‖
        * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2))))
    (x : ℝ) :
    |(P (Set.Iic x)).toReal - (Q (Set.Iic x)).toReal|
      ≤ (∫ ξ : ℝ, ‖charFun P (-(2 * π * ξ)) - charFun Q (-(2 * π * ξ))‖
          * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2))) + A * δ := by
  refine abs_measure_Iic_sub_le_of_trapezoid hδ hQ (fun v u hvu => ?_) x
  obtain ⟨g, hgint, hgfour, hgnorm⟩ := exists_fourier_trapezoid hδ hvu
  have hcast : ∀ R : Measure ℝ, IsProbabilityMeasure R →
      (∫ y : ℝ, 𝓕 g y ∂R) = ((∫ y : ℝ, trapezoid v u δ y ∂R : ℝ) : ℂ) := by
    intro R _
    simp_rw [hgfour]
    exact integral_complex_ofReal
  have hnormeq : ‖(∫ y : ℝ, 𝓕 g y ∂P) - ∫ y : ℝ, 𝓕 g y ∂Q‖
      = |(∫ y : ℝ, trapezoid v u δ y ∂P) - ∫ y : ℝ, trapezoid v u δ y ∂Q| := by
    rw [hcast P inferInstance, hcast Q inferInstance, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
  have hbound : ∀ ξ : ℝ,
      ‖charFun P (-(2 * π * ξ)) - charFun Q (-(2 * π * ξ))‖ * ‖g ξ‖
        ≤ ‖charFun P (-(2 * π * ξ)) - charFun Q (-(2 * π * ξ))‖
          * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2)) :=
    fun ξ => mul_le_mul_of_nonneg_left (hgnorm ξ) (norm_nonneg _)
  have hsm : Measurable fun ξ : ℝ => -(2 * π * ξ) := by fun_prop
  have hmeas : AEStronglyMeasurable
      (fun ξ : ℝ => ‖charFun P (-(2 * π * ξ)) - charFun Q (-(2 * π * ξ))‖ * ‖g ξ‖) volume :=
    (((measurable_charFun.comp hsm).sub
      (measurable_charFun.comp hsm)).norm.aestronglyMeasurable).mul
        hgint.aestronglyMeasurable.norm
  have hLint : Integrable (fun ξ : ℝ =>
      ‖charFun P (-(2 * π * ξ)) - charFun Q (-(2 * π * ξ))‖ * ‖g ξ‖) :=
    hint.mono' hmeas (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hbound ξ)
  rw [← hnormeq]
  exact (norm_integral_fourier_sub_le hgint).trans (integral_mono hLint hint hbound)

/-! ## Esseen's smoothing inequality against a signed comparison density

`abs_measure_Iic_sub_le_charFun` compares two *probability measures*. An Edgeworth expansion
does not: its one-term approximant is the signed measure with `L¹` density
`y ↦ σ⁻¹φ(y/σ)(1 + (γ/6)(y³/σ³ − 3y/σ) n^{-1/2})`, which takes both signs. This section reruns
the whole chain with the comparison law replaced by a real integrable density `q`.

Three of the four steps survive verbatim, because they never used positivity:

* the ramp mass at `−∞` vanishes for any `L¹` density (`tendsto_integral_ramp_mul_atBot`), so
  the passage from ramps to compactly supported trapezoids goes through unchanged;
* Parseval against a density is the same multiplication formula as against a finite measure
  (`integral_fourier_density`), and needs only integrability of both factors;
* the Fourier side (`exists_fourier_trapezoid`) does not see the comparison object at all.

The one step that *did* use positivity is the comparison of a ramp integral with a distribution
function, which for a measure is monotonicity. Its correct substitute is the **total-variation
modulus** `∫_{(a,b]} |q| ≤ A (b − a)` — the same constant `A` that a Lipschitz distribution
function supplies, since for a density the two agree up to the sign of `q`. The resulting
de-smoothing loss is `2Aδ` instead of `Aδ`, which is immaterial.

Total mass is **not** assumed. It is not needed for any of the estimates; it enters only
through finiteness of the right-hand side, whose weight `1/(π|ξ|)` is integrable at the origin
only when `φ_P(0) = φ_q(0)`, i.e. when `∫ q = 1`. -/

/-- The **distribution function of a (possibly signed) `L¹` density**. -/
noncomputable def densityCDF (q : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in Set.Iic x, q y

/-- The **characteristic function of a (possibly signed) `L¹` density**. -/
noncomputable def charFunDensity (q : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∫ y : ℝ, Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I) * (q y : ℂ)

variable {q : ℝ → ℝ}

private lemma integrable_ramp_mul (hq : Integrable q) (u δ : ℝ) :
    Integrable (fun y : ℝ => ramp u δ y * q y) :=
  hq.bdd_mul (c := 1) (continuous_ramp u δ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ramp_nonneg u δ y)]; exact ramp_le_one u δ y)

/-- **The ramp integral against a density differs from the distribution function by at most
`A δ`.** For a probability law this is monotonicity; for a signed density the correct substitute
is the total-variation modulus `∫_{(a,b]} |q| ≤ A (b − a)`. -/
theorem abs_integral_ramp_mul_sub_densityCDF_le (hq : Integrable q) {δ A : ℝ} (hδ : 0 < δ)
    (hA : ∀ a b : ℝ, a ≤ b → (∫ y in Set.Ioc a b, |q y|) ≤ A * (b - a)) (u : ℝ) :
    |(∫ y : ℝ, ramp u δ y * q y) - densityCDF q u| ≤ A * δ := by
  have h1 : Integrable (fun y : ℝ => ramp u δ y * q y) := integrable_ramp_mul hq u δ
  have h2 : Integrable (Set.indicator (Set.Iic u) q) := hq.indicator measurableSet_Iic
  have hmaj : Integrable (Set.indicator (Set.Ioc u (u + δ)) fun y => |q y|) :=
    hq.abs.indicator measurableSet_Ioc
  have hd : densityCDF q u = ∫ y : ℝ, Set.indicator (Set.Iic u) q y :=
    (MeasureTheory.integral_indicator measurableSet_Iic).symm
  have hpt : ∀ y : ℝ, ‖ramp u δ y * q y - Set.indicator (Set.Iic u) q y‖
      ≤ Set.indicator (Set.Ioc u (u + δ)) (fun y => |q y|) y := by
    intro y
    rcases le_or_gt y u with hy | hy
    · rw [Set.indicator_of_mem (Set.mem_Iic.2 hy), ramp_eq_one_of_le hδ hy, one_mul, sub_self,
        norm_zero]
      exact Set.indicator_apply_nonneg fun _ => abs_nonneg _
    · rw [Set.indicator_of_notMem (by simpa using hy)]
      rcases le_or_gt y (u + δ) with hy2 | hy2
      · rw [Set.indicator_of_mem (Set.mem_Ioc.2 ⟨hy, hy2⟩), sub_zero, Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (ramp_nonneg u δ y)]
        exact mul_le_of_le_one_left (abs_nonneg _) (ramp_le_one u δ y)
      · rw [Set.indicator_of_notMem (by simp [not_le.2 hy2]),
          ramp_eq_zero_of_le hδ hy2.le, zero_mul, sub_zero, norm_zero]
  calc |(∫ y : ℝ, ramp u δ y * q y) - densityCDF q u|
      = ‖∫ y : ℝ, (ramp u δ y * q y - Set.indicator (Set.Iic u) q y)‖ := by
        rw [integral_sub h1 h2, hd, Real.norm_eq_abs]
    _ ≤ ∫ y : ℝ, Set.indicator (Set.Ioc u (u + δ)) (fun y => |q y|) y :=
        norm_integral_le_of_norm_le hmaj (Filter.Eventually.of_forall hpt)
    _ = ∫ y in Set.Ioc u (u + δ), |q y| := MeasureTheory.integral_indicator measurableSet_Ioc
    _ ≤ A * δ := by simpa using hA u (u + δ) (by linarith)

/-- **De-smoothing against a signed comparison density.** -/
theorem abs_measure_Iic_sub_densityCDF_le_of_integral_ramp {P : Measure ℝ}
    [IsProbabilityMeasure P] (hq : Integrable q) {δ E A : ℝ} (hδ : 0 < δ)
    (hA : ∀ a b : ℝ, a ≤ b → (∫ y in Set.Ioc a b, |q y|) ≤ A * (b - a))
    (hE : ∀ u : ℝ, |(∫ y, ramp u δ y ∂P) - ∫ y : ℝ, ramp u δ y * q y| ≤ E) (x : ℝ) :
    |(P (Set.Iic x)).toReal - densityCDF q x| ≤ E + 2 * (A * δ) := by
  have hAnn : 0 ≤ A * δ := le_trans (abs_nonneg _)
    (abs_integral_ramp_mul_sub_densityCDF_le hq hδ hA 0)
  have hlip : ∀ a b : ℝ, a ≤ b → |densityCDF q b - densityCDF q a| ≤ A * (b - a) := by
    intro a b hab
    have hunion : (∫ y in Set.Iic b, q y)
        = (∫ y in Set.Iic a, q y) + ∫ y in Set.Ioc a b, q y := by
      rw [← setIntegral_union (Set.Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
        hq.integrableOn hq.integrableOn, Set.Iic_union_Ioc_eq_Iic hab]
    have hsub : densityCDF q b - densityCDF q a = ∫ y in Set.Ioc a b, q y := by
      unfold densityCDF
      rw [hunion]
      ring
    rw [hsub]
    calc |∫ y in Set.Ioc a b, q y| ≤ ∫ y in Set.Ioc a b, |q y| := by
          simpa using MeasureTheory.norm_integral_le_integral_norm
            (μ := volume.restrict (Set.Ioc a b)) q
      _ ≤ A * (b - a) := hA a b hab
  refine abs_le.2 ⟨?_, ?_⟩
  · have h1 : (∫ y, ramp (x - δ) δ y ∂P) ≤ (P (Set.Iic x)).toReal := by
      have := integral_ramp_le_measure_Iic P hδ (x - δ)
      simpa using this
    have h2 := abs_le.1 (abs_integral_ramp_mul_sub_densityCDF_le hq hδ hA (x - δ))
    have h3 := abs_le.1 (hlip (x - δ) x (by linarith))
    have h4 := abs_le.1 (hE (x - δ))
    simp only [sub_sub_cancel] at h3
    linarith [h2.1, h3.1, h4.1]
  · have h1 : (P (Set.Iic x)).toReal ≤ ∫ y, ramp x δ y ∂P :=
      measure_Iic_le_integral_ramp P hδ x
    have h2 := abs_le.1 (abs_integral_ramp_mul_sub_densityCDF_le hq hδ hA x)
    have h4 := abs_le.1 (hE x)
    linarith [h2.2, h4.2]

/-- The tail mass of an integrable function vanishes at `−∞`. -/
private lemma tendsto_setIntegral_abs_Iic_atBot (hq : Integrable q) :
    Filter.Tendsto (fun t : ℝ => ∫ y in Set.Iic t, |q y|) Filter.atBot (𝓝 0) := by
  have hinter : (⋂ t : ℝ, Set.Iic (-t)) = (∅ : Set ℝ) := by
    refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
    have := Set.mem_iInter.1 hx (-x + 1)
    simp only [Set.mem_Iic] at this
    linarith
  have hanti : Filter.Tendsto (fun t : ℝ => ∫ y in Set.Iic (-t), |q y|) Filter.atTop
      (𝓝 (∫ y in ⋂ t : ℝ, Set.Iic (-t), |q y|)) :=
    tendsto_setIntegral_of_antitone (fun _ => measurableSet_Iic)
      (fun s t hst => Set.Iic_subset_Iic.2 (by linarith)) ⟨0, hq.abs.integrableOn⟩
  rw [hinter, setIntegral_empty] at hanti
  have := hanti.comp Filter.tendsto_neg_atBot_atTop
  simpa [Function.comp_def] using this

/-- The ramp integral against a density vanishes as the ramp recedes to `−∞`. -/
private lemma tendsto_integral_ramp_mul_atBot (hq : Integrable q) {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun v : ℝ => ∫ y : ℝ, ramp v δ y * q y) Filter.atBot (𝓝 0) := by
  have hbd : ∀ v : ℝ, ‖∫ y : ℝ, ramp v δ y * q y‖ ≤ ∫ y in Set.Iic (v + δ), |q y| := by
    intro v
    have hmaj : Integrable (Set.indicator (Set.Iic (v + δ)) fun y => |q y|) :=
      hq.abs.indicator measurableSet_Iic
    have hpt : ∀ y : ℝ, ‖ramp v δ y * q y‖
        ≤ Set.indicator (Set.Iic (v + δ)) (fun y => |q y|) y := by
      intro y
      rcases le_or_gt y (v + δ) with hy | hy
      · rw [Set.indicator_of_mem (Set.mem_Iic.2 hy), Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (ramp_nonneg v δ y)]
        exact mul_le_of_le_one_left (abs_nonneg _) (ramp_le_one v δ y)
      · rw [Set.indicator_of_notMem (by simpa using hy), ramp_eq_zero_of_le hδ hy.le,
          zero_mul, norm_zero]
    exact (norm_integral_le_of_norm_le hmaj (Filter.Eventually.of_forall hpt)).trans_eq
      (MeasureTheory.integral_indicator measurableSet_Iic)
  refine squeeze_zero_norm hbd ?_
  exact (tendsto_setIntegral_abs_Iic_atBot hq).comp
    (Filter.tendsto_atBot_add_const_right _ δ Filter.tendsto_id)

/-- **The ramp discrepancy against a density is the limit of trapezoid discrepancies.** -/
theorem abs_integral_ramp_mul_sub_le_of_trapezoid {P : Measure ℝ} [IsProbabilityMeasure P]
    (hq : Integrable q) {u δ E : ℝ} (hδ : 0 < δ)
    (hE : ∀ v : ℝ, v + δ ≤ u →
      |(∫ y, trapezoid v u δ y ∂P) - ∫ y : ℝ, trapezoid v u δ y * q y| ≤ E) :
    |(∫ y, ramp u δ y ∂P) - ∫ y : ℝ, ramp u δ y * q y| ≤ E := by
  have hsplit : ∀ v : ℝ,
      (∫ y, trapezoid v u δ y ∂P) - ∫ y : ℝ, trapezoid v u δ y * q y
        = ((∫ y, ramp u δ y ∂P) - ∫ y : ℝ, ramp u δ y * q y)
          - ((∫ y, ramp v δ y ∂P) - ∫ y : ℝ, ramp v δ y * q y) := by
    intro v
    have hP : (∫ y, trapezoid v u δ y ∂P)
        = (∫ y, ramp u δ y ∂P) - ∫ y, ramp v δ y ∂P := by
      simp only [trapezoid]
      exact integral_sub (integrable_ramp P u δ) (integrable_ramp P v δ)
    have hQ : (∫ y : ℝ, trapezoid v u δ y * q y)
        = (∫ y : ℝ, ramp u δ y * q y) - ∫ y : ℝ, ramp v δ y * q y := by
      rw [← integral_sub (integrable_ramp_mul hq u δ) (integrable_ramp_mul hq v δ)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
        simp only [trapezoid]; ring)
    rw [hP, hQ]
    ring
  have hlim : Filter.Tendsto (fun v : ℝ =>
      |(∫ y, trapezoid v u δ y ∂P) - ∫ y : ℝ, trapezoid v u δ y * q y|) Filter.atBot
      (𝓝 |(∫ y, ramp u δ y ∂P) - ∫ y : ℝ, ramp u δ y * q y|) := by
    simp_rw [hsplit]
    have hmain : Filter.Tendsto (fun v : ℝ =>
        ((∫ y, ramp u δ y ∂P) - ∫ y : ℝ, ramp u δ y * q y)
          - ((∫ y, ramp v δ y ∂P) - ∫ y : ℝ, ramp v δ y * q y)) Filter.atBot
        (𝓝 (((∫ y, ramp u δ y ∂P) - ∫ y : ℝ, ramp u δ y * q y) - (0 - 0))) :=
      tendsto_const_nhds.sub
        ((tendsto_integral_ramp_atBot P hδ).sub (tendsto_integral_ramp_mul_atBot hq hδ))
    simpa using hmain.abs
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_le_atBot (u - δ)] with v hv using hE v (by linarith)

/-- The characteristic function of a density is a Fourier transform, up to the `−2π` rescaling
of the frequency variable. -/
private lemma charFunDensity_eq_fourier (q : ℝ → ℝ) (ξ : ℝ) :
    charFunDensity q (-(2 * π * ξ)) = 𝓕 (fun y : ℝ => (q y : ℂ)) ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, charFunDensity]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [smul_eq_mul]
  congr 2
  push_cast
  ring

/-- **Parseval's identity against a signed `L¹` density.** For every integrable `g : ℝ → ℂ`,
`∫ 𝓕 g · q = ∫ φ_q(−2πξ) g(ξ) dξ`. This is `integral_fourier_measure` with the finite
comparison measure replaced by a real `L¹` density; the multiplication formula it rests on
(`VectorFourier.integral_fourierIntegral_smul_eq_flip`) needs only integrability of both
factors, so nothing about positivity or total mass is used. -/
theorem integral_fourier_density (hq : Integrable q) {g : ℝ → ℂ} (hg : Integrable g) :
    (∫ x : ℝ, 𝓕 g x * (q x : ℂ)) = ∫ ξ : ℝ, charFunDensity q (-(2 * π * ξ)) * g ξ := by
  have hL : Continuous fun p : ℝ × ℝ => (innerₗ ℝ) p.1 p.2 := continuous_inner
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp only [LinearMap.flip_apply, innerₗ_apply_apply]
    exact real_inner_comm x y
  have key := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (L := innerₗ ℝ) (f := fun y : ℝ => (q y : ℂ)) (g := g)
    Real.continuous_fourierChar hL hq.ofReal hg
  rw [hflip] at key
  have hchar : ∀ ξ : ℝ,
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ)
          (fun y : ℝ => (q y : ℂ)) ξ
        = charFunDensity q (-(2 * π * ξ)) := fun ξ => (charFunDensity_eq_fourier q ξ).symm
  have hfour : ∀ x : ℝ,
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) g x = 𝓕 g x :=
    fun _ => rfl
  simp only [hchar, hfour, smul_eq_mul] at key
  rw [show (∫ x : ℝ, 𝓕 g x * (q x : ℂ)) = ∫ x : ℝ, (q x : ℂ) * 𝓕 g x from
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)]
  exact key.symm

/-- The characteristic function of an `L¹` density is bounded by its `L¹` norm. -/
private lemma norm_charFunDensity_le (t : ℝ) :
    ‖charFunDensity q t‖ ≤ ∫ y : ℝ, |q y| := by
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans_eq (integral_congr_ae
    (Filter.Eventually.of_forall fun y => ?_))
  have hone : ‖Complex.exp ((t : ℂ) * (y : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp, show (((t : ℂ) * (y : ℂ) * Complex.I)).re = 0 by simp, Real.exp_zero]
  simp only [norm_mul, hone, one_mul, Complex.norm_real, Real.norm_eq_abs]

/-- **Smoothed comparison of a law with a signed density through characteristic functions.** -/
theorem norm_integral_fourier_sub_density_le {P : Measure ℝ} [IsProbabilityMeasure P]
    (hq : Integrable q) {g : ℝ → ℂ} (hg : Integrable g) :
    ‖(∫ x : ℝ, 𝓕 g x ∂P) - ∫ x : ℝ, 𝓕 g x * (q x : ℂ)‖
      ≤ ∫ ξ : ℝ, ‖charFun P (-(2 * π * ξ)) - charFunDensity q (-(2 * π * ξ))‖ * ‖g ξ‖ := by
  have hsm : Measurable fun ξ : ℝ => -(2 * π * ξ) := by fun_prop
  have hcontq : Continuous fun ξ : ℝ => charFunDensity q (-(2 * π * ξ)) := by
    simp only [charFunDensity_eq_fourier]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hq.ofReal
  have hP : Integrable (fun ξ : ℝ => charFun P (-(2 * π * ξ)) * g ξ) :=
    hg.bdd_mul (measurable_charFun.comp hsm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => norm_charFun_le_one _)
  have hQ : Integrable (fun ξ : ℝ => charFunDensity q (-(2 * π * ξ)) * g ξ) :=
    hg.bdd_mul hcontq.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => norm_charFunDensity_le _)
  rw [integral_fourier_measure hg, integral_fourier_density hq hg, ← integral_sub hP hQ]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans_eq
    (integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_))
  dsimp only
  rw [← sub_mul, norm_mul]

/-- **Esseen's smoothing inequality against a signed comparison density.**

For a probability law `P` on the line and a real `L¹` density `q` whose total-variation
modulus obeys `∫_{(a,b]} |q| ≤ A (b − a)`, and for every flank width `δ > 0`,

`|F_P(x) − ∫_{(-∞,x]} q| ≤ ∫ ‖φ_P(−2πξ) − φ_q(−2πξ)‖ · min(1/(π|ξ|), 1/(δπ²ξ²)) dξ + 2Aδ`

uniformly in `x`. This is `abs_measure_Iic_sub_le_charFun` with the comparison *probability
measure* replaced by a **signed** density, which is what an Edgeworth expansion needs: its
one-term approximant `y ↦ σ⁻¹φ(y/σ)(1 + (γ/6)(y³/σ³ − 3y/σ) n^{-1/2})` takes both signs.

Nothing in the route needed positivity: the ramp mass at `−∞` vanishes for any `L¹` density
(`tendsto_integral_ramp_mul_atBot`), the monotonicity step is replaced by the
total-variation modulus (`abs_integral_ramp_mul_sub_densityCDF_le`), and Parseval holds for a
density exactly as for a finite measure (`integral_fourier_density`). Total mass is not
assumed either; it enters only through the finiteness of the right-hand side, since the
weight `1/(π|ξ|)` is integrable at the origin only if `φ_P(0) = φ_q(0)`. -/
theorem abs_measure_Iic_sub_densityCDF_le_charFun {P : Measure ℝ} [IsProbabilityMeasure P]
    (hq : Integrable q) {δ A : ℝ} (hδ : 0 < δ)
    (hA : ∀ a b : ℝ, a ≤ b → (∫ y in Set.Ioc a b, |q y|) ≤ A * (b - a))
    (hint : Integrable (fun ξ : ℝ =>
      ‖charFun P (-(2 * π * ξ)) - charFunDensity q (-(2 * π * ξ))‖
        * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2))))
    (x : ℝ) :
    |(P (Set.Iic x)).toReal - densityCDF q x|
      ≤ (∫ ξ : ℝ, ‖charFun P (-(2 * π * ξ)) - charFunDensity q (-(2 * π * ξ))‖
          * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2))) + 2 * (A * δ) := by
  refine abs_measure_Iic_sub_densityCDF_le_of_integral_ramp hq hδ hA (fun u => ?_) x
  refine abs_integral_ramp_mul_sub_le_of_trapezoid hq hδ (fun v hvu => ?_)
  obtain ⟨g, hgint, hgfour, hgnorm⟩ := exists_fourier_trapezoid hδ hvu
  have hcastP : (∫ y : ℝ, 𝓕 g y ∂P) = ((∫ y : ℝ, trapezoid v u δ y ∂P : ℝ) : ℂ) := by
    simp_rw [hgfour]
    exact integral_complex_ofReal
  have hcastQ : (∫ y : ℝ, 𝓕 g y * (q y : ℂ))
      = ((∫ y : ℝ, trapezoid v u δ y * q y : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hgfour]
    push_cast
    ring
  have hnormeq : ‖(∫ y : ℝ, 𝓕 g y ∂P) - ∫ y : ℝ, 𝓕 g y * (q y : ℂ)‖
      = |(∫ y : ℝ, trapezoid v u δ y ∂P) - ∫ y : ℝ, trapezoid v u δ y * q y| := by
    rw [hcastP, hcastQ, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hbound : ∀ ξ : ℝ,
      ‖charFun P (-(2 * π * ξ)) - charFunDensity q (-(2 * π * ξ))‖ * ‖g ξ‖
        ≤ ‖charFun P (-(2 * π * ξ)) - charFunDensity q (-(2 * π * ξ))‖
          * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2)) :=
    fun ξ => mul_le_mul_of_nonneg_left (hgnorm ξ) (norm_nonneg _)
  have hsm : Measurable fun ξ : ℝ => -(2 * π * ξ) := by fun_prop
  have hcontq : Continuous fun ξ : ℝ => charFunDensity q (-(2 * π * ξ)) := by
    simp only [charFunDensity_eq_fourier]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      continuous_inner hq.ofReal
  have hmeas : AEStronglyMeasurable
      (fun ξ : ℝ => ‖charFun P (-(2 * π * ξ)) - charFunDensity q (-(2 * π * ξ))‖ * ‖g ξ‖)
      volume :=
    (((measurable_charFun.comp hsm).aestronglyMeasurable.sub
      hcontq.aestronglyMeasurable).norm).mul hgint.aestronglyMeasurable.norm
  have hLint : Integrable (fun ξ : ℝ =>
      ‖charFun P (-(2 * π * ξ)) - charFunDensity q (-(2 * π * ξ))‖ * ‖g ξ‖) :=
    hint.mono' hmeas (Filter.Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hbound ξ)
  rw [← hnormeq]
  exact (norm_integral_fourier_sub_density_le hq hgint).trans
    (integral_mono hLint hint hbound)

/-! ## The tail of the Esseen weight, and the Cramér bookkeeping

The last quantitative ingredient of an Edgeworth assembly is the estimate off the window: on
`ρ ≤ |ξ|` the characteristic-function difference is bounded by a constant `c < 1` raised to the
`n`-th power (`exists_bound_lt_one_of_cramer` in `Bootstrap/Edgeworth.lean`), and what has to be
checked is that the *weight* contributes only a power of `n`. It does: off the origin the flank
term `1/(δπ²ξ²)` alone dominates the weight, and `∫_{ρ ≤ |ξ|} ξ⁻² dξ = 2/ρ`, so the whole tail
contributes `2M/(δπ²ρ)`. With the assembly's choices `δ ≍ n⁻¹` and `ρ ≍ √n` that is
`cⁿ · O(n^{3/2})`, and `exists_pow_mul_geometric_le` turns geometric decay against a polynomial
into a bound of any order — in particular `o(n⁻¹)`.

This is item (E3) of the programme recorded on `edgeworth_mean_uniform`, whose analytic content
(`exists_bound_lt_one_of_cramer`) is already proved; what is added here is only the
bookkeeping. -/

private lemma hasDerivAt_neg_inv {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => -t⁻¹) ((x ^ 2)⁻¹) x := by
  simpa using! (hasDerivAt_inv hx).neg

private lemma tendsto_neg_inv_atTop : Filter.Tendsto (fun t : ℝ => -t⁻¹) Filter.atTop (𝓝 0) := by
  have h : Filter.Tendsto (fun t : ℝ => t⁻¹) Filter.atTop (𝓝 0) := tendsto_inv_atTop_zero
  simpa using h.neg

private lemma integrableOn_inv_sq_Ioi {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Set.Ioi ρ) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun x hx => hasDerivAt_neg_inv (by have := hx.out; linarith))
    (fun x _ => by positivity) tendsto_neg_inv_atTop

private lemma integral_inv_sq_Ioi {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ x in Set.Ioi ρ, (x ^ 2)⁻¹) = ρ⁻¹ := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun t : ℝ => -t⁻¹) (g' := fun x : ℝ => (x ^ 2)⁻¹) (a := ρ) (l := 0)
    (fun x hx => hasDerivAt_neg_inv (by have := hx.out; linarith))
    (fun x _ => by positivity) tendsto_neg_inv_atTop
  rw [h]
  ring

private lemma neg_Ioi_eq_Iio (ρ : ℝ) : -Set.Ioi ρ = Set.Iio (-ρ) := by
  ext x
  simp only [Set.mem_neg, Set.mem_Ioi, Set.mem_Iio]
  constructor <;> intro h <;> linarith

private lemma integrableOn_inv_sq_Iic {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Set.Iic (-ρ)) := by
  have h := (integrableOn_inv_sq_Ioi hρ).comp_neg
  rw [neg_Ioi_eq_Iio] at h
  have h2 : IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) (Set.Iio (-ρ)) :=
    h.congr_fun (fun x _ => by beta_reduce; rw [neg_sq]) measurableSet_Iio
  exact h2.congr_set_ae (Iio_ae_eq_Iic (a := (-ρ : ℝ))).symm

private lemma integral_inv_sq_Iic {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ x in Set.Iic (-ρ), (x ^ 2)⁻¹) = ρ⁻¹ := by
  have h : (∫ x in Set.Iic (-ρ), (((-x) ^ 2)⁻¹)) = ∫ x in Set.Ioi (-(-ρ)), (x ^ 2)⁻¹ :=
    integral_comp_neg_Iic (-ρ) (fun x : ℝ => (x ^ 2)⁻¹)
  rw [neg_neg] at h
  rw [← integral_inv_sq_Ioi hρ, ← h]
  exact setIntegral_congr_fun measurableSet_Iic fun x _ => by rw [neg_sq]

private lemma tail_eq_union (ρ : ℝ) :
    {ξ : ℝ | ρ ≤ |ξ|} = Set.Iic (-ρ) ∪ Set.Ici ρ := by
  ext ξ
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iic, Set.mem_Ici, le_abs']

private lemma measurableSet_tail (ρ : ℝ) : MeasurableSet {ξ : ℝ | ρ ≤ |ξ|} := by
  rw [tail_eq_union]
  exact measurableSet_Iic.union measurableSet_Ici

private lemma integrableOn_inv_sq_tail {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun x : ℝ => (x ^ 2)⁻¹) {ξ : ℝ | ρ ≤ |ξ|} := by
  rw [tail_eq_union, integrableOn_union]
  exact ⟨integrableOn_inv_sq_Iic hρ,
    (integrableOn_inv_sq_Ioi hρ).congr_set_ae (Ioi_ae_eq_Ici (a := ρ)).symm⟩

private lemma integral_inv_sq_tail {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ x in {ξ : ℝ | ρ ≤ |ξ|}, (x ^ 2)⁻¹) = 2 * ρ⁻¹ := by
  have hdisj : Disjoint (Set.Iic (-ρ)) (Set.Ici ρ) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : x ≤ -ρ := hx
    have h2 : ρ ≤ x := hx'
    linarith
  rw [tail_eq_union, setIntegral_union hdisj measurableSet_Ici (integrableOn_inv_sq_Iic hρ)
    ((integrableOn_inv_sq_Ioi hρ).congr_set_ae (Ioi_ae_eq_Ici (a := ρ)).symm),
    integral_inv_sq_Iic hρ,
    setIntegral_congr_set (Ioi_ae_eq_Ici (a := ρ)).symm, integral_inv_sq_Ioi hρ]
  ring

/-- The Esseen weight is dominated on the tail by `(δπ²)⁻¹ ξ⁻²`. -/
private lemma esseenWeight_le (δ ξ : ℝ) :
    min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2)) ≤ (δ * π ^ 2)⁻¹ * (ξ ^ 2)⁻¹ := by
  refine (min_le_right _ _).trans_eq ?_
  rw [one_div, mul_inv]

private lemma esseenWeight_nonneg {δ : ℝ} (hδ : 0 < δ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    0 ≤ min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2)) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hξ' : 0 < |ξ| := abs_pos.2 hξ
  have hξ2 : 0 < ξ ^ 2 := by positivity
  exact le_min (by positivity) (by positivity)

/-- **The Esseen weight is integrable off a neighbourhood of the origin.** -/
theorem integrableOn_esseenWeight_tail {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    IntegrableOn (fun ξ : ℝ => min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2)))
      {ξ : ℝ | ρ ≤ |ξ|} := by
  refine Integrable.mono' ((integrableOn_inv_sq_tail hρ).const_mul (δ * π ^ 2)⁻¹)
    (by fun_prop) ?_
  filter_upwards [ae_restrict_mem (measurableSet_tail ρ)] with ξ hξ
  have hξ0 : ξ ≠ 0 := by
    intro h
    rw [h] at hξ
    simp only [abs_zero] at hξ
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (esseenWeight_nonneg hδ hξ0)]
  exact esseenWeight_le δ ξ

/-- **The tail integral of the Esseen weight.** `∫_{ρ ≤ |ξ|} min(1/(π|ξ|), 1/(δπ²ξ²)) dξ
≤ 2/(δπ²ρ)`: off the origin the flank term alone controls the weight, and `∫ ξ⁻²` over the
two tails is `2/ρ`. -/
theorem setIntegral_esseenWeight_tail_le {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ) :
    (∫ ξ in {ξ : ℝ | ρ ≤ |ξ|}, min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2)))
      ≤ 2 / (δ * π ^ 2 * ρ) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  calc (∫ ξ in {ξ : ℝ | ρ ≤ |ξ|}, min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2)))
      ≤ ∫ ξ in {ξ : ℝ | ρ ≤ |ξ|}, (δ * π ^ 2)⁻¹ * (ξ ^ 2)⁻¹ :=
        integral_mono (integrableOn_esseenWeight_tail hδ hρ)
          ((integrableOn_inv_sq_tail hρ).const_mul _) fun ξ => esseenWeight_le δ ξ
    _ = (δ * π ^ 2)⁻¹ * ∫ ξ in {ξ : ℝ | ρ ≤ |ξ|}, (ξ ^ 2)⁻¹ :=
        MeasureTheory.integral_const_mul _ _
    _ = 2 / (δ * π ^ 2 * ρ) := by
        rw [integral_inv_sq_tail hρ]
        field_simp

/-- **The Cramér tail estimate.** If a nonnegative factor is bounded by `M` on the region
`ρ ≤ |ξ|`, its weighted tail integral is at most `2M/(δπ²ρ)`. Applied with
`M = ‖φ_F‖ⁿ ≤ cⁿ` (`exists_bound_lt_one_of_cramer`), `δ ≍ n⁻¹` and `ρ ≍ √n`, the right-hand
side is `cⁿ · O(n^{3/2})`, which by `exists_pow_mul_geometric_le` is `O(n^{-k})` for every
`k` — in particular `o(n⁻¹)`. -/
theorem setIntegral_mul_esseenWeight_tail_le {δ ρ M : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    {f : ℝ → ℝ} (hfm : AEStronglyMeasurable f volume) (hf0 : ∀ ξ, 0 ≤ f ξ)
    (hfb : ∀ ξ, ρ ≤ |ξ| → f ξ ≤ M) :
    (∫ ξ in {ξ : ℝ | ρ ≤ |ξ|}, f ξ * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2)))
      ≤ 2 * M / (δ * π ^ 2 * ρ) := by
  have hw := integrableOn_esseenWeight_tail hδ hρ
  have hMw : IntegrableOn
      (fun ξ : ℝ => M * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2))) {ξ : ℝ | ρ ≤ |ξ|} :=
    hw.const_mul M
  have hle : ∀ᵐ ξ ∂(volume.restrict {ξ : ℝ | ρ ≤ |ξ|}),
      f ξ * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2))
        ≤ M * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2)) := by
    filter_upwards [ae_restrict_mem (measurableSet_tail ρ)] with ξ hξ
    have hξ0 : ξ ≠ 0 := by
      intro h
      rw [h] at hξ
      simp only [abs_zero] at hξ
      linarith
    exact mul_le_mul_of_nonneg_right (hfb ξ hξ) (esseenWeight_nonneg hδ hξ0)
  have hfw : IntegrableOn
      (fun ξ : ℝ => f ξ * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2))) {ξ : ℝ | ρ ≤ |ξ|} := by
    refine Integrable.mono' hMw (hfm.restrict.mul hw.aestronglyMeasurable) ?_
    filter_upwards [hle, ae_restrict_mem (measurableSet_tail ρ)] with ξ hξle hξ
    have hξ0 : ξ ≠ 0 := by
      intro h
      rw [h] at hξ
      simp only [abs_zero] at hξ
      linarith
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hf0 ξ) (esseenWeight_nonneg hδ hξ0))]
    exact hξle
  calc (∫ ξ in {ξ : ℝ | ρ ≤ |ξ|}, f ξ * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2)))
      ≤ ∫ ξ in {ξ : ℝ | ρ ≤ |ξ|}, M * min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2)) :=
        integral_mono_ae hfw hMw hle
    _ = M * ∫ ξ in {ξ : ℝ | ρ ≤ |ξ|}, min (1 / (π * |ξ|)) (1 / (δ * π ^ 2 * ξ ^ 2)) :=
        MeasureTheory.integral_const_mul _ _
    _ ≤ M * (2 / (δ * π ^ 2 * ρ)) := by
        refine mul_le_mul_of_nonneg_left (setIntegral_esseenWeight_tail_le hδ hρ) ?_
        have h0 : (0 : ℝ) ≤ f ρ := hf0 ρ
        have := hfb ρ (by rw [abs_of_pos hρ])
        linarith
    _ = 2 * M / (δ * π ^ 2 * ρ) := by ring

/-- **Geometric decay beats any polynomial.** For `0 ≤ c < 1` and every `k`, the sequence
`n ↦ nᵏ cⁿ` is bounded; this is the bookkeeping that turns the uniform Cramér bound `c < 1` of
`exists_bound_lt_one_of_cramer` into an `o(n⁻¹)` tail. -/
theorem exists_pow_mul_geometric_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n : ℝ) ^ k * c ^ n ≤ C := by
  have habs : |c| < 1 := abs_lt.2 ⟨by linarith, hc1⟩
  have htend := tendsto_pow_const_mul_const_pow_of_abs_lt_one k habs
  obtain ⟨B, hB⟩ := htend.bddAbove_range
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun n => ?_⟩
  exact (hB ⟨n, rfl⟩).trans (le_max_left _ _)

end StatLean.HypothesisTesting
