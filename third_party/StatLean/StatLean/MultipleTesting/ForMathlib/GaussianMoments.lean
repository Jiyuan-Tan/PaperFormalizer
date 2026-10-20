module
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-!
# Low-order moments of the standard Gaussian — ForMathlib brick

The first four moments of `Z ∼ N(0,1)` and the variance of `Z²`, the inputs to the chi-squared
test's mean/variance computations (Candès, Lecture 2, §2.3):

* `integral_sq_stdGaussian` — `E[Z²] = 1`;
* `integral_cube_stdGaussian` — `E[Z³] = 0` (odd moment);
* `integral_pow_four_stdGaussian` — `E[Z⁴] = 3`;
* `variance_sq_stdGaussian` — `Var[Z²] = E[(Z²−1)²] = 2`.

Under `H₀` these give `E[∑ Zᵢ²] = n`, `Var[∑ Zᵢ²] = 2n`; the `E[Z³] = 0` / `E[Z⁴] = 3` pair feed
the noncentral `H₁` moments `E[(μ+Z)²] = μ²+1`, `Var[(μ+Z)²] = 4μ²+2` in the assembly file
`ChiSquaredTest/Distribution.lean`. (`E[Z] = 0` is Mathlib's `integral_id_gaussianReal`.)

Theorem-agnostic. The χ²₁ MGF integral `∫ exp(l x²) dN(0,1) = (1−2l)^{−1/2}` and the existing
`∫ x² dN(0,1) = 1` derivation in
`HighDimensionalStatistics/CompressedSensing/GaussianChiSquared.lean` are a style reference (that
file proves the second moment via `variance_fun_id_gaussianReal`).

## Proof routes

* `E[Z²] = 1` — `variance_fun_id_gaussianReal` + `variance_eq_integral` (mean `0`), exactly the
  derivation reused from `GaussianChiSquared.lean`.
* `E[Z³] = 0` — symmetry: `gaussianReal_map_neg` makes `N(0,1)` invariant under `x ↦ −x`, so the odd
  integrand `x³` integrates to its own negative.
* `E[Z⁴] = 3` — the Gaussian moment recursion `E[Z⁴] = 3·E[Z²]` obtained from
  `∫ (x³ φ(x))' = 0` (`integral_eq_zero_of_hasDerivAt_of_integrable`, with `φ'(x) = −x φ(x)` the
  standard-density ODE), evaluated against `E[Z²] = 1`. Integrability of every power against the
  density comes from `memLp_id_gaussianReal'`.
* `Var[Z²] = 2` — expand `(x²−1)² = x⁴ − 2x² + 1` and assemble `3 − 2·1 + 1 = 2`.

Reference: Candès, Lecture 2, §2.3, STAT 300C Notes.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace StatLean.MultipleTesting

/-- `E[Z²] = 1` for `Z ∼ N(0,1)`. -/
theorem integral_sq_stdGaussian : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
  have hv := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := 1)
  rw [variance_eq_integral (by fun_prop)] at hv
  simpa using hv

/-- `E[Z³] = 0` for `Z ∼ N(0,1)` (the third moment vanishes by symmetry). -/
theorem integral_cube_stdGaussian : ∫ x, x ^ 3 ∂(gaussianReal 0 1) = 0 := by
  have hmap : Measure.map (fun x => -x) (gaussianReal 0 1) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg, neg_zero]
  have key : ∫ x, x ^ 3 ∂(gaussianReal 0 1) = -∫ x, x ^ 3 ∂(gaussianReal 0 1) := by
    conv_lhs => rw [← hmap]
    rw [integral_map (measurable_neg).aemeasurable (by fun_prop)]
    have hodd : ∀ x : ℝ, (-x) ^ 3 = -(x ^ 3) := fun x => by ring
    simp_rw [hodd]
    rw [integral_neg]
  linarith

/-- Integrability of every power `x ↦ xᵏ` against the standard Gaussian, read off from the fact
that `id` lies in every `Lᵖ` space (`memLp_id_gaussianReal'`). -/
private lemma integrable_pow_stdGaussian (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; simp
  have h : Integrable (fun x : ℝ => ‖id x‖ ^ k) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' (μ := 0) (v := 1) (k : ℝ≥0∞)
      (ENNReal.natCast_ne_top k)).integrable_norm_pow hk0.ne'
  refine h.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp [id, Real.norm_eq_abs]

/-- Integrability over Lebesgue measure of `x ↦ xᵏ · exp(−x²/2)`, obtained from
`integrable_pow_stdGaussian` by unfolding the standard-Gaussian density. -/
private lemma integrable_pow_mul_exp_half (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-x ^ 2 / 2)) := by
  have hN := integrable_pow_stdGaussian k
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
        (ae_of_all _ (fun _ => gaussianPDF_lt_top))] at hN
  simp only [toReal_gaussianPDF, smul_eq_mul] at hN
  have hconv : (fun x : ℝ => x ^ k * Real.exp (-x ^ 2 / 2))
      = fun x => Real.sqrt (2 * Real.pi) * (gaussianPDFReal 0 1 x * x ^ k) := by
    funext x
    have hpdf : gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
      rw [gaussianPDFReal]; simp only [NNReal.coe_one, mul_one, sub_zero]
    have hs : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    rw [hpdf,
      show Real.sqrt (2 * Real.pi) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * x ^ k)
        = (Real.sqrt (2 * Real.pi) * (Real.sqrt (2 * Real.pi))⁻¹) * (Real.exp (-x ^ 2 / 2) * x ^ k)
        from by ring,
      mul_inv_cancel₀ hs, one_mul]
    exact mul_comm _ _
  rw [hconv]
  exact hN.const_mul _

/-- The standard Gaussian moment recursion at `n = 4`: `∫ x⁴ · exp(−x²/2) = 3 · ∫ x² · exp(−x²/2)`,
proved from `∫ (x³ exp(−x²/2))' = 0` using `exp(−x²/2)' = −x · exp(−x²/2)`. -/
private lemma integral_pow_four_mul_exp_half :
    ∫ x : ℝ, x ^ 4 * Real.exp (-x ^ 2 / 2)
      = 3 * ∫ x : ℝ, x ^ 2 * Real.exp (-x ^ 2 / 2) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y => y ^ 3 * Real.exp (-y ^ 2 / 2))
      (3 * (x ^ 2 * Real.exp (-x ^ 2 / 2)) - x ^ 4 * Real.exp (-x ^ 2 / 2)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
      simpa using hasDerivAt_pow 3 x
    have hu : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
      have h : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-(2 * x) / 2) x := by
        simpa using ((hasDerivAt_pow 2 x).neg).div_const 2
      rwa [show -(2 * x) / 2 = -x from by ring] at h
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / 2))
        (Real.exp (-x ^ 2 / 2) * (-x)) x := by
      simpa [Function.comp] using! (Real.hasDerivAt_exp (-x ^ 2 / 2)).comp x hu
    convert! h1.mul h2 using 1
    ring
  have hf : Integrable (fun x : ℝ => x ^ 3 * Real.exp (-x ^ 2 / 2)) :=
    integrable_pow_mul_exp_half 3
  have hf2 : Integrable (fun x : ℝ => x ^ 2 * Real.exp (-x ^ 2 / 2)) :=
    integrable_pow_mul_exp_half 2
  have hf4 : Integrable (fun x : ℝ => x ^ 4 * Real.exp (-x ^ 2 / 2)) :=
    integrable_pow_mul_exp_half 4
  have hf' : Integrable (fun x : ℝ =>
      3 * (x ^ 2 * Real.exp (-x ^ 2 / 2)) - x ^ 4 * Real.exp (-x ^ 2 / 2)) :=
    (hf2.const_mul 3).sub hf4
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hf' hf
  rw [integral_sub (hf2.const_mul 3) hf4, integral_const_mul] at hzero
  linarith

/-- The fourth-moment recursion transported to the Gaussian measure:
`∫ x⁴ ∂N(0,1) = 3 · ∫ x² ∂N(0,1)`. -/
private lemma integral_pow_four_eq_three_mul_sq :
    ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 * ∫ x, x ^ 2 ∂(gaussianReal 0 1) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
      integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  have hpt : ∀ (k : ℕ) (x : ℝ), gaussianPDFReal 0 1 x * x ^ k
      = (Real.sqrt (2 * Real.pi))⁻¹ * (x ^ k * Real.exp (-x ^ 2 / 2)) := by
    intro k x
    have hpdf : gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
      rw [gaussianPDFReal]; simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [hpdf]; ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_const_mul, integral_pow_four_mul_exp_half]
  ring

/-- `E[Z⁴] = 3` for `Z ∼ N(0,1)`. -/
theorem integral_pow_four_stdGaussian : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  rw [integral_pow_four_eq_three_mul_sq, integral_sq_stdGaussian]; norm_num

/-- `Var[Z²] = 2` for `Z ∼ N(0,1)`, written as the central second moment
`E[(Z²−1)²] = E[Z⁴] − 2·E[Z²] + 1 = 2`. -/
theorem variance_sq_stdGaussian : ∫ x, (x ^ 2 - 1) ^ 2 ∂(gaussianReal 0 1) = 2 := by
  have h4 : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := integrable_pow_stdGaussian 4
  have h2 : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := integrable_pow_stdGaussian 2
  have hsub : Integrable (fun x : ℝ => x ^ 4 - 2 * x ^ 2) (gaussianReal 0 1) :=
    h4.sub (h2.const_mul 2)
  have hrw : ∫ x, (x ^ 2 - 1) ^ 2 ∂(gaussianReal 0 1)
      = ∫ x, (x ^ 4 - 2 * x ^ 2 + 1) ∂(gaussianReal 0 1) := by
    apply integral_congr_ae; filter_upwards with x; ring
  rw [hrw, integral_add hsub (integrable_const 1), integral_sub h4 (h2.const_mul 2),
      integral_const_mul, integral_pow_four_stdGaussian, integral_sq_stdGaussian, integral_const]
  norm_num [measure_univ]

end StatLean.MultipleTesting
