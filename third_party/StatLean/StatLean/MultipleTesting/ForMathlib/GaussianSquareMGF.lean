module
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

@[expose] public section

/-!
# MGF of a squared standard Gaussian — ForMathlib brick

The moment generating function of `Z²` for `Z ∼ N(0,1)`, the analytic input to identifying the
chi-squared law `∑ᵢ Zᵢ² ∼ χ²ₙ` (Candès, Lecture 2, §2.3):

* `mgf_exp_sq_stdGaussian` — `∫ exp(l·x²) dN(0,1) = (1 − 2l)^{−1/2}` for `l < 1/2`;
* `integrable_exp_sq_stdGaussian` — integrability of `x ↦ exp(l·x²)` under `N(0,1)` for `l < 1/2`.

(This re-derives, as a public `ForMathlib` lemma, the closed form proved `private`ly as
`integral_exp_mul_sq_stdGaussian` in
`HighDimensionalStatistics/CompressedSensing/GaussianChiSquared.lean`
— that file is a concept-layer module and cannot be imported upward.) Consumed by
`ForMathlib/ChiSquared.map_sum_sq_eq_chiSquared`.

Reference: Candès, Lecture 2, §2.3, STAT 300C Notes.
-/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace StatLean.MultipleTesting

/-- Pointwise identity collapsing the standard-Gaussian density times `exp(l x²)` into a
single Gaussian kernel `(√(2π))⁻¹ · exp(−(1/2 − l) x²)`. -/
private lemma gaussianPDF_mul_exp_sq (l x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (l * x ^ 2)
      = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 2 - l) * x ^ 2) := by
  have hpdf : gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * Real.exp (-x ^ 2 / 2) := by
    rw [gaussianPDFReal]
    simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [hpdf, mul_assoc, ← Real.exp_add,
    show -x ^ 2 / 2 + l * x ^ 2 = -(1 / 2 - l) * x ^ 2 from by ring]

/-- **Squared-Gaussian MGF integral**: `∫ exp(l·x²) dN(0,1) = (1 − 2l)^{−1/2}` for `l < 1/2`
(i.e. `(√(1−2l))⁻¹`). The closed form of the χ²₁ moment generating function. -/
theorem mgf_exp_sq_stdGaussian {l : ℝ} (hl : l < 1 / 2) :
    ∫ x, Real.exp (l * x ^ 2) ∂(gaussianReal 0 1) = (Real.sqrt (1 - 2 * l))⁻¹ := by
  have hb : (0 : ℝ) < 1 / 2 - l := by linarith
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have hpt : ∀ x : ℝ, gaussianPDFReal 0 1 x • Real.exp (l * x ^ 2)
      = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 2 - l) * x ^ 2) := by
    intro x; rw [smul_eq_mul]; exact gaussianPDF_mul_exp_sq l x
  simp_rw [hpt]
  rw [integral_const_mul, integral_gaussian (1 / 2 - l)]
  -- (√(2π))⁻¹ · √(π/(1/2 − l)) = (√(1 − 2l))⁻¹
  have hπ : (0 : ℝ) ≤ (2 * π)⁻¹ := by positivity
  rw [← Real.sqrt_inv, ← Real.sqrt_mul hπ,
    show (2 * π)⁻¹ * (π / (1 / 2 - l)) = (1 - 2 * l)⁻¹ from by
      have hpine : π ≠ 0 := Real.pi_ne_zero
      have hbne : (1 / 2 - l) ≠ 0 := hb.ne'
      field_simp,
    Real.sqrt_inv]

/-- **Non-integrability of `x ↦ exp(l·x²)` under `N(0,1)` for `l ≥ 1/2`**: the density times the
integrand reduces to `(√(2π))⁻¹·exp((l−1/2)x²) ≥ (√(2π))⁻¹ > 0`, a positive constant lower bound
on the infinite-measure line. Pins the χ²₁ MGF to `0` outside its convergence half-line. -/
theorem not_integrable_exp_sq_stdGaussian {l : ℝ} (hl : 1 / 2 ≤ l) :
    ¬ Integrable (fun x => Real.exp (l * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  simp only [toReal_gaussianPDF, smul_eq_mul]
  rw [show (fun x => gaussianPDFReal 0 1 x * Real.exp (l * x ^ 2))
        = fun x => (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 2 - l) * x ^ 2) from
      funext (fun x => gaussianPDF_mul_exp_sq l x)]
  intro hInt
  set c : ℝ := (Real.sqrt (2 * π))⁻¹ with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hle : ∀ x : ℝ, ‖(fun _ => c) x‖ ≤ ‖(fun x => c * Real.exp (-(1 / 2 - l) * x ^ 2)) x‖ := by
    intro x
    have hexp1 : (1 : ℝ) ≤ Real.exp (-(1 / 2 - l) * x ^ 2) :=
      Real.one_le_exp (mul_nonneg (by linarith : (0 : ℝ) ≤ -(1 / 2 - l)) (sq_nonneg x))
    have hge : c ≤ c * Real.exp (-(1 / 2 - l) * x ^ 2) := by
      nlinarith [hcpos, hexp1]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hcpos,
      abs_of_pos (by positivity : (0 : ℝ) < c * Real.exp (-(1 / 2 - l) * x ^ 2))]
    exact hge
  have hconst : Integrable (fun _ : ℝ => c) volume :=
    hInt.mono aestronglyMeasurable_const (ae_of_all _ hle)
  rw [integrable_const_iff] at hconst
  rcases hconst with hc0 | hfin
  · exact hcpos.ne' hc0
  · haveI := hfin
    exact absurd Real.volume_univ (measure_ne_top volume Set.univ)

/-- Integrability of `x ↦ exp(l·x²)` under the standard Gaussian, for `l < 1/2`. -/
theorem integrable_exp_sq_stdGaussian {l : ℝ} (hl : l < 1 / 2) :
    Integrable (fun x => Real.exp (l * x ^ 2)) (gaussianReal 0 1) := by
  have hb : (0 : ℝ) < 1 / 2 - l := by linarith
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  simp only [toReal_gaussianPDF, smul_eq_mul]
  have hpt : (fun x => gaussianPDFReal 0 1 x * Real.exp (l * x ^ 2))
      = fun x => (Real.sqrt (2 * π))⁻¹ * Real.exp (-(1 / 2 - l) * x ^ 2) := by
    funext x; exact gaussianPDF_mul_exp_sq l x
  rw [hpt]
  exact (integrable_exp_neg_mul_sq hb).const_mul _

end StatLean.MultipleTesting
