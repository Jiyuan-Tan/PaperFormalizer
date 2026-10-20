module
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.InformationTheory.KullbackLeibler.Basic

@[expose] public section

/-!
# Kullback–Leibler divergence between equal-variance Gaussians

For two real Gaussian distributions with the same variance $\sigma^2 > 0$ and means $m_1, m_2$,
the Kullback–Leibler divergence is
$$
  D\bigl(\mathcal{N}(m_1, \sigma^2)\,\big\|\,\mathcal{N}(m_2, \sigma^2)\bigr)
    = \frac{(m_1 - m_2)^2}{2\sigma^2}.
$$
This is the equal-covariance case of the general multivariate formula
$D\bigl(\mathcal{N}(\mu_1, \Sigma) \,\|\, \mathcal{N}(\mu_2, \Sigma)\bigr)
  = \tfrac12 \langle \mu_1 - \mu_2, \Sigma^{-1}(\mu_1 - \mu_2)\rangle$,
in which only the mean-shift term survives. It is the divergence input to the Gaussian-location
and linear-regression minimax lower-bound examples (Examples 15.4, 15.14, 15.16). The Lean
statement is stated for a nonzero variance `v ≠ 0` and uses `ENNReal.ofReal` to land in the
extended nonnegative reals that Mathlib's `klDiv` returns.

**Reference.** M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.6, Exercise 15.13.

**Proof formalization notes.** The argument computes the divergence from first principles rather
than invoking a packaged Gaussian-KL lemma (Mathlib has none). Steps:

* `log_gaussianPDFReal` splits the log-density into the mean-independent normalising constant
  `-log √(2πv)` and the quadratic exponent `-(x − m)²/(2v)`.
* Absolute continuity `𝒩(m₁, v) ≪ 𝒩(m₂, v)` is obtained through the common dominating Lebesgue
  measure, so `klDiv` reduces (via `klDiv_of_ac_of_integrable`) to the integral of the
  log-likelihood ratio.
* The log-likelihood ratio equals, `𝒩(m₁, v)`-almost everywhere, the affine surrogate
  `F(x) = ((x − m₂)² − (x − m₁)²) / (2v)`: the equal-variance assumption cancels the quadratic
  normalising constants, leaving a function linear in `x`.
* Affineness gives both integrability (`IsGaussian.integrable_fun_id`) and the value
  `∫ F d𝒩(m₁, v) = (m₁ − m₂)²/(2v)`, using `∫ x d𝒩(m₁, v) = m₁`.

The book's constant is reproduced exactly; the only deviation from the book statement is the
`ENNReal.ofReal` wrapper and the explicit `v ≠ 0` hypothesis, both Lean-side bookkeeping.

**Bibliographic comments.** The closed-form KL divergence between Gaussian laws is folklore with
no single seminal origin; the Kullback–Leibler divergence itself was introduced in S. Kullback and
R. A. Leibler, "On Information and Sufficiency", *Annals of Mathematical Statistics* **22** (1951),
no. 1, 79–86, and the Gaussian special case is a standard exercise (here Wainwright, Exercise
15.13). No research-paper theorem number is attached because the formula is textbook material.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace StatLean.Minimaxity

/-- Logarithm of the Gaussian density splits into the (mean-independent) normalising constant and
the quadratic exponent: `log p_{m,v}(x) = -log √(2πv) − (x−m)²/(2v)`. -/
private lemma log_gaussianPDFReal (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    Real.log (gaussianPDFReal m v x)
      = - Real.log (Real.sqrt (2 * Real.pi * v)) - (x - m) ^ 2 / (2 * (v : ℝ)) := by
  have hv' : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hsqrt : Real.sqrt (2 * Real.pi * v) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.pi * v := by positivity
    exact (Real.sqrt_pos.mpr this).ne'
  simp only [gaussianPDFReal]
  rw [Real.log_mul (inv_ne_zero hsqrt) (Real.exp_ne_zero _), Real.log_inv, Real.log_exp]
  ring

/-- **KL divergence between equal-variance real Gaussians** (Wainwright Exercise 15.13, equal-
covariance case): `D(𝒩(m₁, σ²) ‖ 𝒩(m₂, σ²)) = (m₁ − m₂)² / (2σ²)`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.6, Exercise 15.13. -/
theorem klDiv_gaussianReal (m₁ m₂ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    klDiv (gaussianReal m₁ v) (gaussianReal m₂ v)
      = ENNReal.ofReal ((m₁ - m₂) ^ 2 / (2 * (v : ℝ))) := by
  have hv' : (0 : ℝ) < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hvne : (v : ℝ) ≠ 0 := hv'.ne'
  -- absolute continuity `𝒩(m₁,v) ≪ 𝒩(m₂,v)` via the common dominating Lebesgue measure
  have hac : gaussianReal m₁ v ≪ gaussianReal m₂ v :=
    (gaussianReal_absolutelyContinuous m₁ hv).trans (gaussianReal_absolutelyContinuous' m₂ hv)
  -- the affine surrogate for the log-likelihood ratio
  set F : ℝ → ℝ := fun x => ((x - m₂) ^ 2 - (x - m₁) ^ 2) / (2 * (v : ℝ)) with hF_def
  -- `llr =ᵐ[𝒩(m₁,v)] F`
  have hllr : llr (gaussianReal m₁ v) (gaussianReal m₂ v) =ᵐ[gaussianReal m₁ v] F := by
    -- rnDeriv against Lebesgue
    have hrn_vol : (gaussianReal m₁ v).rnDeriv (gaussianReal m₂ v) =ᵐ[volume]
        fun x => (gaussianPDF m₂ v x)⁻¹ * gaussianPDF m₁ v x := by
      have h1 := Measure.rnDeriv_withDensity_right (gaussianReal m₁ v) volume
        (f := gaussianPDF m₂ v) (measurable_gaussianPDF m₂ v).aemeasurable
        (ae_of_all _ fun x => (gaussianPDF_pos m₂ hv x).ne')
        (ae_of_all _ fun _ => gaussianPDF_ne_top)
      rw [← gaussianReal_of_var_ne_zero m₂ hv] at h1
      filter_upwards [h1, rnDeriv_gaussianReal m₁ v] with x hx hx1
      rw [hx, hx1]
    have hrn : (gaussianReal m₁ v).rnDeriv (gaussianReal m₂ v) =ᵐ[gaussianReal m₁ v]
        fun x => (gaussianPDF m₂ v x)⁻¹ * gaussianPDF m₁ v x :=
      (gaussianReal_absolutelyContinuous m₁ hv).ae_eq hrn_vol
    filter_upwards [hrn] with x hx
    simp only [llr]
    rw [hx, ENNReal.toReal_mul, ENNReal.toReal_inv, toReal_gaussianPDF, toReal_gaussianPDF,
      Real.log_mul (inv_ne_zero (gaussianPDFReal_pos m₂ v x hv).ne')
        (gaussianPDFReal_pos m₁ v x hv).ne', Real.log_inv,
      log_gaussianPDFReal m₁ v hv, log_gaussianPDFReal m₂ v hv, hF_def]
    ring
  -- `F` is integrable against `𝒩(m₁,v)` (it is affine, the quadratic term cancels)
  have hFint : Integrable F (gaussianReal m₁ v) := by
    have key : F = fun x => ((m₁ - m₂) / (v : ℝ)) * x + (m₂ ^ 2 - m₁ ^ 2) / (2 * (v : ℝ)) := by
      funext x; rw [hF_def]; field_simp; ring
    rw [key]
    exact (ProbabilityTheory.IsGaussian.integrable_fun_id.const_mul _).add (integrable_const _)
  have hint : Integrable (llr (gaussianReal m₁ v) (gaussianReal m₂ v)) (gaussianReal m₁ v) :=
    hFint.congr hllr.symm
  -- evaluate `∫ F d𝒩(m₁,v)`
  have hFval : ∫ x, F x ∂(gaussianReal m₁ v) = (m₁ - m₂) ^ 2 / (2 * (v : ℝ)) := by
    have key : F = fun x => ((m₁ - m₂) / (v : ℝ)) * x + (m₂ ^ 2 - m₁ ^ 2) / (2 * (v : ℝ)) := by
      funext x; rw [hF_def]; field_simp; ring
    rw [key, integral_add (ProbabilityTheory.IsGaussian.integrable_fun_id.const_mul _)
      (integrable_const _), integral_const_mul, integral_id_gaussianReal, integral_const,
      probReal_univ, smul_eq_mul, one_mul]
    field_simp
    ring
  rw [klDiv_of_ac_of_integrable hac hint, integral_congr_ae hllr, probReal_univ, probReal_univ,
    add_sub_cancel_right, hFval]

end StatLean.Minimaxity
