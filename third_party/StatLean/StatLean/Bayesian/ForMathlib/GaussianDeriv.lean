module
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# The spatial derivative of the Gaussian density

The elementary but load-bearing fact behind the Tweedie formula: the Gaussian density
`gaussianPDFReal θ v x = (2πv)^{-1/2} exp(−(x−θ)²/(2v))`, viewed as a function of the observation
`x`, satisfies
$$\frac{\partial}{\partial x}\,\mathrm{gaussianPDFReal}\ \theta\ v\ x
  = \frac{\theta - x}{v}\,\mathrm{gaussianPDFReal}\ \theta\ v\ x.$$
Equivalently `(θ − x)·pdf = v·∂ₓ pdf`, the Gaussian score identity that converts the numerator
`∫θ·pdf dG(θ)` of a posterior mean into `x·f_G(x) + v·f_G'(x)` (Tweedie's formula).

**Reference.** Not in Robert. B. Efron, *Large-Scale Inference*, Cambridge University Press, 2010,
§1.5 and eq. (1.24)–(1.26) (Tweedie's formula and the underlying Gaussian identity); the identity
is the one-dimensional case of C. M. Stein's lemma (*Proc. Sixth Berkeley Symp.* 1972).

**Proof formalization notes.** The pin has Gaussian moments and mgf but no derivative of
`gaussianPDFReal`. We supply it directly: `gaussianPDFReal θ v` is `const · exp ∘ g` with
`g x = −(x−θ)²/(2v)`, so `HasDerivAt` follows from `HasDerivAt.exp` and the chain rule, and the
derivative simplifies by `field_simp`/`ring` using `v ≠ 0`. `deriv_gaussianPDFReal` is the
`HasDerivAt.deriv` corollary; `differentiable_gaussianPDFReal` collects pointwise
differentiability. The differentiation-under-the-integral step (moving `∂ₓ` inside `∫ · dG(θ)`) is
stated with its integrable-envelope regularity in `EmpiricalBayes.Tweedie`, not here.

**Bibliographic comments.** The identity `∂ₓ φ = −(x/σ²) φ` for the standard normal density is
classical (it makes the Hermite functions eigenfunctions of the Ornstein–Uhlenbeck operator); its
statistical exploitation is C. M. Stein's unbiased-risk and integration-by-parts lemma (1972,
1981) and, for empirical-Bayes shrinkage, H. Robbins's and M. C. K. Tweedie's marginal-to-posterior
formula popularized by B. Efron ("Tweedie's formula and selection bias," *J. Amer. Statist. Assoc.*
106 (2011), 1602–1614).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- The spatial derivative of the Gaussian density:
`∂ₓ gaussianPDFReal θ v x = ((θ − x)/v)·gaussianPDFReal θ v x` (Efron eq. (1.24)). -/
theorem hasDerivAt_gaussianPDFReal (θ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal θ v)
      ((θ - x) / (v : ℝ) * gaussianPDFReal θ v x) x := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  -- Derivative of the exponent `g x = -(x-θ)^2/(2v)`.
  have hsq : HasDerivAt (fun y : ℝ => (y - θ) ^ 2) ((2 : ℝ) * (x - θ) ^ (2 - 1) * 1) x :=
    ((hasDerivAt_id x).sub_const θ).pow 2
  have hg : HasDerivAt (fun y : ℝ => -(y - θ) ^ 2 / (2 * (v : ℝ)))
      (-((2 : ℝ) * (x - θ) ^ (2 - 1) * 1) / (2 * (v : ℝ))) x :=
    hsq.neg.div_const _
  -- Chain rule through `exp` and the constant prefactor: this IS `gaussianPDFReal θ v` by defeq.
  have hpdf : HasDerivAt (gaussianPDFReal θ v) _ x := (hg.exp).const_mul _
  convert hpdf using 1
  rw [gaussianPDFReal]
  field_simp
  ring

/-- The `deriv` form of `hasDerivAt_gaussianPDFReal`. -/
theorem deriv_gaussianPDFReal (θ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    deriv (gaussianPDFReal θ v) x = (θ - x) / (v : ℝ) * gaussianPDFReal θ v x :=
  (hasDerivAt_gaussianPDFReal θ v hv x).deriv

/-- `gaussianPDFReal θ v` is differentiable in the observation (for nondegenerate variance). -/
theorem differentiable_gaussianPDFReal (θ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Differentiable ℝ (gaussianPDFReal θ v) :=
  fun x => (hasDerivAt_gaussianPDFReal θ v hv x).differentiableAt

end StatLean.Bayesian
