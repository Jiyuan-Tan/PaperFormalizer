module
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

/-!
Asymptotic Statistics — Explicit covariance additivity for multivariate
Gaussian convolutions.

Mathlib's `isGaussian_conv` instance shows that the convolution of two Gaussian
measures is Gaussian, but it does not give the explicit mean / covariance
addition formula at the level of `multivariateGaussian m S`. This file
supplies that formula via the `charFun` + Lévy uniqueness route.

Used in `Experiment/GaussianShiftMinimax.lean` Step D (PSD-monotone-Anderson):
`N(0, Σ₁) ∗ N(0, Σ₂ - Σ₁) = N(0, Σ₂)` for PSD `Σ₁ ≤ Σ₂` rewrites the larger
Gaussian as an independent shift of the smaller, then Anderson on independent
shifts gives the lower-bound monotonicity `∫ L dN(0, Σ₁) ≤ ∫ L dN(0, Σ₂)`.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal RealInnerProductSpace

namespace AsymptoticStatistics

/-- **Multivariate Gaussian convolution = sum of means + sum of covariances.**

Direct corollary of the standard fact `charFun (μ ∗ ν) = charFun μ * charFun ν`
applied to two `multivariateGaussian` measures, then matched against
`charFun_multivariateGaussian` for the candidate sum, then Lévy-uniqueness
(`Measure.ext_of_charFun`) closes.

Mathlib only gives `isGaussian_conv` (existential: the convolution is Gaussian)
without specifying mean and covariance; this lemma fills that gap. -/
theorem multivariateGaussian_conv_multivariateGaussian
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m₁ m₂ : EuclideanSpace ℝ ι) {S₁ S₂ : Matrix ι ι ℝ}
    (hS₁ : S₁.PosSemidef) (hS₂ : S₂.PosSemidef) :
    (multivariateGaussian m₁ S₁) ∗ (multivariateGaussian m₂ S₂)
      = multivariateGaussian (m₁ + m₂) (S₁ + S₂) := by
  refine Measure.ext_of_charFun ?_
  ext t
  rw [charFun_conv, charFun_multivariateGaussian hS₁,
      charFun_multivariateGaussian hS₂,
      charFun_multivariateGaussian (hS₁.add hS₂),
      ← Complex.exp_add]
  congr 1
  -- Reduce: (⟪t, m₁⟫I - t·S₁·t/2) + (⟪t, m₂⟫I - t·S₂·t/2)
  --       = ⟪t, m₁ + m₂⟫I − t·(S₁+S₂)·t/2
  have h_inner : (⟪t, m₁ + m₂⟫ : ℂ) = (⟪t, m₁⟫ : ℂ) + (⟪t, m₂⟫ : ℂ) := by
    rw [inner_add_right]; push_cast; ring
  have h_dot : t.ofLp ⬝ᵥ (S₁ + S₂).mulVec t.ofLp =
      t.ofLp ⬝ᵥ S₁.mulVec t.ofLp + t.ofLp ⬝ᵥ S₂.mulVec t.ofLp := by
    rw [Matrix.add_mulVec, dotProduct_add]
  rw [h_inner, h_dot]
  push_cast
  ring

end AsymptoticStatistics
