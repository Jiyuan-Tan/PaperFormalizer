module
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-!
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junwei Lu, Claude Opus 4.7
-/

/-!
# Multivariate Gaussian under linear scaling

For a real `τ`, the centred multivariate Gaussian
`multivariateGaussian 0 (τ² • I)` on `EuclideanSpace ℝ ι` equals the
pushforward of the standard Gaussian under the scalar multiplication
`x ↦ τ • x`.  Equivalently, scaling a standard Gaussian by `τ` yields
the Gaussian with covariance `τ² • I`.

Used in `LowerBounds/T7_AndersonClosure/DiscreteToContinuousPriorBridge.lean`
(B2 brick): the change-of-variables `Δ ↦ τΔ` translates the standard
multivariate Gaussian `N(0, I)` to `N(0, τ² · I)`, which is the prior
side of the τ-Gaussian Bayes risk.

**Discharge plan (charFun comparison)**:
* LHS charFun at `x`: `exp(-x · (τ²·I) x / 2) = exp(-τ² ‖x‖² / 2)`
  (via `charFun_multivariateGaussian` + matrix-algebra of
  `(τ²·I).mulVec x = τ² • x`).
* RHS charFun at `x`: `charFun stdGaussian (τ • x)
   = exp(- ‖τ • x‖² / 2) = exp(-τ² ‖x‖² / 2)` (via push-forward
  formula for charFun + `charFun_stdGaussian` + `norm_smul`).
* Both Gaussian; apply `Measure.ext_of_charFun`.
-/

namespace AsymptoticStatistics.ForMathlib

open MeasureTheory Filter Topology Complex
open scoped ENNReal NNReal ProbabilityTheory RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- `(τ² • I).PosSemidef` — scalar multiplication of identity by a square. -/
private lemma posSemidef_sq_smul_one (τ : ℝ) :
    ((τ^2 : ℝ) • (1 : Matrix ι ι ℝ)).PosSemidef := by
  have h1 : (1 : Matrix ι ι ℝ).PosSemidef := Matrix.PosDef.posSemidef Matrix.PosDef.one
  exact h1.smul (by positivity : (0 : ℝ) ≤ τ^2)

/-- **Multivariate Gaussian scaling identity** (centred case).

For `τ : ℝ`, the centred multivariate Gaussian with covariance
`τ² • I` equals the pushforward of the standard Gaussian under the
scaling map `x ↦ τ • x`.

**Discharge**: charFun comparison via `Measure.ext_of_charFun`.  Both
sides equal `exp(-τ² ‖x‖² / 2)` at every `x`. -/
theorem multivariateGaussian_eq_stdGaussian_map_smul (τ : ℝ) :
    ProbabilityTheory.multivariateGaussian
        (0 : EuclideanSpace ℝ ι) ((τ^2) • (1 : Matrix ι ι ℝ))
      = (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)).map
          (fun x : EuclideanSpace ℝ ι => τ • x) := by
  -- charFun comparison: both sides equal `exp(-τ² ‖t‖² / 2)` at every `t`.
  have h_smul_meas : Measurable (fun x : EuclideanSpace ℝ ι => τ • x) := by fun_prop
  haveI : IsProbabilityMeasure
      ((ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)).map
        (fun x : EuclideanSpace ℝ ι => τ • x)) :=
    MeasureTheory.Measure.isProbabilityMeasure_map h_smul_meas.aemeasurable
  refine MeasureTheory.Measure.ext_of_charFun ?_
  ext t
  rw [ProbabilityTheory.charFun_multivariateGaussian (posSemidef_sq_smul_one τ),
      MeasureTheory.charFun_map_smul τ t,
      ProbabilityTheory.charFun_stdGaussian]
  -- Reduce both arguments of `Complex.exp` to `-(τ² · ‖t‖²) / 2`.
  congr 1
  -- LHS arg: ⟪t, 0⟫·I - t.ofLp ⬝ᵥ ((τ²·1).mulVec t.ofLp) / 2
  -- RHS arg: -‖τ•t‖² / 2
  have hmv : ((τ^2 : ℝ) • (1 : Matrix ι ι ℝ)).mulVec (WithLp.ofLp t)
      = (τ^2) • (WithLp.ofLp t : ι → ℝ) := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  have hd : dotProduct (WithLp.ofLp t : ι → ℝ) ((τ^2) • (WithLp.ofLp t : ι → ℝ))
      = (τ^2) * dotProduct (WithLp.ofLp t : ι → ℝ) (WithLp.ofLp t) := by
    rw [dotProduct_smul, smul_eq_mul]
  have htt : dotProduct (WithLp.ofLp t : ι → ℝ) (WithLp.ofLp t) = ‖t‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
  have hns : ‖(τ : ℝ) • t‖ ^ 2 = τ^2 * ‖t‖^2 := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hmv, hd, htt, inner_zero_right]
  -- Goal now: ↑0 * I - ↑(τ²·‖t‖²) / 2 = -↑‖τ•t‖² / 2
  -- Convert the ℂ-power on the RHS to a real power via `Complex.ofReal_pow`,
  -- then apply `hns`.
  rw [show ((‖τ • t‖ : ℂ))^2 = ((‖τ • t‖^2 : ℝ) : ℂ) by push_cast; ring,
      hns]
  push_cast
  ring

end AsymptoticStatistics.ForMathlib
