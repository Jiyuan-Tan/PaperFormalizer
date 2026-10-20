module
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.CovarianceBilin
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF

@[expose] public section

/-!
# Gaussian shift experiment (limit experiment) and its likelihood ratio

The **Gaussian shift experiment** is the family of measurements indexed by a shift
parameter $h \in \mathbb{R}^k$ in which one observes a single draw from the multivariate
normal law $N(h, \Sigma)$, where $\Sigma$ is a fixed positive-definite covariance matrix.
In the theory of local asymptotic normality this is the **limit experiment** to which a
locally asymptotically normal sequence $P^n_{\theta_0 + h/\sqrt{n}}$ converges (in the
sense of weak convergence of experiments): the localized parametric family becomes, in
the limit, statistically equivalent to observing $X \sim N(h, \Sigma)$.

The two facts formalized here are:

1. For every shift $h$, the law $N(h, \Sigma)$ is a probability Gaussian measure on
   $\mathbb{R}^k$ (identified with the Euclidean space $\ell^2(\{1,\dots,k\})$) with mean
   $h$ and covariance $\Sigma$; such a family exists for every positive-definite $\Sigma$
   and is realized by Mathlib's `multivariateGaussian`.

2. The log-likelihood ratio against the base measure $N(0, \Sigma)$ has the closed form
   $$
   \log \frac{dN(h,\Sigma)}{dN(0,\Sigma)}(x)
     \;=\; \langle h,\ \Sigma^{-1} x\rangle \;-\; \tfrac12\,\langle h,\ \Sigma^{-1} h\rangle ,
   $$
   the affine-in-$x$ form characteristic of a Gaussian shift. A companion **tilted linear
   pushforward** identity records that the pushforward of $N(h, J^{-1})$ under the linear
   map $x \mapsto Jx$ equals the base Gaussian $N(0, J)$ reweighted by the exponential tilt
   $\exp\!\big(\langle h, y\rangle - \tfrac12\langle h, Jh\rangle\big)$.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in
Statistical and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 7
(Local Asymptotic Normality), §7.3 (Convergence to a Normal Experiment); the Gaussian
limit experiment and its representation theorem (Theorem 7.10) live in that section.
The likelihood-ratio form (2) is the multivariate analogue of the affine LAN expansion
appearing throughout Chapter 7.

**Proof formalization notes.**
Mathlib at this commit does not provide a stand-alone multivariate-Gaussian density or
linear-pushforward calculus (only `gaussianReal`, the abstract `IsGaussian` typeclass, and
`multivariateGaussian`). We therefore package the experiment as the `Prop`-valued predicate
`IsGaussianShift family cov` (each `family h` is a probability Gaussian with mean `h` and
covariance `cov`), and keep the two analytic facts as separate predicates:
`HasGaussianShiftLogLikelihoodRatio` (the closed-form LR above) and
`HasTiltedLinearPushforward` (the linear-pushforward / change-of-base identity used in
Theorem 7.10 Step 7). The existence result `exists_gaussianShift` and the witness
`isGaussianShift_multivariateGaussian` are constructive via `multivariateGaussian`, and
`IsGaussianShift.eq_multivariateGaussian` proves the experiment is determined uniquely at
each parameter (two Gaussians with equal mean and covariance coincide, via
`IsGaussian.ext`). The closed-form LR is not bundled into `exists_gaussianShift` because it
is not consumed downstream and its derivation needs an explicit multivariate density;
`hasTiltedLinearPushforward_of_isGaussianShift` discharges the tilt identity by showing both
sides equal `multivariateGaussian (J h) J`.

**Bibliographic comments.**
The Gaussian shift experiment and its affine log-likelihood ratio are folklore
with no single seminal source; they are the canonical limit object of Le Cam's theory of
asymptotic equivalence of experiments. The foundational reference is
L. Le Cam, "Locally asymptotically normal families of distributions," *University of
California Publications in Statistics* **3** (1960), 37–98, where local asymptotic normality
and the Gaussian limit experiment are introduced; see also L. Le Cam, *Asymptotic Methods
in Statistical Decision Theory*, Springer, 1986.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix

namespace AsymptoticStatistics
namespace GaussianShift

variable {k : ℕ}

/-! ## Linear action of a matrix on `EuclideanSpace`

A utility used to pre-compose kernels with "multiply by `J`" in Theorem 7.10. It is
continuous (hence measurable) because linear maps between finite-dimensional normed
spaces are continuous, and `EuclideanSpace.equiv` is a continuous linear equivalence.

This action is part of the Gaussian-shift API because it converts covariance-scale
draws into the information-scale coordinates used by the experiment. -/

noncomputable def matrixAction
    (J : Matrix (Fin k) (Fin k) ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm
    (Matrix.mulVecLin J ((EuclideanSpace.equiv (Fin k) ℝ) x))

lemma matrixAction_continuous (J : Matrix (Fin k) (Fin k) ℝ) :
    Continuous (matrixAction J) := by
  unfold matrixAction
  refine (EuclideanSpace.equiv (Fin k) ℝ).symm.continuous.comp ?_
  exact (Matrix.mulVecLin J).continuous_of_finiteDimensional.comp
    (EuclideanSpace.equiv (Fin k) ℝ).continuous

lemma matrixAction_measurable (J : Matrix (Fin k) (Fin k) ℝ) :
    Measurable (matrixAction J) :=
  (matrixAction_continuous J).measurable

/-- Spelling of `matrixAction` via `WithLp.equiv`, for use-site compatibility
with inner-product formulas that spell out the equiv manually. -/
lemma matrixAction_eq_withLp
    (J : Matrix (Fin k) (Fin k) ℝ) (x : EuclideanSpace ℝ (Fin k)) :
    matrixAction J x =
      (WithLp.equiv 2 (Fin k → ℝ)).symm (J.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) x)) :=
  rfl

/-- **Bridge**: `matrixAction J` coincides with the Mathlib `toEuclideanCLM J`
applied to the same argument. Both compute `toLp (J *ᵥ ofLp x)`; their definitions
differ only in which intermediate API (mulVecLin vs toEuclideanCLM) performs the
same matrix action. -/
lemma matrixAction_eq_toEuclideanCLM (J : Matrix (Fin k) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin k)) :
    matrixAction J x = Matrix.toEuclideanCLM (𝕜 := ℝ) J x := by
  rfl

/-- A family of probability measures `family : EuclideanSpace ℝ (Fin k) → Measure _`
**is Gaussian shift with covariance `cov`** when each `family h` is a probability
Gaussian measure, has mean `h`, and covariance `cov`. The log-likelihood ratio's
closed form is recorded as a separate proposition `HasGaussianShiftLogLikelihoodRatio`
below. -/
structure IsGaussianShift
    (family : EuclideanSpace ℝ (Fin k) → Measure (EuclideanSpace ℝ (Fin k)))
    (cov : Matrix (Fin k) (Fin k) ℝ) : Prop where
  posDef : Matrix.PosDef cov
  isProb : ∀ h, IsProbabilityMeasure (family h)
  isGaussian : ∀ h, IsGaussian (family h)
  /-- Mean `h`: for every `u`, `∫ ⟨u, x⟩ d(family h)(x) = ⟨u, h⟩`. -/
  mean_eq (h u : EuclideanSpace ℝ (Fin k)) :
    (∫ x, ⟪u, x⟫ ∂(family h)) = ⟪u, h⟫
  /-- Covariance `cov`. Stated via the bilinear integral on centred variables. -/
  cov_eq (h u v : EuclideanSpace ℝ (Fin k)) :
    (∫ x, ⟪u, x - h⟫ * ⟪v, x - h⟫ ∂(family h)) =
      ⟪u, (WithLp.equiv 2 _).symm (cov.mulVec ((WithLp.equiv 2 _) v))⟫

/-- Closed-form log-likelihood ratio of the Gaussian shift family:
`log d N(h, cov)/d N(0, cov) (x) = ⟨h, cov⁻¹ x⟩ - ½ ⟨h, cov⁻¹ h⟩`. -/
def HasGaussianShiftLogLikelihoodRatio
    (family : EuclideanSpace ℝ (Fin k) → Measure (EuclideanSpace ℝ (Fin k)))
    (cov : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ (h x : EuclideanSpace ℝ (Fin k)),
    Real.log (((family h).rnDeriv (family 0) x).toReal) =
      ⟪h, (WithLp.equiv 2 _).symm (cov⁻¹.mulVec ((WithLp.equiv 2 _) x))⟫
      - (1/2) * ⟪h, (WithLp.equiv 2 _).symm (cov⁻¹.mulVec ((WithLp.equiv 2 _) h))⟫

/-- **Gaussian tilted linear pushforward identity**, parametric in a base Gaussian `ν`.

For a Gaussian-shift family `family h ∼ N(h, C)` and a reference Gaussian
`ν ∼ N(0, J)`, the push-forward of `family h` by the linear action of `J` (i.e.
`matrixAction J`) equals `ν` re-weighted by the exponential tilt
`exp(⟨h, y⟩ - ½ ⟨h, J h⟩)`.

This single identity bundles (i) Gaussian push-forward by a linear map (in our setting
`J_*(N(h, J⁻¹)) = N(J h, J)`) and (ii) Radon–Nikodym change-of-base between two
Gaussians with the same covariance (`N(J h, J) = N(0, J).withDensity exp(·)`). It is
exactly the Gaussian-specific fact consumed by Theorem 7.10's `gaussianShift_bind_eq_limit`
(Step 7). Pairs with the measure-theoretic bridges `Measure.bind_map_eq_bind_comap` and
`Measure.withDensity_bind_condDistrib` to close Step 7.

The predicate separates this Gaussian-specific transport identity from the general
measure-theoretic bridges that consume it. For the canonical reference measure,
`hasTiltedLinearPushforward_of_isGaussianShift` derives the predicate from
`IsGaussianShift`. The interface parallels `HasGaussianShiftLogLikelihoodRatio`. -/
def HasTiltedLinearPushforward
    (family : EuclideanSpace ℝ (Fin k) → Measure (EuclideanSpace ℝ (Fin k)))
    (ν : Measure (EuclideanSpace ℝ (Fin k)))
    (J : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  ∀ h : EuclideanSpace ℝ (Fin k),
    (family h).map (matrixAction J) =
      ν.withDensity (fun y : EuclideanSpace ℝ (Fin k) =>
        ENNReal.ofReal (Real.exp (⟪h, y⟫ -
          (1/2 : ℝ) * ⟪h, matrixAction J h⟫)))

/-- **Any Gaussian shift family equals the canonical multivariate Gaussian**
pointwise. In other words, `IsGaussianShift` uniquely determines the family
(at each parameter) as the concrete `ProbabilityTheory.multivariateGaussian h C`.

This is the Gaussian uniqueness-by-parameters fact: two Gaussian measures with the
same mean and covariance are equal (`ProbabilityTheory.IsGaussian.ext`). The proof
re-derives mean / covariance from the `IsGaussianShift` fields and compares them
against `integral_id_multivariateGaussian` / `covarianceBilin_multivariateGaussian`.

Consumed by Theorem 7.10 Step 7 (`hTilt` discharge): lets us substitute the abstract
`gauss h` supplied to `LAN_representation` with the concrete Mathlib term, so the
Gaussian linear-pushforward / Radon–Nikodym identities can be stated against a
specific measure. -/
theorem IsGaussianShift.eq_multivariateGaussian
    {family : EuclideanSpace ℝ (Fin k) → Measure (EuclideanSpace ℝ (Fin k))}
    {C : Matrix (Fin k) (Fin k) ℝ} (hFamily : IsGaussianShift family C)
    (h : EuclideanSpace ℝ (Fin k)) :
    family h = ProbabilityTheory.multivariateGaussian h C := by
  haveI : IsProbabilityMeasure (family h) := hFamily.isProb h
  haveI : ProbabilityTheory.IsGaussian (family h) := hFamily.isGaussian h
  have hCps : C.PosSemidef := hFamily.posDef.posSemidef
  have hInt : Integrable (fun x : EuclideanSpace ℝ (Fin k) => x) (family h) :=
    ProbabilityTheory.IsGaussian.integrable_id
  have hMemLp : MeasureTheory.MemLp
      (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) 2 (family h) :=
    ProbabilityTheory.IsGaussian.memLp_two_id
  refine ProbabilityTheory.IsGaussian.ext ?_ ?_
  · -- Means agree, both equal to `h`.
    simp only [id_eq]
    rw [ProbabilityTheory.integral_id_multivariateGaussian]
    refine ext_inner_left ℝ fun u => ?_
    rw [← integral_inner hInt]
    exact hFamily.mean_eq h u
  · -- Covariance bilinear forms agree.
    refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => ?_
    rw [ProbabilityTheory.covarianceBilin_multivariateGaussian hCps,
      ProbabilityTheory.covarianceBilin_apply_eq_cov hMemLp]
    -- Reduce `covariance` to the centred inner-product integral (as in `exists_gaussianShift`).
    have hMean : ∀ w : EuclideanSpace ℝ (Fin k),
        (∫ x, ⟪w, x⟫ ∂(family h)) = ⟪w, h⟫ := hFamily.mean_eq h
    have hCovAsInt :
        ProbabilityTheory.covariance
            (fun x : EuclideanSpace ℝ (Fin k) => ⟪u, x⟫)
            (fun x : EuclideanSpace ℝ (Fin k) => ⟪v, x⟫) (family h)
          = ∫ x, ⟪u, x - h⟫ * ⟪v, x - h⟫ ∂(family h) := by
      simp_rw [ProbabilityTheory.covariance, hMean u, hMean v, ← inner_sub_right]
    rw [hCovAsInt, hFamily.cov_eq h u v]
    -- Finally, bridge `⟪u, (WithLp.equiv _).symm (C.mulVec (WithLp.equiv _ v))⟫`
    -- with `u.ofLp ⬝ᵥ C.mulVec v.ofLp` (coordinatewise, same trick as `cov_eq`).
    rw [show (u.ofLp ⬝ᵥ C.mulVec v.ofLp)
          = ∑ i, u.ofLp i * (C.mulVec v.ofLp) i from rfl]
    simp only [PiLp.inner_apply, WithLp.equiv_apply, WithLp.equiv_symm_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    change C.mulVec v.ofLp i * u.ofLp i = u.ofLp i * C.mulVec v.ofLp i
    ring

/-- **`multivariateGaussian · C` is a Gaussian shift family with covariance `C`**, for
every positive-definite `C`. This is the concrete witness that downstream callers use
directly when they need `N(h, C)` rather than an abstract Gaussian-shift provider. -/
theorem isGaussianShift_multivariateGaussian
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : Matrix.PosDef C) :
    IsGaussianShift (fun h => ProbabilityTheory.multivariateGaussian h C) C := by
  have hCps : C.PosSemidef := hC.posSemidef
  refine
    { posDef := hC
      isProb := fun _ => inferInstance
      isGaussian := fun _ => inferInstance
      mean_eq := ?_
      cov_eq := ?_ }
  · intro h u
    have hInt : Integrable (fun x : EuclideanSpace ℝ (Fin k) => x)
        (ProbabilityTheory.multivariateGaussian h C) :=
      ProbabilityTheory.IsGaussian.integrable_id
    rw [integral_inner hInt, ProbabilityTheory.integral_id_multivariateGaussian]
  · intro h u v
    have hMemLp : MeasureTheory.MemLp
        (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) 2
        (ProbabilityTheory.multivariateGaussian h C) :=
      ProbabilityTheory.IsGaussian.memLp_two_id
    have hInt : Integrable (fun x : EuclideanSpace ℝ (Fin k) => x)
        (ProbabilityTheory.multivariateGaussian h C) :=
      ProbabilityTheory.IsGaussian.integrable_id
    -- Mean under the Gaussian measure, specialised to both `u` and `v`.
    have hMean : ∀ w : EuclideanSpace ℝ (Fin k),
        (∫ x, ⟪w, x⟫ ∂ProbabilityTheory.multivariateGaussian h C) = ⟪w, h⟫ := by
      intro w
      rw [integral_inner hInt, ProbabilityTheory.integral_id_multivariateGaussian]
    -- Rewrite the target covariance-like integral as the covariance of the real-valued
    -- random variables `⟪u, ·⟫` and `⟪v, ·⟫` under the Gaussian.
    have hCovEq :
        ProbabilityTheory.covariance
            (fun x : EuclideanSpace ℝ (Fin k) => ⟪u, x⟫)
            (fun x : EuclideanSpace ℝ (Fin k) => ⟪v, x⟫)
            (ProbabilityTheory.multivariateGaussian h C)
          = ∫ x, ⟪u, x - h⟫ * ⟪v, x - h⟫
              ∂ProbabilityTheory.multivariateGaussian h C := by
      simp_rw [ProbabilityTheory.covariance, hMean u, hMean v, ← inner_sub_right]
    rw [← hCovEq, ← ProbabilityTheory.covarianceBilin_apply_eq_cov hMemLp,
      ProbabilityTheory.covarianceBilin_multivariateGaussian hCps]
    -- Finally, identify `u.ofLp ⬝ᵥ C.mulVec v.ofLp` with the `WithLp.equiv`-spelling
    -- inner product. Reduce both sides to `∑ i, u.ofLp i * (C.mulVec v.ofLp) i`.
    rw [show (u.ofLp ⬝ᵥ C.mulVec v.ofLp)
          = ∑ i, u.ofLp i * (C.mulVec v.ofLp) i from rfl]
    simp only [PiLp.inner_apply, WithLp.equiv_apply, WithLp.equiv_symm_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- `⟪a, b⟫ = b * a` on `ℝ`, by definition of the real inner product.
    change u.ofLp i * C.mulVec v.ofLp i = C.mulVec v.ofLp i * u.ofLp i
    ring

/-- **Existence of a Gaussian shift family** with covariance `C` for every positive-definite
`C`. Realised by Mathlib's `ProbabilityTheory.multivariateGaussian h C`.

This theorem asserts only `IsGaussianShift`; the closed-form likelihood-ratio
property is a separate interface, `HasGaussianShiftLogLikelihoodRatio`. -/
theorem exists_gaussianShift
    (C : Matrix (Fin k) (Fin k) ℝ) (hC : Matrix.PosDef C) :
    ∃ family : EuclideanSpace ℝ (Fin k) → Measure (EuclideanSpace ℝ (Fin k)),
      IsGaussianShift family C :=
  ⟨fun h => ProbabilityTheory.multivariateGaussian h C,
    isGaussianShift_multivariateGaussian C hC⟩

/-- **Discharge of `HasTiltedLinearPushforward` for a Gaussian shift family.**

Given an abstract Gaussian-shift family `gauss h ~ N(h, J⁻¹)` and the positive-definite
covariance `J`, the tilted linear push-forward identity holds against the base
`multivariateGaussian 0 J`:
```
(gauss h).map (matrixAction J) =
  (multivariateGaussian 0 J).withDensity
    (fun y => ENNReal.ofReal (Real.exp (⟪h, y⟫ - (1/2) * ⟪h, matrixAction J h⟫))).
```

Proof: Both sides equal `multivariateGaussian (toEuclideanCLM J h) J`.

* LHS: `gauss h = multivariateGaussian h J⁻¹` (`IsGaussianShift.eq_multivariateGaussian`).
  Apply `multivariateGaussian_map_toEuclideanCLM` with `A = J`, then collapse
  `J * J⁻¹ * Jᴴ = 1 * J = J` using `Matrix.PosDef.isUnit` + `Matrix.PosDef.isHermitian`.
* RHS: Rewrite the tilt `⟨h, matrixAction J h⟩` as `h.ofLp ⬝ᵥ J *ᵥ h.ofLp` via
  `Matrix.inner_toEuclideanCLM`, then apply `multivariateGaussian_withDensity_exp_shift`.

Lets Theorem 7.10 Step 7 discharge its `hTilt` provider internally once
`π.map snd = multivariateGaussian 0 J` has been identified. -/
theorem hasTiltedLinearPushforward_of_isGaussianShift
    {gauss : EuclideanSpace ℝ (Fin k) → Measure (EuclideanSpace ℝ (Fin k))}
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : Matrix.PosDef J)
    (hGauss : IsGaussianShift gauss J⁻¹) :
    HasTiltedLinearPushforward gauss
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) J := by
  intro h
  have hJ_ps : J.PosSemidef := hJ.posSemidef
  have hJinv_ps : J⁻¹.PosSemidef := hJ.inv.posSemidef
  have hJ_herm : Jᴴ = J := hJ.isHermitian.eq
  have hJ_unit : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det J).mp hJ.isUnit
  -- LHS: `(gauss h).map (matrixAction J) = multivariateGaussian (J h) J`.
  have h_lhs : (gauss h).map (matrixAction J)
      = ProbabilityTheory.multivariateGaussian
          (Matrix.toEuclideanCLM (𝕜 := ℝ) J h) J := by
    rw [hGauss.eq_multivariateGaussian h,
      show (matrixAction J : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
          = Matrix.toEuclideanCLM (𝕜 := ℝ) J from
        funext (matrixAction_eq_toEuclideanCLM J),
      ProbabilityTheory.multivariateGaussian_map_toEuclideanCLM (A := J)
        (μ := h) (S := J⁻¹) hJinv_ps,
      show J * J⁻¹ * Jᴴ = J from by
        rw [Matrix.mul_nonsing_inv _ hJ_unit, one_mul, hJ_herm]]
  -- Tilt equivalence: `⟪h, matrixAction J h⟫ = h.ofLp ⬝ᵥ J *ᵥ h.ofLp`.
  have h_tilt_eq : (1/2 : ℝ) * ⟪h, matrixAction J h⟫
      = (h.ofLp ⬝ᵥ J.mulVec h.ofLp) / 2 := by
    rw [matrixAction_eq_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
    ring
  -- RHS: apply `multivariateGaussian_withDensity_exp_shift`.
  simp_rw [h_tilt_eq]
  rw [ProbabilityTheory.multivariateGaussian_withDensity_exp_shift hJ_ps h]
  exact h_lhs

end GaussianShift
end AsymptoticStatistics
