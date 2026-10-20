module
public import StatLean.StatisticalModels.FactorModels.Moments

@[expose] public section

/-!
# The Gaussian (normal) linear factor model

`BKM`'s own model: Gaussian latent factors and Gaussian specific factors, so that the
observed law is again Gaussian.

* `gaussianFactorModel` — the model map `P ↦ factorLaw P (N(0, Φ)) (N(0, Ψ))`, i.e. the
  parameter-to-law map of the normal factor model. This is the family the identifiability
  statements of `FactorModels.Identifiability` are stated against;
* **`factorLaw_multivariateGaussian`** — `x ∼ N_p(μ, Λ Φ Λᵀ + Ψ)` (`BKM` Eq. (3.5) at `Φ = I`);
* `realizesFactorParams_gaussian` — the Gaussian instantiation does realize the parameters,
  so all of `FactorModels.Moments` applies to it unconditionally;
* `factorLaw_conditional_multivariateGaussian` — the conditional model `x ∣ y ∼ N_p(μ + Λ y,
  Ψ)` of `BKM` Eq. (3.1), i.e. the measurement kernel is Gaussian.

**Reference.** D. Bartholomew, M. Knott, and I. Moustaki, *Latent Variable Models and Factor
Analysis: A Unified Approach*, 3rd ed., Wiley, 2011, Eq. (3.1) (`x ∣ y ∼ N_p(μ + Λ y, Ψ)`),
Eq. (3.2) (`y ∼ N_q(0, I)`), Eq. (3.3), Eq. (3.5) (`x ∼ N_p(μ, Λ Λ′ + Ψ)`) (`BKM`).

**Proof formalization notes.** *Junk values:* `multivariateGaussian m S` is
`Measure.dirac m` when `S` is not positive semidefinite, so
every statement carries `IsProperFactorParams` (or the individual PSD hypotheses)
explicitly — without them `gaussianFactorModel` silently degenerates and, in particular, does
**not** have covariance `factorCovariance P`. *Book vs Lean:* `BKM` Eq. (3.5) is the
orthogonal case `Φ = I`; the general `Φ` below is our generalization.

**Bibliographic comments.** The normal-theory factor model is D. N. Lawley, "The estimation
of factor loadings by the method of maximum likelihood," *Proc. Roy. Soc. Edinburgh* **60**
(1940), 64–82; `BKM` ch. 3 is the modern presentation.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.FactorModels

open StatLean.StatisticalModels

variable {p q : ℕ}

/-- The **normal linear factor model** as a parameter-to-law map (`BKM` Eq. (3.1)–(3.3)):
Gaussian latent factors `y ∼ N_q(0, Φ)` and Gaussian specific factors `e ∼ N_p(0, Ψ)`.

*Edge behavior:* at parameters with a non-PSD `Φ` or `Ψ` the corresponding
`multivariateGaussian` collapses to a Dirac mass, so the law is **not** `N(μ, Σ)`; all
theorems below assume `IsProperFactorParams`. -/
noncomputable def gaussianFactorModel (p q : ℕ) :
    FactorParams p q → Measure (EuclideanSpace ℝ (Fin p)) :=
  fun P => factorLaw P (multivariateGaussian 0 P.factorCov)
    (multivariateGaussian 0 P.uniqueCov)

theorem gaussianFactorModel_apply (P : FactorParams p q) :
    gaussianFactorModel p q P
      = factorLaw P (multivariateGaussian 0 P.factorCov)
          (multivariateGaussian 0 P.uniqueCov) := rfl

/-- **`BKM` Eq. (3.1)** — the conditional (measurement) model is Gaussian: given the factors,
`x ∼ N_p(μ + Λ y, Ψ)`. -/
theorem measurementKernel_multivariateGaussian (P : FactorParams p q)
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : P.uniqueCov.PosSemidef) (y : EuclideanSpace ℝ (Fin q)) :
    measurementKernel P (multivariateGaussian 0 P.uniqueCov) y
      = multivariateGaussian
          (P.μ + Matrix.toEuclideanLin (𝕜 := ℝ) P.loading y) P.uniqueCov := by
  rw [measurementKernel_apply, multivariateGaussian_map_const_add 0 _ hΨ, add_zero]
  congr 1
  abel

/-- **HEADLINE — `BKM` Eq. (3.5), general `Φ`**: the Gaussian factor model has observed law
`x ∼ N_p(μ, Λ Φ Λᵀ + Ψ)`. -/
theorem factorLaw_multivariateGaussian (P : FactorParams p q)
    -- USER-INPUT: genuine covariance parameters; BKM Eq. (3.1)–(3.2)
    (hΦ : P.factorCov.PosSemidef) (hΨ : P.uniqueCov.PosSemidef) :
    factorLaw P (multivariateGaussian 0 P.factorCov) (multivariateGaussian 0 P.uniqueCov)
      = multivariateGaussian P.μ (factorCovariance P) := by
  rw [factorLaw_eq_lmmLaw, MixedEffects.lmmLaw_multivariateGaussian _ _ _ _ hΦ hΨ,
    factorDesign_X, toEuclideanLin_one_apply]
  rfl

/-- The model-map form of the headline. -/
theorem gaussianFactorModel_eq_multivariateGaussian (P : FactorParams p q)
    -- USER-INPUT: genuine covariance parameters; BKM Eq. (3.1)–(3.2)
    (hP : IsProperFactorParams P) :
    gaussianFactorModel p q P = multivariateGaussian P.μ (factorCovariance P) := by
  rw [gaussianFactorModel_apply, factorLaw_multivariateGaussian P hP.1 hP.2]

/-- The Gaussian instantiation **realizes** its parameters: `N(0, Φ)` is centered with
covariance `Φ` and `N(0, Ψ)` is centered with covariance `Ψ`. Hence every theorem of
`FactorModels.Moments` applies to `gaussianFactorModel` with no further hypotheses. -/
theorem realizesFactorParams_gaussian (P : FactorParams p q)
    -- USER-INPUT: genuine covariance parameters; BKM Eq. (3.1)–(3.2)
    (hP : IsProperFactorParams P) :
    RealizesFactorParams P (multivariateGaussian 0 P.factorCov)
      (multivariateGaussian 0 P.uniqueCov) :=
  ⟨meanVec_multivariateGaussian _ _, meanVec_multivariateGaussian _ _,
    covMatrix_multivariateGaussian _ _ hP.1, covMatrix_multivariateGaussian _ _ hP.2⟩

/-- The mean of the Gaussian factor model is `μ` (`BKM` Eq. (3.5)). -/
theorem meanVec_gaussianFactorModel (P : FactorParams p q)
    -- USER-INPUT: genuine covariance parameters; BKM Eq. (3.1)–(3.2)
    (hP : IsProperFactorParams P) :
    meanVec (gaussianFactorModel p q P) = P.μ := by
  rw [gaussianFactorModel_eq_multivariateGaussian P hP]
  exact meanVec_multivariateGaussian _ _

/-- The covariance of the Gaussian factor model is `Σ = Λ Φ Λᵀ + Ψ` (`BKM` Eq. (3.12),
general `Φ`). -/
theorem covMatrix_gaussianFactorModel (P : FactorParams p q)
    -- USER-INPUT: genuine covariance parameters; BKM Eq. (3.1)–(3.2)
    (hP : IsProperFactorParams P) :
    covMatrix (gaussianFactorModel p q P) = factorCovariance P := by
  rw [gaussianFactorModel_eq_multivariateGaussian P hP]
  exact covMatrix_multivariateGaussian _ _ (posSemidef_factorCovariance P hP)

end StatLean.StatisticalModels.FactorModels
