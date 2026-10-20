module
public import StatLean.StatisticalModels.FactorModels.Gaussian
public import StatLean.StatisticalModels.MixedEffects.BLUP
public import StatLean.StatisticalModels.MixedEffects.Henderson
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section

/-!
# Factor scores — the posterior distribution of the latent factors

The factors are not observed, so "estimating" them means computing their conditional law
given the data. In the normal factor model that law is again Gaussian:
$$y \mid x \;\sim\; N_q\big(\Phi \Lambda^{\!\top} \Sigma^{-1}(x-\mu),\;
    \Phi - \Phi \Lambda^{\!\top} \Sigma^{-1} \Lambda \Phi\big), \qquad
  \Sigma = \Lambda \Phi \Lambda^{\!\top} + \Psi .$$

The posterior mean of the factors **is** the best linear unbiased predictor of the random
effects: `condMeanMatrix_factorScores` is Henderson's BLUP matrix at `Z = Λ`, `G = Φ`,
`R = Ψ`.

* `factorJointLaw` — the joint law of `(x, y)`, i.e. `MixedEffects.lmmJointLaw` at the factor
  design; `factorJointLaw_fst` recovers the observed law;
* `factorJointLaw_eq_blockGaussian` — in the Gaussian model it is the block Gaussian with
  `Σ_xx = Λ Φ Λᵀ + Ψ`, `Σ_xy = Λ Φ`, `Σ_yy = Φ`;
* `factorScoreKernel` — the posterior kernel, an instance of `gaussianCondKernel`;
* `condMeanMatrix_factorScores` / `condCovMatrix_factorScores` — the two matrix identities;
* **`compProd_factorJointLaw`** — the exact disintegration: observed law composed with the
  posterior kernel is the joint law;
* `condMeanMatrix_factorScores_precision` — the **covariance form = precision form** of the
  score matrix, `Φ Λᵀ Σ⁻¹ = (Λᵀ Ψ⁻¹ Λ + Φ⁻¹)⁻¹ Λᵀ Ψ⁻¹`. This is `BKM` Eq. (3.7)–(3.8)/(3.64)
  and it is **exactly** Henderson's push-through identity at `Z = Λ`, `G = Φ`, `R = Ψ`. Its
  `Φ = I` specialization `condMeanMatrix_factorScores_standardized` is `BKM` Eq. (3.64)
  verbatim, `Λ′Σ⁻¹ = (I + Γ)⁻¹ Λ′Ψ⁻¹` with `Γ = gammaMatrix P = Λ′Ψ⁻¹Λ`.

**Reference.** D. Bartholomew, M. Knott, and I. Moustaki, *Latent Variable Models and Factor
Analysis: A Unified Approach*, 3rd ed., Wiley, 2011, Eq. (3.6) (`y ∣ x ∼ N_q(Λ′(ΛΛ′+Ψ)⁻¹(x−μ),
(Λ′Ψ⁻¹Λ + I)⁻¹)`), Eq. (3.9) (`E(y ∣ x) = (I+Γ)⁻¹(X − E X)`, with `Γ = Λ′Ψ⁻¹Λ`), Eq. (3.62)
(Bartlett scores) and Eq. (3.64) (regression scores `C = Λ′Σ⁻¹ = (I+Γ)⁻¹Λ′Ψ⁻¹`) (`BKM`);
C. R. Henderson, "Estimation of genetic parameters," *Ann. Math. Statist.* **21** (1950),
309–310 (`Hen50`).

**Proof formalization notes.** *Junk values:* `Matrix.inv` is `0` at singular matrices, so
`hSig : (factorCovariance P).PosDef` is carried explicitly wherever
`Σ⁻¹` appears; `multivariateGaussian` degenerates to a Dirac off the PSD cone, so `Φ` and `Ψ`
carry PSD hypotheses. *Book vs Lean:* `BKM` Eq. (3.6) states the posterior at its
normalization `Φ = I`, and writes the posterior covariance in the Woodbury form
`(Λ′Ψ⁻¹Λ + I)⁻¹`; the form below is the Schur-complement form `Φ − Φ Λ′ Σ⁻¹ Λ Φ`, which at
`Φ = I` and nonsingular `Ψ` is the same matrix. The Woodbury identity between the two forms
is **not** claimed here.

**Bibliographic comments.** Factor-score estimation splits historically into Thomson's
regression scores (the posterior mean, `BKM` Eq. (3.64)) and Bartlett's weighted least-squares
scores (`BKM` Eq. (3.62)); only the posterior law itself is formalized here.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.FactorModels

open StatLean.StatisticalModels

variable {p q : ℕ}

/-! ### The joint law of observations and factors -/

/-- The **joint law of `(x, y)`** — observation block first, latent factors second (the block
order at which `Gaussian.Conditioning` applies without a swap). Defined as the mixed-model
joint law of the factor design. -/
noncomputable def factorJointLaw (P : FactorParams p q)
    (F : Measure (EuclideanSpace ℝ (Fin q))) (E : Measure (EuclideanSpace ℝ (Fin p))) :
    Measure (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) :=
  MixedEffects.lmmJointLaw (factorDesign P) P.μ F E

/-- The observation marginal of the joint law is the factor model's observed law. -/
theorem factorJointLaw_fst (P : FactorParams p q)
    (F : Measure (EuclideanSpace ℝ (Fin q))) (E : Measure (EuclideanSpace ℝ (Fin p)))
    [IsProbabilityMeasure F] [IsProbabilityMeasure E] :
    (factorJointLaw P F E).map Prod.fst = factorLaw P F E := by
  rw [factorJointLaw, MixedEffects.lmmJointLaw_fst, factorLaw_eq_lmmLaw]

/-- **The Gaussian joint law** (`BKM` Eq. (3.1)–(3.3) jointly): `(x, y)` is the block Gaussian
with `Σ_xx = Λ Φ Λᵀ + Ψ`, `Σ_xy = Λ Φ` and `Σ_yy = Φ`. -/
theorem factorJointLaw_eq_blockGaussian (P : FactorParams p q)
    -- USER-INPUT: genuine covariance parameters; BKM Eq. (3.1)–(3.2)
    (hΦ : P.factorCov.PosSemidef) (hΨ : P.uniqueCov.PosSemidef) :
    factorJointLaw P (multivariateGaussian 0 P.factorCov)
        (multivariateGaussian 0 P.uniqueCov)
      = (multivariateGaussian (blockPair P.μ 0)
          (Matrix.fromBlocks (factorCovariance P) (P.loading * P.factorCov)
            (P.loading * P.factorCov)ᵀ P.factorCov)).map
            (sumMeasEquivProd (ι₁ := Fin p) (ι₂ := Fin q)) := by
  rw [factorJointLaw, MixedEffects.lmmJointLaw_eq_blockGaussian _ _ _ _ hΦ hΨ,
    factorDesign_X, toEuclideanLin_one_apply]
  rfl

/-! ### The posterior of the factors -/

/-- The **factor-score kernel** `x ↦ law of (y ∣ x)` (`BKM` Eq. (3.6)): the Gaussian
conditional kernel at the factor model's blocks. Its mean and covariance are computed by
`factorScoreKernel_apply` below.

*Edge behavior:* inherits `gaussianCondKernel`'s unconditional Markov property; at a singular
`Σ` the `Matrix.inv` junk value (`0`) makes the mean function `0`, hence the `PosDef`
hypotheses downstream. -/
noncomputable def factorScoreKernel (P : FactorParams p q) :
    Kernel (EuclideanSpace ℝ (Fin p)) (EuclideanSpace ℝ (Fin q)) :=
  gaussianCondKernel P.μ 0 (factorCovariance P) (P.loading * P.factorCov) P.factorCov

/-- **The posterior mean matrix is `Φ Λᵀ Σ⁻¹`** — Thomson's regression-score matrix
(`BKM` Eq. (3.64); at `Φ = I` this is `Λ′Σ⁻¹`). It is the *same* matrix identity as
Henderson's BLUP matrix `G Zᵀ V⁻¹`. -/
theorem condMeanMatrix_factorScores (P : FactorParams p q)
    -- USER-INPUT: symmetric latent covariance; BKM Eq. (3.2)
    (hΦ : P.factorCovᵀ = P.factorCov) :
    condMeanMatrix (factorCovariance P) (P.loading * P.factorCov)
      = P.factorCov * P.loadingᵀ * (factorCovariance P)⁻¹ :=
  MixedEffects.condMeanMatrix_lmm (factorDesign P) P.factorCov P.uniqueCov hΦ

/-- **The posterior covariance is `Φ − Φ Λᵀ Σ⁻¹ Λ Φ`** — the Schur complement of the factor
model's joint covariance (`BKM` Eq. (3.6), Schur form). -/
theorem condCovMatrix_factorScores (P : FactorParams p q)
    -- USER-INPUT: symmetric latent covariance; BKM Eq. (3.2)
    (hΦ : P.factorCovᵀ = P.factorCov) :
    condCovMatrix (factorCovariance P) (P.loading * P.factorCov) P.factorCov
      = P.factorCov
        - P.factorCov * P.loadingᵀ * (factorCovariance P)⁻¹ * P.loading * P.factorCov := by
  simp only [condCovMatrix, Matrix.transpose_mul, hΦ, Matrix.mul_assoc]

/-- **HEADLINE — the posterior law of the factors** (`BKM` Eq. (3.6), general `Φ`):
`y ∣ x ∼ N_q(Φ Λᵀ Σ⁻¹ (x − μ), Φ − Φ Λᵀ Σ⁻¹ Λ Φ)`. -/
theorem factorScoreKernel_apply (P : FactorParams p q)
    -- USER-INPUT: symmetric latent covariance; BKM Eq. (3.2)
    (hΦ : P.factorCovᵀ = P.factorCov) (x : EuclideanSpace ℝ (Fin p)) :
    factorScoreKernel P x
      = multivariateGaussian
          (Matrix.toEuclideanLin (𝕜 := ℝ)
            (P.factorCov * P.loadingᵀ * (factorCovariance P)⁻¹) (x - P.μ))
          (P.factorCov
            - P.factorCov * P.loadingᵀ * (factorCovariance P)⁻¹ * P.loading
                * P.factorCov) := by
  rw [factorScoreKernel, gaussianCondKernel_apply, condMeanMatrix_factorScores P hΦ,
    condCovMatrix_factorScores P hΦ, zero_add]

/-- **HEADLINE — factor scores as an exact disintegration** (`BKM` Eq. (3.6)): the observed
law composed with the factor-score kernel is the joint law of `(x, y)`. -/
theorem compProd_factorJointLaw (P : FactorParams p q)
    -- USER-INPUT: genuine covariance parameters; BKM Eq. (3.1)–(3.2)
    (hΦ : P.factorCov.PosSemidef) (hΨ : P.uniqueCov.PosSemidef)
    -- USER-INPUT: nondegenerate observed covariance Σ = ΛΦΛᵀ + Ψ — without it `Σ⁻¹` is the
    -- `Matrix.inv` junk value; BKM Eq. (3.6)
    (hSig : (factorCovariance P).PosDef) :
    factorLaw P (multivariateGaussian 0 P.factorCov) (multivariateGaussian 0 P.uniqueCov)
        ⊗ₘ factorScoreKernel P
      = factorJointLaw P (multivariateGaussian 0 P.factorCov)
          (multivariateGaussian 0 P.uniqueCov) := by
  have h := MixedEffects.compProd_lmmJointLaw (factorDesign P) P.μ P.factorCov P.uniqueCov
    hΦ hΨ hSig
  rw [factorDesign_X, toEuclideanLin_one_apply] at h
  rw [factorLaw_eq_lmmLaw, factorJointLaw, factorScoreKernel]
  exact h

/-! ### The covariance form and the precision form of the score matrix

`BKM` gives the factor-score matrix in two shapes — `Λ′Σ⁻¹` (covariance form, Eq. (3.64)
left) and `(I + Γ)⁻¹Λ′Ψ⁻¹` (precision form, Eq. (3.64) right, with `Γ = Λ′Ψ⁻¹Λ`) — and
Eq. (3.7)–(3.8) is the passage between them. That passage **is** Henderson's push-through
identity at `Z = Λ`, `G = Φ`, `R = Ψ`. -/

/-- `BKM`'s `Γ = Λ′Ψ⁻¹Λ` (`BKM` Eq. (3.9)). **Symbol warning:** in `BKM` ch. 3, `Γ` is this
matrix and `Φ` denotes the *correlation matrix of the latent variables* (Eq. (3.56)); the two
must not be confused.

*Edge behavior:* `Matrix.inv` is `0` at a singular `Ψ`, in which case `Γ = 0`; the theorems
below carry `Ψ.PosDef`. -/
noncomputable def gammaMatrix (P : FactorParams p q) : Matrix (Fin q) (Fin q) ℝ :=
  P.loadingᵀ * P.uniqueCov⁻¹ * P.loading

/-- **`BKM` Eq. (3.7)–(3.8), general `Φ`** — the covariance form of the factor-score matrix
equals its precision form. This is **exactly** Henderson's push-through identity
(`Hen50`; Searle–Casella–McCulloch §7.6) at `Z = Λ`, `G = Φ`, `R = Ψ`. -/
theorem condMeanMatrix_factorScores_precision (P : FactorParams p q)
    -- USER-INPUT: positive-definite variance components (both inverses must exist);
    -- BKM Eq. (3.7)–(3.8)
    (hΦ : P.factorCov.PosDef) (hΨ : P.uniqueCov.PosDef) :
    P.factorCov * P.loadingᵀ * (factorCovariance P)⁻¹
      = (gammaMatrix P + P.factorCov⁻¹)⁻¹ * P.loadingᵀ * P.uniqueCov⁻¹ :=
  MixedEffects.pushThrough P.loading P.factorCov P.uniqueCov hΦ hΨ

/-- **`BKM` Eq. (3.64) verbatim** — at the book's normalization `Φ = I`, the regression-score
matrix is `C = Λ′Σ⁻¹ = (I + Γ)⁻¹Λ′Ψ⁻¹`. The `Φ = I` case of
`condMeanMatrix_factorScores_precision`. -/
theorem condMeanMatrix_factorScores_standardized (P : FactorParams p q)
    -- USER-INPUT: BKM's normalization y ∼ N_q(0, I); BKM Eq. (3.2)
    (hP : IsStandardized P)
    -- USER-INPUT: nonsingular specific-factor covariance; BKM Eq. (3.64)
    (hΨ : P.uniqueCov.PosDef) :
    P.loadingᵀ * (factorCovariance P)⁻¹
      = (1 + gammaMatrix P)⁻¹ * P.loadingᵀ * P.uniqueCov⁻¹ := by
  have hΦ : P.factorCov.PosDef := by rw [hP]; exact Matrix.PosDef.one
  have h := condMeanMatrix_factorScores_precision P hΦ hΨ
  rw [hP, inv_one, Matrix.one_mul, add_comm (gammaMatrix P) 1] at h
  exact h

/-- LEAN-ONLY: the joint covariance of `(x, y)` is positive semidefinite, exhibited as
`C Φ Cᵀ + D Ψ Dᵀ` with `C = [Λ; I]` and `D = [I; 0]`. -/
private theorem posSemidef_factorJoint (P : FactorParams p q)
    (hΦ : P.factorCov.PosSemidef) (hΨ : P.uniqueCov.PosSemidef) :
    (Matrix.fromBlocks (factorCovariance P) (P.loading * P.factorCov)
      (P.loading * P.factorCov)ᵀ P.factorCov).PosSemidef := by
  have hΦT : P.factorCovᵀ = P.factorCov := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hΦ.1
  have hC : Matrix.PosSemidef
      (Matrix.fromRows P.loading (1 : Matrix (Fin q) (Fin q) ℝ) * P.factorCov
        * (Matrix.fromRows P.loading (1 : Matrix (Fin q) (Fin q) ℝ))ᵀ) := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hΦ.mul_mul_conjTranspose_same (Matrix.fromRows P.loading (1 : Matrix (Fin q) (Fin q) ℝ))
  have hD : Matrix.PosSemidef
      (Matrix.fromRows (1 : Matrix (Fin p) (Fin p) ℝ) (0 : Matrix (Fin q) (Fin p) ℝ)
        * P.uniqueCov
        * (Matrix.fromRows (1 : Matrix (Fin p) (Fin p) ℝ)
            (0 : Matrix (Fin q) (Fin p) ℝ))ᵀ) := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hΨ.mul_mul_conjTranspose_same
        (Matrix.fromRows (1 : Matrix (Fin p) (Fin p) ℝ) (0 : Matrix (Fin q) (Fin p) ℝ))
  have hCeq : Matrix.fromRows P.loading (1 : Matrix (Fin q) (Fin q) ℝ) * P.factorCov
        * (Matrix.fromRows P.loading (1 : Matrix (Fin q) (Fin q) ℝ))ᵀ
      = Matrix.fromBlocks (P.loading * P.factorCov * P.loadingᵀ) (P.loading * P.factorCov)
          (P.factorCov * P.loadingᵀ) P.factorCov := by
    rw [Matrix.fromRows_mul, Matrix.transpose_fromRows, Matrix.fromRows_mul,
      Matrix.mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_fromCols_eq_fromBlocks]
    simp
  have hDeq : Matrix.fromRows (1 : Matrix (Fin p) (Fin p) ℝ) (0 : Matrix (Fin q) (Fin p) ℝ)
        * P.uniqueCov
        * (Matrix.fromRows (1 : Matrix (Fin p) (Fin p) ℝ) (0 : Matrix (Fin q) (Fin p) ℝ))ᵀ
      = Matrix.fromBlocks P.uniqueCov 0 0 0 := by
    rw [Matrix.fromRows_mul, Matrix.transpose_fromRows, Matrix.fromRows_mul,
      Matrix.mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_fromCols_eq_fromBlocks]
    simp
  have hsum : Matrix.fromRows P.loading (1 : Matrix (Fin q) (Fin q) ℝ) * P.factorCov
        * (Matrix.fromRows P.loading (1 : Matrix (Fin q) (Fin q) ℝ))ᵀ
      + Matrix.fromRows (1 : Matrix (Fin p) (Fin p) ℝ) (0 : Matrix (Fin q) (Fin p) ℝ)
        * P.uniqueCov
        * (Matrix.fromRows (1 : Matrix (Fin p) (Fin p) ℝ) (0 : Matrix (Fin q) (Fin p) ℝ))ᵀ
      = Matrix.fromBlocks (factorCovariance P) (P.loading * P.factorCov)
          (P.loading * P.factorCov)ᵀ P.factorCov := by
    rw [hCeq, hDeq, Matrix.fromBlocks_add, factorCovariance_eq, Matrix.transpose_mul, hΦT]
    simp
  rw [← hsum]
  exact hC.add hD

/-- The posterior covariance is a genuine covariance — the Schur complement of a joint
covariance. -/
theorem posSemidef_condCovMatrix_factorScores (P : FactorParams p q)
    -- USER-INPUT: genuine covariance parameters; BKM Eq. (3.1)–(3.2)
    (hΦ : P.factorCov.PosSemidef) (hΨ : P.uniqueCov.PosSemidef)
    -- USER-INPUT: nondegenerate observed covariance; BKM Eq. (3.6)
    (hSig : (factorCovariance P).PosDef) :
    (condCovMatrix (factorCovariance P) (P.loading * P.factorCov) P.factorCov).PosSemidef :=
  posSemidef_condCovMatrix (posSemidef_factorJoint P hΦ hΨ) hSig

end StatLean.StatisticalModels.FactorModels
