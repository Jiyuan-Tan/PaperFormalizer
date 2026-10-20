module
public import StatLean.StatisticalModels.FactorModels.Bridge
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# Moments of the linear factor model — the covariance decomposition and its rank

The moment theory of `factorLaw`, in the declared parameters:

* `meanVec_factorLaw_of_realizes` — `E x = μ`;
* **`covMatrix_factorLaw_eq_factorCovariance`** — `Σ = Λ Φ Λᵀ + Ψ`, the factor-analytic
  covariance decomposition, for latent and specific laws realizing the parameters `(Φ, Ψ)`;
* `posSemidef_commonCovariance` / `posSemidef_factorCovariance` — the common part `Λ Φ Λᵀ`
  and the total `Σ` are genuine covariance matrices;
* **`rank_commonCovariance_le`** — `rank(Λ Φ Λᵀ) ≤ q`: the common part is at most as rich as
  the number of factors. This is the structural content of factor analysis (and the reason
  the parameter count of `BKM` Eq. (3.50)–(3.51) is what it is).

**Reference.** D. Bartholomew, M. Knott, and I. Moustaki, *Latent Variable Models and Factor
Analysis: A Unified Approach*, 3rd ed., Wiley, 2011, Eq. (3.10) (the variance decomposition),
Eq. (3.12) (`Σ = Λ Λ′ + Ψ`), §3.12.1, Eq. (3.50)–(3.51) (the parameter count) (`BKM`).

**Proof formalization notes.** *Book vs Lean:* `BKM` states Eq. (3.12) in the orthogonal case
`Φ = I` (its model fixes `y ∼ N_q(0, I)` at Eq. (3.2)); the general-`Φ` form below is our
generalization, with (3.12) the corollary at `IsStandardized P`.

**Bibliographic comments.** The decomposition `Σ = Λ Λ′ + Ψ` with `Ψ` diagonal and `Λ` of
rank `q` is Spearman's (1904) and Thurstone's (1947) organizing identity; the rank condition
is what distinguishes a `q`-factor model from an unrestricted covariance.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.FactorModels

open StatLean.StatisticalModels

variable {p q : ℕ}

/-- **First moment in the declared parameters** (`BKM` Eq. (3.3)): the observed mean is `μ`
whenever the latent and specific factors realize the parameters. -/
theorem meanVec_factorLaw_of_realizes (P : FactorParams p q)
    (F : Measure (EuclideanSpace ℝ (Fin q))) (E : Measure (EuclideanSpace ℝ (Fin p)))
    [IsProbabilityMeasure F] [IsProbabilityMeasure E]
    -- USER-INPUT: the free laws carry the declared (centered) parameters; BKM Eq. (3.2)–(3.3)
    (hPFE : RealizesFactorParams P F E)
    -- USER-INPUT: first moments exist; BKM Eq. (3.3)
    (hF1 : Integrable id F) (hE1 : Integrable id E) :
    meanVec (factorLaw P F E) = P.μ :=
  meanVec_factorLaw P F E hPFE.meanVec_latent hPFE.meanVec_error hF1 hE1

/-- **HEADLINE — the factor-analytic covariance decomposition** (`BKM` Eq. (3.12), general
`Φ`): `Σ = Λ Φ Λᵀ + Ψ`, for latent and specific laws realizing `(Φ, Ψ)`. -/
theorem covMatrix_factorLaw_eq_factorCovariance (P : FactorParams p q)
    (F : Measure (EuclideanSpace ℝ (Fin q))) (E : Measure (EuclideanSpace ℝ (Fin p)))
    [IsProbabilityMeasure F] [IsProbabilityMeasure E]
    -- USER-INPUT: the free laws carry the declared parameters; BKM Eq. (3.2)–(3.3)
    (hPFE : RealizesFactorParams P F E)
    -- USER-INPUT: second moments exist; BKM Eq. (3.3)
    (hF2 : MemLp id 2 F) (hE2 : MemLp id 2 E) :
    covMatrix (factorLaw P F E) = factorCovariance P := by
  rw [covMatrix_factorLaw P F E hF2 hE2, hPFE.covMatrix_latent, hPFE.covMatrix_error,
    factorCovariance_eq]

/-- `BKM` Eq. (3.12) verbatim: for **standardized** factors (`Φ = I`, the book's own
normalization at Eq. (3.2)) the decomposition reads `Σ = Λ Λ′ + Ψ`. -/
theorem factorCovariance_of_isStandardized (P : FactorParams p q)
    -- USER-INPUT: BKM's normalization y ∼ N_q(0, I); BKM Eq. (3.2)
    (hP : IsStandardized P) :
    factorCovariance P = P.loading * P.loadingᵀ + P.uniqueCov := by
  rw [factorCovariance_eq, hP, Matrix.mul_one]

/-- The **common part is a genuine covariance**: `Λ Φ Λᵀ ⪰ 0` whenever `Φ ⪰ 0`. -/
theorem posSemidef_commonCovariance (P : FactorParams p q)
    -- USER-INPUT: a genuine latent covariance parameter; BKM Eq. (3.2)
    (hΦ : P.factorCov.PosSemidef) :
    (commonCovariance P).PosSemidef := by
  simpa [commonCovariance, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hΦ.mul_mul_conjTranspose_same P.loading

/-- The **factor covariance is a genuine covariance**: `Λ Φ Λᵀ + Ψ ⪰ 0` for proper
parameters. -/
theorem posSemidef_factorCovariance (P : FactorParams p q)
    -- USER-INPUT: genuine covariance parameters; BKM Eq. (3.1)–(3.2)
    (hP : IsProperFactorParams P) :
    (factorCovariance P).PosSemidef :=
  MixedEffects.posSemidef_variance_components (factorDesign P) P.factorCov P.uniqueCov
    hP.posSemidef_factorCov hP.posSemidef_uniqueCov

/-- **The rank bound**: the common part of the factor covariance has rank at most the number
of factors `q`. This is the structural restriction a `q`-factor model imposes on `Σ` — for
`q < p` it is a genuine constraint, and it is what the parameter count of `BKM` §3.12.1
(Eq. (3.50)–(3.51)) measures. -/
theorem rank_commonCovariance_le (P : FactorParams p q) :
    (commonCovariance P).rank ≤ q := by
  rw [commonCovariance_eq]
  exact ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)).trans
    (Matrix.rank_le_width P.loading)

/-- The same bound stated on the loading matrix alone, the form the identifiability
discussion uses. -/
theorem rank_commonCovariance_le_rank_loading (P : FactorParams p q) :
    (commonCovariance P).rank ≤ P.loading.rank := by
  rw [commonCovariance_eq]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)

end StatLean.StatisticalModels.FactorModels
