module
public import StatLean.StatisticalModels.MixedEffects.Defs
public import StatLean.StatisticalModels.Gaussian.Affine
public import Mathlib.LinearAlgebra.Matrix.IsDiag

@[expose] public section

/-!
# The linear factor model — the latent-variable data model

The classical linear factor model in its **latent-variable form**
`x = μ + Λ y + e` (`BKM` (3.3)), with the latent-factor law `F` and the specific-factor
(error) law `E` **arbitrary** — Gaussianity is never baked in (the Gaussian case is one
instantiation, in `FactorModels.Gaussian`), matching the area rule that models capture
structure, not parametric families:

* `FactorParams p q` — the constitutive parameter quadruple `(μ, Λ, Φ, Ψ)`;
* `IsStandardized` / `HasDiagonalUniqueness` / `IsProperFactorParams` — the validity
  predicates, kept **outside** the structure (a loading matrix with a non-PSD `Φ` is still a
  parameter tuple; PSD is regularity, not constitutive);
* `factorLaw P F E` — the observed law: the latent law `F` mixed through the affine
  measurement kernel `y ↦ law of (Λ y + μ + ξ)`, `ξ ∼ E` (`BKM` (3.1)–(3.3));
* `factorDesign P` — the same model read as a `MixedEffects.LMMDesign` with fixed-effects
  design `1` and random-effects design `Λ`;
* `factorCovariance P = Λ Φ Λᵀ + Ψ` and `commonCovariance P = Λ Φ Λᵀ` — the *parameter-side*
  matrices; that they are the moments of `factorLaw` is `FactorModels.Moments`;
* `RealizesFactorParams P F E` — the compatibility predicate saying the two free laws
  actually carry the parameters `(Φ, Ψ)` and are centered.

**Reference.** D. Bartholomew, M. Knott, and I. Moustaki, *Latent Variable Models and Factor
Analysis: A Unified Approach*, 3rd ed., Wiley, 2011, §3.2, Eq. (3.1)–(3.3) (the normal linear
factor model), Eq. (3.12) (the covariance decomposition) (`BKM`).

**Proof formalization notes.** Definitions and `rfl`-level lemmas only.
*Book vs Lean:* `BKM` fixes the latent law at `y ∼ N_q(0, I)` (Eq. (3.2)), i.e. `Φ = I`,
and states the covariance decomposition as `Σ = Λ Λ′ + Ψ` (Eq. (3.12)); the general
correlated-factor form `Σ = Λ Φ Λ′ + Ψ` is **our** generalization (Eq. (3.12) is recovered as
the corollary at `Φ = I`). *Junk values:* `factorLaw` is a probability measure exactly when `F`
and `E` are (instance below); for non-s-finite `F`/`E` the kernel composition is the usual
`Measure.bind` junk. `Matrix.inv` is `0` at singular matrices, so every statement mentioning
`(factorCovariance P)⁻¹` carries an explicit invertibility hypothesis.

**Bibliographic comments.** The factor model is C. Spearman, "'General intelligence',
objectively determined and measured," *Amer. J. Psychol.* **15** (1904), 201–292 (the
one-factor case) and L. L. Thurstone, *Multiple-Factor Analysis*, Univ. Chicago Press, 1947
(the multi-factor case); the modern latent-variable presentation followed here is `BKM` ch. 3.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.FactorModels

open StatLean.StatisticalModels

/-! ### The parameter tuple -/

/-- The **parameters of a linear factor model** (`BKM` §3.2, Eq. (3.1)–(3.3)): mean vector
`μ`, `p × q` loading matrix `Λ`, latent-factor covariance `Φ`, specific-factor (uniqueness)
covariance `Ψ`.

Positive semidefiniteness of `Φ` and `Ψ` and diagonality of `Ψ` are **not** fields: `BKM`
allows one to write down and manipulate a loading/covariance tuple before checking them, and
the rotation calculus needs to produce tuples first and verify them second. They are the
predicates `IsProperFactorParams` / `HasDiagonalUniqueness` below. -/
structure FactorParams (p q : ℕ) where
  /-- Constitutive (`BKM` Eq. (3.3)): the mean vector `μ` of the observed vector `x`. -/
  μ : EuclideanSpace ℝ (Fin p)
  /-- Constitutive (`BKM` Eq. (3.1), (3.3)): the `p × q` matrix `Λ` of factor loadings. -/
  loading : Matrix (Fin p) (Fin q) ℝ
  /-- Constitutive (`BKM` Eq. (3.2), generalized): the `q × q` covariance matrix `Φ` of the
  latent factors. `BKM` fixes `Φ = I`; carrying it as a parameter is our generalization (and
  is what the oblique-rotation discussion of `BKM` §3.13.2, Eq. (3.56) needs). -/
  factorCov : Matrix (Fin q) (Fin q) ℝ
  /-- Constitutive (`BKM` Eq. (3.1)): the `p × p` covariance matrix `Ψ` of the specific
  factors. `BKM` takes it diagonal; diagonality is the predicate
  `HasDiagonalUniqueness`. -/
  uniqueCov : Matrix (Fin p) (Fin p) ℝ

variable {p q : ℕ}

/-! ### Validity predicates -/

/-- **Standardized (orthogonal) factors**: `Φ = I` — `BKM`'s own normalization
(Eq. (3.2), `y ∼ N_q(0, I)`). -/
def IsStandardized (P : FactorParams p q) : Prop :=
  P.factorCov = 1

/-- **Diagonal uniqueness**: `Ψ` is diagonal, i.e. the specific factors are uncorrelated
across coordinates — `BKM`'s conditional-independence assumption (Eq. (1.9), §1.4;
Eq. (3.1)). -/
def HasDiagonalUniqueness (P : FactorParams p q) : Prop :=
  Matrix.IsDiag P.uniqueCov

/-- **Proper parameters**: `Φ` and `Ψ` are genuine covariance matrices. Regularity, not
constitutive — hence a predicate on `FactorParams`, not fields of it. -/
def IsProperFactorParams (P : FactorParams p q) : Prop :=
  P.factorCov.PosSemidef ∧ P.uniqueCov.PosSemidef

theorem IsProperFactorParams.posSemidef_factorCov {P : FactorParams p q}
    (h : IsProperFactorParams P) : P.factorCov.PosSemidef := h.1

theorem IsProperFactorParams.posSemidef_uniqueCov {P : FactorParams p q}
    (h : IsProperFactorParams P) : P.uniqueCov.PosSemidef := h.2

/-! ### Parameter-side covariance matrices -/

/-- The **common part** `Λ Φ Λᵀ` of the factor covariance — the variance of `x` explained by
the latent factors (`BKM` Eq. (3.12), left summand; at `Φ = I` this is `Λ Λ′`). -/
noncomputable def commonCovariance (P : FactorParams p q) : Matrix (Fin p) (Fin p) ℝ :=
  P.loading * P.factorCov * P.loadingᵀ

/-- The **factor covariance** `Σ = Λ Φ Λᵀ + Ψ` (`BKM` Eq. (3.12) at `Φ = I`; the general `Φ`
is our generalization). This is a *parameter-side* definition: that it is the covariance
matrix of `factorLaw` is `FactorModels.Moments.covMatrix_factorLaw_eq_factorCovariance`. -/
noncomputable def factorCovariance (P : FactorParams p q) : Matrix (Fin p) (Fin p) ℝ :=
  P.loading * P.factorCov * P.loadingᵀ + P.uniqueCov

theorem factorCovariance_eq_commonCovariance_add (P : FactorParams p q) :
    factorCovariance P = commonCovariance P + P.uniqueCov := rfl

theorem commonCovariance_eq (P : FactorParams p q) :
    commonCovariance P = P.loading * P.factorCov * P.loadingᵀ := rfl

theorem factorCovariance_eq (P : FactorParams p q) :
    factorCovariance P = P.loading * P.factorCov * P.loadingᵀ + P.uniqueCov := rfl

/-! ### The observed law -/

/-- LEAN-ONLY: the loading matrix acts measurably on Euclidean space (a linear map on a
finite-dimensional space is continuous). -/
theorem measurable_loadingAct (Λ : Matrix (Fin p) (Fin q) ℝ) :
    Measurable fun y : EuclideanSpace ℝ (Fin q) =>
      Matrix.toEuclideanLin (𝕜 := ℝ) Λ y :=
  ((Matrix.toEuclideanLin (𝕜 := ℝ) Λ).continuous_of_finiteDimensional).measurable

/-- The **measurement kernel** `y ↦ law of (Λ y + μ + ξ)`, `ξ ∼ E`: `BKM`'s conditional model
`x ∣ y ∼ N_p(μ + Λ y, Ψ)` (Eq. (3.1)) with the conditional law's shape left free (Gaussian
`E` recovers (3.1) exactly). -/
noncomputable def measurementKernel (P : FactorParams p q)
    (E : Measure (EuclideanSpace ℝ (Fin p))) :
    Kernel (EuclideanSpace ℝ (Fin q)) (EuclideanSpace ℝ (Fin p)) :=
  affineNoiseKernel E (fun y => Matrix.toEuclideanLin (𝕜 := ℝ) P.loading y)
    (measurable_loadingAct P.loading) P.μ

instance (P : FactorParams p q) (E : Measure (EuclideanSpace ℝ (Fin p)))
    [IsProbabilityMeasure E] : IsMarkovKernel (measurementKernel P E) := by
  rw [measurementKernel]; infer_instance

/-- The **observed law of the linear factor model** (`BKM` Eq. (3.3)/(3.5)): the latent law
`F` marginalized through the measurement kernel, i.e. the law of `x = μ + Λ y + e` with
`y ∼ F` and `e ∼ E` independent. The latent and error laws are free parameters; Gaussianity
enters only in `FactorModels.Gaussian`.

*Edge behavior:* a probability measure exactly when `F` and `E` are (instance below); for
non-s-finite arguments this is the usual `Measure.bind` junk. -/
noncomputable def factorLaw (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p))) : Measure (EuclideanSpace ℝ (Fin p)) :=
  measurementKernel P E ∘ₘ F

instance (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure F]
    [IsProbabilityMeasure E] : IsProbabilityMeasure (factorLaw P F E) := by
  rw [factorLaw]; infer_instance

@[simp]
theorem measurementKernel_apply (P : FactorParams p q)
    (E : Measure (EuclideanSpace ℝ (Fin p))) [SFinite E] (y : EuclideanSpace ℝ (Fin q)) :
    measurementKernel P E y
      = E.map fun z => Matrix.toEuclideanLin (𝕜 := ℝ) P.loading y + P.μ + z := by
  simp [measurementKernel]

/-! ### The bridge design

The factor model is the linear mixed model with fixed-effects design `1`, fixed effect `μ`,
and random-effects design `Λ`; the identity of the two models is `FactorModels.Bridge`. -/

/-- The factor model read as a **linear mixed-effects design**: `X = 1`, `Z = Λ`
(`LW82` Eq. (1.1) instantiated at `BKM` Eq. (3.3)). -/
def factorDesign (P : FactorParams p q) : MixedEffects.LMMDesign p p q :=
  ⟨1, P.loading⟩

@[simp]
theorem factorDesign_X (P : FactorParams p q) : (factorDesign P).X = 1 := rfl

@[simp]
theorem factorDesign_Z (P : FactorParams p q) : (factorDesign P).Z = P.loading := rfl

/-! ### Compatibility of the free laws with the parameters -/

/-- The latent law `F` and the specific-factor law `E` **realize** the parameters of `P`:
both are centered and carry the declared covariances (`BKM` Eq. (3.2)–(3.3): `E y = 0`,
`cov(y) = Φ`, `E e = 0`, `cov(e) = Ψ`). Without this, `factorLaw P F E` ignores `P.factorCov`
and `P.uniqueCov` entirely — the parameter tuple and the two laws are independent inputs. -/
def RealizesFactorParams (P : FactorParams p q) (F : Measure (EuclideanSpace ℝ (Fin q)))
    (E : Measure (EuclideanSpace ℝ (Fin p))) : Prop :=
  meanVec F = 0 ∧ meanVec E = 0 ∧ covMatrix F = P.factorCov ∧ covMatrix E = P.uniqueCov

theorem RealizesFactorParams.meanVec_latent {P : FactorParams p q}
    {F : Measure (EuclideanSpace ℝ (Fin q))} {E : Measure (EuclideanSpace ℝ (Fin p))}
    (h : RealizesFactorParams P F E) : meanVec F = 0 := h.1

theorem RealizesFactorParams.meanVec_error {P : FactorParams p q}
    {F : Measure (EuclideanSpace ℝ (Fin q))} {E : Measure (EuclideanSpace ℝ (Fin p))}
    (h : RealizesFactorParams P F E) : meanVec E = 0 := h.2.1

theorem RealizesFactorParams.covMatrix_latent {P : FactorParams p q}
    {F : Measure (EuclideanSpace ℝ (Fin q))} {E : Measure (EuclideanSpace ℝ (Fin p))}
    (h : RealizesFactorParams P F E) : covMatrix F = P.factorCov := h.2.2.1

theorem RealizesFactorParams.covMatrix_error {P : FactorParams p q}
    {F : Measure (EuclideanSpace ℝ (Fin q))} {E : Measure (EuclideanSpace ℝ (Fin p))}
    (h : RealizesFactorParams P F E) : covMatrix E = P.uniqueCov := h.2.2.2

end StatLean.StatisticalModels.FactorModels
