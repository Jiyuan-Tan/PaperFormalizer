module
public import StatLean.StatisticalModels.FactorModels.Rotation
public import StatLean.StatisticalModels.Identifiability.Transfer

@[expose] public section

/-!
# What a factor model does and does not identify

The rotational indeterminacy of `FactorModels.Rotation` is exactly an identifiability
failure, and it is stated here against the library's own predicates
(`StatLean.PointEstimation.Identifiable` and `StatisticalModels.IdentifiesTarget`).

**Not identified — the loadings.**

* `loadingModel μ Ψ` — the normal factor model with `μ` and `Ψ` held fixed and standardized
  factors, indexed by the loading matrix alone;
* `loadingModel_mul_orthogonal` — `Λ` and `Λ Q` index the *same* law for every orthogonal
  `Q` (for `q ≥ 2` these are genuine rotations; `Q = -I` is the sign flip that already
  defeats identifiability at `q = 1`);
* **`not_identifiable_loadingModel`** — hence `¬ Identifiable (loadingModel μ Ψ)` as soon as
  `p, q ≥ 1`, with an explicit witness pair, and the model-level companion
  `not_identifiable_properGaussianFactorModel`.

**Identified — the covariance decomposition.**

* **`identifiesTarget_loadingModel_commonCovariance`** — `Λ Λᵀ` *is* identified;
* `identifiesTarget_factorCovariance` and `identifiesTarget_mean` — over proper parameters,
  `Σ = Λ Φ Λᵀ + Ψ` and `μ` are identified. (Splitting `Σ` into `Λ Φ Λᵀ` and `Ψ` is a further
  question — the counting condition of `BKM` Eq. (3.50)–(3.51) — and is not claimed here.)

**Reference.** D. Bartholomew, M. Knott, and I. Moustaki, *Latent Variable Models and Factor
Analysis: A Unified Approach*, 3rd ed., Wiley, 2011, §3.12.1, pp. 64–65 and
Eq. (3.50)–(3.51) (the parameter count); §2.11, Eq. (2.24)–(2.26) and §3.13.1 (rotation);
§3.3, p. 50 (`Λ′Ψ⁻¹Λ` diagonal "removes the freedom to arbitrarily rotate `Λ`") (`BKM`);
E. L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed., Springer, 1998, §1.5
(identifiability of a parametrization) (`TPE2 §1.5`).

**Proof formalization notes.** The negative results run on an explicit witness pair (the
all-ones loading matrix and its negative, distinct because `p, q ≥ 1` and `ℝ` has
characteristic zero); the positive ones exhibit the representing functional `covMatrix`
(resp. `meanVec`) of the observed law.
*Junk values:* the positive results are stated over the **subtype of proper parameters**, and
this is not cosmetic — at a non-PSD `Φ` the Gaussian collapses to a Dirac and the law no
longer determines `factorCovariance` (two parameters with `Φ = 0` and with a non-PSD `Φ`
share a law but not a target), so the unrestricted statement is **false**.
*Book vs Lean:* `BKM` treats identifiability by counting free parameters
(Eq. (3.50)–(3.51)); the counting condition is necessary but not sufficient and is not
formalized here — what is formalized is the exact indeterminacy group and the identified
functional.

**Bibliographic comments.** The rotation problem is Thurstone's (1947); the modern
identification-by-restriction treatments (`Λ′Ψ⁻¹Λ` diagonal, or a triangular `Λ`) are
surveyed in `BKM` §3.3 and §3.12.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.FactorModels

open StatLean.StatisticalModels StatLean.PointEstimation

variable {p q : ℕ}

/-! ### The loading-indexed model -/

/-- The **normal factor model indexed by its loadings**, with the mean `μ`, standardized
factors (`Φ = I`, `BKM` Eq. (3.2)) and the specific-factor covariance `Ψ` held fixed. This is
the family in which "the loadings are not identified" is a statement about a statistical
model rather than about matrices. -/
noncomputable def loadingModel (p q : ℕ) (μ : EuclideanSpace ℝ (Fin p))
    (Ψ : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin q) ℝ → Measure (EuclideanSpace ℝ (Fin p)) :=
  fun Λ => gaussianFactorModel p q ⟨μ, Λ, 1, Ψ⟩

/-- The loading model is the normal law with covariance `Λ Λᵀ + Ψ` (`BKM` Eq. (3.5)). -/
theorem loadingModel_eq_multivariateGaussian (μ : EuclideanSpace ℝ (Fin p))
    {Ψ : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : Ψ.PosSemidef) (Λ : Matrix (Fin p) (Fin q) ℝ) :
    loadingModel p q μ Ψ Λ = multivariateGaussian μ (Λ * Λᵀ + Ψ) := by
  have hP : IsProperFactorParams (⟨μ, Λ, 1, Ψ⟩ : FactorParams p q) :=
    ⟨Matrix.PosSemidef.one, hΨ⟩
  rw [loadingModel, gaussianFactorModel_eq_multivariateGaussian _ hP]
  congr 1
  change Λ * 1 * Λᵀ + Ψ = Λ * Λᵀ + Ψ
  rw [Matrix.mul_one]

/-- LEAN-ONLY: the covariance matrix of the loading model, the representing functional used
by the positive results below. -/
private theorem identifiesTarget_loadingModel_covariance_aux
    (μ : EuclideanSpace ℝ (Fin p)) {Ψ : Matrix (Fin p) (Fin p) ℝ}
    (hΨ : Ψ.PosSemidef) (Λ : Matrix (Fin p) (Fin q) ℝ) :
    covMatrix (loadingModel p q μ Ψ Λ) = Λ * Λᵀ + Ψ := by
  have hPSD : (Λ * Λᵀ + Ψ).PosSemidef := by
    refine Matrix.PosSemidef.add ?_ hΨ
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose Λ
  rw [loadingModel_eq_multivariateGaussian μ hΨ, covMatrix_multivariateGaussian _ _ hPSD]

/-! ### The loadings are not identified -/

/-- **The rotational indeterminacy, model form** (`BKM` §2.11, Eq. (2.24)–(2.26); §3.13.1):
`Λ` and `Λ Q` index the *same* law for every orthogonal `Q`. For `q ≥ 2` these include
genuine rotations; `Q = -I` is the sign flip below. -/
theorem loadingModel_mul_orthogonal (μ : EuclideanSpace ℝ (Fin p))
    {Ψ : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : Ψ.PosSemidef) (Λ : Matrix (Fin p) (Fin q) ℝ) {Q : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: `Q` is orthogonal; BKM §2.11, Eq. (2.24)
    (hQ : Q * Qᵀ = 1) :
    loadingModel p q μ Ψ (Λ * Q) = loadingModel p q μ Ψ Λ := by
  rw [loadingModel_eq_multivariateGaussian μ hΨ, loadingModel_eq_multivariateGaussian μ hΨ]
  congr 1
  exact congrArg (· + Ψ)
    (loading_mul_transpose_rotateParams_orthogonal (⟨μ, Λ, 1, Ψ⟩ : FactorParams p q) hQ)

/-- **The sign flip** — the `q = 1` instance of the rotational indeterminacy, and the witness
used below at every `q`. -/
theorem loadingModel_neg (μ : EuclideanSpace ℝ (Fin p)) {Ψ : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : Ψ.PosSemidef) (Λ : Matrix (Fin p) (Fin q) ℝ) :
    loadingModel p q μ Ψ (-Λ) = loadingModel p q μ Ψ Λ := by
  have hQ : (-1 : Matrix (Fin q) (Fin q) ℝ) * (-1 : Matrix (Fin q) (Fin q) ℝ)ᵀ = 1 := by
    rw [Matrix.transpose_neg, Matrix.transpose_one, neg_mul_neg, Matrix.one_mul]
  have h := loadingModel_mul_orthogonal μ hΨ Λ hQ
  rwa [Matrix.mul_neg, Matrix.mul_one] at h

/-- **HEADLINE (negative) — the loadings of a factor model are not identifiable**
(`BKM` §3.12.1, pp. 64–65): with at least one observed variable and at least one factor, two
distinct loading matrices index the same observed law. Stated against the library predicate
`StatLean.PointEstimation.Identifiable`. -/
theorem not_identifiable_loadingModel (μ : EuclideanSpace ℝ (Fin p))
    {Ψ : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : Ψ.PosSemidef)
    -- USER-INPUT: a nondegenerate model — at least one observed variable and one factor;
    -- at `p = 0` or `q = 0` there is only one loading matrix and the model is vacuously
    -- identifiable; BKM §3.12.1
    (hp : 0 < p) (hq : 0 < q) :
    ¬ Identifiable (loadingModel p q μ Ψ) := by
  intro hid
  -- the witness pair: the all-ones loading matrix and its negative (the sign flip)
  have h : -(Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin p) (Fin q) ℝ)
      = (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin p) (Fin q) ℝ) :=
    hid (loadingModel_neg μ hΨ _)
  have h1 : (-(Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin p) (Fin q) ℝ))
        ⟨0, hp⟩ ⟨0, hq⟩
      = (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin p) (Fin q) ℝ) ⟨0, hp⟩ ⟨0, hq⟩ := by
    rw [h]
  norm_num at h1

/-! ### What *is* identified -/

/-- **HEADLINE (positive) — the common covariance is identified**: `Λ Λᵀ` is a functional of
the observed law even though `Λ` is not (`BKM` §3.12.1). -/
theorem identifiesTarget_loadingModel_commonCovariance (μ : EuclideanSpace ℝ (Fin p))
    {Ψ : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : Ψ.PosSemidef) :
    IdentifiesTarget (loadingModel p q μ Ψ) fun Λ : Matrix (Fin p) (Fin q) ℝ => Λ * Λᵀ := by
  refine identifiesTarget_of_rep (fun Q => covMatrix Q - Ψ) fun Λ => ?_
  simp only [identifiesTarget_loadingModel_covariance_aux μ hΨ Λ, add_sub_cancel_right]

/-- The full covariance `Λ Λᵀ + Ψ` is identified in the loading model. -/
theorem identifiesTarget_loadingModel_covariance (μ : EuclideanSpace ℝ (Fin p))
    {Ψ : Matrix (Fin p) (Fin p) ℝ}
    -- USER-INPUT: a genuine specific-factor covariance; BKM Eq. (3.1)
    (hΨ : Ψ.PosSemidef) :
    IdentifiesTarget (loadingModel p q μ Ψ)
      fun Λ : Matrix (Fin p) (Fin q) ℝ => Λ * Λᵀ + Ψ :=
  identifiesTarget_of_rep covMatrix (identifiesTarget_loadingModel_covariance_aux μ hΨ)

/-! ### The model over the full (proper) parameter space

`gaussianFactorModel` is only a `BKM`-model at proper parameters — at a non-PSD `Φ` or `Ψ`
the `multivariateGaussian` junk value (a Dirac mass) takes over and the law stops determining
`factorCovariance`. The identified-target statements are therefore over the subtype. -/

/-- The normal factor model restricted to **proper** parameter tuples. -/
noncomputable def properGaussianFactorModel (p q : ℕ) :
    {P : FactorParams p q // IsProperFactorParams P} → Measure (EuclideanSpace ℝ (Fin p)) :=
  fun P => gaussianFactorModel p q P.1

/-- **`Σ = Λ Φ Λᵀ + Ψ` is identified** — it is the covariance matrix of the observed law
(`BKM` Eq. (3.12), general `Φ`). -/
theorem identifiesTarget_factorCovariance :
    IdentifiesTarget (properGaussianFactorModel p q)
      fun P : {P : FactorParams p q // IsProperFactorParams P} => factorCovariance P.1 :=
  identifiesTarget_of_rep covMatrix fun P => covMatrix_gaussianFactorModel P.1 P.2

/-- **`μ` is identified** — it is the mean vector of the observed law (`BKM` Eq. (3.5)). -/
theorem identifiesTarget_mean :
    IdentifiesTarget (properGaussianFactorModel p q)
      fun P : {P : FactorParams p q // IsProperFactorParams P} => P.1.μ :=
  identifiesTarget_of_rep meanVec fun P => meanVec_gaussianFactorModel P.1 P.2

/-- **The parameter tuple itself is not identified** (`BKM` §3.12.1, pp. 64–65) — the
model-level companion of `not_identifiable_loadingModel`. -/
theorem not_identifiable_properGaussianFactorModel
    -- USER-INPUT: a nondegenerate model — at least one observed variable and one factor;
    -- BKM §3.12.1
    (hp : 0 < p) (hq : 0 < q) :
    ¬ Identifiable (properGaussianFactorModel p q) := by
  intro hid
  have hprop : ∀ M : Matrix (Fin p) (Fin q) ℝ,
      IsProperFactorParams (⟨0, M, 1, 0⟩ : FactorParams p q) :=
    fun _ => ⟨Matrix.PosSemidef.one, Matrix.PosSemidef.zero⟩
  -- the sign flip at `μ = 0`, `Φ = I`, `Ψ = 0` — a proper parameter pair with one law
  have hlaw : properGaussianFactorModel p q
        ⟨⟨0, -(Matrix.of fun _ _ => (1 : ℝ)), 1, 0⟩, hprop _⟩
      = properGaussianFactorModel p q
        ⟨⟨0, Matrix.of fun _ _ => (1 : ℝ), 1, 0⟩, hprop _⟩ :=
    loadingModel_neg (0 : EuclideanSpace ℝ (Fin p)) Matrix.PosSemidef.zero _
  have h : -(Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin p) (Fin q) ℝ)
      = (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin p) (Fin q) ℝ) :=
    congrArg (fun P => P.1.loading) (hid hlaw)
  have h1 : (-(Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin p) (Fin q) ℝ))
        ⟨0, hp⟩ ⟨0, hq⟩
      = (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Fin p) (Fin q) ℝ) ⟨0, hp⟩ ⟨0, hq⟩ := by
    rw [h]
  norm_num at h1

end StatLean.StatisticalModels.FactorModels
