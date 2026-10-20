module
public import StatLean.StatisticalModels.FactorModels.Communality
public import StatLean.StatisticalModels.FactorModels.Gaussian

@[expose] public section

/-!
# Rotation of the loadings — the factor model's exact reparameterization group

The loadings of a factor model are determined only up to a nonsingular change of basis in the
latent space: replacing `(Λ, Φ)` by `(Λ A, A⁻¹ Φ A⁻ᵀ)` leaves the observed model completely
unchanged. This file is the calculus of that reparameterization.

* `rotateParams P A` — the reparameterized tuple `(μ, Λ A, A⁻¹ Φ A⁻ᵀ, Ψ)`;
* **`factorCovariance_rotateParams`** — `Λ Φ Λᵀ` (hence `Σ`) is invariant for every
  nonsingular `A`;
* **`factorLaw_rotateParams`** — the observed law is invariant, once the latent law is
  transported by `A⁻¹` along with the parameters; and `gaussianFactorModel_rotateParams`,
  the Gaussian instance in which the transport is automatic;
* the **orthogonal specialization** for standardized factors (`BKM` §2.11, Eq. (2.24)–(2.26);
  §3.13.1): for `Q Qᵀ = I`, `Λ Q` has the same `Λ Λᵀ`, the same communalities and — with
  `Φ = I` — again standardized factors. Oblique rotations (`BKM` §3.13.2, Eq. (2.27)) are the
  general `A` case above, with the latent correlation matrix `Φ` changing accordingly.

**Reference.** D. Bartholomew, M. Knott, and I. Moustaki, *Latent Variable Models and Factor
Analysis: A Unified Approach*, 3rd ed., Wiley, 2011, §2.11, Eq. (2.24)–(2.26) (orthogonal
rotation of the loadings) and Eq. (2.27) (oblique rotation); §3.13.1–§3.13.2, Eq. (3.56);
§3.3, p. 50 (the normalization `Λ′Ψ⁻¹Λ` diagonal "removes the freedom to arbitrarily rotate
`Λ`") (`BKM`).

**Proof formalization notes.** The covariance invariance rests on `(A⁻¹)ᵀ Aᵀ = (A A⁻¹)ᵀ = 1`;
the law invariance on `(Λ A)(A⁻¹ y) = Λ y` inside the measurement kernel. For orthogonal `Q`
the inverse is the transpose. *Book vs Lean:* `BKM`'s model
fixes `Φ = I` and therefore discusses orthogonal rotation as the whole story (§3.13.1),
oblique rotation entering as a separate construction (§3.13.2); carrying `Φ` as a parameter
makes both the *same* statement at different `A`, which is why the general-`A` theorem comes
first here.

**Bibliographic comments.** Rotational indeterminacy is Thurstone's "simple structure"
problem (*Multiple-Factor Analysis*, 1947); the varimax criterion is H. F. Kaiser, "The
varimax criterion for analytic rotation in factor analysis," *Psychometrika* **23** (1958),
187–200. Only the indeterminacy itself — not any particular rotation criterion — is
formalized here.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.StatisticalModels.FactorModels

open StatLean.StatisticalModels

variable {p q : ℕ}

/-! ### The general (oblique) reparameterization -/

/-- The **rotated parameters** `(μ, Λ A, A⁻¹ Φ A⁻ᵀ, Ψ)` (`BKM` §2.11, Eq. (2.24)–(2.27)).

*Edge behavior:* `Matrix.inv` is `0` at singular `A`, so at a singular `A` this collapses the
latent covariance to `0`; every invariance statement below therefore carries
`IsUnit A.det`. -/
noncomputable def rotateParams (P : FactorParams p q) (A : Matrix (Fin q) (Fin q) ℝ) :
    FactorParams p q :=
  ⟨P.μ, P.loading * A, A⁻¹ * P.factorCov * (A⁻¹)ᵀ, P.uniqueCov⟩

@[simp]
theorem rotateParams_μ (P : FactorParams p q) (A : Matrix (Fin q) (Fin q) ℝ) :
    (rotateParams P A).μ = P.μ := rfl

@[simp]
theorem rotateParams_loading (P : FactorParams p q) (A : Matrix (Fin q) (Fin q) ℝ) :
    (rotateParams P A).loading = P.loading * A := rfl

@[simp]
theorem rotateParams_factorCov (P : FactorParams p q) (A : Matrix (Fin q) (Fin q) ℝ) :
    (rotateParams P A).factorCov = A⁻¹ * P.factorCov * (A⁻¹)ᵀ := rfl

@[simp]
theorem rotateParams_uniqueCov (P : FactorParams p q) (A : Matrix (Fin q) (Fin q) ℝ) :
    (rotateParams P A).uniqueCov = P.uniqueCov := rfl

/-- Rotation preserves properness: `A⁻¹ Φ A⁻ᵀ` is positive semidefinite whenever `Φ` is
(true for **every** `A`, singular or not). -/
theorem isProperFactorParams_rotateParams (P : FactorParams p q)
    (A : Matrix (Fin q) (Fin q) ℝ)
    -- USER-INPUT: genuine covariance parameters; BKM Eq. (3.1)–(3.2)
    (hP : IsProperFactorParams P) :
    IsProperFactorParams (rotateParams P A) := by
  refine ⟨?_, hP.2⟩
  simpa [rotateParams, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hP.1.mul_mul_conjTranspose_same A⁻¹

/-- **The common part is rotation invariant**: `(Λ A)(A⁻¹ Φ A⁻ᵀ)(Λ A)ᵀ = Λ Φ Λᵀ`
(`BKM` §2.11, Eq. (2.26)). -/
theorem commonCovariance_rotateParams (P : FactorParams p q)
    {A : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: the reparameterization is a change of basis of the latent space;
    -- BKM §2.11
    (hA : IsUnit A.det) :
    commonCovariance (rotateParams P A) = commonCovariance P := by
  have h2 : (A⁻¹)ᵀ * Aᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hA, Matrix.transpose_one]
  simp only [commonCovariance, rotateParams_loading, rotateParams_factorCov,
    Matrix.transpose_mul, Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ hA, ← Matrix.mul_assoc (A⁻¹)ᵀ, h2,
    Matrix.one_mul]

/-- **The factor covariance is rotation invariant**: `Σ` does not change under any
nonsingular reparameterization of the latent space (`BKM` §2.11, Eq. (2.26); §3.13). -/
theorem factorCovariance_rotateParams (P : FactorParams p q)
    {A : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: the reparameterization is a change of basis of the latent space;
    -- BKM §2.11
    (hA : IsUnit A.det) :
    factorCovariance (rotateParams P A) = factorCovariance P := by
  rw [factorCovariance_eq_commonCovariance_add, factorCovariance_eq_commonCovariance_add,
    commonCovariance_rotateParams P hA, rotateParams_uniqueCov]

/-- **The observed law is rotation invariant** — the exact statement, with the latent law
transported along with the parameters: `y ↦ A⁻¹ y` turns a draw from `F` into a draw from the
rotated latent law, and the two observed models coincide. No moment or Gaussianity
hypothesis is needed. -/
theorem factorLaw_rotateParams (P : FactorParams p q)
    (F : Measure (EuclideanSpace ℝ (Fin q))) (E : Measure (EuclideanSpace ℝ (Fin p)))
    {A : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: the reparameterization is a change of basis of the latent space;
    -- BKM §2.11
    (hA : IsUnit A.det) :
    factorLaw (rotateParams P A)
        (F.map fun y => Matrix.toEuclideanLin (𝕜 := ℝ) A⁻¹ y) E
      = factorLaw P F E := by
  have hg : Measurable fun y : EuclideanSpace ℝ (Fin q) =>
      Matrix.toEuclideanLin (𝕜 := ℝ) A⁻¹ y :=
    ((Matrix.toEuclideanLin (𝕜 := ℝ) A⁻¹).continuous_of_finiteDimensional).measurable
  -- the loading of the rotated tuple undoes the transport of the latent variable
  have hLA : ∀ y : EuclideanSpace ℝ (Fin q),
      Matrix.toEuclideanLin (𝕜 := ℝ) (rotateParams P A).loading
          (Matrix.toEuclideanLin (𝕜 := ℝ) A⁻¹ y)
        = Matrix.toEuclideanLin (𝕜 := ℝ) P.loading y := by
    intro y
    have key : (P.loading * A) *ᵥ (A⁻¹ *ᵥ (WithLp.ofLp y))
        = P.loading *ᵥ (WithLp.ofLp y) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_right _ _ hA]
    exact congrArg (WithLp.toLp 2) key
  -- hence the two measurement kernels agree along the transport
  have hker : ∀ y : EuclideanSpace ℝ (Fin q),
      measurementKernel (rotateParams P A) E (Matrix.toEuclideanLin (𝕜 := ℝ) A⁻¹ y)
        = measurementKernel P E y := by
    intro y
    by_cases hE : SFinite E
    · rw [measurementKernel_apply, measurementKernel_apply, hLA y, rotateParams_μ]
    · -- LEAN-ONLY: junk regime — without `SFinite E` the product kernel, hence the
      -- measurement kernel, is `0` on both sides
      have hns : ¬ IsSFiniteKernel (Kernel.const (EuclideanSpace ℝ (Fin q)) E) := by
        rw [Kernel.isSFiniteKernel_const]; exact hE
      simp [measurementKernel, affineNoiseKernel,
        Kernel.prod_of_not_isSFiniteKernel_right _ hns]
  ext s hs
  rw [factorLaw, factorLaw, Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _),
    lintegral_map (Kernel.measurable_coe _ hs) hg]
  exact lintegral_congr fun y => by rw [hker y]

/-- The transported latent law realizes the rotated parameters, so the rotated model is a
*bona fide* factor model with the same observed law. -/
theorem realizesFactorParams_rotateParams (P : FactorParams p q)
    (F : Measure (EuclideanSpace ℝ (Fin q))) (E : Measure (EuclideanSpace ℝ (Fin p)))
    [IsProbabilityMeasure F] [IsProbabilityMeasure E] {A : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: the free laws carry the declared parameters; BKM Eq. (3.2)–(3.3)
    (hPFE : RealizesFactorParams P F E)
    -- USER-INPUT: second moments of the latent law (needed to transport its covariance);
    -- BKM Eq. (3.2)
    (hF2 : MemLp id 2 F) :
    RealizesFactorParams (rotateParams P A)
      (F.map fun y => Matrix.toEuclideanLin (𝕜 := ℝ) A⁻¹ y) E := by
  -- the transport is the affine map `y ↦ A⁻¹ y + 0`
  have hmapEq : (fun y : EuclideanSpace ℝ (Fin q) => Matrix.toEuclideanLin (𝕜 := ℝ) A⁻¹ y)
      = fun y => Matrix.toEuclideanLin (𝕜 := ℝ) A⁻¹ y + (0 : EuclideanSpace ℝ (Fin q)) := by
    funext y; rw [add_zero]
  refine ⟨?_, hPFE.meanVec_error, ?_, hPFE.covMatrix_error⟩
  · rw [hmapEq, meanVec_map_affine F A⁻¹ 0 (hF2.integrable (by norm_num)),
      hPFE.meanVec_latent]
    simp
  · rw [hmapEq, covMatrix_map_affine F A⁻¹ 0 hF2, hPFE.covMatrix_latent,
      rotateParams_factorCov]

/-- **Rotation invariance of the Gaussian factor model**: in the Gaussian instantiation the
transport of the latent law is automatic (a Gaussian stays Gaussian), so the parameters
`P` and `rotateParams P A` index *literally the same law* — this is the source of the
non-identifiability in `FactorModels.Identifiability`. -/
theorem gaussianFactorModel_rotateParams (P : FactorParams p q)
    {A : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: genuine covariance parameters; BKM Eq. (3.1)–(3.2)
    (hP : IsProperFactorParams P)
    -- USER-INPUT: the reparameterization is a change of basis of the latent space;
    -- BKM §2.11
    (hA : IsUnit A.det) :
    gaussianFactorModel p q (rotateParams P A) = gaussianFactorModel p q P := by
  rw [gaussianFactorModel_eq_multivariateGaussian _
      (isProperFactorParams_rotateParams P A hP),
    gaussianFactorModel_eq_multivariateGaussian _ hP, rotateParams_μ,
    factorCovariance_rotateParams P hA]

/-! ### The orthogonal specialization (`BKM` §2.11, §3.13.1)

For `Q Qᵀ = I` the inverse is the transpose, so the rotated tuple is `(Λ Q, Qᵀ Φ Q, Ψ)`; at
`BKM`'s normalization `Φ = I` the latent covariance is unchanged and only the loadings move.
Over a commutative ring `Q Qᵀ = 1` already forces `Qᵀ Q = 1` (`Matrix.mul_eq_one_comm`), so a
single hypothesis suffices. -/

/-- For an orthogonal matrix the inverse is the transpose. -/
theorem inv_eq_transpose_of_orthogonal {Q : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: `Q` is orthogonal; BKM §2.11, Eq. (2.24)
    (hQ : Q * Qᵀ = 1) :
    Q⁻¹ = Qᵀ :=
  Matrix.inv_eq_right_inv hQ

/-- An orthogonal matrix is nonsingular. -/
theorem isUnit_det_of_orthogonal {Q : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: `Q` is orthogonal; BKM §2.11, Eq. (2.24)
    (hQ : Q * Qᵀ = 1) :
    IsUnit Q.det :=
  Matrix.isUnit_det_of_right_inverse hQ

/-- **`BKM` Eq. (2.26)**: an orthogonal rotation of the loadings leaves `Λ Λᵀ` unchanged. -/
theorem loading_mul_transpose_rotateParams_orthogonal (P : FactorParams p q)
    {Q : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: `Q` is orthogonal; BKM §2.11, Eq. (2.24)
    (hQ : Q * Qᵀ = 1) :
    (P.loading * Q) * (P.loading * Q)ᵀ = P.loading * P.loadingᵀ := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQ, Matrix.one_mul]

/-- Orthogonal rotation preserves `BKM`'s normalization `Φ = I` (`BKM` §3.13.1). -/
theorem isStandardized_rotateParams_orthogonal (P : FactorParams p q)
    {Q : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: BKM's normalization y ∼ N_q(0, I); BKM Eq. (3.2)
    (hP : IsStandardized P)
    -- USER-INPUT: `Q` is orthogonal; BKM §2.11, Eq. (2.24)
    (hQ : Q * Qᵀ = 1) :
    IsStandardized (rotateParams P Q) := by
  have hQinv : Q⁻¹ = Qᵀ := inv_eq_transpose_of_orthogonal hQ
  change Q⁻¹ * P.factorCov * (Q⁻¹)ᵀ = 1
  rw [hP, Matrix.mul_one, hQinv, Matrix.transpose_transpose, ← hQinv]
  exact Matrix.nonsing_inv_mul _ (isUnit_det_of_orthogonal hQ)

/-- **The book's orthogonal-rotation statement** (`BKM` §3.13.1): for standardized factors,
`Λ` and `Λ Q` give the same covariance `Σ = Λ Λᵀ + Ψ`. -/
theorem factorCovariance_rotateParams_orthogonal (P : FactorParams p q)
    {Q : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: `Q` is orthogonal; BKM §2.11, Eq. (2.24)
    (hQ : Q * Qᵀ = 1) :
    factorCovariance (rotateParams P Q) = factorCovariance P :=
  factorCovariance_rotateParams P (isUnit_det_of_orthogonal hQ)

/-- **Communalities are rotation invariant** — the classical reason communalities, unlike
loadings, are reportable quantities (`BKM` §2.11 with Eq. (3.10)). -/
theorem communality_rotateParams_orthogonal (P : FactorParams p q)
    {Q : Matrix (Fin q) (Fin q) ℝ}
    -- USER-INPUT: `Q` is orthogonal; BKM §2.11, Eq. (2.24)
    (hQ : Q * Qᵀ = 1) (i : Fin p) :
    communality (rotateParams P Q) i = communality P i := by
  -- the communality is the `(i, i)` entry of `Λ Λᵀ`, which orthogonal rotation preserves
  have key : ∀ M : Matrix (Fin p) (Fin q) ℝ, ∑ k, (M i k) ^ 2 = (M * Mᵀ) i i := by
    intro M
    simp [Matrix.mul_apply, Matrix.transpose_apply, sq]
  rw [communality, communality, key, key, rotateParams_loading,
    loading_mul_transpose_rotateParams_orthogonal P hQ]

/-- Specific variances are untouched by any reparameterization (definitional). -/
theorem specificVariance_rotateParams (P : FactorParams p q)
    (A : Matrix (Fin q) (Fin q) ℝ) (i : Fin p) :
    specificVariance (rotateParams P A) i = specificVariance P i := rfl

end StatLean.StatisticalModels.FactorModels
