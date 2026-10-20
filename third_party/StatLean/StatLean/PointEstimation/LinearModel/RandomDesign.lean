module
public import StatLean.PointEstimation.LinearModel.LeastSquares
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Probability.Moments.Covariance
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section

/-!
# Regression coefficients in the normal linear model

In the regression form of the linear model the mean vector is `ξ = θ A` for a known design
matrix `A` of full row rank; the least-squares estimator of the coefficient vector is
`θ̂(y) = y Aᵀ (A Aᵀ)⁻¹`. This file records:

* `designMean`, `designSpace`, `lseCoeff`, `regressionModel` — the regression form and its
  least-squares estimator, together with the bridge `designMean_lseCoeff` identifying
  `θ̂` with the least-squares estimator of the mean vector;
* `isUMVU_regression_coeff` — every linear function of `θ̂` is UMVU for the corresponding
  linear function of `θ`;
* `covariance_regression_coeff` — the covariance matrix of `θ̂` is `σ² (A Aᵀ)⁻¹`;

**Not present: the random-design nonexistence clause.** The source's claim that no best
linear unbiased estimator exists when the design is random with a known second moment
(Shaffer's phenomenon) was formalized and found to be **false as printed**, and has been
removed rather than carried as a debt. Its nondegeneracy hypothesis — "the design law is not
a point mass" — is strictly too weak: for the two-point law `½·δ_a + ½·δ_{-a}` the designs
`a` and `-a` carry the *same* information `1/‖a‖²`, so in the total-variance decomposition
`σ²·E[λ² i] + θ²·Var(λ)` (subject to `E λ = 1`) both terms are minimised at the same weighting
`λ ≡ 1`, and the conditional least-squares estimator *is* best linear unbiased. Shaffer's
phenomenon needs the two terms to be minimised at *different* weightings, which happens
exactly when the design information `cᵀ (A Aᵀ)⁻¹ c` genuinely varies. Restoring the clause is
a **statement change** — replace the point-mass hypothesis by "the design information is not
`Q`-a.s. constant", plus a.s. full row rank — and a decision for the library, not a proof
obligation. The full analysis, with the counterexample and the repair, is in
`notes/point_estimation/defective-statements.tex`.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 3 (Equivariance), §3.4 (Normal
Linear Models), Theorem 4.14 (the regression-coefficient form and its covariance). (`TPE2 §3.4
Thm 4.14`.)

**Proof formalization notes.**
* *Row convention.* Coefficient vectors multiply the design on the left, `ξ = θ A` with `A`
  of size `s × n`, matching `Matrix.vecMul`; `lseCoeff` is the total function
  `y ↦ y Aᵀ (A Aᵀ)⁻¹`, which is junk (zero) when `A A ᵀ` is singular, i.e. exactly when the
  full-row-rank hypothesis fails.
**Bibliographic comments.** The regression form of the linear model and the covariance
formula `σ²(A Aᵀ)⁻¹` are classical, going back to C. F. Gauss (*Theoria combinationis
observationum erroribus minimis obnoxiae*, 1821/1823) and A. A. Markov
(*Wahrscheinlichkeitsrechnung*, Teubner, 1912); see H. Scheffé (*The Analysis of Variance*,
Wiley, 1959), W. Kruskal ("When are Gauss–Markov and least squares estimators identical?"
in *Essays in Probability and Statistics*, 1965) and C. R. Rao (*Linear Statistical
Inference and Its Applications*, 2nd ed., Wiley, 1973). The failure of best linear unbiased
estimation for random regressors with known second moment is due to J. P. Shaffer
("The Gauss–Markov theorem and random regressors," *Amer. Statist.* **45** (1991),
269–273); its relation to ancillarity and admissibility was investigated by L. D. Brown
("An ancillarity paradox which appears in multiple linear regression," *Ann. Statist.*
**18** (1990), 471–493).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Matrix

namespace StatLean.PointEstimation

/-- The regression parameter: the coefficient vector together with the unknown positive
variance (the same packaging as in the canonical model). -/
abbrev RegressionParam (k : ℕ) : Type := (Fin k → ℝ) × PosVar

variable {s n : ℕ}

/-! ## The regression form -/

/-- The **regression mean vector** `ξ = θ A` of a design matrix `A`. -/
noncomputable def designMean (A : Matrix (Fin s) (Fin n) ℝ) (θ : Fin s → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) (θ ᵥ* A)

/-- The **mean subspace of a design**: the span of the rows of `A`, over which the
regression mean vector ranges. -/
noncomputable def designSpace (A : Matrix (Fin s) (Fin n) ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (Set.range fun i : Fin s =>
    ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) (A i)))

/-- The **least-squares estimator of the regression coefficients**,
`θ̂(y) = y Aᵀ (A Aᵀ)⁻¹`. For a design that does not have full row rank the matrix `A Aᵀ` is
singular, its Mathlib inverse is `0`, and this definition returns the junk value `0`; every
theorem below carries the full-row-rank hypothesis. -/
noncomputable def lseCoeff (A : Matrix (Fin s) (Fin n) ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : Fin s → ℝ :=
  ((fun i => y i) ᵥ* Aᵀ) ᵥ* (A * Aᵀ)⁻¹

/-- The **regression model**: independent normal observations with mean vector `θ A` and
unknown common variance. -/
noncomputable def regressionModel (A : Matrix (Fin s) (Fin n) ℝ) (p : RegressionParam s) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  gaussianVector (designMean A p.1) p.2.1

/-- The regression mean vector lies in the span of the rows of the design. -/
theorem designMean_mem_designSpace (A : Matrix (Fin s) (Fin n) ℝ) (θ : Fin s → ℝ) :
    designMean A θ ∈ designSpace A := by
  rw [designMean, designSpace]
  have hsum : (θ ᵥ* A) = ∑ i, θ i • A i := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  have he : (WithLp.toLp 2 (∑ i, θ i • A i) : EuclideanSpace ℝ (Fin n))
      = ∑ i, θ i • (WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n)) :=
    (map_sum (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm (fun i => θ i • A i) Finset.univ).trans
      (Finset.sum_congr rfl (fun i _ => map_smul _ (θ i) (A i)))
  rw [he]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/-- A design of full row rank identifies its coefficient vector. -/
theorem injective_designMean {A : Matrix (Fin s) (Fin n) ℝ}
    -- USER-INPUT: the design has full row rank `s` (the full-rank regression model)
    (hA : A.rank = s) :
    Function.Injective (designMean A) := by
  have hli : LinearIndependent ℝ A.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
        ← Matrix.rank_eq_finrank_span_row, hA]
    simp
  have hvec : Function.Injective A.vecMul := Matrix.vecMul_injective_iff.mpr hli
  intro θ φ h
  exact hvec ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.injective h)

/-- **The coefficient LSE is the mean LSE**: applying the design to `θ̂(y)` returns the
orthogonal projection of `y` onto the mean subspace. This is the bridge that transports the
optimality statements from the mean vector to the regression coefficients. -/
theorem designMean_lseCoeff {A : Matrix (Fin s) (Fin n) ℝ}
    [(designSpace A).HasOrthogonalProjection]
    -- USER-INPUT: the design has full row rank `s` (the full-rank regression model)
    (hA : A.rank = s) (y : EuclideanSpace ℝ (Fin n)) :
    designMean A (lseCoeff A y) = lse (designSpace A) y := by
  classical
  have hli : LinearIndependent ℝ A.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
        ← Matrix.rank_eq_finrank_span_row, hA]; simp
  have hvecA : Function.Injective A.vecMul := Matrix.vecMul_injective_iff.mpr hli
  have hunit : IsUnit (A * Aᵀ) := by
    rw [← Matrix.vecMul_injective_iff_isUnit]
    intro x z h
    have hx0 : (x - z) ᵥ* (A * Aᵀ) = 0 := by rw [Matrix.sub_vecMul, sub_eq_zero]; exact h
    have hself : ((x - z) ᵥ* A) ⬝ᵥ ((x - z) ᵥ* A) = 0 := by
      have e1 : ((x - z) ᵥ* A) ⬝ᵥ ((x - z) ᵥ* A)
          = ((x - z) ᵥ* A) ⬝ᵥ (Aᵀ *ᵥ (x - z)) := by rw [Matrix.mulVec_transpose]
      rw [e1, Matrix.dotProduct_mulVec,
        show ((x - z) ᵥ* A) ᵥ* Aᵀ = (x - z) ᵥ* (A * Aᵀ) from Matrix.vecMul_vecMul _ _ _,
        hx0, zero_dotProduct]
    have hxA : (x - z) ᵥ* A = 0 := by rw [← dotProduct_self_eq_zero]; exact hself
    have hxz : x - z = 0 := hvecA (by simpa using hxA)
    exact sub_eq_zero.mp hxz
  have hunitdet : IsUnit (A * Aᵀ).det := by rw [← Matrix.isUnit_iff_isUnit_det]; exact hunit
  have hAAT_symm : (A * Aᵀ)ᵀ = A * Aᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hinv_symm : ((A * Aᵀ)⁻¹)ᵀ = (A * Aᵀ)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hAAT_symm]
  set c := lseCoeff A y with hc_def
  have hnormal : A *ᵥ (c ᵥ* A) = A *ᵥ (fun i => y i) := by
    have hcv : c = (A *ᵥ (fun i => y i)) ᵥ* (A * Aᵀ)⁻¹ := by
      rw [hc_def, lseCoeff, Matrix.vecMul_transpose]
    calc A *ᵥ (c ᵥ* A)
        = A *ᵥ (Aᵀ *ᵥ c) := by rw [Matrix.mulVec_transpose]
      _ = (A * Aᵀ) *ᵥ c := by rw [Matrix.mulVec_mulVec]
      _ = (A * Aᵀ) *ᵥ ((A *ᵥ (fun i => y i)) ᵥ* (A * Aᵀ)⁻¹) := by rw [hcv]
      _ = (A * Aᵀ) *ᵥ (((A * Aᵀ)⁻¹)ᵀ *ᵥ (A *ᵥ (fun i => y i))) := by rw [Matrix.mulVec_transpose]
      _ = (A * Aᵀ) *ᵥ ((A * Aᵀ)⁻¹ *ᵥ (A *ᵥ (fun i => y i))) := by rw [hinv_symm]
      _ = ((A * Aᵀ) * (A * Aᵀ)⁻¹) *ᵥ (A *ᵥ (fun i => y i)) := by rw [Matrix.mulVec_mulVec]
      _ = 1 *ᵥ (A *ᵥ (fun i => y i)) := by rw [Matrix.mul_nonsing_inv _ hunitdet]
      _ = A *ᵥ (fun i => y i) := by rw [Matrix.one_mulVec]
  have hgen : ∀ r : Fin s,
      ⟪y - designMean A c, (WithLp.toLp 2 (A r) : EuclideanSpace ℝ (Fin n))⟫_ℝ = 0 := by
    intro r
    have hsub : (y - designMean A c : EuclideanSpace ℝ (Fin n))
        = WithLp.toLp 2 ((fun i => y i) - c ᵥ* A) := by
      rw [designMean]
      exact (map_sub (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm _ _)
    rw [hsub]
    show (A r) ⬝ᵥ star ((fun i => y i) - c ᵥ* A) = 0
    have hstar : star ((fun i => y i) - c ᵥ* A) = (fun i => y i) - c ᵥ* A := by
      funext i; exact star_trivial _
    rw [hstar, dotProduct_sub]
    have h1 : (A r) ⬝ᵥ (fun i => y i) = (A *ᵥ (fun i => y i)) r := rfl
    have h2 : (A r) ⬝ᵥ (c ᵥ* A) = (A *ᵥ (c ᵥ* A)) r := rfl
    rw [h1, h2, hnormal, sub_self]
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (designMean_mem_designSpace A c) (fun w hw => ?_)).symm
  induction hw using Submodule.span_induction with
  | mem w hwm => obtain ⟨r, rfl⟩ := hwm; exact hgen r
  | zero => exact inner_zero_right _
  | add a b _ _ ha hb => rw [inner_add_right, ha, hb, add_zero]
  | smul t a _ ha => rw [real_inner_smul_right, ha, mul_zero]

/-! ## Optimality and covariance of the coefficient estimator -/

/-- Full row rank means the rows are linearly independent. -/
private lemma linearIndependent_row_of_rank {A : Matrix (Fin s) (Fin n) ℝ} (hA : A.rank = s) :
    LinearIndependent ℝ A.row := by
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank,
      ← Matrix.rank_eq_finrank_span_row, hA]; simp

/-- For a full-row-rank design the Gram matrix `A Aᵀ` is invertible. -/
private lemma isUnit_mulTranspose_of_rank {A : Matrix (Fin s) (Fin n) ℝ} (hA : A.rank = s) :
    IsUnit (A * Aᵀ) := by
  have hli := linearIndependent_row_of_rank hA
  have hvecA : Function.Injective A.vecMul := Matrix.vecMul_injective_iff.mpr hli
  rw [← Matrix.vecMul_injective_iff_isUnit]
  intro x z h
  have hx0 : (x - z) ᵥ* (A * Aᵀ) = 0 := by rw [Matrix.sub_vecMul, sub_eq_zero]; exact h
  have hself : ((x - z) ᵥ* A) ⬝ᵥ ((x - z) ᵥ* A) = 0 := by
    have e1 : ((x - z) ᵥ* A) ⬝ᵥ ((x - z) ᵥ* A)
        = ((x - z) ᵥ* A) ⬝ᵥ (Aᵀ *ᵥ (x - z)) := by rw [Matrix.mulVec_transpose]
    rw [e1, Matrix.dotProduct_mulVec,
      show ((x - z) ᵥ* A) ᵥ* Aᵀ = (x - z) ᵥ* (A * Aᵀ) from Matrix.vecMul_vecMul _ _ _,
      hx0, zero_dotProduct]
  have hxA : (x - z) ᵥ* A = 0 := by rw [← dotProduct_self_eq_zero]; exact hself
  exact sub_eq_zero.mp (hvecA (by simpa using hxA))

/-- **Reparametrization transport of `IsUMVU`.** Along a *surjective* reindexing `φ` of the
parameter space, a UMVU estimator remains UMVU: unbiasedness and `L²`-membership restrict,
and surjectivity makes the competitor conditions over the reindexed family equivalent to
those over the original, so the variance-minimality transports. -/
private theorem isUMVU_reparam {Θ Θ' 𝓧 : Type*} [MeasurableSpace 𝓧]
    (P : Θ → Measure 𝓧) (φ : Θ' → Θ) (hφ : Function.Surjective φ)
    (g : Θ → ℝ) (δ : 𝓧 → ℝ) (h : IsUMVU P g δ) :
    IsUMVU (fun t => P (φ t)) (fun t => g (φ t)) δ := by
  obtain ⟨hunb, hL2, hmin⟩ := h
  refine ⟨fun t => hunb (φ t), fun t => hL2 (φ t), ?_⟩
  intro δ' hunb' hL2' t
  have hunbP : IsUnbiased P g δ' := fun θ => by
    obtain ⟨t', rfl⟩ := hφ θ; exact hunb' t'
  have hL2P : MemEstL2 P δ' := fun θ => by
    obtain ⟨t', rfl⟩ := hφ θ; exact hL2' t'
  exact hmin δ' hunbP hL2P (φ t)

/-- **Optimality of the regression coefficient estimator**: every linear function of the
least-squares coefficients is the UMVU estimator of the corresponding linear function of the
coefficients. -/
theorem isUMVU_regression_coeff {A : Matrix (Fin s) (Fin n) ℝ}
    -- USER-INPUT: the design has full row rank `s` (the full-rank regression model)
    (hA : A.rank = s)
    -- USER-INPUT: more observations than coefficients (`s < n`); standing dimension
    -- condition of the model, without which the variance is not estimable
    (hsn : s < n)
    -- USER-INPUT: the known coefficient vector of the estimated linear functional
    (c : Fin s → ℝ) :
    IsUMVU (regressionModel A) (fun p => ∑ i, c i * p.1 i)
      (fun y => ∑ i, c i * lseCoeff A y i) := by
  classical
  -- Least squares on the mean subspace `W = designSpace A`, of dimension `s < n`.
  set W := designSpace A with hWdef
  have hli := linearIndependent_row_of_rank hA
  have hlitoLp : LinearIndependent ℝ
      (fun i => (WithLp.toLp 2 (A i) : EuclideanSpace ℝ (Fin n))) :=
    hli.map' (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm.toLinearMap
      (LinearEquiv.ker _)
  have hfr : Module.finrank ℝ W < n := by
    have : Module.finrank ℝ W = s := by
      rw [hWdef, designSpace, finrank_span_eq_card hlitoLp]; simp
    rw [this]; exact hsn
  -- The Riesz vector `γ ∈ W` representing the functional `θ ↦ ∑ cᵢ θᵢ` of the mean.
  set w : Fin s → ℝ := (A * Aᵀ)⁻¹ *ᵥ c with hwdef
  set γ : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (Aᵀ *ᵥ w) with hγdef
  have hunit := isUnit_mulTranspose_of_rank hA
  have hunitdet : IsUnit (A * Aᵀ).det := by rw [← Matrix.isUnit_iff_isUnit_det]; exact hunit
  have hinner : ∀ θ : Fin s → ℝ, ⟪γ, designMean A θ⟫_ℝ = ∑ i, c i * θ i := by
    intro θ
    rw [hγdef, designMean]
    show (θ ᵥ* A) ⬝ᵥ star (Aᵀ *ᵥ w) = ∑ i, c i * θ i
    rw [show star (Aᵀ *ᵥ w) = Aᵀ *ᵥ w from by funext i; exact star_trivial _]
    calc (θ ᵥ* A) ⬝ᵥ (Aᵀ *ᵥ w)
        = (θ ᵥ* (A * Aᵀ)) ⬝ᵥ w := by rw [Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
      _ = (θ ᵥ* ((A * Aᵀ) * (A * Aᵀ)⁻¹)) ⬝ᵥ c := by
            rw [hwdef, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
      _ = θ ⬝ᵥ c := by rw [Matrix.mul_nonsing_inv _ hunitdet, Matrix.vecMul_one]
      _ = ∑ i, c i * θ i := by
            rw [dotProduct]; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  -- The base UMVU statement in the mean coordinates (`T = ⟪γ, ·⟫`).
  have hbase := isUMVU_linear_functional_of_mean W hfr
    (fun ζ => ⟪γ, ζ⟫_ℝ) (γ := γ) (fun ζ _ => rfl)
  -- The reindexing `(θ, σ²) ↦ (designMean A θ, σ²)` is surjective onto `W × PosVar`.
  set φ : RegressionParam s → ↥W × PosVar :=
    fun t => (⟨designMean A t.1, designMean_mem_designSpace A t.1⟩, t.2) with hφdef
  have hφsurj : Function.Surjective φ := by
    rintro ⟨⟨ξ, hξ⟩, σ2⟩
    refine ⟨(lseCoeff A ξ, σ2), ?_⟩
    have hproj : designMean A (lseCoeff A ξ) = ξ := by
      rw [designMean_lseCoeff hA ξ]
      exact Submodule.starProjection_eq_self_iff.mpr hξ
    simp only [hφdef, Prod.mk.injEq, Subtype.mk.injEq]
    refine ⟨hproj, ?_⟩; trivial
  have htrans := isUMVU_reparam _ φ hφsurj _ _ hbase
  -- Match the transported statement to the regression form, coordinatewise.
  have hmodel : (fun t => linearModelFull W (φ t)) = regressionModel A := by
    funext t; rfl
  have hg : (fun t : RegressionParam s => (fun ζ => ⟪γ, ζ⟫_ℝ) ((φ t).1 : _))
      = fun p => ∑ i, c i * p.1 i := by
    funext t; exact hinner t.1
  have hδ : (fun y => (fun ζ => ⟪γ, ζ⟫_ℝ) (lse W y))
      = fun y => ∑ i, c i * lseCoeff A y i := by
    funext y; rw [← designMean_lseCoeff hA y]; exact hinner (lseCoeff A y)
  rw [hmodel, hg, hδ] at htrans
  exact htrans

/-- The coordinate `L²`-membership under a Gaussian vector. -/
private lemma memLp_coord_gaussianVector {N : ℕ} (ξ : EuclideanSpace ℝ (Fin N))
    (σ2 : ℝ≥0) (a : Fin N) :
    MemLp (fun y : EuclideanSpace ℝ (Fin N) => y a) 2 (gaussianVector ξ σ2) := by
  have hcoord : MemLp (Function.eval a) 2 (Measure.pi fun i => gaussianReal (ξ i) σ2) :=
    (memLp_id_gaussianReal 2).comp_measurePreserving
      (measurePreserving_eval (fun i => gaussianReal (ξ i) σ2) a)
  rw [show gaussianVector ξ σ2
        = (Measure.pi fun i => gaussianReal (ξ i) σ2).map (WithLp.toLp 2) from rfl]
  exact (memLp_map_measure_iff
    ((measurable_pi_apply a).comp (WithLp.measurable_ofLp 2 _)).aestronglyMeasurable
    (WithLp.measurable_toLp 2 (Fin N → ℝ)).aemeasurable).mpr hcoord

/-- The coordinate covariance of a Gaussian vector: `σ²` on the diagonal, `0` off it. -/
private lemma covariance_coord_gaussianVector {N : ℕ} (ξ : EuclideanSpace ℝ (Fin N))
    (σ2 : ℝ≥0) (a b : Fin N) :
    covariance (fun y => y a) (fun y => y b) (gaussianVector ξ σ2)
      = if a = b then (σ2 : ℝ) else 0 := by
  classical
  set μ : Measure (Fin N → ℝ) := Measure.pi fun i => gaussianReal (ξ i) σ2 with hμ
  have hgc : ∀ k, Measurable (fun y : EuclideanSpace ℝ (Fin N) => y k) :=
    fun k => (measurable_pi_apply k).comp (WithLp.measurable_ofLp 2 _)
  rw [show gaussianVector ξ σ2 = μ.map (WithLp.toLp 2) from rfl,
      covariance_map_fun (hgc a).aestronglyMeasurable (hgc b).aestronglyMeasurable
        (WithLp.measurable_toLp 2 (Fin N → ℝ)).aemeasurable]
  show covariance (Function.eval a) (Function.eval b) μ = _
  have hcoord : ∀ k : Fin N, MemLp (Function.eval (β := fun _ : Fin N => ℝ) k) 2 μ := fun k =>
    (memLp_id_gaussianReal 2).comp_measurePreserving (measurePreserving_eval _ k)
  by_cases hab : a = b
  · subst hab
    have hmp := measurePreserving_eval (fun i => gaussianReal (ξ i) σ2) a
    rw [if_pos rfl, covariance_self hmp.measurable.aemeasurable,
        ← variance_id_map hmp.measurable.aemeasurable, hmp.map_eq, variance_id_gaussianReal]
  · rw [if_neg hab]
    have hindep : IndepFun (Function.eval a) (Function.eval b) μ :=
      (iIndepFun_pi fun _ => aemeasurable_id).indepFun hab
    exact hindep.covariance_eq_zero (hcoord a) (hcoord b)

/-- **Covariance of the regression coefficient estimator**: `cov(θ̂) = σ² (A Aᵀ)⁻¹`. -/
theorem covariance_regression_coeff {A : Matrix (Fin s) (Fin n) ℝ}
    -- USER-INPUT: the design has full row rank `s` (the full-rank regression model)
    (hA : A.rank = s) (p : RegressionParam s) (i j : Fin s) :
    covariance (fun y => lseCoeff A y i) (fun y => lseCoeff A y j) (regressionModel A p)
      = (p.2.1 : ℝ) * (A * Aᵀ)⁻¹ i j := by
  classical
  haveI : IsProbabilityMeasure (gaussianVector (designMean A p.1) p.2.1) := by
    rw [show gaussianVector (designMean A p.1) p.2.1
        = (Measure.pi fun i => gaussianReal ((designMean A p.1) i) p.2.1).map (WithLp.toLp 2)
        from rfl]
    exact Measure.isProbabilityMeasure_map (WithLp.measurable_toLp 2 _).aemeasurable
  have hunit := isUnit_mulTranspose_of_rank hA
  have hunitdet : IsUnit (A * Aᵀ).det := by rw [← Matrix.isUnit_iff_isUnit_det]; exact hunit
  set M : Matrix (Fin n) (Fin s) ℝ := Aᵀ * (A * Aᵀ)⁻¹ with hMdef
  -- `θ̂ᵢ` is the explicit linear combination `∑ₗ Mₗᵢ yₗ`.
  have hlse : ∀ (y : EuclideanSpace ℝ (Fin n)) (k : Fin s),
      lseCoeff A y k = ∑ l, M l k * y l := by
    intro y k
    rw [lseCoeff, Matrix.vecMul_vecMul, ← hMdef, Matrix.vecMul, dotProduct]
    exact Finset.sum_congr rfl (fun l _ => mul_comm _ _)
  -- The Gram identity `Mᵀ M = (A Aᵀ)⁻¹`.
  have hinv_symm : ((A * Aᵀ)⁻¹)ᵀ = (A * Aᵀ)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hMt : Mᵀ = (A * Aᵀ)⁻¹ * A := by
    rw [hMdef, Matrix.transpose_mul, hinv_symm, Matrix.transpose_transpose]
  have hMtM : Mᵀ * M = (A * Aᵀ)⁻¹ := by
    calc Mᵀ * M
        = (A * Aᵀ)⁻¹ * A * (Aᵀ * (A * Aᵀ)⁻¹) := by rw [hMt, hMdef]
      _ = (A * Aᵀ)⁻¹ * (A * Aᵀ) * (A * Aᵀ)⁻¹ := by
            rw [Matrix.mul_assoc ((A * Aᵀ)⁻¹) A (Aᵀ * (A * Aᵀ)⁻¹),
                ← Matrix.mul_assoc A Aᵀ ((A * Aᵀ)⁻¹),
                ← Matrix.mul_assoc ((A * Aᵀ)⁻¹) (A * Aᵀ) ((A * Aᵀ)⁻¹)]
      _ = 1 * (A * Aᵀ)⁻¹ := by rw [Matrix.nonsing_inv_mul _ hunitdet]
      _ = (A * Aᵀ)⁻¹ := Matrix.one_mul _
  have hgram : (∑ l, M l i * M l j) = (A * Aᵀ)⁻¹ i j := by
    rw [← hMtM, Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun l _ => by rw [Matrix.transpose_apply])
  -- Expand the covariance of the two linear combinations by bilinearity.
  rw [regressionModel,
      show (fun y => lseCoeff A y i) = (fun y => ∑ l, M l i * y l) from funext fun y => hlse y i,
      show (fun y => lseCoeff A y j) = (fun y => ∑ l, M l j * y l) from funext fun y => hlse y j,
      covariance_fun_sum_fun_sum
        (fun l => (memLp_coord_gaussianVector _ _ l).const_mul (M l i))
        (fun l => (memLp_coord_gaussianVector _ _ l).const_mul (M l j))]
  have hcell : ∀ l l', covariance (fun y => M l i * y l) (fun y => M l' j * y l')
      (gaussianVector (designMean A p.1) p.2.1)
      = M l i * M l' j * (if l = l' then (p.2.1 : ℝ) else 0) := by
    intro l l'
    rw [covariance_const_mul_left, covariance_const_mul_right,
        covariance_coord_gaussianVector]
    ring
  simp_rw [hcell]
  have hcollapse : ∀ l, (∑ l', M l i * M l' j * (if l = l' then (p.2.1 : ℝ) else 0))
      = M l i * M l j * (p.2.1 : ℝ) := by
    intro l
    rw [Finset.sum_eq_single l]
    · rw [if_pos rfl]
    · intro l' _ hl'; rw [if_neg (fun h => hl' h.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ l) h
  rw [Finset.sum_congr rfl (fun l _ => hcollapse l)]
  rw [show (∑ l, M l i * M l j * (p.2.1 : ℝ)) = (∑ l, M l i * M l j) * (p.2.1 : ℝ) from by
        rw [Finset.sum_mul], hgram]
  rw [mul_comm]

end StatLean.PointEstimation
