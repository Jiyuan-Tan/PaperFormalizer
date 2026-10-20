module
public import StatLean.StatisticalModels.GraphicalModels.Gaussian.Precision

@[expose] public section

/-!
# Partial regression coefficients — the conditional mean of one coordinate

The third statistical reading of the concentration matrix (Lauritzen §5.1.3, p. 130, the closing
unnumbered displays). Proposition C.5 says that the conditional distribution of `Y_γ` given all
the remaining variables is univariate normal; writing its conditional expectation as

`ξ_γ + ∑_{μ ∈ Γ∖{γ}} β_{γμ ∣ Γ∖{γ}} (y_μ − ξ_μ)`

and "using (C.4) we find the partial regression coefficient as `β_{γμ ∣ Γ∖{γ}} = −k_{γμ}/k_{γγ}`".

* `partialRegressionCoeff S γ μ := −k_{γμ}/k_{γγ}` — Lauritzen's `β_{γμ ∣ Γ∖{γ}}`;
* `condMeanMatrix_eq_neg_mul` — Lauritzen **(C.4)** as a matrix identity on `condMeanMatrix`,
  i.e. the Gaussian regression matrix *is* `−K₂₂⁻¹K₂₁`;
* `condMeanMatrix_apply_eq_neg_precision_div` — its scalar form on a singleton regressed block:
  the `(γ, μ)` regression coefficient is `−k_{γμ}/k_{γγ}`;
* **`gaussianCondKernel_mean_coord` (HEADLINE)** — Lauritzen's regression equation itself: the
  mean of the conditional law delivered by `gaussianCondKernel` is
  `ξ_γ + ∑_{μ} β_{γμ}(y_μ − ξ_μ)`;
* `partialRegressionCoeff_eq_zero_iff` and
  **`condIndepCoords_gaussianCoords_iff_partialRegressionCoeff_eq_zero`** — the corollary: the
  regression coefficient vanishes iff the concentration entry does iff the two coordinates are
  conditionally independent given the rest.

**Reference.** S. L. Lauritzen, *Graphical Models*, Oxford Statistical Science Series 17,
Clarendon Press, Oxford, **1996 (first edition)**, §5.1.3, p. 130 (the conditional expectation
display and `β_{γμ ∣ Γ∖{γ}} = −k_{γμ}/k_{γγ}` — both **unnumbered**), deriving it from
Appendix C, p. 256: Proposition C.5 and the identity (C.4) `K₁₁⁻¹K₁₂ = −Σ₁₂Σ₂₂⁻`
(`Lauritzen §5.1.3`, `Lauritzen App. C`). Page numbers and item kinds follow
`notes/factor_graphical/books.md`; on the generalized inverse `Σ₂₂⁻` versus `Σ₂₂⁻¹` see the
module docstring of `Gaussian.Precision`.

**Proof formalization notes.**

*Book vs Lean, orientation.* As in `Gaussian.Precision`: Lauritzen conditions on the *second*
block, while `condMeanMatrix S₁₁ S₁₂ = S₁₂ᵀ S₁₁⁻¹` regresses the *second* block on the
*first*. So Lauritzen's (C.4) `K₁₁⁻¹K₁₂ = −Σ₁₂Σ₂₂⁻¹` is transcribed as
`K₂₂⁻¹K₂₁ = −condMeanMatrix S₁₁ S₁₂`.

*Book vs Lean, "one coordinate given all others".* Lauritzen regresses a **single** variable
`Y_γ` on the rest, so the regressed block is a singleton. On the sum index that is a second block
`ι₂` with `Subsingleton ι₂` plus a witness — the type-level form of `|{γ}| = 1` — under which
`K₂₂` is a `1 × 1` matrix and `K₂₂⁻¹K₂₁` is the scalar quotient `−k_{γμ}/k_{γγ}`. The
general-block matrix identity is stated too (`condMeanMatrix_eq_neg_mul`) and is the form needed
for BLUP-style applications.

*Book vs Lean, `Matrix.inv` junk.* `partialRegressionCoeff` is total (`x / 0 = 0`); for singular
`S` the concentration matrix is `0` and the coefficient is `0` vacuously. Every substantive
statement carries `PosDef`.

*Not stated here.* The identification of the ambient-index `partialRegressionCoeff S γ μ` with
the sum-index `condMeanMatrix` entry requires transporting `S` along
`Equiv.sumCompl (· ∈ ({γ} : Finset ι)ᶜ)`; that bookkeeping is not carried out here.

**Bibliographic comments.** The reading of `−k_{γμ}/k_{γγ}` as a regression coefficient is
classical (the "normal equations" of least squares applied to the conditional normal); it is the
form in which the Gaussian graphical model is estimated node-by-node in the modern
neighbourhood-selection literature (N. Meinshausen and P. Bühlmann, "High-dimensional graphs and
variable selection with the Lasso," *Ann. Statist.* **34** (2006), 1436–1462), which is exactly
`condIndepCoords_gaussianCoords_iff_partialRegressionCoeff_eq_zero` used as an estimation
principle.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels.GraphicalModels

section Defs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **partial regression coefficient** `β_{γμ ∣ Γ∖{γ}} = −k_{γμ}/k_{γγ}` (Lauritzen §5.1.3,
p. 130, closing display): the coefficient of `y_μ − ξ_μ` in the conditional expectation of `Y_γ`
given all the remaining variables.

Edge behaviour: total (`x / 0 = 0`); for singular `S` the concentration matrix is `0` and the
coefficient is `0` vacuously, so substantive statements assume `S.PosDef`. On the diagonal the
formula gives `β_{γγ} = −1`, an artefact of applying it outside its range `μ ≠ γ`. -/
noncomputable def partialRegressionCoeff (S : Matrix ι ι ℝ) (i j : ι) : ℝ :=
  -(precisionMatrix S i j) / precisionMatrix S i i

end Defs

section BlockIdentity

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]

/-- **Lauritzen (C.4)** (App. C, p. 256), transcribed for the repo's orientation: the Gaussian
regression matrix `condMeanMatrix S₁₁ S₁₂ = S₂₁S₁₁⁻¹` is minus the conditional covariance times
the off-diagonal block of the joint concentration matrix, `−K₂₂⁻¹K₂₁`.

This is (C.4) solved for `condMeanMatrix`, using (C.3) to identify `K₂₂⁻¹` with
`condCovMatrix`. -/
theorem condMeanMatrix_eq_neg_mul
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen App. C, (C.4)
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) :
    condMeanMatrix S₁₁ S₁₂
      = -(condCovMatrix S₁₁ S₁₂ S₂₂
            * (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix Sum.inr Sum.inl) := by
  have hpd := posDef_condCovMatrix hJ
  have hdet : IsUnit (condCovMatrix S₁₁ S₁₂ S₂₂).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
  rw [submatrix_precisionMatrix_fromBlocks_inr_inl S₁₁ S₁₂ S₂₂ hJ, Matrix.mul_neg,
    ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  -- `neg_neg` does not fire on `Matrix` (the `InvolutiveNeg` instance found is the `Pi` one),
  -- so the double negation is cancelled entrywise
  ext i j
  simp

/-- **`β_{γμ ∣ Γ∖{γ}} = −k_{γμ}/k_{γγ}`** (Lauritzen §5.1.3, p. 130): the scalar form of (C.4)
when the regressed block is a single coordinate. -/
theorem condMeanMatrix_apply_eq_neg_precision_div
    -- LEAN-ONLY: Lauritzen regresses one variable `Y_γ` on the rest; `Subsingleton` plus the
    -- witness `a` is the type-level form of `|{γ}| = 1`, under which `K₂₂⁻¹K₂₁` is a quotient
    [Subsingleton ι₂]
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef) (a : ι₂) (u : ι₁) :
    condMeanMatrix S₁₁ S₁₂ a u
      = -(precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inl u))
          / precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inr a) := by
  -- the `(2,2)` principal block of the joint concentration matrix — a `1 × 1` matrix
  have hMpd : ((precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix
      Sum.inr Sum.inr).PosDef :=
    posDef_submatrix_of_injective (precisionMatrix_posDef hJ) Sum.inr_injective
  -- `M⁻¹ a a = (M a a)⁻¹` on a `1 × 1` matrix: read `M * M⁻¹ = 1` at the single entry
  have hmul := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hMpd.isUnit)
  have hentry : ((precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).submatrix
        Sum.inr Sum.inr)⁻¹ a a
      = (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inr a))⁻¹ := by
    have h1 := congrFun (congrFun hmul a) a
    simp only [Matrix.mul_apply, Matrix.one_apply_eq, Matrix.submatrix_apply,
      Fintype.sum_subsingleton _ a] at h1
    exact (inv_eq_of_mul_eq_one_right h1).symm
  have hcond : condCovMatrix S₁₁ S₁₂ S₂₂ a a
      = (precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inr a))⁻¹ := by
    rw [condCovMatrix_eq_inv_submatrix_precisionMatrix S₁₁ S₁₂ S₂₂ hJ, hentry]
  rw [condMeanMatrix_eq_neg_mul S₁₁ S₁₂ S₂₂ hJ]
  simp only [Matrix.neg_apply, Matrix.mul_apply, Matrix.submatrix_apply,
    Fintype.sum_subsingleton _ a, hcond]
  rw [div_eq_inv_mul]
  ring

/-- **HEADLINE — Lauritzen's regression equation** (§5.1.3, p. 130). The conditional law of `Y_γ`
given `Y_{Γ∖{γ}} = y` is, by Proposition C.5, univariate normal; its mean — which
`gaussianCondKernel` delivers as `ξ_γ + (S₂₁S₁₁⁻¹(y − ξ))_γ` — is Lauritzen's

`ξ_γ + ∑_{μ ∈ Γ∖{γ}} β_{γμ ∣ Γ∖{γ}} (y_μ − ξ_μ)`,  with  `β_{γμ ∣ Γ∖{γ}} = −k_{γμ}/k_{γγ}`. -/
theorem gaussianCondKernel_mean_coord
    -- LEAN-ONLY: one regressed variable, as in the book; see `condMeanMatrix_apply_eq_neg_precision_div`
    [Subsingleton ι₂]
    (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂)
    (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosDef)
    (y : EuclideanSpace ℝ ι₁) (a : ι₂) :
    (m₂ + Matrix.toEuclideanLin (𝕜 := ℝ) (condMeanMatrix S₁₁ S₁₂) (y - m₁)) a
      = m₂ a + ∑ u : ι₁,
          (-(precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inl u))
              / precisionMatrix (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) (Sum.inr a) (Sum.inr a))
            * (y u - m₁ u) := by
  -- coordinates of the matrix action are the row sums
  have hcoord : ∀ (A : Matrix ι₂ ι₁ ℝ) (x : EuclideanSpace ℝ ι₁) (k : ι₂),
      (Matrix.toEuclideanLin (𝕜 := ℝ) A x) k = ∑ l, A k l * x l := by
    intro A x k
    simp [Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
  rw [PiLp.add_apply, hcoord]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [condMeanMatrix_apply_eq_neg_precision_div S₁₁ S₁₂ S₂₂ hJ a u, PiLp.sub_apply]

end BlockIdentity

section Corollary

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Matrix ι ι ℝ}

/-- **The regression coefficient vanishes exactly when the concentration entry does.** The
denominator `k_{γγ}` is strictly positive for a regular `Σ`. -/
theorem partialRegressionCoeff_eq_zero_iff
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hS : S.PosDef) (i j : ι) :
    partialRegressionCoeff S i j = 0 ↔ precisionMatrix S i j = 0 := by
  have hpos := precisionMatrix_diag_pos hS i
  rw [partialRegressionCoeff, div_eq_zero_iff, neg_eq_zero]
  exact ⟨fun h => h.resolve_right hpos.ne', Or.inl⟩

/-- **Corollary of Lauritzen Proposition 5.2** (§5.1.3, pp. 129–130): the partial regression
coefficient of `Y_μ` in the regression of `Y_γ` on all the remaining variables vanishes exactly
when `Y_γ` and `Y_μ` are conditionally independent given the rest. This is the "regress each
variable on all the others and read off the graph from the zero coefficients" characterisation
of the Gaussian graphical model. -/
theorem condIndepCoords_gaussianCoords_iff_partialRegressionCoeff_eq_zero
    (m : EuclideanSpace ℝ ι)
    -- USER-INPUT: `Σ` regular; Lauritzen Prop. 5.2, p. 129
    (hS : S.PosDef) {i j : ι}
    -- USER-INPUT: two distinct coordinates `γ ≠ μ`; Lauritzen Prop. 5.2, p. 129
    (hij : i ≠ j) :
    CondIndepCoords (multivariateGaussian m S) gaussianCoords {i} {j} (Finset.univ \ {i, j})
      ↔ partialRegressionCoeff S i j = 0 := by
  rw [condIndepCoords_gaussianCoords_iff_precisionMatrix_eq_zero m hS hij,
    partialRegressionCoeff_eq_zero_iff hS i j]

/-- Asymmetry of the regression coefficients versus symmetry of the graph: `β_{γμ}` and `β_{μγ}`
differ (they are scaled by different diagonal entries) but vanish together, which is what makes
the edge set of the Gaussian graphical model well defined. -/
theorem partialRegressionCoeff_eq_zero_comm
    -- USER-INPUT: `Σ` regular; Lauritzen §5.1.3, p. 130
    (hS : S.PosDef) (i j : ι) :
    partialRegressionCoeff S i j = 0 ↔ partialRegressionCoeff S j i = 0 := by
  rw [partialRegressionCoeff_eq_zero_iff hS i j, partialRegressionCoeff_eq_zero_iff hS j i,
    precisionMatrix_apply_comm hS i j]

end Corollary

end StatLean.StatisticalModels.GraphicalModels
