module
public import StatLean.StatisticalModels.Gaussian.Affine

@[expose] public section

/-!
# Block marginals and independent blocks of a joint Gaussian

The block calculus of a Gaussian on the sum index `ι₁ ⊕ ι₂` with covariance
`fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂` (one off-diagonal block carried; the other is its transpose
definitionally — killing symmetry side conditions):

* `multivariateGaussian_map_blockFst`/`_blockSnd` — the block marginals are the block
  Gaussians `N(m₁, S₁₁)`, `N(m₂, S₂₂)`;
* **`multivariateGaussian_fromBlocks_prod` (G2.9)** — vanishing cross-covariance makes the
  blocks independent: the joint transported to the product space is the product of the
  marginals — the Gaussian "uncorrelated ⇒ independent" theorem in block form, and the base
  case of the conditioning theorem (G-B3).

**Reference.** `And58` §2.4–2.5 (marginal and independence properties of the multivariate
normal) (verify §).

**Proof formalization notes.** Marginals via `multivariateGaussian_map_affine` at the block
projection matrices (`blockFst` as the matrix `[1 0]`: the `fromBlocks`-algebra
`[1 0] · fromBlocks … · [1 0]ᵀ = S₁₁` is `Matrix.fromBlocks_multiply`-level) — or directly
via the pin's `measurePreserving_restrict₂_multivariateGaussian` if its submatrix form
matches. G2.9 by charFun on the sum space: `inner_sum_split` factorizes the joint charFun
when `S₁₂ = 0`; compare against `charFun` of the product (`charFun` of `Measure.prod` splits
— search `charFun_prod`; else compute through `MeasureTheory.integral_prod`), transported by
`ext_of_map_sumMeasEquivProd`.

**Bibliographic comments.** Classical; the "uncorrelated Gaussians are independent" caveat
(true jointly, false marginally) is the standard warning this block formulation makes
precise.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels

section BlockAlgebra

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- LEAN-ONLY: the quadratic form of a block matrix splits into its four block terms. -/
private theorem dotProduct_fromBlocks_mulVec (A : Matrix ι₁ ι₁ ℝ) (B : Matrix ι₁ ι₂ ℝ)
    (C : Matrix ι₂ ι₁ ℝ) (D : Matrix ι₂ ι₂ ℝ) (x : ι₁ ⊕ ι₂ → ℝ) :
    x ⬝ᵥ (Matrix.fromBlocks A B C D) *ᵥ x
      = ((x ∘ Sum.inl) ⬝ᵥ A *ᵥ (x ∘ Sum.inl) + (x ∘ Sum.inl) ⬝ᵥ B *ᵥ (x ∘ Sum.inr))
        + ((x ∘ Sum.inr) ⬝ᵥ C *ᵥ (x ∘ Sum.inl) + (x ∘ Sum.inr) ⬝ᵥ D *ᵥ (x ∘ Sum.inr)) := by
  rw [Matrix.fromBlocks_mulVec]
  simp [dotProduct, Fintype.sum_sum_type, Finset.sum_add_distrib, mul_add]

end BlockAlgebra

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
  (m₁ : EuclideanSpace ℝ ι₁) (m₂ : EuclideanSpace ℝ ι₂)
  (S₁₁ : Matrix ι₁ ι₁ ℝ) (S₁₂ : Matrix ι₁ ι₂ ℝ) (S₂₂ : Matrix ι₂ ι₂ ℝ)

/-- **First block marginal** (`And58 §2.4`): the `blockFst`-image of the joint block
Gaussian is `N(m₁, S₁₁)`. -/
theorem multivariateGaussian_map_blockFst
    -- USER-INPUT: genuine joint covariance; And58 §2.4
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosSemidef) :
    (multivariateGaussian (blockPair m₁ m₂) (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map
        (blockFst (ι₁ := ι₁) (ι₂ := ι₂))
      = multivariateGaussian m₁ S₁₁ := by
  have hsub : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).submatrix Sum.inl Sum.inl = S₁₁ := by
    ext i j; simp
  have hS₁₁ : S₁₁.PosSemidef := hsub ▸ hJ.submatrix (Sum.inl : ι₁ → ι₁ ⊕ ι₂)
  haveI : IsProbabilityMeasure
      ((multivariateGaussian (blockPair m₁ m₂) (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map
        ⇑(blockFst (ι₁ := ι₁) (ι₂ := ι₂))) :=
    Measure.isProbabilityMeasure_map blockFst.continuous.measurable.aemeasurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hL : charFun ((multivariateGaussian (blockPair m₁ m₂)
        (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map ⇑(blockFst (ι₁ := ι₁) (ι₂ := ι₂))) t
      = charFun (multivariateGaussian (blockPair m₁ m₂)
          (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)) (blockPair t 0) := by
    rw [charFun_apply, charFun_apply,
      integral_map blockFst.continuous.measurable.aemeasurable
        (Continuous.aestronglyMeasurable (by fun_prop))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [inner_sum_split x (blockPair t 0)]
  have hinner : ⟪blockPair t (0 : EuclideanSpace ℝ ι₂), blockPair m₁ m₂⟫_ℝ = ⟪t, m₁⟫_ℝ := by
    rw [inner_sum_split]; simp
  have hquad : (blockPair t (0 : EuclideanSpace ℝ ι₂)).ofLp ⬝ᵥ
        (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) *ᵥ (blockPair t (0 : EuclideanSpace ℝ ι₂)).ofLp
      = t.ofLp ⬝ᵥ S₁₁ *ᵥ t.ofLp := by
    rw [dotProduct_fromBlocks_mulVec]
    simp [blockPair]
  rw [hL, charFun_multivariateGaussian hJ, charFun_multivariateGaussian hS₁₁, hinner, hquad]

/-- **Second block marginal** (`And58 §2.4`). -/
theorem multivariateGaussian_map_blockSnd
    -- USER-INPUT: genuine joint covariance; And58 §2.4
    (hJ : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).PosSemidef) :
    (multivariateGaussian (blockPair m₁ m₂) (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map
        (blockSnd (ι₁ := ι₁) (ι₂ := ι₂))
      = multivariateGaussian m₂ S₂₂ := by
  have hsub : (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂).submatrix Sum.inr Sum.inr = S₂₂ := by
    ext i j; simp
  have hS₂₂ : S₂₂.PosSemidef := hsub ▸ hJ.submatrix (Sum.inr : ι₂ → ι₁ ⊕ ι₂)
  haveI : IsProbabilityMeasure
      ((multivariateGaussian (blockPair m₁ m₂) (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map
        ⇑(blockSnd (ι₁ := ι₁) (ι₂ := ι₂))) :=
    Measure.isProbabilityMeasure_map blockSnd.continuous.measurable.aemeasurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  have hL : charFun ((multivariateGaussian (blockPair m₁ m₂)
        (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)).map ⇑(blockSnd (ι₁ := ι₁) (ι₂ := ι₂))) t
      = charFun (multivariateGaussian (blockPair m₁ m₂)
          (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂)) (blockPair 0 t) := by
    rw [charFun_apply, charFun_apply,
      integral_map blockSnd.continuous.measurable.aemeasurable
        (Continuous.aestronglyMeasurable (by fun_prop))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [inner_sum_split x (blockPair 0 t)]
  have hinner : ⟪blockPair (0 : EuclideanSpace ℝ ι₁) t, blockPair m₁ m₂⟫_ℝ = ⟪t, m₂⟫_ℝ := by
    rw [inner_sum_split]; simp
  have hquad : (blockPair (0 : EuclideanSpace ℝ ι₁) t).ofLp ⬝ᵥ
        (Matrix.fromBlocks S₁₁ S₁₂ S₁₂ᵀ S₂₂) *ᵥ (blockPair (0 : EuclideanSpace ℝ ι₁) t).ofLp
      = t.ofLp ⬝ᵥ S₂₂ *ᵥ t.ofLp := by
    rw [dotProduct_fromBlocks_mulVec]
    simp [blockPair]
  rw [hL, charFun_multivariateGaussian hJ, charFun_multivariateGaussian hS₂₂, hinner, hquad]

/-- **G2.9, independent blocks** (`And58 §2.5`): with vanishing cross-covariance, the joint
block Gaussian transported to the product space is the product of its block marginals —
jointly-Gaussian uncorrelated blocks are independent. -/
theorem multivariateGaussian_fromBlocks_prod
    -- USER-INPUT: genuine block covariances; And58 §2.5
    (h₁ : S₁₁.PosSemidef) (h₂ : S₂₂.PosSemidef) :
    (multivariateGaussian (blockPair m₁ m₂) (Matrix.fromBlocks S₁₁ 0 0 S₂₂)).map
        (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))
      = (multivariateGaussian m₁ S₁₁).prod (multivariateGaussian m₂ S₂₂) := by
  have hJ : (Matrix.fromBlocks S₁₁ (0 : Matrix ι₁ ι₂ ℝ) (0 : Matrix ι₂ ι₁ ℝ) S₂₂).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨h₁.1.fromBlocks (by simp) h₂.1, fun x => ?_⟩
    have e₁ := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h₁).2 (x ∘ Sum.inl)
    have e₂ := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h₂).2 (x ∘ Sum.inr)
    simp only [star_trivial] at e₁ e₂ ⊢
    rw [dotProduct_fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, dotProduct_zero, add_zero, zero_add]
    linarith
  have hmeas : Measurable ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm :=
    (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm.measurable
  have key : multivariateGaussian (blockPair m₁ m₂) (Matrix.fromBlocks S₁₁ 0 0 S₂₂)
      = ((multivariateGaussian m₁ S₁₁).prod (multivariateGaussian m₂ S₂₂)).map
          ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm := by
    haveI : IsProbabilityMeasure (((multivariateGaussian m₁ S₁₁).prod
        (multivariateGaussian m₂ S₂₂)).map ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm) :=
      Measure.isProbabilityMeasure_map hmeas.aemeasurable
    refine Measure.ext_of_charFun (funext fun t => ?_)
    have hsplit : ∀ p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂,
        Complex.exp (↑⟪(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm p, t⟫_ℝ * Complex.I)
          = Complex.exp (↑⟪p.1, blockFst t⟫_ℝ * Complex.I)
            * Complex.exp (↑⟪p.2, blockSnd t⟫_ℝ * Complex.I) := by
      intro p
      rw [← Complex.exp_add]
      congr 1
      simp only [sumMeasEquivProd_symm_apply, inner_sum_split (blockPair p.1 p.2) t,
        blockFst_blockPair, blockSnd_blockPair]
      push_cast
      ring
    have hR : charFun (((multivariateGaussian m₁ S₁₁).prod
          (multivariateGaussian m₂ S₂₂)).map ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm) t
        = charFun (multivariateGaussian m₁ S₁₁) (blockFst t)
          * charFun (multivariateGaussian m₂ S₂₂) (blockSnd t) := by
      rw [charFun_apply, integral_map hmeas.aemeasurable
        (Continuous.aestronglyMeasurable (by fun_prop))]
      simp_rw [hsplit]
      rw [charFun_apply, charFun_apply]
      exact integral_prod_mul (μ := multivariateGaussian m₁ S₁₁)
        (ν := multivariateGaussian m₂ S₂₂)
        (fun x => Complex.exp ((⟪x, blockFst t⟫_ℝ : ℂ) * Complex.I))
        (fun y => Complex.exp ((⟪y, blockSnd t⟫_ℝ : ℂ) * Complex.I))
    have hinner : ⟪t, blockPair m₁ m₂⟫_ℝ
        = ⟪blockFst t, m₁⟫_ℝ + ⟪blockSnd t, m₂⟫_ℝ := by
      simp [inner_sum_split t (blockPair m₁ m₂)]
    have hquad : t.ofLp ⬝ᵥ (Matrix.fromBlocks S₁₁ (0 : Matrix ι₁ ι₂ ℝ)
          (0 : Matrix ι₂ ι₁ ℝ) S₂₂) *ᵥ t.ofLp
        = (blockFst t).ofLp ⬝ᵥ S₁₁ *ᵥ (blockFst t).ofLp
          + (blockSnd t).ofLp ⬝ᵥ S₂₂ *ᵥ (blockSnd t).ofLp := by
      rw [dotProduct_fromBlocks_mulVec]
      simp only [Matrix.zero_mulVec, dotProduct_zero, add_zero, zero_add]
      rfl
    rw [hR, charFun_multivariateGaussian hJ, charFun_multivariateGaussian h₁,
      charFun_multivariateGaussian h₂, ← Complex.exp_add, hinner, hquad]
    push_cast
    ring_nf
  rw [key, Measure.map_map (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).measurable hmeas,
    show (⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))
        ∘ ⇑(sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).symm) = id from
      funext fun p => (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂)).apply_symm_apply p]
  exact Measure.map_id

end StatLean.StatisticalModels
