module
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

/-!
# Block-index plumbing: `EuclideanSpace ℝ (ι₁ ⊕ ι₂)` vs the product space

The Gaussian slice works on the **sum index** `ι₁ ⊕ ι₂` (where Mathlib's
`multivariateGaussian`, `Matrix.fromBlocks` and the Schur-complement API live) and crosses to
the product `EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂` (where `Measure.compProd` and kernels
live) through exactly the objects of this file — nothing downstream ever unfolds
`WithLp`/`PiLp` internals:

* `blockFst`/`blockSnd` — the two coordinate-block projections (continuous linear maps);
* `blockPair` — the block assembly `E ι₁ → E ι₂ → E (ι₁ ⊕ ι₂)`;
* `inner_sum_split` — the inner product on the sum space splits over the blocks (the charFun
  workhorse);
* `sumMeasEquivProd` — the measurable equivalence with the product space, with
  `map`-injectivity `ext_of_map_sumMeasEquivProd` (so all charFun-uniqueness arguments run on
  the sum space and transport).

The plain product `E ι₁ × E ι₂` carries the sup norm — **no inner-product structure** — so
characteristic-function arguments cannot run there; this file is what makes "charFun on the
sum space, statements on the product space" sound.

**Reference.** LEAN-ONLY plumbing; no book counterpart. The block-matrix calculus it serves
is And58 Ch. 2 (verify §).

**Proof formalization notes.** The projections/assembly are defined coordinatewise on the
`PiLp` carrier and bundled as continuous linear maps (finite dimension gives continuity);
`sumMeasEquivProd` is the Borel isomorphism induced by the underlying continuous linear
equivalence (`Homeomorph.toMeasurableEquiv`). `inner_sum_split` is
`Fintype.sum_sum_type` applied to `PiLp.inner_apply`. Map-injectivity along a measurable
equivalence is `μ = (μ.map e).map e.symm` rewriting.

**Bibliographic comments.** None (plumbing).
-/

open MeasureTheory
open scoped InnerProductSpace

namespace StatLean.StatisticalModels

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- The `Sum.inl`-block projection as a bare linear map; addition and scalar multiplication on
the `PiLp` carrier are coordinatewise, so both structure fields are `rfl`. -/
noncomputable def blockFstₗ :
    EuclideanSpace ℝ (ι₁ ⊕ ι₂) →ₗ[ℝ] EuclideanSpace ℝ ι₁ where
  toFun x := WithLp.toLp 2 fun i => x (Sum.inl i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The `Sum.inr`-block projection as a bare linear map. -/
noncomputable def blockSndₗ :
    EuclideanSpace ℝ (ι₁ ⊕ ι₂) →ₗ[ℝ] EuclideanSpace ℝ ι₂ where
  toFun x := WithLp.toLp 2 fun j => x (Sum.inr j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Block projection onto the first (`Sum.inl`) coordinates, as a continuous linear map. -/
noncomputable def blockFst :
    EuclideanSpace ℝ (ι₁ ⊕ ι₂) →L[ℝ] EuclideanSpace ℝ ι₁ :=
  LinearMap.toContinuousLinearMap blockFstₗ

/-- Block projection onto the second (`Sum.inr`) coordinates, as a continuous linear map. -/
noncomputable def blockSnd :
    EuclideanSpace ℝ (ι₁ ⊕ ι₂) →L[ℝ] EuclideanSpace ℝ ι₂ :=
  LinearMap.toContinuousLinearMap blockSndₗ

/-- Block assembly: build a sum-index vector from its two blocks. -/
noncomputable def blockPair (x₁ : EuclideanSpace ℝ ι₁) (x₂ : EuclideanSpace ℝ ι₂) :
    EuclideanSpace ℝ (ι₁ ⊕ ι₂) :=
  WithLp.toLp 2 (Sum.elim (WithLp.ofLp x₁) (WithLp.ofLp x₂))

@[simp]
theorem blockFst_apply (x : EuclideanSpace ℝ (ι₁ ⊕ ι₂)) (i : ι₁) :
    blockFst x i = x (Sum.inl i) := rfl

@[simp]
theorem blockSnd_apply (x : EuclideanSpace ℝ (ι₁ ⊕ ι₂)) (j : ι₂) :
    blockSnd x j = x (Sum.inr j) := rfl

@[simp]
theorem blockPair_inl (x₁ : EuclideanSpace ℝ ι₁) (x₂ : EuclideanSpace ℝ ι₂) (i : ι₁) :
    blockPair x₁ x₂ (Sum.inl i) = x₁ i := rfl

@[simp]
theorem blockPair_inr (x₁ : EuclideanSpace ℝ ι₁) (x₂ : EuclideanSpace ℝ ι₂) (j : ι₂) :
    blockPair x₁ x₂ (Sum.inr j) = x₂ j := rfl

@[simp]
theorem blockFst_blockPair (x₁ : EuclideanSpace ℝ ι₁) (x₂ : EuclideanSpace ℝ ι₂) :
    blockFst (blockPair x₁ x₂) = x₁ := rfl

@[simp]
theorem blockSnd_blockPair (x₁ : EuclideanSpace ℝ ι₁) (x₂ : EuclideanSpace ℝ ι₂) :
    blockSnd (blockPair x₁ x₂) = x₂ := rfl

@[simp]
theorem blockPair_blockFst_blockSnd (x : EuclideanSpace ℝ (ι₁ ⊕ ι₂)) :
    blockPair (blockFst x) (blockSnd x) = x := by
  ext k
  cases k <;> rfl

/-- **The inner product splits over the blocks** — the charFun workhorse:
`⟪t, x⟫ = ⟪t₁, x₁⟫ + ⟪t₂, x₂⟫`. -/
theorem inner_sum_split (t x : EuclideanSpace ℝ (ι₁ ⊕ ι₂)) :
    ⟪t, x⟫_ℝ = ⟪blockFst t, blockFst x⟫_ℝ + ⟪blockSnd t, blockSnd x⟫_ℝ := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type]

/-- The measurable equivalence between the sum-index Euclidean space and the product of the
block spaces. -/
noncomputable def sumMeasEquivProd :
    EuclideanSpace ℝ (ι₁ ⊕ ι₂) ≃ᵐ EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ where
  toFun x := (blockFst x, blockSnd x)
  invFun p := blockPair p.1 p.2
  left_inv _ := blockPair_blockFst_blockSnd _
  right_inv p := Prod.ext (blockFst_blockPair _ _) (blockSnd_blockPair _ _)
  measurable_toFun :=
    (blockFst.continuous.measurable).prodMk (blockSnd.continuous.measurable)
  measurable_invFun := by
    have : Continuous fun p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂ =>
        blockPair p.1 p.2 :=
      (EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := ι₁) (κ := ι₂)).symm.continuous
    exact this.measurable

@[simp]
theorem sumMeasEquivProd_apply (x : EuclideanSpace ℝ (ι₁ ⊕ ι₂)) :
    sumMeasEquivProd x = (blockFst x, blockSnd x) := rfl

@[simp]
theorem sumMeasEquivProd_symm_apply (p : EuclideanSpace ℝ ι₁ × EuclideanSpace ℝ ι₂) :
    sumMeasEquivProd.symm p = blockPair p.1 p.2 := rfl

/-- Pushforward along the block equivalence is injective on measures: charFun-uniqueness
arguments on the sum space transport to product-space statements. -/
theorem ext_of_map_sumMeasEquivProd
    {μ ν : Measure (EuclideanSpace ℝ (ι₁ ⊕ ι₂))}
    -- LEAN-ONLY: equality of the transported measures; antecedent
    (h : μ.map (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))
        = ν.map (sumMeasEquivProd (ι₁ := ι₁) (ι₂ := ι₂))) :
    μ = ν :=
  MeasurableEquiv.map_measurableEquiv_injective _ h

end StatLean.StatisticalModels
