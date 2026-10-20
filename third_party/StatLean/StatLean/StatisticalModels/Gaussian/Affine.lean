module
public import StatLean.StatisticalModels.Gaussian.BlockIndex
public import StatLean.StatisticalModels.ForMathlib.CovarianceMatrix
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianConv

@[expose] public section

/-!
# Affine images of multivariate Gaussians — and the affine-noise kernel

The transformation calculus of the Gaussian slice:

* `affineNoiseKernel ν A b` — the kernel `x ↦ law of (A x + b + ξ)`, `ξ ∼ ν` — built
  compositionally (deterministic ×ₖ constant, then mapped), so measurability is inherited,
  never hand-proved; this is the shape of every Gaussian conditional kernel;
* `charFun_map_matrix` — the characteristic function of a linear image:
  `φ_{Aμ}(t) = φ_μ(Aᵀ t)` (matrix form, adjoint-free);
* `multivariateGaussian_map_const_add` — translation;
* **`multivariateGaussian_map_affine` (G2.4, the slice's workhorse)** — the affine image of
  a Gaussian is Gaussian with mean `A m + b` and covariance `A S Aᵀ`.

**Reference.** T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*,
Wiley, 1958, §2.4 (linear transformations of normal vectors) (verify §) (`And58 §2.4`).

**Proof formalization notes.** All Gaussian identities go through characteristic functions
(`charFun_multivariateGaussian` + `Measure.ext_of_charFun`) — never densities (the pin has
no Lebesgue-density lemma for `multivariateGaussian`) and never the `CFC.sqrt` definition.
`Aᵀ` transposes across the real inner product by `Matrix.toEuclideanLin`-vs-`dotProduct`
algebra; the PSD side condition `(A S Aᵀ).PosSemidef` is
`Matrix.PosSemidef.mul_mul_conjTranspose_same`-shaped.

**Bibliographic comments.** Classical (Anderson 1958 and earlier); nothing original.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels

variable {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]

/-- LEAN-ONLY: the real inner product on `EuclideanSpace` is the matrix dot product of the
underlying coordinate vectors. -/
private theorem euclideanInner_eq_dotProduct {ι : Type*} [Fintype ι]
    (x y : EuclideanSpace ℝ ι) : ⟪x, y⟫_ℝ = WithLp.ofLp x ⬝ᵥ WithLp.ofLp y :=
  dotProduct_comm _ _

/-- LEAN-ONLY: the transpose is the adjoint of `Matrix.toEuclideanLin` for the real inner
product — `⟪A x, t⟫ = ⟪x, Aᵀ t⟫`. -/
private theorem inner_toEuclideanLin_left [DecidableEq ι₁] [DecidableEq ι₂]
    (A : Matrix ι₂ ι₁ ℝ) (x : EuclideanSpace ℝ ι₁) (t : EuclideanSpace ℝ ι₂) :
    ⟪Matrix.toEuclideanLin (𝕜 := ℝ) A x, t⟫_ℝ
      = ⟪x, Matrix.toEuclideanLin (𝕜 := ℝ) Aᵀ t⟫_ℝ := by
  rw [euclideanInner_eq_dotProduct, euclideanInner_eq_dotProduct]
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose]
  exact dotProduct_comm _ _

/-- LEAN-ONLY: `Matrix.toEuclideanLin` is measurable (a linear map on a finite-dimensional
space is continuous). -/
private theorem measurable_toEuclideanLin [DecidableEq ι₁] (A : Matrix ι₂ ι₁ ℝ) :
    Measurable fun x : EuclideanSpace ℝ ι₁ => Matrix.toEuclideanLin (𝕜 := ℝ) A x :=
  ((Matrix.toEuclideanLin (𝕜 := ℝ) A).continuous_of_finiteDimensional).measurable

/-- The **affine-noise kernel** `x ↦ law of (A x + b + ξ)`, `ξ ∼ ν` — compositional
construction, measurability inherited. -/
noncomputable def affineNoiseKernel {E₁ E₂ : Type*} [MeasurableSpace E₁] [MeasurableSpace E₂]
    [AddCommMonoid E₂] [MeasurableAdd₂ E₂] (ν : Measure E₂) (A : E₁ → E₂)
    -- LEAN-ONLY: measurability of the affine part
    (hA : Measurable A) (b : E₂) : Kernel E₁ E₂ :=
  ((Kernel.deterministic A hA) ×ₖ Kernel.const E₁ ν).map fun p => p.1 + b + p.2

@[simp]
theorem affineNoiseKernel_apply {E₁ E₂ : Type*} [MeasurableSpace E₁] [MeasurableSpace E₂]
    [AddCommMonoid E₂] [MeasurableAdd₂ E₂] (ν : Measure E₂) [SFinite ν] {A : E₁ → E₂}
    -- LEAN-ONLY: measurability of the affine part
    (hA : Measurable A) (b : E₂) (x : E₁) :
    affineNoiseKernel ν A hA b x = ν.map fun z => A x + b + z := by
  have hf : Measurable fun p : E₂ × E₂ => p.1 + b + p.2 :=
    (measurable_fst.add_const b).add measurable_snd
  rw [affineNoiseKernel, Kernel.map_apply _ hf, Kernel.prod_apply, Kernel.deterministic_apply,
    Kernel.const_apply, Measure.dirac_prod, Measure.map_map hf measurable_prodMk_left]
  rfl

instance {E₁ E₂ : Type*} [MeasurableSpace E₁] [MeasurableSpace E₂] [AddCommMonoid E₂]
    [MeasurableAdd₂ E₂] (ν : Measure E₂) [IsProbabilityMeasure ν] {A : E₁ → E₂}
    (hA : Measurable A) (b : E₂) : IsMarkovKernel (affineNoiseKernel ν A hA b) :=
  Kernel.IsMarkovKernel.map _ ((measurable_fst.add_const b).add measurable_snd)

/-- Characteristic function of a linear image, matrix (adjoint-free) form:
`φ_{Aμ}(t) = φ_μ(Aᵀ t)`. -/
theorem charFun_map_matrix [DecidableEq ι₁] [DecidableEq ι₂]
    (μ : Measure (EuclideanSpace ℝ ι₁)) (A : Matrix ι₂ ι₁ ℝ) (t : EuclideanSpace ℝ ι₂) :
    charFun (μ.map fun x => Matrix.toEuclideanLin (𝕜 := ℝ) A x) t
      = charFun μ (Matrix.toEuclideanLin (𝕜 := ℝ) Aᵀ t) := by
  rw [charFun_apply, charFun_apply,
    integral_map (measurable_toEuclideanLin A).aemeasurable
      (Continuous.aestronglyMeasurable (by fun_prop))]
  simp_rw [inner_toEuclideanLin_left]

/-- Translation of a multivariate Gaussian. -/
theorem multivariateGaussian_map_const_add [DecidableEq ι₁] (m : EuclideanSpace ℝ ι₁)
    (S : Matrix ι₁ ι₁ ℝ)
    -- USER-INPUT: genuine covariance parameter; And58 §2.4
    (hS : S.PosSemidef) (c : EuclideanSpace ℝ ι₁) :
    (multivariateGaussian m S).map (fun x => c + x) = multivariateGaussian (c + m) S := by
  haveI : IsProbabilityMeasure ((multivariateGaussian m S).map fun x => c + x) :=
    Measure.isProbabilityMeasure_map (measurable_const_add c).aemeasurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [show (fun x => c + x) = (c + ·) from rfl, charFun_map_const_add,
    charFun_multivariateGaussian hS, charFun_multivariateGaussian hS, ← Complex.exp_add]
  congr 1
  rw [inner_add_right, real_inner_comm c t]
  push_cast
  ring

/-- **G2.4, affine image of a Gaussian** (`And58 §2.4`): the image of `N(m, S)` under
`x ↦ A x + b` is `N(A m + b, A S Aᵀ)`. -/
theorem multivariateGaussian_map_affine [DecidableEq ι₁] [DecidableEq ι₂]
    (m : EuclideanSpace ℝ ι₁) (S : Matrix ι₁ ι₁ ℝ)
    -- USER-INPUT: genuine covariance parameter; And58 §2.4
    (hS : S.PosSemidef) (A : Matrix ι₂ ι₁ ℝ) (b : EuclideanSpace ℝ ι₂) :
    (multivariateGaussian m S).map
        (fun x => Matrix.toEuclideanLin (𝕜 := ℝ) A x + b)
      = multivariateGaussian (Matrix.toEuclideanLin (𝕜 := ℝ) A m + b) (A * S * Aᵀ) := by
  have hAS : (A * S * Aᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.mul_mul_conjTranspose_same A
  have hlin := measurable_toEuclideanLin (ι₁ := ι₁) (ι₂ := ι₂) A
  have hb : Measurable fun y : EuclideanSpace ℝ ι₂ => y + b := measurable_id.add_const b
  haveI : IsProbabilityMeasure ((multivariateGaussian m S).map
      fun x => Matrix.toEuclideanLin (𝕜 := ℝ) A x + b) :=
    Measure.isProbabilityMeasure_map (hlin.add_const b).aemeasurable
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [show (fun x => Matrix.toEuclideanLin (𝕜 := ℝ) A x + b)
      = (· + b) ∘ (fun x => Matrix.toEuclideanLin (𝕜 := ℝ) A x) from rfl,
    ← Measure.map_map hb hlin, charFun_map_add_const,
    charFun_map_matrix, charFun_multivariateGaussian hS, charFun_multivariateGaussian hAS,
    ← Complex.exp_add]
  congr 1
  have hmean : ⟪Matrix.toEuclideanLin (𝕜 := ℝ) Aᵀ t, m⟫_ℝ
      = ⟪t, Matrix.toEuclideanLin (𝕜 := ℝ) A m⟫_ℝ := by
    rw [real_inner_comm, ← inner_toEuclideanLin_left, real_inner_comm]
  have hquad : (WithLp.ofLp (Matrix.toEuclideanLin (𝕜 := ℝ) Aᵀ t))
        ⬝ᵥ S *ᵥ (WithLp.ofLp (Matrix.toEuclideanLin (𝕜 := ℝ) Aᵀ t))
      = WithLp.ofLp t ⬝ᵥ (A * S * Aᵀ) *ᵥ WithLp.ofLp t := by
    simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
    rw [mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, mulVec_transpose, vecMul_vecMul,
      Matrix.mul_assoc]
  rw [inner_add_right, real_inner_comm b t, hmean, hquad]
  push_cast
  ring

end StatLean.StatisticalModels
