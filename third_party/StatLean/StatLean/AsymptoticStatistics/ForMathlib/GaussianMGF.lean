module
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity

public import Mathlib.Probability.Distributions.Gaussian.Fernique

public import Mathlib.Probability.Distributions.Gaussian.CharFun

@[expose] public section

/-!
# Multivariate Gaussian moment-generating function

Mathlib (at commit v4.29.1) gives us:
* the 1D Gaussian MGF (`ProbabilityTheory.mgf_gaussianReal`), and
* the multivariate Gaussian characteristic function
  (`ProbabilityTheory.charFun_multivariateGaussian`).

But it does **not** provide the real MGF of a multivariate Gaussian. Deriving
the 7.10 provider hypotheses `hMgfTilt` / `hTilt` requires that identity, so we
build it here.

The derivation chain:

1. `integral_exp_mul_gaussianReal` — repackaging `mgf_gaussianReal` so that
   `∫ exp(t · x) d(gaussianReal μ v) = exp(μ t + v t²/2)` is a plain integral
   equation, not `mgf`-notation.
2. `integral_exp_inner_stdGaussian` — via `map_pi_eq_stdGaussian` plus
   `integral_fintype_prod_eq_prod` the integral factorises into a product of
   1D integrals, each collapsing to `exp(aᵢ²/2)` via step 1, then reassembles
   to `exp(‖a‖²/2)` via `EuclideanSpace.real_norm_sq_eq`.
3. `integral_exp_inner_multivariateGaussian` — unfold
   `multivariateGaussian μ S = (stdGaussian E).map (fun x ↦ μ + √S · x)`,
   apply `integral_map`, linear change of variables, and use step 2.

These are purely `Mathlib-level` — no `AsymptoticStatistics`-specific content
above the import of `Mathlib`. Namespace is intentionally `ProbabilityTheory`
so that the identifiers read naturally alongside Mathlib's Gaussian API.
-/

open MeasureTheory Matrix
open scoped RealInnerProductSpace MatrixOrder ENNReal

namespace ProbabilityTheory

/-- **1D Gaussian moment-generating function**, stated as a plain integral. For
`x ∼ N(μ, v)`, `∫ exp(t · x) dN(μ, v)(x) = exp(μ t + v t² / 2)`. -/
lemma integral_exp_mul_gaussianReal (μ : ℝ) (v : NNReal) (t : ℝ) :
    ∫ x, Real.exp (t * x) ∂gaussianReal μ v
      = Real.exp (μ * t + (v : ℝ) * t ^ 2 / 2) := by
  have hmap : Measure.map (id : ℝ → ℝ) (gaussianReal μ v) = gaussianReal μ v := by
    simp [Measure.map_id]
  have := mgf_gaussianReal hmap t
  simpa [mgf, id] using this

/-- **Standard Gaussian moment-generating function** on a Euclidean space.

For the standard Gaussian measure on `EuclideanSpace ℝ ι` and any `a` in that
space, `∫ exp(⟨a, x⟩) d(stdGaussian)(x) = exp(‖a‖² / 2)`. -/
lemma integral_exp_inner_stdGaussian
    {ι : Type*} [Fintype ι] (a : EuclideanSpace ℝ ι) :
    ∫ x, Real.exp (⟪a, x⟫) ∂stdGaussian (EuclideanSpace ℝ ι)
      = Real.exp (‖a‖ ^ 2 / 2) := by
  -- Pull the integral through `map_pi_eq_stdGaussian` down to a product-measure
  -- integral over `ι → ℝ`.
  rw [← map_pi_eq_stdGaussian (ι := ι),
    integral_map (by fun_prop) (by fun_prop)]
  -- On the product measure, the inner unfolds to `∑ i, y i * a.ofLp i` and
  -- `exp` of a sum splits as a product; apply Fubini.
  have h_inner : ∀ y : ι → ℝ,
      ⟪a, (WithLp.toLp 2 y : EuclideanSpace ℝ ι)⟫
        = ∑ i, a.ofLp i * y i := by
    intro y
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- `(WithLp.toLp 2 y).ofLp i = y i`, and `⟪a i, b i⟫ = b i * a i` on `ℝ` (defeq).
    change y i * a.ofLp i = a.ofLp i * y i
    ring
  have h_prod : ∀ y : ι → ℝ,
      Real.exp (⟪a, (WithLp.toLp 2 y : EuclideanSpace ℝ ι)⟫)
        = ∏ i, Real.exp (a.ofLp i * y i) := by
    intro y
    rw [h_inner y, ← Real.exp_sum]
  simp_rw [h_prod]
  rw [integral_fintype_prod_eq_prod
    (f := fun i y => Real.exp (a.ofLp i * y))]
  -- Each factor is a 1D Gaussian MGF at parameter `a.ofLp i`.
  simp_rw [integral_exp_mul_gaussianReal 0 1 _]
  simp_rw [NNReal.coe_one, one_mul, zero_mul, zero_add]
  -- Combine the product of `exp(·²/2)` back into `exp((∑·²)/2)` and identify
  -- with `exp(‖a‖²/2)` via `EuclideanSpace.real_norm_sq_eq`.
  rw [← Real.exp_sum]
  congr 1
  rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_div]

/-- **Multivariate Gaussian moment-generating function**. For `y ∼ N(μ, S)` on
`EuclideanSpace ℝ (Fin k)` with `S` positive semidefinite and any `t`,
`∫ exp(⟨t, y⟩) dN(μ, S)(y) = exp(⟨t, μ⟩ + (t ⬝ᵥ S *ᵥ t)/2)`. -/
lemma integral_exp_inner_multivariateGaussian
    {k : ℕ} (μ : EuclideanSpace ℝ (Fin k)) (S : Matrix (Fin k) (Fin k) ℝ)
    (hS : S.PosSemidef) (t : EuclideanSpace ℝ (Fin k)) :
    ∫ y, Real.exp (⟪t, y⟫) ∂multivariateGaussian μ S
      = Real.exp (⟪t, μ⟫ + (t.ofLp ⬝ᵥ S.mulVec t.ofLp) / 2) := by
  classical
  -- Unfold the definition and pass the integral through the affine push-forward.
  rw [multivariateGaussian,
    integral_map (by fun_prop) (by fun_prop)]
  -- Split `⟨t, μ + Ax⟩ = ⟨t, μ⟩ + ⟨t, Ax⟩`, pull `exp` out of the sum, and
  -- factor the constant `exp(⟨t, μ⟩)` out of the integral.
  simp_rw [inner_add_right, Real.exp_add]
  rw [integral_const_mul]
  congr 1
  -- Self-adjointness of `toEuclideanCLM (sqrt S)` lets us pivot the inner onto
  -- the first argument: `⟨t, A x⟩ = ⟨A t, x⟩`, reducing to `integral_exp_inner_stdGaussian`.
  set A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k) :=
    toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) with hA_def
  set_option backward.isDefEq.respectTransparency false in
  have hA_sa : IsSelfAdjoint A :=
    (CFC.sqrt_nonneg S).isSelfAdjoint.map (toEuclideanCLM (𝕜 := ℝ))
  have h_inner_swap : ∀ x : EuclideanSpace ℝ (Fin k),
      Real.exp (⟪t, A x⟫) = Real.exp (⟪A t, x⟫) := by
    intro x
    congr 1
    have := ContinuousLinearMap.adjoint_inner_left A x t
    rw [hA_sa.adjoint_eq] at this
    exact this.symm
  simp_rw [h_inner_swap]
  rw [integral_exp_inner_stdGaussian]
  congr 1
  -- Identify `‖A t‖² = t.ofLp ⬝ᵥ S.mulVec t.ofLp` via self-adjoint + sqrt·sqrt = S.
  rw [sq, ← real_inner_self_eq_norm_mul_norm]
  have h_self_adjoint_swap : ⟪A t, A t⟫ = ⟪t, A (A t)⟫ := by
    have := ContinuousLinearMap.adjoint_inner_left A (A t) t
    rw [hA_sa.adjoint_eq] at this
    exact this
  rw [h_self_adjoint_swap]
  -- `A (A t) = toEuclideanCLM (sqrt S · sqrt S) t = toEuclideanCLM S t`.
  have hAA : A ∘L A = toEuclideanCLM (𝕜 := ℝ) S := by
    change A * A = toEuclideanCLM (𝕜 := ℝ) S
    rw [hA_def, ← map_mul, CFC.sqrt_mul_sqrt_self _ hS.nonneg]
  have hAAt : A (A t) = (toEuclideanCLM (𝕜 := ℝ) S) t := by
    change (A ∘L A) t = _
    rw [hAA]
  rw [hAAt, Matrix.inner_toEuclideanCLM]

/-- Bridge lemma: the `WithLp.equiv`-spelling inner product with a `Matrix.mulVec`
in the second argument equals the underlying `dotProduct`. Pure book-keeping. -/
private lemma inner_equivSymm_mulVec_eq_dotProduct
    {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) (S : Matrix (Fin k) (Fin k) ℝ)
    (v : EuclideanSpace ℝ (Fin k)) :
    ⟪u, (WithLp.equiv 2 _).symm (S.mulVec ((WithLp.equiv 2 _) v))⟫
      = u.ofLp ⬝ᵥ S.mulVec v.ofLp := by
  rw [show (u.ofLp ⬝ᵥ S.mulVec v.ofLp) = ∑ i, u.ofLp i * (S.mulVec v.ofLp) i from rfl]
  simp only [PiLp.inner_apply, WithLp.equiv_apply, WithLp.equiv_symm_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  change (S.mulVec v.ofLp) i * u.ofLp i = u.ofLp i * (S.mulVec v.ofLp) i
  ring

/-- **Tilted Gaussian integrates to one**. If `π` has second marginal
`multivariateGaussian 0 J`, then for any `h`, `∫ exp q.2 ∂(π.map tilt_map) = 1`
where `tilt_map p := (p.1, ⟪h, p.2⟫ - ½ ⟪h, J h⟩)`.

This is the **MGF half** of `hMgfTilt` (`LAN_representation`'s Step 5 provider).
Integrability is an immediate corollary via `Integrable.of_integral_ne_zero`. -/
theorem integral_exp_tilt_eq_one
    {k d : ℕ}
    (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure π]
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosSemidef)
    (h_marginal : π.map Prod.snd = multivariateGaussian 0 J)
    (h : EuclideanSpace ℝ (Fin k)) :
    ∫ q, Real.exp q.2 ∂(π.map
        (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k) =>
          (p.1, ⟪h, p.2⟫ - (1 / 2 : ℝ) *
            ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫)))
      = 1 := by
  set c : ℝ := (1 / 2 : ℝ) *
    ⟪h, (WithLp.equiv 2 (Fin k → ℝ)).symm (J.mulVec ((WithLp.equiv 2 (Fin k → ℝ)) h))⟫ with hc_def
  have hc_eq : c = (h.ofLp ⬝ᵥ J.mulVec h.ofLp) / 2 := by
    rw [hc_def, inner_equivSymm_mulVec_eq_dotProduct]; ring
  -- Integrand measurability for the various `integral_map` applications.
  have hexp_meas : AEStronglyMeasurable
      (fun y : EuclideanSpace ℝ (Fin k) => Real.exp ⟪h, y⟫) (multivariateGaussian 0 J) :=
    by fun_prop
  calc ∫ q, Real.exp q.2 ∂(π.map
          (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k) =>
            (p.1, ⟪h, p.2⟫ - c)))
      = ∫ p, Real.exp (⟪h, p.2⟫ - c) ∂π := by
        rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ p, Real.exp ⟪h, p.2⟫ * Real.exp (-c) ∂π := by
        simp_rw [sub_eq_add_neg, Real.exp_add]
    _ = (∫ p, Real.exp ⟪h, p.2⟫ ∂π) * Real.exp (-c) := integral_mul_const _ _
    _ = (∫ y, Real.exp ⟪h, y⟫ ∂(π.map Prod.snd)) * Real.exp (-c) := by
        rw [integral_map (by fun_prop) (by rw [h_marginal]; exact hexp_meas)]
    _ = (∫ y, Real.exp ⟪h, y⟫ ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J))
          * Real.exp (-c) := by rw [h_marginal]
    _ = Real.exp (⟪h, (0 : EuclideanSpace ℝ (Fin k))⟫
          + (h.ofLp ⬝ᵥ J.mulVec h.ofLp) / 2) * Real.exp (-c) := by
        rw [integral_exp_inner_multivariateGaussian 0 J hJ h]
    _ = Real.exp ((h.ofLp ⬝ᵥ J.mulVec h.ofLp) / 2) * Real.exp (-c) := by
        rw [inner_zero_right, zero_add]
    _ = Real.exp (0 : ℝ) := by
        rw [← Real.exp_add, ← hc_eq]; ring_nf
    _ = 1 := Real.exp_zero

/-- **Integrability of the exponential tilt under `π` with Gaussian second marginal**.
Companion to `integral_exp_tilt_eq_one`: the integrand `fun q => exp q.2` is
integrable on `π.map tilt_map`, by `Integrable.of_integral_ne_zero` applied to the
value `1`. -/
theorem integrable_exp_tilt
    {k d : ℕ}
    (π : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k)))
    [IsProbabilityMeasure π]
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosSemidef)
    (h_marginal : π.map Prod.snd = multivariateGaussian 0 J)
    (h : EuclideanSpace ℝ (Fin k)) :
    Integrable (fun q : EuclideanSpace ℝ (Fin d) × ℝ => Real.exp q.2)
      (π.map (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin k) =>
        (p.1, ⟪h, p.2⟫ - (1 / 2 : ℝ) *
          ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫))) :=
  MeasureTheory.integrable_of_integral_eq_one
    (integral_exp_tilt_eq_one π J hJ h_marginal h)

/-- **Linear pushforward identity for multivariate Gaussians** (spelled via the
matrix-to-CLM embedding). For every matrix `A`, the push-forward of
`multivariateGaussian μ S` under `toEuclideanCLM A` equals
`multivariateGaussian (toEuclideanCLM A μ) (A * S * Aᴴ)`.

This is the key measure identity consumed by Theorem 7.10 Step 7 (`hTilt`).
Proof via `IsGaussian.ext`: compute means and covariance bilinear forms on each
side. The covariance side uses `covarianceBilin_map` (which inserts the adjoint,
equal to `toEuclideanCLM Aᴴ` because `toEuclideanCLM` is a star algebra iso),
then `covarianceBilin_multivariateGaussian`, then matrix algebra
(`dotProduct_mulVec` + `Matrix.mul_mulVec`) to collapse `A * S * Aᴴ`. -/
theorem multivariateGaussian_map_toEuclideanCLM
    {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (μ : EuclideanSpace ℝ (Fin k))
    {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosSemidef) :
    (multivariateGaussian μ S).map (Matrix.toEuclideanCLM (𝕜 := ℝ) A)
      = multivariateGaussian (Matrix.toEuclideanCLM (𝕜 := ℝ) A μ)
          (A * S * Aᴴ) := by
  classical
  -- `A * S * Aᴴ` is positive semidefinite (needed for the RHS covariance identity).
  have hT : (A * S * Aᴴ).PosSemidef := by
    have := hS.conjTranspose_mul_mul_same (B := Aᴴ)
    rwa [Matrix.conjTranspose_conjTranspose] at this
  -- Integrability of id under the Gaussian.
  have hInt : Integrable (fun x : EuclideanSpace ℝ (Fin k) => x)
      (multivariateGaussian μ S) := ProbabilityTheory.IsGaussian.integrable_id
  have hMemLp : MeasureTheory.MemLp
      (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) 2
      (multivariateGaussian μ S) := ProbabilityTheory.IsGaussian.memLp_two_id
  refine IsGaussian.ext ?_ ?_
  · -- Means agree: both equal `toEuclideanCLM A μ`.
    simp only [id_eq]
    rw [integral_id_multivariateGaussian,
      integral_map (by fun_prop) (by fun_prop),
      ContinuousLinearMap.integral_comp_id_comm hInt,
      integral_id_multivariateGaussian]
  · -- Covariance bilinear forms agree.
    ext u v
    -- Adjoint of `toEuclideanCLM A` equals `toEuclideanCLM Aᴴ` (star preserving).
    set_option backward.isDefEq.respectTransparency false in
    have h_adj : ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) A)
        = Matrix.toEuclideanCLM (𝕜 := ℝ) Aᴴ := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      exact (map_star (Matrix.toEuclideanCLM (𝕜 := ℝ)) A).symm
    rw [covarianceBilin_map hMemLp,
      covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian hT,
      h_adj]
    simp only [Matrix.ofLp_toEuclideanCLM]
    -- Matrix-algebra identity: `u ⬝ᵥ (A * S * Aᴴ) *ᵥ v = Aᴴ.mulVec u ⬝ᵥ S.mulVec (Aᴴ.mulVec v)`.
    have key : ∀ u' v' : Fin k → ℝ,
        u' ⬝ᵥ (A * S * Aᴴ).mulVec v' = Aᴴ.mulVec u' ⬝ᵥ S.mulVec (Aᴴ.mulVec v') := by
      intro u' v'
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
      congr 1
      -- `vecMul u' A = Aᴴ.mulVec u'` on real matrices: both equal `fun i => ∑ j, A j i * u' j`.
      ext i
      change ∑ j, u' j * A j i = ∑ j, A j i * u' j
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact (key u.ofLp v.ofLp).symm

/-- **CLM lift of `Matrix.toLpLin 2 2`** for rectangular matrices.

For `A : Matrix (Fin d) (Fin k) ℝ`, the linear map
`Matrix.toLpLin 2 2 A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)`
becomes a continuous linear map via `LinearMap.toContinuousLinearMap` (the source
is finite-dim).

Companion to `Matrix.toEuclideanCLM` (which is a star-algebra equivalence only
available for square matrices); this rectangular version supports transporting
Gaussian laws and losses through matrices of shape `d × k`. -/
noncomputable def matrixToEuclideanCLMRect
    {d k : ℕ} (A : Matrix (Fin d) (Fin k) ℝ) :
    EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 A)

@[simp]
lemma ofLp_matrixToEuclideanCLMRect
    {d k : ℕ} (A : Matrix (Fin d) (Fin k) ℝ) (v : EuclideanSpace ℝ (Fin k)) :
    (matrixToEuclideanCLMRect A v).ofLp = A.mulVec v.ofLp := rfl

/-- **Adjoint of `matrixToEuclideanCLMRect A`** equals `matrixToEuclideanCLMRect Aᵀ`.

For real rectangular matrices, the CLM-adjoint of `A.mulVec` is exactly the CLM
of the transpose `Aᵀ.mulVec`, paralleling the square version where `Aᴴ = Aᵀ`
(`conjTranspose_eq_transpose_of_trivial` for `ℝ`).

**Proof**: lift `Matrix.toEuclideanLin_conjTranspose_eq_adjoint` (which says
`Matrix.toEuclideanLin Aᴴ = LinearMap.adjoint (Matrix.toEuclideanLin A)` at the
LinearMap level) to CLM via `LinearMap.adjoint_toContinuousLinearMap` (which
says `LinearMap.toContinuousLinearMap` commutes with adjoint in finite-dim).
For real, `Aᴴ = Aᵀ` via `Matrix.conjTranspose_eq_transpose_of_trivial`. -/
lemma matrixToEuclideanCLMRect_adjoint
    {d k : ℕ} (A : Matrix (Fin d) (Fin k) ℝ) :
    ContinuousLinearMap.adjoint (matrixToEuclideanCLMRect A)
      = matrixToEuclideanCLMRect Aᵀ := by
  unfold matrixToEuclideanCLMRect
  rw [← LinearMap.adjoint_toContinuousLinearMap]
  congr 1
  -- LinearMap.adjoint (Matrix.toLpLin 2 2 A) = Matrix.toLpLin 2 2 Aᵀ.
  -- Substitute Aᵀ = Aᴴ on ℝ, then apply Matrix.toEuclideanLin_conjTranspose_eq_adjoint.
  have hAT_eq : (Aᵀ : Matrix (Fin k) (Fin d) ℝ) = Aᴴ :=
    (Matrix.conjTranspose_eq_transpose_of_trivial A).symm
  rw [hAT_eq]
  exact (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm

/-- **Linear pushforward identity for multivariate Gaussians — rectangular case.**

For a rectangular matrix `A : Matrix (Fin d) (Fin k) ℝ`, the push-forward of
`multivariateGaussian μ S` (on `EuclideanSpace ℝ (Fin k)`) under the CLM
`matrixToEuclideanCLMRect A` (viewed as `E_k →L[ℝ] E_d`) equals
`multivariateGaussian (matrixToEuclideanCLMRect A μ) (A * S * Aᵀ)` on
`EuclideanSpace ℝ (Fin d)`.

Companion to `multivariateGaussian_map_toEuclideanCLM` (square case). It gives
the Gaussian pushforward used to transport loss integrals through a `d × k` matrix:
`∫⁻ g, L(c - ψDotMat g) ∂N(0, S) = ∫⁻ z, L(c - z) ∂N(0, ψDotMat S ψDotMatᵀ)`.

**Proof structure** parallel to the square case (`multivariateGaussian_map_toEuclideanCLM`):
- Means agree via `integral_id_multivariateGaussian` + `integral_map` +
  `ContinuousLinearMap.integral_comp_id_comm`.
- Covariance bilinear forms agree via `covarianceBilin_map` + `matrixToEuclideanCLMRect_adjoint`
  + `covarianceBilin_multivariateGaussian` + matrix algebra
  (`Matrix.dotProduct_mulVec` + `Matrix.mulVec_mulVec` to collapse `A * S * Aᵀ`). -/
theorem multivariateGaussian_map_rectangular
    {d k : ℕ} (A : Matrix (Fin d) (Fin k) ℝ)
    (μ : EuclideanSpace ℝ (Fin k))
    {S : Matrix (Fin k) (Fin k) ℝ} (hS : S.PosSemidef) :
    (multivariateGaussian μ S).map (matrixToEuclideanCLMRect A)
      = multivariateGaussian (matrixToEuclideanCLMRect A μ) (A * S * Aᵀ) := by
  classical
  -- `A * S * Aᵀ` is positive semidefinite.
  have hT : (A * S * Aᵀ).PosSemidef := by
    have := hS.mul_mul_conjTranspose_same A
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  -- Integrability of id under the source Gaussian.
  have hInt : Integrable (fun x : EuclideanSpace ℝ (Fin k) => x)
      (multivariateGaussian μ S) := ProbabilityTheory.IsGaussian.integrable_id
  have hMemLp : MeasureTheory.MemLp
      (id : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) 2
      (multivariateGaussian μ S) := ProbabilityTheory.IsGaussian.memLp_two_id
  refine IsGaussian.ext ?_ ?_
  · -- Means agree: both equal `matrixToEuclideanCLMRect A μ`.
    simp only [id_eq]
    rw [integral_id_multivariateGaussian,
      integral_map (by fun_prop) (by fun_prop),
      ContinuousLinearMap.integral_comp_id_comm hInt,
      integral_id_multivariateGaussian]
  · -- Covariance bilinear forms agree.
    ext u v
    rw [covarianceBilin_map hMemLp,
      covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian hT,
      matrixToEuclideanCLMRect_adjoint]
    simp only [ofLp_matrixToEuclideanCLMRect]
    -- Matrix algebra: `u ⬝ᵥ (A * S * Aᵀ).mulVec v = Aᵀ.mulVec u ⬝ᵥ S.mulVec (Aᵀ.mulVec v)`.
    -- State as a quantified helper to control the `Matrix.dotProduct_mulVec` rewrite
    -- direction (the LHS of the main goal already has a matching pattern,
    -- so direct rewrite would target the wrong side).
    have key : ∀ u' v' : Fin d → ℝ,
        u' ⬝ᵥ (A * S * Aᵀ).mulVec v' = Aᵀ.mulVec u' ⬝ᵥ S.mulVec (Aᵀ.mulVec v') := by
      intro u' v'
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
      congr 1
      -- `vecMul u' A = Aᵀ.mulVec u'` on real matrices: both equal `fun i => ∑ j, A j i * u' j`.
      ext i
      change ∑ j, u' j * A j i = ∑ j, A j i * u' j
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact (key u.ofLp v.ofLp).symm

/-- **Girsanov / Esscher identity for 1D standard Gaussian**. Tilting
`gaussianReal 0 1` by the exponential density `exp(a · x - a² / 2)` produces
`gaussianReal a 1` — i.e., shifts the mean by `a`.

Proof by PDF comparison: both sides rewrite to `volume.withDensity f` via
`gaussianReal_of_var_ne_zero`, then `withDensity_mul` composes the 0-mean PDF
with the exponential tilt, and the resulting density matches the `a`-mean PDF
because `exp(-(x-a)²/2) = exp(-x²/2) · exp(a·x - a²/2)`.

First step of the Girsanov chain for the Theorem 7.10 `hTilt` provider; lifts
to the multivariate case via the product-measure representation of `stdGaussian`. -/
lemma gaussianReal_withDensity_exp_shift (a : ℝ) :
    (gaussianReal 0 1).withDensity
        (fun x => ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2)))
      = gaussianReal a 1 := by
  -- Both `gaussianReal`s admit an explicit `volume.withDensity gaussianPDF` form
  -- (since `v = 1 ≠ 0`), turning the identity into a density-side comparison.
  rw [gaussianReal_of_var_ne_zero (0 : ℝ) (by norm_num : (1 : NNReal) ≠ 0),
    gaussianReal_of_var_ne_zero a (by norm_num : (1 : NNReal) ≠ 0)]
  have h_tilt_meas :
      Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (a * x - a ^ 2 / 2))) := by
    fun_prop
  rw [← MeasureTheory.withDensity_mul volume (measurable_gaussianPDF 0 1) h_tilt_meas]
  congr 1
  ext x
  -- Pointwise identity on densities. Move ENNReal.ofReal out and reduce to real algebra.
  simp only [Pi.mul_apply, gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 1 x)]
  congr 1
  -- Real identity: `gaussianPDFReal 0 1 x · exp(a·x - a²/2) = gaussianPDFReal a 1 x`.
  -- Expand the PDFs and collapse `exp(-x²/2) · exp(a·x - a²/2) = exp(-(x-a)²/2)`.
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Pi-product Girsanov for standard 1D Gaussians**. Tilting the product of `ι`
copies of `gaussianReal 0 1` by `exp(∑ᵢ aᵢ yᵢ - ∑ᵢ aᵢ² / 2)` shifts the mean in each
coordinate:
```
(Measure.pi (fun _ => gaussianReal 0 1)).withDensity
    (fun y => ENNReal.ofReal (Real.exp (∑ i, a i * y i - ∑ i, a i ^ 2 / 2)))
  = Measure.pi (fun i => gaussianReal (a i) 1).
```

Proof goes through `pi_withDensity_prod`: the exponential density factors as a
product `∏ i, exp(aᵢ yᵢ - aᵢ² / 2)`, each factor is the 1D Girsanov density, and
`gaussianReal_withDensity_exp_shift` shifts each component individually.

Second step of the multivariate Girsanov chain (`hTilt` for Theorem 7.10). -/
lemma pi_gaussianReal_withDensity_exp_shift {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).withDensity
        (fun y => ENNReal.ofReal (Real.exp (∑ i, a i * y i - ∑ i, a i ^ 2 / 2)))
      = Measure.pi (fun i : ι => gaussianReal (a i) 1) := by
  classical
  -- Record the 1D Girsanov identity on each coordinate; this gives the
  -- `IsProbabilityMeasure` instance needed for `pi_withDensity_prod`.
  have h1d : ∀ i, (gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (a i * x - a i ^ 2 / 2)))
        = gaussianReal (a i) 1 := fun i => gaussianReal_withDensity_exp_shift (a i)
  haveI : ∀ i, IsProbabilityMeasure ((gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (a i * x - a i ^ 2 / 2)))) := by
    intro i; rw [h1d i]; infer_instance
  -- Factor the product density: `exp(∑ aᵢyᵢ - ∑ aᵢ²/2) = ∏ exp(aᵢyᵢ - aᵢ²/2)`.
  have h_density : (fun y : ι → ℝ =>
        ENNReal.ofReal (Real.exp (∑ i, a i * y i - ∑ i, a i ^ 2 / 2)))
      = fun y => ∏ i, ENNReal.ofReal (Real.exp (a i * y i - a i ^ 2 / 2)) := by
    funext y
    rw [show (∑ i, a i * y i - ∑ i, a i ^ 2 / 2)
          = ∑ i, (a i * y i - a i ^ 2 / 2) from (Finset.sum_sub_distrib _ _).symm,
      Real.exp_sum, ENNReal.ofReal_prod_of_nonneg
        (fun i _ => Real.exp_nonneg _)]
  rw [h_density, pi_withDensity_prod
    (f := fun i x => ENNReal.ofReal (Real.exp (a i * x - a i ^ 2 / 2)))
    (fun i => by fun_prop)]
  congr 1
  funext i
  exact h1d i

/-- **Standard Gaussian Girsanov on `EuclideanSpace ℝ ι`** (Esscher shift). Tilting
the standard Gaussian by `exp(⟪a, y⟫ - ‖a‖² / 2)` shifts the mean by `a`:
```
(stdGaussian (EuclideanSpace ℝ ι)).withDensity
    (fun y => ENNReal.ofReal (Real.exp (⟪a, y⟫ - ‖a‖² / 2)))
  = (stdGaussian (EuclideanSpace ℝ ι)).map (fun y => y + a).
```

Lifts the pi-version `pi_gaussianReal_withDensity_exp_shift` through the isomorphism
`(Measure.pi …).map (WithLp.toLp 2) = stdGaussian (EuclideanSpace ℝ ι)` on both
sides. The LHS commutes withDensity past map (`withDensity_map_eq_map_withDensity`)
and expands `⟪a, toLp y⟫` / `‖a‖²` into coordinate sums. The RHS composes the maps
(`Measure.map_map`), rewrites `+ a` on the Lp side as `+ a.ofLp` on the pi side
(linearity of `WithLp.toLp`), and distributes via `pi_map_pi` + `gaussianReal_map_add_const`. -/
theorem stdGaussian_withDensity_exp_shift {ι : Type*} [Fintype ι]
    (a : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).withDensity
        (fun y => ENNReal.ofReal (Real.exp (⟪a, y⟫ - ‖a‖ ^ 2 / 2)))
      = (stdGaussian (EuclideanSpace ℝ ι)).map (fun y => y + a) := by
  classical
  -- Each 1D shift is a probability measure; promote for `pi_map_pi`'s SigmaFinite instance.
  haveI : ∀ i,
      IsProbabilityMeasure ((gaussianReal 0 1).map (fun x : ℝ => x + a.ofLp i)) := by
    intro i; rw [gaussianReal_map_add_const]; infer_instance
  -- Pull both sides back to `pi` via `map_pi_eq_stdGaussian`.
  rw [← map_pi_eq_stdGaussian (ι := ι)]
  -- LHS: commute withDensity past map. RHS: compose the two maps.
  rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity _ _
    (by fun_prop) _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  -- Rewrite RHS function `(· + a) ∘ toLp = toLp ∘ (· + a.ofLp)` by linearity of `toLp`,
  -- then split the composed map back so both sides have `.map (toLp)` outermost.
  have h_add : ((fun y : EuclideanSpace ℝ ι => y + a) ∘ WithLp.toLp 2 (V := ι → ℝ))
      = (WithLp.toLp 2) ∘ fun y : ι → ℝ => y + a.ofLp := by
    funext y
    simp only [Function.comp_apply]
    rw [WithLp.toLp_add, WithLp.toLp_ofLp]
  rw [h_add, ← Measure.map_map (by fun_prop) (by fun_prop)]
  -- Strip the common `.map (toLp 2)` from both sides.
  congr 1
  -- LHS: rewrite the pulled-back density in pi-coord form, then apply pi-Girsanov.
  have h_density : ((fun y : EuclideanSpace ℝ ι =>
        ENNReal.ofReal (Real.exp (⟪a, y⟫ - ‖a‖ ^ 2 / 2))) ∘ WithLp.toLp 2 (V := ι → ℝ))
      = fun y : ι → ℝ =>
          ENNReal.ofReal (Real.exp (∑ i, a.ofLp i * y i - ∑ i, a.ofLp i ^ 2 / 2)) := by
    funext y
    simp only [Function.comp_apply]
    have h_inner : ⟪a, (WithLp.toLp 2 y : EuclideanSpace ℝ ι)⟫
        = ∑ i, a.ofLp i * y i := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      change y i * a.ofLp i = a.ofLp i * y i
      ring
    have h_norm : (‖a‖ : ℝ) ^ 2 / 2 = (∑ i, a.ofLp i ^ 2) / 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    rw [h_inner, h_norm, Finset.sum_div]
  rw [h_density, pi_gaussianReal_withDensity_exp_shift (fun i => a.ofLp i)]
  -- RHS: distribute the coordinate-wise shift through `pi_map_pi`.
  rw [show (fun y : ι → ℝ => y + a.ofLp) = (fun y i => y i + a.ofLp i) from rfl,
    Measure.pi_map_pi (fun i =>
      (by fun_prop : Measurable (fun x : ℝ => x + a.ofLp i)).aemeasurable)]
  simp_rw [gaussianReal_map_add_const, zero_add]

/-- **Multivariate Gaussian Girsanov / Esscher identity**. Tilting the centred
multivariate Gaussian `N(0, S)` by `exp(⟪h, y⟫ - ⟨h, S h⟩ / 2)` shifts the mean to
`S h`:
```
(multivariateGaussian 0 S).withDensity
    (fun y => ENNReal.ofReal (Real.exp (⟪h, y⟫ - (h.ofLp ⬝ᵥ S.mulVec h.ofLp) / 2)))
  = multivariateGaussian (toEuclideanCLM S h) S.
```

Lifts the `stdGaussian` version `stdGaussian_withDensity_exp_shift` through the
square-root decomposition `multivariateGaussian μ S = stdGaussian.map (μ + √S ·)`.

Let `A = toEuclideanCLM (sqrt S)`; by CFC, `A ∘ A = toEuclideanCLM S`, and since
`sqrt S ≥ 0`, `A` is self-adjoint. The LHS density composed with `A` simplifies:
`⟪h, A x⟫ = ⟪A h, x⟫` (self-adjoint) and `⟨h, S h⟩ = ‖A h‖²` (`A ∘ A = S`),
so `(tilt h) ∘ A = tilt_std (A h)`. Applying the `stdGaussian` shift at parameter
`A h` produces `stdGaussian.map (· + A h)`, and composing with `A` on the outside
yields `stdGaussian.map (fun x => A x + A (A h)) = stdGaussian.map (fun x =>
toEuclideanCLM S h + A x)`, which is `multivariateGaussian (toEuclideanCLM S h) S`
by definition. -/
theorem multivariateGaussian_withDensity_exp_shift {ι : Type*} [Fintype ι]
    [DecidableEq ι] {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (h : EuclideanSpace ℝ ι) :
    (multivariateGaussian 0 S).withDensity
        (fun y => ENNReal.ofReal (Real.exp (⟪h, y⟫
          - (h.ofLp ⬝ᵥ S.mulVec h.ofLp) / 2)))
      = multivariateGaussian (toEuclideanCLM (𝕜 := ℝ) S h) S := by
  classical
  -- Abbreviation `A := toEuclideanCLM (sqrt S)` : self-adjoint, `A ∘ A = toEuclideanCLM S`.
  set A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) with hA_def
  set_option backward.isDefEq.respectTransparency false in
  have hA_sa : IsSelfAdjoint A :=
    (CFC.sqrt_nonneg S).isSelfAdjoint.map (toEuclideanCLM (𝕜 := ℝ))
  have hAA : A ∘L A = toEuclideanCLM (𝕜 := ℝ) S := by
    change A * A = toEuclideanCLM (𝕜 := ℝ) S
    rw [hA_def, ← map_mul, CFC.sqrt_mul_sqrt_self _ hS.nonneg]
  have hA_meas : Measurable A := A.continuous.measurable
  -- Adjoint-swap helper.
  have h_inner_swap : ∀ u v, ⟪u, A v⟫ = ⟪A u, v⟫ := fun u v => by
    have := ContinuousLinearMap.adjoint_inner_left A v u
    rw [hA_sa.adjoint_eq] at this
    exact this.symm
  -- `A (A h) = toEuclideanCLM S h` from `A ∘L A = toEuclideanCLM S`.
  have hAAh : A (A h) = (toEuclideanCLM (𝕜 := ℝ) S) h := by
    change (A ∘L A) h = _
    rw [hAA]
  -- Unfold `multivariateGaussian 0 S = stdGaussian.map A` (the `0 +` simplifies).
  have hMvG0 : multivariateGaussian (0 : EuclideanSpace ℝ ι) S
      = (stdGaussian (EuclideanSpace ℝ ι)).map A := by
    rw [multivariateGaussian]
    congr 1
    funext x
    simp [hA_def]
  -- Unfold RHS similarly.
  have hMvGSh : multivariateGaussian (toEuclideanCLM (𝕜 := ℝ) S h) S
      = (stdGaussian (EuclideanSpace ℝ ι)).map
          (fun x => toEuclideanCLM (𝕜 := ℝ) S h + A x) := by
    rw [multivariateGaussian]
  rw [hMvG0, hMvGSh]
  -- Commute withDensity past `.map A` on the LHS.
  rw [AsymptoticStatistics.Measure.withDensity_map_eq_map_withDensity _ _ hA_meas _
    (by fun_prop)]
  -- Rewrite the pulled-back density as the stdGaussian-tilt at parameter `A h`.
  have h_density : ((fun y : EuclideanSpace ℝ ι =>
        ENNReal.ofReal (Real.exp (⟪h, y⟫ - (h.ofLp ⬝ᵥ S.mulVec h.ofLp) / 2))) ∘ A)
      = fun x => ENNReal.ofReal (Real.exp (⟪A h, x⟫ - ‖A h‖ ^ 2 / 2)) := by
    funext x
    simp only [Function.comp_apply]
    -- Inner-product swap: `⟪h, A x⟫ = ⟪A h, x⟫`.
    have h_inner : ⟪h, A x⟫ = ⟪A h, x⟫ := h_inner_swap h x
    -- `‖A h‖² = h.ofLp ⬝ᵥ S.mulVec h.ofLp`.
    have h_norm_sq : ‖A h‖ ^ 2 = h.ofLp ⬝ᵥ S.mulVec h.ofLp := by
      rw [sq, ← real_inner_self_eq_norm_mul_norm, h_inner_swap, hAAh,
        real_inner_comm, Matrix.inner_toEuclideanCLM]
    rw [h_inner, h_norm_sq]
  rw [h_density, stdGaussian_withDensity_exp_shift (A h),
    Measure.map_map hA_meas (by fun_prop)]
  -- Collapse `A ∘ (· + A h) = (toEuclideanCLM S h + ·) ∘ A`.
  congr 1
  funext x
  simp only [Function.comp_apply]
  rw [A.map_add, hAAh, add_comm]

/-- **Pushforward of a centered multivariate Gaussian under an inner-product
projection** is a centered 1-D Gaussian with variance `⟨h, J h⟩_Mat`.

Proved by `charFun` uniqueness: both sides have characteristic function
`exp(-(h · J · h) t²/2)` — the LHS via `charFun_multivariateGaussian` applied
to the argument `t • h` (after transporting through `integral_map`), the RHS
by `charFun_gaussianReal`. -/
theorem multivariateGaussian_map_inner_eq_gaussianReal
    {k : ℕ} (h : EuclideanSpace ℝ (Fin k))
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosSemidef) :
    Measure.map (fun y : EuclideanSpace ℝ (Fin k) => ⟪h, y⟫)
        (multivariateGaussian 0 J)
      = gaussianReal 0 (h.ofLp ⬝ᵥ J.mulVec h.ofLp).toNNReal := by
  classical
  have hL_meas : Measurable (fun y : EuclideanSpace ℝ (Fin k) => ⟪h, y⟫) :=
    (continuous_const.inner continuous_id).measurable
  haveI : IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) :=
    isGaussian_multivariateGaussian.toIsProbabilityMeasure _
  haveI : IsProbabilityMeasure
      (Measure.map (fun y : EuclideanSpace ℝ (Fin k) => ⟪h, y⟫)
        (multivariateGaussian 0 J)) :=
    Measure.isProbabilityMeasure_map hL_meas.aemeasurable
  -- Nonneg quadratic form.
  have h_quad_nn : 0 ≤ h.ofLp ⬝ᵥ J.mulVec h.ofLp := by
    have := hJ.re_dotProduct_nonneg (x := (h.ofLp : Fin k → ℝ))
    simpa using this
  apply MeasureTheory.Measure.ext_of_charFun
  funext t
  -- LHS: `charFun ((mvG 0 J).map L) t = charFun (mvG 0 J) (t • h)`.
  have hLHS : charFun (Measure.map (fun y : EuclideanSpace ℝ (Fin k) => ⟪h, y⟫)
        (multivariateGaussian 0 J)) t
      = charFun (multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) (t • h) := by
    rw [charFun_apply_real, charFun_apply]
    have h_integrand_meas : AEStronglyMeasurable
        (fun x : ℝ => Complex.exp (↑t * ↑x * Complex.I))
        (Measure.map (fun y : EuclideanSpace ℝ (Fin k) => ⟪h, y⟫)
          (multivariateGaussian 0 J)) :=
      (by fun_prop : Continuous fun x : ℝ =>
        Complex.exp (↑t * ↑x * Complex.I)).aestronglyMeasurable
    rw [integral_map hL_meas.aemeasurable h_integrand_meas]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    simp only []
    -- Identity: `⟨y, t • h⟩ = t * ⟨h, y⟩` (linearity + symmetry).
    rw [real_inner_smul_right, real_inner_comm]
    push_cast
    ring
  rw [hLHS, charFun_multivariateGaussian hJ,
    charFun_gaussianReal]
  -- Clean up mean term: `⟨t • h, 0⟩ = 0`.
  have hmean : (inner ℝ (t • h) (0 : EuclideanSpace ℝ (Fin k))) = 0 := by
    rw [inner_zero_right]
  rw [hmean]
  -- Clean up quadratic: `(t • h).ofLp ⬝ᵥ J.mulVec (t • h).ofLp = t² · (h · J · h)`.
  have hquad : (t • h).ofLp ⬝ᵥ J.mulVec (t • h).ofLp
      = t ^ 2 * (h.ofLp ⬝ᵥ J.mulVec h.ofLp) := by
    have h1 : (t • h).ofLp = t • h.ofLp := rfl
    rw [h1, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      smul_eq_mul]
    ring
  rw [hquad]
  -- Clean up the target-RHS constant: `↑(x.toNNReal) = x` when `x ≥ 0`.
  rw [Real.coe_toNNReal _ h_quad_nn]
  -- Final algebra: both sides equal `exp(-t² (h · J · h) / 2)`.
  push_cast
  ring_nf

end ProbabilityTheory
