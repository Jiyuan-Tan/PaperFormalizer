module
public import StatLean.Minimaxity.ForMathlib.GaussianKLMulti
public import StatLean.Minimaxity.ForMathlib.PinskerInequality
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianDensity

@[expose] public section

/-!
# Total-variation bound between equal-covariance Gaussians

For a positive definite covariance `S`, the Kullback–Leibler divergence between two
Gaussians with the same covariance and different means is the Mahalanobis half-square,
and Pinsker's inequality turns it into a mean-Lipschitz total-variation bound:

* `klDiv_multivariateGaussian_same_cov` —
  `KL(N(a,S) ‖ N(b,S)) = ⟪a − b, S⁻¹(a − b)⟫ / 2`;
* `tvDist_multivariateGaussian_le` —
  `tvDist (N(a,S)) (N(b,S)) ≤ (⟪a − b, S⁻¹(a − b)⟫ / 4) ^ (1/2)`.

This is the brick behind the efficient-centering corollary of the Bernstein–von Mises
theorem (vdV Chapter 10, remark after the exponential-tests lemma, p. 144): replacing the centering
`Δ_{n,θ₀}` by any asymptotically equivalent sequence `√n(θ̂_n − θ₀)` changes the Gaussian
approximation by at most a multiple of the difference of the centers.

**Proof formalization notes.** Whitening: push both Gaussians through
`toEuclideanCLM (CFC.sqrt S⁻¹)` (KL is invariant under measurable-equivalence pushforward,
`klDiv_map_eq_of_comp` in `GaussianKLMulti`), reducing to the scalar-covariance case
`klDiv_multivariateGaussian_smul_one` at `c = 1`. Pinsker is
`StatLean.Minimaxity.pinsker_tv_le_kl : tvDist μ ν ≤ (2⁻¹ * klDiv ν μ) ^ (1/2)`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Matrix
open scoped RealInnerProductSpace ENNReal NNReal MatrixOrder
open StatLean.Minimaxity

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Local bricks -/

-- General-index linear pushforward of a multivariate Gaussian: `N(μ,S).map (M·) = N(Mμ, M S Mᴴ)`.
-- (The `Fin`-indexed version lives in `AsymptoticStatistics`; the general-`ι` one there is
-- `private`, so we reproduce the same `IsGaussian.ext` argument here.)
private lemma map_toEuclideanCLM_mvGaussian
    (M : Matrix ι ι ℝ) (μ : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    (multivariateGaussian μ S).map (Matrix.toEuclideanCLM (𝕜 := ℝ) M)
      = multivariateGaussian (Matrix.toEuclideanCLM (𝕜 := ℝ) M μ) (M * S * Mᴴ) := by
  classical
  have hT : (M * S * Mᴴ).PosSemidef := by
    have := hS.conjTranspose_mul_mul_same (B := Mᴴ)
    rwa [Matrix.conjTranspose_conjTranspose] at this
  have hInt : Integrable (fun x : EuclideanSpace ℝ ι => x) (multivariateGaussian μ S) :=
    ProbabilityTheory.IsGaussian.integrable_id
  have hMemLp : MeasureTheory.MemLp (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) 2
      (multivariateGaussian μ S) := ProbabilityTheory.IsGaussian.memLp_two_id
  refine IsGaussian.ext ?_ ?_
  · simp only [id_eq]
    rw [integral_id_multivariateGaussian, integral_map (by fun_prop) (by fun_prop),
      ContinuousLinearMap.integral_comp_id_comm hInt, integral_id_multivariateGaussian]
  · ext u v
    set_option backward.isDefEq.respectTransparency false in
    have h_adj : ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) M)
        = Matrix.toEuclideanCLM (𝕜 := ℝ) Mᴴ := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      exact (map_star (Matrix.toEuclideanCLM (𝕜 := ℝ)) M).symm
    rw [covarianceBilin_map hMemLp, covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian hT, h_adj]
    simp only [Matrix.ofLp_toEuclideanCLM]
    have key : ∀ u' v' : ι → ℝ,
        u' ⬝ᵥ (M * S * Mᴴ).mulVec v' = Mᴴ.mulVec u' ⬝ᵥ S.mulVec (Mᴴ.mulVec v') := by
      intro u' v'
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
      congr 1
      ext i
      change ∑ j, u' j * M j i = ∑ j, M j i * u' j
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    exact (key u.ofLp v.ofLp).symm

-- Identity-covariance KL on a general index type, obtained from the `Fin`-indexed
-- `klDiv_multivariateGaussian_smul_one` by transporting along a linear isometry equivalence.
private lemma klDiv_mvGaussian_one (m m' : EuclideanSpace ℝ ι) :
    klDiv (multivariateGaussian m (1 : Matrix ι ι ℝ))
        (multivariateGaussian m' (1 : Matrix ι ι ℝ))
      = ENNReal.ofReal (‖m - m'‖ ^ 2 / 2) := by
  classical
  set n := Module.finrank ℝ (EuclideanSpace ℝ ι) with hn
  set E : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (stdOrthonormalBasis ℝ (EuclideanSpace ℝ ι)).repr with hE
  have hEm : Measurable (⇑E) := E.continuous.measurable
  have hEsm : Measurable (⇑E.symm) := E.symm.continuous.measurable
  have hmap : ∀ v : EuclideanSpace ℝ ι,
      (multivariateGaussian v (1 : Matrix ι ι ℝ)).map (⇑E)
        = multivariateGaussian (E v) (1 : Matrix (Fin n) (Fin n) ℝ) := by
    intro v
    rw [← AsymptoticStatistics.multivariateGaussian_map_const_add (1 : Matrix ι ι ℝ) v,
      multivariateGaussian_zero_one, Measure.map_map hEm (by fun_prop)]
    have hfun : (⇑E) ∘ (fun x => v + x) = (fun y => E v + y) ∘ (⇑E) := by
      funext x; simp
    rw [hfun, ← Measure.map_map (by fun_prop) hEm, ProbabilityTheory.stdGaussian_map E,
      ← multivariateGaussian_zero_one,
      AsymptoticStatistics.multivariateGaussian_map_const_add]
  rw [← klDiv_map_eq_of_comp (f := ⇑E) (g := ⇑E.symm) hEm hEsm
      (by funext x; simp) (multivariateGaussian m (1 : Matrix ι ι ℝ))
      (multivariateGaussian m' (1 : Matrix ι ι ℝ)), hmap, hmap]
  have hone : ((1 : ℝ≥0) • (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 := by
    ext i j; simp
  have hkl := klDiv_multivariateGaussian_smul_one (E m) (E m') 1 one_ne_zero
  rw [hone] at hkl
  simp only [NNReal.coe_one, mul_one] at hkl
  rw [hkl, ← map_sub E m m', E.norm_map]

/-- **Equal-covariance Gaussian KL divergence** (Mahalanobis half-square): for positive
definite `S`,
`KL(N(a,S) ‖ N(b,S)) = ofReal (⟪a − b, S⁻¹ (a − b)⟫ / 2)`. -/
theorem klDiv_multivariateGaussian_same_cov
    {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness (KL between singular Gaussians is degenerate)
    (hS : S.PosDef) (a b : EuclideanSpace ℝ ι) :
    klDiv (multivariateGaussian a S) (multivariateGaussian b S)
      = ENNReal.ofReal (⟪a - b, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) (a - b)⟫ / 2) := by
  classical
  have hSinv : S⁻¹.PosDef := hS.inv
  set W : Matrix ι ι ℝ := CFC.sqrt S⁻¹ with hWdef
  have hW : W.PosDef := hSinv.isStrictlyPositive.sqrt.posDef
  have hWW : W * W = S⁻¹ := CFC.sqrt_mul_sqrt_self _ hSinv.posSemidef.nonneg
  have hdetS : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
  have hdetW : IsUnit W.det := (Matrix.isUnit_iff_isUnit_det _).mp hW.isUnit
  -- `W⁻¹ = W * S`, hence the whitening identity `W S W = 1`.
  have h1 : W * (W * S) = 1 := by
    rw [← Matrix.mul_assoc, hWW, Matrix.nonsing_inv_mul _ hdetS]
  have hWinv : W⁻¹ = W * S := Matrix.inv_eq_right_inv h1
  have hWSW : W * S * W = 1 := by
    rw [← hWinv]; exact Matrix.nonsing_inv_mul _ hdetW
  have hmap : ∀ v : EuclideanSpace ℝ ι,
      (multivariateGaussian v S).map (Matrix.toEuclideanCLM (𝕜 := ℝ) W)
        = multivariateGaussian ((Matrix.toEuclideanCLM (𝕜 := ℝ) W) v) (1 : Matrix ι ι ℝ) := by
    intro v
    rw [map_toEuclideanCLM_mvGaussian W v hS.posSemidef, hW.isHermitian.eq, hWSW]
  have hcomp : ⇑(Matrix.toEuclideanCLM (𝕜 := ℝ) W⁻¹) ∘ ⇑(Matrix.toEuclideanCLM (𝕜 := ℝ) W)
      = id := by
    funext x
    simp only [Function.comp_apply, id_eq, ← ContinuousLinearMap.mul_apply, ← map_mul,
      Matrix.nonsing_inv_mul _ hdetW, map_one, ContinuousLinearMap.one_apply]
  -- `‖W (a − b)‖² = ⟪a − b, S⁻¹ (a − b)⟫` by self-adjointness of `W` and `W * W = S⁻¹`.
  have hnorm : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) W) a - (Matrix.toEuclideanCLM (𝕜 := ℝ) W) b‖ ^ 2
      = ⟪a - b, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) (a - b)⟫ := by
    rw [← map_sub, sq, ← real_inner_self_eq_norm_mul_norm]
    set A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
      Matrix.toEuclideanCLM (𝕜 := ℝ) W with hA
    set_option backward.isDefEq.respectTransparency false in
    have hAsa : IsSelfAdjoint A :=
      (CFC.sqrt_nonneg S⁻¹).isSelfAdjoint.map (Matrix.toEuclideanCLM (𝕜 := ℝ))
    have hswap : ⟪A (a - b), A (a - b)⟫ = ⟪a - b, A (A (a - b))⟫ := by
      have h := ContinuousLinearMap.adjoint_inner_left A (A (a - b)) (a - b)
      rw [hAsa.adjoint_eq] at h
      exact h
    rw [hswap]
    congr 1
    change (A * A) (a - b) = _
    rw [hA, ← map_mul, hWW]
  rw [← klDiv_map_eq_of_comp (f := ⇑(Matrix.toEuclideanCLM (𝕜 := ℝ) W))
      (g := ⇑(Matrix.toEuclideanCLM (𝕜 := ℝ) W⁻¹)) (by fun_prop) (by fun_prop) hcomp
      (multivariateGaussian a S) (multivariateGaussian b S), hmap, hmap,
    klDiv_mvGaussian_one, hnorm]

/-- **Mean-shift total-variation bound for equal-covariance Gaussians** (Pinsker route):
`tvDist (N(a,S)) (N(b,S)) ≤ (⟪a − b, S⁻¹(a − b)⟫ / 4) ^ (1/2)`. In particular the TV
distance tends to `0` whenever `a − b → 0`. -/
theorem tvDist_multivariateGaussian_le
    {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness (feeds the KL identity above)
    (hS : S.PosDef) (a b : EuclideanSpace ℝ ι) :
    tvDist (multivariateGaussian a S) (multivariateGaussian b S)
      ≤ (ENNReal.ofReal (⟪a - b, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) (a - b)⟫ / 4))
          ^ (1 / 2 : ℝ) := by
  have hq : ⟪b - a, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) (b - a)⟫
      = ⟪a - b, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) (a - b)⟫ := by
    rw [← neg_sub a b, map_neg, inner_neg_neg]
  have key : ∀ q : ℝ, (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (q / 2) = ENNReal.ofReal (q / 4) := by
    intro q
    rw [show (q / 4 : ℝ) = 2⁻¹ * (q / 2) by ring, ENNReal.ofReal_mul (by norm_num)]
    congr 1
    rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    simp
  refine (pinsker_tv_le_kl _ _).trans (le_of_eq ?_)
  rw [klDiv_multivariateGaussian_same_cov hS b a, hq, key]

end StatLean.Bayesian
