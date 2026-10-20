module
public import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
public import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianWeakLimit
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

/-!
# Lebesgue density bricks for the multivariate Gaussian

Mathlib's `ProbabilityTheory.multivariateGaussian μ S` is defined as a pushforward of
`stdGaussian` and carries no explicit Lebesgue density. This file provides the density
facts needed by the Bernstein–von Mises development (vdV Chapter 10), all for a
**positive definite** covariance `S`:

* `multivariateGaussian_map_const_add` — translation pushforward `N(0,S).map (m + ·) = N(m,S)`;
* `multivariateGaussian_map_matrix_inv` — whitening-type pushforward
  `N(0,J).map (J⁻¹·) = N(0,J⁻¹)`;
* `multivariateGaussian_eq_smul_withDensity` — the **constant-free density**: `N(0,S)` is a
  positive finite multiple of `volume.withDensity (exp (−⟪x, S⁻¹x⟫/2))`. All Chapter-10 uses
  are ratios or normalized restrictions, so the normalizing constant `(2π)^{-d/2} det(S)^{-1/2}`
  is deliberately left abstract;
* `multivariateGaussian_eq_withDensity_tilt` — the mean-shift exponential tilt
  `N(m,S) = N(0,S).withDensity (exp (⟪S⁻¹m, y⟫ − ⟪m,S⁻¹m⟫/2))` (Cameron–Martin form);
* `exists_forall_multivariateGaussian_le_smul_volume` — mean-uniform density **upper** bound;
* `exists_pos_smul_volume_le_multivariateGaussian` — density **lower** bound on bounded sets,
  uniform over bounded means;
* `multivariateGaussian_compl_closedBall_uniform_small` — mean-uniform tail smallness;
* `gaussian_loss_convolution_lt_top` / `gaussian_loss_convolution_continuous` — finiteness and
  continuity of `u ↦ ∫⁻ ℓ(u − z) dN(0,S)(z)` for polynomially growing `ℓ` (used for the limit
  criterion function of vdV Theorem 10.8).

**Proof formalization notes.** The density route: `stdGaussian = (Measure.pi gaussianReal(0,1))`
pushed through an orthonormal-basis equiv (`map_pi_eq_stdGaussian`), whose product density is
`pi_gaussianReal_eq_withDensity`; then push through the invertible `toEuclideanCLM (CFC.sqrt S)`
using `Measure.map_linearMap_addHaar_eq_smul_addHaar` (the `|det|` factor is absorbed into the
abstract constant) and the self-adjointness moves for `CFC.sqrt` already used in
`GaussianMGF.lean` (`multivariateGaussian_withDensity_exp_shift`). The tilt is the existing
`multivariateGaussian_withDensity_exp_shift` at `h := S⁻¹ m`, using
`toEuclideanCLM S (S⁻¹ m) = m` for invertible `S`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped RealInnerProductSpace ENNReal MatrixOrder

namespace AsymptoticStatistics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Translation pushforward of a centered Gaussian.** `N(0,S).map (m + ·) = N(m,S)`.
Holds for arbitrary `S` (both sides are pushforwards of `stdGaussian`; the degenerate
`¬PosSemidef` case is Dirac on both sides). -/
theorem multivariateGaussian_map_const_add
    (S : Matrix ι ι ℝ) (m : EuclideanSpace ℝ ι) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).map (fun x => m + x)
      = multivariateGaussian m S := by
  rw [multivariateGaussian, multivariateGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp

-- General-index linear pushforward of a multivariate Gaussian: `N(μ,S).map (M·) = N(Mμ, M S Mᴴ)`.
-- (`AsymptoticStatistics.multivariateGaussian_map_toEuclideanCLM` is stated only for `Fin k`.)
private lemma map_toEuclideanCLM_multivariateGaussian
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

/-- **Whitening pushforward**: for positive definite `J`,
`N(0,J).map (J⁻¹·) = N(0, J⁻¹)`. Immediate from
`multivariateGaussian_map_toEuclideanCLM` and `J⁻¹ * J * (J⁻¹)ᴴ = J⁻¹` (Hermitian inverse). -/
theorem multivariateGaussian_map_matrix_inv
    {J : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness makes `J` invertible; degenerate case meaningless
    (hJ : J.PosDef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) J).map
        (Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹)
      = multivariateGaussian (0 : EuclideanSpace ℝ ι) J⁻¹ := by
  classical
  have hdet : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det _).mp hJ.isUnit
  have hherm : J⁻¹.IsHermitian := hJ.isHermitian.inv
  have hcov : J⁻¹ * J * (J⁻¹)ᴴ = J⁻¹ := by
    rw [hherm.eq, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have h := map_toEuclideanCLM_multivariateGaussian J⁻¹
    (0 : EuclideanSpace ℝ ι) hJ.posSemidef
  rw [hcov, map_zero] at h
  exact h

-- The standard Gaussian on `EuclideanSpace ℝ ι` is a positive finite multiple of
-- `volume.withDensity (exp (−‖x‖²/2))`; the constant `(2π)^{-d/2}` is left abstract.
private lemma stdGaussian_eq_smul_withDensity_euclidean :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      stdGaussian (EuclideanSpace ℝ ι)
        = c • (volume : Measure (EuclideanSpace ℝ ι)).withDensity
            (fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2))) := by
  classical
  have hsq : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  set C : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ ^ (Fintype.card ι) with hC
  have hCpos : 0 < C := by rw [hC]; positivity
  refine ⟨ENNReal.ofReal C, by simpa using hCpos, ENNReal.ofReal_ne_top, ?_⟩
  have hpres : MeasurePreserving (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)
      (volume : Measure (ι → ℝ)) (volume : Measure (EuclideanSpace ℝ ι)) :=
    PiLp.volume_preserving_toLp ι
  set hd : EuclideanSpace ℝ ι → ℝ≥0∞ :=
    fun y => ENNReal.ofReal (C * Real.exp (-‖y‖ ^ 2 / 2)) with hhd
  have hhdmeas : Measurable hd := by rw [hhd]; fun_prop
  have hcomp : (hd ∘ (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι))
      = fun x : ι → ℝ => ∏ i, gaussianPDF 0 1 (x i) := by
    funext x
    have hnorm : ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖ ^ 2 = ∑ i, x i ^ 2 :=
      EuclideanSpace.real_norm_sq_eq _
    have hprod : ∏ i, gaussianPDFReal 0 1 (x i) = C * Real.exp (-(∑ i, x i ^ 2) / 2) := by
      have hterm : ∀ i : ι, gaussianPDFReal 0 1 (x i)
          = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x i ^ 2) / 2) := by
        intro i; simp [gaussianPDFReal]
      rw [Finset.prod_congr rfl (fun i _ => hterm i), Finset.prod_mul_distrib,
        Finset.prod_const, ← Real.exp_sum, Finset.card_univ, hC]
      congr 1
      rw [← Finset.sum_div, ← Finset.sum_neg_distrib]
    simp only [Function.comp_apply, hhd, hnorm, gaussianPDF]
    rw [← hprod, ← ENNReal.ofReal_prod_of_nonneg]
    exact fun i _ => gaussianPDFReal_nonneg 0 1 (x i)
  rw [← map_pi_eq_stdGaussian, pi_gaussianReal_eq_withDensity, ← hcomp,
    ← Measure.withDensity_map_eq_map_withDensity _ _ hpres.measurable _ hhdmeas, hpres.map_eq]
  have hsplit : hd = (ENNReal.ofReal C) •
      (fun y : EuclideanSpace ℝ ι => ENNReal.ofReal (Real.exp (-‖y‖ ^ 2 / 2))) := by
    funext y
    simp only [Pi.smul_apply, smul_eq_mul, hhd]
    rw [ENNReal.ofReal_mul hCpos.le]
  rw [hsplit, withDensity_smul _ (by fun_prop)]

-- Pushforward of Lebesgue measure under an invertible matrix CLM is a positive finite
-- multiple of Lebesgue measure (Haar uniqueness; the `|det|` factor is left abstract).
private lemma exists_smul_volume_map_toEuclideanCLM {Q : Matrix ι ι ℝ} (hQ : Q.PosDef) :
    ∃ r : ℝ≥0∞, 0 < r ∧ r ≠ ∞ ∧
      (volume : Measure (EuclideanSpace ℝ ι)).map (Matrix.toEuclideanCLM (𝕜 := ℝ) Q)
        = r • (volume : Measure (EuclideanSpace ℝ ι)) := by
  have hUnit : IsUnit (Matrix.toEuclideanCLM (𝕜 := ℝ) Q) :=
    (MulEquiv.isUnit_map (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι))).mpr hQ.isUnit
  let T : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι := ContinuousLinearEquiv.ofUnit hUnit.unit
  have hTeq : ⇑T = ⇑(Matrix.toEuclideanCLM (𝕜 := ℝ) Q) := rfl
  haveI hHaar : ((volume : Measure (EuclideanSpace ℝ ι)).map T).IsAddHaarMeasure :=
    ContinuousLinearEquiv.isAddHaarMeasure_map T (volume : Measure (EuclideanSpace ℝ ι))
  refine ⟨(Measure.addHaarScalarFactor ((volume : Measure (EuclideanSpace ℝ ι)).map T)
      (volume : Measure (EuclideanSpace ℝ ι)) : ℝ≥0∞), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  · rw [← hTeq]
    exact Measure.isAddLeftInvariant_eq_smul _ _

/-- **Constant-free Lebesgue density of the centered Gaussian.** For positive definite `S`
there is a positive finite constant `c` (the normalizer `(2π)^{-d/2} det S^{-1/2}`, left
abstract) with
`N(0,S) = c • volume.withDensity (fun x => exp (−⟪x, S⁻¹x⟫/2))`. -/
theorem multivariateGaussian_eq_smul_withDensity
    {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness; the density statement is false for singular `S`
    (hS : S.PosDef) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      multivariateGaussian (0 : EuclideanSpace ℝ ι) S
        = c • volume.withDensity
            (fun x => ENNReal.ofReal
              (Real.exp (-⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x⟫ / 2))) := by
  classical
  obtain ⟨c₀, hc₀pos, hc₀top, hstd⟩ := stdGaussian_eq_smul_withDensity_euclidean (ι := ι)
  have hQPD : (CFC.sqrt S).PosDef := hS.isStrictlyPositive.sqrt.posDef
  obtain ⟨r, hrpos, hrtop, hr⟩ := exists_smul_volume_map_toEuclideanCLM hQPD
  have hQdet : IsUnit (CFC.sqrt S).det := (Matrix.isUnit_iff_isUnit_det _).mp hQPD.isUnit
  have hQQ : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg
  have hBB : (CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹ = S⁻¹ := by
    rw [← Matrix.mul_inv_rev, hQQ]
  have hBQ : (CFC.sqrt S)⁻¹ * CFC.sqrt S = 1 := Matrix.nonsing_inv_mul _ hQdet
  have hBsa : IsSelfAdjoint ((CFC.sqrt S)⁻¹) := hQPD.isHermitian.inv
  set_option backward.isDefEq.respectTransparency false in
  have hA'sa : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) :=
    hBsa.map (Matrix.toEuclideanCLM (𝕜 := ℝ))
  have hswap : ∀ u v : EuclideanSpace ℝ ι,
      ⟪u, (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) v⟫
        = ⟪(Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) u, v⟫ := by
    intro u v
    have h := ContinuousLinearMap.adjoint_inner_left
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) v u
    rw [hA'sa.adjoint_eq] at h
    exact h.symm
  -- the two mutually inverse CLMs
  have hA'A : ∀ x : EuclideanSpace ℝ ι,
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹)
        ((Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) x) = x := by
    intro x
    have hid : (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) *
        (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) = 1 := by
      rw [← map_mul, hBQ, map_one]
    exact congrArg (fun T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι => T x) hid
  -- the Mahalanobis form is the squared norm after whitening
  have hdens : ∀ x : EuclideanSpace ℝ ι,
      ⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x⟫
        = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) x‖ ^ 2 := by
    intro x
    have hSinv : (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x
        = (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹)
            ((Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) x) := by
      rw [← hBB, map_mul]; rfl
    rw [hSinv, hswap, real_inner_self_eq_norm_sq]
  refine ⟨c₀ * r, ENNReal.mul_pos hc₀pos.ne' hrpos.ne', ENNReal.mul_ne_top hc₀top hrtop, ?_⟩
  have hmvg : multivariateGaussian (0 : EuclideanSpace ℝ ι) S
      = (stdGaussian (EuclideanSpace ℝ ι)).map
          (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)) := by
    rw [multivariateGaussian]
    congr 1
    funext x
    rw [zero_add]
  have hcompose : ((fun y : EuclideanSpace ℝ ι =>
        ENNReal.ofReal (Real.exp (-⟪y, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) y⟫ / 2)))
      ∘ (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)))
      = fun y : EuclideanSpace ℝ ι => ENNReal.ofReal (Real.exp (-‖y‖ ^ 2 / 2)) := by
    funext y
    simp only [Function.comp_apply]
    rw [hdens, hA'A y]
  rw [hmvg, hstd, Measure.map_smul, ← hcompose,
    ← Measure.withDensity_map_eq_map_withDensity _ _ (by fun_prop) _ (by fun_prop), hr,
    withDensity_smul_measure, smul_smul]

/-- **Mean-shift exponential tilt** (Cameron–Martin, invertible-covariance form):
`N(m,S) = N(0,S).withDensity (fun y => exp (⟪S⁻¹m, y⟫ − ⟪m, S⁻¹m⟫/2))`.
This is `multivariateGaussian_withDensity_exp_shift` at `h := S⁻¹ m`. -/
theorem multivariateGaussian_eq_withDensity_tilt
    {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness gives `toEuclideanCLM S (S⁻¹ m) = m`
    (hS : S.PosDef) (m : EuclideanSpace ℝ ι) :
    multivariateGaussian m S
      = (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).withDensity
          (fun y => ENNReal.ofReal
            (Real.exp (⟪(Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) m, y⟫
              - ⟪m, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) m⟫ / 2))) := by
  classical
  set h : EuclideanSpace ℝ ι := (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) m with hh
  have hSh : (Matrix.toEuclideanCLM (𝕜 := ℝ) S) h = m := by
    rw [hh, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, ← map_mul,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit), map_one]
    rfl
  have hquad : h.ofLp ⬝ᵥ S.mulVec h.ofLp = ⟪m, h⟫ := by
    rw [← Matrix.inner_toEuclideanCLM, hSh, real_inner_comm]
  have brick := multivariateGaussian_withDensity_exp_shift hS.posSemidef h
  rw [hSh] at brick
  rw [← brick]
  simp_rw [hquad]

-- The Mahalanobis form of a positive definite `S` is nonnegative.
private lemma inner_mahalanobis_nonneg {S : Matrix ι ι ℝ} (hS : S.PosDef)
    (x : EuclideanSpace ℝ ι) :
    0 ≤ ⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x⟫ := by
  rw [Matrix.inner_toEuclideanCLM]
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hS.inv.posSemidef).2 x.ofLp
  simpa using h

-- Cauchy–Schwarz bound on the Mahalanobis form by the operator norm.
private lemma inner_mahalanobis_le (S : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    ⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x⟫
      ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹‖ * ‖x‖ ^ 2 := by
  calc ⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x⟫
      ≤ ‖x‖ * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x‖ := real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹‖ * ‖x‖) := by
        exact mul_le_mul_of_nonneg_left
          ((Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹).le_opNorm x) (norm_nonneg _)
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹‖ * ‖x‖ ^ 2 := by ring

/-- **Mean-uniform density upper bound.** The Gaussian density is bounded by a constant
independent of the mean: there is `D < ∞` with `N(m,S) A ≤ D · volume A` for every mean `m`
and every set `A` (outer-measure monotonicity handles non-measurable `A`). -/
theorem exists_forall_multivariateGaussian_le_smul_volume
    {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness; a singular Gaussian is not volume-dominated
    (hS : S.PosDef) :
    ∃ D : ℝ≥0∞, D ≠ ∞ ∧
      ∀ (m : EuclideanSpace ℝ ι) (A : Set (EuclideanSpace ℝ ι)),
        multivariateGaussian m S A ≤ D * volume A := by
  classical
  obtain ⟨c, hcpos, hctop, hc⟩ := multivariateGaussian_eq_smul_withDensity hS
  have hle1 : ∀ x : EuclideanSpace ℝ ι,
      ENNReal.ofReal (Real.exp (-⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x⟫ / 2)) ≤ 1 := by
    intro x
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr (by linarith [inner_mahalanobis_nonneg hS x])
  have hdensle : ∀ B : Set (EuclideanSpace ℝ ι), MeasurableSet B →
      multivariateGaussian (0 : EuclideanSpace ℝ ι) S B ≤ c * volume B := by
    intro B hB
    rw [hc]
    simp only [Measure.smul_apply, smul_eq_mul]
    refine mul_le_mul_right ?_ c
    rw [withDensity_apply _ hB]
    calc ∫⁻ x in B, ENNReal.ofReal
            (Real.exp (-⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x⟫ / 2)) ∂volume
        ≤ ∫⁻ _ in B, (1 : ℝ≥0∞) ∂volume := lintegral_mono fun x => hle1 x
      _ = volume B := by simp
  refine ⟨c, hctop, fun m A => ?_⟩
  obtain ⟨T, hAT, hTmeas, hTvol⟩ :=
    exists_measurable_superset (volume : Measure (EuclideanSpace ℝ ι)) A
  have hshift : Measurable fun x : EuclideanSpace ℝ ι => m + x := by fun_prop
  calc multivariateGaussian m S A ≤ multivariateGaussian m S T := measure_mono hAT
    _ = multivariateGaussian (0 : EuclideanSpace ℝ ι) S ((fun x => m + x) ⁻¹' T) := by
        rw [← multivariateGaussian_map_const_add S m, Measure.map_apply hshift hTmeas]
    _ ≤ c * volume ((fun x => m + x) ⁻¹' T) := hdensle _ (hshift hTmeas)
    _ = c * volume T := by rw [measure_preimage_add]
    _ = c * volume A := by rw [hTvol]

/-- **Density lower bound on bounded sets, uniform over bounded means.** For every
radius pair `R, r` there is `c > 0` with `c · volume A ≤ N(m,S) A` for all `‖m‖ ≤ R` and all
measurable `A ⊆ closedBall 0 r`. -/
theorem exists_pos_smul_volume_le_multivariateGaussian
    {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness; a singular Gaussian has volume-null support
    (hS : S.PosDef) (R r : ℝ) :
    ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ m : EuclideanSpace ℝ ι, ‖m‖ ≤ R →
        ∀ A : Set (EuclideanSpace ℝ ι), A ⊆ Metric.closedBall 0 r → MeasurableSet A →
          c * volume A ≤ multivariateGaussian m S A := by
  classical
  obtain ⟨c₀, hc₀pos, hc₀top, hc⟩ := multivariateGaussian_eq_smul_withDensity hS
  set K : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹‖ with hK
  set M : ℝ := |R| + |r| with hM
  set ε : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(K * M ^ 2) / 2)) with hε
  have hεpos : 0 < ε := by rw [hε]; exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  refine ⟨c₀ * ε, ENNReal.mul_pos hc₀pos.ne' hεpos.ne', fun m hm A hA hAmeas => ?_⟩
  have hshift : Measurable fun x : EuclideanSpace ℝ ι => m + x := by fun_prop
  set P : Set (EuclideanSpace ℝ ι) := (fun x => m + x) ⁻¹' A with hP
  have hPmeas : MeasurableSet P := hshift hAmeas
  have hPnorm : ∀ x ∈ P, ‖x‖ ≤ M := by
    intro x hx
    have h1 : ‖m + x‖ ≤ |r| := by
      have := hA hx
      rw [mem_closedBall_zero_iff] at this
      exact this.trans (le_abs_self r)
    have h2 : ‖m‖ ≤ |R| := hm.trans (le_abs_self R)
    have : ‖x‖ = ‖(m + x) - m‖ := by rw [add_sub_cancel_left]
    rw [this, hM]
    calc ‖(m + x) - m‖ ≤ ‖m + x‖ + ‖m‖ := norm_sub_le _ _
      _ ≤ |r| + |R| := add_le_add h1 h2
      _ = |R| + |r| := add_comm _ _
  have hεle : ∀ x ∈ P, ε ≤ ENNReal.ofReal
      (Real.exp (-⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x⟫ / 2)) := by
    intro x hx
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have hqle : ⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x⟫ ≤ K * M ^ 2 := by
      refine (inner_mahalanobis_le S x).trans ?_
      have hKnn : 0 ≤ K := by rw [hK]; exact norm_nonneg _
      have := hPnorm x hx
      have hsq : ‖x‖ ^ 2 ≤ M ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _) this
      exact mul_le_mul_of_nonneg_left hsq hKnn
    linarith
  have hmapped : multivariateGaussian m S A
      = multivariateGaussian (0 : EuclideanSpace ℝ ι) S P := by
    rw [← multivariateGaussian_map_const_add S m, Measure.map_apply hshift hAmeas]
  rw [hmapped, hc]
  simp only [Measure.smul_apply, smul_eq_mul]
  have hvolP : volume P = volume A := measure_preimage_add _ _ _
  rw [withDensity_apply _ hPmeas, mul_assoc, ← hvolP]
  refine mul_le_mul_right ?_ c₀
  calc ε * volume P = ∫⁻ _ in P, ε ∂volume := (setLIntegral_const P ε).symm
    _ ≤ ∫⁻ x in P, ENNReal.ofReal
          (Real.exp (-⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x⟫ / 2)) ∂volume :=
        lintegral_mono_ae (ae_restrict_of_forall_mem hPmeas hεle)

/-- **Mean-uniform tail smallness.** For means in a fixed ball, the Gaussian mass outside
`closedBall 0 M` is eventually (in `M`) below any `ε > 0`, uniformly over the mean. No
definiteness assumption is needed (the degenerate case is a Dirac, whose tail vanishes). -/
theorem multivariateGaussian_compl_closedBall_uniform_small
    (S : Matrix ι ι ℝ) (R : ℝ) {ε : ℝ≥0∞}
    -- LEAN-ONLY: nontrivial tolerance
    (hε : 0 < ε) :
    ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → ∀ m : EuclideanSpace ℝ ι, ‖m‖ ≤ R →
      multivariateGaussian m S (Metric.closedBall (0 : EuclideanSpace ℝ ι) M)ᶜ ≤ ε := by
  classical
  set ν := multivariateGaussian (0 : EuclideanSpace ℝ ι) S with hν
  have hmeas : ∀ r : ℝ, MeasurableSet (Metric.closedBall (0 : EuclideanSpace ℝ ι) r)ᶜ :=
    fun r => (Metric.isClosed_closedBall.measurableSet).compl
  have hanti : Antitone fun n : ℕ => (Metric.closedBall (0 : EuclideanSpace ℝ ι) (n : ℝ))ᶜ := by
    intro a b hab
    exact Set.compl_subset_compl.mpr
      (Metric.closedBall_subset_closedBall (by exact_mod_cast hab))
  have hinter : (⋂ n : ℕ, (Metric.closedBall (0 : EuclideanSpace ℝ ι) (n : ℝ))ᶜ) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_compl_iff, mem_closedBall_zero_iff,
      Set.mem_empty_iff_false, iff_false, not_forall, not_not]
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact ⟨n, hn⟩
  have htend := MeasureTheory.tendsto_measure_iInter_atTop
    (μ := ν) (s := fun n : ℕ => (Metric.closedBall (0 : EuclideanSpace ℝ ι) (n : ℝ))ᶜ)
    (fun n => (hmeas _).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  rw [hinter, measure_empty] at htend
  have hnb : Set.Iic ε ∈ 𝓝 (0 : ℝ≥0∞) :=
    Filter.mem_of_superset (Iio_mem_nhds hε) Set.Iio_subset_Iic_self
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (htend.eventually hnb)
  refine ⟨R + N, fun M hM m hm => ?_⟩
  have hkey : (fun x : EuclideanSpace ℝ ι => m + x) ⁻¹'
      (Metric.closedBall (0 : EuclideanSpace ℝ ι) M)ᶜ
      ⊆ (Metric.closedBall (0 : EuclideanSpace ℝ ι) (N : ℝ))ᶜ := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_compl_iff, mem_closedBall_zero_iff] at hx ⊢
    intro hxN
    exact hx ((norm_add_le m x).trans (by linarith [hm, hxN]))
  calc multivariateGaussian m S (Metric.closedBall (0 : EuclideanSpace ℝ ι) M)ᶜ
      = ν ((fun x : EuclideanSpace ℝ ι => m + x) ⁻¹'
          (Metric.closedBall (0 : EuclideanSpace ℝ ι) M)ᶜ) := by
        rw [← multivariateGaussian_map_const_add S m, Measure.map_apply (by fun_prop) (hmeas M)]
    _ ≤ ν (Metric.closedBall (0 : EuclideanSpace ℝ ι) (N : ℝ))ᶜ := measure_mono hkey
    _ ≤ ε := hN N le_rfl

/-- **Finiteness of Gaussian loss averages** for polynomially growing losses:
`∫⁻ ℓ(u − z) dN(0,S)(z) < ∞`. -/
theorem gaussian_loss_convolution_lt_top
    (S : Matrix ι ι ℝ) {ℓ : EuclideanSpace ℝ ι → ℝ≥0∞} {p : ℝ}
    -- LEAN-ONLY: polynomial growth of the loss (vdV §10.3 standing assumption)
    (hpoly : ∀ h, ℓ h ≤ ENNReal.ofReal (1 + ‖h‖ ^ p))
    -- LEAN-ONLY: nonnegative exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p) (u : EuclideanSpace ℝ ι) :
    ∫⁻ z, ℓ (u - z) ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S) < ∞ := by
  classical
  set ν := multivariateGaussian (0 : EuclideanSpace ℝ ι) S with hν
  have hmono : ∫⁻ z, ℓ (u - z) ∂ν ≤ ∫⁻ z, (1 + ‖u - z‖ₑ ^ p) ∂ν := by
    refine lintegral_mono fun z => (hpoly _).trans ?_
    rw [ENNReal.ofReal_add zero_le_one (Real.rpow_nonneg (norm_nonneg _) p),
      ENNReal.ofReal_one, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp,
      ofReal_norm_eq_enorm]
  refine lt_of_le_of_lt hmono ?_
  have hfin : ∫⁻ z, ‖u - z‖ₑ ^ p ∂ν ≠ ∞ := by
    rcases eq_or_lt_of_le hp with hp0 | hppos
    · simp [← hp0, ENNReal.rpow_zero]
    · have hq0 : ENNReal.ofReal p ≠ 0 := by
        simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hppos
      have hmem : MemLp (fun z : EuclideanSpace ℝ ι => u - z) (ENNReal.ofReal p) ν := by
        have h1 : MemLp (fun _ : EuclideanSpace ℝ ι => u) (ENNReal.ofReal p) ν :=
          memLp_const u
        have h2 : MemLp (fun z : EuclideanSpace ℝ ι => z) (ENNReal.ofReal p) ν :=
          IsGaussian.memLp_id ν (ENNReal.ofReal p) ENNReal.ofReal_ne_top
        exact h1.sub h2
      have hlt := hmem.eLpNorm_lt_top
      rw [eLpNorm_eq_lintegral_rpow_enorm hq0 ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hp] at hlt
      intro hcon
      rw [hcon, ENNReal.top_rpow_of_pos (by positivity)] at hlt
      exact lt_irrefl _ hlt
  rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, lt_top_iff_ne_top.mpr hfin⟩

-- The Mahalanobis form of `S⁻¹` is the squared norm of the whitened vector `(√S)⁻¹ x`.
private lemma inner_mahalanobis_eq_norm_sq {S : Matrix ι ι ℝ} (hS : S.PosDef)
    (x : EuclideanSpace ℝ ι) :
    ⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x⟫
      = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) x‖ ^ 2 := by
  classical
  have hQPD : (CFC.sqrt S).PosDef := hS.isStrictlyPositive.sqrt.posDef
  have hQQ : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg
  have hBB : (CFC.sqrt S)⁻¹ * (CFC.sqrt S)⁻¹ = S⁻¹ := by rw [← Matrix.mul_inv_rev, hQQ]
  have hBsa : IsSelfAdjoint ((CFC.sqrt S)⁻¹) := hQPD.isHermitian.inv
  set_option backward.isDefEq.respectTransparency false in
  have hA'sa : IsSelfAdjoint (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) :=
    hBsa.map (Matrix.toEuclideanCLM (𝕜 := ℝ))
  have hswap : ∀ a b : EuclideanSpace ℝ ι,
      ⟪a, (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) b⟫
        = ⟪(Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) a, b⟫ := by
    intro a b
    have h := ContinuousLinearMap.adjoint_inner_left
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) b a
    rw [hA'sa.adjoint_eq] at h
    exact h.symm
  have hSinv : (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x
      = (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹)
          ((Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹) x) := by
    rw [← hBB, map_mul]; rfl
  rw [hSinv, hswap, real_inner_self_eq_norm_sq]

-- Integrability of `polynomial × (half-rate Gaussian density)`: the density `exp(−⟪y,S⁻¹y⟫/4)`
-- is the density of the twice-as-wide Gaussian `N(0, 2S)`, so this is
-- `gaussian_loss_convolution_lt_top` for `2 • S`.
private lemma poly_gaussian_quarter_lintegral_ne_top {S : Matrix ι ι ℝ} (hS : S.PosDef)
    {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ y : EuclideanSpace ℝ ι,
        ENNReal.ofReal (Real.exp (-⟪y, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) y⟫ / 4))
          * ENNReal.ofReal (1 + ‖y‖ ^ p) ∂volume) ≠ ∞ := by
  classical
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit
  have hS₂ : ((2 : ℝ) • S).PosDef := hS.smul (by norm_num)
  have hinv : ((2 : ℝ) • S)⁻¹ = (2⁻¹ : ℝ) • S⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdet, smul_smul]
    norm_num
  have hform : ∀ y : EuclideanSpace ℝ ι,
      Real.exp (-⟪y, (Matrix.toEuclideanCLM (𝕜 := ℝ) ((2 : ℝ) • S)⁻¹) y⟫ / 2)
        = Real.exp (-⟪y, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) y⟫ / 4) := by
    intro y
    congr 1
    rw [hinv, map_smul, ContinuousLinearMap.smul_apply, real_inner_smul_right]
    ring
  obtain ⟨c₂, hc₂pos, hc₂top, hc₂⟩ := multivariateGaussian_eq_smul_withDensity hS₂
  have hfin := gaussian_loss_convolution_lt_top ((2 : ℝ) • S)
    (ℓ := fun h : EuclideanSpace ℝ ι => ENNReal.ofReal (1 + ‖h‖ ^ p))
    (fun _ => le_rfl) hp 0
  rw [hc₂, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)] at hfin
  simp only [Pi.mul_apply, zero_sub, norm_neg, smul_eq_mul] at hfin
  simp_rw [hform] at hfin
  intro hcon
  rw [hcon, ENNReal.mul_top hc₂pos.ne'] at hfin
  simp at hfin

-- Mean-uniform Gaussian-kernel domination: for `‖u‖ ≤ B` the shifted Gaussian density
-- `exp(−⟪u−y, S⁻¹(u−y)⟫/2)` is bounded by a constant times the half-rate density
-- `exp(−⟪y,S⁻¹y⟫/4)`, uniformly in `y`.
private lemma exp_mahalanobis_shift_le {S : Matrix ι ι ℝ} (hS : S.PosDef) (B : ℝ) :
    ∃ b : ℝ, ∀ u y : EuclideanSpace ℝ ι, ‖u‖ ≤ B →
      Real.exp (-⟪u - y, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) (u - y)⟫ / 2)
        ≤ Real.exp b * Real.exp (-⟪y, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) y⟫ / 4) := by
  classical
  set A' := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)⁻¹ with hA'
  refine ⟨(‖A'‖ * B) ^ 2 / 2, fun u y hu => ?_⟩
  have hty := inner_mahalanobis_eq_norm_sq hS y
  have hTy := inner_mahalanobis_eq_norm_sq hS (u - y)
  rw [← hA'] at hty hTy
  have hsub : |‖A' u‖ - ‖A' y‖| ≤ ‖A' (u - y)‖ := by
    rw [map_sub]; exact abs_norm_sub_norm_le _ _
  have hα : ‖A' u‖ ≤ ‖A'‖ * B :=
    (A'.le_opNorm u).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg A'))
  have hα2 : ‖A' u‖ ^ 2 ≤ (‖A'‖ * B) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hα 2
  have hsq : (‖A' u‖ - ‖A' y‖) ^ 2 ≤ ‖A' (u - y)‖ ^ 2 := by
    nlinarith [sq_abs (‖A' u‖ - ‖A' y‖), abs_nonneg (‖A' u‖ - ‖A' y‖), hsub]
  rw [hty, hTy, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  nlinarith [hsq, hα2, sq_nonneg (2 * ‖A' u‖ - ‖A' y‖)]

/-- **Continuity of the Gaussian loss average** `u ↦ ∫⁻ ℓ(u − z) dN(0,S)(z)` for a measurable,
polynomially growing loss and positive definite `S`. This derives the continuity of the limit
criterion in vdV Theorem 10.8 (there taken for granted from smoothness of the normal density);
the proof is convolution-with-a-continuous-density plus dominated convergence, via
`multivariateGaussian_eq_smul_withDensity`. -/
theorem gaussian_loss_convolution_continuous
    {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness (continuity can fail for a Dirac limit measure)
    (hS : S.PosDef) {ℓ : EuclideanSpace ℝ ι → ℝ≥0∞} {p : ℝ}
    -- LEAN-ONLY: the loss is measurable (regularity)
    (hmeas : Measurable ℓ)
    -- LEAN-ONLY: polynomial growth of the loss (vdV §10.3 standing assumption)
    (hpoly : ∀ h, ℓ h ≤ ENNReal.ofReal (1 + ‖h‖ ^ p))
    -- LEAN-ONLY: nonnegative exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p) :
    Continuous fun u : EuclideanSpace ℝ ι =>
      ∫⁻ z, ℓ (u - z) ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S) := by
  classical
  obtain ⟨c, hcpos, hctop, hc⟩ := multivariateGaussian_eq_smul_withDensity hS
  set q : EuclideanSpace ℝ ι → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (-⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x⟫ / 2)) with hqdef
  have hqmeas : Measurable q := by rw [hqdef]; fun_prop
  have hqcont : Continuous q := by
    have hinner : Continuous fun x : EuclideanSpace ℝ ι =>
        ⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x⟫ :=
      continuous_id.inner (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹).continuous
    rw [hqdef]
    exact ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp (hinner.neg.div_const 2))
  have hltop : ∀ y : EuclideanSpace ℝ ι, ℓ y ≠ ∞ := fun y =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hpoly y)
  -- Step 1: move the `u`-dependence from the loss onto the (continuous) Gaussian density,
  -- by writing the measure through its density and substituting `y := u − z`.
  have hrw : ∀ u : EuclideanSpace ℝ ι,
      (∫⁻ z, ℓ (u - z) ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S))
        = c * ∫⁻ y, q (u - y) * ℓ y ∂volume := by
    intro u
    have hcs : Measurable fun z : EuclideanSpace ℝ ι => u - z := measurable_const_sub u
    rw [hc, lintegral_smul_measure,
      lintegral_withDensity_eq_lintegral_mul _ hqmeas
        (g := fun z : EuclideanSpace ℝ ι => ℓ (u - z)) (hmeas.comp hcs), smul_eq_mul]
    congr 1
    have hmp : MeasurePreserving (fun t : EuclideanSpace ℝ ι => u - t)
        (volume : Measure (EuclideanSpace ℝ ι)) volume :=
      Measure.measurePreserving_sub_left volume u
    have hstep := hmp.lintegral_comp (f := fun z : EuclideanSpace ℝ ι => q z * ℓ (u - z))
      (hqmeas.mul (hmeas.comp hcs))
    simpa [Pi.mul_apply, sub_sub_cancel] using hstep.symm
  have hfun : (fun u : EuclideanSpace ℝ ι =>
      ∫⁻ z, ℓ (u - z) ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S))
      = fun u : EuclideanSpace ℝ ι => c * ∫⁻ y, q (u - y) * ℓ y ∂volume := funext hrw
  rw [hfun]
  refine Continuous.comp' (ENNReal.continuous_const_mul hctop) ?_
  -- Step 2: dominated convergence along `𝓝 u₀`, with a Gaussian-tail envelope valid on a
  -- fixed ball around `u₀`.
  rw [continuous_iff_continuousAt]
  intro u₀
  obtain ⟨b, hbdom⟩ := exp_mahalanobis_shift_le hS (‖u₀‖ + 1)
  have hbnd : Measurable fun y : EuclideanSpace ℝ ι =>
      ENNReal.ofReal (Real.exp (-⟪y, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) y⟫ / 4))
        * ENNReal.ofReal (1 + ‖y‖ ^ p) := by fun_prop
  have key : Tendsto (fun u : EuclideanSpace ℝ ι => ∫⁻ y, q (u - y) * ℓ y ∂volume)
      (𝓝 u₀) (𝓝 (∫⁻ y, q (u₀ - y) * ℓ y ∂volume)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence
      (fun y => ENNReal.ofReal (Real.exp b) *
        (ENNReal.ofReal (Real.exp (-⟪y, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) y⟫ / 4))
          * ENNReal.ofReal (1 + ‖y‖ ^ p))) ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun u =>
        (hqmeas.comp (measurable_const_sub u)).mul hmeas
    · filter_upwards [Metric.ball_mem_nhds u₀ one_pos] with u hu
      have hunorm : ‖u‖ ≤ ‖u₀‖ + 1 := by
        have hd : ‖u - u₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hu
        have hsplit : u₀ + (u - u₀) = u := by abel
        calc ‖u‖ = ‖u₀ + (u - u₀)‖ := by rw [hsplit]
          _ ≤ ‖u₀‖ + ‖u - u₀‖ := norm_add_le _ _
          _ ≤ ‖u₀‖ + 1 := by linarith
      refine Filter.Eventually.of_forall fun y => ?_
      have h1 : q (u - y) ≤ ENNReal.ofReal (Real.exp b)
          * ENNReal.ofReal (Real.exp (-⟪y, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) y⟫ / 4)) := by
        simp only [hqdef]
        rw [← ENNReal.ofReal_mul (Real.exp_pos b).le]
        exact ENNReal.ofReal_le_ofReal (hbdom u y hunorm)
      calc q (u - y) * ℓ y
          ≤ (ENNReal.ofReal (Real.exp b)
              * ENNReal.ofReal (Real.exp (-⟪y, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) y⟫ / 4)))
              * ENNReal.ofReal (1 + ‖y‖ ^ p) := mul_le_mul' h1 (hpoly y)
        _ = _ := by rw [mul_assoc]
    · rw [lintegral_const_mul _ hbnd]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (poly_gaussian_quarter_lintegral_ne_top hS hp)
    · refine Filter.Eventually.of_forall fun y => ?_
      have hc1 : Continuous fun u : EuclideanSpace ℝ ι => q (u - y) :=
        hqcont.comp (continuous_id.sub continuous_const)
      exact ((ENNReal.continuous_mul_const (hltop y)).comp' hc1).tendsto u₀
  exact key

end AsymptoticStatistics

