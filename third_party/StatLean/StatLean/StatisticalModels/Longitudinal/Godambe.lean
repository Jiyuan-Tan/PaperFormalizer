module
public import StatLean.StatisticalModels.Longitudinal.Sandwich
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.Matrix.ColumnRowPartitioned

@[expose] public section

/-!
# Godambe optimality — the true covariance is the optimal working covariance

**L3.** Among GEE working covariances, choosing `V = Σ` (the truth) minimizes the exact
sandwich covariance in the Loewner order:
$$B^{-1} M B^{-1} \succeq K^{-1}, \qquad K = \sum_i D_i^\top \Sigma_i^{-1} D_i,$$
with equality at `V = Σ`. Stated as a pure matrix theorem (the probabilistic content — that
`B⁻¹MB⁻¹` and `K⁻¹` are the two candidate estimator covariances — is
`Sandwich.covMatrix_geeEstimator`); the cross-term cancellation `E[U U^{*\top}] = B` that
powers the classical proof appears here as the algebraic identity
`∑ Dᵀ V⁻¹ Σ Σ⁻¹ D = B` inside the stacked-covariance PSD argument.

**Reference.** V. P. Godambe, "An optimum property of regular maximum likelihood
estimation," *Ann. Math. Statist.* **31** (1960), 1208–1211 (`God60`); V. P. Godambe and
C. C. Heyde, "Quasi-likelihood and optimal estimation," *Int. Statist. Rev.* **55** (1987),
231–244 (verify §); `LZ86` (remark after Theorem 2); GMM lineage: L. P. Hansen,
*Econometrica* **50** (1982).

**Proof formalization notes.** Route: the block matrix
`fromBlocks M B Bᵀ K` is PSD (it is the covariance of the stacked scores `(U, U*)` — proved
matricially: it equals `∑ᵢ Wᵢ Σᵢ Wᵢᵀ`-type conjugations with
`Wᵢ = [Dᵢᵀ Vᵢ⁻¹; Dᵢᵀ Σᵢ⁻¹]`-stacked, each PSD by
`Matrix.PosSemidef.mul_mul_conjTranspose_same` and PSD sums); then the Schur-complement
characterization `Matrix.PosSemidef.fromBlocks₁₁`-family (with `K` PosDef) yields
`M − B K⁻¹ Bᵀ ⪰ 0`; congruence by `B⁻¹` (PSD is congruence-stable — again
`mul_mul_conjTranspose_same`) gives the claim, **deliberately avoiding matrix
inverse-monotonicity** (absent from Mathlib). Relation to the Gauss–Markov theorem
(`PointEstimation.LinearModel.GaussMarkov.gauss_markov`, the scalar subspace form of the
same Loewner argument): noted here, no import.

**Bibliographic comments.** Godambe (1960) proved the score is the optimal estimating
function; the working-covariance corollary for GEE is Liang–Zeger's remark; the
finite-sample matrix form here is the standard textbook argument made exact.
-/

open Matrix

namespace StatLean.StatisticalModels.Longitudinal

variable {N m q : ℕ}

/-- The **Godambe information** `K = ∑ Dᵢᵀ Σᵢ⁻¹ Dᵢ` — the bread at the true covariance
(`God60`). -/
noncomputable def godambeInfo (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (Covs : Fin N → Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  ∑ i, (D i)ᵀ * (Covs i)⁻¹ * D i

section Helpers

set_option linter.unusedSectionVars false

/-- LEAN-ONLY: a finite sum of block matrices is the block matrix of the sums. -/
private theorem sum_fromBlocks {ι l m₁ n₁ o : Type*} (s : Finset ι)
    (A : ι → Matrix n₁ l ℝ) (B : ι → Matrix n₁ m₁ ℝ) (C : ι → Matrix o l ℝ)
    (E : ι → Matrix o m₁ ℝ) :
    ∑ i ∈ s, Matrix.fromBlocks (A i) (B i) (C i) (E i)
      = Matrix.fromBlocks (∑ i ∈ s, A i) (∑ i ∈ s, B i) (∑ i ∈ s, C i) (∑ i ∈ s, E i) := by
  ext (i | i) (j | j) <;> simp [Matrix.sum_apply]

/-- LEAN-ONLY: the bread is symmetric when the working covariances are. -/
private theorem geeBread_transpose' (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V : Fin N → Matrix (Fin m) (Fin m) ℝ) (hVsymm : ∀ i, (V i)ᵀ = V i) :
    (geeBread D V)ᵀ = geeBread D V := by
  simp only [geeBread, Matrix.transpose_sum, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, hVsymm]
  exact Finset.sum_congr rfl fun i _ => by rw [← Matrix.mul_assoc]

end Helpers

/-- The stacked-score covariance block matrix is PSD — the matricial form of
"`Cov (U, U*)` is a covariance" with the cross-block `B` (the Godambe cancellation). -/
theorem posSemidef_fromBlocks_meat_bread (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V Covs : Fin N → Matrix (Fin m) (Fin m) ℝ)
    -- USER-INPUT: true covariances positive definite; God60
    (hCov : ∀ i, (Covs i).PosDef)
    -- USER-INPUT: symmetric working covariances; LZ86 §2
    (hVsymm : ∀ i, (V i)ᵀ = V i) :
    (Matrix.fromBlocks (geeMeat D V Covs) (geeBread D V)
      (geeBread D V)ᵀ (godambeInfo D Covs)).PosSemidef := by
  have hCovT : ∀ i, (Covs i)ᵀ = Covs i := fun i => by
    have h := (hCov i).1.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hCovU : ∀ i, IsUnit (Covs i).det := fun i =>
    isUnit_iff_ne_zero.mpr (hCov i).det_pos.ne'
  -- the stacked weight matrix `Wᵢ = [Dᵢᵀ Vᵢ⁻¹ ; Dᵢᵀ Σᵢ⁻¹]`
  let W : Fin N → Matrix (Fin q ⊕ Fin q) (Fin m) ℝ := fun i =>
    Matrix.fromRows ((D i)ᵀ * (V i)⁻¹) ((D i)ᵀ * (Covs i)⁻¹)
  have hblock : ∀ i, W i * Covs i * (W i)ᵀ
      = Matrix.fromBlocks ((D i)ᵀ * (V i)⁻¹ * Covs i * (V i)⁻¹ * D i)
          ((D i)ᵀ * (V i)⁻¹ * D i) ((D i)ᵀ * (V i)⁻¹ * D i)
          ((D i)ᵀ * (Covs i)⁻¹ * D i) := by
    intro i
    have h1 : ((D i)ᵀ * (V i)⁻¹)ᵀ = (V i)⁻¹ * D i := by
      rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hVsymm, Matrix.transpose_transpose]
    have h2 : ((D i)ᵀ * (Covs i)⁻¹)ᵀ = (Covs i)⁻¹ * D i := by
      rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hCovT, Matrix.transpose_transpose]
    change Matrix.fromRows ((D i)ᵀ * (V i)⁻¹) ((D i)ᵀ * (Covs i)⁻¹) * Covs i
        * (Matrix.fromRows ((D i)ᵀ * (V i)⁻¹) ((D i)ᵀ * (Covs i)⁻¹))ᵀ = _
    rw [Matrix.fromRows_mul, Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols, h1, h2]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hCovU i),
      Matrix.nonsing_inv_mul_cancel_left _ _ (hCovU i)]
  have key : ∑ i, W i * Covs i * (W i)ᵀ
      = Matrix.fromBlocks (geeMeat D V Covs) (geeBread D V) (geeBread D V)ᵀ
          (godambeInfo D Covs) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hblock i, sum_fromBlocks,
      geeBread_transpose' D V hVsymm]
    rfl
  rw [← key]
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb) Matrix.PosSemidef.zero ?_
  intro i _
  have h := (hCov i).posSemidef.mul_mul_conjTranspose_same (W i)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- **L3, Godambe optimality** (`God60`; `LZ86` remark after Thm 2): the exact sandwich
dominates the inverse Godambe information in the Loewner order — no working covariance
beats the truth. -/
theorem godambe_optimality (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (V Covs : Fin N → Matrix (Fin m) (Fin m) ℝ)
    -- USER-INPUT: true covariances positive definite; God60
    (hCov : ∀ i, (Covs i).PosDef)
    -- USER-INPUT: symmetric working covariances; LZ86 §2
    (hVsymm : ∀ i, (V i)ᵀ = V i)
    -- USER-INPUT: identified designs — Godambe information and bread invertible; God60
    (hK : (godambeInfo D Covs).PosDef) (hB : IsUnit (geeBread D V).det) :
    ((geeBread D V)⁻¹ * geeMeat D V Covs * (geeBread D V)⁻¹
      - (godambeInfo D Covs)⁻¹).PosSemidef := by
  haveI : Invertible (godambeInfo D Covs) :=
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hK.det_pos.ne')
  have hBt : (geeBread D V)ᵀ = geeBread D V := geeBread_transpose' D V hVsymm
  have hBinvT : ((geeBread D V)⁻¹)ᵀ = (geeBread D V)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hBt]
  have hpsd := posSemidef_fromBlocks_meat_bread D V Covs hCov hVsymm
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial] at hpsd
  have hschur := (Matrix.PosDef.fromBlocks₂₂ (geeMeat D V Covs) (geeBread D V) hK).mp hpsd
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hBt] at hschur
  have hcong := hschur.mul_mul_conjTranspose_same ((geeBread D V)⁻¹)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hBinvT] at hcong
  have hexp : (geeBread D V)⁻¹ * (geeMeat D V Covs
        - geeBread D V * (godambeInfo D Covs)⁻¹ * geeBread D V) * (geeBread D V)⁻¹
      = (geeBread D V)⁻¹ * geeMeat D V Covs * (geeBread D V)⁻¹
        - (godambeInfo D Covs)⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one,
      Matrix.nonsing_inv_mul_cancel_left _ _ hB]
  rw [← hexp]
  exact hcong

/-- **Equality at the truth**: with `V = Σ` the sandwich collapses to `K⁻¹`. -/
theorem sandwich_eq_inv_godambeInfo_of_true (D : Fin N → Matrix (Fin m) (Fin q) ℝ)
    (Covs : Fin N → Matrix (Fin m) (Fin m) ℝ)
    -- USER-INPUT: identified design at the truth; God60
    (hK : IsUnit (godambeInfo D Covs).det)
    -- USER-INPUT: symmetric true covariances; LZ86 §2
    (hCovsymm : ∀ i, (Covs i)ᵀ = Covs i) :
    (geeBread D Covs)⁻¹ * geeMeat D Covs Covs * (geeBread D Covs)⁻¹
      = (godambeInfo D Covs)⁻¹ := by
  have hbread : geeBread D Covs = godambeInfo D Covs := rfl
  have hmeat : geeMeat D Covs Covs = godambeInfo D Covs := by
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : IsUnit (Covs i).det
    · simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ h]
    · rw [Matrix.nonsing_inv_apply_not_isUnit _ h]
      simp
  rw [hbread, hmeat, Matrix.nonsing_inv_mul _ hK, Matrix.one_mul]

end StatLean.StatisticalModels.Longitudinal
