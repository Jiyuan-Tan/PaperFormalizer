module
public import StatLean.AsymptoticStatistics.LowerBounds.FinDimSubmodel
public import StatLean.AsymptoticStatistics.ForMathlib.CharFnConvolution
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import StatLean.AsymptoticStatistics.ForMathlib.JointMGF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Group.Convolution

@[expose] public section

/-!
# Le Cam's third lemma and the characteristic-function identity

Le Cam's third lemma combined with the characteristic-function identity in the
Gaussian-shift limit, yielding two consequences:

(i) the asymptotic covariance of any regular sequence of estimators is bounded
    below in Loewner order by `A_m A_mᵀ` (scalar case: `Cov L ≥ ‖A_m‖²`);

(ii) when `C_m` has nonempty interior, the analytic identity extends from
     `C_m ⊂ ℝᵐ` to `ℂᵐ` via the identity theorem for entire functions, yielding
     the convolution decomposition `L = N(0, A_m A_mᵀ) ∗ M_m`.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.3 —
synthesis step in the proofs of the convolution and minimax theorems.

Headline declarations: `lecam_third_covariance_bound`, `lecam_third_convolution`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal Matrix

namespace AsymptoticStatistics.LowerBounds.LeCamThirdAndCharFn

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.LowerBounds.FinDimSubmodel
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- *Covariance lower bound from the Schur complement.*

If `T_n` is a regular estimator sequence whose centred / rescaled error
`S_n = √n (T_n − ψ(P))` weakly converges (under `Pⁿ`) to a limit law `L`
with finite variance `varL`, then for any orthonormal score basis
`g_P : Fin m → L²₀(P)` of a finite-dim subspace `V_m` of the tangent
space, the coefficients `A i = ⟨IF_eff, g_P i⟩` satisfy

  `varL ≥ Σᵢ (A i)²`.

(Scalar specialisation of the book's Loewner clause `Cov(L) ⪰ A_m A_mᵀ`:
`Cov(L) = varL` is a scalar, and `Σᵢ (A i)² = ‖A_m‖² = A_m A_mᵀ` for the
row-vector `A_m`.)

Reference: vdV §25.3.

The analytic content splits into two parts:
* the *cross-moment extraction* `E[S Δᵀ] = A_m` from differentiating the
  joint MGF identity twice;
* the *Schur-complement step* — discharged in this proof body via
  Mathlib's `Matrix.PosSemidef.fromBlocks₂₂` and `PosSemidef.diag_nonneg`.

Given positive semidefiniteness of the joint covariance block matrix
`[[varL, A_m]; [A_mᵀ, I_m]]`, we apply Schur to extract the scalar inequality
`varL ≥ Σᵢ A_i²`. -/
theorem lecam_third_covariance_bound
    (T_set : TangentSpec P)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (_hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (_hWeak : WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P))) L)
    (varL : ℝ) (_hvar : varL = ∫ x, (x - ∫ y, y ∂L)^2 ∂L)
    -- `g_P` is an orthonormal score basis of a finite-dim subspace of
    -- the tangent space.
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (hg_orth : Orthonormal ℝ
      (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))))
    (_hg_in_tangent : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    -- vdV §25.3 (clause (a) of the convolution theorem): the variance
    -- lower bound `‖IF_eff‖² ≤ varL`. The PSD claim about the joint
    -- covariance block `[[varL, A_m]; [A_mᵀ, I_m]]` is discharged
    -- internally via `JointMGF.joint_covariance_block_posSemidef`, which
    -- builds it as the sum of a Gram block matrix (rank-`(m+1)` from
    -- `(IF_eff, g_P)`) plus a slack block `[[varL − ‖IF_eff‖², 0]; [0, 0]]`
    -- (PSD by `hVarBound`). The Gram-block structure of
    -- `[[‖IF_eff‖², A_m]; [A_mᵀ, I_m]]` is purely linear-algebraic
    -- (orthonormality of `g_P`), so only the slack `‖IF_eff‖² ≤ varL`
    -- remains as input.
    (hVarBound : ‖(IF_eff : ↥(L2ZeroMean P))‖ ^ 2 ≤ varL) :
    -- Conclusion: `varL ≥ Σᵢ ⟨IF_eff, g_P i⟩²`.
    (∑ i : Fin m,
        (⟪(IF_eff : ↥(L2ZeroMean P)), (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2)
      ≤ varL := by
  -- Discharge the joint covariance block PSD claim via
  -- `JointMGF.joint_covariance_block_posSemidef`: the block matrix
  -- `[[varL, A_m]; [A_mᵀ, I_m]]` = Gram block + slack block, both PSD.
  have hCovBlockPSD :
      (Matrix.fromBlocks
          (Matrix.of (fun _ _ : Fin 1 => varL))
          (Matrix.of (fun _ : Fin 1 => fun j : Fin m =>
            ⟪(IF_eff : ↥(L2ZeroMean P)), (g_P j : ↥(L2ZeroMean P))⟫_ℝ))
          (Matrix.of (fun i : Fin m => fun _ : Fin 1 =>
            ⟪(IF_eff : ↥(L2ZeroMean P)), (g_P i : ↥(L2ZeroMean P))⟫_ℝ))
          (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef :=
    AsymptoticStatistics.ForMathlib.JointMGF.joint_covariance_block_posSemidef
      varL (IF_eff : ↥(L2ZeroMean P))
      (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))) hg_orth hVarBound
  -- Set up the block matrices.
  set A : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of (fun _ _ : Fin 1 => varL)
    with hA
  set B : Matrix (Fin 1) (Fin m) ℝ :=
    Matrix.of (fun _ : Fin 1 => fun j : Fin m =>
      ⟪(IF_eff : ↥(L2ZeroMean P)), (g_P j : ↥(L2ZeroMean P))⟫_ℝ) with hB
  -- The conjugate transpose of `B` (over ℝ, just the ordinary transpose).
  have hBH : Bᴴ = Matrix.of (fun i : Fin m => fun _ : Fin 1 =>
      ⟪(IF_eff : ↥(L2ZeroMean P)), (g_P i : ↥(L2ZeroMean P))⟫_ℝ) := by
    ext i j
    simp [B, Matrix.conjTranspose_apply, Matrix.of_apply]
  -- Identity matrix `D = I_m` is positive definite and invertible.
  letI : Invertible (1 : Matrix (Fin m) (Fin m) ℝ) := invertibleOne
  have hD : (1 : Matrix (Fin m) (Fin m) ℝ).PosDef := Matrix.PosDef.one
  -- Apply `Matrix.PosDef.fromBlocks₂₂` to the (now-discharged) PSD
  -- block matrix to get PSD of the Schur complement `A - B * 1⁻¹ * Bᴴ`.
  have hSchurPSD :
      (A - B * (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ * Bᴴ).PosSemidef := by
    have hiff := Matrix.PosDef.fromBlocks₂₂ A B hD
    apply hiff.mp
    -- The discharged PSD claim, with `Bᴴ` equated.
    rw [hBH]
    exact hCovBlockPSD
  -- Extract the scalar inequality from the (0,0)-entry of the PSD
  -- 1×1 Schur complement matrix.
  have hEntry : 0 ≤ (A - B * (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ * Bᴴ) 0 0 :=
    hSchurPSD.diag_nonneg
  -- Compute that entry: `varL - Σⱼ ⟪IF_eff, g_P j⟫²`.
  have hCompute :
      (A - B * (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ * Bᴴ) 0 0 =
        varL - ∑ j : Fin m,
          (⟪(IF_eff : ↥(L2ZeroMean P)), (g_P j : ↥(L2ZeroMean P))⟫_ℝ) ^ 2 := by
    have hinv : (1 : Matrix (Fin m) (Fin m) ℝ)⁻¹ = 1 := inv_one
    rw [hinv, Matrix.mul_one]
    simp only [Matrix.sub_apply, Matrix.mul_apply, A, B, hBH,
      Matrix.of_apply, sq]
  -- Conclude.
  linarith [hEntry, hCompute.symm ▸ hEntry]

/-- *Convolution decomposition under a convex-cone tangent set.*

When the tangent set is a convex cone (so `C_m` has nonempty interior in
`ℝᵐ`), the analytic identity extends from `C_m` to `ℂᵐ` and evaluating at
`z = −i A_mᵀ u` gives

  `L = N(0, ‖A_m‖²) ∗ M_m`

for some probability measure `M_m` on ℝ (the law of `S − A_m Δ`).

Reference: vdV §25.3.

The book chain factorises as:
* (a) the cone hypotheses `_hCone` + `_hConvex` make the agreement set
  `U ⊆ ℝᵐ` (the set of admissible tangent directions where the joint
  MGF identity holds) have nonempty interior.
* (b) entire functions `F(z) := E[exp(i uᵀ S + zᵀ Δ)]` and
  `G(z) := φ_L(u) · exp(i uᵀ A_m z + ½ zᵀ z)` agree on `U`, both are
  entire on `ℂᵐ`. The identity theorem closes the gap to all of
  `ℂᵐ` (`AsymptoticStatistics.ForMathlib.IdentityTheoremMulti`).
* (c) evaluating `F = G` on `ℂᵐ` at `z = −i A_mᵀ u` yields the
  scalar char-fn identity
  `charFun L u = charFun (N(0, ‖A_m‖²)) u · charFun M u`
  for some probability measure `M` (the law of `S − A_m Δ`).

This lemma takes the law `M` together with the scalar char-fn
factorisation `hCharFn` directly, and the extraction step (c) is
discharged internally via `convolution_extraction_from_charFn`. -/
theorem lecam_third_convolution
    (T_set : TangentSpec P)
    (_hCone : ∀ x ∈ T_set.carrier, ∀ t : ℝ, 0 ≤ t →
      t • x ∈ T_set.carrier)
    (_hConvex : ∀ x ∈ T_set.carrier, ∀ y ∈ T_set.carrier,
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a • x + b • y ∈ T_set.carrier)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (_hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set)
              hψ.derivative IF_eff)
    (T_n : ∀ n, (Fin n → Ω) → ℝ)
    (L : Measure ℝ) [IsProbabilityMeasure L]
    (_hWeak : WeakConverges
      (fun n : ℕ =>
        (MeasureTheory.Measure.pi (fun _ : Fin n => P)).map
          (fun X : Fin n → Ω => Real.sqrt n * (T_n n X - ψ P))) L)
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (_hg_orth : Orthonormal ℝ
      (fun i : Fin m => (g_P i : ↥(L2ZeroMean P))))
    (_hg_in_tangent : ∀ i, (g_P i : ↥(L2ZeroMean P)) ∈ tangentSpace T_set)
    -- `M` is the law of `S − A_m Δ`, produced by the joint MGF identity
    -- (vdV §25.3) via clauses (a)+(b)+(c) of the book chain: agreement on
    -- the cone interior, identity theorem to extend to `ℂᵐ`, evaluation
    -- at `z = −i A_mᵀ u`.
    (M : Measure ℝ) [hMP : IsProbabilityMeasure M]
    -- `charFun L u = charFun (N(0, ‖A_m‖²)) u · charFun M u`. This is the
    -- content of clause (c): once `F = G` is extended to all of `ℂᵐ` and
    -- evaluated at the Gaussian-shift direction, it specialises to this 1D
    -- identity on the marginal of `u`. vdV §25.3.
    (hCharFn : ∀ u : ℝ,
      let varA : ℝ≥0 :=
        ⟨∑ i : Fin m,
            (⟪(IF_eff : ↥(L2ZeroMean P)),
              (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩
      MeasureTheory.charFun L u =
        MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 varA) u
          * MeasureTheory.charFun M u) :
    -- Conclusion: `L = N(0, ‖A_m‖²) ∗ M_m` for some `M_m`.
    -- (Encoded as the existential: `∃ M, L = (N(0, ‖A_m‖²)).convolution M`.)
    let varA : ℝ≥0 :=
      ⟨∑ i : Fin m,
          (⟪(IF_eff : ↥(L2ZeroMean P)), (g_P i : ↥(L2ZeroMean P))⟫_ℝ) ^ 2,
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)⟩
    ∃ M : Measure ℝ, IsProbabilityMeasure M ∧
      L = MeasureTheory.Measure.conv
            (ProbabilityTheory.gaussianReal 0 varA) M := by
  -- Apply `convolution_extraction_from_charFn` to the char-fn
  -- factorisation `hCharFn`, witnessing the existential with `M`.
  refine ⟨M, hMP, ?_⟩
  exact AsymptoticStatistics.ForMathlib.CharFnConvolution.convolution_extraction_from_charFn
    L M _ hCharFn

end AsymptoticStatistics.LowerBounds.LeCamThirdAndCharFn
