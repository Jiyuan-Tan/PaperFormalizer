module
public import StatLean.HighDimensionalStatistics.ForMathlib.SupportSubmatrix
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# Gram matrix `XₛᵀXₛ`, its inverse, and the projection `Π_{S⊥}` (ForMathlib)

Theorem-agnostic matrix analysis for Lasso support recovery (Wainwright §7.5):
the support Gram matrix `XₛᵀXₛ`, its inverse `(XₛᵀXₛ)⁻¹`, and the orthogonal
projection `Π_{S⊥}(X) = Iₙ − Xₛ(XₛᵀXₛ)⁻¹Xₛᵀ`.

Book-agnostic: positive-definiteness/invertibility and the operator bounds take the
**quadratic-form coercivity** `cmin·‖v‖² ≤ (1/n)·‖Xₛ v‖²` as a *plain hypothesis*
(this is condition (A3) unfolded; the concept-layer `LowerEigenvalue` supplies it, but
naming it here would invert the `ForMathlib → concept` dependency). All inputs are
hypothesis-free identities or this coercivity adapter; tagged `-- LEAN-ONLY` accordingly.

Mathlib bricks: `Matrix.PosDef`, `Matrix.PosDef.isUnit_det` / `Matrix.nonsing_inv`,
min-eigenvalue quadratic-form bound. The matrix ℓ∞ operator norm is given locally as
`matLinftyNorm A = ⨆ i, ∑ j |A i j|` (max absolute row sum = Mathlib `Matrix.linfty_opNorm`).
-/

open Matrix
open scoped InnerProductSpace

namespace StatLean.HighDimensionalStatistics

variable {n d : ℕ}

/-- **Support Gram matrix** `G_S = XₛᵀXₛ : Matrix ↥S ↥S ℝ`. -/
def gram (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    Matrix {x // x ∈ S} {x // x ∈ S} ℝ :=
  (Xsub X S)ᵀ * (Xsub X S)

/-- **Inverse support Gram** `(XₛᵀXₛ)⁻¹`. Equal to the genuine two-sided inverse once
the Gram is invertible (`gram_isUnit_det`), and to the junk `0` otherwise (Mathlib
`Matrix.inv` convention). -/
noncomputable def gramInv (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    Matrix {x // x ∈ S} {x // x ∈ S} ℝ :=
  (gram X S)⁻¹

/-- **Orthogonal projection** onto the complement of `colspan(Xₛ)`:
`Π_{S⊥}(X) = Iₙ − Xₛ (XₛᵀXₛ)⁻¹ Xₛᵀ`. -/
noncomputable def projPerp (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    Matrix (Fin n) (Fin n) ℝ :=
  1 - (Xsub X S) * (gramInv X S) * (Xsub X S)ᵀ

/-- **Matrix ℓ∞ operator norm** `|||A|||_∞ = max_i ∑_j |A i j|` (max absolute row sum);
the matrix norm appearing in Wainwright's bound (7.45). Equals Mathlib's
`Matrix.linfty_opNorm`. For an empty row index it is `0`. -/
noncomputable def matLinftyNorm {p q : Type*} [Fintype q]
    (A : Matrix p q ℝ) : ℝ :=
  ⨆ i, ∑ j, |A i j|

/-- Gram quadratic form: `vᵀ G_S v = ‖Xₛ v‖²`. -/
lemma gram_quadForm (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    (v : EuclideanSpace ℝ {x // x ∈ S}) :
    (gram X S).mulVec v.ofLp ⬝ᵥ v.ofLp = ‖designSub X S v‖ ^ 2 := by
  rw [normSq_designSub, gram, ← Matrix.mulVec_mulVec]
  rfl

/-- The Gram matrix is symmetric (Hermitian over ℝ). -/
lemma gram_isHermitian (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d)) :
    (gram X S).IsHermitian := by
  have h := Matrix.isHermitian_conjTranspose_mul_self (Xsub X S)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- **(A3) ⇒ positive definiteness.** The quadratic-form coercivity makes `G_S` PosDef. -/
lemma gram_posDef_of_coercive (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ}
    -- LEAN-ONLY: 0 < n (needed to clear the 1/n in the Rayleigh quotient)
    (hn : 0 < n)
    -- LEAN-ONLY: 0 < cmin; Wainwright §7.5 (A3, 7.43a)
    (hcmin : 0 < cmin)
    -- LEAN-ONLY: quadratic-form coercivity = (A3) unfolded; supplied by `LowerEigenvalue`
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2) :
    (gram X S).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (gram_isHermitian X S) (fun x hx => ?_)
  have hstar : (star x : {y // y ∈ S} → ℝ) = x := by funext i; exact star_trivial (x i)
  rw [hstar, dotProduct_comm]
  set v : EuclideanSpace ℝ {x // x ∈ S} := WithLp.toLp 2 x with hv
  have hvofLp : v.ofLp = x := WithLp.ofLp_toLp 2 x
  rw [← hvofLp, gram_quadForm]
  have hvne : v ≠ 0 := by
    intro h
    apply hx
    rw [← hvofLp, h]; rfl
  have hnormpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  have h1 := hcoer v
  have hsq : 0 ≤ ‖designSub X S v‖ ^ 2 := by positivity
  rcases hsq.eq_or_lt with h | h
  · exfalso
    rw [← h, mul_zero] at h1
    nlinarith [mul_pos hcmin (pow_pos hnormpos 2)]
  · exact h

/-- **(A3) ⇒ invertibility.** The Gram determinant is a unit, so `gramInv` is the genuine
two-sided inverse. -/
lemma gram_isUnit_det (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2) :
    IsUnit (gram X S).det :=
  isUnit_iff_ne_zero.mpr
    (Matrix.PosDef.det_pos (gram_posDef_of_coercive X S hn hcmin hcoer)).ne'

/-- `gramInv` is a left inverse of `gram` (on vectors), under (A3). -/
lemma gramInv_mulVec_gram (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2)
    (u : {x // x ∈ S} → ℝ) :
    (gramInv X S).mulVec ((gram X S).mulVec u) = u := by
  rw [gramInv, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (gram_isUnit_det X S hn hcmin hcoer), Matrix.one_mulVec]

/-- `gramInv` is symmetric (inverse of a Hermitian matrix is Hermitian). -/
lemma gramInv_isHermitian (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2) :
    (gramInv X S).IsHermitian := by
  rw [gramInv]
  exact (gram_isHermitian X S).inv

/-- **Operator-ℓ² bound on the inverse Gram** from the min-eigenvalue (A3):
`‖(XₛᵀXₛ)⁻¹ u‖ ≤ (1/(cmin·n))·‖u‖`. (Equivalently `‖(XₛᵀXₛ/n)⁻¹‖₂ ≤ 1/cmin`.) -/
lemma norm_gramInv_mulVec_le (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2)
    (u : EuclideanSpace ℝ {x // x ∈ S}) :
    ‖(WithLp.toLp 2 ((gramInv X S).mulVec u.ofLp) : EuclideanSpace ℝ {x // x ∈ S})‖
      ≤ (1 / (cmin * n)) * ‖u‖ := by
  set w : {x // x ∈ S} → ℝ := (gramInv X S).mulVec u.ofLp with hw
  set tw : EuclideanSpace ℝ {x // x ∈ S} := WithLp.toLp 2 w with htw
  have htwofLp : tw.ofLp = w := WithLp.ofLp_toLp 2 w
  have hrinv : (gram X S).mulVec w = u.ofLp := by
    rw [hw, Matrix.mulVec_mulVec, gramInv,
      Matrix.mul_nonsing_inv _ (gram_isUnit_det X S hn hcmin hcoer), Matrix.one_mulVec]
  have hinner : ⟪u, tw⟫_ℝ = u.ofLp ⬝ᵥ w := by
    simp only [PiLp.inner_apply]
    change tw.ofLp ⬝ᵥ u.ofLp = u.ofLp ⬝ᵥ w
    rw [htwofLp, dotProduct_comm]
  have hqf : u.ofLp ⬝ᵥ w = ‖designSub X S tw‖ ^ 2 := by
    rw [← hrinv, ← htwofLp]
    exact gram_quadForm X S tw
  have hDeq : ⟪u, tw⟫_ℝ = ‖designSub X S tw‖ ^ 2 := hinner.trans hqf
  have hNpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hcn : (0 : ℝ) < cmin * n := mul_pos hcmin hNpos
  have hco' : cmin * (n : ℝ) * ‖tw‖ ^ 2 ≤ ‖designSub X S tw‖ ^ 2 := by
    have h := hcoer tw
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hNpos] at h
    nlinarith [h]
  have hcs : ⟪u, tw⟫_ℝ ≤ ‖u‖ * ‖tw‖ := real_inner_le_norm u tw
  rw [hDeq] at hcs
  rcases (norm_nonneg tw).eq_or_lt with htw0 | htwpos
  · rw [← htw0]
    exact mul_nonneg (le_of_lt (div_pos one_pos hcn)) (norm_nonneg u)
  · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hcn]
    nlinarith [hco', hcs, htwpos, mul_pos htwpos htwpos]

/-- Adjoint identity for `dotProduct`: `(P v) ⬝ v' = v ⬝ (Pᵀ v')`. -/
private lemma dotProduct_mulVec_left {m : Type*} [Fintype m] (P : Matrix m m ℝ) (x y : m → ℝ) :
    P.mulVec x ⬝ᵥ y = x ⬝ᵥ Pᵀ.mulVec y := by
  rw [dotProduct_comm, dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]

/-- `projPerp` is symmetric (`Pᵀ = P`), since `gramInv` is Hermitian over ℝ. -/
private lemma projPerp_isSymm (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2) :
    (projPerp X S)ᵀ = projPerp X S := by
  have hgit : (gramInv X S)ᵀ = gramInv X S := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact gramInv_isHermitian X S hn hcmin hcoer
  unfold projPerp
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose, hgit, ← Matrix.mul_assoc]

/-- The projection is idempotent: `Π_{S⊥}(X)² = Π_{S⊥}(X)`. -/
lemma projPerp_idempotent (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2) :
    (projPerp X S) * (projPerp X S) = projPerp X S := by
  have hgg : gram X S * gramInv X S = 1 := by
    rw [gramInv]; exact Matrix.mul_nonsing_inv _ (gram_isUnit_det X S hn hcmin hcoer)
  have hXtM : (Xsub X S)ᵀ * (Xsub X S * gramInv X S * (Xsub X S)ᵀ) = (Xsub X S)ᵀ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      show (Xsub X S)ᵀ * Xsub X S = gram X S from rfl, hgg, Matrix.one_mul]
  have hMM : (Xsub X S * gramInv X S * (Xsub X S)ᵀ) * (Xsub X S * gramInv X S * (Xsub X S)ᵀ)
      = Xsub X S * gramInv X S * (Xsub X S)ᵀ := by
    rw [Matrix.mul_assoc (Xsub X S * gramInv X S) ((Xsub X S)ᵀ), hXtM]
  unfold projPerp
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hMM]
  abel

/-- **The projection is contractive**: `‖Π_{S⊥}(X) u‖ ≤ ‖u‖`. -/
lemma projPerp_apply_norm_le (X : Matrix (Fin n) (Fin d) ℝ) (S : Finset (Fin d))
    {cmin : ℝ} (hn : 0 < n) (hcmin : 0 < cmin)
    (hcoer : ∀ v : EuclideanSpace ℝ {x // x ∈ S},
      cmin * ‖v‖ ^ 2 ≤ (1 / (n : ℝ)) * ‖designSub X S v‖ ^ 2)
    (u : EuclideanSpace ℝ (Fin n)) :
    ‖(WithLp.toLp 2 ((projPerp X S).mulVec u.ofLp) : EuclideanSpace ℝ (Fin n))‖ ≤ ‖u‖ := by
  set Pu : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 ((projPerp X S).mulVec u.ofLp) with hPu
  have hPuofLp : Pu.ofLp = (projPerp X S).mulVec u.ofLp := WithLp.ofLp_toLp 2 _
  have hsymm := projPerp_isSymm X S hn hcmin hcoer
  have hidem := projPerp_idempotent X S hn hcmin hcoer
  have hidemV : ∀ x, (projPerp X S).mulVec ((projPerp X S).mulVec x) = (projPerp X S).mulVec x := by
    intro x; rw [Matrix.mulVec_mulVec, hidem]
  have hPuPu : ⟪Pu, Pu⟫_ℝ = ⟪Pu, u⟫_ℝ := by
    simp only [PiLp.inner_apply]
    change Pu.ofLp ⬝ᵥ Pu.ofLp = u.ofLp ⬝ᵥ Pu.ofLp
    rw [hPuofLp, dotProduct_mulVec_left (projPerp X S) u.ofLp, hsymm, hidemV]
  have hcs : ⟪Pu, u⟫_ℝ ≤ ‖Pu‖ * ‖u‖ := real_inner_le_norm Pu u
  have hnsq : ⟪Pu, Pu⟫_ℝ = ‖Pu‖ ^ 2 := real_inner_self_eq_norm_sq Pu
  have hkey : ‖Pu‖ ^ 2 ≤ ‖Pu‖ * ‖u‖ := by rw [← hnsq, hPuPu]; exact hcs
  rcases (norm_nonneg Pu).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg u
  · nlinarith [hkey, hpos, mul_pos hpos hpos]

/-- **Matrix ℓ∞ operator bound** `‖A v‖_∞ ≤ |||A|||_∞ · ‖v‖_∞` (coordinatewise form). -/
lemma matLinftyNorm_mulVec_le {p q : Type*} [Finite p] [Fintype q] [Nonempty p]
    (A : Matrix p q ℝ) (v : q → ℝ) :
    (⨆ i, |(A.mulVec v) i|) ≤ matLinftyNorm A * (⨆ j, |v j|) := by
  haveI := Fintype.ofFinite p
  have hMv0 : 0 ≤ ⨆ j, |v j| := by
    rcases isEmpty_or_nonempty q with hq | hq
    · simp
    · exact le_ciSup_of_le (Finite.bddAbove_range _) (Classical.arbitrary q) (abs_nonneg _)
  apply ciSup_le
  intro i
  calc |(A.mulVec v) i| = |∑ j, A i j * v j| := rfl
    _ ≤ ∑ j, |A i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A i j| * |v j| := by simp_rw [abs_mul]
    _ ≤ ∑ j, |A i j| * (⨆ k, |v k|) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (le_ciSup (Finite.bddAbove_range fun k => |v k|) j) (abs_nonneg _)
    _ = (∑ j, |A i j|) * (⨆ k, |v k|) := by rw [← Finset.sum_mul]
    _ ≤ matLinftyNorm A * (⨆ k, |v k|) :=
        mul_le_mul_of_nonneg_right
          (le_ciSup (Finite.bddAbove_range fun i => ∑ j, |A i j|) i) hMv0

end StatLean.HighDimensionalStatistics
