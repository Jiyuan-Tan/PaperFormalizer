module
public import StatLean.NonparametricStatistics.RKHS.KernelFunction
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-!
# The all-ones matrix and the min kernel

Two classical positivity computations:

* the `n × n` all-ones matrix `Jₙ` is positive semidefinite, has eigenvalue `n` (on the
  constant vector), every eigenvalue is `0` or `n`, and has rank one;
* the function `K(x, y) = min x y` on `[0, ∞)` is a kernel function.  Rather than the
  inductive block decomposition, we exhibit `min` as the Gram function of the feature map
  `x ↦ 𝟙_{[0,x]} ∈ L²([0,∞))`, since `∫ 𝟙_{[0,x]} 𝟙_{[0,y]} = min x y`.

The RKHS of the min kernel (Cameron–Martin space of Brownian motion) is identified with
the range of the Volterra operator in `RangeSpace.lean`.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 2, §2.3.2, Lemma 2.20 (the all-ones matrix $J_n$) and Proposition 2.21 (the min
kernel on $[0,\infty)$).

**Proof formalization notes.** Instead of the book's inductive block decomposition, positivity of
the min kernel is exhibited through the feature map $x \mapsto \mathbf{1}_{[0,x]} \in
L^2[0,\infty)$ with $\langle \mathbf{1}_{[0,x]}, \mathbf{1}_{[0,y]}\rangle = \min(x,y)$ — the same
identity that later identifies this space as the range of the Volterra operator (book §11.2.1).
The $J_n$ spectrum is captured as: PSD, eigenvalue $n$ on the constant vector, every eigenvalue in
$\{0, n\}$ (from $J_n^2 = n J_n$), and $\operatorname{rank} J_n = 1$.

**Bibliographic comments.** The min kernel is the covariance of Brownian motion
(N. Wiener 1923); its RKHS was identified by R. H. Cameron and W. T. Martin, Ann. of
Math. **48** (1947), 385–392, and the general covariance–RKHS correspondence is due to
M. Loève and E. Parzen, *Statistical inference on time series by Hilbert space methods*
(1959).
-/

open ComplexConjugate MeasureTheory
open scoped InnerProductSpace ComplexOrder

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜]

section AllOnes

variable (𝕜) in
/-- The `n × n` all-ones matrix `Jₙ`. -/
def allOnesMatrix (n : ℕ) : Matrix (Fin n) (Fin n) 𝕜 := Matrix.of fun _ _ => 1

/-- `Jₙ` is the outer product of the all-ones vector with itself. -/
private theorem allOnesMatrix_eq_vecMulVec (n : ℕ) :
    allOnesMatrix 𝕜 n
      = Matrix.vecMulVec (fun _ => (1 : 𝕜)) (star (fun _ => (1 : 𝕜)) : Fin n → 𝕜) := by
  ext i j
  simp [allOnesMatrix, Matrix.vecMulVec]

/-- `Jₙ *ᵥ v` is the constant vector with value `∑ j, v j`. -/
private theorem allOnesMatrix_mulVec (n : ℕ) (v : Fin n → 𝕜) (i : Fin n) :
    Matrix.mulVec (allOnesMatrix 𝕜 n) v i = ∑ j, v j := by
  simp [allOnesMatrix, Matrix.mulVec, dotProduct]

/-- The all-ones matrix is positive semidefinite: its quadratic form is `|∑ αᵢ|²`. -/
theorem posSemidef_allOnesMatrix (n : ℕ) : (allOnesMatrix 𝕜 n).PosSemidef := by
  rw [allOnesMatrix_eq_vecMulVec]
  exact Matrix.posSemidef_vecMulVec_self_star _

/-- `n` is an eigenvalue of the all-ones matrix `Jₙ` (witnessed by the constant vector),
for `n ≥ 1`. -/
theorem hasEigenvalue_allOnesMatrix (n : ℕ)
    -- LEAN-ONLY: nonempty index type; for `n = 0` there are no eigenvectors at all
    (hn : 0 < n) :
    Module.End.HasEigenvalue (Matrix.toLin' (allOnesMatrix 𝕜 n)) (n : 𝕜) := by
  have hv : (fun _ => (1 : 𝕜)) ≠ (0 : Fin n → 𝕜) := by
    intro h
    have := congrFun h ⟨0, hn⟩
    simp at this
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := fun _ => (1 : 𝕜)) ⟨?_, hv⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  funext i
  rw [allOnesMatrix_mulVec]
  simp

/-- Every eigenvalue of the all-ones matrix is `0` or `n` (since `Jₙ² = n·Jₙ`). -/
theorem eigenvalue_allOnesMatrix (n : ℕ) (μ : 𝕜)
    (hμ : Module.End.HasEigenvalue (Matrix.toLin' (allOnesMatrix 𝕜 n)) μ) :
    μ = 0 ∨ μ = (n : 𝕜) := by
  obtain ⟨v, hmem, hv0⟩ := hμ.exists_hasEigenvector
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply] at hmem
  have key : ∀ i, ∑ j, v j = μ * v i := by
    intro i
    have h := congrFun hmem i
    rw [allOnesMatrix_mulVec] at h
    simpa using h
  by_cases hS : ∑ j, v j = 0
  · left
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (funext h)
    have h := key i
    rw [hS] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hi
  · right
    have hsum : (n : 𝕜) * (∑ j, v j) = μ * (∑ j, v j) := by
      have h1 : ∑ _i : Fin n, (∑ j, v j) = ∑ i : Fin n, μ * v i :=
        Finset.sum_congr rfl fun i _ => key i
      rw [Finset.sum_const, ← Finset.mul_sum] at h1
      simpa [nsmul_eq_mul] using h1
    exact (mul_right_cancel₀ hS hsum).symm

/-- The all-ones matrix has rank one (`n ≥ 1`): the eigenvalue `n` has multiplicity one. -/
theorem rank_allOnesMatrix (n : ℕ)
    -- LEAN-ONLY: nonempty index type; `J₀` has rank zero
    (hn : 0 < n) :
    (allOnesMatrix 𝕜 n).rank = 1 := by
  refine le_antisymm ?_ ?_
  · rw [allOnesMatrix_eq_vecMulVec]
    exact Matrix.rank_vecMulVec_le _ _
  · rw [Nat.one_le_iff_ne_zero]
    intro h
    rw [Matrix.rank] at h
    have hbot : LinearMap.range (allOnesMatrix 𝕜 n).mulVecLin = ⊥ :=
      Submodule.finrank_eq_zero.mp h
    have hmem : (allOnesMatrix 𝕜 n).mulVecLin (fun _ => (1 : 𝕜))
        ∈ LinearMap.range (allOnesMatrix 𝕜 n).mulVecLin := ⟨_, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    have h0 := congrFun hmem ⟨0, hn⟩
    rw [Matrix.mulVecLin_apply, allOnesMatrix_mulVec] at h0
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one, Pi.zero_apply] at h0
    exact absurd (Nat.cast_eq_zero.mp h0) hn.ne'

end AllOnes

section MinKernel

/-- `[0,x] ∩ [0,y] = [0, min x y]`. -/
private theorem Icc_zero_inter_Icc_zero (x y : ℝ) :
    Set.Icc (0 : ℝ) x ∩ Set.Icc (0 : ℝ) y = Set.Icc (0 : ℝ) (min x y) := by
  rw [Set.Icc_inter_Icc, max_self]

/-- The Lebesgue measure of `[0,m]` as a real number, for `m ≥ 0`. -/
private theorem volume_real_Icc_zero (m : ℝ) (hm : 0 ≤ m) :
    (volume : Measure ℝ).real (Set.Icc 0 m) = m := by
  rw [Measure.real, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hm]

/-- `[0,z]` has finite Lebesgue measure. -/
private theorem volume_Icc_zero_ne_top (z : ℝ) : (volume : Measure ℝ) (Set.Icc 0 z) ≠ ⊤ := by
  rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

/-- `min x y = ∫ 𝟙_{[0,x]} · 𝟙_{[0,y]}` over `[0, ∞)`: the min kernel is the Gram
function of indicator feature vectors. -/
theorem min_eq_integral_indicator (x y : ℝ)
    -- USER-INPUT: the points lie in `[0, ∞)`
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min x y
      = ∫ t, Set.indicator (Set.Icc 0 x) (fun _ => (1 : ℝ)) t
          * Set.indicator (Set.Icc 0 y) (fun _ => (1 : ℝ)) t := by
  have hfun : (fun t => Set.indicator (Set.Icc 0 x) (fun _ => (1 : ℝ)) t
        * Set.indicator (Set.Icc 0 y) (fun _ => (1 : ℝ)) t)
      = Set.indicator (Set.Icc (0 : ℝ) (min x y)) (fun _ => (1 : ℝ)) := by
    funext t
    rw [← Set.inter_indicator_mul, Icc_zero_inter_Icc_zero]
    simp
  rw [hfun, MeasureTheory.integral_indicator_const _ measurableSet_Icc,
    volume_real_Icc_zero _ (le_min hx hy), smul_eq_mul, mul_one]

/-- A real Gram function is a kernel function: the quadratic form is `‖∑ᵢ aᵢ φ(xᵢ)‖² ≥ 0`.
(A self-contained copy of `isKernelFun_featureKernel` over `ℝ`, so that `isKernelFun_min`
does not inherit that file's `sorry`.) -/
private theorem isKernelFun_featureKernel_real {X : Type*} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (φ : X → E) : IsKernelFun (featureKernel ℝ φ) where
  conj_symm x y := by
    simp only [featureKernel, starRingEnd_apply, star_trivial]
    exact real_inner_comm _ _
  re_sum_nonneg n x a := by
    have hquad : ∑ i, ∑ j, conj (a i) * a j * featureKernel ℝ φ (x i) (x j)
        = ⟪∑ i, a i • φ (x i), ∑ j, a j • φ (x j)⟫_ℝ := by
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [real_inner_smul_right]
      simp only [featureKernel, starRingEnd_apply, star_trivial]
      ring
    rw [hquad]
    simp

/-- **The min kernel is a kernel function** on `[0, ∞)`. -/
theorem isKernelFun_min :
    IsKernelFun fun x y : Set.Ici (0 : ℝ) => min x.1 y.1 := by
  have key : ∀ x y : Set.Ici (0 : ℝ),
      min (x : ℝ) (y : ℝ)
        = ⟪indicatorConstLp (E := ℝ) 2 (measurableSet_Icc (a := (0 : ℝ)) (b := (x : ℝ)))
              (volume_Icc_zero_ne_top _) (1 : ℝ),
            indicatorConstLp (E := ℝ) 2 (measurableSet_Icc (a := (0 : ℝ)) (b := (y : ℝ)))
              (volume_Icc_zero_ne_top _) (1 : ℝ)⟫_ℝ := by
    intro x y
    rw [MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
        (μ := (volume : Measure ℝ)) (measurableSet_Icc (a := (0 : ℝ)) (b := (x : ℝ)))
        (measurableSet_Icc (a := (0 : ℝ)) (b := (y : ℝ)))
        (volume_Icc_zero_ne_top _) (volume_Icc_zero_ne_top _),
      Icc_zero_inter_Icc_zero,
      volume_real_Icc_zero _ (le_min (Set.mem_Ici.mp x.2) (Set.mem_Ici.mp y.2))]
  have hcast : (fun x y : Set.Ici (0 : ℝ) => min x.1 y.1)
      = featureKernel ℝ (fun x : Set.Ici (0 : ℝ) =>
          indicatorConstLp (E := ℝ) 2 (measurableSet_Icc (a := (0 : ℝ)) (b := (x : ℝ)))
            (volume_Icc_zero_ne_top _) (1 : ℝ)) := by
    funext x y
    exact key x y
  rw [hcast]
  exact isKernelFun_featureKernel_real _

end MinKernel

end StatLean.NonparametricStatistics
