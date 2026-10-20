module
public import StatLean.NonparametricStatistics.RKHS.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# Kernel functions (positive semidefinite functions of two variables)

A function `K : X → X → 𝕜` is a **kernel function** if it is Hermitian and every finite
quadratic form `∑ᵢⱼ conj(aᵢ) aⱼ K(xᵢ, xⱼ)` has nonnegative real part.  Over `ℂ` the
Hermitian condition is automatic from positivity of the complex quadratic form; over `ℝ`
it is *not* (e.g. `K = ![![0, 1], ![-1, 0]]` has vanishing real quadratic form), so we
build symmetry into the definition — this matches the classical convention that a
real-valued kernel is required to be positive for all *complex* scalar families.

Main results here:
* `isKernelFun_featureKernel` — a Gram function `(x, y) ↦ ⟪φ x, φ y⟫` of any map
  `φ : X → E` into an inner product space is a kernel function;
* `isKernelFun_scalarKernel` — the reproducing kernel of an RKHS is a kernel function;
* `gramian_posSemidef` / `gramian_posDef_iff_linearIndependent` — the Grammian matrix
  of a finite family of vectors is positive semidefinite, and positive definite iff the
  family is linearly independent.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 2, §2.2, Definition 2.12 (kernel functions) and Proposition 2.13 (reproducing
kernels are kernel functions); §2.3.4, Definition 2.22 and Proposition 2.23 (Grammians); Chapter
8, §8.2 (kernels induced by feature maps).

**Proof formalization notes.** `IsKernelFun` builds Hermitian symmetry into the definition: over
`ℝ` positivity of the real quadratic form does *not* imply symmetry (the book's Remark 2.16
example $K(1,2) = 1$, $K(2,1) = -1$), and the classical convention quantifies over complex
scalars; the built-in symmetry makes the real and complex cases uniform. Points are not required
to be distinct (coefficient merging makes the two formulations equivalent). Positivity of
Gram/feature kernels is the single computation $\sum_{ij} \bar a_i a_j \langle\varphi(x_i),
\varphi(x_j)\rangle = \|\sum_i a_i \varphi(x_i)\|^2$, and Proposition 2.13 is its specialization
$\varphi = x \mapsto k_x$ via `scalarKernel_eq_featureKernel`.

**Bibliographic comments.** Positive definite functions in this sense were introduced by
E. H. Moore (1935, under the name "positive Hermitian matrices") and J. Mercer,
*Functions of positive and negative type*, Philos. Trans. Roy. Soc. A **209** (1909),
415–446; the Grammian criterion for linear independence is classical (J. P. Gram, 1883).
-/

open ComplexConjugate
open scoped InnerProductSpace ComplexOrder

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}

/-- **Kernel function** (positive semidefinite function): `K : X → X → 𝕜` is Hermitian and
all finite quadratic forms `∑ᵢⱼ conj(aᵢ) aⱼ K(xᵢ, xⱼ)` have nonnegative real part.
Points are not required to be distinct (equivalent to the distinct-points formulation by
merging coefficients). -/
structure IsKernelFun (K : X → X → 𝕜) : Prop where
  /-- Hermitian symmetry: `conj (K x y) = K y x`.  Constitutive: over `ℝ` this is not
  implied by positivity of the real quadratic form and is part of the classical notion. -/
  conj_symm : ∀ x y, conj (K x y) = K y x
  /-- Positivity of all finite quadratic forms. -/
  re_sum_nonneg : ∀ (n : ℕ) (x : Fin n → X) (a : Fin n → 𝕜),
    0 ≤ RCLike.re (∑ i, ∑ j, conj (a i) * a j * K (x i) (x j))

/-- The quadratic form of a kernel function is real: its imaginary part vanishes. -/
theorem IsKernelFun.im_sum_eq_zero {K : X → X → 𝕜} (hK : IsKernelFun K)
    (n : ℕ) (x : Fin n → X) (a : Fin n → 𝕜) :
    RCLike.im (∑ i, ∑ j, conj (a i) * a j * K (x i) (x j)) = 0 := by
  refine RCLike.conj_eq_iff_im.mp ?_
  simp only [map_sum, map_mul, RCLike.conj_conj, hK.conj_symm]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The diagonal of a kernel function is real with nonnegative real part. -/
theorem IsKernelFun.re_apply_self_nonneg {K : X → X → 𝕜} (hK : IsKernelFun K) (x : X) :
    0 ≤ RCLike.re (K x x) := by
  simpa using hK.re_sum_nonneg 1 (fun _ => x) (fun _ => 1)

/-- Conical combination: `p₁ K₁ + p₂ K₂` is a kernel function for `p₁, p₂ ≥ 0`. -/
theorem IsKernelFun.add_smul {K₁ K₂ : X → X → 𝕜} (h₁ : IsKernelFun K₁)
    (h₂ : IsKernelFun K₂) {p₁ p₂ : ℝ}
    (hp₁ : 0 ≤ p₁)  -- USER-INPUT: nonnegative weight
    (hp₂ : 0 ≤ p₂) :  -- USER-INPUT: nonnegative weight
    IsKernelFun (fun x y => (p₁ : 𝕜) * K₁ x y + (p₂ : 𝕜) * K₂ x y) := by
  refine ⟨fun x y => ?_, fun n x a => ?_⟩
  · simp only [map_add, map_mul, RCLike.conj_ofReal, h₁.conj_symm, h₂.conj_symm]
  · have key : (∑ i, ∑ j, conj (a i) * a j *
          ((p₁ : 𝕜) * K₁ (x i) (x j) + (p₂ : 𝕜) * K₂ (x i) (x j)))
        = (p₁ : 𝕜) * (∑ i, ∑ j, conj (a i) * a j * K₁ (x i) (x j))
          + (p₂ : 𝕜) * (∑ i, ∑ j, conj (a i) * a j * K₂ (x i) (x j)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [key, map_add, RCLike.re_ofReal_mul, RCLike.re_ofReal_mul]
    exact add_nonneg (mul_nonneg hp₁ (h₁.re_sum_nonneg n x a))
      (mul_nonneg hp₂ (h₂.re_sum_nonneg n x a))

/-- Conjugation by a scalar function: `(x, y) ↦ conj (g x) * K x y * g y` is a kernel
function whenever `K` is. -/
theorem IsKernelFun.conj_mul {K : X → X → 𝕜} (hK : IsKernelFun K) (g : X → 𝕜) :
    IsKernelFun (fun x y => conj (g x) * K x y * g y) := by
  refine ⟨fun x y => ?_, fun n x a => ?_⟩
  · simp only [map_mul, RCLike.conj_conj, hK.conj_symm]
    ring
  · have key : (∑ i, ∑ j, conj (a i) * a j * (conj (g (x i)) * K (x i) (x j) * g (x j)))
        = ∑ i, ∑ j, conj (a i * g (x i)) * (a j * g (x j)) * K (x i) (x j) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]
      ring
    rw [key]
    exact hK.re_sum_nonneg n x (fun i => a i * g (x i))

section FeatureKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜) in
/-- The **kernel induced by a feature map** `φ : X → E`:
`K(x, y) = ⟪φ x, φ y⟫_𝕜` (conjugate-linear slot first, per Mathlib's convention). -/
noncomputable def featureKernel (φ : X → E) : X → X → 𝕜 := fun x y => ⟪φ x, φ y⟫_𝕜

/-- A Gram function of an arbitrary family of vectors is a kernel function:
the quadratic form is `‖∑ᵢ aᵢ φ(xᵢ)‖² ≥ 0`. -/
theorem isKernelFun_featureKernel (φ : X → E) : IsKernelFun (featureKernel 𝕜 φ) := by
  refine ⟨fun x y => inner_conj_symm _ _, fun n x a => ?_⟩
  simp only [featureKernel]
  have key : (∑ i, ∑ j, conj (a i) * a j * ⟪φ (x i), φ (x j)⟫_𝕜)
      = ⟪∑ i, a i • φ (x i), ∑ j, a j • φ (x j)⟫_𝕜 := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, inner_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [inner_smul_right]; ring
  rw [key]
  exact inner_self_nonneg

end FeatureKernel

section RKHSKernel

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

variable (H) in
/-- The reproducing kernel of an RKHS is its kernel-function Gram representation:
`scalarKernel H = featureKernel 𝕜 (kernelFun H)`. -/
theorem scalarKernel_eq_featureKernel :
    scalarKernel H = featureKernel 𝕜 (kernelFun (X := X) H) := by
  funext x y
  rw [scalarKernel_eq_inner, featureKernel]

variable (H) in
/-- The reproducing kernel of an RKHS is a kernel function. -/
theorem isKernelFun_scalarKernel : IsKernelFun (scalarKernel (X := X) H) := by
  rw [scalarKernel_eq_featureKernel]
  exact isKernelFun_featureKernel _

end RKHSKernel

section Gramian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable (𝕜) in
/-- The **Grammian** of a finite family of vectors: the matrix of pairwise inner products
`G i j = ⟪h i, h j⟫_𝕜` (conjugate-linear slot first). -/
noncomputable def gramian {n : ℕ} (h : Fin n → E) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j => ⟪h i, h j⟫_𝕜

-- The Grammian quadratic form is the inner product of the corresponding linear
-- combination with itself.
private theorem gramian_quadratic {n : ℕ} (h : Fin n → E) (x : Fin n →₀ 𝕜) :
    (x.sum fun i xi => x.sum fun j xj => star xi * gramian 𝕜 h i j * xj)
      = ⟪Finsupp.linearCombination 𝕜 h x, Finsupp.linearCombination 𝕜 h x⟫_𝕜 := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum_inner]
  refine Finsupp.sum_congr fun i _ => ?_
  rw [Finsupp.inner_sum]
  refine Finsupp.sum_congr fun j _ => ?_
  rw [inner_smul_left, inner_smul_right]
  simp only [gramian, Matrix.of_apply, RCLike.star_def]
  ring

/-- The Grammian of any finite family is positive semidefinite. -/
theorem gramian_posSemidef {n : ℕ} (h : Fin n → E) : (gramian 𝕜 h).PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, gramian, Matrix.of_apply, RCLike.star_def,
      inner_conj_symm]
  · rw [gramian_quadratic, RCLike.nonneg_iff]
    exact ⟨inner_self_nonneg, inner_self_im _⟩

/-- The Grammian is positive definite iff the family is linearly independent. -/
theorem gramian_posDef_iff_linearIndependent {n : ℕ} (h : Fin n → E) :
    (gramian 𝕜 h).PosDef ↔ LinearIndependent 𝕜 h := by
  rw [linearIndependent_iff]
  constructor
  · intro hpd l hl
    by_contra hne
    have hpos := hpd.2 hne
    rw [gramian_quadratic, hl, inner_zero_left] at hpos
    exact lt_irrefl (0 : 𝕜) hpos
  · intro hli
    refine ⟨(gramian_posSemidef h).1, fun x hx => ?_⟩
    rw [gramian_quadratic]
    have hv : Finsupp.linearCombination 𝕜 h x ≠ 0 := fun hv => hx (hli x hv)
    refine lt_of_le_of_ne ?_ (fun hcon => hv (inner_self_eq_zero.mp hcon.symm))
    rw [RCLike.nonneg_iff]
    exact ⟨inner_self_nonneg, inner_self_im _⟩

end Gramian

end StatLean.NonparametricStatistics
