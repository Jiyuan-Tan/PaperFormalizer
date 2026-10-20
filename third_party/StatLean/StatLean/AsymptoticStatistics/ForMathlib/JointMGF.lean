module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Data.Real.StarOrdered

@[expose] public section

/-!
# Joint-MGF / joint-covariance bricks

Theorem-agnostic facts in linear algebra and complex analysis supporting the
Le-Cam-third + characteristic-function argument.

* `gram_posSemidef` / `gram_block_posSemidef` — the Gram matrix
  `Gᵢⱼ = ⟪vᵢ, vⱼ⟫` of any finite family of vectors in a real inner
  product space is positive semidefinite. Specialised below to
  `joint_covariance_block_posSemidef`, which packages the
  block matrix `[[varL, A]; [Aᵀ, I_m]]` of an `(IF_eff, g_P)`-style
  family with `g_P` orthonormal.

* `analyticOn_joint_mgf` — packages an `AnalyticOnNhd` claim for a
  candidate joint MGF `F : (Fin m → ℂ) → ℂ`. Mathlib has
  only the one-dimensional analytic-MGF result
  (`Mathlib.Probability.Moments.ComplexMGF.analyticOnNhd_complexMGF`,
  on `z * X ω` with scalar `z`); the multivariate `zᵀ Δ` analogue is
  not packaged, so this brick takes the analyticity claim as input.

* `analyticOn_gaussian_mgf` — the concrete Gaussian-shift MGF
  expression `z ↦ φ * exp(b z + Q z)` is entire on `ℂᵐ` for any
  constant `φ : ℂ`, continuous-linear `b : (Fin m → ℂ) →L[ℂ] ℂ`, and
  any function `Q` with `AnalyticOnNhd ℂ Q Set.univ`, by composition of
  `AnalyticAt` primitives and `AnalyticOnNhd.cexp`.
-/

open Complex Set Filter Topology Matrix
open scoped InnerProductSpace Matrix

namespace AsymptoticStatistics.ForMathlib.JointMGF

/-! ### (i) Gram-matrix PSD packaging -/

section Gram

variable {α : Type*} [NormedAddCommGroup α] [InnerProductSpace ℝ α]

/-- *Gram-matrix is positive semidefinite.* For any finite family
`v : ι → α` (with `ι` a `Fintype`) in a real inner product space, the
Gram matrix `Gᵢⱼ = ⟪vᵢ, vⱼ⟫_ℝ` is positive semidefinite. -/
theorem gram_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → α) :
    (Matrix.of (fun i j : ι => ⟪v i, v j⟫_ℝ)).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · -- Hermitian (symmetric for real entries).
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.of_apply, real_inner_comm]
  · -- Quadratic form nonneg: `xᵀ G x = ⟪Σᵢ xᵢ • vᵢ, Σⱼ xⱼ • vⱼ⟫ ≥ 0`.
    intro x
    have h_eq : star x ⬝ᵥ
        ((Matrix.of (fun i j : ι => ⟪v i, v j⟫_ℝ)) *ᵥ x) =
          ⟪∑ i, x i • v i, ∑ j, x j • v j⟫_ℝ := by
      rw [sum_inner]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply,
        Pi.star_apply, star_trivial]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [inner_sum]
      simp_rw [real_inner_smul_left, real_inner_smul_right]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [h_eq]
    exact real_inner_self_nonneg

/-- *Block-form Gram matrix specialisation.* For a vector `w : α` and
an orthonormal family `g : Fin m → α`, the block matrix

  `[[‖w‖², A]; [Aᵀ, I_m]]`

with `Aⱼ = ⟪w, g j⟫_ℝ` is positive semidefinite (it is the Gram
matrix of the combined family on `Fin 1 ⊕ Fin m`). -/
theorem gram_block_posSemidef {m : ℕ} (w : α) (g : Fin m → α)
    (hg : Orthonormal ℝ g) :
    (Matrix.fromBlocks
        (Matrix.of (fun _ _ : Fin 1 => ‖w‖ ^ 2))
        (Matrix.of (fun _ : Fin 1 => fun j : Fin m => ⟪w, g j⟫_ℝ))
        (Matrix.of (fun i : Fin m => fun _ : Fin 1 => ⟪w, g i⟫_ℝ))
        (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef := by
  classical
  -- Combined family on `Fin 1 ⊕ Fin m`.
  let v : Fin 1 ⊕ Fin m → α := Sum.elim (fun _ : Fin 1 => w) g
  -- Its Gram matrix is PSD by `gram_posSemidef`.
  have hPSD := gram_posSemidef (ι := Fin 1 ⊕ Fin m) v
  -- Identify the Gram matrix entry-by-entry with the block form.
  have hentry :
      (Matrix.fromBlocks
          (Matrix.of (fun _ _ : Fin 1 => ‖w‖ ^ 2))
          (Matrix.of (fun _ : Fin 1 => fun j : Fin m => ⟪w, g j⟫_ℝ))
          (Matrix.of (fun i : Fin m => fun _ : Fin 1 => ⟪w, g i⟫_ℝ))
          (1 : Matrix (Fin m) (Fin m) ℝ)) =
        Matrix.of (fun i j : Fin 1 ⊕ Fin m => ⟪v i, v j⟫_ℝ) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · -- (inl, inl): ‖w‖² = ⟪w, w⟫
      simp only [Matrix.fromBlocks, Matrix.of_apply, v, Sum.elim_inl]
      rw [@real_inner_self_eq_norm_sq]
    · -- (inl, inr): ⟪w, g j⟫
      simp [Matrix.fromBlocks, Matrix.of_apply, v]
    · -- (inr, inl): ⟪g i, w⟫ vs ⟪w, g i⟫
      simp only [Matrix.fromBlocks, Matrix.of_apply, v, Sum.elim_inl,
        Sum.elim_inr]
      exact (real_inner_comm _ _).symm
    · -- (inr, inr): δᵢⱼ
      simp only [Matrix.fromBlocks, Matrix.of_apply, v, Sum.elim_inr,
        Matrix.one_apply]
      by_cases hij : i = j
      · subst hij
        rw [if_pos rfl]
        rw [@real_inner_self_eq_norm_sq]
        rw [hg.norm_eq_one i]
        ring
      · rw [if_neg hij]
        exact (hg.inner_eq_zero hij).symm
  rw [hentry]
  exact hPSD

end Gram

/-! ### (ii) Joint covariance block PSD — the form consumed by
`lecam_third_covariance_bound`. -/

/-- *Joint covariance block matrix is positive semidefinite.*

The block matrix consumed by `lecam_third_covariance_bound`'s Schur
step takes the form `[[varL, A]; [Aᵀ, I_m]]` where `varL : ℝ`,
`Aⱼ = ⟪w, g j⟫_ℝ`, and the bottom-right block is the identity
(reflecting orthonormality of `g`). This holds whenever the user
supplies an "anchor" `w` in the same inner product space with
`‖w‖² ≤ varL` — namely, `IF_eff` itself, plus the variance lower
bound `‖IF_eff‖² ≤ varL` (book content: clause (a) of the
convolution theorem).

Implementation: writes `varL = ‖w‖² + (varL - ‖w‖²)` and exhibits
the block matrix as the sum of the Gram block matrix `[[‖w‖², A];
[Aᵀ, I_m]]` (PSD by `gram_block_posSemidef`) plus
`[[varL - ‖w‖², 0]; [0, 0]]` (PSD when `varL ≥ ‖w‖²`). -/
theorem joint_covariance_block_posSemidef
    {α : Type*} [NormedAddCommGroup α] [InnerProductSpace ℝ α]
    {m : ℕ} (varL : ℝ) (w : α) (g : Fin m → α)
    (hg : Orthonormal ℝ g)
    (hvar : ‖w‖ ^ 2 ≤ varL) :
    (Matrix.fromBlocks
        (Matrix.of (fun _ _ : Fin 1 => varL))
        (Matrix.of (fun _ : Fin 1 => fun j : Fin m => ⟪w, g j⟫_ℝ))
        (Matrix.of (fun i : Fin m => fun _ : Fin 1 => ⟪w, g i⟫_ℝ))
        (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef := by
  classical
  set δ : ℝ := varL - ‖w‖ ^ 2 with hδ_def
  have hδ_nn : 0 ≤ δ := sub_nonneg.mpr hvar
  -- The Gram block matrix is PSD.
  have hMgram_psd :
      (Matrix.fromBlocks
          (Matrix.of (fun _ _ : Fin 1 => ‖w‖ ^ 2))
          (Matrix.of (fun _ : Fin 1 => fun j : Fin m => ⟪w, g j⟫_ℝ))
          (Matrix.of (fun i : Fin m => fun _ : Fin 1 => ⟪w, g i⟫_ℝ))
          (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef :=
    gram_block_posSemidef w g hg
  -- The "slack" block matrix `[[δ, 0]; [0, 0]]` is PSD: it equals
  -- `δ • E₀₀` where `E₀₀` is the rank-one Gram matrix of a single
  -- vector, hence PSD. Cleanest: use `posSemidef_iff_dotProduct_mulVec`
  -- and compute the quadratic form by hand.
  have hMslack_psd :
      (Matrix.fromBlocks
          (Matrix.of (fun _ _ : Fin 1 => δ))
          (0 : Matrix (Fin 1) (Fin m) ℝ)
          (0 : Matrix (Fin m) (Fin 1) ℝ)
          (0 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · -- Hermitian: it's symmetric and real, so equals its conjTranspose.
      ext i j
      rcases i with i | i <;> rcases j with j | j <;>
        simp [Matrix.fromBlocks, Matrix.conjTranspose_apply,
          Matrix.of_apply, Matrix.zero_apply]
    · intro x
      -- Compute the quadratic form by direct sum expansion:
      -- `star x ⬝ᵥ M *ᵥ x = Σᵢⱼ x i * M i j * x j`. Only the
      -- (inl 0, inl 0) entry is nonzero, contributing
      -- `x (inl 0) * δ * x (inl 0) ≥ 0`.
      -- Use `Fintype.sum_sum_type` to split over `Fin 1 ⊕ Fin m`.
      have h_dotprod_form :
          star x ⬝ᵥ
            ((Matrix.fromBlocks
                (Matrix.of (fun _ _ : Fin 1 => δ))
                (0 : Matrix (Fin 1) (Fin m) ℝ)
                (0 : Matrix (Fin m) (Fin 1) ℝ)
                (0 : Matrix (Fin m) (Fin m) ℝ)) *ᵥ x) =
          ∑ i : Fin 1 ⊕ Fin m, ∑ j : Fin 1 ⊕ Fin m,
            x i *
              (Matrix.fromBlocks
                  (Matrix.of (fun _ _ : Fin 1 => δ))
                  (0 : Matrix (Fin 1) (Fin m) ℝ)
                  (0 : Matrix (Fin m) (Fin 1) ℝ)
                  (0 : Matrix (Fin m) (Fin m) ℝ)) i j * x j := by
        simp [dotProduct, Matrix.mulVec, mul_comm, mul_left_comm, 
          Pi.star_apply, 
          star_trivial]
      rw [h_dotprod_form]
      -- Compute the double sum: only the (inl 0, inl 0) term is nonzero.
      have hcompute :
          (∑ i : Fin 1 ⊕ Fin m, ∑ j : Fin 1 ⊕ Fin m,
              x i *
                (Matrix.fromBlocks
                    (Matrix.of (fun _ _ : Fin 1 => δ))
                    (0 : Matrix (Fin 1) (Fin m) ℝ)
                    (0 : Matrix (Fin m) (Fin 1) ℝ)
                    (0 : Matrix (Fin m) (Fin m) ℝ)) i j * x j) =
            δ * (x (Sum.inl 0)) ^ 2 := by
        rw [Fintype.sum_sum_type]
        -- The `inr` outer sum is zero.
        have h_inr_zero : ∑ i : Fin m,
            ∑ j : Fin 1 ⊕ Fin m,
              x (Sum.inr i) *
                (Matrix.fromBlocks
                    (Matrix.of (fun _ _ : Fin 1 => δ))
                    (0 : Matrix (Fin 1) (Fin m) ℝ)
                    (0 : Matrix (Fin m) (Fin 1) ℝ)
                    (0 : Matrix (Fin m) (Fin m) ℝ)) (Sum.inr i) j * x j = 0 := by
          refine Finset.sum_eq_zero (fun i _ => ?_)
          rw [Fintype.sum_sum_type]
          simp [Matrix.fromBlocks, Matrix.zero_apply]
        rw [h_inr_zero, add_zero]
        -- The `inl` outer sum: only `inr` inner contributes 0 and `inl 0` contributes δ.
        rw [Fin.sum_univ_one]
        rw [Fintype.sum_sum_type]
        simp [Matrix.fromBlocks, Matrix.of_apply, Matrix.zero_apply,
          sq, mul_comm, mul_left_comm]
      rw [hcompute]
      exact mul_nonneg hδ_nn (sq_nonneg _)
  -- Decompose the target matrix as a sum.
  have h_decomp :
      (Matrix.fromBlocks
          (Matrix.of (fun _ _ : Fin 1 => varL))
          (Matrix.of (fun _ : Fin 1 => fun j : Fin m => ⟪w, g j⟫_ℝ))
          (Matrix.of (fun i : Fin m => fun _ : Fin 1 => ⟪w, g i⟫_ℝ))
          (1 : Matrix (Fin m) (Fin m) ℝ)) =
      (Matrix.fromBlocks
          (Matrix.of (fun _ _ : Fin 1 => ‖w‖ ^ 2))
          (Matrix.of (fun _ : Fin 1 => fun j : Fin m => ⟪w, g j⟫_ℝ))
          (Matrix.of (fun i : Fin m => fun _ : Fin 1 => ⟪w, g i⟫_ℝ))
          (1 : Matrix (Fin m) (Fin m) ℝ)) +
      (Matrix.fromBlocks
          (Matrix.of (fun _ _ : Fin 1 => δ))
          (0 : Matrix (Fin 1) (Fin m) ℝ)
          (0 : Matrix (Fin m) (Fin 1) ℝ)
          (0 : Matrix (Fin m) (Fin m) ℝ)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.of_apply, Matrix.add_apply, hδ_def]
  rw [h_decomp]
  exact hMgram_psd.add hMslack_psd

/-! ### (iii) Joint MGF analyticity -/

section JointMGFAnalyticity

variable {m : ℕ}

/-- *Joint MGF analyticity.*

Mathlib has the one-dimensional analytic-MGF result
(`Mathlib.Probability.Moments.ComplexMGF.analyticOnNhd_complexMGF`,
operating on `z * X ω` with scalar `z`). The multivariate `zᵀ Δ`
analogue (showing `F(z) := E[exp(i u·S + zᵀ Δ)]` entire on `ℂᵐ`) is
not packaged, so this brick takes the analyticity claim as input and
returns it as an `AnalyticOnNhd ℂ F Set.univ`. Isolating it here keeps
the import surface stable: when the multivariate
`analyticOnNhd_complexMGF` lands, only this file changes. -/
theorem analyticOn_joint_mgf
    {F : (Fin m → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ) :
    AnalyticOnNhd ℂ F Set.univ := hF

/-- *Gaussian-side MGF is entire.*

The Gaussian-shift prediction `G(z) := φ · exp(b z + Q z)` for a
constant `φ : ℂ`, a continuous linear `b : (Fin m → ℂ) →L[ℂ] ℂ`, and
a function `Q : (Fin m → ℂ) → ℂ` that is itself analytic on
`Set.univ` (e.g. a continuous quadratic `Q z = ½ ⟪z, z⟫`), is entire
on `ℂᵐ`.

This is the trivial half of the `lecam_third_convolution` analytic
input: composition of entire functions. The exact form used by
`lecam_third_convolution` is

  `G(z) = φ_L(u) · exp(i u·A_m·z + ½ zᵀ z)`

which fits this template with `φ = φ_L(u)`, `b z = i u · ⟨A_m, z⟩`,
`Q z = ½ ⟪z, z⟫`. -/
theorem analyticOn_gaussian_mgf
    (φ : ℂ) (b : (Fin m → ℂ) →L[ℂ] ℂ)
    {Q : (Fin m → ℂ) → ℂ} (hQ : AnalyticOnNhd ℂ Q Set.univ) :
    AnalyticOnNhd ℂ (fun z : Fin m → ℂ => φ * Complex.exp (b z + Q z))
      Set.univ := by
  -- `b` is continuous linear, hence analytic everywhere.
  have hb : AnalyticOnNhd ℂ (fun z : Fin m → ℂ => b z) Set.univ :=
    fun z _ => b.analyticAt z
  -- Sum is analytic.
  have hbQ : AnalyticOnNhd ℂ (fun z : Fin m → ℂ => b z + Q z) Set.univ :=
    hb.add hQ
  -- exp ∘ (b + Q) is analytic.
  have hexp : AnalyticOnNhd ℂ
      (fun z : Fin m → ℂ => Complex.exp (b z + Q z)) Set.univ :=
    hbQ.cexp
  -- φ * exp(b + Q) is analytic.
  exact (analyticOnNhd_const : AnalyticOnNhd ℂ
    (fun _ : Fin m → ℂ => φ) Set.univ).mul hexp

end JointMGFAnalyticity

end AsymptoticStatistics.ForMathlib.JointMGF
