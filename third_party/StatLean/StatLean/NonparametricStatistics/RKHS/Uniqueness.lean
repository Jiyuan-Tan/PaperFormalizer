module
public import StatLean.NonparametricStatistics.RKHS.Basic
public import Mathlib.Analysis.Normed.Operator.Extend

@[expose] public section

/-!
# The kernel determines the RKHS

Two scalar RKHSs on the same set with the same reproducing kernel are "equal": there is a
(unique) isometric linear equivalence between them commuting with point evaluation.  In
particular they consist of the same functions on `X` with the same norms.  The proof
matches finite combinations of kernel functions (where the inner products are determined
by the kernel) and extends by density (`RKHS.kerFun_dense`).

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 2, §2.1, Proposition 2.3 (two RKHSs with the same kernel coincide, with equal
norms).

**Proof formalization notes.** "Coincide" is formalized as an isometric linear equivalence
commuting with point evaluation. The equivalence is produced by `LinearEquiv.extendOfIsometry`
applied to the identity on coefficient families: `Finsupp.linearCombination` of the kernel
functions has dense range in both spaces (`RKHS.kerFun_dense`) and equal Gram norms (the kernel
double sum), which is precisely the book's compute-on-the-span-and-extend argument.

**Bibliographic comments.** N. Aronszajn, Trans. Amer. Math. Soc. **68** (1950), Part I
§2, Théorème (uniqueness half of the Moore–Aronszajn correspondence).
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
variable {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]
variable [RKHS 𝕜 H₁ X 𝕜] [RKHS 𝕜 H₂ X 𝕜]

section Bricks

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

-- The finite combinations of kernel functions, parametrized by their coefficient family.
-- Its range is the span of the kernel functions, which is dense by `RKHS.kerFun_dense`.
private noncomputable def kerComb : (X →₀ 𝕜) →ₗ[𝕜] H :=
  Finsupp.linearCombination 𝕜 (kernelFun (X := X) H)

private theorem denseRange_kerComb : DenseRange (kerComb (X := X) (H := H)) := by
  have hsm : ∀ (x : X) (w : 𝕜), RKHS.kerFun H x w = w • kernelFun H x := by
    intro x w
    rw [kernelFun, ← ContinuousLinearMap.map_smul]
    congr 1
    simp
  have hspan : LinearMap.range (kerComb (X := X) (H := H))
      = Submodule.span 𝕜 {v : H | ∃ (x : X) (w : 𝕜), RKHS.kerFun H x w = v} := by
    rw [kerComb, Finsupp.range_linearCombination]
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro v ⟨x, rfl⟩
      exact Submodule.subset_span ⟨x, 1, rfl⟩
    · rw [Submodule.span_le]
      rintro v ⟨x, w, rfl⟩
      rw [hsm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  have htop := RKHS.kerFun_dense (𝕜 := 𝕜) (H := H) (X := X) (V := 𝕜)
  have : Dense ((LinearMap.range (kerComb (X := X) (H := H)) : Submodule 𝕜 H) : Set H) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (by rw [hspan]; exact htop)
  simpa [DenseRange, LinearMap.coe_range] using this

-- The Gram identity: the squared norm of a finite combination is the kernel double sum.
private theorem inner_kerComb_self (c : X →₀ 𝕜) :
    ⟪kerComb (X := X) (H := H) c, kerComb (X := X) (H := H) c⟫_𝕜
      = c.sum fun x cx => c.sum fun y cy => conj cx * cy * scalarKernel H x y := by
  rw [kerComb, Finsupp.linearCombination_apply, Finsupp.sum_inner]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [Finsupp.inner_sum]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [inner_smul_left, inner_smul_right, scalarKernel_eq_inner]
  ring

-- The values of a finite combination are the kernel sums.
private theorem apply_kerComb (c : X →₀ 𝕜) (x : X) :
    (kerComb (X := X) (H := H) c : X → 𝕜) x = c.sum fun y cy => cy * scalarKernel H x y := by
  rw [← inner_kernelFun x, kerComb, Finsupp.linearCombination_apply, Finsupp.inner_sum]
  refine Finsupp.sum_congr fun y _ => ?_
  rw [inner_smul_right, scalarKernel_eq_inner]

end Bricks

/-- **The kernel determines the space**: two RKHSs on `X` with equal scalar kernels are
isometrically equivalent through an equivalence that commutes with point evaluation. -/
theorem exists_isometryEquiv_of_scalarKernel_eq
    -- USER-INPUT: the two spaces have the same reproducing kernel
    (hK : scalarKernel H₁ = scalarKernel (X := X) H₂) :
    ∃ e : H₁ ≃ₗᵢ[𝕜] H₂, ∀ (f : H₁) (x : X), (e f) x = f x := by
  have hd₁ : DenseRange (kerComb (X := X) (H := H₁)) := denseRange_kerComb
  have hd₂ : DenseRange (kerComb (X := X) (H := H₂)) := denseRange_kerComb
  have hnorm : ∀ c : X →₀ 𝕜,
      ‖kerComb (X := X) (H := H₂) ((LinearEquiv.refl 𝕜 (X →₀ 𝕜)) c)‖
        = ‖kerComb (X := X) (H := H₁) c‖ := by
    intro c
    have hin : ⟪kerComb (X := X) (H := H₂) c, kerComb (X := X) (H := H₂) c⟫_𝕜
        = ⟪kerComb (X := X) (H := H₁) c, kerComb (X := X) (H := H₁) c⟫_𝕜 := by
      rw [inner_kerComb_self, inner_kerComb_self, hK]
    have h2 : ((‖kerComb (X := X) (H := H₂) c‖ : 𝕜)) ^ 2
        = ((‖kerComb (X := X) (H := H₁) c‖ : 𝕜)) ^ 2 := by
      rw [← inner_self_eq_norm_sq_to_K, ← inner_self_eq_norm_sq_to_K, hin]
    have h3 : ‖kerComb (X := X) (H := H₂) c‖ ^ 2 = ‖kerComb (X := X) (H := H₁) c‖ ^ 2 :=
      RCLike.ofReal_inj.mp (by push_cast; exact h2)
    calc ‖kerComb (X := X) (H := H₂) c‖
        = Real.sqrt (‖kerComb (X := X) (H := H₂) c‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ = Real.sqrt (‖kerComb (X := X) (H := H₁) c‖ ^ 2) := by rw [h3]
      _ = ‖kerComb (X := X) (H := H₁) c‖ := Real.sqrt_sq (norm_nonneg _)
  refine ⟨(LinearEquiv.refl 𝕜 (X →₀ 𝕜)).extendOfIsometry _ _ hd₁ hd₂ hnorm, fun f x => ?_⟩
  have hcomm : (fun g : H₁ =>
      ((LinearEquiv.refl 𝕜 (X →₀ 𝕜)).extendOfIsometry _ _ hd₁ hd₂ hnorm g : X → 𝕜) x)
      = fun g : H₁ => (g : X → 𝕜) x := by
    refine hd₁.equalizer ((RKHS.continuous_eval x).comp
      (LinearIsometryEquiv.continuous _)) (RKHS.continuous_eval x) ?_
    funext c
    change ((LinearEquiv.refl 𝕜 (X →₀ 𝕜)).extendOfIsometry _ _ hd₁ hd₂ hnorm
      (kerComb (X := X) (H := H₁) c) : X → 𝕜) x = (kerComb (X := X) (H := H₁) c : X → 𝕜) x
    rw [LinearEquiv.extendOfIsometry_eq]
    change (kerComb (X := X) (H := H₂) c : X → 𝕜) x = _
    rw [apply_kerComb, apply_kerComb, hK]
  exact congrFun hcomm f

/-- An evaluation-commuting map between RKHSs on `X` is unique (evaluations separate
points of an RKHS). -/
theorem evaluation_commuting_unique {e₁ e₂ : H₁ → H₂}
    (h₁ : ∀ (f : H₁) (x : X), (e₁ f) x = f x)
    (h₂ : ∀ (f : H₁) (x : X), (e₂ f) x = f x) : e₁ = e₂ := by
  funext f
  exact RKHS.ext fun x => (h₁ f x).trans (h₂ f x).symm

/-- Two RKHSs with the same kernel consist of the same functions on `X`. -/
theorem range_coe_eq_of_scalarKernel_eq
    -- USER-INPUT: the two spaces have the same reproducing kernel
    (hK : scalarKernel H₁ = scalarKernel (X := X) H₂) :
    Set.range (fun f : H₁ => (f : X → 𝕜)) = Set.range (fun f : H₂ => (f : X → 𝕜)) := by
  obtain ⟨e, he⟩ := exists_isometryEquiv_of_scalarKernel_eq hK
  refine Set.Subset.antisymm ?_ ?_
  · rintro g ⟨f, rfl⟩
    exact ⟨e f, funext fun x => he f x⟩
  · rintro g ⟨f, rfl⟩
    refine ⟨e.symm f, funext fun x => ?_⟩
    have h := he (e.symm f) x
    rw [e.apply_symm_apply] at h
    exact h.symm

end StatLean.NonparametricStatistics
