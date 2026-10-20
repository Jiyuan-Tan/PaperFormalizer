module
public import StatLean.NonparametricStatistics.RKHS.Basic

@[expose] public section

/-!
# Closed subspaces of an RKHS are RKHSs

A closed subspace `H₀` of a scalar RKHS `H` on `X` is again an RKHS on `X` (evaluation
functionals stay bounded under restriction), and its kernel is the projection of the
ambient kernel: `K₀(x, y) = (P₀ k_y)(x) = ⟪P₀ k_y, k_x⟫`, where `P₀` is the orthogonal
projection onto `H₀`.  In particular `kernelFun H₀ x = P₀ (kernelFun H x)`.

**Reference.** V. I. Paulsen and M. Raghupathi, *An Introduction to the Theory of Reproducing
Kernel Hilbert Spaces*, Cambridge Studies in Advanced Mathematics 152, Cambridge University Press,
2016. Chapter 2, §2.1, Theorem 2.5 (closed subspaces of an RKHS are RKHSs, with the projected
kernel).

**Proof formalization notes.** The subspace RKHS is an instance on the subtype `↥H₀` (`coeCLM`
composed with `Submodule.subtypeL`). The statements pass the `CompleteSpace ↥H₀` instance
*explicitly* (`@kernelFun 𝕜 _ X (↥H₀) _ _ hc _ x`): a bare typeclass-synthesized instance carries
a different (defeq but not instance-transparent) uniformity than the one recorded in
`RKHS.kerFun`'s signature, and unification bridges the two forms only at default transparency —
i.e. only under explicit application. The kernel identity itself is Riesz-uniqueness: both sides
have equal inner products against all of `H₀`
(`Submodule.eq_starProjection_of_mem_of_inner_eq_zero`).

**Bibliographic comments.** N. Aronszajn, Trans. Amer. Math. Soc. **68** (1950),
§I.9 (kernels of subspaces and differences of kernels).
-/

open RKHS ComplexConjugate
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

/-- A (complete, i.e. closed) subspace of an RKHS is an RKHS on the same set, with the
restricted evaluation. -/
noncomputable instance Submodule.instRKHS (H₀ : Submodule 𝕜 H) : RKHS 𝕜 H₀ X 𝕜 where
  coeCLM := (coeCLM 𝕜).comp H₀.subtypeL
  coeCLM_injective := by
    intro f g hfg
    exact Subtype.val_injective (RKHS.coeCLM_injective hfg)

/-- Evaluation in the subspace RKHS agrees with evaluation in the ambient space. -/
@[simp]
theorem coe_submodule_apply (H₀ : Submodule 𝕜 H) (f : H₀) (x : X) :
    f x = (f : H) x := rfl

/-- The kernel function of a closed subspace is the orthogonal projection of the ambient
kernel function: `kernelFun H₀ x = P₀ (kernelFun H x)`. -/
theorem kernelFun_submodule (H₀ : Submodule 𝕜 H) [hc : CompleteSpace H₀] (x : X) :
    ((@kernelFun 𝕜 _ X (↥H₀) _ _ hc _ x : ↥H₀) : H)
      = H₀.starProjection (kernelFun H x) := by
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero (SetLike.coe_mem _) ?_).symm
  intro w hw
  rw [inner_sub_left, inner_kernelFun]
  have h2 : ⟪((@kernelFun 𝕜 _ X (↥H₀) _ _ hc _ x : ↥H₀) : H), w⟫_𝕜 = w x := by
    rw [← H₀.coe_inner (@kernelFun 𝕜 _ X (↥H₀) _ _ hc _ x) ⟨w, hw⟩]
    exact @inner_kernelFun 𝕜 _ X (↥H₀) _ _ hc _ x ⟨w, hw⟩
  rw [h2, sub_self]

/-- **The kernel of a closed subspace**: `K₀(x, y) = (P₀ k_y)(x)`, the projected ambient
kernel function evaluated at the point. -/
theorem scalarKernel_submodule (H₀ : Submodule 𝕜 H) [hc : CompleteSpace H₀] (x y : X) :
    @scalarKernel 𝕜 _ X (↥H₀) _ _ hc _ x y
      = (H₀.starProjection (kernelFun H y)) x := by
  rw [← kernelFun_submodule H₀ y]
  rfl

/-- The kernel of a closed subspace as an inner product against the ambient kernel
function: `K₀(x, y) = ⟪k_x, P₀ k_y⟫`. -/
theorem scalarKernel_submodule_inner (H₀ : Submodule 𝕜 H) [hc : CompleteSpace H₀] (x y : X) :
    @scalarKernel 𝕜 _ X (↥H₀) _ _ hc _ x y
      = ⟪kernelFun H x, H₀.starProjection (kernelFun H y)⟫_𝕜 := by
  rw [scalarKernel_submodule H₀ x y, inner_kernelFun]

end StatLean.NonparametricStatistics
