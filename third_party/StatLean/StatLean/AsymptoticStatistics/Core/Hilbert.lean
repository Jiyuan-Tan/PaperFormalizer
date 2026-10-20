module
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# Hilbert geometry wrappers

This file packages the vdV §25.2 Hilbert-space background (orthogonal projection,
Riesz representation, orthogonal decomposition) under the names the rest of the
library uses, and introduces the central object `L2ZeroMean P`: the closed
submodule of mean-zero functions in `Lp ℝ 2 P`.

Headline declarations: `L2ZeroMean`, `orthogonal_decomp`,
`mem_of_orthogonal_complement_zero`, `riesz_repr_exists_unique`.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Core.Hilbert

/-! ## The mean-zero `L²(P)` subspace -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The constant function `1` lifted to `Lp ℝ 2 P`. Available whenever `P` is a
finite (in particular probability) measure. -/
noncomputable def oneL2 (P : Measure Ω) [IsFiniteMeasure P] : Lp ℝ 2 P :=
  (memLp_const (1 : ℝ)).toLp _

/-- The integral functional `f ↦ ∫ f ∂P` as a continuous linear functional on
`Lp ℝ 2 P`, realised as the inner product against the constant `1`. The
identification `integralL2 P f = ∫ f ∂P` is left for downstream lemmas. -/
noncomputable def integralL2 (P : Measure Ω) [IsFiniteMeasure P] :
    Lp ℝ 2 P →L[ℝ] ℝ :=
  innerSL ℝ (oneL2 P)

/-- The closed submodule of mean-zero `L²(P)` functions: the kernel of the
integral functional `integralL2 P`. -/
noncomputable def L2ZeroMean (P : Measure Ω) [IsFiniteMeasure P] :
    Submodule ℝ (Lp ℝ 2 P) :=
  LinearMap.ker (integralL2 P).toLinearMap

lemma L2ZeroMean_isClosed (P : Measure Ω) [IsFiniteMeasure P] :
    IsClosed (L2ZeroMean P : Set (Lp ℝ 2 P)) :=
  (integralL2 P).isClosed_ker

/-! ## Wrappers around Mathlib's Hilbert geometry -/

section Hilbert

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Specification of the orthogonal projection onto a submodule with an
orthogonal projection: the projection lies in `K`, and the residual is
orthogonal to `K`. -/
theorem orthogonalProjection_spec
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] (x : E) :
    K.starProjection x ∈ K ∧ x - K.starProjection x ∈ Kᗮ :=
  ⟨K.starProjection_apply_mem x, K.sub_starProjection_mem_orthogonal x⟩

/-- Orthogonal decomposition: a submodule with an orthogonal projection
together with its orthogonal complement spans the whole space, and they are
disjoint. -/
theorem orthogonal_decomp
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    K ⊔ Kᗮ = ⊤ ∧ K ⊓ Kᗮ = ⊥ :=
  ⟨K.sup_orthogonal_of_hasOrthogonalProjection,
    K.inf_orthogonal_eq_bot⟩

variable [CompleteSpace E]

/-- Membership in a closed submodule via orthogonality to the orthogonal complement.

For a closed submodule `K` in a complete inner product space, `Kᗮᗮ = K`, so
`x ∈ K` iff `x` is orthogonal to every element of `Kᗮ`. -/
theorem mem_of_orthogonal_complement_zero
    (K : Submodule 𝕜 E) (hK : IsClosed (K : Set E)) (x : E) :
    x ∈ K ↔ ∀ y ∈ Kᗮ, ⟪y, x⟫_𝕜 = 0 := by
  have hKK : Kᗮᗮ = K := by
    rw [K.orthogonal_orthogonal_eq_closure, hK.submodule_topologicalClosure_eq]
  conv_lhs => rw [← hKK]
  exact Submodule.mem_orthogonal (K := Kᗮ) x

/-- Fréchet–Riesz representation: every continuous linear functional on a Hilbert
space is uniquely the inner product against some vector. -/
theorem riesz_repr_exists_unique (φ : E →L[𝕜] 𝕜) :
    ∃! v : E, ∀ x, φ x = ⟪v, x⟫_𝕜 := by
  refine ⟨(InnerProductSpace.toDual 𝕜 E).symm φ, ?_, ?_⟩
  · intro x
    have hsym : (InnerProductSpace.toDual 𝕜 E)
        ((InnerProductSpace.toDual 𝕜 E).symm φ) = φ :=
      LinearIsometryEquiv.apply_symm_apply _ _
    calc
      φ x = (InnerProductSpace.toDual 𝕜 E)
              ((InnerProductSpace.toDual 𝕜 E).symm φ) x := by rw [hsym]
      _ = ⟪(InnerProductSpace.toDual 𝕜 E).symm φ, x⟫_𝕜 := rfl
  · intro v hv
    apply (InnerProductSpace.toDual 𝕜 E).injective
    ext x
    have hsym : (InnerProductSpace.toDual 𝕜 E)
        ((InnerProductSpace.toDual 𝕜 E).symm φ) = φ :=
      LinearIsometryEquiv.apply_symm_apply _ _
    calc
      (InnerProductSpace.toDual 𝕜 E) v x = ⟪v, x⟫_𝕜 := rfl
      _ = φ x := (hv x).symm
      _ = (InnerProductSpace.toDual 𝕜 E)
            ((InnerProductSpace.toDual 𝕜 E).symm φ) x := by rw [hsym]

end Hilbert

end AsymptoticStatistics.Core.Hilbert
