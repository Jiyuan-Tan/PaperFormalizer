module
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section

/-!
# Uniform coercivity of a positive-definite finite matrix

This file isolates the finite-dimensional compactness step that upgrades strict
positivity of a real positive-definite matrix to a uniform lower quadratic bound.
It is independent of the statistical meaning of the matrix.
-/

open scoped RealInnerProductSpace

namespace Matrix.PosDef

/-- A real positive-definite matrix uniformly dominates the ambient Euclidean
norm squared.  For the zero-dimensional space the statement uses the harmless
constant `c = 1`; every vector is then zero. -/
lemma exists_inner_toEuclideanCLM_ge
    {d : ℕ} {I : Matrix (Fin d) (Fin d) ℝ}
    -- Strict positive definiteness of the finite matrix.
    (hI : I.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : EuclideanSpace ℝ (Fin d),
      c * ‖x‖ ^ 2 ≤
        ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) I x⟫ := by
  classical
  by_cases hd : d = 0
  · subst d
    refine ⟨1, zero_lt_one, fun x => ?_⟩
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  · let T := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) I
    let q : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ⟪x, T x⟫
    letI := FiniteDimensional.proper_rclike ℝ (EuclideanSpace ℝ (Fin d))
    have hq_cont : Continuous q := continuous_id.inner T.continuous
    have hq_pos : ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1, 0 < q x := by
      intro x hx
      have hx_ne : x ≠ 0 := by
        intro hx_zero
        simp [hx_zero] at hx
      have hx_ne' : x.1 ≠ 0 := by
        intro hx_zero
        apply hx_ne
        apply PiLp.ext
        intro i
        change x.1 i = 0
        rw [hx_zero]
        rfl
      change 0 < ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d) I x⟫
      rw [Matrix.inner_toEuclideanCLM]
      exact hI.dotProduct_mulVec_pos hx_ne'
    obtain ⟨c, hc, hc_sphere⟩ :=
      (isCompact_sphere (0 : EuclideanSpace ℝ (Fin d)) 1).exists_forall_le'
        hq_cont.continuousOn hq_pos
    refine ⟨c, hc, fun x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    have hx_norm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hx_unit : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hx_norm.ne']
    have hc_unit := hc_sphere (‖x‖⁻¹ • x) hx_unit
    have hscale : q (‖x‖⁻¹ • x) = q x / ‖x‖ ^ 2 := by
      simp only [q, map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
      field_simp
    rw [hscale] at hc_unit
    exact (le_div_iff₀ (sq_pos_of_pos hx_norm)).mp hc_unit

end Matrix.PosDef
