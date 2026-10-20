module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

namespace MeasureTheory

open scoped RealInnerProductSpace

/-!
# Auxiliary lemmas for Cramér-Wold argument

This file contains helper lemmas for the Cramér-Wold decomposition, connecting
positive semidefiniteness conditions with quadratic forms and the pushforward of
characteristic functions via inner products.
-/

section MatrixPosSemidef

variable {n : Type*} [Fintype n]

/-! Brick A: Equivalence between PosSemidef and nonnegative quadratic forms -/

/-- A Hermitian matrix is positive semidefinite iff its quadratic form is nonnegative. -/
theorem Matrix.PosSemidef_iff_quadratic_form_nonneg
    {A : Matrix n n ℝ} (hHerm : A.IsHermitian) :
    A.PosSemidef ↔ ∀ x : n → ℝ, 0 ≤ dotProduct (star x) (A.mulVec x) := by
  constructor
  · exact fun h _ ↦ h.dotProduct_mulVec_nonneg _
  · exact fun h ↦ Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm h

/-- A difference of Hermitian matrices is positive semidefinite iff the quadratic form
    of the first is at most that of the second. -/
theorem Matrix.sub_PosSemidef_iff_quadratic_form_le
    {G Sigma : Matrix n n ℝ}
    (hG_herm : G.IsHermitian) (hSigma_herm : Sigma.IsHermitian) :
    (Sigma - G).PosSemidef ↔
      ∀ x : n → ℝ, dotProduct (star x) (G.mulVec x) ≤ dotProduct (star x) (Sigma.mulVec x) := by
  rw [Matrix.PosSemidef_iff_quadratic_form_nonneg (hSigma_herm.sub hG_herm)]
  constructor
  · intro h x
    have key : dotProduct (star x) ((Sigma - G).mulVec x) = 
               dotProduct (star x) (Sigma.mulVec x) - dotProduct (star x) (G.mulVec x) := by
      simp only [Matrix.sub_mulVec, dotProduct_sub]
    linarith [h x]
  · intro h x
    have key : dotProduct (star x) ((Sigma - G).mulVec x) = 
               dotProduct (star x) (Sigma.mulVec x) - dotProduct (star x) (G.mulVec x) := by
      simp only [Matrix.sub_mulVec, dotProduct_sub]
    linarith [h x]

end MatrixPosSemidef

section CharFunInnerProduct

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [BorelSpace E]

/-! Brick B: Characteristic function of the pushforward via an inner product -/

/-- The characteristic function of the pushforward of μ via the inner product with a fixed vector v
    equals the characteristic function of μ at the scaled vector (t • v). -/
theorem charFun_map_inner_left (μ : Measure E) (v : E) (t : ℝ) :
    charFun (μ.map fun x => inner ℝ v x) t = charFun μ (t • v) := by
  let L := InnerProductSpace.toDualMap ℝ E v
  change charFun (μ.map fun x => inner ℝ v x) t = charFun μ (t • v)
  change charFun (μ.map fun x => (L : E → ℝ) x) t = charFun μ (t • v)
  rw [charFun_map_eq_charFunDual_smul L t]
  simp only [charFunDual_apply, charFun_apply]
  congr 1 with x
  change Complex.exp (↑((t • L) x) * Complex.I) = Complex.exp (↑(inner ℝ x (t • v)) * Complex.I)
  have rhs : inner ℝ x (t • v) = t * inner ℝ v x := by 
    rw [inner_smul_right, real_inner_comm]
  rw [show ((t • L) x : ℝ) = t * inner ℝ v x from rfl, rhs]

end CharFunInnerProduct

end MeasureTheory
