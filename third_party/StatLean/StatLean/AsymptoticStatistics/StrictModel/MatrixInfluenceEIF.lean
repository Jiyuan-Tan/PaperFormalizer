module
public import StatLean.AsymptoticStatistics.StrictModel.EfficientScoreVec
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

/-!
# Matrix-influence identities for the vector EIF

Pure-algebra, concept-layer companion to
`AsymptoticStatistics.StrictModel.EfficientScoreVec`. It records two
identities about the candidate vector EIF
`candidateVecEIF S_θ T_nuis e j = ∑ₖ (Ĩ⁻¹)ⱼₖ • ℓ̃(eₖ)`
built from the efficient scores and the inverse efficient information
matrix `Ĩ⁻¹`:

* `matrix_influence_eq_candidateVecEIF` — the sum
  `∑ₖ (Ĩ⁻¹)ⱼₖ • ℓ̃(eₖ)` *is* `candidateVecEIF` (a definitional
  restatement, exposed as a downstream rewrite target);
* `candidateVecEIF_information_collapse` — the genuine collapse:
  applying `Ĩ⁻¹` to the `Ĩ`-weighted efficient-score tuple recovers the
  plain efficient score,
  `∑ₖ (Ĩ⁻¹)ⱼₖ • (∑ₗ Ĩₖₗ • ℓ̃(eₗ)) = ℓ̃(eⱼ)`,
  because `Ĩ⁻¹ Ĩ = 1` (needs `Ĩ.PosDef` for invertibility).

Both are pure linear algebra over the real inner-product space
`↥(L2ZeroMean P)`; there is **no** measure theory here. They feed the
native multivariate discharge of the semiparametric linear
representation.

Reference: vdV §25.4, lem:25.25 (`EIF = Ĩ⁻¹ ℓ̃`).
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.StrictModel.MatrixInfluenceEIF

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EIF
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.StrictModel.EfficientScoreVec

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
  [CompleteSpace Θ]
variable {d : ℕ}

/-- The efficient-score sum `∑ₖ (Ĩ⁻¹)ⱼₖ • ℓ̃(eₖ)` is definitionally the
candidate vector EIF `candidateVecEIF S_θ T_nuis e j`. Stated explicitly
as the rewrite target consumed by the native discharge. -/
theorem matrix_influence_eq_candidateVecEIF
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (e : Fin d → Θ) (j : Fin d) :
    (∑ k, (efficientInformationMatrix S_θ T_nuis e)⁻¹ j k
        • efficientScore S_θ T_nuis (e k))
      = candidateVecEIF S_θ T_nuis e j := by
  rw [candidateVecEIF]

/-- **Information collapse for the vector EIF.** Applying the inverse
efficient information matrix `Ĩ⁻¹` to the `Ĩ`-weighted efficient-score
tuple recovers the plain efficient score:
`∑ₖ (Ĩ⁻¹)ⱼₖ • (∑ₗ Ĩₖₗ • ℓ̃(eₗ)) = ℓ̃(eⱼ)`.

Pure linear algebra: pull the scalars through the sums, swap the order,
and collapse `∑ₖ (Ĩ⁻¹)ⱼₖ Ĩₖₗ = (Ĩ⁻¹ Ĩ)ⱼₗ = δⱼₗ` via
`Matrix.nonsing_inv_mul` (invertibility from `Ĩ.PosDef`).

Reference: vdV §25.4, lem:25.25. -/
theorem candidateVecEIF_information_collapse
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (e : Fin d → Θ)
    (hPD : (efficientInformationMatrix S_θ T_nuis e).PosDef) (j : Fin d) :
    (∑ k, (efficientInformationMatrix S_θ T_nuis e)⁻¹ j k
        • (∑ l, efficientInformationMatrix S_θ T_nuis e k l
              • efficientScore S_θ T_nuis (e l)))
      = efficientScore S_θ T_nuis (e j) := by
  classical
  set Ĩ := efficientInformationMatrix S_θ T_nuis e with hIdef
  -- Coefficient collapse: `∑ₖ (Ĩ⁻¹)ⱼₖ Ĩₖₗ = δⱼₗ`.
  have hcoef : ∀ l, (∑ k, Ĩ⁻¹ j k * Ĩ k l) = (if j = l then (1 : ℝ) else 0) := by
    intro l
    have h1 : (∑ k, Ĩ⁻¹ j k * Ĩ k l) = (Ĩ⁻¹ * Ĩ) j l := (Matrix.mul_apply).symm
    rw [h1, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hPD.isUnit),
      Matrix.one_apply]
  calc
    (∑ k, Ĩ⁻¹ j k • (∑ l, Ĩ k l • efficientScore S_θ T_nuis (e l)))
        = ∑ l, (∑ k, Ĩ⁻¹ j k * Ĩ k l) • efficientScore S_θ T_nuis (e l) := by
          simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
          exact Finset.sum_comm
    _ = ∑ l, (if j = l then (1 : ℝ) else 0) • efficientScore S_θ T_nuis (e l) := by
          simp_rw [hcoef]
    _ = efficientScore S_θ T_nuis (e j) := by
          simp

end AsymptoticStatistics.StrictModel.MatrixInfluenceEIF
