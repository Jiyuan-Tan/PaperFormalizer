module
public import StatLean.AsymptoticStatistics.StrictModel.EfficientScore
public import StatLean.AsymptoticStatistics.Core.EIFVec
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
# Efficient information matrix and vector EIF for strict `(θ, η)` models

Vector-parameter (`θ ∈ ℝᵈ`) counterpart of the scalar
`AsymptoticStatistics.StrictModel.EfficientScore` layer. For a tuple of
parameter directions `e : Fin d → Θ` we form:

* `efficientInformationMatrix S_θ T_nuis e` — the `d × d` *efficient
  information matrix* `Ĩᵢⱼ = ⟪ℓ̃(eᵢ), ℓ̃(eⱼ)⟫`, realized as the Gram
  matrix `Matrix.gram ℝ (fun j => efficientScore S_θ T_nuis (e j))`
  (positive-semidefinite by `Matrix.posSemidef_gram`);
* `eif_from_efficientScore_vec` — under `Ĩ.PosDef` (hence invertible by
  `Matrix.PosDef.isUnit`), the vector EIF
  `IF j = ∑ₖ (Ĩ⁻¹)ⱼₖ • ℓ̃(eₖ)` is a vector efficient influence function
  (`IsEfficientInfluenceFunction_vec`) for a vector derivative `Dψ`.

This generalizes the scalar `efficientInformation` (its single diagonal
entry) and `eif_from_efficientScore` (the `d = 1` slice). The layer is
**additive**: the scalar declarations are unchanged.

Reference: vdV §25.4, lem:25.25 — the `k`-dim form
`EIF = Ĩ⁻¹ ℓ̃` with `Ĩ` the efficient information matrix.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.StrictModel.EfficientScoreVec

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EIF
open AsymptoticStatistics.Core.EIFVec
open AsymptoticStatistics.StrictModel.EfficientScore

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
  [CompleteSpace Θ]
variable {d : ℕ}

/-- *Efficient information matrix* for the parameter directions
`e : Fin d → Θ`: the `d × d` Gram matrix
`Ĩᵢⱼ = ⟪ℓ̃(eᵢ), ℓ̃(eⱼ)⟫` of the efficient scores.

`efficientInformationMatrix S_θ T_nuis e :=
  Matrix.gram ℝ (fun j => efficientScore S_θ T_nuis (e j))`.

Reference: vdV §25.4. This is the matrix generalization of the scalar
`efficientInformation` (the `(i,i)` diagonal entry is
`‖ℓ̃(eᵢ)‖² = efficientInformation S_θ T_nuis (e i)`). -/
noncomputable def efficientInformationMatrix
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection]
    (e : Fin d → Θ) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.gram ℝ (fun j => efficientScore S_θ T_nuis (e j))

/-- The efficient information matrix is positive-semidefinite (it is a
Gram matrix).

Reference: vdV §25.4 — `Ĩ ⪰ 0` always; positive-definiteness is the
non-degeneracy (identifiability) condition. -/
theorem efficientInformationMatrix_posSemidef
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection]
    (e : Fin d → Θ) :
    (efficientInformationMatrix S_θ T_nuis e).PosSemidef :=
  Matrix.posSemidef_gram ℝ _

/-- The `(i, j)` entry of the efficient information matrix is the inner
product of the corresponding efficient scores. -/
theorem efficientInformationMatrix_apply
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection]
    (e : Fin d → Θ) (i j : Fin d) :
    efficientInformationMatrix S_θ T_nuis e i j
      = ⟪efficientScore S_θ T_nuis (e i),
          efficientScore S_θ T_nuis (e j)⟫_ℝ := by
  rw [efficientInformationMatrix, Matrix.gram_apply]

/-- A positive-definite efficient information matrix is invertible.

Reference: vdV §25.4, p.369 — non-singularity of `Ĩ` is the
identifiability condition needed to form `Ĩ⁻¹`. -/
theorem efficientInformationMatrix_isUnit_of_posDef
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection]
    {e : Fin d → Θ}
    (hPD : (efficientInformationMatrix S_θ T_nuis e).PosDef) :
    IsUnit (efficientInformationMatrix S_θ T_nuis e) :=
  hPD.isUnit

/-- The candidate vector EIF tuple built from the efficient scores and
the inverse efficient information matrix:
`IF j = ∑ₖ (Ĩ⁻¹)ⱼₖ • ℓ̃(eₖ)`.

Reference: vdV §25.4, lem:25.25 — the `k`-dim EIF `Ĩ⁻¹ ℓ̃`. -/
noncomputable def candidateVecEIF
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection]
    (e : Fin d → Θ) (j : Fin d) : ↥(L2ZeroMean P) :=
  ∑ k, (efficientInformationMatrix S_θ T_nuis e)⁻¹ j k
        • efficientScore S_θ T_nuis (e k)

/-- *vdV lem:25.25 (vector form).* Under a positive-definite efficient
information matrix, the tuple `IF j = ∑ₖ (Ĩ⁻¹)ⱼₖ • ℓ̃(eₖ)` is a vector
efficient influence function for a vector derivative
`Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d)`, provided each component lies in
`T` (`h_mem`) and the `j`-th coordinate functional of `Dψ` acts on `T`
as `⟪IF j, ·⟫` (`h_Dψ`).

This is the matrix generalization of the scalar `eif_from_efficientScore`:
it concludes `IsEfficientInfluenceFunction_vec` by checking each
coordinate `j` with `eif_from_efficientScore`. The `hPD` hypothesis
records non-degeneracy (used by callers to form `Ĩ⁻¹` and to discharge
`h_mem`/`h_Dψ`); it is consumed via `candidateVecEIF`'s dependence on the
inverse matrix.

Reference: vdV §25.4, lem:25.25 (k-dim form `EIF = Ĩ⁻¹ ℓ̃`). -/
theorem eif_from_efficientScore_vec
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection]
    (e : Fin d → Θ)
    (T : Submodule ℝ ↥(L2ZeroMean P))
    (Dψ : T →L[ℝ] EuclideanSpace ℝ (Fin d))
    (hPD : (efficientInformationMatrix S_θ T_nuis e).PosDef)
    (h_mem : ∀ j, candidateVecEIF S_θ T_nuis e j ∈ T)
    (h_Dψ : ∀ (j : Fin d) (g : T),
      (EuclideanSpace.proj j ∘L Dψ) g
        = ⟪candidateVecEIF S_θ T_nuis e j, (g : ↥(L2ZeroMean P))⟫_ℝ) :
    IsEfficientInfluenceFunction_vec Dψ
      (candidateVecEIF S_θ T_nuis e) := by
  -- `hPD` ⟹ `Ĩ` invertible (used by callers to discharge h_mem/h_Dψ).
  have _hUnit : IsUnit (efficientInformationMatrix S_θ T_nuis e) :=
    hPD.isUnit
  -- Check each coordinate via `eif_of_representation_and_membership`.
  intro j
  refine eif_of_representation_and_membership ?_ (h_mem j)
  intro g
  exact (h_Dψ j g).symm

end AsymptoticStatistics.StrictModel.EfficientScoreVec
