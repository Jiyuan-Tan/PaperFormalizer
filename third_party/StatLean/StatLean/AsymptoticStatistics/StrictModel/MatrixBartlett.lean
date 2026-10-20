module
public import StatLean.AsymptoticStatistics.ParametricFamily.BartlettIdentity
public import StatLean.AsymptoticStatistics.StrictModel.EfficientScoreVec

@[expose] public section

/-!
# Matrix Bartlett identity: `E_P[∂_k ℓ̃_j] = − Ĩ`

The **matrix / information Bartlett identity** for the efficient information matrix `Ĩ`.
Its `(j,k)` entry is the *off-diagonal* second Bartlett identity in polarized form,
`E_P[∂_k ℓ̃_j] = − ∫ ℓ̃_j · ℓ̃_k dP = − Ĩ_{jk}`, one per pair of parameter directions
`(e_j, e_k)`. Assembling the `d²` scalar identities (each certified by the already-closed
concept brick `AsymptoticStatistics.ParametricFamily.DifferentiableScoreSubmodel.bartlett_identity`)
against `efficientInformationMatrix_apply` yields the full matrix statement

  `(Matrix.of fun j k => ∫ (∂_k ℓ̃_j) dP) = − Ĩ`,

with `Ĩ` the efficient information matrix `Ĩ_{jk} = ⟪ℓ̃(e_j), ℓ̃(e_k)⟫`.

All the analytic content (differentiating `∫ f_θ p_θ dμ = 0` under the integral sign) lives
inside `bartlett_identity`; this file is pure entrywise assembly. The hypothesis `h_match`
is the honest matching claim that the `d²` supplied score submodels realize the efficient
scores `ℓ̃(e_j), ℓ̃(e_k)` — i.e. that `∫ f₀ · k₀ dP` for submodel `(j,k)` equals
`⟪ℓ̃(e_j), ℓ̃(e_k)⟫`. It is discharged later by concrete submodel constructions.

Reference: vdV §25.4 (efficient information matrix `Ĩ` and the matrix Bartlett identity);
§5.3 / §7.2 (the underlying second Bartlett / information identity).

Headline: `matrixBartlett_eq_neg_information` (matrix form), `matrixBartlett_entry`
(the `(j,k)`-entry corollary).
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.StrictModel.MatrixBartlett

open AsymptoticStatistics.ParametricFamily
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.StrictModel.EfficientScoreVec

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
  [CompleteSpace Θ]
variable {d : ℕ}

/-- **Matrix Bartlett / information identity.**

`(Matrix.of fun j k => ∫ (∂_k ℓ̃_j) dP) = − Ĩ`, where `Ĩ = efficientInformationMatrix`
is the `d × d` efficient information matrix `Ĩ_{jk} = ⟪ℓ̃(e_j), ℓ̃(e_k)⟫`.

Entrywise application of the polarized second Bartlett identity
(`DifferentiableScoreSubmodel.bartlett_identity`) over the
`d²` supplied score submodels `M j k`. The matching hypothesis `h_match` records that the
`(j,k)` submodel's density-weighted score product `∫ f₀ · k₀ dP` realizes the efficient
inner product `⟪ℓ̃(e_j), ℓ̃(e_k)⟫`; all analytic content is inside `bartlett_identity`.

Reference: vdV §25.4 (matrix Bartlett / efficient information matrix); §5.3 / §7.2
(second Bartlett / information identity). -/
theorem matrixBartlett_eq_neg_information
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (e : Fin d → Θ)
    (M : Fin d → Fin d → DifferentiableScoreSubmodel P)
    (h_match : ∀ j k, ∫ ω, (M j k).scoreCurve 0 ω * (M j k).densityScore ω ∂P
                = ⟪efficientScore S_θ T_nuis (e j), efficientScore S_θ T_nuis (e k)⟫_ℝ) :
    (Matrix.of (fun j k => ∫ ω, (M j k).scoreDot ω ∂P))
      = - efficientInformationMatrix S_θ T_nuis e := by
  ext j k
  rw [Matrix.of_apply, (M j k).bartlett_identity, h_match j k, Matrix.neg_apply,
      efficientInformationMatrix_apply]

/-- The `(j,k)`-entry form of the matrix Bartlett identity:
`∫ (∂_k ℓ̃_j) dP = − Ĩ_{jk}`. This form applies directly to the matrix-coupled
vector EIF `Ĩ⁻¹ ℓ̃`. -/
theorem matrixBartlett_entry
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (e : Fin d → Θ)
    (M : Fin d → Fin d → DifferentiableScoreSubmodel P)
    (h_match : ∀ j k, ∫ ω, (M j k).scoreCurve 0 ω * (M j k).densityScore ω ∂P
                = ⟪efficientScore S_θ T_nuis (e j), efficientScore S_θ T_nuis (e k)⟫_ℝ)
    (j k : Fin d) :
    ∫ ω, (M j k).scoreDot ω ∂P = - efficientInformationMatrix S_θ T_nuis e j k := by
  rw [(M j k).bartlett_identity, h_match j k, efficientInformationMatrix_apply]

/-- The identity `∫ score_l_dot j k dP = − Ĩ_{jk}` follows from differentiable
score submodels. Given submodels `M j k`
whose density-weighted score products realize the efficient inner products (`h_match`, the
matching condition) and whose score derivatives `(M j k).scoreDot` `P`-a.e. agree with
the matrix entries `score_l_dot j k` (`h_id`), the identity follows from
`matrixBartlett_entry`, the polarized second Bartlett identity
`DifferentiableScoreSubmodel.bartlett_identity`, obtained by differentiating
`∫ ℓ̃_θ p_θ = 0` under the integral.

Reference: vdV §25.4 (matrix Bartlett / information identity). -/
theorem matrix_bartlett_of_submodels
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (e : Fin d → Θ)
    (score_l_dot : Matrix (Fin d) (Fin d) (Lp ℝ 2 P))
    (M : Fin d → Fin d → DifferentiableScoreSubmodel P)
    (h_match : ∀ j k, ∫ ω, (M j k).scoreCurve 0 ω * (M j k).densityScore ω ∂P
                = ⟪efficientScore S_θ T_nuis (e j), efficientScore S_θ T_nuis (e k)⟫_ℝ)
    (h_id : ∀ j k, (fun ω => (M j k).scoreDot ω)
                =ᵐ[P] (fun ω => ((score_l_dot j k : Ω → ℝ)) ω)) :
    ∀ j k, ∫ ω, ((score_l_dot j k : Ω → ℝ)) ω ∂P
      = - efficientInformationMatrix S_θ T_nuis e j k := by
  intro j k
  rw [← integral_congr_ae (h_id j k)]
  exact matrixBartlett_entry S_θ T_nuis e M h_match j k

end AsymptoticStatistics.StrictModel.MatrixBartlett
