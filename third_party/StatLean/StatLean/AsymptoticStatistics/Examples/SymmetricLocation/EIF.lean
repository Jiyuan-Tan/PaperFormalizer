module
public import StatLean.AsymptoticStatistics.Examples.SymmetricLocation.Model

@[expose] public section

/-!
# Efficient influence function for the symmetric location model

The efficient-influence-function results for the symmetric-location example
(van der Vaart, *Asymptotic Statistics*, Example 25.27).

The headline `symLoc_isEIF` states that the candidate
`φ = score / I_η` is the efficient influence function for the location
functional in the symmetric location model. The surprising content of
Example 25.27 (Stein, 1956) is that the **efficient score coincides with
the ordinary score**: because the location score `score = -η'/η` is *odd*
and every nuisance score is *even* (a function of `|x − θ|`), the
projection of the ordinary score onto the nuisance tangent space is
zero. This is proved as `symLoc_efficientScore_eq_score` using the
reflection isometry `R`.

The EIF claim is derived by `symLoc_isEIF` using the derived form of
van der Vaart's Lemma 25.25,
`StrictModel.EfficientScore.eif_from_efficientScore'`, whose hypotheses
are all discharged here from the Stein orthogonality
(`symLoc_starProjection_eq_zero`). The derivative in the conclusion is
`hpd.derivative`, the pathwise derivative of the
location functional `ψ`; the influence-function identity
`⟪φ, g⟫ = ψ̇(g)` follows from the efficient-score projection algebra. The
theorem takes as model assumptions the symmetry conditions
(`R`, `hℓ_odd`, `hR_fix`), nonsingularity of the
Fisher information (`hI_pos`), and the location functional together with its
pathwise differentiability (`ψ`, `hpd`, `h_deriv_eq` — vdV eq (25.26),
Lemma 25.25).

Reference: vdV §25.4, Example 25.27, p.369-370; Lemma 25.25, p.368-369.

Headline declaration: `symLoc_isEIF`.
-/

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Examples.SymmetricLocation

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.StrictModel.EfficientScore

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- *Odd score ⊥ even nuisance (Example 25.27).* The location
score `score` is orthogonal to the whole nuisance tangent space `T_nuis`.

Proof: `R` is a linear isometry (it preserves the inner product), the
score is odd (`R score = -score`) and every nuisance direction is even
(`R g = g`). Hence for `g ∈ T_nuis`,
`⟪g, score⟫ = ⟪R g, R score⟫ = ⟪g, -score⟫ = -⟪g, score⟫`, forcing `⟪g, score⟫ = 0`.

This is the Lean avatar of vdV's `E_{θ,η}[-η'/η (X−θ) · b(|X−θ|)] = 0`
(a symmetric density has an asymmetric derivative). -/
theorem symLoc_score_orthogonal_nuisance (score : ↥(L2ZeroMean P))
    (T_nuis : Submodule ℝ ↥(L2ZeroMean P))
    (R : ↥(L2ZeroMean P) ≃ₗᵢ[ℝ] ↥(L2ZeroMean P))
    (hℓ_odd : R score = -score)
    (hR_fix : ∀ g ∈ T_nuis, R g = g) :
    score ∈ T_nuisᗮ := by
  rw [Submodule.mem_orthogonal]
  intro g hg
  have key : ⟪g, score⟫_ℝ = ⟪R g, R score⟫_ℝ := (R.inner_map_map g score).symm
  rw [hR_fix g hg, hℓ_odd, inner_neg_right] at key
  linarith

/-- The orthogonal projection of the location score onto the nuisance
tangent space is zero (immediate from
`symLoc_score_orthogonal_nuisance`). -/
theorem symLoc_starProjection_eq_zero (score : ↥(L2ZeroMean P))
    (T_nuis : Submodule ℝ ↥(L2ZeroMean P)) [T_nuis.HasOrthogonalProjection]
    (R : ↥(L2ZeroMean P) ≃ₗᵢ[ℝ] ↥(L2ZeroMean P))
    (hℓ_odd : R score = -score)
    (hR_fix : ∀ g ∈ T_nuis, R g = g) :
    T_nuis.starProjection score = 0 := by
  have h := symLoc_score_orthogonal_nuisance score T_nuis R hℓ_odd hR_fix
  exact Submodule.eq_starProjection_of_mem_orthogonal' (Submodule.zero_mem _) h
    (by rw [zero_add])

/-- *Efficient score = ordinary score (Example 25.27 — Stein, 1956).*
The efficient score for `θ` equals the ordinary location score `score`,
because the nuisance projection vanishes. -/
theorem symLoc_efficientScore_eq_score (score : ↥(L2ZeroMean P))
    (T_nuis : Submodule ℝ ↥(L2ZeroMean P)) [T_nuis.HasOrthogonalProjection]
    (R : ↥(L2ZeroMean P) ≃ₗᵢ[ℝ] ↥(L2ZeroMean P))
    (hℓ_odd : R score = -score)
    (hR_fix : ∀ g ∈ T_nuis, R g = g) :
    efficientScore (symLoc_ordinaryScore score) T_nuis 1 = score := by
  rw [efficientScore, symLoc_ordinaryScore_one,
      symLoc_starProjection_eq_zero score T_nuis R hℓ_odd hR_fix, sub_zero]

/-- The efficient information equals the Fisher information `I_η = ‖score‖²`
(there is no information loss for the location under symmetry). -/
theorem symLoc_efficientInformation_eq_fisher (score : ↥(L2ZeroMean P))
    (T_nuis : Submodule ℝ ↥(L2ZeroMean P)) [T_nuis.HasOrthogonalProjection]
    (R : ↥(L2ZeroMean P) ≃ₗᵢ[ℝ] ↥(L2ZeroMean P))
    (hℓ_odd : R score = -score)
    (hR_fix : ∀ g ∈ T_nuis, R g = g) :
    efficientInformation (symLoc_ordinaryScore score) T_nuis 1 = symLoc_fisherInfo score := by
  rw [efficientInformation, symLoc_efficientScore_eq_score score T_nuis R hℓ_odd hR_fix,
      symLoc_fisherInfo]

/-- The normalized efficient score `(1/Ĩ) • ℓ̃` equals the concrete
candidate `φ = score / I_η`. -/
theorem symLoc_candidate_eq_eif (score : ↥(L2ZeroMean P))
    (T_nuis : Submodule ℝ ↥(L2ZeroMean P)) [T_nuis.HasOrthogonalProjection]
    (R : ↥(L2ZeroMean P) ≃ₗᵢ[ℝ] ↥(L2ZeroMean P))
    (hℓ_odd : R score = -score)
    (hR_fix : ∀ g ∈ T_nuis, R g = g) :
    (1 / efficientInformation (symLoc_ordinaryScore score) T_nuis 1)
        • efficientScore (symLoc_ordinaryScore score) T_nuis 1
      = symLoc_candidate score := by
  rw [symLoc_efficientInformation_eq_fisher score T_nuis R hℓ_odd hR_fix,
      symLoc_efficientScore_eq_score score T_nuis R hℓ_odd hR_fix, symLoc_candidate]

/-- Every tangent direction of `T = lin(score) ⊔ T_nuis` splits as
`u • score + g_nuis` with `g_nuis ∈ T_nuis`, i.e. as an ordinary-score
component plus a nuisance component. This is the book's tangent-set
structure `Ṗ_{P_{θ,η}} = lin(ℓ̇_θ) + η̇Ṗ` (vdV §25.4, p.368). -/
theorem symLoc_tangent_decomp (score : ↥(L2ZeroMean P))
    (T_nuis : Submodule ℝ ↥(L2ZeroMean P))
    (g : symLoc_tangent score T_nuis) :
    ∃ (u : ℝ) (g_nuis : ↥(L2ZeroMean P)),
      g_nuis ∈ T_nuis ∧
      (g : ↥(L2ZeroMean P)) = symLoc_ordinaryScore score u + g_nuis := by
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp g.2
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ha
  exact ⟨c, b, hb, by rw [symLoc_ordinaryScore_apply, hc, hab]⟩

/-- **Efficient influence function for the symmetric location model
(vdV Example 25.27).**

For the symmetric location model with location score `score` (odd, via the
reflection isometry `R`) and nuisance tangent space `T_nuis` (the even
mean-zero functions, `R`-fixed), the candidate `φ = score / I_η` is the
**efficient influence function** for the location functional `ψ`.

The theorem takes the following model data and regularity assumptions:

* `R`, `hℓ_odd`, `hR_fix` — the reflection symmetry of the model: the
  score is odd and the nuisance scores are even. These give Stein's
  orthogonality (`symLoc_starProjection_eq_zero`), hence `ℓ̃ = ℓ̇` and
  `Ĩ = I_η`.
* `hI_pos : 0 < I_η` — nonsingularity of the (efficient = Fisher)
  information, required by vdV Lemma 25.25 (p.369) for differentiability
  of the functional.
* `ψ`, `hpd`, `h_deriv_eq` — the location functional `ψ(P_{θ,η}) = θ`,
  its pathwise differentiability (the path-existence content of vdV eq
  (25.26)), and the identity that its derivative reads off the
  score-direction coefficient `u` (`ψ` is the θ-coordinate). Thus
  `h_deriv_eq` specifies the derivative on the score-coordinate
  decomposition used by Lemma 25.25.

The EIF is obtained by feeding these to
`eif_from_efficientScore'` (the derived form of vdV Lemma 25.25): its
`h_decomp`, `h_gram`, and membership obligations are discharged here from
the Stein orthogonality, and the influence-function identity is obtained
from the efficient-score projection algebra. The conclusion's derivative is
`hpd.derivative`, the pathwise derivative of `ψ`. -/
theorem symLoc_isEIF (score : ↥(L2ZeroMean P))
    (T_nuis : Submodule ℝ ↥(L2ZeroMean P)) [T_nuis.HasOrthogonalProjection]
    (R : ↥(L2ZeroMean P) ≃ₗᵢ[ℝ] ↥(L2ZeroMean P))
    (hℓ_odd : R score = -score)
    (hR_fix : ∀ g ∈ T_nuis, R g = g)
    -- vdV p.369: nonsingular (efficient = Fisher) information I_η
    (hI_pos : 0 < symLoc_fisherInfo score)
    -- vdV Ex 25.27 / Lem 25.25: the location functional ψ = θ, its pathwise
    -- differentiability (eq (25.26)), and the θ-coordinate identity
    (ψ : Measure ℝ → ℝ)
    (hpd : PathwiseDifferentiableAt P (symLoc_tangent score T_nuis) ψ)
    (h_deriv_eq : ∀ (u : ℝ) (g_nuis : ↥(L2ZeroMean P)) (_ : g_nuis ∈ T_nuis)
        (hmem : u • score + g_nuis ∈ symLoc_tangent score T_nuis),
        hpd.derivative ⟨u • score + g_nuis, hmem⟩ = u) :
    IsEfficientInfluenceFunction P (symLoc_tangent score T_nuis)
      hpd.derivative
      (symLoc_candidate score) := by
  rw [← symLoc_candidate_eq_eif score T_nuis R hℓ_odd hR_fix]
  refine eif_from_efficientScore' (symLoc_ordinaryScore score) T_nuis 1
    (symLoc_tangent score T_nuis) ψ hpd
    (fun g => symLoc_tangent_decomp score T_nuis g) ?_ ?_ ?_ ?_
  · -- h_deriv_eq: derivative reads off u = ⟪(1 : ℝ), u⟫_ℝ
    intro u g_nuis hg_nuis hmem
    -- `symLoc_ordinaryScore score u` is definitionally equal to `u • score`, so
    -- `h_deriv_eq` (stated with `u • score`) matches the goal's subtype.
    have hval : hpd.derivative ⟨symLoc_ordinaryScore score u + g_nuis, hmem⟩ = u :=
      h_deriv_eq u g_nuis hg_nuis hmem
    rw [hval]
    -- `⟪(1 : ℝ), u⟫_ℝ = u`
    change u = u * 1
    rw [mul_one]
  · -- h_gram: ⟪ℓ̃(1), ℓ̃(u)⟫ = Ĩ · ⟪(1 : ℝ), u⟫
    intro u
    -- `ℓ̃(u) = u • ℓ̃(1) = u • score` (homogeneity + Stein `ℓ̃ = score`).
    have key : efficientScore (symLoc_ordinaryScore score) T_nuis u = u • score := by
      have h1 := efficientScore_smul (symLoc_ordinaryScore score) T_nuis u (1 : ℝ)
      rw [smul_eq_mul, mul_one] at h1
      rw [h1, symLoc_efficientScore_eq_score score T_nuis R hℓ_odd hR_fix]
    rw [key, symLoc_efficientScore_eq_score score T_nuis R hℓ_odd hR_fix,
        symLoc_efficientInformation_eq_fisher score T_nuis R hℓ_odd hR_fix,
        real_inner_smul_right, symLoc_fisherInfo, real_inner_self_eq_norm_sq]
    change u * ‖score‖ ^ 2 = ‖score‖ ^ 2 * (u * 1)
    ring
  · -- hI_pos: 0 < efficientInformation
    rw [symLoc_efficientInformation_eq_fisher score T_nuis R hℓ_odd hR_fix]
    exact hI_pos
  · -- membership: (1/Ĩ) • ℓ̃ = φ ∈ lin(score) ⊆ T
    rw [symLoc_candidate_eq_eif score T_nuis R hℓ_odd hR_fix, symLoc_candidate,
        symLoc_tangent]
    exact Submodule.mem_sup_left
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self score))

end AsymptoticStatistics.Examples.SymmetricLocation
