module
public import StatLean.AsymptoticStatistics.StrictModel.EfficientScore

@[expose] public section

/-!
# The symmetric location model and its location functional

The model-setup half of the concrete-EIF verification for **symmetric
location** (van der Vaart, *Asymptotic Statistics*, Example 25.27).

The model consists of all densities `x ↦ η(x − θ)` with `θ ∈ ℝ` and the
"shape" `η` symmetric about `0` with finite Fisher information for
location `I_η`. The observations are sampled from a density symmetric
about `θ`; the parameter of interest is the location `θ`, and the
nuisance is the shape `η`.

The entire structural content of Example 25.27 is encoded through the
`Core.Hilbert.L2ZeroMean` tangent-geometry:

* `P` — the base law (the density at `θ = 0`), a probability measure on
  `ℝ`;
* `score : ↥(L2ZeroMean P)` — the **location score** `-η'/η`, which is an
  **odd** element (a symmetric density has an asymmetric derivative);
* `T_nuis` — the nuisance tangent space, consisting of the **even**
  mean-zero functions (score functions for `η`, necessarily functions of
  `|x − θ|`);
* `R` — the reflection isometry `g ↦ g ∘ (·↦ −·)` of `↥(L2ZeroMean P)`,
  the Hilbert-space avatar of the symmetry of the model. Oddness of the
  score reads `R score = −score`; evenness of the nuisance scores reads
  `R g = g` for `g ∈ T_nuis`.

This file defines the ordinary score operator, the model tangent space,
the Fisher information, and the candidate influence function
`score / I_η`. Following van der Vaart's Example 25.27, the parameter of
interest is the **location functional** `ψ(P_{θ,η}) = θ` itself; it and
its pathwise differentiability (the path-existence content of vdV eq
(25.26)) are **not** given by an explicit formula here — on a general
symmetric family (e.g. Cauchy) there is no finite mean — but enter the
headline `symLoc_isEIF` as explicit hypotheses in the form of Lemma 25.25
form (a functional `ψ`, its `PathwiseDifferentiableAt` witness, and the
θ-coordinate identity that its derivative reads off the score
coefficient). The efficient-influence-function claim is then *derived*,
not assumed, via `StrictModel.EfficientScore.eif_from_efficientScore'`.

Reference: vdV §25.4, Example 25.27 (Symmetric location), p.369-370.

Headline declarations: `symLoc_ordinaryScore`, `symLoc_tangent`,
`symLoc_fisherInfo`, `symLoc_candidate`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Examples.SymmetricLocation

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.StrictModel.EfficientScore

variable {P : Measure ℝ} [IsProbabilityMeasure P]

/-- The **ordinary score operator** `S_θ : ℝ →L[ℝ] ↥(L²₀(P))`,
`v ↦ v • score`, sending the location direction `v` to `v` times the
location score `score = -η'/η`.

Reference: vdV §25.4 — the ordinary score for `θ` in the model with `η`
fixed. -/
noncomputable def symLoc_ordinaryScore (score : ↥(L2ZeroMean P)) :
    OrdinaryScore P ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ score

@[simp] lemma symLoc_ordinaryScore_one (score : ↥(L2ZeroMean P)) :
    symLoc_ordinaryScore score (1 : ℝ) = score :=
  ContinuousLinearMap.toSpanSingleton_apply_one ℝ score

@[simp] lemma symLoc_ordinaryScore_apply (score : ↥(L2ZeroMean P)) (v : ℝ) :
    symLoc_ordinaryScore score v = v • score :=
  ContinuousLinearMap.toSpanSingleton_apply ℝ score v

/-- The **model tangent space** `T = lin(score) + T_nuis`: the span of the
location score together with the nuisance tangent space.

Reference: vdV §25.4, p.368 — the tangent set
`Ṗ_{P_{θ,η}} = lin(score_θ) + η̇Ṗ`. -/
noncomputable def symLoc_tangent (score : ↥(L2ZeroMean P))
    (T_nuis : Submodule ℝ ↥(L2ZeroMean P)) :
    Submodule ℝ ↥(L2ZeroMean P) :=
  (ℝ ∙ score) ⊔ T_nuis

/-- The **Fisher information for location** `I_η = P score²`, realised as the
squared `L²(P)`-norm of the location score (the score has mean zero, so
`E[score²] = ‖score‖²`).

Reference: vdV Example 25.27 — the finite Fisher information `I_η`. -/
noncomputable def symLoc_fisherInfo (score : ↥(L2ZeroMean P)) : ℝ := ‖score‖ ^ 2

/-- The **candidate efficient influence function** `φ = score / I_η`.

Reference: vdV Example 25.27 — the efficient influence function is
`ℓ̃_θ / Ĩ_θ = score_θ / I_η`, since (by the odd/even orthogonality) the
efficient score coincides with the ordinary score. -/
noncomputable def symLoc_candidate (score : ↥(L2ZeroMean P)) :
    ↥(L2ZeroMean P) :=
  (1 / symLoc_fisherInfo score) • score

end AsymptoticStatistics.Examples.SymmetricLocation
