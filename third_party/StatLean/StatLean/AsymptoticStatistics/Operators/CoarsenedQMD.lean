module
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import StatLean.AsymptoticStatistics.Operators.InformationLoss
public import StatLean.AsymptoticStatistics.Operators.CoarsenedQMDLimit

@[expose] public section

/-!
# Coarsening a QMD path through the observation map (vdV lem:25.34-I)

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.5.2,
lem:25.34(I), book p.375. **The book defers the proof of this preservation
to reference [139, pp.188-193].**

Given a full-data QMD path `γ : QMDPath P_full` and a measurable coarsening
`M : Ω_full → Ω_obs`, the pushed-forward curve `t ↦ (γ.curve t).map M` is again a
QMD path at `P_full.map M`, whose score is the information-loss image
`Π γ.score = E(γ.score | M⁻¹σ_obs)` of the full-data score (lem:25.34-I: taking a
conditional expectation of a QMD score produces the QMD score of the induced
coarsened path).

`QMDPath.coarsen` first replaces the dominating measure by an equivalent finite
measure. Its score is `Π γ.score`, and `coarsen_qmd_limit` proves the
score-preservation estimate that van der Vaart refers to [139] for.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

set_option linter.dupNamespace false

namespace AsymptoticStatistics.Core.QMDPath

open AsymptoticStatistics.Operators.InformationLoss

variable {Ω_full Ω_obs : Type*}
  [MeasurableSpace Ω_full] [MeasurableSpace Ω_obs]

/-- *Coarsening with an explicit mapped sigma-finiteness assumption.*

This form of vdV Lemma 25.34-I (book p.375) assumes that the mapped dominating
measure is sigma-finite.

Pushes a full-data QMD path `γ : QMDPath P_full` forward through a measurable
coarsening `M`, yielding a QMD path at `P_full.map M` with:
  * `curve t := (γ.curve t).map M` (the induced observed-data law),
  * `dominating := γ.dominating.map M`,
  * `score := informationLossOperator hM P_full γ.score = Π γ.score` (the
    conditional-expectation image of the full-data score — lem:25.34-I).

The probability, absolute-continuity, and base-point properties follow under
mapping.
  * `dominating_sigmaFinite` records the explicit
    `[SigmaFinite (γ.dominating.map M)]` assumption.
  * `qmd_limit` — the genuine score-preservation lem:25.34-I, which van der Vaart
    outsources to [139, pp.188-193] and which is proved here by
    `coarsen_qmd_limit_withMappedSigmaFinite`. -/
noncomputable def QMDPath.coarsenWithMappedSigmaFinite {M : Ω_full → Ω_obs}
    (hM : Measurable M)
    {P_full : Measure Ω_full} [IsProbabilityMeasure P_full]
    (γ : QMDPath P_full)
    -- σ-finiteness of the pushed-forward dominating
    -- measure on the observed space; not forced by the setup (pushforward of a
    -- σ-finite measure need not be σ-finite), so supplied explicitly.
    [hσ : SigmaFinite ((γ.dominating).map M)] :
    letI : IsProbabilityMeasure (P_full.map M) :=
      Measure.isProbabilityMeasure_map hM.aemeasurable
    QMDPath (P_full.map M) :=
  letI : IsProbabilityMeasure (P_full.map M) :=
    Measure.isProbabilityMeasure_map hM.aemeasurable
  { curve := fun t => (γ.curve t).map M
    curve_at_zero := by simp only [γ.curve_at_zero]
    curve_isProbability := fun t => by
      haveI := γ.curve_isProbability t
      exact Measure.isProbabilityMeasure_map hM.aemeasurable
    dominating := γ.dominating.map M
    curve_absContinuous := fun t => (γ.curve_absContinuous t).map hM
    -- The explicit `[SigmaFinite (γ.dominating.map M)]` hypothesis is needed because
    -- a pushforward of a σ-finite measure need not be σ-finite.
    dominating_sigmaFinite := hσ
    score := informationLossOperator hM P_full γ.score
    -- The score-preservation statement lem:25.34-I, attributed by vdV to
    -- [139, pp.188-193], follows from `coarsen_qmd_limit` via conditional-projection
    -- domination with λ=1
    -- (the pulled-back √-density residual splits into two `o(t)` L²(μ) brackets,
    -- bounded by conditional Cauchy–Schwarz on the QMD remainder plus a ρ-ratio
    -- DCT argument).
    qmd_limit := coarsen_qmd_limit_withMappedSigmaFinite hM γ }

/-- *Coarsening of a QMD path through the observation map* (vdV Lemma 25.34-I,
book p.375).

The dominating measure is replaced by the equivalent finite measure from
`finiteDominatorRepresentation`; its pushforward through `M` is finite and
hence sigma-finite. The resulting observed path has curve
`t ↦ (γ.curve t).map M` and score
`informationLossOperator hM P_full γ.score`. Thus no sigma-finiteness condition
on `γ.dominating.map M` is required in this statement. -/
noncomputable def QMDPath.coarsen {M : Ω_full → Ω_obs} (hM : Measurable M)
    {P_full : Measure Ω_full} [IsProbabilityMeasure P_full]
    (γ : QMDPath P_full) :
    letI : IsProbabilityMeasure (P_full.map M) :=
      Measure.isProbabilityMeasure_map hM.aemeasurable
    QMDPath (P_full.map M) := by
  let γfin := (finiteDominatorRepresentation γ).1
  have hcurve : γfin.curve = γ.curve := (finiteDominatorRepresentation γ).2.1
  have hdom : γfin.dominating = γ.dominating.toFinite :=
    (finiteDominatorRepresentation γ).2.2.1
  have hscore : γfin.score = γ.score := (finiteDominatorRepresentation γ).2.2.2
  haveI : SigmaFinite (γfin.dominating.map M) := by
    rw [hdom]
    infer_instance
  letI : IsProbabilityMeasure (P_full.map M) :=
    Measure.isProbabilityMeasure_map hM.aemeasurable
  let γmapped := QMDPath.coarsenWithMappedSigmaFinite hM γfin
  exact
    { curve := γmapped.curve
      curve_at_zero := γmapped.curve_at_zero
      curve_isProbability := γmapped.curve_isProbability
      dominating := γmapped.dominating
      curve_absContinuous := γmapped.curve_absContinuous
      dominating_sigmaFinite := γmapped.dominating_sigmaFinite
      score := γmapped.score
      qmd_limit := by
        simpa only [γmapped, QMDPath.coarsenWithMappedSigmaFinite, hcurve, hdom, hscore]
          using coarsen_qmd_limit hM γ }

end AsymptoticStatistics.Core.QMDPath
