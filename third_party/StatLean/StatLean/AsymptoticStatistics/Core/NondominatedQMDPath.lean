module
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import StatLean.AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic

@[expose] public section

/-! # Nondominated one-sided QMD paths -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.Core.NondominatedQMDPath

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.ForMathlib.PairwiseQMDAnalytic

set_option linter.dupNamespace false

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A one-sided QMD path at `P` in the canonical pairwise sense of (25.13).

Constitutive (vdV §25.3 pp.362--363): a path consists of probability laws through
`P`, its `L²₀(P)` score, and the right-sided quadratic-mean derivative.  No
fixed common dominator is part of the object. -/
structure NondominatedQMDPath (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- Constitutive (vdV §25.3 p.362): the one-sided measure-valued path. -/
  curve : ℝ → Measure Ω
  /-- Constitutive (vdV §25.3 p.362): the path passes through `P`. -/
  curve_at_zero : curve 0 = P
  /-- Constitutive (vdV §25.3 p.362): every nonnegative point of the
  one-sided path is a probability law in the model. The definition imposes no
  condition at negative parameters. -/
  curve_isProbability : ∀ t, 0 ≤ t → IsProbabilityMeasure (curve t)
  /-- Constitutive (vdV §25.3 p.362): the QMD score, after Lemma 25.14's
  analytic conclusion has placed it in `L²₀(P)`. -/
  score : ↥(L2ZeroMean P)
  /-- Constitutive (vdV §25.3 eq.25.13): right pairwise QMD at zero. -/
  qmd_limit : IsRightQMD P curve (score : Ω → ℝ)

/-- The canonical pairwise QMD path, with no fixed common dominator. -/
abbrev PairwiseQMDPath {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] := NondominatedQMDPath P

/-- Package bare one-sided QMD data after the analytic score theorem.

The construction applies `rightQMD_score_in_L2ZeroMean` and transports the QMD
residual across its `P`-a.e. score representative. -/
theorem exists_nondominatedQMDPath_of_bare_qmd
    (P : Measure Ω) [IsProbabilityMeasure P]
    (curve : ℝ → Measure Ω)
    (hprob : ∀ t, 0 ≤ t → IsProbabilityMeasure (curve t))
    (hzero : curve 0 = P) (g : Ω → ℝ) (hg : Measurable g)
    (hqmd : IsRightQMD P curve g) :
    ∃ γ : NondominatedQMDPath P,
      γ.curve = curve ∧ g =ᵐ[P] (γ.score : Ω → ℝ) := by
  obtain ⟨g', hgg'⟩ := rightQMD_score_in_L2ZeroMean P curve hprob hzero g hg hqmd
  have hqmd' : IsRightQMD P curve (g' : Ω → ℝ) := by
    apply hqmd.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    let ν := canonicalDominator P (curve t)
    letI : IsProbabilityMeasure (curve t) := hprob t ht.le
    letI : IsFiniteMeasure ν := by
      dsimp [ν, canonicalDominator]
      infer_instance
    have hPν : P ≪ ν :=
      Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
    have hwith : g =ᵐ[ν.withDensity (P.rnDeriv ν)] (g' : Ω → ℝ) := by
      rw [Measure.withDensity_rnDeriv_eq P ν hPν]
      exact hgg'
    have hae : residualAgainst P (curve t) ν g t =ᵐ[ν]
        residualAgainst P (curve t) ν (g' : Ω → ℝ) t := by
      have hon := (ae_withDensity_iff (Measure.measurable_rnDeriv P ν)).mp hwith
      filter_upwards [hon] with ω hω
      by_cases hz : P.rnDeriv ν ω = 0
      · simp [residualAgainst, hz]
      · simp [residualAgainst, hω hz]
    change eLpNorm (residualAgainst P (curve t) ν g t) 2 ν / ENNReal.ofReal t = _
    rw [eLpNorm_congr_ae hae]
  exact ⟨{
    curve := curve
    curve_at_zero := hzero
    curve_isProbability := hprob
    score := g'
    qmd_limit := hqmd' }, rfl, hgg'⟩

namespace QMDPath

/-- A common-dominator, two-sided `QMDPath` determines a one-sided
nondominated path. The converse requires additional left-QMD and
common-domination hypotheses. -/
noncomputable def toNondominatedQMDPath
    {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P) :
    NondominatedQMDPath P where
  curve := γ.curve
  curve_at_zero := γ.curve_at_zero
  curve_isProbability := fun t _ => γ.curve_isProbability t
  score := γ.score
  qmd_limit := by
    have hfilter : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ 𝓝[≠] (0 : ℝ) := by
      apply nhdsWithin_mono
      intro t ht
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht.ne'
    have hlegacy := γ.qmd_limit.mono_left hfilter
    apply hlegacy.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    haveI : IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability t
    letI : IsProbabilityMeasure (γ.curve 0) := γ.curve_isProbability 0
    have hnorm := eLpNorm_residualAgainst_change_dominator
      (γ.curve 0) (γ.curve t) γ.dominating
      (γ.curve_absContinuous 0) (γ.curve_absContinuous t)
      (γ.score : Ω → ℝ) t
    change eLpNorm (residualAgainst (γ.curve 0) (γ.curve t)
      γ.dominating (γ.score : Ω → ℝ) t) 2 γ.dominating /
        ENNReal.ofReal |t| =
      eLpNorm (residualAgainst P (γ.curve t)
        (canonicalDominator P (γ.curve t)) (γ.score : Ω → ℝ) t)
          2 (canonicalDominator P (γ.curve t)) / ENNReal.ofReal t
    rw [← hnorm, γ.curve_at_zero, abs_of_pos ht]

end QMDPath
end AsymptoticStatistics.Core.NondominatedQMDPath
