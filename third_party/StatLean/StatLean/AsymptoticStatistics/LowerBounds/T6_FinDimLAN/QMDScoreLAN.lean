module
public import StatLean.AsymptoticStatistics.Core.QMDPath
public import StatLean.AsymptoticStatistics.LowerBounds.T6_FinDimLAN.Abstract1DLAN

@[expose] public section

/-!
# Bare QMD scores and the literal one-dimensional LAN expansion

This is the formulation of van der Vaart Lemma 25.14 that begins with a
measurable bare function and a genuine QMD limit; mean zero and square
integrability are conclusions. In contrast, `Core.QMDPath` assumes these
properties as part of the path data.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDScoreLAN

open AsymptoticStatistics.Core.Hilbert

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

/-- Bare QMD data whose score has zero mean determine a `QMDPath`.
The proof applies `Core.QMDPath.score_in_L2ZeroMean` and reuses the given
curve, base-point, absolute-continuity, and QMD properties. -/
theorem exists_qmdPath_of_bare_qmd
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Ω) [SigmaFinite μ]
    (curve : ℝ → Measure Ω)
    (h_prob : ∀ t, IsProbabilityMeasure (curve t))
    (h_zero : curve 0 = P)
    (h_ac : ∀ t, curve t ≪ μ)
    (g : Ω → ℝ) (hg_meas : Measurable g)
    (h_qmd :
      Tendsto
        (fun t : ℝ =>
          eLpNorm (fun ω : Ω =>
            Real.sqrt ((curve t).rnDeriv μ ω).toReal
              - Real.sqrt ((curve 0).rnDeriv μ ω).toReal
              - (t / 2) * g ω *
                  Real.sqrt ((curve 0).rnDeriv μ ω).toReal)
            2 μ / ENNReal.ofReal |t|)
        (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞))) :
    ∃ (γ : AsymptoticStatistics.Core.QMDPath.QMDPath P),
      γ.curve = curve ∧ γ.dominating = μ ∧
        g =ᵐ[P] (γ.score : Ω → ℝ) := by
  obtain ⟨g', hg'⟩ :=
    AsymptoticStatistics.Core.QMDPath.score_in_L2ZeroMean
      curve h_prob h_zero h_ac g hg_meas h_qmd
  have hP_ac : P ≪ μ := by
    rw [← h_zero]
    exact h_ac 0
  have hP_eq : μ.withDensity (P.rnDeriv μ) = P :=
    Measure.withDensity_rnDeriv_eq P μ hP_ac
  have hg'_withDensity :
      g =ᵐ[μ.withDensity (P.rnDeriv μ)] (g' : Ω → ℝ) := by
    rwa [hP_eq]
  have hg'_where_pos :
      ∀ᵐ ω ∂μ, P.rnDeriv μ ω ≠ 0 → g ω = (g' : Ω → ℝ) ω :=
    (ae_withDensity_iff (Measure.measurable_rnDeriv P μ)).mp hg'_withDensity
  have h_score_term :
      (fun ω => g ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal) =ᵐ[μ]
        fun ω => (g' : Ω → ℝ) ω *
          Real.sqrt ((curve 0).rnDeriv μ ω).toReal := by
    filter_upwards [hg'_where_pos] with ω hω
    rw [h_zero]
    by_cases hp : P.rnDeriv μ ω = 0
    · simp [hp]
    · rw [hω hp]
  have h_qmd' :
      Tendsto
        (fun t : ℝ =>
          eLpNorm (fun ω : Ω =>
            Real.sqrt ((curve t).rnDeriv μ ω).toReal
              - Real.sqrt ((curve 0).rnDeriv μ ω).toReal
              - (t / 2) * (g' : Ω → ℝ) ω *
                  Real.sqrt ((curve 0).rnDeriv μ ω).toReal)
            2 μ / ENNReal.ofReal |t|)
        (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds (0 : ℝ≥0∞)) := by
    convert h_qmd using 1
    funext t
    congr 1
    apply eLpNorm_congr_ae
    filter_upwards [h_score_term] with ω hω
    congr 1
    calc
      (t / 2) * (g' : Ω → ℝ) ω *
            Real.sqrt ((curve 0).rnDeriv μ ω).toReal
          = (t / 2) * ((g' : Ω → ℝ) ω *
              Real.sqrt ((curve 0).rnDeriv μ ω).toReal) := by ring
      _ = (t / 2) * (g ω *
              Real.sqrt ((curve 0).rnDeriv μ ω).toReal) := by rw [← hω]
      _ = (t / 2) * g ω *
            Real.sqrt ((curve 0).rnDeriv μ ω).toReal := by ring
  let γ : AsymptoticStatistics.Core.QMDPath.QMDPath P :=
    { curve := curve
      curve_at_zero := h_zero
      curve_isProbability := h_prob
      dominating := μ
      curve_absContinuous := h_ac
      dominating_sigmaFinite := inferInstance
      score := g'
      qmd_limit := h_qmd' }
  exact ⟨γ, rfl, rfl, hg'⟩

/-- Bare-data form of vdV Lemma 25.14 together with its literal LAN
consequence at local parameter `1/sqrt n`.

Every assumption is primitive model/sample data: probability and base-point
facts, absolute continuity with respect to the common dominator `μ`, measurability of the bare
score, the genuine nonvacuous QMD limit, and iid sample/law data.  Mean zero,
integrability of `g^2`, and LAN are all conclusions.

Proof idea: `score_in_L2ZeroMean`, `exists_qmdPath_of_bare_qmd`, then
`QMDPath.lanExpansion1D`, rewriting its dominating measure using
`γ.dominating = μ`, and transporting the score and Fisher term across the
almost-everywhere identification. -/
theorem qmd_score_mean_integrable_and_lan
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Ω) [SigmaFinite μ]
    (curve : ℝ → Measure Ω)
    (h_prob : ∀ t, IsProbabilityMeasure (curve t))
    (h_zero : curve 0 = P)
    (h_ac : ∀ t, curve t ≪ μ)
    (g : Ω → ℝ) (hg_meas : Measurable g)
    (h_qmd :
      Tendsto
        (fun t : ℝ =>
          eLpNorm (fun ω : Ω =>
            Real.sqrt ((curve t).rnDeriv μ ω).toReal
              - Real.sqrt ((curve 0).rnDeriv μ ω).toReal
              - (t / 2) * g ω *
                  Real.sqrt ((curve 0).rnDeriv μ ω).toReal)
            2 μ / ENNReal.ofReal |t|)
        (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞)))
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (X : ℕ → Ω' → Ω)
    (hX_meas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => IndepFun (X i) (X j) P')
    (hident : ∀ i, IdentDistrib (X i) (X 0) P' P')
    (hlaw : Measure.map (X 0) P' = P) :
    (∫ ω, g ω ∂P = 0) ∧
      Integrable (fun ω => g ω ^ 2) P ∧
      TendstoInMeasure P'
        (fun n ω =>
          (∑ i ∈ Finset.range n,
            Real.log
              (((curve ((Real.sqrt n)⁻¹)).rnDeriv μ (X i ω)).toReal /
                ((curve 0).rnDeriv μ (X i ω)).toReal))
            - (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, g (X i ω)
            + (1 / 2 : ℝ) * ∫ x, g x ^ 2 ∂P)
        atTop (fun _ => (0 : ℝ)) := by
  classical
  obtain ⟨γ, hγ_curve, hγ_dom, hg_score⟩ :=
    exists_qmdPath_of_bare_qmd P μ curve h_prob h_zero h_ac g hg_meas h_qmd
  have h_g_sqrt :
      MemLp (fun ω => g ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal) 2 μ :=
    AsymptoticStatistics.ForMathlib.QMDAnalytic.memLp_two_score_mul_sqrt_of_qmd
      h_prob h_ac hg_meas h_qmd
  have h_mean : ∫ ω, g ω ∂P = 0 := by
    rw [← h_zero]
    exact AsymptoticStatistics.ForMathlib.QMDAnalytic.integral_score_eq_zero_of_qmd
      h_prob h_ac hg_meas h_g_sqrt h_qmd
  have h_g_memLp : MemLp g 2 P :=
    (memLp_congr_ae hg_score).mpr (Lp.memLp (γ.score : Lp ℝ 2 P))
  refine ⟨h_mean, h_g_memLp.integrable_sq, ?_⟩
  let h' : EuclideanSpace ℝ (Fin 1) := EuclideanSpace.single 0 1
  have h_law_target :
      γ.dominating.withDensity (fun x => ENNReal.ofReal
          ((QMDPath.to1DParametricFamily γ).density 0 x)) = P := by
    have hP_ac : P ≪ γ.dominating := by
      have h := γ.curve_absContinuous 0
      rwa [γ.curve_at_zero] at h
    have h_density_eq : ∀ x,
        (QMDPath.to1DParametricFamily γ).density 0 x =
          (P.rnDeriv γ.dominating x).toReal := by
      intro x
      change ((γ.curve 0).rnDeriv γ.dominating x).toReal = _
      rw [γ.curve_at_zero]
    have h_ae_eq : (fun x => ENNReal.ofReal
        ((QMDPath.to1DParametricFamily γ).density 0 x)) =ᵐ[γ.dominating]
          P.rnDeriv γ.dominating := by
      filter_upwards [Measure.rnDeriv_lt_top P γ.dominating] with x hx
      rw [h_density_eq x, ENNReal.ofReal_toReal hx.ne]
    rw [MeasureTheory.withDensity_congr_ae h_ae_eq,
      Measure.withDensity_rnDeriv_eq P γ.dominating hP_ac]
  have h_law : Measure.map (X 0) P' =
      γ.dominating.withDensity (fun x => ENNReal.ofReal
        ((QMDPath.to1DParametricFamily γ).density 0 x)) := by
    rw [hlaw]
    exact h_law_target.symm
  have h_score_meas : Measurable (QMDPath.score1D γ) := by
    have h_scalar : Measurable
        (fun ω => ((γ.score : Lp ℝ 2 P) : Ω → ℝ) ω) :=
      (Lp.stronglyMeasurable _).measurable
    have h_single : Continuous
        (fun a : ℝ => EuclideanSpace.single (0 : Fin 1) a) := by
      have h_pi : Continuous
          (fun a : ℝ => (Pi.single (0 : Fin 1) a : Fin 1 → ℝ)) := by
        refine continuous_pi (fun j => ?_)
        fin_cases j
        simpa using! (continuous_id : Continuous (id : ℝ → ℝ))
      have h_eq : (fun a : ℝ => EuclideanSpace.single (0 : Fin 1) a) =
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 1 => ℝ)).symm ∘
            (fun a : ℝ => (Pi.single (0 : Fin 1) a : Fin 1 → ℝ)) := by
        funext a
        simp
      rw [h_eq]
      exact (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Fin 1 => ℝ)).symm.continuous.comp h_pi
    exact h_single.measurable.comp h_scalar
  have h_inner_score : ∀ x,
      @inner ℝ _ _ h' (QMDPath.score1D γ x) = (γ.score : Ω → ℝ) x := by
    intro x
    unfold QMDPath.score1D
    rw [PiLp.inner_apply, Fin.sum_univ_one]
    have h_single : EuclideanSpace.single (0 : Fin 1)
        ((γ.score : Ω → ℝ) x) (0 : Fin 1) = (γ.score : Ω → ℝ) x := by
      simp
    rw [h_single]
    change (γ.score : Ω → ℝ) x * h' 0 = (γ.score : Ω → ℝ) x
    rw [show h' 0 = (1 : ℝ) by simp [h'], mul_one]
  have h_density_zero : ∀ x,
      (QMDPath.to1DParametricFamily γ).density 0 x =
        (P.rnDeriv γ.dominating x).toReal := by
    intro x
    change ((γ.curve 0).rnDeriv γ.dominating x).toReal = _
    rw [γ.curve_at_zero]
  have h_fisher :
      AsymptoticStatistics.fisherInformation
          (QMDPath.to1DParametricFamily γ) γ.dominating 0
          (QMDPath.score1D γ) h' h' = ∫ x, g x ^ 2 ∂P := by
    have hP_ac : P ≪ γ.dominating := by
      have h := γ.curve_absContinuous 0
      rwa [γ.curve_at_zero] at h
    unfold AsymptoticStatistics.fisherInformation
    calc
      ∫ x, (@inner ℝ _ _ h' (QMDPath.score1D γ x) *
              @inner ℝ _ _ h' (QMDPath.score1D γ x)) *
            (QMDPath.to1DParametricFamily γ).density 0 x ∂γ.dominating
          = ∫ x, (P.rnDeriv γ.dominating x).toReal *
              (γ.score : Ω → ℝ) x ^ 2 ∂γ.dominating := by
              apply integral_congr_ae
              filter_upwards with x
              rw [h_inner_score x, h_density_zero x]
              ring
      _ = ∫ x, (γ.score : Ω → ℝ) x ^ 2 ∂P :=
        MeasureTheory.integral_toReal_rnDeriv_mul hP_ac
      _ = ∫ x, g x ^ 2 ∂P :=
        integral_congr_ae (hg_score.mono fun _ hx => by
          simpa only using congrArg (fun y : ℝ => y ^ 2) hx.symm)
  have hLAN := QMDPath.lanExpansion1D γ h' (fun _ : ℕ => h')
    tendsto_const_nhds P' X hX_meas hindep hident h_law h_score_meas
  have h_score_X : ∀ i,
      (fun ω => g (X i ω)) =ᵐ[P'] fun ω => (γ.score : Ω → ℝ) (X i ω) := by
    intro i
    have hmap : Measure.map (X i) P' = P := by rw [(hident i).map_eq, hlaw]
    have hg_map : g =ᵐ[Measure.map (X i) P'] (γ.score : Ω → ℝ) := by
      rwa [hmap]
    simpa [Function.comp_def] using ae_eq_comp (hX_meas i).aemeasurable hg_map
  have h_score_X_all :
      ∀ᵐ ω ∂P', ∀ i, g (X i ω) = (γ.score : Ω → ℝ) (X i ω) :=
    ae_all_iff.mpr h_score_X
  refine TendstoInMeasure.congr' ?_ (Eventually.of_forall fun _ => rfl) hLAN
  refine Eventually.of_forall fun n => ?_
  filter_upwards [h_score_X_all] with ω hω
  rw [h_fisher]
  simp [QMDPath.to1DParametricFamily, h', hγ_curve, hγ_dom, h_inner_score, hω]

end AsymptoticStatistics.LowerBounds.T6_FinDimLAN.QMDScoreLAN
