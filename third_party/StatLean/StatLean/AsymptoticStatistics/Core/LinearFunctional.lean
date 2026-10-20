module
public import StatLean.AsymptoticStatistics.Core.MassMethod

@[expose] public section

/-!
# Linear functionals: TV-Fréchet expansion and pathwise differentiability

The reusable **linear-functional** brick for the mass method. For a fixed integrand
`a : Ω → ℝ`, the parameter functional `meanFunctional a : Q ↦ ∫ a dQ` is linear, so its
directional derivative along any quadratic-mean-differentiable path `γ` at `P` is exactly
`∫ a · (γ.score) dP` — i.e. `IsTVFrechetExpansion P (meanFunctional a) a` holds
(`meanFunctional_isTVFrechetExpansion`) whenever `a` is **bounded and measurable**. Fed to
`pathwiseDifferentiableAt_of_TVFrechet` (`Core/MassMethod`), this constructs pathwise
differentiability over the full nonparametric tangent `⊤` with derivative
`g ↦ ⟪a − ∫a dP, g⟫`.

The core theorem is reused by both the empirical-distribution example (vdV
Example 25.24) and the MAR-mean example (25.43, via
`marMean_Ψ = meanFunctional (R·Y/π)`).

Headline declarations: `meanFunctional`, `memLp_two_of_bounded`,
`meanFunctional_isTVFrechetExpansion`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
open AsymptoticStatistics.Core
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.ForMathlib.QMDAnalytic
open AsymptoticStatistics.ForMathlib.RnDerivSqrt
open AsymptoticStatistics.L2Utils

namespace AsymptoticStatistics.Core.MassMethod

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {a : Ω → ℝ}

/-- The linear mean functional `ψ_a(Q) = ∫ a dQ` for a fixed integrand `a`.

Reference: vdV Example 25.24 (§25.3), the empirical-distribution functional
`Q ↦ ∫ a dQ` (equivalently the CDF `Q ↦ Q(−∞, x]` for `a = 𝟙_{(−∞,x]}`). -/
noncomputable def meanFunctional (a : Ω → ℝ) : Measure Ω → ℝ :=
  fun Q => ∫ ω, a ω ∂Q

/-- A bounded measurable integrand is square-integrable under the
probability measure `P`. -/
theorem memLp_two_of_bounded
    (ha_meas : Measurable a) (ha_bdd : ∃ C : ℝ, ∀ ω, |a ω| ≤ C) :
    MemLp a 2 P := by
  obtain ⟨C, hC⟩ := ha_bdd
  refine MemLp.of_bound ha_meas.aestronglyMeasurable C ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]; exact hC ω

/-- The QMD remainder `r_t = √p_t − √p_0 − (t/2)·g·√p_0` is measurable. -/
private lemma qmdRem_measurable
    {μ : Measure Ω} {curve : ℝ → Measure Ω} {g : Ω → ℝ}
    (hg_meas : Measurable g) (t : ℝ) :
    Measurable (qmdRem curve μ g t) := by
  unfold qmdRem
  exact ((((Measure.measurable_rnDeriv (curve t) μ).ennreal_toReal.sqrt).sub
    ((Measure.measurable_rnDeriv (curve 0) μ).ennreal_toReal.sqrt))).sub
    ((measurable_const.mul hg_meas).mul
      (Measure.measurable_rnDeriv (curve 0) μ).ennreal_toReal.sqrt)

/-- The QMD remainder is in `L²(μ)` for `t` in a punctured neighbourhood of `0`
(reproduces the `Core/QMDPath.residual_memLp_eventually` argument for an abstract
curve, directly from the `ℝ≥0∞`-form QMD limit). -/
private lemma qmdRem_memLp_eventually
    {μ : Measure Ω} [SigmaFinite μ] {curve : ℝ → Measure Ω} {g : Ω → ℝ}
    (hg_meas : Measurable g) (h_qmd : IsQMDLimit curve μ g) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), MemLp (qmdRem curve μ g t) 2 μ := by
  have h_lt_one : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      eLpNorm (qmdRem curve μ g t) 2 μ / ENNReal.ofReal |t| < 1 :=
    h_qmd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
  filter_upwards [h_lt_one, self_mem_nhdsWithin] with t htlt htne
  have habs : (0 : ℝ) < |t| := abs_pos.mpr htne
  have hofreal_ne_zero : ENNReal.ofReal |t| ≠ 0 := (ENNReal.ofReal_pos.mpr habs).ne'
  have hofreal_ne_top : ENNReal.ofReal |t| ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_eLp_lt : eLpNorm (qmdRem curve μ g t) 2 μ < ENNReal.ofReal |t| := by
    calc eLpNorm (qmdRem curve μ g t) 2 μ
        = eLpNorm (qmdRem curve μ g t) 2 μ / ENNReal.ofReal |t|
            * ENNReal.ofReal |t| := by
          rw [ENNReal.div_mul_cancel hofreal_ne_zero hofreal_ne_top]
      _ < 1 * ENNReal.ofReal |t| :=
          ENNReal.mul_lt_mul_left hofreal_ne_zero hofreal_ne_top htlt
      _ = ENNReal.ofReal |t| := one_mul _
  exact ⟨(qmdRem_measurable hg_meas t).aestronglyMeasurable,
    lt_trans h_eLp_lt ENNReal.ofReal_lt_top⟩

/-- The QMD ratio `‖r_t‖_{L²(μ)} / |t| → 0` in `ℝ` (the `.toReal` form of the
`ℝ≥0∞`-form QMD limit). This is the differentiability *rate* used to control
the second-order remainder in the pathwise derivative of the mean functional. -/
private lemma qmdRem_norm_div_tendsto_zero
    {μ : Measure Ω} {curve : ℝ → Measure Ω} {g : Ω → ℝ}
    (h_qmd : IsQMDLimit curve μ g) :
    Tendsto (fun t : ℝ => (eLpNorm (qmdRem curve μ g t) 2 μ).toReal / |t|)
      (𝓝[≠] 0) (𝓝 0) := by
  have h_cts : ContinuousAt ENNReal.toReal (0 : ℝ≥0∞) :=
    ENNReal.continuousAt_toReal (by simp)
  have h_to_real := h_cts.tendsto.comp h_qmd
  simp only [Function.comp_def, ENNReal.toReal_zero] at h_to_real
  have h_eq : (fun t : ℝ =>
      (eLpNorm (qmdRem curve μ g t) 2 μ / ENNReal.ofReal |t|).toReal)
        = fun t : ℝ => (eLpNorm (qmdRem curve μ g t) 2 μ).toReal / |t| := by
    funext t; rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (abs_nonneg _)]
  rwa [h_eq] at h_to_real

/-- The `L²(μ)`-norm of the QMD remainder tends to `0` as `t → 0`
(from the QMD ratio `‖r_t‖/|t| → 0` times `|t| → 0`). -/
private lemma qmdRem_norm_tendsto_zero
    {μ : Measure Ω} {curve : ℝ → Measure Ω} {g : Ω → ℝ}
    (h_qmd : IsQMDLimit curve μ g) :
    Tendsto (fun t : ℝ => (eLpNorm (qmdRem curve μ g t) 2 μ).toReal)
      (𝓝[≠] 0) (𝓝 0) := by
  have h_real := qmdRem_norm_div_tendsto_zero h_qmd
  have h_abs : Tendsto (fun t : ℝ => |t|) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => |t|) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ))
    exact h.mono_left nhdsWithin_le_nhds
  have h_prod := h_real.mul h_abs
  simp only [mul_zero] at h_prod
  refine Tendsto.congr' ?_ h_prod
  filter_upwards [self_mem_nhdsWithin] with t htne
  have habs : |t| ≠ 0 := abs_ne_zero.mpr htne
  field_simp

/-- **Pathwise (DQM-path) derivative of the mean functional** — vdV Ex 25.24.

For the linear functional `ψ_a(Q) = ∫ a dQ` and a fixed bounded measurable
`a`, the directional derivative along every quadratic-mean-differentiable
path `γ` at `P` is the inner product of `a` with the path's score:

  `lim_{t→0} (ψ_a(γ.curve t) − ψ_a(P)) / t = ∫ a · (γ.score) dP`.

This is the analytic heart of Example 25.24: writing `pₜ = d(γ.curve t)/dμ`
and `sₜ = √pₜ`, one has `∫ a d(γ.curve t) = ∫ a sₜ² dμ`, and the QMD limit
`sₜ − s₀ = (t/2)·(score)·s₀ + o(t)` in `L²(μ)` gives, after dividing the
difference of squares by `t`, the limit `∫ a · (score) · s₀² dμ = ∫ a · (score) dP`.

Reference: vdV §25.3, Example 25.24; the QMD machinery is `Core/QMDPath`. -/
theorem meanFunctional_isTVFrechetExpansion
    (ha_meas : Measurable a) (ha_bdd : ∃ C : ℝ, ∀ ω, |a ω| ≤ C) :
    IsTVFrechetExpansion P (meanFunctional a) a := by
  intro γ
  simp only [meanFunctional]
  -- Standing data extracted from the QMD path.
  have h_prob : ∀ t, IsProbabilityMeasure (γ.curve t) := γ.curve_isProbability
  have h_ac : ∀ t, γ.curve t ≪ γ.dominating := γ.curve_absContinuous
  have h_zero : γ.curve 0 = P := γ.curve_at_zero
  -- Abbreviations for the score, the square-root densities, and the QMD remainder.
  set g : Ω → ℝ := ((γ.score : Lp ℝ 2 P) : Ω → ℝ) with hg_def
  have hg_meas : Measurable g := (Lp.stronglyMeasurable (γ.score : Lp ℝ 2 P)).measurable
  set s : ℝ → Ω → ℝ :=
    fun t ω => Real.sqrt ((γ.curve t).rnDeriv γ.dominating ω).toReal with hs_def
  set r : ℝ → Ω → ℝ :=
    fun t => qmdRem γ.curve γ.dominating g t with hr_def
  -- The `ℝ≥0∞`-form QMD limit (matches the `qmd_limit` field definitionally).
  have h_qmd : IsQMDLimit γ.curve γ.dominating g := γ.qmd_limit
  -- Pointwise unfolding of the remainder.
  have hr_pt : ∀ t ω, r t ω = s t ω - s 0 ω - (t / 2) * g ω * s 0 ω := fun t ω => rfl
  -- The uniform bound on `a`, with `0 ≤ C`.
  obtain ⟨C, hC⟩ := ha_bdd
  haveI hΩ : Nonempty Ω := MeasureTheory.nonempty_of_isProbabilityMeasure P
  have hC_nn : 0 ≤ C := le_trans (abs_nonneg (a (Classical.arbitrary Ω))) (hC _)
  -- Bounded-times-L² is L² (the dominating measure need not be finite).
  have memLp_bdd : ∀ {h : Ω → ℝ}, MemLp h 2 γ.dominating →
      MemLp (fun ω => a ω * h ω) 2 γ.dominating := by
    intro h hh
    refine MemLp.mono' (hh.norm.const_mul C)
      (ha_meas.aestronglyMeasurable.mul hh.1) ?_
    filter_upwards with ω
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((Real.norm_eq_abs _).le.trans (hC ω)) (norm_nonneg _)
  -- Standing L² memberships.
  haveI : IsProbabilityMeasure (γ.curve 0) := h_prob 0
  have hs0 : MemLp (s 0) 2 γ.dominating :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (h_ac 0)
  have hgs0 : MemLp (fun ω => g ω * s 0 ω) 2 γ.dominating :=
    memLp_two_score_mul_sqrt_of_qmd h_prob h_ac hg_meas h_qmd
  have has0 : MemLp (fun ω => a ω * s 0 ω) 2 γ.dominating := memLp_bdd hs0
  -- `∫ (s 0)² = 1`.
  have hs0_int : ∫ ω, (s 0 ω) ^ 2 ∂γ.dominating = 1 := by
    have h := AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_sqrt_rnDeriv_sq (h_ac 0)
    rw [measure_univ, ENNReal.toReal_one] at h
    exact h
  -- === Reusable integrability helpers ===
  have memLp_sq_int : ∀ {f : Ω → ℝ}, MemLp f 2 γ.dominating →
      Integrable (fun ω => f ω ^ 2) γ.dominating := by
    intro f hf
    exact (integrable_mul_of_memLp_two γ.dominating hf hf).congr
      (by filter_upwards with ω; ring)
  have memLp_bdd_sq_int : ∀ {f : Ω → ℝ}, MemLp f 2 γ.dominating →
      Integrable (fun ω => a ω * f ω ^ 2) γ.dominating := by
    intro f hf
    exact (integrable_mul_of_memLp_two γ.dominating (memLp_bdd hf) hf).congr
      (by filter_upwards with ω; ring)
  -- === Square-root density memberships (all t) ===
  have hst : ∀ t, MemLp (s t) 2 γ.dominating := by
    intro t
    haveI := h_prob t
    exact AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (h_ac t)
  have hdiff : ∀ t, MemLp (fun ω => s t ω - s 0 ω) 2 γ.dominating := fun t => (hst t).sub hs0
  -- Pointwise `(s t ω)² = (rnDeriv).toReal`, used in the bridges.
  have hs_sq : ∀ t ω, s t ω ^ 2 = ((γ.curve t).rnDeriv γ.dominating ω).toReal := by
    intro t ω; simp only [hs_def]; exact Real.sq_sqrt ENNReal.toReal_nonneg
  -- === RN-derivative bridges: ∫ φ dQ = ∫ φ · (√ dQ/dμ)² dμ ===
  have hbridge : ∀ t, ∫ ω, a ω ∂γ.curve t = ∫ ω, a ω * s t ω ^ 2 ∂γ.dominating := by
    intro t
    haveI := h_prob t
    rw [AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_eq_integral_mul_rnDeriv_of_ac
        (h_ac t) a]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    simp only [hs_sq]
  have hbP : ∫ ω, a ω ∂P = ∫ ω, a ω * s 0 ω ^ 2 ∂γ.dominating := by
    rw [← hbridge 0, h_zero]
  have hbL : ∫ ω, a ω * g ω ∂P = ∫ ω, a ω * g ω * s 0 ω ^ 2 ∂γ.dominating := by
    have hb0 : ∫ ω, a ω * g ω ∂γ.curve 0 = ∫ ω, a ω * g ω * s 0 ω ^ 2 ∂γ.dominating := by
      rw [AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_eq_integral_mul_rnDeriv_of_ac
          (h_ac 0) (fun ω => a ω * g ω)]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
      simp only [hs_sq]
    rw [← hb0, h_zero]
  -- === Integrability facts ===
  have hIast : ∀ t, Integrable (fun ω => a ω * s t ω ^ 2) γ.dominating :=
    fun t => memLp_bdd_sq_int (hst t)
  have hI_c : ∀ t, Integrable (fun ω => a ω * (s t ω - s 0 ω) ^ 2) γ.dominating :=
    fun t => memLp_bdd_sq_int (hdiff t)
  have hI_l : Integrable (fun ω => a ω * g ω * s 0 ω ^ 2) γ.dominating :=
    (integrable_mul_of_memLp_two γ.dominating (memLp_bdd hgs0) hs0).congr
      (by filter_upwards with ω; ring)
  have hI_sqdiff : ∀ t, Integrable (fun ω => (s t ω - s 0 ω) ^ 2) γ.dominating :=
    fun t => memLp_sq_int (hdiff t)
  -- === Analytic sub-lemmas (filled below) ===
  have hL2rate : Tendsto (fun t => (∫ ω, (s t ω - s 0 ω) ^ 2 ∂γ.dominating) / |t|)
      (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    have hq : Tendsto (fun t => (eLpNorm (r t) 2 γ.dominating).toReal)
        (𝓝[≠] (0:ℝ)) (𝓝 0) := qmdRem_norm_tendsto_zero h_qmd
    have hqd : Tendsto (fun t => (eLpNorm (r t) 2 γ.dominating).toReal / |t|)
        (𝓝[≠] (0:ℝ)) (𝓝 0) := qmdRem_norm_div_tendsto_zero h_qmd
    have habs : Tendsto (fun t : ℝ => |t|) (𝓝[≠] (0:ℝ)) (𝓝 0) := by
      have h : Tendsto (fun t : ℝ => |t|) (𝓝 (0:ℝ)) (𝓝 0) := by
        simpa using (continuous_abs.tendsto (0:ℝ))
      exact h.mono_left nhdsWithin_le_nhds
    -- Envelope tends to 0.
    have henv : Tendsto (fun t => |t| * ((∫ ω, (g ω * s 0 ω) ^ 2 ∂γ.dominating) / 2)
          + 2 * ((eLpNorm (r t) 2 γ.dominating).toReal
              * ((eLpNorm (r t) 2 γ.dominating).toReal / |t|)))
        (𝓝[≠] (0:ℝ)) (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => |t| * ((∫ ω, (g ω * s 0 ω) ^ 2 ∂γ.dominating) / 2))
          (𝓝[≠] (0:ℝ)) (𝓝 0) := by
        simpa using habs.mul_const ((∫ ω, (g ω * s 0 ω) ^ 2 ∂γ.dominating) / 2)
      have h2 : Tendsto (fun t : ℝ => 2 * ((eLpNorm (r t) 2 γ.dominating).toReal
              * ((eLpNorm (r t) 2 γ.dominating).toReal / |t|)))
          (𝓝[≠] (0:ℝ)) (𝓝 0) := by
        simpa using (hq.mul hqd).const_mul 2
      simpa using h1.add h2
    refine squeeze_zero' ?_ ?_ henv
    · filter_upwards [self_mem_nhdsWithin] with t _
      exact div_nonneg (integral_nonneg fun ω => sq_nonneg _) (abs_nonneg _)
    · filter_upwards [qmdRem_memLp_eventually hg_meas h_qmd, self_mem_nhdsWithin]
        with t hr_memLp ht
      have htne : t ≠ 0 := by simpa using ht
      have htabs : (0:ℝ) < |t| := abs_pos.mpr htne
      have htabs_ne : |t| ≠ 0 := htabs.ne'
      have hrmem : MemLp (r t) 2 γ.dominating := hr_memLp
      have hIrsq : Integrable (fun ω => r t ω ^ 2) γ.dominating := memLp_sq_int hrmem
      have hIgs0sq : Integrable (fun ω => (g ω * s 0 ω) ^ 2) γ.dominating := memLp_sq_int hgs0
      -- `∫ (r t)² dμ = (eLpNorm (r t)).toReal²`.
      have hrq : ∫ ω, r t ω ^ 2 ∂γ.dominating = (eLpNorm (r t) 2 γ.dominating).toReal ^ 2 := by
        rw [← sqrt_integral_sq_eq_eLpNorm_toReal hrmem,
            Real.sq_sqrt (integral_nonneg fun ω => sq_nonneg _)]
      -- Pointwise `(s t − s 0)² ≤ 2 (r t)² + (t²/2)(g·s 0)²`.
      have hpw : ∀ ω, (s t ω - s 0 ω) ^ 2
          ≤ 2 * r t ω ^ 2 + (t ^ 2 / 2) * (g ω * s 0 ω) ^ 2 := by
        intro ω
        rw [hr_pt t ω]
        nlinarith [sq_nonneg (s t ω - s 0 ω - t * (g ω * s 0 ω))]
      have hIg : Integrable
          (fun ω => 2 * r t ω ^ 2 + (t ^ 2 / 2) * (g ω * s 0 ω) ^ 2) γ.dominating :=
        (hIrsq.const_mul 2).add (hIgs0sq.const_mul (t ^ 2 / 2))
      have hle_int : ∫ ω, (s t ω - s 0 ω) ^ 2 ∂γ.dominating
          ≤ 2 * (eLpNorm (r t) 2 γ.dominating).toReal ^ 2
            + (t ^ 2 / 2) * (∫ ω, (g ω * s 0 ω) ^ 2 ∂γ.dominating) := by
        have hmono := integral_mono (hI_sqdiff t) hIg hpw
        rw [integral_add (hIrsq.const_mul 2) (hIgs0sq.const_mul (t ^ 2 / 2)),
            integral_const_mul, integral_const_mul, hrq] at hmono
        exact hmono
      calc (∫ ω, (s t ω - s 0 ω) ^ 2 ∂γ.dominating) / |t|
          ≤ (2 * (eLpNorm (r t) 2 γ.dominating).toReal ^ 2
              + (t ^ 2 / 2) * (∫ ω, (g ω * s 0 ω) ^ 2 ∂γ.dominating)) / |t| :=
            (div_le_div_iff_of_pos_right htabs).mpr hle_int
        _ = |t| * ((∫ ω, (g ω * s 0 ω) ^ 2 ∂γ.dominating) / 2)
              + 2 * ((eLpNorm (r t) 2 γ.dominating).toReal
                  * ((eLpNorm (r t) 2 γ.dominating).toReal / |t|)) := by
            rw [← sq_abs t]; field_simp; ring
  have hTermI : Tendsto (fun t => (∫ ω, a ω * (s t ω - s 0 ω) ^ 2 ∂γ.dominating) / t)
      (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hL2rate.const_mul C)
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htne : t ≠ 0 := by simpa using ht
    have htabs : (0:ℝ) < |t| := abs_pos.mpr htne
    -- Pointwise `|a·(s t − s 0)²| ≤ C·(s t − s 0)²`.
    have hpw_abs : ∀ ω, |a ω * (s t ω - s 0 ω) ^ 2| ≤ C * (s t ω - s 0 ω) ^ 2 := by
      intro ω
      rw [abs_mul, abs_of_nonneg (sq_nonneg (s t ω - s 0 ω))]
      exact mul_le_mul_of_nonneg_right (hC ω) (sq_nonneg _)
    have habs_bound : |∫ ω, a ω * (s t ω - s 0 ω) ^ 2 ∂γ.dominating|
        ≤ C * ∫ ω, (s t ω - s 0 ω) ^ 2 ∂γ.dominating := by
      calc |∫ ω, a ω * (s t ω - s 0 ω) ^ 2 ∂γ.dominating|
          ≤ ∫ ω, |a ω * (s t ω - s 0 ω) ^ 2| ∂γ.dominating := abs_integral_le_integral_abs
        _ ≤ ∫ ω, C * (s t ω - s 0 ω) ^ 2 ∂γ.dominating :=
            integral_mono (hI_c t).abs ((hI_sqdiff t).const_mul C) hpw_abs
        _ = C * ∫ ω, (s t ω - s 0 ω) ^ 2 ∂γ.dominating := integral_const_mul C _
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |∫ ω, a ω * (s t ω - s 0 ω) ^ 2 ∂γ.dominating| / |t|
        ≤ (C * ∫ ω, (s t ω - s 0 ω) ^ 2 ∂γ.dominating) / |t| :=
          (div_le_div_iff_of_pos_right htabs).mpr habs_bound
      _ = C * ((∫ ω, (s t ω - s 0 ω) ^ 2 ∂γ.dominating) / |t|) := mul_div_assoc C _ _
  have hTermIII : Tendsto (fun t => 2 * (∫ ω, (a ω * s 0 ω) * r t ω ∂γ.dominating) / t)
      (𝓝[≠] (0:ℝ)) (𝓝 0) := by
    have hqd : Tendsto (fun t => (eLpNorm (r t) 2 γ.dominating).toReal / |t|)
        (𝓝[≠] (0:ℝ)) (𝓝 0) := qmdRem_norm_div_tendsto_zero h_qmd
    refine squeeze_zero_norm' ?_
      (by simpa using hqd.const_mul (2 * Real.sqrt (∫ ω, (a ω * s 0 ω) ^ 2 ∂γ.dominating)))
    filter_upwards [qmdRem_memLp_eventually hg_meas h_qmd, self_mem_nhdsWithin] with t hr_memLp ht
    have htne : t ≠ 0 := by simpa using ht
    have htabs : (0:ℝ) < |t| := abs_pos.mpr htne
    have hrmem : MemLp (r t) 2 γ.dominating := hr_memLp
    -- Cauchy–Schwarz with the fixed test function a·s 0.
    have hcs := abs_integral_mul_le_sqrt_integral_sq γ.dominating has0 hrmem
    rw [sqrt_integral_sq_eq_eLpNorm_toReal hrmem] at hcs
    -- ‖2·∫/t‖ = 2·|∫|/|t| ≤ 2·√(∫(a s0)²)·q(t)/|t|.
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      show |(2:ℝ)| = 2 from by norm_num]
    calc 2 * |∫ ω, a ω * s 0 ω * r t ω ∂γ.dominating| / |t|
        ≤ 2 * (Real.sqrt (∫ ω, (a ω * s 0 ω) ^ 2 ∂γ.dominating)
            * (eLpNorm (r t) 2 γ.dominating).toReal) / |t| :=
          (div_le_div_iff_of_pos_right htabs).mpr (by linarith [hcs])
      _ = 2 * Real.sqrt (∫ ω, (a ω * s 0 ω) ^ 2 ∂γ.dominating)
            * ((eLpNorm (r t) 2 γ.dominating).toReal / |t|) := by
          ring
  have hGeq : (fun t : ℝ => (∫ ω, a ω ∂γ.curve t - ∫ ω, a ω ∂P) / t)
      =ᶠ[𝓝[≠] (0:ℝ)]
      (fun t : ℝ => (∫ ω, a ω * (s t ω - s 0 ω) ^ 2 ∂γ.dominating) / t
          + (∫ ω, a ω * g ω ∂P)
          + 2 * (∫ ω, (a ω * s 0 ω) * r t ω ∂γ.dominating) / t) := by
    filter_upwards [qmdRem_memLp_eventually hg_meas h_qmd, self_mem_nhdsWithin] with t hr_memLp ht
    have htne : t ≠ 0 := by simpa using ht
    -- Integrability of the cross term `(a·s 0)·r t` (needs `r t ∈ L²`, holds here).
    have hI_d : Integrable (fun ω => a ω * s 0 ω * r t ω) γ.dominating :=
      integrable_mul_of_memLp_two γ.dominating has0 hr_memLp
    have hI_tl : Integrable (fun ω => t * (a ω * g ω * s 0 ω ^ 2)) γ.dominating :=
      hI_l.const_mul t
    have hI_2d : Integrable (fun ω => 2 * (a ω * s 0 ω * r t ω)) γ.dominating :=
      hI_d.const_mul 2
    have hI_c_tl : Integrable
        (fun ω => a ω * (s t ω - s 0 ω) ^ 2 + t * (a ω * g ω * s 0 ω ^ 2)) γ.dominating :=
      (hI_c t).add hI_tl
    -- The QMD-substituted pointwise identity: A − B = C + t·L + 2·D.
    have hID :
        (∫ ω, a ω * s t ω ^ 2 ∂γ.dominating) - (∫ ω, a ω * s 0 ω ^ 2 ∂γ.dominating)
          = (∫ ω, a ω * (s t ω - s 0 ω) ^ 2 ∂γ.dominating)
            + t * (∫ ω, a ω * g ω * s 0 ω ^ 2 ∂γ.dominating)
            + 2 * (∫ ω, a ω * s 0 ω * r t ω ∂γ.dominating) := by
      rw [← integral_sub (hIast t) (hIast 0),
        show (∫ ω, a ω * (s t ω - s 0 ω) ^ 2 ∂γ.dominating)
              + t * (∫ ω, a ω * g ω * s 0 ω ^ 2 ∂γ.dominating)
              + 2 * (∫ ω, a ω * s 0 ω * r t ω ∂γ.dominating)
            = ∫ ω, (a ω * (s t ω - s 0 ω) ^ 2 + t * (a ω * g ω * s 0 ω ^ 2)
                + 2 * (a ω * s 0 ω * r t ω)) ∂γ.dominating from by
          rw [integral_add hI_c_tl hI_2d, integral_add (hI_c t) hI_tl,
              integral_const_mul, integral_const_mul]]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
      simp only [hr_pt]
      ring
    -- Rewrite the difference quotient and divide.
    rw [hbridge t, hbP, hbL, hID]
    field_simp
  -- === Assemble ===
  have hsum : Tendsto (fun t : ℝ => (∫ ω, a ω * (s t ω - s 0 ω) ^ 2 ∂γ.dominating) / t
        + (∫ ω, a ω * g ω ∂P)
        + 2 * (∫ ω, (a ω * s 0 ω) * r t ω ∂γ.dominating) / t)
      (𝓝[≠] (0:ℝ)) (𝓝 (∫ ω, a ω * g ω ∂P)) := by
    have h := (hTermI.add_const (∫ ω, a ω * g ω ∂P)).add hTermIII
    simpa using h
  exact Filter.Tendsto.congr' hGeq.symm hsum

end AsymptoticStatistics.Core.MassMethod
