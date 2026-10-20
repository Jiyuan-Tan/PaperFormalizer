module
public import StatLean.AsymptoticStatistics.ForMathlib.RnDerivSqrt
public import StatLean.AsymptoticStatistics.ForMathlib.L2
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Instances.ENNReal.Lemmas

@[expose] public section

/-!
Analytic engines for the dominated QMD limit (vdV §25.3, lem:25.14).

Given a curve `t ↦ Q_t : ℝ → Measure Ω` of probability measures dominated
by a fixed σ-finite `μ` and a measurable `g : Ω → ℝ`, the QMD limit
`‖√p_t − √p_0 − (t/2) g √p_0‖_{L²(μ)} / |t| → 0` (in `ℝ≥0∞`) as
`t → 0` (along `𝓝[≠] 0`) implies:

* **Stage 1** (`memLp_two_score_mul_sqrt_of_qmd`):
  `g · √p_0 ∈ L²(μ)`. Triangle inequality on the QMD remainder plus
  the unit-norm bound `‖√p_t‖_{L²(μ)} = 1` for probability measures.

* **Stage 2** (`integral_score_eq_zero_of_qmd`):
  `∫ g d(curve 0) = 0`. Cauchy–Schwarz on the *linear* part of QMD
  (no second-order Hellinger expansion needed) plus the affinity
  bound `∫ √p_t √p_0 dμ ≤ 1`, giving a two-sided sign argument.

Together these are the analytic content of the consistency lemma
`Core/QMDPath.score_in_L2ZeroMean`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.ForMathlib.QMDAnalytic

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The QMD remainder
`r_t(ω) = √p_t(ω) − √p_0(ω) − (t/2) g(ω) √p_0(ω)`, written in the
exact pointwise form used by `Core/QMDPath.QMDPath.qmd_limit`. -/
noncomputable def qmdRem (curve : ℝ → Measure Ω) (μ : Measure Ω)
    (g : Ω → ℝ) (t : ℝ) : Ω → ℝ := fun ω =>
  Real.sqrt ((curve t).rnDeriv μ ω).toReal
    - Real.sqrt ((curve 0).rnDeriv μ ω).toReal
    - (t / 2) * g ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal

/-- The `ℝ≥0∞`-form QMD limit: `‖r_t‖_{L²(μ)} / |t| → 0` (in `ℝ≥0∞`)
as `t → 0` along `𝓝[≠] 0`. We give it a name to avoid repeating the
nine-line spelling at every call site. -/
def IsQMDLimit (curve : ℝ → Measure Ω) (μ : Measure Ω) (g : Ω → ℝ) : Prop :=
  Tendsto (fun t : ℝ => eLpNorm (qmdRem curve μ g t) 2 μ / ENNReal.ofReal |t|)
    (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞))

/-- Probability constraint ⇒ `‖√p_t‖_{L²(μ)} = 1` (more precisely the
squared `L²` norm equals 1). Companion to
`RnDerivSqrt.integral_sqrt_rnDeriv_sq` for probability measures. -/
private lemma integral_sqrt_rnDeriv_sq_eq_one
    {μ : Measure Ω} [SigmaFinite μ] {ν : Measure Ω}
    [IsProbabilityMeasure ν] (h_ac : ν ≪ μ) :
    ∫ ω, Real.sqrt ((ν.rnDeriv μ ω).toReal) ^ 2 ∂μ = 1 := by
  rw [AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_sqrt_rnDeriv_sq h_ac,
      measure_univ]
  rfl

/-- Bridge between the L²(μ) `eLpNorm` and the real-valued
`√(∫ f² dμ)` for `MemLp f 2 μ`. -/
lemma sqrt_integral_sq_eq_eLpNorm_toReal {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    Real.sqrt (∫ ω, f ω ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  -- Goal: √(∫ f²) = (ENNReal.ofReal ((∫ ‖f‖^2)^(1/2))).toReal
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  -- Reduce `‖f‖^(2 : ℝ)` to `f^(2 : ℕ)` pointwise.
  have h_int_eq :
      (fun ω => ‖f ω‖ ^ (2 : ℝ≥0∞).toReal) = (fun ω => f ω ^ 2) := by
    funext ω
    rw [h2, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [h_int_eq]
  have h_int_nn : 0 ≤ ∫ ω, f ω ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg h_int_nn _), h2,
      Real.sqrt_eq_rpow]
  norm_num

/-- Cross-term Cauchy–Schwarz: `|∫ r_t · √p_0 dμ| / |t| → 0` along `𝓝[≠] 0`
in `ℝ`. We pair the QMD limit (in `ℝ≥0∞`-form, after `toReal` conversion)
with `(eLpNorm √p_0 2 μ).toReal = 1` for the bound
`|∫ r_t · √p_0 dμ| ≤ (eLpNorm r_t 2 μ).toReal`. -/
private lemma integral_qmdRem_mul_sqrt_p0_isLittleO
    {μ : Measure Ω} [SigmaFinite μ] {curve : ℝ → Measure Ω}
    (h_prob : ∀ t, IsProbabilityMeasure (curve t))
    (h_ac : ∀ t, curve t ≪ μ)
    {g : Ω → ℝ} (hg_meas : Measurable g)
    (_h_g_sqrt : MemLp
      (fun ω => g ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal) 2 μ)
    (h_qmd : IsQMDLimit curve μ g) :
    Tendsto
      (fun t : ℝ =>
        |∫ ω, qmdRem curve μ g t ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ|
          / |t|)
      (𝓝[≠] 0) (𝓝 0) := by
  haveI : IsProbabilityMeasure (curve 0) := h_prob 0
  -- L²(μ)-membership of `√p_0`, with squared L²-norm = 1.
  have hp0_memLp : MemLp (fun ω => Real.sqrt ((curve 0).rnDeriv μ ω).toReal) 2 μ :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (h_ac 0)
  have hp0_int_sq : ∫ ω, Real.sqrt ((curve 0).rnDeriv μ ω).toReal ^ 2 ∂μ = 1 :=
    integral_sqrt_rnDeriv_sq_eq_one (h_ac 0)
  -- Convert the ENNReal QMD limit to ℝ.
  have h_qmd_real : Tendsto
      (fun t : ℝ => (eLpNorm (qmdRem curve μ g t) 2 μ).toReal / |t|)
      (𝓝[≠] 0) (𝓝 0) := by
    have h_cts : ContinuousAt ENNReal.toReal (0 : ℝ≥0∞) :=
      ENNReal.continuousAt_toReal (by simp)
    have h_to_real : Tendsto
        (fun t : ℝ =>
          (eLpNorm (qmdRem curve μ g t) 2 μ / ENNReal.ofReal |t|).toReal)
        (𝓝[≠] 0) (𝓝 (0 : ℝ≥0∞).toReal) := h_cts.tendsto.comp h_qmd
    simp only [ENNReal.toReal_zero] at h_to_real
    -- Rewrite the inner expression using `ENNReal.toReal_div` +
    -- `ENNReal.toReal_ofReal` (with `|t| ≥ 0`).
    have h_eq : (fun t : ℝ =>
        (eLpNorm (qmdRem curve μ g t) 2 μ / ENNReal.ofReal |t|).toReal)
          = fun t : ℝ => (eLpNorm (qmdRem curve μ g t) 2 μ).toReal / |t| := by
      funext t
      rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (abs_nonneg _)]
    rwa [h_eq] at h_to_real
  -- Eventually `MemLp r_t 2 μ` (when `eLpNorm r_t 2 μ < ⊤`).
  have h_evt_memLp : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      MemLp (qmdRem curve μ g t) 2 μ := by
    have h_lt_one : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        eLpNorm (qmdRem curve μ g t) 2 μ / ENNReal.ofReal |t| < 1 :=
      h_qmd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
    have h_ne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 :=
      eventually_nhdsWithin_of_forall (fun _ ht => ht)
    filter_upwards [h_lt_one, h_ne] with t htlt htne
    have habs : (0 : ℝ) < |t| := abs_pos.mpr htne
    have hofreal_ne_zero : ENNReal.ofReal |t| ≠ 0 :=
      (ENNReal.ofReal_pos.mpr habs).ne'
    have hofreal_ne_top : ENNReal.ofReal |t| ≠ ⊤ := ENNReal.ofReal_ne_top
    have h_eLp_lt :
        eLpNorm (qmdRem curve μ g t) 2 μ < ENNReal.ofReal |t| := by
      calc eLpNorm (qmdRem curve μ g t) 2 μ
          = eLpNorm (qmdRem curve μ g t) 2 μ / ENNReal.ofReal |t|
              * ENNReal.ofReal |t| := by
            rw [ENNReal.div_mul_cancel hofreal_ne_zero hofreal_ne_top]
        _ < 1 * ENNReal.ofReal |t| :=
            ENNReal.mul_lt_mul_left hofreal_ne_zero hofreal_ne_top htlt
        _ = ENNReal.ofReal |t| := one_mul _
    have hr_meas : Measurable (qmdRem curve μ g t) := by
      unfold qmdRem
      exact ((((Measure.measurable_rnDeriv (curve t) μ).ennreal_toReal.sqrt).sub
        ((Measure.measurable_rnDeriv (curve 0) μ).ennreal_toReal.sqrt))).sub
        ((measurable_const.mul hg_meas).mul
          (Measure.measurable_rnDeriv (curve 0) μ).ennreal_toReal.sqrt)
    exact ⟨hr_meas.aestronglyMeasurable, lt_trans h_eLp_lt ENNReal.ofReal_lt_top⟩
  -- The pointwise bound `|∫ r_t · √p_0| ≤ (eLpNorm r_t).toReal`.
  have h_bound : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      |∫ ω, qmdRem curve μ g t ω
            * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ|
        ≤ (eLpNorm (qmdRem curve μ g t) 2 μ).toReal := by
    filter_upwards [h_evt_memLp] with t hr_memLp
    have h_cs := AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq
      μ hr_memLp hp0_memLp
    rw [hp0_int_sq, Real.sqrt_one, mul_one] at h_cs
    -- `h_cs : |∫ r_t · √p_0 dμ| ≤ √(∫ r_t² dμ)`. Convert √∫r_t² to (eLpNorm).toReal.
    have h_sqrt_eq : Real.sqrt (∫ ω, qmdRem curve μ g t ω ^ 2 ∂μ)
                    = (eLpNorm (qmdRem curve μ g t) 2 μ).toReal :=
      sqrt_integral_sq_eq_eLpNorm_toReal hr_memLp
    linarith [h_sqrt_eq]
  -- Squeeze: `0 ≤ |∫ r_t · √p_0| / |t| ≤ (eLpNorm r_t).toReal / |t|`,
  -- and the upper bound tends to 0.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_qmd_real ?_ ?_
  · filter_upwards with t
    exact div_nonneg (abs_nonneg _) (abs_nonneg _)
  · filter_upwards [h_bound] with t hb
    -- `|t| ≥ 0`, and we use that division preserves order.
    by_cases ht : |t| = 0
    · simp [ht]
    · have h_pos : (0 : ℝ) < |t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm ht)
      exact (div_le_div_iff_of_pos_right h_pos).mpr hb

/-- Hellinger-affinity bound: `∫ √p_t √p_0 dμ ≤ 1` (Cauchy–Schwarz with
both `√p_t` and `√p_0` of unit `L²(μ)`-norm). -/
private lemma integral_sqrt_pt_sqrt_p0_le_one
    {μ : Measure Ω} [SigmaFinite μ] {curve : ℝ → Measure Ω}
    (h_prob : ∀ t, IsProbabilityMeasure (curve t))
    (h_ac : ∀ t, curve t ≪ μ) (t : ℝ) :
    ∫ ω, Real.sqrt ((curve t).rnDeriv μ ω).toReal
        * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ ≤ 1 := by
  haveI : IsProbabilityMeasure (curve t) := h_prob t
  haveI : IsProbabilityMeasure (curve 0) := h_prob 0
  have hpt : MemLp (fun ω => Real.sqrt ((curve t).rnDeriv μ ω).toReal) 2 μ :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (h_ac t)
  have hp0 : MemLp (fun ω => Real.sqrt ((curve 0).rnDeriv μ ω).toReal) 2 μ :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (h_ac 0)
  have h_cs :=
    AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq μ hpt hp0
  rw [integral_sqrt_rnDeriv_sq_eq_one (h_ac t),
      integral_sqrt_rnDeriv_sq_eq_one (h_ac 0), Real.sqrt_one, mul_one] at h_cs
  -- `h_cs : |∫ √p_t · √p_0 dμ| ≤ 1`. Drop the absolute value since the
  -- integrand is non-negative.
  have h_nn : 0 ≤ ∫ ω, Real.sqrt ((curve t).rnDeriv μ ω).toReal
                * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ :=
    MeasureTheory.integral_nonneg fun _ =>
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc ∫ ω, Real.sqrt ((curve t).rnDeriv μ ω).toReal
          * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ
      = |∫ ω, Real.sqrt ((curve t).rnDeriv μ ω).toReal
            * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ| :=
        (abs_of_nonneg h_nn).symm
    _ ≤ 1 := h_cs

/-! ### Stage-1 engine -/

/-- **Stage 1** (vdV §25.3, lem:25.14, square-integrability part).
The `ℝ≥0∞`-form QMD limit forces `g · √p_0 ∈ L²(μ)`. We pick a *single*
small `t ≠ 0` from the QMD limit with `‖r_t‖_{L²(μ)} < |t|` (in `ℝ≥0∞`),
then read off `(t/2) (g · √p_0) = (√p_t − √p_0) − r_t`, which has each
summand in `L²(μ)`. Dividing by the nonzero scalar `t/2` gives the
result. -/
lemma memLp_two_score_mul_sqrt_of_qmd
    {μ : Measure Ω} [SigmaFinite μ] {curve : ℝ → Measure Ω}
    (h_prob : ∀ t, IsProbabilityMeasure (curve t))
    (h_ac : ∀ t, curve t ≪ μ)
    {g : Ω → ℝ} (hg_meas : Measurable g)
    (h_qmd : IsQMDLimit curve μ g) :
    MemLp (fun ω => g ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal) 2 μ := by
  set f : Ω → ℝ := fun ω => g ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal
    with hf_def
  -- Measurability ingredients (reused throughout).
  have h_pt_meas : ∀ t, Measurable
      (fun ω => Real.sqrt ((curve t).rnDeriv μ ω).toReal) := fun t =>
    (Measure.measurable_rnDeriv (curve t) μ).ennreal_toReal.sqrt
  have hf_meas : Measurable f := hg_meas.mul (h_pt_meas 0)
  -- L²(μ) memberships of `√p_0` and (after picking t) `√p_t`.
  haveI : IsProbabilityMeasure (curve 0) := h_prob 0
  have hp0_memLp : MemLp (fun ω => Real.sqrt ((curve 0).rnDeriv μ ω).toReal) 2 μ :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (h_ac 0)
  -- Step 1: extract a specific `t ≠ 0` with `eLpNorm r_t 2 μ < ENNReal.ofReal |t|`.
  obtain ⟨t, ht_ne, ht_lt⟩ : ∃ t : ℝ, t ≠ 0 ∧
      eLpNorm (qmdRem curve μ g t) 2 μ < ENNReal.ofReal |t| := by
    have h_lt_one : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        eLpNorm (qmdRem curve μ g t) 2 μ / ENNReal.ofReal |t| < 1 :=
      h_qmd.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))
    have h_ne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 :=
      eventually_nhdsWithin_of_forall (fun _ ht => ht)
    have h_combined : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
        t ≠ 0 ∧ eLpNorm (qmdRem curve μ g t) 2 μ < ENNReal.ofReal |t| := by
      filter_upwards [h_lt_one, h_ne] with t htlt htne
      refine ⟨htne, ?_⟩
      have habs : (0 : ℝ) < |t| := abs_pos.mpr htne
      have hofreal_ne_zero : ENNReal.ofReal |t| ≠ 0 :=
        (ENNReal.ofReal_pos.mpr habs).ne'
      have hofreal_ne_top : ENNReal.ofReal |t| ≠ ⊤ := ENNReal.ofReal_ne_top
      calc eLpNorm (qmdRem curve μ g t) 2 μ
          = eLpNorm (qmdRem curve μ g t) 2 μ / ENNReal.ofReal |t|
              * ENNReal.ofReal |t| := by
            rw [ENNReal.div_mul_cancel hofreal_ne_zero hofreal_ne_top]
        _ < 1 * ENNReal.ofReal |t| :=
            ENNReal.mul_lt_mul_left hofreal_ne_zero hofreal_ne_top htlt
        _ = ENNReal.ofReal |t| := one_mul _
    obtain ⟨t, ht⟩ := h_combined.exists
    exact ⟨t, ht.1, ht.2⟩
  -- Set up the `t`-dependent `L²(μ)` ingredients.
  haveI : IsProbabilityMeasure (curve t) := h_prob t
  have hpt_memLp : MemLp (fun ω => Real.sqrt ((curve t).rnDeriv μ ω).toReal) 2 μ :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (h_ac t)
  -- The QMD remainder is measurable.
  have hr_meas : Measurable (qmdRem curve μ g t) := by
    unfold qmdRem
    exact ((h_pt_meas t).sub (h_pt_meas 0)).sub
      (((measurable_const.mul hg_meas).mul (h_pt_meas 0)))
  -- And in L²(μ), since its eLpNorm is finite.
  have hr_memLp : MemLp (qmdRem curve μ g t) 2 μ :=
    ⟨hr_meas.aestronglyMeasurable, lt_trans ht_lt ENNReal.ofReal_lt_top⟩
  -- Pointwise: `(t/2) • f = (√p_t - √p_0) - r_t`.
  have h_tf_eq :
      (fun ω => (t / 2) * f ω)
        = fun ω =>
          (Real.sqrt ((curve t).rnDeriv μ ω).toReal
              - Real.sqrt ((curve 0).rnDeriv μ ω).toReal)
            - qmdRem curve μ g t ω := by
    funext ω
    simp only [qmdRem, hf_def]
    ring
  -- The RHS is in L²(μ).
  have h_tf_memLp : MemLp (fun ω => (t / 2) * f ω) 2 μ := by
    rw [h_tf_eq]
    exact (hpt_memLp.sub hp0_memLp).sub hr_memLp
  -- Divide by `t/2 ≠ 0` to recover MemLp f.
  have ht2_ne : (t / 2) ≠ 0 := by
    intro h; apply ht_ne; linarith
  have h_inv_eq : (fun ω => (2 / t) * ((t / 2) * f ω)) = f := by
    funext ω
    have : (2 / t) * (t / 2) = 1 := by field_simp
    calc (2 / t) * ((t / 2) * f ω)
        = ((2 / t) * (t / 2)) * f ω := by ring
      _ = 1 * f ω := by rw [this]
      _ = f ω := one_mul _
  have h_f_memLp_pre : MemLp (fun ω => (2 / t) * ((t / 2) * f ω)) 2 μ :=
    h_tf_memLp.const_mul (2 / t)
  rwa [h_inv_eq] at h_f_memLp_pre

/-! ### Stage-2 engine -/

/-- **Stage 2** (vdV §25.3, lem:25.14, mean-zero part).
Same hypotheses as Stage 1 plus its conclusion (`g · √p_0 ∈ L²(μ)`)
imply `∫ g d(curve 0) = 0`. Proof via Cauchy–Schwarz on the linear
part of QMD plus the affinity bound and a two-sided sign argument as
`t → 0±`. -/
lemma integral_score_eq_zero_of_qmd
    {μ : Measure Ω} [SigmaFinite μ] {curve : ℝ → Measure Ω}
    (h_prob : ∀ t, IsProbabilityMeasure (curve t))
    (h_ac : ∀ t, curve t ≪ μ)
    {g : Ω → ℝ} (hg_meas : Measurable g)
    (h_g_sqrt : MemLp (fun ω => g ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal) 2 μ)
    (h_qmd : IsQMDLimit curve μ g) :
    ∫ ω, g ω ∂(curve 0) = 0 := by
  haveI : IsProbabilityMeasure (curve 0) := h_prob 0
  set I : ℝ := ∫ ω, g ω ∂(curve 0) with hI_def
  -- Common L²(μ) ingredients.
  have hp0_memLp : MemLp (fun ω => Real.sqrt ((curve 0).rnDeriv μ ω).toReal) 2 μ :=
    AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (h_ac 0)
  have hp0_int_sq : ∫ ω, Real.sqrt ((curve 0).rnDeriv μ ω).toReal ^ 2 ∂μ = 1 :=
    integral_sqrt_rnDeriv_sq_eq_one (h_ac 0)
  -- Pointwise: `(√p_0)² = p_0.toReal`.
  have hp0_sq_pt : ∀ ω, Real.sqrt ((curve 0).rnDeriv μ ω).toReal ^ 2
                        = ((curve 0).rnDeriv μ ω).toReal := fun _ =>
    Real.sq_sqrt ENNReal.toReal_nonneg
  -- ∫g · ((curve 0).rnDeriv μ).toReal dμ = I  (S4 bridge).
  have h_I_eq : ∫ ω, g ω * ((curve 0).rnDeriv μ ω).toReal ∂μ = I :=
    (AsymptoticStatistics.ForMathlib.RnDerivSqrt.integral_eq_integral_mul_rnDeriv_of_ac
      (h_ac 0) g).symm
  -- Algebraic identity for any `t : ℝ`:
  --   ∫ r_t · √p_0 dμ = ∫ √p_t · √p_0 dμ − 1 − (t/2) · I.
  have h_id : ∀ t : ℝ,
      ∫ ω, qmdRem curve μ g t ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ
        = (∫ ω, Real.sqrt ((curve t).rnDeriv μ ω).toReal
              * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ)
          - 1 - (t / 2) * I := by
    intro t
    haveI : IsProbabilityMeasure (curve t) := h_prob t
    have hpt_memLp : MemLp (fun ω => Real.sqrt ((curve t).rnDeriv μ ω).toReal) 2 μ :=
      AsymptoticStatistics.ForMathlib.RnDerivSqrt.memLp_sqrt_rnDeriv (h_ac t)
    -- Integrability ingredients.
    have h_pt_p0_int :
        Integrable (fun ω => Real.sqrt ((curve t).rnDeriv μ ω).toReal
            * Real.sqrt ((curve 0).rnDeriv μ ω).toReal) μ :=
      AsymptoticStatistics.L2Utils.integrable_mul_of_memLp_two μ hpt_memLp hp0_memLp
    have h_p0_sq_int :
        Integrable (fun ω => Real.sqrt ((curve 0).rnDeriv μ ω).toReal ^ 2) μ :=
      hp0_memLp.integrable_sq
    -- `g · (√p_0)² = (g · √p_0) · √p_0` is in L¹(μ) by Hölder L²×L²→L¹.
    have h_g_p0_sq_int :
        Integrable (fun ω => g ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ^ 2) μ := by
      have h_via :
          (fun ω => g ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ^ 2)
            = fun ω =>
              (g ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal)
                * Real.sqrt ((curve 0).rnDeriv μ ω).toReal := by
        funext ω; ring
      rw [h_via]
      exact AsymptoticStatistics.L2Utils.integrable_mul_of_memLp_two μ h_g_sqrt hp0_memLp
    -- Pointwise rewrite the integrand to a *single* outer subtraction:
    -- `r_t · √p_0 = (√p_t · √p_0) - ((√p_0)² + (t/2) · g · (√p_0)²)`.
    have h_pw : (fun ω => qmdRem curve μ g t ω
                  * Real.sqrt ((curve 0).rnDeriv μ ω).toReal)
        = (fun ω =>
            Real.sqrt ((curve t).rnDeriv μ ω).toReal
              * Real.sqrt ((curve 0).rnDeriv μ ω).toReal
            - (Real.sqrt ((curve 0).rnDeriv μ ω).toReal ^ 2
              + (t / 2) *
                (g ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ^ 2))) := by
      funext ω; simp only [qmdRem]; ring
    -- Apply linearity in two steps: outer `integral_sub`, then `integral_add`,
    -- then `integral_const_mul`.
    have h_g_p0_sq_eq_I :
        ∫ ω, g ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ^ 2 ∂μ = I := by
      have h_eq_pt : (fun ω => g ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ^ 2)
                    = (fun ω => g ω * ((curve 0).rnDeriv μ ω).toReal) := by
        funext ω; rw [hp0_sq_pt]
      rw [h_eq_pt, h_I_eq]
    -- Type-ascribe the combined integrability hypothesis pointwise.
    have h_combined_int :
        Integrable (fun ω => Real.sqrt ((curve 0).rnDeriv μ ω).toReal ^ 2
            + (t / 2) * (g ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ^ 2)) μ :=
      h_p0_sq_int.add (h_g_p0_sq_int.const_mul (t / 2))
    rw [h_pw, integral_sub h_pt_p0_int h_combined_int,
        integral_add h_p0_sq_int (h_g_p0_sq_int.const_mul (t / 2)),
        integral_const_mul, hp0_int_sq, h_g_p0_sq_eq_I]
    ring
  -- Master inequality: `(t/2) · I ≤ |∫ r_t · √p_0 dμ|` for all `t`.
  have h_bound : ∀ t : ℝ, (t / 2) * I
      ≤ |∫ ω, qmdRem curve μ g t ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ| := by
    intro t
    have h_aff := integral_sqrt_pt_sqrt_p0_le_one h_prob h_ac t
    have h_neg_C_le :
        -(∫ ω, qmdRem curve μ g t ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ)
        ≤ |∫ ω, qmdRem curve μ g t ω * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ| :=
      neg_le_abs _
    linarith [h_id t]
  -- Cross-term tendsto and its scaled version.
  have h_cross := integral_qmdRem_mul_sqrt_p0_isLittleO
    h_prob h_ac hg_meas h_g_sqrt h_qmd
  have h_cross2 : Tendsto
      (fun t : ℝ =>
        2 * (|∫ ω, qmdRem curve μ g t ω
                  * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ| / |t|))
      (𝓝[≠] 0) (𝓝 0) := by
    have := h_cross.const_mul 2
    simpa using this
  -- Step `I ≤ 0` (use `t > 0`).
  have h_I_le_zero : I ≤ 0 := by
    have h_cross_pos : Tendsto
        (fun t : ℝ =>
          2 * (|∫ ω, qmdRem curve μ g t ω
                    * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ| / |t|))
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      h_cross2.mono_left (nhdsWithin_mono _ (fun _ h => h.ne'))
    have h_evt : ∀ᶠ t in 𝓝[>] (0 : ℝ),
        I ≤ 2 * (|∫ ω, qmdRem curve μ g t ω
                    * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ| / |t|) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos : 0 < t := ht
      have h_t2_pos : 0 < t / 2 := by linarith
      have h_abs_t : |t| = t := abs_of_pos htpos
      have hb := h_bound t
      -- (t/2) · I ≤ |C(t)|. Divide by t/2 > 0:
      have h_div : I ≤
          |∫ ω, qmdRem curve μ g t ω
                * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ| / (t / 2) := by
        rw [le_div_iff₀ h_t2_pos]; linarith
      -- 2|C|/|t| = 2|C|/t = |C|/(t/2):
      have h_two_eq :
          2 * (|∫ ω, qmdRem curve μ g t ω
                    * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ| / |t|)
            = |∫ ω, qmdRem curve μ g t ω
                    * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ| / (t / 2) := by
        rw [h_abs_t]; ring
      rw [h_two_eq]; exact h_div
    exact ge_of_tendsto h_cross_pos h_evt
  -- Step `0 ≤ I` (use `t < 0`).
  have h_I_ge_zero : 0 ≤ I := by
    have h_cross_neg : Tendsto
        (fun t : ℝ =>
          -(2 * (|∫ ω, qmdRem curve μ g t ω
                      * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ| / |t|)))
        (𝓝[<] (0 : ℝ)) (𝓝 0) := by
      have h_left : Tendsto
          (fun t : ℝ =>
            2 * (|∫ ω, qmdRem curve μ g t ω
                      * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ| / |t|))
          (𝓝[<] (0 : ℝ)) (𝓝 0) :=
        h_cross2.mono_left (nhdsWithin_mono _ (fun _ h => h.ne))
      simpa using h_left.neg
    have h_evt : ∀ᶠ t in 𝓝[<] (0 : ℝ),
        -(2 * (|∫ ω, qmdRem curve μ g t ω
                    * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ| / |t|)) ≤ I := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htneg : t < 0 := ht
      have h_t2_neg : t / 2 < 0 := by linarith
      have h_abs_t : |t| = -t := abs_of_neg htneg
      have hb := h_bound t
      -- (t/2) · I ≤ |C|. Divide by t/2 < 0 flips:
      have h_div : |∫ ω, qmdRem curve μ g t ω
                  * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ| / (t / 2) ≤ I := by
        rw [div_le_iff_of_neg h_t2_neg]; linarith
      -- -2|C|/|t| = -2|C|/(-t) = 2|C|/t = |C|/(t/2):
      have ht_ne : t ≠ 0 := ne_of_lt htneg
      have h_neg_two_eq :
          -(2 * (|∫ ω, qmdRem curve μ g t ω
                      * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ| / |t|))
            = |∫ ω, qmdRem curve μ g t ω
                    * Real.sqrt ((curve 0).rnDeriv μ ω).toReal ∂μ| / (t / 2) := by
        rw [h_abs_t]; field_simp
      rw [h_neg_two_eq]; exact h_div
    exact le_of_tendsto h_cross_neg h_evt
  linarith

end AsymptoticStatistics.ForMathlib.QMDAnalytic
