module
public import StatLean.AsymptoticStatistics.DQM.Properties
public import StatLean.AsymptoticStatistics.ForMathlib.DifferentiableInProbability
public import StatLean.AsymptoticStatistics.ForMathlib.LogTaylor
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-!
# DQM and differentiability in probability of the log density

This file records the probability-level bridge used in van der Vaart,
*Asymptotic Statistics*, Theorem 5.39: differentiability in quadratic mean
implies differentiability in probability of the log-density criterion, with
derivative given by the score.

The bridge does not assume strict positivity of nearby densities.  The proof
must isolate the zero-density exceptional sets and use DQM to show that they
vanish in probability under the true distribution.
-/

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace AsymptoticStatistics

private lemma log_sq_ratio_sub_linear_le_sq {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (hR : |ForMathlib.logTaylorRemainder (2 * (a / b - 1))| ≤ 1) :
    |Real.log (a ^ 2) - Real.log (b ^ 2) - 2 * (a / b - 1)|
      ≤ (2 * (a / b - 1)) ^ 2 := by
  have hx : -1 < a / b - 1 := by
    nlinarith [div_pos ha hb]
  have ht := ForMathlib.log_one_add_eq_taylor hx
  have hlog : Real.log (a ^ 2) - Real.log (b ^ 2) =
      2 * Real.log (1 + (a / b - 1)) := by
    have hab : 1 + (a / b - 1) = a / b := by ring
    rw [Real.log_pow, Real.log_pow, hab, Real.log_div ha.ne' hb.ne']
    ring
  rw [hlog, ht]
  have hbound :
      |-(2 * (a / b - 1)) ^ 2 / 4
          + (2 * (a / b - 1)) ^ 2 / 2 *
              ForMathlib.logTaylorRemainder (2 * (a / b - 1))|
        ≤ (2 * (a / b - 1)) ^ 2 := by
    calc
      |-(2 * (a / b - 1)) ^ 2 / 4
          + (2 * (a / b - 1)) ^ 2 / 2 *
              ForMathlib.logTaylorRemainder (2 * (a / b - 1))|
          ≤ (2 * (a / b - 1)) ^ 2 / 4
              + (2 * (a / b - 1)) ^ 2 / 2 *
                  |ForMathlib.logTaylorRemainder (2 * (a / b - 1))| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg _),
              abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_mul, abs_div,
              abs_of_nonneg (sq_nonneg _),
              abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ (2 * (a / b - 1)) ^ 2 / 4
              + (2 * (a / b - 1)) ^ 2 / 2 := by
                have hcoef : 0 ≤ (2 * (a / b - 1)) ^ 2 / 2 :=
                  div_nonneg (sq_nonneg _) (by norm_num)
                exact add_le_add le_rfl (by
                  simpa only [mul_one] using mul_le_mul_of_nonneg_left hR hcoef)
      _ ≤ (2 * (a / b - 1)) ^ 2 := by nlinarith [sq_nonneg (2 * (a / b - 1))]
  convert hbound using 1
  all_goals ring_nf

/-- The elementary L²-to-probability implication in the exact integral form
used below.  Kept private because the public reusable API is
`tendstoInMeasure_of_tendsto_eLpNorm`. -/
private lemma tendstoInMeasure_zero_of_integral_sq
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {l : Filter ι} {f : ι → Ω → ℝ}
    (hmem : ∀ᶠ i in l, MemLp (f i) 2 P)
    (hint : Tendsto (fun i => ∫ ω, (f i ω) ^ 2 ∂P) l (𝓝 0)) :
    TendstoInMeasure P f l (fun _ => 0) := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hupper : Tendsto (fun i => (ε ^ 2)⁻¹ * ∫ ω, (f i ω) ^ 2 ∂P) l (𝓝 0) := by
    simpa using hint.const_mul (ε ^ 2)⁻¹
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ => measureReal_nonneg) ?_
  filter_upwards [hmem] with i hi
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := fun ω => (f i ω) ^ 2)
    (Eventually.of_forall fun _ => sq_nonneg _) hi.integrable_sq (ε ^ 2)
  have hset : {ω | ε ≤ ‖f i ω - 0‖} = {ω | ε ^ 2 ≤ (f i ω) ^ 2} := by
    ext ω
    simp only [Set.mem_setOf_eq, sub_zero, Real.norm_eq_abs]
    constructor
    · intro h
      have hs := (sq_le_sq₀ hε.le (abs_nonneg _)).2 h
      simpa [sq_abs] using hs
    · intro h
      have hs : ε ^ 2 ≤ |f i ω| ^ 2 := by simpa [sq_abs] using h
      exact (sq_le_sq₀ hε.le (abs_nonneg _)).1 hs
  rw [hset]
  rw [← le_div_iff₀' (sq_pos_of_pos hε)] at hmarkov
  simpa [div_eq_inv_mul] using hmarkov

private lemma dqm_score_integral_le_const_norm_sq
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) (θ₀ : Θ) (ℓ : 𝓧 → Θ)
    (hpdf : IsPDFOf M μ) (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Θ,
      ∫ x, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ ≤ C * ‖h‖ ^ 2 := by
  have hrate := (Asymptotics.isLittleO_iff.mp hDQM.isLittleO)
    (show (0 : ℝ) < 1 by norm_num)
  have hlocal : ∀ᶠ h in 𝓝 (0 : Θ),
      MemLp (fun x => M.sqrtDensity (θ₀ + h) x - M.sqrtDensity θ₀ x
        - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) 2 μ ∧
      ∫ x, (M.sqrtDensity (θ₀ + h) x - M.sqrtDensity θ₀ x
        - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ ≤ ‖h‖ ^ 2 := by
    filter_upwards [hDQM.mem, hrate] with h hmem hrate_h
    refine ⟨hmem, ?_⟩
    exact (le_abs_self _).trans (by
      simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖h‖)] using hrate_h)
  rw [Metric.eventually_nhds_iff] at hlocal
  obtain ⟨δ, hδ, hlocal⟩ := hlocal
  let C : ℝ := (32 + 2 * δ ^ 2) * 4 / δ ^ 2
  refine ⟨C, by positivity, fun h => ?_⟩
  by_cases hh : h = 0
  · subst h
    simp
  let c : ℝ := δ / (2 * ‖h‖)
  have hc : 0 < c := div_pos hδ (mul_pos two_pos (norm_pos_iff.mpr hh))
  have hcu : dist (c • h) 0 < δ := by
    rw [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    dsimp [c]
    field_simp [norm_ne_zero_iff.mpr hh]
    linarith
  have hloc := hlocal hcu
  obtain ⟨hrem_mem, hrem_bd⟩ := hloc
  let rem : 𝓧 → ℝ := fun x => M.sqrtDensity (θ₀ + c • h) x - M.sqrtDensity θ₀ x
    - (1 / 2 : ℝ) * ⟪c • h, ℓ x⟫ * M.sqrtDensity θ₀ x
  have hscore_int : Integrable (fun x => ⟪c • h, ℓ x⟫ ^ 2 * M.density θ₀ x) μ :=
    dqm_fisher_integrable M μ θ₀ ℓ (hpdf.density_integrable θ₀) hDQM (c • h)
      (fun t => hpdf.density_integrable _)
  have hden1_int : Integrable (fun x => 16 * M.density (θ₀ + c • h) x) μ :=
    (hpdf.density_integrable _).const_mul 16
  have hden0_int : Integrable (fun x => 16 * M.density θ₀ x) μ :=
    (hpdf.density_integrable θ₀).const_mul 16
  have hrem8_int : Integrable (fun x => 8 * rem x ^ 2) μ := by
    simpa only [rem] using hrem_mem.integrable_sq.const_mul 8
  have hmajor_int : Integrable (fun x =>
      16 * M.density (θ₀ + c • h) x + 16 * M.density θ₀ x + 8 * rem x ^ 2) μ :=
    (hden1_int.add hden0_int).add hrem8_int
  have hpoint : ∀ x,
      ⟪c • h, ℓ x⟫ ^ 2 * M.density θ₀ x ≤
        16 * M.density (θ₀ + c • h) x + 16 * M.density θ₀ x + 8 * rem x ^ 2 := by
    intro x
    have hs0 := M.sqrtDensity_sq θ₀ x
    have hs1 := M.sqrtDensity_sq (θ₀ + c • h) x
    rw [← hs0, ← hs1]
    dsimp [rem]
    nlinarith [sq_nonneg (M.sqrtDensity (θ₀ + c • h) x - M.sqrtDensity θ₀ x),
      sq_nonneg (M.sqrtDensity (θ₀ + c • h) x),
      sq_nonneg (M.sqrtDensity θ₀ x),
      sq_nonneg (M.sqrtDensity (θ₀ + c • h) x - M.sqrtDensity θ₀ x
        - (1 / 2 : ℝ) * ⟪c • h, ℓ x⟫ * M.sqrtDensity θ₀ x),
      sq_nonneg (M.sqrtDensity (θ₀ + c • h) x + M.sqrtDensity θ₀ x),
      sq_nonneg (M.sqrtDensity (θ₀ + c • h) x - M.sqrtDensity θ₀ x
        + (M.sqrtDensity (θ₀ + c • h) x - M.sqrtDensity θ₀ x
          - (1 / 2 : ℝ) * ⟪c • h, ℓ x⟫ * M.sqrtDensity θ₀ x))]
  have hint_bd := integral_mono hscore_int hmajor_int hpoint
  have hAB_eq :
      (∫ x, 16 * M.density (θ₀ + c • h) x + 16 * M.density θ₀ x ∂μ) =
        (∫ x, 16 * M.density (θ₀ + c • h) x ∂μ) +
          ∫ x, 16 * M.density θ₀ x ∂μ := by
    simpa only [Pi.add_apply] using integral_add hden1_int hden0_int
  have hABC_eq :
      (∫ x, 16 * M.density (θ₀ + c • h) x + 16 * M.density θ₀ x
          + 8 * rem x ^ 2 ∂μ) =
        (∫ x, 16 * M.density (θ₀ + c • h) x + 16 * M.density θ₀ x ∂μ) +
          ∫ x, 8 * rem x ^ 2 ∂μ := by
    simpa only [Pi.add_apply] using integral_add (hden1_int.add hden0_int) hrem8_int
  rw [hABC_eq, hAB_eq, integral_const_mul, integral_const_mul,
    integral_const_mul, hpdf.density_integral_eq_one,
    hpdf.density_integral_eq_one] at hint_bd
  simp only [rem] at hint_bd
  have hsmall : ∫ x, ⟪c • h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ ≤ 32 + 2 * δ ^ 2 := by
    calc
      _ ≤ 32 + 8 * ∫ x, (M.sqrtDensity (θ₀ + c • h) x - M.sqrtDensity θ₀ x
            - (1 / 2 : ℝ) * ⟪c • h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ := by
              linarith
      _ ≤ 32 + 8 * ‖c • h‖ ^ 2 := by gcongr
      _ = 32 + 2 * δ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
        dsimp [c]
        field_simp [norm_ne_zero_iff.mpr hh]
        ring
  have hscale : ∫ x, ⟪c • h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ =
      c ^ 2 * ∫ x, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [real_inner_smul_left]
    ring
  rw [hscale] at hsmall
  have hsmall' : ∫ x, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ ≤
      (32 + 2 * δ ^ 2) / c ^ 2 :=
    (le_div_iff₀' (sq_pos_of_pos hc)).2 (by simpa [mul_comm] using hsmall)
  calc
    ∫ x, ⟪h, ℓ x⟫ ^ 2 * M.density θ₀ x ∂μ
        ≤ (32 + 2 * δ ^ 2) / c ^ 2 := hsmall'
    _ = C * ‖h‖ ^ 2 := by
      dsimp [C, c]
      field_simp [hδ.ne', norm_ne_zero_iff.mpr hh]
      ring

namespace ParametricFamily

/-- The real log density `log p_theta(x)` used as the MLE criterion in vdV
Theorem 5.39.

Edge behavior: Mathlib defines `Real.log 0 = 0`.  At the true parameter this
convention changes the function only where `p_theta0 = 0`, a null set under
the true density.  For nearby parameters the DQM-to-probability bridge below
handles their zero sets as exceptional events; it does not assume strict
positivity. -/
noncomputable def logDensity
    {𝓧 : Type*} [MeasurableSpace 𝓧] {Θ : Type*}
    (M : ParametricFamily 𝓧 Θ) (θ : Θ) (x : 𝓧) : ℝ :=
  Real.log (M.density θ x)

end ParametricFamily

/-- DQM implies differentiability in probability of the log density, with
samplewise derivative given canonically by the score inner-product functional.

This is the probability-differentiability step in the proof of vdV Theorem
5.39 (p.65).  No sigma-finiteness, strict-positivity, or local Lipschitz
assumption is needed for this bridge; the local Lipschitz envelope enters only
in the later upgrade from convergence in probability to `L2` convergence. -/
theorem dqm_logDensity_differentiableInProbabilityAt
    {𝓧 : Type*} [MeasurableSpace 𝓧]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) (θ₀ : Θ) (ℓ : 𝓧 → Θ)
    -- The family consists of probability densities with respect to `μ`.
    (hpdf : IsPDFOf M μ)
    -- vdV's differentiability-in-quadratic-mean assumption at `θ₀`.
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ) :
    DifferentiableInProbabilityAt
      (μ.withDensity (fun x => ENNReal.ofReal (M.density θ₀ x)))
      (fun θ => M.logDensity θ)
      (fun x => innerSL ℝ (ℓ x)) θ₀ := by
  let P₀ : Measure 𝓧 := μ.withDensity (fun x => ENNReal.ofReal (M.density θ₀ x))
  let r : Θ → 𝓧 → ℝ := fun θ x =>
    M.sqrtDensity θ x - M.sqrtDensity θ₀ x
      - (1 / 2 : ℝ) * ⟪θ - θ₀, ℓ x⟫ * M.sqrtDensity θ₀ x
  let W : Θ → 𝓧 → ℝ := fun θ x =>
    2 * (M.sqrtDensity θ x - M.sqrtDensity θ₀ x) / M.sqrtDensity θ₀ x
  let z : Θ → 𝓧 → ℝ := fun θ x => ⟪θ - θ₀, ℓ x⟫
  let s : Θ → ℝ := fun θ => ‖θ - θ₀‖
  letI : IsFiniteMeasure P₀ :=
    isFiniteMeasure_withDensity_ofReal (hpdf.density_integrable θ₀).hasFiniteIntegral
  have hshift : Tendsto (fun θ : Θ => θ - θ₀) (𝓝[≠] θ₀) (𝓝[≠] (0 : Θ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have ht : Tendsto (fun θ : Θ => θ - θ₀) (𝓝 θ₀) (𝓝 0) := by
        simpa using!
          (continuous_id.sub (continuous_const : Continuous (fun _ : Θ => θ₀))).tendsto θ₀
      exact ht.mono_left nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    simpa [Set.mem_compl_iff, sub_ne_zero] using hθ
  have hres_ratio_zero : Tendsto
      (fun θ => (s θ)⁻¹ ^ 2 * ∫ x, r θ x ^ 2 ∂μ)
      (𝓝[≠] θ₀) (𝓝 0) := by
    have hzero : Tendsto
        (fun h : Θ => ‖h‖⁻¹ ^ 2 *
          ∫ x, (M.sqrtDensity (θ₀ + h) x - M.sqrtDensity θ₀ x
            - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ)
        (𝓝[≠] (0 : Θ)) (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hrate := (Asymptotics.isLittleO_iff.mp hDQM.isLittleO) (half_pos hε)
      filter_upwards [hrate.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with h hrate_h hh
      rw [Real.dist_eq, sub_zero, abs_of_nonneg]
      · have hh0 : h ≠ 0 := by simpa [Set.mem_compl_iff] using hh
        have hnn : 0 ≤ ∫ x, (M.sqrtDensity (θ₀ + h) x - M.sqrtDensity θ₀ x
            - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ :=
          integral_nonneg fun _ => sq_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg ‖h‖)] at hrate_h
        calc
          ‖h‖⁻¹ ^ 2 * ∫ x, (M.sqrtDensity (θ₀ + h) x - M.sqrtDensity θ₀ x
              - (1 / 2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ₀ x) ^ 2 ∂μ
              ≤ ‖h‖⁻¹ ^ 2 * ((ε / 2) * ‖h‖ ^ 2) :=
                mul_le_mul_of_nonneg_left hrate_h (sq_nonneg _)
          _ = ε / 2 := by field_simp [norm_ne_zero_iff.mpr hh0]
          _ < ε := half_lt_self hε
      · exact mul_nonneg (sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    convert hzero.comp hshift using 1
    funext θ
    simp only [s, r, Function.comp_apply]
    congr 2
    ext x
    rw [add_comm θ₀, sub_add_cancel]
  obtain ⟨C, hC, hscore_bd⟩ :=
    dqm_score_integral_le_const_norm_sq M μ θ₀ ℓ hpdf hDQM
  have hr_mem : ∀ᶠ θ in 𝓝[≠] θ₀, MemLp (r θ) 2 μ := by
    have := (hshift.mono_right nhdsWithin_le_nhds).eventually hDQM.mem
    filter_upwards [this] with θ hθ
    simpa only [r, add_comm θ₀, sub_add_cancel] using hθ
  have hW_meas (θ : Θ) : Measurable (W θ) := by
    exact (((M.sqrtDensity_meas θ).sub (M.sqrtDensity_meas θ₀)).const_mul 2).div
      (M.sqrtDensity_meas θ₀)
  have hbase_pos : ∀ᵐ x ∂P₀, 0 < M.sqrtDensity θ₀ x := by
    change ∀ᵐ x ∂μ.withDensity (fun x => ENNReal.ofReal (M.density θ₀ x)),
      0 < M.sqrtDensity θ₀ x
    rw [ae_withDensity_iff (M.density_meas θ₀).ennreal_ofReal]
    filter_upwards with x
    intro hx
    have hpne : M.density θ₀ x ≠ 0 := by
      intro hp0
      simp [hp0] at hx
    have hp : 0 < M.density θ₀ x :=
      lt_of_le_of_ne (M.density_nonneg θ₀ x) (Ne.symm hpne)
    exact Real.sqrt_pos.mpr hp
  have hW_mem (θ : Θ) (hrem : MemLp (r θ) 2 μ) : MemLp (W θ) 2 P₀ := by
    change MemLp (W θ) 2
      (μ.withDensity (fun x => ENNReal.ofReal (M.density θ₀ x)))
    refine (memLp_two_iff_integrable_sq (hW_meas θ).aestronglyMeasurable).2 ?_
    rw [integrable_withDensity_iff (M.density_meas θ₀).ennreal_ofReal (by simp)]
    let d : 𝓧 → ℝ := fun x => M.sqrtDensity θ x - M.sqrtDensity θ₀ x
    have hd_mem : MemLp d 2 μ :=
      (M.sqrtDensity_memLp_two μ θ (hpdf.density_integrable θ)).sub
        (M.sqrtDensity_memLp_two μ θ₀ (hpdf.density_integrable θ₀))
    have hmajor : Integrable (fun x => 4 * d x ^ 2) μ := hd_mem.integrable_sq.const_mul 4
    refine hmajor.mono (((hW_meas θ).pow_const 2).mul
      ((M.density_meas θ₀).ennreal_ofReal.ennreal_toReal) |>.aestronglyMeasurable) ?_
    filter_upwards with x
    have hs0 := M.sqrtDensity_sq θ₀ x
    rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x)]
    by_cases hb : M.sqrtDensity θ₀ x = 0
    · have hp0 : M.density θ₀ x = 0 := by simpa [hb] using hs0.symm
      rw [hp0]
      simp only [mul_zero, norm_zero]
      exact norm_nonneg _
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg, abs_of_nonneg]
      · dsimp [W, d]
        rw [← hs0]
        field_simp [hb]
        ring_nf
        exact le_rfl
      · exact mul_nonneg (by norm_num) (sq_nonneg _)
      · exact mul_nonneg (sq_nonneg (W θ x)) (M.density_nonneg θ₀ x)
  have hW_integral_bd (θ : Θ) (hrem : MemLp (r θ) 2 μ) :
      ∫ x, W θ x ^ 2 ∂P₀ ≤
        8 * ∫ x, r θ x ^ 2 ∂μ + 2 * C * s θ ^ 2 := by
    have hW2_int := (hW_mem θ hrem).integrable_sq
    have hscore_int : Integrable (fun x => z θ x ^ 2 * M.density θ₀ x) μ :=
      dqm_fisher_integrable M μ θ₀ ℓ (hpdf.density_integrable θ₀) hDQM (θ - θ₀)
        (fun t => hpdf.density_integrable _)
    have hmajor_int : Integrable (fun x => 8 * r θ x ^ 2
        + 2 * (z θ x ^ 2 * M.density θ₀ x)) μ :=
      (hrem.integrable_sq.const_mul 8).add (hscore_int.const_mul 2)
    change (∫ x, W θ x ^ 2 ∂μ.withDensity
      (fun x => ENNReal.ofReal (M.density θ₀ x))) ≤ _
    rw [integral_withDensity_eq_integral_toReal_smul
      (M.density_meas θ₀).ennreal_ofReal (by simp)]
    have hweighted_int : Integrable (fun x =>
        (ENNReal.ofReal (M.density θ₀ x)).toReal * W θ x ^ 2) μ := by
      simpa [mul_comm] using
        (integrable_withDensity_iff (M.density_meas θ₀).ennreal_ofReal (by simp)).mp hW2_int
    have hmono : ∫ x, (ENNReal.ofReal (M.density θ₀ x)).toReal * W θ x ^ 2 ∂μ
        ≤ ∫ x, (8 * r θ x ^ 2 + 2 * (z θ x ^ 2 * M.density θ₀ x)) ∂μ := by
      refine integral_mono hweighted_int hmajor_int fun x => ?_
      rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x)]
      have hs0 := M.sqrtDensity_sq θ₀ x
      by_cases hb : M.sqrtDensity θ₀ x = 0
      · have hp0 : M.density θ₀ x = 0 := by simpa [hb] using hs0.symm
        rw [hp0]
        simp only [mul_zero, zero_mul, add_zero]
        exact mul_nonneg (by norm_num) (sq_nonneg _)
      · dsimp [W, z, r]
        rw [← hs0]
        field_simp [hb]
        nlinarith [sq_nonneg (M.sqrtDensity θ x - M.sqrtDensity θ₀ x
          - (1 / 2 : ℝ) * ⟪θ - θ₀, ℓ x⟫ * M.sqrtDensity θ₀ x),
          sq_nonneg (M.sqrtDensity θ x - M.sqrtDensity θ₀ x
            - ⟪θ - θ₀, ℓ x⟫ * M.sqrtDensity θ₀ x)]
    rw [integral_add, integral_const_mul, integral_const_mul] at hmono
    · calc
        ∫ x, (ENNReal.ofReal (M.density θ₀ x)).toReal • W θ x ^ 2 ∂μ
            ≤ 8 * ∫ x, r θ x ^ 2 ∂μ
                + 2 * ∫ x, z θ x ^ 2 * M.density θ₀ x ∂μ := by
                  simpa [smul_eq_mul, mul_comm] using hmono
        _ ≤ 8 * ∫ x, r θ x ^ 2 ∂μ + 2 * (C * ‖θ - θ₀‖ ^ 2) := by
              gcongr
              exact hscore_bd (θ - θ₀)
        _ = 8 * ∫ x, r θ x ^ 2 ∂μ + 2 * C * s θ ^ 2 := by
              simp only [s]
              ring
    · exact hrem.integrable_sq.const_mul 8
    · exact hscore_int.const_mul 2
  have hs_zero : Tendsto s (𝓝[≠] θ₀) (𝓝 0) := by
    have ht : Tendsto (fun θ : Θ => ‖θ - θ₀‖) (𝓝 θ₀) (𝓝 0) := by
      simpa using! (continuous_norm.comp
        (continuous_id.sub (continuous_const : Continuous (fun _ : Θ => θ₀)))).tendsto θ₀
    exact ht.mono_left nhdsWithin_le_nhds
  have hres_zero : Tendsto (fun θ => ∫ x, r θ x ^ 2 ∂μ) (𝓝[≠] θ₀) (𝓝 0) := by
    have hprod : Tendsto
        (fun θ => ((s θ)⁻¹ ^ 2 * ∫ x, r θ x ^ 2 ∂μ) * s θ ^ 2)
        (𝓝[≠] θ₀) (𝓝 0) := by
      simpa using hres_ratio_zero.mul (hs_zero.pow 2)
    refine hprod.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hs_ne : s θ ≠ 0 := by
      have hne : θ ≠ θ₀ := by simpa [Set.mem_compl_iff] using hθ
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
    field_simp [hs_ne]
  have hW_mem_ev : ∀ᶠ θ in 𝓝[≠] θ₀, MemLp (W θ) 2 P₀ := by
    filter_upwards [hr_mem] with θ hrem
    exact hW_mem θ hrem
  have hW_sq_zero : Tendsto (fun θ => ∫ x, W θ x ^ 2 ∂P₀)
      (𝓝[≠] θ₀) (𝓝 0) := by
    have hu : Tendsto (fun θ =>
        8 * ∫ x, r θ x ^ 2 ∂μ + 2 * C * s θ ^ 2) (𝓝[≠] θ₀) (𝓝 0) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (hres_zero.const_mul 8).add ((hs_zero.pow 2).const_mul (2 * C))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) ?_
    filter_upwards [hr_mem] with θ hrem
    exact hW_integral_bd θ hrem
  have hW_prob : TendstoInMeasure P₀ W (𝓝[≠] θ₀) (fun _ => 0) :=
    tendstoInMeasure_zero_of_integral_sq hW_mem_ev hW_sq_zero
  let V : Θ → 𝓧 → ℝ := fun θ x => (Real.sqrt (s θ))⁻¹ * W θ x
  have hV_meas (θ : Θ) : Measurable (V θ) := (hW_meas θ).const_mul _
  have hV_mem_ev : ∀ᶠ θ in 𝓝[≠] θ₀, MemLp (V θ) 2 P₀ := by
    filter_upwards [hW_mem_ev] with θ hmem
    exact hmem.const_mul _
  have hV_sq_zero : Tendsto (fun θ => ∫ x, V θ x ^ 2 ∂P₀)
      (𝓝[≠] θ₀) (𝓝 0) := by
    have hupper_zero : Tendsto (fun θ =>
        8 * ((s θ)⁻¹ ^ 2 * ∫ x, r θ x ^ 2 ∂μ) * s θ
          + 2 * C * s θ) (𝓝[≠] θ₀) (𝓝 0) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        ((hres_ratio_zero.mul hs_zero).const_mul 8).add (hs_zero.const_mul (2 * C))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_zero
      (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) ?_
    filter_upwards [hr_mem, self_mem_nhdsWithin] with θ hrem hθ
    have hs_pos : 0 < s θ := by
      have hne : θ ≠ θ₀ := by simpa [Set.mem_compl_iff] using hθ
      simpa [s, norm_pos_iff, sub_ne_zero] using hne
    have hsqrt_pos : 0 < Real.sqrt (s θ) := Real.sqrt_pos.mpr hs_pos
    have hVeq : ∫ x, V θ x ^ 2 ∂P₀ = (s θ)⁻¹ * ∫ x, W θ x ^ 2 ∂P₀ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp [V]
      rw [mul_pow, inv_pow, Real.sq_sqrt hs_pos.le]
    rw [hVeq]
    calc
      (s θ)⁻¹ * ∫ x, W θ x ^ 2 ∂P₀
          ≤ (s θ)⁻¹ * (8 * ∫ x, r θ x ^ 2 ∂μ + 2 * C * s θ ^ 2) :=
            mul_le_mul_of_nonneg_left (hW_integral_bd θ hrem) (inv_nonneg.mpr hs_pos.le)
      _ = 8 * ((s θ)⁻¹ ^ 2 * ∫ x, r θ x ^ 2 ∂μ) * s θ
          + 2 * C * s θ := by field_simp [hs_pos.ne']
  have hV_prob : TendstoInMeasure P₀ V (𝓝[≠] θ₀) (fun _ => 0) :=
    tendstoInMeasure_zero_of_integral_sq hV_mem_ev hV_sq_zero
  let q : Θ → 𝓧 → ℝ := fun θ x => (s θ)⁻¹ * (W θ x - z θ x)
  let qg : Θ → 𝓧 → ℝ := fun θ x =>
    2 * (s θ)⁻¹ * r θ x / M.sqrtDensity θ₀ x
  have hq_data : ∀ᶠ θ in 𝓝[≠] θ₀,
      MemLp (q θ) 2 P₀ ∧ ∫ x, q θ x ^ 2 ∂P₀ ≤
        4 * ((s θ)⁻¹ ^ 2 * ∫ x, r θ x ^ 2 ∂μ) := by
    filter_upwards [hr_mem, self_mem_nhdsWithin] with θ hrem hθ
    have hs_ne : s θ ≠ 0 := by
      have hne : θ ≠ θ₀ := by simpa [Set.mem_compl_iff] using hθ
      exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
    have hqg_meas_mu : AEStronglyMeasurable (qg θ) μ := by
      simpa only [qg, div_eq_mul_inv] using!
        ((hrem.aestronglyMeasurable.const_mul (2 * (s θ)⁻¹)).mul
          (M.sqrtDensity_meas θ₀).inv.aestronglyMeasurable)
    have hqg_meas_P : AEStronglyMeasurable (qg θ) P₀ :=
      hqg_meas_mu.mono_ac (withDensity_absolutelyContinuous _ _)
    have hqg_mem : MemLp (qg θ) 2 P₀ := by
      refine (memLp_two_iff_integrable_sq hqg_meas_P).2 ?_
      change Integrable (fun x => qg θ x ^ 2)
        (μ.withDensity (fun x => ENNReal.ofReal (M.density θ₀ x)))
      rw [integrable_withDensity_iff (M.density_meas θ₀).ennreal_ofReal (by simp)]
      have hmajor : Integrable (fun x => 4 * (s θ)⁻¹ ^ 2 * r θ x ^ 2) μ :=
        hrem.integrable_sq.const_mul (4 * (s θ)⁻¹ ^ 2)
      refine hmajor.mono ((hqg_meas_mu.pow 2).mul
        ((M.density_meas θ₀).ennreal_ofReal.ennreal_toReal).aestronglyMeasurable) ?_
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x), Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg, abs_of_nonneg]
      · have hs0 := M.sqrtDensity_sq θ₀ x
        by_cases hb : M.sqrtDensity θ₀ x = 0
        · have hp0 : M.density θ₀ x = 0 := by simpa [hb] using hs0.symm
          rw [hp0]
          simp only [mul_zero]
          exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
        · dsimp [qg]
          rw [← hs0]
          field_simp [hb]
          ring_nf
          exact le_rfl
      · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
      · exact mul_nonneg (sq_nonneg (qg θ x)) (M.density_nonneg θ₀ x)
    have hq_eq : q θ =ᵐ[P₀] qg θ := by
      filter_upwards [hbase_pos] with x hbpos
      dsimp [q, qg, W, z, r]
      field_simp [hbpos.ne', hs_ne]
    have hq_mem : MemLp (q θ) 2 P₀ := hqg_mem.ae_eq hq_eq.symm
    refine ⟨hq_mem, ?_⟩
    have hq_sq_eq : (fun x => q θ x ^ 2) =ᵐ[P₀] fun x => qg θ x ^ 2 :=
      hq_eq.mono fun _ hx => congrArg (fun y : ℝ => y ^ 2) hx
    rw [integral_congr_ae hq_sq_eq]
    change (∫ x, qg θ x ^ 2 ∂μ.withDensity
      (fun x => ENNReal.ofReal (M.density θ₀ x))) ≤ _
    rw [integral_withDensity_eq_integral_toReal_smul
      (M.density_meas θ₀).ennreal_ofReal (by simp)]
    have hweighted_int : Integrable (fun x =>
        (ENNReal.ofReal (M.density θ₀ x)).toReal * qg θ x ^ 2) μ := by
      simpa [mul_comm] using
        (integrable_withDensity_iff (M.density_meas θ₀).ennreal_ofReal (by simp)).mp
          hqg_mem.integrable_sq
    have hmajor : Integrable (fun x => 4 * (s θ)⁻¹ ^ 2 * r θ x ^ 2) μ :=
      hrem.integrable_sq.const_mul (4 * (s θ)⁻¹ ^ 2)
    calc
      ∫ x, (ENNReal.ofReal (M.density θ₀ x)).toReal • qg θ x ^ 2 ∂μ
          ≤ ∫ x, 4 * (s θ)⁻¹ ^ 2 * r θ x ^ 2 ∂μ := by
            refine integral_mono (by simpa [smul_eq_mul, mul_comm] using hweighted_int)
              hmajor fun x => ?_
            rw [ENNReal.toReal_ofReal (M.density_nonneg θ₀ x)]
            have hs0 := M.sqrtDensity_sq θ₀ x
            by_cases hb : M.sqrtDensity θ₀ x = 0
            · have hp0 : M.density θ₀ x = 0 := by simpa [hb] using hs0.symm
              rw [hp0]
              simp only [zero_smul]
              exact mul_nonneg
                (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg ((s θ)⁻¹)))
                (sq_nonneg (r θ x))
            · dsimp [qg]
              rw [← hs0]
              field_simp [hb]
              ring_nf
              exact le_rfl
      _ = 4 * ((s θ)⁻¹ ^ 2 * ∫ x, r θ x ^ 2 ∂μ) := by
            rw [integral_const_mul]
            ring
  have hq_mem_ev : ∀ᶠ θ in 𝓝[≠] θ₀, MemLp (q θ) 2 P₀ := hq_data.mono fun _ h => h.1
  have hq_sq_zero : Tendsto (fun θ => ∫ x, q θ x ^ 2 ∂P₀)
      (𝓝[≠] θ₀) (𝓝 0) := by
    have hupper_zero : Tendsto
        (fun θ => 4 * ((s θ)⁻¹ ^ 2 * ∫ x, r θ x ^ 2 ∂μ))
        (𝓝[≠] θ₀) (𝓝 0) := by
      simpa using hres_ratio_zero.const_mul 4
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hupper_zero
      (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) ?_
    filter_upwards [hq_data] with θ hq
    exact hq.2
  have hq_prob : TendstoInMeasure P₀ q (𝓝[≠] θ₀) (fun _ => 0) :=
    tendstoInMeasure_zero_of_integral_sq hq_mem_ev hq_sq_zero
  have hR_nhds : ∀ᶠ w in 𝓝 (0 : ℝ),
      |ForMathlib.logTaylorRemainder w| ≤ 1 := by
    have ht := ForMathlib.logTaylorRemainder_tendsto_zero.eventually
      (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)
    filter_upwards [ht] with w hw
    simpa [Real.dist_eq] using hw
  rw [Metric.eventually_nhds_iff] at hR_nhds
  obtain ⟨δ, hδ, hR_local⟩ := hR_nhds
  let δ' : ℝ := min δ 1
  have hδ' : 0 < δ' := lt_min hδ one_pos
  have hδ'_le : δ' ≤ 1 := min_le_right _ _
  have hbase_zero : P₀ {x | M.sqrtDensity θ₀ x = 0} = 0 := by
    have hbne : ∀ᵐ x ∂P₀, M.sqrtDensity θ₀ x ≠ 0 :=
      hbase_pos.mono fun _ hx => hx.ne'
    have hset := ae_iff.mp hbne
    simpa only [not_ne_iff] using hset
  let u : Θ → 𝓧 → ℝ := fun θ x => (s θ)⁻¹ *
    (M.logDensity θ x - M.logDensity θ₀ x - W θ x)
  have hu_prob : TendstoInMeasure P₀ u (𝓝[≠] θ₀) (fun _ => 0) := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    have hsqrtε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hWbad := (tendstoInMeasure_iff_norm.mp hW_prob) δ' hδ'
    have hVbad := (tendstoInMeasure_iff_norm.mp hV_prob) (Real.sqrt ε) hsqrtε
    have hupper : Tendsto (fun θ =>
        P₀ {x | M.sqrtDensity θ₀ x = 0} +
          P₀ {x | δ' ≤ ‖W θ x - 0‖} +
          P₀ {x | Real.sqrt ε ≤ ‖V θ x - 0‖})
        (𝓝[≠] θ₀) (𝓝 0) := by
      simpa [hbase_zero] using hWbad.add hVbad
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with θ hθ
    have hs_pos : 0 < s θ := by
      have hne : θ ≠ θ₀ := by simpa [Set.mem_compl_iff] using hθ
      simpa [s, norm_pos_iff, sub_ne_zero] using hne
    have hsub : {x | ε ≤ ‖u θ x - 0‖} ⊆
        ({x | M.sqrtDensity θ₀ x = 0} ∪ {x | δ' ≤ ‖W θ x - 0‖}) ∪
          {x | Real.sqrt ε ≤ ‖V θ x - 0‖} := by
      intro x hx
      by_contra hxn
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le, sub_zero] at hxn
      obtain ⟨⟨hb0, hWsmall⟩, hVsmall⟩ := hxn
      have hbpos : 0 < M.sqrtDensity θ₀ x :=
        lt_of_le_of_ne (M.sqrtDensity_nonneg θ₀ x) (Ne.symm hb0)
      have hWabs : |W θ x| < δ' := by simpa [Real.norm_eq_abs] using hWsmall
      have hR : |ForMathlib.logTaylorRemainder (W θ x)| ≤ 1 := by
        apply hR_local
        rw [Real.dist_eq, sub_zero]
        exact hWabs.trans_le (min_le_left _ _)
      have ha : 0 < M.sqrtDensity θ x := by
        apply lt_of_le_of_ne (M.sqrtDensity_nonneg θ x)
        intro ha0
        have hWtwo : W θ x = -2 := by
          dsimp [W]
          rw [← ha0]
          field_simp [hbpos.ne']
          ring
        rw [hWtwo, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hWabs
        linarith
      have hWform : W θ x =
          2 * (M.sqrtDensity θ x / M.sqrtDensity θ₀ x - 1) := by
        dsimp [W]
        field_simp [hbpos.ne']
      have hlogbd := log_sq_ratio_sub_linear_le_sq ha hbpos (hWform ▸ hR)
      simp only [Set.mem_setOf_eq, u, ParametricFamily.logDensity, sub_zero,
        Real.norm_eq_abs] at hx
      rw [← M.sqrtDensity_sq θ x, ← M.sqrtDensity_sq θ₀ x] at hx
      rw [hWform] at hx
      have hmain : ε ≤ (s θ)⁻¹ * (W θ x) ^ 2 := by
        rw [abs_mul, abs_of_pos (inv_pos.mpr hs_pos)] at hx
        calc
          ε ≤ (s θ)⁻¹ * |Real.log (M.sqrtDensity θ x ^ 2) -
              Real.log (M.sqrtDensity θ₀ x ^ 2) -
                2 * (M.sqrtDensity θ x / M.sqrtDensity θ₀ x - 1)| := hx
          _ ≤ (s θ)⁻¹ * (2 * (M.sqrtDensity θ x /
                M.sqrtDensity θ₀ x - 1)) ^ 2 :=
            mul_le_mul_of_nonneg_left hlogbd (inv_nonneg.mpr hs_pos.le)
          _ = (s θ)⁻¹ * (W θ x) ^ 2 := by rw [hWform]
      have hVsq : V θ x ^ 2 = (s θ)⁻¹ * W θ x ^ 2 := by
        dsimp [V]
        rw [mul_pow, inv_pow, Real.sq_sqrt hs_pos.le]
      have hVlt : V θ x ^ 2 < ε := by
        rw [Real.norm_eq_abs] at hVsmall
        have habssq : |V θ x| ^ 2 = V θ x ^ 2 := sq_abs (V θ x)
        have hprod : 0 < (Real.sqrt ε - |V θ x|) *
            (Real.sqrt ε + |V θ x|) :=
          mul_pos (sub_pos.mpr hVsmall)
            (add_pos_of_pos_of_nonneg hsqrtε (abs_nonneg _))
        nlinarith [Real.sq_sqrt hε.le, habssq, hprod]
      rw [← hVsq] at hmain
      exact (not_le_of_gt hVlt) hmain
    calc
      P₀ {x | ε ≤ ‖u θ x - 0‖}
          ≤ P₀ (({x | M.sqrtDensity θ₀ x = 0} ∪ {x | δ' ≤ ‖W θ x - 0‖}) ∪
              {x | Real.sqrt ε ≤ ‖V θ x - 0‖}) := measure_mono hsub
      _ ≤ P₀ ({x | M.sqrtDensity θ₀ x = 0} ∪ {x | δ' ≤ ‖W θ x - 0‖}) +
              P₀ {x | Real.sqrt ε ≤ ‖V θ x - 0‖} := measure_union_le _ _
      _ ≤ P₀ {x | M.sqrtDensity θ₀ x = 0} + P₀ {x | δ' ≤ ‖W θ x - 0‖} +
              P₀ {x | Real.sqrt ε ≤ ‖V θ x - 0‖} := by
                gcongr
                exact measure_union_le _ _
  have hsum := hu_prob.add_zero hq_prob
  unfold DifferentiableInProbabilityAt
  refine hsum.congr_left fun θ => ?_
  filter_upwards [hbase_pos] with x hbpos
  dsimp [u, q, s, W, z]
  rw [real_inner_comm (ℓ x) (θ - θ₀)]
  ring

end AsymptoticStatistics
