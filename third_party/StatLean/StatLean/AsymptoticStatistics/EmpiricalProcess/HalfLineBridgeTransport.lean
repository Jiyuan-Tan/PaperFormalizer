module
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
public import StatLean.AsymptoticStatistics.EmpiricalProcess.GoodnessOfFit
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.TightCoordinateUniqueness

@[expose] public section

/-!
# Probability-integral transport of half-line Brownian bridges

The distribution-free part of van der Vaart Corollary 19.21 (book
pp.277–278).  For a continuous CDF, the probability integral transform sends
the observation law to Lebesgue probability on `[0,1]`; a continuous linear
pullback sends the uniform half-line bridge to the `P`-bridge.  Tight
coordinate-law uniqueness then identifies the full path-space measures before
KS/CvM pushforwards are compared.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

/-- Lebesgue probability measure on the closed unit interval, regarded as a
measure on `ℝ`.

Edge behavior: using `Icc 0 1` rather than Mathlib's finite-set
`ProbabilityTheory.uniformOn`; the endpoints have Lebesgue mass zero, so the
equivalent `Ioo 0 1` restriction gives the same law. -/
noncomputable def uniform01 : Measure ℝ := by
  exact volume.restrict (Set.Icc 0 1)

/-- The Lebesgue restriction `uniform01` has total mass one. -/
noncomputable instance instIsProbabilityMeasureUniform01 :
    IsProbabilityMeasure uniform01 := by
  refine ⟨?_⟩
  simp [uniform01, Real.volume_Icc]

/-- Probability integral transform for a continuous CDF.  Flat intervals are
allowed: continuity, not strict monotonicity, is the book hypothesis. -/
theorem probabilityIntegralTransform
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hF : Continuous (cdf P)) :
    P.map (cdf P) = uniform01 := by
  have hlevel : ∀ {u : ℝ}, 0 < u → u < 1 →
      P ((cdf P) ⁻¹' Set.Iic u) = ENNReal.ofReal u := by
    intro u hu0 hu1
    let A : Set ℝ := (cdf P) ⁻¹' Set.Iic u
    have hbelow : ∃ a, cdf P a ≤ u := by
      obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot P).eventually
        (Iio_mem_nhds hu0)).exists
      exact ⟨a, ha.le⟩
    have habove : ∃ b, u ≤ cdf P b := by
      obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop P).eventually
        (Ioi_mem_nhds hu1)).exists
      exact ⟨b, hb.le⟩
    obtain ⟨x, hx⟩ := mem_range_of_exists_le_of_exists_ge hF hbelow habove
    have hxA : x ∈ A := by simp [A, hx]
    have hAbdd : BddAbove A := by
      obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop P).eventually
        (Ioi_mem_nhds hu1)).exists
      refine ⟨b, fun t ht ↦ ?_⟩
      change cdf P t ≤ u at ht
      by_contra htb
      have hmono := monotone_cdf P (le_of_not_ge htb)
      exact (not_lt_of_ge ht) (hb.trans_le hmono)
    have hAclosed : IsClosed A := isClosed_Iic.preimage hF
    have hsupA : sSup A ∈ A := hAclosed.csSup_mem ⟨x, hxA⟩ hAbdd
    have hFu : cdf P (sSup A) = u := by
      apply le_antisymm hsupA
      rw [← hx]
      exact monotone_cdf P (le_csSup hAbdd hxA)
    have hAeq : A = Set.Iic (sSup A) := by
      ext t
      constructor
      · exact fun ht ↦ le_csSup hAbdd ht
      · intro ht
        exact (monotone_cdf P ht).trans_eq hFu
    calc
      P ((cdf P) ⁻¹' Set.Iic u) = P (Set.Iic (sSup A)) := by rw [← hAeq]
      _ = ENNReal.ofReal (cdf P (sSup A)) := (ofReal_cdf P _).symm
      _ = ENNReal.ofReal u := by rw [hFu]
  letI : IsProbabilityMeasure (P.map (cdf P)) :=
    Measure.isProbabilityMeasure_map hF.measurable.aemeasurable
  apply Measure.ext_of_Iic
  intro u
  rw [Measure.map_apply hF.measurable measurableSet_Iic, uniform01,
    Measure.restrict_apply measurableSet_Iic]
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · have hpre : (cdf P) ⁻¹' Set.Iic u = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false]
      constructor
      · exact not_le_of_gt (hu.trans_le (cdf_nonneg P x))
      · exact False.elim
    have hset : Set.Iic u ∩ Set.Icc 0 1 = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc,
        Set.mem_empty_iff_false]
      constructor
      · rintro ⟨hxu, hx0, -⟩
        linarith
      · exact False.elim
    rw [hpre, hset]
    simp
  · have hzero : P ((cdf P) ⁻¹' Set.Iic 0) = 0 := by
      apply le_antisymm _ (zero_le)
      refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
      let q : ℝ := min ((ε : ℝ) / 2) (1 / 2)
      have hε' : 0 < (ε : ℝ) := by exact_mod_cast hε
      have hq0 : 0 < q := lt_min (div_pos hε' (by norm_num)) (by norm_num)
      have hq1 : q < 1 := (min_le_right _ _).trans_lt (by norm_num)
      calc
        P ((cdf P) ⁻¹' Set.Iic 0) ≤
            P ((cdf P) ⁻¹' Set.Iic (q : ℝ)) := measure_mono (by
              intro x hx
              change cdf P x ≤ q
              exact hx.trans hq0.le)
        _ = ENNReal.ofReal q := hlevel hq0 hq1
        _ ≤ (ε : ℝ≥0∞) := ENNReal.ofReal_le_coe.mpr
          ((min_le_left _ _).trans (half_le_self hε'.le))
        _ = 0 + ε := by simp
    have hset : Set.Iic 0 ∩ Set.Icc (0 : ℝ) 1 = {0} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hx0, h0x, -⟩
        exact le_antisymm hx0 h0x
      · rintro rfl
        norm_num
    rw [hzero, hset]
    simp
  · by_cases hu1 : u < 1
    · have hset : Set.Iic u ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 u := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨hxu, h0x, -⟩
          exact ⟨h0x, hxu⟩
        · rintro ⟨h0x, hxu⟩
          exact ⟨hxu, h0x, hxu.trans hu1.le⟩
      rw [hlevel hu hu1, hset, Real.volume_Icc, sub_zero]
    · have hu1' : 1 ≤ u := le_of_not_gt hu1
      have hpre : (cdf P) ⁻¹' Set.Iic u = Set.univ := by
        ext x
        simp [(cdf_le_one P x).trans hu1']
      have hset : Set.Iic u ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 1 := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · exact fun h ↦ h.2
        · rintro h
          exact ⟨h.2.trans hu1', h⟩
      rw [hpre, hset]
      simp [Real.volume_Icc]

private theorem cdf_uniform01_of_mem {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    cdf uniform01 u = u := by
  rw [cdf_eq_real, measureReal_def, uniform01,
    Measure.restrict_apply measurableSet_Iic]
  have hset : Set.Iic u ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 u := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · exact fun h ↦ ⟨h.2.1, h.1⟩
    · exact fun h ↦ ⟨h.2, h.1, h.2.trans hu1⟩
  rw [hset, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hu0]

private theorem distL2_halfLine_cdf (P : Measure ℝ) [IsProbabilityMeasure P]
    (s t : ℝ) :
    distL2 uniform01 (halfLineIndicator (cdf P s)) (halfLineIndicator (cdf P t)) =
      distL2 P (halfLineIndicator s) (halfLineIndicator t) := by
  have hsub : ∀ {a b : ℝ}, a ≤ b →
      halfLineIndicator a - halfLineIndicator b =
        (Set.Ioc a b).indicator (fun _ ↦ (-1 : ℝ)) := by
    intro a b hab
    funext x
    by_cases hxa : x ≤ a
    · have hxb : x ≤ b := hxa.trans hab
      simp [halfLineIndicator, hxa, hxb]
    · by_cases hxb : x ≤ b
      · simp [halfLineIndicator, hxa, hxb, not_le.mp hxa]
      · simp [halfLineIndicator, hxa, hxb, not_le.mp hxa]
  have hle : ∀ {s t : ℝ}, s ≤ t →
      distL2 uniform01 (halfLineIndicator (cdf P s)) (halfLineIndicator (cdf P t)) =
        distL2 P (halfLineIndicator s) (halfLineIndicator t) := by
    intro s t hst
    have hFst : cdf P s ≤ cdf P t := monotone_cdf P hst
    unfold distL2
    rw [hsub hFst, hsub hst, eLpNorm_indicator_const measurableSet_Ioc (by norm_num)
      (by norm_num), eLpNorm_indicator_const measurableSet_Ioc (by norm_num) (by norm_num)]
    congr 2
    rw [uniform01, Measure.restrict_apply measurableSet_Ioc]
    have hset : Set.Ioc (cdf P s) (cdf P t) ∩ Set.Icc (0 : ℝ) 1 =
        Set.Ioc (cdf P s) (cdf P t) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc]
      constructor
      · exact fun h ↦ h.1
      · intro h
        exact ⟨h, (cdf_nonneg P s).trans_lt h.1 |>.le,
          h.2.trans (cdf_le_one P t)⟩
    have hPIoc : P (Set.Ioc s t) = ENNReal.ofReal (cdf P t - cdf P s) := by
      calc
        P (Set.Ioc s t) = (cdf P).measure (Set.Ioc s t) := by rw [measure_cdf P]
        _ = ENNReal.ofReal (cdf P t - cdf P s) :=
          StieltjesFunction.measure_Ioc (cdf P) s t
    rw [hset, Real.volume_Ioc, hPIoc]
  rcases le_total s t with hst | hts
  · exact hle hst
  · rw [distL2_comm (halfLineIndicator (cdf P s)),
      distL2_comm (halfLineIndicator s)]
    exact hle hts

private theorem distL2_halfLine_sq (P : Measure ℝ) [IsProbabilityMeasure P]
    (s t : ℝ) :
    (distL2 P (halfLineIndicator s) (halfLineIndicator t)) ^ 2 =
      |cdf P s - cdf P t| := by
  have hsub : ∀ {a b : ℝ}, a ≤ b →
      halfLineIndicator a - halfLineIndicator b =
        (Set.Ioc a b).indicator (fun _ ↦ (-1 : ℝ)) := by
    intro a b hab
    funext x
    by_cases hxa : x ≤ a
    · have hxb : x ≤ b := hxa.trans hab
      simp [halfLineIndicator, hxa, hxb]
    · by_cases hxb : x ≤ b
      · simp [halfLineIndicator, hxa, hxb, not_le.mp hxa]
      · simp [halfLineIndicator, hxa, hxb, not_le.mp hxa]
  have hle : ∀ {s t : ℝ}, s ≤ t →
      (distL2 P (halfLineIndicator s) (halfLineIndicator t)) ^ 2 =
        |cdf P s - cdf P t| := by
    intro s t hst
    have hFst : cdf P s ≤ cdf P t := monotone_cdf P hst
    have hPIoc : P (Set.Ioc s t) = ENNReal.ofReal (cdf P t - cdf P s) := by
      calc
        P (Set.Ioc s t) = (cdf P).measure (Set.Ioc s t) := by rw [measure_cdf P]
        _ = ENNReal.ofReal (cdf P t - cdf P s) :=
          StieltjesFunction.measure_Ioc (cdf P) s t
    unfold distL2
    rw [hsub hst, eLpNorm_indicator_const measurableSet_Ioc (by norm_num)
      (by norm_num), hPIoc]
    have hx : 0 ≤ cdf P t - cdf P s := sub_nonneg.mpr hFst
    rw [show ‖(-1 : ℝ)‖ₑ = 1 by simp, one_mul, ← ENNReal.toReal_rpow]
    norm_num [ENNReal.toReal_ofReal hx, abs_of_nonpos (sub_nonpos.mpr hFst),
      Real.sq_sqrt hx]
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hx]
  rcases le_total s t with hst | hts
  · exact hle hst
  · rw [distL2_comm (halfLineIndicator s), abs_sub_comm]
    exact hle hts

private theorem cdf_uniform01_eq (t : ℝ) :
    cdf uniform01 t = max 0 (min t 1) := by
  by_cases ht0 : t < 0
  · have hmono := monotone_cdf uniform01 (le_of_lt ht0)
    rw [cdf_uniform01_of_mem le_rfl zero_le_one] at hmono
    have ht : cdf uniform01 t = 0 :=
      le_antisymm hmono (cdf_nonneg uniform01 t)
    rw [ht]
    simp [ht0.le]
  · have h0t : 0 ≤ t := le_of_not_gt ht0
    by_cases ht1 : t ≤ 1
    · rw [cdf_uniform01_of_mem h0t ht1]
      simp [h0t, ht1]
    · have h1t : 1 ≤ t := (lt_of_not_ge ht1).le
      have hmono := monotone_cdf uniform01 h1t
      rw [cdf_uniform01_of_mem zero_le_one le_rfl] at hmono
      have ht : cdf uniform01 t = 1 :=
        le_antisymm (cdf_le_one uniform01 t) hmono
      rw [ht]
      simp [h1t]

private theorem continuous_cdf_uniform01 : Continuous (cdf uniform01) := by
  rw [show cdf uniform01 = fun t : ℝ ↦ max 0 (min t 1) by
    funext t
    exact cdf_uniform01_eq t]
  fun_prop

private theorem continuous_halfLine_eval_of_uniform_uc
    (z : LinfF halfLineIndicatorClass)
    (hz : ∀ ε > 0, ∃ δ > 0, ∀ f g : ↑halfLineIndicatorClass,
      distL2 uniform01 f g < δ → |z f - z g| < ε) :
    Continuous (fun t : ℝ ↦ z (halfLineIndex t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hzδ⟩ := hz ε hε
  obtain ⟨η, hη, hcdf⟩ := (Metric.continuousAt_iff.mp
    continuous_cdf_uniform01.continuousAt) (δ ^ 2) (sq_pos_of_pos hδ)
  refine ⟨η, hη, fun s hst ↦ ?_⟩
  have hsquares :
      (distL2 uniform01 (halfLineIndicator s) (halfLineIndicator t)) ^ 2 <
        δ ^ 2 := by
    rw [distL2_halfLine_sq]
    simpa only [Real.dist_eq] using hcdf hst
  have hdist : distL2 uniform01 (halfLineIndicator s)
      (halfLineIndicator t) < δ :=
    (sq_lt_sq₀ ENNReal.toReal_nonneg hδ.le).mp hsquares
  simpa only [Real.dist_eq] using hzδ (halfLineIndex s) (halfLineIndex t) hdist

/-- Continuous linear pullback of a uniform half-line path along `t ↦ F(t)`.

Edge behavior: flat CDF intervals merely repeat a coordinate.  The map is a
contraction in uniform norm; it asserts no inverse or strict monotonicity. -/
noncomputable def cdfPullbackCLM (P : Measure ℝ) :
    LinfF halfLineIndicatorClass →L[ℝ] LinfF halfLineIndicatorClass := by
  letI : Nonempty ↑halfLineIndicatorClass := ⟨halfLineIndex 0⟩
  let L : LinfF halfLineIndicatorClass →ₗ[ℝ]
      LinfF halfLineIndicatorClass :=
    { toFun := fun z ↦
        ⟨fun i ↦ z (halfLineIndex (cdf P (halfLineIndexEquiv.symm i))),
          memℓp_infty ⟨‖z‖, by
            rintro _ ⟨i, rfl⟩
            exact lp.norm_apply_le_norm ENNReal.top_ne_zero z
              (halfLineIndex (cdf P (halfLineIndexEquiv.symm i)))⟩⟩
      map_add' := by intros; ext; rfl
      map_smul' := by intros; ext; rfl }
  exact L.mkContinuous 1 fun z ↦ by
    rw [one_mul, lp.norm_eq_ciSup]
    exact ciSup_le fun i ↦ lp.norm_apply_le_norm ENNReal.top_ne_zero z
      (halfLineIndex (cdf P (halfLineIndexEquiv.symm i)))

/-- Coordinate formula for the CDF pullback. -/
theorem cdfPullbackCLM_apply (P : Measure ℝ)
    (z : LinfF halfLineIndicatorClass) (t : ℝ) :
    cdfPullbackCLM P z (halfLineIndex t) =
      z (halfLineIndex (cdf P t)) := by
  rw [cdfPullbackCLM]
  change z (halfLineIndex (cdf P (halfLineIndexEquiv.symm (halfLineIndex t)))) = _
  have hindex : halfLineIndexEquiv t = halfLineIndex t := rfl
  rw [← hindex, halfLineIndexEquiv.symm_apply_apply]

private theorem ksFunctional_cdfPullback_eq_of_uniform_uc
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hF : Continuous (cdf P))
    (z : LinfF halfLineIndicatorClass)
    (hz : ∀ ε > 0, ∃ δ > 0, ∀ f g : ↑halfLineIndicatorClass,
      distL2 uniform01 f g < δ → |z f - z g| < ε) :
    ksFunctional (cdfPullbackCLM P z) = ksFunctional z := by
  have hzcont := continuous_halfLine_eval_of_uniform_uc z hz
  have hopen : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      |z (halfLineIndex u)| ≤ ‖cdfPullbackCLM P z‖ := by
    intro u hu
    have hbelow : ∃ a, cdf P a ≤ u := by
      obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot P).eventually
        (Iio_mem_nhds hu.1)).exists
      exact ⟨a, ha.le⟩
    have habove : ∃ b, u ≤ cdf P b := by
      obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop P).eventually
        (Ioi_mem_nhds hu.2)).exists
      exact ⟨b, hb.le⟩
    obtain ⟨t, ht⟩ := mem_range_of_exists_le_of_exists_ge hF hbelow habove
    rw [← ht, ← cdfPullbackCLM_apply]
    simpa only [Real.norm_eq_abs] using
      lp.norm_apply_le_norm ENNReal.top_ne_zero (cdfPullbackCLM P z)
        (halfLineIndex t)
  have hclosed : IsClosed {u : ℝ | |z (halfLineIndex u)| ≤
      ‖cdfPullbackCLM P z‖} := by
    exact isClosed_Iic.preimage hzcont.abs
  have hunit : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |z (halfLineIndex u)| ≤ ‖cdfPullbackCLM P z‖ := by
    intro u hu
    have hcl : u ∈ closure (Set.Ioo (0 : ℝ) 1) := by
      rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
      exact hu
    exact (closure_minimal (fun v hv ↦ hopen v hv) hclosed) hcl
  have hreduce : ∀ t : ℝ,
      z (halfLineIndex t) = z (halfLineIndex (cdf uniform01 t)) := by
    intro t
    have hFu0 : 0 ≤ cdf uniform01 t := cdf_nonneg uniform01 t
    have hFu1 : cdf uniform01 t ≤ 1 := cdf_le_one uniform01 t
    have hsq := distL2_halfLine_sq uniform01 t (cdf uniform01 t)
    rw [cdf_uniform01_of_mem hFu0 hFu1, sub_self, abs_zero] at hsq
    have hdist : distL2 uniform01 (halfLineIndicator t)
        (halfLineIndicator (cdf uniform01 t)) = 0 := by
      have hd0 : 0 ≤ distL2 uniform01 (halfLineIndicator t)
          (halfLineIndicator (cdf uniform01 t)) := ENNReal.toReal_nonneg
      nlinarith
    by_contra hne
    have habs : 0 < |z (halfLineIndex t) -
        z (halfLineIndex (cdf uniform01 t))| := abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨δ, hδ, hzδ⟩ := hz _ habs
    have hlt := hzδ (halfLineIndex t) (halfLineIndex (cdf uniform01 t)) (by
      change distL2 uniform01 (halfLineIndicator t)
        (halfLineIndicator (cdf uniform01 t)) < δ
      rw [hdist]
      exact hδ)
    exact (lt_irrefl _ hlt)
  letI : Nonempty ↑halfLineIndicatorClass := ⟨halfLineIndex 0⟩
  unfold ksFunctional
  apply le_antisymm
  · rw [lp.norm_eq_ciSup]
    apply ciSup_le
    intro i
    let t := halfLineIndexEquiv.symm i
    have hi : halfLineIndex t = i := halfLineIndexEquiv.apply_symm_apply i
    rw [← hi, cdfPullbackCLM_apply]
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero z
      (halfLineIndex (cdf P t))
  · rw [lp.norm_eq_ciSup]
    apply ciSup_le
    intro i
    let t := halfLineIndexEquiv.symm i
    have hi : halfLineIndex t = i := halfLineIndexEquiv.apply_symm_apply i
    rw [← hi, Real.norm_eq_abs, hreduce t]
    exact hunit _ ⟨cdf_nonneg uniform01 t, cdf_le_one uniform01 t⟩

private theorem cvmFunctional_cdfPullback_eq_of_uniform_uc
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hF : Continuous (cdf P))
    (z : LinfF halfLineIndicatorClass)
    (hz : ∀ ε > 0, ∃ δ > 0, ∀ f g : ↑halfLineIndicatorClass,
      distL2 uniform01 f g < δ → |z f - z g| < ε) :
    cvmFunctional P (cdfPullbackCLM P z) = cvmFunctional uniform01 z := by
  let g : ℝ → ℝ≥0∞ := fun u ↦ ENNReal.ofReal ((z (halfLineIndex u)) ^ 2)
  have hg : Measurable g := by
    exact ENNReal.measurable_ofReal.comp
      ((continuous_halfLine_eval_of_uniform_uc z hz).pow 2).measurable
  unfold cvmFunctional
  congr 1
  simp_rw [cdfPullbackCLM_apply]
  change outerExpectation P (g ∘ cdf P) = outerExpectation uniform01 g
  rw [outerExpectation_eq_lintegral (hg.comp hF.measurable),
    outerExpectation_eq_lintegral hg]
  change (∫⁻ t, g (cdf P t) ∂P) = ∫⁻ t, g t ∂uniform01
  rw [← lintegral_map hg hF.measurable, probabilityIntegralTransform P hF]

/-- Continuous coordinate evaluation on the half-line bridge carrier. -/
private noncomputable def halfLineEvalCLM
    (i : ↑halfLineIndicatorClass) :
    LinfF halfLineIndicatorClass →L[ℝ] ℝ := by
  let L : LinfF halfLineIndicatorClass →ₗ[ℝ] ℝ :=
    { toFun := fun z ↦ z i
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact L.mkContinuous 1 fun z ↦ by
    simpa only [one_mul, Real.norm_eq_abs] using!
      lp.norm_apply_le_norm ENNReal.top_ne_zero z i

/-- A continuous-CDF probability-integral pullback transports a uniform
half-line Brownian bridge to a `P`-Brownian bridge.  All bridge fields
(probability, covariance, Gaussian finite-dimensional laws, tightness, and
uniformly-continuous paths) are transported explicitly. -/
theorem isPBrownianBridge_map_cdfPullback
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hF : Continuous (cdf P))
    {νU : Measure (LinfF halfLineIndicatorClass)}
      (hνU : IsPBrownianBridge halfLineIndicatorClass uniform01 νU) :
    IsPBrownianBridge halfLineIndicatorClass P
      (νU.map (cdfPullbackCLM P)) := by
  have _hPIT := probabilityIntegralTransform P hF
  let T := cdfPullbackCLM P
  letI : IsProbabilityMeasure νU := hνU.isProbabilityMeasure
  refine
    { isProbabilityMeasure :=
        Measure.isProbabilityMeasure_map T.continuous.aemeasurable
      cov := ?_
      mean := ?_
      isGaussian_fdd := ?_
      tight := by
        simpa only [Set.image_singleton] using hνU.tight.map T.continuous
      ucPaths := ?_ }
  · rintro ⟨_, ⟨s, rfl⟩⟩ ⟨_, ⟨t, rfl⟩⟩
    have hcont : Continuous (fun z : LinfF halfLineIndicatorClass ↦
        z (halfLineIndex s) * z (halfLineIndex t)) :=
      (continuous_halfLine_evaluation s).mul (continuous_halfLine_evaluation t)
    calc
      ∫ z, z (halfLineIndex s) * z (halfLineIndex t) ∂(νU.map T) =
          ∫ z, T z (halfLineIndex s) * T z (halfLineIndex t) ∂νU := by
        rw [integral_map T.continuous.aemeasurable hcont.aestronglyMeasurable]
      _ = ∫ z, z (halfLineIndex (cdf P s)) *
          z (halfLineIndex (cdf P t)) ∂νU := by
        simp_rw [T, cdfPullbackCLM_apply]
      _ = cdf uniform01 (min (cdf P s) (cdf P t)) -
          cdf uniform01 (cdf P s) * cdf uniform01 (cdf P t) :=
        halfLine_bridge_covariance uniform01 hνU _ _
      _ = cdf P (min s t) - cdf P s * cdf P t := by
        rw [cdf_uniform01_of_mem (le_min (cdf_nonneg P s) (cdf_nonneg P t))
            ((min_le_left _ _).trans (cdf_le_one P s)),
          cdf_uniform01_of_mem (cdf_nonneg P s) (cdf_le_one P s),
          cdf_uniform01_of_mem (cdf_nonneg P t) (cdf_le_one P t),
          (monotone_cdf P).map_min]
      _ = (∫ x, halfLineIndicator s x * halfLineIndicator t x ∂P) -
          (∫ x, halfLineIndicator s x ∂P) *
            ∫ x, halfLineIndicator t x ∂P := by
        rw [integral_halfLineIndicator_mul, integral_halfLineIndicator,
          integral_halfLineIndicator]
  · rintro ⟨_, ⟨s, rfl⟩⟩
    calc
      ∫ z, z (halfLineIndex s) ∂(νU.map T) =
          ∫ z, T z (halfLineIndex s) ∂νU := by
        rw [integral_map T.continuous.aemeasurable
          (continuous_halfLine_evaluation s).aestronglyMeasurable]
      _ = ∫ z, z (halfLineIndex (cdf P s)) ∂νU := by
        simp_rw [T, cdfPullbackCLM_apply]
      _ = 0 := hνU.mean (halfLineIndex (cdf P s))
  · intro m φ
    let ψ : Fin m → ↑halfLineIndicatorClass := fun k ↦
      halfLineIndex (cdf P (halfLineIndexEquiv.symm (φ k)))
    refine ⟨?_⟩
    have hgauss := (hνU.isGaussian_fdd m ψ).isGaussian_map
    rw [Measure.map_map (measurable_pi_iff.mpr fun k ↦
      (continuous_linfF_eval (φ k)).measurable)
      T.continuous.measurable]
    convert! hgauss using 1
  · apply (ae_map_iff T.continuous.aemeasurable
      (pBridge_ucPaths_measurableSet (F := halfLineIndicatorClass) (P := P))).2
    filter_upwards [hνU.ucPaths] with z hz
    intro ε hε
    obtain ⟨δ, hδ, hzδ⟩ := hz ε hε
    refine ⟨δ, hδ, ?_⟩
    intro f g hfg
    let s := halfLineIndexEquiv.symm f
    let t := halfLineIndexEquiv.symm g
    have hf : halfLineIndex s = f := by
      have h := halfLineIndexEquiv.apply_symm_apply f
      exact h
    have hg : halfLineIndex t = g := by
      have h := halfLineIndexEquiv.apply_symm_apply g
      exact h
    have hfg' : distL2 P (halfLineIndicator s) (halfLineIndicator t) < δ := by
      change distL2 P (↑(halfLineIndex s)) (↑(halfLineIndex t)) < δ
      rw [hf, hg]
      exact hfg
    rw [← hf, ← hg]
    change |cdfPullbackCLM P z (halfLineIndex s) -
      cdfPullbackCLM P z (halfLineIndex t)| < ε
    rw [cdfPullbackCLM_apply, cdfPullbackCLM_apply]
    apply hzδ (halfLineIndex (cdf P s)) (halfLineIndex (cdf P t))
    change distL2 uniform01 (halfLineIndicator (cdf P s))
      (halfLineIndicator (cdf P t)) < δ
    rw [distL2_halfLine_cdf P s t]
    exact hfg'

/-- Tight half-line Brownian-bridge laws with the same population law are
equal.  The proof passes through finite evaluation vectors and
`tightMeasure_eq_of_finiteCoordinate_laws`; covariance/FDD declarations alone
are not treated as path-space equality. -/
theorem halfLine_brownianBridge_measure_unique
    (P : Measure ℝ)
    {ν κ : Measure (LinfF halfLineIndicatorClass)}
    (hν : IsPBrownianBridge halfLineIndicatorClass P ν)
    (hκ : IsPBrownianBridge halfLineIndicatorClass P κ) :
    ν = κ := by
  classical
  letI : IsProbabilityMeasure ν := hν.isProbabilityMeasure
  letI : IsProbabilityMeasure κ := hκ.isProbabilityMeasure
  apply tightMeasure_eq_of_finiteCoordinate_laws (halfLineEvalCLM)
  · intro x y hxy
    ext i
    exact hxy i
  · exact hν.isProbabilityMeasure
  · exact hκ.isProbabilityMeasure
  · exact hν.tight
  · exact hκ.tight
  · intro m a
    let R := finiteCoordinateCLM halfLineEvalCLM a
    have hR_apply : ∀ z : LinfF halfLineIndicatorClass,
        R z = (WithLp.toLp 2 (fun i ↦ z (a i)) : EuclideanSpace ℝ (Fin m)) := by
      intro z
      apply PiLp.ext
      intro i
      rfl
    have hR_meas : Measurable R := R.continuous.measurable
    have hνpi : HasGaussianLaw
        (fun z : LinfF halfLineIndicatorClass ↦ fun i ↦ z (a i)) ν :=
      hν.isGaussian_fdd m a
    have hκpi : HasGaussianLaw
        (fun z : LinfF halfLineIndicatorClass ↦ fun i ↦ z (a i)) κ :=
      hκ.isGaussian_fdd m a
    let L := (EuclideanSpace.equiv (Fin m) ℝ).symm
    have hcomp : (fun z : LinfF halfLineIndicatorClass ↦ R z) =
        L ∘ (fun z : LinfF halfLineIndicatorClass ↦ fun i ↦ z (a i)) := by
      funext z
      rw [hR_apply]
      rfl
    haveI hνpi_gauss : IsGaussian
        (ν.map (fun z : LinfF halfLineIndicatorClass ↦ fun i ↦ z (a i))) :=
      hνpi.isGaussian_map
    haveI hκpi_gauss : IsGaussian
        (κ.map (fun z : LinfF halfLineIndicatorClass ↦ fun i ↦ z (a i))) :=
      hκpi.isGaussian_map
    have hνR_gauss : IsGaussian (ν.map R) := by
      rw [show R = L ∘
          (fun z : LinfF halfLineIndicatorClass ↦ fun i ↦ z (a i)) from hcomp]
      rw [← AEMeasurable.map_map_of_aemeasurable
        L.continuous.measurable.aemeasurable hνpi.aemeasurable]
      exact isGaussian_map_equiv L
    have hκR_gauss : IsGaussian (κ.map R) := by
      rw [show R = L ∘
          (fun z : LinfF halfLineIndicatorClass ↦ fun i ↦ z (a i)) from hcomp]
      rw [← AEMeasurable.map_map_of_aemeasurable
        L.continuous.measurable.aemeasurable hκpi.aemeasurable]
      exact isGaussian_map_equiv L
    letI : IsGaussian (ν.map R) := hνR_gauss
    letI : IsGaussian (κ.map R) := hκR_gauss
    apply IsGaussian.ext
    · have hνint : Integrable R ν :=
        (integrable_map_measure aestronglyMeasurable_id
          hR_meas.aemeasurable).mp IsGaussian.integrable_id
      have hκint : Integrable R κ :=
        (integrable_map_measure aestronglyMeasurable_id
          hR_meas.aemeasurable).mp IsGaussian.integrable_id
      rw [integral_map hR_meas.aemeasurable aestronglyMeasurable_id,
        integral_map hR_meas.aemeasurable aestronglyMeasurable_id]
      simp only [id_eq]
      apply PiLp.ext
      intro i
      have hνproj : (∫ z, R z ∂ν).ofLp i = ∫ z, (R z).ofLp i ∂ν := by
        have h := ContinuousLinearMap.integral_comp_comm
          (EuclideanSpace.proj i) hνint
        simpa only [EuclideanSpace.coe_proj] using h.symm
      have hκproj : (∫ z, R z ∂κ).ofLp i = ∫ z, (R z).ofLp i ∂κ := by
        have h := ContinuousLinearMap.integral_comp_comm
          (EuclideanSpace.proj i) hκint
        simpa only [EuclideanSpace.coe_proj] using h.symm
      rw [hνproj, hκproj]
      simp_rw [hR_apply]
      rw [hν.mean (a i), hκ.mean (a i)]
    · have hmemν : MemLp id 2 (ν.map R) := IsGaussian.memLp_two_id
      have hmemκ : MemLp id 2 (κ.map R) := IsGaussian.memLp_two_id
      have hmemRν : MemLp R 2 ν :=
        (memLp_map_measure_iff aestronglyMeasurable_id
          hR_meas.aemeasurable).mp hmemν
      have hmemRκ : MemLp R 2 κ :=
        (memLp_map_measure_iff aestronglyMeasurable_id
          hR_meas.aemeasurable).mp hmemκ
      have hmemcoordν : ∀ i : Fin m,
          MemLp (fun z : LinfF halfLineIndicatorClass ↦ z (a i)) 2 ν := by
        intro i
        have heq : (fun z : LinfF halfLineIndicatorClass ↦ z (a i)) =
            (EuclideanSpace.proj i) ∘ R := by
          funext z
          rw [EuclideanSpace.coe_proj]
          rfl
        rw [heq]
        exact ((EuclideanSpace.proj i) :
          EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).lipschitz.comp_memLp
            (map_zero _) hmemRν
      have hmemcoordκ : ∀ i : Fin m,
          MemLp (fun z : LinfF halfLineIndicatorClass ↦ z (a i)) 2 κ := by
        intro i
        have heq : (fun z : LinfF halfLineIndicatorClass ↦ z (a i)) =
            (EuclideanSpace.proj i) ∘ R := by
          funext z
          rw [EuclideanSpace.coe_proj]
          rfl
        rw [heq]
        exact ((EuclideanSpace.proj i) :
          EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).lipschitz.comp_memLp
            (map_zero _) hmemRκ
      have hbasis : ∀ i : Fin m,
          (fun u : EuclideanSpace ℝ (Fin m) ↦
            (inner ℝ ((EuclideanSpace.basisFun (Fin m) ℝ).toBasis i) u : ℝ)) =
            fun u ↦ u.ofLp i := by
        intro i
        funext u
        rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
          PiLp.inner_apply]
        simp_rw [show ∀ j : Fin m,
            (inner ℝ ((EuclideanSpace.single i (1 : ℝ)).ofLp j)
              (u.ofLp j) : ℝ) = u.ofLp j * (if j = i then 1 else 0) by
          intro j
          rw [PiLp.single_apply]
          rfl]
        simp [Finset.sum_ite_eq']
      rw [← ContinuousLinearMap.toBilinForm_inj]
      refine LinearMap.BilinForm.ext_basis
        (EuclideanSpace.basisFun (Fin m) ℝ).toBasis fun i j ↦ ?_
      rw [ContinuousLinearMap.toBilinForm_apply,
        ContinuousLinearMap.toBilinForm_apply,
        covarianceBilin_apply_eq_cov hmemν,
        covarianceBilin_apply_eq_cov hmemκ, hbasis i, hbasis j]
      have hcoord_measν : ∀ i : Fin m,
          AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin m) ↦ u.ofLp i)
            (ν.map R) := by
        intro i
        simpa only [EuclideanSpace.coe_proj] using
          (EuclideanSpace.proj i).continuous.measurable.aestronglyMeasurable
      have hcoord_measκ : ∀ i : Fin m,
          AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin m) ↦ u.ofLp i)
            (κ.map R) := by
        intro i
        simpa only [EuclideanSpace.coe_proj] using
          (EuclideanSpace.proj i).continuous.measurable.aestronglyMeasurable
      rw [covariance_map (hcoord_measν i) (hcoord_measν j)
          hR_meas.aemeasurable,
        covariance_map (hcoord_measκ i) (hcoord_measκ j)
          hR_meas.aemeasurable]
      change cov[fun z : LinfF halfLineIndicatorClass ↦ z (a i),
          fun z : LinfF halfLineIndicatorClass ↦ z (a j); ν] =
        cov[fun z : LinfF halfLineIndicatorClass ↦ z (a i),
          fun z : LinfF halfLineIndicatorClass ↦ z (a j); κ]
      rw [covariance_eq_sub (hmemcoordν i) (hmemcoordν j),
        covariance_eq_sub (hmemcoordκ i) (hmemcoordκ j)]
      simp only [Pi.mul_apply]
      rw [hν.mean (a i), hν.mean (a j), hκ.mean (a i), hκ.mean (a j),
        hν.cov (a i) (a j), hκ.cov (a i) (a j)]

/-- Every `P`-half-line bridge law for continuous `F` is the explicit
pushforward of every uniform half-line bridge law. -/
theorem halfLine_bridge_eq_uniform_pushforward
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hF : Continuous (cdf P))
    {νP νU : Measure (LinfF halfLineIndicatorClass)}
    (hνP : IsPBrownianBridge halfLineIndicatorClass P νP)
    (hνU : IsPBrownianBridge halfLineIndicatorClass uniform01 νU) :
    νP = νU.map (cdfPullbackCLM P) := by
  exact halfLine_brownianBridge_measure_unique P hνP
    (isPBrownianBridge_map_cdfPullback P hF hνU)

/-- On uniform-bridge sample paths, CDF pullback preserves the KS functional
and turns the `P`-weighted CvM functional into the uniform CvM functional.
The assertion is almost-everywhere because endpoint and sample-path
regularity come from the bridge law, not from arbitrary `LinfF` paths. -/
theorem gofFunctional_cdfPullback_ae
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hF : Continuous (cdf P))
    {νU : Measure (LinfF halfLineIndicatorClass)}
    (hνU : IsPBrownianBridge halfLineIndicatorClass uniform01 νU) :
    ∀ᵐ z ∂νU,
      gofFunctional P (cdfPullbackCLM P z) = gofFunctional uniform01 z := by
  filter_upwards [hνU.ucPaths] with z hz
  apply Prod.ext
  · exact ksFunctional_cdfPullback_eq_of_uniform_uc P hF z hz
  · exact cvmFunctional_cdfPullback_eq_of_uniform_uc P hF z hz

/-- **Corollary 19.21, distribution-free joint limit law.**
For every continuous distribution function `F`, the joint KS/CvM Brownian-
bridge functional law equals the uniform `[0,1]` bridge functional law.
The equality is obtained by explicit bridge pushforward and tight-measure
uniqueness, not merely by matching covariance or finite-dimensional laws. -/
theorem continuousCDF_gof_limit_law_eq_uniform
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hF : Continuous (cdf P))
    {νP νU : Measure (LinfF halfLineIndicatorClass)}
    (hνP : IsPBrownianBridge halfLineIndicatorClass P νP)
    (hνU : IsPBrownianBridge halfLineIndicatorClass uniform01 νU) :
    νP.map (gofFunctional P) =
      νU.map (gofFunctional uniform01) := by
  rw [halfLine_bridge_eq_uniform_pushforward P hF hνP hνU,
    Measure.map_map (continuous_gofFunctional P).measurable
      (cdfPullbackCLM P).continuous.measurable]
  exact Measure.map_congr (gofFunctional_cdfPullback_ae P hF hνU)

/-- Distribution-free Kolmogorov–Smirnov limit law for continuous CDFs. -/
theorem continuousCDF_ks_limit_law_eq_uniform
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hF : Continuous (cdf P))
    {νP νU : Measure (LinfF halfLineIndicatorClass)}
    (hνP : IsPBrownianBridge halfLineIndicatorClass P νP)
    (hνU : IsPBrownianBridge halfLineIndicatorClass uniform01 νU) :
    νP.map ksFunctional = νU.map ksFunctional := by
  rw [halfLine_bridge_eq_uniform_pushforward P hF hνP hνU,
    Measure.map_map continuous_ksFunctional.measurable
      (cdfPullbackCLM P).continuous.measurable]
  apply Measure.map_congr
  filter_upwards [gofFunctional_cdfPullback_ae P hF hνU] with z hz
  simpa only [gofFunctional] using! congrArg Prod.fst hz

/-- Distribution-free Cramér–von Mises limit law for continuous CDFs. -/
theorem continuousCDF_cvm_limit_law_eq_uniform
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hF : Continuous (cdf P))
    {νP νU : Measure (LinfF halfLineIndicatorClass)}
    (hνP : IsPBrownianBridge halfLineIndicatorClass P νP)
    (hνU : IsPBrownianBridge halfLineIndicatorClass uniform01 νU) :
    νP.map (cvmFunctional P) =
      νU.map (cvmFunctional uniform01) := by
  rw [halfLine_bridge_eq_uniform_pushforward P hF hνP hνU,
    Measure.map_map (continuous_cvmFunctional P).measurable
      (cdfPullbackCLM P).continuous.measurable]
  apply Measure.map_congr
  filter_upwards [gofFunctional_cdfPullback_ae P hF hνU] with z hz
  simpa only [gofFunctional] using! congrArg Prod.snd hz

/-- **Corollary 19.21, distribution-free joint limit.**
For a continuous CDF, bridge laws exist both for `P` and for `uniform01`, and
every such pair gives the same joint KS/CvM pushforward law. -/
theorem continuousCDF_gof_limit_distributionFree
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hF : Continuous (cdf P)) :
    (∃ νP : Measure (LinfF halfLineIndicatorClass),
      IsPBrownianBridge halfLineIndicatorClass P νP) ∧
    (∃ νU : Measure (LinfF halfLineIndicatorClass),
      IsPBrownianBridge halfLineIndicatorClass uniform01 νU) ∧
    ∀ {νP νU : Measure (LinfF halfLineIndicatorClass)},
      IsPBrownianBridge halfLineIndicatorClass P νP →
      IsPBrownianBridge halfLineIndicatorClass uniform01 νU →
      νP.map (gofFunctional P) =
        νU.map (gofFunctional uniform01) := by
  obtain ⟨νP, hνP, -⟩ := halfLine_isPDonskerWithBridge P
  obtain ⟨νU, hνU, -⟩ := halfLine_isPDonskerWithBridge uniform01
  refine ⟨⟨νP, hνP⟩, ⟨νU, hνU⟩, ?_⟩
  intro νP' νU' hνP' hνU'
  exact continuousCDF_gof_limit_law_eq_uniform P hF hνP' hνU'

/-- **Corollary 19.21, distribution-free Kolmogorov–Smirnov limit.** -/
theorem continuousCDF_ks_limit_distributionFree
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hF : Continuous (cdf P)) :
    (∃ νP : Measure (LinfF halfLineIndicatorClass),
      IsPBrownianBridge halfLineIndicatorClass P νP) ∧
    (∃ νU : Measure (LinfF halfLineIndicatorClass),
      IsPBrownianBridge halfLineIndicatorClass uniform01 νU) ∧
    ∀ {νP νU : Measure (LinfF halfLineIndicatorClass)},
      IsPBrownianBridge halfLineIndicatorClass P νP →
      IsPBrownianBridge halfLineIndicatorClass uniform01 νU →
      νP.map ksFunctional = νU.map ksFunctional := by
  obtain ⟨νP, hνP, -⟩ := halfLine_isPDonskerWithBridge P
  obtain ⟨νU, hνU, -⟩ := halfLine_isPDonskerWithBridge uniform01
  refine ⟨⟨νP, hνP⟩, ⟨νU, hνU⟩, ?_⟩
  intro νP' νU' hνP' hνU'
  exact continuousCDF_ks_limit_law_eq_uniform P hF hνP' hνU'

/-- **Corollary 19.21, distribution-free Cramér–von Mises limit.** -/
theorem continuousCDF_cvm_limit_distributionFree
    (P : Measure ℝ) [IsProbabilityMeasure P]
    (hF : Continuous (cdf P)) :
    (∃ νP : Measure (LinfF halfLineIndicatorClass),
      IsPBrownianBridge halfLineIndicatorClass P νP) ∧
    (∃ νU : Measure (LinfF halfLineIndicatorClass),
      IsPBrownianBridge halfLineIndicatorClass uniform01 νU) ∧
    ∀ {νP νU : Measure (LinfF halfLineIndicatorClass)},
      IsPBrownianBridge halfLineIndicatorClass P νP →
      IsPBrownianBridge halfLineIndicatorClass uniform01 νU →
      νP.map (cvmFunctional P) =
        νU.map (cvmFunctional uniform01) := by
  obtain ⟨νP, hνP, -⟩ := halfLine_isPDonskerWithBridge P
  obtain ⟨νU, hνU, -⟩ := halfLine_isPDonskerWithBridge uniform01
  refine ⟨⟨νP, hνP⟩, ⟨νU, hνU⟩, ?_⟩
  intro νP' νU' hνP' hνU'
  exact continuousCDF_cvm_limit_law_eq_uniform P hF hνP' hνU'

end AsymptoticStatistics.EmpiricalProcess
