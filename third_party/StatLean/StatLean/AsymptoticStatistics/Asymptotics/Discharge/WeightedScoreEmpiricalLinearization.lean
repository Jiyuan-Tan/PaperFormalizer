module
public import StatLean.AsymptoticStatistics.Asymptotics.OneStepVec
public import StatLean.AsymptoticStatistics.DQM.MovingDirection
public import StatLean.AsymptoticStatistics.ForMathlib.SplitProductMoments
public import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.LANExpansion

@[expose] public section

/-!
# Weighted-score empirical linearization

The combined cancellation step used in the native vector one-step discharge for
vdV Theorem 25.57.  The statement deliberately keeps the centered empirical
increment and its population Gram drift in one theorem: under DQM and the literal
weighted-score `L²` condition (25.56), these two terms cancel in probability along
every deterministic root-`n` sequence.
-/

open MeasureTheory Filter Topology
open Asymptotics
open scoped ENNReal Matrix.Norms.L2Operator

namespace AsymptoticStatistics.Asymptotics.Discharge.OneStepVec

open AsymptoticStatistics
open AsymptoticStatistics.Asymptotics.OneStepVec

private theorem modelMeasure_isProbabilityMeasure
    {Omega : Type*} [MeasurableSpace Omega] {d : ℕ}
    (M : ParametricFamily Omega (EuclideanSpace ℝ (Fin d)))
    (mu : Measure Omega) (hPDF : IsPDFOf M mu)
    (theta : EuclideanSpace ℝ (Fin d)) :
    IsProbabilityMeasure (modelMeasure M mu theta) := by
  refine ⟨?_⟩
  rw [modelMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hPDF.density_integrable theta)
      (Eventually.of_forall (M.density_nonneg theta)),
    hPDF.density_integral_eq_one theta, ENNReal.ofReal_one]

private theorem rootNBounded_tendsto_parameter
    {d : ℕ} {theta : ℕ → EuclideanSpace ℝ (Fin d)}
    {theta0 : EuclideanSpace ℝ (Fin d)}
    (h : IsRootNBoundedSeq theta theta0) :
    Tendsto theta atTop (nhds theta0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  obtain ⟨C, hC⟩ := h
  have hinv : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ * max C 0) atTop (nhds 0) := by
    have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    simpa only [zero_mul] using! hsqrt.inv_tendsto_atTop.mul_const (max C 0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [hC, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hbound : Real.sqrt n * ‖theta n - theta0‖ ≤ max C 0 :=
    hn.trans (le_max_left _ _)
  calc
    ‖theta n - theta0‖ = (Real.sqrt n)⁻¹ *
        (Real.sqrt n * ‖theta n - theta0‖) := by field_simp
    _ ≤ (Real.sqrt n)⁻¹ * max C 0 :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hsqrt.le)

private theorem rootNBounded_scaled_littleO
    {d : ℕ} {theta : ℕ → EuclideanSpace ℝ (Fin d)}
    {theta0 : EuclideanSpace ℝ (Fin d)} {f : EuclideanSpace ℝ (Fin d) → ℝ}
    (htheta : Tendsto theta atTop (nhds theta0))
    (hroot : IsRootNBoundedSeq theta theta0)
    (hf : f =o[nhds theta0] (fun t => ‖t - theta0‖ ^ 2)) :
    Tendsto (fun n : ℕ => (n : ℝ) * f (theta n)) atTop (nhds 0) := by
  have hsmall : (fun n : ℕ => f (theta n)) =o[atTop]
      (fun n : ℕ => ‖theta n - theta0‖ ^ 2) := hf.comp_tendsto htheta
  have hmul : (fun n : ℕ => (n : ℝ) * f (theta n)) =o[atTop]
      (fun n : ℕ => (n : ℝ) * ‖theta n - theta0‖ ^ 2) :=
    (isBigO_refl (fun n : ℕ => (n : ℝ)) atTop).mul_isLittleO hsmall
  have hscaleO : (fun n : ℕ => (n : ℝ) * ‖theta n - theta0‖ ^ 2) =O[atTop]
      (fun _ : ℕ => (1 : ℝ)) := by
    rw [Asymptotics.isBigO_iff]
    obtain ⟨C, hC⟩ := hroot
    refine ⟨C ^ 2, ?_⟩
    filter_upwards [hC] with n hn
    have ha : 0 ≤ Real.sqrt n * ‖theta n - theta0‖ :=
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hsq : (Real.sqrt n * ‖theta n - theta0‖) ^ 2 ≤ C ^ 2 :=
      pow_le_pow_left₀ ha hn 2
    rw [norm_one, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))]
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)] using hsq
  exact (isLittleO_one_iff ℝ).mp (hmul.trans_isBigO hscaleO)

private theorem dqm_score_memLp_modelMeasure
    {Omega : Type*} [MeasurableSpace Omega] {d : ℕ}
    (M : ParametricFamily Omega (EuclideanSpace ℝ (Fin d)))
    (mu : Measure Omega) (theta0 : EuclideanSpace ℝ (Fin d))
    (ell : Omega → EuclideanSpace ℝ (Fin d))
    (hell : Measurable ell) (hPDF : IsPDFOf M mu)
    (hDQM : DifferentiableQuadraticMean M mu theta0 ell) :
    MemLp ell 2 (modelMeasure M mu theta0) := by
  rw [memLp_two_iff_integrable_sq_norm hell.aestronglyMeasurable, modelMeasure,
    integrable_withDensity_iff (M.density_meas theta0).ennreal_ofReal (by simp)]
  have hi := dqm_norm_sq_score_integrable M mu theta0 ell
    (hPDF.density_integrable theta0) hDQM (fun _ _ => hPDF.density_integrable _)
  convert hi using 1
  funext x
  rw [ENNReal.toReal_ofReal (M.density_nonneg theta0 x)]

private theorem dqm_score_integral_modelMeasure_eq_zero
    {Omega : Type*} [MeasurableSpace Omega] {d : ℕ}
    (M : ParametricFamily Omega (EuclideanSpace ℝ (Fin d)))
    (mu : Measure Omega) (theta0 : EuclideanSpace ℝ (Fin d))
    (ell : Omega → EuclideanSpace ℝ (Fin d))
    (hell : Measurable ell) (hPDF : IsPDFOf M mu)
    (hDQM : DifferentiableQuadraticMean M mu theta0 ell) :
    (∫ x, ell x ∂(modelMeasure M mu theta0)) = 0 := by
  letI := modelMeasure_isProbabilityMeasure M mu hPDF theta0
  have hmem := dqm_score_memLp_modelMeasure M mu theta0 ell hell hPDF hDQM
  apply PiLp.ext
  intro j
  change (∫ x, ell x ∂(modelMeasure M mu theta0)) j = 0
  rw [MeasureTheory.eval_integral_piLp
    (fun k => (hmem.eval_piLp k).integrable one_le_two) j]
  rw [modelMeasure, integral_withDensity_eq_integral_toReal_smul
    (M.density_meas theta0).ennreal_ofReal (by simp)]
  have hz := LANExpansion.score_mean_zero M mu theta0 ell hell
    (hPDF.density_integral_eq_one theta0) (hPDF.density_integrable theta0)
    (fun _ _ => hPDF.density_integral_eq_one _)
    (fun _ _ => hPDF.density_integrable _) hDQM
    (EuclideanSpace.single j (1 : ℝ))
  have hinner (x : Omega) :
      inner ℝ (EuclideanSpace.single j (1 : ℝ)) (ell x) = ell x j := by
    simpa using EuclideanSpace.inner_single_left (𝕜 := ℝ) j (1 : ℝ) (ell x)
  simp_rw [hinner] at hz
  simpa only [ENNReal.toReal_ofReal, M.density_nonneg, smul_eq_mul,
    PiLp.zero_apply, mul_comm] using hz

private theorem dqm_sqrtDensityRatio_scaled_l2_of_rootNBounded
    {Omega : Type*} [MeasurableSpace Omega] {d : ℕ}
    (M : ParametricFamily Omega (EuclideanSpace ℝ (Fin d)))
    (mu : Measure Omega) (theta0 : EuclideanSpace ℝ (Fin d))
    (ell : Omega → EuclideanSpace ℝ (Fin d))
    (hPDF : IsPDFOf M mu)
    (hDQM : DifferentiableQuadraticMean M mu theta0 ell)
    (theta : ℕ → EuclideanSpace ℝ (Fin d))
    (hroot : IsRootNBoundedSeq theta theta0) :
    Tendsto (fun n : ℕ => ∫ x,
      (Real.sqrt n * M.sqrtDensityRatio theta0 (theta n) x -
        inner ℝ (Real.sqrt n • (theta n - theta0)) (ell x)) ^ 2
        ∂(modelMeasure M mu theta0)) atTop (nhds 0) := by
  have htheta := rootNBounded_tendsto_parameter hroot
  have hlinear := dqm_sqrtDensityRatio_l2_linearization M mu theta0 ell hPDF hDQM
  have hraw := rootNBounded_scaled_littleO htheta hroot hlinear.2
  refine hraw.congr' ?_
  filter_upwards [htheta.eventually hlinear.1] with n hn
  calc
    (n : ℝ) * ∫ x,
        (M.sqrtDensityRatio theta0 (theta n) x -
          inner ℝ (theta n - theta0) (ell x)) ^ 2
          ∂(modelMeasure M mu theta0) =
        ∫ x, (n : ℝ) *
          (M.sqrtDensityRatio theta0 (theta n) x -
            inner ℝ (theta n - theta0) (ell x)) ^ 2
          ∂(modelMeasure M mu theta0) := by
            rw [integral_const_mul]
    _ = ∫ x,
        (Real.sqrt n * M.sqrtDensityRatio theta0 (theta n) x -
          inner ℝ (Real.sqrt n • (theta n - theta0)) (ell x)) ^ 2
          ∂(modelMeasure M mu theta0) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change (n : ℝ) *
            (M.sqrtDensityRatio theta0 (theta n) x -
              inner ℝ (theta n - theta0) (ell x)) ^ 2 =
          (Real.sqrt n * M.sqrtDensityRatio theta0 (theta n) x -
            inner ℝ (Real.sqrt n • (theta n - theta0)) (ell x)) ^ 2
        have hsqrt : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
          Real.sq_sqrt (Nat.cast_nonneg n)
        nth_rewrite 1 [← hsqrt]
        rw [real_inner_smul_left]
        ring

private theorem dqm_deficit_mass_scaled_of_rootNBounded
    {Omega : Type*} [MeasurableSpace Omega] {d : ℕ}
    (M : ParametricFamily Omega (EuclideanSpace ℝ (Fin d)))
    (mu : Measure Omega) (theta0 : EuclideanSpace ℝ (Fin d))
    (ell : Omega → EuclideanSpace ℝ (Fin d))
    (hDQM : DifferentiableQuadraticMean M mu theta0 ell)
    (theta : ℕ → EuclideanSpace ℝ (Fin d))
    (hroot : IsRootNBoundedSeq theta theta0) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      ∫ x in {x | M.density theta0 x = 0}, M.density (theta n) x ∂mu)
      atTop (nhds 0) := by
  let delta : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun t => t - theta0
  let r : EuclideanSpace ℝ (Fin d) → Omega → ℝ := fun t x =>
    M.sqrtDensity t x - M.sqrtDensity theta0 x -
      (1 / 2 : ℝ) * inner ℝ (t - theta0) (ell x) * M.sqrtDensity theta0 x
  have hshift : Tendsto delta (nhds theta0) (nhds 0) := by
    simpa [delta] using! (continuous_id.sub
      (continuous_const : Continuous
        (fun _ : EuclideanSpace ℝ (Fin d) => theta0))).tendsto theta0
  have hrO : (fun t => ∫ x, r t x ^ 2 ∂mu) =o[nhds theta0]
      (fun t => ‖t - theta0‖ ^ 2) := by
    have hraw := hDQM.isLittleO.comp_tendsto hshift
    convert! hraw using 1; funext t
    · apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        simp only [r, delta]
        rw [show theta0 + (t - theta0) = t by abel]
  have hR := rootNBounded_scaled_littleO
    (rootNBounded_tendsto_parameter hroot) hroot hrO
  have hrmem : ∀ᶠ n in atTop, MemLp (r (theta n)) 2 mu := by
    have hm := (rootNBounded_tendsto_parameter hroot).eventually
      (hshift.eventually hDQM.mem)
    simpa [Function.comp_apply, r, delta, sub_eq_add_neg, add_assoc] using hm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) hR
    (Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _)
      (setIntegral_nonneg
        (measurableSet_eq_fun (M.density_meas theta0) measurable_const)
        (fun x _ => M.density_nonneg _ x))) ?_
  filter_upwards [hrmem] with n hn
  have hs : MeasurableSet {x | M.density theta0 x = 0} :=
    measurableSet_eq_fun (M.density_meas theta0) measurable_const
  have heq : (n : ℝ) *
        ∫ x in {x | M.density theta0 x = 0}, M.density (theta n) x ∂mu =
      ∫ x in {x | M.density theta0 x = 0}, (n : ℝ) * (r (theta n) x) ^ 2 ∂mu := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hs (fun x hx => ?_)
    have hsqrt0 : M.sqrtDensity theta0 x = 0 := by
      unfold ParametricFamily.sqrtDensity
      rw [hx, Real.sqrt_zero]
    simp only [r, hsqrt0, sub_zero, mul_zero, M.sqrtDensity_sq]
  rw [heq]
  calc
    (∫ x in {x | M.density theta0 x = 0}, (n : ℝ) * (r (theta n) x) ^ 2 ∂mu) ≤
        ∫ x, (n : ℝ) * (r (theta n) x) ^ 2 ∂mu :=
      setIntegral_le_integral (hn.integrable_sq.const_mul (n : ℝ))
        (Eventually.of_forall fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    _ = (n : ℝ) * ∫ x, r (theta n) x ^ 2 ∂mu := by
      rw [integral_const_mul]

private theorem dqm_sqrtDensityRatio_tail_sq_scaled_of_rootNBounded
    {Omega : Type*} [MeasurableSpace Omega] {d : ℕ}
    (M : ParametricFamily Omega (EuclideanSpace ℝ (Fin d)))
    (mu : Measure Omega) (theta0 : EuclideanSpace ℝ (Fin d))
    (ell : Omega → EuclideanSpace ℝ (Fin d))
    (hPDF : IsPDFOf M mu)
    (hDQM : DifferentiableQuadraticMean M mu theta0 ell)
    (theta : ℕ → EuclideanSpace ℝ (Fin d))
    (hroot : IsRootNBoundedSeq theta theta0) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      ∫ x in {x | (1 : ℝ) ≤ |M.sqrtDensityRatio theta0 (theta n) x|},
        M.sqrtDensityRatio theta0 (theta n) x ^ 2
        ∂(modelMeasure M mu theta0)) atTop (nhds 0) := by
  letI := modelMeasure_isProbabilityMeasure M mu hPDF theta0
  letI : IsFiniteMeasure
      (mu.withDensity fun x => ENNReal.ofReal (M.density theta0 x)) :=
    isFiniteMeasure_withDensity_ofReal
      (hPDF.density_integrable theta0).hasFiniteIntegral
  have htail := (dqm_sqrtDensityRatio_tail_controls M mu theta0 ell hPDF hDQM
    (fun _ => (0 : ℝ)) (memLp_const 0) 1 zero_lt_one).2.1
  exact rootNBounded_scaled_littleO
    (rootNBounded_tendsto_parameter hroot) hroot (by simpa using htail)

/- The square-ratio tail also controls the base-law mass of the common-support
good-set complement at the root-`n` scale. -/
private theorem dqm_good_complement_base_mass_scaled_of_rootNBounded
    {Omega : Type*} [MeasurableSpace Omega] {d : ℕ}
    (M : ParametricFamily Omega (EuclideanSpace ℝ (Fin d)))
    (mu : Measure Omega) (theta0 : EuclideanSpace ℝ (Fin d))
    (ell : Omega → EuclideanSpace ℝ (Fin d))
    (hell : Measurable ell)
    (hPDF : IsPDFOf M mu)
    (hDQM : DifferentiableQuadraticMean M mu theta0 ell)
    (theta : ℕ → EuclideanSpace ℝ (Fin d))
    (hroot : IsRootNBoundedSeq theta theta0) :
    let W := fun n => M.sqrtDensityRatio theta0 (theta n)
    let G := fun n => {x | 0 < M.density theta0 x ∧ |W n x| < 1}
    Tendsto (fun n : ℕ => (n : ℝ) *
      (modelMeasure M mu theta0).real (G n)ᶜ) atTop (nhds 0) := by
  dsimp only
  classical
  let P0 := modelMeasure M mu theta0
  let W := fun n => M.sqrtDensityRatio theta0 (theta n)
  let G := fun n => {x | 0 < M.density theta0 x ∧ |W n x| < 1}
  let T := fun n => {x | (1 : ℝ) ≤ |W n x|}
  letI : IsProbabilityMeasure P0 := modelMeasure_isProbabilityMeasure M mu hPDF theta0
  have htheta := rootNBounded_tendsto_parameter hroot
  have hellMem := dqm_score_memLp_modelMeasure M mu theta0 ell
    hell hPDF hDQM
  have hlinear := dqm_sqrtDensityRatio_l2_linearization M mu theta0 ell hPDF hDQM
  have hWmem : ∀ᶠ n in atTop, MemLp (W n) 2 P0 := by
    filter_upwards [htheta.eventually hlinear.1] with n hn
    have hz : MemLp (fun x => inner ℝ (theta n - theta0) (ell x)) 2 P0 :=
      hellMem.continuousLinearMap_comp (innerSL ℝ (theta n - theta0))
    convert! hn.add hz using 1
    funext x
    change W n x = (W n x - inner ℝ (theta n - theta0) (ell x)) +
      inner ℝ (theta n - theta0) (ell x)
    ring
  have hbasePos : ∀ᵐ x ∂P0, 0 < M.density theta0 x := by
    simp only [P0, modelMeasure]
    rw [ae_withDensity_iff (M.density_meas theta0).ennreal_ofReal]
    filter_upwards with x hx
    exact ENNReal.ofReal_pos.mp (bot_lt_iff_ne_bot.mpr hx)
  have hsets (n : ℕ) : (G n)ᶜ =ᵐ[P0] T n := by
    filter_upwards [hbasePos] with x hx
    apply propext
    change (¬ (0 < M.density theta0 x ∧ |W n x| < 1)) ↔ 1 ≤ |W n x|
    simp only [hx, true_and, not_lt]
  have htail := dqm_sqrtDensityRatio_tail_sq_scaled_of_rootNBounded
    M mu theta0 ell hPDF hDQM theta hroot
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail
    (Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg) ?_
  filter_upwards [hWmem] with n hn
  have hsquare : Integrable (fun x => W n x ^ 2) P0 := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (memLp_two_iff_integrable_sq_norm hn.aestronglyMeasurable).mp hn
  have hT : T n = {x | (1 : ℝ) ≤ W n x ^ 2} := by
    ext x
    simp only [T, Set.mem_setOf_eq]
    exact (one_le_sq_iff_one_le_abs (W n x)).symm
  have hTmeas : MeasurableSet (T n) := by
    rw [hT]
    exact measurableSet_le measurable_const ((M.sqrtDensityRatio_measurable
      theta0 (theta n)).pow_const 2)
  have hmass : P0.real (T n) ≤ ∫ x in T n, W n x ^ 2 ∂P0 := by
    rw [show P0.real (T n) = ∫ _x in T n, (1 : ℝ) ∂P0 by simp]
    exact setIntegral_mono_on (integrable_const (c := (1 : ℝ))).integrableOn
      hsquare.integrableOn hTmeas (fun x hx => by simpa only [hT] using! hx)
  calc
    (n : ℝ) * P0.real (G n)ᶜ = (n : ℝ) * P0.real (T n) := by
      congr 1
      exact measureReal_congr (hsets n)
    _ ≤ (n : ℝ) * ∫ x in T n, W n x ^ 2 ∂P0 := by
      exact mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg n)

private theorem density_eq_base_mul_sqrtDensityRatio_sq
    {Omega : Type*} [MeasurableSpace Omega] {d : ℕ}
    (M : ParametricFamily Omega (EuclideanSpace ℝ (Fin d)))
    (theta0 theta : EuclideanSpace ℝ (Fin d)) (x : Omega)
    (hpos : 0 < M.density theta0 x) :
    M.density theta x = M.density theta0 x *
      (1 + M.sqrtDensityRatio theta0 theta x / 2) ^ 2 := by
  have hdiv : 0 ≤ M.density theta x / M.density theta0 x :=
    div_nonneg (M.density_nonneg _ _) hpos.le
  unfold ParametricFamily.sqrtDensityRatio
  rw [show 1 + 2 * (Real.sqrt (M.density theta x / M.density theta0 x) - 1) / 2 =
      Real.sqrt (M.density theta x / M.density theta0 x) by ring,
    Real.sq_sqrt hdiv]
  field_simp

private theorem one_add_half_sq_le_sq_of_one_le_abs (w : ℝ) (h : 1 ≤ |w|) :
    (1 + w / 2) ^ 2 ≤ (9 / 4 : ℝ) * w ^ 2 := by
  have habs : |1 + w / 2| ≤ (3 / 2 : ℝ) * |w| := by
    calc
      |1 + w / 2| ≤ |(1 : ℝ)| + |w / 2| := abs_add_le _ _
      _ = 1 + |w| / 2 := by norm_num [abs_div]
      _ ≤ (3 / 2 : ℝ) * |w| := by linarith
  have hs := pow_le_pow_left₀ (abs_nonneg _) habs 2
  nlinarith [sq_abs w, sq_abs (1 + w / 2)]

private theorem dqm_good_complement_mass_scaled_of_rootNBounded
    {Omega : Type*} [MeasurableSpace Omega] {d : ℕ}
    (M : ParametricFamily Omega (EuclideanSpace ℝ (Fin d)))
    (mu : Measure Omega) (theta0 : EuclideanSpace ℝ (Fin d))
    (ell : Omega → EuclideanSpace ℝ (Fin d))
    (hell : Measurable ell) (hPDF : IsPDFOf M mu)
    (hDQM : DifferentiableQuadraticMean M mu theta0 ell)
    (theta : ℕ → EuclideanSpace ℝ (Fin d))
    (hroot : IsRootNBoundedSeq theta theta0) :
    let W := fun n => M.sqrtDensityRatio theta0 (theta n)
    let G := fun n => {x | 0 < M.density theta0 x ∧ |W n x| < 1}
    Tendsto (fun n : ℕ => (n : ℝ) *
      (modelMeasure M mu (theta n)).real (G n)ᶜ) atTop (nhds 0) := by
  classical
  let W := fun n => M.sqrtDensityRatio theta0 (theta n)
  let G := fun n => {x | 0 < M.density theta0 x ∧ |W n x| < 1}
  let Z : Set Omega := {x | M.density theta0 x = 0}
  let T := fun n => {x | (1 : ℝ) ≤ |W n x|}
  have hG (n : ℕ) : MeasurableSet (G n) :=
    (measurableSet_lt measurable_const (M.density_meas theta0)).inter
      (measurableSet_lt (continuous_abs.measurable.comp
        (M.sqrtDensityRatio_measurable theta0 (theta n))) measurable_const)
  have hZ : MeasurableSet Z :=
    measurableSet_eq_fun (M.density_meas theta0) measurable_const
  have hT (n : ℕ) : MeasurableSet (T n) :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp
      (M.sqrtDensityRatio_measurable theta0 (theta n)))
  have htheta := rootNBounded_tendsto_parameter hroot
  have hellMem := dqm_score_memLp_modelMeasure M mu theta0 ell hell hPDF hDQM
  have hlinear := dqm_sqrtDensityRatio_l2_linearization M mu theta0 ell hPDF hDQM
  have hWmem : ∀ᶠ n in atTop, MemLp (W n) 2 (modelMeasure M mu theta0) := by
    filter_upwards [htheta.eventually hlinear.1] with n hn
    have hz : MemLp (fun x => inner ℝ (theta n - theta0) (ell x)) 2
        (modelMeasure M mu theta0) :=
      hellMem.continuousLinearMap_comp (innerSL ℝ (theta n - theta0))
    convert! hn.add hz using 1
    funext x
    change W n x = (W n x - inner ℝ (theta n - theta0) (ell x)) +
      inner ℝ (theta n - theta0) (ell x)
    abel
  have hdef := dqm_deficit_mass_scaled_of_rootNBounded M mu theta0 ell hDQM theta hroot
  have htail := dqm_sqrtDensityRatio_tail_sq_scaled_of_rootNBounded
    M mu theta0 ell hPDF hDQM theta hroot
  have hupper : Tendsto (fun n : ℕ =>
      (n : ℝ) * ∫ x in Z, M.density (theta n) x ∂mu +
        (9 / 4 : ℝ) * ((n : ℝ) *
          ∫ x in T n, W n x ^ 2 ∂(modelMeasure M mu theta0)))
      atTop (nhds 0) := by
    simpa only [Z, T, W, zero_add, mul_zero] using hdef.add (htail.const_mul (9 / 4 : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun n => mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg) ?_
  filter_upwards [hWmem] with n hn
  letI := modelMeasure_isProbabilityMeasure M mu hPDF (theta n)
  have hmass : (modelMeasure M mu (theta n)).real (G n)ᶜ ≤
      (∫ x in Z, M.density (theta n) x ∂mu) +
        (9 / 4 : ℝ) * ∫ x in T n, W n x ^ 2
          ∂(modelMeasure M mu theta0) := by
    have hleft : (modelMeasure M mu (theta n)).real (G n)ᶜ =
        ∫ x in (G n)ᶜ, M.density (theta n) x ∂mu := by
      have hnonneg := setIntegral_nonneg (μ := mu) (hG n).compl
        (fun x _ => M.density_nonneg (theta n) x)
      rw [modelMeasure, Measure.real, withDensity_apply _ (hG n).compl,
        ← ofReal_integral_eq_lintegral_ofReal (hPDF.density_integrable (theta n)).restrict
          (ae_restrict_of_ae (Eventually.of_forall (M.density_nonneg (theta n)))),
        ENNReal.toReal_ofReal hnonneg]
    have hright : (∫ x in T n, W n x ^ 2
          ∂(modelMeasure M mu theta0)) =
        ∫ x in T n, M.density theta0 x * W n x ^ 2 ∂mu := by
      rw [modelMeasure, setIntegral_withDensity_eq_setIntegral_toReal_smul
        (M.density_meas theta0).ennreal_ofReal (by simp) _ (hT n)]
      apply setIntegral_congr_fun (hT n)
      intro x _
      change (ENNReal.ofReal (M.density theta0 x)).toReal * W n x ^ 2 =
        M.density theta0 x * W n x ^ 2
      rw [ENNReal.toReal_ofReal (M.density_nonneg theta0 x)]
    have hi : Integrable (fun x => M.density theta0 x * W n x ^ 2) mu := by
      have hi' := hn.integrable_sq
      rw [modelMeasure, integrable_withDensity_iff
        (M.density_meas theta0).ennreal_ofReal (by simp)] at hi'
      convert hi' using 1
      funext x
      rw [ENNReal.toReal_ofReal (M.density_nonneg theta0 x)]
      ring
    have hiT : Integrable (fun x =>
        (9 / 4 : ℝ) * (T n).indicator
          (fun x => M.density theta0 x * W n x ^ 2) x) mu :=
      (hi.indicator (hT n)).const_mul (9 / 4 : ℝ)
    have hiZ : Integrable (fun x =>
        Z.indicator (M.density (theta n)) x) mu :=
      (hPDF.density_integrable (theta n)).indicator hZ
    rw [hleft, hright, ← integral_indicator (hG n).compl,
      ← integral_indicator hZ, ← integral_indicator (hT n),
      ← integral_const_mul, ← integral_add hiZ hiT]
    refine integral_mono (hPDF.density_integrable (theta n) |>.indicator (hG n).compl)
      (hiZ.add hiT) ?_
    intro x
    change (G n)ᶜ.indicator (M.density (theta n)) x ≤
      Z.indicator (M.density (theta n)) x +
        (9 / 4 : ℝ) * (T n).indicator
          (fun x => M.density theta0 x * W n x ^ 2) x
    by_cases h0 : M.density theta0 x = 0
    · have hzmem : x ∈ Z := by simpa [Z]
      have hgnmem : x ∉ G n := by simp [G, h0]
      rw [Set.indicator_of_mem (Set.mem_compl hgnmem),
        Set.indicator_of_mem hzmem]
      exact le_add_of_nonneg_right (mul_nonneg (by positivity)
        (Set.indicator_apply_nonneg fun _ => mul_nonneg
          (M.density_nonneg theta0 x) (sq_nonneg _)))
    · have hp : 0 < M.density theta0 x :=
        lt_of_le_of_ne (M.density_nonneg theta0 x) (Ne.symm h0)
      have hznot : x ∉ Z := by simpa [Z]
      by_cases hg : x ∈ G n
      · have hgc : x ∉ (G n)ᶜ := by simpa
        rw [Set.indicator_of_notMem hgc]
        exact add_nonneg
          (Set.indicator_apply_nonneg fun _ => M.density_nonneg (theta n) x)
          (mul_nonneg (by positivity) (Set.indicator_apply_nonneg fun _ =>
            mul_nonneg (M.density_nonneg theta0 x) (sq_nonneg _)))
      · have ht : x ∈ T n := by
          change 1 ≤ |W n x|
          have hng := hg
          simp only [G, Set.mem_setOf_eq, hp, true_and, not_lt] at hng
          exact hng
        rw [Set.indicator_of_mem (Set.mem_compl hg),
          Set.indicator_of_notMem hznot, Set.indicator_of_mem ht, zero_add]
        rw [density_eq_base_mul_sqrtDensityRatio_sq M theta0 (theta n) x hp]
        have hs := one_add_half_sq_le_sq_of_one_le_abs (W n x) ht
        exact mul_le_mul_of_nonneg_left hs (M.density_nonneg theta0 x) |>.trans_eq (by ring)
  calc
    (n : ℝ) * (modelMeasure M mu (theta n)).real (G n)ᶜ ≤
        (n : ℝ) * ((∫ x in Z, M.density (theta n) x ∂mu) +
          (9 / 4 : ℝ) * ∫ x in T n, W n x ^ 2
            ∂(modelMeasure M mu theta0)) :=
      mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg n)
    _ = (n : ℝ) * ∫ x in Z, M.density (theta n) x ∂mu +
        (9 / 4 : ℝ) * ((n : ℝ) *
          ∫ x in T n, W n x ^ 2 ∂(modelMeasure M mu theta0)) := by ring

/- Multiplying an own-law `L²` row by the square root of its density transports
it to `L²` under the common dominating measure. -/
private theorem memLp_sqrt_density_smul'
    {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E]
    [SecondCountableTopology E]
    (mu Q : Measure Omega) (q : Omega → ℝ)
    (hq_meas : Measurable q) (hq_nonneg : ∀ x, 0 ≤ q x)
    (hQ : Q = mu.withDensity (fun x => ENNReal.ofReal (q x)))
    (f : Omega → E) (hf_meas : Measurable f) (hf : MemLp f 2 Q) :
    MemLp (fun x => Real.sqrt (q x) • f x) 2 mu := by
  have hi' : Integrable
      (fun x => ‖f x‖ ^ 2 * (ENNReal.ofReal (q x)).toReal) mu := by
    rw [← integrable_withDensity_iff hq_meas.ennreal_ofReal (by simp), ← hQ]
    convert (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf using 1
  have hi : Integrable (fun x => ‖f x‖ ^ 2 * q x) mu := by
    convert hi' using 1
    funext x
    rw [ENNReal.toReal_ofReal (hq_nonneg x)]
  rw [memLp_two_iff_integrable_sq_norm
    (hq_meas.sqrt.fun_smul hf_meas).aestronglyMeasurable]
  convert hi using 1
  funext x
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (hq_nonneg x)]
  ring

private theorem TendstoInProbZero.mono_norm
    {S : ℕ → Type*} [∀ n, MeasurableSpace (S n)]
    {G H : Type*} [NormedAddCommGroup G] [NormedAddCommGroup H]
    {P : ∀ n, Measure (S n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z : ∀ n, S n → G} {W : ∀ n, S n → H}
    (hW : TendstoInProbZero P W) (h : ∀ n x, ‖Z n x‖ ≤ ‖W n x‖) :
    TendstoInProbZero P Z := by
  intro epsilon hepsilon
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hW epsilon hepsilon)
    (Eventually.of_forall fun _ => measureReal_nonneg)
    (Eventually.of_forall fun n => measureReal_mono fun x hx => hx.trans (h n x))

private theorem TendstoInProbZero.add
    {S : ℕ → Type*} [∀ n, MeasurableSpace (S n)]
    {G : Type*} [NormedAddCommGroup G] {P : ∀ n, Measure (S n)}
    [∀ n, IsProbabilityMeasure (P n)] {Z W : ∀ n, S n → G}
    (hZ : TendstoInProbZero P Z) (hW : TendstoInProbZero P W) :
    TendstoInProbZero P (fun n x => Z n x + W n x) := by
  intro epsilon hepsilon
  have hs : Tendsto (fun n => (P n).real {x | epsilon / 2 ≤ ‖Z n x‖} +
      (P n).real {x | epsilon / 2 ≤ ‖W n x‖}) atTop (nhds 0) := by
    simpa only [add_zero] using (hZ (epsilon / 2) (by positivity)).add
      (hW (epsilon / 2) (by positivity))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hs
    (Eventually.of_forall fun _ => measureReal_nonneg) (Eventually.of_forall fun n => ?_)
  refine (measureReal_mono (fun x hx => ?_)).trans (measureReal_union_le _ _)
  change epsilon ≤ ‖Z n x + W n x‖ at hx
  by_contra hnot
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_le] at hnot
  linarith [norm_add_le (Z n x) (W n x)]

private theorem TendstoInProbZero.finset_sum
    {S : ℕ → Type*} [∀ n, MeasurableSpace (S n)]
    {G : Type*} [NormedAddCommGroup G] {P : ∀ n, Measure (S n)}
    [∀ n, IsProbabilityMeasure (P n)] {I : Type*} (s : Finset I)
    {Z : I → ∀ n, S n → G} (h : ∀ i ∈ s, TendstoInProbZero P (Z i)) :
    TendstoInProbZero P (fun n x => ∑ i ∈ s, Z i n x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro epsilon hepsilon
      have he : ∀ n, {x : S n | epsilon ≤ ‖∑ i ∈ (∅ : Finset I), Z i n x‖} = ∅ := by
        intro n
        ext x
        simp [not_le.mpr hepsilon]
      simp only [he, measureReal_empty]
      exact tendsto_const_nhds
  | @insert a s ha ih =>
      simpa [Finset.sum_insert ha] using TendstoInProbZero.add
        (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem TendstoInProbZero.euclidean_of_coordinate
    {S : ℕ → Type*} [∀ n, MeasurableSpace (S n)] {d : ℕ}
    {P : ∀ n, Measure (S n)} [∀ n, IsProbabilityMeasure (P n)]
    {Z : ∀ n, S n → EuclideanSpace ℝ (Fin d)}
    (hZ : ∀ j, TendstoInProbZero P (fun n x => Z n x j)) :
    TendstoInProbZero P Z := by
  classical
  have hsingle (j : Fin d) : TendstoInProbZero P
      (fun n x => PiLp.single (β := fun _ : Fin d => Real) 2 j (Z n x j)) := by
    exact TendstoInProbZero.mono_norm (hZ j) (fun _ _ => by
      simp only [PiLp.norm_single, Real.norm_eq_abs]
      exact le_rfl)
  have hsum := TendstoInProbZero.finset_sum (Finset.univ : Finset (Fin d))
    (fun j _ => hsingle j)
  convert hsum using 1
  funext n x
  ext j
  simp

private theorem tendstoInProbZero_of_agrees_off_product_bad
    {Omega : Type*} [MeasurableSpace Omega]
    {G : Type*} [NormedAddCommGroup G]
    (P : ℕ → Measure Omega) [∀ n, IsProbabilityMeasure (P n)]
    (B : ℕ → Set Omega) (hB : ∀ n, MeasurableSet (B n))
    (hBmass : Tendsto (fun n : ℕ => (n : ℝ) * (P n).real (B n))
      atTop (nhds 0))
    (Z W : ∀ n, (Fin n → Omega) → G)
    (hagrees : ∀ n X, (∀ i, X i ∉ B n) → Z n X = W n X)
    (hW : TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n)) W) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n)) Z := by
  intro epsilon hepsilon
  have hsum : Tendsto (fun n =>
      (Measure.pi (fun _ : Fin n => P n)).real {X | epsilon ≤ ‖W n X‖} +
        (n : ℝ) * (P n).real (B n)) atTop (nhds 0) := by
    simpa only [zero_add] using (hW epsilon hepsilon).add hBmass
  refine squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_) hsum
  let E : Fin n → Set (Fin n → Omega) := fun i => {X | X i ∈ B n}
  have hcoord (i : Fin n) :
      (Measure.pi (fun _ : Fin n => P n)).real (E i) = (P n).real (B n) := by
    change (Measure.pi (fun _ : Fin n => P n)).real
        (Function.eval i ⁻¹' B n) = (P n).real (B n)
    rw [← map_measureReal_apply (measurable_pi_apply i) (hB n),
      (measurePreserving_eval (fun _ : Fin n => P n) i).map_eq]
  calc
    (Measure.pi (fun _ : Fin n => P n)).real {X | epsilon ≤ ‖Z n X‖} ≤
        (Measure.pi (fun _ : Fin n => P n)).real
          ({X | epsilon ≤ ‖W n X‖} ∪ ⋃ i, E i) := by
      refine measureReal_mono (fun X hX => ?_) (measure_ne_top _ _)
      by_cases hbad : ∃ i, X i ∈ B n
      · exact Or.inr (by
          rcases hbad with ⟨i, hi⟩
          exact Set.mem_iUnion_of_mem i hi)
      · left
        change epsilon ≤ ‖W n X‖
        rw [← hagrees n X (by simpa only [not_exists] using hbad)]
        exact hX
    _ ≤ (Measure.pi (fun _ : Fin n => P n)).real {X | epsilon ≤ ‖W n X‖} +
        (Measure.pi (fun _ : Fin n => P n)).real (⋃ i, E i) := measureReal_union_le _ _
    _ ≤ (Measure.pi (fun _ : Fin n => P n)).real {X | epsilon ≤ ‖W n X‖} +
        ∑ i, (Measure.pi (fun _ : Fin n => P n)).real (E i) := by
      gcongr
      exact measureReal_iUnion_fintype_le E
    _ = (Measure.pi (fun _ : Fin n => P n)).real {X | epsilon ≤ ‖W n X‖} +
        (n : ℝ) * (P n).real (B n) := by
      simp only [hcoord, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

/- A vanishing `L¹` error plus one fixed integrable envelope gives the moving
tail estimate needed by the ratio row, without any fourth moment. -/
private theorem integral_tail_of_vanishing_error_add_envelope
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (z r : ℕ → Omega → ℝ) (g0 : Omega → ℝ)
    (hz_meas : ∀ n, Measurable (z n)) (hr_meas : ∀ n, Measurable (r n))
    (hg_meas : Measurable g0)
    (hz_int : ∀ᶠ n in atTop, Integrable (z n) P)
    (hr_int : ∀ᶠ n in atTop, Integrable (r n) P)
    (hg_int : Integrable g0 P)
    (hz_nonneg : ∀ n x, 0 ≤ z n x) (hr_nonneg : ∀ n x, 0 ≤ r n x)
    (hg_nonneg : ∀ x, 0 ≤ g0 x)
    (hz_le : ∀ᶠ n in atTop, ∀ x, z n x ≤ r n x + g0 x)
    (hr0 : Tendsto (fun n => ∫ x, r n x ∂P) atTop (nhds 0))
    (A : ℕ → ℝ) (hA : Tendsto A atTop atTop) :
    Tendsto (fun n => ∫ x in {x | A n < z n x}, z n x ∂P)
      atTop (nhds 0) := by
  let R : ℕ → Set Omega := fun n => {x | A n / 2 < r n x}
  let H : ℕ → Set Omega := fun n => {x | A n / 2 < g0 x}
  have hAhalf : Tendsto (fun n => A n / 2) atTop atTop :=
    hA.atTop_div_const (by positivity)
  have hR_meas (n : ℕ) : MeasurableSet (R n) :=
    measurableSet_lt measurable_const (hr_meas n)
  have hH_meas (n : ℕ) : MeasurableSet (H n) :=
    measurableSet_lt measurable_const hg_meas
  have hRprob : Tendsto (fun n => P (R n)) atTop (nhds 0) := by
    have hupper : Tendsto (fun n => ENNReal.ofReal
        ((A n / 2)⁻¹ * ∫ x, r n x ∂P)) atTop (nhds 0) := by
      have hinv : Tendsto (fun n => (A n / 2)⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp hAhalf
      have ht := hinv.mul hr0
      have ht' : Tendsto (fun n => (A n / 2)⁻¹ * ∫ x, r n x ∂P)
          atTop (nhds 0) := by simpa only [zero_mul] using ht
      simpa only [zero_mul, Function.comp_apply, ENNReal.ofReal_zero] using!
        (ENNReal.continuous_ofReal.tendsto 0).comp ht'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hAhalf.eventually (eventually_gt_atTop 0), hr_int] with n hn hrn
    have hm := mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall (hr_nonneg n)) hrn (A n / 2)
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      P.real (R n) ≤ P.real {x | A n / 2 ≤ r n x} :=
        measureReal_mono (fun _ hx => by
          simpa only [Set.mem_setOf_eq] using hx.le) (measure_ne_top P _)
      _ ≤ (A n / 2)⁻¹ * ∫ x, r n x ∂P := by
        rw [← div_eq_inv_mul]
        exact (le_div_iff₀ hn).2 (by simpa [mul_comm] using hm)
  have hHprob : Tendsto (fun n => P (H n)) atTop (nhds 0) := by
    have hupper : Tendsto (fun n => ENNReal.ofReal
        ((A n / 2)⁻¹ * ∫ x, g0 x ∂P)) atTop (nhds 0) := by
      have hinv : Tendsto (fun n => (A n / 2)⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp hAhalf
      have ht : Tendsto (fun n => (A n / 2)⁻¹ * ∫ x, g0 x ∂P)
          atTop (nhds 0) := by
        simpa only [zero_mul] using hinv.mul_const (∫ x, g0 x ∂P)
      simpa only [Function.comp_apply, ENNReal.ofReal_zero] using!
        (ENNReal.continuous_ofReal.tendsto 0).comp ht
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hAhalf.eventually (eventually_gt_atTop 0)] with n hn
    have hm := mul_meas_ge_le_integral_of_nonneg
      (Eventually.of_forall hg_nonneg) hg_int (A n / 2)
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      P.real (H n) ≤ P.real {x | A n / 2 ≤ g0 x} :=
        measureReal_mono (fun _ hx => by
          simpa only [Set.mem_setOf_eq] using hx.le) (measure_ne_top P _)
      _ ≤ (A n / 2)⁻¹ * ∫ x, g0 x ∂P := by
        rw [← div_eq_inv_mul]
        exact (le_div_iff₀ hn).2 (by simpa [mul_comm] using hm)
  have hUprob : Tendsto (fun n => P (R n ∪ H n)) atTop (nhds 0) := by
    have hsum : Tendsto (fun n => P (R n) + P (H n)) atTop (nhds 0) := by
      simpa only [zero_add] using hRprob.add hHprob
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      hsum (Eventually.of_forall fun _ => bot_le)
      (Eventually.of_forall fun n => measure_union_le _ _)
  have hgU : Tendsto (fun n => ∫ x in R n ∪ H n, g0 x ∂P)
      atTop (nhds 0) := hg_int.tendsto_setIntegral_nhds_zero hUprob
  have hupper : Tendsto (fun n => (∫ x, r n x ∂P) +
      ∫ x in R n ∪ H n, g0 x ∂P) atTop (nhds 0) := by
    simpa only [zero_add] using hr0.add hgU
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun n => setIntegral_nonneg
      (measurableSet_lt measurable_const (hz_meas n)) (fun x _ => hz_nonneg n x)) ?_
  filter_upwards [hz_int, hr_int, hz_le] with n hzn hrn hzlen
  let B : Set Omega := {x | A n < z n x}
  have hB : MeasurableSet B := measurableSet_lt measurable_const (hz_meas n)
  calc
    (∫ x in B, z n x ∂P) ≤ ∫ x in B, r n x + g0 x ∂P :=
      setIntegral_mono_on hzn.integrableOn
        (hrn.add hg_int).integrableOn hB (fun x _ => hzlen x)
    _ = (∫ x in B, r n x ∂P) + ∫ x in B, g0 x ∂P := by
      rw [integral_add hrn.integrableOn hg_int.integrableOn]
    _ ≤ (∫ x, r n x ∂P) + ∫ x in R n ∪ H n, g0 x ∂P := by
      apply add_le_add
      · exact setIntegral_le_integral hrn
          (Eventually.of_forall (hr_nonneg n))
      · apply setIntegral_mono_set hg_int.integrableOn
          (Eventually.of_forall fun x => hg_nonneg x)
        exact Eventually.of_forall fun x hx => by
          by_contra hnot
          have hrnot : x ∉ R n := fun hr => hnot (Or.inl hr)
          have hgnot : x ∉ H n := fun hh => hnot (Or.inr hh)
          have hrle : r n x ≤ A n / 2 := by simpa [R] using hrnot
          have hgle : g0 x ≤ A n / 2 := by simpa [H] using hgnot
          have hAeq : A n / 2 + A n / 2 = A n := by ring
          have hsumle : r n x + g0 x ≤ A n := by
            rw [← hAeq]
            exact add_le_add hrle hgle
          exact (not_lt_of_ge ((hzlen x).trans hsumle)) hx

/- On the common-support good set, the square-root-density ratio row obeys
the triangular WLLN; the moving `L²` error supplies UI and no fourth moment. -/
private theorem dqm_ratio_row_centered_tendstoInProbZero
    {Omega : Type*} [MeasurableSpace Omega] {d : ℕ}
    (M : ParametricFamily Omega (EuclideanSpace ℝ (Fin d)))
    (mu : Measure Omega) (theta0 : EuclideanSpace ℝ (Fin d))
    (ell : Omega → EuclideanSpace ℝ (Fin d))
    (hell : Measurable ell) (hPDF : IsPDFOf M mu)
    (hDQM : DifferentiableQuadraticMean M mu theta0 ell)
    (theta : ℕ → EuclideanSpace ℝ (Fin d))
    (hroot : IsRootNBoundedSeq theta theta0) :
    let W := fun n => M.sqrtDensityRatio theta0 (theta n)
    let G := fun n => {x | 0 < M.density theta0 x ∧ |W n x| < 1}
    let Y := fun n x => (G n).indicator (fun x =>
      (-Real.sqrt n * W n x / (2 + W n x)) • ell x) x
    TendstoInProbZero
      (fun n => Measure.pi (fun _ : Fin n => modelMeasure M mu (theta n)))
      (fun n X => empMean Y n X - ∫ x, Y n x ∂(modelMeasure M mu (theta n))) := by
  classical
  dsimp only
  let P0 := modelMeasure M mu theta0
  let Pn : ℕ → Measure Omega := fun n => modelMeasure M mu (theta n)
  let u : ℕ → EuclideanSpace ℝ (Fin d) := fun n => Real.sqrt n • (theta n - theta0)
  let W : ℕ → Omega → ℝ := fun n => M.sqrtDensityRatio theta0 (theta n)
  let V : ℕ → Omega → ℝ := fun n x => Real.sqrt n * W n x
  let q : ℕ → Omega → ℝ := fun n x => V n x - inner ℝ (u n) (ell x)
  let G : ℕ → Set Omega := fun n => {x | 0 < M.density theta0 x ∧ |W n x| < 1}
  let Y : ℕ → Omega → EuclideanSpace ℝ (Fin d) := fun n x => (G n).indicator (fun x =>
    (-Real.sqrt n * W n x / (2 + W n x)) • ell x) x
  letI (n : ℕ) := modelMeasure_isProbabilityMeasure M mu hPDF (theta n)
  letI := modelMeasure_isProbabilityMeasure M mu hPDF theta0
  have hG (n : ℕ) : MeasurableSet (G n) :=
    (measurableSet_lt measurable_const (M.density_meas theta0)).inter
      (measurableSet_lt (continuous_abs.measurable.comp
        (M.sqrtDensityRatio_measurable theta0 (theta n))) measurable_const)
  have hYmeas (n : ℕ) : Measurable (Y n) := by
    exact (((measurable_const.mul (M.sqrtDensityRatio_measurable theta0 (theta n))).div
      (measurable_const.add (M.sqrtDensityRatio_measurable theta0 (theta n)))).smul hell)
      |>.indicator (hG n)
  have hroot' := hroot
  obtain ⟨C, hC⟩ := hroot
  have huC : ∀ᶠ n in atTop, ‖u n‖ ≤ max C 0 := by
    filter_upwards [hC] with n hn
    have hu : ‖u n‖ = Real.sqrt n * ‖theta n - theta0‖ := by
      simp [u, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hu]
    exact hn.trans (le_max_left _ _)
  have hellMem := dqm_score_memLp_modelMeasure M mu theta0 ell hell hPDF hDQM
  have hellj (j : Fin d) : MemLp (fun x => ell x j) 2 P0 := by
    simpa [P0] using hellMem.continuousLinearMap_comp
      (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
        EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
  have hq2 : Tendsto (fun n => ∫ x, q n x ^ 2 ∂P0) atTop (nhds 0) := by
    simpa only [q, V, u, P0] using
      dqm_sqrtDensityRatio_scaled_l2_of_rootNBounded
        M mu theta0 ell hPDF hDQM theta hroot'
  have htheta := rootNBounded_tendsto_parameter hroot'
  have hlinear := dqm_sqrtDensityRatio_l2_linearization M mu theta0 ell hPDF hDQM
  have hqMem : ∀ᶠ n in atTop, MemLp (q n) 2 P0 := by
    filter_upwards [htheta.eventually hlinear.1] with n hn
    convert! hn.const_mul (Real.sqrt n) using 1
    funext x
    simp only [q, V, u, real_inner_smul_left]
    ring
  have hqMeas (n : ℕ) : Measurable (q n) := by
    exact ((M.sqrtDensityRatio_measurable theta0 (theta n)).const_mul _).sub
      ((innerSL ℝ (u n)).measurable.comp hell)
  change TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => Pn n))
    (fun n X => empMean Y n X - ∫ x, Y n x ∂(Pn n))
  apply TendstoInProbZero.euclidean_of_coordinate
  intro j
  let z : ℕ → Omega → ℝ := fun n x => |V n x * ell x j|
  let r : ℕ → Omega → ℝ := fun n x => |q n x * ell x j|
  let g0 : Omega → ℝ := fun x => max C 0 * ‖ell x‖ ^ 2
  have hzMeas (n : ℕ) : Measurable (z n) :=
    (((M.sqrtDensityRatio_measurable theta0 (theta n)).const_mul _).mul
      ((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
        EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp hell)).abs
  have hrMeas (n : ℕ) : Measurable (r n) :=
    ((hqMeas n).mul
      ((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
        EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp hell)).abs
  have hgMeas : Measurable g0 := measurable_const.mul (hell.norm.pow_const 2)
  have hgInt : Integrable g0 P0 := by
    exact ((memLp_two_iff_integrable_sq_norm hellMem.aestronglyMeasurable).mp hellMem).const_mul
      (max C 0)
  have hrInt : ∀ᶠ n in atTop, Integrable (r n) P0 := by
    filter_upwards [hqMem] with n hn
    exact (hn.integrable_mul (hellj j)).norm
  have hzInt : ∀ᶠ n in atTop, Integrable (z n) P0 := by
    filter_upwards [hqMem] with n hn
    have hinnerMem : MemLp (fun x => inner ℝ (u n) (ell x)) 2 P0 :=
      hellMem.continuousLinearMap_comp (innerSL ℝ (u n))
    have hV : MemLp (V n) 2 P0 := by
      convert hn.add hinnerMem using 1
      funext x
      change V n x = q n x + inner ℝ (u n) (ell x)
      simp only [q]
      ring
    exact (hV.integrable_mul (hellj j)).norm
  have hr0 : Tendsto (fun n => ∫ x, r n x ∂P0) atTop (nhds 0) := by
    have hbound (n : ℕ) (hn : MemLp (q n) 2 P0) :
        ∫ x, r n x ∂P0 ≤ Real.sqrt (∫ x, q n x ^ 2 ∂P0) *
          Real.sqrt (∫ x, (ell x j) ^ 2 ∂P0) := by
      have hn2 : MemLp (q n) (ENNReal.ofReal (2 : ℝ)) P0 := by
        norm_num
        exact hn
      have hj2 : MemLp (fun x => ell x j) (ENNReal.ofReal (2 : ℝ)) P0 := by
        norm_num
        exact hellj j
      have hcs := integral_mul_norm_le_Lp_mul_Lq (μ := P0) (p := (2 : ℝ)) (q := (2 : ℝ))
        (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) hn2 hj2
      simpa only [r, Real.norm_eq_abs, ← abs_mul, sq_abs, Real.rpow_two,
        one_div, Real.sqrt_eq_rpow] using hcs
    have hu : Tendsto (fun n => Real.sqrt (∫ x, q n x ^ 2 ∂P0) *
        Real.sqrt (∫ x, (ell x j) ^ 2 ∂P0)) atTop (nhds 0) := by
      have hs := hq2.sqrt
      simpa only [Real.sqrt_zero, mul_zero, zero_mul] using
        hs.mul_const (Real.sqrt (∫ x, (ell x j) ^ 2 ∂P0))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Eventually.of_forall fun n => integral_nonneg fun _ => by
        simp only [r]
        positivity) ?_
    filter_upwards [hqMem] with n hn
    exact hbound n hn
  have hzle : ∀ᶠ n in atTop, ∀ x, z n x ≤ r n x + g0 x := by
    filter_upwards [huC] with n hn
    intro x
    have hv : V n x = q n x + inner ℝ (u n) (ell x) := by simp [q]
    have hj : |ell x j| ≤ ‖ell x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (ell x) j
    have hi := abs_real_inner_le_norm (u n) (ell x)
    simp only [z, r, g0, hv]
    calc
      |(q n x + inner ℝ (u n) (ell x)) * ell x j| ≤
          |q n x * ell x j| + |inner ℝ (u n) (ell x) * ell x j| := by
        rw [add_mul]
        exact abs_add_le _ _
      _ ≤ |q n x * ell x j| + max C 0 * ‖ell x‖ ^ 2 := by
        gcongr
        rw [abs_mul]
        nlinarith [abs_nonneg (inner ℝ (u n) (ell x)), abs_nonneg (ell x j),
          norm_nonneg (ell x)]
  have hztail := integral_tail_of_vanishing_error_add_envelope
    P0 z r g0 hzMeas hrMeas hgMeas hzInt hrInt hgInt
    (fun _ _ => abs_nonneg _)
    (fun _ _ => abs_nonneg _)
    (fun _ => mul_nonneg (le_max_right _ _) (sq_nonneg _))
    hzle hr0 (fun n => Real.sqrt n)
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hYjInt (n : ℕ) (j : Fin d) : Integrable (fun x => Y n x j) (Pn n) := by
    simp only [Pn]
    rw [modelMeasure, integrable_withDensity_iff
      (M.density_meas (theta n)).ennreal_ofReal (by simp)]
    have hellMu := (hellj j).integrable one_le_two |>.norm
    simp only [P0] at hellMu
    rw [modelMeasure, integrable_withDensity_iff
      (M.density_meas theta0).ennreal_ofReal (by simp)] at hellMu
    apply Integrable.mono' (hellMu.const_mul (Real.sqrt n * (9 / 4 : ℝ)))
    · exact (((((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)).measurable.comp
          (hYmeas n)).mul
            (M.density_meas (theta n)).ennreal_ofReal.ennreal_toReal).aestronglyMeasurable)
    · filter_upwards with x
      by_cases hx : x ∈ G n
      · have hp := hx.1
        have hw : |W n x| < 1 := hx.2
        have hden : 0 < 2 + W n x := by linarith [neg_abs_le (W n x)]
        simp only [Y]
        rw [Set.indicator_of_mem hx]
        simp only [PiLp.smul_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_div]
        rw [density_eq_base_mul_sqrtDensityRatio_sq M theta0 (theta n) x hp]
        rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg n), abs_of_pos hden,
          abs_of_nonneg ENNReal.toReal_nonneg,
          ENNReal.toReal_ofReal (mul_nonneg (M.density_nonneg _ _) (sq_nonneg _)),
          ENNReal.toReal_ofReal (M.density_nonneg _ _)]
        have hfac : (1 + W n x / 2) ^ 2 / (2 + W n x) ≤ 9 / 4 := by
          have hid : (1 + W n x / 2) ^ 2 / (2 + W n x) =
              (2 + W n x) / 4 := by
            field_simp
            ring
          rw [hid]
          linarith [le_abs_self (W n x)]
        have hnonneg : 0 ≤ Real.sqrt n * |W n x| * |ell x j| *
            M.density theta0 x := by positivity
        change Real.sqrt n * |W n x| / (2 + W n x) * |ell x j| *
            (M.density theta0 x * (1 + W n x / 2) ^ 2) ≤
          Real.sqrt n * (9 / 4 : ℝ) * (|ell x j| * M.density theta0 x)
        calc
          Real.sqrt n * |W n x| / (2 + W n x) * |ell x j| *
              (M.density theta0 x * (1 + W n x / 2) ^ 2) =
              ((1 + W n x / 2) ^ 2 / (2 + W n x)) *
                (Real.sqrt n * |W n x| * |ell x j| * M.density theta0 x) := by ring
          _ ≤ (9 / 4 : ℝ) * (Real.sqrt n * |W n x| * |ell x j| *
                M.density theta0 x) :=
            mul_le_mul_of_nonneg_right hfac hnonneg
          _ ≤ Real.sqrt n * (9 / 4 : ℝ) *
                (|ell x j| * M.density theta0 x) := by
            calc
              (9 / 4 : ℝ) * (Real.sqrt n * |W n x| * |ell x j| *
                  M.density theta0 x) =
                  (Real.sqrt n * (9 / 4 : ℝ) *
                    (|ell x j| * M.density theta0 x)) * |W n x| := by ring
              _ ≤ (Real.sqrt n * (9 / 4 : ℝ) *
                    (|ell x j| * M.density theta0 x)) * 1 :=
                mul_le_mul_of_nonneg_left hw.le (by positivity)
              _ = _ := by ring
      · simp only [Y, Set.indicator_of_notMem hx, PiLp.zero_apply, zero_mul,
          Real.norm_eq_abs, abs_zero,
          ENNReal.toReal_ofReal (M.density_nonneg theta0 x)]
        exact mul_nonneg
          (mul_nonneg (Real.sqrt_nonneg n) (by norm_num))
          (mul_nonneg (abs_nonneg (ell x j)) (M.density_nonneg theta0 x))
  have hpoint (n : ℕ) (x : Omega) :
      (ENNReal.ofReal (M.density (theta n) x)).toReal * |Y n x j| ≤
        (ENNReal.ofReal (M.density theta0 x)).toReal * z n x := by
    by_cases hx : x ∈ G n
    · have hp := hx.1
      have hw : |W n x| < 1 := hx.2
      have hden : 0 < 2 + W n x := by linarith [neg_abs_le (W n x)]
      rw [ENNReal.toReal_ofReal (M.density_nonneg _ _),
        ENNReal.toReal_ofReal (M.density_nonneg _ _)]
      simp only [Y]
      rw [Set.indicator_of_mem hx,
        density_eq_base_mul_sqrtDensityRatio_sq M theta0 (theta n) x hp]
      simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_div, z, V]
      rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg n), abs_of_pos hden]
      have hfac : (1 + W n x / 2) ^ 2 / (2 + W n x) ≤ 1 := by
        have hid : (1 + W n x / 2) ^ 2 / (2 + W n x) =
            (2 + W n x) / 4 := by
          field_simp
          ring
        rw [hid]
        linarith [le_abs_self (W n x)]
      change M.density theta0 x * (1 + W n x / 2) ^ 2 *
          (Real.sqrt n * |W n x| / (2 + W n x) * |ell x j|) ≤
        M.density theta0 x * (Real.sqrt n * |W n x| * |ell x j|)
      calc
        M.density theta0 x * (1 + W n x / 2) ^ 2 *
            (Real.sqrt n * |W n x| / (2 + W n x) * |ell x j|) =
            M.density theta0 x *
              ((1 + W n x / 2) ^ 2 / (2 + W n x)) *
                (Real.sqrt n * |W n x| * |ell x j|) := by ring
        _ ≤ M.density theta0 x * 1 *
              (Real.sqrt n * |W n x| * |ell x j|) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfac (M.density_nonneg theta0 x)) (by positivity)
        _ = M.density theta0 x *
              (Real.sqrt n * |W n x| * |ell x j|) := by ring
    · simp [Y, hx, z, M.density_nonneg, mul_nonneg]
  have hrow (n : ℕ) (hzi : Integrable (z n) P0)
      (S : Set Omega) (hS : MeasurableSet S) :
      ∫ x in S, |Y n x j| ∂(Pn n) ≤ ∫ x in S, z n x ∂P0 := by
    have hyMu := hYjInt n j |>.norm
    simp only [Pn] at hyMu
    rw [modelMeasure, integrable_withDensity_iff
      (M.density_meas (theta n)).ennreal_ofReal (by simp)] at hyMu
    have hzMu := hzi
    simp only [P0] at hzMu
    rw [modelMeasure, integrable_withDensity_iff
      (M.density_meas theta0).ennreal_ofReal (by simp)] at hzMu
    simp only [Pn, P0]
    rw [modelMeasure, modelMeasure,
      setIntegral_withDensity_eq_setIntegral_toReal_smul
        (M.density_meas (theta n)).ennreal_ofReal (by simp) _ hS,
      setIntegral_withDensity_eq_setIntegral_toReal_smul
        (M.density_meas theta0).ennreal_ofReal (by simp) _ hS]
    exact setIntegral_mono_on
      (by simpa only [Real.norm_eq_abs, smul_eq_mul, mul_comm] using hyMu.integrableOn)
      (by simpa only [Real.norm_eq_abs, smul_eq_mul, mul_comm] using hzMu.integrableOn)
      hS (fun x _ => hpoint n x)
  have hfirst : ∀ᶠ n in atTop, ∫ x, |Y n x j| ∂(Pn n) ≤
      1 + ∫ x, g0 x ∂P0 := by
    have hrSmall : ∀ᶠ n in atTop, ∫ x, r n x ∂P0 < 1 :=
      hr0.eventually (Iio_mem_nhds zero_lt_one)
    filter_upwards [hrSmall, hzInt, hrInt, hzle] with n hrn hzi hri hle
    calc
      ∫ x, |Y n x j| ∂(Pn n) ≤ ∫ x, z n x ∂P0 := by
        simpa only [Measure.restrict_univ, setIntegral_univ] using
          hrow n hzi Set.univ MeasurableSet.univ
      _ ≤ ∫ x, r n x + g0 x ∂P0 := integral_mono hzi (hri.add hgInt) hle
      _ = (∫ x, r n x ∂P0) + ∫ x, g0 x ∂P0 := integral_add hri hgInt
      _ ≤ 1 + ∫ x, g0 x ∂P0 := by linarith
  have htail : Tendsto (fun n =>
      ∫ x in {x | Real.sqrt n < |Y n x j|}, |Y n x j| ∂(Pn n))
      atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hztail
      (Eventually.of_forall fun n => setIntegral_nonneg
        (measurableSet_lt measurable_const (continuous_abs.measurable.comp
          ((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
            EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp (hYmeas n))))
        (fun _ _ => abs_nonneg _)) ?_
    filter_upwards [hzInt] with n hzi
    calc
      ∫ x in {x | Real.sqrt n < |Y n x j|}, |Y n x j| ∂(Pn n) ≤
          ∫ x in {x | Real.sqrt n < |Y n x j|}, z n x ∂P0 :=
        hrow n hzi _ (measurableSet_lt measurable_const (continuous_abs.measurable.comp
          ((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
            EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp (hYmeas n))))
      _ ≤ ∫ x in {x | Real.sqrt n < z n x}, z n x ∂P0 := by
        apply setIntegral_mono_set hzi.integrableOn
          (Eventually.of_forall fun _ => abs_nonneg _)
        exact Eventually.of_forall fun x hx => by
          have hyz : |Y n x j| ≤ z n x := by
            by_cases hy : x ∈ G n
            · have hw : |W n x| < 1 := hy.2
              have hden : 1 < 2 + W n x := by linarith [neg_abs_le (W n x)]
              simp only [Y]
              rw [Set.indicator_of_mem hy]
              simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_div, z, V]
              have hden0 : 0 < 2 + W n x := zero_lt_one.trans hden
              rw [abs_of_pos hden0]
              rw [abs_neg, div_mul_eq_mul_div]
              exact (div_le_iff₀ hden0).2
                (le_mul_of_one_le_right (by positivity) hden.le)
            · simp only [Y]
              rw [Set.indicator_of_notMem hy]
              simp only [PiLp.zero_apply, abs_zero, z, abs_mul]
              exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
          exact hx.trans_le hyz
  have htri := triangular_empirical_mean_of_sqrt_tail Pn (fun n x => Y n x j)
    (fun n => (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
      EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).measurable.comp (hYmeas n))
    (fun n => hYjInt n j) (1 + ∫ x, g0 x ∂P0)
    (by
      have hg0nonneg : 0 ≤ ∫ x, g0 x ∂P0 := integral_nonneg fun x => by
        exact mul_nonneg (le_max_right C 0) (sq_nonneg ‖ell x‖)
      linarith) hfirst htail
  convert htri using 1
  funext n X
  simp only [empMean, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  rw [MeasureTheory.eval_integral_piLp (fun k => hYjInt n k) j,
    WithLp.ofLp_sum, Finset.sum_apply]

private theorem centered_empMean_tendstoInProbZero_of_l2
    {Omega : Type*} [MeasurableSpace Omega] {d : ℕ}
    (P : ℕ → Measure Omega) [∀ n, IsProbabilityMeasure (P n)]
    (f : ℕ → Omega → EuclideanSpace ℝ (Fin d))
    (_ : ∀ n, Measurable (f n))
    (hf_memLp : ∀ n, MemLp (f n) 2 (P n))
    (henergy : Tendsto (fun n => ∫ x, ‖f n x‖ ^ 2 ∂(P n)) atTop (nhds 0)) :
    TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => P n))
      (fun n X => Real.sqrt n •
        (empMean f n X - ∫ x, f n x ∂(P n))) := by
  classical
  apply TendstoInProbZero.euclidean_of_coordinate
  intro j epsilon hepsilon
  rw [Metric.tendsto_atTop]
  intro eta heta
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp henergy (epsilon ^ 2 * eta)
    (mul_pos (sq_pos_of_pos hepsilon) heta)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  have hnpos : 0 < n := Nat.zero_lt_one.trans_le hn1
  let m : ℝ := ∫ x, f n x j ∂(P n)
  let centered : Fin n → Omega → ℝ := fun _ x => f n x j - m
  let S : (Fin n → Omega) → ℝ := fun X =>
    (Real.sqrt n * (n : ℝ)⁻¹) * ∑ i, centered i (X i)
  have hfj : MemLp (fun x => f n x j) 2 (P n) := by
    simpa using (hf_memLp n).continuousLinearMap_comp
      (PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
        EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
  have hc (i : Fin n) : MemLp (centered i) 2 (P n) :=
    hfj.sub (memLp_const m)
  have hS : MemLp S 2 (Measure.pi (fun _ : Fin n => P n)) := by
    apply MemLp.const_mul
    rw [show (fun X => ∑ i, centered i (X i)) =
        ∑ i, centered i ∘ Function.eval i by
      ext X
      simp [Function.comp_apply]]
    exact memLp_finset_sum' Finset.univ (fun i _ =>
      (hc i).comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => P n) i))
  have hmean : ∫ X, S X ∂(Measure.pi (fun _ : Fin n => P n)) = 0 := by
    rw [integral_const_mul]
    have heval (i : Fin n) :
        ∫ X, centered i (X i) ∂(Measure.pi (fun _ : Fin n => P n)) = 0 := by
      rw [integral_comp_eval (μ := fun _ : Fin n => P n) (i := i)
        (hc i).aestronglyMeasurable]
      simp [centered, m, integral_sub (hfj.integrable one_le_two)
        (integrable_const (∫ x, f n x j ∂(P n)))]
    have hint : ∀ i, Integrable (fun X : Fin n → Omega => centered i (X i))
        (Measure.pi (fun _ : Fin n => P n)) := fun i =>
      ((hc i).comp_measurePreserving
        (measurePreserving_eval (fun _ : Fin n => P n) i)).integrable one_le_two
    rw [integral_finset_sum _ (fun i _ => hint i)]
    simp only [heval, Finset.sum_const_zero, mul_zero]
  have hvar : ProbabilityTheory.variance S
      (Measure.pi (fun _ : Fin n => P n)) ≤ ∫ x, ‖f n x‖ ^ 2 ∂(P n) := by
    rw [ProbabilityTheory.variance_const_mul]
    have hvsum : ProbabilityTheory.variance
        (fun X : Fin n → Omega => ∑ i, centered i (X i))
          (Measure.pi (fun _ : Fin n => P n)) =
        ∑ i, ProbabilityTheory.variance (centered i) (P n) := by
      rw [show (fun X : Fin n → Omega => ∑ i, centered i (X i)) =
          ∑ i, fun X => centered i (X i) by
        funext X
        simp only [Finset.sum_apply]]
      exact ProbabilityTheory.variance_sum_pi (fun i => hc i)
    rw [hvsum]
    have hvar_each (i : Fin n) : ProbabilityTheory.variance (centered i) (P n) ≤
        ∫ x, (f n x j) ^ 2 ∂(P n) := by
      rw [show centered i = fun x => f n x j - ∫ y, f n y j ∂(P n) by rfl,
        ProbabilityTheory.variance_sub_const hfj.aestronglyMeasurable]
      exact ProbabilityTheory.variance_le_expectation_sq hfj.aestronglyMeasurable
    have hcoord_le (x : Omega) : (f n x j) ^ 2 ≤ ‖f n x‖ ^ 2 := by
      have hj := PiLp.norm_apply_le (f n x) j
      have hj' : |f n x j| ≤ ‖f n x‖ := by
        simpa only [Real.norm_eq_abs] using hj
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (f n x j)) (norm_nonneg (f n x))).2 hj'
    have hint_le : (∫ x, (f n x j) ^ 2 ∂(P n)) ≤
        ∫ x, ‖f n x‖ ^ 2 ∂(P n) := by
      exact integral_mono hfj.integrable_sq
        ((memLp_two_iff_integrable_sq_norm (hf_memLp n).aestronglyMeasurable).mp
          (hf_memLp n)) hcoord_le
    calc
      (Real.sqrt n * (n : ℝ)⁻¹) ^ 2 *
          ∑ i, ProbabilityTheory.variance (centered i) (P n) ≤
          (Real.sqrt n * (n : ℝ)⁻¹) ^ 2 *
            ((n : ℝ) * ∫ x, (f n x j) ^ 2 ∂(P n)) := by
        gcongr
        simpa [nsmul_eq_mul] using Finset.sum_le_sum
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hvar_each i)
      _ = ∫ x, (f n x j) ^ 2 ∂(P n) := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        field_simp
      _ ≤ ∫ x, ‖f n x‖ ^ 2 ∂(P n) := hint_le
  have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hS hepsilon
  simp only [hmean, sub_zero] at hcheb
  have hsmall : ∫ x, ‖f n x‖ ^ 2 ∂(P n) < epsilon ^ 2 * eta := by
    have hnonneg : 0 ≤ ∫ x, ‖f n x‖ ^ 2 ∂(P n) :=
      integral_nonneg fun _ => sq_nonneg _
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hN n hnN
  have hreal : (Measure.pi (fun _ : Fin n => P n)).real
      {X | epsilon ≤ |S X|} < eta := by
    rw [measureReal_def]
    calc
      ((Measure.pi (fun _ : Fin n => P n)) {X | epsilon ≤ |S X|}).toReal ≤
          (ENNReal.ofReal (ProbabilityTheory.variance S
            (Measure.pi (fun _ : Fin n => P n)) / epsilon ^ 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb
      _ = ProbabilityTheory.variance S
            (Measure.pi (fun _ : Fin n => P n)) / epsilon ^ 2 :=
        ENNReal.toReal_ofReal (div_nonneg (ProbabilityTheory.variance_nonneg _ _)
          (sq_nonneg _))
      _ < eta := (div_lt_iff₀ (sq_pos_of_pos hepsilon)).2
        (lt_of_le_of_lt hvar (by simpa only [mul_comm] using hsmall))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  calc
    (Measure.pi (fun _ : Fin n => P n)).real
        {X | epsilon ≤ ‖(Real.sqrt n •
          (empMean f n X - ∫ x, f n x ∂(P n))) j‖} =
        (Measure.pi (fun _ : Fin n => P n)).real {X | epsilon ≤ |S X|} := by
      apply measureReal_congr
      exact Eventually.of_forall fun X => by
        have hSX : (Real.sqrt n •
            (empMean f n X - ∫ x, f n x ∂(P n))) j = S X := by
          simp only [empMean, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, S, centered, m]
          rw [MeasureTheory.eval_integral_piLp
            (fun k => ((hf_memLp n).eval_piLp k).integrable one_le_two) j,
            WithLp.ofLp_sum, Finset.sum_apply,
            Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
          field_simp
        change (epsilon ≤ |(Real.sqrt n •
          (empMean f n X - ∫ x, f n x ∂(P n))) j|) = (epsilon ≤ |S X|)
        rw [hSX]
    _ < eta := hreal

/- A deterministic vector tending to zero is also negligible under every
probability row; this packages the population remainder for the final sum. -/
private theorem tendstoInProbZero_const
    {S : ℕ → Type*} [∀ n, MeasurableSpace (S n)]
    {G : Type*} [NormedAddCommGroup G]
    (P : ∀ n, Measure (S n)) [∀ n, IsProbabilityMeasure (P n)]
    (z : ℕ → G) (hz : Tendsto z atTop (nhds 0)) :
    TendstoInProbZero P (fun n _ => z n) := by
  intro epsilon hepsilon
  have hevent : ∀ᶠ n in atTop, ‖z n‖ < epsilon := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hz epsilon hepsilon
    exact eventually_atTop.2 ⟨N, fun n hn => by
      simpa only [dist_zero_right] using hN n hn⟩
  rw [Metric.tendsto_atTop]
  intro eta heta
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨N, fun n hn => ?_⟩
  have hempty : {x : S n | epsilon ≤ ‖z n‖} = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact not_le.mpr (hN n hn)
  rw [hempty, measureReal_empty, dist_self]
  exact heta

/- Cauchy--Schwarz turns root-`n` vanishing set mass and a uniform rowwise
second-moment bound into a negligible vector set integral. -/
private theorem scaled_setIntegral_tendsto_zero_of_scaled_mass_and_l2_bounded
    {Omega : Type*} [MeasurableSpace Omega]
    (P : ℕ → Measure Omega) [∀ n, IsProbabilityMeasure (P n)]
    (f : ℕ → Omega → ℝ)
    (hf : ∀ n, MemLp (f n) 2 (P n))
    (S : ℕ → Set Omega) (hS : ∀ n, MeasurableSet (S n))
    (hmass : Tendsto (fun n : ℕ => (n : ℝ) * (P n).real (S n)) atTop (nhds 0))
    (C : ℝ) (_ : 0 ≤ C)
    (hbound : ∀ᶠ n in atTop, ∫ x, ‖f n x‖ ^ 2 ∂(P n) ≤ C) :
    Tendsto (fun n : ℕ => Real.sqrt n • ∫ x in S n, f n x ∂(P n))
      atTop (nhds 0) := by
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  have hupper : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) * (P n).real (S n)) *
      Real.sqrt C) atTop (nhds 0) := by
    simpa only [Real.sqrt_zero, zero_mul] using hmass.sqrt.mul_const (Real.sqrt C)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ => abs_nonneg _) ?_
  filter_upwards [hbound] with n hn
  let oneS : Omega → ℝ := (S n).indicator (fun _ => 1)
  have hone : MemLp oneS 2 (P n) := (memLp_const 1).indicator (hS n)
  have hone2 : MemLp oneS (ENNReal.ofReal (2 : ℝ)) (P n) := by
    norm_num
    exact hone
  have hf2 : MemLp (f n) (ENNReal.ofReal (2 : ℝ)) (P n) := by
    norm_num
    exact hf n
  have hcs := integral_mul_norm_le_Lp_mul_Lq (μ := P n) (p := (2 : ℝ))
    (q := (2 : ℝ)) (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    hone2 hf2
  have honeEnergy : ∫ x, ‖oneS x‖ ^ (2 : ℝ) ∂(P n) = (P n).real (S n) := by
    rw [show (fun x => ‖oneS x‖ ^ (2 : ℝ)) =
        (S n).indicator (fun _ => (1 : ℝ)) by
      funext x
      by_cases hx : x ∈ S n <;> simp [oneS, hx]]
    simp [integral_indicator (hS n)]
  have hsetAbs : |∫ x in S n, f n x ∂(P n)| ≤
      Real.sqrt ((P n).real (S n)) * Real.sqrt (∫ x, (f n x) ^ 2 ∂(P n)) := by
    calc
      |∫ x in S n, f n x ∂(P n)| ≤ ∫ x in S n, |f n x| ∂(P n) :=
        abs_integral_le_integral_abs
      _ = ∫ x, ‖oneS x‖ * ‖f n x‖ ∂(P n) := by
        rw [← integral_indicator (hS n)]
        apply integral_congr_ae
        exact Eventually.of_forall fun x => by
          by_cases hx : x ∈ S n <;> simp [oneS, hx]
      _ ≤ _ := by
        rw [honeEnergy] at hcs
        simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, one_div,
          Real.sqrt_eq_rpow] using hcs
  calc
    |Real.sqrt n • ∫ x in S n, f n x ∂(P n)| =
        Real.sqrt n * |∫ x in S n, f n x ∂(P n)| := by
      rw [smul_eq_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg n)]
    _ ≤ Real.sqrt n *
        (Real.sqrt ((P n).real (S n)) * Real.sqrt (∫ x, (f n x) ^ 2 ∂(P n))) :=
      mul_le_mul_of_nonneg_left hsetAbs (Real.sqrt_nonneg n)
    _ ≤ Real.sqrt n * (Real.sqrt ((P n).real (S n)) * Real.sqrt C) := by
      gcongr
      simpa only [Real.norm_eq_abs, sq_abs] using hn
    _ = Real.sqrt ((n : ℝ) * (P n).real (S n)) * Real.sqrt C := by
      rw [Real.sqrt_mul (Nat.cast_nonneg n)]
      ring

/- Finite-dimensional deterministic convergence is checked coordinatewise. -/
private theorem tendsto_euclidean_zero_of_coordinate
    {d : ℕ} (z : ℕ → EuclideanSpace ℝ (Fin d))
    (hz : ∀ j, Tendsto (fun n => z n j) atTop (nhds 0)) :
    Tendsto z atTop (nhds 0) := by
  classical
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hsum : Tendsto (fun n => ∑ j, |z n j|) atTop (nhds 0) := by
    simpa using
      tendsto_finset_sum Finset.univ (fun j _ => (hz j).abs)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  exact Eventually.of_forall fun n => by
    have hdec : ∑ j, z n j • EuclideanSpace.single j (1 : ℝ) = z n := by
      simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
        (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (z n)
    calc
      ‖z n‖ = ‖∑ j, z n j • EuclideanSpace.single j (1 : ℝ)‖ := by rw [hdec]
      _ ≤ ∑ j, ‖z n j • EuclideanSpace.single j (1 : ℝ)‖ := norm_sum_le _ _
      _ = ∑ j, |z n j| := by
        apply Finset.sum_congr rfl
        intro j _
        simp [norm_smul]

/-- **Combined weighted-score empirical linearization (vdV 25.56).**

For a deterministic root-`n` local sequence, DQM and weighted `L²` convergence
identify the moving centered empirical score increment with the negative
population-Gram drift.  This is the single book-backed cancellation statement;
neither summand is asserted to vanish separately.

The proof expands the square-root-density identity, uses DQM for the
Hellinger remainder, and transfer the resulting triangular-array second-moment
bound to the moving product laws. -/
theorem weightedScore_centeredEmpMean_linearization_of_dqm_rootNBounded
    {Omega : Type*} [MeasurableSpace Omega] {d : ℕ}
    (M : ParametricFamily Omega (EuclideanSpace ℝ (Fin d)))
    (μ : Measure Omega) (θ0 : EuclideanSpace ℝ (Fin d))
    (ℓ : Omega → EuclideanSpace ℝ (Fin d))
    -- `M` is a probability-density family with respect to `μ`.
    (hPDF : IsPDFOf M μ)
    -- strong measurability of the limiting score is needed by the
    -- Bochner-integral and empirical-mean APIs.
    (hℓ : Measurable ℓ)
    -- differentiability in quadratic mean at the true parameter.
    (hDQM : DifferentiableQuadraticMean M μ θ0 ℓ)
    (θn : ℕ → EuclideanSpace ℝ (Fin d))
    -- the deterministic local parameter sequence is root-`n` bounded.
    (hθn : IsRootNBoundedSeq θn θ0)
    (fn : ℕ → Omega → EuclideanSpace ℝ (Fin d))
    -- rowwise score measurability for product-law empirical statistics.
    (hfn_meas : ∀ n, Measurable (fn n))
    -- each moving score is square-integrable under its own model law.
    (hfn_memLp : ∀ n, MemLp (fn n) 2 (modelMeasure M μ (θn n)))
    -- each moving score is centered under its own model law.
    (hfn_centered : ∀ n, (∫ x, fn n x ∂(modelMeasure M μ (θn n))) = 0)
    -- literal weighted-score `L²(μ)` convergence from vdV (25.56).
    (hweighted : Tendsto (fun n => ∫ x,
      ‖M.sqrtDensity (θn n) x • fn n x - M.sqrtDensity θ0 x • ℓ x‖ ^ 2 ∂μ)
      atTop (nhds 0)) :
    TendstoInProbZero
      (fun n => Measure.pi (fun _ : Fin n => modelMeasure M μ (θn n)))
      (fun n X =>
        Real.sqrt n • (empMean fn n X - empMean (fun _ => ℓ) n X) +
          Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
            (populationGram (modelMeasure M μ θ0) ℓ)
            (Real.sqrt n • (θn n - θ0))) := by
  classical
  let P0 := modelMeasure M μ θ0
  let Pn : ℕ → Measure Omega := fun n => modelMeasure M μ (θn n)
  let W : ℕ → Omega → ℝ := fun n => M.sqrtDensityRatio θ0 (θn n)
  let G : ℕ → Set Omega := fun n => {x | 0 < M.density θ0 x ∧ |W n x| < 1}
  let R : ℕ → Omega → EuclideanSpace ℝ (Fin d) := fun n x =>
    (G n).indicator (fun x => (M.sqrtDensity (θn n) x)⁻¹ •
      (M.sqrtDensity (θn n) x • fn n x - M.sqrtDensity θ0 x • ℓ x)) x
  let Y : ℕ → Omega → EuclideanSpace ℝ (Fin d) := fun n x =>
    (G n).indicator (fun x =>
      (-Real.sqrt n * W n x / (2 + W n x)) • ℓ x) x
  let gram := Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin d)
    (populationGram P0 ℓ)
  let D : ℕ → EuclideanSpace ℝ (Fin d) := fun n =>
    Real.sqrt n • (∫ x, R n x ∂(Pn n)) + (∫ x, Y n x ∂(Pn n)) +
      gram (Real.sqrt n • (θn n - θ0))
  let Z : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d) := fun n X =>
    Real.sqrt n • (empMean fn n X - empMean (fun _ => ℓ) n X) +
      gram (Real.sqrt n • (θn n - θ0))
  let H : ∀ n, (Fin n → Omega) → EuclideanSpace ℝ (Fin d) := fun n X =>
    Real.sqrt n • (empMean R n X - ∫ x, R n x ∂(Pn n)) +
      (empMean Y n X - ∫ x, Y n x ∂(Pn n)) + D n
  letI (n : ℕ) := modelMeasure_isProbabilityMeasure M μ hPDF (θn n)
  letI := modelMeasure_isProbabilityMeasure M μ hPDF θ0
  have hG (n : ℕ) : MeasurableSet (G n) :=
    (measurableSet_lt measurable_const (M.density_meas θ0)).inter
      (measurableSet_lt (continuous_abs.measurable.comp
        (M.sqrtDensityRatio_measurable θ0 (θn n))) measurable_const)
  have hRmeas (n : ℕ) : Measurable (R n) := by
    exact ((M.sqrtDensity_meas (θn n)).inv.smul
      ((M.sqrtDensity_meas (θn n)).smul (hfn_meas n) |>.sub
        ((M.sqrtDensity_meas θ0).smul hℓ))).indicator (hG n)
  have hbad : Tendsto (fun n : ℕ => (n : ℝ) * (Pn n).real (G n)ᶜ)
      atTop (nhds 0) := by
    simpa only [Pn, G, W] using
      dqm_good_complement_mass_scaled_of_rootNBounded
        M μ θ0 ℓ hℓ hPDF hDQM θn hθn
  have hratio : TendstoInProbZero
      (fun n => Measure.pi (fun _ : Fin n => Pn n))
      (fun n X => empMean Y n X - ∫ x, Y n x ∂(Pn n)) := by
    simpa only [Pn, Y, G, W] using
      dqm_ratio_row_centered_tendstoInProbZero
        M μ θ0 ℓ hℓ hPDF hDQM θn hθn
  have hRcenter : TendstoInProbZero
      (fun n => Measure.pi (fun _ : Fin n => Pn n))
      (fun n X => Real.sqrt n •
        (empMean R n X - ∫ x, R n x ∂(Pn n))) := by
    let e : ℕ → Omega → EuclideanSpace ℝ (Fin d) := fun n x =>
      M.sqrtDensity (θn n) x • fn n x - M.sqrtDensity θ0 x • ℓ x
    have hgMem (n : ℕ) : MemLp (fun x => M.sqrtDensity (θn n) x • fn n x) 2 μ := by
      simpa only [Pn, modelMeasure] using! memLp_sqrt_density_smul' μ (Pn n)
        (M.density (θn n)) (M.density_meas (θn n)) (M.density_nonneg (θn n))
        rfl (fn n) (hfn_meas n) (hfn_memLp n)
    have hg0Mem : MemLp (fun x => M.sqrtDensity θ0 x • ℓ x) 2 μ := by
      have hℓMem := dqm_score_memLp_modelMeasure M μ θ0 ℓ hℓ hPDF hDQM
      simpa only [P0, modelMeasure] using! memLp_sqrt_density_smul' μ P0
        (M.density θ0) (M.density_meas θ0) (M.density_nonneg θ0)
        rfl ℓ hℓ hℓMem
    have heMem (n : ℕ) : MemLp (e n) 2 μ := (hgMem n).sub hg0Mem
    have hRweightedEq (n : ℕ) :
        (fun x => ‖R n x‖ ^ 2 * M.density (θn n) x) =
          fun x => (G n).indicator (fun x => ‖e n x‖ ^ 2) x := by
      funext x
      by_cases hx : x ∈ G n
      · have hp0 := hx.1
        have hpn : 0 < M.density (θn n) x := by
          rw [density_eq_base_mul_sqrtDensityRatio_sq M θ0 (θn n) x hp0]
          have hden : 0 < 1 + W n x / 2 := by
            have := hx.2
            linarith [neg_abs_le (W n x)]
          positivity
        rw [Set.indicator_of_mem hx]
        simp only [R, e, Set.indicator_of_mem hx, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (M.sqrtDensity_nonneg _ _)), mul_pow]
        rw [← M.sqrtDensity_sq]
        have hs : M.sqrtDensity (θn n) x ≠ 0 := (Real.sqrt_pos.2 hpn).ne'
        field_simp [hs]
      · rw [Set.indicator_of_notMem hx]
        simp only [R, Set.indicator_of_notMem hx, norm_zero]
        norm_num
    have hRenergy (n : ℕ) :
        ∫ x, ‖R n x‖ ^ 2 ∂(Pn n) = ∫ x in G n, ‖e n x‖ ^ 2 ∂μ := by
      simp only [Pn]
      rw [modelMeasure, integral_withDensity_eq_integral_toReal_smul
        (M.density_meas (θn n)).ennreal_ofReal (by simp), ← integral_indicator (hG n)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change (ENNReal.ofReal (M.density (θn n) x)).toReal * ‖R n x‖ ^ 2 = _
        rw [ENNReal.toReal_ofReal (M.density_nonneg (θn n) x)]
        rw [mul_comm]
        exact congrFun (hRweightedEq n) x
    have hRMem (n : ℕ) : MemLp (R n) 2 (Pn n) := by
      rw [memLp_two_iff_integrable_sq_norm (hRmeas n).aestronglyMeasurable]
      simp only [Pn]
      rw [modelMeasure, integrable_withDensity_iff
        (M.density_meas (θn n)).ennreal_ofReal (by simp)]
      have heInt := (memLp_two_iff_integrable_sq_norm
        (heMem n).aestronglyMeasurable).mp (heMem n) |>.indicator (hG n)
      convert! heInt using 1
      funext x
      rw [ENNReal.toReal_ofReal (M.density_nonneg (θn n) x)]
      exact congrFun (hRweightedEq n) x
    have henergy : Tendsto (fun n => ∫ x, ‖R n x‖ ^ 2 ∂(Pn n))
        atTop (nhds 0) := by
      rw [show (fun n => ∫ x, ‖R n x‖ ^ 2 ∂(Pn n)) =
          fun n => ∫ x in G n, ‖e n x‖ ^ 2 ∂μ by
        funext n
        exact hRenergy n]
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hweighted
        (Eventually.of_forall fun n => setIntegral_nonneg (hG n) (fun _ _ => sq_nonneg _))
        (Eventually.of_forall fun n => setIntegral_le_integral
          ((memLp_two_iff_integrable_sq_norm (heMem n).aestronglyMeasurable).mp (heMem n))
          (Eventually.of_forall fun _ => sq_nonneg _))
    exact centered_empMean_tendstoInProbZero_of_l2 Pn R hRmeas hRMem henergy
  have hD : Tendsto D atTop (nhds 0) := by
    let e : ℕ → Omega → EuclideanSpace ℝ (Fin d) := fun n x =>
      M.sqrtDensity (θn n) x • fn n x - M.sqrtDensity θ0 x • ℓ x
    let g0 : Omega → EuclideanSpace ℝ (Fin d) := fun x => M.sqrtDensity θ0 x • ℓ x
    let g : ℕ → Omega → EuclideanSpace ℝ (Fin d) := fun n x =>
      M.sqrtDensity (θn n) x • fn n x
    have hgMem (n : ℕ) : MemLp (g n) 2 μ := by
      simpa only [Pn, g, modelMeasure] using! memLp_sqrt_density_smul' μ (Pn n)
        (M.density (θn n)) (M.density_meas (θn n)) (M.density_nonneg (θn n))
        rfl (fn n) (hfn_meas n) (hfn_memLp n)
    have hg0Mem : MemLp g0 2 μ := by
      have hℓMem := dqm_score_memLp_modelMeasure M μ θ0 ℓ hℓ hPDF hDQM
      simpa only [P0, g0, modelMeasure] using! memLp_sqrt_density_smul' μ P0
        (M.density θ0) (M.density_meas θ0) (M.density_nonneg θ0)
        rfl ℓ hℓ hℓMem
    have heMem (n : ℕ) : MemLp (e n) 2 μ := by
      simpa only [e, g, g0] using! (hgMem n).sub hg0Mem
    let B0 := ∫ x, ‖g0 x‖ ^ 2 ∂μ
    let C := 2 + 2 * B0
    have hB0 : 0 ≤ B0 := integral_nonneg fun _ => sq_nonneg _
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hgEnergy : ∀ᶠ n in atTop, ∫ x, ‖g n x‖ ^ 2 ∂μ ≤ C := by
      have heSmall : ∀ᶠ n in atTop, ∫ x, ‖e n x‖ ^ 2 ∂μ ≤ 1 :=
        hweighted.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))
      filter_upwards [heSmall] with n hn
      have heInt := (memLp_two_iff_integrable_sq_norm
        (heMem n).aestronglyMeasurable).mp (heMem n)
      have hg0Int := (memLp_two_iff_integrable_sq_norm
        hg0Mem.aestronglyMeasurable).mp hg0Mem
      calc
        ∫ x, ‖g n x‖ ^ 2 ∂μ ≤ ∫ x, 2 * ‖e n x‖ ^ 2 + 2 * ‖g0 x‖ ^ 2 ∂μ := by
          apply integral_mono
          · exact (memLp_two_iff_integrable_sq_norm (hgMem n).aestronglyMeasurable).mp (hgMem n)
          · exact (heInt.const_mul 2).add (hg0Int.const_mul 2)
          · intro x
            dsimp only
            have heq : g n x = e n x + g0 x := by simp [e, g, g0]
            rw [heq]
            calc
              ‖e n x + g0 x‖ ^ 2 ≤ (‖e n x‖ + ‖g0 x‖) ^ 2 :=
                (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (norm_add_le _ _)
              _ ≤ 2 * ‖e n x‖ ^ 2 + 2 * ‖g0 x‖ ^ 2 := by
                nlinarith [sq_nonneg (‖e n x‖ - ‖g0 x‖)]
        _ = 2 * (∫ x, ‖e n x‖ ^ 2 ∂μ) + 2 * B0 := by
          rw [integral_add (heInt.const_mul 2) (hg0Int.const_mul 2),
            integral_const_mul, integral_const_mul]
        _ ≤ C := by dsimp [C]; linarith
    have hfnEnergy (n : ℕ) : ∫ x, ‖fn n x‖ ^ 2 ∂(Pn n) = ∫ x, ‖g n x‖ ^ 2 ∂μ := by
      simp only [Pn, modelMeasure]
      rw [integral_withDensity_eq_integral_toReal_smul
        (M.density_meas (θn n)).ennreal_ofReal (by simp)]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change (ENNReal.ofReal (M.density (θn n) x)).toReal * ‖fn n x‖ ^ 2 =
          ‖g n x‖ ^ 2
        rw [ENNReal.toReal_ofReal (M.density_nonneg (θn n) x)]
        simp only [g, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (M.sqrtDensity_nonneg _ _), mul_pow, M.sqrtDensity_sq]
    have hP0bad : Tendsto (fun n : ℕ => (n : ℝ) * P0.real (G n)ᶜ)
        atTop (nhds 0) := by
      simpa only [P0, G, W] using
        dqm_good_complement_base_mass_scaled_of_rootNBounded
          M μ θ0 ℓ hℓ hPDF hDQM θn hθn
    have hbadFn (j : Fin d) : Tendsto
        (fun n : ℕ => Real.sqrt n • ∫ x in (G n)ᶜ, fn n x j ∂(Pn n))
        atTop (nhds 0) := by
      apply scaled_setIntegral_tendsto_zero_of_scaled_mass_and_l2_bounded
        Pn (fun n x => fn n x j) (fun n => (hfn_memLp n).eval_piLp j)
        (fun n => (G n)ᶜ) (fun n => (hG n).compl) hbad C hC
      filter_upwards [hgEnergy] with n hn
      calc
        ∫ x, ‖fn n x j‖ ^ 2 ∂(Pn n) ≤ ∫ x, ‖fn n x‖ ^ 2 ∂(Pn n) := by
          apply integral_mono
          · exact (memLp_two_iff_integrable_sq_norm
              ((hfn_memLp n).eval_piLp j).aestronglyMeasurable).mp
                ((hfn_memLp n).eval_piLp j)
          · exact (memLp_two_iff_integrable_sq_norm
              (hfn_memLp n).aestronglyMeasurable).mp (hfn_memLp n)
          · intro x
            exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
              (PiLp.norm_apply_le (fn n x) j)
        _ = ∫ x, ‖g n x‖ ^ 2 ∂μ := hfnEnergy n
        _ ≤ C := hn
    have hℓMem := dqm_score_memLp_modelMeasure M μ θ0 ℓ hℓ hPDF hDQM
    have hbadℓ (j : Fin d) : Tendsto
        (fun n : ℕ => Real.sqrt n • ∫ x in (G n)ᶜ, ℓ x j ∂P0)
        atTop (nhds 0) := by
      apply scaled_setIntegral_tendsto_zero_of_scaled_mass_and_l2_bounded
        (fun _ => P0) (fun _ x => ℓ x j) (fun _ => hℓMem.eval_piLp j)
        (fun n => (G n)ᶜ) (fun n => (hG n).compl) hP0bad
        (∫ x, ‖ℓ x j‖ ^ 2 ∂P0) (integral_nonneg fun _ => sq_nonneg _)
      exact Eventually.of_forall fun _ => le_rfl
    let u : ℕ → EuclideanSpace ℝ (Fin d) := fun n => Real.sqrt n • (θn n - θ0)
    let V : ℕ → Omega → ℝ := fun n x => Real.sqrt n * W n x
    let q : ℕ → Omega → ℝ := fun n x => V n x - inner ℝ (u n) (ℓ x)
    have htheta := rootNBounded_tendsto_parameter hθn
    have hlinear := dqm_sqrtDensityRatio_l2_linearization M μ θ0 ℓ hPDF hDQM
    have hqMem : ∀ᶠ n in atTop, MemLp (q n) 2 P0 := by
      filter_upwards [htheta.eventually hlinear.1] with n hn
      convert! hn.const_mul (Real.sqrt n) using 1
      funext x
      simp only [q, V, u, W, real_inner_smul_left]
      ring
    have hq2 : Tendsto (fun n => ∫ x, q n x ^ 2 ∂P0) atTop (nhds 0) := by
      simpa only [q, V, u, W, P0] using
        dqm_sqrtDensityRatio_scaled_l2_of_rootNBounded M μ θ0 ℓ hPDF hDQM θn hθn
    have hWMem : ∀ᶠ n in atTop, MemLp (W n) 2 P0 := by
      filter_upwards [htheta.eventually hlinear.1] with n hn
      have hz := hℓMem.continuousLinearMap_comp (innerSL ℝ (θn n - θ0))
      convert! hn.add hz using 1
      funext x
      change W n x = (W n x - inner ℝ (θn n - θ0) (ℓ x)) +
        inner ℝ (θn n - θ0) (ℓ x)
      ring
    have hW2 : Tendsto (fun n => ∫ x, W n x ^ 2 ∂P0) atTop (nhds 0) := by
      let s : EuclideanSpace ℝ (Fin d) → ℝ := fun t => ‖t - θ0‖
      have hs0 : Tendsto (fun t : EuclideanSpace ℝ (Fin d) => s t ^ 2)
          (nhds θ0) (nhds 0) := by
        have hs : Tendsto s (nhds θ0) (nhds 0) := by
          convert! (continuous_norm.comp (continuous_id.sub
            (continuous_const : Continuous
              (fun _ : EuclideanSpace ℝ (Fin d) => θ0)))).tendsto θ0 using 1 <;>
            simp
        convert hs.pow 2 using 1; norm_num
      have hrem : Tendsto (fun t => (∫ x, M.sqrtDensityRatio θ0 t x ^ 2 ∂P0) -
          fisherInformation M μ θ0 ℓ (t - θ0) (t - θ0)) (nhds θ0) (nhds 0) := by
        apply (show (fun t => (∫ x, M.sqrtDensityRatio θ0 t x ^ 2 ∂P0) -
          fisherInformation M μ θ0 ℓ (t - θ0) (t - θ0)) =o[nhds θ0]
            (fun t => s t ^ 2) by
          simpa only [P0, modelMeasure, s] using
            dqm_sqrtDensityRatio_sq_expansion M μ θ0 ℓ hPDF hDQM).trans_tendsto hs0
      have hshift : Tendsto (fun t : EuclideanSpace ℝ (Fin d) => t - θ0)
          (nhds θ0) (nhds 0) := by
        simpa using! (continuous_id.sub
          (continuous_const : Continuous
            (fun _ : EuclideanSpace ℝ (Fin d) => θ0))).tendsto θ0
      have hfish : Tendsto
          (fun t => fisherInformation M μ θ0 ℓ (t - θ0) (t - θ0))
          (nhds θ0) (nhds 0) := by
        simpa [fisherInformation, pow_two] using!
          (dqm_fisher_cont M μ θ0 ℓ (hPDF.density_integrable θ0) hDQM
            (fun _ _ => hPDF.density_integrable _)).comp hshift
      have hall : Tendsto (fun t => ∫ x, M.sqrtDensityRatio θ0 t x ^ 2 ∂P0)
          (nhds θ0) (nhds 0) := by
        simpa only [sub_add_cancel, zero_add] using hrem.add hfish
      simpa only [W] using! hall.comp htheta
    have hWmeasure : TendstoInMeasure P0 W atTop (fun _ => 0) := by
      rw [tendstoInMeasure_iff_norm]
      intro delta hdelta
      simpa only [sub_zero, Real.norm_eq_abs] using
        L2Utils.l2_markov_tail_tendsto atTop P0 W
          (fun n => M.sqrtDensityRatio_measurable θ0 (θn n)) hWMem hW2 delta hdelta
    have hgoodWscore : Tendsto (fun n => ∫ x in G n, |W n x| * ‖ℓ x‖ ^ 2 ∂P0)
        atTop (nhds 0) := by
      apply Filter.tendsto_of_subseq_tendsto
      intro ns hns
      obtain ⟨ms, _hms, hae⟩ := (hWmeasure.comp hns).exists_seq_tendsto_ae
      refine ⟨ms, ?_⟩
      rw [show (fun k => ∫ x in G (ns (ms k)), |W (ns (ms k)) x| * ‖ℓ x‖ ^ 2 ∂P0) =
          fun k => ∫ x, (G (ns (ms k))).indicator
            (fun x => |W (ns (ms k)) x| * ‖ℓ x‖ ^ 2) x ∂P0 by
        funext k
        rw [integral_indicator (hG (ns (ms k)))]]
      rw [show (0 : ℝ) = ∫ _x, (0 : ℝ) ∂P0 by simp]
      refine tendsto_integral_filter_of_dominated_convergence (l := (atTop : Filter ℕ))
        (μ := P0) (F := fun k x => (G (ns (ms k))).indicator
          (fun x => |W (ns (ms k)) x| * ‖ℓ x‖ ^ 2) x)
        (f := fun _ : Omega => (0 : ℝ)) (fun x => ‖ℓ x‖ ^ 2) ?_ ?_
        ((memLp_two_iff_integrable_sq_norm hℓMem.aestronglyMeasurable).mp hℓMem) ?_
      · exact Eventually.of_forall fun k =>
          (((M.sqrtDensityRatio_measurable θ0 (θn (ns (ms k)))).abs.mul
            (hℓ.norm.pow_const 2)).indicator (hG (ns (ms k)))).aestronglyMeasurable
      · exact Eventually.of_forall fun k => Eventually.of_forall fun x => by
          by_cases hx : x ∈ G (ns (ms k))
          · rw [Set.indicator_of_mem hx]
            simp only [Real.norm_eq_abs, abs_mul, abs_abs, abs_pow, abs_norm]
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hx.2.le (sq_nonneg ‖ℓ x‖)
          · simp [hx]
      · filter_upwards [hae] with x hx
        have habs := hx.abs
        have hprod : Tendsto (fun k => |W (ns (ms k)) x| * ‖ℓ x‖ ^ 2)
            atTop (nhds 0) := by simpa using habs.mul_const (‖ℓ x‖ ^ 2)
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hprod
          (Eventually.of_forall fun k => by
            by_cases hk : x ∈ G (ns (ms k))
            · rw [Set.indicator_of_mem hk]
              exact mul_nonneg (abs_nonneg _) (sq_nonneg _)
            · simp [hk]) ?_
        exact Eventually.of_forall fun k => by
          by_cases hk : x ∈ G (ns (ms k))
          · rw [Set.indicator_of_mem hk]
          · rw [Set.indicator_of_notMem hk]
            exact mul_nonneg (abs_nonneg _) (sq_nonneg _)
    obtain ⟨Cu, hCu⟩ := hθn
    have huBound : ∀ᶠ n in atTop, ‖u n‖ ≤ max Cu 0 := by
      filter_upwards [hCu] with n hn
      simp only [u, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg n)]
      exact hn.trans (le_max_left _ _)
    have hP0badReal : Tendsto (fun n => P0.real (G n)ᶜ) atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hP0bad
        (Eventually.of_forall fun _ => measureReal_nonneg) ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [measureReal_nonneg (μ := P0) (s := (G n)ᶜ)]
    have hP0badMeasure : Tendsto (fun n => P0 (G n)ᶜ) atTop (nhds 0) := by
      rw [← ENNReal.tendsto_toReal_zero_iff (fun n => measure_ne_top P0 (G n)ᶜ)]
      simpa only [measureReal_def] using hP0badReal
    have hscoreTail : Tendsto (fun n => ∫ x in (G n)ᶜ, ‖ℓ x‖ ^ 2 ∂P0)
        atTop (nhds 0) :=
      ((memLp_two_iff_integrable_sq_norm hℓMem.aestronglyMeasurable).mp hℓMem)
        |>.tendsto_setIntegral_nhds_zero hP0badMeasure
    have hqAbs (j : Fin d) : Tendsto (fun n => ∫ x, |q n x * ℓ x j| ∂P0)
        atTop (nhds 0) := by
      have hellj := hℓMem.eval_piLp j
      have hupp : Tendsto (fun n => Real.sqrt (∫ x, q n x ^ 2 ∂P0) *
          Real.sqrt (∫ x, (ℓ x j) ^ 2 ∂P0)) atTop (nhds 0) := by
        simpa only [Real.sqrt_zero, zero_mul] using
          hq2.sqrt.mul_const (Real.sqrt (∫ x, (ℓ x j) ^ 2 ∂P0))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupp
        (Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _) ?_
      filter_upwards [hqMem] with n hn
      have hcs := integral_mul_norm_le_Lp_mul_Lq (μ := P0) (p := (2 : ℝ)) (q := (2 : ℝ))
        (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩) (by norm_num; exact hn)
        (by norm_num; exact hellj)
      simpa only [Real.norm_eq_abs, ← abs_mul, sq_abs, Real.rpow_two,
        one_div, Real.sqrt_eq_rpow] using hcs
    have hqGood (j : Fin d) : Tendsto (fun n => ∫ x in G n, q n x * ℓ x j ∂P0)
        atTop (nhds 0) := by
      apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hqAbs j)
        (Eventually.of_forall fun _ => abs_nonneg _) ?_
      filter_upwards [hqMem] with n hn
      exact (abs_integral_le_integral_abs).trans
        (setIntegral_le_integral ((hn.integrable_mul (hℓMem.eval_piLp j)).norm)
          (Eventually.of_forall fun _ => abs_nonneg _))
    have hinnerBad (j : Fin d) : Tendsto
        (fun n => ∫ x in (G n)ᶜ, inner ℝ (u n) (ℓ x) * ℓ x j ∂P0)
        atTop (nhds 0) := by
      apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
      have hupp := hscoreTail.const_mul (max Cu 0)
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa only [mul_zero] using hupp) (Eventually.of_forall fun _ => abs_nonneg _) ?_
      filter_upwards [huBound] with n hn
      calc
        |∫ x in (G n)ᶜ, inner ℝ (u n) (ℓ x) * ℓ x j ∂P0| ≤
            ∫ x in (G n)ᶜ, |inner ℝ (u n) (ℓ x) * ℓ x j| ∂P0 :=
          abs_integral_le_integral_abs
        _ ≤ ∫ x in (G n)ᶜ, max Cu 0 * ‖ℓ x‖ ^ 2 ∂P0 := by
          apply setIntegral_mono_on
          · exact ((hℓMem.continuousLinearMap_comp (innerSL ℝ (u n))).integrable_mul
              (hℓMem.eval_piLp j)).norm.integrableOn
          · exact (((memLp_two_iff_integrable_sq_norm hℓMem.aestronglyMeasurable).mp
              hℓMem).const_mul _).integrableOn
          · exact (hG n).compl
          · intro x _
            calc
              |inner ℝ (u n) (ℓ x) * ℓ x j| ≤ ‖u n‖ * ‖ℓ x‖ ^ 2 := by
                rw [abs_mul, pow_two]
                calc
                  |inner ℝ (u n) (ℓ x)| * |ℓ x j| ≤
                      (‖u n‖ * ‖ℓ x‖) * |ℓ x j| :=
                    mul_le_mul_of_nonneg_right (abs_real_inner_le_norm _ _) (abs_nonneg _)
                  _ ≤ (‖u n‖ * ‖ℓ x‖) * ‖ℓ x‖ :=
                    mul_le_mul_of_nonneg_left (by
                      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (ℓ x) j)
                      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
                  _ = ‖u n‖ * (‖ℓ x‖ * ‖ℓ x‖) := by ring
              _ ≤ max Cu 0 * ‖ℓ x‖ ^ 2 := mul_le_mul_of_nonneg_right hn (sq_nonneg _)
        _ = max Cu 0 * ∫ x in (G n)ᶜ, ‖ℓ x‖ ^ 2 ∂P0 := by
          rw [integral_const_mul]
    have hquad (j : Fin d) : Tendsto
        (fun n => ∫ x in G n, V n x * W n x * ℓ x j ∂P0) atTop (nhds 0) := by
      apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
      have hupp := (hqAbs j).add (hgoodWscore.const_mul (max Cu 0))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa only [zero_add, mul_zero] using hupp)
        (Eventually.of_forall fun _ => abs_nonneg _) ?_
      filter_upwards [huBound, hqMem] with n hn hqm
      calc
        |∫ x in G n, V n x * W n x * ℓ x j ∂P0| ≤
            ∫ x in G n, |V n x * W n x * ℓ x j| ∂P0 := abs_integral_le_integral_abs
        _ ≤ ∫ x, |q n x * ℓ x j| ∂P0 +
            max Cu 0 * ∫ x in G n, |W n x| * ‖ℓ x‖ ^ 2 ∂P0 := by
          rw [← integral_const_mul]
          let B := fun x => |q n x * ℓ x j| + max Cu 0 * (|W n x| * ‖ℓ x‖ ^ 2)
          have hWgood : IntegrableOn (fun x => |W n x| * ‖ℓ x‖ ^ 2) (G n) P0 := by
            refine Integrable.mono'
              (((memLp_two_iff_integrable_sq_norm hℓMem.aestronglyMeasurable).mp
                hℓMem).integrableOn) ?_ ?_
            · exact ((M.sqrtDensityRatio_measurable θ0 (θn n)).abs.mul
                (hℓ.norm.pow_const 2)).aestronglyMeasurable.restrict
            · exact ae_restrict_of_forall_mem (hG n) fun x hx => by
                simpa only [Real.norm_eq_abs, abs_mul, abs_abs, abs_pow, abs_norm, one_mul] using
                  mul_le_mul_of_nonneg_right hx.2.le (sq_nonneg ‖ℓ x‖)
          have hB : IntegrableOn B (G n) P0 :=
            (hqm.integrable_mul (hℓMem.eval_piLp j)).norm.integrableOn.add
              (hWgood.const_mul _)
          have hdom : ∀ x ∈ G n, |V n x * W n x * ℓ x j| ≤ B x := by
            intro x hx
            have hv : V n x = q n x + inner ℝ (u n) (ℓ x) := by simp [q]
            have hj : |ℓ x j| ≤ ‖ℓ x‖ := by
              simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (ℓ x) j
            have hi := abs_real_inner_le_norm (u n) (ℓ x)
            have hw : |W n x| ≤ 1 := hx.2.le
            have hiC : |inner ℝ (u n) (ℓ x)| ≤ max Cu 0 * ‖ℓ x‖ :=
              hi.trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
            have hfirst : |q n x * W n x * ℓ x j| ≤ |q n x * ℓ x j| := by
              rw [abs_mul, abs_mul, abs_mul]
              calc
                |q n x| * |W n x| * |ℓ x j| ≤ |q n x| * 1 * |ℓ x j| :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hw (abs_nonneg _)) (abs_nonneg _)
                _ = |q n x| * |ℓ x j| := by ring
            have hsecond : |inner ℝ (u n) (ℓ x) * W n x * ℓ x j| ≤
                max Cu 0 * (|W n x| * ‖ℓ x‖ ^ 2) := by
              rw [abs_mul, abs_mul]
              calc
                |inner ℝ (u n) (ℓ x)| * |W n x| * |ℓ x j| ≤
                    (max Cu 0 * ‖ℓ x‖) * |W n x| * |ℓ x j| :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hiC (abs_nonneg _)) (abs_nonneg _)
                _ ≤ (max Cu 0 * ‖ℓ x‖) * |W n x| * ‖ℓ x‖ :=
                  mul_le_mul_of_nonneg_left hj
                    (mul_nonneg (mul_nonneg (le_max_right _ _) (norm_nonneg _)) (abs_nonneg _))
                _ = max Cu 0 * (|W n x| * ‖ℓ x‖ ^ 2) := by ring
            calc
              |V n x * W n x * ℓ x j| =
                  |q n x * W n x * ℓ x j +
                    inner ℝ (u n) (ℓ x) * W n x * ℓ x j| := by rw [hv, add_mul, add_mul]
              _ ≤ |q n x * W n x * ℓ x j| +
                    |inner ℝ (u n) (ℓ x) * W n x * ℓ x j| := abs_add_le _ _
              _ ≤ B x := by simpa only [B] using add_le_add hfirst hsecond
          have hleft : IntegrableOn (fun x => |V n x * W n x * ℓ x j|) (G n) P0 := by
            refine Integrable.mono' hB ?_ ?_
            · exact ((((M.sqrtDensityRatio_measurable θ0 (θn n)).const_mul _).mul
                (M.sqrtDensityRatio_measurable θ0 (θn n))).mul
                ((PiLp.continuous_apply 2 _ j).measurable.comp
                  hℓ)).norm.aestronglyMeasurable.restrict
            · exact ae_restrict_of_forall_mem (hG n) fun x hx => by
                simpa only [Real.norm_eq_abs, abs_abs] using hdom x hx
          refine (setIntegral_mono_on hleft hB (hG n) hdom).trans ?_
          have hqInt : IntegrableOn (fun x => |q n x * ℓ x j|) (G n) P0 := by
            simpa only [Real.norm_eq_abs] using!
              (hqm.integrable_mul (hℓMem.eval_piLp j)).norm.integrableOn
          have hCInt : IntegrableOn
              (fun x => max Cu 0 * (|W n x| * ‖ℓ x‖ ^ 2)) (G n) P0 :=
            hWgood.const_mul _
          change (∫ x in G n, |q n x * ℓ x j| +
              max Cu 0 * (|W n x| * ‖ℓ x‖ ^ 2) ∂P0) ≤ _
          calc
            _ = (∫ x in G n, |q n x * ℓ x j| ∂P0) +
                ∫ x in G n, max Cu 0 * (|W n x| * ‖ℓ x‖ ^ 2) ∂P0 := by
              rw [integral_add hqInt hCInt]
            _ ≤ (∫ x, |q n x * ℓ x j| ∂P0) +
                ∫ x in G n, max Cu 0 * (|W n x| * ‖ℓ x‖ ^ 2) ∂P0 :=
              add_le_add (setIntegral_le_integral
                (by simpa only [Real.norm_eq_abs] using!
                  (hqm.integrable_mul (hℓMem.eval_piLp j)).norm)
                (Eventually.of_forall fun _ => abs_nonneg _)) le_rfl
    -- The population Gram action is the integrated score outer product.
    have hgram (n : ℕ) (j : Fin d) : gram (u n) j =
        ∫ x, inner ℝ (u n) (ℓ x) * ℓ x j ∂P0 := by
      rw [show u n = WithLp.toLp 2 (fun k => u n k) by rfl,
        Matrix.toEuclideanCLM_toLp]
      simp only [Matrix.mulVec, dotProduct, populationGram, PiLp.inner_apply]
      simp_rw [Finset.sum_mul]
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro k _
        rw [mul_comm, ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        change u n k * (ℓ x j * ℓ x k) = (ℓ x k * u n k) * ℓ x j
        ring
      · intro k _
        convert ((hℓMem.eval_piLp k).integrable_mul
          (hℓMem.eval_piLp j) |>.const_mul (u n k)) using 1
        funext x
        change (ℓ x k * u n k) * ℓ x j = u n k * (ℓ x k * ℓ x j)
        ring
    -- The weighted residual is square-integrable after division on the common support.
    have hRMem (n : ℕ) : MemLp (R n) 2 (Pn n) := by
      rw [memLp_two_iff_integrable_sq_norm (hRmeas n).aestronglyMeasurable]
      simp only [Pn, modelMeasure]
      rw [integrable_withDensity_iff
        (M.density_meas (θn n)).ennreal_ofReal (by simp)]
      have heInt := (memLp_two_iff_integrable_sq_norm
        (heMem n).aestronglyMeasurable).mp (heMem n) |>.indicator (hG n)
      apply Integrable.congr heInt
      exact Eventually.of_forall fun x => by
        change (G n).indicator (fun x => ‖e n x‖ ^ 2) x =
          ‖R n x‖ ^ 2 * (ENNReal.ofReal (M.density (θn n) x)).toReal
        rw [ENNReal.toReal_ofReal (M.density_nonneg (θn n) x)]
        by_cases hx : x ∈ G n
        · have hp0 := hx.1
          have hpn : 0 < M.density (θn n) x := by
            rw [density_eq_base_mul_sqrtDensityRatio_sq M θ0 (θn n) x hp0]
            have : 0 < 1 + W n x / 2 := by linarith [neg_abs_le (W n x), hx.2]
            positivity
          rw [Set.indicator_of_mem hx]
          simp only [R, Set.indicator_of_mem hx, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (inv_nonneg.mpr (M.sqrtDensity_nonneg _ _)), mul_pow]
          rw [← M.sqrtDensity_sq]
          field_simp [(Real.sqrt_pos.2 hpn).ne']
          exact (mul_div_cancel_left₀ _ (Real.sqrt_pos.2 hpn).ne').symm
        · rw [Set.indicator_of_notMem hx]
          simp [R, hx]
    -- On the good set the ratio correction is integrable under the moving law.
    have hYInt : ∀ᶠ n in atTop, ∀ j : Fin d,
        Integrable (fun x => Y n x j) (Pn n) := by
      filter_upwards [hWMem] with n hwn
      intro j
      have hYmeas : Measurable (Y n) := by
        exact (((measurable_const.mul (M.sqrtDensityRatio_measurable θ0 (θn n))).div
          (measurable_const.add (M.sqrtDensityRatio_measurable θ0 (θn n)))).smul hℓ)
          |>.indicator (hG n)
      simp only [Pn, modelMeasure]
      rw [integrable_withDensity_iff
        (M.density_meas (θn n)).ennreal_ofReal (by simp)]
      have henv : Integrable
          (fun x => Real.sqrt n * |W n x| * |ℓ x j| * M.density θ0 x) μ := by
        have hh := hwn.integrable_mul (hℓMem.eval_piLp j) |>.norm.const_mul (Real.sqrt n)
        simp only [P0, modelMeasure] at hh
        rw [integrable_withDensity_iff
          (M.density_meas θ0).ennreal_ofReal (by simp)] at hh
        convert hh using 1
        funext x
        rw [ENNReal.toReal_ofReal (M.density_nonneg θ0 x)]
        simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
        ring
      apply Integrable.mono' henv
      · exact (((((PiLp.proj (p := 2) (β := fun _ : Fin d => ℝ) j :
          EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)).measurable.comp hYmeas).mul
          (M.density_meas (θn n)).ennreal_ofReal.ennreal_toReal).aestronglyMeasurable)
      · filter_upwards with x
        by_cases hx : x ∈ G n
        · have hden : 0 < 2 + W n x := by linarith [neg_abs_le (W n x), hx.2]
          rw [ENNReal.toReal_ofReal (M.density_nonneg (θn n) x),
            density_eq_base_mul_sqrtDensityRatio_sq M θ0 (θn n) x hx.1]
          simp only [Y, Set.indicator_of_mem hx, PiLp.smul_apply, smul_eq_mul,
            Real.norm_eq_abs, abs_mul, abs_div, abs_neg,
            abs_of_nonneg (Real.sqrt_nonneg n), abs_of_pos hden]
          rw [abs_of_nonneg (M.density_nonneg θ0 x),
            abs_of_nonneg (sq_nonneg (1 + W n x / 2))]
          have hfac : (1 + W n x / 2) ^ 2 / (2 + W n x) ≤ 1 := by
            rw [show (1 + W n x / 2) ^ 2 / (2 + W n x) =
              (2 + W n x) / 4 by field_simp; ring]
            linarith [le_abs_self (W n x), hx.2]
          have henv0 : 0 ≤ Real.sqrt n * |W n x| * |ℓ x j| * M.density θ0 x :=
            mul_nonneg
              (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) (abs_nonneg _))
              (M.density_nonneg _ _)
          calc
            Real.sqrt n * |W n x| / (2 + W n x) * |ℓ x j| *
                (M.density θ0 x * (1 + W n x / 2) ^ 2) =
              ((1 + W n x / 2) ^ 2 / (2 + W n x)) *
                (Real.sqrt n * |W n x| * |ℓ x j| * M.density θ0 x) := by ring
            _ ≤ 1 * (Real.sqrt n * |W n x| * |ℓ x j| * M.density θ0 x) :=
              mul_le_mul_of_nonneg_right hfac henv0
            _ = Real.sqrt n * |W n x| * |ℓ x j| * M.density θ0 x := one_mul _
        · simp only [Y, Set.indicator_of_notMem hx, PiLp.zero_apply, zero_mul,
            Real.norm_eq_abs, abs_zero]
          exact mul_nonneg
            (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)) (abs_nonneg _))
            (M.density_nonneg _ _)
    -- The score restricted to the common support is integrable under the moving law.
    have hℓGoodInt (n : ℕ) (j : Fin d) : IntegrableOn (fun x => ℓ x j) (G n) (Pn n) := by
      rw [← integrable_indicator_iff (hG n)]
      simp only [Pn, modelMeasure]
      rw [integrable_withDensity_iff
        (M.density_meas (θn n)).ennreal_ofReal (by simp)]
      have hbase := (hℓMem.eval_piLp j).integrable one_le_two
      simp only [modelMeasure] at hbase
      rw [integrable_withDensity_iff
        (M.density_meas θ0).ennreal_ofReal (by simp)] at hbase
      apply Integrable.mono' (hbase.norm.const_mul (9 / 4 : ℝ))
      · exact ((((PiLp.continuous_apply 2 _ j).measurable.comp hℓ).indicator
          (hG n)).mul
          (M.density_meas (θn n)).ennreal_ofReal.ennreal_toReal).aestronglyMeasurable
      · filter_upwards with x
        by_cases hx : x ∈ G n
        · rw [ENNReal.toReal_ofReal (M.density_nonneg _ _),
            density_eq_base_mul_sqrtDensityRatio_sq M θ0 (θn n) x hx.1,
            ENNReal.toReal_ofReal (M.density_nonneg _ _)]
          simp only [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (M.density_nonneg _ _), abs_pow]
          have hpos : 0 < 1 + W n x / 2 := by
            linarith [neg_abs_le (W n x), hx.2]
          change |ℓ x j| * (M.density θ0 x * |1 + W n x / 2| ^ 2) ≤
            9 / 4 * (|ℓ x j| * M.density θ0 x)
          rw [abs_of_pos hpos]
          have : (1 + W n x / 2) ^ 2 ≤ 9 / 4 := by
            nlinarith [neg_abs_le (W n x), le_abs_self (W n x), hx.2]
          calc
            |ℓ x j| * (M.density θ0 x * (1 + W n x / 2) ^ 2) ≤
                |ℓ x j| * (M.density θ0 x * (9 / 4)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left this (M.density_nonneg _ _)) (abs_nonneg _)
            _ = 9 / 4 * (|ℓ x j| * M.density θ0 x) := by ring
        · simp only [Set.indicator_of_notMem hx, zero_mul, norm_zero]
          positivity
    -- The good-support density square gives the exact population shift.
    have hshift (n : ℕ) (j : Fin d) (hqm : MemLp (q n) 2 P0) : Real.sqrt n *
        (∫ x in G n, ℓ x j ∂(Pn n)) =
        Real.sqrt n * (∫ x in G n, ℓ x j ∂P0) +
          ∫ x in G n, V n x * ℓ x j ∂P0 +
          (1 / 4 : ℝ) * ∫ x in G n, V n x * W n x * ℓ x j ∂P0 := by
      have hVmem : MemLp (V n) 2 P0 := by
        have hi := hℓMem.continuousLinearMap_comp (innerSL ℝ (u n))
        convert hqm.add hi using 1
        funext x
        change V n x = (V n x - inner ℝ (u n) (ℓ x)) + inner ℝ (u n) (ℓ x)
        ring
      have hVj := hVmem.integrable_mul (hℓMem.eval_piLp j)
      have hVj' : Integrable (fun x => V n x * ℓ x j) P0 := by
        simpa only [Pi.mul_apply] using! hVj
      have hscaled : Integrable (fun x => Real.sqrt n * ℓ x j) P0 :=
        ((hℓMem.eval_piLp j).integrable one_le_two).const_mul _
      have hVWj : IntegrableOn (fun x => V n x * W n x * ℓ x j) (G n) P0 := by
        refine Integrable.mono' hVj.norm.integrableOn ?_ ?_
        · exact ((((M.sqrtDensityRatio_measurable θ0 (θn n)).const_mul _).mul
            (M.sqrtDensityRatio_measurable θ0 (θn n))).mul
            ((PiLp.continuous_apply 2 _ j).measurable.comp hℓ)).aestronglyMeasurable.restrict
        · exact ae_restrict_of_forall_mem (hG n) fun x hx => by
            simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
            calc
              |V n x| * |W n x| * |ℓ x j| =
                  |W n x| * (|V n x| * |ℓ x j|) := by ring
              _ ≤ 1 * (|V n x| * |ℓ x j|) :=
                mul_le_mul_of_nonneg_right hx.2.le
                  (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              _ = |V n x| * |ℓ x j| := one_mul _
      rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
        ← integral_add hscaled.integrableOn hVj'.integrableOn]
      change _ =
        (∫ x in G n, ((fun y => Real.sqrt n * ℓ y j) +
          fun y => V n y * ℓ y j) x ∂P0) +
        ∫ x in G n, (1 / 4 : ℝ) * (V n x * W n x * ℓ x j) ∂P0
      rw [← integral_add (hscaled.integrableOn.add hVj'.integrableOn)
        (hVWj.const_mul _)]
      simp only [Pn, P0, modelMeasure]
      rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
          (M.density_meas (θn n)).ennreal_ofReal (by simp) _ (hG n),
        setIntegral_withDensity_eq_setIntegral_toReal_smul
          (M.density_meas θ0).ennreal_ofReal (by simp) _ (hG n)]
      simp_rw [ENNReal.toReal_ofReal (M.density_nonneg _ _)]
      apply integral_congr_ae
      exact ae_restrict_of_forall_mem (hG n) fun x hx => by
        simp only [Pi.add_apply, smul_eq_mul]
        rw [density_eq_base_mul_sqrtDensityRatio_sq M θ0 (θn n) x hx.1]
        simp only [V, W]
        ring
    -- Center first, then split support: this is the cancellation-preserving identity.
    have hDid : ∀ᶠ n in atTop, ∀ j : Fin d, D n j =
        -(Real.sqrt n * ∫ x in (G n)ᶜ, fn n x j ∂(Pn n)) +
          Real.sqrt n * ∫ x in (G n)ᶜ, ℓ x j ∂P0 -
          ∫ x in G n, q n x * ℓ x j ∂P0 +
          ∫ x in (G n)ᶜ, inner ℝ (u n) (ℓ x) * ℓ x j ∂P0 -
          (1 / 4 : ℝ) * ∫ x in G n, V n x * W n x * ℓ x j ∂P0 := by
      filter_upwards [hYInt, hqMem, eventually_ge_atTop 1] with n hy hqm hn
      intro j
      have hsqrt : Real.sqrt n ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
      have hRj := (hRMem n).eval_piLp j |>.integrable one_le_two
      have hfnj := (hfn_memLp n).eval_piLp j |>.integrable one_le_two
      have hℓj := (hℓMem.eval_piLp j).integrable one_le_two
      have hgoodEq : Real.sqrt n * (∫ x, R n x j ∂(Pn n)) +
          ∫ x, Y n x j ∂(Pn n) =
          Real.sqrt n * ∫ x in G n, (fn n x j - ℓ x j) ∂(Pn n) := by
        rw [← integral_const_mul, ← integral_add (hRj.const_mul _) (hy j),
          ← integral_indicator (hG n), ← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        by_cases hx : x ∈ G n
        · rw [Set.indicator_of_mem hx]
          have hden : 2 + W n x ≠ 0 := by
            have : 0 < 2 + W n x := by linarith [neg_abs_le (W n x), hx.2]
            exact this.ne'
          have hs : M.sqrtDensity (θn n) x =
              M.sqrtDensity θ0 x * (1 + W n x / 2) := by
            change Real.sqrt (M.density (θn n) x) = _
            rw [density_eq_base_mul_sqrtDensityRatio_sq M θ0 (θn n) x hx.1,
              Real.sqrt_mul (M.density_nonneg θ0 x), Real.sqrt_sq_eq_abs,
              abs_of_pos (by linarith [neg_abs_le (W n x), hx.2])]
            simp only [W, ParametricFamily.sqrtDensity]
          simp only [R, Y, Set.indicator_of_mem hx, PiLp.smul_apply,
            PiLp.sub_apply, smul_eq_mul]
          rw [hs]
          have hfac : 1 + W n x / 2 ≠ 0 :=
            (by linarith [neg_abs_le (W n x), hx.2] : 0 < 1 + W n x / 2).ne'
          have hbase : M.sqrtDensity θ0 x ≠ 0 := by
            change Real.sqrt (M.density θ0 x) ≠ 0
            exact (Real.sqrt_pos.2 hx.1).ne'
          field_simp [hden, hsqrt, hbase, hfac]
          ring
        · simp [R, Y, hx]
      simp only [D, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      rw [MeasureTheory.eval_integral_piLp
          (fun k => ((hRMem n).eval_piLp k).integrable one_le_two) j,
        MeasureTheory.eval_integral_piLp hy j]
      change Real.sqrt n * (∫ x, R n x j ∂(Pn n)) +
        ∫ x, Y n x j ∂(Pn n) + gram (u n) j = _
      rw [hgoodEq, hgram n j]
      have hcenter := congrArg (fun z : EuclideanSpace ℝ (Fin d) => z j) (hfn_centered n)
      change (∫ x, fn n x ∂(Pn n)) j = (0 : EuclideanSpace ℝ (Fin d)) j at hcenter
      rw [MeasureTheory.eval_integral_piLp
        (fun k => ((hfn_memLp n).eval_piLp k).integrable one_le_two) j] at hcenter
      simp only [PiLp.zero_apply] at hcenter
      rw [← integral_add_compl (hG n) hfnj] at hcenter
      have hcenter' : ∫ x in G n, fn n x j ∂(Pn n) =
          -∫ x in (G n)ᶜ, fn n x j ∂(Pn n) := by
        linarith [hcenter]
      have hscore := congrArg (fun z : EuclideanSpace ℝ (Fin d) => z j)
        (dqm_score_integral_modelMeasure_eq_zero M μ θ0 ℓ hℓ hPDF hDQM)
      change (∫ x, ℓ x ∂P0) j = (0 : EuclideanSpace ℝ (Fin d)) j at hscore
      rw [MeasureTheory.eval_integral_piLp
        (fun k => ((hℓMem.eval_piLp k).integrable one_le_two)) j] at hscore
      simp only [PiLp.zero_apply] at hscore
      rw [← integral_add_compl (hG n) hℓj] at hscore
      have hscore' : ∫ x in G n, ℓ x j ∂P0 =
          -∫ x in (G n)ᶜ, ℓ x j ∂P0 := by
        linarith [hscore]
      rw [integral_sub hfnj.integrableOn (hℓGoodInt n j), hcenter']
      have hsplit : Real.sqrt n *
          (-∫ x in (G n)ᶜ, fn n x j ∂(Pn n) - ∫ x in G n, ℓ x j ∂(Pn n)) =
          -(Real.sqrt n * ∫ x in (G n)ᶜ, fn n x j ∂(Pn n)) -
            Real.sqrt n * ∫ x in G n, ℓ x j ∂(Pn n) := by
        ring
      rw [hsplit, hshift n j hqm, hscore']
      simp only [q]
      have hinnerj := (hℓMem.continuousLinearMap_comp (innerSL ℝ (u n))).integrable_mul
        (hℓMem.eval_piLp j)
      have hinnerj' : Integrable
          (fun x => inner ℝ (u n) (ℓ x) * ℓ x j) P0 := by
        simpa only [Pi.mul_apply] using! hinnerj
      have hVmem' : MemLp (V n) 2 P0 := by
        convert hqm.add (hℓMem.continuousLinearMap_comp (innerSL ℝ (u n))) using 1
        funext x
        change V n x = (V n x - inner ℝ (u n) (ℓ x)) + inner ℝ (u n) (ℓ x)
        ring
      have hVell := hVmem'.integrable_mul (hℓMem.eval_piLp j)
      have hqsplit : ∫ x in G n,
          (V n x - inner ℝ (u n) (ℓ x)) * ℓ x j ∂P0 =
          (∫ x in G n, V n x * ℓ x j ∂P0) -
            ∫ x in G n, inner ℝ (u n) (ℓ x) * ℓ x j ∂P0 := by
        have hi := integral_sub (μ := P0.restrict (G n))
          hVell.integrableOn hinnerj.integrableOn
        convert! hi using 1; apply integral_congr_ae;
          exact ae_restrict_of_forall_mem (hG n) fun x _ => by
            simp only [Pi.mul_apply, innerSL_apply_apply]
            ring
      rw [hqsplit, ← integral_add_compl (hG n) hinnerj']
      ring
    apply tendsto_euclidean_zero_of_coordinate D
    intro j
    have hz := (((hbadFn j).neg.add (hbadℓ j)).sub (hqGood j)).add
      (hinnerBad j) |>.sub ((hquad j).const_mul (1 / 4 : ℝ))
    have hz' : Tendsto (fun (n : ℕ) =>
        -(Real.sqrt n * ∫ x in (G n)ᶜ, fn n x j ∂(Pn n)) +
          Real.sqrt n * ∫ x in (G n)ᶜ, ℓ x j ∂P0 -
          ∫ x in G n, q n x * ℓ x j ∂P0 +
          ∫ x in (G n)ᶜ, inner ℝ (u n) (ℓ x) * ℓ x j ∂P0 -
          (1 / 4 : ℝ) * ∫ x in G n, V n x * W n x * ℓ x j ∂P0)
        atTop (nhds 0) := by
      simpa only [smul_eq_mul, neg_zero, zero_add, zero_sub, mul_zero, sub_zero] using hz
    exact hz'.congr' (hDid.mono fun n hn => (hn j).symm)
  have hH : TendstoInProbZero
      (fun n => Measure.pi (fun _ : Fin n => Pn n)) H := by
    exact TendstoInProbZero.add (TendstoInProbZero.add hRcenter hratio)
      (tendstoInProbZero_const
        (fun n => Measure.pi (fun _ : Fin n => Pn n)) D hD)
  have hagrees (n : ℕ) (X : Fin n → Omega)
      (hX : ∀ i, X i ∉ (G n)ᶜ) : Z n X = H n X := by
    have hpoint (i : Fin n) : Real.sqrt n • (fn n (X i) - ℓ (X i)) =
        Real.sqrt n • R n (X i) + Y n (X i) := by
      have hi : X i ∈ G n := by simpa only [Set.mem_compl_iff, not_not] using hX i
      have hw : |W n (X i)| < 1 := hi.2
      have hden : 2 + W n (X i) ≠ 0 := by
        have : 0 < 2 + W n (X i) := by linarith [neg_abs_le (W n (X i))]
        exact this.ne'
      have hhalf : 0 < 1 + W n (X i) / 2 := by
        linarith [neg_abs_le (W n (X i))]
      have hsqrt : M.sqrtDensity (θn n) (X i) =
          M.sqrtDensity θ0 (X i) * (1 + W n (X i) / 2) := by
        change Real.sqrt (M.density (θn n) (X i)) =
          Real.sqrt (M.density θ0 (X i)) * (1 + W n (X i) / 2)
        rw [density_eq_base_mul_sqrtDensityRatio_sq M θ0 (θn n) (X i) hi.1,
          Real.sqrt_mul (M.density_nonneg θ0 (X i)), Real.sqrt_sq_eq_abs,
          abs_of_pos hhalf]
      have hsqrtn_ne : M.sqrtDensity (θn n) (X i) ≠ 0 := by
        rw [hsqrt]
        exact mul_ne_zero (Real.sqrt_pos.2 hi.1).ne' hhalf.ne'
      apply PiLp.ext
      intro j
      simp only [R, Y, Set.indicator_of_mem hi, PiLp.smul_apply,
        PiLp.sub_apply, PiLp.add_apply, smul_eq_mul]
      field_simp [hden, hsqrtn_ne]
      rw [hsqrt]
      ring
    have hsum : Real.sqrt n • (∑ i, fn n (X i) - ∑ i, ℓ (X i)) =
        Real.sqrt n • ∑ i, R n (X i) + ∑ i, Y n (X i) := by
      rw [← Finset.sum_sub_distrib]
      calc
        Real.sqrt n • ∑ i, (fn n (X i) - ℓ (X i)) =
            ∑ i, Real.sqrt n • (fn n (X i) - ℓ (X i)) := by
          exact (map_sum (DistribSMul.toAddMonoidHom
            (EuclideanSpace ℝ (Fin d)) (Real.sqrt n))
              (fun i => fn n (X i) - ℓ (X i)) Finset.univ)
        _ = ∑ i, (Real.sqrt n • R n (X i) + Y n (X i)) :=
          Finset.sum_congr rfl (fun i _ => hpoint i)
        _ = _ := by rw [Finset.sum_add_distrib, Finset.smul_sum]
    simp only [Z, H, D, empMean]
    have hscaled : Real.sqrt n • ((n : ℝ)⁻¹ • ∑ i, fn n (X i) -
          (n : ℝ)⁻¹ • ∑ i, ℓ (X i)) =
        (n : ℝ)⁻¹ • (Real.sqrt n • ∑ i, R n (X i) + ∑ i, Y n (X i)) := by
      rw [← smul_sub, ← smul_assoc]
      change (Real.sqrt n * (n : ℝ)⁻¹) •
          (∑ i, fn n (X i) - ∑ i, ℓ (X i)) = _
      rw [mul_comm]
      rw [mul_smul]
      exact congrArg ((n : ℝ)⁻¹ • ·) hsum
    rw [hscaled]
    module
  change TendstoInProbZero (fun n => Measure.pi (fun _ : Fin n => Pn n)) Z
  exact tendstoInProbZero_of_agrees_off_product_bad Pn (fun n => (G n)ᶜ)
    (fun n => (hG n).compl) hbad Z H hagrees hH

end AsymptoticStatistics.Asymptotics.Discharge.OneStepVec
