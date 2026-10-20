module
public import StatLean.AsymptoticStatistics.Consistency.UniformConsistency
public import StatLean.AsymptoticStatistics.ForMathlib.InProbability
public import StatLean.AsymptoticStatistics.ForMathlib.WellSeparatedMaximum
public import StatLean.AsymptoticStatistics.MaximumLikelihood.Likelihood
public import StatLean.AsymptoticStatistics.ParametricFamily.KullbackLeibler

@[expose] public section

/-!
# Maximum-likelihood consistency from KL identifiability

This file combines vdV Lemma 5.35 with Theorem 5.7.  Following the technically
advantageous route on book p.63, the real-valued criterion is the stabilized
mixture log-likelihood

`log ((p_theta + p_theta0) / (2 * p_theta0))`.

The KL lemma derives strict uniqueness, the compact-superlevel adapter derives
the strong separation required by Theorem 5.7, and `mEstimator_consistent`
performs the stochastic assembly.  No consistency or separation conclusion is
accepted as a hypothesis.
-/

open MeasureTheory Filter Topology Set
open AsymptoticStatistics.EmpiricalProcess
open scoped ENNReal

namespace AsymptoticStatistics.MaximumLikelihood

/-- The measure represented by a member of a density family.

Edge behavior: `ENNReal.ofReal` sends negative density values to zero.  In this
repository `ParametricFamily.density_nonneg` rules that case out, so the fallback
does not change the represented model. -/
noncomputable def parametricMeasure
    {X : Type*} [MeasurableSpace X] {Theta : Type*}
    (M : ParametricFamily X Theta) (mu : Measure X) (theta : Theta) : Measure X :=
  mu.withDensity (fun x => ENNReal.ofReal (M.density theta x))

/-- The stabilized log-likelihood criterion from vdV p.63,
`m_theta = log ((p_theta + p_theta0) / (2 p_theta0))`.

Edge behavior: where `p_theta0 = 0`, Lean's division gives zero and `Real.log 0 = 0`.
That set has zero mass under the true density, so the population criterion below
is unchanged.  On the true support the ratio is at least `1/2`, which is the
technical advantage of the stabilized route. -/
noncomputable def stabilizedLogCriterion
    {X : Type*} [MeasurableSpace X] {Theta : Type*}
    (M : ParametricFamily X Theta) (theta0 theta : Theta) (x : X) : Real :=
  Real.log ((M.density theta x + M.density theta0 x) /
    (2 * M.density theta0 x))

/-- The population expectation under the truth of vdV's stabilized criterion.

Edge behavior follows `stabilizedLogCriterion`: values on the zero set of the
true density are multiplied by zero and hence do not affect the integral. -/
noncomputable def stabilizedPopulationCriterion
    {X : Type*} [MeasurableSpace X] {Theta : Type*}
    (M : ParametricFamily X Theta) (mu : Measure X) (theta0 theta : Theta) : Real :=
  ∫ x, stabilizedLogCriterion M theta0 theta x * M.density theta0 x ∂mu

/-- The subprobability measure with mixture density `(p_theta + p_theta0) / 2`
used by the p.63 stabilized likelihood argument.

Edge behavior: `ENNReal.ofReal` truncates negative inputs, but both component
densities are nonnegative by `ParametricFamily`, so no truncation occurs. -/
noncomputable def stabilizedParametricMeasure
    {X : Type*} [MeasurableSpace X] {Theta : Type*}
    (M : ParametricFamily X Theta) (mu : Measure X) (theta0 theta : Theta) : Measure X :=
  mu.withDensity (fun x => ENNReal.ofReal
    ((M.density theta x + M.density theta0 x) / 2))

/-- Density-to-measure bridge for the stabilized p.63 criterion.

The real population integral equals the extended-real KL objective of the
mixture family.  This named theorem is the place where the zero-density set,
finite mass, and Mathlib's finite-measure KL correction are reconciled; callers
do not provide the equality as a hypothesis. -/
theorem stabilized_populationCriterion_eq_klObjective
    {X : Type*} [MeasurableSpace X] {Theta : Type*}
    (M : ParametricFamily X Theta) (mu : Measure X) (theta0 : Theta)
    (hsub_int : forall theta, Integrable (M.density theta) mu)
    (hsub_mass : forall theta, (∫ x, M.density theta x ∂mu) <= 1)
    (htrue_mass : (∫ x, M.density theta0 x ∂mu) = 1) :
    forall theta,
      (stabilizedPopulationCriterion M mu theta0 theta : EReal) =
        -ParametricFamily.subprobKLDivergence
          (stabilizedParametricMeasure M mu theta0) theta0 theta := by
  intro theta
  let f0 : X → ENNReal := fun x => ENNReal.ofReal
    ((M.density theta0 x + M.density theta0 x) / 2)
  let fq : X → ENNReal := fun x => ENNReal.ofReal
    ((M.density theta x + M.density theta0 x) / 2)
  let P0 : Measure X := mu.withDensity f0
  let Q : Measure X := mu.withDensity fq
  let r : X → ENNReal := fun x => f0 x / fq x
  have hf0_meas : Measurable f0 := by
    dsimp [f0]
    exact (((M.density_meas theta0).add (M.density_meas theta0)).div_const 2).ennreal_ofReal
  have hfq_meas : Measurable fq := by
    dsimp [fq]
    exact (((M.density_meas theta).add (M.density_meas theta0)).div_const 2).ennreal_ofReal
  have hr_meas : Measurable r := hf0_meas.div hfq_meas
  have hf0_real (x : X) : (f0 x).toReal = M.density theta0 x := by
    dsimp [f0]
    rw [ENNReal.toReal_ofReal (div_nonneg
      (add_nonneg (M.density_nonneg theta0 x) (M.density_nonneg theta0 x)) (by norm_num))]
    ring
  have hfq_real (x : X) : (fq x).toReal =
      (M.density theta x + M.density theta0 x) / 2 := by
    dsimp [fq]
    rw [ENNReal.toReal_ofReal (div_nonneg
      (add_nonneg (M.density_nonneg theta x) (M.density_nonneg theta0 x)) (by norm_num))]
  have hf0_ne_top (x : X) : f0 x ≠ ∞ := by
    dsimp [f0]
    exact ENNReal.ofReal_ne_top
  have hfq_ne_top (x : X) : fq x ≠ ∞ := by
    dsimp [fq]
    exact ENNReal.ofReal_ne_top
  have hf0_int : Integrable (fun x =>
      (M.density theta0 x + M.density theta0 x) / 2) mu := by
    fun_prop
  have hfq_int : Integrable (fun x =>
      (M.density theta x + M.density theta0 x) / 2) mu := by
    fun_prop
  letI : IsFiniteMeasure P0 := isFiniteMeasure_withDensity (by
    rw [← ofReal_integral_eq_lintegral_ofReal hf0_int]
    · exact ENNReal.ofReal_ne_top
    · filter_upwards with x
      exact div_nonneg
        (add_nonneg (M.density_nonneg theta0 x) (M.density_nonneg theta0 x)) (by norm_num))
  letI : IsFiniteMeasure Q := isFiniteMeasure_withDensity (by
    rw [← ofReal_integral_eq_lintegral_ofReal hfq_int]
    · exact ENNReal.ofReal_ne_top
    · filter_upwards with x
      exact div_nonneg
        (add_nonneg (M.density_nonneg theta x) (M.density_nonneg theta0 x)) (by norm_num))
  have hf0_le (x : X) : f0 x ≤ 2 * fq x := by
    dsimp [f0, fq]
    rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : Real) < 2),
      ENNReal.ofReal_div_of_pos (by positivity : (0 : Real) < 2)]
    rw [ENNReal.ofReal_add (M.density_nonneg theta0 x) (M.density_nonneg theta0 x),
      ENNReal.ofReal_add (M.density_nonneg theta x) (M.density_nonneg theta0 x)]
    simp only [ENNReal.ofReal_ofNat]
    have h : ENNReal.ofReal (M.density theta0 x) ≤
        ENNReal.ofReal (M.density theta x) + ENNReal.ofReal (M.density theta0 x) :=
      le_add_left le_rfl
    rw [two_mul]
    calc
      _ ≤ ((ENNReal.ofReal (M.density theta x) + ENNReal.ofReal (M.density theta0 x)) +
          (ENNReal.ofReal (M.density theta x) + ENNReal.ofReal (M.density theta0 x))) / 2 :=
        ENNReal.div_le_div_right (add_le_add h h) 2
      _ = _ := by simp only [div_eq_mul_inv, add_mul]
  have hr_le (x : X) : r x ≤ 2 := by
    exact ENNReal.div_le_of_le_mul (by simpa [mul_comm] using hf0_le x)
  have hmul (x : X) : fq x * r x = f0 x := by
    by_cases hq : fq x = 0
    · have h0 : f0 x = 0 := by
        apply nonpos_iff_eq_zero.mp
        simpa [hq] using hf0_le x
      simp [hq, h0]
    · exact ENNReal.mul_div_cancel hq (hfq_ne_top x)
  have hP0_eq : P0 = Q.withDensity r := by
    dsimp [P0, Q]
    rw [← withDensity_mul mu hfq_meas hr_meas]
    exact withDensity_congr_ae (ae_of_all mu fun x => by
      simpa only [Pi.mul_apply] using (hmul x).symm)
  have h_ac : P0 ≪ Q := by
    rw [hP0_eq]
    exact withDensity_absolutelyContinuous Q r
  have hrn : P0.rnDeriv Q =ᵐ[Q] r := by
    rw [hP0_eq]
    exact Measure.rnDeriv_withDensity Q hr_meas
  have hrn_le : P0.rnDeriv Q ≤ᵐ[Q] fun _ => (2 : ENNReal) :=
    hrn.mono fun x hx => hx.le.trans (hr_le x)
  have hkl_bound : ∀ᵐ x ∂Q,
      ‖InformationTheory.klFun (P0.rnDeriv Q x).toReal‖ ≤ (1 : Real) := by
    filter_upwards [hrn_le, Measure.rnDeriv_lt_top P0 Q] with x hx hx_top
    let y := (P0.rnDeriv Q x).toReal
    have hy0 : 0 ≤ y := ENNReal.toReal_nonneg
    have hy2 : y ≤ 2 := by
      simpa [y] using (ENNReal.toReal_le_toReal hx_top.ne (by simp)).2 hx
    rw [Real.norm_eq_abs, abs_of_nonneg (InformationTheory.klFun_nonneg hy0)]
    by_cases hy : y = 0
    · simp [hy, InformationTheory.klFun_zero]
    · have hlog := Real.log_le_sub_one_of_pos (lt_of_le_of_ne hy0 (Ne.symm hy))
      rw [InformationTheory.klFun_apply]
      nlinarith [mul_le_mul_of_nonneg_left hlog hy0,
        sq_nonneg (y - 1), mul_nonneg hy0 (sub_nonneg.mpr hy2)]
  have hkl_int : Integrable
      (fun x => InformationTheory.klFun (P0.rnDeriv Q x).toReal) Q :=
    (integrable_const (1 : Real)).mono
      ((InformationTheory.measurable_klFun.comp
        (Measure.measurable_rnDeriv P0 Q).ennreal_toReal).aestronglyMeasurable)
      (by simpa only [norm_one] using hkl_bound)
  have hllr_int : Integrable (llr P0 Q) P0 :=
    (InformationTheory.integrable_klFun_rnDeriv_iff h_ac).mp hkl_int
  have hP0_mass : P0 univ = 1 := by
    dsimp [P0]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hf0_int]
    · rw [show (∫ x, (M.density theta0 x + M.density theta0 x) / 2 ∂mu) = 1 by
        rw [integral_div, integral_add (hsub_int theta0) (hsub_int theta0), htrue_mass]
        norm_num]
      simp
    · filter_upwards with x
      exact div_nonneg
        (add_nonneg (M.density_nonneg theta0 x) (M.density_nonneg theta0 x)) (by norm_num)
  have hq_integral : (∫ x, (M.density theta x + M.density theta0 x) / 2 ∂mu) ≤ 1 := by
    rw [integral_div, integral_add (hsub_int theta) (hsub_int theta0), htrue_mass]
    linarith [hsub_mass theta]
  have hQ_mass : Q univ ≤ 1 := by
    dsimp [Q]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hfq_int]
    · simpa using ENNReal.ofReal_le_ofReal hq_integral
    · filter_upwards with x
      exact div_nonneg
        (add_nonneg (M.density_nonneg theta x) (M.density_nonneg theta0 x)) (by norm_num)
  have hQ_le_P0 : Q univ ≤ P0 univ := by simpa [hP0_mass] using hQ_mass
  have hcrit : stabilizedPopulationCriterion M mu theta0 theta =
      -(∫ x, llr P0 Q x ∂P0) := by
    have hp0_ne : ∀ᵐ x ∂P0, f0 x ≠ 0 :=
      (ae_withDensity_iff hf0_meas).2 (ae_of_all mu fun _ hx => hx)
    have hstable : stabilizedLogCriterion M theta0 theta =ᵐ[P0]
        fun x => -llr P0 Q x := by
      filter_upwards [h_ac.ae_le hrn, hp0_ne] with x hxrn hx0
      have hp0 : 0 < M.density theta0 x := by
        have hpos : 0 < (f0 x).toReal := ENNReal.toReal_pos hx0 (hf0_ne_top x)
        simpa only [hf0_real] using hpos
      have hq : 0 < (M.density theta x + M.density theta0 x) / 2 :=
        div_pos (add_pos_of_nonneg_of_pos (M.density_nonneg theta x) hp0) (by norm_num)
      have hratio : (M.density theta x + M.density theta0 x) /
          (2 * M.density theta0 x) =
          ((M.density theta x + M.density theta0 x) / 2) /
            M.density theta0 x := by ring
      simp only [stabilizedLogCriterion, llr, hxrn, r, ENNReal.toReal_div,
        hf0_real, hfq_real, hratio]
      rw [Real.log_div hq.ne' hp0.ne', Real.log_div hp0.ne' hq.ne']
      ring
    calc
      stabilizedPopulationCriterion M mu theta0 theta =
          (∫ x, stabilizedLogCriterion M theta0 theta x ∂P0) := by
        dsimp [stabilizedPopulationCriterion, P0]
        rw [integral_withDensity_eq_integral_toReal_smul hf0_meas
          (ae_of_all mu fun x => (hf0_ne_top x).lt_top)]
        simp_rw [hf0_real, smul_eq_mul, mul_comm]
      _ = ∫ x, -llr P0 Q x ∂P0 := integral_congr_ae hstable
      _ = -(∫ x, llr P0 Q x ∂P0) := integral_neg (llr P0 Q)
  let D : ENNReal := InformationTheory.klDiv P0 Q + (P0 univ - Q univ)
  have hD_ne_top : D ≠ ∞ := by
    exact ENNReal.add_ne_top.mpr ⟨InformationTheory.klDiv_ne_top h_ac hllr_int,
      ENNReal.sub_ne_top (measure_ne_top P0 univ)⟩
  have hD_real : D.toReal = ∫ x, llr P0 Q x ∂P0 := by
    dsimp [D]
    rw [ENNReal.toReal_add (InformationTheory.klDiv_ne_top h_ac hllr_int)
      (ENNReal.sub_ne_top (measure_ne_top P0 univ)),
      InformationTheory.toReal_klDiv h_ac hllr_int,
      ENNReal.toReal_sub_of_le hQ_le_P0 (measure_ne_top P0 univ)]
    simp only [measureReal_def]
    ring
  change (stabilizedPopulationCriterion M mu theta0 theta : EReal) = -(D : EReal)
  rw [← EReal.coe_ennreal_toReal hD_ne_top, hD_real]
  exact_mod_cast hcrit

/-- The stabilized population criterion is strictly uniquely maximized at the
truth.  This is the p.63 mixture application of Lemma 5.35; the conclusion is
derived from the preceding KL bridge and raw-model identifiability. -/
theorem stabilized_populationCriterion_uniquely_maximized_at_truth
    {X : Type*} [MeasurableSpace X] {Theta : Type*}
    (M : ParametricFamily X Theta) (mu : Measure X) (theta0 : Theta)
    (hsub_int : forall theta, Integrable (M.density theta) mu)
    (hsub_mass : forall theta, (∫ x, M.density theta x ∂mu) <= 1)
    (htrue_mass : (∫ x, M.density theta0 x ∂mu) = 1)
    (hident : forall theta,
      parametricMeasure M mu theta = parametricMeasure M mu theta0 -> theta = theta0)
    (theta : Theta) (htheta : theta ≠ theta0) :
    stabilizedPopulationCriterion M mu theta0 theta <
      stabilizedPopulationCriterion M mu theta0 theta0 := by
  let P : Theta → Measure X := stabilizedParametricMeasure M mu theta0
  have hmix_int (eta : Theta) : Integrable (fun x =>
      (M.density eta x + M.density theta0 x) / 2) mu := by
    fun_prop
  have hmix_nonneg (eta : Theta) (x : X) :
      0 ≤ (M.density eta x + M.density theta0 x) / 2 :=
    div_nonneg (add_nonneg (M.density_nonneg eta x) (M.density_nonneg theta0 x)) (by norm_num)
  have hP_mass (eta : Theta) : P eta univ = ENNReal.ofReal
      (∫ x, (M.density eta x + M.density theta0 x) / 2 ∂mu) := by
    dsimp [P, stabilizedParametricMeasure]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hmix_int eta)]
    exact ae_of_all mu (hmix_nonneg eta)
  have hP_sub (eta : Theta) : P eta univ ≤ 1 := by
    rw [hP_mass]
    have hmass : (∫ x,
        (M.density eta x + M.density theta0 x) / 2 ∂mu) ≤ 1 := by
      rw [integral_div, integral_add (hsub_int eta) (hsub_int theta0), htrue_mass]
      linarith [hsub_mass eta]
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hmass
  have hP_true : P theta0 univ = 1 := by
    rw [hP_mass]
    have hmix_true : (∫ x,
        (M.density theta0 x + M.density theta0 x) / 2 ∂mu) = 1 := by
      rw [integral_div, integral_add (hsub_int theta0) (hsub_int theta0), htrue_mass]
      norm_num
    rw [hmix_true]
    simp
  have hP_ident (eta : Theta) (heq : P eta = P theta0) : eta = theta0 := by
    apply hident eta
    unfold parametricMeasure
    apply withDensity_congr_ae
    have hmix_finite :
        (∫⁻ x, ENNReal.ofReal
          ((M.density eta x + M.density theta0 x) / 2) ∂mu) ≠ ∞ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hmix_int eta)]
      · exact ENNReal.ofReal_ne_top
      · exact ae_of_all mu (hmix_nonneg eta)
    have hmix_meas (zeta : Theta) : Measurable (fun x => ENNReal.ofReal
        ((M.density zeta x + M.density theta0 x) / 2)) :=
      (((M.density_meas zeta).add (M.density_meas theta0)).div_const 2).ennreal_ofReal
    have hmix_ae : (fun x => ENNReal.ofReal
        ((M.density eta x + M.density theta0 x) / 2)) =ᵐ[mu]
        fun x => ENNReal.ofReal
          ((M.density theta0 x + M.density theta0 x) / 2) := by
      apply (withDensity_eq_iff (hmix_meas eta).aemeasurable
        (hmix_meas theta0).aemeasurable hmix_finite).mp
      simpa only [P, stabilizedParametricMeasure] using heq
    filter_upwards [hmix_ae] with x hx
    apply (ENNReal.ofReal_eq_ofReal_iff
      (M.density_nonneg eta x) (M.density_nonneg theta0 x)).2
    have hx_real := (ENNReal.ofReal_eq_ofReal_iff
      (hmix_nonneg eta x) (hmix_nonneg theta0 x)).mp hx
    linarith
  have hkl := ParametricFamily.kl_uniquely_maximized_at_truth P theta0
    hP_sub hP_true hP_ident theta htheta
  apply EReal.coe_lt_coe_iff.mp
  rw [stabilized_populationCriterion_eq_klObjective M mu theta0
      hsub_int hsub_mass htrue_mass theta,
    stabilized_populationCriterion_eq_klObjective M mu theta0
      hsub_int hsub_mass htrue_mass theta0]
  exact hkl

/-- **MLE consistency from vdV Lemma 5.35 and Theorem 5.7.**

Identifiability gives strict uniqueness for the p.63 stabilized criterion;
upper semicontinuity and compact far-superlevels upgrade uniqueness to the
well-separated maximum required by Theorem 5.7.  Uniform stochastic control and
near-maximality are the genuine Theorem 5.7 caller inputs. -/
theorem mEstimator_consistent_of_kl_identifiable
    {X : Type*} [MeasurableSpace X] {Theta : Type*} [MetricSpace Theta]
    (M : ParametricFamily X Theta) (mu : Measure X) (theta0 : Theta)
    (hsub_int : forall theta, Integrable (M.density theta) mu)
    (hsub_mass : forall theta, (∫ x, M.density theta x ∂mu) <= 1)
    (htrue_mass : (∫ x, M.density theta0 x ∂mu) = 1)
    (hident : forall theta,
      parametricMeasure M mu theta = parametricMeasure M mu theta0 -> theta = theta0)
    (husc : UpperSemicontinuous (stabilizedPopulationCriterion M mu theta0))
    (hcompact : ∃ c : Real,
      c < stabilizedPopulationCriterion M mu theta0 theta0 ∧
        IsCompact {theta | c <= stabilizedPopulationCriterion M mu theta0 theta})
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    (Mn : Nat -> Omega -> Theta -> Real) (thetahat : Nat -> Omega -> Theta)
    (U R : Nat -> Omega -> Real)
    (hU_dom : forall n omega theta,
      |Mn n omega theta - stabilizedPopulationCriterion M mu theta0 theta| <= U n omega)
    (hU_conv : TendstoInMeasure P U atTop (fun _ => (0 : Real)))
    (hnear : forall n omega,
      Mn n omega theta0 - R n omega <= Mn n omega (thetahat n omega))
    (hR_conv : TendstoInMeasure P R atTop (fun _ => (0 : Real)))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    Tendsto (fun n => P {omega | epsilon <= dist (thetahat n omega) theta0})
      atTop (nhds 0) := by
  have hunique : ∀ theta, theta ≠ theta0 ->
      stabilizedPopulationCriterion M mu theta0 theta <
        stabilizedPopulationCriterion M mu theta0 theta0 := by
    intro theta htheta
    exact stabilized_populationCriterion_uniquely_maximized_at_truth M mu theta0
      hsub_int hsub_mass htrue_mass hident theta htheta
  have hsep := ForMathlib.wellSeparated_of_uniqueMax_upperSemicontinuous_compactSuperlevel
    (stabilizedPopulationCriterion M mu theta0) theta0 hunique husc hcompact
  exact Consistency.mEstimator_consistent
    (Ω := Omega) (P := P) (Θ := Theta) (Mn := Mn)
    (M := stabilizedPopulationCriterion M mu theta0) (θ₀ := theta0)
    (θhat := thetahat) (U := U) (R := R)
    hU_dom hU_conv hsep hnear hR_conv epsilon hepsilon

/-- A product MLE dominates the p.63 stabilized empirical criterion at the
truth almost everywhere.  The exceptional samples are precisely those on
which at least one true-density factor vanishes; normalization makes each such
coordinate event null. -/
theorem stabilized_empirical_nearmax_ae_of_mle
    {X : Type*} [MeasurableSpace X] {Θ : Type*}
    (M : ParametricFamily X Θ) (μ : Measure X) (θ₀ : Θ)
    (θhat : ∀ n, (Fin n → X) → Θ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xs : ℕ → Ω → X)
    -- Measurability of the sample coordinates.
    (hXs_meas : ∀ i, Measurable (Xs i))
    -- Identical-distribution component of the sample encoding.
    (hXs_id : ∀ i, ProbabilityTheory.IdentDistrib (Xs i) (Xs 0) P P)
    -- Identifies the common observation law with the true model law.
    (hXs_law : P.map (Xs 0) =
      μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
    -- Exact product-likelihood maximization.
    (hMLE : IsMaximumLikelihoodEstimator M θhat) :
    ∀ n, ∀ᵐ ω ∂P,
      empiricalAvg (stabilizedLogCriterion M θ₀ θ₀) n
          (fun i : Fin n => Xs i.val ω) ≤
        empiricalAvg
          (stabilizedLogCriterion M θ₀
            (θhat n (fun i : Fin n => Xs i.val ω))) n
          (fun i : Fin n => Xs i.val ω) := by
  let Mmix : ParametricFamily X Θ :=
    { density := fun θ x => (M.density θ x + M.density θ₀ x) / 2
      density_meas := fun θ =>
        ((M.density_meas θ).add (M.density_meas θ₀)).div_const 2
      density_nonneg := fun θ x => div_nonneg
        (add_nonneg (M.density_nonneg θ x) (M.density_nonneg θ₀ x)) (by norm_num) }
  have htrue_pos : ∀ᵐ x ∂(μ.withDensity fun y =>
      ENNReal.ofReal (M.density θ₀ y)), 0 < M.density θ₀ x := by
    apply (ae_withDensity_iff (M.density_meas θ₀).ennreal_ofReal).2
    filter_upwards with x
    intro hx
    have hp_ne : M.density θ₀ x ≠ 0 := by
      intro hp
      exact hx (by simp [hp])
    exact lt_of_le_of_ne (M.density_nonneg θ₀ x) hp_ne.symm
  have hpos_meas : MeasurableSet {x : X | 0 < M.density θ₀ x} :=
    measurableSet_lt measurable_const (M.density_meas θ₀)
  have hcoord_pos (i : ℕ) : ∀ᵐ ω ∂P, 0 < M.density θ₀ (Xs i ω) := by
    apply (ae_map_iff (hXs_meas i).aemeasurable hpos_meas).1
    rw [(hXs_id i).map_eq, hXs_law]
    exact htrue_pos
  intro n
  have hall_pos : ∀ᵐ ω ∂P, ∀ i : Fin n, 0 < M.density θ₀ (Xs i.val ω) := by
    rw [ae_all_iff]
    intro i
    exact hcoord_pos i.val
  filter_upwards [hall_pos] with ω hpos
  let x : Fin n → X := fun i => Xs i.val ω
  let η : Θ := θhat n x
  have hB_pos : 0 < ∏ i : Fin n, M.density θ₀ (x i) :=
    Finset.prod_pos fun i _ => hpos i
  have hB_nonneg : 0 ≤ ∏ i : Fin n, M.density θ₀ (x i) := hB_pos.le
  have hA_nonneg : 0 ≤ ∏ i : Fin n, M.density η (x i) :=
    Finset.prod_nonneg fun i _ => M.density_nonneg η (x i)
  have hC_nonneg : 0 ≤ ∏ i : Fin n,
      (M.density η (x i) + M.density θ₀ (x i)) / 2 :=
    Finset.prod_nonneg fun i _ => div_nonneg
      (add_nonneg (M.density_nonneg η (x i)) (M.density_nonneg θ₀ (x i))) (by norm_num)
  have hBA : (∏ i : Fin n, M.density θ₀ (x i)) ≤
      ∏ i : Fin n, M.density η (x i) := by
    simpa only [sampleLikelihood, η, x] using hMLE n x θ₀
  have hBsq_le_AB :
      (∏ i : Fin n, M.density θ₀ (x i)) *
          (∏ i : Fin n, M.density θ₀ (x i)) ≤
        (∏ i : Fin n, M.density η (x i)) *
          (∏ i : Fin n, M.density θ₀ (x i)) :=
    mul_le_mul_of_nonneg_right hBA hB_nonneg
  have hAB_le_Csq :
      (∏ i : Fin n, M.density η (x i)) *
          (∏ i : Fin n, M.density θ₀ (x i)) ≤
        (∏ i : Fin n, (M.density η (x i) + M.density θ₀ (x i)) / 2) *
          (∏ i : Fin n, (M.density η (x i) + M.density θ₀ (x i)) / 2) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro i _
      exact mul_nonneg (M.density_nonneg η (x i)) (M.density_nonneg θ₀ (x i))
    · intro i _
      nlinarith [sq_nonneg (M.density η (x i) - M.density θ₀ (x i))]
  have hBC : (∏ i : Fin n, M.density θ₀ (x i)) ≤
      ∏ i : Fin n, (M.density η (x i) + M.density θ₀ (x i)) / 2 := by
    nlinarith [hBsq_le_AB.trans hAB_le_Csq]
  have hmix_pos : 0 < sampleLikelihood Mmix θ₀ n x := by
    simpa [sampleLikelihood, Mmix] using hB_pos
  have hmix_le : sampleLikelihood Mmix θ₀ n x ≤ sampleLikelihood Mmix η n x := by
    simpa [sampleLikelihood, Mmix] using hBC
  have hlog := empiricalAvg_logDensity_le_of_sampleLikelihood_le Mmix hmix_pos hmix_le
  have hstable_true (i : Fin n) : stabilizedLogCriterion M θ₀ θ₀ (x i) = 0 := by
    have hratio : (M.density θ₀ (x i) + M.density θ₀ (x i)) /
        (2 * M.density θ₀ (x i)) = 1 := by
      calc
        _ = (2 * M.density θ₀ (x i)) / (2 * M.density θ₀ (x i)) := by ring
        _ = 1 := div_self (mul_ne_zero (by norm_num) (hpos i).ne')
    rw [stabilizedLogCriterion, hratio, Real.log_one]
  have hstable_est (i : Fin n) : stabilizedLogCriterion M θ₀ η (x i) =
      Mmix.logDensity η (x i) - Mmix.logDensity θ₀ (x i) := by
    have hp0 : M.density θ₀ (x i) ≠ 0 := (hpos i).ne'
    have hmix : 0 < (M.density η (x i) + M.density θ₀ (x i)) / 2 :=
      div_pos (add_pos_of_nonneg_of_pos (M.density_nonneg η (x i)) (hpos i)) (by norm_num)
    rw [stabilizedLogCriterion]
    rw [show (M.density η (x i) + M.density θ₀ (x i)) /
        (2 * M.density θ₀ (x i)) =
        ((M.density η (x i) + M.density θ₀ (x i)) / 2) /
          M.density θ₀ (x i) by ring]
    rw [Real.log_div hmix.ne' hp0]
    simp [ParametricFamily.logDensity, Mmix]
  rw [show empiricalAvg (stabilizedLogCriterion M θ₀ θ₀) n x = 0 by
    unfold empiricalAvg
    simp_rw [hstable_true]
    simp]
  rw [show empiricalAvg (stabilizedLogCriterion M θ₀ η) n x =
      empiricalAvg (Mmix.logDensity η) n x -
        empiricalAvg (Mmix.logDensity θ₀) n x by
    unfold empiricalAvg
    simp_rw [hstable_est]
    rw [Finset.sum_sub_distrib, mul_sub]]
  exact sub_nonneg.mpr hlog

/-- MLE consistency from KL identifiability with no public near-maximization
remainder.  Product maximization gives the a.e. stabilized comparison, which
feeds the a.e.-nearmax form of Theorem 5.7. -/
theorem mle_consistentInProb_of_kl_identifiable
    {d : ℕ} {X : Type*} [MeasurableSpace X]
    (M : ParametricFamily X (EuclideanSpace ℝ (Fin d))) (μ : Measure X)
    (θ₀ : EuclideanSpace ℝ (Fin d))
    -- USER-INPUT: the model is a family of probability densities w.r.t. μ; vdV §5.5
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: identifiability, P_θ = P_{θ₀} → θ = θ₀; vdV Lem 5.35
    (hident : ∀ θ, parametricMeasure M μ θ = parametricMeasure M μ θ₀ → θ = θ₀)
    -- USER-INPUT: upper semicontinuity of the population criterion (Wald-type
    -- regularity used to derive the well-separated maximum); vdV Thm 5.7 route, §5.2
    (husc : UpperSemicontinuous (stabilizedPopulationCriterion M μ θ₀))
    -- USER-INPUT: a compact superlevel set below the maximum (vdV's compactness
    -- caveat for the argmax argument); vdV §5.2
    (hcompact : ∃ c : ℝ,
      c < stabilizedPopulationCriterion M μ θ₀ θ₀ ∧
        IsCompact {θ | c ≤ stabilizedPopulationCriterion M μ θ₀ θ})
    (θhat : ∀ n, (Fin n → X) → EuclideanSpace ℝ (Fin d))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xs : ℕ → Ω → X) (U : ℕ → Ω → ℝ)
    -- USER-INPUT (hU_dom, hU_conv): uniform convergence of the empirical criterion,
    -- phrased through a measurable envelope U; vdV Thm 5.7
    (hU_dom : ∀ n ω θ,
      |empiricalAvg (stabilizedLogCriterion M θ₀ θ) n
          (fun i : Fin n => Xs i.val ω) -
        stabilizedPopulationCriterion M μ θ₀ θ| ≤ U n ω)
    -- (second half of the envelope input above)
    (hU_conv : TendstoInMeasure P U atTop (fun _ => (0 : ℝ)))
    -- LEAN-ONLY: measurability of the sample coordinates; no scope change.
    (hXs_meas : ∀ i, Measurable (Xs i))
    -- USER-INPUT (hXs_id, hXs_law): identically distributed observations drawn from
    -- the true model law P_{θ₀}; vdV §5.2
    (hXs_id : ∀ i, ProbabilityTheory.IdentDistrib (Xs i) (Xs 0) P P)
    -- (second half of the sample-law input above)
    (hXs_law : P.map (Xs 0) =
      μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x))
    -- USER-INPUT: θ̂ₙ maximizes the product likelihood (exact MLE); vdV §5.5
    (hMLE : IsMaximumLikelihoodEstimator M θhat) :
    TendstoInProbZero (fun _ : ℕ => P)
      (fun n ω => θhat n (fun i : Fin n => Xs i.val ω) - θ₀) := by
  have hsub_mass : ∀ θ, (∫ x, M.density θ x ∂μ) ≤ 1 := by
    intro θ
    rw [hPDF.density_integral_eq_one θ]
  have htrue_mass : (∫ x, M.density θ₀ x ∂μ) = 1 :=
    hPDF.density_integral_eq_one θ₀
  have hunique : ∀ θ, θ ≠ θ₀ →
      stabilizedPopulationCriterion M μ θ₀ θ <
        stabilizedPopulationCriterion M μ θ₀ θ₀ := by
    intro θ hθ
    exact stabilized_populationCriterion_uniquely_maximized_at_truth M μ θ₀
      hPDF.density_integrable hsub_mass htrue_mass hident θ hθ
  have hsep := ForMathlib.wellSeparated_of_uniqueMax_upperSemicontinuous_compactSuperlevel
    (stabilizedPopulationCriterion M μ θ₀) θ₀ hunique husc hcompact
  let θhatΩ : ℕ → Ω → EuclideanSpace ℝ (Fin d) :=
    fun n ω => θhat n (fun i : Fin n => Xs i.val ω)
  have hnear : ∀ n, ∀ᵐ ω ∂P,
      empiricalAvg (stabilizedLogCriterion M θ₀ θ₀) n
          (fun i : Fin n => Xs i.val ω) ≤
        empiricalAvg (stabilizedLogCriterion M θ₀ (θhatΩ n ω)) n
          (fun i : Fin n => Xs i.val ω) := by
    simpa only [θhatΩ] using stabilized_empirical_nearmax_ae_of_mle
      M μ θ₀ θhat P Xs hXs_meas hXs_id hXs_law hMLE
  have hcons : ∀ ε > (0 : ℝ),
      Tendsto (fun n => P {ω | ε ≤ dist (θhatΩ n ω) θ₀}) atTop (𝓝 0) := by
    exact Consistency.mEstimator_consistent_ae_nearmax
      (Mn := fun n ω θ => empiricalAvg (stabilizedLogCriterion M θ₀ θ) n
        (fun i : Fin n => Xs i.val ω))
      (M := stabilizedPopulationCriterion M μ θ₀) (θ₀ := θ₀)
      (θhat := θhatΩ) (U := U) hU_dom hU_conv hsep hnear
  unfold TendstoInProbZero
  intro ε hε
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcons ε hε)
  simpa only [θhatΩ, measureReal_def, ENNReal.toReal_zero, dist_eq_norm] using! h

/-- Convert the explicit metric consistency conclusion of Theorem 5.7 to the
project's varying-base `TendstoInProbZero` form used by Theorem 5.23.

This is representation-only glue: it assumes exactly the already-derived T4
conclusion and introduces no statistical regularity hypothesis. -/
theorem tendstoInProbZero_sub_of_t4_consistency
    {Omega : Type*} [MeasurableSpace Omega] (P : Measure Omega)
    {Theta : Type*} [NormedAddCommGroup Theta]
    (thetahat : Nat -> Omega -> Theta) (theta0 : Theta)
    (hcons : ∀ epsilon, 0 < epsilon ->
      Tendsto (fun n => P {omega | epsilon <= dist (thetahat n omega) theta0})
        atTop (nhds 0)) :
    TendstoInProbZero (fun _ => P) (fun n omega => thetahat n omega - theta0) := by
  unfold TendstoInProbZero
  intro epsilon hepsilon
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hcons epsilon hepsilon)
  simpa only [measureReal_def, ENNReal.toReal_zero, dist_eq_norm] using! h

end AsymptoticStatistics.MaximumLikelihood
