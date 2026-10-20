module
public import StatLean.AsymptoticStatistics.ForMathlib.WeakConvergence.OuterTightness

@[expose] public section

/-!
# Slutsky perturbation for weak convergence in outer expectation

This file proves the shared-base outer analogue of Slutsky's theorem.  Neither
map is assumed measurable: closeness is expressed by the outer value
`μ.real {ω | δ ≤ dist (X ω) (Y ω)}`.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace AsymptoticStatistics

/-- The outer mass `E*[1_A]` is at most the outer value `μ A`, without a
measurability assumption on `A`. -/
theorem outerMeasureStar_le_measure {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) : μ.outerMeasureStar A ≤ μ A := by
  rw [measure_eq_iInf]
  refine le_iInf fun t => le_iInf fun hAt => le_iInf fun ht => ?_
  rw [Measure.outerMeasureStar, outerExpectation]
  calc
    (⨅ U : {U : Ω → ℝ≥0∞ // Measurable U ∧ A.indicator 1 ≤ U},
        ∫⁻ ω, (U : Ω → ℝ≥0∞) ω ∂μ)
        ≤ ∫⁻ ω, t.indicator 1 ω ∂μ :=
      iInf_le (fun U : {U : Ω → ℝ≥0∞ // Measurable U ∧ A.indicator 1 ≤ U} =>
        ∫⁻ ω, (U : Ω → ℝ≥0∞) ω ∂μ)
        ⟨t.indicator 1, measurable_one.indicator ht, fun ω => by
          by_cases hω : ω ∈ A
          · simp [hω, hAt hω]
          · simp [hω]⟩
    _ = μ t := lintegral_indicator_one ht

/-- A one-sided real bound for shifted outer readouts. -/
theorem outerReadout_le_of_modulus {Ω D : Type*} [MeasurableSpace Ω]
    [MeasurableSpace D] [PseudoMetricSpace D] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : D →ᵇ ℝ) (X Y : Ω → D) {δ η : ℝ} (hη : 0 ≤ η)
    (hmod : ∀ ω, dist (X ω) (Y ω) ≤ δ → f (X ω) ≤ f (Y ω) + η) :
    (outerExpectation μ (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖))).toReal ≤
      (outerExpectation μ (fun ω => ENNReal.ofReal (f (Y ω) + ‖f‖))).toReal + η +
        2 * ‖f‖ * (outerExpectation μ
          ({ω | δ < dist (X ω) (Y ω)}.indicator (fun _ => (1 : ℝ≥0∞)))).toReal := by
  classical
  set bad : Set Ω := {ω | δ < dist (X ω) (Y ω)}
  set ind : Ω → ℝ≥0∞ := bad.indicator (fun _ => 1)
  set EX := outerExpectation μ (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖))
  set EY := outerExpectation μ (fun ω => ENNReal.ofReal (f (Y ω) + ‖f‖))
  set I := outerExpectation μ ind
  set err : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal η + ENNReal.ofReal (2 * ‖f‖) * ind ω
  have hmaj : ∀ ω, ENNReal.ofReal (f (X ω) + ‖f‖) ≤
      ENNReal.ofReal (f (Y ω) + ‖f‖) + ENNReal.ofReal 1 * err ω := by
    intro ω
    rw [ENNReal.ofReal_one, one_mul]
    change ENNReal.ofReal (f (X ω) + ‖f‖) ≤
      ENNReal.ofReal (f (Y ω) + ‖f‖) +
        (ENNReal.ofReal η + ENNReal.ofReal (2 * ‖f‖) * ind ω)
    have hY : 0 ≤ f (Y ω) + ‖f‖ := by
      have := (abs_le.1 (f.norm_coe_le_norm (Y ω))).1
      linarith
    have hreal : f (X ω) + ‖f‖ ≤ f (Y ω) + ‖f‖ +
        (η + 2 * ‖f‖ * (ind ω).toReal) := by
      by_cases hg : dist (X ω) (Y ω) ≤ δ
      · have hi : ind ω = 0 := by simp [ind, bad, not_lt.2 hg]
        rw [hi]
        simp only [ENNReal.toReal_zero, mul_zero, add_zero]
        linarith [hmod ω hg]
      · have hi : ind ω = 1 := by simp [ind, bad, lt_of_not_ge hg]
        rw [hi]
        simp only [ENNReal.toReal_one, mul_one]
        have hX := (abs_le.1 (f.norm_coe_le_norm (X ω))).2
        have hY' := (abs_le.1 (f.norm_coe_le_norm (Y ω))).1
        linarith
    calc
      ENNReal.ofReal (f (X ω) + ‖f‖) ≤
          ENNReal.ofReal (f (Y ω) + ‖f‖ + (η + 2 * ‖f‖ * (ind ω).toReal)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (f (Y ω) + ‖f‖) +
          (ENNReal.ofReal η + ENNReal.ofReal (2 * ‖f‖) * ind ω) := by
        have hi : ind ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
          (Set.indicator_le_self _ _ ω)
        rw [ENNReal.ofReal_add hY (by positivity), ENNReal.ofReal_add hη (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hi]
  have hS5 := outerExpectation_readout_triangle μ f X Y 1 err hmaj
  rw [ENNReal.ofReal_one, one_mul] at hS5
  have hEerr : outerExpectation μ err ≤
      ENNReal.ofReal η + ENNReal.ofReal (2 * ‖f‖) * I := by
    have hs := outerExpectation_add_le (μ := μ) (fun _ => ENNReal.ofReal η)
      (fun ω => ENNReal.ofReal (2 * ‖f‖) * ind ω)
    have hc : outerExpectation μ (fun _ => ENNReal.ofReal η) = ENNReal.ofReal η := by
      rw [outerExpectation_const]
      simp
    have hm : outerExpectation μ (fun ω => ENNReal.ofReal (2 * ‖f‖) * ind ω) =
        ENNReal.ofReal (2 * ‖f‖) * I := by
      have heq : (fun ω => ENNReal.ofReal (2 * ‖f‖) * ind ω) =
          ENNReal.ofReal (2 * ‖f‖) • ind := by ext; simp [smul_eq_mul]
      change outerExpectation μ (fun ω => ENNReal.ofReal (2 * ‖f‖) * ind ω) =
        ENNReal.ofReal (2 * ‖f‖) * outerExpectation μ ind
      rw [heq, outerExpectation_const_smul _ ENNReal.ofReal_ne_top, smul_eq_mul]
    have hs' : outerExpectation μ err ≤
        outerExpectation μ (fun _ => ENNReal.ofReal η) +
          outerExpectation μ (fun ω => ENNReal.ofReal (2 * ‖f‖) * ind ω) := by
      simpa only [err, Pi.add_apply] using! hs
    rw [hc, hm] at hs'
    exact hs'
  have hS5' : EX ≤ EY + outerExpectation μ err := by simpa [EX, EY] using hS5
  have hchain : EX ≤ EY + (ENNReal.ofReal η + ENNReal.ofReal (2 * ‖f‖) * I) :=
    hS5'.trans (add_le_add le_rfl hEerr)
  have hI_le : I ≤ 1 := by
    calc
      I ≤ outerExpectation μ (fun _ => 1) :=
        outerExpectation_mono fun ω => Set.indicator_le_self _ _ ω
      _ = 1 := by rw [outerExpectation_const]; simp
  have hI_top : I ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hI_le
  have hEY_le : EY ≤ ENNReal.ofReal (2 * ‖f‖) := by
    calc
      EY ≤ outerExpectation μ (fun _ => ENNReal.ofReal (2 * ‖f‖)) := by
        refine outerExpectation_mono fun ω => ENNReal.ofReal_le_ofReal ?_
        have := (abs_le.1 (f.norm_coe_le_norm (Y ω))).2
        linarith
      _ = ENNReal.ofReal (2 * ‖f‖) := by rw [outerExpectation_const]; simp
  have hEY_top : EY ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEY_le
  have hRHS : EY + (ENNReal.ofReal η + ENNReal.ofReal (2 * ‖f‖) * I) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hEY_top, ENNReal.add_ne_top.2
      ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI_top⟩⟩
  have hr := (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hRHS hchain) hRHS).2 hchain
  rw [ENNReal.toReal_add hEY_top (ENNReal.add_ne_top.2
      ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI_top⟩),
    ENNReal.toReal_add ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI_top), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hη, ENNReal.toReal_ofReal (by positivity)] at hr
  change EX.toReal ≤ EY.toReal + η + 2 * ‖f‖ * I.toReal
  linarith

/-- The corresponding two-sided shifted-readout bound. -/
theorem abs_outerReadout_diff_le_of_modulus {Ω D : Type*} [MeasurableSpace Ω]
    [MeasurableSpace D] [PseudoMetricSpace D] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (f : D →ᵇ ℝ) (X Y : Ω → D) {δ η : ℝ} (hη : 0 ≤ η)
    (hmod : ∀ ω, dist (X ω) (Y ω) ≤ δ → |f (X ω) - f (Y ω)| ≤ η) :
    |(outerExpectation μ (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖))).toReal -
        (outerExpectation μ (fun ω => ENNReal.ofReal (f (Y ω) + ‖f‖))).toReal| ≤
      η + 2 * ‖f‖ * (outerExpectation μ
        ({ω | δ < dist (X ω) (Y ω)}.indicator (fun _ => (1 : ℝ≥0∞)))).toReal := by
  rw [abs_sub_le_iff]
  constructor
  · have h := outerReadout_le_of_modulus μ f X Y hη fun ω hω => by
      linarith [le_trans (le_abs_self (f (X ω) - f (Y ω))) (hmod ω hω)]
    linarith
  · have h := outerReadout_le_of_modulus μ f Y X hη fun ω hω => by
      have hm := hmod ω (by simpa [dist_comm] using hω)
      linarith [le_trans (le_abs_self (f (Y ω) - f (X ω))) (by simpa [abs_sub_comm] using hm)]
    simpa only [dist_comm] using (by linarith [h] :
      (outerExpectation μ (fun ω => ENNReal.ofReal (f (Y ω) + ‖f‖))).toReal -
        (outerExpectation μ (fun ω => ENNReal.ofReal (f (X ω) + ‖f‖))).toReal ≤
      η + 2 * ‖f‖ * (outerExpectation μ
        ({ω | δ < dist (Y ω) (X ω)}.indicator (fun _ => (1 : ℝ≥0∞)))).toReal)

/-- **Outer Slutsky theorem.** If `Xₙ` converges weakly in outer expectation and
`dist (Xₙ,Yₙ)` tends to zero in outer probability, then `Yₙ` has the same outer
weak limit. -/
theorem WeakConvergesOuter.slutsky_of_tendstoInOuterProbability_dist
    {Ω D : Type*} [MeasurableSpace Ω] [MeasurableSpace D] [PseudoMetricSpace D]
    [OpensMeasurableSpace D] {μ : ℕ → Measure Ω} [∀ n, IsProbabilityMeasure (μ n)]
    {X Y : ℕ → Ω → D} {ν : Measure D} [IsProbabilityMeasure ν]
    (hX : WeakConvergesOuter μ X ν)
    (hDist : ∀ δ > 0, Tendsto
      (fun n => (μ n).real {ω | δ ≤ dist (X n ω) (Y n ω)}) atTop (𝓝 0)) :
    WeakConvergesOuter μ Y ν := by
  apply weakConvergesOuter_of_lipschitz_readout (νD := ν)
  intro f hf
  obtain ⟨K, hK⟩ := hf
  let RX : ℕ → ℝ := fun n =>
    (outerExpectation (μ n) (fun ω => ENNReal.ofReal (f (X n ω) + ‖f‖))).toReal -
      ‖f‖ * (μ n Set.univ).toReal
  let RY : ℕ → ℝ := fun n =>
    (outerExpectation (μ n) (fun ω => ENNReal.ofReal (f (Y n ω) + ‖f‖))).toReal -
      ‖f‖ * (μ n Set.univ).toReal
  have hdiff : Tendsto (fun n => RY n - RX n) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let δ : ℝ := ε / (4 * ((K : ℝ) + 1))
    have hδ : 0 < δ := by positivity
    let I : ℕ → ℝ := fun n =>
      (outerExpectation (μ n)
        ({ω | δ < dist (X n ω) (Y n ω)}.indicator (fun _ => (1 : ℝ≥0∞)))).toReal
    have hI_le : ∀ n, I n ≤ (μ n).real {ω | δ ≤ dist (X n ω) (Y n ω)} := by
      intro n
      change (outerExpectation (μ n)
        ({ω | δ < dist (X n ω) (Y n ω)}.indicator (fun _ => (1 : ℝ≥0∞)))).toReal ≤
          ((μ n) {ω | δ ≤ dist (X n ω) (Y n ω)}).toReal
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      change (μ n).outerMeasureStar {ω | δ < dist (X n ω) (Y n ω)} ≤
        (μ n) {ω | δ ≤ dist (X n ω) (Y n ω)}
      exact (outerMeasureStar_le_measure (μ n) _).trans
        (measure_mono fun _ hω => by
          simpa only [Set.mem_setOf_eq] using hω.le)
    have hI : Tendsto I atTop (𝓝 0) :=
      squeeze_zero (fun n => ENNReal.toReal_nonneg) hI_le (hDist δ hδ)
    have hscaled : Tendsto (fun n => 2 * ‖f‖ * I n) atTop (𝓝 0) := by
      simpa using hI.const_mul (2 * ‖f‖)
    have hsmall : ∀ᶠ n in atTop, 2 * ‖f‖ * I n < ε / 2 :=
      hscaled.eventually_lt_const (by simpa using half_pos hε)
    filter_upwards [hsmall] with n hn
    have hmod : ∀ ω, dist (X n ω) (Y n ω) ≤ δ →
        |f (X n ω) - f (Y n ω)| ≤ (K : ℝ) * δ := by
      intro ω hω
      exact (hK.dist_le_mul_of_le hω)
    have hb := abs_outerReadout_diff_le_of_modulus (δ := δ) (η := (K : ℝ) * δ)
      (μ n) f (Y n) (X n)
      (by positivity) (fun ω hω => by
        rw [abs_sub_comm]
        exact hmod ω (by simpa [dist_comm] using hω))
    have hη : (K : ℝ) * δ < ε / 2 := by
      dsimp [δ]
      have hK1 : (K : ℝ) < 2 * ((K : ℝ) + 1) := by
        have hK0 : (0 : ℝ) ≤ K := NNReal.zero_le_coe
        linarith
      calc
        (K : ℝ) * (ε / (4 * ((K : ℝ) + 1)))
            = ε / 2 * ((K : ℝ) / (2 * ((K : ℝ) + 1))) := by field_simp; ring
        _ < ε / 2 * 1 := mul_lt_mul_of_pos_left ((div_lt_one (by positivity)).2 hK1)
          (half_pos hε)
        _ = ε / 2 := mul_one _
    rw [Real.dist_eq, sub_zero]
    rw [show RY n - RX n =
        (outerExpectation (μ n)
          (fun ω => ENNReal.ofReal (f (Y n ω) + ‖f‖))).toReal -
        (outerExpectation (μ n)
          (fun ω => ENNReal.ofReal (f (X n ω) + ‖f‖))).toReal by
      dsimp only [RY, RX]
      ring]
    exact lt_of_le_of_lt (by simpa [I, dist_comm] using hb) (by linarith)
  have hXf : Tendsto RX atTop (𝓝 (∫ y, f y ∂ν)) := by
    simpa only [RX] using hX f
  simpa only [RY, RX, sub_add_cancel, zero_add] using hdiff.add hXf

end AsymptoticStatistics
