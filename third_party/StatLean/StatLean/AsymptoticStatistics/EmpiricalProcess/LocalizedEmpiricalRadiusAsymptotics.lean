module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ChangingLindeberg
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LocalizedEmpiricalSquareRadius
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringOuterMaximal
public import Mathlib.MeasureTheory.Integral.MeanInequalities

@[expose] public section
namespace AsymptoticStatistics.EmpiricalProcess
open Filter MeasureTheory Topology
open scoped ENNReal NNReal
set_option linter.style.longLine false
theorem lintegral_localized_empiricalSquareRadius_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Set (Ω → ℝ))
    (hDense : ∀ n, EmpProcPointwiseDense (F n) P)
    (hF_meas : ∀ n g, g ∈ F n → Measurable g)
    (Φ : ℕ → Ω → ℝ)
    (hΦ : ∀ n, IsEnvelope (F n) (Φ n))
    (hΦmeas : ∀ n, Measurable (Φ n))
    (hLin : ChangingLindeberg P Φ)
    (hJ : ∀ a : ℕ → ℝ,
      (∀ n, 0 < a n) → Antitone a →
      Tendsto a atTop (𝓝 0) →
      Tendsto (fun n =>
        bookUniformCoveringEntropyIntegral (a n) (F n) (Φ n))
        atTop (𝓝 0))
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n)
    (hεanti : Antitone ε)
    (hεzero : Tendsto ε atTop (𝓝 0))
    (htail : Tendsto (fun n =>
      ∫⁻ x in {x | ε n * Real.sqrt n < |Φ n x|},
        ENNReal.ofReal ((Φ n x) ^ 2) ∂P) atTop (𝓝 0)) :
    Tendsto (fun n =>
      ∫⁻ Z : Fin n → Ω,
        empiricalSquareRadius
          (strictLocalizedDifferenceClass (F n) P (Real.sqrt (ε n))) n Z
        ∂Measure.pi (fun _ : Fin n => P)) atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun n => Real.sqrt (ε n)
  let J : ℕ → ℝ≥0∞ := fun n => bookUniformCoveringEntropyIntegral (a n) (F n) (Φ n)
  let G : ℕ → Set (Ω → ℝ) := fun n => strictLocalizedDifferenceClass (F n) P (Real.sqrt (ε n))
  let θ : ∀ n, (Fin n → Ω) → ℝ := fun n Z => empiricalRelativeRadiusReal (G n) (fun x => 2 * Φ n x) n Z
  let D : ∀ n, (Fin n → Ω) → ℝ≥0∞ := fun n Z => ENNReal.ofReal (empiricalL2Seminorm n Z (fun x => 2 * Φ n x))
  let Q : ℕ → ℝ≥0∞ := fun n => J n + ENNReal.ofReal (1 / a n) * J n
  obtain ⟨B, hBtop, hB⟩ := hLin.1
  let M : ℝ≥0∞ := 2 * B ^ (1 / 2 : ℝ)
  let C : ℝ≥0∞ := 16 * (78 * ENNReal.ofReal (Real.sqrt 2)) * M
  have ha_pos : ∀ n, 0 < a n := fun n => Real.sqrt_pos.2 (hεpos n)
  have ha_anti : Antitone a := fun _ _ hnm => Real.sqrt_le_sqrt (hεanti hnm)
  have ha_zero : Tendsto a atTop (𝓝 0) := by
    simpa only [a, Real.sqrt_zero] using! (Real.continuous_sqrt.tendsto 0).comp hεzero
  have hJzero : Tendsto J atTop (𝓝 0) := hJ a ha_pos ha_anti ha_zero
  have hMtop : M < ⊤ := by
    exact ENNReal.mul_lt_top (by norm_num) (ENNReal.rpow_lt_top_of_nonneg (by positivity) hBtop.ne)
  have hCtop : C < ⊤ := by
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num)
      (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)) hMtop
  have hnorm : ∀ n, eLpNorm (fun x => 2 * Φ n x) 2 P ≤ M := by
    intro n
    have hbase : eLpNorm (Φ n) 2 P ≤ B ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
      norm_num only [ENNReal.toReal_ofNat]
      have hint : (∫⁻ x, ‖Φ n x‖ₑ ^ (2 : ℝ) ∂P) = ∫⁻ x, ENNReal.ofReal ((Φ n x) ^ 2) ∂P := by
        refine lintegral_congr fun x => ?_
        rw [ENNReal.rpow_two, Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg (Φ n x)), sq_abs]
      rw [hint]
      exact ENNReal.rpow_le_rpow (hB n) (by norm_num)
    rw [show (fun x => 2 * Φ n x) = (2 : ℝ) • Φ n by ext; simp]
    rw [eLpNorm_const_smul]
    norm_num [Real.enorm_eq_ofReal_abs, M]; exact mul_le_mul_right hbase 2
  have hJ_eventually : ∀ᶠ n in atTop, J n ≤ 1 := ((tendsto_order.1 hJzero).2 1 (by norm_num)).mono fun _ h => h.le
  have hn_eventually : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_atTop.2 ⟨1, fun _ => id⟩
  have hupper : ∀ᶠ n : ℕ in atTop,
      (∫⁻ Z : Fin n → Ω, empiricalSquareRadius (G n) n Z
        ∂Measure.pi (fun _ : Fin n => P)) ≤
      ENNReal.ofReal (ε n) +
        C * (ENNReal.ofReal (ε n) + ENNReal.ofReal (a n)) +
        4 * ∫⁻ x in {x | ε n * Real.sqrt n < |Φ n x|},
          ENNReal.ofReal ((Φ n x) ^ 2) ∂P := by
    filter_upwards [hJ_eventually, hn_eventually] with n hJn hn
    have hJtop : J n ≠ ⊤ := ne_of_lt (hJn.trans_lt (by norm_num))
    have hratio_top : ENNReal.ofReal (1 / a n) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hQtop : Q n ≠ ⊤ := by
      dsimp only [Q]
      exact ENNReal.add_ne_top.mpr ⟨hJtop, ENNReal.mul_ne_top hratio_top hJtop⟩
    have hlocalEnvelope : IsEnvelope (G n) (fun x => 2 * Φ n x) := by
      dsimp only [G]
      exact (isEnvelope_differenceClass_two (hΦ n)).mono
        (strictLocalizedDifferenceClass_subset_differenceClass (F n) P (Real.sqrt (ε n)))
    have htheta (Z : Fin n → Ω) : θ n Z ≤ 1 :=
      empiricalRelativeRadiusReal_le_one_of_isEnvelope _ _ _ _ hlocalEnvelope
    have hentropy (Z : Fin n → Ω) :
        bookUniformCoveringEntropyIntegral (θ n Z) (F n) (Φ n) ≤ Q n := by
      dsimp only [Q]
      refine (bookUniformCoveringEntropyIntegral_le_initial_add_ratio_mul_initial (F n) (Φ n) (ha_pos n)).trans ?_
      gcongr; exact htheta Z
    have hI :
        (∫⁻ Z : Fin n → Ω, D n Z *
            bookUniformCoveringEntropyIntegral (θ n Z) (F n) (Φ n)
          ∂Measure.pi (fun _ : Fin n => P)) ≤ Q n * M := by
      calc
        _ ≤ ∫⁻ Z : Fin n → Ω, Q n * D n Z ∂Measure.pi (fun _ : Fin n => P) := by
          refine lintegral_mono fun Z => ?_; rw [mul_comm]; gcongr; exact hentropy Z
        _ = Q n * ∫⁻ Z : Fin n → Ω, D n Z ∂Measure.pi (fun _ : Fin n => P) := by
          rw [lintegral_const_mul' _ _ hQtop]
        _ ≤ Q n * M := by
          gcongr; dsimp only [D]
          exact (lintegral_empiricalL2Seminorm_le_eLpNorm
            P (fun x => 2 * Φ n x) ((hΦmeas n).const_mul 2) n).trans (hnorm n)
    have hcoeff : ENNReal.ofReal (8 * (2 * ε n * Real.sqrt n) * (Real.sqrt n)⁻¹) = ENNReal.ofReal (16 * ε n) := by
      apply congrArg ENNReal.ofReal
      have hsqrt : Real.sqrt n ≠ 0 := by positivity
      field_simp; ring
    have htail_set : {x | 2 * ε n * Real.sqrt n < 2 * |Φ n x|} =
        {x | ε n * Real.sqrt n < |Φ n x|} := by
      ext x
      simp only [Set.mem_setOf_eq]; constructor <;> intro hx <;> linarith
    have hscaled :
        (ENNReal.ofReal (16 * ε n) *
            (78 * ENNReal.ofReal (Real.sqrt 2))) *
          (Q n * M) ≤
        C * (ENNReal.ofReal (ε n) + ENNReal.ofReal (a n)) := by
      have ha := ha_pos n
      have ha_sq : ε n = a n * a n := by
        dsimp only [a]
        rw [Real.mul_self_sqrt (le_of_lt (hεpos n))]
      have hreal : 16 * ε n * (1 + 1 / a n) = 16 * (ε n + a n) := by
        rw [ha_sq]
        field_simp
      have hratio : ENNReal.ofReal (16 * ε n) *
          (1 + ENNReal.ofReal (1 / a n)) =
          16 * (ENNReal.ofReal (ε n) + ENNReal.ofReal (a n)) := by
        rw [← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add (by norm_num) (one_div_nonneg.mpr ha.le),
          ← ENNReal.ofReal_mul
            (mul_nonneg (by norm_num) (le_of_lt (hεpos n))), hreal,
          ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_add (le_of_lt (hεpos n)) (le_of_lt ha)]
        norm_num
      calc
        _ ≤ (ENNReal.ofReal (16 * ε n) *
              (78 * ENNReal.ofReal (Real.sqrt 2))) *
            ((1 + ENNReal.ofReal (1 / a n)) * M) := by
          gcongr
          dsimp only [Q]
          exact add_le_add hJn
            (by simpa using mul_le_mul_right hJn (ENNReal.ofReal (1 / a n)))
        _ = _ := by
          rw [show (ENNReal.ofReal (16 * ε n) *
              (78 * ENNReal.ofReal (Real.sqrt 2))) *
              ((1 + ENNReal.ofReal (1 / a n)) * M) =
              (ENNReal.ofReal (16 * ε n) *
                (1 + ENNReal.ofReal (1 / a n))) *
              ((78 * ENNReal.ofReal (Real.sqrt 2)) * M) by ring,
            hratio]
          dsimp only [C]
          ring
    calc
      _ ≤ ENNReal.ofReal ((Real.sqrt (ε n)) ^ 2) +
          (ENNReal.ofReal (8 * (2 * ε n * Real.sqrt n) * (Real.sqrt n)⁻¹) *
            (78 * ENNReal.ofReal (Real.sqrt 2))) *
            (∫⁻ Z : Fin n → Ω,
              D n Z * bookUniformCoveringEntropyIntegral
                (θ n Z) (F n) (Φ n)
              ∂Measure.pi (fun _ : Fin n => P)) +
          4 * ∫⁻ x in {x | 2 * ε n * Real.sqrt n < 2 * |Φ n x|},
            ENNReal.ofReal ((Φ n x) ^ 2) ∂P := by
        simpa only [G, D, θ] using
          lintegral_canonical_empiricalSquareRadius_strictLocalizedDifferenceClass_le_rowBookEntropy
            P (F n) (hDense n) (hF_meas n) (Φ n) (hΦ n)
            (hLin.envelope_memLp_two hΦmeas n) (hΦmeas n)
            (Real.sqrt (ε n)) (2 * ε n * Real.sqrt n)
            (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt (hεpos n)))
              (Real.sqrt_nonneg _)) n
      _ ≤ ENNReal.ofReal (ε n) +
          C * (ENNReal.ofReal (ε n) + ENNReal.ofReal (a n)) +
          4 * ∫⁻ x in {x | ε n * Real.sqrt n < |Φ n x|},
            ENNReal.ofReal ((Φ n x) ^ 2) ∂P := by
        rw [Real.sq_sqrt (le_of_lt (hεpos n)), hcoeff, htail_set]
        exact add_le_add (add_le_add le_rfl
          ((mul_le_mul_right hI _).trans hscaled)) le_rfl
  have heps_enn : Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, ENNReal.ofReal_zero] using! ENNReal.continuous_ofReal.continuousAt.tendsto.comp hεzero
  have ha_enn : Tendsto (fun n => ENNReal.ofReal (a n)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, ENNReal.ofReal_zero] using! ENNReal.continuous_ofReal.continuousAt.tendsto.comp ha_zero
  have hentropy_term : Tendsto (fun n =>
      C * (ENNReal.ofReal (ε n) + ENNReal.ofReal (a n))) atTop (𝓝 0) := by
    simpa only [zero_add, add_zero, mul_zero] using
      ENNReal.Tendsto.const_mul (heps_enn.add ha_enn) (Or.inr hCtop.ne)
  have htail4 : Tendsto (fun n =>
      4 * ∫⁻ x in {x | ε n * Real.sqrt n < |Φ n x|},
        ENNReal.ofReal ((Φ n x) ^ 2) ∂P) atTop (𝓝 0) :=
    by simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := (4 : ℝ≥0∞)) htail (Or.inr (by norm_num))
  have hbound_zero : Tendsto (fun n =>
      ENNReal.ofReal (ε n) +
        C * (ENNReal.ofReal (ε n) + ENNReal.ofReal (a n)) +
        4 * ∫⁻ x in {x | ε n * Real.sqrt n < |Φ n x|},
          ENNReal.ofReal ((Φ n x) ^ 2) ∂P) atTop (𝓝 0) :=
    by simpa using (heps_enn.add hentropy_term).add htail4
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbound_zero
    (Eventually.of_forall fun _ => zero_le) hupper

theorem weightedEmpiricalRelativeRadius_sq_le_empiricalSquareRadius
    {Ω : Type*} [MeasurableSpace Ω]
    (F : Set (Ω → ℝ)) (Φ : Ω → ℝ) (n : ℕ) (X : Fin n → Ω) :
    (ENNReal.ofReal (empiricalL2Seminorm n X Φ) *
      ENNReal.ofReal (empiricalRelativeRadiusReal F Φ n X)) ^ (2 : ℕ) ≤
      empiricalSquareRadius F n X := by
  calc
    _ ≤ (supNormOver F (empiricalL2Seminorm n X)) ^ (2 : ℕ) := by
      gcongr
      exact ofReal_empiricalL2Seminorm_mul_relativeRadiusReal_le_supNormOver F Φ n X
    _ = empiricalSquareRadius F n X := by
      unfold supNormOver empiricalSquareRadius
      rw [ENNReal.iSup₂_pow_of_ne_zero _ (by norm_num)]
      congr 1 with f; congr 1 with hf
      rw [abs_of_nonneg (empiricalL2Seminorm_nonneg n X f),
        ← ENNReal.ofReal_pow (empiricalL2Seminorm_nonneg n X f)]
      apply congrArg ENNReal.ofReal
      rw [empiricalL2Seminorm, Real.sq_sqrt]
      · apply congrArg (fun z : ℝ => (n : ℝ)⁻¹ * z)
        apply Finset.sum_congr rfl; intro i hi
        change |f (X i)| ^ 2 = f (X i) ^ 2
        rw [sq_abs]
      · unfold empiricalAvg; positivity

theorem lintegral_localized_weightedRelativeRadius_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Set (Ω → ℝ))
    (hDense : ∀ n, EmpProcPointwiseDense (F n) P) (hF_meas : ∀ n f, f ∈ F n → Measurable f)
    (Φ : ℕ → Ω → ℝ)
    (hΦ : ∀ n, IsEnvelope (F n) (Φ n))
    (hΦmeas : ∀ n, Measurable (Φ n))
    (hLin : ChangingLindeberg P Φ)
    (r : ℕ → ℝ)
    (hSquare : Tendsto (fun n =>
      ∫⁻ X : Fin n → Ω,
        empiricalSquareRadius
          (strictLocalizedDifferenceClass (F n) P (r n)) n X
        ∂Measure.pi (fun _ : Fin n => P)) atTop (𝓝 0)) :
    Tendsto (fun n =>
      ∫⁻ X : Fin n → Ω,
        ENNReal.ofReal
            (empiricalL2Seminorm n X (fun x => 2 * Φ n x)) *
          ENNReal.ofReal
            (empiricalRelativeRadiusReal
              (strictLocalizedDifferenceClass (F n) P (r n))
              (fun x => 2 * Φ n x) n X)
        ∂Measure.pi (fun _ : Fin n => P)) atTop (𝓝 0) := by
  let W : ∀ n, (Fin n → Ω) → ℝ≥0∞ := fun n X => ENNReal.ofReal
    (empiricalL2Seminorm n X (fun x => 2 * Φ n x)) *
      ENNReal.ofReal (empiricalRelativeRadiusReal
        (strictLocalizedDifferenceClass (F n) P (r n))
        (fun x => 2 * Φ n x) n X)
  let S : ℕ → ℝ≥0∞ := fun n => ∫⁻ X : Fin n → Ω,
      empiricalSquareRadius (strictLocalizedDifferenceClass (F n) P (r n)) n X
      ∂Measure.pi (fun _ : Fin n => P)
  have hW_meas (n : ℕ) : Measurable (W n) := by
    apply Measurable.fun_mul
    · exact (measurable_empiricalL2Seminorm
        (fun x => 2 * Φ n x) (measurable_const.mul (hΦmeas n)) n).ennreal_ofReal
    · exact (measurable_empiricalRelativeRadiusReal_strictLocalizedDifferenceClass
        (hDense n) (hF_meas n) (hΦ n)
        (hLin.envelope_memLp_two hΦmeas n) (hΦmeas n) (r n) n).ennreal_ofReal
  have hupper (n : ℕ) : (∫⁻ X, W n X ∂Measure.pi (fun _ : Fin n => P)) ≤
      (S n) ^ (1 / 2 : ℝ) := by
    calc
      (∫⁻ X, W n X ∂Measure.pi (fun _ : Fin n => P)) =
          ∫⁻ X, W n X * 1 ∂Measure.pi (fun _ : Fin n => P) := by simp
      _ ≤ (∫⁻ X, (W n X) ^ (2 : ℝ)
              ∂Measure.pi (fun _ : Fin n => P)) ^ (1 / 2 : ℝ) := by
        simpa using ENNReal.lintegral_mul_le_Lp_mul_Lq
          (f := W n) (g := fun _ => 1)
          (Measure.pi (fun _ : Fin n => P)) Real.HolderConjugate.two_two
          (hW_meas n).aemeasurable measurable_const.aemeasurable
      _ ≤ (S n) ^ (1 / 2 : ℝ) := by
        gcongr
        refine lintegral_mono fun X => ?_
        exact (ENNReal.rpow_natCast (W n X) 2).trans_le <| by simpa only [W] using
          (weightedEmpiricalRelativeRadius_sq_le_empiricalSquareRadius
            (strictLocalizedDifferenceClass (F n) P (r n)) (fun x => 2 * Φ n x) n X)
  have hsqrt : Tendsto (fun n => (S n) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    simpa [S] using!
      (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp hSquare
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsqrt (Eventually.of_forall fun _ => zero_le)
    (Eventually.of_forall hupper)

theorem random_radius_book_entropy_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Set (Ω → ℝ)) (Φ : ℕ → Ω → ℝ)
    (hΦmeas : ∀ n, Measurable (Φ n))
    (hLin : ChangingLindeberg P Φ) (r : ℕ → ℝ)
    (hWeighted : Tendsto (fun n =>
      ∫⁻ X : Fin n → Ω,
        ENNReal.ofReal
            (empiricalL2Seminorm n X (fun x => 2 * Φ n x)) *
          ENNReal.ofReal
            (empiricalRelativeRadiusReal
              (strictLocalizedDifferenceClass (F n) P (r n))
              (fun x => 2 * Φ n x) n X)
        ∂Measure.pi (fun _ : Fin n => P)) atTop (𝓝 0))
    (hJ : ∀ a : ℕ → ℝ, (∀ n, 0 < a n) → Antitone a →
      Tendsto a atTop (𝓝 0) →
      Tendsto (fun n =>
        bookUniformCoveringEntropyIntegral (a n) (F n) (Φ n))
        atTop (𝓝 0)) :
    Tendsto (fun n =>
      ∫⁻ X : Fin n → Ω,
        ENNReal.ofReal
            (empiricalL2Seminorm n X (fun x => 2 * Φ n x)) *
          bookUniformCoveringEntropyIntegral
            (empiricalRelativeRadiusReal
              (strictLocalizedDifferenceClass (F n) P (r n))
              (fun x => 2 * Φ n x) n X)
            (F n) (Φ n)
        ∂Measure.pi (fun _ : Fin n => P)) atTop (𝓝 0) := by
  let D : ∀ n, (Fin n → Ω) → ℝ≥0∞ := fun n X => ENNReal.ofReal
    (empiricalL2Seminorm n X (fun x => 2 * Φ n x))
  let R : ∀ n, (Fin n → Ω) → ℝ≥0∞ := fun n X => D n X *
    ENNReal.ofReal (empiricalRelativeRadiusReal
      (strictLocalizedDifferenceClass (F n) P (r n)) (fun x => 2 * Φ n x) n X)
  obtain ⟨B, hBtop, hB⟩ := hLin.1
  let C : ℝ≥0∞ := 2 * B ^ (1 / 2 : ℝ)
  have hCtop : C < ⊤ := ENNReal.mul_lt_top (by norm_num) <| ENNReal.rpow_lt_top_of_nonneg (by positivity) hBtop.ne
  have hDbdd (n : ℕ) : (∫⁻ X, D n X ∂Measure.pi (fun _ : Fin n => P)) ≤ C := by
    refine (lintegral_empiricalL2Seminorm_le_eLpNorm P (fun x => 2 * Φ n x)
      (measurable_const.mul (hΦmeas n)) n).trans ?_
    rw [show (fun x => 2 * Φ n x) = (2 : ℝ) • Φ n by ext; simp,
      eLpNorm_const_smul]
    have hbase : eLpNorm (Φ n) 2 P ≤ B ^ (1 / 2 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
      norm_num only [ENNReal.toReal_ofNat]
      rw [show (∫⁻ x, ‖Φ n x‖ₑ ^ (2 : ℝ) ∂P) =
          ∫⁻ x, ENNReal.ofReal ((Φ n x) ^ 2) ∂P by
        refine lintegral_congr fun x => ?_
        rw [ENNReal.rpow_two, Real.enorm_eq_ofReal_abs,
          ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]]
      exact ENNReal.rpow_le_rpow (hB n) (by norm_num)
    norm_num [Real.enorm_eq_ofReal_abs, C]; exact mul_le_mul_right hbase 2
  obtain ⟨a, ha, haanti, hazero, hRscale⟩ :=
    AsymptoticStatistics.ForMathlib.exists_pos_antitone_scale_tendsto_zero_div
      (fun n => ∫⁻ X, R n X ∂Measure.pi (fun _ : Fin n => P)) hWeighted
  let J : ℕ → ℝ≥0∞ := fun n => bookUniformCoveringEntropyIntegral (a n) (F n) (Φ n)
  have hJzero : Tendsto J atTop (𝓝 0) := hJ a ha haanti hazero
  have hupper : ∀ᶠ n in atTop,
      (∫⁻ X, D n X * bookUniformCoveringEntropyIntegral
        (empiricalRelativeRadiusReal (strictLocalizedDifferenceClass (F n) P (r n))
          (fun x => 2 * Φ n x) n X) (F n) (Φ n)
        ∂Measure.pi (fun _ : Fin n => P)) ≤
      J n * C + J n * ((∫⁻ X, R n X ∂Measure.pi (fun _ : Fin n => P)) /
        ENNReal.ofReal (a n)) := by
    filter_upwards [hJzero.eventually_ne ENNReal.zero_ne_top] with n hJn
    have ha0 : ENNReal.ofReal (a n) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (ha n)
    have hp (X : Fin n → Ω) : D n X * bookUniformCoveringEntropyIntegral
        (empiricalRelativeRadiusReal (strictLocalizedDifferenceClass (F n) P (r n))
          (fun x => 2 * Φ n x) n X) (F n) (Φ n) ≤
        D n X * J n + (R n X / ENNReal.ofReal (a n)) * J n := by
      rw [show J n = bookUniformCoveringEntropyIntegral (a n) (F n) (Φ n) by rfl]
      refine mul_le_mul_right (bookUniformCoveringEntropyIntegral_le_initial_add_ratio_mul_initial
        (F n) (Φ n) (ha n)) _ |>.trans ?_
      rw [mul_add]
      have hratio : D n X * ENNReal.ofReal
          (empiricalRelativeRadiusReal (strictLocalizedDifferenceClass (F n) P (r n))
            (fun x => 2 * Φ n x) n X / a n) ≤ R n X / ENNReal.ofReal (a n) := by
        rw [ENNReal.ofReal_div_of_pos (ha n), ← mul_div_assoc]
      exact add_le_add le_rfl <| by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hratio (zero_le)
    calc
      _ ≤ ∫⁻ X, D n X * J n + (R n X / ENNReal.ofReal (a n)) * J n
          ∂Measure.pi (fun _ : Fin n => P) := lintegral_mono hp
      _ = (∫⁻ X, D n X ∂Measure.pi (fun _ : Fin n => P)) * J n +
          ((∫⁻ X, R n X ∂Measure.pi (fun _ : Fin n => P)) /
            ENNReal.ofReal (a n)) * J n := by
        rw [lintegral_add_left' ((((measurable_empiricalL2Seminorm
          (fun x => 2 * Φ n x) (measurable_const.mul (hΦmeas n)) n).ennreal_ofReal).mul_const _).aemeasurable),
          lintegral_mul_const' _ _ hJn, lintegral_mul_const' _ _ hJn]
        simp only [div_eq_mul_inv]
        rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr ha0)]
      _ ≤ J n * C + J n * ((∫⁻ X, R n X ∂Measure.pi (fun _ : Fin n => P)) /
          ENNReal.ofReal (a n)) := by
        simpa only [mul_comm] using
          (add_le_add (mul_le_mul_right (hDbdd n) (J n)) le_rfl)
  have hz := (ENNReal.Tendsto.mul hJzero (Or.inr ENNReal.zero_ne_top) hRscale
    (Or.inr ENNReal.zero_ne_top)).add (ENNReal.Tendsto.mul_const hJzero (Or.inr hCtop.ne))
  simpa only [D] using tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (by simpa [add_comm] using hz)
    (Eventually.of_forall fun _ => zero_le) hupper
end AsymptoticStatistics.EmpiricalProcess
