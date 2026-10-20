module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.EmpiricalSquareRadius
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringBookDifference
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringRademacherFiniteChaining

@[expose] public section

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory
open scoped ENNReal

noncomputable section

theorem populationSquareRadius_strictLocalizedDifferenceClass_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Set (Ω → ℝ)) (r : ℝ) :
    populationSquareRadius P
        (strictLocalizedDifferenceClass F P r) ≤
      ENNReal.ofReal (r ^ 2) := by
  unfold populationSquareRadius
  refine iSup_le fun h => iSup_le fun hh => ?_
  rcases hh with ⟨f, hf, g, hg, heq, hr⟩
  have hr_pos : 0 < r := ENNReal.ofReal_pos.mp ((zero_le).trans_lt hr)
  have hnorm_sq :
      eLpNorm h 2 P ^ (2 : ℕ) =
        ∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂P := by
    calc
      eLpNorm h 2 P ^ (2 : ℕ) = eLpNorm h 2 P ^ (2 : ℝ) :=
        (ENNReal.rpow_natCast _ 2).symm
      _ = ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂P := by
        simpa using eLpNorm_nnreal_pow_eq_lintegral
          (f := h) (μ := P) (p := (2 : NNReal))
          (show (2 : NNReal) ≠ 0 by norm_num)
      _ = ∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂P := by
        refine lintegral_congr fun x => ?_
        calc
          ‖h x‖ₑ ^ (2 : ℝ) = ‖h x‖ₑ ^ (2 : ℕ) :=
            ENNReal.rpow_natCast _ 2
          _ = ENNReal.ofReal (h x ^ 2) := by
            rw [Real.enorm_eq_ofReal_abs,
              ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  calc
    (∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂P) =
        eLpNorm h 2 P ^ (2 : ℕ) := hnorm_sq.symm
    _ ≤ ENNReal.ofReal r ^ (2 : ℕ) := by gcongr
    _ = ENNReal.ofReal (r ^ 2) :=
      (ENNReal.ofReal_pow hr_pos.le 2).symm

theorem lintegral_canonical_empiricalSquareRadius_strictLocalizedDifferenceClass_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set (Ω → ℝ))
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ) (hΦ : IsEnvelope F Φ)
    (hΦ_memLp : MemLp Φ 2 P)
    (hΦ_meas : Measurable Φ)
    (r K : ℝ) (hK : 0 ≤ K) (n : ℕ) :
    (∫⁻ X : Fin n → Ω,
      empiricalSquareRadius
        (strictLocalizedDifferenceClass F P r) n X
      ∂Measure.pi (fun _ : Fin n => P)) ≤
      ENNReal.ofReal (r ^ 2) +
        ENNReal.ofReal (8 * K * (Real.sqrt n)⁻¹) *
          ∫⁻ X : Fin n → Ω,
            conditionalRademacherSup
              (strictLocalizedDifferenceClass F P r) n X
            ∂Measure.pi (fun _ : Fin n => P) +
        ∫⁻ x, ENNReal.ofReal
          (squareTailEnvelope K (fun y => 2 * Φ y) x) ∂P := by
  have hLocalDense :
      EmpProcPointwiseDense (strictLocalizedDifferenceClass F P r) P :=
    EmpProcPointwiseDense_strictLocalizedDifferenceClass
      hDense hF_meas hΦ hΦ_memLp r
  have hLocalMeas :
      ∀ h ∈ strictLocalizedDifferenceClass F P r, Measurable h := by
    rintro h ⟨f, hf, g, hg, rfl, -⟩
    exact (hF_meas f hf).sub (hF_meas g hg)
  have hLocalEnvelope :
      IsEnvelope (strictLocalizedDifferenceClass F P r)
        (fun y => 2 * Φ y) :=
    (isEnvelope_differenceClass_two hΦ).mono
      (strictLocalizedDifferenceClass_subset_differenceClass F P r)
  have hTwoPhiMeas : Measurable (fun y => 2 * Φ y) :=
    measurable_const.mul hΦ_meas
  calc
    (∫⁻ X : Fin n → Ω,
        empiricalSquareRadius
          (strictLocalizedDifferenceClass F P r) n X
        ∂Measure.pi (fun _ : Fin n => P)) ≤
        populationSquareRadius P (strictLocalizedDifferenceClass F P r) +
          ENNReal.ofReal (8 * K * (Real.sqrt n)⁻¹) *
            ∫⁻ X : Fin n → Ω,
              conditionalRademacherSup
                (strictLocalizedDifferenceClass F P r) n X
              ∂Measure.pi (fun _ : Fin n => P) +
          ∫⁻ x, ENNReal.ofReal
            (squareTailEnvelope K (fun y => 2 * Φ y) x) ∂P :=
      lintegral_canonical_empiricalSquareRadius_le P
        (strictLocalizedDifferenceClass F P r)
        hLocalDense hLocalMeas (fun y => 2 * Φ y) hLocalEnvelope
        hTwoPhiMeas K hK n
    _ ≤ ENNReal.ofReal (r ^ 2) +
          ENNReal.ofReal (8 * K * (Real.sqrt n)⁻¹) *
            ∫⁻ X : Fin n → Ω,
              conditionalRademacherSup
                (strictLocalizedDifferenceClass F P r) n X
              ∂Measure.pi (fun _ : Fin n => P) +
          ∫⁻ x, ENNReal.ofReal
            (squareTailEnvelope K (fun y => 2 * Φ y) x) ∂P := by
      gcongr
      exact populationSquareRadius_strictLocalizedDifferenceClass_le P F r

theorem conditionalRademacherSup_strictLocalizedDifferenceClass_le_bookEntropy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Set (Ω → ℝ))
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ) (hΦ : IsEnvelope F Φ)
    (hΦ_meas : Measurable Φ)
    (r : ℝ) (n : ℕ) (X : Fin n → Ω) :
    conditionalRademacherSup
        (strictLocalizedDifferenceClass F P r) n X ≤
      78 *
        ENNReal.ofReal
          (empiricalL2Seminorm n X (fun x => 2 * Φ x)) *
        bookUniformCoveringEntropyIntegral
          (empiricalRelativeRadiusReal
            (strictLocalizedDifferenceClass F P r)
            (fun x => 2 * Φ x) n X)
          (strictLocalizedDifferenceClass F P r)
          (fun x => 2 * Φ x) := by
  let G := strictLocalizedDifferenceClass F P r
  have hGempty_of_Fempty (hFempty : F = ∅) :
      strictLocalizedDifferenceClass F P r = ∅ := by
    subst F
    ext h
    simp [strictLocalizedDifferenceClass]
  have hGempty_of_nonpos (hr : ¬0 < r) :
      strictLocalizedDifferenceClass F P r = ∅ := by
    have hr_nonpos : r ≤ 0 := le_of_not_gt hr
    ext h
    simp only [strictLocalizedDifferenceClass, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨f, hf, g, hg, heq, hnorm⟩
    rw [ENNReal.ofReal_eq_zero.mpr hr_nonpos] at hnorm
    exact (not_lt_of_ge (zero_le)) hnorm
  rcases F.eq_empty_or_nonempty with hFempty | hFnonempty
  · rw [hGempty_of_Fempty hFempty]
    simp only [conditionalRademacherSup_empty, zero_le]
  by_cases hr : 0 < r
  · have hzero : (fun _ : Ω => 0) ∈ G := by
      exact zero_mem_strictLocalizedDifferenceClass hFnonempty hr
    have hGmeas : ∀ h ∈ G, Measurable h := by
      rintro h ⟨f, hf, g, hg, rfl, -⟩
      exact (hF_meas f hf).sub (hF_meas g hg)
    have hGenv : IsEnvelope G (fun x => 2 * Φ x) :=
      (isEnvelope_differenceClass_two hΦ).mono
        (strictLocalizedDifferenceClass_subset_differenceClass F P r)
    have hTwoPhiMeas : Measurable (fun x => 2 * Φ x) :=
      measurable_const.mul hΦ_meas
    calc
      conditionalRademacherSup G n X ≤
          26 * ENNReal.ofReal
            (empiricalL2Seminorm n X (fun x => 2 * Φ x)) *
            uniformCoveringEntropyIntegral
              (empiricalRelativeRadiusReal G (fun x => 2 * Φ x) n X)
              G (fun x => 2 * Φ x) :=
        conditionalRademacherSup_le_uniformCoveringEntropyIntegral
          G (fun x => 2 * Φ x) n X hGenv
      _ ≤ 26 * ENNReal.ofReal
            (empiricalL2Seminorm n X (fun x => 2 * Φ x)) *
            (3 * bookUniformCoveringEntropyIntegral
              (empiricalRelativeRadiusReal G (fun x => 2 * Φ x) n X)
              G (fun x => 2 * Φ x)) := by
        gcongr
        exact empiricalUniformEntropyIntegral_le_three_mul_book
          G hzero hGmeas (fun x => 2 * Φ x) hTwoPhiMeas n X
      _ = 78 * ENNReal.ofReal
            (empiricalL2Seminorm n X (fun x => 2 * Φ x)) *
            bookUniformCoveringEntropyIntegral
              (empiricalRelativeRadiusReal G (fun x => 2 * Φ x) n X)
              G (fun x => 2 * Φ x) := by ring
  · rw [hGempty_of_nonpos hr]
    simp only [conditionalRademacherSup_empty, zero_le]

theorem bookUniformCoveringEntropyIntegral_strictLocalizedDifferenceClass_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Set (Ω → ℝ))
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ)
    (r δ : ℝ) :
    bookUniformCoveringEntropyIntegral δ
        (strictLocalizedDifferenceClass F P r)
        (fun x => 2 * Φ x) ≤
      ENNReal.ofReal (Real.sqrt 2) *
        bookUniformCoveringEntropyIntegral δ F Φ := by
  exact
    (bookUniformCoveringEntropyIntegral_mono_class
      (strictLocalizedDifferenceClass_subset_differenceClass F P r)
      (fun x => 2 * Φ x) δ).trans
    (bookUniformCoveringEntropyIntegral_differenceClass_le_sqrtTwo_mul
      F hF_meas Φ δ)

theorem conditionalRademacherSup_strictLocalizedDifferenceClass_le_rowBookEntropy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Set (Ω → ℝ))
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ) (hΦ : IsEnvelope F Φ)
    (hΦ_meas : Measurable Φ)
    (r : ℝ) (n : ℕ) (X : Fin n → Ω) :
    conditionalRademacherSup
        (strictLocalizedDifferenceClass F P r) n X ≤
      (78 * ENNReal.ofReal (Real.sqrt 2)) *
        (ENNReal.ofReal
            (empiricalL2Seminorm n X (fun x => 2 * Φ x)) *
          bookUniformCoveringEntropyIntegral
            (empiricalRelativeRadiusReal
              (strictLocalizedDifferenceClass F P r)
              (fun x => 2 * Φ x) n X)
            F Φ) := by
  refine
    (conditionalRademacherSup_strictLocalizedDifferenceClass_le_bookEntropy
      P F hF_meas Φ hΦ hΦ_meas r n X).trans ?_
  calc
    78 * ENNReal.ofReal
          (empiricalL2Seminorm n X (fun x => 2 * Φ x)) *
        bookUniformCoveringEntropyIntegral
          (empiricalRelativeRadiusReal
            (strictLocalizedDifferenceClass F P r)
            (fun x => 2 * Φ x) n X)
          (strictLocalizedDifferenceClass F P r)
          (fun x => 2 * Φ x) ≤
      78 * ENNReal.ofReal
          (empiricalL2Seminorm n X (fun x => 2 * Φ x)) *
        (ENNReal.ofReal (Real.sqrt 2) *
          bookUniformCoveringEntropyIntegral
            (empiricalRelativeRadiusReal
              (strictLocalizedDifferenceClass F P r)
              (fun x => 2 * Φ x) n X)
            F Φ) := by
      gcongr
      exact bookUniformCoveringEntropyIntegral_strictLocalizedDifferenceClass_le
        P F hF_meas Φ r
          (empiricalRelativeRadiusReal
            (strictLocalizedDifferenceClass F P r)
            (fun x => 2 * Φ x) n X)
    _ = (78 * ENNReal.ofReal (Real.sqrt 2)) *
          (ENNReal.ofReal
              (empiricalL2Seminorm n X (fun x => 2 * Φ x)) *
            bookUniformCoveringEntropyIntegral
              (empiricalRelativeRadiusReal
                (strictLocalizedDifferenceClass F P r)
                (fun x => 2 * Φ x) n X)
              F Φ) := by ring

theorem lintegral_canonical_empiricalSquareRadius_strictLocalizedDifferenceClass_le_rowBookEntropy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set (Ω → ℝ))
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (Φ : Ω → ℝ) (hΦ : IsEnvelope F Φ)
    (hΦ_memLp : MemLp Φ 2 P)
    (hΦ_meas : Measurable Φ)
    (r K : ℝ) (hK : 0 ≤ K) (n : ℕ) :
    (∫⁻ X : Fin n → Ω,
      empiricalSquareRadius
        (strictLocalizedDifferenceClass F P r) n X
      ∂Measure.pi (fun _ : Fin n => P)) ≤
      ENNReal.ofReal (r ^ 2) +
        (ENNReal.ofReal (8 * K * (Real.sqrt n)⁻¹) *
          (78 * ENNReal.ofReal (Real.sqrt 2))) *
          (∫⁻ X : Fin n → Ω,
            ENNReal.ofReal
                (empiricalL2Seminorm n X (fun x => 2 * Φ x)) *
              bookUniformCoveringEntropyIntegral
                (empiricalRelativeRadiusReal
                  (strictLocalizedDifferenceClass F P r)
                  (fun x => 2 * Φ x) n X)
                F Φ
            ∂Measure.pi (fun _ : Fin n => P)) +
        4 * ∫⁻ x in {x | K < 2 * |Φ x|},
          ENNReal.ofReal (Φ x ^ 2) ∂P := by
  let G := strictLocalizedDifferenceClass F P r
  let C : ℝ≥0∞ := 78 * ENNReal.ofReal (Real.sqrt 2)
  let H : (Fin n → Ω) → ℝ≥0∞ := fun X =>
    ENNReal.ofReal (empiricalL2Seminorm n X (fun x => 2 * Φ x)) *
      bookUniformCoveringEntropyIntegral
        (empiricalRelativeRadiusReal G (fun x => 2 * Φ x) n X) F Φ
  have hC_ne_top : C ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  have hRad :
      (∫⁻ X : Fin n → Ω, conditionalRademacherSup G n X
        ∂Measure.pi (fun _ : Fin n => P)) ≤
        C * ∫⁻ X : Fin n → Ω, H X
          ∂Measure.pi (fun _ : Fin n => P) := by
    calc
      (∫⁻ X : Fin n → Ω, conditionalRademacherSup G n X
          ∂Measure.pi (fun _ : Fin n => P)) ≤
          ∫⁻ X : Fin n → Ω, C * H X
            ∂Measure.pi (fun _ : Fin n => P) := by
        refine lintegral_mono fun X => ?_
        simpa only [C, H, G] using
          conditionalRademacherSup_strictLocalizedDifferenceClass_le_rowBookEntropy
            P F hF_meas Φ hΦ hΦ_meas r n X
      _ = C * ∫⁻ X : Fin n → Ω, H X
            ∂Measure.pi (fun _ : Fin n => P) := by
        rw [lintegral_const_mul' C H hC_ne_top]
  calc
    (∫⁻ X : Fin n → Ω,
        empiricalSquareRadius
          (strictLocalizedDifferenceClass F P r) n X
        ∂Measure.pi (fun _ : Fin n => P)) ≤
        ENNReal.ofReal (r ^ 2) +
          ENNReal.ofReal (8 * K * (Real.sqrt n)⁻¹) *
            (∫⁻ X : Fin n → Ω, conditionalRademacherSup G n X
              ∂Measure.pi (fun _ : Fin n => P)) +
          ∫⁻ x, ENNReal.ofReal
            (squareTailEnvelope K (fun y => 2 * Φ y) x) ∂P := by
      simpa only [G] using
        lintegral_canonical_empiricalSquareRadius_strictLocalizedDifferenceClass_le
          P F hDense hF_meas Φ hΦ hΦ_memLp hΦ_meas r K hK n
    _ ≤ ENNReal.ofReal (r ^ 2) +
          ENNReal.ofReal (8 * K * (Real.sqrt n)⁻¹) *
            (C * ∫⁻ X : Fin n → Ω, H X
              ∂Measure.pi (fun _ : Fin n => P)) +
          ∫⁻ x, ENNReal.ofReal
            (squareTailEnvelope K (fun y => 2 * Φ y) x) ∂P := by
      gcongr
    _ = ENNReal.ofReal (r ^ 2) +
          (ENNReal.ofReal (8 * K * (Real.sqrt n)⁻¹) *
            (78 * ENNReal.ofReal (Real.sqrt 2))) *
            (∫⁻ X : Fin n → Ω,
              ENNReal.ofReal
                  (empiricalL2Seminorm n X (fun x => 2 * Φ x)) *
                bookUniformCoveringEntropyIntegral
                  (empiricalRelativeRadiusReal
                    (strictLocalizedDifferenceClass F P r)
                    (fun x => 2 * Φ x) n X)
                  F Φ
              ∂Measure.pi (fun _ : Fin n => P)) +
          4 * ∫⁻ x in {x | K < 2 * |Φ x|},
            ENNReal.ofReal (Φ x ^ 2) ∂P := by
      rw [lintegral_squareTailEnvelope_two_mul_eq P K hK Φ hΦ_meas]
      simp only [C, H, G]
      ring

end

end AsymptoticStatistics.EmpiricalProcess
