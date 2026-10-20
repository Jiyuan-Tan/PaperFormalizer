module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ChangingClassUniformRadius
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LocalizedEmpiricalRadiusAsymptotics

@[expose] public section

/-! # Local oscillation for changing classes -/

namespace AsymptoticStatistics.EmpiricalProcess

open Filter MeasureTheory Topology
open scoped ENNReal

set_option linter.style.longLine false

/-- The repaired uniform-covering route makes every population-`L²`-null
changing local class asymptotically negligible in outer expectation. -/
theorem changingLocalOscillation_tendsto_zero
    {Ω T Ξ : Type*} [MeasurableSpace Ω] [PseudoMetricSpace T]
    [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (X : ℕ → Ξ → Ω) (hX_meas : ∀ i, Measurable (X i))
    (hX_iindep : ProbabilityTheory.iIndepFun X μ)
    (hX_idem : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hX_law : μ.map (X 0) = P)
    (f : ℕ → T → Ω → ℝ) (Φ : ℕ → Ω → ℝ)
    (hDense : ∀ n, EmpProcPointwiseDense (Set.range (f n)) P)
    (hf : ∀ n t, Measurable (f n t))
    (hΦ : ChangingEnvelope f Φ)
    (hΦmeas : ∀ n, Measurable (Φ n))
    (hLin : ChangingLindeberg P Φ)
    (hJ : ∀ a : ℕ → ℝ, (∀ n, 0 < a n) → Antitone a →
      Tendsto a atTop (𝓝 0) →
      Tendsto (fun n =>
        bookUniformCoveringEntropyIntegral (a n) (Set.range (f n)) (Φ n))
        atTop (𝓝 0))
    (δ : ℕ → ℝ)
    (hL2 : Tendsto (fun n => populationSquareRadius P
      (changingLocalDifferenceClass f n (δ n))) atTop (𝓝 0)) :
    Tendsto (fun n => outerExpectation μ (fun ξ =>
      supNormOver (changingLocalDifferenceClass f n (δ n))
        (empiricalProcess P n (fun i : Fin n => X i.val ξ))))
      atTop (𝓝 0) := by
  classical
  rcases isEmpty_or_nonempty T with hT | hT
  · letI : IsEmpty T := hT
    have hempty (n : ℕ) : changingLocalDifferenceClass f n (δ n) = ∅ := by
      ext g
      constructor
      · rintro ⟨s, t, -, rfl⟩
        exact isEmptyElim s
      · simp
    have hz : (fun n => outerExpectation μ (fun ξ =>
        supNormOver (changingLocalDifferenceClass f n (δ n))
          (empiricalProcess P n (fun i : Fin n => X i.val ξ)))) =
        fun _ : ℕ => (0 : ℝ≥0∞) := by
      funext n
      rw [hempty]
      simp only [supNormOver, Set.mem_empty_iff_false, iSup_false, iSup_bot]
      change outerExpectation μ (fun _ : Ξ => 0) = 0
      rw [outerExpectation_eq_lintegral measurable_const]
      simp
    rw [hz]
    exact tendsto_const_nhds
  · letI : Nonempty T := hT
    have hFmeas : ∀ n g, g ∈ Set.range (f n) → Measurable g := by
      rintro n g ⟨t, rfl⟩
      exact hf n t
    have hFenv : ∀ n, IsEnvelope (Set.range (f n)) (Φ n) := by
      rintro n g ⟨t, rfl⟩ x
      exact hΦ n t x
    let b : ℕ → ℝ≥0∞ := fun n =>
      populationSquareRadius P (changingLocalDifferenceClass f n (δ n))
    obtain ⟨ε, hεpos, hεanti, hεzero, htail, hratio⟩ :=
      hLin.exists_pos_antitone_tail_scale_div b (by simpa [b] using hL2)
    have hb_lt : ∀ᶠ n in atTop, b n < ENNReal.ofReal (ε n) := by
      filter_upwards [((tendsto_order.1 hratio).2 1 (by norm_num))] with n hn
      have hε0 : ENNReal.ofReal (ε n) ≠ 0 :=
        ENNReal.ofReal_ne_zero_iff.mpr (hεpos n)
      have hεtop : ENNReal.ofReal (ε n) ≠ ⊤ := ENNReal.ofReal_ne_top
      simpa using (ENNReal.div_lt_iff (Or.inl hε0) (Or.inl hεtop)).1 hn
    have hSquare := lintegral_localized_empiricalSquareRadius_tendsto_zero
      P (fun n => Set.range (f n)) hDense hFmeas Φ hFenv hΦmeas hLin hJ
      ε hεpos hεanti hεzero (by simpa [changingLindebergTail] using htail)
    have hWeighted := lintegral_localized_weightedRelativeRadius_tendsto_zero
      P (fun n => Set.range (f n)) hDense hFmeas Φ hFenv hΦmeas hLin
      (fun n => Real.sqrt (ε n)) hSquare
    let R : ℕ → ℝ≥0∞ := fun n =>
      ∫⁻ Z : Fin n → Ω,
        ENNReal.ofReal (empiricalL2Seminorm n Z (fun x => 2 * Φ n x)) *
          bookUniformCoveringEntropyIntegral
            (empiricalRelativeRadiusReal
              (strictLocalizedDifferenceClass (Set.range (f n)) P
                (Real.sqrt (ε n))) (fun x => 2 * Φ n x) n Z)
            (Set.range (f n)) (Φ n) ∂Measure.pi (fun _ : Fin n => P)
    have hRzero : Tendsto R atTop (𝓝 0) := by
      simpa [R] using random_radius_book_entropy_tendsto_zero P
        (fun n => Set.range (f n)) Φ hΦmeas hLin
        (fun n => Real.sqrt (ε n)) hWeighted hJ
    let C : ℝ≥0∞ := 156 * ENNReal.ofReal (Real.sqrt 2)
    have hCtop : C < ⊤ :=
      ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top
    have hupper : ∀ᶠ n in atTop,
        outerExpectation μ (fun ξ =>
          supNormOver (changingLocalDifferenceClass f n (δ n))
            (empiricalProcess P n (fun i : Fin n => X i.val ξ))) ≤ C * R n := by
      filter_upwards [hb_lt] with n hn
      let G := strictLocalizedDifferenceClass (Set.range (f n)) P (Real.sqrt (ε n))
      let Ψ := fun x => 2 * Φ n x
      let Y : Ξ → (Fin n → Ω) := fun ξ i => X i.val ξ
      let D : (Fin n → Ω) → ℝ≥0∞ := fun Z =>
        ENNReal.ofReal (empiricalL2Seminorm n Z Ψ)
      let θ : (Fin n → Ω) → ℝ := fun Z => empiricalRelativeRadiusReal G Ψ n Z
      let J₀ : (Fin n → Ω) → ℝ≥0∞ := fun Z =>
        bookUniformCoveringEntropyIntegral (θ Z) (Set.range (f n)) (Φ n)
      have hsub : changingLocalDifferenceClass f n (δ n) ⊆ G :=
        changingLocalDifferenceClass_subset_strictLocalizedDifferenceClass_of_populationSquareRadius_lt
          f P n (δ n) (hεpos n) (by simpa [b] using hn)
      have hGdense : EmpProcPointwiseDense G P := by
        exact EmpProcPointwiseDense_strictLocalizedDifferenceClass
          (hDense n) (hFmeas n) (hFenv n)
          (hLin.envelope_memLp_two hΦmeas n) (Real.sqrt (ε n))
      have hGmeas : ∀ g ∈ G, Measurable g := by
        rintro g ⟨u, hu, v, hv, rfl, -⟩
        exact (hFmeas n u hu).sub (hFmeas n v hv)
      have hGenv : IsEnvelope G Ψ := by
        exact (isEnvelope_differenceClass_two (hFenv n)).mono
          (strictLocalizedDifferenceClass_subset_differenceClass
            (Set.range (f n)) P (Real.sqrt (ε n)))
      have hΨmeas : Measurable Ψ := measurable_const.mul (hΦmeas n)
      have hYmeas : Measurable Y := measurable_pi_lambda _ fun i => hX_meas i.val
      have hYmap : μ.map Y = Measure.pi (fun _ : Fin n => P) :=
        AsymptoticStatistics.map_fin_restrict_eq_pi_of_iid
          P μ X hX_meas hX_iindep hX_idem hX_law n
      have hθmeas : Measurable θ := by
        exact measurable_empiricalRelativeRadiusReal_strictLocalizedDifferenceClass
          (hDense n) (hFmeas n) (hFenv n)
          (hLin.envelope_memLp_two hΦmeas n) (hΦmeas n)
          (Real.sqrt (ε n)) n
      have hJmeas : Measurable J₀ :=
        (show Monotone (fun a : ℝ =>
            bookUniformCoveringEntropyIntegral a (Set.range (f n)) (Φ n)) from
          fun _ _ h => bookUniformCoveringEntropyIntegral_mono_delta _ _ h).measurable.comp hθmeas
      have hHmeas : Measurable (fun Z => D Z * J₀ Z) :=
        ((measurable_empiricalL2Seminorm Ψ hΨmeas n).ennreal_ofReal).mul hJmeas
      have hmap : (∫⁻ ξ, D (Y ξ) * J₀ (Y ξ) ∂μ) =
          ∫⁻ Z, D Z * J₀ Z ∂Measure.pi (fun _ : Fin n => P) := by
        rw [← lintegral_map' hHmeas.aemeasurable hYmeas.aemeasurable, hYmap]
      have hentropy (Z : Fin n → Ω) :
          bookUniformCoveringEntropyIntegral (θ Z) G Ψ ≤
            ENNReal.ofReal (Real.sqrt 2) * J₀ Z := by
        exact bookUniformCoveringEntropyIntegral_strictLocalizedDifferenceClass_le
          P (Set.range (f n)) (hFmeas n) (Φ n) (Real.sqrt (ε n)) (θ Z)
      have hlin : (∫⁻ ξ, D (Y ξ) *
          bookUniformCoveringEntropyIntegral (θ (Y ξ)) G Ψ ∂μ) ≤
          ENNReal.ofReal (Real.sqrt 2) * ∫⁻ ξ, D (Y ξ) * J₀ (Y ξ) ∂μ := by
        calc
          _ ≤ ∫⁻ ξ, ENNReal.ofReal (Real.sqrt 2) * (D (Y ξ) * J₀ (Y ξ)) ∂μ := by
            refine lintegral_mono fun ξ => ?_
            calc
              D (Y ξ) * bookUniformCoveringEntropyIntegral (θ (Y ξ)) G Ψ ≤
                  D (Y ξ) * (ENNReal.ofReal (Real.sqrt 2) * J₀ (Y ξ)) :=
                by simpa [mul_comm] using
                  mul_le_mul_right (hentropy (Y ξ)) (D (Y ξ))
              _ = _ := by ac_rfl
          _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      calc
        _ ≤ outerExpectation μ (fun ξ => supNormOver G
            (empiricalProcess P n (fun i : Fin n => X i.val ξ))) :=
          outerExpectation_mono fun ξ => supNormOver_mono hsub _
        _ ≤ 156 * ∫⁻ ξ, D (Y ξ) *
            bookUniformCoveringEntropyIntegral (θ (Y ξ)) G Ψ ∂μ := by
          simpa [G, Ψ, Y, D, θ] using
            outer_empiricalProcessSup_le_expected_bookUniformEntropy_of_zero_mem
              P μ X hX_meas hX_iindep hX_idem hX_law G
              (zero_mem_strictLocalizedDifferenceClass (Set.range_nonempty _)
                (Real.sqrt_pos.2 (hεpos n))) hGdense hGmeas Ψ hGenv hΨmeas n
        _ ≤ C * (∫⁻ ξ, D (Y ξ) * J₀ (Y ξ) ∂μ) := by
          simpa [C, mul_comm, mul_left_comm, mul_assoc] using
            mul_le_mul_right hlin 156
        _ = C * R n := by
          rw [hmap]
    have hCR : Tendsto (fun n => C * R n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul hRzero (Or.inr hCtop.ne)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hCR (Eventually.of_forall fun _ => zero_le) hupper

end AsymptoticStatistics.EmpiricalProcess
