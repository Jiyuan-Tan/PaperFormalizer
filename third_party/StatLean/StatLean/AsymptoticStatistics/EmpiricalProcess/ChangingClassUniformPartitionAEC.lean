module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ChangingClassUniformAEC
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ChangingClassUniformProcess
public import StatLean.AsymptoticStatistics.ForMathlib.AntitoneDiagonal

@[expose] public section

/-! # Finite-partition equicontinuity for changing classes -/

namespace AsymptoticStatistics.EmpiricalProcess

open Filter MeasureTheory Topology
open scoped ENNReal

/-- Vanishing local oscillations along every positive antitone null diagonal
give finite-partition asymptotic equicontinuity on a totally bounded index
space. -/
theorem partitionAEC_of_localOscillation
    {Ω T Ξ : Type*} [MeasurableSpace Ω] [PseudoMetricSpace T]
    [MeasurableSpace Ξ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure Ξ)
    (X : ℕ → Ξ → Ω)
    (f : ℕ → T → Ω → ℝ) (Φ : ℕ → Ω → ℝ)
    (hΦ : ChangingEnvelope f Φ) (hLin : ChangingLindeberg P Φ)
    (hf : ∀ n t, Measurable (f n t))
    (hΦmeas : ∀ n, Measurable (Φ n))
    (hTB : TotallyBounded (Set.univ : Set T))
    (hLoc : ∀ δ : ℕ → ℝ, (∀ n, 0 < δ n) → Antitone δ →
      Tendsto δ atTop (𝓝 0) →
      Tendsto (fun n => outerExpectation μ (fun ξ =>
        supNormOver (changingLocalDifferenceClass f n (δ n))
          (empiricalProcess P n (fun i : Fin n => X i.val ξ))))
        atTop (𝓝 0)) :
    PartitionAEC (fun _ : ℕ => μ)
      (fun n ξ => changingClassEmpiricalProcessLinf
        P f Φ hΦ hLin hf hΦmeas n (fun i : Fin n => X i.val ξ)) := by
  intro ε η hε hη
  let L : ℕ → ℝ → ℝ≥0∞ := fun n r => outerExpectation μ (fun ξ =>
    supNormOver (changingLocalDifferenceClass f n r)
      (empiricalProcess P n (fun i : Fin n => X i.val ξ)))
  have hL : ∀ δ : ℕ → ℝ, (∀ n, 0 < δ n) → Antitone δ →
      Tendsto δ atTop (𝓝 0) → Tendsto (fun n => L n (δ n)) atTop (𝓝 0) := by
    intro δ hδpos hδanti hδzero
    simpa only [L] using hLoc δ hδpos hδanti hδzero
  have hε0 : ENNReal.ofReal ε ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hε
  have hη0 : ENNReal.ofReal η ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hη
  have hηtop : ENNReal.ofReal η ≠ ⊤ := ENNReal.ofReal_ne_top
  have hc : 0 < ENNReal.ofReal ε * ENNReal.ofReal η :=
    ENNReal.mul_pos hε0 hη0
  obtain ⟨r, hr, hsmall⟩ :=
    AsymptoticStatistics.ForMathlib.exists_pos_fixed_scale_eventually_lt_of_antitone_diagonal
      L hL hc
  obtain ⟨a, ha⟩ := exists_finiteApproximation_dist_lt hTB hr
  refine ⟨a, ?_⟩
  filter_upwards [hsmall] with n hn
  let Z : Ξ → ℝ≥0∞ := fun ξ =>
    supNormOver (changingLocalDifferenceClass f n r)
      (empiricalProcess P n (fun i : Fin n => X i.val ξ))
  have hsubset : {ξ | η < ‖
      changingClassEmpiricalProcessLinf
          P f Φ hΦ hLin hf hΦmeas n (fun i : Fin n => X i.val ξ) -
        a.project (changingClassEmpiricalProcessLinf
          P f Φ hΦ hLin hf hΦmeas n (fun i : Fin n => X i.val ξ))‖} ⊆
      {ξ | ENNReal.ofReal η ≤ Z ξ} := by
    intro ξ hξ
    have hnorm : 0 < ‖
        changingClassEmpiricalProcessLinf
            P f Φ hΦ hLin hf hΦmeas n (fun i : Fin n => X i.val ξ) -
          a.project (changingClassEmpiricalProcessLinf
            P f Φ hΦ hLin hf hΦmeas n (fun i : Fin n => X i.val ξ))‖ :=
      hη.trans hξ
    have hηnorm : ENNReal.ofReal η < ENNReal.ofReal ‖
        changingClassEmpiricalProcessLinf
            P f Φ hΦ hLin hf hΦmeas n (fun i : Fin n => X i.val ξ) -
          a.project (changingClassEmpiricalProcessLinf
            P f Φ hΦ hLin hf hΦmeas n (fun i : Fin n => X i.val ξ))‖ :=
      (ENNReal.ofReal_lt_ofReal_iff hnorm).2 hξ
    exact hηnorm.le.trans (by
      simpa only [Z] using ofReal_norm_changingClass_sub_project_le
        P f Φ hΦ hLin hf hΦmeas a ha n (fun i : Fin n => X i.val ξ))
  calc
    μ.outerMeasureStar {ξ | η < ‖
        changingClassEmpiricalProcessLinf
            P f Φ hΦ hLin hf hΦmeas n (fun i : Fin n => X i.val ξ) -
          a.project (changingClassEmpiricalProcessLinf
            P f Φ hΦ hLin hf hΦmeas n (fun i : Fin n => X i.val ξ))‖}
        ≤ μ.outerMeasureStar {ξ | ENNReal.ofReal η ≤ Z ξ} := by
      rw [Measure.outerMeasureStar, Measure.outerMeasureStar]
      apply outerExpectation_mono
      exact Set.indicator_le_indicator_of_subset hsubset (fun _ => zero_le)
    _ ≤ outerExpectation μ Z / ENNReal.ofReal η :=
      outerExpectation_markov (ENNReal.ofReal η) hη0 hηtop
    _ < ENNReal.ofReal ε := by
      apply (ENNReal.div_lt_iff (Or.inl hη0) (Or.inl hηtop)).2
      simpa only [L, Z] using hn

/-- The repaired uniform-covering local-oscillation theorem supplies the
finite-partition criterion for the changing empirical-process paths. -/
theorem partitionAEC_of_uniformCovering
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
    (hTB : TotallyBounded (Set.univ : Set T))
    (hL2 : ∀ δ : ℕ → ℝ, (∀ n, 0 < δ n) → Antitone δ →
      Tendsto δ atTop (𝓝 0) →
      Tendsto (fun n => populationSquareRadius P
        (changingLocalDifferenceClass f n (δ n))) atTop (𝓝 0))
    (hJ : ∀ a : ℕ → ℝ, (∀ n, 0 < a n) → Antitone a →
      Tendsto a atTop (𝓝 0) →
      Tendsto (fun n =>
        bookUniformCoveringEntropyIntegral
          (a n) (Set.range (f n)) (Φ n)) atTop (𝓝 0)) :
    PartitionAEC (fun _ : ℕ => μ)
      (fun n ξ => changingClassEmpiricalProcessLinf
        P f Φ hΦ hLin hf hΦmeas n (fun i : Fin n => X i.val ξ)) := by
  apply partitionAEC_of_localOscillation P μ X f Φ hΦ hLin hf hΦmeas hTB
  intro δ hδpos hδanti hδzero
  exact changingLocalOscillation_tendsto_zero P μ X hX_meas hX_iindep
    hX_idem hX_law f Φ hDense hf hΦ hΦmeas hLin hJ δ
    (hL2 δ hδpos hδanti hδzero)

end AsymptoticStatistics.EmpiricalProcess
