module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.OuterProbAsymptotics
public import StatLean.AsymptoticStatistics.ForMathlib.OuterIntegration.OuterExpectation
public import StatLean.AsymptoticStatistics.ForMathlib.InProbability

@[expose] public section

/-!
# Outer-probability peeling infrastructure

Outer-probability lemmas for the concentric-shell arguments in van der Vaart
Theorems 5.52 and 5.55.  The positive sample size is always `n + 1`, so all
real-valued rate exponents use `Real.rpow` without a zero-sample convention.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory Filter
open scoped ENNReal Topology

/-- Outer expectation agrees with the lower integral for an
almost-everywhere measurable nonnegative extended-real random variable. -/
theorem outerExpectation_eq_lintegral_of_aemeasurable
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) (Z : Ξ → ℝ≥0∞)
    -- an a.e.-measurable representative is enough for the integral readout.
    (hZ : AEMeasurable Z μ) :
    outerExpectation μ Z = ∫⁻ ξ, Z ξ ∂μ := by
  calc
    outerExpectation μ Z = outerExpectation μ (hZ.mk Z) :=
      outerExpectation_congr_ae hZ.ae_eq_mk
    _ = ∫⁻ ξ, hZ.mk Z ξ ∂μ := outerExpectation_eq_lintegral hZ.measurable_mk
    _ = ∫⁻ ξ, Z ξ ∂μ := lintegral_congr_ae hZ.ae_eq_mk.symm

/-- **Finite subadditivity of the induced outer measure**, in the
finite-union form used by the shell decompositions. -/
theorem outerMeasureStar_finset_iUnion_le
    {Ξ ι : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ)
    (s : Finset ι) (A : ι → Set Ξ) :
    μ.outerMeasureStar (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, μ.outerMeasureStar (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hempty : μ.outerMeasureStar (∅ : Set Ξ) = 0 := by
        rw [outerMeasureStar_eq_measure MeasurableSet.empty, measure_empty]
      simp [hempty]
  | @insert a s ha ih =>
      have hunion : (⋃ i ∈ insert a s, A i) = A a ∪ ⋃ i ∈ s, A i := by
        ext ξ
        simp
      rw [hunion, Finset.sum_insert ha]
      exact (outerMeasureStar_union_le μ _ _).trans (add_le_add le_rfl ih)

/-- **Ordinary uniform boundedness in probability implies scalar
boundedness in outer probability.** -/
theorem isBoundedInOuterProbScalar_of_isBoundedInProb
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (Z : ℕ → Ξ → ℝ)
    -- Ordinary `O_P(1)` is the stronger measurable-event formulation.
    (hZ : IsBoundedInProb (fun _ : ℕ => μ) Z) :
    IsBoundedInOuterProbScalar μ Z := by
  have hstar_le : ∀ A : Set Ξ, μ.outerMeasureStar A ≤ μ A := by
    intro A
    rw [measure_eq_iInf]
    refine le_iInf fun t => le_iInf fun hAt => le_iInf fun ht => ?_
    rw [Measure.outerMeasureStar, outerExpectation]
    calc
      (⨅ U : {U : Ξ → ℝ≥0∞ // Measurable U ∧ A.indicator 1 ≤ U},
          ∫⁻ ξ, (U : Ξ → ℝ≥0∞) ξ ∂μ)
          ≤ ∫⁻ ξ, t.indicator 1 ξ ∂μ :=
        iInf_le (fun U : {U : Ξ → ℝ≥0∞ // Measurable U ∧ A.indicator 1 ≤ U} =>
          ∫⁻ ξ, (U : Ξ → ℝ≥0∞) ξ ∂μ)
          ⟨t.indicator 1, measurable_one.indicator ht, fun ξ => by
            by_cases hξ : ξ ∈ A
            · simp [hξ, hAt hξ]
            · simp [hξ]⟩
      _ = μ t := lintegral_indicator_one ht
  intro η hη
  obtain ⟨M, hM⟩ := hZ η hη
  refine ⟨M, ?_⟩
  have hbound : ∀ n, μ.outerMeasureStar {ξ | M < |Z n ξ|} ≤ ENNReal.ofReal η := by
    intro n
    calc
      μ.outerMeasureStar {ξ | M < |Z n ξ|} ≤ μ {ξ | M < |Z n ξ|} :=
        hstar_le _
      _ = ENNReal.ofReal (μ.real {ξ | M < |Z n ξ|}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
      _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (hM n)
  calc
    limsup (fun n => μ.outerMeasureStar {ξ | M < |Z n ξ|}) atTop
        ≤ limsup (fun _ : ℕ => ENNReal.ofReal η) atTop :=
      limsup_le_limsup (Eventually.of_forall hbound) isCobounded_le_of_bot
        (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    _ = ENNReal.ofReal η := limsup_const _

/-- **Inner probability tending to one makes the outer measure of
the complementary event tend to zero.** -/
theorem TendstoInnerProbOne.tendsto_outerMeasureStar_compl
    {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {S : ℕ → Set Ξ}
    -- arbitrary target events are handled through measurable inner witnesses.
    (hS : TendstoInnerProbOne μ S) :
    Tendsto (fun n => μ.outerMeasureStar ((S n)ᶜ)) atTop (𝓝 0) := by
  obtain ⟨E, hEmeas, hES, hE⟩ := hS
  have hEmeasure : Tendsto (fun n => μ (E n)) atTop (𝓝 1) := by
    have hofReal := (ENNReal.continuous_ofReal.tendsto 1).comp hE
    convert hofReal using 1
    · funext n
      change μ (E n) = ENNReal.ofReal (μ.real (E n))
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
    · simp
  have hEcompl : Tendsto (fun n => μ ((E n)ᶜ)) atTop (𝓝 0) := by
    have hsub : Tendsto (fun n => (1 : ℝ≥0∞) - μ (E n)) atTop (𝓝 0) := by
      simpa using! ((ENNReal.continuous_sub_left ENNReal.one_ne_top).tendsto 1).comp hEmeasure
    refine hsub.congr' (Eventually.of_forall fun n => ?_)
    simpa using (measure_compl (hEmeas n) (measure_ne_top μ _)).symm
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hEcompl
    (Eventually.of_forall fun _ => zero_le)
    (Eventually.of_forall fun n => ?_)
  calc
    μ.outerMeasureStar ((S n)ᶜ) ≤ μ.outerMeasureStar ((E n)ᶜ) :=
      outerMeasureStar_mono μ (Set.compl_subset_compl.mpr (hES n))
    _ = μ ((E n)ᶜ) := outerMeasureStar_eq_measure (hEmeas n).compl

/-- The positive-sample rate `N_n^(1/(2α-2β))` from vdV Theorem 5.52, with
`N_n = n+1`.  Edge behavior is inherited from `Real.rpow`; the theorem-facing
interfaces always assume `0 < α` and `β < α`. -/
noncomputable def rateScale (α β : ℝ) (n : ℕ) : ℝ :=
  Real.rpow ((n + 1 : ℕ) : ℝ) (1 / (2 * α - 2 * β))

/-- **Algebraic balance behind the shell scale:**
`sqrt(N_n) r_n^β = r_n^α`. -/
theorem rpow_rate_shell_identity (α β : ℝ) (n : ℕ)
    -- BOOK: vdV 5.52 assumes the deterministic exponent is strictly larger.
    (hβα : β < α) :
    Real.sqrt ((n + 1 : ℕ) : ℝ) * Real.rpow (rateScale α β n) β =
      Real.rpow (rateScale α β n) α := by
  have hN : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hab : α - β ≠ 0 := ne_of_gt (sub_pos.mpr hβα)
  rw [Real.sqrt_eq_rpow, rateScale]
  have hβ : Real.rpow (Real.rpow (((n + 1 : ℕ) : ℝ))
      (1 / (2 * α - 2 * β))) β =
      Real.rpow (((n + 1 : ℕ) : ℝ)) (β / (2 * α - 2 * β)) := by
    calc
      Real.rpow (Real.rpow (((n + 1 : ℕ) : ℝ)) (1 / (2 * α - 2 * β))) β =
          Real.rpow (((n + 1 : ℕ) : ℝ)) ((1 / (2 * α - 2 * β)) * β) :=
        (Real.rpow_mul hN.le _ _).symm
      _ = Real.rpow (((n + 1 : ℕ) : ℝ)) (β / (2 * α - 2 * β)) := by
        congr 1
        ring
  have hα : Real.rpow (Real.rpow (((n + 1 : ℕ) : ℝ))
      (1 / (2 * α - 2 * β))) α =
      Real.rpow (((n + 1 : ℕ) : ℝ)) (α / (2 * α - 2 * β)) := by
    calc
      Real.rpow (Real.rpow (((n + 1 : ℕ) : ℝ)) (1 / (2 * α - 2 * β))) α =
          Real.rpow (((n + 1 : ℕ) : ℝ)) ((1 / (2 * α - 2 * β)) * α) :=
        (Real.rpow_mul hN.le _ _).symm
      _ = Real.rpow (((n + 1 : ℕ) : ℝ)) (α / (2 * α - 2 * β)) := by
        congr 1
        ring
  rw [hβ, hα]
  calc
    Real.rpow (((n + 1 : ℕ) : ℝ)) (1 / 2) *
        Real.rpow (((n + 1 : ℕ) : ℝ)) (β / (2 * α - 2 * β)) =
        Real.rpow (((n + 1 : ℕ) : ℝ)) (1 / 2 + β / (2 * α - 2 * β)) :=
      (Real.rpow_add hN _ _).symm
    _ = Real.rpow (((n + 1 : ℕ) : ℝ)) (α / (2 * α - 2 * β)) := by
      congr 1
      field_simp [hab]
      ring

/-- **A uniform eventual outer-tail estimate**, obtained by a
geometric shell sum, yields scalar outer `O_P(1)`. -/
theorem outer_geometric_peeling
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (Z : ℕ → Ξ → ℝ)
    -- terminal output of the geometric shell calculation.
    (hTail : ∀ η : ℝ, 0 < η → ∃ M : ℝ, ∃ N : ℕ, ∀ n, N ≤ n →
      μ.outerMeasureStar {ξ | M < |Z n ξ|} ≤ ENNReal.ofReal η) :
    IsBoundedInOuterProbScalar μ Z := by
  intro η hη
  obtain ⟨M, N, hN⟩ := hTail η hη
  refine ⟨M, ?_⟩
  calc
    limsup (fun n => μ.outerMeasureStar {ξ | M < |Z n ξ|}) atTop
        ≤ limsup (fun _ : ℕ => ENNReal.ofReal η) atTop :=
      limsup_le_limsup (eventually_atTop.mpr ⟨N, hN⟩) isCobounded_le_of_bot
        (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
    _ = ENNReal.ofReal η := limsup_const _

end AsymptoticStatistics.EmpiricalProcess
