module
public import StatLean.AsymptoticStatistics.Consistency.WaldCompactAvoidance

@[expose] public section

/-!
# Wald consistency on compact sets

Statement and compact-set proof of van der Vaart, Theorem 5.14.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace AsymptoticStatistics.Consistency

/-- **van der Vaart, Theorem 5.14 (Wald consistency).**

For every positive separation radius and compact parameter set, a near
maximizer of the iid empirical criterion lies in that compact set and stays
separated from the population argmax set with probability tending
to zero. -/
theorem wald_consistent_on_compact
    {X Ω Θ : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MetricSpace Θ]
    (Q : Measure X) [IsProbabilityMeasure Q]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (Xs : ℕ → Ω → X) (m : Θ → X → EReal) (θ₀ : Θ)
    (θhat : ℕ → Ω → Θ) (R : ℕ → Ω → ℝ)
    -- USER-INPUT: finite-valued criterion, upper semicontinuity, and local
    -- integrable envelopes; vdV Theorem 5.14.
    (hm_top : ∀ θ x, m θ x ≠ ⊤)
    (husc : ∀ θ, ∀ᵐ x ∂Q, UpperSemicontinuousAt (fun η => m η x) θ)
    (hlocal : ∀ θ, ∃ ρ > 0, ∀ r, 0 < r → r ≤ ρ →
      Measurable (localCriterionSup m θ r) ∧
      (∫⁻ x, (localCriterionSup m θ r x).toENNReal ∂Q) ≠ ∞)
    -- USER-INPUT: `θ₀` maximizes the population criterion; vdV Theorem 5.14.
    (hmax : θ₀ ∈ {θ | ∀ η,
      extendedExpectation Q (m η) ≤ extendedExpectation Q (m θ)})
    -- LEAN-ONLY: measurability of each sample coordinate.
    (hXs_meas : ∀ i, Measurable (Xs i))
    -- USER-INPUT: iid observations with common law `Q`; vdV Theorem 5.14.
    (hXs_indep : ProbabilityTheory.iIndepFun Xs ℙ)
    (hXs_id : ∀ i, ProbabilityTheory.IdentDistrib (Xs i) (Xs 0) ℙ ℙ)
    (hXs_law : ℙ.map (Xs 0) = Q)
    -- USER-INPUT: approximate maximization with an `o_P(1)` remainder;
    -- vdV Theorem 5.14.
    (hnear : ∀ n ω,
      extendedEmpiricalAvg (m θ₀) n (fun i : Fin n => Xs i.val ω) - (R n ω : EReal) ≤
      extendedEmpiricalAvg (m (θhat n ω)) n (fun i : Fin n => Xs i.val ω))
    (hR : TendstoInMeasure ℙ R atTop (fun _ => 0))
    -- USER-INPUT: compact subset on which consistency is asserted.
    (K : Set Θ) (hK : IsCompact K) :
    ∀ ε > 0, Tendsto (fun n => ℙ {ω |
      ε ≤ Metric.infDist (θhat n ω)
        {θ | ∀ η, extendedExpectation Q (m η) ≤ extendedExpectation Q (m θ)} ∧
      θhat n ω ∈ K}) atTop (𝓝 0) := by
  intro ε hε
  by_cases hbot : extendedExpectation Q (m θ₀) = ⊥
  · have hall (θ : Θ) : extendedExpectation Q (m θ) = ⊥ := by
      exact le_bot_iff.mp (hbot ▸ hmax θ)
    have hargmax :
        {θ : Θ | ∀ η, extendedExpectation Q (m η) ≤ extendedExpectation Q (m θ)} =
          Set.univ := by
      ext θ
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro η
      rw [hall η, hall θ]
    simp only [hargmax]
    have hinf (n : ℕ) (ω : Ω) : Metric.infDist (θhat n ω) (Set.univ : Set Θ) = 0 :=
      Metric.infDist_zero_of_mem (Set.mem_univ _)
    simp only [hinf, not_le_of_gt hε, false_and, Set.setOf_false, measure_empty,
      tendsto_const_nhds]
  have hfinite : ∃ a : ℝ, extendedExpectation Q (m θ₀) = (a : EReal) := by
    obtain ⟨ρ, hρ, hloc⟩ := hlocal θ₀
    have hlocρ := (hloc ρ hρ le_rfl).2
    have hpos_le :
        (∫⁻ x, (m θ₀ x).toENNReal ∂Q) ≤
          ∫⁻ x, (localCriterionSup m θ₀ ρ x).toENNReal ∂Q := by
      apply lintegral_mono
      intro x
      apply EReal.toENNReal_le_toENNReal
      unfold localCriterionSup
      exact le_iSup_of_le ⟨θ₀, Metric.mem_ball_self hρ⟩ le_rfl
    have hpos : (∫⁻ x, (m θ₀ x).toENNReal ∂Q) ≠ ∞ :=
      ne_top_of_le_ne_top hlocρ hpos_le
    have htop : extendedExpectation Q (m θ₀) ≠ ⊤ := by
      by_cases hneg : (∫⁻ x, (-m θ₀ x).toENNReal ∂Q) = ∞
      · simp [extendedExpectation, hneg]
      · rw [extendedExpectation, ← EReal.coe_ennreal_toReal hpos,
          ← EReal.coe_ennreal_toReal hneg, ← EReal.coe_sub]
        exact EReal.coe_ne_top _
    exact ⟨(extendedExpectation Q (m θ₀)).toReal,
      (EReal.coe_toReal htop hbot).symm⟩
  let Θ₀ : Set Θ :=
    {θ | ∀ η, extendedExpectation Q (m η) ≤ extendedExpectation Q (m θ)}
  let B : Set Θ := K ∩ {θ | ε ≤ Metric.infDist θ Θ₀}
  have hfar_closed : IsClosed {θ : Θ | ε ≤ Metric.infDist θ Θ₀} :=
    isClosed_le continuous_const (Metric.continuous_infDist_pt Θ₀)
  have hB_compact : IsCompact B := hK.inter_right hfar_closed
  have hB_disjoint : Disjoint B Θ₀ := by
    rw [Set.disjoint_left]
    intro θ hθB hθ₀
    change θ ∈ K ∩ {η | ε ≤ Metric.infDist η Θ₀} at hθB
    have hzero : Metric.infDist θ Θ₀ = 0 := Metric.infDist_zero_of_mem hθ₀
    exact (not_le_of_gt hε) (hzero ▸ hθB.2)
  have havoid := wald_avoids_compact_disjoint Q ℙ Xs m θ₀ θhat R
    hm_top husc hlocal hmax hfinite hXs_meas hXs_indep hXs_id hXs_law
    hnear hR B hB_compact (by simpa only [Θ₀] using hB_disjoint)
  simpa only [B, Θ₀, Set.mem_inter_iff, Set.mem_setOf_eq, and_comm] using havoid

end AsymptoticStatistics.Consistency
