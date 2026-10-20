module
public import StatLean.AsymptoticStatistics.ForMathlib.MeanVarConvergence
public import Mathlib.Order.Interval.Set.OrdConnected

@[expose] public section

/-!
# One-dimensional Z-estimator consistency, monotone case (van der Vaart, Lemma 5.10)

vdV, *Asymptotic Statistics* §5.2 ("Consistency"), Lemma 5.10, p. 47.

Let `Θ ⊆ ℝ` be order-connected ("a subset of the real line"), let `Ψn` be random
functions and `Ψ` a fixed function with `Ψn(θ) →ₚ Ψ(θ)` for every `θ ∈ Θ`, and let
`θ₀ ∈ Θ` satisfy the sign-separation `Ψ θ < 0` for `θ < θ₀` and `0 < Ψ θ` for
`θ₀ < θ` (both restricted to `Θ`). If each `θ ↦ Ψn(θ)` is **nondecreasing on `Θ`**
with `Ψn(θ̂ₙ) = oₚ(1)`, then the estimator sequence `θ̂ₙ` is consistent:
`P{ε ≤ |θ̂ₙ − θ₀|} → 0` for every `ε > 0`.

The continuous unique-zero half of Lemma 5.10 lives in the sibling file
`OneDimContinuousConsistency.lean`.

The proof is purely set-theoretic on the measure side: it uses only `measure_mono`
and `measure_union_le`, so `P` is kept a completely general measure (no measurability
of `θ̂ₙ`, no `IsProbabilityMeasure`). The convergence inputs enter through
`MeasureTheory.tendstoInMeasure_iff_norm`.

Order-connectedness of `Θ` is what powers the monotone case at a boundary: whenever
the deviation event `{θ̂ₙ ≤ θ₀ − ε}` reaches a point `θ₀ − ε ∉ Θ`, that point would sit
inside `Icc (θ̂ₙ) θ₀ ⊆ Θ`, a contradiction, so the event is empty. No interiority of `θ₀`
is required (contrast the continuous case, which is false at a boundary `θ₀`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.Consistency

/-- **van der Vaart, Lemma 5.10 (nondecreasing case), general `Θ ⊆ ℝ`.**
Let `Θ` be an order-connected subset of `ℝ`. If each `θ ↦ Ψn n ω θ` is nondecreasing
on `Θ`, `Ψn(θ̂ₙ) →ₚ 0`, `Ψn(θ) →ₚ Ψ(θ)` for every `θ ∈ Θ`, `θ₀, θ̂ₙ ∈ Θ`, and `Ψ`
changes sign strictly across `θ₀` (`Ψ θ < 0` for `θ ∈ Θ`, `θ < θ₀`; `0 < Ψ θ` for
`θ ∈ Θ`, `θ₀ < θ`), then the estimator sequence `θ̂ₙ` is consistent for `θ₀`. -/
theorem oneDim_monotone_zEstimator_consistent
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    -- USER-INPUT: the parameter domain is an interval (order-connected); vdV Lem 5.10
    {Θ : Set ℝ} (hΘ : Θ.OrdConnected)
    {Ψn : ℕ → Ω → ℝ → ℝ} {Ψ : ℝ → ℝ} {θ₀ : ℝ} {θhat : ℕ → Ω → ℝ}
    -- USER-INPUT (hθ₀, hθhat): θ₀ and the estimators take values in the domain; vdV Lem 5.10
    (hθ₀ : θ₀ ∈ Θ)
    (hθhat : ∀ n ω, θhat n ω ∈ Θ)
    -- USER-INPUT: each sample criterion θ ↦ Ψₙ(θ) is monotone; vdV Lem 5.10
    (hmono : ∀ n ω, MonotoneOn (Ψn n ω) Θ)
    -- USER-INPUT: pointwise convergence in probability Ψₙ(θ) → Ψ(θ); vdV Lem 5.10
    (hptwise : ∀ θ ∈ Θ, TendstoInMeasure P (fun n ω => Ψn n ω θ) atTop (fun _ => Ψ θ))
    -- USER-INPUT: θ̂ₙ is a near-zero, Ψₙ(θ̂ₙ) = o_P(1); vdV Lem 5.10
    (hnear : TendstoInMeasure P (fun n ω => Ψn n ω (θhat n ω)) atTop (fun _ => (0 : ℝ)))
    -- USER-INPUT (hsign_lt, hsign_gt): strict sign change of Ψ at θ₀,
    -- Ψ < 0 left of θ₀ and Ψ > 0 right of θ₀; vdV Lem 5.10
    (hsign_lt : ∀ θ ∈ Θ, θ < θ₀ → Ψ θ < 0)
    (hsign_gt : ∀ θ ∈ Θ, θ₀ < θ → 0 < Ψ θ) :
    ∀ ε > (0 : ℝ), Tendsto (fun n => P {ω | ε ≤ |θhat n ω - θ₀|}) atTop (𝓝 0) := by
  intro ε hε
  -- **Lower tail**: `P{θ̂ₙ ≤ θ₀ − ε} → 0`.
  have h_lo : Tendsto (fun n => P {ω | θhat n ω ≤ θ₀ - ε}) atTop (𝓝 0) := by
    by_cases hmem : θ₀ - ε ∈ Θ
    · -- `θ₀−ε ∈ Θ`: monotonicity compares `Ψn(θ̂ₙ) ≤ Ψn(θ₀−ε)`.
      have hΨneg : Ψ (θ₀ - ε) < 0 := hsign_lt (θ₀ - ε) hmem (by linarith)
      set η : ℝ := -Ψ (θ₀ - ε) / 2 with hη_def
      have hη : 0 < η := by rw [hη_def]; linarith
      have hΨeq : Ψ (θ₀ - ε) = -2 * η := by rw [hη_def]; ring
      have T_lo := tendstoInMeasure_iff_norm.mp (hptwise (θ₀ - ε) hmem) η hη
      have T_near := tendstoInMeasure_iff_norm.mp hnear η hη
      have hincl : ∀ n, {ω | θhat n ω ≤ θ₀ - ε} ⊆
          {ω | η ≤ ‖Ψn n ω (θ₀ - ε) - Ψ (θ₀ - ε)‖}
          ∪ {ω | η ≤ ‖Ψn n ω (θhat n ω) - 0‖} := by
        intro n ω hω
        simp only [Set.mem_setOf_eq] at hω
        by_contra hcon
        rw [Set.mem_union, not_or] at hcon
        obtain ⟨h1, h2⟩ := hcon
        simp only [Set.mem_setOf_eq, Real.norm_eq_abs, not_le] at h1 h2
        rw [abs_lt] at h1 h2
        have hmono' : Ψn n ω (θhat n ω) ≤ Ψn n ω (θ₀ - ε) :=
          hmono n ω (hθhat n ω) hmem hω
        linarith [h1.2, h2.1, hmono', hΨeq]
      have h_meas_bd : ∀ n, P {ω | θhat n ω ≤ θ₀ - ε} ≤
          P {ω | η ≤ ‖Ψn n ω (θ₀ - ε) - Ψ (θ₀ - ε)‖}
          + P {ω | η ≤ ‖Ψn n ω (θhat n ω) - 0‖} := fun n =>
        (measure_mono (hincl n)).trans (measure_union_le _ _)
      have h_sum : Tendsto (fun n =>
          P {ω | η ≤ ‖Ψn n ω (θ₀ - ε) - Ψ (θ₀ - ε)‖}
          + P {ω | η ≤ ‖Ψn n ω (θhat n ω) - 0‖}) atTop (𝓝 0) := by
        simpa using T_lo.add T_near
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum
        (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall h_meas_bd)
    · -- `θ₀−ε ∉ Θ`: order-connectedness forces the event to be empty.
      have hempty : ∀ n, {ω | θhat n ω ≤ θ₀ - ε} = (∅ : Set Ω) := by
        intro n
        rw [Set.eq_empty_iff_forall_notMem]
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω
        exact hmem (hΘ.out (hθhat n ω) hθ₀ (Set.mem_Icc.mpr ⟨hω, by linarith⟩))
      simp only [hempty, measure_empty]
      exact tendsto_const_nhds
  -- **Upper tail**: `P{θ₀ + ε ≤ θ̂ₙ} → 0`.
  have h_hi : Tendsto (fun n => P {ω | θ₀ + ε ≤ θhat n ω}) atTop (𝓝 0) := by
    by_cases hmem : θ₀ + ε ∈ Θ
    · -- `θ₀+ε ∈ Θ`: monotonicity compares `Ψn(θ₀+ε) ≤ Ψn(θ̂ₙ)`.
      have hΨpos : 0 < Ψ (θ₀ + ε) := hsign_gt (θ₀ + ε) hmem (by linarith)
      set η : ℝ := Ψ (θ₀ + ε) / 2 with hη_def
      have hη : 0 < η := by rw [hη_def]; linarith
      have hΨeq : Ψ (θ₀ + ε) = 2 * η := by rw [hη_def]; ring
      have T_hi := tendstoInMeasure_iff_norm.mp (hptwise (θ₀ + ε) hmem) η hη
      have T_near := tendstoInMeasure_iff_norm.mp hnear η hη
      have hincl : ∀ n, {ω | θ₀ + ε ≤ θhat n ω} ⊆
          {ω | η ≤ ‖Ψn n ω (θ₀ + ε) - Ψ (θ₀ + ε)‖}
          ∪ {ω | η ≤ ‖Ψn n ω (θhat n ω) - 0‖} := by
        intro n ω hω
        simp only [Set.mem_setOf_eq] at hω
        by_contra hcon
        rw [Set.mem_union, not_or] at hcon
        obtain ⟨h1, h2⟩ := hcon
        simp only [Set.mem_setOf_eq, Real.norm_eq_abs, not_le] at h1 h2
        rw [abs_lt] at h1 h2
        have hmono' : Ψn n ω (θ₀ + ε) ≤ Ψn n ω (θhat n ω) :=
          hmono n ω hmem (hθhat n ω) hω
        linarith [h1.1, h2.2, hmono', hΨeq]
      have h_meas_bd : ∀ n, P {ω | θ₀ + ε ≤ θhat n ω} ≤
          P {ω | η ≤ ‖Ψn n ω (θ₀ + ε) - Ψ (θ₀ + ε)‖}
          + P {ω | η ≤ ‖Ψn n ω (θhat n ω) - 0‖} := fun n =>
        (measure_mono (hincl n)).trans (measure_union_le _ _)
      have h_sum : Tendsto (fun n =>
          P {ω | η ≤ ‖Ψn n ω (θ₀ + ε) - Ψ (θ₀ + ε)‖}
          + P {ω | η ≤ ‖Ψn n ω (θhat n ω) - 0‖}) atTop (𝓝 0) := by
        simpa using T_hi.add T_near
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum
        (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall h_meas_bd)
    · -- `θ₀+ε ∉ Θ`: order-connectedness forces the event to be empty.
      have hempty : ∀ n, {ω | θ₀ + ε ≤ θhat n ω} = (∅ : Set Ω) := by
        intro n
        rw [Set.eq_empty_iff_forall_notMem]
        intro ω hω
        simp only [Set.mem_setOf_eq] at hω
        exact hmem (hΘ.out hθ₀ (hθhat n ω) (Set.mem_Icc.mpr ⟨by linarith, hω⟩))
      simp only [hempty, measure_empty]
      exact tendsto_const_nhds
  -- Combine the two one-sided tails through the `abs` split.
  have hincl : ∀ n, {ω | ε ≤ |θhat n ω - θ₀|} ⊆
      {ω | θhat n ω ≤ θ₀ - ε} ∪ {ω | θ₀ + ε ≤ θhat n ω} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq] at hω
    rcases le_abs.mp hω with h | h
    · exact Or.inr (by simp only [Set.mem_setOf_eq]; linarith)
    · exact Or.inl (by simp only [Set.mem_setOf_eq]; linarith)
  have h_meas_bd : ∀ n, P {ω | ε ≤ |θhat n ω - θ₀|} ≤
      P {ω | θhat n ω ≤ θ₀ - ε} + P {ω | θ₀ + ε ≤ θhat n ω} := fun n =>
    (measure_mono (hincl n)).trans (measure_union_le _ _)
  have h_sum : Tendsto (fun n =>
      P {ω | θhat n ω ≤ θ₀ - ε} + P {ω | θ₀ + ε ≤ θhat n ω}) atTop (𝓝 0) := by
    simpa using h_lo.add h_hi
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall h_meas_bd)

/-- **`Θ = ℝ` specialization** of `oneDim_monotone_zEstimator_consistent`, for the
common ambient-line callers (median sign-sum etc.). Each `Ψn n ω` is nondecreasing on
all of `ℝ` and the sign change is stated with unrestricted `θ`. -/
theorem oneDim_monotone_zEstimator_consistent_univ
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Ψn : ℕ → Ω → ℝ → ℝ} {Ψ : ℝ → ℝ} {θ₀ : ℝ} {θhat : ℕ → Ω → ℝ}
    (hmono : ∀ n ω, Monotone (Ψn n ω))
    (hptwise : ∀ θ, TendstoInMeasure P (fun n ω => Ψn n ω θ) atTop (fun _ => Ψ θ))
    (hnear : TendstoInMeasure P (fun n ω => Ψn n ω (θhat n ω)) atTop (fun _ => (0 : ℝ)))
    (hsign_lt : ∀ θ, θ < θ₀ → Ψ θ < 0)
    (hsign_gt : ∀ θ, θ₀ < θ → 0 < Ψ θ) :
    ∀ ε > (0 : ℝ), Tendsto (fun n => P {ω | ε ≤ |θhat n ω - θ₀|}) atTop (𝓝 0) :=
  oneDim_monotone_zEstimator_consistent Set.ordConnected_univ (Set.mem_univ _)
    (fun _ _ => Set.mem_univ _) (fun n ω => monotoneOn_univ.mpr (hmono n ω))
    (fun θ _ => hptwise θ) hnear (fun θ _ => hsign_lt θ) (fun θ _ => hsign_gt θ)

end AsymptoticStatistics.Consistency
