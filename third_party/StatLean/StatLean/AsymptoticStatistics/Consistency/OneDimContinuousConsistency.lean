module
public import StatLean.AsymptoticStatistics.ForMathlib.MeanVarConvergence
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# One-dimensional Z-estimator consistency, continuous case (van der Vaart, Lemma 5.10)

vdV, *Asymptotic Statistics* §5.2 ("Consistency"), Lemma 5.10, p. 47.

Let `Θ ⊆ ℝ`, let `Ψn` be random functions and `Ψ` a fixed function with
`Ψn(θ) →ₚ Ψ(θ)` for every `θ ∈ Θ`, and let `θ₀` be an **interior** point of `Θ`
(`Θ ∈ 𝓝 θ₀`) at which `Ψ` changes sign strictly (`Ψ θ < 0` for `θ ∈ Θ`, `θ < θ₀`;
`0 < Ψ θ` for `θ ∈ Θ`, `θ₀ < θ`). If each `θ ↦ Ψn(θ)` is **continuous on `Θ`** with
`θ̂ₙ` the **unique zero** in `Θ` (`hunique`), then the estimator sequence `θ̂ₙ` is
consistent: `P{ε ≤ |θ̂ₙ − θ₀|} → 0` for every `ε > 0`.

This is proved at **greater generality than vdV states**: the intermediate-value
route establishes existence of a zero in a small interval around `θ₀` and pins it to
`θ̂ₙ` via `hunique` on the convergence-relevant event, so vdV's setup facts "`θ̂ₙ` is a
zero", "`θ̂ₙ ∈ Θ`", and "`Θ` is an interval (order-connected)" are **not needed** — they
are recovered as instances (any genuine unique-zero estimator satisfies them). Only a
neighborhood of `θ₀` (`hθ₀_int`) and the local uniqueness `hunique` are used.

The nondecreasing half of Lemma 5.10 lives in the sibling file
`OneDimMonotoneConsistency.lean`.

**Interiority is genuinely needed here** (unlike the monotone case). The continuous
half of Lemma 5.10 is *false* at a boundary `θ₀`: e.g. `Θ = [0, ∞)`, `θ₀ = 0`,
`Ψn(x) = x` on `[0, n−1]` ramped down to a single zero at `x = n`, gives
`Ψn → Ψ = id` pointwise with each `Ψn` continuous with unique zero, yet `θ̂ₙ = n → ∞`.
Continuity alone cannot pin the zero from one side. So this theorem carries the
interiority hypothesis `hθ₀_int : Θ ∈ 𝓝 θ₀`, which vdV's "for every `ε > 0`" sign
condition tacitly presupposes through non-vacuity on both sides of `θ₀`.

The proof is purely set-theoretic on the measure side: it uses only `measure_mono`
and `measure_union_le`, so `P` is kept a completely general measure (no measurability
of `θ̂ₙ`, no `IsProbabilityMeasure`). The intermediate value theorem produces a zero of
`Ψn` inside a small `(θ₀ − δ, θ₀ + δ)` (with `δ ≤ ε` and `Icc(θ₀−δ)(θ₀+δ) ⊆ Θ` from
interiority) whenever `Ψn` is negative at `θ₀ − δ` and positive at `θ₀ + δ`; uniqueness
identifies it with `θ̂ₙ`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.Consistency

/-- **van der Vaart, Lemma 5.10 (continuous unique-zero case), general `Θ ⊆ ℝ`.**
Let `θ₀` be an interior point of `Θ ⊆ ℝ`. If each `θ ↦ Ψn n ω θ` is continuous on `Θ`,
`θ̂ₙ` is the **unique zero** of `Ψn n ω` in `Θ` (`hunique`), `Ψn(θ) →ₚ Ψ(θ)` for every
`θ ∈ Θ`, and `Ψ` changes sign strictly across `θ₀` (`Ψ θ < 0` for `θ ∈ Θ`, `θ < θ₀`;
`0 < Ψ θ` for `θ ∈ Θ`, `θ₀ < θ`), then `θ̂ₙ` is consistent for `θ₀`.

Minimal-hypothesis form (see the module docstring): `θ̂ₙ` need not be assumed a zero or in
`Θ`, nor `Θ` order-connected — these are recovered on the good event, making this strictly
more general than vdV's stated setup. -/
theorem oneDim_continuous_zEstimator_consistent
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Θ : Set ℝ}
    {Ψn : ℕ → Ω → ℝ → ℝ} {Ψ : ℝ → ℝ} {θ₀ : ℝ} {θhat : ℕ → Ω → ℝ}
    -- USER-INPUT: the domain is a neighbourhood of θ₀; vdV Lem 5.10
    (hθ₀_int : Θ ∈ 𝓝 θ₀)
    -- USER-INPUT: each sample criterion θ ↦ Ψₙ(θ) is continuous on the domain; vdV Lem 5.10
    (hcont : ∀ n ω, ContinuousOn (Ψn n ω) Θ)
    -- USER-INPUT: θ̂ₙ is the unique zero of Ψₙ on the domain ("has exactly one zero");
    -- vdV Lem 5.10
    (hunique : ∀ n ω θ, θ ∈ Θ → Ψn n ω θ = 0 → θ = θhat n ω)
    -- USER-INPUT: pointwise convergence in probability Ψₙ(θ) → Ψ(θ); vdV Lem 5.10
    (hptwise : ∀ θ ∈ Θ, TendstoInMeasure P (fun n ω => Ψn n ω θ) atTop (fun _ => Ψ θ))
    -- USER-INPUT (hsign_lt, hsign_gt): strict sign change of Ψ at θ₀; vdV Lem 5.10
    (hsign_lt : ∀ θ ∈ Θ, θ < θ₀ → Ψ θ < 0)
    (hsign_gt : ∀ θ ∈ Θ, θ₀ < θ → 0 < Ψ θ) :
    ∀ ε > (0 : ℝ), Tendsto (fun n => P {ω | ε ≤ |θhat n ω - θ₀|}) atTop (𝓝 0) := by
  intro ε hε
  -- Extract an interior radius `r` with `ball θ₀ r ⊆ Θ`, then shrink to `δ ≤ ε`.
  obtain ⟨r, hr, hr_sub⟩ := Metric.mem_nhds_iff.mp hθ₀_int
  set δ : ℝ := min ε (r / 2) with hδ_def
  have hδ_pos : 0 < δ := lt_min hε (by linarith)
  have hδ_le_ε : δ ≤ ε := min_le_left _ _
  have hδ_le_r : δ ≤ r / 2 := min_le_right _ _
  have hIcc_sub : Set.Icc (θ₀ - δ) (θ₀ + δ) ⊆ Θ := by
    intro x hx
    rw [Set.mem_Icc] at hx
    apply hr_sub
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · linarith [hx.1, hδ_le_r, hr]
    · linarith [hx.2, hδ_le_r, hr]
  have hmem_lo : θ₀ - δ ∈ Θ := hIcc_sub (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩)
  have hmem_hi : θ₀ + δ ∈ Θ := hIcc_sub (Set.mem_Icc.mpr ⟨by linarith, le_rfl⟩)
  -- Sign margin `η > 0` with `Ψ(θ₀−δ) ≤ −2η` and `2η ≤ Ψ(θ₀+δ)`.
  have hΨneg : Ψ (θ₀ - δ) < 0 := hsign_lt (θ₀ - δ) hmem_lo (by linarith)
  have hΨpos : 0 < Ψ (θ₀ + δ) := hsign_gt (θ₀ + δ) hmem_hi (by linarith)
  set η : ℝ := min (-Ψ (θ₀ - δ)) (Ψ (θ₀ + δ)) / 2 with hη_def
  have hlopos : 0 < -Ψ (θ₀ - δ) := by linarith
  have hminpos : 0 < min (-Ψ (θ₀ - δ)) (Ψ (θ₀ + δ)) := lt_min hlopos hΨpos
  have hη : 0 < η := by rw [hη_def]; linarith
  have hbound_lo : Ψ (θ₀ - δ) ≤ -2 * η := by
    have h := min_le_left (-Ψ (θ₀ - δ)) (Ψ (θ₀ + δ)); rw [hη_def]; linarith
  have hbound_hi : 2 * η ≤ Ψ (θ₀ + δ) := by
    have h := min_le_right (-Ψ (θ₀ - δ)) (Ψ (θ₀ + δ)); rw [hη_def]; linarith
  have T_lo := tendstoInMeasure_iff_norm.mp (hptwise (θ₀ - δ) hmem_lo) η hη
  have T_hi := tendstoInMeasure_iff_norm.mp (hptwise (θ₀ + δ) hmem_hi) η hη
  have hab : θ₀ - δ ≤ θ₀ + δ := by linarith
  -- Event inclusion via the intermediate value theorem + uniqueness of the zero.
  have hincl : ∀ n, {ω | ε ≤ |θhat n ω - θ₀|} ⊆
      {ω | η ≤ ‖Ψn n ω (θ₀ - δ) - Ψ (θ₀ - δ)‖}
      ∪ {ω | η ≤ ‖Ψn n ω (θ₀ + δ) - Ψ (θ₀ + δ)‖} := by
    intro n ω hω
    simp only [Set.mem_setOf_eq] at hω
    by_contra hcon
    rw [Set.mem_union, not_or] at hcon
    obtain ⟨h1, h2⟩ := hcon
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs, not_le] at h1 h2
    rw [abs_lt] at h1 h2
    -- Strict sign change of `Ψn` across `[θ₀−δ, θ₀+δ]`.
    have hsign_lo : Ψn n ω (θ₀ - δ) < 0 := by linarith [hbound_lo, h1.2, hη]
    have hsign_hi : 0 < Ψn n ω (θ₀ + δ) := by linarith [hbound_hi, h2.1, hη]
    have hmem0 : (0 : ℝ) ∈ Set.Ioo (Ψn n ω (θ₀ - δ)) (Ψn n ω (θ₀ + δ)) :=
      ⟨hsign_lo, hsign_hi⟩
    have hsub := intermediate_value_Ioo hab ((hcont n ω).mono hIcc_sub)
    obtain ⟨c, hc_mem, hc_eq⟩ := hsub hmem0
    -- The interior zero `c` must be the unique zero `θ̂ₙ`.
    have hc_mem_Θ : c ∈ Θ := hIcc_sub (Set.Ioo_subset_Icc_self hc_mem)
    have hc_that : c = θhat n ω := hunique n ω c hc_mem_Θ hc_eq
    rw [hc_that] at hc_mem
    obtain ⟨hm1, hm2⟩ := hc_mem
    have hcontra : |θhat n ω - θ₀| < δ := by rw [abs_lt]; constructor <;> linarith
    linarith [hω, hcontra, hδ_le_ε]
  -- Measure bound + two-term squeeze.
  have h_meas_bd : ∀ n, P {ω | ε ≤ |θhat n ω - θ₀|} ≤
      P {ω | η ≤ ‖Ψn n ω (θ₀ - δ) - Ψ (θ₀ - δ)‖}
      + P {ω | η ≤ ‖Ψn n ω (θ₀ + δ) - Ψ (θ₀ + δ)‖} := fun n =>
    (measure_mono (hincl n)).trans (measure_union_le _ _)
  have h_sum : Tendsto (fun n =>
      P {ω | η ≤ ‖Ψn n ω (θ₀ - δ) - Ψ (θ₀ - δ)‖}
      + P {ω | η ≤ ‖Ψn n ω (θ₀ + δ) - Ψ (θ₀ + δ)‖}) atTop (𝓝 0) := by
    simpa using T_lo.add T_hi
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall h_meas_bd)

/-- **`Θ = ℝ` specialization** of `oneDim_continuous_zEstimator_consistent`: interiority
of `θ₀` is automatic (`Set.univ ∈ 𝓝 θ₀`), each `Ψn n ω` is continuous on all of `ℝ`,
the zero is globally unique, and the sign change is stated with unrestricted `θ`. -/
theorem oneDim_continuous_zEstimator_consistent_univ
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Ψn : ℕ → Ω → ℝ → ℝ} {Ψ : ℝ → ℝ} {θ₀ : ℝ} {θhat : ℕ → Ω → ℝ}
    (hcont : ∀ n ω, Continuous (Ψn n ω))
    (hunique : ∀ n ω θ, Ψn n ω θ = 0 → θ = θhat n ω)
    (hptwise : ∀ θ, TendstoInMeasure P (fun n ω => Ψn n ω θ) atTop (fun _ => Ψ θ))
    (hsign_lt : ∀ θ, θ < θ₀ → Ψ θ < 0)
    (hsign_gt : ∀ θ, θ₀ < θ → 0 < Ψ θ) :
    ∀ ε > (0 : ℝ), Tendsto (fun n => P {ω | ε ≤ |θhat n ω - θ₀|}) atTop (𝓝 0) :=
  oneDim_continuous_zEstimator_consistent Filter.univ_mem
    (fun n ω => (hcont n ω).continuousOn)
    (fun n ω θ _ => hunique n ω θ) (fun θ _ => hptwise θ)
    (fun θ _ => hsign_lt θ) (fun θ _ => hsign_gt θ)

end AsymptoticStatistics.Consistency
