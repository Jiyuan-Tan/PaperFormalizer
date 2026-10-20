module
public import StatLean.AsymptoticStatistics.ForMathlib.MeanVarConvergence
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.MeasureTheory.OuterMeasure.AE

@[expose] public section

/-!
# Consistency of M- and Z-estimators (vdV §5.2)

This file formalizes van der Vaart, *Asymptotic Statistics* (Cambridge, 1998):

* **Theorem 5.7** (`mEstimator_consistent`): consistency of an M-estimator `θ̂ₙ`
  under a uniform-convergence condition on the criterion functions `Mₙ` and a
  well-separated-maximum condition on the limit `M`.
* **Theorem 5.9** (`zEstimator_consistent`): the Z-estimator corollary, obtained
  from 5.7 by the substitution `Mₙ := −‖Ψₙ‖`, `M := −‖Ψ‖`.

## Encoding

vdV states the uniform-convergence hypothesis as `sup_θ |Mₙ(θ) − M(θ)| →ₚ 0`, with
an explicit footnote that this supremum "may be nonmeasurable; then the probability
statements are understood in terms of outer measure". We render this faithfully by a
*measurable envelope* `Uₙ : ℕ → Ω → ℝ` dominating `|Mₙθ − Mθ|` pointwise in `θ` and
converging in probability to `0`. Under vdV's own outer-measure reading the two forms
are equivalent (`{sup ≥ ε} ⊆ {Uₙ ≥ ε}` gives one direction; the measurable majorant
gives the other), so the envelope is the measurable surrogate for the outer-probability
sup, not a strengthening. Consequently the proofs need only `measure_mono`
(unconditional) plus the two convergence bricks from `ForMathlib/MeanVarConvergence`,
and require **no** measurability of `θ̂ₙ` / `Mₙ` and **no** `IsProbabilityMeasure P`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace AsymptoticStatistics.Consistency

/-- **van der Vaart, Theorem 5.7 (consistency of M-estimators).**

Let `Mₙ` be random criterion functions on a metric parameter space `Θ`, dominated by a
measurable envelope `Uₙ` (`hU_dom`) that converges to `0` in probability (`hU_conv`),
the measurable surrogate for vdV's outer-probability `sup_θ|Mₙ−M| →ₚ 0`. Suppose the
limit criterion `M` has a **well-separated maximum** at `θ₀` (`hsep`): off every
`ε`-ball, `M` stays below `M θ₀` by a fixed margin `η`. Then any near-maximizing sequence
`θ̂ₙ` — one for which `Mₙ(θ̂ₙ) ≥ Mₙ(θ₀) − Rₙ` with `Rₙ →ₚ 0` (`hnear`, `hR_conv`) —
is consistent: `θ̂ₙ →ₚ θ₀`. -/
theorem mEstimator_consistent
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Θ : Type*} [MetricSpace Θ]
    {Mn : ℕ → Ω → Θ → ℝ} {M : Θ → ℝ} {θ₀ : Θ} {θhat : ℕ → Ω → Θ}
    {U R : ℕ → Ω → ℝ}
    -- USER-INPUT (hU_dom, hU_conv): sup_θ |Mₙ(θ) − M(θ)| → 0 in probability, phrased
    -- through a measurable envelope U (the envelope replaces the book's outer
    -- probability of the possibly non-measurable sup); vdV Thm 5.7
    (hU_dom : ∀ n ω θ, |Mn n ω θ - M θ| ≤ U n ω)
    (hU_conv : TendstoInMeasure P U atTop (fun _ => (0 : ℝ)))
    -- USER-INPUT: M has a well-separated maximum at θ₀; vdV Thm 5.7
    (hsep : ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ θ, ε ≤ dist θ θ₀ → M θ ≤ M θ₀ - η)
    -- USER-INPUT (hnear, hR_conv): θ̂ₙ near-maximizes Mₙ up to a vanishing slack,
    -- Mₙ(θ̂ₙ) ≥ Mₙ(θ₀) − o_P(1); vdV Thm 5.7
    (hnear : ∀ n ω, Mn n ω θ₀ - R n ω ≤ Mn n ω (θhat n ω))
    (hR_conv : TendstoInMeasure P R atTop (fun _ => (0 : ℝ))) :
    ∀ ε > (0 : ℝ), Tendsto (fun n => P {ω | ε ≤ dist (θhat n ω) θ₀}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨η, hη, hsepη⟩ := hsep ε hε
  -- `2·Uₙ + Rₙ →ₚ 0` from the two convergence bricks.
  have hconv : TendstoInMeasure P (fun n ω => 2 * U n ω + R n ω) atTop (fun _ => (0 : ℝ)) := by
    have h2U := tendstoInMeasure_const_mul (2 : ℝ) hU_conv
    simp only [mul_zero] at h2U
    have hsum := tendstoInMeasure_add h2U hR_conv
    simpa using hsum
  have hthresh := tendstoInMeasure_iff_norm.mp hconv η hη
  -- On the event `{ε ≤ dist(θ̂ₙ,θ₀)}` the deviation `2Uₙ+Rₙ` is at least `η`.
  have hsubset : ∀ n, {ω | ε ≤ dist (θhat n ω) θ₀}
      ⊆ {ω | η ≤ ‖(2 * U n ω + R n ω) - 0‖} := by
    intro n ω hω
    rw [Set.mem_setOf_eq] at hω
    rw [Set.mem_setOf_eq, Real.norm_eq_abs, sub_zero]
    have hsep_ineq := hsepη (θhat n ω) hω
    have hd0 := abs_le.mp (hU_dom n ω θ₀)
    have hdhat := abs_le.mp (hU_dom n ω (θhat n ω))
    have hnr := hnear n ω
    calc η ≤ 2 * U n ω + R n ω := by
              linarith [hsep_ineq, hd0.1, hdhat.2, hnr]
      _ ≤ |2 * U n ω + R n ω| := le_abs_self _
  -- Squeeze `0 ≤ P{ε ≤ dist} ≤ P{η ≤ ‖2Uₙ+Rₙ‖} → 0`.
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hthresh
    (Eventually.of_forall fun _ => zero_le)
    (Eventually.of_forall fun n => measure_mono (hsubset n))

/-- **van der Vaart, Theorem 5.7 with almost-everywhere exact near-maximality.**

This mirrors `mEstimator_consistent`, replacing its pointwise remainder
inequality and convergence premise by the exact comparison
`Mₙ(θ₀) ≤ Mₙ(θ̂ₙ)` almost everywhere for each `n`. -/
theorem mEstimator_consistent_ae_nearmax
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Θ : Type*} [MetricSpace Θ]
    {Mn : ℕ → Ω → Θ → ℝ} {M : Θ → ℝ} {θ₀ : Θ} {θhat : ℕ → Ω → Θ}
    {U : ℕ → Ω → ℝ}
    -- Measurable-envelope form of uniform convergence.
    (hU_dom : ∀ n ω θ, |Mn n ω θ - M θ| ≤ U n ω)
    -- Convergence of the measurable envelope.
    (hU_conv : TendstoInMeasure P U atTop (fun _ => (0 : ℝ)))
    -- Well-separated population maximum.
    (hsep : ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ θ,
      ε ≤ dist θ θ₀ → M θ ≤ M θ₀ - η)
    -- Exact empirical comparison, almost everywhere for each sample size.
    (hnear : ∀ n, ∀ᵐ ω ∂P, Mn n ω θ₀ ≤ Mn n ω (θhat n ω)) :
    ∀ ε > (0 : ℝ), Tendsto (fun n => P {ω | ε ≤ dist (θhat n ω) θ₀})
      atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨η, hη, hsepη⟩ := hsep ε hε
  have hconv : TendstoInMeasure P (fun n ω => 2 * U n ω) atTop (fun _ => (0 : ℝ)) := by
    have h2U := tendstoInMeasure_const_mul (2 : ℝ) hU_conv
    simpa using h2U
  have hthresh := tendstoInMeasure_iff_norm.mp hconv η hη
  have hsubset : ∀ n, {ω | ε ≤ dist (θhat n ω) θ₀}
      ≤ᵐ[P] {ω | η ≤ ‖(2 * U n ω) - 0‖} := by
    intro n
    filter_upwards [hnear n] with ω hnearω
    intro hω
    change ε ≤ dist (θhat n ω) θ₀ at hω
    change η ≤ ‖(2 * U n ω) - 0‖
    rw [Real.norm_eq_abs, sub_zero]
    have hsep_ineq := hsepη (θhat n ω) hω
    have hd0 := abs_le.mp (hU_dom n ω θ₀)
    have hdhat := abs_le.mp (hU_dom n ω (θhat n ω))
    calc
      η ≤ 2 * U n ω := by
        linarith [hsep_ineq, hd0.1, hdhat.2, hnearω]
      _ ≤ |2 * U n ω| := le_abs_self _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hthresh
    (Eventually.of_forall fun _ => zero_le)
    (Eventually.of_forall fun n => measure_mono_ae (hsubset n))

/-- **van der Vaart, Theorem 5.9 (consistency of Z-estimators).**

Let `Ψₙ` be random vector-valued functions dominated by a measurable envelope `Uₙ`
(`hU_dom`) with `Uₙ →ₚ 0` (`hU_conv`), the surrogate for vdV's `sup_θ‖Ψₙ−Ψ‖ →ₚ 0`.
Suppose the limit `Ψ` vanishes at `θ₀` (`hΨ0`) and is well-separated from `0` off every
`ε`-ball (`hsep`). Then any near-zero sequence `θ̂ₙ` with `‖Ψₙ(θ̂ₙ)‖ →ₚ 0` (`hnear`)
is consistent: `θ̂ₙ →ₚ θ₀`.

The proof is the vdV reduction to Theorem 5.7 with `Mₙ := −‖Ψₙ‖`, `M := −‖Ψ‖`, the same
envelope `Uₙ`, and near-max slack `Rₙ := ‖Ψₙ(θ̂ₙ)‖`. -/
theorem zEstimator_consistent
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {Θ : Type*} [MetricSpace Θ]
    {F : Type*} [NormedAddCommGroup F]
    {Ψn : ℕ → Ω → Θ → F} {Ψ : Θ → F} {θ₀ : Θ} {θhat : ℕ → Ω → Θ}
    {U : ℕ → Ω → ℝ}
    -- USER-INPUT (hU_dom, hU_conv): sup_θ ‖Ψₙ(θ) − Ψ(θ)‖ → 0 in probability, phrased
    -- through a measurable envelope U (replaces the book's outer probability of the
    -- possibly non-measurable sup); vdV Thm 5.9
    (hU_dom : ∀ n ω θ, ‖Ψn n ω θ - Ψ θ‖ ≤ U n ω)
    (hU_conv : TendstoInMeasure P U atTop (fun _ => (0 : ℝ)))
    -- USER-INPUT: θ₀ is a zero of Ψ (implicit in the book's "well-separated zero");
    -- vdV Thm 5.9
    (hΨ0 : Ψ θ₀ = 0)
    -- USER-INPUT: the zero is well separated, inf_{d(θ,θ₀) ≥ ε} ‖Ψ(θ)‖ > 0; vdV Thm 5.9
    (hsep : ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ θ, ε ≤ dist θ θ₀ → η ≤ ‖Ψ θ‖)
    -- USER-INPUT: θ̂ₙ is a near-zero of Ψₙ, ‖Ψₙ(θ̂ₙ)‖ = o_P(1); vdV Thm 5.9
    (hnear : TendstoInMeasure P (fun n ω => ‖Ψn n ω (θhat n ω)‖) atTop (fun _ => (0 : ℝ))) :
    ∀ ε > (0 : ℝ), Tendsto (fun n => P {ω | ε ≤ dist (θhat n ω) θ₀}) atTop (𝓝 0) := by
  apply mEstimator_consistent (Mn := fun n ω θ => -‖Ψn n ω θ‖) (M := fun θ => -‖Ψ θ‖)
    (U := U) (R := fun n ω => ‖Ψn n ω (θhat n ω)‖)
  · -- envelope domination: `|(−‖Ψₙθ‖)−(−‖Ψθ‖)| = |‖Ψₙθ‖−‖Ψθ‖| ≤ ‖Ψₙθ−Ψθ‖ ≤ Uₙ`
    intro n ω θ
    rw [show (-‖Ψn n ω θ‖) - (-‖Ψ θ‖) = -(‖Ψn n ω θ‖ - ‖Ψ θ‖) from by ring, abs_neg]
    exact (abs_norm_sub_norm_le _ _).trans (hU_dom n ω θ)
  · -- `Uₙ →ₚ 0`
    exact hU_conv
  · -- well-separated maximum of `M = −‖Ψ‖`: off the `ε`-ball, `−‖Ψθ‖ ≤ 0 − η`
    intro ε hε
    obtain ⟨η, hη, hsepη⟩ := hsep ε hε
    refine ⟨η, hη, fun θ hθ => ?_⟩
    rw [hΨ0, norm_zero]
    linarith [hsepη θ hθ]
  · -- near-max slack: `−‖Ψₙθ₀‖ − ‖Ψₙθ̂ₙ‖ ≤ −‖Ψₙθ̂ₙ‖` since `‖Ψₙθ₀‖ ≥ 0`
    intro n ω
    change -‖Ψn n ω θ₀‖ - ‖Ψn n ω (θhat n ω)‖ ≤ -‖Ψn n ω (θhat n ω)‖
    linarith [norm_nonneg (Ψn n ω θ₀)]
  · -- `Rₙ = ‖Ψₙ(θ̂ₙ)‖ →ₚ 0`
    exact hnear

end AsymptoticStatistics.Consistency
