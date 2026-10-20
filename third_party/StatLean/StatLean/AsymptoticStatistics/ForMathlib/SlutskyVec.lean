module
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity
public import StatLean.AsymptoticStatistics.ForMathlib.Slutsky

@[expose] public section

/-!
# Vector deterministic-Slutsky / recentering bridge

For the k-extension of `semiparametric_convolution_theorem`
(`productMeasure_unbounded_pushforward_vec_target`), we need to swap the
parametric recentering term `ψ(curve(1/√n))` for the affine approximation
`ψ_proj_vec ((√n)⁻¹ • h)`. The two differ by `o((√n)⁻¹)` deterministically
(pathwise differentiability + first-order Taylor on the affine functional),
so vector weak convergence of the recentered statistic is preserved across
the swap via a deterministic-shift Slutsky argument.

Headline declaration: `vec_slutsky_recentering`.
-/

open MeasureTheory Filter Topology

namespace AsymptoticStatistics.ForMathlib

/-- **Vector deterministic-Slutsky / recentering bridge.**

If `(P n).map (fun ω => Xn n ω + cn n) ⇝ L` weakly on `E` and the
deterministic shift `cn → 0`, then `(P n).map (Xn n) ⇝ L` as well.

Used in `productMeasure_unbounded_pushforward_vec_target` to swap the
parametric recentering `ψ(curve(1/√n))` for the affine approximation
`ψ_proj_vec ((√n)⁻¹ • h)`: the deterministic difference vanishes by
pathwise differentiability of `ψ` plus first-order Taylor on the affine
`ψ_proj_vec`.

Proof idea: composition of `WeakConverges.map` for the continuous shift
functor with the limit identification under `Tendsto cn 0`. -/
theorem vec_slutsky_recentering
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [SeminormedAddCommGroup E]
    [BorelSpace E] [SecondCountableTopology E] [Nonempty E]
    [MeasurableAdd E] [MeasurableSub E]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {Xn : ∀ n, Ω n → E} {cn : ℕ → E}
    {L : Measure E} [IsProbabilityMeasure L]
    (hXn_meas : ∀ n, AEMeasurable (Xn n) (P n))
    (h_weak : WeakConverges (fun n => (P n).map (fun ω => Xn n ω + cn n)) L)
    (h_det : Filter.Tendsto cn Filter.atTop (𝓝 0)) :
    WeakConverges (fun n => (P n).map (fun ω => Xn n ω)) L := by
  -- Apply scalar Slutsky-by-distance with `X n := Xn n + cn n` and `Y n := Xn n`.
  -- The deterministic shift gives `dist (Xn n ω + cn n) (Xn n ω) = ‖cn n‖`, which is
  -- independent of `ω`. Since `cn n → 0`, for every `ε > 0` we have `‖cn n‖ < ε`
  -- eventually, so the level set `{ω | ε ≤ ‖cn n‖}` is empty and has zero `P n`-mass.
  refine AsymptoticStatistics.WeakConverges.slutsky_of_tendstoInMeasure_dist
    (X := fun n ω => Xn n ω + cn n) (Y := fun n ω => Xn n ω)
    (fun n => (hXn_meas n).add_const _) hXn_meas h_weak ?_
  intro ε hε
  -- Show eventually-zero: pick `n` large enough that `‖cn n‖ < ε`.
  have h_norm_tendsto : Filter.Tendsto (fun n => ‖cn n‖) Filter.atTop (𝓝 0) := by
    have h := (continuous_norm.tendsto (0 : E)).comp h_det
    simpa using! h
  have h_eventually : ∀ᶠ n in Filter.atTop, ‖cn n‖ < ε := by
    have := (Metric.tendsto_nhds.mp h_norm_tendsto) ε hε
    filter_upwards [this] with n hn
    rw [Real.dist_eq, sub_zero] at hn
    exact lt_of_le_of_lt (le_abs_self _) hn
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [h_eventually] with n hn
  -- For this `n`, the set is empty.
  have h_set_empty : {ω : Ω n | ε ≤ dist (Xn n ω + cn n) (Xn n ω)} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
    have h_dist : dist (Xn n ω + cn n) (Xn n ω) = ‖cn n‖ := dist_self_add_left _ _
    rw [h_dist]
    exact hn
  rw [h_set_empty, MeasureTheory.measureReal_empty]

end AsymptoticStatistics.ForMathlib
