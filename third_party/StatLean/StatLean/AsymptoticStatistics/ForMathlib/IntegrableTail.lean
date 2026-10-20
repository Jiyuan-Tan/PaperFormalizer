module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

@[expose] public section

/-!
Asymptotic Statistics — `L¹`-tail integrals vanish.

Theorem-agnostic DCT consequence: if `h ∈ L¹(μ)`, `f : α → ℝ` is measurable, and
`t n → ∞`, then the tail integral of `h` on `{y | t n < f y}` tends to `0`.

Used in Theorem 7.2 Step 6b (bounding `∫ g² · 1_{g² > nε²/2} · p dμ → 0`) and
expected to resurface in Step 6a (controlling `g²`-tails under a truncation).

## Contents

* `tendsto_setIntegral_tail_of_integrable` — the main lemma.
-/

open MeasureTheory Filter Topology

namespace AsymptoticStatistics
namespace ForMathlib

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **L¹ tail integrals vanish along a diverging threshold.**

If `h : α → ℝ` is integrable, `f : α → ℝ` is measurable, and `t : ℕ → ℝ` satisfies
`t n → ∞`, then `∫_{y : f y > t n} h(x) dμ → 0` as `n → ∞`.

**Proof.** DCT on `F n x := {y | t n < f y}.indicator h x`:
* Dominator: `|h|`, integrable by `Integrable.abs`.
* Pointwise: for each `x`, `f x` is a finite real, so `t n > f x` eventually,
  which forces `x ∉ {y | t n < f y}` and hence the indicator vanishes eventually. -/
lemma tendsto_setIntegral_tail_of_integrable
    {h : α → ℝ} (hh : Integrable h μ)
    {f : α → ℝ} (hf : Measurable f)
    {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) :
    Tendsto (fun n : ℕ => ∫ x in {y | t n < f y}, h x ∂μ) atTop (𝓝 0) := by
  have hS_meas : ∀ n : ℕ, MeasurableSet {y | t n < f y} :=
    fun n => measurableSet_lt measurable_const hf
  -- Convert set integrals to indicator integrals.
  suffices h_ind : Tendsto
      (fun n : ℕ => ∫ x, {y | t n < f y}.indicator h x ∂μ) atTop (𝓝 0) by
    refine h_ind.congr (fun n => ?_)
    exact MeasureTheory.integral_indicator (hS_meas n)
  -- DCT ingredients.
  have h_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x => {y | t n < f y}.indicator h x) μ :=
    fun n => hh.aestronglyMeasurable.indicator (hS_meas n)
  have h_bound : ∀ n : ℕ, ∀ᵐ x ∂μ,
      ‖{y | t n < f y}.indicator h x‖ ≤ |h x| := by
    intro n
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ {y | t n < f y}
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]
    · rw [Set.indicator_of_notMem hx, norm_zero]; exact abs_nonneg _
  have h_ptwise : ∀ᵐ x ∂μ,
      Tendsto (fun n : ℕ => {y | t n < f y}.indicator h x) atTop (𝓝 0) := by
    refine Filter.Eventually.of_forall fun x => ?_
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [ht.eventually_gt_atTop (f x)] with n hn
    symm
    rw [Set.indicator_of_notMem]
    simp only [Set.mem_setOf_eq, not_lt]
    exact hn.le
  have h_DCT :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (F := fun n : ℕ => fun x => {y | t n < f y}.indicator h x)
      (f := fun _ => (0 : ℝ))
      (bound := fun x => |h x|)
      h_meas hh.abs h_bound h_ptwise
  simpa using h_DCT

end ForMathlib
end AsymptoticStatistics
