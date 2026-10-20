module
public import Mathlib.MeasureTheory.Function.UniformIntegrable

@[expose] public section

/-!
# Dominated convergence in `L²`

A reusable finite-measure-space form of dominated convergence for the
`eLpNorm`: pointwise convergence under one common `L²` dominator implies
convergence in `L²`.
-/

open Filter Topology
open scoped ENNReal

namespace MeasureTheory

/-- Pointwise convergence under a common `L²` dominator implies convergence
in `L²` on a finite measure space. -/
theorem tendsto_eLpNorm_sub_zero_of_pointwise_of_memLp_dominator
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    {u : ℕ → Ω → ℝ} {v Ψ : Ω → ℝ}
    (hu_meas : ∀ m, AEStronglyMeasurable (u m) P)
    (hΨ : MemLp Ψ 2 P)
    (hu_dom : ∀ m x, ‖u m x‖ ≤ ‖Ψ x‖)
    (huv : ∀ x,
      Tendsto (fun m => u m x) atTop (𝓝 (v x))) :
    Tendsto
      (fun m => eLpNorm (fun x => u m x - v x) 2 P)
      atTop (𝓝 0) := by
  have hv_meas : AEStronglyMeasurable v P :=
    aestronglyMeasurable_of_tendsto_ae atTop hu_meas
      (Eventually.of_forall huv)
  have hv_dom : ∀ x, ‖v x‖ ≤ ‖Ψ x‖ := fun x =>
    le_of_tendsto' ((continuous_norm.tendsto _).comp (huv x))
      (fun m => hu_dom m x)
  have hv_mem : MemLp v 2 P :=
    hΨ.of_le hv_meas (Eventually.of_forall hv_dom)
  have hΨ_ui : UnifIntegrable (fun _ : ℕ => Ψ) 2 P :=
    unifIntegrable_const (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hΨ
  have hu_ui : UnifIntegrable u 2 P := by
    intro ε hε
    obtain ⟨δ, hδ, hbound⟩ := hΨ_ui hε
    refine ⟨δ, hδ, fun m s hs hPs => ?_⟩
    refine (eLpNorm_mono (fun x => ?_)).trans (hbound m s hs hPs)
    by_cases hx : x ∈ s
    · simpa [Set.indicator_of_mem hx] using hu_dom m x
    · simp [Set.indicator_of_notMem hx]
  simpa only [Pi.sub_apply] using!
    tendsto_Lp_finite_of_tendsto_ae (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) hu_meas hv_mem hu_ui
      (Eventually.of_forall huv)

end MeasureTheory
