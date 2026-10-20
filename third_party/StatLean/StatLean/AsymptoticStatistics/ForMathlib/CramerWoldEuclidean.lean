module
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import StatLean.AsymptoticStatistics.ForMathlib.Contiguity

@[expose] public section

/-!
# Cramér–Wold device on `EuclideanSpace ℝ (Fin k)`

The plain-`EuclideanSpace` analogue of
`AsymptoticStatistics.ForMathlib.cramerWold_weakConverges` (which is typed for
`ℝ × EuclideanSpace ℝ (Fin m)`): joint weak convergence on
`EuclideanSpace ℝ (Fin k)` is determined by the per-direction linear projections
`v ↦ ⟪lam, v⟫_ℝ`.

Since `EuclideanSpace ℝ (Fin k)` is *already* a finite-dimensional real
inner-product space, no `WithLp` bridge is needed: Mathlib's Lévy continuity
theorem `ProbabilityMeasure.tendsto_of_tendsto_charFun` applies directly, and the
characteristic function at a direction `v` equals the scalar characteristic
function of the projected measure `μ.map ⟪v, ·⟫` at `1`.

## Public API

* `cramerWold_weakConverges_euclidean` — the Cramér–Wold device.
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal InnerProductSpace

namespace AsymptoticStatistics.ForMathlib

namespace CramerWoldEuclidean

variable {k : ℕ}

/-- Characteristic-function bridge: at a direction `v`, the characteristic
function of `μ` equals the scalar characteristic function of the projected
measure `μ.map (⟪v, ·⟫_ℝ)` evaluated at `1`. -/
lemma charFun_eq_charFun_map_inner
    (μ : Measure (EuclideanSpace ℝ (Fin k))) [SFinite μ]
    (v : EuclideanSpace ℝ (Fin k)) :
    charFun μ v = charFun (μ.map (fun x => ⟪v, x⟫_ℝ)) 1 := by
  -- Match `charFun`'s `⟪x, v⟫` orientation by commuting the projection.
  have h_proj_eq : (fun x : EuclideanSpace ℝ (Fin k) => ⟪v, x⟫_ℝ)
      = (fun x => ⟪x, v⟫_ℝ) := by
    funext x; rw [real_inner_comm]
  rw [h_proj_eq, charFun_apply, charFun_apply_real]
  have h_meas : Measurable (fun x : EuclideanSpace ℝ (Fin k) => ⟪x, v⟫_ℝ) := by
    fun_prop
  have h_int_meas : AEStronglyMeasurable
      (fun y : ℝ => Complex.exp ((1 : ℝ) * y * I)) (μ.map (fun x => ⟪x, v⟫_ℝ)) :=
    Continuous.aestronglyMeasurable (by fun_prop)
  rw [integral_map h_meas.aemeasurable h_int_meas]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [Complex.ofReal_one, one_mul]

end CramerWoldEuclidean

/-- **Cramér–Wold device on `EuclideanSpace ℝ (Fin k)`.**

If, for every direction `lam : EuclideanSpace ℝ (Fin k)`, the push-forward
`(μ_n).map (fun v ↦ ⟪lam, v⟫_ℝ)` weakly converges to `μ.map (fun v ↦ ⟪lam, v⟫_ℝ)`,
then `μ_n` weakly converges to `μ`.

Proof: per-direction Lévy on `ℝ` gives scalar `charFun` convergence of the
projected measures at `1`; via `charFun_eq_charFun_map_inner` this is exactly
pointwise `charFun` convergence on `EuclideanSpace ℝ (Fin k)`, whence the Lévy
continuity theorem yields joint weak convergence. -/
theorem cramerWold_weakConverges_euclidean
    {k : ℕ}
    {μ_n : ℕ → Measure (EuclideanSpace ℝ (Fin k))}
    {μ : Measure (EuclideanSpace ℝ (Fin k))}
    [∀ n, IsProbabilityMeasure (μ_n n)] [IsProbabilityMeasure μ]
    (h_per_dir : ∀ (lam : EuclideanSpace ℝ (Fin k)),
      WeakConverges
        (fun n => (μ_n n).map (fun v => ⟪lam, v⟫_ℝ))
        (μ.map (fun v => ⟪lam, v⟫_ℝ))) :
    WeakConverges μ_n μ := by
  classical
  let pn : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) :=
    fun n => ⟨μ_n n, inferInstance⟩
  let pμ : ProbabilityMeasure (EuclideanSpace ℝ (Fin k)) := ⟨μ, inferInstance⟩
  -- Lévy: pointwise `charFun` convergence ⇒ weak convergence.
  have h_conv : Tendsto pn atTop (𝓝 pμ) := by
    refine ProbabilityMeasure.tendsto_of_tendsto_charFun ?_
    intro v
    -- Probability-measure structure on the projected (scalar) measures.
    haveI h_prob_n : ∀ n, IsProbabilityMeasure ((μ_n n).map (fun x => ⟪v, x⟫_ℝ)) :=
      fun n => Measure.isProbabilityMeasure_map (by fun_prop)
    haveI h_prob_μ : IsProbabilityMeasure (μ.map (fun x => ⟪v, x⟫_ℝ)) :=
      Measure.isProbabilityMeasure_map (by fun_prop)
    let qn : ℕ → ProbabilityMeasure ℝ :=
      fun n => ⟨(μ_n n).map (fun x => ⟪v, x⟫_ℝ), h_prob_n n⟩
    let qμ : ProbabilityMeasure ℝ := ⟨μ.map (fun x => ⟪v, x⟫_ℝ), h_prob_μ⟩
    -- Per-direction weak convergence on ℝ (hypothesis, since `⟪v, ·⟫ = ⟪v, ·⟫`).
    have h_proj_conv : Tendsto qn atTop (𝓝 qμ) := by
      rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
      intro f
      change Tendsto (fun n => ∫ x, f x ∂((μ_n n).map (fun x => ⟪v, x⟫_ℝ))) _ _
      exact h_per_dir v f
    -- Lévy on ℝ: scalar `charFun` convergence at `1`.
    have h_cf : Tendsto (fun n => charFun ((qn n : Measure ℝ)) 1) atTop
        (𝓝 (charFun ((qμ : Measure ℝ)) 1)) :=
      (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp h_proj_conv) 1
    -- Bridge back to `charFun` on `EuclideanSpace ℝ (Fin k)`.
    have hb_n : ∀ n, charFun ((pn n : Measure (EuclideanSpace ℝ (Fin k)))) v
        = charFun ((qn n : Measure ℝ)) 1 := fun n =>
      CramerWoldEuclidean.charFun_eq_charFun_map_inner (μ_n n) v
    have hb_μ : charFun ((pμ : Measure (EuclideanSpace ℝ (Fin k)))) v
        = charFun ((qμ : Measure ℝ)) 1 :=
      CramerWoldEuclidean.charFun_eq_charFun_map_inner μ v
    rw [hb_μ]
    simp_rw [hb_n]
    exact h_cf
  -- Convert `ProbabilityMeasure` convergence to `WeakConverges`.
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h_conv
  intro f
  exact h_conv f

end AsymptoticStatistics.ForMathlib
