module
public import Mathlib.Probability.Distributions.Gaussian.Real
public import StatLean.AsymptoticStatistics.ForMathlib.BowlShaped

@[expose] public section

/-!
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junwei Lu, Claude Opus 4.7
-/

/-!
# Variance-monotonicity of Gaussian integrals against a bowl-shaped loss

For a `BowlShaped` (subconvex, symmetric, measurable) loss `ℓ : ℝ → ℝ≥0∞`,
the integral `∫⁻ u, ℓ u ∂(gaussianReal 0 v)` is non-decreasing in `v`.

This is the **scalar Anderson Bypass** for the LAM lower bound:
instead of going through PSD-monotone Anderson on matrix covariances, we
exploit the scalar nature of the LAM problem and the change-of-variables
`(c • _) ⋆ N(0, v) = N(0, c² v)` (Mathlib's `gaussianReal_map_const_mul`).

## Main results

* `BowlShaped.le_smul_of_one_le`: if `1 ≤ c`, then `ℓ x ≤ ℓ (c • x)`.
  Reduces to a one-step convex combination `x = c⁻¹ • (c • x) + (1 − c⁻¹) • 0`
  inside the sublevel set `{y | ℓ y ≤ ℓ (c • x)}`.

* `gaussianReal_lintegral_monotone_in_var_of_bowlShaped`:
  `v₁ ≤ v₂ ⇒ ∫⁻ ℓ dN(0, v₁) ≤ ∫⁻ ℓ dN(0, v₂)`.

This is the analytic engine of vdV §25.3 (b)'s "PSD-monotone Anderson"
reduction in the scalar LAM lower bound (`StatLean/AsymptoticStatistics/LowerBounds/LAM.lean`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace AsymptoticStatistics.ForMathlib


end AsymptoticStatistics.ForMathlib

namespace ProbabilityTheory

open AsymptoticStatistics
open AsymptoticStatistics

/-- **Variance-monotone Gaussian integral against a bowl-shaped loss.**

For a bowl-shaped (subconvex, symmetric) loss `ℓ : ℝ → ℝ≥0∞` and any
non-negative variances `v₁ ≤ v₂`,
`∫⁻ u, ℓ u ∂(gaussianReal 0 v₁) ≤ ∫⁻ u, ℓ u ∂(gaussianReal 0 v₂)`.

This is the scalar Anderson Bypass: rescaling by `c := √(v₂ / v₁) ≥ 1`
maps `gaussianReal 0 v₁` to `gaussianReal 0 v₂` (Mathlib's
`gaussianReal_map_const_mul`), then `BowlShaped.le_smul_of_one_le`
delivers the pointwise inequality `ℓ x ≤ ℓ (c * x)`.

The degenerate case `v₁ = 0` (Dirac at `0`) reduces to
`ℓ 0 ≤ ∫⁻ ℓ dN(0, v₂)`, which holds because `ℓ` attains its minimum at
`0` (`BowlShaped.le_at_zero`) and `gaussianReal 0 v₂` is a probability
measure. -/
theorem gaussianReal_lintegral_monotone_in_var_of_bowlShaped
    {ℓ : ℝ → ℝ≥0∞} (hℓ : BowlShaped ℓ)
    {v₁ v₂ : ℝ≥0} (hv : v₁ ≤ v₂) :
    ∫⁻ u, ℓ u ∂(gaussianReal 0 v₁) ≤ ∫⁻ u, ℓ u ∂(gaussianReal 0 v₂) := by
  by_cases hv₁ : v₁ = 0
  · -- Degenerate: gaussianReal 0 0 = δ_0.
    subst hv₁
    rw [gaussianReal_zero_var, lintegral_dirac' (a := (0 : ℝ)) hℓ.measurable]
    -- Goal: ℓ 0 ≤ ∫⁻ u, ℓ u ∂(gaussianReal 0 v₂)
    have h_const : ∫⁻ _ : ℝ, ℓ 0 ∂(gaussianReal 0 v₂) = ℓ 0 := by
      rw [lintegral_const]; simp
    calc ℓ 0
        = ∫⁻ _ : ℝ, ℓ 0 ∂(gaussianReal 0 v₂) := h_const.symm
      _ ≤ ∫⁻ u, ℓ u ∂(gaussianReal 0 v₂) :=
          lintegral_mono fun u => hℓ.le_at_zero u
  · -- Non-degenerate: v₁ > 0, set c := √(v₂/v₁) ≥ 1.
    have hv₁_pos : (0 : ℝ≥0) < v₁ :=
      lt_of_le_of_ne (zero_le (a := v₁)) (Ne.symm hv₁)
    have hv₁_pos_real : (0 : ℝ) < (v₁ : ℝ) := by exact_mod_cast hv₁_pos
    have hv₂_nn_real : (0 : ℝ) ≤ (v₂ : ℝ) := NNReal.coe_nonneg _
    have h_ratio_nn : (0 : ℝ) ≤ (v₂ : ℝ) / (v₁ : ℝ) :=
      div_nonneg hv₂_nn_real hv₁_pos_real.le
    set c : ℝ := Real.sqrt ((v₂ : ℝ) / (v₁ : ℝ)) with hc_def
    have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
    have hc_sq : c ^ 2 = (v₂ : ℝ) / (v₁ : ℝ) := by
      rw [hc_def, sq, ← Real.sqrt_mul h_ratio_nn, Real.sqrt_mul_self h_ratio_nn]
    have h_one_le_c : (1 : ℝ) ≤ c := by
      have h_one_le_ratio : (1 : ℝ) ≤ (v₂ : ℝ) / (v₁ : ℝ) := by
        rw [le_div_iff₀ hv₁_pos_real, one_mul]; exact_mod_cast hv
      have : Real.sqrt 1 ≤ c := by
        rw [hc_def]; exact Real.sqrt_le_sqrt h_one_le_ratio
      simpa using this
    -- gaussianReal 0 v₁ pushed through (c * ·) is gaussianReal 0 v₂.
    have h_map : (gaussianReal 0 v₁).map (c * ·) = gaussianReal 0 v₂ := by
      rw [gaussianReal_map_const_mul, mul_zero]
      congr 1
      apply NNReal.coe_injective
      change c ^ 2 * (v₁ : ℝ) = (v₂ : ℝ)
      rw [hc_sq, div_mul_cancel₀ _ (ne_of_gt hv₁_pos_real)]
    -- ∫ ℓ dN(0, v₂) = ∫ ℓ(c * x) dN(0, v₁).
    have h_meas_cmul : Measurable (fun x : ℝ => c * x) :=
      measurable_const.mul measurable_id
    have h_change : ∫⁻ u, ℓ u ∂(gaussianReal 0 v₂)
        = ∫⁻ x, ℓ (c * x) ∂(gaussianReal 0 v₁) := by
      rw [← h_map, lintegral_map hℓ.measurable h_meas_cmul]
    rw [h_change]
    refine lintegral_mono (fun x => ?_)
    -- Pointwise: ℓ x ≤ ℓ (c * x). For E = ℝ, c • x = c * x by `rfl`.
    exact hℓ.le_smul_of_one_le h_one_le_c x

end ProbabilityTheory
