module
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# A centred Gaussian random variable is sub-Gaussian with proxy variance = its variance

This file is a small, reusable bridge between the Gaussian distribution API and the
sub-Gaussian MGF API in Mathlib.

Mathematical content.  If `Y : Ω → ℝ` has law `N(0, σ²)` under `μ` (i.e.
`μ.map Y = gaussianReal 0 σ2`), then `Y` is *sub-Gaussian* with proxy variance `σ²`:
its moment-generating function satisfies `mgf Y μ t ≤ exp(σ² t² / 2)` for every `t`,
and `ω ↦ exp(t·Y ω)` is integrable for every `t`.  For a centred Gaussian the bound
is in fact an *equality* — the mean-`0` Gaussian MGF is `exp(σ² t² / 2)` — so the
sub-Gaussian proxy variance is sharp and equal to the true variance.

This supplies the Gaussian-to-sub-Gaussian connection for the Brownian-bridge
chaining argument: the increments of the isonormal process are
Gaussian, and via this lemma they feed the generic sub-Gaussian maximal inequality
`expectation_iSup_abs_le_of_subgaussian` and the concentration bound
`HasSubgaussianMGF.measure_ge_le`.

Bricks used:
* `ProbabilityTheory.mgf_gaussianReal` — closed form of the Gaussian MGF.
* `ProbabilityTheory.integrable_exp_mul_gaussianReal` — integrability of `exp(t·x)`
  against a Gaussian, pulled back through the law via `integrable_map_measure`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- A random variable with centred Gaussian law `N(0, σ²)` is sub-Gaussian with proxy
variance equal to its variance `σ²`.

The measurability hypothesis `hY : AEMeasurable Y μ` is needed to pull integrability of `exp(t·x)`
back through the law `μ.map Y` via `integrable_map_measure`.

The hypothesis `h` gives the mean-`0` Gaussian law `μ.map Y = gaussianReal 0 σ2`,
the genuine mathematical content (centred Gaussian of variance `σ²`).

For a centred Gaussian the MGF is exactly `exp(σ² t² / 2)`, so the sub-Gaussian bound
`mgf Y μ t ≤ exp(σ² t² / 2)` holds with equality. -/
theorem hasSubgaussianMGF_of_map_eq_gaussianReal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {Y : Ω → ℝ} {σ2 : ℝ≥0}
    (hY : AEMeasurable Y μ) (h : μ.map Y = ProbabilityTheory.gaussianReal 0 σ2) :
    ProbabilityTheory.HasSubgaussianMGF Y σ2 μ where
  integrable_exp_mul t := by
    -- `exp(t·x)` is integrable against `gaussianReal 0 σ2`; pull back through `μ.map Y = …`.
    have hint : Integrable (fun x => Real.exp (t * x)) (μ.map Y) := by
      rw [h]; exact integrable_exp_mul_gaussianReal t
    -- `integrable_map_measure` turns `Integrable g (μ.map Y)` into `Integrable (g ∘ Y) μ`.
    have hg : AEStronglyMeasurable (fun x => Real.exp (t * x)) (μ.map Y) := by
      rw [h]; exact (integrable_exp_mul_gaussianReal t).aestronglyMeasurable
    exact (integrable_map_measure hg hY).1 hint
  mgf_le t := by
    -- The mean-`0` Gaussian MGF is `exp(0·t + σ2·t²/2) = exp(σ2·t²/2)`, so the bound is equality.
    rw [mgf_gaussianReal h t]
    simp

/-- **Monotonicity in the proxy variance.** A sub-Gaussian random variable with proxy
variance `c` is also sub-Gaussian with any larger proxy variance `c'`: the MGF bound
`mgf Y μ t ≤ exp(c·t²/2)` only weakens when `c` grows to `c'`.  Mean-agnostic: the
sub-Gaussian definition forces `E[Y] = 0` regardless of the proxy variance, and the
integrability requirement is unchanged.

The order hypothesis `hcc' : c ≤ c'` makes the proxy bound monotone. -/
theorem HasSubgaussianMGF.mono_proxy {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {Y : Ω → ℝ} {c c' : ℝ≥0} (h : HasSubgaussianMGF Y c μ) (hcc' : c ≤ c') :
    HasSubgaussianMGF Y c' μ where
  integrable_exp_mul t := h.integrable_exp_mul t
  mgf_le t := le_trans (h.mgf_le t) (Real.exp_le_exp.mpr (by
    have hcoe : (c : ℝ) ≤ (c' : ℝ) := by exact_mod_cast hcc'
    nlinarith [sq_nonneg t, hcoe]))

end ProbabilityTheory
