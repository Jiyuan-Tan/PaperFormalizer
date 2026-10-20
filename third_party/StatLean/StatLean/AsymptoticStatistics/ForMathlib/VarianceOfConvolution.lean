module
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
Variance of convolution of measures on `ℝ`.

For probability measures `μ, ν` on `ℝ` with finite second moment, the
variance of `μ ∗ ν` decomposes additively:

  `Var[id; μ ∗ ν] = Var[id; μ] + Var[id; ν]`,

so in particular `Var[id; μ] ≤ Var[id; μ ∗ ν]` whenever both factors
have finite second moment. We package the inequality form
`variance_id_le_variance_id_conv` directly from `MemLp id 2 μ` plus
`MemLp id 2 (μ ∗ ν)` (which entails `MemLp id 2 ν` via `memLp_of_conv_right`).

Used by `AsymptoticStatistics.LowerBounds.Convolution.semiparametric_convolution_theorem_regular`
to derive the variance lower bound `‖IF_eff‖² ≤ Var(L)` from the per-`m`
char-fn factorisation (instantiated at `m = 1` with `g_P 0 := IF_eff/‖IF_eff‖`).
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ENNReal NNReal

namespace AsymptoticStatistics.ForMathlib.VarianceOfConvolution

/-- *Marginal `MemLp` from convolution `MemLp`.*

If `μ` and `μ ∗ ν` have finite second moment (and both are probability
measures on `ℝ`), then so does `ν`. -/
theorem memLp_of_conv_right
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MeasureTheory.MemLp (id : ℝ → ℝ) 2 μ)
    (hL : MeasureTheory.MemLp (id : ℝ → ℝ) 2 (μ ∗ ν)) :
    MeasureTheory.MemLp (id : ℝ → ℝ) 2 ν := by
  -- Step 1: rewrite `MemLp id 2 (μ ∗ ν)` as `MemLp (· + ·) 2 (μ.prod ν)`.
  have h_conv_def : (μ ∗ ν) = (μ.prod ν).map (fun p : ℝ × ℝ => p.1 + p.2) := rfl
  rw [h_conv_def] at hL
  have hL_prod : MemLp (fun p : ℝ × ℝ => p.1 + p.2) 2 (μ.prod ν) := by
    rw [memLp_map_measure_iff (by fun_prop) (by fun_prop)] at hL
    -- `id ∘ (· + ·) = (· + ·)`.
    simpa [Function.comp_def] using hL
  -- Step 2: `MemLp (fun p => p.1) 2 (μ.prod ν)` from `hμ`.
  have hFst : MemLp (fun p : ℝ × ℝ => p.1) 2 (μ.prod ν) :=
    hμ.comp_fst ν
  -- Step 3: `MemLp (fun p => p.2) 2 (μ.prod ν)` via subtraction
  -- `p.2 = (p.1 + p.2) - p.1`.
  have hSnd_prod : MemLp (fun p : ℝ × ℝ => p.2) 2 (μ.prod ν) := by
    have : (fun p : ℝ × ℝ => p.2) =
        (fun p : ℝ × ℝ => (p.1 + p.2) - p.1) := by
      funext p; ring
    rw [this]
    exact hL_prod.sub hFst
  -- Step 4: pass marginal `MemLp` from `μ.prod ν` to `ν` via
  -- `(μ.prod ν).map Prod.snd = ν` (since `μ` is probability).
  have h_snd_map : (μ.prod ν).map Prod.snd = ν := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have h_id_eq : (id : ℝ → ℝ) ∘ Prod.snd = (fun p : ℝ × ℝ => p.2) := rfl
  rw [← h_snd_map, memLp_map_measure_iff (by fun_prop) (by fun_prop), h_id_eq]
  exact hSnd_prod

/-- *Variance of an additive convolution decomposes additively.*

For probability measures `μ, ν` on `ℝ` with `id ∈ L²`, the variance of
the convolution `μ ∗ ν` equals the sum of the individual variances. -/
theorem variance_id_conv
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MeasureTheory.MemLp (id : ℝ → ℝ) 2 μ)
    (hν : MeasureTheory.MemLp (id : ℝ → ℝ) 2 ν) :
    ProbabilityTheory.variance id (μ ∗ ν) =
      ProbabilityTheory.variance id μ + ProbabilityTheory.variance id ν := by
  -- `Measure.conv = (μ.prod ν).map (fun p : ℝ × ℝ => p.1 + p.2)`.
  -- So `Var[id; μ ∗ ν] = Var[id; (μ.prod ν).map (· + ·)]
  --                    = Var[fun p => p.1 + p.2; μ.prod ν]`
  -- by `variance_id_map`, and the right-hand side equals
  -- `Var[id; μ] + Var[id; ν]` by `variance_add_prod`.
  have h_eq : (μ ∗ ν) = (μ.prod ν).map (fun p : ℝ × ℝ => p.1 + p.2) := rfl
  rw [h_eq, variance_id_map (by fun_prop)]
  have h_fun :
      (fun p : ℝ × ℝ => p.1 + p.2) =
        (fun p : ℝ × ℝ => (id : ℝ → ℝ) p.1 + (id : ℝ → ℝ) p.2) := rfl
  rw [h_fun]
  exact variance_add_prod hμ hν

/-- *Variance of a measure is `≤` variance of its convolution with another
probability measure.*

For probability measures `μ, ν` on `ℝ` with `id ∈ L²` (in `μ` and in
`μ ∗ ν`), `Var[id; μ] ≤ Var[id; μ ∗ ν]`. The hypothesis on the convolution
is what one usually has at hand (the limit law's second moment); we
internally extract `MemLp id 2 ν` via `memLp_of_conv_right`. -/
theorem variance_id_le_variance_id_conv
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MeasureTheory.MemLp (id : ℝ → ℝ) 2 μ)
    (hL : MeasureTheory.MemLp (id : ℝ → ℝ) 2 (μ ∗ ν)) :
    ProbabilityTheory.variance id μ ≤ ProbabilityTheory.variance id (μ ∗ ν) := by
  have hν : MeasureTheory.MemLp (id : ℝ → ℝ) 2 ν :=
    memLp_of_conv_right μ ν hμ hL
  rw [variance_id_conv μ ν hμ hν]
  exact le_add_of_nonneg_right (ProbabilityTheory.variance_nonneg _ _)

end AsymptoticStatistics.ForMathlib.VarianceOfConvolution
