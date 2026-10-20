module
public import StatLean.AsymptoticStatistics.ForMathlib.DifferentiableInProbability
public import StatLean.AsymptoticStatistics.EmpiricalProcess.ZEstimatorNormality

@[expose] public section

/-!
# Probability differentiability adapter for M-estimators

This file is the thin subject-layer bridge from the generic local-scale `L²`
theorem to the exact `distL2` premise consumed by the fixed-direction
empirical-process adapters for vdV Theorems 5.23 and 5.39.
-/

namespace AsymptoticStatistics.MEstimator

open MeasureTheory Filter EmpiricalProcess
open scoped ENNReal Topology RealInnerProductSpace

/-- The samplewise continuous-linear derivative canonically determined by the
coordinate family `mdot` used by the M-estimator empirical-process layer.

It bundles `mdot` with `psiVec` and takes the real inner-product functional.
Thus the derivative content is fixed by `mdot`; there is no free derivative or
compatibility equality for callers to supply.  Edge behavior: for `d = 0` this
is the unique zero functional on the zero-dimensional Euclidean space. -/
noncomputable def mdotProbabilityDerivative {d : ℕ} {Ω : Type*}
    (mdot : Fin d → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    (ω : Ω) : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
  innerSL ℝ (psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω)

/-- Convert generic fixed-direction local-scale `L²(P)` convergence into the
exact `distL2` premise of
`linearization_marginal_tendstoInProbZero_of_distL2`.

The target inner product is obtained from `mdotProbabilityDerivative` by
symmetry of the real inner product, not by assuming a provider equality.
Neither score measurability nor score `L²` membership is an input: both are
consequences of probability differentiability plus the common envelope. -/
theorem distL2_localScale_mdot_of_differentiableInProbabilityAt
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (m : EuclideanSpace ℝ (Fin d) → Ω → ℝ)
    (mdot : Fin d → Ω → ℝ) (θ₀ : EuclideanSpace ℝ (Fin d))
    -- This premise follows from the DQM/log bridge.
    (hdiff : DifferentiableInProbabilityAt P m
      (mdotProbabilityDerivative mdot θ₀) θ₀)
    -- Minimal measure-relative measurability of the criterion sections.
    (hm_meas : ∀ θ, AEStronglyMeasurable (m θ) P)
    -- vdV 5.39's common local log-Lipschitz envelope in L2(P).
    (menv : Ω → ℝ) (hmenv : MemLp menv 2 P)
    -- A nontrivial local neighborhood on which the envelope applies.
    (ρ : ℝ) (hρ : 0 < ρ)
    -- Pointwise local domination; moving spikes show this assumption is necessary.
    (henv : ∀ θ ∈ Metric.closedBall θ₀ ρ, ∀ ω,
      |m θ ω - m θ₀ ω| ≤ ‖menv ω‖ * ‖θ - θ₀‖)
    (h : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun n : ℕ => distL2 P
      (fun ω => Real.sqrt n *
        (m (θ₀ + (Real.sqrt n)⁻¹ • h) ω - m θ₀ ω))
      (fun ω => ⟪h,
        psiVec (fun _ : EuclideanSpace ℝ (Fin d) => mdot) θ₀ ω⟫))
      atTop (𝓝 0) := by
  have hL2 := hdiff.eLpNorm_localScale hm_meas menv hmenv ρ hρ henv h
  unfold EmpiricalProcess.distL2
  exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (by
    simpa only [mdotProbabilityDerivative, innerSL_apply_apply, real_inner_comm] using! hL2)

end AsymptoticStatistics.MEstimator
