module
public import StatLean.AsymptoticStatistics.OneStepEstimator.Discretization

@[expose] public section

/-!
# Asymptotic expansion of one-step estimators

Formalizations of vdV Theorems 5.45 and 5.48.
-/

open MeasureTheory Filter
open scoped Topology Matrix.Norms.L2Operator

namespace AsymptoticStatistics.OneStepEstimator

/-- **vdV Theorem 5.45 (one-step estimation).** Under (5.44), a root-`n` bounded
preliminary estimator and a consistent estimated derivative matrix yield the standard
one-step asymptotic expansion. -/
theorem oneStepEstimator_linearExpansion
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    {k : ℕ} (Ψ : ℕ → Ξ → E k → E k) (pre : ℕ → Ξ → E k)
    (Vhat : ℕ → Ξ → Matrix (Fin k) (Fin k) ℝ) (θ0 : E k)
    (V0 : Matrix (Fin k) (Fin k) ℝ) (ν : Measure (E k)) [IsProbabilityMeasure ν]
    (hweak : WeakConverges
      (fun n => μ.map (fun ξ => Real.sqrt n • Ψ n ξ θ0)) ν)
    (hV0 : V0.det ≠ 0)
    (hVhat : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => Vhat n ξ - V0))
    (hpre : IsBoundedInProb (fun _ : ℕ => μ)
      (fun n ξ => Real.sqrt n • (pre n ξ - θ0)))
    (h44 : ∀ M : ℝ, 0 < M →
      EmpiricalProcess.TendstoZeroInOuterProbSup μ (fun n ξ (θ : E k) =>
        if Real.sqrt n * ‖θ - θ0‖ < M then ‖oneStepResidual Ψ θ0 V0 n ξ θ‖ else 0))
    (hΨ0_meas : ∀ n : ℕ, Measurable (fun ξ => Real.sqrt n • Ψ n ξ θ0))
    (hpre_meas : ∀ n : ℕ, Measurable (fun ξ => Real.sqrt n • (pre n ξ - θ0)))
    (hVhat_meas : ∀ n i j, Measurable (fun ξ => Vhat n ξ i j)) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      Real.sqrt n • (oneStepUpdate Ψ pre Vhat n ξ - θ0)
        + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0⁻¹
            (Real.sqrt n • Ψ n ξ θ0)) := by
  have hLeading : IsBoundedInProb (fun _ : ℕ => μ)
      (fun n ξ => Real.sqrt n • Ψ n ξ θ0) :=
    isBoundedInProb_of_weakConverges (P := fun _ : ℕ => μ) hΨ0_meas hweak
  have hResidual : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => oneStepResidual Ψ θ0 V0 n ξ (pre n ξ)) :=
    uniformLinearization_at_preliminary μ Ψ pre θ0 V0 h44 hpre hpre_meas
  exact oneStep_linearExpansion_core μ Ψ pre Vhat θ0 V0 hV0 hVhat_meas hVhat
    hLeading hpre hResidual

/-- **vdV Theorem 5.48 (discretized one-step estimation).** The uniform condition
(5.44) is replaced by the deterministic-sequence condition (5.47) and the exact
root-`n` grid restriction. This theorem assembles the pointwise discretization lemma
with the common expansion core directly; it does not reuse Theorem 5.45. -/
theorem discretizedOneStepEstimator_linearExpansion
    {Ξ : Type*} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    {k : ℕ} (Ψ : ℕ → Ξ → E k → E k) (pre : ℕ → Ξ → E k)
    (Vhat : ℕ → Ξ → Matrix (Fin k) (Fin k) ℝ) (θ0 : E k)
    (V0 : Matrix (Fin k) (Fin k) ℝ) (ν : Measure (E k)) [IsProbabilityMeasure ν]
    (hweak : WeakConverges
      (fun n => μ.map (fun ξ => Real.sqrt n • Ψ n ξ θ0)) ν)
    (hV0 : V0.det ≠ 0)
    (hVhat : TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ => Vhat n ξ - V0))
    (hpre : IsBoundedInProb (fun _ : ℕ => μ)
      (fun n ξ => Real.sqrt n • (pre n ξ - θ0)))
    (h47 : ∀ θn : ℕ → E k,
      (∃ M : ℝ, ∀ᶠ n : ℕ in atTop, Real.sqrt n * ‖θn n - θ0‖ ≤ M) →
      TendstoInProbZero (fun _ : ℕ => μ)
        (fun n ξ => oneStepResidual Ψ θ0 V0 n ξ (θn n)))
    (hgrid : ∀ n, 0 < n → ∀ ξ, ∃ z : Fin k → ℤ, ∀ j,
      pre n ξ j = (z j : ℝ) / Real.sqrt n)
    (hΨ0_meas : ∀ n : ℕ, Measurable (fun ξ => Real.sqrt n • Ψ n ξ θ0))
    (hVhat_meas : ∀ n i j, Measurable (fun ξ => Vhat n ξ i j)) :
    TendstoInProbZero (fun _ : ℕ => μ) (fun n ξ =>
      Real.sqrt n • (oneStepUpdate Ψ pre Vhat n ξ - θ0)
        + Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) V0⁻¹
            (Real.sqrt n • Ψ n ξ θ0)) := by
  have hLeading : IsBoundedInProb (fun _ : ℕ => μ)
      (fun n ξ => Real.sqrt n • Ψ n ξ θ0) :=
    isBoundedInProb_of_weakConverges (P := fun _ : ℕ => μ) hΨ0_meas hweak
  have hResidual : TendstoInProbZero (fun _ : ℕ => μ)
      (fun n ξ => oneStepResidual Ψ θ0 V0 n ξ (pre n ξ)) :=
    pointwiseLinearization_at_discretized μ Ψ pre θ0 V0 h47 hpre hgrid
  exact oneStep_linearExpansion_core μ Ψ pre Vhat θ0 V0 hV0 hVhat_meas hVhat
    hLeading hpre hResidual

end AsymptoticStatistics.OneStepEstimator
