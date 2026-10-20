module
public import StatLean.AsymptoticStatistics.LowerBounds.RegularEstimatorNarrow

@[expose] public section

/-!
# The canonical-path LHS functional `LHS_canonical`

This file defines the headline left-hand-side functional of the
local-asymptotic-minimax bound:

* `LHS_canonical` — the canonical-path LHS centered on the **true** functional
  `ψ((canonicalPath g).curve (1/√n))`, with truncated loss `ℓ_M`.

Feeding the true submodel functional directly into the per-direction-shift
sibling of Theorem 8.11 makes the per-`n` inclusion
`localAsymptoticRisk ≤ LHS_canonical` (proved in
`LAMUnboundedBridge.unboundedLam_le_LHS_canonical`) **exact**: there is no
affine centering detour and hence no external recenter step.

Reference: van der Vaart, *Asymptotic Statistics*, §25.3.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal MeasureTheory

namespace AsymptoticStatistics.LowerBounds

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics
open AsymptoticStatistics.LowerBounds.RegularEstimator

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-! ## The canonical-path LHS functional. -/

/-- **Canonical-path LHS** centered on the true functional `ψ(curve)`.
Matches the headline 25.21 LHS (with truncated loss `ℓ_M`). -/
noncomputable def LHS_canonical (T_set : TangentSpec P)
    (T_n : ∀ n, (Fin n → Ω) → ℝ) (ψ : Measure Ω → ℝ) (ℓ_M : ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ I : { S : Finset ↥(L2ZeroMean P) // (S : Set _) ⊆ T_set.carrier },
    Filter.liminf (fun n : ℕ => I.val.sup (fun g =>
      ∫⁻ X : Fin n → Ω, ℓ_M (Real.sqrt n *
          (T_n n X - ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹))))
        ∂(MeasureTheory.Measure.pi (fun _ : Fin n => (canonicalPath g).curve ((Real.sqrt n)⁻¹)))))
      Filter.atTop

/-- **Vector-valued canonical-path LHS** (codomain generalization of
`LHS_canonical` to `EuclideanSpace ℝ (Fin d)`). The estimator `T_n` and functional
`ψ` take values in `EuclideanSpace ℝ (Fin d)`, the loss `ℓ_M` is on that space, and
the scalar rescaling `√n * (…)` becomes the `√n • (…)` smul. The `canonicalPath g`
realiser is unchanged. -/
noncomputable def LHS_canonical_vec {d : ℕ} (T_set : TangentSpec P)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d))
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin d))
    (ℓ_M : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ I : { S : Finset ↥(L2ZeroMean P) // (S : Set _) ⊆ T_set.carrier },
    Filter.liminf (fun n : ℕ => I.val.sup (fun g =>
      ∫⁻ X : Fin n → Ω, ℓ_M (Real.sqrt n • (T_n n X
          - ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹))))
        ∂(MeasureTheory.Measure.pi (fun _ : Fin n => (canonicalPath g).curve ((Real.sqrt n)⁻¹)))))
      Filter.atTop

end AsymptoticStatistics.LowerBounds
