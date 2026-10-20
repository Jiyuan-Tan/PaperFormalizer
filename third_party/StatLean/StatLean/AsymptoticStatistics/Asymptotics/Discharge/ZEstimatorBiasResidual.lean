module
public import StatLean.AsymptoticStatistics.Asymptotics.Discharge.ZEstimator

@[expose] public section

/-!
# Z-estimator bias-residual expansion (vdV §25.8, thm:25.59)

Closes the bundled `asympLinear_25_59` field of
`EfficientScoreEqBiasResidualAssumptions` from book-level primitives.
This is the bias-residual variant of vdV thm:25.54: same hypotheses
except the no-bias condition (25.52), with conclusion retaining the
bias term explicitly:

```
√n(θ̂_n − θ) = (1/√n) Σᵢ Ĩ⁻¹ ℓ̃(X_i)
              + √n · P_{θ̂_n, η} ℓ̃_{θ̂_n, η̂_n} + o_P(1).
```

The discharge of vdV thm:25.54 (`zEstimator_asympLinear_of_taylor`) takes
`ZEstimatorTaylorCore`, whose interface omits the no-bias field. This file gives the
discharge of thm:25.59 as a thin wrapper around the `Core`-based AL
theorem, proving `AsymptoticallyLinearWithBiasAt` with
`bias = (fun _ _ => 0)` (vdV's bias term `√n P ℓ̃` is absorbed by the
estimating-equation rate `√n 𝕡_n ℓ̃ →_P 0`).

Headline declarations: `zEstimator_biasResidual_asympLinear_of_taylor`
and `toEfficientScoreEqBiasResidualAssumptions`.

Reference: vdV §25.8 (Efficient Score Equations), thm:25.59.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal Function

namespace AsymptoticStatistics.Asymptotics.Discharge.ZEstimator

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.StrictModel.EfficientScore
open AsymptoticStatistics.Asymptotics.ZEstimator

variable {Ω : Type} [MeasurableSpace Ω]

/-- *vdV thm:25.59 strong-regularity bundle (Taylor route).*

A type alias for `ZEstimatorTaylorCore`: the discharge of vdV thm:25.59
takes the same primitive hypotheses as thm:25.54 **minus** the no-bias
condition (25.52). The aliasing makes the call site and downstream
documentation read in vdV's thm:25.59 vocabulary while reusing the
already-proved Taylor route from `Discharge/ZEstimator.lean`.

Reference: vdV §25.8 (Efficient Score Equations), thm:25.59 hypotheses
(everything in thm:25.54 except eq:25.52). -/
abbrev ZEstimatorBiasResidualTaylorHyp
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (v : Θ)
    (estimator : ∀ n, (Fin n → Ω) → ℝ)
    (score_func_seq : ∀ n, (Fin n → Ω) → (Ω → ℝ))
    (score_truth : Ω → ℝ)
    (donsker_class : Set (Ω → ℝ))
    (score_l_dot : Lp ℝ 2 P)
    (θ₀ : ℝ) : Prop :=
  ZEstimatorTaylorCore P Θ S_θ T_nuis v
    estimator score_func_seq score_truth donsker_class score_l_dot θ₀

namespace ZEstimatorBiasResidualTaylorHyp

variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
variable {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
variable [T_nuis.HasOrthogonalProjection] {v : Θ}
variable {estimator : ∀ n, (Fin n → Ω) → ℝ}
variable {score_func_seq : ∀ n, (Fin n → Ω) → (Ω → ℝ)}
variable {score_truth : Ω → ℝ}
variable {donsker_class : Set (Ω → ℝ)}
variable {score_l_dot : Lp ℝ 2 P}
variable {θ₀ : ℝ}

/-- *vdV thm:25.59 — Z-estimator bias-residual expansion via the Taylor route.*

From the strong-regularity bundle `ZEstimatorBiasResidualTaylorHyp`
(= `ZEstimatorTaylorCore`, i.e. thm:25.54's hypothesis bundle minus the
no-bias condition), the Z-estimator satisfies the bias-residual
asymptotic-linear expansion with influence function `(1/Ĩ) • ℓ̃`,
centering `θ₀`, and bias-residual sequence `(fun _ _ => 0)`.

**Why bias = 0.** vdV's thm:25.59 carries an
explicit bias term `√n · P_{θ̂_n,η} ℓ̃_{θ̂_n,η̂_n}` in the conclusion
because the no-bias condition (25.52) is dropped. Under our Lean
encoding, the estimating-equation rate hypothesis
`√n · 𝕡_n ℓ̃_{θ̂_n,η̂_n} →_P 0` (the `score_eq` field of `Core`) is
retained, and the Taylor route's algebraic identity already absorbs
the `√n P ℓ̃_{θ̂,η̂}` term into the AL conclusion (Step 6 of the
discharge). Hence the natural specialization of thm:25.59 in our
setup has identically-zero bias.

The full vdV thm:25.59 conclusion with non-trivial bias would require
also relaxing `score_eq` to a weaker form `√n 𝕡_n ℓ̃_{θ̂,η̂} = bias_n + o_P(1)`,
which is a separate, harder closure (out of scope here).

**Recovery to thm:25.54.** When the bias is identically zero (as
produced by this theorem), `asympLinearWithBiasAt_zero_iff_asympLinearAt`
recovers `AsymptoticallyLinearAt` and hence `EfficientScoreEqAssumptions`
via the existing thm:25.54 pipeline.

Reference: vdV §25.8 (Efficient Score Equations), thm:25.59. -/
theorem zEstimator_biasResidual_asympLinear_of_taylor
    (h : ZEstimatorBiasResidualTaylorHyp P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀) :
    AsymptoticallyLinearWithBiasAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) θ₀ (fun _ _ => 0) := by
  rw [asympLinearWithBiasAt_zero_iff_asympLinearAt]
  -- `h : ZEstimatorBiasResidualTaylorHyp …` is definitionally
  -- `ZEstimatorTaylorCore …`; recoerce via `show` for unification.
  have hCore :
      ZEstimatorTaylorCore P Θ S_θ T_nuis v
        estimator score_func_seq score_truth donsker_class
        score_l_dot θ₀ := h
  exact ZEstimatorTaylorCore.zEstimator_asympLinear_of_taylor hCore

/-- **Zero-residual Taylor assumptions as a bias-residual bundle.**

Constructs `EfficientScoreEqBiasResidualAssumptions` from
`ZEstimatorBiasResidualTaylorHyp` and the EIF-construction inputs `h_mem` and `h_dψ`,
with residual `(fun _ _ => 0)`. Positivity of the efficient information is inherited
from the underlying `ZEstimatorTaylorCore`, and `asympLinear_25_59` is supplied by
`zEstimator_biasResidual_asympLinear_of_taylor`.

Mirrors `ZEstimatorTaylorCore.toEfficientScoreEqAssumptions` for thm:25.54.

Reference: vdV §25.8 (Efficient Score Equations), thm:25.59. -/
def toEfficientScoreEqBiasResidualAssumptions
    {T : Submodule ℝ ↥(L2ZeroMean P)} {dψ : T →L[ℝ] ℝ}
    (h : ZEstimatorBiasResidualTaylorHyp P Θ S_θ T_nuis v
            estimator score_func_seq score_truth donsker_class
            score_l_dot θ₀)
    (h_mem :
      (1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v ∈ T)
    (h_dψ : ∀ g : T,
      dψ g
        = (1 / efficientInformation S_θ T_nuis v)
            * ⟪efficientScore S_θ T_nuis v, (g : ↥(L2ZeroMean P))⟫_ℝ) :
    EfficientScoreEqBiasResidualAssumptions P Θ S_θ T_nuis v T dψ
      estimator (fun _ _ => 0) θ₀ where
  h_mem := h_mem
  h_dψ := h_dψ
  hI_pos := (h : ZEstimatorTaylorCore P Θ S_θ T_nuis v
              estimator score_func_seq score_truth donsker_class
              score_l_dot θ₀).hI_pos
  asympLinear_25_59 := zEstimator_biasResidual_asympLinear_of_taylor h

end ZEstimatorBiasResidualTaylorHyp

end AsymptoticStatistics.Asymptotics.Discharge.ZEstimator
