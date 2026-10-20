module
public import StatLean.AsymptoticStatistics.Core.MassMethod
public import StatLean.AsymptoticStatistics.Core.LinearFunctional

@[expose] public section

/-!
# The empirical distribution as an asymptotically efficient estimator

Formalises van der Vaart, *Asymptotic Statistics* (Cambridge, 1998),
Example 25.24 (§25.3): the fully **nonparametric** model at a probability
measure `P` on `(Ω, 𝓐)`, whose tangent space is *all* of `L²₀(P)` (every
mean-zero square-integrable function is a score), and the linear parameter
functional

  `ψ_a(Q) = ∫ a dQ`

for a fixed **bounded measurable** `a : Ω → ℝ`. The efficient influence
function is the centered integrand itself,

  `φ = a − ∫ a dP`,

with efficient information `Var_P(a) = ‖φ‖²_{L²(P)}` (the operational
efficiency bound of `Core/EIF.efficient_bound_eq_sqNorm`). This is the
simplest EIF example: the functional is linear, the tangent space is the
whole of `L²₀(P)`, and the EIF is the centered integrand with no nuisance
correction.

Because `ψ_a` is linear, the directional derivative along any QMD path `γ`
is exactly `∫ a · (score) dP`, so the *centered* candidate `a − ∫ a dP` is
the mixture-Gâteaux / TV-Fréchet representer. We route through the
`Core/MassMethod` harness entry point `eif_via_TV_QMD`, which constructs the
pathwise derivative from the DQM-path expansion `meanFunctional_isTVFrechetExpansion`
and closes the EIF claim over the full tangent `⊤` in one line.

Headline: `empiricalDistribution_isEIF`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal
open AsymptoticStatistics.Core
open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.Core.MassMethod
open AsymptoticStatistics.ForMathlib.QMDAnalytic
open AsymptoticStatistics.ForMathlib.RnDerivSqrt
open AsymptoticStatistics.L2Utils

namespace AsymptoticStatistics.Examples.EmpiricalDistribution

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {a : Ω → ℝ}


/-- **Efficient influence function of the empirical-distribution functional**
(vdV Example 25.24). For the fully nonparametric model (tangent space `⊤`,
all mean-zero `L²(P)` functions) and the linear functional
`ψ_a(Q) = ∫ a dQ`, the centered integrand `φ = a − ∫ a dP` is the efficient
influence function.

The pathwise derivative is *constructed internally* by the harness as the
`L²(P)` inner product against `φ` (via `pathwiseDifferentiableAt_of_TVFrechet`);
the membership `φ ∈ ⊤` is trivial. -/
theorem empiricalDistribution_isEIF
    (ha_meas : Measurable a) (ha_bdd : ∃ C : ℝ, ∀ ω, |a ω| ≤ C) :
    IsEfficientInfluenceFunction P (⊤ : Submodule ℝ ↥(L2ZeroMean P))
      (pathwiseDifferentiableAt_of_TVFrechet
        (memLp_two_of_bounded ha_meas ha_bdd)
        (meanFunctional_isTVFrechetExpansion ha_meas ha_bdd)).derivative
      ((centeredCandidate (P := P) a
        (memLp_two_of_bounded ha_meas ha_bdd)).toL2ZeroMean) :=
  eif_via_TV_QMD (memLp_two_of_bounded ha_meas ha_bdd)
    (meanFunctional_isTVFrechetExpansion ha_meas ha_bdd)

end AsymptoticStatistics.Examples.EmpiricalDistribution
