module
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

@[expose] public section

/-!
# Joint weak convergence under independence

Given `μₙ ⇝ μ` and `νₙ ⇝ ν` (weak convergence of sequences of probability
measures), the product measures converge weakly: `μₙ.prod νₙ ⇝ μ.prod ν`.

This "weak-convergence-respects-product" fact, combined with the continuous
map `Prod.fst + Prod.snd = (+)`, gives joint weak convergence of the sum
(vdV §8.4).

Headline declaration: `tendsto_prod_of_tendsto`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace AsymptoticStatistics
namespace ForMathlib

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Joint weak convergence of product measures**.

If `μₙ ⇝ μ` and `νₙ ⇝ ν` (as bundled probability measures on finite-
dimensional inner-product spaces), then `μₙ.prod νₙ ⇝ μ.prod ν` on the
product space.

**Proof**: Mathlib's `ProbabilityMeasure.continuous_prod` states that
`(μ, ν) ↦ μ.prod ν : ProbabilityMeasure α × ProbabilityMeasure β →
ProbabilityMeasure (α × β)` is continuous in the product topology, under
the regularity hypotheses
`[SecondCountableTopology] [PseudoMetrizableSpace] [OpensMeasurableSpace]`
on both factors. Finite-dimensional real inner-product spaces with the
Borel σ-algebra satisfy all three. Composing with the joint convergence
`(μₙ, νₙ) → (μ, ν)` (which is exactly `Filter.Tendsto.prodMk_nhds`) gives
the result. -/
theorem tendsto_prod_of_tendsto
    {μₙ : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    {νₙ : ℕ → ProbabilityMeasure F} {ν : ProbabilityMeasure F}
    (hμ : Tendsto μₙ atTop (𝓝 μ))
    (hν : Tendsto νₙ atTop (𝓝 ν)) :
    Tendsto (fun n => (μₙ n).prod (νₙ n)) atTop (𝓝 (μ.prod ν)) :=
  (ProbabilityMeasure.continuous_prod (α := E) (β := F)).tendsto _
    |>.comp (hμ.prodMk_nhds hν)

end ForMathlib
end AsymptoticStatistics
