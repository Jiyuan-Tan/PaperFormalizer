module
public import StatLean.AsymptoticStatistics.ForMathlib.PiWithDensity
public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

/-!
# Pi-product of standard 1D Gaussians

Two basic facts about `Measure.pi (fun _ => gaussianReal 0 1)` on `ι → ℝ`:

* `pi_gaussianReal_eq_withDensity` — the Pi-product Gaussian equals the Lebesgue
  measure on `ι → ℝ` tilted by the product density `∏ i, gaussianPDF 0 1 (x i)`.
* `pi_gaussianReal_neg_invariant` — Pi-product Gaussian is preserved by `x ↦ -x`.

Used by `Anderson.lean` (PL application + symmetry) and
`MultivariateGaussianWeakLimit.lean` (AC chain for `multivariateGaussian 0 S`
when `S.PosDef`).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AsymptoticStatistics

variable {ι : Type*} [Fintype ι]

/-- **`Measure.pi (gaussianReal 0 1) = volume.withDensity ρ`** where
`ρ x = ∏ i, gaussianPDF 0 1 (x i)` is the standard Pi Gaussian density on `ι → ℝ`.

Bridges Pi standard Gaussian to a Lebesgue density form. Closed via
`pi_withDensity_prod`. -/
lemma pi_gaussianReal_eq_withDensity :
    Measure.pi (fun _ : ι => gaussianReal 0 1)
      = (volume : Measure (ι → ℝ)).withDensity
          (fun x => ∏ i, gaussianPDF 0 1 (x i)) := by
  have h_each : (fun _ : ι => gaussianReal 0 1)
      = fun _ : ι => (volume : Measure ℝ).withDensity (gaussianPDF 0 1) := by
    funext _
    exact gaussianReal_of_var_ne_zero 0 one_ne_zero
  -- Provide the `SigmaFinite` instance for the tilted measure (it equals
  -- `gaussianReal 0 1`, a probability measure).
  haveI : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 1)) := by
    rw [← gaussianReal_of_var_ne_zero 0 one_ne_zero]
    infer_instance
  rw [h_each, ← MeasureTheory.pi_withDensity_prod
    (fun _ : ι => measurable_gaussianPDF 0 1)]
  rfl

/-- **Pi standard Gaussian is invariant under negation** `x ↦ -x`.

Each component `gaussianReal 0 1` is symmetric (`gaussianReal_map_neg` with mean 0);
the Pi product preserves this via `MeasureTheory.measurePreserving_pi`. -/
lemma pi_gaussianReal_neg_invariant :
    Measure.map (fun x : ι → ℝ => -x) (Measure.pi (fun _ : ι => gaussianReal 0 1))
      = Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  have h_each : ∀ _ : ι, MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 1)
      (gaussianReal 0 1) := by
    intro _
    refine ⟨measurable_neg, ?_⟩
    have := gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
    rwa [neg_zero] at this
  exact (MeasureTheory.measurePreserving_pi _ _ h_each).map_eq

end AsymptoticStatistics
