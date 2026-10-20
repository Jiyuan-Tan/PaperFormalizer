module
public import StatLean.AsymptoticStatistics.DQM.Defs
public import StatLean.AsymptoticStatistics.ParametricFamily.ParameterSubset

@[expose] public section

/-!
# Differentiability in quadratic mean on a parameter subset

This file expresses DQM at an interior point of `Θ ⊆ E` through the canonical
ambient extension of the model.  This matches the local meaning of DQM used in
van der Vaart, Theorem 5.39.
-/

namespace AsymptoticStatistics

open MeasureTheory

/-- DQM for a model indexed by `Θ ⊆ E`, defined using the ambient extension
that equals the true density outside `Θ`.  At an interior point only a
neighborhood contained in `Θ` matters, so the off-set fallback does not affect
the book's local condition. -/
def DifferentiableQuadraticMeanOn
    {𝒜 E : Type*} [MeasurableSpace 𝒜]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Θ : Set E} (M : ParametricFamily 𝒜 Θ) (μ : Measure 𝒜)
    (θ₀ : Θ) (ℓ : 𝒜 → E) : Prop :=
  DifferentiableQuadraticMean (M.extendFromSetAt θ₀) μ (θ₀ : E) ℓ

/-- The subset DQM condition is exactly DQM of the canonical ambient
extension at the coerced true parameter. -/
theorem differentiableQuadraticMeanOn_iff_extendFromSetAt
    {𝒜 E : Type*} [MeasurableSpace 𝒜]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {Θ : Set E} (M : ParametricFamily 𝒜 Θ) (μ : Measure 𝒜)
    (θ₀ : Θ) (ℓ : 𝒜 → E) :
    DifferentiableQuadraticMeanOn M μ θ₀ ℓ ↔
      DifferentiableQuadraticMean (M.extendFromSetAt θ₀) μ (θ₀ : E) ℓ := by
  rfl

end AsymptoticStatistics
