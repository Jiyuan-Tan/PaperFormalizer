module
public import StatLean.AsymptoticStatistics.ParametricFamily.Defs

@[expose] public section

/-!
# Extending a family from a parameter subset

This file extends a family indexed by a set `Θ ⊆ E` to the ambient parameter
space.  Outside `Θ` the extension uses the density at a fixed reference point.
This lets local ambient-space results be applied at an interior point without
changing the statistical model on `Θ`.
-/

namespace AsymptoticStatistics.ParametricFamily

open MeasureTheory

/-- Extend a family indexed by `Θ ⊆ E` to all of `E`, using the density at
`θ₀` outside `Θ`.  Thus the extension agrees with the original family on
`Θ`; its off-set values introduce no new distributions. -/
noncomputable def extendFromSetAt
    {𝒜 E : Type*} [MeasurableSpace 𝒜] {Θ : Set E}
    (M : ParametricFamily 𝒜 Θ) (θ₀ : Θ) : ParametricFamily 𝒜 E := by
  classical
  exact
    { density := fun θ x =>
        if hθ : θ ∈ Θ then M.density ⟨θ, hθ⟩ x else M.density θ₀ x
      density_meas := fun θ => by
        by_cases hθ : θ ∈ Θ
        · simpa [hθ] using M.density_meas ⟨θ, hθ⟩
        · simpa [hθ] using M.density_meas θ₀
      density_nonneg := fun θ x => by
        by_cases hθ : θ ∈ Θ
        · simpa [hθ] using M.density_nonneg ⟨θ, hθ⟩ x
        · simpa [hθ] using M.density_nonneg θ₀ x }

/-- On a parameter belonging to `Θ`, the ambient extension has the original
density. -/
@[simp] theorem extendFromSetAt_density_of_mem
    {𝒜 E : Type*} [MeasurableSpace 𝒜] {Θ : Set E}
    (M : ParametricFamily 𝒜 Θ) (θ₀ : Θ) (θ : E) (hθ : θ ∈ Θ) (x : 𝒜) :
    (M.extendFromSetAt θ₀).density θ x = M.density ⟨θ, hθ⟩ x := by
  classical
  simp [extendFromSetAt, hθ]

/-- Outside `Θ`, the ambient extension has the density at the reference
parameter. -/
@[simp] theorem extendFromSetAt_density_of_not_mem
    {𝒜 E : Type*} [MeasurableSpace 𝒜] {Θ : Set E}
    (M : ParametricFamily 𝒜 Θ) (θ₀ : Θ) (θ : E) (hθ : θ ∉ Θ) (x : 𝒜) :
    (M.extendFromSetAt θ₀).density θ x = M.density θ₀ x := by
  classical
  simp [extendFromSetAt, hθ]

/-- The ambient extension agrees with the original family at each subtype
parameter. -/
@[simp] theorem extendFromSetAt_density_coe
    {𝒜 E : Type*} [MeasurableSpace 𝒜] {Θ : Set E}
    (M : ParametricFamily 𝒜 Θ) (θ₀ θ : Θ) (x : 𝒜) :
    (M.extendFromSetAt θ₀).density (θ : E) x = M.density θ x := by
  exact M.extendFromSetAt_density_of_mem θ₀ θ θ.property x

/-- Normalization and integrability of the original family pass to its
ambient extension, including at parameters outside `Θ`. -/
theorem isPDFOf_extendFromSetAt
    {𝒜 E : Type*} [MeasurableSpace 𝒜] {Θ : Set E}
    (M : ParametricFamily 𝒜 Θ) (μ : Measure 𝒜) (θ₀ : Θ)
    -- Normalized integrable densities on the book's parameter set.
    (hPDF : IsPDFOf M μ) : IsPDFOf (M.extendFromSetAt θ₀) μ := by
  constructor
  · intro θ
    classical
    by_cases hθ : θ ∈ Θ
    · simpa [extendFromSetAt, hθ] using hPDF.density_integral_eq_one ⟨θ, hθ⟩
    · simpa [extendFromSetAt, hθ] using hPDF.density_integral_eq_one θ₀
  · intro θ
    classical
    by_cases hθ : θ ∈ Θ
    · simpa [extendFromSetAt, hθ] using hPDF.density_integrable ⟨θ, hθ⟩
    · simpa [extendFromSetAt, hθ] using hPDF.density_integrable θ₀

end AsymptoticStatistics.ParametricFamily
