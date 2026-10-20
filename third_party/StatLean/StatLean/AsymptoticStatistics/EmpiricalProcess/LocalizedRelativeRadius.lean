module
public import StatLean.AsymptoticStatistics.EmpiricalProcess.LocalizedPointwiseDense
public import StatLean.AsymptoticStatistics.EmpiricalProcess.UniformCoveringMeasurability

@[expose] public section

/-!
# Measurability of localized empirical relative radii

Pointwise density of a class makes the empirical relative radius of its
strictly localized difference class measurable as a function of the sample.
-/

namespace AsymptoticStatistics.EmpiricalProcess

open MeasureTheory

/-- The empirical relative radius of a strict localized difference class is
measurable in the sample. -/
theorem measurable_empiricalRelativeRadius_strictLocalizedDifferenceClass
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hΦ : IsEnvelope F Φ) (hΦ_memLp : MemLp Φ 2 P)
    (hΦ_meas : Measurable Φ) (r : ℝ) (n : ℕ) :
    Measurable (fun X : Fin n → Ω =>
      empiricalRelativeRadius (strictLocalizedDifferenceClass F P r)
        (fun x => 2 * Φ x) n X) := by
  have hLocalDense := EmpProcPointwiseDense_strictLocalizedDifferenceClass
    hDense hF_meas hΦ hΦ_memLp r
  obtain ⟨F', hsub, hct, hApprox, _⟩ := hLocalDense
  apply measurable_empiricalRelativeRadius_of_pointwiseDense
    hsub hct hApprox
  · intro h hh
    obtain ⟨f, hf, g, hg, rfl, _⟩ := hsub hh
    exact (hF_meas f hf).sub (hF_meas g hg)
  · exact measurable_const.mul hΦ_meas

/-- The real-valued empirical relative radius of a strict localized
difference class is measurable in the sample. -/
theorem measurable_empiricalRelativeRadiusReal_strictLocalizedDifferenceClass
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Set (Ω → ℝ)} {Φ : Ω → ℝ}
    (hDense : EmpProcPointwiseDense F P)
    (hF_meas : ∀ f ∈ F, Measurable f)
    (hΦ : IsEnvelope F Φ) (hΦ_memLp : MemLp Φ 2 P)
    (hΦ_meas : Measurable Φ) (r : ℝ) (n : ℕ) :
    Measurable (fun X : Fin n → Ω =>
      empiricalRelativeRadiusReal (strictLocalizedDifferenceClass F P r)
        (fun x => 2 * Φ x) n X) := by
  have hLocalDense := EmpProcPointwiseDense_strictLocalizedDifferenceClass
    hDense hF_meas hΦ hΦ_memLp r
  obtain ⟨F', hsub, hct, hApprox, _⟩ := hLocalDense
  apply measurable_empiricalRelativeRadiusReal_of_pointwiseDense
    hsub hct hApprox
  · intro h hh
    obtain ⟨f, hf, g, hg, rfl, _⟩ := hsub hh
    exact (hF_meas f hf).sub (hF_meas g hg)
  · exact measurable_const.mul hΦ_meas

end AsymptoticStatistics.EmpiricalProcess
