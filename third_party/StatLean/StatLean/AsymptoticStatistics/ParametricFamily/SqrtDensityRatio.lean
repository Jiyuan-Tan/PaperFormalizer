module
public import StatLean.AsymptoticStatistics.ForMathlib.LogTaylor
public import StatLean.AsymptoticStatistics.ParametricFamily.Defs

@[expose] public section

/-!
# Square-root density ratios

The Hellinger coordinate `2 * (√(pθ / p₀) - 1)` used in the likelihood
expansions of van der Vaart, Theorems 5.39 and 7.2.
-/

namespace AsymptoticStatistics

/-- Twice the centered square-root density ratio.

Edge behavior: division and square root are Mathlib's totalized operations.  In
particular, a zero denominator gives ratio zero and value `-2`; applications
under the base law use this only on a null set. -/
noncomputable def ParametricFamily.sqrtDensityRatio
    {𝒳 Θ : Type*} [MeasurableSpace 𝒳]
    (M : ParametricFamily 𝒳 Θ) (base target : Θ) (x : 𝒳) : ℝ :=
  2 * (Real.sqrt (M.density target x / M.density base x) - 1)

/-- The square-root density ratio is measurable in the observation. -/
lemma ParametricFamily.sqrtDensityRatio_measurable
    {𝒳 Θ : Type*} [MeasurableSpace 𝒳]
    (M : ParametricFamily 𝒳 Θ) (base target : Θ) :
    Measurable (M.sqrtDensityRatio base target) := by
  unfold ParametricFamily.sqrtDensityRatio
  exact (((M.density_meas target).div (M.density_meas base)).sqrt.sub_const _).const_mul _

/-- Pointwise Taylor identity for a parametric density ratio.  It includes the
zero-ratio boundary case and therefore needs no positivity hypothesis. -/
lemma ParametricFamily.log_density_ratio_taylor
    {𝒳 Θ : Type*} [MeasurableSpace 𝒳]
    (M : ParametricFamily 𝒳 Θ) (base target : Θ) (x : 𝒳) :
    Real.log (M.density target x / M.density base x) =
      M.sqrtDensityRatio base target x
        - M.sqrtDensityRatio base target x ^ 2 / 4
        + M.sqrtDensityRatio base target x ^ 2 / 2
          * ForMathlib.logTaylorRemainder (M.sqrtDensityRatio base target x) := by
  simpa only [ParametricFamily.sqrtDensityRatio] using
    (ForMathlib.log_div_nonneg_eq_sqrt_taylor
      (M.density_nonneg target x) (M.density_nonneg base x))

end AsymptoticStatistics
