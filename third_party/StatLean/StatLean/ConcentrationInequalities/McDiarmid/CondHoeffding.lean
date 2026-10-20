module
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

/-!
# Conditional Hoeffding MGF lemma

Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 4 (Concentration Inequalities), §4.2
(Sub-Gaussian Random Variables), Theorem 4.7 (Hoeffding Inequality): for a real random variable `Z`
that is conditionally bounded in an interval of length `c = b − a` given a
sub-σ-algebra `m`, the conditional MGF of the centered random variable
`Z − E[Z|m]` is bounded by `exp(λ² c² / 8)` almost surely. This is the
per-step MGF estimate underpinning McDiarmid's bounded differences inequality
(Lu, *Big Data Analysis*, Chapter 5 §5.1, Theorem 5.1 (McDiarmid Inequality)).

The proof builds a `ProbabilityTheory.HasCondSubgaussianMGF` witness for
`W := Z − E[Z|m]` with parameter `((b − a)/2)² = c²/4`, by applying Mathlib's
unconditional Hoeffding lemma `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`
fiber-by-fiber against the conditional-expectation kernel `condExpKernel μ m`.
The fiber hypotheses (per-fiber boundedness, integrability, zero mean) are
transported from their global statements via `Measure.ae_ae_of_ae_comp`,
`Measure.ae_integrable_of_integrable_comp`, and
`condExp_ae_eq_trim_integral_condExpKernel` (plus `MeasureTheory.condExp_sub`
and `condExp_of_stronglyMeasurable` to identify `μ[W|m] = 0` a.s.). The bound
then follows from `HasCondSubgaussianMGF.ae_condExp_le`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {μ : Measure Ω}

/-- **Conditional Hoeffding MGF lemma** (Lu-BDA Chapter 4 §4.2 Sub-Gaussian Random Variables,
Theorem 4.7 (Hoeffding Inequality); per-step estimate for the McDiarmid Inequality, Chapter 5 §5.1
Theorem 5.1).

If a real random variable `Z` satisfies, almost surely,
`Z − E[Z|m] ∈ Set.Icc a b` for fixed reals `a, b`, then for every `λ : ℝ` the
conditional MGF obeys
`E[exp(λ (Z − E[Z|m])) | m] ≤ exp(λ² (b − a)² / 8)` almost surely.

The proof goes via the per-fiber unconditional Hoeffding lemma applied to the
conditional-expectation kernel `condExpKernel μ m`. -/
theorem condExp_hoeffding_mgf [IsProbabilityMeasure μ]
    (hm : m ≤ mΩ) {Z : Ω → ℝ} {a b : ℝ}
    -- USER-INPUT: Z is integrable w.r.t. μ; Lu-BDA §4.2 (regularity, implicit in the book).
    (hZ_int : Integrable Z μ)
    -- USER-INPUT: Z − E[Z|m] ∈ [a,b] almost surely (length b−a = McDiarmid constant); Lu-BDA §4.2.
    (hbound : ∀ᵐ ω ∂μ, Z ω - (μ[Z | m]) ω ∈ Set.Icc a b)
    (lam : ℝ) :
    ∀ᵐ ω ∂μ, (μ[fun ω' => Real.exp (lam * (Z ω' - (μ[Z | m]) ω')) | m]) ω
      ≤ Real.exp (lam ^ 2 * (b - a) ^ 2 / 8) := by
  -- Centered variable `W := Z - μ[Z | m]` (pointwise).
  -- LEAN-ONLY: integrability and a.e. measurability of W.
  have hW_int : Integrable (fun ω => Z ω - (μ[Z | m]) ω) μ :=
    hZ_int.sub integrable_condExp
  have hW_aem : AEMeasurable (fun ω => Z ω - (μ[Z | m]) ω) μ :=
    hW_int.1.aemeasurable
  -- Step 1: `μ[W|m] = 0` a.e. (μ) — via `condExp_sub` and the fact that the inner
  -- `μ[Z | m]` is itself `m`-strongly-measurable hence its own conditional expectation.
  have h_inner : (μ[(μ[Z | m]) | m]) = (μ[Z | m]) := by
    refine condExp_of_stronglyMeasurable hm ?_ integrable_condExp
    exact stronglyMeasurable_condExp
  have h_sub :
      μ[fun ω => Z ω - (μ[Z | m]) ω | m]
        =ᵐ[μ] (μ[Z | m]) - μ[(μ[Z | m]) | m] :=
    condExp_sub hZ_int integrable_condExp m
  have h_condExp_W_zero :
      μ[fun ω => Z ω - (μ[Z | m]) ω | m] =ᵐ[μ] (0 : Ω → ℝ) := by
    filter_upwards [h_sub] with ω hω
    have : ((μ[Z | m]) - μ[(μ[Z | m]) | m]) ω = (μ[Z | m]) ω - (μ[(μ[Z | m]) | m]) ω := rfl
    rw [hω, this, h_inner]
    simp
  -- Step 1': lift to `μ.trim hm` via `m`-strong measurability.
  have h_condExp_W_zero_trim :
      μ[fun ω => Z ω - (μ[Z | m]) ω | m] =ᵐ[μ.trim hm] (0 : Ω → ℝ) :=
    stronglyMeasurable_condExp.ae_eq_trim_of_stronglyMeasurable hm
      stronglyMeasurable_zero h_condExp_W_zero
  -- Step 2: condExpKernel disintegration.
  have h_disint :
      μ[fun ω => Z ω - (μ[Z | m]) ω | m] =ᵐ[μ.trim hm]
        fun ω' => ∫ y, (Z y - (μ[Z | m]) y) ∂((condExpKernel μ m) ω') :=
    condExp_ae_eq_trim_integral_condExpKernel hm hW_int
  -- Per-fiber zero mean.
  have h_fiber_zero : ∀ᵐ ω' ∂(μ.trim hm),
      ∫ y, (Z y - (μ[Z | m]) y) ∂((condExpKernel μ m) ω') = 0 := by
    filter_upwards [h_disint.symm.trans h_condExp_W_zero_trim] with ω' h
    simpa using h
  -- Step 3: per-fiber boundedness.
  have hμ_eq : (condExpKernel μ m) ∘ₘ (μ.trim hm) = μ := condExpKernel_comp_trim hm
  have h_fiber_bound : ∀ᵐ ω' ∂(μ.trim hm),
      ∀ᵐ ω ∂((condExpKernel μ m) ω'), Z ω - (μ[Z | m]) ω ∈ Set.Icc a b := by
    refine Measure.ae_ae_of_ae_comp ?_
    rw [hμ_eq]; exact hbound
  -- Per-fiber AEMeasurable of W.
  have h_fiber_aem : ∀ᵐ ω' ∂(μ.trim hm),
      AEMeasurable (fun ω => Z ω - (μ[Z | m]) ω) ((condExpKernel μ m) ω') := by
    have h1 : Integrable (fun ω => Z ω - (μ[Z | m]) ω)
        ((condExpKernel μ m) ∘ₘ (μ.trim hm)) := by
      rw [hμ_eq]; exact hW_int
    filter_upwards [Measure.ae_integrable_of_integrable_comp h1] with ω' hI
    exact hI.aestronglyMeasurable.aemeasurable
  -- Step 4: assemble `Kernel.HasSubgaussianMGF` witness, i.e. `HasCondSubgaussianMGF`.
  have hCS : HasCondSubgaussianMGF m hm (fun ω => Z ω - (μ[Z | m]) ω)
      ((‖b - a‖₊ / 2) ^ 2) μ := by
    refine ⟨?_, ?_⟩
    · intro t
      rw [hμ_eq]
      exact integrable_exp_mul_of_mem_Icc hW_aem hbound
    · filter_upwards [h_fiber_bound, h_fiber_zero, h_fiber_aem]
        with ω' h_bd h_mean h_aem t
      have h_subg :
          HasSubgaussianMGF (fun ω => Z ω - (μ[Z | m]) ω)
            ((‖b - a‖₊ / 2) ^ 2) ((condExpKernel μ m) ω') :=
        hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero h_aem h_bd h_mean
      exact h_subg.mgf_le t
  -- Step 5: extract conditional MGF bound; convert the constant.
  have hAE := hCS.ae_condExp_le lam
  -- `(((‖b - a‖₊ / 2)^2 : ℝ≥0) : ℝ) = (b - a)^2 / 4`.
  have h_const : ((((‖b - a‖₊ : ℝ≥0) / 2) ^ 2 : ℝ≥0) : ℝ) = (b - a) ^ 2 / 4 := by
    push_cast
    rw [Real.norm_eq_abs, div_pow, sq_abs]
    ring
  filter_upwards [hAE] with ω hω
  refine hω.trans (le_of_eq ?_)
  apply congr_arg Real.exp
  rw [h_const]
  ring

end StatLean.ConcentrationInequalities
