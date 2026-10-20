module
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-!
# Binding a scale-family of `withDensity` measures

The Giry-monad `bind` of a parametrized family of `withDensity` measures is again a `withDensity`,
whose density is the mixture (marginal) density:
$$\Big(\mu \gg\!\!= \big(b \mapsto \nu \cdot f_b\big)\Big) \;=\; \nu \cdot \Big(x \mapsto \int f_b(x)\,d\mu(b)\Big).$$
This is the one brick that turns the Dirichlet–Laplace scale mixture
`dlMarginal a = (Gamma a).bind laplaceMeasure` into an explicit `volume.withDensity dlDensity` form.

**Reference.** Bhattacharya–Pati–Pillai–Dunson, *Dirichlet–Laplace priors for optimal shrinkage*
(arXiv:1401.5398), eq. (10) (the scale-mixture representation `θ | ψ ~ Laplace(ψ)`,
`ψ ~ Gamma(a, 1/2)`); the identity itself is the elementary Giry-monad / Tonelli fact that makes
that mixture density computable. A candidate for upstreaming (kept in the area `ForMathlib/` layer,
namespace `StatLean.Bayesian`, until then).

**Proof formalization notes.** By `Measure.ext` on measurable `s`:
`(μ.bind fun b => ν.withDensity (f b)) s = ∫⁻ b, (ν.withDensity (f b)) s ∂μ` (`bind_apply`, using
measurability of `b ↦ ν.withDensity (f b)`) `= ∫⁻ b, ∫⁻ x in s, f b x ∂ν ∂μ` (`withDensity_apply`)
`= ∫⁻ x in s, ∫⁻ b, f b x ∂μ ∂ν` (Tonelli, `lintegral_lintegral_swap`, joint measurability of `f`)
`= (ν.withDensity fun x => ∫⁻ b, f b x ∂μ) s` (`withDensity_apply` again, using
`measurable_lintegral_param`). The `SFinite μ`/`SigmaFinite ν` hypotheses are exactly what the
`bind`, the swap, and the `withDensity` restriction require; both hold for the DL mixture
(`μ = Gamma(a, 1/2)` is a probability measure, `ν = volume`).

**Bibliographic comments.** The measure monad (unit/bind) is due to M. Giry (*A categorical approach
to probability theory*, LNM 915, 1982); the integral swap is the Fubini–Tonelli theorem (Tonelli,
1909), valid here in the s-finite / σ-finite regime.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

/-- Measurability of the **marginalized density** `x ↦ ∫⁻ b, f b x ∂μ` (Tonelli's right-hand
integrand), for jointly measurable `f` and s-finite `μ`. Wrapper around
`Measurable.lintegral_prod_left'`. -/
theorem measurable_lintegral_param {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure β) [SFinite μ] {f : β → α → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the parametrized integrand (regularity)
    (hf : Measurable (Function.uncurry f)) :
    Measurable (fun x => ∫⁻ b, f b x ∂μ) :=
  hf.lintegral_prod_left

/-- **`bind` of a `withDensity` family is `withDensity` of the marginal density.** For jointly
measurable `f`, s-finite mixing measure `μ`, and σ-finite base `ν`:
`(μ.bind fun b => ν.withDensity (f b)) = ν.withDensity (fun x => ∫⁻ b, f b x ∂μ)`. -/
theorem Measure.bind_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure β) (ν : Measure α) [SFinite μ] [SigmaFinite ν] {f : β → α → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the parametrized density (regularity)
    (hf : Measurable (Function.uncurry f)) :
    (μ.bind fun b => ν.withDensity (f b)) = ν.withDensity (fun x => ∫⁻ b, f b x ∂μ) := by
  have hmeas : AEMeasurable (fun b => ν.withDensity (f b)) μ := by
    refine (Measure.measurable_of_measurable_coe _ fun s hs => ?_).aemeasurable
    simp_rw [withDensity_apply _ hs]
    exact (hf.comp measurable_swap).lintegral_prod_left' (μ := ν.restrict s)
  ext s hs
  rw [Measure.bind_apply hs hmeas, withDensity_apply _ hs]
  simp_rw [withDensity_apply _ hs]
  rw [lintegral_lintegral_swap hf.aemeasurable]

end StatLean.Bayesian
