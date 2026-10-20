module
public import StatLean.Bayesian.Dominated.Defs

@[expose] public section

/-!
# The prior predictive density and its regularity

For a dominated model `κ θ = ν.withDensity (p θ)` with prior `π`, this file establishes that the
data distribution has the prior predictive density `m` with respect to `ν`,
$$\kappa \circ_m \pi = \nu.\mathrm{withDensity}\,(m), \qquad m(x) = \int_\Theta p(\theta,x)\,\pi(d\theta),$$
together with the measurability of `m` and the a.e. non-degeneracy facts (`0 < m < ∞`) that hold
automatically under a finite model.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.4, the marginal
`m(x) = ∫ f(x|θ) π(dθ)`, p. 22.

**Proof formalization notes.** `m`'s finiteness (`ν`-a.e. and `(κ ∘ₘ π)`-a.e.) and positivity
(`(κ ∘ₘ π)`-a.e.) are **derived** from `IsFiniteMeasure (κ ∘ₘ π)` and the withDensity
representation — they are *not* hypotheses (assuming `0 < m` would be laundering a fact forced by
the setup). Key Mathlib bricks: `Measurable.lintegral_prod_left'`, `Measure.bind_apply`,
`MeasureTheory.withDensity_apply`, `lintegral_eq_zero_iff`, `ae_lt_top`,
`withDensity_absolutelyContinuous`.

**Bibliographic comments.** The marginal (prior predictive) density `m(x)` is the *evidence* of
the model: its systematic use for hypothesis comparison begins with H. Jeffreys (*Theory of
Probability*, Oxford, 1939), and it underlies Bayes factors, model averaging, and empirical-Bayes
calibration — see R. E. Kass and A. E. Raftery, "Bayes factors," *J. Amer. Statist. Assoc.* 90
(1995), 773–795.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  {κ : Kernel Θ 𝓧} {π : Measure Θ} {ν : Measure 𝓧} {p : Θ → 𝓧 → ℝ≥0∞}

/-- The prior predictive density is measurable. -/
theorem measurable_predictiveDensity [SFinite π]
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p)) :
    Measurable (predictiveDensity p π) :=
  hp.lintegral_prod_left

/-- Where the predictive density vanishes, the likelihood section is `π`-a.e. zero. -/
theorem likelihood_ae_eq_zero_of_predictiveDensity_eq_zero [SFinite π]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p)) {x : 𝓧} (hx : predictiveDensity p π x = 0) :
    (fun θ => p θ x) =ᵐ[π] 0 := by
  have h : ∫⁻ θ, p θ x ∂π = 0 := hx
  exact (lintegral_eq_zero_iff hp.of_uncurry_right).mp h

/-- **The data distribution has the prior predictive density** `m` with respect to `ν`:
`κ ∘ₘ π = ν.withDensity (predictiveDensity p π)` (Robert §1.4, the marginal `m(x)`). -/
theorem comp_eq_withDensity_predictiveDensity [SFinite π] [SFinite ν]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model, K(θ, ·) = p(θ, ·) ν; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    κ ∘ₘ π = ν.withDensity (predictiveDensity p π) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), withDensity_apply _ hs]
  simp_rw [hκ, withDensity_apply _ hs]
  rw [lintegral_lintegral_swap hp.aemeasurable]
  rfl

/-- Forced by finiteness of the data distribution: `m < ∞` holds `ν`-a.e. (not a hypothesis). -/
theorem predictiveDensity_lt_top_ae [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    ∀ᵐ x ∂ν, predictiveDensity p π x < ∞ := by
  refine ae_lt_top (measurable_predictiveDensity hp) ?_
  have hint : ∫⁻ x, predictiveDensity p π x ∂ν = (κ ∘ₘ π) Set.univ := by
    rw [comp_eq_withDensity_predictiveDensity hp hκ, withDensity_apply _ MeasurableSet.univ,
      setLIntegral_univ]
  rw [hint]
  exact measure_ne_top _ _

/-- `m < ∞` holds `(κ ∘ₘ π)`-a.e. (transferred along `κ ∘ₘ π = ν.withDensity m ≪ ν`). -/
theorem predictiveDensity_lt_top_ae_comp [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    ∀ᵐ x ∂(κ ∘ₘ π), predictiveDensity p π x < ∞ := by
  have hac : (κ ∘ₘ π) ≪ ν := by
    rw [comp_eq_withDensity_predictiveDensity hp hκ]
    exact withDensity_absolutelyContinuous ν _
  exact hac.ae_le (predictiveDensity_lt_top_ae hp hκ)

/-- `m > 0` holds `(κ ∘ₘ π)`-a.e.: the data distribution charges no set where its own density
vanishes (not a hypothesis). -/
theorem predictiveDensity_pos_ae [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    ∀ᵐ x ∂(κ ∘ₘ π), 0 < predictiveDensity p π x := by
  rw [ae_iff]
  have hms : MeasurableSet {x | ¬ 0 < predictiveDensity p π x} := by
    simp only [not_lt, nonpos_iff_eq_zero]
    exact measurable_predictiveDensity hp (measurableSet_singleton 0)
  rw [comp_eq_withDensity_predictiveDensity hp hκ, withDensity_apply _ hms]
  refine setLIntegral_eq_zero hms fun x hx => ?_
  simpa only [not_lt, nonpos_iff_eq_zero] using! hx

end StatLean.Bayesian
