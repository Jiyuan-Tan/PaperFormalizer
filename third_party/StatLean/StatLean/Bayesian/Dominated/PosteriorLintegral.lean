module
public import StatLean.Bayesian.Dominated.PosteriorDensity

@[expose] public section

/-!
# Posterior expectation formula (dominated form)

The posterior expectation of a nonnegative functional, in dominated form: for predictive-a.e. `x`,
$$\int_\Theta g(\theta)\,\pi(d\theta \mid x)
   = \frac{\int_\Theta g(\theta)\,p(\theta, x)\,\pi(d\theta)}{\int_\Theta p(\theta', x)\,\pi(d\theta')},$$
and its set-indicator special case `π(s | x) = ∫_s p(·,x) dπ / ∫ p(·,x) dπ`.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.4, p. 22 (the
posterior and expectations under it); the formula is eq. (1.2.3) integrated against `g`.

**Proof formalization notes.** Follows from `posterior_eq_withDensity_likelihood_div_predictive`
by `lintegral_withDensity_eq_lintegral_mul` and pulling the constant `(m x)⁻¹` out of the
`lintegral` with `lintegral_mul_const''` (unconditional in `ℝ≥0∞`, so **no positivity hypotheses
needed**). Stated for `ℝ≥0∞`-valued `g`; a real-integrable version can follow later. Watch
CLAUDE.md gotcha 12 (`simp_rw` after the withDensity rewrite).

**Bibliographic comments.** Ratios of the form `∫ g·p dπ / ∫ p dπ` are the computational core of
Bayesian inference — already Laplace's 1774 memoir evaluates posterior expectations of exactly
this shape, and their numerical approximation motivates the Monte Carlo and Laplace-approximation
methods.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  {κ : Kernel Θ 𝓧} {π : Measure Θ} {ν : Measure 𝓧} {p : Θ → 𝓧 → ℝ≥0∞}

/-- **Posterior expectation formula** (Robert §1.4): for predictive-a.e. `x` and measurable
`g ≥ 0`, `∫ g dπ(·|x) = (∫ g·p(·,x) dπ) / (∫ p(·,x) dπ)`. -/
theorem posterior_lintegral_eq_div [StandardBorelSpace Θ] [Nonempty Θ]
    [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ))
    -- LEAN-ONLY: the integrand is measurable
    {g : Θ → ℝ≥0∞} (hg : Measurable g) :
    ∀ᵐ x ∂(κ ∘ₘ π),
      ∫⁻ θ, g θ ∂((κ†π) x) = (∫⁻ θ, g θ * p θ x ∂π) / ∫⁻ θ', p θ' x ∂π := by
  filter_upwards [posterior_eq_withDensity_likelihood_div_predictive (π := π) hp hκ] with x hx
  rw [hx, lintegral_withDensity_eq_lintegral_mul _
    (hp.of_uncurry_right.fun_div measurable_const) hg]
  have hpt : ∀ θ, ((fun θ => p θ x / ∫⁻ θ', p θ' x ∂π) * g) θ
      = (g θ * p θ x) * (∫⁻ θ', p θ' x ∂π)⁻¹ := by
    intro θ; simp only [Pi.mul_apply, div_eq_mul_inv]; ring
  simp_rw [hpt]
  rw [lintegral_mul_const'' _ (hg.fun_mul hp.of_uncurry_right).aemeasurable, ← div_eq_mul_inv]

/-- Set form of Robert eq. (1.2.3): `π(s | x) = ∫_s p(·,x) dπ / ∫ p(·,x) dπ` for predictive-a.e.
`x`. -/
theorem posterior_apply_eq_div [StandardBorelSpace Θ] [Nonempty Θ]
    [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ))
    -- LEAN-ONLY: the target parameter set is measurable
    {s : Set Θ} (hs : MeasurableSet s) :
    ∀ᵐ x ∂(κ ∘ₘ π), (κ†π) x s = (∫⁻ θ in s, p θ x ∂π) / ∫⁻ θ', p θ' x ∂π := by
  filter_upwards [posterior_lintegral_eq_div (π := π) hp hκ (g := s.indicator 1)
    (measurable_const.indicator hs)] with x hx
  rw [← lintegral_indicator_one hs, hx]
  congr 1
  rw [← lintegral_indicator hs]
  refine lintegral_congr fun θ => ?_
  by_cases hθ : θ ∈ s <;> simp [hθ]

end StatLean.Bayesian
