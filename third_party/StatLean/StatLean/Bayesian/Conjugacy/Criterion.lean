module
public import StatLean.Bayesian.GeneralizedBayes.Defs
public import StatLean.Bayesian.Dominated.PosteriorDensity

@[expose] public section

/-!
# The conjugacy criterion (normalization principle)

The engine behind every conjugate-prior computation: **if the unnormalized posterior is a positive
finite multiple of a probability measure, the posterior IS that measure.**

* Pointwise: if `π.withDensity (p(·, x)) = c • ρ` with `c ∉ {0, ∞}` and `ρ` a probability
  measure, then `generalizedPosterior p π x = ρ` — no measurability, no almost-everywhere.
* A.e. lift: under a dominated model, if for every `x` the unnormalized posterior is `c(x) • ρ(x)`
  with each `ρ(x)` a probability measure, then `(κ†π) x = ρ x` for predictive-a.e. `x` — with
  **no side conditions on `c`**: evaluating at the whole space forces `c(x) = m(x)`, and Batch 1
  proves `0 < m < ∞` predictive-a.e.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §3.3.2, Definition 3.3.1 (conjugate families) and the
"proportionality" computations of §3.3–§4.2 that this lemma packages.

**Proof formalization notes.** Pointwise: apply the hypothesis to `Set.univ` to identify
`c = predictiveDensity p π x` (`withDensity_apply`, `setLIntegral_univ`, `Measure.smul_apply`,
`measure_univ`), then divide by `c` via `withDensity_smul'` (needs only `c⁻¹ ≠ ∞`) and cancel with
`ENNReal.inv_mul_cancel`. A.e. lift: `filter_upwards` with the Batch-1 headline
`posterior_eq_withDensity_likelihood_div_predictive` and `predictiveDensity_pos_ae` /
`predictiveDensity_lt_top_ae_comp`.

**Bibliographic comments.** "Recognize the posterior up to its normalizing constant" is the
working principle of every conjugate analysis since H. Raiffa and R. Schlaifer (*Applied
Statistical Decision Theory*, 1961); the posterior "is proportional to
f(x|θ)π(θ)" is its informal statement. Packaging it as a reusable measure-theoretic lemma is what
lets each conjugate pair below reduce to one pointwise density identity.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-- **Pointwise normalization principle**: if the unnormalized posterior at `x` is a nondegenerate
multiple of a probability measure, the generalized posterior at `x` is that measure. -/
theorem generalizedPosterior_eq_of_withDensity_eq_smul
    {p : Θ → 𝓧 → ℝ≥0∞} {π : Measure Θ} {x : 𝓧} {ρ : Measure Θ} [IsProbabilityMeasure ρ]
    {c : ℝ≥0∞}
    -- LEAN-ONLY: nondegeneracy of the recognized constant (automatic in the a.e. lift below)
    (hc0 : c ≠ 0) (hc' : c ≠ ∞)
    -- USER-INPUT: the recognized-form identity "prior × likelihood = c · candidate";
    -- Robert §3.3.2 (the conjugate-family computation)
    (h : π.withDensity (fun θ => p θ x) = c • ρ) :
    generalizedPosterior p π x = ρ := by
  have hm : predictiveDensity p π x = c := by
    have hu := congrArg (fun μ => μ Set.univ) h
    simp only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at hu
    exact hu
  have hbd : bayesDensity p π x = c⁻¹ • fun θ => p θ x := by
    funext θ
    simp only [bayesDensity, hm, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [generalizedPosterior_def, hbd, withDensity_smul' c⁻¹ _ (ENNReal.inv_ne_top.mpr hc0), h,
    smul_smul, ENNReal.inv_mul_cancel hc0 hc', one_smul]

/-- **Conjugacy criterion, a.e. lift**: under a dominated model, a pointwise recognized form
`π·p(·,x) = c(x) • ρ(x)` with probability candidates identifies the posterior kernel
predictive-a.e. — no conditions on `c` (forced to equal the predictive density). -/
theorem posterior_ae_eq_of_withDensity_eq_smul
    [StandardBorelSpace Θ] [Nonempty Θ] {π : Measure Θ} [IsFiniteMeasure π]
    {κ : Kernel Θ 𝓧} [IsFiniteKernel κ] {ν : Measure 𝓧} [SFinite ν] {p : Θ → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ))
    {ρ : 𝓧 → Measure Θ}
    -- USER-INPUT: the candidate posteriors are probability measures; Robert §3.3.2
    (hρ : ∀ x, IsProbabilityMeasure (ρ x))
    {c : 𝓧 → ℝ≥0∞}
    -- USER-INPUT: the recognized-form identity at every data point; Robert §3.3.2
    (h : ∀ x, π.withDensity (fun θ => p θ x) = c x • ρ x) :
    ∀ᵐ x ∂(κ ∘ₘ π), (κ†π) x = ρ x := by
  filter_upwards [posterior_eq_withDensity_likelihood_div_predictive hp hκ,
    predictiveDensity_pos_ae hp hκ, predictiveDensity_lt_top_ae_comp hp hκ]
    with x hx hpos htop
  haveI := hρ x
  have hm : predictiveDensity p π x = c x := by
    have hu := congrArg (fun μ => μ Set.univ) (h x)
    simp only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      Measure.smul_apply, measure_univ, smul_eq_mul, mul_one] at hu
    exact hu
  have hc0 : c x ≠ 0 := by rw [← hm]; exact hpos.ne'
  have hc' : c x ≠ ∞ := by rw [← hm]; exact htop.ne
  rw [hx]
  have key := generalizedPosterior_eq_of_withDensity_eq_smul hc0 hc' (h x)
  rw [generalizedPosterior_def] at key
  exact key

end StatLean.Bayesian
