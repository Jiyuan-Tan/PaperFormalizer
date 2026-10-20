module
public import StatLean.Bayesian.Experiment.Defs

@[expose] public section

/-!
# Bayesian model — basic properties and the posterior disintegration

Textbook-facing restatements, for a `BayesExperiment`, of Mathlib's posterior-kernel identities:

* `posterior_disintegrates_joint` — **predictive × posterior = joint (swapped)**, the core of
  Bayesian conditioning "prior × likelihood becomes predictive × posterior" (Robert §1.4);
* `posterior_comp_predictive` — composing the posterior with the predictive returns the prior.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.4 (a)–(d)
(joint, marginal, posterior, predictive), p. 22.

**Proof formalization notes.** These are *aliases* of pinned Mathlib theorems under
textbook-facing names — we `import` and reuse `ProbabilityTheory.compProd_posterior_eq_map_swap`
and `posterior_comp_self`, we do not reprove them. The probability/Markov instances follow from
the constitutive `BayesExperiment` fields through Mathlib's instance chains.

**Bibliographic comments.** The disintegration of a joint law into a marginal and a regular
conditional distribution originates with A. N. Kolmogorov (*Grundbegriffe*, 1933) and was given
its standard-Borel form by J. L. Doob (*Stochastic Processes*, Wiley, 1953); see also
K. R. Parthasarathy, *Probability Measures on Metric Spaces* (Academic Press, 1967) for the
disintegration theorem Mathlib's `condKernel` implements. Reading "prior × likelihood =
predictive × posterior" as the statistical meaning of this disintegration is the standard Bayesian
viewpoint.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]

namespace BayesExperiment

variable (E : BayesExperiment Θ 𝓧)

instance : IsProbabilityMeasure E.joint := by
  unfold BayesExperiment.joint; infer_instance

instance : IsProbabilityMeasure E.predictive := by
  unfold BayesExperiment.predictive; infer_instance

instance [StandardBorelSpace Θ] [Nonempty Θ] : IsMarkovKernel E.posterior := by
  unfold BayesExperiment.posterior; infer_instance

/-- **The posterior disintegrates the joint distribution**: `predictive ⊗ₘ posterior` equals the
joint distribution with its coordinates swapped (Robert §1.4). Textbook alias of Mathlib's
`compProd_posterior_eq_map_swap`. -/
theorem posterior_disintegrates_joint [StandardBorelSpace Θ] [Nonempty Θ] :
    E.predictive ⊗ₘ E.posterior = E.joint.map Prod.swap := by
  unfold BayesExperiment.predictive BayesExperiment.posterior BayesExperiment.joint
  exact compProd_posterior_eq_map_swap

/-- Composing the posterior kernel with the prior predictive recovers the prior
(Robert §1.4). Textbook alias of Mathlib's `posterior_comp_self`. -/
theorem posterior_comp_predictive [StandardBorelSpace Θ] [Nonempty Θ] :
    E.posterior ∘ₘ E.predictive = E.prior := by
  unfold BayesExperiment.posterior BayesExperiment.predictive
  exact posterior_comp_self

end BayesExperiment

end StatLean.Bayesian
