module
public import Mathlib.Probability.Kernel.Posterior

@[expose] public section

/-!
# Bayesian statistical model — core data model (`BayesExperiment`)

A **Bayesian statistical model** bundles a prior distribution on a parameter space `Θ` with a
sampling model — a family of data distributions `θ ↦ f(·|θ)` — presented as a Markov kernel
`likelihood : Kernel Θ 𝓧`. From these three ingredients Bayesian inference produces:

* the **joint distribution** $\pi \otimes_m K$ of parameter and data on $\Theta \times \mathcal X$;
* the **prior predictive** (marginal) distribution $K \circ_m \pi$ of the data on $\mathcal X$
  (Robert's $m(x)$);
* the **posterior kernel** $K^{\dagger}_\pi$ taking data $x$ to the posterior $\pi(\cdot \mid x)$.

This file is a thin textbook-facing wrapper over Mathlib's kernel infrastructure
(`Measure.compProd` `⊗ₘ`, `Measure.bind` `∘ₘ`, and `ProbabilityTheory.posterior` `†`); the
disintegration identity relating these objects is stated in `StatLean.Bayesian.Experiment.Basic`
as an alias of Mathlib's `compProd_posterior_eq_map_swap`.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.2,
Definition 1.2.1 (Bayesian statistical model), p. 9; §1.4, items (a)–(d) (joint, marginal
`m(x)`, posterior, predictive), p. 22.

**Proof formalization notes.** Laptop-only data model — definitions only. `BayesExperiment`
carries the probability/Markov requirements as instance-typed fields (registered as instances),
because Robert's Definition 1.2.1 constitutively demands a *probability* prior and a *family of
probability distributions* for the likelihood; dropping either makes the object not Robert's
Bayesian model. The regularity that Mathlib's posterior requires of the parameter space —
`StandardBorelSpace Θ` and `Nonempty Θ` — is Lean-side and attaches as typeclass arguments on
`posterior`, not as structure fields (Robert never demands a Polish parameter space). Improper
priors (σ-finite, non-probability) are a deliberate extension (Robert §1.5) and out of scope for
this structure.

**Bibliographic comments.** The measure-theoretic Bayesian model — prior on the parameter,
regular conditional distribution for the posterior — is standard; for the kernel/disintegration
formulation used by Mathlib, see the regular-conditional-probability theory of J. L. Doob and the
standard-Borel disintegration theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]

/-- A **Bayesian statistical model** (Robert Definition 1.2.1): a prior probability distribution
on the parameter space `Θ` together with a sampling model presented as a Markov kernel
`likelihood : Kernel Θ 𝓧` (the family `θ ↦ f(·|θ)`). -/
structure BayesExperiment (Θ 𝓧 : Type*) [MeasurableSpace Θ] [MeasurableSpace 𝓧] where
  /-- The prior distribution `π` on the parameter space. -/
  prior : Measure Θ
  /-- The sampling model `θ ↦ f(·|θ)`, as a Markov kernel from parameters to data. -/
  likelihood : Kernel Θ 𝓧
  /-- Constitutive (Robert Def 1.2.1): the prior is a *probability* distribution. Removing this
  makes the object not Robert's Bayesian model (improper priors are the §1.5 extension). -/
  priorIsProbability : IsProbabilityMeasure prior
  /-- Constitutive (Robert Def 1.2.1): each `f(·|θ)` is a probability distribution, i.e. the
  likelihood is a Markov kernel. -/
  likelihoodIsMarkov : IsMarkovKernel likelihood

attribute [instance] BayesExperiment.priorIsProbability BayesExperiment.likelihoodIsMarkov

namespace BayesExperiment

variable (E : BayesExperiment Θ 𝓧)

/-- The **joint distribution** of parameter and data, `π ⊗ₘ K` on `Θ × 𝓧`
(Robert §1.4 (a), `φ(θ, x) = f(x|θ) π(θ)`). -/
noncomputable def joint : Measure (Θ × 𝓧) := E.prior ⊗ₘ E.likelihood

/-- The **prior predictive** (marginal) distribution of the data, `K ∘ₘ π` on `𝓧`
(Robert §1.4 (b), the marginal `m(x) = ∫ f(x|θ) π(dθ)`). -/
noncomputable def predictive : Measure 𝓧 := E.likelihood ∘ₘ E.prior

/-- The **posterior kernel** `x ↦ π(·|x)`, as Mathlib's posterior `K†π` of the likelihood with
respect to the prior (Robert §1.4 (c)). Requires the parameter space to be standard Borel and
nonempty (Lean-side regularity for the regular-conditional-distribution construction). -/
noncomputable def posterior [StandardBorelSpace Θ] [Nonempty Θ] : Kernel 𝓧 Θ :=
  E.likelihood † E.prior

end BayesExperiment

end StatLean.Bayesian
