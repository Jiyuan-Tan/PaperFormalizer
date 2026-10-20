module
public import Mathlib.Probability.ConditionalProbability

@[expose] public section

/-!
# Prior odds, posterior odds, and the Bayes factor — core data model

Data model for the odds-based reformulation of Bayes' theorem for a single hypothesis event
`s` (with alternative `sᶜ`) against observed data `d`, on a measure space `(Ω, μ)`.

Writing $\mu[t \mid s]$ for the conditional probability of $t$ given $s$
(Mathlib's `ProbabilityTheory.cond`, notation `μ[t | s]`), this file names three ratios:

* the **prior odds** $\mu(s) / \mu(s^c)$ of the hypothesis before seeing data;
* the **posterior odds** $\mu[s \mid d] / \mu[s^c \mid d]$ after seeing data;
* the **Bayes factor** $\mu[d \mid s] / \mu[d \mid s^c]$, the likelihood ratio of the data
  under the hypothesis versus its alternative.

The central identity — *posterior odds = prior odds × Bayes factor* — is proved in
`StatLean.Bayesian.Cond.Odds`; this file only fixes the vocabulary.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.2 (Bayes' theorem, p. 8) for the
odds form of Bayes' theorem; §5.2.2, Definition 5.2.5 (Bayes factor) and eq. (5.2.2), p. 227.

**Proof formalization notes.** This is a laptop-only shared data model — definitions only.
Everything is expressed with Mathlib's `ProbabilityTheory.cond`. All three quantities live in
`ℝ≥0∞`, so division follows the extended-nonnegative conventions (`x / 0 = ∞` for `x ≠ 0`,
`0 / 0 = 0`, `x / ∞ = 0`): the ratios are total and require no positivity side conditions to
*state*, though the Bayes-factor inversion in `Cond.Odds` does need nondegenerate priors.

**Bibliographic comments.** The odds/Bayes-factor formulation of hypothesis comparison is due to
H. Jeffreys (*Theory of Probability*, Oxford, 1939); the terminology "Bayes factor" and its role
in model choice are surveyed by R. E. Kass and A. E. Raftery (*Bayes factors*, J. Amer. Statist.
Assoc. 90 (1995), 773–795).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- The **prior odds** of a hypothesis event `s`: the ratio `μ s / μ sᶜ` of its probability to
that of its complement, before conditioning on data (Robert §5.2.2, the prior ratio `ρ₀/ρ₁`
of Definition 5.2.5). Extended-nonnegative division: equals `∞` when `μ sᶜ = 0 < μ s` and `0`
when `μ s = 0`. -/
noncomputable def priorOdds (μ : Measure Ω) (s : Set Ω) : ℝ≥0∞ := μ s / μ sᶜ

/-- The **posterior odds** of a hypothesis event `s` given data `d`: the ratio
`μ[s | d] / μ[sᶜ | d]` of the posterior probability of `s` to that of its complement
(Robert §5.2.2, the posterior ratio of Definition 5.2.5). Extended-nonnegative division. -/
noncomputable def posteriorOdds (μ : Measure Ω) (s d : Set Ω) : ℝ≥0∞ := μ[s | d] / μ[sᶜ | d]

/-- The **Bayes factor** of a hypothesis event `s` against `sᶜ` for data `d`: the likelihood
ratio `μ[d | s] / μ[d | sᶜ]` of the data under the hypothesis versus its alternative
(Robert §5.2.2, Definition 5.2.5; eq. (5.2.2) writes it as the marginal ratio `m₀(x)/m₁(x)`).
Extended-nonnegative division. -/
noncomputable def bayesFactor (μ : Measure Ω) (s d : Set Ω) : ℝ≥0∞ := μ[d | s] / μ[d | sᶜ]

end StatLean.Bayesian
