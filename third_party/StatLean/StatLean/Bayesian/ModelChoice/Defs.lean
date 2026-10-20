module
public import StatLean.Bayesian.Dominated.Defs
public import Mathlib.Probability.Kernel.Posterior

@[expose] public section

/-!
# Model choice and testing — core data model

Data model for Bayesian testing, model comparison, and credible sets:

* `bayesFactorM` — the **Bayes factor between two models** as the ratio of marginal (predictive)
  densities, `B₀₁(x) = m₀(x)/m₁(x)`;
* `posteriorModelProb` — the **posterior probability of a model index** in a model-indexed
  experiment `Q : Kernel M 𝓧` with model prior `ϖ`;
* `hypLoss` — the asymmetric **`a₀–a₁` testing loss** for `H₀ : θ ∈ Θ₀`;
* `bayesTest` — the Bayes decision rule for that loss (accept `H₀` iff
  `a₁·π(Θ₀ᶜ|x) ≤ a₀·π(Θ₀|x)`, accepting on ties);
* `IsCredibleSet` — a family `C(x)` of parameter sets with posterior mass `≥ 1 − γ`.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §5.2.1, eq. (5.2.1) and Proposition 5.2.2 (the a₀–a₁ loss and its
Bayes rule), p. 225; §5.2.2, Definition 5.2.5 and eq. (5.2.2) (Bayes factor as marginal ratio),
p. 227; §7.2.1, eq. (7.2.2) (posterior model probabilities), p. 348; §5.5.1, Definition 5.5.2
(α-credible sets), p. 260.

**Proof formalization notes.** Laptop-only data model — definitions only. `bayesFactorM` is
distinct from the Batch-1 event-level `Cond.bayesFactor` (that one conditions two events of one
measure; this one compares two dominated models). `predictiveDensity` serves as Robert's marginal
`m(x)` for improper priors too, so no separate "marginal likelihood" name is introduced.
`posteriorModelProb` needs the model index to be standard Borel — automatic for the intended
finite/countable discrete `M`. `bayesTest` uses classical decidability of `≤` in `ℝ≥0∞` (the rule
is noncomputable, like every posterior quantity here).

**Bibliographic comments.** Bayes factors are due to H. Jeffreys (*Theory of Probability*, 1939);
the modern review is R. E. Kass and A. E. Raftery, "Bayes factors," *J. Amer. Statist. Assoc.* 90
(1995), 773–795. Posterior model probabilities and model averaging in the form (7.2.2)–(7.2.3)
were systematized in the 1990s (A. E. Raftery, D. Madigan, J. A. Hoeting, "Bayesian model averaging
for linear regression models," *J. Amer. Statist. Assoc.* 92 (1997), 179–191). Credible regions
are the Bayesian counterpart of confidence sets, following the HPD tradition of Box and Tiao
(*Bayesian Inference in Statistical Analysis*, Addison-Wesley, 1973).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ Θ₀' Θ₁' 𝓧 M : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  [mΘ₀' : MeasurableSpace Θ₀'] [mΘ₁' : MeasurableSpace Θ₁'] [mM : MeasurableSpace M]

/-- **Bayes factor between two (dominated) models** as the ratio of their marginal densities at
the observed data: `B₀₁(x) = m₀(x)/m₁(x)` (Robert Definition 5.2.5 via eq. (5.2.2)). `ℝ≥0∞`
division junk applies when a marginal degenerates. -/
noncomputable def bayesFactorM (p₀ : Θ₀' → 𝓧 → ℝ≥0∞) (π₀ : Measure Θ₀')
    (p₁ : Θ₁' → 𝓧 → ℝ≥0∞) (π₁ : Measure Θ₁') (x : 𝓧) : ℝ≥0∞ :=
  predictiveDensity p₀ π₀ x / predictiveDensity p₁ π₁ x

/-- **Posterior probability of a model** in a model-indexed experiment: the posterior mass of the
index `m` given data `x` (Robert §7.2.1, eq. (7.2.2)). -/
noncomputable def posteriorModelProb [StandardBorelSpace M] [Nonempty M]
    (Q : Kernel M 𝓧) [IsFiniteKernel Q] (ϖ : Measure M) [IsFiniteMeasure ϖ]
    (x : 𝓧) (m : M) : ℝ≥0∞ :=
  (Q†ϖ) x {m}

open Classical in
/-- The asymmetric **`a₀–a₁` testing loss** for `H₀ : θ ∈ Θ₀` (Robert eq. (5.2.1)): the action
`true` accepts `H₀`; wrongly rejecting costs `a₀`, wrongly accepting costs `a₁`. -/
noncomputable def hypLoss (Θ₀ : Set Θ) (a₀ a₁ : ℝ≥0∞) : Θ → Bool → ℝ≥0∞ :=
  fun θ b => if θ ∈ Θ₀ then (if b then 0 else a₀) else (if b then a₁ else 0)

open Classical in
/-- The **Bayes test** for the `a₀–a₁` loss: accept `H₀` iff the posterior expected loss of
accepting does not exceed that of rejecting, i.e. `a₁·π(Θ₀ᶜ|x) ≤ a₀·π(Θ₀|x)`, accepting on ties
(Robert Proposition 5.2.2 / eq. (5.2.3)). -/
noncomputable def bayesTest [StandardBorelSpace Θ] [Nonempty Θ]
    (κ : Kernel Θ 𝓧) [IsFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π]
    (Θ₀ : Set Θ) (a₀ a₁ : ℝ≥0∞) : 𝓧 → Bool :=
  fun x => if a₁ * (κ†π) x Θ₀ᶜ ≤ a₀ * (κ†π) x Θ₀ then true else false

/-- A family `C(x)` of parameter sets is a **`γ`-credible set family** for the posterior kernel
`post` if its posterior mass is at least `1 − γ` for a.e. data (Robert Definition 5.5.2). -/
def IsCredibleSet (post : Kernel 𝓧 Θ) (m : Measure 𝓧) (C : 𝓧 → Set Θ) (γ : ℝ≥0∞) : Prop :=
  ∀ᵐ x ∂m, 1 - γ ≤ post x (C x)

end StatLean.Bayesian
