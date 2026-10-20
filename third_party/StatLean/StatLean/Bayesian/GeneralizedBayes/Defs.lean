module
public import StatLean.Bayesian.Dominated.Defs

@[expose] public section

/-!
# Generalized Bayes — core data model (posteriors from σ-finite priors)

Data model for **generalized (improper-prior) Bayesian inference**: for a σ-finite prior `π` —
not necessarily a probability, e.g. Lebesgue measure as the flat prior — and a likelihood density
`p`, the **generalized posterior** at data `x` is
$$\pi_x(d\theta) = \frac{p(\theta, x)\,\pi(d\theta)}{\int_\Theta p(\theta', x)\,\pi(d\theta')},$$
a genuine probability measure whenever the pseudo-marginal `m(x) = ∫ p(θ', x) π(dθ')` is positive
and finite (posterior propriety).

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.5 (improper prior distributions), pp. 26–30; the generalized
posterior display on p. 28 and the propriety condition `∫ f(x|θ)π(θ)dθ < ∞` on p. 30.

**Proof formalization notes.** Laptop-only data model — definitions only. The definition reuses
the Batch-1 `bayesDensity p π x = p θ x / predictiveDensity p π x` verbatim; `Measure.withDensity`
needs no finiteness of `π`, so the same formula covers proper and improper priors. On probability
priors it agrees `(κ ∘ₘ π)`-a.e. with the abstract posterior `κ†π` (Batch-1
`posterior_eq_withDensity_likelihood_div_predictive`); the pinned `posterior` itself requires
`IsFiniteMeasure π` and thus does not exist in the improper case — this definition is the
extension. Junk: the zero measure wherever `m(x) ∈ {0, ∞}` (`0/0 = 0`, `·/∞ = 0`).

**Bibliographic comments.** Improper priors begin with Laplace's uniform "prior of ignorance"
(1774) and were systematized by H. Jeffreys (*Theory of Probability*, 1939), whose invariance
priors are typically improper. The σ-finite formulation with the propriety condition is standard;
improper priors are safe for estimation but dangerous for Bayes factors, formalized in
`GeneralizedBayes.Basic`. See also
A. P. Dawid, M. Stone and J. V. Zidek, "Marginalization paradoxes in Bayesian and structural
inference," *J. Roy. Statist. Soc. B* 35 (1973), 189–233 for the classical pitfalls.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-- The **generalized posterior** from a (possibly improper, σ-finite) prior: the prior reweighted
by the normalized likelihood density, `π.withDensity (p(·,x) / m(x))` (Robert §1.5, p. 28). Junk:
the zero measure wherever the pseudo-marginal `m(x)` is `0` or `∞`. -/
noncomputable def generalizedPosterior (p : Θ → 𝓧 → ℝ≥0∞) (π : Measure Θ) (x : 𝓧) :
    Measure Θ :=
  π.withDensity (bayesDensity p π x)

@[simp]
theorem generalizedPosterior_def (p : Θ → 𝓧 → ℝ≥0∞) (π : Measure Θ) (x : 𝓧) :
    generalizedPosterior p π x = π.withDensity (bayesDensity p π x) := rfl

end StatLean.Bayesian
