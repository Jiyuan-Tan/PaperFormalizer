module
public import Mathlib.Probability.Kernel.Posterior
public import Mathlib.Probability.Kernel.WithDensity

@[expose] public section

/-!
# Dominated Bayesian model — core data model (predictive density, posterior density, Bayes kernel)

Data model for the *dominated* Bayesian setup: a likelihood kernel `K(θ, ·)` that admits a
density `p(θ, x)` with respect to a common dominating measure `ν` on the data space, i.e.
`K θ = ν.withDensity (p θ)`. In this setting Bayes' theorem takes its familiar density form.

Given a prior `π` on the parameter space `Θ` and a nonnegative jointly-measurable density
`p : Θ → 𝓧 → ℝ≥0∞`, this file names:

* the **prior predictive (marginal) density** $m(x) = \int_\Theta p(\theta, x)\,\pi(d\theta)$;
* the **posterior density** $\theta \mapsto p(\theta, x) / m(x)$ with respect to the prior;
* the **Bayes posterior kernel** $x \mapsto \pi.\mathrm{withDensity}(\theta \mapsto p(\theta,x)/m(x))$,
  the explicit density-form posterior.

The theorem that this explicit kernel agrees, for predictive-almost-every `x`, with Mathlib's
abstract posterior `K†π` is `StatLean.Bayesian.Dominated.PosteriorDensity`.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.2, eq. (1.2.3)
(posterior density), p. 9; §1.4, marginal `m(x)`, p. 22.

**Proof formalization notes.** Laptop-only data model — definitions only, all in `ℝ≥0∞`. The
posterior density uses extended-nonnegative division, so it is total: it takes the junk value `0`
wherever `m(x) = 0` or `m(x) = ∞` (both of which are `(K ∘ₘ π)`-null under a finite model, proved
in `Dominated.PredictiveDensity`). `bayesKernel` is built with `Kernel.withDensity` of the
constant kernel `Kernel.const 𝓧 π`; when `Function.uncurry (bayesDensity p π)` is not measurable,
`Kernel.withDensity` returns the zero kernel (Mathlib's junk convention), which is why several
downstream lemmas take joint measurability of `p` as an explicit hypothesis.

**Bibliographic comments.** The density form of Bayes' theorem is the original one: Bayes (1763)
and Laplace ("Mémoire sur la probabilité des causes par les événements," 1774) both worked with
likelihood densities against a uniform base measure. The modern dominated-family framework —
a family of distributions admitting densities with respect to one σ-finite measure — is due to
P. R. Halmos and L. J. Savage, "Application of the Radon–Nikodym theorem to the theory of
sufficient statistics," *Annals of Mathematical Statistics* 20 (1949), 225–241, building on the
Radon–Nikodym theorem (J. Radon 1913; O. Nikodym 1930).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-- The **prior predictive (marginal) density** `m(x) = ∫ p(θ, x) π(dθ)` of the data
(Robert §1.4, the marginal `m(x)`). Junk behavior: may be `0` or `∞` off the support of the data
distribution; both cases are `(K ∘ₘ π)`-null under a finite model. -/
noncomputable def predictiveDensity (p : Θ → 𝓧 → ℝ≥0∞) (π : Measure Θ) : 𝓧 → ℝ≥0∞ :=
  fun x => ∫⁻ θ, p θ x ∂π

/-- The **posterior density** `θ ↦ p(θ, x) / m(x)` with respect to the prior (Robert eq. (1.2.3)).
Extended-nonnegative division: the density is `0` wherever the predictive density `m(x)`
degenerates (`0/0 = 0`, `·/∞ = 0`). -/
noncomputable def bayesDensity (p : Θ → 𝓧 → ℝ≥0∞) (π : Measure Θ) : 𝓧 → Θ → ℝ≥0∞ :=
  fun x θ => p θ x / predictiveDensity p π x

/-- The **Bayes posterior kernel** built from a likelihood density: `x ↦ π.withDensity
(bayesDensity p π x)`, i.e. the posterior `π(·|x) ∝ p(·, x) π` of Robert eq. (1.2.3), realized as
a kernel. Sub-Markov in general (total mass `1` where `0 < m(x) < ∞`, `0` otherwise); it is the
zero kernel when `Function.uncurry (bayesDensity p π)` fails to be measurable. -/
noncomputable def bayesKernel (p : Θ → 𝓧 → ℝ≥0∞) (π : Measure Θ) [IsFiniteMeasure π] :
    Kernel 𝓧 Θ :=
  Kernel.withDensity (Kernel.const 𝓧 π) (bayesDensity p π)

end StatLean.Bayesian
