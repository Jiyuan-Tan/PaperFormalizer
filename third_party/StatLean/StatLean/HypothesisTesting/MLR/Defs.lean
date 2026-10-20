module
public import Mathlib.MeasureTheory.Measure.MeasureSpace

@[expose] public section

/-!
# Monotone likelihood ratio — core data model

A dominated family with densities `p : Θ → 𝓧 → ℝ` (`Θ` ordered) has **monotone
likelihood ratio (MLR)** in a real statistic `T` when, for `θ < θ'`, the ratio
`p_{θ'}/p_θ` is a nondecreasing function of `T`. We record the division-free (total
positivity of order 2) form:

* `HasMLR p T` — for all `θ < θ'` and all `x, y` with `T x ≤ T y`,
  `p_{θ'}(x)·p_θ(y) ≤ p_θ(x)·p_{θ'}(y)`.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.4 (Distributions with Monotone Likelihood Ratio), the definition of a
family with monotone likelihood ratio. (`TSH4 §3.4`.)

**Proof formalization notes.**
* The TP2 cross-product form avoids division junk entirely (no `0/0` cases) and is
  exactly what the Neyman–Pearson-style arguments consume; the classical "ratio is a
  nondecreasing function of `T`" packaging is derived as a lemma where densities are
  positive.
* Only `Preorder Θ` is required by the definition; the one-sided testing theorems
  assume `LinearOrder Θ`.

**Bibliographic comments.** The MLR condition and the resulting one-sided optimal tests
are due to S. Karlin and H. Rubin ("The theory of decision procedures for distributions
with monotone likelihood ratio," *Ann. Math. Statist.* **27** (1956), 272–299), with
antecedents in the hypergeometric/binomial analyses of J. Neyman and E. S. Pearson;
total positivity is systematized in S. Karlin, *Total Positivity*, Stanford, 1968.
-/

namespace StatLean.HypothesisTesting

variable {Θ 𝓧 : Type*} [Preorder Θ] [MeasurableSpace 𝓧]

/-- **Monotone likelihood ratio** of the density family `p` in the statistic `T`
(division-free TP2 form): for `θ < θ'`, `T x ≤ T y` implies
`p_{θ'}(x)·p_θ(y) ≤ p_θ(x)·p_{θ'}(y)`. -/
def HasMLR (p : Θ → 𝓧 → ℝ) (T : 𝓧 → ℝ) : Prop :=
  ∀ ⦃θ θ' : Θ⦄, θ < θ' → ∀ x y, T x ≤ T y →
    p θ' x * p θ y ≤ p θ x * p θ' y

end StatLean.HypothesisTesting
