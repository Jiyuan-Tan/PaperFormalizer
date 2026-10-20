module
public import StatLean.ConcentrationInequalities.SubGaussian.Defs

@[expose] public section

/-!
# Bounded random variables are sub-Gaussian (Hoeffding's lemma)

If a random variable $X$ is bounded, $a \le X \le b$ almost surely, then $X$ is
sub-Gaussian with variance proxy $\sigma^2 = (b - a)^2 / 4$. Equivalently, the
centered moment generating function satisfies
$$\mathbb{E}\!\left[e^{\lambda (X - \mathbb{E} X)}\right] \le
  \exp\!\left(\frac{\lambda^2 (b - a)^2}{8}\right), \qquad \lambda \in \mathbb{R}.$$

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 4 (Concentration Inequalities), §4.2,
Theorem 4.6 (Bounded Random Variables); the variance proxy $(b-a)^2/4$ is the
standard statement of Hoeffding's lemma underlying that result.

**Proof formalization notes.** The book's proxy $(b - a)^2 / 4$ is exactly
Mathlib's `(‖b − a‖₊ / 2) ^ 2` (since `‖b − a‖₊ = |b − a|` and
`|b − a|² = (b − a)²`). The result is a direct consequence of Mathlib's Hoeffding
lemma `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc`, which already centers by
the mean — matching our `IsSubGaussian` (a centered `HasSubgaussianMGF`). The
only added hypothesis relative to the book is the a.e.-measurability of `X`,
which the book leaves implicit as a regularity condition.

**Bibliographic comments.** Hoeffding, W. (1963), "Probability inequalities for
sums of bounded random variables", *Journal of the American Statistical
Association* **58**(301), 13–30. The moment-generating-function bound for a
bounded centered random variable (Hoeffding's lemma) is the key step in the proof
of Theorem 2 of that paper (the Hoeffding inequality for sums of bounded
variables); it is now standard textbook material and is what the variance-proxy
statement formalized here records.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A bounded random variable `a ≤ X ≤ b` (a.s.) is sub-Gaussian with variance
proxy `(b − a)² / 4`, written `(‖b − a‖₊ / 2) ^ 2` (Lu-BDA §4.2,
Theorem 4.6 (Bounded Random Variables)). -/
theorem isSubGaussian_of_mem_Icc {X : Ω → ℝ} {a b : ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    -- USER-INPUT: X is (a.e.-)measurable; Lu-BDA §4.2 (regularity, implicit in the book).
    (hm : AEMeasurable X μ)
    -- USER-INPUT: a ≤ X ≤ b almost surely; Lu-BDA §4.2 hypothesis.
    (hb : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    IsSubGaussian X ((‖b - a‖₊ / 2) ^ 2) μ :=
  hasSubgaussianMGF_of_mem_Icc hm hb

end StatLean.ConcentrationInequalities
