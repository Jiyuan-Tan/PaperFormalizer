module
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

/-!
# Sub-Gaussian random variables — definition

A random variable $X$ is *sub-Gaussian with variance proxy $\sigma^2$* if its
centered moment generating function is dominated by that of a centered Gaussian
with variance $\sigma^2$:
$$ \mathbb{E}\bigl[\exp\bigl(\lambda (X - \mathbb{E} X)\bigr)\bigr]
   \le \exp\!\left(\frac{\lambda^2 \sigma^2}{2}\right)
   \qquad \text{for all } \lambda \in \mathbb{R}. $$
Equivalently, the tails of $X$ decay at least as fast as those of a Gaussian.
This is the foundational object of the concentration-inequalities area: Markov /
Chernoff bounds, Gaussian-type tail bounds, Hoeffding's inequality, and the
maximal inequalities are all derived from this single MGF condition.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 4 (Concentration Inequalities), §4.2,
Definition 4.1 (Sub-Gaussian). The Lean statement matches the book's
centered-MGF definition with variance proxy $\sigma^2$.

**Proof formalization notes.** We formalize `IsSubGaussian` as a thin bridge to
Mathlib's `ProbabilityTheory.HasSubgaussianMGF` applied to the **centered**
variable $X - \mathbb{E}[X]$. Mathlib's predicate bounds the *raw* MGF
(`mgf X μ t ≤ exp (c t²/2)`, via `cgf_le`); centering by the Bochner mean
$\int X \, d\mu$ recovers the textbook form and immediately inherits the Mathlib
MGF / Chernoff / Hoeffding / Azuma toolkit. Edge behavior: for non-integrable
$X$ the Bochner integral is Mathlib's junk value $0$, so the definition reduces
to the un-centered Mathlib predicate. `isSubGaussian_iff` records that
`IsSubGaussian` is definitionally this centered `HasSubgaussianMGF`. The
textbook theorems (Markov, Chernoff, tails, Hoeffding, …) live in sibling files
and consume `IsSubGaussian`; concept files never import assembly files.

**Bibliographic comments.** The notion of a sub-Gaussian random variable is
classical folklore with no single seminal origin. The terminology and the
defining MGF bound trace to J.-P. Kahane, "Propriétés locales des fonctions à
séries de Fourier aléatoires," *Studia Mathematica* 19 (1960), 1–25, and the
systematic study to V. V. Buldygin and Yu. V. Kozachenko, "Sub-Gaussian random
variables," *Ukrainian Mathematical Journal* 32 (1980), 483–489. The
variance-proxy MGF formulation used here is the standard modern synthesis (see
also Wainwright, *High-Dimensional Statistics*, 2019, §2.1.2, Def. 2.2;
Boucheron, Lugosi & Massart, *Concentration Inequalities*, 2013, §2.3); no
attribution to a single research paper is appropriate.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `IsSubGaussian X σ2 μ`: the random variable `X` is sub-Gaussian with variance
proxy `σ2` under the measure `μ`, i.e. its centered moment generating function
satisfies `E[exp(λ (X − E[X]))] ≤ exp(λ² σ2 / 2)` for every `λ ∈ ℝ`
(Lu-BDA §4.2, Definition 4.1 (Sub-Gaussian)).

Implemented as `ProbabilityTheory.HasSubgaussianMGF` of the centered variable
`fun ω => X ω − ∫ x, X x ∂μ`. The mean `∫ x, X x ∂μ` is the Bochner integral of
`X`; for non-integrable `X` it is `0` (Mathlib's junk value), in which case this
reduces to the un-centered Mathlib predicate. -/
def IsSubGaussian (X : Ω → ℝ) (σ2 : ℝ≥0) (μ : Measure Ω := by volume_tac) : Prop :=
  HasSubgaussianMGF (fun ω => X ω - ∫ x, X x ∂μ) σ2 μ

/-- Unfolding lemma: `IsSubGaussian` is definitionally the centered
`HasSubgaussianMGF`. -/
theorem isSubGaussian_iff {X : Ω → ℝ} {σ2 : ℝ≥0} {μ : Measure Ω} :
    IsSubGaussian X σ2 μ ↔ HasSubgaussianMGF (fun ω => X ω - ∫ x, X x ∂μ) σ2 μ :=
  Iff.rfl

end StatLean.ConcentrationInequalities
