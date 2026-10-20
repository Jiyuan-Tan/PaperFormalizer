module
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

/-!
# Sub-exponential random variables — definition

A random variable $X$ is *sub-exponential with parameter $\alpha$* if its
centered moment generating function satisfies
$$\mathbb{E}\!\left[\exp\big(\lambda\,(X - \mathbb{E}X)\big)\right]
  \le \exp\!\left(\tfrac{\lambda^2 \alpha^2}{2}\right)
  \qquad\text{for all } |\lambda| \le \tfrac{1}{\alpha}.$$

The key difference from the sub-Gaussian definition is the **restricted range**
of $\lambda$: the sub-Gaussian MGF bound holds for all $\lambda \in \mathbb{R}$,
whereas the sub-exponential bound is required only on the interval
$|\lambda| \le 1/\alpha$. The Lean formalization carries one addition relative to
the book statement: an explicit **integrability** requirement of the centered
exponential $\exp(\lambda\,(X-\mathbb{E}X))$ on the same range, so that the MGF
is the genuine Bochner integral rather than Mathlib's junk value. The book leaves
this implicit (the MGF is assumed to exist on the range). The degenerate parameter
$\alpha = 0$ collapses the range to $\lambda = 0$ (since $1/0 = 0$ in $\mathbb{R}$),
where the bound reads $\mathrm{mgf}(\cdot)(0) \le 1$.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0). Chapter 5 (Sub-exponential Random Variables), §5.2,
Definition 5.1 (Sub-exponential).

**Proof formalization notes.** Mathlib has no predicate for the restricted-range
MGF bound, so we build it here as a structure over the **centered** variable
$X - \mathbb{E}[X]$, mirroring the shape of
`ProbabilityTheory.HasSubgaussianMGF` (an MGF-bound field plus an integrability
field). The mean is the Bochner integral `∫ x, X x ∂μ` (Mathlib junk value `0`
for non-integrable `X`). This is a concept-layer foundation: the sub-exponential
tail bound (Theorem 5.2), the sample-mean concentration, and the Bernstein
machinery (Chapter 6, Bernstein and Maximal Inequalities, §6.1, Theorem 6.1
(Bernstein Inequality)) all consume `IsSubExponential`.

**Bibliographic comments.** The sub-exponential class via a restricted-range MGF
(equivalently, sub-exponential characterized by Orlicz $\psi_1$-norm,
linear-in-$t$ MGF growth, or exponential tails) is folklore with no
single seminal origin; it is standard background for the Bernstein-type
inequalities tracing to S. N. Bernstein (1920s). A modern treatment is
M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019 (§2.1.3, Def. of sub-exponential variables and
the $(\nu^2, \alpha)$-Bernstein condition). The two-parameter form used there
($\mathbb{E}[e^{\lambda(X-\mu)}] \le e^{\nu^2\lambda^2/2}$ for
$|\lambda| < 1/\alpha$) specializes to the single-parameter $\alpha$ form here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `IsSubExponential X α μ`: the random variable `X` is sub-exponential with
parameter `α` under `μ`, i.e. its centered moment generating function satisfies
`E[exp(λ (X − E[X]))] ≤ exp(λ² α² / 2)` for every `λ` with `|λ| ≤ 1/α`
(Lu-BDA §5.2, Definition 5.1 (Sub-exponential)).

The centered variable is `fun ω => X ω − ∫ x, X x ∂μ`; the mean is the Bochner
integral (Mathlib junk value `0` for non-integrable `X`). For the degenerate
`α = 0` the range collapses to `λ = 0` (`1/0 = 0` in `ℝ`), where the bound reads
`mgf … 0 ≤ 1`. -/
structure IsSubExponential (X : Ω → ℝ) (α : ℝ≥0) (μ : Measure Ω := by volume_tac) :
    Prop where
  /-- Constitutive (Lu-BDA §5.2, Definition 5.1 (Sub-exponential)): on the restricted range
  `|λ| ≤ 1/α`, the centered MGF obeys the sub-Gaussian-type bound
  `mgf (X − E X) λ ≤ exp(λ² α² / 2)`. Removing this makes the object not the
  book's sub-exponential variable. -/
  mgf_le : ∀ l : ℝ, |l| ≤ 1 / (α : ℝ) →
    mgf (fun ω => X ω - ∫ x, X x ∂μ) μ l ≤ Real.exp (l ^ 2 * (α : ℝ) ^ 2 / 2)
  /-- Regularity (LEAN-ONLY): integrability of the centered exponential on the
  range, so that `mgf` is the genuine integral rather than Mathlib's junk `0`.
  Bundled to mirror Mathlib's `HasSubgaussianMGF.integrable_exp_mul`; the book
  leaves it implicit (the MGF is assumed to exist on the range). -/
  integrable_exp_mul : ∀ l : ℝ, |l| ≤ 1 / (α : ℝ) →
    Integrable (fun ω => Real.exp (l * (X ω - ∫ x, X x ∂μ))) μ

/-- The centered MGF bound carried by `IsSubExponential`, extracted for the
range `0 ≤ l ≤ 1/α` used by the one-sided Chernoff tail (Theorem 5.2). -/
theorem IsSubExponential.mgf_le_of_mem_Icc {X : Ω → ℝ} {α : ℝ≥0} {μ : Measure Ω}
    (hX : IsSubExponential X α μ) {l : ℝ} (hl₀ : 0 ≤ l) (hl₁ : l ≤ 1 / (α : ℝ)) :
    mgf (fun ω => X ω - ∫ x, X x ∂μ) μ l ≤ Real.exp (l ^ 2 * (α : ℝ) ^ 2 / 2) :=
  hX.mgf_le l (by rw [abs_of_nonneg hl₀]; exact hl₁)

end StatLean.ConcentrationInequalities
