module
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section

/-!
# Bernstein condition — definition

A real random variable $X$ with mean zero, $\mathbb{E}[X] = 0$, and variance
$\operatorname{Var}(X) = \sigma^2$ satisfies the **Bernstein condition with
parameter $b$** if its higher absolute moments are controlled by
$$\mathbb{E}\,|X|^k \;\le\; \frac{\sigma^2}{2}\,k!\,b^{\,k-2}
  \qquad\text{for all integers } k \ge 3.$$
The cases $k = 1, 2$ are omitted because they are forced by the centering and
variance assumptions ($k = 1$ is $\mathbb{E}[X] = 0$, $k = 2$ is the variance
identity $\mathbb{E}[X^2] = \sigma^2$). Bounded variables satisfy the condition:
if $|X| \le B$ then $X$ is Bernstein with parameter $B/3$ (Lu-BDA §6.1, Example).
The headline use is the implication chain "Bernstein condition $\Rightarrow$
sub-exponential $\Rightarrow$ Bernstein inequality" (assembled in
`Bernstein/MGFBound.lean` and `Bernstein/Bernstein.lean`).

This is a concept-layer foundation; it is theorem-agnostic.

**Reference.** Junwei Lu, *Big Data Analysis*, Springer Nature Switzerland, 2025
(ISBN 978-3-032-03160-0), Chapter 6 (Bernstein and Maximal Inequalities), §6.1,
Definition 6.1 (Bernstein Condition) and Theorem 6.1 (Bernstein Inequality).

**Proof formalization notes.** This file states only the definition; there is no
proof obligation. Two deviations from the bare book statement are deliberate:

* *Range of $k$.* The structure carries the moment bound only for $k \ge 3$,
  together with separate `mean_zero` and `variance_eq` fields for the $k = 1, 2$
  cases. This matches the book, which states the condition for $k \ge 3$ on top
  of the standing centering/variance assumptions.
* *Lower Lebesgue integral instead of Bochner.* The moment bound is stated with
  the lower Lebesgue integral $\int^- |X|^k\,d\mu$ rather than the Bochner
  integral $\int |X|^k\,d\mu$. For a heavy-tailed $X$ (in $L^2$ but not $L^k$,
  $k \ge 3$) the Bochner integral returns Mathlib's junk value $0$, which would
  make the bound hold *vacuously* while $\exp(\lambda X)$ fails to be integrable
  — breaking the Bernstein-$\Rightarrow$-sub-exponential implication. The lower
  Lebesgue integral records the genuine moment ($=\infty$ when the moment is
  infinite), so the bound is a real constraint. ($k-2$ is $\mathbb{N}$-subtraction,
  harmless since $k \ge 3$.)

**Bibliographic comments.** The moment condition
$\mathbb{E}\,|X|^k \le \tfrac12\,k!\,\sigma^2\,b^{k-2}$ is the classical
**Bernstein moment condition**, named for S. N. Bernstein, who introduced this
family of moment hypotheses to derive exponential tail bounds: S. N. Bernstein,
*Theory of Probability* (Теория вероятностей), Gostekhizdat, Moscow–Leningrad,
1927 (with antecedents in his 1924 work on the extension of the limit theorem of
probability theory). The exact factorial form used here is textbook standard and
appears, e.g., as the Bernstein condition in S. Boucheron, G. Lugosi and
P. Massart, *Concentration Inequalities: A Nonasymptotic Theory of Independence*,
Oxford University Press, 2013, §2.8, and in V. H. de la Peña and others' surveys
of sub-exponential variables. The specific factor placement and the
$\sigma^2/2$ normalization follow Lu-BDA §6.1; the constant is conventional and
not attributable to a single seminal equation number.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `HasBernsteinCondition X σ2 b μ`: the centered random variable `X` (with
`E X = 0` and `Var X = σ2` under `μ`) satisfies the Bernstein moment bound with
parameter `b`, i.e. `E |X|ᵏ ≤ (σ2/2)·k!·bᵏ⁻²` for every `k ≥ 3`
(Lu-BDA §6.1, Definition 6.1, Bernstein Condition). -/
structure HasBernsteinCondition (X : Ω → ℝ) (σ2 b : ℝ≥0)
    (μ : Measure Ω := by volume_tac) : Prop where
  /-- Constitutive (Lu-BDA §6.1): the book states the condition for a centered
  variable, `E X = 0`. -/
  mean_zero : ∫ ω, X ω ∂μ = 0
  /-- Constitutive (Lu-BDA §6.1): the parameter `σ2` is the variance of `X`;
  with `E X = 0` this is `E[X²] = σ2`. -/
  variance_eq : ∫ ω, (X ω) ^ 2 ∂μ = (σ2 : ℝ)
  /-- Constitutive (Lu-BDA §6.1): the defining moment bound
  `E |X|ᵏ ≤ (σ2/2)·k!·bᵏ⁻²` for all `k ≥ 3`. Removing it makes the object not
  the book's Bernstein-condition variable. (`k - 2` is `ℕ`-subtraction; harmless
  since `k ≥ 3`.)

  Stated with the **lower Lebesgue integral** `∫⁻ |X|ᵏ` rather than the Bochner
  `∫ |X|ᵏ`: for a heavy-tailed `X` (in `L²` but not `Lᵏ`, `k ≥ 3`) the Bochner
  integral returns Mathlib's junk value `0`, which would make the bound hold
  *vacuously* while `exp(λX)` is not integrable — breaking the
  Bernstein-⇒-sub-exponential implication. `∫⁻` records the genuine moment
  (`= ∞` when the moment is infinite), so the bound is a real constraint. -/
  moment_le : ∀ k : ℕ, 3 ≤ k →
    ∫⁻ ω, ENNReal.ofReal (|X ω| ^ k) ∂μ
      ≤ ENNReal.ofReal ((σ2 : ℝ) / 2 * (k.factorial : ℝ) * (b : ℝ) ^ (k - 2))

end StatLean.ConcentrationInequalities
