module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-!
# E-variables and p-variables — definitions

Concept-layer data model for **e-values**. Fix a simple null hypothesis represented by a
probability measure $\mu$ on the sample space $\Omega$.

* An **e-variable** is a nonnegative statistic $E : \Omega \to \mathbb{R}$ whose expectation under
  the null is at most one, $\mathbb{E}_\mu[E] \le 1$. Its realized values are *e-values*.
  E-variables are the natural currency for *optional continuation* (sequential testing with
  data-dependent stopping), where p-values fail.
* A **p-variable** is a statistic $P : \Omega \to \mathbb{R}$ with $\mu\{P \le \alpha\} \le \alpha$
  for every $\alpha \in (0,1)$ — exactly the super-uniformity property (see [[`SuperUniform`]])
  restricted to $(0,1)$. Its realized values are *p-values*.

The two notions are linked by the conversion $P = 1/E$, proved in the sibling assembly file
`EValues/Conversion.lean`. These definitions are theorem-agnostic.

**Reference.** E. J. Candès, *STAT 300C: Theory of Statistics*, Lecture Notes, Stanford University,
2023, Lecture 15 (E-values), Definition 3 (e-variable) and Definition 4 (p-variable); the
conversion $P = 1/E$ is Proposition 3 of the same lecture.

**Proof formalization notes.** The defining inequality $\mathbb{E}_\mu[E] \le 1$ is stated as a
**lower integral** $\int^- \mathrm{ofReal}(E)\,d\mu \le 1$ rather than as a Bochner integral. For a
nonnegative measurable $E$ this $\int^-$ is the genuine (possibly $+\infty$) expectation, so
bounding it by $1$ both encodes $\mathbb{E}_\mu[E] \le 1$ *and* witnesses finiteness — forcing
integrability of $E$. The Bochner form $\int E\,d\mu \le 1$ would be unsound here: a non-integrable
nonnegative $E$ has Bochner integral $0 \le 1$ *vacuously*, so it would spuriously qualify with
infinite true expectation and break the e→p conversion. Measurability of $E$ is carried as a field
because the expectation must be the genuine null expectation. The p-variable side restricts
super-uniformity to the open unit interval $(0,1)$, matching the book's Definition 4.

**Bibliographic comments.** The e-value / e-variable formalism originates in the betting-based
approach to hypothesis testing. The standard reference for the calibration and combination theory
of e-values is V. Vovk and R. Wang, "E-values: Calibration, combination and applications,"
*The Annals of Statistics* **49**(3):1736–1754, 2021, where e-variables are defined as nonnegative
random variables with expectation at most one under the null and the duality with p-values
(notably $P = 1/E$ and the calibration map) is developed. The conceptual "testing by betting"
viewpoint that motivates e-values as wealth processes is laid out in G. Shafer, "Testing by
betting: A strategy for statistical and scientific communication," *Journal of the Royal
Statistical Society: Series A* **184**(2):407–431, 2021 (read before the Society, with discussion).
The Candès lecture notes synthesize these sources; the definitions formalized here follow that
synthesis.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.MultipleTesting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `IsEVariable E μ`: the statistic `E : Ω → ℝ` is an **e-variable** for the simple null `μ`
(Candès, Lecture 15, Def. 3, STAT 300C) — nonnegative with `Eμ[E] ≤ 1`. -/
structure IsEVariable (E : Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- Constitutive (Candès, L15, Def. 3): an e-variable is a *nonnegative* random variable. -/
  nonneg : ∀ ω, 0 ≤ E ω
  /-- Constitutive (Candès, L15, Def. 3): `E` is a statistic, hence measurable — needed for the
  expectation in `expectation_le_one` to be the genuine null expectation. -/
  measurable : Measurable E
  /-- Constitutive (Candès, L15, Def. 3): the defining inequality `Eμ[E] ≤ 1`, stated as the
  **lower integral** of `ofReal ∘ E`. For a nonnegative measurable `E` this `∫⁻` is the genuine
  (possibly `∞`) expectation, so bounding it by `1` both encodes `Eμ[E] ≤ 1` *and* witnesses
  finiteness — forcing integrability of `E`. (The Bochner form `∫ E ∂μ ≤ 1` is unsound here: a
  non-integrable nonneg `E` has Bochner integral `0 ≤ 1` *vacuously*, so it would qualify with
  infinite true expectation and break the e→p conversion.) -/
  expectation_le_one : ∫⁻ ω, ENNReal.ofReal (E ω) ∂μ ≤ 1

/-- `IsPVariable P μ`: the statistic `P : Ω → ℝ` is a **p-variable** for the simple null `μ`
(Candès, Lecture 15, Def. 4, STAT 300C) — `μ{P ≤ α} ≤ α` for every `α ∈ (0,1)`. This is the
[[`SuperUniform`]] property on the open unit interval. -/
def IsPVariable (P : Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ α : ℝ, 0 < α → α < 1 → μ {ω | P ω ≤ α} ≤ ENNReal.ofReal α

end StatLean.MultipleTesting
