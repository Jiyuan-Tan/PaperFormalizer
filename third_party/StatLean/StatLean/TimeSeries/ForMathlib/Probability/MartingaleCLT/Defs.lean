module
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# Martingale-difference arrays — data model (laptop-only)

The triangular-array martingale-difference structure underlying the Brown/Hall–Heyde
martingale CLT (commissioned 2026-08-04 as the probability pillar of the Hannan
Theorem 3.2 program; see `notes/time_series/roadmap.md`):

for each row `n`, a filtration `𝓕_{n,0} ≤ 𝓕_{n,1} ≤ ⋯ ≤ 𝓕_{n,k_n}` and differences
`X_{n,i}` (`i < k_n`) that are `𝓕_{n,i+1}`-measurable, square-integrable, and have
vanishing conditional mean given `𝓕_{n,i}`.

The **conditional variance process** is `V_n = Σ_{i<k_n} E[X_{n,i}² | 𝓕_{n,i}]`; the
Brown conditions (`V_n →p σ²` + conditional Lindeberg) and the CLT live in
`MartingaleCLT/BrownCLT.lean`; the conditional characteristic-function calculus in
`MartingaleCLT/CondCharFun.lean`.

**Reference.** B. M. Brown, *Martingale central limit theorems*, Ann. Math. Statist.
**42** (1971), 59–66; P. Hall and C. C. Heyde, *Martingale Limit Theory and Its
Application*, Academic Press, 1980, Thm 3.2 and Cor 3.1. Consumed by FY Theorem 3.2
(Hannan's ARMA MLE asymptotics) through the score-as-MDS representation.
(`Hall–Heyde Thm 3.2` in tags.)

**Design notes (laptop-only file).**
* Filtrations are plain monotone families `Fin (k n + 1) → MeasurableSpace Ω` (not
  Mathlib `Filtration`s over a preorder) — rows are finite and re-indexed each `n`, so
  the lightweight form avoids `Filtration` coercion friction; `i.castSucc` is "before",
  `i.succ` is "after".
* Only the two-sided essentials are fields (measurability, adaptedness, `L²`,
  conditional centering). Row-wise integrability of products, predictable variance
  measurability etc. are derived, not assumed.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Martingale-difference (triangular) array**: row `n` has `k n` differences adapted
to the row filtration `F n : Fin (k n + 1) → MeasurableSpace Ω`. -/
structure IsMDSArray (k : ℕ → ℕ) (X : (n : ℕ) → Fin (k n) → Ω → ℝ)
    (F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω) (μ : Measure Ω) : Prop where
  /-- Constitutive (Hall–Heyde §3.2): the row filtration is a sub-σ-algebra family. -/
  le_ambient : ∀ n i, F n i ≤ ‹MeasurableSpace Ω›
  /-- Constitutive (Hall–Heyde §3.2): the row filtration is monotone. -/
  mono : ∀ n, Monotone (F n)
  /-- Constitutive (Hall–Heyde §3.2): `X_{n,i}` is `𝓕_{n,i+1}`-measurable. -/
  adapted : ∀ n (i : Fin (k n)), Measurable[F n i.succ] (X n i)
  /-- Constitutive (Hall–Heyde §3.2): square-integrability of the differences. -/
  memLp : ∀ n (i : Fin (k n)), MemLp (X n i) 2 μ
  /-- Constitutive (Hall–Heyde §3.2, the martingale-difference property):
  `E[X_{n,i} | 𝓕_{n,i}] = 0`. -/
  condexp_zero : ∀ n (i : Fin (k n)), μ[X n i | F n i.castSucc] =ᵐ[μ] 0

/-- The **conditional variance process** of a row:
`V_n = Σ_{i<k_n} E[X_{n,i}² | 𝓕_{n,i}]` (Hall–Heyde's `V²_{n,k_n}`). -/
noncomputable def mdsCondVariance (k : ℕ → ℕ) (X : (n : ℕ) → Fin (k n) → Ω → ℝ)
    (F : (n : ℕ) → Fin (k n + 1) → MeasurableSpace Ω) (μ : Measure Ω) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∑ i, μ[fun ω' => X n i ω' ^ 2 | F n i.castSucc] ω

/-- The row sums `S_n = Σ_{i<k_n} X_{n,i}`. -/
def mdsRowSum (k : ℕ → ℕ) (X : (n : ℕ) → Fin (k n) → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i, X n i ω

end StatLean.TimeSeries
