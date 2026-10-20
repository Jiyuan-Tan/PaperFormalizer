module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Kernel.Basic

@[expose] public section

/-!
# Randomized tests — core data model

A **randomized test** (critical function) is a measurable `φ : 𝓧 → [0,1]`: on observing
`x`, the null hypothesis is rejected with probability `φ(x)`. Its **power function**
against a model `P : Θ → Measure 𝓧` is `θ ↦ ∫ φ dP_θ`. This file fixes the test-class
predicates the whole area quantifies over:

* `IsCriticalFn φ` — measurable with values in `[0,1]`;
* `power P φ θ` — the power function;
* `IsLevel P Θ₀ φ α` — size at most `α` on the null set `Θ₀`;
* `IsMostPowerful P₀ P₁ α φ` — most powerful level-`α` for a simple null vs simple
  alternative;
* `IsUMP P Θ₀ Θ₁ α φ` — uniformly most powerful level-`α`;
* `IsUnbiasedTest P Θ₀ Θ₁ α φ`, `IsUMPU P Θ₀ Θ₁ α φ` — unbiasedness and UMP-unbiased;
* `IsSimilar P ω α φ` — power identically `α` on `ω`;
* `HasNeymanStructure T Q ν α φ` — conditional size `α` given a sufficient statistic.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 3 (Uniformly Most
Powerful Tests), §3.1 (Stating the Problem), the formulation of a randomized test, its level
and its power function. (`TSH4 §3.1`.)

**Proof formalization notes.**
* Powers are real Bochner integrals: for probability measures and `0 ≤ φ ≤ 1` they are
  always finite, so no `ℝ≥0∞` bookkeeping is needed at the definition layer.
* Predicates are deliberately unbundled (`IsCriticalFn` is a separate conjunct wherever
  a class of competitors is quantified over), so theorems can weaken or strengthen the
  competitor class explicitly.
* `HasNeymanStructure` takes the θ-free conditional kernel `Q` (from the sufficiency
  theory of the point-estimation area) and a reference law `ν` on the statistic's range:
  the conditional expectation of `φ` given `T = t` equals `α` for `ν`-a.e. `t`.

**Bibliographic comments.** The randomized-test formulation, power functions, and the
optimality program are due to J. Neyman and E. S. Pearson ("On the problem of the most
efficient tests of statistical hypotheses," *Phil. Trans. R. Soc. A* **231** (1933),
289–337). Unbiasedness of tests was introduced by J. Neyman and E. S. Pearson
("Contributions to the theory of testing statistical hypotheses," *Stat. Res. Mem.*
**1** (1936), 1–37); similar regions and their Neyman structure go back to J. Neyman
("Sur la vérification des hypothèses statistiques composées," *Bull. Soc. Math. France*
**63** (1935), 246–266) and were systematized by E. L. Lehmann and H. Scheffé
("Completeness, similar regions, and unbiased estimation," *Sankhyā* **10** (1950),
305–340).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.HypothesisTesting

variable {Θ 𝓧 𝓣 : Type*} [MeasurableSpace 𝓧] [MeasurableSpace 𝓣]

/-- A **critical function** (randomized test): measurable, `[0,1]`-valued. -/
def IsCriticalFn (φ : 𝓧 → ℝ) : Prop :=
  Measurable φ ∧ ∀ x, φ x ∈ Set.Icc (0 : ℝ) 1

/-- The **power function** of the test `φ` against the model `P`. -/
noncomputable def power (P : Θ → Measure 𝓧) (φ : 𝓧 → ℝ) (θ : Θ) : ℝ :=
  ∫ x, φ x ∂(P θ)

/-- The power of `φ` against a single distribution. -/
noncomputable def powerAgainst (P : Measure 𝓧) (φ : 𝓧 → ℝ) : ℝ :=
  ∫ x, φ x ∂P

/-- **Level-`α`** test on the null set `Θ₀`: power at most `α` there. -/
def IsLevel (P : Θ → Measure 𝓧) (Θ₀ : Set Θ) (φ : 𝓧 → ℝ) (α : ℝ) : Prop :=
  ∀ θ ∈ Θ₀, power P φ θ ≤ α

/-- **Most powerful level-`α` test** of the simple null `P₀` against the simple
alternative `P₁`. -/
def IsMostPowerful (P₀ P₁ : Measure 𝓧) (α : ℝ) (φ : 𝓧 → ℝ) : Prop :=
  IsCriticalFn φ ∧ powerAgainst P₀ φ ≤ α ∧
    ∀ ψ, IsCriticalFn ψ → powerAgainst P₀ ψ ≤ α → powerAgainst P₁ ψ ≤ powerAgainst P₁ φ

/-- **Uniformly most powerful level-`α` test** of `Θ₀` against `Θ₁`. -/
def IsUMP (P : Θ → Measure 𝓧) (Θ₀ Θ₁ : Set Θ) (α : ℝ) (φ : 𝓧 → ℝ) : Prop :=
  IsCriticalFn φ ∧ IsLevel P Θ₀ φ α ∧
    ∀ ψ, IsCriticalFn ψ → IsLevel P Θ₀ ψ α → ∀ θ ∈ Θ₁, power P ψ θ ≤ power P φ θ

/-- **Unbiased test**: power at most `α` on the null, at least `α` on the
alternative. -/
def IsUnbiasedTest (P : Θ → Measure 𝓧) (Θ₀ Θ₁ : Set Θ) (α : ℝ) (φ : 𝓧 → ℝ) : Prop :=
  IsLevel P Θ₀ φ α ∧ ∀ θ ∈ Θ₁, α ≤ power P φ θ

/-- **UMP unbiased level-`α` test**: unbiased of level `α`, and at least as powerful as
every unbiased level-`α` competitor, everywhere on the alternative. -/
def IsUMPU (P : Θ → Measure 𝓧) (Θ₀ Θ₁ : Set Θ) (α : ℝ) (φ : 𝓧 → ℝ) : Prop :=
  IsCriticalFn φ ∧ IsUnbiasedTest P Θ₀ Θ₁ α φ ∧
    ∀ ψ, IsCriticalFn ψ → IsUnbiasedTest P Θ₀ Θ₁ α ψ →
      ∀ θ ∈ Θ₁, power P ψ θ ≤ power P φ θ

/-- **Similar test** on `ω`: power identically `α` there. -/
def IsSimilar (P : Θ → Measure 𝓧) (ω : Set Θ) (α : ℝ) (φ : 𝓧 → ℝ) : Prop :=
  ∀ θ ∈ ω, power P φ θ = α

/-- **Neyman structure** with respect to a statistic `T` with θ-free conditional kernel
`Q` and reference law `ν` on its range: the conditional size given `T = t` equals `α`
for `ν`-a.e. `t`. -/
def HasNeymanStructure (T : 𝓧 → 𝓣) (Q : Kernel 𝓣 𝓧) (ν : Measure 𝓣) (α : ℝ)
    (φ : 𝓧 → ℝ) : Prop :=
  ∀ᵐ t ∂ν, ∫ x, φ x ∂(Q t) = α

end StatLean.HypothesisTesting
