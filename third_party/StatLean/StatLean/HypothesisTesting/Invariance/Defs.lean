module
public import StatLean.PointEstimation.Equivariance.Defs
public import StatLean.HypothesisTesting.Tests.Defs

@[expose] public section

/-!
# Invariant tests — core data model

A testing problem is **invariant** under a group `G` acting (measurably) on the sample
space with an induced action on the parameter space when the model intertwines the two
actions and the null and alternative parameter sets are stable. The invariance
reduction replaces the data by a **maximal invariant** — an invariant statistic that
separates the orbits — and tests by **invariant tests**. This file fixes:

* invariant model — reused from the point-estimation area (`IsInvariantModel`);
* `IsInvariantTest φ` — `φ(g·x) = φ(x)`;
* `IsMaximalInvariant M` — invariant and orbit-separating;
* `IsAlmostInvariant μ φ` — invariant up to a `μ`-null set, per group element;
* `IsUMPInvariant P Θ₀ Θ₁ α φ` — UMP among invariant level-`α` tests;
* `orbitAverage G φ` — the finite-group symmetrization `|G|⁻¹ ∑_g φ(g·x)`.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 6 (Invariance), §6.1
(Symmetry and Invariance), the definitions of an invariant testing problem and of an invariant
test. (`TSH4 §6.1`.)

**Proof formalization notes.**
* The induced parameter action is data (a `MulAction G Θ` instance) with the model
  intertwining law `IsInvariantModel` (from `StatLean.PointEstimation.Equivariance`);
  stability of `Θ₀`, `Θ₁` under it enters as hypotheses of the theorems.
* `IsMaximalInvariant` is the set-level notion (invariance + orbit separation);
  the measurable-factorization upgrade carries its own hypotheses in the theorems.
* Almost invariance quantifies a.e. per group element (`∀ g, ∀ᵐ x`), the classical
  reading; joint-measurability strengthenings appear only in theorem hypotheses.

**Bibliographic comments.** Invariance as a systematic reduction principle for tests is
due to G. A. Hunt and C. Stein ("Most stringent tests of statistical hypotheses,"
unpublished, 1946), developed in E. L. Lehmann's lecture tradition and in C. Stein's
work; maximal invariants and the factorization of invariant statistics are classical
(cf. W. J. Hall, R. A. Wijsman, J. K. Ghosh, "The relationship between sufficiency and
invariance with applications in sequential analysis," *Ann. Math. Statist.* **36**
(1965), 575–614). Almost invariance and its equivalence with invariance under
quasi-invariant group measures follow A. Berk and probabilistic refinements of the
Hunt–Stein circle of ideas.
-/

open MeasureTheory
open scoped ENNReal

namespace StatLean.HypothesisTesting

open StatLean.PointEstimation (IsInvariantModel)

variable {G Θ 𝓧 𝓘 : Type*} [Group G] [MeasurableSpace 𝓧] [MulAction G 𝓧] [MulAction G Θ]

/-- **Invariant test**: unchanged along every orbit. -/
def IsInvariantTest (G : Type*) [Group G] [MulAction G 𝓧] (φ : 𝓧 → ℝ) : Prop :=
  ∀ (g : G) (x : 𝓧), φ (g • x) = φ x

/-- **Maximal invariant**: invariant, and separating the orbits (equal values only on a
common orbit). -/
def IsMaximalInvariant (G : Type*) [Group G] [MulAction G 𝓧] (M : 𝓧 → 𝓘) : Prop :=
  (∀ (g : G) (x : 𝓧), M (g • x) = M x) ∧
    ∀ x y, M x = M y → ∃ g : G, y = g • x

/-- **Almost invariant test** w.r.t. `μ`: for each group element, invariant off a
`μ`-null set. -/
def IsAlmostInvariant (G : Type*) [Group G] [MulAction G 𝓧] (μ : Measure 𝓧)
    (φ : 𝓧 → ℝ) : Prop :=
  ∀ g : G, ∀ᵐ x ∂μ, φ (g • x) = φ x

/-- **UMP invariant level-`α` test**: invariant, level `α`, and at least as powerful as
every invariant level-`α` competitor on the alternative. -/
def IsUMPInvariant (G : Type*) [Group G] [MulAction G 𝓧] (P : Θ → Measure 𝓧)
    (Θ₀ Θ₁ : Set Θ) (α : ℝ) (φ : 𝓧 → ℝ) : Prop :=
  IsCriticalFn φ ∧ IsInvariantTest G φ ∧ IsLevel P Θ₀ φ α ∧
    ∀ ψ, IsCriticalFn ψ → IsInvariantTest G ψ → IsLevel P Θ₀ ψ α →
      ∀ θ ∈ Θ₁, power P ψ θ ≤ power P φ θ

/-- Finite-group **orbit average** (symmetrization) of a test. -/
noncomputable def orbitAverage (G : Type*) [Group G] [Fintype G] [MulAction G 𝓧]
    (φ : 𝓧 → ℝ) (x : 𝓧) : ℝ :=
  (Fintype.card G : ℝ)⁻¹ * ∑ g : G, φ (g • x)

end StatLean.HypothesisTesting
