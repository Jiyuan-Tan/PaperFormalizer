module
public import StatLean.AsymptoticStatistics.ParametricFamily.Defs
public import Mathlib.Probability.Kernel.Basic

@[expose] public section

/-!
# Statistical models and risk — core data model for point estimation

Carrier conventions for the point-estimation area:

* a **statistical model** is a plain family of probability measures `P : Θ → Measure 𝓧`
  (no measurability in `θ` is ever assumed — kernels enter through their coercion);
* `Identifiable P` — distinct parameters give distinct distributions;
* `ParametricFamily.toMeasure M μ θ` — the measure `μ.withDensity (p_θ)` of a dominated
  model, connecting the density-based `ParametricFamily` carrier to measure families;
* `crossRisk P L δ θ θ'` — the expected loss `∫⁻ L θ' (δ x) ∂P θ` of estimating `θ'`'s
  value when data are generated under `θ` (the two-parameter form needed for
  risk-unbiasedness);
* `risk P L δ θ` — the risk function `R(θ, δ) = E_θ L(θ, δ(X))`;
* `riskRand P L κ θ` — the risk of a **randomized** estimator, a Markov kernel
  `κ : 𝓧 ⇝ D`.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 1 (Preparations), §1.1 (The
Problem), the decision-theoretic framework (model, estimand, loss and risk). (`TPE2 §1.1`.)

**Proof formalization notes.**
* Risks are `ℝ≥0∞`-valued lower Lebesgue integrals (junk-value discipline): a
  non-integrable loss records the genuine value `∞` rather than the Bochner junk `0`,
  so risk inequalities carry real content. Real-valued convex losses enter individual
  theorems through `ENNReal.ofReal`.
* `riskRand` is compatible with the kernel-composition risk shape: for `K : Kernel Θ 𝓧`
  one has `riskRand ⇑K L κ θ = ∫⁻ d, L θ d ∂((κ ∘ₖ K) θ)` (proved where used).
* We deliberately do not bundle `IsProbabilityMeasure` into a structure; it is carried
  as an instance argument `[∀ θ, IsProbabilityMeasure (P θ)]` by consumers, keeping the
  carrier a bare function.

**Bibliographic comments.** The decision-theoretic framing of estimation — loss, risk,
and comparison of estimators by their risk functions — is due to A. Wald (*Statistical
Decision Functions*, Wiley, 1950). Identifiability as a property of the parametrization
is classical folklore; see E. L. Lehmann, "A general concept of unbiasedness," *Ann.
Math. Statist.* **22** (1951), 587–592 for the risk-based comparisons this file feeds.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.PointEstimation

variable {Θ 𝓧 D : Type*} [MeasurableSpace 𝓧] [MeasurableSpace D]

/-- **Identifiability**: distinct parameter values index distinct distributions. Its
negation (two parameters with `P θ₁ = P θ₂`) is unidentifiability. -/
def Identifiable (P : Θ → Measure 𝓧) : Prop :=
  Function.Injective P

/-- The measure family of a dominated model: `θ ↦ μ.withDensity p_θ`. -/
noncomputable def _root_.AsymptoticStatistics.ParametricFamily.toMeasure
    (M : AsymptoticStatistics.ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) (θ : Θ) :
    Measure 𝓧 :=
  μ.withDensity fun x => ENNReal.ofReal (M.density θ x)

/-- **Cross risk** `∫⁻ L θ' (δ x) ∂P θ`: expected loss against the parameter value `θ'`
when the data follow `P θ`. The diagonal `θ' = θ` is the risk function; the off-diagonal
values appear in risk-unbiasedness. -/
noncomputable def crossRisk (P : Θ → Measure 𝓧) (L : Θ → D → ℝ≥0∞) (δ : 𝓧 → D)
    (θ θ' : Θ) : ℝ≥0∞ :=
  ∫⁻ x, L θ' (δ x) ∂(P θ)

/-- **Risk function** `R(θ, δ) = E_θ L(θ, δ(X))` of a (nonrandomized) estimator. -/
noncomputable def risk (P : Θ → Measure 𝓧) (L : Θ → D → ℝ≥0∞) (δ : 𝓧 → D) (θ : Θ) :
    ℝ≥0∞ :=
  crossRisk P L δ θ θ

/-- **Risk of a randomized estimator** `κ : 𝓧 ⇝ D`: first draw `x ~ P θ`, then a
decision `d ~ κ x`, and average the loss. -/
noncomputable def riskRand (P : Θ → Measure 𝓧) (L : Θ → D → ℝ≥0∞) (κ : Kernel 𝓧 D)
    (θ : Θ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ d, L θ d ∂(κ x) ∂(P θ)

end StatLean.PointEstimation
