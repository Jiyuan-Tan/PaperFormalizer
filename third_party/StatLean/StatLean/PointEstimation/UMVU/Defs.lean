module
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-!
# Unbiased estimation — core data model

An estimator `δ : 𝓧 → ℝ` of an estimand `g : Θ → ℝ` is **unbiased** when
`E_θ δ = g(θ)` for every `θ`; among the square-integrable unbiased estimators, one is
**UMVU** (uniformly minimum variance unbiased) when it minimizes the variance at every
parameter simultaneously, and **LMVU at `θ₀`** when it does so at a single parameter.

* `IsUnbiased P g δ`;
* `IsUnbiasedZero P U` — the unbiased estimators of zero (the "𝒰" of the covariance
  characterization);
* `MemEstL2 P δ` — the estimator class `Δ`: square-integrable under every `P θ`;
* `IsUMVU P g δ`, `IsLMVU P g δ θ₀`.

**Reference.** E.L. Lehmann and G. Casella, *Theory of Point Estimation*, 2nd ed.,
Springer-Verlag New York, 1998 (ISBN 0-387-98502-6), Chapter 2 (Unbiasedness), §2.1 (UMVU
Estimators), Definition 1.1 (unbiased estimator) and Definition 1.6 (UMVU estimator). (`TPE2
§2.1 Def 1.1, Def 1.6`.)

**Proof formalization notes.**
* UMVU is variance-based (the covariance characterization is an `L²` statement); the
  stronger convex-loss risk minimality of the complete-sufficient-statistic estimator is
  stated separately in `UMVU.LehmannScheffe` via the area's `ℝ≥0∞` risk.
* Variance is Mathlib's `ProbabilityTheory.variance` (junk `∞ ↦ 0` never bites on the
  `MemEstL2` class, where second moments are finite by definition).

**Bibliographic comments.** Unbiasedness as a systematic requirement originates with
C. F. Gauss's theory of least squares (*Theoria combinationis observationum erroribus
minimis obnoxiae*, 1821/1823) and was refined by A. A. Markov; the modern minimum-
variance theory is due to C. R. Rao ("Information and the accuracy attainable in the
estimation of statistical parameters," *Bull. Calcutta Math. Soc.* **37** (1945),
81–91), D. Blackwell ("Conditional expectation and unbiased sequential estimation,"
*Ann. Math. Statist.* **18** (1947), 105–110), and E. L. Lehmann and H. Scheffé
("Completeness, similar regions, and unbiased estimation," *Sankhyā* **10** (1950),
305–340). The covariance characterization of minimum variance appears in E. L. Lehmann
and H. Scheffé (ibid.) and in C. R. Rao ("Sufficient statistics and minimum variance
estimates," *Proc. Camb. Phil. Soc.* **45** (1949), 213–218).
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.PointEstimation

variable {Θ 𝓧 : Type*} [MeasurableSpace 𝓧]

/-- `δ` is an **unbiased estimator** of `g`: `E_θ δ = g θ` for every `θ`. -/
def IsUnbiased (P : Θ → Measure 𝓧) (g : Θ → ℝ) (δ : 𝓧 → ℝ) : Prop :=
  ∀ θ, ∫ x, δ x ∂(P θ) = g θ

/-- `U` is an **unbiased estimator of zero**. -/
def IsUnbiasedZero (P : Θ → Measure 𝓧) (U : 𝓧 → ℝ) : Prop :=
  IsUnbiased P (fun _ => 0) U

/-- The estimator class `Δ`: square-integrable under every member of the model. -/
def MemEstL2 (P : Θ → Measure 𝓧) (δ : 𝓧 → ℝ) : Prop :=
  ∀ θ, MemLp δ 2 (P θ)

/-- **UMVU**: unbiased, square-integrable, and of minimal variance at every parameter
among all square-integrable unbiased estimators of the same estimand. -/
def IsUMVU (P : Θ → Measure 𝓧) (g : Θ → ℝ) (δ : 𝓧 → ℝ) : Prop :=
  IsUnbiased P g δ ∧ MemEstL2 P δ ∧
    ∀ δ', IsUnbiased P g δ' → MemEstL2 P δ' →
      ∀ θ, variance δ (P θ) ≤ variance δ' (P θ)

/-- **LMVU at `θ₀`** (locally minimum variance unbiased): minimal variance at the single
parameter `θ₀` among square-integrable unbiased estimators. -/
def IsLMVU (P : Θ → Measure 𝓧) (g : Θ → ℝ) (δ : 𝓧 → ℝ) (θ₀ : Θ) : Prop :=
  IsUnbiased P g δ ∧ MemEstL2 P δ ∧
    ∀ δ', IsUnbiased P g δ' → MemEstL2 P δ' →
      variance δ (P θ₀) ≤ variance δ' (P θ₀)

end StatLean.PointEstimation
