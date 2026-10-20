module
public import Mathlib.Probability.Decision.Risk.Basic
public import Mathlib.Probability.Kernel.Posterior
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# Bayes decision theory — core data model (Bayes estimator, posterior risk, canonical losses)

Data model for the decision-theoretic layer, built on Mathlib's risk framework
(`ProbabilityTheory.avgRisk` / `bayesRisk`, where an estimation problem is a data kernel
`P : Kernel Θ 𝓧` with loss `ℓ : Θ → 𝓨 → ℝ≥0∞` and an estimator is a Markov kernel
`Kernel 𝓧 𝓨`). This file fixes:

* `IsBayesEstimator` — an estimator attains the Bayes risk (Robert Definition 2.3.3);
* `posteriorRisk` — the posterior expected loss `ρ(π, y | x) = ∫ ℓ(θ, y) π(dθ|x)`
  (Robert §2.3);
* `sqLoss` / `zeroOneLoss` — the quadratic loss `(θ − a)²` (Robert eq. (2.5.1)) and the 0–1 loss
  `𝟙[θ ≠ a]` (Robert §2.5.3 / §4.1.2), the two canonical losses;
* `posteriorMean` / `posteriorMode` — the resulting Bayes actions (Robert Prop. 2.5.1 and
  §4.1.2), plus the choice-free finite argmax `fintypeArgmax` used to define the mode.

The theorems that these are Bayes estimators live in `StatLean.Bayesian.Decision.SquaredLoss`
and `.ZeroOneLoss`; the general "pointwise posterior-risk minimizer ⇒ Bayes" engine is in
`.BayesEstimator`.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §2.3, Theorem 2.3.2
and Definition 2.3.3 (Bayes estimator, integrated risk `r(π,δ)`, posterior expected loss
`ρ(π,d|x)`), p. 62–63; §2.5.1, eq. (2.5.1) and Proposition 2.5.1 (quadratic loss → posterior
mean), p. 77–78; §2.5.3, eq. (2.5.5), and §4.1.2 (MAP estimator, 0–1 loss → posterior mode),
p. 81 and p. 166.

**Proof formalization notes.** Laptop-only data model — definitions only. Terminology bridge:
Robert's *integrated risk* `r(π,δ)` is Mathlib's `avgRisk`, and Robert's *Bayes risk* `r(π)` is
Mathlib's `bayesRisk`; `IsBayesEstimator ℓ P κ π := avgRisk ℓ P κ π = bayesRisk ℓ P π` is our own
formalization of Robert Definition 2.3.3, not taken from any external Lean source. Design choices:
`sqLoss θ a = ‖θ − a‖ₑ ^ 2` matches the integrand of Mathlib's `evariance`, so the variance API
applies directly. `fintypeArgmax` selects, among the maximizers of a finite family of `ℝ≥0∞`
values, the one least in the canonical `Fintype.equivFin` enumeration — a *choice-free*
(deterministic) selection, so that estimators built from it are measurable (an `Exists.choose`
mode would not be). `zeroOneLoss`/`fintypeArgmax`/`posteriorMode` are `noncomputable` and use
classical decidability. Junk behavior: `posteriorMean` is the Bochner integral, which is `0` when
the posterior has no first moment (harmless — then every action has infinite posterior quadratic
risk).

**Bibliographic comments.** The reduction of Bayesian estimation to per-observation minimization
of posterior expected loss is classical decision theory (A. Wald, *Statistical Decision
Functions*, Wiley, 1950; L. J. Savage, *The Foundations of Statistics*, Wiley, 1954). The
posterior-mean/median/mode correspondence with quadratic/absolute/0–1 loss is standard.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

/-! ### Bayes estimator and posterior risk -/

variable {Θ 𝓧 𝓨 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  [m𝓨 : MeasurableSpace 𝓨]

/-- An estimator `κ` is a **Bayes estimator** for the prior `π` if it attains the Bayes risk:
`avgRisk ℓ P κ π = bayesRisk ℓ P π` (Robert Definition 2.3.3; Robert's *integrated risk* is
Mathlib's `avgRisk`, his *Bayes risk* is Mathlib's `bayesRisk`). -/
def IsBayesEstimator (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨)
    (π : Measure Θ) : Prop :=
  avgRisk ℓ P κ π = bayesRisk ℓ P π

/-- The **posterior expected loss** `ρ(π, y | x) = ∫ ℓ(θ, y) π(dθ|x)` of action `y` given data
`x` (Robert §2.3, eq. (2.3.1) context). -/
noncomputable def posteriorRisk [StandardBorelSpace Θ] [Nonempty Θ]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) [IsFiniteKernel P]
    (π : Measure Θ) [IsFiniteMeasure π] (y : 𝓨) (x : 𝓧) : ℝ≥0∞ :=
  ∫⁻ θ, ℓ θ y ∂(P†π) x

/-! ### Quadratic loss and the posterior mean (Robert §2.5.1) -/

/-- The **quadratic (squared-error) loss** `ℓ(θ, a) = (θ − a)²` on `ℝ`, valued in `ℝ≥0∞` as
`‖θ − a‖ₑ ^ 2` (Robert eq. (2.5.1)). The `‖·‖ₑ ^ 2` form matches the integrand of Mathlib's
`evariance`. -/
noncomputable def sqLoss : ℝ → ℝ → ℝ≥0∞ := fun θ a => ‖θ - a‖ₑ ^ 2

/-- The **posterior mean** `x ↦ ∫ θ π(dθ|x)`, the Bayes action under quadratic loss
(Robert Proposition 2.5.1). Bochner integral; `0` when the posterior lacks a first moment. -/
noncomputable def posteriorMean (P : Kernel ℝ 𝓧) [IsFiniteKernel P]
    (π : Measure ℝ) [IsFiniteMeasure π] : 𝓧 → ℝ :=
  fun x => ∫ θ, θ ∂(P†π) x

/-! ### Zero–one loss and the posterior mode (Robert §2.5.3 / §4.1.2) -/

open Classical in
/-- The **0–1 loss** `ℓ(θ, a) = 𝟙[θ ≠ a]` on an arbitrary type (Robert §2.5.3, eq. (2.5.5), and
§4.1.2). Generalizes `StatLean.Minimaxity.zeroOneLoss`, which is specialized to `Fin M`. -/
noncomputable def zeroOneLoss {α : Type*} : α → α → ℝ≥0∞ := fun θ a => if θ = a then 0 else 1

open Classical in
/-- **Choice-free finite argmax.** Among the maximizers of `g : α → ℝ≥0∞` over a nonempty finite
type, returns the one least in the canonical `Fintype.equivFin` enumeration. Being a deterministic
function of `g` (no `Exists.choose`), selections built from it are measurable. -/
noncomputable def fintypeArgmax {α : Type*} [Fintype α] [Nonempty α] (g : α → ℝ≥0∞) : α :=
  (Fintype.equivFin α).symm
    (((Finset.univ.filter fun a => ∀ b, g b ≤ g a).image (Fintype.equivFin α)).min' (by
      obtain ⟨a, -, ha⟩ := Finset.exists_max_image Finset.univ g Finset.univ_nonempty
      exact ⟨_, Finset.mem_image_of_mem _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ a, fun b => ha b (Finset.mem_univ b)⟩)⟩))

/-- The **posterior mode (MAP)** `x ↦ argmax_a π({a} | x)`, the Bayes action under 0–1 loss on a
finite parameter space (Robert §4.1.2, p. 166; §2.5.3, Proposition 2.5.7). Uses the choice-free
`fintypeArgmax`. -/
noncomputable def posteriorMode [Fintype Θ] [Nonempty Θ] [DiscreteMeasurableSpace Θ]
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] : 𝓧 → Θ :=
  fun x => fintypeArgmax fun a => (P†π) x {a}

/-! ### Frequentist risk, minimaxity, and least favorable priors (Robert §2.4) -/

/-- The **frequentist risk** `R(θ, κ) = ∫ ℓ(θ, y) d((κ ∘ₖ P) θ)(y)` of the (randomized) estimator
`κ` at parameter `θ` (Robert §2.3, prose display p. 61). Definitionally the integrand of the
pinned `avgRisk`/`minimaxRisk`, so `minimaxRisk ℓ P = ⨅ κ (Markov), ⨆ θ, risk ℓ P κ θ`
holds by `rfl`. -/
noncomputable def risk (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) (θ : Θ) : ℝ≥0∞ :=
  ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)

/-- A (Markov) estimator is **minimax** if its worst-case risk attains the minimax risk
(Robert Definition 2.4.3, p. 67). -/
def IsMinimaxEstimator (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (κ : Kernel 𝓧 𝓨) : Prop :=
  ⨆ θ, risk ℓ P κ θ = minimaxRisk ℓ P

/-- A prior is **least favorable** if it is a probability measure maximizing the Bayes risk over
all probability priors (Robert §2.4.3, after Lemma 2.4.10, p. 70). -/
def IsLeastFavorable (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (π : Measure Θ) : Prop :=
  IsProbabilityMeasure π ∧
    ∀ π' : Measure Θ, IsProbabilityMeasure π' → bayesRisk ℓ P π' ≤ bayesRisk ℓ P π

end StatLean.Bayesian
