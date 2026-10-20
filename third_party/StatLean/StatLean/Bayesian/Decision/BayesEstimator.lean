module
public import StatLean.Bayesian.Decision.Defs

@[expose] public section

/-!
# Bayes estimators via posterior-risk minimization (Robert Theorem 2.3.2)

Our own formalization of Robert's Theorem 2.3.2 and Definition 2.3.3: the integrated (average)
risk decomposes as an integral of the posterior expected loss over the predictive distribution,
$$r(\pi, \delta) = \int_{\mathcal X} \Big(\int_\Theta \ell(\theta, \delta(x))\,\pi(d\theta\mid x)\Big)\,m(dx),$$
so an estimator that minimizes the posterior expected loss pointwise (for predictive-a.e. `x`) is
a Bayes estimator.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §2.3, Theorem 2.3.2
and eq. (2.3.1) (integrated risk = integrated posterior expected loss), Definition 2.3.3 (Bayes
estimator), p. 62–63.

**Proof formalization notes.** This is proved *from the textbook* using only pinned Mathlib
primitives; it is not adapted from any external Lean development. The engine is the disintegration
`(P ∘ₘ π) ⊗ₘ (P†π) = (π ⊗ₘ P).map Prod.swap` (Mathlib's `compProd_posterior_eq_map_swap`), which is
exactly Robert's Fubini step (2.3.1):
`avgRisk ℓ P (deterministic δ) π = ∫⁻ (θ,x), ℓ θ (δ x) ∂(π ⊗ₘ P)` (by
`Measure.lintegral_compProd` and `Kernel.lintegral_deterministic'`), then pushed through
`Prod.swap` via `lintegral_map` to `∫⁻ x, ∫⁻ θ, ℓ θ (δ x) ∂(P†π) x ∂(P ∘ₘ π)`. The Bayes-risk
lower bound uses `iInf_le_lintegral` (needs `IsProbabilityMeasure ((P†π) x)`, from the posterior's
Markov instance); `isBayesEstimator_of_ae_argmin` closes by the `bayesRisk_le_avgRisk` sandwich.
No copied code; `IsBayesEstimator` is our own definition (`Decision.Defs`).

**Bibliographic comments.** The frequentist-risk framework in which Bayes rules are optimal
points is due to A. Wald, *Statistical Decision Functions* (Wiley, 1950); the subjectivist
justification of minimizing posterior expected loss is L. J. Savage, *The Foundations of
Statistics* (Wiley, 1954), with the axiomatic treatment developed further in M. H. DeGroot,
*Optimal Statistical Decisions* (McGraw-Hill, 1970). The reduction of the integrated risk to a
pointwise posterior minimization is the standard bridge between the two viewpoints and appears in
every decision-theoretic account since Wald.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 𝓨 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  [m𝓨 : MeasurableSpace 𝓨]

/-- **Robert Theorem 2.3.2 / eq. (2.3.1)** for a deterministic estimator `δ`: the integrated risk
equals the integral over the data of the posterior expected loss. -/
theorem avgRisk_deterministic_eq_lintegral_posteriorRisk [StandardBorelSpace Θ] [Nonempty Θ]
    (ℓ : Θ → 𝓨 → ℝ≥0∞)
    -- LEAN-ONLY: joint measurability of the loss (regularity)
    (hℓ : Measurable (Function.uncurry ℓ))
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π]
    -- LEAN-ONLY: the estimator `δ` is measurable (regularity of a free-choice input)
    {δ : 𝓧 → 𝓨} (hδ : Measurable δ) :
    avgRisk ℓ P (Kernel.deterministic δ hδ) π
      = ∫⁻ x, (∫⁻ θ, ℓ θ (δ x) ∂(P†π) x) ∂(P ∘ₘ π) := by
  have hℓθ : ∀ θ, Measurable (ℓ θ) := fun θ =>
    hℓ.comp (measurable_const.prodMk measurable_id)
  have hmeas1 : Measurable (fun p : Θ × 𝓧 => ℓ p.1 (δ p.2)) :=
    hℓ.comp (measurable_fst.prodMk (hδ.comp measurable_snd))
  have hmeas2 : Measurable (fun q : 𝓧 × Θ => ℓ q.2 (δ q.1)) :=
    hℓ.comp (measurable_snd.prodMk (hδ.comp measurable_fst))
  have inner : ∀ θ, ∫⁻ y, ℓ θ y ∂((Kernel.deterministic δ hδ ∘ₖ P) θ)
      = ∫⁻ x, ℓ θ (δ x) ∂(P θ) := by
    intro θ
    rw [Kernel.deterministic_comp_eq_map hδ, Kernel.lintegral_map P hδ θ (hℓθ θ)]
  have hswap : π ⊗ₘ P = ((P ∘ₘ π) ⊗ₘ (P†π)).map Prod.swap := by
    rw [compProd_posterior_eq_map_swap, Measure.map_map measurable_swap measurable_swap]
    simp
  calc avgRisk ℓ P (Kernel.deterministic δ hδ) π
      = ∫⁻ θ, ∫⁻ x, ℓ θ (δ x) ∂(P θ) ∂π := by rw [avgRisk]; simp_rw [inner]
    _ = ∫⁻ p, ℓ p.1 (δ p.2) ∂(π ⊗ₘ P) := (Measure.lintegral_compProd hmeas1).symm
    _ = ∫⁻ p, ℓ p.1 (δ p.2) ∂(((P ∘ₘ π) ⊗ₘ (P†π)).map Prod.swap) := by rw [hswap]
    _ = ∫⁻ q, ℓ (Prod.swap q).1 (δ (Prod.swap q).2) ∂((P ∘ₘ π) ⊗ₘ (P†π)) :=
          lintegral_map hmeas1 measurable_swap
    _ = ∫⁻ x, ∫⁻ θ, ℓ θ (δ x) ∂(P†π) x ∂(P ∘ₘ π) := Measure.lintegral_compProd hmeas2

/-- **General disintegration** (Robert eq. (2.3.1) for an arbitrary Markov estimator `κ`): the
integrated risk equals the integral over the data of the `κ`-averaged posterior expected loss.
Mirrors `avgRisk_deterministic_eq_lintegral_posteriorRisk` with a general kernel in place of the
deterministic one, and Tonelli's theorem to bring the posterior integral inside. -/
private theorem avgRisk_eq_lintegral_lintegral_posteriorRisk [StandardBorelSpace Θ] [Nonempty Θ]
    (ℓ : Θ → 𝓨 → ℝ≥0∞) (hℓ : Measurable (Function.uncurry ℓ))
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π]
    (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
    avgRisk ℓ P κ π
      = ∫⁻ x, ∫⁻ y, (∫⁻ θ, ℓ θ y ∂(P†π) x) ∂κ x ∂(P ∘ₘ π) := by
  have hℓθ : ∀ θ, Measurable (ℓ θ) := fun θ =>
    hℓ.comp (measurable_const.prodMk measurable_id)
  -- `G (θ, x) = ∫⁻ y, ℓ θ y ∂κ x`, measurable on `Θ × 𝓧`
  have hG : Measurable (fun p : Θ × 𝓧 => ∫⁻ y, ℓ p.1 y ∂κ p.2) := by
    have h := Measurable.lintegral_kernel_prod_right' (κ := κ.prodMkLeft Θ)
      (f := fun u : (Θ × 𝓧) × 𝓨 => ℓ u.1.1 u.2)
      (hℓ.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
    simpa only [Kernel.prodMkLeft_apply] using h
  -- `H (x, θ) = ∫⁻ y, ℓ θ y ∂κ x`, measurable on `𝓧 × Θ`
  have hH : Measurable (fun q : 𝓧 × Θ => ∫⁻ y, ℓ q.2 y ∂κ q.1) := by
    have h := Measurable.lintegral_kernel_prod_right' (κ := κ.prodMkRight Θ)
      (f := fun u : (𝓧 × Θ) × 𝓨 => ℓ u.1.2 u.2)
      (hℓ.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    simpa only [Kernel.prodMkRight_apply] using h
  have inner : ∀ θ, ∫⁻ y, ℓ θ y ∂((κ ∘ₖ P) θ)
      = ∫⁻ x, ∫⁻ y, ℓ θ y ∂κ x ∂(P θ) := fun θ => Kernel.lintegral_comp κ P θ (hℓθ θ)
  have hswap : π ⊗ₘ P = ((P ∘ₘ π) ⊗ₘ (P†π)).map Prod.swap := by
    rw [compProd_posterior_eq_map_swap, Measure.map_map measurable_swap measurable_swap]
    simp
  calc avgRisk ℓ P κ π
      = ∫⁻ θ, ∫⁻ x, (∫⁻ y, ℓ θ y ∂κ x) ∂(P θ) ∂π := by rw [avgRisk]; simp_rw [inner]
    _ = ∫⁻ p, (∫⁻ y, ℓ p.1 y ∂κ p.2) ∂(π ⊗ₘ P) := (Measure.lintegral_compProd hG).symm
    _ = ∫⁻ p, (∫⁻ y, ℓ p.1 y ∂κ p.2) ∂(((P ∘ₘ π) ⊗ₘ (P†π)).map Prod.swap) := by rw [hswap]
    _ = ∫⁻ q, (∫⁻ y, ℓ (Prod.swap q).1 y ∂κ (Prod.swap q).2) ∂((P ∘ₘ π) ⊗ₘ (P†π)) :=
          lintegral_map hG measurable_swap
    _ = ∫⁻ x, ∫⁻ θ, (∫⁻ y, ℓ θ y ∂κ x) ∂(P†π) x ∂(P ∘ₘ π) := Measure.lintegral_compProd hH
    _ = ∫⁻ x, ∫⁻ y, (∫⁻ θ, ℓ θ y ∂(P†π) x) ∂κ x ∂(P ∘ₘ π) :=
          lintegral_congr fun x => lintegral_lintegral_swap hℓ.aemeasurable

/-- The Bayes risk is bounded below by the integral of the pointwise-minimal posterior expected
loss (Robert Theorem 2.3.2, the "≥" half). -/
theorem lintegral_iInf_posteriorRisk_le_bayesRisk [StandardBorelSpace Θ] [Nonempty Θ]
    (ℓ : Θ → 𝓨 → ℝ≥0∞)
    -- LEAN-ONLY: joint measurability of the loss
    (hℓ : Measurable (Function.uncurry ℓ))
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π] :
    (∫⁻ x, ⨅ y, ∫⁻ θ, ℓ θ y ∂(P†π) x ∂(P ∘ₘ π)) ≤ bayesRisk ℓ P π := by
  rw [bayesRisk]
  refine le_iInf₂ fun κ hκ => ?_
  haveI := hκ
  rw [avgRisk_eq_lintegral_lintegral_posteriorRisk ℓ hℓ P π κ]
  refine lintegral_mono fun x => ?_
  exact iInf_le_lintegral _

/-- **Robert Theorem 2.3.2**: a deterministic estimator that minimizes the posterior expected loss
pointwise, for predictive-a.e. `x`, is a Bayes estimator. -/
theorem isBayesEstimator_of_ae_argmin [StandardBorelSpace Θ] [Nonempty Θ]
    (ℓ : Θ → 𝓨 → ℝ≥0∞)
    -- LEAN-ONLY: joint measurability of the loss
    (hℓ : Measurable (Function.uncurry ℓ))
    (P : Kernel Θ 𝓧) [IsFiniteKernel P] (π : Measure Θ) [IsFiniteMeasure π]
    -- LEAN-ONLY: the estimator `δ` is measurable
    {δ : 𝓧 → 𝓨} (hδ : Measurable δ)
    -- USER-INPUT: `δ(x)` minimizes the posterior expected loss for predictive-a.e. `x`;
    -- Robert Theorem 2.3.2
    (hmin : ∀ᵐ x ∂(P ∘ₘ π), ∀ y, ∫⁻ θ, ℓ θ (δ x) ∂(P†π) x ≤ ∫⁻ θ, ℓ θ y ∂(P†π) x) :
    IsBayesEstimator ℓ P (Kernel.deterministic δ hδ) π := by
  unfold IsBayesEstimator
  refine le_antisymm ?_ (bayesRisk_le_avgRisk ℓ P (Kernel.deterministic δ hδ) π)
  rw [avgRisk_deterministic_eq_lintegral_posteriorRisk ℓ hℓ P π hδ]
  refine le_trans (le_of_eq ?_) (lintegral_iInf_posteriorRisk_le_bayesRisk ℓ hℓ P π)
  refine lintegral_congr_ae ?_
  filter_upwards [hmin] with x hx
  exact le_antisymm (le_iInf fun y => hx y) (iInf_le _ (δ x))

end StatLean.Bayesian
