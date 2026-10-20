module
public import StatLean.Bayesian.Decision.Defs
public import StatLean.Bayesian.ForMathlib.KernelMixture

@[expose] public section

/-!
# The Bayesian route to minimaxity (Robert §2.4)

The decision-theoretic bridge between Bayes optimality and minimax optimality:

* **risk linearity for randomized estimators** (2G.1; Robert Theorem 2.4.2): the risk of a
  kernel mixture is the mixture of the risks;
* **Bayes + risk domination ⇒ minimax** (2G.2; Robert Lemma 2.4.13): a Bayes estimator whose
  risk never exceeds its Bayes risk is minimax — with constant risk as the classical special
  case (Robert Example 2.4.14);
* **the associated prior is least favorable** (2G.3; Robert Lemma 2.4.13's second half).

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §2.4.1, Theorem 2.4.2, p. 66; §2.4.2, Definition 2.4.3, p. 67;
§2.4.3, Lemma 2.4.10, p. 70 and **Lemma 2.4.13**, p. 71 (stated there with domination on the
support of `π₀`; we state the global-domination form, of which constant risk is the textbook
instance — the support-restricted refinement is a recorded stretch for the next batch).

**Proof formalization notes.** 2G.1 is `mixKernel_comp_left` + `lintegral_add_measure` +
`lintegral_smul_measure` (no measurability needed in `ℝ≥0∞`). 2G.2 is a three-step sandwich
from the pinned `bayesRisk_le_minimaxRisk` (needs `IsProbabilityMeasure π`) and
`iInf₂_le`-instantiation of `minimaxRisk` at `κ`; 2G.3 chains `bayesRisk_le_avgRisk` and the
pinned `avgRisk_le_iSup_risk` into the domination hypothesis. `IsBayesEstimator` is the Batch-1
definition; `risk`/`IsMinimaxEstimator`/`IsLeastFavorable` live in `Decision.Defs`.

**Bibliographic comments.** The Bayes-to-minimax route is A. Wald's (*Statistical Decision
Functions*, 1950), with the geometric risk-set picture of D. Blackwell and M. A. Girshick
(*Theory of Games and Statistical Decisions*, Wiley, 1954). The constant-risk criterion and least
favorable priors are the standard devices for exhibiting minimax estimators — e.g. the
`Beta(√n/2, √n/2)` binomial example. This file complements the
`StatLean.Minimaxity` area (Wainwright ch. 15), which bounds minimax risks from below; here Bayes
rules certify them from above.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 𝓨 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  [m𝓨 : MeasurableSpace 𝓨] {ℓ : Θ → 𝓨 → ℝ≥0∞} {P : Kernel Θ 𝓧}

/-- **Risk linearity for randomized estimators** (2G.1; Robert Theorem 2.4.2): the risk of a
kernel mixture is the mixture of the risks. -/
theorem risk_mixKernel (w : ℝ≥0∞) (κ₁ κ₂ : Kernel 𝓧 𝓨) (θ : Θ) :
    risk ℓ P (mixKernel w κ₁ κ₂) θ
      = w * risk ℓ P κ₁ θ + (1 - w) * risk ℓ P κ₂ θ := by
  unfold risk
  rw [mixKernel_comp_left, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    smul_eq_mul, smul_eq_mul]

/-- Average-risk linearity for randomized estimators (Robert Theorem 2.4.2). Unlike
`risk_mixKernel`, splitting the outer `∫⁻ · ∂π` in `ℝ≥0∞` genuinely needs the risk integrand
measurable: without `hℓ` the statement is false (inner-measure counterexample: a non-measurable
`A ⊆ Θ`, `𝓨 = Bool`, `κ₁ = δ_true`, `κ₂ = δ_false`, `ℓ θ true = 𝟙_A θ`, `ℓ θ false = 𝟙_{Aᶜ} θ`,
`w = ½` gives LHS `= ½·π(univ)` but RHS `= ½·(π_*(A) + π_*(Aᶜ)) < ½·π(univ)`). -/
theorem avgRisk_mixKernel
    -- LEAN-ONLY: s-finiteness feeds Measurable.lintegral_kernel_prod_right; Markov kernels have it
    [IsSFiniteKernel P] (w : ℝ≥0∞) (κ₁ κ₂ : Kernel 𝓧 𝓨)
    [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂] (π : Measure Θ)
    -- USER-INPUT: jointly measurable loss; Robert §2.4.1 (setting of Theorem 2.4.2)
    (hℓ : Measurable (Function.uncurry ℓ)) :
    avgRisk ℓ P (mixKernel w κ₁ κ₂) π
      = w * avgRisk ℓ P κ₁ π + (1 - w) * avgRisk ℓ P κ₂ π := by
  have h1 : Measurable fun θ => risk ℓ P κ₁ θ := by
    unfold risk; exact hℓ.lintegral_kernel_prod_right
  have h2 : Measurable fun θ => risk ℓ P κ₂ θ := by
    unfold risk; exact hℓ.lintegral_kernel_prod_right
  have key : ∀ κ : Kernel 𝓧 𝓨, avgRisk ℓ P κ π = ∫⁻ θ, risk ℓ P κ θ ∂π := fun _ => rfl
  rw [key, key, key]
  simp_rw [risk_mixKernel]
  rw [lintegral_add_left (h1.const_mul w), lintegral_const_mul w h1,
    lintegral_const_mul (1 - w) h2]

/-- **A Bayes estimator dominating its Bayes risk is minimax** (2G.2; Robert Lemma 2.4.13,
global-domination form — constant risk is the special case of Example 2.4.14). -/
theorem isMinimaxEstimator_of_isBayesEstimator_of_risk_le
    {κ : Kernel 𝓧 𝓨} [IsMarkovKernel κ] {π : Measure Θ} [IsProbabilityMeasure π]
    -- USER-INPUT: the estimator is Bayes for the prior π; Robert Lemma 2.4.13
    (hB : IsBayesEstimator ℓ P κ π)
    -- USER-INPUT: its risk never exceeds its Bayes risk; Robert Lemma 2.4.13
    (hle : ∀ θ, risk ℓ P κ θ ≤ bayesRisk ℓ P π) :
    IsMinimaxEstimator ℓ P κ := by
  unfold IsMinimaxEstimator
  refine le_antisymm ?_ ?_
  · exact (iSup_le hle).trans (bayesRisk_le_minimaxRisk ℓ P π)
  · exact iInf₂_le κ ‹IsMarkovKernel κ›

/-- **The prior of a risk-dominating Bayes estimator is least favorable** (2G.3; Robert
Lemma 2.4.13). -/
theorem isLeastFavorable_of_isBayesEstimator_of_risk_le
    {κ : Kernel 𝓧 𝓨} [IsMarkovKernel κ] {π : Measure Θ} [IsProbabilityMeasure π]
    -- USER-INPUT: the estimator is Bayes for the prior π; Robert Lemma 2.4.13
    (hB : IsBayesEstimator ℓ P κ π)
    -- USER-INPUT: its risk never exceeds its Bayes risk; Robert Lemma 2.4.13
    (hle : ∀ θ, risk ℓ P κ θ ≤ bayesRisk ℓ P π) :
    IsLeastFavorable ℓ P π := by
  refine ⟨‹IsProbabilityMeasure π›, fun π' hπ' => ?_⟩
  haveI := hπ'
  calc bayesRisk ℓ P π' ≤ avgRisk ℓ P κ π' := bayesRisk_le_avgRisk ℓ P κ π'
    _ ≤ ⨆ θ, risk ℓ P κ θ := avgRisk_le_iSup_risk ℓ P κ π'
    _ ≤ bayesRisk ℓ P π := iSup_le hle

/-- **A constant-risk Bayes estimator is minimax** (Robert Example 2.4.14's principle). -/
theorem isMinimaxEstimator_of_isBayesEstimator_of_risk_const
    {κ : Kernel 𝓧 𝓨} [IsMarkovKernel κ] {π : Measure Θ} [IsProbabilityMeasure π]
    -- USER-INPUT: the estimator is Bayes for the prior π; Robert Lemma 2.4.13
    (hB : IsBayesEstimator ℓ P κ π)
    -- USER-INPUT: the estimator has constant risk; Robert Example 2.4.14
    (hconst : ∀ θ θ', risk ℓ P κ θ = risk ℓ P κ θ') :
    IsMinimaxEstimator ℓ P κ := by
  refine isMinimaxEstimator_of_isBayesEstimator_of_risk_le hB (fun θ => ?_)
  have hconstθ : ∀ θ', risk ℓ P κ θ' = risk ℓ P κ θ := fun θ' => hconst θ' θ
  have havg : avgRisk ℓ P κ π = risk ℓ P κ θ := by
    unfold avgRisk
    refine (lintegral_congr fun θ' => hconstθ θ').trans ?_
    rw [lintegral_const, measure_univ, mul_one]
  exact (havg.symm.trans hB).le

end StatLean.Bayesian
