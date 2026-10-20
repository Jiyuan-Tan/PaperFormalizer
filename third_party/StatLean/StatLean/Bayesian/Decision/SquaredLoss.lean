module
public import StatLean.Bayesian.Decision.BayesEstimator
public import Mathlib.Probability.Kernel.MeasurableIntegral

@[expose] public section

/-!
# The posterior mean is the Bayes estimator under quadratic loss (Robert Proposition 2.5.1)

Under the quadratic loss `ℓ(θ, a) = (θ − a)²`, the posterior mean `x ↦ 𝔼[θ | x]` is a Bayes
estimator.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §2.5.1,
eq. (2.5.1) and Proposition 2.5.1, p. 77–78.

**Proof formalization notes.** No integrability hypothesis: we case-split on whether the posterior
`(P†π) x` has a finite second moment (`MemLp id 2`). If not, every action has infinite posterior
quadratic risk (`lintegral_sqLoss_eq_top`), so any value — including the junk `posteriorMean` — is
a pointwise minimizer; if so, the pointwise minimizer is the mean by the bias–variance inequality
(`variance_eq_integral` / `variance_sub_const` / `variance_le_expectation_sq`). The posterior is a
probability measure at every `x` (posterior Markov instance), so the split is pointwise and
`isBayesEstimator_of_ae_argmin` applies via `ae_of_all`. Bridge `‖·‖ₑ ^ 2` ↔ `(· )²` via
`Real.enorm_eq_ofReal_abs`, `ENNReal.ofReal_pow`, `sq_abs`. This subsumes Robert's "provided the
expectation exists" proviso.

**Bibliographic comments.** Quadratic loss is the founding loss function of statistics, going back
to the least-squares theory of A. M. Legendre (*Nouvelles méthodes pour la détermination des
orbites des comètes*, 1805) and C. F. Gauss (*Theoria motus corporum coelestium*, 1809); that the
posterior mean minimizes posterior quadratic loss was already implicit in Laplace's "probability
of causes" computations (1774). The bias–variance decomposition used in the proof is textbook
folklore.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]

/-- The quadratic loss is jointly measurable. -/
theorem measurable_uncurry_sqLoss : Measurable (Function.uncurry sqLoss) :=
  ((measurable_fst.sub measurable_snd).enorm).pow_const 2

/-- Pointwise bridge `‖θ − a‖ₑ ^ 2 = ENNReal.ofReal ((θ − a)²)`. -/
private theorem sqLoss_eq_ofReal (θ a : ℝ) : sqLoss θ a = ENNReal.ofReal ((θ - a) ^ 2) := by
  unfold sqLoss
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- If the measure has no finite second moment, every action has infinite posterior quadratic
risk. -/
theorem lintegral_sqLoss_eq_top (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    -- USER-INPUT: the measure lacks a finite second moment (this branch of the case split)
    (hρ : ¬ MemLp (id : ℝ → ℝ) 2 ρ) (a : ℝ) :
    ∫⁻ θ, sqLoss θ a ∂ρ = ∞ := by
  by_contra h
  refine hρ ?_
  rw [lintegral_congr (fun θ => sqLoss_eq_ofReal θ a)] at h
  have hnn : 0 ≤ᵐ[ρ] fun θ => (θ - a) ^ 2 := ae_of_all _ fun θ => sq_nonneg _
  have hmeas : Measurable fun θ : ℝ => (θ - a) ^ 2 := (measurable_id.sub_const a).pow_const 2
  have hfi : HasFiniteIntegral (fun θ => (θ - a) ^ 2) ρ :=
    (hasFiniteIntegral_iff_ofReal hnn).mpr (lt_top_iff_ne_top.mpr h)
  have hint : Integrable (fun θ => (θ - a) ^ 2) ρ := ⟨hmeas.aestronglyMeasurable, hfi⟩
  have hmemsub : MemLp (fun θ => θ - a) 2 ρ :=
    (memLp_two_iff_integrable_sq (measurable_id.sub_const a).aestronglyMeasurable).mpr hint
  have h2 := hmemsub.add (memLp_const (μ := ρ) a)
  have hcancel : ((fun θ : ℝ => θ - a) + fun _ => a) = id := by funext θ; simp
  rwa [hcancel] at h2

/-- With a finite second moment, the posterior quadratic risk is the real integral of `(θ − a)²`. -/
theorem lintegral_sqLoss_eq_ofReal_integral (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    -- USER-INPUT: the measure has a finite second moment (this branch of the case split)
    (hρ : MemLp (id : ℝ → ℝ) 2 ρ) (a : ℝ) :
    ∫⁻ θ, sqLoss θ a ∂ρ = ENNReal.ofReal (∫ θ, (θ - a) ^ 2 ∂ρ) := by
  have hint : Integrable (fun θ : ℝ => (θ - a) ^ 2) ρ := (hρ.sub (memLp_const a)).integrable_sq
  rw [lintegral_congr (fun θ => sqLoss_eq_ofReal θ a),
    ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun θ => sq_nonneg _)]

/-- Bias–variance inequality: the mean minimizes `a ↦ ∫ (θ − a)² dρ`. -/
theorem integral_sq_sub_integral_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    -- USER-INPUT: finite second moment (needed for the variance identity)
    (hρ : MemLp (id : ℝ → ℝ) 2 ρ) (a : ℝ) :
    ∫ θ, (θ - ∫ t, t ∂ρ) ^ 2 ∂ρ ≤ ∫ θ, (θ - a) ^ 2 ∂ρ := by
  have e1 : ∫ θ, (θ - ∫ t, t ∂ρ) ^ 2 ∂ρ = variance (id : ℝ → ℝ) ρ :=
    (variance_eq_integral aemeasurable_id).symm
  have e2 : variance (id : ℝ → ℝ) ρ = variance (fun θ => θ - a) ρ :=
    (variance_sub_const aestronglyMeasurable_id a).symm
  rw [e1, e2]
  refine (variance_le_expectation_sq (measurable_id.sub_const a).aestronglyMeasurable).trans_eq ?_
  simp [Pi.pow_apply]

/-- Pointwise minimizer: the mean minimizes the quadratic posterior risk (hypothesis-free, by the
`MemLp` case split). -/
theorem lintegral_sqLoss_integral_le (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (a : ℝ) :
    ∫⁻ θ, sqLoss θ (∫ t, t ∂ρ) ∂ρ ≤ ∫⁻ θ, sqLoss θ a ∂ρ := by
  by_cases h : MemLp (id : ℝ → ℝ) 2 ρ
  · rw [lintegral_sqLoss_eq_ofReal_integral ρ h, lintegral_sqLoss_eq_ofReal_integral ρ h]
    exact ENNReal.ofReal_le_ofReal (integral_sq_sub_integral_le ρ h a)
  · rw [lintegral_sqLoss_eq_top ρ h a]
    exact le_top

/-- The posterior mean is measurable. -/
theorem measurable_posteriorMean (P : Kernel ℝ 𝓧) [IsFiniteKernel P]
    (π : Measure ℝ) [IsFiniteMeasure π] :
    Measurable (posteriorMean P π) := by
  have hf : StronglyMeasurable (fun q : 𝓧 × ℝ => q.2) := measurable_snd.stronglyMeasurable
  exact (MeasureTheory.StronglyMeasurable.integral_kernel_prod_right' (κ := P†π) hf).measurable

/-- **The posterior mean is a Bayes estimator under quadratic loss** (Robert Proposition 2.5.1). -/
theorem posteriorMean_isBayesEstimator_sqLoss (P : Kernel ℝ 𝓧) [IsFiniteKernel P]
    (π : Measure ℝ) [IsFiniteMeasure π] :
    IsBayesEstimator sqLoss P
      (Kernel.deterministic (posteriorMean P π) (measurable_posteriorMean P π)) π := by
  refine isBayesEstimator_of_ae_argmin sqLoss measurable_uncurry_sqLoss P π
    (measurable_posteriorMean P π) ?_
  exact ae_of_all _ fun x y => lintegral_sqLoss_integral_le ((P†π) x) y

end StatLean.Bayesian
