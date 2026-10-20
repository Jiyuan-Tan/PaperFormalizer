module
public import StatLean.Bayesian.EmpiricalBayes.Defs

@[expose] public section

/-!
# The two-groups model and local false discovery rate

Efron's empirical-Bayes reading of large-scale testing: with a fraction `π₀` of null cases, the
marginal density is the mixture `f = π₀ f₀ + (1−π₀) f₁`, and the **local false discovery rate**
`fdr(x) = π₀ f₀(x) / f(x)` is exactly the posterior probability that a case with statistic `x` is
null. The Bayes decision rule rejects when the local FDR falls below a threshold.

**Reference.** Not in Robert. B. Efron, *Large-Scale Inference: Empirical Bayes Methods for
Estimation, Testing, and Prediction*, Cambridge University Press, 2010, §2.1 (two-groups model),
§5.1–5.2 (local FDR); the FDR framework is Y. Benjamini and Y. Hochberg (*J. Roy. Statist. Soc.
Ser. B* 57 (1995), 289–300).

**Proof formalization notes.** `twoGroupMarginalDensity_eq` and `localFDR_eq_posteriorNullProb`
are definitional unfoldings of `twoGroupsMixture`/`localFDR`; `localFDR_bayesRule_threshold` is
`ENNReal.div_le_iff` (with the nondegenerate-marginal side conditions), turning the threshold on
the ratio into a weighted-density comparison — the same posterior-odds thresholding as the Batch-2
`bayesTest` (`ModelChoice.Testing`).

**Bibliographic comments.** The two-groups model and local false discovery rate are B. Efron's
empirical-Bayes formulation (Efron, Tibshirani, Storey, Tusher, *J. Amer. Statist. Assoc.* 96
(2001), 1151–1160; Efron 2010); the local FDR as a posterior null probability is the Bayesian
reading of the Benjamini–Hochberg (1995) tail-area FDR, and connects large-scale testing to the
empirical-Bayes shrinkage of the rest of this directory.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **Two-groups marginal** (3G.1): `f(x) = π₀ f₀(x) + (1−π₀) f₁(x)` (Efron §2.1). -/
theorem twoGroupMarginalDensity_eq (π₀ : ℝ≥0∞) (f₀ f₁ : 𝓧 → ℝ≥0∞) (x : 𝓧) :
    twoGroupsMixture π₀ f₀ f₁ x = π₀ * f₀ x + (1 - π₀) * f₁ x := by
  rfl

/-- **Local FDR is the posterior null probability** (3G.2): `fdr(x) = π₀ f₀(x)/f(x)` is the
posterior probability of the null given `x` (Efron §5.1). -/
theorem localFDR_eq_posteriorNullProb (π₀ : ℝ≥0∞)
    -- USER-INPUT: the null proportion is a probability; Efron §2.1
    (hπ₀ : π₀ ≤ 1) (f₀ f₁ : 𝓧 → ℝ≥0∞) (x : 𝓧) :
    localFDR π₀ f₀ f₁ x = (π₀ * f₀ x) / (π₀ * f₀ x + (1 - π₀) * f₁ x) := by
  rfl

/-- **Local-FDR threshold rule** (3G.3): rejecting when `fdr(x) ≤ t` is the weighted-density
comparison `π₀ f₀(x) ≤ t·f(x)` — the Bayes decision rule (Efron §5.2). -/
theorem localFDR_bayesRule_threshold (π₀ : ℝ≥0∞) (f₀ f₁ : 𝓧 → ℝ≥0∞) (t : ℝ≥0∞) (x : 𝓧)
    -- USER-INPUT: nondegenerate marginal at `x`; Efron §5.2
    (hb0 : twoGroupsMixture π₀ f₀ f₁ x ≠ 0) (hbt : twoGroupsMixture π₀ f₀ f₁ x ≠ ∞) :
    localFDR π₀ f₀ f₁ x ≤ t ↔ π₀ * f₀ x ≤ t * twoGroupsMixture π₀ f₀ f₁ x := by
  rw [localFDR, ENNReal.div_le_iff hb0 hbt]

end StatLean.Bayesian
