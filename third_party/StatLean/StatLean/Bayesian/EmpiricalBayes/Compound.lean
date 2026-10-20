module
public import StatLean.Bayesian.EmpiricalBayes.Defs
public import StatLean.Bayesian.GeneralizedBayes.Basic

@[expose] public section

/-!
# Compound decision problems and the oracle Bayes rule

The decision-theoretic frame for nonparametric empirical Bayes: with a mixing distribution `G`, the
oracle posterior is the ordinary generalized posterior of the likelihood against `G`, and the
oracle Bayes rule — which minimizes the posterior expected loss pointwise — minimizes the
**compound risk** (the loss integrated over the data marginal). Empirical Bayes approximates this
oracle by estimating `G` (or the marginal) from data.

**Reference.** Not in Robert (Robert §10.4.1 is the closest). H. Robbins, "Asymptotically subminimax
solutions of compound statistical decision problems," *Proc. Second Berkeley Symp.* (1951), 131–148;
B. Efron, *Large-Scale Inference*, Cambridge University Press, 2010, §1.

**Proof formalization notes.** `mixtureDensity_eq_predictiveDensity` and
`npEB_oraclePosterior_eq_withDensity` are the definitional bridges to the Batch-1/2 dominated-Bayes
machinery (`predictiveDensity`, `generalizedPosterior_def`, `bayesDensity`);
`oracleBayesRule_minimizes_compoundRisk` is `lintegral_mono` applied to a pointwise
posterior-risk domination — the pointwise Bayes optimality of the oracle rule integrates to
compound optimality.

**Bibliographic comments.** The compound decision problem and its empirical-Bayes solution are
Robbins's (1951, 1956); the "oracle" terminology and the modern large-scale reading are Efron's
(2010). The equivalence of pointwise (posterior) and compound (frequentist, integrated) Bayes
optimality is the decision-theoretic content of Fubini's theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝓧]

/-- **Marginal density = predictive density** (3F.1): the empirical-Bayes mixture density is the
Bayesian predictive density (a definitional bridge). -/
theorem mixtureDensity_eq_predictiveDensity (p : Θ → 𝓧 → ℝ≥0∞) (G : Measure Θ) (x : 𝓧) :
    mixtureDensity p G x = predictiveDensity p G x := by
  rfl

/-- **Oracle posterior** (3F.2): the empirical-Bayes oracle posterior is the generalized posterior
of the likelihood against the mixing distribution (Robbins 1956). -/
theorem npEB_oraclePosterior_eq_withDensity (p : Θ → 𝓧 → ℝ≥0∞) (G : Measure Θ) (x : 𝓧) :
    generalizedPosterior p G x = G.withDensity (bayesDensity p G x) := by
  exact generalizedPosterior_def p G x

/-- **The oracle Bayes rule minimizes compound risk** (3F.3): a decision rule with pointwise
smaller posterior expected loss has smaller compound (marginal-integrated) risk (Robbins 1951). -/
theorem oracleBayesRule_minimizes_compoundRisk {ℓ : Θ → Θ → ℝ≥0∞} (p : Θ → 𝓧 → ℝ≥0∞)
    (G : Measure Θ) (m : Measure 𝓧) (d₀ d₁ : 𝓧 → Θ)
    -- USER-INPUT: the oracle rule dominates the competitor in posterior risk pointwise; Robbins 1951
    (hpoint : ∀ x, ∫⁻ θ, ℓ θ (d₀ x) ∂(generalizedPosterior p G x)
      ≤ ∫⁻ θ, ℓ θ (d₁ x) ∂(generalizedPosterior p G x)) :
    ∫⁻ x, (∫⁻ θ, ℓ θ (d₀ x) ∂(generalizedPosterior p G x)) ∂m
      ≤ ∫⁻ x, (∫⁻ θ, ℓ θ (d₁ x) ∂(generalizedPosterior p G x)) ∂m := by
  exact lintegral_mono hpoint

end StatLean.Bayesian
