module
public import StatLean.Bayesian.EmpiricalBayes.Defs
public import StatLean.Bayesian.Conjugacy.NormalNormal

@[expose] public section

/-!
# Parametric empirical Bayes — the normal random-effects model

Parametric empirical Bayes estimates the hyperparameters `(μ, τ²)` from the marginal likelihood and
plugs them into the Bayes rule. For the normal random-effects model `Yⱼ ∣ θⱼ ∼ N(θⱼ, σ²)`,
`θⱼ ∼ N(μ, τ²)`, the marginal is `Yⱼ ∼ N(μ, σ²+τ²)`, so the method-of-moments estimators
`μ̂ = ȳ`, `τ̂² = max(0, s² − σ²)` are consistent, and the empirical-Bayes shrinkage weight converges
to the oracle weight. Fisher's identity and the EM monotonicity underpin the general marginal-MLE
computation.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §10.4.2 (parametric empirical Bayes), p. 481; §10.5.1 (the normal
case), p. 485.

**Proof formalization notes.** `normalRandomEffects_marginal` is `comp_gaussKernel_gaussianReal`
(the Batch-2 Gaussian convolution). Consistency is cut to the method-of-moments estimator (per the
plan): `normalParamEB_shrinkageWeight_tendsto_oracle` is a continuous-mapping limit of the plug-in
weight given a consistent sample variance (which `strong_law_ae_real` supplies); the general-family
consistency is deferred to Batch 4. `fisherIdentity_normalMarginal` is the concrete score identity
`(y−μ)/(σ²+τ²) = (1−B)(y−μ)/τ²` (marginal score = shrinkage × complete-data score);
`EM_monotonicity_marginalLikelihood` is the abstract `ℓ = Q − R` decomposition with the M-step
ascent and Gibbs' inequality (`linarith`).

**Bibliographic comments.** Parametric empirical Bayes is H. Robbins (1956) made parametric by
M. C. K. Tweedie and by C. Stein; the normal random-effects analysis is B. Efron and C. Morris
(1972–1973). Fisher's identity is R. A. Fisher's (1925) missing-information formula; the EM
algorithm and its monotonicity are A. P. Dempster, N. M. Laird, and D. B. Rubin ("Maximum
likelihood from incomplete data via the EM algorithm," *J. Roy. Statist. Soc. Ser. B* 39 (1977),
1–38), with the marginal-likelihood ascent guaranteeing convergence to a stationary point.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

namespace StatLean.Bayesian

/-- The **sample mean** `ȳ = (∑ⱼ yⱼ)/J`. -/
noncomputable def sampleMean {J : ℕ} (y : Fin J → ℝ) : ℝ := (∑ i, y i) / (J : ℝ)

/-- The **sample variance** `s² = (∑ⱼ (yⱼ − ȳ)²)/J`. -/
noncomputable def sampleVar {J : ℕ} (y : Fin J → ℝ) : ℝ :=
  (∑ i, (y i - sampleMean y) ^ 2) / (J : ℝ)

/-- The **method-of-moments hyper-variance estimate** `τ̂² = max(0, s² − σ²)` (Robert §10.5.1). -/
noncomputable def normalEBhyperVar {J : ℕ} (y : Fin J → ℝ) (σ2 : ℝ) : ℝ :=
  max 0 (sampleVar y - σ2)

/-- The **parametric empirical-Bayes estimator** of `θⱼ`: shrink `yⱼ` toward `ȳ` with the plug-in
weight `τ̂²/(τ̂²+σ²)` (Robert §10.5.1). -/
noncomputable def normalParamEBEstimator {J : ℕ} (y : Fin J → ℝ) (σ2 : ℝ) (j : Fin J) : ℝ :=
  sampleMean y
    + (normalEBhyperVar y σ2 / (normalEBhyperVar y σ2 + σ2)) * (y j - sampleMean y)

/-- **The random-effects marginal** (3E.6): integrating out the group mean, `Y ∼ N(μ, σ²+τ²)`
(Robert §10.5.1). -/
theorem normalRandomEffects_marginal (μ : ℝ) (τ2 σ2 : ℝ≥0)
    -- USER-INPUT: nondegenerate noise variance; Robert §10.5.1
    (hσ : σ2 ≠ 0) :
    gaussKernel σ2 ∘ₘ gaussianReal μ τ2 = gaussianReal μ (τ2 + σ2) := by
  exact comp_gaussKernel_gaussianReal hσ μ τ2

/-- **The parametric-EB estimator formula** (3E.7): the plug-in shrinkage form (Robert §10.5.1). -/
theorem normalParamEB_estimator_formula {J : ℕ} (y : Fin J → ℝ) (σ2 : ℝ) (j : Fin J) :
    normalParamEBEstimator y σ2 j
      = sampleMean y
        + (normalEBhyperVar y σ2 / (normalEBhyperVar y σ2 + σ2)) * (y j - sampleMean y) := by
  rfl

/-- **Consistency of the plug-in shrinkage weight** (3E.4/3E.5, normal method-of-moments): if the
sample variance is consistent for `σ²+τ²`, the empirical-Bayes weight converges to the oracle
weight `τ²/(σ²+τ²)` (Robert §10.4.2). -/
theorem normalParamEB_shrinkageWeight_tendsto_oracle (τ2 σ2 : ℝ)
    -- USER-INPUT: nondegenerate variances; Robert §10.4.2
    (hσ : 0 < σ2) (hτ : 0 < τ2) (vn : ℕ → ℝ)
    -- USER-INPUT: the sample variance is consistent for the marginal variance (SLLN); Robert §10.4.2
    (hv : Tendsto vn atTop (𝓝 (τ2 + σ2))) :
    Tendsto (fun n => max 0 (vn n - σ2) / (max 0 (vn n - σ2) + σ2)) atTop
      (𝓝 (τ2 / (τ2 + σ2))) := by
  have hcont : ContinuousAt
      (fun t : ℝ => max 0 (t - σ2) / (max 0 (t - σ2) + σ2)) (τ2 + σ2) := by
    have hnum : ContinuousAt (fun t : ℝ => max 0 (t - σ2)) (τ2 + σ2) :=
      (continuous_const.max (continuous_id.sub continuous_const)).continuousAt
    have hden : ContinuousAt (fun t : ℝ => max 0 (t - σ2) + σ2) (τ2 + σ2) :=
      hnum.add continuousAt_const
    have hne : (fun t : ℝ => max 0 (t - σ2) + σ2) (τ2 + σ2) ≠ 0 := by
      have : max 0 (τ2 + σ2 - σ2) + σ2 = τ2 + σ2 := by
        rw [add_sub_cancel_right, max_eq_right hτ.le]
      simp only [this]; positivity
    exact hnum.div hden hne
  have key : (fun t : ℝ => max 0 (t - σ2) / (max 0 (t - σ2) + σ2)) (τ2 + σ2)
      = τ2 / (τ2 + σ2) := by
    simp only [add_sub_cancel_right, max_eq_right hτ.le]
  rw [← key]
  exact hcont.tendsto.comp hv

/-- **Fisher's identity for the normal marginal** (3E.8): the marginal score equals the shrinkage
factor times the complete-data score, `(y−μ)/(σ²+τ²) = (1−B)·(y−μ)/τ²` (Robert §10.4.2). -/
theorem fisherIdentity_normalMarginal (μ τ2 σ2 : ℝ)
    -- USER-INPUT: nondegenerate variances; Robert §10.4.2
    (hτ : 0 < τ2) (hσ : 0 < σ2) (y : ℝ) :
    (y - μ) / (σ2 + τ2) = (1 - σ2 / (σ2 + τ2)) * ((y - μ) / τ2) := by
  have h1 : σ2 + τ2 ≠ 0 := by positivity
  have h2 : τ2 ≠ 0 := hτ.ne'
  field_simp
  ring

/-- **EM monotonicity** (3E.9, stretch): with the decomposition `ℓ = Q − R`, an M-step that
increases `Q` together with Gibbs' inequality on `R` does not decrease the marginal log-likelihood
(Dempster–Laird–Rubin 1977). -/
theorem EM_monotonicity_marginalLikelihood (marginalLogLik : ℝ → ℝ) (Q R : ℝ → ℝ → ℝ) (θ₀ θ₁ : ℝ)
    -- USER-INPUT: the EM decomposition ℓ(θ) = Q(θ|θ₀) − R(θ|θ₀); Dempster–Laird–Rubin 1977
    (hdecomp : ∀ θ, marginalLogLik θ = Q θ θ₀ - R θ θ₀)
    -- USER-INPUT: the M-step increases the expected complete log-likelihood; DLR 1977
    (hM : Q θ₀ θ₀ ≤ Q θ₁ θ₀)
    -- USER-INPUT: Gibbs' inequality on the entropy term; DLR 1977
    (hGibbs : R θ₁ θ₀ ≤ R θ₀ θ₀) :
    marginalLogLik θ₀ ≤ marginalLogLik θ₁ := by
  rw [hdecomp θ₀, hdecomp θ₁]
  linarith [hM, hGibbs]

end StatLean.Bayesian
