module
public import StatLean.Bayesian.GeneralizedBayes.Defs
public import StatLean.Bayesian.Dominated.PosteriorDensity
public import StatLean.Bayesian.ModelChoice.Defs

@[expose] public section

/-!
# Generalized Bayes: propriety, scale invariance, and Bayes-factor scaling

The safe core of improper-prior Bayesian inference:

* **propriety** — the generalized posterior is a probability measure whenever the pseudo-marginal
  `m(x) = ∫ p(θ, x) π(dθ)` is positive and finite;
* **scale invariance** — rescaling the prior by `c ∈ (0, ∞)` does not change the posterior
  (why improper priors are usable "up to an arbitrary constant");
* **marginal scaling** — the pseudo-marginal scales linearly, `m_{cπ}(x) = c·m_π(x)`;
* **Bayes-factor scaling** — consequently the Bayes factor of model `0` against model `1` is
  multiplied by `c` when `π₀` is rescaled: improper priors are safe for estimation but
  **meaningless for Bayes factors**;
* the **bridge**: on probability priors, the generalized posterior agrees predictive-a.e. with the
  abstract posterior `κ†π`.

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.5, pp. 26–30 (improper priors; the generalized posterior
display, p. 28; propriety `∫ f(x|θ)π(θ)dθ < ∞`, p. 30; the "important exception" for testing,
pp. 28–29 pointing to Chapter 5).

**Proof formalization notes.** Propriety: `generalizedPosterior` has total mass `m(x)/m(x)`;
positivity and finiteness of `m(x)` are genuine USER-INPUTs here (for σ-finite priors they are NOT
forced by the setup — that is the entire subtlety of improper priors, in contrast with the
probability-prior facts `predictiveDensity_pos_ae`/`_lt_top_ae_comp`). Scaling:
`withDensity_smul_measure` + `lintegral_smul_measure` + `ℝ≥0∞` division algebra. The bridge is a
restatement of the Batch-1 headline `posterior_eq_withDensity_likelihood_div_predictive`.

**Bibliographic comments.** The scale-invariance of generalized posteriors and the resulting
indeterminacy of Bayes factors under improper priors were emphasized by H. Jeffreys (1939) and are
the reason for pseudo-Bayes-factor proposals (intrinsic and fractional Bayes factors: J. O. Berger
and L. R. Pericchi, *J. Amer. Statist. Assoc.* 91 (1996), 109–122; A. O'Hagan, *J. Roy. Statist.
Soc. B* 57 (1995), 99–138). The marginalization
paradoxes of Dawid, Stone and Zidek (*J. Roy. Statist. Soc. B* 35 (1973), 189–233) delimit the
safe zone formalized here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ Θ₀' Θ₁' 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  [mΘ₀' : MeasurableSpace Θ₀'] [mΘ₁' : MeasurableSpace Θ₁']

/-- **Posterior propriety** (Robert §1.5, p. 30): if the pseudo-marginal is positive and finite at
`x`, the generalized posterior is a probability measure. -/
theorem isProbabilityMeasure_generalizedPosterior {p : Θ → 𝓧 → ℝ≥0∞} {π : Measure Θ} {x : 𝓧}
    -- LEAN-ONLY: the likelihood section at `x` is measurable (regularity)
    (hpx : Measurable fun θ => p θ x)
    -- USER-INPUT: posterior propriety, 0 < ∫ p(θ,x) π(dθ) < ∞; Robert §1.5, p. 30
    (h0 : predictiveDensity p π x ≠ 0) (h1 : predictiveDensity p π x ≠ ∞) :
    IsProbabilityMeasure (generalizedPosterior p π x) := by
  refine ⟨?_⟩
  rw [generalizedPosterior_def, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  simp only [bayesDensity, div_eq_mul_inv]
  rw [lintegral_mul_const'' _ hpx.aemeasurable]
  exact ENNReal.mul_inv_cancel h0 h1

/-- **Scale invariance of the generalized posterior** (Robert §1.5, p. 28): rescaling the prior by
`c ∈ (0, ∞)` leaves the posterior unchanged. -/
theorem generalizedPosterior_smul_prior {p : Θ → 𝓧 → ℝ≥0∞} {π : Measure Θ} {x : 𝓧} {c : ℝ≥0∞}
    -- USER-INPUT: nondegenerate rescaling constant; Robert §1.5
    (hc0 : c ≠ 0) (hc1 : c ≠ ∞) :
    generalizedPosterior p (c • π) x = generalizedPosterior p π x := by
  have hbd : bayesDensity p (c • π) x = c⁻¹ • bayesDensity p π x := by
    funext θ
    have hps : predictiveDensity p (c • π) x = c * predictiveDensity p π x := by
      simp only [predictiveDensity, lintegral_smul_measure, smul_eq_mul]
    simp only [bayesDensity, Pi.smul_apply, smul_eq_mul]
    rw [hps, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc0) (Or.inl hc1)]
    ring
  rw [generalizedPosterior_def, generalizedPosterior_def, hbd, withDensity_smul_measure,
    withDensity_smul' c⁻¹ _ (ENNReal.inv_ne_top.mpr hc0), smul_smul,
    ENNReal.mul_inv_cancel hc0 hc1, one_smul]

/-- **The pseudo-marginal scales linearly in the prior**: `m_{cπ}(x) = c · m_π(x)`. -/
theorem predictiveDensity_smul_prior (p : Θ → 𝓧 → ℝ≥0∞) (π : Measure Θ) (c : ℝ≥0∞) (x : 𝓧) :
    predictiveDensity p (c • π) x = c * predictiveDensity p π x := by
  simp only [predictiveDensity, lintegral_smul_measure, smul_eq_mul]

/-- **Bayes factors scale with improper-prior constants** (Robert §1.5/§5.2): rescaling the null
model's prior by `c` multiplies the Bayes factor by `c` — the formal reason improper priors are
unsafe for testing. -/
theorem bayesFactorM_smul_left {p₀ : Θ₀' → 𝓧 → ℝ≥0∞} {π₀ : Measure Θ₀'}
    {p₁ : Θ₁' → 𝓧 → ℝ≥0∞} {π₁ : Measure Θ₁'} {x : 𝓧} (c : ℝ≥0∞)
    -- USER-INPUT: the alternative's marginal is nondegenerate at `x`; Robert §5.2.2
    (h1 : predictiveDensity p₁ π₁ x ≠ 0) (h1' : predictiveDensity p₁ π₁ x ≠ ∞) :
    bayesFactorM p₀ (c • π₀) p₁ π₁ x = c * bayesFactorM p₀ π₀ p₁ π₁ x := by
  rw [bayesFactorM, bayesFactorM, predictiveDensity_smul_prior, mul_div_assoc]

/-- **Bridge to the abstract posterior**: on probability (or finite) priors, the generalized
posterior agrees predictive-a.e. with `κ†π` (restatement of the Batch-1 dominated Bayes
theorem). -/
theorem posterior_ae_eq_generalizedPosterior [StandardBorelSpace Θ] [Nonempty Θ]
    {π : Measure Θ} [IsFiniteMeasure π] {κ : Kernel Θ 𝓧} [IsFiniteKernel κ]
    {ν : Measure 𝓧} [SFinite ν] {p : Θ → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    ∀ᵐ x ∂(κ ∘ₘ π), (κ†π) x = generalizedPosterior p π x := by
  filter_upwards [posterior_eq_withDensity_likelihood_div_predictive hp hκ] with x hx
  rw [hx, generalizedPosterior_def]
  rfl

end StatLean.Bayesian
