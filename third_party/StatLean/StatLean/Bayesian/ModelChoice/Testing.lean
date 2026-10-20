module
public import StatLean.Bayesian.ModelChoice.Defs
public import StatLean.Bayesian.Decision.BayesEstimator
public import StatLean.Bayesian.Dominated.PosteriorDensity

@[expose] public section

/-!
# Bayesian testing: the threshold rule and point-null mixtures

Two testing results:

* **the Bayes test under asymmetric 0–1 loss** (Robert Proposition 5.2.2): the rule accepting
  `H₀ : θ ∈ Θ₀` iff `a₁·π(Θ₀ᶜ|x) ≤ a₀·π(Θ₀|x)` — equivalently iff
  `π(Θ₀|x) ≥ a₁/(a₀+a₁)` — is a Bayes estimator for the `a₀–a₁` loss;
* **the point-null posterior probability** (Robert §5.2.4): under the mixture prior
  `w·δ_{θ₀} + (1−w)·π₁`,
  $$\pi(\{\theta_0\} \mid x)
    = \frac{w\,p(\theta_0, x)}{w\,p(\theta_0, x) + (1-w)\int p(\theta, x)\,\pi_1(d\theta)}
    \qquad \text{predictive-a.e.}$$

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §5.2.1, eq. (5.2.1) and Proposition 5.2.2, p. 225; eq. (5.2.3),
p. 227; §5.2.3 (the mixture prior, Dirac at `θ₀`), p. 229; §5.2.4 (the posterior-probability
formula, verbatim but unnumbered), p. 231.

**Proof formalization notes.** The test: posterior expected losses of the two actions are
`a₁·post(Θ₀ᶜ)` and `a₀·post(Θ₀)` (indicator lintegrals of `hypLoss`), so the a.e.-argmin engine
`isBayesEstimator_of_ae_argmin` (Batch 1) applies with a `Bool.rec` over actions; measurability of
`bayesTest` comes from `Kernel.measurable_coe`. The point-null formula: the mixture prior is
finite by instances (`w : ℝ≥0` smul), the predictive density over it splits by
`lintegral_add_measure`/`lintegral_smul_measure`/`lintegral_dirac'`, and the posterior singleton
mass follows from the Batch-1 headline with `withDensity_apply` on `{θ₀}` (the hypothesis
`π₁{θ₀} = 0` keeps the alternative from contaminating the atom).

**Bibliographic comments.** The threshold structure of Bayes tests is the Bayesian counterpart of
the Neyman–Pearson lemma (1933) and appears with the a₀–a₁ loss following Wald's decision theory.
Point-null mixture priors originate with H. Jeffreys (1939) and were sharpened into calibration
results by J. O. Berger and T. Sellke ("Testing a point null hypothesis: the irreconcilability of
P values and evidence," *J. Amer. Statist. Assoc.* 82 (1987), 112–122).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]

/-- The Bayes test is a measurable decision rule. -/
theorem measurable_bayesTest [StandardBorelSpace Θ] [Nonempty Θ]
    (κ : Kernel Θ 𝓧) [IsFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π]
    {Θ₀ : Set Θ}
    -- LEAN-ONLY: the null hypothesis is an event (regularity)
    (hΘ₀ : MeasurableSet Θ₀) (a₀ a₁ : ℝ≥0∞) :
    Measurable (bayesTest κ π Θ₀ a₀ a₁) := by
  unfold bayesTest
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_le ((Kernel.measurable_coe _ hΘ₀.compl).const_mul a₁)
    ((Kernel.measurable_coe _ hΘ₀).const_mul a₀)

/-- The posterior expected loss of accepting `H₀` is `a₁·π(Θ₀ᶜ|x)`. -/
private theorem lintegral_hypLoss_true {Θ₀ : Set Θ} (hΘ₀ : MeasurableSet Θ₀) (a₀ a₁ : ℝ≥0∞)
    (ρ : Measure Θ) :
    ∫⁻ θ, hypLoss Θ₀ a₀ a₁ θ true ∂ρ = a₁ * ρ Θ₀ᶜ := by
  have h : (fun θ => hypLoss Θ₀ a₀ a₁ θ true) = Θ₀ᶜ.indicator (fun _ => a₁) := by
    funext θ
    by_cases hθ : θ ∈ Θ₀ <;> simp [hypLoss, Set.indicator_apply, Set.mem_compl_iff, hθ]
  rw [h, lintegral_indicator hΘ₀.compl, setLIntegral_const]

/-- The posterior expected loss of rejecting `H₀` is `a₀·π(Θ₀|x)`. -/
private theorem lintegral_hypLoss_false {Θ₀ : Set Θ} (hΘ₀ : MeasurableSet Θ₀) (a₀ a₁ : ℝ≥0∞)
    (ρ : Measure Θ) :
    ∫⁻ θ, hypLoss Θ₀ a₀ a₁ θ false ∂ρ = a₀ * ρ Θ₀ := by
  have h : (fun θ => hypLoss Θ₀ a₀ a₁ θ false) = Θ₀.indicator (fun _ => a₀) := by
    funext θ
    by_cases hθ : θ ∈ Θ₀ <;> simp [hypLoss, Set.indicator_apply, hθ]
  rw [h, lintegral_indicator hΘ₀, setLIntegral_const]

/-- **The Bayes test is a Bayes estimator for the `a₀–a₁` loss** (Robert Proposition 5.2.2). -/
theorem isBayesEstimator_bayesTest [StandardBorelSpace Θ] [Nonempty Θ]
    (κ : Kernel Θ 𝓧) [IsFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π]
    {Θ₀ : Set Θ}
    -- LEAN-ONLY: the null hypothesis is an event (regularity)
    (hΘ₀ : MeasurableSet Θ₀) (a₀ a₁ : ℝ≥0∞) :
    IsBayesEstimator (hypLoss Θ₀ a₀ a₁) κ
      (Kernel.deterministic (bayesTest κ π Θ₀ a₀ a₁) (measurable_bayesTest κ π hΘ₀ a₀ a₁))
      π := by
  have hℓ : Measurable (Function.uncurry (hypLoss Θ₀ a₀ a₁)) := by
    classical
    apply measurable_from_prod_countable_left
    intro b
    have h : (fun θ => Function.uncurry (hypLoss Θ₀ a₀ a₁) (θ, b))
        = fun θ => if θ ∈ Θ₀ then (if b then (0 : ℝ≥0∞) else a₀) else (if b then a₁ else 0) := rfl
    rw [h]
    exact Measurable.ite hΘ₀ measurable_const measurable_const
  refine isBayesEstimator_of_ae_argmin (hypLoss Θ₀ a₀ a₁) hℓ κ π
    (measurable_bayesTest κ π hΘ₀ a₀ a₁) ?_
  refine ae_of_all _ fun x y => ?_
  have hbt : bayesTest κ π Θ₀ a₀ a₁ x
      = if a₁ * (κ†π) x Θ₀ᶜ ≤ a₀ * (κ†π) x Θ₀ then true else false := rfl
  by_cases hc : a₁ * (κ†π) x Θ₀ᶜ ≤ a₀ * (κ†π) x Θ₀
  · rw [hbt, if_pos hc, lintegral_hypLoss_true hΘ₀]
    cases y with
    | true => exact le_of_eq (lintegral_hypLoss_true hΘ₀ a₀ a₁ _).symm
    | false => rw [lintegral_hypLoss_false hΘ₀]; exact hc
  · rw [hbt, if_neg hc, lintegral_hypLoss_false hΘ₀]
    cases y with
    | true => rw [lintegral_hypLoss_true hΘ₀]; exact (not_le.mp hc).le
    | false => exact le_of_eq (lintegral_hypLoss_false hΘ₀ a₀ a₁ _).symm

/-- **Threshold form of the Bayes test** (Robert Proposition 5.2.2 / eq. (5.2.3)): for
nondegenerate `a₀ + a₁`, the test accepts iff the posterior null probability is at least
`a₁/(a₀+a₁)`. -/
theorem bayesTest_eq_threshold [StandardBorelSpace Θ] [Nonempty Θ]
    (κ : Kernel Θ 𝓧) [IsFiniteKernel κ] (π : Measure Θ) [IsFiniteMeasure π]
    {Θ₀ : Set Θ}
    -- LEAN-ONLY: the null hypothesis is an event (regularity)
    (hΘ₀ : MeasurableSet Θ₀) {a₀ a₁ : ℝ≥0∞}
    -- USER-INPUT: nondegenerate loss weights; Robert eq. (5.2.1)
    (h0 : a₀ + a₁ ≠ 0) (h1 : a₀ + a₁ ≠ ∞) (x : 𝓧) :
    bayesTest κ π Θ₀ a₀ a₁ x = (a₁ / (a₀ + a₁) ≤ (κ†π) x Θ₀ : Bool) := by
  obtain ⟨ha0, ha1⟩ := ENNReal.add_ne_top.mp h1
  have hp : (κ†π) x Θ₀ ≤ 1 := prob_le_one
  have hfin : a₁ * (κ†π) x Θ₀ ≠ ∞ :=
    ENNReal.mul_ne_top ha1 (ne_top_of_le_ne_top ENNReal.one_ne_top hp)
  have hcompl : (κ†π) x Θ₀ᶜ = 1 - (κ†π) x Θ₀ := prob_compl_eq_one_sub hΘ₀
  have hiff : (a₁ * (κ†π) x Θ₀ᶜ ≤ a₀ * (κ†π) x Θ₀)
      ↔ (a₁ / (a₀ + a₁) ≤ (κ†π) x Θ₀) := by
    rw [hcompl, ENNReal.div_le_iff' h0 h1, add_mul,
      ← ENNReal.add_le_add_iff_right hfin, ← mul_add, tsub_add_cancel_of_le hp, mul_one]
  simp only [bayesTest]
  exact decide_eq_decide.mpr hiff

/-- **Point-null posterior probability** (Robert §5.2.4, p. 231): under the mixture prior
`w·δ_{θ₀} + (1−w)·π₁` with `π₁{θ₀} = 0`, the posterior mass of the null atom is
`w·p(θ₀,x) / (w·p(θ₀,x) + (1−w)·m₁(x))`, predictive-a.e. -/
theorem pointNull_posterior_singleton_ae [StandardBorelSpace Θ] [Nonempty Θ]
    [MeasurableSingletonClass Θ]
    {κ : Kernel Θ 𝓧} [IsFiniteKernel κ] {ν : Measure 𝓧} [SFinite ν] {p : Θ → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ))
    {w : ℝ≥0}
    -- USER-INPUT: the null prior weight is a probability; Robert §5.2.3
    (hw : w ≤ 1) {θ₀ : Θ} {π₁ : Measure Θ} [IsProbabilityMeasure π₁]
    -- USER-INPUT: the alternative prior puts no mass at the null point; Robert §5.2.3
    (hπ₁ : π₁ {θ₀} = 0) :
    ∀ᵐ x ∂(κ ∘ₘ (w • Measure.dirac θ₀ + (1 - w) • π₁)),
      (κ†(w • Measure.dirac θ₀ + (1 - w) • π₁)) x {θ₀}
        = (w : ℝ≥0∞) * p θ₀ x
            / ((w : ℝ≥0∞) * p θ₀ x + ((1 - w : ℝ≥0) : ℝ≥0∞) * ∫⁻ θ, p θ x ∂π₁) := by
  filter_upwards [posterior_eq_withDensity_likelihood_div_predictive
      (κ := κ) (π := w • Measure.dirac θ₀ + (1 - w) • π₁) (ν := ν) (p := p) hp hκ] with x hx
  have hsing : (w • Measure.dirac θ₀ + (1 - w) • π₁) {θ₀} = (w : ℝ≥0∞) := by
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply' _ (measurableSet_singleton θ₀), hπ₁,
      Set.indicator_of_mem (Set.mem_singleton θ₀)]
    simp [ENNReal.smul_def, smul_eq_mul]
  have hD : ∫⁻ θ', p θ' x ∂(w • Measure.dirac θ₀ + (1 - w) • π₁)
      = (w : ℝ≥0∞) * p θ₀ x + ((1 - w : ℝ≥0) : ℝ≥0∞) * ∫⁻ θ, p θ x ∂π₁ := by
    rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
      lintegral_dirac' θ₀ hp.of_uncurry_right]
    simp only [ENNReal.smul_def, smul_eq_mul]
  rw [hx, withDensity_apply _ (measurableSet_singleton θ₀), lintegral_singleton]
  rw [hsing, hD, div_eq_mul_inv, div_eq_mul_inv]
  ring

end StatLean.Bayesian
