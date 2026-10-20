module
public import StatLean.Bayesian.Sufficiency.Defs
public import StatLean.Bayesian.GeneralizedBayes.Defs
public import StatLean.Bayesian.Dominated.PosteriorDensity

@[expose] public section

/-!
# Factorized likelihoods: posterior reduction and the likelihood principle

Consequences of the Fisher–Neyman factorization `p(θ, x) = g(θ, T x) · h(x)` for a dominated
model:

* the base factor `h` **cancels from the posterior** — the posterior at `x` is the
  `g(·, T x)`-reweighted prior (Robert's "the factor h(x) disappears," §1.3.1);
* the **posterior depends on the data only through the sufficient statistic**:
  `(κ†π) x = ((statKernel κ T)†π) (T x)` for predictive-a.e. `x`;
* the **likelihood principle**, dominated version: proportional likelihoods (`p₁(·, x₁) =
  c · p₂(·, x₂)`) give equal posteriors under the same prior (Robert §1.3.2).

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.3.1 (Definition 1.3.1 and the factorization theorem, p. 14);
§1.3.2 (the Likelihood Principle, stated as a boldface display, pp. 15–16, and the observation on
p. 16 that the posterior (1.2.3) depends on `x` only through the likelihood).

**Proof formalization notes.** The cancellation is `withDensity` algebra: at data with
`h(x) ∉ {0, ∞}` the ratio `p/m` equals `g/(∫ g dπ)` pointwise (`ENNReal.mul_div_mul_right`-style).
For the statistic reduction, the key bridge is `map_withDensity_comp` (a density factoring through
`T` passes through `Measure.map T`), which exhibits the statistic experiment as dominated by
`(ν.withDensity h).map T` with density `g`; both experiments' posteriors are then identified by the
Batch-1 dominated Bayes theorem, and the exceptional sets transport because `h ∈ (0, ∞)` holds
`(κ ∘ₘ π)`-a.e. (forced by `predictiveDensity_pos_ae`/`_lt_top_ae_comp` — not hypotheses). The
likelihood principle is the scalar case of the same cancellation.

**Bibliographic comments.** The Likelihood Principle was articulated by G. Barnard (1949) and
R. A. Fisher, given its modern form by A. Birnbaum ("On the foundations of statistical inference,"
*J. Amer. Statist. Assoc.* 57 (1962), 269–306), and defended at book length by J. O. Berger and
R. L. Wolpert, *The Likelihood Principle* (IMS, 1988). That Bayesian inference automatically obeys
it (the posterior depends only on the likelihood) is formalized here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 S : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  [mS : MeasurableSpace S]

/-- The statistic kernel is the pushforward: `statKernel K T hT θ = (K θ).map T`
(Robert §1.3.1). -/
theorem statKernel_apply (K : Kernel Θ 𝓧) {T : 𝓧 → S} (hT : Measurable T) (θ : Θ) :
    statKernel K hT θ = (K θ).map T := by
  show (Kernel.deterministic T hT ∘ₖ K) θ = (K θ).map T
  rw [Kernel.comp_apply, Measure.deterministic_comp_eq_map hT]

/-- A density factoring through `T` passes through the pushforward:
`(μ.withDensity (f ∘ T)).map T = (μ.map T).withDensity f`. -/
theorem map_withDensity_comp {T : 𝓧 → S}
    -- LEAN-ONLY: the statistic and the density are measurable (regularity)
    (hT : Measurable T) {f : S → ℝ≥0∞} (hf : Measurable f) (μ : Measure 𝓧) :
    (μ.withDensity fun x => f (T x)).map T = (μ.map T).withDensity f := by
  ext s hs
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs), withDensity_apply _ hs,
    Measure.restrict_map hT hs, lintegral_map hf hT]

/-- **The base factor cancels from the posterior** (Robert §1.3.1): under a Fisher–Neyman
factorization, at any data point where `h(x) ∉ {0, ∞}` the generalized posterior is the
`g(·, T x)`-reweighted prior. -/
theorem generalizedPosterior_of_factorized {p : Θ → 𝓧 → ℝ≥0∞} {T : 𝓧 → S}
    {g : Θ → S → ℝ≥0∞} {h : 𝓧 → ℝ≥0∞} {π : Measure Θ}
    -- USER-INPUT: Fisher–Neyman factorization of the likelihood; Robert §1.3.1, p. 14
    (hfac : IsFactorizedLikelihood p T g h) {x : 𝓧}
    -- USER-INPUT: the base factor is positive and finite at the observed data; Robert §1.3.1
    (hx0 : h x ≠ 0) (hx' : h x ≠ ∞) :
    generalizedPosterior p π x
      = π.withDensity fun θ => g θ (T x) / ∫⁻ θ', g θ' (T x) ∂π := by
  have hpred : predictiveDensity p π x = (∫⁻ θ', g θ' (T x) ∂π) * h x := by
    unfold predictiveDensity
    have hfac' : ∀ θ' x', p θ' x' = g θ' (T x') * h x' := hfac
    simp_rw [hfac']
    rw [lintegral_mul_const' _ _ hx']
  rw [generalizedPosterior_def]
  congr 1
  funext θ
  show p θ x / predictiveDensity p π x = g θ (T x) / ∫⁻ θ', g θ' (T x) ∂π
  rw [hfac θ x, hpred, ENNReal.mul_div_mul_right _ _ hx0 hx']

/-- **The posterior depends on the data only through a sufficient statistic** (Robert §1.3.1–1.3.2,
dominated form): under a Fisher–Neyman factorization, the full-data posterior at `x` equals the
statistic-experiment posterior at `T x`, for predictive-almost-every `x`. -/
theorem posterior_ae_eq_posterior_statKernel [StandardBorelSpace Θ] [Nonempty Θ]
    {π : Measure Θ} [IsFiniteMeasure π] {κ : Kernel Θ 𝓧} [IsFiniteKernel κ]
    {ν : Measure 𝓧} [SFinite ν] {p : Θ → 𝓧 → ℝ≥0∞} {T : 𝓧 → S}
    -- LEAN-ONLY: measurability of the density family, statistic, and factors (regularity)
    (hp : Measurable (Function.uncurry p)) (hT : Measurable T)
    {g : Θ → S → ℝ≥0∞} (hg : Measurable (Function.uncurry g))
    {h : 𝓧 → ℝ≥0∞} (hh : Measurable h)
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ))
    -- USER-INPUT: Fisher–Neyman factorization of the likelihood; Robert §1.3.1, p. 14
    (hfac : IsFactorizedLikelihood p T g h) :
    ∀ᵐ x ∂(κ ∘ₘ π), (κ†π) x = ((statKernel κ hT)†π) (T x) := by
  -- `g θ` is measurable, as is its precomposition with `T`.
  have hgθ : ∀ θ, Measurable (g θ) := fun θ =>
    hg.comp (measurable_const.prodMk measurable_id)
  -- The statistic experiment is dominated by `ν' := (ν.withDensity h).map T` with density `g`.
  have hκ' : ∀ θ, statKernel κ hT θ = ((ν.withDensity h).map T).withDensity (g θ) := by
    intro θ
    rw [statKernel_apply κ hT θ, hκ θ]
    have hpθ : (p θ) = h * fun x => g θ (T x) := by
      funext x; rw [Pi.mul_apply, hfac θ x, mul_comm]
    rw [hpθ, withDensity_mul _ hh (show Measurable fun x => g θ (T x) from (hgθ θ).comp hT),
      map_withDensity_comp hT (hgθ θ)]
  -- Batch-1 dominated Bayes for the full and the statistic experiments.
  have hfull := posterior_eq_withDensity_likelihood_div_predictive (κ := κ) (π := π) (ν := ν) hp hκ
  have hstatpost := posterior_eq_withDensity_likelihood_div_predictive
    (κ := statKernel κ hT) (π := π) (ν := (ν.withDensity h).map T) hg hκ'
  -- The statistic law is the pushforward of the data law: `statKernel κ hT ∘ₘ π = (κ ∘ₘ π).map T`.
  have hmap : statKernel κ hT ∘ₘ π = (κ ∘ₘ π).map T := by
    show (Kernel.deterministic T hT ∘ₖ κ) ∘ₘ π = (κ ∘ₘ π).map T
    rw [← Measure.comp_assoc, Measure.deterministic_comp_eq_map hT]
  rw [hmap] at hstatpost
  -- Transport the statistic-side a.e. equality back along `T`.
  have hstat := ae_of_ae_map hT.aemeasurable hstatpost
  have hpos := predictiveDensity_pos_ae (κ := κ) (π := π) (ν := ν) hp hκ
  have hlt := predictiveDensity_lt_top_ae_comp (κ := κ) (π := π) (ν := ν) hp hκ
  filter_upwards [hfull, hstat, hpos, hlt] with x hx hxstat hxpos hxlt
  -- The predictive density factors: `m x = (∫ g(·, T x) dπ) * h x`.
  have hgTx : Measurable fun θ' => g θ' (T x) := hg.comp (measurable_id.prodMk measurable_const)
  have hmfac : predictiveDensity p π x = (∫⁻ θ', g θ' (T x) ∂π) * h x := by
    unfold predictiveDensity
    have hfac' : ∀ θ' x', p θ' x' = g θ' (T x') * h x' := hfac
    simp_rw [hfac']
    rw [lintegral_mul_const _ hgTx]
  -- Hence `h x ∈ (0, ∞)`.
  have hne0 : (∫⁻ θ', g θ' (T x) ∂π) * h x ≠ 0 := by rw [← hmfac]; exact hxpos.ne'
  obtain ⟨hA0, hx0⟩ := mul_ne_zero_iff.mp hne0
  have hx' : h x ≠ ∞ := by
    intro hinf
    exact hxlt.ne (by rw [hmfac, hinf, ENNReal.mul_top hA0])
  -- Bridge the two posteriors via the cancellation of `h`.
  rw [hx, hxstat, ← generalizedPosterior_of_factorized hfac hx0 hx', generalizedPosterior_def]
  rfl

/-- **The likelihood principle**, dominated version (Robert §1.3.2, pp. 15–16): proportional
likelihoods yield the same posterior under the same prior. -/
theorem generalizedPosterior_eq_of_likelihood_proportional {p₁ p₂ : Θ → 𝓧 → ℝ≥0∞}
    {π : Measure Θ} {x₁ x₂ : 𝓧} {c : ℝ≥0∞}
    -- USER-INPUT: the proportionality constant is nondegenerate; Robert §1.3.2
    (hc0 : c ≠ 0) (hc' : c ≠ ∞)
    -- USER-INPUT: the two observations have proportional likelihoods; Robert §1.3.2
    (hprop : ∀ θ, p₁ θ x₁ = c * p₂ θ x₂) :
    generalizedPosterior p₁ π x₁ = generalizedPosterior p₂ π x₂ := by
  have hpred : predictiveDensity p₁ π x₁ = c * predictiveDensity p₂ π x₂ := by
    unfold predictiveDensity
    simp_rw [hprop]
    rw [lintegral_const_mul' c _ hc']
  rw [generalizedPosterior_def, generalizedPosterior_def]
  congr 1
  funext θ
  show p₁ θ x₁ / predictiveDensity p₁ π x₁ = p₂ θ x₂ / predictiveDensity p₂ π x₂
  rw [hprop θ, hpred, ENNReal.mul_div_mul_left _ _ hc0 hc']

end StatLean.Bayesian
