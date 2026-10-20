module
public import StatLean.Bayesian.Hierarchical.Defs
public import StatLean.Bayesian.GeneralizedBayes.Basic

@[expose] public section

/-!
# Hierarchical decomposition — marginal prior, marginal likelihood, hyper/conditional posteriors

The algebra of the three-stage hierarchy: the marginal prior integrates out the hyperparameter,
the marginal likelihood is the hyperprior-average of the per-hyperparameter marginals, and both the
hyperposterior and the conditional posteriors are ordinary dominated Bayes posteriors.

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §5.3
(hierarchical posterior factorization, eq. 5.3), p. 108.

**Proof formalization notes.** `mixPrior_apply` is `Measure.bind_apply`; `dataMarginal_eq_comp_mixPrior`
is kernel/measure composition associativity (`Measure.comp_assoc`/`bind_bind`);
`marginalLikelihood_hier_eq_lintegral_hyperMarginal` is Tonelli (`lintegral_bind`) on the nested
`∫λ∫θ p(θ,x)`; `hyperPosterior_ae_eq_generalizedPosterior` and
`conditionalPosterior_givenHyper_ae_eq_generalizedPosterior` are single applications of the Batch-2
`posterior_ae_eq_generalizedPosterior` to the collapsed likelihood `K∘ₖΠ` (resp. `K`) with respect
to the hyperprior (resp. the prior `Π_λ`).

**Bibliographic comments.** The conditional decomposition of a hierarchical posterior into a
hyperposterior and per-hyperparameter conditional posteriors is the computational heart of
hierarchical Bayes (Lindley and Smith, *J. Roy. Statist. Soc. Ser. B* 34 (1972), 1–41); it is what
makes the Gibbs sampler of Gelfand and Smith (*J. Amer. Statist. Assoc.* 85
(1990), 398–409) applicable to these models.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Λ Θ 𝓧 : Type*} [MeasurableSpace Λ] [MeasurableSpace Θ] [MeasurableSpace 𝓧]
  (H : HierBayesExperiment Λ Θ 𝓧)

/-- **Marginal prior on a set** (3A.1): `Π(s) = ∫ Π_λ(s) ρ(dλ)` (Gelman §5.3). -/
theorem mixPrior_apply {s : Set Θ} (hs : MeasurableSet s) :
    H.mixPrior s = ∫⁻ lam, H.priorKernel lam s ∂H.hyperPrior := by
  unfold HierBayesExperiment.mixPrior
  rw [Measure.bind_apply hs H.priorKernel.aemeasurable]

/-- **Associativity of the three-stage marginal** (3A.2): the data marginal equals the likelihood
pushed through the marginal prior (Gelman §5.3). -/
theorem dataMarginal_eq_comp_mixPrior :
    H.dataMarginal = H.likelihood ∘ₘ H.mixPrior := by
  unfold HierBayesExperiment.dataMarginal HierBayesExperiment.mixPrior
  rw [Measure.comp_assoc]

/-- **Marginal likelihood of the hierarchy** (3A.3): the marginal density under the mixed prior is
the hyperprior-average of the per-hyperparameter marginal densities (Gelman §5.3). -/
theorem marginalLikelihood_hier_eq_lintegral_hyperMarginal
    (p : Θ → 𝓧 → ℝ≥0∞) (hp : Measurable (Function.uncurry p)) (x : 𝓧) :
    predictiveDensity p H.mixPrior x
      = ∫⁻ lam, predictiveDensity p (H.priorKernel lam) x ∂H.hyperPrior := by
  unfold predictiveDensity HierBayesExperiment.mixPrior
  have hpx : Measurable fun θ => p θ x := hp.comp (measurable_id.prodMk measurable_const)
  rw [Measure.lintegral_bind H.priorKernel.aemeasurable hpx.aemeasurable]

/-- **Hyperposterior in density form** (3A.4, the central theorem of hierarchical Bayes): if the
collapsed likelihood `K ∘ₖ Π` is dominated with per-hyperparameter density `q`, the hyperposterior
is the generalized posterior of `q` against the hyperprior, for data-marginal-a.e. `x`
(Gelman §5.3). -/
theorem hyperPosterior_ae_eq_generalizedPosterior
    [StandardBorelSpace Λ] [Nonempty Λ] {ν : Measure 𝓧} [SFinite ν] {q : Λ → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the collapsed marginal density (regularity)
    (hq : Measurable (Function.uncurry q))
    -- USER-INPUT: the collapsed likelihood is dominated with density `q`; Gelman §5.3
    (hcollapse : ∀ lam, (H.likelihood ∘ₖ H.priorKernel) lam = ν.withDensity (q lam)) :
    ∀ᵐ x ∂H.dataMarginal, H.hyperPosterior x = generalizedPosterior q H.hyperPrior x := by
  unfold HierBayesExperiment.dataMarginal HierBayesExperiment.hyperPosterior
  exact posterior_ae_eq_generalizedPosterior hq hcollapse

/-- **Conditional posterior given a hyperparameter** (3A.5): for fixed `λ`, the posterior on `Θ` is
the generalized posterior of the likelihood density against the prior `Π_λ` (Gelman §5.3). -/
theorem conditionalPosterior_givenHyper_ae_eq_generalizedPosterior
    [StandardBorelSpace Θ] [Nonempty Θ] {ν : Measure 𝓧} [SFinite ν] {p : Θ → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated likelihood; Gelman §5.3
    (hκ : ∀ θ, H.likelihood θ = ν.withDensity (p θ)) (lam : Λ) :
    ∀ᵐ x ∂(H.likelihood ∘ₘ H.priorKernel lam),
      H.conditionalPosterior lam x = generalizedPosterior p (H.priorKernel lam) x := by
  unfold HierBayesExperiment.conditionalPosterior
  exact posterior_ae_eq_generalizedPosterior hp hκ

end StatLean.Bayesian
