module
public import StatLean.Bayesian.Hierarchical.Decomposition

@[expose] public section

/-!
# Hierarchical posterior tower and mixture identity

The mathematical heart of hierarchical Bayes: the parameter posterior is the hyperposterior-average
of the conditional posteriors,
$$\Pi(d\theta \mid x) = \int_\Lambda \Pi_\lambda(d\theta \mid x)\,\rho(d\lambda \mid x),$$
and posterior expectations obey the corresponding tower rule
`E[g(θ)∣x] = E_{λ∣x}[ E_{θ∣λ,x}[g(θ)] ]`. The same decomposition lifts to the posterior predictive.

These are stated for a **dominated** hierarchical model (the setting the whole `StatLean.Bayesian`
area uses): the likelihood and prior kernels admit densities `p`, `q` against base measures `ν`, `μ`.
There the conditional posterior `Π_λ(·∣x)` is the density-form `generalizedPosterior p (Π_λ) x`
(equal a.e. to the abstract `conditionalPosterior λ x` by
`conditionalPosterior_givenHyper_ae_eq_generalizedPosterior`), which — unlike the abstract
measure-posterior — is jointly measurable in `(λ, x)`, so the outer hyperposterior integral is
well-behaved and the identity is a density Fubini computation.

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §5.3
(hierarchical model factorization), p. 108.

**Proof formalization notes.** Only the *likelihood* is assumed dominated (`hlik`); the prior kernel
`Π_•` stays abstract. Both sides reduce, for data-marginal-a.e. `x`, to
`Z(x)⁻¹ · ∫λ (∫θ g(θ)·p(θ,x) ∂Π_λ) ∂ρ` with `Z(x) = predictiveDensity p (mixPrior) x`. LHS:
`posterior_ae_eq_generalizedPosterior` turns `(K†Π)x` into the density form and `lintegral_bind`
expands `mixPrior = Π_• ∘ₘ ρ` over the abstract prior kernel. RHS:
`hyperPosterior_ae_eq_generalizedPosterior` with the collapsed per-`λ` density
`Z_λ(x) = predictiveDensity p (Π_λ) x` (the collapsed likelihood `K∘ₖΠ_• = ν.withDensity (Z_•(x))`
via the dominated predictive) turns the outer integral into a `withDensity` against `ρ` whose
per-`λ` normalizer `Z_λ(x)` **cancels** the conditional normalizer inside; `∫λ Z_λ(x) ∂ρ = Z(x)` is
`marginalLikelihood_hier_eq_lintegral_hyperMarginal`. No prior density is needed. The abstract
density-free version (dropping `hlik` too) needs a jointly-measurable conditional-posterior kernel
family (a ForMathlib disintegration primitive; see `notes/bayesian/roadmap.md`, Batch 4).

**Bibliographic comments.** The mixture/tower decomposition of a hierarchical posterior is the
Rao–Blackwellization structure exploited by every hierarchical Gibbs sampler (Gelfand and Smith,
1990) and the basis of the "conditioning" justifications of the Stein effect; it is
the measure-theoretic content of the law of total (conditional) expectation applied to the
three-stage model of Lindley and Smith (1972).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

/-- **Generalized-posterior expectation in density form** (the per-`x` reduction underlying the
whole tower): integrating `g` against `generalizedPosterior p π x` unweights by the pseudo-marginal,
`∫ g dΠ(·|x) = (∫ g(θ) p(θ,x) π(dθ)) · m(x)⁻¹`. Holds unconditionally (junk regimes `m ∈ {0,∞}`
are absorbed by `ℝ≥0∞` division). -/
private theorem lintegral_generalizedPosterior_mul {Θ 𝓧 : Type*} [MeasurableSpace Θ]
    [MeasurableSpace 𝓧] {p : Θ → 𝓧 → ℝ≥0∞} (hp : Measurable (Function.uncurry p))
    (π : Measure Θ) (x : 𝓧) {g : Θ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ θ, g θ ∂(generalizedPosterior p π x)
      = (∫⁻ θ, g θ * p θ x ∂π) * (predictiveDensity p π x)⁻¹ := by
  have hpx : Measurable fun θ => p θ x := hp.comp (measurable_id.prodMk measurable_const)
  rw [generalizedPosterior_def, lintegral_withDensity_eq_lintegral_mul _
    (show Measurable (bayesDensity p π x) from hpx.div_const _) hg]
  simp only [bayesDensity, Pi.mul_apply, div_eq_mul_inv]
  rw [← lintegral_mul_const _ (hg.fun_mul hpx)]
  exact lintegral_congr fun θ => by ring

variable {Λ Θ 𝓧 𝓨 : Type*} [MeasurableSpace Λ] [MeasurableSpace Θ] [MeasurableSpace 𝓧]
  [MeasurableSpace 𝓨] [StandardBorelSpace Θ] [Nonempty Θ] [StandardBorelSpace Λ] [Nonempty Λ]
  (H : HierBayesExperiment Λ Θ 𝓧)

omit [StandardBorelSpace Λ] [Nonempty Λ] in
/-- **Collapsed-joint disintegration** (the measure-theoretic content the tower rests on): the
`(x, θ)`-joint disintegrates through the data marginal with the parameter posterior as its
conditional. This is `compProd_posterior_eq_map_swap` for the collapsed likelihood `K` against the
mixed prior `Π = priorKernel ∘ₘ hyperPrior`, rewritten through `dataMarginal_eq_comp_mixPrior`. -/
theorem dataMarginal_compProd_thetaPosterior_eq_map_swap :
    H.dataMarginal ⊗ₘ (H.likelihood † H.mixPrior)
      = (H.mixPrior ⊗ₘ H.likelihood).map Prod.swap := by
  rw [dataMarginal_eq_comp_mixPrior]
  exact compProd_posterior_eq_map_swap

/-- **Posterior tower for the dominated hierarchy** (3A.7): a posterior expectation is the
hyperposterior average of the conditional (density-form) posterior expectations
(Gelman §5.3). -/
theorem posteriorExpectation_tower_hierarchical
    {ν : Measure 𝓧} [SFinite ν] {p : Θ → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated likelihood; Gelman §5.3
    (hlik : ∀ θ, H.likelihood θ = ν.withDensity (p θ))
    (g : Θ → ℝ≥0∞) (hg : Measurable g) :
    ∀ᵐ x ∂H.dataMarginal,
      ∫⁻ θ, g θ ∂((H.likelihood † H.mixPrior) x)
        = ∫⁻ lam, (∫⁻ θ, g θ ∂(generalizedPosterior p (H.priorKernel lam) x))
            ∂(H.hyperPosterior x) := by
  -- The collapsed likelihood `K ∘ₖ Π_•` is dominated with per-hyperparameter density
  -- `q' lam = predictiveDensity p (Π_λ)` (the per-`λ` marginal likelihood).
  set q' : Λ → 𝓧 → ℝ≥0∞ := fun lam => predictiveDensity p (H.priorKernel lam) with hq'def
  have hpx : ∀ y : 𝓧, Measurable fun θ => p θ y := fun y =>
    hp.comp (measurable_id.prodMk measurable_const)
  have hq' : Measurable (Function.uncurry q') := by
    have hf : Measurable (fun u : (Λ × 𝓧) × Θ => p u.2 u.1.2) :=
      hp.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
    exact Measurable.lintegral_kernel_prod_right'
      (κ := H.priorKernel.comap Prod.fst measurable_fst) hf
  have hcollapse : ∀ lam, (H.likelihood ∘ₖ H.priorKernel) lam = ν.withDensity (q' lam) := by
    intro lam
    rw [Kernel.comp_apply]
    exact comp_eq_withDensity_predictiveDensity hp hlik
  -- Transport the data marginal to the composed form used by the LHS-side lemmas.
  rw [dataMarginal_eq_comp_mixPrior]
  filter_upwards
    [posterior_ae_eq_generalizedPosterior (κ := H.likelihood) (π := H.mixPrior) hp hlik,
    dataMarginal_eq_comp_mixPrior H ▸ hyperPosterior_ae_eq_generalizedPosterior H hq' hcollapse,
    predictiveDensity_pos_ae (κ := H.likelihood) (π := H.mixPrior) hp hlik,
    predictiveDensity_lt_top_ae_comp (κ := H.likelihood) (π := H.mixPrior) hp hlik]
    with x hLHS hRHS hZpos hZlt
  -- Marginal-likelihood normalizer: `∫λ q'(λ,x) ρ = predictiveDensity p (mixPrior) x`.
  have hW : predictiveDensity q' H.hyperPrior x = predictiveDensity p H.mixPrior x := by
    rw [hq'def]
    exact (marginalLikelihood_hier_eq_lintegral_hyperMarginal H p hp x).symm
  -- Inner conditional expectation, in density form.
  have hFeq : ∀ lam, (∫⁻ θ, g θ ∂(generalizedPosterior p (H.priorKernel lam) x))
      = (∫⁻ θ, g θ * p θ x ∂(H.priorKernel lam)) * (predictiveDensity p (H.priorKernel lam) x)⁻¹ :=
    fun lam => lintegral_generalizedPosterior_mul hp _ x hg
  have hF : Measurable
      fun lam => ∫⁻ θ, g θ ∂(generalizedPosterior p (H.priorKernel lam) x) := by
    have hA : Measurable fun lam => ∫⁻ θ, g θ * p θ x ∂(H.priorKernel lam) :=
      Measurable.lintegral_kernel_prod_right' (κ := H.priorKernel)
        ((hg.comp measurable_snd).mul ((hpx x).comp measurable_snd))
    have hZlam : Measurable fun lam => predictiveDensity p (H.priorKernel lam) x :=
      Measurable.lintegral_kernel_prod_right' (κ := H.priorKernel) ((hpx x).comp measurable_snd)
    simp_rw [hFeq]
    exact hA.mul hZlam.inv
  -- `Z_λ(x) < ∞` for `ρ`-a.e. `λ`, since its `ρ`-integral is the finite `Z(x)`.
  have hZlam : Measurable fun lam => predictiveDensity p (H.priorKernel lam) x :=
    Measurable.lintegral_kernel_prod_right' (κ := H.priorKernel) ((hpx x).comp measurable_snd)
  have hZlamfin : ∀ᵐ lam ∂H.hyperPrior, predictiveDensity p (H.priorKernel lam) x < ∞ := by
    apply ae_lt_top hZlam
    rw [← marginalLikelihood_hier_eq_lintegral_hyperMarginal H p hp x]
    exact hZlt.ne
  -- Expand `mixPrior = Π_• ∘ₘ ρ` in the LHS numerator.
  have hbind : ∫⁻ θ, g θ * p θ x ∂H.mixPrior
      = ∫⁻ lam, ∫⁻ θ, g θ * p θ x ∂(H.priorKernel lam) ∂H.hyperPrior := by
    unfold HierBayesExperiment.mixPrior
    rw [Measure.lintegral_bind H.priorKernel.aemeasurable (hg.fun_mul (hpx x)).aemeasurable]
  -- Reduce both sides to the density form, then cancel the per-`λ` normalizer.
  rw [hLHS, hRHS, lintegral_generalizedPosterior_mul hp H.mixPrior x hg,
    lintegral_generalizedPosterior_mul (p := q') hq' H.hyperPrior x hF, hW]
  congr 1
  rw [hbind]
  apply lintegral_congr_ae
  filter_upwards [hZlamfin] with lam hlamfin
  rw [hFeq lam]
  simp only [hq'def]
  rcases eq_or_ne (predictiveDensity p (H.priorKernel lam) x) 0 with hz | hz
  · have hp0 : (fun θ => p θ x) =ᵐ[H.priorKernel lam] 0 :=
      likelihood_ae_eq_zero_of_predictiveDensity_eq_zero hp hz
    have hA0 : ∫⁻ θ, g θ * p θ x ∂(H.priorKernel lam) = 0 := by
      refine (lintegral_eq_zero_iff (hg.fun_mul (hpx x))).mpr ?_
      filter_upwards [hp0] with θ hθ
      simp only [Pi.zero_apply] at hθ ⊢
      rw [hθ, mul_zero]
    rw [hA0]; simp
  · rw [mul_assoc, ENNReal.inv_mul_cancel hz hlamfin.ne, mul_one]

/-- **The mixture identity** (3A.6, the single most important theorem of the batch), in evaluated
form: the parameter posterior of a set is the hyperposterior average of the conditional posteriors
of that set — `Π(s∣x) = ∫ Π_λ(s∣x) ρ(dλ∣x)` (Gelman §5.3). -/
theorem thetaPosterior_apply_eq_lintegral_hyperPosterior
    {ν : Measure 𝓧} [SFinite ν] {p : Θ → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated likelihood; Gelman §5.3
    (hlik : ∀ θ, H.likelihood θ = ν.withDensity (p θ))
    {s : Set Θ} (hs : MeasurableSet s) :
    ∀ᵐ x ∂H.dataMarginal,
      (H.likelihood † H.mixPrior) x s
        = ∫⁻ lam, generalizedPosterior p (H.priorKernel lam) x s ∂(H.hyperPosterior x) := by
  filter_upwards [posteriorExpectation_tower_hierarchical H hp hlik
    (s.indicator 1) (measurable_one.indicator hs)] with x hx
  rw [← lintegral_indicator_one hs, hx]
  simp_rw [lintegral_indicator_one hs]

/-- **Predictive tower** (3A.8): the hierarchical posterior predictive is the hyperposterior
average of the conditional posterior predictives (Gelman §5.3). -/
theorem posteriorPredictive_hierarchical_tower
    {ν : Measure 𝓧} [SFinite ν] {p : Θ → 𝓧 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated likelihood; Gelman §5.3
    (hlik : ∀ θ, H.likelihood θ = ν.withDensity (p θ))
    (KY : Kernel Θ 𝓨) [IsMarkovKernel KY] {s : Set 𝓨} (hs : MeasurableSet s) :
    ∀ᵐ x ∂H.dataMarginal,
      (KY ∘ₖ (H.likelihood † H.mixPrior)) x s
        = ∫⁻ lam, (KY ∘ₘ (generalizedPosterior p (H.priorKernel lam) x)) s
            ∂(H.hyperPosterior x) := by
  filter_upwards [posteriorExpectation_tower_hierarchical H hp hlik
    (fun θ => KY θ s) (KY.measurable_coe hs)] with x hx
  rw [Kernel.comp_apply' KY (H.likelihood † H.mixPrior) x hs, hx]
  simp_rw [Measure.bind_apply hs (Kernel.aemeasurable KY)]

end StatLean.Bayesian
