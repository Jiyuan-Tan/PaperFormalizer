module
public import StatLean.Bayesian.GeneralizedBayes.Defs
public import StatLean.Bayesian.Dominated.PredictiveDensity
public import StatLean.Bayesian.Dominated.PosteriorDensity

@[expose] public section

/-!
# Sequential Bayes and reparameterization equivariance

Two coherence properties of Bayesian updating:

* **Sequential Bayes** (Gelman §1.3): updating on `x` and then on `y` equals updating once
  on the joint observation `(x, y)` — for a dominated pair experiment `κ₁ ×ₖ κ₂`,
  $$\big((\kappa_1 \times \kappa_2)^{\dagger}_\pi\big)(x, y)
    = \big(\pi_x\big)_y \qquad \text{predictive-a.e.},$$
  where `π_x` is the generalized posterior for the first coordinate;
* **Reparameterization equivariance**: for a measurable equivalence `φ : Θ ≃ᵐ Θ'`, the posterior
  transforms by pushforward, `(κ.comap φ.symm)†(π.map φ) = ((κ†π) ·).map φ` predictive-a.e.

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §1.3, p. 6.

**Proof formalization notes.** Sequential: the pair kernel is dominated by `ν₁.prod ν₂` with the
product density (pinned `prod_withDensity_left/right` + `withDensity_mul`); apply the Batch-1
headline and rearrange with `ENNReal` algebra; the first-coordinate nondegeneracy `0 < m₁ < ∞`
transports along `Prod.fst` (`Kernel.fst_prod`, `Measure.map_comp`). Reparameterization is
abstract (no domination): verify the disintegration property of `((κ†π) ·).map φ` with
`ae_eq_posterior_of_compProd_eq`, `Measure.compProd_map`, and the rectangle lemma
`map_compProd_comap` below.

**Bibliographic comments.** Sequential coherence — today's posterior is tomorrow's prior — is the
operational heart of Bayesian learning, already used by Laplace and stressed axiomatically by
B. de Finetti (1937) and D. V. Lindley (*Introduction to Probability and Statistics from a
Bayesian Viewpoint*, Cambridge, 1965). Equivariance under reparameterization is the invariance
desideratum behind Jeffreys's priors (H. Jeffreys, *Theory of Probability*, 1939).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ Θ' 𝓧 𝓨 : Type*} [mΘ : MeasurableSpace Θ] [mΘ' : MeasurableSpace Θ']
  [m𝓧 : MeasurableSpace 𝓧] [m𝓨 : MeasurableSpace 𝓨]

/-- **Sequential Bayes** (Gelman §1.3), dominated form: the posterior of the pair
experiment at `(x, y)` is the `y`-update of the `x`-posterior, predictive-a.e. -/
theorem posterior_prod_ae_eq_sequential
    [StandardBorelSpace Θ] [Nonempty Θ] {π : Measure Θ} [IsFiniteMeasure π]
    {κ₁ : Kernel Θ 𝓧} [IsMarkovKernel κ₁] {κ₂ : Kernel Θ 𝓨} [IsMarkovKernel κ₂]
    {ν₁ : Measure 𝓧} [SigmaFinite ν₁] {ν₂ : Measure 𝓨} [SigmaFinite ν₂]
    {p₁ : Θ → 𝓧 → ℝ≥0∞} {p₂ : Θ → 𝓨 → ℝ≥0∞}
    -- LEAN-ONLY: joint measurability of the two densities (regularity)
    (hp₁ : Measurable (Function.uncurry p₁)) (hp₂ : Measurable (Function.uncurry p₂))
    -- USER-INPUT: both coordinates are dominated models; Gelman §1.3
    (hκ₁ : ∀ θ, κ₁ θ = ν₁.withDensity (p₁ θ)) (hκ₂ : ∀ θ, κ₂ θ = ν₂.withDensity (p₂ θ)) :
    ∀ᵐ q ∂((κ₁ ×ₖ κ₂) ∘ₘ π),
      ((κ₁ ×ₖ κ₂)†π) q = generalizedPosterior p₂ (generalizedPosterior p₁ π q.1) q.2 := by
  -- (i) The pair experiment is dominated by `ν₁.prod ν₂` with the product density.
  set pJ : Θ → 𝓧 × 𝓨 → ℝ≥0∞ := fun θ q => p₁ θ q.1 * p₂ θ q.2 with hpJdef
  have hpJmeas : Measurable (Function.uncurry pJ) :=
    (hp₁.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hp₂.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hκJ : ∀ θ, (κ₁ ×ₖ κ₂) θ = (ν₁.prod ν₂).withDensity (pJ θ) := by
    intro θ
    have h₁ : Measurable (p₁ θ) := hp₁.comp (measurable_const.prodMk measurable_id)
    have h₂ : Measurable (p₂ θ) := hp₂.comp (measurable_const.prodMk measurable_id)
    rw [Kernel.prod_apply, hκ₁, hκ₂, prod_withDensity₀ h₁.aemeasurable h₂.aemeasurable]
  -- (ii) Batch-1 dominated Bayes for the pair.
  haveI : IsMarkovKernel (κ₁ ×ₖ κ₂) := inferInstance
  haveI : SFinite (ν₁.prod ν₂) := inferInstance
  have hbayes := posterior_eq_withDensity_likelihood_div_predictive
    (π := π) (κ := κ₁ ×ₖ κ₂) (ν := ν₁.prod ν₂) (p := pJ) hpJmeas hκJ
  -- (iii) The first-coordinate predictive `m₁` is nondegenerate `(κ₁ ×ₖ κ₂) ∘ₘ π`-a.e.
  have hfst : ((κ₁ ×ₖ κ₂) ∘ₘ π).map Prod.fst = κ₁ ∘ₘ π := by
    rw [Measure.map_comp _ _ measurable_fst, ← Kernel.fst_eq, Kernel.fst_prod]
  have hpos : ∀ᵐ q ∂((κ₁ ×ₖ κ₂) ∘ₘ π), 0 < predictiveDensity p₁ π q.1 := by
    have h := predictiveDensity_pos_ae (κ := κ₁) (π := π) (ν := ν₁) hp₁ hκ₁
    rw [← hfst] at h
    rwa [ae_map_iff measurable_fst.aemeasurable
      (measurableSet_lt measurable_const (measurable_predictiveDensity hp₁))] at h
  have htop : ∀ᵐ q ∂((κ₁ ×ₖ κ₂) ∘ₘ π), predictiveDensity p₁ π q.1 < ∞ := by
    have h := predictiveDensity_lt_top_ae_comp (κ := κ₁) (π := π) (ν := ν₁) hp₁ hκ₁
    rw [← hfst] at h
    rwa [ae_map_iff measurable_fst.aemeasurable
      (measurableSet_lt (measurable_predictiveDensity hp₁) measurable_const)] at h
  -- (iv) Rearrange the joint posterior into the two-stage form.
  filter_upwards [hbayes, hpos, htop] with q hq hqpos hqtop
  rw [hq]
  have hm0 : predictiveDensity p₁ π q.1 ≠ 0 := hqpos.ne'
  have hmtop : predictiveDensity p₁ π q.1 ≠ ∞ := hqtop.ne
  have ha : Measurable (fun θ => p₁ θ q.1) := hp₁.comp (measurable_id.prodMk measurable_const)
  have hb : Measurable (fun θ => p₂ θ q.2) := hp₂.comp (measurable_id.prodMk measurable_const)
  have hbd1 : Measurable (bayesDensity p₁ π q.1) := ha.div_const (predictiveDensity p₁ π q.1)
  have hbd2 : Measurable (bayesDensity p₂ (generalizedPosterior p₁ π q.1) q.2) :=
    hb.div_const (predictiveDensity p₂ (generalizedPosterior p₁ π q.1) q.2)
  -- The first-stage generalized posterior has density `p₁(·,q.1)/m₁`.
  have hgp₁ : generalizedPosterior p₁ π q.1
      = π.withDensity (fun θ => p₁ θ q.1 / predictiveDensity p₁ π q.1) := rfl
  -- The second-stage predictive `m₂ = m₁₂ / m₁`, in multiplicative form `m₁ * m₂ = m₁₂`.
  have hprod : predictiveDensity p₁ π q.1
        * predictiveDensity p₂ (generalizedPosterior p₁ π q.1) q.2
      = ∫⁻ θ', p₁ θ' q.1 * p₂ θ' q.2 ∂π := by
    show predictiveDensity p₁ π q.1 * (∫⁻ θ, p₂ θ q.2 ∂(generalizedPosterior p₁ π q.1))
      = ∫⁻ θ', p₁ θ' q.1 * p₂ θ' q.2 ∂π
    rw [hgp₁, lintegral_withDensity_eq_lintegral_mul _ (ha.div_const _) hb]
    simp only [Pi.mul_apply]
    rw [← lintegral_const_mul _ ((ha.div_const _).fun_mul hb)]
    refine lintegral_congr fun θ => ?_
    rw [← mul_assoc, ENNReal.mul_div_cancel hm0 hmtop]
  -- Assemble: two-stage density equals the joint density.
  rw [generalizedPosterior_def]
  nth_rewrite 1 [generalizedPosterior_def]
  rw [← withDensity_mul _ hbd1 hbd2]
  refine withDensity_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  simp only [Pi.mul_apply, bayesDensity, hpJdef]
  rw [← hprod, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl hm0) (Or.inl hmtop)]
  ring

/-- Change of prior variables through `compProd` (rectangle computation). -/
theorem map_compProd_comap (φ : Θ ≃ᵐ Θ') (κ : Kernel Θ 𝓧) [IsSFiniteKernel κ]
    (π : Measure Θ) [SFinite π] :
    (π.map φ) ⊗ₘ (κ.comap φ.symm φ.symm.measurable) = (π ⊗ₘ κ).map (Prod.map φ id) := by
  have hmap : Measurable (Prod.map (φ : Θ → Θ') (id : 𝓧 → 𝓧)) :=
    φ.measurable.prodMap measurable_id
  have hk : (Kernel.id ×ₖ κ.comap φ.symm φ.symm.measurable) ∘ₖ
        Kernel.deterministic (φ : Θ → Θ') φ.measurable
      = (Kernel.id ×ₖ κ).map (Prod.map (φ : Θ → Θ') id) := by
    rw [Kernel.comp_deterministic_eq_comap]
    ext θ : 1
    rw [Kernel.comap_apply, Kernel.map_apply _ hmap, Kernel.prod_apply, Kernel.prod_apply,
      Kernel.id_apply, Kernel.id_apply, Kernel.comap_apply, φ.symm_apply_apply,
      ← Measure.map_prod_map _ _ φ.measurable measurable_id, Measure.map_dirac' φ.measurable,
      Measure.map_id]
  rw [Measure.compProd_eq_comp_prod, ← Measure.deterministic_comp_eq_map φ.measurable,
    Measure.comp_assoc, hk, Measure.compProd_eq_comp_prod, Measure.map_comp _ _ hmap]

/-- **Reparameterization equivariance of the posterior** (Gelman §1.3 invariance): for a
measurable equivalence of parameter spaces, the posterior of the reparameterized experiment is the
pushforward of the original posterior, predictive-a.e. -/
theorem posterior_comap_map_ae_eq_map_posterior
    [StandardBorelSpace Θ] [Nonempty Θ] [StandardBorelSpace Θ'] [Nonempty Θ']
    {π : Measure Θ} [IsFiniteMeasure π] (κ : Kernel Θ 𝓧) [IsFiniteKernel κ] (φ : Θ ≃ᵐ Θ') :
    ∀ᵐ x ∂(κ ∘ₘ π),
      ((κ.comap φ.symm φ.symm.measurable)†(π.map φ)) x = ((κ†π) x).map φ := by
  haveI : IsFiniteMeasure (π.map φ) := Measure.isFiniteMeasure_map π φ
  have hmapφid : Measurable (Prod.map (φ : Θ → Θ') (id : 𝓧 → 𝓧)) :=
    φ.measurable.prodMap measurable_id
  have hmapidφ : Measurable (Prod.map (id : 𝓧 → 𝓧) (φ : Θ → Θ')) :=
    measurable_id.prodMap φ.measurable
  -- The reparameterized experiment has the same data distribution.
  have hker : (κ.comap φ.symm φ.symm.measurable).comap (φ : Θ → Θ') φ.measurable = κ := by
    ext θ : 1
    rw [Kernel.comap_apply, Kernel.comap_apply, φ.symm_apply_apply]
  have hbase : (κ.comap φ.symm φ.symm.measurable) ∘ₘ (π.map φ) = κ ∘ₘ π := by
    rw [← Measure.deterministic_comp_eq_map φ.measurable, Measure.comp_assoc,
      Kernel.comp_deterministic_eq_comap, hker]
  -- The pushforward posterior disintegrates the reparameterized experiment.
  have hfun : (Prod.map (id : 𝓧 → 𝓧) (φ : Θ → Θ')) ∘ (Prod.swap : Θ × 𝓧 → 𝓧 × Θ)
      = (Prod.swap : Θ' × 𝓧 → 𝓧 × Θ') ∘ (Prod.map (φ : Θ → Θ') id) := by
    funext z; rfl
  have hcompProd :
      ((κ.comap φ.symm φ.symm.measurable) ∘ₘ (π.map φ)) ⊗ₘ ((κ†π).map (φ : Θ → Θ'))
        = ((π.map φ) ⊗ₘ (κ.comap φ.symm φ.symm.measurable)).map Prod.swap := by
    rw [hbase, Measure.compProd_map φ.measurable, compProd_posterior_eq_map_swap,
      Measure.map_map hmapidφ measurable_swap, hfun,
      ← Measure.map_map measurable_swap hmapφid, ← map_compProd_comap]
  have hae := ae_eq_posterior_of_compProd_eq
    (κ := κ.comap φ.symm φ.symm.measurable) (μ := π.map φ) hcompProd
  rw [hbase] at hae
  filter_upwards [hae] with x hx
  rw [← hx, Kernel.map_apply _ φ.measurable]

end StatLean.Bayesian
