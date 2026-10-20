module
public import StatLean.Bayesian.Updating.Defs
public import Mathlib.Probability.Kernel.CondDistrib

@[expose] public section

/-!
# The posterior predictive is the conditional law of the future given the data

The theorem that justifies `posteriorPredictive`: under the joint Bayesian model
`(θ, x, y) ~ π ⊗ₘ (KX ×ₖ KY)` (parameter from the prior; data and future conditionally
independent given the parameter), the conditional law of the future `y` given the data `x` is the
posterior predictive:
$$\mathcal L(Y \mid X = x) = \int_\Theta K_Y(\theta, \cdot)\,\pi(d\theta \mid x)
  \qquad \text{for } (K_X \circ_m \pi)\text{-a.e. } x.$$
The mathematical pivot is the disintegration
`(KX ×ₖ KY) ∘ₘ π = (KX ∘ₘ π) ⊗ₘ posteriorPredictive KX KY π` — "data ⊗ predictive = joint of the
pair" — from which the `condDistrib` identification is uniqueness of disintegration.

**Reference.** A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, and D. B. Rubin,
*Bayesian Data Analysis*, 3rd ed., Chapman & Hall/CRC, 2014 (ISBN 978-1-4398-9820-8). §1.3
(prediction / posterior predictive distribution), p. 7.

**Proof formalization notes.** The pivotal lemma is a rectangle (π-system) computation routed
through the pinned `compProd_posterior_eq_map_swap`: both sides evaluate on `A ×ˢ B` to
`∫⁻ θ, KX θ A * KY θ B ∂π`. The `condDistrib` statement then follows from the pinned uniqueness
lemma `condDistrib_ae_eq_of_measure_eq_compProd` applied to the coordinate maps on
`Θ × 𝓧 × 𝓨`, with marginal bookkeeping (`Measure.snd_compProd`, `Kernel.fst_prod`,
`Measure.map_map`); the future space `𝓨` must be standard Borel for `condDistrib` to exist.
Conditional independence of `x` and `y` given `θ` is encoded by the product kernel `KX ×ₖ KY` —
a constitutive modeling choice, not a regularity assumption.

**Bibliographic comments.** Reading prediction as conditioning in a joint model over parameter,
data, and future is the de Finetti–Geisser predictivist program (B. de Finetti, *Theory of
Probability*, 1974; S. Geisser, *Predictive Inference*, 1993) and the semantic basis of
probabilistic programming. The disintegration technology is Kolmogorov (1933) and Doob (1953), as
packaged by Mathlib's `condDistrib`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 𝓨 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  [m𝓨 : MeasurableSpace 𝓨]

/-- **Data ⊗ predictive = joint of the pair** (the pivotal disintegration behind Gelman §1.3): binding the prior through the pair experiment factors as the data marginal
`compProd` the posterior predictive. -/
theorem comp_prod_eq_compProd_posteriorPredictive
    [StandardBorelSpace Θ] [Nonempty Θ] {π : Measure Θ} [IsFiniteMeasure π]
    (KX : Kernel Θ 𝓧) [IsMarkovKernel KX] (KY : Kernel Θ 𝓨) [IsMarkovKernel KY] :
    (KX ×ₖ KY) ∘ₘ π = (KX ∘ₘ π) ⊗ₘ posteriorPredictive KX KY π := by
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro s ⟨A, hA, B, hB, rfl⟩
    -- The integrand on `𝓧 × Θ`.
    set F : 𝓧 × Θ → ℝ≥0∞ := fun p => A.indicator (1 : 𝓧 → ℝ≥0∞) p.1 * KY p.2 B with hFdef
    have hF : Measurable F :=
      ((measurable_const.indicator hA).comp measurable_fst).mul
        ((KY.measurable_coe hB).comp measurable_snd)
    -- Swap route: the pivotal disintegration identity.
    have key2 : ∫⁻ p, F p ∂((KX ∘ₘ π) ⊗ₘ (KX†π)) = ∫⁻ θ, KX θ A * KY θ B ∂π := by
      rw [compProd_posterior_eq_map_swap, lintegral_map hF measurable_swap,
        Measure.lintegral_compProd (f := fun a : Θ × 𝓧 => F a.swap) (hF.comp measurable_swap)]
      refine lintegral_congr fun θ => ?_
      simp only [hFdef, Prod.swap_prod_mk]
      rw [lintegral_mul_const _ (measurable_one.indicator hA), lintegral_indicator_one hA]
    -- CompProd route: unfold the posterior predictive on the rectangle.
    have key : ∫⁻ p, F p ∂((KX ∘ₘ π) ⊗ₘ (KX†π))
        = ∫⁻ x in A, ∫⁻ θ, KY θ B ∂((KX†π) x) ∂(KX ∘ₘ π) := by
      rw [Measure.lintegral_compProd hF]
      simp only [hFdef]
      rw [← lintegral_indicator hA]
      refine lintegral_congr fun x => ?_
      rw [lintegral_const_mul _ (KY.measurable_coe hB)]
      by_cases hx : x ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
    -- Assemble.
    rw [Measure.bind_apply (hA.prod hB) (Kernel.aemeasurable _)]
    simp_rw [Kernel.prod_apply_prod]
    rw [Measure.compProd_apply_prod hA hB]
    simp_rw [posteriorPredictive_apply, Measure.bind_apply hB (Kernel.aemeasurable _)]
    rw [← key, key2]
  · simp

/-- **The posterior predictive is the conditional law of the future given the data**
(Gelman §1.3): under `(θ, x, y) ~ π ⊗ₘ (KX ×ₖ KY)`, `condDistrib` of the future given the
data agrees with `posteriorPredictive`, predictive-a.e. -/
theorem condDistrib_ae_eq_posteriorPredictive
    [StandardBorelSpace Θ] [Nonempty Θ] [StandardBorelSpace 𝓨] [Nonempty 𝓨]
    {π : Measure Θ} [IsFiniteMeasure π]
    (KX : Kernel Θ 𝓧) [IsMarkovKernel KX] (KY : Kernel Θ 𝓨) [IsMarkovKernel KY] :
    condDistrib (fun ω : Θ × 𝓧 × 𝓨 => ω.2.2) (fun ω => ω.2.1) (π ⊗ₘ (KX ×ₖ KY))
      =ᵐ[KX ∘ₘ π] posteriorPredictive KX KY π := by
  set μ : Measure (Θ × 𝓧 × 𝓨) := π ⊗ₘ (KX ×ₖ KY) with hμ
  set X : Θ × 𝓧 × 𝓨 → 𝓧 := fun ω => ω.2.1 with hXdef
  set Y : Θ × 𝓧 × 𝓨 → 𝓨 := fun ω => ω.2.2 with hYdef
  have hY : AEMeasurable Y μ := (measurable_snd.comp measurable_snd).aemeasurable
  -- Data marginal of the joint model is the predictive base measure.
  have hmarg : μ.map X = KX ∘ₘ π := by
    have hXcomp : X = Prod.fst ∘ Prod.snd := rfl
    rw [hXcomp, ← Measure.map_map measurable_fst measurable_snd,
      show μ.map Prod.snd = μ.snd from rfl, hμ, Measure.snd_compProd,
      Measure.map_comp _ _ measurable_fst, ← Kernel.fst_eq, Kernel.fst_prod]
  -- Joint law of the pair `(data, future)` factors as data ⊗ predictive.
  have hjoint : μ.map (fun ω => (X ω, Y ω)) = μ.map X ⊗ₘ (posteriorPredictive KX KY π) := by
    have he : (fun ω : Θ × 𝓧 × 𝓨 => (X ω, Y ω)) = Prod.snd := rfl
    rw [he, show μ.map Prod.snd = μ.snd from rfl, hμ, Measure.snd_compProd,
      comp_prod_eq_compProd_posteriorPredictive, ← hmarg]
  have h := condDistrib_ae_eq_of_measure_eq_compProd X hY hjoint
  rwa [hmarg] at h

end StatLean.Bayesian
