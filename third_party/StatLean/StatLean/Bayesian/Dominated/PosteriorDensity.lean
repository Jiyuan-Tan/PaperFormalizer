module
public import StatLean.Bayesian.Dominated.PredictiveDensity

@[expose] public section

/-!
# Bayes' theorem in dominated form (posterior density)

The central theorem of Bayesian inference in the dominated setting: for predictive-almost-every
data `x`, the posterior is the prior reweighted by the normalized likelihood density,
$$\pi(d\theta \mid x) = \frac{p(\theta, x)\,\pi(d\theta)}{\int_\Theta p(\theta', x)\,\pi(d\theta')}.$$

The proof identifies the explicit density kernel `bayesKernel p π` with Mathlib's abstract
posterior `κ†π`, via the disintegration identity
`(κ ∘ₘ π) ⊗ₘ bayesKernel p π = (π ⊗ₘ κ).map Prod.swap` and the uniqueness of disintegrations
(`ae_eq_posterior_of_compProd_eq`).

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §1.2, eq. (1.2.3)
(the posterior density), p. 9; §1.4, p. 22.

**Proof formalization notes.** The headline `compProd_bayesKernel_eq_map_swap` is a π-system
computation on measurable rectangles. `IsFiniteKernel (bayesKernel p π)` is proved unconditionally
(the total mass is `≤ 1` where measurable, and the junk branch of `Kernel.withDensity` is the zero
kernel). No `IsMarkovKernel κ` is required — `bayesKernel` self-normalizes. `SFinite ν` is needed
for the Tonelli/withDensity manipulations. Watch CLAUDE.md gotcha 12: after
`lintegral_withDensity_eq_lintegral_mul` the integrand is un-β-reduced — use `simp_rw`. Key
bricks: `ext_of_generate_finite`, `generateFrom_prod`, `isPiSystem_prod`,
`Measure.compProd_apply_prod`, `Measure.map_apply`, `Set.preimage_swap_prod`,
`Kernel.withDensity_apply'`, `ae_eq_posterior_of_compProd_eq`.

**Bibliographic comments.** The density form of Bayes' theorem goes back to Bayes (1763, published
by R. Price) and, in the generality of "the probability of causes," to P. S. Laplace (1774; and
*Théorie analytique des probabilités*, 1812). Its measure-theoretic justification rests on
A. N. Kolmogorov's axiomatization of conditioning (*Grundbegriffe der
Wahrscheinlichkeitsrechnung*, Springer, 1933) and on the theory of regular conditional
distributions on standard Borel spaces (J. L. Doob, *Stochastic Processes*, Wiley, 1953), which is
what Mathlib's disintegration-uniqueness lemma encapsulates.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧]
  {κ : Kernel Θ 𝓧} {π : Measure Θ} {ν : Measure 𝓧} {p : Θ → 𝓧 → ℝ≥0∞}

/-- The posterior density is jointly measurable. -/
theorem measurable_uncurry_bayesDensity [SFinite π]
    -- LEAN-ONLY: joint measurability of the likelihood density (regularity)
    (hp : Measurable (Function.uncurry p)) :
    Measurable (Function.uncurry (bayesDensity p π)) :=
  (hp.comp measurable_swap).div ((measurable_predictiveDensity hp).comp measurable_fst)

/-- The Bayes kernel evaluated at `x` is the prior reweighted by the posterior density. -/
theorem bayesKernel_apply [IsFiniteMeasure π]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p)) (x : 𝓧) :
    bayesKernel p π x = π.withDensity (bayesDensity p π x) := by
  rw [bayesKernel, Kernel.withDensity_apply _ (measurable_uncurry_bayesDensity hp),
    Kernel.const_apply]

/-- The Bayes kernel is sub-Markov: total mass `≤ 1` (mass `1` where `0 < m x < ∞`, else `0`). -/
theorem bayesKernel_apply_univ_le_one [IsFiniteMeasure π]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p)) (x : 𝓧) :
    bayesKernel p π x Set.univ ≤ 1 := by
  rw [bayesKernel_apply hp, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  show ∫⁻ θ, p θ x / predictiveDensity p π x ∂π ≤ 1
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const'' _ hp.of_uncurry_right.aemeasurable]
  exact ENNReal.mul_inv_le_one _

/-- The Bayes kernel is a finite kernel (total mass `≤ 1`). -/
theorem isFiniteKernel_bayesKernel [IsFiniteMeasure π]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p)) :
    IsFiniteKernel (bayesKernel p π) := by
  refine ⟨1, ENNReal.one_lt_top, fun x => ?_⟩
  rw [bayesKernel_apply hp, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  show ∫⁻ θ, p θ x / predictiveDensity p π x ∂π ≤ 1
  rcases eq_or_ne (predictiveDensity p π x) 0 with hm | hm
  · -- `m x = 0`: with `hp`, `p(·,x) =ᵐ[π] 0`, so the integrand is `π`-a.e. `0`.
    have hae : (fun θ => p θ x) =ᵐ[π] 0 :=
      likelihood_ae_eq_zero_of_predictiveDensity_eq_zero hp hm
    rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞))]
    · simp
    · filter_upwards [hae] with θ hθ
      simp [hθ]
  · simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hm)]
    exact ENNReal.mul_inv_le_one _

/-- Pointwise heart of the disintegration: for `ν`-a.e. `x`,
`m x * ∫_s (p(·,x)/m x) dπ = ∫_s p(·,x) dπ`. -/
theorem predictiveDensity_mul_setLIntegral_bayesDensity
    [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ))
    -- LEAN-ONLY: the target parameter set is measurable
    {s : Set Θ} (hs : MeasurableSet s) :
    ∀ᵐ x ∂ν, predictiveDensity p π x * ∫⁻ θ in s, bayesDensity p π x θ ∂π
      = ∫⁻ θ in s, p θ x ∂π := by
  filter_upwards [predictiveDensity_lt_top_ae (π := π) hp hκ] with x hxlt
  rcases eq_or_ne (predictiveDensity p π x) 0 with hm | hm
  · rw [hm, zero_mul, eq_comm]
    have hae : (fun θ => p θ x) =ᵐ[π] 0 :=
      likelihood_ae_eq_zero_of_predictiveDensity_eq_zero hp hm
    rw [lintegral_congr_ae (ae_restrict_of_ae hae)]
    simp
  · show predictiveDensity p π x * ∫⁻ θ in s, p θ x / predictiveDensity p π x ∂π
      = ∫⁻ θ in s, p θ x ∂π
    simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const'' _ hp.of_uncurry_right.aemeasurable, mul_comm _ (predictiveDensity p π x)⁻¹,
      ← mul_assoc, ENNReal.mul_inv_cancel hm hxlt.ne, one_mul]

/-- **The prior×likelihood disintegration**: `predictive ⊗ posterior-candidate = joint (swapped)`.
This is the "prior × likelihood = predictive × posterior" identity for the explicit density
kernel. -/
theorem compProd_bayesKernel_eq_map_swap [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    (κ ∘ₘ π) ⊗ₘ bayesKernel p π = (π ⊗ₘ κ).map Prod.swap := by
  haveI := isFiniteKernel_bayesKernel (π := π) hp
  have key : ∀ {t : Set 𝓧} {s : Set Θ}, MeasurableSet t → MeasurableSet s →
      ((κ ∘ₘ π) ⊗ₘ bayesKernel p π) (t ×ˢ s) = ((π ⊗ₘ κ).map Prod.swap) (t ×ˢ s) := by
    intro t s ht hs
    have hG : Measurable (fun x => ∫⁻ θ in s, bayesDensity p π x θ ∂π) := by
      have h := Kernel.measurable_coe (bayesKernel p π) hs
      simp_rw [bayesKernel_apply hp, withDensity_apply _ hs] at h
      exact h
    rw [Measure.compProd_apply_prod ht hs]
    simp_rw [bayesKernel_apply hp, withDensity_apply _ hs]
    rw [comp_eq_withDensity_predictiveDensity hp hκ,
      setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_predictiveDensity hp) hG ht]
    simp only [Pi.mul_apply]
    rw [lintegral_congr_ae
      (ae_restrict_of_ae (predictiveDensity_mul_setLIntegral_bayesDensity (π := π) hp hκ hs)),
      Measure.map_apply measurable_swap (ht.prod hs), Set.preimage_swap_prod,
      Measure.compProd_apply_prod hs ht]
    simp_rw [hκ, withDensity_apply _ ht]
    exact lintegral_lintegral_swap (hp.comp measurable_swap).aemeasurable
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨t, ht, s, hs, rfl⟩
    exact key ht hs
  · rw [← Set.univ_prod_univ]
    exact key MeasurableSet.univ MeasurableSet.univ

/-- Uniqueness of disintegration: the explicit density kernel IS the abstract posterior,
`(κ ∘ₘ π)`-a.e. -/
theorem bayesKernel_ae_eq_posterior [StandardBorelSpace Θ] [Nonempty Θ]
    [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    -- LEAN-ONLY: joint measurability of the likelihood density
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    bayesKernel p π =ᵐ[κ ∘ₘ π] κ†π := by
  haveI := isFiniteKernel_bayesKernel (π := π) hp
  exact ae_eq_posterior_of_compProd_eq (μ := π) (compProd_bayesKernel_eq_map_swap hp hκ)

/-- **Bayes' theorem, dominated form** (Robert eq. (1.2.3)): for predictive-a.e. `x`,
`π(dθ | x) = p(θ,x) π(dθ) / ∫ p(θ',x) π(dθ')`. -/
theorem posterior_eq_withDensity_likelihood_div_predictive
    [StandardBorelSpace Θ] [Nonempty Θ] [IsFiniteMeasure π] [IsFiniteKernel κ] [SFinite ν]
    -- LEAN-ONLY: joint measurability of the likelihood density (measure-theoretic regularity)
    (hp : Measurable (Function.uncurry p))
    -- USER-INPUT: dominated model, K(θ, ·) = p(θ, ·) ν; Robert Definition 1.2.1 / §1.4
    (hκ : ∀ θ, κ θ = ν.withDensity (p θ)) :
    ∀ᵐ x ∂(κ ∘ₘ π), (κ†π) x = π.withDensity fun θ => p θ x / ∫⁻ θ', p θ' x ∂π := by
  filter_upwards [bayesKernel_ae_eq_posterior (π := π) hp hκ] with x hx
  rw [← hx, bayesKernel_apply hp]
  rfl

end StatLean.Bayesian
