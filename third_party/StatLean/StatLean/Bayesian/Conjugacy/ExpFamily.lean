module
public import StatLean.Bayesian.Conjugacy.Defs
public import StatLean.Bayesian.Conjugacy.Criterion
public import StatLean.Bayesian.ForMathlib.IIDKernel

@[expose] public section

/-!
# Exponential-family conjugacy (Diaconis–Ylvisaker)

The single most reusable conjugacy theorem: for a natural exponential family
`p(θ, x) = h(x)·exp(⟨η θ, T x⟩ − A θ)` with Diaconis–Ylvisaker conjugate prior
`π_{χ,ν₀} ∝ exp(⟨χ, η θ⟩ − ν₀ A θ) μ₀(dθ)`,

* **conjugate update** (Robert Prop. 3.3.13): after `n` iid observations `x₁, …, xₙ`,
  $$\pi_{\chi,\nu_0}(\cdot \mid x_{1:n}) = \pi_{\chi + \sum_i T(x_i),\ \nu_0 + n},$$
* **marginal as normalizer ratio**: the predictive density is
  $$m(x_{1:n}) = \Big(\prod_i h(x_i)\Big)\,
    \frac{Z(\chi + \sum_i T(x_i),\ \nu_0 + n)}{Z(\chi, \nu_0)}.$$

**Reference.** C. P. Robert, *The Bayesian Choice: From Decision-Theoretic
Foundations to Computational Implementation*, 2nd ed., Springer Texts in Statistics, Springer,
2007 (ISBN 978-0-387-71598-8). §3.3.3, Proposition 3.3.13 and eqs. (3.3.4)–(3.3.5), p. 120
(single observation); the `n`-sample form via sufficiency, §4.2.2, p. 175 and eq. (3.3.6).

**Proof formalization notes.** The pointwise weight algebra is
`conjExpWeight χ ν₀ θ · ∏ᵢ p(θ, xᵢ) = (∏ᵢ h xᵢ) · conjExpWeight (χ + ∑ᵢ T xᵢ) (ν₀ + n) θ`
(`Real.exp_add`, sum rearrangement, `ENNReal.ofReal_mul`), fed to the conjugacy criterion with
the iid product density (`iidKernel_withDensity`). Propriety of the prior and of every updated
prior (`0 < Z < ∞`) is Robert's condition (3.3.5) — a genuine USER-INPUT (Diaconis–Ylvisaker give
`ν₀ > 0`, `χ/ν₀` interior as sufficient conditions; we take the propriety itself as hypothesis to
stay measure-theoretically minimal). The base factor must be finite (`h x ≠ ∞`) for the scalar
manipulations; base densities are finite in every model.

**Bibliographic comments.** The conjugate family for a natural exponential family and the
posterior linearity that characterizes it are P. Diaconis and D. Ylvisaker, "Conjugate priors for
exponential families," *Ann. Statist.* 7 (1979), 269–281; the
conjugate-prior program itself is H. Raiffa and R. Schlaifer (1961). Exponential-family theory:
L. D. Brown (1986). In modern practice this theorem is the backbone of variational inference and
natural-gradient methods, where conjugate updates are the tractable primitives.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Bayesian

variable {Θ 𝓧 : Type*} [mΘ : MeasurableSpace Θ] [m𝓧 : MeasurableSpace 𝓧] {d : ℕ}
  {η : Θ → Fin d → ℝ} {T : 𝓧 → Fin d → ℝ} {A : Θ → ℝ} {h : 𝓧 → ℝ≥0∞}
  {μ₀ : Measure Θ} {χ : Fin d → ℝ} {ν₀ : ℝ}

/-- Measurability of the conjugate-prior weight `θ ↦ exp(⟨χ, η θ⟩ − ν₀ A θ)`. -/
private theorem measurable_conjExpWeight (hη : Measurable η) (hA : Measurable A) :
    Measurable (conjExpWeight η A χ ν₀) := by
  unfold conjExpWeight
  refine (Real.measurable_exp.comp ?_).ennreal_ofReal
  refine Measurable.sub ?_ (measurable_const.mul hA)
  exact Finset.measurable_sum _ fun i _ =>
    measurable_const.mul ((measurable_pi_apply i).comp hη)

/-- Joint measurability of the single-observation exponential-family density
`(θ, x) ↦ h x · exp(⟨η θ, T x⟩ − A θ)`. -/
private theorem measurable_uncurry_expFamilyDensity
    (hη : Measurable η) (hA : Measurable A) (hT : Measurable T) (hh : Measurable h) :
    Measurable (Function.uncurry (expFamilyDensity η T A h)) := by
  have he : Function.uncurry (expFamilyDensity η T A h)
      = fun z : Θ × 𝓧 =>
        h z.2 * ENNReal.ofReal (Real.exp (∑ i, η z.1 i * T z.2 i - A z.1)) := rfl
  rw [he]
  refine (hh.comp measurable_snd).mul ?_
  refine (Real.measurable_exp.comp ?_).ennreal_ofReal
  refine Measurable.sub ?_ (hA.comp measurable_fst)
  exact Finset.measurable_sum _ fun i _ =>
    (((measurable_pi_apply i).comp (hη.comp measurable_fst)).mul
      ((measurable_pi_apply i).comp (hT.comp measurable_snd)))

/-- Pointwise conjugate weight algebra: prior weight × product likelihood = base factors ×
updated weight. -/
theorem conjExpWeight_mul_prod_expFamilyDensity {n : ℕ}
    -- USER-INPUT: base factors are finite (true for every density model); Robert §3.3.3
    (hh' : ∀ x, h x ≠ ∞) (θ : Θ) (x : Fin n → 𝓧) :
    conjExpWeight η A χ ν₀ θ * ∏ i, expFamilyDensity η T A h θ (x i)
      = (∏ i, h (x i)) * conjExpWeight η A (χ + ∑ i, T (x i)) (ν₀ + n) θ := by
  have hexp : (∑ i, χ i * η θ i - ν₀ * A θ) + ∑ k, (∑ i, η θ i * T (x k) i - A θ)
      = ∑ i, (χ + ∑ k, T (x k)) i * η θ i - (ν₀ + (n : ℝ)) * A θ := by
    have hS : ∑ i, (χ + ∑ k, T (x k)) i * η θ i
        = ∑ i, χ i * η θ i + ∑ k, ∑ i, η θ i * T (x k) i := by
      simp only [Pi.add_apply, Finset.sum_apply, add_mul]
      rw [Finset.sum_add_distrib]
      congr 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hS, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  simp only [expFamilyDensity, conjExpWeight]
  rw [Finset.prod_mul_distrib, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le),
    ← Real.exp_sum, mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, hexp]

/-- The conjugate prior is a probability measure under propriety. -/
theorem isProbabilityMeasure_conjExpPrior
    -- USER-INPUT: prior propriety 0 < Z(χ, ν₀) < ∞; Robert eq. (3.3.5)
    (hZ0 : conjExpZ μ₀ η A χ ν₀ ≠ 0) (hZ' : conjExpZ μ₀ η A χ ν₀ ≠ ∞) :
    IsProbabilityMeasure (conjExpPrior μ₀ η A χ ν₀) := by
  refine ⟨?_⟩
  simp only [conjExpPrior, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  exact ENNReal.inv_mul_cancel hZ0 hZ'

/-- **Exponential-family conjugate update, `n` iid observations** (Robert Proposition 3.3.13;
Table 4.2.1's sufficiency remark): the posterior of `π_{χ,ν₀}` after `x₁,…,xₙ` is
`π_{χ+∑T(xᵢ), ν₀+n}`, predictive-a.e. -/
theorem expFamily_iid_posterior_ae [StandardBorelSpace Θ] [Nonempty Θ]
    {ν : Measure 𝓧} [SigmaFinite ν] {κ : Kernel Θ 𝓧} [IsMarkovKernel κ]
    -- LEAN-ONLY: measurability of the family components (regularity)
    (hη : Measurable η) (hA : Measurable A) (hT : Measurable T) (hh : Measurable h)
    -- USER-INPUT: base factors are finite; Robert §3.3.3
    (hh' : ∀ x, h x ≠ ∞)
    -- USER-INPUT: the model is the dominated exponential family; Robert Def 3.3.2/eq. (3.3.1)
    (hκ : ∀ θ, κ θ = ν.withDensity (expFamilyDensity η T A h θ)) (n : ℕ)
    -- USER-INPUT: prior propriety 0 < Z(χ, ν₀) < ∞; Robert eq. (3.3.5)
    (hZ0 : conjExpZ μ₀ η A χ ν₀ ≠ 0) (hZ' : conjExpZ μ₀ η A χ ν₀ ≠ ∞)
    -- LEAN-ONLY: instance plumbing, derivable from hZ0/hZ' via `isProbabilityMeasure_conjExpPrior`
    [IsFiniteMeasure (conjExpPrior μ₀ η A χ ν₀)]
    -- USER-INPUT: propriety of every updated prior; Robert eq. (3.3.5)
    (hZn : ∀ x : Fin n → 𝓧,
      conjExpZ μ₀ η A (χ + ∑ i, T (x i)) (ν₀ + n) ≠ 0
        ∧ conjExpZ μ₀ η A (χ + ∑ i, T (x i)) (ν₀ + n) ≠ ∞) :
    ∀ᵐ x ∂(iidKernel κ n ∘ₘ conjExpPrior μ₀ η A χ ν₀),
      ((iidKernel κ n)†(conjExpPrior μ₀ η A χ ν₀)) x
        = conjExpPrior μ₀ η A (χ + ∑ i, T (x i)) (ν₀ + n) := by
  have hunc := measurable_uncurry_expFamilyDensity hη hA hT hh
  refine posterior_ae_eq_of_withDensity_eq_smul
    (ν := Measure.pi fun _ => ν)
    (p := fun θ x => ∏ i, expFamilyDensity η T A h θ (x i))
    (ρ := fun x => conjExpPrior μ₀ η A (χ + ∑ i, T (x i)) (ν₀ + n))
    (c := fun x => (conjExpZ μ₀ η A χ ν₀)⁻¹ * (∏ i, h (x i)) *
      conjExpZ μ₀ η A (χ + ∑ i, T (x i)) (ν₀ + n))
    (measurable_uncurry_prod_likelihood hunc)
    (fun θ => iidKernel_withDensity hunc hκ n θ)
    (fun x => isProbabilityMeasure_conjExpPrior (hZn x).1 (hZn x).2)
    ?_
  intro x
  have hg : Measurable fun θ => ∏ i, expFamilyDensity η T A h θ (x i) :=
    Finset.measurable_prod _ fun i _ =>
      hunc.comp (measurable_id.prodMk measurable_const)
  have hw : Measurable (conjExpWeight η A χ ν₀) := measurable_conjExpWeight hη hA
  have hprodne : (∏ i, h (x i)) ≠ ∞ := ENNReal.prod_ne_top fun i _ => hh' (x i)
  have hdens : conjExpWeight η A χ ν₀ * (fun θ => ∏ i, expFamilyDensity η T A h θ (x i))
      = (∏ i, h (x i)) • conjExpWeight η A (χ + ∑ i, T (x i)) (ν₀ + n) := by
    funext θ
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    exact conjExpWeight_mul_prod_expFamilyDensity hh' θ x
  simp only [conjExpPrior]
  rw [withDensity_smul_measure, ← withDensity_mul _ hw hg, hdens,
    withDensity_smul' _ _ hprodne, smul_smul, smul_smul]
  congr 1
  rw [mul_assoc, ENNReal.mul_inv_cancel (hZn x).1 (hZn x).2, mul_one]

/-- **The exponential-family marginal is a normalizer ratio** (single observation):
`m(x) = h(x) · Z(χ + T x, ν₀ + 1) / Z(χ, ν₀)`. No propriety needed — the `ℝ≥0∞` junk conventions
match on both sides. -/
theorem expFamily_predictiveDensity_eq_ratio
    -- LEAN-ONLY: measurability of the family components (regularity)
    (hη : Measurable η) (hA : Measurable A) (x : 𝓧) :
    predictiveDensity (expFamilyDensity η T A h) (conjExpPrior μ₀ η A χ ν₀) x
      = h x * (conjExpZ μ₀ η A (χ + T x) (ν₀ + 1) / conjExpZ μ₀ η A χ ν₀) := by
  have hw : Measurable (conjExpWeight η A χ ν₀) := measurable_conjExpWeight hη hA
  have hwn : Measurable (conjExpWeight η A (χ + T x) (ν₀ + 1)) := measurable_conjExpWeight hη hA
  have hgx : Measurable (fun θ => expFamilyDensity η T A h θ x) := by
    unfold expFamilyDensity
    refine Measurable.const_mul ?_ (h x)
    refine (Real.measurable_exp.comp ?_).ennreal_ofReal
    refine Measurable.sub ?_ hA
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp hη).mul_const (T x i)
  have hsingle : ∀ θ, conjExpWeight η A χ ν₀ θ * expFamilyDensity η T A h θ x
      = h x * conjExpWeight η A (χ + T x) (ν₀ + 1) θ := by
    intro θ
    have hexp : (∑ i, χ i * η θ i - ν₀ * A θ) + (∑ i, η θ i * T x i - A θ)
        = ∑ i, (χ + T x) i * η θ i - (ν₀ + 1) * A θ := by
      have hS : ∑ i, (χ + T x) i * η θ i = ∑ i, χ i * η θ i + ∑ i, η θ i * T x i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Pi.add_apply, add_mul, mul_comm (T x i) (η θ i)]
      rw [hS]; ring
    simp only [conjExpWeight, expFamilyDensity]
    rw [mul_left_comm, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, hexp]
  simp only [predictiveDensity, conjExpPrior, conjExpZ]
  rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hw hgx]
  simp only [Pi.mul_apply]
  rw [lintegral_congr hsingle, lintegral_const_mul _ hwn, smul_eq_mul,
    ENNReal.div_eq_inv_mul, mul_left_comm]

end StatLean.Bayesian
